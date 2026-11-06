(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fr.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fy e6 Start7States.

(* [comment removed for export] *)
Module FpsU_b0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st"; "T7b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "PRE_U"; "SUF_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs"; "T8C"; "tailC_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs.
Import ListNotations.
Open Scope Z_scope.

Lemma okC : ltac2:(tb__ "0|1|
S3S1S8S5S6Z7M0S4S0A1S7G0S0A2A5S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsU_b0.

(* [comment removed for export] *)
Module FpsC_b0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st"; "T7b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "PRE_C"; "SUF_NL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs"; "T8C"; "tailC_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs.
Import ListNotations.
Open Scope Z_scope.

Lemma okC : ltac2:(tb__ "0|1|
S3S1S8S5S6Z11M0S4S0A1S7G0S0A2A5S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_b0.

(* [comment removed for export] *)
Module Fps_tailC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "valuation"; "sv"; "rl"; "ss_next"; "rm"; "rw"; "ss_objs"; "eval"; "holds"; "sstate"; "SLit"; "obj_range"; "agree_below"; "ob_dflt"; "outside_all"; "swf"; "odefault"; "smatch"; "ss_lenient"; "DList"; "cell"; "ranges_disjoint"; "dflt_writable"; "ob_cells"; "obj_holds"; "obj_lo_of"; "sprop_below"; "ss_facts"; "ss_pc"; "SVar"; "image_byte"; "is_arr"; "mkObj"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "obj_hi_of"; "rd"; "rom_ok"; "soff"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "to_nat"; "pow"; "of_nat"; "div"; "leb"; "ltb"; "mul"; "sub"; "@Corelib.Init.Datatypes"; "bool"; "list"; "option"; "Some"; "true"; "length"; "app"; "nat"; "nil"; "cons"; "false"; "pair"; "prod"; "snd"; "fst"; "None"; "andb"; "negb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs"; "FIN"; "FC1"; "obj_lowb"; "FSC"; "lastobj"; "unlistk_at"; "xr_lowb"; "O_strR"; "splitsC"; "tailC_out"; "XM"; "XWC"; "blC"; "osome_eqb"; "selR"; "subC1"; "tailC"; "unk_keep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "xword"; "ok_frameA"; "smatchA"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "sX"; "O_strS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "BASEF"; "facts_fps"; "runp"; "set_facts"; "fs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "HSE"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "FdChannel"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "wview"; "find_segment"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Fps_tailC"; "LOWV"; "lastobj_of"; "xwords_clear'"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "sprop_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Fps_tailC.TailC"; "Jp1"; "rhoC_of"; "PG0"; "PG1"; "PG2"; "PG3"; "PG4"; "PG5"; "PG6"; "RC1"; "WLF1"; "mrest"; "rhoM_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "w_cfg"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates"; "app_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "Posts_fps"; "tailA_out"; "x_ok"; "bexps_eqb"; "blA"; "dropL"; "tailA_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL"; "dlist_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA"; "exts_rl_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_run"; "FsBelow"; "FsHold"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA"; "Kf"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@Stdlib.Arith.PeanoNat.Nat"; "min"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj MuslWL DrvGlue CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform ListCommitA SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_run OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Fps_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition xwords_clear' (rho : valuation) (A : axst) (lo' hi' : Z) : Prop := ltac2:(tb__ "0|5|
S51S8S8A2M0S35S35S7eG0R3S5cVA;A1A3S1S3aS38Q40M1SeVrho;S53S8S8R4A3A2A2M2R3A2S3cR3S3bG2S38G1SeVrho;S52S8S8R4A3A2A2A2A2A2S1S3aZ0R3A2S3cR3Z8M3A2A2S2S1S3aVlo';S3bS43S40S3bS38G1SeVrho;S5dVA;A1A2A2S40R5G3A2A2G3A2G3A2R4A2M4A2S3cG4Vhi';A2A2A1F_;F_;F_;Fj;Fy;Frr;").

Lemma SPA_carve_listobj : ltac2:(tb__ "0|a|
S77S7S5aS46S37Q40M0A1A1Sb7S8S8S35S17S36S36S75S58RbR9RaR8R7A6S0S47S36A1ScaR4A1S48S36R3A2A3S5bRbA1S10S27R9S11Z0M1A1R8S4dS1bA1R6A5S5S28S23R2A1S33R2A1S32R2A1S31R2A1S34R2A1S4bS5SdR2A1S4eS5R1S4dS5A1A3A3S22R2A1R5S19R2A1A9S10S0S45S16R1A1S49A3S99SaR4A1R7A2S38G0SeR11RdA2A2S35S0S35S2fR12RdA2RcA3S3aG1RdA2S3cReS3eZ2M2Z3fA2A2S3aS3bR4RfA2S3eG2Z40A2A2S0S35S3fS4aS37Q8M3A1M4S9R16ReA2A2A1R10A3S5fS5S5S1cS12R18R1A2S50S35S35R7S3bR7R12A2A4A2Lo';SdRbA1A3S35S1S3aG1R1A2M5S3cR1R13A2A2S0S45S1dR13A1S49A3S2S0S47G4A1M6S90S58SbR1bA1M7S39G0S3bRaR3A2A2A3S54G4A1M8A3A1F_;F_;Foff;S35S1G5S3cR1R14A2A2S0G6SccS58G7S39G0S3bRaR2A2A2A3S48G4S60G4S3dR2A1S9R1bR13A2S39G3G1A2A4A2A3F_;Foff;S35S1S3aRaR1A2S3cR1S3bRaR15A2M9A2A2S2S0G6SbR1cS39G0R2A2A2G8A3A1F_;Fz;S98R1bR1aRaG9A4S75S58R1dS5eR1bReA2R1cR1aR19A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';To;TS;F_;F_;Fnx;Fl;Fd;Fhi;Fehi;Fbase;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w base ehi hi d l nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hd S o S' Hwf' Hnx b Hehi Hh0 Hh Hbh Hlen Hdisj Hw Hrd Hdef Hxs.
  subst S. split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    pose proof (urange (eval rho base)) as Rb.
    apply (smatch_carve_listobj segs rho (ax_S A) _ base (SLit 0) ehi 0 hi d l nx Hsm Hd Hwf');
      [apply soff_lit_small; lia | exact Hehi | lia | lia | fold b; lia | fold b; lia | rewrite Hlen; lia | | |].
    + fold b. replace (b + 0) with b by lia. exact Hdisj.
    + intros off Hoff Hdw. apply Hw; [lia | exact Hdw].
    + intros off Hoff. rewrite Z.sub_0_r. apply Hrd. lia.
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of, o. cbn [ob_base ob_lo ob_hi fst snd]. fold b.
    rewrite soff_lit_small by lia. rewrite Hehi.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2.
    pose proof (Hxs rr y j Hr Hy Hj). lia.
Qed.

Lemma obj_holds_unlistk : ltac2:(tb__ "0|0|
S7S8fS5S36S0S17S14R2A1S1aR1A1A3S1fS58R5R4R3A4S1fS58R6R5S74R4A1A4F_;F_;Fl;Fob;Fms;Frho;").
Proof.
  intros rho ms ob l Hd (Hb & Hwr & Hcl & Hdf & Hi). unfold unk_keep, obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi].
  split; [exact Hb|]. split; [intros off Hoff _; apply Hwr; [exact Hoff | rewrite Hd; reflexivity]|].
  split; [exact Hcl|]. split; [|exact I].
  intros off Hoff Hnc. cbn. rewrite Hd in Hdf. cbn in Hdf. eexists. apply Hdf; [exact Hoff | exact Hnc].
Qed.

Lemma smatch_unlistk_at : ltac2:(tb__ "0|0|
S7S10S4cS5S36S51S46S88A1S93A2S0S47S5A1S7cS5SdR5A1R4A3S48S5R3A2A3S0S17S14R4A1S1aR3A1A3S0S45S16S68R7R6A2A1S49A3S18S58R9R8R4A4S18S58RaS68R9R8A2R5A4F_;F_;F_;F_;Fw;Fl;Fob;Fi;FS;Frho;").
Proof.
  intros rho S i ob l [tr [ms md]] Hn Hd Hwf Hsm.
  pose proof (nth_error_split3 _ _ _ Hn) as Esplit.
  unfold unlistk_at in Hwf |- *. rewrite Hn in Hwf |- *.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hcsr & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (RNG : obj_range rho (unk_keep ob) = obj_range rho ob) by reflexivity.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hcsr|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs set_objs]. destruct Hm as (Hall & Hpd & Hfr). rewrite Esplit in Hall, Hpd, Hfr.
  split; [|split].
  - apply Forall_app in Hall as [HA HB]. inversion HB; subst. apply Forall_app. split; [exact HA|].
    constructor; [eapply obj_holds_unlistk; eauto | assumption].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Lemma two62_eq : two62 = 2 ^ 62. Proof. reflexivity. Qed.
Lemma segs_top_val : InitState.segs_top segs = 0x646000.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma find_segment_none_high : ltac2:(tb__ "0|1|
S37Q40M0A1S3aS87S38G0R1A2A2S0S47SbdA1S91S58S38G0R2A2Z1A3S54SbdA1A3F_;Fa;").
Proof.
  intros a Ha. destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:E0; [|reflexivity].
  exfalso. pose proof (InitState.find_segment_top segs (bv_unsigned a) 1 sg ltac:(lia) E0) as X. rewrite segs_top_val in X. unfold HSE in Ha. lia.
Qed.
Lemma image_byte_none_high : ltac2:(tb__ "0|2|
S37Q40M0A1S3aS87S38G0R1A2A2S0S47S37Q8A1M1A1S25S58R2A2S54G1A1A3F_;Fa;").
Proof. intros a Ha. unfold image_byte, memory_read. rewrite find_segment_none_high by exact Ha. reflexivity. Qed.
Lemma rd_of_high : ltac2:(tb__ "0|3|
S37Q40M0A1M1S47S37Q8A1A1M2F_;G1S3aS87S38G0R1A2A2S0G2SccS58R3R2A3R3R2A1A3F_;Fa;Fm;").
Proof. intros m a Ha. unfold rd_of. destruct (m a); [reflexivity|]. apply image_byte_none_high. exact Ha. Qed.
Lemma wview_high : ltac2:(tb__ "0|3|
S37Q40M0A1M1S47S37Q8A1A1M2F_;G1S3aS87S38G0R1A2A2S0G2S90S58R3R2A3R3R2A1A3F_;Fa;Fm;").
Proof. intros m a Ha. unfold wview. destruct (m a); [reflexivity|]. rewrite find_segment_none_high by exact Ha. reflexivity. Qed.
Lemma rd_high : ltac2:(tb__ "0|1|
S8fS37Q40M0A1S2eS58R2A2S3aS87S38G0R2A2A2S0S47S37Q8A1A1S2dR4R3A2S92R4R3A2A3F_;F_;Fa;Fms;").
Proof.
  intros ms a Hrom Ha. unfold rd, ms_read_byte. destruct (ms_mem ms a) eqn:E0; [reflexivity|].
  rewrite (Hrom a). apply image_byte_none_high. exact Ha.
Qed.

Lemma splitsC_SPA : ltac2:(tb__ "0|0|
S77S35S5aS10S7S46S37Q40A1A1Sb7S0S47S10A1S6bR6S5bR5A1A2S48S10R4A2A3S75S58R8R6R4R3R2A6S75S58R9S5eR7R6A2R5R4R3A6F_;F_;Fw;Ftp;Frho;FS6;FA;Fa;FJ;").
Proof.
  intros J a A S6 rho tp w H Hsp. unfold splitsC, obindW in H.
  destruct (split_obj_at (ax_S A) 0 (SLit (-1128))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-1096))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 2 (SLit (-464))) as [S3|] eqn:E3; [|discriminate].
  destruct (split_obj_at S3 3 (SLit (-464 + a))) as [S4|] eqn:E4; [|discriminate].
  destruct (split_obj_at S4 5 (SLit (FERR + 120))) as [S5|] eqn:E5; [|discriminate].
  pose proof (SPA_split segs J rho A 0 (SLit (-1128)) S1 tp w E1 Hsp) as H1.
  pose proof (SPA_split segs J rho (ax_setS A S1) 1 (SLit (-1096)) S2 tp w E2 H1) as H2.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS A S1) S2) 2 (SLit (-464)) S3 tp w E3 H2) as H3.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS A S1) S2) S3) 3 (SLit (-464 + a)) S4 tp w E4 H3) as H4.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS A S1) S2) S3) S4) 5 (SLit (FERR + 120)) S5 tp w E5 H4) as H5.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS (ax_setS A S1) S2) S3) S4) S5) 6 (SLit (FERR + 124)) S6 tp w H H5) as H6.
  rewrite !ax_setS_setS in H6. exact H6.
Qed.

Definition LOWV (r : valuation) : Prop := ltac2:(tb__ "0|6|
S1S3aZ7fff7ffff000S38Q40M0ScVr;PaA2A2M1A2S1S3aG1S38G0SeVr;S80A2A2M2A2S1S3aS87S38G0ScVr;P12A2A2M3A2S1S3aS3bG3S38G0ScVr;P13A2A2M4A2S3eZ2Z2fA2A2S1S3aS3bS38G0ScVr;P14A2A2M5Z8A2G4A2S0S35G2S3bG3G5A2A3A2A2A2A2A2").
Lemma LOWV_of_facts : ltac2:(tb__ "0|0|
S7S5fS6SfR1A1S83A3S96R2A1F_;Fr;").
Proof.
  intros r HF. unfold facts_fps in HF. apply Forall_app in HF as [HB HS].
  destruct (str_factsZ r HS) as (Z1 & _ & Z5 & _ & Z10 & _ & _).
  pose proof (Forall_inv (Forall_inv_tail HB)) as B2. cbn [holds eval] in B2. rewrite lit_unsigned in B2. change (0x7fff7ffff000 mod 2 ^ 64) with 0x7fff7ffff000 in B2.
  do 9 (apply Forall_inv_tail in HS). pose proof (Forall_inv HS) as F9. do 7 (apply Forall_inv_tail in HS). pose proof (Forall_inv HS) as F16.
  unfold vXB in F9. cbn [holds eval] in F9, F16. rewrite lit_unsigned in F9. change (HSE mod 2 ^ 64) with HSE in F9.
  pose proof (urange (rw r 18)) as R18. pose proof (urange (rw r 20)) as R20. pose proof (urange (rw r 17)) as R17. pose proof (urange (rw r 16)) as R16.
  assert (EsX : bv_unsigned (eval r sX) = bv_unsigned (rw r 18) + bv_unsigned (rw r 20)).
  { unfold sX, vXB, vXO. apply (U_add2 r (SVar 18) (SVar 20)); [reflexivity | reflexivity | unfold HSE in *; lia]. }
  unfold LOWV. rewrite EsX in *. unfold HSE in *. repeat split; lia.
Qed.

Lemma obj_lowb_below : ltac2:(tb__ "0|0|
S7S5S96R2A1S0S45S65R2A1S49A3S3aS52S35S35S12R4R3A2A3S38Q40SeR4S80A2A2A2F_;F_;Fo;Fr;").
Proof.
  intros r o (L1 & L2 & L3 & L4 & L5 & L6) H. unfold obj_lowb in H. unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd].
  pose proof (urange (rw r 10)) as R10.
  destruct (ob_base o) as [bz|bi|op ba bb| | | | |] eqn:Eb; try discriminate.
  - destruct bz; try discriminate. destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    cbn [eval]. rewrite lit_unsigned, Z.mod_small by lia. rewrite soff_lit_small by (unfold HSE in *; lia). unfold HSE in *. lia.
  - destruct bi as [p|p|]; try discriminate; try (destruct p as [p'|p'|]; try discriminate; destruct p' as [q|q|]; try discriminate; destruct q; try discriminate).
    destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    cbn [eval]. rewrite two62_eq in H1. rewrite soff_lit_small by lia. lia.
  - destruct op; try discriminate. destruct ba as [|ai| | | | | |]; try discriminate.
    destruct ai as [p|p|]; try discriminate; try (destruct p as [p'|p'|]; try discriminate; destruct p' as [q|q|]; try discriminate; destruct q; try discriminate).
    destruct bb as [c| | | | | | |]; try discriminate.
    destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
    apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. rewrite two62_eq in H3.
    rewrite soff_lit_small by lia. rewrite (U_addc r (SVar 10) c (bv_unsigned (rw r 10)) eq_refl) by lia. lia.
Qed.
Lemma obj_lowb_disjoint : ltac2:(tb__ "0|1|
S7S5S35S96R3A1S0S45S65R3A1S49A3S3aZ0R3A2S1cS12R6R5A2S50S35S35S38Q40SeR6S80A2A2M0S3bG0R4A2A4A2F_;F_;F_;Fh;Fo;Fr;").
Proof. intros r o h HL H Hh. pose proof (obj_lowb_below r o HL H). unfold ranges_disjoint. cbn [fst snd]. lia. Qed.
Lemma objs_lowb_disjoint : ltac2:(tb__ "0|1|
S7S46S5A1S35S96R3A1S0S45S7bS5S65R3A3S49A3S3aZ0R3A2S5fS5S5S1cS12R7R1A2S50S35S35S38Q40SeR7S80A2A2M0S3bG0R5A2A4A2Lo';R5A3F_;F_;F_;Fh;Fobjs;Fr;").
Proof.
  intros r objs h HL H Hh. apply Forall_forall. intros o Ho. apply obj_lowb_disjoint; [exact HL | exact (proj1 (forallb_forall _ _) H o Ho) | exact Hh].
Qed.
Lemma objs_lowb_outside : ltac2:(tb__ "0|1|
S7S46S5A1S37Q40M0A1S96R3A1S0S45S7bS5S65R3A3S49A3S3aS38G0SeR5S80A2A2S38G0R3A2A2S15R6R5R4A3F_;F_;F_;Fa;Fobjs;Fr;").
Proof.
  intros r objs a HL H Ha. unfold outside_all. apply Forall_forall. intros o Ho. cbn zeta.
  pose proof (obj_lowb_below r o HL (proj1 (forallb_forall _ _) H o Ho)). lia.
Qed.

Lemma xr_lowb_word : ltac2:(tb__ "0|1|
S7S5aS37Q40M0A1S96R3A1S0S45S7bS51S8S8A2S69S5cR3A1A3S49A3S0S8S5dR4A1S11S59A1A3S78R6R5R4A3S3cS38G0R5A2S87A2F_;F_;F_;F_;Fx;FA;Fr;").
Proof.
  intros r A x (L1 & L2 & L3 & L4 & L5 & L6) HX Hb (rr & y & j & Hr & Hy & Hj & Hz & ->).
  rewrite Hb in *. cbn [eval] in Hz |- *. rewrite lit_unsigned in *. change (SHB mod 2 ^ 64) with SHB in *.
  destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2.
  pose proof (proj1 (forallb_forall _ _) HX rr Hr) as H. unfold xr_lowb in H.
  assert (Y : y < 2 ^ 47).
  { destruct rr as [e1 e2]. cbn [fst snd] in Hy.
    destruct e1 as [bz|bi|op ba bb| | | | |]; try discriminate.
    - destruct e2 as [lz| | | | | | |]; try discriminate. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. cbn [eval] in Hy. rewrite !lit_unsigned, !Z.mod_small in Hy by lia. lia.
    - destruct bi as [p|p|]; try discriminate; destruct p as [p'|p'|]; try discriminate; try (destruct p' as [q|q|]; try discriminate; destruct q as [q'|q'|]; try discriminate; destruct q'; try discriminate).
      destruct e2 as [|li|op2 c1 c2| | | | |]; try discriminate.
      + destruct li as [p|p|]; try discriminate; destruct p as [p'|p'|]; try discriminate; try (destruct p' as [q|q|]; try discriminate; destruct q as [q'|q'|]; try discriminate; destruct q'; try discriminate).
        cbn [eval] in Hy. pose proof (urange (rw r 19)). lia.
      +
        destruct op2; try discriminate. destruct c1 as [|li| | | | | |]; try discriminate.
        destruct li as [p|p|]; try discriminate; destruct p as [p'|p'|]; try discriminate; try (destruct p' as [q|q|]; try discriminate; destruct q as [q'|q'|]; try discriminate; destruct q'; try discriminate).
        destruct c2 as [c| | | | | | |]; try discriminate.
        apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
        pose proof (urange (rw r 19)) as R19. pose proof (urange (rw r 20)) as R20.
        rewrite (U_addc r (SVar 19) c (bv_unsigned (rw r 19)) eq_refl) in Hy by lia. cbn [eval] in Hy. lia.
    - destruct op; try discriminate. destruct ba as [|ai| | | | | |]; try discriminate.
      destruct ai as [p|p|]; try discriminate; try (destruct p as [p'|p'|]; try discriminate; destruct p' as [q|q|]; try discriminate; destruct q; try discriminate).
      destruct bb as [c| | | | | | |]; try discriminate. destruct e2 as [lz| | | | | | |]; try discriminate.
      apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
      pose proof (urange (rw r 10)) as R10. rewrite (U_addc r (SVar 10) c (bv_unsigned (rw r 10)) eq_refl) in Hy by lia.
      cbn [eval] in Hy. rewrite lit_unsigned, Z.mod_small in Hy by lia. unfold HSE in *. lia. }
  unfold SHB, HSE. pose proof (Z.div_le_mono y (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with (2 ^ 44) in H0. lia.
Qed.

Lemma smatch_set_rm_under : ltac2:(tb__ "0|5|
S7S10S51S46S88A1S93A2S37Q40M0A1M1S47S37Q8A1A1M2F_;S35S35S18S58R6R5R4A4S3S5S5S1S7eS5R1SdR7A1A3S1S3aS53S35S35S12R8R1A2M3A3R4A2S3aR3S52S35S35G3A3A2A2A2Lo;A2G1S2S0G2R6R1A1SbR9R1A2A3A1S1S3aR6S38G0R2A2M4A2S3cG4R5A2A2F_;Fa;S18S58SadR9R6A2R8R7A4F_;F_;F_;Fhi;Flo;Fm';Fw;FS;Frho;").
Proof.
  intros rho S [tr [ms md]] m' lo hi Hsm (o & Ho & Hlo & Hhi) Hm.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hcsr & Hv & Hm0 & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *. unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hswf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [intros rg Hrg; rewrite eval_set_rm; exact (Hr rg Hrg)|].
  split; [intros rg; unfold fregs_match in Hf; rewrite eval_set_rm; exact (Hf rg)|].
  split; [unfold fcsr_match in *; destruct (ss_fcsr S); [exact Hcsr | rewrite eval_set_rm; exact Hcsr]|].
  split; [unfold resv_match in *; destruct (ss_resv S), (ms_resv ms); try exact Hv; rewrite ?eval_set_rm; exact Hv|].
  split; [| apply Forall_forall; intros p Hp; apply (proj2 (holds_set_rm rho m' p)); exact (proj1 (Forall_forall _ _) Hfa p Hp)].
  destruct Hm0 as (Hall & Hpd & Hfr). split; [|split].
  - apply Forall_forall. intros ob Hob. apply (obj_holds_set_rm_ext segs rho m' ms ms ob (fun _ => eq_refl) (fun _ _ => eq_refl)).
    exact (proj1 (Forall_forall _ _) Hall ob Hob).
  - apply pairwise_disjoint_set_rm. exact Hpd.
  - intros a Hout. apply outside_all_set_rm in Hout. cbn [rm set_rm].
    destruct (decide (m' a = rm rho a)) as [E|NE].
    + rewrite E. exact (Hfr a Hout).
    + exfalso. pose proof (Hm a NE) as Ha. pose proof (proj1 (Forall_forall _ _) Hout o Ho) as X. lazy beta zeta in X. lia.
Qed.

Lemma SPA_rm_under : ltac2:(tb__ "0|6|
S77S5aS7S37Q40M0A1M1S47S37Q8A1A1M2F_;S46G1A1Sb7S35S35S75S58R8R7R6R4R3A6S3S5S5S1S7eS5R1SdS5bR9A1A1A3S1S3aS53S35S35S12R8R1A2M3A3R4A2S3aR3S52S35S35G3A3A2A2A2Lo;A2G1S2S0G2R8R1A1SbR9R1A2A3A1S1S3aR6S38G0R2A2M4A2S3cG4R5A2A2F_;Fa;G1S78RaRbR1A3S3cG4R7A2F_;Fx;RcRaR8SbbR7A1S95SbaR7A1A1A4RdSadRbRaA2M5R9SbbR8A1S95SbaR8A1A1A4F_;S75S58RdRcG5R9R8A6F_;F_;F_;F_;F_;Fhi;Flo;Fw;Ftp;Fm';Frho;FA;FJ;").
Proof.
  intros J A rho m' tp w lo hi Hsp Ho Hm Hx HJ.
  pose proof Hsp as [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  enough (G : SPA segs J (ax_setS A (ax_S A)) (set_rm rho m') tp w) by (rewrite ax_setS_id in G; exact G).
  eapply (SPA_morphX J J A (ax_S A) rho (set_rm rho m') tp w); [ | apply eval_set_rm | intros r Hr; split; apply eval_set_rm | | | exact HJ | exact Hsp].
  - unfold axwf in Hwf. exact Hwf.
  - intros x Hout Hrm. split; [apply outside_all_set_rm; exact Hout|]. cbn [rm set_rm].
    destruct (decide (m' x = rm rho x)) as [E|NE]; [exact E|]. exfalso.
    destruct Ho as (o & HoIn & Hlo & Hhi). pose proof (Hm x NE). pose proof (proj1 (Forall_forall _ _) Hout o HoIn) as X. lazy beta zeta in X. lia.
  - intros Hsm0. exact (smatch_set_rm_under rho (ax_S A) (virt tp w) m' lo hi Hsm0 Ho Hm).
Qed.

Lemma released_listA : ltac2:(tb__ "0|6|
S7S5aS46S5A1M0S5S46S37Q40M1A1A1S46S88A1M2S8fS89S36S0G0SdS5bR8A1A1S4bS5R7S4eS5R6S4dS5A1M3A3A3A3S7aS58RaR6R9S50G2S93R5S94R4R3A2A4A5S0S47S36A1ScaS14R8A1A1S48S36R3A2A3S0S46S1bA1S1eR9A1S4dS1bA1A3S3aS87S53S35S35S12RdRaA2A3A2S3aS52S35S35S12ReRbA2A3S3eZ2Z3fA2A2SaeRfS4eS5RcG3A3SbcR8RbR9A3A3S7S35S1S3aS20R11ReA2R1A2S3cR1S2cR11ReA2A2A2S0S47S37Q8M4A1M5A1SbR3S39G1S3bS38G1SeR12S29RfA1A2A2R2A2A2A2S48G5S60G5S3dS44R2S20R12RfA2A2A1S9R12RaA2S39G4Z0A2A4A2A3F_;Foff;Trho';F_;F_;F_;F_;F_;F_;Fl;Fmd;Fms;Ftr;Ftp;Fo;Fobjs;FA;Frho;").
Proof.
  intros rho A objs o tp tr ms md l Ho (Hsm & _) Hd Hc Hlo Hhi rho' off Hoff.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hcsr & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [virt fst snd cfg_ms cfg_model] in *.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (rewrite Ho; apply in_or_app; right; left; reflexivity).
  pose proof (proj1 (Forall_forall _ _) Hall o Hin_o) as Hoh.
  unfold obj_range in Hlo, Hhi. cbn [fst snd] in Hlo, Hhi. pose proof Hoh as ((B1 & B2 & B3 & B4) & _).
  assert (INR : in_ranges rho [o] (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))).
  { exists o. split; [left; reflexivity|]. unfold obj_range. cbn [fst snd]. rewrite u64_of_sum by lia. lia. }
  unfold rho'. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho [o] _) as [_|NI]; [|exfalso; exact (NI INR)].
  rewrite <- (rd_high (vms md tp ms) _ Hrom) by (rewrite u64_of_sum by lia; lia).
  exact (obj_bytes_list segs rho (vms md tp ms) o l off Hoh Hd Hc Hoff).
Qed.

Lemma xr_lowb_clear : ltac2:(tb__ "0|0|
S7S5aS35S35S96R4A1S0S45S7bS51S8S8A2S69S5cR4A1A3S49A3S0S8S5dR5A1S11S59A1A3S3aS87R5A2S98R8R7R6R5A4F_;F_;F_;F_;Fhi;Flo;FA;Fr;").
Proof.
  intros r A lo hi HL HX Hb Hlo rr y j Hr Hy Hj Hin.
  pose proof (urange (eval r (fst rr))). pose proof (urange (eval r (snd rr))).
  assert (Hz : 0 <= bv_unsigned (eval r (ax_base A)) + y / 8 < 2 ^ 64 \/ ~ (0 <= bv_unsigned (eval r (ax_base A)) + y / 8 < 2 ^ 64)) by lia.
  destruct Hz as [Hz|Hz].
  - pose proof (xr_lowb_word r A (word_byte (bv_unsigned (eval r (ax_base A)) + y / 8) j) HL HX Hb
                  ltac:(exists rr, y, j; repeat split; try assumption; lia)) as W.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2 in W. lia.
  - rewrite Hb in *. cbn [eval] in Hz, Hin. rewrite lit_unsigned in Hz, Hin. change (SHB mod 2 ^ 64) with SHB in Hz, Hin.
    pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Q. unfold SHB in *.
    assert (0 <= y / 8) by (apply Z.div_pos; lia). assert (y / 8 <= y) by (apply Z.div_le_upper_bound; lia).

    exfalso. apply Hz. split; [lia|].
    assert (y / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma outside_all_set_rl_state : ltac2:(tb__ "0|0|
S7S36S46S37Q8A1A1S10S37Q40A1S0S45S9cR4R2A2S4fA3S15R6SdR3A1R2A3S15S9bR7R6R5A3SdR4A1R3A3F_;F_;Fx;FS;FL;Fl;Fr;").
Proof.
  intros r l L S x Hst Hout. unfold state_has_rl in Hst.
  apply Bool.orb_false_iff in Hst as [Hst Xf]. apply Bool.orb_false_iff in Hst as [Hst Xo].
  unfold outside_all in *. apply Forall_forall. intros ob Hob. cbv beta zeta.
  rewrite (SymCall.obj_range_set_rl r l L ob (SymCall.existsb_false_forall _ _ ob Xo Hob)).
  exact (proj1 (Forall_forall _ _) Hout ob Hob).
Qed.
Lemma outside_all_unlistk : ltac2:(tb__ "0|0|
S7S10S4cS37Q40A1S15R4SdR3A1R1A3S15R5SdS68R4R3A2A1R2A3F_;Fx;Fi;FS;Fr;").
Proof.
  intros r S i x H. unfold unlistk_at. destruct (nth_error (ss_objs S) i) as [ob|] eqn:E; [|exact H]. cbn [ss_objs set_objs].
  rewrite (nth_error_split3 _ _ _ E) in H. unfold outside_all in *. rewrite Forall_app in *. destruct H as [H1 H2]. split; [exact H1|].
  inversion H2; subst. constructor; [|assumption]. exact H3.
Qed.
Lemma apply_axforms_Xb : ltac2:(tb__ "0|0|
S5aS46Sb2A1S5aS0S47S5aA1Sb1R3R2A2S48S5aR1A2A3S1S0S46S51S8S8A2A1S5cR2A1S5cR4A1A3S0S8S5dR2A1S5dR4A1A3A2F_;FA';Fxs;FA;").
Proof.
  intros A xs A' H. rewrite apply_axforms_ref_eq in H. unfold apply_axforms_ref in H. destruct (apply_axformsS (ax_S A) xs) as [S'|]; [|discriminate].
  injection H as <-. destruct A as [S0 X0 b0]. split; reflexivity.
Qed.
Definition lastobj_of (l : list sobj) : option sobj := ltac2:(tb__ "0|0|
S7cS5Vl;SceS4aS5Vl;A2U1A2A3").
Lemma lastobj_eq : ltac2:(tb__ "0|0|
S10S0S47S5A1S67R1A1S97SdR1A1A1A3FS;"). Proof. reflexivity. Qed.

Local Opaque FUEL_T.
Section TailC.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Variables pre suf : list Z.
Variable str : list byte.
Let MSGb : list byte := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.MSGb pre suf str.
Let Kwr : nat -> jpredA := ltac2:(tb__ "0|0|
Sd2VJ0;Vpre;Vsuf;Vstr;A4").
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S7S46S37Q40A1A1S46S88A1S89VJ0;R4R3R2R1A4S0S47S8aA1S8cS8dR2A1SbeA2S48S8aS8bSbeA1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
S4cS79S58Vok;VKwr;R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S4cSd6S58Vok;VKwr;R1A1A3Fk;").
Variable rho : valuation.
Variable tp : list word.
Hypothesis Hstr : ltac2:(tb__ "0|1|
S0S46S37Q8A1M0A1S62G0S4aG0Vstr;A2S9Vrho;P3A2A3Vstr;A3").
Let n : Z := Z.of_nat (length str).
Hypothesis Hn16 : ltac2:(tb__ "0|0|
S0S35S38Q40ScVrho;P10A2A2Vn;A3").
Hypothesis HA3 : ltac2:(tb__ "0|0|
S0S35S3fS4aS37Q8A1S9Vrho;P3A2A2A1S38Q40ScVrho;P11A2A2A3").
Let Kf : nat -> jpredA := ltac2:(tb__ "0|0|
Sd1VJ0;Vpre;Vsuf;Vstr;Vrho;Vtp;A6").
Variable a : Z.
Variable v : positive.
Variables T8 : axst.
Variable o : tailC_out.
Hypothesis Hcert : ltac2:(tb__ "0|0|
S0S47S6cA1S73Vpre;Vsuf;Va;Vv;VT8;A5S48S6cVo;A2A3").
Hypothesis HlT8 : ltac2:(tb__ "0|0|
S0S45S19S5bVT8;A1A1S4fA3").
Hypothesis HnT8 : ltac2:(tb__ "0|0|
S99S8eSaS5bVT8;A1A1A2").
Let b : Z := Z.of_nat (length suf).

Let W1 := tc_W1 o. Let S6 := tc_S6 o. Let L6 := tc_L6 o. Let Cs := tc_Cs o. Let s := tc_s o. Let R := tc_R o. Let T := tc_T o.
Let T1 := tc_T1 o. Let T2 := tc_T2 o. Let T3 := tc_T3 o. Let M := tc_M o. Let W0 := tc_W0 o. Let oA := tc_o o.
Let D6 : sstate := dropL L6.
Let C : axst := ax_setS W1 Cs.

Definition PG0 : Prop := ltac2:(tb__ "0|4|
S1S0S35Va;S3fS4aS35Vpre;A2A1A3S1S3aZ1M0Va;A2S1S3aG0Vb;A2S1S3aVa;Z50M1A2S1S3aVb;G1A2S1S0S45S86S4eS46S6A1M2S64Va;Vv;A2S4eG2S82S4eG2S63Vv;A1S4dG2A1A3A3A3S5bVT8;A1M3A2S49A3S0S47S5A1S7cS5SdG3A1U1A3S48S5S81A2A3A2A2A2A2A2A2").
Definition PG1 : Prop := ltac2:(tb__ "0|5|
S3S5aS5aS1S0S47S5aA1M0S84S66Va;Vv;A2VT8;A2S48S5aR1A2A3S1S0S35S23S5bR1A1M1A1Zd9ad4A3S1S99SaS5bVT8;A1A1SaG1A1M2A2S1S0G0Sb1S85R1S63Vv;A1M3A2S6eA2S48S5aVW1;A2A3S1S0S45S7bS6S6S7fS6S30R1A1S22S5bVW1;A1M4A1A3Lf;G3A3S49A3S1S0S36SaG4A1G2A3S1S0S45S7bS51S8S8A2S69S5cVW1;A1A3S49A3S0S8S5dVW1;A1S11S59A1A3A2A2A2A2A2A2A2LW1';A2").
Definition PG2 : Prop := ltac2:(tb__ "0|9|
S3S5S5S3S46Sc7A1M0G0S1S0S47S10A1S6bVa;S5bVW1;A1M1A2S48S10VS6;A2A3S1S0S47S5A1M2S7cS5SdVS6;A1M3U3A3S48S5R2A2A3S1S0S47G0A1Sc9S1eR2A1S11N1d0M4A1M5Z0S3dVa;A1A4S48G0R1A2A3S1S0S45Sc3R1S6fVpre;A1A2S49A3S1S0S45S9cP5M6VS6;A2S4fA3S1S0S45S9cP6M7VS6;A2S4fA3S1S0S45S1dS14R2A1M8A1S49A3S1S0S45S26G8A1S4fA3S1S0S8S2bR2A1G5A3S1S0S8S2aR2A1S11S3bG4Va;A2A1A3S1S0S45ScbG6G3A2S49A3S1S0S45ScbG7G3A2S49A3S1S0S4cS4aS5G3A2U14A3S1S0G2S67VS6;A1S48S5S81A2A3S0S36SaVS6;A1SaG1A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lbl;A2Lo8;A2").
Definition PG3 : Prop := ltac2:(tb__ "0|2|
S1S0S10VL6;Sd7VS6;U3P5A3A3S1S0S10VCs;SbfVD6;S6aVv;A1A2A3S1S0Sb0Vs;S72Va;Vv;VCs;A3A3S1S0S45Sc2VW1;SaVCs;A1M0A2S49A3S1S0S45S16VCs;A1S49A3S1S0S45S7bS5S65SdVD6;A1A3S49A3S1S0S45S9cP6VD6;A2S4fA3S1S0S36SaVL6;A1SaS5bVW1;A1A1M1A3S1S0S36G0G1A3S1S0S4cS4aS5SdVL6;A1A2U14A3S0S47S5A1S67VL6;A1S48S5S81A2A3A2A2A2A2A2A2A2A2A2A2").
Definition PG4 : Prop := ltac2:(tb__ "0|2|
S1S0S47S46S5A1M0A1Sd4VC;SabVs;A3S48G0VR;A2A3S1S0S45Sd3VC;SabVs;VR;S4eS5aSacS4dS5aA1A3A5S49A3S1S0S8SafVs;PdA2S11Va;A1A3S1S0S8SafVs;PfA2S24Vv;A1A3S1S0S5aVT;Sd5Vs;SabSacVC;VR;A5A3S1S0S45S19S5bVT;A1M1A1S4fA3S99SaVCs;A1SaG1A1A2A2A2A2A2A2A2").
Definition PG5 : Prop := ltac2:(tb__ "0|7|
S3S5S5S1S0S47S5aA1Sb1S85VT;S63Vv;A1A2S4eSb2Sb3S71A1S4dSb2A1A3A2S48S5aVT1;A2A3S1S0S47S5A1M0S7cS5SdSc5S5bVT1;A1M1A1M2A1U1M3A3S48S5R1A2A3S1S0S4cS4aS5SdG1A1A2U14A3S1S0G0S67G1A1S48S5S6aVv;A1A2A3S1S0S17S14R1A1S1aP5A1A3S1S0S36SaG1A1SaS5bVT;A1A1M4A3S1S0S8S5dVT1;A1S11S59A1A3S1S0S45S7bS51S8S8A2S69S5cVT1;A1A3S49A3S1S0S5aVT2;S5eVT1;S68G2G3A2A2A3S1S0S5aVT3;S5eVT2;SbfS5bVT2;A1M5S81A2A2A3S1S0S45S16G5A1S49A3S1S0S45S16S5bVT3;A1M6A1S49A3S1S0S45S7bS5S65SdG5A1A3S49A3S1S0S36SaG5A1G4A3S0S36SaG6A1G4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lob1;A2").
Definition PG6 : Prop := ltac2:(tb__ "0|3|
S1S0S47S5aA1M0Sb1VT3;S6dA2S48S5aVM;A2A3S1S0S45S19S5bVM;A1M1A1S4fA3S1S0S36SaG1A1M2SaS5bVT;A1A1A3S1S0S45S9cP5G1A2S4fA3S1S0S45S9cP6G1A2S4fA3S1S0S47S5A1S7cS5SdG1A1U1A3S48S5S81A2A3S1S0S45Sc2VM;G2A2S49A3S1S0G0S84S66Va;Vv;A2VM;A2S48S5aVW0;A2A3S0S47Sc1A1Sc6S4dS35A1Vsuf;Z0Vb;VT8;VW0;A6S48Sc1VoA;A2A3A2A2A2A2A2A2A2A2").

Lemma osome_eqb_sound : ltac2:(tb__ "0|1|
S47S5A1M0S5S0S45S70R2R1A2S49A3S0G0R3S48S5R2A2A3F_;Fob;Fx;").
Proof. intros [y|] ob H; cbn in H; [|discriminate]. apply sobj_eqb_sound in H. subst. reflexivity. Qed.

Lemma certC : ltac2:(tb__ "0|0|
S1Sa0S1Sa1S1Sa2S1Sa3S1Sa4S1Sa5Sa6A2A2A2A2A2A2").
Proof.
  pose proof Hcert as H. unfold tailC in H. cbn zeta in H. fold b in H.
  destruct ((a =? Z.of_nat (length pre)) && (1 <=? a) && (1 <=? b) && (a <=? 80) && (b <=? 80)
            && fs_ok [FC1 a v; BASEF; FIN v] (ax_S T8) && osome_eqb (nth_error (ss_objs (ax_S T8)) 1) O_strS) eqn:B0; [|discriminate]. cbn [negb] in H.
  destruct (runp (FSC a v) T8) as [W1'|] eqn:EW1'; [|discriminate].
  destruct ((ss_pc (ax_S W1') =? 0xd9ad4) && (ss_next (ax_S T8) <=? ss_next (ax_S W1'))%positive) eqn:B1; [|discriminate]. cbn [negb] in H.
  destruct (apply_axforms (set_facts W1' (FIN v)) XWC) as [W1x|] eqn:EW1; [|discriminate].
  destruct (forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S W1x))) (FIN v) && (ss_next (ax_S W1x) =? ss_next (ax_S W1'))%positive
            && forallb xr_lowb (ax_X W1x) && sv_eqb (ax_base W1x) (SLit SHB)) eqn:B2; [|discriminate]. cbn [negb] in H.
  destruct (splitsC a (ax_S W1x)) as [S6x|] eqn:ES6; [|discriminate].
  destruct (nth_error (ss_objs S6x) 3) as [o8|] eqn:Eo8; [|discriminate].
  destruct (cells_bytes (ob_cells o8) (SLit (-464)) 0 (Z.to_nat a)) as [bl|] eqn:Ebl; [|discriminate].
  destruct (bexps_eqb bl (blC pre) && negb (state_has_rl 5 S6x) && negb (state_has_rl 6 S6x) && dflt_writable (ob_dflt o8) && negb (is_arr (ob_dflt o8))
           && sv_eqb (ob_lo o8) (SLit (-464)) && sv_eqb (ob_hi o8) (SLit (-464 + a)) && exts_rl_free 5 (ss_objs S6x) && exts_rl_free 6 (ss_objs S6x)
           && (length (ss_objs S6x) =? 20)%nat && osome_eqb (lastobj S6x) O_strS && (ss_next S6x =? ss_next (ax_S W1x))%positive) eqn:B3; [|discriminate]. cbn [negb] in H.
  destruct (x_ok W1x (ss_next (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v))) && swf (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v))
           && forallb obj_lowb (ss_objs (dropL (obj_to_list S6x 3 5))) && negb (state_has_rl 6 (dropL (obj_to_list S6x 3 5))) && (ss_next (obj_to_list S6x 3 5) =? ss_next (ax_S W1x))%positive
           && (ss_next (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v)) =? ss_next (ax_S W1x))%positive && (length (ss_objs (obj_to_list S6x 3 5)) =? 20)%nat
           && osome_eqb (lastobj (obj_to_list S6x 3 5)) O_strS) eqn:B4; [|discriminate]. cbn [negb] in H.
  destruct (entails_frA (ax_setS W1x (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v))) WLerrS.Pre_wl2 (subC1 a v (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v)))) as [Rx|] eqn:ER; [|discriminate].
  match type of H with (if negb ?c then None else _) = _ => destruct c eqn:B5; [|discriminate] end. cbn [negb] in H.
  match type of H with (if ?c then None else _) = _ => destruct c eqn:B6; [discriminate|] end.
  match type of H with (match apply_axforms ?x ?y with _ => _ end) = _ => destruct (apply_axforms x y) as [T1x|] eqn:ET1; [|discriminate] end.
  destruct (nth_error (ss_objs (dropL (ax_S T1x))) 1) as [ob1|] eqn:Eob1; [|discriminate].
  match type of H with (if negb ?c then None else _) = _ => destruct c eqn:B7; [|discriminate] end. cbn [negb] in H.
  match type of H with (if negb ?c then None else _) = _ => destruct c eqn:B8; [|discriminate] end. cbn [negb] in H.
  match type of H with (match apply_axforms ?x ?y with _ => _ end) = _ => destruct (apply_axforms x y) as [Mx|] eqn:EM; [|discriminate] end.
  match type of H with (if ?c then None else _) = _ => destruct c eqn:B9; [discriminate|] end.
  destruct (runp (FSC a v) Mx) as [W0x|] eqn:EW0; [|discriminate].
  match type of H with (match tailA_post ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 with _ => _ end) = _ => destruct (tailA_post p1 p2 p3 p4 p5 p6) as [oAx|] eqn:EoA; [|discriminate] end.
  injection H as Eo.
  assert (EW1v : W1 = W1x) by (unfold W1; rewrite <- Eo; reflexivity).
  assert (ES6v : S6 = S6x) by (unfold S6; rewrite <- Eo; reflexivity).
  assert (EL6v : L6 = obj_to_list S6x 3 5) by (unfold L6; rewrite <- Eo; reflexivity).
  assert (ECsv : Cs = app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v)) by (unfold Cs; rewrite <- Eo; reflexivity).
  assert (Esv : s = subC1 a v (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v))) by (unfold s; rewrite <- Eo; reflexivity).
  assert (ERv : R = Rx) by (unfold R; rewrite <- Eo; reflexivity).
  assert (ETv : T = import_postA (subC1 a v (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v))) WLerrS.Pre_wl2 WLerrS.D
                                  (ax_setS W1x (app_obj (dropL (obj_to_list S6x 3 5)) (O_strR v))) Rx) by (unfold T; rewrite <- Eo; reflexivity).
  assert (ET1v : T1 = T1x) by (unfold T1; rewrite <- Eo; reflexivity).
  assert (ET2v : T2 = ax_setS T1x (unlistk_at (dropL (ax_S T1x)) 1)) by (unfold T2; rewrite <- Eo; reflexivity).
  assert (ET3v : T3 = ax_setS (ax_setS T1x (unlistk_at (dropL (ax_S T1x)) 1)) (app_obj (ax_S (ax_setS T1x (unlistk_at (dropL (ax_S T1x)) 1))) O_strS)) by (unfold T3; rewrite <- Eo; reflexivity).
  assert (EMv : M = Mx) by (unfold M; rewrite <- Eo; reflexivity).
  assert (EW0v : W0 = W0x) by (unfold W0; rewrite <- Eo; reflexivity).
  assert (EoAv : oA = oAx) by (unfold oA; rewrite <- Eo; reflexivity).
  clear Eo.
  repeat match goal with H : (_ && _) = true |- _ => let H1 := fresh "Q" in let H2 := fresh "Q" in apply andb_prop in H; destruct H as [H1 H2] end.
  apply Bool.orb_false_iff in B6 as [B6a B6b].
  apply Bool.orb_false_iff in B9 as [B9 B9f]. apply Bool.orb_false_iff in B9 as [B9 B9e].
  apply Bool.orb_false_iff in B9 as [B9 B9d]. apply Bool.orb_false_iff in B9 as [B9 B9c]. apply Bool.orb_false_iff in B9 as [B9a B9b].
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  | H : Pos.leb _ _ = true |- _ => apply Pos.leb_le in H
  | H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H
  | H : osome_eqb _ _ = true |- _ => apply osome_eqb_sound in H
  | H : dflt_eqb _ _ = true |- _ => apply dflt_eqb_sound in H
  | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
  | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
  end.
  repeat match goal with
  | H : Pos.leb _ _ = true |- _ => apply Pos.leb_le in H
  | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
  end.
  unfold PG0, PG1, PG2, PG3, PG4, PG5, PG6, D6, C.
  rewrite ?EW1v, ?ES6v, ?EL6v, ?ECsv, ?Esv, ?ERv, ?ETv, ?ET1v, ?ET2v, ?ET3v, ?EMv, ?EW0v, ?EoAv.
  split; [repeat split; assumption|].
  split; [exists W1'; repeat split; assumption|].
  split; [exists o8, bl; repeat split; assumption|].
  split; [repeat split; first [assumption | reflexivity]|].
  split; [repeat split; first [assumption | reflexivity]|].
  split; [exists ob1; repeat split; first [assumption | reflexivity]|].
  repeat split; first [assumption | reflexivity].
Qed.

Lemma split_last20 : ltac2:(tb__ "0|1|
S46S5A1M0S5S0S4cS4aS5R2A2U14A3S0S47S5A1S97R3A1S48S5R2A2A3S0G0R4S4bS5S62S5U13R4A3S4eS5R3S4dS5A1A3A3A3F_;F_;Fx;Fl;").
Proof.
  intros l x Hl Hn. unfold lastobj_of in Hn. rewrite Hl in Hn. change (20 - 1)%nat with 19%nat in Hn.
  rewrite (nth_error_split3 l 19 x Hn) at 1. replace (skipn 20 l) with (@nil sobj); [reflexivity|]. symmetry. apply skipn_all2. lia.
Qed.
Lemma FC_norl : ltac2:(tb__ "0|0|
S0S45S7bS6S6S56S57S9dP5R1A2S9dP6R1A2A2A1Lp;S4bS6S64Va;Vv;A2S4bS6S82S63Vv;A1A3A3A3S49A3").
Proof. reflexivity. Qed.
Lemma Forall_holds_set_rl56 : ltac2:(tb__ "0|0|
S7S36S46S37Q8A1A1S46S6A1S4S0S36R3P5A3S0S36R3P6A3A2S7dS6R2S4bS6S64Va;Vv;A2S4bS6S82S63Vv;A1A3A3A3S5fS6SfR6A1R3A3S5fS6SfS9bR7R6R5A3A1R4A3F_;F_;F_;FF;FL;Fl;Fr;").
Proof.
  intros r l L F Hl Hincl HF. apply Forall_forall. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) FC_norl p (Hincl p Hp)) as X. cbn beta in X. apply Bool.negb_true_iff in X. apply Bool.orb_false_iff in X as [X5 X6].
  apply (proj2 (SymCall.holds_set_rl r l L p ltac:(destruct Hl as [-> | ->]; assumption))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.
Lemma Forall_holds_absorb : ltac2:(tb__ "0|0|
S7S46S5A1S8fS46S6A1S5fS6SfR4A1R1A3S5fS6SfSaeR5R4R3A3A1R2A3F_;FF;Fm;FRr;Fr;").
Proof. intros r Rr m F HF. apply Forall_forall. intros p Hp. apply holds_absorb. exact (proj1 (Forall_forall _ _) HF p Hp). Qed.
Lemma Forall_holds_set_rm : ltac2:(tb__ "0|0|
S7S37Q40A1S47S37Q8A1A1F_;S46S6A1S5fS6SfR3A1R1A3S5fS6SfSadR4R3A2A1R2A3F_;FF;Fm;Fr;").
Proof. intros r m F HF. apply Forall_forall. intros p Hp. apply holds_set_rm. exact (proj1 (Forall_forall _ _) HF p Hp). Qed.
Lemma incl_FIN : ltac2:(tb__ "0|1|
S7dS6S63Vv;A1M0S4bS6S64Va;Vv;A2S4bS6S82G0A3A3A3"). Proof. intros p Hp. rewrite !in_app_iff. right. right. exact Hp. Qed.
Lemma incl_FC1 : ltac2:(tb__ "0|1|
S7dS6S64Va;Vv;A2M0S4bS6G0S4bS6S82S63Vv;A1A3A3A3"). Proof. intros p Hp. rewrite !in_app_iff. left. exact Hp. Qed.
Lemma incl_BASEF : ltac2:(tb__ "0|0|
S7dS6S82S4bS6S64Va;Vv;A2S4bS6S82S63Vv;A1A3A3A3"). Proof. intros p Hp. rewrite !in_app_iff. right. left. exact Hp. Qed.
Lemma FIN_fps : ltac2:(tb__ "0|0|
S7S5fS6SfR1A1S63Vv;A1A3S5fS6SfR2A1S83A3F_;Fr;").
Proof. intros r H. exact (Forall_inv_tail (Forall_inv_tail H)). Qed.
Lemma FIN_v : ltac2:(tb__ "0|0|
S7S5fS6SfR1A1S63Vv;A1A3S0S37Q40A1ScR2Vv;A2ScR2P10A2A3F_;Fr;").
Proof. intros r H. pose proof (Forall_inv H) as X. cbn [holds eval] in X. exact X. Qed.

Definition rhoC_of (rhoW : valuation) (ms : machine_state) (md : Model) : valuation := ltac2:(tb__ "0|1|
S9bSaeS9bVrhoW;P5S61S35S37Q8M0A1S39G0A1Vpre;A4A3S4eS5S81S4dS5A1A3SbcVmd;Vtp;Vms;A3A3P6Vstr;A3").

Lemma reshape1 : ltac2:(tb__ "0|b|
S7S46S88A1M0S8fS89S13S8eVrho;R4A3S5fS6SfR5A1S63Vv;A1A3S75S58VKf;U0A1M1VW1;R6Vtp;S50G0S93R5S94R4R3A2A4A6S1S75S58G1VC;S9fR7R5R4A3Vtp;S50G0S93R6S94R5R4A2A4A6S1S35S1S3aZ0M2R1A2S3cR1S38Q40M3ScVrho;P11A2A2M4A2A2S0S47S37Q8M5A1M6A1M7SbS9fR9R7R6A3M8S39G3S3bS38G3SeR9S80A2A2R2A2A2A2S48G6S60G6S3dR2A1S9Vrho;P3A2S39G5G2A2A4A2A3F_;Foff;S37G3A1S2S1S3aS38G3SeR8S80A2A2M9S38G3R1A2MaA2S3cGaS3bG9G4A2A2A2A1S0G7SbG8R2A2SbR9R2A2A3F_;Fz;A2A2F_;F_;F_;Fmd;Fms;Ftr;FrhoW;").
Proof.
  intros rhoW tr ms md HagW HFW Hsp.
  destruct certC as (G0 & G1 & G2 & G3 & _).
  destruct G0 as (Ha & Ha1 & Hb1 & Ha80 & Hb80 & HLok & HstrS8).
  destruct G1 as (W1' & EW1' & HpcW1 & HnW1' & EW1 & HfinW1 & HnW1 & HxW1 & HbW1).
  destruct G2 as (o8 & bl & ES6 & Eo8 & Ebl & Bbl & Hrl5 & Hrl6 & Hw8 & Ha8 & Hlo8 & Hhi8 & Hx5 & Hx6 & Hlen6 & Hlast6 & Hn6).
  destruct G3 as (EL6 & ECs & Es & Hxok & HswfCs & Hlow6 & Hrl6D & HnL6 & HnCs & HlenL6 & HlastL6).
  pose proof (LOWV_of_facts rhoW (FIN_fps rhoW HFW)) as HL. pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6').
  destruct (str_factsZ rhoW (proj2 (proj1 (Forall_app _ _ _) (FIN_fps rhoW HFW)))) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _).
  assert (E16 : rw rhoW 16 = rw rho 16) by (destruct HagW as (A & _ & _); symmetry; apply A; reflexivity).
  assert (E17 : rw rhoW 17 = rw rho 17) by (destruct HagW as (A & _ & _); symmetry; apply A; reflexivity).
  assert (Hrl3 : rl rhoW 3 = rl rho 3) by (destruct HagW as (_ & LW & _); rewrite <- (LW 3%positive); reflexivity).
  pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  assert (HnA : n + 8 <= bv_unsigned (rw rho 17)) by (rewrite <- Hn16, <- E16, <- E17; pose proof Z1; lia).
  assert (HA62 : bv_unsigned (rw rho 17) <= 2 ^ 62) by (rewrite <- E17; exact Z2).
  pose proof (urange (rw rhoW 18)) as R18. pose proof (urange (rw rhoW 19)) as R19. pose proof (urange (rw rhoW 20)) as R20. pose proof (urange (eval rhoW sX)) as RsX.

  pose proof (splitsC_SPA _ a W1 S6 rhoW tp _ ES6 Hsp) as H6.

  unfold x_ok in Hxok. apply andb_prop in Hxok as [Hxok Hbase]. apply andb_prop in Hxok as [Hnorl Hxb]. apply sv_eqb_sound in Hbase.
  assert (Hbl : map (beval rhoW) bl = map (Z_to_bv 8) pre).
  { apply bexps_eqb_sound in Bbl. rewrite Bbl. unfold blC. apply map_beval_lit. }
  set (rho5 := rho_set_rl rhoW 5 (map (Z_to_bv 8) pre)).
  assert (H7 : SPA segs (Kf 0) (ax_setS W1 L6) rho5 tp (tr, mkCfg ms md)).
  { eapply (SPA_morphX (Kf 0) (Kf 0) (ax_setS W1 S6) L6 rhoW rho5 tp _).
    - cbn [ax_X ax_base ax_setS]. rewrite HnL6, <- HnCs, Hxb, Hbase. reflexivity.
    - cbn [ax_base ax_setS]. rewrite Hbase. reflexivity.
    - cbn [ax_X ax_setS]. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hnorl r Hr) as X0. unfold xr_norl in X0.
      apply Bool.negb_true_iff in X0. apply Bool.orb_false_iff in X0 as [X0 X4]. apply Bool.orb_false_iff in X0 as [X0 X3]. apply Bool.orb_false_iff in X0 as [X1 X2].
      unfold rho5. split; rewrite !SymCall.eval_set_rl by assumption; reflexivity.
    - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [|reflexivity].
      rewrite EL6. unfold rho5. apply (outside_all_exts_rl _ 5 _ (ss_objs S6)); [apply obj_to_list_ext | exact Hx5 | exact Hout].
    - intros Hsm. rewrite EL6. unfold rho5. rewrite <- Hbl.
      exact (smatch_obj_to_list segs _ S6 (virt tp (tr, mkCfg ms md)) 3 5 o8 (-464) (-464 + a) bl Hsm Eo8 Hlo8 Hhi8
               ltac:(lia) ltac:(lia) Hw8 Ha8 ltac:(replace (Z.to_nat (-464 + a - -464)) with (Z.to_nat a) by lia; exact Ebl) Hrl5).
    - intros HK. exact HK.
    - exact H6. }

  assert (EobjL6 : ss_objs (ax_S (ax_setS W1 L6)) = firstn 19 (ss_objs L6) ++ [O_strS]).
  { cbn [ax_S ax_setS]. apply split_last20; [exact HlenL6 | rewrite <- lastobj_eq; exact HlastL6]. }
  assert (ED6 : set_objs L6 (firstn 19 (ss_objs L6)) = D6) by (unfold D6, dropL; rewrite HlenL6; reflexivity).
  pose proof (SPA_unobj segs (Kf 0) rho5 (ax_setS W1 L6) (firstn 19 (ss_objs L6)) [O_strS] tp tr ms md EobjL6 H7
                (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_inv J0 pre suf str rho tp 0 _ _ _ _ _)) as H8.
  cbn zeta in H8. rewrite ax_setS_setS in H8. cbn [ax_S ax_setS] in H8. rewrite ED6 in H8.
  set (rhoA := rho_absorb rho5 [O_strS] (vms md tp ms)) in H8.
  assert (RNG : obj_range rho5 O_strS = (bv_unsigned (eval rhoW sX), bv_unsigned (eval rhoW sX) + bv_unsigned (rw rho 17))).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_strS. cbn [ob_base ob_lo ob_hi fst snd]. unfold rho5. rewrite SymCall.eval_set_rl by reflexivity.
    rewrite !SymCall.soff_set_rl by reflexivity. rewrite soff_lit_small by lia. unfold soff. cbn [eval]. rewrite E17, signed_small by lia. f_equal; lia. }
  assert (HREL : forall off, 0 <= off < bv_unsigned (rw rho 17) ->
             rm rhoA (Z_to_bv 64 (bv_unsigned (eval rhoW sX) + off)) = Some (nth (Z.to_nat off) (rl rho 3) (Z_to_bv 8 0))).
  { intros off Hoff.
    pose proof (released_listA rho5 (ax_setS W1 L6) (firstn 19 (ss_objs L6)) O_strS tp tr ms md 3 EobjL6 (proj1 H7) eq_refl eq_refl
                  ltac:(rewrite RNG; cbn [fst]; lia) ltac:(rewrite RNG; cbn [snd]; lia) off) as X.
    cbn zeta in X. fold rhoA in X.
    replace (obj_lo_of rho5 O_strS) with 0 in X by (unfold obj_lo_of, O_strS; cbn [ob_lo]; symmetry; apply soff_lit_small; lia).
    replace (obj_hi_of rho5 O_strS) with (bv_unsigned (rw rho 17)) in X
      by (unfold obj_hi_of, soff, O_strS; cbn [ob_hi eval]; unfold rho5; cbn [rw rho_set_rl]; rewrite E17; symmetry; apply signed_small; lia).
    replace (eval rho5 (ob_base O_strS)) with (eval rhoW sX) in X by (unfold rho5, O_strS; cbn [ob_base]; symmetry; apply SymCall.eval_set_rl; reflexivity).
    replace (rl rho5 3) with (rl rho 3) in X by (unfold rho5; cbn [rl rho_set_rl]; symmetry; exact Hrl3).
    rewrite Z.sub_0_r in X. exact (X Hoff). }
  assert (HOUT : forall z, ~ (bv_unsigned (eval rhoW sX) <= bv_unsigned z < bv_unsigned (eval rhoW sX) + bv_unsigned (rw rho 17)) -> rm rhoA z = rm rhoW z).
  { intros z Hz. unfold rhoA, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho5 [O_strS] z) as [Hin|]; [|reflexivity].
    exfalso. destruct Hin as (ob & [<-|[]] & Hr). rewrite RNG in Hr. cbn [fst snd] in Hr. exact (Hz Hr). }

  set (rho6 := rho_set_rl rhoA 6 str).
  assert (HF5 : Forall (holds rho5) (FIN v)) by (unfold rho5; apply Forall_holds_set_rl56; [left; reflexivity | apply incl_FIN | exact HFW]).
  assert (HF6 : Forall (holds rho6) (FIN v)).
  { unfold rho6. apply Forall_holds_set_rl56; [right; reflexivity | apply incl_FIN |]. unfold rhoA. apply Forall_holds_absorb. exact HF5. }
  pose proof (LOWV_of_facts rho6 (FIN_fps rho6 HF6)) as HL6.
  assert (H9 : SPA segs (Kf 0) (ax_setS W1 D6) rho6 tp (tr, mkCfg ms md)).
  { rewrite <- (ax_setS_setS W1 D6 D6).
    eapply (SPA_morphX (Kf 0) (Kf 0) (ax_setS W1 D6) D6 rhoA rho6 tp _).
    - cbn [ax_X ax_base ax_setS]. replace (ss_next D6) with (ss_next Cs) by (rewrite ECs; reflexivity). rewrite Hxb, Hbase. reflexivity.
    - cbn [ax_base ax_setS]. rewrite Hbase. reflexivity.
    - cbn [ax_X ax_setS]. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hnorl r Hr) as X0. unfold xr_norl in X0.
      apply Bool.negb_true_iff in X0. apply Bool.orb_false_iff in X0 as [X0 X4]. apply Bool.orb_false_iff in X0 as [X0 X3]. apply Bool.orb_false_iff in X0 as [X1 X2].
      unfold rho6. split; rewrite !SymCall.eval_set_rl by assumption; reflexivity.
    - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [|reflexivity]. unfold rho6. apply outside_all_set_rl_state; [exact Hrl6D | exact Hout].
    - intros Hsm. unfold rho6. apply SymCall.smatch_set_rl; [exact Hrl6D | exact Hsm].
    - intros HK. exact HK.
    - exact H8. }

  assert (EsX6 : eval rho6 sX = eval rhoW sX) by (unfold rho6, rhoA, rho5; rewrite SymCall.eval_set_rl, eval_absorb, SymCall.eval_set_rl by reflexivity; reflexivity).
  assert (Ev6 : rw rho6 v = rw rho 16) by (rewrite (FIN_v rho6 HF6); unfold rho6, rhoA, rho5; cbn [rw rho_set_rl rho_absorb]; exact E16).
  assert (HC : SPA segs (Kf 0) C rho6 tp (tr, mkCfg ms md)).
  { unfold C. rewrite ECs. rewrite <- (ax_setS_setS W1 D6 (app_obj D6 (O_strR v))).
    apply (SPA_carve_listobj (Kf 0) rho6 (ax_setS W1 D6) tp (tr, mkCfg ms md) sX (SVar v) n (DRom 6) 6 (ss_next D6) H9 eq_refl).
    - pose proof HswfCs as Wf. rewrite ECs in Wf. exact Wf.
    - apply Pos.le_refl.
    - unfold soff. cbn [eval]. rewrite Ev6, signed_small by lia. exact Hn16.
    - lia.
    - lia.
    - rewrite EsX6. lia.
    - unfold rho6. cbn [rl rho_set_rl]. rewrite Pos.eqb_refl. reflexivity.
    - cbn [ax_S ax_setS]. apply objs_lowb_disjoint; [exact HL6 | exact Hlow6 | lia].
    - intros off Hoff D. discriminate D.
    - intros off Hoff. rewrite EsX6. rewrite rd_of_high by (rewrite u64_of_sum by lia; lia).
      unfold rho6. cbn [rm rl rho_set_rl]. rewrite Pos.eqb_refl. rewrite (HREL off) by lia.
      f_equal. rewrite <- Hstr. rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat off) (length str)); [reflexivity | lia].
    - intros z Hz. rewrite EsX6 in Hz. unfold rho6. cbn [rm rho_set_rl].
      pose proof (HREL (z - bv_unsigned (eval rhoW sX))) as X. replace (bv_unsigned (eval rhoW sX) + (z - bv_unsigned (eval rhoW sX))) with z in X by lia.
      rewrite (X ltac:(lia)). discriminate.
    - cbn [ax_X ax_base ax_setS]. rewrite EsX6. apply (xr_lowb_clear rho6 W1); [exact HL6 | exact HxW1 | exact Hbase | lia]. }
  split; [exact HC|]. split.
  - intros off Hoff. unfold rhoC_of. fold rho5. fold rhoA. cbn [rm rho_set_rl]. exact (HREL off Hoff).
  - intros z Hz. unfold rhoC_of. fold rho5. fold rhoA. cbn [rm rho_set_rl]. rewrite (HOUT z Hz). unfold rho5. reflexivity.
Qed.

Hypothesis Hnmax : n <= 131071.
Let bs1 : list byte := map (Z_to_bv 8) pre.
Let k1 : nat := ltac2:(tb__ "0|0|
ScdS4aS35Vpre;A2S4aS37Q8A1Vstr;A2A2").
Definition WLF1 (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S0S46S37Q8A1A1M0S9Vr;P5A2Vbs1;A3S1S0G0S9Vr;P6A2Vstr;A3S1S0S35S38Q40M1ScVr;PdA2A2Va;A3S0S35S38G1ScVr;PfA2A2Vn;A3A2A2A2").
Definition Jp1 : jpredA := ltac2:(tb__ "0|0|
S7S46S37Q40A1A1S46S88A1S89S1Sa8R4A1VKf;U0R4R3R2R1A5A2Lmd;Ltr;Lt;Lr;").
Lemma Jp1_stable : stableA segs 92 Jp1.
Proof.
  intros r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0%nat 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF1.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.
Lemma bs1_len : ltac2:(tb__ "0|0|
S0S4cS4aS37Q8A1Vbs1;A2S4aS35Vpre;A2A3"). Proof. unfold bs1. apply length_map. Qed.
Lemma Kw_Jp1_Kf : ltac2:(tb__ "0|0|
S4cS7S46S37Q40A1A1S46S88A1S89Sb4S9eVbs1;Vstr;R5R4R3R2R1A8VKf;Sd8R6Vk1;A2R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;Fk;").
Proof.
  intros k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLerr.TRk, WLerr.MSG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.EVS, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.MSGb. cbn [firstn map]. rewrite <- app_assoc. f_equal. f_equal. fold bs1.
  assert (L : length (bs1 ++ str) = k1) by (unfold k1; rewrite length_app, bs1_len; reflexivity).
  rewrite app_assoc, (firstn_app (Nat.min k k1)). rewrite L. replace (Nat.min k k1 - k1)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  rewrite <- L, <- firstn_firstn, firstn_all. reflexivity.
Qed.
Lemma wl1_MSG_len : ltac2:(tb__ "0|0|
S0S4cS4aS37Q8A1Sb5Vbs1;Vstr;A2A2Vk1;A3").
Proof. unfold WLerr.MSG, k1. rewrite length_app, bs1_len. reflexivity. Qed.
Lemma wl_call1 : ltac2:(tb__ "0|0|
S7S46S37Q40A1A1Sb9S58Vok;S75S58S9eSabR2R1A5S76S58Sb4S9eVbs1;Vstr;S4aS37Q8A1Sb5Vbs1;Vstr;A2A2A4P5cR2R1Sb6A6A4Ftp2;Frho2;").
Proof.
  intros rho2 tp2. destruct certC as ((Ha & Ha1 & _ & Ha80 & _) & _).
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ Jp1); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLerr.wl2_sum ok Jp1 rho2 tp2 bs1 str A5 A6).
  - rewrite A13, bs1_len. lia.
  - rewrite A15. reflexivity.
  - rewrite wl1_MSG_len. unfold k1, max_write_total. unfold n in Hnmax. lia.
  - apply Jp1_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK rho tp _ r t tr0 ms md0 msv' (Kw_Jp1_Kf k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okP ok J0 pre suf str HokP rho tp _ r t tr0 ms md0 x8 (Kw_Jp1_Kf k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - rewrite bs1_len. lia.
Qed.
Lemma wl_call1_ex : ltac2:(tb__ "0|0|
S7S46S37Q40A1A1Sb8S58S75S58S9eSabR2R1A5S76S58Sb4S9eVbs1;Vstr;S4aS37Q8A1Sb5Vbs1;Vstr;A2A2A4P5cR2R1Sb6A6A3Ftp2;Frho2;").
Proof.
  intros rho2 tp2 w Hw. destruct certC as ((Ha & Ha1 & _ & Ha80 & _) & _). pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLerr.wl2_sum_ex Jp1 rho2 tp2 bs1 str A5 A6).
  - rewrite A13, bs1_len. lia.
  - rewrite A15. reflexivity.
  - rewrite wl1_MSG_len. unfold k1, max_write_total. unfold n in Hnmax. lia.
  - apply Jp1_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - rewrite bs1_len. lia.
  - exact Hw.
Qed.

Definition mrest (rU : valuation) (lo hi : Z) : word -> option byte := ltac2:(tb__ "0|2|
S37Q40M0A1S45S47S37Q8A1A1L_;S55S41Vlo;S38G0R1A2M1A2S42G1Vhi;A2A2SbVrho;R1A2SbVrU;R1A2X45x2Lz;").
Definition rhoM_of (rho' : valuation) (ms : machine_state) (md : Model) : valuation := ltac2:(tb__ "0|3|
SaeVrho';S4eS5S6aVv;A1S4dS5A1A3SbcVmd;Vtp;Vms;A3A3S7S38Q40M0SeVrho';S80A2A2S35S9bS9bSadR2Sa9R2R1S3bR1S38G0ScVrho;P11A2A2A2A3A2P5M1S9Vrho;G1A2A3P6M2S9Vrho;G2A2A3Tlo;TrU;").
Let FA (r : valuation) : Prop := ltac2:(tb__ "0|0|
S5fS6SfVr;A1S4bS6S64Va;Vv;A2S4bS6S82S63Vv;A1A3A3A3").
Lemma FA_FIN : ltac2:(tb__ "0|0|
S7VFA;R1A1S5fS6SfR2A1S63Vv;A1A3F_;Fr;").
Proof. intros r H. unfold FA in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [_ H]. exact H. Qed.

Lemma reshape2 : ltac2:(tb__ "0|d|
S4cS7S46S88A1M0S8fS89VFA;R4A1S0S45S7bS6S21SaS5bVT;A1A1A1S63Vv;A1A3S49A3S36S9aR1S8eA2S0S37Q40M1A1M2ScR8R2A2ScVrho;R2A2A3F_;Fi;S36S2S0S36R1P5A3A1S2S0S36R2P6M3A3A1S0S46S37Q8M4A1M5A1M6S9RaR3A2S9Vrho;R3A2A3F_;F_;Fl;S0G6S9R8G3A2Vstr;A3S35S1S3aZ0M7R1A2S3cR1S38G1ScVrho;P11A2A2M8A2A2S0S47G5A1M9SbRbS39G1S3bS38G1SeRbS80A2A2MaR2A2A2A2S48G5S60G5S3dR2A1S9Vrho;P3A2S39G4G7A2A4A2A3F_;Foff;G2S2S1S3aGaS38G1R1A2MbA2S3cGbS3bGaG8A2A2A2A1S0G9SbRcR2A2SbVrho;R2A2A3F_;Fz;S75S58VKf;RcA1VT;RbVtp;S50G0S93RaS94R9R8A2A4A6S1S75S58VKf;RdA1VM;SaaRcRaR9A3McVtp;S50G0S93RbS94RaR9A2A4A6S1S13S8eVrho;GcA3VFA;GcA1A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho';Fk;").
Proof.
  intros k rho' tr ms md HFA HbFIN Hrw Hrl Hrl6 Hrm_in Hrm_out Hsp.
  destruct certC as (G0 & _ & _ & _ & G4 & G5 & G6).
  destruct G0 as (Ha & Ha1 & Hb1 & Ha80 & Hb80 & HLok & HstrS8).
  destruct G5 as (ob1 & ET1 & Eob1 & HlenT1 & HlastT1 & Hdob1 & HnT1 & HbT1 & HxT1 & ET2 & ET3 & Hswf2 & Hswf3 & Hlow2 & HnT2 & HnT3).
  destruct G6 as (EM & HlM & HnM & Hrl5M & Hrl6M & HstrM & HxokM & EW0 & HoA).
  pose proof (FA_FIN rho' HFA) as HFIN'. pose proof (LOWV_of_facts rho' (FIN_fps rho' HFIN')) as HL'. pose proof HL' as (L1 & L2 & L3 & L4 & L5 & L6').
  destruct (str_factsZ rho' (proj2 (proj1 (Forall_app _ _ _) (FIN_fps rho' HFIN')))) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _).
  pose proof (Hrw 16%positive ltac:(reflexivity)) as E16. pose proof (Hrw 17%positive ltac:(reflexivity)) as E17.
  pose proof (Hrl 3%positive ltac:(lia) ltac:(lia)) as Hrl3.
  pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho' 18)) as R18. pose proof (urange (rw rho' 19)) as R19. pose proof (urange (rw rho' 20)) as R20. pose proof (urange (eval rho' sX)) as RsX.
  assert (HnA : n + 8 <= bv_unsigned (rw rho 17)) by (rewrite <- Hn16, <- E16, <- E17; pose proof Z1; lia).
  assert (HA62 : bv_unsigned (rw rho 17) <= 2 ^ 62) by (rewrite <- E17; exact Z2).
  assert (Ev' : rw rho' v = rw rho 16) by (rewrite (FIN_v rho' HFIN'); exact E16).

  pose proof (SPA_set_facts (Kf k) T (FIN v) rho' tp _ HFIN' HbFIN Hsp) as H1.
  pose proof (SPA_axforms segs (Kf k) [AXSelect selR] rho' _ T1 tp _ ET1 H1) as H2.

  assert (EobjT1 : ss_objs (ax_S T1) = firstn 19 (ss_objs (ax_S T1)) ++ [O_strR v]).
  { apply split_last20; [exact HlenT1 | rewrite <- lastobj_eq; exact HlastT1]. }
  assert (ED1 : set_objs (ax_S T1) (firstn 19 (ss_objs (ax_S T1))) = dropL (ax_S T1)) by (unfold dropL; rewrite HlenT1; reflexivity).
  pose proof (SPA_unobj segs (Kf k) rho' T1 (firstn 19 (ss_objs (ax_S T1))) [O_strR v] tp tr ms md EobjT1 H2
                (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_inv J0 pre suf str rho tp k _ _ _ _ _)) as H3.
  cbn zeta in H3. rewrite ED1 in H3.
  set (rhoU := rho_absorb rho' [O_strR v] (vms md tp ms)) in H3.
  assert (RNG : obj_range rho' (O_strR v) = (bv_unsigned (eval rho' sX), bv_unsigned (eval rho' sX) + n)).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_strR. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia. unfold soff. cbn [eval]. rewrite Ev', signed_small by lia. rewrite Hn16. f_equal; lia. }
  assert (HREL : forall off, 0 <= off < n -> rm rhoU (Z_to_bv 64 (bv_unsigned (eval rho' sX) + off)) = Some (nth (Z.to_nat off) (rl rho 3) (Z_to_bv 8 0))).
  { intros off Hoff.
    pose proof (released_listA rho' T1 (firstn 19 (ss_objs (ax_S T1))) (O_strR v) tp tr ms md 6 EobjT1 (proj1 H2) eq_refl eq_refl
                  ltac:(rewrite RNG; cbn [fst]; lia) ltac:(rewrite RNG; cbn [snd]; unfold n in *; lia) off) as X.
    cbn zeta in X. fold rhoU in X.
    replace (obj_lo_of rho' (O_strR v)) with 0 in X by (unfold obj_lo_of, O_strR; cbn [ob_lo]; symmetry; apply soff_lit_small; lia).
    replace (obj_hi_of rho' (O_strR v)) with n in X by (unfold obj_hi_of, soff, O_strR; cbn [ob_hi eval]; rewrite Ev', signed_small by lia; symmetry; exact Hn16).
    change (eval rho' (ob_base (O_strR v))) with (eval rho' sX) in X. rewrite Hrl6, Z.sub_0_r in X.
    rewrite (X Hoff). f_equal. rewrite <- Hstr. rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat off) (length str)); [reflexivity | unfold n in Hoff; lia]. }
  assert (HOUT : forall z, ~ (bv_unsigned (eval rho' sX) <= bv_unsigned z < bv_unsigned (eval rho' sX) + n) -> rm rhoU z = rm rho' z).
  { intros z Hz. unfold rhoU, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' [O_strR v] z) as [Hin|]; [|reflexivity].
    exfalso. destruct Hin as (ob & [<-|[]] & Hr). rewrite RNG in Hr. cbn [fst snd] in Hr. exact (Hz Hr). }
  assert (HFU : FA rhoU) by (unfold rhoU; apply Forall_holds_absorb; exact HFA).
  pose proof (LOWV_of_facts rhoU (FIN_fps rhoU (FA_FIN rhoU HFU))) as HLU.

  assert (H4 : SPA segs (Kf k) T2 rhoU tp (tr, mkCfg ms md)).
  { rewrite ET2. rewrite <- (ax_setS_setS T1 (dropL (ax_S T1))).
    eapply (SPA_morphX (Kf k) (Kf k) (ax_setS T1 (dropL (ax_S T1))) _ rhoU rhoU tp _); [ | reflexivity | intros r Hr; split; reflexivity | | | intros HK; exact HK | exact H3].
    - cbn [ax_X ax_base ax_setS]. pose proof Hswf2 as W2. rewrite ET2 in W2. cbn [ax_S ax_setS] in W2.
      destruct (proj1 H3) as (_ & _ & Hwf & _). unfold axwf in Hwf. cbn [ax_S ax_X ax_base ax_setS] in Hwf.
      replace (ss_next (unlistk_at (dropL (ax_S T1)) 1)) with (ss_next (dropL (ax_S T1))); [exact Hwf|].
      unfold unlistk_at. destruct (nth_error (ss_objs (dropL (ax_S T1))) 1); reflexivity.
    - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [apply outside_all_unlistk; exact Hout | reflexivity].
    - intros Hsm. pose proof Hswf2 as W2. rewrite ET2 in W2. cbn [ax_S ax_setS] in W2. exact (smatch_unlistk_at rhoU (dropL (ax_S T1)) 1 ob1 5 _ Eob1 Hdob1 W2 Hsm). }

  assert (EsXU : eval rhoU sX = eval rho' sX) by (unfold rhoU; apply eval_absorb).
  assert (H5 : SPA segs (Kf k) T3 rhoU tp (tr, mkCfg ms md)).
  { rewrite ET3.
    apply (SPA_carve_listobj (Kf k) rhoU T2 tp (tr, mkCfg ms md) sX (SVar 17) (bv_unsigned (rw rho 17)) (DList 3) 3 (ss_next (ax_S T2)) H4 eq_refl).
    - pose proof Hswf3 as W3. rewrite ET3 in W3. exact W3.
    - apply Pos.le_refl.
    - unfold soff. cbn [eval]. unfold rhoU. cbn [rw rho_absorb]. rewrite E17. apply signed_small. lia.
    - lia.
    - lia.
    - rewrite EsXU. lia.
    - unfold rhoU. cbn [rl rho_absorb]. rewrite Hrl3. exact HA3.
    - rewrite EsXU. rewrite <- EsXU. apply objs_lowb_disjoint; [exact HLU | rewrite ET2 in Hlow2; rewrite ET2; exact Hlow2 | lia].
    - intros off Hoff _. rewrite EsXU. rewrite wview_high by (rewrite u64_of_sum by lia; lia).
      destruct (Z_lt_le_dec off n) as [Hlt|Hge].
      + rewrite (HREL off) by lia. discriminate.
      + rewrite HOUT by (rewrite u64_of_sum by lia; lia). rewrite (Hrm_in off) by lia. discriminate.
    - intros off Hoff. rewrite EsXU. rewrite rd_of_high by (rewrite u64_of_sum by lia; lia). unfold rhoU at 2. cbn [rl rho_absorb]. rewrite Hrl3.
      destruct (Z_lt_le_dec off n) as [Hlt|Hge].
      + apply HREL. lia.
      + rewrite HOUT by (rewrite u64_of_sum by lia; lia). apply Hrm_in. lia.
    - intros z Hz. rewrite EsXU in Hz.
      destruct (Z_lt_le_dec (z - bv_unsigned (eval rho' sX)) n) as [Hlt|Hge].
      + pose proof (HREL (z - bv_unsigned (eval rho' sX)) ltac:(lia)) as X. replace (bv_unsigned (eval rho' sX) + (z - bv_unsigned (eval rho' sX))) with z in X by lia. rewrite X. discriminate.
      + rewrite HOUT by (pose proof (urange (Z_to_bv 64 z)); rewrite lit_unsigned, Z.mod_small by lia; lia).
        pose proof (Hrm_in (z - bv_unsigned (eval rho' sX)) ltac:(lia)) as X. replace (bv_unsigned (eval rho' sX) + (z - bv_unsigned (eval rho' sX))) with z in X by lia. rewrite X. discriminate.
    - rewrite EsXU. apply (xr_lowb_clear rhoU T2); [exact HLU | rewrite ET2; cbn [ax_X ax_setS]; exact HxT1 | rewrite ET2; cbn [ax_base ax_setS]; exact HbT1 | lia]. }

  pose proof (SPA_axforms segs (Kf k) XM rhoU T3 M tp _ EM H5) as H6.

  set (lo := bv_unsigned (eval rho' sX)). set (hi := lo + bv_unsigned (rw rho 17)).
  assert (H7 : SPA segs (Kf k) M (set_rm rhoU (mrest rhoU lo hi)) tp (tr, mkCfg ms md)).
  { apply (SPA_rm_under (Kf k) M rhoU (mrest rhoU lo hi) tp _ lo hi H6).
    - exists O_strS. split; [exact (nth_error_In _ _ HstrM)|]. unfold obj_range, obj_lo_of, obj_hi_of, O_strS. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite EsXU. fold lo. rewrite soff_lit_small by lia. unfold soff. cbn [eval]. unfold rhoU. cbn [rw rho_absorb]. rewrite E17, signed_small by lia. unfold hi. lia.
    - intros z Hz. unfold mrest in Hz. destruct ((lo <=? bv_unsigned z) && (bv_unsigned z <? hi)) eqn:B; [|exfalso; exact (Hz eq_refl)].
      apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia.
    - intros x Hx. pose proof (xr_lowb_word rhoU M x HLU) as W.
      unfold x_ok in HxokM. apply andb_prop in HxokM as [HxM HbM]. apply andb_prop in HxM as [HnorlM HxbM]. apply sv_eqb_sound in HbM.
      assert (XM1 : forallb xr_lowb (ax_X M) = true).
      { destruct (apply_axforms_Xb _ _ _ EM) as [EX _]. rewrite EX, ET3, ET2. cbn [ax_X ax_setS]. exact HxT1. }
      specialize (W XM1 HbM Hx). unfold lo. rewrite <- EsXU. pose proof HLU as (_ & _ & U3 & _ & _ & U6). pose proof (urange (rw rhoU 20)). lia.
    - intros HK. exact HK. }

  set (rhoM := rho_set_rl (rho_set_rl (set_rm rhoU (mrest rhoU lo hi)) 5 (rl rho 5)) 6 (rl rho 6)).
  assert (ErM : rhoM_of rho' ms md = rhoM) by reflexivity.
  unfold x_ok in HxokM. apply andb_prop in HxokM as [HxM HbM]. apply andb_prop in HxM as [HnorlM HxbM]. apply sv_eqb_sound in HbM.
  assert (H8 : SPA segs (Kf k) M rhoM tp (tr, mkCfg ms md)).
  { rewrite <- (ax_setS_id M).
    eapply (SPA_morphX (Kf k) (Kf k) M (ax_S M) (set_rm rhoU (mrest rhoU lo hi)) rhoM tp _); [ | | | | | intros HK; exact HK | exact H7].
    - rewrite HxbM. destruct (proj1 H7) as (_ & _ & Hwf & _). unfold axwf in Hwf. apply andb_prop in Hwf as [_ Hb]. exact Hb.
    - rewrite HbM. reflexivity.
    - intros r Hr. pose proof (proj1 (forallb_forall _ _) HnorlM r Hr) as X0. unfold xr_norl in X0.
      apply Bool.negb_true_iff in X0. apply Bool.orb_false_iff in X0 as [X0 X4]. apply Bool.orb_false_iff in X0 as [X0 X3]. apply Bool.orb_false_iff in X0 as [X1 X2].
      unfold rhoM. split; rewrite !SymCall.eval_set_rl by assumption; reflexivity.
    - intros x Hout Hrm. split; [|reflexivity]. unfold rhoM. apply outside_all_set_rl_state; [exact Hrl6M|]. apply outside_all_set_rl_state; [exact Hrl5M | exact Hout].
    - intros Hsm. unfold rhoM. apply SymCall.smatch_set_rl; [exact Hrl6M|]. apply SymCall.smatch_set_rl; [exact Hrl5M | exact Hsm]. }
  rewrite ErM. split; [exact H8|]. split.
  - split; [|split].
    + intros i Hi. unfold rhoM. cbn [rw rho_set_rl set_rm]. unfold rhoU. cbn [rw rho_absorb]. symmetry. apply Hrw. exact Hi.
    + intros l. unfold rhoM. cbn [rl rho_set_rl set_rm].
      destruct (Pos.eqb_spec l 6) as [->|N6]; [reflexivity|]. destruct (Pos.eqb_spec l 5) as [->|N5]; [reflexivity|].
      unfold rhoU. cbn [rl rho_absorb]. symmetry. apply Hrl; assumption.
    + intros z. unfold rhoM. cbn [rm rho_set_rl set_rm]. unfold mrest.
      destruct ((lo <=? bv_unsigned z) && (bv_unsigned z <? hi)) eqn:B; [reflexivity|].
      assert (Hz : ~ (lo <= bv_unsigned z < hi)).
      { intros [Y1 Y2]. apply Bool.andb_false_iff in B as [B|B]; [apply Z.leb_gt in B | apply Z.ltb_ge in B]; lia. }
      unfold hi, lo in Hz. rewrite HOUT by (unfold n in *; lia). symmetry. apply Hrm_out. exact Hz.
  - unfold rhoM, FA. apply Forall_holds_set_rl56; [right; reflexivity | intros p Hp; exact Hp |].
    apply Forall_holds_set_rl56; [left; reflexivity | intros p Hp; exact Hp |]. apply Forall_holds_set_rm. exact HFU.
Qed.

Definition RC1 (rhoW rc : valuation) : Prop := ltac2:(tb__ "0|c|
S1S36S0S37Q40M0A1M1ScVrc;R1A2ScVrhoW;R1A2A3Fi;S1S0S46S37Q8M2A1M3A1M4S9Vrc;P5M5A2Vbs1;A3S1S0G4S9Vrc;P6M6A2Vstr;A3S1S36S2S0S36R1G5A3A1S2S0S36R2G6A3A1S0G4S9Vrc;R3A2S9VrhoW;R3A2A3F_;F_;Fl;S1S35S1S3aZ0M7R1A2S3cR1S38G0ScVrho;P11A2A2M8A2A2S0S47G3A1M9SbVrc;S39G0S3bS38G0SeVrhoW;S80A2A2MaR2A2A2A2S48G3S60G3S3dR2A1S9Vrho;P3A2S39G2G7A2A4A2A3F_;Foff;S1G1S2S1S3aGaS38G0R1A2MbA2S3cGbS3bGaG8A2A2A2A1S0G9SbVrc;R2A2SbVrhoW;R2A2A3F_;Fz;VFA;Vrc;A1A2A2A2A2A2A2").
Lemma RC1_intro : ltac2:(tb__ "0|9|
S7S8fS89VFA;R3A1S35S1S3aZ0M0R1A2S3cR1S38Q40M1ScVrho;P11A2A2M2A2A2S0S47S37Q8M3A1M4A1M5SbS9fR6R5R4A3M6S39G1S3bS38G1SeR6S80A2A2M7R2A2A2A2S48G4S60G4S3dR2A1S9Vrho;P3A2S39G3G0A2A4A2A3F_;Foff;S37G1A1S2S1S3aG7S38G1R1A2M8A2S3cG8S3bG7G2A2A2A2A1S0G5SbS9fR7R6R5A3R2A2SbR7R2A2A3F_;Fz;Sa7R6G6A2F_;F_;F_;Fmd;Fms;FrhoW;").
Proof.
  intros rhoW ms md HFA X2 X3. unfold RC1.
  split; [intros i; reflexivity|]. split; [unfold rhoC_of; cbn [rl rho_set_rl rho_absorb]; reflexivity|]. split; [reflexivity|].
  split; [intros l N5 N6; unfold rhoC_of; cbn [rl rho_set_rl rho_absorb]; destruct (Pos.eqb_spec l 6) as [->|]; [congruence|]; destruct (Pos.eqb_spec l 5) as [->|]; [congruence|]; reflexivity|].
  split; [exact X2|]. split; [exact X3|].
  unfold FA, rhoC_of. apply Forall_holds_set_rl56; [right; reflexivity | intros p Hp; exact Hp |]. apply Forall_holds_absorb.
  apply Forall_holds_set_rl56; [left; reflexivity | intros p Hp; exact Hp | exact HFA].
Qed.

Lemma FA_split : ltac2:(tb__ "0|1|
S7VFA;R1A1S1S5fS6SfR2A1M0S64Va;Vv;A2A3S1S5fS6G0S82A3S5fS6G0S63Vv;A1A3A2A2F_;Fr;").
Proof. intros r H. unfold FA in H. apply Forall_app in H as [H1 H]. apply Forall_app in H as [H2 H3]. repeat split; assumption. Qed.
Lemma FA_FSC : ltac2:(tb__ "0|0|
S7VFA;R1A1Sd0R2S66Va;Vv;A2A2F_;Fr;").
Proof. intros r H. destruct (FA_split r H) as (H1 & H2 & H3). unfold FsHold, FSC. constructor; [exact H1|]. constructor; [exact H2|]. constructor; [exact H2|]. constructor; [exact H1|]. constructor. Qed.
Lemma FA_agree : ltac2:(tb__ "0|1|
S36S7S7S99SaS5bVT8;A1A1R3A2S13R4R3R2A3VFA;R4A1M0G0F_;F_;F_;Fr';Fr;Fm;").
Proof.
  intros m r r' Hm Hag H. destruct certC as ((_ & _ & _ & _ & _ & HLok & _) & _).
  pose proof (fs_ok_below _ _ HLok) as Hb. unfold FsBelow in Hb. cbn [forallb] in Hb.
  apply andb_prop in Hb as [B1 Hb]. apply andb_prop in Hb as [B2 Hb]. apply andb_prop in Hb as [B3 _].
  destruct (FA_split r H) as (H1 & H2 & H3). unfold FA. rewrite !Forall_app.
  repeat split; (eapply Forall_holds_agree; [exact Hag | eapply forallb_below_mono; [exact Hm | eassumption] | assumption]).
Qed.
Lemma FSC_below : ltac2:(tb__ "0|0|
S36S99SaS5bVT8;A1A1R1A2S0S45ScfR2S66Va;Vv;A2A2S49A3F_;Fm;").
Proof.
  intros m Hm. destruct certC as ((_ & _ & _ & _ & _ & HLok & _) & _).
  pose proof (fs_ok_below _ _ HLok) as Hb. unfold FsBelow in Hb |- *. cbn [forallb] in Hb |- *. unfold FSC. cbn [forallb].
  apply andb_prop in Hb as [B1 Hb]. apply andb_prop in Hb as [B2 Hb]. apply andb_prop in Hb as [B3 _].
  rewrite !(forallb_below_mono _ _ _ Hm B1), !(forallb_below_mono _ _ _ Hm B2). reflexivity.
Qed.
Lemma FIN_below : ltac2:(tb__ "0|0|
S36S99SaS5bVT8;A1A1R1A2S0S45S7bS6S21R2A1S63Vv;A1A3S49A3F_;Fm;").
Proof.
  intros m Hm. destruct certC as ((_ & _ & _ & _ & _ & HLok & _) & _).
  pose proof (fs_ok_below _ _ HLok) as Hb. unfold FsBelow in Hb. cbn [forallb] in Hb.
  apply andb_prop in Hb as [B1 Hb]. apply andb_prop in Hb as [B2 Hb]. apply andb_prop in Hb as [B3 _]. exact (forallb_below_mono _ _ _ Hm B3).
Qed.
Lemma HM1 : ltac2:(tb__ "0|2|
S0S46S37Q8M0A1M1A1VMSGb;S4bG1S4bG1Vbs1;Vstr;A3S61S35G1S39G0A1Vsuf;A4A3A3"). Proof. unfold MSGb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.MSGb, bs1. rewrite <- app_assoc. reflexivity. Qed.
Lemma Hk1 : ltac2:(tb__ "0|1|
S0S4cVk1;S4aS37Q8A1M0S4bG0Vbs1;Vstr;A3A2A3"). Proof. unfold k1. rewrite length_app, bs1_len. reflexivity. Qed.
Lemma Hbl2 : ltac2:(tb__ "0|4|
S7S0S46S37Q8M0A1M1A1M2S9R1P3M3A2S9Vrho;G3A2A3S0G2S61Sc7G1Sc8R2A1Sc4S4dS35A1Z0Vsuf;A3A4S61S35G1S39G0A1Vsuf;A4A3F_;Fr;").
Proof. intros r _. unfold blA. cbn [map seq Z.to_nat app]. apply map_beval_lit. Qed.

Theorem tailC_sound : ltac2:(tb__ "0|0|
S7S13S8eVrho;R1A3Sb9S58Vok;S75S58VKf;U0A1VT8;R2Vtp;A5S76S58VKwr;S4aS37Q8A1VMSGb;A2A1S8eVrho;Vtp;Sc0A6A4F_;Frho7;").
Proof.
  intros rho7 Hag7.
  destruct certC as (G0 & G1 & _ & G3 & G4 & _ & G6).
  destruct G0 as (Ha & Ha1 & Hb1 & Ha80 & Hb80 & HLok & HstrS8).
  destruct G1 as (W1' & EW1' & HpcW1 & HnW1' & EW1 & HfinW1 & HnW1 & HxW1 & HbW1).
  destruct G3 as (_ & ECs & _ & _ & _ & _ & _ & _ & HnCs & _).
  destruct G4 as (Hefr & Hchk & S13 & S15 & ET & HlT & HnT).
  destruct G6 as (EM & HlM & HnM & _ & _ & _ & _ & EW0 & HoA).
  pose proof (urange (rw rho 16)) as R16.
  apply (triple_pre ok _ (FsHold rho7 [FC1 a v; BASEF; FIN v] /\ FsBelow (ss_next (ax_S T8)) [FC1 a v; BASEF; FIN v] = true));
    [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w HLok Hw) | intros [HF0 HLb]].
  assert (HFA7 : FA rho7).
  { unfold FA. unfold FsHold in HF0. rewrite !Forall_app. pose proof (Forall_inv HF0) as X1. pose proof (Forall_inv (Forall_inv_tail HF0)) as X2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF0))) as X3. repeat split; assumption. }
  eapply (runp_tr ok (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) (FSC a v) T8 W1' rho7 tp);
    [exact EW1' | exact HlT8 | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | exact (FA_FSC _ HFA7) | exact (FSC_below _ (Pos.le_refl _)) |].
  intros rhoW HagW.
  pose proof (FA_agree _ rho7 rhoW (Pos.le_refl _) HagW HFA7) as HFAW. pose proof (FA_FIN _ HFAW) as HFINW.
  assert (HagNW : agree_below NF rho rhoW) by (eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagW)]).
  eapply triple_conseq with (P := SPA segs (Kf 0) W1 rhoW tp);
    [intros w Hw; exact (SPA_axforms segs _ XWC rhoW _ W1 tp w EW1 (SPA_set_facts (Kf 0) W1' (FIN v) rhoW tp w HFINW (FIN_below _ HnW1') Hw)) | intros w Hw; exact Hw |].
  eapply triple_conseq with (P := fun w => exists rc, RC1 rhoW rc /\ SPA segs (Kf 0) C rc tp w);
    [intros [tr [ms md]] Hw; destruct (reshape1 rhoW tr ms md HagNW HFINW Hw) as (X1 & X2 & X3); exists (rhoC_of rhoW ms md); split; [exact (RC1_intro rhoW ms md HFAW X2 X3) | exact X1]
    | intros w Hw; exact Hw |].
  apply triple_ex. intros rc. apply triple_pure. intros (HRw & HR5 & HR6 & HRl & HRin & HRout & HFrc).
  pose proof (FIN_v rc (FA_FIN rc HFrc)) as Evc.
  apply (call_soundA segs ok (Kf 0) Jp1 (WLerr.Kw Jp1 bs1 str (length (WLerr.MSG bs1 str))) (Kf k1) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ rc tp Hefr Hchk).
  - intros rho2 tp2. apply wl_call1.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF1. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15, !eval_absorb. cbn [eval]. rewrite HR5, HR6, Evc, HRw, lit_unsigned, Z.mod_small by lia.
    destruct HagNW as (AW & _ & _). rewrite <- (AW 16%positive) by reflexivity. repeat split; try reflexivity. exact Hn16.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp1_Kf in HK'. rewrite wl1_MSG_len, Nat.min_id in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite <- ET.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf k1)); [intros t md0 (HJ & _ & _); exact HJ|].
    assert (HnC : ss_next (ax_S C) = ss_next (ax_S W1)) by (unfold C; cbn [ax_S ax_setS]; exact HnCs).
    assert (HFA' : FA rho') by (apply (FA_agree (ss_next (ax_S C)) rc rho'); [rewrite HnC, HnW1; exact HnW1' | exact Hag' | exact HFrc]).
    destruct Hag' as (A' & L' & M'). rewrite HnC in A'. destruct HagNW as (AW & LW & MW).
    assert (EsX' : eval rho' sX = eval rhoW sX).
    { cbn [eval sX vXB vXO]. rewrite <- (A' 18%positive), <- (A' 20%positive) by (rewrite HnW1; unfold NF in *; lia). rewrite !HRw. reflexivity. }
    eapply triple_conseq with (P := fun w => exists rM, (agree_below NF rho rM /\ FA rM) /\ SPA segs (Kf k1) M rM tp w); [ | intros w Hw; exact Hw |].
    { intros [tr2 [ms2 md2]] Hw. exists (rhoM_of rho' ms2 md2).
      destruct (reshape2 k1 rho' tr2 ms2 md2 HFA' (FIN_below _ ltac:(eapply Pos.le_trans; [exact HnW1' | rewrite <- HnW1, <- HnCs; exact HnT]))
                  ltac:(intros i Hi; rewrite <- (A' i) by (rewrite HnW1; unfold NF in *; lia); rewrite HRw; symmetry; apply AW; exact Hi)
                  ltac:(intros l N5 N6; rewrite <- (L' l), (HRl l N5 N6); symmetry; apply LW)
                  ltac:(rewrite <- (L' 6%positive); exact HR6)
                  ltac:(intros off Hoff; rewrite <- (M' _), EsX'; exact (HRin off Hoff))
                  ltac:(intros z Hz; rewrite <- (M' z), EsX' in *; rewrite (HRout z Hz); symmetry; apply MW) Hw) as (X1 & X2 & X3).
      split; [split; [exact X2 | exact X3] | exact X1]. }
    apply triple_ex. intros rM. apply triple_pure. intros [HagM HFAM].
    assert (HnTM : (ss_next (ax_S T8) <= ss_next (ax_S M))%positive) by (rewrite HnM; eapply Pos.le_trans; [exact HnW1' | rewrite <- HnW1, <- HnCs; exact HnT]).
    eapply (runp_tr ok (Kf k1) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp k1) (FSC a v) M W0 rM tp);
      [exact EW0 | exact HlM | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | exact (FA_FSC _ HFAM) | exact (FSC_below _ HnTM) |].
    intros rhoV HagV.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.post_sound ok J0 pre suf str Hst0 Hfd2 HokK HokP rho tp k1 (bs1 ++ str) (map (Z_to_bv 8) suf) b [] suf 0
             HM1 Hk1 ltac:(unfold b; rewrite length_map; reflexivity) (conj Hb1 Hb80) Hbl2 T8 W0 oA HoA HnT8 rhoV).
    + eapply agree_below_trans; [exact HagM | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnT8 HnTM) HagV)].
    + exact (FIN_fps rhoV (FA_FIN rhoV (FA_agree _ rM rhoV (Pos.le_refl _) ltac:(exact (agree_below_le _ _ _ _ HnTM HagV)) HFAM))).
Qed.
Theorem tailC_sound_ex : ltac2:(tb__ "0|0|
S7S13S8eVrho;R1A3Sb8S58S75S58VKf;U0A1VT8;R2Vtp;A5S76S58VKwr;S4aS37Q8A1VMSGb;A2A1S8eVrho;Vtp;Sc0A6A3F_;Frho7;").
Proof.
  intros rho7 Hag7.
  destruct certC as (G0 & G1 & _ & G3 & G4 & _ & G6).
  destruct G0 as (Ha & Ha1 & Hb1 & Ha80 & Hb80 & HLok & HstrS8).
  destruct G1 as (W1' & EW1' & HpcW1 & HnW1' & EW1 & HfinW1 & HnW1 & HxW1 & HbW1).
  destruct G3 as (_ & ECs & _ & _ & _ & _ & _ & _ & HnCs & _).
  destruct G4 as (Hefr & Hchk & S13 & S15 & ET & HlT & HnT).
  destruct G6 as (EM & HlM & HnM & _ & _ & _ & _ & EW0 & HoA).
  pose proof (urange (rw rho 16)) as R16.
  apply (etriple_pre _ (FsHold rho7 [FC1 a v; BASEF; FIN v] /\ FsBelow (ss_next (ax_S T8)) [FC1 a v; BASEF; FIN v] = true));
    [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w HLok Hw) | intros [HF0 HLb]].
  assert (HFA7 : FA rho7).
  { unfold FA. unfold FsHold in HF0. rewrite !Forall_app. pose proof (Forall_inv HF0) as X1. pose proof (Forall_inv (Forall_inv_tail HF0)) as X2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF0))) as X3. repeat split; assumption. }
  eapply (runp_etr (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) (FSC a v) T8 W1' rho7 tp);
    [exact EW1' | exact HlT8 | exact (FA_FSC _ HFA7) | exact (FSC_below _ (Pos.le_refl _)) |].
  intros rhoW HagW.
  pose proof (FA_agree _ rho7 rhoW (Pos.le_refl _) HagW HFA7) as HFAW. pose proof (FA_FIN _ HFAW) as HFINW.
  assert (HagNW : agree_below NF rho rhoW) by (eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagW)]).
  eapply etriple_conseq with (P := SPA segs (Kf 0) W1 rhoW tp);
    [intros w Hw; exact (SPA_axforms segs _ XWC rhoW _ W1 tp w EW1 (SPA_set_facts (Kf 0) W1' (FIN v) rhoW tp w HFINW (FIN_below _ HnW1') Hw)) | intros w Hw; exact Hw |].
  eapply etriple_conseq with (P := fun w => exists rc, RC1 rhoW rc /\ SPA segs (Kf 0) C rc tp w);
    [intros [tr [ms md]] Hw; destruct (reshape1 rhoW tr ms md HagNW HFINW Hw) as (X1 & X2 & X3); exists (rhoC_of rhoW ms md); split; [exact (RC1_intro rhoW ms md HFAW X2 X3) | exact X1]
    | intros w Hw; exact Hw |].
  apply etriple_ex. intros rc. apply etriple_pure. intros (HRw & HR5 & HR6 & HRl & HRin & HRout & HFrc).
  pose proof (FIN_v rc (FA_FIN rc HFrc)) as Evc.
  apply (call_completeA segs (Kf 0) Jp1 (WLerr.Kw Jp1 bs1 str (length (WLerr.MSG bs1 str))) (Kf k1) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ rc tp Hefr Hchk).
  - intros rho2 tp2. apply wl_call1_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF1. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15, !eval_absorb. cbn [eval]. rewrite HR5, HR6, Evc, HRw, lit_unsigned, Z.mod_small by lia.
    destruct HagNW as (AW & _ & _). rewrite <- (AW 16%positive) by reflexivity. repeat split; try reflexivity. exact Hn16.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp1_Kf in HK'. rewrite wl1_MSG_len, Nat.min_id in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite <- ET.
    enough (HE : forall tr md, tpL = tp -> etriple segs (SPA segs (Kf k1) T rho' tpL) (LQA segs (Kwr (length MSGb)) NF rho tp Posts_fps))
      by (intros w0 [Hsm0 [Et HK0]]; exact (HE (w_tr w0) (cfg_model (w_cfg w0)) Et w0 (conj Hsm0 (conj Et HK0)))).
    intros tr md Et. subst tpL.
    assert (HnC : ss_next (ax_S C) = ss_next (ax_S W1)) by (unfold C; cbn [ax_S ax_setS]; exact HnCs).
    assert (HFA' : FA rho') by (apply (FA_agree (ss_next (ax_S C)) rc rho'); [rewrite HnC, HnW1; exact HnW1' | exact Hag' | exact HFrc]).
    destruct Hag' as (A' & L' & M'). rewrite HnC in A'. destruct HagNW as (AW & LW & MW).
    assert (EsX' : eval rho' sX = eval rhoW sX).
    { cbn [eval sX vXB vXO]. rewrite <- (A' 18%positive), <- (A' 20%positive) by (rewrite HnW1; unfold NF in *; lia). rewrite !HRw. reflexivity. }
    eapply etriple_conseq with (P := fun w => exists rM, (agree_below NF rho rM /\ FA rM) /\ SPA segs (Kf k1) M rM tp w); [ | intros w Hw; exact Hw |].
    { intros [tr2 [ms2 md2]] Hw. exists (rhoM_of rho' ms2 md2).
      destruct (reshape2 k1 rho' tr2 ms2 md2 HFA' (FIN_below _ ltac:(eapply Pos.le_trans; [exact HnW1' | rewrite <- HnW1, <- HnCs; exact HnT]))
                  ltac:(intros i Hi; rewrite <- (A' i) by (rewrite HnW1; unfold NF in *; lia); rewrite HRw; symmetry; apply AW; exact Hi)
                  ltac:(intros l N5 N6; rewrite <- (L' l), (HRl l N5 N6); symmetry; apply LW)
                  ltac:(rewrite <- (L' 6%positive); exact HR6)
                  ltac:(intros off Hoff; rewrite <- (M' _), EsX'; exact (HRin off Hoff))
                  ltac:(intros z Hz; rewrite <- (M' z), EsX' in *; rewrite (HRout z Hz); symmetry; apply MW) Hw) as (X1 & X2 & X3).
      split; [split; [exact X2 | exact X3] | exact X1]. }
    apply etriple_ex. intros rM. apply etriple_pure. intros [HagM HFAM].
    assert (HnTM : (ss_next (ax_S T8) <= ss_next (ax_S M))%positive) by (rewrite HnM; eapply Pos.le_trans; [exact HnW1' | rewrite <- HnW1, <- HnCs; exact HnT]).
    eapply (runp_etr (Kf k1) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp k1) (FSC a v) M W0 rM tp);
      [exact EW0 | exact HlM | exact (FA_FSC _ HFAM) | exact (FSC_below _ HnTM) |].
    intros rhoV HagV.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.post_sound_ex J0 pre suf str Hst0 Hfd2 rho tp k1 (bs1 ++ str) (map (Z_to_bv 8) suf) b [] suf 0
             HM1 Hk1 ltac:(unfold b; rewrite length_map; reflexivity) (conj Hb1 Hb80) Hbl2 T8 W0 oA HoA HnT8 rhoV).
    + eapply agree_below_trans; [exact HagM | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnT8 HnTM) HagV)].
    + exact (FIN_fps rhoV (FA_FIN rhoV (FA_agree _ rM rhoV (Pos.le_refl _) ltac:(exact (agree_below_le _ _ _ _ HnTM HagV)) HFAM))).
Qed.
End TailC.
End Fps_tailC.

(* [comment removed for export] *)
Module Start8RegGlob.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sobj"; "sv"; "mkObj"; "DImage"; "SAlu"; "SVar"; "ss_regs"; "FcsrFrm0"; "mkSS"; "ss_next"; "swf"; "valuation"; "DUnknown"; "sprop"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "true"; "bool"; "list"; "option"; "None"; "false"; "Some"; "pair"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "axwf"; "mkLeafA"; "ax_setS"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Start8RegGlob"; "E_G2"; "Pre_G2"; "P_G2"; "CUTS_G2"; "FUEL_G2"; "NPG2"; "NPOST_G2"; "Posts_G2"; "junk_regs2"; "sub_G2"; "O_afl1_2"; "O_afl2_2"; "O_gl2"; "O_gstk2'"; "O_lla2"; "O_llmin2"; "O_ph2"; "Pre_G2_S"; "leaf1G2"; "objs_G2"; "post_regs_G2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface"; "facts_G"; "fregs_G"; "regglob_ret"; "vS0"; "D_G"; "O_aglob"; "O_b1"; "O_gstk"; "O_pgA"; "O_pgB"; "regglob_entry"; "regs_G"; "vRA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "O_got"; "O_rtc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "O_flg"; "O_real"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.RegGlob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition O_lla2 : sobj := ltac2:(tb__ "0|3|
S5S0Z0A1S0Z173648A1M0S0Z173658A1S14S1S2S0Z173650A1Z8M1S7S46S8P1A1M2S0Z4dc0A1A3A3S14S1S2G0G1S7S46G2S0Z10000A1A3A3S16S1A1A3A3S6A5").
Definition O_gl2 : sobj := ltac2:(tb__ "0|1|
S5S0Z0A1S0Zeec70A1S0Zeecc0A1S14S1S2S0Zeec90A1Z8M0S7S46S8P1A1S0Z4da8A1A3A3S14S1S2S0Zeecb0A1G0S0Z1000000000000000A1A3S16S1A1A3A3S6A5").
Definition O_afl1_2 : sobj := ltac2:(tb__ "0|5|
S5S0Z0A1M0S0Zeebf8A1M1S0Zeec24A1S14S1S2S0Zeec00A1Z4M2S0Z400A1A3S14S1S2S0ZeebfcA1G2S0Z100A1A3S14S1S2S0Zeec0cA1Z1M3G0A3S14S1S2S0Zeec20A1G3G0A3S14S1S2S0Zeec18A1Z8M4S0Z1400000010A1A3S14S1S2S0Zeec10A1G4S0Z101010000000001A1A3S14S1S2S0Zeec08A1G2S0Z800A1A3S14S1S2S0Zeec04A1G2S0Z10A1A3S14S1S2G1G2S0ZffffffffffffffffA1A3S16S1A1A3A3A3A3A3A3A3A3A3S6A5").
Definition O_afl2_2 : sobj := ltac2:(tb__ "0|7|
S5S0Z0A1M0S0Zeec30A1M1S0Zeec70A1S14S1S2S0Zeec46A1Z1M2S0G2A1M3A3S14S1S2S0Zeec52A1G2G0A3S14S1S2S0Zeec60A1Z8M4S0Z14487A1A3S14S1S2S0Zeec5cA1Z4M5S0Z2M6A1A3S14S1S2S0Zeec58A1G2G3A3S14S1S2S0Zeec54A1G5G0A3S14S1S2S0Zeec50A1G6G3A3S14S1S2S0Zeec48A1G4S0Z101010101000001A1A3S14S1S2S0Zeec40A1Z6S0Z1000100000000A1A3S14S1S2S0Zeec47A1G2G0A3S14S1S2S0Zeec38A1G4G0A3S14S1S2S0Zeec34A1G2G3A3S14S1S2G1G5S0Z55A1A3S14S1S2S0Zeec68A1G5S0Z10101A1A3S16S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3S6A5").
Definition O_llmin2 : sobj := ltac2:(tb__ "0|2|
S5S0Z0A1S0Ze9b30A1M0S0Ze9b38A1S14S1S2G0Z8M1S0G1A1A3S16S1A1A3S6A5").
Definition O_ph2 : sobj := ltac2:(tb__ "0|2|
S5S0Z0A1S0Zf0c5cA1M0S0Zf0c5dA1S14S1S2G0Z1M1S0G1A1A3S16S1A1A3S6A5").
Definition objs_G2 : list sobj := ltac2:(tb__ "0|0|
S14S3S4eS14S3S4fS14S3S50S14S3S4dS14S3S3aS14S3S38S14S3S36S14S3S37S14S3S4cS14S3S3bS14S3S3cS14S3S60S14S3S61S14S3S5eS14S3S5fS16S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition Pre_G2_S : sstate := ltac2:(tb__ "0|0|
SbS51S52S48SaS1bS4A1S3fS47S41S1cA9").
Definition Pre_G2 : axst := axG Pre_G2_S.
Lemma Pre_G2_wf : ltac2:(tb__ "0|0|
S21S20S18SdS3dA1S17A3S20S18S27S2dA1S17A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition leaf1G2 (A : axst) (o : option (list leafA)) : axst := ltac2:(tb__ "0|1|
S1aS19S23A1M0A1S25Lo;Vo;G0G0S25Ll0;R1VA;S23G0G0S25Ll1;R1S2bR2A1S23G0VA;Ll3;Ll2;X19x2Ll1;Ll;X19x2Ll0;VA;X1ax2").
Definition run_toG2 (fuel : nat) (cuts : list Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S3eVA;S26S22Vfuel;Vcuts;VA;S17A5A2").

Definition CUTS_G2 : list Z := [regglob_ret].
Definition FUEL_G2 : nat := 13500%nat.

Definition run_G2__R : option (list leafA) := ltac2:(tb__ "0|0|
S26S22S30S2fS2dS17A5").
Local Strategy expand [run_G2__R].
Definition E_G2 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1G2 Pre_G2 (ro1__)))) run_G2__R).
Lemma run_G2 : ltac2:(tb__ "0|1|
S20S1aS19S23A1M0A1S26S22S30S2fS2dS17A5S1dG0S14S23S28S2cS54A2S16S23A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_G2__R <: run_G2__R = Some [mkLeafA E_G2 RsCut]). Qed.

Lemma E_G2_at : ltac2:(tb__ "0|3|
S21S20S45S13S24S2cA1M0A1S49A3S21S20S44ScG0A1S41A3S21S20S19S10A1S11G0A1S47A3S21S20S4S42S4U1S9G0A1M1S0Z0A1M2A4S53A3S20S4S42S4U2G1G2A4S4aA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition junk_regs2 : list nat := ltac2:(tb__ "0|0|
S14S15U5S14S15U6S14S15U7S14S15UaS14S15UbS14S15UcS14S15UdS14S15UeS14S15UfS14S15U10S14S15U11S16S15A1A3A3A3A3A3A3A3A3A3A3A3").
Definition NPG2 : positive := 100.
Definition NPOST_G2 : positive := 132.
Definition post_reg_G2 (r : nat) : sv := ltac2:(tb__ "0|0|
S18S4L_;S67S15S66Vr;A1S34A3S8S5bS31S5cVr;A1A2A1S42S4Vr;S9S24S2cA1A1S0Z0A1A4X18x2").
Definition post_regs_G2 : list sv := map post_reg_G2 (seq 0 32).
Definition O_gstk2' : sobj := ltac2:(tb__ "0|0|
S5S4aS0S68S4bA1A1S0Z0A1S16S1A1SfA5").
Definition P_G20 : axst := ltac2:(tb__ "0|0|
S29S2cSbS49S40S48SaS1bS4A1S55S3S12S24S2cA1A1U0S39A4S47S32S1cA9A2").
Definition P_G2 : axst := Eval vm_compute in P_G20.
Definition Posts_G2 : list leafA := ltac2:(tb__ "0|0|
S14S23S28S2eS54A2S16S23A1A3").

Definition sub_G2 : wsub := ltac2:(tb__ "0|0|
S43S15S1fS44S4A2S15S1eS44S4S5bS31S5cR1A1A2S42S4R1S9S24S2cA1A1S0Z0A1A4A4Lr;S34A4").
Lemma ent_G2 : ltac2:(tb__ "0|0|
S20S18S2aS2cS2eS35A3S17A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_G2 : ltac2:(tb__ "0|0|
S20S18S65S35S41A2S17A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma P_G2_wf : ltac2:(tb__ "0|1|
S21S20S18S27S2eA1S17A3S21S20S18SdS24S2eA1M0A1S17A3S20S44ScG0A1S32A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Theorem regglob2_sum : ltac2:(tb__ "0|0|
S64OF_;S58SeS19S5dQ40A1A1S5aS22R4R3A3S59S22S41R4A3S63S22R6S57S22R5S2dR4R3A5S56S22R5S41R4R3S33A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_soundA; [exact run_G2 | exact Hok | reflexivity | exact Hst]. }
  apply triple_LQA_of_leaves. intros L rho1 [<-|[]] Hag. cbn [la_state].
  eapply (triple_entailsA segsA ok J NF E_G2 P_G2 sub_G2 rho1 tp); [exact ent_G2 | exact wid_G2 | exact Hst |].
  eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl ].
  intros w Hw. eapply (LQA_intro segsA J NF rho tp (mkLeafA P_G2 RsCut)); [left; reflexivity | | exact Hw].
  eapply agree_below_trans; [exact Hag | apply rho_sub_agree; exact wid_G2].
Qed.

Theorem regglob2_sum_ex : ltac2:(tb__ "0|0|
S58SeS19S5dQ40A1A1S59S22S41R3A3S62S22S57S22R4S2dR3R2A5S56S22R4S41R3R2S33A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_seq.
  { eapply sym_run_etripleA; [reflexivity | exact Hst | exact run_G2]. }
  apply etriple_LQA_of_leaves. intros L rho1 [<-|[]] Hag. cbn [la_state].
  eapply (etriple_entailsA segsA J NF E_G2 P_G2 sub_G2 rho1 tp); [exact ent_G2 | exact wid_G2 | exact Hst |].
  eapply etriple_conseq; [ | intros w Hw; exact Hw | apply etriple_refl ].
  intros w Hw. eapply (LQA_intro segsA J NF rho tp (mkLeafA P_G2 RsCut)); [left; reflexivity | | exact Hw].
  eapply agree_below_trans; [exact Hag | apply rho_sub_agree; exact wid_G2].
Qed.
End Start8RegGlob.

