(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nq.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr o5.

(* [comment removed for export] *)
Module FpsU_b0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsU_st"; "T7b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "PRE_U"; "SUF_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs"; "T8C"; "tailC_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsU_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs.
Import ListNotations.
Open Scope Z_scope.

Lemma okC : ltac2:(tb__ "0|1|
S3S1S8S5S6Z7M0S4S0A1S7G0S0A2A5S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsU_b0.

(* [comment removed for export] *)
Module FpsC_b0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7b"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "PRE_C"; "SUF_NL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs"; "T8C"; "tailC_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs.
Import ListNotations.
Open Scope Z_scope.

Lemma okC : ltac2:(tb__ "0|1|
S3S1S8S5S6Z11M0S4S0A1S7G0S0A2A5S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_b0.

(* [comment removed for export] *)
Module Fps_tailC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "valuation"; "sv"; "rl"; "ss_next"; "rm"; "rw"; "ss_objs"; "eval"; "holds"; "sstate"; "SLit"; "obj_range"; "agree_below"; "ob_dflt"; "outside_all"; "swf"; "odefault"; "smatch"; "ss_lenient"; "DList"; "cell"; "ranges_disjoint"; "dflt_writable"; "ob_cells"; "obj_holds"; "obj_lo_of"; "sprop_below"; "ss_facts"; "ss_pc"; "SVar"; "image_byte"; "is_arr"; "mkObj"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "obj_hi_of"; "rd"; "rom_ok"; "soff"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "to_nat"; "pow"; "of_nat"; "div"; "leb"; "ltb"; "mul"; "sub"; "@Corelib.Init.Datatypes"; "bool"; "list"; "option"; "Some"; "true"; "length"; "app"; "nat"; "nil"; "cons"; "false"; "pair"; "prod"; "snd"; "fst"; "None"; "andb"; "negb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs"; "FIN"; "FC1"; "obj_lowb"; "FSC"; "lastobj"; "unlistk_at"; "xr_lowb"; "O_strR"; "splitsC"; "tailC_out"; "XM"; "XWC"; "blC"; "osome_eqb"; "selR"; "subC1"; "tailC"; "unk_keep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "xword"; "ok_frameA"; "smatchA"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "sX"; "O_strS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "BASEF"; "facts_fps"; "runp"; "set_facts"; "fs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "HSE"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "FdChannel"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "wview"; "find_segment"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Fps_tailC"; "LOWV"; "lastobj_of"; "xwords_clear'"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "sprop_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Fps_tailC.TailC"; "Jp1"; "rhoC_of"; "PG0"; "PG1"; "PG2"; "PG3"; "PG4"; "PG5"; "PG6"; "RC1"; "WLF1"; "mrest"; "rhoM_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "w_cfg"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "app_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "Posts_fps"; "tailA_out"; "x_ok"; "bexps_eqb"; "blA"; "dropL"; "tailA_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL"; "dlist_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA"; "exts_rl_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_run"; "FsBelow"; "FsHold"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA"; "Kf"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@Stdlib.Arith.PeanoNat.Nat"; "min"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.DrvFp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_run OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs.
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
Lemma segs_top_val : InitState.segs_top segs = 0x643000.
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
Let MSGb : list byte := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.MSGb pre suf str.
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
S3S5aS5aS1S0S47S5aA1M0S84S66Va;Vv;A2VT8;A2S48S5aR1A2A3S1S0S35S23S5bR1A1M1A1Zd6760A3S1S99SaS5bVT8;A1A1SaG1A1M2A2S1S0G0Sb1S85R1S63Vv;A1M3A2S6eA2S48S5aVW1;A2A3S1S0S45S7bS6S6S7fS6S30R1A1S22S5bVW1;A1M4A1A3Lf;G3A3S49A3S1S0S36SaG4A1G2A3S1S0S45S7bS51S8S8A2S69S5cVW1;A1A3S49A3S0S8S5dVW1;A1S11S59A1A3A2A2A2A2A2A2A2LW1';A2").
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
  destruct ((ss_pc (ax_S W1') =? 0xd6760) && (ss_next (ax_S T8) <=? ss_next (ax_S W1'))%positive) eqn:B1; [|discriminate]. cbn [negb] in H.
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
                (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_inv J0 pre suf str rho tp 0 _ _ _ _ _)) as H8.
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
  split; [| eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0%nat 92%positive); [exact Hag | exact Hme | exact HK]].
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
  exists tr00. split; [exact HJ|]. unfold WLerr.TRk, WLerr.MSG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.EVS, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.MSGb. cbn [firstn map]. rewrite <- app_assoc. f_equal. f_equal. fold bs1.
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
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_okK ok J0 pre suf str HokK rho tp _ r t tr0 ms md0 msv' (Kw_Jp1_Kf k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_okP ok J0 pre suf str HokP rho tp _ r t tr0 ms md0 x8 (Kw_Jp1_Kf k r t tr0 md0 HK) Hp Ho).
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
                (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_inv J0 pre suf str rho tp k _ _ _ _ _)) as H3.
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
S0S46S37Q8M0A1M1A1VMSGb;S4bG1S4bG1Vbs1;Vstr;A3S61S35G1S39G0A1Vsuf;A4A3A3"). Proof. unfold MSGb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.MSGb, bs1. rewrite <- app_assoc. reflexivity. Qed.
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
  eapply (runp_tr ok (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) (FSC a v) T8 W1' rho7 tp);
    [exact EW1' | exact HlT8 | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | exact (FA_FSC _ HFA7) | exact (FSC_below _ (Pos.le_refl _)) |].
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
    eapply (runp_tr ok (Kf k1) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp k1) (FSC a v) M W0 rM tp);
      [exact EW0 | exact HlM | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | exact (FA_FSC _ HFAM) | exact (FSC_below _ HnTM) |].
    intros rhoV HagV.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.post_sound ok J0 pre suf str Hst0 Hfd2 HokK HokP rho tp k1 (bs1 ++ str) (map (Z_to_bv 8) suf) b [] suf 0
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
  eapply (runp_etr (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) (FSC a v) T8 W1' rho7 tp);
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
    eapply (runp_etr (Kf k1) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp k1) (FSC a v) M W0 rM tp);
      [exact EW0 | exact HlM | exact (FA_FSC _ HFAM) | exact (FSC_below _ HnTM) |].
    intros rhoV HagV.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.post_sound_ex J0 pre suf str Hst0 Hfd2 rho tp k1 (bs1 ++ str) (map (Z_to_bv 8) suf) b [] suf 0
             HM1 Hk1 ltac:(unfold b; rewrite length_map; reflexivity) (conj Hb1 Hb80) Hbl2 T8 W0 oA HoA HnT8 rhoV).
    + eapply agree_below_trans; [exact HagM | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnT8 HnTM) HagV)].
    + exact (FIN_fps rhoV (FA_FIN rhoV (FA_agree _ rM rhoV (Pos.le_refl _) ltac:(exact (agree_below_le _ _ _ _ HnTM HagV)) HFAM))).
Qed.
End TailC.
End Fps_tailC.

(* [comment removed for export] *)
Module Start8RegGlob.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sobj"; "sv"; "mkObj"; "DImage"; "SAlu"; "SVar"; "ss_regs"; "FcsrFrm0"; "mkSS"; "ss_next"; "swf"; "valuation"; "DUnknown"; "sprop"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "true"; "bool"; "list"; "option"; "None"; "false"; "Some"; "pair"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "axwf"; "mkLeafA"; "ax_setS"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Start8RegGlob"; "E_G2"; "Pre_G2"; "P_G2"; "CUTS_G2"; "FUEL_G2"; "NPG2"; "NPOST_G2"; "Posts_G2"; "junk_regs2"; "sub_G2"; "O_afl1_2"; "O_afl2_2"; "O_gl2"; "O_gstk2'"; "O_lla2"; "O_llmin2"; "O_ph2"; "Pre_G2_S"; "leaf1G2"; "objs_G2"; "post_regs_G2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface"; "facts_G"; "fregs_G"; "regglob_ret"; "vS0"; "D_G"; "O_aglob"; "O_b1"; "O_gstk"; "O_pgA"; "O_pgB"; "regglob_entry"; "regs_G"; "vRA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "O_got"; "O_rtc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface"; "O_flg"; "O_real"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.RegGlob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition O_lla2 : sobj := ltac2:(tb__ "0|3|
S5S0Z0A1S0Z170308A1M0S0Z170318A1S14S1S2S0Z170310A1Z8M1S7S46S8P1A1M2S0Z4dc0A1A3A3S14S1S2G0G1S7S46G2S0Z10000A1A3A3S16S1A1A3A3S6A5").
Definition O_gl2 : sobj := ltac2:(tb__ "0|1|
S5S0Z0A1S0Zeb930A1S0Zeb980A1S14S1S2S0Zeb950A1Z8M0S7S46S8P1A1S0Z4da8A1A3A3S14S1S2S0Zeb970A1G0S0Z1000000000000000A1A3S16S1A1A3A3S6A5").
Definition O_afl1_2 : sobj := ltac2:(tb__ "0|5|
S5S0Z0A1M0S0Zeb8b8A1M1S0Zeb8e4A1S14S1S2S0Zeb8c0A1Z4M2S0Z400A1A3S14S1S2S0Zeb8bcA1G2S0Z100A1A3S14S1S2S0Zeb8ccA1Z1M3G0A3S14S1S2S0Zeb8e0A1G3G0A3S14S1S2S0Zeb8d8A1Z8M4S0Z1400000010A1A3S14S1S2S0Zeb8d0A1G4S0Z101010000000001A1A3S14S1S2S0Zeb8c8A1G2S0Z800A1A3S14S1S2S0Zeb8c4A1G2S0Z10A1A3S14S1S2G1G2S0ZffffffffffffffffA1A3S16S1A1A3A3A3A3A3A3A3A3A3S6A5").
Definition O_afl2_2 : sobj := ltac2:(tb__ "0|7|
S5S0Z0A1M0S0Zeb8f0A1M1S0Zeb930A1S14S1S2S0Zeb906A1Z1M2S0G2A1M3A3S14S1S2S0Zeb912A1G2G0A3S14S1S2S0Zeb920A1Z8M4S0Z144adA1A3S14S1S2S0Zeb91cA1Z4M5S0Z2M6A1A3S14S1S2S0Zeb918A1G2G3A3S14S1S2S0Zeb914A1G5G0A3S14S1S2S0Zeb910A1G6G3A3S14S1S2S0Zeb908A1G4S0Z101010101000001A1A3S14S1S2S0Zeb900A1Z6S0Z1000100000000A1A3S14S1S2S0Zeb907A1G2G0A3S14S1S2S0Zeb8f8A1G4G0A3S14S1S2S0Zeb8f4A1G2G3A3S14S1S2G1G5S0Z55A1A3S14S1S2S0Zeb928A1G5S0Z10101A1A3S16S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3S6A5").
Definition O_llmin2 : sobj := ltac2:(tb__ "0|2|
S5S0Z0A1S0Ze67c0A1M0S0Ze67c8A1S14S1S2G0Z8M1S0G1A1A3S16S1A1A3S6A5").
Definition O_ph2 : sobj := ltac2:(tb__ "0|2|
S5S0Z0A1S0Zed91cA1M0S0Zed91dA1S14S1S2G0Z1M1S0G1A1A3S16S1A1A3S6A5").
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

(* [comment removed for export] *)
Module Lib_vec_reserve_rom_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "Some"; "app"; "option"; "list"; "pair"; "bool"; "cons"; "fst"; "nat"; "nil"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "sobj"; "SVar"; "SLit"; "ss_objs"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom"; "E_c8'"; "E_r15f"; "E_rW1f"; "Xk_r"; "s_r"; "xf_rback"; "E_r15x"; "E_rW1x"; "T_c8ok0"; "T_c8okZ"; "inj"; "kn15"; "vW"; "Pre_c"; "R_c8"; "R_r15"; "R_rW1"; "T_c8n00"; "T_c8ok00"; "T_r15f0"; "T_r15ok0"; "T_r15okB"; "T_rW1f0"; "T_rW1ok0"; "T_rW1okB"; "X15"; "X8"; "XW1"; "injR"; "kbytes"; "s_c"; "tvf0"; "xf_rcall"; "E_c8"; "E_r15"; "E_rW1"; "FUEL_vr"; "N15"; "N8"; "NW1"; "PhisV"; "T_c8n0"; "T_c8ok"; "T_r15f"; "T_r15ok"; "T_rW1f"; "T_rW1ok"; "cutpcs_vr"; "cutsE"; "exitsE"; "injZ"; "xf_cbackN"; "xf_cbackZ"; "xf_ccall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.RR"; "Pre_rr"; "P_fail"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "ejcertAF"; "efnode"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLeOrPc"; "Wcan"; "L_calloc_null"; "L_calloc_ok"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Lib_vec_reserve_rom_eqs"; "o_blk8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "drop_lastA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr.

Goal True. idtac "checking ejcertAF (vm_compute)". Abort.
Lemma ejcertAF_ok0 : ltac2:(tb__ "0|0|
S2S9S58S62S64S41S3dS48P64S49S4aA8SfA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ejcertAF_V : ltac2:(tb__ "0|6|
S7S61A1S54S7SeS7S54A1M0S18OF_;M1A2M2A1M3G3ScS7S55A1S54S7S59A1M4G4S2S7G0A1S5aG2G0SbG0G1A2M5R7A4S5aG2G0G5R6A4A3S2S9S58RaR9R8R6R5R4R3R2A8S58RaR9R7R6R5R4R3R2A8A3F_;Fexits;Fcuts;Fg;Fcps;Ffuel;FPhis';FPhis;Fnp;Fsg;").
Proof.
  intros sg np Phis Phis' fuel cps g cuts exits H. unfold ejcertAF, eecheckJAF_pf, echeckJAF_pf, VK. rewrite H. reflexivity.
Qed.

Lemma E_r15x_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S3bS39A2S4S0S1fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_rW1x_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S3cS39A2S4S0S20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_r15f_eq : ltac2:(tb__ "0|0|
S2S0S4fS1fS5S11S38S13S1S1fA1A1A3A2S1aA3"). Proof. reflexivity. Qed.
Lemma E_rW1f_eq : ltac2:(tb__ "0|0|
S2S0S4fS20S5S11S38S13S1S20A1A1A3A2S1bA3"). Proof. reflexivity. Qed.
Lemma T_r15f0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1aS1dS1aA1S28S51S1cA6S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1aS1dS1aA1S28S52S1cA6S2dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1bS1dS1bA1S29S51S1cA6S2fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1bS1dS1bA1S29S52S1cA6S30A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15f_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2cS1eA2S4S0S44A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2fS1eA2S4S0S46A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15okB_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2dS1eA2S4S0S2eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1okB_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S30S1eA2S4S0S31A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok_eq : ltac2:(tb__ "0|0|
S2S0S56S57S8S12S12S15P8dA1S36S24A1A4A1S2eA2S45A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok_eq : ltac2:(tb__ "0|0|
S2S0S56S57S8S12S12S15P8dA1S36S25A1A4A1S31A2S47A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8n00_eq : ltac2:(tb__ "0|0|
S2S0S5bS26S19S37S19A1S27S5fS5cS5eU1A1S5dA3A5S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8n0_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2aS4cA2S4S0S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_c8'_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S3aS4eA2S4S0S19A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok00_eq : ltac2:(tb__ "0|0|
S2S0S5bS26S19S37S19A1S27S60S5cS5eU1A1S5dA3A5S2bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok0_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2bS4dA2S4S0S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition o_blk8 : sobj := Eval vm_compute in last (ss_objs (ax_S T_c8ok0)) O_W.
Lemma T_c8okZ_eq : ltac2:(tb__ "0|1|
S3S2S7S14A1S17S1S21A1A1S5S14S17S1S22A1A1M0SaS14S63SdS14A1A3A3A3S2S0S65S21G0A2S22A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma T_c8ok_eq : ltac2:(tb__ "0|0|
S2S0S56S57S8S12S12S15P70A1S16Z80A1A4A1S22A2S43A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N15_eq : ltac2:(tb__ "0|0|
S2S0S4fS32S5S11S5S11S35S24A1S23S24A1A3S13S1S32A1A1A3A2S3eA3"). Proof. reflexivity. Qed.
Lemma NW1_eq : ltac2:(tb__ "0|0|
S2S0S4fS34S5S11S5S11S35S25A1S23S25A1A3S13S1S34A1A1A3A2S40A3"). Proof. reflexivity. Qed.
Lemma N8_eq : ltac2:(tb__ "0|0|
S2S0S4fS33S5S11S5S11S4bS23S16Z8A1A1A3S13S1S33A1A1A3A2S3fA3"). Proof. reflexivity. Qed.
End Lib_vec_reserve_rom_eqs.

(* [comment removed for export] *)
Module Lib_vec_reserve_rom_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "zlog15"; "bitem"; "KU"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "bd_subst"; "BIc"; "BIs"; "BXok_d"; "ZK"; "bud_le"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "SLit"; "sprop_eqb"; "sobj"; "SPUle"; "SVar"; "ss_next"; "rm"; "holds"; "SPBranch"; "DUnknown"; "SPNot"; "mkObj"; "rw"; "ob_cells"; "SAlu"; "sprop_below"; "cell"; "eval"; "ss_objs"; "sv_below"; "dflt_writable"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "pair"; "prod"; "cons"; "nil"; "nat"; "option"; "None"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "add"; "lt"; "pow"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom"; "vK"; "vW"; "bdP"; "s_r"; "nd0"; "vDt"; "kbytes"; "vE"; "cutsE"; "vC"; "kn15"; "ndG"; "vAl"; "E_c8'"; "O_W"; "Pre_c"; "Xk_r"; "tv0"; "B32"; "O_vec"; "vV"; "PD_rr"; "s_c"; "two47"; "vKn"; "z0"; "E_r15f"; "E_rW1f"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "R_c8"; "X15"; "X8"; "XW1"; "c8"; "exitsE"; "inj"; "ndN"; "spm"; "tvP"; "tvf0"; "vDn"; "B_EW"; "E_c8"; "E_r15"; "E_rW1"; "FUEL_vr"; "G_15"; "G_8"; "G_W1"; "O_alv"; "X_vr"; "cutpcs_vr"; "kbytesN"; "two48"; "xf_cbackN"; "xf_cbackZ"; "xf_ccall"; "xf_rback"; "xf_rcall"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "hd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "ND"; "JA_pre"; "nd_below"; "tv_factsA"; "ffinA"; "JA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "in_ranges"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Lib_vec_reserve_rom_pf.Sum"; "baseF"; "basez"; "Phis"; "s_rbd"; "Phi1"; "Posts_vrr"; "d0"; "injF"; "C0"; "Phi0"; "K0"; "KN15"; "Phi3"; "W0"; "injz"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.RR"; "Pre_rr"; "P_ok"; "P0_rr"; "tv0"; "P_fail"; "bd0"; "vPn"; "ndR"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"; "csz"; "T_afterA"; "call_checkTA"; "site_okA"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "AE_A"; "V_TOP"; "Wcan"; "unwind_stopJ"; "J_alloc_pre"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "Pre_calloc"; "V_RES"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "calloc_size"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "call_linkP"; "sv_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "import_subA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "JAF"; "phiK"; "efmeasA"; "phi_reads"; "JLAP"; "ejcertAF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Lib_vec_reserve_rom_pf"; "P0_vrr"; "Psi_keep"; "P0_vr"; "PDk_vrr"; "Psi_gdef"; "Psi_grown"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "T_ok"; "import_tv"; "tv_sub_eqb"; "FBx"; "ivar_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "robjs_okF"; "xrs_okF"; "FFx"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "drop_lastA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Lib_vec_reserve_rom_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr.

Lemma uval_kn15 : ltac2:(tb__ "0|1|
S19S44S5R1S4bA2S5dA2S0S3S5R2S55A2S46S5R2S4bA2M0S4aG0Z2A2A2A3F_;Frho;").
Proof.
  intros rho HK. unfold kn15. pose proof (uval_range rho vK).
  assert (E1 : uval rho (SAlu ALU_SRL vK (SLit 1)) = uval rho vK / 2).
  { unfold uval. rewrite U_srl_lit. change (2 ^ (1 mod 64)) with 2. reflexivity. }
  unfold B32 in HK. rewrite uval_add_small; rewrite E1; [lia|]. pose proof (Z.div_le_upper_bound (uval rho vK) 2). lia.
Qed.

Definition P0_vr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2S0S3S8bQ40M0S28Vr;P11A2A2Z0M1A3A1S2S0S3S8bG0S28Vr;PfA2A2G1A3A1F_;SedVFF;S8bG0S28Vr;PeA2A2Z30A3A2").

Definition P0_vrr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1SfaVFB;VFF;Vr;A3S3S1S44S5Vr;S50A2M0R1A2S47R1S46G0S45Z10S5Vr;S4bA2A2A2A2A2S2S0S3dS89Q8A1M1A1S22Vr;S8aQ40R2A2A2S3eG1A1A3A1F_;Fz;A2").

Definition Psi_keep (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S1S44S5Vr0;S50A2M0R1A2S47R1S46G0S45Z10S5Vr0;S4bA2A2A2A2A2S0S3dS89Q8A1A1S22Vrho;S8aQ40R2A2M1A2S22Vr0;G1A2A3F_;Fz;").

Definition Psi_gdef (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S1S44S5Vrho;S76A2M0R1A2S47R1S46G0S45Z10S5Vrho;S63A2A2A2A2A2S2S0S3dS89Q8A1M1A1S22Vrho;S8aQ40R2A2A2S3eG1A1A3A1F_;Fz;").
Definition Psi_grown (r0 rho : valuation) : Prop := ltac2:(tb__ "0|4|
S1S3S1S44Z0R1A2S47R1S45Z10S5Vr0;S54A2A2A2A2S1S0S3dS89Q8A1M0A1M1S22Vrho;S8aQ40M2S46S5Vrho;S76A2R2A2A2A2S22Vr0;S8aG2S46S5Vr0;S50A2R2A2A2A2M3A3S2S0G1G3S3eG0A1A3A1A2F_;Fj;SfcVr0;Vrho;A2A2").
Definition PDk_vrr : list pdescK := ltac2:(tb__ "0|4|
S3aS39S39S14S94A2M0S19S19OFrho;Fr0;M1A2M2S38G0G1S38S14S94S69S4fA4Sf9A4S3aG2S38G0G1S38S14S94S67S96S5cS3bS39S39S18S3A2S18A2A1M3S3bS7A1A3A4Sf9A4S3aG2S38G0G1S38S14S94S68S96S74G3S4dS4cS63A2A3A4SfdA4S3bG2A1A3A3A3").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Se5S19S37S89Q40A1A1Sf4OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sd6S43VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3S111VCST;R1A2S1S44Z0R2A2S47R2S110A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3S111VXGL;R1A2S1S44Z0R2A2S47R2S110A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S37S39S39S3S3A2S3A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Variable rho0 : valuation.

Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 := P0_vrr FB FF.
Definition Posts_vrr : list (axst * jpostA) := ltac2:(tb__ "0|0|
S10fVAInv;VCST;VXGL;VKc;Sf8S95SfbVFB;VFF;VBX;Aa").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S9bVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95Vnd;Ac").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
SdeS43S8cVrho0;Vtp0;SadA5").

Definition d0 : Z := uval rho0 vDt.
Definition C0 : Z := uval rho0 vC.
Definition K0 : Z := uval rho0 vK.
Definition KN15 : Z := uval rho0 kn15.
Definition W0 : Z := uval rho0 vW.

Definition Phi0 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S3S1S44SaeR1A2S47R1S46SaeS45Z10Sb2A2A2A2A2S0S3dS89Q8A1A1S22Vrho;S8aQ40R2A2M0A2S22Vrho0;G0A2A3F_;Fz;").

Definition Phi1 (kn : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|6|
S1S3S1S44Z0R1A2M0S47R1S45Z10M1Sb0A2A2A2S0S3dS89Q8A1M2A1M3S22Vrho;S8aQ40M4S46S5Vrho;S20P8dA1A2R2A2A2A2M5S22Vrho0;S8aG4S46SaeR2A2A2A2A3F_;Fj;S3S1G0S47R1S45G1Vkn;A2A2A2S2S0G3G5S3eG2A1A3A1F_;Fj;A2").

Definition Phi3 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S3S1S44Z0R1A2S47R1Z80A2A2S2S0S3dS89Q8A1M0A1S22Vrho;S8aQ40S46S5Vrho;S20P70A1A2R2A2A2A2S3eG0A1A3A1F_;Fj;").
Definition Phis : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|5|
S3aS39S37S4A1M0S19OFrho;M1A2M2S38G0G1S3bS4A1M3Sb1A4S3aG2S38G0G1S3aS4P8dG3A3M4SacSb3A1A4S3aG2S38G0G1G4SacSb5A1A4S3aG2S38G0G1S3aS4P70G3A3Sb4A4S3bG2A1A3A3A3A3").
Let JAFv (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95SefSaaVk;A2Vnd;Ad").

Lemma Phi1_reads : ltac2:(tb__ "0|0|
S3Sf1S3aS4P8dS3bS4A1A3SacR1A1A2Fkn;").
Proof.
  intros kn rho rho' HV _ HM [H1 H2].
  assert (E141 : uval rho' (SVar 141) = uval rho (SVar 141)) by (unfold uval; cbn [eval]; rewrite <- (HV 141%positive) by (cbn; tauto); reflexivity).
  unfold Phi1. rewrite E141. split; intros j Hj; rewrite <- HM; [exact (H1 j Hj) | exact (H2 j Hj)].
Qed.
Lemma Phis_reads : ltac2:(tb__ "0|3|
Sb7S39S37S4A1M0S19OF_;M1A2M2G2Sf1S41G0G1R1A3S42G0G1R1A3A2Lp;SaaA3").
Proof.
  unfold Phis. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [fst snd]; try apply Phi1_reads; unfold Phi3, Phi0.
  - intros rho rho' _ _ HM H z Hz. rewrite <- HM. exact (H z Hz).
  - intros rho rho' HV _ HM H j Hj.
    assert (E112 : uval rho' (SVar 112) = uval rho (SVar 112)) by (unfold uval; cbn [eval]; rewrite <- (HV 112%positive) by (cbn; tauto); reflexivity).
    rewrite E112, <- HM. exact (H j Hj).
Qed.
Lemma ejcertAF_ok : ltac2:(tb__ "0|0|
S0S35Sf3S43S8cSaaS7bS81P64S53S70A8S36A3").
Proof. rewrite (ejcertAF_V segs NF Phis PhisV FUEL_vr cutpcs_vr 100 cutsE exitsE eq_refl). exact ejcertAF_ok0. Qed.

Lemma JA_P0 : ltac2:(tb__ "0|0|
S94S14S19S37S89Q40A1A1S9eS8dS43VJAv;R5A1R4R3R2R1A6S1VP0;Vrho0;A1Sd9S8cVrho0;R4A3A2F_;Fw;Ftp;Frho;FS;Fnd;").
Proof. intros nd S rho tp [tr [ms md]] [_ (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. Qed.
Lemma vals_uval : ltac2:(tb__ "0|1|
S19S4Sd9S8cVrho0;R2A3SffR2S8cA2S0S3S5R4S20R3A1M0A2S5Vrho0;G0A2A3F_;F_;Fv;Frho;").
Proof. intros rho v Hav Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. Qed.

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|4|
S1S0S35S90S1aS1dS1fS20P1eA1M0S73Z40A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fG0S20PaA1M1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fG1S5fA2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS2aSe9S5fS1cZ20A1A3S1cS62A1M2A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS5fG2A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fG1G2A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS1cZ1A1S52A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS52S1cZ1000A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS4cS1cS83A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS4bS1cS5dA1M3A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS51S4cA1S1cS77A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS51S4bA1G3A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS1cZ7fff7f800000A1G0A2A1VF;A3S36A3S0S35S90S1aS1dS1fG0S1cZ7fffff800000A1A2A1VF;A3S36A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : aceil + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_v : uval rho (SVar 10) <= uval rho vV /\ uval rho vV + 32 <= 2 ^ 47;
  bz_e : 1 <= uval rho vE <= 4096;
  bz_w : uval rho vW <= 2 ^ 48;
  bz_k : uval rho vK <= B32;
  bz_ew : uval rho (kbytes vW) = uval rho vE * uval rho vW /\ uval rho (kbytes vW) <= B_EW;
  bz_ek : uval rho (kbytes vK) = uval rho vE * uval rho vK /\ uval rho (kbytes vK) <= B32;

  bz_top : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S19S3S1S44Z0R1A2S44R1S5R2S20PaA1M0A2A2A2S0S3S5R3S73R2A1A2S49S5R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RR.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S19S37S1aA1Sb7S1aS23R2A1R1A3Sa8R2A1Sa9R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B1' & BV1 & BV2 & BV3 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2. zf HT1. zf HT2.
  pose proof (holds_mem _ _ _ HF BV1) as V1. pose proof (holds_mem _ _ _ HF BV2) as V2. pose proof (holds_mem _ _ _ HF BV3) as V3. zf V1. zf V2. zf V3.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B1') as H1'. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8.
  zf H1. zf H1'. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold aceil, two47, RR.two47, two48, B_EW, B32 in *.
  rewrite !uval_lit in H2, H3, H4, H5, H6, H7, H8, HT1, HT2 by lia.
  rewrite uval_spm in H1 by lia.
  assert (EW : uval rho (kbytes vW) = uval rho vE * uval rho vW) by (unfold kbytes; apply uval_mul_small; nia).
  assert (EK : uval rho (kbytes vK) = uval rho vE * uval rho vK) by (unfold kbytes; apply uval_mul_small; nia).
  pose proof (uval_range rho vV). unfold two47, RR.two47 in V2, V3. rewrite uval_lit in V3 by lia. rewrite uval_add_small in V2 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in V2 by lia.
  constructor; unfold aceil, B_EW, B32; lia.
Qed.

Lemma robjs_r : ltac2:(tb__ "0|1|
S19S37S1eA1M0S0G0R1S3aS1eS27S20PaA1S1cN40A1S1cZ0A1S29S93S1eS59R1A3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa9R3A1S0S3S102Vrho0;A1S8bQ40S28R4ScbA2A2A3S10aVCST;Vrho0;VFB;VFF;R5S3bS39S18S18A2A1S3bS39S39S18S3A2S18A2A1R4A8F_;F_;F_;FR;Frho;").
Proof.
  intros rho R -> BZ ET o a Ho Hr. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. left. destruct BZ. lia.
Qed.
Lemma xrs_r : ltac2:(tb__ "0|0|
S19Sa9R1A1S0S3S102Vrho0;A1S8bQ40S28R2ScbA2A2A3SedVFF;S5R3S57A2Z30A3S10bVCST;VXGL;Vrho0;VFB;VFF;R4S3bS39S18S18A2A1S3bS39S39S18S3A2S18A2A1S5bA9F_;F_;F_;Frho;").
Proof.
  intros rho BZ ET HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. left. destruct BZ. lia.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
Qed.

Lemma P0_now : ltac2:(tb__ "0|1|
S19Sd9S8cVrho0;R1A3VP0;Vrho0;A1S1S2S0S3S5R3S4bA2Z0M0A3A1S2S0S3S5R4S50A2G0A3A1F_;SedVFF;S5R3S57A2Z30A3A2F_;F_;Frho;").
Proof.
  intros rho Hav [(A & C) _]. unfold uval, vK, vDt, vV, vAl. cbn [eval].
  rewrite <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 14%positive eq_refl).
  auto.
Qed.

Lemma HIN_r : ltac2:(tb__ "0|3|
S14S37S1eA1M0S19Sd8S0G0R3S3aS1eS27S20PaA1S1cN40A1S1cZ0A1S29S93S1eS59R3A3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa8S1bS15R5A1A1A1S0S18Sa1S4eR6A1PcA2S57A3S0S18Sa1S4eR7A1PdA2S50A3S0S18Sa1S4eR8A1PeA2S4bA3S0S35S90S1aS1dS1fS2aSe9S50S51S4bA1A3S20P1eA1A2A1S1bS15R9A1A1A3S36A3S0S35S90S1aS1dS1fS50S1cS62A1A2A1S1bS15RaA1A1A3S36A3Sb1R9A1Sb7S1aS23RaA1S1bS15RcA1A1A3VP0;Vrho0;A1Sd9S8cVrho0;RcA3S1S10aVCST;Vrho0;VFB;VFF;RdS3bS39S18S18A2A1M1S3bS39S39S18S3A2S18A2A1M2ReA8S1S10bVCST;VXGL;Vrho0;VFB;VFF;RdG1G2S5bA9SbbS106VFB;RdG1A3S10cVFF;RdG2A3Sa3Sa2RdReRcA3S4eRfA1A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR HB Hs12 Hs13 Hs14 HD30 HD47 HPhi HF HP0 Hav. destruct (P0_now rho Hav HP0) as (_ & HA).
  pose proof (holds_mem _ _ _ HF HD47) as F4. zf F4. unfold two47, RR.two47 in F4. rewrite uval_lit in F4 by lia.
  pose proof (basez_of rho _ HF HB) as BZ. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  pose proof (holds_mem _ _ _ HF HD30) as F3. zf F3.
  split; [exact (robjs_r rho R HR BZ ET)|]. split; [exact (xrs_r rho BZ ET HA)|].
  split.
  - unfold RR.P0_ra. rewrite rw_call', Hs12. destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl.
    split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
  -
    intros z Hz. unfold uval, RR.vP, RR.vK in Hz. cbn [eval] in Hz. rewrite !rw_call', Hs13, Hs14 in Hz. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in Hz.
    assert (ED : uval rho vDt = d0) by (unfold d0; exact (vals_uval rho 15 Hav ltac:(reflexivity))).
    assert (EK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 17 Hav ltac:(reflexivity))).
    destruct BZ as [Bsp Bv Be Bw Bk _ [EK16 _] [BT1 BT2]]. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in F3.
    pose proof (uval_range rho vDt). unfold B32 in Bk. change (uval rho vE) with 16 in EK16.
    rewrite uval_add_small in F3 by (rewrite EK16; lia). rewrite EK16 in F3.
    rewrite rm_absorb_out.
    + rewrite (HPhi z) by lia. destruct HP0 as [_ HDEF]. apply HDEF. unfold d0, K0 in *. lia.
    + intros (o & Ho & Hr). rewrite HR in Ho. cbn in Ho. rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia).
      destruct Ho as [<-|[<-|[]]].
      * apply range_lit' in Hr; [|lia|lia]. lia.
      * unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. lia.
Qed.

Lemma robjs_c : ltac2:(tb__ "0|3|
S19Se5S37S1eA1M0S0G0R1S3aS1eS27S20PaA1S1cN40A1S1cZ0M1A1S29S93S1eS59R1A3A1S25A5S3aS1eS27S5fS1cZ10M2A1S1cZ20A1S3aS2cS6fG2S4bA2S3aS2cS6fZ18S52A2S3bS2cA1A3A3S25A5S3aS1eS7fS3bS1eA1A3A3A3A3Sa9R4A1S103R5Se7Se6R4A1A1A2S0S3S5R6S4bA2G1A3S9aVFF;R6A2SedVFF;S5R8S57A2Z30A3Sc7VCST;R8S3eS3A1R9R7A5F_;F_;F_;F_;F_;F_;FR;FAi;Frho;").
Proof.
  intros rho Ai R -> BZ HTK HK0 HFF HA o a Ho Hr. cbn in Ho. apply T_ok_rw in HTK as [HTK HTR]. destruct Ho as [<-|[<-|[<-|[]]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - apply range_lit' in Hr; [|lia|lia]. left. destruct BZ. lia.
  - unfold O_alv in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
Qed.
Lemma xrs_c : ltac2:(tb__ "0|1|
S19Se5S37S39S18S18A2A1M0S0G0R1S80S50S4bA2A3Sa9R4A1S103R5Se7Se6R4A1A1A2S0S3S5R6S4bA2Z0A3S9aVFF;R6A2SedVFF;S5R8S57A2Z30A3Sc8VCST;VXGL;R8S3eS3A1R9R7A6F_;F_;F_;F_;F_;F_;FX;FAi;Frho;").
Proof.
  intros rho Ai X -> BZ HTK HK0 HFF HA r a Hr Ha. cbn in Hr. apply T_ok_rw in HTK as [HTK HTR]. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. left. destruct BZ. lia.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ _ [EK _] _]. rewrite EK, HK0 in Ha. lia.
Qed.

Lemma baseF_E_c8' : ltac2:(tb__ "0|0|
Sa8S1bS15S58A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_r15f : ltac2:(tb__ "0|0|
Sa8S1bS15S65A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_rW1f : ltac2:(tb__ "0|0|
Sa8S1bS15S66A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X15 : ltac2:(tb__ "0|0|
Sa8S1bS15S6cA1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW1 : ltac2:(tb__ "0|0|
Sa8S1bS15S6eA1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X8 : ltac2:(tb__ "0|0|
Sa8S1bS15S6dA1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma site_c8 : ltac2:(tb__ "0|2|
S19Sc6VAInv;VCST;VXGL;S8cVrho0;VP0;VFB;VFF;S58S61S58A1M0S6bR1S4fS3eS3A1Se5Sd8S1S1S44Z1S5R3Sc3G0A1A2M1A2S47G1S48Z2Z27A2A2A2S1S0S3S45S5R3Sa1G0PcA2A2S5R3Sa1G0PdA2A2A2G1A3ScdSccU1A1Sc9Sa3Sa2R3S6bR1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HA).
  pose proof (basez_of rho _ HF baseF_E_c8') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HA]|].
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). change (wsub_get (s_c E_c8') 12) with (SLit 8). change (wsub_get (s_c E_c8') 13) with vE.
  factz HF (SPUle vDt (SVar 30)) HDA. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in HDA.
  destruct BZ as [Bsp [BV1 BV2] Be Bw Bk [EW BEW] [EK BEK] [BT1 BT2]]. rewrite uval_mul_lit by lia. rewrite uval_lit by lia.
  split; [lia|]. split; [lia |].
  unfold unwind_stopJ. cbn [last_link link_var nth Wcan Wcan_from eval]. right. rewrite !rw_call'. change (wsub_get (s_c E_c8') 52) with vDt. change (wsub_get (s_c E_c8') 28) with (SAlu ALU_ADD vV (SLit 16)).
  repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Definition s_rbd (kn : sv) : list bitem := ltac2:(tb__ "0|2|
S3fS7S3aS7SfZ1M0Z0M1S51Vkn;A1A3S3aS7SeG1S45Z2S8A2G0A3S3bS7A1A3A3S4dS4cVkn;A2A3").

Lemma sums_bdP : ltac2:(tb__ "0|1|
S19S18S18S1S0S3SbS4dR2R1A2M0R3A2S46S49S45Z6S5R3S51R2A1A2A2S45Z4S5R3S51R1A1A2A2A2S45Z20S5R3S52A2A2A2A3S0S3SaG0R3A2S45S45Z2S8A2S49S11S6S5R3R1A2A1A2A2A3A2Fk;Fw;Frho;").
Proof. intros. unfold bdP, PHI, KLG. cbn [bsumV bsumK]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma sums_s_rbd : ltac2:(tb__ "0|2|
S19S18S1S0S3SbSabR1A1M0R2A2S46S5R2S51R1A1A2SbS4dS4cR1A2M1R2A2A2A3S0S3SaG0R2A2S46S45Z2S8A2SaG1R2A2A2A3A2Fkn;Frho;").
Proof. intros. unfold s_rbd, BIs, BIc. cbn [bsumV bsumK app]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma bd_nn_bdP : ltac2:(tb__ "0|1|
S19S18S18S44S45Z4S5R3S51R1A1A2A2S46S45Z6S5R3S51R2A1A2A2S45Z20M0S5R3S52A2A2A2A2S44S5R4R2A2S48Z2G0A2A2S9S4dR4R3A2R5A2F_;F_;Fk;Fw;Frho;").
Proof.
  intros rho w k H1 H2. unfold bd_nn, bdP, PHI, KLG. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c]; [lia|].
  pose proof (zlog15_ZK _ H2). lia.
Qed.
Lemma bd_nn_s_rbd : ltac2:(tb__ "0|0|
S19S18S9S4dS4cR1A2R2A2S9SabR2A1R3A2F_;Fkn;Frho;").
Proof.
  intros rho kn H. unfold s_rbd. apply bd_nn_app. split; [|exact H]. unfold bd_nn, BIs, BIc. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c].
  - pose proof (uval_range rho (kbytes kn)). lia.
  - lia.
Qed.

Record injz (rho : valuation) (kn : sv) : Prop := IJ {
  ij_b : 4 * uval rho (kbytes vK) <= 3 * uval rho (kbytes kn);
  ij_a : 4 * uval rho (kbytes kn) <= 6 * uval rho (kbytes vW) + 32 * uval rho vE;
  ij_c : 1 <= uval rho (kbytes kn) <= B32;
  ij_e : uval rho (kbytes kn) = uval rho vE * uval rho kn }.
Definition injF (kn : sv) (F : list sprop) : Prop := ltac2:(tb__ "0|0|
S0S35S92S1aS1aS90S1aS1dR1A1VF;A3Lf;S71Vkn;A1A3S36A3").
Lemma injz_of : ltac2:(tb__ "0|0|
S19S18S37S1aA1Sb7S1aS23R3A1R1A3Sa9R4A1SafR4R3A2S44S5R6R5A2S48Z2Z31A2A2Sb6R7R6A2F_;F_;F_;F_;FF;Fkn;Frho;").
Proof.
  intros rho kn F HF BZ H Hkn. unfold injF, inj in H. cbn [forallb] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  zf F1. zf F2. zf F3. zf F4. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  pose proof (uval_range rho kn) as Rkn.
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite !uval_lit in F3, F4 by lia.
  rewrite !uval_mul_lit in F1 by (rewrite ?EKn; lia). rewrite uval_add_small in F2 by (rewrite !uval_mul_lit by lia; lia).
  rewrite !uval_mul_lit in F2 by lia.
  constructor; unfold B32; lia.
Qed.

Lemma grow15 : ltac2:(tb__ "0|0|
S19Sa9R1A1S2S0S3S5R2S4bA2Z0A3A1S47S5R3S4bA2S5R3S4cA2A2S47S5R4S4cA2S5R4S55A2A2S44S46S6S5R5S4bA2A1Z1A2S6S5R5S55A2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Bv Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2 |- *.
  pose proof (uval_range rho vK). pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma growW1 : ltac2:(tb__ "0|0|
S19Sa9R1A1S2S0S3S5R2S4bA2Z0A3A1S47S5R3S4bA2S5R3S4cA2A2S44S5R4S55A2S5R4S4cA2A2S44S46S6S5R5S4bA2A1Z1A2S6S5R5S4cA2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Bv Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2.
  pose proof (uval_range rho vK).
  destruct (Z_lt_ge_dec (uval rho vK) 2).
  - assert (E1 : uval rho vK = 1) by lia. rewrite E1, zlog15_1. pose proof (zlog15_ge1 (uval rho vW) ltac:(lia)). lia.
  - pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). pose proof (zlog15_mono (uval rho vK + uval rho vK / 2) (uval rho vW) ltac:(lia)). lia.
Qed.
Lemma grow0 : ltac2:(tb__ "0|0|
S19S18S0S3S5R2S4bA2Z0A3S44Z8S5R3R2A2A2S44S46S6S5R4S4bA2A1Z1A2S6S5R4R3A2A1A2F_;F_;Fkn;Frho;").
Proof. intros rho kn -> H. rewrite zlog15_0. pose proof (zlog15_ge1 (uval rho kn) ltac:(lia)). lia. Qed.

Lemma pay_r : ltac2:(tb__ "0|3|
S14S18Sa8S1bS15R2A1A1A1SafR2S1bS15R3A1A1A2S19Sb7S1aS23R1A1S1bS15R5A1A1M0A3Sa9R2A1S1S44S5R3R6A2M1S48Z2Z31A2A2S44S46S6S5R3S4bA2A1Z1A2S6G1A1A2A2F_;F_;Frho;Sc2S8cVrho0;VP0;G0S1cZ0M2A1G2S4dS4cS4bA2SabR4A1A8F_;F_;F_;Fkn;FE;").
Proof.
  intros E kn HB HI HG. split; [reflexivity|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as [Hkn HL]. pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|apply bd_nn_s_rbd; exact NN]].
  - rewrite uval_lit by lia. destruct (sums_s_rbd rho kn) as [-> _]. destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. lia.
  - destruct (sums_s_rbd rho kn) as [_ ->]. destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_r15 : ltac2:(tb__ "0|1|
Sc2S8cVrho0;VP0;S1bS15S65A1A1S1cZ0M0A1G0S4dS4cS4bA2SabS55A1A8").
Proof.
  apply pay_r; [exact baseF_E_r15f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (grow15 rho BZ HK0 HKW HWn)].
  destruct BZ as [Bsp Bv Be Bw Bk _ _ _]. rewrite (uval_kn15 rho Bk). pose proof (uval_range rho vK). lia.
Qed.
Lemma pay_rW1 : ltac2:(tb__ "0|1|
Sc2S8cVrho0;VP0;S1bS15S66A1A1S1cZ0M0A1G0S4dS4cS4bA2SabS4cA1A8").
Proof.
  apply pay_r; [exact baseF_E_rW1f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (growW1 rho BZ HK0 HKW HWn)]. destruct BZ; lia.
Qed.

Lemma pay_c : ltac2:(tb__ "0|2|
S14S18S18Sa8S1bS15R3A1A1A1SafR3S1bS15R4A1A1A2S19Sb7S1aS23R1A1S1bS15R6A1A1M0A3Sa9R2A1S1S44S5R3R7A2M1S48Z2Z31A2A2S1S0S3S5R3S4bA2Z0A3S1S44Z8G1A2S0S3S5R3R6A2S5R3S51R7A1A2A3A2A2A2F_;F_;Frho;Sc2S8cVrho0;VP0;G0R4S8S4dS4cS4bA2S4dS4cR5A2A8F_;F_;F_;Fcst;Fkn;FE;").
Proof.
  intros E kn cst HB HI HG. split; [reflexivity|]. split; [unfold KU; lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as (Hkn & HK0 & H8 & ->). pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  pose proof (grow0 rho kn HK0 H8) as HL.
  destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|exact NN]].
  - destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. rewrite EK, HK0. lia.
  - destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_c8 : ltac2:(tb__ "0|0|
Sc2S8cVrho0;VP0;S1bS15S58A1A1Sc3S61S58A1A1S8S4dS4cS4bA2S4dS4cS1cZ8A1A2A8").
Proof.
  apply pay_c; [exact baseF_E_c8' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). rewrite uval_mul_comm. fold (kbytes (SLit 8)).
  rewrite uval_lit by lia. destruct BZ; repeat split; lia.
Qed.

Lemma inj_holds : ltac2:(tb__ "0|4|
S19S18Sa9R2A1S44S5R3R2A2S48Z2Z31A2A2S44S45Z4M0S45S5R4S52A2M1S5R4S4bA2A2A2S45Z3S45G1S5R4R3A2A2A2A2S44S45G0S45S5R5S52A2M2S5R5R4A2A2A2S46S45Z6S45G2S5R5S4cA2A2A2S45Z20G2A2A2A2S1S44Z1S45S5R6S52A2S5R6R5A2A2M3A2S44G3S5dA2A2Sb7S1aS23R7A1S71R6A1A3F_;F_;F_;F_;F_;Fkn;Frho;").
Proof.
  intros rho kn BZ Hkn H1 H2 H3. destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  assert (Hkn32 : uval rho kn <= 4294967295) by nia.
  pose proof (uval_range rho kn).
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  unfold inj, B32. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite !uval_mul_lit by (rewrite ?EK, ?EKn; lia). rewrite EK, EKn. lia.
  - rewrite uval_add_small by (rewrite !uval_mul_lit by (rewrite ?EW; lia); rewrite EW; lia).
    rewrite !uval_mul_lit by (rewrite ?EW, ?EKn; lia). rewrite EW, EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. exact Hkn32.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S3S37S89Q40A1A1S9dF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S8eS14S19S37S89Q40A1A1S9dSb7S1aS23R3A1S1bS15R4A1A1A3VTR;S8dS43R6R5R4R3A5R2A2M0F_;G0F_;FQa;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Qa : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Qa) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Qa.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S9dS9dS9dS9eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQa;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S9dS9dS9eS2R3R1A1A1Fw;VTR;R3R2A2F_;FQa;FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S9dOS9dS9eR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQa;FX;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Qa : assn), (forall a, TR (P a) Qa) -> TR (fun w => exists a, P a w) Qa.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S8eS8eS14S14Sa4S37S1eA1M0S37S39S14SdfA2M1A1S37S39S18S18A2M2A1S9dS19S37S89Q40A1A1M3G2S91G2R1R5A3S91G2R2S16RbA1A3F_;Fr;S0S3dG0A1Se2RaR9R8A3S40G0R7A2A3S0S35Se1RbRaR9R8Sb8G1S14S41S14SdfA2R7A4A5S36A3S19G3VTR;S8dS43RfRdR2R1A5SdeS43S21S15RdA1A1R2R1RaA5A2Ftp1;Frho1;S37Sf5A1M4Sd8Sf4S8fS43R9R8R10S38G4Sf6R3Sf7R2R1A2A4A5R13RaR9R4R2A4R13Sa3Sa2RbRfSe4R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S14SdfG4Sd8Sf4S19G3G4Sd8Sf4S91G1S38S14SdfRaR9A4R14A3S8fS43R12R11R19S38G4Sf6R9Sf7R8R7A2A4A5R1cR13R12RaR8A4Sd9S21S15R1aA1A1Sa3Sa2R14R18Se4R9R13RaA3A3R19A2R8A3S8fS43R9R8ReS38G4Sf6R7Sf7R6R5A2A4A5ReSa3Sa2R16R1aSe4RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S112R17Se4RcR16RdA3R1bR1cR1dR10R1eR19RbA9S19SdbR18Se4RdR17ReA3R1cR1dS15R1eA1S15R1fA1S15R11A1R1RcA9VTR;S8dS43Se3R11Sa3Sa2R19R1dSe4ReR18RfA3A3R1eA2R18RdRcA5S113R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S8dS43R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQa;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_phi : ltac2:(tb__ "0|0|
S19OF_;S94S14S19S37S89Q40A1A1S9dR6R3A1VTR;S8dS43VJAv;R6A1R5R4R3A5R2A2F_;VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95R7R6AdR5R4R3A5R2A2F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Hypothesis CCALLOC : ltac2:(tb__ "0|1|
Se5S19S37S89Q40A1A1VTR;S8dS43SceVAInv;SccU1A1M0Sc9R3VKc;Sd7A6Sd2ScaG0Sc9A3R2R1A5SdeS43S8cR2R1Sd1ScaVAInv;VCST;VXGL;G0Sc9R3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CREALLOC : ltac2:(tb__ "0|1|
S37S39S3S3A2M0A1S37S39G0S3A2A1S13S19S37S89Q40A1A1S10Z2R3A2VTR;S8dS43S97VAInv;VCST;VXGL;VKc;SbbR6R5A2R6R5R4S95Sc0SbcSbeA2AaSb9R3R2A5SdeS43S8cR3R2S10fVAInv;VCST;VXGL;VKc;SbbS95S60R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|5|
S14S94S3cS39S3S18A2M0S19S37S89Q40A1A1M1S3G1S91S39S39S39S14S94A2M2S3cA2M3G0A2S38G3G0S38G2S3cS38S14S94R8R7A4R6A4R5A4S53A3SefSaaR7R5A3S1S44Z0Sf0S38G3G0S38G2S3cS38S14S94RaR9A4R8A4R7A4R6A2M4A2S47G4R4A2A2VTR;S8dS43VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|2|
S14S94S19OF_;M0S19G0F_;S19S37S89Q40A1A1M1S3G1S91S39S14SdfA2S38S14SdfR8Sf2VAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S95R7R5AbA4SadA3S19R8R1A1R8Vrho0;R2A2F_;Fr;VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95R8R9AdRaR6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;FPsi;FPhi;Fnd;FP;").

Ltac meas := unfold efmeasA; cbn [ef_rank ef_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsE exitsE Posts_vrr PDk_vrr PostsCk map fst snd]; do n right; left; reflexivity.

Lemma TR_phi_in : ltac2:(tb__ "0|0|
S19OF_;S94S14S19S37S89Q40A1A1S9dR6R3A1VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95R7R6AdR5R4R3A5R2A2VTR;S8dS43VJAv;R7A1R6R5R4A5R3A2F_;F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Proof. intros Phi nd S rho tp Qa HP H. eapply TR_pre; [|exact H]. intros w Hw. apply SPA_JAF_intro; [exact Hw | exact HP]. Qed.

Lemma X_N : ltac2:(tb__ "0|6|
S14S14S37S1aA1S3S19S37S89Q40A1A1M0S3G0S0S14S101R8S3fS1aR6S1bS15R8A1A1A3A2R7A3S91S39S39S39S14S94A2M1S3cA2M2S39S3S18A2M3A2S38G2G3S38G1S3cS38S14S94R8S4fA4U0M4A4S38S3S18R6S64A4A4S53A3S44S45S46R7Z1A2S48Z2Z40A2A2R4A2S44Z0R8A2S0S35S92S1aS2bS21S15RcA1M5A1A1S3fS1aRaS1bG5A1A3A3S36A3S19Sb7S1aS23R1A1S1bS15ReA1A1A3Sb7S1aS23R2A1RdA3F_;Frho;VTR;S8dS43VJAFv;G4S4fA2ReRaR9A5VFAM;R8R7A2A2F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fr;Ffl;FNs;FXs;").
Proof.
  intros Xs Ns fl r rho tp b tp0 HN Hin Hb Hr Hbelow Hinj. apply TR_phi. intros HPhi.
  eapply TR_pre; [|apply (REENTER Ns nd0 0%nat (r, z0)); [exact Hin | exact HPhi | meas]].
  intros w Hw. rewrite <- HN. apply (SPA_refacts_JA segs); [exact Hw | exact Hbelow |].
  intros tr md _ HF. apply Forall_app. split; [exact (Hinj _ HF) | exact HF].
Qed.

Lemma X_X15 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z5aS48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S6cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X15 N15 (injR kn15 ++ inj kn15) 80 rho tp b tp0 N15_eq); [innth 1 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X15) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  factz HF (SPUle vW (SAlu ALU_ADD vC (SLit 1))) HWC. factz HF (SPUle vC vK) HCK.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  rewrite uval_add_small in HWC by (rewrite uval_lit by lia; lia). rewrite uval_lit in HWC by lia.
  apply Forall_app. split.
  { unfold injR. constructor; [apply (proj2 (h_ule _ _ _)); lia|]. constructor; [|constructor].
    apply (proj2 (holds_bltu _ _ _)). repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e). rewrite (uval_kn15 r Bk). lia. }
  apply (inj_holds r kn15 BZ); rewrite ?(uval_kn15 r Bk); unfold B32; try nia.
Qed.
Lemma X_XW1 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z5aS48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S6eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW1 NW1 (injR vW ++ inj vW) 80 rho tp b tp0 NW1_eq); [innth 2 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW1) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  factz HF (SPUle vW (SAlu ALU_ADD vC (SLit 1))) HWC. factz HF (SPUle vC vK) HCK.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  rewrite uval_add_small in HWC by (rewrite uval_lit by lia; lia). rewrite uval_lit in HWC by lia.
  apply Forall_app. split.
  { unfold injR. constructor; [apply (proj2 (h_ule _ _ _)); lia|]. constructor; [|constructor].
    apply (proj2 (holds_bltu _ _ _)). repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e). lia. }
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_X8 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z5aS48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S6dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X8 N8 (injZ ++ inj (SLit 8)) 80 rho tp b tp0 N8_eq); [innth 3 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X8) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPUle vW (SAlu ALU_ADD vC (SLit 1))) HW8. factz HF (SPUle vC vK) HCK.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  pose proof (uval_range r vW). pose proof (uval_range r vC). rewrite uval_add_small in HW8 by (rewrite uval_lit by lia; lia). rewrite uval_lit in HW8 by lia.
  apply Forall_app. split.
  { unfold injZ. constructor; [|constructor]. apply (proj2 (h_ule _ _ _)). rewrite uval_lit by lia. lia. }
  apply (inj_holds r (SLit 8) BZ); rewrite ?uval_lit by lia; unfold B32; try nia.
Qed.

Lemma C_calloc_contra : ltac2:(tb__ "0|1|
S14S19S37S89Q40A1A1S9dS0S35S90S1aS1dS24SeaS4bS1cZ0A1M0A3A1S1bS15R4A1A1A3S36A3S0S35S90S1aS1dS24Se8S50G0A3A1S1bS15R5A1A1A3S36A3VTR;S8dS43VJAFv;U0S4fA2R6R5R4A5R3A2F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2. apply TR_phi. intros _. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  destruct (P0_now rho Hav HP0) as (HKD & _ & _).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1, F2 by lia. exact (HKD F1 F2).
Qed.
Lemma C_realloc_contra : ltac2:(tb__ "0|1|
S14S19S37S89Q40A1A1S9dS0S35S90S1aS1dS26S24SeaS4bS1cZ0A1M0A3A1A1S1bS15R4A1A1A3S36A3S0S35S90S1aS1dS26S24Se8S50G0A3A1A1S1bS15R5A1A1A3S36A3Sa8S1bS15R6A1A1A1VTR;S8dS43VJAFv;U0S4fA2R7R6R5A5R4A2F_;F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2 HB. apply TR_phi. intros _. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & (HN & _ & _) & _).
  pose proof (basez_of rho _ HF HB) as [_ _ _ _ _ _ [EK _] _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (tnz_of_fact rho vDt (kbytes vK) F2) as Hnz. zf F1.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1 by lia.
  cbn [nd_tv nd0] in HN. destruct (proj1 (Forall_forall _ _) HN (vDt, kbytes vK) ltac:(left; reflexivity) Hnz) as (Hpos & _).
  unfold tvv in Hpos. cbn [snd] in Hpos. change (bv_unsigned (eval rho (kbytes vK))) with (uval rho (kbytes vK)) in Hpos.
  rewrite EK, F1 in Hpos. lia.
Qed.

Lemma X_P_keep : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U0S4fA2S69R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply (POST P_keep nd0 (phiK Phis 0) Psi_keep); [innth 0 | intros r Hr z Hz; exact (Hr z Hz)]. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U0S96S5cS3bS39S39S18S3A2S18A2A1S3bS7A1A3A2S67R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply (POST P_fail (ND tv0 [] []) (phiK Phis 0) Psi_keep); [innth 1 | intros r Hr z Hz; exact (Hr z Hz)]. Qed.

Lemma X_G : ltac2:(tb__ "0|8|
S14Sa4S18S18S19OF_;S19S37S89Q40M0A1A1M1S3G1S0S35S17R9S68R8A3S36A3S0S35Sa7R9S8cA2S36A3S0S35SfeS8cS21S15RbA1A1A2S36A3S0S35S98S21S15RcA1A1S56RaR9A2A2S36A3S0S35S105RcS3aS39S18S18A2M2S38S18S18RbS82RaA1A4S3bG2A1A3S74A3S36A3S0S35S12S1bS15ReA1A1SdRdS4dS4cS63A2A2S4dS4cRbA2A3S36A3S0S18Sa1ReP8cA2RdA3S0S18Sa1RfP8dA2RdA3S0S35S90S1aS1dS1fS54S4bA2A1S1bS15R11A1A1A3S36A3S19Sb7S1aS23R1A1S1bS15R13A1A1A3Sd9S8cVrho0;R2A3R11R3A1S1S3S1S44Z0R1A2M3S47R1S45Z10M4Sb0A2A2A2S0S3dS89Q8A1M5A1M6S22R6S8aG0S46S5R6R16A2R2A2A2A2M7S22Vrho0;S8aG0S46SaeR2A2A2A2A3F_;Fj;S3S1G3S47R1S45G4S5R5R14A2A2A2A2S2S0G6G7S3eG5A1A3A1F_;Fj;A2F_;F_;F_;Fr;VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95RfS56R11R10A2AdR13ReRdA5VFAM;RcRbA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FPhi;Fkn;Fp;Fs;FG;").
Proof.
  intros G s p kn Phi rho tp b tp0 Hent Hid Hnf Hnb Htv Hbud Hs140 Hs141 HCK HPSI.
  apply TR_phi. intros HPhi. apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  destruct (HPSI rho HF Hav HPhi) as [HC HDF].
  apply (TR_pre (SPA segs (JAv (ND tvP [] (bdP vW vKn))) P_grown (rho_sub rho s) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc G P_grown s (ndG p kn) (ND tvP [] (bdP vW vKn)) rho tp w Hent Hid Hnf Hnb Htv eq_refl Hbud eq_refl Hw). }
  apply (TR_phi_in (fun r => Psi_grown rho0 r) (ND tvP [] (bdP vW vKn)) P_grown (rho_sub rho s) tp).
  - assert (E140 : uval (rho_sub rho s) vDn = uval rho p) by (unfold uval, vDn; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs140; reflexivity).
    assert (E141 : uval (rho_sub rho s) vKn = uval rho kn) by (unfold uval, vKn; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs141; reflexivity).
    assert (EM : rm (rho_sub rho s) = rm rho) by reflexivity. unfold Psi_grown, Psi_gdef. rewrite E140, E141, EM. split.
    + intros j Hj. split; [exact (HC j Hj) | apply (proj2 HP0); unfold d0, C0 in *].
      pose proof (vals_uval rho 16 Hav ltac:(reflexivity)) as EC. pose proof (vals_uval rho 17 Hav ltac:(reflexivity)) as EK.
      pose proof (holds_mem _ _ _ HF HCK) as FCK. zf FCK. change (uval rho vC) with (uval rho (SVar 16)) in FCK. change (uval rho vK) with (uval rho (SVar 17)) in FCK.
      change vDt with (SVar 15). change vK with (SVar 17). change vC with (SVar 16) in Hj. lia.
    + intros z Hz. replace z with (uval rho p + (z - uval rho p)) by lia. apply HDF. lia.
  - apply (POST P_grown (ND tvP [] (bdP vW vKn)) (fun r => Psi_grown rho0 r) Psi_grown); [innth 2 | intros r Hr; exact Hr].
Qed.

Lemma X_G15 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U1S56S20P8dA1S55A2A2S7cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_G G_15 s_g15 (SVar 141) kn15 (phiK Phis 1) rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF Hav [H1 H2]. split; [exact H1|]. intros j Hj. apply H2. unfold KN15.
  replace (uval rho0 kn15) with (uval r kn15); [exact Hj|]. unfold uval. rewrite (eval_agree_vals NF rho0 r kn15 Hav eq_refl). reflexivity.
Qed.
Lemma X_GW1 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U2S56S20P8dA1S4cA2A2S7eR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_G G_W1 s_gW1 (SVar 141) vW (phiK Phis 2) rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF Hav [H1 H2]. split; [exact H1|]. intros j Hj. apply H2. unfold W0, vW. rewrite <- (vals_uval r 13 Hav ltac:(reflexivity)). exact Hj.
Qed.
Lemma X_G8 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U3S56S20P70A1S1cZ8A1A2A2S7dR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_G G_8 s_g8 (SVar 112) (SLit 8) (phiK Phis 3) rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF Hav H. split.
  - intros j Hj. exfalso. pose proof (uval_range r vC).
    factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) F1. factz HF (SPUle vC vK) F2. rewrite uval_lit in F1 by lia.
    pose proof (vals_uval r 16 Hav ltac:(reflexivity)) as EC. change (uval r vC) with (uval r (SVar 16)) in F2. unfold C0 in Hj. change vC with (SVar 16) in Hj. lia.
  - intros j Hj. apply H. rewrite uval_lit in Hj by lia. lia.
Qed.

Lemma U_Z_to_bv : ltac2:(tb__ "0|1|
S3S1S44Z0R1A2S47R1S48Z2Z40A2A2A2S0S3S8bQ40M0S8aG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. exact Hz. Qed.

Lemma not_in_R : ltac2:(tb__ "0|3|
S37S1eA1M0S19S3S0G0R3S3aS1eS27S20PaA1S1cN40A1S1cZ0M1A1S29S93S1eS59R3A3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa9R3A1S1S44G1R3A2S47R3S8bQ40M2S28R4ScbA2A2A2A2S2Sa5R5R6S8aG2R4A2A3A1F_;F_;F_;Fz;Frho;FR;").
Proof.
  intros R rho z HR BZ Hz (o & Ho & Hr). destruct BZ as [Bsp Bv Be Bw Bk _ _ [BT1 BT2]]. rewrite U_Z_to_bv in Hr by lia.
  rewrite HR in Ho. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - apply range_lit' in Hr; [|lia|lia]. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. lia.
Qed.

Lemma X_E_r : ltac2:(tb__ "0|1c|
S14S14S14S14S14S14S14S14S37S1eA1M0S18S3S3cS19S37S89Q40A1A1M1S3G1S0S3dS14A1M2SecR10S88A2S40S14RfA2A3S0S14S101R10S3fS1aS75S1bS15R10A1A1A3A2RfA3S0S35S90S1aS1dS26S24Se8S50S1cZ0M3A1M4A3A1A1S1bS15R11A1A1A3S36A3S0G0RbS3aS1eS27S20PaA1S1cN40A1G4S29S93S1eS59RbA3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa8S1bS15R12A1A1A1S0S18Sa1S4eR13A1PcA2S57A3S0S18Sa1S4eR14A1PdA2S50A3S0S18Sa1S4eR15A1PeA2S4bA3S0S18Sa1S4eR16A1P21A2RfA3S0S35S90S1aS1dS1fS54S4bA2A1S1bS15R17A1A1A3S36A3S0S35S90S1aS1dS1fS2aSe9S50S51S4bA1A3S20P1eA1M5A2A1S1bS15R18A1A1A3S36A3S0S35S90S1aS1dS1fS50S1cS62A1M6A2A1S1bS15R19A1A1A3S36A3S0S35S10eS5bS16R1aA1A2S36A3S0S3dG0A1Se2R1bSb9S4eR1bA1A3S40G0R15A2A3S0S35Se1R1cSb9S4eR1cA1R16Sb8S39S39S14S94A2M7S19S19OF_;M8F_;M9A2MaS14GaS41S14S94S41G7G9R1A3A3Ld;S60A4A5S36A3S0S35Sc5S8cS4eR1dA1A2S36A3S0S35SddS4eR1eA1S8cA2S36A3S0S35SfeS8cS21S15R1fA1A1A2S36A3S0S35S98S21S15R20A1A1S96S3fS39S18S18A2MbS3bGbA1McS5cA3S3bS39S39S18S3A2S18A2A1MdS4dS4cS4bA2MeA3A2S36A3S0S35ScS21S15R21A1A1S4dS4cR1aA2A2S36A3S0S35S105S4eR22A1S5cSbcA3S36A3Sc2S8cVrho0;VP0;S1bS15R23A1A1G4G3GeS3fS7SdS4eR23A1SbeA2S4dS4cR1cA2A3A8S0S35S92S39S109G9A2MfGfS10dSb9S8cS4eR25A1M10S21S15R25A1A1S41S109G9R1A3A5Ld;S60A3S36A3S0S14S108Sb9R25G10R1fSbdS5bA6R24A3S0G2SecR25S87A2S40S14R24A2A3M11S0S14S108Sb9R27S4eR27A1R21SbaS5bA6R24A3G11S0S14S100S99S38S18S18S20P8dA1M12S51R22A1A4A1R25A2R24A3S0S37GbA1M13S104Se0S4eR2aA1Sb9SbaR2aA4Sc1A2S3aGbS38S18S18G12S51R23A1A4GcA3A3S0G13S104Se0S4eR2bA1Sb9SbdR2bA4SbcA2S5cA3S0S18Sa6Se0S4eR2cA1Sb9SbaR2cA4SbfA2G12A3S0S35SdcS107S8cS4eR2dA1S21S15R2dA1M14A1S15SbaA1A4SbfA2S36A3S0S35S90S1aS1dS1fS2aSe9G12S51R27A1A3G5A2A1S1bS15R2bA1A1A3S36A3S0S35S90S1aS1dS1fR28S1cS5dA1A2A1S1bS15R2cA1A1A3S36A3S0S35S90S1aS1dS1fG12G6A2A1S1bG14A1A3S36A3S0S35S2fS8cR2aA2S36A3S0S3R2aS5Vrho0;R2bA2A3S0S35S90S1aS1dS24SebS4bR2cA3A1S1bS15R33A1A1A3S36A3S0S35S90S1aS1dS26S24Se8G12G4A3A1A1S1bS15R30A1A1A3S36A3S0S35S92S1aS2bS21S15R31A1M15A1A1S3fS1aS99S38S18S18G12S51R2eA1A4A1S1bG15A1A3A3S36A3S0S35S92S1aS2bS21S15R37A1M16A1A1S3fS1aS75S1bG16A1A3A3S36A3S91S39S39G7S3cA2M17S39S3S18A2M18A2M19S38G17G18S38G7S3cS38S14S94R35S72R30A1A4U0M1aA4S38S3S18Z3cS64A4M1bA4S53A3S91G19S38G17G18S38G7S3cS38S14S94R33S96S3aGbS38S18S18G12S51R31A1A4GcA3GdS4dS4cR31A2A3A4R2fA4G1bA4S53A3S0G8SefSaaR30A2SacR31A1A3S44S45Z46S48Z2Z40A2A2R2eA2VTR;S8dS43VJAFv;G1aS4fA2R3dR31R30A5VFAM;R2fR2eA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;FKN;Fkn;FR;FTok;FTokB;FTok0;FTf;FTf0;FEf;FEx;FE;").
Proof.
  intros E Ex Ef Tf0 Tf Tok0 TokB Tok R kn KN k rho tp b tp0 HEx HEf HD HR HB Hs12 Hs13 Hs14 Hs33 HCK HD30 HD47 HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass HPAY Hpd
         HTf0 HTf HTok0 HTokB HTok Htvok Htvf Himp Hiv HN30 HknB HN47 Hknb HKN HKkn HpN Hbelow HbelowE HinF HinOK HPhik Hb.
  apply TR_phi. intros HPhi.

  eapply TR_pre with (P := SPA segs (JAv nd0) Ef rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_rcall rho E Ex tp w HEx Hw) as Hw1.
    rewrite <- HEf. apply (SPA_refacts_JA segs); [exact Hw1 | exact HbelowE | ].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF HD). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof (basez_of rho _ HF HB) as BZ.
  pose proof (holds_mem _ _ _ HF HCK) as FCK. pose proof (holds_mem _ _ _ HF HD30) as FD30. pose proof (holds_mem _ _ _ HF HD47) as FD47.
  pose proof (holds_mem _ _ _ HF HKkn) as FKkn.
  zf FCK. zf FD30. zf FD47. zf FKkn. unfold two47, RR.two47 in FD47. rewrite uval_lit in FD47 by lia.
  assert (ED : uval rho vDt = d0) by (unfold d0; exact (vals_uval rho 15 Hav ltac:(reflexivity))).
  assert (EC : uval rho vC = C0) by (unfold C0; exact (vals_uval rho 16 Hav ltac:(reflexivity))).
  assert (EK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 17 Hav ltac:(reflexivity))).
  assert (EKN : uval rho kn = KN) by (rewrite HKN; unfold uval; rewrite (eval_agree_vals NF rho0 rho kn Hav Hknb); reflexivity).
  assert (EK16 : uval rho (kbytes vK) = 16 * uval rho vK) by (destruct BZ as [_ _ _ _ Bk _ [EKb _] _]; rewrite EKb; reflexivity).
  rewrite uval_add_small in FD30 by (rewrite EK16; destruct BZ; unfold B32 in *; lia). rewrite EK16 in FD30.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in FD30.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX RR.P0_rr PTrue (fun _ H => H) (fun _ _ _ H => H) RR.Pre_rr (RR.ndR RR.tv0 RR.bd0) PD_rr NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CREALLOC eq_refl
           Ef (s_r Ef) R Xk_r rho tp [] tv0 [] (bdP vW vK) (bdP vW kn) ANone (FAM b tp0) HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass eq_refl HPAY Hpd).
  - intros Ai ms HF' HP0' Hav' HBf HFF HN HD' HZ HFR HM HT HTK. apply (HIN_r Ef R rho ms HR HB Hs12 Hs13 Hs14 HD30 HD47 HPhi HF' HP0' Hav').
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag _ HPSI. cbn [PD_rr RRP.PDk_rr In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd nd_tv nd_bd nd_am RR.ndR ND am_subst app];
      destruct HPSI as (r0c & rhoL & HPsi & Hd1 & Hd2 & Hd3); cbn [fst snd] in HPsi, Hd1, Hd2, Hd3.
    +
      rewrite HTf0, Htvf. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tf (ndN kn) 0%nat (60, z0)); [exact HinF | | meas]].
      { intros w Hw. exact (SPA_axforms segs _ xf_rback rho' Tf0 Tf tp' w HTf Hw). }
      intros z Hz. pose proof (uval_range rho vDt).
      assert (NR : ~ in_ranges rho R (Z_to_bv 64 z)) by (apply (not_in_R R rho z HR BZ); lia).
      destruct (Hd2 _ NR) as [E1 E2]. rewrite E2. rewrite (HPsi z); [rewrite E1; exact (HPhi z Hz)|].
      unfold uval, RR.vP, RR.vK. rewrite !Hd1. cbn [sv_subst]. rewrite Hs13, Hs14. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). lia.
    +
      rewrite HTok0, Htvok. change (bd_subst _ []) with (@nil bitem). cbn [app].
      apply TR_facts. intros HF2.
      pose proof (holds_mem _ _ _ HF2 HN30) as FN30. pose proof (holds_mem _ _ _ HF2 HknB) as FknB. zf FN30. zf FknB. unfold B32 in FknB. rewrite uval_lit in FknB by lia.
      assert (H30 : (30 < ss_next (ax_S Ef))%positive) by (eapply Pos.lt_le_trans; [|apply (proj1 (Pos.leb_le _ _)); exact Hnf]; reflexivity).
      assert (E30 : uval rho' (SVar 30) = bv_unsigned (rw rho V_TOP)) by (unfold uval; cbn [eval]; rewrite <- (proj1 Hag 30%positive H30); reflexivity).
      assert (HknN : sv_below (ss_next (ax_S Ef)) kn = true) by (eapply sv_below_mono; [apply (proj1 (Pos.leb_le _ _)); exact Hnf | exact Hknb]).
      assert (EKn' : uval rho' kn = uval rho kn) by (unfold uval; rewrite <- (eval_agree_vals _ rho rho' kn Hag HknN); reflexivity).
      assert (EKn : uval rho' (kbytes kn) = 16 * uval rho' kn) by (unfold kbytes, vE; apply uval_mul_lit; lia).
      pose proof (uval_range rho' (SVar 141)) as R141. pose proof (holds_mem _ _ _ HF2 HN47) as FN47. zf FN47. unfold two47, RR.two47 in FN47. rewrite uval_lit in FN47 by lia.
      rewrite uval_add_small in FN30 by (rewrite EKn; lia). rewrite EKn, E30 in FN30.
      assert (E141 : uval rho' (SVar 141) = uval rhoL RR.vPn).
      { unfold uval. rewrite <- (Hd3 RR.vPn Hiv), Himp. reflexivity. }
      assert (ER0K : uval r0c RR.vK = uval rho vK) by (unfold uval, RR.vK; rewrite Hd1; cbn [sv_subst]; rewrite Hs14; reflexivity).
      assert (ER0P : uval r0c RR.vP = uval rho vDt) by (unfold uval, RR.vP; rewrite Hd1; cbn [sv_subst]; rewrite Hs13; reflexivity).
      assert (ER0N : uval r0c RR.vKn = uval rho kn) by (unfold uval, RR.vKn; rewrite Hd1; cbn [sv_subst]; rewrite Hs33; reflexivity).
      destruct HPsi as [HPsiC HPsiD]. rewrite ER0K, ER0P in HPsiC. rewrite ER0N in HPsiD.
      assert (NR1 : forall j, 0 <= j < 16 * uval rho kn -> ~ in_ranges rho R (Z_to_bv 64 (uval rho' (SVar 141) + j))).
      { intros j Hj. apply (not_in_R R rho _ HR BZ). lia. }
      assert (HP1 : Phi1 KN rho').
      { split.
        - intros j Hj.
          assert (HjK : 0 <= j < 16 * uval rho vK) by lia.
          assert (NR2 : ~ in_ranges rho R (Z_to_bv 64 (uval rho vDt + j))) by (apply (not_in_R R rho _ HR BZ); pose proof (uval_range rho vDt); lia).
          destruct (Hd2 _ (NR1 j ltac:(lia))) as [_ E2]. destruct (Hd2 _ NR2) as [E3 _].
          rewrite E2, E141. destruct (HPsiC j HjK) as [E4 _]. rewrite E4, E3, ED. apply HPhi. unfold K0 in *. rewrite <- ED. lia.
        - intros j Hj. rewrite <- EKN in Hj. destruct (Hd2 _ (NR1 j Hj)) as [_ E2]. rewrite E2, E141. apply HPsiD. exact Hj. }
      eapply TR_pre; [|apply (REENTER Tok (ND [(SVar 141, kbytes kn)] [] (bdP vW kn)) k (60, z0)); [exact HinOK | rewrite HPhik; exact HP1 | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_rback rho' Tok0 TokB tp' w HTokB Hw) as Hw1.
      rewrite <- HTok. unfold ax_add_facts.
      change (ax_setS TokB (add_facts (tv_factsA (SVar 141, kbytes kn)) (ax_S TokB))) with (ax_with_facts TokB (tv_factsA (SVar 141, kbytes kn) ++ ss_facts (ax_S TokB))).
      apply (SPA_refacts_JA segs); [exact Hw1 | exact Hbelow |].
      intros tr md HJ HF3. apply Forall_app. split; [|exact HF3].
      eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
      apply tnz_of_fact. exact (holds_mem _ _ _ HF3 HpN).
Qed.

Lemma X_E_r15 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z46S48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S79R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_r15 E_r15x E_r15f T_r15f0 T_r15f T_r15ok0 T_r15okB T_r15ok R_r15 kn15 KN15 1%nat rho tp b tp0 E_r15x_eq E_r15f_eq);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact baseF_E_r15f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact T_r15f0_eq | exact T_r15f_eq | exact T_r15ok0_eq | exact T_r15okB_eq | exact T_r15ok_eq
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 4 | innth 5 | reflexivity | exact Hb].
  pose proof pay_r15 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes kn15); BIc 0 (2 * KU) 1] ++ bdP vW kn15) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
Qed.
Lemma X_E_rW1 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z46S48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S7aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_rW1 E_rW1x E_rW1f T_rW1f0 T_rW1f T_rW1ok0 T_rW1okB T_rW1ok R_rW1 vW W0 2%nat rho tp b tp0 E_rW1x_eq E_rW1f_eq);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact baseF_E_rW1f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact T_rW1f0_eq | exact T_rW1f_eq | exact T_rW1ok0_eq | exact T_rW1okB_eq | exact T_rW1ok_eq
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 6 | innth 7 | reflexivity | exact Hb].
  pose proof pay_rW1 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes vW); BIc 0 (2 * KU) 1] ++ bdP vW vW) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
Qed.

Lemma X_E_c : ltac2:(tb__ "0|19|
S14S14S14S14S14S14S14S14Sa4S37S1eA1M0S1eS19S37S89Q40A1M1A1M2S3G2S0S3dS14A1M3SecRfS86A2S40S14ReA2A3S0Sa4R8S61RfA1A3S0S3dG0A1Se2R10S5aR9A3S40G0R8A2A3S0S35Se1R11S5aRaR9S3aS14ScfScaSccU1A1M4Sc9A3M5S3aS14Sd0ScaG4Sc9A3M6S3bS14A1A3A3A5S36A3S0S35Sc5S8cRbA2S36A3S0S35SfeS8cS21S15R13A1A1A2S36A3S0S35S98S21S15R14A1A1S4fA2S36A3S0S35ScS21S15R15A1A1S4dS4cS1cZ8A1M7A2M8A2S36A3S0S35S2fS21S15R16A1A1Sc3RfA1A2S36A3S0S18Sa1Se0R10S5aG6R17A4Sd3A2S20SdaS21S15R17A1A1UaM9A2A1A3S0S18S20SdaS21S15R18A1A1G9A2A1S20P70A1MaA3Sc2S8cVrho0;VP0;S1bS15R19A1A1Sc3R12A1S8S4dS4cS4bA2G8A8Sc6VAInv;VCST;VXGL;S8cVrho0;VP0;VFB;VFF;R1aR13R12R10S4fS3eS3A1Se5Sd8S1S1S44Z1S5R12Sc3R15A1A2MbA2S47GbS48Z2McZ27A2A2A2S1S0S3S45S5R12Sa1R15PcA2A2S5R12Sa1R15PdA2A2A2GbA3ScdG4Sc9Sa3Sa2R12R14R1A3R15A2A3A2A2Lms;LAi;AfS0S35S90S1aS1dS26S24SeaS4bS1cZ0A1MdA3A1A1S1bS15R1bA1A1A3S36A3S0S14Sc4S5aR1cR15R14G5A5R1bA3S0G3SecR1cS84A2S40S14R1bA2MeA3S0S14Sc4S5aR1eR17R16G6A5R1bA3S0G3SecR1cS85A2GeA3S19S0G1S2dR1Sc3R1aA1A2S2dR1S1cZ80A1MfA2A3Fr;S0G0S2eS15R1dA1A1M10S3fS1eS2eS15R1cA1A1S3aS1eR18S3bS1eA1A3A3A3S0S14S114R1eG10A2R1dA3S0S18S31R1aA1GaA3S0S18S34R1bA1GdA3S0S18S33R1cA1GfA3S0S35S30S32R1dA1A1S36A3S0S14S100S99S38S18S18GaGfA4A1M11R22A2R21A3S0S35S90S1aS1dS26S24Se8GaGdA3A1A1S1bS15R23A1A1A3S36A3S0S35S92S1aS2bS21S15R24A1M12A1A1S3fS1aG11S1bG12A1A3A3S36A3S91S39S39S39S14S94A2M13S3cA2M14S39S3S18A2M15A2M16S38G14G15S38G13S3cS38S14S94R28S72G7A1A4U0M17A4S38S3S18Z3cS64A4M18A4S53A3S91G16S38G14G15S38G13S3cS38S14S94R25S56GaG7A2A4U3A4G18A4S53A3S44S45Z46S48GcZ40A2A2R20A2VTR;S8dS43VJAFv;G17S4fA2R2eR23R22A5VFAM;R21R20A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FoB;FR;Fs;FTok;FTokZ;FTok0;FTok00;FTn;FTn0;FE;FE0;").
Proof.
  intros E0 E Tn0 Tn Tok00 Tok0 TokZ Tok s R oB rho tp b tp0 HE0 Hs He Hchk Htp Hnf Hnb Hbr Hcsz Hres H112 HPAY HSITE HK0
         HTn0 HTn HTok00 HTok0 Hcst HoZ HdZ Hb Hl Hh Hdw HTok Hp0 Hbelow HinN HinOK Hbnd.
  apply TR_phi. intros _.
  eapply TR_pre with (P := SPA segs (JAv nd0) E rho tp); [intros w Hw; exact (SPA_axforms segs _ xf_ccall rho E0 E tp w HE0 Hw)|].
  apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].

  pose proof (holds_mem _ _ _ HF HK0) as FK0. zf FK0. rewrite uval_lit in FK0 by lia.
  assert (EK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 17 Hav ltac:(reflexivity))).
  assert (PHI0 : forall r, Phi0 r) by (intros r z Hz; exfalso; pose proof (uval_range rho vK); lia).
  subst s. unfold Pre_c in *.
  apply (calloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           (Wcan 1) UStopLeOrPc E (s_c E) R rho tp nd0 (bdP vW (SLit 8)) (FAM b tp0) CCALLOC He Hchk Htp Hnf Hnb Hbr Hcsz Hres HPAY (fun _ _ _ _ => I) HSITE).
  -   intros rho' tp'. rewrite HTn0. cbn [nd_tv nd_fr nd0].
    eapply TR_pre; [|apply (REENTER Tn (ndN (SLit 8)) 0%nat (60, z0)); [exact HinN | exact (PHI0 rho') | meas]]. intros w Hw. exact (SPA_axforms segs _ xf_cbackN rho' Tn0 Tn tp' w HTn Hw).
  -   intros rho' tp'. rewrite HTok00, H112. cbn [nd_tv nd_fr nd0].
    apply (TR_pre (fun w => exists r2, Phi3 r2 /\ SPA segs (JAv (ndG (SVar 112) (SLit 8))) Tok r2 tp' w)).
    { intros w Hw0. pose proof (SPA_axforms segs _ xf_cbackZ rho' Tok00 Tok0 tp' w HTok0 Hw0) as Hw. clear Hw0.

      apply (SPA_JA_tv_ext segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ((SVar 112, csz (s_c E)) :: tv0) ((SVar 112, SLit 128) :: tv0)) in Hw.
      2: { intros _. split; [cbn [map]; unfold tvv; cbn [fst snd]; rewrite (Hcst rho'); reflexivity|].
           intros [|k] t t' Ht Ht'; cbn [nth_error] in Ht, Ht'; [injection Ht as <-; injection Ht' as <-; unfold tnz; cbn [fst]; tauto|].
           rewrite Ht in Ht'. injection Ht' as <-. tauto. }
      apply (SPA_JA_drop_tv segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue _ [] (bdP vW (SLit 8)) 1) in Hw.
      2: {
           intros _ t Ht. unfold tv0 in Ht. cbn [nth_error] in Ht. injection Ht as <-. right.
           destruct (JA_P0 _ _ _ _ w Hw) as [_ Hav'].
           assert (EK' : uval rho' vK = 0).
           { transitivity (uval rho0 (SVar 17)); [exact (vals_uval rho' 17 Hav' ltac:(reflexivity))|].
             transitivity (uval rho vK); [symmetry; exact (vals_uval rho 17 Hav ltac:(reflexivity)) | exact FK0]. }
           unfold tvv. cbn [snd]. change (bv_unsigned (eval rho' (kbytes vK))) with (uval rho' (kbytes vK)).
           unfold kbytes. rewrite uval_mul_small by (rewrite EK'; lia). rewrite EK'. lia. }
      cbn [remove_nth] in Hw.
      change (ND [(SVar 112, SLit 128)] [] (bdP vW (SLit 8))) with (NDA [(SVar 112, SLit 128)] [] (bdP vW (SLit 8)) ANone) in Hw.
      destruct w as [tr [ms md]].

      destruct (JA_absorb_tr segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue [(SVar 112, SLit 128)] [] (bdP vW (SLit 8)) ANone 0 (SVar 112) (SLit 128)
                  Tok0 (ss_objs (ax_S TokZ)) oB (SLit 128) rho' tp' tr ms md HoZ eq_refl Hl Hh Hdw) as (Hw6 & OUT & DEF & _).
      { intros r _. rewrite Hb. rewrite !uval_lit by lia. lia. }
      { exact Hw. }
      rewrite HdZ in Hw6. rewrite Hb, (uval_lit rho' 128) in DEF by lia.
      set (r2 := rho_absorb rho' [oB] (vms md tp' ms)) in *. exists r2. split.
      - intros j Hj. apply DEF. unfold r2, uval. rewrite eval_absorb. change (bv_unsigned (eval rho' (SVar 112))) with (uval rho' (SVar 112)). lia.
      - rewrite <- HTok. unfold ax_add_facts.
        change (ax_setS TokZ (add_facts (tv_factsA (SVar 112, SLit 128)) (ax_S TokZ))) with (ax_with_facts TokZ (tv_factsA (SVar 112, SLit 128) ++ ss_facts (ax_S TokZ))).
        apply (SPA_refacts_JA segs); [exact Hw6 | exact Hbelow |].
        intros tr' md' HJ HF2. apply Forall_app. split; [|exact HF2].
        eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
        apply tnz_of_fact. exact (holds_mem _ _ _ HF2 Hp0). }
    apply TR_exw; intros r2. eapply TR_pureP; [intros w [H _]; exact H|]. intros HP3.
    eapply TR_pre; [intros w [_ Hw]; exact Hw|].
    apply (REENTER Tok (ndG (SVar 112) (SLit 8)) 3%nat (60, z0)); [exact HinOK | exact HP3 | meas].
Qed.
Lemma X_E_c8 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z46S48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S78R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_c8 E_c8' T_c8n00 T_c8n0 T_c8ok00 T_c8ok0 T_c8okZ T_c8ok (s_c E_c8') R_c8 o_blk8 rho tp b tp0 E_c8'_eq eq_refl);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact pay_c8 | exact (site_c8 rho) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact T_c8n00_eq | exact T_c8n0_eq | exact T_c8ok00_eq | exact T_c8ok0_eq
    | intros r; apply bv_eq; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact (proj1 T_c8okZ_eq) | exact (proj2 T_c8okZ_eq) | reflexivity | reflexivity | reflexivity | reflexivity
    | exact T_c8ok_eq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 8 | innth 9 | exact Hb].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S14S94S3cS39S3S18A2M0S19S37S89Q40A1A1M1G1S91S39S39S39S14S94A2M2S3cA2M3G0A2S38G3G0S38G2S3cS38S14S94R7R6A4R5A4R4A4S70A3VTR;S8dS43VJAFv;R6R7A2R8R4R3A5VFAM;Sf0S38G3G0S38G2S3cS38S14S94R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FkX;FndX;FX;").
Proof.
  intros X ndX kX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]; injection H as <- <- <- <-.
  - apply X_X15. meas.
  - apply X_XW1. meas.
  - apply X_X8. meas.
  - apply X_E_r15. meas.
  - apply X_E_rW1. meas.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply X_E_c8. meas.
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply X_P_keep.
  - apply X_P_fail.
  - apply X_G15.
  - apply X_GW1.
  - apply X_G8.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S9cS43VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sd4S43ScaVAInv;VCST;VXGL;A5").

Theorem vec_reserve_rom_sum : ltac2:(tb__ "0|0|
S37S89Q40A1A1Sa0S43Vok;S8dS43S97VAInv;VCST;VXGL;VKc;Sf8VFB;VFF;A2VFB;VFF;VBX;S95S4fAaS6aVrho0;R1A5SdeS43S8cVrho0;R1SadA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_vr cutpcs_vr 100
                (map efdrop cutsE) (map efdrop exitsE) ok (Q tp0) Hok (ejcertAF_jcertAF segs NF Phis _ _ _ _ _ ejcertAF_ok))
         with (ndT := nd0) (kT := 0%nat); [|left; reflexivity].
       intros X ndX kX rho tp Hin. apply in_map_iff in Hin as ([[[X' nd'] k'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map (nodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) (map efdrop cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (TRs_pureP segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (aca_calloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros FBc FFc BXc rho1 tp1 HB. apply (RRP.realloc_rom_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ok Hok AC tp1).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP _. apply (reenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis ok (map efdrop cutsE) T nd k); [|exact HP].
         apply in_map_iff. exists (T, nd, k, rv'). auto.
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (exit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue ok rho0 tp0 Phi Psi nd Posts_vrr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sd5S43ScaVAInv;VCST;VXGL;A5").

Theorem vec_reserve_rom_sum_ex : ltac2:(tb__ "0|0|
S37S89Q40A1A1S9fS43S8dS43S97VAInv;VCST;VXGL;VKc;Sf8VFB;VFF;A2VFB;VFF;VBX;S95S4fAaS6aVrho0;R1A5SdeS43S8cVrho0;R1SadA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_vr cutpcs_vr 100 cutsE exitsE (Q tp0) ejcertAF_ok)
         with (ndT := nd0) (kT := 0%nat) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX kX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (TRe_pureP segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (acx_calloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros FBc FFc BXc rho1 tp1 HB. apply (RRP.realloc_rom_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ACX tp1).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP Hm. apply (ereenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis cutsE T nd k rv'); [exact HinT | exact HP | exact Hm].
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (eexit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue rho0 tp0 Phi Psi nd Posts_vrr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Existence.

End Sum.

Print Assumptions vec_reserve_rom_sum.
Print Assumptions vec_reserve_rom_sum_ex.
End Lib_vec_reserve_rom_pf.

