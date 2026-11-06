(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_029.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2 g2 g3.

(* [comment removed for export] *)
Module Fps_tailB.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "ss_next"; "sv"; "sprop"; "SLit"; "agree_below"; "rl"; "sstate"; "holds"; "obj_range"; "ss_lenient"; "ss_objs"; "rm"; "ranges_disjoint"; "cell"; "reg_sv"; "rw"; "ob_cells"; "mkCell"; "ob_dflt"; "ss_pc"; "swf"; "DList"; "SAlu"; "SVar"; "dflt_writable"; "is_arr"; "ob_base"; "ob_hi"; "ob_lo"; "odefault"; "ro_addr"; "smatch"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "@Corelib.Init.Datatypes"; "bool"; "list"; "Some"; "option"; "true"; "length"; "cons"; "false"; "nat"; "nil"; "prod"; "pair"; "None"; "app"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "obj_ext"; "ax_base"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "facts_fps"; "BASEF"; "fs_ok"; "runp"; "FUEL_T"; "set_facts"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "to_nat"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs"; "tailB_out"; "obj_far"; "tailB_post"; "iov01_ok"; "splitsB"; "tailBR_out"; "FSB"; "finishB"; "subB"; "tailB"; "tailBR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "Posts_fps"; "P_fps"; "T8"; "blA"; "seg"; "FA1"; "FA5"; "FA6"; "XQ1"; "XQ2"; "XW"; "bexps_eqb"; "dropL"; "post_sub"; "x_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Fps_tailR"; "rcall_out"; "rc_Tm"; "rcall"; "sR1"; "sR2"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB.TailB"; "Jp"; "rho_wl"; "WLF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "ALU_ADD"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB.TailB.PostB"; "rho_fin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Fps_tailC"; "LOWV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA"; "exts_rl_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "fp_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates"; "unlist_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates"; "axc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA"; "Kf"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "rom_bytes_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj MuslWL DrvGlue CursorGlue DrvPristine.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Fps_tailR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvFp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_run OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Fps_tailC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Fps_tailR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma splitsB_SPA : ltac2:(tb__ "0|0|
S46S3bS3eScS5S2bS38Q40A1A1S85S0S2dScA1S5dR6S3dR5A1A2S2cScR4A2A3S44S28R8R6R4R3R2A6S44S28R9S41R7R6A2R5R4R3A6F_;F_;Fw;Ftp;Frho;FS6;FA;Fe;FJ;").
Proof.
  intros J e A S6 rho tp w H Hsp. unfold splitsB, obindW in H.
  destruct (split_obj_at (ax_S A) 0 (SLit (-1128))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-1096))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 2 (SLit (-464))) as [S3|] eqn:E3; [|discriminate].
  destruct (split_obj_at S3 3 (SLit e)) as [S4|] eqn:E4; [|discriminate].
  destruct (split_obj_at S4 5 (SLit (FERR + 120))) as [S5|] eqn:E5; [|discriminate].
  pose proof (SPA_split segs J rho A 0 (SLit (-1128)) S1 tp w E1 Hsp) as H1.
  pose proof (SPA_split segs J rho (ax_setS A S1) 1 (SLit (-1096)) S2 tp w E2 H1) as H2.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS A S1) S2) 2 (SLit (-464)) S3 tp w E3 H2) as H3.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS A S1) S2) S3) 3 (SLit e) S4 tp w E4 H3) as H4.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS A S1) S2) S3) S4) 5 (SLit (FERR + 120)) S5 tp w E5 H4) as H5.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS (ax_setS A S1) S2) S3) S4) S5) 6 (SLit (FERR + 124)) S6 tp w H H5) as H6.
  rewrite !ax_setS_setS in H6. exact H6.
Qed.

Lemma obj_far_disjoint : ltac2:(tb__ "0|0|
S5S3bS3bS4S97R4A1S51Z0R4A2S51R4S55Z2Z20A2A2S0S2aS5aR6R5R4A3S2eA3S12SeR8R5A2S35S3bS3bR7R6A4A2F_;F_;F_;F_;Fo;Fhi0;Flo0;Fr;").
Proof.
  intros r lo0 hi0 o (L1 & L2 & L3 & L4 & L5 & L6) Hlo0 Hhi0 H. unfold obj_far in H. unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd].
  pose proof (urange (rw r 10)) as R10.
  destruct (ob_base o) as [bz|bi|op ba bb| | | | |] eqn:Eb; try discriminate.
  - destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply Z.eqb_eq in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst bz.
    cbn [eval]. rewrite lit_unsigned, Z.mod_small by lia. rewrite !soff_lit_small by (unfold HSE in *; lia).
    apply Bool.orb_true_iff in H4. rewrite !Z.leb_le in H4. unfold HSE in *. lia.
  - destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply Pos.eqb_eq in H0. subst bi. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    cbn [eval]. rewrite !soff_lit_small by lia. lia.
  - destruct op; try discriminate. destruct ba as [|ai| | | | | |]; try discriminate.
    destruct bb as [c|v2| | | | | |]; try discriminate.
    + destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
      apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
      apply Pos.eqb_eq in H0. subst ai. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
      rewrite !soff_lit_small by lia. rewrite (U_addc r (SVar 10) c (bv_unsigned (rw r 10)) eq_refl) by lia. lia.
    + destruct (ob_lo o) as [lz| | | | | | |]; try discriminate.
      apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1]. apply Pos.eqb_eq in H0. apply Pos.eqb_eq in H1. apply Z.eqb_eq in H2. subst ai v2 lz.
      rewrite soff_lit_small by lia. change (SAlu ALU_ADD (SVar 18) (SVar 20)) with sX. lia.
Qed.
Lemma objs_far_disjoint : ltac2:(tb__ "0|0|
S5S3bS3bS2bS4A1S97R4A1S51Z0R4A2S51R4S55Z2Z20A2A2S0S2aS87S4S5aR6R5A2R4A3S2eA3S48S4S4S12SeR9R1A2S35S3bS3bR8R7A4A2Lo;R5A3F_;F_;F_;F_;Fobjs;Fhi0;Flo0;Fr;").
Proof.
  intros r lo0 hi0 objs HL Hlo Hhi H. apply Forall_forall. intros o Ho. apply obj_far_disjoint; [exact HL | exact Hlo | exact Hhi | exact (proj1 (forallb_forall _ _) H o Ho)].
Qed.

Lemma obj_range_ext : ltac2:(tb__ "0|0|
S5S4S4S0S34S34S7S7A2S7A2S3fR1A1S3fR2A1A3S0S34S3bS3bA2SeR4R2A2SeR4R3A2A3F_;Fo';Fo;Fr;").
Proof. intros r [b lo hi c d] [b' lo' hi' c' d'] H. unfold obj_ext in H. cbn in H. injection H as -> -> ->. reflexivity. Qed.
Lemma Forall_disjoint_ext : ltac2:(tb__ "0|2|
S5S2bS4A1M0G0S34S3bS3bA2S0S2bS34S34S7S7A2S7A2M1A1S49S4G1S3fR2A4S49S4G1S3fR3A4A3S48S4S4S12SeR6R1A2R3A2Lo;R4A3S48S4S4S12SeR7R1A2R4A2Lo;R4A3F_;F_;Frg;Fobjs';Fobjs;Fr;").
Proof.
  intros r objs. induction objs as [|o t IH]; intros [|o' t'] rg Hm H; cbn in Hm; try discriminate; [constructor|].
  inversion H; subst. constructor; [rewrite (obj_range_ext r o o') by congruence; assumption | apply IH; [congruence | assumption]].
Qed.

Lemma split_last21 : ltac2:(tb__ "0|2|
S2bS4A1M0S4S0S32S2fS4R2A2U15A3S0S2dS4A1S86S4R3U14M1A3S2cS4R2A2A3S0G0R4S37S4S4aS4G1R4A3S30S4R3S33S4A1A3A3A3F_;F_;Fx;Fl;").
Proof.
  intros l x Hl Hnth. rewrite (nth_error_split3 l 20 x Hnth) at 1.
  replace (skipn 21 l) with (@nil sobj); [reflexivity|]. symmetry. apply skipn_all2. lia.
Qed.

Lemma ecall_at_wl : ltac2:(tb__ "0|0|
S0S2dS92A1Sa8S28Zd9ad4A2S2cS92S94A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma iov01_sound : ltac2:(tb__ "0|6|
S3eS32S3bS0S2aS5cR3R2R1A3S2eA3S1S0S7S14S3dR4A1M0Z11A2S9Z42A1A3S1S0S7S14G0ZaA2S9Z2A1A3S1S0S7S14G0ZcA2S9Z1A1A3S1S0S7S14G0ZbA2S1cS93S1dPaA1M1S9R2A1A3A3S1S51N1000R2A2S1S51S52R2Z10A2Z0M2A2S1S0S3bS19G0A1Zd9ad4A3S1S0S2aSfG0A1S31A3S2S4S4S1S0S2dS4A1S86S4S10S3dR5A1A1R4A3S2cS4R1A2A3S1S0S7S20R1A1G1A3S1S88S13S17S9R3A1Z8M3S9G2A1M4A3S16R1A1M5A3S88S13S17S9S52R3G3A2A1G3G4A3G5A3A2A2A2Lob;A2A2A2A2A2A2A2A2A2F_;Fc;Fi;FW2;").
Proof.
  intros W2 i c H. unfold iov01_ok in H.
  destruct (nth_error (ss_objs (ax_S W2)) i) as [ob|] eqn:Eob; [| rewrite !Bool.andb_false_r in H; discriminate].
  apply andb_prop in H as [H Hc]. apply andb_prop in Hc as [Hc Hc2]. apply andb_prop in Hc as [Hb Hc1].
  apply andb_prop in H as [H Hl]. apply andb_prop in H as [H Hpc]. apply andb_prop in H as [H Hc16]. apply andb_prop in H as [H Hc0].
  apply andb_prop in H as [H H11]. apply andb_prop in H as [H H12]. apply andb_prop in H as [H17 H10].
  apply sv_eqb_sound in H17. apply sv_eqb_sound in H10. apply sv_eqb_sound in H12. apply sv_eqb_sound in H11. apply sv_eqb_sound in Hb.
  apply Z.leb_le in Hc0. apply Z.leb_le in Hc16. apply Z.eqb_eq in Hpc. apply Bool.negb_true_iff in Hl.
  apply existsb_cell_eqb in Hc1. apply existsb_cell_eqb in Hc2.
  repeat split; try assumption. exists ob. repeat split; assumption.
Qed.

Section TailB.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Variables pre suf : list Z.
Variable str : list byte.
Let MSGb : list byte := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.MSGb pre suf str.
Let Kwr : nat -> jpredA := ltac2:(tb__ "0|0|
Sa7VJ0;Vpre;Vsuf;Vstr;A4").
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S5S2bS38Q40A1A1S2bS79A1S78VJ0;R4R3R2R1A4S0S2dS7aA1S7cS7dR2A1S95A2S2cS7aS7bS95A1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
S32S47S28Vok;VKwr;R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S32SacS28Vok;VKwr;R1A1A3Fk;").
Variable rho : valuation.
Variable tp : list word.
Hypothesis Hstr : ltac2:(tb__ "0|1|
S0S2bS38Q8A1M0A1S4aG0S2fG0Vstr;A2SbVrho;P3A2A3Vstr;A3").
Variable n : Z.
Hypothesis Hn : ltac2:(tb__ "0|0|
S0S3bVn;S54S2fS38Q8A1Vstr;A2A1A3").
Let a : Z := Z.of_nat (length pre).
Let b : Z := Z.of_nat (length suf).
Let lenB : Z := a + n.
Hypothesis HlenB : lenB <= 80.
Hypothesis Hpre1 : (1 <= length pre)%nat.
Hypothesis Hb : b <= 80.
Let Kf : nat -> jpredA := ltac2:(tb__ "0|0|
Sa6VJ0;Vpre;Vsuf;Vstr;Vrho;Vtp;A6").
Let bs1 : list byte := ltac2:(tb__ "0|2|
S37S38Q8M0A1M1S49S3bG1S3aG0A1Vpre;A4Vstr;A3").
Let bs2 : list byte := map (Z_to_bv 8) suf.

Lemma HM : ltac2:(tb__ "0|1|
S0S2bS38Q8A1M0A1VMSGb;S37G0Vbs1;Vbs2;A3A3"). Proof. unfold MSGb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.MSGb, bs1, bs2. rewrite <- app_assoc. reflexivity. Qed.
Lemma bs1_len : ltac2:(tb__ "0|0|
S0S3bS54S2fS38Q8A1Vbs1;A2A1VlenB;A3"). Proof. unfold bs1, lenB, a. rewrite length_app, length_map, Hn. lia. Qed.
Lemma bs2_len : ltac2:(tb__ "0|0|
S0S3bS54S2fS38Q8A1Vbs2;A2A1Vb;A3"). Proof. unfold bs2, b. rewrite length_map. reflexivity. Qed.
Lemma lenB1 : 1 <= lenB. Proof. unfold lenB, a. pose proof Hn. lia. Qed.
Lemma Hbl1 : ltac2:(tb__ "0|3|
S5S0S2bS38Q8A1M0A1M1SbR1P3M2A2SbVrho;G2A2A3S0G1S49S98G0S99R2A1S67Vpre;Vn;S33S3bA1A3A4Vbs1;A3F_;Fr;").
Proof. intros r Hr3. rewrite Hn. unfold bs1. rewrite (blA_val r pre str [] ltac:(rewrite Hr3; exact Hstr)). cbn [map]. rewrite app_nil_r. reflexivity. Qed.

Definition rho_wl (r : valuation) : valuation := ltac2:(tb__ "0|0|
S8aS8aVr;P6Vbs2;A3P5Vbs1;A3").
Definition WLF (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S0S2bS38Q8A1A1M0SbVr;P5A2Vbs1;A3S1S0G0SbVr;P6A2Vbs2;A3S1S0S3bS39Q40M1S15Vr;PdA2A2VlenB;A3S0S3bS39G1S15Vr;PfA2A2Vb;A3A2A2A2").
Definition Jp : jpredA := ltac2:(tb__ "0|0|
S5S2bS38Q40A1A1S2bS79A1S78S1S80R4A1VKf;U0R4R3R2R1A5A2Lmd;Ltr;Lt;Lr;").
Lemma Jp_stable : stableA segs 92 Jp.
Proof.
  intros r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.
Lemma Kw_Jp_Kf : ltac2:(tb__ "0|0|
S32S5S2bS38Q40A1A1S2bS79A1S78S8eS7eVbs1;Vbs2;R5R4R3R2R1A8VKf;R6R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;Fk;").
Proof.
  intros k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLerr.TRk, WLerr.MSG, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.EVS. cbn [firstn map]. rewrite <- app_assoc. f_equal. f_equal.
  fold MSGb. rewrite HM. reflexivity.
Qed.
Lemma wl_MSG_len : ltac2:(tb__ "0|1|
S0S32S2fS38Q8A1M0S8fVbs1;Vbs2;A2A2S2fG0VMSGb;A2A3").
Proof. unfold WLerr.MSG. rewrite HM. reflexivity. Qed.
Lemma wl_call : ltac2:(tb__ "0|0|
S5S2bS38Q40A1A1S84S28Vok;S44S28S7eS81R2R1A5S45S28S8eS7eVbs1;Vbs2;S2fS38Q8A1S8fVbs1;Vbs2;A2A2A4P5cR2R1S90A6A4Ftp2;Frho2;").
Proof.
  intros rho2 tp2.
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ Jp); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLerr.wl2_sum ok Jp rho2 tp2 bs1 bs2 A5 A6).
  - rewrite A13, bs1_len. reflexivity.
  - rewrite A15, bs2_len. reflexivity.
  - rewrite wl_MSG_len. unfold MSGb. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.MSGb_len. unfold max_write_total. pose proof HlenB. pose proof Hb. unfold lenB, a, b in *. rewrite Hn in *. lia.
  - apply Jp_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK rho tp k r t tr0 ms md0 msv' (Kw_Jp_Kf k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okP ok J0 pre suf str HokP rho tp k r t tr0 ms md0 x8 (Kw_Jp_Kf k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - unfold bs1. rewrite length_app, length_map. lia.
Qed.
Lemma wl_call_ex : ltac2:(tb__ "0|0|
S5S2bS38Q40A1A1S83S28S44S28S7eS81R2R1A5S45S28S8eS7eVbs1;Vbs2;S2fS38Q8A1S8fVbs1;Vbs2;A2A2A4P5cR2R1S90A6A3Ftp2;Frho2;").
Proof.
  intros rho2 tp2 w Hw. pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLerr.wl2_sum_ex Jp rho2 tp2 bs1 bs2 A5 A6).
  - rewrite A13, bs1_len. reflexivity.
  - rewrite A15, bs2_len. reflexivity.
  - rewrite wl_MSG_len. unfold MSGb. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.MSGb_len. unfold max_write_total. pose proof HlenB. pose proof Hb. unfold lenB, a, b in *. rewrite Hn in *. lia.
  - apply Jp_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - unfold bs1. rewrite length_app, length_map. lia.
  - exact Hw.
Qed.

Local Opaque FUEL_T.
Section PostB.
Variable sufa : Z.
Variables T8 W1 : axst.
Variable o : tailB_out.
Hypothesis Hcert : ltac2:(tb__ "0|0|
S0S2dS59A1S5bVpre;Vsuf;Vn;Vsufa;VT8;VW1;A6S2cS59Vo;A2A3").
Hypothesis HnT8 : ltac2:(tb__ "0|0|
S57S43S6S3dVT8;A1A1A2").

Let W := tb_W o. Let S6 := tb_S6 o. Let Cs := tb_Cs o. Let s := tb_s o. Let R := tb_R o. Let T := tb_T o. Let W2 := tb_W2 o.
Let F0 := tb_F o. Let G1 := tb_G1 o. Let G2 := tb_G2 o. Let G2u := tb_G2u o. Let G3 := tb_G3 o. Let sp := tb_sp o.
Let C : axst := ax_setS W Cs.
Let Tf : axst := ax_add_facts BASEF T.
Let W2a : axst := A_after W2 (SLit 0).
Let F : axst := ax_add_facts facts_fps F0.
Let OR : sobj := O_sufR sufa b.

Lemma cert : ltac2:(tb__ "0|1c|
S2S4S4S2S2bS98A1M0G0S2S4S4S1S1S0S3bS19S3dVW1;A1M1A1Zd9ad4M2A3S57S6S3dVT8;A1A1M3S6G1A1A2A2S1S0S2dS3eA1M4Sb0S50VW1;S4bA2S6eA2S2cS3eVW;A2A3S1S0S2aS87S8S8S89S8S26R1A1S27S3dVW;A1M5A1A3Lf;S4bA3S2eA3S1S57G3S6G5A1M6A2S1S0S2dScA1M7S5dS52N1d0M8VlenB;A2M9G5A2S2cScVS6;A2A3S1S0S2dS4A1MaS86S4S10VS6;A1MbU3McA3S2cS4R3A2A3S1S0S2dG0A1S9aS16R3A1S9G8A1MdZ0MeS56VlenB;A1A4S2cG0R2A2A3S1S0S2aS6fR2S67Vpre;Vn;S33S3bA1A3A2S2eA3S1S0S2aS8bP5MfVS6;A2S31A3S1S0S2aS8bP6M10VS6;A2S31A3S1S0S2aS1eS18R3A1M11A1S2eA3S1S0S2aS1fG11A1S31A3S1S0S7S22R3A1GdA3S1S0S7S21R3A1S9G9A1A3S1S0S2aSa2GfGbA2S2eA3S1S0S2aSa2G10GbA2S2eA3S1S1S0S2aS87S4S5aVsufa;S52Vsufa;Vb;A2M12A2GbA3S2eA3S1S0S2aSafS28Vsufa;Vbs2;A3S2eA3S1S51G12S55Z2Z20A2A2S51GeVsufa;A2A2A2A2S1S0ScVCs;S60Vsufa;Vb;VS6;A3A3S1S0S9bVs;S61VlenB;Vsufa;Vb;VCs;A4A3S1S0S2aS72VW;S6VCs;A1M13A2S2eA3S1S0S2dS2bS4A1M14A1SaaVC;S81Vs;A3S2cG14VR;A2A3S1S0S2aSa9VC;S81Vs;VR;S30S3eS82S33S3eA1A3A5S2eA3S1S0S2aS1aVCs;A1S2eA3S1S0S7S9cVs;PdA2S9VlenB;A1A3S1S0S7S9cVs;PfA2S9Vb;A1A3S1S0S3cG13G6A3S1S0S3cS6Sa0VS6;GcGfA3A1G6A3S1S0S3cS6VS6;A1G6A3S1S0S3eVT;SabVs;S81S82VC;VR;A5A3S1S0S2aSfS3dVTf;A1A1S31A3S1S57S43S6S3dVT;A1A1M15A2S1S0G4S68S4fVTf;G2A3S2cS3eVW2;A2A3S1S1S0S2aS5cVW2;U5N238A3S2eA3S1S57G15S6S3dVW2;A1A1M16A2S0S7S40VW2;A1S9S29A1M17A3A2A2S1S0G4S68S4fVW2a;Sa3A3S2cS3eVF0;A2A3S1S0G7Sa1S3dVF;A1M18S6cA2S2cScVG1;A2A3S1S0GaS86S4S10VG1;A1M19U14A3S2cS4VOR;A2A3S1S0S32S2fS4G19A2U15A3S1S0ScVG2;S70VG1;A1A3S1S0GaS86S4S10VG2;A1U1M1aA3S2cS4R1A2A3S1S0S23S18R1A1S1bGfA1A3S1S0S2bS13A1S16R1A1S33S13A1A3S1S0ScVG2u;Sa4VG2;G1aA2A3S1S0S2aS1aVG2u;A1S2eA3S1S0G7Sa1VG2u;S6dA2S2cScVG3;A2A3S1S0S9bVsp;S71VG3;A1A3S1S0S2aS42Sa5VG3;A1S65Vsp;A3S2eA3S1S0S2aS9fVsp;S43A2S2eA3S1S0S2aS8bGfVG3;A2S31A3S1S0S2aS8bG10VG3;A2S31A3S1S0S7S40VF;A1G17A3S1S57S43S6G18A1M1bA2S1S57G16G1bA2S1S0S3cS6VG1;A1G1bA3S1S0S3cS6VG2u;A1G1bA3S0S3cS6VG3;A1G1bA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lob1;A2Lbl;A2Lo8;A2").
Proof.
  pose proof Hcert as H. unfold tailB_post in H. cbn zeta in H.
  destruct ((ss_pc (ax_S W1) =? 0xd9ad4) && (ss_next (ax_S T8) <=? ss_next (ax_S W1))%positive) eqn:BP; [|discriminate]. cbn [negb] in H.
  apply andb_prop in BP as [BP BnW0]. apply Z.eqb_eq in BP. apply Pos.leb_le in BnW0.
  destruct (apply_axforms (set_facts W1 facts_fps) XW) as [W'|] eqn:EW; [|discriminate].
  destruct (forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S W'))) facts_fps && (ss_next (ax_S T8) <=? ss_next (ax_S W'))%positive) eqn:Bf; [|discriminate]. cbn [negb] in H.
  apply andb_prop in Bf as [Bf BnW]. apply Pos.leb_le in BnW.
  destruct (splitsB (-464 + (Z.of_nat (length pre) + n)) (ax_S W')) as [S6'|] eqn:ES6; [|discriminate].
  destruct (nth_error (ss_objs S6') 3) as [o8|] eqn:Eo8; [|discriminate].
  destruct (cells_bytes (ob_cells o8) (SLit (-464)) 0 (Z.to_nat (Z.of_nat (length pre) + n))) as [bl|] eqn:Ebl; [|discriminate].
  destruct (bexps_eqb bl (blA pre n []) && negb (state_has_rl 5 S6') && negb (state_has_rl 6 S6') && dflt_writable (ob_dflt o8) && negb (is_arr (ob_dflt o8))
            && sv_eqb (ob_lo o8) (SLit (-464)) && sv_eqb (ob_hi o8) (SLit (-464 + (Z.of_nat (length pre) + n))) && exts_rl_free 5 (ss_objs S6') && exts_rl_free 6 (ss_objs S6')
            && forallb (obj_far sufa (sufa + Z.of_nat (length suf))) (ss_objs S6') && rom_bytes_ok segs sufa (map (Z_to_bv 8) suf) && (sufa + Z.of_nat (length suf) <=? 2 ^ 32) && (0 <=? sufa)) eqn:B1; [|discriminate]. cbn [negb] in H.
  destruct (x_ok W' (ss_next (finishB sufa (Z.of_nat (length suf)) S6'))) eqn:Bx; [|discriminate]. cbn [negb] in H.
  destruct (entails_frA (ax_setS W' (finishB sufa (Z.of_nat (length suf)) S6')) WLerrS.Pre_wl2 (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6'))) as [R'|] eqn:ER; [|discriminate].
  destruct (call_checkA (ax_setS W' (finishB sufa (Z.of_nat (length suf)) S6')) WLerrS.Pre_wl2 (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6')) R' [WLerrS.D] && swf (finishB sufa (Z.of_nat (length suf)) S6')
            && sv_eqb (wsub_get (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6')) 13) (SLit (Z.of_nat (length pre) + n)) && sv_eqb (wsub_get (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6')) 15) (SLit (Z.of_nat (length suf)))
            && (ss_next (finishB sufa (Z.of_nat (length suf)) S6') =? ss_next (ax_S W'))%positive && (ss_next (obj_to_list S6' 3 5) =? ss_next (ax_S W'))%positive
            && (ss_next S6' =? ss_next (ax_S W'))%positive) eqn:B2; [|discriminate]. cbn [negb] in H.
  destruct (ss_lenient (ax_S (ax_add_facts BASEF (import_postA (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6')) WLerrS.Pre_wl2 WLerrS.D (ax_setS W' (finishB sufa (Z.of_nat (length suf)) S6')) R'))) || negb (NF <=? ss_next (ax_S (import_postA (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6')) WLerrS.Pre_wl2 WLerrS.D (ax_setS W' (finishB sufa (Z.of_nat (length suf)) S6')) R')))%positive) eqn:B3; [discriminate|].
  destruct (seg FUEL_T (ax_add_facts BASEF (import_postA (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6')) WLerrS.Pre_wl2 WLerrS.D (ax_setS W' (finishB sufa (Z.of_nat (length suf)) S6')) R')) 0xd9ad4) as [W2'|] eqn:EW2; [|discriminate].
  destruct (iov01_ok W2' 5 (-568) && (ss_next (ax_S (import_postA (subB (Z.of_nat (length pre) + n) sufa (Z.of_nat (length suf)) (finishB sufa (Z.of_nat (length suf)) S6')) WLerrS.Pre_wl2 WLerrS.D (ax_setS W' (finishB sufa (Z.of_nat (length suf)) S6')) R')) <=? ss_next (ax_S W2'))%positive && sv_eqb (ax_base W2') (SLit SHB)) eqn:Bi; [|discriminate]. cbn [negb] in H.
  destruct (seg FUEL_T (A_after W2' (SLit 0)) fp_ret) as [F'|] eqn:EF; [|discriminate]. cbn zeta in H.
  destruct (apply_xforms (ax_S (ax_add_facts facts_fps F')) XQ1) as [G1'|] eqn:EG1; [|discriminate].
  destruct (nth_error (ss_objs G1') 20) as [ob2|] eqn:Eob2; [|discriminate].
  destruct (sobj_eqb ob2 (O_sufR sufa (Z.of_nat (length suf))) && (length (ss_objs G1') =? 21)%nat) eqn:B4; [|discriminate]. cbn [negb] in H.
  destruct (nth_error (ss_objs (dropL G1')) 1) as [ob1|] eqn:Eob1; [|discriminate].
  destruct (dflt_eqb (ob_dflt ob1) (DList 5) && (length (ob_cells ob1) =? 0)%nat) eqn:B5; [|discriminate]. cbn [negb] in H.
  destruct (swf (unlist_at (dropL G1') 1)) eqn:B6; [|discriminate]. cbn [negb] in H.
  destruct (apply_xforms (unlist_at (dropL G1') 1) XQ2) as [G3'|] eqn:EG3; [|discriminate].
  destruct (entailsA (axc G3') P_fps (post_sub G3') && wsub_id_below (post_sub G3') NF && negb (state_has_rl 5 G3') && negb (state_has_rl 6 G3')
            && sv_eqb (ax_base (ax_add_facts facts_fps F')) (SLit SHB) && (NF <=? ss_next (ax_S (ax_add_facts facts_fps F')))%positive
            && (ss_next (ax_S W2') <=? ss_next (ax_S (ax_add_facts facts_fps F')))%positive
            && (ss_next G1' =? ss_next (ax_S (ax_add_facts facts_fps F')))%positive && (ss_next (unlist_at (dropL G1') 1) =? ss_next (ax_S (ax_add_facts facts_fps F')))%positive
            && (ss_next G3' =? ss_next (ax_S (ax_add_facts facts_fps F')))%positive) eqn:B7; [|discriminate].
  injection H as Eo. subst o. subst W S6 Cs s R T W2 F0 F G1 G2 G2u G3 sp C Tf W2a OR.
  cbn [tb_W tb_S6 tb_Cs tb_s tb_R tb_T tb_W2 tb_F tb_G1 tb_G2 tb_G2u tb_G3 tb_sp] in *.
  apply andb_prop in B1 as [B1 B1m]. apply andb_prop in B1 as [B1 B1l]. apply andb_prop in B1 as [B1 B1k]. apply andb_prop in B1 as [B1 B1j].
  apply andb_prop in B1 as [B1 B1i]. apply andb_prop in B1 as [B1 B1h].
  apply andb_prop in B1 as [B1 B1g]. apply andb_prop in B1 as [B1 B1f]. apply andb_prop in B1 as [B1 B1e]. apply andb_prop in B1 as [B1 B1d].
  apply andb_prop in B1 as [B1 B1c]. apply andb_prop in B1 as [B1a B1b].
  apply andb_prop in B2 as [B2 B2g]. apply andb_prop in B2 as [B2 B2f]. apply andb_prop in B2 as [B2 B2e]. apply andb_prop in B2 as [B2 B2d].
  apply andb_prop in B2 as [B2 B2c]. apply andb_prop in B2 as [B2a B2b].
  apply Bool.orb_false_iff in B3 as [B3a B3b].
  apply andb_prop in Bi as [Bi Bi3]. apply andb_prop in Bi as [Bi1 Bi2].
  apply andb_prop in B4 as [B4a B4b]. apply andb_prop in B5 as [B5a B5b].
  apply andb_prop in B7 as [B7 B7i]. apply andb_prop in B7 as [B7 B7h]. apply andb_prop in B7 as [B7 B7g]. apply andb_prop in B7 as [B7 B7f2]. apply andb_prop in B7 as [B7 B7f].
  apply andb_prop in B7 as [B7 B7e]. apply andb_prop in B7 as [B7 B7d]. apply andb_prop in B7 as [B7 B7c]. apply andb_prop in B7 as [B7a B7b].
  apply sv_eqb_sound in B1f. apply sv_eqb_sound in B1g. apply sv_eqb_sound in B2c. apply sv_eqb_sound in B2d. apply sv_eqb_sound in B7e. apply sv_eqb_sound in Bi3.
  apply Pos.eqb_eq in B2e. apply Pos.eqb_eq in B2f. apply Pos.eqb_eq in B2g. apply Pos.leb_le in B7f. apply Pos.leb_le in B7f2. apply Pos.eqb_eq in B7g. apply Pos.eqb_eq in B7h. apply Pos.eqb_eq in B7i.
  apply Pos.leb_le in Bi2. apply Z.leb_le in B1l. apply Z.leb_le in B1m.
  apply Nat.eqb_eq in B4b. apply Nat.eqb_eq in B5b. apply sobj_eqb_sound in B4a. subst ob2. apply dflt_eqb_sound in B5a.
  apply Bool.negb_true_iff in B1b. apply Bool.negb_true_iff in B1c. apply Bool.negb_true_iff in B1e. apply Bool.negb_true_iff in B7c. apply Bool.negb_true_iff in B7d.
  apply Bool.negb_false_iff in B3b. apply Pos.leb_le in B3b.
  assert (Hc1 : ob_cells ob1 = []) by (destruct (ob_cells ob1); [reflexivity | cbn in B5b; lia]).
  exists o8, bl, ob1. repeat split; try assumption; try reflexivity.
Qed.

Lemma obj_to_list_ext : ltac2:(tb__ "0|1|
ScS32S3cS0S2bS34S34S7S7A2S7A2M0A1S49S4G0S3fS10Sa0R3R2R1A3A1A4S49S4G0S3fS10R3A1A4A3Fl;Fi;FS;").
Proof.
  intros S i l. unfold obj_to_list. destruct (nth_error (ss_objs S) i) as [ob|] eqn:Hnth; [|reflexivity].
  cbn [ss_objs set_objs].
  transitivity (map obj_ext (firstn i (ss_objs S) ++ ob :: skipn (Datatypes.S i) (ss_objs S))); [rewrite !map_app; reflexivity|].
  rewrite <- (nth_error_split3 _ _ _ Hnth). reflexivity.
Qed.
Lemma facts_rho_wl : ltac2:(tb__ "0|0|
S5S48S8SdR1A1S4bA3S48S8SdS7fR2A1A1S4bA3F_;Fr;").
Proof.
  intros r H. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) H p Hp) as X.
  unfold facts_fps, str_facts in Hp. cbn [app] in Hp.
  repeat (destruct Hp as [<-|Hp]; [exact X|]). destruct Hp.
Qed.
Lemma W_facts : ltac2:(tb__ "0|0|
S46S5S85S44S28R3VW;R2Vtp;R1A6S48S8SdR3A1S4bA3F_;Fw;FrhoW;FJ;").
Proof.
  intros J rhoW w Hsp. destruct cert as (o8 & bl & ob1 & _ & _ & Bf & _ & _).
  pose proof (SPA_facts_hold segs J rhoW W tp w Hsp) as HF.
  apply Forall_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) Bf p Hp) as E. cbn beta in E.
  apply existsb_exists in E as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q. exact (proj1 (Forall_forall _ _) HF _ Hq).
Qed.

Lemma suf_ro : ltac2:(tb__ "0|0|
S3bS1S51Z0R1A2S53R1Vb;A2A2S0S2aS24S28S3aQ40S52Vsufa;R2A2A2A2S2eA3F_;Fk;").
Proof.
  intros k Hk. destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hrom & _ & _) & _).
  exact (proj1 (rom_bytes_ok_sound segs sufa bs2 Hrom k ltac:(rewrite bs2_len; exact Hk))).
Qed.
Lemma S6_disj : ltac2:(tb__ "0|0|
S5S48S8SdR1A1S4bA3S48S4S4S12SeR3R1A2S35S3bS3bVsufa;S52Vsufa;Vb;A2A4A2Lo';S10VS6;A1A3F_;Fr;").
Proof.
  intros r HF. destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hfar & _ & Hhi & Hlo) & _).
  exact (objs_far_disjoint r sufa (sufa + b) (ss_objs S6) (LOWV_of_facts r HF) Hlo Hhi Hfar).
Qed.

Lemma W_rm : ltac2:(tb__ "0|3|
S46S5S85S44S28R3VW;R2Vtp;R1A6S38Q40M0A1S1S51Vsufa;S39G0R1A2M1A2S53G1S52Vsufa;Vb;A2A2A2S0S2dS38Q8A1M2A1S11R5R2A2S36G2A1A3F_;Fx;F_;Fw;FrhoW;FJ;").
Proof.
  intros J rhoW w Hsp. destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & ES6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hhi & Hlo) & _).
  pose proof (W_facts J rhoW w Hsp) as HF.
  destruct (splitsB_SPA J _ W S6 rhoW tp w ES6 Hsp) as [HsmA _]. pose proof (smatchA_smatch segs _ _ _ _ HsmA) as Hsm. cbn [ax_S ax_setS] in Hsm.
  apply (rm_none_ro rhoW S6 tp w sufa (sufa + b) Hsm (S6_disj rhoW HF)); [| exact Hlo | lia].
  intros k Hk. apply suf_ro. lia.
Qed.

Lemma reshape : ltac2:(tb__ "0|1|
S32S5S85S0S2bS38Q8A1A1SbR2P3M0A2SbVrho;G0A2A3S44S28VKf;R4A1VW;R3Vtp;R2A6S44S28VKf;R5A1VC;S7fR4A1Vtp;R3A6F_;F_;Fw;FrhoW;Fk;").
Proof.
  intros k rhoW w Hrl3 Hsp.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & ES6 & Eo8 & Ebl & Bbl & Hrl5 & Hrl6 & Hw8 & Ha8 & Hlo & Hhi & Hx5 & Hx6 & (Hfar & Hrom & Hshi & Hslo) & ECs & _ & Hxok & _ & _ & HswfC & _ & _ & HnC & HnL & Hn6 & _).
  pose proof (W_facts _ rhoW w Hsp) as HFW. pose proof (W_rm _ rhoW w Hsp) as HRM.
  pose proof (splitsB_SPA _ _ W S6 rhoW tp w ES6 Hsp) as H6.
  unfold C. rewrite <- (ax_setS_twice W S6 Cs).
  unfold x_ok in Hxok. apply andb_prop in Hxok as [Hxok Hbase]. apply andb_prop in Hxok as [Hnorl Hxb]. apply sv_eqb_sound in Hbase.
  assert (Hbl : map (beval (rho_set_rl rhoW 6 bs2)) bl = bs1).
  { apply bexps_eqb_sound in Bbl. rewrite Bbl. apply Hbl1. cbn [rl rho_set_rl]. exact Hrl3. }
  pose proof lenB1 as HlenB1.
  eapply (SPA_morphX (Kf k) (Kf k) (ax_setS W S6) Cs rhoW (rho_wl rhoW) tp w).
  - cbn [ax_X ax_base ax_setS]. rewrite Hxb, Hbase. reflexivity.
  - cbn [ax_base ax_setS]. rewrite Hbase. reflexivity.
  - cbn [ax_X ax_setS]. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hnorl r Hr) as X0. unfold xr_norl in X0.
    apply Bool.negb_true_iff in X0. apply Bool.orb_false_iff in X0 as [X0 X4]. apply Bool.orb_false_iff in X0 as [X0 X3]. apply Bool.orb_false_iff in X0 as [X1 X2].
    unfold rho_wl. split; rewrite !SymCall.eval_set_rl by assumption; reflexivity.
  - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [|reflexivity].
    rewrite ECs. unfold finishB. cbn [ss_objs app_obj]. apply outside_all_app_iff. split.
    + unfold rho_wl. apply (outside_all_exts_rl _ 5 bs1 (ss_objs S6)); [apply obj_to_list_ext | exact Hx5 |].
      apply (outside_all_exts_rl rhoW 6 bs2 (ss_objs S6)); [reflexivity | exact Hx6 | exact Hout].
    + unfold outside_all. constructor; [|constructor]. cbn zeta. unfold obj_range, obj_lo_of, obj_hi_of, O_sufR; cbn [ob_base ob_lo ob_hi eval fst snd].
      rewrite !soff_lit_small by lia. rewrite lit_unsigned, Z.mod_small by lia. intros Hin. apply Hrm. apply HRM. lia.
  - intros Hsm. rewrite ECs. unfold finishB.
    pose proof (SymCall.smatch_set_rl segs rhoW 6 bs2 S6 (virt tp w) Hrl6 Hsm) as H5.
    pose proof (smatch_obj_to_list segs _ S6 (virt tp w) 3 5 o8 (-464) (-464 + lenB) bl H5 Eo8 Hlo Hhi
                  ltac:(lia) ltac:(lia) Hw8 Ha8 ltac:(replace (Z.to_nat (-464 + lenB - -464)) with (Z.to_nat lenB) by lia; exact Ebl) Hrl5) as H7.
    rewrite Hbl in H7. change (rho_set_rl (rho_set_rl rhoW 6 bs2) 5 bs1) with (rho_wl rhoW) in H7.
    unfold app_obj, O_sufR.
    apply (smatch_carve_rom segs (rho_wl rhoW) (obj_to_list S6 3 5) (virt tp w) sufa b 6 (ss_next (obj_to_list S6 3 5)) H7).
    + rewrite ECs in HswfC. unfold finishB, app_obj, O_sufR in HswfC. exact HswfC.
    + lia. + unfold b. lia. + lia.
    + unfold rho_wl. cbn [rl rho_set_rl]. exact bs2_len.
    + intros j Hj. unfold rho_wl. cbn [rl rho_set_rl]. apply (rom_bytes_ok_sound segs sufa bs2 Hrom). rewrite bs2_len. exact Hj.
    + apply (Forall_disjoint_ext _ (ss_objs S6)); [apply obj_to_list_ext|]. exact (S6_disj (rho_wl rhoW) (facts_rho_wl rhoW HFW)).
  - intros HK. exact HK.
  - exact H6.
Qed.

Lemma iov01_reads : forall (J : jpredA) rho2 tr ms md,
  Forall (holds rho2) facts_fps ->
  smatch_pendingA segs rho2 tp W2 (tr, mkCfg ms md) ->
  exists b0, read_u64 (ms_read_byte (vms md tp ms)) (eval rho2 (reg_sv (ax_S W2) 11)) = Some b0
        /\ read_u64 (ms_read_byte (vms md tp ms)) (eval rho2 (reg_sv (ax_S W2) 11) + 8)%bv = Some (Z_to_bv 64 0)
        /\ bv_unsigned (eval rho2 (reg_sv (ax_S W2) 11)) + 16 <= TASK_SIZE /\ bv_unsigned b0 <= TASK_SIZE.
Proof.
  intros J rho2 tr ms md HF2 Hsp.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hiov & _ & _) & _).
  destruct (iov01_sound W2 5 (-568) Hiov) as (_ & _ & _ & H11 & Hc0 & Hc16 & _ & _ & ob & Hob & Hbase & Hin1 & Hin2).
  pose proof (LOWV_of_facts rho2 HF2) as (L1 & L2 & _ & L4 & L5 & L6). pose proof (urange (rw rho2 10)) as R10.
  assert (Hlen : (5 < length (ss_objs (ax_S W2)))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hob; discriminate).
  pose proof (objsA_hold segs rho2 tp W2 tr ms md 5 Hsp Hlen) as Ho. unfold obA in Ho. rewrite (nth_error_nth _ _ _ Hob) in Ho.
  assert (Ua : bv_unsigned (eval rho2 (reg_sv (ax_S W2) 11)) = bv_unsigned (rw rho2 10) + -568).
  { rewrite H11. apply (U_addc rho2 (SVar 10) (-568) (bv_unsigned (rw rho2 10)) eq_refl); lia. }
  exists (eval rho2 (SLit 0)). split; [|split; [|split]].
  - apply (cell_read_u64 segs rho2 (vms md tp ms) ob (SLit (-568)) (SLit 0) _ Ho Hin1). rewrite Hbase, Ua. change (eval rho2 (SVar 10)) with (rw rho2 10). rewrite soff_lit_small by lia. lia.
  - change (Z_to_bv 64 0) with (eval rho2 (SLit 0)).
    apply (cell_read_u64 segs rho2 (vms md tp ms) ob (SLit (-568 + 8)) (SLit 0) _ Ho Hin2). rewrite Hbase. change (eval rho2 (SVar 10)) with (rw rho2 10).
    rewrite soff_lit_small by lia. rewrite (U_bvadd _ _ _ 8 Ua u8) by lia. lia.
  - rewrite Ua. unfold TASK_SIZE. lia.
  - cbn [eval]. rewrite Z_to_bv_small by (rewrite two64; lia). unfold TASK_SIZE. lia.
Qed.

Definition rho_fin (rho3 : valuation) (ms : machine_state) (md : Model) : valuation := ltac2:(tb__ "0|2|
S9eS8aS8aS9dVrho3;S30S4VOR;S33S4A1A3SaeVmd;Vtp;Vms;A3A3P5M0SbVrho;G0A2A3P6M1SbVrho;G1A2A3Vsp;A2").

Lemma cleanup : ltac2:(tb__ "0|1|
S32S5S2bS79A1M0S91S78S48S8SdR4A1S4bA3S44S28VKf;R6A1VF0;R5Vtp;S35G0S8cR4S8dR3R2A2A4A6S44S28VKf;R7A1S65S96R6R4R3A3Vtp;S35G0S8cR5S8dR4R3A2A4A6F_;F_;Fmd;Fms;Ftr;Frho3;Fk;").
Proof.
  intros k rho3 tr ms md HF3 Hsp0.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                    & _ & EG1 & HG1b2 & HG1len & EG2 & Eob1 & Hob1d & Hob1c & EG2u & HswfG2u & EG3 & Esp & Hent & Hspid & Hg5 & Hg6 & HbF & HnF & _ & HnG1 & HnG2u & HnG3).
  assert (EnF : ss_next (ax_S F) = ss_next (ax_S F0)) by (unfold F, ax_add_facts, add_facts, ax_setS; destruct F0 as [S0 X0 b0]; reflexivity).
  assert (Hsp : SPA segs (Kf k) F rho3 tp (tr, mkCfg ms md)).
  { destruct Hsp0 as [Hsm0 HK0]. split; [|exact HK0]. unfold F. apply smatchA_add_facts; [exact Hsm0 | exact HF3 | apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.fb_facts_le; rewrite <- EnF; exact HnF]. }
  pose proof (SPA_x_sub segs (Kf k) rho3 F [] tp _ ltac:(intros r Hr; destruct Hr) Hsp) as H0.
  assert (E0 : ax_setX F [] = axc (ax_S F)) by (unfold ax_setX, axc; rewrite HbF; reflexivity). rewrite E0 in H0.
  assert (H1 : SPA segs (Kf k) (axc G1) rho3 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc (ax_S F)) G1 rho3 rho3 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H0].
    intros Hsm. exact (smatch_xforms segs XQ1 rho3 (ax_S F) G1 _ EG1 Hsm). }
  pose proof (SPA_unobj segs (Kf k) rho3 (axc G1) (firstn 20 (ss_objs G1)) [OR] tp tr ms md
                (split_last21 _ _ HG1len HG1b2) H1 ltac:(intros HK; exact HK)) as H2.
  cbn zeta in H2. cbn [ax_S axc] in H2.
  assert (EG2' : set_objs G1 (firstn 20 (ss_objs G1)) = G2) by (rewrite EG2; unfold dropL; rewrite HG1len; reflexivity).
  rewrite EG2' in H2.
  set (rho4 := rho_absorb rho3 [OR] (vms md tp ms)) in H2.
  change (ax_setS (axc G1) G2) with (axc G2) in H2.
  assert (H2u : SPA segs (Kf k) (axc G2u) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc G2) G2u rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H2].
    intros Hsm. rewrite EG2u. eapply (smatch_unlist_at rho4 G2 1 ob1 5 _ Eob1 Hob1d Hob1c); [rewrite <- EG2u; exact HswfG2u | exact Hsm]. }
  assert (H3 : SPA segs (Kf k) (axc G3) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc G2u) G3 rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H2u].
    intros Hsm. exact (smatch_xforms segs XQ2 rho4 G2u G3 _ EG3 Hsm). }
  set (rho5 := rho_set_rl (rho_set_rl rho4 5 (rl rho 5)) 6 (rl rho 6)).
  assert (H4 : SPA segs (Kf k) (axc G3) rho5 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc G3) G3 rho4 rho5 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H3].
    intros Hsm. unfold rho5. apply SymCall.smatch_set_rl; [exact Hg6|]. apply SymCall.smatch_set_rl; [exact Hg5|]. exact Hsm. }
  unfold rho_fin. fold rho4. fold rho5. destruct H4 as [Hsm4 HK4]. split; [| exact HK4].
  rewrite Esp. eapply smatchA_entails; [rewrite <- Esp; exact Hent | exact Hsm4].
Qed.

Lemma rho_fin_agree : ltac2:(tb__ "0|6|
S5S2bS79A1M0S91S78S3cS58R1S43A2S0S38Q40M1A1M2S15R6R2A2S15Vrho;R2A2A3F_;Fi;S3cS3S0S3cR1P5A3A1S3S0S3cR2P6A3A1S0S2bS38Q8A1M3A1SbR8R3A2SbVrho;R3A2A3F_;F_;Fl;G2S0S2dG3A1M4S11R7R1A2S11Vrho;R1A2A3Fx;G2S1S51Vsufa;S39G1R1A2M5A2S53G5S52Vsufa;Vb;A2A2A2S0G4S11Vrho;R2A2S36G3A1A3F_;Fx;S25S28R8S3dVF0;A1SadVtp;S35G0S8cR7S8dR6R5A2A4A2A4SaS43Vrho;S96R9R7R6A3A3F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho3;").
Proof.
  intros rho3 tr ms md Hrw Hrl Hrm HRM Hsm3.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hshi & Hslo) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspid & _).
  pose proof bs2_len as Hb0.
  unfold rho_fin. split; [|split].
  - intros i Hi. cbn [rw rho_sub rho_set_rl rho_absorb]. rewrite (wsub_get_id sp NF i Hspid Hi). cbn. symmetry. apply Hrw. exact Hi.
  - intros l. cbn [rl rho_sub rho_set_rl rho_absorb].
    destruct (Pos.eqb_spec l 6) as [->|N6]; [reflexivity|]. destruct (Pos.eqb_spec l 5) as [->|N5]; [reflexivity|].
    symmetry. apply Hrl; assumption.
  - intros x. cbn [rm rho_sub rho_set_rl rho_absorb].
    destruct (in_ranges_dec rho3 [OR] x) as [Hin|Hnin]; [| symmetry; apply Hrm].
    destruct Hin as (ob & [<-|[]] & Hr). unfold obj_range, obj_lo_of, obj_hi_of, OR, O_sufR in Hr. cbn [ob_base ob_lo ob_hi eval fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. rewrite Z_to_bv_small in Hr by (rewrite two64; lia).
    rewrite (HRM x ltac:(lia)). symmetry. apply (vms_none_ro rho3 (ax_S F0) tp tr ms md x Hsm3).
    replace x with (Z_to_bv 64 (sufa + (bv_unsigned x - sufa))) by (apply bv_eq; rewrite Z_to_bv_small; [lia | rewrite two64; lia]).
    apply suf_ro. lia.
Qed.

Lemma Tf_next : ltac2:(tb__ "0|0|
S0S3cS6S3dVTf;A1A1S6S3dVT;A1A1A3").
Proof. unfold Tf, ax_add_facts, add_facts. destruct T as [ST XT bT]. reflexivity. Qed.
Lemma W2a_shape : ltac2:(tb__ "0|2|
S1S0S3cS6S3dVW2a;A1M0A1S6S3dVW2;A1M1A1A3S0S2aSfG0A1SfG1A1A3A2").
Proof. unfold W2a, A_after, ax_setS, S_after. destruct W2 as [S2 X2 b2]. split; reflexivity. Qed.
Lemma facts_agree : ltac2:(tb__ "0|1|
S3cS5S5S57S43R3A2SaR4R3R2A3S48S8SdR4A1S4bA3M0G0F_;F_;F_;Fr';Fr;Fm;").
Proof.
  intros m r r' Hm Hag HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree m r r' p Hag ltac:(apply (sprop_below_mono NF); [exact Hm | exact (proj1 (forallb_forall _ _) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.fb_facts p Hp)]))).
  exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Lemma after_call : ltac2:(tb__ "0|4|
S5S5SaS43Vrho;R2A3S48S8SdR3A1S4bA3S38Q40M0A1S1S51Vsufa;S39G0R1A2M1A2S53G1S52Vsufa;Vb;A2A2A2S0S2dS38Q8A1M2A1S11R6R2A2S36G2A1A3F_;Fx;SaS6S3dVC;A1A1S7fR5A1R4A3S84S28Vok;S44S28VKf;S2fG2VMSGb;A2M3A1VT;R5Vtp;A5S45S28VKwr;G3A1S43Vrho;Vtp;S64A6A4F_;F_;F_;F_;Frho';FrhoW;").
Proof.
  intros rhoW rho' HagW HF1 HRM Hag'.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & HnW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnC & _ & _
                    & ET & HlTf & HnT & EW2 & (Hiov & HnTW2 & HbW2) & EF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnF & HnW2F & _).
  destruct (seg_run _ _ _ _ EW2) as [HrunW2 HpcW2']. destruct (seg_run _ _ _ _ EF) as [HrunF HpcF].
  destruct (iov01_sound W2 5 (-568) Hiov) as (H17 & H10 & H12 & H11 & _ & _ & HpcW2 & HlW2 & _).
  destruct W2a_shape as [HnW2a HlW2a].
  assert (HF' : Forall (holds rho') facts_fps).
  { apply (facts_agree (ss_next (ax_S C)) (rho_wl rhoW) rho'); [unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (Pos.le_trans _ _ _ HnT8 HnW) | exact Hag' | exact (facts_rho_wl rhoW HF1)]. }
  eapply triple_conseq with (P := SPA segs (Kf (length MSGb)) Tf rho' tp); [ | intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [|exact HJ]. unfold Tf. apply smatchA_add_facts; [exact Hsm | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.basef_holds _ HF') | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.fb_basef_le _ HnT)]. }
  eapply (runA_tr segs ok FUEL_T CUTS_FPS Tf _ (Kf (length MSGb)) rho' tp);
    [exact HrunW2 | exact HlTf | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0) |].
  intros L2 rho2 [<-|[]] Hag2. cbn [la_state]. rewrite Tf_next in Hag2.
  assert (HF2 : Forall (holds rho2) facts_fps) by (exact (facts_agree _ rho' rho2 HnT Hag2 HF')).
  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_writev01A segs ok (Kf (length MSGb)) W2 rho2 tp 2);
      [apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okP ok J0 pre suf str HokP) | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0)
      | rewrite HpcW2; exact ecall_at_wl | exact H17 | exact H10 | exact H12 | lia
      | intros r t tr0 md0 [_ (tr00 & HJ & _)]; exact (Hfd2 _ _ _ _ HJ)
      | intros tr ms md Hsp HJ; exact (iov01_reads (Kf (length MSGb)) rho2 tr ms md HF2 Hsp)]. }
  fold W2a.
  eapply (runA_tr segs ok FUEL_T CUTS_FPS W2a _ (Kf (length MSGb)) rho2 tp);
    [exact HrunF | rewrite HlW2a; exact HlW2 | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0) |].
  intros L3 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnW2a in Hag3.
  intros m Hg w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]].
  assert (HF3 : Forall (holds rho3) facts_fps) by (exact (facts_agree _ rho2 rho3 (Pos.le_trans _ _ _ HnT HnTW2) Hag3 HF2)).
  pose proof (cleanup (length MSGb) rho3 tr3 ms3 md3 HF3 (conj Hsm3 HK3)) as [HsmP HKP].
  assert (HagF : agree_below NF rho (rho_fin rho3 ms3 md3)).
  { destruct HagW as (AW & LW & MW). destruct Hag' as (A' & L' & M'). destruct Hag2 as (A2 & L2' & M2). destruct Hag3 as (A3 & L3' & M3).
    unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'.
    apply (rho_fin_agree rho3 tr3 ms3 md3).
    - intros i Hi. rewrite <- (A3 i) by (unfold NF in *; lia). rewrite <- (A2 i) by (unfold NF in *; lia). rewrite <- (A' i) by (unfold NF in *; lia).
      cbn [rw rho_wl rho_set_rl]. rewrite <- (AW i Hi). reflexivity.
    - intros l N5 N6. rewrite <- (L3' l), <- (L2' l), <- (L' l). cbn [rl rho_wl rho_set_rl].
      destruct (Pos.eqb_spec l 5) as [->|_]; [congruence|]. destruct (Pos.eqb_spec l 6) as [->|_]; [congruence|].
      rewrite <- (LW l). reflexivity.
    - intros x. rewrite <- (M3 x), <- (M2 x), <- (M' x). cbn [rm rho_wl rho_set_rl]. rewrite <- (MW x). reflexivity.
    - intros x Hx. rewrite (MW x). exact (HRM x Hx).
    - exact (smatchA_smatch segs _ _ _ _ Hsm3). }
  apply Hg.
  exists (mkLeafA P_fps RsCut), (rho_fin rho3 ms3 md3). split; [left; reflexivity|]. split; [exact HagF|].
  split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
  exists tr0. split; [|reflexivity].
  eapply Hst0; [exact HagF | apply mat_equiv_refl | exact HJ0].
Qed.

Lemma after_call_ex : ltac2:(tb__ "0|4|
S5S5SaS43Vrho;R2A3S48S8SdR3A1S4bA3S38Q40M0A1S1S51Vsufa;S39G0R1A2M1A2S53G1S52Vsufa;Vb;A2A2A2S0S2dS38Q8A1M2A1S11R6R2A2S36G2A1A3F_;Fx;SaS6S3dVC;A1A1S7fR5A1R4A3S83S28S44S28VKf;S2fG2VMSGb;A2M3A1VT;R5Vtp;A5S45S28VKwr;G3A1S43Vrho;Vtp;S64A6A3F_;F_;F_;F_;Frho';FrhoW;").
Proof.
  intros rhoW rho' HagW HF1 HRM Hag'.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & HnW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnC & _ & _
                    & ET & HlTf & HnT & EW2 & (Hiov & HnTW2 & HbW2) & EF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnF & HnW2F & _).
  destruct (seg_run _ _ _ _ EW2) as [HrunW2 HpcW2']. destruct (seg_run _ _ _ _ EF) as [HrunF HpcF].
  destruct (iov01_sound W2 5 (-568) Hiov) as (H17 & H10 & H12 & H11 & _ & _ & HpcW2 & HlW2 & _).
  destruct W2a_shape as [HnW2a HlW2a].
  assert (HF' : Forall (holds rho') facts_fps).
  { apply (facts_agree (ss_next (ax_S C)) (rho_wl rhoW) rho'); [unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (Pos.le_trans _ _ _ HnT8 HnW) | exact Hag' | exact (facts_rho_wl rhoW HF1)]. }
  eapply etriple_conseq with (P := SPA segs (Kf (length MSGb)) Tf rho' tp); [ | intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [|exact HJ]. unfold Tf. apply smatchA_add_facts; [exact Hsm | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.basef_holds _ HF') | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.fb_basef_le _ HnT)]. }
  eapply (erunA_tr segs FUEL_T CUTS_FPS Tf _ (Kf (length MSGb)) rho' tp); [exact HrunW2 | exact HlTf | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0) |].
  intros L2 rho2 [<-|[]] Hag2. cbn [la_state]. rewrite Tf_next in Hag2.
  assert (HF2 : Forall (holds rho2) facts_fps) by (exact (facts_agree _ rho' rho2 HnT Hag2 HF')).
  eapply etriple_seq.
  { apply (etriple_writev01A segs (Kf (length MSGb)) W2 rho2 tp 2);
      [apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0)
      | rewrite HpcW2; exact ecall_at_wl | exact H17 | exact H10 | exact H12 | lia
      | intros r t tr0 md0 [_ (tr00 & HJ & _)]; exact (Hfd2 _ _ _ _ HJ)
      | intros tr ms md Hsp HJ; exact (iov01_reads (Kf (length MSGb)) rho2 tr ms md HF2 Hsp)]. }
  fold W2a.
  eapply (erunA_tr segs FUEL_T CUTS_FPS W2a _ (Kf (length MSGb)) rho2 tp); [exact HrunF | rewrite HlW2a; exact HlW2 | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0) |].
  intros L3 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnW2a in Hag3.
  intros w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]]. exists (tr3, mkCfg ms3 md3). split; [apply wsteps_refl|].
  assert (HF3 : Forall (holds rho3) facts_fps) by (exact (facts_agree _ rho2 rho3 (Pos.le_trans _ _ _ HnT HnTW2) Hag3 HF2)).
  pose proof (cleanup (length MSGb) rho3 tr3 ms3 md3 HF3 (conj Hsm3 HK3)) as [HsmP HKP].
  assert (HagF : agree_below NF rho (rho_fin rho3 ms3 md3)).
  { destruct HagW as (AW & LW & MW). destruct Hag' as (A' & L' & M'). destruct Hag2 as (A2 & L2' & M2). destruct Hag3 as (A3 & L3' & M3).
    unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'.
    apply (rho_fin_agree rho3 tr3 ms3 md3).
    - intros i Hi. rewrite <- (A3 i) by (unfold NF in *; lia). rewrite <- (A2 i) by (unfold NF in *; lia). rewrite <- (A' i) by (unfold NF in *; lia).
      cbn [rw rho_wl rho_set_rl]. rewrite <- (AW i Hi). reflexivity.
    - intros l N5 N6. rewrite <- (L3' l), <- (L2' l), <- (L' l). cbn [rl rho_wl rho_set_rl].
      destruct (Pos.eqb_spec l 5) as [->|_]; [congruence|]. destruct (Pos.eqb_spec l 6) as [->|_]; [congruence|].
      rewrite <- (LW l). reflexivity.
    - intros x. rewrite <- (M3 x), <- (M2 x), <- (M' x). cbn [rm rho_wl rho_set_rl]. rewrite <- (MW x). reflexivity.
    - intros x Hx. rewrite (MW x). exact (HRM x Hx).
    - exact (smatchA_smatch segs _ _ _ _ Hsm3). }
  exists (mkLeafA P_fps RsCut), (rho_fin rho3 ms3 md3). split; [left; reflexivity|]. split; [exact HagF|].
  split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
  exists tr0. split; [|reflexivity].
  eapply Hst0; [exact HagF | apply mat_equiv_refl | exact HJ0].
Qed.

Theorem post_soundB : ltac2:(tb__ "0|0|
S5SaS43Vrho;R1A3S48S8SdR2A1S4bA3S84S28Vok;S44S28VKf;U0A1VW1;R3Vtp;A5S45S28VKwr;S2fS38Q8A1VMSGb;A2A1S43Vrho;Vtp;S64A6A4F_;F_;FrhoW;").
Proof.
  intros rhoW HagW HFW.
  destruct cert as (o8 & bl & ob1 & EW0 & EW & _ & HnW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Es & _ & Hefr & Hchk & _ & S13 & S15 & HnC & _ & _ & ET & _).
  destruct EW0 as (HpcW & HnW0).
  assert (HbW0 : forallb (sprop_below (ss_next (ax_S W1))) facts_fps = true) by (apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.fb_facts_le; exact (Pos.le_trans _ _ _ HnT8 HnW0)).
  eapply triple_conseq with (P := SPA segs (Kf 0) W rhoW tp); [intros w Hw; exact (SPA_axforms segs _ XW rhoW (set_facts W1 facts_fps) W tp w EW (SPA_set_facts (Kf 0) W1 facts_fps rhoW tp w HFW HbW0 Hw)) | intros w Hw; exact Hw |].
  apply (triple_pre ok _ (Forall (holds rhoW) facts_fps /\ (forall x : word, sufa <= bv_unsigned x < sufa + b -> rm rhoW x = None)));
    [intros w Hw; exact (conj (W_facts _ rhoW w Hw) (W_rm _ rhoW w Hw)) | intros [HF1 HRM]].
  assert (Hrl3 : rl rhoW 3 = rl rho 3) by (destruct HagW as (_ & LW & _); rewrite <- (LW 3%positive); reflexivity).
  eapply triple_conseq with (P := SPA segs (Kf 0) C (rho_wl rhoW) tp); [intros w Hw; exact (reshape 0 rhoW w Hrl3 Hw) | intros w Hw; exact Hw |].
  apply (call_soundA segs ok (Kf 0) Jp (WLerr.Kw Jp bs1 bs2 (length (WLerr.MSG bs1 bs2))) (Kf (length MSGb)) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rhoW) tp Hefr Hchk).
  - intros rho2 tp2. apply wl_call.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval rl rho_wl rho_set_rl].
    rewrite !lit_unsigned. pose proof lenB1. pose proof bs2_len. rewrite !Z.mod_small by (unfold b in *; lia). repeat split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite wl_MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite <- ET.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf (length MSGb))); [intros t md0 (HJ & _ & _); exact HJ|].
    exact (after_call rhoW rho' HagW HF1 HRM Hag').
Qed.

Theorem post_soundB_ex : ltac2:(tb__ "0|0|
S5SaS43Vrho;R1A3S48S8SdR2A1S4bA3S83S28S44S28VKf;U0A1VW1;R3Vtp;A5S45S28VKwr;S2fS38Q8A1VMSGb;A2A1S43Vrho;Vtp;S64A6A3F_;F_;FrhoW;").
Proof.
  intros rhoW HagW HFW.
  destruct cert as (o8 & bl & ob1 & EW0 & EW & _ & HnW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Es & _ & Hefr & Hchk & _ & S13 & S15 & HnC & _ & _ & ET & _).
  destruct EW0 as (HpcW & HnW0).
  assert (HbW0 : forallb (sprop_below (ss_next (ax_S W1))) facts_fps = true) by (apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.fb_facts_le; exact (Pos.le_trans _ _ _ HnT8 HnW0)).
  eapply etriple_conseq with (P := SPA segs (Kf 0) W rhoW tp); [intros w Hw; exact (SPA_axforms segs _ XW rhoW (set_facts W1 facts_fps) W tp w EW (SPA_set_facts (Kf 0) W1 facts_fps rhoW tp w HFW HbW0 Hw)) | intros w Hw; exact Hw |].
  apply (etriple_pre _ (Forall (holds rhoW) facts_fps /\ (forall x : word, sufa <= bv_unsigned x < sufa + b -> rm rhoW x = None)));
    [intros w Hw; exact (conj (W_facts _ rhoW w Hw) (W_rm _ rhoW w Hw)) | intros [HF1 HRM]].
  assert (Hrl3 : rl rhoW 3 = rl rho 3) by (destruct HagW as (_ & LW & _); rewrite <- (LW 3%positive); reflexivity).
  eapply etriple_conseq with (P := SPA segs (Kf 0) C (rho_wl rhoW) tp); [intros w Hw; exact (reshape 0 rhoW w Hrl3 Hw) | intros w Hw; exact Hw |].
  apply (call_completeA segs (Kf 0) Jp (WLerr.Kw Jp bs1 bs2 (length (WLerr.MSG bs1 bs2))) (Kf (length MSGb)) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rhoW) tp Hefr Hchk).
  - intros rho2 tp2. apply wl_call_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval rl rho_wl rho_set_rl].
    rewrite !lit_unsigned. pose proof lenB1. pose proof bs2_len. rewrite !Z.mod_small by (unfold b in *; lia). repeat split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite wl_MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite <- ET.
    intros w0 [Hsm0 [Et HK0]]. subst tpL.
    apply (after_call_ex rhoW rho' HagW HF1 HRM Hag'). split; [exact Hsm0 | split; [reflexivity | exact HK0]].
Qed.
End PostB.

Section InstB.
Variables r sufa : Z.
Variable cls : list sprop.
Variable T7 : axst.
Variable o : tailB_out.
Hypothesis Hcert : ltac2:(tb__ "0|0|
S0S2dS59A1S62Vpre;Vsuf;Vn;Vr;Vsufa;Vcls;VT7;A7S2cS59Vo;A2A3").
Let T8 : axst := ltac2:(tb__ "0|0|
S66Va;Vn;Vr;Vcls;VT7;A5").
Hypothesis HlT8 : ltac2:(tb__ "0|0|
S0S2aSfS3dVT8;A1A1S31A3").
Hypothesis HnT8 : ltac2:(tb__ "0|0|
S57S43S6S3dVT8;A1A1A2").

Lemma certB : ltac2:(tb__ "0|3|
S2S3eS3eS1S0S2aS4dS5fVn;Vr;VT7;A3M0S3dVT8;A1M1A2S2eA3S1S0S2aS4dS30S2bS8A1M2S4bS33G2A1A3G1A2S2eA3S1S0S2dS3eA1S4eG0VT8;A2S2cS3eR1A2A3S0S2dS59A1S5bVpre;Vsuf;Vn;Vsufa;VT8;R1A6S2cS59Vo;A2A3A2A2A2LW1;A2").
Proof.
  pose proof Hcert as H. unfold tailB in H. cbn zeta in H. fold a in H. fold T8 in H.
  destruct (fs_ok (FSB n r T7) (ax_S T8) && fs_ok [facts_fps] (ax_S T8)) eqn:BL; [|discriminate]. cbn [negb] in H. apply andb_prop in BL as [BL BL2].
  destruct (runp (FSB n r T7) T8) as [W1|] eqn:EW1; [|discriminate].
  exists W1. repeat split; try assumption.
Qed.

Theorem tailB_sound : ltac2:(tb__ "0|0|
S5SaS43Vrho;R1A3S84S28Vok;S44S28VKf;U0A1VT8;R2Vtp;A5S45S28VKwr;S2fS38Q8A1VMSGb;A2A1S43Vrho;Vtp;S64A6A4F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certB as (W1 & HLok & HLf & EW1 & HP).
  apply (triple_pre ok _ (FsHold rho7 (FSB n r T7) /\ FsBelow (ss_next (ax_S T8)) (FSB n r T7) = true)); [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w HLok Hw) | intros [HF0 HLb]].
  apply (triple_pre ok _ (FsHold rho7 [facts_fps] /\ FsBelow (ss_next (ax_S T8)) [facts_fps] = true)); [intros w Hw; exact (fs_ok_sound _ [facts_fps] T8 rho7 tp w HLf Hw) | intros [HFf0 HLfb]].
  eapply (runp_tr ok (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) (FSB n r T7) T8 W1 rho7 tp);
    [exact EW1 | exact HlT8 | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | exact HF0 | exact HLb |].
  intros rhoW HagW.
  assert (HFW : Forall (holds rhoW) facts_fps) by (exact (Forall_inv (FsHold_agree _ rho7 rhoW [facts_fps] HagW HLfb HFf0))).
  apply (post_soundB sufa T8 W1 o HP HnT8 rhoW); [|exact HFW].
  eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagW)].
Qed.

Theorem tailB_sound_ex : ltac2:(tb__ "0|0|
S5SaS43Vrho;R1A3S83S28S44S28VKf;U0A1VT8;R2Vtp;A5S45S28VKwr;S2fS38Q8A1VMSGb;A2A1S43Vrho;Vtp;S64A6A3F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certB as (W1 & HLok & HLf & EW1 & HP).
  apply (etriple_pre _ (FsHold rho7 (FSB n r T7) /\ FsBelow (ss_next (ax_S T8)) (FSB n r T7) = true)); [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w HLok Hw) | intros [HF0 HLb]].
  apply (etriple_pre _ (FsHold rho7 [facts_fps] /\ FsBelow (ss_next (ax_S T8)) [facts_fps] = true)); [intros w Hw; exact (fs_ok_sound _ [facts_fps] T8 rho7 tp w HLf Hw) | intros [HFf0 HLfb]].
  eapply (runp_etr (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) (FSB n r T7) T8 W1 rho7 tp); [exact EW1 | exact HlT8 | exact HF0 | exact HLb |].
  intros rhoW HagW.
  assert (HFW : Forall (holds rhoW) facts_fps) by (exact (Forall_inv (FsHold_agree _ rho7 rhoW [facts_fps] HagW HLfb HFf0))).
  apply (post_soundB_ex sufa T8 W1 o HP HnT8 rhoW); [|exact HFW].
  eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagW)].
Qed.
End InstB.

Section InstBR.
Variables r sufa : Z.
Variable cls : list sprop.
Variable T7 : axst.
Variable o : tailBR_out.
Hypothesis Hcert : ltac2:(tb__ "0|0|
S0S2dS5eA1S63Vpre;Vsuf;Vn;Vr;Vsufa;Vcls;VT7;A7S2cS5eVo;A2A3").
Let T8 : axst := ltac2:(tb__ "0|0|
S66Va;Vn;Vr;Vcls;VT7;A5").
Hypothesis HlT8 : ltac2:(tb__ "0|0|
S0S2aSfS3dVT8;A1A1S31A3").
Hypothesis HnT8 : ltac2:(tb__ "0|0|
S57S43S6S3dVT8;A1A1A2").
Let v : positive := zvar T7.

Lemma certBR : ltac2:(tb__ "0|a|
S2S3eS3eS2S73S73S2S73S73S2S3eS3eS2S59S59S1S0S2aS4dS30S2bS8A1M0S69Vv;Vn;A2M1S30G0S4cS30G0S6aVv;Vn;A2M2S30G0S6bVv;Vn;Vr;A3M3S30G0S4bS33G0A1M4A3A3A3A3A3S3dVT8;A1M5A2S2eA3S1S0S2dS3eA1M6S4eS30G0G1S30G0S4cS30G0S4cS30G0S4cG4A3M7A3A3A3VT8;A2S2cS3eR5A2A3S1S0S2aSfS3dR5A1M8A1S31A3S1S57S6G5A1S6G8A1A2S1S0S2dS73A1M9S75G2S76Va;A1R5A3S2cS73R4A2A3S1S0G9S75G2S77Va;A1S74R4A1A3S2cS73R3A2A3S1S0G6S4eS30G0G2S30G0G3G7A3A3S74R3A1A2S2cS3eR2A2A3S0S2dS59A1S5bVpre;Vsuf;Vn;Vsufa;VT8;R2A6S2cS59R1A2A3A2A2A2A2A2A2A2LoB;A2LW1;A2Lc2;A2Lc1;A2LM4;A2").
Proof.
  pose proof Hcert as H. unfold tailBR in H. cbn zeta in H. fold a in H. fold T8 in H. fold v in H.
  destruct (fs_ok [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] (ax_S T8)) eqn:Hfs; [|discriminate]. cbn [negb] in H.
  destruct (runp [FA1 v n; BASEF; BASEF; BASEF] T8) as [M4|] eqn:EM4; [|discriminate].
  destruct (ss_lenient (ax_S M4) || negb (ss_next (ax_S T8) <=? ss_next (ax_S M4))%positive) eqn:B1; [discriminate|].
  apply Bool.orb_false_iff in B1 as [HlM4 HnM4]. apply Bool.negb_false_iff in HnM4. apply Pos.leb_le in HnM4.
  destruct (rcall (FA5 v n) (sR1 a) M4) as [c1|] eqn:Ec1; [|discriminate].
  destruct (rcall (FA5 v n) (sR2 a) (rc_Tm c1)) as [c2|] eqn:Ec2; [|discriminate].
  destruct (runp [FA5 v n; FA6 v n r; BASEF] (rc_Tm c2)) as [W1|] eqn:EW1; [|discriminate].
  destruct (tailB_post pre suf n sufa T8 W1) as [oB|] eqn:EoB; [|discriminate].
  exists M4, c1, c2, W1, oB. repeat split; assumption.
Qed.

Theorem tailBR_sound : ltac2:(tb__ "0|0|
S5SaS43Vrho;R1A3S84S28Vok;S44S28VKf;U0A1VT8;R2Vtp;A5S45S28VKwr;S2fS38Q8A1VMSGb;A2A1S43Vrho;Vtp;S64A6A4F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certBR as (M4 & c1 & c2 & W1 & oB & Hfs & EM4 & HlM4 & HnM4 & Ec1 & Ec2 & EW1 & HP).
  destruct (rcall_shape _ _ _ _ Ec1) as [HlT1 HnT1]. destruct (rcall_shape _ _ _ _ Ec2) as [HlT2 HnT2].
  apply (triple_pre ok _ (FsHold rho7 [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] /\ FsBelow (ss_next (ax_S T8)) [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] = true));
    [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w Hfs Hw) | intros [HF0 HLb]].
  pose proof (Forall_inv HF0) as H1. pose proof (Forall_inv (Forall_inv_tail HF0)) as HB.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF0))) as H5. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0)))) as H6.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0))))) as HFf.
  unfold FsBelow in HLb. cbn [forallb] in HLb.
  apply andb_prop in HLb as [B1 HLb]. apply andb_prop in HLb as [BB HLb]. apply andb_prop in HLb as [B5 HLb]. apply andb_prop in HLb as [B6 HLb]. apply andb_prop in HLb as [Bf _].
  eapply (runp_tr ok (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) [FA1 v n; BASEF; BASEF; BASEF] T8 M4 rho7 tp);
    [exact EM4 | exact HlT8 | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK) | repeat (constructor; [assumption|]); constructor | unfold FsBelow; cbn [forallb]; rewrite B1, BB; reflexivity |].
  intros rhoM HagM.
  apply (Fps_tailR.rcall_sound ok J0 pre suf str Hst0 HokK rho tp (FA5 v n) (sR1 a) M4 c1 rhoM _ Ec1 HlM4); [exact (Forall_holds_agree _ _ _ _ HagM B5 H5) |].
  intros rhoT HagT.
  assert (HagMT : agree_below (ss_next (ax_S T8)) rho7 rhoT) by (eapply agree_below_trans; [exact HagM | exact (agree_below_le _ _ _ _ HnM4 HagT)]).
  apply (Fps_tailR.rcall_sound ok J0 pre suf str Hst0 HokK rho tp (FA5 v n) (sR2 a) (rc_Tm c1) c2 rhoT _ Ec2 HlT1); [exact (Forall_holds_agree _ _ _ _ HagMT B5 H5) |].
  intros rhoU HagU.
  assert (HnTU : (ss_next (ax_S T8) <= ss_next (ax_S (rc_Tm c2)))%positive) by (exact (Pos.le_trans _ _ _ HnM4 (Pos.le_trans _ _ _ HnT1 HnT2))).
  assert (HagMU : agree_below (ss_next (ax_S T8)) rho7 rhoU) by (eapply agree_below_trans; [exact HagMT | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnM4 HnT1) HagU)]).
  eapply (runp_tr ok (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) [FA5 v n; FA6 v n r; BASEF] (rc_Tm c2) W1 rhoU tp);
    [exact EW1 | exact HlT2 | apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_okK ok J0 pre suf str HokK)
    | constructor; [exact (Forall_holds_agree _ _ _ _ HagMU B5 H5) | constructor; [exact (Forall_holds_agree _ _ _ _ HagMU B6 H6) | constructor; [exact (Forall_holds_agree _ _ _ _ HagMU BB HB) | constructor]]]
    | unfold FsBelow; cbn [forallb]; rewrite (forallb_below_mono _ _ _ HnTU B5), (forallb_below_mono _ _ _ HnTU B6), (forallb_below_mono _ _ _ HnTU BB); reflexivity |].
  intros rhoW HagW.
  assert (HagMW : agree_below (ss_next (ax_S T8)) rho7 rhoW) by (eapply agree_below_trans; [exact HagMU | exact (agree_below_le _ _ _ _ HnTU HagW)]).
  apply (post_soundB sufa T8 W1 oB HP HnT8 rhoW).
  - eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagMW)].
  - exact (Forall_holds_agree _ _ _ _ HagMW Bf HFf).
Qed.

Theorem tailBR_sound_ex : ltac2:(tb__ "0|0|
S5SaS43Vrho;R1A3S83S28S44S28VKf;U0A1VT8;R2Vtp;A5S45S28VKwr;S2fS38Q8A1VMSGb;A2A1S43Vrho;Vtp;S64A6A3F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certBR as (M4 & c1 & c2 & W1 & oB & Hfs & EM4 & HlM4 & HnM4 & Ec1 & Ec2 & EW1 & HP).
  destruct (rcall_shape _ _ _ _ Ec1) as [HlT1 HnT1]. destruct (rcall_shape _ _ _ _ Ec2) as [HlT2 HnT2].
  apply (etriple_pre _ (FsHold rho7 [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] /\ FsBelow (ss_next (ax_S T8)) [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] = true));
    [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w Hfs Hw) | intros [HF0 HLb]].
  pose proof (Forall_inv HF0) as H1. pose proof (Forall_inv (Forall_inv_tail HF0)) as HB.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF0))) as H5. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0)))) as H6.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0))))) as HFf.
  unfold FsBelow in HLb. cbn [forallb] in HLb.
  apply andb_prop in HLb as [B1 HLb]. apply andb_prop in HLb as [BB HLb]. apply andb_prop in HLb as [B5 HLb]. apply andb_prop in HLb as [B6 HLb]. apply andb_prop in HLb as [Bf _].
  eapply (runp_etr (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) [FA1 v n; BASEF; BASEF; BASEF] T8 M4 rho7 tp);
    [exact EM4 | exact HlT8 | repeat (constructor; [assumption|]); constructor | unfold FsBelow; cbn [forallb]; rewrite B1, BB; reflexivity |].
  intros rhoM HagM.
  apply (Fps_tailR.rcall_sound_ex J0 pre suf str Hst0 rho tp (FA5 v n) (sR1 a) M4 c1 rhoM _ Ec1 HlM4); [exact (Forall_holds_agree _ _ _ _ HagM B5 H5) |].
  intros rhoT HagT.
  assert (HagMT : agree_below (ss_next (ax_S T8)) rho7 rhoT) by (eapply agree_below_trans; [exact HagM | exact (agree_below_le _ _ _ _ HnM4 HagT)]).
  apply (Fps_tailR.rcall_sound_ex J0 pre suf str Hst0 rho tp (FA5 v n) (sR2 a) (rc_Tm c1) c2 rhoT _ Ec2 HlT1); [exact (Forall_holds_agree _ _ _ _ HagMT B5 H5) |].
  intros rhoU HagU.
  assert (HnTU : (ss_next (ax_S T8) <= ss_next (ax_S (rc_Tm c2)))%positive) by (exact (Pos.le_trans _ _ _ HnM4 (Pos.le_trans _ _ _ HnT1 HnT2))).
  assert (HagMU : agree_below (ss_next (ax_S T8)) rho7 rhoU) by (eapply agree_below_trans; [exact HagMT | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnM4 HnT1) HagU)]).
  eapply (runp_etr (Kf 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0) [FA5 v n; FA6 v n r; BASEF] (rc_Tm c2) W1 rhoU tp);
    [exact EW1 | exact HlT2
    | constructor; [exact (Forall_holds_agree _ _ _ _ HagMU B5 H5) | constructor; [exact (Forall_holds_agree _ _ _ _ HagMU B6 H6) | constructor; [exact (Forall_holds_agree _ _ _ _ HagMU BB HB) | constructor]]]
    | unfold FsBelow; cbn [forallb]; rewrite (forallb_below_mono _ _ _ HnTU B5), (forallb_below_mono _ _ _ HnTU B6), (forallb_below_mono _ _ _ HnTU BB); reflexivity |].
  intros rhoW HagW.
  assert (HagMW : agree_below (ss_next (ax_S T8)) rho7 rhoW) by (eapply agree_below_trans; [exact HagMU | exact (agree_below_le _ _ _ _ HnTU HagW)]).
  apply (post_soundB_ex sufa T8 W1 oB HP HnT8 rhoW).
  - eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagMW)].
  - exact (Forall_holds_agree _ _ _ _ HagMW Bf HFf).
Qed.
End InstBR.
End TailB.
End Fps_tailB.

(* [comment removed for export] *)
Module FpsC_b1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st"; "T7s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "PRE_C"; "SUF_NL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs"; "SUFA_C"; "tailB_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs.
Import ListNotations.
Open Scope Z_scope.

Lemma okB_1 : ltac2:(tb__ "0|0|
S5S2ScS0S0SaS7S8Z3fR1S9SbS6A7Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S3S0A1A3A3A3A3A3S4A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_b1.

(* [comment removed for export] *)
Module Start8States.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "sym_runA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "list"; "Some"; "option"; "true"; "prod"; "app"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "sobj"; "ss_next"; "ss_pc"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8States"; "E23_of"; "E24_of"; "EG_of"; "S22ok_of"; "S23ok0_of"; "S23ok_of"; "S24ok_of"; "SPIN22_of"; "SPIN23_of"; "SPIN24_of"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0"; "E22_of"; "o13p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.Start8StatesB"; "GPC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "eager_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3"; "null_rw_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8StatesA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.Start8StatesB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition S22ok_of (v : bool) : axst := pick v S22okA S22okB.
Lemma S22ok_eq : ltac2:(tb__ "0|0|
SeS0S6S39S36R1A1Z100000Pa0A3S2bR1A1A3Fv;").
Proof. intros [|]; reflexivity. Qed.
Definition E23_of (v : bool) : axst := pick v E23A E23B.
Lemma run23 : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eS32S33S20S21S1fS1fS1fS22A1A1A1A1A1A1A1ScSaZ7050cScSaZ6bd84SdSaA1A3A3S2bR1A1S12A5S10G0ScS2S3S28R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run23A | exact run23B]. Qed.
Definition SPIN22_of (v : bool) : axst := pick v SPIN22A SPIN22B.
Lemma run22_fail : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eU12cScSaZ6bd84SdSaA1A3S34S36R1A1A1S12A5S10G0ScS2S3S2fR1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run22A_fail | exact run22B_fail]. Qed.
Lemma spin22 : ltac2:(tb__ "0|2|
SeS0S11SfS2A1M0A1S4S1eU2ScSaZ6bd84SdSaA1A3S2fR1A1M1S12A5S10G0ScS2S3G1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact spin22A | exact spin22B]. Qed.
Lemma E23_at : ltac2:(tb__ "0|5|
SeS1S0SaS1cS5S28R1A1M0A1M1A1M2Z7050cA3S1S0SbS1bG1A1Pa0A3S1S0S11S26A1S24S1eG2A2S10S26S27A2A3S1S0SfS13S17S17A2M3A1S7G0A1SdG3A1A3S1S0S17S8G0A1S18S35A1A3S1S0S17S19G1Z11A2S18ZdeA1A3S1S0S17S19G1ZaA2S18Z0A1M4A3S1S0S17S19G1ZbA2S18Z800000A1A3S1S0S17S19G1ZcA2S18Z3A1A3S1S0S17S19G1ZdA2S18Z4022A1A3S1S0S17S19G1ZeA2S18ZffffffffffffffffA1A3S0S17S19G1ZfA2G4A3A2A2A2A2A2A2A2A2A2A2A2Fv;").
Proof. intros [|]; [exact E23A_at | exact E23B_at]. Qed.
Definition S23ok0_of (v : bool) : axst := pick v S23ok0A S23ok0B.
Lemma S23ok0_eq : ltac2:(tb__ "0|0|
SeS0S6S3aS28R1A1Z800000Pa1A3S2cR1A1A3Fv;").
Proof. intros [|]; reflexivity. Qed.
Definition S23ok_of (v : bool) : axst := pick v S23okA S23okB.
Lemma S23ok_eq : ltac2:(tb__ "0|3|
SeS1S0S6S9S2cR1A1M0S25S5G0A1M1S14S1aS1dG1A1ScS1aS37SdS1aA1A3A3A2M2A2S2dR1A1A3S0SeS3bG1G2A2S12A3A2Fv;").
Proof. intros [|]; [exact S23okA_eq | exact S23okB_eq]. Qed.
Definition E24_of (v : bool) : axst := pick v E24A E24B.
Lemma run24 : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eS32S33S20S21S1fS1fS1fS22A1A1A1A1A1A1A1ScSaZ7050cScSaZ6bd84SdSaA1A3A3S2dR1A1S12A5S10G0ScS2S3S29R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run24A | exact run24B]. Qed.
Definition SPIN23_of (v : bool) : axst := pick v SPIN23A SPIN23B.
Lemma run23_fail : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eU12cScSaZ6bd84SdSaA1A3S34S28R1A1A1S12A5S10G0ScS2S3S30R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run23A_fail | exact run23B_fail]. Qed.
Lemma spin23 : ltac2:(tb__ "0|2|
SeS0S11SfS2A1M0A1S4S1eU2ScSaZ6bd84SdSaA1A3S30R1A1M1S12A5S10G0ScS2S3G1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact spin23A | exact spin23B]. Qed.
Lemma E24_at : ltac2:(tb__ "0|5|
SeS1S0SaS1cS5S29R1A1M0A1M1A1M2Z7050cA3S1S0SbS1bG1A1Pa1A3S1S0S11S26A1S24S1eG2A2S10S26S27A2A3S1S0SfS13S17S17A2M3A1S7G0A1SdG3A1A3S1S0S17S8G0A1S18S35A1A3S1S0S17S19G1Z11A2S18ZdeA1A3S1S0S17S19G1ZaA2S18Z0A1M4A3S1S0S17S19G1ZbA2S18Z1000A1A3S1S0S17S19G1ZcA2S18Z3A1A3S1S0S17S19G1ZdA2S18Z22A1A3S1S0S17S19G1ZeA2S18ZffffffffffffffffA1A3S0S17S19G1ZfA2G4A3A2A2A2A2A2A2A2A2A2A2A2Fv;").
Proof. intros [|]; [exact E24A_at | exact E24B_at]. Qed.
Definition S24ok_of (v : bool) : axst := pick v S24okA S24okB.
Lemma S24ok_eq : ltac2:(tb__ "0|0|
SeS0S6S39S29R1A1Z1000Pa2A3S2eR1A1A3Fv;").
Proof. intros [|]; reflexivity. Qed.
Definition EG_of (v : bool) : axst := pick v EGA EGB.
Lemma runG : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eS32S33S20S21S1fS1fS1fS22A1A1A1A1A1A1A1ScSaS38ScSaZ7050cScSaZ6bd84SdSaA1A3A3A3S2eR1A1S12A5S10G0ScS2S3S2aR1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact runGA | exact runGB]. Qed.
Definition SPIN24_of (v : bool) : axst := pick v SPIN24A SPIN24B.
Lemma run24_fail : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eU12cScSaZ6bd84SdSaA1A3S34S29R1A1A1S12A5S10G0ScS2S3S31R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run24A_fail | exact run24B_fail]. Qed.
Lemma spin24 : ltac2:(tb__ "0|2|
SeS0S11SfS2A1M0A1S4S1eU2ScSaZ6bd84SdSaA1A3S31R1A1M1S12A5S10G0ScS2S3G1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact spin24A | exact spin24B]. Qed.
Lemma EG_at : ltac2:(tb__ "0|3|
SeS1S0SaS1cS5S2aR1A1M0A1M1A1S38A3S1S0SbS1bG1A1Pa2A3S1S0SfS13S17S17A2M2A1S7G0A1SdG2A1A3S1S0S17S8G0A1S18S35A1A3S0S16S15S1aS1dG1A1A2U31A3A2A2A2A2Fv;").
Proof. intros [|]; [exact EGA_at | exact EGB_at]. Qed.
End Start8States.

(* [comment removed for export] *)
Module Start8CallA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "bool"; "option"; "prod"; "Some"; "app"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallA"; "C22Ag"; "C22Aa"; "IGA"; "C22Ae"; "IGAf"; "MAINA"; "C22A"; "R22A"; "s22A"; "RMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_facts"; "ss_objs"; "sstate"; "sprop"; "ss_pc"; "SLit"; "ss_regs"; "sprop_below"; "ss_next"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "ax_X"; "ax_base"; "la_state"; "mkAX"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs"; "MAINPC"; "PGA"; "PGB"; "splits22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Start8RegGlob"; "Pre_G2"; "P_G2"; "Posts_G2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8StatesA"; "EGA"; "GPC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "zero_page_obj"; "ax_setX"; "ax_with_facts"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface"; "regglob_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "split_chain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8StatesA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition C22Aa : sstate := Eval vm_compute in (match split_chain (ax_S EGA) splits22 with Some St => St | None => ax_S EGA end).
Lemma split22A_ok : ltac2:(tb__ "0|0|
S0S9S1dA1S41S25S36A1S31A2SbS1dS10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition C22Ae : sstate := Eval vm_compute in set_objs C22Aa (ss_objs C22Aa ++ [zero_page_obj PGA]).
Definition C22Ag : sstate := Eval vm_compute in set_objs C22Ae (ss_objs C22Ae ++ [zero_page_obj PGB]).
Lemma C22Ae_facts : ltac2:(tb__ "0|3|
S1S0S1dS3aS10ScS1aS1cS10A1S4S1aS3cS2fA1S5S1aA1M0A3A3A2M1S12A3S1S0S8S39S10G1A2S6A3S1S0S1dS3aS12ScS1aS1cS12A1S4S1aS3cS30A1G0A3A3A2M2SfA3S0S8S39S12G2A2S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C22A : axst := ltac2:(tb__ "0|0|
S2cSfS5SaS19S19A2A1S20S38A1A3").
Lemma C22A_at : ltac2:(tb__ "0|1|
S1S0S2S1fSfA1S37A3S1S0S3S23SfA1Pa2A3S1S0SeSdS1aS1cSfA1A2U42A3S1S0S8S24SfA1S6A3S1S0S7S1eA1S1bSfA1S1bS25S36A1M0A1A3S1S0S7S19A1S21SfA1S21G0A1A3S0SeSdS1aS1cS10A1A2U40A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C22A_facts_below : ltac2:(tb__ "0|0|
S0S8S45S1eS22Pa2A1S1bSfA1A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition owinA : sobj := Eval vm_compute in ob22 C22Ag 56.
Definition s22A : wsub := Eval vm_compute in mk_s22 C22Ag owinA.
Definition R22A : list sobj := Eval vm_compute in (match entails_frA C22A Pre_G2 s22A with Some R => R | None => [] end).
Lemma ent22A : ltac2:(tb__ "0|1|
S0S9S7S1aA1M0A1S43S15S33S17A3SbG0S16A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk22A : ltac2:(tb__ "0|0|
S0S8S42S15S33S17S16S3fS26S27S2bS35A4A5S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R22A_len : length R22A = 51%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IGA : axst := Eval vm_compute in (import_postA s22A Pre_G2 P_G2 C22A R22A).
Lemma IGA_eq : ltac2:(tb__ "0|0|
S0S27S44S17S33S34S15S16A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IGAf : axst := Eval vm_compute in (ax_with_facts (ax_setX IGA []) (ss_facts (ax_S IGA) ++ ss_facts C22Ag)).
Lemma IGAf_eq : ltac2:(tb__ "0|0|
S0S27S3eS3dS11S5SaS19S19A2A1A2ScS1eS1bS25S11A1A1S1bSfA1A3A2S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IGA_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S11A1A1S40A3S0S7SaS19S19A2M0A1S29S11A1S5G0A1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition RMA_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S28S32Ubb8S4S2S2eS4S2Z7050cS4S2Z6bd84S5S2A1A3A3A3S13S6A5").
Local Strategy expand [RMA_run__R].
Definition RMA : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) RMA_run__R).
Lemma RMA_run : ltac2:(tb__ "0|0|
S0S9S7S26A1A1S28S32Ubb8S4S2S2eS4S2Z7050cS4S2Z6bd84S5S2A1A3A3A3S13S6A5S18A3").
Proof. exact (@eq_refl (option (list leafA)) RMA_run__R <: RMA_run__R = RMA). Qed.
Definition MAINA : axst := Eval vm_compute in (match RMA with Some (l :: _) => la_state l | _ => IGAf end).
Lemma runMA : ltac2:(tb__ "0|1|
S0S9S7S26A1M0A1S28S32Ubb8S4S2S2eS4S2Z7050cS4S2Z6bd84S5S2A1A3A3A3S13S6A5SbG0S4S26S2dS14S3bA2S5S26A1A3A2A3").
Proof. rewrite RMA_run. reflexivity. Qed.
Lemma MAINA_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S14A1A1S2eA3S1S0S7SaS19S19A2M0A1S29S14A1S5G0A1A3S0S19S2aS14A1S20S38A1A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8CallA.

(* [comment removed for export] *)
Module Start8CallB.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "bool"; "option"; "prod"; "Some"; "app"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallB"; "C22Bg"; "C22Ba"; "IGB"; "C22Be"; "IGBf"; "MAINB"; "C22B"; "R22B"; "s22B"; "RMB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_facts"; "ss_objs"; "sstate"; "sprop"; "ss_pc"; "SLit"; "ss_regs"; "sprop_below"; "ss_next"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "ax_X"; "ax_base"; "la_state"; "mkAX"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs"; "MAINPC"; "PGA"; "PGB"; "splits22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Start8RegGlob"; "Pre_G2"; "P_G2"; "Posts_G2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.Start8StatesB"; "EGB"; "GPC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "zero_page_obj"; "ax_setX"; "ax_with_facts"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface"; "regglob_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "split_chain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.Start8StatesB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8CallDefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition C22Ba : sstate := Eval vm_compute in (match split_chain (ax_S EGB) splits22 with Some St => St | None => ax_S EGB end).
Lemma split22B_ok : ltac2:(tb__ "0|0|
S0S9S1dA1S41S25S36A1S31A2SbS1dS10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition C22Be : sstate := Eval vm_compute in set_objs C22Ba (ss_objs C22Ba ++ [zero_page_obj PGA]).
Definition C22Bg : sstate := Eval vm_compute in set_objs C22Be (ss_objs C22Be ++ [zero_page_obj PGB]).
Lemma C22Be_facts : ltac2:(tb__ "0|3|
S1S0S1dS3aS10ScS1aS1cS10A1S4S1aS3cS2fA1S5S1aA1M0A3A3A2M1S12A3S1S0S8S39S10G1A2S6A3S1S0S1dS3aS12ScS1aS1cS12A1S4S1aS3cS30A1G0A3A3A2M2SfA3S0S8S39S12G2A2S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C22B : axst := ltac2:(tb__ "0|0|
S2cSfS5SaS19S19A2A1S20S38A1A3").
Lemma C22B_at : ltac2:(tb__ "0|1|
S1S0S2S1fSfA1S37A3S1S0S3S23SfA1Pa2A3S1S0SeSdS1aS1cSfA1A2U42A3S1S0S8S24SfA1S6A3S1S0S7S1eA1S1bSfA1S1bS25S36A1M0A1A3S1S0S7S19A1S21SfA1S21G0A1A3S0SeSdS1aS1cS10A1A2U40A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C22B_facts_below : ltac2:(tb__ "0|0|
S0S8S45S1eS22Pa2A1S1bSfA1A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition owinB : sobj := Eval vm_compute in ob22 C22Bg 56.
Definition s22B : wsub := Eval vm_compute in mk_s22 C22Bg owinB.
Definition R22B : list sobj := Eval vm_compute in (match entails_frA C22B Pre_G2 s22B with Some R => R | None => [] end).
Lemma ent22B : ltac2:(tb__ "0|1|
S0S9S7S1aA1M0A1S43S15S33S17A3SbG0S16A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk22B : ltac2:(tb__ "0|0|
S0S8S42S15S33S17S16S3fS26S27S2bS35A4A5S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R22B_len : length R22B = 51%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IGB : axst := Eval vm_compute in (import_postA s22B Pre_G2 P_G2 C22B R22B).
Lemma IGB_eq : ltac2:(tb__ "0|0|
S0S27S44S17S33S34S15S16A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IGBf : axst := Eval vm_compute in (ax_with_facts (ax_setX IGB []) (ss_facts (ax_S IGB) ++ ss_facts C22Bg)).
Lemma IGBf_eq : ltac2:(tb__ "0|0|
S0S27S3eS3dS11S5SaS19S19A2A1A2ScS1eS1bS25S11A1A1S1bSfA1A3A2S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IGB_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S11A1A1S40A3S0S7SaS19S19A2M0A1S29S11A1S5G0A1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition RMB_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S28S32Ubb8S4S2S2eS4S2Z7050cS4S2Z6bd84S5S2A1A3A3A3S13S6A5").
Local Strategy expand [RMB_run__R].
Definition RMB : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) RMB_run__R).
Lemma RMB_run : ltac2:(tb__ "0|0|
S0S9S7S26A1A1S28S32Ubb8S4S2S2eS4S2Z7050cS4S2Z6bd84S5S2A1A3A3A3S13S6A5S18A3").
Proof. exact (@eq_refl (option (list leafA)) RMB_run__R <: RMB_run__R = RMB). Qed.
Definition MAINB : axst := Eval vm_compute in (match RMB with Some (l :: _) => la_state l | _ => IGBf end).
Lemma runMB : ltac2:(tb__ "0|1|
S0S9S7S26A1M0A1S28S32Ubb8S4S2S2eS4S2Z7050cS4S2Z6bd84S5S2A1A3A3A3S13S6A5SbG0S4S26S2dS14S3bA2S5S26A1A3A2A3").
Proof. rewrite RMB_run. reflexivity. Qed.
Lemma MAINB_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S14A1A1S2eA3S1S0S7SaS19S19A2M0A1S29S14A1S5G0A1A3S0S19S2aS14A1S20S38A1A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8CallB.

