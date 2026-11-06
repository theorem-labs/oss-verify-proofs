(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import KnWalk.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AxSymExec3SemSound.   (* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanCeil.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanFO.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

Module APSC.
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition cfg_fp {FP : PropExec.FPState} (SEGS : list Segment) (R : bvmap 5 word) (p : Z)
    (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst FP R (Z_to_bv 64 p) M (seg_rom SEGS)) model.

(* [comment removed for export] *)
Lemma cfg_fp_cfg_of : forall (FP : PropExec.FPState) SEGS R p M model,
  @cfg_fp FP SEGS R p M model = @APS.cfg_of FP SEGS R p M model.
Proof. reflexivity. Qed.

Section SoundCfg.
Variable SEGS : list Segment.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis argH_sp : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
Hypothesis RES_cover : res_cover_ok SEGS A.
Hypothesis NX0_sp : nx0_sp_ok nx0.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Hypothesis HOLES_eq : forall h h' E fs, HOLES h E fs = HOLES h' E fs.
Variable FS0 : Fs.Fs.
Variable KC : nat.
(* [comment removed for export] *)
Variable FPS : PropExec.FPState -> Prop.

#[local] Abbreviation CHECK := (APF.check SEGS IT A nx0 LIMIT XN XE XB HS KC).

#[local] Abbreviation Mr := (APS.Mr A argH).
#[local] Abbreviation allowA := (APS.allowA A).
#[local] Abbreviation co_halt := (APS.co_halt SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation co_know := (APS.co_know SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation co_minv := (APS.co_minv SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation co_regs := (APS.co_regs SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation hid := (APS.hid A argH).
#[local] Abbreviation lc_guard := (APS.lc_guard).
#[local] Abbreviation sd := (APS.sd HOLES).
Let A_wf_allowA := APS.A_wf_allowA A HS XN XE XB KC.
Let H_off_segments_cs := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let abstractcell_sound := APS.abstractcell_sound SEGS A LIMIT SEGS_in_hull HULL_ok SINV argH FS0.
Let allowA_agree := APS.allowA_agree A.
Let bump_sound := APS.bump_sound SEGS A LIMIT SINV argH FS0.
Let casedisj_sound := APS.casedisj_sound SEGS A LIMIT SINV argH FS0.
Let casedisj_o_sound := APS.casedisj_o_sound SEGS A LIMIT SINV argH FS0.   (* [comment removed for export] *)
Let casedisj_o_nxt := APS.casedisj_o_nxt.
Let check_all_ok := APS.check_all_ok A.
Let compact_sound := APS.compact_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let cs_gc_ok := APS.cs_gc_ok SEGS A LIMIT SINV argH FS0.
Let cs_ok_agree := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let cs_ok_frame := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let cs_ok_inst := APS.cs_ok_inst SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let cs_ok_set_kn := APS.cs_ok_set_kn SEGS A LIMIT SINV argH FS0.
Let deand_vars := APS.deand_vars.
Let diamond_join_sound := APS.diamond_join_sound SEGS A nx0 LIMIT SEGS_in_hull HULL_ok SINV argH argH_agree SINV_agree NX0_sp FS0.
Let droprange_sound := APS.droprange_sound SEGS A LIMIT SINV argH FS0.
Let entails_h_sound := APS.entails_h_sound SEGS A nx0 LIMIT SEGS_in_hull HULL_ok SINV argH argH_agree SINV_agree NX0_sp FS0.
Let entails_sound := APS.entails_sound SEGS A LIMIT SINV argH FS0.
Let env_agree_le := APS.env_agree_le.
Let env_agree_refl := APS.env_agree_refl.
Let env_agree_trans := APS.env_agree_trans.
#[local] Abbreviation ext1 := (APS.ext1).
Let ext1_agree := APS.ext1_agree.
Let ext1_at := APS.ext1_at.
Let fact_sound := APS.fact_sound SEGS A LIMIT SINV argH FS0.
Let fog_sound := APS.fog_sound SEGS A LIMIT SINV argH FS0.
Let fognew_sound := APS.fognew_sound SEGS A LIMIT SINV argH FS0.
Let forget_sound := APS.forget_sound SEGS A LIMIT SINV argH FS0.
Let fresh_ok_mono := APS.fresh_ok_mono nx0.
Let fresh_ok_parts := APS.fresh_ok_parts nx0.
Let ghost_sound := APS.ghost_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH FS0 KC.
Let havoc_sound := APS.havoc_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let havocbig_sound := APS.havocbig_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let havocbrk_sound := APS.havocbrk_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let havocwords_sound := APS.havocwords_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let wordfresh_sound := APS.wordfresh_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.   (* [comment removed for export] *)
Let hid_agree := APS.hid_agree A nx0 argH argH_agree.
Let intro_sound := APS.intro_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let kn_contra_sound := APS.kn_contra_sound SEGS.
Let kn_vars_lt_eq := APS.kn_vars_lt_eq.
Let know_ok_filter := APS.know_ok_filter SEGS.
Let lazy_cover_cs := APS.lazy_cover_cs SEGS A LIMIT HS XN XE XB SINV argH FS0 KC.
Let loop_ok_facts := APS.loop_ok_facts nx0.
Let mrestrict_munrestrict_clean := APS.mrestrict_munrestrict_clean.
Let nth_sr_vars_lt := APS.nth_sr_vars_lt.
Let pc_cs_gc := APS.pc_cs_gc.
Let pc_inst := APS.pc_inst.
Let pc_set_kn := APS.pc_set_kn.
Let regs_ok_respell := APS.regs_ok_respell.
Let rename_sound := APS.rename_sound SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let residue_fact_sound := APS.residue_fact_sound SEGS.
Let respell_sound := APS.respell_sound SEGS A LIMIT SINV argH FS0.
Let salt2_vars := APS.salt2_vars.
Let sd_agree := APS.sd_agree nx0 HOLES HOLES_agree.
Let sd_has_nil := APS.sd_has_nil HOLES HOLES_nil.
Let sd_hnorm := APS.sd_hnorm HOLES HOLES_eq.   (* [comment removed for export] *)
Let sd_salt2 := APS.sd_salt2 nx0 HS XN XE XB HOLES HOLES_nil.
Let self_jump_word := APS.self_jump_word SEGS.
Let shape_eqb_eq := APS.shape_eqb_eq.
Let shdisj_sound := APS.shdisj_sound SEGS A LIMIT SHADOW_ok SINV argH FS0.
Let split_sound := APS.split_sound SEGS A LIMIT SINV argH FS0.
Let sr_vars_lt_eq := APS.sr_vars_lt_eq.
Let t_eq_alt2 := APS.t_eq_alt2.
Let u_small := APS.u_small.
Let unvis_sound := APS.unvis_sound SEGS A LIMIT SHADOW_ok SINV argH FS0.
#[local] Abbreviation upd := (APS.upd).
Let upd_agree := APS.upd_agree.
Let upd_at := APS.upd_at.
Let upd_upd := APS.upd_upd.
Let xhi2_sound := APS.xhi2_sound SEGS.
Let xlo2_sound := APS.xlo2_sound SEGS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cont_cfg (cs cs' : acs) (E : env) (model : Model) (T : TSet) : Prop :=
  forall (FP' : PropExec.FPState), FPS FP' ->
  forall E' R' FULL' model',
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
    srealizes_cfg SEGS (@cfg_fp FP' SEGS R' (pc cs') FULL' model') T.

(* [comment removed for export] *)
Definition node1_stmt_cfg (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    cont_cfg cs cs' E model T ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.

Definition sys_stmt_cfg (y : snode) : Prop := node1_stmt_cfg (is_ecall_at SEGS) (node_sys A nx0 y).
Definition x_stmt_cfg (x : xnode) : Prop := forall args, node1_stmt_cfg APS.always (node_x SEGS A nx0 x args).
Definition join_stmt_cfg : Prop := forall b off n, node1_stmt_cfg APS.always (fun cs => node_join SEGS cs b off n).
Definition ext_stmt_cfg : Prop := forall id args, node1_stmt_cfg APS.always (XN id args).

(* [comment removed for export] *)
Definition mm2_stmt_fo (node : acs -> option (acs * acs)) : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall cs csa csb E R FULL model TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    cont_cfg cs csb E model TB ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) TB.

Definition mm3_stmt_fo (node : acs -> option (acs * acs * list acs)) : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall cs csa csb cscs E R FULL model TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    cont_cfg cs csb E model TB ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) TB.

Definition brk2_stmt_fo : Prop := mm2_stmt_fo (node_brk2 A LIMIT).

(* [comment removed for export] *)
Definition brku_stmt_cfg : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall cs csa csb E R FULL model T,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_brku A LIMIT cs = Some (csa, csb) ->
    cont_cfg cs csa E model T -> cont_cfg cs csb E model T ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.

Definition exit_stmt_cfg : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall cs code E R FULL model,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) (t_exit (Z_to_bv 64 code) (m_fs model)).

(* [comment removed for export] *)
Definition ext2_stmt_cfg : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall id args cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> XB id args cs = Some (csa, csb) ->
    cont_cfg cs csa E model TA -> cont_cfg cs csb E model TB ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) (t_alt2 TA TB).

(* [comment removed for export] *)
Definition emit_stmt_cfg : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall id args cs fd ps cs' E R FULL model T,
    cs_ok E cs R FULL model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    cont_cfg cs cs' E model T ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) (t_emit (Wp E fd ps) T).

(* [comment removed for export] *)
Definition holes_stmt_cfg : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall h ch, HS h = Some ch ->
  forall E R FULL model, cs_ok E ch R FULL model ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc ch) FULL model) (HOLES h E (m_fs model)).

(* [comment removed for export] *)
Definition run_block_stmt_cfg : Prop :=
  forall (FP : PropExec.FPState), FPS FP ->
  forall gb bfuel stops cs cs' E R FULL model T,
    (nx0 <= gb)%nat ->
    run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc cs') FULL' model') T) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.

(* [comment removed for export] *)
Definition node1_stmt_fp (FP : PropExec.FPState) (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc cs') FULL' model') T) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.

Lemma node1_of_fp : forall pre node, (forall FP, FPS FP -> node1_stmt_fp FP pre node) -> node1_stmt_cfg pre node.
Proof.
  intros pre node H FP HFP cs cs' E R FULL model T HC Hpre Hn Hk.
  exact (H FP HFP cs cs' E R FULL model T HC Hpre Hn (Hk FP HFP)).
Qed.

Definition mm2_stmt_fp (FP : PropExec.FPState) (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E R FULL model TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc csb) FULL' model') TB) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) TB.

Lemma mm2_of_fp : forall node, (forall FP, FPS FP -> mm2_stmt_fp FP node) -> mm2_stmt_fo node.
Proof.
  intros node H FP HFP cs csa csb E R FULL model TB HC Hec Hn Hk.
  exact (H FP HFP cs csa csb E R FULL model TB HC Hec Hn (Hk FP HFP)).
Qed.

Definition mm3_stmt_fp (FP : PropExec.FPState) (node : acs -> option (acs * acs * list acs)) : Prop :=
  forall cs csa csb cscs E R FULL model TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc csb) FULL' model') TB) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) TB.

Lemma mm3_of_fp : forall node, (forall FP, FPS FP -> mm3_stmt_fp FP node) -> mm3_stmt_fo node.
Proof.
  intros node H FP HFP cs csa csb cscs E R FULL model TB HC Hec Hn Hk.
  exact (H FP HFP cs csa csb cscs E R FULL model TB HC Hec Hn (Hk FP HFP)).
Qed.

Definition ext2_stmt_fp (FP : PropExec.FPState) : Prop :=
  forall id args cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> XB id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc csb) FULL' model') TB) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) (t_alt2 TA TB).

Lemma ext2_of_fp : (forall FP, FPS FP -> ext2_stmt_fp FP) -> ext2_stmt_cfg.
Proof.
  intros H FP HFP id args cs csa csb E R FULL model TA TB HC Hn HA HB.
  exact (H FP HFP id args cs csa csb E R FULL model TA TB HC Hn (HA FP HFP) (HB FP HFP)).
Qed.

Definition emit_stmt_fp (FP : PropExec.FPState) : Prop :=
  forall id args cs fd ps cs' E R FULL model T,
    cs_ok E cs R FULL model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc cs') FULL' model') T) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) (t_emit (Wp E fd ps) T).

Lemma emit_of_fp : (forall FP, FPS FP -> emit_stmt_fp FP) -> emit_stmt_cfg.
Proof.
  intros H FP HFP id args cs fd ps cs' E R FULL model T HC Hn HT Hk.
  exact (H FP HFP id args cs fd ps cs' E R FULL model T HC Hn HT (Hk FP HFP)).
Qed.

Definition brku_stmt_fp (FP : PropExec.FPState) : Prop :=
  forall cs csa csb E R FULL model T,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_brku A LIMIT cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc csa) FULL' model') T) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc csb) FULL' model') T) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.

Lemma brku_of_fp : (forall FP, FPS FP -> brku_stmt_fp FP) -> brku_stmt_cfg.
Proof.
  intros H FP HFP cs csa csb E R FULL model T HC Hec Hn HA HB.
  exact (H FP HFP cs csa csb E R FULL model T HC Hec Hn (HA FP HFP) (HB FP HFP)).
Qed.

Definition sys_stmt_fp (FP : PropExec.FPState) (y : snode) : Prop := node1_stmt_fp FP (is_ecall_at SEGS) (node_sys A nx0 y).

Lemma sys_of_fp : forall y, (forall FP, FPS FP -> sys_stmt_fp FP y) -> sys_stmt_cfg y.
Proof. intros y H. apply node1_of_fp. exact H. Qed.

Definition exit_stmt_fp (FP : PropExec.FPState) : Prop :=
  forall cs code E R FULL model,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) (t_exit (Z_to_bv 64 code) (m_fs model)).

Lemma exit_of_fp : (forall FP, FPS FP -> exit_stmt_fp FP) -> exit_stmt_cfg.
Proof. intros H FP HFP. exact (H FP HFP). Qed.

(* [comment removed for export] *)
Definition x_stmt_fp (FP : PropExec.FPState) (x : xnode) : Prop :=
  forall args, node1_stmt_fp FP APS.always (node_x SEGS A nx0 x args).

Lemma x_of_fp : forall x, (forall FP, FPS FP -> x_stmt_fp FP x) -> x_stmt_cfg x.
Proof. intros x H args. apply node1_of_fp. intros FP HFP. exact (H FP HFP args). Qed.

Definition join_stmt_fp (FP : PropExec.FPState) : Prop :=
  forall b off n, node1_stmt_fp FP APS.always (fun cs => node_join SEGS cs b off n).

Lemma join_of_fp : (forall FP, FPS FP -> join_stmt_fp FP) -> join_stmt_cfg.
Proof. intros H b off n. apply node1_of_fp. intros FP HFP. exact (H FP HFP b off n). Qed.

Definition ext_stmt_fp (FP : PropExec.FPState) : Prop :=
  forall id args, node1_stmt_fp FP APS.always (XN id args).

Lemma ext_of_fp : (forall FP, FPS FP -> ext_stmt_fp FP) -> ext_stmt_cfg.
Proof. intros H id args. apply node1_of_fp. intros FP HFP. exact (H FP HFP id args). Qed.

(* [comment removed for export] *)
Hypothesis run_block_cfg : run_block_stmt_cfg.
Hypothesis node_sys_cfg : forall y, sys_stmt_cfg y.
Hypothesis node_brk2_cfg : brk2_stmt_fo.
Hypothesis node_brku_cfg : brku_stmt_cfg.   (* [comment removed for export] *)
Hypothesis node_mmap2_cfg : mm2_stmt_fo (node_mmap2 A nx0 LIMIT).
Hypothesis node_mmapin_cfg : forall hole : bool, mm3_stmt_fo (node_mmapin A LIMIT hole).
Hypothesis node_mprotect2_cfg : mm2_stmt_fo (node_mprotect2 A LIMIT).
Hypothesis node_exit_cfg : exit_stmt_cfg.
Hypothesis node_x_cfg : forall x, APF.xnode_fo x = true -> x_stmt_cfg x.   (* [comment removed for export] *)
Hypothesis node_join_cfg : join_stmt_cfg.
Hypothesis node_ext_cfg : ext_stmt_cfg.
Hypothesis node_emit_cfg : emit_stmt_cfg.
Hypothesis node_ext2_cfg : ext2_stmt_cfg.
Hypothesis HS_cfg : holes_stmt_cfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma check_vars_fo : forall bfuel fuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros lc p cs s Hc; [discriminate|].
  cbn [APF.check] in Hc. rewrite ?entailsF_fun, ?entails_hF_fun, ?node_diamond_joinF_fun in Hc.
  match type of Hc with (if ?g then _ else _) = _ => destruct g; [discriminate|] end.
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|bua bub|dd1 dd2 ddo ddj ddrs ddk|wfb wfn wfk|cx1 cx2 cxo cxk1 cxk2].
  - destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { destruct (Z.leb hi mid); [exact (IH _ k1 _ s Hc) | exact (IH _ k2 _ s Hc)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv, (IH _ k1 _ s1 H1), (IH _ k2 _ s2 H2). reflexivity.
  - destruct (erange (kn cs) ce) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (IH _ ck1 _ s Hc) | exact (IH _ ck2 _ s Hc)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))); [exact (IH _ ck2 _ s Hc)|].
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))); [exact (IH _ ck1 _ s Hc)|].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ ck1 _ s1 H1).
  - destruct (node_casedisj cs db1 db2) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ dk1 _ s1 H1).
  - destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (fact_ok (kn cs) K); [|discriminate]. exact (IH _ k _ s Hc).
  - destruct (node_join SEGS cs jb joff jn) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - destruct (node_bump cs bm) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havoc nx0 cs hrs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havocbig nx0 cs hbK) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_fresh nx0 cs r logc fb) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_sys A nx0 y cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmap2 A nx0 LIMIT cs) as [[csa csb]|]; [|discriminate].
    exact (IH _ mb _ s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|]; [|discriminate].
    exact (IH _ ib _ s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    exact (IH _ qb _ s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_brk2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    exact (IH _ kb _ s Hc).
  - destruct (APF.xnode_fo x); [|discriminate].
    destruct (node_x SEGS A nx0 x args cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XN xid xargs cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XE eid eargs cs) as [[[fd ps] cs1]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. exact (IH _ k cs1 s1 H1).
  - destruct (XB bid bargs cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. rewrite (IH _ kb1 _ sa H1), (IH _ kb2 _ sb H2). reflexivity.
  - destruct (loop_ok nx0 cs lJ lN linv) as [nhi|]; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool; [|discriminate].
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|]; [|discriminate].
    destruct sb; try discriminate. exact (IH _ lk _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
    destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool; [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (HS h) as [ch|]; [|discriminate]. destruct (entails cs ch); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_exit cs); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (node_spin SEGS cs); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (node_fog cs fi fsz) as [cs1|]; [|discriminate]. exact (IH _ fk cs1 s Hc).
  - destruct (node_fognew cs gi gsz) as [cs1|]; [|discriminate]. exact (IH _ gk cs1 s Hc).
  - destruct (node_ghost LIMIT cs gb gn) as [cs1|]; [|discriminate]. exact (IH _ gk2 cs1 s Hc).
  - destruct (node_unvis A cs ub un) as [cs1|]; [|discriminate]. exact (IH _ uk cs1 s Hc).
  - destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|]; [|discriminate]. exact (IH _ hk cs1 s Hc).
  - destruct (node_intro nx0 cs ilo ihi) as [cs1|]; [|discriminate]. exact (IH _ ik cs1 s Hc).
  - destruct (branch_probe IT cs) as [e|]; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool.
    { destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|]; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate]. exact (IH _ dk cs1 s Hc). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|]; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|]; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|]; [|discriminate]. exact (IH _ dk csj s Hc).
  - destruct (node_rename _ cs rnm) as [cs1|]; [|discriminate]. exact (IH _ rnk cs1 s Hc).
  - destruct (node_compact _ cs) as [cs1|]; [|discriminate]. exact (IH _ cpk cs1 s Hc).
  - destruct (via_ok nx0 cs vjs vlo); [|discriminate].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk|]; [|discriminate]. exact (IH _ vka _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
    injection Hc as <-. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [_ Hsv]. exact Hsv.
  - destruct (node_abstractcell A cs ab an) as [cs1|]; [|discriminate]. exact (IH _ ak cs1 s Hc).
  - destruct (node_havocwords nx0 cs hws) as [cs1|]; [|discriminate]. exact (IH _ hwk cs1 s Hc).
  - destruct (node_respell cs rsr rse) as [cs1|]; [|discriminate]. exact (IH _ rsk cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|]; [|discriminate].
    exact (IH _ ihb _ s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_brku A LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa bua) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb bub) as [sb|] eqn:H2; [|discriminate].
    destruct (shape_eqb (hnorm sa) (hnorm sb)); [|discriminate]. injection Hc as <-. exact (IH _ bua _ sa H1).
  - (* [comment removed for export] *)
    destruct (node_casedisj_o cs dd1 dd2 ddo) as [[cs1 cs2]|]; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (ddj :: STOPS A) cs1) as [ca|]; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (ddj :: STOPS A) cs2) as [cb|]; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) ddj ddrs ca cb) as [csj|]; [|discriminate]. exact (IH _ ddk csj s Hc).
  - (* [comment removed for export] *)
    destruct (node_wordfresh SEGS nx0 cs wfb wfn) as [cs1|]; [|discriminate]. exact (IH _ wfk cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (node_casedisj_o cs cx1 cx2 cxo) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa cxk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb cxk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ cxk1 _ s1 H1).
Qed.


Lemma node_fresh_cfg : forall r logc base, node1_stmt_cfg APS.always (fun cs => node_fresh nx0 cs r logc base).
Proof.
  intros r logc base FP HFP cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_fresh in Hn.
  set (b := match base with Some b => b | None => ELit 0 end) in Hn.
  set (e := esub (reg cs r) b) in Hn.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign (kn cs) e)
            && AP.expr_vars_lt (nxt cs) b && AP.expr_vars_lt (nxt cs) e && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hve]. apply andb_prop in Hc as [Hc Hvb].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
  apply andb_prop in Hc as [Hr0 Hr32].
  apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
  destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate].
  injection Hn as <-.
  set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  pose proof (xlo2_sound E _ (kn cs) e lo HK Hlo) as Hlo'.
  pose proof (xhi2_sound E _ (kn cs) e hi HK Hhi) as Hhi'.
  destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
  assert (Hc : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
  assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
  assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
  { eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
  destruct Hcd as [q Hq].
  pose proof (u64_range (edenot E e)) as Hue.
  assert (Hq0 : 0 <= q) by nia.
  assert (Hq64 : q < 2 ^ 64) by nia.
  set (a := Z_to_bv 64 q). set (E' := ext1 E v a).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  destruct (fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC'.
  assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hve]).
  assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
  assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
  { unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite ext1_at. unfold a.
    apply bv_eq. rewrite u_mul64. rewrite (u_small c) by lia. rewrite (u_small q) by lia. rewrite Z.mod_small by nia. lia. }
  assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
  apply (Hk FP HFP E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
  (* [comment removed for export] *)
  assert (HKf : know_ok SEGS E' (Mr E' cs model FULL)
            ((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
               :: residue_fact (kn cs) e (escale c (EVar v)))
             ++ kn cs)).
  { apply Forall_app. split; [|exact (co_know _ _ _ _ _ HC')].
    constructor; [|constructor].
    - cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite ext1_at. unfold a. rewrite u_small by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; nia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
      rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
    - eapply (residue_fact_sound E E' _ _ (kn cs) e); [exact HK | exact Hne |].
      intros e1 s1 Hd1. symmetry. eapply (edenot_agree' v); [exact Hag | exact (deand_vars v e e1 s1 Hd1 Hve)]. }
  destruct HC'; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption.
  - apply regs_ok_respell; [eassumption | lia |].
    unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv, He_sem.
    apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
    rewrite Z.mod_small by lia. reflexivity.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - reflexivity.
Qed.




Lemma node_spin_cfg : forall (FP : PropExec.FPState) cs E R FULL model,
  cs_ok E cs R FULL model -> node_spin SEGS cs = true ->
  srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) t_nil.
Proof.
  intros FP cs E R FULL model HC Hn. unfold node_spin in Hn.
  apply andb_prop in Hn as [Hn Hw]. apply andb_prop in Hn as [H0 H4].
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  apply Z.eqb_eq in Hw.
  assert (Hw' : w = Z_to_bv 32 SPIN_WORD).
  { apply bv_eq. rewrite Hw. reflexivity. }
  subst w.
  apply srz_cfg_spin.
  - apply is_self_jump_to_spin. apply self_jump_word; [reflexivity | exact Hf].
  - exact (co_halt _ _ _ _ _ HC).
Qed.

(* [comment removed for export] *)
Definition LCOK_cfg (lc : option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
  match lc with
  | None => True
  | Some (LC h nx lo hi) => ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ length (s_regs (a_ss nx)) = 32%nat) /\
              forall (FP' : PropExec.FPState), FPS FP' -> forall E' R' F' m', env_agree lo E E' -> cs_ok E' nx R' F' m' -> m_fs m' = fs ->
                srealizes_cfg SEGS (@cfg_fp FP' SEGS R' h F' m') D
  | Some (JC j js sk b lo) => ((nx0 <= b)%nat /\ (b <= lo)%nat /\ length (s_regs (a_ss js)) = 32%nat) /\
              forall (FP' : PropExec.FPState), FPS FP' -> forall E' R' F' m', env_agree b E E' -> cs_ok E' js R' F' m' -> m_fs m' = fs ->
                srealizes_cfg SEGS (@cfg_fp FP' SEGS R' (pc js) F' m') (sd D E' fs sk)
  end.

Lemma LCOK_bnd_cfg : forall lc D E fs, LCOK_cfg lc D E fs -> (nx0 <= match lc with Some c => lc_bnd c | None => nx0 end)%nat.
Proof. intros [[h nx lo hi|j js sk b lo]|] D E fs HL; cbn [LCOK_cfg lc_bnd] in *; [destruct HL as [(H1 & H2 & _) _]; lia | destruct HL as [(H1 & _ & _) _]; lia | lia]. Qed.

Lemma LCOK_agree_cfg : forall lc D E E' fs cs,
  LCOK_cfg lc D E fs -> lc_guard lc cs = true -> env_agree (nxt cs) E E' -> LCOK_cfg lc D E' fs.
Proof.
  intros [[h nx lo hi|j js sk b lo]|] D E E' fs cs HL Hg Hag; [| |exact I]; cbn [LCOK_cfg APS.lc_guard lc_bnd] in *;
  apply Nat.leb_le in Hg; destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros FP' HFP' E2 R' F' m' Hag2; apply HL; first [exact HFP' | (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2])].
Qed.

Lemma LCOK_agree_gb_cfg : forall lc D E E' fs,
  LCOK_cfg lc D E fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> LCOK_cfg lc D E' fs.
Proof.
  intros [[h nx lo hi|j js sk b lo]|] D E E' fs HL Hag; [| |exact I]; cbn [LCOK_cfg lc_bnd] in *;
  destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros FP' HFP' E2 R' F' m' Hag2; apply HL; first [exact HFP' | (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2])].
Qed.

(* [comment removed for export] *)
Lemma cont_agree_cfg : forall (FP' : PropExec.FPState) bfuel fuel lc k cs cs' s E model D,
  CHECK bfuel fuel lc cs' k = COk s ->
  LCOK_cfg lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  (forall E R FULL model, cs_ok E cs' R FULL model -> LCOK_cfg lc D E (m_fs model) -> D [] ->
     srealizes_cfg SEGS (@cfg_fp FP' SEGS R (pc cs') FULL model) (sd D E (m_fs model) s)) ->
  forall E' R' FULL' model',
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
    srealizes_cfg SEGS (@cfg_fp FP' SEGS R' (pc cs') FULL' model') (sd D E (m_fs model) s).
Proof.
  intros FP' bfuel fuel lc k cs cs' s E model D Hc HL Hg HD IH E' R' FULL' model' [Hag Hag2] HC' Hfs.
  rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars_fo _ _ _ _ _ _ Hc)), <- Hfs.
  apply (IH E' R' FULL' model' HC'); [|exact HD]. rewrite Hfs. eapply LCOK_agree_cfg; [exact HL | exact Hg | exact Hag2].
Qed.

Theorem check_sound_cfg : forall fuel bfuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s ->
  forall (FP : PropExec.FPState), FPS FP ->
  forall E R FULL model D, cs_ok E cs R FULL model -> LCOK_cfg lc D E (m_fs model) -> D [] ->
  srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) (sd D E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel lc p cs s Hc FP HFP E R FULL model D HC HL HD; [discriminate|].
  cbn [APF.check] in Hc. rewrite ?entailsF_fun, ?entails_hF_fun, ?node_diamond_joinF_fun in Hc.
  match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
  (* [comment removed for export] *)
  assert (CONT : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall (FP' : PropExec.FPState), FPS FP' ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            m_fs model' = m_fs model -> srealizes_cfg SEGS (@cfg_fp FP' SEGS R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk FP' HFP'. eapply (cont_agree_cfg FP'); [exact Hk | exact HL | exact Hg | exact HD |].
    intros; eapply IH; eassumption. }
  (* [comment removed for export] *)
  assert (CONT0 : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            m_fs model' = m_fs model -> srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk. exact (CONT k cs' s' Hk FP HFP). }
  assert (SAME : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' R FULL model ->
            srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs') FULL model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hk HC'. refine (CONT0 k cs' s' Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|bua bub|dd1 dd2 ddo ddj ddrs ddk|wfb wfn wfk|cx1 cx2 cxo cxk1 cxk2].
  - (* [comment removed for export] *)
    destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
    pose proof (LCOK_bnd_cfg lc D E (m_fs model) HL) as Hgb.
    eapply (run_block_cfg FP HFP); [exact Hgb | exact Hrb | exact HC |].
    intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT0 k cs1 s Hc E' R' FULL' model' Hag HC1 Hfs).
  - (* [comment removed for export] *)
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { (* [comment removed for export] *)
         pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
         destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hc HC) | exact (SAME k2 _ s Hc HC)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    destruct (split_sound cs e mid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + exact (SAME k1 _ s1 H1 (HCl Hle)).
    + exact (SAME k2 _ s2 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    destruct (erange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hc HC) | exact (SAME ck2 _ s Hc HC)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (split_sound cs ce cmid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCl Hle)) Hk1).
      - exact (SAME ck2 _ s Hc (HCr ltac:(lia))). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exact (SAME ck1 _ s Hc (HCl Hle)).
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCr ltac:(lia))) Hk2). }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    + exact (SAME ck1 _ s1 H1 (HCl Hle)).
    + exact (SAME ck2 _ s1 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    destruct (node_casedisj cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
    destruct (casedisj_sound cs db1 db2 csa csb E R FULL model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
    + exact (SAME dk1 _ s1 H1 HC').
    + exact (SAME dk2 _ s1 H2 HC').
  - (* [comment removed for export] *)
    destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|] eqn:Hn; [|discriminate].
    destruct (shdisj_sound cs sb1 sn1 sb2 sn2 cs1 E R FULL model HC Hn) as [HC' Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hc HC').
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound E _ (kn cs) (co_know _ _ _ _ _ HC) Hk).
  - (* [comment removed for export] *)
    destruct (fact_ok (kn cs) K) eqn:Hf; [|discriminate].
    exact (SAME k _ s Hc (fact_sound E cs R FULL model K HC Hf)).
  - (* [comment removed for export] *)
    destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_join_cfg jb joff jn FP HFP cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    exact (SAME k _ s Hc (forget_sound E cs R FULL model ixs HC)).
  - (* [comment removed for export] *)
    assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    rewrite <- Hpc. exact (SAME k _ s Hc (droprange_sound E cs R FULL model db dn HC)).
  - (* [comment removed for export] *)
    rewrite <- (pc_set_kn cs (kn_keep (kn cs) gws)).
    exact (SAME k _ s Hc (cs_ok_set_kn E cs R FULL model _ HC (know_ok_filter E _ _ (kn cs) (co_know _ _ _ _ _ HC)))).
  - (* [comment removed for export] *)
    destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (bump_sound E cs R FULL model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havoc_sound E cs R FULL model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT0 k cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbig_sound E cs R FULL model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT0 k cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_fresh_cfg r logc fb FP HFP cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_sys A nx0 y cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_sys_cfg y FP HFP cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmap2 A nx0 LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    eapply (node_mmap2_cfg FP HFP cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT mb csb s Hc)].
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    eapply (node_mmapin_cfg false FP HFP cs csa csb cscs E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ib csb s Hc)].
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    eapply (node_mprotect2_cfg FP HFP cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT qb csb s Hc)].
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_brk2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    eapply (node_brk2_cfg FP HFP cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT kb csb s Hc)].
  - (* [comment removed for export] *)
    destruct (APF.xnode_fo x) eqn:Hxf; [|discriminate].
    destruct (node_x SEGS A nx0 x args cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_x_cfg x Hxf args FP HFP cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_ext_cfg xid xargs FP HFP cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_emit_cfg FP HFP eid eargs cs fd ps cs1 E R FULL model); [exact HC | exact Hn | apply sd_has_nil; exact HD |]. exact (CONT k cs1 s1 H1).
  - (* [comment removed for export] *)
    destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    eapply (node_ext2_cfg FP HFP bid bargs cs csa csb E R FULL model); [exact HC | exact Hn | exact (CONT kb1 csa sa H1) | exact (CONT kb2 csb sb H2)].
  - (* [comment removed for export] *)
    destruct (loop_ok nx0 cs lJ lN linv) as [nhi|] eqn:Hlo; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool eqn:Ht; [|discriminate].
    apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|] eqn:Hbody; [|discriminate].
    destruct sb; try discriminate. rename Hc into Hk.
    destruct (loop_ok_facts cs lJ lN linv nhi Hlo) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
    destruct (fresh_ok_parts cs Ffr) as (_ & _ & _ & _ & _ & _ & Fle).
    pose proof (xhi_sound SEGS E _ (kn cs) lN nhi (co_know _ _ _ _ _ HC) FxN) as HNv.
    set (Nv := bv_unsigned (edenot E lN)) in *. pose proof (u64_range (edenot E lN)) as RN. fold Nv in RN.
    set (D0 := sd D E (m_fs model) s).
    assert (HD0 : D0 []) by (apply sd_has_nil; exact HD).
    set (h := pc cs) in *.
    (* [comment removed for export] *)
    assert (Q : forall m j (FP' : PropExec.FPState), FPS FP' -> forall E' R' F' m', j = Nv - Z.of_nat m -> 0 <= j -> env_agree (nxt cs) E E' ->
               cs_ok E' (inst linv lJ (ELit j)) R' F' m' -> m_fs m' = m_fs model ->
               srealizes_cfg SEGS (@cfg_fp FP' SEGS R' h F' m') D0).
    { induction m as [|m IHm]; intros j FP' HFP' E' R' F' m' Hj Hj0 Hag HCj Hfs.
      - (* [comment removed for export] *)
        assert (HNe : edenot E' lN = edenot E' (ELit j)).
        { cbn [edenot]. rewrite <- (edenot_agree' (nxt cs) E E' lN Hag FvN). apply bv_eq. rewrite u_small by lia. cbn in Hj. lia. }
        assert (HCN : cs_ok E' (inst linv lJ lN) R' F' m').
        { apply (proj2 (cs_ok_inst E' lJ lN linv R' F' m' ltac:(lia) Flog)). rewrite HNe.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        unfold D0. rewrite (sd_agree D E E' (m_fs model) s ltac:(eapply env_agree_le; [exact Hag | exact Fle]) (check_vars_fo _ _ _ _ _ _ Hk)).
        rewrite <- Hfs. replace h with (pc (inst linv lJ lN)) by (unfold h; rewrite pc_inst; exact Hpc).
        apply (IH bfuel lc lk _ s Hk FP' HFP' E' R' F' m' D HCN); [|exact HD].
        rewrite Hfs. eapply LCOK_agree_cfg; [exact HL | exact Hg | exact Hag].
      - (* [comment removed for export] *)
        set (E'' := upd E' lJ (Z_to_bv 64 j)).
        assert (Hjlt : j < Nv) by lia.
        assert (HCinv : cs_ok E'' linv R' F' m').
        { unfold E''. replace (Z_to_bv 64 j) with (edenot E' (ELit j)) by reflexivity.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        assert (Hag'' : env_agree (nxt cs) E E'').
        { eapply env_agree_trans; [exact Hag|]. eapply env_agree_le; [apply upd_agree | exact FJ]. }
        assert (HNE'' : edenot E'' lN = edenot E lN) by (symmetry; eapply (edenot_agree' (nxt cs)); [exact Hag'' | exact FvN]).
        assert (HJ'' : ev E'' lJ = Z_to_bv 64 j) by (unfold E''; apply upd_at).
        assert (HCb : cs_ok E'' (loop_body_state lJ lN nhi linv) R' F' m').
        { unfold loop_body_state, add_kn. apply cs_ok_set_kn; [exact HCinv|]. apply Forall_app. split; [|exact (co_know _ _ _ _ _ HCinv)].
          constructor; [|constructor; [|constructor]]; cbn [kentry_ok edenot].
          - rewrite HJ'', u_small by lia. lia.
          - unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HNE'', HJ''. fold Nv. rewrite u_small by lia.
            rewrite Z.mod_small by lia. lia. }
        replace h with (pc (loop_body_state lJ lN nhi linv)) by exact Hpc.
        refine (IH bfuel _ lbody _ SNext Hbody FP' HFP' E'' R' F' m' D0 HCb _ HD0).
        (* [comment removed for export] *)
        cbn [LCOK_cfg]. split.
        { split; [lia|]. split; [lia|]. unfold inst. cbn [a_ss s_regs mk_ss]. rewrite length_map. exact Flen. }
        intros FP3 HFP3 E3 R3 F3 m3 Hag3 HC3 Hfs3.
        assert (HJ3 : ev E3 lJ = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag3); lia).
        assert (Hnext : edenot E3 (eaddz (EVar lJ) 1) = Z_to_bv 64 (j + 1)).
        { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ3. apply bv_eq. rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity. }
        set (E4 := upd E3 lJ (Z_to_bv 64 (j + 1))).
        apply (IHm (j + 1) FP3 HFP3 E4 R3 F3 m3); [lia | lia | | | rewrite Hfs3; exact Hfs].
        + eapply env_agree_trans; [exact Hag''|]. eapply env_agree_trans; [eapply env_agree_le; [exact Hag3 | lia]|].
          eapply env_agree_le; [apply upd_agree | exact FJ].
        + apply (proj2 (cs_ok_inst E4 lJ (ELit (j + 1)) linv R3 F3 m3 ltac:(lia) Flog)).
          unfold E4. cbn [edenot]. rewrite upd_upd. rewrite <- Hnext.
          apply (proj1 (cs_ok_inst E3 lJ (eaddz (EVar lJ) 1) linv R3 F3 m3 ltac:(lia) Flog)). exact HC3. }
    (* [comment removed for export] *)
    destruct (entails_h_sound (Datatypes.S lJ) (nxt linv) E cs (inst linv lJ (ELit 0)) R FULL model HC Hent ltac:(lia)
                ltac:(unfold inst; cbn [a_ss s_regs mk_ss]; rewrite length_map; exact Flen)) as (E1 & Hag1 & _ & HC1 & _).
    unfold D0 in Q. apply (Q (Z.to_nat Nv) 0 FP HFP E1 R FULL model); [lia | lia | eapply env_agree_le; [exact Hag1 | lia] | exact HC1 | reflexivity].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
    destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool eqn:Ht; [|discriminate]. injection Hc as <-. cbn [sd].
    apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
    cbn [LCOK_cfg] in HL. destruct HL as [(Hn0 & Hlh & Hlen) HL]. cbn [lc_guard lc_bnd] in Hg. apply Nat.leb_le in Hg.
    destruct (entails_h_sound lo hi E cs nx R FULL model HC Hent Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc').
    rewrite Hpc. exact (HL FP HFP E' R FULL model Hag HC' eq_refl).
  - (* [comment removed for export] *)
    destruct (HS h) as [ch|] eqn:Hh; [|discriminate].
    destruct (entails cs ch) eqn:He; [|discriminate]. injection Hc as <-. cbn [sd].
    destruct (entails_sound E cs ch R FULL model HC He) as [HC' Hpc].
    rewrite <- Hpc. exact (HS_cfg FP HFP h ch Hh E R FULL model HC').
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_exit_cfg FP HFP); eassumption.
  - (* [comment removed for export] *)
    destruct (node_spin SEGS cs) eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    exact (node_spin_cfg FP cs E R FULL model HC Hn).
  - (* [comment removed for export] *)
    destruct (node_fog cs fi fsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fog_sound E cs R FULL model fi fsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME fk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_fognew cs gi gsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fognew_sound E cs R FULL model gi gsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_ghost LIMIT cs gb gn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (ghost_sound E cs R FULL model gb gn cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk2 _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_unvis A cs ub un) as [cs1|] eqn:Hn; [|discriminate].
    destruct (unvis_sound E cs R FULL model ub un cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME uk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbrk_sound E cs R FULL model hlo hhi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT0 hk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (intro_sound E cs R FULL model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT0 ik cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (LCOK_bnd_cfg lc D E (m_fs model) HL) as Hgb.
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
    { (* [comment removed for export] *)
      destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply (run_block_cfg FP HFP); [exact Hgb | exact Hrb | exact HC |].
      intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT0 dk cs1 s Hc E' R' FULL' model' Hag HC1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (diamond_join_sound (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply (run_block_cfg FP HFP); [exact Hgb | exact Hra | exact (HCl Hle) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Ja E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT0 dk csj s Hc E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
    + rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply (run_block_cfg FP HFP); [exact Hgb | exact Hrb | exact (HCr ltac:(lia)) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Jb E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT0 dk csj s Hc E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
  - (* [comment removed for export] *)
    destruct (node_rename _ cs rnm) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd_cfg lc D E (m_fs model) HL) as Hgb.
    destruct (rename_sound _ E cs R FULL model rnm cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars_fo _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact HFP | exact HC1 | eapply LCOK_agree_gb_cfg; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    destruct (node_compact _ cs) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd_cfg lc D E (m_fs model) HL) as Hgb.
    destruct (compact_sound _ E cs R FULL model cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars_fo _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact HFP | exact HC1 | eapply LCOK_agree_gb_cfg; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    destruct (via_ok nx0 cs vjs vlo) eqn:Hv; [|discriminate].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk|] eqn:Hk; [|discriminate].
    unfold via_ok in Hv. repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [Hv ?X] end.
    match goal with Hl : match s_log (a_ss vjs) with _ => _ end = true |- _ => clear Hl end.
    match goal with Hl : Nat.eqb (length _) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
    repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
    pose proof (LCOK_bnd_cfg lc D E (m_fs model) HL) as Hgb.
    assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
    { destruct lc as [c|]; [apply Nat.leb_le; exact Hg | lia]. }
    apply (IH bfuel (Some (JC vj vjs sk (nxt cs) vlo)) vka cs s Hc FP HFP E R FULL model D HC); [|exact HD].
    cbn [LCOK_cfg]. split; [split; [lia | split; [lia | exact Hlen]]|].
    intros FP' HFP' E' R' F' m' Hag HC' Hfs. rewrite <- Hfs.
    apply (IH bfuel lc vk vjs sk Hk FP' HFP' E' R' F' m' D HC'); [|exact HD].
    rewrite Hfs. eapply LCOK_agree_gb_cfg; [exact HL|]. eapply env_agree_le; [exact Hag | exact Hgb'].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
    injection Hc as <-.
    apply andb_prop in Ht as [Ht Hent]. apply andb_prop in Ht as [Ht Hsv]. apply andb_prop in Ht as [_ Hpc]. apply Z.eqb_eq in Hpc.
    cbn [LCOK_cfg] in HL. destruct HL as [(Hn0 & Hbl & Hlen) HJ].
    destruct (entails_h_sound lo' (nxt js') E cs js' R FULL model HC Hent ltac:(clear -Hn0 Hbl; lia) Hlen) as (E' & Hag & _ & HC' & Hpc').
    assert (Hn0l : (nx0 <= lo')%nat) by lia.
    rewrite (sd_agree D E E' (m_fs model) sk' (env_agree_le nx0 lo' E E' Hag Hn0l) Hsv). rewrite Hpc.
    exact (HJ FP HFP E' R FULL model (env_agree_le _ _ _ _ Hag Hbl) HC' eq_refl).
  - (* [comment removed for export] *)
    destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
    destruct (abstractcell_sound E cs R FULL model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME ak _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocwords_sound E cs R FULL model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT0 hwk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
    destruct (respell_sound E cs R FULL model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME rsk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    eapply (node_mmapin_cfg true FP HFP cs csa csb cscs E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ihb csb s Hc)].
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_brku A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa bua) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb bub) as [sb|] eqn:H2; [|discriminate].
    destruct (shape_eqb (hnorm sa) (hnorm sb)) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse.
    assert (SDE : sd D E (m_fs model) sb = sd D E (m_fs model) sa)
      by (rewrite <- (sd_hnorm D E (m_fs model) sb), <- (sd_hnorm D E (m_fs model) sa), Hse; reflexivity).
    eapply (node_brku_cfg FP HFP cs csa csb E R FULL model);
      [exact HC | exact Hec | exact Hn | exact (CONT bua csa sa H1) | rewrite <- SDE; exact (CONT bub csb sb H2)].
  - (* [comment removed for export] *)
    destruct (node_casedisj_o cs dd1 dd2 ddo) as [[cs1 cs2]|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd_cfg lc D E (m_fs model) HL) as Hgb.
    destruct (run_block_gc SEGS IT _ KC bfuel (ddj :: STOPS A) cs1) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (ddj :: STOPS A) cs2) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) ddj ddrs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (diamond_join_sound (nxt cs) ddj ddrs ca cb csj Hj) as [Ja Jb].
    destruct (casedisj_o_nxt cs dd1 dd2 ddo cs1 cs2 Hn) as [N1 N2].
    destruct (casedisj_o_sound cs dd1 dd2 ddo cs1 cs2 E R FULL model HC Hn) as [[HC1 Hpc1]|[HC2 Hpc2]].
    + rewrite <- Hpc1.
      eapply (run_block_cfg FP HFP); [exact Hgb | exact Hra | exact HC1 |].
      intros E' R' FULL' model' [Hag0 Hag1] HCa Hfs. rewrite N1 in Hag1.
      destruct (Ja E' R' FULL' model' HCa) as (E'' & [Hag2a Hag2b] & HC3 & Hpc3). rewrite <- Hpc3.
      exact (CONT0 ddk csj s Hc E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC3 Hfs).
    + rewrite <- Hpc2.
      eapply (run_block_cfg FP HFP); [exact Hgb | exact Hrb | exact HC2 |].
      intros E' R' FULL' model' [Hag0 Hag1] HCb Hfs. rewrite N2 in Hag1.
      destruct (Jb E' R' FULL' model' HCb) as (E'' & [Hag2a Hag2b] & HC3 & Hpc3). rewrite <- Hpc3.
      exact (CONT0 ddk csj s Hc E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC3 Hfs).
  - (* [comment removed for export] *)
    destruct (node_wordfresh SEGS nx0 cs wfb wfn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (wordfresh_sound E cs R FULL model wfb wfn cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT0 wfk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_casedisj_o cs cx1 cx2 cxo) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa cxk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb cxk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
    destruct (casedisj_o_sound cs cx1 cx2 cxo csa csb E R FULL model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
    + exact (SAME cxk1 _ s1 H1 HC').
    + exact (SAME cxk2 _ s1 H2 HC').
Qed.

End SoundCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RunBlockFP.
Variable SEGS : list Segment.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : nx0_sp_ok nx0.
Variable FS0 : Fs.Fs.
Variable KC : nat.
Context {FP : PropExec.FPState}.

#[local] Abbreviation Mr := (APS.Mr A argH).
#[local] Abbreviation allowA := (APS.allowA A).
#[local] Abbreviation co_halt := (APS.co_halt SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation co_know := (APS.co_know SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation co_minv := (APS.co_minv SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation co_regs := (APS.co_regs SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Abbreviation hid := (APS.hid A argH).
Let A_wf_allowA := APS.A_wf_allowA A HS XN XE XB KC.
Let H_off_segments_cs := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let allowA_agree := APS.allowA_agree A.
Let cs_gc_ok := APS.cs_gc_ok SEGS A LIMIT SINV argH FS0.
Let cs_ok_agree := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let cs_ok_frame := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let env_agree_le := APS.env_agree_le.
Let fresh_ok_mono := APS.fresh_ok_mono nx0.
Let fresh_ok_parts := APS.fresh_ok_parts nx0.
Let hid_agree := APS.hid_agree A nx0 argH argH_agree.
Let kn_vars_lt_eq := APS.kn_vars_lt_eq.
Let lazy_cover_cs := APS.lazy_cover_cs SEGS A LIMIT HS XN XE XB SINV argH FS0 KC.
Let mrestrict_munrestrict_clean := APS.mrestrict_munrestrict_clean.
Let pc_cs_gc := APS.pc_cs_gc.
Let sr_vars_lt_eq := APS.sr_vars_lt_eq.

Lemma run_block_sound_cfg_fp : forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc cs') FULL' model') T) ->
  srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.
Proof.
  intros gb bfuel stops cs cs' E R FULL model T Hgb Hrb HC Hk.
  (* [comment removed for export] *)
  rewrite (run_block_xs _ _ _ _ _ _ _ (fun b1 k1 n1 c m => AxSymExec3SemSound.side_testS_sem _ _ _ _ b1 k1 n1 c m (facts_of_ok _ _ _ _ (co_know _ _ _ _ _ HC)))) in Hrb.
  rewrite run_block_x_eq in Hrb. (* [comment removed for export] *) unfold run_block_ref in Hrb.
  destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
  pose proof (fresh_ok_mono gb cs Hgb Hf0) as Hf.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs _ _ _ _ _ HC) as HR. pose proof (co_know _ _ _ _ _ HC) as HK.
  unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
  cbn [s_know s_regs s_pc s_next] in Hrb, HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  set (ss' := sym_execTX SEGS IT KC bfuel true stops (SS p sr [] k nx)) in Hrb.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  (* [comment removed for export] *)
  set (H := hid E cs model). set (MR := Mr E cs model FULL).
  rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
  pose proof (runTX_sound SEGS IT KC bfuel stops p sr k nx E MR (seg_rom SEGS) R IT_ok HR HK Fsr Fkn) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
  pose proof (cs_ok_agree E E' cs R FULL model Hagc Hf HC) as HC'.
  assert (HH : hid E' cs model = H).
  { unfold H. eapply hid_agree; [exact Hagc | unfold nxt; rewrite Hss; exact Fle | unfold nxt; rewrite Hss; exact Fallow]. }
  unfold cfg_fp, pc. rewrite Hss. cbn [a_ss s_pc].
  apply (srz_cfg_msteps_restricted_T SEGS H (H_off_segments_cs E cs model) SEGS_wx (allowA E cs)
           (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)) _ model T
           (lazy_cover_cs E cs R FULL model HC) (A_wf_allowA E cs) (co_minv _ _ _ _ _ HC) (co_halt _ _ _ _ _ HC) Hms).
  intros model' Hinv' Hsame Hclean.
  assert (HKc : know_ok SEGS E' (mem_denot E' MR (s_log ss')) kn').
  { eapply (carry_sound SEGS E' MR); [exact Hc | exact Hlf | exact HK' | constructor]. }
  set (FULL' := munrestrict H FULL (mem_denot E' MR (s_log ss'))).
  assert (Hmr' : Mr E' cs model FULL' = mem_denot E' MR (s_log ss')).
  { unfold Mr, FULL'. rewrite HH. apply mrestrict_munrestrict_clean. intros a Ha. exact (Hclean a Ha). }
  assert (Flec : (nx0 <= nxt cs)%nat) by (unfold nxt; rewrite Hss; exact Fle).
  assert (Fallowc : pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true) by (unfold nxt; rewrite Hss; exact Fallow).
  specialize (Hk E' R' FULL' model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfg_fp, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
  replace (unrestrict H (ms_mem (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)))
             (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' MR (s_log ss')) (seg_rom SEGS)))
    with (mkst R' (Z_to_bv 64 (s_pc ss')) FULL' (seg_rom SEGS)) by reflexivity.
  apply Hk.
  - eapply cs_ok_frame; [exact HC' | exact Hsame | | exact HR' | reflexivity | | ].
    + rewrite (allowA_agree (nxt cs) E E' cs Hagc Fallowc). exact Hinv'.
    + cbn [mk_ss s_know]. rewrite Hmr'. exact HKc.
    + intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict. rewrite Ha. reflexivity.
  - pose proof (same_but_materialized_frame _ _ Hsame) as Hfr. apply Hfr.
Qed.

Lemma run_block_gc_sound_cfg_fp : forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc cs') FULL' model') T) ->
  srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.
Proof.
  intros gb bfuel stops cs cs' E R FULL model T Hgb H HC Hk. unfold run_block_gc in H.
  destruct (run_block SEGS IT gb KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  eapply run_block_sound_cfg_fp; [exact Hgb | exact Hrb | exact HC |].
  intros E' R' FULL' model' Hag HC1 Hfs. rewrite <- (pc_cs_gc gb cs1). apply (Hk E' R' FULL' model'); [exact Hag | apply cs_gc_ok; exact HC1 | exact Hfs].
Qed.


Lemma run_block_stmt_cfg_here :
  forall gb bfuel stops cs cs' E R FULL model T,
    (nx0 <= gb)%nat ->
    run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@cfg_fp FP SEGS R' (pc cs') FULL' model') T) ->
    srealizes_cfg SEGS (@cfg_fp FP SEGS R (pc cs) FULL model) T.
Proof. exact run_block_gc_sound_cfg_fp. Qed.
End RunBlockFP.

(* [comment removed for export] *)
Theorem run_block_stmt_cfg_all :
  forall SEGS IT (IT_ok : itab_sound SEGS IT) A nx0 LIMIT (HS : nat -> option acs)
    (XN : nat -> list expr -> acs -> option acs) (XE : nat -> list expr -> acs -> option (Z * list spiece * acs))
    (XB : nat -> list expr -> acs -> option (acs * acs))
    (SEGS_wx : wx_segs_nowrap SEGS)
    (SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None)
    (HULL_ok : hull_ok A) SINV argH
    (argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a)
    (argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a)
    (SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M')
    (SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M)
    (NX0_sp : nx0_sp_ok nx0) FS0 KC (FPS : PropExec.FPState -> Prop),
  run_block_stmt_cfg SEGS IT A nx0 LIMIT SINV argH FS0 KC FPS.
Proof.
  intros SEGS IT IT_ok A nx0 LIMIT HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame
    SINV_agree NX0_sp FS0 KC FPS FP _.
  exact (@run_block_stmt_cfg_here SEGS IT IT_ok A nx0 LIMIT HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high
           argH_agree SINV_frame SINV_agree NX0_sp FS0 KC FP).
Qed.
End APSC.
