(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "obj_range"; "pairwise_disjoint"; "eval"; "outside_all"; "cell"; "obj_holds"; "holds"; "smatch"; "sstate"; "ss_objs"; "covered"; "odefault"; "soff"; "tfact"; "ranges_disjoint"; "sfcsr"; "swf"; "agree_below"; "dflt_inv"; "freg_sv"; "in_cell"; "mem_match"; "mkVal"; "ob_base"; "rd"; "rd_bytes"; "reg_sv"; "rl"; "rm"; "tf_expr"; "tf_holds"; "tf_with_expr"; "DArr"; "FcsrFrm0"; "FcsrVal"; "SLit"; "SPAlign"; "SVar"; "c_off"; "c_val"; "c_width"; "mkCell"; "mkObj"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "obj_hi_of"; "obj_lo_of"; "obj_wf"; "rw"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "list"; "option"; "bool"; "app"; "true"; "prod"; "pair"; "Some"; "nat"; "None"; "fst"; "snd"; "@Corelib.Init.Logic"; "eq"; "iff"; "and"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_rom"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "sv_subst"; "rho_sub"; "obj_subst"; "cell_subst"; "wsub_get"; "dflt_subst"; "sprop_subst"; "wsub_id_below"; "tf_subst"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.Fr"; "rho_absorb"; "subst_state"; "in_ranges"; "subst_facts"; "in_ranges_dec"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "branch_cond"; "mulop"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition wsub := list (positive * sv).

Fixpoint wsub_get (s : wsub) (i : positive) : sv :=
  match s with
  | [] => SVar i
  | (j, e) :: t => if Pos.eqb i j then e else wsub_get t i
  end.

Fixpoint sv_subst (s : wsub) (e : sv) : sv :=
  match e with
  | SLit z => SLit z
  | SVar i => wsub_get s i
  | SAlu op a b => mk_alu op (sv_subst s a) (sv_subst s b)
  | SAluW op a b => mk_aluw op (sv_subst s a) (sv_subst s b)
  | SMd op a b => mk_md op (sv_subst s a) (sv_subst s b)
  | SMdW op a b => mk_mdw op (sv_subst s a) (sv_subst s b)
  | SExt sgn w a => mk_ext sgn w (sv_subst s a)
  | SLBytes l i k => SLBytes l (sv_subst s i) k
  end.

Definition rho_sub (rho : valuation) (s : wsub) : valuation := ltac2:(tb__ "0|0|
S1aS52S6Vrho;S5cVs;R1A2A2Li;S1fVrho;A1S20Vrho;A1A3").

Lemma eval_subst : ltac2:(tb__ "0|0|
S2S57S1S4cS61Q40A1S6R3S58R2R1A2A2S6S59R3R2A2R1A2A3Fe;Fs;Frho;").
Proof.
  intros rho s e. induction e; cbn; try reflexivity.
  - rewrite mk_alu_sound, IHe1, IHe2. reflexivity.
  - rewrite mk_aluw_sound, IHe1, IHe2. reflexivity.
  - rewrite mk_md_sound, IHe1, IHe2. reflexivity.
  - rewrite mk_mdw_sound, IHe1, IHe2. reflexivity.
  - rewrite mk_ext_sound, IHe. reflexivity.
  - rewrite IHe. reflexivity.
Qed.

Lemma soff_subst : ltac2:(tb__ "0|0|
S2S57S1S4cS51S10R3S58R2R1A2A2S10S59R3R2A2R1A2A3Fe;Fs;Frho;").
Proof. intros. unfold soff. rewrite eval_subst. reflexivity. Qed.

Definition cell_subst (s : wsub) (c : cell) : cell := ltac2:(tb__ "0|0|
S2dS58Vs;S2aVc;A1A2S2cVc;A1S58Vs;S2bVc;A1A2A3").

Definition tf_subst (s : wsub) (t : tfact) : tfact := ltac2:(tb__ "0|0|
S23Vt;S58Vs;S21Vt;A1A2A2").

Definition dflt_subst (s : wsub) (d : odefault) : odefault := ltac2:(tb__ "0|1|
SfSfLd;Vd;Vd;Vd;Vd;S52Vd;Ll;M0G0S51S1S40S45S51S51A2A1S40S11A1S24R4S58Vs;R3A2R2S64S11S11S60Vs;A1R1A4A4Ltmpl;Lflds;Lcnt;Lesz;Xfx6").

Lemma tf_holds_with_expr : ltac2:(tb__ "0|1|
S2S2S40S61Q40A1M0A1S11S1S4cG0S6R5R1A2S6R4S21R2A1A2A3S4dS22R6R4S23R3R2A2A3S22R5R4R3A3A2F_;Fe;Ft;Fvals;Frho';Frho;").
Proof. intros rho rho' vals t e H. destruct t; cbn in H |- *; rewrite H; tauto. Qed.

Lemma dflt_inv_subst : ltac2:(tb__ "0|0|
S2S57SfS51S51S51S54S4dS16S59R7R6A2R5R4R3R2R1A6S16R7S5dR6R5A2R4R3R2R1A6A2Fms;Fhi;Flo;Fb;Fd;Fs;Frho;").
Proof.
  intros rho s d b lo hi ms. destruct d; cbn [dflt_subst]; try tauto.
  cbn [dflt_inv]. rewrite eval_subst.
  assert (E : forall k, elem_holds (rho_sub rho s) ms (b + lo + esz * k) flds tmpl <-> elem_holds rho ms (b + lo + esz * k) flds (map (tf_subst s) tmpl)).
  { intros k. unfold elem_holds. split; intros (vals & L & F & T); exists vals; (split; [exact L|]); (split; [exact F|]).
    - apply Forall_map. apply Forall_forall. intros t Hin. apply (proj2 (tf_holds_with_expr rho (rho_sub rho s) vals t _ (eval_subst rho s (tf_expr t)))).
      exact (proj1 (Forall_forall _ _) T t Hin).
    - apply Forall_forall. intros t Hin.
      apply (proj1 (tf_holds_with_expr rho (rho_sub rho s) vals t _ (eval_subst rho s (tf_expr t)))).
      apply (proj1 (Forall_forall _ _) T (tf_subst s t)). apply in_map. exact Hin. }
  split; intros (A & B & C & D); (split; [exact A|]); (split; [exact B|]); (split; [exact C|]); intros k Hk; apply E; apply D; exact Hk.
Qed.

Definition obj_subst (s : wsub) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S2eS58Vs;S1bVo;A1A2S58Vs;S33Vo;A1A2S58Vs;S32Vo;A1A2S64S8S8S5bVs;A1S30Vo;A1A4S5dVs;S31Vo;A1A2A5").

Fixpoint sprop_subst (s : wsub) (p : sprop) : option sprop :=
  match p with
  | SPBranch c a b => Some (SPBranch c (sv_subst s a) (sv_subst s b))
  | SPNot q => match sprop_subst s q with Some q' => Some (SPNot q') | None => None end
  | SPUlt a b => Some (SPUlt (sv_subst s a) (sv_subst s b))
  | SPUle a b => Some (SPUle (sv_subst s a) (sv_subst s b))
  | SPEq a b => Some (SPEq (sv_subst s a) (sv_subst s b))
  | SPTrue => Some SPTrue
  | SPAlign _ _ => None
  end.

Lemma sprop_subst_sound : ltac2:(tb__ "0|0|
S2S57S3S3S4cS41S3A1S5eR3R2A2S47S3R1A2A3S4dSaR5R2A2SaS59R5R4A2R3A2A2F_;Fp';Fp;Fs;Frho;").
Proof.
  intros rho s p. induction p; intros p' H; cbn in H; try discriminate;
    try (injection H as <-; cbn; rewrite ?eval_subst; tauto).
  destruct (sprop_subst s p) as [q|] eqn:Hq; [|discriminate].
  injection H as <-. cbn. specialize (IHp q eq_refl). tauto.
Qed.

Definition wsub_id_below (s : wsub) (g : positive) : bool := ltac2:(tb__ "0|1|
S6fS45S52S1A2M0G0S7eVg;S4aS52S1R1A3A2Lje;Vs;A3").

Lemma wsub_get_id : ltac2:(tb__ "0|0|
S57S52S52S4cS42S5fR3R2A2S44A3S7fR2R3A2S4cS1S5cR5R3A2S29R3A1A3F_;F_;Fi;Fg;Fs;").
Proof.
  induction s as [|[j e] t IH]; intros g i H Hi; cbn; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. apply Pos.leb_le in H1.
  destruct (Pos.eqb_spec i j) as [->|Hne]; [lia|]. eapply IH; eauto.
Qed.

Lemma rho_sub_agree : ltac2:(tb__ "0|0|
S57S52S2S4cS42S5fR3R2A2S44A3S15R3R2S59R2R4A2A3F_;Frho;Fg;Fs;").
Proof.
  intros s g rho H. repeat split; intros; cbn; try reflexivity.
  rewrite (wsub_get_id s g i H) by assumption. reflexivity.
Qed.

Lemma in_cell_subst : ltac2:(tb__ "0|0|
S2S57S51S8S4dS18R4R2S5bR3R1A2A3S18S59R4R3A2R2R1A3A2Fc;Foff;Fs;Frho;").
Proof. intros. unfold in_cell, cell_subst. cbn [c_off c_width]. rewrite soff_subst. tauto. Qed.

Lemma covered_subst : ltac2:(tb__ "0|0|
S2S57S40S8A1S51S4dSeR4S64S8S8S5bR3A1R2A4R1A3SeS59R4R3A2R2R1A3A2Foff;Fcells;Fs;Frho;").
Proof.
  intros rho s cells off. unfold covered. rewrite !Exists_exists. split.
  - intros (c & Hin & Hc). apply in_map_iff in Hin as (c0 & <- & Hin0).
    exists c0. split; [exact Hin0|]. apply in_cell_subst. exact Hc.
  - intros (c & Hin & Hc). exists (cell_subst s c). split; [apply in_map; exact Hin|].
    apply in_cell_subst. exact Hc.
Qed.

Section Fr.
Variable segs : list Segment.

Lemma obj_holds_subst : ltac2:(tb__ "0|0|
S2S57S54S0S9Vsegs;S59R4R3A2R2R1A4S9Vsegs;R5R3S5aR4R2A2A4F_;Fo;Fms;Fs;Frho;").
Proof using .
  intros rho s ms o (Hb & Hw & Hc & Hd & Hdl).
  unfold obj_holds, obj_subst, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  rewrite eval_subst, !soff_subst. split; [exact Hb|]. split; [|split; [|split]].
  - intros off Hoff Hdw. apply Hw; [exact Hoff|]. revert Hdw. destruct (ob_dflt o); cbn; intros Hdw; exact Hdw.
  - apply Forall_forall. intros c Hin. apply in_map_iff in Hin as (c0 & <- & Hin0).
    pose proof (proj1 (Forall_forall _ _) Hc c0 Hin0) as H. unfold cell_holds in *.
    cbn [cell_subst c_off c_width c_val]. unfold oaddr in *. rewrite !eval_subst, !soff_subst. exact H.
  - intros off Hoff Hcov. rewrite covered_subst in Hcov. specialize (Hd off Hoff Hcov).
    destruct (ob_dflt o); cbn in *; exact Hd.
  - apply dflt_inv_subst. exact Hdl.
Qed.

Lemma obj_range_subst : ltac2:(tb__ "0|0|
S2S57S0S4cS45S51S51A2S4R3S5aR2R1A2A2S4S59R3R2A2R1A2A3Fo;Fs;Frho;").
Proof using .
  intros. unfold obj_range, obj_subst, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite eval_subst, !soff_subst. reflexivity.
Qed.

Lemma pairwise_disjoint_subst : ltac2:(tb__ "0|0|
S2S57S40S0A1S5S59R3R2A2R1A2S5R4S64S0S0S5aR3A1R2A4A2F_;Fobjs;Fs;Frho;").
Proof using .
  intros rho s objs. induction objs as [|o t IH]; cbn; [tauto|].
  intros [Hf Hp]. split; [|apply IH; exact Hp].
  apply Forall_forall. intros o' Hin. apply in_map_iff in Hin as (o0 & <- & Hin0).
  rewrite !obj_range_subst. exact (proj1 (Forall_forall _ _) Hf o0 Hin0).
Qed.

Lemma outside_all_subst : ltac2:(tb__ "0|0|
S2S57S40S0A1S61Q40A1S4dS7R4S64S0S0S5aR3A1R2A4R1A3S7S59R4R3A2R2R1A3A2Fa;Fobjs;Fs;Frho;").
Proof using .
  intros rho s objs a. unfold outside_all. rewrite Forall_map.
  split; intros H; apply Forall_forall; intros o Hin;
    pose proof (proj1 (Forall_forall _ _) H o Hin) as X; cbn beta in X |- *;
    [rewrite obj_range_subst in X | rewrite obj_range_subst]; exact X.
Qed.

Lemma mem_match_subst : ltac2:(tb__ "0|0|
S2S57S40S0A1S54S19Vsegs;S59R4R3A2R2R1A4S19Vsegs;R5S64S0S0S5aR4A1R3A4R2A4F_;Fms;Fobjs;Fs;Frho;").
Proof using .
  intros rho s objs ms (Hall & Hpd & Hfr). split; [|split].
  - apply Forall_forall. intros o Hin. apply in_map_iff in Hin as (o0 & <- & Hin0).
    apply obj_holds_subst. exact (proj1 (Forall_forall _ _) Hall o0 Hin0).
  - apply pairwise_disjoint_subst. exact Hpd.
  - intros a Ha. apply Hfr. apply outside_all_subst. exact Ha.
Qed.

Definition sprop_subst_opt (s : wsub) (p : sprop) : option sprop := ltac2:(tb__ "0|7|
S3S41S3A1M0Lp;Vp;S7bS1S1S5eVs;Vp;A2M1Lb;La;M2Lc;S3G1Lp0;G2G2G2G1S52S51S1G0Lx;S5cVs;R2A2S51S49S3A1M3Lz;S52S47S3S28R1R2A2A2Lj;S7aS1S1G3Lb;La0;M4Lop;M5G5S7cG4Lop;M6G6S42S53S1G3La0;Lw;Lsgn;S52S1S51G3Lk;Li0;Ll;X1x8La;Li;X3x7").

Fixpoint subst_facts (s : wsub) (facts : list sprop) : list sprop :=
  match facts with
  | [] => []
  | p :: rest => match sprop_subst_opt s p with
                 | Some p' => p' :: subst_facts s rest
                 | None => subst_facts s rest
                 end
  end.

Definition subst_state (s : wsub) (S : sstate) (nx : positive) : sstate := ltac2:(tb__ "0|3|
S2fS3dVS;A1S64S1S1S58Vs;A1M0S3eVS;A1A4S64S1S1G0S3aVS;A1A4S13S13Lx;S39VS;A1S25S1S26S58Vs;R1A2M1A1Lv;X13x2S41S1A1M2G2Lx;S3fVS;A1S1S47S1G1A2Lv;S49S1A1X41x2S64S0S0S5aVs;A1SdVS;A1A4S6aVs;S38VS;A1A2Vnx;S3bVS;A1A9").

Lemma nth_map_sv_subst : ltac2:(tb__ "0|1|
S57S40S1A1S48S4cS1S66S1R1S64S1S1S58R3A1R2A4S27Z0A1M0A4S58R3S66S1R1R2G0A4A2A3Fn;Fl;Fs;").
Proof using .
  intros s l. induction l as [|x t IH]; intros n; destruct n; cbn; try reflexivity. apply IH.
Qed.

Lemma reg_sv_subst_state : ltac2:(tb__ "0|0|
S57ScS52S51S4cS1S1eS68R4R3R2A3R1A2S58R4S1eR3R1A2A2A3Fr;Fnx;FS;Fs;").
Proof using .
  intros s S nx r. unfold reg_sv. cbn [ss_regs subst_state].
  destruct (r =? 0); [reflexivity|]. apply nth_map_sv_subst.
Qed.

Lemma freg_sv_subst_state : ltac2:(tb__ "0|0|
S57ScS52S51S4cS1S17S68R4R3R2A3R1A2S58R4S17R3R1A2A2A3Fr;Fnx;FS;Fs;").
Proof using . intros. unfold freg_sv. cbn [ss_fregs subst_state]. apply nth_map_sv_subst. Qed.

Lemma subst_facts_sound : ltac2:(tb__ "0|0|
S2S57S40S3A1S65S3SaS59R3R2A2A1R1A3S65S3SaR4A1S6aR3R2A2A3F_;Ffacts;Fs;Frho;").
Proof using .
  intros rho s facts H. induction facts as [|p rest IH]; cbn; [constructor|].
  inversion H as [|p' rest' Hp Hrest]; subst.
  destruct (sprop_subst_opt s p) as [p'|] eqn:E; [|apply IH; exact Hrest].
  constructor; [|apply IH; exact Hrest].
  unfold sprop_subst_opt in E. destruct p;
    try (apply (sprop_subst_sound rho s _ p' E); exact Hp).
  destruct (wsub_get s i) eqn:Eg; try discriminate. injection E as <-.
  cbn in Hp |- *. rewrite Eg in Hp. cbn in Hp. exact Hp.
Qed.

Lemma smatch_subst_intro : ltac2:(tb__ "0|0|
S2S57ScS52S45S40S71A1S6cA2S4cS42S14S68R4R3R2A3A1S44A3SbVsegs;S59R6R5A2R4R2A4SbVsegs;R7S68R6R5R4A3R3A4F_;F_;Fw;Fnx;FS;Fs;Frho;").
Proof using .
  intros rho s S nx [tr [ms md]] Hwf Hsm.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hroc|].
  split. { intros r Hr. rewrite reg_sv_subst_state, eval_subst. apply Hregs. exact Hr. }
  split. { intros r. rewrite freg_sv_subst_state, eval_subst. apply Hfregs. }
  split. { cbn [ss_fcsr subst_state]. destruct (ss_fcsr S); cbn in *; [exact Hfcsr|]. rewrite eval_subst. exact Hfcsr. }
  split. { cbn [ss_resv subst_state]. unfold resv_match in *. destruct (ss_resv S); destruct (ms_resv ms); try exact Hresv.
           rewrite eval_subst. exact Hresv. }
  split. { cbn [ss_objs subst_state]. apply mem_match_subst. exact Hmem. }
  cbn [ss_facts subst_state]. apply subst_facts_sound. exact Hfacts.
Qed.

Definition in_ranges (rho : valuation) (R : list sobj) (a : word) : Prop := ltac2:(tb__ "0|2|
S50S0S0S4eS6eS0R1VR;A3S4eS75S4aS51S51S4Vrho;R1A2M0A3S62Q40Va;A2M1A2S76G1S4bS51S51G0A3A2A2A2Lo;A2").

Lemma in_ranges_dec : ltac2:(tb__ "0|1|
S2S40S0A1S61Q40A1S70S69R3R2R1A3M0S4fG0A1A2Fa;FR;Frho;").
Proof.
  intros rho R a. induction R as [|o t IH].
  - right. intros (o & Hin & _). exact Hin.
  - destruct (Z_le_dec (fst (obj_range rho o)) (bv_unsigned a)), (Z_lt_dec (bv_unsigned a) (snd (obj_range rho o))).
    + left. exists o. split; [left; reflexivity | lia].
    + destruct IH as [IH|IH]; [left | right].
      * destruct IH as (o' & Hin & H). exists o'. split; [right; exact Hin | exact H].
      * intros (o' & [<-|Hin] & H); [lia|]. apply IH. exists o'. auto.
    + destruct IH as [IH|IH]; [left | right].
      * destruct IH as (o' & Hin & H). exists o'. split; [right; exact Hin | exact H].
      * intros (o' & [<-|Hin] & H); [lia|]. apply IH. exists o'. auto.
    + destruct IH as [IH|IH]; [left | right].
      * destruct IH as (o' & Hin & H). exists o'. split; [right; exact Hin | exact H].
      * intros (o' & [<-|Hin] & H); [lia|]. apply IH. exists o'. auto.
Defined.

Definition rho_absorb (rho : valuation) (R : list sobj) (ms : machine_state) : valuation := ltac2:(tb__ "0|2|
S1aS37Vrho;A1S1fVrho;A1S61Q40A1S70S69Vrho;VR;R1A3M0S4fG0A1M1A2S41S61Q8A1A1L_;S6bVrho;VR;R1A3G0S56Vms;R2A2L_;G1S20Vrho;R2A2L_;X70x2La;A3").

Lemma eval_absorb : ltac2:(tb__ "0|0|
S2S40S0A1S54S1S4cS61Q40A1S6S67R4R3R2A3R1A2S6R4R1A2A3Fe;Fms;FR;Frho;").
Proof using . intros rho R ms e. induction e; cbn; try rewrite ?IHe1, ?IHe2, ?IHe; reflexivity. Qed.

Lemma soff_absorb : ltac2:(tb__ "0|0|
S2S40S0A1S54S1S4cS51S10S67R4R3R2A3R1A2S10R4R1A2A3Fe;Fms;FR;Frho;").
Proof using . intros. unfold soff. rewrite eval_absorb. reflexivity. Qed.

Lemma holds_absorb : ltac2:(tb__ "0|0|
S2S40S0A1S54S3S4dSaS67R4R3R2A3R1A2SaR4R1A2A2Fp;Fms;FR;Frho;").
Proof using . intros rho R ms p. induction p; cbn; rewrite ?eval_absorb; try tauto. Qed.

Lemma obj_range_absorb : ltac2:(tb__ "0|0|
S2S40S0A1S54S0S4cS45S51S51A2S4S67R4R3R2A3R1A2S4R4R1A2A3Fo;Fms;FR;Frho;").
Proof using . intros. unfold obj_range, obj_lo_of, obj_hi_of. rewrite eval_absorb, !soff_absorb. reflexivity. Qed.

Lemma covered_absorb : ltac2:(tb__ "0|0|
S2S40S0A1S54S40S8A1S51S4dSeS67R5R4R3A3R2R1A3SeR5R2R1A3A2Foff;Fcells;Fms;FR;Frho;").
Proof using .
  intros. unfold covered. rewrite !Exists_exists. unfold in_cell.
  split; intros (c & Hin & Hc); exists c; split; auto; revert Hc; rewrite !soff_absorb; tauto.
Qed.

Lemma obj_holds_absorb : ltac2:(tb__ "0|0|
S2S40S0A1S54S54S0S9Vsegs;R5R2R1A4S9Vsegs;S67R6R5R4A3R3R2A4F_;Fo;Fms1;Fms;FR;Frho;").
Proof using .
  intros rho R ms ms1 o (Hb & Hw & Hc & Hd & Hdl). unfold obj_holds, obj_lo_of, obj_hi_of in *.
  rewrite eval_absorb, !soff_absorb.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split].
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as H.
    unfold cell_holds, oaddr in *. rewrite !eval_absorb, !soff_absorb. exact H.
  - intros off Hoff Hcov. rewrite covered_absorb in Hcov. specialize (Hd off Hoff Hcov).
    destruct (ob_dflt o); cbn in *; exact Hd.
  - eapply dflt_inv_exprs; [| | exact Hdl]; [intros; reflexivity|].
    destruct (ob_dflt o); try exact I. split; [symmetry; apply eval_absorb|].
    apply Forall_forall. intros t _. symmetry. apply eval_absorb.
Qed.

Lemma pairwise_disjoint_absorb : ltac2:(tb__ "0|1|
S2S40S0A1M0S54G0S5R4R1A2S5S67R5R4R3A3R2A2F_;Fobjs;Fms;FR;Frho;").
Proof using .
  intros rho R ms objs. induction objs as [|o t IH]; cbn; [tauto|]. intros [Hf Hp]. split; [|apply IH; exact Hp].
  apply Forall_forall. intros o' Hin. rewrite !obj_range_absorb. exact (proj1 (Forall_forall _ _) Hf o' Hin).
Qed.

Lemma outside_all_absorb : ltac2:(tb__ "0|1|
S2S40S0A1M0S54G0S61Q40A1S4dS7S67R5R4R3A3R2R1A3S7R5R2R1A3A2Fa;Fobjs;Fms;FR;Frho;").
Proof using .
  intros. unfold outside_all. split; intros H; apply Forall_forall; intros o Hin;
    pose proof (proj1 (Forall_forall _ _) H o Hin) as X; cbn beta in X |- *;
    [rewrite obj_range_absorb in X | rewrite obj_range_absorb]; exact X.
Qed.

Lemma outside_all_app_iff : ltac2:(tb__ "0|1|
S2S40S0A1M0G0S61Q40A1S4dS7R4S43S0R3R2A3R1A3S4eS7R4R3R1A3S7R4R2R1A3A2A2Fa;Fl2;Fl1;Frho;").
Proof using . intros. unfold outside_all. rewrite Forall_app. tauto. Qed.

Lemma outside_not_in_ranges : ltac2:(tb__ "0|0|
S2S40S0A1S61Q40A1S7R3R2R1A3S4fS69R4R3R2A3A1F_;Fa;FR;Frho;").
Proof using .
  intros rho R a H (o & Hin & Hr). pose proof (proj1 (Forall_forall _ _) H o Hin) as X.
  cbn beta in X. apply X. exact Hr.
Qed.

Lemma pairwise_disjoint_app_inv : ltac2:(tb__ "0|2|
S2S40S0A1M0G0S5R3S43S0R2R1A3A2S4eS5R4R3A2S4eS5R4R2A2S0S0S6eS0R2R5A3M1G1S12S4R8R4A2S4R8R3A2A2F_;F_;Fo2;Fo1;A2A2F_;Fl2;Fl1;Frho;").
Proof using .
  intros rho l1 l2. induction l1 as [|o t IH]; cbn; intros H.
  - split; [exact I|]. split; [exact H|]. intros o1 o2 [].
  - destruct H as [Hf Hp]. apply Forall_app in Hf as [Hf1 Hf2].
    destruct (IH Hp) as (P1 & P2 & X). split; [split; [exact Hf1 | exact P1]|]. split; [exact P2|].
    intros o1 o2 [<-|Hin1] Hin2.
    + exact (proj1 (Forall_forall _ _) Hf2 o2 Hin2).
    + apply X; assumption.
Qed.

Lemma swf_drop_objs : ltac2:(tb__ "0|1|
ScS40S0A1M0G0S4cG0SdR3A1S43S0R2R1A3A3S4cS42S14R4A1S44A3S4cS42S14S73R5R4A2A1S44A3F_;F_;FR;Fobjs;FS;").
Proof using .
  intros S objs R Ho Hwf. pose proof Hwf as W. unfold swf in W |- *. unfold set_objs.
  cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next]. rewrite Ho in W.
  repeat (apply andb_prop in W; destruct W as [W ?]).
  repeat (apply andb_true_intro; split); try assumption.
  rewrite forallb_app in H0. apply andb_prop in H0 as [H0 _]. exact H0.
Qed.

Lemma smatch_frame_in : ltac2:(tb__ "0|2|
S2ScS40S0A1M0G0S40S71A1M1S54S72S4cG0SdR6A1S43S0R5R4A3A3SbVsegs;R8R7S46G1S6cR4S6dR3R2A2A4A4SbVsegs;S67R9R6R4A3S73R8R7A2S46G1S6cR5S6dR4R3A2A4A4F_;F_;Fmd;Fms;Ftr;FR;Fobjs;FS;Frho;").
Proof using .
  intros rho S objs R tr ms md Ho Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [eapply swf_drop_objs; eauto|].
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [intros r Hr; rewrite eval_absorb; apply Hregs; exact Hr|].
  split; [intros r; rewrite eval_absorb; apply Hfregs|].
  split; [destruct (ss_fcsr S); cbn in *; rewrite ?eval_absorb; exact Hfcsr|].
  split; [unfold resv_match in *; destruct (ss_resv S); destruct (ms_resv ms); rewrite ?eval_absorb; exact Hresv|].
  split.
  - rewrite Ho in Hmem. destruct Hmem as (Hall & Hpd & Hfr).
    apply Forall_app in Hall as [Hall1 Hall2]. apply pairwise_disjoint_app_inv in Hpd as (Hpd1 & Hpd2 & Hx).
    split; [apply Forall_forall; intros o Hin; apply obj_holds_absorb; exact (proj1 (Forall_forall _ _) Hall1 o Hin)|].
    split; [apply pairwise_disjoint_absorb; exact Hpd1|].
    intros a Ha. apply outside_all_absorb in Ha. unfold rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho R a) as [Hin|Hnin]; [reflexivity|].
    apply Hfr. apply outside_all_app_iff. split; [exact Ha|].
    apply Forall_forall. intros o Hino. lazy beta zeta. intros Hrng. apply Hnin. exists o. auto.
  - apply Forall_forall. intros p Hp. apply holds_absorb. exact (proj1 (Forall_forall _ _) Hfacts p Hp).
Qed.

Lemma pairwise_disjoint_app : ltac2:(tb__ "0|2|
S2S40S0A1M0G0S5R3R2A2S5R4R2A2S0S0S6eS0R2R6A3M1G1S12S4R9R4A2S4R9R3A2A2F_;F_;Fo2;Fo1;S5R6S43S0R5R4A3A2F_;F_;F_;Fl2;Fl1;Frho;").
Proof using .
  intros rho l1 l2. induction l1 as [|o t IH]; cbn; intros H1 H2 Hx; [exact H2|].
  destruct H1 as [Hf Hp]. split.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros o2 Hin2. apply Hx; [left; reflexivity | exact Hin2].
  - apply IH; [exact Hp | exact H2 |]. intros o1 o2 Hin1 Hin2. apply Hx; [right; exact Hin1 | exact Hin2].
Qed.

Lemma rd_mem_ext : ltac2:(tb__ "0|2|
S54S54S61Q40A1M0S4cS41S61Q8A1A1M1S56R2R1A2S56R3R1A2A3G0S4cG1S55R4R1A2S55R5R1A2A3Fa;S4cG1S1cR4R3A2S1cR5R3A2A3F_;F_;Fx;Fms';Fms;").
Proof using . intros ms ms' x Hm Hr. unfold rd, ms_read_byte. rewrite Hm, Hr. reflexivity. Qed.

Lemma rd_bytes_mem_ext : ltac2:(tb__ "0|5|
S54S54S48S61Q40M0A1M1G1S4cS41S61Q8A1M2A1M3S55R4R1A2S55R5R1A2A3Fx;S75S74S62G0R2A2S77R3A1A2S78Z2Z40A2A2S48S79R1R5A2S4cG3S56R7S63G0S74S62G0R5A2S77R2A1A2A2M4A2S56R8G4A2A3F_;Fj;S4cS41S40G2A1A1S1dR6R4R5A3S1dR7R4R5A3A3F_;F_;F_;Fa;Fk;Fms';Fms;").
Proof using .
  intros ms ms' k. induction k as [|k IH]; intros a Hr Hnw Hsame; [reflexivity|].
  cbn [rd_bytes]. rewrite Nat2Z.inj_succ in Hnw.
  pose proof (Hsame 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
  rewrite (rd_mem_ext ms ms' a H0 Hr).
  destruct k as [|k']; [reflexivity|].
  rewrite (IH (a + 1)%bv Hr).
  - reflexivity.
  - rewrite u_add1; lia.
  - intros j Hj. rewrite u_add1 by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hsame. lia.
Qed.

Lemma obj_holds_mem_ext : ltac2:(tb__ "0|3|
S2S54S54S0S61Q40M0A1S4cS41S61Q8A1A1M1S55R3R1A2S55R4R1A2A3Fa;S51S4eS75S35R6R3A2R1A2S76R1S34R6R3A2A2A2S4cG1S56R5S63G0S74S62G0S6R7S1bR4A1A2A2R2A2A2M2A2S56R6G2A2A3F_;Foff;S9Vsegs;R6R5R3A4S9Vsegs;R7R5R4A4F_;F_;F_;Fo;Fms';Fms;Frho;").
Proof using .
  intros rho ms ms' o Hr Hsame (Hb & Hw & Hc & Hd & Hdl).
  split; [exact Hb|]. split.
  { intros off' Hoff'. unfold wview. rewrite Hsame by exact Hoff'. apply Hw. exact Hoff'. }
  split.
  { apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (C1 & C2 & C3).
    split; [exact C1|]. split; [exact C2|]. rewrite <- C3.
    destruct (Z.to_nat (c_width c)) as [|k'] eqn:Ek; [reflexivity|].
    assert (Hw' : c_width c = Z.of_nat (S k')) by lia.
    unfold obj_lo_of, obj_hi_of in *.
    apply rd_bytes_mem_ext; [exact Hr | |].
    - rewrite oaddr_unsigned by lia. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. rewrite <- Z.add_assoc. apply Hsame. lia. }
  split.
  2:{ destruct (ob_dflt o); cbn in Hdl |- *; try exact Hdl.
      destruct Hdl as (He & Hf & Hfit & Hall). split; [exact He|]. split; [exact Hf|]. split; [exact Hfit|].
      intros k Hk. apply (elem_holds_rd_ext rho ms ms'); [|exact (Hall k Hk)].
      intros i f Hi. pose proof (proj1 (Forall_forall _ _) Hf f (nth_error_In _ _ Hi)) as (F0 & F1 & F2).
      pose proof (urange (eval rho cnt)) as Hcu.
      assert (Hel : esz * k + esz <= esz * bv_unsigned (eval rho cnt)) by (rewrite <- Z.mul_succ_r; apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hkn : 0 <= esz * k) by (apply Z.mul_nonneg_nonneg; lia).
      unfold obj_lo_of, obj_hi_of in *.
      apply rd_bytes_mem_ext; [exact Hr | |].
      - rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). rewrite Z2Nat.id by lia. lia.
      - intros j Hj. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia).
        replace (bv_unsigned (eval rho (ob_base o)) + soff rho (ob_lo o) + esz * k + fst f + Z.of_nat j)
          with (bv_unsigned (eval rho (ob_base o)) + (soff rho (ob_lo o) + esz * k + fst f + Z.of_nat j)) by lia.
        apply Hsame. lia. }
  intros off' Hoff' Hcov. specialize (Hd off' Hoff' Hcov).
  destruct (ob_dflt o); cbn in Hd |- *.
  - destruct Hd as [b Hbb]. exists b. rewrite (rd_mem_ext ms ms'); [exact Hbb | apply Hsame; lia | exact Hr].
  - rewrite (rd_mem_ext ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - destruct Hd as [Hnone Hib]. split; [|exact Hib]. rewrite Hsame by lia. exact Hnone.
  - rewrite (rd_mem_ext ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - rewrite (rd_mem_ext ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - destruct Hd as [b Hbb]. exists b. rewrite (rd_mem_ext ms ms'); [exact Hbb | apply Hsame; lia | exact Hr].
Qed.

Lemma smatch_frame_out : ltac2:(tb__ "0|1|
S2S2S40S0A1S52ScS54S40S71A1M0S54S72S65S0S9Vsegs;R9R4A3R7A3S5RaR8A2S4cS42S6fS0S36R8A1R9A3S44A3S15R9S67RcRaR7A3RbA3S7dRaS3cR9A1A2S61Q40A1S4cS41S61Q8A1A1S55R8R1A2S55RaR1A2A3Fa;SbVsegs;ReRbS46G0S6cR9S6dR8R7A2A4A4S0S0S6eS0R2SdReA1A3S6eS0R2R11A3S12S4R13R4A2S4R14R3A2A2F_;F_;FoR;Fo';SbVsegs;R10S73RdS43S0SdRdA1RfA3A2S46G0S6cRbS6dRaR9A2A4A4F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';Fms;FS';Fn;FR;Frho1;Frho;").
Proof using .
  intros rho rho1 R n S' ms tr' ms' md' HR Hpd Hwf Hag Hle Hrom' Hsm' Hdisj.
  pose proof (smatch_swf segs _ _ _ Hsm') as Hwf'.
  destruct Hsm' as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hmem as (Hall & Hpd' & Hfr).
  assert (RNG : forall oR, In oR R -> obj_range rho1 oR = obj_range rho oR).
  { intros oR Hin. rewrite <- (obj_range_absorb rho R ms oR).
    apply (obj_range_agree n). exact Hag. exact (proj1 (forallb_forall _ _) Hwf oR Hin). }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { pose proof Hwf' as W. unfold swf in W |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    repeat (apply andb_prop in W; destruct W as [W ?]).
    repeat (apply andb_true_intro; split); try assumption.
    apply forallb_forall. intros o Hin. apply in_app_or in Hin as [Hin|Hin].
    - revert o Hin. apply forallb_forall. assumption.
    - apply (obj_wf_mono n); [exact Hle|]. exact (proj1 (forallb_forall _ _) Hwf o Hin). }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  split; [|split].
  - apply Forall_app. split; [exact Hall|].
    apply Forall_forall. intros oR Hin.
    pose proof (proj1 (Forall_forall _ _) HR oR Hin) as HoR.
    pose proof (proj1 (forallb_forall _ _) Hwf oR Hin) as HwfR.
    apply (obj_holds_absorb rho R ms) in HoR.
    apply (obj_holds_agree segs n _ rho1) in HoR; [| exact Hag | exact HwfR].
    eapply (obj_holds_mem_ext rho1 ms ms'); [exact Hrom' | | exact HoR].
    intros off Hoff.
    rewrite Hfr.
    + destruct Hag as (_ & _ & C). rewrite <- C. unfold rho_absorb. cbn [rm].
      destruct (in_ranges_dec rho R _) as [Hi|Hn]; [reflexivity|].
      exfalso. apply Hn. exists oR. split; [exact Hin|].
      rewrite <- (RNG oR Hin). unfold obj_range. cbn [fst snd].
      pose proof (proj1 HoR) as HB. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia.
    + apply Forall_forall. intros o' Hin'. lazy beta zeta. intros Hr.
      pose proof (Hdisj o' oR Hin' Hin) as D. rewrite <- (RNG oR Hin) in D.
      unfold ranges_disjoint, obj_range in D. cbn [fst snd] in D.
      unfold obj_range in Hr. cbn [fst snd] in Hr.
      pose proof (proj1 HoR) as HB. rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia). lia.
  - apply pairwise_disjoint_app; [exact Hpd' | |].
    + apply (pairwise_disjoint_agree n (rho_absorb rho R ms)); [exact Hag | exact Hwf |].
      apply pairwise_disjoint_absorb. exact Hpd.
    + intros o1 o2 Hin1 Hin2. rewrite (RNG o2 Hin2). apply Hdisj; assumption.
  - intros a Ha. apply Hfr. apply outside_all_app_iff in Ha as [Ha _]. exact Ha.
Qed.

End Fr.
