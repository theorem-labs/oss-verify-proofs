(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheckG HBArg HBChain HBUsageDefs HBHop HBParity HBSel
  BVT012Se BVT012SeEq BVT012Lit BNTeFE BNTeFEE BNTecFE BNTecFEE BNTesFE BNTesFEE BNTeDrvz BNTeDrvs BNTeDrvp BNTeDrvw1 BNTeDrvw2 BNTeDrvv BNTeDrvw6 BNTeDrvw10 BNTeDrvgn BNTeDrvgc BNTeDrvgs BNTeDrvw19.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition PALL (E : env) : Prop := True.
Lemma PALL_agree : forall E E', env_agree NX0 E E' -> PALL E -> PALL E'. Proof. intros; exact I. Qed.
Lemma cover : forall E, 0 <= nb_of E <= 65529 -> PALL E. Proof. intros; exact I. Qed.
Definition T0 (E : env) (fs' : Fs.Fs) : TSet := TGT (nb_of E <? 11) (calls_of E) (cnt_of E) fs'.
Lemma closed_agree : forall e E E', expr_vars_lt 0 e = true -> env_agree NX0 E E' -> uE E e = uE E' e.
Proof. intros e E E' He Hag. unfold uE. rewrite (edenot_agree' 0 E E' e); [reflexivity | | exact He]. destruct Hag as [_ Hb]. split; [intros n Hn; lia | exact Hb]. Qed.
Lemma nb_agree : forall E E', env_agree NX0 E E' -> nb_of E = nb_of E'.
Proof. intros E E' Hag. unfold nb_of, cl_of. rewrite (closed_agree e_cl E E' eq_refl Hag). destruct Hag as [_ Hb]. rewrite Hb. reflexivity. Qed.
Lemma T0_agree : t_agree T0.
Proof.
  intros E E' fs0 Hag. unfold T0, calls_of, cnt_of, cl_of. rewrite (nb_agree E E' Hag), (closed_agree e_cl E E' eq_refl Hag), (closed_agree e_cm E E' eq_refl Hag), (closed_agree e_b1s E E' eq_refl Hag). reflexivity.
Qed.
Lemma T0_nil : forall E fs0, T0 E fs0 [].
Proof. intros E fs0. unfold T0, TGT. apply t_emit_has_nil. Qed.
Section Tail.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  Hypothesis H_FE : fx_hole SV argH ISP fs nte_tfe ntefee.
  Hypothesis H_FEc : fx_hole SV argH ISP fs ntec_tfe ntecfee.
  Hypothesis H_FEs : fx_hole SV argH ISP fs ntes_tfe ntesfee.
  Lemma tail_t012e_lit : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs vt012se T0.
  Proof.
    intros PHIb E R FULL m HC.
    pose proof (nb_range sp rdraw argv envp uid hw fs SV BNTeDrvz.BASE BNTeDrvz.HKN PHIb E R FULL m HC) as Hr.
    unfold T0.
    destruct (Z_le_gt_dec (nb_of E) 0) as [H0|H0]; [replace (nb_of E <? 11) with true by (symmetry; apply Z.ltb_lt; lia); exact (BNTeDrvz.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 10) as [H1|H1]; [replace (nb_of E <? 11) with true by (symmetry; apply Z.ltb_lt; lia); exact (BNTeDrvs.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 15) as [H2|H2]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvp.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 16) as [H3|H3]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvw1.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 48) as [H4|H4]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvw2.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 64) as [H5|H5]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvv.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 96) as [H6|H6]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgn.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 128) as [H7|H7]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvw6.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 224) as [H8|H8]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 256) as [H9|H9]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvw10.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 288) as [H10|H10]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgn.drive1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 352) as [H11|H11]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 384) as [H12|H12]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgn.drive2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 448) as [H13|H13]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 640) as [H14|H14]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgn.drive3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 896) as [H15|H15]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 1408) as [H16|H16]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvw19.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 1920) as [H17|H17]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 2944) as [H18|H18]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgn.drive4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 3968) as [H19|H19]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 12032) as [H20|H20]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgn.drive5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 32256) as [H21|H21]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 48128) as [H22|H22]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgn.drive6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 64512) as [H23|H23]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNTeDrvgc.drive7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia). exact (BNTeDrvgs.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEs PHIb E R FULL m HC ltac:(lia)).
  Qed.
  Theorem tail_t012e : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts t012 [par_even]) T0.
  Proof. rewrite <- vt012se_eq. exact tail_t012e_lit. Qed.
End Tail.
