(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheckG HBArg HBChain HBUsageDefs HBHop HBParity HBSel
  BVT3Se BVT3SeEq BVT3Lit BNT3eFE BNT3eFEE BNT3ecFE BNT3ecFEE BNT3esFE BNT3esFEE BNT3eDrvz BNT3eDrvs BNT3eDrvp BNT3eDrvw1 BNT3eDrvw2 BNT3eDrvv BNT3eDrvw6 BNT3eDrvw10 BNT3eDrvgn BNT3eDrvgc BNT3eDrvgs BNT3eDrvw19.
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
  Hypothesis H_FE : fx_hole SV argH ISP fs nt3e_tfe nt3efee.
  Hypothesis H_FEc : fx_hole SV argH ISP fs nt3ec_tfe nt3ecfee.
  Hypothesis H_FEs : fx_hole SV argH ISP fs nt3es_tfe nt3esfee.
  Lemma tail_t3e_lit : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs vt3se T0.
  Proof.
    intros PHIb E R FULL m HC.
    pose proof (nb_range sp rdraw argv envp uid hw fs SV BNT3eDrvz.BASE BNT3eDrvz.HKN PHIb E R FULL m HC) as Hr.
    unfold T0.
    destruct (Z_le_gt_dec (nb_of E) 0) as [H0|H0]; [replace (nb_of E <? 11) with true by (symmetry; apply Z.ltb_lt; lia); exact (BNT3eDrvz.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 10) as [H1|H1]; [replace (nb_of E <? 11) with true by (symmetry; apply Z.ltb_lt; lia); exact (BNT3eDrvs.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 15) as [H2|H2]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvp.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 16) as [H3|H3]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvw1.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 48) as [H4|H4]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvw2.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 64) as [H5|H5]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvv.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 96) as [H6|H6]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgn.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 128) as [H7|H7]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvw6.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 224) as [H8|H8]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 256) as [H9|H9]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvw10.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 288) as [H10|H10]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgn.drive1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 352) as [H11|H11]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 384) as [H12|H12]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgn.drive2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 448) as [H13|H13]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 640) as [H14|H14]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgn.drive3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 896) as [H15|H15]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 1408) as [H16|H16]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvw19.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 1920) as [H17|H17]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 2944) as [H18|H18]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgn.drive4 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 3968) as [H19|H19]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 12032) as [H20|H20]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgn.drive5 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 32256) as [H21|H21]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 48128) as [H22|H22]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgn.drive6 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FE PHIb E R FULL m HC ltac:(lia))|].
    destruct (Z_le_gt_dec (nb_of E) 64512) as [H23|H23]; [replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia); exact (BNT3eDrvgc.drive7 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEc PHIb E R FULL m HC ltac:(lia))|].
    replace (nb_of E <? 11) with false by (symmetry; apply Z.ltb_ge; lia). exact (BNT3eDrvgs.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEs PHIb E R FULL m HC ltac:(lia)).
  Qed.
  Theorem tail_t3e : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts t3 [par_even]) T0.
  Proof. rewrite <- vt3se_eq. exact tail_t3e_lit. Qed.
End Tail.
