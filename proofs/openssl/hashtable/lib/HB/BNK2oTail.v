(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBCheckG HBArg HBChain HBUsageDefs HBHop HBParity HBSelK
  BVG2T012So BVG2T012SoEq BVG2T012Lit BNK2osFE BNK2osFEE BNK2oDrvks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition PALL (E : env) : Prop := True.
Lemma PALL_agree : forall E E', env_agree NX0 E E' -> PALL E -> PALL E'. Proof. intros; exact I. Qed.
Lemma cover : forall E, PALL E. Proof. intros; exact I. Qed.
Definition T0 (E : env) (fs' : Fs.Fs) : TSet := TGT false (calls_of E) (cnt_of E) fs'.      (* [comment removed for export] *)
Lemma closed_agree : forall e E E', expr_vars_lt 0 e = true -> env_agree NX0 E E' -> uE E e = uE E' e.
Proof. intros e E E' He Hag. unfold uE. rewrite (edenot_agree' 0 E E' e); [reflexivity | | exact He]. destruct Hag as [_ Hb]. split; [intros n Hn; lia | exact Hb]. Qed.
Lemma T0_agree : t_agree T0.
Proof.
  intros E E' fs0 Hag. unfold T0, calls_of, cnt_of, cl_of. rewrite (closed_agree e_cl E E' eq_refl Hag), (closed_agree e_cm E E' eq_refl Hag), (closed_agree e_b1s E E' eq_refl Hag). reflexivity.
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
  Hypothesis H_FEs : fx_hole SV argH ISP fs nk2os_tfe nk2osfee.
  Lemma tail_g2t012o_lit : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs vg2t012so T0.
  Proof.
    intros PHIb E R FULL m HC.
    pose proof (nb_range sp rdraw argv envp uid hw fs SV _ _ _ _ BNK2oDrvks.HL BNK2oDrvks.BASE BNK2oDrvks.NB BNK2oDrvks.HNB BNK2oDrvks.HNB0 BNK2oDrvks.HKN PHIb E R FULL m HC) as Hr.      (* [comment removed for export] *)
    unfold T0.
    exact (BNK2oDrvks.drive sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit H_FEs PHIb E R FULL m HC ltac:(lia)).
  Qed.
  Theorem tail_g2t012o : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts vg2t012 [par_odd]) T0.
  Proof. rewrite <- vg2t012so_eq. exact tail_g2t012o_lit. Qed.
End Tail.
