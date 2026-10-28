(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxReblob HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBUsageDefs HBParity.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section VtHop.
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
  Let SVF := SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c.
  Let SVA := SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c.
  Let SV1 := SVm_to1 sp rdraw brk0 argv envp uid hw c.

  Variable PHI : env -> Prop.
  Hypothesis PHI_agree : forall E E', env_agree NX0 E E' -> PHI E -> PHI E'.
  Variable T : env -> Fs.Fs -> TSet.
  Hypothesis T_agree : t_agree T.
  Hypothesis T_nil : forall E fs0, T E fs0 [].
  #[local] Notation SVP := (SVG PHI SV).
  #[local] Notation PIECE := (piece SVP argH ISP fs).

  (* [comment removed for export] *)
  Variable NX : nat.
  Hypothesis NX_ge : (NX0 <= NX)%nat.
  Hypothesis NX_spw : CAP.expr_vars_lt NX e_spw = true.
  Variables TT S : acs.
  Variable sig : list (nat * expr).
  Variable F : list kentry.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound HASEGS IT.
  Variable plan : CAP.plan.
  Variable h : nat.
  Hypothesis HT_ok : ht_ok NX (TT, sig, F) = true.
  (* [comment removed for export] *)
  Hypothesis Htmpl : forall PHIb : env -> Prop, piece (SVG PHIb SV) argH ISP fs (with_facts TT F) T.
  (* [comment removed for export] *)
  Hypothesis CHK : CAP.check HASEGS IT HAT NX AsanInit.LIMIT (hag_XN NX) (hag_XE NX) hag_XB (HS_tg [(h, (TT, sig, F))]) 0 true false true 400000 3000 None S plan = COk (SHole h).

  Let HOLES : nat -> env -> Fs.Fs -> TSet := fun _ E fs0 => T E fs0.

  Lemma PHI_agreeNX : forall E E', env_agree NX E E' -> PHI E -> PHI E'.
  Proof. intros E E' Hag HP. exact (PHI_agree E E' (CXS.env_agree_le NX0 NX E E' Hag NX_ge) HP). Qed.
  Lemma HOLES_agree : forall h0 E E' fs0, env_agree NX E E' -> HOLES h0 E fs0 = HOLES h0 E' fs0.
  Proof. intros h0 E E' fs0 Hag. unfold HOLES. exact (T_agree E E' fs0 (CXS.env_agree_le NX0 NX E E' Hag NX_ge)). Qed.
  Lemma HOLES_nil : forall h0 E fs0, HOLES h0 E fs0 []. Proof. intros h0 E fs0. unfold HOLES. apply T_nil. Qed.
  Lemma HOLES_mod : forall h0 E fs0, HOLES h0 E fs0 = HOLES (CAP.hole_cls h0) E fs0. Proof. intros; reflexivity. Qed.
  Lemma holes_ok : forallb (fun p => ht_ok NX (snd p)) [(h, (TT, sig, F))] = true.
  Proof. cbn [forallb snd]. rewrite HT_ok. reflexivity. Qed.

  Lemma conts : forall h0 t, assoc h0 [(h, (TT, sig, F))] = Some t ->
    forall E R FULL model, cs_ok HASEGS HAT AsanInit.LIMIT (SVG (PHI_ext PHI (ht_s t) (ht_F t)) SV) argH ISP fs E (ht_T t) R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc (ht_T t)) FULL model) (HOLES h0 E (m_fs model)).
  Proof.
    intros h0 t Hh E R FULL model HC. cbn [assoc] in Hh. destruct (Nat.eqb h h0); [|discriminate Hh]. diet_injection Hh.
    cbn [ht_T ht_s ht_F fst snd] in HC |- *. unfold HOLES.
    assert (HC2 : cs_ok HASEGS HAT AsanInit.LIMIT (SVG (PHI_ext PHI sig F) SV) argH ISP fs E (with_facts TT F) R FULL model).
    { change (with_facts TT F) with (add_kn TT F).
      eapply add_facts; [|exact HC]. intros E0 (_ & _ & HF). exact HF. }
    change (pc TT) with (pc (with_facts TT F)).
    exact (Htmpl (PHI_ext PHI sig F) E R FULL model HC2).
  Qed.

  Theorem vt_hop : PIECE S T.
  Proof.
    intros E R FULL m HC.
    exact (hop_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA true 400000%nat 3000%nat
             NX NX NX_ge NX_spw (le_n NX) PHI PHI_agreeNX [(h, (TT, sig, F))] holes_ok HOLES HOLES_agree HOLES_nil HOLES_mod conts
             IT IT_ok S plan (SHole h) CHK E R FULL m HC).
  Qed.
End VtHop.

(* [comment removed for export] *)
Definition vt_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma vt_IT_ok : itab_sound HASEGS vt_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
