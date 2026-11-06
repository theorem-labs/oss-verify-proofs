(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegFastLoad SegFastCopy SegFastHavoc FxBlock FxCarry FxExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SGF.

Fixpoint existsb_l {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | a :: r => if f a then true else existsb_l f r end.
Lemma existsb_l_eq : forall A (f : A -> bool) l, existsb_l f l = existsb f l.
Proof. induction l as [|a r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f a); reflexivity. Qed.
Fixpoint forallb_l {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => true | a :: r => if f a then forallb_l f r else false end.
Lemma forallb_l_eq : forall A (f : A -> bool) l, forallb_l f l = forallb f l.
Proof. induction l as [|a r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f a); reflexivity. Qed.

Definition within1X_f (kn : list kentry) (b : expr) (k n : Z) (r : SGP.region) : bool :=
  let '(rb, rlo, rlen) := r in
  if (match rlen with
      | ELit m => if Z.leb 0 m then (if Z.ltb m two64 then SR.within1 b k n (rb, rlo, m) else false) else false
      | _ => false
      end) then true else xinside kn b k (ELit n) rb rlo rlen.
Lemma within1X_f_eq : forall kn b k n r, within1X_f kn b k n r = SGP.within1X kn b k n r.
Proof.
  intros kn b k n [[rb rlo] rlen]. unfold within1X_f, SGP.within1X.
  destruct rlen; try reflexivity. destruct (Z.leb 0 z); [|reflexivity]. destruct (Z.ltb z two64); reflexivity.
Qed.
Definition withinX_f (kn : list kentry) (F : list SGP.region) (b : expr) (k n : Z) : bool :=
  if Z.ltb 0 n then (if Z.ltb n two64 then existsb_l (within1X_f kn b k n) F else false) else false.
Lemma withinX_f_eq : forall kn F b k n, withinX_f kn F b k n = SGP.withinX kn F b k n.
Proof.
  intros. unfold withinX_f, SGP.withinX. rewrite existsb_l_eq.
  replace (within1X_f kn b k n) with (SGP.within1X kn b k n) by (apply functional_extensionality; intros; symmetry; apply within1X_f_eq).
  destruct (Z.ltb 0 n); [|reflexivity]. destruct (Z.ltb n two64); reflexivity.
Qed.
Definition went_withinX_f (kn : list kentry) (F : list SGP.region) (g : SR.went) : bool :=
  match g with
  | SR.WSt (SA b k) wd _ => withinX_f kn F b k (Z.of_nat wd)
  | SR.WCopy db dk _ _ n => withinX_f kn F db dk n
  | SR.WFill db dk n _ => withinX_f kn F db dk n
  end.
Lemma went_withinX_f_eq : forall kn F g, went_withinX_f kn F g = SGP.went_withinX kn F g.
Proof. intros kn F [[b k] wd v|db dk sb sk n|db dk n c]; cbn [went_withinX_f SGP.went_withinX]; apply withinX_f_eq. Qed.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.
Variable IT : itab.
Variable x_cpy x_set x_len ro_lo ro_hi : Z.
Variable BFUEL : nat.

Definition step_block_f (stops : list Z) (ss : sym_state) (w : list SR.went) : option (sym_state * list SR.went) :=
  let bc := BLKF.mkbc_m (facts_of (s_know ss)) in
  let '(ss', scs) := EXF.sym_execTXBIFL segs bc (s_know ss) (CARF.mk_bext bc) IT 0%nat BFUEL true stops ss in
  match CARF.carryKF_ctx bc (s_log ss') scs (s_know ss') [] with
  | (kn', [], _) => Some (SS (s_pc ss') (s_regs ss') [] kn' (s_next ss'), SR.wlog (s_log ss') ++ w)
  | _ => None
  end.
Lemma step_block_f_eq : forall stops ss w, step_block_f stops ss w = SR.step_block segs IT BFUEL stops ss w.
Proof.
  intros. unfold step_block_f, SR.step_block. rewrite EXF.sym_execTXBIFL_eq. rewrite BLKF.mkbc_m_eq, BLKF.mk_kix_f_eq.
  rewrite EXF.sym_execTXBIF_eq by (first [reflexivity | eexists; reflexivity]). rewrite CARF.carryKF_ctx_eq, CARF.carryKF_eq.
  rewrite (sym_execTXBI_eq segs (s_know ss)) by reflexivity.
  rewrite <- (sym_execTX_know segs IT 0%nat BFUEL true stops ss) at 1.
  rewrite carryK_eq. reflexivity.
Qed.

End WithSegs.

Ltac has_const t c := lazymatch t with context [c] => idtac | _ => fail "abstraction target does not occur:" c end.

Definition copy_factsM := AX2Y.copy_factsM2.
Lemma copy_factsM_eq : copy_factsM = @APC.copy_facts.
Proof. exact AX2Y.copy_factsM2_eq. Qed.
Lemma step_block_f_eqf : step_block_f = @SR.step_block.
Proof. repeat (apply functional_extensionality; intros ?). apply step_block_f_eq. Qed.
Lemma went_withinX_f_eqf : went_withinX_f = SGP.went_withinX.
Proof. repeat (apply functional_extensionality; intros ?). apply went_withinX_f_eq. Qed.
Lemma existsb_l_eqf : @existsb_l = @existsb.
Proof. apply functional_extensionality_dep; intros A. repeat (apply functional_extensionality; intros ?). apply existsb_l_eq. Qed.
Lemma forallb_l_eqf : @forallb_l = @forallb.
Proof. apply functional_extensionality_dep; intros A. repeat (apply functional_extensionality; intros ?). apply forallb_l_eq. Qed.

Definition step1_g :=
  ltac:(let t := eval cbv beta delta [SGP.step1 SR.seg_step SR.step_copy SR.step_fill] in @SGP.step1 in
        has_const t (@SR.step_block); has_const t (@APC.kn_havoc); has_const t (@APC.copy_facts); has_const t (@SGP.went_withinX); has_const t (@forallb);
        let t' := eval pattern (@SR.step_block), (@APC.kn_havoc), (@APC.copy_facts), (@SGP.went_withinX), (@forallb) in t in
        lazymatch t' with ?F _ _ _ _ _ => exact F end).
Lemma step1_g_ref : step1_g (@SR.step_block) (@APC.kn_havoc) (@APC.copy_facts) (@SGP.went_withinX) (@forallb) = @SGP.step1.
Proof. reflexivity. Qed.
Definition step1_f := step1_g step_block_f AX2H.kn_havocMF copy_factsM went_withinX_f (@forallb_l).
Lemma step1_f_eqf : step1_f = @SGP.step1.
Proof. unfold step1_f. rewrite step_block_f_eqf, AX2H.kn_havocMF_eq, copy_factsM_eq, went_withinX_f_eqf, forallb_l_eqf. exact step1_g_ref. Qed.

Definition cert_ok_g :=
  ltac:(let t := eval cbv beta delta [SGP.cert_ok SGP.check] in @SGP.cert_ok in
        has_const t (@SGP.step1);
        let t' := eval pattern (@SGP.step1) in t in
        lazymatch t' with ?F _ => exact F end).
Lemma cert_ok_g_ref : cert_ok_g (@SGP.step1) = @SGP.cert_ok.
Proof. reflexivity. Qed.

Definition cert_ok_fast := cert_ok_g step1_f.
Theorem cert_ok_fast_eq : cert_ok_fast = @SGP.cert_ok.
Proof. unfold cert_ok_fast. rewrite step1_f_eqf. exact cert_ok_g_ref. Qed.

Lemma cert_of_fast : forall segs IT xc xs xl rl rh BF A nx0 BR XSTEP XSTEP2 F PSS p pc0 sr0 kn0,
  cert_ok_fast segs IT xc xs xl rl rh BF A nx0 BR XSTEP XSTEP2 F PSS p pc0 sr0 kn0 = true ->
  SGP.cert_ok segs IT xc xs xl rl rh BF A nx0 BR XSTEP XSTEP2 F PSS p pc0 sr0 kn0 = true.
Proof. intros until kn0. rewrite cert_ok_fast_eq. exact (fun H => H). Qed.
Lemma cert_by_fast : forall (XSTEP' XSTEP : list SGP.region -> nat -> sym_state -> option sym_state), XSTEP' = XSTEP ->
  forall segs IT xc xs xl rl rh BF A nx0 BR XSTEP2 F PSS p pc0 sr0 kn0,
  cert_ok_fast segs IT xc xs xl rl rh BF A nx0 BR XSTEP' XSTEP2 F PSS p pc0 sr0 kn0 = true ->
  SGP.cert_ok segs IT xc xs xl rl rh BF A nx0 BR XSTEP XSTEP2 F PSS p pc0 sr0 kn0 = true.
Proof. intros XSTEP' XSTEP <-. intros. apply cert_of_fast. assumption. Qed.

End SGF.
