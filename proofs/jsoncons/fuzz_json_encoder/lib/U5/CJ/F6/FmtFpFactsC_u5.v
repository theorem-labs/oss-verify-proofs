(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FloatScan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FloatScanProps.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloatProps.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFpDig.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFpProps.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFpRun.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFpTail.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_split.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import FmtFp_facts_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import FmtFp_facts2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_facts3.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFpNF.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require F_fmt_fp_nf_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ffp_e_eq : ffp_e = g_e. Proof. reflexivity. Qed.
Lemma ffp_j_eq : ffp_j = g_j. Proof. reflexivity. Qed.
Lemma ffp_R_eq : ffp_R = g_R. Proof. reflexivity. Qed.
Lemma ffp_H_eq : ffp_H = g_H. Proof. reflexivity. Qed.

Lemma ffp_sign_0 : forall y, ffp_sign y 0 = if negb (signbitl y =? 0) then (Z.lxor y F128_SIGNBIT, 0, 1) else (y, 1, 0).
Proof. intros. reflexivity. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fmt_fp_g_total : forall d p1, dfin d -> (p1 = 15 \/ p1 = 17) ->
  exists txt pl l', fmt_fp [] (f128_of_d d) 1 p1 0 CHR_g = Some (txt, pl + l') /\
    zlength txt = pl + l' /\ Forall gch txt /\ 0 <= pl <= 1 /\ 1 <= l' <= p1 + 7.
Proof.
  intros d p1 Hfin Hp.
  destruct (fmt_loops d p1 CHR_g Hfin ltac:(lia) ltac:(cbv; discriminate))
    as [nz [fr [e0 [y2 (C1 & C2 & C3 & C4 & REST)]]]].
  cbv zeta in REST. destruct REST as (He2 & [big [z (ED & Hz & WB & LB & ZO & W0 & ZC & [s1 (EU & HS1 & DS1 & ZS1 & [big2 [a2 [z2 (EDN & PN & PZ)]]])])]]).
  rewrite fmt_fp_split, ffp_sign_0.
  set (sb := negb (signbitl (f128_of_d d) =? 0)).
  assert (Y1 : forall prefix pl, (if sb then (Z.lxor (f128_of_d d) F128_SIGNBIT, 0, 1) else (f128_of_d d, 1, 0)) = (strip_sign (f128_of_d d), prefix, pl) ->
     exists txt l', ffp_C [] 1 0 CHR_g (strip_sign (f128_of_d d)) p1 prefix pl = Some (txt, pl + l') /\
       zlength txt = pl + l' /\ Forall gch txt /\ 1 <= l' <= p1 + 7).
  2:{ assert (SS : strip_sign (f128_of_d d) = if sb then Z.lxor (f128_of_d d) F128_SIGNBIT else f128_of_d d) by reflexivity.
      destruct sb.
      - destruct (Y1 0 1) as [txt [l' (E & L & F & B)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, 1, l'. repeat split; auto; lia.
      - destruct (Y1 1 0) as [txt [l' (E & L & F & B)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, 0, l'. repeat split; auto; lia. }
  intros prefix pl EQ.
  assert (PP : (prefix = 0 /\ pl = 1) \/ (prefix = 1 /\ pl = 0)) by (destruct sb; inversion EQ; lia).
  unfold ffp_C. rewrite C2. cbv zeta. rewrite C3. unfold ffp_C2. rewrite C4.
  replace (p1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct nz.
  - (* [comment removed for export] *)
    cbv iota in ED. cbv iota.
    set (e2 := e0 - 1 - 28) in *.
    unfold ffp_D. change (128 - 5 - 1) with 122.
    set (r0 := if e2 <? 0 then 0 else 122) in *.
    rewrite ED. unfold ffp_E. rewrite EU. unfold ffp_F.
    destruct s1 as [[[b1 a1] z1] e21]. rewrite EDN.
    rewrite ffp_G_eq, ffp_e_eq, ffp_j_eq, ffp_R_eq, ffp_H_eq.
    pose proof (PN eq_refl) as PO.
    destruct (g_e_spec r0 big2 a2 z2 PO) as [e (Ee & TSe)]. rewrite Ee.
    pose proof PO as (_ & _ & _ & _ & NZa & _ & Rr).
    destruct (R_spec p1 prefix pl r0 big2 a2 z2 e TSe NZa) as [bigR [aR [zR [eR (ER & TSR & NZR & AR & ZR)]]]]; [| | lia |].
    { intros R0. destruct Rr as [[_ B]|[R1 _]]; [exact B| lia]. }
    { intros R1. destruct Rr as [[R0 _]|(_ & B & _)]; [lia| lia]. }
    cbv zeta. rewrite ER.
    destruct (H_spec [] p1 prefix pl r0 bigR aR zR eR TSR NZR) as [txt [l' (EH & L & F & B)]]; try lia.
    { destruct PP as [[-> ->]|[-> ->]]; cbn; [constructor; [unfold gch; lia| constructor] | constructor]. }
    rewrite EH. exists txt, l'. cbn. repeat split; auto; lia.
  - (* [comment removed for export] *)
    destruct (ZC eq_refl) as (E2 & Ez & Ebig). cbv iota in ED. cbv iota.
    rewrite E2 in *. change (0 <? 0) with false in *. cbv iota in ED. cbv iota.
    unfold ffp_D. change (128 - 5 - 1) with 122. change (0 <? 0) with false. cbv iota.
    rewrite ED. unfold ffp_E. rewrite EU. rewrite (HS1 ltac:(lia)). unfold ffp_F.
    rewrite (HS1 ltac:(lia)) in EDN. rewrite EDN.
    destruct (PZ eq_refl) as (-> & -> & ->).
    assert (G15a : ffp_G [] 1 0 CHR_g 15 0 1 (zrepeat 0 128) 122 122 123 = Some ([45; 48], 2)) by (vm_compute; reflexivity).
    assert (G15b : ffp_G [] 1 0 CHR_g 15 1 0 (zrepeat 0 128) 122 122 123 = Some ([48], 1)) by (vm_compute; reflexivity).
    assert (G17a : ffp_G [] 1 0 CHR_g 17 0 1 (zrepeat 0 128) 122 122 123 = Some ([45; 48], 2)) by (vm_compute; reflexivity).
    assert (G17b : ffp_G [] 1 0 CHR_g 17 1 0 (zrepeat 0 128) 122 122 123 = Some ([48], 1)) by (vm_compute; reflexivity).
    destruct Hp as [-> | ->]; destruct PP as [[-> ->]|[-> ->]].
    + rewrite G15a. exists [45; 48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G15b. exists [48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G17a. exists [45; 48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G17b. exists [48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_fp_g_some_dfin : forall o d w p fl t r, fmt_fp o (f128_of_d d) w p fl t = Some r -> dfin d.
Proof.
  intros o d w p fl t r H. unfold dfin. intros E.
  pose proof (fpclassifyl_infnan d E) as C.
  rewrite fmt_fp_split in H.
  assert (S1 : fst (fst (ffp_sign (f128_of_d d) fl)) = strip_sign (f128_of_d d)).
  { unfold ffp_sign, strip_sign. destruct (negb (signbitl (f128_of_d d) =? 0)); [reflexivity|].
    destruct (negb (Z.land fl MARK_POS =? 0)); [reflexivity|]. destruct (negb (Z.land fl PAD_POS =? 0)); reflexivity. }
  destruct (ffp_sign (f128_of_d d) fl) as [[y1 prefix] pl]. cbn [fst] in S1. subst y1.
  replace (fpclassifyl (strip_sign (f128_of_d d)) <=? 1) with true in H by (symmetry; apply Z.leb_le; exact C).
  discriminate H.
Qed.


Lemma fmt_fp_dn_iter_eq : forall n p t r s, fmt_fp_dn_iter n p t r s = dn_iter n p t r s.
Proof. reflexivity. Qed.
Lemma ffp_sign_fst : forall y, fst (fst (ffp_sign y 0)) = strip_sign y.
Proof. intros y. unfold ffp_sign, strip_sign. destruct (negb (signbitl y =? 0)); reflexivity. Qed.

Theorem fmt_fp_facts_g : forall d prec o r, (prec = 15 \/ prec = 17) -> fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, r) ->
  fmt_fp_facts (f128_of_d d) 0 prec CHR_g.
Proof.
  intros d prec o r Hp EG.
  pose proof (fmt_fp_g_some_dfin _ _ _ _ _ _ _ EG) as Hfin.
  pose proof (yn_widened d Hfin) as [YN0 YN1].
  destruct (fmt_loops d prec CHR_g Hfin ltac:(lia) ltac:(cbv; discriminate))
    as [nz [fr [e0 [y2 (C1 & C2 & C3 & C4 & REST)]]]].
  cbv zeta in REST. destruct REST as (He2 & [big [z (ED & Hz & WB & LB & ZO & W0 & ZC & [s1 (EU & HS1 & DS1 & ZS1 & [big2 [a2 [z2 (EDN & PN & PZ)]]])])]]).
  set (y := f128_of_d d) in *.
  set (e2 := if nz then e0 - 1 - 28 else e0) in *.
  replace (if nz then (if nz then e0 - 1 else e0) - 28 else if nz then e0 - 1 else e0) with e2 in * by (subst e2; destruct nz; reflexivity).
  set (yy := if nz then f128_mul y2 (f128_of_d D_0x1p28) else y2) in *.
  set (r0 := if e2 <? 0 then 0 else 122) in *.
  replace (prec <? 0) with false in * by (symmetry; apply Z.ltb_ge; lia).
  (* [comment removed for export] *)
  assert (PRE : forall y1 fr' e0', fst (fst (ffp_sign y 0)) = y1 -> frexpl FREXPL_FUEL y1 0 = Some (fr', e0') -> fr' = fr /\ e0' = e0).
  { intros y1 fr' e0' <- E. rewrite ffp_sign_fst, C2 in E. injection E as <- <-. split; reflexivity. }
  assert (YE : forall y' e2', (y' = (if negb (f128_le (f128_mul fr (f128_of_i32 2)) F128_ZERO =? 0) then f128_mul (f128_mul fr (f128_of_i32 2)) (f128_of_d D_0x1p28) else f128_mul fr (f128_of_i32 2))
            /\ e2' = (if negb (f128_le (f128_mul fr (f128_of_i32 2)) F128_ZERO =? 0) then e0 - 1 - 28 else e0)) -> y' = yy /\ e2' = e2).
  { intros y' e2' [-> ->]. rewrite C3, C4. split; reflexivity. }
  (* [comment removed for export] *)
  assert (RUN : forall p1 r0' bigD aD zD, run_to_dn y 0 prec CHR_g p1 r0' bigD aD zD -> p1 = prec /\ r0' = r0 /\ bigD = big2 /\ aD = a2 /\ zD = z2).
  { intros p1 r0' bigD aD zD (y1 & fr' & e0' & y' & e2' & b' & z' & yf & s & e2f & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
    destruct (PRE _ _ _ S1 S2) as [-> ->]. destruct (YE _ _ S3) as [-> ->].
    replace (prec <? 0) with false in S4 by (symmetry; apply Z.ltb_ge; lia). subst p1 r0'. fold r0 in S6, S7, S8.
    rewrite ED in S6. injection S6 as <- <- <-. rewrite EU in S7. injection S7 as <-. rewrite EDN in S8. injection S8 as <- <- <- _.
    repeat split; reflexivity. }
  unfold fmt_fp_facts. fold y.
  split; [exact YN0|]. split; [exact YN1|].
  split. { (* [comment removed for export] *)
    intros y1 fr' e0' y' e2' b' z' y'' S1 S2 S3 S4.
    destruct (PRE _ _ _ S1 S2) as [-> ->]. destruct (YE _ _ S3) as [-> ->]. fold r0 in S4 |- *.
    rewrite ED in S4. injection S4 as <- <- <-. lia. }
  split. { (* [comment removed for export] *)
    intros y1 fr' e0' S1 S2. destruct (PRE _ _ _ S1 S2) as [-> ->]. cbv zeta. rewrite C3, C4. lia. }
  split. { (* [comment removed for export] *)
    intros y1 fr' e0' y' e2' b' z' y'' s S1 S2 S3 S4 S5.
    destruct (PRE _ _ _ S1 S2) as [-> ->]. destruct (YE _ _ S3) as [-> ->]. fold r0 in S4, S5 |- *.
    rewrite ED in S4. injection S4 as <- <- <-. rewrite EU in S5. injection S5 as <-.
    intros n bigI aI zI e2I IT HeI. rewrite fmt_fp_dn_iter_eq in IT.
    replace (if prec <? 0 then 6 else prec) with prec in IT by (replace (prec <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    destruct (Z.lt_ge_cases e2 0) as [NEG|NNEG].
    - destruct nz; [| destruct (ZC eq_refl) as [E0 _]; lia].
      pose proof (DS1 eq_refl NEG) as DI. rewrite (HS1 ltac:(lia)) in DI, IT.
      assert (R0 : r0 = 0) by (subst r0; replace (e2 <? 0) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      rewrite R0 in IT, DI.
      pose proof (dn_iter_DNI prec CHR_g n _ _ ltac:(lia) ltac:(cbv; discriminate) DI IT) as (_ & _ & AZ & NZ' & _ & ZM & _).
      unfold dn_ok. unfold dnm in ZM. split; [lia|]. intros; lia.
    - destruct (ZS1 NNEG) as [b1 [a1 [z1 ES1]]]. rewrite ES1 in IT. destruct n as [|n].
      + cbn in IT. injection IT as <- <- <- <-. lia.
      + cbn [dn_iter] in IT. change (0 <? 0) with false in IT. discriminate IT. }
  split. { (* [comment removed for export] *)
    intros p1 r0' bigD aD zD R i. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
    destruct nz.
    - destruct (PN eq_refl) as (W & _). unfold W9, NB in W. apply W.
    - destruct (PZ eq_refl) as (-> & _). rewrite znth_zrepeat. destruct (_ && _); lia. }
  split. { (* [comment removed for export] *)
    intros p1 r0' bigD aD zD R e prefix pl bigR aR zR eR Ee ER. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
    rewrite ffp_e_eq in Ee. rewrite ffp_R_eq, ffp_j_eq in ER.
    destruct nz.
    - pose proof (PN eq_refl) as PO. destruct (g_e_spec r0 big2 a2 z2 PO) as [e' (Ee' & TSe)]. rewrite Ee' in Ee. injection Ee as ->.
      pose proof PO as (_ & _ & _ & _ & NZa & _ & Rr).
      destruct (R_spec prec prefix pl r0 big2 a2 z2 e TSe NZa) as [bigR' [aR' [zR' [eR' (ER' & TSR & _)]]]]; [| | lia |].
      { intros R0. destruct Rr as [[_ B]|[R1 _]]; [exact B| lia]. }
      { intros R1. destruct Rr as [[R0 _]|(_ & B & _)]; [lia| lia]. }
      rewrite ER' in ER. injection ER as <- <- <- <-. destruct TSR as (_ & _ & AZ & _). lia.
    - destruct (PZ eq_refl) as (-> & -> & ->). destruct (ZC eq_refl) as (E20 & _ & _).
      assert (R0 : r0 = 122) by (subst r0; rewrite E20; reflexivity). rewrite R0 in *.
      assert (EE : e = 0). { revert Ee. clear. intros Ee. vm_compute in Ee. congruence. }
      subst e. unfold g_R in ER.
      replace (g_j CHR_g prec 0 <? 9 * (123 - 122 - 1)) with false in ER.
      2:{ symmetry. apply Z.ltb_ge. unfold g_j. change (Z.lor CHR_g 32 =? CHR_f) with false. change (Z.lor CHR_g 32 =? CHR_g) with true.
          replace (prec =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. lia. }
      injection ER as <- <- <- <-. lia. }
  split. { (* [comment removed for export] *)
    intros p1 r0' bigD aD zD R e prefix pl bigR aR zR eR zS Ee ER ES Ht HzS. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
    rewrite ffp_e_eq in Ee. rewrite ffp_R_eq, ffp_j_eq in ER.
    destruct nz.
    - pose proof (PN eq_refl) as PO. destruct (g_e_spec r0 big2 a2 z2 PO) as [e' (Ee' & TSe)]. rewrite Ee' in Ee. injection Ee as ->.
      pose proof PO as (_ & _ & _ & _ & NZa & _ & Rr).
      destruct (R_spec prec prefix pl r0 big2 a2 z2 e TSe NZa) as [bigR' [aR' [zR' [eR' (ER' & TSR & NZR & _)]]]]; [| | lia |].
      { intros R0. destruct Rr as [[_ B]|[R1 _]]; [exact B| lia]. }
      { intros R1. destruct Rr as [[R0 _]|(_ & B & _)]; [lia| lia]. }
      rewrite ER' in ER. injection ER as <- <- <- <-. destruct TSR as (_ & _ & AZ & Z7 & _).
      destruct (strip_spec bigR' aR' zR' ltac:(lia) ltac:(lia) NZR) as [zS' (ES' & HzS' & _)]. rewrite ES' in ES. injection ES as <-. lia.
    - destruct (PZ eq_refl) as (-> & -> & ->). destruct (ZC eq_refl) as (E20 & _ & _).
      assert (R0 : r0 = 122) by (subst r0; rewrite E20; reflexivity). rewrite R0 in *.
      assert (EE : e = 0). { revert Ee. clear. intros Ee. vm_compute in Ee. congruence. }
      subst e. unfold g_R in ER.
      replace (g_j CHR_g prec 0 <? 9 * (123 - 122 - 1)) with false in ER.
      2:{ symmetry. apply Z.ltb_ge. unfold g_j. change (Z.lor CHR_g 32 =? CHR_f) with false. change (Z.lor CHR_g 32 =? CHR_g) with true.
          replace (prec =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. lia. }
      injection ER as <- <- <- <-. reflexivity. }
  (* [comment removed for export] *)
  intros p1 r0' bigD aD zD R k Hk. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
  destruct nz.
  - destruct (PN eq_refl) as (_ & _ & _ & _ & _ & ZB & _). apply ZB. lia.
  - destruct (PZ eq_refl) as (-> & _). rewrite znth_zrepeat. destruct (_ && _); lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dfin_dec : forall d, {dfin d} + {~ dfin d}.
Proof. intros d. unfold dfin. destruct (Z.eq_dec (d_exp d) 2047); [right; tauto | left; exact n]. Qed.

Lemma nonfinite_of_d : forall d, ~ dfin d -> nonfinite (f128_of_d d) 0.
Proof.
  intros d H. unfold dfin in H. assert (E : d_exp d = 2047) by (destruct (Z.eq_dec (d_exp d) 2047); [exact e | contradiction]).
  pose proof (fpclassifyl_infnan d E) as C. unfold nonfinite.
  rewrite ffp_sign_0. unfold strip_sign in C.
  destruct (negb (signbitl (f128_of_d d) =? 0)); exact C.
Qed.

(* [comment removed for export] *)
Theorem fmt_fp'_g_total : forall d prec, (prec = 15 \/ prec = 17) ->
  exists o l, fmt_fp' [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) /\ l = zlength o /\ 1 <= zlength o <= 25
              /\ F_fmt_fp_nf_u5.fmt_fp_facts' (f128_of_d d) 0 prec CHR_g
              /\ (dfin d -> fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l))
              /\ (~ dfin d -> In o [INF_LC; 45 :: INF_LC; NAN_LC; 45 :: NAN_LC]).
Proof.
  intros d prec Hp.
  destruct (dfin_dec d) as [Hfin|Hnf].
  - destruct (fmt_fp_g_total d prec Hfin Hp) as [txt [pl [l' (E & L & F & B1 & B2)]]].
    exists txt, (pl + l'). unfold fmt_fp'. rewrite E. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [right; exact (fmt_fp_facts_g d prec txt (pl + l') Hp E)|].
    split; [intros _; reflexivity | intros X; contradiction].
  - pose proof (nonfinite_of_d d Hnf) as NF.
    rewrite (fmt_fp'_nonfinite _ _ _ _ _ _ NF). unfold fmt_fp_nf.
    unfold nonfinite in NF. destruct (ffp_sign (f128_of_d d) 0) as [[y1 prefix] pl] eqn:ES.
    assert (PP : (prefix = 0 /\ pl = 1) \/ (prefix = 1 /\ pl = 0)).
    { rewrite ffp_sign_0 in ES. destruct (negb (signbitl (f128_of_d d) =? 0)); injection ES as _ <- <-; lia. }
    replace (fpclassifyl y1 <=? 1) with true by (symmetry; apply Z.leb_le; exact NF). cbn [andb Z.leb].
    exists (zsub PREFIX_STR prefix pl ++ nf_str y1 CHR_g), (3 + pl).
    split; [reflexivity|].
    assert (LS : zlength (zsub PREFIX_STR prefix pl ++ nf_str y1 CHR_g) = pl + 3).
    { unfold zlength. rewrite length_app, nf_str_length. rewrite zsub_length; [lia | lia | lia | unfold PREFIX_STR, zlength; cbn; lia]. }
    split; [lia|]. split; [lia|]. split; [left; unfold nonfinite; rewrite ES; exact NF|].
    split; [intros X; contradiction|]. intros _.
    assert (NS : nf_str y1 CHR_g = INF_LC \/ nf_str y1 CHR_g = NAN_LC).
    { unfold nf_str. change (Z.land CHR_g 32 =? 0) with false. destruct (f128_le y1 y1 =? 0); [left|right]; reflexivity. }
    destruct PP as [[-> ->]|[-> ->]]; destruct NS as [-> | ->]; cbn; tauto.
Qed.
