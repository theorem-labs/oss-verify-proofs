(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp.
Module NumFacts_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition num_gch (c : Z) : Prop := 48 <= c <= 57 \/ c = 43 \/ c = 45 \/ c = 46 \/ c = 69 \/ c = 101.

Definition NUM_FMT_G_TOTAL : Prop :=
  forall d p1, ((d mod 2^64) / 2^52) mod 2^11 <> 2047 -> (p1 = 15 \/ p1 = 17) ->
    exists txt, fmt_g d p1 = Some (txt, zlength txt) /\ Forall num_gch txt /\ zlength txt <= p1 + 8.

Definition NUM_FMT_D_TOTAL : Prop :=
  forall x, exists o, fmt_d x = Some (o, zlength o) /\ Forall num_gch o /\ zlength o <= 22 /\ (- 2^31 <= x < 2^31 -> zlength o <= 11).

Definition NUM_FMT_G_FACTS : Prop :=
  forall d prec o r, (prec = 15 \/ prec = 17) -> fmt_g d prec = Some (o, r) -> F_fmt_fp.fmt_fp_facts (f128_of_d d) 0 prec CHR_g.

Definition NUM_SSCANF_JUNK : Prop :=
  forall t junk, Forall (fun c => FmtFp_facts3.is_numch c = true) t ->
    scan_sscanf_lg (t ++ 0 :: junk) = scan_sscanf_lg (t ++ [0]).
End NumFacts_iface.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan FloatScanProps SoftFloatProps FmtFpDig.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require NumFacts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.NumFacts.FmtFpProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require NumFacts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.NumFacts.FmtFpRun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require NumFacts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.NumFacts.FmtFpTail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import NumFacts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts2.FmtFp_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts2 FmtFp_facts3 F_printf_iface F_fmt_fp.
Import NumFacts_iface.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem num_fmt_g_total_proof : NUM_FMT_G_TOTAL.
Proof. exact fmt_g_total. Qed.

Theorem num_fmt_d_total_proof : NUM_FMT_D_TOTAL.
Proof. exact fmt_d_spec. Qed.

Theorem fmt_g_ret_proof : FMT_G_RET.
Proof.
  intros d prec o l Hp E.
  pose proof (fmt_fp_g_some_dfin _ _ _ _ _ _ _ E) as Hfin.
  destruct (fmt_fp_g_total d prec Hfin Hp) as [txt [pl [l' (E' & L & _)]]]. rewrite E' in E. injection E as <- <-. lia.
Qed.

Theorem fmt_g_len25_proof : FMT_G_LEN25.
Proof.
  intros d prec o l Hp E.
  pose proof (fmt_fp_g_some_dfin _ _ _ _ _ _ _ E) as Hfin.
  destruct (fmt_fp_g_total d prec Hfin Hp) as [txt [pl [l' (E' & L & F & B1 & B2)]]]. rewrite E' in E. injection E as <- <-. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_fp_dn_iter_eq : forall n p t r s, fmt_fp_dn_iter n p t r s = dn_iter n p t r s.
Proof. reflexivity. Qed.
Lemma ffp_sign_fst : forall y, fst (fst (ffp_sign y 0)) = strip_sign y.
Proof. intros y. unfold ffp_sign, strip_sign. destruct (negb (signbitl y =? 0)); reflexivity. Qed.

Theorem num_fmt_g_facts_proof : NUM_FMT_G_FACTS.
Proof.
  intros d prec o r Hp EG.
  pose proof (fmt_g_some_dfin d prec (o, r) EG) as Hfin.
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_junk.
Theorem num_sscanf_junk_proof : NUM_SSCANF_JUNK.
Proof. exact sscanf_junk. Qed.
