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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import FmtFpFactsC_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frac_shape (t : list Z) : Prop := t = [] \/ exists t3, t = CHR_dot :: t3 /\ t3 <> [] /\ Forall isdig t3.
Definition f_body (t : list Z) : Prop := exists t1 t2, t = t1 ++ t2 /\ t1 <> [] /\ Forall isdig t1 /\ frac_shape t2.
Definition e_body (t : list Z) : Prop :=
  exists d t2 es ed, t = d :: t2 ++ 101 :: es :: ed /\ isdig d /\ frac_shape t2 /\ (es = CHR_plus \/ es = CHR_minus) /\ ed <> [] /\ Forall isdig ed.
Definition gshape (t : list Z) : Prop := exists sg body, t = sg ++ body /\ (sg = [] \/ sg = [CHR_minus]) /\ (f_body body \/ e_body body).

Lemma skipn_cons_nth : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma zsub_cons : forall l i n, 0 <= i -> 0 < n -> i < zlength l -> zsub l i n = znth l i :: zsub l (i + 1) (n - 1).
Proof.
  intros l i n Hi Hn Hl. unfold zsub, znth.
  destruct (Z.ltb_spec i 0); [lia|].
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite skipn_cons_nth by (unfold zlength in Hl; lia). reflexivity.
Qed.
Lemma Forall_isdig_zrepeat0 : forall n, Forall isdig (zrepeat CHR_0 n).
Proof. intros n. apply Forall_zrepeat. apply isdig_0. Qed.
Lemma nonnil_of_zlength : forall (l : list Z), 1 <= zlength l -> l <> [].
Proof. intros l H E. subst l. unfold zlength in H. cbn in H. lia. Qed.
Lemma nil_of_zlength : forall (l : list Z), zlength l = 0 -> l = [].
Proof. intros [|x l] H; [reflexivity|]. unfold zlength in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma emit_f_shape : forall o big a r0 z p k, W9 big -> 0 <= r0 -> r0 - 128 < a -> a < z -> z <= 128 -> 0 <= a -> 0 <= p <= 40 ->
  (r0 < a -> znth big r0 = 0) -> DIGk (znth big a) k -> 1 <= k <= 9 ->
  exists txt, fmt_fp_emit_f o big a r0 z p 0 = Some (o ++ txt) /\ f_body txt.
Proof.
  intros o big a r0 z p k WB Hr0 Har Haz Hz Ha Hp Hbelow D Hk. unfold fmt_fp_emit_f.
  set (a0 := if r0 <? a then r0 else a).
  assert (A0 : (a <= r0 /\ a0 = a) \/ (r0 < a /\ a0 = r0)) by (subst a0; destruct (Z.ltb_spec r0 a); lia).
  assert (K0 : exists k0, DIGk (znth big a0) k0 /\ 0 <= k0 <= 9 /\ Z.max k0 1 = (if a <=? r0 then k else 1)).
  { destruct A0 as [[H1 ->]|[H1 ->]].
    - exists k. split; [exact D|]. replace (a <=? r0) with true by (symmetry; apply Z.leb_le; lia). lia.
    - exists 0. rewrite (Hbelow H1). split; [left; lia|]. replace (a <=? r0) with false by (symmetry; apply Z.leb_gt; lia). lia. }
  destruct K0 as [k0 (D0 & Hk0 & MK)]. clearbody a0.
  destruct (fint_spec big a0 r0 o k0 WB ltac:(lia) ltac:(lia) D0 Hk0) as [t1 (E1 & F1 & L1)]. rewrite E1.
  change (Z.land 0 ALT_FORM =? 0) with true. cbn [negb orb].
  destruct (Z.eqb_spec p 0) as [P0|P0]; cbn [negb orb].
  - (* [comment removed for export] *)
    destruct (ffrac_spec big z (r0 + 1) p (o ++ t1) WB ltac:(lia) ltac:(lia)) as [d' [p' [t3 (E3 & F3 & L3 & P3)]]].
    rewrite E3. rewrite pad_exact by lia.
    exists (t1 ++ t3 ++ zrepeat CHR_0 (p' + 9 - 9)). unfold out. split; [rewrite <- !app_assoc; reflexivity|].
    assert (Z0 : t3 ++ zrepeat CHR_0 (p' + 9 - 9) = []).
    { apply nil_of_zlength. rewrite zlength_app, zlength_zrepeat'. lia. }
    rewrite Z0. exists t1, []. split; [reflexivity|]. split; [apply nonnil_of_zlength; lia|]. split; [exact F1| left; reflexivity].
  - (* [comment removed for export] *)
    destruct (ffrac_spec big z (r0 + 1) p (out (o ++ t1) [CHR_dot]) WB ltac:(lia) ltac:(lia)) as [d' [p' [t3 (E3 & F3 & L3 & P3)]]].
    rewrite E3. rewrite pad_exact by lia.
    exists (t1 ++ CHR_dot :: t3 ++ zrepeat CHR_0 (p' + 9 - 9)). unfold out. split; [rewrite <- !app_assoc; reflexivity|].
    exists t1, (CHR_dot :: t3 ++ zrepeat CHR_0 (p' + 9 - 9)). split; [reflexivity|]. split; [apply nonnil_of_zlength; lia|]. split; [exact F1|].
    right. exists (t3 ++ zrepeat CHR_0 (p' + 9 - 9)). split; [reflexivity|]. split.
    + apply nonnil_of_zlength. rewrite zlength_app, zlength_zrepeat'. lia.
    + apply Forall_app. split; [exact F3| apply Forall_isdig_zrepeat0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma emit_e_shape : forall o big a z p ebuf0 estr k, W9 big -> 0 <= a -> a < z -> z <= 128 -> 0 <= p <= 40 ->
  DIGk (znth big a) k -> 1 <= k <= 9 -> 0 <= estr <= 12 -> zlength ebuf0 = 12 ->
  exists d t2, fmt_fp_emit_e o big a z p 0 ebuf0 estr = Some (o ++ (d :: t2) ++ zsub ebuf0 estr (12 - estr)) /\ isdig d /\ frac_shape t2.
Proof.
  intros o big a z p ebuf0 estr k WB Ha Haz Hz Hp D Hk He HLe. unfold fmt_fp_emit_e.
  replace (z <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  change BIG_FUEL with (S 129%nat). rewrite eloop_S.
  replace ((a <? z) && (0 <=? p)) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Z.leb_le; lia]. }
  unfold fmt_fp_eloop_body at 1.
  pose proof (WB a) as Wa.
  destruct (fmt_u_spec (znth big a) (zrepeat 0 37) 9 k ltac:(lia) D ltac:(lia)) as [b1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  replace (9 - k =? 9) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Z.eqb_refl. cbn [negb]. change (Z.land 0 ALT_FORM =? 0) with true. cbn [negb]. rewrite Bool.orb_false_r.
  assert (Ed : exists d, zsub b1 (9 - k) 1 = [d] /\ isdig d).
  { pose proof (zsub_length b1 (9 - k) 1 ltac:(lia) ltac:(lia) ltac:(lia)) as LL.
    assert (F0 : Forall isdig (zsub b1 (9 - k) 1)) by (apply zsub_Forall; try lia; intros i Hi; apply D1; lia).
    destruct (zsub b1 (9 - k) 1) as [|d [|d2 r]]; cbn in LL; try lia.
    exists d. split; [reflexivity|]. inversion F0; assumption. }
  destruct Ed as [d (Ed & Dd)].
  set (tf := zsub b1 (9 - k + 1) (Z.min (9 - (9 - k + 1)) p)).
  assert (F2 : Forall isdig tf) by (apply zsub_Forall; try lia; intros i Hi; apply D1; lia).
  assert (L2 : zlength tf = Z.min (k - 1) p) by (unfold tf; rewrite zlength_zsub by lia; lia).
  unfold out. rewrite Ed. fold tf.
  destruct (Z.ltb_spec 0 p) as [P1|P1].
  - destruct (eloop_rest_spec 129%nat big a z (a + 1) (p - (9 - (9 - k + 1))) (((o ++ [d]) ++ [CHR_dot]) ++ tf) WB ltac:(lia) ltac:(lia) ltac:(lia))
      as [d' [p' [t4 (E4 & F4 & L4 & P4)]]].
    rewrite E4. rewrite pad_exact by lia.
    exists d, (CHR_dot :: tf ++ t4 ++ zrepeat CHR_0 (p' + 18 - 18)). split; [unfold out; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; reflexivity|].
    split; [exact Dd|]. right. exists (tf ++ t4 ++ zrepeat CHR_0 (p' + 18 - 18)). split; [reflexivity|]. split.
    + apply nonnil_of_zlength. rewrite !zlength_app, zlength_zrepeat', L2, L4. lia.
    + apply Forall_app. split; [exact F2|]. apply Forall_app. split; [exact F4| apply Forall_isdig_zrepeat0].
  - destruct (eloop_rest_spec 129%nat big a z (a + 1) (p - (9 - (9 - k + 1))) ((o ++ [d]) ++ tf) WB ltac:(lia) ltac:(lia) ltac:(lia))
      as [d' [p' [t4 (E4 & F4 & L4 & P4)]]].
    rewrite E4. rewrite pad_exact by lia.
    exists d, (tf ++ t4 ++ zrepeat CHR_0 (p' + 18 - 18)). split; [unfold out; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; reflexivity|].
    split; [exact Dd|]. left. apply nil_of_zlength. rewrite !zlength_app, zlength_zrepeat', L2, L4. lia.
Qed.

(* [comment removed for export] *)
Lemma len_e_shape : forall l e, 0 <= l <= 100 -> -9999 <= e <= 9999 ->
  exists estr eb, fmt_fp_len 101 l e = Some (Cont (l + (12 - estr), eb, estr)) /\ 4 <= 12 - estr <= 6 /\ zlength eb = 12 /\
    exists es ed, zsub eb estr (12 - estr) = 101 :: es :: ed /\ (es = CHR_plus \/ es = CHR_minus) /\ ed <> [] /\ Forall isdig ed.
Proof.
  intros l e Hl He. unfold fmt_fp_len. change (Z.lor 101 32 =? CHR_f) with false. cbv iota.
  set (ea := if e <? 0 then - e else e).
  assert (Hea : 0 <= ea < 10^4) by (subst ea; destruct (Z.ltb_spec e 0); lia).
  destruct (DIGk_exists ea 4 Hea ltac:(lia)) as [ke [Dk Hke]].
  destruct (fmt_u_spec ea (zrepeat 0 12) 12 ke ltac:(lia) Dk ltac:(lia)) as [eb1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  destruct (epad_spec (12 - ke) eb1 ltac:(lia) L1) as [eb2 (E2 & L2 & G1 & G2)]. rewrite E2.
  replace (INT_MAX - l <? 12 - (Z.min (12 - ke) 10 - 1 - 1)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
  eexists _, _. split; [reflexivity|]. split; [lia|]. split; [rewrite !zlength_zupd; exact L2|].
  set (s0 := Z.min (12 - ke) 10 - 1 - 1).
  set (eb := zupd (zupd eb2 (Z.min (12 - ke) 10 - 1) (if e <? 0 then CHR_minus else CHR_plus)) s0 (u8 101)).
  assert (Leb : zlength eb = 12) by (unfold eb; rewrite !zlength_zupd; exact L2).
  assert (Z1 : znth eb s0 = 101) by (unfold eb; rewrite znth_zupd_eq by (rewrite zlength_zupd, L2; unfold s0; lia); reflexivity).
  assert (Z2 : znth eb (s0 + 1) = if e <? 0 then CHR_minus else CHR_plus).
  { unfold eb. rewrite znth_zupd_neq by (unfold s0; lia). replace (s0 + 1) with (Z.min (12 - ke) 10 - 1) by (unfold s0; lia).
    rewrite znth_zupd_eq by (rewrite L2; lia). reflexivity. }
  rewrite (zsub_cons eb s0) by (unfold s0; lia). rewrite (zsub_cons eb (s0 + 1)) by (unfold s0; lia).
  rewrite Z1, Z2. exists (if e <? 0 then CHR_minus else CHR_plus), (zsub eb (s0 + 1 + 1) (12 - s0 - 1 - 1)).
  split; [reflexivity|]. split; [destruct (e <? 0); [right|left]; reflexivity|]. split.
  - apply nonnil_of_zlength. rewrite zlength_zsub by (unfold s0; lia). unfold s0; lia.
  - apply zsub_Forall; try (unfold s0; lia). intros i Hi. unfold eb.
    rewrite znth_zupd_neq by (unfold s0 in *; lia). rewrite znth_zupd_neq by (unfold s0 in *; lia).
    destruct (Z.lt_ge_cases i (12 - ke)); [rewrite G1 by (unfold s0 in *; lia); apply isdig_0 | rewrite G2 by lia; apply D1; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem H_shape : forall o p1 prefix pl r0 big a z e,
  TS r0 big a z e -> znth big a <> 0 -> 1 <= p1 <= 26 -> 0 <= pl -> 0 <= prefix -> prefix + pl <= 18 ->
  exists txt l', g_H o 1 0 CHR_g p1 prefix pl big a r0 z e = Some (o ++ zsub PREFIX_STR prefix pl ++ txt, pl + l') /\ (f_body txt \/ e_body txt).
Proof.
  intros o p1 prefix pl r0 big a z e HT NZ Hp Hpl Hpr Hpp.
  pose proof HT as (WB & LB & AZ & Z7 & ZB & R & [k (Hk & Hka & He)]).
  assert (Hr0 : 0 <= r0 <= 122) by (destruct R as [->|[-> _]]; lia).
  unfold g_H.
  destruct (strip_spec big a z ltac:(lia) ltac:(lia) NZ) as [z' (Es & Hz' & Zs & NZs)]. rewrite Es.
  change (Z.lor CHR_g 32 =? CHR_g) with true. cbv iota.
  replace (p1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (Z.land 0 ALT_FORM =? 0) with true.
  replace ((a <? z') && negb (znth big (z' - 1) =? 0)) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Bool.negb_true_iff, Z.eqb_neq; exact NZs]. }
  pose proof (WB (z' - 1)) as Wz.
  destruct (fmt_fp_tz_total (znth big (z' - 1)) ltac:(unfold NB in Wz; lia)) as [it [jt Et]]. rewrite Et.
  assert (PL : zlength (zsub PREFIX_STR prefix pl) = pl) by (apply zlength_zsub; [lia|lia| unfold PREFIX_STR, zlength; cbn [length]; lia]).
  destruct ((e <? p1) && (-4 <=? e)) eqn:CF.
  - (* [comment removed for export] *)
    apply andb_prop in CF. destruct CF as [CF1 CF2]. apply Z.ltb_lt in CF1. apply Z.leb_le in CF2.
    change (Z.lor (CHR_g - 1) 32 =? CHR_f) with true. cbv iota.
    set (p2 := Z.min (p1 - (e + 1)) (Z.max 0 (9 * (z' - r0 - 1) - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - (e + 1)) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 1) with 102. rewrite len_f_spec by lia.
    set (l2 := if 0 <? e then 1 + p2 + palt + e else 1 + p2 + palt).
    assert (Hl2 : l2 = 1 + p2 + palt + Z.max e 0 /\ 1 <= l2 <= p1 + 7) by (subst l2; destruct (Z.ltb_spec 0 e); lia).
    destruct Hl2 as [El2 Bl2]. clearbody l2.
    replace (INT_MAX - pl <? l2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 102 32 =? CHR_f) with true. cbv iota.
    destruct (emit_f_shape (out o (zsub PREFIX_STR prefix pl)) big a r0 z' p2 k WB) as [txt (Ef & Sf)]; try lia.
    { intros Hra. apply ZB. lia. }
    { right. split; [lia| exact Hka]. }
    rewrite Ef. rewrite pad_flag by (cbv; discriminate).
    exists txt, l2. unfold out. rewrite <- app_assoc.
    split; [f_equal; f_equal; lia|]. left. exact Sf.
  - (* [comment removed for export] *)
    change (Z.lor (CHR_g - 2) 32 =? CHR_f) with false. cbv iota.
    set (p2 := Z.min (p1 - 1) (Z.max 0 (9 * (z' - r0 - 1) + e - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - 1) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 2) with 101.
    pose proof (TS_e_bound _ _ _ _ _ HT) as EB.
    destruct (len_e_shape (1 + p2 + palt) e ltac:(lia) ltac:(lia)) as [estr [eb (El & Hest & Leb & es & ed & Eeb & Hes & Ned & Fed)]]. rewrite El.
    replace (INT_MAX - pl <? 1 + p2 + palt + (12 - estr)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 101 32 =? CHR_f) with false. cbv iota.
    destruct (emit_e_shape (out o (zsub PREFIX_STR prefix pl)) big a z' p2 eb estr k WB) as [d [t2 (Ee & Dd & Ft2)]]; try lia.
    { right. split; [lia| exact Hka]. }
    rewrite Ee. rewrite pad_flag by (cbv; discriminate).
    exists ((d :: t2) ++ zsub eb estr (12 - estr)), (1 + p2 + palt + (12 - estr)). unfold out. rewrite <- !app_assoc.
    split; [f_equal; f_equal; lia|]. right.
    exists d, t2, es, ed. split; [rewrite Eeb; reflexivity|]. split; [exact Dd|]. split; [exact Ft2|]. split; [exact Hes|]. split; [exact Ned| exact Fed].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gshape_of : forall prefix pl body, (prefix = 0 /\ pl = 1) \/ (prefix = 1 /\ pl = 0) -> f_body body \/ e_body body ->
  gshape (zsub PREFIX_STR prefix pl ++ body).
Proof.
  intros prefix pl body PP B. exists (zsub PREFIX_STR prefix pl), body. split; [reflexivity|]. split; [|exact B].
  destruct PP as [[-> ->]|[-> ->]]; [right|left]; reflexivity.
Qed.

Theorem fmt_fp_g_shape : forall d p1, dfin d -> (p1 = 15 \/ p1 = 17) ->
  exists txt l, fmt_fp [] (f128_of_d d) 1 p1 0 CHR_g = Some (txt, l) /\ gshape txt.
Proof.
  intros d p1 Hfin Hp.
  destruct (fmt_loops d p1 CHR_g Hfin ltac:(lia) ltac:(cbv; discriminate))
    as [nz [fr [e0 [y2 (C1 & C2 & C3 & C4 & REST)]]]].
  cbv zeta in REST. destruct REST as (He2 & [big [z (ED & Hz & WB & LB & ZO & W0 & ZC & [s1 (EU & HS1 & DS1 & ZS1 & [big2 [a2 [z2 (EDN & PN & PZ)]]])])]]).
  rewrite fmt_fp_split, ffp_sign_0.
  set (sb := negb (signbitl (f128_of_d d) =? 0)).
  assert (Y1 : forall prefix pl, (if sb then (Z.lxor (f128_of_d d) F128_SIGNBIT, 0, 1) else (f128_of_d d, 1, 0)) = (strip_sign (f128_of_d d), prefix, pl) ->
     exists txt l, ffp_C [] 1 0 CHR_g (strip_sign (f128_of_d d)) p1 prefix pl = Some (txt, l) /\ gshape txt).
  2:{ assert (SS : strip_sign (f128_of_d d) = if sb then Z.lxor (f128_of_d d) F128_SIGNBIT else f128_of_d d) by reflexivity.
      destruct sb.
      - destruct (Y1 0 1) as [txt [l (E & S)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, l. split; [reflexivity| exact S].
      - destruct (Y1 1 0) as [txt [l (E & S)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, l. split; [reflexivity| exact S]. }
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
    destruct (H_shape [] p1 prefix pl r0 bigR aR zR eR TSR NZR) as [txt [l' (EH & S)]]; try lia.
    rewrite EH. exists (zsub PREFIX_STR prefix pl ++ txt), (pl + l'). split; [reflexivity|]. apply gshape_of; assumption.
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
    assert (F0 : f_body [48] \/ e_body [48]).
    { left. exists [48], []. split; [reflexivity|]. split; [discriminate|]. split; [constructor; [unfold isdig; lia| constructor]| left; reflexivity]. }
    destruct Hp as [-> | ->]; destruct PP as [[-> ->]|[-> ->]].
    + rewrite G15a. exists [45; 48], 2. split; [reflexivity|]. exact (gshape_of 0 1 [48] ltac:(left; lia) F0).
    + rewrite G15b. exists [48], 1. split; [reflexivity|]. exact (gshape_of 1 0 [48] ltac:(right; lia) F0).
    + rewrite G17a. exists [45; 48], 2. split; [reflexivity|]. exact (gshape_of 0 1 [48] ltac:(left; lia) F0).
    + rewrite G17b. exists [48], 1. split; [reflexivity|]. exact (gshape_of 1 0 [48] ltac:(right; lia) F0).
Qed.

(* [comment removed for export] *)
Theorem fmt_fp_g_shape_of : forall d prec o l, (prec = 15 \/ prec = 17) -> dfin d ->
  fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> gshape o.
Proof.
  intros d prec o l Hp Hfin E. destruct (fmt_fp_g_shape d prec Hfin Hp) as [txt [l' (E' & S)]].
  rewrite E in E'. injection E' as -> _. exact S.
Qed.
