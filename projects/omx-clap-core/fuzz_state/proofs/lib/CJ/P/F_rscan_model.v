(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require FloatScan.
Module F_rscan_facts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.Prelim OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.FloatScan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> P 0 -> P (znth l i).
Proof.
  intros P l i HF H0. unfold znth. destruct (i <? 0); [exact H0|].
  revert HF. generalize (Z.to_nat i) as n. intros n HF. revert n.
  induction HF as [|a l Ha HF IH]; intros [|n]; cbn; auto.
Qed.

Definition FB (f : shfile) : Prop := Forall (fun c => 0 <= c < 256) (sh_buf f).

Lemma sh_getc_char : forall f, FB f -> -1 <= fst (sh_getc f) < 256 /\ FB (snd (sh_getc f)).
Proof.
  intros f HB. unfold sh_getc.
  assert (R : 0 <= znth (sh_buf f) (sh_rpos f) < 256) by (apply (Forall_znth (fun c => 0 <= c < 256)); [exact HB | lia]).
  destruct (negb (sh_stdio f)); [cbn; split; [lia | exact HB]|].
  destruct (negb (sh_rpos f =? sh_n f)); cbn; (split; [lia | exact HB]).
Qed.

Lemma sh_unget_FB : forall f, FB f -> FB (sh_unget f).
Proof. intros f HB. unfold sh_unget. destruct (negb (sh_shlim_neg f)); [exact HB | exact HB]. Qed.

Lemma isdigitc_range : forall c, -1 <= c < 256 -> isdigitc c = true -> 48 <= c <= 57.
Proof. intros c Hc H. unfold isdigitc, u32 in H. apply Z.ltb_lt in H. Z.div_mod_to_equations. lia. Qed.

Lemma scanexp_l1_inv : forall n v c f v' c' f',
  scanexp_l1_loop n (v, c, f) = Some (v', c', f') -> FB f -> -1 <= c < 256 -> 0 <= v <= 2^31 ->
  0 <= v' <= 2^31 /\ FB f' /\ -1 <= c' < 256.
Proof.
  induction n as [|n IH]; intros v c f v' c' f' HL HB Hc Hv; [discriminate HL|].
  cbn [scanexp_l1_loop] in HL. unfold scanexp_l1_cond in HL at 1.
  destruct (isdigitc c) eqn:Hd; cbn [andb] in HL.
  - destruct (Z.ltb_spec v (Z.quot INT_MAX_ 10)) as [Hlt|Hge].
    + unfold scanexp_l1_body in HL. destruct (sh_getc f) as [c2 f2] eqn:G.
      pose proof (sh_getc_char f HB) as [R2 B2]. rewrite G in R2, B2. cbn [fst snd] in R2, B2.
      pose proof (isdigitc_range c Hc Hd). change (Z.quot INT_MAX_ 10) with 214748364 in Hlt.
      eapply IH; [exact HL | exact B2 | exact R2 | lia].
    + injection HL as <- <- <-. auto.
  - injection HL as <- <- <-. auto.
Qed.

Lemma scanexp_l2_inv : forall n v c f v' c' f',
  scanexp_l2_loop n (v, c, f) = Some (v', c', f') -> FB f -> -1 <= c < 256 -> 0 <= v <= 2^60 ->
  0 <= v' <= 2^60 /\ FB f' /\ -1 <= c' < 256.
Proof.
  induction n as [|n IH]; intros v c f v' c' f' HL HB Hc Hv; [discriminate HL|].
  cbn [scanexp_l2_loop] in HL. unfold scanexp_l2_cond in HL at 1.
  destruct (isdigitc c) eqn:Hd; cbn [andb] in HL.
  - destruct (Z.ltb_spec v (Z.quot LLONG_MAX_ 100)) as [Hlt|Hge].
    + unfold scanexp_l2_body in HL. destruct (sh_getc f) as [c2 f2] eqn:G.
      pose proof (sh_getc_char f HB) as [R2 B2]. rewrite G in R2, B2. cbn [fst snd] in R2, B2.
      pose proof (isdigitc_range c Hc Hd). change (Z.quot LLONG_MAX_ 100) with 92233720368547758 in Hlt.
      eapply IH; [exact HL | exact B2 | exact R2 | lia].
    + injection HL as <- <- <-. auto.
  - injection HL as <- <- <-. auto.
Qed.

Lemma scanexp_l3_inv : forall n c f c' f',
  scanexp_l3_loop n (c, f) = Some (c', f') -> FB f -> FB f'.
Proof.
  induction n as [|n IH]; intros c f c' f' HL HB; [discriminate HL|].
  cbn [scanexp_l3_loop] in HL. destruct (isdigitc c).
  - unfold scanexp_l3_body in HL. destruct (sh_getc f) as [c2 f2] eqn:G.
    pose proof (sh_getc_char f HB) as [_ B2]. rewrite G in B2. cbn [snd] in B2. eapply IH; [exact HL | exact B2].
  - injection HL as <- <-. exact HB.
Qed.

(* [comment removed for export] *)
Lemma scanexp_bound : forall fuel f pok f' e,
  Forall (fun c => 0 <= c < 256) (sh_buf f) ->
  scanexp fuel f pok = Some (f', e) -> e = LLONG_MIN_ \/ -2^60 <= e <= 2^60.
Proof.
  intros fuel f pok f' e HB HS. unfold scanexp in HS.
  destruct (sh_getc f) as [c1 f1] eqn:G1.
  pose proof (sh_getc_char f HB) as [R1 B1]. rewrite G1 in R1, B1. cbn [fst snd] in R1, B1.
  match type of HS with (match ?hd with _ => _ end) = _ =>
    destruct hd as [[neg c2] f2] eqn:Ehd end.
  assert (RB : -1 <= c2 < 256 /\ FB f2).
  { destruct ((c1 =? 43) || (c1 =? 45)).
    - destruct (sh_getc f1) as [c3 f3] eqn:G2.
      pose proof (sh_getc_char f1 B1) as [R2 B2]. rewrite G2 in R2, B2. cbn [fst snd] in R2, B2.
      injection Ehd as <- <- <-. split; [exact R2|]. destruct (negb (isdigitc c3) && nz pok); [apply sh_unget_FB; exact B2 | exact B2].
    - injection Ehd as <- <- <-. split; [exact R1 | exact B1]. }
  destruct RB as [Rc2 B2]. clear Ehd.
  destruct (negb (isdigitc c2)). { injection HS as _ <-. left. reflexivity. }
  destruct (scanexp_l1_loop fuel (0, c2, f2)) as [[[x c3] f3]|] eqn:L1; [|discriminate HS].
  destruct (scanexp_l1_inv _ _ _ _ _ _ _ L1 B2 Rc2 ltac:(lia)) as (Rx & B3 & Rc3).
  destruct (scanexp_l2_loop fuel (x, c3, f3)) as [[[y c4] f4]|] eqn:L2; [|discriminate HS].
  destruct (scanexp_l2_inv _ _ _ _ _ _ _ L2 B3 Rc3 ltac:(lia)) as (Ry & B4 & Rc4).
  destruct (scanexp_l3_loop fuel (c4, f4)) as [[c5 f5]|]; [|discriminate HS].
  injection HS as _ <-. right. unfold nz. destruct (negb (neg =? 0)); lia.
Qed.

(* [comment removed for export] *)
Lemma sh_getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f /\ sh_buf (snd (sh_getc f)) = sh_buf f.
Proof. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; auto|]. destruct (negb _); cbn; auto. Qed.
Lemma sh_unget_stdio : forall f, sh_stdio (sh_unget f) = sh_stdio f /\ sh_buf (sh_unget f) = sh_buf f.
Proof. intros f. unfold sh_unget. destruct (negb (sh_shlim_neg f)); cbn; auto. Qed.

Lemma scanexp_l1_stdio : forall n v c f v' c' f',
  scanexp_l1_loop n (v, c, f) = Some (v', c', f') -> sh_stdio f' = sh_stdio f /\ sh_buf f' = sh_buf f.
Proof.
  induction n as [|n IH]; intros v c f v' c' f' HL; [discriminate HL|].
  cbn [scanexp_l1_loop] in HL. destruct (scanexp_l1_cond (v, c, f)).
  - unfold scanexp_l1_body in HL. destruct (sh_getc f) as [c2 f2] eqn:G.
    pose proof (sh_getc_stdio f) as [S1 B1]. rewrite G in S1, B1. cbn [snd] in S1, B1.
    destruct (IH _ _ _ _ _ _ HL) as [S2 B2]. rewrite S2, B2. auto.
  - injection HL as <- <- <-. auto.
Qed.

Lemma scanexp_stdio : forall fuel f pok f' e,
  scanexp fuel f pok = Some (f', e) -> sh_stdio f' = sh_stdio f /\ sh_buf f' = sh_buf f.
Proof.
  intros fuel f pok f' e HS. unfold scanexp in HS.
  destruct (sh_getc f) as [c1 f1] eqn:G1.
  pose proof (sh_getc_stdio f) as [S1 B1]. rewrite G1 in S1, B1. cbn [snd] in S1, B1.
  match type of HS with (match ?hd with _ => _ end) = _ => destruct hd as [[neg c2] f2] eqn:Ehd end.
  assert (SB2 : sh_stdio f2 = sh_stdio f /\ sh_buf f2 = sh_buf f).
  { destruct ((c1 =? 43) || (c1 =? 45)).
    - destruct (sh_getc f1) as [c3 f3] eqn:G2.
      pose proof (sh_getc_stdio f1) as [S2 B2]. rewrite G2 in S2, B2. cbn [snd] in S2, B2.
      injection Ehd as <- <- <-. destruct (negb (isdigitc c3) && nz pok).
      + destruct (sh_unget_stdio f3) as [S3 B3]. rewrite S3, B3, S2, B2. auto.
      + rewrite S2, B2. auto.
    - injection Ehd as <- <- <-. auto. }
  destruct SB2 as [S2 B2]. clear Ehd.
  destruct (negb (isdigitc c2)).
  { injection HS as <- _. destruct (sh_unget_stdio f2) as [S3 B3]. rewrite S3, B3. auto. }
  destruct (scanexp_l1_loop fuel (0, c2, f2)) as [[[x c3] f3]|] eqn:L1; [|discriminate HS].
  destruct (scanexp_l1_stdio _ _ _ _ _ _ _ L1) as [S3 B3].
  destruct (scanexp_l2_loop fuel (x, c3, f3)) as [[[y c4] f4]|] eqn:L2; [|discriminate HS].
  assert (SB4 : sh_stdio f4 = sh_stdio f3 /\ sh_buf f4 = sh_buf f3).
  { revert L2. generalize y c4 f4 x c3 f3. clear. induction fuel as [|n IH]; intros y c4 f4 x c3 f3 HL; [discriminate HL|].
    cbn [scanexp_l2_loop] in HL. destruct (scanexp_l2_cond (x, c3, f3)).
    - unfold scanexp_l2_body in HL. destruct (sh_getc f3) as [c5 f5] eqn:G.
      pose proof (sh_getc_stdio f3) as [S5 B5]. rewrite G in S5, B5. cbn [snd] in S5, B5.
      destruct (IH _ _ _ _ _ _ HL) as [S6 B6]. rewrite S6, B6. auto.
    - injection HL as <- <- <-. auto. }
  destruct SB4 as [S4 B4].
  destruct (scanexp_l3_loop fuel (c4, f4)) as [[c5 f5]|] eqn:L3; [|discriminate HS].
  assert (SB5 : sh_stdio f5 = sh_stdio f4 /\ sh_buf f5 = sh_buf f4).
  { revert L3. generalize c5 f5 c4 f4. clear. induction fuel as [|n IH]; intros c5 f5 c4 f4 HL; [discriminate HL|].
    cbn [scanexp_l3_loop] in HL. destruct (isdigitc c4).
    - unfold scanexp_l3_body in HL. destruct (sh_getc f4) as [c6 f6] eqn:G.
      pose proof (sh_getc_stdio f4) as [S6 B6]. rewrite G in S6, B6. cbn [snd] in S6, B6.
      destruct (IH _ _ _ _ HL) as [S7 B7]. rewrite S7, B7. auto.
    - injection HL as <- <-. auto. }
  destruct SB5 as [S5 B5].
  injection HS as <- _. destruct (sh_unget_stdio f5) as [S6 B6]. rewrite S6, B6, S5, B5, S4, B4, S3, B3, S2, B2. auto.
Qed.
End F_rscan_facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import Prelim SoftFloat FloatScan FloatScanProps.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import FmtFp_facts3.
Import F_rscan_facts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Lemma znth_In' : forall (l : list Z) i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i Hi. unfold znth. destruct (i <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
  apply nth_In. unfold zlength in Hi. lia.
Qed.


Lemma znth_app_mid : forall (pre post : list Z), znth (pre ++ 0 :: post)%Z (Z.of_nat (length pre)) = 0%Z.
Proof. intros pre post. rewrite znth_app_r by (unfold zlength; lia). unfold zlength. rewrite Z.sub_diag. reflexivity. Qed.
Lemma znth_app_pre : forall (pre post : list Z) i, (0 <= i < Z.of_nat (length pre))%Z -> znth (pre ++ 0 :: post)%Z i = znth pre i.
Proof. intros pre post i Hi. apply znth_app_l. unfold zlength. lia. Qed.

Section Model.
  Variables (txt : list Z) (p : Z).
  Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Hypothesis Hp : (0 <= p < zlength txt)%Z.
  Hypothesis Hnul : znth txt p = 0%Z.
  Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.

  Lemma numch_facts : forall i, (0 <= i < p)%Z -> let c := znth txt i in (43 <= c <= 57 \/ c = 69 \/ c = 101)%Z.
  Proof.
    clear -Hnum. intros i Hi. pose proof (Hnum i Hi) as E. cbv zeta. unfold is_numch in E.
    repeat (apply Bool.orb_true_iff in E; destruct E as [E|E]); try (apply Z.eqb_eq in E; lia).
    apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  Qed.

  (* [comment removed for export] *)
  Definition okch (c : Z) : Prop := (43 <= c <= 57 \/ c = 69 \/ c = 101 \/ c = 0 \/ c = -1)%Z.

  Lemma fs_ws_loop_step : forall n f, fs_ws_loop (S n) f = (let '(c, f') := sh_getc f in if m_isspace c then fs_ws_loop n f' else Some (c, f')).
  Proof. clear. intros. cbn [fs_ws_loop]. destruct (sh_getc f). reflexivity. Qed.
  Lemma okch_cases : forall c, okch c ->
    m_isspace c = false /\ (Z.lor c 32 =? 105) = false /\ (Z.lor c 32 =? 110) = false /\ c <> 32%Z /\ ~ (9 <= c <= 13)%Z.
  Proof.
    clear. intros c Hc. unfold okch in Hc.
    assert (E : (c = -1 \/ c = 0 \/ c = 43 \/ c = 44 \/ c = 45 \/ c = 46 \/ c = 47 \/ c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/ c = 53
                 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57 \/ c = 69 \/ c = 101)%Z) by lia.
    clear Hc.
    repeat (destruct E as [E|E]; [subst c; split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | lia]]] |]).
    subst c; split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | lia]]].
  Qed.
  Lemma fs_inf_nil : forall c f, (Z.lor c 32 =? 105) = false -> fs_inf_loop 9 (0%Z, c, f) = Some (0%Z, c, f).
  Proof. clear. intros c f H. cbn [fs_inf_loop fs_inf_cond]. change (znth str_infinity 0) with 105%Z. rewrite H. reflexivity. Qed.
  Lemma fs_nan_nil : forall c f, (Z.lor c 32 =? 110) = false -> fs_nan_loop 4 (0%Z, c, f) = Some (0%Z, c, f).
  Proof. clear. intros c f H. cbn [fs_nan_loop fs_nan_cond]. change (znth str_nan 0) with 110%Z. rewrite H. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma dfK_dn_f : forall sg f rp a z e2 x f' y, dfK_dn 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
  Proof.
    clear. intros until y. unfold dfK_dn. destruct (df_dn_loop _ _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate].
    destruct (df_final _ _ _ _ _ _ _ _ _ _); [|discriminate]. intros H. injection H as <- _. reflexivity.
  Qed.
  Lemma dfK_up_f : forall sg f rp a z e2 x f' y, dfK_up 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
  Proof. clear. intros until y. unfold dfK_up. destruct (df_up_loop _ _) as [[rp2 a2 z2 e22 x2]|]; [|discriminate]. apply dfK_dn_f. Qed.
  Lemma dfK_al_f : forall sg f rp z x f' y, dfK_al 53 (-1074) sg f rp z x = Some (f', y) -> f' = f.
  Proof.
    clear. intros until y. unfold dfK_al.
    destruct (if nz (Z.rem rp 9) then _ else _) as [[[[a2 z2] rp2] x2]|]; [|discriminate]. apply dfK_up_f.
  Qed.
  Lemma dfK_tz_f : forall sg f rp k x f' y, dfK_tz 53 (-1074) sg f rp k x = Some (f', y) -> f' = f.
  Proof. clear. intros until y. unfold dfK_tz. destruct (df_tz_loop _ _ _); [|discriminate]. apply dfK_al_f. Qed.
  Lemma dfK_mid_f : forall sg f rp lnz k x f' y, dfK_mid 53 (-1074) sg f rp lnz k x = Some (f', y) -> f' = f.
  Proof.
    clear. intros until y. unfold dfK_mid.
    destruct (_ && _ && _)%Z; cbv beta iota zeta; [|apply dfK_tz_f].
    destruct (rp =? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
    destruct (rp <? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
    destruct (_ || _); cbv beta iota. { intros H; injection H as <- _; reflexivity. }
    apply dfK_tz_f.
  Qed.
  Lemma dfK_pad_f : forall sg f lrp lnz j k x f' y, dfK_pad 53 (-1074) sg f lrp lnz j k x = Some (f', y) -> f' = f.
  Proof.
    clear. intros until y. unfold dfK_pad. destruct (if nz j then _ else _) as [[k2 x2]|]; [|discriminate]. apply dfK_mid_f.
  Qed.
  Lemma dfK_rng_f : forall sg f lrp dc lnz j k x f' y, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f', y) -> f' = f.
  Proof.
    clear. intros until y. unfold dfK_rng.
    destruct (znth x 0 =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
    destruct (_ && _ && _); [intros H; injection H as <- _; reflexivity|].
    destruct (_ <? lrp)%Z; [intros H; injection H as <- _; reflexivity|].
    destruct (lrp <? _)%Z; [intros H; injection H as <- _; reflexivity|].
    apply dfK_pad_f.
  Qed.

  (* [comment removed for export] *)
  Lemma dfK_rng_f' : forall {sg f lrp dc lnz j k x f2 y}, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f2, y) -> f = f2.
  Proof. clear. intros. symmetry. exact (dfK_rng_f sg _ _ _ _ _ _ _ _ _ H). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition JF (k c : Z) (f : shfile) : Prop :=
    (sh_buf f = txt /\ sh_cnt0 f = 0 /\ 0 <= sh_rpos f /\ -1 <= c /\
     (sh_shlim_neg f = false -> k <= sh_rpos f) /\
     (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0 -> sh_rpos f <= p) /\ 0 <= c) /\
     (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p)))%Z.
  (* [comment removed for export] *)
  Definition JR (f : shfile) : Prop := (0 <= sh_cnt0 f <= sh_rpos f /\ sh_rpos f <= p)%Z.

  Ltac crush_jf := repeat (repeat split; try reflexivity; try discriminate; try lia;
                           lazymatch goal with |- (_ -> _) => intro | |- _ => fail end).
  Lemma JF_getc : forall k c f, JF k c f -> c <> 0%Z -> JF (k + 1) (fst (sh_getc f)) (snd (sh_getc f)).
  Proof.
    clear -Hp Hnul BYT. intros k c f J Hc.
    assert (R0 : forall i, (0 <= i)%Z -> (0 <= znth txt i)%Z).
    { intros i Hi. destruct (Z.lt_ge_cases i (zlength txt)) as [LT|GE].
      - exact (proj1 (proj1 (Forall_forall _ _) BYT _ (znth_In' txt _ (conj Hi LT)))).
      - rewrite znth_ge by exact GE. lia. }
    destruct f as [buf rpos cnt0 n st sn]. unfold JF, sh_getc in *. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *.
    (nelim J 7%nat; intros A B D0 Rc KM NS SS). subst buf cnt0.
    destruct st; cbn [negb].
    - (nelim (SS eq_refl) 3%nat; intros N1 N2 N3).
      destruct (Z.eqb_spec rpos n) as [E|NE]; cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
      + crush_jf.
      + pose proof (R0 _ D0).
        destruct sn; [specialize (N3 eq_refl); lia|]. specialize (KM eq_refl).
        crush_jf.
    - (nelim (NS eq_refl) 4%nat; intros N1 N2 N3 N4). specialize (N3 Hc). subst sn. specialize (KM eq_refl).
      cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. pose proof (R0 _ D0).
      crush_jf.
      all: destruct (Z.eq_dec rpos p) as [Ep|]; [|lia]; exfalso; subst rpos; rewrite Hnul in *; lia.
  Qed.
  Lemma JF_unget_any : forall k c f c', JF k c f -> (1 <= k)%Z -> (-1 <= c')%Z -> (sh_stdio f = false -> 0 <= c')%Z ->
    JF (k - 1) c' (sh_unget f) /\ JR (sh_unget f).
  Proof.
    clear. intros k c f c' J Hk Hc' Hc2.
    destruct f as [buf rpos cnt0 n st sn]. unfold JF, JR, sh_unget in *. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *.
    (nelim J 7%nat; intros A B D0 Rc KM NS SS). subst buf cnt0.
    destruct sn; cbn [negb sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    - destruct st.
      + (nelim (SS eq_refl) 3%nat; intros N1 N2 N3). specialize (N3 eq_refl). crush_jf.
      + destruct (NS eq_refl) as (N1 & _). discriminate N1.
    - specialize (KM eq_refl). destruct st.
      + (nelim (SS eq_refl) 3%nat; intros N1 N2 N3). crush_jf.
      + (nelim (NS eq_refl) 4%nat; intros N1 N2 N3 N4). specialize (Hc2 eq_refl). crush_jf.
  Qed.
  Lemma JR_lim0 : forall f, JR f -> JR (sh_lim0 f).
  Proof. clear. intros f R. unfold JR, sh_lim0 in *. cbn. lia. Qed.
  Lemma JF_weak : forall k k' c f, JF k c f -> (k' <= k)%Z -> JF k' c f.
  Proof. clear. intros k k' c f (A & B & D0 & Rc & KM & NS & SS) Hk. unfold JF. split; [exact A|]. split; [exact B|]. split; [exact D0|]. split; [exact Rc|].
         split; [intros X; specialize (KM X); lia|]. split; [exact NS | exact SS]. Qed.
  Lemma JF_neg_JR : forall k c f, JF k c f -> (c < 0)%Z -> JR f.
  Proof.
    clear. intros k c f (A & B & D0 & Rc & KM & NS & SS) Hc. unfold JR. destruct (sh_stdio f).
    - (nelim (SS eq_refl) 3%nat; intros N1 N2 N3). lia.
    - (nelim (NS eq_refl) 4%nat; intros N1 N2 N3 N4). lia.
  Qed.
  Lemma JF_okch : forall k c f, JF k c f -> c <> 0%Z -> okch (fst (sh_getc f)).
  Proof.
    clear -Hp Hnul Hnum. intros k c f J Hc.
    destruct f as [buf rpos cnt0 n st sn]. unfold JF, sh_getc, okch in *. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *.
    (nelim J 7%nat; intros A B D0 Rc KM NS SS). subst buf cnt0.
    destruct st; cbn [negb].
    - (nelim (SS eq_refl) 3%nat; intros N1 N2 N3).
      destruct (Z.eqb_spec rpos n) as [E|NE]; cbn [negb fst]; [lia|].
      pose proof (numch_facts rpos ltac:(lia)) as X. cbv zeta in X. lia.
    - (nelim (NS eq_refl) 4%nat; intros N1 N2 N3 N4). specialize (N3 Hc). cbn [fst].
      destruct (Z.eq_dec rpos p) as [Ep|Np]; [rewrite Ep, Hnul; lia|].
      pose proof (numch_facts rpos ltac:(lia)) as X. cbv zeta in X. lia.
  Qed.

  Lemma df_lz_J : forall n g c f g' c' f' k, df_lz_loop n (g, c, f) = Some (g', c', f') -> JF k c f -> (1 <= k)%Z -> exists k', JF k' c' f' /\ (1 <= k')%Z.
  Proof.
    clear -Hp Hnul BYT. induction n as [|n IH]; intros g c f g' c' f' k HL J Hk; [discriminate HL|].
    cbn [df_lz_loop] in HL. destruct (Z.eqb_spec c 48) as [Ec|Nc].
    - unfold df_lz_body in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
      pose proof (JF_getc k c f J ltac:(lia)) as J2. rewrite EG in J2. cbn [fst snd] in J2.
      eapply (IH _ _ _ _ _ _ (k + 1)%Z HL J2). lia.
    - injection HL as <- <- <-. exists k. split; [exact J | exact Hk].
  Qed.
  Lemma df_rz_J : forall n g l c f g' l' c' f' k, df_rz_loop n (g, l, c, f) = Some (g', l', c', f') -> JF k c f -> (1 <= k)%Z -> exists k', JF k' c' f' /\ (1 <= k')%Z.
  Proof.
    clear -Hp Hnul BYT. induction n as [|n IH]; intros g l c f g' l' c' f' k HL J Hk; [discriminate HL|].
    cbn [df_rz_loop] in HL. destruct (Z.eqb_spec c 48) as [Ec|Nc].
    - unfold df_rz_body in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
      pose proof (JF_getc k c f J ltac:(lia)) as J2. rewrite EG in J2. cbn [fst snd] in J2.
      eapply (IH _ _ _ _ _ _ _ _ (k + 1)%Z HL J2). lia.
    - injection HL as <- <- <- <-. exists k. split; [exact J | exact Hk].
  Qed.
  Lemma df_dig_J : forall n s s' k, df_dig_loop n s = Some s' -> JF k (dl_c s) (dl_f s) -> (1 <= k)%Z -> exists k', JF k' (dl_c s') (dl_f s') /\ (1 <= k')%Z.
  Proof.
    clear -Hp Hnul BYT. induction n as [|n IH]; intros s s' k HL J Hk; [discriminate HL|].
    cbn [df_dig_loop] in HL. unfold df_dig_cond in HL.
    destruct (isdigitc (dl_c s) || (dl_c s =? 46)) eqn:EC.
    - assert (Hc : dl_c s <> 0%Z).
      { intros E0. rewrite E0 in EC. cbv in EC. discriminate EC. }
      unfold df_dig_body in HL.
      destruct (dl_c s =? 46).
      + destruct (nz (dl_gotrad s)).
        * injection HL as <-. exists k. split; [exact J | exact Hk].
        * destruct (sh_getc (dl_f s)) as [c2 f2] eqn:EG.
          pose proof (JF_getc k _ _ J Hc) as J2. rewrite EG in J2. cbn [fst snd] in J2.
          eapply (IH _ _ (k + 1)%Z HL); [cbn; exact J2 | lia].
      + destruct (dl_k s <? KMAX - 3).
        * destruct (sh_getc (dl_f s)) as [c2 f2] eqn:EG.
          pose proof (JF_getc k _ _ J Hc) as J2. rewrite EG in J2. cbn [fst snd] in J2.
          revert HL. destruct (dl_j s + 1 =? 9); intros HL; (eapply (IH _ _ (k + 1)%Z HL); [cbn; exact J2 | lia]).
        * destruct (sh_getc (dl_f s)) as [c2 f2] eqn:EG.
          pose proof (JF_getc k _ _ J Hc) as J2. rewrite EG in J2. cbn [fst snd] in J2.
          revert HL. destruct (negb (dl_c s =? 48)); intros HL; (eapply (IH _ _ (k + 1)%Z HL); [cbn; exact J2 | lia]).
    - injection HL as <-. exists k. split; [exact J | exact Hk].
  Qed.
  Lemma scanexp_l1_J : forall n x c f x' c' f' k, scanexp_l1_loop n (x, c, f) = Some (x', c', f') -> JF k c f -> (2 <= k)%Z -> exists k', JF k' c' f' /\ (2 <= k')%Z.
  Proof.
    clear -Hp Hnul BYT. induction n as [|n IH]; intros x c f x' c' f' k HL J Hk; [discriminate HL|].
    cbn [scanexp_l1_loop] in HL. unfold scanexp_l1_cond in HL.
    destruct (isdigitc c) eqn:EC; cbn [andb] in HL.
    - assert (Hc : c <> 0%Z) by (intros E0; rewrite E0 in EC; cbv in EC; discriminate EC).
      destruct (x <? _).
      + unfold scanexp_l1_body in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
        pose proof (JF_getc k c f J Hc) as J2. rewrite EG in J2. cbn [fst snd] in J2.
        eapply (IH _ _ _ _ _ _ (k + 1)%Z HL J2). lia.
      + injection HL as <- <- <-. exists k. split; [exact J | exact Hk].
    - injection HL as <- <- <-. exists k. split; [exact J | exact Hk].
  Qed.
  Lemma scanexp_l2_J : forall n x c f x' c' f' k, scanexp_l2_loop n (x, c, f) = Some (x', c', f') -> JF k c f -> (2 <= k)%Z -> exists k', JF k' c' f' /\ (2 <= k')%Z.
  Proof.
    clear -Hp Hnul BYT. induction n as [|n IH]; intros x c f x' c' f' k HL J Hk; [discriminate HL|].
    cbn [scanexp_l2_loop] in HL. unfold scanexp_l2_cond in HL.
    destruct (isdigitc c) eqn:EC; cbn [andb] in HL.
    - assert (Hc : c <> 0%Z) by (intros E0; rewrite E0 in EC; cbv in EC; discriminate EC).
      destruct (x <? _).
      + unfold scanexp_l2_body in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
        pose proof (JF_getc k c f J Hc) as J2. rewrite EG in J2. cbn [fst snd] in J2.
        eapply (IH _ _ _ _ _ _ (k + 1)%Z HL J2). lia.
      + injection HL as <- <- <-. exists k. split; [exact J | exact Hk].
    - injection HL as <- <- <-. exists k. split; [exact J | exact Hk].
  Qed.
  Lemma scanexp_l3_J : forall n c f c' f' k, scanexp_l3_loop n (c, f) = Some (c', f') -> JF k c f -> (2 <= k)%Z -> exists k', JF k' c' f' /\ (2 <= k')%Z.
  Proof.
    clear -Hp Hnul BYT. induction n as [|n IH]; intros c f c' f' k HL J Hk; [discriminate HL|].
    cbn [scanexp_l3_loop] in HL.
    destruct (isdigitc c) eqn:EC.
    - assert (Hc : c <> 0%Z) by (intros E0; rewrite E0 in EC; cbv in EC; discriminate EC).
      unfold scanexp_l3_body in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
      pose proof (JF_getc k c f J Hc) as J2. rewrite EG in J2. cbn [fst snd] in J2.
      eapply (IH _ _ _ _ (k + 1)%Z HL J2). lia.
    - injection HL as <- <-. exists k. split; [exact J | exact Hk].
  Qed.
  (* [comment removed for export] *)
  Lemma scanexp_J : forall n f c pk f' e10 k, scanexp n f pk = Some (f', e10) -> JF k c f -> c <> 0%Z -> (1 <= k)%Z ->
    JR f' /\ JR (sh_unget f').
  Proof.
    clear -Hp Hnul BYT. intros n f c pk f' e10 k HS J Hc Hk. unfold scanexp in HS.
    destruct (sh_getc f) as [c1 f1] eqn:EG1.
    pose proof (JF_getc k c f J Hc) as J1. rewrite EG1 in J1. cbn [fst snd] in J1.
    assert (FIN : forall k2 c2 f2, JF k2 c2 f2 -> (2 <= k2)%Z -> JR (sh_unget f2) /\ JR (sh_unget (sh_unget f2))).
    { intros k2 c2 f2 J2 Hk2. destruct (JF_unget_any k2 c2 f2 0 J2 ltac:(lia) ltac:(lia) ltac:(intros; lia)) as [J3 R3]. split; [exact R3|].
      destruct (JF_unget_any _ _ _ 0 J3 ltac:(lia) ltac:(lia) ltac:(intros; lia)) as [_ R4]. exact R4. }
    destruct ((c1 =? 43) || (c1 =? 45)) eqn:ESG.
    - assert (Hc1 : c1 <> 0%Z) by (intros E0; rewrite E0 in ESG; cbv in ESG; discriminate ESG).
      destruct (sh_getc f1) as [c2 f2] eqn:EG2.
      pose proof (JF_getc _ _ _ J1 Hc1) as J2. rewrite EG2 in J2. cbn [fst snd] in J2.
      set (f3 := if negb (isdigitc c2) && nz pk then sh_unget f2 else f2) in HS.
      assert (J3 : JF (k + 1) c2 f3).
      { subst f3. destruct (negb (isdigitc c2) && nz pk); [| eapply JF_weak; [exact J2 | lia]].
        pose proof J2 as J2'. (nelim J2' 7%nat; intros _ _ _ Rc2 _ NS2 _).
        destruct (JF_unget_any _ _ _ c2 J2 ltac:(lia) Rc2 ltac:(intros X; (nelim (NS2 X) 4%nat; intros _ _ _ Y); exact Y)) as [J3 _]. eapply JF_weak; [exact J3 | lia]. }
      destruct (negb (isdigitc c2)).
      + injection HS as <- <-. exact (FIN _ _ _ J3 ltac:(lia)).
      + destruct (scanexp_l1_loop n (0%Z, c2, f3)) as [[[xa ca] fa]|] eqn:HL1; [|discriminate HS].
        (nelim (scanexp_l1_J _ _ _ _ _ _ _ _ HL1 J3 ltac:(lia)) 3%nat; intros ka Ja Hka).
        destruct (scanexp_l2_loop n (xa, ca, fa)) as [[[xb cb] fb]|] eqn:HL2; [|discriminate HS].
        (nelim (scanexp_l2_J _ _ _ _ _ _ _ _ HL2 Ja Hka) 3%nat; intros kb Jb Hkb).
        destruct (scanexp_l3_loop n (cb, fb)) as [[cc fcc]|] eqn:HL3; [|discriminate HS].
        (nelim (scanexp_l3_J _ _ _ _ _ _ HL3 Jb Hkb) 3%nat; intros kc Jc Hkc).
        injection HS as <- <-. exact (FIN _ _ _ Jc Hkc).
    - cbn [negb] in HS. destruct (negb (isdigitc c1)).
      + injection HS as <- <-. exact (FIN _ _ _ J1 ltac:(lia)).
      + destruct (scanexp_l1_loop n (0%Z, c1, f1)) as [[[xa ca] fa]|] eqn:HL1; [|discriminate HS].
        (nelim (scanexp_l1_J _ _ _ _ _ _ _ _ HL1 J1 ltac:(lia)) 3%nat; intros ka Ja Hka).
        destruct (scanexp_l2_loop n (xa, ca, fa)) as [[[xb cb] fb]|] eqn:HL2; [|discriminate HS].
        (nelim (scanexp_l2_J _ _ _ _ _ _ _ _ HL2 Ja Hka) 3%nat; intros kb Jb Hkb).
        destruct (scanexp_l3_loop n (cb, fb)) as [[cc fcc]|] eqn:HL3; [|discriminate HS].
        (nelim (scanexp_l3_J _ _ _ _ _ _ HL3 Jb Hkb) 3%nat; intros kc Jc Hkc).
        injection HS as <- <-. exact (FIN _ _ _ Jc Hkc).
  Qed.

  Lemma decfloat_J : forall n f c sg pk f' y k, decfloat n f c 53 (-1074) sg pk = Some (f', y) -> JF k c f -> (1 <= k)%Z -> JR f'.
  Proof.
    clear -Hp Hnul BYT. intros n f c sg pk f' y k HD J Hk.
    rewrite (decfloat_split n 53 (-1074) sg pk) in HD.
    destruct (df_lz_loop n (0%Z, c, f)) as [[[g1 c1] f1]|] eqn:HLZ; [|discriminate HD].
    (nelim (df_lz_J _ _ _ _ _ _ _ _ HLZ J Hk) 3%nat; intros k1 J1 Hk1).
    unfold dfK_rz in HD.
    assert (G : forall g gr l c2 f2 k2, JF k2 c2 f2 -> (1 <= k2)%Z ->
      dfK_dig n 53 (-1074) sg pk (mkDL f2 c2 0 0 l 0 0 g gr (zupd (zrepeat 0 KMAX) 0 0)) = Some (f', y) -> JR f').
    { intros g gr l c2 f2 k2 J2 Hk2 HK. unfold dfK_dig in HK.
      destruct (df_dig_loop n _) as [s'|] eqn:HDG; [|discriminate HK].
      (nelim (df_dig_J _ _ _ _ HDG J2 Hk2) 3%nat; intros k3 J3 Hk3). cbn [dl_c dl_f] in J3.
      unfold dfK_exp in HK. destruct s' as [f3 c3 j3 kk3 lrp3 dc3 lnz3 gd3 gr3 x3]. cbn [dl_c dl_f] in J3.
      cbv beta iota zeta in HK.
      destruct (nz gd3 && (Z.lor c3 32 =? 101)) eqn:EE.
      - assert (Hc3 : c3 <> 0%Z) by (intros E0; rewrite E0 in EE; rewrite andb_false_r in EE; discriminate EE).
        destruct (scanexp n f3 pk) as [[f4 e10]|] eqn:HSE; [|discriminate HK].
        destruct (scanexp_J _ _ _ _ _ _ _ HSE J3 Hc3 Hk3) as [R4 R4u].
        destruct (e10 =? LLONG_MIN_).
        + destruct (nz pk).
          * destruct (negb (nz gd3)); [injection HK as <- <-; apply JR_lim0; exact R4u|].
            rewrite <- (dfK_rng_f' HK). exact R4u.
          * injection HK as <- <-. apply JR_lim0. exact R4.
        + destruct (negb (nz gd3)); [injection HK as <- <-; apply JR_lim0; exact R4|].
          rewrite <- (dfK_rng_f' HK). exact R4.
      - destruct (Z.leb_spec 0 c3).
        + destruct (JF_unget_any _ _ _ 0 J3 Hk3 ltac:(lia) ltac:(intros; lia)) as [J4 R4].
          destruct (negb (nz gd3)); [injection HK as <- <-; apply JR_lim0; exact R4|].
          rewrite <- (dfK_rng_f' HK). exact R4.
        + pose proof (JF_neg_JR _ _ _ J3 ltac:(lia)) as R3.
          destruct (negb (nz gd3)); [injection HK as <- <-; apply JR_lim0; exact R3|].
          rewrite <- (dfK_rng_f' HK). exact R3. }
    destruct (Z.eqb_spec c1 46) as [E46|N46].
    - destruct (sh_getc f1) as [c2 f2] eqn:EG2.
      pose proof (JF_getc _ _ _ J1 ltac:(lia)) as J2. rewrite EG2 in J2. cbn [fst snd] in J2.
      destruct (df_rz_loop n (g1, 0%Z, c2, f2)) as [[[[g3 l3] c3] f3]|] eqn:HRZ; [|discriminate HD].
      (nelim (df_rz_J _ _ _ _ _ _ _ _ _ _ HRZ J2 ltac:(lia)) 3%nat; intros k3 J3 Hk3).
      exact (G _ _ _ _ _ _ J3 Hk3 HD).
    - exact (G _ _ _ _ _ _ J1 Hk1 HD).
  Qed.

  (* [comment removed for export] *)
  Lemma floatscan_JR : forall n f pk f' y, floatscan (S n) f 1 pk = Some (f', y) -> JF 0 1 f -> JR f'.
  Proof.
    clear -Hp Hnul BYT Hnum. intros n f pk f' y HF J0.
    unfold floatscan in HF. cbn [Z.eqb Pos.eqb] in HF. change (-1021 - 53)%Z with (-1074)%Z in HF.
    rewrite fs_ws_loop_step in HF.
    pose proof (JF_okch _ _ _ J0 ltac:(lia)) as OK1. pose proof (JF_getc _ _ _ J0 ltac:(lia)) as J1.
    destruct (sh_getc f) as [c1 f1]. cbn [fst snd] in OK1, J1.
    (nelim (okch_cases c1 OK1) 5%nat; intros NS1 NI1 NN1 _ _). rewrite NS1 in HF.
    assert (G : forall k c g sg, JF k c g -> (1 <= k)%Z -> okch c ->
      match fs_inf_loop 9 (0%Z, c, g) with
      | Some (i, c0, f0) =>
          if (i =? 3) || (i =? 8) || (3 <? i) && nz pk
          then Some (if negb (i =? 8) then if nz pk then fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f0) else sh_unget f0 else f0, if 0 <? sg then C_INF else C_NINF)
          else
           match (if i =? 0 then fs_nan_loop 4 (0%Z, c0, f0) else Some (i, c0, f0)) with
           | Some (i0, c2, f2) =>
               if i0 =? 3
               then let '(c3, f3) := sh_getc f2 in
                    if negb (c3 =? 40) then Some (sh_unget f3, C_NAN)
                    else match fs_par_loop (S n) (1%Z, f3) with
                         | Some (i1, c4, f4) => if c4 =? 41 then Some (f4, C_NAN) else if negb (nz pk) then Some (sh_lim0 (sh_unget f4), f128_of_i32 0) else Some (fs_unget_loop (Z.to_nat i1) (sh_unget f4), C_NAN)
                         | None => None end
               else if nz i0 then Some (sh_lim0 (sh_unget f2), f128_of_i32 0)
               else if c2 =? 48 then let '(c3, f3) := sh_getc f2 in if Z.lor c3 32 =? 120 then None else decfloat (S n) (sh_unget f3) 48 53 (-1074) sg pk
               else decfloat (S n) f2 c2 53 (-1074) sg pk
           | None => None end
      | None => None end = Some (f', y) -> JR f').
    { intros k c g sg Jg Hk OK HK. (nelim (okch_cases c OK) 5%nat; intros NS NI NN _ _).
      rewrite fs_inf_nil in HK by exact NI. cbn [Z.eqb orb andb Z.ltb] in HK. rewrite fs_nan_nil in HK by exact NN. cbn [Z.eqb nz negb] in HK.
      destruct (Z.eqb_spec c 48) as [E48|N48].
      - pose proof (JF_getc _ _ _ Jg ltac:(lia)) as J3. destruct (sh_getc g) as [c3 f3]. cbn [fst snd] in J3.
        destruct (Z.lor c3 32 =? 120); [discriminate HK|].
        eapply (decfloat_J _ _ _ _ _ _ _ k HK); [| exact Hk]. replace k with (k + 1 - 1)%Z by lia. apply (JF_unget_any _ _ _ _ J3); intros; lia.
      - exact (decfloat_J _ _ _ _ _ _ _ k HK Jg Hk). }
    destruct ((c1 =? 43) || (c1 =? 45)) eqn:ESG.
    - assert (Hc1 : c1 <> 0%Z) by (intros E0; rewrite E0 in ESG; discriminate ESG).
      pose proof (JF_okch _ _ _ J1 Hc1) as OK2. pose proof (JF_getc _ _ _ J1 Hc1) as J2.
      destruct (sh_getc f1) as [c2 f2]. cbn [fst snd] in OK2, J2.
      exact (G _ _ _ _ J2 ltac:(lia) OK2 HF).
    - exact (G _ _ _ _ J1 ltac:(lia) OK1 HF).
  Qed.


Lemma strlen_loop_first0 : forall fuel s n q,
  (0 <= n <= q)%Z -> (forall i, (n <= i < q)%Z -> znth s i <> 0%Z) -> znth s q = 0%Z -> (Z.to_nat (q - n) < fuel)%nat ->
  strlen_loop fuel s n = Some q.
Proof.
  clear. induction fuel as [|fuel IH]; intros s n q Hn Hnz Hq Hf; [lia|].
  cbn [strlen_loop]. destruct (Z.eq_dec n q) as [->|NE].
  - rewrite Hq. reflexivity.
  - unfold nz. destruct (Z.eqb_spec (znth s n) 0) as [E|NE']; [exfalso; exact (Hnz n ltac:(lia) E)|]. cbn [negb].
    apply IH; [lia | intros i Hi; apply Hnz; lia | exact Hq | lia].
Qed.


  Definition ssf0 : shfile := mkSh txt 0 0 p true false.

  Lemma ss_JF0 : JF 0 1 ssf0.
  Proof. clear -Hp. unfold JF, ssf0. cbn. repeat split; try reflexivity; try lia; intros X; try discriminate X; lia. Qed.

  (* [comment removed for export] *)
  Lemma ss_peek :
    let c1 := fst (sh_getc ssf0) in let f1 := snd (sh_getc ssf0) in let f2 := sh_unget f1 in
    okch c1 /\ (sh_shlim_neg f1 = false -> 1 <= sh_rpos f1 <= 2^40)%Z /\
    sh_rpos f2 = 0%Z /\ sh_n f2 = p /\ sh_stdio f2 = true /\ sh_buf f2 = txt /\ sh_lim0 f2 = ssf0 /\
    (c1 <> (-1)%Z -> f2 = ssf0) /\ m_isspace c1 = false /\ ((c1 <? 0) = (c1 =? -1))%Z.
  Proof.
    pose proof (JF_okch _ _ _ ss_JF0 ltac:(lia)) as OK.
    (nelim (okch_cases _ OK) 5%nat; intros NS _ _ _ _).
    revert OK NS. unfold ssf0, sh_getc. cbn [sh_stdio sh_rpos sh_n sh_buf sh_cnt0 sh_shlim_neg negb].
    destruct (Z.eqb_spec 0 p) as [E|NE]; cbn [fst snd sh_unget sh_lim0 sh_shlim_neg sh_rpos sh_n sh_stdio sh_buf sh_cnt0 negb]; intros OK NS.
    - subst p. repeat split; try assumption; try reflexivity; try lia; try (intros X; discriminate X).
    - assert (R0 : (0 <= znth txt 0 < 256)%Z) by (apply (proj1 (Forall_forall _ _) BYT); apply znth_In'; lia).
      replace (0 + 1 - 1)%Z with 0%Z by lia.
      repeat split; try assumption; try reflexivity; try lia.
      all: destruct (Z.ltb_spec0 (znth txt 0) 0); destruct (Z.eqb_spec (znth txt 0) (-1)); try reflexivity; lia.
  Qed.

  Lemma ss_model : forall r res, scan_sscanf_lg txt = Some (r, res) ->
    let c1 := fst (sh_getc ssf0) in
    (c1 = (-1)%Z /\ r = (-1)%Z /\ res = None) \/
    (c1 <> (-1)%Z /\ exists fR yR, floatscan (fuel_of txt) ssf0 1 0 = Some (fR, yR) /\ JR fR /\
       ((sh_cnt fR = 0%Z /\ r = 0%Z /\ res = None) \/ (sh_cnt fR <> 0%Z /\ r = 1%Z /\ res = Some (f128_to_d yR)))).
  Proof.
    intros r res HS. pose proof ss_peek as PK. cbv zeta in PK. (nelim PK 10%nat; intros OK _ R2 N2 S2 B2 L2 U2 NS LT).
    cbv zeta. unfold scan_sscanf_lg in HS.
    rewrite (strlen_loop_first0 (fuel_of txt) txt 0 p) in HS;
      [| lia | intros i Hi E0; pose proof (Hnum i Hi) as X; rewrite E0 in X; discriminate X | exact Hnul | unfold fuel_of; unfold zlength in Hp; lia].
    change (sh_lim0 (mkSh txt 0 0 p true false)) with ssf0 in HS.
    unfold fuel_of in HS. rewrite fs_ws_loop_step in HS. fold (fuel_of txt) in HS.
    destruct (sh_getc ssf0) as [c1 f1] eqn:EG1. cbn [fst snd] in *. rewrite NS in HS. cbv beta iota in HS.
    rewrite L2, EG1, LT in HS.
    destruct (Z.eqb_spec c1 (-1)) as [E|NE].
    - left. injection HS as <- <-. repeat split; assumption || reflexivity.
    - right. split; [exact NE|]. rewrite (U2 NE) in HS.
      destruct (floatscan (fuel_of txt) ssf0 1 0) as [[fR yR]|] eqn:HF; [|discriminate HS].
      exists fR, yR. split; [reflexivity|]. split.
      + unfold fuel_of in HF. exact (floatscan_JR _ _ _ _ _ HF ss_JF0).
      + destruct (Z.eqb_spec (sh_cnt fR) 0) as [E0|N0]; injection HS as <- <-; [left | right]; repeat split; assumption || reflexivity.
  Qed.


End Model.
