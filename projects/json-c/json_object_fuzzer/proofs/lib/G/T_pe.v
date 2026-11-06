(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B QZAi QfYR QfcC Ql2m Qx2n QhAd QXfH QzgB Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module F_rscan_modelH.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import Qc3B.
Import QZAi.Mq1 QZAi QfYR QfcC Ql2m Qx2n.
Import QhAd.
Import QXfH.
Import QzgB.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs.

Section M.
Variables (txt : list Z) (p : Z).
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.

Local Notation JF := (JF txt p).
Local Notation JR := (JR p).

#[using="BYT Hp Hnul"] Lemma JF_getc' : forall k c f c2 f2, JF k c f -> c <> 0 -> sh_getc f = (c2, f2) -> JF (k + 1) c2 f2.
Proof. clear - BYT Hp Hnul txt p. intros k c f c2 f2 J Hc EG. pose proof (JF_getc txt p BYT Hp Hnul k c f J Hc) as J2. rewrite EG in J2. exact J2. Qed.

#[using="Type"] Lemma JF_JR : forall k c f, JF k c f -> c <> 0 -> JR f.
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac].
clear. intros k c f (A & B & D0 & Rc & KM & NS & SS) Hc. unfold QzgB.JR. destruct (sh_stdio f).
- destruct (SS eq_refl) as (N1 & N2 & N3). lia.
- destruct (NS eq_refl) as (N1 & N2 & N3 & N4). specialize (N3 Hc). lia.
Qed.
#[using="Hp"] Lemma JF_unget_JR : forall k c f, JF k c f -> 1 <= k -> JF (k - 1) 0 (sh_unget f) /\ JR (sh_unget f).
Proof. clear - Hp txt p BYT Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]. intros k c f J Hk. apply (JF_unget_any txt p k c f 0 J Hk); intros; lia. Qed.
#[using="Hp"] Lemma JF_ungets_JR : forall n k c f, JF k c f -> Z.of_nat n <= k -> (1 <= n)%nat -> JR (fs_unget_loop n f).
Proof. clear - Hp txt p BYT Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac].
induction n as [|n IH]; intros k c f J Hk Hn; [lia|].
cbn [fs_unget_loop]. destruct (JF_unget_JR k c f J ltac:(lia)) as [J1 R1].
destruct n as [|n']; [exact R1|]. eapply IH; [exact J1 | lia | lia].
Qed.
#[using="Type"] Lemma JR_lim0' : forall f, JR f -> JR (sh_lim0 f).
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]. clear. intros f R. unfold QzgB.JR, sh_lim0 in *. cbn. lia. Qed.

#[using="BYT Hp Hnul"] Lemma fs_ws_J : forall n f k c c' f', fs_ws_loop n f = Some (c', f') -> JF k c f -> c <> 0 -> 0 <= k ->
exists k', JF k' c' f' /\ 1 <= k'.
Proof. clear - BYT Hp Hnul txt p.
induction n as [|n IH]; intros f k c c' f' HL J Hc Hk; [discriminate HL|].
rewrite fs_ws_loop_S in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
destruct (m_isspace c2) eqn:SP.
- eapply (IH f2 (k + 1) c2); [exact HL | exact J2 | | lia].
intros E0. rewrite E0 in SP. discriminate SP.
- injection HL as <- <-. exists (k + 1). split; [exact J2 | lia].
Qed.

#[using="Type"] Lemma lor32_nz : forall c v, (Z.lor c 32 =? v) = true -> 97 <= v -> c <> 0.
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]. clear. intros c v E Hv ->. rewrite Z.lor_0_l in E. apply Z.eqb_eq in E. lia. Qed.

#[using="BYT Hp Hnul"] Lemma fs_inf_J : forall n i c f i' c' f' k, fs_inf_loop n (i, c, f) = Some (i', c', f') -> JF k c f -> 0 <= i ->
exists k', JF k' c' f' /\ k + (Z.min i' 7 - Z.min i 7) <= k' /\ i <= i' <= Z.max i 8 /\ (i < i' -> i' = 8 -> c' <> 0).
Proof. clear - BYT Hp Hnul txt p.
induction n as [|n IH]; intros i c f i' c' f' k HL J Hi; [discriminate HL|].
rewrite fs_inf_loop_S in HL. unfold fs_inf_cond in HL.
destruct (Z.ltb_spec i 8) as [L8|G8]; cbn [andb] in HL.
- destruct (Z.lor c 32 =? znth str_infinity i) eqn:EQ.
+ assert (Hc : c <> 0) by (apply (lor32_nz _ _ EQ); apply str_infinity_ge; lia).
unfold fs_inf_body in HL. destruct (Z.ltb_spec i 7) as [L7|G7].
* destruct (sh_getc f) as [c2 f2] eqn:EG. pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
destruct (IH _ _ _ _ _ _ _ HL J2 ltac:(lia)) as [k' (J' & Hk' & Hi' & Hc')].
exists k'. split; [exact J'|]. split; [lia|]. split; [lia|]. intros _ E8. apply Hc'; lia.
* destruct (IH _ _ _ _ _ _ _ HL J ltac:(lia)) as [k' (J' & Hk' & Hi' & Hc')].
exists k'. split; [exact J'|]. split; [lia|]. split; [lia|]. intros _ E8.
destruct (Z.lt_ge_cases (i + 1) i') as [LT|GE]; [apply Hc'; lia|].

destruct n as [|n2]; [discriminate HL|]. rewrite fs_inf_loop_S in HL. unfold fs_inf_cond in HL.
replace (i + 1 <? 8) with false in HL by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in HL.
injection HL as _ <- _. exact Hc.
+ injection HL as <- <- <-. exists k. split; [exact J|]. split; [lia|]. split; [lia|]. intros; lia.
- injection HL as <- <- <-. exists k. split; [exact J|]. split; [lia|]. split; [lia|]. intros; lia.
Qed.

#[using="BYT Hp Hnul"] Lemma fs_nan_J : forall n i c f i' c' f' k, fs_nan_loop n (i, c, f) = Some (i', c', f') -> JF k c f -> 0 <= i ->
exists k', JF k' c' f' /\ k + (Z.min i' 2 - Z.min i 2) <= k' /\ i <= i' <= Z.max i 3 /\ (i < i' -> i' = 3 -> c' <> 0).
Proof. clear - BYT Hp Hnul txt p.
induction n as [|n IH]; intros i c f i' c' f' k HL J Hi; [discriminate HL|].
rewrite fs_nan_loop_S in HL. unfold fs_nan_cond in HL.
destruct (Z.ltb_spec i 3) as [L8|G8]; cbn [andb] in HL.
- destruct (Z.lor c 32 =? znth str_nan i) eqn:EQ.
+ assert (Hc : c <> 0) by (apply (lor32_nz _ _ EQ); apply str_nan_ge; lia).
unfold fs_nan_body in HL. destruct (Z.ltb_spec i 2) as [L7|G7].
* destruct (sh_getc f) as [c2 f2] eqn:EG. pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
destruct (IH _ _ _ _ _ _ _ HL J2 ltac:(lia)) as [k' (J' & Hk' & Hi' & Hc')].
exists k'. split; [exact J'|]. split; [lia|]. split; [lia|]. intros _ E8. apply Hc'; lia.
* destruct (IH _ _ _ _ _ _ _ HL J ltac:(lia)) as [k' (J' & Hk' & Hi' & Hc')].
exists k'. split; [exact J'|]. split; [lia|]. split; [lia|]. intros _ E8.
destruct (Z.lt_ge_cases (i + 1) i') as [LT|GE]; [apply Hc'; lia|].
destruct n as [|n2]; [discriminate HL|]. rewrite fs_nan_loop_S in HL. unfold fs_nan_cond in HL.
replace (i + 1 <? 3) with false in HL by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in HL.
injection HL as _ <- _. exact Hc.
+ injection HL as <- <- <-. exists k. split; [exact J|]. split; [lia|]. split; [lia|]. intros; lia.
- injection HL as <- <- <-. exists k. split; [exact J|]. split; [lia|]. split; [lia|]. intros; lia.
Qed.

#[using="Type"] Lemma alnum_nz : forall c, (u32 (c - 48) <? 10) || (u32 (c - 65) <? 26) || (u32 (c - 97) <? 26) || (c =? 95) = true -> c <> 0.
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]. clear. intros c H ->. cbv in H. discriminate H. Qed.

#[using="BYT Hp Hnul"] Lemma fs_par_J : forall n i f i' c' f' k c, fs_par_loop n (i, f) = Some (i', c', f') -> JF k c f -> c <> 0 -> 0 <= i ->
exists k', JF k' c' f' /\ k + (i' - i) + 1 <= k' /\ i <= i'.
Proof. clear - BYT Hp Hnul txt p.
induction n as [|n IH]; intros i f i' c' f' k c HL J Hc Hi; [discriminate HL|].
rewrite fs_par_loop_S in HL. unfold fs_par_body in HL.
destruct (sh_getc f) as [c2 f2] eqn:EG. pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
destruct ((u32 (c2 - 48) <? 10) || (u32 (c2 - 65) <? 26) || (u32 (c2 - 97) <? 26) || (c2 =? 95)) eqn:AN.
- destruct (IH _ _ _ _ _ _ _ HL J2 (alnum_nz _ AN) ltac:(lia)) as [k' (J' & Hk' & Hi')].
exists k'. split; [exact J'|]. lia.
- injection HL as <- <- <-. exists (k + 1). split; [exact J2|]. lia.
Qed.

#[using="BYT Hp Hnul"] Lemma df_lz_Jk : forall n g c f g' c' f' k, df_lz_loop n (g, c, f) = Some (g', c', f') -> JF k c f -> c <> 0 ->
exists k', JF k' c' f' /\ k <= k' /\ (g' = g \/ c' <> 0 \/ True) /\ (c' = 48 -> False \/ True).
Proof. clear - BYT Hp Hnul txt p.
induction n as [|n IH]; intros g c f g' c' f' k HL J Hc; [discriminate HL|].
rewrite df_lz_loop_S in HL. destruct (Z.eqb_spec c 48) as [Ec|Nc].
- unfold df_lz_body in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
destruct (Z.eq_dec c2 0) as [Z2|NZ2].
+
destruct n as [|n2]; [discriminate HL|]. rewrite df_lz_loop_S in HL. rewrite Z2 in HL. cbn [Z.eqb] in HL.
injection HL as <- <- <-. exists (k + 1). split; [rewrite <- Z2; exact J2|]. split; [lia|]. tauto.
+ destruct (IH _ _ _ _ _ _ (k + 1) HL J2 NZ2) as [k' (J' & Hk' & _)]. exists k'. split; [exact J'|]. split; [lia|]. tauto.
- injection HL as <- <- <-. exists k. split; [exact J|]. split; [lia|]. tauto.
Qed.
#[using="BYT Hp Hnul"] Lemma df_rz_Jk : forall n g l c f g' l' c' f' k, df_rz_loop n (g, l, c, f) = Some (g', l', c', f') -> JF k c f -> c <> 0 ->
exists k', JF k' c' f' /\ k <= k'.
Proof. clear - BYT Hp Hnul txt p.
induction n as [|n IH]; intros g l c f g' l' c' f' k HL J Hc; [discriminate HL|].
rewrite df_rz_loop_S in HL. destruct (Z.eqb_spec c 48) as [Ec|Nc].
- unfold df_rz_body in HL. destruct (sh_getc f) as [c2 f2] eqn:EG.
pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
destruct (Z.eq_dec c2 0) as [Z2|NZ2].
+ destruct n as [|n2]; [discriminate HL|]. rewrite df_rz_loop_S in HL. rewrite Z2 in HL. cbn [Z.eqb] in HL.
injection HL as <- <- <- <-. exists (k + 1). split; [rewrite <- Z2; exact J2|]. lia.
+ destruct (IH _ _ _ _ _ _ _ _ (k + 1) HL J2 NZ2) as [k' (J' & Hk')]. exists k'. split; [exact J'|]. lia.
- injection HL as <- <- <- <-. exists k. split; [exact J|]. lia.
Qed.

#[using="Type"] Lemma ishexc_nz : forall c, ishexc c = true -> c <> 0.
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]. clear. intros c H ->. cbv in H. discriminate H. Qed.
#[using="Type"] Lemma hx_dig_cond_nz : forall s, hx_dig_cond s = true -> hx_c s <> 0.
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac].
clear. intros s H. unfold hx_dig_cond in H. apply Bool.orb_true_iff in H. destruct H as [H|H].
- apply ishexc_nz. exact H.
- apply Z.eqb_eq in H. lia.
Qed.

#[using="BYT Hp Hnul"] Lemma hx_dig_Jk : forall n s s' k, hx_dig_loop n s = Some s' -> JF k (hx_c s) (hx_f s) -> (hx_c s = 0 -> hx_dig_cond s = false) ->
exists k', JF k' (hx_c s') (hx_f s') /\ k <= k'.
Proof. clear - BYT Hp Hnul txt p.
induction n as [|n IH]; intros s s' k HL J H0; [discriminate HL|].
rewrite hx_dig_loop_S in HL. destruct (hx_dig_cond s) eqn:CND.
- pose proof (hx_dig_cond_nz s CND) as Hc.
destruct s as [c f x y sc gt gr gd rp dc]. cbn [hx_c hx_f] in *.
unfold hx_dig_body in HL.
destruct (sh_getc f) as [c2 f2] eqn:EG.
pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
assert (STEP : forall x' y' sc' gt' gr' gd' rp' dc',
hx_dig_loop n (mkHX c2 f2 x' y' sc' gt' gr' gd' rp' dc') = Some s' -> exists k', JF k' (hx_c s') (hx_f s') /\ k <= k').
{ intros * HL2. destruct (Z.eq_dec c2 0) as [Z2|NZ2].
- destruct n as [|n2]; [discriminate HL2|]. rewrite hx_dig_loop_S in HL2.
replace (hx_dig_cond _) with false in HL2 by (unfold hx_dig_cond; cbn [hx_c]; rewrite Z2; reflexivity).
injection HL2 as <-. cbn [hx_c hx_f]. exists (k + 1). split; [exact J2|]. lia.
- destruct (IH _ _ (k + 1) HL2 J2 ltac:(cbn [hx_c]; intros E; exfalso; exact (NZ2 E))) as [k' [J' Hk']].
exists k'. split; [exact J'|]. lia. }
destruct (Z.eqb_spec c 46) as [E46|N46].
+ destruct (nz gr).
* injection HL as <-. cbn [hx_c hx_f]. exists k. split; [exact J|]. lia.
* cbv iota beta in HL. eapply STEP. exact HL.
+ match type of HL with context [match ?U with pair _ _ => _ end] =>
destruct U as [[[x2 y2] sc2] gt2] end.
cbv iota beta in HL. eapply STEP. exact HL.
- injection HL as <-. exists k. split; [exact J|]. lia.
Qed.

#[using="Type"] Lemma df_lz_0 : forall n g f r, df_lz_loop n (g, 0, f) = Some r -> r = (g, 0, f).
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]. clear. intros [|n] g f r H; [discriminate H|]. rewrite df_lz_loop_S in H. cbn [Z.eqb] in H. injection H as <-. reflexivity. Qed.
#[using="Type"] Lemma df_rz_0 : forall n g l f r, df_rz_loop n (g, l, 0, f) = Some r -> r = (g, l, 0, f).
Proof. clear - txt p BYT Hp Hnul. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]. clear. intros [|n] g l f r H; [discriminate H|]. rewrite df_rz_loop_S in H. cbn [Z.eqb] in H. injection H as <-. reflexivity. Qed.

Section HXJ.
Variables (fuelc : nat) (bits emin sign pok : Z).
Hypothesis Hpk : nz pok = true.
Local Notation HX_e2' := (HX_e2 bits emin sign).
Local Notation HX_tail' := (HX_tail fuelc bits emin sign pok).
Local Notation HX_dig' := (HX_dig fuelc bits emin sign pok).
Local Notation HX_rz' := (HX_rz fuelc bits emin sign pok).
Local Notation HX_alz' := (HX_alz fuelc bits emin sign pok).
Local Notation HX_lz' := (HX_lz fuelc bits emin sign pok).

#[using="Type"] Lemma HX_e2_f : forall f x y e2 f' y', HX_e2' f x y e2 = Some (f', y') -> f' = f.
Proof. clear - txt p BYT Hp Hnul fuelc bits emin sign pok Hpk. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hpk | gw_hide Hpk | idtac].
clear. intros until y'. unfold HX_e2, HX_fin.
destruct (x =? 0); [intros H; injection H as <- _; reflexivity|].
destruct (- emin <? e2); [intros H; injection H as <- _; reflexivity|].
destruct (e2 <? emin - _); [intros H; injection H as <- _; reflexivity|].
destruct (hx_norm_loop 33 _) as [[[x7 y7] e7]|]; [|discriminate].
match goal with |- context [match ?X with pair _ _ => _ end] => destruct X as [[bias x2] y2] end.
intros H; injection H as <- _; reflexivity.
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_tail_J : forall c f x y gr gd rp dc k f' y', HX_tail' c f x y gr gd rp dc = Some (f', y') ->
JF k c f -> 3 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc bits emin sign pok.
intros until y'. intros HT J Hk. unfold HX_tail in HT. rewrite Hpk in HT.
destruct (negb (nz gd)).
- injection HT as <- _.
destruct (JF_unget_JR _ _ _ J ltac:(lia)) as [J6 R6].
destruct (JF_unget_JR _ _ _ J6 ltac:(lia)) as [J7 R7].
destruct (nz gr); [|exact R7]. exact (proj2 (JF_unget_JR _ _ _ J7 ltac:(lia))).
- destruct (Z.lor c 32 =? 112) eqn:EP.
+ assert (Hc : c <> 0) by (apply (lor32_nz _ _ EP); lia).
destruct (scanexp fuelc f pok) as [[f6 e6]|] eqn:HSE; [|discriminate HT].
destruct (scanexp_J txt p BYT Hp Hnul _ _ _ _ _ _ _ HSE J Hc ltac:(lia)) as [R6 R6u].
destruct (e6 =? LLONG_MIN_); cbv iota beta in HT.
* pose proof (HX_e2_f _ _ _ _ _ _ HT) as Ef. rewrite Ef. exact R6u.
* pose proof (HX_e2_f _ _ _ _ _ _ HT) as Ef. rewrite Ef. exact R6.
+ pose proof (HX_e2_f _ _ _ _ _ _ HT) as Ef. rewrite Ef. exact (proj2 (JF_unget_JR _ _ _ J ltac:(lia))).
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_dig_J : forall s k f' y', HX_dig' s = Some (f', y') -> JF k (hx_c s) (hx_f s) -> 3 <= k ->
(hx_c s = 0 -> hx_dig_cond s = false) -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc bits emin sign pok.
intros s k f' y' HD J Hk H0. unfold HX_dig in HD.
destruct (hx_dig_loop fuelc s) as [[c5 f5 x5 y5 sc5 gt5 gr5 gd5 rp5 dc5]|] eqn:HL; [|discriminate HD].
destruct (hx_dig_Jk _ _ _ k HL J H0) as [k5 [J5 Hk5]]. cbn [hx_c hx_f] in J5.
eapply HX_tail_J; [exact HD | exact J5 | lia].
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_rz_J : forall gd rp c f k f' y', HX_rz' gd rp c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc bits emin sign pok.
intros until y'. intros HR J Hk. unfold HX_rz in HR.
destruct (df_rz_loop fuelc (gd, rp, c, f)) as [[[[g4 l4] c4] f4]|] eqn:HL; [|discriminate HR].
destruct (Z.eq_dec c 0) as [Zc|NZc].
- subst c. pose proof (df_rz_0 _ _ _ _ _ HL) as E4. injection E4 as -> -> -> ->.
eapply HX_dig_J; [exact HR | cbn [hx_c hx_f]; exact J | lia | intros _; reflexivity].
- destruct (df_rz_Jk _ _ _ _ _ _ _ _ _ _ HL J NZc) as [k4 [J4 Hk4]].
eapply HX_dig_J; [exact HR | cbn [hx_c hx_f]; exact J4 | lia |].
cbn [hx_c hx_gr]. intros Z4. unfold hx_dig_cond. cbn [hx_c]. rewrite Z4. reflexivity.
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_alz_J : forall gd c f k f' y', HX_alz' gd c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc bits emin sign pok.
intros until y'. intros HA J Hk. unfold HX_alz in HA.
destruct (Z.eqb_spec c 46) as [E46|N46].
- destruct (sh_getc f) as [c2 f2] eqn:EG. pose proof (JF_getc' k c f c2 f2 J ltac:(lia) EG) as J2.
eapply HX_rz_J; [exact HA | exact J2 | lia].
- eapply HX_dig_J; [exact HA | cbn [hx_c hx_f]; exact J | lia |].
cbn [hx_c hx_gr]. intros Zc. unfold hx_dig_cond. cbn [hx_c]. rewrite Zc. reflexivity.
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma HX_lz_J : forall gd c f k f' y', HX_lz' gd c f = Some (f', y') -> JF k c f -> 3 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc bits emin sign pok.
intros until y'. intros HZ J Hk. unfold HX_lz in HZ.
destruct (df_lz_loop fuelc (gd, c, f)) as [[[g2 c2] f2]|] eqn:HL; [|discriminate HZ].
destruct (Z.eq_dec c 0) as [Zc|NZc].
- subst c. pose proof (df_lz_0 _ _ _ _ HL) as E4. injection E4 as -> -> ->. eapply HX_alz_J; [exact HZ | exact J | lia].
- destruct (df_lz_Jk _ _ _ _ _ _ _ _ HL J NZc) as [k2 (J2 & Hk2 & _)].
eapply HX_alz_J; [exact HZ | exact J2 | lia].
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma hexfloat_J : forall f c k f' y', hexfloat_m fuelc f bits emin sign pok = Some (f', y') ->
JF k c f -> c <> 0 -> 2 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc bits emin sign pok.
intros f c k f' y' HM J Hc Hk. rewrite hexfloat_m_eq in HM.
destruct (sh_getc f) as [c1 f1] eqn:EG. pose proof (JF_getc' k c f c1 f1 J Hc EG) as J1.
eapply HX_lz_J; [exact HM | exact J1 | lia].
Qed.
End HXJ.

Section FSJ.
Variables (fuelc : nat) (pok : Z).
Hypothesis Hpk : nz pok = true.
Local Notation FS_zero' := (FS_zero fuelc 53 (-1074) pok).
Local Notation FS_tail_h' := (FS_tail_h fuelc 53 (-1074) pok).
Local Notation FS_nan' := (FS_nan fuelc 53 (-1074) pok).
Local Notation FS_inf' := (FS_inf fuelc 53 (-1074) pok).
Local Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).
Local Notation FS_sign' := (FS_sign fuelc 53 (-1074) pok).

#[using="BYT Hp Hnul Hpk"] Lemma FS_zero_J : forall sg c2 f2 k f' y', FS_zero' sg c2 f2 = Some (f', y') -> JF k c2 f2 -> 2 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc pok.
intros until y'. intros HZ J Hk. unfold FS_zero in HZ.
destruct (Z.lor c2 32 =? 120) eqn:EX.
- eapply hexfloat_J; [exact Hpk | exact HZ | exact J | apply (lor32_nz _ _ EX); lia | exact Hk].
- destruct (JF_unget_JR _ _ _ J ltac:(lia)) as [J3 _].
pose proof (JF_unget_any txt p k c2 f2 48 J ltac:(lia) ltac:(lia) ltac:(intros; lia)) as [J4 _].
eapply (decfloat_J txt p BYT Hp Hnul); [exact HZ | exact J4 | lia].
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_tail_h_J : forall sg c f k f' y', FS_tail_h' sg c f = Some (f', y') -> JF k c f -> 1 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc pok.
intros until y'. intros HT J Hk. unfold FS_tail_h in HT.
destruct (Z.eqb_spec c 48) as [E48|N48].
- destruct (sh_getc f) as [c2 f2] eqn:EG. pose proof (JF_getc' k c f c2 f2 J ltac:(lia) EG) as J2.
eapply FS_zero_J; [exact HT | exact J2 | lia].
- eapply (decfloat_J txt p BYT Hp Hnul); [exact HT | exact J | exact Hk].
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_nan_J : forall sg i c f k f' y', FS_nan' sg i c f = Some (f', y') -> JF k c f -> 1 <= k -> 0 <= i ->
(i = 3 -> c <> 0) -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc pok.
intros until y'. intros HN J Hk Hi H3. unfold FS_nan in HN. rewrite Hpk in HN. cbn [negb] in HN.
destruct (Z.eqb_spec i 3) as [E3|N3].
- specialize (H3 E3). destruct (sh_getc f) as [c2 f2] eqn:EG. pose proof (JF_getc' k c f c2 f2 J H3 EG) as J2.
destruct (Z.eqb_spec c2 40) as [E40|N40]; cbn [negb] in HN.
+ destruct (fs_par_loop fuelc (1, f2)) as [[[i6 c6] f6]|] eqn:HPL; [|discriminate HN].
destruct (fs_par_J _ _ _ _ _ _ _ _ HPL J2 ltac:(lia) ltac:(lia)) as [k6 (J6 & Hk6 & Hi6)].
destruct (Z.eqb_spec c6 41) as [E41|N41].
* injection HN as <- _. eapply JF_JR; [exact J6 | lia].
* injection HN as <- _. destruct (JF_unget_JR _ _ _ J6 ltac:(lia)) as [J7 R7].
destruct (Z.to_nat i6) as [|n7] eqn:EN; [exact R7|].
eapply JF_ungets_JR; [exact J7 | lia | lia].
+ injection HN as <- _. exact (proj2 (JF_unget_JR _ _ _ J2 ltac:(lia))).
- destruct (nz i).
+ injection HN as <- _. apply JR_lim0'. exact (proj2 (JF_unget_JR _ _ _ J Hk)).
+ eapply FS_tail_h_J; [exact HN | exact J | exact Hk].
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_inf_J : forall sg i c f k f' y', FS_inf' sg i c f = Some (f', y') -> JF k c f -> 0 <= i <= 8 ->
Z.min i 7 + 1 <= k -> (i = 8 -> c <> 0) -> (i = 0 -> True) -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc pok.
intros until y'. intros HI J Hi Hk H8 _. unfold FS_inf in HI. rewrite Hpk, Bool.andb_true_r in HI. cbv iota beta in HI.
match type of HI with (if ?b then _ else _) = _ => destruct b eqn:REC end.
- injection HI as <- _. destruct (Z.eqb_spec i 8) as [E8|N8]; cbn [negb].
+ eapply JF_JR; [exact J | exact (H8 E8)].
+ assert (Hi3 : 3 <= i <= 7).
{ rewrite ?Bool.orb_true_iff in REC.
destruct REC as [[REC|REC]|REC]; first [apply Z.eqb_eq in REC; lia | apply Z.ltb_lt in REC; lia | discriminate REC]. }
destruct (JF_unget_JR _ _ _ J ltac:(lia)) as [J2 R2].
destruct (Z.to_nat (i - 3)) as [|n3] eqn:EN; [exact R2|].
eapply JF_ungets_JR; [exact J2 | lia | lia].
- destruct (Z.eqb_spec i 0) as [E0|N0].
+ destruct (fs_nan_loop 4 (0, c, f)) as [[[i4 c4] f4]|] eqn:HNL; [|discriminate HI].
destruct (fs_nan_J _ _ _ _ _ _ _ _ HNL J ltac:(lia)) as [k4 (J4 & Hk4 & Hi4 & Hc4)].
eapply FS_nan_J; [exact HI | exact J4 | lia | lia | intros E3; apply Hc4; lia].
+ eapply FS_nan_J; [exact HI | exact J | lia | lia |]. intros ->. exfalso.
cbn in REC. discriminate REC.
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma FS_sign_J : forall c f k f' y', FS_sign' c f = Some (f', y') -> JF k c f -> 1 <= k -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc pok.
intros until y'. intros HS J Hk. unfold FS_sign in HS.
assert (G : forall sg c2 f2 k2, JF k2 c2 f2 -> 1 <= k2 -> FS_infk' sg 0 c2 f2 = Some (f', y') -> JR f').
{ intros sg c2 f2 k2 J2 Hk2 HK. unfold FS_infk in HK. change (Z.to_nat (9 - 0)) with 9%nat in HK.
destruct (fs_inf_loop 9 (0, c2, f2)) as [[[i3 c3] f3]|] eqn:HIL; [|discriminate HK].
destruct (fs_inf_J _ _ _ _ _ _ _ _ HIL J2 ltac:(lia)) as [k3 (J3 & Hk3 & Hi3 & Hc3)].
eapply FS_inf_J; [exact HK | exact J3 | lia | lia | intros E8; apply Hc3; lia | trivial]. }
destruct ((c =? 43) || (c =? 45)) eqn:SG.
- assert (Hc : c <> 0) by (intros ->; discriminate SG).
destruct (sh_getc f) as [c2 f2] eqn:EG. pose proof (JF_getc' k c f c2 f2 J Hc EG) as J2.
eapply G; [exact J2 | lia | exact HS].
- eapply G; [exact J | exact Hk | exact HS].
Qed.

#[using="BYT Hp Hnul Hpk"] Lemma floatscan_h_JR : forall f f' y, floatscan_h fuelc f 1 pok = Some (f', y) -> JF 0 1 f -> JR f'.
Proof. clear - BYT Hp Hnul Hpk txt p fuelc pok.
intros f f' y HF J0. rewrite floatscan_h_1 in HF.
destruct (fs_ws_loop fuelc f) as [[c1 f1]|] eqn:HW; [|discriminate HF].
destruct (fs_ws_J _ _ _ _ _ _ HW J0 ltac:(lia) ltac:(lia)) as [k1 [J1 Hk1]].
change (-1021 - 53) with (-1074) in HF.
eapply FS_sign_J; [exact HF | exact J1 | exact Hk1].
Qed.
End FSJ.
End M.

End G.
End F_rscan_modelH.
From Stdlib Require String Ascii.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 QqdR QYTG G.T_printf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Printf_model.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import QlEo_c1.Mq0.
Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope mspec_scope.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

Notation parg := G.T_printf.parg.
Notation PA_s := G.T_printf.PA_s.
Notation PA_i := G.T_printf.PA_i.
Notation PA_u := G.T_printf.PA_u.
Notation PA_g := G.T_printf.PA_g.
Notation PA_li := G.T_printf.PA_li.
Notation PA_lu := G.T_printf.PA_lu.

Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).

Definition T_PTR : Z := 9.  Definition T_INT : Z := 10.  Definition T_UINT : Z := 11.  Definition T_DBL : Z := 25.
Definition T_LONG : Z := 13. Definition T_ULONG : Z := 14.

Definition FLAGMASK : Z := 75913.

Fixpoint digits_aux (fuel : nat) (base_ : Z) (dig : Z -> Z) (x : Z) (acc : list Z) : list Z :=
match fuel with
| O => acc
| S fuel' => if x =? 0 then acc else digits_aux fuel' base_ dig (x / base_) (dig (x mod base_) :: acc)
end.

Definition dec_digits (x : Z) : list Z := digits_aux 20 10 (fun v => 48 + v) x [].

Definition XDIGITS : list Z := [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 65; 66; 67; 68; 69; 70].
Definition hex_digits (lower : Z) (x : Z) : list Z := digits_aux 16 16 (fun v => Z.lor (znth XDIGITS v) lower) x [].

Fixpoint lit_run (s : list Z) : list Z :=
match s with
| [] => []
| c :: s' => if (c =? 0) || (c =? 37) then [] else c :: lit_run s'
end.

Definition flag_bit (c : Z) : option Z :=
if (32 <=? c) && (c <? 64) && negb (Z.land FLAGMASK (Z.shiftl 1 (c - 32)) =? 0)
then Some (Z.shiftl 1 (c - 32)) else None.
Fixpoint parse_flags (s : list Z) (fl : Z) {struct s} : Z * list Z :=
match s with
| [] => (fl, s)
| c :: s' => match flag_bit c with
| Some b => parse_flags s' (Z.lor fl b)
| None => (fl, s)
end
end.

Fixpoint getint (s : list Z) (i : Z) {struct s} : option (Z * list Z) :=
match s with
| [] => Some (i, s)
| c :: s' => if is_digit c then
if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None
else getint s' (10 * i + (c - 48))
else Some (i, s)
end.

Definition conv_type (t : Z) : option Z :=
if t =? 115 then Some T_PTR
else if (t =? 100) || (t =? 105) || (t =? 99) then Some T_INT
else if (t =? 117) || (t =? 120) || (t =? 88) then Some T_UINT
else if (t =? 101) || (t =? 102) || (t =? 103) || (t =? 69) || (t =? 70) || (t =? 71)
then Some T_DBL
else None.

Definition conv_type_l (t : Z) : option Z :=
if (t =? 100) || (t =? 105) then Some T_LONG else if t =? 117 then Some T_ULONG else None.

Definition tyspec (s : list Z) : option (Z * Z * list Z) :=
match s with
| [] => None
| t :: s4 => if t =? 108 then match s4 with
| [] => None
| t2 :: s5 => let? ty := conv_type_l t2 in Some (ty, t2, s5)
end
else let? ty := conv_type t in Some (ty, t, s4)
end.

Notation dir := G.T_printf.dir.
Notation mkDir := G.T_printf.mkDir.
Notation d_fl := G.T_printf.d_fl.
Notation d_w := G.T_printf.d_w.
Notation d_p := G.T_printf.d_p.
Notation d_xp := G.T_printf.d_xp.
Notation d_t := G.T_printf.d_t.
Notation d_ty := G.T_printf.d_ty.

Definition d_ps (d : dir) : Z := if (d_ty d =? T_LONG) || (d_ty d =? T_ULONG) then 1 else 0.

Definition dir_ty_ok (d : dir) : Prop :=
(conv_type (d_t d) = Some (d_ty d) /\ d_ps d = 0) \/ (conv_type_l (d_t d) = Some (d_ty d) /\ d_ps d = 1).

Definition parse_dir (s : list Z) : option (dir * list Z) :=
let positional := match s with
| c1 :: c2 :: _ => is_digit c1 && (c2 =? 36)
| [c1] => is_digit c1
| [] => false
end in
if positional then None else
let '(fl, s1) := parse_flags s 0 in
match s1 with
| [] => None
| c1 :: _ =>
if c1 =? 42 then None else
let? (w, s2) := getint s1 0 in
match s2 with
| [] => None
| c2 :: s2' =>
let pxs : option (Z * bool * list Z) :=
if c2 =? 46 then
match s2' with
| [] => None
| c3 :: _ => if c3 =? 42 then None
else let? (p, s3) := getint s2' 0 in Some (p, true, s3)
end
else Some (-1, false, s2) in
match pxs with
| None => None
| Some (p, xp, s3) =>
match s3 with
| [] => None
| _ :: _ => let? tys := tyspec s3 in let '(ty, t, s4) := tys in Some (mkDir fl w p xp t ty, s4)
end
end
end
end.

Section PrintfModel.
Context {St : Type}.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

Definition mpad (c w l fl : Z) : M St unit :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then mret tt
else if 256 <=? w - l then munr
else OUT (zrepeat c (w - l)).

Definition conv_tail (cnt fl w p : Z) (prefix body : list Z) : M St Z :=
let pl := zlength prefix in
let n := zlength body in
let p := Z.max p n in
if INT_MAX - pl <? p then munr else
let w := Z.max w (pl + p) in
if INT_MAX - cnt <? w then munr else
mpad 32 w (pl + p) fl ;;;
OUT prefix ;;;
mpad 48 w (pl + p) (Z.lxor fl ZERO_PAD) ;;;
mpad 48 p n 0 ;;;
OUT body ;;;
mpad 32 w (pl + p) (Z.lxor fl LEFT_ADJ) ;;;
mret (cnt + w).

Definition conv_int (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : M St Z :=
if xp && (p <? 0) then munr else
let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
if (argi =? 0) && (p =? 0) then conv_tail cnt fl w p prefix []
else conv_tail cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.

Definition conv (cnt : Z) (d : dir) (a : parg) : M St Z :=
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
match a with
| PA_s s =>
if negb (d_ty d =? T_PTR) then munr else

if (p <? 0) && (INT_MAX <=? zlength s) then munr else
let n := if p <? 0 then zlength s else Z.min (zlength s) p in
conv_tail cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
| PA_i i =>
if negb (d_ty d =? T_INT) then munr else
if t =? 99 then
conv_tail cnt (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256]
else
let argi := i mod 2^64 in

let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
conv_int cnt fl w p xp argi prefix (dec_digits argi)
| PA_li i =>
if negb (d_ty d =? T_LONG) then munr else
let argi := i mod 2^64 in
let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
conv_int cnt fl w p xp argi prefix (dec_digits argi)
| PA_lu u =>
if negb (d_ty d =? T_ULONG) || negb (t =? 117) then munr else
conv_int cnt fl w p xp u [] (dec_digits u)
| PA_u u =>
if negb (d_ty d =? T_UINT) then munr else
if t =? 117 then conv_int cnt fl w p xp u [] (dec_digits u)
else

let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
then (if t =? 120 then [48; 120] else [48; 88]) else [] in
conv_int cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
| PA_g dd =>
if negb (d_ty d =? T_DBL) then munr else
if xp && (p <? 0) then munr else
if (1 <? w) || (2^20 <=? p) then munr else
r <- OUTFP (f128_of_d dd) w p fl t ;;
if (r <? 0) || (INT_MAX - cnt <? r) then munr else mret (cnt + r)
end.

Fixpoint printf_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel} : M St Z :=
match fuel with
| O => munr
| S fuel' =>
match s with
| [] => munr
| c :: _ =>
if c =? 0 then mret cnt else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => munr
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end
then munr
else if 0 <? l then
(if INT_MAX - cnt <? l then munr
else OUT lit ;;; printf_loop fuel' s1 args (cnt + l))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
OUT [] ;;;
cnt' <- conv cnt d a ;;
printf_loop fuel' s3 args' cnt'
| _, _ => munr
end
end
end
end.

Definition printf_model (fmt : list Z) (args : list parg) : M St Z :=
printf_loop (Datatypes.length fmt) fmt args 0.
End PrintfModel.

Arguments mpad {St} OUT _ _ _ _.
Arguments conv_tail {St} OUT _ _ _ _ _ _.
Arguments conv_int {St} OUT _ _ _ _ _ _ _ _.
Arguments conv {St} OUT OUTFP _ _ _.
Arguments printf_loop {St} OUT OUTFP _ _ _ _.
Arguments printf_model {St} OUT OUTFP _ _.

Fixpoint fp_calls (fuel : nat) (s : list Z) (args : list parg) {struct fuel} : list (Z * Z * Z * Z * Z) :=
match fuel with
| O => []
| S fuel' =>
match s with
| [] => []
| c :: _ =>
if c =? 0 then [] else
let lit := lit_run s in
let s1 := skipn (Datatypes.length lit) s in
if 0 <? zlength lit then fp_calls fuel' s1 args
else match s1 with
| _ :: s2 =>
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match a with
| PA_g dd =>
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
(f128_of_d dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel' s3 args'
| _ => fp_calls fuel' s3 args'
end
| _, _ => []
end
| _ => []
end
end
end.

Definition pass1_ok (fmt : list Z) : bool :=
let lit := lit_run fmt in
(zlength lit <=? INT_MAX) &&
match skipn (Datatypes.length lit) fmt with
| [] => false
| c1 :: s2 =>
if c1 =? 0 then true
else match s2 with
| [] => false
| c2 :: _ => negb (c2 =? 37) && match parse_dir s2 with Some _ => true | None => false end
end
end.

Definition pad_pieces (c w l fl : Z) : option (list (list Z)) :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then Some []
else if 256 <=? w - l then None
else Some [zrepeat c (w - l)].

Definition tail_pieces (cnt fl w p : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
let pl := zlength prefix in
let n := zlength body in
let p := Z.max p n in
if INT_MAX - pl <? p then None else
let w := Z.max w (pl + p) in
if INT_MAX - cnt <? w then None else
let? p1 := pad_pieces 32 w (pl + p) fl in
let? p2 := pad_pieces 48 w (pl + p) (Z.lxor fl ZERO_PAD) in
let? p3 := pad_pieces 48 p n 0 in
let? p4 := pad_pieces 32 w (pl + p) (Z.lxor fl LEFT_ADJ) in
Some (p1 ++ [prefix] ++ p2 ++ p3 ++ [body] ++ p4, cnt + w).

Definition int_pieces (cnt fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) : option (list (list Z) * Z) :=
if xp && (p <? 0) then None else
let fl := if xp then Z.land fl (Z.lnot ZERO_PAD) else fl in
if (argi =? 0) && (p =? 0) then tail_pieces cnt fl w p prefix []
else tail_pieces cnt fl w (Z.max p (zlength body + (if argi =? 0 then 1 else 0))) prefix body.

Definition conv_pieces (cnt : Z) (d : dir) (a : parg) : option (list (list Z) * Z) :=
let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
match a with
| PA_s s =>
if negb (d_ty d =? T_PTR) then None else
if (p <? 0) && (INT_MAX <=? zlength s) then None else
let n := if p <? 0 then zlength s else Z.min (zlength s) p in
tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
| PA_i i =>
if negb (d_ty d =? T_INT) then None else
if t =? 99 then tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256] else
let argi := i mod 2^64 in
let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
int_pieces cnt fl w p xp argi prefix (dec_digits argi)
| PA_li i =>
if negb (d_ty d =? T_LONG) then None else
let argi := i mod 2^64 in
let '(argi, prefix) :=
if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
else (argi, []) in
int_pieces cnt fl w p xp argi prefix (dec_digits argi)
| PA_lu u =>
if negb (d_ty d =? T_ULONG) || negb (t =? 117) then None else
int_pieces cnt fl w p xp u [] (dec_digits u)
| PA_u u =>
if negb (d_ty d =? T_UINT) then None else
if t =? 117 then int_pieces cnt fl w p xp u [] (dec_digits u)
else
let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
then (if t =? 120 then [48; 120] else [48; 88]) else [] in
int_pieces cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
| PA_g _ => None
end.

Fixpoint printf_pieces_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel}
: option (list (list Z) * Z) :=
match fuel with
| O => None
| S fuel' =>
match s with
| [] => None
| c :: _ =>
if c =? 0 then Some ([], cnt) else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => None
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
else if 0 <? l then
(if INT_MAX - cnt <? l then None
else let? (ps, r) := printf_pieces_loop fuel' s1 args (cnt + l) in Some (lit :: ps, r))
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
let? (ps1, cnt') := conv_pieces cnt d a in
let? (ps, r) := printf_pieces_loop fuel' s3 args' cnt' in
Some ([] :: ps1 ++ ps, r)
| _, _ => None
end
end
end
end.

Definition printf_pieces (fmt : list Z) (args : list parg) : option (list (list Z) * Z) :=
printf_pieces_loop (Datatypes.length fmt) fmt args 0.

Definition FMT_emit : list Z := [37; 115; 10; 0].
Definition FMT_u04x : list Z := [117; 37; 48; 52; 120; 0].
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].
Definition FMT_g15 : list Z := [37; 49; 46; 49; 53; 103; 0].
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0].
Definition FMT_g17 : list Z := [37; 49; 46; 49; 55; 103; 0].
Definition FMT_d : list Z := [37; 100; 0].
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].
Definition A_FMT_emit : Z := 0x102a8.       Definition A_FMT_u04x : Z := 0x102c3.
Definition A_FMT_usage : Z := 0x102e5.      Definition A_FMT_g15 : Z := 0x10316.
Definition A_FMT_too_big : Z := 0x1032a.    Definition A_FMT_g17 : Z := 0x1034b.
Definition A_FMT_d : Z := 0x10352.          Definition A_FMT_cannot_open : Z := 0x10355.
Definition A_FMT_read_error : Z := 0x1036a.

#[using="Type"] Example pieces_emit_ex : printf_pieces FMT_emit [PA_s (str "hi")] = Some (pieces_emit (str "hi"), 3).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some (pieces_usage (str "prog"), 18).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some (pieces_cannot_open (str "f"), 19).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some (pieces_read_error (str "f"), 21).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_too_big_ex : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_d_ex1 : printf_pieces FMT_d [PA_i (-2147483648)] = Some ([[]; [45]; str "2147483648"], 11).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_d_ex2 : printf_pieces FMT_d [PA_i 0] = Some ([[]; []; [48]; []], 1).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_u04x_ex1 : printf_pieces FMT_u04x [PA_u 31] = Some ([[117]; []; []; [48; 48]; [49; 102]], 5).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pieces_u04x_ex2 : printf_pieces FMT_u04x [PA_u 1] = Some ([[117]; []; []; [48; 48; 48]; [49]], 5).
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example fp_calls_g17_ex : fp_calls 7 FMT_g17 [PA_g 5] = [(f128_of_d 5, 1, 17, 0, 103)].
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example pass1_ok_ex : map pass1_ok [FMT_emit; FMT_u04x; FMT_usage; FMT_g15; FMT_too_big; FMT_g17; FMT_d; FMT_cannot_open; FMT_read_error]
= repeat true 9.
Proof. vm_compute. reflexivity. Qed.

End G.
End Printf_model.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. Unset Keyed Unification.

Record pe_saved := PES { pe_ra : word; pe_s0 : word; pe_s1 : word; pe_s2 : word; pe_s3 : word; pe_s4 : word;
pe_s5 : word; pe_s6 : word; pe_s7 : word; pe_s8 : word; pe_s9 : word; pe_s10 : word; pe_s11 : word }.

Record pe_fix := PEF { pf_tk : Z; pf_oldl : Z; pf_newl : Z; pf_len : Z ;
pf_lenr : Z ;
pf_sb : Z ; pf_spf : Z ;
pf_md : Model ;
pf_mxd : Z ;
pf_fl : Z  }.
