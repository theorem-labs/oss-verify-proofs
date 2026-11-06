(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR.
Import ListNotations. Unset Keyed Unification.
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

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs.

End G.
