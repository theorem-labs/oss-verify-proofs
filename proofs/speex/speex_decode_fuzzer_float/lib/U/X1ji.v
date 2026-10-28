(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1rd X1oc X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1jh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1jg.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
X1bs.impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> X1bs.impl segs atn t Q' ms.
Proof.
intros segs node R atn t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. exact (HQ r).
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
Qed.
Lemma implM_post_evt : forall segs {St A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
X1qx.implM segs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt segs (Q' a s') ms') -> X1qx.implM segs c s Q' ms.
Proof.
intros segs St A c s Q Q' ms H HQ. unfold X1qx.implM in *. eapply impl_post_evt; [exact H|].
intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I | apply HQ].
Qed.

Section Outs.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.
Context {St : Type}.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
Local Notation implM := (X1qx.implM segs).

Fixpoint outsk {B} (ps : list (list Z)) (k : M St B) : M St B :=
match ps with
| [] => k
| p :: ps' => OUT p ;;; outsk ps' k
end.

#[using="Type"] Lemma outsk_app : forall {B} ps qs (k : M St B), outsk (ps ++ qs) k = outsk ps (outsk qs k).
Proof. induction ps as [|p ps IH]; intros qs k; [reflexivity|]. cbn [outsk app]. rewrite IH. reflexivity. Qed.

#[using="Type"] Lemma outsk_mono : forall {B} ps (k1 k2 : M St B) Q,
(forall s ms, implM k1 s Q ms -> implM k2 s Q ms) ->
forall s ms, implM (outsk ps k1) s Q ms -> implM (outsk ps k2) s Q ms.
Proof.
induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
eapply implM_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
Qed.

#[using="Type"] Lemma mpad_outs : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
pad_pieces c w l fl = Some pp ->
implM (mbind (mpad OUT c w l fl) K) s Q ms -> implM (outsk pp (K tt)) s Q ms.
Proof.
intros B c w l fl pp K s Q ms P H. unfold mpad, pad_pieces in *.
destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
- inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H.
- destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [outsk].
eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
Qed.

#[using="Type"] Lemma out_outs : forall {B} p (K : unit -> M St B) s Q ms,
implM (mbind (OUT p) K) s Q ms -> implM (outsk [p] (K tt)) s Q ms.
Proof. intros B p K s Q ms H. cbn [outsk]. eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'. Qed.

#[using="Type"] Lemma conv_tail_outs : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
tail_pieces cnt fl w p prefix body = Some (ps, r) ->
implM (mbind (conv_tail OUT cnt fl w p prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p prefix body ps r K s Q ms T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta in H.
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
inversion T; subst. clear T.
match goal with |- implM (outsk ?L (K ?rr)) _ _ _ =>
replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
by (rewrite ?outsk_app; cbn [outsk]; rewrite ?outsk_app; cbn [outsk]; reflexivity) end.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P1) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s1 ms1 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x2 s2 ms2 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P2) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s3 ms3 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P3) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s4 ms4 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x5 s5 ms5 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P4) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s6 ms6 H.
apply implM_ret_l_rev in H. exact H.
Qed.

#[using="Type"] Lemma conv_int_outs : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
implM (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs; eassumption.
Qed.

#[using="Type"] Lemma conv_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
conv_pieces cnt d a = Some (ps, r) ->
implM (mbind (conv OUT OUTFP cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
destruct a as [str|i|u|dd].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|].
destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
eapply conv_tail_outs; eassumption.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (INTMAX_MAX <? i mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_outs; eassumption.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|].
destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
- discriminate.
Qed.

#[using="Type"] Lemma printf_loop_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
printf_pieces_loop fuel s args cnt = Some (ps, r) ->
implM (mbind (printf_loop OUT OUTFP fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof.
induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms P H; [discriminate|].
cbn [printf_pieces_loop] in P. cbn [printf_loop] in H.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H. }
cbv zeta in P. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
destruct (0 <? zlength lit).
- destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
eapply IH; [exact R | exact H'].
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P.
match goal with |- implM (outsk ?L (k ?rr)) _ _ _ =>
replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
apply implM_assoc_rev in H'. apply (conv_outs _ _ _ _ _ _ _ _ _ C) in H'.
eapply outsk_mono; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
Qed.

#[using="Type"] Theorem printf_model_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
printf_pieces fmt args = Some (ps, r) ->
implM (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loop_outs; [exact P | exact H]. Qed.
End Outs.

Ltac lhs_cbvs := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces] in l in change l with l' end.
Lemma zlength_nonneg' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma conv_pieces_s : forall cnt s, 0 <= cnt -> zlength s < INT_MAX - cnt ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} (PA_s s)
= Some ([[]; s], cnt + zlength s).
Proof.
intros cnt s Hc Hs. pose proof (zlength_nonneg' s) as H0.
unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_PTR Pos.eqb andb Z.ltb Z.compare].
replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; lia).
unfold tail_pieces. cbv zeta. rewrite firstn_all2 by (unfold zlength; lia).
change (zlength (@nil Z)) with 0.
replace (Z.max (zlength s) (zlength s)) with (zlength s) by lia.
replace (INT_MAX - 0 <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (0 + zlength s)) with (zlength s) by lia.
replace (INT_MAX - cnt <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces.
replace (zlength s <=? 0 + zlength s) with true by (symmetry; apply Z.leb_le; lia).
rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ].
reflexivity.
Qed.

Lemma ppl_unfold : forall fuel s args cnt,
printf_pieces_loop (S fuel) s args cnt =
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
else match printf_pieces_loop fuel s1 args (cnt + l) with Some (ps, r) => Some (lit :: ps, r) | None => None end)
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match conv_pieces cnt d a with
| Some (ps1, cnt') =>
match printf_pieces_loop fuel s3 args' cnt' with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end
| None => None
end
| _, _ => None
end
end
end.
Proof. reflexivity. Qed.

Lemma ppl_noargs_shift_gen : forall fuel s c0 ps r,
printf_pieces_loop fuel s [] c0 = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_pieces_loop fuel s [] (c0 + k) = Some (ps, r + k)).
Proof.
induction fuel as [|fuel IH]; intros s c0 ps r P; [discriminate|].
rewrite ppl_unfold in P. setoid_rewrite ppl_unfold.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. split; [lia|]. intros k _ _. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg' lit).
destruct (0 <? zlength lit).
- destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) [] (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. destruct (IH _ _ _ _ R) as [LE SH].
split; [lia|]. intros k Hk Hr.
replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; discriminate.
Qed.

Lemma ppl_noargs_shift : forall fuel s cnt ps r,
printf_pieces_loop fuel s [] 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
printf_pieces_loop fuel s [] cnt = Some (ps, cnt + r).
Proof.
intros fuel s cnt ps r P Hc Hr. destruct (ppl_noargs_shift_gen _ _ _ _ _ P) as [_ SH].
rewrite <- (Z.add_0_l cnt). rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed.

Ltac ppl_step := rewrite ppl_unfold; match goal with |- ?l = _ => let l' := eval cbv -[printf_pieces_loop conv_pieces] in l in change l with l' end.

Lemma dec_text_aux_digits : forall f x acc, dec_text_aux f x acc = digits_aux f 10 (fun v => 48 + v) x acc.
Proof. induction f as [|f IH]; intros x acc; [reflexivity|]. cbn [dec_text_aux digits_aux]. destruct (x =? 0); [reflexivity|]. apply IH. Qed.
Lemma dec_digits_text : forall x, dec_digits x = dec_text_aux 20 x [].
Proof. intros. unfold dec_digits. symmetry. apply dec_text_aux_digits. Qed.

Lemma digits_aux_length_le : forall f base dig x acc, (length (digits_aux f base dig x acc) <= f + length acc)%nat.
Proof. induction f as [|f IH]; intros; cbn [digits_aux]; [lia|]. destruct (x =? 0); [cbn; lia|]. specialize (IH base dig (x / base) (dig (x mod base) :: acc)). cbn in IH. lia. Qed.
Lemma digits_aux_length_ge : forall f base dig x acc, (length acc <= length (digits_aux f base dig x acc))%nat.
Proof. induction f as [|f IH]; intros; cbn [digits_aux]; [lia|]. destruct (x =? 0); [cbn; lia|]. specialize (IH base dig (x / base) (dig (x mod base) :: acc)). cbn in IH. lia. Qed.
Lemma dec_digits_length : forall x, 0 <= zlength (dec_digits x) <= 20.
Proof. intros. unfold dec_digits, zlength. pose proof (digits_aux_length_le 20 10 (fun v => 48 + v) x []). cbn [length] in *. lia. Qed.
Lemma digits_aux_S : forall f base dig x acc,
digits_aux (S f) base dig x acc = if x =? 0 then acc else digits_aux f base dig (x / base) (dig (x mod base) :: acc).
Proof. reflexivity. Qed.
Lemma dec_digits_nonnil : forall x, 0 < x -> 1 <= zlength (dec_digits x).
Proof.
intros x Hx. unfold dec_digits, zlength. rewrite digits_aux_S. replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (digits_aux_length_ge 19 10 (fun v => 48 + v) (x / 10) [48 + x mod 10]). cbn [length] in *. lia.
Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. reflexivity. Qed.

Lemma conv_pieces_d : forall cnt i, 0 <= cnt <= INT_MAX - 32 -> -2^31 <= i < 2^31 ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |} (PA_i i)
= Some ((if i <? 0 then [45] else []) :: (if i =? 0 then [[48]] else []) ++ [if i =? 0 then [] else dec_text_aux 20 (Z.abs i) []],
cnt + zlength (dec_text i)).
Proof.
intros cnt i Hc Hi.
unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty].
change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota. change (negb (T_INT =? T_INT)) with false. cbv iota.
change (negb (Z.land 0 MARK_POS =? 0)) with false. change (negb (Z.land 0 PAD_POS =? 0)) with false. cbv iota.

assert (IP : forall argi prefix, 0 <= argi -> zlength prefix <= 1 ->
int_pieces cnt 0 0 (-1) false argi prefix (dec_digits argi)
= Some (prefix :: (if argi =? 0 then [[48]] else []) ++ [dec_digits argi], cnt + zlength prefix + Z.max 1 (zlength (dec_digits argi)))).
{ intros argi prefix Ha Hp. pose proof (dec_digits_length argi) as DL. pose proof (zlength_nonneg' prefix) as PL.
unfold int_pieces. cbn [andb Z.ltb Z.eqb Pos.eqb].
destruct (Z.eqb_spec argi 0) as [->|NZ].
- cbn [andb]. rewrite dec_digits_0. change (zlength (@nil Z)) with 0. change (Z.max (-1) (0 + 1)) with 1.
unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0. change (Z.max 1 0) with 1.
replace (INT_MAX - zlength prefix <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (zlength prefix + 1)) with (zlength prefix + 1) by lia.
replace (INT_MAX - cnt <? zlength prefix + 1) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces. rewrite !Z.leb_refl. cbn [Z.land Z.lor Z.lxor LEFT_ADJ ZERO_PAD Z.eqb negb orb].
change (1 <=? 0) with false. cbn [orb]. change (256 <=? 1 - 0) with false. cbv iota.
cbn [app]. f_equal. f_equal. lia.
- cbn [andb]. pose proof (dec_digits_nonnil argi ltac:(lia)) as DN.
rewrite Z.add_0_r. replace (Z.max (-1) (zlength (dec_digits argi))) with (zlength (dec_digits argi)) by lia.
unfold tail_pieces. cbv zeta. rewrite Z.max_id.
replace (INT_MAX - zlength prefix <? zlength (dec_digits argi)) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (zlength prefix + zlength (dec_digits argi))) with (zlength prefix + zlength (dec_digits argi)) by lia.
replace (INT_MAX - cnt <? zlength prefix + zlength (dec_digits argi)) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces. rewrite !Z.leb_refl. cbn [Z.land Z.lor Z.lxor LEFT_ADJ ZERO_PAD Z.eqb negb orb].
cbn [app]. f_equal. f_equal. lia. }
destruct (Z.ltb_spec i 0) as [NEG|NNEG].
- replace (i mod 2 ^ 64) with ((i + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia). rewrite (Z.mod_small (i + 1 * 2^64)) by lia.
replace (INTMAX_MAX <? i + 1 * 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia).
replace (- (i + 1 * 2 ^ 64) mod 2 ^ 64) with ((- (i + 1 * 2 ^ 64) + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia).
replace (- (i + 1 * 2 ^ 64) + 1 * 2 ^ 64) with (- i) by lia. rewrite (Z.mod_small (- i)) by lia.
rewrite (IP (- i) [45] ltac:(lia) ltac:(apply Z.leb_le; reflexivity)). replace (- i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite dec_digits_text. replace (Z.abs i) with (- i) by lia.
unfold dec_text. replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (i <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [app]. f_equal. f_equal. pose proof (dec_digits_nonnil (- i) ltac:(lia)) as DN. rewrite dec_digits_text in DN.
unfold zlength in *. cbn [length]. lia.
- rewrite (Z.mod_small i) by lia.
replace (INTMAX_MAX <? i) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
rewrite (IP i [] ltac:(lia) ltac:(apply Z.leb_le; reflexivity)). rewrite dec_digits_text. replace (Z.abs i) with i by lia.
unfold dec_text. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eqb_spec i 0) as [->|NZ].
+ unfold zlength. cbn. f_equal. f_equal. lia.
+ cbn [app]. f_equal. f_equal. pose proof (dec_digits_nonnil i ltac:(lia)) as DN. rewrite dec_digits_text in DN.
unfold zlength in *. cbn [length]. lia.
Qed.

Lemma dec_text_length : forall i, -2^31 <= i < 2^31 -> 1 <= zlength (dec_text i) <= 21.
Proof.
intros i Hi. unfold dec_text. pose proof (dec_digits_length (Z.abs i)) as DL. rewrite dec_digits_text in DL.
destruct (Z.eqb_spec i 0); [unfold zlength; cbn; lia|].
assert (DN : 1 <= zlength (dec_digits (Z.abs i))) by (apply dec_digits_nonnil; lia). rewrite dec_digits_text in DN.
destruct (Z.ltb_spec i 0).
- replace (- i) with (Z.abs i) by lia. unfold zlength in *. cbn [length]. lia.
- replace (Z.abs i) with i in * by lia. lia.
Qed.

Lemma printf_pieces_emit : forall i, -2^31 <= i < 2^31 ->
printf_pieces FMT_emit [PA_i i] = Some (pieces_emit i, zlength (dec_text i) + 1).
Proof.
intros i Hi. pose proof (dec_text_length i Hi) as DL. unfold printf_pieces.
change (Datatypes.length FMT_emit) with 4%nat.
ppl_step. change X1jh.T_INT with T_INT. rewrite conv_pieces_d by (unfold INT_MAX; lia). rewrite Z.add_0_l.
rewrite (ppl_noargs_shift 3 [10; 0] (zlength (dec_text i)) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
unfold pieces_emit. destruct (i <? 0); destruct (i =? 0); reflexivity.
Qed.

Lemma printf_pieces_usage : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_usage) with 17%nat.
ppl_step. ppl_step. change X1jh.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 15 [32; 73; 78; 80; 85; 84; 10; 0] (7 + zlength s) [[32; 73; 78; 80; 85; 84; 10]] 7 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_usage. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_cannot_open : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_cannot_open) with 21%nat.
ppl_step. ppl_step. change X1jh.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 19 [10; 0] (17 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_cannot_open. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_read_error : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_read_error) with 23%nat.
ppl_step. ppl_step. change X1jh.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 21 [10; 0] (19 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_read_error. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_too_big : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.

Lemma printf_pieces_notify : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_notify [PA_s s] = Some (pieces_notify s, 15 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_notify) with 18%nat.
ppl_step. ppl_step. change X1jh.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 16 [10; 0] (14 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_notify. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_warning : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_warning [PA_s s] = Some (pieces_warning s, 10 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_warning) with 13%nat.
ppl_step. ppl_step. change X1jh.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 11 [10; 0] (9 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_warning. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma tail_pieces_shift : forall c0 fl w p prefix body ps r,
tail_pieces c0 fl w p prefix body = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> tail_pieces (c0 + k) fl w p prefix body = Some (ps, r + k)).
Proof.
intros c0 fl w p prefix body ps r T. unfold tail_pieces in *. cbv zeta in T |- *.
pose proof (zlength_nonneg' prefix). pose proof (zlength_nonneg' body).
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (Z.ltb_spec (INT_MAX - c0) (Z.max w (zlength prefix + Z.max p (zlength body)))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|]; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|]; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|]; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|]; [|discriminate].
inversion T; subst. split; [lia|]. intros k Hk Hr.
replace (INT_MAX - (c0 + k) <? Z.max w (zlength prefix + Z.max p (zlength body))) with false by (symmetry; apply Z.ltb_ge; lia).
f_equal. f_equal. lia.
Qed.

Lemma int_pieces_shift : forall c0 fl w p xp argi prefix body ps r,
int_pieces c0 fl w p xp argi prefix body = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> int_pieces (c0 + k) fl w p xp argi prefix body = Some (ps, r + k)).
Proof.
intros until r. unfold int_pieces. destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta.
destruct ((argi =? 0) && (p =? 0))%bool; apply tail_pieces_shift.
Qed.

Lemma conv_pieces_shift : forall c0 d a ps r,
conv_pieces c0 d a = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> conv_pieces (c0 + k) d a = Some (ps, r + k)).
Proof.
intros c0 d a ps r. unfold conv_pieces. cbv zeta. destruct a as [str|i|u|dd].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|]. destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
apply tail_pieces_shift.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (INTMAX_MAX <? i mod 2 ^ 64); [apply int_pieces_shift|].
destruct (negb (Z.land _ MARK_POS =? 0)); [apply int_pieces_shift|].
destruct (negb (Z.land _ PAD_POS =? 0)); apply int_pieces_shift.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|]. destruct (d_t d =? 117); apply int_pieces_shift.
- discriminate.
Qed.

Lemma ppl_shift_gen : forall fuel s args c0 ps r,
printf_pieces_loop fuel s args c0 = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_pieces_loop fuel s args (c0 + k) = Some (ps, r + k)).
Proof.
induction fuel as [|fuel IH]; intros s args c0 ps r P; [discriminate|].
rewrite ppl_unfold in P. setoid_rewrite ppl_unfold.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. split; [lia|]. intros k _ _. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg' lit).
destruct (0 <? zlength lit).
- destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. destruct (IH _ _ _ _ _ R) as [LE SH].
split; [lia|]. intros k Hk Hr.
replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces c0 d a) as [[ps1 c1']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' c1') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P.
destruct (conv_pieces_shift _ _ _ _ _ C) as [LE1 SH1]. destruct (IH _ _ _ _ _ R) as [LE2 SH2].
split; [lia|]. intros k Hk Hr. rewrite (SH1 k Hk ltac:(lia)). rewrite (SH2 k Hk Hr). reflexivity.
Qed.

Lemma ppl_shift : forall fuel s args cnt ps r,
printf_pieces_loop fuel s args 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
printf_pieces_loop fuel s args cnt = Some (ps, cnt + r).
Proof.
intros fuel s args cnt ps r P Hc Hr. destruct (ppl_shift_gen _ _ _ _ _ _ P) as [_ SH].
rewrite <- (Z.add_0_l cnt). rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma printf_pieces_warning_int : forall s i, zlength s < INT_MAX - 256 -> -2^31 <= i < 2^31 ->
printf_pieces FMT_warning_int [PA_s s; PA_i i] = Some (pieces_warning_int s i, 11 + zlength s + zlength (dec_text i)).
Proof.
intros s i Hs Hi. pose proof (zlength_nonneg' s) as H0. pose proof (dec_text_length i Hi) as DL. unfold printf_pieces.
change (Datatypes.length FMT_warning_int) with 16%nat.
ppl_step. ppl_step. change X1jh.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
assert (TL : printf_pieces_loop 14 [32; 37; 100; 10; 0] [PA_i i] 0
= Some ([32] :: [] :: ((if i <? 0 then [45] else []) :: (if i =? 0 then [[48]] else []) ++ [if i =? 0 then [] else dec_text_aux 20 (Z.abs i) []]) ++ [[10]],
2 + zlength (dec_text i))).
{ ppl_step. ppl_step. change X1jh.T_INT with T_INT. rewrite conv_pieces_d by (unfold INT_MAX; lia).
rewrite (ppl_noargs_shift 12 [10; 0] (1 + zlength (dec_text i)) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
f_equal. f_equal. lia. }
rewrite (ppl_shift 14 _ _ (9 + zlength s) _ _ TL) by (unfold INT_MAX in *; lia).
unfold pieces_warning_int. destruct (i <? 0); destruct (i =? 0); cbv -[zlength Z.add dec_text_aux dec_text Z.abs]; do 2 f_equal; lia.
Qed.

Lemma pass1_ok_emit : pass1_ok FMT_emit = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_usage : pass1_ok FMT_usage = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_cannot_open : pass1_ok FMT_cannot_open = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_read_error : pass1_ok FMT_read_error = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_too_big : pass1_ok FMT_too_big = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_notify : pass1_ok FMT_notify = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_warning : pass1_ok FMT_warning = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_warning_int : pass1_ok FMT_warning_int = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_s : forall fmt s, In fmt [FMT_usage; FMT_cannot_open; FMT_read_error; FMT_notify; FMT_warning] ->
fp_calls (Datatypes.length fmt) fmt [PA_s s] = [].
Proof. intros fmt s [<-|[<-|[<-|[<-|[<-|[]]]]]]; vm_compute; reflexivity. Qed.
Lemma fp_calls_emit : forall i, fp_calls (Datatypes.length FMT_emit) FMT_emit [PA_i i] = [].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma fp_calls_warning_int : forall s i, fp_calls (Datatypes.length FMT_warning_int) FMT_warning_int [PA_s s; PA_i i] = [].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma fp_calls_too_big : fp_calls (Datatypes.length FMT_too_big) FMT_too_big [PA_u 67108864] = [].
Proof. vm_compute. reflexivity. Qed.
