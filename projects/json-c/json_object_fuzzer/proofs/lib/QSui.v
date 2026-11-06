(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Local Open Scope Z_scope.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition esyn (e : ev) : Prop :=
match e with
| EMunmap _ _ => True
| EMmap a len prot flags => prot = PROT_RW /\ Z.land flags MAP_FIXED = 0 /\ len mod 4096 = 0 /\ 0 < len <= 2^26
| EUndef _ => True
| _ => False
end.
Definition is_mmap (e : ev) : bool := match e with EMmap _ _ _ _ => true | _ => false end.

Fixpoint tsynP {R} (P : R -> Prop) (t : M R) (N : nat) : Prop :=
match t with
| SRet r => P r
| SVis e k => esyn e /\ (if is_mmap e then exists N', N = S N' /\ forall z, tsynP P (k z) N' else forall z, tsynP P (k z) N)
end.
Definition tsyn {R} (t : M R) (N : nat) : Prop := tsynP (fun _ => True) t N.

Lemma tsynP_mono : forall {R} (P : R -> Prop) (t : M R) N N', tsynP P t N -> (N <= N')%nat -> tsynP P t N'.
Proof.
induction t as [r|e k IH]; intros N N' H Hle; [exact H|]. cbn [tsynP] in *. destruct H as [He H]. split; [exact He|].
destruct (is_mmap e).
- destruct H as (N0 & -> & H). destruct N' as [|N'']; [lia|]. exists N''. split; [reflexivity|]. intros z. eapply IH; [apply H| lia].
- intros z. eapply IH; [apply H| exact Hle].
Qed.

Lemma tsynP_bind : forall {R S} (Q : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) N,
tsynP Q t N -> (forall r, Q r -> tsynP P (f r) 0) -> tsynP P (sbind t f) N.
Proof.
induction t as [r|e k IH]; intros f N H Hf.
- cbn [sbind]. eapply tsynP_mono; [apply Hf; exact H| lia].
- cbn [sbind tsynP] in *. destruct H as [He H]. split; [exact He|]. destruct (is_mmap e).
+ destruct H as (N0 & -> & H). exists N0. split; [reflexivity|]. intros z. apply IH; [apply H| exact Hf].
+ intros z. apply IH; [apply H| exact Hf].
Qed.

Lemma tsyn_undef : forall {R} (P : R -> Prop) w (k : Z -> M R) N, (forall z, tsynP P (k z) N) -> tsynP P (SVis (EUndef w) k) N.
Proof. intros R P w k N H. cbn. split; [exact I| exact H]. Qed.

Lemma tsyn_bad_answer : forall {R} (P : R -> Prop) (bail : M R) N, tsynP P bail N -> tsynP P (bad_answer bail) N.
Proof. intros R P bail N H. unfold bad_answer. apply tsyn_undef. intros _. exact H. Qed.

Lemma tsyn_guard : forall {R} (P : R -> Prop) tag (c : bool) (k bail : M R) N, tsynP P k N -> tsynP P bail N -> tsynP P (guard tag c k bail) N.
Proof. intros R P tag c k bail N Hk Hb. unfold guard. destruct c; [exact Hk| apply tsyn_undef; intros _; exact Hb]. Qed.

Definition cntm (st : mstate) : Z := c_avail_meta_count (s_ctx st).

Lemma cntm_dequeue : forall h m st, cntm (dequeue h m st) = cntm st.
Proof.
intros h m st. unfold dequeue.
destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m))).
- destruct (m_prev (get_meta_rec st m)); destruct (m_next (get_meta_rec st m));
match goal with |- context [if ?c then _ else _] => destruct c end; destruct h; reflexivity.
- destruct h; reflexivity.
Qed.
Lemma cntm_upd_meta : forall m f st, cntm (upd_meta m f st) = cntm st.
Proof. intros. reflexivity. Qed.

Lemma cntm_decay_bounces : forall sc st, cntm (decay_bounces sc st) = cntm st.
Proof. intros. unfold decay_bounces. destruct (_ && _); reflexivity. Qed.
Lemma cntm_set_group_active_idx : forall g ai st, cntm (set_group_active_idx g ai st) = cntm st.
Proof. intros. unfold set_group_active_idx. destruct (get_group st g); reflexivity. Qed.
Lemma cntm_step_seq : forall st, cntm (step_seq st) = cntm st.
Proof. intros. unfold step_seq. destruct (_ =? 255); reflexivity. Qed.
Lemma cntm_account_bounce : forall sc st, cntm (account_bounce sc st) = cntm st.
Proof. intros. unfold account_bounce. repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity. Qed.

Lemma tsyn_alloc_meta : forall {R} (P : R -> Prop) st (k : mstate -> optr -> M R) bail N,
1 <= cntm st ->
(forall st' om, cntm st - 1 <= cntm st' -> tsynP P (k st' om) N) ->
tsynP P bail N ->
tsynP P (alloc_meta st k bail) N.
Proof.
intros R P st k bail N Hc Hk Hb. unfold alloc_meta.
set (st0 := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st).
assert (E0 : cntm st0 = cntm st) by (unfold st0; destruct (c_init_done (ctx st) =? 0); reflexivity).
destruct (c_free_meta_head (ctx st0)) as [m|].
- apply Hk. rewrite cntm_dequeue, E0. lia.
- assert (Hne : negb (c_avail_meta_count (ctx st0) =? 0) = true).
{ apply negb_true_iff. apply Z.eqb_neq. unfold cntm, ctx in *. lia. }
rewrite Hne. unfold am_take. destruct (c_avail_meta (ctx st0)) as [m|]; [| apply tsyn_undef; intros _; exact Hb].
apply Hk. rewrite cntm_upd_meta. unfold cntm, upd_ctx, ctx in *. cbn. lia.
Qed.

Lemma tsyn_queue : forall {R} (P : R -> Prop) h m st (k : mstate -> M R) bail N,
(forall st', cntm st' = cntm st -> tsynP P (k st') N) -> tsynP P bail N -> tsynP P (queue h m st k bail) N.
Proof.
intros R P h m st k bail N Hk Hb. unfold queue. apply tsyn_guard; [| exact Hb]. apply tsyn_guard; [| exact Hb].
destruct (get_head st h) as [hd|]; apply Hk; [destruct (m_prev (get_meta_rec st hd)); reflexivity|].
destruct h; reflexivity.
Qed.

Lemma tsyn_free_meta : forall {R} (P : R -> Prop) m st (k : mstate -> M R) bail N,
(forall st', cntm st' = cntm st -> tsynP P (k st') N) -> tsynP P bail N -> tsynP P (free_meta m st k bail) N.
Proof. intros R P m st k bail N Hk Hb. unfold free_meta. apply tsyn_queue; [| exact Hb]. intros st' E. apply Hk. rewrite E. reflexivity. Qed.

Lemma tsyn_activate_group : forall {R} (P : R -> Prop) m st (k : mstate -> Z -> M R) bail N,
(forall st' v, cntm st' = cntm st -> tsynP P (k st' v) N) -> tsynP P bail N -> tsynP P (activate_group m st k bail) N.
Proof. intros R P m st k bail N Hk Hb. unfold activate_group. apply tsyn_guard; [| exact Hb]. apply Hk. reflexivity. Qed.

Local Opaque span_loop.
Lemma tsyn_try_avail : forall {R} (P : R -> Prop) sc st (k : mstate -> Z -> M R) bail N,
(forall st' v, cntm st' = cntm st -> tsynP P (k st' v) N) -> tsynP P bail N -> tsynP P (try_avail sc st k bail) N.
Proof.
intros R P sc st k bail N Hk Hb. unfold try_avail.
destruct (active st sc) as [m|]; [| apply Hk; reflexivity].
destruct (negb (m_avail (get_meta_rec st m) =? 0)); [unfold ta_fin; apply Hk; reflexivity|].
match goal with |- tsynP _ (match ?X with _ => _ end) _ => set (step1 := X) end.
assert (F1 : forall st1 m1, step1 = Some (st1, m1) -> cntm st1 = cntm st).
{ unfold step1. intros st1 m1 E. destruct (m_freed (get_meta_rec st m) =? 0).
- destruct (active (dequeue (LActive sc) m st) sc); inversion E; subst. apply cntm_dequeue.
- destruct (m_next (get_meta_rec st m)); inversion E; subst. reflexivity. }
destruct step1 as [[st1 m1]|].
2:{ destruct (m_freed (get_meta_rec st m) =? 0); [apply Hk; apply cntm_dequeue| apply tsyn_undef; intros _; exact Hb]. }
specialize (F1 st1 m1 eq_refl).
match goal with |- tsynP _ (match ?X with pair _ _ => _ end) _ => destruct X as [[st2 m2] mask0] eqn:E2 end.
assert (F2 : cntm st2 = cntm st1).
{ revert E2. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end.
- destruct (m_next (get_meta_rec st1 m1)); intros E2; injection E2 as E2a _ _; rewrite <- E2a; reflexivity.
- intros E2; injection E2 as E2a _ _; rewrite <- E2a; reflexivity. }
clear E2.
match goal with |- tsynP _ (match ?X with pair _ _ => _ end) _ => destruct X as [st3 m3] eqn:E3 end.
assert (F3 : cntm st3 = cntm st2).
{ revert E3. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end.
- match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end.
+ destruct (m_next (get_meta_rec st2 m2)); intros E3; injection E3 as E3a _; rewrite <- E3a; reflexivity.
+ destruct (m_mem (get_meta_rec st2 m2)); intros E3; injection E3 as E3a _; rewrite <- E3a; [apply cntm_set_group_active_idx| reflexivity].
- intros E3; injection E3 as E3a _; rewrite <- E3a; reflexivity. }
clear E3.
apply tsyn_activate_group; [| exact Hb]. intros st4 mask F4.
apply tsyn_guard; [| exact Hb]. unfold ta_fin. apply Hk. rewrite cntm_upd_meta, cntm_decay_bounces. congruence.
Qed.

Lemma nth_Forall : forall {A} (P : A -> Prop) l d n, Forall P l -> P d -> P (nth n l d).
Proof. intros A P l d n Hl Hd. revert n. induction Hl; intros [|n]; cbn; auto. Qed.

Lemma size_class_bound : forall i, 0 <= size_class i <= 8191.
Proof. intros i. unfold size_class. apply nth_Forall; [| lia]. unfold size_classes. repeat constructor; lia. Qed.

Definition cnt_ok (c : Z) : Prop := 0 <= c <= 32.

Lemma small_cnt_ok : forall sc i, cnt_ok (small_cnt sc i).
Proof.
intros sc i. unfold small_cnt. apply nth_Forall; [| unfold cnt_ok; lia].
apply (nth_Forall (fun l => Forall cnt_ok l)); [| constructor].
unfold small_cnt_tab, cnt_ok. repeat constructor; lia.
Qed.

Lemma small_cnt_pick_ok : forall sc u, cnt_ok (small_cnt_pick sc u).
Proof. intros. unfold small_cnt_pick. repeat destruct (negb _); apply small_cnt_ok. Qed.

Lemma med_cnt_ok : forall i, cnt_ok (med_cnt i).
Proof. intros. unfold med_cnt. apply nth_Forall; [| unfold cnt_ok; lia]. unfold med_cnt_tab, cnt_ok. repeat constructor; lia. Qed.

Lemma shiftr1_ok : forall c, cnt_ok c -> cnt_ok (Z.shiftr c 1).
Proof. intros c [H1 H2]. unfold cnt_ok. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]. Qed.

Lemma halve_even_ok : forall f c u, cnt_ok c -> cnt_ok (halve_even f c u).
Proof. induction f as [|f IH]; intros c u H; cbn [halve_even]; [exact H|]. destruct (_ && _); [apply IH, shiftr1_ok, H| exact H]. Qed.

Lemma halve_big_ok : forall f c sz, cnt_ok c -> cnt_ok (halve_big f c sz).
Proof. induction f as [|f IH]; intros c sz H; cbn [halve_big]; [exact H|]. destruct (_ <=? _); [apply IH, shiftr1_ok, H| exact H]. Qed.

Lemma round_up_pg_facts : forall x, 0 <= x -> x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
intros x Hx. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)) as Hm.
split; [lia|].
rewrite Z.add_mod by lia. rewrite Z.mod_mod by lia. rewrite <- Z.add_mod by lia.
replace (x + - x) with 0 by lia. reflexivity.
Qed.

Lemma esyn_mmap_group : forall needed, 0 < needed <= 2^26 -> needed mod 4096 = 0 ->
esyn (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)).
Proof. intros needed Hn Hm. cbn [esyn]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hm| lia]. Qed.

Lemma tsyn_ag_tail : forall {R} (P : R -> Prop) st sc m p cnt ai (k : mstate -> optr -> M R) N,
(forall st' om, cntm st' = cntm st -> tsynP P (k st' om) N) -> tsynP P (ag_tail lay_none st sc m p cnt ai k) N.
Proof. intros. unfold ag_tail. apply H. reflexivity. Qed.

Section AG.
Variable R : Type.
Variable P : R -> Prop.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Variable f : Z.
Hypothesis Hf : 0 <= f.
Variable okj : Z -> Prop.
Hypothesis Hrec : forall st j req k bail, okj j -> f <= cntm st -> 0 <= req <= 2^25 ->
(forall st' v, cntm st - f <= cntm st' -> tsynP P (k st' v) 0) -> tsynP P bail 0 -> tsynP P (rec st j req k bail) 1.

Lemma tsyn_alloc_group : forall st sc req (k : mstate -> optr -> M R) bail,

(forall cnt, In cnt (QSfG.cnt0_list sc) -> (PGSZ / 2 <? UNIT * size_class sc * QSfG.bump (UNIT * size_class sc) cnt + UNIT) = false ->
okj (size_to_class (UNIT + QSfG.bump (UNIT * size_class sc) cnt * (UNIT * size_class sc) - IB))) ->
f + 1 <= cntm st -> 0 <= req <= 2^25 ->
(forall st' om, cntm st - (f + 1) <= cntm st' -> tsynP P (k st' om) 0) -> tsynP P bail 0 ->
tsynP P (alloc_group R lay_none rec st sc req k bail) 1.
Proof.
intros st sc req k bail Hok Hc Hreq Hk Hb. unfold alloc_group.
assert (Hb1 : tsynP P bail 1) by (eapply tsynP_mono; [exact Hb| lia]).
apply tsyn_alloc_meta; [lia| | exact Hb1].
intros st1 [m|] Hc1; [| eapply tsynP_mono; [apply Hk; lia| lia]].
set (size := UNIT * size_class sc) in *.
pose proof (size_class_bound sc) as HSZ. assert (Hsize : 0 <= size <= 16 * 8191) by (unfold size, UNIT; lia).
set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st1 sc)
else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) size).
assert (Hcnt0 : cnt_ok cnt0).
{ unfold cnt0. destruct (sc <? 9); [apply small_cnt_pick_ok| apply halve_big_ok, halve_even_ok, med_cnt_ok]. }
assert (Hin0 : In cnt0 (QSfG.cnt0_list sc)) by (apply (QSfG.cnt0_in sc (usage st1 sc))).
set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0).
assert (Ecnt1 : cnt1 = QSfG.bump size cnt0) by reflexivity.
assert (Hcnt1 : cnt_ok cnt1) by (unfold cnt1; destruct (_ && _); [unfold cnt_ok; lia| exact Hcnt0]).
specialize (Hok cnt0 Hin0). fold size in Hok. rewrite <- Ecnt1 in Hok.
clearbody cnt1. clear Hcnt0 Hin0 Ecnt1. clearbody cnt0.
destruct (PGSZ / 2 <? size * cnt1 + UNIT) eqn:EB.
-
match goal with |- context [if ?c then (if (Z.land sc 3 =? 1) && ?d then 2 else ?rest) else cnt1] =>
set (cnt2 := if c then (if (Z.land sc 3 =? 1) && d then 2 else rest) else cnt1) in * end.
assert (Hcnt2 : cnt_ok cnt2).
{ unfold cnt2. repeat match goal with |- cnt_ok (if ?c then _ else _) => destruct c end; try exact Hcnt1; unfold cnt_ok; lia. }
clearbody cnt2.
match goal with |- tsynP _ (match ?X with pair _ _ => _ end) _ => destruct X as [cnt3 needed] eqn:EP end.
assert (Hneeded : 0 < needed <= 2^26 /\ needed mod 4096 = 0).
{ assert (H1 : 0 < round_up_pg (req + IB + UNIT) <= 2^26 /\ round_up_pg (req + IB + UNIT) mod 4096 = 0).
{ pose proof (round_up_pg_facts (req + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold IB, UNIT in *. lia. }
assert (H2 : 0 < round_up_pg (size * cnt2 + UNIT) <= 2^26 /\ round_up_pg (size * cnt2 + UNIT) mod 4096 = 0).
{ unfold cnt_ok in Hcnt2.
assert (Hp0 : 0 <= size * cnt2) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hp1 : size * cnt2 <= (16 * 8191) * 32) by (apply Z.mul_le_mono_nonneg; lia).
pose proof (round_up_pg_facts (size * cnt2 + UNIT) ltac:(unfold UNIT; lia)). unfold UNIT in *. lia. }
revert EP. repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; intros EP; injection EP as _ <-; assumption. }
clear EP. destruct Hneeded as [Hn1 Hn2].
cbn [tsynP is_mmap]. split; [apply esyn_mmap_group; assumption|].
exists 0%nat. split; [reflexivity|]. intros r.
destruct (negb _); [apply tsyn_bad_answer; exact Hb|].
destruct (is_err r).
{ apply tsyn_free_meta; [| exact Hb]. intros st2 E2. apply Hk. rewrite E2, cntm_step_seq, cntm_account_bounce. lia. }
destruct (new_region RKGroup r needed (step_seq (account_bounce sc st1))) as [st2 rid] eqn:ENR.
assert (E2 : cntm st2 = cntm st1).
{ unfold new_region in ENR. injection ENR as <- _. unfold cntm. cbn. fold (cntm (step_seq (account_bounce sc st1))).
rewrite cntm_step_seq, cntm_account_bounce. reflexivity. }
apply tsyn_ag_tail. intros st4 om E4. apply Hk. rewrite E4. unfold cntm in *. cbn. cbn in E2. lia.
-
apply Hrec.
+ apply Hok. reflexivity.
+ lia.
+ unfold cnt_ok in Hcnt1. unfold UNIT, IB in *.
assert (0 <= cnt1 * size) by (apply Z.mul_nonneg_nonneg; lia).
assert (cnt1 * size <= 32 * (16 * 8191)) by (apply Z.mul_le_mono_nonneg; lia). lia.
+ intros st2 idx E2. destruct (idx <? 0).
{ apply tsyn_free_meta; [| exact Hb]. intros st3 E3. apply Hk. rewrite E3. lia. }
destruct (active st2 _); [| apply tsyn_undef; intros _; exact Hb].
apply tsyn_ag_tail. intros st4 om E4. apply Hk. rewrite E4, cntm_upd_meta. cbn [lh_nest lay_none]. lia.
+ exact Hb.
Qed.
End AG.

Definition lvz (sc : Z) : Z := Z.max 0 (24 - sc).

Lemma nest_class : forall sc cnt, 0 <= sc < 48 -> In cnt (QSfG.cnt0_list sc) ->
(PGSZ / 2 <? UNIT * size_class sc * QSfG.bump (UNIT * size_class sc) cnt + UNIT) = false ->
let j := size_to_class (UNIT + QSfG.bump (UNIT * size_class sc) cnt * (UNIT * size_class sc) - IB) in sc < j <= 23.
Proof.
intros sc cnt Hsc Hin Hb.
pose proof (QSfG.forallb_zrange QSfG.ag_check_sc 0 48 sc QSfG.ag_check_true ltac:(lia) ltac:(lia)) as H.
unfold QSfG.ag_check_sc in H. cbv zeta in H. rewrite forallb_forall in H. specialize (H cnt Hin). cbv beta in H.
rewrite Hb in H. apply QSfG.nest_ok_sound in H. cbv zeta in H. destruct H as (_ & H & _). exact H.
Qed.

Lemma tsyn_alloc_slot : forall {R} (P : R -> Prop) fuel st sc req (k : mstate -> Z -> M R) bail,
0 <= sc < 48 -> lvz sc + 1 <= cntm st -> 0 <= req <= 2^25 ->
(forall st' v, cntm st - (lvz sc + 1) <= cntm st' -> tsynP P (k st' v) 0) -> tsynP P bail 0 ->
tsynP P (alloc_slot lay_none fuel st sc req k bail) 1.
Proof.
intros R P fuel. induction fuel as [|f IH]; intros st sc req k bail Hsc Hc Hreq Hk Hb.
- cbn [alloc_slot]. apply tsyn_undef. intros _. eapply tsynP_mono; [exact Hb| lia].
- cbn [alloc_slot].
assert (Hb1 : tsynP P bail 1) by (eapply tsynP_mono; [exact Hb| lia]).
assert (Hlv : 0 <= lvz sc) by (unfold lvz; lia).
apply tsyn_try_avail; [| exact Hb1]. intros st1 first E1.
destruct (negb (first =? 0)); [eapply tsynP_mono; [apply Hk; lia| lia]|].
apply (tsyn_alloc_group R P (alloc_slot lay_none f) (lvz sc) Hlv (fun j => sc < j <= 23)).
+ intros st2 j req2 k2 bail2 Hj Hc2 Hr2 Hk2 Hb2. apply IH; [lia| unfold lvz in *; lia| exact Hr2| | exact Hb2].
intros st' v Hst'. apply Hk2. unfold lvz in *. lia.
+ intros cnt Hin Hbr. exact (nest_class sc cnt Hsc Hin Hbr).
+ lia.
+ exact Hreq.
+ intros st2 [g|] E2; [| apply Hk; lia]. apply tsyn_queue; [| exact Hb]. intros st4 E4. apply Hk. rewrite E4, cntm_upd_meta. lia.
+ exact Hb.
Qed.

Lemma tsyn_malloc_small_ctrl : forall {R} (P : R -> Prop) st n (k : mstate -> option (aptr * Z) -> M R) bail,
25 <= cntm st -> 0 <= n < MMAP_THRESHOLD ->
(forall st' r, cntm st - 25 <= cntm st' -> tsynP P (k st' r) 0) -> tsynP P bail 0 ->
tsynP P (malloc_small_ctrl lay_none st n k bail) 1.
Proof.
intros R P st n k bail Hc Hn Hk Hb. unfold malloc_small_ctrl.
pose proof (QSfG.size_to_class_ok n Hn) as [Hsc0 _].
set (sc0 := size_to_class n) in *.
match goal with |- context [active st ?SC] => match SC with sc0 => fail 1 | _ => set (sc := SC) in * end end.
assert (Hsc : 0 <= sc < 48).
{ unfold sc. destruct (active st sc0); [exact Hsc0|].
destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| exact Hsc0].
match goal with |- context [if ?c then _ else _] => destruct c end; [| exact Hsc0].
apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E Ev]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E4 E32].
apply Z.leb_le in E4. apply Z.ltb_lt in E32. rewrite (QSfG.lor1_even sc0 ltac:(lia) Ev). lia. }
clearbody sc.
assert (Hlv : lvz sc + 1 <= 25) by (unfold lvz; lia).
assert (HS : tsynP P (alloc_slot lay_none FUEL st sc n
(fun st1 idx => if idx <? 0 then k st1 None else match active st1 sc with Some gp => k st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => bail) end) bail) 1).
{ apply tsyn_alloc_slot; [exact Hsc| lia| unfold MMAP_THRESHOLD in Hn; lia| | exact Hb].
intros st1 idx E1. destruct (idx <? 0); [apply Hk; lia|]. destruct (active st1 sc); [apply Hk; lia| apply tsyn_undef; intros _; exact Hb]. }
destruct (active st sc) as [gp|]; [| exact HS].
match goal with |- tsynP _ (if ?b then _ else _) _ => destruct b end; [| exact HS].
eapply tsynP_mono; [apply Hk; rewrite cntm_upd_meta; lia| lia].
Qed.

Theorem tsyn_cmalloc : forall cs n,
25 <= cntm cs -> 0 <= n < MMAP_THRESHOLD ->
tsynP (fun r : mstate * option cptr => cntm cs - 25 <= cntm (fst r)) (cmalloc cs n) 1.
Proof.
intros cs n Hc Hn. unfold cmalloc.
apply (tsynP_bind (fun r : mstate * option (aptr * Z) => cntm cs - 25 <= cntm (fst r))).
- unfold malloc_core. destruct (size_overflows n); [cbn; lia|].
assert (E : (MMAP_THRESHOLD <=? n) = false) by (apply Z.leb_gt; lia). rewrite E.
apply tsyn_malloc_small_ctrl; [exact Hc| exact Hn| intros st' r Hst'; cbn; exact Hst'| cbn; lia].
- intros [st1 r] Hr. cbn [fst] in Hr. cbn. exact Hr.
Qed.

Lemma cntm_record_seq : forall sc st, cntm (record_seq sc st) = cntm st.
Proof. intros. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.

Lemma tsyn_dec_slots : forall {R} (P : R -> Prop) st p (k : aptr -> Z -> M R) bail N,
(forall m idx, tsynP P (k m idx) N) -> tsynP P bail N -> tsynP P (dec_slots st p k bail) N.
Proof. intros R P st p k bail N Hk Hb. unfold dec_slots. destruct (s_slots st !! p) as [[m idx]|]; [apply Hk| apply tsyn_undef; intros _; exact Hb]. Qed.

Lemma tsyn_free_group : forall {R} (P : R -> Prop) (rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M R) -> M R -> M R) N,
(forall st m idx k bail, (forall st' mi, cntm st' = cntm st -> tsynP P (k st' mi) N) -> tsynP P bail N -> tsynP P (rec st m idx k bail) N) ->
forall st g (k : mstate -> mapinfo -> M R) bail,
(forall st' mi, cntm st' = cntm st -> tsynP P (k st' mi) N) -> tsynP P bail N -> tsynP P (free_group R dec_slots rec st g k bail) N.
Proof.
intros R P rec N Hrec st g k bail Hk Hb. unfold free_group.
set (st1 := if m_sizeclass (get_meta_rec st g) <? 48 then _ else st).
assert (E1 : cntm st1 = cntm st) by (unfold st1; destruct (_ <? 48); reflexivity).
destruct (m_mem (get_meta_rec st g)) as [p|]; [| apply tsyn_undef; intros _; exact Hb].
destruct (negb (m_maplen (get_meta_rec st g) =? 0)).
- apply tsyn_free_meta; [| exact Hb]. intros st3 E3. apply Hk. rewrite E3, cntm_record_seq, cntm_step_seq. exact E1.
- apply tsyn_dec_slots; [| exact Hb]. intros m idx. apply Hrec; [| exact Hb].
intros st3 mi E3. apply tsyn_free_meta; [| exact Hb]. intros st4 E4. apply Hk. rewrite E4, E3. exact E1.
Qed.

Lemma tsyn_nontrivial_free : forall {R} (P : R -> Prop) fuel st g i (k : mstate -> mapinfo -> M R) bail N,
(forall st' mi, cntm st' = cntm st -> tsynP P (k st' mi) N) -> tsynP P bail N -> tsynP P (nontrivial_free dec_slots fuel st g i k bail) N.
Proof.
intros R P fuel. induction fuel as [|f IH]; intros st g i k bail N Hk Hb; cbn [nontrivial_free].
- apply tsyn_undef. intros _. exact Hb.
- assert (FG : forall st0, cntm st0 = cntm st -> tsynP P (free_group R dec_slots (nontrivial_free dec_slots f) st0 g k bail) N).
{ intros st0 E0. apply tsyn_free_group; [| | exact Hb].
- intros st1 m idx k1 bail1 Hk1 Hb1. apply IH; assumption.
- intros st' mi E'. apply Hk. rewrite E'. exact E0. }
destruct (_ && okay_to_free st g).
+ destruct (m_next (get_meta_rec st g)); [| apply FG; reflexivity].
apply tsyn_guard; [| exact Hb].
destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)); [| apply FG; apply cntm_dequeue].
destruct (active (dequeue _ g st) _); [| apply FG; apply cntm_dequeue].
apply tsyn_activate_group; [| exact Hb]. intros st2 _ E2. apply FG. rewrite E2. apply cntm_dequeue.
+ destruct (_ =? 0); [| apply Hk; reflexivity].
apply tsyn_guard; [| exact Hb].
destruct (negb _); [apply tsyn_queue; [intros st' E'; apply Hk; rewrite cntm_upd_meta; exact E'| exact Hb]| apply Hk; reflexivity].
Qed.

Theorem tsyn_cfree : forall cs p, tsynP (fun cs' : mstate => cntm cs' = cntm cs) (cfree cs p) 0.
Proof.
intros cs [s|]; cbn [cfree]; [| reflexivity].
destruct (s_slots cs !! s) as [[g idx]|]; [| apply tsyn_undef; intros _; reflexivity].
apply (tsynP_bind (fun st1 : mstate => cntm st1 = cntm cs)); [| intros st1 E1; exact E1].
unfold free_tail. apply tsyn_guard; [| reflexivity].
destruct (negb _); [reflexivity|].
apply tsyn_nontrivial_free; [| reflexivity].
intros st2 [[base len]|] E2; [| exact E2].
destruct (negb (len =? 0)); [| exact E2].
cbn [tsynP is_mmap esyn]. split; [exact I|]. intros ru. destruct (munmap_answer_ok ru); [exact E2| apply tsyn_bad_answer; reflexivity].
Qed.

End RC__1.
