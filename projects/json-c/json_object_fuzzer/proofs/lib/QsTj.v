(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSui.
Import ListNotations.
Local Open Scope Z_scope.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Fixpoint tleaf {R} (t : M R) (P : R -> Prop) : Prop :=
match t with
| SRet r => P r
| SVis e k => forall z, tleaf (k z) P
end.

Lemma tleaf_bind : forall {R S} (t : M R) (f : R -> M S) (Q : R -> Prop) (P : S -> Prop),
tleaf t Q -> (forall r, Q r -> tleaf (f r) P) -> tleaf (sbind t f) P.
Proof.
induction t as [r|e k IH]; intros f Q P H Hf; cbn [sbind tleaf] in *; [apply Hf; exact H|].
intros z. eapply IH; [apply H| exact Hf].
Qed.

Lemma tleaf_undef : forall {R} w (k : Z -> M R) (P : R -> Prop), (forall z, tleaf (k z) P) -> tleaf (SVis (EUndef w) k) P.
Proof. intros R w k P H. exact H. Qed.

Lemma tleaf_bad_answer : forall {R} (bail : M R) (P : R -> Prop), tleaf bail P -> tleaf (bad_answer bail) P.
Proof. intros R bail P H. unfold bad_answer. apply tleaf_undef. intros _. exact H. Qed.

Lemma tleaf_guard : forall {R} tag (c : bool) (k bail : M R) (P : R -> Prop), tleaf k P -> tleaf bail P -> tleaf (guard tag c k bail) P.
Proof. intros R tag c k bail P Hk Hb. unfold guard. destruct c; [exact Hk| apply tleaf_undef; intros _; exact Hb]. Qed.

Lemma tleaf_alloc_meta : forall {R} st (k : mstate -> optr -> M R) bail (P : R -> Prop),
1 <= cntm st ->
(forall st' om, cntm st - 1 <= cntm st' -> tleaf (k st' om) P) ->
tleaf bail P ->
tleaf (alloc_meta st k bail) P.
Proof.
intros R st k bail P Hc Hk Hb. unfold alloc_meta.
set (st0 := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st).
assert (E0 : cntm st0 = cntm st) by (unfold st0; destruct (c_init_done (ctx st) =? 0); reflexivity).
destruct (c_free_meta_head (ctx st0)) as [m|].
- apply Hk. rewrite cntm_dequeue, E0. lia.
- assert (Hne : negb (c_avail_meta_count (ctx st0) =? 0) = true).
{ apply negb_true_iff. apply Z.eqb_neq. unfold cntm, ctx in *. lia. }
rewrite Hne. unfold am_take. destruct (c_avail_meta (ctx st0)) as [m|]; [| apply tleaf_undef; intros _; exact Hb].
apply Hk. rewrite cntm_upd_meta. unfold cntm, upd_ctx, ctx in *. cbn. lia.
Qed.

Lemma tleaf_queue : forall {R} h m st (k : mstate -> M R) bail (P : R -> Prop),
(forall st', cntm st' = cntm st -> tleaf (k st') P) -> tleaf bail P -> tleaf (queue h m st k bail) P.
Proof.
intros R h m st k bail P Hk Hb. unfold queue. apply tleaf_guard; [| exact Hb]. apply tleaf_guard; [| exact Hb].
destruct (get_head st h) as [hd|]; apply Hk; [destruct (m_prev (get_meta_rec st hd)); reflexivity|].
destruct h; reflexivity.
Qed.

Lemma tleaf_free_meta : forall {R} m st (k : mstate -> M R) bail (P : R -> Prop),
(forall st', cntm st' = cntm st -> tleaf (k st') P) -> tleaf bail P -> tleaf (free_meta m st k bail) P.
Proof. intros R m st k bail P Hk Hb. unfold free_meta. apply tleaf_queue; [| exact Hb]. intros st' E. apply Hk. rewrite E. reflexivity. Qed.

Lemma tleaf_activate_group : forall {R} m st (k : mstate -> Z -> M R) bail (P : R -> Prop),
(forall st' v, cntm st' = cntm st -> tleaf (k st' v) P) -> tleaf bail P -> tleaf (activate_group m st k bail) P.
Proof. intros R m st k bail P Hk Hb. unfold activate_group. apply tleaf_guard; [| exact Hb]. apply Hk. reflexivity. Qed.

Local Opaque span_loop.
Lemma tleaf_try_avail : forall {R} sc st (k : mstate -> Z -> M R) bail (P : R -> Prop),
(forall st' v, cntm st' = cntm st -> tleaf (k st' v) P) -> tleaf bail P -> tleaf (try_avail sc st k bail) P.
Proof.
intros R sc st k bail P Hk Hb. unfold try_avail.
destruct (active st sc) as [m|]; [| apply Hk; reflexivity].
destruct (negb (m_avail (get_meta_rec st m) =? 0)); [unfold ta_fin; apply Hk; reflexivity|].
match goal with |- tleaf (match ?X with _ => _ end) _ => set (step1 := X) end.
assert (F1 : forall st1 m1, step1 = Some (st1, m1) -> cntm st1 = cntm st).
{ unfold step1. intros st1 m1 E. destruct (m_freed (get_meta_rec st m) =? 0).
- destruct (active (dequeue (LActive sc) m st) sc); inversion E; subst. apply cntm_dequeue.
- destruct (m_next (get_meta_rec st m)); inversion E; subst. reflexivity. }
destruct step1 as [[st1 m1]|].
2:{ destruct (m_freed (get_meta_rec st m) =? 0); [apply Hk; apply cntm_dequeue| apply tleaf_undef; intros _; exact Hb]. }
specialize (F1 st1 m1 eq_refl).
match goal with |- tleaf (match ?X with pair _ _ => _ end) _ => destruct X as [[st2 m2] mask0] eqn:E2 end.
assert (F2 : cntm st2 = cntm st1).
{ revert E2. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end.
- destruct (m_next (get_meta_rec st1 m1)); intros E2; injection E2 as E2a _ _; rewrite <- E2a; reflexivity.
- intros E2; injection E2 as E2a _ _; rewrite <- E2a; reflexivity. }
clear E2.
match goal with |- tleaf (match ?X with pair _ _ => _ end) _ => destruct X as [st3 m3] eqn:E3 end.
assert (F3 : cntm st3 = cntm st2).
{ revert E3. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end.
- match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end.
+ destruct (m_next (get_meta_rec st2 m2)); intros E3; injection E3 as E3a _; rewrite <- E3a; reflexivity.
+ destruct (m_mem (get_meta_rec st2 m2)); intros E3; injection E3 as E3a _; rewrite <- E3a; [apply cntm_set_group_active_idx| reflexivity].
- intros E3; injection E3 as E3a _; rewrite <- E3a; reflexivity. }
clear E3.
apply tleaf_activate_group; [| exact Hb]. intros st4 mask F4.
apply tleaf_guard; [| exact Hb]. unfold ta_fin. apply Hk. rewrite cntm_upd_meta, cntm_decay_bounces. congruence.
Qed.

Lemma small_cnt_pos : forall sc i, sc < 9 -> (i = 0 \/ i = 1 \/ i = 2) -> 1 <= small_cnt sc i.
Proof.
intros sc i Hsc Hi. unfold small_cnt. assert (Hn : (Z.to_nat sc < 9)%nat) by lia.
destruct (Z.to_nat sc) as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; try lia; destruct Hi as [->|[->| ->]]; vm_compute; intros H; discriminate H.
Qed.

Lemma small_cnt_pick_pos : forall sc u, sc < 9 -> 1 <= small_cnt_pick sc u.
Proof. intros sc u H. unfold small_cnt_pick. repeat destruct (negb _); apply small_cnt_pos; auto. Qed.

Lemma med_cnt_pos : forall sc, 1 <= med_cnt (Z.land sc 3).
Proof.
intros sc. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
pose proof (Z.mod_pos_bound sc 4 ltac:(lia)) as H. unfold med_cnt.
assert (E : sc mod 4 = 0 \/ sc mod 4 = 1 \/ sc mod 4 = 2 \/ sc mod 4 = 3) by lia.
destruct E as [->|[->|[->| ->]]]; vm_compute; intros H0; discriminate H0.
Qed.

Lemma halve_even_pos : forall f c u, 1 <= c -> 1 <= halve_even f c u.
Proof.
induction f as [|f IH]; intros c u H; cbn [halve_even]; [exact H|].
destruct (Z.even c) eqn:E; cbn [andb]; [| exact H]. destruct (u <? 4 * c); [| exact H]. apply IH.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. apply Z.even_spec in E as [q ->].
rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma halve_big_pos : forall f c sz, 1 <= c -> 0 <= sz < 65536 * UNIT -> 1 <= halve_big f c sz.
Proof.
induction f as [|f IH]; intros c sz H Hsz; cbn [halve_big]; [exact H|].
destruct (Z.leb_spec (65536 * UNIT) (sz * c)); [| exact H]. apply IH; [| exact Hsz].
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
assert (2 <= c) by (destruct (Z.eq_dec c 1) as [->|]; [rewrite Z.mul_1_r in *; lia| lia]).
apply Z.div_le_lower_bound; lia.
Qed.

Lemma tleaf_ag_tail : forall {R} st sc m p cnt ai (k : mstate -> optr -> M R) (P : R -> Prop),
(forall st' om, cntm st' = cntm st -> tleaf (k st' om) P) -> tleaf (ag_tail lay_none st sc m p cnt ai k) P.
Proof. intros R st sc m p cnt ai k P Hk. unfold ag_tail. apply Hk. reflexivity. Qed.

Lemma cntm_account_bounce : forall sc st, cntm (account_bounce sc st) = cntm st.
Proof.
intros sc st. unfold account_bounce. destruct (sc_in_seq_range sc); [| reflexivity].
destruct (_ && _); [| reflexivity]. destruct (_ <? 100); reflexivity.
Qed.

Lemma cntm_step_seq : forall st, cntm (step_seq st) = cntm st.
Proof. intros st. unfold step_seq. destruct (_ =? 255); reflexivity. Qed.

Definition lvl_ok (i sc : Z) : Prop := 0 <= i <= 7 /\ 2 ^ i <= size_class sc + 1.

Section AG.
Variable R : Type.
Variable P : R -> Prop.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Variable i : Z.
Hypothesis Hrec : forall st j req k bail, lvl_ok (i + 1) j -> 8 - (i + 1) <= cntm st ->
(forall st' v, cntm st - (8 - (i + 1)) <= cntm st' -> tleaf (k st' v) P) -> tleaf bail P -> tleaf (rec st j req k bail) P.

Lemma tleaf_alloc_group : forall st sc req (k : mstate -> optr -> M R) bail,
lvl_ok i sc -> 8 - i <= cntm st ->
(forall st' om, cntm st - (8 - i) <= cntm st' -> tleaf (k st' om) P) -> tleaf bail P ->
tleaf (alloc_group R lay_none rec st sc req k bail) P.
Proof.
intros st sc req k bail [Hi Hlv] Hc Hk Hb. unfold alloc_group.
apply tleaf_alloc_meta; [lia| | exact Hb].
intros st1 [m|] Hc1; [| apply Hk; lia].
set (size := UNIT * size_class sc).
pose proof (size_class_bound sc) as HSZ. assert (Hsize : 0 <= size <= 16 * 8191) by (unfold size, UNIT; lia).
set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st1 sc)
else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) size).
assert (Hcnt0 : 1 <= cnt0).
{ unfold cnt0. destruct (Z.ltb_spec sc 9); [apply small_cnt_pick_pos; assumption|].
apply halve_big_pos; [apply halve_even_pos, med_cnt_pos| unfold UNIT in *; lia]. }
set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0).
assert (Hcnt1 : 1 <= cnt1 /\ (cnt1 = 1 -> PGSZ / 2 < size + UNIT)).
{ unfold cnt1. destruct (Z.eqb_spec cnt0 1) as [E|E]; cbn [andb].
- rewrite E, Z.mul_1_r. destruct (Z.leb_spec (size + UNIT) (PGSZ / 2)); [split; [lia| intros; lia]| split; [lia| intros _; assumption]].
- split; [lia| intros E1; contradiction]. }
clearbody cnt1. clear Hcnt0. clearbody cnt0.
destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [Hbig|Hsmall].
-
match goal with |- tleaf (match ?Q with pair _ _ => _ end) _ => destruct Q as [cnt3 needed] end.
cbn [tleaf]. intros r.
destruct (negb _); [apply tleaf_bad_answer; exact Hb|].
destruct (is_err r); [apply tleaf_free_meta; [intros st2 E2; apply Hk; rewrite E2, cntm_step_seq, cntm_account_bounce; lia| exact Hb]|].
destruct (new_region RKGroup r needed (step_seq (account_bounce sc st1))) as [st2 rid] eqn:ENR.
assert (E2 : cntm st2 = cntm st1).
{ unfold new_region in ENR. injection ENR as <- _. change (cntm (step_seq (account_bounce sc st1)) = cntm st1). rewrite cntm_step_seq, cntm_account_bounce. reflexivity. }
apply tleaf_ag_tail. intros st' om E'. apply Hk. rewrite E'.
match goal with |- _ <= cntm ?S => assert (ES : cntm S = cntm st2) by reflexivity; rewrite ES end. rewrite E2. lia.
-
destruct Hcnt1 as [Hc1a Hc1b].
assert (Hc2 : 2 <= cnt1).
{ destruct (Z.eq_dec cnt1 1) as [E|E]; [| lia]. specialize (Hc1b E). rewrite E, Z.mul_1_r in Hsmall. lia. }
assert (Hs63 : size_class sc <= 63).
{ unfold size, UNIT, PGSZ in *. change (4096 / 2) with 2048 in Hsmall. nia. }
set (n' := UNIT + cnt1 * size - IB).
assert (Hn' : 0 <= n' < MMAP_THRESHOLD) by (unfold n', size, UNIT, IB, PGSZ, MMAP_THRESHOLD in *; change (4096 / 2) with 2048 in Hsmall; nia).
destruct (size_to_class_ok n' Hn') as [_ Hfit].
assert (Hdbl : 2 * (size_class sc + 1) <= size_class (size_to_class n') + 1).
{ unfold n', size, UNIT, IB in *. nia. }
assert (Hi6 : i <= 6).
{ destruct (Z.eq_dec i 7) as [->|]; [| lia]. change (2 ^ 7) with 128 in Hlv. lia. }
apply Hrec.
+ split; [lia|]. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
+ lia.
+ intros st2 idx Hc2'. destruct (idx <? 0); [apply tleaf_free_meta; [intros st3 E3; apply Hk; lia| exact Hb]|].
destruct (active st2 _); [| apply tleaf_undef; intros _; exact Hb].
apply tleaf_ag_tail. intros st' om E'. apply Hk. rewrite E', cntm_upd_meta. change (cntm (lh_nest lay_none st2 _ idx _ size cnt1)) with (cntm st2). lia.
+ exact Hb.
Qed.
End AG.

Lemma tleaf_alloc_slot : forall {R} (P : R -> Prop) fuel i st sc req (k : mstate -> Z -> M R) bail,
lvl_ok i sc -> 8 - i <= cntm st ->
(forall st' v, cntm st - (8 - i) <= cntm st' -> tleaf (k st' v) P) -> tleaf bail P ->
tleaf (alloc_slot lay_none fuel st sc req k bail) P.
Proof.
intros R P fuel. induction fuel as [|f IH]; intros i st sc req k bail Hl Hc Hk Hb.
- cbn [alloc_slot]. apply tleaf_undef. intros _. exact Hb.
- cbn [alloc_slot]. destruct Hl as [Hi Hlv].
apply tleaf_try_avail; [| exact Hb]. intros st1 first E1.
destruct (negb (first =? 0)); [apply Hk; lia|].
apply (tleaf_alloc_group R P (alloc_slot lay_none f) i); [| split; assumption| lia| | exact Hb].
+ intros st2 j req2 k2 bail2 Hl2 Hc2 Hk2 Hb2. apply (IH (i + 1)); assumption.
+ intros st2 [g|] Hc2; [| apply Hk; lia].
apply tleaf_queue; [| exact Hb]. intros st4 E4. apply Hk. rewrite E4, cntm_upd_meta. lia.
Qed.

Lemma lvl_ok_0 : forall sc, lvl_ok 0 sc.
Proof. intros sc. split; [lia|]. pose proof (size_class_bound sc). change (2 ^ 0) with 1. lia. Qed.

Lemma tleaf_malloc_small_ctrl : forall {R} (P : R -> Prop) st n (k : mstate -> option (aptr * Z) -> M R) bail,
8 <= cntm st ->
(forall st' r, cntm st - 8 <= cntm st' -> tleaf (k st' r) P) -> tleaf bail P ->
tleaf (malloc_small_ctrl lay_none st n k bail) P.
Proof.
intros R P st n k bail Hc Hk Hb. unfold malloc_small_ctrl.
match goal with |- tleaf (match ?g with Some _ => _ | None => _ end) _ => destruct g as [gp|] end;
[match goal with |- tleaf (if ?b then _ else _) _ => destruct b end|].
- apply Hk. rewrite cntm_upd_meta. lia.
- apply (tleaf_alloc_slot P FUEL 0); [apply lvl_ok_0| lia| | exact Hb].
intros st1 idx Hc1. destruct (idx <? 0); [apply Hk; lia|]. destruct (active st1 _); [apply Hk; rewrite ?cntm_upd_meta; lia| apply tleaf_undef; intros _; exact Hb].
- apply (tleaf_alloc_slot P FUEL 0); [apply lvl_ok_0| lia| | exact Hb].
intros st1 idx Hc1. destruct (idx <? 0); [apply Hk; lia|]. destruct (active st1 _); [apply Hk; rewrite ?cntm_upd_meta; lia| apply tleaf_undef; intros _; exact Hb].
Qed.

Theorem cmalloc_count : forall cs n,
8 <= cntm cs -> 0 <= n < MMAP_THRESHOLD ->
tleaf (cmalloc cs n) (fun r => cntm cs - 8 <= cntm (fst r)).
Proof.
intros cs n Hc Hn. unfold cmalloc.
apply (tleaf_bind _ _ (fun r => cntm cs - 8 <= cntm (fst r))); [| intros [st1 r] H; exact H].
unfold malloc_core. destruct (size_overflows n); [cbn; lia|].
assert (E : (MMAP_THRESHOLD <=? n) = false) by (apply Z.leb_gt; lia). rewrite E.
apply tleaf_malloc_small_ctrl; [exact Hc| | cbn; lia].
intros st' r Hc'. cbn [tleaf fst]. exact Hc'.
Qed.

Lemma tleaf_cpath : forall {R} (t : M R) (P : R -> Prop) L L' r, tleaf t P -> cpath L t L' r -> P r.
Proof.
intros R t P L L' r Ht Hp. induction Hp as [L0 r0|L0 e k z L1 r0 Ha Hp IH]; [exact Ht|]. apply IH. exact (Ht z).
Qed.

Corollary cmalloc_count_cpath : forall cs n L L' r,
8 <= cntm cs -> 0 <= n < MMAP_THRESHOLD -> cpath L (cmalloc cs n) L' r -> cntm cs - 8 <= cntm (fst r).
Proof. intros cs n L L' r Hc Hn Hp. exact (tleaf_cpath _ _ L L' r (cmalloc_count cs n Hc Hn) Hp). Qed.

Lemma tleaf_dec_slots : forall {R} st p (k : aptr -> Z -> M R) bail (P : R -> Prop),
(forall m idx, tleaf (k m idx) P) -> tleaf bail P -> tleaf (dec_slots st p k bail) P.
Proof. intros R st p k bail P Hk Hb. unfold dec_slots. destruct (s_slots st !! p) as [[m idx]|]; [apply Hk| apply tleaf_undef; intros _; exact Hb]. Qed.

Lemma tleaf_free_group : forall {R} (P : R -> Prop) (rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M R) -> M R -> M R),
(forall st m idx k bail, (forall st' mi, cntm st' = cntm st -> tleaf (k st' mi) P) -> tleaf bail P -> tleaf (rec st m idx k bail) P) ->
forall st g (k : mstate -> mapinfo -> M R) bail,
(forall st' mi, cntm st' = cntm st -> tleaf (k st' mi) P) -> tleaf bail P -> tleaf (free_group R dec_slots rec st g k bail) P.
Proof.
intros R P rec Hrec st g k bail Hk Hb. unfold free_group.
destruct (m_mem (get_meta_rec st g)) as [p|]; [| apply tleaf_undef; intros _; exact Hb].
set (st1 := del_slots p _ _ (del_group p _)).
assert (E1 : cntm st1 = cntm st) by (unfold st1; destruct (m_sizeclass (get_meta_rec st g) <? 48); reflexivity).
destruct (negb (m_maplen (get_meta_rec st g) =? 0)).
- apply tleaf_free_meta; [| exact Hb]. intros st3 E3. apply Hk. rewrite E3.
match goal with |- cntm ?S = _ => assert (ES : cntm S = cntm (step_seq st1)) by (unfold record_seq; destruct (sc_in_seq_range _); reflexivity); rewrite ES end.
rewrite cntm_step_seq. exact E1.
- apply tleaf_dec_slots; [| exact Hb]. intros m idx. apply Hrec; [| exact Hb].
intros st3 mi E3. apply tleaf_free_meta; [| exact Hb]. intros st4 E4. apply Hk. congruence.
Qed.

Lemma tleaf_nontrivial_free : forall {R} (P : R -> Prop) fuel st g i (k : mstate -> mapinfo -> M R) bail,
(forall st' mi, cntm st' = cntm st -> tleaf (k st' mi) P) -> tleaf bail P -> tleaf (nontrivial_free dec_slots fuel st g i k bail) P.
Proof.
intros R P fuel. induction fuel as [|f IH]; intros st g i k bail Hk Hb; cbn [nontrivial_free].
- apply tleaf_undef. intros _. exact Hb.
- assert (FG : forall st0, cntm st0 = cntm st -> tleaf (free_group R dec_slots (nontrivial_free dec_slots f) st0 g k bail) P).
{ intros st0 E0. apply tleaf_free_group; [| | exact Hb].
- intros st1 m idx k1 bail1 Hk1 Hb1. apply IH; assumption.
- intros st' mi E'. apply Hk. congruence. }
destruct (_ && okay_to_free st g).
+ destruct (m_next (get_meta_rec st g)); [| apply FG; reflexivity].
apply tleaf_guard; [| exact Hb].
destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)); [| apply FG; apply cntm_dequeue].
destruct (active (dequeue _ g st) _); [| apply FG; apply cntm_dequeue].
apply tleaf_activate_group; [| exact Hb]. intros st2 v E2. apply FG. rewrite E2. apply cntm_dequeue.
+ destruct (_ =? 0); [| apply Hk; apply cntm_upd_meta].
apply tleaf_guard; [| exact Hb].
destruct (negb _); [apply tleaf_queue; [intros st' E'; apply Hk; rewrite cntm_upd_meta; exact E'| exact Hb]| apply Hk; apply cntm_upd_meta].
Qed.

Theorem cfree_count : forall cs p, tleaf (cfree cs p) (fun r => cntm r = cntm cs).
Proof.
intros cs [s|]; cbn [cfree]; [| reflexivity].
destruct (s_slots cs !! s) as [[g idx]|]; [| apply tleaf_undef; intros _; reflexivity].
apply (tleaf_bind _ _ (fun r => cntm r = cntm cs)); [| intros st1 H; exact H].
unfold free_tail. apply tleaf_guard; [| reflexivity].
destruct (negb _); [cbn [tleaf]; apply cntm_upd_meta|].
apply tleaf_nontrivial_free; [| reflexivity].
intros st2 [[base len]|] E2; [| exact E2].
destruct (negb (len =? 0)); [| exact E2].
cbn [tleaf]. intros ru. destruct (munmap_answer_ok ru); [| apply tleaf_bad_answer; reflexivity].
cbn [tleaf]. rewrite <- E2. reflexivity.
Qed.

Corollary cfree_count_cpath : forall cs p L L' r, cpath L (cfree cs p) L' r -> cntm r = cntm cs.
Proof. intros cs p L L' r Hp. exact (tleaf_cpath _ _ L L' r (cfree_count cs p) Hp). Qed.

End RC__1.
