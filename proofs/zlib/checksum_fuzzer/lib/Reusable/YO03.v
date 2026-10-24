(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK15 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e YO05 YO02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition GT {A} (P : A -> Prop) (t : itree astate A) : Prop := gtree mgrant t /\ leaves P t.
Lemma GT_ibind {A B} (P : A -> Prop) (Q : B -> Prop) t (f : A -> itree astate B) :
GT P t -> (forall a, P a -> GT Q (f a)) -> GT Q (ibind t f).
Proof.
intros [Hg Hl] Hf. split.
- apply gtree_ibind; [exact Hg|]. intros tr a Hp. apply (proj1 (Hf a (leaves_cpath _ _ _ _ Hl Hp))).
- eapply leaves_ibind; [exact Hl|]. intros a Ha. apply (proj2 (Hf a Ha)).
Qed.
Lemma GT_bind {A B} (P : A * astate -> Prop) (Q : B * astate -> Prop) (m : M A) (f : A -> M B) s :
GT P (m s) -> (forall a s', P (a, s') -> GT Q (f a s')) -> GT Q (bind m f s).
Proof. intros Hm Hf. unfold bind. eapply GT_ibind; [exact Hm|]. intros [a s'] H. apply Hf, H. Qed.
Lemma GT_mono {A} (P Q : A -> Prop) t : (forall a, P a -> Q a) -> GT P t -> GT Q t.
Proof. intros H [Hg Hl]. split; [exact Hg | eapply leaves_mono; eauto]. Qed.
Lemma GT_ret {A} (a : A) s (Q : A * astate -> Prop) : Q (a, s) -> GT Q (ret a s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma GT_IRet {A} (a : A) (Q : A -> Prop) : Q a -> GT Q (IRet a).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma GT_fail {A} f s (Q : A * astate -> Prop) : GT Q (fail f s).
Proof. split; exact I. Qed.
Lemma GT_get s (Q : astate * astate -> Prop) : Q (s, s) -> GT Q (get s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma GT_put s s' (Q : unit * astate -> Prop) : Q (tt, s') -> GT Q (put s' s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma GT_modify f s (Q : unit * astate -> Prop) : Q (tt, f s) -> GT Q (modify f s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma GT_massert b x s (Q : unit * astate -> Prop) : Q (tt, s) -> GT Q (massert b x s).
Proof. intros H. unfold massert. destruct b; [apply GT_ret, H | apply GT_fail]. Qed.
Lemma GT_mcheck b x s (Q : unit * astate -> Prop) : Q (tt, s) -> GT Q (mcheck b x s).
Proof. intros H. unfold mcheck. destruct b; [apply GT_ret, H | apply GT_fail]. Qed.
Lemma GT_ask q s (Q : bool * astate -> Prop) :
(fallible q = true -> mgrant s q) -> (forall p, q <> KJunk p) -> (forall b, Q (b, s)) -> GT Q (ask q s).
Proof.
intros Hg Hj HQ. split.
- unfold ask. destruct q; cbn; try (intros; exact I); try (split; [apply Hg; reflexivity | split; exact I]).
- cbn. intros z _. apply HQ.
Qed.
Lemma GT_askz_junk p s (Q : Z * astate -> Prop) : (forall z, 0 <= z < 256 -> Q (z, s)) -> GT Q (askz (KJunk p) s).
Proof. intros HQ. split; [cbn; intros; exact I | cbn; intros z Hz; apply HQ, Hz]. Qed.
Lemma GT_if {A} (c : bool) (m1 m2 : M A) s Q : GT Q (m1 s) -> GT Q (m2 s) -> GT Q ((if c then m1 else m2) s).
Proof. destruct c; auto. Qed.
Lemma GT_gtree {A} P (t : itree astate A) : GT P t -> gtree mgrant t. Proof. intros [H _]; exact H. Qed.
Definition KEEP (s : astate) {A} (r : A * astate) : Prop :=
st_regions (snd r) = st_regions s /\ st_avail_meta_count (snd r) = st_avail_meta_count s.
Definition presK {A} (m : M A) : Prop := forall s, GT (KEEP s) (m s).
Lemma KEEP_refl s {A} (a : A) : KEEP s (a, s). Proof. split; reflexivity. Qed.
Lemma KEEP_trans s s1 {A B} (a : A) (b : B) s2 : KEEP s (a, s1) -> KEEP s1 (b, s2) -> KEEP s (b, s2).
Proof. unfold KEEP; cbn. intros [H1 H2] [H3 H4]. rewrite H3, H4, H1, H2. split; reflexivity. Qed.
Lemma presK_bind {A B} (m : M A) (k : A -> M B) : presK m -> (forall a, presK (k a)) -> presK (bind m k).
Proof.
intros Hm Hk s. eapply GT_bind; [apply Hm|]. intros a s' HK. eapply GT_mono; [|apply Hk].
intros [b s2] H2. eapply KEEP_trans; eauto.
Qed.
Lemma presK_bind_get {B} (k : astate -> M B) : (forall s, GT (KEEP s) (k s s)) -> presK (bind get k).
Proof. intros Hk s. unfold bind, get. cbn. apply Hk. Qed.
Lemma presK_ret {A} (a : A) : presK (ret a). Proof. intros s. apply GT_ret. apply KEEP_refl. Qed.
Lemma presK_get : presK get. Proof. intros s. apply GT_get. apply KEEP_refl. Qed.
Lemma presK_fail {A} f : presK (@fail A f). Proof. intros s. apply GT_fail. Qed.
Lemma presK_massert b x : presK (massert b x). Proof. intros s. apply GT_massert. apply KEEP_refl. Qed.
Lemma presK_mcheck b x : presK (mcheck b x). Proof. intros s. apply GT_mcheck. apply KEEP_refl. Qed.
Lemma presK_modify f : (forall s, st_regions (f s) = st_regions s /\ st_avail_meta_count (f s) = st_avail_meta_count s) -> presK (modify f).
Proof. intros Hf s. apply GT_modify. unfold KEEP. cbn [snd]. apply Hf. Qed.
Lemma presK_askz_junk p : presK (askz (KJunk p)). Proof. intros s. apply GT_askz_junk. intros; apply KEEP_refl. Qed.
Lemma GT_KEEP_presK {A} (m : M A) s : presK m -> GT (KEEP s) (m s). Proof. intros H; apply H. Qed.
Lemma GT_put_KEEP s s1 : st_regions s1 = st_regions s -> st_avail_meta_count s1 = st_avail_meta_count s -> GT (KEEP s) (put s1 s).
Proof. intros H1 H2. apply GT_put. split; assumption. Qed.
End e.
Ltac keep_setter := intros ?; cbn; split; reflexivity.
Create HintDb presK.
Ltac kstep :=
lazymatch goal with
| |- presK (bind get _) => apply presK_bind_get; intros ?
| |- presK (bind _ _) => apply presK_bind; [ | intros ? ]
| |- presK (ret _) => apply presK_ret
| |- presK get => apply presK_get
| |- presK (fail _) => apply presK_fail
| |- presK (massert _ _) => apply presK_massert
| |- presK (mcheck _ _) => apply presK_mcheck
| |- presK (askz (KJunk _)) => apply presK_askz_junk
| |- presK (modify _) => apply presK_modify; [ keep_setter ]
| |- presK (match ?x with _ => _ end) => destruct x
| |- presK (if ?x then _ else _) => destruct x
| |- presK _ => solve [auto with presK]
| |- KEEP _ _ => split; cbn; reflexivity
| |- GT _ (IRet _) => apply GT_IRet
| |- GT (KEEP _) (match ?x with _ => _ end _) => destruct x
| |- GT (KEEP _) ((if ?b then _ else _) _) => destruct b
| |- GT (KEEP _) (put _ _) => apply GT_put_KEEP; [cbn; reflexivity | cbn; reflexivity]
| |- GT ?P (bind (put ?s1) ?k ?s0) => change (GT P (k tt s1))
| |- GT ?P (bind get ?k ?s0) => change (GT P (k s0 s0))
| |- GT ?P (bind (modify ?f) ?k ?s0) => change (GT P (k tt (f s0)))
| |- GT (KEEP ?s0) (?m ?s) =>
tryif constr_eq s0 s then (apply (GT_KEEP_presK m s))
else (eapply GT_mono; [ | apply (GT_KEEP_presK m s) ];
[ intros [? ?] ?; eapply KEEP_trans; [ | eassumption]; split; cbn; reflexivity | ])
end.
Ltac kgo := repeat kstep.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_getm p : presK (getm p). Proof. unfold getm. kgo. Qed.
End j.
#[export] Hint Resolve k_getm : presK.
Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_setm p am : presK (setm p am). Proof. unfold setm. kgo. Qed.
End o.
#[export] Hint Resolve k_setm : presK.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_setslot p x : presK (setslot p x). Proof. unfold setslot. kgo. Qed.
End w.
#[export] Hint Resolve k_setslot : presK.
Section y. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_get_links p : presK (get_links p). Proof. unfold get_links. kgo. Qed.
End y.
#[export] Hint Resolve k_get_links : presK.
Section a0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_set_links p a b : presK (set_links p a b). Proof. unfold set_links. kgo. Qed.
End a0.
#[export] Hint Resolve k_set_links : presK.
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_set_prev p a : presK (set_prev p a). Proof. unfold set_prev. kgo. Qed.
End b0.
#[export] Hint Resolve k_set_prev : presK.
Section c0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_set_next p a : presK (set_next p a). Proof. unfold set_next. kgo. Qed.
End c0.
#[export] Hint Resolve k_set_next : presK.
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_get_head h : presK (get_head h). Proof. unfold get_head. kgo. Qed.
End d0.
#[export] Hint Resolve k_get_head : presK.
Section e0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_set_head h v : presK (set_head h v). Proof. unfold set_head. destruct h; kgo. Qed.
End e0.
#[export] Hint Resolve k_set_head : presK.
Section f0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_queue h m : presK (queue h m). Proof. unfold queue. kgo. Qed.
End f0.
#[export] Hint Resolve k_queue : presK.
Section g0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_dequeue h m : presK (dequeue h m). Proof. unfold dequeue. kgo. Qed.
End g0.
#[export] Hint Resolve k_dequeue : presK.
Section h0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_dequeue_head h : presK (dequeue_head h). Proof. unfold dequeue_head. kgo. Qed.
End h0.
#[export] Hint Resolve k_dequeue_head : presK.
Section i0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_free_meta m : presK (free_meta m). Proof. unfold free_meta. kgo. Qed.
End i0.
#[export] Hint Resolve k_free_meta : presK.
Section j0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_set_usage_of sc v : presK (set_usage_of sc v). Proof. unfold set_usage_of. kgo. Qed.
End j0.
#[export] Hint Resolve k_set_usage_of : presK.
Section k0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_step_seq : presK step_seq.
Proof. unfold step_seq. apply presK_modify. intros s. destruct (st_seq s =? 255); cbn; split; reflexivity. Qed.
End k0.
#[export] Hint Resolve k_step_seq : presK.
Section l0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_record_seq sc : presK (record_seq sc). Proof. unfold record_seq. kgo. Qed.
End l0.
#[export] Hint Resolve k_record_seq : presK.
Section m0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_account_bounce sc : presK (account_bounce sc).
Proof. unfold account_bounce. destruct (bounce_idx sc); [|kgo]. apply presK_modify. intros s. cbn zeta.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; split; reflexivity. Qed.
End m0.
#[export] Hint Resolve k_account_bounce : presK.
Section n0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_decay_bounces sc : presK (decay_bounces sc).
Proof. unfold decay_bounces. destruct (bounce_idx sc); [|kgo]. apply presK_modify. intros s. cbn zeta.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; split; reflexivity. Qed.
End n0.
#[export] Hint Resolve k_decay_bounces : presK.
Section o0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_activate_group m : presK (activate_group m). Proof. unfold activate_group. kgo. Qed.
End o0.
#[export] Hint Resolve k_activate_group : presK.
Section p0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_try_avail sc : presK (try_avail sc). Proof. unfold try_avail. kgo. Qed.
End p0.
#[export] Hint Resolve k_try_avail : presK.
Section q0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_enframe g idx n ctr k : presK (enframe g idx n ctr k). Proof. unfold enframe. kgo. Qed.
End q0.
#[export] Hint Resolve k_enframe : presK.
Section r0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_install_group m sc cnt aidx maplen mem sl : presK (install_group m sc cnt aidx maplen mem sl).
Proof. unfold install_group. kgo. Qed.
End r0.
#[export] Hint Resolve k_install_group : presK.
Section t0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_find_frame p : presK (find_frame p). Proof. unfold find_frame. kgo. Qed.
End t0.
#[export] Hint Resolve k_find_frame : presK.
Section u0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_forget_frame g i : presK (forget_frame g i). Proof. unfold forget_frame. kgo. Qed.
End u0.
#[export] Hint Resolve k_forget_frame : presK.
Section v0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma k_release_slot g i : presK (release_slot g i). Proof. unfold release_slot. kgo. Qed.
End v0.
#[export] Hint Resolve k_release_slot : presK.
Notation amc s := (st_avail_meta_count s).
Section w0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma GT_keep_budget {A} (m : M A) s :
presK m -> GT (fun r : A * astate => live_bytes (snd r) = live_bytes s /\ nslots (snd r) = nslots s /\ amc (snd r) = amc s) (m s).
Proof.
intros H. eapply GT_mono; [|apply H]. intros [a s'] [Hr Hc]; cbn in *.
unfold live_bytes, nslots. rewrite Hr, Hc. repeat split; reflexivity.
Qed.
Lemma live_bytes_app_live rs k len :
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 (rs ++ [mkRegion k len [] true])
= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 rs + len.
Proof. induction rs as [|r rs IH]; cbn; [lia|]. rewrite IH. destruct (rg_live r); lia. Qed.
Lemma nslots_app_map rs len :
fold_right (fun rg acc => region_slots rg + acc) 0 (rs ++ [mkRegion RkMap len [] true])
= fold_right (fun rg acc => region_slots rg + acc) 0 rs + 1.
Proof. induction rs as [|r rs IH]; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma GT_new_region_map len s (Q : nat * astate -> Prop) :
(forall s', live_bytes s' = live_bytes s + len -> nslots s' = nslots s + 1 -> amc s' = amc s -> Q (length (st_regions s), s')) ->
GT Q (new_region RkMap len s).
Proof.
intros HQ. unfold new_region, bind, get, put, ret. cbn. split; [exact I|]. cbn.
apply HQ; cbn; [apply live_bytes_app_live | apply nslots_app_map | reflexivity].
Qed.
Lemma GT_alloc_meta s :
0 < amc s ->
GT (fun r : option sptr * astate => live_bytes (snd r) = live_bytes s /\ nslots (snd r) = nslots s /\ amc s - 1 <= amc (snd r)) (alloc_meta s).
Proof.
intros Hc. unfold alloc_meta.
change (GT ?Q (bind (modify (set_init_done true)) ?k s)) with (GT Q (k tt (set_init_done true s))). cbv beta.
eapply GT_bind; [apply (GT_keep_budget _ (set_init_done true s)); auto with presK|].
intros fm s1 (L1 & N1 & C1). cbn in L1, N1, C1 |- *.
destruct fm as [m|].
- apply GT_ret. cbn. unfold live_bytes, nslots in *. cbn in *. lia.
- change (GT ?Q (bind get ?k s1)) with (GT Q (k s1 s1)). cbv beta.
assert (E : (0 <? amc s1) = true) by (apply Z.ltb_lt; unfold live_bytes in *; cbn in *; lia).
rewrite E. rewrite bind_ret_l. cbn [negb].
change (GT ?Q (bind get ?k s1)) with (GT Q (k s1 s1)). cbv beta.
match goal with |- GT ?Q (bind (put ?s2) ?k ?s0) => change (GT Q (k tt s2)) end. cbv beta.
eapply GT_bind; [apply GT_keep_budget; auto with presK|].
intros [] s3 (L3 & N3 & C3). apply GT_ret. cbn in *. unfold live_bytes, nslots in *. cbn in *. lia.
Qed.
Lemma nth_bound (l : list Z) lo hi d k : lo <= d <= hi -> Forall (fun x => lo <= x <= hi) l -> lo <= nth k l d <= hi.
Proof. intros Hd HF. destruct (nth_in_or_default k l d) as [H| ->]; [|lia]. rewrite Forall_forall in HF. apply HF, H. Qed.
Lemma class_size_bound sc : 0 <= class_size sc <= 131056.
Proof.
unfold class_size, znth, UNIT.
assert (H : 0 <= nth (Z.to_nat sc) size_classes 0 <= 8191).
{ apply nth_bound; [lia|]. unfold size_classes. repeat constructor; lia. }
lia.
Qed.
Lemma small_cnt_tab_rows k : Forall (fun x => 0 <= x <= 31) (nth k small_cnt_tab []).
Proof. unfold small_cnt_tab. do 9 (destruct k as [|k]; [cbn; repeat constructor; lia|]). destruct k; constructor. Qed.
Lemma small_cnt_bound sc u : 0 <= small_cnt sc u <= 31.
Proof.
unfold small_cnt. pose proof (small_cnt_tab_rows (Z.to_nat sc)) as HR.
unfold znth. repeat match goal with |- context [if ?b then _ else _] => destruct b end.
all: apply nth_bound; auto; lia.
Qed.
Lemma halve_even_bound f c u : 0 <= c -> 0 <= halve_while_even f c u <= c.
Proof. revert c. induction f as [|f IH]; intros c Hc; cbn; [lia|]. destruct (Z.even c && (u <? 4 * c)); [|lia].
specialize (IH (c/2)). assert (0 <= c / 2 <= c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. Qed.
Lemma halve_big_bound f c sz : 0 <= c -> 0 <= halve_while_big f c sz <= c.
Proof. revert c. induction f as [|f IH]; intros c Hc; cbn; [lia|]. destruct (65536 * UNIT <=? sz * c); [|lia].
specialize (IH (c/2)). assert (0 <= c / 2 <= c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. Qed.
Lemma initial_cnt_bound sc u : 0 <= initial_cnt sc u <= 32.
Proof.
unfold initial_cnt.
assert (Hm : 0 <= znth (Z.land sc 3) med_cnt_tab <= 32).
{ unfold znth. apply nth_bound; [lia|]. unfold med_cnt_tab. repeat constructor; lia. }
pose proof (small_cnt_bound sc u).
pose proof (halve_even_bound 8 (znth (Z.land sc 3) med_cnt_tab) u ltac:(lia)).
pose proof (halve_big_bound 8 (halve_while_even 8 (znth (Z.land sc 3) med_cnt_tab) u) (class_size sc) ltac:(lia)).
repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.
Lemma page_round_bounds x : 0 <= x -> x <= page_round x <= x + 4095.
Proof. intros Hx. unfold page_round, PGSZ. split; [|].
- pose proof (Z.mul_succ_div_gt (x + 4096 - 1) 4096 ltac:(lia)). pose proof (Z_div_mod_eq_full (x+4096-1) 4096). nia.
- pose proof (Z.mul_div_le (x + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.
Lemma page_round_pos x : 0 < x -> 0 < page_round x.
Proof. intros. pose proof (page_round_bounds x ltac:(lia)). lia. Qed.
Definition MMAX : Z := 2 ^ 23.
Lemma mmap_plan_len_bound s sc req cnt0 u :
0 <= req < 2 ^ 17 -> 0 <= cnt0 <= 32 ->
0 < snd (mmap_plan s sc req cnt0 u) /\ page_round (snd (mmap_plan s sc req cnt0 u)) <= MMAX.
Proof.
intros Hr Hc. unfold mmap_plan, MMAX, UNIT, IB, PGSZ. pose proof (class_size_bound sc) as Hs.
assert (G : forall cnt, 0 <= cnt <= 32 -> 0 < page_round (class_size sc * cnt + 16) /\ page_round (page_round (class_size sc * cnt + 16)) <= 2 ^ 23).
{ intros cnt Hcnt. pose proof (page_round_bounds (class_size sc * cnt + 16) ltac:(nia)) as P1.
pose proof (page_round_bounds (page_round (class_size sc * cnt + 16)) ltac:(nia)) as P2. nia. }
assert (R : 0 < page_round (req + 4 + 16) /\ page_round (page_round (req + 4 + 16)) <= 2 ^ 23).
{ pose proof (page_round_bounds (req + 4 + 16) ltac:(lia)) as P1.
pose proof (page_round_bounds (page_round (req + 4 + 16)) ltac:(lia)) as P2. lia. }
repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [fst snd]; first [apply R | apply G; lia].
Qed.
Definition BUD (s0 : astate) (k : Z) {A} (r : A * astate) : Prop :=
live_bytes (snd r) <= live_bytes s0 + MMAX /\ nslots (snd r) <= nslots s0 + 1 /\ amc s0 - k <= amc (snd r).
Lemma KEEP_BUD s0 k s1 {A B} (a : A) (r : B * astate) :
BUD s0 k (a, s1) -> KEEP s1 r -> BUD s0 k r.
Proof. unfold BUD, KEEP, live_bytes, nslots. destruct r as [b s2]; cbn. intros (H1 & H2 & H3) [-> ->]. auto. Qed.
Lemma GT_presK_BUD {A} (m : M A) s0 k s1 {B} (b : B) :
presK m -> BUD s0 k (b, s1) -> GT (BUD s0 k) (m s1).
Proof. intros Hm HB. eapply GT_mono; [|apply Hm]. intros r Hr. eapply KEEP_BUD; eauto. Qed.
End w0.
Local Open Scope mm_scope.
Section x0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma alloc_slot_S f sc req :
alloc_slot (S f) sc req =
(first <- try_avail sc ;;
if negb (first =? 0) then ret (ctz32 first)
else og <- alloc_group f sc req ;;
match og with None => ret (-1) | Some g => ret 0 end).
Proof. reflexivity. Qed.
Lemma BUD_of_KEEP s0 k {A} (r : A * astate) : 0 <= k -> KEEP s0 r -> BUD s0 k r.
Proof. unfold BUD, KEEP, live_bytes, nslots, MMAX. intros Hk [-> ->]. lia. Qed.
Definition PRE (fuel : nat) (s0 : astate) : Prop :=
Z.of_nat fuel <= amc s0 /\ live_bytes s0 + MMAX <= MG_LIVE /\ nslots s0 + 1 <= MG_SLOTS.
Definition SAME (s0 : astate) (d : Z) (s : astate) : Prop :=
live_bytes s = live_bytes s0 /\ nslots s = nslots s0 /\ amc s0 - d <= amc s.
Lemma SAME_KEEP s0 d s {A} (r : A * astate) : SAME s0 d s -> KEEP s r -> SAME s0 d (snd r).
Proof. unfold SAME, KEEP, live_bytes, nslots. intros (A1 & A2 & A3) [R C]. rewrite R, C. auto. Qed.
Lemma GT_SAME_presK {A} (m : M A) s0 d s : presK m -> SAME s0 d s -> GT (fun r => SAME s0 d (snd r)) (m s).
Proof. intros Hm HS. eapply GT_mono; [|apply Hm]. intros r Hr. eapply SAME_KEEP; eauto. Qed.
Lemma BUD_of_SAME s0 d k s {A} (a : A) : SAME s0 d s -> d <= k -> BUD s0 k (a, s).
Proof. unfold SAME, BUD, MMAX. cbn. lia. Qed.
Lemma GT_BUD_presK {A} (m : M A) s0 k s : presK m -> BUD s0 k (tt, s) -> GT (BUD s0 k) (m s).
Proof. intros Hm HB. eapply GT_mono; [|apply Hm]. intros [a s'] [R C]. unfold BUD, live_bytes, nslots in *. cbn in *. rewrite R, C. exact HB. Qed.
Lemma GT_bind_new_region_map {B} len s (k : nat -> M B) Q :
GT Q (k (length (st_regions s)) (set_regions (st_regions s ++ [mkRegion RkMap len [] true]) s)) ->
GT Q (bind (new_region RkMap len) k s).
Proof. intros H. exact H. Qed.
Lemma live_bytes_add_map s len : live_bytes (set_regions (st_regions s ++ [mkRegion RkMap len [] true]) s) = live_bytes s + len.
Proof. unfold live_bytes. cbn. apply live_bytes_app_live. Qed.
Lemma nslots_add_map s len : nslots (set_regions (st_regions s ++ [mkRegion RkMap len [] true]) s) = nslots s + 1.
Proof. unfold nslots. cbn. apply nslots_app_map. Qed.
Lemma amc_set_regions s v : amc (set_regions v s) = amc s. Proof. reflexivity. Qed.
End x0.
#[export] Hint Resolve presK_ret presK_get presK_fail presK_massert presK_mcheck presK_askz_junk : presK.
Section y0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma BUD_shift s0 s1 k {A} (r : A * astate) :
SAME s0 1 s1 -> BUD s1 k r -> BUD s0 (k + 1) r.
Proof. unfold SAME, BUD. intros (H1 & H2 & H3) (B1 & B2 & B3). rewrite H1 in B1. rewrite H2 in B2. lia. Qed.
Lemma BUD_any s0 k s {A B} (a : A) (b : B) : BUD s0 k (a, s) -> BUD s0 k (b, s).
Proof. intros H; exact H. Qed.
End y0.
Ltac bstep :=
lazymatch goal with
| |- GT (BUD ?s0 ?k) (bind get ?c ?s) => change (GT (BUD s0 k) (c s s)); cbv beta
| |- GT (BUD ?s0 ?k) (bind (put ?s') ?c ?s) => change (GT (BUD s0 k) (c tt s')); cbv beta
| |- GT (BUD ?s0 ?k) (bind _ _ _) =>
eapply (GT_bind (BUD s0 k)); [apply GT_BUD_presK; [auto with presK | eapply BUD_any; eassumption] | intros ? ? ?]
| |- GT (BUD ?s0 ?k) (ret _ _) => apply GT_ret; eapply BUD_any; eassumption
| |- GT _ (fail _ _) => apply GT_fail
| |- GT _ ((match ?x with _ => _ end) _) => destruct x
| |- GT _ ((if ?x then _ else _) _) => destruct x
end.
Section z0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma GT_alloc_both : forall fuel,
(forall sc req s0, PRE fuel s0 -> 0 <= req < 2^17 -> GT (BUD s0 (Z.of_nat fuel)) (alloc_slot fuel sc req s0))
/\ (forall sc req s0, PRE fuel s0 -> 0 <= req < 2^17 -> GT (BUD s0 (Z.of_nat fuel)) (alloc_group fuel sc req s0)).
Proof.
induction fuel as [|f [IHs IHg]].
- split; intros sc req s0 HP Hr; cbn; apply GT_fail.
- split; intros sc req s0 (P1 & P2 & P3) Hr.
+ rewrite alloc_slot_S.
eapply GT_bind; [apply (GT_KEEP_presK _ s0); auto with presK|].
intros first s1 K1. apply GT_if.
* apply GT_ret. apply BUD_of_KEEP; [lia|exact K1].
* destruct K1 as [R1 C1]; cbn in R1, C1. eapply GT_bind.
{ apply IHg; [|exact Hr]. unfold PRE, live_bytes, nslots in *. rewrite R1, C1. lia. }
intros og s2 B2. destruct og; apply GT_ret; unfold BUD, live_bytes, nslots in *; cbn in *; rewrite <- R1, <- C1; lia.
+ cbn [alloc_group].
eapply GT_bind.
{ eapply GT_mono; [|apply GT_alloc_meta; lia]. intros r Hr'. exact Hr'. }
intros om s1 S1. cbn [fst snd] in S1.
assert (HS1 : SAME s0 1 s1) by (unfold SAME; lia). clear S1.
destruct om as [m|]; [|apply GT_ret; eapply BUD_of_SAME; [exact HS1|lia]].
change (GT ?Q (bind get ?k s1)) with (GT Q (k s1 s1)); cbv beta.
pose proof (initial_cnt_bound sc (usage_of s1 sc)) as Hcnt.
set (cnt0 := initial_cnt sc (usage_of s1 sc)) in *.
destruct (PGSZ / 2 <? class_size sc * cnt0 + UNIT) eqn:Enest.
*
pose proof (mmap_plan_len_bound s1 sc req cnt0 (usage_of s1 sc) Hr Hcnt) as Hlen.
set (plan := mmap_plan s1 sc req cnt0 (usage_of s1 sc)) in *.
eapply GT_bind; [apply (GT_SAME_presK _ s0 1 s1); auto with presK|]. intros [] s2 HS2.
eapply GT_bind; [apply (GT_SAME_presK _ s0 1 s2); auto with presK|]. intros [] s3 HS3.
eapply (GT_bind (fun r => SAME s0 1 (snd r))).
{ apply GT_ask; [ | intros; discriminate | intros b; exact HS3 ].
intros _. cbn [mgrant req_len]. unfold MG_REQ, MMAX in *. unfold SAME in HS3. cbn [snd] in HS3. pose proof (page_round_pos _ (proj1 Hlen)). lia. }
intros ok s4 HS4. cbn [snd] in HS4. apply GT_if.
{ eapply GT_bind; [apply (GT_SAME_presK _ s0 1 s4); auto with presK|]. intros [] s5 HS5. apply GT_ret. eapply BUD_of_SAME; [exact HS5|lia]. }
apply GT_bind_new_region_map.
pose proof (live_bytes_add_map s4 (page_round (snd plan))) as L5.
pose proof (nslots_add_map s4 (page_round (snd plan))) as N5.
pose proof (amc_set_regions s4 (st_regions s4 ++ [mkRegion RkMap (page_round (snd plan)) [] true])) as C5.
set (s5 := set_regions _ s4) in *.
change (GT ?Q (bind get ?k s5)) with (GT Q (k s5 s5)); cbv beta.
match goal with |- GT ?Q (bind (put ?s') ?k ?s) => change (GT Q (k tt s')) end. cbv beta.
eapply (GT_bind (BUD s0 (Z.of_nat (S f)))); [apply GT_BUD_presK; [auto with presK|] |].
{ unfold BUD, SAME in *. cbn [snd] in *. unfold live_bytes, nslots in *. cbn -[s5]. cbn -[s5] in L5, N5, C5. lia. }
intros [] s6 B6. apply GT_ret. exact B6.
*
pose proof (class_size_bound sc) as Hsz.
assert (Htot : 0 <= UNIT + cnt0 * class_size sc - IB < 2 ^ 17).
{ apply Z.ltb_ge in Enest. unfold UNIT, IB, PGSZ in *. nia. }
eapply (GT_bind (BUD s1 (Z.of_nat f))).
{ apply IHs; [|exact Htot]. unfold PRE, SAME in *. lia. }
intros idx s7 B7.
apply (BUD_shift s0 s1) in B7; [|exact HS1].
replace (Z.of_nat f + 1) with (Z.of_nat (S f)) in B7 by lia.
repeat bstep.
Qed.
Lemma GT_alloc_slot fuel sc req s0 :
PRE fuel s0 -> 0 <= req < 2^17 -> GT (BUD s0 (Z.of_nat fuel)) (alloc_slot fuel sc req s0).
Proof. apply (proj1 (GT_alloc_both fuel)). Qed.
Definition TT {A} (r : A) : Prop := True.
Lemma GT_TT_presK {A} (m : M A) s : presK m -> GT TT (m s).
Proof. intros Hm. eapply GT_mono; [|apply Hm]. intros; exact I. Qed.
Lemma GT_TT_any {A} (t : itree astate A) P : GT P t -> GT TT t.
Proof. apply GT_mono. intros; exact I. Qed.
End z0.
Ltac tstep :=
lazymatch goal with
| |- GT ?Q (bind get ?c ?s) => change (GT Q (c s s)); cbv beta
| |- GT ?Q (bind (put ?s') ?c ?s) => change (GT Q (c tt s')); cbv beta
| |- GT ?Q (bind (modify ?f) ?c ?s) => change (GT Q (c tt (f s))); cbv beta
| |- GT TT (bind _ _ _) => eapply (GT_bind TT); [first [apply GT_TT_presK; solve [auto with presK] | idtac] | intros ? ? _]
| |- GT TT (ret _ _) => apply GT_ret; exact I
| |- GT _ (fail _ _) => apply GT_fail
| |- GT _ ((match ?x with _ => _ end) _) => destruct x
| |- GT _ ((if ?x then _ else _) _) => destruct x
| |- GT TT (ask _ _) => apply GT_ask; [ first [intros; discriminate | cbn; intros; exact I | idtac] | intros; discriminate | intros; exact I]
| |- GT TT (upd_region _ _ _) => unfold upd_region; apply GT_modify; exact I
| |- GT TT (modify _ _) => apply GT_modify; exact I
| |- GT TT (?m ?s) => apply GT_TT_presK; solve [auto with presK]
end.
Section a1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma PRE_KEEP fuel s0 {A} (r : A * astate) : PRE fuel s0 -> KEEP s0 r -> PRE fuel (snd r).
Proof. unfold PRE, KEEP, live_bytes, nslots. intros (P1 & P2 & P3) [R C]. rewrite R, C. auto. Qed.
Lemma GT_malloc n s0 :
0 <= n < 2 ^ 26 -> 64 <= amc s0 -> live_bytes s0 + 2 ^ 27 <= MG_LIVE -> nslots s0 + 1 <= MG_SLOTS -> GT TT (malloc n s0).
Proof.
intros Hn HA HL HN. unfold malloc.
destruct (size_overflows n) eqn:Eo.
{ unfold size_overflows in Eo. apply Z.leb_le in Eo. lia. }
destruct (MMAP_THRESHOLD <=? n) eqn:Em.
-
eapply (GT_bind (fun r => snd r = s0)).
{ apply GT_ask; [ | intros; discriminate | intros; reflexivity ].
intros _. cbn [mgrant req_len]. unfold MG_REQ, MMAX in *. unfold MG_LIVE, MG_SLOTS in *.
pose proof (page_round_bounds (n + IB + UNIT)) as PB. unfold IB, UNIT in *. lia. }
intros ok s1 E1. cbn [snd] in E1. subst s1.
tstep; [tstep|].
apply GT_bind_new_region_map.
pose proof (amc_set_regions s0 (st_regions s0 ++ [mkRegion RkMap (page_round (n + IB + UNIT)) [] true])) as C1.
set (s1 := set_regions _ s0) in *.
eapply (GT_bind (fun r => 0 < amc (snd r))).
{ eapply GT_mono; [|apply (GT_KEEP_presK _ s1); auto with presK]. intros [u s2] [R C]. cbn in R, C |- *. rewrite C. subst s1. cbn. lia. }
intros [] s2 C2. cbn [snd] in C2.
eapply (GT_bind TT). { eapply GT_TT_any. apply GT_alloc_meta. exact C2. }
intros og s3 _. repeat tstep.
-
change (GT ?Q (bind get ?c s0)) with (GT Q (c s0 s0)). cbv beta. lazy zeta.
match goal with |- GT _ (bind _ (fun r => bind (match r with Some gi => ret (Some gi) | None => bind (alloc_slot _ ?sc _) _ end) _) _) =>
set (scz := sc) end.
eapply (GT_bind (KEEP s0)).
{ kgo. }
intros r s1 [R1 C1]. cbn in R1, C1.
eapply (GT_bind TT).
{ destruct r as [gi|]; [apply GT_ret; exact I|].
eapply (GT_bind TT).
{ eapply GT_TT_any. apply GT_alloc_slot.
{ unfold PRE, NEST_FUEL, MMAX, MG_LIVE, MG_SLOTS, live_bytes, nslots in *. rewrite R1, C1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
apply Z.leb_gt in Em. unfold MMAP_THRESHOLD in Em. lia. }
intros idx s2 _. repeat tstep. }
intros gi s2 _. repeat tstep.
Qed.
Lemma gtree_malloc n s0 :
0 <= n < 2 ^ 26 -> 64 <= amc s0 -> live_bytes s0 + 2 ^ 27 <= MG_LIVE -> nslots s0 + 1 <= MG_SLOTS ->
gtree mgrant (malloc n s0).
Proof. intros. eapply GT_gtree. apply GT_malloc; auto. Qed.
End a1.
Ltac solve_gtree_concrete :=
vm_compute; repeat split; try discriminate; try reflexivity.
Ltac gstep :=
lazymatch goal with
| |- gtree _ (IRet _) => exact I
| |- gtree _ (ret _ _) => exact I
| |- gtree _ (bind (ret _) _ _) => rewrite bind_ret_l; cbv beta iota
| |- gtree _ (bind (bind _ _) _ _) => rewrite bind_assoc
| |- gtree _ (bind (if ?c then _ else _) _ _) => rewrite bind_if
| |- gtree _ ((if ?c then _ else _) _) => jif c
| |- gtree _ (if ?c then _ else _) => jif c
| |- gtree _ (bind (read_phase (S _) _ _ _) _ _) => rewrite read_phase_S
| |- gtree _ (bind (read_phase O _ _ _) _ _) => rewrite read_phase_O
| |- gtree _ (bind (read_phase ?f _ _ _) _ _) => let v := eval cbv in f in change f with v
| |- gtree _ (bind (malloc (payload_len _)) _ _) =>
apply gtree_mbind;
[ apply gtree_malloc;
[ unfold payload_len, HDR_MIN, config_len, dlen, CAP0, MAX_INPUT in *; bool_hyps; lia
| (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])
| (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])
| (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) ]
| intros ? [?|] ? ?; exact I ]
| |- gtree _ (bind (malloc ?n) _ ?s) =>
eapply gtree_mbind_leaves;
[ solve_gtree_concrete
| solve_cleaves
| let a := fresh "a" in let s' := fresh "s" in let Hin := fresh "Hin" in
intros a s' Hin; in_cases Hin; cbv beta iota ]
| |- gtree _ (bind (free (Some ?b)) _ ?s) =>
eapply gtree_mbind_leaves;
[ solve_gtree_concrete
| solve_cleaves
| let a := fresh "a" in let s' := fresh "s" in let Hin := fresh "Hin" in
intros a s' Hin; in_cases Hin; cbv beta iota ]
end.
Ltac gwalk := repeat (progress gstep).
Section b1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem do_gtree_proved : forall data, gtree mgrant (driver_tree data).
Proof.
intros data. unfold driver_tree, driver_m.
gwalk.
Qed.
End b1.
