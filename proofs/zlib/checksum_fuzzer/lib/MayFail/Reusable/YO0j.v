(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0j.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition OK4 {A} (P : A -> Prop) (t : itree astate A) : Prop := ok04 mgrant t /\ leaves P t.
Lemma GT_OK4 {A} (P : A -> Prop) t : GT P t -> OK4 P t.
Proof. intros [Hg Hl]. split; [apply gtree_ok04; exact Hg | exact Hl]. Qed.
Lemma leaves_cpath04 {A} : forall (P : A -> Prop) (t : itree astate A) tr a,
leaves P t -> cpath04 t tr a -> P a.
Proof. intros P t tr a Hl Hp. eapply leaves_cpath; [exact Hl | apply cpath04_cpath; exact Hp]. Qed.
Lemma OK4_ibind {A B} (P : A -> Prop) (Q : B -> Prop) t (f : A -> itree astate B) :
OK4 P t -> (forall a, P a -> OK4 Q (f a)) -> OK4 Q (ibind t f).
Proof.
intros [Ho Hl] Hf. split.
- apply ok04_ibind; [exact Ho|]. intros tr a Hp. apply (proj1 (Hf a (leaves_cpath04 _ _ _ _ Hl Hp))).
- eapply leaves_ibind; [exact Hl|]. intros a Ha. apply (proj2 (Hf a Ha)).
Qed.
Lemma OK4_bind {A B} (P : A * astate -> Prop) (Q : B * astate -> Prop) (m : M A) (f : A -> M B) s :
OK4 P (m s) -> (forall a s', P (a, s') -> OK4 Q (f a s')) -> OK4 Q (bind m f s).
Proof. intros Hm Hf. unfold bind. eapply OK4_ibind; [exact Hm|]. intros [a s'] H. apply Hf, H. Qed.
Lemma OK4_mono {A} (P Q : A -> Prop) t : (forall a, P a -> Q a) -> OK4 P t -> OK4 Q t.
Proof. intros H [Ho Hl]. split; [exact Ho | eapply leaves_mono; eauto]. Qed.
Lemma OK4_ret {A} (a : A) s (Q : A * astate -> Prop) : Q (a, s) -> OK4 Q (ret a s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma OK4_fail {A} f s (Q : A * astate -> Prop) : OK4 Q (fail f s).
Proof. split; exact I. Qed.
Lemma OK4_get s (Q : astate * astate -> Prop) : Q (s, s) -> OK4 Q (get s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma OK4_put s s' (Q : unit * astate -> Prop) : Q (tt, s') -> OK4 Q (put s' s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma OK4_modify f s (Q : unit * astate -> Prop) : Q (tt, f s) -> OK4 Q (modify f s).
Proof. intros H. split; [exact I | exact H]. Qed.
Lemma OK4_if {A} (c : bool) (m1 m2 : M A) s Q : OK4 Q (m1 s) -> OK4 Q (m2 s) -> OK4 Q ((if c then m1 else m2) s).
Proof. destruct c; auto. Qed.
Lemma OK4_ask_free q s (Q : bool * astate -> Prop) :
mmapclass q = false -> (forall p, q <> KJunk p) -> (forall b, Q (b, s)) -> OK4 Q (ask q s).
Proof.
intros Hm Hj HQ. split.
- unfold ask. cbn. destruct q; cbn in Hm |- *; try discriminate; auto; try (split; exact I); exfalso; eapply Hj; reflexivity.
- cbn. intros z _. apply HQ.
Qed.
Lemma OK4_ask_room q s (Q : bool * astate -> Prop) :
mgrant s q -> (forall p, q <> KJunk p) -> (forall b, Q (b, s)) -> OK4 Q (ask q s).
Proof.
intros Hg Hj HQ. split.
- unfold ask. cbn. destruct q; cbn; auto; try (split; [exact Hg | exact I]); try (split; exact I); exfalso; eapply Hj; reflexivity.
- cbn. intros z _. apply HQ.
Qed.
Notation amc s := (st_avail_meta_count s).
Definition shift (s : astate) : Z := st_meta_alloc_shift s.
Definition nkeys (s : astate) : Z := Z.of_nat (length (st_metas s)).
Lemma live_bytes_app_any rs k len :
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 (rs ++ [mkRegion k len [] true])
= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 rs + len.
Proof. induction rs as [|r rs IH]; cbn; [lia|]. rewrite IH. destruct (rg_live r); lia. Qed.
Lemma nslots_app_any rs k len :
fold_right (fun rg acc => region_slots rg + acc) 0 (rs ++ [mkRegion k len [] true])
= fold_right (fun rg acc => region_slots rg + acc) 0 rs + region_slots (mkRegion k len [] true).
Proof. induction rs as [|r rs IH]; cbn -[region_slots]; [lia|]. rewrite IH. lia. Qed.
Lemma resv_app_any rs k len :
fold_right (fun rg acc => match rg_kind rg with RkMetaRes => rg_len rg + acc | _ => acc end) 0 (rs ++ [mkRegion k len [] true])
= fold_right (fun rg acc => match rg_kind rg with RkMetaRes => rg_len rg + acc | _ => acc end) 0 rs
+ match k with RkMetaRes => len | _ => 0 end.
Proof. induction rs as [|r rs IH]; cbn; [destruct k; lia|]. rewrite IH. destruct (rg_kind r); lia. Qed.
Definition cres (s : astate) : list sptr * Z * Z * brkst :=
(st_areas s, st_meta_alloc_shift s, st_avail_meta_area_count s, st_brk s).
Definition KEEPC (s : astate) {A} (r : A * astate) : Prop := cres (snd r) = cres s.
Definition presC {A} (m : M A) : Prop := forall s, GT (KEEPC s) (m s).
Lemma KEEPC_refl s {A} (a : A) : KEEPC s (a, s). Proof. reflexivity. Qed.
Lemma KEEPC_trans s s1 {A B} (a : A) (b : B) s2 : KEEPC s (a, s1) -> KEEPC s1 (b, s2) -> KEEPC s (b, s2).
Proof. unfold KEEPC; cbn. intros H1 H2. rewrite H2, H1. reflexivity. Qed.
Lemma presC_bind {A B} (m : M A) (k : A -> M B) : presC m -> (forall a, presC (k a)) -> presC (bind m k).
Proof.
intros Hm Hk s. eapply GT_bind; [apply Hm|]. intros a s' HK. eapply GT_mono; [|apply Hk].
intros [b s2] H2. eapply KEEPC_trans; eauto.
Qed.
Lemma presC_bind_get {B} (k : astate -> M B) : (forall s, GT (KEEPC s) (k s s)) -> presC (bind get k).
Proof. intros Hk s. unfold bind, get. cbn. apply Hk. Qed.
Lemma presC_ret {A} (a : A) : presC (ret a). Proof. intros s. apply GT_ret. apply KEEPC_refl. Qed.
Lemma presC_get : presC get. Proof. intros s. apply GT_get. apply KEEPC_refl. Qed.
Lemma presC_fail {A} f : presC (@fail A f). Proof. intros s. apply GT_fail. Qed.
Lemma presC_massert b x : presC (massert b x). Proof. intros s. apply GT_massert. apply KEEPC_refl. Qed.
Lemma presC_mcheck b x : presC (mcheck b x). Proof. intros s. apply GT_mcheck. apply KEEPC_refl. Qed.
Lemma presC_modify f : (forall s, cres (f s) = cres s) -> presC (modify f).
Proof. intros Hf s. apply GT_modify. unfold KEEPC. cbn [snd]. apply Hf. Qed.
Lemma presC_askz_junk p : presC (askz (KJunk p)). Proof. intros s. apply GT_askz_junk. intros; apply KEEPC_refl. Qed.
Lemma GT_KEEPC_presC {A} (m : M A) s : presC m -> GT (KEEPC s) (m s). Proof. intros H; apply H. Qed.
Lemma GT_put_KEEPC s s1 : cres s1 = cres s -> GT (KEEPC s) (put s1 s).
Proof. intros H1. apply GT_put. exact H1. Qed.
End j.
Create HintDb presC.
Ltac cstep :=
lazymatch goal with
| |- presC (bind get _) => apply presC_bind_get; intros ?
| |- presC (bind _ _) => apply presC_bind; [ | intros ? ]
| |- presC (ret _) => apply presC_ret
| |- presC get => apply presC_get
| |- presC (fail _) => apply presC_fail
| |- presC (massert _ _) => apply presC_massert
| |- presC (mcheck _ _) => apply presC_mcheck
| |- presC (askz (KJunk _)) => apply presC_askz_junk
| |- presC (modify _) => apply presC_modify; [ intros ?; cbn; reflexivity ]
| |- presC (match ?x with _ => _ end) => destruct x
| |- presC (if ?x then _ else _) => destruct x
| |- presC _ => solve [auto with presC]
| |- KEEPC _ _ => cbn; reflexivity
| |- GT _ (IRet _) => apply GT_IRet
| |- GT (KEEPC _) (match ?x with _ => _ end _) => destruct x
| |- GT (KEEPC _) ((if ?b then _ else _) _) => destruct b
| |- GT (KEEPC _) (put _ _) => apply GT_put_KEEPC; cbn; reflexivity
| |- GT ?P (bind (put ?s1) ?k ?s0) => change (GT P (k tt s1))
| |- GT ?P (bind get ?k ?s0) => change (GT P (k s0 s0))
| |- GT ?P (bind (modify ?f) ?k ?s0) => change (GT P (k tt (f s0)))
| |- GT (KEEPC ?s0) (?m ?s) =>
tryif constr_eq s0 s then (apply (GT_KEEPC_presC m s))
else (eapply GT_mono; [ | apply (GT_KEEPC_presC m s) ];
[ intros [? ?] ?; eapply KEEPC_trans; [ | eassumption]; cbn; reflexivity | ])
end.
Ltac cgo := repeat cstep.
Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_getm p : presC (getm p). Proof. unfold getm. cgo. Qed.
Lemma c_setm p am : presC (setm p am). Proof. unfold setm. cgo. Qed.
Lemma c_setslot p x : presC (setslot p x). Proof. unfold setslot. cgo. Qed.
Lemma c_get_links p : presC (get_links p). Proof. unfold get_links. cgo. Qed.
End o.
#[export] Hint Resolve c_getm c_setm c_setslot c_get_links presC_ret presC_get presC_fail presC_massert presC_mcheck presC_askz_junk : presC.
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_set_links p a b : presC (set_links p a b). Proof. unfold set_links. cgo. Qed.
End u.
#[export] Hint Resolve c_set_links : presC.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_set_prev p a : presC (set_prev p a). Proof. unfold set_prev. cgo. Qed.
Lemma c_set_next p a : presC (set_next p a). Proof. unfold set_next. cgo. Qed.
Lemma c_get_head h : presC (get_head h). Proof. unfold get_head. cgo. Qed.
Lemma c_set_head h v : presC (set_head h v). Proof. unfold set_head. destruct h; cgo. Qed.
End w.
#[export] Hint Resolve c_set_prev c_set_next c_get_head c_set_head : presC.
Section y. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_queue h m : presC (queue h m). Proof. unfold queue. cgo. Qed.
Lemma c_dequeue h m : presC (dequeue h m). Proof. unfold dequeue. cgo. Qed.
End y.
#[export] Hint Resolve c_queue c_dequeue : presC.
Section a0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_dequeue_head h : presC (dequeue_head h). Proof. unfold dequeue_head. cgo. Qed.
Lemma c_free_meta m : presC (free_meta m). Proof. unfold free_meta. cgo. Qed.
Lemma c_set_usage_of sc v : presC (set_usage_of sc v). Proof. unfold set_usage_of. cgo. Qed.
Lemma c_step_seq : presC step_seq.
Proof. unfold step_seq. apply presC_modify. intros s. destruct (st_seq s =? 255); cbn; reflexivity. Qed.
Lemma c_record_seq sc : presC (record_seq sc). Proof. unfold record_seq. cgo. Qed.
Lemma c_account_bounce sc : presC (account_bounce sc).
Proof. unfold account_bounce. destruct (bounce_idx sc); [|cgo]. apply presC_modify. intros s. cbn zeta.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; reflexivity. Qed.
Lemma c_decay_bounces sc : presC (decay_bounces sc).
Proof. unfold decay_bounces. destruct (bounce_idx sc); [|cgo]. apply presC_modify. intros s. cbn zeta.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; reflexivity. Qed.
End a0.
#[export] Hint Resolve c_dequeue_head c_free_meta c_set_usage_of c_step_seq c_record_seq c_account_bounce c_decay_bounces : presC.
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_activate_group m : presC (activate_group m). Proof. unfold activate_group. cgo. Qed.
End b0.
#[export] Hint Resolve c_activate_group : presC.
Section c0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_try_avail sc : presC (try_avail sc). Proof. unfold try_avail. cgo. Qed.
Lemma c_enframe g idx n ctr k : presC (enframe g idx n ctr k). Proof. unfold enframe. cgo. Qed.
End c0.
#[export] Hint Resolve c_try_avail c_enframe : presC.
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_install_group m sc cnt aidx maplen mem sl : presC (install_group m sc cnt aidx maplen mem sl).
Proof. unfold install_group. cgo. Qed.
Lemma c_find_frame p : presC (find_frame p). Proof. unfold find_frame. cgo. Qed.
Lemma c_forget_frame g i : presC (forget_frame g i). Proof. unfold forget_frame. cgo. Qed.
End d0.
#[export] Hint Resolve c_install_group c_find_frame c_forget_frame : presC.
Section e0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c_release_slot g i : presC (release_slot g i). Proof. unfold release_slot. cgo. Qed.
Lemma c_new_region k len : presC (new_region k len).
Proof. intros s0. unfold new_region, bind, get, put, ret. cbn. apply GT_IRet. reflexivity. Qed.
Lemma c_upd_region r f : presC (upd_region r f). Proof. unfold upd_region. cgo. Qed.
End e0.
#[export] Hint Resolve c_release_slot c_new_region c_upd_region : presC.
Section f0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition rsum (f : region -> Z) (l : list region) : Z := fold_right (fun rg acc => f rg + acc) 0 l.
Lemma rsum_cons f r l : rsum f (r :: l) = f r + rsum f l.
Proof. reflexivity. Qed.
Lemma rsum_nil f : rsum f [] = 0.
Proof. reflexivity. Qed.
Lemma rsum_app f l1 l2 : rsum f (l1 ++ l2) = rsum f l1 + rsum f l2.
Proof. induction l1 as [|r l1 IH]; [rewrite rsum_nil; cbn [app]; lia|]. cbn [app]. rewrite !rsum_cons, IH. lia. Qed.
Lemma rsum_lupd f l : forall i v d, (i < length l)%nat -> rsum f (lupd l i v) = rsum f l - f (nth i l d) + f v.
Proof.
induction l as [|r l IH]; intros i v d Hi; cbn in Hi; [lia|].
destruct i as [|i]; cbn [lupd nth]; rewrite !rsum_cons; [lia|]. rewrite (IH i v d) by lia. lia.
Qed.
Lemma rsum_le f g l : (forall r, In r l -> f r <= g r) -> rsum f l <= rsum g l.
Proof. induction l as [|r l IH]; intros H; [rewrite !rsum_nil; lia|]. rewrite !rsum_cons. pose proof (H r (or_introl eq_refl)). assert (rsum f l <= rsum g l) by (apply IH; intros x Hx; apply H; right; exact Hx). lia. Qed.
Lemma rsum_zero l : rsum (fun _ => 0) l = 0.
Proof. induction l as [|r l IH]; [reflexivity|]. rewrite rsum_cons, IH. reflexivity. Qed.
Lemma rsum_nonneg f l : (forall r, In r l -> 0 <= f r) -> 0 <= rsum f l.
Proof. intros H. pose proof (rsum_le (fun _ => 0) f l H). rewrite rsum_zero in *. lia. Qed.
Lemma rsum_plus f g l : rsum (fun r => f r + g r) l = rsum f l + rsum g l.
Proof. induction l as [|r l IH]; [rewrite !rsum_nil; lia|]. rewrite !rsum_cons, IH. lia. Qed.
Definition is_map (rg : region) : bool := match rg_kind rg with RkMap => true | _ => false end.
Definition is_brk (rg : region) : bool := match rg_kind rg with RkBrk => true | _ => false end.
Definition is_resv (rg : region) : bool := match rg_kind rg with RkMetaRes => true | _ => false end.
Definition f_live (rg : region) : Z := if rg_live rg then rg_len rg else 0.
Definition f_mapb (rg : region) : Z := if rg_live rg && is_map rg then rg_len rg else 0.
Definition f_mapc (rg : region) : Z := if rg_live rg && is_map rg then 1 else 0.
Definition f_brkb (rg : region) : Z := if rg_live rg && is_brk rg then rg_len rg else 0.
Definition f_resvb (rg : region) : Z := if is_resv rg then rg_len rg else 0.
Definition f_resvc (rg : region) : Z := if is_resv rg then 1 else 0.
Definition map_bytes (s : astate) : Z := rsum f_mapb (st_regions s).
Definition map_count (s : astate) : Z := rsum f_mapc (st_regions s).
Definition brk_bytes (s : astate) : Z := rsum f_brkb (st_regions s).
Definition resv_count (s : astate) : Z := rsum f_resvc (st_regions s).
Lemma live_bytes_rsum s : live_bytes s = rsum f_live (st_regions s).
Proof. unfold live_bytes. induction (st_regions s) as [|r l IH]; [reflexivity|]. cbn [fold_right]. rewrite rsum_cons, IH. unfold f_live. destruct (rg_live r); lia. Qed.
Lemma nslots_rsum s : nslots s = rsum region_slots (st_regions s).
Proof. reflexivity. Qed.
Lemma resv_total_rsum s : resv_total s = rsum f_resvb (st_regions s).
Proof. unfold resv_total. induction (st_regions s) as [|r l IH]; [reflexivity|]. cbn [fold_right]. rewrite rsum_cons, IH. unfold f_resvb, is_resv. destruct (rg_kind r); lia. Qed.
Definition regs_nn (s : astate) : Prop := forall r, In r (st_regions s) -> 0 <= rg_len r.
Lemma regs_nn_wf s : WF s -> regs_nn s.
Proof.
intros HW r Hr. destruct (inv_areas HW) as (_ & _ & _ & _ & _ & _ & _ & _ & Hnn).
apply In_nth_error in Hr as [k Hk]. exact (Hnn k r Hk).
Qed.
Lemma live_bytes_decomp s : regs_nn s -> live_bytes s <= map_bytes s + brk_bytes s + resv_total s.
Proof.
intros NN. rewrite live_bytes_rsum, resv_total_rsum. unfold map_bytes, brk_bytes. rewrite <- !rsum_plus.
apply rsum_le. intros r Hr. pose proof (NN r Hr). unfold f_live, f_mapb, f_brkb, f_resvb, is_map, is_brk, is_resv.
destruct (rg_live r), (rg_kind r); cbn; lia.
Qed.
Lemma brk_div_le l : (forall r, In r l -> 0 <= rg_len r) ->
rsum (fun r => if rg_live r && is_brk r then rg_len r / PGSZ else 0) l <= rsum f_brkb l / PGSZ.
Proof.
induction l as [|r l IH]; intros NN; [rewrite !rsum_nil, Zdiv_0_l; lia|].
rewrite !rsum_cons. assert (NN' : forall x, In x l -> 0 <= rg_len x) by (intros x Hx; apply NN; right; exact Hx).
specialize (IH NN'). pose proof (NN r (or_introl eq_refl)) as Hr.
assert (G : 0 <= rsum f_brkb l).
{ apply rsum_nonneg. intros x Hx. unfold f_brkb. destruct (rg_live x && is_brk x); [apply NN'; exact Hx|lia]. }
set (B := rsum f_brkb l) in *. unfold f_brkb.
set (C := rsum (fun r0 => if rg_live r0 && is_brk r0 then rg_len r0 / PGSZ else 0) l) in *.
destruct (rg_live r && is_brk r).
- assert (rg_len r / PGSZ + B / PGSZ <= (rg_len r + B) / PGSZ); [|lia].
apply Z.div_le_lower_bound; [unfold PGSZ; lia|].
pose proof (Z.mul_div_le (rg_len r) PGSZ ltac:(unfold PGSZ; lia)). pose proof (Z.mul_div_le B PGSZ ltac:(unfold PGSZ; lia)). lia.
- rewrite !Z.add_0_l. lia.
Qed.
Lemma nslots_decomp s : regs_nn s -> nslots s <= map_count s + brk_bytes s / PGSZ + resv_count s.
Proof.
intros NN. rewrite nslots_rsum. unfold map_count, brk_bytes, resv_count.
pose proof (brk_div_le (st_regions s) NN) as Hb.
eapply Z.le_trans; [| apply Z.add_le_mono; [apply Z.add_le_mono; [apply Z.le_refl | exact Hb] | apply Z.le_refl]].
rewrite <- !rsum_plus. apply rsum_le. intros r Hr. pose proof (NN r Hr).
unfold region_slots, f_mapc, f_resvc, is_map, is_brk, is_resv. destruct (rg_live r), (rg_kind r); cbn -[Z.div PGSZ]; try lia.
Qed.
End f0.
Section g0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma reqs_ok_ibind_inv {A B} (t : itree astate A) (f : A -> itree astate B) :
reqs_ok (ibind t f) -> reqs_ok t /\ forall tr a, yields t tr a -> reqs_ok (f a).
Proof.
induction t as [a | q snap k IH | e]; cbn; intros H.
- split; [exact I|]. intros tr a' Hy. destruct tr; [subst; exact H | destruct Hy].
- destruct H as [Hr Hk]. split.
+ split; [exact Hr|]. intros z Hz. apply (proj1 (IH z (Hk z Hz))).
+ intros [|[q' z] tr] a Hy; [destruct Hy|]. destruct Hy as (-> & Hz & Hy). apply (proj2 (IH z (Hk z Hz)) tr a Hy).
- split; [exact I|]. intros tr a Hy. destruct tr; destruct Hy.
Qed.
Lemma reqs_ok_mbind_inv {A B} (m : M A) (f : A -> M B) s :
reqs_ok (bind m f s) -> reqs_ok (m s) /\ forall tr a s', yields (m s) tr (a, s') -> reqs_ok (f a s').
Proof. intros H. unfold bind in H. destruct (reqs_ok_ibind_inv _ _ H) as [H1 H2]. split; [exact H1|]. intros tr a s' Hy. exact (H2 tr (a, s') Hy). Qed.
Lemma reqs_ok_ask_inv q s : reqs_ok (ask q s) -> req_ok s q.
Proof. intros [H _]. exact H. Qed.
Lemma leaves_ibind_yields {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree astate A) (f : A -> itree astate B) :
leaves P t -> (forall tr a, yields t tr a -> P a -> leaves Q (f a)) -> leaves Q (ibind t f).
Proof.
induction t as [a | q snap k IH | e]; cbn; intros Hl Hf.
- apply (Hf []); [reflexivity | exact Hl].
- intros z Hz. apply IH; [apply Hl; exact Hz|]. intros tr a Hy HP.
apply (Hf ((q, z) :: tr)); [cbn; auto | exact HP].
- exact I.
Qed.
Lemma OK4_bind_y {A B} (P : A * astate -> Prop) (Q : B * astate -> Prop) (m : M A) (f : A -> M B) s :
OK4 P (m s) -> (forall a s' tr, yields (m s) tr (a, s') -> P (a, s') -> OK4 Q (f a s')) -> OK4 Q (bind m f s).
Proof.
intros [Ho Hl] Hf. unfold bind. split.
- apply ok04_ibind; [exact Ho|]. intros tr [a s'] Hp.
apply (proj1 (Hf a s' tr (cpath04_yields _ _ _ Hp) (leaves_cpath04 _ _ _ _ Hl Hp))).
- eapply leaves_ibind_yields; [exact Hl|]. intros tr [a s'] Hy HP. apply (proj2 (Hf a s' tr Hy HP)).
Qed.
End g0.
