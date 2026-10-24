(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition is_junk (q : kreq) : bool := match q with KJunk _ => true | _ => false end.
Lemma tsim_ask_inv {A B} (R : A -> B -> Prop) q sp k q' sp' k' :
tsim R (IAsk q sp k) (IAsk q' sp' k') ->
(is_junk q = true /\ is_junk q' = true /\
forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> tsim R (k z) (k' z'))
\/ (is_junk q = false /\ q = q' /\ forall z, tsim R (k z) (k' z)).
Proof. intros H. destruct q, q'; cbn in H; first [right; split; [reflexivity|exact H] | left; split; [reflexivity|split; [reflexivity|exact H]] | destruct H as [H _]; discriminate]. Qed.
Lemma tsim_ask_intro {A B} (R : A -> B -> Prop) q sp k q' sp' k' :
((is_junk q = true /\ is_junk q' = true /\
forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> tsim R (k z) (k' z'))
\/ (is_junk q = false /\ q = q' /\ forall z, tsim R (k z) (k' z))) ->
tsim R (IAsk q sp k) (IAsk q' sp' k').
Proof.
intros [(J & J' & H) | (J & <- & H)].
- destruct q, q'; cbn in J, J'; try discriminate. exact H.
- destruct q; cbn in J; try discriminate; cbn; (split; [reflexivity|exact H]).
Qed.
Lemma tsim_mono {A B} (R R' : A -> B -> Prop) (x : itree astate A) (y : itree astate B) :
(forall a b, R a b -> R' a b) -> tsim R x y -> tsim R' x y.
Proof.
intros HR. revert y. induction x as [a | q sp k IH | f]; intros y H; destruct y as [b | q' sp' k' | f'];
try (cbn in H; first [contradiction | destruct q; contradiction]).
- exact (HR _ _ H).
- apply tsim_ask_inv in H. apply tsim_ask_intro. destruct H as [(J & J' & H) | (J & E & H)].
+ left. split; [exact J|]. split; [exact J'|]. intros z z' Hz Hz'. apply IH. apply H; assumption.
+ right. split; [exact J|]. split; [exact E|]. intros z. apply IH. apply H.
- exact I.
Qed.
Lemma tsim_ibind {A B C D} (R1 : A -> B -> Prop) (R2 : C -> D -> Prop)
(x : itree astate A) (y : itree astate B) (K : A -> itree astate C) (K' : B -> itree astate D) :
tsim R1 x y -> (forall a b, R1 a b -> tsim R2 (K a) (K' b)) -> tsim R2 (ibind x K) (ibind y K').
Proof.
intros H HK. revert y H. induction x as [a | q sp k IH | f]; intros y H; destruct y as [b | q' sp' k' | f'];
try (cbn in H; first [contradiction | destruct q; contradiction]).
- cbn. apply HK, H.
- cbn [ibind]. apply tsim_ask_inv in H. apply tsim_ask_intro. destruct H as [(J & J' & H) | (J & E & H)].
+ left. split; [exact J|]. split; [exact J'|]. intros z z' Hz Hz'. apply IH. apply H; assumption.
+ right. split; [exact J|]. split; [exact E|]. intros z. apply IH. apply H.
- exact I.
Qed.
Lemma itok_unbind {A B} (x : itree astate A) (K : A -> itree astate B) Q :
itok (ibind x K) Q -> itok x (fun a => itok (K a) Q).
Proof.
induction x as [a | q sp k IH | f]; cbn; intros H; [exact H | | exact H].
destruct H as [Hq H]. split; [exact Hq|]. intros z Hz. apply IH. apply H, Hz.
Qed.
Definition rsim {A B} (R : A -> B -> Prop) (x : itree astate A) (y : itree astate B) : Prop :=
forall P P', itok x P -> itok y P' -> tsim (fun a b => R a b /\ P a /\ P' b) x y.
Lemma rsim_tsim {A B} (R : A -> B -> Prop) x y P P' :
rsim R x y -> itok x P -> itok y P' -> tsim (fun a b => R a b /\ P a /\ P' b) x y.
Proof. intros H Hx Hy. exact (H P P' Hx Hy). Qed.
Lemma rsim_mono {A B} (R R' : A -> B -> Prop) (x : itree astate A) (y : itree astate B) :
(forall a b, R a b -> R' a b) -> rsim R x y -> rsim R' x y.
Proof.
intros HR H P P' Hx Hy. eapply tsim_mono; [|exact (H P P' Hx Hy)]. intros a b (H1 & H2 & H3). auto.
Qed.
Lemma rsim_iret {A B} (R : A -> B -> Prop) a b : R a b -> rsim R (IRet a) (IRet b).
Proof. intros H P P' Hx Hy. cbn in *. auto. Qed.
Lemma rsim_ifail_l {A B} (R : A -> B -> Prop) f (y : itree astate B) : rsim R (IFail f) y.
Proof. intros P P' Hx Hy. destruct Hx. Qed.
Lemma rsim_ifail_r {A B} (R : A -> B -> Prop) (x : itree astate A) f : rsim R x (IFail f).
Proof. intros P P' Hx Hy. destruct Hy. Qed.
Lemma rsim_ibind {A B C D} (R1 : A -> B -> Prop) (R2 : C -> D -> Prop)
(x : itree astate A) (y : itree astate B) (K : A -> itree astate C) (K' : B -> itree astate D) :
rsim R1 x y -> (forall a b, R1 a b -> rsim R2 (K a) (K' b)) -> rsim R2 (ibind x K) (ibind y K').
Proof.
intros H HK P P' Hx Hy. apply itok_unbind in Hx. apply itok_unbind in Hy.
eapply tsim_ibind; [exact (H _ _ Hx Hy)|]. intros a b (H1 & H2 & H3). exact (HK a b H1 P P' H2 H3).
Qed.
Lemma rsim_iask {A B} (R : A -> B -> Prop) q sp sp' k k' :
is_junk q = false -> (forall z, rsim R (k z) (k' z)) -> rsim R (IAsk q sp k) (IAsk q sp' k').
Proof.
intros J H P P' Hx Hy. cbn in Hx, Hy. destruct Hx as [_ Hx], Hy as [_ Hy].
apply tsim_ask_intro. right. split; [exact J|]. split; [reflexivity|]. intros z.
assert (Az : answer_ok q z) by (destruct q; cbn in J |- *; first [exact I | discriminate]).
exact (H z P P' (Hx z Az) (Hy z Az)).
Qed.
Lemma rsim_iask_junk {A B} (R : A -> B -> Prop) c c' sp sp' k k' :
(forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> rsim R (k z) (k' z')) ->
rsim R (IAsk (KJunk c) sp k) (IAsk (KJunk c') sp' k').
Proof.
intros H P P' Hx Hy. cbn in Hx, Hy. destruct Hx as [_ Hx], Hy as [_ Hy].
cbn. intros z z' Hz Hz'. exact (H z z' Hz Hz' P P' (Hx z Hz) (Hy z' Hz')).
Qed.
Section d.
Context {A B : Type}.
Implicit Types (s t : astate).
Lemma rsim_ret (R : A * astate -> A * astate -> Prop) (a b : A) s t :
R (a, s) (b, t) -> rsim R (ret a s) (ret b t).
Proof. intros H. apply rsim_iret. exact H. Qed.
Lemma rsim_bind (R1 : B * astate -> B * astate -> Prop) (R2 : A * astate -> A * astate -> Prop)
(m m' : M B) (k k' : B -> M A) s t :
rsim R1 (m s) (m' t) ->
(forall b s1 b' t1, R1 (b, s1) (b', t1) -> rsim R2 (k b s1) (k' b' t1)) ->
rsim R2 (bind m k s) (bind m' k' t).
Proof.
intros H HK. unfold bind. eapply rsim_ibind; [exact H|]. intros [b s1] [b' t1] Hb. exact (HK _ _ _ _ Hb).
Qed.
Lemma rsim_fail_l R f s (y : itree astate (A * astate)) : rsim R (@fail A f s) y.
Proof. apply rsim_ifail_l. Qed.
Lemma rsim_fail_r R (x : itree astate (A * astate)) f t : rsim R x (@fail A f t).
Proof. apply rsim_ifail_r. Qed.
Lemma rsim_get (R : astate * astate -> astate * astate -> Prop) s t :
R (s, s) (t, t) -> rsim R (get s) (get t).
Proof. intros H. apply rsim_iret. exact H. Qed.
Lemma rsim_put (R : unit * astate -> unit * astate -> Prop) s1 t1 s t :
R (tt, s1) (tt, t1) -> rsim R (put s1 s) (put t1 t).
Proof. intros H. apply rsim_iret. exact H. Qed.
Lemma rsim_modify (R : unit * astate -> unit * astate -> Prop) f f' s t :
R (tt, f s) (tt, f' t) -> rsim R (modify f s) (modify f' t).
Proof. intros H. apply rsim_iret. exact H. Qed.
Lemma rsim_ask (R : bool * astate -> bool * astate -> Prop) q s t :
is_junk q = false -> (forall b : bool, R (b, s) (b, t)) -> rsim R (ask q s) (ask q t).
Proof. intros J H. unfold ask. apply rsim_iask; [exact J|]. intros z. apply rsim_iret. apply H. Qed.
Lemma rsim_askz_junk (R : Z * astate -> Z * astate -> Prop) c c' s t :
(forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> R (z, s) (z', t)) ->
rsim R (askz (KJunk c) s) (askz (KJunk c') t).
Proof. intros H. unfold askz. apply rsim_iask_junk. intros z z' Hz Hz'. apply rsim_iret. apply H; assumption. Qed.
End d.
Lemma rsim_massert (R : unit * astate -> unit * astate -> Prop) b b' i i' s t :
(b = true -> b' = true -> R (tt, s) (tt, t)) -> rsim R (massert b i s) (massert b' i' t).
Proof.
intros H. unfold massert. destruct b; [|apply rsim_ifail_l]. destruct b'; [|apply rsim_ifail_r].
apply rsim_ret. apply H; reflexivity.
Qed.
Lemma rsim_mcheck (R : unit * astate -> unit * astate -> Prop) b b' i i' s t :
(b = true -> b' = true -> R (tt, s) (tt, t)) -> rsim R (mcheck b i s) (mcheck b' i' t).
Proof.
intros H. unfold mcheck. destruct b; [|apply rsim_ifail_l]. destruct b'; [|apply rsim_ifail_r].
apply rsim_ret. apply H; reflexivity.
Qed.
Definition erase_am (am : ameta) : ameta := am_set_slots (map erase_slot (am_slots am)) am.
Definition ef (e : sptr * mslot) : sptr * mslot := (fst e, erase_meta (snd e)).
Definition mrel (ms mt : list (sptr * mslot)) : Prop := map ef ms = map ef mt.
Lemma erase_unfold s : erase s = set_metas (map ef (st_metas s)) s.
Proof. reflexivity. Qed.
Definition sheq (s t : astate) : Prop := shape_eq s t /\ NoDup (keys s).
Lemma sheq_shape s t : sheq s t -> shape_eq s t.
Proof. intros [H _]; exact H. Qed.
Lemma sq_metas s t : shape_eq s t -> mrel (st_metas s) (st_metas t).
Proof. intros H. exact (f_equal st_metas H). Qed.
Lemma sheq_metas s t : sheq s t -> mrel (st_metas s) (st_metas t).
Proof. intros [H _]. apply sq_metas, H. Qed.
Lemma mrel_keys ms mt : mrel ms mt -> map fst ms = map fst mt.
Proof.
intros H. transitivity (map fst (map ef ms)); [rewrite map_map; reflexivity|].
unfold mrel in H. rewrite H, map_map. reflexivity.
Qed.
Lemma sheq_nodup_l s t : sheq s t -> NoDup (keys s).
Proof. intros [_ H]; exact H. Qed.
Lemma sheq_nodup_r s t : sheq s t -> NoDup (keys t).
Proof. intros [H ND]. unfold keys in *. rewrite <- (mrel_keys _ _ (sq_metas _ _ H)). exact ND. Qed.
Lemma sq_init_done s t : sheq s t -> st_init_done t = st_init_done s.
Proof. intros [H _]. symmetry. exact (f_equal st_init_done H). Qed.
Lemma sq_mmap_counter s t : sheq s t -> st_mmap_counter t = st_mmap_counter s.
Proof. intros [H _]. symmetry. exact (f_equal st_mmap_counter H). Qed.
Lemma sq_free_meta_head s t : sheq s t -> st_free_meta_head t = st_free_meta_head s.
Proof. intros [H _]. symmetry. exact (f_equal st_free_meta_head H). Qed.
Lemma sq_avail_meta s t : sheq s t -> st_avail_meta t = st_avail_meta s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta H). Qed.
Lemma sq_avail_meta_count s t : sheq s t -> st_avail_meta_count t = st_avail_meta_count s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_count H). Qed.
Lemma sq_avail_meta_area_count s t : sheq s t -> st_avail_meta_area_count t = st_avail_meta_area_count s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_area_count H). Qed.
Lemma sq_meta_alloc_shift s t : sheq s t -> st_meta_alloc_shift t = st_meta_alloc_shift s.
Proof. intros [H _]. symmetry. exact (f_equal st_meta_alloc_shift H). Qed.
Lemma sq_area_head s t : sheq s t -> st_area_head t = st_area_head s.
Proof. intros [H _]. symmetry. exact (f_equal st_area_head H). Qed.
Lemma sq_area_tail s t : sheq s t -> st_area_tail t = st_area_tail s.
Proof. intros [H _]. symmetry. exact (f_equal st_area_tail H). Qed.
Lemma sq_avail_meta_areas s t : sheq s t -> st_avail_meta_areas t = st_avail_meta_areas s.
Proof. intros [H _]. symmetry. exact (f_equal st_avail_meta_areas H). Qed.
Lemma sq_active s t : sheq s t -> st_active t = st_active s.
Proof. intros [H _]. symmetry. exact (f_equal st_active H). Qed.
Lemma sq_usage s t : sheq s t -> st_usage t = st_usage s.
Proof. intros [H _]. symmetry. exact (f_equal st_usage H). Qed.
Lemma sq_unmap_seq s t : sheq s t -> st_unmap_seq t = st_unmap_seq s.
Proof. intros [H _]. symmetry. exact (f_equal st_unmap_seq H). Qed.
Lemma sq_bounces s t : sheq s t -> st_bounces t = st_bounces s.
Proof. intros [H _]. symmetry. exact (f_equal st_bounces H). Qed.
Lemma sq_seq s t : sheq s t -> st_seq t = st_seq s.
Proof. intros [H _]. symmetry. exact (f_equal st_seq H). Qed.
Lemma sq_brk s t : sheq s t -> st_brk t = st_brk s.
Proof. intros [H _]. symmetry. exact (f_equal st_brk H). Qed.
Lemma sq_regions s t : sheq s t -> st_regions t = st_regions s.
Proof. intros [H _]. symmetry. exact (f_equal st_regions H). Qed.
Lemma sq_areas s t : sheq s t -> st_areas t = st_areas s.
Proof. intros [H _]. symmetry. exact (f_equal st_areas H). Qed.
Lemma sq_is_bouncing s t sc : sheq s t -> is_bouncing t sc = is_bouncing s sc.
Proof. intros H. unfold is_bouncing. rewrite (sq_bounces _ _ H). reflexivity. Qed.
Lemma sq_usage_of s t sc : sheq s t -> usage_of t sc = usage_of s sc.
Proof. intros H. unfold usage_of. rewrite (sq_usage _ _ H). reflexivity. Qed.
Lemma sq_active_hd s t sc : sheq s t -> active_hd t sc = active_hd s sc.
Proof. intros H. unfold active_hd. rewrite (sq_active _ _ H). reflexivity. Qed.
Lemma sq_mmap_plan s t sc req c u : sheq s t -> mmap_plan t sc req c u = mmap_plan s sc req c u.
Proof. intros H. unfold mmap_plan. rewrite !(sq_is_bouncing _ _ _ H), !(sq_usage_of _ _ _ H). reflexivity. Qed.
Ltac shrw H := rewrite ?(sq_mmap_plan _ _ _ _ _ _ H), ?(sq_is_bouncing _ _ _ H), ?(sq_usage_of _ _ _ H), ?(sq_active_hd _ _ _ H), ?(sq_init_done _ _ H), ?(sq_mmap_counter _ _ H), ?(sq_free_meta_head _ _ H), ?(sq_avail_meta _ _ H), ?(sq_avail_meta_count _ _ H), ?(sq_avail_meta_area_count _ _ H), ?(sq_meta_alloc_shift _ _ H), ?(sq_area_head _ _ H), ?(sq_area_tail _ _ H), ?(sq_avail_meta_areas _ _ H), ?(sq_active _ _ H), ?(sq_usage _ _ H), ?(sq_unmap_seq _ _ H), ?(sq_bounces _ _ H), ?(sq_seq _ _ H), ?(sq_brk _ _ H), ?(sq_regions _ _ H), ?(sq_areas _ _ H) in *.
Ltac shrwg H := rewrite ?(sq_mmap_plan _ _ _ _ _ _ H), ?(sq_is_bouncing _ _ _ H), ?(sq_usage_of _ _ _ H), ?(sq_active_hd _ _ _ H), ?(sq_init_done _ _ H), ?(sq_mmap_counter _ _ H), ?(sq_free_meta_head _ _ H), ?(sq_avail_meta _ _ H), ?(sq_avail_meta_count _ _ H), ?(sq_avail_meta_area_count _ _ H), ?(sq_meta_alloc_shift _ _ H), ?(sq_area_head _ _ H), ?(sq_area_tail _ _ H), ?(sq_avail_meta_areas _ _ H), ?(sq_active _ _ H), ?(sq_usage _ _ H), ?(sq_unmap_seq _ _ H), ?(sq_bounces _ _ H), ?(sq_seq _ _ H), ?(sq_brk _ _ H), ?(sq_regions _ _ H), ?(sq_areas _ _ H).
Lemma sq_mk x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 ms mt :
mrel ms mt -> shape_eq (mkA x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ms x17 x18) (mkA x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 mt x17 x18).
Proof. intros H. unfold shape_eq. rewrite !erase_unfold. cbn. unfold mrel in H. rewrite H. reflexivity. Qed.
Lemma sq_fields s t :
shape_eq s t <-> (st_init_done s = st_init_done t /\ st_mmap_counter s = st_mmap_counter t /\ st_free_meta_head s = st_free_meta_head t /\ st_avail_meta s = st_avail_meta t /\ st_avail_meta_count s = st_avail_meta_count t /\ st_avail_meta_area_count s = st_avail_meta_area_count t /\ st_meta_alloc_shift s = st_meta_alloc_shift t /\ st_area_head s = st_area_head t /\ st_area_tail s = st_area_tail t /\ st_avail_meta_areas s = st_avail_meta_areas t /\ st_active s = st_active t /\ st_usage s = st_usage t /\ st_unmap_seq s = st_unmap_seq t /\ st_bounces s = st_bounces t /\ st_seq s = st_seq t /\ st_brk s = st_brk t /\ st_regions s = st_regions t /\ st_areas s = st_areas t /\ mrel (st_metas s) (st_metas t)).
Proof.
split.
- intros H. repeat match goal with |- _ /\ _ => split end;
match goal with
| |- mrel _ _ => exact (f_equal st_metas H)
| |- ?p s = ?p t => pose proof (f_equal p H) as E; cbn in E; exact E
end.
- destruct s as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19], t as [b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19]. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas].
intros (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM). subst. unfold shape_eq. rewrite !erase_unfold. unfold set_metas.
cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. unfold mrel in EM. rewrite EM. reflexivity.
Qed.
Lemma sheq_set_init_done v s t : sheq s t -> sheq (set_init_done v s) (set_init_done v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_init_done. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_mmap_counter v s t : sheq s t -> sheq (set_mmap_counter v s) (set_mmap_counter v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_mmap_counter. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_free_meta_head v s t : sheq s t -> sheq (set_free_meta_head v s) (set_free_meta_head v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_free_meta_head. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta v s t : sheq s t -> sheq (set_avail_meta v s) (set_avail_meta v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_avail_meta. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_count v s t : sheq s t -> sheq (set_avail_meta_count v s) (set_avail_meta_count v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_avail_meta_count. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_area_count v s t : sheq s t -> sheq (set_avail_meta_area_count v s) (set_avail_meta_area_count v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_avail_meta_area_count. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_meta_alloc_shift v s t : sheq s t -> sheq (set_meta_alloc_shift v s) (set_meta_alloc_shift v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_meta_alloc_shift. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_area_head v s t : sheq s t -> sheq (set_area_head v s) (set_area_head v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_area_head. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_area_tail v s t : sheq s t -> sheq (set_area_tail v s) (set_area_tail v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_area_tail. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_avail_meta_areas v s t : sheq s t -> sheq (set_avail_meta_areas v s) (set_avail_meta_areas v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_avail_meta_areas. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_active v s t : sheq s t -> sheq (set_active v s) (set_active v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_active. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_usage v s t : sheq s t -> sheq (set_usage v s) (set_usage v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_usage. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_unmap_seq v s t : sheq s t -> sheq (set_unmap_seq v s) (set_unmap_seq v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_unmap_seq. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_bounces v s t : sheq s t -> sheq (set_bounces v s) (set_bounces v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_bounces. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_seq v s t : sheq s t -> sheq (set_seq v s) (set_seq v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_seq. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_brk v s t : sheq s t -> sheq (set_brk v s) (set_brk v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_brk. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_regions v s t : sheq s t -> sheq (set_regions v s) (set_regions v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_regions. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma sheq_set_areas v s t : sheq s t -> sheq (set_areas v s) (set_areas v t).
Proof.
intros [H ND]. split; [|exact ND]. apply sq_fields in H. apply (proj2 (sq_fields _ _)).
unfold set_areas. cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma mrel_mupdate ms mt p x x' :
mrel ms mt -> erase_meta x = erase_meta x' -> mrel (mupdate ms p x) (mupdate mt p x').
Proof.
unfold mrel. revert mt. induction ms as [|[q y] ms IH]; intros [|[q' y'] mt] H Ex; cbn [mupdate map] in *; try discriminate.
- unfold ef. cbn [fst snd]. rewrite Ex. reflexivity.
- unfold ef in H at 1 3. cbn [fst snd] in H. injection H as Eq Ey Et. subst q'. destruct (sptr_eqb p q); cbn [map].
+ unfold ef at 1 3. cbn [fst snd]. rewrite Ex, Et. reflexivity.
+ unfold ef at 1 3. cbn [fst snd]. rewrite Ey. f_equal. apply IH; assumption.
Qed.
Definition orel (o o' : option mslot) : Prop :=
match o, o' with
| None, None => True
| Some x, Some x' => erase_meta x = erase_meta x'
| _, _ => False
end.
Lemma mrel_mlookup ms mt p : mrel ms mt -> orel (mlookup ms p) (mlookup mt p).
Proof.
unfold mrel. revert mt. induction ms as [|[q y] ms IH]; intros [|[q' y'] mt] H; cbn [mlookup map] in *; try discriminate; [exact I|].
unfold ef in H at 1 3. cbn [fst snd] in H. injection H as Eq Ey Et. subst q'. destruct (sptr_eqb p q); [exact Ey|]. apply IH. exact Et.
Qed.
Lemma sheq_MT s t p : sheq s t -> orel (MT s p) (MT t p).
Proof. intros H. unfold MT. apply mrel_mlookup. apply sheq_metas, H. Qed.
Lemma erase_meta_inv x x' :
erase_meta x = erase_meta x' ->
match x with
| MUsed am =>
exists sl', x' = MUsed (mkAMeta (am_prev am) (am_next am) (am_mem am) (am_avail am) (am_freed am)
(am_last am) (am_sc am) (am_maplen am) (am_aidx am) sl') /\
map erase_slot (am_slots am) = map erase_slot sl'
| _ => x' = x
end.
Proof.
destruct x as [pr nx| |am], x' as [pr' nx'| |am']; cbn; intros E; try discriminate; try congruence.
destruct am, am'. cbn in E |- *. injection E as -> -> -> -> -> -> -> -> -> Esl. eexists. split; [reflexivity | exact Esl].
Qed.
Lemma erase_am_mk pr nx mem av frd la sc ml ai sl sl' :
map erase_slot sl = map erase_slot sl' ->
erase_meta (MUsed (mkAMeta pr nx mem av frd la sc ml ai sl)) = erase_meta (MUsed (mkAMeta pr nx mem av frd la sc ml ai sl')).
Proof. intros H. cbn. rewrite H. reflexivity. Qed.
Lemma links_of_erase x x' : erase_meta x = erase_meta x' -> links_of x' = links_of x.
Proof. intros E. apply erase_meta_inv in E. destruct x; subst; try reflexivity. destruct E as (sl' & -> & _). destruct m; reflexivity. Qed.
Lemma with_links_erase x x' pr nx :
erase_meta x = erase_meta x' -> erase_meta (with_links x pr nx) = erase_meta (with_links x' pr nx).
Proof. intros E. pose proof (erase_meta_inv _ _ E) as E'. destruct x; subst; try reflexivity. destruct E' as (sl' & -> & Es). destruct m. cbn in Es |- *. rewrite Es. reflexivity. Qed.
Lemma cons_inj {T} (a b : T) (l m : list T) : a :: l = b :: m -> a = b /\ l = m.
Proof. intros H. injection H as -> ->. split; reflexivity. Qed.
Lemma map_erase_nth sl sl' i :
map erase_slot sl = map erase_slot sl' -> erase_slot (nth i sl slot_junk) = erase_slot (nth i sl' slot_junk).
Proof.
revert sl' i. induction sl as [|x sl IH]; intros [|x' sl'] i H; cbn [map] in H; try discriminate; [reflexivity|].
apply cons_inj in H as [Ex Et]. destruct i; cbn [nth]; [exact Ex | apply IH; exact Et].
Qed.
Lemma map_erase_lupd sl sl' i x x' :
map erase_slot sl = map erase_slot sl' -> erase_slot x = erase_slot x' ->
map erase_slot (lupd sl i x) = map erase_slot (lupd sl' i x').
Proof.
revert sl' i. induction sl as [|y sl IH]; intros [|y' sl'] i H Ex; cbn [map] in H; try discriminate; [reflexivity|].
apply cons_inj in H as [Ey Et]. destruct i; cbn [lupd map]; [congruence|]. rewrite Ey. f_equal. apply IH; assumption.
Qed.
Lemma map_erase_length sl sl' : map erase_slot sl = map erase_slot sl' -> length sl' = length sl.
Proof. intros H. rewrite <- (length_map erase_slot sl), <- (length_map erase_slot sl'), H. reflexivity. Qed.
Lemma erase_slot_inv x x' :
erase_slot x = erase_slot x' ->
(ss_hdr x = None <-> ss_hdr x' = None) /\
match ss_fr x, ss_fr x' with
| None, None => True
| Some fr, Some fr' => fr_n fr' = fr_n fr /\ fr_kind fr' = fr_kind fr /\ (fr_kind fr = FGroup -> fr_off fr' = fr_off fr)
| _, _ => False
end.
Proof.
destruct x as [h f], x' as [h' f']. unfold erase_slot. cbn [ss_hdr ss_fr]. intros E. injection E as Eh Ef. split.
- destruct h, h'; split; intros; congruence.
- destruct f as [fr|], f' as [fr'|]; try discriminate; [|exact I]. injection Ef as Eo En Ek.
split; [congruence|]. split; [congruence|]. intros K. rewrite K in Eo. rewrite <- Ek, K in Eo. congruence.
Qed.
Lemma erase_slot_rehdr x x' f :
erase_slot x = erase_slot x' -> erase_slot (mkSlot (ss_hdr x) f) = erase_slot (mkSlot (ss_hdr x') f).
Proof. intros E. unfold erase_slot in *. cbn [ss_hdr ss_fr] in *. injection E as Eh Ef. rewrite Eh. reflexivity. Qed.
Lemma map_erase_nth_slot pr nx mem av frd la sc ml ai sl pr' nx' mem' av' frd' la' sc' ml' ai' sl' i :
map erase_slot sl = map erase_slot sl' ->
erase_slot (nth_slot (mkAMeta pr nx mem av frd la sc ml ai sl) i) =
erase_slot (nth_slot (mkAMeta pr' nx' mem' av' frd' la' sc' ml' ai' sl') i).
Proof. intros H. unfold nth_slot. cbn [am_slots]. apply map_erase_nth. exact H. Qed.
Lemma sheq_set_metas s t p x x' :
sheq s t -> erase_meta x = erase_meta x' ->
sheq (set_metas (mupdate (st_metas s) p x) s) (set_metas (mupdate (st_metas t) p x') t).
Proof.
intros [H ND] Ex. split.
- pose proof (mrel_mupdate _ _ p x x' (sq_metas _ _ H) Ex) as M.
apply sq_fields in H. apply (proj2 (sq_fields _ _)). unfold set_metas.
cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas]. destruct H as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & EM).
repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
- unfold keys. cbn [st_metas set_metas]. apply NoDup_keys_mupdate. exact ND.
Qed.
Create HintDb sheq.
Hint Resolve sheq_set_init_done sheq_set_mmap_counter sheq_set_free_meta_head sheq_set_avail_meta
sheq_set_avail_meta_count sheq_set_avail_meta_area_count sheq_set_meta_alloc_shift sheq_set_area_head
sheq_set_area_tail sheq_set_avail_meta_areas sheq_set_active sheq_set_usage sheq_set_unmap_seq
sheq_set_bounces sheq_set_seq sheq_set_brk sheq_set_regions sheq_set_areas sheq_set_metas : sheq.
Definition stride_flds (la ml sc : Z) : Z := if (la =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else class_size sc.
Lemma stride_of_mk pr nx mem av frd la sc ml ai sl :
stride_of (mkAMeta pr nx mem av frd la sc ml ai sl) = stride_flds la ml sc.
Proof. reflexivity. Qed.
Ltac amsimp := cbn [am_set_slots am_set_avail am_set_freed am_set_aidx am_set_links am_set_prev am_set_next upd_slot
am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_slots]; rewrite ?stride_of_mk.
Ltac eam :=
amsimp;
first [ reflexivity | assumption
| apply erase_am_mk;
first [ assumption
| apply map_erase_lupd;
first [ assumption | reflexivity
| apply erase_slot_rehdr; first [assumption | apply map_erase_nth_slot; assumption | apply map_erase_nth; assumption] ] ]
| apply with_links_erase; assumption
| congruence ].
Hint Extern 1 (erase_meta _ = erase_meta _) => eam : sheq.
Ltac sheq_tac :=
match goal with H : sheq ?s ?t |- _ => shrwg H; solve [eauto 20 with sheq] end.
Definition eqr {A} (r r' : A * astate) : Prop := fst r = fst r' /\ sheq (snd r) (snd r').
Definition amr (p : sptr) (s t : astate) (r r' : ameta * astate) : Prop :=
exists pr nx mem av frd la sc ml ai sl sl',
fst r = mkAMeta pr nx mem av frd la sc ml ai sl /\ fst r' = mkAMeta pr nx mem av frd la sc ml ai sl' /\
map erase_slot sl = map erase_slot sl' /\
MT s p = Some (MUsed (fst r)) /\ MT t p = Some (MUsed (fst r')) /\ snd r = s /\ snd r' = t.
Section j.
Context {A : Type}.
Implicit Types (s t : astate).
Lemma rsim_ret_eq (a : A) s t : sheq s t -> rsim eqr (ret a s) (ret a t).
Proof. intros H. apply rsim_ret. split; [reflexivity | exact H]. Qed.
Lemma rsim_get_eq s t : rsim (fun r r' => r = (s, s) /\ r' = (t, t)) (get s) (get t).
Proof. apply rsim_get. split; reflexivity. Qed.
Lemma rsim_modify_eq f f' s t : sheq (f s) (f' t) -> rsim eqr (modify f s) (modify f' t).
Proof. intros H. apply rsim_modify. split; [reflexivity | exact H]. Qed.
Lemma rsim_put_eq s1 t1 s t : sheq s1 t1 -> rsim eqr (put s1 s) (put t1 t).
Proof. intros H. apply rsim_put. split; [reflexivity | exact H]. Qed.
Lemma rsim_ask_eq q s t : sheq s t -> is_junk q = false -> rsim eqr (ask q s) (ask q t).
Proof. intros H J. apply rsim_ask; [exact J|]. intros b. split; [reflexivity | exact H]. Qed.
End j.
Definition chk (b b' : bool) (s t : astate) (r r' : unit * astate) : Prop :=
b = true /\ b' = true /\ snd r = s /\ snd r' = t.
Lemma rsim_massert_chk b b' i i' s t : rsim (chk b b' s t) (massert b i s) (massert b' i' t).
Proof. apply rsim_massert. intros B B'. split; [exact B|]. split; [exact B'|]. split; reflexivity. Qed.
Lemma rsim_mcheck_chk b b' i i' s t : rsim (chk b b' s t) (mcheck b i s) (mcheck b' i' t).
Proof. apply rsim_mcheck. intros B B'. split; [exact B|]. split; [exact B'|]. split; reflexivity. Qed.
Lemma rsim_getm p s t : sheq s t -> rsim (amr p s t) (getm p s) (getm p t).
Proof.
intros H. unfold getm. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
destruct (mlookup (st_metas s) p) as [x|] eqn:Ms, (mlookup (st_metas t) p) as [x'|] eqn:Mt; cbn in OR; try contradiction; [|apply rsim_ifail_l].
pose proof (erase_meta_inv _ _ OR) as INV. destruct x as [pr0 nx0| |am]; [subst x'; apply rsim_ifail_l .. |].
destruct INV as (sl' & -> & ES). apply rsim_ret. destruct am as [pr nx mem av frd la sc ml ai sl]. cbn in ES.
exists pr, nx, mem, av, frd, la, sc, ml, ai, sl, sl'. unfold MT. cbn [fst snd].
repeat match goal with |- _ /\ _ => split end; first [reflexivity | exact ES | exact Ms | exact Mt].
Qed.
Lemma rsim_setm p am am' s t :
sheq s t -> erase_meta (MUsed am) = erase_meta (MUsed am') -> rsim eqr (setm p am s) (setm p am' t).
Proof. intros H E. unfold setm. apply rsim_modify_eq. apply sheq_set_metas; assumption. Qed.
Lemma rsim_setslot p x x' s t :
sheq s t -> erase_meta x = erase_meta x' -> rsim eqr (setslot p x s) (setslot p x' t).
Proof. intros H E. unfold setslot. apply rsim_modify_eq. apply sheq_set_metas; assumption. Qed.
Lemma rsim_get_links p s t : sheq s t -> rsim eqr (get_links p s) (get_links p t).
Proof.
intros H. unfold get_links. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
destruct (mlookup (st_metas s) p) as [x|], (mlookup (st_metas t) p) as [x'|]; cbn in OR; try contradiction; [|apply rsim_ifail_l].
apply rsim_ret. split; [cbn [fst]; symmetry; apply links_of_erase; exact OR | exact H].
Qed.
Lemma rsim_set_links p pr nx s t : sheq s t -> rsim eqr (set_links p pr nx s) (set_links p pr nx t).
Proof.
intros H. unfold set_links. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
pose proof (sheq_MT s t p H) as OR. unfold MT in OR.
destruct (mlookup (st_metas s) p) as [x|], (mlookup (st_metas t) p) as [x'|]; cbn in OR; try contradiction; [|apply rsim_ifail_l].
apply rsim_setslot; [exact H|]. apply with_links_erase. exact OR.
Qed.
Lemma rsim_set_prev p pr s t : sheq s t -> rsim eqr (set_prev p pr s) (set_prev p pr t).
Proof.
intros H. unfold set_prev. eapply rsim_bind; [apply rsim_get_links; exact H|].
intros l s1 l' t1 [E HS]; cbn [fst snd] in E, HS; subst l'. apply rsim_set_links. exact HS.
Qed.
Lemma rsim_set_next p nx s t : sheq s t -> rsim eqr (set_next p nx s) (set_next p nx t).
Proof.
intros H. unfold set_next. eapply rsim_bind; [apply rsim_get_links; exact H|].
intros l s1 l' t1 [E HS]; cbn [fst snd] in E, HS; subst l'. apply rsim_set_links. exact HS.
Qed.
Lemma rsim_get_head h s t : sheq s t -> rsim eqr (get_head h s) (get_head h t).
Proof.
intros H. unfold get_head. eapply rsim_bind; [apply rsim_get_eq|]. intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->.
destruct h; apply rsim_ret; (split; [cbn [fst]; shrwg H; reflexivity | exact H]).
Qed.
Lemma rsim_set_head h v s t : sheq s t -> rsim eqr (set_head h v s) (set_head h v t).
Proof. intros H. unfold set_head. destruct h; apply rsim_modify_eq; shrwg H; auto with sheq. Qed.
Ltac shall := repeat match goal with H : sheq _ _ |- _ => progress (shrwg H) end.
Create HintDb rsim.
Ltac rhead :=
lazymatch goal with
| |- rsim _ (get _) (get _) => apply rsim_get_eq
| |- rsim _ (ret _ _) (ret _ _) => apply rsim_ret_eq; assumption
| |- rsim _ (modify _ _) (modify _ _) => apply rsim_modify_eq; sheq_tac
| |- rsim _ (put _ _) (put _ _) => apply rsim_put_eq; sheq_tac
| |- rsim _ (getm _ _) (getm _ _) => apply rsim_getm; assumption
| |- rsim _ (setm _ _ _) (setm _ _ _) => apply rsim_setm; [assumption | eam]
| |- rsim _ (setslot _ _ _) (setslot _ _ _) => apply rsim_setslot; [assumption | eam]
| |- rsim _ (get_links _ _) (get_links _ _) => apply rsim_get_links; assumption
| |- rsim _ (set_links _ _ _ _) (set_links _ _ _ _) => apply rsim_set_links; assumption
| |- rsim _ (set_prev _ _ _) (set_prev _ _ _) => apply rsim_set_prev; assumption
| |- rsim _ (set_next _ _ _) (set_next _ _ _) => apply rsim_set_next; assumption
| |- rsim _ (get_head _ _) (get_head _ _) => apply rsim_get_head; assumption
| |- rsim _ (set_head _ _ _) (set_head _ _ _) => apply rsim_set_head; assumption
| |- rsim _ (massert _ _ _) (massert _ _ _) => apply rsim_massert_chk
| |- rsim _ (mcheck _ _ _) (mcheck _ _ _) => apply rsim_mcheck_chk
| |- rsim _ (ask _ _) (ask _ _) => apply rsim_ask_eq; [assumption | reflexivity]
| |- rsim _ (fail _ _) _ => apply rsim_ifail_l
| |- rsim _ _ (fail _ _) => apply rsim_ifail_r
| |- rsim _ _ _ => solve [eauto 3 with rsim nocore]
end.
Ltac rintro :=
let a := fresh "a" in let s1 := fresh "s" in let a' := fresh "a'" in let t1 := fresh "t" in
let HR := fresh "HR" in
intros a s1 a' t1 HR; cbn beta in HR;
lazymatch type of HR with
| eqr _ _ =>
let E := fresh "E" in let HS := fresh "HS" in
destruct HR as [E HS]; cbn [fst snd] in E, HS; subst a'
| chk _ _ _ _ _ _ =>
let B1 := fresh "CHK" in let B2 := fresh "CHK'" in let E1 := fresh "E" in let E2 := fresh "E" in
destruct HR as (B1 & B2 & E1 & E2); cbn [fst snd] in E1, E2; subst s1 t1; destruct a, a'
| _ = _ /\ _ = _ =>
let E1 := fresh "E" in let E2 := fresh "E" in
destruct HR as [E1 E2]; injection E1 as -> ->; injection E2 as -> ->
| amr _ _ _ _ _ =>
let pr := fresh "pr" in let nx := fresh "nx" in let mem := fresh "mem" in let av := fresh "av" in
let frd := fresh "frd" in let la := fresh "la" in let sc := fresh "sc" in let ml := fresh "ml" in
let ai := fresh "ai" in let sl := fresh "sl" in let sl' := fresh "sl'" in
let E1 := fresh "E" in let E2 := fresh "E" in let ES := fresh "ES" in
let M1 := fresh "Ms" in let M2 := fresh "Mt" in let E3 := fresh "E" in let E4 := fresh "E" in
destruct HR as (pr & nx & mem & av & frd & la & sc & ml & ai & sl & sl' & E1 & E2 & ES & M1 & M2 & E3 & E4);
cbn [fst snd] in E1, E2, M1, M2, E3, E4; subst a a' s1 t1
| _ => idtac
end; cbn beta iota zeta delta [fst snd].
Ltac rauto :=
shall; amsimp;
first
[ lazymatch goal with
| |- rsim _ (bind _ _ _) (bind _ _ _) => eapply rsim_bind; [solve [rauto] | rintro; rauto]
| |- rsim _ (match ?x with _ => _ end _) (match ?x with _ => _ end _) => destruct x eqn:?; rauto
| |- rsim _ (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x eqn:?; rauto
| |- rsim _ _ _ => rhead
end
| idtac ].
Ltac rstep := shall; amsimp; eapply rsim_bind; [rhead | rintro].
Ltac rbind tac := shall; amsimp; eapply rsim_bind; [tac | rintro].
Ltac rcase :=
shall; amsimp;
lazymatch goal with
| |- rsim _ (match ?x with _ => _ end _) _ => destruct x eqn:?
| |- rsim _ (match ?x with _ => _ end) _ => destruct x eqn:?
end.
Lemma rsim_queue h m s t : sheq s t -> rsim eqr (queue h m s) (queue h m t).
Proof. intros H. unfold queue. rauto. Qed.
Global Hint Resolve rsim_queue : rsim.
Lemma rsim_dequeue h m s t : sheq s t -> rsim eqr (dequeue h m s) (dequeue h m t).
Proof. intros H. unfold dequeue. rauto. Qed.
Global Hint Resolve rsim_dequeue : rsim.
Lemma rsim_dequeue_head h s t : sheq s t -> rsim eqr (dequeue_head h s) (dequeue_head h t).
Proof. intros H. unfold dequeue_head. rauto. Qed.
Global Hint Resolve rsim_dequeue_head : rsim.
Lemma rsim_free_meta m s t : sheq s t -> rsim eqr (free_meta m s) (free_meta m t).
Proof. intros H. unfold free_meta. rauto. Qed.
Global Hint Resolve rsim_free_meta : rsim.
Lemma rsim_set_usage_of sc v s t : sheq s t -> rsim eqr (set_usage_of sc v s) (set_usage_of sc v t).
Proof. intros H. unfold set_usage_of. rauto. Qed.
Global Hint Resolve rsim_set_usage_of : rsim.
Lemma rsim_step_seq s t : sheq s t -> rsim eqr (step_seq s) (step_seq t).
Proof. intros H. unfold step_seq. apply rsim_modify_eq. shrwg H. destruct (st_seq s =? 255); auto with sheq. Qed.
Global Hint Resolve rsim_step_seq : rsim.
Lemma rsim_record_seq sc s t : sheq s t -> rsim eqr (record_seq sc s) (record_seq sc t).
Proof. intros H. unfold record_seq. destruct (bounce_idx sc); rauto. Qed.
Global Hint Resolve rsim_record_seq : rsim.
Lemma rsim_account_bounce sc s t : sheq s t -> rsim eqr (account_bounce sc s) (account_bounce sc t).
Proof.
intros H. unfold account_bounce. destruct (bounce_idx sc); [|rauto].
apply rsim_modify_eq. shrwg H. destruct (negb _ && _); auto with sheq.
Qed.
Global Hint Resolve rsim_account_bounce : rsim.
Lemma rsim_decay_bounces sc s t : sheq s t -> rsim eqr (decay_bounces sc s) (decay_bounces sc t).
Proof.
intros H. unfold decay_bounces. destruct (bounce_idx sc); [|rauto].
apply rsim_modify_eq. shrwg H. destruct (_ =? 0); auto with sheq.
Qed.
Global Hint Resolve rsim_decay_bounces : rsim.
Lemma rsim_new_region k len s t : sheq s t -> rsim eqr (new_region k len s) (new_region k len t).
Proof. intros H. unfold new_region. rauto. Qed.
Global Hint Resolve rsim_new_region : rsim.
Lemma rsim_upd_region r f s t : sheq s t -> rsim eqr (upd_region r f s) (upd_region r f t).
Proof. intros H. unfold upd_region. rauto. Qed.
Global Hint Resolve rsim_upd_region : rsim.
Lemma rsim_area_from_brk s t : sheq s t -> rsim eqr (area_from_brk s) (area_from_brk t).
Proof. intros H. unfold area_from_brk. rauto. Qed.
Global Hint Resolve rsim_area_from_brk : rsim.
Lemma rsim_area_from_mmap s t : sheq s t -> rsim eqr (area_from_mmap s) (area_from_mmap t).
Proof. intros H. unfold area_from_mmap. rauto. Qed.
Global Hint Resolve rsim_area_from_mmap : rsim.
Lemma rsim_open_area nu s t : sheq s t -> rsim eqr (open_area nu s) (open_area nu t).
Proof. intros H. unfold open_area. rauto. Qed.
Global Hint Resolve rsim_open_area : rsim.
Lemma rsim_alloc_meta s t : sheq s t -> rsim eqr (alloc_meta s) (alloc_meta t).
Proof. intros H. unfold alloc_meta. rauto. Qed.
Global Hint Resolve rsim_alloc_meta : rsim.
Lemma rsim_activate_group m s t : sheq s t -> rsim eqr (activate_group m s) (activate_group m t).
Proof. intros H. unfold activate_group. rauto. Qed.
Global Hint Resolve rsim_activate_group : rsim.
Lemma rsim_install_group m sc cnt aidx maplen mem sl s t :
sheq s t -> rsim eqr (install_group m sc cnt aidx maplen mem sl s) (install_group m sc cnt aidx maplen mem sl t).
Proof. intros H. unfold install_group. rauto. Qed.
Global Hint Resolve rsim_install_group : rsim.
Lemma rsim_forget_frame g i s t : sheq s t -> rsim eqr (forget_frame g i s) (forget_frame g i t).
Proof. intros H. unfold forget_frame. rauto. Qed.
Global Hint Resolve rsim_forget_frame : rsim.
Lemma rsim_try_avail sc s t : sheq s t -> rsim eqr (try_avail sc s) (try_avail sc t).
Proof. intros H. unfold try_avail. rauto. Qed.
Global Hint Resolve rsim_try_avail : rsim.
Definition enr (g : sptr) (idx n : Z) (k : fkind) (s t : astate) (r r' : sptr * astate) : Prop :=
exists pr nx mem av frd la sc ml ai sl sl' off off' hdr hdr',
let am := mkAMeta pr nx mem av frd la sc ml ai sl in
let am' := mkAMeta pr nx mem av frd la sc ml ai sl' in
MT s g = Some (MUsed am) /\ MT t g = Some (MUsed am') /\
map erase_slot sl = map erase_slot sl' /\ 0 <= idx <= la /\
snd r = set_metas (mupdate (st_metas s) g (MUsed (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n k)))))) s /\
snd r' = set_metas (mupdate (st_metas t) g (MUsed (upd_slot am' idx (mkSlot (Some hdr') (Some (mkFrame off' n k)))))) t /\
fst r = padd (slot_start am idx) (UNIT * off) /\ fst r' = padd (slot_start am idx) (UNIT * off') /\
(k = FGroup -> off = 0 /\ off' = 0) /\
sheq (snd r) (snd r').
Lemma rsim_enframe g idx n ctr k s t :
sheq s t ->
(k = FGroup -> exists am, MT s g = Some (MUsed am) /\ n = stride_of am - IB) ->
rsim (enr g idx n k s t) (enframe g idx n ctr k s) (enframe g idx n ctr k t).
Proof.
intros H HG. unfold enframe. rstep. rstep.
set (am := mkAMeta pr nx mem av frd la sc ml ai sl) in *. set (am' := mkAMeta pr nx mem av frd la sc ml ai sl') in *.
set (slack := (stride_flds la ml sc - IB - n) / UNIT).
assert (EN : erase_slot (nth_slot am idx) = erase_slot (nth_slot am' idx)) by (apply map_erase_nth_slot; exact ES).
apply erase_slot_inv in EN as [EH _].
eapply (rsim_bind (fun r r' => snd r = s /\ snd r' = t /\ (slack = 0 -> fst r = 0 /\ fst r' = 0))).
{ destruct (slack =? 0) eqn:Es0.
- apply rsim_ret. cbn [fst snd]. auto.
- apply Z.eqb_neq in Es0.
destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Eh, (ss_hdr (nth_slot am' idx)) as [[h3' h16']|] eqn:Eh';
[| exfalso; pose proof (proj2 EH eq_refl); congruence | exfalso; pose proof (proj1 EH eq_refl); congruence |].
+ apply rsim_ret. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. intros; lia.
+ eapply (rsim_bind (fun r r' => snd r = s /\ snd r' = t)).
* apply rsim_askz_junk. intros; split; reflexivity.
* intros z s1 z' t1 [E1 E2]. cbn [fst snd] in E1, E2. subst s1 t1. apply rsim_ret. cbn [fst snd].
split; [reflexivity|]. split; [reflexivity|]. intros; lia. }
intros off0 s1 off0' t1 (E1 & E2 & Z0). cbn [fst snd] in E1, E2, Z0. subst s1 t1.
rstep.
unfold bind, setm, modify, ret. cbn [ibind]. apply rsim_iret.
match goal with |- enr _ _ _ _ _ _ (padd _ (UNIT * ?o), _) (padd _ (UNIT * ?o'), _) => set (off := o); set (off' := o') end.
assert (HG0 : k = FGroup -> off = 0 /\ off' = 0).
{ intros Hk. destruct (HG Hk) as (am0 & M0 & En). rewrite Ms in M0. injection M0 as <-. subst am. rewrite stride_of_mk in En.
assert (S0 : slack = 0).
{ subst slack. rewrite En. replace (stride_flds la ml sc - IB - (stride_flds la ml sc - IB)) with 0 by lia. reflexivity. }
destruct (Z0 S0) as [-> ->]. subst off off'. rewrite S0. cbn. split; reflexivity. }
unfold enr. exists pr, nx, mem, av, frd, la, sc, ml, ai, sl, sl', off, off'. eexists. eexists. cbn [fst snd]. fold am am'.
split; [exact Ms|]. split; [exact Mt|]. split; [exact ES|].
split; [apply andb_prop in CHK as [B1 B2]; apply Z.leb_le in B1; apply Z.leb_le in B2; lia|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HG0|].
apply sheq_set_metas; [exact H|]. subst am am'. unfold upd_slot. amsimp. apply erase_am_mk. apply map_erase_lupd; [exact ES|].
destruct k; [reflexivity|]. destruct (HG0 eq_refl) as [-> ->]. reflexivity.
Qed.
Ltac enr_intro HR :=
destruct HR as (?pr & ?nx & ?mem & ?av & ?frd & ?la & ?sc & ?ml & ?ai & ?sl & ?sl' & ?off & ?off' & ?hdr & ?hdr' &
?Ms & ?Mt & ?ES & ?Hidx & ?E1 & ?E2 & ?P1 & ?P2 & ?HG0 & ?HS); cbn [fst snd] in Ms, Mt, E1, E2, P1, P2, HS.
Lemma rsim_alloc_mutual fuel :
(forall sc req s t, sheq s t -> rsim eqr (alloc_slot fuel sc req s) (alloc_slot fuel sc req t)) /\
(forall sc req s t, sheq s t -> rsim eqr (alloc_group fuel sc req s) (alloc_group fuel sc req t)).
Proof.
induction fuel as [|f [IHs IHg]].
{ split; intros; cbn; apply rsim_ifail_l. }
split.
- intros sc req s t H. cbn fix beta iota delta [alloc_slot]. rauto.
- intros sc req s t H. cbn fix beta iota delta [alloc_group]. rauto.
rbind ltac:(apply rsim_enframe; [assumption | intros _; eexists; split; [eassumption | apply Z.eqb_eq in CHK; rewrite <- CHK; reflexivity]]).
enr_intro HR. subst. destruct (HG0 eq_refl) as [-> ->]. rauto.
Qed.
Lemma rsim_alloc_slot fuel sc req s t : sheq s t -> rsim eqr (alloc_slot fuel sc req s) (alloc_slot fuel sc req t).
Proof. apply (proj1 (rsim_alloc_mutual fuel)). Qed.
Global Hint Resolve rsim_alloc_slot : rsim.
Definition mres (n : Z) (r r' : option sptr * astate) : Prop :=
sheq (snd r) (snd r') /\
match fst r, fst r' with
| None, None => True
| Some p, Some p' => exists g idx s0 t0, enr g idx n FUser s0 t0 (p, snd r) (p', snd r')
| _, _ => False
end.
Lemma sq_head_full s t h :
sheq s t ->
match mlookup (st_metas t) h with
| Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
| _ => true
end =
match mlookup (st_metas s) h with
| Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
| _ => true
end.
Proof.
intros H. pose proof (sheq_MT s t h H) as OR. unfold MT in OR.
destruct (mlookup (st_metas s) h) as [x|], (mlookup (st_metas t) h) as [x'|]; cbn in OR; try contradiction; [|reflexivity].
pose proof (erase_meta_inv _ _ OR) as INV. destruct x; [subst x'; reflexivity .. |]. destruct INV as (sl' & -> & _). reflexivity.
Qed.
Lemma enr_sheq g idx n k s t p s1 p' t1 : enr g idx n k s t (p, s1) (p', t1) -> sheq s1 t1.
Proof. intros HR. enr_intro HR. exact HS. Qed.
Ltac mres_leaf :=
apply rsim_ret; split; [ first [assumption | eapply enr_sheq; eassumption] | cbn [fst snd]; first [exact I | do 4 eexists; eassumption] ].
Lemma rsim_malloc n s t : sheq s t -> rsim (mres n) (malloc n s) (malloc n t).
Proof.
intros H. unfold malloc. destruct (size_overflows n); [mres_leaf|].
destruct (MMAP_THRESHOLD <=? n).
-
rauto; try mres_leaf.
rbind ltac:(apply rsim_enframe; [assumption | intros; discriminate]). mres_leaf.
-
rstep. shall. destruct (nth (Z.to_nat (size_to_class n + 1)) (st_active s) None) as [h|];
[rewrite (sq_head_full s t h H)|].
all: match goal with |- rsim _ (bind (match nth (Z.to_nat ?x) _ _ with _ => _ end) _ _) _ => set (sc := x) end.
all: rauto; try mres_leaf.
all: rbind ltac:(apply rsim_enframe; [assumption | intros; discriminate]); mres_leaf.
Qed.
Lemma find_in_slots_ge sl base stride i p k : find_in_slots sl base stride i p = Some k -> i <= k.
Proof.
revert i. induction sl as [|x sl IH]; intros i H; cbn [find_in_slots] in H; [discriminate|].
destruct (ss_fr x) as [fr|]; [destruct (sptr_eqb _ p); [injection H as <-; lia|]|]; apply IH in H; lia.
Qed.
Lemma find_in_slots_rel sl sl' base stride i p :
map erase_slot sl = map erase_slot sl' ->
find_in_slots sl base stride i p = find_in_slots sl' base stride i p
\/ (exists k, find_in_slots sl base stride i p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) sl slot_junk) = false)
\/ (exists k, find_in_slots sl' base stride i p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) sl' slot_junk) = false).
Proof.
revert sl' i. induction sl as [|x sl IH]; intros [|x' sl'] i H; cbn [map] in H; try discriminate; [left; reflexivity|].
apply cons_inj in H as [Ex Et]. pose proof (erase_slot_inv _ _ Ex) as [_ FR]. cbn [find_in_slots].
assert (SH : forall y l k, i + 1 <= k -> nth (Z.to_nat (k - i)) (y :: l) slot_junk = nth (Z.to_nat (k - (i + 1))) l slot_junk).
{ intros y l k Hk. replace (Z.to_nat (k - i)) with (S (Z.to_nat (k - (i + 1)))) by lia. reflexivity. }
assert (REC : find_in_slots sl base stride (i + 1) p = find_in_slots sl' base stride (i + 1) p
\/ (exists k, find_in_slots sl base stride (i + 1) p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) (x :: sl) slot_junk) = false)
\/ (exists k, find_in_slots sl' base stride (i + 1) p = Some k /\ i <= k /\ slot_is_group (nth (Z.to_nat (k - i)) (x' :: sl') slot_junk) = false)).
{ destruct (IH sl' (i + 1) Et) as [E | [(k & Hk & Hik & Hg) | (k & Hk & Hik & Hg)]]; [left; exact E | right; left | right; right];
exists k; rewrite SH by lia; repeat split; auto; lia. }
assert (G0 : forall y : slotst, forall fr, ss_fr y = Some fr -> fr_kind fr = FUser -> slot_is_group (nth (Z.to_nat (i - i)) (y :: sl) slot_junk) = false).
{ intros y fr Hy Hk. rewrite Z.sub_diag. cbn [Z.to_nat nth]. unfold slot_is_group. rewrite Hy, Hk. reflexivity. }
assert (G0' : forall y : slotst, forall fr, ss_fr y = Some fr -> fr_kind fr = FUser -> slot_is_group (nth (Z.to_nat (i - i)) (y :: sl') slot_junk) = false).
{ intros y fr Hy Hk. rewrite Z.sub_diag. cbn [Z.to_nat nth]. unfold slot_is_group. rewrite Hy, Hk. reflexivity. }
destruct (ss_fr x) as [fr|] eqn:Fx, (ss_fr x') as [fr'|] eqn:Fx'; try contradiction; [|exact REC].
destruct FR as (En & Ek & Eo).
destruct (fr_kind fr) eqn:K.
-
destruct (sptr_eqb (padd base (stride * i + UNIT * fr_off fr)) p).
+ right; left. exists i. split; [reflexivity|]. split; [lia|]. eapply G0; [exact Fx | exact K].
+ destruct (sptr_eqb (padd base (stride * i + UNIT * fr_off fr')) p).
* right; right. exists i. split; [reflexivity|]. split; [lia|]. eapply G0'; [exact Fx' | exact Ek].
* exact REC.
-
rewrite (Eo eq_refl). destruct (sptr_eqb _ p); [left; reflexivity | exact REC].
Qed.
Lemma find_frame_in_rel ms mt p :
mrel ms mt ->
find_frame_in ms p = find_frame_in mt p
\/ (exists m k am, find_frame_in ms p = Some (m, k) /\ In (m, MUsed am) ms /\ slot_is_group (nth_slot am k) = false)
\/ (exists m k am', find_frame_in mt p = Some (m, k) /\ In (m, MUsed am') mt /\ slot_is_group (nth_slot am' k) = false).
Proof.
unfold mrel. revert mt. induction ms as [|[q x] ms IH]; intros [|[q' x'] mt] H; cbn [map] in H; try discriminate; [left; reflexivity|].
apply cons_inj in H as [Eqx Et]. unfold ef in Eqx. cbn [fst snd] in Eqx. injection Eqx as Eq Ex. subst q'.
assert (REC : find_frame_in ms p = find_frame_in mt p
\/ (exists m k am, find_frame_in ms p = Some (m, k) /\ In (m, MUsed am) ((q, x) :: ms) /\ slot_is_group (nth_slot am k) = false)
\/ (exists m k am', find_frame_in mt p = Some (m, k) /\ In (m, MUsed am') ((q, x') :: mt) /\ slot_is_group (nth_slot am' k) = false)).
{ destruct (IH mt Et) as [E | [(m & k & am & Hf & Hin & Hg) | (m & k & am & Hf & Hin & Hg)]]; [left; exact E | right; left | right; right];
exists m, k, am; repeat split; auto; right; exact Hin. }
pose proof (erase_meta_inv _ _ Ex) as INV. cbn [find_frame_in].
destruct x as [pr0 nx0| |am]; [subst x'; exact REC .. |]. destruct INV as (sl' & -> & ES).
destruct am as [pr nx mem av frd la sc ml ai sl]. unfold stride_of. cbn [am_slots am_mem am_prev am_next am_avail am_freed am_last am_sc am_maplen am_aidx] in ES |- *.
match goal with |- context [find_in_slots sl ?b ?st 0 p] =>
destruct (find_in_slots_rel sl sl' b st 0 p ES) as [E | [(k & Hk & _ & Hg) | (k & Hk & _ & Hg)]] end.
- rewrite E. destruct (find_in_slots sl' _ _ 0 p); [left; reflexivity | exact REC].
- right; left. rewrite Hk. eexists q, k, _. split; [reflexivity|]. split; [left; reflexivity|]. unfold nth_slot. cbn [am_slots]. rewrite Z.sub_0_r in Hg. exact Hg.
- right; right. rewrite Hk. eexists q, k, _. split; [reflexivity|]. split; [left; reflexivity|]. unfold nth_slot. cbn [am_slots]. rewrite Z.sub_0_r in Hg. exact Hg.
Qed.
Definition ffr (s t : astate) (r r' : (sptr * Z) * astate) : Prop :=
snd r = s /\ snd r' = t /\
(fst r = fst r'
\/ (exists am, MT s (fst (fst r)) = Some (MUsed am) /\ slot_is_group (nth_slot am (snd (fst r))) = false)
\/ (exists am', MT t (fst (fst r')) = Some (MUsed am') /\ slot_is_group (nth_slot am' (snd (fst r'))) = false)).
Lemma rsim_find_frame p s t : sheq s t -> rsim (ffr s t) (find_frame p s) (find_frame p t).
Proof.
intros H. unfold find_frame. rstep.
destruct (find_frame_in_rel _ _ p (sheq_metas _ _ H)) as [E | [(m & k & am & Hf & Hin & Hg) | (m & k & am & Hf & Hin & Hg)]].
- rewrite <- E. destruct (find_frame_in (st_metas s) p); [|apply rsim_ifail_l]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|]. left. reflexivity.
- rewrite Hf. destruct (find_frame_in (st_metas t) p); [|apply rsim_ifail_r]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|].
right; left. exists am. cbn [fst snd]. split; [|exact Hg]. unfold MT. apply mlookup_of_In; [exact (sheq_nodup_l _ _ H) | exact Hin].
- rewrite Hf. destruct (find_frame_in (st_metas s) p); [|apply rsim_ifail_l]. apply rsim_ret. split; [reflexivity|]. split; [reflexivity|].
right; right. exists am. cbn [fst snd]. split; [|exact Hg]. unfold MT. apply mlookup_of_In; [exact (sheq_nodup_r _ _ H) | exact Hin].
Qed.
Lemma rsim_parent_check_fail_l {B C} (R : C * astate -> B -> Prop) m k am s (K : unit -> M C) (y : itree astate B) :
MT s m = Some (MUsed am) -> slot_is_group (nth_slot am k) = false ->
rsim R (bind (getm m) (fun amp => bind (mcheck (slot_is_group (nth_slot amp k)) 10) K) s) y.
Proof.
intros Hm Hg. unfold bind at 1. unfold getm, bind, get. cbn [ibind]. unfold MT in Hm. rewrite Hm. cbn [ibind ret].
unfold mcheck. rewrite Hg. cbn. apply rsim_ifail_l.
Qed.
Lemma rsim_parent_check_fail_r {A C} (R : A -> C * astate -> Prop) m k am t (K : unit -> M C) (x : itree astate A) :
MT t m = Some (MUsed am) -> slot_is_group (nth_slot am k) = false ->
rsim R x (bind (getm m) (fun amp => bind (mcheck (slot_is_group (nth_slot amp k)) 10) K) t).
Proof.
intros Hm Hg. unfold bind at 1. unfold getm, bind, get. cbn [ibind]. unfold MT in Hm. rewrite Hm. cbn [ibind ret].
unfold mcheck. rewrite Hg. cbn. apply rsim_ifail_r.
Qed.
Definition hdr_known_at (s : astate) (g : sptr) (i : Z) : Prop :=
forall am fr, MT s g = Some (MUsed am) -> ss_fr (nth_slot am i) = Some fr -> fr_off fr = 0 -> ss_hdr (nth_slot am i) <> None.
Lemma rsim_release_slot g i s t :
sheq s t -> hdr_known_at s g i -> hdr_known_at t g i ->
rsim eqr (release_slot g i s) (release_slot g i t).
Proof.
intros H H0s H0t. unfold release_slot. rstep.
set (am := mkAMeta pr nx mem av frd la sc ml ai sl) in *. set (am' := mkAMeta pr nx mem av frd la sc ml ai sl') in *.
assert (EN : erase_slot (nth_slot am i) = erase_slot (nth_slot am' i)) by (apply map_erase_nth_slot; exact ES).
pose proof (erase_slot_inv _ _ EN) as [EH FR].
apply rsim_setm; [exact H|]. subst am am'. unfold upd_slot. amsimp. apply erase_am_mk. apply map_erase_lupd; [exact ES|].
match goal with |- erase_slot (match ss_fr ?x with _ => _ end) = erase_slot (match ss_fr ?x' with _ => _ end) =>
set (sx := x) in *; set (sx' := x') in * end.
destruct (ss_fr sx) as [fr|] eqn:F, (ss_fr sx') as [fr'|] eqn:F'; try contradiction; [|exact EN].
destruct FR as (En & Ek & Eo).
destruct (fr_off fr =? 0) eqn:O, (fr_off fr' =? 0) eqn:O'.
- reflexivity.
- apply Z.eqb_eq in O. specialize (H0s _ fr Ms F O). destruct (ss_hdr sx') eqn:Eh'; [reflexivity|]. exfalso. apply H0s. apply (proj2 EH). reflexivity.
- apply Z.eqb_eq in O'. specialize (H0t _ fr' Mt F' O'). destruct (ss_hdr sx) eqn:Eh; [reflexivity|]. exfalso. apply H0t. apply (proj1 EH). reflexivity.
- apply erase_slot_rehdr. exact EN.
Qed.
Lemma rsim_nontrivial_free fuel g i s t :
sheq s t -> rsim eqr (nontrivial_free fuel g i s) (nontrivial_free fuel g i t).
Proof.
revert g i s t. induction fuel as [|f IH]; intros g i s t H; [cbn; apply rsim_ifail_l|].
cbn fix beta iota delta [nontrivial_free]. unfold okay_to_free. rauto.
eapply rsim_bind.
{ rcase; [rauto|].
rbind ltac:(apply rsim_find_frame; assumption).
destruct HR as (E1 & E2 & CASES); cbn [fst snd] in E1, E2, CASES; subst.
destruct CASES as [<- | [(am0 & M0 & G0) | (am0 & M0 & G0)]].
- rauto.
- eapply rsim_parent_check_fail_l; eassumption.
- eapply rsim_parent_check_fail_r; eassumption. }
rintro; rauto.
Qed.
Global Hint Resolve rsim_nontrivial_free : rsim.
Lemma rsim_free p p' g i s t :
sheq s t ->
find_frame_in (st_metas s) p = Some (g, i) -> find_frame_in (st_metas t) p' = Some (g, i) ->
hdr_known_at s g i -> hdr_known_at t g i ->
rsim eqr (free (Some p) s) (free (Some p') t).
Proof.
intros H Fs Ft H0s H0t. unfold free.
eapply (rsim_bind (fun r r' => r = ((g, i), s) /\ r' = ((g, i), t))).
{ unfold find_frame. rstep. rewrite Fs, Ft. apply rsim_ret. split; reflexivity. }
intros ? ? ? ? [E1 E2]. injection E1 as -> ->. injection E2 as -> ->. cbn beta iota zeta delta [fst snd].
rstep. rbind ltac:(apply rsim_release_slot; assumption). rauto.
Qed.
