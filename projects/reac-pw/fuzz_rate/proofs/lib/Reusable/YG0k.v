(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0k.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0k.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Definition krefusable (q : kreq) : bool :=
match q with KMapUser _ _ _ | KMapFreeArray _ _ _ | KMmapSec _ => true | _ => false end.
Definition refusal_offered (t : itree astate (sptr * astate)) : Prop :=
exists q snap k, t = IAsk q snap k /\ krefusable q = true /\ aok snap q 0 /\ exists S', k 0 = IRet (PNull, S').
Lemma malloc_refusal_sec : forall n trc S,
from_primary n = false -> n < kMaxAllowedMalloc - kPage -> refusal_offered (malloc n trc S).
Proof.
intros n trc S Hp Hn. unfold refusal_offered, malloc. rewrite Hp.
replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; exact Hn).
unfold bind, tick, mcheck, sec_alloc, bind, askz, modify, ret. cbn [ibind].
eexists. eexists. eexists. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; left; reflexivity|].
eexists. cbn [ibind Z.eqb]. reflexivity.
Qed.
Definition pristine_class (S : astate) (c : Z) : Prop :=
rg_mapped_user (reg S c) = 0 /\ rg_alloc_user (reg S c) = 0 /\ rg_free (reg S c) = [] /\ pc_chunks (cache S c) = [].
Definition prim_pristine_except (S : astate) (cs : list Z) : Prop :=
forall c, 1 <= c <= 31 -> ~ In c cs -> pristine_class S c.
Lemma pristine_init : prim_pristine_except init_state [].
Proof.
intros c Hc _. unfold pristine_class, reg, cache, init_state, znth. cbn [st_regions st_cache].
assert (R : forall i, (i < 32)%nat -> nth i (repeat region0 32) region0 = region0) by (intros i Hi; apply nth_repeat).
assert (P : forall i, (i < 32)%nat -> nth i (repeat pclass0 32) pclass0 = pclass0) by (intros i Hi; apply nth_repeat).
rewrite R, P by lia. cbn. repeat split; reflexivity.
Qed.
Section d.
Variable U : list (list Z).
Lemma malloc_refusal_prim : forall n trc S cs,
Wf U S -> prim_pristine_except S cs ->
0 <= n -> n < kMaxAllowedMalloc - kPage -> from_primary n = true -> ~ In (chunk_class n) cs ->
refusal_offered (malloc n trc S).
Proof.
intros n trc S cs W HP Hn0 Hn Hp Hcs.
pose proof (primary_geometry n Hn0 Hp) as (Hc & _ & Hsz & _ & Hpos).
set (c := chunk_class n) in *.
destruct (HP c ltac:(lia) Hcs) as (M0 & A0 & F0 & C0).
pose proof (wf_len_regions _ _ _ _ _ W) as LR. pose proof (wf_len_cache _ _ _ _ _ W) as LC.
assert (MC : 1 <= max_cached c / 2 <= 8).
{ unfold max_cached. rewrite (Z.mul_comm 2), Z.div_mul by lia. pose proof (Z.div_pos 1024 (class_size c) ltac:(lia) Hpos). lia. }
assert (NS : 1 <= max_cached c / 2 * class_size c <= kUserMapSize).
{ unfold max_cached. rewrite (Z.mul_comm 2), Z.div_mul by lia.
unfold kUserMapSize, kMaxSize in *.
destruct (Z_lt_le_dec 1024 (class_size c)).
- rewrite (Z.div_small 1024 (class_size c)) by lia. change (Z.max 1 (Z.min 8 0)) with 1. lia.
- assert (1 <= 1024 / class_size c) by (apply Z.div_le_lower_bound; lia).
pose proof (Z.mul_div_le 1024 (class_size c) ltac:(lia)). nia. }
unfold refusal_offered, malloc. rewrite Hp.
replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; exact Hn).
unfold cache_alloc, init_cache_if_needed, refill_if_empty.
cbn [bind ret tick modify mcheck ibind get put set_nev set_cache_inited set_cache st_cache_inited].
assert (CORE : forall s2 (cl : list pclass) (F : sptr -> astate -> itree astate (sptr * astate)),
st_regions s2 = st_regions S -> length (st_cache s2) = 32%nat -> st_cache s2 = cl ->
pc_chunks (znth pclass0 c cl) = [] -> pc_max (znth pclass0 c cl) = max_cached c ->
exists (q : kreq) (snap : astate) (k : Z -> itree astate (sptr * astate)),
ibind (ibind (ibind
((match pc_chunks (znth pclass0 c cl) with
| [] => bind (get_from_allocator c (pc_max (znth pclass0 c cl) / 2))
(fun got => match got with
| Some tops => set_pc c (mkPC (pc_max (znth pclass0 c cl)) (cache_fill_order tops))
| None => ret tt end)
| _ :: _ => ret tt end) s2)
(fun '(_, s') => (match pc_chunks (znth pclass0 c (st_cache s')) with
| [] => ret None
| z :: l0 => bind (set_pc c (mkPC (pc_max (znth pclass0 c (st_cache s'))) (removelast (z :: l0))))
(fun _ => ret (Some (region_off c + last (z :: l0) 0)))
end) s'))
(fun '(a, s') => ret (match a with Some off => Some (PPrim off) | None => None end) s'))
(fun '(a, s') => (match a with Some beg => F beg | None => fun s => IRet (PNull, s) end) s') = IAsk q snap k /\
krefusable q = true /\ aok snap q 0 /\ (exists S', k 0 = IRet (PNull, S'))).
{ intros s2 cl F R2 L2 CL C2 X2. rewrite C2, X2.
unfold get_from_allocator, get_region. lazy [bind get ret ibind]. rewrite R2. fold (reg S c). rewrite F0. cbn [fa_len].
replace (0 <? max_cached c / 2) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Z.sub_0_r.
unfold populate, map_more_user, get_region. lazy [bind get ret ibind]. rewrite R2. fold (reg S c). rewrite M0, A0.
replace (0 <? 0 + max_cached c / 2 * class_size c) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Z.sub_0_r.
replace (round_up (0 + max_cached c / 2 * class_size c) kUserMapSize) with kUserMapSize.
2:{ unfold round_up, kUserMapSize in *. replace ((0 + max_cached c / 2 * class_size c + 262144 - 1) / 262144) with 1; [reflexivity|].
apply Z.div_unique with (r := 0 + max_cached c / 2 * class_size c - 1); lia. }
unfold mcheck. replace (0 + kUserMapSize <=? kFreeArrayOffset) with true by reflexivity. unfold askz. lazy [ret bind ibind].
eexists. eexists. eexists. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; left; reflexivity|].
eexists. cbn [aGranted aDestroyed Z.eqb negb ibind]. rewrite CL, C2. cbn [ibind]. reflexivity. }
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c ltac:(lia))) as XC. unfold cache in XC.
destruct (st_cache_inited S) eqn:CI.
-
cbn [ibind get_pc bind get ret st_cache set_nev]. apply CORE; [reflexivity | exact LC | reflexivity | exact C0 | exact (proj1 XC)].
-
cbn [ibind get_pc bind get ret st_cache set_nev set_cache_inited set_cache].
pose proof (cache_after_init S c ltac:(lia)) as X. unfold cache in X. cbn [st_cache set_cache_inited set_cache] in X.
apply CORE; [reflexivity | apply length_init_caches | reflexivity | | ];
cbn [st_cache set_cache_inited set_cache]; rewrite X; [exact C0 | reflexivity].
Qed.
End d.
Definition apost {A : Type} (t : itree astate A) (Q : A -> Prop) : Prop := forall tr a, apath t tr a -> Q a.
Lemma apost_ret {A} : forall (a : A) s (Q : A * astate -> Prop), Q (a, s) -> apost (ret a s) Q.
Proof. intros a s Q H tr r Hy. cbn in Hy. destruct tr; [subst; exact H | destruct Hy]. Qed.
Lemma apost_leaf {A} : forall (a : A) (Q : A -> Prop), Q a -> apost (IRet a) Q.
Proof. intros a Q H tr r Hy. cbn in Hy. destruct tr; [subst; exact H | destruct Hy]. Qed.
Lemma apost_ibind {A B} (t : itree astate A) : forall (k : A -> itree astate B) (Q : B -> Prop),
apost t (fun a => apost (k a) Q) -> apost (ibind t k) Q.
Proof.
induction t as [a | q snap c IH | pc | f]; cbn; intros k Q H tr b Hy.
- apply (H [] a eq_refl tr b Hy).
- destruct tr as [|[q' z] tr']; cbn in Hy; [destruct Hy|]. destruct Hy as (-> & Hz & Hy).
refine (IH z k Q _ tr' b Hy). intros tr1 a Ha. apply (H ((q, z) :: tr1) a). cbn. auto.
- destruct tr; destruct Hy.
- destruct tr; destruct Hy.
Qed.
Lemma apost_mono {A} (t : itree astate A) : forall (Q Q' : A -> Prop), (forall a, Q a -> Q' a) -> apost t Q -> apost t Q'.
Proof. intros Q Q' HQ H tr a Hy. apply HQ. exact (H tr a Hy). Qed.
Section e.
Context {A B : Type}.
Implicit Types (Q : A * astate -> Prop) (s : astate).
Lemma apost_bind (m : M B) (k : B -> M A) s Q :
apost (m s) (fun r => apost (k (fst r) (snd r)) Q) -> apost (bind m k s) Q.
Proof. intros H. unfold bind. apply apost_ibind. eapply apost_mono; [|exact H]. intros [x s'] Hb. exact Hb. Qed.
Lemma apost_fail f s Q : apost (@fail A f s) Q.
Proof. intros tr a Hy. cbn in Hy. destruct tr; destruct Hy. Qed.
Lemma apost_spin pc s Q : apost (@spin A pc s) Q.
Proof. intros tr a Hy. cbn in Hy. destruct tr; destruct Hy. Qed.
Lemma apost_get s (Q : astate * astate -> Prop) : Q (s, s) -> apost (get s) Q.
Proof. intros H. apply apost_leaf. exact H. Qed.
Lemma apost_put s s' (Q : unit * astate -> Prop) : Q (tt, s') -> apost (put s' s) Q.
Proof. intros H. apply apost_leaf. exact H. Qed.
Lemma apost_modify f s (Q : unit * astate -> Prop) : Q (tt, f s) -> apost (modify f s) Q.
Proof. intros H. apply apost_leaf. exact H. Qed.
Lemma apost_askz q s (Q : Z * astate -> Prop) : (forall z, aok s q z -> Q (z, s)) -> apost (askz q s) Q.
Proof.
intros H tr a Hy. cbn in Hy. destruct tr as [|[q' z] tr']; [destruct Hy|]. destruct Hy as (-> & Hz & Hy).
destruct tr'; cbn in Hy; [subst; apply H, Hz | destruct Hy].
Qed.
Lemma apost_mcheck (b : bool) tag s (Q : unit * astate -> Prop) : (b = true -> Q (tt, s)) -> apost (mcheck b tag s) Q.
Proof. intros H. unfold mcheck. destruct b; [apply apost_leaf; apply H; reflexivity | intros tr a Hy; cbn in Hy; destruct tr; destruct Hy]. Qed.
Lemma apost_if (b : bool) (m1 m2 : M A) s Q :
(b = true -> apost (m1 s) Q) -> (b = false -> apost (m2 s) Q) -> apost ((if b then m1 else m2) s) Q.
Proof. intros H1 H2. destruct b; auto. Qed.
Lemma apost_tick s (Q : unit * astate -> Prop) : Q (tt, set_nev (st_nev s + 1) s) -> apost (tick s) Q.
Proof. intros H. apply apost_leaf. exact H. Qed.
End e.
Lemma apost_apath {A} : forall (t : itree astate A) Q tr a, apost t Q -> apath t tr a -> Q a.
Proof. intros t Q tr a H Hy. exact (H tr a Hy). Qed.
Definition quar_bytes (s : astate) : Z := qc_bytes (st_qglobal s) + qc_bytes (st_qthread s).
Definition FRAME (c : Z) (s s' : astate) : Prop :=
(forall c', 1 <= c' <= 31 -> c' <> c -> reg s' c' = reg s c' /\ pc_chunks (cache s' c') = pc_chunks (cache s c')) /\
st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\ length (st_cache s') = length (st_cache s).
Lemma FRAME_refl : forall c s, FRAME c s s.
Proof. intros c s. repeat split; reflexivity. Qed.
Lemma FRAME_trans : forall c s1 s2 s3, FRAME c s1 s2 -> FRAME c s2 s3 -> FRAME c s1 s3.
Proof.
intros c s1 s2 s3 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2). split; [|repeat split; congruence].
intros c' H1 H2. destruct (A1 c' H1 H2) as [X1 Y1]. destruct (A2 c' H1 H2) as [X2 Y2]. split; congruence.
Qed.
Lemma FRAME_upd_reg : forall c r s, 0 <= c -> FRAME c s (upd_reg c r s).
Proof.
intros c r s Hc. split; [|repeat split; reflexivity]. intros c' H1 H2. split; [|reflexivity].
apply reg_upd_reg_other; lia.
Qed.
Lemma FRAME_upd_pc : forall c p s, 0 <= c -> FRAME c s (upd_pc c p s).
Proof.
intros c p s Hc. split.
- intros c' H1 H2. split; [reflexivity|]. unfold cache, upd_pc. cbn [st_cache set_cache]. rewrite znth_zupd_other by lia. reflexivity.
- repeat split; try reflexivity. unfold upd_pc. cbn [st_cache set_cache]. unfold zupd. generalize (Z.to_nat c).
induction (st_cache s) as [|h t IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.
Lemma FRAME_init : forall c s, length (st_cache s) = 32%nat -> FRAME c s (set_cache_inited true (set_cache (init_caches (st_cache s)) s)).
Proof.
intros c s L. split.
- intros c' H1 H2. split; [reflexivity|]. rewrite cache_after_init by lia. reflexivity.
- repeat split; try reflexivity. cbn [st_cache set_cache_inited set_cache]. rewrite length_init_caches, L. reflexivity.
Qed.
Lemma apost_get_region : forall c s (Q : region * astate -> Prop), Q (reg s c, s) -> apost (get_region c s) Q.
Proof. intros c s Q H. unfold get_region. apply apost_bind. apply apost_get. cbn [fst snd]. apply apost_ret. exact H. Qed.
Lemma apost_get_pc : forall c s (Q : pclass * astate -> Prop), Q (cache s c, s) -> apost (get_pc c s) Q.
Proof. intros c s Q H. unfold get_pc. apply apost_bind. apply apost_get. cbn [fst snd]. apply apost_ret. exact H. Qed.
Lemma apost_set_region : forall c r s (Q : unit * astate -> Prop), Q (tt, upd_reg c r s) -> apost (set_region c r s) Q.
Proof. intros c r s Q H. unfold set_region. apply apost_modify. exact H. Qed.
Lemma apost_set_pc : forall c p s (Q : unit * astate -> Prop), Q (tt, upd_pc c p s) -> apost (set_pc c p s) Q.
Proof. intros c p s Q H. unfold set_pc. apply apost_modify. exact H. Qed.
Section g.
Implicit Types (s : astate) (c : Z).
Lemma ensure_free_array_frame : forall c need b s, 0 <= c -> apost (ensure_free_array c need b s) (fun r => FRAME c s (snd r)).
Proof.
intros c need b s Hc. unfold ensure_free_array.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; apply FRAME_refl|].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _.
- apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. cbn [snd]. apply FRAME_upd_reg. exact Hc.
- apply apost_bind.
apply apost_if; intros _; [apply apost_set_region | apply apost_ret]; cbn [fst snd];
(apply apost_if; intros _; [apply apost_spin | apply apost_ret]); cbn [snd]; try (apply FRAME_upd_reg; exact Hc); apply FRAME_refl.
Qed.
Lemma map_more_user_frame : forall c need s, 0 <= c -> apost (map_more_user c need s) (fun r => FRAME c s (snd r)).
Proof.
intros c need s Hc. unfold map_more_user.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_if; intros _; [|apply apost_ret; apply FRAME_refl].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _.
- apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. cbn [snd]. apply FRAME_upd_reg. exact Hc.
- apply apost_bind. apply apost_if; intros _; [apply apost_set_region | apply apost_ret]; cbn [fst snd]; apply apost_ret; cbn [snd];
[apply FRAME_upd_reg; exact Hc | apply FRAME_refl].
Qed.
Lemma populate_frame : forall c need s, 0 <= c -> apost (populate c need s) (fun r => FRAME c s (snd r)).
Proof.
intros c need s Hc. unfold populate.
apply apost_bind. eapply apost_mono; [|apply map_more_user_frame; exact Hc]. intros [ok s1] F1. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact F1|].
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_bind. eapply apost_mono; [|apply ensure_free_array_frame; exact Hc]. intros [ok2 s2] F2. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact (FRAME_trans _ _ _ _ F1 F2)|].
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. cbn [snd].
eapply FRAME_trans; [exact (FRAME_trans _ _ _ _ F1 F2) | apply FRAME_upd_reg; exact Hc].
Qed.
Lemma get_from_allocator_frame : forall c n s, 0 <= c -> apost (get_from_allocator c n s) (fun r => FRAME c s (snd r)).
Proof.
intros c n s Hc. unfold get_from_allocator.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_bind.
assert (P : apost ((if fa_len (rg_free (reg s c)) <? n then populate c (n - fa_len (rg_free (reg s c))) else ret true) s) (fun r => FRAME c s (snd r))).
{ apply apost_if; intros _; [apply populate_frame; exact Hc | apply apost_ret; apply FRAME_refl]. }
eapply apost_mono; [|exact P]. intros [ok s1] F1. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact F1|].
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact F1|].
destruct (fa_pop_n _ _ _ _ _) as [[tops rest]|]; [|apply apost_fail].
apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. cbn [snd]. eapply FRAME_trans; [exact F1 | apply FRAME_upd_reg; exact Hc].
Qed.
Lemma cache_alloc_frame : forall c s, 0 <= c -> length (st_cache s) = 32%nat -> apost (cache_alloc c s) (fun r => FRAME c s (snd r)).
Proof.
intros c s Hc L. unfold cache_alloc, init_cache_if_needed, refill_if_empty.
apply apost_bind. apply apost_bind. apply apost_get. cbn [fst snd].
assert (I : apost ((if st_cache_inited s then ret tt else put (set_cache_inited true (set_cache (init_caches (st_cache s)) s))) s)
(fun r => FRAME c s (snd r))).
{ apply apost_if; intros _; [apply apost_ret; apply FRAME_refl | apply apost_put; apply FRAME_init; exact L]. }
eapply apost_mono; [|exact I]. intros [[] s1] F1. cbn [fst snd].
apply apost_bind. apply apost_bind. apply apost_get_pc. cbn [fst snd]. unfold cache.
assert (R : apost ((match pc_chunks (znth pclass0 c (st_cache s1)) with
| [] => bind (get_from_allocator c (pc_max (znth pclass0 c (st_cache s1)) / 2))
(fun got => match got with Some tops => set_pc c (mkPC (pc_max (znth pclass0 c (st_cache s1))) (cache_fill_order tops)) | None => ret tt end)
| _ :: _ => ret tt end) s1) (fun r => FRAME c s (snd r))).
{ destruct (pc_chunks (znth pclass0 c (st_cache s1))).
- apply apost_bind. eapply apost_mono; [|apply get_from_allocator_frame; exact Hc]. intros [got s2] F2. cbn [fst snd].
destruct got as [tops|]; [apply apost_set_pc | apply apost_ret]; cbn [snd];
[eapply FRAME_trans; [exact (FRAME_trans _ _ _ _ F1 F2) | apply FRAME_upd_pc; exact Hc] | exact (FRAME_trans _ _ _ _ F1 F2)].
- apply apost_ret. exact F1. }
eapply apost_mono; [|exact R]. intros [[] s2] F2. cbn [fst snd].
apply apost_bind. apply apost_get_pc. cbn [fst snd]. unfold cache.
destruct (pc_chunks (znth pclass0 c (st_cache s2))); [apply apost_ret; exact F2|].
apply apost_bind. apply apost_set_pc. cbn [fst snd]. apply apost_ret. cbn [snd]. eapply FRAME_trans; [exact F2 | apply FRAME_upd_pc; exact Hc].
Qed.
End g.
Definition SAMEQ (s s' : astate) : Prop :=
st_regions s' = st_regions s /\ st_cache s' = st_cache s /\ st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s.
Ltac sameq := unfold SAMEQ in *; cbn [fst snd st_regions st_cache st_qthread st_qglobal set_nev set_secs set_sec_arr set_sec_reserved
set_depot set_chunks set_internal_inited set_fs] in *; repeat split; try reflexivity; try congruence; try tauto.
Lemma depot_put_sameq : forall trc s0 s, SAMEQ s0 s -> apost (depot_put trc s) (fun r => SAMEQ s0 (snd r)).
Proof.
intros trc s0 s H. unfold depot_put.
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact H|].
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_put. cbn [snd]. destruct H as (A & B & C & D). sameq.
Qed.
Lemma sec_alloc_sameq : forall n s0 s, SAMEQ s0 s -> apost (sec_alloc n s) (fun r => SAMEQ s0 (snd r)).
Proof.
intros n s0 s H. unfold sec_alloc. destruct H as (A & B & C & D).
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; cbn [snd]; sameq|].
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_put. cbn [fst snd].
apply apost_bind.
match goal with |- apost ((if ?b then ?m1 else ?m2) ?s2) _ =>
assert (X : apost ((if b then m1 else m2) s2) (fun r => SAMEQ s0 (snd r))) end.
{ apply apost_if; intros _.
- apply apost_bind. apply apost_askz. intros z2 _. cbn [fst snd]. apply apost_if; intros _; [apply apost_modify | apply apost_spin]. cbn [snd]. sameq.
- apply apost_ret. cbn [snd]. sameq. }
eapply apost_mono; [|exact X]. intros [[] s3] H3. cbn [fst snd].
apply apost_bind. apply apost_modify. cbn [fst snd]. apply apost_ret. cbn [snd]. destruct H3 as (A3 & B3 & C3 & D3). sameq.
Qed.
Lemma malloc_sec_sameq : forall n trc S, from_primary n = false -> apost (malloc n trc S) (fun r => SAMEQ S (snd r)).
Proof.
intros n trc S Hp. unfold malloc. rewrite Hp.
apply apost_bind. apply apost_tick. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. eapply apost_mono; [|apply sec_alloc_sameq; sameq]. intros [ob s1] H1. cbn [fst snd].
destruct ob as [beg|]; [|apply apost_ret; exact H1].
apply apost_bind. eapply apost_mono; [|apply depot_put_sameq; exact H1]. intros [[] s2] H2. cbn [fst snd].
apply apost_bind.
match goal with |- apost ((if ?b then ?m1 else ?m2) ?sx) _ =>
assert (X : apost ((if b then m1 else m2) sx) (fun r => SAMEQ S (snd r))) end.
{ apply apost_if; intros _.
- apply apost_bind. apply apost_askz. intros z _. cbn [fst snd]. apply apost_if; intros _; [apply apost_ret | apply apost_spin]. exact H2.
- apply apost_ret. exact H2. }
eapply apost_mono; [|exact X]. intros [[] s3] H3. cbn [fst snd].
apply apost_bind. apply apost_modify. cbn [fst snd]. apply apost_ret. cbn [snd]. destruct H3 as (A & B & C & D). sameq.
Qed.
Lemma enqueue_effect : forall k s, length (st_cache s) = 32%nat -> 0 <= ck_n k ->
apost (enqueue k s) (fun r =>
(forall c, 1 <= c <= 31 -> c <> kBatchClass -> reg (snd r) c = reg s c /\ pc_chunks (cache (snd r) c) = pc_chunks (cache s c)) /\
st_qglobal (snd r) = st_qglobal s /\
qc_bytes (st_qthread s) <= qc_bytes (st_qthread (snd r)) <= qc_bytes (st_qthread s) + ck_n k + kBatchBytes).
Proof.
intros k s L Hn. unfold enqueue.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind.
lazymatch goal with |- apost (?m s) _ => assert (X : apost (m s) (fun r => FRAME kBatchClass s (snd r))) end.
{ apply apost_if; intros _.
- apply apost_bind. eapply apost_mono; [|apply cache_alloc_frame; [unfold kBatchClass; lia | exact L]]. intros [ob s4] F4. cbn [fst snd] in F4 |- *.
destruct ob; [apply apost_ret; exact F4 | apply apost_spin].
- apply apost_ret. apply FRAME_refl. }
eapply apost_mono; [|exact X]. intros [nb s4] (F4 & Q4 & G4 & L4). cbn [fst snd] in F4, Q4, G4, L4 |- *.
apply apost_modify. cbn [snd st_qglobal st_qthread set_qthread]. unfold reg, cache in *. cbn [st_regions st_cache set_qthread].
split; [intros c Hc Hc'; destruct (F4 c Hc Hc') as [X1 X2]; rewrite X1, X2; split; reflexivity|].
rewrite G4, Q4. split; [reflexivity|].
unfold qc_push. destruct nb; cbn [qc_bytes]; unfold kBatchBytes; lia.
Qed.
Lemma maybe_drain_effect : forall s, quar_bytes s <= kQuarantineMax ->
apost (maybe_drain s) (fun r => st_regions (snd r) = st_regions s /\ st_cache (snd r) = st_cache s /\ quar_bytes (snd r) = quar_bytes s).
Proof.
intros s Hq. unfold maybe_drain.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_if; intros Hb; [apply apost_ret; cbn [snd]; repeat split; reflexivity|].
apply apost_bind. apply apost_put. cbn [fst snd].
apply apost_if; intros Hb2.
- apply apost_ret. cbn [snd st_regions st_cache set_qglobal set_qthread]. split; [reflexivity|]. split; [reflexivity|].
unfold quar_bytes. cbn [st_qglobal st_qthread set_qglobal set_qthread qc_bytes qc0]. lia.
- exfalso. apply Z.leb_gt in Hb2. cbn [qc_bytes] in Hb2. unfold quar_bytes in Hq. lia.
Qed.
Definition FREEQ (s : astate) (k : chunk) (s' : astate) : Prop :=
(forall c, 1 <= c <= 31 -> c <> kBatchClass -> reg s' c = reg s c /\ pc_chunks (cache s' c) = pc_chunks (cache s c)) /\
quar_bytes s <= quar_bytes s' <= quar_bytes s + ck_n k + kBatchBytes.
Lemma free_norecycle_effect : forall p trc S k,
length (st_cache S) = 32%nat -> find_user (st_chunks S) p = Some k ->
0 <= ck_n k -> quar_bytes S + ck_n k + kBatchBytes <= kQuarantineMax ->
apost (free p trc S) (fun r => FREEQ S k (snd r)).
Proof.
intros p trc S k L Hf Hn Hq. unfold free.
apply apost_bind. apply apost_tick. cbn [fst snd].
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind.
lazymatch goal with |- apost (?m ?sx) _ =>
assert (X : apost (m sx) (fun r => SAMEQ S (snd r) /\ st_chunks (snd r) = st_chunks S /\ length (st_cache (snd r)) = 32%nat)) end.
{ apply apost_if; intros _; [apply apost_ret | apply apost_modify]; cbn [snd]; sameq. }
eapply apost_mono; [|exact X]. intros [[] s1] (H1 & C1 & L1). cbn [fst snd] in H1, C1, L1 |- *. clear X.
assert (NULLQ : FREEQ S k s1).
{ destruct H1 as (A & B & C & D). split; [| unfold quar_bytes; rewrite C, D; unfold kBatchBytes; lia].
intros c Hc _. unfold reg, cache. rewrite A, B. split; reflexivity. }
assert (K : forall s0, SAMEQ S s0 -> st_chunks s0 = st_chunks S -> length (st_cache s0) = 32%nat ->
apost ((s <- get ;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 1 ;;
depot_put trc ;;
modify (fun s2 => set_chunks (upd_chunk (st_chunks s2) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s2) ;;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |} ;;
maybe_drain
| None => fail (FCheck 2)
end) s0) (fun r => FREEQ S k (snd r))).
2:{ destruct p; [apply apost_ret; exact NULLQ | apply K; assumption | apply K; assumption | apply K; assumption]. }
intros s0 H0 C0 L0.
apply apost_bind. apply apost_get. cbn [fst snd]. rewrite C0, Hf.
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. eapply apost_mono; [|apply depot_put_sameq; exact H0]. intros [[] s2] H2. cbn [fst snd] in H2 |- *.
apply apost_bind. apply apost_modify. cbn [fst snd].
set (k' := {| ck_beg := ck_beg k; ck_req := ck_req k; ck_state := CQuarantined |}).
set (s3 := set_chunks (upd_chunk (st_chunks s2) k') s2).
assert (H3 : SAMEQ S s3 /\ length (st_cache s3) = 32%nat).
{ destruct H0 as (A0 & B0 & C0' & D0). destruct H2 as (A & B & C & D). subst s3. split; [sameq | cbn [st_cache set_chunks]; rewrite B, <- B0; exact L0]. }
clearbody s3. clear H2. destruct H3 as ((A & B & C & D) & L3).
apply apost_bind. eapply apost_mono; [|apply (enqueue_effect k' s3 L3); subst k'; unfold ck_n in *; cbn [ck_req] in *; exact Hn].
intros [[] s4] (R4 & G4 & Q4). cbn [fst snd] in R4, G4, Q4 |- *.
assert (Q4' : quar_bytes S <= quar_bytes s4 <= quar_bytes S + ck_n k + kBatchBytes).
{ unfold quar_bytes. rewrite G4, D. rewrite C in Q4. subst k'. unfold ck_n in *. cbn [ck_req] in *. lia. }
eapply apost_mono; [|apply maybe_drain_effect; lia]. intros [[] s5] (R5 & C5 & Q5). cbn [fst snd] in R5, C5, Q5 |- *.
split; [|lia]. intros c Hc Hc'. unfold reg, cache. rewrite R5, C5. destruct (R4 c Hc Hc') as [X1 X2]. unfold reg, cache in X1, X2, A, B |- *.
rewrite X1, X2, A, B. split; reflexivity.
Qed.
Lemma quar_bytes_init : quar_bytes init_state = 0.
Proof. reflexivity. Qed.
Lemma pristine_malloc_sec : forall n trc S evs r S' cs,
from_primary n = false -> apath (malloc n trc S) evs (r, S') -> prim_pristine_except S cs ->
prim_pristine_except S' cs /\ quar_bytes S' = quar_bytes S.
Proof.
intros n trc S evs r S' cs Hp Hy HP.
pose proof (apost_apath _ _ _ _ (malloc_sec_sameq n trc S Hp) Hy) as (A & B & C & D). cbn [snd] in A, B, C, D.
split; [| unfold quar_bytes; rewrite C, D; reflexivity].
intros c Hc Hcs. unfold pristine_class, reg, cache. rewrite A, B. exact (HP c Hc Hcs).
Qed.
Lemma pristine_free_null : forall trc S evs S' cs,
apath (free PNull trc S) evs (tt, S') -> prim_pristine_except S cs -> prim_pristine_except S' cs /\ quar_bytes S' = quar_bytes S.
Proof.
intros trc S evs S' cs Hy HP.
assert (X : apost (free PNull trc S) (fun r => SAMEQ S (snd r))).
{ unfold free. apply apost_bind. apply apost_tick. cbn [fst snd]. apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind.
lazymatch goal with |- apost (?m ?sx) _ => assert (X : apost (m sx) (fun r => SAMEQ S (snd r))) end.
{ apply apost_if; intros _; [apply apost_ret | apply apost_modify]; cbn [snd]; sameq. }
eapply apost_mono; [|exact X]. intros [[] s1] H1. apply apost_ret. exact H1. }
pose proof (apost_apath _ _ _ _ X Hy) as (A & B & C & D). cbn [snd] in A, B, C, D.
split; [| unfold quar_bytes; rewrite C, D; reflexivity].
intros c Hc Hcs. unfold pristine_class, reg, cache. rewrite A, B. exact (HP c Hc Hcs).
Qed.
Lemma pristine_free_norecycle : forall U p n trc S evs S' cs,
Wf U S -> In (p, n) (blocks S) -> quar_bytes S + req_size n + kBatchBytes <= kQuarantineMax ->
apath (free p trc S) evs (tt, S') -> prim_pristine_except S cs ->
prim_pristine_except S' (kBatchClass :: cs) /\ quar_bytes S <= quar_bytes S' <= quar_bytes S + req_size n + kBatchBytes.
Proof.
intros U p n trc S evs S' cs W Hin Hq Hy HP.
destruct (find_user_block U 0 0 0 S p n W Hin) as (k & Hf & Hk & _ & _ & Hr).
assert (Hn : ck_n k = req_size n) by (unfold ck_n; rewrite Hr; reflexivity).
assert (Hn0 : 0 <= ck_n k) by (rewrite Hn; unfold req_size; destruct (n =? 0) eqn:E; [lia|]; apply Z.eqb_neq in E;
pose proof (proj1 (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k Hk)); lia).
rewrite <- Hn in Hq |- *.
pose proof (apost_apath _ _ _ _ (free_norecycle_effect p trc S k (wf_len_cache _ _ _ _ _ W) Hf Hn0 Hq) Hy) as [R Q]. cbn [snd] in R, Q.
split; [|exact Q].
intros c Hc Hcs. assert (c <> kBatchClass /\ ~ In c cs) as [H1 H2] by (split; [intros ->; apply Hcs; left; reflexivity | intros H; apply Hcs; right; exact H]).
destruct (R c Hc H1) as [X1 X2]. unfold pristine_class. rewrite X1, X2. exact (HP c Hc H2).
Qed.
