(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh.
Import ListNotations.
Open Scope Z_scope.
Local Open Scope amodel_scope.

Section TreeLogic.
Variable aok : evA -> ansA -> Prop.

Fixpoint tall {R} (Q : res R -> Prop) (t : T R) : Prop :=
match t with
| SRet r => Q r
| SVis e k => forall a, aok e a -> tall Q (k a)
end.

Definition rok {R} (P : R -> Prop) (r : res R) : Prop :=
match r with ROk x => P x | RSpin => True | RUnr _ => False end.

Lemma tall_ret {R} (Q : res R -> Prop) (r : R) : Q (ROk r) -> tall Q (tret r).
Proof. intros H; exact H. Qed.

Lemma tall_vis {R} (Q : res R -> Prop) e (k : ansA -> T R) :
(forall a, aok e a -> tall Q (k a)) -> tall Q (tvis e k).
Proof. intros H; exact H. Qed.

Lemma tall_mono {R} (Q Q' : res R -> Prop) (t : T R) :
tall Q t -> (forall r, Q r -> Q' r) -> tall Q' t.
Proof.
induction t as [r|e k IH]; cbn; intros H HQ; [auto|].
intros a Ha. eapply IH; eauto.
Qed.

Lemma tall_bind {R S} (Q : res S -> Prop) (t : T R) (f : R -> T S) :
tall (fun r => match r with ROk x => tall Q (f x) | RSpin => Q RSpin | RUnr w => Q (RUnr w) end) t ->
tall Q (tbind t f).
Proof.
unfold tbind. induction t as [r|e k IH]; cbn; intros H.
- destruct r as [x| |w]; cbn; auto.
- intros a Ha. apply IH. apply H. exact Ha.
Qed.

Lemma tall_bind_rok {R S} (P1 : R -> Prop) (P : S -> Prop) (t : T R) (f : R -> T S) :
tall (rok P1) t -> (forall x, P1 x -> tall (rok P) (f x)) -> tall (rok P) (tbind t f).
Proof.
intros Ht Hf. apply tall_bind. eapply tall_mono; [exact Ht|].
intros [x| |w]; cbn; auto.
Qed.

Lemma tall_rok_ret {R} (P : R -> Prop) (r : R) : P r -> tall (rok P) (tret r).
Proof. intros H; exact H. Qed.
Lemma tall_rok_spin {R} (P : R -> Prop) : tall (rok P) (@tspin R).
Proof. exact I. Qed.

End TreeLogic.

Lemma tall_aok_mono {R} (aok aok' : evA -> ansA -> Prop) (Q : res R -> Prop) (t : T R) :
tall aok Q t -> (forall e a, aok' e a -> aok e a) -> tall aok' Q t.
Proof. induction t as [r|e k IH]; cbn; intros H Hm; [exact H|]. intros a Ha. apply IH; auto. Qed.

Definition is_prim (p : aptr) : bool := match p with APrim _ _ => true | ASec _ _ => false end.
Definition is_cls (c : Z) (p : aptr) : bool :=
match p with APrim _ n => class_of n =? c | ASec _ _ => false end.

Definition cntc (c : Z) (ps : list aptr) : Z := zcount (is_cls c) ps.

Definition qchunks (q : qcache) : list aptr := flat_map b_chunks (q_list q).
Definition nbat (q : qcache) : Z := zlen (q_list q).

Fixpoint secs (ps : list aptr) : list (Z * Z) :=
match ps with
| [] => []
| ASec a n :: ps' => (a, n) :: secs ps'
| APrim _ _ :: ps' => secs ps'
end.
Definition reg_pairs (r : list secent) : list (Z * Z) := map (fun e => (se_beg e, se_req e)) r.

Definition umin_tab : list Z :=
[0; 1; 17; 49; 65; 0; 97; 129; 161; 193; 225; 257; 289; 321; 353; 385; 417; 449; 641; 897; 1409; 1921; 2945; 3969;
5889; 7937; 12033; 16129; 24065; 32257; 48129].
Definition umin (c : Z) : Z := nth (Z.to_nat c) umin_tab 0.

Lemma umin_nonneg c : 0 <= umin c.
Proof.
unfold umin. generalize (Z.to_nat c) as k. intros k.
do 31 (destruct k as [|k]; [cbn; lia|]). cbn. destruct k; cbn; lia.
Qed.

Record cwf (c : Z) (x : cstate) : Prop := mkCWF {
cw_nf    : 0 <= c_num_freed x;
cw_cnt   : 0 <= c_count x <= max_count c;
cw_au    : 0 <= c_alloc_user x <= c_mapped_user x;
cw_mu    : c_mapped_user x <= kFreeArrayOffset;
cw_mu_al : (kUserMapSize | c_mapped_user x);
cw_fa    : 4 * c_num_freed x <= c_mapped_fa x <= kFreeArraySize;
cw_fa_al : (kFreeArrayMapSize | c_mapped_fa x)
}.

Definition bwf (lo : Z) (b : batch) : Prop :=
b_count b = zlen (b_chunks b) /\ lo <= b_count b <= kBatchCount /\
b_size b = kBatchBytes + zsum (map aptr_used (b_chunks b)).

Definition qwf (q : qcache) : Prop :=
Forall (bwf 1) (q_list q) /\ q_bytes q = zsum (map b_size (q_list q)).

Definition pwf (next : N) (p : aptr) : Prop :=
match p with
| APrim id n => (id < next)%N /\ 0 <= n /\ from_primary n = true
| ASec a n => 0 <= n /\ from_primary n = false
end.

Definition acc (c : Z) (x : cstate) : Z := c_alloc_user x - class_size c * (c_num_freed x + c_count x).

Definition allptrs (X E : list aptr) (s : AState) : list aptr :=
X ++ E ++ qchunks (as_tq s) ++ qchunks (as_gq s).

Definition tot (X E : list aptr) (B : Z) (s : AState) (c : Z) : Z :=
cntc c (allptrs X E s) + (if c =? kBatchClass then nbat (as_tq s) + nbat (as_gq s) + B else 0).

Record ainvx (X E : list aptr) (B : Z) (s : AState) : Prop := mkAINV {
ai_cls  : forall c, cwf c (cls s c);

ai_cons : forall c, 1 <= c <= 31 -> acc c (cls s c) = class_size c * tot X E B s c;
ai_tq   : qwf (as_tq s);
ai_gq   : qwf (as_gq s);
ai_B    : 0 <= B;
ai_pwf  : Forall (pwf (as_next s)) (allptrs X E s);
ai_reg  : Permutation (reg_pairs (as_reg s)) (secs (allptrs X E s));
ai_regw : Forall (fun e => se_size e = sec_map_size (se_req e)) (as_reg s);
ai_regd : NoDup (map se_beg (as_reg s));
ai_nres : zlen (as_reg s) <= as_nres s /\ 0 <= as_nres s <= kMaxNumChunks /\ (kPtrArrBlock | as_nres s)
}.

Definition qbounds (s : AState) : Prop := q_bytes (as_tq s) <= kQMaxCache /\ q_bytes (as_gq s) <= kQMaxSize.
Definition ainv (X : list aptr) (s : AState) : Prop := ainvx X [] 0 s /\ qbounds s.

Definition zavoids (b n : Z) (avoid : list (Z * Z)) : bool :=
forallb (fun iv => (b + n <=? fst iv) || (snd iv <=? b)) avoid.

Definition aok (s : AState) (e : evA) (a : ansA) : Prop :=
match e, a with
| EvMapAnon len avoid, AOk b => b mod kPage = 0 /\ 0 < b /\ zavoids b len avoid = true
| EvMapFixed _ _, AErr => False
| _, _ => True
end.

Lemma max_count_nonneg c : 0 <= max_count c.
Proof. unfold max_count. generalize (1024 / class_size c) as q. intros q. destruct (class_size c =? 0); lia. Qed.

Lemma cwf_cst0 c : cwf c cst0.
Proof.
constructor; cbn; unfold kFreeArrayOffset, kFreeArraySize, kUserMapSize, kFreeArrayMapSize; try lia.
- pose proof (max_count_nonneg c). lia.
- exists 0; lia.
- exists 0; lia.
Qed.

Lemma cls_astate0 c : cls astate0 c = cst0.
Proof. unfold cls. cbn. rewrite lookup_empty. reflexivity. Qed.

Lemma ainv_init : ainv [] astate0.
Proof.
unfold ainv. split; [|unfold qbounds, kQMaxCache, kQMaxSize; cbn; lia]. constructor; cbn -[cls].
- intros c. rewrite cls_astate0. apply cwf_cst0.
- intros c Hc. rewrite cls_astate0. unfold acc, tot, allptrs. cbn -[Z.mul Z.add Z.sub]. change (cntc c []) with 0. change (nbat q0) with 0. destruct (c =? kBatchClass); lia.
- split; [constructor| reflexivity].
- split; [constructor| reflexivity].
- lia.
- constructor.
- apply Permutation_refl.
- constructor.
- constructor.
- unfold zlen, kMaxNumChunks; cbn. repeat split; try lia. exists 0; lia.
Qed.

Lemma cls_set_cls_eq c x s : cls (set_cls c x s) c = x.
Proof. unfold cls, set_cls. cbn [as_cls]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma cls_set_cls_ne c c' x s : c' <> c -> cls (set_cls c x s) c' = cls s c'.
Proof. intros H. unfold cls, set_cls. cbn [as_cls]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma cls_set_inited s c : cls (set_inited s) c = cls s c. Proof. reflexivity. Qed.
Lemma cls_upd_cls_eq c f s : cls (upd_cls c f s) c = f (cls s c).
Proof. unfold upd_cls. apply cls_set_cls_eq. Qed.

Lemma cls_set_next v s c : cls (set_next v s) c = cls s c. Proof. reflexivity. Qed.

Lemma cls_set_tq v s c : cls (set_tq v s) c = cls s c. Proof. reflexivity. Qed.
Lemma cls_set_gq v s c : cls (set_gq v s) c = cls s c. Proof. reflexivity. Qed.

Definition only_cls (c : Z) (s s' : AState) : Prop :=
(forall c', c' <> c -> cls s' c' = cls s c') /\ as_next s' = as_next s /\ as_reg s' = as_reg s /\
as_nres s' = as_nres s /\ as_tq s' = as_tq s /\ as_gq s' = as_gq s.

Lemma only_cls_refl c s : only_cls c s s.
Proof. repeat split; auto. Qed.
Lemma only_cls_trans c s1 s2 s3 : only_cls c s1 s2 -> only_cls c s2 s3 -> only_cls c s1 s3.
Proof.
intros (A1&A2&A3&A4&A5&A6) (B1&B2&B3&B4&B5&B6). repeat split; try congruence.
intros c' Hc. rewrite B1 by exact Hc. apply A1. exact Hc.
Qed.
Lemma only_cls_set_cls c x s : only_cls c s (set_cls c x s).
Proof. repeat split; auto. intros c' Hc. apply cls_set_cls_ne. exact Hc. Qed.
Lemma only_cls_upd_cls c f s : only_cls c s (upd_cls c f s).
Proof. apply only_cls_set_cls. Qed.
Lemma only_cls_set_inited c s : only_cls c s (set_inited s).
Proof. repeat split; auto. Qed.
Lemma only_cls_set_cls' c x s0 s : only_cls c s0 s -> only_cls c s0 (set_cls c x s).
Proof. intros H. eapply only_cls_trans; [exact H| apply only_cls_set_cls]. Qed.
Lemma only_cls_upd_cls' c f s0 s : only_cls c s0 s -> only_cls c s0 (upd_cls c f s).
Proof. intros H. eapply only_cls_trans; [exact H| apply only_cls_upd_cls]. Qed.

Lemma round_up_ge x a : 0 < a -> x <= round_up x a.
Proof. intros Ha. unfold round_up. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a Ha). nia. Qed.
Lemma round_up_lt x a : 0 < a -> round_up x a < x + a.
Proof. intros Ha. unfold round_up. pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a Ha). nia. Qed.
Lemma round_up_mul x a : 0 < a -> (a | round_up x a).
Proof. intros Ha. unfold round_up. exists ((x + a - 1) / a). lia. Qed.
Lemma round_up_le_mul x a m : 0 < a -> (a | m) -> x <= m -> round_up x a <= m.
Proof.
intros Ha [k ->] Hx. unfold round_up.
assert ((x + a - 1) / a < k + 1) ; [|nia].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma round_down_le x a : 0 < a -> 0 <= x -> round_down x a <= x.
Proof. intros Ha Hx. unfold round_down. pose proof (Z.div_mod x a ltac:(lia)). pose proof (Z.mod_pos_bound x a Ha). nia. Qed.
Lemma round_down_gt x a : 0 < a -> x - a < round_down x a.
Proof. intros Ha. unfold round_down. pose proof (Z.div_mod x a ltac:(lia)). pose proof (Z.mod_pos_bound x a Ha). nia. Qed.
Lemma round_down_mul x a : 0 < a -> (a | round_down x a).
Proof. intros Ha. unfold round_down. exists (x / a). lia. Qed.

Definition zseqn (lo : Z) (n : nat) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 n).
Lemma zseqn_spec lo n c : lo <= c < lo + Z.of_nat n -> In c (zseqn lo n).
Proof.
intros H. unfold zseqn. apply in_map_iff. exists (Z.to_nat (c - lo)). split; [lia|].
apply in_seq. lia.
Qed.

Fixpoint forall_range (P : Z -> bool) (lo : Z) (n : nat) {struct n} : bool :=
match n with O => true | S n' => P lo && forall_range P (lo + 1) n' end.
Lemma forall_range_spec P lo n hi : forall_range P lo n = true -> hi = lo + Z.of_nat n ->
forall c, lo <= c < hi -> P c = true.
Proof.
intros H -> c. revert lo H c. induction n as [|n IH]; intros lo H c Hc; [lia|].
cbn [forall_range] in H. apply andb_true_iff in H as [H1 H2].
destruct (Z.eq_dec c lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1)); [exact H2| lia].
Qed.

Definition class_check (c : Z) : bool :=
(32 <=? class_size c) && (2 <=? max_count c) && (max_count c <=? 16) && (max_count c =? 2 * (max_count c / 2)).
Lemma class_tab : forall_range class_check 1 31 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma class_facts c : 1 <= c <= 31 ->
32 <= class_size c /\ 2 <= max_count c <= 16 /\ max_count c = 2 * (max_count c / 2).
Proof.
intros Hc. pose proof (forall_range_spec _ _ _ 32 class_tab ltac:(reflexivity) c ltac:(lia)) as H.
unfold class_check in H. rewrite !andb_true_iff, !Z.leb_le, Z.eqb_eq in H. tauto.
Qed.

Definition class30_check (c : Z) : bool := (class_size c <=? 65536) && (max_count c / 2 * class_size c <=? 65536).

Definition class_of_check (n : Z) : bool :=
let c := class_of n in (1 <=? c) && (c <=? 30) && (umin c <=? used_size n) && (needed n <=? class_size c).
Lemma class_of_tab : forall_range class_of_check 0 64513 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma from_primary_le n : 0 <= n -> from_primary n = true -> n <= 64512.
Proof.
intros Hn Hp. unfold from_primary, needed, rz_size, kMaxSize in Hp.
destruct (Z.leb_spec n 64512); [lia|]. exfalso.
do 6 (destruct (n <=? _) eqn:?E in Hp; [apply Z.leb_le in E; lia| clear E]).
unfold round_up in Hp. apply Z.leb_le in Hp.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia.
Qed.

Lemma class_of_facts n : 0 <= n -> from_primary n = true ->
1 <= class_of n <= 30 /\ umin (class_of n) <= used_size n /\ needed n <= class_size (class_of n).
Proof.
intros Hn Hp. pose proof (from_primary_le n Hn Hp) as Hle.
pose proof (forall_range_spec _ _ _ 64513 class_of_tab ltac:(vm_compute; reflexivity) n ltac:(lia)) as H.
unfold class_of_check in H. cbn zeta in H. rewrite !andb_true_iff, !Z.leb_le in H. tauto.
Qed.

Lemma used_size_pos n : 1 <= used_size n.
Proof. unfold used_size. lia. Qed.
