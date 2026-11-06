(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition OBJ_SIZE : Z := 24.
Definition KV_SIZE : Z := 48.
Definition STACK_ELEM_SIZE : Z := 8.
Definition PTR_SIZE : Z := 8.
Definition ELEM_SIZE : Z := 24.
Definition CHUNK_HDR : Z := 8.
Definition CHUNK_SIZE0 : Z := 8192.
Definition SBUF_INIT : Z := 8192.
Definition LIMIT : Z := 1000.
Definition EMBED_STACK : Z := 32.
Definition VIS_SIZE : Z := 128.
Definition CTX_SIZE : Z := 64.
Definition ZONE_SIZE : Z := 56.
Definition VIS_OBJ_OFF : Z := 64.

Definition T_NIL : Z := 0.  Definition T_BOOLEAN : Z := 1.  Definition T_POSINT : Z := 2.  Definition T_NEGINT : Z := 3.
Definition T_FLOAT64 : Z := 4.  Definition T_STR : Z := 5.  Definition T_BIN : Z := 6.  Definition T_ARRAY : Z := 7.
Definition T_MAP : Z := 8.  Definition T_EXT : Z := 9.  Definition T_FLOAT32 : Z := 10.

Definition CS_HEADER : Z := 0.  Definition ACS_STR_VALUE : Z := 32.  Definition ACS_BIN_VALUE : Z := 33.  Definition ACS_EXT_VALUE : Z := 34.

Definition PARSE_SUCCESS : Z := 2.  Definition PARSE_EXTRA_BYTES : Z := 1.  Definition PARSE_CONTINUE : Z := 0.
Definition PARSE_PARSE_ERROR : Z := -1.  Definition PARSE_STOP_VISITOR : Z := -2.

Inductive ctype := CT_ARRAY_ITEM | CT_MAP_KEY | CT_MAP_VALUE.

Definition ctype_code (t : ctype) : Z :=
  match t with CT_ARRAY_ITEM => 0 | CT_MAP_KEY => 1 | CT_MAP_VALUE => 2 end.
Definition ctype_eqb (a b : ctype) : bool := Z.eqb (ctype_code a) (ctype_code b).
Definition ctype_of_code (c : Z) : option ctype :=
  if c =? 0 then Some CT_ARRAY_ITEM else if c =? 1 then Some CT_MAP_KEY else if c =? 2 then Some CT_MAP_VALUE else None.

Definition per (t : ctype) : Z := match t with CT_ARRAY_ITEM => 1 | _ => 2 end.

Definition container_type (t : ctype) : Z := match t with CT_ARRAY_ITEM => T_ARRAY | _ => T_MAP end.

Record level := mkLevel { lv_t : ctype; lv_n : Z; lv_rest : Z; lv_P : Z }.

Definition lv_k (l : level) : Z :=
  match lv_t l with
  | CT_ARRAY_ITEM => lv_n l - lv_rest l
  | CT_MAP_KEY => 2 * (lv_n l - lv_rest l)
  | CT_MAP_VALUE => 2 * (lv_n l - lv_rest l) + 1
  end.

Definition lv_slot (l : level) : Z := lv_P l + OBJ_SIZE * lv_k l.

Definition lv_bytes (l : level) : Z := OBJ_SIZE * per (lv_t l) * lv_n l.

Fixpoint containers (root : Z) (ls : list level) : list Z :=
  match ls with
  | [] => []
  | l :: ls' => root :: containers (lv_slot l) ls'
  end.

Definition cur_slot (root : Z) (ls : list level) : Z :=
  match rev ls with [] => root | l :: _ => lv_slot l end.

Definition level_valid (l : level) : Prop :=
  1 <= lv_rest l /\ lv_rest l <= lv_n l /\ lv_n l <= LIMIT /\ lv_P l <> 0 /\ lv_P l mod 8 = 0.
Definition level_valid_b (l : level) : bool :=
  (1 <=? lv_rest l) && (lv_rest l <=? lv_n l) && (lv_n l <=? LIMIT) && negb (lv_P l =? 0) && (lv_P l mod 8 =? 0).

Record vecg := mkVec { v_begin : Z; v_size : Z  ; v_cap : Z  ; v_elt : Z   }.
Definition v_end (v : vecg) : Z := v_begin v + v_elt v * v_size v.
Definition v_capend (v : vecg) : Z := v_begin v + v_elt v * v_cap v.
Definition v_bytes (v : vecg) : Z := v_elt v * v_cap v.

Fixpoint zseq (a : Z) (n : nat) : list Z := match n with O => [] | S n' => a :: zseq (a + 1) n' end.
Definition pow2_b (x : Z) : bool := existsb (fun k => x =? 2^k) (zseq 0 63).
Lemma zseq_in : forall a n i, In i (zseq a n) <-> a <= i < a + Z.of_nat n.
Proof.
  intros a n. revert a. induction n as [|n IH]; intros a i; cbn [zseq].
  - split; [intros []|lia].
  - rewrite Nat2Z.inj_succ. split.
    + intros [<-|H]; [lia|]. apply IH in H. lia.
    + intros H. destruct (Z.eq_dec a i); [now left|right]. apply IH. lia.
Qed.
Lemma pow2_b_spec : forall x, pow2_b x = true <-> exists k, 0 <= k < 63 /\ x = 2^k.
Proof.
  intros x. unfold pow2_b. rewrite existsb_exists. split.
  - intros (k & Hk & E). apply Z.eqb_eq in E. apply zseq_in in Hk. exists k. split; [lia|exact E].
  - intros (k & Hk & E). exists k. split; [apply zseq_in; lia| now apply Z.eqb_eq].
Qed.
Lemma pow2_b_double : forall x, pow2_b x = true -> x < 2^62 -> pow2_b (2 * x) = true.
Proof.
  intros x H Hx. apply pow2_b_spec in H. destruct H as (k & Hk & ->). apply pow2_b_spec. exists (k + 1).
  assert (k < 62). { destruct (Z.lt_ge_cases k 62) as [L|L]; [exact L|]. exfalso.
    assert (2^62 <= 2^k) by (apply Z.pow_le_mono_r; lia). lia. }
  split; [lia|]. rewrite Z.pow_add_r by lia. change (2^1) with 2. lia.
Qed.
Definition vec_valid (v : vecg) : Prop :=
  0 < v_elt v /\ 0 <= v_size v <= v_cap v /\ v_begin v <> 0 /\ v_begin v mod 8 = 0.
Definition vec_valid_b (v : vecg) : bool :=
  (0 <? v_elt v) && (0 <=? v_size v) && (v_size v <=? v_cap v) && negb (v_begin v =? 0) && (v_begin v mod 8 =? 0).

Record zoneg := mkZone { z_addr : Z; z_chunks : list (Z * Z)  ;
                         z_ptr : Z; z_free : Z }.
Definition z_head (z : zoneg) : Z := match z_chunks z with [] => 0 | (c, _) :: _ => c end.
Definition z_head_sz (z : zoneg) : Z := match z_chunks z with [] => 0 | (_, sz) :: _ => sz end.

Definition chunk_lo (c : Z * Z) : Z := fst c + CHUNK_HDR.
Definition chunk_hi (c : Z * Z) : Z := fst c + CHUNK_HDR + snd c.
Definition in_chunk (c : Z * Z) (a n : Z) : Prop := chunk_lo c <= a /\ a + n <= chunk_hi c.
Definition in_chunk_b (c : Z * Z) (a n : Z) : bool := (chunk_lo c <=? a) && (a + n <=? chunk_hi c).

Definition in_zone (z : zoneg) (a n : Z) : Prop := exists c, In c (z_chunks z) /\ in_chunk c a n.
Definition in_zone_b (z : zoneg) (a n : Z) : bool := existsb (fun c => in_chunk_b c a n) (z_chunks z).

Definition in_alloc (z : zoneg) (a n : Z) : Prop :=
  (exists c, In c (tl (z_chunks z)) /\ in_chunk c a n) \/ (chunk_lo (hd (0,0) (z_chunks z)) <= a /\ a + n <= z_ptr z).
Definition in_alloc_b (z : zoneg) (a n : Z) : bool :=
  existsb (fun c => in_chunk_b c a n) (tl (z_chunks z)) || ((chunk_lo (hd (0,0) (z_chunks z)) <=? a) && (a + n <=? z_ptr z)).

Definition rdisj (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.
Definition rdisj_b (a n b k : Z) : bool := (a + n <=? b) || (b + k <=? a).
Fixpoint pairwise_b {A} (f : A -> A -> bool) (l : list A) : bool :=
  match l with [] => true | x :: l' => forallb (f x) l' && pairwise_b f l' end.

Definition chunk_disj (c c' : Z * Z) : Prop := rdisj (fst c) (CHUNK_HDR + snd c) (fst c') (CHUNK_HDR + snd c').
Definition chunk_disj_b (c c' : Z * Z) : bool := rdisj_b (fst c) (CHUNK_HDR + snd c) (fst c') (CHUNK_HDR + snd c').

Definition zone_valid (z : zoneg) : Prop :=
  z_chunks z <> [] /\ z_addr z <> 0 /\
  (forall c, In c (z_chunks z) -> fst c <> 0 /\ fst c mod 16 = 0 /\ CHUNK_SIZE0 <= snd c) /\
  chunk_lo (hd (0,0) (z_chunks z)) <= z_ptr z /\ 0 <= z_free z /\
  z_ptr z + z_free z = chunk_hi (hd (0,0) (z_chunks z)) /\
  ForallOrdPairs chunk_disj (z_chunks z).
Definition zone_valid_b (z : zoneg) : bool :=
  negb (Nat.eqb (length (z_chunks z)) 0) && negb (z_addr z =? 0) &&
  forallb (fun c => negb (fst c =? 0) && (fst c mod 16 =? 0) && (CHUNK_SIZE0 <=? snd c)) (z_chunks z) &&
  (chunk_lo (hd (0,0) (z_chunks z)) <=? z_ptr z) && (0 <=? z_free z) &&
  (z_ptr z + z_free z =? chunk_hi (hd (0,0) (z_chunks z))) &&
  pairwise_b chunk_disj_b (z_chunks z).

Lemma pairwise_b_ok : forall {A} (f : A -> A -> bool) (R : A -> A -> Prop) l,
  (forall x y, f x y = true -> R x y) -> pairwise_b f l = true -> ForallOrdPairs R l.
Proof.
  intros A f R l Hf. induction l as [|x l IH]; cbn; intros H; [constructor|].
  apply andb_prop in H. destruct H as [H1 H2]. constructor; [|now apply IH].
  apply Forall_forall. intros y Hy. apply Hf. eapply forallb_forall in H1; eauto.
Qed.
Lemma rdisj_b_ok : forall a n b k, rdisj_b a n b k = true -> rdisj a n b k.
Proof. intros a n b k H. unfold rdisj_b, rdisj in *. apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia. Qed.
Lemma rdisj_sym : forall a n b k, rdisj a n b k -> rdisj b k a n.
Proof. unfold rdisj; intros; lia. Qed.
Lemma rdisj_sub : forall a n b k a' n' b' k', rdisj a n b k -> a <= a' -> a' + n' <= a + n -> b <= b' -> b' + k' <= b + k -> rdisj a' n' b' k'.
Proof. unfold rdisj; intros; lia. Qed.

Lemma ForallOrdPairs_app_inv : forall {A} (R : A -> A -> Prop) l1 x l2,
  ForallOrdPairs R (l1 ++ x :: l2) -> Forall (R x) l2 /\ Forall (fun y => R y x) l1.
Proof.
  intros A R l1. induction l1 as [|y l1 IH]; intros x l2 H; cbn in H.
  - inversion H; subst. split; [assumption|constructor].
  - inversion H as [|y' l' Hf Hp]; subst. destruct (IH x l2 Hp) as [A1 A2]. split; [exact A1|]. constructor; [|exact A2].
    apply Forall_forall with (x := x) in Hf; [exact Hf|]. apply in_app_iff. right. now left.
Qed.
Lemma in_alloc_in_zone : forall z a n, z_chunks z <> [] -> z_ptr z <= chunk_hi (hd (0,0) (z_chunks z)) -> in_alloc z a n -> in_zone z a n.
Proof.
  intros z a n Hne Hp [(c & Hc & Hi)|(H1 & H2)]; unfold in_zone.
  - exists c. split; [|exact Hi]. destruct (z_chunks z); [contradiction|]. cbn in Hc. now right.
  - exists (hd (0,0) (z_chunks z)). destruct (z_chunks z) as [|c r]; [contradiction|]. cbn in *. split; [now left|].
    unfold in_chunk. lia.
Qed.
Lemma in_alloc_b_ok : forall z a n, in_alloc_b z a n = true -> in_alloc z a n.
Proof.
  intros z a n H. unfold in_alloc_b, in_alloc in *. apply orb_prop in H. destruct H as [H|H].
  - left. apply existsb_exists in H. destruct H as (c & Hc & Hb). exists c. split; [exact Hc|].
    unfold in_chunk_b, in_chunk in *. apply andb_prop in Hb. destruct Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
  - right. apply andb_prop in H. destruct H as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

Record unpg := mkUnp {
  u_ctx : Z;
  u_vis : Z;
  u_data : Z; u_len : Z;
  u_levels : list level;
  u_cstk : vecg;
  u_vstk : vecg;
  u_zone : zoneg }.

Definition u_root (g : unpg) : Z := u_vis g + VIS_OBJ_OFF.
Definition u_pe (g : unpg) : Z := u_data g + u_len g.
Definition u_D (g : unpg) : Z := Z.of_nat (length (u_levels g)).
Definition u_cur_slot (g : unpg) : Z := cur_slot (u_root g) (u_levels g).

#[warnings="-register-all"]
Inductive obj : Type :=
| ONil
| OBool (b : bool)
| OPos (u : Z)
| ONeg (i : Z)
| OF32 (bits : Z)
| OF64 (bits : Z)
| OStr (p n : Z)
| OBin (p n : Z)
| OExt (p n : Z)
| OArr (p : Z) (kids : list obj)
| OMap (p : Z) (kids : list obj).

Fixpoint obj_size (o : obj) : nat :=
  match o with
  | OArr _ kids | OMap _ kids => S (list_sum (map obj_size kids))
  | _ => 1%nat
  end.
Definition objs_size (l : list obj) : nat := list_sum (map obj_size l).
Lemma obj_size_arr : forall p kids, obj_size (OArr p kids) = S (objs_size kids).
Proof. reflexivity. Qed.
Lemma obj_size_map : forall p kids, obj_size (OMap p kids) = S (objs_size kids).
Proof. reflexivity. Qed.
Lemma objs_size_cons : forall o l, objs_size (o :: l) = (obj_size o + objs_size l)%nat.
Proof. reflexivity. Qed.

Definition obj_type (o : obj) : Z :=
  match o with
  | ONil => T_NIL | OBool _ => T_BOOLEAN | OPos _ => T_POSINT | ONeg _ => T_NEGINT | OF32 _ => T_FLOAT32 | OF64 _ => T_FLOAT64
  | OStr _ _ => T_STR | OBin _ _ => T_BIN | OExt _ _ => T_EXT | OArr _ _ => T_ARRAY | OMap _ _ => T_MAP
  end.

Definition obj_count (o : obj) : Z :=
  match o with
  | OArr _ kids => Z.of_nat (length kids)
  | OMap _ kids => Z.of_nat (length kids) / 2
  | _ => 0
  end.
Definition obj_ptr (o : obj) : Z :=
  match o with OStr p _ | OBin p _ | OExt p _ | OArr p _ | OMap p _ => p | _ => 0 end.

Record pelem := mkPE { pe_ptr : Z; pe_rest : Z; pe_map : bool; pe_key : bool }.

Definition pe_obj (e : pelem) : Z := pe_ptr e + (if pe_map e && negb (pe_key e) then OBJ_SIZE else 0).
Definition pe_per (e : pelem) : Z := if pe_map e then 2 else 1.

Fixpoint pcontainers (root : Z) (es : list pelem) : list Z :=
  match es with [] => [] | e :: es' => root :: pcontainers (pe_obj e) es' end.

Record sbufg := mkSb { sb_addr : Z; sb_size : Z; sb_data : Z; sb_alloc : Z }.
Definition sbuf_valid (s : sbufg) : Prop :=
  0 <= sb_size s <= sb_alloc s /\ SBUF_INIT <= sb_alloc s /\ sb_data s <> 0.
Definition sbuf_valid_b (s : sbufg) : bool :=
  (0 <=? sb_size s) && (sb_size s <=? sb_alloc s) && (SBUF_INIT <=? sb_alloc s) && negb (sb_data s =? 0).

Record packg := mkPack {
  p_op : Z;
  p_root : Z;
  p_elems : list pelem;
  p_evec : vecg;
  p_sb : sbufg }.

Definition last_opt {A} (l : list A) : option A := match rev l with [] => None | x :: _ => Some x end.
Definition removelast {A} (l : list A) : list A := rev (tl (rev l)).

Lemma containers_length : forall root ls, length (containers root ls) = length ls.
Proof. intros root ls. revert root. induction ls; intros; cbn; [reflexivity|]. now rewrite IHls. Qed.
Lemma pcontainers_length : forall root es, length (pcontainers root es) = length es.
Proof. intros root es. revert root. induction es; intros; cbn; [reflexivity|]. now rewrite IHes. Qed.

Lemma cur_slot_cons : forall root l ls, cur_slot root (l :: ls) = cur_slot (lv_slot l) ls.
Proof.
  intros root l ls. unfold cur_slot. cbn [rev]. destruct (rev ls) as [|x r] eqn:E; cbn; reflexivity.
Qed.

Lemma containers_app : forall root ls1 ls2,
  containers root (ls1 ++ ls2) = containers root ls1 ++ containers (cur_slot root ls1) ls2.
Proof.
  intros root ls1. revert root. induction ls1 as [|l ls1 IH]; intros root ls2; cbn -[cur_slot].
  - reflexivity.
  - rewrite IH, cur_slot_cons. reflexivity.
Qed.

Lemma cur_slot_snoc : forall root ls l, cur_slot root (ls ++ [l]) = lv_slot l.
Proof. intros. unfold cur_slot. rewrite rev_app_distr. cbn. reflexivity. Qed.
Lemma cur_slot_nil : forall root, cur_slot root [] = root.
Proof. reflexivity. Qed.
