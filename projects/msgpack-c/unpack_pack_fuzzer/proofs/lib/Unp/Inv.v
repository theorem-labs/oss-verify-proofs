(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Fixpoint even_len {A} (l : list A) : bool := match l with [] => true | _ :: [] => false | _ :: _ :: l' => even_len l' end.

Fixpoint tree_wf (m : bmem) (z : zoneg) (o : obj) {struct o} : Prop :=
  match o with
  | ONil | OBool _ | OF32 _ | OF64 _ => True
  | OPos u => 0 <= u < 2^64
  | ONeg i => - 2^64 <= i < 0
  | OStr p n | OBin p n => 0 <= n <= LIMIT /\ (p = 0 -> n = 0) /\ (p <> 0 -> in_zone z p n /\ readable m p (Z.to_nat n))
  | OExt p n => 0 <= n /\ n + 1 <= LIMIT /\ p <> 0 /\ in_zone z p (n + 1) /\ readable m p (Z.to_nat (n + 1))
  | OArr p kids =>
      Z.of_nat (length kids) <= LIMIT /\ (kids = [] <-> p = 0) /\
      (kids <> [] -> p mod 8 = 0 /\ in_zone z p (OBJ_SIZE * Z.of_nat (length kids))) /\
      (fix wfl (l : list obj) {struct l} : Prop := match l with [] => True | o' :: l' => tree_wf m z o' /\ wfl l' end) kids
  | OMap p kids =>
      even_len kids = true /\ Z.of_nat (length kids) / 2 <= LIMIT /\ (kids = [] <-> p = 0) /\
      (kids <> [] -> p mod 8 = 0 /\ in_zone z p (OBJ_SIZE * Z.of_nat (length kids))) /\
      (fix wfl (l : list obj) {struct l} : Prop := match l with [] => True | o' :: l' => tree_wf m z o' /\ wfl l' end) kids
  end.
Fixpoint trees_wf (m : bmem) (z : zoneg) (l : list obj) : Prop :=
  match l with [] => True | o :: l' => tree_wf m z o /\ trees_wf m z l' end.

Definition listZ_eqb_nil {A} (l : list A) : bool := match l with [] => true | _ => false end.
Fixpoint tree_wf_b (m : bmem) (z : zoneg) (o : obj) {struct o} : bool :=
  match o with
  | ONil | OBool _ | OF32 _ | OF64 _ => true
  | OPos u => (0 <=? u) && (u <? 2^64)
  | ONeg i => (- 2^64 <=? i) && (i <? 0)
  | OStr p n | OBin p n => (0 <=? n) && (n <=? LIMIT) && (if p =? 0 then n =? 0 else in_zone_b z p n && readable_b m p (Z.to_nat n))
  | OExt p n => (0 <=? n) && (n + 1 <=? LIMIT) && negb (p =? 0) && in_zone_b z p (n + 1) && readable_b m p (Z.to_nat (n + 1))
  | OArr p kids =>
      (Z.of_nat (length kids) <=? LIMIT) && Bool.eqb (listZ_eqb_nil kids) (p =? 0) &&
      (listZ_eqb_nil kids || ((p mod 8 =? 0) && in_zone_b z p (OBJ_SIZE * Z.of_nat (length kids)))) &&
      (fix wfl (l : list obj) {struct l} : bool := match l with [] => true | o' :: l' => tree_wf_b m z o' && wfl l' end) kids
  | OMap p kids =>
      even_len kids && (Z.of_nat (length kids) / 2 <=? LIMIT) && Bool.eqb (listZ_eqb_nil kids) (p =? 0) &&
      (listZ_eqb_nil kids || ((p mod 8 =? 0) && in_zone_b z p (OBJ_SIZE * Z.of_nat (length kids)))) &&
      (fix wfl (l : list obj) {struct l} : bool := match l with [] => true | o' :: l' => tree_wf_b m z o' && wfl l' end) kids
  end.

Lemma in_zone_b_ok : forall z a n, in_zone_b z a n = true -> in_zone z a n.
Proof.
  intros z a n H. unfold in_zone_b, in_zone in *. apply existsb_exists in H. destruct H as (c & Hc & Hb).
  exists c. split; [exact Hc|]. unfold in_chunk_b, in_chunk in *. apply andb_prop in Hb. destruct Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Local Ltac zbool :=
  repeat match goal with
    | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : negb (_ =? _) = true |- _ => apply negb_true_iff in H; apply Z.eqb_neq in H
    | H : in_zone_b _ _ _ = true |- _ => apply in_zone_b_ok in H
    | H : readable_b _ _ _ = true |- _ => apply readable_b_ok in H
    end.

Lemma tree_wf_b_ok : forall m z o, tree_wf_b m z o = true -> tree_wf m z o.
Proof.
  intros m z. apply (obj_ind_size (fun o => tree_wf_b m z o = true -> tree_wf m z o)).
  intros o IH H. destruct o; cbn [tree_wf_b tree_wf] in H |- *; try exact I.
  - zbool. lia.
  - zbool. lia.
  - zbool. destruct (Z.eqb_spec p 0); zbool; repeat split; try lia; intros; try contradiction; tauto.
  - zbool. destruct (Z.eqb_spec p 0); zbool; repeat split; try lia; intros; try contradiction; tauto.
  - zbool. repeat split; try lia; tauto.
  -
    apply andb_prop in H. destruct H as [H Hk]. zbool.
    assert (Hkids : (fix wfl (l : list obj) {struct l} : Prop := match l with [] => True | o' :: l' => tree_wf m z o' /\ wfl l' end) kids).
    { assert (IHk : forall o', In o' kids -> tree_wf_b m z o' = true -> tree_wf m z o').
      { intros o' Hin. apply IH. rewrite obj_size_arr. pose proof (in_kids_size o' kids Hin). lia. }
      clear - IHk Hk. revert Hk IHk. induction kids as [|x l IHl]; intros Hk IHk; cbn in Hk |- *; [exact I|].
      apply andb_prop in Hk. destruct Hk as [Hx Hl].
      split; [apply IHk; [now left|exact Hx]|]. apply IHl; [exact Hl|]. intros o' Ho'. apply IHk. now right. }
    repeat split; try exact Hkids; try lia.
    + intro E. subst kids. cbn in H1. destruct (Z.eqb_spec p 0); [lia|discriminate].
    + intro E. subst p. rewrite Z.eqb_refl in H1. destruct kids; [reflexivity|discriminate].
    + destruct kids; [congruence|]. cbn [listZ_eqb_nil orb] in H0. zbool. lia.
    + destruct kids; [congruence|]. cbn [listZ_eqb_nil orb] in H0. zbool. assumption.
  -
    apply andb_prop in H. destruct H as [H Hk]. zbool.
    assert (Hkids : (fix wfl (l : list obj) {struct l} : Prop := match l with [] => True | o' :: l' => tree_wf m z o' /\ wfl l' end) kids).
    { assert (IHk : forall o', In o' kids -> tree_wf_b m z o' = true -> tree_wf m z o').
      { intros o' Hin. apply IH. rewrite obj_size_map. pose proof (in_kids_size o' kids Hin). lia. }
      clear - IHk Hk. revert Hk IHk. induction kids as [|x l IHl]; intros Hk IHk; cbn in Hk |- *; [exact I|].
      apply andb_prop in Hk. destruct Hk as [Hx Hl].
      split; [apply IHk; [now left|exact Hx]|]. apply IHl; [exact Hl|]. intros o' Ho'. apply IHk. now right. }
    repeat split; try exact Hkids; try lia; try assumption.
    + intro E. subst kids. cbn in H1. destruct (Z.eqb_spec p 0); [lia|discriminate].
    + intro E. subst p. rewrite Z.eqb_refl in H1. destruct kids; [reflexivity|discriminate].
    + destruct kids; [congruence|]. cbn [listZ_eqb_nil orb] in H0. zbool. lia.
    + destruct kids; [congruence|]. cbn [listZ_eqb_nil orb] in H0. zbool. assumption.
Qed.

Definition tree_at (m : bmem) (z : zoneg) (a : Z) (o : obj) : Prop := obj_at m a o /\ tree_wf m z o.

Definition cap32_b (c : Z) : bool := (EMBED_STACK <=? c) && (c mod EMBED_STACK =? 0) && pow2_b (c / EMBED_STACK).

Definition level_disj (l l' : level) : Prop := rdisj (lv_P l) (lv_bytes l) (lv_P l') (lv_bytes l').
Definition level_disj_b (l l' : level) : bool := rdisj_b (lv_P l) (lv_bytes l) (lv_P l') (lv_bytes l').
Definition levels_alloc (z : zoneg) (ls : list level) : Prop :=
  (forall l, In l ls -> in_alloc z (lv_P l) (lv_bytes l)) /\ ForallOrdPairs level_disj ls.
Definition levels_alloc_b (z : zoneg) (ls : list level) : bool :=
  forallb (fun l => in_alloc_b z (lv_P l) (lv_bytes l)) ls && pairwise_b level_disj_b ls.

Definition lv_unfilled (l : level) : Z := lv_P l + lv_bytes l - lv_slot l.

Definition cell_ok (z : zoneg) (ls : list level) (c : Z) : Prop :=
  in_alloc z c OBJ_SIZE /\ forall l, In l ls -> rdisj c OBJ_SIZE (lv_slot l) (lv_unfilled l).
Definition cell_ok_b (z : zoneg) (ls : list level) (c : Z) : bool :=
  in_alloc_b z c OBJ_SIZE && forallb (fun l => rdisj_b c OBJ_SIZE (lv_slot l) (lv_unfilled l)) ls.

Definition completed_wf (m : bmem) (z : zoneg) (ls : list level) : Prop :=
  forall l, In l ls -> forall i, 0 <= i < lv_k l ->
    exists o, tree_at m z (lv_P l + OBJ_SIZE * i) o /\ (forall c, In c (obj_cells (lv_P l + OBJ_SIZE * i) o) -> cell_ok z ls c).

Definition node_ok_b (fuel : nat) (m : bmem) (z : zoneg) (a : Z) : bool :=
  match decode_obj fuel m a with Some o => obj_at_b m a o && tree_wf_b m z o | None => false end.
Definition cnode_ok_b (fuel : nat) (m : bmem) (z : zoneg) (ls : list level) (a : Z) : bool :=
  match decode_obj fuel m a with
  | Some o => obj_at_b m a o && tree_wf_b m z o && forallb (cell_ok_b z ls) (obj_cells a o)
  | None => false
  end.
Definition completed_wf_b (fuel : nat) (m : bmem) (z : zoneg) (ls : list level) : bool :=
  forallb (fun l => forallb (fun i => cnode_ok_b fuel m z ls (lv_P l + OBJ_SIZE * i)) (zseq 0 (Z.to_nat (lv_k l)))) ls.

Definition regions_disj (rs : list (Z * Z)) : Prop := ForallOrdPairs (fun r r' => rdisj (fst r) (snd r) (fst r') (snd r')) rs.
Definition regions_disj_b (rs : list (Z * Z)) : bool := pairwise_b (fun r r' => rdisj_b (fst r) (snd r) (fst r') (snd r')) rs.
Lemma regions_disj_b_ok : forall rs, regions_disj_b rs = true -> regions_disj rs.
Proof. intros rs H. eapply pairwise_b_ok; [|exact H]. intros x y Hxy. now apply rdisj_b_ok. Qed.

Definition chunk_block (c : Z * Z) : Z * Z := (fst c, CHUNK_HDR + snd c).
Definition unp_blocks (g : unpg) : list (Z * Z) :=
  (v_begin (u_cstk g), v_bytes (u_cstk g)) :: (v_begin (u_vstk g), v_bytes (u_vstk g)) :: (z_addr (u_zone g), ZONE_SIZE)
  :: map chunk_block (z_chunks (u_zone g)).

Definition unp_regions (g : unpg) : list (Z * Z) := (u_ctx g, CTX_SIZE) :: (u_vis g, VIS_SIZE) :: unp_blocks g.

Definition UNP_CORE (live : Z -> Z -> Prop) (m : bmem) (g : unpg) (cur cs trail : Z) : Prop :=

  ctx_at m g cur cs trail /\ vis_at m g /\ zone_at m (u_zone g) /\ stacks_at m g /\
  conts_at m (containers (u_root g) (u_levels g)) (u_levels g) /\

  vec_valid (u_cstk g) /\ v_elt (u_cstk g) = 8 /\ v_size (u_cstk g) = u_D g /\ cap32_b (v_cap (u_cstk g)) = true /\
  vec_valid (u_vstk g) /\ v_elt (u_vstk g) = 8 /\ v_size (u_vstk g) = u_D g + 1 /\ cap32_b (v_cap (u_vstk g)) = true /\

  Forall level_valid (u_levels g) /\ u_D g <= LIMIT /\ levels_alloc (u_zone g) (u_levels g) /\
  completed_wf m (u_zone g) (u_levels g) /\

  zone_valid (u_zone g) /\

  (forall b, In b (unp_blocks g) -> live (fst b) (snd b)) /\ regions_disj (unp_regions g) /\

  u_ctx g <> 0 /\ u_vis g <> 0 /\ u_ctx g mod 8 = 0 /\ u_vis g mod 8 = 0 /\ 0 < u_len g /\ 0 < u_data g /\ u_pe g < 2^47.

Definition UNP_HEAD_INV (live : Z -> Z -> Prop) (m : bmem) (g : unpg) (cur pe offv fta nreg cs trail : Z) : Prop :=
  UNP_CORE live m g cur cs trail /\
  pe = u_pe g /\ offv = 0 /\
  u_data g <= cur < u_pe g /\
  ((cs = CS_HEADER /\ fta = 0) \/ ((cs = ACS_STR_VALUE \/ cs = ACS_BIN_VALUE \/ cs = ACS_EXT_VALUE) /\ fta = 1 /\ 0 <= trail < 2^64)) /\
  (nreg = 0 \/ u_data g <= nreg <= u_pe g).

Definition CONSUME_INV (live : Z -> Z -> Prop) (m : bmem) (g : unpg) (cur cs trail : Z) : Prop :=
  UNP_CORE live m g cur cs trail /\ u_data g < cur <= u_pe g /\ 1 <= u_D g /\

  (exists o, tree_at m (u_zone g) (u_cur_slot g) o /\ (forall c, In c (tl (obj_cells (u_cur_slot g) o)) -> cell_ok (u_zone g) (u_levels g) c)).

Definition UNP_THROW_SHAPE (live : Z -> Z -> Prop) (m : bmem) (g : unpg) : Prop :=
  vec_at m (u_ctx g + 32) (u_cstk g) /\ vec_at m (u_vis g + 88) (u_vstk g) /\ zone_at m (u_zone g) /\ zone_valid (u_zone g) /\
  vec_valid (u_cstk g) /\ vec_valid (u_vstk g) /\
  (forall b, In b (unp_blocks g) -> live (fst b) (snd b)).

Lemma UNP_CORE_throw_shape : forall live m g cur cs trail, UNP_CORE live m g cur cs trail -> UNP_THROW_SHAPE live m g.
Proof.
  intros live m g cur cs trail H. unfold UNP_CORE, UNP_THROW_SHAPE, ctx_at, vis_at in *. decompose [and] H.
  repeat match goal with |- _ /\ _ => split end; auto.
Qed.

Definition addr_sane_b (g : unpg) : bool :=
  negb (u_ctx g =? 0) && negb (u_vis g =? 0) && (u_ctx g mod 8 =? 0) && (u_vis g mod 8 =? 0) && (0 <? u_len g) && (0 <? u_data g) && (u_pe g <? 2^47).
Definition UNP_CORE_b (fuel : nat) (live_b : Z -> Z -> bool) (m : bmem) (g : unpg) (cur cs trail : Z) : bool :=
  ctx_at_b m g cur cs trail && vis_at_b m g && zone_at_b m (u_zone g) && stacks_at_b m g &&
  conts_at_b m (containers (u_root g) (u_levels g)) (u_levels g) &&
  vec_valid_b (u_cstk g) && (v_elt (u_cstk g) =? 8) && (v_size (u_cstk g) =? u_D g) && cap32_b (v_cap (u_cstk g)) &&
  vec_valid_b (u_vstk g) && (v_elt (u_vstk g) =? 8) && (v_size (u_vstk g) =? u_D g + 1) && cap32_b (v_cap (u_vstk g)) &&
  forallb level_valid_b (u_levels g) && (u_D g <=? LIMIT) && levels_alloc_b (u_zone g) (u_levels g) &&
  completed_wf_b fuel m (u_zone g) (u_levels g) &&
  zone_valid_b (u_zone g) &&
  forallb (fun b => live_b (fst b) (snd b)) (unp_blocks g) && regions_disj_b (unp_regions g) && addr_sane_b g.

Definition UNP_HEAD_INV_b (fuel : nat) (live_b : Z -> Z -> bool) (m : bmem) (g : unpg) (cur pe offv fta nreg cs trail : Z) : bool :=
  UNP_CORE_b fuel live_b m g cur cs trail &&
  (pe =? u_pe g) && (offv =? 0) && (u_data g <=? cur) && (cur <? u_pe g) &&
  (((cs =? CS_HEADER) && (fta =? 0)) || (((cs =? ACS_STR_VALUE) || (cs =? ACS_BIN_VALUE) || (cs =? ACS_EXT_VALUE)) && (fta =? 1) && (0 <=? trail) && (trail <? 2^64))) &&
  ((nreg =? 0) || ((u_data g <=? nreg) && (nreg <=? u_pe g))).

Definition cnode_tl_ok_b (fuel : nat) (m : bmem) (z : zoneg) (ls : list level) (a : Z) : bool :=
  match decode_obj fuel m a with
  | Some o => obj_at_b m a o && tree_wf_b m z o && forallb (cell_ok_b z ls) (tl (obj_cells a o))
  | None => false
  end.
Definition CONSUME_INV_b (fuel : nat) (live_b : Z -> Z -> bool) (m : bmem) (g : unpg) (cur cs trail : Z) : bool :=
  UNP_CORE_b fuel live_b m g cur cs trail && (u_data g <? cur) && (cur <=? u_pe g) && (1 <=? u_D g) &&
  cnode_tl_ok_b fuel m (u_zone g) (u_levels g) (u_cur_slot g).

Definition pelem_ok (m : bmem) (K : Z) (e : pelem) (allow_empty : bool) : Prop :=
  exists N Q,
    u32_at m K (if pe_map e then T_MAP else T_ARRAY) /\ u32_at m (K + 8) N /\ u64_at m (K + 16) Q /\
    ((1 <= pe_rest e <= N /\ Q <> 0 /\ pe_ptr e = Q + OBJ_SIZE * pe_per e * (N - pe_rest e))
     \/ (allow_empty = true /\ N = 0 /\ Q = 0 /\ pe_rest e = 0 /\ pe_ptr e = 0)).
Definition pelem_ok_b (m : bmem) (K : Z) (e : pelem) (allow_empty : bool) : bool :=
  u32_b m K (if pe_map e then T_MAP else T_ARRAY) &&
  match rdZ m (K + 8) 4, rdZ m (K + 16) 8 with
  | Some N, Some Q =>
      ((1 <=? pe_rest e) && (pe_rest e <=? N) && negb (Q =? 0) && (pe_ptr e =? Q + OBJ_SIZE * pe_per e * (N - pe_rest e)))
      || (allow_empty && (N =? 0) && (Q =? 0) && (pe_rest e =? 0) && (pe_ptr e =? 0))
  | _, _ => false
  end.
Fixpoint pelems_ok (m : bmem) (Ks : list Z) (es : list pelem) (allow_empty_top : bool) : Prop :=
  match Ks, es with
  | K :: Ks', e :: es' => pelem_ok m K e (match es' with [] => allow_empty_top | _ => false end) /\ pelems_ok m Ks' es' allow_empty_top
  | _, _ => True
  end.
Fixpoint pelems_ok_b (m : bmem) (Ks : list Z) (es : list pelem) (allow_empty_top : bool) : bool :=
  match Ks, es with
  | K :: Ks', e :: es' => pelem_ok_b m K e (match es' with [] => allow_empty_top | _ => false end) && pelems_ok_b m Ks' es' allow_empty_top
  | _, _ => true
  end.

Definition pk_blocks (pk : packg) : list (Z * Z) :=
  (sb_data (p_sb pk), sb_alloc (p_sb pk)) ::
  (if v_begin (p_evec pk) =? 0 then [] else [(v_begin (p_evec pk), v_bytes (p_evec pk))]).

Definition OP_SIZE : Z := 32.
Definition SBUF_HDR : Z := 24.
Definition pk_regions (pk : packg) (z : zoneg) : list (Z * Z) :=
  (p_op pk, OP_SIZE) :: (sb_addr (p_sb pk), SBUF_HDR) :: (p_root pk, OBJ_SIZE) :: pk_blocks pk ++ map chunk_block (z_chunks z).

Definition PK_CORE (live : Z -> Z -> Prop) (m : bmem) (z : zoneg) (pk : packg) (cur : Z) (pop : bool) : Prop :=
  op_at m pk cur /\ sbuf_at m (p_sb pk) /\ sbuf_valid (p_sb pk) /\ pow2_b (sb_alloc (p_sb pk) / SBUF_INIT) = true /\ sb_alloc (p_sb pk) mod SBUF_INIT = 0 /\

  v_elt (p_evec pk) = ELEM_SIZE /\ v_size (p_evec pk) = Z.of_nat (length (p_elems pk)) /\
  ((v_begin (p_evec pk) = 0 /\ v_cap (p_evec pk) = 0 /\ p_elems pk = [])
   \/ (vec_valid (p_evec pk) /\ pow2_b (v_cap (p_evec pk)) = true /\ pelems_at m (v_begin (p_evec pk)) (p_elems pk))) /\
  Z.of_nat (length (p_elems pk)) <= LIMIT + 1 /\
  Forall (fun e => pe_key e = true -> pe_map e = true) (p_elems pk) /\
  pelems_ok m (pcontainers (p_root pk) (p_elems pk)) (p_elems pk) pop /\

  (exists t, tree_at m z (p_root pk) t) /\ zone_at m z /\ zone_valid z /\
  (forall b, In b (pk_blocks pk) -> live (fst b) (snd b)) /\
  (forall c, In c (z_chunks z) -> live (fst c) (CHUNK_HDR + snd c)) /\ regions_disj (pk_regions pk z) /\
  p_op pk <> 0 /\ p_op pk mod 8 = 0 /\ p_root pk <> 0 /\ p_root pk mod 8 = 0 /\ sb_addr (p_sb pk) mod 8 = 0.

Definition PK_HEAD_INV (live : Z -> Z -> Prop) (m : bmem) (z : zoneg) (pk : packg) (cur : Z) : Prop :=
  PK_CORE live m z pk cur false /\
  cur = match last_opt (p_elems pk) with None => p_root pk | Some e => pe_obj e end /\
  (exists t, tree_at m z cur t).

Definition PK_POP_INV (live : Z -> Z -> Prop) (m : bmem) (z : zoneg) (pk : packg) (cur : Z) : Prop :=
  PK_CORE live m z pk cur true /\ p_elems pk <> [].

Definition SBUF_WRITE_PRE (live : Z -> Z -> Prop) (m : bmem) (s : sbufg) (this buf len : Z) : Prop :=
  this = sb_addr s /\ sbuf_at m s /\ sbuf_valid s /\ live (sb_data s) (sb_alloc s) /\
  0 <= len <= LIMIT + 1 /\ (buf = 0 -> len = 0) /\ (buf <> 0 -> readable m buf (Z.to_nat len)).

Definition PK_CORE_b (fuel : nat) (live_b : Z -> Z -> bool) (m : bmem) (z : zoneg) (pk : packg) (cur : Z) (pop : bool) : bool :=
  op_at_b m pk cur && sbuf_at_b m (p_sb pk) && sbuf_valid_b (p_sb pk) && pow2_b (sb_alloc (p_sb pk) / SBUF_INIT) && (sb_alloc (p_sb pk) mod SBUF_INIT =? 0) &&
  (v_elt (p_evec pk) =? ELEM_SIZE) && (v_size (p_evec pk) =? Z.of_nat (length (p_elems pk))) &&
  (((v_begin (p_evec pk) =? 0) && (v_cap (p_evec pk) =? 0) && listZ_eqb_nil (p_elems pk))
   || (vec_valid_b (p_evec pk) && pow2_b (v_cap (p_evec pk)) && pelems_at_b m (v_begin (p_evec pk)) (p_elems pk))) &&
  (Z.of_nat (length (p_elems pk)) <=? LIMIT + 1) &&
  forallb (fun e => negb (pe_key e) || pe_map e) (p_elems pk) &&
  pelems_ok_b m (pcontainers (p_root pk) (p_elems pk)) (p_elems pk) pop &&
  node_ok_b fuel m z (p_root pk) && zone_at_b m z && zone_valid_b z &&
  forallb (fun b => live_b (fst b) (snd b)) (pk_blocks pk) &&
  forallb (fun c => live_b (fst c) (CHUNK_HDR + snd c)) (z_chunks z) && regions_disj_b (pk_regions pk z) &&
  negb (p_op pk =? 0) && (p_op pk mod 8 =? 0) && negb (p_root pk =? 0) && (p_root pk mod 8 =? 0) && (sb_addr (p_sb pk) mod 8 =? 0).

Definition PK_HEAD_INV_b (fuel : nat) (live_b : Z -> Z -> bool) (m : bmem) (z : zoneg) (pk : packg) (cur : Z) : bool :=
  PK_CORE_b fuel live_b m z pk cur false &&
  (cur =? match last_opt (p_elems pk) with None => p_root pk | Some e => pe_obj e end) &&
  node_ok_b fuel m z cur.
Definition PK_POP_INV_b (fuel : nat) (live_b : Z -> Z -> bool) (m : bmem) (z : zoneg) (pk : packg) (cur : Z) : bool :=
  PK_CORE_b fuel live_b m z pk cur true && negb (listZ_eqb_nil (p_elems pk)).
Definition SBUF_WRITE_PRE_b (live_b : Z -> Z -> bool) (m : bmem) (s : sbufg) (this buf len : Z) : bool :=
  (this =? sb_addr s) && sbuf_at_b m s && sbuf_valid_b s && live_b (sb_data s) (sb_alloc s) &&
  (0 <=? len) && (len <=? LIMIT + 1) && (if buf =? 0 then len =? 0 else readable_b m buf (Z.to_nat len)).

Local Ltac zbool2 :=
  repeat match goal with
    | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : negb (_ =? _) = true |- _ => apply negb_true_iff in H; apply Z.eqb_neq in H
    | H : negb (Nat.eqb _ _) = true |- _ => apply negb_true_iff in H; apply Nat.eqb_neq in H
    | H : in_zone_b _ _ _ = true |- _ => apply in_zone_b_ok in H
    | H : readable_b _ _ _ = true |- _ => apply readable_b_ok in H
    | H : u64_b _ _ _ = true |- _ => apply u64_b_ok in H
    | H : u32_b _ _ _ = true |- _ => apply u32_b_ok in H
    | H : u8_b _ _ _ = true |- _ => apply u8_b_ok in H
    end.

Lemma vec_valid_b_ok : forall v, vec_valid_b v = true -> vec_valid v.
Proof. intros v H. unfold vec_valid_b, vec_valid in *. zbool2. lia. Qed.
Lemma level_valid_b_ok : forall l, level_valid_b l = true -> level_valid l.
Proof. intros l H. unfold level_valid_b, level_valid in *. zbool2. lia. Qed.
Lemma sbuf_valid_b_ok : forall s, sbuf_valid_b s = true -> sbuf_valid s.
Proof. intros s H. unfold sbuf_valid_b, sbuf_valid in *. zbool2. lia. Qed.
Lemma zone_valid_b_ok : forall z, zone_valid_b z = true -> zone_valid z.
Proof.
  intros z H. unfold zone_valid_b in H. zbool2.
  match goal with Hf : forallb _ (z_chunks z) = true |- _ => rename Hf into HF end.
  match goal with Hn : length (z_chunks z) <> 0%nat |- _ => rename Hn into HN end.
  unfold zone_valid. split; [destruct (z_chunks z); [cbn in HN; congruence|discriminate]|].
  split; [assumption|]. split.
  { intros c' Hc. eapply forallb_forall in HF; [|exact Hc]. cbn in HF. zbool2. lia. }
  repeat split; try lia.
  match goal with Hp : pairwise_b _ _ = true |- _ => eapply pairwise_b_ok; [|exact Hp] end.
  intros x y Hxy. now apply rdisj_b_ok.
Qed.
Lemma levels_alloc_b_ok : forall z ls, levels_alloc_b z ls = true -> levels_alloc z ls.
Proof.
  intros z ls H. unfold levels_alloc_b in H. apply andb_prop in H. destruct H as [H1 H2]. split.
  - intros l Hl. eapply forallb_forall in H1; [|exact Hl]. now apply in_alloc_b_ok.
  - eapply pairwise_b_ok; [|exact H2]. intros x y Hxy. now apply rdisj_b_ok.
Qed.
Lemma cell_ok_b_ok : forall z ls c, cell_ok_b z ls c = true -> cell_ok z ls c.
Proof.
  intros z ls c H. unfold cell_ok_b in H. apply andb_prop in H. destruct H as [H1 H2]. split; [now apply in_alloc_b_ok|].
  intros l Hl. eapply forallb_forall in H2; [|exact Hl]. now apply rdisj_b_ok.
Qed.

Lemma node_ok_b_ok : forall fuel m z a, node_ok_b fuel m z a = true -> exists o, tree_at m z a o.
Proof.
  intros fuel m z a H. unfold node_ok_b in H. destruct (decode_obj fuel m a) as [o|] eqn:E; [|discriminate].
  zbool2. exists o. split; [now apply obj_at_b_ok| now apply tree_wf_b_ok].
Qed.
Lemma cnode_ok_b_ok : forall fuel m z ls a, cnode_ok_b fuel m z ls a = true ->
  exists o, tree_at m z a o /\ (forall c, In c (obj_cells a o) -> cell_ok z ls c).
Proof.
  intros fuel m z ls a H. unfold cnode_ok_b in H. destruct (decode_obj fuel m a) as [o|] eqn:E; [|discriminate].
  zbool2. exists o. split; [split; [now apply obj_at_b_ok| now apply tree_wf_b_ok]|].
  intros c Hc. apply cell_ok_b_ok. match goal with Hf : forallb _ _ = true |- _ => eapply forallb_forall in Hf; [exact Hf|exact Hc] end.
Qed.
Lemma cnode_tl_ok_b_ok : forall fuel m z ls a, cnode_tl_ok_b fuel m z ls a = true ->
  exists o, tree_at m z a o /\ (forall c, In c (tl (obj_cells a o)) -> cell_ok z ls c).
Proof.
  intros fuel m z ls a H. unfold cnode_tl_ok_b in H. destruct (decode_obj fuel m a) as [o|] eqn:E; [|discriminate].
  zbool2. exists o. split; [split; [now apply obj_at_b_ok| now apply tree_wf_b_ok]|].
  intros c Hc. apply cell_ok_b_ok. match goal with Hf : forallb _ _ = true |- _ => eapply forallb_forall in Hf; [exact Hf|exact Hc] end.
Qed.
Lemma completed_wf_b_ok : forall fuel m z ls, completed_wf_b fuel m z ls = true -> completed_wf m z ls.
Proof.
  intros fuel m z ls H l Hl i Hi. unfold completed_wf_b in H. eapply forallb_forall in H; [|exact Hl].
  assert (Hin : In i (zseq 0 (Z.to_nat (lv_k l)))) by (apply zseq_in; rewrite Z2Nat.id by lia; lia).
  eapply forallb_forall in H; [|exact Hin].
  now apply cnode_ok_b_ok in H.
Qed.
Lemma forallb_Forall : forall {A} (f : A -> bool) (P : A -> Prop) l,
  (forall x, f x = true -> P x) -> forallb f l = true -> Forall P l.
Proof. intros A f P l Hf H. apply Forall_forall. intros x Hx. apply Hf. eapply forallb_forall in H; eauto. Qed.
Lemma addr_sane_b_ok : forall g, addr_sane_b g = true ->
  u_ctx g <> 0 /\ u_vis g <> 0 /\ u_ctx g mod 8 = 0 /\ u_vis g mod 8 = 0 /\ 0 < u_len g /\ 0 < u_data g /\ u_pe g < 2^47.
Proof. intros g H. unfold addr_sane_b in H. zbool2. repeat split; auto. Qed.

Lemma UNP_CORE_b_ok : forall fuel live_b (live : Z -> Z -> Prop) m g cur cs trail,
  (forall a n, live_b a n = true -> live a n) ->
  UNP_CORE_b fuel live_b m g cur cs trail = true -> UNP_CORE live m g cur cs trail.
Proof.
  intros fuel live_b live m g cur cs trail Hlive H. unfold UNP_CORE_b in H. zbool2.
  unfold UNP_CORE.
  repeat match goal with |- _ /\ _ => split end;
    try (now apply ctx_at_b_ok); try (now apply vis_at_b_ok); try (now apply zone_at_b_ok); try (now apply stacks_at_b_ok);
    try (now apply conts_at_b_ok); try (now apply vec_valid_b_ok); try (now apply zone_valid_b_ok); try (now apply levels_alloc_b_ok); try (now apply regions_disj_b_ok);
    try (eapply completed_wf_b_ok; eassumption); try assumption; try lia.
  all: try match goal with Ha : addr_sane_b _ = true |- _ => apply addr_sane_b_ok in Ha; tauto end.
  - eapply forallb_Forall; [apply level_valid_b_ok| eassumption].
  - intros b Hb. apply Hlive. match goal with Hf : forallb _ (unp_blocks _) = true |- _ => eapply forallb_forall in Hf; [exact Hf|exact Hb] end.
Qed.

Lemma UNP_HEAD_INV_b_ok : forall fuel live_b (live : Z -> Z -> Prop) m g cur pe offv fta nreg cs trail,
  (forall a n, live_b a n = true -> live a n) ->
  UNP_HEAD_INV_b fuel live_b m g cur pe offv fta nreg cs trail = true -> UNP_HEAD_INV live m g cur pe offv fta nreg cs trail.
Proof.
  intros fuel live_b live m g cur pe offv fta nreg cs trail Hlive H. unfold UNP_HEAD_INV_b in H.
  apply andb_prop in H. destruct H as [H Hn]. apply andb_prop in H. destruct H as [H Hmode].
  zbool2. unfold UNP_HEAD_INV. split; [eapply UNP_CORE_b_ok; eassumption|].
  repeat match goal with |- _ /\ _ => split end; try lia.
  all: try (apply orb_prop in Hmode; destruct Hmode as [Hm|Hm]; zbool2; [left; lia|right];
            repeat match goal with H : _ || _ = true |- _ => apply orb_prop in H; destruct H end; zbool2; lia).
  all: apply orb_prop in Hn; destruct Hn as [Hn|Hn]; zbool2; lia.
Qed.

Lemma CONSUME_INV_b_ok : forall fuel live_b (live : Z -> Z -> Prop) m g cur cs trail,
  (forall a n, live_b a n = true -> live a n) ->
  CONSUME_INV_b fuel live_b m g cur cs trail = true -> CONSUME_INV live m g cur cs trail.
Proof.
  intros fuel live_b live m g cur cs trail Hlive H. unfold CONSUME_INV_b in H. zbool2. unfold CONSUME_INV.
  split; [eapply UNP_CORE_b_ok; eassumption|]. repeat match goal with |- _ /\ _ => split end; try lia.
  eapply cnode_tl_ok_b_ok; eassumption.
Qed.

Lemma pelem_ok_b_ok : forall m K e ae, pelem_ok_b m K e ae = true -> pelem_ok m K e ae.
Proof.
  intros m K e ae H. unfold pelem_ok_b in H. apply andb_prop in H. destruct H as [Ht H].
  destruct (rdZ m (K+8) 4) as [N|] eqn:EN; [|discriminate]. destruct (rdZ m (K+16) 8) as [Q|] eqn:EQ; [|discriminate].
  exists N, Q. apply u32_b_ok in Ht. split; [exact Ht|]. split; [exact EN|]. split; [exact EQ|].
  apply orb_prop in H. destruct H as [H|H]; zbool2; [left; lia| right].
  destruct ae; [|discriminate]. repeat split; auto.
Qed.
Lemma pelems_ok_b_ok : forall m Ks es top, pelems_ok_b m Ks es top = true -> pelems_ok m Ks es top.
Proof.
  intros m Ks. induction Ks as [|K Ks IH]; intros [|e es] top H; cbn in *; try exact I.
  zbool2. split; [now apply pelem_ok_b_ok| now apply IH].
Qed.

Lemma PK_CORE_b_ok : forall fuel live_b (live : Z -> Z -> Prop) m z pk cur pop,
  (forall a n, live_b a n = true -> live a n) ->
  PK_CORE_b fuel live_b m z pk cur pop = true -> PK_CORE live m z pk cur pop.
Proof.
  intros fuel live_b live m z pk cur pop Hlive H. unfold PK_CORE_b in H.

  repeat (apply andb_prop in H; let H1 := fresh "K" in destruct H as [H H1]).
  unfold PK_CORE.
  split. { split; [now apply u64_b_ok| now apply vec_at_b_ok]. }
  split; [now apply sbuf_at_b_ok|]. split; [now apply sbuf_valid_b_ok|].
  split; [assumption|]. split; [now apply Z.eqb_eq|].
  split; [now apply Z.eqb_eq|]. split; [now apply Z.eqb_eq|].
  split.
  { apply orb_prop in K13. destruct K13 as [Hv|Hv]; zbool2.
    - left. repeat split; auto. destruct (p_elems pk); [reflexivity|discriminate].
    - right. split; [now apply vec_valid_b_ok|]. split; [assumption| now apply pelems_at_b_ok]. }
  split; [now apply Z.leb_le|].
  split. { eapply forallb_Forall; [|exact K11]. intros e He. cbn in He. intros Hk. apply orb_prop in He.
           destruct He as [He|He]; [rewrite Hk in He; discriminate| exact He]. }
  split; [now apply pelems_ok_b_ok|].
  split; [eapply node_ok_b_ok; eassumption|].
  split; [now apply zone_at_b_ok|]. split; [now apply zone_valid_b_ok|].
  split. { intros b Hb. apply Hlive. eapply forallb_forall in K6; [exact K6|exact Hb]. }
  split. { intros c Hc. apply Hlive. eapply forallb_forall in K5; [|exact Hc]. exact K5. }
  split; [now apply regions_disj_b_ok|].
  zbool2. repeat split; assumption.
Qed.

Lemma last_opt_spec : forall {A} (l : list A), match last_opt l with None => l = [] | Some x => exists l', l = l' ++ [x] end.
Proof.
  intros A l. unfold last_opt. destruct (rev l) as [|x r] eqn:E.
  - rewrite <- (rev_involutive l), E. reflexivity.
  - exists (rev r). rewrite <- (rev_involutive l), E. cbn. reflexivity.
Qed.

Lemma PK_HEAD_INV_b_ok : forall fuel live_b (live : Z -> Z -> Prop) m z pk cur,
  (forall a n, live_b a n = true -> live a n) ->
  PK_HEAD_INV_b fuel live_b m z pk cur = true -> PK_HEAD_INV live m z pk cur.
Proof.
  intros fuel live_b live m z pk cur Hlive H. unfold PK_HEAD_INV_b in H. zbool2. unfold PK_HEAD_INV.
  split; [eapply PK_CORE_b_ok; eassumption|]. split; [assumption|]. eapply node_ok_b_ok; eassumption.
Qed.
Lemma PK_POP_INV_b_ok : forall fuel live_b (live : Z -> Z -> Prop) m z pk cur,
  (forall a n, live_b a n = true -> live a n) ->
  PK_POP_INV_b fuel live_b m z pk cur = true -> PK_POP_INV live m z pk cur.
Proof.
  intros fuel live_b live m z pk cur Hlive H. unfold PK_POP_INV_b in H. zbool2. unfold PK_POP_INV.
  split; [eapply PK_CORE_b_ok; eassumption|].
  match goal with Hn : negb (listZ_eqb_nil _) = true |- _ => destruct (p_elems pk); [discriminate|congruence] end.
Qed.
Lemma SBUF_WRITE_PRE_b_ok : forall live_b (live : Z -> Z -> Prop) m s this buf len,
  (forall a n, live_b a n = true -> live a n) ->
  SBUF_WRITE_PRE_b live_b m s this buf len = true -> SBUF_WRITE_PRE live m s this buf len.
Proof.
  intros live_b live m s this buf len Hlive H. unfold SBUF_WRITE_PRE_b in H. zbool2. unfold SBUF_WRITE_PRE.
  repeat match goal with |- _ /\ _ => split end; auto using sbuf_at_b_ok, sbuf_valid_b_ok; try lia.
  - match goal with Hb : (if ?c then _ else _) = true |- _ => destruct (Z.eqb_spec buf 0); zbool2; [lia| intros; contradiction] end.
  - match goal with Hb : (if ?c then _ else _) = true |- _ => destruct (Z.eqb_spec buf 0); zbool2; [intros; contradiction| auto] end.
Qed.
