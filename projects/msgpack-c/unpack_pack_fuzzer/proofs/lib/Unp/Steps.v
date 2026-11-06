(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Arguments Z.mul : simpl never.
Local Arguments Z.add : simpl never.
Local Arguments Z.sub : simpl never.
Local Arguments Z.div : simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow : simpl never.
Local Ltac splits := repeat match goal with |- _ /\ _ => split end.

Definition new_level (t : ctype) (n P : Z) : level := mkLevel t n n P.

Lemma new_level_k : forall t n P, t <> CT_MAP_VALUE -> lv_k (new_level t n P) = 0.
Proof. intros [| |] n P H; cbn; try lia. exfalso; now apply H. Qed.
Lemma new_level_slot : forall t n P, t <> CT_MAP_VALUE -> lv_slot (new_level t n P) = P.
Proof. intros t n P H. unfold lv_slot. rewrite new_level_k by exact H. cbn [new_level lv_P]. lia. Qed.
Lemma new_level_valid : forall t n P, 1 <= n <= LIMIT -> P <> 0 -> P mod 8 = 0 -> level_valid (new_level t n P).
Proof. intros t n P Hn HP HA. unfold level_valid, new_level; cbn. lia. Qed.

Definition push_level (ls : list level) (t : ctype) (n P : Z) : list level := ls ++ [new_level t n P].

Lemma push_level_valid : forall ls t n P,
  Forall level_valid ls -> 1 <= n <= LIMIT -> P <> 0 -> P mod 8 = 0 -> Forall level_valid (push_level ls t n P).
Proof. intros. unfold push_level. apply Forall_app. split; [assumption|]. constructor; [now apply new_level_valid|constructor]. Qed.
Lemma push_level_length : forall ls t n P, length (push_level ls t n P) = S (length ls).
Proof. intros. unfold push_level. rewrite length_app. cbn. lia. Qed.
Lemma push_level_cur_slot : forall root ls t n P, t <> CT_MAP_VALUE -> cur_slot root (push_level ls t n P) = P.
Proof. intros. unfold push_level. rewrite cur_slot_snoc. now apply new_level_slot. Qed.
Lemma push_level_containers : forall root ls t n P,
  containers root (push_level ls t n P) = containers root ls ++ [cur_slot root ls].
Proof. intros. unfold push_level. rewrite containers_app. cbn. reflexivity. Qed.

Inductive cstep : Type :=
| CS_Ret (l' : level)
| CS_Pop.

Definition consume_top (l : level) : cstep :=
  match lv_t l with
  | CT_ARRAY_ITEM => if lv_rest l =? 1 then CS_Pop else CS_Ret (mkLevel CT_ARRAY_ITEM (lv_n l) (lv_rest l - 1) (lv_P l))
  | CT_MAP_KEY => CS_Ret (mkLevel CT_MAP_VALUE (lv_n l) (lv_rest l) (lv_P l))
  | CT_MAP_VALUE => if lv_rest l =? 1 then CS_Pop else CS_Ret (mkLevel CT_MAP_KEY (lv_n l) (lv_rest l - 1) (lv_P l))
  end.

Lemma consume_top_ret : forall l l', consume_top l = CS_Ret l' -> level_valid l ->
  lv_slot l' = lv_slot l + OBJ_SIZE /\ lv_P l' = lv_P l /\ lv_n l' = lv_n l /\ lv_k l' = lv_k l + 1 /\ level_valid l' /\
  lv_bytes l' = lv_bytes l /\ container_type (lv_t l') = container_type (lv_t l).
Proof.
  intros l l' H V. unfold consume_top in H. unfold level_valid in V.
  destruct l as [t n r P]; cbn in *. destruct t; cbn in H.
  - destruct (Z.eqb_spec r 1); [discriminate|]. inversion H; subst. unfold lv_slot, lv_k, lv_bytes, level_valid; cbn. unfold OBJ_SIZE. lia.
  - inversion H; subst. unfold lv_slot, lv_k, lv_bytes, level_valid; cbn. unfold OBJ_SIZE. lia.
  - destruct (Z.eqb_spec r 1); [discriminate|]. inversion H; subst. unfold lv_slot, lv_k, lv_bytes, level_valid; cbn. unfold OBJ_SIZE. lia.
Qed.
Lemma consume_top_pop : forall l, consume_top l = CS_Pop -> lv_rest l = 1 /\ lv_t l <> CT_MAP_KEY.
Proof.
  intros [t n r P] H. unfold consume_top in H; cbn in *. destruct t; cbn in H.
  - destruct (Z.eqb_spec r 1); [split; [assumption|congruence]|discriminate].
  - discriminate.
  - destruct (Z.eqb_spec r 1); [split; [assumption|congruence]|discriminate].
Qed.

Lemma pop_full : forall l, level_valid l -> lv_rest l = 1 -> lv_t l <> CT_MAP_KEY -> (lv_k l + 1) * OBJ_SIZE = lv_bytes l.
Proof. intros [t n r P] V Hr Ht. unfold level_valid, lv_k, lv_bytes in *; cbn in *. destruct t; cbn; try congruence; unfold OBJ_SIZE; lia. Qed.

Fixpoint consume_rev (rls : list level) : list level * Z :=
  match rls with
  | [] => ([], PARSE_SUCCESS)
  | l :: rest => match consume_top l with
                 | CS_Ret l' => (l' :: rest, PARSE_CONTINUE)
                 | CS_Pop => consume_rev rest
                 end
  end.
Definition consume (ls : list level) : list level * Z :=
  let rc := consume_rev (rev ls) in (rev (fst rc), snd rc).

Lemma consume_rev_spec : forall rls,
  (snd (consume_rev rls) = PARSE_SUCCESS /\ fst (consume_rev rls) = [] /\ Forall (fun l => consume_top l = CS_Pop) rls)
  \/ (snd (consume_rev rls) = PARSE_CONTINUE /\
      exists popped l l' rest, rls = popped ++ l :: rest /\ Forall (fun x => consume_top x = CS_Pop) popped /\
                               consume_top l = CS_Ret l' /\ fst (consume_rev rls) = l' :: rest).
Proof.
  induction rls as [|l rest IH]; cbn.
  - left. repeat split; constructor.
  - destruct (consume_top l) as [l'|] eqn:E; cbn.
    + right. split; [reflexivity|]. exists [], l, l', rest. repeat split; auto.
    + destruct IH as [(H1 & H2 & H3)|(H1 & popped & l0 & l0' & rest0 & -> & Hp & Hc & Hf)].
      * left. repeat split; auto.
      * right. split; [exact H1|]. exists (l :: popped), l0, l0', rest0. repeat split; auto.
Qed.

Lemma consume_valid : forall ls, Forall level_valid ls -> Forall level_valid (fst (consume ls)).
Proof.
  intros ls V. unfold consume. cbn. apply Forall_rev.
  assert (Vr : Forall level_valid (rev ls)) by (apply Forall_rev in V; exact V).
  revert Vr. generalize (rev ls) as r. clear. induction r as [|l rest IH]; intros V; cbn; [constructor|].
  inversion V; subst. destruct (consume_top l) as [l'|] eqn:E; cbn.
  - constructor; [|assumption]. eapply consume_top_ret in E; [|eassumption]. tauto.
  - now apply IH.
Qed.
Lemma consume_length : forall ls, (length (fst (consume ls)) <= length ls)%nat.
Proof.
  intros ls. unfold consume. cbn. rewrite length_rev. rewrite <- (length_rev ls).
  generalize (rev ls) as r. clear. induction r as [|l rest IH]; cbn; [lia|].
  destruct (consume_top l); cbn; lia.
Qed.
Lemma consume_code : forall ls, (snd (consume ls) = PARSE_SUCCESS /\ fst (consume ls) = []) \/ (snd (consume ls) = PARSE_CONTINUE /\ fst (consume ls) <> []).
Proof.
  intros ls. unfold consume. cbn. destruct (consume_rev_spec (rev ls)) as [(H1 & H2 & _)|(H1 & p & l & l' & r & _ & _ & _ & Hf)].
  - left. rewrite H2. auto.
  - right. rewrite Hf. split; [exact H1|]. cbn. intros E. apply app_eq_nil in E. destruct E; discriminate.
Qed.

Lemma consume_shape : forall ls, snd (consume ls) = PARSE_CONTINUE ->
  exists keep l l' popped, ls = keep ++ [l] ++ popped /\ fst (consume ls) = keep ++ [l'] /\ consume_top l = CS_Ret l' /\
                           Forall (fun x => consume_top x = CS_Pop) popped.
Proof.
  intros ls Hc. unfold consume in *. cbn in *.
  destruct (consume_rev_spec (rev ls)) as [(H1 & _)|(H1 & popped & l & l' & rest & E & Hp & Hl & Hf)]; [rewrite H1 in Hc; discriminate|].
  exists (rev rest), l, l', (rev popped). rewrite Hf. cbn. repeat split.
  - rewrite <- (rev_involutive ls), E. rewrite rev_app_distr. cbn. rewrite <- app_assoc. reflexivity.
  - exact Hl.
  - now apply Forall_rev.
Qed.

Lemma consume_pop_measure : forall (rest : list level) l, (length rest < length (l :: rest))%nat.
Proof. intros; cbn; lia. Qed.

Definition zone_bump (z : zoneg) (adjusted : Z) : zoneg := mkZone (z_addr z) (z_chunks z) (z_ptr z + adjusted) (z_free z - adjusted).
Definition zone_expand (z : zoneg) (c sz : Z) : zoneg := mkZone (z_addr z) ((c, sz) :: z_chunks z) (c + CHUNK_HDR) sz.

Definition zalloc8_fits (z : zoneg) (size : Z) : Z * zoneg :=
  let aligned := align8 (z_ptr z) in (aligned, zone_bump z (size + (aligned - z_ptr z))).

Definition zalloc1_fits (z : zoneg) (size : Z) : Z * zoneg := (z_ptr z, zone_bump z size).

Definition zalloc_fresh (z : zoneg) (c sz size : Z) : Z * zoneg := (c + CHUNK_HDR, zone_bump (zone_expand z c sz) size).

Lemma in_zone_mono_bump : forall z adj a n, in_zone z a n -> in_zone (zone_bump z adj) a n.
Proof. intros z adj a n (c & Hc & Hi). exists c. split; [exact Hc|exact Hi]. Qed.
Lemma in_zone_mono_expand : forall z c sz a n, in_zone z a n -> in_zone (zone_expand z c sz) a n.
Proof. intros z c sz a n (c0 & Hc & Hi). exists c0. split; [cbn; now right|exact Hi]. Qed.

Lemma zalloc8_fits_ok : forall z size, zone_valid z -> 0 <= size -> 0 <= z_ptr z ->
  size + (align8 (z_ptr z) - z_ptr z) <= z_free z ->
  let r := zalloc8_fits z size in
  zone_valid (snd r) /\ fst r mod 8 = 0 /\ z_ptr z <= fst r /\ fst r + size = z_ptr (snd r) /\
  z_ptr (snd r) <= chunk_hi (hd (0,0) (z_chunks z)) /\
  in_alloc (snd r) (fst r) size /\ z_chunks (snd r) = z_chunks z.
Proof.
  intros z size V Hs Hp Hfit r. subst r. unfold zalloc8_fits, zone_bump. cbn.
  pose proof (align8_spec (z_ptr z) Hp) as (A1 & A2 & A3).
  destruct V as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
  unfold zone_valid, in_alloc; cbn. unfold chunk_lo, chunk_hi in *.
  repeat match goal with |- _ /\ _ => split end; auto; try lia.
Qed.
Lemma zalloc1_fits_ok : forall z size, zone_valid z -> 0 <= size <= z_free z ->
  let r := zalloc1_fits z size in
  zone_valid (snd r) /\ fst r = z_ptr z /\ fst r + size = z_ptr (snd r) /\ z_ptr (snd r) <= chunk_hi (hd (0,0) (z_chunks z)) /\
  in_alloc (snd r) (fst r) size /\ z_chunks (snd r) = z_chunks z.
Proof.
  intros z size V Hs r. subst r. unfold zalloc1_fits, zone_bump. cbn.
  destruct V as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
  unfold zone_valid, in_alloc; cbn. unfold chunk_lo, chunk_hi in *.
  repeat match goal with |- _ /\ _ => split end; auto; try lia.
Qed.

Lemma zalloc_fresh_ok : forall z c sz size, zone_valid z -> 0 < c -> c mod 16 = 0 -> CHUNK_SIZE0 <= sz -> 0 <= size <= sz ->
  Forall (chunk_disj (c, sz)) (z_chunks z) ->
  let r := zalloc_fresh z c sz size in
  zone_valid (snd r) /\ fst r = c + CHUNK_HDR /\ fst r mod 8 = 0 /\ fst r + size = z_ptr (snd r) /\
  z_ptr (snd r) <= chunk_hi (c, sz) /\ in_alloc (snd r) (fst r) size /\
  z_chunks (snd r) = (c, sz) :: z_chunks z.
Proof.
  intros z c sz size V Hc Hm Hsz Hs Hd r. subst r. unfold zalloc_fresh, zone_bump, zone_expand. cbn.
  destruct V as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
  unfold zone_valid, in_alloc, chunk_lo, chunk_hi, CHUNK_HDR in *; cbn.
  repeat match goal with |- _ /\ _ => split end; auto; try lia; try congruence.
  - intros c0 [<-|H]; cbn; [lia| now apply V3].
  - now constructor.
  - rewrite (Z.div_mod c 16) by lia. rewrite Hm, Z.add_0_r. replace (16 * (c / 16) + 8) with ((2 * (c / 16) + 1) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma in_alloc_mono_bump : forall z adj a n, 0 <= adj -> in_alloc z a n -> in_alloc (zone_bump z adj) a n.
Proof. intros z adj a n Hadj [(c & Hc & Hi)|(H1 & H2)]; unfold in_alloc, zone_bump; cbn; [left; eauto|right; lia]. Qed.
Lemma in_alloc_mono_expand : forall z c sz a n, zone_valid z -> in_alloc z a n -> in_alloc (zone_expand z c sz) a n.
Proof.
  intros z c sz a n V [(c0 & Hc & Hi)|(H1 & H2)]; unfold in_alloc, zone_expand; cbn; left.
  - exists c0. split; [|exact Hi]. destruct (z_chunks z); [contradiction|]. cbn in Hc |- *. now right.
  - destruct V as (V1 & _ & _ & V4 & V5 & V6 & _). exists (hd (0,0) (z_chunks z)). destruct (z_chunks z) as [|ch r]; [contradiction|]. cbn in *.
    split; [now left|]. unfold in_chunk. lia.
Qed.
Lemma in_alloc_mono_fresh : forall z c sz size a n, zone_valid z -> 0 <= size -> in_alloc z a n -> in_alloc (snd (zalloc_fresh z c sz size)) a n.
Proof. intros. unfold zalloc_fresh. cbn. apply in_alloc_mono_bump; [assumption|]. now apply in_alloc_mono_expand. Qed.

Lemma in_alloc_chunk : forall z a n, zone_valid z -> in_alloc z a n -> exists ch, In ch (z_chunks z) /\ in_chunk ch a n.
Proof.
  intros z a n V Ha. destruct V as (V1 & _ & _ & V4 & V5 & V6 & _).
  destruct (in_alloc_in_zone z a n V1 ltac:(lia) Ha) as (ch & Hch & Hi). eauto.
Qed.

Lemma in_alloc_fresh_disj : forall z a n lo k, zone_valid z -> 0 <= n -> in_alloc z a n ->
  z_ptr z <= lo -> lo + k <= chunk_hi (hd (0,0) (z_chunks z)) -> rdisj a n lo k.
Proof.
  intros z a n lo k V Hn Ha Hlo Hhi. destruct V as (V1 & _ & V3 & V4 & V5 & V6 & V7).
  destruct Ha as [(c & Hc & Hi)|(H1 & H2)]; [|unfold rdisj; lia].
  destruct (z_chunks z) as [|h r]; [contradiction|]. cbn in *.
  inversion V7 as [|h' r' Hf Hp]; subst. apply Forall_forall with (x := c) in Hf; [|exact Hc].
  unfold chunk_disj, in_chunk, chunk_lo, chunk_hi, rdisj, CHUNK_HDR in *. cbn in *. lia.
Qed.

Lemma in_alloc_outside_disj : forall z a n lo k, zone_valid z -> in_alloc z a n ->
  (forall ch, In ch (z_chunks z) -> rdisj lo k (fst ch) (CHUNK_HDR + snd ch)) -> rdisj a n lo k.
Proof.
  intros z a n lo k V Ha Hout. destruct (in_alloc_chunk z a n V Ha) as (ch & Hch & Hi).
  specialize (Hout ch Hch). unfold in_chunk, chunk_lo, chunk_hi, rdisj, CHUNK_HDR in *. lia.
Qed.

Lemma zalloc8_fresh : forall z size a n, zone_valid z -> 0 <= size -> 0 <= z_ptr z -> 0 <= n ->
  size + (align8 (z_ptr z) - z_ptr z) <= z_free z -> in_alloc z a n -> rdisj a n (fst (zalloc8_fits z size)) size.
Proof.
  intros z size a n V Hs Hp Hn Hfit Ha.
  pose proof (zalloc8_fits_ok z size V Hs Hp Hfit) as (_ & _ & R1 & R2 & R3 & _ & _).
  eapply in_alloc_fresh_disj; eauto. cbn in R2, R3 |- *. unfold zone_bump in *; cbn in *. lia.
Qed.
Lemma zalloc1_fresh : forall z size a n, zone_valid z -> 0 <= size <= z_free z -> 0 <= n ->
  in_alloc z a n -> rdisj a n (fst (zalloc1_fits z size)) size.
Proof.
  intros z size a n V Hs Hn Ha.
  pose proof (zalloc1_fits_ok z size V Hs) as (_ & R0 & R2 & R3 & _ & _).
  eapply in_alloc_fresh_disj; eauto; cbn in *; lia.
Qed.
Lemma zalloc_fresh_fresh : forall z c sz size a n, zone_valid z -> 0 <= size <= sz ->
  Forall (chunk_disj (c, sz)) (z_chunks z) -> in_alloc z a n -> rdisj a n (c + CHUNK_HDR) size.
Proof.
  intros z c sz size a n V Hs Hd Ha. apply (rdisj_sub a n c (CHUNK_HDR + sz)); [| lia | lia | unfold CHUNK_HDR; lia | lia].
  eapply in_alloc_outside_disj; eauto. intros ch Hch. apply Forall_forall with (x := ch) in Hd; [|exact Hch].
  unfold chunk_disj in Hd. cbn in Hd. exact Hd.
Qed.

Definition vec_push (v : vecg) : vecg := mkVec (v_begin v) (v_size v + 1) (v_cap v) (v_elt v).
Definition vec_push_grow (v : vecg) (newbegin : Z) : vecg := mkVec newbegin (v_size v + 1) (2 * v_cap v) (v_elt v).
Lemma vec_push_valid : forall v, vec_valid v -> v_size v < v_cap v -> vec_valid (vec_push v) /\ v_end (vec_push v) = v_end v + v_elt v.
Proof. intros v V H. unfold vec_valid, vec_push, v_end in *; cbn. split; [lia|lia]. Qed.
Lemma vec_push_grow_valid : forall v nb, vec_valid v -> v_size v = v_cap v -> 0 < v_cap v -> nb <> 0 -> nb mod 8 = 0 ->
  vec_valid (vec_push_grow v nb) /\ v_bytes (vec_push_grow v nb) = 2 * v_bytes v.
Proof. intros v nb V H Hc Hn Ha. unfold vec_valid, vec_push_grow, v_bytes in *; cbn. split; [lia|lia]. Qed.
Lemma vec_push_grow_cap32 : forall v nb, cap32_b (v_cap v) = true -> v_cap v < 2^40 -> cap32_b (v_cap (vec_push_grow v nb)) = true.
Proof. intros v nb H Hc. unfold vec_push_grow; cbn. unfold cap32_b in *. now apply cap32_double. Qed.

Inductive next_ret := NR_cont | NR_finish.
Definition pe_next (e : pelem) : pelem * next_ret :=
  if pe_rest e =? 0 then (e, NR_finish)
  else if negb (pe_map e) then
    (if pe_rest e - 1 =? 0 then (mkPE (pe_ptr e) 0 false false, NR_finish)
     else (mkPE (pe_ptr e + OBJ_SIZE) (pe_rest e - 1) false false, NR_cont))
  else if pe_key e then (mkPE (pe_ptr e) (pe_rest e) true false, NR_cont)
  else (if pe_rest e - 1 =? 0 then (mkPE (pe_ptr e) 0 true false, NR_finish)
        else (mkPE (pe_ptr e + KV_SIZE) (pe_rest e - 1) true true, NR_cont)).

Lemma pe_next_cont : forall e e', pe_next e = (e', NR_cont) -> 1 <= pe_rest e ->
  pe_obj e' = pe_obj e + OBJ_SIZE /\ pe_map e' = pe_map e /\
  ((pe_map e = false /\ pe_rest e' = pe_rest e - 1 /\ 1 <= pe_rest e' /\ pe_ptr e' = pe_ptr e + OBJ_SIZE) \/
   (pe_map e = true /\ pe_key e = true /\ pe_key e' = false /\ pe_rest e' = pe_rest e /\ pe_ptr e' = pe_ptr e) \/
   (pe_map e = true /\ pe_key e = false /\ pe_key e' = true /\ pe_rest e' = pe_rest e - 1 /\ 1 <= pe_rest e' /\ pe_ptr e' = pe_ptr e + KV_SIZE)).
Proof.
  intros [p r mp ky] e' H Hr. unfold pe_next in H; cbn in *.
  destruct (Z.eqb_spec r 0); [discriminate|]. destruct mp; cbn in H.
  - destruct ky.
    + inversion H; subst. unfold pe_obj; cbn. unfold OBJ_SIZE. lia.
    + destruct (Z.eqb_spec (r - 1) 0); [discriminate|]. inversion H; subst. unfold pe_obj; cbn. unfold OBJ_SIZE, KV_SIZE. lia.
  - destruct (Z.eqb_spec (r - 1) 0); [discriminate|]. inversion H; subst. unfold pe_obj; cbn. unfold OBJ_SIZE. lia.
Qed.
Lemma pe_next_finish : forall e e', pe_next e = (e', NR_finish) -> pe_rest e = 0 \/ (pe_rest e = 1 /\ (pe_map e = false \/ pe_key e = false)).
Proof.
  intros [p r mp ky] e' H. unfold pe_next in H; cbn in *.
  destruct (Z.eqb_spec r 0); [now left|]. destruct mp; cbn in H.
  - destruct ky; [discriminate|]. destruct (Z.eqb_spec (r - 1) 0); [|discriminate]. right. split; [lia|now right].
  - destruct (Z.eqb_spec (r - 1) 0); [|discriminate]. right. split; [lia|now left].
Qed.

Lemma pe_next_ptr_formula : forall e e' N Q, pe_next e = (e', NR_cont) -> 1 <= pe_rest e <= N ->
  pe_ptr e = Q + OBJ_SIZE * pe_per e * (N - pe_rest e) ->
  pe_ptr e' = Q + OBJ_SIZE * pe_per e' * (N - pe_rest e') /\ 1 <= pe_rest e' <= N.
Proof.
  intros e e' N Q H Hr Hp. pose proof (pe_next_cont e e' H ltac:(lia)) as (Ho & Hm & C).
  unfold pe_per in *. rewrite Hm.
  destruct C as [(M & R & R1 & P)|[(M & K & K' & R & P)|(M & K & K' & R & R1 & P)]]; rewrite M in *; rewrite R, P, Hp; unfold OBJ_SIZE, KV_SIZE in *; split; try lia.
Qed.

Definition pk_push (es : list pelem) (ptr n : Z) (is_map : bool) : list pelem := es ++ [mkPE ptr n is_map is_map].
Definition pk_pop (es : list pelem) : list pelem := removelast es.
Lemma pk_pop_length : forall es e, pk_pop (es ++ [e]) = es.
Proof. intros. unfold pk_pop, removelast. rewrite rev_app_distr. cbn. apply rev_involutive. Qed.
Lemma pk_pop_measure : forall es e, (length (pk_pop (es ++ [e])) < length (es ++ [e]))%nat.
Proof. intros. rewrite pk_pop_length, length_app. cbn. lia. Qed.

Definition pack_bound (root : obj) : nat := obj_size root.
Lemma pack_bound_pos : forall o, (0 < pack_bound o)%nat.
Proof. intros o. unfold pack_bound. destruct o; cbn; lia. Qed.

Lemma tree_wf_arr : forall m z p kids,
  tree_wf m z (OArr p kids) <->
  (Z.of_nat (length kids) <= LIMIT /\ (kids = [] <-> p = 0) /\
   (kids <> [] -> p mod 8 = 0 /\ in_zone z p (OBJ_SIZE * Z.of_nat (length kids))) /\ trees_wf m z kids).
Proof.
  intros m z p kids. cbn [tree_wf].
  assert (E : (fix wfl (l : list obj) : Prop := match l with [] => True | o' :: l' => tree_wf m z o' /\ wfl l' end) kids <-> trees_wf m z kids).
  { induction kids as [|o l IH]; cbn [trees_wf]; [tauto|]. rewrite <- IH. tauto. }
  rewrite E. tauto.
Qed.
Lemma tree_wf_map : forall m z p kids,
  tree_wf m z (OMap p kids) <->
  (even_len kids = true /\ Z.of_nat (length kids) / 2 <= LIMIT /\ (kids = [] <-> p = 0) /\
   (kids <> [] -> p mod 8 = 0 /\ in_zone z p (OBJ_SIZE * Z.of_nat (length kids))) /\ trees_wf m z kids).
Proof.
  intros m z p kids. cbn [tree_wf].
  assert (E : (fix wfl (l : list obj) : Prop := match l with [] => True | o' :: l' => tree_wf m z o' /\ wfl l' end) kids <-> trees_wf m z kids).
  { induction kids as [|o l IH]; cbn [trees_wf]; [tauto|]. rewrite <- IH. tauto. }
  rewrite E. tauto.
Qed.
Lemma trees_wf_forall : forall m z kids, trees_wf m z kids <-> (forall o, In o kids -> tree_wf m z o).
Proof.
  intros m z kids. induction kids as [|o l IH]; cbn [trees_wf].
  - split; [intros _ o []|tauto].
  - rewrite IH. split.
    + intros [H1 H2] o' [<-|Ho']; auto.
    + intros H. split; [apply H; now left|]. intros o' Ho'. apply H. now right.
Qed.

Fixpoint kids_cells (q : Z) (l : list obj) : list Z :=
  match l with [] => [] | o :: l' => obj_cells q o ++ kids_cells (q + OBJ_SIZE) l' end.
Lemma obj_cells_arr : forall a p kids, obj_cells a (OArr p kids) = a :: kids_cells p kids.
Proof. intros a p kids. reflexivity. Qed.
Lemma obj_cells_map : forall a p kids, obj_cells a (OMap p kids) = a :: kids_cells p kids.
Proof. intros a p kids. reflexivity. Qed.
Lemma obj_cells_root : forall a o, In a (obj_cells a o).
Proof. intros a o. destruct o; cbn; now left. Qed.
Lemma obj_cells_hd : forall a o, obj_cells a o = a :: tl (obj_cells a o).
Proof. intros a o. destruct o; reflexivity. Qed.
Lemma kids_cells_app : forall q l1 l2, kids_cells q (l1 ++ l2) = kids_cells q l1 ++ kids_cells (q + OBJ_SIZE * Z.of_nat (length l1)) l2.
Proof.
  intros q l1. revert q. induction l1 as [|o l IH]; intros q l2.
  - cbn [app kids_cells length Z.of_nat]. f_equal. f_equal. lia.
  - cbn [app kids_cells length]. rewrite IH, <- app_assoc. f_equal. f_equal. f_equal. rewrite Nat2Z.inj_succ. unfold OBJ_SIZE. lia.
Qed.
Lemma in_kids_cells : forall c q kids, In c (kids_cells q kids) <->
  exists i o, nth_error kids i = Some o /\ In c (obj_cells (q + OBJ_SIZE * Z.of_nat i) o).
Proof.
  intros c q kids. revert q. induction kids as [|o l IH]; intros q; cbn [kids_cells].
  - split; [intros []|intros (i & o & H & _)]. destruct i; discriminate.
  - rewrite in_app_iff, IH. split.
    + intros [H|(i & o' & Hn & Hc)].
      * exists 0%nat, o. split; [reflexivity|]. cbn [Z.of_nat]. now replace (q + OBJ_SIZE * 0) with q by lia.
      * exists (S i), o'. split; [exact Hn|]. rewrite Nat2Z.inj_succ. now replace (q + OBJ_SIZE * Z.succ (Z.of_nat i)) with (q + OBJ_SIZE + OBJ_SIZE * Z.of_nat i) by lia.
    + intros (i & o' & Hn & Hc). destruct i as [|i].
      * left. cbn in Hn. inversion Hn; subst. cbn [Z.of_nat] in Hc. now replace (q + OBJ_SIZE * 0) with q in Hc by lia.
      * right. exists i, o'. split; [exact Hn|]. rewrite Nat2Z.inj_succ in Hc. now replace (q + OBJ_SIZE + OBJ_SIZE * Z.of_nat i) with (q + OBJ_SIZE * Z.succ (Z.of_nat i)) by lia.
Qed.

Lemma objs_at_nth : forall m q kids, objs_at m q kids <-> (forall i o, nth_error kids i = Some o -> obj_at m (q + OBJ_SIZE * Z.of_nat i) o).
Proof.
  intros m q kids. revert q. induction kids as [|o l IH]; intros q; cbn [objs_at].
  - split; [intros _ [|i] o H; discriminate|tauto].
  - rewrite IH. split.
    + intros [H1 H2] [|i] o' Hn.
      * cbn in Hn. inversion Hn; subst. cbn [Z.of_nat]. now replace (q + OBJ_SIZE * 0) with q by lia.
      * cbn in Hn. rewrite Nat2Z.inj_succ. replace (q + OBJ_SIZE * Z.succ (Z.of_nat i)) with (q + OBJ_SIZE + OBJ_SIZE * Z.of_nat i) by lia. now apply H2.
    + intros H. split.
      * specialize (H 0%nat o eq_refl). cbn [Z.of_nat] in H. now replace (q + OBJ_SIZE * 0) with q in H by lia.
      * intros i o' Hn. specialize (H (S i) o' Hn). rewrite Nat2Z.inj_succ in H.
        replace (q + OBJ_SIZE * Z.succ (Z.of_nat i)) with (q + OBJ_SIZE + OBJ_SIZE * Z.of_nat i) in H by lia. exact H.
Qed.

Definition readable_mono (m m' : bmem) : Prop := forall a n, readable m a n -> readable m' a n.
Lemma readable_mono_refl : forall m, readable_mono m m. Proof. now intros m a n. Qed.
Lemma readable_mono_trans : forall m1 m2 m3, readable_mono m1 m2 -> readable_mono m2 m3 -> readable_mono m1 m3.
Proof. intros m1 m2 m3 A B a n H. apply B, A, H. Qed.
Lemma rdZ_some_iff : forall m a n, (exists v, rdZ m a n = Some v) <-> (forall i, 0 <= i < Z.of_nat n -> m (a + i) <> None).
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a; cbn [rdZ].
  - split; [intros _ i Hi; lia| intros _; eauto].
  - rewrite Nat2Z.inj_succ. split.
    + intros (v & Hv) i Hi. destruct (m a) as [b|] eqn:Eb; [|discriminate]. destruct (rdZ m (a+1) n) as [r|] eqn:Er; [|discriminate].
      destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r; congruence|].
      assert (H : exists v, rdZ m (a+1) n = Some v) by eauto. apply IH with (i := i - 1) in H; [|lia].
      now replace (a + 1 + (i - 1)) with (a + i) in H by lia.
    + intros H. destruct (m a) as [b|] eqn:Eb. 2:{ exfalso. apply (H 0); [lia|]. now rewrite Z.add_0_r. }
      assert (H' : exists v, rdZ m (a+1) n = Some v). { apply IH. intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
      destruct H' as (r & ->). eauto.
Qed.

Lemma readable_mono_of_bytes : forall m m', (forall x, m x <> None -> m' x <> None) -> readable_mono m m'.
Proof. intros m m' H a n Hr. unfold readable in *. apply rdZ_some_iff. intros i Hi. apply H. revert i Hi. now apply rdZ_some_iff. Qed.

Definition zone_grows (z z' : zoneg) : Prop :=
  (forall a k, in_zone z a k -> in_zone z' a k) /\ (forall a k, in_alloc z a k -> in_alloc z' a k).
Lemma zone_grows_refl : forall z, zone_grows z z. Proof. intros z; split; auto. Qed.
Lemma zone_grows_trans : forall z1 z2 z3, zone_grows z1 z2 -> zone_grows z2 z3 -> zone_grows z1 z3.
Proof. intros z1 z2 z3 [A B] [C D]; split; auto. Qed.
Lemma zone_grows_bump : forall z adj, 0 <= adj -> zone_grows z (zone_bump z adj).
Proof. intros z adj H. split; [intros a k Hk; now apply in_zone_mono_bump| intros a k Hk; now apply in_alloc_mono_bump]. Qed.
Lemma zone_grows_fresh : forall z c sz size, zone_valid z -> 0 <= size -> zone_grows z (snd (zalloc_fresh z c sz size)).
Proof.
  intros z c sz size V Hs. split.
  - intros a k Hk. unfold zalloc_fresh; cbn. apply in_zone_mono_bump. now apply in_zone_mono_expand.
  - intros a k Hk. now apply in_alloc_mono_fresh.
Qed.

Lemma tree_wf_mono : forall m m' z z' o, readable_mono m m' -> zone_grows z z' -> tree_wf m z o -> tree_wf m' z' o.
Proof.
  intros m m' z z' o R [G _]. revert o. apply (obj_ind_size (fun o => tree_wf m z o -> tree_wf m' z' o)).
  intros o IH H. destruct o; try exact H.
  - cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|]. intros Hp. destruct (C Hp) as [C1 C2]. split; [now apply G|now apply R].
  - cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|]. intros Hp. destruct (C Hp) as [C1 C2]. split; [now apply G|now apply R].
  - cbn [tree_wf] in H |- *. destruct H as (A & B & C & D & E). repeat split; auto.
  - apply tree_wf_arr in H. apply tree_wf_arr. destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
    + intros Hk. destruct (H3 Hk) as [A B]. split; [exact A| now apply G].
    + apply trees_wf_forall. intros o' Ho'. apply IH; [|revert o' Ho'; now apply trees_wf_forall].
      rewrite obj_size_arr. pose proof (in_kids_size o' kids Ho'). lia.
  - apply tree_wf_map in H. apply tree_wf_map. destruct H as (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
    + intros Hk. destruct (H3 Hk) as [A B]. split; [exact A| now apply G].
    + apply trees_wf_forall. intros o' Ho'. apply IH; [|revert o' Ho'; now apply trees_wf_forall].
      rewrite obj_size_map. pose proof (in_kids_size o' kids Ho'). lia.
Qed.

Lemma tree_at_frame : forall m m' z z' a o,
  readable_mono m m' -> zone_grows z z' -> (forall c, In c (obj_cells a o) -> agree_on m m' c OBJ_SIZE) ->
  tree_at m z a o -> tree_at m' z' a o.
Proof.
  intros m m' z z' a o R G Hc [H1 H2]. split; [eapply obj_at_frame; eauto| eapply tree_wf_mono; eauto].
Qed.

Lemma tree_at_kid : forall m z a o i k,
  tree_at m z a o ->
  match o with OArr p kids | OMap p kids => nth_error kids i = Some k -> tree_at m z (p + OBJ_SIZE * Z.of_nat i) k | _ => True end.
Proof.
  intros m z a o i k [Ho Hw]. destruct o; try exact I; intros Hn.
  - apply obj_at_arr in Ho. apply tree_wf_arr in Hw. destruct Ho as (_ & _ & _ & Hk). destruct Hw as (_ & _ & _ & Hw).
    split; [eapply (proj1 (objs_at_nth _ _ _)); eauto|]. eapply (proj1 (trees_wf_forall _ _ _)); eauto using nth_error_In.
  - apply obj_at_map in Ho. apply tree_wf_map in Hw. destruct Ho as (_ & _ & _ & Hk). destruct Hw as (_ & _ & _ & _ & Hw).
    split; [eapply (proj1 (objs_at_nth _ _ _)); eauto|]. eapply (proj1 (trees_wf_forall _ _ _)); eauto using nth_error_In.
Qed.

Lemma kid_cells_sub : forall a o i k c,
  match o with OArr p kids | OMap p kids =>
    nth_error kids i = Some k -> In c (obj_cells (p + OBJ_SIZE * Z.of_nat i) k) -> In c (tl (obj_cells a o)) | _ => True end.
Proof.
  intros a o i k c. destruct o; try exact I; intros Hn Hc.
  - rewrite obj_cells_arr. cbn [tl]. apply in_kids_cells. eauto.
  - rewrite obj_cells_map. cbn [tl]. apply in_kids_cells. eauto.
Qed.

Lemma tree_cells_in_zone : forall m z a o c, tree_at m z a o -> In c (tl (obj_cells a o)) -> in_zone z c OBJ_SIZE.
Proof.
  intros m z a o c. revert a c. apply (obj_ind_size (fun o => forall a c, tree_at m z a o -> In c (tl (obj_cells a o)) -> in_zone z c OBJ_SIZE)).
  clear o. intros o IH a c Ht Hc.
  destruct o; try (cbn in Hc; contradiction).
  - rewrite obj_cells_arr in Hc. cbn [tl] in Hc. apply in_kids_cells in Hc. destruct Hc as (i & k & Hn & Hck).
    pose proof (tree_at_kid m z a (OArr p kids) i k Ht Hn) as Hk. cbn iota in Hk.
    rewrite obj_cells_hd in Hck. destruct Hck as [<-|Hck].
    + destruct Ht as [_ Hw]. apply tree_wf_arr in Hw. destruct Hw as (_ & _ & Hz & _).
      assert (Hne : kids <> []) by (intros ->; destruct i; discriminate).
      destruct (Hz Hne) as [_ (ch & Hch & Hi)]. exists ch. split; [exact Hch|].
      assert (Hlt : (i < length kids)%nat) by (apply nth_error_Some; congruence). unfold in_chunk in *. unfold OBJ_SIZE in *. nia.
    + eapply (IH k); [|exact Hk|exact Hck]. rewrite obj_size_arr. pose proof (in_kids_size k kids (nth_error_In _ _ Hn)). lia.
  - rewrite obj_cells_map in Hc. cbn [tl] in Hc. apply in_kids_cells in Hc. destruct Hc as (i & k & Hn & Hck).
    pose proof (tree_at_kid m z a (OMap p kids) i k Ht Hn) as Hk. cbn iota in Hk.
    rewrite obj_cells_hd in Hck. destruct Hck as [<-|Hck].
    + destruct Ht as [_ Hw]. apply tree_wf_map in Hw. destruct Hw as (_ & _ & _ & Hz & _).
      assert (Hne : kids <> []) by (intros ->; destruct i; discriminate).
      destruct (Hz Hne) as [_ (ch & Hch & Hi)]. exists ch. split; [exact Hch|].
      assert (Hlt : (i < length kids)%nat) by (apply nth_error_Some; congruence). unfold in_chunk in *. unfold OBJ_SIZE in *. nia.
    + eapply (IH k); [|exact Hk|exact Hck]. rewrite obj_size_map. pose proof (in_kids_size k kids (nth_error_In _ _ Hn)). lia.
Qed.

Lemma level_geom : forall l, level_valid l ->
  lv_P l <= lv_slot l /\ lv_slot l + OBJ_SIZE <= lv_P l + lv_bytes l /\ 0 <= lv_unfilled l /\
  lv_slot l + lv_unfilled l = lv_P l + lv_bytes l /\ 0 <= lv_k l /\ (lv_k l + 1) * OBJ_SIZE <= lv_bytes l.
Proof.
  intros [t n r P] (V1 & V2 & V3 & V4 & V5); unfold lv_unfilled, lv_slot, lv_bytes, lv_k in *; cbn in *.
  destruct t; cbn; unfold OBJ_SIZE; lia.
Qed.

Lemma cell_ok_mono_zone : forall z z' ls c, zone_grows z z' -> cell_ok z ls c -> cell_ok z' ls c.
Proof. intros z z' ls c [_ G] [A B]. split; [now apply G| exact B]. Qed.

Lemma cell_ok_mono_levels : forall z ls ls' c,
  (forall l', In l' ls' -> exists l, In l ls /\ lv_slot l <= lv_slot l' /\ lv_slot l' + lv_unfilled l' <= lv_slot l + lv_unfilled l) ->
  cell_ok z ls c -> cell_ok z ls' c.
Proof.
  intros z ls ls' c Hsub [A B]. split; [exact A|]. intros l' Hl'. destruct (Hsub l' Hl') as (l & Hl & H1 & H2).
  specialize (B l Hl). unfold rdisj in *. lia.
Qed.

Lemma cell_ok_push : forall z ls c t n P, t <> CT_MAP_VALUE ->
  cell_ok z ls c -> rdisj c OBJ_SIZE P (lv_bytes (new_level t n P)) -> cell_ok z (push_level ls t n P) c.
Proof.
  intros z ls c t n P Ht [A B] Hd. split; [exact A|]. intros l Hl. unfold push_level in Hl. apply in_app_iff in Hl.
  destruct Hl as [Hl|[<-|[]]]; [now apply B|].
  rewrite new_level_slot by exact Ht. unfold lv_unfilled. rewrite new_level_slot by exact Ht.
  replace (lv_P (new_level t n P)) with P by reflexivity. unfold rdisj in *. lia.
Qed.

Inductive store_ok (z : zoneg) (ls : list level) (lo k : Z) : Prop :=
| SO_outside : (forall ch, In ch (z_chunks z) -> rdisj lo k (fst ch) (CHUNK_HDR + snd ch)) -> store_ok z ls lo k
| SO_unfilled : forall l, In l ls -> lv_slot l <= lo -> lo + k <= lv_slot l + lv_unfilled l -> store_ok z ls lo k
| SO_fresh : z_ptr z <= lo -> lo + k <= chunk_hi (hd (0,0) (z_chunks z)) -> store_ok z ls lo k
| SO_chunk_hdr : forall ch, In ch (z_chunks z) -> fst ch <= lo -> lo + k <= fst ch + CHUNK_HDR -> store_ok z ls lo k.

Lemma store_ok_disj_cell : forall z ls lo k c, zone_valid z -> cell_ok z ls c -> store_ok z ls lo k -> rdisj c OBJ_SIZE lo k.
Proof.
  intros z ls lo k c V [A B] S. destruct S as [Hout| l Hl H1 H2 | H1 H2 | ch Hch H1 H2].
  - eapply in_alloc_outside_disj; eauto.
  - specialize (B l Hl). unfold rdisj in *. lia.
  - eapply in_alloc_fresh_disj; eauto. unfold OBJ_SIZE; lia.
  - destruct (in_alloc_chunk z c OBJ_SIZE V A) as (ch' & Hch' & Hi).
    destruct V as (V1 & _ & V3 & _ & _ & _ & V7).
    destruct (In_nth_error _ _ Hch) as (i & Hi1). destruct (In_nth_error _ _ Hch') as (j & Hj1).
    destruct (Nat.eq_dec i j) as [->|Hne].
    + rewrite Hj1 in Hi1. inversion Hi1; subst. unfold in_chunk, chunk_lo, chunk_hi, rdisj in *. lia.
    + assert (D : chunk_disj ch ch' \/ chunk_disj ch' ch).
      { destruct (Nat.lt_ge_cases i j) as [L|L].
        - left. destruct (nth_error_split _ _ Hi1) as (l1 & l2 & El & Hl1). rewrite El in V7, Hj1.
          apply ForallOrdPairs_app_inv in V7. destruct V7 as [F _]. apply Forall_forall with (x := ch') in F; [exact F|].
          rewrite nth_error_app2 in Hj1 by lia. destruct (j - length l1)%nat eqn:E; [lia|]. cbn in Hj1. eapply nth_error_In; eauto.
        - right. destruct (nth_error_split _ _ Hj1) as (l1 & l2 & El & Hl1). rewrite El in V7, Hi1.
          apply ForallOrdPairs_app_inv in V7. destruct V7 as [F _]. apply Forall_forall with (x := ch) in F; [exact F|].
          rewrite nth_error_app2 in Hi1 by lia. destruct (i - length l1)%nat eqn:E; [lia|]. cbn in Hi1. eapply nth_error_In; eauto. }
      pose proof (V3 ch Hch). pose proof (V3 ch' Hch').
      unfold chunk_disj, in_chunk, chunk_lo, chunk_hi, rdisj, CHUNK_HDR, CHUNK_SIZE0, OBJ_SIZE in *. lia.
Qed.

Definition outside (x : Z) (w : Z * Z) : Prop := x < fst w \/ fst w + snd w <= x.
Definition stores_ok (z : zoneg) (ls : list level) (m m' : bmem) : Prop :=
  exists ws : list (Z * Z), Forall (fun w => store_ok z ls (fst w) (snd w)) ws /\
    forall x, Forall (outside x) ws -> m' x = m x.
Lemma stores_ok_agree : forall z ls m m' c, zone_valid z -> stores_ok z ls m m' -> cell_ok z ls c -> agree_on m m' c OBJ_SIZE.
Proof.
  intros z ls m m' c V (ws & Hws & Hout) Hc x Hx. apply Hout. apply Forall_forall. intros w Hw.
  apply Forall_forall with (x := w) in Hws; [|exact Hw].
  pose proof (store_ok_disj_cell z ls (fst w) (snd w) c V Hc Hws). unfold outside, rdisj in *. lia.
Qed.
Lemma stores_ok_nil : forall z ls m, stores_ok z ls m m.
Proof. intros z ls m. exists []. split; [constructor|]. reflexivity. Qed.
Lemma stores_ok_cons : forall z ls m1 m2 m3 lo k,
  stores_ok z ls m1 m2 -> store_ok z ls lo k -> updated_within m2 m3 lo k -> stores_ok z ls m1 m3.
Proof.
  intros z ls m1 m2 m3 lo k (ws & Hws & Hout) Hs Hu. exists ((lo, k) :: ws). split; [now constructor|].
  intros x Hx. inversion Hx as [|w' ws' Hw Hrest]; subst. rewrite (Hu x); [now apply Hout|]. unfold outside in Hw. cbn in Hw. lia.
Qed.

Lemma completed_wf_frame : forall m m' z z' ls,
  zone_valid z -> readable_mono m m' -> zone_grows z z' -> stores_ok z ls m m' ->
  completed_wf m z ls -> completed_wf m' z' ls.
Proof.
  intros m m' z z' ls V R G S H l Hl i Hi. destruct (H l Hl i Hi) as (o & Ht & Hc). exists o. split.
  - eapply tree_at_frame; eauto. intros c Hcc. eapply stores_ok_agree; eauto.
  - intros c Hcc. eapply cell_ok_mono_zone; eauto.
Qed.

Lemma just_completed_frame : forall m m' z z' ls a o,
  zone_valid z -> readable_mono m m' -> zone_grows z z' -> stores_ok z ls m m' -> agree_on m m' a OBJ_SIZE ->
  tree_at m z a o /\ (forall c, In c (tl (obj_cells a o)) -> cell_ok z ls c) ->
  tree_at m' z' a o /\ (forall c, In c (tl (obj_cells a o)) -> cell_ok z' ls c).
Proof.
  intros m m' z z' ls a o V R G S Ha [Ht Hc]. split.
  - eapply tree_at_frame; eauto. intros c Hcc. rewrite obj_cells_hd in Hcc. destruct Hcc as [<-|Hcc]; [exact Ha|].
    eapply stores_ok_agree; eauto.
  - intros c Hcc. eapply cell_ok_mono_zone; eauto.
Qed.

Lemma conts_at_frame : forall m m' cs ls,
  (forall c, In c cs -> agree_on m m' c OBJ_SIZE) -> conts_at m cs ls -> conts_at m' cs ls.
Proof.
  intros m m' cs. induction cs as [|c cs IH]; intros [|l ls] Hag H; cbn in *; try exact I.
  destruct H as (A & B & C & D).
  assert (Hc : agree_on m m' c OBJ_SIZE) by (apply Hag; now left).
  split; [eapply u32_at_frame; [|exact A]; eapply agree_on_sub; [exact Hc|lia|unfold OBJ_SIZE; lia]|].
  split; [eapply u32_at_frame; [|exact B]; eapply agree_on_sub; [exact Hc|lia|unfold OBJ_SIZE; lia]|].
  split; [eapply u64_at_frame; [|exact C]; eapply agree_on_sub; [exact Hc|lia|unfold OBJ_SIZE; lia]|].
  apply IH; [|exact D]. intros c' Hc'. apply Hag. now right.
Qed.

Lemma ForallOrdPairs_sub_snoc : forall {A} (R : A -> A -> Prop) ls (l : A),
  ForallOrdPairs R (ls ++ [l]) -> ForallOrdPairs R ls /\ Forall (fun x => R x l) ls.
Proof.
  intros A R ls l H. induction ls as [|x ls IH]; cbn in *.
  - split; constructor.
  - inversion H as [|x' l' Hf Hp]; subst. destruct (IH Hp) as [P1 P2]. split.
    + constructor; [|exact P1]. apply Forall_forall. intros y Hy. apply Forall_forall with (x := y) in Hf; [exact Hf|]. apply in_app_iff. now left.
    + constructor; [|exact P2]. apply Forall_forall with (x := l) in Hf; [exact Hf|]. apply in_app_iff. right. now left.
Qed.
Lemma ForallOrdPairs_snoc : forall {A} (R : A -> A -> Prop) ls (l : A),
  ForallOrdPairs R ls -> Forall (fun x => R x l) ls -> ForallOrdPairs R (ls ++ [l]).
Proof.
  intros A R ls l H1 H2. induction ls as [|x ls IH]; cbn.
  - constructor; constructor.
  - inversion H1; inversion H2; subst. constructor; [|now apply IH]. apply Forall_app. split; [assumption|]. now constructor.
Qed.

Lemma levels_alloc_push : forall z ls t n P,
  levels_alloc z ls -> in_alloc z P (lv_bytes (new_level t n P)) ->
  Forall (fun l => rdisj (lv_P l) (lv_bytes l) P (lv_bytes (new_level t n P))) ls ->
  levels_alloc z (push_level ls t n P).
Proof.
  intros z ls t n P [A B] Hin Hd. split.
  - intros l Hl. unfold push_level in Hl. apply in_app_iff in Hl. destruct Hl as [Hl|[<-|[]]]; [now apply A| exact Hin].
  - unfold push_level. apply ForallOrdPairs_snoc; [exact B|]. eapply Forall_impl; [|exact Hd]. intros l Hl. exact Hl.
Qed.
Lemma levels_alloc_retop : forall z ls l l',
  lv_P l' = lv_P l -> lv_bytes l' = lv_bytes l -> levels_alloc z (ls ++ [l]) -> levels_alloc z (ls ++ [l']).
Proof.
  intros z ls l l' HP HB [A B]. split.
  - intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [apply A; apply in_app_iff; now left|].
    rewrite HP, HB. apply A. apply in_app_iff. right; now left.
  - apply ForallOrdPairs_sub_snoc in B. destruct B as [B1 B2]. apply ForallOrdPairs_snoc; [exact B1|].
    eapply Forall_impl; [|exact B2]. intros x Hx. unfold level_disj in *. now rewrite HP, HB.
Qed.
Lemma levels_alloc_pop : forall z ls l, levels_alloc z (ls ++ [l]) -> levels_alloc z ls.
Proof.
  intros z ls l [A B]. split.
  - intros x Hx. apply A. apply in_app_iff. now left.
  - now apply ForallOrdPairs_sub_snoc in B.
Qed.
Lemma levels_alloc_mono_zone : forall z z' ls, zone_grows z z' -> levels_alloc z ls -> levels_alloc z' ls.
Proof. intros z z' ls [_ G] [A B]. split; [|exact B]. intros l Hl. apply G. now apply A. Qed.

Lemma in_alloc_sub : forall z a n a' n', in_alloc z a n -> a <= a' -> a' + n' <= a + n -> in_alloc z a' n'.
Proof.
  intros z a n a' n' [(c & Hc & Hi)|(H1 & H2)] L1 L2; [left|right; lia].
  exists c. split; [exact Hc|]. unfold in_chunk in *. lia.
Qed.

Lemma collect_kids : forall m z (Q : Z -> Prop) K P,
  (forall i, 0 <= i < Z.of_nat K -> exists o, tree_at m z (P + OBJ_SIZE * i) o /\ (forall c, In c (obj_cells (P + OBJ_SIZE * i) o) -> Q c)) ->
  exists kids, length kids = K /\ objs_at m P kids /\ trees_wf m z kids /\ (forall c, In c (kids_cells P kids) -> Q c).
Proof.
  intros m z Q K. induction K as [|K IH]; intros P H.
  - exists []. cbn. repeat split; auto. intros c [].
  - destruct (H 0 ltac:(lia)) as (o & Ho & Hc). rewrite Z.mul_0_r, Z.add_0_r in Ho, Hc.
    destruct (IH (P + OBJ_SIZE)) as (kids & Hlen & Hat & Hwf & HQ).
    { intros i Hi. destruct (H (i + 1) ltac:(lia)) as (o' & Ho' & Hc').
      replace (P + OBJ_SIZE * (i + 1)) with (P + OBJ_SIZE + OBJ_SIZE * i) in Ho', Hc' by lia. eauto. }
    exists (o :: kids). cbn [length objs_at trees_wf kids_cells]. rewrite Hlen. repeat split; auto; try apply Ho.
    intros c Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; auto.
Qed.
Lemma even_len_spec : forall {A} (l : list A), even_len l = true <-> Nat.Even (length l).
Proof.
  intros A l. induction l as [l IH] using (well_founded_induction (Wf_nat.well_founded_ltof _ (@length A))).
  destruct l as [|x [|y l']]; cbn [even_len length].
  - split; [intros _; now exists 0%nat|reflexivity].
  - split; [discriminate|]. intros [k Hk]. lia.
  - rewrite IH by (unfold Wf_nat.ltof; cbn; lia). split.
    + intros [k Hk]. exists (S k). lia.
    + intros [k Hk]. exists (k - 1)%nat. lia.
Qed.

Lemma conts_at_app : forall m cs1 cs2 ls1 ls2, length cs1 = length ls1 ->
  conts_at m (cs1 ++ cs2) (ls1 ++ ls2) <-> conts_at m cs1 ls1 /\ conts_at m cs2 ls2.
Proof.
  intros m cs1. induction cs1 as [|c cs1 IH]; intros cs2 [|l ls1] ls2 Hlen; cbn in Hlen |- *; try discriminate.
  - tauto.
  - rewrite IH by lia. tauto.
Qed.
Lemma containers_snoc_indep : forall root ls l l', containers root (ls ++ [l']) = containers root (ls ++ [l]).
Proof. intros. rewrite !containers_app. reflexivity. Qed.

Lemma complete_item : forall m z root ls l l',
  Forall level_valid (ls ++ [l]) -> levels_alloc z (ls ++ [l]) -> consume_top l = CS_Ret l' ->
  completed_wf m z (ls ++ [l]) ->
  (exists o, tree_at m z (lv_slot l) o /\ (forall c, In c (tl (obj_cells (lv_slot l) o)) -> cell_ok z (ls ++ [l]) c)) ->
  completed_wf m z (ls ++ [l']) /\ levels_alloc z (ls ++ [l']) /\ Forall level_valid (ls ++ [l']) /\
  containers root (ls ++ [l']) = containers root (ls ++ [l]) /\
  cur_slot root (ls ++ [l']) = cur_slot root (ls ++ [l]) + OBJ_SIZE /\
  lv_slot l' = lv_slot l + OBJ_SIZE /\ lv_P l' = lv_P l /\ lv_n l' = lv_n l /\
  (forall m', conts_at m' (containers root (ls ++ [l])) (ls ++ [l]) -> conts_at m' (containers root (ls ++ [l'])) (ls ++ [l'])).
Proof.
  intros m z root ls l l' V LA Hc CW (o & Ht & Htl).
  apply Forall_app in V. destruct V as [Vls Vl]. inversion Vl as [|l0 l1 Vl' _]; subst. clear Vl.
  pose proof (consume_top_ret l l' Hc Vl') as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (level_geom l Vl') as G. pose proof (level_geom l' S5) as G'. assert (HO : OBJ_SIZE = 24) by reflexivity.
  assert (SUB : forall x', In x' (ls ++ [l']) -> exists x, In x (ls ++ [l]) /\ lv_slot x <= lv_slot x' /\ lv_slot x' + lv_unfilled x' <= lv_slot x + lv_unfilled x).
  { intros x' Hx'. apply in_app_iff in Hx'. destruct Hx' as [Hx'|[<-|[]]].
    - exists x'. split; [apply in_app_iff; now left|lia].
    - exists l. split; [apply in_app_iff; right; now left|]. lia. }
  assert (ROOT : cell_ok z (ls ++ [l']) (lv_slot l)).
  { destruct LA as [A B]. split.
    - eapply in_alloc_sub; [apply A; apply in_app_iff; right; now left| lia | lia].
    - intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [|unfold rdisj; lia].
      apply ForallOrdPairs_sub_snoc in B. destruct B as [_ B2]. apply Forall_forall with (x := x) in B2; [|exact Hx].
      apply Forall_forall with (x := x) in Vls; [|exact Hx]. pose proof (level_geom x Vls).
      unfold level_disj, rdisj in *. lia. }
  repeat split.
  - intros x Hx i Hi. apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]].
    + destruct (CW x ltac:(apply in_app_iff; now left) i Hi) as (ox & Hox & Hcx). exists ox. split; [exact Hox|].
      intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx.
    + rewrite S2. destruct (Z.lt_ge_cases i (lv_k l)) as [Hlt|Hge].
      * destruct (CW l ltac:(apply in_app_iff; right; now left) i ltac:(lia)) as (ox & Hox & Hcx). exists ox. split; [exact Hox|].
        intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx.
      * assert (Ei : i = lv_k l) by lia. subst i. replace (lv_P l + OBJ_SIZE * lv_k l) with (lv_slot l) by (unfold lv_slot; lia).
        exists o. split; [exact Ht|]. intros c Hcc. rewrite obj_cells_hd in Hcc. destruct Hcc as [<-|Hcc]; [exact ROOT|].
        eapply cell_ok_mono_levels; [exact SUB|]. now apply Htl.
  - destruct LA as [A B]. intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [apply A; apply in_app_iff; now left|].
    rewrite S2, S6. apply A. apply in_app_iff. right; now left.
  - destruct LA as [A B]. apply ForallOrdPairs_sub_snoc in B. destruct B as [B1 B2]. apply ForallOrdPairs_snoc; [exact B1|].
    eapply Forall_impl; [|exact B2]. intros x Hx. unfold level_disj in *. now rewrite S2, S6.
  - apply Forall_app. split; [exact Vls|]. now constructor.
  - apply containers_snoc_indep.
  - rewrite !cur_slot_snoc. exact S1.
  - exact S1. - exact S2. - exact S3.
  - intros m' H. rewrite (containers_snoc_indep root ls l l'). rewrite containers_app in H |- *. cbn [containers] in H |- *.
    rewrite conts_at_app in H |- * by apply containers_length. destruct H as [H1 H2]. split; [exact H1|].
    cbn in H2 |- *. rewrite S7, S3, S2. exact H2.
Qed.

Lemma complete_container : forall m z root ls l,
  Forall level_valid (ls ++ [l]) -> levels_alloc z (ls ++ [l]) -> zone_valid z -> consume_top l = CS_Pop ->
  conts_at m (containers root (ls ++ [l])) (ls ++ [l]) ->
  completed_wf m z (ls ++ [l]) ->
  (exists o, tree_at m z (lv_slot l) o /\ (forall c, In c (tl (obj_cells (lv_slot l) o)) -> cell_ok z (ls ++ [l]) c)) ->
  (exists o, tree_at m z (cur_slot root ls) o /\ obj_type o = container_type (lv_t l) /\ obj_count o = lv_n l /\ obj_ptr o = lv_P l /\
             (forall c, In c (tl (obj_cells (cur_slot root ls) o)) -> cell_ok z ls c)) /\
  completed_wf m z ls /\ levels_alloc z ls /\ Forall level_valid ls /\ conts_at m (containers root ls) ls.
Proof.
  intros m z root ls l V LA Vz Hc CA CW (o & Ht & Htl).
  apply Forall_app in V. destruct V as [Vls Vl]. inversion Vl as [|l0 l1 Vl' _]; subst. clear Vl.
  destruct (consume_top_pop l Hc) as [R1 NK]. pose proof (pop_full l Vl' R1 NK) as FULL. pose proof (level_geom l Vl') as G.
  assert (HO : OBJ_SIZE = 24) by reflexivity.
  rewrite containers_app in CA. cbn [containers] in CA. rewrite conts_at_app in CA by apply containers_length.
  destruct CA as [CAls CAl]. cbn in CAl. destruct CAl as (T1 & T2 & T3 & _).
  assert (SUB : forall x', In x' ls -> exists x, In x (ls ++ [l]) /\ lv_slot x <= lv_slot x' /\ lv_slot x' + lv_unfilled x' <= lv_slot x + lv_unfilled x).
  { intros x' Hx'. exists x'. split; [apply in_app_iff; now left|lia]. }
  assert (ROOT : cell_ok z ls (lv_slot l)).
  { destruct LA as [A B]. split.
    - eapply in_alloc_sub; [apply A; apply in_app_iff; right; now left| lia | lia].
    - intros x Hx. apply ForallOrdPairs_sub_snoc in B. destruct B as [_ B2]. apply Forall_forall with (x := x) in B2; [|exact Hx].
      apply Forall_forall with (x := x) in Vls; [|exact Hx]. pose proof (level_geom x Vls). unfold level_disj, rdisj in *. lia. }

  destruct (collect_kids m z (cell_ok z ls) (Z.to_nat (lv_k l + 1)) (lv_P l)) as (kids & Hlen & Hat & Hwf & Hcells).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. destruct (Z.lt_ge_cases i (lv_k l)) as [Hlt|Hge].
    - destruct (CW l ltac:(apply in_app_iff; right; now left) i ltac:(lia)) as (ox & Hox & Hcx). exists ox. split; [exact Hox|].
      intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx.
    - assert (Ei : i = lv_k l) by lia. subst i. replace (lv_P l + OBJ_SIZE * lv_k l) with (lv_slot l) by (unfold lv_slot; lia).
      exists o. split; [exact Ht|]. intros c Hcc. rewrite obj_cells_hd in Hcc. destruct Hcc as [<-|Hcc]; [exact ROOT|].
      eapply cell_ok_mono_levels; [exact SUB|]. now apply Htl. }
  assert (Hlen' : Z.of_nat (length kids) = lv_k l + 1) by (rewrite Hlen, Z2Nat.id; lia).
  assert (Hne : kids <> []) by (intros ->; cbn in Hlen'; lia).
  assert (HPz : in_zone z (lv_P l) (OBJ_SIZE * Z.of_nat (length kids))).
  { rewrite Hlen'. destruct LA as [A _]. destruct Vz as (Vz1 & _ & _ & Vz4 & Vz5 & Vz6 & _).
    apply in_alloc_in_zone; [exact Vz1| lia |]. rewrite Z.mul_comm, FULL. apply A. apply in_app_iff. right; now left. }
  destruct Vl' as (W1 & W2 & W3 & W4 & W5).
  split.
  { destruct (lv_t l) eqn:Et; [| exfalso; now apply NK |].
    -   exists (OArr (lv_P l) kids). cbn [obj_type obj_count obj_ptr container_type].
      assert (Hn : Z.of_nat (length kids) = lv_n l) by (rewrite Hlen'; unfold lv_k; rewrite Et; lia).
      split; [|split; [reflexivity|split; [exact Hn|split; [reflexivity|]]]].
      + split; [apply obj_at_arr| apply tree_wf_arr]; rewrite ?Hn; repeat split; auto; try lia; try tauto. now rewrite <- Hn.
      + intros c Hcc. rewrite obj_cells_arr in Hcc. cbn [tl] in Hcc. now apply Hcells.
    -   exists (OMap (lv_P l) kids). cbn [obj_type obj_count obj_ptr container_type].
      assert (Hn : Z.of_nat (length kids) = 2 * lv_n l) by (rewrite Hlen'; unfold lv_k; rewrite Et; lia).
      assert (Hn2 : Z.of_nat (length kids) / 2 = lv_n l) by (rewrite Hn, Z.mul_comm; apply Z.div_mul; lia).
      assert (Hev : even_len kids = true). { apply even_len_spec. exists (Z.to_nat (lv_n l)). lia. }
      split; [|split; [reflexivity|split; [exact Hn2|split; [reflexivity|]]]].
      + split; [apply obj_at_map| apply tree_wf_map]; rewrite ?Hn2; repeat split; auto; try lia; try tauto.
      + intros c Hcc. rewrite obj_cells_map in Hcc. cbn [tl] in Hcc. now apply Hcells. }
  split. { intros x Hx i Hi. destruct (CW x ltac:(apply in_app_iff; now left) i Hi) as (ox & Hox & Hcx). exists ox. split; [exact Hox|].
           intros c Hcc. eapply cell_ok_mono_levels; [exact SUB|]. now apply Hcx. }
  split; [eapply levels_alloc_pop; exact LA|]. split; [exact Vls| exact CAls].
Qed.

Lemma push_ok : forall m z root ls t n P,
  t <> CT_MAP_VALUE -> 1 <= n <= LIMIT -> P <> 0 -> P mod 8 = 0 ->
  Forall level_valid ls -> levels_alloc z ls -> completed_wf m z ls ->
  (forall a k, 0 <= k -> in_alloc z a k -> rdisj a k P (lv_bytes (new_level t n P))) ->
  let ls' := push_level ls t n P in
  Forall level_valid ls' /\
  (forall z', zone_grows z z' -> in_alloc z' P (lv_bytes (new_level t n P)) -> levels_alloc z' ls') /\
  completed_wf m z ls' /\
  containers root ls' = containers root ls ++ [cur_slot root ls] /\ cur_slot root ls' = P /\
  lv_k (new_level t n P) = 0 /\ lv_slot (new_level t n P) = P /\
  (forall m', conts_at m' (containers root ls') ls' <->
              (conts_at m' (containers root ls) ls /\ u32_at m' (cur_slot root ls) (container_type t) /\
               u32_at m' (cur_slot root ls + 8) n /\ u64_at m' (cur_slot root ls + 16) P)).
Proof.
  intros m z root ls t n P Ht Hn HP HA V LA CW FR ls'. subst ls'.
  assert (HO : OBJ_SIZE = 24) by reflexivity.
  assert (Hb : 0 <= lv_bytes (new_level t n P)) by (unfold lv_bytes, new_level; cbn; destruct t; cbn; lia).
  split; [now apply push_level_valid|].
  split. { intros z' G Hin. apply levels_alloc_push; [eapply levels_alloc_mono_zone; eauto| exact Hin|].
    apply Forall_forall. intros l Hl. apply FR. { apply Forall_forall with (x := l) in V; [|exact Hl]. pose proof (level_geom l V). lia. }
    now apply (proj1 LA). }
  split. { intros l Hl i Hi. unfold push_level in Hl. apply in_app_iff in Hl. destruct Hl as [Hl|[<-|[]]].
    + destruct (CW l Hl i Hi) as (o & Ho & Hc). exists o. split; [exact Ho|]. intros c Hcc. apply cell_ok_push; [exact Ht| now apply Hc|].
      apply FR; [lia|]. exact (proj1 (Hc c Hcc)).
    + rewrite new_level_k in Hi by exact Ht. lia. }
  split; [apply push_level_containers|]. split; [now apply push_level_cur_slot|].
  split; [now apply new_level_k|]. split; [now apply new_level_slot|].
  intros m'. unfold push_level. rewrite containers_app. cbn [containers]. rewrite conts_at_app by apply containers_length. cbn. tauto.
Qed.

Lemma just_nil : forall m z ls a, u32_at m a T_NIL ->
  tree_at m z a ONil /\ (forall c, In c (tl (obj_cells a ONil)) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|exact I]| intros c []]. Qed.
Lemma just_bool : forall m z ls a (b : bool), u32_at m a T_BOOLEAN -> u8_at m (a + 8) (if b then 1 else 0) ->
  tree_at m z a (OBool b) /\ (forall c, In c (tl (obj_cells a (OBool b))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|exact I]| intros c []]. Qed.
Lemma just_pos : forall m z ls a u, u32_at m a T_POSINT -> u64_at m (a + 8) u -> 0 <= u < 2^64 ->
  tree_at m z a (OPos u) /\ (forall c, In c (tl (obj_cells a (OPos u))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|cbn; lia]| intros c []]. Qed.
Lemma just_neg : forall m z ls a i, u32_at m a T_NEGINT -> u64_at m (a + 8) (enc64 i) -> - 2^64 <= i < 0 ->
  tree_at m z a (ONeg i) /\ (forall c, In c (tl (obj_cells a (ONeg i))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|cbn; lia]| intros c []]. Qed.

Lemma just_negu : forall m z ls a u, u32_at m a T_NEGINT -> u64_at m (a + 8) u -> 0 <= u < 2^64 ->
  tree_at m z a (ONeg (u - 2^64)) /\ (forall c, In c (tl (obj_cells a (ONeg (u - 2^64)))) -> cell_ok z ls c).
Proof.
  intros m z ls a u H1 H2 Hu. apply just_neg; [exact H1| |lia]. unfold enc64.
  replace ((u - 2 ^ 64) mod 2 ^ 64) with u; [exact H2|].
  replace (u - 2 ^ 64) with (u + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
Qed.

Lemma just_int : forall m z ls a ty u, u32_at m a ty -> u64_at m (a + 8) u -> (ty = T_POSINT \/ ty = T_NEGINT) -> 0 <= u < 2^64 ->
  exists o, tree_at m z a o /\ (forall c, In c (tl (obj_cells a o)) -> cell_ok z ls c).
Proof.
  intros m z ls a ty u H1 H2 [-> | ->] Hu.
  - exists (OPos u). apply just_pos; assumption.
  - exists (ONeg (u - 2^64)). apply just_negu; assumption.
Qed.
Lemma just_f32 : forall m z ls a bits, u32_at m a T_FLOAT32 -> u64_at m (a + 8) bits ->
  tree_at m z a (OF32 bits) /\ (forall c, In c (tl (obj_cells a (OF32 bits))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|exact I]| intros c []]. Qed.
Lemma just_f64 : forall m z ls a bits, u32_at m a T_FLOAT64 -> u64_at m (a + 8) bits ->
  tree_at m z a (OF64 bits) /\ (forall c, In c (tl (obj_cells a (OF64 bits))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|exact I]| intros c []]. Qed.

Lemma just_str : forall m z ls a p n, u32_at m a T_STR -> u32_at m (a + 8) n -> u64_at m (a + 16) p ->
  0 <= n <= LIMIT -> (p = 0 -> n = 0) -> (p <> 0 -> in_zone z p n /\ readable m p (Z.to_nat n)) ->
  tree_at m z a (OStr p n) /\ (forall c, In c (tl (obj_cells a (OStr p n))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|cbn; tauto]| intros c []]. Qed.
Lemma just_bin : forall m z ls a p n, u32_at m a T_BIN -> u32_at m (a + 8) n -> u64_at m (a + 16) p ->
  0 <= n <= LIMIT -> (p = 0 -> n = 0) -> (p <> 0 -> in_zone z p n /\ readable m p (Z.to_nat n)) ->
  tree_at m z a (OBin p n) /\ (forall c, In c (tl (obj_cells a (OBin p n))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|cbn; tauto]| intros c []]. Qed.
Lemma just_ext : forall m z ls a p n, u32_at m a T_EXT -> u32_at m (a + 8) n -> u64_at m (a + 16) p ->
  0 <= n -> n + 1 <= LIMIT -> p <> 0 -> in_zone z p (n + 1) -> readable m p (Z.to_nat (n + 1)) ->
  tree_at m z a (OExt p n) /\ (forall c, In c (tl (obj_cells a (OExt p n))) -> cell_ok z ls c).
Proof. intros. split; [split; [cbn; auto|cbn; tauto]| intros c []]. Qed.
Lemma just_empty_arr : forall m z ls a, u32_at m a T_ARRAY -> u32_at m (a + 8) 0 -> u64_at m (a + 16) 0 ->
  tree_at m z a (OArr 0 []) /\ (forall c, In c (tl (obj_cells a (OArr 0 []))) -> cell_ok z ls c).
Proof.
  intros. split; [|intros c []]. split; [apply obj_at_arr; cbn; tauto| apply tree_wf_arr; cbn].
  repeat split; auto; try (unfold LIMIT; lia); try tauto.
Qed.
Lemma just_empty_map : forall m z ls a, u32_at m a T_MAP -> u32_at m (a + 8) 0 -> u64_at m (a + 16) 0 ->
  tree_at m z a (OMap 0 []) /\ (forall c, In c (tl (obj_cells a (OMap 0 []))) -> cell_ok z ls c).
Proof.
  intros. split; [|intros c []]. split; [apply obj_at_map; cbn; tauto| apply tree_wf_map; cbn].
  repeat split; auto; try (unfold LIMIT; cbn; lia); try tauto. change (0/2) with 0. unfold LIMIT; lia.
Qed.

Lemma body_in_zone : forall z a n, zone_valid z -> in_alloc z a n -> in_zone z a n.
Proof. intros z a n V H. destruct V as (V1 & _ & _ & V4 & V5 & V6 & _). apply in_alloc_in_zone; auto. lia. Qed.

Lemma FOP_remove : forall {A} (R : A -> A -> Prop) l1 x l2, ForallOrdPairs R (l1 ++ x :: l2) -> ForallOrdPairs R (l1 ++ l2).
Proof.
  intros A R l1. induction l1 as [|y l1 IH]; intros x l2 H; cbn in *.
  - now inversion H.
  - inversion H as [|y' l' Hf Hp]; subst. constructor; [|eapply IH; eauto].
    apply Forall_app in Hf. destruct Hf as [F1 F2]. inversion F2; subst. apply Forall_app. now split.
Qed.
Lemma FOP_insert : forall {A} (R : A -> A -> Prop) l1 x l2, (forall a b, R a b -> R b a) ->
  ForallOrdPairs R (l1 ++ l2) -> Forall (R x) (l1 ++ l2) -> ForallOrdPairs R (l1 ++ x :: l2).
Proof.
  intros A R l1. induction l1 as [|y l1 IH]; intros x l2 Hs H Hx; cbn in *.
  - now constructor.
  - inversion H as [|y' l' Hf Hp]; subst. inversion Hx as [|y'' l'' Hxy Hxr]; subst. constructor; [|now apply IH].
    apply Forall_app in Hf. destruct Hf as [F1 F2]. apply Forall_app. split; [exact F1|]. constructor; [now apply Hs| exact F2].
Qed.
Lemma regions_disj_replace : forall l1 r r' l2,
  regions_disj (l1 ++ r :: l2) -> Forall (fun x => rdisj (fst r') (snd r') (fst x) (snd x)) (l1 ++ l2) -> regions_disj (l1 ++ r' :: l2).
Proof.
  intros l1 r r' l2 H Hf. unfold regions_disj in *. apply FOP_insert; [intros a b; apply rdisj_sym| eapply FOP_remove; eauto| exact Hf].
Qed.
Lemma regions_disj_insert : forall l1 r' l2,
  regions_disj (l1 ++ l2) -> Forall (fun x => rdisj (fst r') (snd r') (fst x) (snd x)) (l1 ++ l2) -> regions_disj (l1 ++ r' :: l2).
Proof. intros l1 r' l2 H Hf. unfold regions_disj in *. apply FOP_insert; auto. intros a b; apply rdisj_sym. Qed.
Lemma regions_disj_remove : forall l1 r l2, regions_disj (l1 ++ r :: l2) -> regions_disj (l1 ++ l2).
Proof. intros. eapply FOP_remove; eauto. Qed.

Lemma regions_disj_nth : forall rs i j r r', regions_disj rs -> nth_error rs i = Some r -> nth_error rs j = Some r' -> i <> j ->
  rdisj (fst r) (snd r) (fst r') (snd r').
Proof.
  intros rs i j r r' H Hi Hj Hne.
  destruct (Nat.lt_ge_cases i j) as [L|L].
  - destruct (nth_error_split _ _ Hi) as (l1 & l2 & E & Hl1). rewrite E in H, Hj.
    apply ForallOrdPairs_app_inv in H. destruct H as [F _]. apply Forall_forall with (x := r') in F; [exact F|].
    rewrite nth_error_app2 in Hj by lia. destruct (j - length l1)%nat eqn:En; [lia|]. cbn in Hj. eapply nth_error_In; eauto.
  - destruct (nth_error_split _ _ Hj) as (l1 & l2 & E & Hl1). rewrite E in H, Hi.
    apply ForallOrdPairs_app_inv in H. destruct H as [F _]. apply Forall_forall with (x := r) in F; [|].
    + now apply rdisj_sym.
    + rewrite nth_error_app2 in Hi by lia. destruct (i - length l1)%nat eqn:En; [lia|]. cbn in Hi. eapply nth_error_In; eauto.
Qed.

Definition UNP_PURE (g : unpg) : Prop :=
  vec_valid (u_cstk g) /\ v_elt (u_cstk g) = 8 /\ v_size (u_cstk g) = u_D g /\ cap32_b (v_cap (u_cstk g)) = true /\
  vec_valid (u_vstk g) /\ v_elt (u_vstk g) = 8 /\ v_size (u_vstk g) = u_D g + 1 /\ cap32_b (v_cap (u_vstk g)) = true /\
  Forall level_valid (u_levels g) /\ u_D g <= LIMIT /\ levels_alloc (u_zone g) (u_levels g) /\
  zone_valid (u_zone g) /\ regions_disj (unp_regions g) /\
  u_ctx g <> 0 /\ u_vis g <> 0 /\ u_ctx g mod 8 = 0 /\ u_vis g mod 8 = 0 /\ 0 < u_len g /\ 0 < u_data g /\ u_pe g < 2^47.
Definition UNP_MEM (live : Z -> Z -> Prop) (m : bmem) (g : unpg) (cur cs trail : Z) : Prop :=
  ctx_at m g cur cs trail /\ vis_at m g /\ zone_at m (u_zone g) /\ stacks_at m g /\
  conts_at m (containers (u_root g) (u_levels g)) (u_levels g) /\ completed_wf m (u_zone g) (u_levels g) /\
  (forall b, In b (unp_blocks g) -> live (fst b) (snd b)).
Lemma UNP_CORE_iff : forall live m g cur cs trail, UNP_CORE live m g cur cs trail <-> (UNP_MEM live m g cur cs trail /\ UNP_PURE g).
Proof. intros. unfold UNP_CORE, UNP_MEM, UNP_PURE. tauto. Qed.

Definition g_levels (g : unpg) (ls : list level) : unpg :=
  mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) ls
        (mkVec (v_begin (u_cstk g)) (Z.of_nat (length ls)) (v_cap (u_cstk g)) (v_elt (u_cstk g)))
        (mkVec (v_begin (u_vstk g)) (Z.of_nat (length ls) + 1) (v_cap (u_vstk g)) (v_elt (u_vstk g)))
        (u_zone g).
Definition g_zone (g : unpg) (z : zoneg) : unpg :=
  mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) (u_levels g) (u_cstk g) (u_vstk g) z.
Definition g_cstk (g : unpg) (v : vecg) : unpg :=
  mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) (u_levels g) v (u_vstk g) (u_zone g).
Definition g_vstk (g : unpg) (v : vecg) : unpg :=
  mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) (u_levels g) (u_cstk g) v (u_zone g).

Lemma unp_regions_levels : forall g ls, unp_regions (g_levels g ls) = unp_regions g.
Proof. intros. unfold unp_regions, unp_blocks, g_levels, v_bytes; cbn. reflexivity. Qed.

Lemma UNP_PURE_levels : forall g ls,
  UNP_PURE g -> Forall level_valid ls -> Z.of_nat (length ls) <= LIMIT -> levels_alloc (u_zone g) ls ->
  Z.of_nat (length ls) <= v_cap (u_cstk g) -> Z.of_nat (length ls) + 1 <= v_cap (u_vstk g) ->
  UNP_PURE (g_levels g ls).
Proof.
  intros g ls P V L LA C1 C2. unfold UNP_PURE in *. rewrite unp_regions_levels.
  unfold g_levels, u_D, vec_valid in *; cbn in *. decompose [and] P. splits; auto; lia.
Qed.

Lemma UNP_PURE_zone : forall g z',
  UNP_PURE g -> zone_valid z' -> z_addr z' = z_addr (u_zone g) -> levels_alloc z' (u_levels g) ->
  (z_chunks z' = z_chunks (u_zone g) \/
   exists c sz, z_chunks z' = (c, sz) :: z_chunks (u_zone g) /\ Forall (fun r => rdisj c (CHUNK_HDR + sz) (fst r) (snd r)) (unp_regions g)) ->
  UNP_PURE (g_zone g z').
Proof.
  intros g z' P Vz Ha LA Hch. unfold UNP_PURE in *. unfold g_zone, u_D in *; cbn in *. decompose [and] P.
  assert (RD : regions_disj (unp_regions {| u_ctx := u_ctx g; u_vis := u_vis g; u_data := u_data g; u_len := u_len g;
                                            u_levels := u_levels g; u_cstk := u_cstk g; u_vstk := u_vstk g; u_zone := z' |})).
  { unfold unp_regions, unp_blocks in *; cbn in *. rewrite Ha. destruct Hch as [->|(c & sz & -> & Hf)]; [assumption|].
    cbn [map]. change (?a :: ?b :: ?c0 :: ?d :: ?e :: chunk_block (c, sz) :: ?r) with ([a; b; c0; d; e] ++ chunk_block (c, sz) :: r).
    apply regions_disj_insert; [assumption|]. exact Hf. }
  splits; auto.
Qed.

Definition vec_regrow (v : vecg) (nb : Z) : vecg := mkVec nb (v_size v) (2 * v_cap v) (v_elt v).
Lemma vec_regrow_bytes : forall v nb, v_bytes (vec_regrow v nb) = 2 * v_bytes v.
Proof. intros. unfold vec_regrow, v_bytes; cbn. lia. Qed.
Lemma cap32_pos : forall c, cap32_b c = true -> EMBED_STACK <= c.
Proof. intros c H. unfold cap32_b in H. apply andb_prop in H. destruct H as [H _]. apply andb_prop in H. destruct H as [H _]. now apply Z.leb_le in H. Qed.
Lemma UNP_PURE_grow_cstk : forall g nb,
  UNP_PURE g -> v_size (u_cstk g) = v_cap (u_cstk g) -> nb <> 0 -> nb mod 8 = 0 ->
  Forall (fun r => rdisj nb (2 * v_bytes (u_cstk g)) (fst r) (snd r)) ((u_ctx g, CTX_SIZE) :: (u_vis g, VIS_SIZE) :: tl (unp_blocks g)) ->
  UNP_PURE (g_cstk g (vec_regrow (u_cstk g) nb)).
Proof.
  intros g nb P Hfull Hnb Hal Hf. unfold UNP_PURE in *. unfold g_cstk, u_D in *; cbn in *. decompose [and] P.
  match goal with Hc : cap32_b (v_cap (u_cstk g)) = true |- _ => pose proof (cap32_pos _ Hc) as Hcap end. unfold EMBED_STACK in Hcap.
  splits; auto.
  - unfold vec_valid, vec_regrow in *; cbn. lia.
  - unfold vec_regrow; cbn. apply cap32_double; [assumption|]. unfold vec_valid, LIMIT in *. lia.
  - unfold unp_regions, unp_blocks in *; cbn in *. rewrite vec_regrow_bytes. unfold vec_regrow; cbn.
    match goal with Hr : regions_disj _ |- _ =>
      change (?a :: ?b :: ?c :: ?r) with ([a; b] ++ c :: r); eapply regions_disj_replace; [exact Hr|]; cbn; exact Hf end.
Qed.
Lemma UNP_PURE_grow_vstk : forall g nb,
  UNP_PURE g -> v_size (u_vstk g) = v_cap (u_vstk g) -> nb <> 0 -> nb mod 8 = 0 ->
  Forall (fun r => rdisj nb (2 * v_bytes (u_vstk g)) (fst r) (snd r))
         ((u_ctx g, CTX_SIZE) :: (u_vis g, VIS_SIZE) :: (v_begin (u_cstk g), v_bytes (u_cstk g)) :: tl (tl (unp_blocks g))) ->
  UNP_PURE (g_vstk g (vec_regrow (u_vstk g) nb)).
Proof.
  intros g nb P Hfull Hnb Hal Hf. unfold UNP_PURE in *. unfold g_vstk, u_D in *; cbn in *. decompose [and] P.
  match goal with Hc : cap32_b (v_cap (u_vstk g)) = true |- _ => pose proof (cap32_pos _ Hc) as Hcap end. unfold EMBED_STACK in Hcap.
  splits; auto.
  - unfold vec_valid, vec_regrow in *; cbn. lia.
  - unfold vec_regrow; cbn. apply cap32_double; [assumption|]. unfold vec_valid, LIMIT in *. lia.
  - unfold unp_regions, unp_blocks in *; cbn in *. rewrite vec_regrow_bytes. unfold vec_regrow; cbn.
    match goal with Hr : regions_disj _ |- _ =>
      change (?a :: ?b :: ?c :: ?d :: ?r) with ([a; b; c] ++ d :: r); eapply regions_disj_replace; [exact Hr|]; cbn; exact Hf end.
Qed.

Lemma unp_regions_nth_chunk : forall g i ch, nth_error (z_chunks (u_zone g)) i = Some ch ->
  nth_error (unp_regions g) (5 + i) = Some (chunk_block ch).
Proof. intros g i ch H. unfold unp_regions, unp_blocks. cbn. now apply map_nth_error. Qed.

Lemma u32_at_inj : forall m a v v', u32_at m a v -> u32_at m a v' -> v = v'.
Proof. intros m a v v' H H'. unfold u32_at in *. congruence. Qed.
Lemma u64_at_inj : forall m a v v', u64_at m a v -> u64_at m a v' -> v = v'.
Proof. intros m a v v' H H'. unfold u64_at in *. congruence. Qed.
Lemma in_zone_sub : forall z a n a' n', in_zone z a n -> a <= a' -> a' + n' <= a + n -> in_zone z a' n'.
Proof. intros z a n a' n' (c & Hc & Hi) L1 L2. exists c. split; [exact Hc|]. unfold in_chunk in *. lia. Qed.
Lemma last_opt_cons : forall {A} (x : A) l, last_opt (x :: l) = match l with [] => Some x | _ => last_opt l end.
Proof.
  intros A x l. unfold last_opt. cbn [rev]. destruct l as [|y l']; [reflexivity|].
  destruct (rev (y :: l')) as [|r rs] eqn:E; [|reflexivity]. exfalso. cbn in E. destruct (rev l'); discriminate.
Qed.
Lemma last_opt_snoc : forall {A} (x : A) l, last_opt (l ++ [x]) = Some x.
Proof. intros. unfold last_opt. rewrite rev_app_distr. reflexivity. Qed.
Lemma pcontainers_snoc : forall root es e,
  pcontainers root (es ++ [e]) = pcontainers root es ++ [match last_opt es with None => root | Some e' => pe_obj e' end].
Proof.
  intros root es. revert root. induction es as [|x es IH]; intros root e; cbn -[last_opt]; [reflexivity|].
  rewrite IH, last_opt_cons. destruct es as [|p es']; [reflexivity|].
  pose proof (last_opt_spec (p :: es')) as Hs. destruct (last_opt (p :: es')); [reflexivity| discriminate].
Qed.

Definition pe_idx (e : pelem) (N : Z) : Z := pe_per e * (N - pe_rest e) + (if pe_map e && negb (pe_key e) then 1 else 0).

Lemma pelem_tree : forall m z K e ae o,
  pelem_ok m K e ae -> tree_at m z K o ->
  exists p kids, o = (if pe_map e then OMap p kids else OArr p kids) /\
    ((1 <= pe_rest e /\ p <> 0 /\ kids <> [] /\
      0 <= pe_idx e (obj_count o) < Z.of_nat (length kids) /\ pe_obj e = p + OBJ_SIZE * pe_idx e (obj_count o) /\
      (exists k, nth_error kids (Z.to_nat (pe_idx e (obj_count o))) = Some k /\ tree_at m z (pe_obj e) k) /\
      in_zone z (pe_obj e) OBJ_SIZE)
     \/ (ae = true /\ pe_rest e = 0 /\ pe_ptr e = 0 /\ kids = [] /\ p = 0)).
Proof.
  intros m z K e ae o (N & Q & T1 & T2 & T3 & ALT) Ht.
  assert (HO : OBJ_SIZE = 24) by reflexivity.
  pose proof Ht as Ht0. destruct Ht as [Ho Hw].
  assert (Hty : obj_type o = (if pe_map e then T_MAP else T_ARRAY)).
  { assert (u32_at m K (obj_type o)) by (destruct o; cbn in Ho; tauto). eapply u32_at_inj; eauto. }
  destruct (pe_map e) eqn:Em.
  -   destruct o; cbn in Hty; try discriminate. apply obj_at_map in Ho. destruct Ho as (_ & S1 & S2 & S3).
    pose proof (u32_at_inj _ _ _ _ S1 T2) as EN. pose proof (u64_at_inj _ _ _ _ S2 T3) as EQ. subst N Q.
    apply tree_wf_map in Hw. destruct Hw as (W0 & W1 & W2 & W3 & W4).
    exists p, kids. split; [reflexivity|]. cbn [obj_count].
    apply even_len_spec in W0. destruct W0 as [h Hh].
    assert (Hh2 : Z.of_nat (length kids) / 2 = Z.of_nat h). { rewrite Hh, Nat2Z.inj_mul. change (Z.of_nat 2) with 2. rewrite Z.mul_comm. apply Z.div_mul. lia. }
    rewrite Hh2 in *.
    destruct ALT as [(R1 & R2 & R3)|(A1 & A2 & A3 & A4 & A5)].
    + left. assert (Hne : kids <> []) by (intros ->; cbn in Hh; lia).
      assert (Hidx : 0 <= pe_idx e (Z.of_nat h) < Z.of_nat (length kids)).
      { unfold pe_idx, pe_per. rewrite Em. cbn [andb]. destruct (pe_key e); cbn; lia. }
      assert (Hobj : pe_obj e = p + OBJ_SIZE * pe_idx e (Z.of_nat h)).
      { unfold pe_obj, pe_idx, pe_per in *. rewrite Em in *. cbn [andb] in *. rewrite R3. destruct (pe_key e); cbn; lia. }
      split; [lia|]. split; [intros Hp; apply Hne; now apply W2|]. split; [exact Hne|]. split; [exact Hidx|]. split; [exact Hobj|].
      split.
      * destruct (nth_error kids (Z.to_nat (pe_idx e (Z.of_nat h)))) as [k|] eqn:Ek. 2:{ exfalso. apply nth_error_None in Ek. lia. }
        exists k. split; [reflexivity|]. rewrite Hobj. rewrite <- (Z2Nat.id (pe_idx e (Z.of_nat h))) by lia.
        exact (tree_at_kid m z K (OMap p kids) _ k Ht0 Ek).
      * destruct (W3 Hne) as [_ Hz]. eapply in_zone_sub; [exact Hz| lia | lia].
    + right. assert (kids = []) as ->. { destruct kids as [|x [|y l]]; [reflexivity| cbn in Hh; lia|]. exfalso. cbn in Hh. lia. }
      repeat split; auto.
  -   destruct o; cbn in Hty; try discriminate. apply obj_at_arr in Ho. destruct Ho as (_ & S1 & S2 & S3).
    pose proof (u32_at_inj _ _ _ _ S1 T2) as EN. pose proof (u64_at_inj _ _ _ _ S2 T3) as EQ. subst N Q.
    apply tree_wf_arr in Hw. destruct Hw as (W1 & W2 & W3 & W4).
    exists p, kids. split; [reflexivity|]. cbn [obj_count].
    destruct ALT as [(R1 & R2 & R3)|(A1 & A2 & A3 & A4 & A5)].
    + left. assert (Hne : kids <> []) by (intros ->; cbn in R1; lia).
      assert (Hidx : 0 <= pe_idx e (Z.of_nat (length kids)) < Z.of_nat (length kids)).
      { unfold pe_idx, pe_per. rewrite Em. cbn [andb]. lia. }
      assert (Hobj : pe_obj e = p + OBJ_SIZE * pe_idx e (Z.of_nat (length kids))).
      { unfold pe_obj, pe_idx, pe_per in *. rewrite Em in *. cbn [andb] in *. rewrite R3. lia. }
      split; [lia|]. split; [intros Hp; apply Hne; now apply W2|]. split; [exact Hne|]. split; [exact Hidx|]. split; [exact Hobj|].
      split.
      * destruct (nth_error kids (Z.to_nat (pe_idx e (Z.of_nat (length kids))))) as [k|] eqn:Ek. 2:{ exfalso. apply nth_error_None in Ek. lia. }
        exists k. split; [reflexivity|]. rewrite Hobj. rewrite <- (Z2Nat.id (pe_idx e (Z.of_nat (length kids)))) by lia.
        exact (tree_at_kid m z K (OArr p kids) _ k Ht0 Ek).
      * destruct (W3 Hne) as [_ Hz]. eapply in_zone_sub; [exact Hz| lia | lia].
    + right. assert (kids = []) as -> by (destruct kids; [reflexivity| cbn in A2; lia]).
      repeat split; auto.
Qed.

Lemma pelems_path : forall m z es root t pop,
  tree_at m z root t -> pelems_ok m (pcontainers root es) es pop ->
  (forall K, In K (pcontainers root es) -> (K = root \/ in_zone z K OBJ_SIZE) /\ exists tK, tree_at m z K tK) /\
  match last_opt es with
  | None => True
  | Some e => 1 <= pe_rest e -> (exists t', tree_at m z (pe_obj e) t') /\ in_zone z (pe_obj e) OBJ_SIZE
  end.
Proof.
  intros m z es. induction es as [|e es IH]; intros root t pop Ht Hok.
  - cbn. split; [intros K []| exact I].
  - cbn [pcontainers pelems_ok] in Hok |- *. destruct Hok as [He Hes]. rewrite last_opt_cons.
    destruct (pelem_tree m z root e _ t He Ht) as (p & kids & Eo & [(R1 & R2 & R3 & R4 & R5 & (k & Hk & Htk) & Rz)|(A1 & A2 & A3 & A4 & A5)]).
    + destruct (IH (pe_obj e) k pop Htk Hes) as [IH1 IH2]. split.
      * intros K [<-|HK]; [split; [now left| now exists t]|]. destruct (IH1 K HK) as [[->|Hz] HT]; split; auto.
      * destruct es as [|e' es']; [|exact IH2]. intros _. split; [now exists k| exact Rz].
    + destruct es as [|e' es']; [|discriminate]. split.
      * intros K [<-|[]]. split; [now left| now exists t].
      * intros Hr. lia.
Qed.

Definition pk_store_ok (pk : packg) (z : zoneg) (lo k : Z) : Prop :=
  (forall ch, In ch (z_chunks z) -> rdisj lo k (fst ch) (CHUNK_HDR + snd ch)) /\ rdisj lo k (p_root pk) OBJ_SIZE.
Definition pk_stores_ok (pk : packg) (z : zoneg) (m m' : bmem) : Prop :=
  exists ws : list (Z * Z), Forall (fun w => pk_store_ok pk z (fst w) (snd w)) ws /\ forall x, Forall (outside x) ws -> m' x = m x.
Lemma pk_stores_ok_nil : forall pk z m, pk_stores_ok pk z m m.
Proof. intros. exists []. split; [constructor|reflexivity]. Qed.
Lemma pk_stores_ok_cons : forall pk z m1 m2 m3 lo k,
  pk_stores_ok pk z m1 m2 -> pk_store_ok pk z lo k -> updated_within m2 m3 lo k -> pk_stores_ok pk z m1 m3.
Proof.
  intros pk z m1 m2 m3 lo k (ws & Hws & Hout) Hs Hu. exists ((lo, k) :: ws). split; [now constructor|].
  intros x Hx. inversion Hx as [|w' ws' Hw Hrest]; subst. rewrite (Hu x); [now apply Hout|]. unfold outside in Hw. cbn in Hw. lia.
Qed.
Lemma pk_stores_agree : forall pk z m m' c, zone_valid z -> pk_stores_ok pk z m m' ->
  (c = p_root pk \/ in_zone z c OBJ_SIZE) -> agree_on m m' c OBJ_SIZE.
Proof.
  intros pk z m m' c V (ws & Hws & Hout) Hc x Hx. apply Hout. apply Forall_forall. intros w Hw.
  apply Forall_forall with (x := w) in Hws; [|exact Hw]. destruct Hws as [S1 S2]. unfold outside.
  destruct Hc as [->|(ch & Hch & Hi)]; [unfold rdisj in S2; lia|].
  specialize (S1 ch Hch). unfold in_chunk, chunk_lo, chunk_hi, rdisj, CHUNK_HDR in *. lia.
Qed.
Lemma tree_at_pk_frame : forall pk z m m' a t, zone_valid z -> readable_mono m m' -> pk_stores_ok pk z m m' ->
  (a = p_root pk \/ in_zone z a OBJ_SIZE) -> tree_at m z a t -> tree_at m' z a t.
Proof.
  intros pk z m m' a t V R S Ha Ht. eapply tree_at_frame; [exact R| apply zone_grows_refl| |exact Ht].
  intros c Hc. rewrite obj_cells_hd in Hc. destruct Hc as [<-|Hc]; eapply pk_stores_agree; eauto. right. eapply tree_cells_in_zone; eauto.
Qed.
Lemma pelem_ok_frame : forall m m' K e ae, agree_on m m' K OBJ_SIZE -> pelem_ok m K e ae -> pelem_ok m' K e ae.
Proof.
  intros m m' K e ae Hag (N & Q & T1 & T2 & T3 & ALT). exists N, Q.
  split; [eapply u32_at_frame; [|exact T1]; eapply agree_on_sub; [exact Hag|lia|unfold OBJ_SIZE; lia]|].
  split; [eapply u32_at_frame; [|exact T2]; eapply agree_on_sub; [exact Hag|lia|unfold OBJ_SIZE; lia]|].
  split; [eapply u64_at_frame; [|exact T3]; eapply agree_on_sub; [exact Hag|lia|unfold OBJ_SIZE; lia]|]. exact ALT.
Qed.
Lemma pelems_ok_frame : forall m m' Ks es pop, (forall K, In K Ks -> agree_on m m' K OBJ_SIZE) -> pelems_ok m Ks es pop -> pelems_ok m' Ks es pop.
Proof.
  intros m m' Ks. induction Ks as [|K Ks IH]; intros [|e es] pop Hag H; cbn in *; try exact I.
  destruct H as [H1 H2]. split; [eapply pelem_ok_frame; [apply Hag; now left| exact H1]|]. apply IH; [|exact H2]. intros K' HK'. apply Hag. now right.
Qed.
Lemma pelems_ok_pk_frame : forall pk z m m' es t pop, zone_valid z -> readable_mono m m' -> pk_stores_ok pk z m m' ->
  tree_at m z (p_root pk) t -> pelems_ok m (pcontainers (p_root pk) es) es pop -> pelems_ok m' (pcontainers (p_root pk) es) es pop.
Proof.
  intros pk z m m' es t pop V R S Ht H. eapply pelems_ok_frame; [|exact H]. intros K HK.
  destruct (proj1 (pelems_path m z es (p_root pk) t pop Ht H) K HK) as [HK' _]. eapply pk_stores_agree; eauto.
Qed.

Lemma pelems_ok_weaken : forall m Ks es b, pelems_ok m Ks es b -> pelems_ok m Ks es true.
Proof.
  intros m Ks. induction Ks as [|K Ks IH]; intros [|e es] b H; cbn in *; try exact I. destruct H as [H1 H2]. split; [|eapply IH; eauto].
  destruct es; [|exact H1]. destruct H1 as (N & Q & A & B & C & ALT). exists N, Q. repeat split; auto.
  destruct ALT as [L|(-> & RR)]; [now left| right; auto].
Qed.
Lemma pelems_ok_app : forall m Ks1 Ks2 es1 es2 b, length Ks1 = length es1 -> es2 <> [] ->
  pelems_ok m (Ks1 ++ Ks2) (es1 ++ es2) b <-> pelems_ok m Ks1 es1 false /\ pelems_ok m Ks2 es2 b.
Proof.
  intros m Ks1. induction Ks1 as [|K Ks1 IH]; intros Ks2 [|e es1] es2 b Hlen Hne; cbn in Hlen |- *; try discriminate; [tauto|].
  rewrite IH by (lia || assumption).
  assert (E : match es1 ++ es2 with [] => b | _ :: _ => false end = match es1 with [] => false | _ :: _ => false end).
  { destruct es1; cbn; [destruct es2; [congruence|reflexivity]|reflexivity]. }
  rewrite E. tauto.
Qed.
Lemma pelems_ok_push : forall m Ks es K e ae, length Ks = length es ->
  pelems_ok m Ks es false -> pelem_ok m K e ae -> pelems_ok m (Ks ++ [K]) (es ++ [e]) ae.
Proof. intros m Ks es K e ae Hl H He. apply pelems_ok_app; auto; [discriminate|]. cbn. auto. Qed.
Lemma pelems_ok_pop : forall m Ks es K e b, length Ks = length es ->
  pelems_ok m (Ks ++ [K]) (es ++ [e]) b -> pelems_ok m Ks es false /\ pelem_ok m K e b.
Proof. intros m Ks es K e b Hl H. apply pelems_ok_app in H; auto; [|discriminate]. cbn in H. tauto. Qed.
Lemma pelems_ok_retop : forall m Ks es K e e' b b', length Ks = length es ->
  pelems_ok m (Ks ++ [K]) (es ++ [e]) b -> pelem_ok m K e' b' -> pelems_ok m (Ks ++ [K]) (es ++ [e']) b'.
Proof. intros m Ks es K e e' b b' Hl H He'. apply pelems_ok_pop in H; [|exact Hl]. apply pelems_ok_push; tauto. Qed.

Lemma pelem_ok_new : forall m K (is_map : bool) n p,
  u32_at m K (if is_map then T_MAP else T_ARRAY) -> u32_at m (K + 8) n -> u64_at m (K + 16) p -> 1 <= n -> p <> 0 ->
  pelem_ok m K (mkPE p n is_map is_map) false /\ pe_obj (mkPE p n is_map is_map) = p.
Proof.
  intros m K is_map n p T1 T2 T3 Hn Hp. split.
  - exists n, p. cbn. split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. left. unfold pe_per; cbn. destruct is_map; lia.
  - unfold pe_obj; cbn. destruct is_map; cbn; lia.
Qed.

Lemma pelem_ok_new_empty : forall m K (is_map : bool),
  u32_at m K (if is_map then T_MAP else T_ARRAY) -> u32_at m (K + 8) 0 -> u64_at m (K + 16) 0 ->
  pelem_ok m K (mkPE 0 0 is_map is_map) true.
Proof. intros m K is_map T1 T2 T3. exists 0, 0. cbn. split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. right. repeat split; auto. Qed.

Lemma pelem_ok_next : forall m K e e' ae, pelem_ok m K e ae -> 1 <= pe_rest e -> pe_next e = (e', NR_cont) -> pelem_ok m K e' false.
Proof.
  intros m K e e' ae (N & Q & T1 & T2 & T3 & ALT) Hr Hn.
  destruct ALT as [(A1 & A2 & A3)|(B1 & B2 & B3)]; [|lia].
  pose proof (pe_next_cont e e' Hn Hr) as (C1 & C2 & C3).
  destruct (pe_next_ptr_formula e e' N Q Hn A1 A3) as [F1 F2].
  exists N, Q. rewrite C2. split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. left. lia.
Qed.

Lemma pe_next_tree : forall m z K e e' ae o, pelem_ok m K e ae -> 1 <= pe_rest e -> pe_next e = (e', NR_cont) -> tree_at m z K o ->
  (exists k, tree_at m z (pe_obj e') k) /\ in_zone z (pe_obj e') OBJ_SIZE.
Proof.
  intros m z K e e' ae o He Hr Hn Ht.
  pose proof (pelem_ok_next m K e e' ae He Hr Hn) as He'.
  destruct (pe_next_cont e e' Hn Hr) as (_ & _ & C3).
  assert (Hr' : 1 <= pe_rest e') by (destruct C3 as [C|[C|C]]; lia).
  destruct (pelem_tree m z K e' false o He' Ht) as (p & kids & Eo & [(R1 & R2 & R3 & R4 & R5 & (k & Hk & Htk) & Rz)|(A1 & _)]); [|discriminate].
  split; [now exists k| exact Rz].
Qed.
