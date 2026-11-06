(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the TREE-TRANSPORT facts of pj_set's image-B walk (fuzz_preset asan-ubsan): pure lemmas
   over the reader's tree predicates (lib/A/PRH_Reader.v: pj_nodeR, pj_memsR, pj_hdrR, pj_cstrR, pj_agreeR, ...),
   generic over the segment list and two memories m m'. The walk's segments use them to carry an object tree across
   grow's realloc of the kids / keys arrays, the replacement of one member's value and the append of a new member.
   proves no function (kind: glue lemma). No machine step, no image constant.
   - pjst_mems_app / pjst_mems_one / pjst_mems_nth: split and join of a member list; the i-th member with the member
     lists before and after it.
   - pjst_node_lblk / pjst_mems_lblk: every block a node (a member list) lists is a block of lblk.
   - pjst_node_frame / pjst_mems_frame: PRH_Reader's pj_nodeR_frame with a change of block predicate.
   - pjst_node_move: a node's 56-byte header copied to d is the same tree at d (its subtree blocks stay in place).
   - pjst_mems_move: a member list moved to new value / key-pointer arrays (grow's realloc).
   The frame lemmas of PRH_Reader.v (pj_nodeR_frame, rd_u64_frame, pj_cstrR_frame, pj_itemsR_mono) are reused.
   Section fo, THE ORDERED FREE LIST (PRH_PjOrder.v's pj_foR / pf_oitemsR, pj_free's order) across the same moves, for
   the FREEORD-COPY conjuncts of the kit's tpj_set_specX (the result's order list) and the present arm's pj_free (old):
   - pjsf_oitems_app / pjsf_oitems_one: split and join of an ordered slot list;
   - pjsf_oshape_move / pjsf_foR_move: a node's 56-byte header copied to z is the same ordered tree at z;
   - pjsf_oitems_move: an object's ordered slot list moved to new value / key-pointer arrays (grow's realloc);
   - pjsf_obj_dest / pjsf_obj_intro: an object's ordered list is its slot list, then its kids and keys arrays;
   - pjsf_slots_map / pjsf_arrz_eq / pjsf_arrz_of / pjsf_oitems_member: the order list's requests against the
     model's fo cut at the arrays and at a member (PjFoMember.v's counting: pfm_oslots_len, pfm_slot_len, with
     PRH_PjOrder.pf_map_split);
   - pjsf_foR_n0 / pjsf_foR_lower / pjsf_oitems_lower: an order list at a depth above the tree's is one at any depth
     the tree fits (the header's member count is read once);
   - pjsf_fo_obj / pjsf_slots_app / pjsf_slots_nth / pjsf_depth_app / pjsf_depth_obj: fo and depth of an object.
   Numerals: 56 / 8 (LENGTH: the struct pj_value and a key pointer, in the slot strides), 8 .. 48 (LENGTH: the header's
   field offsets), 7 (56 = 7 * 8, for the alignment of the next slot), 6 (the pj type tag of an object). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
Import ListNotations.
Local Open Scope Z_scope.

Section tr.
Variable segs : list Segment.

(* ---- helpers ---- *)
Lemma pjst_agree_b : forall m m' (X : Z -> Prop) x, pj_agreeR segs m m' X -> X x -> mbyte segs m' x = mbyte segs m x.
Proof. intros m m' X x H Hx. exact (proj1 (H x Hx)). Qed.

Lemma pjst_u64_move : forall m m' a b v, rd_u64 segs m a v ->
  (forall k, (k < 8)%nat -> mbyte segs m' (b + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) -> rd_u64 segs m' b v.
Proof. intros m m' a b v [Hr Hv] E. split; [exact Hr|]. intros k Hk. rewrite E by exact Hk. exact (Hv k Hk). Qed.

Lemma pjst_cstr_sw : forall m lblk lblk' a k s, pj_cstrR segs m lblk a k s -> lblk' a k -> pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (_ & Hk & Hb) Hl. split; [exact Hl|]. split; [exact Hk|exact Hb]. Qed.

Lemma pjst_cstr_fsw : forall m m' lblk lblk' a k s, pj_cstrR segs m lblk a k s ->
  (forall x, a <= x < a + k -> mbyte segs m' x = mbyte segs m x) -> lblk' a k -> pj_cstrR segs m' lblk' a k s.
Proof.
intros m m' lblk lblk' a k s H E Hl.
exact (pjst_cstr_sw m' lblk lblk' a k s (pj_cstrR_frame segs m m' lblk a k s H E) Hl).
Qed.

(* PRH_Reader's pj_memsR_mono with a change of block predicate *)
Lemma pjst_mems_mono2 : forall m m' lblk lblk' (P P' : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall i nm u x k D1, nth_error l i = Some (nm, u) -> In (x, k) D -> incl D1 D ->
     rd_u64 segs m (ka + 8 * Z.of_nat i) x -> pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     rd_u64 segs m' (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m' lblk' x k nm /\ P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m' lblk' P' a ka l D.
Proof.
intros m m' lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
pose proof (HP 0%nat nm u x k D1 eq_refl (or_introl eq_refl)
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. replace (ka + 8 * Z.of_nat 0) with ka in HP0 by lia.
destruct (HP0 Hx Hc H1) as (Hx' & Hc' & H1'). split; [exact Hx'|]. split; [exact Hc'|].
split; [exact H1'|].
apply (IH (a + 56) (ka + 8) D2 H2). intros i nm' u' x' k' D1' Hi Hin Hinc Hx2 Hc2 HP2.
specialize (HP (S i) nm' u' x' k' D1' Hi (in_cons _ _ _ (in_or_app _ _ _ (or_intror Hin)))
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) in HP by lia.
exact (HP Hx2 Hc2 HP2).
Qed.

(* the blocks of an item list / a member list: the items' own blocks (and the key strings) *)
Lemma pjst_items_blk : forall (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> Z -> Prop) l a D,
  pj_itemsR P a l D -> (forall a0 u D1, In u l -> P a0 u D1 -> forall x k, In (x, k) D1 -> Q x k) ->
  forall x k, In (x, k) D -> Q x k.
Proof.
intros P Q l. induction l as [|u r IH]; intros a D H HP x k Hin; cbn [pj_itemsR] in H.
- subst D. destruct Hin.
- destruct H as (D1 & D2 & -> & H1 & H2). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + exact (HP a u D1 (or_introl eq_refl) H1 x k Hin).
  + apply (IH (a + 56) D2 H2); [|exact Hin]. intros a0 u0 D0 Hu. exact (HP a0 u0 D0 (or_intror Hu)).
Qed.

Lemma pjst_mems_blk : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall a0 nm u D1, In (nm, u) l -> P a0 u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  forall x k, In (x, k) D -> lblk x k.
Proof.
intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D H HP x k Hin; cbn [pj_memsR] in H.
- subst D. destruct Hin.
- destruct H as (x0 & k0 & D1 & D2 & -> & _ & Hc & H1 & H2). destruct Hin as [Hin|Hin].
  + injection Hin as <- <-. exact (proj1 Hc).
  + apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    * exact (HP a nm u D1 (or_introl eq_refl) H1 x k Hin).
    * apply (IH (a + 56) (ka + 8) D2 H2); [|exact Hin].
      intros a0 nm0 u0 D0 Hu. exact (HP a0 nm0 u0 D0 (or_intror Hu)).
Qed.

(* ---- S1: split / join of a member list ---- *)
Lemma pjst_mems_app : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) ms1 ms2 a ka D,
  pj_memsR segs m lblk P a ka (ms1 ++ ms2) D <->
  exists D1 D2, D = D1 ++ D2 /\ pj_memsR segs m lblk P a ka ms1 D1 /\
    pj_memsR segs m lblk P (a + 56 * Z.of_nat (length ms1)) (ka + 8 * Z.of_nat (length ms1)) ms2 D2.
Proof.
intros m lblk P ms1 ms2. induction ms1 as [|[nm u] r IH]; intros a ka D; cbn [app length pj_memsR].
- replace (a + 56 * Z.of_nat 0) with a by lia. replace (ka + 8 * Z.of_nat 0) with ka by lia. split.
  + intros H. exists [], D. split; [reflexivity|]. split; [reflexivity|exact H].
  + intros (D1 & D2 & -> & -> & H). exact H.
- replace (a + 56 * Z.of_nat (S (length r))) with (a + 56 + 56 * Z.of_nat (length r)) by lia.
  replace (ka + 8 * Z.of_nat (S (length r))) with (ka + 8 + 8 * Z.of_nat (length r)) by lia.
  split.
  + intros (x & k & D1 & D2 & -> & Hx & Hc & HP & H2).
    destruct (proj1 (IH (a + 56) (ka + 8) D2) H2) as (D3 & D4 & -> & H3 & H4).
    exists ((x, k) :: D1 ++ D3), D4. split; [cbn [app]; rewrite <- List.app_assoc; reflexivity|].
    split; [|exact H4]. exists x, k, D1, D3. split; [reflexivity|]. split; [exact Hx|]. split; [exact Hc|].
    split; [exact HP|exact H3].
  + intros (D3 & D4 & -> & (x & k & D1 & D2 & -> & Hx & Hc & HP & H2) & H4).
    exists x, k, D1, (D2 ++ D4). split; [cbn [app]; rewrite <- List.app_assoc; reflexivity|].
    split; [exact Hx|]. split; [exact Hc|]. split; [exact HP|].
    apply (proj2 (IH (a + 56) (ka + 8) (D2 ++ D4))). exists D2, D4.
    split; [reflexivity|]. split; [exact H2|exact H4].
Qed.

Lemma pjst_mems_one : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) a ka nm u D,
  pj_memsR segs m lblk P a ka [(nm, u)] D <->
  exists x k D1, D = (x, k) :: D1 /\ rd_u64 segs m ka x /\ pj_cstrR segs m lblk x k nm /\ P a u D1.
Proof.
intros m lblk P a ka nm u D. cbn [pj_memsR]. split.
- intros (x & k & D1 & D2 & -> & Hx & Hc & HP & ->). exists x, k, D1. rewrite List.app_nil_r.
  split; [reflexivity|]. split; [exact Hx|]. split; [exact Hc|exact HP].
- intros (x & k & D1 & -> & Hx & Hc & HP). exists x, k, D1, []. rewrite List.app_nil_r.
  split; [reflexivity|]. split; [exact Hx|]. split; [exact Hc|]. split; [exact HP|reflexivity].
Qed.

(* ---- S8: the i-th member, with the member lists before / after it ---- *)
Lemma pjst_mems_nth : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) mbs a ka D i nm u,
  pj_memsR segs m lblk P a ka mbs D -> nth_error mbs i = Some (nm, u) ->
  exists D1 x k Du D2, D = D1 ++ (x, k) :: Du ++ D2 /\
    pj_memsR segs m lblk P a ka (firstn i mbs) D1 /\
    rd_u64 segs m (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m lblk x k nm /\ P (a + 56 * Z.of_nat i) u Du /\
    pj_memsR segs m lblk P (a + 56 * Z.of_nat (S i)) (ka + 8 * Z.of_nat (S i)) (skipn (S i) mbs) D2.
Proof.
intros m lblk P mbs a ka D i. revert mbs a ka D.
induction i as [|i IH]; intros mbs a ka D nm u H Hn;
  (destruct mbs as [|[nm0 u0] r]; [cbn [nth_error] in Hn; discriminate|]); cbn [nth_error] in Hn;
  cbn [pj_memsR] in H; destruct H as (x0 & k0 & D10 & D20 & -> & Hx0 & Hc0 & HP0 & H2).
- injection Hn as -> ->. exists [], x0, k0, D10, D20.
  split; [reflexivity|]. split; [cbn [firstn pj_memsR]; reflexivity|].
  replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
  replace (a + 56 * Z.of_nat 1) with (a + 56) by lia. replace (ka + 8 * Z.of_nat 1) with (ka + 8) by lia.
  cbn [skipn]. split; [exact Hx0|]. split; [exact Hc0|]. split; [exact HP0|exact H2].
- destruct (IH r (a + 56) (ka + 8) D20 nm u H2 Hn) as (D1 & x & k & Du & D2 & -> & H1 & Hx & Hc & HP & H3).
  exists ((x0, k0) :: D10 ++ D1), x, k, Du, D2.
  split; [cbn [app]; rewrite <- List.app_assoc; reflexivity|].
  split.
  { cbn [firstn pj_memsR]. exists x0, k0, D10, D1. split; [reflexivity|]. split; [exact Hx0|].
    split; [exact Hc0|]. split; [exact HP0|exact H1]. }
  replace (ka + 8 + 8 * Z.of_nat i) with (ka + 8 * Z.of_nat (S i)) in Hx by lia.
  replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP by lia.
  replace (a + 56 + 56 * Z.of_nat (S i)) with (a + 56 * Z.of_nat (S (S i))) in H3 by lia.
  replace (ka + 8 + 8 * Z.of_nat (S i)) with (ka + 8 * Z.of_nat (S (S i))) in H3 by lia.
  cbn [skipn]. split; [exact Hx|]. split; [exact Hc|]. split; [exact HP|exact H3].
Qed.

(* ---- S2: every block a node lists is a block of lblk ---- *)
Lemma pjst_node_lblk : forall t m lblk p D, pj_nodeR segs m lblk p t D -> forall a k, In (a, k) D -> lblk a k.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m lblk p D H a0 k0 Hin; cbn [pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb).
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & k & Hc & ->). destruct Hin as [Hin|[]].
  injection Hin as <- <-. exact (proj1 Hc).
- destruct Hb as (_ & _ & _ & _ & k & Hc & ->). destruct Hin as [Hin|[]].
  injection Hin as <- <-. exact (proj1 Hc).
- destruct Hb as (_ & _ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + revert Hin. destruct (cap =? 0) eqn:Ec; intros Hin; [destruct Hin|].
    destruct Hin as [Hin|[]]. injection Hin as <- <-.
    destruct Hcap as [(H0 & _)|(_ & Hl)]; [apply Z.eqb_neq in Ec; contradiction|exact Hl].
  + apply (pjst_items_blk (pj_nodeR segs m lblk) lblk items kids Di Hi); [|exact Hin].
    intros a1 u D1 Hu HP. rewrite Forall_forall in IH. exact (IH u Hu m lblk a1 D1 HP).
- destruct Hb as (_ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  + revert Hin. destruct (cap =? 0) eqn:Ec; intros Hin; [destruct Hin|].
    apply Z.eqb_neq in Ec. destruct Hcap as [(H0 & _)|(_ & Hl1 & Hl2)]; [contradiction|].
    destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; assumption.
  + apply (pjst_mems_blk m lblk (pj_nodeR segs m lblk) members kids keys Di Hi); [|exact Hin].
    intros a1 nm u D1 Hu HP. rewrite Forall_forall in IH. exact (IH (nm, u) Hu m lblk a1 D1 HP).
Qed.

Lemma pjst_mems_lblk : forall mbs m lblk a ka D, pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka mbs D ->
  forall a' k, In (a', k) D -> lblk a' k.
Proof.
intros mbs m lblk a ka D H. apply (pjst_mems_blk m lblk _ mbs a ka D H).
intros a0 nm u D1 _ HP. exact (pjst_node_lblk u m lblk a0 D1 HP).
Qed.

(* a node keeps its shape under any block predicate that holds of its blocks (same memory) *)
Lemma pjst_node_sw : forall t m lblk lblk' p D, pj_nodeR segs m lblk p t D ->
  (forall a k, In (a, k) D -> lblk' a k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
  (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (pjst_cstr_sw m lblk lblk' str k txt Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (pjst_cstr_sw m lblk lblk' str k s Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [H0|(Hp & _)]; [left; exact H0|right; split; [exact Hp|]].
    apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros a0 k0 H0. apply HL. apply HDi. apply Hinc. exact H0.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [H0|(Hp & _ & _)]; [left; exact H0|right; split; [exact Hp|]].
    split.
    - apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
    - apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. right. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pjst_mems_mono2 m m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  intros i nm u x k D1 Hil Hxk Hinc Hx Hcs HP.
  split; [exact Hx|]. split; [apply (pjst_cstr_sw m lblk lblk' x k nm Hcs); apply HL; apply HDi; exact Hxk|].
  rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
  apply (IH m lblk lblk' _ D1 HP). intros a0 k0 H0. apply HL. apply HDi. apply Hinc. exact H0.
Qed.

(* ---- S3 / S4: frame with a change of block predicate ---- *)
Lemma pjst_node_frame : forall t m m' lblk lblk' p D, pj_nodeR segs m lblk p t D ->
  pj_agreeR segs m m' (pj_footR p D) -> (forall a k, In (a, k) D -> lblk' a k) -> pj_nodeR segs m' lblk' p t D.
Proof.
intros t m m' lblk lblk' p D H HM HL.
exact (pjst_node_sw t m' lblk lblk' p D (pj_nodeR_frame segs t m m' lblk p D H HM) HL).
Qed.

Lemma pjst_mems_frame : forall mbs m m' lblk lblk' a ka D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka mbs D ->
  pj_agreeR segs m m' (fun x => a <= x < a + 56 * Z.of_nat (length mbs) \/ ka <= x < ka + 8 * Z.of_nat (length mbs) \/
                              exists b, In b D /\ pj_holdsR b x) ->
  (forall a' k, In (a', k) D -> lblk' a' k) ->
  pj_memsR segs m' lblk' (pj_nodeR segs m' lblk') a ka mbs D.
Proof.
intros mbs m m' lblk lblk' a ka D H HM HL.
apply (pjst_mems_mono2 m m' lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk') mbs a ka D H).
intros i nm u x k D1 Hil Hxk Hinc Hx Hcs HP.
pose proof (pj_nth_lenR mbs i (nm, u) Hil) as Hlt.
split; [|split].
- apply (rd_u64_frame segs m m' _ x Hx). intros y Hy. apply (pjst_agree_b m m' _ y HM). cbv beta.
  right. left. lia.
- apply (pjst_cstr_fsw m m' lblk lblk' x k nm Hcs); [|exact (HL x k Hxk)].
  intros y Hy. apply (pjst_agree_b m m' _ y HM). cbv beta. right. right. exists (x, k).
  split; [exact Hxk|unfold pj_holdsR; cbn [fst snd]; exact Hy].
- apply (pjst_node_frame u m m' lblk lblk' _ D1 HP).
  + intros y Hy. apply HM. cbv beta. destruct Hy as [Hy|(b & Hb & Hy)].
    * left. lia.
    * right. right. exists b. split; [apply Hinc; exact Hb|exact Hy].
  + intros a0 k0 H0. apply HL. apply Hinc. exact H0.
Qed.

(* a node header copied byte for byte to a writable, aligned d is the same header at d *)
Lemma pjst_hdr_move : forall m m' w d ty num str kids keys n cap,
  pj_hdrR segs m w ty num str kids keys n cap ->
  (forall i, 0 <= i < 56 -> mbyte segs m' (d + i) = mbyte segs m (w + i)) ->
  pj_rwR segs m' d -> pj_hdrR segs m' d ty num str kids keys n cap.
Proof.
intros m m' w d ty num str kids keys n cap (_ & (Tr & Tv) & N & Sx & K & Y & Nn & C) E Hrw.
assert (F : forall off, 0 <= off <= 48 -> forall k, (k < 8)%nat ->
  mbyte segs m' (d + off + Z.of_nat k) = mbyte segs m (w + off + Z.of_nat k)).
{ intros off Ho k Hk. rewrite <- !Z.add_assoc. apply E. lia. }
split; [exact Hrw|].
split; [split; [exact Tr|]; intros k Hk; rewrite E by lia; exact (Tv k Hk)|].
split; [apply (pjst_u64_move m m' (w + 8) (d + 8) num N); intros k Hk; apply F; lia|].
split; [apply (pjst_u64_move m m' (w + 16) (d + 16) str Sx); intros k Hk; apply F; lia|].
split; [apply (pjst_u64_move m m' (w + 24) (d + 24) kids K); intros k Hk; apply F; lia|].
split; [apply (pjst_u64_move m m' (w + 32) (d + 32) keys Y); intros k Hk; apply F; lia|].
split; [apply (pjst_u64_move m m' (w + 40) (d + 40) n Nn); intros k Hk; apply F; lia|].
apply (pjst_u64_move m m' (w + 48) (d + 48) cap C); intros k Hk; apply F; lia.
Qed.

(* ---- S5: a node's 56-byte header copied to d (its subtree blocks stay where they are) is the same tree at d ---- *)
Lemma pjst_node_move : forall t m m' lblk lblk' w d D, pj_nodeR segs m lblk w t D ->
  (forall i, 0 <= i < 56 -> mbyte segs m' (d + i) = mbyte segs m (w + i)) ->
  pj_rwR segs m' d -> pj_apartR D d ->
  pj_agreeR segs m m' (fun x => exists b, In b D /\ pj_holdsR b x) ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  pj_nodeR segs m' lblk' d t D.
Proof.
intros t m m' lblk lblk' w d D H E Hrw Hap HM HL.
assert (HB : forall b x, In b D -> pj_holdsR b x -> mbyte segs m' x = mbyte segs m x).
{ intros b x Hb Hx. apply (pjst_agree_b m m' _ x HM). cbv beta. exists b. split; [exact Hb|exact Hx]. }
destruct t as [| | | txt bits | s | items | members]; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & _ & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Hap|]); exists num, str, kids, keys, n, cap;
  (split; [exact (pjst_hdr_move m m' w d _ _ _ _ _ _ _ Hh E Hrw)|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  assert (Hin : In (str, k) D) by (subst D; left; reflexivity).
  apply (pjst_cstr_fsw m m' lblk lblk' str k txt Hc); [|exact (HL str k Hin)].
  intros x Hx. apply (HB (str, k) x Hin). unfold pj_holdsR; cbn [fst snd]; exact Hx.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  assert (Hin : In (str, k) D) by (subst D; left; reflexivity).
  apply (pjst_cstr_fsw m m' lblk lblk' str k s Hc); [|exact (HL str k Hin)].
  intros x Hx. apply (HB (str, k) x Hin). unfold pj_holdsR; cbn [fst snd]; exact Hx.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [H0|(Hp & _)]; [left; exact H0|right; split; [exact Hp|]].
    apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP.
  pose proof (pj_nth_lenR items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D)
    by (subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity).
  apply (pjst_node_frame u m m' lblk lblk' _ D1 HP).
  + intros x Hx. apply HM. cbv beta. destruct Hx as [Hx|(b & Hb & Hx)].
    * exists (kids, 56 * cap). split; [exact Hin|unfold pj_holdsR; cbn [fst snd]; lia].
    * exists b. split; [apply HDi; apply Hinc; exact Hb|exact Hx].
  + intros a0 k0 H0. apply HL. apply HDi. apply Hinc. exact H0.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [H0|(Hp & _ & _)]; [left; exact H0|right; split; [exact Hp|]].
    split.
    - apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
    - apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. right. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pjst_mems_frame members m m' lblk lblk' kids keys Di Hi).
  + intros x Hx. apply HM. cbv beta in Hx |- *. destruct Hx as [Hx|[Hx|(b & Hb & Hx)]].
    * assert (Hp : 0 < cap) by lia.
      exists (kids, 56 * cap). split; [|unfold pj_holdsR; cbn [fst snd]; lia].
      subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
    * assert (Hp : 0 < cap) by lia.
      exists (keys, 8 * cap). split; [|unfold pj_holdsR; cbn [fst snd]; lia].
      subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. right. left. reflexivity.
    * exists b. split; [apply HDi; exact Hb|exact Hx].
  + intros a0 k0 H0. apply HL. apply HDi. exact H0.
Qed.

(* ---- S6: the member list moved to new arrays a' (values, 56 bytes each) and ka' (key pointers, 8 bytes each).
   The pj_memsR move across grow's realloc; plays the role of donor 427ad2ede0bc lib/B/Prog/pj_set_miss.v
   m_g_di :3263 / m_g_node_w :3196 / m_g_key :3282 in the old framework. ---- *)
Lemma pjst_mems_move : forall mbs m m' lblk lblk' a ka a' ka' D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka mbs D ->
  (forall j, 0 <= j < 56 * Z.of_nat (length mbs) -> mbyte segs m' (a' + j) = mbyte segs m (a + j)) ->
  (forall j, 0 <= j < 8 * Z.of_nat (length mbs) -> mbyte segs m' (ka' + j) = mbyte segs m (ka + j)) ->
  rd_rw segs m' a' (56 * Z.of_nat (length mbs)) -> a' mod 8 = 0 ->
  (forall b x, In b D -> pj_holdsR b x -> ~ (a' <= x < a' + 56 * Z.of_nat (length mbs))) ->
  pj_agreeR segs m m' (fun x => exists b, In b D /\ pj_holdsR b x) ->
  (forall a0 k, In (a0, k) D -> lblk' a0 k) ->
  pj_memsR segs m' lblk' (pj_nodeR segs m' lblk') a' ka' mbs D.
Proof.
intros mbs m m' lblk lblk'. induction mbs as [|[nm u] r IH];
  intros a ka a' ka' D H Ev Ek Hrw Hal Hap HM HL; cbn [pj_memsR] in H |- *; [exact H|].
cbn [length] in Ev, Ek, Hrw, Hap.
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & HP & H2).
exists x, k, D1, D2. split; [reflexivity|].
split.
{ apply (pjst_u64_move m m' ka ka' x Hx). intros j Hj. apply Ek. lia. }
split.
{ apply (pjst_cstr_fsw m m' lblk lblk' x k nm Hc); [|apply HL; left; reflexivity].
  intros y Hy. apply (pjst_agree_b m m' _ y HM). cbv beta. exists (x, k).
  split; [left; reflexivity|unfold pj_holdsR; cbn [fst snd]; exact Hy]. }
split.
{ apply (pjst_node_move u m m' lblk lblk' a a' D1 HP).
  - intros i Hi. apply Ev. lia.
  - split; [exact Hal|]. intros y Hy. apply Hrw. lia.
  - intros b y Hb Hy Hr. apply (Hap b y); [right; apply in_or_app; left; exact Hb|exact Hy|lia].
  - intros y Hy. apply HM. cbv beta in Hy |- *. destruct Hy as (b & Hb & Hy).
    exists b. split; [right; apply in_or_app; left; exact Hb|exact Hy].
  - intros a0 k0 H0. apply HL. right. apply in_or_app. left. exact H0. }
apply (IH (a + 56) (ka + 8) (a' + 56) (ka' + 8) D2 H2).
- intros j Hj. rewrite <- !Z.add_assoc. apply Ev. lia.
- intros j Hj. rewrite <- !Z.add_assoc. apply Ek. lia.
- intros y Hy. apply Hrw. lia.
- replace (a' + 56) with (a' + 7 * 8) by lia. rewrite Z.mod_add by lia. exact Hal.
- intros b y Hb Hy Hr. apply (Hap b y); [right; apply in_or_app; right; exact Hb|exact Hy|lia].
- intros y Hy. apply HM. cbv beta in Hy |- *. destruct Hy as (b & Hb & Hy).
  exists b. split; [right; apply in_or_app; right; exact Hb|exact Hy].
- intros a0 k0 H0. apply HL. right. apply in_or_app. right. exact H0.
Qed.

End tr.

(* ================================================================ the ordered free list (pj_free's order) *)
Section fo.
Variable segs : list Segment.
#[local] Abbreviation hb := (fun b : (Z * Z)%type => snd b + PresetReqAt.HEAD).

(* ---- an ordered slot list: split and join ---- *)
Lemma pjsf_oitems_app : forall m lblk (P : Z -> list (Z * Z) -> list (Z * Z) -> Prop) ks n1 n2 a ka D F,
  pf_oitemsR segs m lblk P ks a ka (n1 + n2) D F <->
  exists D1 F1 D2 F2, D = D1 ++ D2 /\ F = F1 ++ F2 /\ pf_oitemsR segs m lblk P ks a ka n1 D1 F1 /\
    pf_oitemsR segs m lblk P ks (a + 56 * Z.of_nat n1) (ka + 8 * Z.of_nat n1) n2 D2 F2.
Proof.
intros m lblk P ks n1. induction n1 as [|n1 IH]; intros n2 a ka D F; cbn [Nat.add pf_oitemsR].
- replace (a + 56 * Z.of_nat 0) with a by lia. replace (ka + 8 * Z.of_nat 0) with ka by lia. split.
  + intros H. exists [], [], D, F. split; [reflexivity|]. split; [reflexivity|].
    split; [split; reflexivity | exact H].
  + intros (D1 & F1 & D2 & F2 & -> & -> & [-> ->] & H). exact H.
- replace (a + 56 * Z.of_nat (S n1)) with (a + 56 + 56 * Z.of_nat n1) by lia.
  replace (ka + 8 * Z.of_nat (S n1)) with (ka + 8 + 8 * Z.of_nat n1) by lia.
  split.
  + intros (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & H2).
    destruct (proj1 (IH n2 (a + 56) (ka + 8) D2 F2) H2) as (D3 & F3 & D4 & F4 & -> & -> & H3 & H4).
    exists (Dk ++ D1 ++ D3), (F1 ++ Dk ++ F3), D4, F4.
    split; [rewrite !app_assoc; reflexivity|]. split; [rewrite !app_assoc; reflexivity|].
    split; [|exact H4].
    exists Dk, D1, F1, D3, F3. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk|].
    split; [exact H1 | exact H3].
  + intros (D3 & F3 & D4 & F4 & -> & -> & (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & H2) & H4).
    exists Dk, D1, F1, (D2 ++ D4), (F2 ++ F4).
    split; [rewrite !app_assoc; reflexivity|]. split; [rewrite !app_assoc; reflexivity|].
    split; [exact Hk|]. split; [exact H1|].
    apply (proj2 (IH n2 (a + 56) (ka + 8) (D2 ++ D4) (F2 ++ F4))). exists D2, F2, D4, F4.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact H2 | exact H4].
Qed.

Lemma pjsf_oitems_one : forall m lblk (P : Z -> list (Z * Z) -> list (Z * Z) -> Prop) ks a ka D F,
  pf_oitemsR segs m lblk P ks a ka 1 D F <->
  exists Dk D1 F1, D = Dk ++ D1 /\ F = F1 ++ Dk /\ pj_keyR segs m lblk ks ka Dk /\ P a D1 F1.
Proof.
intros m lblk P ks a ka D F. cbn [pf_oitemsR]. split.
- intros (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & [-> ->]). exists Dk, D1, F1.
  rewrite !app_nil_r. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk | exact H1].
- intros (Dk & D1 & F1 & -> & -> & Hk & H1). exists Dk, D1, F1, [], [].
  rewrite !app_nil_r. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk|].
  split; [exact H1 | split; reflexivity].
Qed.

(* ---- a node's header copied byte for byte to z (its blocks stay where they are): the same ordered node ---- *)
Lemma pjsf_oshape_move : forall m m' lblk lblk'
    (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> list (Z * Z) -> Prop) w z D F,
  pj_oshapeR segs m lblk Pi w D F ->
  (forall i, 0 <= i < 56 -> mbyte segs m' (z + i) = mbyte segs m (w + i)) ->
  pj_rwR segs m' z -> pj_apartR D z ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  (forall ks kids keys n Dk Dy Di Fi,
     (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) ->
     (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) ->
     (forall b, In b (Dk ++ Dy ++ Di) -> In b D) ->
     Pi ks kids keys n Di Fi -> Pi' ks kids keys n Di Fi) ->
  pj_oshapeR segs m' lblk' Pi' z D F.
Proof.
intros m m' lblk lblk' Pi Pi' w z D F H E Hrw Hap HL HPi'. unfold pj_oshapeR in H |- *.
destruct H as (Hnd & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
  Hh & Hs & Hk & Hy & Hp & HPi & ->).
assert (HinD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hb]).
split; [exact Hnd|]. split; [exact Hap|].
exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi.
split; [exact (pjst_hdr_move segs m m' w z ty num str kids keys n cap Hh E Hrw)|].
split.
{ destruct Hs as [Hs|(k & _ & ->)]; [left; exact Hs|].
  right. exists k. split; [|reflexivity]. apply HL. apply HinD. apply in_or_app. left. apply in_eq. }
split.
{ destruct Hk as [Hk'|(k & _ & Hnk & ->)]; [left; exact Hk'|].
  right. exists k. split; [|split; [exact Hnk | reflexivity]]. apply HL. apply HinD.
  apply in_or_app. right. apply in_or_app. left. apply in_eq. }
split.
{ destruct Hy as [Hy'|(Hks & k & _ & Hnk & ->)]; [left; exact Hy'|].
  right. split; [exact Hks|]. exists k. split; [|split; [exact Hnk | reflexivity]]. apply HL. apply HinD.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. apply in_eq. }
split; [exact Hp|].
split; [|reflexivity].
apply (HPi' ks kids keys n Dk Dy Di Fi Hk Hy); [|exact HPi].
intros b Hb. apply HinD. apply in_or_app. right. exact Hb.
Qed.

(* pjst_node_move for the ordered list *)
Lemma pjsf_foR_move : forall d m m' lblk lblk' w z D F,
  pj_foR segs m lblk d w D F ->
  (forall i, 0 <= i < 56 -> mbyte segs m' (z + i) = mbyte segs m (w + i)) ->
  pj_rwR segs m' z -> pj_apartR D z ->
  pj_agreeR segs m m' (fun x => exists b, In b D /\ pj_holdsR b x) ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  pj_foR segs m' lblk' d z D F.
Proof.
intros d m m' lblk lblk' w z D F H E Hrw Hap HM HL.
destruct d as [|d]; cbn [pj_foR] in H |- *;
  apply (pjsf_oshape_move m m' lblk lblk' _ _ w z D F H E Hrw Hap HL).
- intros ks kids keys n Dk Dy Di Fi _ _ _ HPi. exact HPi.
- intros ks kids keys n Dk Dy Di Fi Hk Hy HinD HPi. cbv beta in HPi |- *.
  apply (pf_oitemsR_frame segs d m m' lblk lblk' ks kids keys (Z.to_nat n) Di Fi HPi).
  + intros x k Hin. apply HL. apply HinD. apply in_or_app. right. apply in_or_app. right. exact Hin.
  + apply (pf_agree_mono segs m m' _ _ HM). unfold pf_ofoot.
    intros y [Hy'|[(Hks & Hy')|(b & Hb & Hy')]].
    * destruct Hk as [(-> & -> & ->)|(k & _ & Hnk & ->)]; [cbn in Hy'; lia|].
      exists (kids, k). split; [apply HinD; apply in_or_app; left; apply in_eq|].
      unfold pj_holdsR; cbn [fst snd]. lia.
    * destruct Hy as [(-> & -> & ->)|(_ & k & _ & Hnk & ->)]; [discriminate Hks|].
      exists (keys, k). split; [apply HinD; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
      unfold pj_holdsR; cbn [fst snd]. lia.
    * exists b. split; [|exact Hy']. apply HinD. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

(* pjst_mems_move for the ordered slot list of an object (n slots) *)
Lemma pjsf_oitems_move : forall d m m' lblk lblk' n a ka a' ka' D F,
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) true a ka n D F ->
  (forall j, 0 <= j < 56 * Z.of_nat n -> mbyte segs m' (a' + j) = mbyte segs m (a + j)) ->
  (forall j, 0 <= j < 8 * Z.of_nat n -> mbyte segs m' (ka' + j) = mbyte segs m (ka + j)) ->
  rd_rw segs m' a' (56 * Z.of_nat n) -> a' mod 8 = 0 ->
  (forall b x, In b D -> pj_holdsR b x -> ~ (a' <= x < a' + 56 * Z.of_nat n)) ->
  pj_agreeR segs m m' (fun x => exists b, In b D /\ pj_holdsR b x) ->
  (forall a0 k, In (a0, k) D -> lblk' a0 k) ->
  pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' d) true a' ka' n D F.
Proof.
intros d m m' lblk lblk' n. induction n as [|n IH];
  intros a ka a' ka' D F H Ev Ek Hrw Hal Hap HM HL; cbn [pf_oitemsR] in H |- *; [exact H|].
destruct H as (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & H2).
exists Dk, D1, F1, D2, F2. split; [reflexivity|]. split; [reflexivity|].
split.
{ unfold pj_keyR in Hk |- *. destruct Hk as (x & Hx & Hc). exists x. split.
  - apply (pjst_u64_move segs m m' ka ka' x Hx). intros j Hj. apply Ek. lia.
  - destruct Hc as [Hc|(k & _ & ->)]; [left; exact Hc|]. right. exists k. split; [|reflexivity].
    apply HL. apply in_or_app. left. apply in_eq. }
split.
{ apply (pjsf_foR_move d m m' lblk lblk' a a' D1 F1 H1).
  - intros i Hi. apply Ev. lia.
  - split; [exact Hal|]. intros y Hy. apply Hrw. lia.
  - intros b y Hb Hy Hr. apply (Hap b y); [apply in_or_app; right; apply in_or_app; left; exact Hb|exact Hy|lia].
  - intros y Hy. apply HM. cbv beta in Hy |- *. destruct Hy as (b & Hb & Hy).
    exists b. split; [apply in_or_app; right; apply in_or_app; left; exact Hb|exact Hy].
  - intros a0 k0 H0. apply HL. apply in_or_app. right. apply in_or_app. left. exact H0. }
apply (IH (a + 56) (ka + 8) (a' + 56) (ka' + 8) D2 F2 H2).
- intros j Hj. rewrite <- !Z.add_assoc. apply Ev. lia.
- intros j Hj. rewrite <- !Z.add_assoc. apply Ek. lia.
- intros y Hy. apply Hrw. lia.
- replace (a' + 56) with (a' + 7 * 8) by lia. rewrite Z.mod_add by lia. exact Hal.
- intros b y Hb Hy Hr. apply (Hap b y); [apply in_or_app; right; apply in_or_app; right; exact Hb|exact Hy|lia].
- intros y Hy. apply HM. cbv beta in Hy |- *. destruct Hy as (b & Hb & Hy).
  exists b. split; [apply in_or_app; right; apply in_or_app; right; exact Hb|exact Hy].
- intros a0 k0 H0. apply HL. apply in_or_app. right. apply in_or_app. right. exact H0.
Qed.

(* ---- an object's ordered list: its slot list, then the kids and keys arrays (lblk functional, no block at 0) ---- *)
Lemma pjsf_obj_dest : forall m lblk d o ms D F,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  pj_nodeR segs m lblk o (PjTree.JObj ms) D ->
  pj_foR segs m lblk (S d) o D F ->
  exists num kids keys cap Dm Di Fi,
    pj_hdrR segs m o 6 num 0 kids keys (Z.of_nat (length ms)) cap /\
    pj_memsR segs m lblk (pj_nodeR segs m lblk) kids keys ms Dm /\
    pf_oitemsR segs m lblk (pj_foR segs m lblk d) true kids keys (length ms) Di Fi /\
    Permutation Dm Di /\
    ((cap = 0 /\ ms = [] /\ D = [] /\ F = []) \/
     (0 < cap /\ Z.of_nat (length ms) <= cap /\ lblk kids (56 * cap) /\ lblk keys (8 * cap) /\
      D = (kids, 56 * cap) :: (keys, 8 * cap) :: Dm /\ F = Fi ++ [(kids, 56 * cap); (keys, 8 * cap)])).
Proof.
intros m lblk d o ms D F HFn HZ HN HF.
cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & HB).
destruct HB as (Es & En & Hc & Hcap & Dm & ED & Hm).
cbn [pj_foR pj_oshapeR] in HF.
destruct HF as (_ & _ & ty' & num' & str' & kids' & keys' & n' & cap' & ks & Ds & Dk & Dy & Di & Fi &
  Hh' & Hs & Hk & Hy & Hp & HPi & EF).
destruct (PjFoMember.pfm_hdr_det segs m o _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hh Hh') as (-> & -> & -> & ->).
rewrite (PjFoMember.pfm_ds0 lblk str Ds HZ Es Hs) in Hp, EF.
rewrite En, Nat2Z.id in HPi.
exists num, kids, keys, cap, Dm, Di, Fi.
split; [rewrite Es, En in Hh; exact Hh|].
split; [exact Hm|].
destruct Hcap as [(Ec & Ek & Ey)|(Hcp & Hlk & Hly)].
- subst cap kids keys.
  assert (Hms : ms = []) by (destruct ms as [|mm r]; [reflexivity | cbn [length] in En; lia]).
  subst ms. cbn [pj_memsR] in Hm. subst Dm. cbn in ED. subst D.
  destruct (PjFoMember.pfm_dk0 lblk 0 n Dk HZ eq_refl Hk) as [_ ->].
  destruct (PjFoMember.pfm_dy0 lblk 0 n ks Dy HZ eq_refl Hy) as [-> ->].
  cbn [app] in Hp. apply Permutation_nil in Hp. subst Di.
  cbn [length pf_oitemsR] in HPi. destruct HPi as [_ ->].
  split; [cbn [length pf_oitemsR]; split; reflexivity|].
  split; [apply perm_nil|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. subst F. reflexivity.
- rewrite (PjFoMember.pfm_dk1 lblk kids n (56 * cap) Dk HFn HZ Hlk Hk) in Hp, EF.
  destruct (PjFoMember.pfm_dy1 lblk keys n (8 * cap) ks Dy HFn HZ Hly Hy) as [-> ->].
  rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. subst D.
  cbn [app] in Hp, EF.
  split; [exact HPi|].
  split; [exact (Permutation_cons_inv (Permutation_cons_inv Hp))|].
  right. split; [exact Hcp|]. split; [lia|]. split; [exact Hlk|]. split; [exact Hly|].
  split; [reflexivity | exact EF].
Qed.

Lemma pjsf_obj_intro : forall m lblk d o num kids keys n cap Di Fi,
  pj_hdrR segs m o 6 num 0 kids keys n cap -> 0 <= n <= cap -> 0 < cap ->
  lblk kids (56 * cap) -> lblk keys (8 * cap) ->
  NoDup ((kids, 56 * cap) :: (keys, 8 * cap) :: Di) ->
  pj_apartR ((kids, 56 * cap) :: (keys, 8 * cap) :: Di) o ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) true kids keys (Z.to_nat n) Di Fi ->
  pj_foR segs m lblk (S d) o ((kids, 56 * cap) :: (keys, 8 * cap) :: Di) (Fi ++ [(kids, 56 * cap); (keys, 8 * cap)]).
Proof.
intros m lblk d o num kids keys n cap Di Fi Hh Hn Hcp Hlk Hly Hnd Hap HPi.
cbn [pj_foR pj_oshapeR]. split; [exact Hnd|]. split; [exact Hap|].
exists 6, num, 0, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di, Fi.
split; [exact Hh|].
split; [left; split; reflexivity|].
split; [right; exists (56 * cap); split; [exact Hlk | split; [lia | reflexivity]]|].
split; [right; split; [reflexivity|]; exists (8 * cap); split; [exact Hly | split; [lia | reflexivity]]|].
split; [apply Permutation_refl|].
split; [exact HPi | reflexivity].
Qed.

(* ---- the requests of an order list against fo ---- *)
Lemma pjsf_fo_obj : forall (ms : list (list Z * PjTree.jv)),
  PresetReqAt.fo (PjTree.JObj ms) =
    PjFoMember.pfm_slots PresetReqAtNoMiss.kblk ms ++ PresetReqAt.arrz true (PresetReqAt.ncap (length ms)).
Proof. intros ms. reflexivity. Qed.

Lemma pjsf_slots_app : forall (K : list Z -> Z) (ms1 ms2 : list (list Z * PjTree.jv)),
  PjFoMember.pfm_slots K (ms1 ++ ms2) = PjFoMember.pfm_slots K ms1 ++ PjFoMember.pfm_slots K ms2.
Proof. intros K ms1 ms2. unfold PjFoMember.pfm_slots. rewrite map_app, concat_app. reflexivity. Qed.

Lemma pjsf_slots_nth : forall (K : list Z -> Z) (ms : list (list Z * PjTree.jv)) i nm u,
  nth_error ms i = Some (nm, u) ->
  PjFoMember.pfm_slots K ms =
    PjFoMember.pfm_slots K (firstn i ms) ++ PresetReqAt.fo u ++ K nm :: PjFoMember.pfm_slots K (skipn (S i) ms).
Proof.
intros K ms. induction ms as [|[nm0 u0] r IH]; intros i nm u H; [destruct i; discriminate H|].
destruct i as [|i]; cbn [nth_error] in H.
- injection H as -> ->. rewrite PjFoMember.pfm_slots_cons. reflexivity.
- cbn [firstn skipn]. rewrite !PjFoMember.pfm_slots_cons, (IH i nm u H). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma pjsf_slots_map : forall m lblk d (K : list Z -> Z) ms a ka Dm Di Fi (A : list (Z * Z)) (X : list Z),
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Dm ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) true a ka (length ms) Di Fi ->
  map hb (Fi ++ A) = PjFoMember.pfm_slots K ms ++ X -> (length X <= length A)%nat ->
  map hb Fi = PjFoMember.pfm_slots K ms /\ map hb A = X.
Proof.
intros m lblk d K ms a ka Dm Di Fi A X HFn HZ Hm HPi HM HL.
exact (pf_map_split Fi A (PjFoMember.pfm_slots K ms) X HM
  (PjFoMember.pfm_oslots_len segs m lblk d K ms a ka Dm Di Fi HFn HZ Hm HPi) HL).
Qed.

Lemma pjsf_arrz_eq : forall kids keys cap c,
  map hb [(kids, 56 * cap); (keys, 8 * cap)] = PresetReqAt.arrz true c -> cap = Z.of_nat c /\ (0 < c)%nat.
Proof.
intros kids keys cap c H. destruct c as [|c']; cbn [PresetReqAt.arrz map snd] in H; [discriminate H|].
injection H as H1 _. split; lia.
Qed.

Lemma pjsf_arrz_of : forall kids keys c, (0 < c)%nat ->
  map hb [(kids, 56 * Z.of_nat c); (keys, 8 * Z.of_nat c)] = PresetReqAt.arrz true c.
Proof.
intros kids keys c Hc. destruct c as [|c']; [lia|]. cbn [PresetReqAt.arrz map snd].
f_equal; [lia | f_equal; lia].
Qed.

(* member i of an object's ordered slot list whose requests are fo's slots: its slot, cut where the counts force it *)
Lemma pjsf_oitems_member : forall m lblk d (K : list Z -> Z) ms kids keys Dm Di Fi i kname vi,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) kids keys ms Dm ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) true kids keys (length ms) Di Fi ->
  map hb Fi = PjFoMember.pfm_slots K ms -> nth_error ms i = Some (kname, vi) ->
  exists Di1 Fi1 Dk Du Fu Di2 Fi2,
    Di = Di1 ++ Dk ++ Du ++ Di2 /\ Fi = Fi1 ++ Fu ++ Dk ++ Fi2 /\
    pf_oitemsR segs m lblk (pj_foR segs m lblk d) true kids keys i Di1 Fi1 /\
    pj_keyR segs m lblk true (keys + 8 * Z.of_nat i) Dk /\
    pj_foR segs m lblk d (kids + 56 * Z.of_nat i) Du Fu /\
    pf_oitemsR segs m lblk (pj_foR segs m lblk d) true (kids + 56 * Z.of_nat (S i)) (keys + 8 * Z.of_nat (S i))
      (length ms - S i) Di2 Fi2 /\
    map hb Fi1 = PjFoMember.pfm_slots K (firstn i ms) /\ map hb Fu = PresetReqAt.fo vi /\
    map hb Dk = [K kname] /\ map hb Fi2 = PjFoMember.pfm_slots K (skipn (S i) ms).
Proof.
intros m lblk d K ms kids keys Dm Di Fi i kname vi HFn HZ Hm HPi HM Hnth.
pose proof (pj_nth_lenR ms i (kname, vi) Hnth) as Hi.
destruct (pjst_mems_nth segs m lblk _ ms kids keys Dm i kname vi Hm Hnth)
  as (D1 & x & k & Du0 & D2 & EDm & HM1 & Hx & Hcs & HU & HM2).
assert (EL : length ms = (i + S (length ms - S i))%nat) by lia.
rewrite EL in HPi.
destruct (proj1 (pjsf_oitems_app m lblk _ true i (S (length ms - S i)) kids keys Di Fi) HPi)
  as (Di1 & Fi1 & DiR & FiR & -> & -> & H1 & HR).
cbn [pf_oitemsR] in HR.
destruct HR as (Dk & Du & Fu & Di2 & Fi2 & -> & -> & Hk & HU' & H2).
replace (kids + 56 * Z.of_nat i + 56) with (kids + 56 * Z.of_nat (S i)) in H2 by lia.
replace (keys + 8 * Z.of_nat i + 8) with (keys + 8 * Z.of_nat (S i)) in H2 by lia.
assert (Lf : length (firstn i ms) = i) by (apply firstn_length_le; lia).
assert (Ls : length (skipn (S i) ms) = (length ms - S i)%nat) by (apply length_skipn).
pose proof (PjFoMember.pfm_oslots_len segs m lblk d K (firstn i ms) kids keys D1 Di1 Fi1 HFn HZ HM1
  ltac:(rewrite Lf; exact H1)) as L1.
pose proof (PjFoMember.pfm_slot_len segs m lblk d (kids + 56 * Z.of_nat i) vi Du0 Du Fu HFn HZ HU HU') as LU.
pose proof (PjFoMember.pfm_oslots_len segs m lblk d K (skipn (S i) ms) _ _ D2 Di2 Fi2 HFn HZ HM2
  ltac:(rewrite Ls; exact H2)) as L2.
pose proof (PjFoMember.pfm_key1 segs m lblk (keys + 8 * Z.of_nat i) x k kname Dk HFn HZ Hx Hcs Hk) as EDk.
assert (LDk : length Dk = 1%nat) by (rewrite EDk; reflexivity).
rewrite (pjsf_slots_nth K ms i kname vi Hnth) in HM.
assert (L1' : (length (PresetReqAt.fo vi ++ K kname :: PjFoMember.pfm_slots K (skipn (S i) ms)) <=
  length (Fu ++ Dk ++ Fi2))%nat) by (rewrite !length_app; cbn [length]; lia).
destruct (pf_map_split Fi1 (Fu ++ Dk ++ Fi2) (PjFoMember.pfm_slots K (firstn i ms))
  (PresetReqAt.fo vi ++ K kname :: PjFoMember.pfm_slots K (skipn (S i) ms)) HM L1 L1') as [E1 E2].
assert (LU' : (length (K kname :: PjFoMember.pfm_slots K (skipn (S i) ms)) <= length (Dk ++ Fi2))%nat)
  by (rewrite length_app; cbn [length]; lia).
destruct (pf_map_split Fu (Dk ++ Fi2) (PresetReqAt.fo vi) (K kname :: PjFoMember.pfm_slots K (skipn (S i) ms))
  E2 LU LU') as [E3 E4].
assert (LK : (length [K kname] <= length Dk)%nat) by (cbn [length]; lia).
destruct (pf_map_split Dk Fi2 [K kname] (PjFoMember.pfm_slots K (skipn (S i) ms)) E4 LK L2) as [E5 E6].
exists Di1, Fi1, Dk, Du, Fu, Di2, Fi2.
split; [reflexivity|]. split; [reflexivity|].
split; [exact H1|]. split; [exact Hk|]. split; [exact HU'|]. split; [exact H2|].
split; [exact E1|]. split; [exact E3|]. split; [exact E5 | exact E6].
Qed.

(* ---- depth: an order list read at a depth the tree fits ---- *)
(* a node whose header holds no member: its order list is the same at every depth *)
Lemma pjsf_foR_n0 : forall m lblk d d' p D F ty num str kids keys cap,
  pj_hdrR segs m p ty num str kids keys 0 cap -> pj_foR segs m lblk d p D F -> pj_foR segs m lblk d' p D F.
Proof.
intros m lblk d d' p D F ty num str kids keys cap Hh0 H.
assert (HND : NoDup D /\ pj_apartR D p)
  by (destruct d; cbn [pj_foR pj_oshapeR] in H; destruct H as (Hnd & Hap & _); split; assumption).
destruct HND as [Hnd Hap].
destruct (PjFoMember.pfm_foR_inv segs m lblk d p D F H) as (ty' & num' & str' & kids' & keys' & n' & cap' & ks &
  Ds & Dk & Dy & Di & Fi & Hh & Hs & Hk & Hy & Hp & EF & Hd).
destruct (PjFoMember.pfm_hdr_det segs m p _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hh0 Hh) as (_ & _ & _ & En).
assert (E0 : Di = [] /\ Fi = []).
{ destruct Hd as [(_ & _ & HD & HF)|(d0 & _ & HO)]; [split; assumption|].
  rewrite En in HO. change (Z.to_nat 0) with O in HO. cbn [pf_oitemsR] in HO. exact HO. }
destruct E0 as [-> ->]. subst F.
destruct d' as [|d']; cbn [pj_foR pj_oshapeR]; (split; [exact Hnd|]); (split; [exact Hap|]);
  exists ty', num', str', kids', keys', n', cap', ks, Ds, Dk, Dy, [], [];
  (split; [exact Hh|]); (split; [exact Hs|]); (split; [exact Hk|]); (split; [exact Hy|]);
  (split; [exact Hp|]); (split; [|reflexivity]).
- split; [exact En | split; reflexivity].
- rewrite En. change (Z.to_nat 0) with O. cbn [pf_oitemsR]. split; reflexivity.
Qed.

Lemma pjsf_items_lower : forall m lblk d d' (items : list PjTree.jv) a ka ks Di0 Di Fi,
  Forall (fun u => forall m lblk p D d D' F d', pj_nodeR segs m lblk p u D -> pj_foR segs m lblk d p D' F ->
     (PjTree.depth u <= d')%nat -> pj_foR segs m lblk d' p D' F) items ->
  pj_itemsR (pj_nodeR segs m lblk) a items Di0 ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) ks a ka (length items) Di Fi ->
  (forall u, In u items -> (PjTree.depth u <= d')%nat) ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d') ks a ka (length items) Di Fi.
Proof.
intros m lblk d d' items a ka ks Di0 Di Fi HA. revert a ka Di0 Di Fi.
induction HA as [|u r Hu Hr IHr]; intros a ka Di0 Di Fi Hi HO Hd; cbn [pj_itemsR] in Hi;
  cbn [length pf_oitemsR] in HO |- *.
- exact HO.
- destruct Hi as (D1 & D2 & -> & H1 & H2).
  destruct HO as (Dk & D1' & F1 & D2' & F2 & -> & -> & Hk & H1' & H2').
  exists Dk, D1', F1, D2', F2. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk|].
  split.
  + exact (Hu m lblk a D1 d D1' F1 d' H1 H1' (Hd u (or_introl eq_refl))).
  + exact (IHr (a + 56) (ka + 8) D2 D2' F2 H2 H2' (fun v Hv => Hd v (or_intror Hv))).
Qed.

Lemma pjsf_mems_lower : forall m lblk d d' (ms : list (list Z * PjTree.jv)) a ka ks Dm Di Fi,
  Forall (fun mm => forall m lblk p D d D' F d', pj_nodeR segs m lblk p (snd mm) D ->
     pj_foR segs m lblk d p D' F -> (PjTree.depth (snd mm) <= d')%nat -> pj_foR segs m lblk d' p D' F) ms ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Dm ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) ks a ka (length ms) Di Fi ->
  (forall nm u, In (nm, u) ms -> (PjTree.depth u <= d')%nat) ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d') ks a ka (length ms) Di Fi.
Proof.
intros m lblk d d' ms a ka ks Dm Di Fi HA. revert a ka Dm Di Fi.
induction HA as [|[nm u] r Hu Hr IHr]; intros a ka Dm Di Fi Hm HO Hd; cbn [pj_memsR] in Hm;
  cbn [length pf_oitemsR] in HO |- *.
- exact HO.
- destruct Hm as (x & k & D1 & D2 & -> & Hx & Hcs & H1 & H2).
  destruct HO as (Dk & D1' & F1 & D2' & F2 & -> & -> & Hk & H1' & H2').
  exists Dk, D1', F1, D2', F2. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk|].
  split.
  + exact (Hu m lblk a D1 d D1' F1 d' H1 H1' (Hd nm u (or_introl eq_refl))).
  + exact (IHr (a + 56) (ka + 8) D2 D2' F2 H2 H2' (fun nm' v Hv => Hd nm' v (or_intror Hv))).
Qed.

Lemma pjsf_foR_lower : forall t m lblk p D d D' F d',
  pj_nodeR segs m lblk p t D -> pj_foR segs m lblk d p D' F -> (PjTree.depth t <= d')%nat ->
  pj_foR segs m lblk d' p D' F.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind';
  intros m lblk p D d D' F d' HN HF Hd; cbn [pj_nodeR] in HN;
  destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & HB).
- destruct HB as (_ & _ & _ & -> & _ & _). exact (pjsf_foR_n0 m lblk d d' p D' F _ _ _ _ _ _ Hh HF).
- destruct HB as (_ & _ & _ & -> & _ & _). exact (pjsf_foR_n0 m lblk d d' p D' F _ _ _ _ _ _ Hh HF).
- destruct HB as (_ & _ & _ & -> & _ & _). exact (pjsf_foR_n0 m lblk d d' p D' F _ _ _ _ _ _ Hh HF).
- destruct HB as (_ & _ & _ & -> & _ & _). exact (pjsf_foR_n0 m lblk d d' p D' F _ _ _ _ _ _ Hh HF).
- destruct HB as (_ & _ & -> & _ & _). exact (pjsf_foR_n0 m lblk d d' p D' F _ _ _ _ _ _ Hh HF).
- destruct HB as (Es & Ek & En & Hc & Hcap & Di0 & ED & Hi).
  destruct d' as [|d'']; [cbn [PjTree.depth] in Hd; lia|].
  destruct (PjFoMember.pfm_foR_inv segs m lblk d p D' F HF) as (ty' & num' & str' & kids' & keys' & n' & cap' & ks &
    Ds & Dk & Dy & Di & Fi & Hh' & Hs & Hk & Hy & Hp & EF & Hdd).
  destruct (PjFoMember.pfm_hdr_det segs m p _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hh Hh') as (-> & -> & -> & ->).
  destruct Hdd as [(-> & En0 & _ & _)|(d0 & -> & HO)].
  + rewrite En0 in Hh. exact (pjsf_foR_n0 m lblk O (S d'') p D' F _ _ _ _ _ _ Hh HF).
  + assert (HND : NoDup D' /\ pj_apartR D' p)
      by (cbn [pj_foR pj_oshapeR] in HF; destruct HF as (Hnd & Hap & _); split; assumption).
    destruct HND as [Hnd Hap].
    cbn [pj_foR pj_oshapeR]. split; [exact Hnd|]. split; [exact Hap|].
    exists ty', num', str, kids, keys, n, cap', ks, Ds, Dk, Dy, Di, Fi.
    split; [exact Hh'|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|]. split; [exact Hp|].
    split; [|exact EF].
    rewrite En, Nat2Z.id in HO |- *.
    apply (pjsf_items_lower m lblk d0 d'' items kids keys ks Di0 Di Fi IH Hi HO).
    intros u Hu. pose proof (PjTree.depth_item items u Hu). lia.
- destruct HB as (Es & En & Hc & Hcap & Dm & ED & Hm).
  destruct d' as [|d'']; [cbn [PjTree.depth] in Hd; lia|].
  destruct (PjFoMember.pfm_foR_inv segs m lblk d p D' F HF) as (ty' & num' & str' & kids' & keys' & n' & cap' & ks &
    Ds & Dk & Dy & Di & Fi & Hh' & Hs & Hk & Hy & Hp & EF & Hdd).
  destruct (PjFoMember.pfm_hdr_det segs m p _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hh Hh') as (-> & -> & -> & ->).
  destruct Hdd as [(-> & En0 & _ & _)|(d0 & -> & HO)].
  + rewrite En0 in Hh. exact (pjsf_foR_n0 m lblk O (S d'') p D' F _ _ _ _ _ _ Hh HF).
  + assert (HND : NoDup D' /\ pj_apartR D' p)
      by (cbn [pj_foR pj_oshapeR] in HF; destruct HF as (Hnd & Hap & _); split; assumption).
    destruct HND as [Hnd Hap].
    cbn [pj_foR pj_oshapeR]. split; [exact Hnd|]. split; [exact Hap|].
    exists ty', num', str, kids, keys, n, cap', ks, Ds, Dk, Dy, Di, Fi.
    split; [exact Hh'|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|]. split; [exact Hp|].
    split; [|exact EF].
    rewrite En, Nat2Z.id in HO |- *.
    apply (pjsf_mems_lower m lblk d0 d'' ms kids keys ks Dm Di Fi IH Hm HO).
    intros nm u Hu. pose proof (PjTree.depth_member ms nm u Hu). lia.
Qed.

Lemma pjsf_oitems_lower : forall m lblk d d' (ms : list (list Z * PjTree.jv)) a ka Dm Di Fi,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Dm ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) true a ka (length ms) Di Fi ->
  (forall nm u, In (nm, u) ms -> (PjTree.depth u <= d')%nat) ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d') true a ka (length ms) Di Fi.
Proof.
intros m lblk d d' ms a ka Dm Di Fi Hm HO Hd.
apply (pjsf_mems_lower m lblk d d' ms a ka true Dm Di Fi); [|exact Hm | exact HO | exact Hd].
apply Forall_forall. intros mm _ m' lblk' p D d0 D' F d1 HN HF Hd1.
exact (pjsf_foR_lower (snd mm) m' lblk' p D d0 D' F d1 HN HF Hd1).
Qed.

(* ---- the depth of an object ---- *)
Lemma pjsf_depth_app : forall (ms : list (list Z * PjTree.jv)) x,
  (PjTree.depth (PjTree.JObj ms) <= PjTree.depth (PjTree.JObj (ms ++ [x])))%nat.
Proof. intros ms x. cbn [PjTree.depth]. rewrite map_app, list_max_app. lia. Qed.

Lemma pjsf_depth_obj : forall (ms : list (list Z * PjTree.jv)) nn,
  (PjTree.depth (PjTree.JObj ms) <= S nn)%nat <-> (forall nm u, In (nm, u) ms -> (PjTree.depth u <= nn)%nat).
Proof.
intros ms nn. cbn [PjTree.depth]. rewrite <- Nat.succ_le_mono, list_max_le, Forall_forall. split.
- intros H nm u Hin. apply (H (PjTree.depth u)). apply in_map_iff. exists (nm, u). split; [reflexivity | exact Hin].
- intros H k Hk. apply in_map_iff in Hk as ([nm u] & <- & Hin). exact (H nm u Hin).
Qed.

End fo.
