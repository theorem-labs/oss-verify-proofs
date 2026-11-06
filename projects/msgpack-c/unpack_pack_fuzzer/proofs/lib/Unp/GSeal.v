(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Ops GLib Seal SealX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UO UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GSeal.

Definition SBw : w64 := wlit 0x7fff8000%uint63.

Fixpoint link_of (fs : list fact) (sh : int) : option int :=
  match fs with
  | FEq (VP s o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k o') (VL c3)) (VL sb)) :: fs' =>
      if PrimInt63.eqb s sh && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some k else link_of fs' sh
  | _ :: fs' => link_of fs' sh
  | [] => None
  end.

Definition block_region_ok (st : sstate) (k : int) : bool :=
  negb (PrimInt63.eqb k 0%uint63) && PrimInt63.leb 3%uint63 (find_align (s_facts st) k)
  && match IMap.find k (s_regs st) with
     | Some r => PrimInt63.eqb (rg_lo r) 0%uint63
                 && match decide_ltu (s_facts st) (VL wzero) (rg_hi r) with Some true => true | _ => false end
     | None => false
     end.

Definition twin_explained (st : sstate) (kC : int) (vecs : list sv) (w : sv * sv * sv) : bool :=
  match kind_of w with
  | Some kd =>
      negb (kd =? 9) ||
      match w with
      | (VP sh o, _, _) =>
          weqb o wzero
          && match link_of (s_facts st) sh with
             | Some k => negb (PrimInt63.eqb k kC) && (block_region_ok st k || existsb (sv_eqb (VP k wzero)) vecs)
             | None => false
             end
      | _ => false
      end
  | None => false
  end.
Definition twins_explained (st : sstate) (kC : int) (vecs : list sv) (ws : list (sv * sv * sv)) : bool :=
  forallb (twin_explained st kC vecs) ws.

Lemma twins_explained_nil9 : forall st kC vecs ws,
  (forall w, In w ws -> exists kd, kind_of w = Some kd /\ kd <> 9) -> twins_explained st kC vecs ws = true.
Proof.
  intros st kC vecs ws H. apply forallb_forall. intros w Hw. destruct (H w Hw) as (kd & K & N). unfold twin_explained. rewrite K.
  apply orb_true_iff. left. apply negb_true_iff. apply Z.eqb_neq. exact N.
Qed.

Section Sound.
Variable E : env.

Lemma link_of_sound : forall fs sh k, facts_hold E fs -> link_of fs sh = Some k ->
  bv_unsigned (ev E sh) = Seal.shadZ (bv_unsigned (ev E k)).
Proof.
  intros fs sh k HF. induction fs as [|f fs IH]; intros H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst. cbn [link_of] in H.
  destruct f as [| | | |x y| | |]; try (exact (IH HF' H)).
  destruct x as [|sh0 z| | | | | | | | |]; try (exact (IH HF' H)).
  destruct y as [| |op y1 y2| | | | | | | |]; try (exact (IH HF' H)). destruct op; try (exact (IH HF' H)).
  destruct y1 as [| |op1 u1 u2| | | | | | | |]; try (exact (IH HF' H)). destruct op1; try (exact (IH HF' H)).
  destruct u1 as [|k' z'| | | | | | | | |]; try (exact (IH HF' H)). destruct u2 as [c| | | | | | | | | |]; try (exact (IH HF' H)).
  destruct y2 as [s'| | | | | | | | | |]; try (exact (IH HF' H)).
  destruct (PrimInt63.eqb sh0 sh && weqb z wzero && weqb z' wzero && weqb c (wlit 3%uint63) && weqb s' SBw) eqn:C; [| exact (IH HF' H)].
  injection H as ->. apply andb_prop in C as [C S']. apply andb_prop in C as [C C3]. apply andb_prop in C as [C Z']. apply andb_prop in C as [K' Z0].
  apply (proj1 (weqb_ok _ _)) in Z0. apply (proj1 (weqb_ok _ _)) in Z'. apply (proj1 (weqb_ok _ _)) in S'. apply (proj1 (weqb_ok _ _)) in C3.
  apply Uint63.eqb_correct in K'. subst z z' s' c sh0.
  cbn [fact_holds] in Hf.
  assert (DL : bv_unsigned (den E (VP sh wzero)) = bv_unsigned (ev E sh)) by (apply den_VP0; apply weqb_refl).
  rewrite <- DL, Hf.
  change (den E (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)))
    with (alu64 ALU_ADD (alu64 ALU_SRL (den E (VP k wzero)) (wbv (wlit 3%uint63))) (wbv SBw)).
  unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned.
  rewrite (den_VP0 E k wzero (weqb_refl _)).
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (bv_unsigned (wbv SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
  unfold Seal.shadZ, Seal.SBz, bv_wrap. rewrite bv_modulus_64.
  pose proof (bv_unsigned_in_range _ (ev E k)) as RK. rewrite bv_modulus_64 in RK. unfold two64 in *.
  apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
  assert (bv_unsigned (ev E k) / 8 < 2305843009213693952) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma block_region_ok_sound : forall st k, facts_hold E (s_facts st) -> block_region_ok st k = true ->
  PrimInt63.eqb k 0%uint63 = false /\ bv_unsigned (ev E k) mod 8 = 0 /\
  exists r, IMap.find k (s_regs st) = Some r /\ loZ r = 0 /\ 0 < hiZ E r.
Proof.
  intros st k HF H. unfold block_region_ok in H. apply andb_prop in H as [H RG]. apply andb_prop in H as [K0 AL].
  apply negb_true_iff in K0. split; [exact K0|]. split.
  - pose proof (find_align_sound_gen E (s_facts st) HF k) as A. apply Uint63.leb_spec in AL. change (to_Z 3%uint63) with 3 in AL.
    pose proof (int_range (find_align (s_facts st) k)) as RA.
    replace (2 ^ to_Z (find_align (s_facts st) k)) with (8 * 2 ^ (to_Z (find_align (s_facts st) k) - 3)) in A
      by (replace (to_Z (find_align (s_facts st) k)) with (3 + (to_Z (find_align (s_facts st) k) - 3)) at 2 by lia; rewrite Z.pow_add_r by lia; reflexivity).
    assert (PP : 0 < 2 ^ (to_Z (find_align (s_facts st) k) - 3)) by (apply Z.pow_pos_nonneg; lia).
    apply Z.mod_divide in A; [|lia]. apply Z.mod_divide; [lia|]. destruct A as [q Hq]. exists (q * 2 ^ (to_Z (find_align (s_facts st) k) - 3)). lia.
  - destruct (IMap.find k (s_regs st)) as [r|]; [|discriminate]. exists r. split; [reflexivity|].
    apply andb_prop in RG as [LO HI]. apply Uint63.eqb_correct in LO. split; [unfold loZ; rewrite LO; reflexivity|].
    destruct (decide_ltu (s_facts st) (VL wzero) (rg_hi r)) as [[|]|] eqn:DH; try discriminate.
    pose proof (decide_ltu_sound E (s_facts st) HF _ _ _ DH) as HPOS. apply (proj1 (ltu_iff _ _ true)) in HPOS.
    cbn [den] in HPOS. rewrite wbv_unsigned, wzero_ok in HPOS. exact HPOS.
Qed.

Lemma twin_explained_sound : forall st kC rc vecs w,
  facts_hold E (s_facts st) -> regions_disjoint E (s_regs st) ->
  IMap.find kC (s_regs st) = Some rc -> PrimInt63.eqb kC 0%uint63 = false -> rg_w rc = true -> loZ rc = 0 -> 0 < hiZ E rc ->
  bv_unsigned (ev E kC) mod 8 = 0 ->
  (forall v, In v vecs -> bv_unsigned (den E v) mod 8 = 0 /\ bv_unsigned (den E v) <> bv_unsigned (ev E kC)) ->
  twin_explained st kC vecs w = true -> w_kind (wden E w) = Seal.K_TWIN -> w_lo (wden E w) <> Seal.shadZ (bv_unsigned (ev E kC)).
Proof.
  intros st kC rc vecs w HF DJ FC KC0 WC LC HC AC VECS H K.
  unfold twin_explained in H. destruct (kind_of w) as [kd|] eqn:KO; [|discriminate].
  pose proof (kind_of_sound E w kd KO) as KS. rewrite K in KS. unfold Seal.K_TWIN in KS. subst kd.
  change (negb (9 =? 9)) with false in H. cbn [orb] in H.
  destruct w as [[lo len] kdv]. destruct lo as [|sh o| | | | | | | | |]; try discriminate.
  apply andb_prop in H as [O0 H]. destruct (link_of (s_facts st) sh) as [k|] eqn:LK; [|discriminate].
  apply andb_prop in H as [NE EV]. apply negb_true_iff in NE. apply Uint63.eqb_false_correct in NE.
  cbn [wden w_lo]. rewrite (den_VP0 E sh o O0), (link_of_sound _ sh k HF LK).
  assert (X : bv_unsigned (ev E k) mod 8 = 0 /\ bv_unsigned (ev E k) <> bv_unsigned (ev E kC)).
  { apply orb_prop in EV as [RG|VC].
    - destruct (block_region_ok_sound st k HF RG) as (K0 & AL & r & FR & LO & HI). split; [exact AL|].
      intros EQ. apply (DJ k r kC rc FR FC NE K0 KC0 (or_intror WC) (bv_unsigned (ev E k))). rewrite LO, LC, <- EQ. lia.
    - apply existsb_exists in VC as (v & Hv & EQv). apply sv_eqb_eq in EQv. subst v.
      destruct (VECS _ Hv) as [A N]. rewrite (den_VP0 E k wzero (weqb_refl _)) in A, N. split; [exact A| exact N]. }
  destruct X as [A N]. apply SealX.shadZ_neq8; assumption.
Qed.

Lemma twins_explained_sound : forall st kC rc vecs ws,
  facts_hold E (s_facts st) -> regions_disjoint E (s_regs st) ->
  IMap.find kC (s_regs st) = Some rc -> PrimInt63.eqb kC 0%uint63 = false -> rg_w rc = true -> loZ rc = 0 -> 0 < hiZ E rc ->
  bv_unsigned (ev E kC) mod 8 = 0 ->
  (forall v, In v vecs -> bv_unsigned (den E v) mod 8 = 0 /\ bv_unsigned (den E v) <> bv_unsigned (ev E kC)) ->
  twins_explained st kC vecs ws = true ->
  forall w, In w (map (wden E) ws) -> w_kind w = Seal.K_TWIN -> w_lo w <> Seal.shadZ (bv_unsigned (ev E kC)).
Proof.
  intros st kC rc vecs ws HF DJ FC KC0 WC LC HC AC VECS H w Hw K. apply in_map_iff in Hw as (x & <- & Hx).
  exact (twin_explained_sound st kC rc vecs x HF DJ FC KC0 WC LC HC AC VECS (proj1 (forallb_forall _ _) H x Hx) K).
Qed.

End Sound.
End GSeal.
