(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep BootLayout.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxStep AxSys AxJoinSound AxAcct AxGrant AsanWLazy AsanWBase AsanSBase AsanWMemset AsanWMat AsanWMsM AxSum AxScan AxForget.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumMem.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint fill_rng (d : nat) (t : itrie cell) (lo hi : int) (c : cell) : itrie cell :=
  if (hi <=? lo)%uint63 then t else
  match d with
  | O => if (lo =? 0)%uint63 then ILeaf c else t
  | S d' =>
      let l := match t with INode l _ => l | _ => IEmpty end in
      let r := match t with INode _ r => r | _ => IEmpty end in
      INode (fill_rng d' l ((lo + 1) >> 1)%uint63 ((hi + 1) >> 1)%uint63 c) (fill_rng d' r (lo >> 1)%uint63 (hi >> 1)%uint63 c)
  end.

Lemma rng_odd (lo hi j : Z) : 0 <= lo -> 0 <= hi -> 0 <= j -> j mod 2 = 1 ->
  ((lo / 2 <=? j / 2) && (j / 2 <? hi / 2)) = ((lo <=? j) && (j <? hi)).
Proof.
  intros Hl Hh Hj Ho. assert (N2 : 2 <> 0) by discriminate. assert (P2 : 0 < 2) by reflexivity.
  pose proof (Z.div_mod j 2 N2). pose proof (Z.div_mod lo 2 N2). pose proof (Z.div_mod hi 2 N2).
  pose proof (Z.mod_pos_bound lo 2 P2). pose proof (Z.mod_pos_bound hi 2 P2).
  destruct (Z.leb_spec lo j), (Z.ltb_spec j hi), (Z.leb_spec (lo / 2) (j / 2)), (Z.ltb_spec (j / 2) (hi / 2)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma rng_even (lo hi j : Z) : 0 <= lo -> 0 <= hi -> 0 <= j -> j mod 2 = 0 ->
  (((lo + 1) / 2 <=? j / 2) && (j / 2 <? (hi + 1) / 2)) = ((lo <=? j) && (j <? hi)).
Proof.
  intros Hl Hh Hj Ho. assert (N2 : 2 <> 0) by discriminate. assert (P2 : 0 < 2) by reflexivity.
  pose proof (Z.div_mod j 2 N2). pose proof (Z.div_mod (lo + 1) 2 N2). pose proof (Z.div_mod (hi + 1) 2 N2).
  pose proof (Z.mod_pos_bound (lo + 1) 2 P2). pose proof (Z.mod_pos_bound (hi + 1) 2 P2).
  destruct (Z.leb_spec lo j), (Z.ltb_spec j hi), (Z.leb_spec ((lo + 1) / 2) (j / 2)), (Z.ltb_spec (j / 2) ((hi + 1) / 2)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma iget_fill_rng (c : cell) : forall (d : nat) (t : itrie cell) (lo hi j : int),
  to_Z hi < 2 ^ 62 -> to_Z j < 2 ^ Z.of_nat d ->
  iget d (fill_rng d t lo hi c) j = if (to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi) then Some c else iget d t j.
Proof.
  induction d as [|d IH]; intros t lo hi j Hhi Hj.
  - (* [comment removed for export] *)
    pose proof (to_Z_bounded j) as Hjb. pose proof (to_Z_bounded lo) as Hlb. pose proof (to_Z_bounded hi) as Hhb.
    change (2 ^ Z.of_nat 0) with 1 in Hj. assert (Ej : to_Z j = 0) by lia. rewrite Ej.
    cbn [fill_rng]. destruct (hi <=? lo)%uint63 eqn:E1.
    + apply Uint63.leb_spec in E1.
      replace ((to_Z lo <=? 0) && (0 <? to_Z hi)) with false; [reflexivity|].
      symmetry. apply andb_false_iff. destruct (Z.leb_spec (to_Z lo) 0); [right; apply Z.ltb_ge; lia | left; reflexivity].
    + assert (Hlt : to_Z lo < to_Z hi).
      { destruct (Z.lt_ge_cases (to_Z lo) (to_Z hi)) as [X|X]; [exact X|]. apply Uint63.leb_spec in X. rewrite X in E1. discriminate. }
      destruct (lo =? 0)%uint63 eqn:E0.
      * apply Uint63.eqb_spec in E0. subst lo. change (to_Z 0%uint63) with 0 in *.
        replace (0 <? to_Z hi) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      * assert (to_Z lo <> 0) by (intros X; assert (lo = 0%uint63) by (apply to_Z_inj; exact X); subst lo; rewrite Uint63.eqb_refl in E0; discriminate).
        replace (to_Z lo <=? 0) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - pose proof (to_Z_bounded j) as Hjb. pose proof (to_Z_bounded lo) as Hlb. pose proof (to_Z_bounded hi) as Hhb. change wB with (2 ^ 63) in *.
    cbn [fill_rng]. destruct (hi <=? lo)%uint63 eqn:E1.
    + apply Uint63.leb_spec in E1.
      replace ((to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi)) with false; [reflexivity|].
      symmetry. apply andb_false_iff. destruct (Z.leb_spec (to_Z lo) (to_Z j)); [right; apply Z.ltb_ge; lia | left; reflexivity].
    + assert (Hlt : to_Z lo < to_Z hi).
      { destruct (Z.lt_ge_cases (to_Z lo) (to_Z hi)) as [X|X]; [exact X|]. apply Uint63.leb_spec in X. rewrite X in E1. discriminate. }
      assert (Hl1 : to_Z ((lo + 1) >> 1)%uint63 = (to_Z lo + 1) / 2).
      { rewrite lsr_spec, add_spec. change (to_Z 1%uint63) with 1. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). reflexivity. }
      assert (Hh1 : to_Z ((hi + 1) >> 1)%uint63 = (to_Z hi + 1) / 2).
      { rewrite lsr_spec, add_spec. change (to_Z 1%uint63) with 1. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). reflexivity. }
      assert (Hl0 : to_Z (lo >> 1)%uint63 = to_Z lo / 2) by (rewrite lsr_spec; reflexivity).
      assert (Hh0 : to_Z (hi >> 1)%uint63 = to_Z hi / 2) by (rewrite lsr_spec; reflexivity).
      assert (Hj1 : to_Z (j >> 1)%uint63 = to_Z j / 2) by (rewrite lsr_spec; reflexivity).
      assert (Hj2 : to_Z (j >> 1)%uint63 < 2 ^ Z.of_nat d).
      { rewrite Hj1. apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hj by lia. lia. }
      pose proof (Z.mod_pos_bound (to_Z j) 2 ltac:(lia)) as Mj.
      cbn [iget]. destruct (iodd j) eqn:Eo; rewrite iodd_spec in Eo.
      * apply Z.eqb_eq in Eo.
        rewrite IH by (try exact Hj2; rewrite Hh0; apply Z.div_lt_upper_bound; lia). rewrite Hl0, Hh0, Hj1.
        rewrite (rng_odd (to_Z lo) (to_Z hi) (to_Z j)) by lia.
        destruct ((to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi)); [reflexivity|]. destruct t as [|v|l r]; cbn [iget]; try (rewrite iget_empty; reflexivity).
        replace (iodd j) with true by (symmetry; rewrite iodd_spec; apply Z.eqb_eq; exact Eo). reflexivity.
      * apply Z.eqb_neq in Eo.
        rewrite IH by (try exact Hj2; rewrite Hh1; apply Z.div_lt_upper_bound; lia). rewrite Hl1, Hh1, Hj1.
        rewrite (rng_even (to_Z lo) (to_Z hi) (to_Z j)) by lia.
        destruct ((to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi)); [reflexivity|]. destruct t as [|v|l r]; cbn [iget]; try (rewrite iget_empty; reflexivity).
        replace (iodd j) with false by (symmetry; rewrite iodd_spec; apply Z.eqb_neq; exact Eo). reflexivity.
Qed.

(* [comment removed for export] *)
Definition mk_node (l r : itrie cell) : itrie cell := match l, r with IEmpty, IEmpty => IEmpty | _, _ => INode l r end.

Fixpoint rm_rng (d : nat) (t : itrie cell) (lo hi : int) : itrie cell :=
  if (hi <=? lo)%uint63 then t else
  match t with
  | IEmpty => IEmpty
  | ILeaf v => match d with O => if (lo =? 0)%uint63 then IEmpty else t | S _ => t end
  | INode l r => match d with
                 | O => t
                 | S d' => mk_node (rm_rng d' l ((lo + 1) >> 1)%uint63 ((hi + 1) >> 1)%uint63) (rm_rng d' r (lo >> 1)%uint63 (hi >> 1)%uint63)
                 end
  end.

Lemma iget_mk_node (d : nat) (l r : itrie cell) (j : int) : iget (S d) (mk_node l r) j = iget (S d) (INode l r) j.
Proof.
  unfold mk_node. destruct l; try reflexivity. destruct r; try reflexivity.
  cbn [iget]. destruct (iodd j); rewrite iget_empty; reflexivity.
Qed.

Lemma iget_rm_rng : forall (d : nat) (t : itrie cell) (lo hi j : int),
  to_Z hi < 2 ^ 62 -> to_Z j < 2 ^ Z.of_nat d ->
  iget d (rm_rng d t lo hi) j = if (to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi) then None else iget d t j.
Proof.
  induction d as [|d IH]; intros t lo hi j Hhi Hj.
  - pose proof (to_Z_bounded j) as Hjb. pose proof (to_Z_bounded lo) as Hlb. pose proof (to_Z_bounded hi) as Hhb.
    change (2 ^ Z.of_nat 0) with 1 in Hj. assert (Ej : to_Z j = 0) by lia. rewrite Ej.
    cbn [rm_rng]. destruct (hi <=? lo)%uint63 eqn:E1.
    + apply Uint63.leb_spec in E1.
      replace ((to_Z lo <=? 0) && (0 <? to_Z hi)) with false; [reflexivity|].
      symmetry. apply andb_false_iff. destruct (Z.leb_spec (to_Z lo) 0); [right; apply Z.ltb_ge; lia | left; reflexivity].
    + assert (Hlt : to_Z lo < to_Z hi).
      { destruct (Z.lt_ge_cases (to_Z lo) (to_Z hi)) as [X|X]; [exact X|]. apply Uint63.leb_spec in X. rewrite X in E1. discriminate. }
      destruct t as [|v|l r]; cbn [iget]; [destruct ((to_Z lo <=? 0) && (0 <? to_Z hi)); reflexivity | | destruct ((to_Z lo <=? 0) && (0 <? to_Z hi)); reflexivity].
      destruct (lo =? 0)%uint63 eqn:E0.
      * apply Uint63.eqb_spec in E0. subst lo. change (to_Z 0%uint63) with 0 in *.
        replace (0 <? to_Z hi) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      * assert (to_Z lo <> 0) by (intros X; assert (lo = 0%uint63) by (apply to_Z_inj; exact X); subst lo; rewrite Uint63.eqb_refl in E0; discriminate).
        replace (to_Z lo <=? 0) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - pose proof (to_Z_bounded j) as Hjb. pose proof (to_Z_bounded lo) as Hlb. pose proof (to_Z_bounded hi) as Hhb. change wB with (2 ^ 63) in *.
    cbn [rm_rng]. destruct (hi <=? lo)%uint63 eqn:E1.
    + apply Uint63.leb_spec in E1.
      replace ((to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi)) with false; [reflexivity|].
      symmetry. apply andb_false_iff. destruct (Z.leb_spec (to_Z lo) (to_Z j)); [right; apply Z.ltb_ge; lia | left; reflexivity].
    + assert (Hlt : to_Z lo < to_Z hi).
      { destruct (Z.lt_ge_cases (to_Z lo) (to_Z hi)) as [X|X]; [exact X|]. apply Uint63.leb_spec in X. rewrite X in E1. discriminate. }
      destruct t as [|v|l r].
      * rewrite iget_empty. destruct ((to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi)); reflexivity.
      * cbn [iget]. destruct ((to_Z lo <=? to_Z j) && (to_Z j <? to_Z hi)); reflexivity.
      * assert (Hl1 : to_Z ((lo + 1) >> 1)%uint63 = (to_Z lo + 1) / 2).
        { rewrite lsr_spec, add_spec. change (to_Z 1%uint63) with 1. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). reflexivity. }
        assert (Hh1 : to_Z ((hi + 1) >> 1)%uint63 = (to_Z hi + 1) / 2).
        { rewrite lsr_spec, add_spec. change (to_Z 1%uint63) with 1. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). reflexivity. }
        assert (Hl0 : to_Z (lo >> 1)%uint63 = to_Z lo / 2) by (rewrite lsr_spec; reflexivity).
        assert (Hh0 : to_Z (hi >> 1)%uint63 = to_Z hi / 2) by (rewrite lsr_spec; reflexivity).
        assert (Hj1 : to_Z (j >> 1)%uint63 = to_Z j / 2) by (rewrite lsr_spec; reflexivity).
        assert (Hj2 : to_Z (j >> 1)%uint63 < 2 ^ Z.of_nat d).
        { rewrite Hj1. apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hj by lia. lia. }
        pose proof (Z.mod_pos_bound (to_Z j) 2 ltac:(lia)) as Mj.
        rewrite iget_mk_node. cbn [iget]. destruct (iodd j) eqn:Eo; rewrite iodd_spec in Eo.
        -- apply Z.eqb_eq in Eo.
           rewrite IH by (try exact Hj2; rewrite Hh0; apply Z.div_lt_upper_bound; lia). rewrite Hl0, Hh0, Hj1.
           rewrite (rng_odd (to_Z lo) (to_Z hi) (to_Z j)) by lia. reflexivity.
        -- apply Z.eqb_neq in Eo.
           rewrite IH by (try exact Hj2; rewrite Hh1; apply Z.div_lt_upper_bound; lia). rewrite Hl1, Hh1, Hj1.
           rewrite (rng_even (to_Z lo) (to_Z hi) (to_Z j)) by lia. reflexivity.
Qed.

Definition fill_cells (R : region) (k0 : int) (cnt : nat) (c : int) : region :=
  with_cells R (fill_rng (rg_d R) (rg_cells R) k0 (k0 + of_Z (Z.of_nat cnt))%uint63 (CB (repeat (BL c) 8))).

Section WithSegs.
Variable segs : list Segment.

Lemma rbyte_fill (R : region) (k0 : int) (cnt : nat) (c : int) (x : int) :
  (rg_d R <= 44)%nat -> to_Z k0 + Z.of_nat cnt <= 2 ^ Z.of_nat (rg_d R) ->
  to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z x < to_Z (rg_n R) ->
  rbyte segs (fill_cells R k0 cnt c) x =
  if (to_Z k0 <=? to_Z x / 8) && (to_Z x / 8 <? to_Z k0 + Z.of_nat cnt) then BL c else rbyte segs R x.
Proof.
  intros Hd Hk Hn Hx. unfold rbyte, get_cell_opt, fill_cells, with_cells. cbn [rg_d rg_cells rg_kind].
  pose proof (key_small R x Hn Hx) as Hks.
  assert (Hp44 : 2 ^ Z.of_nat (rg_d R) <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
  pose proof (to_Z_bounded k0) as Hk0b. change wB with (2 ^ 63) in Hk0b.
  assert (Hcnt : to_Z (of_Z (Z.of_nat cnt)) = Z.of_nat cnt) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  assert (Hhi : to_Z (k0 + of_Z (Z.of_nat cnt))%uint63 = to_Z k0 + Z.of_nat cnt) by (rewrite add_spec, Hcnt; apply Z.mod_small; change wB with (2 ^ 63); lia).
  rewrite iget_fill_rng by (try exact Hks; rewrite Hhi; lia). rewrite Hhi. rewrite phi_lsr3 in *.
  destruct ((to_Z k0 <=? to_Z x / 8) && (to_Z x / 8 <? to_Z k0 + Z.of_nat cnt)); [|reflexivity].
  cbn [cbyte]. unfold i2n. repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* [comment removed for export] *)
Definition zero_kind (k : rkind) : bool := match k with KZero | KShadow => true | _ => false end.

Definition fill_region (R : region) (k0 : int) (cnt : nat) (c : int) : region :=
  if (c =? 0)%uint63 && zero_kind (rg_kind R)
  then with_cells R (rm_rng (rg_d R) (rg_cells R) k0 (k0 + of_Z (Z.of_nat cnt))%uint63)
  else fill_cells R k0 cnt c.

Lemma rbyte_fill_region (R : region) (k0 : int) (cnt : nat) (c : int) (x : int) :
  (rg_d R <= 44)%nat -> to_Z k0 + Z.of_nat cnt <= 2 ^ Z.of_nat (rg_d R) ->
  to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z x < to_Z (rg_n R) ->
  rbyte segs (fill_region R k0 cnt c) x =
  if (to_Z k0 <=? to_Z x / 8) && (to_Z x / 8 <? to_Z k0 + Z.of_nat cnt) then BL c else rbyte segs R x.
Proof.
  intros Hd Hk Hn Hx. unfold fill_region.
  destruct ((c =? 0)%uint63 && zero_kind (rg_kind R)) eqn:E; [|exact (rbyte_fill R k0 cnt c x Hd Hk Hn Hx)].
  apply andb_prop in E as [Ec Ez]. apply Uint63.eqb_spec in Ec. subst c.
  unfold rbyte, get_cell_opt, with_cells. cbn [rg_d rg_cells rg_kind].
  pose proof (key_small R x Hn Hx) as Hks.
  assert (Hp44 : 2 ^ Z.of_nat (rg_d R) <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
  pose proof (to_Z_bounded k0) as Hk0b. change wB with (2 ^ 63) in Hk0b.
  assert (Hcnt : to_Z (of_Z (Z.of_nat cnt)) = Z.of_nat cnt) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  assert (Hhi : to_Z (k0 + of_Z (Z.of_nat cnt))%uint63 = to_Z k0 + Z.of_nat cnt) by (rewrite add_spec, Hcnt; apply Z.mod_small; change wB with (2 ^ 63); lia).
  rewrite iget_rm_rng by (try exact Hks; rewrite Hhi; lia). rewrite Hhi. rewrite phi_lsr3 in *.
  destruct (iget (rg_d R) (rg_cells R) (x >> 3)%uint63) as [cc|];
    destruct ((to_Z k0 <=? to_Z x / 8) && (to_Z x / 8 <? to_Z k0 + Z.of_nat cnt)); try reflexivity;
    unfold default_byte; destruct (rg_kind R); try discriminate Ez; reflexivity.
Qed.

(* [comment removed for export] *)
Definition fill_kind (k : rkind) : bool := match k with KZero | KShadow | KUnk | KImg true _ => true | _ => false end.

Definition a_fill (A : list region) (v : xv) (n : Z) (c : int) : option (list region) :=
  match xaddr v with
  | Some (ts, o) =>
      if (8 <=? n) &&& (n <? 1073741824) &&& (n mod 8 =? 0) then
        match find_reg A ts o (of_Z n) 0 with
        | Some (i, R, x) =>
            if fill_kind (rg_kind R) &&& (to_Z x mod 8 =? 0)
            then Some (replace_nth A i (fill_region R (x >> 3)%uint63 (Z.to_nat (n / 8)) c)) else None
        | None => None
        end
      else None
  | None => None
  end.

Lemma a_fill_fields (A A' : list region) (v : xv) (n : Z) (c : int) : a_fill A v n c = Some A' -> Forall2 same_fields A A'.
Proof.
  unfold a_fill. destruct (xaddr v) as [[ts o]|]; [|discriminate].
  destruct ((8 <=? n) &&& (n <? 1073741824) &&& (n mod 8 =? 0)); [|discriminate].
  destruct (find_reg A ts o (of_Z n) 0) as [[[i R] x]|] eqn:Ef; [|discriminate].
  destruct (fill_kind (rg_kind R) &&& (to_Z x mod 8 =? 0)); [|discriminate]. intros H. injection H as <-.
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi _]]. rewrite Nat.sub_0_r in Hi.
  apply (Forall2_replace_nth same_fields A i R); [intros X; repeat split | exact Hi |].
  unfold fill_region. destruct ((c =? 0)%uint63 && zero_kind (rg_kind R)); repeat split.
Qed.

Theorem a_fill_sound (ρ : valuation) (A A' : list region) (m m' : word -> option byte) (v : xv) (a : bv 64) (n : Z) (c : int) :
  segs_low segs -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ v a -> a_fill A v n c = Some A' -> to_Z c < 256 ->
  store_ok segs m a (Z.to_nat n) = true /\
  (filled m' m (bv_unsigned a) (bv_unsigned a + n) (Z_to_bv 8 (to_Z c)) -> RMem segs ρ A' m' /\ hs_ok ρ A' m').
Proof.
  intros Hlow [Hok HR] Hhs Hv H Hc. pose proof H as Hfill0. unfold a_fill in H.
  destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct ((8 <=? n) &&& (n <? 1073741824) &&& (n mod 8 =? 0)) eqn:En; [|discriminate].
  apply land_true in En as [En En8]. apply land_true in En as [En1 En2].
  apply Z.leb_le in En1. apply Z.ltb_lt in En2. apply Z.eqb_eq in En8.
  destruct (find_reg A ts o (of_Z n) 0) as [[[i R] x]|] eqn:Ef; [|discriminate].
  destruct (fill_kind (rg_kind R) &&& (to_Z x mod 8 =? 0)) eqn:Ek; [|discriminate].
  apply land_true in Ek as [Ek Ex8]. apply Z.eqb_eq in Ex8. injection H as <-.
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf. pose proof (Forall_nth _ A i R HR Hi) as HRR.
  pose proof (roff_ne R ts o _ x Hr) as Hne0. rewrite (RRegion_ne segs ρ m R Hne0) in HRR.
  pose proof (xaddr_val ρ v a ts o Hv Ea) as Hav.
  assert (Hnz : to_Z (of_Z n) = n) by (apply phi_of_Z_n; lia).
  destruct (roff_addr ρ R ts o (of_Z n) x a ltac:(rewrite Hnz; lia) Hwf Hav Hr) as [Eaddr Hfit]. rewrite Hnz in Hfit.
  pose proof Hwf as [Hw1 [H47 [Hd [Hd44 Himg]]]].
  pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hsr. fold (rbase ρ R) in Hsr.
  assert (Hwr : rk_writable (rg_kind R) = true) by (unfold fill_kind in Ek; destruct (rg_kind R) as [| | |[|] ?|]; try discriminate; reflexivity).
  assert (Ea' : a = wz (rbase ρ R + to_Z x)) by (apply bv_eq; rewrite u_wz by (unfold two64 in *; lia); exact Eaddr).
  assert (Hsok : store_ok segs m a (Z.to_nat n) = true).
  { rewrite Ea'. apply (store_ok_range segs ρ m R x (Z.to_nat n) HRR Hwr); [lia | exact H47]. }
  split; [exact Hsok|].
  intros Hf.
  split.
  2:{ (* [comment removed for export] *)
    assert (Hpw : forall y, m' y = write_to_mem m a (repeat (Z_to_bv 8 (to_Z c)) (Z.to_nat n)) y).
    { apply filled_write; [unfold two64 in *; lia|]. rewrite Z2Nat.id by lia. exact Hf. }
    apply (hs_ok_pw ρ _ _ m' Hpw).
    apply (hs_ok_write segs ρ A _ m a _ Hlow Hhs (a_fill_fields A _ v n c Hfill0)).
    - exists R. split; [exact (nth_error_In A i Hi)|]. rewrite repeat_length, Z2Nat.id by lia. lia.
    - rewrite repeat_length, Z2Nat.id by lia. unfold two64 in *. lia.
    - rewrite repeat_length. exact Hsok. }
  assert (Hk3 : to_Z (x >> 3)%uint63 = to_Z x / 8) by apply phi_lsr3.
  assert (Hcnt : Z.of_nat (Z.to_nat (n / 8)) = n / 8) by (apply Z2Nat.id; apply Z.div_pos; lia).
  assert (Hxn : to_Z x / 8 + n / 8 <= 2 ^ Z.of_nat (rg_d R)).
  { assert (E1 : to_Z x = 8 * (to_Z x / 8)) by (rewrite (Z.div_mod (to_Z x) 8) at 1 by lia; lia).
    assert (E2 : n = 8 * (n / 8)) by (rewrite (Z.div_mod n 8) at 1 by lia; lia). lia. }
  (* [comment removed for export] *)
  assert (Hfr : forall y : word, ~ (bv_unsigned a <= bv_unsigned y < bv_unsigned a + n) -> m' y = m y) by (intros y Hy; exact (proj2 (Hf y) Hy)).
  assert (Hoth : forall j Rj, nth_error A j = Some Rj -> j <> i -> RRegion segs ρ m' Rj).
  { intros j Rj Hj Hne. pose proof (Forall_nth _ A j Rj HR Hj) as HRj.
    pose proof (regions_ok_disj ρ A i j R Rj Hok Hi Hj ltac:(lia)) as Hdis.
    pose proof (regions_ok_nth ρ A j Rj Hok Hj) as Wj. pose proof Wj as [Wj1 _].
    apply (RRegion_mframe segs ρ m _ Rj Wj); [|exact HRj].
    intros y Hy. apply Hfr. rewrite Eaddr.
    rewrite u_wz by (pose proof (smod_range ρ (rg_ts Rj) (rg_bo Rj)); unfold rbase in *; unfold two64 in *; lia).
    unfold rdisj in Hdis. lia. }
  assert (Ekind : rg_kind (fill_region R (x >> 3)%uint63 (Z.to_nat (n / 8)) c) = rg_kind R)
    by (unfold fill_region; destruct ((c =? 0)%uint63 && zero_kind (rg_kind R)); reflexivity).
  assert (Enn : rg_n (fill_region R (x >> 3)%uint63 (Z.to_nat (n / 8)) c) = rg_n R)
    by (unfold fill_region; destruct ((c =? 0)%uint63 && zero_kind (rg_kind R)); reflexivity).
  assert (Ebase : rbase ρ (fill_region R (x >> 3)%uint63 (Z.to_nat (n / 8)) c) = rbase ρ R)
    by (unfold fill_region; destruct ((c =? 0)%uint63 && zero_kind (rg_kind R)); reflexivity).
  assert (Edd : rg_d (fill_region R (x >> 3)%uint63 (Z.to_nat (n / 8)) c) = rg_d R)
    by (unfold fill_region; destruct ((c =? 0)%uint63 && zero_kind (rg_kind R)); reflexivity).
  assert (Ets : rg_ts (fill_region R (x >> 3)%uint63 (Z.to_nat (n / 8)) c) = rg_ts R)
    by (unfold fill_region; destruct ((c =? 0)%uint63 && zero_kind (rg_kind R)); reflexivity).
  split.
  - apply (regions_ok_replace ρ A i R); [exact Hok | exact Hi | exact Ebase | exact Enn |].
    intros W. unfold region_wf in *. rewrite Ebase, Enn, Edd, Ekind, Ets. exact W.
  - apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
    rewrite RRegion_ne by (unfold is_entry in *; rewrite Ekind; exact Hne0).
    intros y Hy. rewrite Enn in Hy. rewrite Ebase, Ekind.
    rewrite (rbyte_fill_region R (x >> 3)%uint63 (Z.to_nat (n / 8)) c y Hd44 ltac:(rewrite Hk3, Hcnt; exact Hxn) Hd Hy).
    rewrite Hk3, Hcnt.
    pose proof (to_Z_bounded y) as Hyb. change wB with (2^63) in Hyb.
    assert (E1 : to_Z x = 8 * (to_Z x / 8)) by (rewrite (Z.div_mod (to_Z x) 8) at 1 by lia; lia).
    assert (E2 : n = 8 * (n / 8)) by (rewrite (Z.div_mod n 8) at 1 by lia; lia).
    pose proof (Z.div_mod (to_Z y) 8 ltac:(lia)) as Ey. pose proof (Z.mod_pos_bound (to_Z y) 8 ltac:(lia)) as Hym.
    destruct (HRR y Hy) as [[b [Hb Hab]] Hwv].
    destruct ((to_Z x / 8 <=? to_Z y / 8) && (to_Z y / 8 <? to_Z x / 8 + n / 8)) eqn:Ein.
    + apply andb_prop in Ein as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
      assert (Hin : bv_unsigned a <= bv_unsigned (wz (rbase ρ R + to_Z y)) < bv_unsigned a + n)
        by (rewrite u_wz by (unfold two64 in *; lia); rewrite Eaddr; lia).
      pose proof (proj1 (Hf (wz (rbase ρ R + to_Z y))) Hin) as Hm'.
      split.
      * exists (Z_to_bv 8 (to_Z c)). split; [unfold rv; rewrite Hm'; reflexivity|].
        unfold xb_bv. cbn [xb_z]. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256.
        pose proof (to_Z_bounded c). lia.
      * intros _. unfold wview. rewrite Hm'. discriminate.
    + assert (Hout : ~ (bv_unsigned a <= bv_unsigned (wz (rbase ρ R + to_Z y)) < bv_unsigned a + n)).
      { rewrite u_wz by (unfold two64 in *; lia). rewrite Eaddr.
        apply andb_false_iff in Ein as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia. }
      pose proof (Hfr _ Hout) as E.
      split; [exists b; unfold rv in *; rewrite E; split; assumption | intros Hw'; unfold wview in *; rewrite E; exact (Hwv Hw')].
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sum_memset_big (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let e := wZ (a_pc A) in
  let s := a_facts A in
  let d := aget (a_regs A) 10%uint63 in
  match xlit (aget (a_regs A) 11%uint63), xlit (aget (a_regs A) 12%uint63), aget (a_regs A) 1%uint63, xaddr d with
  | Some c, Some n, XL r, Some (td, od) =>
      if (0 <=? c) &&& (c <? 256) &&& (0 <=? n) &&& (n <? 1073741824) &&& ms_code_ok segs e &&& (wZ r mod 4 =? 0) &&& (wZ r <? 2 ^ 26)
         &&& rbetween 2 s (wS od, td) 0 (2 ^ 47 - n)
         &&& (a_budget A + 4096 * ms_pages n <=? LIM) then
        match a_fill (a_mem A) d n (of_Z c) with
        | Some mem' => Some [AS (wofZ (wZ r)) (clob MS_CLOB' (a_regs A)) (match a_resv A with RNone => RNone | _ => RUnk end)
                                mem' s (a_model A) (a_budget A + 4096 * ms_pages n) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _ => None
  end.

Section MemsetBigSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_memset_big_sound (A : AST) (l : list AST) : sum_memset_big segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho.
  unfold sum_memset_big in Hs.
  destruct (xlit (aget (a_regs A) 11%uint63)) as [c|] eqn:E11; [|discriminate].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [n|] eqn:E12; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (xaddr (aget (a_regs A) 10%uint63)) as [[td od]|] eqn:Ed; [|discriminate].
  match type of Hs with context [if ?c then _ else _] => destruct c eqn:Ec; [|discriminate] end.
  destruct (a_fill (a_mem A) (aget (a_regs A) 10%uint63) n (of_Z c)) as [mem'|] eqn:Emc; [|discriminate].
  injection Hs as <-.
  apply andb_prop in Ec as [Ec Hbud]. apply andb_prop in Ec as [Ec Hrd].
  apply andb_prop in Ec as [Ec Hr26]. apply andb_prop in Ec as [Ec Hr4]. apply andb_prop in Ec as [Ec Hcode].
  apply andb_prop in Ec as [Ec Hn1]. apply andb_prop in Ec as [Ec Hn0]. apply andb_prop in Ec as [Hc0 Hc1].
  apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1. apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. apply Z.ltb_lt in Hr26. apply Z.eqb_eq in Hr4.
  apply Z.leb_le in Hbud.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (e := wZ (a_pc A)) in *. set (dst := rg ms 10%bv).
  assert (Hvd : xv_val ρ (aget (a_regs A) 10%uint63) dst) by exact (Hregs 10%bv).
  pose proof (reg_lit ρ _ ms 11%bv 11%uint63 c Hregs eq_refl E11) as Hcv.
  pose proof (reg_lit ρ _ ms 12%bv 12%uint63 n Hregs eq_refl E12) as Hcnt.
  pose proof (rbetween_sound ρ _ 2 _ 0 (2 ^ 47 - n) Hsat Hrd) as Hrdv.
  assert (Hdv : bv_unsigned dst = leval ρ (wS od, td)) by (apply (addr_form_val' ρ _ dst td od (2 ^ 47 - n) Hvd Ed); [lia | unfold FastWord.two64; lia]).
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  pose proof (wZ_range r) as Hrr.
  assert (Edst : dst = Z_to_bv 64 (bv_unsigned dst)) by (apply word_lit_w; reflexivity).
  assert (Hcz : to_Z (of_Z c) = c) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  destruct (a_fill_sound segs ρ (a_mem A) mem' (ms_mem ms) (ms_mem ms) _ dst n (of_Z c) Hlow Hmem Hhs Hvd Emc ltac:(lia)) as [Hok _].
  apply (internal_memset_sum_mat segs cfg e (ms_code_sound segs e Hcode) ms model (KT ρ o') (bv_unsigned dst) n (rg ms 11%bv) Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - exact Edst.
  - reflexivity.
  - apply word_lit_w. exact Hcnt.
  - rewrite Hcv. exact Hc1.
  - lia.
  - lia.
  - lia.
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - rewrite <- Edst. exact Hok.
  - destruct Hb as [Hb1 Hb2]. rewrite Hb2. unfold page_size. lia.
  - intros ms' model' HMS Hfill Hpc' Hmat.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model') _ o' Ho).
    destruct HMS as [P1 P2 P3 P4 P5 P6].
    destruct Hmat as [[pages Em'] Hused]. subst model'.
    destruct (model_backing_fields model pages) as [MH ML].
    assert (Er : wZ (wofZ (wZ r)) = wZ r) by (rewrite wZ_wofZ; apply Z.mod_small; exact Hrr).
    rewrite Hcv in Hfill.
    destruct (a_fill_sound segs ρ (a_mem A) mem' (ms_mem ms) (ms_mem ms') _ dst n (of_Z c) Hlow Hmem Hhs Hvd Emc ltac:(lia)) as [_ X].
    rewrite Hcz in X. destruct (X Hfill) as [Hmem' Hhs'].
    pose proof (a_fill_fields (a_mem A) mem' _ n (of_Z c) Emc) as Hsf.
    constructor; cbn [cfg_ms cfg_model a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. rewrite Er. apply word_lit_w. exact Hra.
    + rewrite Er. split; lia.
    + exact P1.
    + apply (RRegs_clob ρ (a_regs A) ms ms' MS_CLOB' Hregs); [|exact MS_CLOB'_nz].
      intros r0 Hr0. destruct (MS_CLOB'_out r0 Hr0) as (N1 & N2 & N3). exact (P6 r0 N1 N2 N3).
    + destruct (a_resv A); cbn [RResv] in *; try exact I. destruct P5 as [Y|Y]; rewrite Y; [exact Hres | reflexivity].
    + rewrite P2. exact Hrom.
    + exact Hmem'.
    + exact (MR_mat segs fs0 ρ (a_model A) model pages Hmod).
    + rewrite MH. exact Hh.
    + destruct Hb as [Hb1 Hb2]. split; [unfold page_size in Hused; lia | rewrite ML; exact Hb2].
    + exact Hsat.
    + exact Hhs'.
    + apply mem_cov_backing.
      apply (mem_cov_range segs model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hcov ltac:(lia) ltac:(unfold AxAcct.two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hfill x)). lia.
    + apply comp_inv_backing. exact (comp_inv_geom segs ρ (a_mem A) mem' model Hsf Hcomp).
    + apply na_ok_backing. apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
      apply (na_ok_range segs ρ (a_mem A) model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hnaok ltac:(lia) ltac:(unfold AxAcct.two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hfill x)). lia.
Qed.

End MemsetBigSound.
