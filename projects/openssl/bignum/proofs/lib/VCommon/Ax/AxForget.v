(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxMemC AxZZ AxState AxScan AxTrieShift.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Lemma phi_of_nat_lt (n : nat) : (Z.of_nat n < 2 ^ 62) -> to_Z (of_Z (Z.of_nat n)) = Z.of_nat n.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2^63). lia. Qed.

Section Gen.
Variable segs : list Segment.

Lemma a_store_gen_sound (ρ : valuation) (A A' : list region) (m m' : word -> option byte) (v : xv) (a : bv 64) (nb : list xb) :
  RMem segs ρ A m -> xv_val ρ v a -> (1 <= length nb)%nat -> Z.of_nat (length nb) < 2 ^ 40 -> a_store segs A v nb = Some A' ->
  (forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length nb)) -> m' x = m x) ->
  (forall i, (i < length nb)%nat -> (exists b, m' (wz (bv_unsigned a + Z.of_nat i)) = Some b /\ xb_bv ρ (nth i nb BT) b)
     \/ (m' (wz (bv_unsigned a + Z.of_nat i)) = m (wz (bv_unsigned a + Z.of_nat i)) /\ nth i nb BT = BT)) ->
  store_ok segs m a (length nb) = true /\ RMem segs ρ A' m'.
Proof.
  intros [Hok HR] Hv Hn1 Hn H Hfr Hby. unfold a_store in H.
  destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct (find_reg A ts o (of_Z (Z.of_nat (length nb))) 0) as [[[i R0] x]|] eqn:Ef; [|discriminate].
  destruct (rk_writable (rg_kind R0)) eqn:Ew; [|discriminate]. injection H as <-.
  destruct (find_reg_spec A ts o _ 0 i R0 x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R0 Hok Hi) as Hwf. pose proof (Forall_nth _ A i R0 HR Hi) as HRR.
  pose proof (roff_ne R0 ts o _ x Hr) as Hne0. rewrite (RRegion_ne segs ρ m R0 Hne0) in HRR.
  assert (Hav : bv_unsigned a = smod ρ ts o).
  { destruct v; cbn [xaddr] in Ea; try discriminate; injection Ea as <- <-; cbn [xv_val] in Hv.
    - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
    - exact Hv. }
  destruct (roff_addr ρ R0 ts o (of_Z (Z.of_nat (length nb))) x a ltac:(rewrite phi_of_nat_lt by lia; lia) Hwf Hav Hr) as [Eaddr Hfit].
  rewrite phi_of_nat_lt in Hfit by lia.
  pose proof Hwf as [Hw1 [H47 [Hd [Hd44 _]]]].
  pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  pose proof (smod_range ρ (rg_ts R0) (rg_bo R0)) as Hsr. fold (rbase ρ R0) in Hsr.
  destruct (rwrite_fields segs nb R0 x) as [F1 [F2 [F3 [F4 F5]]]].
  assert (Ha : a = wz (rbase ρ R0 + to_Z x)) by (apply bv_eq; rewrite u_wz; [lia | unfold two64 in *; lia]).
  split; [rewrite Ha; apply store_ok_range; assumption|].
  split.
  - apply (regions_ok_replace ρ A i R0); [exact Hok | exact Hi | apply rbase_rwrite | exact F3 |].
    intros [W1 [W2 [W3 [W4 W5]]]]. unfold region_wf. rewrite rbase_rwrite, F3, F5, F4, F1. repeat split; assumption.
  - apply Forall_replace_nth'.
    +
      intros j Rj Hj Hne. pose proof (Forall_nth _ A j Rj HR Hj) as HRj.
      pose proof (regions_ok_disj ρ A i j R0 Rj Hok Hi Hj ltac:(lia)) as Hdis.
      pose proof (regions_ok_nth ρ A j Rj Hok Hj) as Wj. pose proof Wj as [Wj1 _].
      apply (RRegion_mframe segs ρ m _ Rj Wj); [|exact HRj].
      intros y Hy. apply Hfr. rewrite Eaddr.
      rewrite u_wz by (pose proof (smod_range ρ (rg_ts Rj) (rg_bo Rj)); unfold rbase in *; unfold two64 in *; lia).
      unfold rdisj in Hdis. lia.
    + rewrite (RRegion_ne segs ρ _ _ ltac:(unfold is_entry in *; rewrite F4; exact Hne0)).
      intros y Hy. rewrite F3 in Hy. rewrite rbase_rwrite. rewrite F4.
      pose proof (to_Z_bounded y). change wB with (2^63) in *.
      rewrite rbyte_rwrite by lia.
      destruct (HRR y Hy) as [[b [Hb Hab]] Hwv].
      assert (Hy64 : bv_unsigned (wz (rbase ρ R0 + to_Z y)) = rbase ρ R0 + to_Z y) by (apply u_wz; unfold two64 in *; lia).
      destruct ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) eqn:Ein.
      * apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        destruct (Hby (Z.to_nat (to_Z y - to_Z x)) ltac:(lia)) as [[b1 [Hb1 Hab1]]|[Eq1 EBT]];
          replace (bv_unsigned a + Z.of_nat (Z.to_nat (to_Z y - to_Z x))) with (rbase ρ R0 + to_Z y) in * by lia.
        -- split.
           ++ exists b1. unfold rv. rewrite Hb1. split; [reflexivity | exact Hab1].
           ++ intros _. unfold wview. rewrite Hb1. discriminate.
        -- rewrite EBT. split.
           ++ exists b. unfold rv in *. rewrite Eq1. split; [exact Hb | exact I].
           ++ intros Hwr. unfold wview in *. rewrite Eq1. apply Hwv. exact Hwr.
      * assert (Eq : m' (wz (rbase ρ R0 + to_Z y)) = m (wz (rbase ρ R0 + to_Z y))).
        { apply Hfr. rewrite Hy64, Eaddr. apply andb_false_iff in Ein as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1]; lia. }
        split.
        -- exists b. unfold rv in *. rewrite Eq. split; assumption.
        -- intros Hwr. unfold wview in *. rewrite Eq. apply Hwv. exact Hwr.
    + destruct (nth_error_Some A i) as [Hs _]. apply Hs. rewrite Hi. discriminate.
Qed.

Lemma store_ok_le (m : word -> option byte) : forall (k n : nat) (a : word), (k <= n)%nat -> store_ok segs m a n = true -> store_ok segs m a k = true.
Proof.
  induction k as [|k IH]; intros n a Hk H; [reflexivity|]. destruct n as [|n]; [lia|]. cbn [store_ok] in *.
  destruct (wview segs m a); [exact (IH n _ ltac:(lia) H) | discriminate].
Qed.

End Gen.

Definition lo_region (R : region) (x : int) : region := Rg (rg_ts R) (rg_bo R) x (rg_kind R) (rg_d R) (rg_cells R).

Definition mid_region (R : region) (x : int) : region :=
  Rg (rg_ts R) (w_add (rg_bo R) (wofZ (to_Z x))) (rg_n R - x)%uint63 KUnk (rg_d R) IEmpty.

Definition unk_region (R : region) : region := Rg (rg_ts R) (rg_bo R) (rg_n R) KUnk (rg_d R) IEmpty.

Section Forget.
Variable segs : list Segment.

Fixpoint copy_cells (R : region) (kh : int) (d : nat) (t : itrie cell) (j : int) (cnt : nat) : itrie cell :=
  match cnt with
  | O => t
  | S cnt' => copy_cells R kh d (iset d t j (cell_of segs R (kh + j)%uint63)) (j + 1)%uint63 cnt'
  end.

Definition buf_region (R : region) (x n : int) : region :=
  Rg (rg_ts R) (w_add (rg_bo R) (wofZ (to_Z x))) n KUnk (rg_d R) IEmpty.

Definition hi_region (R : region) (xh : int) : region :=
  Rg (rg_ts R) (w_add (rg_bo R) (wofZ (to_Z xh))) (rg_n R - xh)%uint63 KUnk (rg_d R)
     (copy_cells R (xh >> 3)%uint63 (rg_d R) IEmpty 0%uint63 (Z.to_nat ((to_Z (rg_n R - xh)%uint63 + 7) / 8))).

Definition al8 (z : int) : int := (((z + 7) >> 3) << 3)%uint63.

Definition carve_ok (R : region) (x : int) (n : Z) : bool :=
  (4096 <=? n) && (0 <? to_Z x) && (to_Z x + n + 7 <? to_Z (rg_n R)).

Definition has_mark (A : list region) : bool := lexists (fun R => (to_Z (rg_n R) =? 0)) A.

Definition hiz_region (R : region) (xh : int) : region :=
  Rg (rg_ts R) (w_add (rg_bo R) (wofZ (to_Z xh))) (rg_n R - xh)%uint63 KZero (rg_d R)
     (ishift (rg_d R) (to_Z (xh >> 3)%uint63) (rg_cells R)).

Definition zsplit_ok (R : region) (x : int) (n : Z) : bool := (to_Z x + n + 7 <? to_Z (rg_n R)).

Definition a_forget (A : list region) (v : xv) (n : Z) : option (list region) :=
  match xaddr v with
  | Some (ts, o) =>
      if (1 <=? n) && (n <? 1099511627776) then
      match find_reg A ts o (of_Z n) 0 with
      | Some (i, R, x) =>
          let k0 := to_Z x / 8 in
          let k1 := (to_Z x + n - 1) / 8 in
          match rg_kind R with
          | KUnk => Some (replace_nth A i (with_cells R (iremove (in_keys k0 k1) (rg_cells R) 0 1)))
          | KZero => if has_mark A &&& zsplit_ok R x n then
                       if (x =? 0)%uint63 then Some (replace_nth A i (buf_region R x (al8 (x + of_Z n) - x)%uint63) ++ [hiz_region R (al8 (x + of_Z n))])
                       else Some (replace_nth A i (lo_region R x) ++ [buf_region R x (al8 (x + of_Z n) - x)%uint63; hiz_region R (al8 (x + of_Z n))])
                     else if (x =? 0)%uint63 then Some (replace_nth A i (unk_region R))
                     else Some (replace_nth A i (lo_region R x) ++ [mid_region R x])
          | KImg true _ =>
              if carve_ok R x n then
                Some (replace_nth A i (lo_region R x) ++ [buf_region R x (al8 (x + of_Z n) - x)%uint63; hi_region R (al8 (x + of_Z n))])
              else Some (replace_nth A i (with_cells R (fill_bt (rg_d R) (rg_cells R) (of_Z k0) (Z.to_nat (k1 - k0 + 1)))))
          | _ => None
          end
      | None => None
      end
      else None
  | None => None
  end.

Lemma regions_ok_snoc (ρ : valuation) (B : list region) (M : region) :
  regions_ok ρ B -> region_wf ρ M -> Forall (fun R => rdisj ρ R M) B -> regions_ok ρ (B ++ [M]).
Proof.
  induction B as [|R B IH]; intros Hok Hw HF; cbn [app regions_ok] in *.
  - split; [exact Hw | split; [constructor | exact I]].
  - destruct Hok as [Hr [Hd Hok]]. inversion HF as [|? ? HRM HF']; subst.
    split; [exact Hr|]. split; [apply Forall_app; split; [exact Hd | constructor; [exact HRM | constructor]] | exact (IH Hok Hw HF')].
Qed.

Lemma regions_ok_replace_sub (ρ : valuation) (A : list region) (i : nat) (R R' : region) :
  regions_ok ρ A -> nth_error A i = Some R -> region_wf ρ R' ->
  rbase ρ R <= rbase ρ R' -> rbase ρ R' + to_Z (rg_n R') <= rbase ρ R + to_Z (rg_n R) ->
  regions_ok ρ (replace_nth A i R').
Proof.
  revert i. induction A as [|R0 A IH]; intros i Hok Hi Hw H1 H2; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error replace_nth regions_ok] in *.
  - injection Hi as <-. destruct Hok as [_ [Hd Hok]]. split; [exact Hw|]. split; [|exact Hok].
    rewrite Forall_forall in *. intros R2 HR2. specialize (Hd R2 HR2). unfold rdisj in *. lia.
  - destruct Hok as [Hw0 [Hd Hok]]. split; [exact Hw0|]. split; [|exact (IH i Hok Hi Hw H1 H2)].
    clear IH Hok. revert i Hi. induction A as [|R2 A IH2]; intros i Hi; [destruct i; discriminate|].
    inversion Hd as [|? ? HR2 Hd']; subst. destruct i as [|i]; cbn [nth_error replace_nth] in *.
    + injection Hi as <-. constructor; [unfold rdisj in *; lia | exact Hd'].
    + constructor; [exact HR2 | exact (IH2 Hd' i Hi)].
Qed.

Lemma Forall_replace_in (P : region -> Prop) (A : list region) (i : nat) (R' : region) :
  (forall j Rj, nth_error A j = Some Rj -> j <> i -> P Rj) -> P R' -> Forall P (replace_nth A i R').
Proof.
  revert i. induction A as [|R0 A IH]; intros i H HP; [destruct i; constructor|].
  destruct i as [|i]; cbn [replace_nth]; constructor.
  - exact HP.
  - apply Forall_forall. intros x Hx. apply In_nth_error in Hx as [j Hj]. apply (H (S j) x Hj). lia.
  - apply (H 0%nat R0 eq_refl). lia.
  - apply IH; [|exact HP]. intros j Rj Hj Hne. apply (H (S j) Rj Hj). lia.
Qed.

Lemma in_replace_nth (A : list region) (i : nat) (R' X : region) : In X (replace_nth A i R') -> X = R' \/ In X A.
Proof.
  revert i. induction A as [|R0 A IH]; intros i H; [destruct i; destruct H|].
  destruct i as [|i]; cbn [replace_nth] in H; destruct H as [<-|H].
  - left. reflexivity.
  - right. right. exact H.
  - right. left. reflexivity.
  - destruct (IH i H) as [E|E]; [left; exact E | right; right; exact E].
Qed.

Lemma in_replace_nth_keep (A : list region) (i : nat) (R R' X : region) :
  nth_error A i = Some R -> In X A -> X <> R -> In X (replace_nth A i R').
Proof.
  revert i. induction A as [|R0 A IH]; intros i Hi HX Hne; [destruct HX|].
  destruct i as [|i]; cbn [nth_error replace_nth] in *.
  - injection Hi as <-. destruct HX as [<-|HX]; [exfalso; apply Hne; reflexivity | right; exact HX].
  - destruct HX as [<-|HX]; [left; reflexivity | right; exact (IH i Hi HX Hne)].
Qed.

Lemma phi_of_Z_n (n : Z) : 0 <= n < 2 ^ 62 -> to_Z (of_Z n) = n.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2^63). lia. Qed.

Lemma rbyte_iremove (R : region) (k0 k1 : Z) (x : int) :
  to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z x < to_Z (rg_n R) -> rg_kind R = KUnk ->
  rbyte segs (with_cells R (iremove (in_keys k0 k1) (rg_cells R) 0 1)) x =
  if in_keys k0 k1 (to_Z x / 8) then BT else rbyte segs R x.
Proof.
  intros Hn Hx Ek. unfold rbyte, get_cell_opt, with_cells. cbn [rg_d rg_cells rg_kind]. rewrite iget_iremove.
  pose proof (key_small R x Hn Hx) as Hks. rewrite phi_lsr3 in *.
  rewrite Z.mod_small by (pose proof (to_Z_bounded x); change wB with (2 ^ 63) in *; split; [apply Z.div_pos; lia | lia]).
  rewrite Z.add_0_l, Z.mul_1_l. unfold default_byte. cbn [rg_kind]. rewrite Ek.
  destruct (iget (rg_d R) (rg_cells R) (x >> 3)%uint63) as [c|]; [|destruct (in_keys k0 k1 (to_Z x / 8)); reflexivity].
  destruct (in_keys k0 k1 (to_Z x / 8)); reflexivity.
Qed.

Lemma rbase_mid (ρ : valuation) (R : region) (x : int) :
  rbase ρ R + to_Z x <= two64 - 1 -> 0 <= to_Z x -> rbase ρ (mid_region R x) = rbase ρ R + to_Z x.
Proof.
  intros H Hx. unfold rbase, mid_region, smod. cbn [rg_ts rg_bo]. rewrite wZ_add, wZ_wofZ.
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hr. unfold rbase, smod in *.
  rewrite (Z.mod_small (to_Z x) two64) by (pose proof (to_Z_bounded x); change wB with (2^63) in *; unfold two64; lia).
  rewrite Zplus_mod_idemp_r. rewrite Z.add_assoc. rewrite <- Zplus_mod_idemp_l. apply Z.mod_small. lia.
Qed.

Lemma iget_copy_cells (R : region) (kh : int) (d : nat) : forall (cnt : nat) (t : itrie cell) (k j : int),
  (d <= 44)%nat -> to_Z k + Z.of_nat cnt <= 2 ^ Z.of_nat d -> to_Z j < 2 ^ Z.of_nat d ->
  iget d (copy_cells R kh d t k cnt) j =
  if (to_Z k <=? to_Z j) && (to_Z j <? to_Z k + Z.of_nat cnt) then Some (cell_of segs R (kh + j)%uint63) else iget d t j.
Proof.
  induction cnt as [|cnt IH]; intros t k j Hd Hk Hj; cbn [copy_cells].
  - replace ((to_Z k <=? to_Z j) && (to_Z j <? to_Z k + Z.of_nat 0)) with false; [reflexivity|].
    symmetry. apply andb_false_iff. destruct (Z.leb_spec (to_Z k) (to_Z j)); [right; apply Z.ltb_ge; lia | left; reflexivity].
  - pose proof (to_Z_bounded k) as Hkb. pose proof (to_Z_bounded j) as Hjb. change wB with (2 ^ 63) in *.
    assert (Hp : 2 ^ Z.of_nat d <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
    assert (Hk1 : to_Z (k + 1)%uint63 = to_Z k + 1).
    { rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    rewrite IH by (try assumption; rewrite Hk1; lia). rewrite Hk1. rewrite iget_iset.
    rewrite (Z.mod_small (to_Z k)) by lia. rewrite (Z.mod_small (to_Z j)) by lia.
    destruct (Z.eqb_spec (to_Z k) (to_Z j)) as [E|E].
    + apply to_Z_inj in E. subst j. rewrite Z.leb_refl. cbn [andb].
      replace (to_Z k <? to_Z k + Z.of_nat (S cnt)) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct ((to_Z k + 1 <=? to_Z k) && (to_Z k <? to_Z k + 1 + Z.of_nat cnt)); reflexivity.
    + replace ((to_Z k <=? to_Z j) && (to_Z j <? to_Z k + Z.of_nat (S cnt)))
        with ((to_Z k + 1 <=? to_Z j) && (to_Z j <? to_Z k + 1 + Z.of_nat cnt)); [reflexivity|].
      destruct (Z.leb_spec (to_Z k + 1) (to_Z j)), (Z.ltb_spec (to_Z j) (to_Z k + 1 + Z.of_nat cnt)),
               (Z.leb_spec (to_Z k) (to_Z j)), (Z.ltb_spec (to_Z j) (to_Z k + Z.of_nat (S cnt))); cbn [andb]; try reflexivity; lia.
Qed.

Lemma rbase_buf (ρ : valuation) (R : region) (x n : int) :
  rbase ρ R + to_Z x <= two64 - 1 -> 0 <= to_Z x -> rbase ρ (buf_region R x n) = rbase ρ R + to_Z x.
Proof. exact (rbase_mid ρ R x). Qed.

Lemma rbase_hi (ρ : valuation) (R : region) (xh : int) :
  rbase ρ R + to_Z xh <= two64 - 1 -> 0 <= to_Z xh -> rbase ρ (hi_region R xh) = rbase ρ R + to_Z xh.
Proof. exact (rbase_mid ρ R xh). Qed.

Lemma rbyte_hi (R : region) (xh y : int) :
  (rg_d R <= 44)%nat -> to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z (rg_n R) < 2 ^ 47 ->
  to_Z xh <= to_Z (rg_n R) -> to_Z xh mod 8 = 0 -> to_Z y < to_Z (rg_n R) - to_Z xh ->
  rbyte segs (hi_region R xh) y = rbyte segs R (xh + y)%uint63.
Proof.
  intros Hd44 Hd H47 Hxh Hal Hy.
  pose proof (to_Z_bounded xh) as Hxb. pose proof (to_Z_bounded y) as Hyb. pose proof (to_Z_bounded (rg_n R)) as Hnb. change wB with (2 ^ 63) in *.
  assert (Hnh : to_Z (rg_n R - xh)%uint63 = to_Z (rg_n R) - to_Z xh) by (rewrite sub_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  assert (Hsum : to_Z (xh + y)%uint63 = to_Z xh + to_Z y) by (rewrite add_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  assert (Hp : 2 ^ Z.of_nat (rg_d R) <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z.div_mod (to_Z xh) 8 ltac:(lia)) as Hdx. pose proof (Z.div_mod (to_Z y) 8 ltac:(lia)) as Hdy.
  pose proof (Z.mod_pos_bound (to_Z y) 8 ltac:(lia)) as Hmy.
  assert (Hy8 : to_Z y / 8 < (to_Z (rg_n R) - to_Z xh + 7) / 8).
  { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (to_Z (rg_n R) - to_Z xh + 7) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (to_Z (rg_n R) - to_Z xh + 7) 8 ltac:(lia)). lia. }
  assert (Hc8 : (to_Z (rg_n R) - to_Z xh + 7) / 8 <= 2 ^ Z.of_nat (rg_d R)).
  { assert ((to_Z (rg_n R) - to_Z xh + 7) / 8 < 2 ^ Z.of_nat (rg_d R) + 1) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hdiv : (to_Z xh + to_Z y) / 8 = to_Z xh / 8 + to_Z y / 8).
  { replace (to_Z xh + to_Z y) with (to_Z y + to_Z xh / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hmod : (to_Z xh + to_Z y) mod 8 = to_Z y mod 8).
  { replace (to_Z xh + to_Z y) with (to_Z y + to_Z xh / 8 * 8) by lia. apply Z.mod_add. lia. }
  assert (Ekey : ((xh >> 3) + (y >> 3))%uint63 = ((xh + y) >> 3)%uint63).
  { apply to_Z_inj. rewrite add_spec, !phi_lsr3, Hsum, Hdiv. apply Z.mod_small. change wB with (2 ^ 63).
    assert (0 <= to_Z xh / 8) by (apply Z.div_pos; lia). assert (0 <= to_Z y / 8) by (apply Z.div_pos; lia).
    assert (to_Z xh / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). assert (to_Z y / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Eland : (y land 7)%uint63 = ((xh + y) land 7)%uint63).
  { apply to_Z_inj. rewrite !phi_land7, Hsum, Hmod. reflexivity. }
  unfold rbyte at 1. unfold get_cell_opt, hi_region. cbn [rg_d rg_cells rg_kind].
  rewrite iget_copy_cells; [|exact Hd44 | change (to_Z 0%uint63) with 0; rewrite Hnh, Z2Nat.id by (apply Z.div_pos; lia); lia
                            | rewrite phi_lsr3; lia].
  change (to_Z 0%uint63) with 0. rewrite phi_lsr3, Hnh, Z2Nat.id by (apply Z.div_pos; lia).
  replace ((0 <=? to_Z y / 8) && (to_Z y / 8 <? 0 + (to_Z (rg_n R) - to_Z xh + 7) / 8)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; apply Z.div_pos; lia | apply Z.ltb_lt; lia]).
  rewrite Ekey, Eland. apply cbyte_cell_of. lia.
Qed.

Lemma al8_spec (z : int) : to_Z z < 2 ^ 61 -> to_Z z <= to_Z (al8 z) < to_Z z + 8 /\ to_Z (al8 z) mod 8 = 0.
Proof.
  intros Hz. pose proof (to_Z_bounded z) as Hzb. change wB with (2 ^ 63) in Hzb. unfold al8.
  assert (E1 : to_Z (z + 7)%uint63 = to_Z z + 7) by (rewrite add_spec; change (to_Z 7%uint63) with 7; apply Z.mod_small; change wB with (2 ^ 63); lia).
  assert (E2 : to_Z ((z + 7) >> 3)%uint63 = (to_Z z + 7) / 8) by (rewrite lsr_spec, E1; change (to_Z 3%uint63) with 3; reflexivity).
  pose proof (Z.div_mod (to_Z z + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (to_Z z + 7) 8 ltac:(lia)) as B.
  assert (E3 : to_Z (((z + 7) >> 3) << 3)%uint63 = (to_Z z + 7) / 8 * 8).
  { rewrite lsl_spec, E2. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  rewrite E3. split; [lia | apply Z_mod_mult].
Qed.

Lemma carve_ok_spec (R : region) (x : int) (n : Z) : 1 <= n < 1099511627776 -> to_Z (rg_n R) < 2 ^ 47 -> carve_ok R x n = true ->
  0 < to_Z x /\ to_Z x + n <= to_Z (al8 (x + of_Z n)) < to_Z x + n + 8 /\ to_Z (al8 (x + of_Z n)) < to_Z (rg_n R)
  /\ to_Z (al8 (x + of_Z n)) mod 8 = 0 /\ to_Z (of_Z n) = n /\ to_Z (al8 (x + of_Z n) - x)%uint63 = to_Z (al8 (x + of_Z n)) - to_Z x.
Proof.
  intros Hn H47 H. unfold carve_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H2, H3. pose proof (to_Z_bounded x) as Hxb. change wB with (2 ^ 63) in Hxb.
  assert (Hnz : to_Z (of_Z n) = n) by (apply phi_of_Z_n; lia).
  assert (Hs : to_Z (x + of_Z n)%uint63 = to_Z x + n) by (rewrite add_spec, Hnz; apply Z.mod_small; change wB with (2 ^ 63); lia).
  destruct (al8_spec (x + of_Z n)%uint63 ltac:(lia)) as [A1 A2]. rewrite Hs in A1.
  split; [exact H2|]. split; [exact A1|]. split; [lia|]. split; [exact A2|]. split; [exact Hnz|].
  rewrite sub_spec. apply Z.mod_small. change wB with (2 ^ 63). lia.
Qed.

Lemma zsplit_ok_spec (R : region) (x : int) (n : Z) : 1 <= n < 1099511627776 -> to_Z (rg_n R) < 2 ^ 47 -> zsplit_ok R x n = true ->
  to_Z x + n <= to_Z (al8 (x + of_Z n)) < to_Z x + n + 8 /\ to_Z (al8 (x + of_Z n)) < to_Z (rg_n R)
  /\ to_Z (al8 (x + of_Z n)) mod 8 = 0 /\ to_Z (al8 (x + of_Z n) - x)%uint63 = to_Z (al8 (x + of_Z n)) - to_Z x.
Proof.
  intros Hn H47 H. unfold zsplit_ok in H. apply Z.ltb_lt in H. pose proof (to_Z_bounded x) as Hxb. change wB with (2 ^ 63) in Hxb.
  assert (Hnz : to_Z (of_Z n) = n) by (apply phi_of_Z_n; lia).
  assert (Hs : to_Z (x + of_Z n)%uint63 = to_Z x + n) by (rewrite add_spec, Hnz; apply Z.mod_small; change wB with (2 ^ 63); lia).
  destruct (al8_spec (x + of_Z n)%uint63 ltac:(lia)) as [A1 A2]. rewrite Hs in A1.
  split; [exact A1|]. split; [lia|]. split; [exact A2|].
  rewrite sub_spec. apply Z.mod_small. change wB with (2 ^ 63). lia.
Qed.

Lemma rbyte_hiz (R : region) (xh y : int) : rg_kind R = KZero ->
  (rg_d R <= 44)%nat -> to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z (rg_n R) < 2 ^ 47 ->
  to_Z xh <= to_Z (rg_n R) -> to_Z xh mod 8 = 0 -> to_Z y < to_Z (rg_n R) - to_Z xh ->
  rbyte segs (hiz_region R xh) y = rbyte segs R (xh + y)%uint63.
Proof.
  intros Ek Hd44 Hd H47 Hxh Hal Hy.
  pose proof (to_Z_bounded xh) as Hxb. pose proof (to_Z_bounded y) as Hyb. pose proof (to_Z_bounded (rg_n R)) as Hnb. change wB with (2 ^ 63) in *.
  assert (Hsum : to_Z (xh + y)%uint63 = to_Z xh + to_Z y) by (rewrite add_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  assert (Hp : 2 ^ Z.of_nat (rg_d R) <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z.div_mod (to_Z xh) 8 ltac:(lia)) as Hdx. pose proof (Z.div_mod (to_Z y) 8 ltac:(lia)) as Hdy.
  pose proof (Z.mod_pos_bound (to_Z y) 8 ltac:(lia)) as Hmy.
  assert (Hdiv : (to_Z xh + to_Z y) / 8 = to_Z xh / 8 + to_Z y / 8).
  { replace (to_Z xh + to_Z y) with (to_Z y + to_Z xh / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hmod : (to_Z xh + to_Z y) mod 8 = to_Z y mod 8).
  { replace (to_Z xh + to_Z y) with (to_Z y + to_Z xh / 8 * 8) by lia. apply Z.mod_add. lia. }
  assert (Hq : 0 <= to_Z y / 8 + to_Z xh / 8 < 2 ^ Z.of_nat (rg_d R)).
  { split; [assert (0 <= to_Z xh / 8) by (apply Z.div_pos; lia); assert (0 <= to_Z y / 8) by (apply Z.div_pos; lia); lia|].
    rewrite Z.add_comm, <- Hdiv. apply Z.div_lt_upper_bound; lia. }
  assert (Ey : (y >> 3)%uint63 = of_Z (to_Z y / 8)) by (rewrite <- phi_lsr3; symmetry; apply of_to_Z).
  assert (Ekey : of_Z (to_Z y / 8 + to_Z xh / 8) = ((xh + y) >> 3)%uint63).
  { apply to_Z_inj. rewrite phi_lsr3, Hsum, Hdiv, of_Z_spec. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). lia. }
  assert (Eland : (y land 7)%uint63 = ((xh + y) land 7)%uint63).
  { apply to_Z_inj. rewrite !phi_land7, Hsum, Hmod. reflexivity. }
  unfold rbyte at 1. unfold get_cell_opt, hiz_region. cbn [rg_d rg_cells rg_kind].
  rewrite Ey, (iget_ishift (rg_d R) (to_Z (xh >> 3)%uint63) (rg_cells R) (to_Z y / 8) ltac:(lia)
                 ltac:(rewrite phi_lsr3; apply Z.div_pos; lia)
                 ltac:(assert (0 <= to_Z xh / 8) by (apply Z.div_pos; lia); assert (0 <= to_Z y / 8) by (apply Z.div_pos; lia); lia)).
  rewrite phi_lsr3. unfold zget.
  replace ((0 <=? to_Z y / 8 + to_Z xh / 8) && (to_Z y / 8 + to_Z xh / 8 <? 2 ^ Z.of_nat (rg_d R))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite Ekey, Eland. unfold rbyte, get_cell_opt. rewrite Ek. reflexivity.
Qed.

Definition mem_grows (m m' : word -> option byte) : Prop := forall y, m y <> None -> m' y <> None.

Lemma rv_grows (m m' : word -> option byte) (y : word) (b : byte) :
  mem_grows m m' -> rv segs m y = Some b -> exists b', rv segs m' y = Some b'.
Proof.
  intros Hg H. unfold rv in *. destruct (m y) as [b0|] eqn:E.
  - destruct (m' y) as [b1|] eqn:E'; [exists b1; reflexivity|]. exfalso. apply (Hg y); [rewrite E; discriminate | exact E'].
  - destruct (m' y) as [b1|]; [exists b1; reflexivity | exists b; exact H].
Qed.

Lemma wview_grows (m m' : word -> option byte) (y : word) :
  mem_grows m m' -> wview segs m y <> None -> wview segs m' y <> None.
Proof.
  intros Hg H. unfold wview in *. destruct (m y) as [b0|] eqn:E.
  - destruct (m' y) as [b1|] eqn:E'; [discriminate|]. exfalso. apply (Hg y); [rewrite E; discriminate | exact E'].
  - destruct (m' y); [discriminate | exact H].
Qed.

Lemma RRegion0_unk (ρ : valuation) (m m' : word -> option byte) (R R' : region) (off : Z) :
  RRegion0 segs ρ m R -> rk_writable (rg_kind R) = true -> mem_grows m m' ->
  rbase ρ R' = rbase ρ R + off -> 0 <= off -> off + to_Z (rg_n R') <= to_Z (rg_n R) ->
  rk_writable (rg_kind R') = true -> (forall y, to_Z y < to_Z (rg_n R') -> rbyte segs R' y = BT) ->
  RRegion0 segs ρ m' R'.
Proof.
  intros HR Hw Hg Eb Ho Hn Hw' HBT y Hy. rewrite (HBT y Hy), Eb.
  pose proof (to_Z_bounded y) as Hyb. pose proof (to_Z_bounded (rg_n R)) as HnR. change wB with (2^63) in *.
  assert (Hyx : to_Z (of_Z (off + to_Z y)) = off + to_Z y) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2^63); lia).
  destruct (HR (of_Z (off + to_Z y)) ltac:(rewrite Hyx; lia)) as [[b [Hb _]] Hwv]. rewrite Hyx, Z.add_assoc in Hb, Hwv.
  split.
  - destruct (rv_grows m m' _ b Hg Hb) as [b' Hb']. exists b'. split; [exact Hb' | exact I].
  - intros _. exact (wview_grows m m' _ Hg (Hwv Hw)).
Qed.

Lemma div8_lt (y z : Z) : y / 8 < z / 8 -> y < z.
Proof. intros H. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
  pose proof (Z.div_mod z 8 ltac:(lia)). pose proof (Z.mod_pos_bound z 8 ltac:(lia)). lia. Qed.

Lemma a_forget_inv (A A' : list region) (v : xv) (n : Z) :
  a_forget A v n = Some A' ->
  exists ts o i R x, xaddr v = Some (ts, o) /\ 1 <= n < 1099511627776 /\ find_reg A ts o (of_Z n) 0 = Some (i, R, x) /\
    ((rg_kind R = KUnk /\ A' = replace_nth A i (with_cells R (iremove (in_keys (to_Z x / 8) ((to_Z x + n - 1) / 8)) (rg_cells R) 0 1)))
     \/ (rg_kind R = KZero /\ x = 0%uint63 /\ A' = replace_nth A i (unk_region R))
     \/ (rg_kind R = KZero /\ x <> 0%uint63 /\ A' = replace_nth A i (lo_region R x) ++ [mid_region R x])
     \/ (exists j, rg_kind R = KImg true j /\ A' = replace_nth A i (havoc_cells R (to_Z x / 8) ((to_Z x + n - 1) / 8)))
     \/ (exists j, rg_kind R = KImg true j /\ carve_ok R x n = true
                   /\ A' = replace_nth A i (lo_region R x) ++ [buf_region R x (al8 (x + of_Z n) - x)%uint63; hi_region R (al8 (x + of_Z n))])
     \/ (rg_kind R = KZero /\ x = 0%uint63 /\ zsplit_ok R x n = true
         /\ A' = replace_nth A i (buf_region R x (al8 (x + of_Z n) - x)%uint63) ++ [hiz_region R (al8 (x + of_Z n))])
     \/ (rg_kind R = KZero /\ x <> 0%uint63 /\ zsplit_ok R x n = true
         /\ A' = replace_nth A i (lo_region R x) ++ [buf_region R x (al8 (x + of_Z n) - x)%uint63; hiz_region R (al8 (x + of_Z n))])).
Proof.
  unfold a_forget. destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct ((1 <=? n) && (n <? 1099511627776)) eqn:En; [|discriminate].
  apply andb_prop in En as [En1 En2]. apply Z.leb_le in En1. apply Z.ltb_lt in En2.
  destruct (find_reg A ts o (of_Z n) 0) as [[[i R] x]|] eqn:Ef; [|discriminate].
  intros H. exists ts, o, i, R, x. split; [reflexivity|]. split; [lia|]. split; [exact Ef|].
  destruct (rg_kind R) as [| | |[|] j|ph] eqn:Ek; try discriminate.
  - destruct (has_mark A &&& zsplit_ok R x n) eqn:Ezs.
    + apply land_true in Ezs as [_ Ezs]. destruct (x =? 0)%uint63 eqn:Ex; injection H as <-.
      * right. right. right. right. right. left. apply Uint63.eqb_spec in Ex. split; [reflexivity|]. split; [exact Ex|]. split; [exact Ezs | reflexivity].
      * right. right. right. right. right. right. split; [reflexivity|]. split; [|split; [exact Ezs | reflexivity]].
        intros E. rewrite E, Uint63.eqb_refl in Ex. discriminate.
    + destruct (x =? 0)%uint63 eqn:Ex; injection H as <-.
      * right. left. apply Uint63.eqb_spec in Ex. split; [reflexivity | split; [exact Ex | reflexivity]].
      * right. right. left. split; [reflexivity|]. split; [|reflexivity]. intros E. rewrite E, Uint63.eqb_refl in Ex. discriminate.
  - injection H as <-. left. split; reflexivity.
  - destruct (carve_ok R x n) eqn:Ecv; injection H as <-.
    + right. right. right. right. left. exists j. split; [reflexivity|]. split; reflexivity.
    + right. right. right. left. exists j. split; [reflexivity|]. rewrite havoc_bt_eq. reflexivity.
Qed.

Theorem a_forget_sound (ρ : valuation) (A A' : list region) (m m' : word -> option byte) (v : xv) (a : bv 64) (n : Z) :
  RMem segs ρ A m -> xv_val ρ v a -> a_forget A v n = Some A' ->
  (forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + n) -> m' x = m x) ->
  mem_grows m m' -> RMem segs ρ A' m'.
Proof.
  intros [Hok HR] Hv H Hfr Hg.
  destruct (a_forget_inv A A' v n H) as (ts & o & i & R & x & Ea & Hn & Ef & Hcase).
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf. pose proof (Forall_nth _ A i R HR Hi) as HRR.
  pose proof (roff_ne R ts o _ x Hr) as Hne0. rewrite (RRegion_ne segs ρ m R Hne0) in HRR.
  assert (Hav : bv_unsigned a = smod ρ ts o).
  { destruct v; cbn [xaddr] in Ea; try discriminate; injection Ea as <- <-; cbn [xv_val] in Hv.
    - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
    - exact Hv. }
  assert (Hnz : to_Z (of_Z n) = n) by (apply phi_of_Z_n; lia).
  destruct (roff_addr ρ R ts o (of_Z n) x a ltac:(rewrite Hnz; lia) Hwf Hav Hr) as [Eaddr Hfit]. rewrite Hnz in Hfit.
  pose proof Hwf as [Hw1 [H47 [Hd [Hd44 Himg]]]].
  pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hsr. fold (rbase ρ R) in Hsr.
  assert (Hwr : rk_writable (rg_kind R) = true) by (destruct Hcase as [[E _]|[[E _]|[[E _]|[[j [E _]]|[[j [E _]]|[[E _]|[E _]]]]]]]; rewrite E; reflexivity).

  assert (Hoth : forall j Rj, nth_error A j = Some Rj -> j <> i -> RRegion segs ρ m' Rj).
  { intros j Rj Hj Hne. pose proof (Forall_nth _ A j Rj HR Hj) as HRj.
    pose proof (regions_ok_disj ρ A i j R Rj Hok Hi Hj ltac:(lia)) as Hdis.
    pose proof (regions_ok_nth ρ A j Rj Hok Hj) as Wj. pose proof Wj as [Wj1 _].
    apply (RRegion_mframe segs ρ m _ Rj Wj); [|exact HRj].
    intros y Hy. apply Hfr. rewrite Eaddr.
    rewrite u_wz by (pose proof (smod_range ρ (rg_ts Rj) (rg_bo Rj)); unfold rbase in *; unfold two64 in *; lia).
    unfold rdisj in Hdis. lia. }

  assert (Hkeep : forall y : int, to_Z y < to_Z (rg_n R) -> (to_Z y < to_Z x \/ to_Z x + n <= to_Z y) ->
            m' (wz (rbase ρ R + to_Z y)) = m (wz (rbase ρ R + to_Z y))).
  { intros y Hy Hout. apply Hfr. pose proof (to_Z_bounded y). change wB with (2^63) in *.
    rewrite u_wz by (unfold two64 in *; lia). rewrite Eaddr. lia. }
  assert (Hold : forall y : int, to_Z y < to_Z (rg_n R) -> (to_Z y < to_Z x \/ to_Z x + n <= to_Z y) ->
            (exists b, rv segs m' (wz (rbase ρ R + to_Z y)) = Some b /\ xb_z ρ (rbyte segs R y) (bv_unsigned b))
            /\ (rk_writable (rg_kind R) = true -> wview segs m' (wz (rbase ρ R + to_Z y)) <> None)).
  { intros y Hy Hout. destruct (HRR y Hy) as [[b [Hb Hab]] Hwv]. pose proof (Hkeep y Hy Hout) as E.
    split; [exists b; unfold rv in *; rewrite E; split; assumption | intros Hw'; unfold wview in *; rewrite E; exact (Hwv Hw')]. }
  assert (Hunk : forall y : int, to_Z y < to_Z (rg_n R) ->
            (exists b, rv segs m' (wz (rbase ρ R + to_Z y)) = Some b /\ xb_z ρ BT (bv_unsigned b))
            /\ (rk_writable KUnk = true -> wview segs m' (wz (rbase ρ R + to_Z y)) <> None)).
  { intros y Hy. destruct (HRR y Hy) as [[b [Hb _]] Hwv].
    split; [destruct (rv_grows m m' _ b Hg Hb) as [b' Hb']; exists b'; split; [exact Hb' | exact I]|].
    intros _. exact (wview_grows m m' _ Hg (Hwv Hwr)). }
  destruct Hcase as [[Ek EA]|[[Ek [Ex EA]]|[[Ek [Ex EA]]|[[j [Ek EA]]|[[j [Ek [Hcv EA]]]|[[Ek [Ex [Hzs EA]]]|[Ek [Ex [Hzs EA]]]]]]]]]; subst A'.
  -
    split.
    + apply (regions_ok_replace ρ A i R); [exact Hok | exact Hi | reflexivity | reflexivity |].
      intros W. exact W.
    + apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
      rewrite RRegion_ne by (unfold is_entry, with_cells; cbn [rg_kind]; rewrite Ek; reflexivity).
      intros y Hy. cbn [with_cells rg_n] in Hy. unfold rbase at 1 2; cbn [with_cells rg_ts rg_bo]; fold (rbase ρ R).
      rewrite rbyte_iremove by (try exact Hd; try exact Hy; exact Ek). cbn [with_cells rg_kind]. rewrite Ek.
      destruct (in_keys (to_Z x / 8) ((to_Z x + n - 1) / 8) (to_Z y / 8)) eqn:Ein.
      * exact (Hunk y Hy).
      * rewrite <- Ek. apply Hold; [exact Hy|]. unfold in_keys in Ein. pose proof (to_Z_bounded y); change wB with (2^63) in *.
        apply andb_false_iff in Ein as [E|E]; apply Z.leb_gt in E; [left; exact (div8_lt _ _ E) | right; pose proof (div8_lt _ _ E); lia].
  -
    split.
    + apply (regions_ok_replace ρ A i R); [exact Hok | exact Hi | reflexivity | reflexivity |].
      intros [W1 [W2 [W3 [W4 W5]]]]. unfold region_wf, unk_region, rbase in *. cbn [rg_ts rg_bo rg_n rg_d rg_kind] in *.
      repeat split; try assumption. intros a0 i0 E. discriminate E.
    + apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
      rewrite RRegion_ne by reflexivity. intros y Hy. cbn [unk_region rg_n] in Hy.
      replace (rbase ρ (unk_region R)) with (rbase ρ R) by reflexivity.
      replace (rbyte segs (unk_region R) y) with BT by (unfold rbyte, get_cell_opt, unk_region; cbn [rg_d rg_cells]; rewrite iget_empty; reflexivity).
      exact (Hunk y Hy).
  -
    assert (Hx0 : 0 < to_Z x) by (assert (to_Z x <> 0) by (intros E; apply Ex; apply to_Z_inj; exact E); lia).
    assert (Hnm : to_Z (rg_n R - x)%uint63 = to_Z (rg_n R) - to_Z x).
    { rewrite sub_spec. apply Z.mod_small. pose proof (to_Z_bounded (rg_n R)). change wB with (2^63) in *. lia. }
    assert (Ebm : rbase ρ (mid_region R x) = rbase ρ R + to_Z x) by (apply rbase_mid; unfold two64 in *; lia).
    assert (Wlo : region_wf ρ (lo_region R x)).
    { unfold region_wf, lo_region, rbase in *. cbn [rg_ts rg_bo rg_n rg_d rg_kind] in *. repeat split; try lia; assumption. }
    assert (Wmid : region_wf ρ (mid_region R x)).
    { unfold region_wf. rewrite Ebm. cbn [mid_region rg_n rg_d rg_kind]. rewrite Hnm. repeat split; try lia. intros a0 i0 E. discriminate E. }
    split.
    + apply regions_ok_snoc.
      * apply (regions_ok_replace_sub ρ A i R); [exact Hok | exact Hi | exact Wlo | unfold rbase, lo_region; cbn [rg_ts rg_bo]; lia |].
        unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
      * exact Wmid.
      * apply Forall_replace_in.
        -- intros j Rj Hj Hne. pose proof (regions_ok_disj ρ A j i Rj R Hok Hj Hi ltac:(lia)) as Hdis.
           unfold rdisj in *. rewrite Ebm. cbn [mid_region rg_n]. rewrite Hnm. lia.
        -- unfold rdisj. rewrite Ebm. unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
    + apply Forall_app. split.
      * apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
        rewrite RRegion_ne by (unfold is_entry, lo_region; cbn [rg_kind]; rewrite Ek; reflexivity).
        intros y Hy. cbn [lo_region rg_n] in Hy. replace (rbase ρ (lo_region R x)) with (rbase ρ R) by reflexivity.
        replace (rbyte segs (lo_region R x) y) with (rbyte segs R y) by reflexivity.
        replace (rk_writable (rg_kind (lo_region R x))) with (rk_writable (rg_kind R)) by reflexivity.
        apply Hold; lia.
      * constructor; [|constructor]. rewrite RRegion_ne by reflexivity.
        apply (RRegion0_unk ρ m m' R (mid_region R x) (to_Z x) HRR Hwr Hg Ebm ltac:(lia)); [cbn [mid_region rg_n]; rewrite Hnm; lia | reflexivity|].
        intros y _. unfold rbyte, get_cell_opt, mid_region. cbn [rg_d rg_cells]. rewrite iget_empty. reflexivity.
  -
    assert (Hk1 : (to_Z x + n - 1) / 8 < 2 ^ Z.of_nat (rg_d R)) by (apply Z.div_lt_upper_bound; lia).
    split.
    + apply (regions_ok_replace ρ A i R); [exact Hok | exact Hi | reflexivity | reflexivity |]. intros W. exact W.
    + apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
      rewrite RRegion_ne by (unfold is_entry, havoc_cells, with_cells; cbn [rg_kind]; rewrite Ek; reflexivity).
      intros y Hy. cbn [havoc_cells with_cells rg_n] in Hy. replace (rbase ρ (havoc_cells R _ _)) with (rbase ρ R) by reflexivity.
      replace (rk_writable (rg_kind (havoc_cells R (to_Z x / 8) ((to_Z x + n - 1) / 8)))) with (rk_writable (rg_kind R)) by reflexivity.
      rewrite (rbyte_havoc segs R (to_Z x / 8) ((to_Z x + n - 1) / 8) y ltac:(apply Z.div_pos; lia) Hk1 Hd44 Hd Hy).
      destruct ((to_Z x / 8 <=? to_Z y / 8) && (to_Z y / 8 <=? (to_Z x + n - 1) / 8)) eqn:Ein.
      * rewrite Hwr. destruct (Hunk y Hy) as [X1 X2]. split; [exact X1 | intros _; exact (X2 eq_refl)].
      * apply Hold; [exact Hy|]. pose proof (to_Z_bounded y); change wB with (2^63) in *.
        apply andb_false_iff in Ein as [E|E]; apply Z.leb_gt in E; [left; exact (div8_lt _ _ E) | right; pose proof (div8_lt _ _ E); lia].
  -
    destruct (carve_ok_spec R x n Hn H47 Hcv) as (Hx0 & Hxh & Hlt & Hal & _ & Hnb).
    set (xh := al8 (x + of_Z n)) in *. set (nb := (xh - x)%uint63) in *.
    pose proof (to_Z_bounded (rg_n R)) as HnRb. change wB with (2^63) in HnRb.
    assert (Hnh : to_Z (rg_n R - xh)%uint63 = to_Z (rg_n R) - to_Z xh).
    { rewrite sub_spec. apply Z.mod_small. change wB with (2^63). lia. }
    assert (Ebb : rbase ρ (buf_region R x nb) = rbase ρ R + to_Z x) by (apply rbase_buf; unfold two64 in *; lia).
    assert (Ebh : rbase ρ (hi_region R xh) = rbase ρ R + to_Z xh) by (apply rbase_hi; unfold two64 in *; lia).
    assert (Wlo : region_wf ρ (lo_region R x)).
    { unfold region_wf, lo_region, rbase in *. cbn [rg_ts rg_bo rg_n rg_d rg_kind] in *. repeat split; try lia; assumption. }
    assert (Wbuf : region_wf ρ (buf_region R x nb)).
    { unfold region_wf. rewrite Ebb. cbn [buf_region rg_n rg_d rg_kind]. rewrite Hnb. repeat split; try lia. intros a0 i0 E. discriminate E. }
    assert (Whi : region_wf ρ (hi_region R xh)).
    { unfold region_wf. rewrite Ebh. cbn [hi_region rg_n rg_d rg_kind]. rewrite Hnh. repeat split; try lia. intros a0 i0 E. discriminate E. }
    split.
    + change [buf_region R x nb; hi_region R xh] with ([buf_region R x nb] ++ [hi_region R xh]). rewrite app_assoc.
      apply regions_ok_snoc; [apply regions_ok_snoc | exact Whi |].
      * apply (regions_ok_replace_sub ρ A i R); [exact Hok | exact Hi | exact Wlo | unfold rbase, lo_region; cbn [rg_ts rg_bo]; lia |].
        unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
      * exact Wbuf.
      * apply Forall_replace_in.
        -- intros j0 Rj Hj Hne. pose proof (regions_ok_disj ρ A j0 i Rj R Hok Hj Hi ltac:(lia)) as Hdis.
           unfold rdisj in *. rewrite Ebb. cbn [buf_region rg_n]. rewrite Hnb. lia.
        -- unfold rdisj. rewrite Ebb. unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
      * apply Forall_app. split; [apply Forall_replace_in | constructor; [|constructor]].
        -- intros j0 Rj Hj Hne. pose proof (regions_ok_disj ρ A j0 i Rj R Hok Hj Hi ltac:(lia)) as Hdis.
           unfold rdisj in *. rewrite Ebh. cbn [hi_region rg_n]. rewrite Hnh. lia.
        -- unfold rdisj. rewrite Ebh. unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
        -- unfold rdisj. rewrite Ebh, Ebb. cbn [buf_region rg_n]. rewrite Hnb. lia.
    + apply Forall_app. split.
      * apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
        rewrite RRegion_ne by (unfold is_entry, lo_region; cbn [rg_kind]; rewrite Ek; reflexivity).
        intros y Hy. cbn [lo_region rg_n] in Hy. replace (rbase ρ (lo_region R x)) with (rbase ρ R) by reflexivity.
        replace (rbyte segs (lo_region R x) y) with (rbyte segs R y) by reflexivity.
        replace (rk_writable (rg_kind (lo_region R x))) with (rk_writable (rg_kind R)) by reflexivity.
        apply Hold; lia.
      * constructor; [|constructor; [|constructor]].
        -- rewrite RRegion_ne by reflexivity.
           apply (RRegion0_unk ρ m m' R (buf_region R x nb) (to_Z x) HRR Hwr Hg Ebb ltac:(lia)); [cbn [buf_region rg_n]; rewrite Hnb; lia | reflexivity|].
           intros y _. unfold rbyte, get_cell_opt, buf_region. cbn [rg_d rg_cells]. rewrite iget_empty. reflexivity.
        -- rewrite RRegion_ne by reflexivity. intros y Hy. cbn [hi_region rg_n] in Hy. rewrite Hnh in Hy. rewrite Ebh.
           pose proof (to_Z_bounded y) as Hyb. change wB with (2^63) in Hyb.
           rewrite (rbyte_hi R xh y Hd44 Hd H47 ltac:(lia) Hal ltac:(lia)).
           assert (Hsum : to_Z (xh + y)%uint63 = to_Z xh + to_Z y) by (rewrite add_spec; apply Z.mod_small; change wB with (2^63); lia).
           destruct (Hold (xh + y)%uint63 ltac:(rewrite Hsum; lia) ltac:(right; rewrite Hsum; lia)) as [X1 X2].
           rewrite Hsum, Z.add_assoc in X1, X2. split; [exact X1 | intros _; exact (X2 Hwr)].
  -
    destruct (zsplit_ok_spec R x n Hn H47 Hzs) as (Hxh & Hlt & Hal & Hnb).
    assert (Hx00 : to_Z x = 0) by (rewrite Ex; reflexivity).
    set (xh := al8 (x + of_Z n)) in *. set (nb := (xh - x)%uint63) in *.
    pose proof (to_Z_bounded (rg_n R)) as HnRb. change wB with (2^63) in HnRb.
    assert (Hnh : to_Z (rg_n R - xh)%uint63 = to_Z (rg_n R) - to_Z xh).
    { rewrite sub_spec. apply Z.mod_small. change wB with (2^63). lia. }
    assert (Ebb : rbase ρ (buf_region R x nb) = rbase ρ R + to_Z x) by (apply rbase_buf; unfold two64 in *; lia).
    assert (Ebh : rbase ρ (hiz_region R xh) = rbase ρ R + to_Z xh) by (exact (rbase_mid ρ R xh ltac:(unfold two64 in *; lia) ltac:(lia))).
    assert (Wbuf : region_wf ρ (buf_region R x nb)).
    { unfold region_wf. rewrite Ebb. cbn [buf_region rg_n rg_d rg_kind]. rewrite Hnb. repeat split; try lia. intros a0 i0 E. discriminate E. }
    assert (Whi : region_wf ρ (hiz_region R xh)).
    { unfold region_wf. rewrite Ebh. cbn [hiz_region rg_n rg_d rg_kind]. rewrite Hnh. repeat split; try lia. intros a0 i0 E. discriminate E. }
    split.
    + apply regions_ok_snoc.
      * apply (regions_ok_replace_sub ρ A i R); [exact Hok | exact Hi | exact Wbuf | rewrite Ebb; lia |].
        rewrite Ebb. cbn [buf_region rg_n]. rewrite Hnb. lia.
      * exact Whi.
      * apply Forall_replace_in.
        -- intros j0 Rj Hj Hne. pose proof (regions_ok_disj ρ A j0 i Rj R Hok Hj Hi ltac:(lia)) as Hdis.
           unfold rdisj in *. rewrite Ebh. cbn [hiz_region rg_n]. rewrite Hnh. lia.
        -- unfold rdisj. rewrite Ebh, Ebb. cbn [buf_region rg_n]. rewrite Hnb. lia.
    + apply Forall_app. split.
      * apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
        rewrite RRegion_ne by reflexivity.
        apply (RRegion0_unk ρ m m' R (buf_region R x nb) (to_Z x) HRR Hwr Hg Ebb ltac:(lia)); [cbn [buf_region rg_n]; rewrite Hnb; lia | reflexivity|].
        intros y _. unfold rbyte, get_cell_opt, buf_region. cbn [rg_d rg_cells]. rewrite iget_empty. reflexivity.
      * constructor; [|constructor].
        rewrite RRegion_ne by reflexivity. intros y Hy. cbn [hiz_region rg_n] in Hy. rewrite Hnh in Hy. rewrite Ebh.
        pose proof (to_Z_bounded y) as Hyb. change wB with (2^63) in Hyb.
        rewrite (rbyte_hiz R xh y Ek Hd44 Hd H47 ltac:(lia) Hal ltac:(lia)).
        assert (Hsum : to_Z (xh + y)%uint63 = to_Z xh + to_Z y) by (rewrite add_spec; apply Z.mod_small; change wB with (2^63); lia).
        destruct (Hold (xh + y)%uint63 ltac:(rewrite Hsum; lia) ltac:(right; rewrite Hsum; lia)) as [X1 X2].
        rewrite Hsum, Z.add_assoc in X1, X2. split; [exact X1 | intros _; exact (X2 Hwr)].
  -
    destruct (zsplit_ok_spec R x n Hn H47 Hzs) as (Hxh & Hlt & Hal & Hnb).
    assert (Hx0 : 0 < to_Z x) by (assert (to_Z x <> 0) by (intros E; apply Ex; apply to_Z_inj; exact E); lia).
    set (xh := al8 (x + of_Z n)) in *. set (nb := (xh - x)%uint63) in *.
    pose proof (to_Z_bounded (rg_n R)) as HnRb. change wB with (2^63) in HnRb.
    assert (Hnh : to_Z (rg_n R - xh)%uint63 = to_Z (rg_n R) - to_Z xh).
    { rewrite sub_spec. apply Z.mod_small. change wB with (2^63). lia. }
    assert (Ebb : rbase ρ (buf_region R x nb) = rbase ρ R + to_Z x) by (apply rbase_buf; unfold two64 in *; lia).
    assert (Ebh : rbase ρ (hiz_region R xh) = rbase ρ R + to_Z xh) by (exact (rbase_mid ρ R xh ltac:(unfold two64 in *; lia) ltac:(lia))).
    assert (Wlo : region_wf ρ (lo_region R x)).
    { unfold region_wf, lo_region, rbase in *. cbn [rg_ts rg_bo rg_n rg_d rg_kind] in *. repeat split; try lia; assumption. }
    assert (Wbuf : region_wf ρ (buf_region R x nb)).
    { unfold region_wf. rewrite Ebb. cbn [buf_region rg_n rg_d rg_kind]. rewrite Hnb. repeat split; try lia. intros a0 i0 E. discriminate E. }
    assert (Whi : region_wf ρ (hiz_region R xh)).
    { unfold region_wf. rewrite Ebh. cbn [hiz_region rg_n rg_d rg_kind]. rewrite Hnh. repeat split; try lia. intros a0 i0 E. discriminate E. }
    split.
    + change [buf_region R x nb; hiz_region R xh] with ([buf_region R x nb] ++ [hiz_region R xh]). rewrite app_assoc.
      apply regions_ok_snoc; [apply regions_ok_snoc | exact Whi |].
      * apply (regions_ok_replace_sub ρ A i R); [exact Hok | exact Hi | exact Wlo | unfold rbase, lo_region; cbn [rg_ts rg_bo]; lia |].
        unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
      * exact Wbuf.
      * apply Forall_replace_in.
        -- intros j0 Rj Hj Hne. pose proof (regions_ok_disj ρ A j0 i Rj R Hok Hj Hi ltac:(lia)) as Hdis.
           unfold rdisj in *. rewrite Ebb. cbn [buf_region rg_n]. rewrite Hnb. lia.
        -- unfold rdisj. rewrite Ebb. unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
      * apply Forall_app. split; [apply Forall_replace_in | constructor; [|constructor]].
        -- intros j0 Rj Hj Hne. pose proof (regions_ok_disj ρ A j0 i Rj R Hok Hj Hi ltac:(lia)) as Hdis.
           unfold rdisj in *. rewrite Ebh. cbn [hiz_region rg_n]. rewrite Hnh. lia.
        -- unfold rdisj. rewrite Ebh. unfold rbase, lo_region in *. cbn [rg_ts rg_bo rg_n]. lia.
        -- unfold rdisj. rewrite Ebh, Ebb. cbn [buf_region rg_n]. rewrite Hnb. lia.
    + apply Forall_app. split.
      * apply Forall_replace_nth'; [exact Hoth| |destruct (nth_error_Some A i) as [Hs _]; apply Hs; rewrite Hi; discriminate].
        rewrite RRegion_ne by (unfold is_entry, lo_region; cbn [rg_kind]; rewrite Ek; reflexivity).
        intros y Hy. cbn [lo_region rg_n] in Hy. replace (rbase ρ (lo_region R x)) with (rbase ρ R) by reflexivity.
        replace (rbyte segs (lo_region R x) y) with (rbyte segs R y) by reflexivity.
        replace (rk_writable (rg_kind (lo_region R x))) with (rk_writable (rg_kind R)) by reflexivity.
        apply Hold; lia.
      * constructor; [|constructor; [|constructor]].
        -- rewrite RRegion_ne by reflexivity.
           apply (RRegion0_unk ρ m m' R (buf_region R x nb) (to_Z x) HRR Hwr Hg Ebb ltac:(lia)); [cbn [buf_region rg_n]; rewrite Hnb; lia | reflexivity|].
           intros y _. unfold rbyte, get_cell_opt, buf_region. cbn [rg_d rg_cells]. rewrite iget_empty. reflexivity.
        -- rewrite RRegion_ne by reflexivity. intros y Hy. cbn [hiz_region rg_n] in Hy. rewrite Hnh in Hy. rewrite Ebh.
           pose proof (to_Z_bounded y) as Hyb. change wB with (2^63) in Hyb.
           rewrite (rbyte_hiz R xh y Ek Hd44 Hd H47 ltac:(lia) Hal ltac:(lia)).
           assert (Hsum : to_Z (xh + y)%uint63 = to_Z xh + to_Z y) by (rewrite add_spec; apply Z.mod_small; change wB with (2^63); lia).
           destruct (Hold (xh + y)%uint63 ltac:(rewrite Hsum; lia) ltac:(right; rewrite Hsum; lia)) as [X1 X2].
           rewrite Hsum, Z.add_assoc in X1, X2. split; [exact X1 | intros _; exact (X2 Hwr)].
Qed.

Lemma forget_shadow1 (A A' : list region) (v : xv) (n : Z) : a_forget A v n = Some A' ->
  forall X, In X A' -> is_shadow X = true -> In X A.
Proof.
  intros H X HX Hs. destruct (a_forget_inv A A' v n H) as (ts & o & i & R & x & _ & _ & _ & Hcase).
  destruct Hcase as [[Ek EA]|[[Ek [_ EA]]|[[Ek [_ EA]]|[[j [Ek EA]]|[[j [Ek [_ EA]]]|[[Ek [_ [_ EA]]]|[Ek [_ [_ EA]]]]]]]]]; subst A'.
  7: { apply in_app_or in HX as [HX|[E|[E|[]]]]; [|subst X; discriminate|subst X; discriminate].
       destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; unfold is_shadow, lo_region in Hs; cbn [rg_kind] in Hs; rewrite Ek in Hs; discriminate | exact E]. }
  6: { apply in_app_or in HX as [HX|[E|[]]]; [|subst X; discriminate].
       destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; discriminate | exact E]. }
  - destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; unfold is_shadow, with_cells in Hs; cbn [rg_kind] in Hs; rewrite Ek in Hs; discriminate | exact E].
  - destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; discriminate | exact E].
  - apply in_app_or in HX as [HX|[E|[]]]; [|subst X; discriminate].
    destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; unfold is_shadow, lo_region in Hs; cbn [rg_kind] in Hs; rewrite Ek in Hs; discriminate | exact E].
  - destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; unfold is_shadow, havoc_cells, with_cells in Hs; cbn [rg_kind] in Hs; rewrite Ek in Hs; discriminate | exact E].
  - apply in_app_or in HX as [HX|[E|[E|[]]]]; [|subst X; discriminate|subst X; discriminate].
    destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; unfold is_shadow, lo_region in Hs; cbn [rg_kind] in Hs; rewrite Ek in Hs; discriminate | exact E].
Qed.

Lemma forget_shadow2 (A A' : list region) (v : xv) (n : Z) : a_forget A v n = Some A' ->
  forall X, In X A -> is_shadow X = true -> In X A'.
Proof.
  intros H X HX Hs. destruct (a_forget_inv A A' v n H) as (ts & o & i & R & x & _ & _ & Ef & Hcase).
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi _]]. rewrite Nat.sub_0_r in Hi.
  assert (Hne : X <> R).
  { intros ->. destruct Hcase as [[Ek _]|[[Ek _]|[[Ek _]|[[j [Ek _]]|[[j [Ek _]]|[[Ek _]|[Ek _]]]]]]]; unfold is_shadow in Hs; rewrite Ek in Hs; discriminate. }
  destruct Hcase as [[Ek EA]|[[Ek [_ EA]]|[[Ek [_ EA]]|[[j [Ek EA]]|[[j [Ek [_ EA]]]|[[Ek [_ [_ EA]]]|[Ek [_ [_ EA]]]]]]]]]; subst A';
    try exact (in_replace_nth_keep A i R _ X Hi HX Hne).
  all: apply in_or_app; left; exact (in_replace_nth_keep A i R _ X Hi HX Hne).
Qed.

Lemma forget_mark (A A' : list region) (v : xv) (n : Z) : a_forget A v n = Some A' ->
  forall X, In X A -> to_Z (rg_n X) = 0 -> exists X', In X' A' /\ to_Z (rg_n X') = 0.
Proof.
  intros H X HX Hn0. destruct (a_forget_inv A A' v n H) as (ts & o & i & R & x & _ & Hn & Ef & Hcase).
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  assert (Hne : X <> R).
  { intros ->. destruct (roff_spec R ts o (of_Z n) x ltac:(rewrite phi_of_Z_n by lia; lia) Hr) as (_ & _ & _ & Hfit).
    rewrite phi_of_Z_n in Hfit by lia. pose proof (to_Z_bounded x). lia. }
  exists X. split; [|exact Hn0].
  destruct Hcase as [[Ek EA]|[[Ek [_ EA]]|[[Ek [_ EA]]|[[j [Ek EA]]|[[j [Ek [_ EA]]]|[[Ek [_ [_ EA]]]|[Ek [_ [_ EA]]]]]]]]]; subst A';
    try exact (in_replace_nth_keep A i R _ X Hi HX Hne).
  all: apply in_or_app; left; exact (in_replace_nth_keep A i R _ X Hi HX Hne).
Qed.

Lemma forget_sub (ρ : valuation) (A A' : list region) (m : word -> option byte) (v : xv) (n : Z) :
  RMem segs ρ A m -> a_forget A v n = Some A' ->
  forall X, In X A' -> is_shadow X = false -> exists Y, In Y A /\ is_shadow Y = false /\ (forall z, in_rg ρ X z -> in_rg ρ Y z).
Proof.
  intros [Hok _] H X HX Hs. destruct (a_forget_inv A A' v n H) as (ts & o & i & R & x & _ & Hn & Ef & Hcase).
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf. pose proof Hwf as [Hw1 [H47 _]].
  destruct (roff_spec R ts o (of_Z n) x ltac:(rewrite phi_of_Z_n by lia; lia) Hr) as (_ & _ & _ & Hfit).
  rewrite phi_of_Z_n in Hfit by lia. pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hsr. fold (rbase ρ R) in Hsr.
  assert (HRin : In R A) by (apply nth_error_In with i; exact Hi).
  assert (HRs : is_shadow R = false) by (destruct Hcase as [[Ek _]|[[Ek _]|[[Ek _]|[[j [Ek _]]|[[j [Ek _]]|[[Ek _]|[Ek _]]]]]]]; unfold is_shadow; rewrite Ek; reflexivity).
  assert (Hself : forall X', rbase ρ X' = rbase ρ R -> to_Z (rg_n X') <= to_Z (rg_n R) ->
            exists Y, In Y A /\ is_shadow Y = false /\ (forall z, in_rg ρ X' z -> in_rg ρ Y z)).
  { intros X' E1 E2. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *. lia. }
  destruct Hcase as [[Ek EA]|[[Ek [_ EA]]|[[Ek [Ex EA]]|[[j [Ek EA]]|[[j [Ek [Hcv EA]]]|[[Ek [Ex [Hzs EA]]]|[Ek [Ex [Hzs EA]]]]]]]]]; subst A'.
  - destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; apply Hself; reflexivity|]. exists X. split; [exact E|]. split; [exact Hs | exact (fun z Hz => Hz)].
  - destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; apply Hself; reflexivity|]. exists X. split; [exact E|]. split; [exact Hs | exact (fun z Hz => Hz)].
  - apply in_app_or in HX as [HX|[E|[]]].
    + destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; apply Hself; [reflexivity | cbn [lo_region rg_n]; lia]|].
      exists X. split; [exact E|]. split; [exact Hs | exact (fun z Hz => Hz)].
    + subst X. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *.
      rewrite (rbase_mid ρ R x ltac:(unfold two64 in *; lia) ltac:(lia)) in Hz. cbn [mid_region rg_n] in Hz.
      rewrite sub_spec, Z.mod_small in Hz by (pose proof (to_Z_bounded (rg_n R)); change wB with (2^63) in *; lia). lia.
  - destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; apply Hself; reflexivity|]. exists X. split; [exact E|]. split; [exact Hs | exact (fun z Hz => Hz)].
  - destruct (carve_ok_spec R x n Hn H47 Hcv) as (Hx0 & Hxh & Hlt & Hal & Hnz & Hnb).
    pose proof (to_Z_bounded (rg_n R)) as HnRb. change wB with (2^63) in HnRb.
    apply in_app_or in HX as [HX|[E|[E|[]]]].
    + destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; apply Hself; [reflexivity | cbn [lo_region rg_n]; lia]|].
      exists X. split; [exact E|]. split; [exact Hs | exact (fun z Hz => Hz)].
    + subst X. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *.
      rewrite (rbase_buf ρ R x (al8 (x + of_Z n) - x)%uint63 ltac:(unfold two64 in *; lia) ltac:(lia)) in Hz. cbn [buf_region rg_n] in Hz. rewrite Hnb in Hz. lia.
    + subst X. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *.
      rewrite (rbase_hi ρ R (al8 (x + of_Z n)) ltac:(unfold two64 in *; lia) ltac:(lia)) in Hz. cbn [hi_region rg_n] in Hz.
      rewrite sub_spec, Z.mod_small in Hz by (change wB with (2^63); lia). lia.
  - destruct (zsplit_ok_spec R x n Hn H47 Hzs) as (Hxh & Hlt & Hal & Hnb).
    assert (Hx00 : to_Z x = 0) by (rewrite Ex; reflexivity).
    pose proof (to_Z_bounded (rg_n R)) as HnRb. change wB with (2^63) in HnRb.
    apply in_app_or in HX as [HX|[E|[]]].
    + destruct (in_replace_nth A i _ X HX) as [E|E]; [|exists X; split; [exact E|]; split; [exact Hs | exact (fun z Hz => Hz)]].
      subst X. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *.
      rewrite (rbase_buf ρ R x (al8 (x + of_Z n) - x)%uint63 ltac:(unfold two64 in *; lia) ltac:(lia)) in Hz. cbn [buf_region rg_n] in Hz. rewrite Hnb in Hz. lia.
    + subst X. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *.
      rewrite (rbase_mid ρ R (al8 (x + of_Z n)) ltac:(unfold two64 in *; lia) ltac:(lia) : rbase ρ (hiz_region R (al8 (x + of_Z n))) = _) in Hz. cbn [hiz_region rg_n] in Hz.
      rewrite sub_spec, Z.mod_small in Hz by (change wB with (2^63); lia). lia.
  - destruct (zsplit_ok_spec R x n Hn H47 Hzs) as (Hxh & Hlt & Hal & Hnb).
    assert (Hx0 : 0 < to_Z x) by (assert (to_Z x <> 0) by (intros E; apply Ex; apply to_Z_inj; exact E); lia).
    pose proof (to_Z_bounded (rg_n R)) as HnRb. change wB with (2^63) in HnRb.
    apply in_app_or in HX as [HX|[E|[E|[]]]].
    + destruct (in_replace_nth A i _ X HX) as [E|E]; [subst X; apply Hself; [reflexivity | cbn [lo_region rg_n]; lia]|].
      exists X. split; [exact E|]. split; [exact Hs | exact (fun z Hz => Hz)].
    + subst X. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *.
      rewrite (rbase_buf ρ R x (al8 (x + of_Z n) - x)%uint63 ltac:(unfold two64 in *; lia) ltac:(lia)) in Hz. cbn [buf_region rg_n] in Hz. rewrite Hnb in Hz. lia.
    + subst X. exists R. split; [exact HRin|]. split; [exact HRs|]. intros z Hz. unfold in_rg in *.
      rewrite (rbase_mid ρ R (al8 (x + of_Z n)) ltac:(unfold two64 in *; lia) ltac:(lia) : rbase ρ (hiz_region R (al8 (x + of_Z n))) = _) in Hz. cbn [hiz_region rg_n] in Hz.
      rewrite sub_spec, Z.mod_small in Hz by (change wB with (2^63); lia). lia.
Qed.

Lemma hs_ok_forget' (ρ : valuation) (A A' : list region) (m m' : word -> option byte) (v : xv) (n : Z) :
  RMem segs ρ A m -> a_forget A v n = Some A' -> (hs_old ρ A m -> forall z, in_ss z -> m' (wz z) = m (wz z)) -> hs_ok ρ A m -> hs_ok ρ A' m'.
Proof.
  intros HM H Hz0 [Hpl|Hold].
  { left. destruct Hpl as [[R0 [HR0 Hn0]] Hno]. split.
    - destruct (forget_mark A A' v n H R0 HR0 Hn0) as [R1 [HR1 Hn1]]. exists R1. split; assumption.
    - intros X HX. destruct (is_shadow X) eqn:Es; [|reflexivity]. rewrite (Hno X (forget_shadow1 A A' v n H X HX Es)) in Es. discriminate Es. }
  pose proof (Hz0 Hold) as Hz. destruct Hold as [P1 [P2 [P3 P4]]]. right. split; [|split; [|split]].
  - intros X HX Hs z HzX. destruct (forget_sub ρ A A' m v n HM H X HX Hs) as [Y [HY [HYs Hsub]]]. exact (P1 Y HY HYs z (Hsub z HzX)).
  - intros z Hss Hout. rewrite (Hz z Hss). apply (P2 z Hss). intros R HR Hs. apply (Hout R (forget_shadow2 A A' v n H R HR Hs) Hs).
  - destruct P3 as [X|X]; [left | right]; intros z Hzr; rewrite Hz by (left; exact Hzr); exact (X z Hzr).
  - destruct P4 as [X|X]; [left | right]; intros z Hzr; rewrite Hz by (right; exact Hzr); exact (X z Hzr).
Qed.

Lemma comp_inv_forget (ρ : valuation) (A A' : list region) (model : Model) (v : xv) (n : Z) :
  a_forget A v n = Some A' -> comp_inv segs ρ A model -> comp_inv segs ρ A' model.
Proof. intros H Hc R HR Hs. exact (Hc R (forget_shadow1 A A' v n H R HR Hs) Hs). Qed.

Lemma na_ok_forget (ρ : valuation) (A A' : list region) (model : Model) (m : word -> option byte) (v : xv) (n : Z) :
  a_forget A v n = Some A' -> na_ok segs ρ A model m -> na_ok segs ρ A' model m.
Proof. intros H [N1 [N2 N3]]. split; [exact N1|]. split; [exact N2|]. intros R HR Hs. exact (N3 R (forget_shadow1 A A' v n H R HR Hs) Hs). Qed.

Lemma a_forget_range (ρ : valuation) (A A' : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : Z) :
  RMem segs ρ A m -> xv_val ρ v a -> a_forget A v n = Some A' ->
  exists R, In R A /\ is_shadow R = false /\ rbase ρ R <= bv_unsigned a /\ bv_unsigned a + n <= rbase ρ R + to_Z (rg_n R)
    /\ store_ok segs m a (Z.to_nat n) = true /\ 1 <= n < 1099511627776.
Proof.
  intros [Hok HR] Hv H. destruct (a_forget_inv A A' v n H) as (ts & o & i & R & x & Ea & Hn & Ef & Hcase).
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf. pose proof (Forall_nth _ A i R HR Hi) as HRR.
  pose proof (roff_ne R ts o _ x Hr) as Hne0. rewrite (RRegion_ne segs ρ m R Hne0) in HRR.
  assert (Hav : bv_unsigned a = smod ρ ts o).
  { destruct v; cbn [xaddr] in Ea; try discriminate; injection Ea as <- <-; cbn [xv_val] in Hv.
    - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
    - exact Hv. }
  assert (Hnz : to_Z (of_Z n) = n) by (apply phi_of_Z_n; lia).
  destruct (roff_addr ρ R ts o (of_Z n) x a ltac:(rewrite Hnz; lia) Hwf Hav Hr) as [Eaddr Hfit]. rewrite Hnz in Hfit.
  pose proof Hwf as [Hw1 [H47 _]]. pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hsr. fold (rbase ρ R) in Hsr.
  assert (Hwr : rk_writable (rg_kind R) = true) by (destruct Hcase as [[E _]|[[E _]|[[E _]|[[j [E _]]|[[j [E _]]|[[E _]|[E _]]]]]]]; rewrite E; reflexivity).
  exists R. split; [apply nth_error_In with i; exact Hi|].
  split; [destruct Hcase as [[E _]|[[E _]|[[E _]|[[j [E _]]|[[j [E _]]|[[E _]|[E _]]]]]]]; unfold is_shadow; rewrite E; reflexivity|].
  split; [lia|]. split; [lia|]. split; [|exact Hn].
  assert (Ha : a = wz (rbase ρ R + to_Z x)) by (apply bv_eq; rewrite u_wz; [lia | unfold two64 in *; lia]). rewrite Ha.
  apply store_ok_range; try assumption. lia.
Qed.

End Forget.
