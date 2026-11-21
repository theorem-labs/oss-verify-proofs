(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeB2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeB2.RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Tail.
Variable t : tree_id.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.

Definition HM : Z := 574 - 2 * L.
Definition tail (i : Z) : Prop := HM <= i < 573.
Definition nd (i : Z) : Z := arr_get HPf i.
Definition leafb (i : Z) : bool := nd i <? E.

Lemma ML_range : 7 <= ML <= 15 /\ E <= 2 ^ ML.
Proof. destruct t; cbn -[Z.pow]; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia. Qed.

Lemma E_range : 19 <= E <= 286.
Proof. pose proof (elems_range t). lia. Qed.

Lemma HM_range : 2 <= HM <= 570.
Proof. unfold HM. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR). pose proof E_range. lia. Qed.

Fixpoint find_pos (k : nat) (u : Z) : Z :=
  match k with
  | O => HM
  | S k' => let i := 572 - Z.of_nat k' in if arr_get HPf i =? u then
              match k' with O => i | _ => let j := find_pos k' u in if (arr_get HPf j =? u) && (j <? i) then j else i end
            else find_pos k' u
  end.

Fixpoint scan_pos (k : nat) (u : Z) : Z :=
  match k with
  | O => HM
  | S k' => if arr_get HPf (HM + Z.of_nat k') =? u then HM + Z.of_nat k' else scan_pos k' u
  end.
Definition posof (u : Z) : Z := scan_pos (Z.to_nat (573 - HM)) u.

Lemma scan_pos_spec : forall k u, (exists i, HM <= i < HM + Z.of_nat k /\ nd i = u) ->
  HM <= scan_pos k u < HM + Z.of_nat k /\ nd (scan_pos k u) = u.
Proof.
  induction k as [|k IH]; intros u Hex; cbn [scan_pos].
  - destruct Hex as (i & Hi & _). lia.
  - unfold nd in *. destruct (Z.eqb_spec (arr_get HPf (HM + Z.of_nat k)) u) as [Eq|Ne].
    + split; [lia | exact Eq].
    + destruct Hex as (i & Hi & Ei).
      destruct (IH u) as [A B]; [| split; [lia | exact B]].
      exists i. split; [|exact Ei]. destruct (Z.eq_dec i (HM + Z.of_nat k)) as [->|]; [congruence | lia].
Qed.

Lemma posof_spec : forall u, Vj t FC2 (L - 1) u -> tail (posof u) /\ nd (posof u) = u.
Proof.
  intros u Hu. unfold posof, tail. pose proof HM_range as R.
  destruct (hr_cov _ _ _ _ _ _ _ _ _ HR u Hu) as (i & Hi & Ei).
  destruct (scan_pos_spec (Z.to_nat (573 - HM)) u) as [A B].
  { exists i. unfold HM in *. split; [lia | exact Ei]. }
  unfold HM in *. split; [lia | exact B].
Qed.

Lemma posof_nd : forall i, tail i -> posof (nd i) = i.
Proof.
  intros i Hi.
  assert (Vi : Vj t FC2 (L - 1) (nd i)).
  { destruct (Z.eq_dec i HM) as [->|N].
    - unfold nd, HM. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR). unfold Vj. right. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR). lia.
    - apply (hr_tail _ _ _ _ _ _ _ _ _ HR). unfold tail, HM in *. lia. }
  destruct (posof_spec (nd i) Vi) as [A B].
  apply (hr_inj _ _ _ _ _ _ _ _ _ HR); unfold tail, HM in *; [lia | lia | exact B].
Qed.

Lemma nd_cases : forall i, tail i ->
  (0 <= nd i < E /\ arr_get FC2 (nd i) <> 0) \/ (E <= nd i < E + L - 1).
Proof.
  intros i Hi. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR).
  destruct (Z.eq_dec i HM) as [->|N].
  - unfold nd, HM. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR). right. lia.
  - pose proof (hr_tail _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail, HM in *; lia)) as V. unfold Vj, V0, Vscan in V. unfold nd. lia.
Qed.

Definition dadid (i : Z) : Z := E + (572 - i) / 2.
Definition par (i : Z) : Z := posof (dadid i).

Lemma dadid_range : forall i, HM < i < 573 -> E <= dadid i < E + L - 1 /\ 2 * (dadid i - E) <= 572 - i <= 2 * (dadid i - E) + 1.
Proof.
  intros i Hi. unfold dadid, HM in *. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR).
  assert ((572 - i) / 2 < L - 1) by (apply Z.div_lt_upper_bound; lia).
  assert (0 <= (572 - i) / 2) by (apply Z.div_pos; lia).
  pose proof (Z.div_mod (572 - i) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (572 - i) 2 ltac:(lia)). lia.
Qed.

Lemma par_spec : forall i, HM < i < 573 -> tail (par i) /\ par i < i /\ nd (par i) = dadid i /\ E <= nd (par i).
Proof.
  intros i Hi. pose proof (dadid_range i Hi) as [D1 D2]. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR).
  destruct (posof_spec (dadid i)) as [A B]; [unfold Vj; right; lia|].
  unfold par. split; [exact A|]. split; [| split; [exact B | rewrite B; lia]].
  destruct (Z.eq_dec (posof (dadid i)) HM) as [->|N]; [unfold tail, HM in *; lia|].
  pose proof (hr_old _ _ _ _ _ _ _ _ _ HR (posof (dadid i)) ltac:(unfold tail, HM in *; lia)) as O.
  unfold nd in B. rewrite B in O. specialize (O ltac:(lia)).
  set (d := dadid i) in *. assert (Ed : d = E + (572 - i) / 2) by reflexivity.
  destruct (Z_lt_le_dec (posof d) i) as [|C]; [assumption|]. exfalso.
  assert ((572 - posof d) / 2 <= (572 - i) / 2) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma dad_cell : forall i, HM < i < 573 -> arr_get DLf (nd i) = nd (par i).
Proof.
  intros i Hi. destruct (par_spec i Hi) as (_ & _ & B & _). rewrite B. unfold nd, dadid.
  apply (hr_dad _ _ _ _ _ _ _ _ _ HR). unfold HM in Hi. lia.
Qed.

Lemma par_of_child : forall i p, HM < i < 573 -> tail p -> par i = p <-> nd p = dadid i.
Proof.
  intros i p Hi Hp. destruct (par_spec i Hi) as (A & _ & B & _). split.
  - intros <-. exact B.
  - intros Ep. apply (hr_inj _ _ _ _ _ _ _ _ _ HR); unfold tail, HM in *; [lia | lia |]. unfold nd in *. rewrite B, Ep. reflexivity.
Qed.

Lemma children_leaf : forall p i, tail p -> nd p < E -> HM < i < 573 -> par i <> p.
Proof.
  intros p i Hp Hl Hi E1. pose proof (proj1 (par_of_child i p Hi Hp) E1). pose proof (dadid_range i Hi). lia.
Qed.

Lemma children_internal : forall p i, tail p -> E <= nd p -> HM < i < 573 ->
  (par i = p <-> (i = 572 - 2 * (nd p - E) \/ i = 571 - 2 * (nd p - E))).
Proof.
  intros p i Hp Hint Hi. rewrite (par_of_child i p Hi Hp). unfold dadid.
  pose proof (Z.div_mod (572 - i) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (572 - i) 2 ltac:(lia)).
  split; [intros Ep | intros [-> | ->]]; [lia | |].
  - replace (572 - (572 - 2 * (nd p - E))) with ((nd p - E) * 2) by lia. rewrite Z.div_mul by lia. lia.
  - replace (572 - (571 - 2 * (nd p - E))) with (1 + (nd p - E) * 2) by lia. rewrite Z.div_add by lia. change (1 / 2) with 0. lia.
Qed.

Lemma children_pos : forall p, tail p -> E <= nd p ->
  HM < 571 - 2 * (nd p - E) /\ 572 - 2 * (nd p - E) < 573 /\ p < 571 - 2 * (nd p - E).
Proof.
  intros p Hp Hint. pose proof (nd_cases p Hp) as C. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR).
  destruct C as [[A0 B0]|C]; [lia|].
  assert (HMlt : HM < 571 - 2 * (nd p - E)) by (unfold HM; lia).
  split; [exact HMlt|]. split; [lia|].
  destruct (par_spec (571 - 2 * (nd p - E)) ltac:(lia)) as (A & B & _).
  pose proof (proj2 (children_internal p (571 - 2 * (nd p - E)) Hp Hint ltac:(lia)) (or_intror eq_refl)) as P.
  rewrite P in B. exact B.
Qed.

Fixpoint Cf (f : nat) (i : Z) : Z :=
  match f with
  | O => 0
  | S f' => if i <=? HM then 0 else Z.min (Cf f' (par i) + 1) ML
  end.
Definition C (i : Z) : Z := Cf 573 i.

Lemma Cf_stable : forall f g i, tail i -> (Z.to_nat (i - HM) < f)%nat -> (Z.to_nat (i - HM) < g)%nat -> Cf f i = Cf g i.
Proof.
  induction f as [|f IH]; intros g i Hi Hf Hg; [lia|].
  destruct g as [|g]; [lia|]. cbn [Cf].
  destruct (Z.leb_spec i HM) as [Le|Gt]; [reflexivity|].
  destruct (par_spec i ltac:(unfold tail in Hi; lia)) as (A & B & _). pose proof HM_range.
  rewrite (IH g (par i) A); [reflexivity | unfold tail in *; lia | unfold tail in *; lia].
Qed.

Lemma Cf_S : forall f i, Cf (S f) i = if i <=? HM then 0 else Z.min (Cf f (par i) + 1) ML.
Proof. reflexivity. Qed.

Lemma C_root : C HM = 0.
Proof. unfold C. change 573%nat with (S 572). rewrite Cf_S. rewrite Z.leb_refl. reflexivity. Qed.

Lemma C_step : forall i, HM < i < 573 -> C i = Z.min (C (par i) + 1) ML.
Proof.
  intros i Hi. unfold C. change 573%nat with (S 572). rewrite Cf_S.
  replace (i <=? HM) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (par_spec i Hi) as (A & B & _). pose proof HM_range.
  rewrite (Cf_stable 572 573 (par i) A); [reflexivity | unfold tail in *; lia | unfold tail in *; lia].
Qed.

Lemma C_range : forall i, tail i -> 0 <= C i <= ML.
Proof.
  intros i Hi. pose proof ML_range. destruct (Z.eq_dec i HM) as [->|N]; [rewrite C_root; lia|].
  rewrite C_step by (unfold tail in Hi; lia).
  assert (GEN : forall f z, 0 <= Cf f z).
  { induction f as [|f IH]; intros z; [cbn; lia|]. rewrite Cf_S.
    destruct (z <=? HM); [lia|]. pose proof (IH (par z)). lia. }
  pose proof (GEN 573%nat (par i)). unfold C in *. lia.
Qed.

Lemma C_pos : forall i, HM < i < 573 -> 1 <= C i.
Proof.
  intros i Hi. rewrite C_step by exact Hi. destruct (par_spec i Hi) as (A & _). pose proof (C_range _ A). pose proof ML_range. lia.
Qed.



Definition tid (u : Z) : bool := arr_get HPf (posof u) =? u.

Lemma posof_range : forall u, HM <= posof u < 573.
Proof.
  intros u. unfold posof. pose proof HM_range.
  assert (G : forall k, HM <= scan_pos k u <= HM + Z.of_nat k /\ (0 < Z.of_nat k -> scan_pos k u < HM + Z.of_nat k)).
  { induction k as [|k IH]; cbn [scan_pos]; [lia|]. destruct (_ =? _); [lia|]. destruct IH. lia. }
  destruct (G (Z.to_nat (573 - HM))) as [A B]. rewrite Z2Nat.id in A, B by lia. lia.
Qed.

Lemma tid_true : forall u, tid u = true <-> (tail (posof u) /\ nd (posof u) = u).
Proof.
  intros u. unfold tid, nd, tail. rewrite Z.eqb_eq. pose proof (posof_range u). tauto.
Qed.

Lemma tid_nd : forall i, tail i -> tid (nd i) = true /\ posof (nd i) = i.
Proof. intros i Hi. rewrite (posof_nd i Hi). split; [| reflexivity]. unfold tid. rewrite (posof_nd i Hi). apply Z.eqb_refl. Qed.

Definition dl_at (h : Z) (u : Z) : Z := if tid u && (posof u <? h) then C (posof u) else arr_get DLf u.

Lemma leaf_mc : forall i, tail i -> (nd i < E <-> nd i <= mc).
Proof.
  intros i Hi. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR). destruct (nd_cases i Hi) as [[A B]|A]; [|lia].
  split; [intros _ | lia]. apply (hr_mc_max _ _ _ _ _ _ _ _ _ HR); assumption.
Qed.

Definition w_opt (i : Z) : Z := zind (leafb i) * (arr_get FC2 (nd i) * (C i + xbits t (nd i))).
Definition w_stat (i : Z) : Z := zind (leafb i) * (arr_get FC2 (nd i) * (stree_Len t (nd i) + xbits t (nd i))).
Definition w_cnt (b : Z) (i : Z) : Z := zind (leafb i && (C i =? b)).
Definition w_ovf (i : Z) : Z := zind (C (par i) =? ML).

Record L1I (s : deflate_state) (BC0 : arr) (OL SL : Z) (h : Z) (X : deflate_state) (ovf : Z) : Prop := {
  l1_h : HM + 1 <= h <= 573;
  l1_X : exists DL BC OL' SL',
           X = bt_upd s t FCf DL HPf 1 HM DPf BC OL' SL' mc
           /\ (forall u, arr_get DL u = dl_at h u) /\ arr_len DL = tsize t
           /\ (forall b, 0 <= b < 16 -> arr_get BC b = zsum (w_cnt b) (HM + 1) (Z.to_nat (h - HM - 1))) /\ arr_len BC = 16
           /\ OL' = wrap64 (OL + zsum w_opt (HM + 1) (Z.to_nat (h - HM - 1)))
           /\ SL' = (if stree_has t then wrap64 (SL + zsum w_stat (HM + 1) (Z.to_nat (h - HM - 1))) else SL);
  l1_ovf : ovf = zsum w_ovf (HM + 1) (Z.to_nat (h - HM - 1)) }.


Lemma cnt_bound : forall b lo n, 0 <= zsum (w_cnt b) lo n <= Z.of_nat n.
Proof.
  intros b lo n. induction n as [|n IH]; [cbn; lia|]. rewrite zsum_snoc. unfold w_cnt at 2. pose proof (zind_le1 (leafb (lo + Z.of_nat n) && (C (lo + Z.of_nat n) =? b))). unfold w_cnt in IH |- *. lia.
Qed.

Lemma ovf_bound : forall lo n, 0 <= zsum w_ovf lo n <= Z.of_nat n.
Proof.
  intros lo n. induction n as [|n IH]; [cbn; lia|]. rewrite zsum_snoc. unfold w_ovf in *. pose proof (zind_le1 (C (par (lo + Z.of_nat n)) =? ML)). lia.
Qed.

Lemma L1_step : forall s BC0 OL SL h X ovf,
  L1I s BC0 OL SL h X ovf -> h < 573 ->
  L1I s BC0 OL SL (h + 1) (fst (GB1 t mc X h ovf)) (snd (GB1 t mc X h ovf))
  /\ 0 <= Dad X t (heap_get X h) < tsize t.
Proof.
  intros s BC0 OL SL h X ovf [Hh (DL & BC & OL' & SL' & -> & HDL & LDL & HBC & LBC & HOL & HSL) Hovf] Hlt.
  pose proof HM_range as RHM. pose proof ML_range as RML. pose proof E_range as RE. pose proof (elems_range t) as RE2.
  pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL.
  assert (Th : tail h) by (unfold tail; lia).
  destruct (par_spec h ltac:(lia)) as (Tp & Pp & NDp & Ip).
  destruct (tid_nd h Th) as [TIh PSh]. destruct (tid_nd (par h) Tp) as [TIp PSp].
  assert (Rn : arr_get HPf h = nd h) by reflexivity.
  assert (Rdad : arr_get DL (nd h) = nd (par h)).
  { rewrite HDL. unfold dl_at. rewrite TIh, PSh. replace (h <? h) with false by (symmetry; apply Z.ltb_irrefl). cbn [andb]. apply dad_cell. lia. }
  assert (Rlen : arr_get DL (nd (par h)) = C (par h)).
  { rewrite HDL. unfold dl_at. rewrite TIp, PSp. replace (par h <? h) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  pose proof (C_step h ltac:(lia)) as Ch. pose proof (C_range (par h) Tp) as CRp. pose proof (C_range h Th) as CRh.
  split.
  2: { unfold Dad, heap_get. autorewrite with btupd. rewrite Rn, Rdad. destruct (nd_cases (par h) Tp); lia. }
  rewrite (GB1_flat t mc s FCf DL HPf 1 HM DPf BC OL' SL' h ovf). cbv zeta. rewrite Rn, Rdad, Rlen.
  assert (Ebits : (if ML <? C (par h) + 1 then ML else C (par h) + 1) = C h) by (rewrite Ch; destruct (Z.ltb_spec ML (C (par h) + 1)); lia).
  rewrite Ebits.
  assert (Eovf : (if ML <? C (par h) + 1 then ovf + 1 else ovf) = ovf + w_ovf h).
  { unfold w_ovf, zind. destruct (Z.ltb_spec ML (C (par h) + 1)); destruct (Z.eqb_spec (C (par h)) ML); lia. }
  rewrite Eovf.
  assert (HDL' : forall u, arr_get (arr_set DL (nd h) (wrap16 (C h))) u = dl_at (h + 1) u).
  { intros u. rewrite arr_get_set. unfold arr_inb. rewrite LDL. rewrite wrap16_id by lia.
    destruct (Z.eqb_spec (nd h) u) as [<-|Nu].
    - replace ((0 <=? nd h) && (nd h <? tsize t)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; destruct (nd_cases h Th); lia).
      cbn [andb]. unfold dl_at. rewrite TIh, PSh. replace (h <? h + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - cbn [andb]. rewrite HDL. unfold dl_at. destruct (tid u) eqn:Tu; cbn [andb]; [|reflexivity].
      apply tid_true in Tu. destruct Tu as [Tu Eu].
      assert (posof u <> h) by (intros Ep; apply Nu; rewrite <- Eu, Ep; reflexivity).
      destruct (Z.ltb_spec (posof u) h); destruct (Z.ltb_spec (posof u) (h + 1)); try reflexivity; lia. }
  assert (EN : Z.to_nat (h + 1 - HM - 1) = S (Z.to_nat (h - HM - 1))) by lia.
  assert (Epos : HM + 1 + Z.of_nat (Z.to_nat (h - HM - 1)) = h) by lia.
  destruct (Z.ltb_spec mc (nd h)) as [Cint|Cleaf].
  -
    assert (Lf : leafb h = false) by (unfold leafb; apply Z.ltb_ge; pose proof (leaf_mc h Th); lia).
    cbn [fst snd]. split; [lia| |].
    + exists (arr_set DL (nd h) (wrap16 (C h))), BC, OL', SL'. rewrite EN. split; [reflexivity|]. split; [exact HDL'|]. split; [rewrite arr_len_set; exact LDL|].
      split. { intros b Hb. rewrite HBC by exact Hb. rewrite zsum_snoc, Epos. unfold w_cnt at 3. rewrite Lf. cbn [andb zind]. lia. }
      split; [exact LBC|].
      split. { rewrite HOL. rewrite zsum_snoc, Epos. unfold w_opt at 3. rewrite Lf. cbn [zind]. rewrite Z.mul_0_l, Z.add_0_r. reflexivity. }
      rewrite HSL. rewrite zsum_snoc, Epos. unfold w_stat at 3. rewrite Lf. cbn [zind]. rewrite Z.mul_0_l, Z.add_0_r. reflexivity.
    + rewrite EN, zsum_snoc, Epos. lia.
  -
    assert (Lf : leafb h = true) by (unfold leafb; apply Z.ltb_lt; pose proof (leaf_mc h Th); lia).
    assert (Hfc : arr_get FCf (nd h) = arr_get FC2 (nd h)) by (apply (hr_fc _ _ _ _ _ _ _ _ _ HR); destruct (nd_cases h Th); lia).
    cbn [fst snd]. split; [lia| |].
    + exists (arr_set DL (nd h) (wrap16 (C h))), (arr_set BC (C h) (wrap16 (arr_get BC (C h) + 1))),
             (wrap64 (OL' + arr_get FCf (nd h) * (C h + xbits t (nd h)))),
             (if stree_has t then wrap64 (SL' + arr_get FCf (nd h) * (stree_Len t (nd h) + xbits t (nd h))) else SL').
      rewrite EN. split; [reflexivity|]. split; [exact HDL'|]. split; [rewrite arr_len_set; exact LDL|].
      split.
      { intros b Hb. rewrite arr_get_set. unfold arr_inb. rewrite LBC. pose proof (C_pos h ltac:(lia)).
        rewrite zsum_snoc, Epos. unfold w_cnt at 2. rewrite Lf. cbn [andb].
        destruct (Z.eqb_spec (C h) b) as [<-|Nb].
        - replace ((0 <=? C h) && (C h <? 16)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          cbn [andb]. rewrite HBC by lia. change (zind true) with 1.
          pose proof (cnt_bound (C h) (HM + 1) (Z.to_nat (h - HM - 1))). rewrite wrap16_id by lia. reflexivity.
        - cbn [andb]. rewrite HBC by lia. change (zind false) with 0. lia. }
      split; [rewrite arr_len_set; exact LBC|].
      split. { rewrite HOL, wrap64_add_l. rewrite zsum_snoc, Epos. unfold w_opt at 3. rewrite Lf, Hfc. cbn [zind]. f_equal. lia. }
      rewrite HSL. destruct (stree_has t); [|reflexivity]. rewrite wrap64_add_l. rewrite zsum_snoc, Epos. unfold w_stat at 3. rewrite Lf, Hfc. cbn [zind]. f_equal. lia.
    + rewrite EN, zsum_snoc, Epos. lia.
Qed.


Lemma L1_run : forall f s BC0 OL SL h X ovf,
  L1I s BC0 OL SL h X ovf -> (Z.of_nat f >= 573 - h) ->
  L1I s BC0 OL SL 573 (fst (gen_bitlen_loop1 f X t mc (sd_extra_base t) ML h ovf))
                      (snd (gen_bitlen_loop1 f X t mc (sd_extra_base t) ML h ovf))
  /\ gb1_ok t mc f X h ovf.
Proof.
  induction f as [|f IH]; intros s BC0 OL SL h X ovf HI Hf.
  - cbn [gen_bitlen_loop1 gb1_ok fst snd]. pose proof (l1_h _ _ _ _ _ _ _ HI). replace h with 573 in HI by lia. split; [exact HI | exact I].
  - rewrite GL1_step. cbn [gb1_ok]. unfold HEAP_SIZE. pose proof (l1_h _ _ _ _ _ _ _ HI).
    destruct (Z.ltb_spec h 573) as [Ch|Ch].
    + destruct (L1_step s BC0 OL SL h X ovf HI Ch) as [HI' HD].
      destruct (GB1 t mc X h ovf) as [X' o'] eqn:EG. cbn [fst snd] in HI'.
      destruct (IH s BC0 OL SL (h + 1) X' o' HI' ltac:(lia)) as [A B].
      split; [exact A|]. split; [exact HD | exact B].
    + replace h with 573 in HI by lia. cbn [fst snd]. split; [exact HI | exact I].
Qed.

Lemma L1_init : forall s BC OL SL,
  arr_len BC = 16 -> 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  L1I s BC OL SL (HM + 1)
      (bt_upd s t FCf (arr_set DLf (arr_get HPf HM) (wrap16 0)) HPf 1 HM DPf (arr_fill BC 0 (MAX_BITS + 1) 0) OL SL mc) 0.
Proof.
  intros s BC OL SL LBC HOL HSL. pose proof HM_range. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof E_range. pose proof (elems_range t).
  assert (Rr : 0 <= arr_get HPf HM < tsize t) by (unfold HM; rewrite (hr_root _ _ _ _ _ _ _ _ _ HR); lia).
  constructor; [lia| |].
  - exists (arr_set DLf (arr_get HPf HM) (wrap16 0)), (arr_fill BC 0 (MAX_BITS + 1) 0), OL, SL.
    replace (Z.to_nat (HM + 1 - HM - 1)) with 0%nat by lia. cbn [zsum]. rewrite !Z.add_0_r.
    split; [reflexivity|]. split.
    { intros u. rewrite arr_get_set. unfold arr_inb. rewrite (hr_ldl _ _ _ _ _ _ _ _ _ HR). change (wrap16 0) with 0.
      pose proof (tid_nd HM ltac:(unfold tail; lia)) as [T1 P1]. unfold nd in T1, P1.
      unfold dl_at. destruct (Z.eqb_spec (arr_get HPf HM) u) as [<-|Nu].
      + rewrite T1, P1. replace (HM <? HM + 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. rewrite C_root.
        replace ((0 <=? arr_get HPf HM) && (arr_get HPf HM <? tsize t)) with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
      + cbn [andb]. destruct (tid u) eqn:Tu; cbn [andb]; [|reflexivity].
        apply tid_true in Tu. destruct Tu as [Tu Eu]. unfold tail in Tu.
        destruct (Z.ltb_spec (posof u) (HM + 1)); [|reflexivity].
        exfalso. apply Nu. rewrite <- Eu. unfold nd. f_equal. lia. }
    split; [rewrite arr_len_set; apply (hr_ldl _ _ _ _ _ _ _ _ _ HR)|].
    split. { intros b Hb. unfold MAX_BITS. rewrite arr_get_fill. unfold arr_inb. rewrite LBC.
             replace ((0 <=? b) && (b <? 0 + Z.max 0 (15 + 1)) && ((0 <=? b) && (b <? 16))) with true; [reflexivity|].
             symmetry. rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia. }
    split; [unfold MAX_BITS; rewrite arr_len_fill; exact LBC|].
    split; [symmetry; apply wrap64_id; exact HOL|].
    destruct (stree_has t); [symmetry; apply wrap64_id; exact HSL | reflexivity].
  - replace (Z.to_nat (HM + 1 - HM - 1)) with 0%nat by lia. reflexivity.
Qed.





Definition cc (p h : Z) : Z := zsum (fun i => zind (par i =? p)) (HM + 1) (Z.to_nat (h - HM - 1)).
Definition pw (x : Z) : Z := 2 ^ (ML - Z.min x ML).
Definition psi_term (h p : Z) : Z := if leafb p then 2 ^ (ML - C p) else (2 - cc p h) * pw (C p + 1).
Definition Psi (h : Z) : Z := zsum (psi_term h) HM (Z.to_nat (h - HM)).
Definition NI (h : Z) : Z := zsum (fun i => zind (negb (leafb i) && (C i =? ML))) (HM + 1) (Z.to_nat (h - HM - 1)).

Lemma root_internal : leafb HM = false.
Proof.
  unfold leafb, nd, HM. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR). apply Z.ltb_ge. pose proof (hr_L _ _ _ _ _ _ _ _ _ HR). lia.
Qed.

Lemma cc_none : forall p h, HM <= h <= p + 1 -> h <= 573 -> cc p h = 0.
Proof.
  intros p h Hh H573. unfold cc. apply zsum_0. intros i Hi.
  destruct (Z.eqb_spec (par i) p) as [Ep|Np]; [|reflexivity]. exfalso.
  pose proof HM_range. destruct (par_spec i ltac:(lia)) as (_ & B & _). lia.
Qed.

Lemma Psi_init : Psi (HM + 1) = 2 ^ ML.
Proof.
  unfold Psi. replace (Z.to_nat (HM + 1 - HM)) with 1%nat by lia. cbn [zsum]. rewrite Z.add_0_r.
  unfold psi_term. rewrite root_internal. pose proof HM_range. rewrite cc_none by lia. rewrite C_root. unfold pw.
  pose proof ML_range. replace (Z.min (0 + 1) ML) with 1 by lia.
  replace (2 ^ ML) with (2 ^ (ML - 1 + 1)) by (f_equal; lia). rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.

Lemma Psi_step : forall h, HM + 1 <= h < 573 ->
  Psi (h + 1) = Psi h + zind (negb (leafb h) && (C h =? ML)).
Proof.
  intros h Hh. pose proof HM_range as RHM. pose proof ML_range as RML.
  destruct (par_spec h ltac:(lia)) as (Tp & Pp & NDp & Ip).
  pose proof (C_step h ltac:(lia)) as Ch. pose proof (C_range (par h) Tp) as CRp.
  unfold Psi. replace (Z.to_nat (h + 1 - HM)) with (S (Z.to_nat (h - HM))) by lia. rewrite zsum_snoc.
  replace (HM + Z.of_nat (Z.to_nat (h - HM))) with h by lia.
  assert (D : zsum (psi_term (h + 1)) HM (Z.to_nat (h - HM))
              = zsum (psi_term h) HM (Z.to_nat (h - HM)) + zsum (fun p => - (zind (par h =? p) * pw (C p + 1))) HM (Z.to_nat (h - HM))).
  { rewrite <- zsum_add. apply zsum_ext. intros p Hp. unfold psi_term.
    destruct (leafb p) eqn:Lp.
    - destruct (Z.eqb_spec (par h) p) as [Ep|Np]; [| cbn [zind]; lia].
      exfalso. apply (children_leaf p h); [unfold tail; lia | apply Z.ltb_lt; exact Lp | lia | exact Ep].
    - unfold cc. replace (Z.to_nat (h + 1 - HM - 1)) with (S (Z.to_nat (h - HM - 1))) by lia. rewrite zsum_snoc.
      replace (HM + 1 + Z.of_nat (Z.to_nat (h - HM - 1))) with h by lia. lia. }
  rewrite D. rewrite (zsum_single (fun p => - (zind (par h =? p) * pw (C p + 1))) HM (Z.to_nat (h - HM)) (par h)); [| unfold tail in Tp; lia |].
  2: { intros p Hp Np. replace (par h =? p) with false by (symmetry; apply Z.eqb_neq; congruence). reflexivity. }
  rewrite Z.eqb_refl. change (zind true) with 1. rewrite Z.mul_1_l.
  assert (Epw : pw (C (par h) + 1) = 2 ^ (ML - C h)) by (unfold pw; rewrite Ch; reflexivity).
  rewrite Epw.
  unfold psi_term at 2. rewrite (cc_none h (h + 1)) by lia.
  destruct (leafb h); cbn [negb andb].
  - change (zind false) with 0. lia.
  - unfold pw. destruct (Z.eqb_spec (C h) ML) as [E1|N1].
    + rewrite E1. replace (Z.min (ML + 1) ML) with ML by lia. rewrite Z.sub_diag. change (2 ^ 0) with 1. change (zind true) with 1. lia.
    + pose proof (C_range h ltac:(unfold tail; lia)). replace (Z.min (C h + 1) ML) with (C h + 1) by lia. change (zind false) with 0.
      replace (2 ^ (ML - C h)) with (2 ^ (ML - (C h + 1) + 1)) by (f_equal; lia). rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.

Lemma Psi_run : forall k, (Z.of_nat k <= 572 - HM) ->
  Psi (HM + 1 + Z.of_nat k) = 2 ^ ML + zsum (fun i => zind (negb (leafb i) && (C i =? ML))) (HM + 1) k.
Proof.
  induction k as [|k IH]; intros Hk.
  - cbn [zsum]. rewrite !Z.add_0_r. apply Psi_init.
  - rewrite zsum_snoc. replace (HM + 1 + Z.of_nat (S k)) with (HM + 1 + Z.of_nat k + 1) by lia.
    rewrite Psi_step by lia. rewrite IH by lia. lia.
Qed.

Lemma cc_final : forall p, tail p -> cc p 573 = if leafb p then 0 else 2.
Proof.
  intros p Hp. unfold cc. pose proof HM_range.
  destruct (leafb p) eqn:Lp.
  - apply zsum_0. intros i Hi. destruct (Z.eqb_spec (par i) p) as [Ep|]; [|reflexivity].
    exfalso. apply (children_leaf p i Hp); [apply Z.ltb_lt; exact Lp | lia | exact Ep].
  - assert (Ip : E <= nd p) by (apply Z.ltb_ge in Lp; lia).
    destruct (children_pos p Hp Ip) as (A & B & Cq).
    rewrite (zsum_two _ (HM + 1) (Z.to_nat (573 - HM - 1)) (572 - 2 * (nd p - E)) (571 - 2 * (nd p - E))); try lia.
    + rewrite (proj2 (Z.eqb_eq (par (572 - 2 * (nd p - E))) p)). 2: { apply (proj2 (children_internal p (572 - 2 * (nd p - E)) Hp Ip ltac:(lia))). left; reflexivity. }
      rewrite (proj2 (Z.eqb_eq (par (571 - 2 * (nd p - E))) p)). 2: { apply (proj2 (children_internal p (571 - 2 * (nd p - E)) Hp Ip ltac:(lia))). right; reflexivity. }
      reflexivity.
    + intros i Hi N1 N2. destruct (Z.eqb_spec (par i) p) as [Ep|]; [|reflexivity].
      exfalso. destruct (proj1 (children_internal p i Hp Ip ltac:(lia)) Ep); lia.
Qed.

Lemma Psi_final : Psi 573 = zsum (fun p => zind (leafb p) * 2 ^ (ML - C p)) HM (Z.to_nat (573 - HM)).
Proof.
  unfold Psi. apply zsum_ext. intros p Hp. pose proof HM_range. unfold psi_term. rewrite cc_final by (unfold tail; lia).
  destruct (leafb p); cbn [zind]; lia.
Qed.

Definition cntL (b : Z) : Z := zsum (w_cnt b) (HM + 1) (Z.to_nat (572 - HM)).
Definition KR (BCv : Z -> Z) : Z := zsum (fun b => BCv b * 2 ^ (ML - b)) 0 16.

Lemma kraft_identity : KR cntL = 2 ^ ML + NI 573.
Proof.
  pose proof HM_range. pose proof ML_range.
  unfold KR, cntL, NI.
  transitivity (zsum (fun p => zind (leafb p) * 2 ^ (ML - C p)) (HM + 1) (Z.to_nat (572 - HM))).
  - rewrite (zsum_ext _ (fun b => zsum (fun p => w_cnt b p * 2 ^ (ML - b)) (HM + 1) (Z.to_nat (572 - HM)))).
    2: { intros b Hb. rewrite (Z.mul_comm (zsum (w_cnt b) _ _)). rewrite <- zsum_scale. apply zsum_ext. intros; lia. }
    rewrite (zsum_swap (fun b p => w_cnt b p * 2 ^ (ML - b))).
    apply zsum_ext. intros p Hp. unfold w_cnt.
    destruct (leafb p) eqn:Lp; cbn [andb].
    + pose proof (C_range p ltac:(unfold tail; lia)). pose proof (C_pos p ltac:(lia)).
      rewrite (zsum_single _ 0 16 (C p)); [| lia |].
      * rewrite Z.eqb_refl. cbn [zind]. lia.
      * intros b Hb Nb. replace (C p =? b) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + cbn [zind]. rewrite Z.mul_0_l. apply zsum_0. intros; reflexivity.
  - replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) by lia.
    pose proof (Psi_run (Z.to_nat (572 - HM)) ltac:(lia)) as R. replace (HM + 1 + Z.of_nat (Z.to_nat (572 - HM))) with 573 in R by lia.
    rewrite Psi_final in R.
    replace (Z.to_nat (573 - HM)) with (S (Z.to_nat (572 - HM))) in R by lia.
    rewrite zsum_shift in R. rewrite root_internal in R. cbn [zind] in R. lia.
Qed.

Lemma ovf_identity : zsum w_ovf (HM + 1) (Z.to_nat (572 - HM)) = 2 * NI 573.
Proof.
  pose proof HM_range. unfold NI. replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) by lia.
  transitivity (zsum (fun i => zsum (fun p => zind (par i =? p) * zind (negb (leafb p) && (C p =? ML))) HM (Z.to_nat (573 - HM))) (HM + 1) (Z.to_nat (572 - HM))).
  - apply zsum_ext. intros i Hi. destruct (par_spec i ltac:(lia)) as (Tp & Pp & NDp & Ip).
    rewrite (zsum_single _ HM (Z.to_nat (573 - HM)) (par i)); [| unfold tail in Tp; lia |].
    + rewrite Z.eqb_refl. unfold w_ovf. replace (leafb (par i)) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb andb zind]. lia.
    + intros p Hp Np. replace (par i =? p) with false by (symmetry; apply Z.eqb_neq; congruence). reflexivity.
  - transitivity (zsum (fun p => zsum (fun i => zind (par i =? p) * zind (negb (leafb p) && (C p =? ML))) (HM + 1) (Z.to_nat (572 - HM))) HM (Z.to_nat (573 - HM))).
    { symmetry. exact (zsum_swap (fun p i => zind (par i =? p) * zind (negb (leafb p) && (C p =? ML))) (HM + 1) (Z.to_nat (572 - HM)) HM (Z.to_nat (573 - HM))). }
    replace (Z.to_nat (573 - HM)) with (S (Z.to_nat (572 - HM))) by lia. rewrite zsum_shift.
    rewrite C_root. pose proof ML_range. replace (0 =? ML) with false by (symmetry; apply Z.eqb_neq; lia). rewrite root_internal. cbn [negb andb].
    rewrite (zsum_ext (fun i => zind (par i =? HM) * zind false) (fun _ => 0)) by (intros; cbn [zind]; lia). rewrite zsum_0 by (intros; reflexivity).
    rewrite Z.add_0_l. rewrite <- zsum_scale. apply zsum_ext. intros p Hp.
    transitivity (zind (negb (leafb p) && (C p =? ML)) * cc p 573).
    + unfold cc. replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) by lia. rewrite <- zsum_scale. apply zsum_ext. intros; lia.
    + rewrite cc_final by (unfold tail; lia). destruct (leafb p); cbn [negb andb zind]; lia.
Qed.

Lemma capped_leaf_surplus : 0 < NI 573 -> NI 573 + 1 <= cntL ML.
Proof.
  intros Hpos. pose proof HM_range. pose proof ML_range.
  unfold NI, cntL in *. replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) in Hpos |- * by lia.
  destruct (zsum_pos_has (fun i => negb (leafb i) && (C i =? ML)) (HM + 1) (Z.to_nat (572 - HM)) Hpos) as (a & Ha & Pa & Mina).
  apply andb_prop in Pa. destruct Pa as [Ia Ca]. apply Z.eqb_eq in Ca.
  set (capped := fun i => C i =? ML).
  assert (TOT : zsum (fun i => zind (capped i)) (HM + 1) (Z.to_nat (572 - HM))
                = zsum (fun i => zind (negb (leafb i) && (C i =? ML))) (HM + 1) (Z.to_nat (572 - HM)) + zsum (w_cnt ML) (HM + 1) (Z.to_nat (572 - HM))).
  { rewrite <- zsum_add. apply zsum_ext. intros i Hi. unfold w_cnt. subst capped. destruct (leafb i), (C i =? ML); reflexivity. }
  assert (SPLIT : zsum (fun i => zind (capped i)) (HM + 1) (Z.to_nat (572 - HM))
                  = zsum (fun i => zind (capped i && capped (par i))) (HM + 1) (Z.to_nat (572 - HM))
                    + zsum (fun i => zind (capped i && negb (capped (par i)))) (HM + 1) (Z.to_nat (572 - HM))).
  { rewrite <- zsum_add. apply zsum_ext. intros i Hi. destruct (capped i), (capped (par i)); reflexivity. }
  assert (CH : zsum (fun i => zind (capped i && capped (par i))) (HM + 1) (Z.to_nat (572 - HM)) = 2 * zsum (fun i => zind (negb (leafb i) && (C i =? ML))) (HM + 1) (Z.to_nat (572 - HM))).
  { pose proof ovf_identity as OV. unfold NI in OV. replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) in OV by lia.
    rewrite <- OV. apply zsum_ext. intros i Hi. unfold w_ovf. subst capped.
    destruct (par_spec i ltac:(lia)) as (Tp & _). pose proof (C_step i ltac:(lia)) as Ci.
    destruct (Z.eqb_spec (C (par i)) ML) as [E1|N1].
    - rewrite Ci, E1. replace (Z.min (ML + 1) ML =? ML) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
    - rewrite Bool.andb_false_r. reflexivity. }
  assert (ONE : 1 <= zsum (fun i => zind (capped i && negb (capped (par i)))) (HM + 1) (Z.to_nat (572 - HM))).
  { apply (zsum_ind_ge1 _ _ _ a); [lia|]. subst capped. cbn beta. rewrite Ca, Z.eqb_refl. cbn [andb].
    destruct (par_spec a ltac:(lia)) as (Tp & Pp & _ & Ip).
    destruct (Z.eq_dec (par a) HM) as [Er|Nr]; [rewrite Er, C_root; apply Bool.negb_true_iff; apply Z.eqb_neq; lia|].
    pose proof (Mina (par a) ltac:(unfold tail in Tp; lia)) as M. apply Bool.negb_true_iff.
    replace (leafb (par a)) with false in M by (symmetry; apply Z.ltb_ge; lia). cbn [negb andb] in M. exact M. }
  lia.
Qed.

End Tail.
