(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMspec_str.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* The functional half of the bridge for the string walks: the walks answer with
   `strstr_val` (lib/A/Spec/StrStr.v, a computation over byte lists), while fm's program
   part asks for `first_occ` / `no_occ` (lib/A/FMH_Rt.v:31-32, relations over the byte
   values).  These are the two translations, and the same for isalnum.

   Pure list reasoning: it needs neither the donor core nor the walks. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Rt.
Import ListNotations.
Open Scope Z_scope.

(* ---- prefix_eqb ---- *)

Lemma prefix_eqb_spec : forall (w t : list Z),
  prefix_eqb w t = true <-> ((length w <= length t)%nat /\ firstn (length w) t = w).
Proof.
  induction w as [|a w IH]; intros t; cbn [prefix_eqb length firstn].
  - split; [intros _; split; [lia | reflexivity] | reflexivity].
  - destruct t as [|b t]; cbn [length firstn].
    + split; [discriminate | intros (H & _); lia].
    + rewrite andb_true_iff, Z.eqb_eq, (IH t). split.
      * intros (-> & Hlen & Hfst). split; [lia|]. rewrite Hfst. reflexivity.
      * intros (Hlen & Heq). injection Heq as -> Hfst. split; [reflexivity | split; [lia | exact Hfst]].
Qed.

Lemma prefix_eqb_occ : forall (t w : list Z), prefix_eqb w t = true <-> occ_at t w 0.
Proof.
  intros t w. rewrite prefix_eqb_spec. unfold occ_at. cbn [skipn].
  split; intros (H1 & H2); (split; [lia | exact H2]).
Qed.

Lemma occ_at_cons : forall (b : Z) (t w : list Z) (j : nat),
  occ_at (b :: t) w (S j) <-> occ_at t w j.
Proof.
  intros b t w j. unfold occ_at. cbn [length skipn]. split; intros (H1 & H2); (split; [lia | exact H2]).
Qed.

(* ---- find_first ---- *)

Lemma find_first_some : forall (t w : list Z) (j : nat),
  find_first t w = Some j -> first_occ t w j.
Proof.
  induction t as [|b t IH]; intros w j Hf.
  - cbn in Hf. destruct (prefix_eqb w []) eqn:EP; [|discriminate].
    injection Hf as <-. split; [apply prefix_eqb_occ; exact EP | intros j' Hj'; lia].
  - cbn [find_first] in Hf. destruct (prefix_eqb w (b :: t)) eqn:EP.
    + injection Hf as <-. split; [apply prefix_eqb_occ; exact EP | intros j' Hj'; lia].
    + destruct (find_first t w) as [k|] eqn:EF; [|discriminate].
      cbn [option_map] in Hf. injection Hf as <-.
      destruct (IH w k EF) as (Hocc & Hmin).
      split; [apply occ_at_cons; exact Hocc|].
      intros j' Hj'. destruct j' as [|j''].
      * intros Hc. rewrite (proj2 (prefix_eqb_occ (b :: t) w) Hc) in EP. discriminate.
      * intros Hc. apply (Hmin j'' ltac:(lia)). apply (proj1 (occ_at_cons b t w j'')). exact Hc.
Qed.

Lemma find_first_none : forall (t w : list Z),
  find_first t w = None -> no_occ t w.
Proof.
  induction t as [|b t IH]; intros w Hf j.
  - cbn in Hf. destruct (prefix_eqb w []) eqn:EP; [discriminate|].
    intros Hc. destruct j as [|j']; cbn [occ_at] in Hc.
    + rewrite (proj2 (prefix_eqb_occ [] w) Hc) in EP. discriminate.
    + unfold occ_at in Hc. cbn [length skipn] in Hc. lia.
  - cbn [find_first] in Hf. destruct (prefix_eqb w (b :: t)) eqn:EP; [discriminate|].
    destruct (find_first t w) as [k|] eqn:EF; [cbn [option_map] in Hf; discriminate|].
    intros Hc. destruct j as [|j'].
    + rewrite (proj2 (prefix_eqb_occ (b :: t) w) Hc) in EP. discriminate.
    + apply (IH w EF j'). apply (proj1 (occ_at_cons b t w j')). exact Hc.
Qed.

(* ---- what the walk answers, in the words of fm's program part ---- *)

Theorem strstr_val_spec : forall (A : Z) (hb nb : list byte),
  (strstr_val A hb nb = 0 /\ no_occ (map bv_unsigned hb) (map bv_unsigned nb))
  \/ (exists j, first_occ (map bv_unsigned hb) (map bv_unsigned nb) j
                /\ strstr_val A hb nb = A + Z.of_nat j).
Proof.
  intros A hb nb. unfold strstr_val.
  destruct (find_first (map bv_unsigned hb) (map bv_unsigned nb)) as [j|] eqn:EF.
  - right. exists j. split; [apply find_first_some; exact EF | reflexivity].
  - left. split; [reflexivity | apply find_first_none; exact EF].
Qed.

(* ---- isalnum ---- *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import isalnum_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.

(* the walk's answer and fm's model are the same test *)
Lemma alnum_b_is_alnum : forall c, alnum_b c = ManifestModel.is_alnum c.
Proof. intros c. reflexivity. Qed.

(* ---- strncasecmp ---- *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A Require Import I_scasem.

(* the walk's ToLower (I_scasem.v:20) and the program part's (FMH_Rt.v:26) are one function *)
Lemma lc_is_zlw : lc = zlw.
Proof. reflexivity. Qed.

(* the index the walk stops at, read on the byte values *)
Fixpoint zcase_idx (k : nat) (m1 m2 : list Z) {struct k} : nat :=
  match k with
  | O => O
  | S k' => match m1, m2 with
            | x :: r1, y :: r2 => if negb (zlw x =? zlw y) || (x =? 0) then O else S (zcase_idx k' r1 r2)
            | _, _ => O
            end
  end.

Lemma scase_idx_aux_z : forall (k : nat) (m1 m2 : list Z),
  Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  scase_idx_aux (map (Z_to_bv 8) m1) (map (Z_to_bv 8) m2) k = zcase_idx k m1 m2.
Proof.
  induction k as [|k IH]; intros m1 m2 H1 H2; [reflexivity|].
  destruct m1 as [|x r1]; [reflexivity|]. destruct m2 as [|y r2]; [reflexivity|].
  inversion H1 as [|? ? Hx H1']; subst. inversion H2 as [|? ? Hy H2']; subst.
  cbn [map scase_idx_aux zcase_idx].
  assert (Ex : bv_unsigned (Z_to_bv 8 x) = x)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; lia).
  assert (Ey : bv_unsigned (Z_to_bv 8 y) = y)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; lia).
  rewrite Ex, Ey.
  destruct (negb (zlw x =? zlw y) || (x =? 0))%bool; [reflexivity|].
  rewrite (IH r1 r2 H1' H2'). reflexivity.
Qed.

(* the walk's answer, read on the byte values *)
Definition zcase_res (k : nat) (m1 m2 : list Z) : Z :=
  let i := zcase_idx k m1 m2 in
  if (i =? k)%nat then 0 else zlw (nth i m1 0) - zlw (nth i m2 0).

(* a C string as the walk sees it: its bytes and then one NUL, nowhere else *)
Definition nul_last (m : list Z) : Prop :=
  exists l, m = l ++ [0] /\ Forall (fun c => c <> 0) l /\ Forall (fun c => 0 <= c < 256) l.

Lemma lc_zero : forall c, 0 <= c -> zlw c = 0 -> c = 0.
Proof.
  intros c Hc. unfold zlw. destruct ((65 <=? c) && (c <=? 90))%bool eqn:E; [|exact (fun H => H)].
  apply andb_prop in E as [E1 _]. apply Z.leb_le in E1. lia.
Qed.

Lemma nul_last_cons : forall x r, nul_last (x :: r) -> x = 0 -> r = [].
Proof.
  intros x r (l & Hm & Hnz & _) Hx. subst x.
  destruct l as [|a l]; cbn in Hm.
  - congruence.
  - exfalso. inversion Hnz as [|? ? Hz _]; subst. apply Hz. congruence.
Qed.

Lemma nul_last_hd_range : forall x r, nul_last (x :: r) -> 0 <= x < 256.
Proof.
  intros x r (l & Hm & Hnz & Hr).
  destruct l as [|a l]; cbn in Hm.
  - assert (x = 0) by congruence. lia.
  - inversion Hr as [|? ? Ha _]; subst. assert (x = a) by congruence. lia.
Qed.

Lemma nul_last_tl : forall x r, nul_last (x :: r) -> x <> 0 -> nul_last r.
Proof.
  intros x r (l & Hm & Hnz & Hr) Hx.
  destruct l as [|a l]; cbn in Hm.
  - exfalso. apply Hx. congruence.
  - inversion Hnz as [|? ? _ Hnz']; subst. inversion Hr as [|? ? _ Hr']; subst.
    exists l. split; [congruence | split; [exact Hnz' | exact Hr']].
Qed.

(* a zero answer and the program part's `strncase_eq` are the same claim *)
Lemma zcase_res_zero : forall (k : nat) (m1 m2 : list Z),
  nul_last m1 -> nul_last m2 ->
  (zcase_res k m1 m2 = 0 <-> map zlw (firstn k m1) = map zlw (firstn k m2)).
Proof.
  induction k as [|k IH]; intros m1 m2 N1 N2.
  { unfold zcase_res. cbn [zcase_idx firstn map]. split; reflexivity. }
  destruct m1 as [|x r1]; [destruct N1 as (l & Hm & _); destruct l; discriminate|].
  destruct m2 as [|y r2]; [destruct N2 as (l & Hm & _); destruct l; discriminate|].
  unfold zcase_res. cbn [zcase_idx firstn map nth].
  destruct (negb (zlw x =? zlw y) || (x =? 0))%bool eqn:EB.
  - cbn [Nat.eqb]. apply orb_true_iff in EB as [EB|EB].
    + apply negb_true_iff, Z.eqb_neq in EB.
      split; [intros Hz; exfalso; apply EB; lia | intros Heq; exfalso; apply EB; injection Heq as Hh _; exact Hh].
    + apply Z.eqb_eq in EB. subst x.
      assert (Hr1 : r1 = []) by (apply (nul_last_cons 0 r1 N1); reflexivity).
      destruct (Z.eq_dec y 0) as [->|NY].
      * assert (Hr2 : r2 = []) by (apply (nul_last_cons 0 r2 N2); reflexivity).
        subst r1 r2. cbn [firstn map]. split; [reflexivity | intros _; unfold zlw; cbn; lia].
      * assert (Hy0 : 0 <= y < 256) by (apply (nul_last_hd_range y r2 N2)).
        assert (Hne : zlw 0 <> zlw y)
          by (intros Hc; apply NY; apply lc_zero; [lia | rewrite <- Hc; reflexivity]).
        split; [intros Hz; exfalso; apply Hne; lia
               | intros Heq; exfalso; apply Hne; injection Heq as Hh _; exact Hh].
  - apply orb_false_iff in EB as [EL EX]. apply negb_false_iff, Z.eqb_eq in EL. apply Z.eqb_neq in EX.
    cbn [Nat.eqb nth].
    assert (Hx0 : 0 <= x < 256) by (apply (nul_last_hd_range x r1 N1)).
    assert (HY : y <> 0) by (intros ->; apply EX; apply lc_zero; [lia | rewrite EL; reflexivity]).
    rewrite (IH r1 r2 (nul_last_tl x r1 N1 EX) (nul_last_tl y r2 N2 HY)).
    split; [intros H; rewrite EL, H; reflexivity | intros H; injection H as _ H; exact H].
Qed.

(* the walk's answer on byte lists is the Z-level one on their values *)
Lemma nth_error_map_nth : forall (m : list Z) (i : nat),
  (i < length m)%nat -> nth_error (map (Z_to_bv 8) m) i = Some (Z_to_bv 8 (nth i m 0)).
Proof.
  intros m i Hi. rewrite nth_error_map.
  destruct (nth_error m i) as [v|] eqn:E.
  - cbn [option_map]. rewrite (nth_error_nth m i 0 E). reflexivity.
  - apply nth_error_None in E. lia.
Qed.

Lemma u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. lia.
Qed.

Lemma scase_res_z : forall (n : Z) (m1 m2 : list Z),
  0 <= n -> Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  (zcase_idx (Z.to_nat n) m1 m2 < length m1)%nat -> (zcase_idx (Z.to_nat n) m1 m2 < length m2)%nat ->
  scase_res n (map (Z_to_bv 8) m1) (map (Z_to_bv 8) m2) = zcase_res (Z.to_nat n) m1 m2.
Proof.
  intros n m1 m2 Hn H1 H2 L1 L2.
  unfold scase_res, zcase_res, scase_idx.
  rewrite (scase_idx_aux_z (Z.to_nat n) m1 m2 H1 H2).
  set (i := zcase_idx (Z.to_nat n) m1 m2) in *.
  assert (Hi : Z.to_nat (Z.of_nat i) = i) by apply Nat2Z.id.
  rewrite Hi.
  destruct (Nat.eq_dec i (Z.to_nat n)) as [->|NE].
  - replace (Z.of_nat (Z.to_nat n) =? n) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite Nat.eqb_refl. reflexivity.
  - replace (Z.of_nat i =? n) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (i =? Z.to_nat n)%nat with false by (symmetry; apply Nat.eqb_neq; exact NE).
    rewrite (nth_error_map_nth m1 i L1), (nth_error_map_nth m2 i L2).
    rewrite !u8; [reflexivity | |].
    + apply (proj1 (Forall_forall _ _) H2 (nth i m2 0)). apply nth_In. exact L2.
    + apply (proj1 (Forall_forall _ _) H1 (nth i m1 0)). apply nth_In. exact L1.
Qed.
