(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIfaceA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition off_poison (P : list (Z * Z)) (x : Z) : Prop := Forall (fun r => x < S (fst r) \/ S (snd r) <= x) P.

Fixpoint zruns (lo : Z) (P : list (Z * Z)) (hi : Z) : list (Z * Z) :=
  match P with
  | [] => [(S lo, S hi - S lo)]
  | r :: P' => (S lo, S (fst r) - S lo) :: zruns (snd r) P' hi
  end.

Lemma zruns_cover : forall P lo hi x, S lo <= x < S hi -> off_poison P x -> exists z, In z (zruns lo P hi) /\ fst z <= x < fst z + snd z.
Proof.
  induction P as [|r P IH]; intros lo hi x Hx OP; cbn [zruns].
  - exists (S lo, S hi - S lo). split; [left; reflexivity | cbn [fst snd]; lia].
  - unfold off_poison in OP. apply Forall_cons_iff in OP as [[O1 | O1] O2].
    + exists (S lo, S (fst r) - S lo). split; [left; reflexivity | cbn [fst snd]; lia].
    + destruct (IH (snd r) hi x ltac:(lia) O2) as (z & Hz & Hzx). exists z. split; [right; exact Hz | exact Hzx].
Qed.

Lemma off_poison_of_range : forall P a n x, Forall (fun r => fst r mod 8 = 0) P -> 0 < n ->
  Forall (fun r => a + n <= fst r \/ snd r <= a) P -> in_shadow_of a n x -> off_poison P x.
Proof.
  intros P a n x AL Hn AV (X1 & X2). unfold off_poison. rewrite Forall_forall in *. intros r Hr.
  specialize (AL r Hr). specialize (AV r Hr). unfold S in *. destruct AV as [AV | AV].
  - left. assert ((a + n - 1) / 8 < fst r / 8); [|lia].
    apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (fst r) 8 ltac:(lia)). lia.
  - right. assert (snd r / 8 <= a / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma shadow_blk_keep : forall lo hi (M M' : word -> option byte) u n, 0 <= lo -> hi mod 8 = 0 -> lo <= u -> u + n <= hi -> 0 < n ->
  (forall x v, S lo <= x < S hi -> byte_at M x v -> byte_at M' x v) -> shadow_blk M u n -> shadow_blk M' u n.
Proof.
  intros lo hi M M' u n Hlo Hhi Hu Hn Hp BYTE (Z0 & PT).
  assert (D1 : lo / 8 <= u / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_mod u 8 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as Bu.
  pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Bn.
  pose proof (Z.div_mod hi 8 ltac:(lia)) as Dh.
  split.
  - intros j Hj. apply BYTE; [|exact (Z0 j Hj)]. unfold S. lia.
  - intros NZ. apply BYTE; [|exact (PT NZ)]. unfold S. lia.
Qed.

Definition glob_in (lo hi : Z) (g : Z * Z) : bool := ((lo <=? fst g) && (fst g + snd g <=? hi) && (0 <? snd g))%bool.
Lemma glob_in_spec : forall lo hi g, glob_in lo hi g = true -> lo <= fst g /\ fst g + snd g <= hi /\ 0 < snd g.
Proof. intros lo hi g H. unfold glob_in in H. rewrite !andb_true_iff, !Z.leb_le, Z.ltb_lt in H. lia. Qed.

Lemma globs_keep : forall lo hi G (M M' : word -> option byte), 0 <= lo -> hi mod 8 = 0 -> forallb (glob_in lo hi) G = true ->
  (forall x v, S lo <= x < S hi -> byte_at M x v -> byte_at M' x v) ->
  Forall (fun g => shadow_blk M (fst g) (snd g)) G -> Forall (fun g => shadow_blk M' (fst g) (snd g)) G.
Proof.
  intros lo hi G M M' Hlo Hhi HG BYTE F. rewrite Forall_forall in *. intros g Hg.
  destruct (glob_in_spec lo hi g (proj1 (forallb_forall _ _) HG g Hg)) as (G1 & G2 & G3).
  exact (shadow_blk_keep lo hi M M' (fst g) (snd g) Hlo Hhi G1 G2 G3 BYTE (F g Hg)).
Qed.

Definition aligned8 (P : list (Z * Z)) : bool := forallb (fun r => (fst r mod 8 =? 0)) P.
Lemma aligned8_spec : forall P, aligned8 P = true -> Forall (fun r => fst r mod 8 = 0) P.
Proof. intros P H. apply Forall_forall. intros r Hr. exact (proj1 (Z.eqb_eq _ _) (proj1 (forallb_forall _ _) H r Hr)). Qed.

(* [comment removed for export] *)
Definition off_poison_rngb (P : list (Z * Z)) (xlo xhi : Z) : bool := forallb (fun r => (xhi <=? S (fst r)) || (S (snd r) <=? xlo))%bool P.
Lemma off_poison_rng : forall P xlo xhi, off_poison_rngb P xlo xhi = true -> forall x, xlo <= x < xhi -> off_poison P x.
Proof.
  intros P xlo xhi H x Hx. apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as B. cbn beta in B.
  apply orb_prop in B as [B | B]; apply Z.leb_le in B; lia.
Qed.
