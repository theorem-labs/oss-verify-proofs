(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Mem Cells Step.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook HxToolkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Glue.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma rw_CB_bytes (m : word -> option byte) (A : Z) (n : nat) (bs : list byte) :
  rw_cells segs m A [CB n bs] ->
  forall i, 0 <= i < Z.of_nat n -> (exists b, mrd segs m (wa (A + i)) = Some b) /\ wview segs m (wa (A + i)) <> None.
Proof.
  intros [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] i Hi. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb, H1. rewrite app_nil_r in Hb, H1. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  split; [|apply Hw; lia].
  specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; exact Hb|]. apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_bytes (m : word -> option byte) (A : Z) (cs : list Cells.cell) :
  rw_cells segs m A cs ->
  forall i, 0 <= i < Z.of_nat (cells_size cs) ->
    mrd segs m (wa (A + i)) = nth_error (cells_bytes cs) (Z.to_nat i) /\ nth_error (cells_bytes cs) (Z.to_nat i) <> None
    /\ wview segs m (wa (A + i)) <> None.
Proof.
  intros [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] i Hi. rewrite (cells_bytes_length cs Hwf) in Hb, H1.
  specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. split; [exact Hb|]. split; [|apply Hw; lia].
  apply nth_error_Some. rewrite (cells_bytes_length cs Hwf). lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_rw_CB (m : word -> option byte) (A : Z) (n : nat) :
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> (exists b, mrd segs m (wa (A + i)) = Some b) /\ wview segs m (wa (A + i)) <> None) ->
  exists bs, rw_cells segs m A [CB n bs].
Proof.
  intros HA Hn H.
  destruct (collect_bytes segs m n A (fun _ _ => True) HA Hn) as (bs & Hl & Hb & _).
  { intros i Hi. destruct (H i Hi) as [[b Eb] _]. exists b. split; [exact Eb | exact I]. }
  exists bs. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. exact (proj2 (H i Hi)).
Qed.

(* [comment removed for export] *)
Lemma le4_exists (bs : list byte) : length bs = 4%nat -> exists v : word, le4 v = bs.
Proof.
  intros Hl. destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try discriminate.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. change (bv_modulus 8) with 256 in *.
  set (z := bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
  assert (Hz : 0 <= z < 2 ^ 64) by (unfold z; lia).
  exists (Z_to_bv 64 z). unfold le4. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hz.
  cbn [Z_to_le_bytes]. repeat f_equal;
    (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256;
     rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256; unfold z; Z.div_mod_to_equations; lia).
Qed.

Lemma bytes_rw_C4 (m : word -> option byte) (A : Z) :
  0 <= A -> A + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 -> (exists b, mrd segs m (wa (A + i)) = Some b) /\ wview segs m (wa (A + i)) <> None) ->
  exists v : word, rw_cells segs m A [C4 v].
Proof.
  intros HA Hn H.
  destruct (collect_bytes segs m 4 A (fun _ _ => True) HA ltac:(lia)) as (bs & Hl & Hb & _).
  { intros i Hi. destruct (H i ltac:(lia)) as [[b Eb] _]. exists b. split; [exact Eb | exact I]. }
  destruct (le4_exists bs Hl) as [v Ev]. exists v. split; [split|].
  - cbn. exact (conj I I).
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, Ev. exact Hb.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. exact (proj2 (H i ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma rw_C4_bytes (m : word -> option byte) (A : Z) (v : word) :
  rw_cells segs m A [C4 v] ->
  forall i, 0 <= i < 4 -> (exists b, mrd segs m (wa (A + i)) = Some b) /\ wview segs m (wa (A + i)) <> None.
Proof.
  intros [[_ (H0 & H1 & Hb)] (W0 & W1 & Hw)] i Hi.
  cbn [cells_bytes cbytes] in Hb, H1. rewrite app_nil_r in Hb, H1. rewrite length_le4 in Hb, H1. cbn [cells_size csize] in Hw.
  split; [|apply Hw; lia].
  specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
  destruct (nth_error (le4 v) (Z.to_nat i)) as [b|] eqn:E; [exists b; exact Hb|]. apply nth_error_None in E. rewrite length_le4 in E. lia.
Qed.

(* [comment removed for export] *)
Lemma region_mapped (rho : valuation) (t : int) (rg : region) (m : word -> option byte) :
  region_ok segs rho t rg m ->
  forall i, 0 <= i < to_Z (rg_size rg) ->
    (exists b, mrd segs m (wa (rbase rho t rg + i)) = Some b) /\ (rg_wr rg = true -> wview segs m (wa (rbase rho t rg + i)) <> None).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hb) i Hi. destruct (Hb i Hi) as (b & Eb & _ & Wb). split; [exists b; exact Eb | exact Wb].
Qed.

(* [comment removed for export] *)
Lemma region_ok_of_cells (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (cs : list Cells.cell) :
  rw_cells segs m (rbase rho t rg) cs ->
  0 < rbase rho t rg -> rbase rho t rg + to_Z (rg_size rg) < two63 -> to_Z (rg_size rg) < 2 ^ 62 ->
  to_Z (rg_size rg) <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 -> to_Z (rg_al rg) < 63 -> rbase rho t rg mod 2 ^ to_Z (rg_al rg) = 0 ->
  Z.of_nat (cells_size cs) = to_Z (rg_size rg) ->
  (forall i b, nth_error (cells_bytes cs) i = Some b -> kb_ok rho (rg_kb segs rg (Z.of_nat i)) b) ->
  region_ok segs rho t rg m.
Proof.
  intros Hrw H0 H1 H2 H3 H4 H5 H6 Hsz Hk. pose proof Hrw as [[Hwf (_ & _ & Hb)] (_ & _ & Hw)].
  apply (region_ok_of_bytes segs rho t rg m (cells_bytes cs) H0 H1 H2 H3 H4 H5 H6).
  - rewrite (cells_bytes_length cs Hwf). exact Hsz.
  - exact Hb.
  - intros _ i Hi. apply Hw. lia.
  - exact Hk.
Qed.

End Glue.

(* [comment removed for export] *)
Lemma reset_errno_inv (te ea : int) (M M1 : mem) : reset_errno te ea M = Some M1 ->
  exists rg, mget M te = Some rg /\ rg_abs rg = Some ea /\ rg_dflt rg = DUnk /\ rg_size rg = 4%uint63 /\ rg_wr rg = true
             /\ M1 = mset M te (RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) DUnk (rg_d rg) IEmpty).
Proof.
  unfold reset_errno. intros H. destruct (mget M te) as [rg|] eqn:Eg; [|discriminate].
  destruct (rg_abs rg) as [a|] eqn:Ea; [|discriminate]. destruct (rg_dflt rg) eqn:Ed; try discriminate.
  destruct ((a =? ea)%uint63 && (rg_size rg =? 4)%uint63 && rg_wr rg) eqn:Ec; [|discriminate].
  apply andb_prop in Ec as [Ec Ew]. apply andb_prop in Ec as [Ec1 Ec2]. apply Uint63.eqb_spec in Ec1, Ec2. subst a.
  injection H as <-. exists rg. rewrite Ea. auto 8.
Qed.
