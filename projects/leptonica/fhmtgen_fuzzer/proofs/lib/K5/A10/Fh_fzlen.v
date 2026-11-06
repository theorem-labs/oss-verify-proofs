(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA Layout RT_iface Lept_iface Gm_iface Fh_iface Fh_sel_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma flat_map_rev_length : forall (A B : Type) (f : A -> list B) (l : list A), length (flat_map f (rev l)) = length (flat_map f l).
Proof.
  intros A B f l. induction l as [|a l IH]; [reflexivity|].
  cbn [rev]. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r, !length_app, IH. lia.
Qed.

Lemma sel_live_length : forall sel v, length (sel_live sel v) = (3 + length (s_rows v))%nat.
Proof. intros sel v. unfold sel_live. cbn [length]. rewrite length_app, length_rev, length_map. cbn [length]. lia. Qed.

Lemma sela_live_len_hm : forall live (m : mem) sela arr sels,
  sela_obj live m sela arr sels -> hm_sels_ok sels -> length (sela_live sela arr sels) = 74%nat.
Proof.
  intros live m sela arr sels (_ & _ & _ & _ & _ & SELS) (HL & HJ).
  unfold sela_live. rewrite length_app, flat_map_rev_length. cbn [length].
  assert (ROWS : forall i, (i < 10)%nat -> Z.of_nat (length (s_rows (snd (fst (nth i sels (0, mkSelv 0 0 0 0 0 0 [], [])))))) = fst (fst (fst (nth i HM_DIMS (0, 0, 0, 0))))).
  { intros i Hi. pose proof (HJ i Hi) as HI. cbv zeta in HI. destruct HI as (HSY & _).
    assert (EIN : In (nth i sels (0, mkSelv 0 0 0 0 0 0 [], [])) sels) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) SELS _ EIN) as SO. cbv beta in SO.
    destruct SO as ((_ & _ & _ & _ & RL & _) & _). rewrite RL. exact HSY. }
  do 10 (destruct sels as [|? sels]; [discriminate HL|]). destruct sels; [| discriminate HL].
  pose proof (ROWS 0%nat ltac:(lia)) as R0. pose proof (ROWS 1%nat ltac:(lia)) as R1. pose proof (ROWS 2%nat ltac:(lia)) as R2.
  pose proof (ROWS 3%nat ltac:(lia)) as R3. pose proof (ROWS 4%nat ltac:(lia)) as R4. pose proof (ROWS 5%nat ltac:(lia)) as R5.
  pose proof (ROWS 6%nat ltac:(lia)) as R6. pose proof (ROWS 7%nat ltac:(lia)) as R7. pose proof (ROWS 8%nat ltac:(lia)) as R8.
  pose proof (ROWS 9%nat ltac:(lia)) as R9.
  cbn [nth HM_DIMS fst snd] in R0, R1, R2, R3, R4, R5, R6, R7, R8, R9.
  cbn [flat_map]. rewrite !length_app, !sel_live_length. cbn [length]. lia.
Qed.
