(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface R_depot_defs R_unwind_defs R_unwind_chain RT_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MAIN_PCS : list Z := [PC_MALLOC; PC_FREE; PC_CALLOC; PC_REALLOC].

Lemma T_MAIN_eq : T_MAIN = traces_of MAIN_PCS SITE_TRACES. Proof. reflexivity. Qed.

Lemma sites_ok : sites_okb 4096 MAIN_PCS 28 SITE_TRACES = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma T_MAIN_length : Z.of_nat (length T_MAIN) <= 19999. Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma T_MAIN_len5 : forall tr, In tr T_MAIN -> (1 <= length tr <= TR_MAX)%nat.
Proof.
  intros tr H. assert (X : forallb (fun t => (1 <=? length t)%nat && (length t <=? TR_MAX)%nat) T_MAIN = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X tr H) as Y. cbv beta in Y. apply andb_prop in Y as [Y1 Y2].
  apply Nat.leb_le in Y1. apply Nat.leb_le in Y2. lia.
Qed.

Lemma T_MAIN_rng64 : forall tr, In tr T_MAIN -> Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
  intros tr H. assert (X : forallb (fun t => forallb (fun x => (0 <=? x) && (x <? 2 ^ 64)) t) T_MAIN = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X tr H) as Y. cbv beta in Y. apply Forall_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) Y x Hx) as Z0. cbv beta in Z0. apply andb_prop in Z0 as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. lia.
Qed.

(* [comment removed for export] *)
Theorem site_trace_main : forall (m : mem) pc bot top (ra s0 sp : word),
  In pc MAIN_PCS -> unwind_ch m ra s0 sp -> top - 16 <= 2 ^ 63 ->
  exists ch tr, chain_cells [(0, bv_unsigned sp)] m (bv_unsigned s0) ch
    /\ unwind_trace pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr
    /\ In tr T_MAIN /\ (1 <= length tr <= TR_MAX)%nat.
Proof.
  intros m pc bot top ra s0 sp Hpc (ras & Hs & HU) Htop.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  destruct (site_unwind USTACK_TOP [(0, bv_unsigned sp)] m MAIN_PCS SITE_TRACES 28 pc bot top 30 (bv_unsigned sp) (bv_unsigned ra)
              (bv_unsigned s0) ras sites_ok Hpc Hs ltac:(unfold USTACK_TOP; lia) Htop ltac:(lia) ltac:(cbn; lia) HU)
    as (ch & tr & CC & ET & HT & HL).
  { intros a Ha _. cbn [disjoint_from]. split; [right; exact Ha | exact I]. }
  exists ch, tr. split; [exact CC|]. split; [exact ET|]. split; [rewrite T_MAIN_eq; exact HT | cbn in HL; lia].
Qed.

(* [comment removed for export] *)
Lemma site_trace_frameless : forall pc bot top (ra s0 sp : word) ch tr,
  unwind_ok ra s0 sp -> top - 16 <= 2 ^ 63 -> In pc MAIN_PCS ->
  unwind_trace pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
  tr = [pc] \/ tr = [pc; bv_unsigned ra].
Proof.
  intros pc bot top ra s0 sp ch tr (Hra & Hs0) Htop Hpc H. unfold unwind_trace in H.
  destruct (top / 4096 =? 0); [injection H as <-; left; reflexivity|].
  destruct (fr_ok bot (top - 16) (bv_unsigned sp)); [| injection H as <-; left; reflexivity].
  cbn [uw_loop length Z.of_nat] in H. change (30 <=? 1) with false in H. cbv iota in H.
  assert (FS : fr_ok (bv_unsigned sp) (top - 16) (bv_unsigned s0) = false).
  { apply fp_stop_fr_ok; [exact Htop|]. unfold fp_stop. destruct Hs0 as [X|[X|X]]; [left; lia | right; left; exact X | right; right; exact X]. }
  rewrite FS in H.
  destruct (bv_unsigned ra <? 4096); [injection H as <-; left; reflexivity|].
  destruct (bv_unsigned ra =? pc); injection H as <-; [left | right]; reflexivity.
Qed.
