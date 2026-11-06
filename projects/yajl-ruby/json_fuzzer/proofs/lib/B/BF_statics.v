(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import MState Mem Cells Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition amalloc_statics (m : mem) : Prop :=
     rw_cells bsegs m 0xa61f8 [C8 (Z_to_bv 64 0x10)]          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5e1560 [C4 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x130822 [C1 (Z_to_bv 8 0)]             (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa55e0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x1400dc)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x140178 [C8 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x1401ec [C1 (Z_to_bv 8 0)]             (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x1401d8 [C4 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x601810 [C8 (Z_to_bv 64 4096)]         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x1401dc [C1 (Z_to_bv 8 1)]             (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa55c8 [C8 (Z_to_bv 64 0xa7400)]        (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa5588 [C8 (Z_to_bv 64 0xa7440)]        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa7440 [C8 (Z_to_bv 64 0x193ca)]        (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa6228 [C8 (Z_to_bv 64 0x601590)].       (* [comment removed for export] *)

Definition amalloc_statics_cells : list (Z * Z) :=
  [(0xa61f8, 8); (0x5e1560, 4); (0x130822, 1); (0xa55e0, 16); (0x140178, 8); (0x1401ec, 1); (0x1401d8, 4); (0x601810, 8); (0x1401dc, 1); (0xa55c8, 8); (0xa5588, 8); (0xa7440, 8); (0xa6228, 8)].

Lemma amalloc_statics_transport : forall W m m',
  amalloc_statics m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun c => disjoint_from W (fst c) (snd c)) amalloc_statics_cells ->
  amalloc_statics m'.
Proof. aceil.
  intros W m m' (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13) MU WM D.
  unfold amalloc_statics_cells in D.
  inversion D as [|? ? D1 X1]; subst. inversion X1 as [|? ? D2 X2]; subst. inversion X2 as [|? ? D3 X3]; subst.
  inversion X3 as [|? ? D4 X4]; subst. inversion X4 as [|? ? D5 X5]; subst. inversion X5 as [|? ? D6 X6]; subst.
  inversion X6 as [|? ? D7 X7]; subst. inversion X7 as [|? ? D8 X8]; subst. inversion X8 as [|? ? D9 X9]; subst. inversion X9 as [|? ? D10 X10]; subst.
  inversion X10 as [|? ? D11 X11]; subst. inversion X11 as [|? ? D12 X12]; subst. inversion X12 as [|? ? D13 _]; subst.
  cbn [fst snd] in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]];
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; assumption]).
Qed.

(* [comment removed for export] *)
Definition in_amalloc_statics (a : Z) : Prop :=
  (0xa61f8 <= a < 0xa6200) \/ (0x5e1560 <= a < 0x5e1564) \/ (0x130822 <= a < 0x130823)
  \/ (0xa55e0 <= a < 0xa55f0) \/ (0x140178 <= a < 0x140180) \/ (0x1401ec <= a < 0x1401ed)
  \/ (0x1401d8 <= a < 0x1401dd) \/ (0x601810 <= a < 0x601818) \/ (0xa55c8 <= a < 0xa55d0)
  \/ (0xa5588 <= a < 0xa5590) \/ (0xa7440 <= a < 0xa7448) \/ (0xa6228 <= a < 0xa6230).

Lemma amalloc_statics_agree : forall m m',
  amalloc_statics m -> wmono bsegs m m' -> (forall a, in_amalloc_statics a -> m' (wa a) = m (wa a)) -> amalloc_statics m'.
Proof. aceil.
  intros m m' S WM AG.
  eapply (amalloc_statics_transport [(0, 0xa5588); (0xa5590, 0xa55c8); (0xa55d0, 0xa55e0); (0xa55f0, 0xa61f8); (0xa6200, 0xa6228); (0xa6230, 0xa7440); (0xa7448, 0x130822); (0x130823, 0x140178); (0x140180, 0x1401d8); (0x1401dd, 0x1401ec); (0x1401ed, 0x5e1560); (0x5e1564, 0x601810); (0x601818, 2^64)]); [exact S| | exact WM|].
  - intros x Hx. pose proof (bv_unsigned_in_range _ x) as R. change (bv_modulus 64) with (2^64) in R.
    rewrite <- (MState.Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply AG. unfold in_amalloc_statics. cbn in Hx. lia.
  - unfold amalloc_statics_cells. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
(* [comment removed for export] *)
Lemma guard_cell : forall m, exists g, rw_cells bsegs m 0x601590 [C8 g].
Proof.
  intros m.
  set (rd := fun i : nat => match mrd bsegs m (wa (0x601590 + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (RD : forall i, (i < 8)%nat -> mrd bsegs m (wa (0x601590 + Z.of_nat i)) = Some (rd i)).
  { intros i Hi. subst rd. cbn beta. unfold mrd. destruct (m (wa (0x601590 + Z.of_nat i))) as [b|]; [reflexivity|].
    do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). exfalso. clear -Hi. lia. }
  assert (WV : forall i, 0 <= i < 8 -> wview bsegs m (wa (0x601590 + i)) <> None).
  { intros i Hi. unfold wview. destruct (m (wa (0x601590 + i))); [discriminate|].
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by (clear -Hi; lia).
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate. }
  exists (le_bytes_to_word (map rd (seq 0 8))).
  split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite BF_kit3.le8_of_bytes by reflexivity.
    split; [clear; lia|]. split; [cbn; clear; lia|]. intros i Hi. cbn [length map seq] in Hi.
    rewrite nth_error_map. rewrite (nth_error_seq 0 8 i). replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add]. apply RD. exact Hi.
  - split; [clear; lia|]. split; [cbn; clear; lia|]. intros i Hi. apply WV. cbn in Hi. clear -Hi. lia.
Qed.

End RC__1.
