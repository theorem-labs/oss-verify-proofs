(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import MState Mem Cells Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_kit3.
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
     rw_cells asegs m 0xa5608 [C8 (Z_to_bv 64 0x10)]          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5e0b20 [C4 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells asegs m 0x12fde2 [C1 (Z_to_bv 8 0)]             (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa49f0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x13f69c)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13f738 [C8 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13f7ac [C1 (Z_to_bv 8 0)]             (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13f798 [C4 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells asegs m 0x600dd0 [C8 (Z_to_bv 64 4096)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13f79c [C1 (Z_to_bv 8 1)]             (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa49d8 [C8 (Z_to_bv 64 0xa6820)]        (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa4998 [C8 (Z_to_bv 64 0xa6860)]        (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6860 [C8 (Z_to_bv 64 0x19399)]        (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5638 [C8 (Z_to_bv 64 0x600b50)].       (* [comment removed for export] *)

Definition amalloc_statics_cells : list (Z * Z) :=
  [(0xa5608, 8); (0x5e0b20, 4); (0x12fde2, 1); (0xa49f0, 16); (0x13f738, 8); (0x13f7ac, 1); (0x13f798, 4); (0x600dd0, 8); (0x13f79c, 1); (0xa49d8, 8); (0xa4998, 8); (0xa6860, 8); (0xa5638, 8)].

Lemma amalloc_statics_transport : forall W m m',
  amalloc_statics m -> munch W m m' -> wmono asegs m m' ->
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
  (0xa5608 <= a < 0xa5610) \/ (0x5e0b20 <= a < 0x5e0b24) \/ (0x12fde2 <= a < 0x12fde3)
  \/ (0xa49f0 <= a < 0xa4a00) \/ (0x13f738 <= a < 0x13f740) \/ (0x13f7ac <= a < 0x13f7ad)
  \/ (0x13f798 <= a < 0x13f79d) \/ (0x600dd0 <= a < 0x600dd8) \/ (0xa49d8 <= a < 0xa49e0)
  \/ (0xa4998 <= a < 0xa49a0) \/ (0xa6860 <= a < 0xa6868) \/ (0xa5638 <= a < 0xa5640).

Lemma amalloc_statics_agree : forall m m',
  amalloc_statics m -> wmono asegs m m' -> (forall a, in_amalloc_statics a -> m' (wa a) = m (wa a)) -> amalloc_statics m'.
Proof. aceil.
  intros m m' S WM AG.
  eapply (amalloc_statics_transport [(0, 0xa4998); (0xa49a0, 0xa49d8); (0xa49e0, 0xa49f0); (0xa4a00, 0xa5608); (0xa5610, 0xa5638); (0xa5640, 0xa6860); (0xa6868, 0x12fde2); (0x12fde3, 0x13f738); (0x13f740, 0x13f798); (0x13f79d, 0x13f7ac); (0x13f7ad, 0x5e0b20); (0x5e0b24, 0x600dd0); (0x600dd8, 2^64)]); [exact S| | exact WM|].
  - intros x Hx. pose proof (bv_unsigned_in_range _ x) as R. change (bv_modulus 64) with (2^64) in R.
    rewrite <- (MState.Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply AG. unfold in_amalloc_statics. cbn in Hx. lia.
  - unfold amalloc_statics_cells. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
(* [comment removed for export] *)
Lemma guard_cell : forall m, exists g, rw_cells asegs m 0x600b50 [C8 g].
Proof.
  intros m.
  set (rd := fun i : nat => match mrd asegs m (wa (0x600b50 + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (RD : forall i, (i < 8)%nat -> mrd asegs m (wa (0x600b50 + Z.of_nat i)) = Some (rd i)).
  { intros i Hi. subst rd. cbn beta. unfold mrd. destruct (m (wa (0x600b50 + Z.of_nat i))) as [b|]; [reflexivity|].
    do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). exfalso. clear -Hi. lia. }
  assert (WV : forall i, 0 <= i < 8 -> wview asegs m (wa (0x600b50 + i)) <> None).
  { intros i Hi. unfold wview. destruct (m (wa (0x600b50 + i))); [discriminate|].
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by (clear -Hi; lia).
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate. }
  exists (le_bytes_to_word (map rd (seq 0 8))).
  split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite AF_kit3.le8_of_bytes by reflexivity.
    split; [clear; lia|]. split; [cbn; clear; lia|]. intros i Hi. cbn [length map seq] in Hi.
    rewrite nth_error_map. rewrite (nth_error_seq 0 8 i). replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add]. apply RD. exact Hi.
  - split; [clear; lia|]. split; [cbn; clear; lia|]. intros i Hi. apply WV. cbn in Hi. clear -Hi. lia.
Qed.

End RC__1.
