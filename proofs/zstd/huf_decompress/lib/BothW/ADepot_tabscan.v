(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ADepot_iface ADepot.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation S3 := AsanUbsan_seg_bytes_003 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Lemma tab_scan : zscanN AsanUbsan_seg_bytes_003 64 0xe91d8 4194304 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)

Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma tab_byte_at : forall off : N, (0xe91d8 <= off < 0xe91d8 + 4194304)%N ->
  segment_byte_at (seg_bytes AsanUbsan_segment_003) off = Some (Z_to_bv 8 0).
Proof.
  intros off Hoff. cbn [seg_bytes AsanUbsan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (off <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
  replace off with (0xe91d8 + (off - 0xe91d8))%N by lia.
  apply (zscanN_sound _ 64 _ 4194304 tab_scan). lia.
Qed.

End CANSEC2.
