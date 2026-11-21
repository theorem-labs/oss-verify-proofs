(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg ABase ADepot_iface ADepot.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require HexScanFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

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

End CANSEC1.
Lemma zscanN_fastE : forall s fuel base n, zscanN s fuel base n = HexScanFast.gscanN (HexScanFast.byte_zero s) fuel base n.
Proof. intros s fuel. induction fuel as [|f IH]; intros base n; cbn [zscanN HexScanFast.gscanN]; [reflexivity|]. rewrite !IH. reflexivity. Qed.
Notation S3 := Tgt_zlib_uncompress3_fuzzer_both_seg_bytes_003 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Lemma tab_scan : zscanN Tgt_zlib_uncompress3_fuzzer_both_seg_bytes_003 64 0xe8d98 4194304 = true.
Proof. rewrite zscanN_fastE. apply HexScanFast.zscanN_of_I; [vm_cast_no_check (eq_refl true) | vm_compute; reflexivity]. Qed.

Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length Tgt_zlib_uncompress3_fuzzer_both_seg_bytes_003) / 2) = 0x5ac000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma tab_byte_at : forall off : N, (0xe8d98 <= off < 0xe8d98 + 4194304)%N ->
  segment_byte_at (seg_bytes Tgt_zlib_uncompress3_fuzzer_both_segment_003) off = Some (Z_to_bv 8 0).
Proof.
  intros off Hoff. cbn [seg_bytes Tgt_zlib_uncompress3_fuzzer_both_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (off <? 0x5ac000)%N with true by (symmetry; apply N.ltb_lt; lia).
  replace off with (0xe8d98 + (off - 0xe8d98))%N by lia.
  apply (zscanN_sound _ 64 _ 4194304 tab_scan). lia.
Qed.

End CANSEC2.
