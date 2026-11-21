(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import ZStep ZMem ZSysLite ZCall ZCallL ZArr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Section Generic.
Variable segs : list Segment.

Definition wr_rd_ok : Prop :=
  forall seg, In seg segs -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis WR : wr_rd_ok.

Lemma find_segment_In : forall sl a n seg, find_segment sl a n = Some seg -> In seg sl.
Proof.
  induction sl as [|s sl IH]; cbn; intros a n seg H; [discriminate|].
  destruct (_ && _); [injection H as ->; now left | right; eapply IH; exact H].
Qed.

Lemma wview_rdn1 : forall M a, wview segs M a <> None -> exists b, rdn segs M a 1 = Some [b].
Proof.
  intros M a H. unfold wview in H. cbn [rdn].
  destruct (M a) as [b|] eqn:E.
  - exists b. reflexivity.
  - destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:F; [|congruence].
    destruct (seg_writable seg) eqn:W; [|congruence].
    destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:B; [|congruence].
    exists b. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite F.
    rewrite (WR seg (find_segment_In _ _ _ _ F) W). change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    rewrite B. reflexivity.
Qed.

Lemma mem_wr_readable_nat : forall n M a,
  mem_wr segs M a (Z.of_nat n) -> exists bs, mem_is segs M a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros M a H.
  - exists []. split; [reflexivity | reflexivity].
  - destruct (wview_rdn1 M (w64 a) ltac:(replace (w64 a) with (w64 (a + 0)) by (f_equal; lia); apply H; lia)) as [b Hb].
    destruct (IH M (a + 1) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia)) as [bs [Hbs Hlen]].
    exists (b :: bs). split; [| cbn; lia].
    unfold mem_is in *. cbn [length rdn]. cbn [rdn] in Hb.
    destruct (match M (w64 a) with Some b0 => Some b0 | None => seg_rom segs (w64 a) end); [|discriminate].
    injection Hb as ->. rewrite Hlen in *.
    replace (w64 a + 1)%bv with (w64 (a + 1)); [rewrite Hbs; reflexivity|].
    rewrite word1_nat, w64_add_nat. reflexivity.
Qed.

Lemma mem_wr_readable : forall M a n,
  mem_wr segs M a n -> 0 <= n -> exists bs, mem_is segs M a bs /\ Z.of_nat (length bs) = n.
Proof.
  intros M a n H Hn. destruct (mem_wr_readable_nat (Z.to_nat n) M a ltac:(rewrite Z2Nat.id by lia; exact H)) as [bs [A B]].
  exists bs. split; [exact A | lia].
Qed.

Lemma mem_wr_rdn1 : forall M a n i,
  mem_wr segs M a n -> 0 <= i < n -> exists b, rdn segs M (w64 (a + i)) 1 = Some [b].
Proof. intros M a n i H Hi. apply wview_rdn1. apply H. exact Hi. Qed.

Lemma mem_wr_arr_exists : forall M a n,
  mem_wr segs M a n -> 0 <= a -> 0 <= n -> a + n <= two64 ->
  exists f, mem_arr 1 segs M a n f /\ (forall i, 0 <= f i < 256).
Proof.
  intros M a n H Ha Hn Han. destruct (mem_wr_readable M a n H Hn) as [bs [A B]].
  exists (fun i => bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))). split.
  - rewrite <- B. apply mem_arr8_of_bytes; [exact A | exact Ha | lia].
  - intros i. pose proof (bv_unsigned_in_range _ (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as R.
    change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma mem_wr_u32_exists : forall M a, mem_wr segs M a 4 -> exists v, mem_u32 segs M a v /\ 0 <= v < 4294967296.
Proof.
  intros M a H. destruct (mem_wr_readable_nat 4 M a H) as [bs [A B]].
  exists (bytes_le_to_Z bs). split.
  - unfold mem_u32. rewrite <- B, bytes_roundtrip. exact A.
  - pose proof (bytes_le_to_Z_bound bs) as R. pose proof (bytes_le_to_Z_nonneg bs) as R0.
    rewrite B in R. cbn in R. lia.
Qed.

Lemma mem_wr_u64_exists : forall M a, mem_wr segs M a 8 -> exists v, mem_u64 segs M a v /\ 0 <= v < 18446744073709551616.
Proof.
  intros M a H. destruct (mem_wr_readable_nat 8 M a H) as [bs [A B]].
  exists (bytes_le_to_Z bs). split.
  - unfold mem_u64. rewrite <- B, bytes_roundtrip. exact A.
  - pose proof (bytes_le_to_Z_bound bs) as R. pose proof (bytes_le_to_Z_nonneg bs) as R0.
    rewrite B in R. cbn in R. lia.
Qed.

Lemma mem_wr_u16_exists : forall M a, mem_wr segs M a 2 -> exists v, mem_u16 segs M a v /\ 0 <= v < 65536.
Proof.
  intros M a H. destruct (mem_wr_readable_nat 2 M a H) as [bs [A B]].
  exists (bytes_le_to_Z bs). split.
  - unfold mem_u16. rewrite <- B, bytes_roundtrip. exact A.
  - pose proof (bytes_le_to_Z_bound bs) as R. pose proof (bytes_le_to_Z_nonneg bs) as R0.
    rewrite B in R. cbn in R. lia.
Qed.

Lemma mem_wr_u8_exists : forall M a, mem_wr segs M a 1 -> exists v, mem_u8 segs M a v /\ 0 <= v < 256.
Proof.
  intros M a H. destruct (mem_wr_readable_nat 1 M a H) as [bs [A B]].
  exists (bytes_le_to_Z bs). split.
  - unfold mem_u8. rewrite <- B, bytes_roundtrip. exact A.
  - pose proof (bytes_le_to_Z_bound bs) as R. pose proof (bytes_le_to_Z_nonneg bs) as R0.
    rewrite B in R. cbn in R. lia.
Qed.
End Generic.
End FXG.
