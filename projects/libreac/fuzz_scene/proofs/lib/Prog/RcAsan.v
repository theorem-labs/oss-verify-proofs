From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Frame.
Import ListNotations.
Open Scope Z_scope.

Definition asan_shadow (off a : Z) : Z := a / 8 + off.

Definition asan_ok (k : byte) (a : Z) : Prop := bv_signed k = 0 \/ a mod 8 < bv_signed k.

Definition asan_rt (segs : list Segment) (m : word -> option byte) (gotK cellK off : Z) (W : list ivl) : Prop :=
  bytes_at segs m gotK (le8 (Z_to_bv 64 cellK)) /\ bytes_at segs m cellK (le8 (Z_to_bv 64 off)) /\
  (forall x, gotK <= x < gotK + 8 -> outside W x) /\ (forall x, cellK <= x < cellK + 8 -> outside W x).

Definition asan_shadow_rd (segs : list Segment) (m : word -> option byte) (off a n : Z) (W : list ivl) : Prop :=
  forall i, 0 <= i < n ->
    outside W (asan_shadow off (a + i)) /\ exists k : byte, bytes_at segs m (asan_shadow off (a + i)) [k].

Definition asan_addressable (segs : list Segment) (m : word -> option byte) (off a n : Z) : Prop :=
  forall i (k : byte), 0 <= i < n -> bytes_at segs m (asan_shadow off (a + i)) [k] -> asan_ok k (a + i).

Definition asan_rt3 (segs : list Segment) (m : word -> option byte) (off a n : Z) : Prop :=
  forall i (k : byte), 0 <= i < n -> bytes_at segs m (asan_shadow off (a + i)) [k] -> bv_signed k <= 7.
