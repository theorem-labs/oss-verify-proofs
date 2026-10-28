(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes FsKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma wr_at_sub' : forall m a n a' n', wr_at bsegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
Lemma chunks_ablock_shadow : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  (n mod 8 <> 0 -> rw_cells bsegs m (shad A + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH BODY LAST g Hg0 Hg.
  assert (S0 : 0x625000 <= shad A /\ shad A + n / 8 < 2^62) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (DB : 0 <= n / 8 /\ 8 * (n / 8) <= n /\ n < 8 * (n / 8) + 8 /\ n mod 8 = n - 8 * (n / 8)) by (Z.div_mod_to_equations; lia).
  destruct DB as (D1 & D2 & D3 & D6). destruct S0 as [S0 S1].
  destruct (Z.leb_spec (8 * g + 8) n) as [LE|GT].
  - (* [comment removed for export] *)
    destruct BODY as [[_ [B0 [B1 BR]]] _]. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
    rewrite repeat_length in B1, BR.
    specialize (BR (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BR by lia. rewrite <- mrd_high by lia. rewrite BR.
    rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    assert (g = n / 8) as -> by lia. assert (NE : n mod 8 <> 0) by lia.
    rewrite <- mrd_high by lia. pose proof (rw_cells_read bsegs m _ _ 0%nat (C1 (Z_to_bv 8 (n mod 8))) (LAST NE) eq_refl) as R.
    cbn [csize cbytes] in R. rewrite Z.add_0_r in R.
    (* [comment removed for export] *)
    rewrite ov_rdn in R. cbn [rdn] in R.
    destruct (mrd bsegs m (wa (shad A + n / 8))) as [b|] eqn:E; [| unfold mrd in E; rewrite E in R; discriminate].
    unfold mrd in E. rewrite E in R. injection R as ->. rewrite <- D6. reflexivity.
Qed.
End CANSEC1.
