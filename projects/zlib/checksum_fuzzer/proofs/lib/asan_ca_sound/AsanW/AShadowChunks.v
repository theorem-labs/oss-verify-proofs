(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW Require Import AImg ABase ABytes FsKit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CANSEC1. Context {rc : runConstT}.
Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv : Z * Z => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n H; cbn; [exact I|]. inversion H; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.


Lemma chunks_ablock_shadow : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad A + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH BODY LAST g Hg0 Hg.
  assert (S0 : 0x5f7000 <= shad A /\ shad A + n / 8 < 2^62) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (DB : 0 <= n / 8 /\ 8 * (n / 8) <= n /\ n < 8 * (n / 8) + 8 /\ n mod 8 = n - 8 * (n / 8)) by (Z.div_mod_to_equations; lia).
  destruct DB as (D1 & D2 & D3 & D6). destruct S0 as [S0 S1].
  destruct (Z.leb_spec (8 * g + 8) n) as [LE|GT].
  -
    destruct BODY as [[_ [B0 [B1 BR]]] _]. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
    rewrite repeat_length in B1, BR.
    specialize (BR (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BR by lia. rewrite <- mrd_high by lia. rewrite BR.
    rewrite nth_error_repeat by lia. reflexivity.
  -
    assert (g = n / 8) as -> by lia. assert (NE : n mod 8 <> 0) by lia.
    rewrite <- mrd_high by lia. pose proof (rw_cells_read asegs m _ _ 0%nat (C1 (Z_to_bv 8 (n mod 8))) (LAST NE) eq_refl) as R.
    cbn [csize cbytes] in R. rewrite Z.add_0_r in R.
    rewrite ov_rdn in R. cbn [rdn] in R.
    destruct (mrd asegs m (wa (shad A + n / 8))) as [b|] eqn:E; [| unfold mrd in E; rewrite E in R; discriminate].
    unfold mrd in E. rewrite E in R. injection R as ->. rewrite <- D6. reflexivity.
Qed.
End CANSEC1.
