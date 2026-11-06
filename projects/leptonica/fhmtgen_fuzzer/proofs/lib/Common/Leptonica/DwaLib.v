(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptArith LeptArith2.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Loop.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma dowhile_loop : forall segs rom (HEAD EXIT : word)
    (I : bvmap 5 word -> (word -> option byte) -> Z -> Prop) (O : bvmap 5 word -> (word -> option byte) -> Prop) (N : Z),
  (forall regs m j, 0 <= j < N -> I regs m j ->
      (j + 1 < N /\ exists regs' m', msteps segs (mkst regs HEAD m rom) (mkst regs' HEAD m' rom) /\ I regs' m' (j + 1))
      \/ (j + 1 >= N /\ exists regs' m', msteps segs (mkst regs HEAD m rom) (mkst regs' EXIT m' rom) /\ O regs' m')) ->
  1 <= N -> forall regs m, I regs m 0 ->
  exists regs' m', msteps segs (mkst regs HEAD m rom) (mkst regs' EXIT m' rom) /\ O regs' m'.
Proof.
  intros segs rom HEAD EXIT I O N STEP HN.
  assert (G : forall (n : nat) j regs m, Z.of_nat (S n) = N - j -> 0 <= j -> I regs m j ->
                exists regs' m', msteps segs (mkst regs HEAD m rom) (mkst regs' EXIT m' rom) /\ O regs' m').
  { induction n as [|n IH]; intros j regs m Hn Hj HI.
    - destruct (STEP regs m j ltac:(lia) HI) as [[LT _] | [_ X]]; [lia | exact X].
    - destruct (STEP regs m j ltac:(lia) HI) as [[LT (r1 & m1 & RUN1 & HI1)] | [GE _]]; [| lia].
      destruct (IH (j + 1) r1 m1 ltac:(lia) ltac:(lia) HI1) as (r2 & m2 & RUN2 & HO).
      exists r2, m2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | exact HO]. }
  intros regs m H0. apply (G (Z.to_nat (N - 1)) 0 regs m); [lia | lia | exact H0].
Qed.
End Loop.

(* [comment removed for export] *)
Definition dwa_MInv (M : word -> option byte) (datad DN sp SPL : Z) (Mi : word -> option byte) : Prop :=
  (forall x : word, ~ (datad <= bv_unsigned x < datad + DN) -> ~ (sp <= bv_unsigned x < sp + SPL) -> Mi x = M x) /\ mem_grows M Mi.
Definition dwa_cell (segs : list Segment) (sp : Z) (Mi : word -> option byte) (off : Z) (v : word) : Prop :=
  rdn segs Mi (Z_to_bv 64 (sp + off)) 8 = Some (word_to_le_bytes 8 v).
Definition dwa_EX (M : word -> option byte) (datad DN sp SPL : Z) (gpv tpv : word) (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
  dwa_MInv M datad DN sp SPL Mi /\ getr regs 2 = Z_to_bv 64 sp /\ getr regs 3 = gpv /\ getr regs 4 = tpv.

(* [comment removed for export] *)
Lemma slli32_srli30 : forall x, 0 <= x < 2 ^ 32 -> v_srli (Z_to_bv 64 (x * 2 ^ 32)) 30 = Z_to_bv 64 (4 * x).
Proof.
  intros x Hx. rewrite zbv_srli by lia. f_equal.
  replace (x * 2 ^ 32) with ((4 * x) * 2 ^ 30) by (change (2 ^ 32) with (4 * 2 ^ 30); lia). apply Z.div_mul. lia.
Qed.

Lemma v_slliw_Z : forall a k, 0 <= k -> v_slliw (Z_to_bv 64 a) k = Z_to_bv 64 (sw32 (a * 2 ^ k)).
Proof.
  intros a k Hk. unfold v_slliw. rewrite u_zbv, sw32_eq, Z.shiftl_mul_pow2 by lia. unfold zx. f_equal.
  rewrite <- (sw32_mod (a mod 2 ^ 64 * 2 ^ k) ((a / 2 ^ 64) * 2 ^ 32 * 2 ^ k)). f_equal.
  pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)) as E. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32) in *. nia.
Qed.

(* [comment removed for export] *)
Lemma bytes4_word : forall bs : list byte, length bs = 4%nat -> exists v : word, bytes_le_to_Z bs = bv_unsigned v.
Proof.
  intros bs Hl. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hn. rewrite Hl in Hb.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb. rewrite u_Z2bv by lia. reflexivity.
Qed.
