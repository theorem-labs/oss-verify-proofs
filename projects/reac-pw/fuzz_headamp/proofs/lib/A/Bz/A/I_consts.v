(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/I_consts.v, with its module paths and addresses changed; 6 of its 57 lines of code are new or changed and 19 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_consts.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 1 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition e_region_is_poisoned : Z := 0x54888.

(* [comment removed for export] *)
Definition region_in_mem (b n : Z) : Prop :=
  (0 <= b /\ b + n <= kLowMemEnd /\ b + 7 <= kLowMemEnd) \/ (kHighShadowEnd < b /\ b + n <= kHighMemEnd /\ b + 7 <= kHighMemEnd).

Definition rip_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (beg size lo : Z),
  a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 size ->
  acc asegs m beg size -> 0 < size <= 2^40 -> region_in_mem beg size -> m2s_cells m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> kHighShadowEnd < lo -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 80, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_region_is_poisoned) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma acc_granule_zero : forall m a, a mod 8 = 0 -> acc asegs m a 8 -> bytes_at asegs m (shad a) [z8].
Proof.
  intros m a Ha H. destruct (H 7 ltac:(lia)) as (b & Hb & Hok).
  assert (E : shad (a + 7) = shad a).
  { unfold shad. f_equal. pose proof (Z.div_mod a 8 ltac:(lia)).
    replace (a + 7) with (7 + (a / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
  rewrite E in Hb.
  assert (E7 : (a + 7) mod 8 = 7).
  { replace (a + 7) with (7 + (a / 8) * 8) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia).
    rewrite Z.mod_add by lia. reflexivity. }
  destruct Hok as [H0|[H1 H2]]; [| rewrite E7 in H2; lia].
  replace z8 with b; [exact Hb|]. apply bv_eq. rewrite H0. reflexivity.
Qed.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat z8 8.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma acc_word_zero : forall m a, a mod 64 = 0 -> acc asegs m a 64 -> ro_cells asegs m (shad a) [C8 (Z_to_bv 64 0)].
Proof.
  intros m a Ha H.
  assert (G : forall j, 0 <= j < 8 -> bytes_at asegs m (shad a + j) [z8]).
  { intros j Hj. replace (shad a + j) with (shad (a + 8 * j)).
    - apply acc_granule_zero.
      + apply Z.mod_divide; [lia|]. exists (j + (a / 64) * 8). pose proof (Z.div_mod a 64 ltac:(lia)). lia.
      + intros i Hi. replace (a + 8 * j + i) with (a + (8 * j + i)) by lia. apply H. lia.
    - unfold shad. replace (a + 8 * j) with (j * 8 + a) by lia. rewrite Z.div_add_l by lia. lia. }
  split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r, le8_zero.
  destruct (G 0 ltac:(lia)) as (B0 & _ & _).
  split; [lia|]. split.
  { rewrite repeat_length. destruct (G 7 ltac:(lia)) as (_ & B7 & _). cbn [length] in B7. lia. }
  intros i Hi. rewrite repeat_length in Hi.
  destruct (G (Z.of_nat i) ltac:(lia)) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)).
  rewrite Z.add_0_r in Hb. rewrite Hb. cbn [nth_error].
  rewrite nth_error_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shad_lit : forall a, shad a = a / 8 + 2147450880.
Proof. reflexivity. Qed.
