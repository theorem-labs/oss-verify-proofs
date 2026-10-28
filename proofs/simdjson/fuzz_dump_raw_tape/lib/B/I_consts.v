(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition g_REAL_read : Z := 0x1705c8.
Definition e_musl_read : Z := 0x167814.

Definition RS_PAD : Z := 0x69a200.

Definition g_REAL_fwrite : Z := 0x1705d0.
Definition e_musl_fwrite : Z := 0x158210.
Definition LIT_BLK1 : Z := 0x21c40.
Definition LIT_BLK2 : Z := 0x16300.

Definition icpt_consts (m : mem) : Prop :=
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m g_REAL_read [C8 (Z_to_bv 64 e_musl_read)]
  /\ m2s_cells m
  /\ acc bsegs m RS_PAD 16
  /\ rw_cells bsegs m g_REAL_fwrite [C8 (Z_to_bv 64 e_musl_fwrite)]
  /\ acc bsegs m LIT_BLK1 128 /\ acc bsegs m LIT_BLK2 128.

Definition e_region_is_poisoned : Z := 0x826c8.

Definition region_in_mem (b n : Z) : Prop :=
  (0 <= b /\ b + n + 8 <= kLowMemEnd) \/ (kHighShadowEnd + 16 <= b /\ b + n + 8 <= kHighMemEnd).

Definition rip_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (beg size lo : Z),
  a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 size ->
  acc bsegs m beg size -> 0 < size <= 2^40 -> region_in_mem beg size -> m2s_cells m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> kHighShadowEnd + 8 <= lo -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 [(bv_unsigned sp - 80, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_region_is_poisoned) fc None m (seg_rom bsegs)).

Lemma acc_granule_zero : forall m a, a mod 8 = 0 -> acc bsegs m a 8 -> bytes_at bsegs m (shad a) [z8].
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

Lemma acc_word_zero : forall m a, a mod 64 = 0 -> acc bsegs m a 64 -> ro_cells bsegs m (shad a) [C8 (Z_to_bv 64 0)].
Proof.
  intros m a Ha H.
  assert (G : forall j, 0 <= j < 8 -> bytes_at bsegs m (shad a + j) [z8]).
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

Lemma shad_lit : forall a, shad a = a / 8 + 2147450880.
Proof. reflexivity. Qed.
