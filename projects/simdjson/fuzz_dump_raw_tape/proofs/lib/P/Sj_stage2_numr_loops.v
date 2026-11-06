(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto Sj_stage2_auto2 Sj_stage2_numkit Sj_stage2_numkit3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_cp | solve_load_image ].

Section NumRLoops.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variable Q : machine_state -> Prop.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 <= CP)%Z.
  Notation rl := (blen t).

  Lemma numr_L1 : forall (fuel : nat) p xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 CP (zbytes (crs t)) -> (0 <= p < rl)%Z -> (rl - p < Z.of_nat fuel)%Z ->
    (forall p' ya2 yt3 yt0 yt4, (p < p' <= rl)%Z ->
       evt psegs Q (S2R E 0x3e198 xra yt0 (Z_to_bv 64 (10)) (Z_to_bv 64 (CP + p')) xs0 xs1 xa0 xa1 ya2 xa3 (Z_to_bv 64 (CP + p')) xa5 (Z_to_bv 64 (B (crs t) p')) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 xt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x3e174 xra xt0 (Z_to_bv 64 (10)) (Z_to_bv 64 (CP + p)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using TOK CP0.
    induction fuel as [|fuel IH]; intros p xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 CPRO HP HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (B_range (crs t) (p + 1) BOK) as HB1.
    pose proof (crs_blen t) as CBL. rewrite zbytes_length in CBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + p + 1)%Z with (CP + (p + 1))%Z by lia.
      eapply (IH (p + 1)%Z); [exact CPRO | lia | lia |].
      intros p' ya2 yt3 yt0 yt4 HP'. eapply K. lia.
    - replace (CP + p + 1)%Z with (CP + (p + 1))%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numr_L2 : forall (fuel : nat) p q xra xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 CP (zbytes (crs t)) -> (0 <= q <= rl)%Z -> (rl - q < Z.of_nat fuel)%Z ->
    (forall q' ys9 ys10 ys11 yra ya0 ya1 ya2 yt6, (q <= q' <= rl)%Z ->
       evt psegs Q (S2R E 0x3e678 yra (Z_to_bv 64 (1085102592571150095)) (Z_to_bv 64 (434041037028460038)) (Z_to_bv 64 (q' - p)) xs0 xs1 ya0 ya1 ya2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 ys9 ys10 ys11 (Z_to_bv 64 (V8 (B (crs t) q') (B (crs t) (q' + 1)) (B (crs t) (q' + 2)) (B (crs t) (q' + 3)) (B (crs t) (q' + 4)) (B (crs t) (q' + 5)) (B (crs t) (q' + 6)) (B (crs t) (q' + 7)))) (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) yt6 F fc m1)) ->
    evt psegs Q (S2R E 0x3e5d4 xra (Z_to_bv 64 (1085102592571150095)) (Z_to_bv 64 (434041037028460038)) (Z_to_bv 64 (q - p - 8)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) (Z_to_bv 64 (CP + q)) F fc m1).
  Proof using TOK CP0.
    induction fuel as [|fuel IH]; intros p q xra xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 F fc m1 CPRO HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) q BOK) as HB0. pose proof (B_range (crs t) (q + 1) BOK) as HB1. pose proof (B_range (crs t) (q + 2) BOK) as HB2.
    pose proof (B_range (crs t) (q + 3) BOK) as HB3. pose proof (B_range (crs t) (q + 4) BOK) as HB4. pose proof (B_range (crs t) (q + 5) BOK) as HB5.
    pose proof (B_range (crs t) (q + 6) BOK) as HB6. pose proof (B_range (crs t) (q + 7) BOK) as HB7.
    srun_to 0x3e658%Z.
    replace (CP + q)%Z with (CP + (q + 0))%Z by lia. nnorm. fold_V8. replace (q + 0)%Z with q by lia.
    srun.
    if_cases KC; zify_cond KC.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR. rewrite ?(Z.mod_small _ _ HVR) in KC.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL.
      assert (HNZ : (q + 7 < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + q + 8)%Z with (CP + (q + 8))%Z by lia.
      replace (q - p - 8 + 8)%Z with (q + 8 - p - 8)%Z by lia.
      eapply (IH p (q + 8)%Z); [exact CPRO | lia | lia |].
      intros q' ys9 ys10 ys11 yra ya0 ya1 ya2 yt6 HQ'. eapply K. lia.
    - replace (q - p - 8 + 8)%Z with (q - p)%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numr_L3 : forall (fuel : nat) q xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 CP (zbytes (crs t)) -> (0 <= q < rl)%Z -> (rl - q < Z.of_nat fuel)%Z ->
    (forall q' ya2 ya0 yt0 ya1, (q < q' <= rl)%Z ->
       evt psegs Q (S2R E 0x3eedc xra yt0 (Z_to_bv 64 (10)) (Z_to_bv 64 (CP + q')) xs0 xs1 ya0 ya1 ya2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (B (crs t) q')) (Z_to_bv 64 (CP + q')) xt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x3eeb8 xra xt0 (Z_to_bv 64 (10)) (Z_to_bv 64 (CP + q)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using TOK CP0.
    induction fuel as [|fuel IH]; intros q xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 CPRO HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (B_range (crs t) (q + 1) BOK) as HB1.
    pose proof (crs_blen t) as CBL. rewrite zbytes_length in CBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q + 1 < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact CPRO | lia | lia |].
      intros q' ya2 ya0 yt0 ya1 HQ'. eapply K. lia.
    - replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numr_L4 : forall (fuel : nat) q0 c xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 CP (zbytes (crs t)) -> (0 <= q0)%Z -> (0 <= c)%Z -> (q0 + c < rl)%Z -> (rl - (q0 + c) < Z.of_nat fuel)%Z ->
    (forall c' ya0 ya4 ya7, (c < c')%Z -> (q0 + c' <= rl)%Z ->
       evt psegs Q (S2R E 0x3f560 xra xt0 xt1 (Z_to_bv 64 (10)) xs0 xs1 ya0 xa1 xa2 xa3 ya4 xa5 (Z_to_bv 64 (CP + q0)) ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (B (crs t) (q0 + c'))) (Z_to_bv 64 (c')) xt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x3f53c xra xt0 xt1 (Z_to_bv 64 (10)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (CP + q0)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (c)) xt5 xt6 F fc m1).
  Proof using TOK CP0.
    induction fuel as [|fuel IH]; intros q0 c xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 F fc m1 CPRO HQ0 HC HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (B_range (crs t) (q0 + c + 1) BOK) as HB1.
    pose proof (crs_blen t) as CBL. rewrite zbytes_length in CBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q0 + c + 1 < rl)%Z) by (apply Bc_lt; lia).
      eapply (IH q0 (c + 1)%Z); [exact CPRO | lia | lia | lia | lia |].
      intros c' ya0 ya4 ya7 HC' HQ'. eapply K; lia.
    - replace (q0 + c + 1)%Z with (q0 + (c + 1))%Z by lia.
      eapply K; lia.
  Qed.

  Lemma numr_L5 : forall (fuel : nat) q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 CP (zbytes (crs t)) -> (0 <= q <= rl)%Z -> (rl - q < Z.of_nat fuel)%Z ->
    (forall ya0 ya6, evt psegs Q (S2R E 0x4054c xra xt0 xt1 xt2 xs0 xs1 ya0 xa1 xa2 xa3 xa4 xa5 ya6 (Z_to_bv 64 (48)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x40540 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (CP + q + 17)) (Z_to_bv 64 (48)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using TOK CP0.
    induction fuel as [|fuel IH]; intros q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 CPRO HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (B_range (crs t) q BOK) as HB0.
    pose proof (crs_blen t) as CBL. rewrite zbytes_length in CBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + q + 18)%Z with (CP + (q + 1) + 17)%Z by lia.
      eapply (IH (q + 1)%Z); [exact CPRO | lia | lia |].
      intros ya0 ya6. eapply K.
    - eapply K.
  Qed.

  Lemma numr_L6 : forall (fuel : nat) q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 CP (zbytes (crs t)) -> (0 <= q <= rl)%Z -> (rl - q < Z.of_nat fuel)%Z ->
    (forall ya3 yt1 ya5, evt psegs Q (S2R E 0x3f5c0 xra xt0 yt1 xt2 xs0 xs1 xa0 xa1 xa2 ya3 (Z_to_bv 64 (48)) ya5 (Z_to_bv 64 (46)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x3f5a8 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (48)) (Z_to_bv 64 (CP + q)) (Z_to_bv 64 (46)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using TOK CP0.
    induction fuel as [|fuel IH]; intros q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 CPRO HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (B_range (crs t) q BOK) as HB0.
    pose proof (crs_blen t) as CBL. rewrite zbytes_length in CBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact CPRO | lia | lia |].
      intros ya3 yt1 ya5. eapply K.
    - srun.
      if_cases KC2; zify_cond KC2.
      + assert (HNZ : (q < rl)%Z) by (apply Bc_lt; lia).
        replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
        eapply (IH (q + 1)%Z); [exact CPRO | lia | lia |].
        intros ya3 yt1 ya5. eapply K.
      + eapply K.
  Qed.
End NumRLoops.
