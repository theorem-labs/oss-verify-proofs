(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto Sj_stage2_auto2 Sj_stage2_numkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].

Section NumOLoops.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Variable Q : machine_state -> Prop.

  Lemma numo_L1 : forall (fuel : nat) p xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= p < e_len E)%Z -> (e_len E - p < Z.of_nat fuel)%Z ->
    (forall p' ya2 yt1 yt4 yt5, (p < p' <= e_len E)%Z ->
       evt psegs Q (S2R E 0x438f4 xra xt0 yt1 (Z_to_bv 64 (10)) xs0 xs1 xa0 xa1 ya2 xa3 xa4 (Z_to_bv 64 (e_BUF E + p')) xa6 (Z_to_bv 64 (B bs p')) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (e_BUF E + p')) yt4 yt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x438d0 xra xt0 xt1 (Z_to_bv 64 (10)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (e_BUF E + p)) xt4 xt5 xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros p xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 F fc m1 BUFRO HP HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs (p + 1) BOK) as HB1.
    pose proof (padded_bytes_blen bs) as PBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
      eapply (IH (p + 1)%Z); [exact BUFRO | lia | lia |].
      intros p' ya2 yt1 yt4 yt5 HP'. eapply K. lia.
    - replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numo_L2 : forall (fuel : nat) p q xra xt0 xt1 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q <= e_len E)%Z -> (e_len E - q < Z.of_nat fuel)%Z ->
    (forall q' ys3 ys2 ya1 yt1 ya6 yt0 ya2 ys5, (q <= q' <= e_len E)%Z ->
       evt psegs Q (S2R E 0x43ad0 xra yt0 yt1 (Z_to_bv 64 (1085102592571150095)) xs0 (Z_to_bv 64 (3689348814741910323)) xa0 ya1 ya2 xa3 xa4 xa5 ya6 xa7 ys2 ys3 xs4 ys5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (434041037028460038)) (Z_to_bv 64 (q' - p)) (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (V8 (B bs q') (B bs (q' + 1)) (B bs (q' + 2)) (B bs (q' + 3)) (B bs (q' + 4)) (B bs (q' + 5)) (B bs (q' + 6)) (B bs (q' + 7)))) F fc m1)) ->
    evt psegs Q (S2R E 0x43a2c xra xt0 xt1 (Z_to_bv 64 (1085102592571150095)) xs0 (Z_to_bv 64 (3689348814741910323)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E + q)) xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (434041037028460038)) (Z_to_bv 64 (q - p - 8)) (Z_to_bv 64 (17361641481138401520)) xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros p q xra xt0 xt1 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt6 F fc m1 BUFRO HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (padded_bytes_blen bs) as PBL.
    pose proof (B_range bs q BOK) as HB0. pose proof (B_range bs (q + 1) BOK) as HB1. pose proof (B_range bs (q + 2) BOK) as HB2.
    pose proof (B_range bs (q + 3) BOK) as HB3. pose proof (B_range bs (q + 4) BOK) as HB4. pose proof (B_range bs (q + 5) BOK) as HB5.
    pose proof (B_range bs (q + 6) BOK) as HB6. pose proof (B_range bs (q + 7) BOK) as HB7.
    srun_to 0x43ab0%Z.
    replace (e_BUF E + q)%Z with (e_BUF E + (q + 0))%Z by lia. nnorm. fold_V8. replace (q + 0)%Z with q by lia.
    srun.
    if_cases KC; zify_cond KC.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR. rewrite ?(Z.mod_small _ _ HVR) in KC.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL.
      assert (HNZ : (q + 7 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + q + 8)%Z with (e_BUF E + (q + 8))%Z by lia.
      replace (q - p - 8 + 8)%Z with (q + 8 - p - 8)%Z by lia.
      eapply (IH p (q + 8)%Z); [exact BUFRO | lia | lia |].
      intros q' ys3 ys2 ya1 yt1 ya6 yt0 ya2 ys5 HQ'. eapply K. lia.
    - replace (q - p - 8 + 8)%Z with (q - p)%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numo_L3 : forall (fuel : nat) q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q < e_len E)%Z -> (e_len E - q < Z.of_nat fuel)%Z ->
    (forall q' ya2 ya1 yt2 ya6, (q < q' <= e_len E)%Z ->
       evt psegs Q (S2R E 0x43b80 xra xt0 xt1 yt2 xs0 xs1 xa0 ya1 ya2 xa3 xa4 (Z_to_bv 64 (e_BUF E + q')) ya6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (B bs q')) (Z_to_bv 64 (10)) (Z_to_bv 64 (e_BUF E + q')) xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x43b5c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (10)) (Z_to_bv 64 (e_BUF E + q)) xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt6 F fc m1 BUFRO HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs (q + 1) BOK) as HB1.
    pose proof (padded_bytes_blen bs) as PBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact BUFRO | lia | lia |].
      intros q' ya2 ya1 yt2 ya6 HQ'. eapply K. lia.
    - replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numo_L4 : forall (fuel : nat) q0 c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q0)%Z -> (0 <= c)%Z -> (q0 + c < e_len E)%Z -> (e_len E - (q0 + c) < Z.of_nat fuel)%Z ->
    (forall c' ya1 ya5 yt0, (c < c')%Z -> (q0 + c' <= e_len E)%Z ->
       evt psegs Q (S2R E 0x43da8 xra yt0 xt1 xt2 xs0 xs1 xa0 ya1 xa2 xa3 xa4 ya5 xa6 (Z_to_bv 64 (e_BUF E + q0)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (B bs (q0 + c'))) (Z_to_bv 64 (10)) (Z_to_bv 64 (c')) xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x43d84 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (e_BUF E + q0)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 (10)) (Z_to_bv 64 (c)) xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros q0 c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt6 F fc m1 BUFRO HQ0 HC HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs (q0 + c + 1) BOK) as HB1.
    pose proof (padded_bytes_blen bs) as PBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q0 + c + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
      eapply (IH q0 (c + 1)%Z); [exact BUFRO | lia | lia | lia | lia |].
      intros c' ya1 ya5 yt0 HC' HQ'. eapply K; lia.
    - replace (q0 + c + 1)%Z with (q0 + (c + 1))%Z by lia.
      eapply K; lia.
  Qed.

  Lemma numo_L5 : forall (fuel : nat) q xra xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q <= e_len E)%Z -> (e_len E - q < Z.of_nat fuel)%Z ->
    (forall ya1 ya7, evt psegs Q (S2R E 0x44150 xra (Z_to_bv 64 (48)) xt1 xt2 xs0 xs1 xa0 ya1 xa2 xa3 xa4 xa5 xa6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x44144 xra (Z_to_bv 64 (48)) xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (e_BUF E + q + 17)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros q xra xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 BUFRO HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs q BOK) as HB0.
    pose proof (padded_bytes_blen bs) as PBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + q + 18)%Z with (e_BUF E + (q + 1) + 17)%Z by lia.
      eapply (IH (q + 1)%Z); [exact BUFRO | lia | lia |].
      intros ya1 ya7. eapply K.
    - eapply K.
  Qed.

  Lemma numo_L6 : forall (fuel : nat) q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q <= e_len E)%Z -> (e_len E - q < Z.of_nat fuel)%Z ->
    (forall ya4 yt2 ya5, evt psegs Q (S2R E 0x43e20 xra xt0 xt1 yt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 (48)) ya4 ya5 (Z_to_bv 64 (46)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt psegs Q (S2R E 0x43e08 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 (48)) xa4 (Z_to_bv 64 (e_BUF E + q)) (Z_to_bv 64 (46)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa4 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 BUFRO HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs q BOK) as HB0.
    pose proof (padded_bytes_blen bs) as PBL.
    srun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact BUFRO | lia | lia |].
      intros ya4 yt2 ya5. eapply K.
    - srun.
      if_cases KC2; zify_cond KC2.
      + assert (HNZ : (q < e_len E)%Z) by (apply B_nz_lt; lia).
        replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
        eapply (IH (q + 1)%Z); [exact BUFRO | lia | lia |].
        intros ya4 yt2 ya5. eapply K.
      + eapply K.
  Qed.
End NumOLoops.
