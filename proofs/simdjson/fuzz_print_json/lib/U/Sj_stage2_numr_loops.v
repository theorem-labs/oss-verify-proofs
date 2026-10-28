(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr.
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
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Notation rl := (blen t).

  Lemma numr_L1 : forall (fuel : nat) p xra xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 CP (zbytes (crs t)) -> (0 <= p < rl)%Z -> (rl - p < Z.of_nat fuel)%Z ->
    (forall p' ya2 yt4 ya6 yt5, (p < p' <= rl)%Z ->
       evt usegs Q (S2R E 0x43958 xra (Z_to_bv 64 (CP + p')) (Z_to_bv 64 (2)) (Z_to_bv 64 (10)) xs0 xs1 xa0 xa1 ya2 xa3 (Z_to_bv 64 (CP + p')) xa5 ya6 (Z_to_bv 64 (B (crs t) p')) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (CP + p')) yt4 yt5 xt6 F fc m1)) ->
    evt usegs Q (S2R E 0x43928 xra (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (2)) (Z_to_bv 64 (10)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (CP + p)) xt4 xt5 xt6 F fc m1).
  Proof using OK TOK CP0 CPHI.
    induction fuel as [|fuel IH]; intros p xra xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 F fc m1 CPRO HP HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL. s2_env OK.
    pose proof (B_range (crs t) (p + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + p + 1)%Z with (CP + (p + 1))%Z by lia.
      eapply (IH (p + 1)%Z); [exact CPRO | lia | lia |].
      intros p' ya2 yt4 ya6 yt5 HP'. eapply K. lia.
    - replace (CP + p + 1)%Z with (CP + (p + 1))%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numr_L2 : forall (fuel : nat) p q xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 CP (zbytes (crs t)) -> (0 <= q <= rl)%Z -> (rl - q < Z.of_nat fuel)%Z ->
    (forall q' ys6 ys7 ys8 ys9 ys11 yra ya2 yt5, (q <= q' <= rl)%Z ->
       evt usegs Q (S2R E 0x43d38 yra (Z_to_bv 64 (V8 (B (crs t) q') (B (crs t) (q' + 1)) (B (crs t) (q' + 2)) (B (crs t) (q' + 3)) (B (crs t) (q' + 4)) (B (crs t) (q' + 5)) (B (crs t) (q' + 6)) (B (crs t) (q' + 7)))) (Z_to_bv 64 (1085102592571150095)) (Z_to_bv 64 (434041037028460038)) xs0 xs1 xa0 xa1 ya2 xa3 xa4 xa5 (Z_to_bv 64 (q' - p)) xa7 xs2 xs3 xs4 xs5 ys6 ys7 ys8 ys9 xs10 ys11 (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) yt5 xt6 F fc m1)) ->
    evt usegs Q (S2R E 0x43c94 xra xt0 (Z_to_bv 64 (1085102592571150095)) (Z_to_bv 64 (434041037028460038)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (q - p - 8)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) (Z_to_bv 64 (CP + q)) xt6 F fc m1).
  Proof using OK TOK CP0 CPHI.
    induction fuel as [|fuel IH]; intros p q xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 F fc m1 CPRO HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL. s2_env OK.
    pose proof (B_range (crs t) q BOK) as HB0. pose proof (B_range (crs t) (q + 1) BOK) as HB1. pose proof (B_range (crs t) (q + 2) BOK) as HB2.
    pose proof (B_range (crs t) (q + 3) BOK) as HB3. pose proof (B_range (crs t) (q + 4) BOK) as HB4. pose proof (B_range (crs t) (q + 5) BOK) as HB5.
    pose proof (B_range (crs t) (q + 6) BOK) as HB6. pose proof (B_range (crs t) (q + 7) BOK) as HB7.
    ngrun_to 0x43d18%Z.
    replace (CP + q)%Z with (CP + (q + 0))%Z by lia. nnorm. fold_V8. replace (q + 0)%Z with q by lia.
    ngrun.
    if_cases KC; zify_cond KC.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR. rewrite ?(Z.mod_small _ _ HVR) in KC.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL.
      assert (HNZ : (q + 7 < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + q + 8)%Z with (CP + (q + 8))%Z by lia.
      replace (q - p - 8 + 8)%Z with (q + 8 - p - 8)%Z by lia.
      eapply (IH p (q + 8)%Z); [exact CPRO | lia | lia |].
      intros q' ys6 ys7 ys8 ys9 ys11 yra ya2 yt5 HQ'. eapply K. lia.
    - replace (q - p - 8 + 8)%Z with (q - p)%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numr_L3 : forall (fuel : nat) p d xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 CP (zbytes (crs t)) -> (0 <= p)%Z -> (0 <= d)%Z -> (p + d < rl)%Z -> (rl - (p + d) < Z.of_nat fuel)%Z ->
    (forall d' ya2 yt5 yt1 yt6, (d < d')%Z -> (p + d' <= rl)%Z ->
       evt usegs Q (S2R E 0x44c90 xra (Z_to_bv 64 (B (crs t) (p + d'))) yt1 (Z_to_bv 64 (CP + p + 1)) xs0 xs1 xa0 xa1 ya2 xa3 xa4 xa5 (Z_to_bv 64 (d')) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (10)) (Z_to_bv 64 (d')) yt5 yt6 F fc m1)) ->
    evt usegs Q (S2R E 0x44c68 xra xt0 xt1 (Z_to_bv 64 (CP + p + 1)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (10)) (Z_to_bv 64 (d)) xt5 xt6 F fc m1).
  Proof using OK TOK CP0 CPHI.
    induction fuel as [|fuel IH]; intros p d xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 F fc m1 CPRO HP HD HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL. s2_env OK.
    pose proof (B_range (crs t) (p + 1 + d) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 + d < rl)%Z) by (apply Bc_lt; lia).
      eapply (IH p (d + 1)%Z); [exact CPRO | lia | lia | lia | lia |].
      intros d' ya2 yt5 yt1 yt6 HD' HQ'. eapply K; lia.
    - replace (p + 1 + d)%Z with (p + (d + 1))%Z by lia.
      eapply K; lia.
  Qed.

  Lemma numr_L4 : forall (fuel : nat) q0 c xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 CP (zbytes (crs t)) -> (0 <= q0)%Z -> (0 <= c)%Z -> (q0 + c < rl)%Z -> (rl - (q0 + c) < Z.of_nat fuel)%Z ->
    digits (crs t) q0 (c + 1) ->
    (forall c' yt6 yt3, (c < c')%Z -> (q0 + c' <= rl)%Z -> digits (crs t) q0 c' -> ~ (48 <= B (crs t) (q0 + c') <= 57)%Z ->
       evt usegs Q (S2R E 0x44d4c xra (Z_to_bv 64 (B (crs t) (q0 + c'))) xt1 (Z_to_bv 64 (c')) xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (dval (crs t) q0 c')) xa5 xa6 (Z_to_bv 64 (CP + q0)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 (Z_to_bv 64 (2)) (Z_to_bv 64 (10)) yt6 F fc m1)) ->
    evt usegs Q (S2R E 0x44d1c xra xt0 xt1 (Z_to_bv 64 (c)) xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (dval (crs t) q0 c)) xa5 xa6 (Z_to_bv 64 (CP + q0)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (B (crs t) (q0 + c) + -48)) (Z_to_bv 64 (2)) (Z_to_bv 64 (10)) xt6 F fc m1).
  Proof using OK TOK CP0 CPHI.
    induction fuel as [|fuel IH]; intros q0 c xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 F fc m1 CPRO HQ0 HC HQ HF HD K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL. s2_env OK.
    pose proof (B_range (crs t) (q0 + c + 1) BOK) as HB1. pose proof (HD c ltac:(lia)) as HDC.
    ngrun.
    rewrite (dval_step_wz (crs t) q0 c HC HDC).
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q0 + c + 1 < rl)%Z) by (apply Bc_lt; lia).
      replace (q0 + c + 1)%Z with (q0 + (c + 1))%Z by lia.
      eapply (IH q0 (c + 1)%Z); [exact CPRO | lia | lia | lia | lia | | ].
      + apply digits_S; [lia | exact HD |]. replace (q0 + (c + 1))%Z with (q0 + c + 1)%Z by lia. lia.
      + intros c' yt6 yt3 HC' HQ' HD' HND. eapply K; [lia | lia | exact HD' | exact HND].
    - replace (q0 + c + 1)%Z with (q0 + (c + 1))%Z by lia.
      eapply K; [lia | lia | exact HD | replace (q0 + (c + 1))%Z with (q0 + c + 1)%Z by lia; lia].
  Qed.

  Lemma numr_L5 : forall (fuel : nat) q xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 CP (zbytes (crs t)) -> (0 <= q < rl)%Z -> (rl - q < Z.of_nat fuel)%Z ->
    (forall q' yt6, (q < q' <= rl)%Z -> (forall i, (q < i < q')%Z -> B (crs t) i = 48%Z) ->
       evt usegs Q (S2R E 0x472ec xra xt0 xt1 (Z_to_bv 64 (48)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (CP + q')) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 ((-1))) (Z_to_bv 64 (CP + q')) yt6 F fc m1)) ->
    evt usegs Q (S2R E 0x472d4 xra xt0 xt1 (Z_to_bv 64 (48)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (CP + q)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 ((-1))) xt5 xt6 F fc m1).
  Proof using OK TOK CP0 CPHI.
    induction fuel as [|fuel IH]; intros q xra xt0 xt1 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 F fc m1 CPRO HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL. s2_env OK.
    pose proof (B_range (crs t) (q + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q + 1 < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact CPRO | lia | lia |].
      intros q' yt6 HQ' HZ. eapply K; [lia|]. intros i Hi. destruct (Z.eq_dec i (q + 1)) as [->|NE]; [lia| apply HZ; lia].
    - replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
      eapply K; [lia|]. intros i Hi. lia.
  Qed.

  Lemma numr_L6 : forall (fuel : nat) q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 CP (zbytes (crs t)) -> (0 <= q < rl)%Z -> (rl - q < Z.of_nat fuel)%Z ->
    (forall ya3 yt1 yt0, evt usegs Q (S2R E 0x44ec0 xra yt0 yt1 xt2 xs0 xs1 xa0 xa1 xa2 ya3 (Z_to_bv 64 (48)) (Z_to_bv 64 ((-1))) xa6 (Z_to_bv 64 (46)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt usegs Q (S2R E 0x44ea4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 (CP + q)) (Z_to_bv 64 (48)) (Z_to_bv 64 ((-1))) xa6 (Z_to_bv 64 (46)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK TOK CP0 CPHI.
    induction fuel as [|fuel IH]; intros q xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 CPRO HQ HF K; [lia|].
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL. s2_env OK.
    pose proof (B_range (crs t) (q + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q + 1 < rl)%Z) by (apply Bc_lt; lia).
      replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact CPRO | lia | lia |].
      intros ya3 yt1 yt0. eapply K.
    - ngrun.
      if_cases KC2; zify_cond KC2.
      + assert (HNZ : (q + 1 < rl)%Z) by (apply Bc_lt; lia).
        replace (CP + q + 1)%Z with (CP + (q + 1))%Z by lia.
        eapply (IH (q + 1)%Z); [exact CPRO | lia | lia |].
        intros ya3 yt1 yt0. eapply K.
      + eapply K.
  Qed.
End NumRLoops.
