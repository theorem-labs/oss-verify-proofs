(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit Sj_stage2_numkit2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].

Section NumALoops.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variable Q : machine_state -> Prop.
  Notation bs := (e_bs E).

  Lemma numa_L1 : forall (fuel : nat) p xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= p < e_len E)%Z -> (e_len E - p < Z.of_nat fuel)%Z ->
    (forall p' ya3 yt4 ya0 yt5, (p < p' <= e_len E)%Z ->
       evt usegs Q (S2R E 0x47fc4 xra (Z_to_bv 64 (B bs p')) (Z_to_bv 64 (2)) (Z_to_bv 64 (10)) xs0 xs1 ya0 xa1 xa2 ya3 xa4 (Z_to_bv 64 (e_BUF E + p')) xa6 (Z_to_bv 64 (e_BUF E + p')) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (e_BUF E + p')) yt4 yt5 xt6 F fc m1)) ->
    evt usegs Q (S2R E 0x47f94 xra xt0 (Z_to_bv 64 (2)) (Z_to_bv 64 (10)) xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (e_BUF E + p)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (e_BUF E + p)) xt4 xt5 xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros p xra xt0 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 F fc m1 BUFRO HP HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (padded_bytes_blen bs) as PBL. s2_env OK.
    pose proof (B_range bs (p + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
      eapply (IH (p + 1)%Z); [exact BUFRO | lia | lia |].
      intros p' ya3 yt4 ya0 yt5 HP'. eapply K. lia.
    - replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numa_L2 : forall (fuel : nat) p q xra xt0 xt1 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q <= e_len E)%Z -> (e_len E - q < Z.of_nat fuel)%Z ->
    (forall q' ys7 ys8 ys9 ys10 ys11 yra ya3 yt5, (q <= q' <= e_len E)%Z ->
       evt usegs Q (S2R E 0x4819c yra xt0 (Z_to_bv 64 (V8 (B bs q') (B bs (q' + 1)) (B bs (q' + 2)) (B bs (q' + 3)) (B bs (q' + 4)) (B bs (q' + 5)) (B bs (q' + 6)) (B bs (q' + 7)))) (Z_to_bv 64 (434041037028460038)) xs0 xs1 (Z_to_bv 64 (1085102592571150095)) xa1 xa2 ya3 xa4 xa5 xa6 (Z_to_bv 64 (q' - p)) xs2 xs3 xs4 xs5 xs6 ys7 ys8 ys9 ys10 ys11 (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) yt5 xt6 F fc m1)) ->
    evt usegs Q (S2R E 0x480f8 xra xt0 xt1 (Z_to_bv 64 (434041037028460038)) xs0 xs1 (Z_to_bv 64 (1085102592571150095)) xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (q - p - 8)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) (Z_to_bv 64 (e_BUF E + q)) xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros p q xra xt0 xt1 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 F fc m1 BUFRO HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (padded_bytes_blen bs) as PBL. s2_env OK.
    pose proof (B_range bs q BOK) as HB0. pose proof (B_range bs (q + 1) BOK) as HB1. pose proof (B_range bs (q + 2) BOK) as HB2.
    pose proof (B_range bs (q + 3) BOK) as HB3. pose proof (B_range bs (q + 4) BOK) as HB4. pose proof (B_range bs (q + 5) BOK) as HB5.
    pose proof (B_range bs (q + 6) BOK) as HB6. pose proof (B_range bs (q + 7) BOK) as HB7.
    ngrun_to 0x4817c%Z.
    replace (e_BUF E + q)%Z with (e_BUF E + (q + 0))%Z by lia. nnorm. fold_V8. replace (q + 0)%Z with q by lia.
    ngrun.
    if_cases KC; zify_cond KC.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR. rewrite ?(Z.mod_small _ _ HVR) in KC.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL.
      assert (HNZ : (q + 7 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + q + 8)%Z with (e_BUF E + (q + 8))%Z by lia.
      replace (q - p - 8 + 8)%Z with (q + 8 - p - 8)%Z by lia.
      eapply (IH p (q + 8)%Z); [exact BUFRO | lia | lia |].
      intros q' ys7 ys8 ys9 ys10 ys11 yra ya3 yt5 HQ'. eapply K. lia.
    - replace (q - p - 8 + 8)%Z with (q - p)%Z by lia.
      eapply K. lia.
  Qed.

  Lemma numa_L3 : forall (fuel : nat) p d xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= p)%Z -> (0 <= d)%Z -> (p + d < e_len E)%Z -> (e_len E - (p + d) < Z.of_nat fuel)%Z ->
    (forall d' ya3 yt5 yt2 yt6, (d < d')%Z -> (p + d' <= e_len E)%Z ->
       evt usegs Q (S2R E 0x48254 xra xt0 (Z_to_bv 64 (B bs (p + d'))) yt2 xs0 xs1 (Z_to_bv 64 (e_BUF E + p + 1)) xa1 xa2 ya3 xa4 xa5 xa6 (Z_to_bv 64 (d')) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (10)) (Z_to_bv 64 (d')) yt5 yt6 F fc m1)) ->
    evt usegs Q (S2R E 0x4822c xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (e_BUF E + p + 1)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (10)) (Z_to_bv 64 (d)) xt5 xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros p d xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 F fc m1 BUFRO HP HD HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (padded_bytes_blen bs) as PBL. s2_env OK.
    pose proof (B_range bs (p + 1 + d) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 + d < e_len E)%Z) by (apply B_nz_lt; lia).
      eapply (IH p (d + 1)%Z); [exact BUFRO | lia | lia | lia | lia |].
      intros d' ya3 yt5 yt2 yt6 HD' HQ'. eapply K; lia.
    - replace (p + 1 + d)%Z with (p + (d + 1))%Z by lia.
      eapply K; lia.
  Qed.

  Lemma numa_L4 : forall (fuel : nat) q0 c xra xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q0)%Z -> (0 <= c)%Z -> (q0 + c < e_len E)%Z -> (e_len E - (q0 + c) < Z.of_nat fuel)%Z ->
    digits bs q0 (c + 1) ->
    (forall c' ys0 yt5, (c < c')%Z -> (q0 + c' <= e_len E)%Z -> digits bs q0 c' -> ~ (48 <= B bs (q0 + c') <= 57)%Z ->
       evt usegs Q (S2R E 0x48584 xra (Z_to_bv 64 (e_BUF E + q0)) (Z_to_bv 64 (B bs (q0 + c'))) xt2 ys0 xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (dval bs q0 c')) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (c')) (Z_to_bv 64 (2)) yt5 (Z_to_bv 64 (10)) F fc m1)) ->
    evt usegs Q (S2R E 0x48554 xra (Z_to_bv 64 (e_BUF E + q0)) xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 (dval bs q0 c)) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (c)) (Z_to_bv 64 (2)) (Z_to_bv 64 (B bs (q0 + c) + -48)) (Z_to_bv 64 (10)) F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros q0 c xra xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 F fc m1 BUFRO HQ0 HC HQ HF HD K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (padded_bytes_blen bs) as PBL. s2_env OK.
    pose proof (B_range bs (q0 + c + 1) BOK) as HB1. pose proof (HD c ltac:(lia)) as HDC.
    ngrun.
    rewrite (dval_step_wz bs q0 c HC HDC).
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q0 + c + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (q0 + c + 1)%Z with (q0 + (c + 1))%Z by lia.
      eapply (IH q0 (c + 1)%Z); [exact BUFRO | lia | lia | lia | lia | | ].
      + apply digits_S; [lia | exact HD |]. replace (q0 + (c + 1))%Z with (q0 + c + 1)%Z by lia. lia.
      + intros c' ys0 yt5 HC' HQ' HD' HND. eapply K; [lia | lia | exact HD' | exact HND].
    - replace (q0 + c + 1)%Z with (q0 + (c + 1))%Z by lia.
      eapply K; [lia | lia | exact HD | replace (q0 + (c + 1))%Z with (q0 + c + 1)%Z by lia; lia].
  Qed.

  Lemma numa_L5 : forall (fuel : nat) q xra xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q < e_len E)%Z -> (e_len E - q < Z.of_nat fuel)%Z ->
    (forall q' yt6, (q < q' <= e_len E)%Z -> (forall i, (q < i < q')%Z -> B bs i = 48%Z) ->
       evt usegs Q (S2R E 0x48afc xra (Z_to_bv 64 (e_BUF E + q')) xt1 xt2 xs0 xs1 (Z_to_bv 64 (48)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 ((-1))) xt4 (Z_to_bv 64 (e_BUF E + q')) yt6 F fc m1)) ->
    evt usegs Q (S2R E 0x48ae4 xra (Z_to_bv 64 (e_BUF E + q)) xt1 xt2 xs0 xs1 (Z_to_bv 64 (48)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 ((-1))) xt4 xt5 xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros q xra xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 F fc m1 BUFRO HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (padded_bytes_blen bs) as PBL. s2_env OK.
    pose proof (B_range bs (q + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact BUFRO | lia | lia |].
      intros q' yt6 HQ' HZ. eapply K; [lia|]. intros i Hi. destruct (Z.eq_dec i (q + 1)) as [->|NE]; [lia| apply HZ; lia].
    - replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
      eapply K; [lia|]. intros i Hi. lia.
  Qed.

  Lemma numa_L6 : forall (fuel : nat) q xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    bytes_at usegs m1 (e_BUF E) (padded_bytes bs) -> (0 <= q < e_len E)%Z -> (e_len E - q < Z.of_nat fuel)%Z ->
    (forall ya4 yt2 yt0, evt usegs Q (S2R E 0x48648 xra yt0 xt1 yt2 xs0 xs1 (Z_to_bv 64 (48)) xa1 xa2 xa3 ya4 (Z_to_bv 64 ((-1))) (Z_to_bv 64 (46)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt usegs Q (S2R E 0x4862c xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (48)) xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + q)) (Z_to_bv 64 ((-1))) (Z_to_bv 64 (46)) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    induction fuel as [|fuel IH]; intros q xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 BUFRO HQ HF K; [lia|].
    pose proof (ok_bytes _ OK) as BOK. pose proof (padded_bytes_blen bs) as PBL. s2_env OK.
    pose proof (B_range bs (q + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
      replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
      eapply (IH (q + 1)%Z); [exact BUFRO | lia | lia |].
      intros ya4 yt2 yt0. eapply K.
    - ngrun.
      if_cases KC2; zify_cond KC2.
      + assert (HNZ : (q + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
        replace (e_BUF E + q + 1)%Z with (e_BUF E + (q + 1))%Z by lia.
        eapply (IH (q + 1)%Z); [exact BUFRO | lia | lia |].
        intros ya4 yt2 yt0. eapply K.
      + eapply K.
  Qed.
End NumALoops.
