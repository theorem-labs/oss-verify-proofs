(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | solve_load_image ].

Section NumOLoops.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable Q : machine_state -> Prop.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).

  Lemma numo_L1 : forall (fuel : nat) p (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xt2 xa0 xa3 xa4 xa7 xs2 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E nxt [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] sc fc m1 ->
    (0 <= p < LEN)%Z ->
    (LEN - p < Z.of_nat fuel)%Z ->
    (forall p' yt0 yt1 ya6 ya7 ya4 yt2, (p < p' <= LEN)%Z ->
       evt bsegs Q (S2R E 0xc2e38 xra yt0 yt1 yt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p')) (Z_to_bv 64 (10)) xa3 ya4 (Z_to_bv 64 (2)) ya6 ya7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 (Z_to_bv 64 (2147450880)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt bsegs Q (S2R E 0xc2df8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (10)) xa3 xa4 (Z_to_bv 64 (2)) (Z_to_bv 64 (e_BUF E + p)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 (Z_to_bv 64 (2147450880)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    induction fuel as [|fuel IH]; intros p nxt sc xra xt0 xt1 xt2 xa0 xa3 xa4 xa7 xs2 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 F fc m1 HM HP0 HP1 K; [lia|].
    pose proof HM as HM0.
    pose proof (ok_bytes _ OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (p + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      kapply (IH (p + 1)%Z nxt sc); [exact HM0 | lia | lia |].
      intros p' yt0 yt1 ya6 ya7 ya4 yt2 HP'. eapply K. lia.
    - ngrun_to 0xc2e38%Z. kapply (K (p + 1)%Z). lia.
  Qed.

  Lemma numo_L3 : forall (fuel : nat) p d (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xa0 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E nxt [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; C8 (Z_to_bv 64 (e_BUF E + p + 1)); CB 8 j288; CB 8 j304] sc fc m1 ->
    (0 <= p)%Z ->
    (1 <= d)%Z ->
    (p + d < LEN)%Z ->
    (LEN - (p + d) < Z.of_nat fuel)%Z ->
    (forall d' ya5 ya0 ya2 ya6 ya7 ya3, (d < d')%Z -> (p + d' <= LEN)%Z ->
       evt bsegs Q (S2R E 0xc3408 xra xt0 xt1 (Z_to_bv 64 (d')) (e_sp E) (Z_to_bv 64 (e_spa E)) ya0 (Z_to_bv 64 (e_BUF E + p)) ya2 ya3 (Z_to_bv 64 (10)) ya5 ya6 ya7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt bsegs Q (S2R E 0xc33cc xra xt0 xt1 (Z_to_bv 64 (d)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 (Z_to_bv 64 (10)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    induction fuel as [|fuel IH]; intros p d nxt sc xra xt0 xt1 xa0 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j288 j304 F fc m1 HM HP0 HP1 HP2 HP3 K; [lia|].
    pose proof HM as HM0.
    pose proof (ok_bytes _ OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (p + 1 + d) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 + d < LEN)%Z) by (nz_lt_by ltac:(lia)).
      kapply (IH p (d + 1)%Z nxt sc); [exact HM0 | lia | lia | lia | lia |].
      intros d' ya5 ya0 ya2 ya6 ya7 ya3 HD1 HD2. eapply K; lia.
    - ngrun_to 0xc3408%Z. kapply (K (d + 1)%Z); lia.
  Qed.

  Lemma numo_L4 : forall (fuel : nat) q0 c (nxt : word) (sc : list (bool * Z)) xra xt0 xt2 xa1 xa3 xa4 xa7 xs2 xs4 xs5 xs6 xs8 xs9 xs11 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E nxt [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] sc fc m1 ->
    (0 <= q0)%Z ->
    (0 <= c)%Z ->
    (q0 + c < LEN)%Z ->
    (LEN - (q0 + c) < Z.of_nat fuel)%Z ->
    digits bs q0 (c + 1) ->
    (forall c' yt5 ya1 yt6 ya6 yt4, (c < c')%Z -> (q0 + c' <= LEN)%Z -> digits bs q0 c' -> ~ (48 <= B bs (q0 + c') <= 57)%Z ->
       evt bsegs Q (S2R E 0xc3788 xra xt0 (Z_to_bv 64 (dval bs q0 c')) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (2)) ya1 (Z_to_bv 64 (e_BUF E + q0)) xa3 xa4 (Z_to_bv 64 (c')) ya6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 (Z_to_bv 64 (2147450880)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (10)) yt4 yt5 yt6 F fc m1)) ->
    evt bsegs Q (S2R E 0xc3744 xra xt0 (Z_to_bv 64 (dval bs q0 c)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (2)) xa1 (Z_to_bv 64 (e_BUF E + q0)) xa3 xa4 (Z_to_bv 64 (c)) (Z_to_bv 64 (B bs (q0 + c) + -48)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 (Z_to_bv 64 (2147450880)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (10)) (Z_to_bv 64 (e_BUF E + q0 + c)) xt5 xt6 F fc m1).
  Proof using OK SHZ.
    induction fuel as [|fuel IH]; intros q0 c nxt sc xra xt0 xt2 xa1 xa3 xa4 xa7 xs2 xs4 xs5 xs6 xs8 xs9 xs11 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 F fc m1 HM HP0 HP1 HP2 HP3 HP4 K; [lia|].
    pose proof HM as HM0.
    pose proof (ok_bytes _ OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (q0 + c + 1) BOK) as HB1. pose proof (HP4 c ltac:(lia)) as HDC.
    ngrun.
    rewrite ?(dval_step_wz bs q0 c HP1 HDC).
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q0 + c + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      assert (HD1 : digits bs q0 (c + 1 + 1)) by (apply digits_S; [lia | exact HP4 | replace (q0 + (c + 1))%Z with (q0 + c + 1)%Z by lia; lia]).
      kapply (IH q0 (c + 1)%Z nxt sc); [exact HM0 | lia | lia | lia | lia | exact HD1 |].
      intros c' yt5 ya1 yt6 ya6 yt4 HC1 HC2 HC3 HC4. eapply K; [lia | lia | exact HC3 | exact HC4].
    - ngrun_to 0xc3788%Z. kapply (K (c + 1)%Z); [lia | lia | exact HP4 | replace (q0 + (c + 1))%Z with (q0 + c + 1)%Z by lia; lia].
  Qed.

  Lemma numo_L5 : forall (fuel : nat) z (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xt2 xa0 xa1 xa4 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E nxt [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] sc fc m1 ->
    (0 <= z < LEN)%Z ->
    (LEN - z < Z.of_nat fuel)%Z ->
    (forall z' yt3 ya0 ya3, (z < z' <= LEN)%Z -> (forall i, (z < i < z')%Z -> B bs i = 48%Z) ->
       evt bsegs Q (S2R E 0xc3b04 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) ya0 xa1 (Z_to_bv 64 (e_BUF E + z')) ya3 xa4 (Z_to_bv 64 (48)) (Z_to_bv 64 ((-1))) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 yt3 xt4 xt5 xt6 F fc m1)) ->
    evt bsegs Q (S2R E 0xc3ad8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 (Z_to_bv 64 (e_BUF E + z)) (Z_to_bv 64 (e_BUF E + z + 1)) xa4 (Z_to_bv 64 (48)) (Z_to_bv 64 ((-1))) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    induction fuel as [|fuel IH]; intros z nxt sc xra xt0 xt1 xt2 xa0 xa1 xa4 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 F fc m1 HM HP0 HP1 K; [lia|].
    pose proof HM as HM0.
    pose proof (ok_bytes _ OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (z + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (z + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      kapply (IH (z + 1)%Z nxt sc); [exact HM0 | lia | lia |].
      intros z' yt3 ya0 ya3 HZ1 HZ2. eapply K; [lia|]. intros i Hi. destruct (Z.eq_dec i (z + 1)) as [->|NE]; [lia | apply HZ2; lia].
    - ngrun_to 0xc3b04%Z. kapply (K (z + 1)%Z); [lia|]. intros i Hi. lia.
  Qed.

  Lemma numo_L6 : forall (fuel : nat) z (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xt2 xa1 xa4 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E nxt [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] sc fc m1 ->
    (0 <= z <= LEN)%Z ->
    (LEN - z < Z.of_nat fuel)%Z ->
    (forall ya6 ys4 ya0 yt2 ya1,
       evt bsegs Q (S2R E 0xc3c08 xra xt0 xt1 yt2 (e_sp E) (Z_to_bv 64 (e_spa E)) ya0 ya1 (Z_to_bv 64 (48)) (Z_to_bv 64 ((-1))) xa4 (Z_to_bv 64 (46)) ya6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) ys4 xs5 xs6 (Z_to_bv 64 (2147450880)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt bsegs Q (S2R E 0xc3bfc xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + z)) xa1 (Z_to_bv 64 (48)) (Z_to_bv 64 ((-1))) xa4 (Z_to_bv 64 (46)) xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + z)) xs5 xs6 (Z_to_bv 64 (2147450880)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    induction fuel as [|fuel IH]; intros z nxt sc xra xt0 xt1 xt2 xa1 xa4 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j272 j288 j304 F fc m1 HM HP0 HP1 K; [lia|].
    pose proof HM as HM0.
    pose proof (ok_bytes _ OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs z BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (z < LEN)%Z) by (nz_lt_by ltac:(lia)).
      ngrun_to 0xc3bfc%Z.
      kapply (IH (z + 1)%Z nxt sc); [exact HM0 | lia | lia |].
      intros ya6 ys4 ya0 yt2 ya1. eapply K.
    - ngrun.
      if_cases KD; zify_cond KD.
      + assert (HNZ : (z < LEN)%Z) by (nz_lt_by ltac:(lia)).
        ngrun_to 0xc3bfc%Z.
        kapply (IH (z + 1)%Z nxt sc); [exact HM0 | lia | lia |].
        intros ya6 ys4 ya0 yt2 ya1. eapply K.
      + ngrun_to 0xc3c08%Z. kapply K.
  Qed.

  Lemma numo_L2 : forall (fuel : nat) p j (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xa2 xa4 xa6 xa7 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6
      j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j168 j176 j184 j192 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E nxt [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; C8 (Z_to_bv 64 (3689348814741910323)); C8 (Z_to_bv 64 (17361641481138401520)); C8 (Z_to_bv 64 (434041037028460038)); CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] sc fc m1 ->
    (0 <= p)%Z ->
    (0 <= j)%Z ->
    (p + 8 + 8 * j < LEN)%Z ->
    (LEN - (p + 8 * j) < Z.of_nat fuel)%Z ->
    (forall j' yt1 ya4 ya2 yt4 yt5 yt6 ya7 ya0 ya5 ya3 ys2 ys7, (j < j')%Z -> (p + 8 * j' < LEN)%Z ->
       evt bsegs Q (S2R E 0xc320c xra xt0 yt1 (Z_to_bv 64 (1 + 8 * j')) (e_sp E) (Z_to_bv 64 (e_spa E)) ya0 (Z_to_bv 64 (e_BUF E + p)) ya2 ya3 ya4 ya5 xa6 ya7 ys2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 ys7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (1085102592571150095)) yt4 yt5 yt6 F fc m1)) ->
    evt bsegs Q (S2R E 0xc3134 xra xt0 xt1 (Z_to_bv 64 (1 + 8 * j)) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + p + 9 + 8 * j)) (Z_to_bv 64 (e_BUF E + p)) xa2 (Z_to_bv 64 (e_BUF E + p + 16 + 8 * j)) xa4 (Z_to_bv 64 (SHA (e_BUF E + p + 9) + j)) xa6 xa7 (Z_to_bv 64 (V8 (B bs (p + 1 + 8 * j)) (B bs (p + 1 + 8 * j + 1)) (B bs (p + 1 + 8 * j + 2)) (B bs (p + 1 + 8 * j + 3)) (B bs (p + 1 + 8 * j + 4)) (B bs (p + 1 + 8 * j + 5)) (B bs (p + 1 + 8 * j + 6)) (B bs (p + 1 + 8 * j + 7)))) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 (Z_to_bv 64 (e_BUF E + p + 9 + 8 * j)) xs8 xs9 xs10 xs11 (Z_to_bv 64 (1085102592571150095)) xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    induction fuel as [|fuel IH]; intros p j nxt sc xra xt0 xt1 xa2 xa4 xa6 xa7 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j168 j176 j184 j192 j200 j272 j288 j304 F fc m1 HM HP0 HP1 HP2 HP3 K; [lia|].
    pose proof HM as HM0.
    pose proof (ok_bytes _ OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (p + 9 + 8 * j) BOK) as HB0. pose proof (B_range bs (p + 9 + 8 * j + 1) BOK) as HB1. pose proof (B_range bs (p + 9 + 8 * j + 2) BOK) as HB2.
    pose proof (B_range bs (p + 9 + 8 * j + 3) BOK) as HB3. pose proof (B_range bs (p + 9 + 8 * j + 4) BOK) as HB4. pose proof (B_range bs (p + 9 + 8 * j + 5) BOK) as HB5.
    pose proof (B_range bs (p + 9 + 8 * j + 6) BOK) as HB6. pose proof (B_range bs (p + 9 + 8 * j + 7) BOK) as HB7.
    replace (Z_to_bv 64 (SHA (e_BUF E + p + 9) + j)) with (Z_to_bv 64 (SHA (e_BUF E + p + 9 + 8 * j))) by (f_equal; rewrite (shr3_add8 (e_BUF E + p + 9) j); lia).
    ngrun_to 0xc31dc%Z. fold_V8.
    ngrun.
    if_cases KC; zify_cond KC.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR. rewrite ?(Z.mod_small _ _ HVR) in KC.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL.
      assert (HNZ : (p + 9 + 8 * j + 7 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      rewrite (shr3_add8 (e_BUF E + p + 9) j).
      kapply (IH p (j + 1)%Z nxt sc); [exact HM0 | lia | lia | lia | lia |].
      intros j' yt1 ya4 ya2 yt4 yt5 yt6 ya7 ya0 ya5 ya3 ys2 ys7 HJ1 HJ2. eapply K; lia.
    - ngrun_to 0xc320c%Z. kapply (K (j + 1)%Z); lia.
  Qed.
End NumOLoops.
