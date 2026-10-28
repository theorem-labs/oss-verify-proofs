(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow_cp | s2_load_shadow | s2_load_cp | solve_load_image ].

Section NumRLoops.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Variable Q : machine_state -> Prop.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Lemma numr_L1 : forall (fuel : nat) p (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xt2 xa0 xa3 xa4 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP nxt [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272] sc fc m1 ->
    (0 <= p < LEN)%Z ->
    (LEN - p < Z.of_nat fuel)%Z ->
    (forall p' ya6 ya7 ya4 ya2, (p < p' <= LEN)%Z ->
       evt asegs Q (S2R E 0xbd578 xra xt0 (Z_to_bv 64 (B bs p')) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (CP + p')) ya2 xa3 ya4 (Z_to_bv 64 (10)) ya6 ya7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt asegs Q (S2R E 0xbd348 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + p + 1)) xa3 xa4 (Z_to_bv 64 (10)) xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ HCP SHZC.
    induction fuel as [|fuel IH]; intros p nxt sc xra xt0 xt1 xt2 xa0 xa3 xa4 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 F fc m1 HM HP0 HP1 K; [lia|].
    pose proof HM as HM0.
    pose proof (rtxt_ok E OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (p + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (p + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      kapply (IH (p + 1)%Z nxt sc); [exact HM0 | lia | lia |].
      intros p' ya6 ya7 ya4 ya2 HP'. eapply K. lia.
    - ngrun_to 0xbd578%Z. kapply (K (p + 1)%Z). lia.
  Qed.

  Lemma numr_L3 : forall (fuel : nat) q (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP nxt [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272] sc fc m1 ->
    (0 <= q < LEN)%Z ->
    (LEN - q < Z.of_nat fuel)%Z ->
    (forall q' ya2 ya7 ya4 ya1 ya6, (q < q' <= LEN)%Z ->
       evt asegs Q (S2R E 0xbee5c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 ya1 ya2 (Z_to_bv 64 (CP + q')) ya4 (Z_to_bv 64 (10)) ya6 ya7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt asegs Q (S2R E 0xbee00 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (CP + q + 1)) xa2 xa3 xa4 (Z_to_bv 64 (10)) (Z_to_bv 64 (CP + q)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ HCP SHZC.
    induction fuel as [|fuel IH]; intros q nxt sc xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 F fc m1 HM HP0 HP1 K; [lia|].
    pose proof HM as HM0.
    pose proof (rtxt_ok E OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (q + 1) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      kapply (IH (q + 1)%Z nxt sc); [exact HM0 | lia | lia |].
      intros q' ya2 ya7 ya4 ya1 ya6 HP'. eapply K. lia.
    - ngrun_to 0xbee5c%Z. kapply (K (q + 1)%Z). lia.
  Qed.

  Lemma numr_L4 : forall (fuel : nat) q0 c (nxt : word) (sc : list (bool * Z)) xra xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP nxt [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272] sc fc m1 ->
    (0 <= q0)%Z ->
    (1 <= c)%Z ->
    (q0 + c <= LEN)%Z ->
    (LEN - (q0 + c) < Z.of_nat fuel)%Z ->
    (forall c' ya1 yt3 ya5 ya6, (c <= c')%Z -> (q0 + c' <= LEN)%Z ->
       evt asegs Q (S2R E 0xbf008 xra (Z_to_bv 64 (c' + 1)) (Z_to_bv 64 (10)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 ya1 (Z_to_bv 64 (CP + q0)) xa3 xa4 ya5 ya6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 xt4 xt5 xt6 F fc m1)) ->
    evt asegs Q (S2R E 0xbef04 xra (Z_to_bv 64 (c)) (Z_to_bv 64 (10)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 (Z_to_bv 64 (CP + q0)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ HCP SHZC.
    induction fuel as [|fuel IH]; intros q0 c nxt sc xra xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 F fc m1 HM HP0 HP1 HP2 HP3 K; [lia|].
    pose proof HM as HM0.
    pose proof (rtxt_ok E OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (q0 + c) BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (q0 + c < LEN)%Z) by (nz_lt_by ltac:(lia)).
      kapply (IH q0 (c + 1)%Z nxt sc); [exact HM0 | lia | lia | lia | lia |].
      intros c' ya1 yt3 ya5 ya6 HC1 HC2. eapply K; lia.
    - ngrun_to 0xbf008%Z. kapply (K c); lia.
  Qed.

  Lemma numr_L5 : forall (fuel : nat) z (nxt : word) (sc : list (bool * Z)) xra xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP nxt [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272] sc fc m1 ->
    (0 <= z <= LEN)%Z ->
    (LEN - z < Z.of_nat fuel)%Z ->
    (forall yt1 ya2 ya6,
       evt asegs Q (S2R E 0xc3c7c xra (Z_to_bv 64 (48)) yt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 ya2 xa3 xa4 xa5 ya6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt asegs Q (S2R E 0xc3c48 xra (Z_to_bv 64 (48)) xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 (Z_to_bv 64 (CP + z)) xa3 xa4 xa5 (Z_to_bv 64 (CP + z + 17)) xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ HCP SHZC.
    induction fuel as [|fuel IH]; intros z nxt sc xra xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 F fc m1 HM HP0 HP1 K; [lia|].
    pose proof HM as HM0.
    pose proof (rtxt_ok E OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs z BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (z < LEN)%Z) by (nz_lt_by ltac:(lia)).
      kapply (IH (z + 1)%Z nxt sc); [exact HM0 | lia | lia |].
      intros yt1 ya2 ya6. eapply K.
    - ngrun_to 0xc3c7c%Z. kapply K.
  Qed.

  Lemma numr_L6 : forall (fuel : nat) z (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP nxt [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272] sc fc m1 ->
    (0 <= z <= LEN)%Z ->
    (LEN - z < Z.of_nat fuel)%Z ->
    (forall ya5 ya0 ya1 yt2,
       evt asegs Q (S2R E 0xbfbac xra xt0 xt1 yt2 (e_sp E) (Z_to_bv 64 (e_spa E)) ya0 ya1 (Z_to_bv 64 (48)) (Z_to_bv 64 (46)) xa4 ya5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1)) ->
    evt asegs Q (S2R E 0xbf090 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + z)) (Z_to_bv 64 (CP + z)) (Z_to_bv 64 (48)) (Z_to_bv 64 (46)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ HCP SHZC.
    induction fuel as [|fuel IH]; intros z nxt sc xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j168 j176 j208 j272 F fc m1 HM HP0 HP1 K; [lia|].
    pose proof HM as HM0.
    pose proof (rtxt_ok E OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs z BOK) as HB1.
    ngrun.
    if_cases KC; zify_cond KC.
    - assert (HNZ : (z < LEN)%Z) by (nz_lt_by ltac:(lia)).
      ngrun_to 0xbf090%Z.
      kapply (IH (z + 1)%Z nxt sc); [exact HM0 | lia | lia |].
      intros ya5 ya0 ya1 yt2. eapply K.
    - ngrun.
      if_cases KD; zify_cond KD.
      + assert (HNZ : (z < LEN)%Z) by (nz_lt_by ltac:(lia)).
        ngrun_to 0xbf090%Z.
        kapply (IH (z + 1)%Z nxt sc); [exact HM0 | lia | lia |].
        intros ya5 ya0 ya1 yt2. eapply K.
      + ngrun_to 0xbfbac%Z. kapply K.
  Qed.

  Lemma numr_L2 : forall (fuel : nat) p j (nxt : word) (sc : list (bool * Z)) xra xt0 xt1 xt2 xa0 xa2 xa3 xa7 xs6 xs7 xs8 xs9 xs10 xs11 xt5
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP nxt [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (434041037028460038)); CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272] sc fc m1 ->
    (0 <= p)%Z ->
    (0 <= j)%Z ->
    (p + 8 + 8 * j < LEN)%Z ->
    (LEN - (p + 8 * j) < Z.of_nat fuel)%Z ->
    (forall j' ya3 yt5 yt2 yt0 ya2 ys10 ya7 yt6 ys2, (j < j')%Z -> (p + 8 * j' < LEN)%Z ->
       evt asegs Q (S2R E 0xbecdc xra yt0 xt1 yt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (CP + p)) ya2 ya3 (Z_to_bv 64 (1085102592571150095)) (Z_to_bv 64 (CP + p + 16)) (Z_to_bv 64 (8 * j')) ya7 ys2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (CP + p + 9)) xs6 xs7 xs8 xs9 ys10 xs11 (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) yt5 yt6 F fc m1)) ->
    evt asegs Q (S2R E 0xbd764 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (CP + p)) xa2 xa3 (Z_to_bv 64 (1085102592571150095)) (Z_to_bv 64 (CP + p + 16)) (Z_to_bv 64 (8 * j)) xa7 (Z_to_bv 64 (SHA (CP + p + 9) + j)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (CP + p + 9)) xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (17361641481138401520)) (Z_to_bv 64 (3689348814741910323)) xt5 (Z_to_bv 64 (V8 (B bs (p + 1 + 8 * j)) (B bs (p + 1 + 8 * j + 1)) (B bs (p + 1 + 8 * j + 2)) (B bs (p + 1 + 8 * j + 3)) (B bs (p + 1 + 8 * j + 4)) (B bs (p + 1 + 8 * j + 5)) (B bs (p + 1 + 8 * j + 6)) (B bs (p + 1 + 8 * j + 7)))) F fc m1).
  Proof using OK SHZ HCP SHZC.
    induction fuel as [|fuel IH]; intros p j nxt sc xra xt0 xt1 xt2 xa0 xa2 xa3 xa7 xs6 xs7 xs8 xs9 xs10 xs11 xt5 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 F fc m1 HM HP0 HP1 HP2 HP3 K; [lia|].
    pose proof HM as HM0.
    pose proof (rtxt_ok E OK) as BOK. s2_env OK.
    nopen HM.
    pose proof (B_range bs (p + 9 + 8 * j) BOK) as HB0. pose proof (B_range bs (p + 9 + 8 * j + 1) BOK) as HB1. pose proof (B_range bs (p + 9 + 8 * j + 2) BOK) as HB2.
    pose proof (B_range bs (p + 9 + 8 * j + 3) BOK) as HB3. pose proof (B_range bs (p + 9 + 8 * j + 4) BOK) as HB4. pose proof (B_range bs (p + 9 + 8 * j + 5) BOK) as HB5.
    pose proof (B_range bs (p + 9 + 8 * j + 6) BOK) as HB6. pose proof (B_range bs (p + 9 + 8 * j + 7) BOK) as HB7.
    replace (Z_to_bv 64 (SHA (CP + p + 9) + j)) with (Z_to_bv 64 (SHA (CP + p + 9 + 8 * j))) by (f_equal; rewrite (shr3_add8 (CP + p + 9) j); lia).
    ngrun_to 0xbd810%Z. fold_V8.
    ngrun.
    if_cases KC; zify_cond KC.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR. rewrite ?(Z.mod_small _ _ HVR) in KC.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL.
      assert (HNZ : (p + 9 + 8 * j + 7 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      rewrite (shr3_add8 (CP + p + 9) j).
      kapply (IH p (j + 1)%Z nxt sc); [exact HM0 | lia | lia | lia | lia |].
      intros j' ya3 yt5 yt2 yt0 ya2 ys10 ya7 yt6 ys2 HJ1 HJ2. eapply K; lia.
    - ngrun_to 0xbecdc%Z. kapply (K (j + 1)%Z); lia.
  Qed.
End NumRLoops.
