(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype F_syscalls F_errno_location F_strtol F_atoi F_htons F_memset F_memmove F_stpncpy F_strncasecmp
     F_inet_pton_A F_inet_pton_C H_parse_uric H_parse_uri_A H_parse_uri_B HU_puri_af HU_list_kit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (U O ulen : Z) (ustr slack : list byte) (canary gifv : word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis USL : Z.of_nat (length ustr) = ulen.
  Hypothesis ULR : (0 <= ulen < 2^31)%Z.
  Hypothesis PAD : ((- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis U4K : (4096 <= U)%Z.
  Hypothesis ULO : (U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 928)%Z.
  Hypothesis OSP : (bv_unsigned sp <= O)%Z.
  Hypothesis OHI : (O + 216 <= 2^62)%Z.
  Hypothesis OAL : oal O.
  Hypothesis SPH : (bv_unsigned sp + 2^41 <= 2^63)%Z.
  Hypothesis TP1 : (4096 + 164 <= bv_unsigned tp)%Z.
  Hypothesis TP2 : (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis SGLO : (ssp_guard + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GSLO : (got_ssp + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GFLO : (GIF + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis DE1 : (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE2 : (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE3 : (bv_unsigned tp - 164 + 4 <= GOT_GIF \/ GOT_GIF + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE4 : (bv_unsigned tp - 164 + 4 <= GIF \/ GIF + 4 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE5 : (bv_unsigned tp - 164 + 4 <= U \/ U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned tp - 164)%Z.

  Notation SP := (bv_unsigned sp).
  Notation q := (bv_unsigned sp + -400)%Z.
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -400)).
  Notation lo := (bv_unsigned sp - 928)%Z.
  Notation TPE := (bv_unsigned tp - 164)%Z.
  Notation W := [(bv_unsigned sp - 928, bv_unsigned sp); (O, O + 216); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z.
  Notation POST := (parse_uri_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc U O ustr slack canary gifv m0).
  Notation USTR m := (bytes_at rsegs m U (ustr ++ Z_to_bv 8 0 :: slack)).

  Notation baseP := (base U O ustr slack canary gifv sp tp m0).

  Notation FRB m := (rw_cells rsegs m (q + 296) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac open_base B :=
    let errv := fresh "errv" in
    destruct B as (USTR & [errv ERR] & GOT & CAN & GIFP & GIFV & MI & MU & WM).
  Ltac close_base :=
      split; [assumption|]; split; [eexists; eassumption|]; repeat (split; [assumption|]); assumption.

  #[using="U ulen slack ULR U4K ULO SPH"] Lemma sp_rangeB : (928 <= SP /\ SP + 2^41 <= 2^63)%Z.
  Proof. clear -ULR U4K ULO SPH. pose proof (word_lt64 sp). lia. Qed.
  #[using="U ulen ustr slack ULR U4K ULO SPH GFLO"] Lemma q_spB : bv_unsigned spw = q.
  Proof. pose proof sp_rangeB. apply unsigned_lit. lia. Qed.


  #[using="U ulen ustr slack ULR"] Lemma dig_land : forall c, (0 <= c < 256 -> Z.land (c + -48) 18446744073709551615 < 10 -> 48 <= c < 58)%Z.
  Proof.
    intros c Hc H. change 18446744073709551615%Z with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
    destruct (Z.lt_ge_cases c 48).
    - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
    - rewrite Z.mod_small in H by lia. lia.
  Qed.
  #[using="U ulen ustr slack ULR"] Lemma nodig_land : forall c, (0 <= c < 256 -> ~ (Z.land (c + -48) 18446744073709551615 < 10) -> ~ (48 <= c < 58))%Z.
  Proof.
    intros c Hc H Hd. apply H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wrap_sub_lt : forall c a n, (0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
    Z.land (c + a) 18446744073709551615 < n -> - a <= c < - a + n)%Z.
  Proof.
    intros c a n Hc Ha Hn H. change 18446744073709551615%Z with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
    destruct (Z.lt_ge_cases c (- a)).
    - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
    - rewrite Z.mod_small in H by lia. lia.
  Qed.
  #[using="U ulen ustr slack ULR"] Lemma wrap_sub_ge : forall c a n, (0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
    ~ (Z.land (c + a) 18446744073709551615 < n) -> ~ (- a <= c < - a + n))%Z.
  Proof.
    intros c a n Hc Ha Hn H Hd. apply H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  #[using="Type"] Lemma is_alnum_nz : forall c, is_alnum c = true -> c <> 0%Z.
  Proof. intros c H ->. discriminate H. Qed.

  #[using="Type"] Lemma firstn_S_snoc : forall (l : list byte) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
  Proof.
    induction l as [|a l IH]; intros n x H; [destruct n; discriminate|].
    destruct n as [|n]; cbn in H |- *. { injection H as ->. reflexivity. } rewrite (IH n x H). reflexivity.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_string : forall m wb (a z : Z),
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat -> (0 <= a <= z)%Z -> (z <= 255)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    bytes_at rsegs m (q + 40 + a) (firstn (Z.to_nat (z - a)) (skipn (Z.to_nat a) wb) ++ [Z_to_bv 8 0])
    /\ length (firstn (Z.to_nat (z - a)) (skipn (Z.to_nat a) wb)) = Z.to_nat (z - a).
  Proof.
    intros m wb a z [B _] L A Z0 NZ. split.
    - rewrite <- (firstn_S_snoc (skipn (Z.to_nat a) wb) (Z.to_nat (z - a)) (Z_to_bv 8 0)).
      2:{ rewrite nth_error_skipn. replace (Z.to_nat a + Z.to_nat (z - a))%nat with (Z.to_nat z) by lia. exact NZ. }
      rewrite <- (firstn_skipn (Z.to_nat a) wb) in B. apply bytes_at_app in B. destruct B as [_ B].
      rewrite firstn_length, Nat.min_l in B by lia. rewrite Z2Nat.id in B by lia.
      rewrite <- (firstn_skipn (S (Z.to_nat (z - a))) (skipn (Z.to_nat a) wb)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
    - rewrite firstn_length, skipn_length, L. lia.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_nth : forall (wb : list byte) i, length wb = 256%nat -> (0 <= i <= 255)%Z -> exists b, nth_error wb (Z.to_nat i) = Some b.
  Proof.
    intros wb i L Hi. destruct (nth_error wb (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma port : forall (bh2 p0 z srv af : Z) (pw : word) (host h : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x26 x27 x28 x29 x30 x31
      m c0 wb csL,
    baseP m -> rw_cells rsegs m q c0 -> cells_size c0 = 8%nat -> rw_cells rsegs m (q + 8) [C4 (Z_to_bv 64 bh2); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (q + 16) [C8 (Z_to_bv 64 (O + 64))] -> rw_cells rsegs m (q + 24) [C8 (Z_to_bv 64 (U + bh2))] -> rw_cells rsegs m (q + 32) [C8 pw] ->
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 40 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 296)%Z ->
    (0 <= p0 < z)%Z -> (z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (af = 0 \/ af = 2 \/ af = 10)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j b, (p0 < j < z)%Z -> nth_error wb (Z.to_nat j) = Some b -> bv_unsigned b <> 0%Z) ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 (q + 40 + p0 + 1)) x22 (Z_to_bv 64 srv) (Z_to_bv 64 af) (Z_to_bv 64 1) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16fa4) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B F0 L0 F8 F16 F24 F32 WB LW FRBm ST OL LL HP HOST SRV1 SRV2 P0 Z0 BH BND AF WZ WNZ.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    destruct (wb_string m wb (p0 + 1) z WB LW ltac:(lia) ltac:(lia) WZ) as [PSTR PL].
    set (pstr := firstn (Z.to_nat (z - (p0 + 1))) (skipn (Z.to_nat (p0 + 1)) wb)) in PSTR, PL. clearbody pstr.
    replace (q + 40 + (p0 + 1))%Z with (SP + -360 + p0 + 1)%Z in PSTR by lia.
    replace (q + 32)%Z with (SP + -368)%Z in F32 by lia.

    assert (EXIT : forall (p' s3v s5v : Z) y10 y11 y12 y13,
      (p0 + 1 <= p' <= z)%Z -> s3v = (q + 40 + p')%Z -> s5v = (q + 40 + p0 + 1)%Z ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) y10 y11 y12 y13 x14 x15 x16 x17
                              (Z_to_bv 64 U) (Z_to_bv 64 s3v) x20 (Z_to_bv 64 s5v) x22 (Z_to_bv 64 srv) (Z_to_bv 64 af) (Z_to_bv 64 1) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16fdc) fc None m (seg_rom rsegs))).
    { intros p' s3v s5v y10 y11 y12 y13 HP' -> ->.
      pwalk_to 0x16fe8%Z. step.
      unfold got_ssp, ssp_guard in *.
      callq (strtol10_call q lo (SP + -360 + p0 + 1)%Z pstr errv canary).
      all: side (first [exact PSTR | exact ERR | exact GOT | exact CAN | exact ST | exact MI | reflexivity | (f_equal; lia) | (unfold got_ssp, ssp_guard, STRTOL_DEPTH in *; lia)]).
      match goal with H : rw_cells _ _ TPE _ |- _ => rename H into ERR end.
      match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
      pwalk_to 0x17000%Z. if_cases K1; zify_cond K1.
      { pwalk_to 0x170dc%Z.
        replace (SP + -368)%Z with (q + 32)%Z in F32 by lia.
        pose proof (puri_C4C4_C8 _ (q + 8) [] bh2 [] F8 ltac:(lia)) as F8'. cbn [app] in F8'.
        destruct (frame5 U ulen ustr slack sp ULR _ c0 _ [C8 (Z_to_bv 64 (O + 64))] _ [C8 _] F0 L0 F8' F16 eq_refl F24 F32 eq_refl) as [FQ LQ].
        eapply fail; try eassumption; try reflexivity. close_base. }
      pwalk_to 0x17000%Z. step. call (atoi_spec). all: side (first [eassumption | lia]).
      pwalk_to 0x1702c%Z. if_cases K2; zify_cond K2.
      2:{ pwalk_to 0x170dc%Z.
        replace (SP + -368)%Z with (q + 32)%Z in F32 by lia.
        pose proof (puri_C4C4_C8 _ (q + 8) [] bh2 [] F8 ltac:(lia)) as F8'. cbn [app] in F8'.
        destruct (frame5 U ulen ustr slack sp ULR _ c0 _ [C8 (Z_to_bv 64 (O + 64))] _ [C8 _] F0 L0 F8' F16 eq_refl F24 F32 eq_refl) as [FQ LQ].
        eapply fail; try eassumption; try reflexivity. close_base. }
      replace (SP + -360 + p')%Z with (q + 40 + p')%Z by lia. replace (SP + -368)%Z with (q + 32)%Z in F32 by lia.
      eapply afsw with (bh2 := bh2) (size := p'); try eassumption; try reflexivity; try LiaTuning.alia. close_base. }
    assert (LOOP : forall (k : nat) (p a2v s3v s5v : Z) y13, (z - p < Z.of_nat k)%Z -> (p0 + 1 <= p < z)%Z ->
      a2v = (q + 40 + p)%Z -> s3v = (q + 40 + p)%Z -> s5v = (q + 40 + p0 + 1)%Z ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 (-1)) (Z_to_bv 64 10) (Z_to_bv 64 a2v) y13 x14 x15 x16 x17
                              (Z_to_bv 64 U) (Z_to_bv 64 s3v) x20 (Z_to_bv 64 s5v) x22 (Z_to_bv 64 srv) (Z_to_bv 64 af) (Z_to_bv 64 1) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16fc4) fc None m (seg_rom rsegs))).
    { induction k as [|k IH]; intros p a2v s3v s5v y13 HK HPp -> -> ->; [lia|].
      destruct (wb_nth wb (p + 1) LW ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
      pose proof (u8arr_read rsegs m _ wb (p + 1) b (Z_to_bv 64 (SP + -360 + p + 1)) WB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      pwalk_to 0x16fdc%Z. if_cases K0; zify_cond K0.
      - assert (p + 1 <> z)%Z.
        { intros E. rewrite E, WZ in Hb. injection Hb as Hb'. subst b. vm_compute in K0; try discriminate K0; lia. }
        eapply (IH (p + 1)%Z); lia.
      - eapply (EXIT (p + 1)%Z); lia. }
    destruct (wb_nth wb (p0 + 1) LW ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
    pose proof (u8arr_read rsegs m _ wb (p0 + 1) b (Z_to_bv 64 (SP + -360 + p0 + 1)) WB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    pwalk_to 0x16fdc%Z. if_cases K0; zify_cond K0.
    - eapply (EXIT (p0 + 1)%Z); lia.
    - assert (p0 + 1 <> z)%Z.
      { intros E. rewrite E, WZ in Hb. injection Hb as Hb'. subst b. vm_compute in K0; try discriminate K0; try (exfalso; apply K0; reflexivity); lia. }
      pwalk_to 0x16fc4%Z.
      eapply (LOOP (S (Z.to_nat (z - (p0 + 1)))) (p0 + 1)%Z); lia.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma split5 : forall m j0 a b c d, rw_cells rsegs m q [CB 8 j0; C8 a; C8 b; C8 c; C8 d] ->
    rw_cells rsegs m q [CB 8 j0] /\ rw_cells rsegs m (q + 8) [C8 a] /\ rw_cells rsegs m (q + 16) [C8 b] /\ rw_cells rsegs m (q + 24) [C8 c] /\ rw_cells rsegs m (q + 32) [C8 d].
  Proof.
    intros m j0 a b c d H. change [CB 8 j0; C8 a; C8 b; C8 c; C8 d] with ([CB 8 j0] ++ [C8 a] ++ [C8 b] ++ [C8 c] ++ [C8 d]) in H.
    apply rw_cells_app in H as [H0 H]. apply rw_cells_app in H as [H1 H]. apply rw_cells_app in H as [H2 H]. apply rw_cells_app in H as [H3 H4].
    cbn [cells_size csize Nat.add] in *.
    replace (q + Z.of_nat 8)%Z with (q + 8)%Z in H1 by lia. replace (q + Z.of_nat 8 + Z.of_nat 8)%Z with (q + 16)%Z in H2 by lia.
    replace (q + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (q + 24)%Z in H3 by lia.
    replace (q + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (q + 32)%Z in H4 by lia.
    exact (conj H0 (conj H1 (conj H2 (conj H3 H4)))).
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v4exit : forall (bh2 z j c ld e6 defport : Z) (bc : byte) (h j0 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x26 x28 x29 x30 x31
      m wb csL,
    baseP m -> rw_cells rsegs m q [CB 8 j0; C8 (Z_to_bv 64 bh2); C8 (Z_to_bv 64 (O + 64)); C8 (Z_to_bv 64 (U + bh2)); C8 (Z_to_bv 64 defport)] ->
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (0 <= j <= z)%Z -> (z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^16)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    nth_error wb (Z.to_nat j) = Some bc -> c = bv_unsigned bc ->
    (ld = 0 \/ exists d, ld = q + 40 + d /\ 0 <= d < j)%Z -> (e6 = q + 40 + j + 1)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 e6) x22 (Z_to_bv 64 ld) x24 (Z_to_bv 64 1) x26 (Z_to_bv 64 c) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16f20) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B FQ WB LW FRBm ST OL LL HP J Z0 BH BND DP WZ WNZ Hbc Hc LD E6. subst e6.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B. pose proof (byte_range bc) as BR.
    pwalk_to 0x16fa4%Z.
    pose proof (u8arr_store_ok rsegs _ _ _ j (Z_to_bv 64 (SP + -360 + j)) WB ltac:(rewrite LW; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
    replace (Z_to_bv 64 (SP + -360 + j)) with (wa (q + 40 + j)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write rsegs _ _ _ j (Z_to_bv 8 0) WB ltac:(rewrite LW; lia)) as WB2. clear WB. store_done.
    set (wb' := upd wb (Z.to_nat j) (Z_to_bv 8 0)) in WB2.
    assert (LW' : length wb' = 256%nat) by (subst wb'; rewrite upd_length; exact LW).
    assert (WZj : nth_error wb' (Z.to_nat j) = Some (Z_to_bv 8 0)) by (subst wb'; apply nth_error_upd_same; rewrite LW; lia).
    assert (WOTH : forall i, i <> Z.to_nat j -> nth_error wb' i = nth_error wb i) by (intros i Hi; subst wb'; apply nth_error_upd_other; lia).
    clearbody wb'.
    destruct (wb_string _ wb' 0 j WB2 LW' ltac:(lia) ltac:(lia) WZj) as [HOST HL]. rewrite Z.sub_0_r in HOST, HL.
    set (host := firstn (Z.to_nat j) (skipn (Z.to_nat 0) wb')) in HOST, HL. clearbody host.
    replace (q + 40 + 0)%Z with (SP + -360)%Z in HOST by lia.
    assert (WZ' : c <> 0%Z -> nth_error wb' (Z.to_nat z) = Some (Z_to_bv 8 0)).
    { intros Hc0. rewrite WOTH; [exact WZ|]. intros E. assert (j = z) by lia. subst j c. rewrite WZ in Hbc. injection Hbc as <-. apply Hc0. reflexivity. }
    assert (JZ : c <> 0%Z -> (j < z)%Z).
    { intros Hc0. destruct (Z.eq_dec j z); [|lia]. subst j c. rewrite WZ in Hbc. injection Hbc as <-. exfalso. apply Hc0. reflexivity. }
    assert (WNZ' : forall j' b, (j < j' < z)%Z -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z).
    { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
    destruct (split5 _ j0 _ _ _ _ FQ) as (F0 & F8 & F16 & F24 & F32).
    pose proof (puri_C8_C4C4 _ (q + 8) [] bh2 [] F8 ltac:(lia)) as F8'. cbn [app] in F8'. clear F8.
    destruct LD as [-> | (d & -> & Hd)].
    - pwalk_to 0x16fa4%Z. if_cases K0; zify_cond K0.
      + pwalk_to 0x1702c%Z. unfold wa.
        replace (SP + -360 + j)%Z with (q + 40 + j)%Z by lia.
        eapply afsw with (bh2 := bh2) (size := j) (srv := (SP + -360)%Z) (af := 0%Z) (host := host); try eassumption; try reflexivity; try (rewrite ?HL; lia). close_base.
      + pwalk_to 0x16fa4%Z. unfold wa. pwalk_to 0x16fa4%Z.
        rewrite ?unsigned_lit in K0 by lia.
        replace (SP + -360 + j + 1)%Z with (q + 40 + j + 1)%Z by lia.
        eapply (port bh2 j z (SP + -360) 0 _ host h); try eassumption; try reflexivity; try (rewrite ?HL; lia).
        * close_base.
        * apply WZ'; lia.
    - destruct (wb_nth wb' (d + 1) LW' ltac:(lia)) as [bd Hbd]. pose proof (byte_range bd) as BRd.
      pose proof (u8arr_read rsegs _ _ wb' (d + 1) bd (Z_to_bv 64 (SP + -360 + d + 1)) WB2 Hbd ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      pwalk_to 0x16fa4%Z. if_cases K0; zify_cond K0.
      + unfold wa. pwalk_to 0x1702c%Z.
        match goal with |- context [Z_to_bv 64 (Z.shiftl (Z.b2z ?b) 1)] =>
          set (af := Z.shiftl (Z.b2z b) 1); assert (AF : (af = 0 \/ af = 2 \/ af = 10)%Z) by (subst af; clear; destruct b; [right; left | left]; reflexivity); clearbody af end.
        replace (SP + -360 + j)%Z with (q + 40 + j)%Z by lia.
        eapply afsw with (bh2 := bh2) (size := j) (srv := (SP + -360)%Z) (af := af) (host := host); try eassumption; try reflexivity; try (rewrite ?HL; lia). close_base.
      + unfold wa. pwalk_to 0x16fa4%Z.
        match goal with |- context [Z_to_bv 64 (Z.shiftl (Z.b2z ?b) 1)] =>
          set (af := Z.shiftl (Z.b2z b) 1); assert (AF : (af = 0 \/ af = 2 \/ af = 10)%Z) by (subst af; clear; destruct b; [right; left | left]; reflexivity); clearbody af end.
        rewrite ?unsigned_lit in K0 by lia.
        replace (SP + -360 + j + 1)%Z with (q + 40 + j + 1)%Z by lia.
        eapply (port bh2 j z (SP + -360) af _ host h); try eassumption; try reflexivity; try (rewrite ?HL; lia).
        * close_base.
        * apply WZ'; lia.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v4loop : forall (bh2 z defport : Z) (h j0 : list byte) m wb csL (k : nat) (j c ld e6 : Z) (bc : byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 8 j0; C8 (Z_to_bv 64 bh2); C8 (Z_to_bv 64 (O + 64)); C8 (Z_to_bv 64 (U + bh2)); C8 (Z_to_bv 64 defport)] ->
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^16)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    (z - j < Z.of_nat k)%Z -> (0 <= j <= z)%Z ->
    nth_error wb (Z.to_nat j) = Some bc -> c = bv_unsigned bc ->
    (ld = 0 \/ exists d, ld = q + 40 + d /\ 0 <= d < j)%Z -> (e6 = q + 40 + j + 1)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 58) (Z_to_bv 64 2) (Z_to_bv 64 e6) (Z_to_bv 64 46) (Z_to_bv 64 ld) (Z_to_bv 64 47) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 c) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16ef0) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros k. induction k as [|k IH]; intros until x31; intros B FQ WB LW FRBm ST OL LL HP Z0 BH BND DP WZ WNZ HK J Hbc Hc LD E6; [lia|].
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. pose proof (byte_range bc) as BR.
    pose proof B as B0. open_base B.
    zstep. if_cases K0; zify_cond K0.
    {   eapply v4exit; try eassumption; try LiaTuning.alia. }
    zstep. if_cases K1; zify_cond K1.
    {   eapply v4exit; try eassumption; try LiaTuning.alia. }
    zstep. replace (Z.land c 255) with c by (subst c; change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    zstep. call isalnum_spec. all: side (rewrite ?unsigned_lit by lia; first [exact MI | lia]).
    rewrite unsigned_lit by lia.

    assert (ADV : forall (e5 : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y23 y27 y28 y29 y30 y31, (e5 = 0 \/ exists d, e5 = q + 40 + d /\ 0 <= d < j + 1)%Z -> c <> 0%Z ->
      evt rsegs POST (MS (mkR y1 spw gp tp y5 y6 y7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 e5) y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 U) (Z_to_bv 64 58) (Z_to_bv 64 2) (Z_to_bv 64 e6) (Z_to_bv 64 46) y23 (Z_to_bv 64 47) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x16ee4) fc None m (seg_rom rsegs))).
    { intros until y31. intros LD' Hc0.
      assert (JZ : (j < z)%Z).
      { destruct (Z.eq_dec j z); [|lia]. subst j c. rewrite WZ in Hbc. injection Hbc as <-. exfalso. apply Hc0. reflexivity. }
      destruct (wb_nth wb (j + 1) LW ltac:(lia)) as [b' Hb']. pose proof (byte_range b') as BR'.
      pose proof (u8arr_read rsegs _ _ wb (j + 1) b' (Z_to_bv 64 e6) WB Hb' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. zstep. zstep.
      eapply (IH (j + 1)%Z); try eassumption; try LiaTuning.alia. }

    assert (DASH : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31, (c = 45 \/ c = 46 \/ is_alnum c = true)%Z ->
      evt rsegs POST (MS (mkR y1 spw gp tp y5 y6 y7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 U) (Z_to_bv 64 58) (Z_to_bv 64 2) (Z_to_bv 64 e6) (Z_to_bv 64 46) (Z_to_bv 64 ld) (Z_to_bv 64 47) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 c) y28 y29 y30 y31)
                        F (Z_to_bv 64 0x16f0c) fc None m (seg_rom rsegs))).
    { intros until y31. intros HC.
      assert (Hc0 : c <> 0%Z). { destruct HC as [-> | [-> | HA]]; [lia| lia| apply is_alnum_nz; exact HA]. }
      zstep. step.
      first [ ubr
            | ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; try change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia) ].
      zstep. if_cases K3; zify_cond K3.
      -   eapply ADV; [| exact Hc0]. right. exists j. lia.
      -   zstep. zstep. eapply ADV; [| exact Hc0]. destruct LD as [-> | (d & -> & Hd)]; [left; reflexivity | right; exists d; lia]. }
    zstep. zstep. if_cases K2; zify_cond K2.
    {   apply wrap_sub_lt in K2; [|lia|lia|lia]. apply DASH. lia. }
    zstep. if_cases K4; zify_cond K4.
    {   eapply v4exit; try eassumption; try LiaTuning.alia. }
    apply DASH. right. right. first [exact K4 | destruct (is_alnum c); [reflexivity| exfalso; first [discriminate | apply K4; reflexivity]]].
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v4 : forall (bh2 z defport c0 : Z) (b0 : byte) (h j0 : list byte) m wb csL
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 8 j0; C8 (Z_to_bv 64 bh2); C8 (Z_to_bv 64 (O + 64)); C8 (Z_to_bv 64 (U + bh2)); C8 (Z_to_bv 64 defport)] ->
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (0 <= z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^16)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    nth_error wb 0%nat = Some b0 -> c0 = bv_unsigned b0 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 (SP + -360)) x20 x21 x22 x23 x24 (Z_to_bv 64 1) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 c0) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16ec4) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FQ WB LW FRBm ST OL LL HP Z0 BH BND DP WZ WNZ Hb0 Hc0.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. pose proof (byte_range b0) as BR. open_base B.
    pose proof OAL as OA. unfold oal in OA.
    pwalk_to 0x16ef0%Z.
    eapply (v4loop bh2 z defport h _ _ wb csL (S (Z.to_nat z)) 0 c0 0 _ b0); try eassumption; try reflexivity; try lia. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v6 : forall (bh2 z defport : Z) (h j0 : list byte) m wb csL
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 8 j0; C8 (Z_to_bv 64 bh2); C8 (Z_to_bv 64 (O + 64)); C8 (Z_to_bv 64 (U + bh2)); C8 (Z_to_bv 64 defport)] ->
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (0 <= z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^16)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    nth_error wb 0%nat = Some (Z_to_bv 8 91) ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 (SP + -360)) x20 x21 x22 x23 x24 (Z_to_bv 64 1) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 91) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16e90) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FQ WB LW FRBm ST OL LL HP Z0 BH BND DP WZ WNZ Hb0.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    assert (Z1 : (1 <= z)%Z).
    { destruct (Z.eq_dec z 0); [|lia]. exfalso. subst z. change (Z.to_nat 0) with 0%nat in WZ. rewrite WZ in Hb0. injection Hb0 as E. vm_compute in E. lia. }

    assert (FOUND : forall (j a0v : Z) y11 y12 y13,
      (1 <= j < z)%Z -> a0v = (q + 40 + j)%Z -> nth_error wb (Z.to_nat j) = Some (Z_to_bv 8 93) ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 a0v) y11 y12 y13 x14 x15 x16 x17
                              (Z_to_bv 64 U) (Z_to_bv 64 (SP + -360)) x20 x21 x22 (Z_to_bv 64 (SP + -359)) x24 (Z_to_bv 64 1) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 91) x28 x29 x30 x31)
                          F (Z_to_bv 64 0x16f78) fc None m (seg_rom rsegs))).
    { intros j a0v y11 y12 y13 J -> Hj.
      destruct (wb_nth wb (j + 1) LW ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
      pose proof (u8arr_read rsegs _ _ wb (j + 1) b1 (Z_to_bv 64 (SP + -360 + j + 1)) WB Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      pwalk_to 0x17018%Z.
      pose proof (u8arr_store_ok rsegs _ _ _ j (Z_to_bv 64 (SP + -360 + j)) WB ltac:(rewrite LW; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
      zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
      replace (Z_to_bv 64 (SP + -360 + j)) with (wa (q + 40 + j)) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write rsegs _ _ _ j (Z_to_bv 8 0) WB ltac:(rewrite LW; lia)) as WB2. clear WB RD. store_done.
      set (wb' := upd wb (Z.to_nat j) (Z_to_bv 8 0)) in WB2.
      assert (LW' : length wb' = 256%nat) by (subst wb'; rewrite upd_length; exact LW).
      assert (WZj : nth_error wb' (Z.to_nat j) = Some (Z_to_bv 8 0)) by (subst wb'; apply nth_error_upd_same; rewrite LW; lia).
      assert (WOTH : forall i, i <> Z.to_nat j -> nth_error wb' i = nth_error wb i) by (intros i Hi; subst wb'; apply nth_error_upd_other; lia).
      clearbody wb'.
      destruct (wb_string _ wb' 1 j WB2 LW' ltac:(lia) ltac:(lia) WZj) as [HOST HL].
      set (host := firstn (Z.to_nat (j - 1)) (skipn (Z.to_nat 1) wb')) in HOST, HL. clearbody host.
      replace (q + 40 + 1)%Z with (SP + -359)%Z in HOST by lia.
      destruct (split5 _ j0 _ _ _ _ FQ) as (F0 & F8 & F16 & F24 & F32).
      pose proof (puri_C8_C4C4 _ (q + 8) [] bh2 [] F8 ltac:(lia)) as F8'. cbn [app] in F8'. clear F8.
      pwalk_to 0x1702c%Z. if_cases K0; zify_cond K0.
      - pwalk_to 0x1702c%Z.
        replace (SP + -360 + j + 1)%Z with (q + 40 + (j + 1))%Z by lia.
        eapply afsw with (bh2 := bh2) (size := (j + 1)%Z) (srv := (SP + -359)%Z) (af := 10%Z) (host := host); try eassumption; try reflexivity; try (rewrite ?HL; lia). close_base.
      - assert (J1 : (j + 1 < z)%Z).
        { destruct (Z.eq_dec (j + 1) z) as [e|]; [|lia]. exfalso. rewrite <- e, Hb1 in WZ. injection WZ as ->. revert K0. clear. intros K0. vm_compute in K0. lia. }
        pwalk_to 0x16fa4%Z.
        replace (SP + -360 + j + 2)%Z with (q + 40 + (j + 1) + 1)%Z by lia.
        eapply (port bh2 (j + 1) z (SP + -359) 10 _ host h); try eassumption; try reflexivity; try (rewrite ?HL; lia).
        + close_base.
        + rewrite WOTH by lia. exact WZ.
        + intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
    assert (LOOP : forall (k : nat) (j a0v : Z) (bc : byte),
      (z - j < Z.of_nat k)%Z -> (1 <= j <= z)%Z -> nth_error wb (Z.to_nat j) = Some bc -> bv_unsigned bc <> 0%Z -> a0v = (q + 40 + j)%Z ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 a0v) (Z_to_bv 64 (-1)) (Z_to_bv 64 93) (zxb bc) x14 x15 x16 x17
                              (Z_to_bv 64 U) (Z_to_bv 64 (SP + -360)) x20 x21 x22 (Z_to_bv 64 (SP + -359)) x24 (Z_to_bv 64 1) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 91) x28 x29 x30 x31)
                          F (Z_to_bv 64 0x16eac) fc None m (seg_rom rsegs))).
    { induction k as [|k IH]; intros j a0v bc HK J Hbc Hc0 ->; [lia|]. pose proof (byte_range bc) as BR.
      assert (JZ : (j < z)%Z).
      { destruct (Z.eq_dec j z); [|lia]. exfalso. subst j. rewrite WZ in Hbc. injection Hbc as <-. apply Hc0. reflexivity. }
      pwalk_to 0x16f78%Z. if_cases K0; zify_cond K0.
      {   eapply (FOUND j); try lia. rewrite Hbc. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 93) with 93%Z. rewrite unsigned_lit in K0 by lia. exact K0. }
      destruct (wb_nth wb (j + 1) LW ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
      pose proof (u8arr_read rsegs _ _ wb (j + 1) b1 (Z_to_bv 64 (SP + -360 + j + 1)) WB Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      pwalk_to 0x16eac%Z. if_cases K1; zify_cond K1.
      - rewrite unsigned_lit in K1 by lia. eapply (IH (j + 1)%Z _ b1); try eassumption; try lia.
      - pwalk_to 0x170dc%Z. eapply fail; try eassumption; try reflexivity. close_base. }
    destruct (wb_nth wb 1 LW ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
    pose proof (u8arr_read rsegs _ _ wb 1 b1 (Z_to_bv 64 (SP + -360 + 1)) WB Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    pwalk_to 0x16eac%Z. if_cases K0; zify_cond K0.
    {   pwalk_to 0x170dc%Z. eapply fail; try eassumption; try reflexivity. close_base. }
    rewrite unsigned_lit in K0 by lia. eapply (LOOP (S (Z.to_nat z)) 1 _ b1); try eassumption; try lia.
  Qed.

  #[using="U ulen ustr slack canary tp m0 ULR DE1 DE2 DE3 DE4 DE5"] Lemma nul_split : forall (l1 l2 : list byte), exists s r, l1 ++ Z_to_bv 8 0 :: l2 = s ++ Z_to_bv 8 0 :: r /\ ~ In (Z_to_bv 8 0) s /\ (length s <= length l1)%nat.
  Proof.
    induction l1 as [|a l1 IH]; intros l2.
    - exists [], l2. cbn. repeat split; [LiaTuning.ctauto| lia].
    - destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
      + exists [], (l1 ++ Z_to_bv 8 0 :: l2). assert (a = Z_to_bv 8 0) as -> by (apply bv_eq; rewrite E; reflexivity).
        cbn. repeat split; [LiaTuning.ctauto| lia].
      + destruct (IH l2) as (s & r & E & NI & L). exists (a :: s), r. cbn. rewrite E. repeat split; [| cbn in *; lia].
        intros [H|H]; [| exact (NI H)]. apply NE. subst a. reflexivity.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma mod8_shift : forall x d, 0 <= d -> (x + d) mod 8 <= x mod 8 + d.
  Proof.
    intros x d Hd. rewrite <- Z.add_mod_idemp_l by lia. apply Z.mod_le; [| lia]. pose proof (Z.mod_pos_bound x 8). lia.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_nth_lt : forall (str : list byte) j, (j < stpn_k str 255)%nat -> nth_error (stpn_result str 255 ++ [Z_to_bv 8 0]) j = nth_error str j.
  Proof.
    intros str j Hj. unfold stpn_result. pose proof (Nat.le_min_l (length str) 255). unfold stpn_k in *.
    rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
    rewrite nth_error_app1 by (rewrite firstn_length; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec0 j (Nat.min (length str) 255)); [reflexivity| lia].
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_nth_z : forall (str : list byte), nth_error (stpn_result str 255 ++ [Z_to_bv 8 0]) (stpn_k str 255) = Some (Z_to_bv 8 0).
  Proof.
    intros str. unfold stpn_result. pose proof (Nat.le_min_l (length str) 255). pose proof (Nat.le_min_r (length str) 255). unfold stpn_k in *.
    set (k := Nat.min (length str) 255) in *.
    destruct (Nat.eq_dec k 255).
    - rewrite nth_error_app2. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
      rewrite length_app, firstn_length, repeat_length. replace (k - (Nat.min k (length str) + (255 - k)))%nat with 0%nat by lia. reflexivity.
    - rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
      rewrite nth_error_app2 by (rewrite firstn_length; lia). rewrite firstn_length.
      replace (k - Nat.min k (length str))%nat with 0%nat by lia.
      destruct (255 - k)%nat eqn:E; [lia|]. reflexivity.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma u8arr_snoc1 : forall m A bs b, u8arr rsegs m A bs -> rw_cells rsegs m (A + Z.of_nat (length bs)) [C1 b] -> u8arr rsegs m A (bs ++ [b]).
  Proof.
    intros m A bs b [B W] [[_ B1] W1]. cbn [cells_bytes cbytes cells_size csize app Nat.add] in B1, W1. split.
    - apply bytes_at_app. split; [exact B| exact B1].
    - rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. apply (proj2 (wr_at_app rsegs m A (Z.of_nat (length bs)) (Z.of_nat 1) ltac:(lia) ltac:(lia))). split; [exact W| exact W1].
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma hp : forall (bh2 defport : Z) m jA jB junk
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 32 jA; C8 (Z_to_bv 64 defport); CB 256 jB] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 216 junk] ->
    (0 <= bh2 <= ulen)%Z -> (0 <= defport < 2^16)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 1) (Z_to_bv 64 bh2) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16e4c) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FRA FRBm ST OUT BH DP.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B. pose proof USTR_len as UL.
    pose proof OAL as OA. unfold oal in OA.

    pose proof (rw_cells_split_CB rsegs m O [] 216 junk [] [64; 152]%nat OUT eq_refl) as OUT'. cbn [mk_CB_cells app] in OUT'. clear OUT.
    lazymatch type of OUT' with rw_cells _ _ _ [?a; ?b] => change (rw_cells rsegs m O ([a] ++ [b])) in OUT' end.
    apply rw_cells_app in OUT'. destruct OUT' as [OL HP]. cbn [cells_size csize Nat.add] in HP. change (Z.of_nat 64) with 64%Z in HP.
    pwalk_to 0x16e64%Z. zstep.
    lazymatch type of HP with rw_cells _ _ _ [CB _ ?h] => call (memset0_call (O + 64) 152 h) end.
    all: side (first [exact HP | exact MI | reflexivity | lia]).
    match goal with H : rw_cells _ _ (O + 64)%Z _ |- _ => rename H into HP end. change (Z.to_nat 152) with 152%nat in HP.
    set (h := repeat (Z_to_bv 8 0) 152) in HP. clearbody h.
    pwalk_to 0x16e80%Z.

    destruct (nul_split (skipn (Z.to_nat bh2) ustr) slack) as (str & rest & ES & NI & LS). rewrite skipn_length in LS.
    pose proof (bytes_at_drop _ U _ (Z.to_nat bh2) USTR ltac:(rewrite app_length; cbn [length]; lia)) as SRC. rewrite Z2Nat.id in SRC by lia.
    rewrite skipn_app in SRC. replace (Z.to_nat bh2 - length ustr)%nat with 0%nat in SRC by lia. cbn [skipn] in SRC. rewrite ES in SRC.
    assert (LR : (Z.of_nat (length rest) = ulen - bh2 - Z.of_nat (length str) + Z.of_nat (length slack))%Z).
    { pose proof (f_equal (@length byte) ES) as EL. rewrite !length_app, skipn_length in EL. cbn [length] in EL. rewrite ?length_app in EL. cbn [length] in EL. lia. }
    assert (PAD' : ((- (U + bh2 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length rest))%Z).
    { replace (- (U + bh2 + Z.of_nat (length str) + 1))%Z with (- (U + ulen + 1) + (ulen - bh2 - Z.of_nat (length str)))%Z by lia.
      etransitivity; [apply mod8_shift; lia|]. lia. }

    lazymatch goal with FQ : rw_cells _ ?m' q [?a0; ?a8; ?a16; ?a24; ?a32; CB 255 ?w; ?c1] |- _ =>
      change (rw_cells rsegs m' q ([a0; a8; a16; a24; a32] ++ [CB 255 w] ++ [c1])) in FQ;
      apply rw_cells_take3 in FQ; destruct FQ as (FQ & WB0 & NUL1); cbn [cells_size csize Nat.add] in WB0, NUL1 end.
    change (Z.of_nat 40) with 40%Z in *. change (Z.of_nat 295) with 295%Z in *.
    pose proof (rw_CB_len _ _ _ _ WB0) as LW0. apply u8arr_of_rw_cells in WB0.
    zstep.
    replace (q + 40)%Z with (SP + -360)%Z in WB0 by lia.
    callq (strncpy_call q lo (SP + -360)%Z (U + bh2)%Z 255 str rest).
    all: side (first [exact WB0 | exact LW0 | exact SRC | exact NI | exact PAD' | exact ST | assumption | reflexivity | (f_equal; lia) | lia]).
    match goal with H : u8arr _ _ _ (stpn_result _ _) |- _ => rename H into WB1 end. change (Z.to_nat 255) with 255%nat in WB1.
    match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
    replace (q + 40 + Z.of_nat 255)%Z with (SP + -360 + Z.of_nat (length (stpn_result str 255)))%Z in NUL1 by (rewrite stpn_result_length; lia).
    pose proof (u8arr_snoc1 _ _ _ _ WB1 NUL1) as WB. clear WB1 NUL1.
    set (wb := stpn_result str 255 ++ [Z_to_bv 8 0]) in WB.
    assert (LW : length wb = 256%nat) by (subst wb; rewrite length_app, stpn_result_length; reflexivity).
    set (zn := stpn_k str 255). assert (ZN : (zn <= length str /\ zn <= 255)%nat) by (subst zn; unfold stpn_k; split; [apply Nat.le_min_l | apply Nat.le_min_r]).
    assert (WZ : nth_error wb (Z.to_nat (Z.of_nat zn)) = Some (Z_to_bv 8 0)) by (rewrite Nat2Z.id; subst wb zn; apply wb_nth_z).
    assert (WNZ : forall j' b, (0 <= j' < Z.of_nat zn)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z).
    { intros j' b Hj' Hb E0. subst wb. rewrite wb_nth_lt in Hb by lia. apply NI. assert (b = Z_to_bv 8 0) as <- by (apply bv_eq; rewrite E0; reflexivity).
      eapply nth_error_In. exact Hb. }
    clearbody wb zn.
    destruct (wb_nth wb 0 LW ltac:(lia)) as [b0 Hb0]. pose proof (byte_range b0) as BR0. change (Z.to_nat 0) with 0%nat in Hb0.
    pose proof (u8arr_read rsegs _ _ wb 0 b0 (Z_to_bv 64 (SP + -360)) WB Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    replace (O + 64 + 152)%Z with (O + 216)%Z in * by lia.
    pwalk_to 0x16ec4%Z. if_cases K0; zify_cond K0.
    -
      replace (SP + -360)%Z with (q + 40)%Z in WB by lia.
      eapply (v4 bh2 (Z.of_nat zn) defport); try eassumption; try reflexivity; try lia. close_base.
    -
      replace (SP + -360)%Z with (q + 40)%Z in WB by lia.
      assert (b0 = Z_to_bv 8 91) as E91 by (apply bv_eq; rewrite K0; reflexivity). rewrite E91 in Hb0. rewrite K0.
      eapply (v6 bh2 (Z.of_nat zn) defport); try eassumption; try reflexivity; try lia. close_base.
  Qed.
End WALK.
