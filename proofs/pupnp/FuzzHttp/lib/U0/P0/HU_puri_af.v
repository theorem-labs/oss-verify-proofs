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
     F_inet_pton_A F_inet_pton_C H_parse_uric H_parse_uri_A H_parse_uri_B HU_list_kit.
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

  #[using="U ulen slack ULR U4K ULO SPH"] Lemma af_sp_range : (928 <= SP /\ SP + 2^41 <= 2^63)%Z.
  Proof. clear -ULR U4K ULO SPH. pose proof (word_lt64 sp). lia. Qed.
  #[using="U ulen ustr slack ULR U4K ULO SPH GFLO"] Lemma af_q_sp : bv_unsigned spw = q.
  Proof. pose proof af_sp_range. apply unsigned_lit. lia. Qed.

  #[using="Type"] Lemma split4 : forall m A l0 l1 l2 l3, rw_cells rsegs m A (l0 ++ l1 ++ l2 ++ l3) ->
    rw_cells rsegs m A l0 /\ rw_cells rsegs m (A + Z.of_nat (cells_size l0)) l1
    /\ rw_cells rsegs m (A + Z.of_nat (cells_size l0) + Z.of_nat (cells_size l1)) l2
    /\ rw_cells rsegs m (A + Z.of_nat (cells_size l0) + Z.of_nat (cells_size l1) + Z.of_nat (cells_size l2)) l3.
  Proof.
    intros m A l0 l1 l2 l3 H. apply rw_cells_app in H. destruct H as [H0 H]. apply rw_cells_app in H. destruct H as [H1 H].
    apply rw_cells_app in H. destruct H as [H2 H3]. auto.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma v6fill : forall (bh2 size srv : Z) (pw : word) (host h hr : list byte)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x26 x27 x28 x29 x30 x31
      m c0 wb csL,
    baseP m -> rw_cells rsegs m q c0 -> cells_size c0 = 8%nat -> rw_cells rsegs m (q + 8) [C4 (Z_to_bv 64 bh2); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (q + 16) [C8 (Z_to_bv 64 (O + 64))] -> rw_cells rsegs m (q + 24) [C8 (Z_to_bv 64 (U + bh2))] -> rw_cells rsegs m (q + 32) [C8 pw] ->
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 144 h; C2 pw; CB 6 hr] ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 40 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 296)%Z ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 10) x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 (q + 40 + size)) x22 (Z_to_bv 64 srv) (Z_to_bv 64 10) (Z_to_bv 64 1) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x17064) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B F0 L0 F8 F16 F24 F32 WB LW FRBm ST OL LL HP HOST SRV1 SRV2 SZ BH BND.
    pose proof af_sp_range as SR. pose proof af_q_sp as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    pose proof (word_lt64 pw) as PW.
    replace (q + 32)%Z with (SP + -368)%Z in F32 by lia.
    sstep. zstep. zstep. zstep.
    change 65535%Z with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^16) ltac:(lia)) as P16.
    zstep. call htons_spec. all: side (rewrite ?unsigned_lit by lia; first [exact MI | lia]).
    rewrite unsigned_lit by lia.
    zstep. zstep. zstep. sstep. sstep. zstep.
    lazymatch type of HP with rw_cells _ ?m' _ [?c0; ?c1; ?c2; CB 20 ?d; ?c4; ?c5; ?c6; ?c7] =>
      pose proof (rw_cells_split_CB rsegs m' (O + 64) [c0; c1; c2] 20 d [c4; c5; c6; c7] [4; 16]%nat HP eq_refl) as HP'; clear HP;
      cbn [mk_CB_cells app] in HP';
      lazymatch type of HP' with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?cN; ?c4; ?c5; ?c6; ?c7] =>
        change (rw_cells rsegs m' (O + 64) ([c0] ++ [c1; c2; c3] ++ [cN] ++ [c4; c5; c6; c7])) in HP' end end.
    apply split4 in HP'. destruct HP' as (H0 & HL & OC & HR). cbn [cells_size csize Nat.add] in HL, OC, HR.
    change (Z.of_nat 16) with 16%Z in *. change (Z.of_nat 8) with 8%Z in *.
    replace (O + 64 + 16)%Z with (O + 80)%Z in HL by lia. replace (O + 64 + 16 + 8)%Z with (O + 80 + 8)%Z in OC by lia.
    replace (O + 64 + 16 + 8 + 16)%Z with (O + 80 + 8 + Z.of_nat 16)%Z in HR by lia.
    replace (SP + -368)%Z with (q + 32)%Z in * by lia.
    try replace (SP + -360 + size)%Z with (q + 40 + size)%Z by lia.
    eapply inet with (nl := 8); try eassumption; try reflexivity; try lia. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma afsw : forall (bh2 size srv af : Z) (pw : word) (host h : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x26 x27 x28 x29 x30 x31
      m c0 wb csL,
    baseP m -> rw_cells rsegs m q c0 -> cells_size c0 = 8%nat -> rw_cells rsegs m (q + 8) [C4 (Z_to_bv 64 bh2); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (q + 16) [C8 (Z_to_bv 64 (O + 64))] -> rw_cells rsegs m (q + 24) [C8 (Z_to_bv 64 (U + bh2))] -> rw_cells rsegs m (q + 32) [C8 pw] ->
    u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 40 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 296)%Z ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z -> (af = 0 \/ af = 2 \/ af = 10)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 (q + 40 + size)) x22 (Z_to_bv 64 srv) (Z_to_bv 64 af) (Z_to_bv 64 1) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x1702c) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B F0 L0 F8 F16 F24 F32 WB LW FRBm ST OL LL HP HOST SRV1 SRV2 SZ BH BND AF.
    pose proof af_sp_range as SR. pose proof af_q_sp as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    pose proof (word_lt64 pw) as PW.
    replace (q + 32)%Z with (SP + -368)%Z in F32 by lia.
    zstep. zstep. sstep.
    zstep. if_cases K0; zify_cond K0.
    { replace af with 10%Z by lia. replace (SP + -368)%Z with (q + 32)%Z in * by lia.
      try replace (SP + -360 + size)%Z with (q + 40 + size)%Z by lia.
      eapply v6fill; try eassumption; try LiaTuning.alia. close_base. }
    zstep. zstep. if_cases K1; zify_cond K1.
    {
      lazymatch type of HP with rw_cells _ ?m' _ [CB 144 ?d; ?c1; ?c2] =>
        pose proof (rw_cells_split_CB rsegs m' (O + 64) [] 144 d [c1; c2] [16; 128]%nat HP eq_refl) as HP'; clear HP;
        cbn [mk_CB_cells app] in HP';
        lazymatch type of HP' with rw_cells _ _ _ [?c0; ?cA; ?cB; ?cC] =>
          change (rw_cells rsegs m' (O + 64) ([c0] ++ [cA; cB; cC])) in HP' end end.
      apply rw_cells_app in HP'. destruct HP' as [H0 HH]. cbn [cells_size csize Nat.add] in HH. change (Z.of_nat 16) with 16%Z in HH.
      replace (O + 64 + 16)%Z with (O + 80)%Z in HH by lia. replace (SP + -368)%Z with (q + 32)%Z in * by lia.
      try replace (SP + -360 + size)%Z with (q + 40 + size)%Z by lia.
      eapply hpend; try eassumption; try reflexivity; try lia. close_base. }
    replace af with 2%Z by lia.
    sstep. zstep. zstep. zstep.
    change 65535%Z with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^16) ltac:(lia)) as P16.
    zstep. call htons_spec. all: side (rewrite ?unsigned_lit by lia; first [exact MI | lia]).
    rewrite unsigned_lit by lia.
    sstep. zstep. zstep.
    lazymatch type of HP with rw_cells _ ?m' _ [?c0; ?c1; ?c2; CB 124 ?d; ?c6; ?c7] =>
      pose proof (rw_cells_split_CB rsegs m' (O + 64) [c0; c1; c2] 124 d [c6; c7] [4; 120]%nat HP eq_refl) as HP'; clear HP;
      cbn [mk_CB_cells app] in HP';
      lazymatch type of HP' with rw_cells _ _ _ [?c0; ?c1; ?c2; ?cN; ?c4; ?c6; ?c7] =>
        change (rw_cells rsegs m' (O + 64) ([c0] ++ [c1; c2] ++ [cN] ++ [c4; c6; c7])) in HP' end end.
    apply split4 in HP'. destruct HP' as (H0 & HL & OC & HR). cbn [cells_size csize Nat.add] in HL, OC, HR.
    change (Z.of_nat 16) with 16%Z in *. change (Z.of_nat 4) with 4%Z in *.
    replace (O + 64 + 16)%Z with (O + 80)%Z in HL by lia. replace (O + 64 + 16 + 4)%Z with (O + 80 + 4)%Z in OC by lia.
    replace (O + 64 + 16 + 4 + 4)%Z with (O + 80 + 4 + Z.of_nat 4)%Z in HR by lia.
    replace (SP + -368)%Z with (q + 32)%Z in * by lia.
    try replace (SP + -360 + size)%Z with (q + 40 + size)%Z by lia.
    eapply inet with (nl := 4); try eassumption; try reflexivity; try lia. close_base.
  Qed.
End WALK.
