(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition MEMMOVE_ENTRY : Z := 0xd027c.
Definition MM_MEMCPY : Z := 0xcfe78.

Section MEMMOVE.
  Hypothesis HMEMCPY : memcpyZ_stmt_g usegs MM_MEMCPY.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D S N U : Z) (L : nat) (m0 : mem).
  Hypothesis HUS : (U <= S)%Z.
  Hypothesis HSD : (S <= D < 2^64)%Z.
  Hypothesis HDN : (D + N <= U + Z.of_nat L)%Z.
  Hypothesis HN : (0 <= N < 2^62)%Z.
  Hypothesis HAL : ((D - S) mod 8 = 0)%Z.

  Notation POST := (memmove_post_g usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D N U L m0).
  Notation MM pc xa1 xa2 xa3 xa4 xa5 xa6 xa7 mm :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition MMINV (mm : mem) : Prop :=
    (exists bs, u8arr usegs mm U bs /\ length bs = L) /\ mem_inv usegs mm /\ munch [(D, D + N)]%Z m0 mm /\ wmono usegs m0 mm.

  Ltac mm_open H := let bs := fresh "bs" in destruct H as ((bs & UA & UL) & MI & MU & WM);
    pose proof (u8arr_bound _ _ _ _ UA) as UB; rewrite UL in UB.
  Ltac mm_close := lazymatch goal with |- MMINV _ =>
    split; [eexists; split; [eassumption| rewrite ?upd_bytes_length by (rewrite ?length_le8, ?length_le1; cbn [length]; lia); assumption]|];
    split; [eassumption|]; split; eassumption end.

  Lemma mm_ret : forall xa1 xa2 xa3 xa4 xa5 xa6 xa7 mm, MMINV mm -> evt usegs POST (MM 0xd0308 xa1 xa2 xa3 xa4 xa5 xa6 xa7 mm).
  Proof using.
    intros until mm. intros INV. mm_open INV.
    zstep.
    apply evt_done. unfold memmove_post_g. do 14 eexists. exists mm, bs.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA| exact UL].
  Qed.

  Lemma mm_BL : forall (f : nat) (r : Z) xa4 xa5 xa6 xa7 mm,
    MMINV mm -> (1 <= r <= N)%Z -> (r <= Z.of_nat f)%Z ->
    evt usegs POST (MM 0xd02f0 (Z_to_bv 64 (S + r - 1)) (Z_to_bv 64 (- r)) (Z_to_bv 64 (D + r - 1)) xa4 xa5 xa6 xa7 mm).
  Proof using HUS HSD HDN HN.
    intros f. induction f as [|f IH]; intros r xa4 xa5 xa6 xa7 mm INV Hr Hf; [exfalso; lia|].
    mm_open INV.
    destruct (u8arr_read1 usegs mm U bs (S + r - 1 - U) UA ltac:(lia)) as [b RD].
    replace (U + (S + r - 1 - U))%Z with (S + r - 1)%Z in RD by lia.
    zstep. zstep.
    u8_store UA (D + r - 1 - U)%Z 1%nat.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - assert (R1 : (r - 1 <> 0)%Z).
      { intros E0. apply K. replace (- r + 1)%Z with (- (r - 1))%Z by lia. apply neg_mod64_zero; lia. }
      eapply evt_eq; [| eapply (IH (r - 1)%Z); [mm_close | lia | lia]]. num_st_eq.
    - eapply mm_ret. mm_close.
  Qed.

  Lemma mm_150 : forall (r : Z) xa2 xa4 xa5 xa6 xa7 mm,
    MMINV mm -> (0 <= r <= N)%Z ->
    evt usegs POST (MM 0xd02dc (Z_to_bv 64 S) xa2 (Z_to_bv 64 r) xa4 xa5 xa6 xa7 mm).
  Proof using HUS HSD HDN HN.
    intros until mm. intros INV Hr.
    zstep.
    if_cases K; zify_cond K.
    { eapply mm_ret. exact INV. }
    zstep. zstep. zstep. zstep.
    eapply evt_eq; [| eapply (mm_BL (Z.to_nat r) r); [exact INV | lia | lia]]. num_st_eq.
  Qed.

  Lemma mm_WL : forall (f : nat) (r : Z) xa3 xa7 mm,
    MMINV mm -> (8 <= r <= N)%Z -> (r <= Z.of_nat f)%Z ->
    evt usegs POST (MM 0xd03a8 (Z_to_bv 64 S) (Z_to_bv 64 r) xa3 (Z_to_bv 64 (S + -8)) (Z_to_bv 64 (D + -8)) (Z_to_bv 64 7) xa7 mm).
  Proof using HUS HSD HDN HN.
    intros f. induction f as [|f IH]; intros r xa3 xa7 mm INV Hr Hf; [exfalso; lia|].
    mm_open INV.
    destruct (u8arr_read8 usegs mm U bs (S + r - 8 - U) UA ltac:(lia) ltac:(lia)) as [w RD].
    replace (U + (S + r - 8 - U))%Z with (S + r - 8)%Z in RD by lia.
    zstep. zstep. zstep. zstep.
    u8_store UA (D + r - 8 - U)%Z 8%nat.
    zstep. zstep.
    if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (IH (r - 8)%Z); [mm_close | lia | lia]]. num_st_eq.
    - zstep. eapply evt_eq; [| eapply (mm_150 (r - 8)%Z); [mm_close | lia]]. num_st_eq.
  Qed.

  Lemma mm_208 : forall (r : Z) xa3 xa4 xa5 xa6 xa7 mm,
    MMINV mm -> (0 <= r <= N)%Z ->
    evt usegs POST (MM 0xd0394 (Z_to_bv 64 S) (Z_to_bv 64 r) xa3 xa4 xa5 xa6 xa7 mm).
  Proof using HUS HSD HDN HN.
    intros until mm. intros INV Hr.
    zstep. zstep.
    if_cases K; zify_cond K.
    - zstep. eapply mm_150; [exact INV | lia].
    - zstep. zstep. zstep.
      eapply evt_eq; [| eapply (mm_WL (Z.to_nat r) r); [exact INV | lia | lia]]. num_st_eq.
  Qed.

  Lemma mm_AL : forall (f : nat) (r : Z) xa6 xa7 mm,
    MMINV mm -> (0 <= r <= N)%Z -> (r <= Z.of_nat f)%Z ->
    evt usegs POST (MM 0xd036c (Z_to_bv 64 S) (Z_to_bv 64 (D + r - 1)) (Z_to_bv 64 (- r)) (Z_to_bv 64 (S + r - 1)) (Z_to_bv 64 (D + r - 1)) xa6 xa7 mm).
  Proof using HUS HSD HDN HN.
    intros f. induction f as [|f IH]; intros r xa6 xa7 mm INV Hr Hf.
    - zstep. if_cases K; zify_cond K; [eapply mm_ret; exact INV|].
      exfalso. apply K. apply neg_mod64_zero; lia.
    - zstep.
      if_cases K; zify_cond K; [eapply mm_ret; exact INV|].
      assert (R1 : (1 <= r)%Z).
      { destruct (Z.eq_dec r 0) as [->|]; [exfalso; apply K; reflexivity | lia]. }
      mm_open INV.
      destruct (u8arr_read1 usegs mm U bs (S + r - 1 - U) UA ltac:(lia)) as [b RD].
      replace (U + (S + r - 1 - U))%Z with (S + r - 1)%Z in RD by lia.
      zstep.
      u8_store UA (D + r - 1 - U)%Z 1%nat.
      zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K2.
      + eapply evt_eq; [| eapply (IH (r - 1)%Z); [mm_close | lia | lia]]. num_st_eq.
      + zstep. eapply evt_eq; [| eapply (mm_208 (r - 1)%Z); [mm_close | lia]]. num_st_eq.
  Qed.

  Lemma mm_body : forall a3 a4 a5 a6 a7 bs,
    u8arr usegs m0 U bs -> length bs = L -> mem_inv usegs m0 ->
    evt usegs POST (MM MEMMOVE_ENTRY (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 m0).
  Proof using HMEMCPY HUS HSD HDN HN HAL.
    intros a3 a4 a5 a6 a7 bs UA UL MI. unfold MEMMOVE_ENTRY.
    pose proof (u8arr_bound _ _ _ _ UA) as UB. rewrite UL in UB.
    pose proof (munch_refl [(D, D + N)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    assert (INV : MMINV m0) by (split; [eexists; split; eassumption|]; split; [assumption|]; split; assumption).
    zstep.
    if_cases K0; zify_cond K0; [eapply mm_ret; exact INV|].
    zstep. zstep. zstep. zstep. zstep.
    if_cases K1; zify_cond K1.
    -
      pose proof (memmove_overlap_test_w S D N ltac:(lia) ltac:(lia) ltac:(lia) K1) as SEP.
      zstep.
      pose proof (bytes_at_sub usegs m0 U bs (Z.to_nat (S - U)) (Z.to_nat N) (proj1 UA) ltac:(lia)) as SRC.
      replace (U + Z.of_nat (Z.to_nat (S - U)))%Z with S in SRC by lia.
      destruct (u8arr_range_split usegs m0 U bs (Z.to_nat (D - U)) (Z.to_nat (D - U + N)) UA ltac:(lia) ltac:(lia))
        as (b1 & mid & b3 & L1 & LMID & L3 & U1 & MID & U3).
      replace (U + Z.of_nat (Z.to_nat (D - U)))%Z with D in MID by lia.
      replace (Z.to_nat (D - U + N) - Z.to_nat (D - U))%nat with (Z.to_nat N) in MID by lia.
      pose proof HMEMCPY as HM. unfold memcpyZ_stmt_g in HM.
      eapply evt_mono.
      { eapply HM with (Dst := D) (Src := S) (N := N) (src := firstn (Z.to_nat N) (skipn (Z.to_nat (S - U)) bs)) (junk := mid);
          [exact SRC | rewrite length_firstn, length_skipn; lia | exact MID | lia | lia | lia | lia | exact MI]. }
      cbv beta. intros ms' P. unfold memcpyZ_post_g in P.
      destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc & MIc & DSTc & SRCc).
      clear SRC SRCc UA MID.
      transport_after_call usegs m0 m3 MUc WMc.
      replace D with (U + Z.of_nat (length b1))%Z in DSTc at 1 by lia.
      replace (U + Z.of_nat (Z.to_nat (D - U + N)))%Z with (U + Z.of_nat (length b1) + Z.of_nat (Z.to_nat N))%Z in U3 by lia.
      destruct (u8arr_range_join usegs m3 U b1 _ _ b3 U1 DSTc U3) as (bs' & LB' & UA').
      unfold memmove_post_g. do 14 eexists. exists m3, bs'.
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact UA'| lia].
    - zstep. zstep. zstep.
      if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep.
      if_cases K3; zify_cond K3.
      2:{ exfalso. apply K3. apply xor_low3_zero; lia. }
      zstep. zstep. zstep.
      if_cases K4.
      + eapply evt_eq; [| eapply (mm_208 N); [exact INV | lia]]. num_st_eq.
      + zstep. zstep. zstep. zstep. zstep.
        eapply evt_eq; [| eapply (mm_AL (Z.to_nat N) N); [exact INV | lia | lia]]. num_st_eq.
  Qed.
End MEMMOVE.

Theorem memmove_spec : memcpyZ_stmt_g usegs MM_MEMCPY -> memmove_stmt_g usegs MEMMOVE_ENTRY.
Proof.
  intros HCPY. unfold memmove_stmt_g. intros until bs. intros UA HUS HSD HDN HN HAL MI.
  eapply mm_body; try eassumption. reflexivity.
Qed.
