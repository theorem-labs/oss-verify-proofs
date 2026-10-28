(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma limbz_app_mid : forall (b1 src b3 : list byte) k, (0 <= k)%Z -> (k + 8 <= Z.of_nat (length src))%Z ->
  limbz (b1 ++ src ++ b3) (Z.of_nat (length b1) + k) = limbz src k.
Proof.
  intros b1 src b3 k Hk Hl. unfold limbz. f_equal.
  replace (Z.to_nat (Z.of_nat (length b1) + k)) with (length b1 + Z.to_nat k)%nat by lia.
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  replace (length b1 + Z.to_nat k - length b1)%nat with (Z.to_nat k) by lia.
  rewrite skipn_app. rewrite firstn_app. rewrite length_skipn.
  replace (8 - (length src - Z.to_nat k))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma limbz_slice : forall (bs : list byte) (j n : nat) k, (0 <= k)%Z -> (k + 8 <= Z.of_nat n)%Z -> (j + n <= length bs)%nat ->
  limbz (firstn n (skipn j bs)) k = limbz bs (Z.of_nat j + k).
Proof.
  intros bs j n k Hk Hl Hb. unfold limbz. f_equal.
  replace (Z.to_nat (Z.of_nat j + k)) with (j + Z.to_nat k)%nat by lia.
  rewrite skipn_firstn_comm. rewrite firstn_firstn. replace (Nat.min 8 (n - Z.to_nat k)) with 8%nat by lia.
  rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma u8arr_range_join_s : forall segs (m : mem) A b1 (k : nat) mid b3,
  u8arr segs m A b1 -> rw_cells segs m (A + Z.of_nat (length b1)) [CB k mid] ->
  u8arr segs m (A + Z.of_nat (length b1) + Z.of_nat k) b3 ->
  length mid = k /\ u8arr segs m A (b1 ++ mid ++ b3).
Proof.
  intros segs m A b1 k mid b3 [B1 W1] H2 [B3 W3].
  pose proof (u8arr_of_rw_cells segs m _ k mid H2) as [B2 W2].
  destruct H2 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [L2 _].
  split; [exact L2|]. split.
  - apply bytes_at_app. split; [exact B1|]. apply bytes_at_app. split; [exact B2|]. rewrite L2. exact B3.
  - rewrite !length_app, L2.
    replace (Z.of_nat (length b1 + (k + length b3))) with (Z.of_nat (length b1) + (Z.of_nat k + Z.of_nat (length b3)))%Z by lia.
    apply wr_at_join; [exact W1| | lia | lia]. rewrite L2 in W2. apply wr_at_join; [exact W2| exact W3 | lia | lia].
Qed.

Definition memmoveN_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S N U : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m' bs',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m' /\ u8arr segs m' U bs' /\ length bs' = length bs
    /\ ((8 <= N)%Z -> limbz bs' (D - U + N - 8) = limbz bs (S - U + N - 8)).
Definition memmoveN_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D S N U : Z) (bs : list byte),
  u8arr segs m U bs -> (U <= S)%Z -> (S < D < 2^64)%Z -> (D + N <= U + Z.of_nat (length bs))%Z -> (0 <= N < 2^62)%Z ->
  ((D - S) mod 8 = 0)%Z -> (D mod 8 = 0)%Z -> (N mod 8 = 0)%Z -> mem_inv segs m ->
  evt segs (memmoveN_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N U bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition MEMMOVEN_ENTRY : Z := 0xd0aec.
Definition MMN_MEMCPY : Z := 0xd06e8.

Section MEMMOVEN.
  Hypothesis HMEMCPY : memcpyZ_stmt_g usegs MMN_MEMCPY.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D S N U : Z) (bs0 : list byte) (m0 : mem).
  Hypothesis HUS : (U <= S)%Z.
  Hypothesis HSD : (S < D < 2^64)%Z.
  Hypothesis HDN : (D + N <= U + Z.of_nat (length bs0))%Z.
  Hypothesis HN : (0 <= N < 2^62)%Z.
  Hypothesis HAL : ((D - S) mod 8 = 0)%Z.
  Hypothesis HD8 : (D mod 8 = 0)%Z.
  Hypothesis HN8 : (N mod 8 = 0)%Z.

  Notation POST := (memmoveN_post_g usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N U bs0 m0).
  Notation MM pc xa1 xa2 xa3 xa4 xa5 xa6 xa7 mm :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation W0 := (limbz bs0 (S - U + N - 8)).

  Definition MMINV (mm : mem) (r : Z) : Prop :=
    (exists bs, u8arr usegs mm U bs /\ length bs = length bs0 /\
                ((8 <= N)%Z -> (r = N -> limbz bs (S - U + N - 8) = W0) /\ (r < N -> limbz bs (D - U + N - 8) = W0)%Z)) /\
    mem_inv usegs mm /\ munch [(D, D + N)]%Z m0 mm /\ wmono usegs m0 mm.

  Ltac mm_open H := let bs := fresh "bs" in destruct H as ((bs & UA & UL & TOP) & MI & MU & WM);
    pose proof (u8arr_bound _ _ _ _ UA) as UB; rewrite UL in UB.

  Lemma mm_ret : forall xa1 xa2 xa3 xa4 xa5 xa6 xa7 mm r, MMINV mm r -> (r < N \/ N < 8)%Z -> evt usegs POST (MM 0xd0b78 xa1 xa2 xa3 xa4 xa5 xa6 xa7 mm).
  Proof using HUS HSD HDN HN HAL HD8 HN8.
    intros until r. intros INV Hr. mm_open INV.
    zstep.
    apply evt_done. unfold memmoveN_post_g. do 14 eexists. exists mm, bs.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA|]. split; [exact UL|].
    intros H8. destruct (TOP H8) as [_ T]. apply T. lia.
  Qed.

  Lemma mm_150 : forall xa2 xa4 xa5 xa6 xa7 mm,
    MMINV mm 0 -> evt usegs POST (MM 0xd0b4c (Z_to_bv 64 S) xa2 (Z_to_bv 64 0) xa4 xa5 xa6 xa7 mm).
  Proof using HUS HSD HDN HN HAL HD8 HN8.
    intros until mm. intros INV.
    zstep.
    if_cases K; zify_cond K; [|exfalso; lia].
    eapply mm_ret; [exact INV | lia].
  Qed.

  Lemma mm_WL : forall (f : nat) (r : Z) xa3 xa7 mm,
    MMINV mm r -> (8 <= r <= N)%Z -> (r mod 8 = 0)%Z -> (r <= Z.of_nat f)%Z ->
    evt usegs POST (MM 0xd0c18 (Z_to_bv 64 S) (Z_to_bv 64 r) xa3 (Z_to_bv 64 (S + -8)) (Z_to_bv 64 (D + -8)) (Z_to_bv 64 7) xa7 mm).
  Proof using HUS HSD HDN HN HAL HD8 HN8.
    intros f. induction f as [|f IH]; intros r xa3 xa7 mm INV Hr Hr8 Hf; [exfalso; lia|].
    mm_open INV.
    pose proof (u8arr_read8_at usegs mm U bs (S + r - 8 - U) _ UA ltac:(lia) ltac:(lia) eq_refl) as RD.
    replace (U + (S + r - 8 - U))%Z with (S + r - 8)%Z in RD by lia.
    zstep. zstep. zstep. zstep.
    u8_store UA (D + r - 8 - U)%Z 8%nat.
    assert (INV1 : MMINV m (r - 8)).
    { split; [|split; [assumption|]; split; assumption].
      eexists. split; [eassumption|]. split; [rewrite upd_bytes_length by (rewrite length_le8; lia); exact UL|].
      intros H8. destruct (TOP H8) as [T1 T2]. split; [intros; exfalso; lia|]. intros _.
      destruct (Z.eq_dec r N) as [EN|NE].
      - replace (D - U + N - 8)%Z with (D + r - 8 - U)%Z by lia. rewrite limbz_upd_same by lia.
        rewrite <- (T1 EN). unfold limbz. f_equal. f_equal. f_equal. lia.
      - rewrite limbz_upd_other; [apply T2; lia | lia | lia | rewrite length_le8; lia | lia | rewrite length_le8; lia]. }
    zstep. zstep.
    if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (IH (r - 8)%Z); [exact INV1 | lia | Z.div_mod_to_equations; lia | lia]]. num_st_eq.
    - zstep. assert (r - 8 = 0)%Z by (Z.div_mod_to_equations; lia).
      eapply evt_eq; [| eapply mm_150]; [num_st_eq | replace 0%Z with (r - 8)%Z by lia; exact INV1].
  Qed.

  Lemma mm_208 : forall xa3 xa4 xa5 xa6 xa7 mm,
    MMINV mm N ->
    evt usegs POST (MM 0xd0c04 (Z_to_bv 64 S) (Z_to_bv 64 N) xa3 xa4 xa5 xa6 xa7 mm).
  Proof using HUS HSD HDN HN HAL HD8 HN8.
    intros until mm. intros INV.
    zstep. zstep.
    if_cases K; zify_cond K.
    - zstep. assert (N = 0)%Z by (Z.div_mod_to_equations; lia).
      mm_open INV.
      zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep. apply evt_done. unfold memmoveN_post_g. do 14 eexists. exists mm, bs.
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA|]. split; [exact UL|]. intros; exfalso; lia.
    - zstep. zstep. zstep.
      eapply evt_eq; [| eapply (mm_WL (Z.to_nat N) N); [exact INV | lia | exact HN8 | lia]]. num_st_eq.
  Qed.

  Lemma mm_body : forall a3 a4 a5 a6 a7,
    u8arr usegs m0 U bs0 -> mem_inv usegs m0 ->
    evt usegs POST (MM MEMMOVEN_ENTRY (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 m0).
  Proof using HMEMCPY HUS HSD HDN HN HAL HD8 HN8.
    intros a3 a4 a5 a6 a7 UA MI. unfold MEMMOVEN_ENTRY.
    pose proof (u8arr_bound _ _ _ _ UA) as UB.
    pose proof (munch_refl [(D, D + N)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    assert (INV : MMINV m0 N).
    { split; [|split; [assumption|]; split; assumption]. exists bs0. split; [exact UA|]. split; [reflexivity|].
      intros _. split; [intros _; reflexivity | intros; exfalso; lia]. }
    zstep.
    if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep.
    if_cases K1; zify_cond K1.
    -
      pose proof (memmove_overlap_test_w S D N ltac:(lia) ltac:(lia) ltac:(lia) K1) as SEP.
      zstep.
      pose proof (bytes_at_sub usegs m0 U bs0 (Z.to_nat (S - U)) (Z.to_nat N) (proj1 UA) ltac:(lia)) as SRC.
      replace (U + Z.of_nat (Z.to_nat (S - U)))%Z with S in SRC by lia.
      destruct (u8arr_range_split usegs m0 U bs0 (Z.to_nat (D - U)) (Z.to_nat (D - U + N)) UA ltac:(lia) ltac:(lia))
        as (b1 & mid & b3 & L1 & LMID & L3 & U1 & MID & U3).
      replace (U + Z.of_nat (Z.to_nat (D - U)))%Z with D in MID by lia.
      replace (Z.to_nat (D - U + N) - Z.to_nat (D - U))%nat with (Z.to_nat N) in MID by lia.
      pose proof HMEMCPY as HM. unfold memcpyZ_stmt_g in HM.
      eapply evt_mono.
      { eapply HM with (Dst := D) (Src := S) (N := N) (src := firstn (Z.to_nat N) (skipn (Z.to_nat (S - U)) bs0)) (junk := mid);
          [exact SRC | rewrite length_firstn, length_skipn; lia | exact MID | lia | lia | lia | lia | exact MI]. }
      cbv beta. intros ms' P. unfold memcpyZ_post_g in P.
      destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc & MIc & DSTc & SRCc).
      clear SRC SRCc UA MID.
      transport_after_call usegs m0 m3 MUc WMc.
      replace D with (U + Z.of_nat (length b1))%Z in DSTc at 1 by lia.
      replace (U + Z.of_nat (Z.to_nat (D - U + N)))%Z with (U + Z.of_nat (length b1) + Z.of_nat (Z.to_nat N))%Z in U3 by lia.
      destruct (u8arr_range_join_s usegs m3 U b1 _ _ b3 U1 DSTc U3) as (LS & UA').
      unfold memmoveN_post_g. do 14 eexists. exists m3. eexists.
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact UA'|].
      split; [rewrite !length_app; lia|].
      intros H8. replace (D - U + N - 8)%Z with (Z.of_nat (length b1) + (N - 8))%Z by lia.
      rewrite limbz_app_mid by lia. rewrite limbz_slice by lia. apply limbz_eq. lia.
    - zstep. zstep. zstep.
      if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep.
      if_cases K3; zify_cond K3.
      2:{ exfalso. apply K3. apply xor_low3_zero; lia. }
      zstep. zstep. zstep.
      if_cases K4; zify_cond K4.
      + eapply evt_eq; [| eapply mm_208; exact INV]. num_st_eq.
      + exfalso. apply K4. rewrite land_7. Z.div_mod_to_equations; lia.
  Qed.
End MEMMOVEN.

Theorem memmoveN_spec : memcpyZ_stmt_g usegs MMN_MEMCPY -> memmoveN_stmt_g usegs MEMMOVEN_ENTRY.
Proof.
  intros HCPY. unfold memmoveN_stmt_g. intros until bs. intros UA HUS HSD HDN HN HAL HD8 HN8 MI.
  eapply mm_body; eassumption.
Qed.
