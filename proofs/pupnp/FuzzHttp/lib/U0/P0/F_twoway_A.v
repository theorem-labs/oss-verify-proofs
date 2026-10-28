(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memchr F_syscalls.
Import ListNotations.
Open Scope bv_scope.

Definition twoway_entry := 0x24dcc%Z.
Definition NAD := 0x103d2%Z.
Definition NAD1 := 0x103d3%Z.

Definition chunked_bytes : list byte :=
  [Z_to_bv 8 99; Z_to_bv 8 104; Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107; Z_to_bv 8 101; Z_to_bv 8 100; Z_to_bv 8 0].
Definition BSW1 := 9087704121737216%Z.
Definition M1 := 18446744073709551615%Z.

Notation w z := (Z_to_bv 64 z) (only parsing).

Definition LOCELLS (j0 j1 j2 j3 j4 j5 j6 : list byte) : list cell :=
  [CB 16 j0; C8 (w 0); C8 (w ssp_guard); C8 (w M1); C8 (w NAD1);
   CB 792 j1; C8 (w 1)  ; C8 (w 7)  ; C8 (w 6)  ; CB 16 j2; C8 (w 2)  ; CB 16 j3;
   C8 (w 5)  ; CB 16 j4; C8 (w 4)  ; CB 48 j5; C8 (w 3)  ; CB 1104 j6;
   C8 (w 0); C8 (w BSW1); C8 (w 0); C8 (w 0)].

Definition HICELLS (canary s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 canary; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition twoway_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (H : Z) (hay slack : list byte) (canary : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (w r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' H (hay ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells rsegs m' got_ssp [C8 (w ssp_guard)]
    /\ rw_cells rsegs m' ssp_guard [C8 canary]
    /\ (r = 0 \/ H <= r <= H + Z.of_nat (length hay))%Z.

Lemma bs_off : forall b, (0 <= b < 256)%Z -> Z.land (Z.shiftr b 3) 24 = (8 * (b / 64))%Z.
Proof.
  intros b Hb.
  pose proof (brute256_ok (fun b => Z.land (Z.shiftr b 3) 24 =? 8 * (b / 64))%Z ltac:(vm_compute; reflexivity) b Hb) as E.
  apply Z.eqb_eq. exact E.
Qed.

Definition in_chunked (b : Z) : bool :=
  ((b =? 99) || (b =? 100) || (b =? 101) || (b =? 104) || (b =? 107) || (b =? 110) || (b =? 117))%Z.

Lemma bsw1_bit : forall b, (0 <= b < 256)%Z -> (b / 64 = 1)%Z ->
  (Z.land (Z.shiftr BSW1 (b mod 64)) 1 =? 0)%Z = negb (in_chunked b).
Proof.
  intros b Hb Hq.
  pose proof (brute256_ok (fun b => implb (b / 64 =? 1) (Bool.eqb (Z.land (Z.shiftr BSW1 (b mod 64)) 1 =? 0) (negb (in_chunked b))))%Z
                ltac:(vm_compute; reflexivity) b Hb) as E.
  cbn beta in E. rewrite (proj2 (Z.eqb_eq _ _) Hq) in E. cbn [implb] in E. apply Bool.eqb_prop in E. exact E.
Qed.

Lemma in_chunked_cases : forall b, in_chunked b = true ->
  (b = 99 \/ b = 100 \/ b = 101 \/ b = 104 \/ b = 107 \/ b = 110 \/ b = 117)%Z.
Proof. intros b Hb. unfold in_chunked in Hb. rewrite !Bool.orb_true_iff, !Z.eqb_eq in Hb. LiaTuning.ctauto. Qed.

Lemma chunked_nz : forall k b, (k < 7)%nat -> nth_error chunked_bytes k = Some b -> (0 < bv_unsigned b < 256)%Z.
Proof.
  intros k b Hk Hb.
  do 7 (destruct k as [|k]; [cbn in Hb; injection Hb as <-; rewrite Z_to_bv_unsigned, bv_wrap8_mod; cbn; lia|]). lia.
Qed.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : Z) (hay slack : list byte) (canary : word) (lo : Z).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) hay.
  Hypothesis PAD : ((- (H + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis BND : (0 <= H /\ H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= lo /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis SEPH : (H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= H)%Z.
  Hypothesis SEPG : (got_ssp + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis SEPC : (ssp_guard + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis SEPN : (NAD + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis HPOS : (0 < H)%Z.

  Notation len := (Z.of_nat (length hay)).
  Notation full := (hay ++ Z_to_bv 8 0 :: slack).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z.
  Notation POST := (twoway_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H hay slack canary lo m).

  Definition INVc (m1 : word -> option byte) : Prop :=
    bytes_at rsegs m1 H full /\ bytes_at rsegs m1 NAD chunked_bytes /\ mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1
    /\ stk rsegs m1 lo (SP - 2240)
    /\ rw_cells rsegs m1 got_ssp [C8 (w ssp_guard)] /\ rw_cells rsegs m1 ssp_guard [C8 canary]
    /\ rw_cells rsegs m1 (SP + -112) (HICELLS canary s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
  Definition INV (m1 : word -> option byte) : Prop :=
    INVc m1 /\ exists j0 j1 j2 j3 j4 j5 j6, rw_cells rsegs m1 (SP + -2240) (LOCELLS j0 j1 j2 j3 j4 j5 j6).
  Ltac open_invc Hc := destruct Hc as (HAY & NEE & MI & MU & WM & STK & GOT & GUARD & FRhi); unfold HICELLS in FRhi.
  Ltac open_inv Hi := let Hc := fresh in destruct Hi as [Hc (j0 & j1 & j2 & j3 & j4 & j5 & j6 & FRlo)]; unfold LOCELLS in FRlo; open_invc Hc.

  #[using="H"] Lemma full_length : length full = (length hay + S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  #[using="H NONUL"] Lemma hay_nth : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error hay (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error hay (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. } split; [reflexivity|].
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.
  #[using="H"] Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.
  #[using="H hay slack"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as B. unfold bv_modulus in B. cbn in B. cbn. lia. Qed.

  #[using="LO BND"] Lemma tw_epi : forall m1 (cs : list cell) (r : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x8 x9 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    INVc m1 -> rw_cells rsegs m1 (SP + -2240) cs -> cells_size cs = 2128%nat ->
    (r = 0 \/ H <= r <= H + len)%Z ->
    evt rsegs POST (MS (mkR x1 (w (SP + -2240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (w r) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (w 0x25104) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros Ic FRlo CS Hr; open_invc Ic. pose proof BND as BD.
    do 17 zstep.
    release_frame FRlo STK (bv_unsigned sp - 112)%Z. release_frame FRhi STK (bv_unsigned sp).
    finish.
  Qed.

  Definition LR (x1 : word) (z : Z) (xs4 : word) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 : word) (xs11 : word) (x28 x29 x30 x31 : word) :=
    mkR x1 (w (SP + -2240)) gp tp x5 x6 x7 (w NAD) (w z) x10 x11 x12 x13 x14 x15 x16 x17
        (w 2) (w 63) xs4 (w (SP + -144)) (w NAD1) (w 7) (w 1) (w 6) (w (SP + -2192)) xs11 x28 x29 x30 x31.

  #[using="LO BND"] Lemma tw_found : forall m1 z h x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31,
    INV m1 -> (H <= h <= H + len)%Z ->
    evt rsegs POST (MS (LR x1 z (w h) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31) F (w 0x250ec) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros I Hh; open_inv I. pose proof BND as BD. unfold LR.
    unfold got_ssp, ssp_guard in *.
    do 6 zstep. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
    eapply tw_epi; [ | exact FRlo | reflexivity | right; exact Hh ].
    repeat (split; [assumption|]); exact FRhi.
  Qed.

  #[using="LO BND"] Lemma tw_ret0 : forall m1 z h x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31,
    INV m1 ->
    evt rsegs POST (MS (LR x1 z (w h) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31) F (w 0x251bc) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros I; open_inv I. pose proof BND as BD. unfold LR.
    unfold got_ssp, ssp_guard in *.
    do 7 zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    eapply tw_epi; [ | exact FRlo | reflexivity | left; reflexivity ].
    repeat (split; [assumption|]); exact FRhi.
  Qed.

  Definition CONT (m1 : word -> option byte) (z h : Z) : Prop :=
    forall h', (h < h' <= h + 7)%Z -> forall hold x1 x5 x6 x7 (xa0 : word) x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31,
      xa0 = w h' ->
      evt rsegs POST (MS (LR x1 z hold x5 x6 x7 xa0 (w 0) x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31) F (w 0x24fe4) fc None m1 (seg_rom rsegs)).

  #[using="NONUL"] Lemma hay_read : forall m1 i a, bytes_at rsegs m1 H full -> (0 <= i < len)%Z -> a = w (H + i) ->
    exists b, ov_read_bytes rsegs m1 a 1 = Some [b] /\ nth_error hay (Z.to_nat i) = Some b /\ (0 < bv_unsigned b < 256)%Z.
  Proof.
    intros m1 i a HAY Hi Ha. destruct (hay_nth i Hi) as (b & Hb & Hs & NZ). pose proof (byte_range b).
    exists b. split; [|split; [exact Hs|lia]]. eapply u8ro_read; eauto. lia.
  Qed.
  #[using="H hay slack"] Lemma nee_read : forall m1 (k : nat) b a, bytes_at rsegs m1 NAD chunked_bytes -> nth_error chunked_bytes k = Some b -> a = w (NAD + Z.of_nat k) ->
    ov_read_bytes rsegs m1 a 1 = Some [b].
  Proof. intros m1 k b a NEE Hk Ha. eapply (u8ro_read rsegs m1 NAD chunked_bytes (Z.of_nat k)); eauto; [|lia]. rewrite Nat2Z.id. exact Hk. Qed.

  #[using="NONUL LO BND"] Lemma tw_lh : forall m1 z h x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INV m1 -> CONT m1 z h -> (H <= h)%Z -> (h + 7 <= z <= H + len)%Z ->
    evt rsegs POST (MS (LR x1 z (w h) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (w 0) x28 x29 x30 x31) F (w 0x250a0) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros I CO Hh Hz; pose proof I as I'; open_inv I. pose proof BND as BD. unfold LR. unfold NAD, NAD1, ssp_guard, M1, BSW1 in *.
    destruct (hay_read m1 (h - H + 1) (w (h + 1)) HAY ltac:(lia) ltac:(f_equal; lia)) as (b1 & RD1 & Hs1 & R1).
    destruct (hay_read m1 (h - H) (w h) HAY ltac:(lia) ltac:(f_equal; lia)) as (b0 & RD0 & Hs0 & R0).
    pose proof (nee_read m1 1 _ (w (66514 + 1)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN1.
    pose proof (nee_read m1 0 _ (w 66514) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN0.
    do 4 zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
    do 6 zstep. if_cases K1; zify_cond K1.
    -
      zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
      do 6 zstep. if_cases K3; zify_cond K3.
      +
        zstep. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
        apply tw_found; [exact I'|lia].
      + do 3 zstep. eapply (CO (h + 6)%Z); [lia|word_eq_tac].
    - do 3 zstep. eapply (CO (h + 6)%Z); [lia|word_eq_tac].
  Qed.

  #[using="NONUL LO BND"] Lemma tw_rh : forall (j : nat) (k : nat) nk m1 z h x1 x5 x6 x7 (xa0 xa1 xa2 xa3 : word) x14 x15 x16 x17 x28 x29 x30 x31,
    INV m1 -> CONT m1 z h -> (H <= h)%Z -> (h + 7 <= z <= H + len)%Z ->
    (6 - k = j)%nat -> (2 <= k <= 6)%nat -> nth_error chunked_bytes k = Some nk ->
    xa0 = w (h + Z.of_nat k - 1) -> xa1 = w (bv_unsigned nk) -> xa2 = w (h + Z.of_nat k) -> xa3 = w (NAD + Z.of_nat k + 1) ->
    evt rsegs POST (MS (LR x1 z (w h) x5 x6 x7 xa0 xa1 xa2 xa3 x14 x15 x16 x17 (w 0) x28 x29 x30 x31)
                       F (w 0x25084) fc None m1 (seg_rom rsegs)).
  Proof.
    induction j as [|j IH]; intros until x31; intros I CO Hh Hz Hj Hk Hnk -> -> -> ->; pose proof I as I'; open_inv I; pose proof BND as BD;
      unfold LR; unfold NAD, NAD1, ssp_guard, M1, BSW1 in *.
    -
      assert (k = 6%nat) by lia. subst k. cbn in Hnk. injection Hnk as <-.
      destruct (hay_read m1 (h - H + 6) (w (h + 6)) HAY ltac:(lia) ltac:(f_equal; lia)) as (b & RD & Hs & R).
      pose proof (nee_read m1 7 _ (w (66514 + 6 + 1)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN.
      zstep. zstep. if_cases K1; zify_cond K1.
      +   do 2 zstep. eapply (CO (h + 5)%Z); [lia|word_eq_tac].
      + do 5 zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
        apply tw_lh; auto.
    - pose proof (nth_error_lt _ _ _ Hnk) as LK. cbn [length chunked_bytes] in LK.
      destruct (nth_error chunked_bytes (S k)) as [nk1|] eqn:Hnk1. 2:{ apply nth_error_None in Hnk1. cbn in Hnk1. lia. }
      pose proof (chunked_nz (S k) nk1 ltac:(lia) Hnk1) as NZ1.
      destruct (hay_read m1 (h - H + Z.of_nat k) (w (h + Z.of_nat k)) HAY ltac:(lia) ltac:(f_equal; lia)) as (b & RD & Hs & R).
      pose proof (nee_read m1 (S k) _ (w (66514 + Z.of_nat k + 1)) NEE Hnk1 ltac:(unfold NAD; f_equal; lia)) as RN.
      pose proof (byte_range nk).
      zstep. zstep. if_cases K1; zify_cond K1.
      + do 2 zstep. eapply (CO (h + Z.of_nat k - 1)%Z); [lia|word_eq_tac].
      + do 5 zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
        eapply (IH (S k)); eauto; try lia; word_eq_tac.
  Qed.

  #[using="NONUL LO BND"] Lemma tw_b2 : forall m1 z h x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INV m1 -> CONT m1 z h -> (H <= h)%Z -> (h + 7 <= z <= H + len)%Z ->
    evt rsegs POST (MS (LR x1 z (w h) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (w 0) x28 x29 x30 x31) F (w 0x25024) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros I CO Hh Hz; pose proof I as I'; open_inv I. pose proof BND as BD. unfold LR. unfold NAD, NAD1, ssp_guard, M1, BSW1 in *.
    destruct (hay_read m1 (h - H + 6) (w (h + 6)) HAY ltac:(lia) ltac:(f_equal; lia)) as (b6 & RD6 & Hs6 & R6).
    do 5 zstep.
    assert (Hq : (bv_unsigned b6 / 64 = 1 \/ (bv_unsigned b6 / 64 = 0 \/ bv_unsigned b6 / 64 = 2 \/ bv_unsigned b6 / 64 = 3))%Z) by lia.
    destruct Hq as [Hq|Hq].
    2:{
        destruct Hq as [Hq|[Hq|Hq]];
        [ replace (Z.land (Z.shiftr (bv_unsigned b6) 3) 24) with 0%Z by (rewrite bs_off by lia; rewrite Hq; reflexivity)
        | replace (Z.land (Z.shiftr (bv_unsigned b6) 3) 24) with 16%Z by (rewrite bs_off by lia; rewrite Hq; reflexivity)
        | replace (Z.land (Z.shiftr (bv_unsigned b6) 3) 24) with 24%Z by (rewrite bs_off by lia; rewrite Hq; reflexivity) ];
        do 5 zstep; rewrite Z.shiftr_0_l; cbn [Z.land]; if_true; (eapply (CO (h + 7)%Z); [lia|word_eq_tac]). }
    replace (Z.land (Z.shiftr (bv_unsigned b6) 3) 24) with 8%Z by (rewrite bs_off by lia; rewrite Hq; reflexivity).
    do 5 zstep. if_cases K; [zify_cond K|].
    {   eapply (CO (h + 7)%Z); [lia|word_eq_tac]. }

    assert (IC : in_chunked (bv_unsigned b6) = true).
    { pose proof (bsw1_bit (bv_unsigned b6) ltac:(lia) Hq) as E. unfold BSW1 in E.
      destruct (in_chunked (bv_unsigned b6)); [reflexivity|]. exfalso.
      cbn [negb] in E. apply Z.eqb_eq in E. revert K E. clear. intros K E.

      zify_cond K. apply K. exact E. }
    clear K.
    destruct (in_chunked_cases _ IC) as [E|[E|[E|[E|[E|[E|E]]]]]]; rewrite E in *.
    all: do 4 zstep.
    2:{   if_cases K; zify_cond K. { exfalso; lia. }
        pose proof (nee_read m1 2 _ (w (66514 + 2)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN2.
        do 2 zstep. if_cases K1; zify_cond K1. 2:{ exfalso; lia. }
        do 3 zstep. if_cases K2; zify_cond K2. { exfalso; lia. }
        do 4 zstep.
        eapply (tw_rh 4 2); eauto; try lia; try reflexivity; try word_eq_tac.
        all: rewrite Z_to_bv_unsigned, bv_wrap8_mod; reflexivity. }
    all: if_cases K; zify_cond K; [|exfalso; lia].
    all: do 2 zstep; if_cases K1; zify_cond K1; [|exfalso; lia].

    - do 2 zstep; eapply (CO (h + 6)%Z); [lia|word_eq_tac].
    - do 2 zstep; eapply (CO (h + 1)%Z); [lia|word_eq_tac].
    - do 2 zstep; eapply (CO (h + 5)%Z); [lia|word_eq_tac].
    - do 2 zstep; eapply (CO (h + 2)%Z); [lia|word_eq_tac].
    - do 2 zstep; eapply (CO (h + 3)%Z); [lia|word_eq_tac].
    - do 2 zstep; eapply (CO (h + 4)%Z); [lia|word_eq_tac].
  Qed.

  #[using="NONUL PAD"] Lemma memchr_pre : forall m1 z, bytes_at rsegs m1 H full -> (H <= z <= H + len)%Z ->
    let buf := skipn (Z.to_nat (z - H)) full in
    bytes_at rsegs m1 z buf /\ memchr_ok z 0 63 buf /\
    ((exists j, find_byte 0 (firstn (Z.to_nat 63) buf) = Some j /\ (z + Z.of_nat j = H + len)%Z)
     \/ (find_byte 0 (firstn (Z.to_nat 63) buf) = None /\ (z + 63 <= H + len)%Z)).
  Proof.
    intros m1 z HAY Hz buf.
    pose proof HAY as HAY2. rewrite <- (firstn_skipn (Z.to_nat (z - H)) full) in HAY2.
    apply bytes_at_app in HAY2. destruct HAY2 as [_ BUF]. rewrite firstn_length_le in BUF by (rewrite full_length; lia).
    replace (H + Z.of_nat (Z.to_nat (z - H)))%Z with z in BUF by lia. fold buf in BUF.
    assert (LB : length buf = (length hay + S (length slack) - Z.to_nat (z - H))%nat).
    { subst buf. rewrite skipn_length, full_length. reflexivity. }
    assert (NB : forall j b, nth_error buf j = Some b -> (Z.to_nat (z - H) + j < length hay)%nat -> bv_unsigned b <> 0%Z).
    { intros j b Hn Hj. subst buf. rewrite nth_error_skipn in Hn.
      destruct (hay_nth (Z.of_nat (Z.to_nat (z - H) + j)) ltac:(lia)) as (b' & Hb' & _ & NZ). rewrite Nat2Z.id in Hb'.
      rewrite Hb' in Hn. injection Hn as <-. exact NZ. }
    assert (ZB : nth_error buf (length hay - Z.to_nat (z - H))%nat = Some (Z_to_bv 8 0)).
    { subst buf. rewrite nth_error_skipn. rewrite <- full_nth_len. f_equal. lia. }
    split; [exact BUF|].
    destruct (find_byte 0 (firstn (Z.to_nat 63) buf)) as [j|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hj & (b & Hn & Hb) & Hmin). rewrite firstn_length in Hj.
      rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat 63)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
      assert (E : (Z.to_nat (z - H) + j = length hay)%nat).
      { destruct (Nat.lt_trichotomy (Z.to_nat (z - H) + j) (length hay)) as [LT|[EQ|GT]]; [|exact EQ|].
        - exfalso. exact (NB _ _ Hn LT Hb).
        - exfalso. refine (Hmin (length hay - Z.to_nat (z - H))%nat (Z_to_bv 8 0) ltac:(lia) _ eq_refl).
          rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact ZB. }
      split.
      + unfold memchr_ok. rewrite FB. right. rewrite LB.
        replace (z + Z.of_nat j + 1)%Z with (H + len + 1)%Z by lia. pose proof PAD. lia.
      + left. exists j. split; [reflexivity|lia].
    - assert (GE : (63 <= length hay - Z.to_nat (z - H))%nat).
      { destruct (Nat.lt_ge_cases (length hay - Z.to_nat (z - H)) 63) as [LT|GE]; [|exact GE]. exfalso.
        refine (find_byte_None _ _ FB (length hay - Z.to_nat (z - H))%nat (Z_to_bv 8 0) _ eq_refl).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact ZB. }
      split.
      + unfold memchr_ok. rewrite FB. rewrite LB. lia.
      + right. split; [reflexivity|lia].
  Qed.

  #[using="NONUL PAD LO BND SEPH SEPC HPOS"] Lemma tw_loop : forall (fuel : nat) m1 z hold h x1 x5 x6 x7 (xa0 : word) x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31,
    INV m1 -> (H <= h <= z)%Z -> (z <= H + len)%Z -> (Z.to_nat (H + len - h) < fuel)%nat -> xa0 = w h ->
    evt rsegs POST (MS (LR x1 z hold x5 x6 x7 xa0 (w 0) x12 x13 x14 x15 x16 x17 mem x28 x29 x30 x31) F (w 0x24fe4) fc None m1 (seg_rom rsegs)).
  Proof.
    induction fuel as [|fuel IH]; [lia|].
    intros until x31. intros I Hh Hz Hf ->.
    assert (CO' : forall m' z', INV m' -> (h + 7 <= z' <= H + len)%Z -> CONT m' z' h).
    { intros m' z' I2 Hz'. unfold CONT. intros h' Hh'. intros. subst. eapply IH; eauto; lia. }
    pose proof I as I'; open_inv I. pose proof BND as BD. unfold LR. unfold NAD, NAD1, ssp_guard, M1, BSW1 in *.
    do 4 zstep. if_cases K0; zify_cond K0.
    -   apply tw_b2; [exact I' | apply CO'; [exact I'|] | |]; rewrite ?Z.mod_small in K0 by lia; lia.
    - destruct (memchr_pre m1 z HAY ltac:(lia)) as (BUF & OK & CASES).
      do 4 zstep. call memchr_spec.
      1:{ rewrite unsigned_lit by lia. exact BUF. }
      1:{ rewrite !unsigned_lit by lia. exact OK. }
      1:{ exact MI. }
      rewrite !unsigned_lit in * by lia. change (0 mod 256)%Z with 0%Z. unfold memchr_res.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (I2 : INV mm); [ split; [ repeat (split; [eassumption|]); eassumption | do 7 eexists; eassumption ] | ] end.
      destruct CASES as [(j & FB & Hj)|(FB & Hz63)]; rewrite FB.
      + zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear -Hj BD HPOS Hz Hh. intros K1. Z.div_mod_to_equations; lia. }
        zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. clear -Hj BD HPOS Hz Hh. intros K2. Z.div_mod_to_equations; lia. }
        zstep. zstep. if_cases K3; zify_cond K3.
        *   apply tw_ret0. exact I2.
        * apply tw_b2; [exact I2 | apply CO'; [exact I2|] | |]; rewrite ?Z.mod_small in K3 by lia; lia.
      + zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
        zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
        apply tw_b2; [exact I2 | apply CO'; [exact I2|] | |]; rewrite ?Z.mod_small in K0 by lia; lia.
  Qed.
End Loop.
