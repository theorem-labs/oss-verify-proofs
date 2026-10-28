(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_strlen.
Import ListNotations.
Open Scope bv_scope.

Definition strchrnul_entry := 0x24794%Z.
Definition strchr_entry := 0x24758%Z.

Definition strchrnul_res (A : Z) (str : list byte) (c : Z) (r : Z) : Prop :=
  (A <= r <= A + Z.of_nat (length str))%Z /\
  (r = (A + Z.of_nat (length str))%Z \/ nth_error str (Z.to_nat (r - A)) = Some (Z_to_bv 8 c)).

Definition strchrnul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack)
    /\ strchrnul_res (bv_unsigned a0) str (bv_unsigned a1 mod 256) r.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo : Z).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 16)%Z.
  Hypothesis BND : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 2^64
                    /\ 0 <= lo /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis SEP : (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16
                    \/ bv_unsigned sp <= bv_unsigned a0)%Z.

  Notation A := (bv_unsigned a0).
  Notation c := (bv_unsigned a1 mod 256)%Z.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 16, bv_unsigned sp)]%Z.
  Notation POST := (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m).
  Notation CMAGIC := 72340172838076672%Z.
  Notation HIGHS := 9259542123273814144%Z.

  Notation ST pc m1 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at rsegs m1 A full /\ mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1
    /\ stk rsegs m1 lo (SP - 16)
    /\ rw_cells rsegs m1 (SP + -16) [C8 s0; C8 ra].
  Ltac open_inv H := destruct H as (STR & MI & MU & WM & STK & FR).

  #[using="a0"] Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  #[using="a0 str slack"] Lemma c_range : (0 <= c < 256)%Z.
  Proof. apply Z.mod_pos_bound. lia. Qed.

  #[using="a0 NONUL"] Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. } split; [reflexivity|].
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  #[using="a0"] Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  #[using="a0 str slack"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

  #[using="LO BND"] Lemma sn_ret : forall m1 (r : Z) x12 x13 x14 x15 x16 x17,
    INV m1 -> strchrnul_res A str c r ->
    evt rsegs POST (ST 0x24864 m1 (Z_to_bv 64 r) x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 r x12 x13 x14 x15 x16 x17 I Hr; open_inv I. pose proof BND as BD.
    do 4 zstep. release_frame FR STK (bv_unsigned sp). finish.
  Qed.

  #[using="NONUL LO BND"] Lemma sn_tail : forall (k : nat) (i : Z) m1 x12 x13 x14 x15 x16 x17,
    INV m1 -> (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evt rsegs POST (ST 0x24854 m1 (Z_to_bv 64 (A + i - 1)) x12 x13 x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i m1 x12 x13 x14 x15 x16 x17 I Hk Hi; pose proof I as I'; open_inv I; pose proof BND as BD;
      pose proof c_range as CR.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read rsegs m1 A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 3 zstep. if_true. replace (A + len - 1 + 1)%Z with (A + len)%Z by lia.
      apply sn_ret; [exact I'|]. split; [lia|left; reflexivity].
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hs & Hb). pose proof (byte_range b).
      pose proof (u8ro_read rsegs m1 A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 3 zstep. replace (A + i - 1 + 1)%Z with (A + i)%Z by lia.
      if_cases K0; zify_cond K0. { exfalso. exact (Hb K0). }
      zstep. if_cases Kc; zify_cond Kc.
      + replace (A + i)%Z with (A + (i + 1) - 1)%Z by lia. apply (IH (i + 1)%Z); try exact I'; lia.
      + apply sn_ret; [exact I'|]. split; [lia|right].
        replace (Z.to_nat (A + i - A)) with (Z.to_nat i) by lia. rewrite Hs. f_equal. apply bv_eq.
        rewrite Z_to_bv_unsigned, bv_wrap8_mod. rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="NONUL LO BND"] Lemma sn_tail_entry : forall (j : Z) m1 x10 x12 x13 x14 x15 x17,
    INV m1 -> (0 <= j <= len)%Z ->
    evt rsegs POST (ST 0x24850 m1 x10 x12 x13 x14 x15 (Z_to_bv 64 (A + j)) x17).
  Proof.
    intros j m1 x10 x12 x13 x14 x15 x17 I Hj. pose proof BND as BD.
    zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
    apply (sn_tail (Z.to_nat (len - j)) j); try exact I; lia.
  Qed.

  #[using="NONUL PAD LO BND"] Lemma sn_words : forall (k : nat) (j : Z) (kk : Z) m1 (x14 : word) x16 x17,
    INV m1 -> (Z.to_nat (len - j) = k) -> (0 <= j)%Z -> (j + 8 <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    (0 <= kk < 2^64)%Z ->
    evt rsegs POST (ST 0x247fc m1 (Z_to_bv 64 (A + j)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) x14 (Z_to_bv 64 kk) x16 x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros j kk m1 x14 x16 x17 I Hk Hj Hj8 Hal KK;
      pose proof I as I'; open_inv I; pose proof BND as BD; pose proof c_range as CR.
    pose proof (bv_unsigned_in_range 64 x14) as WR. unfold bv_modulus in WR; cbn in WR.
    do 5 zstep. if_cases K1; zify_cond K1.
    -
      zstep. apply sn_tail_entry; [exact I'|lia].
    -
      assert (HW : (Z.to_nat (j + 8) + 8 <= length full)%nat).
      { rewrite full_length. Z.div_mod_to_equations. lia. }
      pose proof (bytes_at_read rsegs m1 A full (j + 8) 8 STR ltac:(lia) HW) as RD.
      set (chunk' := firstn 8 (skipn (Z.to_nat (j + 8)) full)) in RD.
      assert (CL' : length chunk' = 8%nat). { subst chunk'. rewrite firstn_length, skipn_length. lia. }
      pose proof (le_val_range _ (bytes_ok_map chunk')) as WR'. rewrite length_map, CL' in WR'.
      change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR'.
      do 7 zstep. rewrite (load8_le_val chunk' CL'). replace (A + j + 8)%Z with (A + (j + 8))%Z by lia.
      if_cases K2; zify_cond K2.
      +
        apply (haszero64_clang _ (bytes_ok_map chunk') ltac:(rewrite length_map; exact CL')) in K2.
        rewrite In0_map_unsigned in K2.
        assert (Hj16 : (j + 16 <= len)%Z).
        { destruct (Z.lt_ge_cases len (j + 16)); [|assumption]. exfalso. apply K2. subst chunk'.
          apply nth_error_In with (n := (Z.to_nat len - Z.to_nat (j + 8))%nat).
          rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
          rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
        apply (IH (Z.to_nat (len - (j + 8)))); try exact I'; try lia; Z.div_mod_to_equations; lia.
      +
        zstep. apply sn_tail_entry; [exact I'|lia].
  Qed.

  #[using="NONUL PAD LO BND"] Lemma sn_wentry : forall (j : Z) m1 x12 x13 x14 x15 x16 x17,
    INV m1 -> (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evt rsegs POST (ST 0x247d0 m1 (Z_to_bv 64 (A + j)) x12 x13 x14 x15 x16 x17).
  Proof.
    intros j m1 x12 x13 x14 x15 x16 x17 I Hj Hal; pose proof I as I'; open_inv I; pose proof BND as BD; pose proof c_range as CR.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read rsegs m1 A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 9 zstep. rewrite ?Z.add_0_r. rewrite (load8_le_val chunk CL).
    if_cases K1; zify_cond K1.
    {   zstep. apply sn_tail_entry; [exact I'|lia]. }
    -
      apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K1.
      rewrite In0_map_unsigned in K1.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K1. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      zstep. zstep.
      apply (sn_words (Z.to_nat (len - j)) j (c * 72340172838076673)%Z); try exact I'; try lia.
      all: pose proof c_range; Z.div_mod_to_equations; nia.
  Qed.

  #[using="NONUL PAD LO BND SEP"] Lemma sn_head : forall (k : nat) (i : Z) m1 x13 x14 x15 x16 x17,
    INV m1 -> (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evt rsegs POST (ST 0x247b4 m1 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) x13 x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i m1 x13 x14 x15 x16 x17 I Hk Hi; pose proof I as I'; open_inv I; pose proof BND as BD;
      pose proof c_range as CR.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read rsegs m1 A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_true. apply sn_ret; [exact I'|]. split; [lia|left; reflexivity].
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hs & Hb). pose proof (byte_range b).
      pose proof (u8ro_read rsegs m1 A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K0; zify_cond K0. { exfalso. exact (Hb K0). }
      zstep. if_cases Kc; zify_cond Kc.
      + apply sn_ret; [exact I'|]. split; [lia|right].
        replace (Z.to_nat (A + i - A)) with (Z.to_nat i) by lia. rewrite Hs. f_equal. apply bv_eq.
        rewrite Z_to_bv_unsigned, bv_wrap8_mod. rewrite Z.mod_small by lia. lia.
      + do 4 zstep. if_cases Kal; zify_cond Kal.
        * replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
          apply (IH (i + 1)%Z); try exact I'; lia.
        * replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
          apply sn_wentry; [exact I'|lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.

  #[using="NONUL PAD LO BND SEP"] Lemma sn_body :
    mem_inv rsegs m -> bytes_at rsegs m A full -> stk rsegs m lo SP ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x24794) fc None m (seg_rom rsegs)).
  Proof.
    intros MI STR STK; pose proof BND as BD; pose proof c_range as CR.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1. cbn in R1.
    carve_frame 16%nat STK.
    do 4 zstep. replace (Z.land (bv_unsigned a1) 255) with c.
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (I : INV mm) by (split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact STK|]; exact FR) end.
    zstep. if_cases Kz; zify_cond Kz.
    -
      zstep. zstep. call strlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ exact MI. }
      do 5 zstep.
      lazymatch goal with H : stk _ ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => release_frame FR H (bv_unsigned sp) end.
      finish. split; [lia|left; reflexivity].
    - zstep. zstep. if_cases Kal; zify_cond Kal.
      +
        eapply evt_eq. 2:{ apply (sn_wentry 0); [exact I|lia|]. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
      + zstep.
        eapply evt_eq. 2:{ apply (sn_head (Z.to_nat len) 0); [exact I|lia|lia]. }
        unfold mkR. rewrite !Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.

Lemma strchrnul_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24794) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros STR NONUL PAD STK LO SEP MI.
  apply sn_body; try assumption.
  pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B.
  destruct STK as [? _]. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R. lia.
Qed.

Definition strchr_res (A : Z) (str : list byte) (c : Z) (r : Z) : Prop :=
  r = 0%Z \/ (c = 0%Z /\ r = (A + Z.of_nat (length str))%Z)
  \/ ((A <= r < A + Z.of_nat (length str))%Z /\ nth_error str (Z.to_nat (r - A)) = Some (Z_to_bv 8 c)).

Definition strchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack)
    /\ strchr_res (bv_unsigned a0) str (bv_unsigned a1 mod 256) r.

Lemma strchr_sel : forall bb cc r, (0 <= bb < 256)%Z -> (0 <= cc < 256)%Z -> (0 <= r < 2^64)%Z ->
  Z.land ((Z.b2z (0 <? Z.lxor bb cc)%Z + -1) mod 18446744073709551616) r = (if bb =? cc then r else 0)%Z.
Proof.
  intros bb cc r Hb Hc Hr. pose proof (Z.lxor_nonneg bb cc) as NN.
  destruct (Z.eqb_spec bb cc) as [E|NE].
  - subst. rewrite Z.lxor_nilpotent.
    replace ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616)%Z with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - assert (Hx : Z.lxor bb cc <> 0%Z). { intros Hx. apply NE. apply Z.lxor_eq. exact Hx. }
    replace (0 <? Z.lxor bb cc)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.

Lemma strchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24758) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros STR NONUL PAD STK LO SEP MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B.
  pose proof STK as STK0. destruct STK0 as [LO0 _]. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1; cbn in R1.
  assert (CR : (0 <= bv_unsigned a1 mod 256 < 256)%Z) by (apply Z.mod_pos_bound; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat STK.
  do 5 zstep.
  pose proof (unsigned_lit (bv_unsigned sp + -16) ltac:(lia)) as USP.
  call strchrnul_spec.
  1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ rewrite USP. exact STK. }
  all: rewrite ?USP; try lia. 1:{ exact MI. }
  rewrite ?USP in *.
  lazymatch goal with H : strchrnul_res _ _ _ ?rr |- _ => rename H into RES; rename rr into r end.
  destruct RES as [Hr Hrc].
  lazymatch goal with H : bytes_at _ ?mm (bv_unsigned a0) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR' end.

  assert (exists b, nth_error (str ++ Z_to_bv 8 0 :: slack) (Z.to_nat (r - bv_unsigned a0)) = Some b /\
                    (r = bv_unsigned a0 + Z.of_nat (length str) /\ bv_unsigned b = 0 \/
                     r < bv_unsigned a0 + Z.of_nat (length str) /\ nth_error str (Z.to_nat (r - bv_unsigned a0)) = Some b /\
                     bv_unsigned b = bv_unsigned a1 mod 256)%Z) as (b & Hb & Hcase).
  { destruct (Z.eq_dec r (bv_unsigned a0 + Z.of_nat (length str))) as [E|NE].
    - exists (Z_to_bv 8 0). split. { rewrite E. replace (Z.to_nat _) with (length str) by lia.
        rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. } left. split; [exact E|reflexivity].
    - destruct Hrc as [|Hn]; [lia|]. exists (Z_to_bv 8 (bv_unsigned a1 mod 256)). split.
      { rewrite nth_error_app1 by (apply nth_error_lt in Hn; lia). exact Hn. }
      right. split; [lia|]. split; [exact Hn|]. rewrite Z_to_bv_unsigned, bv_wrap8_mod. rewrite Z.mod_small by lia. reflexivity. }
  pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB; cbn in RB.
  pose proof (u8ro_read rsegs _ (bv_unsigned a0) _ (r - bv_unsigned a0) b (Z_to_bv 64 r) STR' Hb ltac:(lia)
                ltac:(cbv delta [wa]; f_equal; lia)) as RD.
  do 2 zstep. replace (Z.land (bv_unsigned a1) 255) with (bv_unsigned a1 mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  do 8 zstep.
  lazymatch goal with H : stk _ ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => release_frame FR H (bv_unsigned sp) end.
  rewrite (strchr_sel (bv_unsigned b) (bv_unsigned a1 mod 256) r) by lia.
  assert (RES' : strchr_res (bv_unsigned a0) str (bv_unsigned a1 mod 256)%Z (if bv_unsigned b =? bv_unsigned a1 mod 256 then r else 0)%Z).
  { unfold strchr_res. destruct (Z.eqb_spec (bv_unsigned b) (bv_unsigned a1 mod 256)%Z) as [E|NE].
    - destruct Hcase as [[Hr1 Hb0]|(Hr1 & Hn & Hbc)].
      + right. left. split; [lia|exact Hr1].
      + right. right. split; [lia|]. rewrite Hn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap8_mod, Z.mod_small by lia. exact Hbc.
    - left. reflexivity. }
  finish.
Qed.
