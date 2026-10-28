(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition memchr_entry := 0xd05ec%Z.

Section ZFacts.
  Open Scope Z_scope.
  Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
  Proof.
    intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. split; [lia|].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
    pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
    assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    lia.
  Qed.

  Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= y -> 0 <= y' ->
    Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
  Proof.
    intros x y x' y' Hx Hx' Hy Hy'.
    pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
    apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
    destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
  Qed.

  Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
  Proof. intros bs H. pose proof (le_val_range bs H). lia. Qed.

  Lemma le_val_xor_bcast : forall bs c, bytes_ok bs -> 0 <= c < 256 ->
    Z.lxor (le_val bs) (c * ones (length bs)) = le_val (map (fun b => Z.lxor b c) bs).
  Proof.
    induction bs as [|b bs IH]; intros c Hok Hc.
    - cbn. rewrite Z.mul_0_r. reflexivity.
    - inversion Hok as [|b0 bs0 Hb Hbs]; subst. cbn [le_val ones length map].
      replace (c * (1 + 256 * ones (length bs))) with (c + 256 * (c * ones (length bs))) by lia.
      rewrite lxor_split; try lia.
      + rewrite IH by assumption. reflexivity.
      + apply le_val_nonneg. exact Hbs.
      + pose proof (le_val_range (repeat 1 (length bs))) as Hr. assert (0 <= ones (length bs)); [|nia].
        clear. induction (length bs); cbn; lia.
  Qed.

  Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
  Proof.
    intros bs c H Hc. unfold bytes_ok in *. rewrite Forall_map. eapply Forall_impl; [|exact H].
    intros b Hb. apply lxor_lt_256; assumption.
  Qed.

  Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
  Proof.
    intros bs c. rewrite in_map_iff. split.
    - intros (b & Hb & Hin). apply Z.lxor_eq in Hb. subst. exact Hin.
    - intros Hin. exists c. split; [apply Z.lxor_nilpotent| exact Hin].
  Qed.
End ZFacts.

Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ bytes_at usegs m' (bv_unsigned a0) buf.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis BUF : bytes_at usegs m (bv_unsigned a0) buf.
  Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono usegs m m := wmono_refl usegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length buf)).
  Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).

  Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
  Notation CMAGIC := 72340172838076672%Z.
  Notation HIGHS := 9259542123273814144%Z.
  Notation ONES := 72340172838076673%Z.

  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ BUF).
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  Lemma NOB_0 : NOB 0.
  Proof. intros j b Hj. cbn in Hj. lia. Qed.

  Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof.
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  Lemma ok_cases :
    (exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
       (forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
       (n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
    \/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
  Proof.
    pose proof OK as H. unfold memchr_ok in H.
    destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
    - left. destruct (find_byte_Some _ _ _ FB) as (Hl & (b & Hn & Hb) & Hmin).
      rewrite firstn_length in Hl.
      rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
      exists j, b. repeat split; try assumption; try lia.
      intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
      replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
    - right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
      replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
  Qed.

  Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
  Proof.
    intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. apply nth_error_None in E.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
    exact (HN _ _ Hlt Hn Hb).
  Qed.

  Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    (Z.to_nat i + 8 <= length buf)%nat.
  Proof.
    intros i Hi Hi8 Hal HN.
    destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
    pose proof (nth_error_lt _ _ _ Hn).
    destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
    destruct Hsl as [Hsl|Hsl]; [lia|].
    destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    memchr_res A c n buf = (A + i)%Z.
  Proof.
    intros i b Hi HN Hn Hb. unfold memchr_res.
    rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
    - rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
    - intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
      exact (HN _ _ Hj Hn').
  Qed.

  Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
  Proof.
    intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
    exact (HN j b ltac:(lia) Hn).
  Qed.

  Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
    evt usegs POST (ST 0xd068c x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K; zify_cond K.
    -   zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
    - zstep. zstep. zstep. if_cases K0; zify_cond K0.
      + replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      +   zstep. zstep. rewrite <- res_none at 1. { finish. }
        replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
  Qed.

  Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i ->
    evt usegs POST (ST 0xd0684 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
    - apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
  Qed.

  Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    evt usegs POST (ST 0xd0660 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
    pose proof (readable8 i Hi Hi8 Hal HN) as HW.
    pose proof (bytes_at_read usegs m A buf i 8 BUF ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat i) buf)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    do 6 zstep.
    rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    if_cases K; zify_cond K.
    -
      clear K. destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
      zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kz; zify_cond Kz; [|exfalso; lia].
        replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (memchr_tail (Z.to_nat (n - (i + 1))) (i + 1)); try lia. eapply NOB_S; eauto; lia.
      + zstep. zstep. rewrite <- (res_found i b ltac:(lia) HN Hn Kb). finish.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.

      assert (HN8 : NOB (i + 8)).
      { intros j b Hj Hn. destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (j - Z.to_nat i)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- Hn. f_equal. lia. }
      zstep. zstep. zstep. if_cases K8; zify_cond K8.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (IH (Z.to_nat (n - (i + 8)))); try lia; try exact HN8. all: Z.div_mod_to_equations; lia.
      + replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
        apply (memchr_tail_entry (i + 8)); try lia; exact HN8.
  Qed.

  Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
    evt usegs POST (ST 0xd0630 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
    zstep. if_cases K; zify_cond K.
    -   apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
    - assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
      destruct Hal as [|Hal]; [lia|].
      destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases Kb; zify_cond Kb.
      + apply memchr_tail_entry; [lia| exact HN].
      + zstep. zstep. if_cases K8; zify_cond K8.
        * apply memchr_tail_entry; [lia| exact HN].
        * do 7 zstep.
          apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
  Qed.

  Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
  Proof. intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed.

  Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
    evt usegs POST (ST 0xd0608 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
  Proof.
    induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read usegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
    -   apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
    - pose proof (NOB_S i b ltac:(lia) HN Hn Kb) as HN1.
      zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
        apply (memchr_mid (i + 1)); try lia; try exact HN1.
        * rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
        * right. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
      + zstep. zstep. if_cases K1; zify_cond K1.
        * replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
          replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (IH (i + 1)%Z); try lia; try exact HN1. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
        * replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
          apply (memchr_mid (i + 1)); try lia; try exact HN1. rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
  Qed.

  Lemma memchr_body :
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xd05ec) fc None m (seg_rom usegs)).
  Proof.
    pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
    zstep. replace (Z.land (bv_unsigned a1) 255) with c.
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
    zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    -
      eapply evt_eq.
      2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
          - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          - right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zstep. if_cases K0; zify_cond K0.
      +
        eapply evt_eq.
        2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
            - apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + zstep. zstep.
        eapply evt_eq.
        2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
            - apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
        unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
  Qed.
End Proofs.

Lemma memchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at usegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv usegs m ->
  evt usegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd05ec) fc None m (seg_rom usegs)).
Proof. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.
