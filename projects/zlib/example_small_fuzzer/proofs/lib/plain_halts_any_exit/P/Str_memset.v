(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.

Module F_memchr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Open Scope bv_scope.

Definition memchr_entry := 0x27a6c%Z.

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
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ bytes_at psegs m' (bv_unsigned a0) buf.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv psegs m.
  Hypothesis BUF : bytes_at psegs m (bv_unsigned a0) buf.
  Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono psegs m m := wmono_refl psegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length buf)).
  Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).
  Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).
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
    evt psegs POST (ST 0x27b0c x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read psegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
    - zstep. zstep. zstep. if_cases K0; zify_cond K0.
      + replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + zstep. zstep. rewrite <- res_none at 1. { finish. }
        replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
  Qed.

  Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
    (0 <= i <= n)%Z -> NOB i ->
    evt psegs POST (ST 0x27b04 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
    - apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
  Qed.

  Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
    Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
    evt psegs POST (ST 0x27ae0 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
    pose proof (readable8 i Hi Hi8 Hal HN) as HW.
    pose proof (bytes_at_read psegs m A buf i 8 BUF ltac:(lia) HW) as RD.
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
      pose proof (u8ro_read psegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
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
    evt psegs POST (ST 0x27ab0 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
  Proof.
    intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
    zstep. if_cases K; zify_cond K.
    - apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
    - assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
      destruct Hal as [|Hal]; [lia|].
      destruct (readable i ltac:(lia) HN) as [b Hn].
      pose proof (u8ro_read psegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
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
    evt psegs POST (ST 0x27a88 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
  Proof.
    induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
    destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
    pose proof (u8ro_read psegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
    - apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
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
    evt psegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x27a6c) fc None m (seg_rom psegs)).
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
  bytes_at psegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv psegs m ->
  evt psegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x27a6c) fc None m (seg_rom psegs)).
Proof. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.
End F_memchr.

Module F_strnlen.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.F_memchr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Definition strnlen_entry := 0x27a28%Z.

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ bytes_at psegs m' (bv_unsigned a0) buf.

Lemma strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk psegs m lo (bv_unsigned sp) ->
  bytes_at psegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv psegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt psegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x27a28) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros ST BUF OK MI LO SEP A0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep.
  call memchr_spec.
  1:{ exact BUF. }
  1:{ rewrite unsigned_lit by lia. exact OK. }
  1:{ assumption. }
  rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
      by (unfold strnlen_res; rewrite FB; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
    replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
      by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.
End F_strnlen.

Module InitMem.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.
(* the body below is the edition's text, spliced by tools727/splice_module727.py *)

Lemma extract_byte_eq : forall (v : word) (k : N),
  bv_extract k 8 v = Z_to_bv 8 (Z.shiftr (bv_unsigned v) (Z.of_N k)).
Proof. intros v k. apply bv_eq. rewrite bv_extract_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

Lemma word_le8_le8 : forall v : word, word_le8 v = le8 v.
Proof.
  intros v. unfold word_le8, le8, word_to_le_bytes. cbn [Z_to_le_bytes].
  rewrite !extract_byte_eq. rewrite !Z.shiftr_shiftr by lia. cbn [Z.of_N Z.add].
  rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma flat_map_word_le8 : forall ws, flat_map word_le8 ws = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [flat_map u64s]. rewrite word_le8_le8, IH. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Fixpoint rw_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A), wview segs (fun _ => None) (wa A) with
      | Some b', Some _ => bv_eqb b b' && rw_bytes_b (A + 1) bs'
      | _, _ => false
      end
  end.

Lemma rw_bytes_b_sound : forall bs A (m : word -> option byte),
  rw_bytes_b A bs = true ->
  (forall a : word, (A <= bv_unsigned a < A + Z.of_nat (length bs))%Z -> m a = None) ->
  (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  forall i b, nth_error bs i = Some b ->
    mrd segs m (wa (A + Z.of_nat i)) = Some b /\ wview segs m (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs as [|b0 bs IH]; intros A m Hb Hm HA Hl i b Hn; [destruct i; discriminate|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom segs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [Hbe Hb]. unfold bv_eqb in Hbe. apply Z.eqb_eq in Hbe. apply bv_eq in Hbe. subst b'.
  cbn [length] in Hl, Hm.
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. rewrite Z.add_0_r.
    assert (Hnone : m (wa A) = None). { apply Hm. rewrite wa_unsigned by lia. lia. }
    split. { unfold mrd. rewrite Hnone. exact Er. }
    unfold wview in *. rewrite Hnone. intros C. rewrite C in Ew. discriminate.
  - cbn in Hn. replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia.
    apply (IH (A + 1)%Z m Hb); try lia; [|exact Hn]. intros a Ha. apply Hm. lia.
Qed.

Lemma rw_cells_image0 : forall (m : word -> option byte) A bs,
  (forall a : word, (A <= bv_unsigned a < A + Z.of_nat (length bs))%Z -> m a = None) ->
  rw_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs Hm Hb HA Hl. pose proof (rw_bytes_b_sound bs A m Hb Hm HA Hl) as G.
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:E. { apply (proj1 (G i b E)). } apply nth_error_None in E. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E. { apply (proj2 (G _ b E)). } apply nth_error_None in E. lia.
Qed.

Lemma rw_cells_recast : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> wr_at segs m a' n'.
Proof.
  intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
Qed.

Lemma rw_cells_of_parts : forall m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros m A cs Hwf Hb Hw. split; [split; assumption| exact Hw]. Qed.

Lemma bytes_at_eqa : forall m a b bs, bytes_at segs m a bs -> a = b -> bytes_at segs m b bs.
Proof. intros m a b bs H E. subst b. exact H. Qed.

Lemma bytes_at_slice : forall m a bs off k,
  bytes_at segs m a bs -> (off + k <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros m a bs off k H Hk.
  rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Fixpoint segs_top (sg : list Segment) : Z :=
  match sg with
  | [] => 0
  | s0 :: rest => Z.max (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) (segs_top rest)
  end.

Lemma find_segment_high : forall sg a n, (1 <= n)%Z -> (segs_top sg <= a)%Z -> find_segment sg a n = None.
Proof.
  induction sg as [|s0 sg IH]; intros a n Hn Ha; [reflexivity|]. cbn [find_segment segs_top] in *.
  replace (Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. apply IH; lia.
Qed.

(* The initial memory of a launch: Linux's block from [sp] up to the stack
   VMA's end, zero bytes in [[stack_window_lo, sp)], nothing elsewhere. *)
Section Init.

  Variables (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw).
  Notation m0 := (wrap_mem inp mbase ph entry sp draw).
  Notation ent := (entry_stack_image inp mbase ph entry sp draw).
  Notation wlo := (stack_window_lo (in_kernel inp) mbase draw).

  Lemma init_at : forall a : word,
    m0 a = if (Z.leb (bv_unsigned sp) (bv_unsigned a)) then
             (if Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))
              then nth_error ent (Z.to_nat (bv_unsigned a - bv_unsigned sp)) else None)
           else if Z.leb wlo (bv_unsigned a) then Some (Z_to_bv 8 0) else None.
  Proof.
    intros a. unfold wrap_mem, stack_to_mem.
    destruct (Z.leb_spec0 (bv_unsigned sp) (bv_unsigned a)).
    - destruct (Z.ltb_spec0 (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))).
      + destruct (nth_error ent (Z.to_nat (bv_unsigned a - bv_unsigned sp))) eqn:E; [reflexivity|].
        apply nth_error_None in E. lia.
      + replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity.
    - replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite andb_true_r. reflexivity.
  Qed.

  Lemma init_at_block : forall a : word,
    (bv_unsigned sp <= bv_unsigned a < bv_unsigned sp + Z.of_nat (length ent))%Z ->
    m0 a = nth_error ent (Z.to_nat (bv_unsigned a - bv_unsigned sp)).
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  Qed.

  Lemma init_none : forall a : word,
    (bv_unsigned a < bv_unsigned sp)%Z -> (bv_unsigned a < wlo)%Z -> m0 a = None.
  Proof.
    intros a H1 H2. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb wlo (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  Qed.

  Lemma init_none_above : forall a : word, (bv_unsigned sp + Z.of_nat (length ent) <= bv_unsigned a)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  Lemma init_stk : forall lo, (wlo <= lo)%Z -> (0 <= lo)%Z -> stk segs m0 lo (bv_unsigned sp).
  Proof.
    intros lo Hlo H0. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (E : m0 (wa a) = Some (Z_to_bv 8 0)).
    { rewrite init_at, wa_unsigned by lia.
      replace (Z.leb (bv_unsigned sp) a) with false by (symmetry; apply Z.leb_gt; lia).
      replace (Z.leb wlo a) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    split. { unfold wview. rewrite E. discriminate. } exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.

  Section Inv.
    Variable L : Z.
    Hypothesis SEGS_LOW : forall a : word, (L <= bv_unsigned a)%Z -> find_segment segs (bv_unsigned a) 1 = None.
    Hypothesis LSP : (L <= bv_unsigned sp)%Z.
    Hypothesis LWLO : (L <= wlo)%Z.
    (* OUR Lib/Mem.mem_inv is stronger than the donor's (mem_ok_at: also every mapped byte and
       every segment byte below UTOP), so the block's top below UTOP is a premise here, as in our r30q2 init_mem_inv
       (its IMGTOP); the proof is our r30q2 one with the donor's floor L for r30q2's sp - stack_max_size *)
    Hypothesis IMGTOP : (bv_unsigned sp + Z.of_nat (length ent) <= UTOP)%Z.

    Lemma init_mem_inv : mem_inv segs m0.
    Proof.
      apply mem_inv_intro.
      - intros a Hs. unfold seg_addr in Hs.
        destruct (Z.lt_ge_cases (bv_unsigned a) L) as [Hl|Hh].
        + pose proof (Nat2Z.is_nonneg (length ent)). lia.
        + rewrite SEGS_LOW in Hs by lia. discriminate.
      - intros a b H. unfold ro_addr.
        destruct (Z.lt_ge_cases (bv_unsigned a) L) as [Hl|Hh].
        + rewrite init_none in H by lia. discriminate.
        + rewrite SEGS_LOW by lia. split; [reflexivity|].
          destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp + Z.of_nat (length ent))) as [Hl'|Hh']; [lia|].
          rewrite init_none_above in H by lia. discriminate.
    Qed.
  End Inv.

  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length ent) <= 2^64)%Z.

  Lemma init_stack_bytes : bytes_at segs m0 (bv_unsigned sp) ent.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold mrd.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + Z.of_nat i)) = (bv_unsigned sp + Z.of_nat i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    replace (Z.to_nat (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)) with i by lia.
    destruct (nth_error ent i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_wr : wr_at segs m0 (bv_unsigned sp) (Z.of_nat (length ent)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + i)) = (bv_unsigned sp + i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    destruct (nth_error ent (Z.to_nat (bv_unsigned sp + i - bv_unsigned sp))) eqn:E; [discriminate|].
    apply nth_error_None in E. lia.
  Qed.
End Init.

(* the donor's statement plus our UTOP premise (our r30q2 init_mem_inv' had it too) *)
Lemma init_mem_inv' : forall inp mbase ph entry sp draw L,
  (L <= bv_unsigned sp)%Z -> (L <= stack_window_lo (in_kernel inp) mbase draw)%Z ->
  (bv_unsigned sp + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) <= UTOP)%Z ->
  (segs_top segs <= L)%Z ->
  mem_inv segs (wrap_mem inp mbase ph entry sp draw).
Proof.
  intros inp mbase ph entry sp draw L H1 H2 H3 H4. apply (init_mem_inv inp mbase ph entry sp draw L); try assumption.
  intros a Ha. apply find_segment_high; lia.
Qed.

Fixpoint str_ptrs (base : Z) (strs : list (list byte)) : list Z :=
  match strs with
  | [] => []
  | s :: rest => base :: str_ptrs (base + Z.of_nat (length s) + 1)%Z rest
  end.

Lemma str_ptrs_length : forall strs base, length (str_ptrs base strs) = length strs.
Proof. induction strs; intros; cbn; [reflexivity|]. now rewrite IHstrs. Qed.

Lemma total_arg_bytes_cons : forall s0 strs, total_arg_bytes (s0 :: strs) = (Z.of_nat (length s0) + 1 + total_arg_bytes strs)%Z.
Proof. reflexivity. Qed.
Lemma total_arg_bytes_nil : total_arg_bytes [] = 0%Z.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_nonneg : forall strs, (0 <= total_arg_bytes strs)%Z.
Proof. induction strs; [rewrite total_arg_bytes_nil | rewrite total_arg_bytes_cons]; lia. Qed.

Lemma flatten_strings_length : forall strs, Z.of_nat (length (flatten_strings strs)) = total_arg_bytes strs.
Proof.
  induction strs as [|s0 strs IH]; [reflexivity|]. rewrite total_arg_bytes_cons. unfold flatten_strings in *. cbn [flat_map].
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

Lemma string_addrs_eq : forall strs base,
  string_addrs (Z_to_bv 64 base) strs = (map (Z_to_bv 64) (str_ptrs base strs), Z_to_bv 64 (base + total_arg_bytes strs)%Z).
Proof.
  induction strs as [|s0 strs IH]; intros base; cbn [string_addrs str_ptrs map].
  - rewrite total_arg_bytes_nil, Z.add_0_r. reflexivity.
  - unfold len_word. rewrite !lit_add_lit.
    change (Z_to_bv 64 (base + Z.of_nat (length s0))) with (wa (base + Z.of_nat (length s0))). rewrite wa_succ. unfold wa.
    rewrite IH. cbn [fst snd]. f_equal. f_equal. rewrite total_arg_bytes_cons. lia.
Qed.

Lemma str_ptrs_nth : forall strs base i s, nth_error strs i = Some s ->
  exists off, nth_error (str_ptrs base strs) i = Some (base + off)%Z /\
    (0 <= off)%Z /\ (off + Z.of_nat (length s) + 1 <= total_arg_bytes strs)%Z /\
    firstn (length s + 1) (skipn (Z.to_nat off) (flatten_strings strs)) = s ++ [Z_to_bv 8 0].
Proof.
  induction strs as [|s0 strs IH]; intros base [|i] s Hn; cbn in Hn; try discriminate.
  - injection Hn as ->. exists 0%Z. cbn [str_ptrs nth_error]. rewrite Z.add_0_r. split; [reflexivity|].
    split; [lia|]. split. { rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia. }
    unfold flatten_strings. change (Z.to_nat 0) with 0%nat. rewrite skipn_O. cbn [flat_map].
    rewrite firstn_app. rewrite (@firstn_all2 _ (length s + 1) (s ++ [Z_to_bv 8 0])) by (rewrite app_length; cbn; lia).
    rewrite app_length. cbn [length]. replace (length s + 1 - (length s + 1))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
  - destruct (IH (base + Z.of_nat (length s0) + 1)%Z i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (Z.of_nat (length s0) + 1 + off)%Z. cbn [str_ptrs nth_error].
    split. { rewrite Hp. f_equal. lia. } split; [lia|]. split. { rewrite total_arg_bytes_cons. lia. }
    unfold flatten_strings. cbn [flat_map]. rewrite skipn_app, app_length. cbn [length].
    replace (Z.to_nat (Z.of_nat (length s0) + 1 + off) - (length s0 + 1))%nat with (Z.to_nat off) by lia.
    rewrite skipn_all2 by (rewrite app_length; cbn; lia). cbn [app]. exact Hf.
Qed.

Lemma str_ptrs_bounds : forall strs base i p, nth_error (str_ptrs base strs) i = Some p ->
  (base <= p /\ p < base + total_arg_bytes strs)%Z.
Proof.
  induction strs as [|s0 strs IH]; intros base [|i] p Hn; cbn in Hn; try discriminate.
  - injection Hn as <-. rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia.
  - apply IH in Hn. rewrite total_arg_bytes_cons. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* The layout of [StackLayout.build_stack_bytes], as offsets from [sp] and     *)
(* from the stack VMA's end [top]: argc, the argv pointers, NULL, the envp     *)
(* pointers, NULL, the auxv, the odd-item gap, the sixteen AT_RANDOM bytes,     *)
(* the [arch_align_stack] pad, the argv/envp strings, the exec name and its    *)
(* NUL, and the eight-byte slot under [top].                                   *)
(* ------------------------------------------------------------------------- *)

Definition argc (argv : list (list byte)) : Z := Z.of_nat (length argv).
Definition envc (envp : list (list byte)) : Z := Z.of_nat (length envp).

Definition lsb (argv envp : list (list byte)) (execfn : list byte) : Z :=
  Z.of_nat (launch_string_bytes argv envp execfn).

Definition str_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (bv_unsigned top - 8 - lsb argv envp execfn)%Z.
Definition env_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (str_base top argv envp execfn + total_arg_bytes argv)%Z.
Definition xfn_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (env_base top argv envp execfn + total_arg_bytes envp)%Z.

Definition argv_ptrs (top : word) (argv envp : list (list byte)) (execfn : list byte) : list word :=
  map (Z_to_bv 64) (str_ptrs (str_base top argv envp execfn) argv).
Definition envp_ptrs (top : word) (argv envp : list (list byte)) (execfn : list byte) : list word :=
  map (Z_to_bv 64) (str_ptrs (env_base top argv envp execfn) envp).

Definition head_len (rseq : bool) (argv envp : list (list byte)) : Z :=
  Z.of_nat (block_head_size rseq argv envp).
Definition rnd_addr (rseq : bool) (sp : word) (argv envp : list (list byte)) : Z :=
  (bv_unsigned sp + head_len rseq argv envp - 16)%Z.
Definition envp_addr (sp : word) (argv : list (list byte)) : Z := (bv_unsigned sp + 8 * (argc argv + 2))%Z.
Definition auxv_addr (sp : word) (argv envp : list (list byte)) : Z := (bv_unsigned sp + 8 * (argc argv + envc envp + 3))%Z.
Definition gap_len (argv envp : list (list byte)) : nat := (8 * (block_items argv envp mod 2))%nat.

Definition auxv_words (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : word) (argv envp : list (list byte))
    (execfn : list byte) (uid gid hw : word) : list word :=
  flat_map (fun e : word * word => [fst e; snd e])
    (auxv_entries la ph entry uid gid hw (Z_to_bv 64 (rnd_addr (la_rseq la) sp argv envp))
                  (Z_to_bv 64 (xfn_base top argv envp execfn))).

(* What the launch conjunct of [Run.valid_entry_va] guarantees about the
   block: the pad [arch_align_stack] left is not clamped, so the block runs
   exactly from [sp] to [top]. *)
Definition geom_ok (rseq : bool) (sp top : word) (argv envp : list (list byte)) (execfn : list byte) : Prop :=
  (bv_unsigned sp + head_len rseq argv envp + lsb argv envp execfn + 8 <= bv_unsigned top)%Z.

(* The facts about a launch the start-up and [main] read off the block: the
   block's geometry and the stack VMA's end inside the Sv48 window.  The
   auxv's length stays symbolic in [la_rseq la]: no kernel build is pinned. *)
Definition launch_ok (la : LaunchAuxv) (sp top : word) (argv envp : list (list byte)) (execfn : list byte) : Prop :=
  geom_ok (la_rseq la) sp top argv envp execfn /\ (bv_unsigned top <= sp_window_hi)%Z.

Lemma lsb_eq : forall argv envp execfn,
  lsb argv envp execfn = (total_arg_bytes argv + total_arg_bytes envp + Z.of_nat (length execfn) + 1)%Z.
Proof.
  intros argv envp execfn. pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
  unfold lsb, launch_string_bytes. lia.
Qed.

Lemma xfn_base_eq : forall top argv envp execfn,
  xfn_base top argv envp execfn = (bv_unsigned top - 9 - Z.of_nat (length execfn))%Z.
Proof. intros. unfold xfn_base, env_base, str_base. rewrite lsb_eq. lia. Qed.

Lemma lit_sub_wrap : forall (a : word) (k : Z), a - Z_to_bv 64 k = Z_to_bv 64 (bv_unsigned a - k).
Proof.
  intros a k. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

Lemma string_base_addr_eq : forall top argv envp execfn,
  string_base_addr top argv envp execfn = Z_to_bv 64 (str_base top argv envp execfn).
Proof.
  intros. unfold string_base_addr, nat_to_word. rewrite lit_sub_wrap. f_equal. unfold str_base, lsb. lia.
Qed.

Lemma at_execfn_ptr_eq : forall top argv envp execfn,
  at_execfn_ptr top execfn = Z_to_bv 64 (xfn_base top argv envp execfn).
Proof.
  intros. unfold at_execfn_ptr, nat_to_word. rewrite lit_sub_wrap, xfn_base_eq. f_equal. lia.
Qed.

Lemma at_random_ptr_eq : forall (sp : word) rseq argv envp,
  at_random_ptr sp rseq argv envp = Z_to_bv 64 (rnd_addr rseq sp argv envp).
Proof.
  intros. unfold at_random_ptr, rnd_addr, head_len, nat_to_word.
  assert (H16 : (16 <= block_head_size rseq argv envp)%nat) by (unfold block_head_size; cbv zeta; lia).
  rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite lit_add_lit. f_equal. lia.
Qed.

Lemma u64s_flat_pairs : forall es : list (word * word),
  u64s (flat_map (fun e : word * word => [fst e; snd e]) es)
  = flat_map (fun e : word * word => word_le8 (fst e) ++ word_le8 (snd e)) es.
Proof.
  induction es as [|e es IH]; [reflexivity|]. cbn [flat_map].
  rewrite u64s_app, IH. cbn [u64s]. rewrite ?app_nil_r.
  rewrite ?(word_le8_le8 (fst e)), ?(word_le8_le8 (snd e)).
  rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma build_stack_bytes_eq : forall la ph entry (sp top : word) argv envp execfn (uid gid hw : word) draw,
  build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw =
  le8 (Z_to_bv 64 (argc argv)) ++ u64s (argv_ptrs top argv envp execfn) ++ le8 (Z_to_bv 64 0)
  ++ u64s (envp_ptrs top argv envp execfn) ++ le8 (Z_to_bv 64 0)
  ++ u64s (auxv_words la ph entry sp top argv envp execfn uid gid hw)
  ++ repeat (Z_to_bv 8 0) (gap_len argv envp) ++ at_random_bytes (ed_random draw)
  ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top argv envp execfn)
  ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8.
Proof.
  intros. unfold build_stack_bytes. cbv zeta.
  rewrite string_base_addr_eq, string_addrs_eq. cbv beta iota.
  rewrite string_addrs_eq. cbv beta iota.
  rewrite (at_random_ptr_eq sp (la_rseq la) argv envp), (at_execfn_ptr_eq top argv envp execfn).
  unfold auxv_bytes, build_auxv, auxv_words. rewrite <- u64s_flat_pairs.
  rewrite !word_le8_le8, !flat_map_word_le8.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma length_bsb : forall la ph entry (sp top : word) argv envp execfn (uid gid hw : word) draw,
  Z.of_nat (length (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw))
  = (head_len (la_rseq la) argv envp + Z.of_nat (block_pad_len (la_rseq la) sp top argv envp execfn)
     + lsb argv envp execfn + 8)%Z.
Proof. intros. rewrite length_build_stack_bytes. unfold head_len, lsb. lia. Qed.

Lemma pad_len_eq : forall rseq (sp top : word) argv envp execfn,
  geom_ok rseq sp top argv envp execfn ->
  Z.of_nat (block_pad_len rseq sp top argv envp execfn)
  = (bv_unsigned top - 8 - lsb argv envp execfn - bv_unsigned sp - head_len rseq argv envp)%Z.
Proof.
  intros rseq sp top argv envp execfn G. unfold geom_ok in G. unfold block_pad_len. unfold lsb, head_len in *.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma head_len_eq : forall rseq argv envp,
  head_len rseq argv envp
  = (8 * (argc argv + envc envp + 3) + 16 * Z.of_nat (auxv_count rseq) + Z.of_nat (gap_len argv envp) + 16)%Z.
Proof.
  intros. unfold head_len, block_head_size, gap_len, block_items, auxv_size, argc, envc. cbv zeta.
  remember ((length argv + length envp + 3) mod 2)%nat as q. lia.
Qed.

Lemma head_len_ge : forall rseq argv envp,
  (8 * (argc argv + envc envp + 3) + Z.of_nat (auxv_size rseq) + 16 <= head_len rseq argv envp)%Z.
Proof.
  intros. rewrite head_len_eq. unfold gap_len, auxv_size.
  pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia.
Qed.

Lemma auxv_words_length : forall la ph entry sp top argv envp execfn uid gid hw,
  length (auxv_words la ph entry sp top argv envp execfn uid gid hw) = (2 * auxv_count (la_rseq la))%nat.
Proof. intros. unfold auxv_words, auxv_entries. destruct (la_rseq la); reflexivity. Qed.

Lemma argv_ptrs_length : forall top argv envp execfn, length (argv_ptrs top argv envp execfn) = length argv.
Proof. intros. unfold argv_ptrs. rewrite map_length. apply str_ptrs_length. Qed.
Lemma envp_ptrs_length : forall top argv envp execfn, length (envp_ptrs top argv envp execfn) = length envp.
Proof. intros. unfold envp_ptrs. rewrite map_length. apply str_ptrs_length. Qed.

Lemma img_length : forall la ph entry (sp top : word) argv envp execfn (uid gid hw : word) draw,
  geom_ok (la_rseq la) sp top argv envp execfn ->
  Z.of_nat (length (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw))
  = (bv_unsigned top - bv_unsigned sp)%Z.
Proof. intros la ph entry sp top argv envp execfn uid gid hw draw G. rewrite length_bsb, (pad_len_eq _ _ _ _ _ _ G). lia. Qed.

Lemma str_base_ge : forall rseq (sp top : word) argv envp execfn,
  geom_ok rseq sp top argv envp execfn ->
  (bv_unsigned sp + head_len rseq argv envp <= str_base top argv envp execfn)%Z.
Proof. intros rseq sp top argv envp execfn G. unfold geom_ok in G. unfold str_base. lia. Qed.

Lemma envp_ptrs_nz : forall rseq (sp top : word) argv envp execfn,
  geom_ok rseq sp top argv envp execfn ->
  Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs top argv envp execfn).
Proof.
  intros rseq sp top argv envp execfn G.
  apply Forall_forall. intros w Hw. apply In_nth_error in Hw. destruct Hw as [i Hi].
  unfold envp_ptrs in Hi. rewrite nth_error_map in Hi.
  destruct (nth_error (str_ptrs (env_base top argv envp execfn) envp) i) as [q|] eqn:E; [|discriminate].
  cbn in Hi. injection Hi as <-.
  apply str_ptrs_bounds in E.
  pose proof (str_base_ge _ _ _ _ _ _ G) as SB. pose proof (head_len_ge rseq argv envp) as HG.
  pose proof (lsb_eq argv envp execfn) as LE. pose proof (total_arg_bytes_nonneg argv) as TA.
  pose proof (bv_unsigned_in_range 64 top) as RT. unfold bv_modulus in RT. cbn in RT.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  unfold env_base, str_base, argc, envc in *.
  rewrite unsigned_lit by lia. lia.
Qed.

(* Reading the block back out of a memory that holds it at [sp]. *)
Section Pieces.
  Variables (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : word) (argv envp : list (list byte))
            (execfn : list byte) (uid gid hw : word) (draw : EntryDraw) (m : word -> option byte).
  Notation img := (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw).
  Notation usp := (bv_unsigned sp).
  Notation AP := (argv_ptrs top argv envp execfn).
  Notation EP := (envp_ptrs top argv envp execfn).
  Notation AW := (auxv_words la ph entry sp top argv envp execfn uid gid hw).
  Hypothesis IMG : bytes_at segs m usp img.
  Hypothesis GEOM : geom_ok (la_rseq la) sp top argv envp execfn.

  Lemma img_pieces :
    bytes_at segs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at segs m (usp + 8) (u64s (AP ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (envp_addr sp argv) (u64s EP ++ le8 (Z_to_bv 64 0) ++ u64s AW) /\
    bytes_at segs m (auxv_addr sp argv envp) (u64s AW) /\
    bytes_at segs m (rnd_addr (la_rseq la) sp argv envp) (at_random_bytes (ed_random draw)) /\
    bytes_at segs m (str_base top argv envp execfn) (flatten_strings argv) /\
    bytes_at segs m (env_base top argv envp execfn) (flatten_strings envp) /\
    bytes_at segs m (xfn_base top argv envp execfn) (execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8).
  Proof.
    pose proof IMG as B. rewrite build_stack_bytes_eq in B.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    pose proof (pad_len_eq _ _ _ _ _ _ GEOM) as PL.
    pose proof (head_len_eq (la_rseq la) argv envp) as HL.
    pose proof (auxv_words_length la ph entry sp top argv envp execfn uid gid hw) as AL.
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length, argv_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length, envp_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length, AL in B.
    apply bytes_at_app in B. destruct B as [B6 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B7 B]. rewrite length_at_random_bytes in B.
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B9 B].
    apply bytes_at_app in B. destruct B as [B10 B].
    unfold envp_addr, auxv_addr, rnd_addr, xfn_base, env_base, str_base, argc, envc in *.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split; [exact B1|].
      rewrite u64s_length, argv_ptrs_length. apply (bytes_at_eqa _ _ _ _ B2). lia.
    - apply (proj2 (bytes_at_app segs m _ _ _)). split; [apply (bytes_at_eqa _ _ _ _ B3); lia|].
      rewrite u64s_length, envp_ptrs_length. apply (proj2 (bytes_at_app segs m _ _ _)).
      split; [apply (bytes_at_eqa _ _ _ _ B4); lia|].
      rewrite length_le8. apply (bytes_at_eqa _ _ _ _ B5). lia.
    - apply (bytes_at_eqa _ _ _ _ B5). lia.
    - apply (bytes_at_eqa _ _ _ _ B7). lia.
    - apply (bytes_at_eqa _ _ _ _ B9). lia.
    - apply (bytes_at_eqa _ _ _ _ B10). lia.
    - apply (bytes_at_eqa _ _ _ _ B). lia.
  Qed.

  Lemma img_argv_string : forall i s, nth_error argv i = Some s ->
    exists p, nth_error AP i = Some (Z_to_bv 64 p) /\ (str_base top argv envp execfn <= p)%Z /\
      (p + Z.of_nat (length s) + 1 <= env_base top argv envp execfn)%Z /\ bytes_at segs m p (s ++ [Z_to_bv 8 0]).
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv (str_base top argv envp execfn) i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (str_base top argv envp execfn + off)%Z. split. { unfold argv_ptrs. rewrite nth_error_map, Hp. reflexivity. }
    split; [lia|]. split. { unfold env_base. lia. }
    destruct img_pieces as (_ & _ & _ & _ & _ & B6 & _).
    pose proof (flatten_strings_length argv).
    pose proof (bytes_at_slice m (str_base top argv envp execfn) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as B.
    rewrite Hf in B. replace (str_base top argv envp execfn + Z.of_nat (Z.to_nat off))%Z with (str_base top argv envp execfn + off)%Z in B by lia.
    exact B.
  Qed.

  (* An argv string with the bytes after its NUL up to the next 8-byte
     boundary: the strings sit under the eight-byte slot below [top], so
     those bytes are always inside the block. *)
  Lemma img_argv_cstring : forall i s, nth_error argv i = Some s ->
    exists p slack, nth_error AP i = Some (Z_to_bv 64 p) /\ (str_base top argv envp execfn <= p)%Z /\
      (p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length img))%Z /\
      bytes_at segs m p (s ++ Z_to_bv 8 0 :: slack) /\
      ((- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv (str_base top argv envp execfn) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (img_length la ph entry sp top argv envp execfn uid gid hw draw GEOM) as BL. pose proof (flatten_strings_length argv) as L1.
    pose proof (lsb_eq argv envp execfn) as LE.
    pose proof (str_base_ge _ _ _ _ _ _ GEOM) as SB. pose proof (head_len_ge (la_rseq la) argv envp) as HG.
    pose proof (total_arg_bytes_nonneg envp) as TE.
    unfold argc, envc in HG.
    set (p := (str_base top argv envp execfn + off)%Z).
    set (e := (p + Z.of_nat (length s) + 1)%Z).
    set (k := ((- e) mod 8)%Z).
    assert (HK : (0 <= k < 8)%Z) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : (usp <= p /\ e + k <= usp + Z.of_nat (length img))%Z).
    { subst p e k. unfold str_base in *. split; lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) img)).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) img)) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [lia|]. split; [| lia].
    destruct img_pieces as (_ & _ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice m (str_base top argv envp execfn) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base top argv envp execfn + Z.of_nat (Z.to_nat off))%Z with p in BS by (subst p; lia).
    pose proof (bytes_at_slice m usp img (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp)))%Z with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0])))%Z in BK
      by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app segs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.

End Pieces.
End WithSegs.

(* The sixteen AT_RANDOM bytes as the canary word and the secret word. *)
Lemma testbit_bv_wrap : forall n z i, (0 <= i)%Z ->
  Z.testbit (bv_wrap n z) i = if (i <? Z.of_N n)%Z then Z.testbit z i else false.
Proof.
  intros n z i Hi. unfold bv_wrap, bv_modulus.
  destruct (Z.ltb_spec i (Z.of_N n)).
  - apply Z.mod_pow2_bits_low. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma extract8_via64 : forall (r : bv 128) (h k : N), (k + 8 <= 64)%N ->
  bv_extract (h + k) 8 r = Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (bv_extract h 64 r)))) (Z.of_N k)).
Proof.
  intros r h k Hk. apply bv_eq. rewrite Z_to_bv_bv_unsigned. rewrite !bv_extract_unsigned, Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi.
  rewrite !testbit_bv_wrap, !Z.shiftr_spec, testbit_bv_wrap, Z.shiftr_spec by lia.
  change (Z.of_N 8) with 8%Z. destruct (Z.ltb_spec i 8); [|reflexivity].
  replace (i + Z.of_N k <? Z.of_N 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
Qed.

Definition draw_canary (d : EntryDraw) : Z := bv_unsigned (bv_extract 0 64 (ed_random d)).
Definition draw_secret (d : EntryDraw) : Z := bv_unsigned (bv_extract 64 64 (ed_random d)).

Lemma draw_canary_range : forall d, (0 <= draw_canary d < 2^64)%Z.
Proof. intros d. unfold draw_canary. pose proof (bv_unsigned_in_range 64 (bv_extract 0 64 (ed_random d))) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
Lemma draw_secret_range : forall d, (0 <= draw_secret d < 2^64)%Z.
Proof. intros d. unfold draw_secret. pose proof (bv_unsigned_in_range 64 (bv_extract 64 64 (ed_random d))) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma at_random_bytes_split : forall r : bv 128,
  at_random_bytes r = le8 (Z_to_bv 64 (bv_unsigned (bv_extract 0 64 r))) ++ le8 (Z_to_bv 64 (bv_unsigned (bv_extract 64 64 r))).
Proof.
  intros r. unfold at_random_bytes, le8, word_to_le_bytes. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
  rewrite (extract8_via64 _ 0 0), (extract8_via64 _ 0 8), (extract8_via64 _ 0 16), (extract8_via64 _ 0 24),
          (extract8_via64 _ 0 32), (extract8_via64 _ 0 40), (extract8_via64 _ 0 48), (extract8_via64 _ 0 56),
          (extract8_via64 _ 64 0), (extract8_via64 _ 64 8), (extract8_via64 _ 64 16), (extract8_via64 _ 64 24),
          (extract8_via64 _ 64 32), (extract8_via64 _ 64 40), (extract8_via64 _ 64 48), (extract8_via64 _ 64 56) by lia.
  cbn [Z.of_N N.add Pos.add]. rewrite !Z.shiftr_0_r. reflexivity.
Qed.

Definition rnd_bytes (d : EntryDraw) : list byte := at_random_bytes (ed_random d).
Lemma rnd_bytes_length : forall d, length (rnd_bytes d) = 16%nat.
Proof. reflexivity. Qed.

Lemma rnd_bytes_split : forall d,
  rnd_bytes d = le8 (Z_to_bv 64 (draw_canary d)) ++ le8 (Z_to_bv 64 (draw_secret d)).
Proof. intros d. apply at_random_bytes_split. Qed.

Definition entry_atop (en : ExecEntry) : Z := (bv_unsigned (en_sp en) - stack_max_size)%Z.
Definition entry_secret (en : ExecEntry) : Z := draw_secret (en_draw en).
Definition entry_canary (en : ExecEntry) : Z := draw_canary (en_draw en).



(* ------------------------------------------------------------------------- *)
(* The launch conjunct, read as arithmetic.  [launch_sp_le_top] ...          *)
(* [stack_window_lo_valid] are the model's own lemmas (Common/StepTac.v and   *)
(* Common/StoreOk.v at 08b1429), copied here because this library does not   *)
(* vendor those two files.                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma geom_of_launch : forall v inp (sp brk mbase : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  geom_ok (kb_rseq (in_kernel inp)) sp (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp).
Proof.
  intros v inp sp brk mbase draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi. unfold geom_ok, head_len, lsb.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)))
    16 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma top_of_launch : forall inp (sp brk mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned (ed_top draw) <= sp_window_hi)%Z.
Proof.
  intros inp sp brk mbase draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as ((_ & Htop & _) & _ & _). exact Htop.
Qed.

Lemma block_head_size_le : forall rseq argv envp,
  (Z.of_nat (block_head_size rseq argv envp)
   <= 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 512)%Z.
Proof.
  intros rseq argv envp.
  unfold block_head_size, block_items, auxv_size, auxv_count.
  pose proof (Nat.mod_upper_bound
                (length argv + length envp + 3) 2 ltac:(lia)).
  destruct rseq; lia.
Qed.

Lemma launch_sp_le_top : forall inp (top sp : word),
  valid_launch_sp top inp sp ->
  (bv_unsigned sp <= bv_unsigned top)%Z.
Proof.
  intros inp top sp [_ [_ Hhi]].
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

Lemma launch_top_minus_sp : forall inp (top sp : word),
  valid_launch inp ->
  valid_launch_sp top inp sp ->
  (bv_unsigned top - bv_unsigned sp <= 2101782)%Z.
Proof.
  intros inp top sp [_ Hb] [_ [Hlo _]].
  unfold launch_bytes, e2big_limit in Hb.
  unfold launch_sp_lo, align_down16 in Hlo.
  pose proof (block_head_size_le (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))
     - 4095) 16 ltac:(lia)).
  lia.
Qed.

Lemma page_round_up_Z_fixed : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

Lemma mmap_gap_sv48 : forall kb,
  mmap_gap Sv48 kb
  = (let g := (stack_max_size + (stack_guard_gap_bytes kb
                 + if kb_aslr kb then stack_rnd_max else 0))%Z in
     if (g <? mmap_min_gap)%Z then mmap_min_gap else g).
Proof.
  intros kb. pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  unfold mmap_gap. cbv zeta.
  rewrite Z.mod_small
    by (unfold two_pow_64, stack_max_size, stack_rnd_max;
        destruct (kb_aslr kb); lia).
  assert (Hmax : mmap_max_gap Sv48 = 117281240296105%Z)
    by (vm_compute; reflexivity).
  rewrite !Hmax.
  unfold mmap_min_gap in *. rewrite !Z.gtb_ltb.
  destruct (kb_aslr kb); cbv beta iota delta [andb];
  [ destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + stack_rnd_max))%Z
      eqn:Ein
  | destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + 0))%Z
      eqn:Ein ];
  try apply Z.ltb_lt in Ein; try apply Z.ltb_ge in Ein;
  cbv beta iota delta [andb];
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota delta [andb]);
  unfold stack_max_size, stack_rnd_max in *; lia.
Qed.

Lemma mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold stack_guard_gap_bytes, mmap_min_gap, stack_max_size,
    stack_rnd_max, page_size.
  destruct (_ <? _)%Z;
    [ replace (128 * 1024 * 1024)%Z with (4096 * 32768)%Z by reflexivity;
      apply H4096 |].
  destruct (kb_aslr kb);
    [ replace (8 * 1024 * 1024
               + (4096 * stack_guard_gap_pages kb + 1073737728))%Z
        with (4096 * (264191 + stack_guard_gap_pages kb))%Z by lia
    | replace (8 * 1024 * 1024 + (4096 * stack_guard_gap_pages kb + 0))%Z
        with (4096 * (2048 + stack_guard_gap_pages kb))%Z by lia ];
    apply H4096.
Qed.

Lemma stack_window_lo_ge_sp : forall inp (sp brk0 mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (bv_unsigned sp - stack_max_size
   <= stack_window_lo (in_kernel inp) mbase draw)%Z.
Proof.
  intros inp sp brk0 mbase draw (_ & Hsp & _).
  pose proof (launch_sp_le_top inp (ed_top draw) sp Hsp).
  unfold stack_window_lo.
  apply Z.le_trans with (bv_unsigned (ed_top draw) - stack_max_size)%Z;
    [lia | apply Z.le_max_l].
Qed.

Lemma launch_base_gap_le : forall kb mbase,
  valid_launch_base Sv48 kb mbase ->
  (bv_unsigned mbase + stack_guard_gap_bytes kb
   <= va_stack_top Sv48
      - (if kb_aslr kb then 0x407ff000 else 8 * 1024 * 1024))%Z.
Proof.
  intros kb mbase (r & Hr & _ & _ & Heq).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  rewrite Heq. unfold mmap_base_of.
  assert (Hdiv : (page_size
                  | va_stack_top Sv48 - mmap_gap Sv48 kb - page_size * r)%Z).
  { apply Z.divide_sub_r; [apply Z.divide_sub_r|].
    - exists 34359738368%Z. vm_compute. reflexivity.
    - apply Z.mod_divide; [unfold page_size; lia|]. apply mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite page_round_up_Z_fixed
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold mmap_min_gap, va_stack_top, sp_window_hi, stack_max_size,
    stack_rnd_max, page_size in *.
  destruct (kb_aslr kb); cbv beta iota;
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota);
  lia.
Qed.

(* Both floors of the zero window are at least 6144513 bytes below [sp]
   for every launch the fifth conjunct of [Run.valid_entry_va] admits. *)
Lemma stack_window_lo_valid : forall inp (sp brk0 mbase : word) draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (stack_window_lo (in_kernel inp) mbase draw
   <= bv_unsigned sp + 2244095 - stack_max_size)%Z.
Proof.
  intros inp sp brk0 mbase draw Hlaunch (Htop & Hsp & Hbase).
  pose proof (launch_top_minus_sp inp (ed_top draw) sp Hlaunch Hsp) as Hd.
  pose proof (launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  destruct Htop as (_ & Hhi & Hlo).
  unfold stack_window_lo, stack_max_size,
    va_stack_top, sp_window_hi, stack_rnd_max, page_size in *.
  destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo;
    apply Z.max_lub; lia.
Qed.
End InitMem.

Module Str_cpy.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_CB_split_at : forall segs m A n bs k, (k <= n)%nat ->
  rw_cells segs m A [CB n bs] ->
  rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k)%nat (skipn k bs)].
Proof.
  intros segs m A n bs k Hk H.
  pose proof (rw_cells_CB_length segs m A n bs H) as L.
  pose proof (rw_cells_split_CB segs m A [] n bs [] [k; (n - k)%nat] H ltac:(cbn; lia)) as H2.
  cbn [mk_CB_cells app] in H2.
  apply (proj1 (rw_cells_app segs m A [_] _)) in H2. destruct H2 as [Ha Hb].
  cbn [cells_size csize Nat.add] in Hb. rewrite Nat.add_0_r in Hb.
  split; [exact Ha|].
  replace (skipn k bs) with (firstn (n - k) (skipn k bs)); [exact Hb|].
  apply firstn_all2. rewrite skipn_length. lia.
Qed.

Lemma rw_cells_CB_join : forall segs m A k1 bs1 k2 bs2,
  rw_cells segs m A [CB k1 bs1] -> rw_cells segs m (A + Z.of_nat k1) [CB k2 bs2] ->
  rw_cells segs m A [CB (k1 + k2)%nat (bs1 ++ bs2)].
Proof.
  intros segs m A k1 bs1 k2 bs2 H1 H2.
  pose proof (rw_cells_CB_length segs m A k1 bs1 H1) as L1.
  pose proof (rw_cells_CB_length segs m _ k2 bs2 H2) as L2.
  assert (H : rw_cells segs m A ([CB k1 bs1] ++ [CB k2 bs2])).
  { apply (proj2 (rw_cells_app segs m A [_] [_])). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  pose proof (rw_cells_merge segs m A [] ([CB k1 bs1] ++ [CB k2 bs2]) []) as M.
  rewrite app_nil_r in M. cbn [app cells_size cells_bytes csize cbytes] in M.
  rewrite app_nil_r, Nat.add_0_r in M. apply M. exact H.
Qed.

Lemma le8_ld : forall w : list byte, length w = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word w)) = w.
Proof.
  intros w Hl. unfold le8, word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (le_val_range (map bv_unsigned w) (bytes_ok_map w)) as Hr. rewrite length_map, Hl in Hr.
  rewrite bytes_le_to_Z_le_val in *.
  change (256 ^ Z.of_nat 8) with (bv_modulus 64) in Hr.
  rewrite !(bv_wrap_small 64 (le_val _)) by lia.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma firstn_add_split : forall {X} (l : list X) p k, firstn (p + k) l = firstn p l ++ firstn k (skipn p l).
Proof.
  intros X l p k. revert l. induction p as [|p IH]; intros [|x l]; cbn; try reflexivity.
  - now destruct k.
  - rewrite IH. reflexivity.
Qed.

Lemma upd_bytes_prefix : forall (bs buf xs : list byte) (p : nat),
  firstn p bs = firstn p buf -> firstn (length xs) (skipn p buf) = xs -> (p + length xs <= length bs)%nat ->
  (p + length xs <= length buf)%nat ->
  firstn (p + length xs) (upd_bytes bs p xs) = firstn (p + length xs) buf.
Proof.
  intros bs buf xs p Hp Hx Hl Hlb. unfold upd_bytes.
  assert (Lp : length (firstn p bs) = p) by (rewrite firstn_length; lia).
  rewrite firstn_app, Lp, firstn_all2 by lia. replace (p + length xs - p)%nat with (length xs) by lia.
  rewrite firstn_app_exact.
  rewrite firstn_add_split, Hp, Hx. reflexivity.
Qed.
End Str_cpy.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ms_facts (A n i : Z) (k : nat) : Prop :=
  (0 <= i /\ i + Z.of_nat k <= n /\ 0 <= A /\ A + n <= 2^64)%Z.

Lemma ms_store_ok : forall segs m A n bs i k a,
  u8arr segs m A bs -> length bs = Z.to_nat n -> ms_facts A n i k -> a = wa (A + i) ->
  store_ok segs m a k = true.
Proof.
  intros segs m A n bs i k a ARR LEN (Hi & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m A bs i k a ARR); [lia | rewrite LEN; lia | exact Ha].
Qed.

Lemma ms_store : forall segs m0 m A n bs cb (Q : Z -> Prop) i k a,
  u8arr segs m A bs -> filled cb bs Q -> length bs = Z.to_nat n ->
  mem_inv segs m -> munch [(A, A + n)]%Z m0 m -> wmono segs m0 m ->
  ms_facts A n i k -> a = wa (A + i) ->
  u8arr segs (write_to_mem m a (repeat cb k)) A (upd_bytes bs (Z.to_nat i) (repeat cb k)) /\
  filled cb (upd_bytes bs (Z.to_nat i) (repeat cb k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z) /\
  length (upd_bytes bs (Z.to_nat i) (repeat cb k)) = Z.to_nat n /\
  mem_inv segs (write_to_mem m a (repeat cb k)) /\ munch [(A, A + n)]%Z m0 (write_to_mem m a (repeat cb k)) /\
  wmono segs m0 (write_to_mem m a (repeat cb k)).
Proof.
  intros segs m0 m A n bs cb Q i k a ARR FIL LEN MI MU WM MF Ha.
  assert (SOK : store_ok segs m a (length (repeat cb k)) = true).
  { rewrite repeat_length. eapply ms_store_ok; eauto. }
  destruct MF as (Hi & Hk & A0 & An). subst a.
  split; [|split; [|split; [|split; [|split]]]].
  - apply (u8arr_write_bytes segs m A bs i _ ARR); [lia|]. rewrite repeat_length, LEN. lia.
  - apply filled_updZ; [exact FIL | lia | rewrite LEN; lia].
  - rewrite upd_bytes_length; [exact LEN|]. rewrite repeat_length, LEN. lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | rewrite repeat_length; lia |]. cbn [inside]. left. rewrite repeat_length. lia.
  - apply wmono_write. exact WM.
Qed.

Ltac ms_arr_store MF bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs ?Q, LEN : length ?bs = Z.to_nat ?n,
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
    lazymatch type of MF with ms_facts _ _ ?i ?k =>
     let xs := eval cbv beta iota delta [repeat] in (repeat cb k) in
     let kz := eval vm_compute in (Z.of_nat k) in
     replace (write_to_mem m a bs0) with (write_to_mem m (wa (A + i)%Z) xs)
       by (apply (f_equal2 (write_to_mem m)); [ unfold wa; first [ reflexivity | f_equal; lia | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned ] | bytes_tac ]);
     let ARR' := fresh "ARR" in let FIL' := fresh "FIL" in let LEN' := fresh "LEN" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (ms_store segs m0 m A n bs cb Q i k _ ARR FIL LEN MI MU WM MF eq_refl)
       as (ARR' & FIL' & LEN' & MI' & MU' & WM');
     change (repeat cb k) with xs in ARR', FIL', LEN', MI', MU', WM';
     change (repeat cb k) with xs;
     cbv beta in FIL'; change (Z.of_nat k) with kz in FIL';
     clear ARR FIL LEN MI MU WM MF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m (wa (A + i)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat i) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename ARR' into ARR; rename FIL' into FIL; rename LEN' into LEN;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
    end
  end.

Ltac mst i k bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, LEN : length ?bs = Z.to_nat ?n |- _ =>
    let MF := fresh "MF" in let SOK := fresh "SOK" in
    assert (MF : ms_facts A n i k) by (unfold ms_facts; lia);
    pose proof (ms_store_ok segs m A n bs i k (wa (A + i)) ARR LEN MF eq_refl) as SOK; unfold wa in SOK;
    zstep; [ ms_arr_store MF bytes_tac | .. ]
  end.

