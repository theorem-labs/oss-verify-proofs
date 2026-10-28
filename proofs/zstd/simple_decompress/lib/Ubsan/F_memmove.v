(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition memmove_entry := 0x35670%Z.

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mv_inv usegs (bv_unsigned a1) (bv_unsigned a0) (bv_unsigned a2) m m'.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis AB : (S + n <= 2^63 /\ D + n <= 2^63)%Z.

  Notation POST := (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  Notation INV m1 := (mv_inv usegs S D n m m1).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma rng : (0 <= S < 2^64 /\ 0 <= D < 2^64 /\ 0 <= n < 2^64)%Z.
  Proof.
    pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. pose proof (bv_unsigned_in_range 64 a2) as R2.
    unfold bv_modulus in *. cbn in R0, R1, R2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mm_ret : forall m1 x5 x11 x12 x13 x14 x15 x16 x17, INV m1 -> evt usegs POST (ST 0x356fc m1 x5 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x11 x12 x13 x14 x15 x16 x17 I. zstep. finish2.
  Qed.

  (* [comment removed for export] *)
  Ltac ldk P k bs :=
    lazymatch goal with I : mv_inv ?segs ?S0 ?D0 ?n0 ?m0 ?m1 |- _ =>
      let a := cur_mem_addr in
      let RD := fresh "RD" in let L := fresh "L" bs in
      destruct (mv_read segs S0 D0 n0 m0 m1 P k a I ltac:(lia) ltac:(lia) ltac:(addr_tac)) as [bs [L RD]];
      zstep; try clear RD
    end.
  Ltac stk_ P k :=
    lazymatch goal with I : mv_inv ?segs ?S0 ?D0 ?n0 ?m0 ?m1 |- _ =>
      let a := cur_mem_addr in
      let SOK := fresh "SOK" in
      pose proof (mv_store_ok segs S0 D0 n0 m0 m1 P k a I ltac:(lia) ltac:(lia) ltac:(addr_tac)) as SOK;
      zstep;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?a' ?xs) _) =>
        let I' := fresh "I" in
        pose proof (mv_store segs S0 D0 n0 m0 m1 P k xs a' I ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(addr_tac)) as I';
        clear I SOK;
        let m' := fresh "m" in remember (write_to_mem m1 a' xs) as m' eqn:Heqm; clear Heqm; try clear m1;
        rename I' into I
      end
    end.

  (* [comment removed for export] *)
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ eassumption | idtac ]; try (f_equal; lia); try lia;
    try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

  (* [comment removed for export] *)
  Lemma mm_fb : forall (k : nat) m1 (P : Z) x5 x11 xa2 xa3 xa4 x15 x16 x17,
    INV m1 -> (0 <= P)%Z -> (P + Z.of_nat k + 1 = n)%Z ->
    xa2 = Z_to_bv 64 (D + n) -> xa3 = Z_to_bv 64 (D + P) -> xa4 = Z_to_bv 64 (S + P) ->
    evt usegs POST (ST 0x356a8 m1 x5 x11 xa2 xa3 xa4 x15 x16 x17).
  Proof.
    pose proof rng as RNG.
    induction k as [|k IH]; intros m1 P x5 x11 xa2 xa3 xa4 x15 x16 x17 I HP HK -> -> ->.
    - ldk P 1%nat bs. zstep. zstep. stk_ P 1%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. use mm_ret.
    - ldk P 1%nat bs. zstep. zstep. stk_ P 1%nat. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ (P + 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_ft : forall m1 (P r : Z) x5 x11 xa2 xa3 xa4 x15 x16 x17,
    INV m1 -> (0 <= P)%Z -> (0 <= r)%Z -> (P + r = n)%Z ->
    xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) -> xa4 = Z_to_bv 64 (S + P) ->
    evt usegs POST (ST 0x356a0 m1 x5 x11 xa2 xa3 xa4 x15 x16 x17).
  Proof.
    pose proof rng as RNG.
    intros m1 P r x5 x11 xa2 xa3 xa4 x15 x16 x17 I HP Hr HPr -> -> ->.
    zstep. if_cases K; zify_cond K.
    - use mm_ret.
    - zstep. use (mm_fb (Z.to_nat (r - 1)) _ P).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_fwl : forall (q : nat) m1 (P r : Z) x5 xa1 xa2 xa3 xa4 x15 x16 x17,
    INV m1 -> (0 <= P)%Z -> (8 <= r)%Z -> (P + r = n)%Z -> (r - 8 < 8 * (Z.of_nat q + 1))%Z ->
    xa1 = Z_to_bv 64 7 -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) -> xa4 = Z_to_bv 64 (S + P) ->
    evt usegs POST (ST 0x357d0 m1 x5 xa1 xa2 xa3 xa4 x15 x16 x17).
  Proof.
    pose proof rng as RNG.
    induction q as [|q IH]; intros m1 P r x5 xa1 xa2 xa3 xa4 x15 x16 x17 I HP Hr HPr Hq -> -> -> ->.
    - ldk P 8%nat bs. zstep. stk_ P 8%nat. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. use (mm_ft _ (P + 8)%Z (r - 8)%Z).
    - ldk P 8%nat bs. zstep. stk_ P 8%nat. zstep. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ (P + 8)%Z (r - 8)%Z).
      + zstep. use (mm_ft _ (P + 8)%Z (r - 8)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_fw : forall m1 (P r : Z) x5 x11 xa2 xa3 xa4 x15 x16 x17,
    INV m1 -> (0 <= P)%Z -> (0 <= r)%Z -> (P + r = n)%Z ->
    xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) -> xa4 = Z_to_bv 64 (S + P) ->
    evt usegs POST (ST 0x357c4 m1 x5 x11 xa2 xa3 xa4 x15 x16 x17).
  Proof.
    pose proof rng as RNG.
    intros m1 P r x5 x11 xa2 xa3 xa4 x15 x16 x17 I HP Hr HPr -> -> ->.
    zstep. zstep. if_cases K; zify_cond K.
    - use (mm_ft _ P r).
    - zstep. use (mm_fwl (Z.to_nat r) _ P r).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_fa : forall (k : nat) m1 (P r : Z) x5 xa1 xa2 x13 x14 xa5 xa6 x17,
    INV m1 -> (0 <= P)%Z -> r = Z.of_nat k -> (P + r = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa5 = Z_to_bv 64 (D + P + 1) -> xa6 = Z_to_bv 64 (D + P) ->
    evt usegs POST (ST 0x35710 m1 x5 xa1 xa2 x13 x14 xa5 xa6 x17).
  Proof.
    pose proof rng as RNG.
    induction k as [|k IH]; intros m1 P r x5 xa1 xa2 x13 x14 xa5 xa6 x17 I HP Hr HPr -> -> -> ->.
    - zstep. if_cases K; zify_cond K; [| exfalso; lia]. use mm_ret.
    - zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. ldk P 1%nat bs. zstep. zstep. zstep. stk_ P 1%nat. zstep. zstep. zstep. zstep. if_cases K2.
      + use (IH _ (P + 1)%Z (r - 1)%Z).
      + zstep. use (mm_fw _ (P + 1)%Z (r - 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_bb : forall (k : nat) m1 (j : Z) x5 xa1 xa2 xa3 x14 x15 x16 x17,
    INV m1 -> j = Z.of_nat k -> (j < n)%Z ->
    xa1 = Z_to_bv 64 (S + j) -> xa2 = Z_to_bv 64 (- (j + 1)) -> xa3 = Z_to_bv 64 (D + j) ->
    evt usegs POST (ST 0x356e4 m1 x5 xa1 xa2 xa3 x14 x15 x16 x17).
  Proof.
    pose proof rng as RNG.
    induction k as [|k IH]; intros m1 j x5 xa1 xa2 xa3 x14 x15 x16 x17 I Hj Hn -> -> ->.
    - ldk j 1%nat bs. zstep. stk_ j 1%nat. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. use mm_ret.
    - ldk j 1%nat bs. zstep. stk_ j 1%nat. zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ (j - 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_bt : forall m1 (r : Z) x5 x12 xa3 x14 x15 x16 x17,
    INV m1 -> (0 <= r <= n)%Z -> xa3 = Z_to_bv 64 r ->
    evt usegs POST (ST 0x356d0 m1 x5 a1 x12 xa3 x14 x15 x16 x17).
  Proof.
    pose proof rng as RNG.
    intros m1 r x5 x12 xa3 x14 x15 x16 x17 I Hr ->.
    zstep. if_cases K; zify_cond K.
    - use mm_ret.
    - zstep. zstep. zstep. zstep. use (mm_bb (Z.to_nat (r - 1)) _ (r - 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_bwl : forall (q : nat) m1 (r : Z) x5 xa2 x13 xa4 xa5 xa6 x17,
    INV m1 -> (8 <= r <= n)%Z -> (r - 8 < 8 * (Z.of_nat q + 1))%Z ->
    xa2 = Z_to_bv 64 r -> xa4 = Z_to_bv 64 (S + -8) -> xa5 = Z_to_bv 64 (D + -8) -> xa6 = Z_to_bv 64 7 ->
    evt usegs POST (ST 0x3579c m1 x5 a1 xa2 x13 xa4 xa5 xa6 x17).
  Proof.
    pose proof rng as RNG.
    induction q as [|q IH]; intros m1 r x5 xa2 x13 xa4 xa5 xa6 x17 I Hr Hq -> -> -> ->.
    - zstep. ldk (r - 8)%Z 8%nat bs. zstep. zstep. stk_ (r - 8)%Z 8%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. use (mm_bt _ (r - 8)%Z).
    - zstep. ldk (r - 8)%Z 8%nat bs. zstep. zstep. stk_ (r - 8)%Z 8%nat. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ (r - 8)%Z).
      + zstep. use (mm_bt _ (r - 8)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_bw : forall m1 (r : Z) x5 xa2 x13 x14 x15 x16 x17,
    INV m1 -> (0 <= r <= n)%Z -> xa2 = Z_to_bv 64 r ->
    evt usegs POST (ST 0x35788 m1 x5 a1 xa2 x13 x14 x15 x16 x17).
  Proof.
    pose proof rng as RNG.
    intros m1 r x5 xa2 x13 x14 x15 x16 x17 I Hr ->.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. use (mm_bt _ r).
    - zstep. zstep. zstep. use (mm_bwl (Z.to_nat r) _ r).
  Qed.

  (* [comment removed for export] *)
  Lemma mm_ba : forall (k : nat) m1 (r : Z) x5 xa2 xa3 xa4 xa5 x16 x17,
    INV m1 -> r = Z.of_nat k -> (r <= n)%Z ->
    xa2 = Z_to_bv 64 (D + r + -1) -> xa3 = Z_to_bv 64 (- r) -> xa4 = Z_to_bv 64 (S + r + -1) -> xa5 = Z_to_bv 64 (D + r + -1) ->
    evt usegs POST (ST 0x35760 m1 x5 a1 xa2 xa3 xa4 xa5 x16 x17).
  Proof.
    pose proof rng as RNG.
    induction k as [|k IH]; intros m1 r x5 xa2 xa3 xa4 xa5 x16 x17 I Hr Hn -> -> -> ->.
    - zstep. if_cases K; zify_cond K; [| exfalso; lia]. use mm_ret.
    - zstep. if_cases K; zify_cond K; [exfalso; lia|].
      ldk (r - 1)%Z 1%nat bs. stk_ (r - 1)%Z 1%nat. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2.
      + use (IH _ (r - 1)%Z).
      + zstep. use (mm_bw _ (r - 1)%Z).
        apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
        clear - Hr Hn RNG AB. Z.div_mod_to_equations. lia.
  Qed.

  Hypothesis STD : stk usegs m D (D + n).
  Hypothesis RDS : rdbl usegs m S (S + n).
  Hypothesis MI : mem_inv usegs m.

  Lemma memmove_body : evt usegs POST (ST 0x35670 m t0 a1 a2 a3 a4 a5 a6 a7).
  Proof.
    pose proof rng as RNG.
    pose proof (mv_inv_init usegs S D n m STD RDS MI) as I.
    zstep. if_cases K0; zify_cond K0.
    { use mm_ret. }
    zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      zstep.
      assert (SEP : (S + n <= D \/ D + n <= S)%Z).
      { rewrite Z.shiftl_mul_pow2 in K1 by lia. change (2 ^ 1)%Z with 2%Z in K1. clear - K0 K1 RNG AB. Z.div_mod_to_equations. lia. }
      destruct (rdbl_bytes usegs m S (S + n) RDS ltac:(lia)) as (src & LEN & SRC).
      replace (S + n - S)%Z with n in LEN by lia.
      destruct (stk_carve usegs m D (D + n) (Z.to_nat n) STD ltac:(lia)) as (_ & junk & DST).
      replace (D + n - Z.of_nat (Z.to_nat n))%Z with D in DST by lia.
      eapply evt_mono; [eapply (memcpy_spec _ _ _ _ _ _ _ _ _ a0 a1 a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m src junk SRC LEN DST SEP MI)|].
      intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & DST' & SRC').
      do 15 eexists. split; [reflexivity|].
      split. { pose proof (stk_of_rw_cells usegs m' D _ DST') as ST'. cbn [cells_size csize Nat.add] in ST'. rewrite Nat.add_0_r, Z2Nat.id in ST' by lia. exact ST'. }
      split. { pose proof (rdbl_of_bytes_at usegs m' S src SRC') as R'. rewrite LEN, Z2Nat.id in R' by lia. exact R'. }
      split; [exact MI'|]. split; [exact MU| exact WM]. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. if_cases K4.
        * use (mm_bw m n).
        * zstep. zstep. zstep. zstep. zstep. use (mm_ba (Z.to_nat n) m n).
      + zstep. use (mm_bt m n).
    - (* [comment removed for export] *)
      zstep. if_cases K3.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K4.
        * zstep. zstep. use (mm_fw m 0%Z n).
        * zstep. zstep. use (mm_fa (Z.to_nat n) m 0%Z n).
      + zstep. zstep. use (mm_ft m 0%Z n).
  Qed.
End Proofs.

Lemma memmove_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned a1 + bv_unsigned a2 <= 2^63 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^63)%Z ->
  stk usegs m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2)%Z ->
  rdbl usegs m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2)%Z ->
  mem_inv usegs m ->
  evt usegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memmove_entry) fc None m (seg_rom usegs)).
Proof. intros. unfold memmove_entry. eapply memmove_body; eassumption. Qed.

(* [comment removed for export] *)
Definition memmove_reg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n B0 B1 R0 R1 : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' B0 B1 /\ rdbl usegs m' R0 R1.

Lemma memmove_reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n B0 B1 R0 R1 : Z),
  stk usegs m B0 B1 -> rdbl usegs m R0 R1 ->
  (B0 <= D /\ D + n <= B1 /\ R0 <= S /\ S + n <= R1 /\ 0 <= n /\ 0 <= D /\ 0 <= S /\ S + n <= 2^63 /\ D + n <= 2^63)%Z ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  evt usegs (memmove_reg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n B0 B1 R0 R1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memmove_entry) fc None m (seg_rom usegs)).
Proof.
  intros until R1. intros ST RD (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) MI -> -> ->.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  - eapply memmove_spec; rewrite ?ED, ?ES, ?EN.
    + split; lia.
    + pose proof ST as (S0 & S1 & _). destruct (stk_split usegs m B0 D B1 ST ltac:(lia)) as [_ ST2].
      destruct (stk_split usegs m D (D + n) B1 ST2 ltac:(lia)) as [ST3 _]. exact ST3.
    + eapply rdbl_sub; [exact RD| lia| lia].
    + exact MI.
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & I).
    rewrite ED, ES, EN in I. destruct I as (STD & RDS & MI' & MU & WM).
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split.
    + eapply stk_after_sub; [exact ST| exact MU| exact WM| exact STD].
    + eapply rdbl_after_sub; [exact RD| exact MU| apply rdbl_of_stk; exact STD].
Qed.
