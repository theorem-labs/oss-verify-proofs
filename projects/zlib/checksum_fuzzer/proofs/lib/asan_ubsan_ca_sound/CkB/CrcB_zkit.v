(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.cks Require Import CkTables CkModel CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkA Require Import CrcAGlue CrcAMirror.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit CrcBGlue.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition crcz_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition crcz_framec (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP : Z) (m1 : amem) : Prop :=
  exists junk40, rw_cells asegs m1 (SP + -144)
    [CB 40 junk40; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition crcz_inv (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP lo A : Z) (bs : list Z) (m m1 : amem) : Prop :=
  crcz_framec ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP m1
  /\ stk asegs m1 lo (SP + -144)
  /\ munch [(SP - 144, SP)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
  /\ bytes_at asegs m1 A (zb bs).

Definition crcz_tail_stmt (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo A : Z) (bs : list Z) : Prop :=
  forall (m1 : amem) (i c res : Z)
      (x1 x5 x6 x7 x8 x9 x10 x13 x14 x16 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned sp) lo A bs m m1 ->
    0 <= i <= Z.of_nat (length bs) -> 0 <= c < 2^32 ->
    res = Z.lxor (crc_bytes c (skipn (Z.to_nat i) bs)) M32 ->
    evtF asegs RNG (ck_postA 144 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (Z.of_nat (length bs) - i)) x13 x14
               (Z_to_bv 64 c) x16 (Z_to_bv 64 2147450880) (Z_to_bv 64 135136) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x813b4) fc None m1 (seg_rom asegs)).

Lemma zx32_lit : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.

Lemma shrng_acc_off : forall RNG lo hi a j,
  shrng RNG lo hi -> lo <= a -> a + 8 * j < hi -> 0 <= j -> 0 <= lo ->
  acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr a 3 + j), 1%nat).
Proof.
  intros RNG lo hi a j H Ha Hj J0 L0. specialize (H ltac:(lia)).
  apply (rng_acc_litZ RNG (shad lo) (shad (hi - 1) + 1 - shad lo) _ 1%nat 1 H eq_refl ltac:(lia)).
  rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
  Z.div_mod_to_equations. lia.
Qed.

Lemma shiftr3_off : forall a j, 0 <= a -> Z.shiftr (a + 8 * j) 3 = Z.shiftr a 3 + j.
Proof. intros a j Ha. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.

Ltac crcz_acc_hint :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr (135136 + ?x) 3 + 2147450880), 1%nat) =>
      lazymatch goal with H : shrng RNG 135136 ?hi |- _ => apply (shrng_acc RNG 135136 hi (135136 + x) H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr (136416 + ?x) 3 + 2147450880), 1%nat) =>
      lazymatch goal with H : shrng RNG 136416 ?hi |- _ => apply (shrng_acc RNG 136416 hi (136416 + x) H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), 1%nat) =>
      lazymatch goal with H : shrng RNG ?lo (?lo + Z.of_nat (length ?l)) |- _ =>
        apply (shrng_acc RNG lo (lo + Z.of_nat (length l)) a H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (2147450880 + Z.shiftr ?a 3 + ?j), 1%nat) =>
      lazymatch goal with H : shrng RNG ?lo (?lo + Z.of_nat (length ?l)) |- _ =>
        apply (shrng_acc_off RNG lo (lo + Z.of_nat (length l)) a j H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (135136 + ?x), ?n) =>
      lazymatch goal with H : rng RNG 65536 ?len |- _ => solve_acc_with H end
  | |- acc_in ?RNG (Z_to_bv 64 (136416 + ?x), ?n) =>
      lazymatch goal with H : rng RNG 65536 ?len |- _ => solve_acc_with H end
  end.


Lemma bnez_sval_true : forall b : byte,
  negb (bv_eqb (Z_to_bv 64 (sval b)) (Z_to_bv 64 0)) = true -> sval b <> 0.
Proof.
  intros b H E. rewrite E in H. cbn in H. discriminate.
Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma ck_slow1 : forall a (b : byte),
  (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + 1 - 1 < sval b)) -> sval b <> 0 ->
  bv_lts (Z_to_bv 64 (Z.land a 7)) (Z_to_bv 64 (sval b)) = true.
Proof.
  intros a b CK NZ. unfold bv_lts. rewrite land7_mod.
  rewrite !signed_lit_small64 by (pose proof (sval_range b); Z.div_mod_to_equations; lia).
  apply Z.ltb_lt. destruct CK as [Z0|[_ C]]; [contradiction| lia].
Qed.

Lemma ck_slow4 : forall a (b : byte),
  (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + 3 < sval b)) -> sval b <> 0 ->
  bv_lts (Z_to_bv 64 (Z.land a 7 + 3)) (Z_to_bv 64 (sval b)) = true.
Proof.
  intros a b CK NZ. unfold bv_lts. rewrite land7_mod.
  rewrite !signed_lit_small64 by (pose proof (sval_range b); Z.div_mod_to_equations; lia).
  apply Z.ltb_lt. destruct CK as [Z0|[_ C]]; [contradiction| lia].
Qed.

Lemma ck_slow4' : forall a (b : byte),
  (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + 4 - 1 < sval b)) -> sval b <> 0 ->
  bv_lts (Z_to_bv 64 (Z.land a 7 + 3)) (Z_to_bv 64 (sval b)) = true.
Proof. intros a b CK NZ. apply ck_slow4; [|exact NZ]. destruct CK as [Z0|[C1 C2]]; [left; exact Z0| right; split; [exact C1| lia]]. Qed.

Ltac ck_fast U JOIN CK :=
  ck_join U JOIN;
  [ let K := fresh "K" in
    if_cases K;
    [ apply bnez_sval_true in K; ck_slow_steps;
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (if bv_lts (Z_to_bv 64 (Z.land ?a 7 + 3)) (Z_to_bv 64 (sval ?b)) then _ else _) _ _ _ _) =>
          first [ rewrite (ck_slow4 a b CK K) | rewrite (ck_slow4' a b CK K) ]; ck_done U
      | |- evtF _ _ _ (MS _ _ (if bv_lts (Z_to_bv 64 (Z.land ?a 7)) (Z_to_bv 64 (sval ?b)) then _ else _) _ _ _ _) =>
          rewrite (ck_slow1 a b CK K); ck_done U
      end
    | ck_done U ]
  | ].


Lemma bz_bzp : forall bs i, bz bs i = bzp bs i.
Proof. reflexivity. Qed.

Lemma Z_to_bv8_eqmod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

Lemma le4_wle : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  le4 (Z_to_bv 64 (wle b0 b1 b2 b3)) = [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2; Z_to_bv 8 b3].
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold le4, wle. rewrite unsigned_lit by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ (8 + 8 + 8)) with 16777216. change (2 ^ (8 + 8)) with 65536.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  f_equal; [apply Z_to_bv8_eqmod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_eqmod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_eqmod; Z.div_mod_to_equations; lia|].
  f_equal. apply Z_to_bv8_eqmod; Z.div_mod_to_equations; lia.
Qed.

Lemma ck_buf_read4 : forall m A bs (i : Z) a,
  bytes_at asegs m A (zb bs) -> bytes bs -> 0 <= i -> i + 4 <= Z.of_nat (length bs) -> a = wa (A + i) ->
  ov_read_bytes asegs m a 4 = Some (le4 (Z_to_bv 64 (wdp bs i))).
Proof.
  intros m A bs i a HB BF Hi Hl ->.
  rewrite (bytes_at_read asegs m A (zb bs) i 4 HB Hi) by (rewrite zb_length; lia).
  f_equal. rewrite <- zb_skipn, <- zb_firstn.
  do 4 (rewrite firstn_S_skipn by lia). cbn [firstn]. unfold wdp.
  rewrite le4_wle by (apply bzp_range; exact BF).
  unfold zb. cbn [map]. repeat (f_equal; try lia).
Qed.

Lemma zr_lit_8 : 0 <= 8. Proof. lia. Qed.
Lemma zr_lit_24 : 0 <= 24. Proof. lia. Qed.
Lemma zr_lit_6 : 0 <= 6. Proof. lia. Qed.
Lemma zr_lit_14 : 0 <= 14. Proof. lia. Qed.
Lemma zr_lit_2p32 : 0 < 4294967296 <= 2 ^ 64. Proof. lia. Qed.
Lemma zr_lit_255 : 0 <= 255 < 2 ^ 64. Proof. lia. Qed.
Lemma zr_lit_1020 : 0 <= 1020 < 2 ^ 64. Proof. lia. Qed.
Ltac pose_zr_lits :=
  pose proof zr_lit_8 as ZL8; pose proof zr_lit_2p32 as ZL32; pose proof zr_lit_255 as ZL255;
  pose proof zr_lit_24 as ZL24; pose proof zr_lit_6 as ZL6; pose proof zr_lit_14 as ZL14; pose proof zr_lit_1020 as ZL1020.

Lemma ctab_addr_range : forall i, 0 <= i < 256 -> 0 <= 135136 + 4 * i < 2 ^ 64.
Proof. intros i H. lia. Qed.
Lemma braid_addr_range : forall k i, 0 <= k < 4 -> 0 <= i < 256 -> 0 <= 136416 + 4 * (256 * k + i) < 2 ^ 64.
Proof. intros k i Hk H. lia. Qed.


Definition crcz_framel (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP : Z) (v0 : word) (m1 : amem) : Prop :=
  exists junk32, rw_cells asegs m1 (SP + -144)
    [C8 v0; CB 32 junk32; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition crcz_invl (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP lo A : Z) (bs : list Z)
    (v0 : word) (m m1 : amem) : Prop :=
  crcz_framel ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP v0 m1
  /\ stk asegs m1 lo (SP + -144)
  /\ munch [(SP - 144, SP)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
  /\ bytes_at asegs m1 A (zb bs).

Definition crcz_frameb (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP : Z) (v0 v8 v16 v24 v32 : word) (m1 : amem) : Prop :=
  rw_cells asegs m1 (SP + -144)
    [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition crcz_invb (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP lo A : Z) (bs : list Z)
    (v0 v8 v16 v24 v32 : word) (m m1 : amem) : Prop :=
  crcz_frameb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP v0 v8 v16 v24 v32 m1
  /\ stk asegs m1 lo (SP + -144)
  /\ munch [(SP - 144, SP)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
  /\ bytes_at asegs m1 A (zb bs).

Lemma rw_cells_CB8_C8 : forall m A pre bs post,
  rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre bs post [[Hwf Hb] Hw].
  assert (L : length bs = 8%nat).
  { apply cells_wf_app in Hwf. destruct Hwf as [_ [H _]]. exact H. }
  split; [split|].
  - apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite (le8_of_bytes bs L). exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Lemma crcz_invb_invl : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v0 v8 v16 v24 v32 m m1,
  crcz_invb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v0 v8 v16 v24 v32 m m1 ->
  crcz_invl ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v0 m m1.
Proof.
  intros until m1. intros (FR & REST). split; [|exact REST].
  pose proof (rw_cells_merge asegs m1 (SP + -144) [C8 v0] [C8 v8; C8 v16; C8 v24; C8 v32]
                [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as M.
  cbn [app cells_size csize Nat.add] in M. eexists. exact M.
Qed.

Lemma crcz_invl_inv : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v0 m m1,
  crcz_invl ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v0 m m1 ->
  crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs m m1.
Proof.
  intros until m1. intros ([j32 FR] & REST). split; [|exact REST].
  pose proof (rw_cells_merge asegs m1 (SP + -144) [] [C8 v0; CB 32 j32]
                [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as M.
  cbn [app cells_size csize Nat.add] in M. eexists. exact M.
Qed.

Lemma braid_idx_range : forall k i, 0 <= k < 4 -> 0 <= i < 256 -> 0 <= 256 * k + i < 1024.
Proof. intros. lia. Qed.
Lemma braid_wa : forall k i, Z_to_bv 64 (136416 + 4 * (256 * k + i)) = wa (ABRAID + 1024 * k + 4 * i).
Proof. intros. unfold wa, ABRAID. f_equal. lia. Qed.
Lemma k0_range : 0 <= 0 < 4. Proof. lia. Qed.
Lemma k1_range : 0 <= 1 < 4. Proof. lia. Qed.
Lemma k2_range : 0 <= 2 < 4. Proof. lia. Qed.
Lemma k3_range : 0 <= 3 < 4. Proof. lia. Qed.

Definition crcz_last_stmt (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo A : Z) (bs : list Z) : Prop :=
  forall (m1 : amem) (iL x0 x1 x2 x3 x4 n1 blks res : Z)
      (x1r x5 x6 x7 x8 x9 x10 x13 x14 x19 x22 x23 x24 x25 x26 x27 x28 x30 x31 : word),
    crcz_invl ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned sp) lo A bs (Z_to_bv 64 blks) m m1 ->
    0 <= iL -> iL + 20 <= Z.of_nat (length bs) -> (A + iL) mod 4 = 0 ->
    0 <= x0 < 2^64 -> 0 <= x1 < 2^64 -> 0 <= x2 < 2^64 -> 0 <= x3 < 2^64 -> 0 <= x4 < 2^64 ->
    0 <= n1 < 2^64 -> 0 <= blks < 2^64 -> n1 - 20 * blks = Z.of_nat (length bs) - (iL + 20) ->
    res = Z.lxor (crc_bytes (braid_last [x0 mod 2^32; x1 mod 2^32; x2 mod 2^32; x3 mod 2^32; x4 mod 2^32]
                                        (firstn 20 (skipn (Z.to_nat iL) bs)))
                            (skipn (Z.to_nat (iL + 20)) bs)) M32 ->
    evtF asegs RNG (ck_postA 144 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
      (MS (mkR x1r (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (A + iL)) (Z_to_bv 64 n1) x13 x14
               (Z_to_bv 64 x0) (Z_to_bv 64 x4) (Z_to_bv 64 2147450880) (Z_to_bv 64 135136) x19 (Z_to_bv 64 x2) (Z_to_bv 64 x1)
               x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 x3) x30 x31)
          F (Z_to_bv 64 0x80fc0) fc None m1 (seg_rom asegs)).

Lemma beqz_sval_false : forall b : byte,
  bv_eqb (Z_to_bv 64 (sval b)) (Z_to_bv 64 0) = false -> sval b <> 0.
Proof. intros b H E. rewrite E in H. cbn in H. discriminate. Qed.

Ltac ck_fast_z U JOIN CK :=
  ck_join U JOIN;
  [ let K := fresh "K" in
    if_cases K;
    [ ck_done U
    | apply beqz_sval_false in K; ck_slow_steps;
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (if bv_lts (Z_to_bv 64 (Z.land ?a 7 + 3)) (Z_to_bv 64 (sval ?b)) then _ else _) _ _ _ _) =>
          first [ rewrite (ck_slow4 a b CK K) | rewrite (ck_slow4' a b CK K) ]; ck_done U
      | |- evtF _ _ _ (MS _ _ (if bv_lts (Z_to_bv 64 (Z.land ?a 7)) (Z_to_bv 64 (sval ?b)) then _ else _) _ _ _ _) =>
          rewrite (ck_slow1 a b CK K); ck_done U
      end ]
  | ].

Lemma mulhu20_form : forall n, (n * 14757395258967641293) ≫ 64 = n * 14757395258967641293 / 18446744073709551616.
Proof. intros n. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma mulhu20_range : forall n, 0 <= n < 2^64 -> 0 <= n * 14757395258967641293 / 18446744073709551616 < 2 ^ 64.
Proof. intros n H. apply (div20_ranges n H). Qed.

Lemma div20_form : forall n, 0 <= n < 2^64 -> (n * 14757395258967641293 / 18446744073709551616) ≫ 4 = n / 20.
Proof. intros n H. apply (div20_magic n H). Qed.

Lemma braid_from_lanes : forall c bs i blks X0 X1 X2 X3 X4,
  0 <= i -> blks = (Z.of_nat (length bs) - i) / 20 -> 1 <= blks -> i + 20 * blks <= Z.of_nat (length bs) ->
  [X0 mod 2^32; X1 mod 2^32; X2 mod 2^32; X3 mod 2^32; X4 mod 2^32]
    = braid_state [c; 0; 0; 0; 0] (Z.to_nat (blks - 1)) (skipn (Z.to_nat i) bs) ->
  braid_from c (skipn (Z.to_nat i) bs)
  = (braid_last [X0 mod 2^32; X1 mod 2^32; X2 mod 2^32; X3 mod 2^32; X4 mod 2^32]
                (firstn 20 (skipn (Z.to_nat (i + 20 * (blks - 1))) bs)),
     skipn (Z.to_nat (i + 20 * (blks - 1) + 20)) bs).
Proof.
  intros c bs i blks X0 X1 X2 X3 X4 Hi Hb H1 Hl E. unfold braid_from.
  assert (ZL : Zlen (skipn (Z.to_nat i) bs) = Z.of_nat (length bs) - i) by (unfold Zlen; rewrite length_skipn; lia).
  rewrite ZL, <- Hb, <- E. unfold block. rewrite !skipn_skipn.
  replace (20 * Z.to_nat (blks - 1) + Z.to_nat i)%nat with (Z.to_nat (i + 20 * (blks - 1))) by lia.
  replace (Z.to_nat (20 * blks) + Z.to_nat i)%nat with (Z.to_nat (i + 20 * (blks - 1) + 20)) by lia.
  reflexivity.
Qed.

Lemma crc_pre_form : forall c, Z.lxor c 18446744073709551615 mod 4294967296 = crc_pre c.
Proof.
  intros c. unfold crc_pre, M32. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia.
  change 4294967296 with (2^32). apply Z.bits_inj'. intros n Hn.
  destruct (Z.ltb_spec n 32) as [L|L].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lxor_spec, Z.lnot_spec by lia.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.ones_spec_low by lia. apply xorb_true_r.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma crc_pre_range32 : forall c, 0 <= crc_pre c < 2^32.
Proof. intros c. apply crc_pre_range. Qed.

Lemma land3_mod : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.


Lemma ctab_addr_formB : forall y, 135136 + 4 * Z.land y 255 = 135136 + Z.land y 255 ≪ 2.
Proof. intros y. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. ring. Qed.

Lemma braid_addrB0 : forall y, 136416 + Z.land y 255 ≪ 2 = 136416 + 4 * (256 * 0 + bI0 y).
Proof. intros y. unfold bI0. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.
Lemma braid_addrB1 : forall y, 136416 + Z.land (y ≫ 6) 1020 + 1024 = 136416 + 4 * (256 * 1 + bI1 y).
Proof. intros y. unfold bI1. change 6 with (8 - 2). rewrite (land_1020_shiftr y 8) by lia. lia. Qed.
Lemma braid_addrB2 : forall y, 136416 + Z.land (y ≫ 14) 1020 + 2048 = 136416 + 4 * (256 * 2 + bI2 y).
Proof. intros y. unfold bI2. change 14 with (16 - 2). rewrite (land_1020_shiftr y 16) by lia. lia. Qed.
Lemma braid_addrB3 : forall y, 136416 + ((y mod 4294967296) ≫ 24) ≪ 2 + 3072 = 136416 + 4 * (256 * 3 + bI3 y).
Proof. intros y. unfold bI3. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia. Qed.

Lemma guard_bltu_dead : forall p k, 0 <= p -> p + k < 18446744073709551616 -> 0 < k ->
  ~ ((18446744073709551616 - k) mod 18446744073709551616 < p mod 18446744073709551616).
Proof. intros p k Hp Hk K0 C. rewrite !Z.mod_small in C by lia. lia. Qed.

Lemma guard_beq_m1 : forall p, 0 <= p < 18446744073709551615 -> bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 (-1)) = false.
Proof.
  intros p H. unfold bv_eqb. rewrite unsigned_lit by lia.
  change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. apply Z.eqb_neq. lia.
Qed.

Lemma guard_beq_m2 : forall p, 0 <= p < 18446744073709551614 -> bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 (-2)) = false.
Proof.
  intros p H. unfold bv_eqb. rewrite unsigned_lit by lia.
  change (bv_unsigned (Z_to_bv 64 (-2))) with 18446744073709551614. apply Z.eqb_neq. lia.
Qed.

Lemma guard_bltu_neg : forall k p, 0 < k <= 4096 -> 0 <= p -> p + k < 18446744073709551616 ->
  bv_ltu (Z_to_bv 64 (- k)) (Z_to_bv 64 p) = false.
Proof.
  intros k p Hk Hp H. unfold bv_ltu. rewrite (unsigned_lit p) by lia.
  replace (bv_unsigned (Z_to_bv 64 (- k))) with (18446744073709551616 - k).
  - apply Z.ltb_ge. lia.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    replace (- k) with (18446744073709551616 - k + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
Qed.

Lemma evtF_if_false : forall RNG Q R F (c : bool) a b fc rv m ro,
  c = false -> evtF asegs RNG Q (MS R F b fc rv m ro) -> evtF asegs RNG Q (MS R F (if c then a else b) fc rv m ro).
Proof. intros. subst c. assumption. Qed.

Lemma evtF_if_true : forall RNG Q R F (c : bool) a b fc rv m ro,
  c = true -> evtF asegs RNG Q (MS R F a fc rv m ro) -> evtF asegs RNG Q (MS R F (if c then a else b) fc rv m ro).
Proof. intros. subst c. assumption. Qed.
