(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.cks Require Import CkMathCrc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit CrcAGlue CrcAMirror.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
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
      (x1 x5 x6 x7 x8 x9 x10 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned sp) lo A bs m m1 ->
    0 <= i <= Z.of_nat (length bs) -> 0 <= c < 2^32 ->
    res = Z.lxor (crc_bytes c (skipn (Z.to_nat i) bs)) M32 ->
    evtF asegs RNG (ck_postA 144 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (Z.of_nat (length bs) - i)) x13 x14
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 c))
          F (Z_to_bv 64 0x8140c) fc None m1 (seg_rom asegs)).

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
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr (135264 + ?x) 3 + 2147450880), 1%nat) =>
      lazymatch goal with H : shrng RNG 135264 ?hi |- _ => apply (shrng_acc RNG 135264 hi (135264 + x) H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr (136544 + ?x) 3 + 2147450880), 1%nat) =>
      lazymatch goal with H : shrng RNG 136544 ?hi |- _ => apply (shrng_acc RNG 136544 hi (136544 + x) H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), 1%nat) =>
      lazymatch goal with H : shrng RNG ?lo (?lo + Z.of_nat (length ?l)) |- _ =>
        apply (shrng_acc RNG lo (lo + Z.of_nat (length l)) a H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (2147450880 + Z.shiftr ?a 3 + ?j), 1%nat) =>
      lazymatch goal with H : shrng RNG ?lo (?lo + Z.of_nat (length ?l)) |- _ =>
        apply (shrng_acc_off RNG lo (lo + Z.of_nat (length l)) a j H); lia end
  | |- acc_in ?RNG (Z_to_bv 64 (135264 + ?x), ?n) =>
      lazymatch goal with H : rng RNG 65536 ?len |- _ => solve_acc_with H end
  | |- acc_in ?RNG (Z_to_bv 64 (136544 + ?x), ?n) =>
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

Lemma ctab_addr_range : forall i, 0 <= i < 256 -> 0 <= 135264 + 4 * i < 2 ^ 64.
Proof. intros i H. lia. Qed.
Lemma braid_addr_range : forall k i, 0 <= k < 4 -> 0 <= i < 256 -> 0 <= 136544 + 4 * (256 * k + i) < 2 ^ 64.
Proof. intros k i Hk H. lia. Qed.


Definition crcz_frameb (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP : Z) (v8 v16 v24 v32 : word) (m1 : amem) : Prop :=
  exists junk8, rw_cells asegs m1 (SP + -144)
    [CB 8 junk8; C8 v8; C8 v16; C8 v24; C8 v32; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition crcz_invb (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP lo A : Z) (bs : list Z)
    (v8 v16 v24 v32 : word) (m m1 : amem) : Prop :=
  crcz_frameb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP v8 v16 v24 v32 m1
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

Lemma crcz_invb_inv : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v8 v16 v24 v32 m m1,
  crcz_invb ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs v8 v16 v24 v32 m m1 ->
  crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs m m1.
Proof.
  intros until m1. intros ([j8 FR] & REST). split; [|exact REST].
  pose proof (rw_cells_merge asegs m1 (SP + -144) [] [CB 8 j8; C8 v8; C8 v16; C8 v24; C8 v32]
                [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as M.
  cbn [app cells_size csize Nat.add] in M. eexists. exact M.
Qed.

Lemma braid_idx_range : forall k i, 0 <= k < 4 -> 0 <= i < 256 -> 0 <= 256 * k + i < 1024.
Proof. intros. lia. Qed.
Lemma braid_wa : forall k i, Z_to_bv 64 (136544 + 4 * (256 * k + i)) = wa (ABRAID + 1024 * k + 4 * i).
Proof. intros. unfold wa, ABRAID. f_equal. lia. Qed.
Lemma k0_range : 0 <= 0 < 4. Proof. lia. Qed.
Lemma k1_range : 0 <= 1 < 4. Proof. lia. Qed.
Lemma k2_range : 0 <= 2 < 4. Proof. lia. Qed.
Lemma k3_range : 0 <= 3 < 4. Proof. lia. Qed.
