(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import CkTables CkModel CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit CrcAGlue CrcAMirror CrcA_zkit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition crcz_last_stmt (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo A : Z) (bs : list Z) : Prop :=
  forall (m1 : amem) (iL x0 x1 x2 x3 x4 n1 blks res : Z)
      (x1r x5 x6 x9 x10 x12 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 : word),
    crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned sp) lo A bs m m1 ->
    0 <= iL -> iL + 20 <= Z.of_nat (length bs) -> (A + iL) mod 4 = 0 ->
    0 <= x0 < 2^64 -> 0 <= x1 < 2^64 -> 0 <= x2 < 2^64 -> 0 <= x3 < 2^64 -> 0 <= x4 < 2^64 ->
    0 <= n1 < 2^64 -> 0 <= blks < 2^64 -> n1 - 20 * blks = Z.of_nat (length bs) - (iL + 20) ->
    res = Z.lxor (crc_bytes (braid_last [x0 mod 2^32; x1 mod 2^32; x2 mod 2^32; x3 mod 2^32; x4 mod 2^32]
                                        (firstn 20 (skipn (Z.to_nat iL) bs)))
                            (skipn (Z.to_nat (iL + 20)) bs)) M32 ->
    evtF asegs RNG (ck_postA 144 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
      (MS (mkR x1r (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 (Z_to_bv 64 n1) (Z_to_bv 64 x2) x9 x10 (Z_to_bv 64 (A + iL)) x12 (Z_to_bv 64 x1) (Z_to_bv 64 x4)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 blks) x29 (Z_to_bv 64 x3) (Z_to_bv 64 x0))
          F (Z_to_bv 64 0x81054) fc None m1 (seg_rom asegs)).

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
