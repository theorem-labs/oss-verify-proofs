From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue RingBuf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_ex_base.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import R2X.

Lemma pick_fact : forall rho (F : list sprop) f, Forall (holds rho) F -> In f F -> holds rho f.
Proof. intros rho F f H Hin. exact (proj1 (Forall_forall _ _) H f Hin). Qed.

Lemma U_and : forall rho a b,
  bv_unsigned (eval rho (SAlu ALU_AND a b)) = Z.land (bv_unsigned (eval rho a)) (bv_unsigned (eval rho b)).
Proof. intros. cbn [eval]. unfold alu64, alu. rewrite bv_and_unsigned. reflexivity. Qed.

Lemma soff_IX4 : forall rho e, bv_unsigned (eval rho e) < 2 ^ 60 -> soff rho (IX4 e) = 4 * bv_unsigned (eval rho e).
Proof.
  intros rho e He. unfold soff. rewrite bv_signed_U. pose proof (U_IX4 rho e ltac:(lia)) as X. rewrite X.
  unfold Zsigned, H63v. pose proof (urange (eval rho e)).
  destruct (Z.ltb_spec (4 * bv_unsigned (eval rho e)) 9223372036854775808); lia.
Qed.

Lemma base_n : forall rho (F : list sprop), Forall (holds rho) (F ++ r2_base_facts) ->
  5 <= bv_unsigned (rw rho 13%positive) <= 2 ^ 20.
Proof.
  intros rho F HF. apply Forall_app in HF as [_ HB].
  unfold r2_base_facts in HB. apply Forall_app in HB as [HB _].
  apply Forall_cons_iff in HB as [H5 HB]. apply Forall_cons_iff in HB as [H6 _].
  cbn [holds eval r2_N] in *. rewrite lit_unsigned in H5, H6. change (5 mod 2 ^ 64) with 5 in H5.
  change (r2_two20 mod 2 ^ 64) with (2 ^ 20) in H6. lia.
Qed.

Lemma lget_put4 : forall (L : list (bv 8)) k v x,
  0 <= k -> 0 <= x -> 4 * k + 4 <= Z.of_nat (length L) ->
  lget (lput L (Z.to_nat (4 * k)) (enc_bytes 4 v)) x = if x =? k then bv_unsigned v mod 2 ^ 32 else lget L x.
Proof.
  intros L k v x Hk Hx HL.
  replace (Z.to_nat (4 * k)) with (4 * Z.to_nat k)%nat by lia.
  destruct (Z.eqb_spec x k) as [->|Hne].
  - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). apply bytes_le_to_Z_enc4.
  - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity.
Qed.

Lemma sel_val : forall rho,
  bv_unsigned (rw rho 123%positive) < bv_unsigned (rw rho 13%positive) ->
  bv_unsigned (rw rho 13%positive) <= 2 ^ 20 ->
  bv_unsigned (eval rho SEL) =
    if bv_unsigned (rw rho 123%positive) + 1 =? bv_unsigned (rw rho 13%positive) then 0
    else bv_unsigned (rw rho 123%positive) + 1.
Proof.
  intros rho HI Hn. unfold SEL.
  repeat rewrite ?U_and, ?U_add, ?U_sltu, ?U_sub, ?U_lit. cbn [eval]. unfold M64v.
  pose proof (urange (rw rho 13%positive)) as R13. pose proof (urange (rw rho 123%positive)) as R123.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  change (0 mod 18446744073709551616) with 0. change (1 mod 18446744073709551616) with 1.
  change ((-1) mod 18446744073709551616) with 18446744073709551615.
  rewrite (Z.mod_small (I + 1)) by lia.
  replace ((0 - n) mod 18446744073709551616) with (18446744073709551616 - n)
    by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
  destruct (Z.eqb_spec (I + 1) n) as [E|NE].
  - replace (18446744073709551616 - n + (I + 1)) with (0 + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. cbn. reflexivity.
  - rewrite (Z.mod_small (18446744073709551616 - n + (I + 1))) by lia.
    destruct (Z.ltb_spec (18446744073709551616 - n + (I + 1)) 1); [lia|].
    change ((0 + 18446744073709551615) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rem_prv_val : forall rho,
  5 <= bv_unsigned (rw rho 13%positive) <= 2 ^ 20 ->
  bv_unsigned (rw rho 123%positive) < bv_unsigned (rw rho 13%positive) ->
  bv_unsigned (eval rho REMP) =
    (bv_unsigned (rw rho 123%positive) + bv_unsigned (rw rho 13%positive) - 1) mod bv_unsigned (rw rho 13%positive).
Proof.
  intros rho Hn HI. unfold REMP. cbn [eval]. unfold mul_div.
  set (a := alu64 ALU_ADD (alu64 ALU_ADD (rw rho 13%positive) (Z_to_bv 64 (-1))) (rw rho 123%positive)).
  pose proof (urange (rw rho 13%positive)) as R13. pose proof (urange (rw rho 123%positive)) as R123.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  assert (Ha : bv_unsigned a = n - 1 + I).
  { subst a. rewrite !add_val, lit_unsigned. fold n I. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
    replace ((n + (2 ^ 64 - 1)) mod 2 ^ 64) with (n - 1).
    2:{ replace (n + (2 ^ 64 - 1)) with ((n - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
        rewrite Z.mod_small by lia. reflexivity. }
    apply Z.mod_small. lia. }
  rewrite !low32_umod. fold n. rewrite (Z.mod_small n) by lia.
  destruct (Z.eqb_spec n 0); [lia|].
  assert (HM : bv_unsigned (bv_modu (low32 a) (low32 (rw rho 13%positive))) = (n - 1 + I) mod n).
  { rewrite bv_modu_unsigned, !low32_umod, Ha. fold n. rewrite (Z.mod_small n) by lia.
    rewrite (Z.mod_small (n - 1 + I)) by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (n - 1 + I) n ltac:(lia)) as MB.
  rewrite sext64_32_small by (rewrite HM; lia). rewrite HM. f_equal. lia.
Qed.

Lemma test_r : forall rho,
  bv_unsigned (rw rho 123%positive) < bv_unsigned (rw rho 13%positive) ->
  bv_unsigned (rw rho 13%positive) <= 2 ^ 20 ->
  (holds rho TEST_r <-> bv_unsigned (rw rho 123%positive) + 1 <> bv_unsigned (rw rho 13%positive)).
Proof.
  intros rho HI Hn. unfold TEST_r, TESTV. rewrite holds_bne.
  repeat rewrite ?U_add, ?U_sub, ?U_lit. cbn [eval]. unfold M64v.
  pose proof (urange (rw rho 13%positive)) as R13. pose proof (urange (rw rho 123%positive)) as R123.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  change (0 mod 18446744073709551616) with 0. change (1 mod 18446744073709551616) with 1.
  change (2 mod 18446744073709551616) with 2.
  rewrite (Z.mod_small (I + 2)) by lia.
  replace ((0 - n) mod 18446744073709551616) with (18446744073709551616 - n)
    by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
  destruct (Z.lt_ge_cases (I + 2) n).
  - rewrite Z.mod_small by lia. lia.
  - replace (18446744073709551616 - n + (I + 2)) with ((I + 2 - n) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
