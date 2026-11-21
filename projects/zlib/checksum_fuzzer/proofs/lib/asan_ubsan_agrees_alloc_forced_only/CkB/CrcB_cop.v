(* 1.4 pilot (2026-11-06): crc32_combine_op at the 1.4 both image (0x81b8c .. 0x81c00; the plain 1.4
   code), re-walked; crc32_combine_op_proofA keeps its 1.3.1 statement (crc32_combine_op_stmtA). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkA Require Import CrcAGlue.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkB Require Import CkBImg CkBTables CkBShadow CkBIface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* the 1.4 shift block's b update, as zstep leaves it *)
Lemma bstepA14 : forall b,
  Z.lxor (b ≫ 1) (Z.land (bv_signed (Z_to_bv 64 (b ≪ 63)) ≫ 63 mod 18446744073709551616) 3988292384) = bstep b.
Proof.
  intros b. change 18446744073709551616 with (2^64). rewrite sra63_odd. unfold bstep, POLY.
  destruct (Z.odd b); [reflexivity | rewrite Z.land_0_l, Z.lxor_0_r; reflexivity].
Qed.

Lemma bstepA14_range : forall b, 0 <= b < 2^32 -> 0 <= bstep b < 2^32.
Proof.
  intros b Hb. unfold bstep.
  assert (Hs : 0 <= b ≫ 1 < 2^32).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia|].
    apply (Z.le_lt_trans _ b); [apply Z.div_le_upper_bound; lia| lia]. }
  destruct (Z.odd b); [| exact Hs].
  apply lxor_range32; [exact Hs | unfold POLY; lia].
Qed.

Lemma landM32A14 : forall c, Z.land c 4294967295 = c mod 2^32.
Proof. intros c. change 4294967295 with (Z.ones 32). apply Z.land_ones. lia. Qed.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem).

  Notation POST res := (ck_leaf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res m).
  Notation ST pc x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* the exit: a0 := p ^ (c2 & 0xffffffff); ret *)
  Lemma cop14_exit : forall (c2 p res : Z) (x12 x14 x15 x16 x17 : word),
    0 <= c2 < 2^64 -> 0 <= p < 2^64 -> res = Z.lxor p (c2 mod 2^32) ->
    evtF asegs RNG (POST res)
         (ST 0x81c34 (Z_to_bv 64 4294967295) (Z_to_bv 64 c2) x12 (Z_to_bv 64 p) x14 x15 x16 x17).
  Proof.
    intros c2 p res x12 x14 x15 x16 x17 Hc Hp HR.
    zstep. zstep. zstep.
    setreg 10 (Z_to_bv 64 res) ltac:(f_equal; rewrite HR, landM32A14; reflexivity).
    finish.
  Qed.

  (* the multmodp loop from its test (0x81bd4): a2 = op, a3 = p, a4 = m, a5 = b, a6 = POLY, a7 scratch *)
  Lemma cop14_loop : forall (i : nat) (a b p c2 mreg res : Z) (x17 : word),
    (i <= 31)%nat -> 0 <= a < 2^64 -> a mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < 2^32 -> 0 <= p < 2^32 -> 0 <= c2 < 2^64 -> mreg = 2 ^ Z.of_nat i ->
    res = Z.lxor (mm_loop i a b p) (c2 mod 2^32) ->
    evtF asegs RNG (POST res)
         (ST 0x81c1c (Z_to_bv 64 4294967295) (Z_to_bv 64 c2) (Z_to_bv 64 a) (Z_to_bv 64 p) (Z_to_bv 64 mreg)
             (Z_to_bv 64 b) (Z_to_bv 64 3988292384) x17).
  Proof.
    induction i as [|i IH]; intros a b p c2 mreg res x17 Hi Ha Hanz Hb Hp Hc2 Hmi HR.
    - (* bit 0: the last one *)
      change (Z.of_nat 0 + 1) with 1 in Hanz. change (2 ^ 1) with 2 in Hanz. change (Z.of_nat 0) with 0 in Hmi.
      assert (Ht : Z.testbit a 0 = true).
      { rewrite Z.bit0_odd. rewrite Zmod_odd in Hanz. destruct (Z.odd a); [reflexivity | exfalso; apply Hanz; reflexivity]. }
      assert (E1 : Z.land mreg a = mreg) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
      assert (E2 : Z.land (mreg + -1) a = 0) by (rewrite Hmi; reflexivity).
      assert (Hmr : 0 <= mreg < 2^64) by (rewrite Hmi; cbn; lia). assert (Hmr1 : 0 <= mreg + -1 < 2^64) by (rewrite Hmi; cbn; lia).
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. rewrite E1, Hmi in K. cbn in K. lia. }
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      { exfalso. rewrite E2 in K2. lia. }
      apply cop14_exit; [lia | apply lxor_range64; lia |].
      rewrite HR, (mm_loop_exit 0 a) by (first [exact Ht | apply Z.mod_1_r]). reflexivity.
    - (* bit j = i + 1 *)
      set (j := S i) in *.
      assert (Hj : Z.of_nat j = Z.of_nat i + 1) by (subst j; lia).
      pose proof (pow2_le_31 (Z.of_nat j) ltac:(lia)) as Pj.
      pose proof (pow2_le_31 (Z.of_nat i) ltac:(lia)) as Pi.
      assert (Hp2' : 2 ^ Z.of_nat j = 2 * 2 ^ Z.of_nat i) by (rewrite Hj, Z.pow_add_r by lia; lia).
      pose proof (mod_pow2_succ a (Z.of_nat j) ltac:(lia)) as Hsplit.
      pose proof (Z.mod_pos_bound a (2 ^ Z.of_nat j) ltac:(lia)) as Hr3.
      assert (Hm' : mreg ≫ 1 = 2 ^ Z.of_nat i).
      { rewrite Hmi, Hp2', Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
        rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
      assert (E2 : Z.land (mreg + -1) a = a mod 2 ^ Z.of_nat j).
      { replace (mreg + -1) with (2 ^ Z.of_nat j - 1) by lia. apply land_ones_l. lia. }
      pose proof (bstepA14_range b Hb) as Hb'.
      assert (Hmr : 0 <= mreg < 2^64) by lia. assert (Hmr1 : 0 <= mreg + -1 < 2^64) by lia.
      (* the shift block, then the loop at bit i *)
      assert (NEXT : forall p' (x17' : word), 0 <= p' < 2^32 -> a mod 2 ^ Z.of_nat j <> 0 ->
                res = Z.lxor (mm_loop i a (bstep b) p') (c2 mod 2^32) ->
                evtF asegs RNG (POST res)
                     (ST 0x81c04 (Z_to_bv 64 4294967295) (Z_to_bv 64 c2) (Z_to_bv 64 a) (Z_to_bv 64 p')
                         (Z_to_bv 64 mreg) (Z_to_bv 64 b) (Z_to_bv 64 3988292384) x17')).
      { intros p' x17' Hp' Hnz HR'.
        zstep. zstep. zstep. zstep. zstep. zstep.
        rewrite Hm', bstepA14.
        apply IH; try lia; try (rewrite <- Hj; exact Hnz); try exact HR'. }
      zstep. zstep. if_cases K; zify_cond K.
      + (* bit j clear *)
        assert (Ht : Z.testbit a (Z.of_nat j) = false).
        { destruct (Z.testbit a (Z.of_nat j)) eqn:E; [|reflexivity]. exfalso.
          assert (E1 : Z.land mreg a = mreg) by (rewrite Hmi, land_pow2_l, E by lia; reflexivity).
          rewrite E1 in K. lia. }
        rewrite Ht in Hsplit.
        apply NEXT; [lia| lia|].
        rewrite HR, (mm_loop_skip i a) by exact Ht. reflexivity.
      + assert (Ht : Z.testbit a (Z.of_nat j) = true).
        { destruct (Z.testbit a (Z.of_nat j)) eqn:E; [reflexivity|]. exfalso.
          assert (E1 : Z.land mreg a = 0) by (rewrite Hmi, land_pow2_l, E by lia; reflexivity).
          rewrite E1 in K. lia. }
        zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
        * (* a lower bit left: shift, go on *)
          assert (Hnz : a mod 2 ^ Z.of_nat j <> 0) by (rewrite E2 in K2; exact K2).
          apply NEXT; [apply lxor_range32; lia| exact Hnz|].
          rewrite HR, (mm_loop_go i a) by assumption. reflexivity.
        * (* no lower bit left: exit *)
          assert (Hz : a mod 2 ^ Z.of_nat j = 0) by (rewrite E2 in K2; exact K2).
          apply cop14_exit; [lia | apply lxor_range64; lia |].
          rewrite HR, (mm_loop_exit j a) by assumption. reflexivity.
  Qed.

  (* crc32_combine_op from its entry (0x81b88), at op mod 2^32 <> 0 *)
  Lemma cop14_run : forall (crc1 crc2 op : Z) (x13 x14 x15 x16 x17 : word),
    0 <= crc1 < 2^32 -> 0 <= crc2 < 2^64 -> 0 <= op < 2^64 -> op mod 2^32 <> 0 ->
    evtF asegs RNG (POST (Z.lxor (mm_loop 31 op crc1 0) (crc2 mod 2^32)))
         (ST ACK_OP (Z_to_bv 64 crc1) (Z_to_bv 64 crc2) (Z_to_bv 64 op) x13 x14 x15 x16 x17).
  Proof.
    intros crc1 crc2 op x13 x14 x15 x16 x17 Hc1 Hc2 Hop Hnz. unfold ACK_OP.
    zstep. if_cases K; zify_cond K.
    { exfalso. apply Hnz. rewrite K. reflexivity. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (Z.mod_small crc1 4294967296) by lia.
    apply (cop14_loop 31 op crc1 0 crc2 2147483648); try lia; try reflexivity.
    all: change (2 ^ (Z.of_nat 31 + 1)) with (2^32); exact Hnz.
  Qed.
End P.

(* the 1.3.1 statement, at the 1.4 model *)
Theorem crc32_combine_op_proofA : crc32_combine_op_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         FR fc m crc1 crc2 op E0 E1 E2 Hc1 Hc2 Hop Hnz.
  subst a0 a1 a2.
  assert (Hop0 : op <> 0) by (intro E; subst op; apply Hnz; reflexivity).
  replace (crc32_combine_op crc1 crc2 op) with (Z.lxor (mm_loop 31 op crc1 0) (crc2 mod 2^32)).
  - apply cop14_run; assumption.
  - unfold crc32_combine_op, multmodp, M32. rewrite (proj2 (Z.eqb_neq op 0) Hop0), !landM32A14.
    rewrite (Z.mod_small crc1) by lia. reflexivity.
Qed.
