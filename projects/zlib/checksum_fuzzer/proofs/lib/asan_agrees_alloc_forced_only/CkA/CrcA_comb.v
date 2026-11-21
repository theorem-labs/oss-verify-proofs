(* 1.4 pilot (2026-11-06): crc32_combine at the 1.4 asan image (0x81bfc .. 0x81d40; crc32_combine64 with
   crc32_combine_gen64, x2nmodp, multmodp and crc32_combine_op inlined, the ASan shadow check on the x2n_table load),
   re-walked; crc32_combine_proofA keeps its 1.3.1 statement (crc32_combine_stmtA). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkXt CkMultmodp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.CkA Require Import CkAImg CkATables CkAShadow CkAIface CrcAGlue CrcATac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Lemma bstepAC14 : forall b,
  Z.lxor (b ≫ 1) (Z.land (bv_signed (Z_to_bv 64 (b ≪ 63)) ≫ 63 mod 18446744073709551616) 3988292384) = bstep b.
Proof.
  intros b. change 18446744073709551616 with (2^64). rewrite sra63_odd. unfold bstep, POLY.
  destruct (Z.odd b); [reflexivity | rewrite Z.land_0_l, Z.lxor_0_r; reflexivity].
Qed.

Lemma bstepAC14_range : forall b, 0 <= b < 2^32 -> 0 <= bstep b < 2^32.
Proof.
  intros b Hb. unfold bstep.
  assert (Hs : 0 <= b ≫ 1 < 2^32).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia|].
    apply (Z.le_lt_trans _ b); [apply Z.div_le_upper_bound; lia| lia]. }
  destruct (Z.odd b); [| exact Hs].
  apply lxor_range32; [exact Hs | unfold POLY; lia].
Qed.

Lemma mm_loopAC14_range : forall i a b p, 0 <= b < 2^32 -> 0 <= p < 2^32 -> 0 <= mm_loop i a b p < 2^32.
Proof.
  induction i as [|i IH]; intros a b p Hb Hp; rewrite mm_loop_unfold; cbv zeta.
  - destruct (Z.testbit a (Z.of_nat 0)); cbn [andb]; [destruct (_ =? 0)|]; try apply lxor_range32; lia.
  - pose proof (lxor_range32 p b Hp Hb). pose proof (bstepAC14_range b Hb).
    destruct (Z.testbit a (Z.of_nat (S i))); cbn [andb]; [destruct (_ =? 0)|]; try lia; apply IH; lia.
Qed.

Lemma landM32AC14 : forall c, Z.land c 4294967295 = c mod 2^32.
Proof. intros c. change 4294967295 with (Z.ones 32). apply Z.land_ones. lia. Qed.

(* the 1.4 low-bit test: (m + 0xffffffff) & x, x zero-extended *)
Lemma land_mM32AC14 : forall mreg j x, 0 <= j <= 31 -> mreg = 2 ^ j -> 0 <= x < 2^32 ->
  Z.land (mreg + 4294967295) x = x mod 2 ^ j.
Proof.
  intros mreg j x Hj -> Hx. pose proof (pow2_le_31 j Hj) as P.
  assert (Ex : x = Z.land x (Z.ones 32)) by (rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite Ex at 1. rewrite (Z.land_comm x (Z.ones 32)), Z.land_assoc, (Z.land_ones (2 ^ j + 4294967295) 32) by lia.
  replace ((2 ^ j + 4294967295) mod 2 ^ 32) with (2 ^ j - 1).
  - apply land_ones_l. lia.
  - replace (2 ^ j + 4294967295) with ((2 ^ j - 1) + 1 * 2^32) by (change (2^32) with 4294967296; lia).
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* CrcATac's ck_join / ck_done over TWO registers: the 1.4 slow check writes t5 as well as the shadow byte's t4 *)
Ltac ck_join2 n1 n2 okpc :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      let p1 := eval vm_compute in (bv_key (Z_to_bv 5 n1)) in
      let p2 := eval vm_compute in (bv_key (Z_to_bv 5 n2)) in
      let H := fresh "CONT" in
      enough (H : forall y1 y2 : word, evtF segs RNG Q (MS (tset p2 y2 (tset p1 y1 R)) F (Z_to_bv 64 okpc) fc rv m ro));
      [ | let y1 := fresh "y" in let y2 := fresh "y" in intros y1 y2;
          let g := lazymatch goal with |- ?g => g end in
          let g' := eval cbv beta iota delta [tset mkR] in g in change g' ]
  end.

Ltac ck_done2 n1 n2 :=
  lazymatch goal with
  | CONT : forall y1 y2 : word, evtF _ _ _ _ |- _ =>
      let v1 := reg_val n1 in let v2 := reg_val n2 in exact (CONT v1 v2)
  end.

Lemma zx32_litAC14 : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.

Section BODY.
  Variables (RNG : footprint)
            (ra spw gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Hypothesis MI0 : mem_inv asegs m0.
  Hypothesis UX0 : unpoisoned m0 AX2N (AX2N + 128).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.

  (* the x2nmodp phase: t0 = the shadow offset, t2 = 2^31, a4 = 0xffffffff, a5 = 2^31, a6 = POLY, t3 = x2n_table *)
  Notation ST pc x6 x10 x11 x12 x13 x17 x29 x30 x31 :=
    (MS (mkR ra spw gp tp (Z_to_bv 64 2147450880) x6 (Z_to_bv 64 2147483648) s0 s1 x10 x11 x12 x13
             (Z_to_bv 64 4294967295) (Z_to_bv 64 2147483648) (Z_to_bv 64 3988292384) x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 141664) x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m0 (seg_rom asegs)).

  (* the combine_op phase: only a4 = 0xffffffff and a6 = POLY are fixed *)
  Notation STF pc x5 x6 x7 x10 x11 x12 x13 x15 x17 x28 x29 x30 x31 :=
    (MS (mkR ra spw gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 (Z_to_bv 64 4294967295) x15 (Z_to_bv 64 3988292384) x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m0 (seg_rom asegs)).

  (* x2nmodp's multmodp loop (test 0x81cac) back to the latch (0x81c50), the product in a7 *)
  Definition cmm_post (x6 x10 x11 x12 x13 : word) (res : Z) : machine_state -> Prop :=
    fun ms' => exists (P : Z) (x29 x30 x31 : word),
      ms' = ST 0x81ca0 x6 x10 x11 x12 x13 (Z_to_bv 64 P) x29 x30 x31 /\ P = res.

  Lemma comb_mm : forall (i : nat) (a b p mreg res : Z) (x6 x10 x11 x12 x31 : word),
    (i <= 31)%nat -> 0 <= a < 2^32 -> a mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < 2^32 -> 0 <= p < 2^32 -> mreg = 2 ^ Z.of_nat i -> res = mm_loop i a b p ->
    evtF asegs RNG (cmm_post x6 x10 x11 x12 (Z_to_bv 64 a) res)
         (ST 0x81cfc x6 x10 x11 x12 (Z_to_bv 64 a) (Z_to_bv 64 p) (Z_to_bv 64 mreg) (Z_to_bv 64 b) x31).
  Proof.
    induction i as [|i IH]; intros a b p mreg res x6 x10 x11 x12 x31 Hi Ha Hanz Hb Hp Hmi HR.
    - change (Z.of_nat 0 + 1) with 1 in Hanz. change (2 ^ 1) with 2 in Hanz. change (Z.of_nat 0) with 0 in Hmi.
      assert (Ht : Z.testbit a 0 = true).
      { rewrite Z.bit0_odd. rewrite Zmod_odd in Hanz. destruct (Z.odd a); [reflexivity | exfalso; apply Hanz; reflexivity]. }
      assert (E1 : Z.land mreg a = mreg) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
      assert (E2 : Z.land (mreg + 4294967295) a = 0)
        by (rewrite (land_mM32AC14 mreg 0 a ltac:(lia) Hmi Ha); apply Z.mod_1_r).
      assert (Hmr : 0 <= mreg < 2^64) by (rewrite Hmi; cbn; lia).
      assert (Hmr2 : 0 <= mreg + 4294967295 < 2^64) by (rewrite Hmi; cbn; lia).
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. rewrite E1, Hmi in K. cbn in K. lia. }
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      { exfalso. rewrite E2 in K2. lia. }
      zstep.
      apply evtF_done. unfold cmm_post. eexists (Z.lxor p b), _, _, _. split; [reflexivity|].
      rewrite HR, (mm_loop_exit 0 a) by (first [exact Ht | apply Z.mod_1_r]). reflexivity.
    - set (j := S i) in *.
      assert (Hj : Z.of_nat j = Z.of_nat i + 1) by (subst j; lia).
      pose proof (pow2_le_31 (Z.of_nat j) ltac:(lia)) as Pj.
      pose proof (pow2_le_31 (Z.of_nat i) ltac:(lia)) as Pi.
      assert (Hp2' : 2 ^ Z.of_nat j = 2 * 2 ^ Z.of_nat i) by (rewrite Hj, Z.pow_add_r by lia; lia).
      pose proof (mod_pow2_succ a (Z.of_nat j) ltac:(lia)) as Hsplit.
      pose proof (Z.mod_pos_bound a (2 ^ Z.of_nat j) ltac:(lia)) as Hr3.
      assert (Hm' : mreg ≫ 1 = 2 ^ Z.of_nat i).
      { rewrite Hmi, Hp2', Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
        rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
      assert (E2 : Z.land (mreg + 4294967295) a = a mod 2 ^ Z.of_nat j) by (apply land_mM32AC14; lia).
      pose proof (bstepAC14_range b Hb) as Hb'.
      assert (Hmr : 0 <= mreg < 2^64) by lia. assert (Hmr2 : 0 <= mreg + 4294967295 < 2^64) by lia.
      assert (NEXT : forall p' (x31' : word), 0 <= p' < 2^32 -> a mod 2 ^ Z.of_nat j <> 0 ->
                res = mm_loop i a (bstep b) p' ->
                evtF asegs RNG (cmm_post x6 x10 x11 x12 (Z_to_bv 64 a) res)
                     (ST 0x81ce4 x6 x10 x11 x12 (Z_to_bv 64 a) (Z_to_bv 64 p') (Z_to_bv 64 mreg) (Z_to_bv 64 b) x31')).
      { intros p' x31' Hp' Hnz HR'.
        zstep. zstep. zstep. zstep. zstep. zstep.
        rewrite Hm', bstepAC14.
        apply IH; try lia; try (rewrite <- Hj; exact Hnz); try exact HR'. }
      zstep. zstep. if_cases K; zify_cond K.
      + assert (Ht : Z.testbit a (Z.of_nat j) = false).
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
        * assert (Hnz : a mod 2 ^ Z.of_nat j <> 0) by (rewrite E2 in K2; exact K2).
          apply NEXT; [apply lxor_range32; lia| exact Hnz|].
          rewrite HR, (mm_loop_go i a) by assumption. reflexivity.
        * assert (Hz : a mod 2 ^ Z.of_nat j = 0) by (rewrite E2 in K2; exact K2).
          zstep.
          apply evtF_done. unfold cmm_post. eexists (Z.lxor p b), _, _, _. split; [reflexivity|].
          rewrite HR, (mm_loop_exit j a) by assumption. reflexivity.
  Qed.

  (* the x2nmodp loop from its odd test (0x81c5c) to 0x81cdc (n = 0), the result in a7 *)
  Definition cloop_post (x10 x11 : word) (res : Z) : machine_state -> Prop :=
    fun ms' => exists (P : Z) (x6 x12 x13 x29 x30 x31 : word),
      ms' = ST 0x81d2c x6 x10 x11 x12 x13 (Z_to_bv 64 P) x29 x30 x31 /\ P = res.

  Lemma comb_loop : forall (fuel : nat) (n k p res : Z) (x10 x11 x13 x29 x30 x31 : word),
    0 < n < 2 ^ Z.of_nat fuel -> n < 2^63 -> 0 <= k -> k + Z.of_nat fuel < 2^32 -> 0 <= p < 2^32 ->
    res = x2n_loop fuel n k p ->
    evtF asegs RNG (cloop_post x10 x11 res)
         (ST 0x81cac (Z_to_bv 64 k) x10 x11 (Z_to_bv 64 n) x13 (Z_to_bv 64 p) x29 x30 x31).
  Proof.
    induction fuel as [|f IH]; intros n k p res x10 x11 x13 x29 x30 x31 Hn Hf Hk Hkf Hp HR.
    { exfalso. change (2 ^ Z.of_nat 0) with 1 in Hn. lia. }
    assert (SH : 0 <= n ≫ 1 < 2 ^ Z.of_nat f).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
      replace (Z.of_nat (S f)) with (Z.of_nat f + 1) in Hn by lia. rewrite Z.pow_add_r in Hn by lia. change (2^1) with 2 in Hn.
      Z.div_mod_to_equations. lia. }
    assert (SH63 : n ≫ 1 < 2^63) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia).
    (* the latch (0x81c50): n >>= 1; k++; leave on n = 0 *)
    assert (LATCH : forall (P : Z) (x13' x29' x30' x31' : word), 0 <= P < 2^32 ->
              res = x2n_loop f (n ≫ 1) (k + 1) P ->
              evtF asegs RNG (cloop_post x10 x11 res)
                   (ST 0x81ca0 (Z_to_bv 64 k) x10 x11 (Z_to_bv 64 n) x13' (Z_to_bv 64 P) x29' x30' x31')).
    { intros P x13' x29' x30' x31' HP HR'.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      - apply evtF_done. unfold cloop_post. eexists P, _, _, _, _, _, _. split; [reflexivity|].
        rewrite HR', K2, x2n_loop_done. reflexivity.
      - apply IH; first [lia | exact HR']. }
    rewrite (x2n_loop_step f n k) in HR by lia.
    zstep. zstep. if_cases K1; zify_cond K1.
    - assert (OD : Z.odd n = false).
      { rewrite <- Z.bit0_odd. apply Z.bits_inj_iff in K1. specialize (K1 0). rewrite Z.land_spec, Z.bits_0 in K1.
        change (Z.testbit 1 0) with true in K1. rewrite andb_true_r in K1. exact K1. }
      rewrite OD in HR. apply LATCH; [exact Hp| exact HR].
    - assert (OD : Z.odd n = true).
      { destruct (Z.odd n) eqn:E; [reflexivity|]. exfalso. apply K1.
        apply Z.bits_inj'. intros b Hb. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.eq_dec b 0) as [->|NZ]; [rewrite Z.bit0_odd, E; reflexivity|].
        replace (Z.testbit 1 b) with false; [apply andb_false_r|]. symmetry. apply (testbit_high 1 1 b); lia. }
      rewrite OD in HR.
      set (idx := k mod 32) in *. assert (Hidx : 0 <= idx < 32) by (subst idx; apply Z.mod_pos_bound; lia).
      set (a := x2n idx) in *. pose proof (x2n_range idx) as Ha. fold a in Ha.
      assert (Hanz : a mod 2 ^ (Z.of_nat 31 + 1) <> 0) by (subst a; apply x2n_nz_mod; exact Hidx).
      zstep. zstep. zstep.
      setreg 13 (Z_to_bv 64 (141664 + 4 * idx))
        ltac:(f_equal; subst idx; rewrite Z.shiftl_mul_pow2 by lia; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; change (2^5) with 32; change (2^2) with 4; lia).
      destruct (unpoisoned_check_rd asegs m0 AX2N (AX2N + 128) (141664 + 4 * idx) 4 UX0
                  ltac:(unfold AX2N; lia) ltac:(unfold AX2N; lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK).
      unfold shad, ASHOFF in RD. replace (2147450880 + Z.shiftr (141664 + 4 * idx) 3) with (Z.shiftr (141664 + 4 * idx) 3 + 2147450880) in RD by lia.
      pose proof (sval_range b) as SR.
      pose proof (x2n_read m0 idx (Z_to_bv 64 (141664 + 4 * idx)) MI0 Hidx eq_refl) as RDT. fold a in RDT.
      zstep. zstep. zstep. rewrite sxb_sval.
      ck_join2 29 30 0x81cd0.
      { zstep. if_cases KS; zify_cond KS; [| ck_done2 29 30].
        zstep. zstep. zstep. if_cases KB; zify_lts KB; [ck_done2 29 30|].
        exfalso. Z.div_mod_to_equations. lia. }
      zstep. rewrite (zx32_litAC14 a Ha). zstep. zstep. zstep. zstep.
      eapply evtF_cut.
      { eapply (comb_mm 31%nat a p 0 2147483648); try lia; try reflexivity. }
      cbv beta. intros ms' (P & x29' & x30' & x31' & -> & HP).
      apply LATCH; [rewrite HP; apply mm_loopAC14_range; lia|].
      rewrite HR, HP. unfold multmodp. reflexivity.
  Qed.

  (* crc32_combine_op's multmodp loop (test 0x81d04) to the exit (0x81d1c), the product in a2 *)
  Definition cfin_post (x5 x6 x7 x11 x17 x28 x29 x30 x31 : word) (res : Z) : machine_state -> Prop :=
    fun ms' => exists (P : Z) (x10 x13 x15 : word),
      ms' = STF 0x81d6c x5 x6 x7 x10 x11 (Z_to_bv 64 P) x13 x15 x17 x28 x29 x30 x31 /\ P = res.

  Lemma comb_fin : forall (i : nat) (a b p mreg res : Z) (x5 x6 x7 x11 x13 x28 x29 x30 x31 : word),
    (i <= 31)%nat -> 0 <= a < 2^64 -> a mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < 2^32 -> 0 <= p < 2^32 -> mreg = 2 ^ Z.of_nat i -> res = mm_loop i a b p ->
    evtF asegs RNG (cfin_post x5 x6 x7 x11 (Z_to_bv 64 a) x28 x29 x30 x31 res)
         (STF 0x81d54 x5 x6 x7 (Z_to_bv 64 b) x11 (Z_to_bv 64 p) x13 (Z_to_bv 64 mreg) (Z_to_bv 64 a) x28 x29 x30 x31).
  Proof.
    induction i as [|i IH]; intros a b p mreg res x5 x6 x7 x11 x13 x28 x29 x30 x31 Hi Ha Hanz Hb Hp Hmi HR.
    - change (Z.of_nat 0 + 1) with 1 in Hanz. change (2 ^ 1) with 2 in Hanz. change (Z.of_nat 0) with 0 in Hmi.
      assert (Ht : Z.testbit a 0 = true).
      { rewrite Z.bit0_odd. rewrite Zmod_odd in Hanz. destruct (Z.odd a); [reflexivity | exfalso; apply Hanz; reflexivity]. }
      assert (E1 : Z.land mreg a = mreg) by (rewrite Hmi, land_pow2_l, Ht by lia; reflexivity).
      assert (E2 : Z.land (mreg + -1) a = 0) by (rewrite Hmi; reflexivity).
      assert (Hmr : 0 <= mreg < 2^64) by (rewrite Hmi; cbn; lia). assert (Hmr1 : 0 <= mreg + -1 < 2^64) by (rewrite Hmi; cbn; lia).
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. rewrite E1, Hmi in K. cbn in K. lia. }
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      { exfalso. rewrite E2 in K2. lia. }
      apply evtF_done. unfold cfin_post. eexists (Z.lxor p b), _, _, _. split; [reflexivity|].
      rewrite HR, (mm_loop_exit 0 a) by (first [exact Ht | apply Z.mod_1_r]). reflexivity.
    - set (j := S i) in *.
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
      pose proof (bstepAC14_range b Hb) as Hb'.
      assert (Hmr : 0 <= mreg < 2^64) by lia. assert (Hmr1 : 0 <= mreg + -1 < 2^64) by lia.
      assert (NEXT : forall p' (x13' : word), 0 <= p' < 2^32 -> a mod 2 ^ Z.of_nat j <> 0 ->
                res = mm_loop i a (bstep b) p' ->
                evtF asegs RNG (cfin_post x5 x6 x7 x11 (Z_to_bv 64 a) x28 x29 x30 x31 res)
                     (STF 0x81d3c x5 x6 x7 (Z_to_bv 64 b) x11 (Z_to_bv 64 p') x13' (Z_to_bv 64 mreg) (Z_to_bv 64 a) x28 x29 x30 x31)).
      { intros p' x13' Hp' Hnz HR'.
        zstep. zstep. zstep. zstep. zstep. zstep.
        rewrite Hm', bstepAC14.
        apply IH; try lia; try (rewrite <- Hj; exact Hnz); try exact HR'. }
      zstep. zstep. if_cases K; zify_cond K.
      + assert (Ht : Z.testbit a (Z.of_nat j) = false).
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
        * assert (Hnz : a mod 2 ^ Z.of_nat j <> 0) by (rewrite E2 in K2; exact K2).
          apply NEXT; [apply lxor_range32; lia| exact Hnz|].
          rewrite HR, (mm_loop_go i a) by assumption. reflexivity.
        * assert (Hz : a mod 2 ^ Z.of_nat j = 0) by (rewrite E2 in K2; exact K2).
          apply evtF_done. unfold cfin_post. eexists (Z.lxor p b), _, _, _. split; [reflexivity|].
          rewrite HR, (mm_loop_exit j a) by assumption. reflexivity.
  Qed.
End BODY.

(* the 1.3.1 statement, at the 1.4 model *)
Theorem crc32_combine_proofA : crc32_combine_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         Fr fc m lo crc1 crc2 len2 MI ST LOS KLO GOT SHB CKSH E0 E1 E2 Hc1 Hc2 Hlen RI RISH RSTK.
  subst a0 a1 a2. unfold ACK_COMBINE. unfold CK_COMBINE_STACK in *.

  pose proof (x2nmodp_range_any len2 3) as Hxr.
  assert (Hxnz : x2nmodp len2 3 mod 2 ^ 32 <> 0).
  { pose proof (x2nmodp_nz_any len2 3 ltac:(lia)) as H. exact H. }
  assert (Hx0 : x2nmodp len2 3 <> 0) by (intro E; apply Hxnz; rewrite E; reflexivity).
  assert (COMB : crc32_combine crc1 crc2 len2 = Z.lxor (mm_loop 31 (x2nmodp len2 3) crc1 0) (crc2 mod 2^32)).
  { unfold crc32_combine, crc32_combine64, crc32_combine_op, crc32_combine_gen64.
    rewrite (proj2 (Z.ltb_ge len2 0)) by lia. rewrite (proj2 (Z.eqb_neq _ 0) Hx0).
    unfold multmodp, M32. rewrite !landM32AC14, (Z.mod_small crc1) by lia. reflexivity. }
  rewrite COMB. clear COMB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (x2n_unpoisoned m CKSH) as UX.
  pose proof KLO as KLO'. unfold KHIGH in KLO'.
  carve_frame 16%nat ST.
  zstep. zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU1 : munch _ m m1 |- _ =>
      pose proof (unpoisoned_mu _ lo m m1 AX2N (AX2N + 128) UX MU1
                    ltac:(cbn; lia) ltac:(unfold AX2N, KHIGH in *; lia) KLO) as UX1
    end end.
  zstep. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* from 0x81ce0: p := 0; b := crc1 & 0xffffffff; the combine_op loop; the exit *)
  assert (TAIL : forall (P : Z) (x5 x6 x7 x12 x13 x28 x29 x30 x31 : word), P = x2nmodp len2 3 ->
            evtF asegs RNG (ck_postA 16 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc
                              (Z.lxor (mm_loop 31 (x2nmodp len2 3) crc1 0) (crc2 mod 2^32)) lo m)
                 (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 crc1) (Z_to_bv 64 crc2) x12 x13
                          (Z_to_bv 64 4294967295) (Z_to_bv 64 2147483648) (Z_to_bv 64 3988292384) (Z_to_bv 64 P)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     Fr (Z_to_bv 64 0x81d30) fc None m0 (seg_rom asegs))).
  { intros P x5 x6 x7 x12 x13 x28 x29 x30 x31 HP.
    pose proof Hxr as HPr. rewrite <- HP in HPr.
    zstep. zstep. rewrite landM32AC14, (Z.mod_small crc1) by lia. zstep.
    eapply evtF_cut.
    { eapply (comb_fin RNG) with (i := 31%nat) (a := P) (b := crc1) (p := 0) (mreg := 2147483648)
        (res := mm_loop 31 P crc1 0); try eassumption; try lia; try reflexivity.
      all: (change (2 ^ (Z.of_nat 31 + 1)) with (2^32); rewrite HP; exact Hxnz). }
    cbv beta. intros ms' (P2 & x10' & x13' & x15' & -> & HP2).
    assert (HP2r : 0 <= P2 < 2^64) by (rewrite HP2; pose proof (mm_loopAC14_range 31 P crc1 0 ltac:(lia) ltac:(lia)); lia).
    zstep. zstep. zstep. zstep. zstep.
    setreg 10 (Z_to_bv 64 (Z.lxor (mm_loop 31 (x2nmodp len2 3) crc1 0) (crc2 mod 2^32)))
      ltac:(f_equal; rewrite landM32AC14, HP2, HP; reflexivity).
    release_frame FR ST (bv_unsigned sp). finish. }
  zstep. if_cases K; zify_cond K.
  - (* len2 = 0: the op is x^0 *)
    rewrite ?unsigned_lit in K by lia. subst len2.
    apply TAIL. reflexivity.
  - rewrite ?unsigned_lit in K by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    eapply evtF_cut.
    { eapply (comb_loop RNG) with (fuel := 64%nat) (n := len2) (k := 3) (p := 2147483648) (res := x2nmodp len2 3);
        try eassumption; try lia.
      unfold x2nmodp, X0. reflexivity. }
    cbv beta. intros ms' (P & x6 & x12 & x13 & x29 & x30 & x31 & -> & HP).
    zstep. if_cases KZ; zify_cond KZ.
    { exfalso. apply Hx0. rewrite <- HP. pose proof Hxr. rewrite <- HP in *. lia. }
    apply TAIL. exact HP.
Qed.
