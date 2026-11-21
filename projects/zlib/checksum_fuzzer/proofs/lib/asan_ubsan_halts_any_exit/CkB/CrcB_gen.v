(* 1.4 pilot (2026-11-06): crc32_combine_gen64 at the 1.4 both image (0x81a88 .. 0x81b8c; x2nmodp and
   multmodp inlined, ASan shadow check on the x2n_table load), re-walked; crc32_combine_gen_proofA keeps its 1.3.1
   statement (crc32_combine_gen_stmtA). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.cks Require Import CkTables CkModel CkMultmodp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkA Require Import CrcAGlue CrcATac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CrcBGlue.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

(* the 1.4 shift block's b update, as zstep leaves it *)
Lemma bstepAG14 : forall b,
  Z.lxor (b ≫ 1) (Z.land (bv_signed (Z_to_bv 64 (b ≪ 63)) ≫ 63 mod 18446744073709551616) 3988292384) = bstep b.
Proof.
  intros b. change 18446744073709551616 with (2^64). rewrite sra63_odd. unfold bstep, POLY.
  destruct (Z.odd b); [reflexivity | rewrite Z.land_0_l, Z.lxor_0_r; reflexivity].
Qed.

Lemma bstepAG14_range : forall b, 0 <= b < 2^32 -> 0 <= bstep b < 2^32.
Proof.
  intros b Hb. unfold bstep.
  assert (Hs : 0 <= b ≫ 1 < 2^32).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia|].
    apply (Z.le_lt_trans _ b); [apply Z.div_le_upper_bound; lia| lia]. }
  destruct (Z.odd b); [| exact Hs].
  apply lxor_range32; [exact Hs | unfold POLY; lia].
Qed.

Lemma mm_loopAG14_range : forall i a b p, 0 <= b < 2^32 -> 0 <= p < 2^32 -> 0 <= mm_loop i a b p < 2^32.
Proof.
  induction i as [|i IH]; intros a b p Hb Hp; rewrite mm_loop_unfold; cbv zeta.
  - destruct (Z.testbit a (Z.of_nat 0)); cbn [andb]; [destruct (_ =? 0)|]; try apply lxor_range32; lia.
  - pose proof (lxor_range32 p b Hp Hb). pose proof (bstepAG14_range b Hb).
    destruct (Z.testbit a (Z.of_nat (S i))); cbn [andb]; [destruct (_ =? 0)|]; try lia; apply IH; lia.
Qed.

(* the 1.4 lwu leaves zx32 of the loaded word (CrcA_zkit's zx32_lit, which this file does not import) *)
Lemma zx32_litAG14 : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.

(* CrcATac's ck_join / ck_done over TWO registers: the 1.4 slow check writes t1 as well as the shadow byte's a1 *)
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

Section BODY.
  Variables (RNG : footprint)
            (ra spw gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Hypothesis MI0 : mem_inv asegs m0.
  Hypothesis UX0 : unpoisoned m0 AX2N (AX2N + 128).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.

  (* t0 = POLY, a4 = 2^31, a5 = x2n_table, a6 = the shadow offset, a7 = ~x2n_table, constant over the loop *)
  Notation ST pc x6 x7 x28 x10 x11 x12 x13 :=
    (MS (mkR ra spw gp tp (Z_to_bv 64 3988292384) x6 x7 s0 s1 x10 x11 x12 x13 (Z_to_bv 64 2147483648)
             (Z_to_bv 64 141536) (Z_to_bv 64 2147450880) (Z_to_bv 64 18446744073709410079)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m0 (seg_rom asegs)).

  (* the multmodp loop (test 0x81b34) ends at the x2nmodp latch (0x81ad4) with the product in a1 *)
  Definition gmm_post (x10 x13 : word) (res : Z) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x12 : word), ms' = ST 0x81b1c x5 x6 x7 x10 (Z_to_bv 64 res) x12 x13.

  Lemma gen_mm : forall (i : nat) (a b p mreg res : Z) (x7 x10 x13 : word),
    (i <= 31)%nat -> 0 <= a < 2^32 -> a mod 2 ^ (Z.of_nat i + 1) <> 0 ->
    0 <= b < 2^32 -> 0 <= p < 2^32 -> mreg = 2 ^ Z.of_nat i ->
    res = mm_loop i a b p ->
    evtF asegs RNG (gmm_post x10 x13 res)
         (ST 0x81b7c (Z_to_bv 64 b) (Z_to_bv 64 mreg) x7 x10 (Z_to_bv 64 p) (Z_to_bv 64 a) x13).
  Proof.
    induction i as [|i IH]; intros a b p mreg res x7 x10 x13 Hi Ha Hanz Hb Hp Hmi HR.
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
      zstep.
      apply evtF_done. unfold gmm_post. subst res. rewrite (mm_loop_exit 0 a) by (first [exact Ht | apply Z.mod_1_r]).
      eexists _, _, _, _. reflexivity.
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
      pose proof (bstepAG14_range b Hb) as Hb'.
      assert (Hmr : 0 <= mreg < 2^64) by lia. assert (Hmr1 : 0 <= mreg + -1 < 2^64) by lia.
      (* the shift block (0x81b1c), then the loop at bit i *)
      assert (NEXT : forall p' (x7' : word), 0 <= p' < 2^32 -> a mod 2 ^ Z.of_nat j <> 0 ->
                res = mm_loop i a (bstep b) p' ->
                evtF asegs RNG (gmm_post x10 x13 res)
                     (ST 0x81b64 (Z_to_bv 64 b) (Z_to_bv 64 mreg) x7' x10 (Z_to_bv 64 p') (Z_to_bv 64 a) x13)).
      { intros p' x7' Hp' Hnz HR'.
        zstep. zstep. zstep. zstep. zstep. zstep.
        rewrite Hm', bstepAG14.
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
          zstep.
          apply evtF_done. unfold gmm_post. subst res. rewrite (mm_loop_exit j a) by assumption.
          eexists _, _, _, _. reflexivity.
  Qed.

  (* the x2nmodp loop from its odd test (0x81ae4) to the exit block (0x81b68), the result in a1; p in t0 *)
  Definition gloop_post (res : Z) : machine_state -> Prop :=
    fun ms' => exists (P : Z) (x5 x6 x7 x10 x12 x13 : word),
      ms' = ST 0x81bb0 x5 x6 x7 x10 (Z_to_bv 64 P) x12 x13 /\ P = res.

  Lemma gen_loop : forall (fuel : nat) (n k p res : Z) (x6 x7 x11 x12 : word),
    0 < n < 2 ^ Z.of_nat fuel -> n < 2^63 -> 0 <= k -> k + Z.of_nat fuel < 2^32 -> 0 <= p < 2^32 ->
    res = x2n_loop fuel n k p ->
    evtF asegs RNG (gloop_post res)
         (ST 0x81b2c (Z_to_bv 64 p) x6 x7 (Z_to_bv 64 n) x11 x12 (Z_to_bv 64 k)).
  Proof.
    induction fuel as [|f IH]; intros n k p res x6 x7 x11 x12 Hn Hf Hk Hkf Hp HR.
    { exfalso. change (2 ^ Z.of_nat 0) with 1 in Hn. lia. }
    assert (SH : 0 <= n ≫ 1 < 2 ^ Z.of_nat f).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
      replace (Z.of_nat (S f)) with (Z.of_nat f + 1) in Hn by lia. rewrite Z.pow_add_r in Hn by lia. change (2^1) with 2 in Hn.
      Z.div_mod_to_equations. lia. }
    assert (SH63 : n ≫ 1 < 2^63) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia).
    (* the latch (0x81ad4): n >>= 1; k++; t0 := a1; leave on n = 0 *)
    assert (LATCH : forall (P : Z) (x5' x6' x7' x12' : word), 0 <= P < 2^32 ->
              res = x2n_loop f (n ≫ 1) (k + 1) P ->
              evtF asegs RNG (gloop_post res)
                   (ST 0x81b1c x5' x6' x7' (Z_to_bv 64 n) (Z_to_bv 64 P) x12' (Z_to_bv 64 k))).
    { intros P x5' x6' x7' x12' HP HR'.
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      - (* n >> 1 = 0: leave *)
        apply evtF_done. unfold gloop_post. eexists P, _, _, _, _, _, _. split; [reflexivity|].
        rewrite HR', K2, x2n_loop_done. reflexivity.
      - apply IH; first [lia | exact HR']. }
    rewrite (x2n_loop_step f n k) in HR by lia.
    zstep. zstep. if_cases K1; zify_cond K1.
    - (* even: a1 := t0, to the latch *)
      assert (OD : Z.odd n = false).
      { rewrite <- Z.bit0_odd. apply Z.bits_inj_iff in K1. specialize (K1 0). rewrite Z.land_spec, Z.bits_0 in K1.
        change (Z.testbit 1 0) with true in K1. rewrite andb_true_r in K1. exact K1. }
      rewrite OD in HR. zstep. apply LATCH; [exact Hp| exact HR].
    - (* odd: p := multmodp (x2n_table[k & 31], p), behind the ASan check of the load *)
      assert (OD : Z.odd n = true).
      { destruct (Z.odd n) eqn:E; [reflexivity|]. exfalso. apply K1.
        apply Z.bits_inj'. intros b Hb. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.eq_dec b 0) as [->|NZ]; [rewrite Z.bit0_odd, E; reflexivity|].
        replace (Z.testbit 1 b) with false; [apply andb_false_r|]. symmetry. apply (testbit_high 1 1 b); lia. }
      rewrite OD in HR.
      set (idx := k mod 32) in *. assert (Hidx : 0 <= idx < 32) by (subst idx; apply Z.mod_pos_bound; lia).
      set (a := x2n idx) in *. pose proof (x2n_range idx) as Ha. fold a in Ha.
      assert (Hanz : a mod 2 ^ (Z.of_nat 31 + 1) <> 0) by (subst a; apply x2n_nz_mod; exact Hidx).
      zstep. zstep. zstep. if_cases KU; zify_cond KU.
      { exfalso. exact (x2n_guard_dead k 18446744073709410079 ltac:(lia) KU). }   (* the UBSan table-bound check *)
      zstep.
      setreg 12 (Z_to_bv 64 (141536 + 4 * idx))
        ltac:(f_equal; subst idx; rewrite Z.shiftl_mul_pow2 by lia; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; change (2^5) with 32; change (2^2) with 4; lia).
      destruct (unpoisoned_check_rd asegs m0 AX2N (AX2N + 128) (141536 + 4 * idx) 4 UX0
                  ltac:(unfold AX2N; lia) ltac:(unfold AX2N; lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK).
      unfold shad, ASHOFF in RD. replace (2147450880 + Z.shiftr (141536 + 4 * idx) 3) with (Z.shiftr (141536 + 4 * idx) 3 + 2147450880) in RD by lia.
      pose proof (sval_range b) as SR.
      pose proof (x2n_read m0 idx (Z_to_bv 64 (141536 + 4 * idx)) MI0 Hidx eq_refl) as RDT. fold a in RDT.
      zstep. zstep. zstep. rewrite sxb_sval.
      ck_join2 11 7 0x81b54.
      { zstep. if_cases KS; zify_cond KS; [| ck_done2 11 7].
        zstep. zstep. zstep. if_cases KB; zify_lts KB; [ck_done2 11 7|].
        exfalso. Z.div_mod_to_equations. lia. }
      zstep. zstep. rewrite (zx32_litAG14 a Ha). zstep. zstep.
      eapply evtF_cut.
      { eapply (gen_mm 31%nat a p 0 2147483648); try lia; try reflexivity. }
      cbv beta. intros ms' (x5' & x6' & x7' & x12' & ->).
      apply LATCH; [apply mm_loopAG14_range; lia|].
      rewrite HR. unfold multmodp. reflexivity.
  Qed.
End BODY.

(* the 1.3.1 statement, at the 1.4 model *)
Theorem crc32_combine_gen_proofA : crc32_combine_gen_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         Fr fc m lo len2 MI ST LOS KLO GOT SHB CKSH E0 Hlen RI RISH RSTK.
  subst a0. unfold ACK_GEN. unfold CK_GEN_STACK in *.
  assert (GEN : crc32_combine_gen len2 = x2nmodp len2 3)
    by (unfold crc32_combine_gen, crc32_combine_gen64; rewrite (proj2 (Z.ltb_ge len2 0)) by lia; reflexivity).
  rewrite GEN. clear GEN.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (x2n_unpoisoned m CKSH) as UX.
  pose proof KLO as KLO'. unfold KHIGH in KLO'.
  carve_frame 16%nat ST.
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep. zstep. if_cases K; zify_cond K.
  - (* len2 = 0: x^0 *)
    rewrite ?unsigned_lit in K by lia. subst len2.
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp). finish.
  - rewrite ?unsigned_lit in K by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU1 : munch _ m m1 |- _ =>
        pose proof (unpoisoned_mu _ lo m m1 AX2N (AX2N + 128) UX MU1
                      ltac:(cbn; lia) ltac:(unfold AX2N, KHIGH in *; lia) KLO) as UX1
      end end.
    eapply evtF_cut.
    { eapply (gen_loop RNG) with (fuel := 64%nat) (n := len2) (k := 3) (p := 2147483648) (res := x2nmodp len2 3);
        try eassumption; try lia.
      unfold x2nmodp, X0. reflexivity. }
    cbv beta. intros ms' (P & x5 & x6 & x7 & x10 & x12 & x13 & -> & HP).
    zstep. zstep. zstep. zstep.
    setreg 10 (Z_to_bv 64 (x2nmodp len2 3)) ltac:(f_equal; symmetry; exact HP).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.
