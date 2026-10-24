(** Exact loop composition for both actual Adler 16-byte instruction bodies. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Step Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  Img0 CrcLib CrcModel AdlerModel AdlerBlock AdlerChunks AdlerBlockControl.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Local Opaque adler_output adler_block16_a adler_block16_b.
Section OuterBlocks.
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B ending : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TOP : B+Z.of_nat (length inp) < 2^64.
  Variable Q : machine_state -> Prop.
  Notation AT pc i a b g8 g9 g18 g31 :=
    (MS (mkR ra sp gp tp t0 t1 t2 g8 g9 a0 a1 a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 g18
      s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (B+ending)) (Z_to_bv 64 (B+i)) g31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Definition adler_outer_blocks_cont answer : Prop := forall af bf,
    0 <= af < 2^40 -> 0 <= bf < 2^40 ->
    adler_output (skipn (Z.to_nat ending) inp) af bf = answer ->
    forall h8 h9 h18 h31, evt rsegs Q (AT 0x14fe0 ending af bf h8 h9 h18 h31).
  Theorem adler_outer_blocks : forall (n : nat) i a b answer g8 g9 g18 g31,
    ending=i+16*Z.of_nat (S n) -> 0 <= i -> ending <= Z.of_nat (length inp) ->
    0 <= a -> 0 <= b -> a+255*(16*Z.of_nat (S n)) < 2^40 ->
    b+(16*Z.of_nat (S n))*a+255*(16*Z.of_nat (S n))*(16*Z.of_nat (S n)) < 2^40 ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> adler_outer_blocks_cont answer ->
    evt rsegs Q (AT 0x14f18 i a b g8 g9 g18 g31).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros i a b answer g8 g9 g18 g31 END HI HL HA HB BA BB REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as PB.
    assert (LI : i+16 <= Z.of_nat (length inp)) by (clear -END HI HL;lia).
    assert (RA : 0 <= a < 2^48) by (clear -HA BA;nia).
    assert (RB : 0 <= b < 2^48) by (clear -HA HB BB;nia).
    pose proof (adler_block16_range inp i a b HA HB) as [RNA RNB].
    pose proof (adler_budget_sixteen inp i (16*Z.of_nat (S n)) a b (2^40) ltac:(lia) HA HB BA BB) as [BAN BBN].
    replace (16*Z.of_nat (S n)-16) with (16*Z.of_nat n) in BAN,BBN by lia.
    assert (RAN : 0 <= adler_block16_a inp i a b < 2^40) by (clear -RNA BAN;nia).
    assert (RBN : 0 <= adler_block16_b inp i a b < 2^40) by (clear -RNA RNB BBN;nia).
    rewrite (adler_suffix_sixteen inp i a b HI LI) in REM.
    eapply adler_block16_outer;[exact INP|exact HI|exact LI|exact RA|exact RB|].
    intros h8 h9 h18 h31.
    assert (PN : 0 <= B+i+16 < 2^64) by (clear -HI END HL TOP PB;lia).
    assert (PE : 0 <= B+ending < 2^64) by (clear -HI END HL TOP PB;lia).
    eapply adler_outer_block_branch_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 (B+i+16) PN),(bv_wrap_small 64 (B+ending) PE) in BR;zify_bool BR.
    - destruct n as [|n];[exfalso;clear -END BR;cbn in END;lia|].
      replace (B+i+16) with (B+(i+16)) by ring.
      eapply (IH n ltac:(apply Nat.lt_succ_diag_r) (i+16)
        (adler_block16_a inp i a b) (adler_block16_b inp i a b) answer);
        [clear -END;rewrite Nat2Z.inj_succ in END;lia|clear -HI;lia|exact HL|
         exact (proj1 RAN)|exact (proj1 RBN)|exact BAN|exact BBN|exact REM|exact CONT].
    - assert (E : i+16=ending) by (clear -BR;lia).
      replace (B+i+16) with (B+ending) by (clear -E;lia).
      assert (RF : adler_output (skipn (Z.to_nat ending) inp)
        (adler_block16_a inp i a b) (adler_block16_b inp i a b) = answer).
      { rewrite <- E. exact REM. }
      unfold adler_outer_blocks_cont in CONT. exact (CONT _ _ RAN RBN RF h8 h9 h18 h31).
  Qed.
End OuterBlocks.
Section InnerBlocks.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis SIZE : Z.of_nat (length inp) <= 1048576.
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Notation AT pc i a b g5 g6 g16 g17 :=
    (MS (mkR ra sp gp tp g5 g6 t2 s0 s1 (Z_to_bv 64 0x11ed4) (Z_to_bv 64 15)
      (Z_to_bv 64 (L-i)) (Z_to_bv 64 b) (Z_to_bv 64 a) (Z_to_bv 64 (B+i)) g16 g17 s2
      s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Definition adler_inner_blocks_cont answer : Prop := forall j af bf,
    0 <= j <= L -> L-j < 16 -> 0 <= af -> 0 <= bf ->
    af+255*(L-j) < 2^40 -> bf+(L-j)*af+255*(L-j)*(L-j) < 2^40 ->
    adler_output (skipn (Z.to_nat j) inp) af bf = answer ->
    forall h5 h6 h16 h17, evt rsegs Q (AT 0x1510c j af bf h5 h6 h16 h17).
  Theorem adler_inner_blocks : forall (k : nat) i a b answer g5 g6 g16 g17,
    k=Z.to_nat (L-i) -> 0 <= i -> i+16 <= L -> 0 <= a -> 0 <= b ->
    a+255*(L-i) < 2^40 -> b+(L-i)*a+255*(L-i)*(L-i) < 2^40 ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> adler_inner_blocks_cont answer ->
    evt rsegs Q (AT 0x15040 i a b g5 g6 g16 g17).
  Proof.
    induction k as [k IH] using lt_wf_ind.
    intros i a b answer g5 g6 g16 g17 HK HI HL HA HB BA BB REM CONT.
    assert (RA : 0 <= a < 2^48) by (clear -HA BA HI HL;nia).
    assert (RB : 0 <= b < 2^48) by (clear -HA HB BB HI HL;nia).
    pose proof (adler_block16_range inp i a b HA HB) as [RNA RNB].
    pose proof (adler_budget_sixteen inp i (L-i) a b (2^40) ltac:(lia) HA HB BA BB) as [BAN BBN].
    replace (L-i-16) with (L-(i+16)) in BAN,BBN by ring.
    rewrite (adler_suffix_sixteen inp i a b HI HL) in REM.
    eapply adler_block16_inner;[exact INP|exact HI|exact HL|exact RA|exact RB|lia|].
    intros h16 h17 h5 h6.
    replace (B+i+16) with (B+(i+16)) by ring.
    replace (L-i-16) with (L-(i+16)) by ring.
    assert (NL : 0 <= L-(i+16) < 2^64) by (clear -HI HL SIZE;lia).
    eapply adler_inner_block_branch_cert. if_cases BR;zify_bool BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 15 ltac:(change (0 <= 15 < 2^64);lia)),
        (bv_wrap_small 64 (L-(i+16)) NL) in BR;zify_bool BR.
    - eapply (IH (Z.to_nat (L-(i+16))) ltac:(clear -HK HI HL;lia) (i+16)
        (adler_block16_a inp i a b) (adler_block16_b inp i a b) answer);
        [reflexivity|clear -HI;lia|clear -BR;lia|exact (proj1 RNA)|exact (proj1 RNB)|exact BAN|exact BBN|exact REM|exact CONT].
    - unfold adler_inner_blocks_cont in CONT.
      exact (CONT (i+16) _ _ ltac:(lia) ltac:(lia) (proj1 RNA) (proj1 RNB) BAN BBN REM h5 h6 h16 h17).
  Qed.
End InnerBlocks.
