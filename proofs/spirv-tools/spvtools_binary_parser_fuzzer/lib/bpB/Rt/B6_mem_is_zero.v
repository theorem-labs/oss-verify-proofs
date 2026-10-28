(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import B8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition mem_is_zero_entry := 0xcc29c%Z.

Definition zeros (k : nat) : list byte := repeat (Z_to_bv 8 0) k.

Definition mem_is_zero_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A n lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ZB : bytes_at asegs m A (zeros (Z.to_nat n)).
  Hypothesis Hn : 0 <= n <= 2^40.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + 16 <= bv_unsigned sp.
  Hypothesis SEP : A + n <= lo \/ bv_unsigned sp <= A.
  Hypothesis TOP : A + n + 8 <= 2^64.

  Notation POST := (mem_is_zero_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m).

  Lemma zeros_length : forall k, length (zeros k) = k.
  Proof. intros k. unfold zeros. apply repeat_length. Qed.

  Lemma zeros_nth : forall k i, (i < k)%nat -> nth_error (zeros k) i = Some (Z_to_bv 8 0).
  Proof.
    intros k i Hi. unfold zeros. rewrite nth_error_nth' with (d := Z_to_bv 8 0).
    - f_equal. apply nth_repeat.
    - rewrite repeat_length. exact Hi.
  Qed.

  Lemma A_bound : 0 <= A /\ A + n <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ ZB) as B. rewrite zeros_length in B. lia. Qed.

  Lemma land_m8 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551608 = 8 * (y / 8).
  Proof.
    intros y Hy. transitivity (Z.ldiff (Z.land y (Z.ones 64)) (Z.ones 3)).
    - rewrite Z.ldiff_land. rewrite <- Z.land_assoc. f_equal.
    - rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
  Qed.

  Lemma skipn_repeat : forall {X} (x : X) j k, skipn j (repeat x k) = repeat x (k - j).
  Proof. intros X x j; induction j as [|j IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

  Lemma firstn_repeat' : forall {X} (x : X) w k, (w <= k)%nat -> firstn w (repeat x k) = repeat x w.
  Proof. intros X x w; induction w as [|w IH]; intros [|k] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.

  Lemma zeros_firstn_skipn : forall k j w, (j + w <= k)%nat -> firstn w (skipn j (zeros k)) = zeros w.
  Proof. intros k j w H. unfold zeros. rewrite skipn_repeat, firstn_repeat' by lia. reflexivity. Qed.

  Lemma zero_byte_read : forall (i : Z) mm,
    bytes_at asegs mm A (zeros (Z.to_nat n)) -> 0 <= i < n ->
    ov_read_bytes asegs mm (wa (A + i)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros i mm ZBm Hi. apply (u8ro_read asegs mm A (zeros (Z.to_nat n)) i); [exact ZBm | apply zeros_nth; lia | lia | reflexivity].
  Qed.

  Lemma zero_word_read : forall (j : Z) mm,
    bytes_at asegs mm A (zeros (Z.to_nat n)) -> 0 <= j -> j + 8 <= n ->
    ov_read_bytes asegs mm (wa (A + j)) 8
    = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
  Proof.
    intros j mm ZBm H0 H8. rewrite (bytes_at_read asegs mm A (zeros (Z.to_nat n)) j 8 ZBm) by (rewrite ?zeros_length; lia).
    rewrite zeros_firstn_skipn by lia. reflexivity.
  Qed.

  Notation SP16 := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation ST pc x10 x11 x12 x13 x14 x15 x16 mm :=
    (MS (mkR ra SP16 gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Section Inside.
    Variables (mm : word -> option byte) (junk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis ZBm : bytes_at asegs mm A (zeros (Z.to_nat n)).
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -16).
    Hypothesis MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m mm.
    Hypothesis WM : wmono asegs m mm.

    Lemma miz_exit : forall x10 x12 x13 x14 x15 x16,
      evt asegs POST (ST 0xcc328 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 mm).
    Proof.
      intros. pose proof A_bound as AB.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
      do 4 zstep.
      release_frame FR STm (bv_unsigned sp).
      finish.
    Qed.

    Lemma miz_tail : forall (c : nat) (i : Z) x10 x13 x15 x16,
      (0 < c)%nat -> 0 <= i -> i + Z.of_nat c = n ->
      evt asegs POST (ST 0xcc314 x10 (Z_to_bv 64 0) (Z_to_bv 64 (A + i)) x13 (Z_to_bv 64 (Z.of_nat c)) x15 x16 mm).
    Proof.
      induction c as [|c IH]; intros i x10 x13 x15 x16 Hc Hi Hic; [lia|]. pose proof A_bound as AB.
      pose proof (zero_byte_read i mm ZBm ltac:(lia)) as RD.
      do 4 zstep.
      zstep. if_cases K; zify_cond K.
      - replace (A + i + 1) with (A + (i + 1)) by lia. replace (Z.of_nat (S c) + -1) with (Z.of_nat c) by lia.
        apply (IH (i + 1)); lia.
      - apply miz_exit.
    Qed.

    Lemma miz_junction2 : forall (dn : Z) x13 x15 x16,
      dn mod 8 = 0 -> A + n - 8 < dn <= A + n -> 0 <= dn ->
      evt asegs POST (ST 0xcc308 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 dn) x13 (Z_to_bv 64 (A + n)) x15 x16 mm).
    Proof.
      intros dn x13 x15 x16 Hdn8 Hdn Hdn0. pose proof A_bound as AB.
      zstep. if_cases K1; zify_cond K1.
      - apply miz_exit.
      - zstep. if_cases K2; zify_cond K2.
        + apply miz_exit.
        + zstep. replace dn with (A + (dn - A)) at 1 by lia.
          replace (A + n - dn) with (Z.of_nat (Z.to_nat (A + n - dn))) by lia.
          apply (miz_tail (Z.to_nat (A + n - dn)) (dn - A)); lia.
    Qed.

    Lemma miz_words : forall (k : nat) (q dn : Z) x13 x16,
      Z.to_nat (dn - q) = k -> dn mod 8 = 0 -> q mod 8 = 0 -> A <= q < dn -> A + n - 8 < dn <= A + n ->
      evt asegs POST (ST 0xcc2f8 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 dn) x13 (Z_to_bv 64 (A + n)) (Z_to_bv 64 q) x16 mm).
    Proof.
      induction k as [k IH] using lt_wf_ind; intros q dn x13 x16 Hk Hdn8 Hq8 Hq Hdn. pose proof A_bound as AB.
      assert (Hq8' : q + 8 <= dn) by (Z.div_mod_to_equations; lia).
      pose proof (zero_word_read (q - A) mm ZBm ltac:(lia) ltac:(lia)) as RD.
      replace (A + (q - A)) with q in RD by lia.
      do 3 zstep.
      zstep. if_cases K; zify_cond K.
      - apply (IH (Z.to_nat (dn - (q + 8)))); first [lia | Z.div_mod_to_equations; lia].
      - apply miz_junction2; lia.
    Qed.

    Lemma miz_junction1 : forall (up dn : Z) x13 x16,
      up mod 8 = 0 -> A <= up < A + 8 -> dn mod 8 = 0 -> A + n - 8 < dn <= A + n -> 0 <= dn ->
      evt asegs POST (ST 0xcc2f4 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 dn) x13 (Z_to_bv 64 (A + n)) (Z_to_bv 64 up) x16 mm).
    Proof.
      intros up dn x13 x16 Hup8 Hup Hdn8 Hdn Hdn0. pose proof A_bound as AB.
      zstep. if_cases K; zify_cond K.
      - apply miz_junction2; lia.
      - apply (miz_words (Z.to_nat (dn - up)) up dn); lia.
    Qed.

    Lemma miz_head : forall (k : nat) (i up dn : Z) x16,
      Z.to_nat (n - i) = k -> 0 <= i < n -> A + i < up ->
      up mod 8 = 0 -> A <= up < A + 8 -> dn mod 8 = 0 -> A + n - 8 < dn <= A + n -> 0 <= dn ->
      evt asegs POST (ST 0xcc2dc (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 dn) (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (A + n)) (Z_to_bv 64 up) x16 mm).
    Proof.
      induction k as [k IH] using lt_wf_ind; intros i up dn x16 Hk Hi Hiu Hup8 Hup Hdn8 Hdn Hdn0. pose proof A_bound as AB.
      pose proof (zero_byte_read i mm ZBm ltac:(lia)) as RD.
      do 3 zstep.
      zstep. if_cases K1; zify_cond K1.
      - apply miz_junction1; lia.
      - zstep. zstep. if_cases K2; zify_cond K2.
        + replace (A + i + 2) with (A + (i + 1) + 1) by lia.
          apply (IH (Z.to_nat (n - (i + 1)))); lia.
        + apply miz_junction1; lia.
    Qed.
  End Inside.

End Proofs.

Section Body.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A n lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ZB : bytes_at asegs m A (zeros (Z.to_nat n)).
  Hypothesis Hn : 0 <= n <= 2^40.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + 16 <= bv_unsigned sp.
  Hypothesis SEP : A + n <= lo \/ bv_unsigned sp <= A.
  Hypothesis TOP : A + n + 8 <= 2^64.
  Notation POST := (mem_is_zero_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m).

  Lemma miz_body : forall x12 x13 x14 x15 x16,
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 mem_is_zero_entry) fc None m (seg_rom asegs)).
  Proof.
    intros x12 x13 x14 x15 x16. pose proof (A_bound m A n ZB) as AB. unfold mem_is_zero_entry.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (zeros_length (Z.to_nat n)) as LZ.
    pose proof ZB as ZB0. change (id (bytes_at asegs m A (zeros (Z.to_nat n)))) in ZB0.
    pose proof ST0 as ST. carve_frame 16%nat ST.
    zstep. zstep.
    do 4 zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
    do 5 zstep.
    rewrite !land_m8 by lia.
    zstep. if_cases K1; zify_cond K1.
    { eapply miz_junction1; try eassumption; try exact ZB0; Z.div_mod_to_equations; lia. }
    zstep. if_cases K2; zify_cond K2.
    { eapply miz_junction1; try eassumption; try exact ZB0; Z.div_mod_to_equations; lia. }
    zstep. zstep. replace (A + 1) with (A + 0 + 1) by lia.
    eapply (miz_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m A n lo); try eassumption; try exact ZB0; try reflexivity; Z.div_mod_to_equations; lia.
  Qed.
End Body.
