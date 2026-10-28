(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs B6_tac.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition imm_entry := 0xcbcf8%Z.

Definition imm_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3 a4 a5 a6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at asegs m' (bv_unsigned a1) src.

Lemma copy_fwd_step : forall i (src junk : list byte) b,
  length junk = length src -> nth_error src i = Some b ->
  upd (firstn i src ++ skipn i junk) i b = firstn (S i) src ++ skipn (S i) junk.
Proof.
  induction i as [|i IH]; intros [|x src] [|y junk] b L Hn; cbn in L, Hn |- *; try discriminate.
  - inversion Hn; subst. reflexivity.
  - f_equal. apply IH; [lia | exact Hn].
Qed.

Lemma copy_bwd_step : forall i (src junk : list byte) b,
  length junk = length src -> nth_error src i = Some b ->
  upd (firstn (S i) junk ++ skipn (S i) src) i b = firstn i junk ++ skipn i src.
Proof.
  induction i as [|i IH]; intros [|x src] [|y junk] b L Hn; cbn in L, Hn |- *; try discriminate.
  - inversion Hn; subst. reflexivity.
  - f_equal. apply IH; [lia | exact Hn].
Qed.

Lemma firstn_all_skipn_nil : forall (src junk : list byte), length junk = length src ->
  firstn (length src) src ++ skipn (length src) junk = src /\ firstn 0 junk ++ skipn 0 src = src
  /\ firstn 0 src ++ skipn 0 junk = junk /\ firstn (length src) junk ++ skipn (length src) src = junk.
Proof.
  intros src junk L. change (firstn 0 junk) with (@nil byte). change (firstn 0 src) with (@nil byte).
  change (skipn 0 src) with src. change (skipn 0 junk) with junk. cbn [app].
  rewrite firstn_all. rewrite (skipn_all2 junk) by lia. rewrite app_nil_r.
  rewrite <- L. rewrite firstn_all. rewrite (skipn_all2 src) by lia. rewrite app_nil_r. repeat split; reflexivity.
Qed.

Section IMM.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SRC : bytes_at asegs m (bv_unsigned a1) src.
  Hypothesis LEN : length src = Z.to_nat (bv_unsigned a2).
  Hypothesis DST : rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk].
  Hypothesis SEP : bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1.
  Hypothesis N63 : bv_unsigned a2 < 2^63.
  Hypothesis TOP : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ bv_unsigned a1 + bv_unsigned a2 < 2^64.

  Notation dst := (bv_unsigned a0).
  Notation sa := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation POST := (imm_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a0 a1 a2 src m).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation ST pc x11 x12 x13 x14 x15 x16 mm :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Lemma junk_len : length junk = length src.
  Proof. pose proof (proj1 (proj1 (proj1 DST))) as H. cbn in H. rewrite LEN. exact H. Qed.

  Section Loops.

    Lemma imm_ret : forall x11 x12 x13 x14 x15 x16 mm,
      mem_inv asegs mm -> bytes_at asegs mm (bv_unsigned a1) src -> munch W m mm -> wmono asegs m mm ->
      u8arr asegs mm dst src ->
      evt asegs POST (ST 0xcbd4c x11 x12 x13 x14 x15 x16 mm).
    Proof.
      intros x11 x12 x13 x14 x15 x16 mm MIm SRCm MU WM DA.
      pose proof (rw_cells_of_u8arr asegs mm dst src DA) as DC. rewrite LEN in DC.
      zstep. unfold imm_post. finish.
    Qed.

    Lemma imm_fwd : forall (k : nat) (i : Z) w11 w13 x14 x15 x16 mcur,
      Z.to_nat (n - i) = k -> 0 <= i < n -> w11 = Z_to_bv 64 (sa + i) -> w13 = Z_to_bv 64 (dst + i) ->
      mem_inv asegs mcur -> bytes_at asegs mcur sa src -> munch W m mcur -> wmono asegs m mcur ->
      u8arr asegs mcur dst (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) junk) ->
      evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 w11 (Z_to_bv 64 (dst + n)) w13 x14 x15 x16 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0xcbd08) fc None mcur (seg_rom asegs)).
    Proof.
      induction k as [k IH] using lt_wf_ind; intros i w11 w13 x14 x15 x16 mcur Hk Hi -> -> MIc SRCc MUc WMc DA.
      pose proof junk_len as JL.
      pose proof (bytes_at_bound _ _ _ _ SRCc) as SB. rewrite LEN in SB.
      pose proof (u8arr_bound _ _ _ _ DA) as DB. rewrite length_app, length_firstn, length_skipn, JL, LEN in DB.
      destruct (nth_error src (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
      pose proof (u8ro_read asegs mcur sa src i b _ SRCc NTH ltac:(lia) eq_refl) as RD.
      zstep.
      pose proof (u8arr_store_ok asegs _ _ _ i _ DA ltac:(rewrite length_app, length_firstn, length_skipn, JL, LEN; lia) eq_refl) as SOK.
      zstep.
      replace (le1 (Z_to_bv 64 (bv_unsigned b))) with [b] by (symmetry; exact (le1_zxb b)).
      pose proof (u8arr_write asegs _ _ _ i b DA ltac:(rewrite length_app, length_firstn, length_skipn, JL, LEN; lia)) as DA'.
      rewrite (copy_fwd_step (Z.to_nat i) src junk b JL NTH) in DA'. clear DA. store_done.
      do 2 zstep.
      zstep. if_cases K; zify_cond K; try rewrite !land_ones64 in K; try rewrite !Z.mod_small in K by lia.
      - replace (sa + i + 1) with (sa + (i + 1)) by lia. replace (dst + i + 1) with (dst + (i + 1)) by lia.
        replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in DA' by lia.
        eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); try eassumption; try reflexivity; lia.
      - zstep. eapply imm_ret; try eassumption.
        replace (S (Z.to_nat i)) with (length src) in DA' by lia.
        rewrite (proj1 (firstn_all_skipn_nil src junk JL)) in DA'. exact DA'.
    Qed.

    Lemma imm_bwd : forall (k : nat) (i : Z) x14 x15 x16 mcur,
      Z.to_nat i = k -> 0 <= i < n ->
      mem_inv asegs mcur -> bytes_at asegs mcur sa src -> munch W m mcur -> wmono asegs m mcur ->
      u8arr asegs mcur dst (firstn (Z.to_nat (i + 1)) junk ++ skipn (Z.to_nat (i + 1)) src) ->
      evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 1) (Z_to_bv 64 i) x14 x15 x16 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0xcbd30) fc None mcur (seg_rom asegs)).
    Proof.
      induction k as [k IH] using lt_wf_ind; intros i x14 x15 x16 mcur Hk Hi MIc SRCc MUc WMc DA.
      pose proof junk_len as JL. pose proof TOP as TOP'.
      pose proof (bytes_at_bound _ _ _ _ SRCc) as SB. rewrite LEN in SB.
      pose proof (u8arr_bound _ _ _ _ DA) as DB. rewrite length_app, length_firstn, length_skipn, JL, LEN in DB.
      destruct (nth_error src (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
      pose proof (u8ro_read asegs mcur sa src i b _ SRCc NTH ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep.
      pose proof (u8arr_store_ok asegs _ _ _ i _ DA ltac:(rewrite length_app, length_firstn, length_skipn, JL, LEN; lia) eq_refl) as SOK.
      zstep.
      replace (le1 (Z_to_bv 64 (bv_unsigned b))) with [b] by (symmetry; exact (le1_zxb b)).
      pose proof (u8arr_write asegs _ _ _ i b DA ltac:(rewrite length_app, length_firstn, length_skipn, JL, LEN; lia)) as DA'.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in DA' by lia.
      rewrite (copy_bwd_step (Z.to_nat i) src junk b JL NTH) in DA'. clear DA. store_done.
      zstep. if_cases K; zify_cond K.
      - replace (i + -1) with (i - 1) by lia.
        replace (Z.to_nat i) with (Z.to_nat (i - 1 + 1)) in DA' by lia.
        eapply (IH (Z.to_nat (i - 1)) ltac:(lia) (i - 1)); try eassumption; lia.
      - eapply imm_ret; try eassumption.
        replace (Z.to_nat i) with 0%nat in DA' by lia.
        rewrite (proj1 (proj2 (firstn_all_skipn_nil src junk JL))) in DA'. exact DA'.
    Qed.
  End Loops.

  Lemma imm_spec_sec : forall x13 x14 x15 x16,
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 imm_entry) fc None m (seg_rom asegs)).
  Proof.
    intros. unfold imm_entry. pose proof junk_len as JL. pose proof TOP as TOP'.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LEN in SB.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bv_unsigned_in_range 64 a2) as A2R. unfold bv_modulus in A2R. change (2 ^ Z.of_N 64) with (2^64) in A2R.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells asegs m _ _ _ DST) as DA.
    assert (RET0 : n = 0 -> forall x11 x12 x13' x14' x15' x16' ,
              evt asegs POST (ST 0xcbd4c x11 x12 x13' x14' x15' x16' m)).
    { intros N0. intros. eapply imm_ret; try eassumption.
      assert (src = []) as -> by (apply length_zero_iff_nil; lia).
      assert (junk = []) as E by (apply length_zero_iff_nil; rewrite JL; reflexivity). rewrite E in DA. exact DA. }
    zstep. if_cases K1; zify_cond K1.
    - zstep. if_cases K3; zify_cond K3.
      + apply RET0. lia.
      + zstep. if_cases K2; zify_cond K2; try rewrite signed_of_Z in K2 by lia.
        * apply RET0. lia.
        * zstep. zstep. replace (n + -1) with (n - 1) by lia.
          eapply (imm_bwd (Z.to_nat (n - 1)) (n - 1)); try eassumption; try lia.
          replace (Z.to_nat (n - 1 + 1)) with (length src) by lia.
          rewrite (proj2 (proj2 (proj2 (firstn_all_skipn_nil src junk JL)))). exact DA.
    - zstep. if_cases K2; zify_cond K2; try rewrite signed_of_Z in K2 by lia.
      + apply RET0. lia.
      + zstep. zstep.
        eapply (imm_fwd (Z.to_nat n) 0); try eassumption; try lia.
        * symmetry. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
        * symmetry. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
  Qed.
End IMM.
