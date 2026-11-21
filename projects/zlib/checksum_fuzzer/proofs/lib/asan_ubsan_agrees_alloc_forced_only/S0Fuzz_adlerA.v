(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code FuzzAdlerLib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold csub lo16 hi16 byte_at.
Section FXG. Context {fx : FPState}.

Definition KA : list reg := [1; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition LD : list reg := [1; 2; 3; 4; 7; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LS : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LT : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LM : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LR : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LE : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%bv.
Definition LB : list reg := [1; 2; 3; 4; 5; 6; 7; 10; 11; 12; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29]%bv.

Definition AMREF : Z := 73504.
Definition AMREF2 : Z := 73404.

Section ADL.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at RSEGS m).
  #[local] Abbreviation BS := (bytes_at RSEGS m).

  Lemma rd1 : forall a, adr0 <= a < adr0 + len0 ->
    exists b : byte, rdn RSEGS m (Z_to_bv 64 a) 1 = Some [b] /\ Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (BA a).
  Proof.
    intros a Ha. destruct (Hrd (a - adr0) ltac:(lia)) as [b Hb].
    replace (adr0 + (a - adr0)) with a in Hb by lia.
    exists b. split; [exact Hb | apply (rdn_byte_at_v RSEGS), Hb].
  Qed.

  Lemma BA_range : forall a, 0 <= BA a < 256.
  Proof. intros. apply byte_at_range. Qed.

  Lemma rd_amagic : rdn RSEGS m (Z_to_bv 64 AMAG) 8 = Some amag_bs.
  Proof. apply rd_amag. exact Himg. Qed.

  Ltac solve_ka := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption|]; first [assumption | solve_lkeeps | eapply lkeeps_trans; eassumption] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_ka ].

  Ltac lbu_pl F D Hb Eb :=
    chain_step;
    [ reflexivity
    | eapply step_lbu; [exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          match type of Hb with rdn _ _ (Z_to_bv 64 ?y) _ = _ => replace x with y by lia end end;
        exact Hb ]
    | step_simpl; gres; rewrite Eb ].

  Ltac ld_amag F D :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := Z_to_bv 64 4223091239536077);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with AMAG by (unfold AMAG, AMREF, AMREF2; lia) end;
        exact rd_amagic
      | exact amag_bs_v ]
    | step_simpl; gres ].


  Lemma a1_run : forall regs (retw : word) (a : Z),
    ret_ok retw -> getr regs 1 = retw ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 1 ->
    0 <= a < two64 -> 1 <= len0 ->
    exists r, msteps RSEGS (mkst regs (0x14e14 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a [BA adr0])
      /\ keeps_cs regs r.
  Proof.
    intros regs retw a Hret R1 R10 R11 R12 Ha Hl.
    destruct (rd1 adr0 ltac:(lia)) as (b0 & Hb0 & Eb0).
    pose proof (BA_range adr0) as Hb. pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split; [|split].
    - stepz F_14d68 D_14d68. rewrite (hi16_machine a) by lia.
      stepz F_14d6c D_14d6c.
      stepz F_14d70 D_14d70.
      stepi F_14d74 D_14d74; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_ft F_14d78 D_14d78 ltac:(condZ).
      lbu_pl F_14d7c D_14d7c Hb0 Eb0.
      stepz F_14d80 D_14d80. stepz F_14d84 D_14d84. stepz F_14d88 D_14d88. stepz F_14d8c D_14d8c.
      stepz F_14d90 D_14d90.
      stepi F_14d94 D_14d94; znorm. rewrite (zv_sltu 65520 (lo16 a + BA adr0)) by lia.
      stepz F_14d98 D_14d98.
      stepz F_14d9c D_14d9c. rewrite land_negflag.
      stepz F_14da0 D_14da0.
      stepz F_14da4 D_14da4. rewrite (csub_machine (lo16 a + BA adr0)) by (lia || reflexivity).
      stepz F_14da8 D_14da8.
      pose proof (csub_nonneg (lo16 a + BA adr0) ltac:(lia)) as Hc1.
      stepi F_14dac D_14dac; znorm. rewrite (zv_sltu 65520 (csub (lo16 a + BA adr0) + hi16 a)) by lia.
      stepz F_14db0 D_14db0.
      stepz F_14db4 D_14db4.
      stepz F_14db8 D_14db8.
      stepz F_14dbc D_14dbc. rewrite land_negflag.
      stepz F_14dc0 D_14dc0. rewrite (csub16_machine (csub (lo16 a + BA adr0) + hi16 a)) by (lia || reflexivity).
      stepz F_14dc4 D_14dc4.
      stepret F_14dc8 D_14dc8 retw ltac:(rwR; reflexivity).
      apply mst_refl.
    - gres. rewrite <- (adler_len1_path a (BA adr0)) by lia. cbv zeta.
      rewrite <- !csub_sltu, <- csub_sltu_shift16. reflexivity.
    - apply (proj2 (keeps_cs_lkeeps _ _)). solve_lkeeps.
  Qed.


  Lemma d16_seg0 : forall regs (A B p c : Z),
    getr regs 15 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x1508c : word) m rom) (mkst r (0x150cc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 16 = Z_to_bv 64 (BA (p + 4))
      /\ getr r 17 = Z_to_bv 64 (BA (p + 5))
      /\ getr r 5 = Z_to_bv 64 (BA (p + 6))
      /\ getr r 6 = Z_to_bv 64 (BA (p + 7))
      /\ getr r 15 = Z_to_bv 64 p
      /\ getr r 12 = Z_to_bv 64 c
      /\ lkeeps LD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RN Hp1 Hp2.
    destruct (rd1 (p + 0) ltac:(lia)) as (b0 & Hb0 & Eb0).
    destruct (rd1 (p + 1) ltac:(lia)) as (b1 & Hb1 & Eb1).
    destruct (rd1 (p + 2) ltac:(lia)) as (b2 & Hb2 & Eb2).
    destruct (rd1 (p + 3) ltac:(lia)) as (b3 & Hb3 & Eb3).
    destruct (rd1 (p + 4) ltac:(lia)) as (b4 & Hb4 & Eb4).
    destruct (rd1 (p + 5) ltac:(lia)) as (b5 & Hb5 & Eb5).
    destruct (rd1 (p + 6) ltac:(lia)) as (b6 & Hb6 & Eb6).
    destruct (rd1 (p + 7) ltac:(lia)) as (b7 & Hb7 & Eb7).
    replace (p + 0) with p in Hb0, Eb0 by lia.
    eexists. split.
    - lbu_pl F_14fe0 D_14fe0 Hb0 Eb0.
      lbu_pl F_14fe4 D_14fe4 Hb1 Eb1.
      lbu_pl F_14fe8 D_14fe8 Hb2 Eb2.
      lbu_pl F_14fec D_14fec Hb3 Eb3.
      stepz F_14ff0 D_14ff0.
      stepz F_14ff4 D_14ff4.
      stepz F_14ff8 D_14ff8.
      stepz F_14ffc D_14ffc.
      stepz F_15000 D_15000.
      stepz F_15004 D_15004.
      stepz F_15008 D_15008.
      lbu_pl F_1500c D_1500c Hb4 Eb4.
      lbu_pl F_15010 D_15010 Hb5 Eb5.
      lbu_pl F_15014 D_15014 Hb6 Eb6.
      lbu_pl F_15018 D_15018 Hb7 Eb7.
      stepz F_1501c D_1501c.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma d16_seg1 : forall regs (A B p c : Z),
    getr regs 15 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 16 = Z_to_bv 64 (BA (p + 4)) ->
    getr regs 17 = Z_to_bv 64 (BA (p + 5)) ->
    getr regs 5 = Z_to_bv 64 (BA (p + 6)) ->
    getr regs 6 = Z_to_bv 64 (BA (p + 7)) ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x150cc : word) m rom) (mkst r (0x150fc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 16 = Z_to_bv 64 (BA (p + 8))
      /\ getr r 17 = Z_to_bv 64 (BA (p + 9))
      /\ getr r 5 = Z_to_bv 64 (BA (p + 10))
      /\ getr r 6 = Z_to_bv 64 (BA (p + 11))
      /\ getr r 15 = Z_to_bv 64 p
      /\ getr r 12 = Z_to_bv 64 c
      /\ lkeeps LD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT16 RT17 RT5 RT6 RN Hp1 Hp2.
    destruct (rd1 (p + 8) ltac:(lia)) as (b8 & Hb8 & Eb8).
    destruct (rd1 (p + 9) ltac:(lia)) as (b9 & Hb9 & Eb9).
    destruct (rd1 (p + 10) ltac:(lia)) as (b10 & Hb10 & Eb10).
    destruct (rd1 (p + 11) ltac:(lia)) as (b11 & Hb11 & Eb11).
    eexists. split.
    - stepz F_15020 D_15020.
      stepz F_15024 D_15024.
      stepz F_15028 D_15028.
      stepz F_1502c D_1502c.
      stepz F_15030 D_15030.
      stepz F_15034 D_15034.
      stepz F_15038 D_15038.
      lbu_pl F_1503c D_1503c Hb8 Eb8.
      lbu_pl F_15040 D_15040 Hb9 Eb9.
      lbu_pl F_15044 D_15044 Hb10 Eb10.
      lbu_pl F_15048 D_15048 Hb11 Eb11.
      stepz F_1504c D_1504c.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma d16_seg2 : forall regs (A B p c : Z),
    getr regs 15 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 16 = Z_to_bv 64 (BA (p + 8)) ->
    getr regs 17 = Z_to_bv 64 (BA (p + 9)) ->
    getr regs 5 = Z_to_bv 64 (BA (p + 10)) ->
    getr regs 6 = Z_to_bv 64 (BA (p + 11)) ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x150fc : word) m rom) (mkst r (0x1512c : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 16 = Z_to_bv 64 (BA (p + 12))
      /\ getr r 17 = Z_to_bv 64 (BA (p + 13))
      /\ getr r 5 = Z_to_bv 64 (BA (p + 14))
      /\ getr r 6 = Z_to_bv 64 (BA (p + 15))
      /\ getr r 15 = Z_to_bv 64 p
      /\ getr r 12 = Z_to_bv 64 c
      /\ lkeeps LD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT16 RT17 RT5 RT6 RN Hp1 Hp2.
    destruct (rd1 (p + 12) ltac:(lia)) as (b12 & Hb12 & Eb12).
    destruct (rd1 (p + 13) ltac:(lia)) as (b13 & Hb13 & Eb13).
    destruct (rd1 (p + 14) ltac:(lia)) as (b14 & Hb14 & Eb14).
    destruct (rd1 (p + 15) ltac:(lia)) as (b15 & Hb15 & Eb15).
    eexists. split.
    - stepz F_15050 D_15050.
      stepz F_15054 D_15054.
      stepz F_15058 D_15058.
      stepz F_1505c D_1505c.
      stepz F_15060 D_15060.
      stepz F_15064 D_15064.
      stepz F_15068 D_15068.
      lbu_pl F_1506c D_1506c Hb12 Eb12.
      lbu_pl F_15070 D_15070 Hb13 Eb13.
      lbu_pl F_15074 D_15074 Hb14 Eb14.
      lbu_pl F_15078 D_15078 Hb15 Eb15.
      stepz F_1507c D_1507c.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma d16_seg3 : forall regs (A B p c : Z),
    getr regs 15 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 16 = Z_to_bv 64 (BA (p + 12)) ->
    getr regs 17 = Z_to_bv 64 (BA (p + 13)) ->
    getr regs 5 = Z_to_bv 64 (BA (p + 14)) ->
    getr regs 6 = Z_to_bv 64 (BA (p + 15)) ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x1512c : word) m rom) (mkst r (0x15154 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 15 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ lkeeps LD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT16 RT17 RT5 RT6 RN Hp1 Hp2.
    eexists. split.
    - stepz F_15080 D_15080.
      stepz F_15084 D_15084.
      stepz F_15088 D_15088.
      stepz F_1508c D_1508c.
      stepz F_15090 D_15090.
      stepz F_15094 D_15094.
      stepz F_15098 D_15098.
      stepz F_1509c D_1509c.
      stepz F_150a0 D_150a0.
      stepz F_150a4 D_150a4.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma b16_seg0 : forall regs (A B p : Z),
    getr regs 30 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14f64 : word) m rom) (mkst r (0x14fa4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 31 = Z_to_bv 64 (BA (p + 4))
      /\ getr r 8 = Z_to_bv 64 (BA (p + 5))
      /\ getr r 9 = Z_to_bv 64 (BA (p + 6))
      /\ getr r 18 = Z_to_bv 64 (BA (p + 7))
      /\ getr r 30 = Z_to_bv 64 p
      /\ lkeeps LB regs r.
  Proof.
    intros regs A B p RC R14 R13 Hp1 Hp2.
    destruct (rd1 (p + 0) ltac:(lia)) as (b0 & Hb0 & Eb0).
    destruct (rd1 (p + 1) ltac:(lia)) as (b1 & Hb1 & Eb1).
    destruct (rd1 (p + 2) ltac:(lia)) as (b2 & Hb2 & Eb2).
    destruct (rd1 (p + 3) ltac:(lia)) as (b3 & Hb3 & Eb3).
    destruct (rd1 (p + 4) ltac:(lia)) as (b4 & Hb4 & Eb4).
    destruct (rd1 (p + 5) ltac:(lia)) as (b5 & Hb5 & Eb5).
    destruct (rd1 (p + 6) ltac:(lia)) as (b6 & Hb6 & Eb6).
    destruct (rd1 (p + 7) ltac:(lia)) as (b7 & Hb7 & Eb7).
    replace (p + 0) with p in Hb0, Eb0 by lia.
    eexists. split.
    - lbu_pl F_14eb8 D_14eb8 Hb0 Eb0.
      lbu_pl F_14ebc D_14ebc Hb1 Eb1.
      lbu_pl F_14ec0 D_14ec0 Hb2 Eb2.
      lbu_pl F_14ec4 D_14ec4 Hb3 Eb3.
      stepz F_14ec8 D_14ec8.
      stepz F_14ecc D_14ecc.
      stepz F_14ed0 D_14ed0.
      stepz F_14ed4 D_14ed4.
      stepz F_14ed8 D_14ed8.
      stepz F_14edc D_14edc.
      stepz F_14ee0 D_14ee0.
      lbu_pl F_14ee4 D_14ee4 Hb4 Eb4.
      lbu_pl F_14ee8 D_14ee8 Hb5 Eb5.
      lbu_pl F_14eec D_14eec Hb6 Eb6.
      lbu_pl F_14ef0 D_14ef0 Hb7 Eb7.
      stepz F_14ef4 D_14ef4.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma b16_seg1 : forall regs (A B p : Z),
    getr regs 30 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 31 = Z_to_bv 64 (BA (p + 4)) ->
    getr regs 8 = Z_to_bv 64 (BA (p + 5)) ->
    getr regs 9 = Z_to_bv 64 (BA (p + 6)) ->
    getr regs 18 = Z_to_bv 64 (BA (p + 7)) ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14fa4 : word) m rom) (mkst r (0x14fd4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 31 = Z_to_bv 64 (BA (p + 8))
      /\ getr r 8 = Z_to_bv 64 (BA (p + 9))
      /\ getr r 9 = Z_to_bv 64 (BA (p + 10))
      /\ getr r 18 = Z_to_bv 64 (BA (p + 11))
      /\ getr r 30 = Z_to_bv 64 p
      /\ lkeeps LB regs r.
  Proof.
    intros regs A B p RC R14 R13 RT31 RT8 RT9 RT18 Hp1 Hp2.
    destruct (rd1 (p + 8) ltac:(lia)) as (b8 & Hb8 & Eb8).
    destruct (rd1 (p + 9) ltac:(lia)) as (b9 & Hb9 & Eb9).
    destruct (rd1 (p + 10) ltac:(lia)) as (b10 & Hb10 & Eb10).
    destruct (rd1 (p + 11) ltac:(lia)) as (b11 & Hb11 & Eb11).
    eexists. split.
    - stepz F_14ef8 D_14ef8.
      stepz F_14efc D_14efc.
      stepz F_14f00 D_14f00.
      stepz F_14f04 D_14f04.
      stepz F_14f08 D_14f08.
      stepz F_14f0c D_14f0c.
      stepz F_14f10 D_14f10.
      lbu_pl F_14f14 D_14f14 Hb8 Eb8.
      lbu_pl F_14f18 D_14f18 Hb9 Eb9.
      lbu_pl F_14f1c D_14f1c Hb10 Eb10.
      lbu_pl F_14f20 D_14f20 Hb11 Eb11.
      stepz F_14f24 D_14f24.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma b16_seg2 : forall regs (A B p : Z),
    getr regs 30 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 31 = Z_to_bv 64 (BA (p + 8)) ->
    getr regs 8 = Z_to_bv 64 (BA (p + 9)) ->
    getr regs 9 = Z_to_bv 64 (BA (p + 10)) ->
    getr regs 18 = Z_to_bv 64 (BA (p + 11)) ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14fd4 : word) m rom) (mkst r (0x15004 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 31 = Z_to_bv 64 (BA (p + 12))
      /\ getr r 8 = Z_to_bv 64 (BA (p + 13))
      /\ getr r 9 = Z_to_bv 64 (BA (p + 14))
      /\ getr r 18 = Z_to_bv 64 (BA (p + 15))
      /\ getr r 30 = Z_to_bv 64 p
      /\ lkeeps LB regs r.
  Proof.
    intros regs A B p RC R14 R13 RT31 RT8 RT9 RT18 Hp1 Hp2.
    destruct (rd1 (p + 12) ltac:(lia)) as (b12 & Hb12 & Eb12).
    destruct (rd1 (p + 13) ltac:(lia)) as (b13 & Hb13 & Eb13).
    destruct (rd1 (p + 14) ltac:(lia)) as (b14 & Hb14 & Eb14).
    destruct (rd1 (p + 15) ltac:(lia)) as (b15 & Hb15 & Eb15).
    eexists. split.
    - stepz F_14f28 D_14f28.
      stepz F_14f2c D_14f2c.
      stepz F_14f30 D_14f30.
      stepz F_14f34 D_14f34.
      stepz F_14f38 D_14f38.
      stepz F_14f3c D_14f3c.
      stepz F_14f40 D_14f40.
      lbu_pl F_14f44 D_14f44 Hb12 Eb12.
      lbu_pl F_14f48 D_14f48 Hb13 Eb13.
      lbu_pl F_14f4c D_14f4c Hb14 Eb14.
      lbu_pl F_14f50 D_14f50 Hb15 Eb15.
      stepz F_14f54 D_14f54.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma b16_seg3 : forall regs (A B p : Z),
    getr regs 30 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 31 = Z_to_bv 64 (BA (p + 12)) ->
    getr regs 8 = Z_to_bv 64 (BA (p + 13)) ->
    getr regs 9 = Z_to_bv 64 (BA (p + 14)) ->
    getr regs 18 = Z_to_bv 64 (BA (p + 15)) ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x15004 : word) m rom) (mkst r (0x15028 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 30 = Z_to_bv 64 (p + 16)
      /\ lkeeps LB regs r.
  Proof.
    intros regs A B p RC R14 R13 RT31 RT8 RT9 RT18 Hp1 Hp2.
    eexists. split.
    - stepz F_14f58 D_14f58.
      stepz F_14f5c D_14f5c.
      stepz F_14f60 D_14f60.
      stepz F_14f64 D_14f64.
      stepz F_14f68 D_14f68.
      stepz F_14f6c D_14f6c.
      stepz F_14f70 D_14f70.
      stepz F_14f74 D_14f74.
      stepz F_14f78 D_14f78.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.




  Lemma d16_body : forall regs (A B p c : Z),
    getr regs 15 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x1508c : word) m rom) (mkst r (0x15154 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) (BS p 16)))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) (BS p 16)))
      /\ getr r 15 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ lkeeps LD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RN Hp1 Hp2.
    destruct (d16_seg0 regs A B p c RC R14 R13 RN Hp1 Hp2) as (r1 & M1 & A1 & B1 & T1 & T2 & T3 & T4 & C1 & N1 & K1).
    destruct (d16_seg1 r1 _ _ p c C1 A1 B1 T1 T2 T3 T4 N1 Hp1 Hp2) as (r2 & M2 & A2 & B2 & U1 & U2 & U3 & U4 & C2 & N2 & K2).
    destruct (d16_seg2 r2 _ _ p c C2 A2 B2 U1 U2 U3 U4 N2 Hp1 Hp2) as (r3 & M3 & A3 & B3 & V1 & V2 & V3 & V4 & C3 & N3 & K3).
    destruct (d16_seg3 r3 _ _ p c C3 A3 B3 V1 V2 V3 V4 N3 Hp1 Hp2) as (r4 & M4 & A4 & B4 & C4 & N4 & K4).
    exists r4. split.
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
      eapply msteps_trans; [exact M3 | exact M4].
    - rewrite bytes_at_16_list, adler_fold_16_groups. rewrite <- !adler_fold_pair_eta in A4, B4.
      repeat split; try assumption.
      eapply lkeeps_trans; [exact K1|]. eapply lkeeps_trans; [exact K2|]. eapply lkeeps_trans; [exact K3 | exact K4].
  Qed.

  Lemma b16_body : forall regs (A B p : Z),
    getr regs 30 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14f64 : word) m rom) (mkst r (0x15028 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) (BS p 16)))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) (BS p 16)))
      /\ getr r 30 = Z_to_bv 64 (p + 16)
      /\ lkeeps LB regs r.
  Proof.
    intros regs A B p RC R14 R13 Hp1 Hp2.
    destruct (b16_seg0 regs A B p RC R14 R13 Hp1 Hp2) as (r1 & M1 & A1 & B1 & T1 & T2 & T3 & T4 & C1 & K1).
    destruct (b16_seg1 r1 _ _ p C1 A1 B1 T1 T2 T3 T4 Hp1 Hp2) as (r2 & M2 & A2 & B2 & U1 & U2 & U3 & U4 & C2 & K2).
    destruct (b16_seg2 r2 _ _ p C2 A2 B2 U1 U2 U3 U4 Hp1 Hp2) as (r3 & M3 & A3 & B3 & V1 & V2 & V3 & V4 & C3 & K3).
    destruct (b16_seg3 r3 _ _ p C3 A3 B3 V1 V2 V3 V4 Hp1 Hp2) as (r4 & M4 & A4 & B4 & C4 & K4).
    exists r4. split.
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
      eapply msteps_trans; [exact M3 | exact M4].
    - rewrite bytes_at_16_list, adler_fold_16_groups. rewrite <- !adler_fold_pair_eta in A4, B4.
      repeat split; try assumption.
      eapply lkeeps_trans; [exact K1|]. eapply lkeeps_trans; [exact K2|]. eapply lkeeps_trans; [exact K3 | exact K4].
  Qed.

  Lemma d16_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat) (rest : Z),
    getr regs 15 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    getr regs 12 = Z_to_bv 64 (16 * Z.of_nat (S k) + rest) ->
    getr regs 11 = Z_to_bv 64 15 ->
    0 <= rest < 16 -> adr0 <= q -> q + Z.of_nat n + 16 * Z.of_nat (S k) + rest <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x1508c : word) m rom) (mkst r (0x15158 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 15 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S k))
      /\ getr r 12 = Z_to_bv 64 rest
      /\ getr r 11 = Z_to_bv 64 15
      /\ lkeeps LD regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n rest RC R14 R13 RN R11 Hrest Hq Hfit.
    - destruct (d16_body regs _ _ (q + Z.of_nat n) _ RC R14 R13 RN ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & N1 & K1).
      assert (E11 : getr r1 11 = Z_to_bv 64 15) by (rewrite (K1 11%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R11).
      eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_150a8 D_150a8 ltac:(condZ).
        apply mst_refl.
      + gres. rewrite A1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite B1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite C1. zbv.
      + gres. rewrite N1. zbv.
      + gres. exact E11.
      + solve_ka.
    - destruct (d16_body regs _ _ (q + Z.of_nat n) _ RC R14 R13 RN ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & N1 & K1).
      assert (E11 : getr r1 11 = Z_to_bv 64 15) by (rewrite (K1 11%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R11).
      rewrite <- adler_fold_pair_eta, <- adler_fold_bytes_add in A1, B1.
      replace (q + Z.of_nat n + 16) with (q + Z.of_nat (n + 16)) in C1 by lia.
      replace (16 * Z.of_nat (S (S k)) + rest - 16) with (16 * Z.of_nat (S k) + rest) in N1 by lia.
      destruct (IH r1 ab q (n + 16)%nat rest C1 A1 B1 N1 E11 Hrest Hq ltac:(lia))
        as (r2 & M2 & A2 & B2 & C2 & N2 & E2 & K2).
      eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_150a8 D_150a8 ltac:(condZ).
        exact M2.
      + rewrite A2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite B2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite C2. zbv.
      + exact N2.
      + exact E2.
      + eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  Lemma b16_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    getr regs 30 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    getr regs 29 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S k)) ->
    adr0 <= q -> q + Z.of_nat n + 16 * Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14f64 : word) m rom) (mkst r (0x1502c : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 30 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S k))
      /\ lkeeps LB regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n RC R14 R13 RE Hq Hfit.
    - destruct (b16_body regs _ _ (q + Z.of_nat n) RC R14 R13 ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & K1).
      assert (E29 : getr r1 29 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat 1)) by (rewrite (K1 29%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact RE).
      eexists. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_14f7c D_14f7c ltac:(condZ).
        apply mst_refl.
      + gres. rewrite A1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite B1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite C1. zbv.
      + solve_ka.
    - destruct (b16_body regs _ _ (q + Z.of_nat n) RC R14 R13 ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & K1).
      assert (E29 : getr r1 29 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S (S k)))) by (rewrite (K1 29%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact RE).
      rewrite <- adler_fold_pair_eta, <- adler_fold_bytes_add in A1, B1.
      replace (q + Z.of_nat n + 16) with (q + Z.of_nat (n + 16)) in C1 by lia.
      replace (q + Z.of_nat n + 16 * Z.of_nat (S (S k))) with (q + Z.of_nat (n + 16) + 16 * Z.of_nat (S k)) in E29 by lia.
      destruct (IH r1 ab q (n + 16)%nat C1 A1 B1 E29 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & C2 & K2).
      eexists. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_14f7c D_14f7c ltac:(condZ).
        exact M2.
      + rewrite A2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite B2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite C2. zbv.
      + eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.


  Lemma sb_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 12 = Z_to_bv 64 (q + Z.of_nat n + Z.of_nat (S k)) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    adr0 <= q -> q + Z.of_nat n + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14e9c : word) m rom) (mkst r (0x14eb4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps LS regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R11 R12 R14 R13 Hq Hfit.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + lbu_pl F_14df0 D_14df0 Hb0 Eb0.
        stepz F_14df4 D_14df4. stepz F_14df8 D_14df8. stepz F_14dfc D_14dfc. stepz F_14e00 D_14e00.
        stepb_ft F_14e04 D_14e04 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x14e9c : word) m rom)
               (fun r => getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps LS regs r)).
      { eexists. split.
        - lbu_pl F_14df0 D_14df0 Hb0 Eb0.
          stepz F_14df4 D_14df4. stepz F_14df8 D_14df8. stepz F_14dfc D_14dfc. stepz F_14e00 D_14e00.
          stepb_tk F_14e04 D_14e04 ltac:(condZ).
          apply mst_refl.
        - rewrite adler_fold_bytes_S. cbn [fst snd]. post. }
      cbv beta. intros r1 (S11 & S12 & S14 & S13 & K1).
      destruct (IH r1 ab q (S n) S11 S12 S14 S13 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & K2).
      exists r2. split; [exact M2|].
      replace (n + S (S k))%nat with (S n + S k)%nat by lia.
      repeat split; try assumption. eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  Lemma tb_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    getr regs 15 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 12 = Z_to_bv 64 (q + Z.of_nat n + Z.of_nat (S k)) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    adr0 <= q -> q + Z.of_nat n + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x15160 : word) m rom) (mkst r (0x15178 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps LT regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R15 R12 R14 R13 Hq Hfit.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + lbu_pl F_150b4 D_150b4 Hb0 Eb0.
        stepz F_150b8 D_150b8. stepz F_150bc D_150bc. stepz F_150c0 D_150c0. stepz F_150c4 D_150c4.
        stepb_ft F_150c8 D_150c8 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x15160 : word) m rom)
               (fun r => getr r 15 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps LT regs r)).
      { eexists. split.
        - lbu_pl F_150b4 D_150b4 Hb0 Eb0.
          stepz F_150b8 D_150b8. stepz F_150bc D_150bc. stepz F_150c0 D_150c0. stepz F_150c4 D_150c4.
          stepb_tk F_150c8 D_150c8 ltac:(condZ).
          apply mst_refl.
        - rewrite adler_fold_bytes_S. cbn [fst snd]. post. }
      cbv beta. intros r1 (S15 & S12 & S14 & S13 & K1).
      destruct (IH r1 ab q (S n) S15 S12 S14 S13 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & K2).
      exists r2. split; [exact M2|].
      replace (n + S (S k))%nat with (S n + S k)%nat by lia.
      repeat split; try assumption. eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.


  Lemma AMAGIC_range : 0 <= AMAGIC < two64.
  Proof. rewrite AMAGIC_val. lia. Qed.

  Ltac step_auipc F D := stepi F D; znorm;
    try match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.

  Ltac srli_z F D x := stepi F D; znorm; rewrite (zv_srli x) by first [assumption | lia
      | apply amag_u_range; assumption | apply amag_v_range; assumption].
  Ltac mulhu_z F D x := stepi F D; znorm;
      first [ rewrite (zv_mulhu x 4223091239536077) by first [assumption | rewrite <- AMAGIC_val; apply AMAGIC_range]
            | rewrite (zv_mulhu x AMAGIC) by first [assumption | apply AMAGIC_range] ];
      first [ change (x * 4223091239536077 / two64) with (amag_t x) | change (x * AMAGIC / two64) with (amag_t x) ].

  Lemma smod_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps RSEGS (mkst regs (0x14eb4 : word) m rom) (mkst r (0x14f04 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((B mod BASE) * 2 ^ 16) (csub A))
      /\ lkeeps LM regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range B HB) as Ht. pose proof (amag_q_range B HB) as Hq.
    eexists. split; [|split].
    - stepz F_14e08 D_14e08. stepz F_14e0c D_14e0c. step_auipc F_14e10 D_14e10. stepz F_14e14 D_14e14.
      stepz F_14e18 D_14e18.
      ld_amag F_14e1c D_14e1c.
      stepi F_14e20 D_14e20; znorm. rewrite (zv_sltu 65520 A) by lia.
      stepz F_14e24 D_14e24.
      stepz F_14e28 D_14e28. rewrite land_negflag.
      stepz F_14e2c D_14e2c. rewrite (csub_machine A) by (lia || reflexivity).
      mulhu_z F_14e30 D_14e30 B.
      stepz F_14e34 D_14e34.
      srli_z F_14e38 D_14e38 (B - amag_t B).
      stepz F_14e3c D_14e3c.
      srli_z F_14e40 D_14e40 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_14e44 D_14e44.
      stepz F_14e48 D_14e48.
      stepz F_14e4c D_14e4c. rewrite (amag_mod B HB).
      stepz F_14e50 D_14e50.
      stepz F_14e54 D_14e54.
      apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma tmod_run : forall regs (A B : Z),
    getr regs 10 = Z_to_bv 64 AMREF -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps RSEGS (mkst regs (0x15178 : word) m rom) (mkst r (0x151bc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ lkeeps LR regs r.
  Proof.
    intros regs A B R10 R14 R13 HA HB.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split]].
    - ld_amag F_150cc D_150cc.
      mulhu_z F_150d0 D_150d0 A.
      mulhu_z F_150d4 D_150d4 B.
      stepz F_150d8 D_150d8.
      srli_z F_150dc D_150dc (A - amag_t A).
      stepz F_150e0 D_150e0.
      stepz F_150e4 D_150e4.
      srli_z F_150e8 D_150e8 (B - amag_t B).
      stepz F_150ec D_150ec.
      stepz F_150f0 D_150f0. stepz F_150f4 D_150f4.
      srli_z F_150f8 D_150f8 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      srli_z F_150fc D_150fc (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_15100 D_15100. stepz F_15104 D_15104.
      stepz F_15108 D_15108. rewrite (amag_mod A HA).
      stepz F_1510c D_1510c. rewrite (amag_mod B HB).
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma comb_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    exists r, msteps RSEGS (mkst regs (0x151bc : word) m rom) (mkst r (0x151c4 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor (B * 2 ^ 16) A)
      /\ lkeeps LR regs r.
  Proof.
    intros regs A B R14 R13.
    eexists. split; [|split].
    - stepz F_15110 D_15110. stepz F_15114 D_15114. apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma bmod_run : forall regs (A B bp rem i : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 17 = Z_to_bv 64 4223091239536077 -> getr regs 7 = Z_to_bv 64 65521 ->
    getr regs 15 = Z_to_bv 64 bp -> getr regs 5 = Z_to_bv 64 5552 ->
    getr regs 12 = Z_to_bv 64 rem -> getr regs 16 = Z_to_bv 64 i ->
    0 <= A < two64 -> 0 <= B < two64 -> 0 <= rem < two64 ->
    exists r, msteps RSEGS (mkst regs (0x1502c : word) m rom) (mkst r (0x15070 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ getr r 15 = Z_to_bv 64 (bp + 5552)
      /\ getr r 29 = Z_to_bv 64 (Z.shiftr rem 4)
      /\ getr r 16 = Z_to_bv 64 (i + 1)
      /\ lkeeps LE regs r.
  Proof.
    intros regs A B bp rem i R14 R13 R17 R7 R15 R5 R12 R16 HA HB Hrem.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - mulhu_z F_14f80 D_14f80 A.
      mulhu_z F_14f84 D_14f84 B.
      stepz F_14f88 D_14f88.
      srli_z F_14f8c D_14f8c (A - amag_t A).
      stepz F_14f90 D_14f90.
      stepz F_14f94 D_14f94.
      srli_z F_14f98 D_14f98 (B - amag_t B).
      stepz F_14f9c D_14f9c.
      stepz F_14fa0 D_14fa0.
      srli_z F_14fa4 D_14fa4 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      stepz F_14fa8 D_14fa8.
      stepz F_14fac D_14fac. rewrite (amag_mod A HA).
      srli_z F_14fb0 D_14fb0 rem.
      srli_z F_14fb4 D_14fb4 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_14fb8 D_14fb8.
      stepz F_14fbc D_14fbc. rewrite (amag_mod B HB).
      stepz F_14fc0 D_14fc0.
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.
End ADL.
End FXG.
