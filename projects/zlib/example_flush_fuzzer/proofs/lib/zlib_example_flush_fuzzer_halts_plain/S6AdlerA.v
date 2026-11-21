(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S6AdlerBase S6Adler_code FuzzAdlerLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold csub lo16 hi16 byte_at.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition KA : list reg := [1; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition LD : list reg := [1; 2; 3; 4; 7; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LS : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LT : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LM : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LR : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LE : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%bv.
Definition LB : list reg := [1; 2; 3; 4; 5; 6; 7; 10; 11; 12; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29]%bv.

Definition AMREF : Z := 65820.
Definition AMREF2 : Z := 65720.

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
    exists r, msteps RSEGS (mkst regs (0x1a010 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a [BA adr0])
      /\ keeps_cs regs r.
  Proof.
    intros regs retw a Hret R1 R10 R11 R12 Ha Hl.
    destruct (rd1 adr0 ltac:(lia)) as (b0 & Hb0 & Eb0).
    pose proof (BA_range adr0) as Hb. pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split; [|split].
    - stepz F_19f74 D_19f74. rewrite (hi16_machine a) by lia.
      stepz F_19f78 D_19f78.
      stepz F_19f7c D_19f7c.
      stepi F_19f80 D_19f80; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_ft F_19f84 D_19f84 ltac:(condZ).
      lbu_pl F_19f88 D_19f88 Hb0 Eb0.
      stepz F_19f8c D_19f8c. stepz F_19f90 D_19f90. stepz F_19f94 D_19f94. stepz F_19f98 D_19f98.
      stepz F_19f9c D_19f9c.
      stepi F_19fa0 D_19fa0; znorm. rewrite (zv_sltu 65520 (lo16 a + BA adr0)) by lia.
      stepz F_19fa4 D_19fa4.
      stepz F_19fa8 D_19fa8. rewrite land_negflag.
      stepz F_19fac D_19fac.
      stepz F_19fb0 D_19fb0. rewrite (csub_machine (lo16 a + BA adr0)) by (lia || reflexivity).
      stepz F_19fb4 D_19fb4.
      pose proof (csub_nonneg (lo16 a + BA adr0) ltac:(lia)) as Hc1.
      stepi F_19fb8 D_19fb8; znorm. rewrite (zv_sltu 65520 (csub (lo16 a + BA adr0) + hi16 a)) by lia.
      stepz F_19fbc D_19fbc.
      stepz F_19fc0 D_19fc0.
      stepz F_19fc4 D_19fc4.
      stepz F_19fc8 D_19fc8. rewrite land_negflag.
      stepz F_19fcc D_19fcc. rewrite (csub16_machine (csub (lo16 a + BA adr0) + hi16 a)) by (lia || reflexivity).
      stepz F_19fd0 D_19fd0.
      stepret F_19fd4 D_19fd4 retw ltac:(rwR; reflexivity).
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
    exists r, msteps RSEGS (mkst regs (0x1a288 : word) m rom) (mkst r (0x1a2c8 : word) m rom)
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
    - lbu_pl F_1a1ec D_1a1ec Hb0 Eb0.
      lbu_pl F_1a1f0 D_1a1f0 Hb1 Eb1.
      lbu_pl F_1a1f4 D_1a1f4 Hb2 Eb2.
      lbu_pl F_1a1f8 D_1a1f8 Hb3 Eb3.
      stepz F_1a1fc D_1a1fc.
      stepz F_1a200 D_1a200.
      stepz F_1a204 D_1a204.
      stepz F_1a208 D_1a208.
      stepz F_1a20c D_1a20c.
      stepz F_1a210 D_1a210.
      stepz F_1a214 D_1a214.
      lbu_pl F_1a218 D_1a218 Hb4 Eb4.
      lbu_pl F_1a21c D_1a21c Hb5 Eb5.
      lbu_pl F_1a220 D_1a220 Hb6 Eb6.
      lbu_pl F_1a224 D_1a224 Hb7 Eb7.
      stepz F_1a228 D_1a228.
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
    exists r, msteps RSEGS (mkst regs (0x1a2c8 : word) m rom) (mkst r (0x1a2f8 : word) m rom)
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
    - stepz F_1a22c D_1a22c.
      stepz F_1a230 D_1a230.
      stepz F_1a234 D_1a234.
      stepz F_1a238 D_1a238.
      stepz F_1a23c D_1a23c.
      stepz F_1a240 D_1a240.
      stepz F_1a244 D_1a244.
      lbu_pl F_1a248 D_1a248 Hb8 Eb8.
      lbu_pl F_1a24c D_1a24c Hb9 Eb9.
      lbu_pl F_1a250 D_1a250 Hb10 Eb10.
      lbu_pl F_1a254 D_1a254 Hb11 Eb11.
      stepz F_1a258 D_1a258.
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
    exists r, msteps RSEGS (mkst regs (0x1a2f8 : word) m rom) (mkst r (0x1a328 : word) m rom)
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
    - stepz F_1a25c D_1a25c.
      stepz F_1a260 D_1a260.
      stepz F_1a264 D_1a264.
      stepz F_1a268 D_1a268.
      stepz F_1a26c D_1a26c.
      stepz F_1a270 D_1a270.
      stepz F_1a274 D_1a274.
      lbu_pl F_1a278 D_1a278 Hb12 Eb12.
      lbu_pl F_1a27c D_1a27c Hb13 Eb13.
      lbu_pl F_1a280 D_1a280 Hb14 Eb14.
      lbu_pl F_1a284 D_1a284 Hb15 Eb15.
      stepz F_1a288 D_1a288.
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
    exists r, msteps RSEGS (mkst regs (0x1a328 : word) m rom) (mkst r (0x1a350 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 15 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ lkeeps LD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT16 RT17 RT5 RT6 RN Hp1 Hp2.
    eexists. split.
    - stepz F_1a28c D_1a28c.
      stepz F_1a290 D_1a290.
      stepz F_1a294 D_1a294.
      stepz F_1a298 D_1a298.
      stepz F_1a29c D_1a29c.
      stepz F_1a2a0 D_1a2a0.
      stepz F_1a2a4 D_1a2a4.
      stepz F_1a2a8 D_1a2a8.
      stepz F_1a2ac D_1a2ac.
      stepz F_1a2b0 D_1a2b0.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma b16_seg0 : forall regs (A B p : Z),
    getr regs 30 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x1a160 : word) m rom) (mkst r (0x1a1a0 : word) m rom)
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
    - lbu_pl F_1a0c4 D_1a0c4 Hb0 Eb0.
      lbu_pl F_1a0c8 D_1a0c8 Hb1 Eb1.
      lbu_pl F_1a0cc D_1a0cc Hb2 Eb2.
      lbu_pl F_1a0d0 D_1a0d0 Hb3 Eb3.
      stepz F_1a0d4 D_1a0d4.
      stepz F_1a0d8 D_1a0d8.
      stepz F_1a0dc D_1a0dc.
      stepz F_1a0e0 D_1a0e0.
      stepz F_1a0e4 D_1a0e4.
      stepz F_1a0e8 D_1a0e8.
      stepz F_1a0ec D_1a0ec.
      lbu_pl F_1a0f0 D_1a0f0 Hb4 Eb4.
      lbu_pl F_1a0f4 D_1a0f4 Hb5 Eb5.
      lbu_pl F_1a0f8 D_1a0f8 Hb6 Eb6.
      lbu_pl F_1a0fc D_1a0fc Hb7 Eb7.
      stepz F_1a100 D_1a100.
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
    exists r, msteps RSEGS (mkst regs (0x1a1a0 : word) m rom) (mkst r (0x1a1d0 : word) m rom)
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
    - stepz F_1a104 D_1a104.
      stepz F_1a108 D_1a108.
      stepz F_1a10c D_1a10c.
      stepz F_1a110 D_1a110.
      stepz F_1a114 D_1a114.
      stepz F_1a118 D_1a118.
      stepz F_1a11c D_1a11c.
      lbu_pl F_1a120 D_1a120 Hb8 Eb8.
      lbu_pl F_1a124 D_1a124 Hb9 Eb9.
      lbu_pl F_1a128 D_1a128 Hb10 Eb10.
      lbu_pl F_1a12c D_1a12c Hb11 Eb11.
      stepz F_1a130 D_1a130.
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
    exists r, msteps RSEGS (mkst regs (0x1a1d0 : word) m rom) (mkst r (0x1a200 : word) m rom)
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
    - stepz F_1a134 D_1a134.
      stepz F_1a138 D_1a138.
      stepz F_1a13c D_1a13c.
      stepz F_1a140 D_1a140.
      stepz F_1a144 D_1a144.
      stepz F_1a148 D_1a148.
      stepz F_1a14c D_1a14c.
      lbu_pl F_1a150 D_1a150 Hb12 Eb12.
      lbu_pl F_1a154 D_1a154 Hb13 Eb13.
      lbu_pl F_1a158 D_1a158 Hb14 Eb14.
      lbu_pl F_1a15c D_1a15c Hb15 Eb15.
      stepz F_1a160 D_1a160.
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
    exists r, msteps RSEGS (mkst regs (0x1a200 : word) m rom) (mkst r (0x1a224 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 30 = Z_to_bv 64 (p + 16)
      /\ lkeeps LB regs r.
  Proof.
    intros regs A B p RC R14 R13 RT31 RT8 RT9 RT18 Hp1 Hp2.
    eexists. split.
    - stepz F_1a164 D_1a164.
      stepz F_1a168 D_1a168.
      stepz F_1a16c D_1a16c.
      stepz F_1a170 D_1a170.
      stepz F_1a174 D_1a174.
      stepz F_1a178 D_1a178.
      stepz F_1a17c D_1a17c.
      stepz F_1a180 D_1a180.
      stepz F_1a184 D_1a184.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.




  Lemma d16_body : forall regs (A B p c : Z),
    getr regs 15 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x1a288 : word) m rom) (mkst r (0x1a350 : word) m rom)
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
    exists r, msteps RSEGS (mkst regs (0x1a160 : word) m rom) (mkst r (0x1a224 : word) m rom)
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
    exists r, msteps RSEGS (mkst regs (0x1a288 : word) m rom) (mkst r (0x1a354 : word) m rom)
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
      assert (E11 : getr r1 11 = Z_to_bv 64 15) by (rewrite (K1 11%bv) by (cbv; tauto); exact R11).
      eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_1a2b4 D_1a2b4 ltac:(condZ).
        apply mst_refl.
      + gres. rewrite A1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite B1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite C1. zbv.
      + gres. rewrite N1. zbv.
      + gres. exact E11.
      + solve_ka.
    - destruct (d16_body regs _ _ (q + Z.of_nat n) _ RC R14 R13 RN ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & N1 & K1).
      assert (E11 : getr r1 11 = Z_to_bv 64 15) by (rewrite (K1 11%bv) by (cbv; tauto); exact R11).
      rewrite <- adler_fold_pair_eta, <- adler_fold_bytes_add in A1, B1.
      replace (q + Z.of_nat n + 16) with (q + Z.of_nat (n + 16)) in C1 by lia.
      replace (16 * Z.of_nat (S (S k)) + rest - 16) with (16 * Z.of_nat (S k) + rest) in N1 by lia.
      destruct (IH r1 ab q (n + 16)%nat rest C1 A1 B1 N1 E11 Hrest Hq ltac:(lia))
        as (r2 & M2 & A2 & B2 & C2 & N2 & E2 & K2).
      eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_1a2b4 D_1a2b4 ltac:(condZ).
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
    exists r, msteps RSEGS (mkst regs (0x1a160 : word) m rom) (mkst r (0x1a228 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 30 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S k))
      /\ lkeeps LB regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n RC R14 R13 RE Hq Hfit.
    - destruct (b16_body regs _ _ (q + Z.of_nat n) RC R14 R13 ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & K1).
      assert (E29 : getr r1 29 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat 1)) by (rewrite (K1 29%bv) by (cbv; tauto); exact RE).
      eexists. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_1a188 D_1a188 ltac:(condZ).
        apply mst_refl.
      + gres. rewrite A1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite B1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite C1. zbv.
      + solve_ka.
    - destruct (b16_body regs _ _ (q + Z.of_nat n) RC R14 R13 ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & K1).
      assert (E29 : getr r1 29 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S (S k)))) by (rewrite (K1 29%bv) by (cbv; tauto); exact RE).
      rewrite <- adler_fold_pair_eta, <- adler_fold_bytes_add in A1, B1.
      replace (q + Z.of_nat n + 16) with (q + Z.of_nat (n + 16)) in C1 by lia.
      replace (q + Z.of_nat n + 16 * Z.of_nat (S (S k))) with (q + Z.of_nat (n + 16) + 16 * Z.of_nat (S k)) in E29 by lia.
      destruct (IH r1 ab q (n + 16)%nat C1 A1 B1 E29 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & C2 & K2).
      eexists. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_1a188 D_1a188 ltac:(condZ).
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
    exists r, msteps RSEGS (mkst regs (0x1a098 : word) m rom) (mkst r (0x1a0b0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps LS regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R11 R12 R14 R13 Hq Hfit.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + lbu_pl F_19ffc D_19ffc Hb0 Eb0.
        stepz F_1a000 D_1a000. stepz F_1a004 D_1a004. stepz F_1a008 D_1a008. stepz F_1a00c D_1a00c.
        stepb_ft F_1a010 D_1a010 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x1a098 : word) m rom)
               (fun r => getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps LS regs r)).
      { eexists. split.
        - lbu_pl F_19ffc D_19ffc Hb0 Eb0.
          stepz F_1a000 D_1a000. stepz F_1a004 D_1a004. stepz F_1a008 D_1a008. stepz F_1a00c D_1a00c.
          stepb_tk F_1a010 D_1a010 ltac:(condZ).
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
    exists r, msteps RSEGS (mkst regs (0x1a35c : word) m rom) (mkst r (0x1a374 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps LT regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R15 R12 R14 R13 Hq Hfit.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + lbu_pl F_1a2c0 D_1a2c0 Hb0 Eb0.
        stepz F_1a2c4 D_1a2c4. stepz F_1a2c8 D_1a2c8. stepz F_1a2cc D_1a2cc. stepz F_1a2d0 D_1a2d0.
        stepb_ft F_1a2d4 D_1a2d4 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x1a35c : word) m rom)
               (fun r => getr r 15 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps LT regs r)).
      { eexists. split.
        - lbu_pl F_1a2c0 D_1a2c0 Hb0 Eb0.
          stepz F_1a2c4 D_1a2c4. stepz F_1a2c8 D_1a2c8. stepz F_1a2cc D_1a2cc. stepz F_1a2d0 D_1a2d0.
          stepb_tk F_1a2d4 D_1a2d4 ltac:(condZ).
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
    exists r, msteps RSEGS (mkst regs (0x1a0b0 : word) m rom) (mkst r (0x1a100 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((B mod BASE) * 2 ^ 16) (csub A))
      /\ lkeeps LM regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range B HB) as Ht. pose proof (amag_q_range B HB) as Hq.
    eexists. split; [|split].
    - stepz F_1a014 D_1a014. stepz F_1a018 D_1a018. step_auipc F_1a01c D_1a01c. stepz F_1a020 D_1a020.
      stepz F_1a024 D_1a024.
      ld_amag F_1a028 D_1a028.
      stepi F_1a02c D_1a02c; znorm. rewrite (zv_sltu 65520 A) by lia.
      stepz F_1a030 D_1a030.
      stepz F_1a034 D_1a034. rewrite land_negflag.
      stepz F_1a038 D_1a038. rewrite (csub_machine A) by (lia || reflexivity).
      mulhu_z F_1a03c D_1a03c B.
      stepz F_1a040 D_1a040.
      srli_z F_1a044 D_1a044 (B - amag_t B).
      stepz F_1a048 D_1a048.
      srli_z F_1a04c D_1a04c (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_1a050 D_1a050.
      stepz F_1a054 D_1a054.
      stepz F_1a058 D_1a058. rewrite (amag_mod B HB).
      stepz F_1a05c D_1a05c.
      stepz F_1a060 D_1a060.
      apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma tmod_run : forall regs (A B : Z),
    getr regs 10 = Z_to_bv 64 AMREF -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps RSEGS (mkst regs (0x1a374 : word) m rom) (mkst r (0x1a3b8 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ lkeeps LR regs r.
  Proof.
    intros regs A B R10 R14 R13 HA HB.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split]].
    - ld_amag F_1a2d8 D_1a2d8.
      mulhu_z F_1a2dc D_1a2dc A.
      mulhu_z F_1a2e0 D_1a2e0 B.
      stepz F_1a2e4 D_1a2e4.
      srli_z F_1a2e8 D_1a2e8 (A - amag_t A).
      stepz F_1a2ec D_1a2ec.
      stepz F_1a2f0 D_1a2f0.
      srli_z F_1a2f4 D_1a2f4 (B - amag_t B).
      stepz F_1a2f8 D_1a2f8.
      stepz F_1a2fc D_1a2fc. stepz F_1a300 D_1a300.
      srli_z F_1a304 D_1a304 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      srli_z F_1a308 D_1a308 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_1a30c D_1a30c. stepz F_1a310 D_1a310.
      stepz F_1a314 D_1a314. rewrite (amag_mod A HA).
      stepz F_1a318 D_1a318. rewrite (amag_mod B HB).
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma comb_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    exists r, msteps RSEGS (mkst regs (0x1a3b8 : word) m rom) (mkst r (0x1a3c0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor (B * 2 ^ 16) A)
      /\ lkeeps LR regs r.
  Proof.
    intros regs A B R14 R13.
    eexists. split; [|split].
    - stepz F_1a31c D_1a31c. stepz F_1a320 D_1a320. apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma bmod_run : forall regs (A B bp rem i : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 17 = Z_to_bv 64 4223091239536077 -> getr regs 7 = Z_to_bv 64 65521 ->
    getr regs 15 = Z_to_bv 64 bp -> getr regs 5 = Z_to_bv 64 5552 ->
    getr regs 12 = Z_to_bv 64 rem -> getr regs 16 = Z_to_bv 64 i ->
    0 <= A < two64 -> 0 <= B < two64 -> 0 <= rem < two64 ->
    exists r, msteps RSEGS (mkst regs (0x1a228 : word) m rom) (mkst r (0x1a26c : word) m rom)
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
    - mulhu_z F_1a18c D_1a18c A.
      mulhu_z F_1a190 D_1a190 B.
      stepz F_1a194 D_1a194.
      srli_z F_1a198 D_1a198 (A - amag_t A).
      stepz F_1a19c D_1a19c.
      stepz F_1a1a0 D_1a1a0.
      srli_z F_1a1a4 D_1a1a4 (B - amag_t B).
      stepz F_1a1a8 D_1a1a8.
      stepz F_1a1ac D_1a1ac.
      srli_z F_1a1b0 D_1a1b0 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      stepz F_1a1b4 D_1a1b4.
      stepz F_1a1b8 D_1a1b8. rewrite (amag_mod A HA).
      srli_z F_1a1bc D_1a1bc rem.
      srli_z F_1a1c0 D_1a1c0 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_1a1c4 D_1a1c4.
      stepz F_1a1c8 D_1a1c8. rewrite (amag_mod B HB).
      stepz F_1a1cc D_1a1cc.
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
