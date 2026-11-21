(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S7AdlerBase S7Adler_code FuzzAdlerLib.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold csub lo16 hi16 byte_at.

Definition KA : list reg := [1; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition LD : list reg := [1; 2; 3; 4; 7; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LS : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LT : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LM : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LR : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LE : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%bv.
Definition LB : list reg := [1; 2; 3; 4; 5; 6; 7; 10; 11; 12; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29]%bv.

Definition AMREF : Z := 66364.
Definition AMREF2 : Z := 66264.

Section ADL.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m).
  #[local] Abbreviation BS := (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m).

  Lemma rd1 : forall a, adr0 <= a < adr0 + len0 ->
    exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 a) 1 = Some [b] /\ Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (BA a).
  Proof.
    intros a Ha. destruct (Hrd (a - adr0) ltac:(lia)) as [b Hb].
    replace (adr0 + (a - adr0)) with a in Hb by lia.
    exists b. split; [exact Hb | apply (rdn_byte_at_v (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)), Hb].
  Qed.

  Lemma BA_range : forall a, 0 <= BA a < 256.
  Proof. intros. apply byte_at_range. Qed.

  Lemma rd_amagic : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 AMAG) 8 = Some amag_bs.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17230 : word) m rom) (mkst r retw m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a [BA adr0])
      /\ keeps_cs regs r.
  Proof.
    intros regs retw a Hret R1 R10 R11 R12 Ha Hl.
    destruct (rd1 adr0 ltac:(lia)) as (b0 & Hb0 & Eb0).
    pose proof (BA_range adr0) as Hb. pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split; [|split].
    - stepz F_1712c D_1712c. rewrite (hi16_machine a) by lia.
      stepz F_17130 D_17130.
      stepz F_17134 D_17134.
      stepi F_17138 D_17138; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_ft F_1713c D_1713c ltac:(condZ).
      lbu_pl F_17140 D_17140 Hb0 Eb0.
      stepz F_17144 D_17144. stepz F_17148 D_17148. stepz F_1714c D_1714c. stepz F_17150 D_17150.
      stepz F_17154 D_17154.
      stepi F_17158 D_17158; znorm. rewrite (zv_sltu 65520 (lo16 a + BA adr0)) by lia.
      stepz F_1715c D_1715c.
      stepz F_17160 D_17160. rewrite land_negflag.
      stepz F_17164 D_17164.
      stepz F_17168 D_17168. rewrite (csub_machine (lo16 a + BA adr0)) by (lia || reflexivity).
      stepz F_1716c D_1716c.
      (* BA's RunCtx is resolved at the end of the term, AFTER a term-level ltac:(lia) runs *)
      pose proof (csub_nonneg (lo16 a + BA adr0)) as Hc1. specialize (Hc1 ltac:(lia)).
      stepi F_17170 D_17170; znorm. rewrite (zv_sltu 65520 (csub (lo16 a + BA adr0) + hi16 a)) by lia.
      stepz F_17174 D_17174.
      stepz F_17178 D_17178.
      stepz F_1717c D_1717c.
      stepz F_17180 D_17180. rewrite land_negflag.
      stepz F_17184 D_17184. rewrite (csub16_machine (csub (lo16 a + BA adr0) + hi16 a)) by (lia || reflexivity).
      stepz F_17188 D_17188.
      stepret F_1718c D_1718c retw ltac:(rwR; reflexivity).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x174a8 : word) m rom) (mkst r (0x174e8 : word) m rom)
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
    - lbu_pl F_173a4 D_173a4 Hb0 Eb0.
      lbu_pl F_173a8 D_173a8 Hb1 Eb1.
      lbu_pl F_173ac D_173ac Hb2 Eb2.
      lbu_pl F_173b0 D_173b0 Hb3 Eb3.
      stepz F_173b4 D_173b4.
      stepz F_173b8 D_173b8.
      stepz F_173bc D_173bc.
      stepz F_173c0 D_173c0.
      stepz F_173c4 D_173c4.
      stepz F_173c8 D_173c8.
      stepz F_173cc D_173cc.
      lbu_pl F_173d0 D_173d0 Hb4 Eb4.
      lbu_pl F_173d4 D_173d4 Hb5 Eb5.
      lbu_pl F_173d8 D_173d8 Hb6 Eb6.
      lbu_pl F_173dc D_173dc Hb7 Eb7.
      stepz F_173e0 D_173e0.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x174e8 : word) m rom) (mkst r (0x17518 : word) m rom)
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
    - stepz F_173e4 D_173e4.
      stepz F_173e8 D_173e8.
      stepz F_173ec D_173ec.
      stepz F_173f0 D_173f0.
      stepz F_173f4 D_173f4.
      stepz F_173f8 D_173f8.
      stepz F_173fc D_173fc.
      lbu_pl F_17400 D_17400 Hb8 Eb8.
      lbu_pl F_17404 D_17404 Hb9 Eb9.
      lbu_pl F_17408 D_17408 Hb10 Eb10.
      lbu_pl F_1740c D_1740c Hb11 Eb11.
      stepz F_17410 D_17410.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17518 : word) m rom) (mkst r (0x17548 : word) m rom)
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
    - stepz F_17414 D_17414.
      stepz F_17418 D_17418.
      stepz F_1741c D_1741c.
      stepz F_17420 D_17420.
      stepz F_17424 D_17424.
      stepz F_17428 D_17428.
      stepz F_1742c D_1742c.
      lbu_pl F_17430 D_17430 Hb12 Eb12.
      lbu_pl F_17434 D_17434 Hb13 Eb13.
      lbu_pl F_17438 D_17438 Hb14 Eb14.
      lbu_pl F_1743c D_1743c Hb15 Eb15.
      stepz F_17440 D_17440.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17548 : word) m rom) (mkst r (0x17570 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 15 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ lkeeps LD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT16 RT17 RT5 RT6 RN Hp1 Hp2.
    eexists. split.
    - stepz F_17444 D_17444.
      stepz F_17448 D_17448.
      stepz F_1744c D_1744c.
      stepz F_17450 D_17450.
      stepz F_17454 D_17454.
      stepz F_17458 D_17458.
      stepz F_1745c D_1745c.
      stepz F_17460 D_17460.
      stepz F_17464 D_17464.
      stepz F_17468 D_17468.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma b16_seg0 : forall regs (A B p : Z),
    getr regs 30 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17380 : word) m rom) (mkst r (0x173c0 : word) m rom)
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
    - lbu_pl F_1727c D_1727c Hb0 Eb0.
      lbu_pl F_17280 D_17280 Hb1 Eb1.
      lbu_pl F_17284 D_17284 Hb2 Eb2.
      lbu_pl F_17288 D_17288 Hb3 Eb3.
      stepz F_1728c D_1728c.
      stepz F_17290 D_17290.
      stepz F_17294 D_17294.
      stepz F_17298 D_17298.
      stepz F_1729c D_1729c.
      stepz F_172a0 D_172a0.
      stepz F_172a4 D_172a4.
      lbu_pl F_172a8 D_172a8 Hb4 Eb4.
      lbu_pl F_172ac D_172ac Hb5 Eb5.
      lbu_pl F_172b0 D_172b0 Hb6 Eb6.
      lbu_pl F_172b4 D_172b4 Hb7 Eb7.
      stepz F_172b8 D_172b8.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x173c0 : word) m rom) (mkst r (0x173f0 : word) m rom)
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
    - stepz F_172bc D_172bc.
      stepz F_172c0 D_172c0.
      stepz F_172c4 D_172c4.
      stepz F_172c8 D_172c8.
      stepz F_172cc D_172cc.
      stepz F_172d0 D_172d0.
      stepz F_172d4 D_172d4.
      lbu_pl F_172d8 D_172d8 Hb8 Eb8.
      lbu_pl F_172dc D_172dc Hb9 Eb9.
      lbu_pl F_172e0 D_172e0 Hb10 Eb10.
      lbu_pl F_172e4 D_172e4 Hb11 Eb11.
      stepz F_172e8 D_172e8.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x173f0 : word) m rom) (mkst r (0x17420 : word) m rom)
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
    - stepz F_172ec D_172ec.
      stepz F_172f0 D_172f0.
      stepz F_172f4 D_172f4.
      stepz F_172f8 D_172f8.
      stepz F_172fc D_172fc.
      stepz F_17300 D_17300.
      stepz F_17304 D_17304.
      lbu_pl F_17308 D_17308 Hb12 Eb12.
      lbu_pl F_1730c D_1730c Hb13 Eb13.
      lbu_pl F_17310 D_17310 Hb14 Eb14.
      lbu_pl F_17314 D_17314 Hb15 Eb15.
      stepz F_17318 D_17318.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17420 : word) m rom) (mkst r (0x17444 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 30 = Z_to_bv 64 (p + 16)
      /\ lkeeps LB regs r.
  Proof.
    intros regs A B p RC R14 R13 RT31 RT8 RT9 RT18 Hp1 Hp2.
    eexists. split.
    - stepz F_1731c D_1731c.
      stepz F_17320 D_17320.
      stepz F_17324 D_17324.
      stepz F_17328 D_17328.
      stepz F_1732c D_1732c.
      stepz F_17330 D_17330.
      stepz F_17334 D_17334.
      stepz F_17338 D_17338.
      stepz F_1733c D_1733c.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.




  Lemma d16_body : forall regs (A B p c : Z),
    getr regs 15 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x174a8 : word) m rom) (mkst r (0x17570 : word) m rom)
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17380 : word) m rom) (mkst r (0x17444 : word) m rom)
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x174a8 : word) m rom) (mkst r (0x17574 : word) m rom)
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
        stepb_ft F_1746c D_1746c ltac:(condZ).
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
        stepb_tk F_1746c D_1746c ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17380 : word) m rom) (mkst r (0x17448 : word) m rom)
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
        stepb_ft F_17340 D_17340 ltac:(condZ).
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
        stepb_tk F_17340 D_17340 ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x172b8 : word) m rom) (mkst r (0x172d0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps LS regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R11 R12 R14 R13 Hq Hfit.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + lbu_pl F_171b4 D_171b4 Hb0 Eb0.
        stepz F_171b8 D_171b8. stepz F_171bc D_171bc. stepz F_171c0 D_171c0. stepz F_171c4 D_171c4.
        stepb_ft F_171c8 D_171c8 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x172b8 : word) m rom)
               (fun r => getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps LS regs r)).
      { eexists. split.
        - lbu_pl F_171b4 D_171b4 Hb0 Eb0.
          stepz F_171b8 D_171b8. stepz F_171bc D_171bc. stepz F_171c0 D_171c0. stepz F_171c4 D_171c4.
          stepb_tk F_171c8 D_171c8 ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1757c : word) m rom) (mkst r (0x17594 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps LT regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R15 R12 R14 R13 Hq Hfit.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + lbu_pl F_17478 D_17478 Hb0 Eb0.
        stepz F_1747c D_1747c. stepz F_17480 D_17480. stepz F_17484 D_17484. stepz F_17488 D_17488.
        stepb_ft F_1748c D_1748c ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x1757c : word) m rom)
               (fun r => getr r 15 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps LT regs r)).
      { eexists. split.
        - lbu_pl F_17478 D_17478 Hb0 Eb0.
          stepz F_1747c D_1747c. stepz F_17480 D_17480. stepz F_17484 D_17484. stepz F_17488 D_17488.
          stepb_tk F_1748c D_1748c ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x172d0 : word) m rom) (mkst r (0x17320 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((B mod BASE) * 2 ^ 16) (csub A))
      /\ lkeeps LM regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range B HB) as Ht. pose proof (amag_q_range B HB) as Hq.
    eexists. split; [|split].
    - stepz F_171cc D_171cc. stepz F_171d0 D_171d0. step_auipc F_171d4 D_171d4. stepz F_171d8 D_171d8.
      stepz F_171dc D_171dc.
      ld_amag F_171e0 D_171e0.
      stepi F_171e4 D_171e4; znorm. rewrite (zv_sltu 65520 A) by lia.
      stepz F_171e8 D_171e8.
      stepz F_171ec D_171ec. rewrite land_negflag.
      stepz F_171f0 D_171f0. rewrite (csub_machine A) by (lia || reflexivity).
      mulhu_z F_171f4 D_171f4 B.
      stepz F_171f8 D_171f8.
      srli_z F_171fc D_171fc (B - amag_t B).
      stepz F_17200 D_17200.
      srli_z F_17204 D_17204 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_17208 D_17208.
      stepz F_1720c D_1720c.
      stepz F_17210 D_17210. rewrite (amag_mod B HB).
      stepz F_17214 D_17214.
      stepz F_17218 D_17218.
      apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma tmod_run : forall regs (A B : Z),
    getr regs 10 = Z_to_bv 64 AMREF -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17594 : word) m rom) (mkst r (0x175d8 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ lkeeps LR regs r.
  Proof.
    intros regs A B R10 R14 R13 HA HB.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split]].
    - ld_amag F_17490 D_17490.
      mulhu_z F_17494 D_17494 A.
      mulhu_z F_17498 D_17498 B.
      stepz F_1749c D_1749c.
      srli_z F_174a0 D_174a0 (A - amag_t A).
      stepz F_174a4 D_174a4.
      stepz F_174a8 D_174a8.
      srli_z F_174ac D_174ac (B - amag_t B).
      stepz F_174b0 D_174b0.
      stepz F_174b4 D_174b4. stepz F_174b8 D_174b8.
      srli_z F_174bc D_174bc (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      srli_z F_174c0 D_174c0 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_174c4 D_174c4. stepz F_174c8 D_174c8.
      stepz F_174cc D_174cc. rewrite (amag_mod A HA).
      stepz F_174d0 D_174d0. rewrite (amag_mod B HB).
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma comb_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x175d8 : word) m rom) (mkst r (0x175e0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor (B * 2 ^ 16) A)
      /\ lkeeps LR regs r.
  Proof.
    intros regs A B R14 R13.
    eexists. split; [|split].
    - stepz F_174d4 D_174d4. stepz F_174d8 D_174d8. apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma bmod_run : forall regs (A B bp rem i : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 17 = Z_to_bv 64 4223091239536077 -> getr regs 7 = Z_to_bv 64 65521 ->
    getr regs 15 = Z_to_bv 64 bp -> getr regs 5 = Z_to_bv 64 5552 ->
    getr regs 12 = Z_to_bv 64 rem -> getr regs 16 = Z_to_bv 64 i ->
    0 <= A < two64 -> 0 <= B < two64 -> 0 <= rem < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17448 : word) m rom) (mkst r (0x1748c : word) m rom)
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
    - mulhu_z F_17344 D_17344 A.
      mulhu_z F_17348 D_17348 B.
      stepz F_1734c D_1734c.
      srli_z F_17350 D_17350 (A - amag_t A).
      stepz F_17354 D_17354.
      stepz F_17358 D_17358.
      srli_z F_1735c D_1735c (B - amag_t B).
      stepz F_17360 D_17360.
      stepz F_17364 D_17364.
      srli_z F_17368 D_17368 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      stepz F_1736c D_1736c.
      stepz F_17370 D_17370. rewrite (amag_mod A HA).
      srli_z F_17374 D_17374 rem.
      srli_z F_17378 D_17378 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_1737c D_1737c.
      stepz F_17380 D_17380. rewrite (amag_mod B HB).
      stepz F_17384 D_17384.
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.
End ADL.
