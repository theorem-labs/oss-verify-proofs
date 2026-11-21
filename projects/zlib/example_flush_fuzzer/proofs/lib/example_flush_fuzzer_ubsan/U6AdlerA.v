(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U6AdlerBase U6Adler_code FuzzAdlerLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold csub lo16 hi16 byte_at.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ULD : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 26; 27; 28; 29; 30; 31]%bv.
Definition ULB : list reg := [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 23; 24; 28; 29; 30; 31]%bv.
Definition ULS : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition ULT : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition ULM : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition ULR : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition ULE : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
Definition ULH : list reg := ULR.

Definition NEG (k : Z) : Z := 18446744073709551616 - k.

Definition CK16 (regs : bvmap 5 word) : Prop :=
  getr regs 10 = Z_to_bv 64 (NEG 1) /\ getr regs 15 = Z_to_bv 64 (NEG 3) /\ getr regs 16 = Z_to_bv 64 (NEG 4)
  /\ getr regs 17 = Z_to_bv 64 (NEG 5) /\ getr regs 5 = Z_to_bv 64 (NEG 6) /\ getr regs 6 = Z_to_bv 64 (NEG 7)
  /\ getr regs 7 = Z_to_bv 64 (NEG 8) /\ getr regs 28 = Z_to_bv 64 (NEG 9) /\ getr regs 29 = Z_to_bv 64 (NEG 10)
  /\ getr regs 30 = Z_to_bv 64 (NEG 11) /\ getr regs 31 = Z_to_bv 64 (NEG 12) /\ getr regs 8 = Z_to_bv 64 (NEG 13)
  /\ getr regs 9 = Z_to_bv 64 (NEG 14) /\ getr regs 18 = Z_to_bv 64 (NEG 15) /\ getr regs 19 = Z_to_bv 64 (NEG 16)
  /\ getr regs 20 = Z_to_bv 64 (NEG 17).

Definition CKR : list reg := [10; 15; 16; 17; 5; 6; 7; 28; 29; 30; 31; 8; 9; 18; 19; 20]%bv.

Lemma CK16_kept : forall l r1 r2, CK16 r1 -> lkeeps l r1 r2 -> incl CKR l -> CK16 r2.
Proof.
  intros l r1 r2 H K Hi. unfold CK16 in *.
  repeat match goal with |- _ /\ _ => split end;
  (rewrite (K _) by (apply Hi; cbv; tauto)); tauto.
Qed.

Lemma ucnt_S : forall k : nat, (1 <= k <= 400)%nat ->
  sx32 ((two64 - Z.of_nat (S k) + 1) mod two32) = two64 - Z.of_nat k.
Proof.
  intros k Hk. unfold sx32.
  replace (two64 - Z.of_nat (S k) + 1) with ((two32 - Z.of_nat k) + 4294967295 * two32) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia.
  destruct (Z.ltb_spec (two32 - Z.of_nat k) 2147483648); lia.
Qed.
Lemma ucnt_O : sx32 ((two64 - Z.of_nat 1 + 1) mod two32) = 0.
Proof. reflexivity. Qed.

Section UADL.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn USEGS m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at USEGS m).
  #[local] Abbreviation BS := (bytes_at USEGS m).

  Lemma rd1 : forall a, adr0 <= a < adr0 + len0 ->
    exists b : byte, rdn USEGS m (Z_to_bv 64 a) 1 = Some [b] /\ Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (BA a).
  Proof.
    intros a Ha. destruct (Hrd (a - adr0) ltac:(lia)) as [b Hb].
    replace (adr0 + (a - adr0)) with a in Hb by lia.
    exists b. split; [exact Hb | apply (rdn_byte_at_v USEGS), Hb].
  Qed.

  Lemma BA_range : forall a, 0 <= BA a < 256.
  Proof. intros. apply byte_at_range. Qed.

  Lemma rd_amagic : rdn USEGS m (Z_to_bv 64 AMAG) 8 = Some amag_bs.
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
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with AMAG by (unfold AMAG; lia) end;
        exact rd_amagic
      | exact amag_bs_v ]
    | step_simpl; gres ].

  Ltac step_auipc F D := stepi F D; znorm;
    try match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.

  Ltac negz :=
    match goal with |- context [regupd _ _ (Z_to_bv 64 (Zneg ?p))] =>
      let v := eval cbv in (18446744073709551616 - Zpos p) in
      replace (Z_to_bv 64 (Zneg p) : word) with (Z_to_bv 64 v : word) by (apply zv_eq; reflexivity) end.

  Lemma AMAGIC_range : 0 <= AMAGIC < two64.
  Proof. rewrite AMAGIC_val. lia. Qed.

  Ltac srli_z F D x := stepi F D; znorm; rewrite (zv_srli x) by first [assumption | lia
      | apply amag_u_range; assumption | apply amag_v_range; assumption].
  Ltac mulhu_z F D x := stepi F D; znorm;
      first [ rewrite (zv_mulhu x 4223091239536077) by first [assumption | rewrite <- AMAGIC_val; apply AMAGIC_range]
            | rewrite (zv_mulhu x AMAGIC) by first [assumption | apply AMAGIC_range] ];
      first [ change (x * 4223091239536077 / two64) with (amag_t x) | change (x * AMAGIC / two64) with (amag_t x) ].


  Lemma ua1_run : forall regs (a : Z),
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 1 ->
    0 <= a < two64 -> 1 <= len0 -> 1 <= adr0 ->
    exists r, msteps USEGS (mkst regs (0x1aa44 : word) m rom) (mkst r (0x1aefc : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a [BA adr0])
      /\ lkeeps ULH regs r.
  Proof.
    intros regs a R10 R11 R12 Ha Hl Hadr.
    destruct (rd1 adr0 ltac:(lia)) as (b0 & Hb0 & Eb0).
    pose proof (BA_range adr0) as Hb. pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split; [|split].
    - stepz F_1a93c D_1a93c. rewrite (hi16_machine a) by lia.
      stepz F_1a940 D_1a940.
      stepz F_1a944 D_1a944.
      stepi F_1a948 D_1a948; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_ft F_1a94c D_1a94c ltac:(condZ).
      stepb_ft F_1a950 D_1a950 ltac:(condZ).
      lbu_pl F_1a954 D_1a954 Hb0 Eb0.
      stepz F_1a958 D_1a958. stepz F_1a95c D_1a95c. stepz F_1a960 D_1a960. stepz F_1a964 D_1a964.
      stepz F_1a968 D_1a968.
      stepi F_1a96c D_1a96c; znorm. rewrite (zv_sltu 65520 (lo16 a + BA adr0)) by lia.
      stepz F_1a970 D_1a970.
      stepz F_1a974 D_1a974. rewrite land_negflag.
      stepz F_1a978 D_1a978.
      stepz F_1a97c D_1a97c. rewrite (csub_machine (lo16 a + BA adr0)) by (lia || reflexivity).
      stepz F_1a980 D_1a980.
      pose proof (csub_nonneg (lo16 a + BA adr0) ltac:(lia)) as Hc1.
      stepi F_1a984 D_1a984; znorm. rewrite (zv_sltu 65520 (csub (lo16 a + BA adr0) + hi16 a)) by lia.
      stepz F_1a988 D_1a988.
      stepz F_1a98c D_1a98c.
      stepz F_1a990 D_1a990.
      stepz F_1a994 D_1a994. rewrite land_negflag.
      stepz F_1a998 D_1a998. rewrite (csub16_machine (csub (lo16 a + BA adr0) + hi16 a)) by (lia || reflexivity).
      stepz F_1a99c D_1a99c.
      stepz F_1a9a0 D_1a9a0.
      apply mst_refl.
    - gres. rewrite <- (adler_len1_path a (BA adr0)) by lia. cbv zeta.
      rewrite <- !csub_sltu, <- csub_sltu_shift16. reflexivity.
    - solve_ka.
  Qed.

  Lemma uhalves_run : forall regs (a : Z),
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    0 <= a < two64 -> 0 <= len0 -> len0 <> 1 -> 1 <= adr0 ->
    exists r, msteps USEGS (mkst regs (0x1aa44 : word) m rom) (mkst r (0x1aab0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (lo16 a) /\ getr r 13 = Z_to_bv 64 (hi16 a) /\ getr r 10 = Z_to_bv 64 1
      /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 12 = Z_to_bv 64 len0
      /\ lkeeps ULH regs r.
  Proof.
    intros regs a R10 R11 R12 Ha Hl H1 Hadr.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split.
    - stepz F_1a93c D_1a93c. rewrite (hi16_machine a) by lia.
      stepz F_1a940 D_1a940.
      stepz F_1a944 D_1a944.
      stepi F_1a948 D_1a948; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_tk F_1a94c D_1a94c ltac:(condZ).
      stepb_ft F_1a9a4 D_1a9a4 ltac:(condZ).
      apply mst_refl.
    - post.
  Qed.


  Ltac ck16 H := pose proof H as CK; unfold CK16 in CK;
    destruct CK as (C10 & C15 & C16 & C17 & C5 & C6 & C7 & C28 & C29 & C30 & C31 & C8 & C9 & C18 & C19 & C20).

  Lemma ud16_chk : forall regs (p : Z),
    CK16 regs -> getr regs 11 = Z_to_bv 64 p -> 0 <= p -> p + 17 <= two64 ->
    exists r, msteps USEGS (mkst regs (0x1ad74 : word) m rom) (mkst r (0x1adb4 : word) m rom)
      /\ r = regs.
  Proof.
    intros regs p HCK R11 Hp0 Hp. ck16 HCK. unfold NEG in *.
    eexists. split; [|reflexivity].
    stepb_ft F_1ac6c D_1ac6c ltac:(condZ). stepb_ft F_1ac70 D_1ac70 ltac:(condZ).
    stepb_ft F_1ac74 D_1ac74 ltac:(condZ). stepb_ft F_1ac78 D_1ac78 ltac:(condZ).
    stepb_ft F_1ac7c D_1ac7c ltac:(condZ). stepb_ft F_1ac80 D_1ac80 ltac:(condZ).
    stepb_ft F_1ac84 D_1ac84 ltac:(condZ). stepb_ft F_1ac88 D_1ac88 ltac:(condZ).
    stepb_ft F_1ac8c D_1ac8c ltac:(condZ). stepb_ft F_1ac90 D_1ac90 ltac:(condZ).
    stepb_ft F_1ac94 D_1ac94 ltac:(condZ). stepb_ft F_1ac98 D_1ac98 ltac:(condZ).
    stepb_ft F_1ac9c D_1ac9c ltac:(condZ). stepb_ft F_1aca0 D_1aca0 ltac:(condZ).
    stepb_ft F_1aca4 D_1aca4 ltac:(condZ). stepb_ft F_1aca8 D_1aca8 ltac:(condZ).
    apply mst_refl.
  Qed.

  Lemma ub16_chk : forall regs (p : Z),
    CK16 regs -> getr regs 26 = Z_to_bv 64 p -> 0 <= p -> p + 17 <= two64 ->
    exists r, msteps USEGS (mkst regs (0x1abd4 : word) m rom) (mkst r (0x1ac14 : word) m rom)
      /\ r = regs.
  Proof.
    intros regs p HCK R26 Hp0 Hp. ck16 HCK. unfold NEG in *.
    eexists. split; [|reflexivity].
    stepb_ft F_1aacc D_1aacc ltac:(condZ). stepb_ft F_1aad0 D_1aad0 ltac:(condZ).
    stepb_ft F_1aad4 D_1aad4 ltac:(condZ). stepb_ft F_1aad8 D_1aad8 ltac:(condZ).
    stepb_ft F_1aadc D_1aadc ltac:(condZ). stepb_ft F_1aae0 D_1aae0 ltac:(condZ).
    stepb_ft F_1aae4 D_1aae4 ltac:(condZ). stepb_ft F_1aae8 D_1aae8 ltac:(condZ).
    stepb_ft F_1aaec D_1aaec ltac:(condZ). stepb_ft F_1aaf0 D_1aaf0 ltac:(condZ).
    stepb_ft F_1aaf4 D_1aaf4 ltac:(condZ). stepb_ft F_1aaf8 D_1aaf8 ltac:(condZ).
    stepb_ft F_1aafc D_1aafc ltac:(condZ). stepb_ft F_1ab00 D_1ab00 ltac:(condZ).
    stepb_ft F_1ab04 D_1ab04 ltac:(condZ). stepb_ft F_1ab08 D_1ab08 ltac:(condZ).
    apply mst_refl.
  Qed.


  Lemma ud16_seg0 : forall regs (A B p c : Z),
    getr regs 11 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1adb4 : word) m rom) (mkst r (0x1adf4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 22 = Z_to_bv 64 (BA (p + 4))
      /\ getr r 23 = Z_to_bv 64 (BA (p + 5))
      /\ getr r 24 = Z_to_bv 64 (BA (p + 6))
      /\ getr r 25 = Z_to_bv 64 (BA (p + 7))
      /\ getr r 11 = Z_to_bv 64 p
      /\ getr r 12 = Z_to_bv 64 c
      /\ lkeeps ULD regs r.
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
    - lbu_pl F_1acac D_1acac Hb0 Eb0.
      lbu_pl F_1acb0 D_1acb0 Hb1 Eb1.
      lbu_pl F_1acb4 D_1acb4 Hb2 Eb2.
      lbu_pl F_1acb8 D_1acb8 Hb3 Eb3.
      stepz F_1acbc D_1acbc.
      stepz F_1acc0 D_1acc0.
      stepz F_1acc4 D_1acc4.
      stepz F_1acc8 D_1acc8.
      stepz F_1accc D_1accc.
      stepz F_1acd0 D_1acd0.
      stepz F_1acd4 D_1acd4.
      lbu_pl F_1acd8 D_1acd8 Hb4 Eb4.
      lbu_pl F_1acdc D_1acdc Hb5 Eb5.
      lbu_pl F_1ace0 D_1ace0 Hb6 Eb6.
      lbu_pl F_1ace4 D_1ace4 Hb7 Eb7.
      stepz F_1ace8 D_1ace8.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ud16_seg1 : forall regs (A B p c : Z),
    getr regs 11 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 22 = Z_to_bv 64 (BA (p + 4)) ->
    getr regs 23 = Z_to_bv 64 (BA (p + 5)) ->
    getr regs 24 = Z_to_bv 64 (BA (p + 6)) ->
    getr regs 25 = Z_to_bv 64 (BA (p + 7)) ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1adf4 : word) m rom) (mkst r (0x1ae24 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 22 = Z_to_bv 64 (BA (p + 8))
      /\ getr r 23 = Z_to_bv 64 (BA (p + 9))
      /\ getr r 24 = Z_to_bv 64 (BA (p + 10))
      /\ getr r 25 = Z_to_bv 64 (BA (p + 11))
      /\ getr r 11 = Z_to_bv 64 p
      /\ getr r 12 = Z_to_bv 64 c
      /\ lkeeps ULD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT22 RT23 RT24 RT25 RN Hp1 Hp2.
    destruct (rd1 (p + 8) ltac:(lia)) as (b8 & Hb8 & Eb8).
    destruct (rd1 (p + 9) ltac:(lia)) as (b9 & Hb9 & Eb9).
    destruct (rd1 (p + 10) ltac:(lia)) as (b10 & Hb10 & Eb10).
    destruct (rd1 (p + 11) ltac:(lia)) as (b11 & Hb11 & Eb11).
    eexists. split.
    - stepz F_1acec D_1acec.
      stepz F_1acf0 D_1acf0.
      stepz F_1acf4 D_1acf4.
      stepz F_1acf8 D_1acf8.
      stepz F_1acfc D_1acfc.
      stepz F_1ad00 D_1ad00.
      stepz F_1ad04 D_1ad04.
      lbu_pl F_1ad08 D_1ad08 Hb8 Eb8.
      lbu_pl F_1ad0c D_1ad0c Hb9 Eb9.
      lbu_pl F_1ad10 D_1ad10 Hb10 Eb10.
      lbu_pl F_1ad14 D_1ad14 Hb11 Eb11.
      stepz F_1ad18 D_1ad18.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ud16_seg2 : forall regs (A B p c : Z),
    getr regs 11 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 22 = Z_to_bv 64 (BA (p + 8)) ->
    getr regs 23 = Z_to_bv 64 (BA (p + 9)) ->
    getr regs 24 = Z_to_bv 64 (BA (p + 10)) ->
    getr regs 25 = Z_to_bv 64 (BA (p + 11)) ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ae24 : word) m rom) (mkst r (0x1ae54 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 22 = Z_to_bv 64 (BA (p + 12))
      /\ getr r 23 = Z_to_bv 64 (BA (p + 13))
      /\ getr r 24 = Z_to_bv 64 (BA (p + 14))
      /\ getr r 25 = Z_to_bv 64 (BA (p + 15))
      /\ getr r 11 = Z_to_bv 64 p
      /\ getr r 12 = Z_to_bv 64 c
      /\ lkeeps ULD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT22 RT23 RT24 RT25 RN Hp1 Hp2.
    destruct (rd1 (p + 12) ltac:(lia)) as (b12 & Hb12 & Eb12).
    destruct (rd1 (p + 13) ltac:(lia)) as (b13 & Hb13 & Eb13).
    destruct (rd1 (p + 14) ltac:(lia)) as (b14 & Hb14 & Eb14).
    destruct (rd1 (p + 15) ltac:(lia)) as (b15 & Hb15 & Eb15).
    eexists. split.
    - stepz F_1ad1c D_1ad1c.
      stepz F_1ad20 D_1ad20.
      stepz F_1ad24 D_1ad24.
      stepz F_1ad28 D_1ad28.
      stepz F_1ad2c D_1ad2c.
      stepz F_1ad30 D_1ad30.
      stepz F_1ad34 D_1ad34.
      lbu_pl F_1ad38 D_1ad38 Hb12 Eb12.
      lbu_pl F_1ad3c D_1ad3c Hb13 Eb13.
      lbu_pl F_1ad40 D_1ad40 Hb14 Eb14.
      lbu_pl F_1ad44 D_1ad44 Hb15 Eb15.
      stepz F_1ad48 D_1ad48.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ud16_seg3 : forall regs (A B p c : Z),
    getr regs 11 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 22 = Z_to_bv 64 (BA (p + 12)) ->
    getr regs 23 = Z_to_bv 64 (BA (p + 13)) ->
    getr regs 24 = Z_to_bv 64 (BA (p + 14)) ->
    getr regs 25 = Z_to_bv 64 (BA (p + 15)) ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ae54 : word) m rom) (mkst r (0x1ae80 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 11 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ getr r 22 = Z_to_bv 64 (p + 16)
      /\ lkeeps ULD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT22 RT23 RT24 RT25 RN Hp1 Hp2.
    eexists. split.
    - stepz F_1ad4c D_1ad4c.
      stepz F_1ad50 D_1ad50.
      stepz F_1ad54 D_1ad54.
      stepz F_1ad58 D_1ad58.
      stepz F_1ad5c D_1ad5c.
      stepz F_1ad60 D_1ad60.
      stepz F_1ad64 D_1ad64.
      stepz F_1ad68 D_1ad68.
      stepz F_1ad6c D_1ad6c.
      stepz F_1ad70 D_1ad70.
      stepz F_1ad74 D_1ad74.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ub16_seg0 : forall regs (A B p cnt : Z),
    getr regs 26 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ac14 : word) m rom) (mkst r (0x1ac54 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA p; BA (p + 1); BA (p + 2); BA (p + 3)]))
      /\ getr r 21 = Z_to_bv 64 (BA (p + 4))
      /\ getr r 22 = Z_to_bv 64 (BA (p + 5))
      /\ getr r 25 = Z_to_bv 64 (BA (p + 6))
      /\ getr r 1 = Z_to_bv 64 (BA (p + 7))
      /\ getr r 26 = Z_to_bv 64 p
      /\ getr r 27 = Z_to_bv 64 cnt
      /\ lkeeps ULB regs r.
  Proof.
    intros regs A B p cnt RC R14 R13 RK Hp1 Hp2.
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
    - lbu_pl F_1ab0c D_1ab0c Hb0 Eb0.
      lbu_pl F_1ab10 D_1ab10 Hb1 Eb1.
      lbu_pl F_1ab14 D_1ab14 Hb2 Eb2.
      lbu_pl F_1ab18 D_1ab18 Hb3 Eb3.
      stepz F_1ab1c D_1ab1c.
      stepz F_1ab20 D_1ab20.
      stepz F_1ab24 D_1ab24.
      stepz F_1ab28 D_1ab28.
      stepz F_1ab2c D_1ab2c.
      stepz F_1ab30 D_1ab30.
      stepz F_1ab34 D_1ab34.
      lbu_pl F_1ab38 D_1ab38 Hb4 Eb4.
      lbu_pl F_1ab3c D_1ab3c Hb5 Eb5.
      lbu_pl F_1ab40 D_1ab40 Hb6 Eb6.
      lbu_pl F_1ab44 D_1ab44 Hb7 Eb7.
      stepz F_1ab48 D_1ab48.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ub16_seg1 : forall regs (A B p cnt : Z),
    getr regs 26 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 21 = Z_to_bv 64 (BA (p + 4)) ->
    getr regs 22 = Z_to_bv 64 (BA (p + 5)) ->
    getr regs 25 = Z_to_bv 64 (BA (p + 6)) ->
    getr regs 1 = Z_to_bv 64 (BA (p + 7)) ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ac54 : word) m rom) (mkst r (0x1ac84 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 4); BA (p + 5); BA (p + 6); BA (p + 7)]))
      /\ getr r 21 = Z_to_bv 64 (BA (p + 8))
      /\ getr r 22 = Z_to_bv 64 (BA (p + 9))
      /\ getr r 25 = Z_to_bv 64 (BA (p + 10))
      /\ getr r 1 = Z_to_bv 64 (BA (p + 11))
      /\ getr r 26 = Z_to_bv 64 p
      /\ getr r 27 = Z_to_bv 64 cnt
      /\ lkeeps ULB regs r.
  Proof.
    intros regs A B p cnt RC R14 R13 RT21 RT22 RT25 RT1 RK Hp1 Hp2.
    destruct (rd1 (p + 8) ltac:(lia)) as (b8 & Hb8 & Eb8).
    destruct (rd1 (p + 9) ltac:(lia)) as (b9 & Hb9 & Eb9).
    destruct (rd1 (p + 10) ltac:(lia)) as (b10 & Hb10 & Eb10).
    destruct (rd1 (p + 11) ltac:(lia)) as (b11 & Hb11 & Eb11).
    eexists. split.
    - stepz F_1ab4c D_1ab4c.
      stepz F_1ab50 D_1ab50.
      stepz F_1ab54 D_1ab54.
      stepz F_1ab58 D_1ab58.
      stepz F_1ab5c D_1ab5c.
      stepz F_1ab60 D_1ab60.
      stepz F_1ab64 D_1ab64.
      lbu_pl F_1ab68 D_1ab68 Hb8 Eb8.
      lbu_pl F_1ab6c D_1ab6c Hb9 Eb9.
      lbu_pl F_1ab70 D_1ab70 Hb10 Eb10.
      lbu_pl F_1ab74 D_1ab74 Hb11 Eb11.
      stepz F_1ab78 D_1ab78.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ub16_seg2 : forall regs (A B p cnt : Z),
    getr regs 26 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 21 = Z_to_bv 64 (BA (p + 8)) ->
    getr regs 22 = Z_to_bv 64 (BA (p + 9)) ->
    getr regs 25 = Z_to_bv 64 (BA (p + 10)) ->
    getr regs 1 = Z_to_bv 64 (BA (p + 11)) ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ac84 : word) m rom) (mkst r (0x1acb4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 8); BA (p + 9); BA (p + 10); BA (p + 11)]))
      /\ getr r 21 = Z_to_bv 64 (BA (p + 12))
      /\ getr r 22 = Z_to_bv 64 (BA (p + 13))
      /\ getr r 25 = Z_to_bv 64 (BA (p + 14))
      /\ getr r 1 = Z_to_bv 64 (BA (p + 15))
      /\ getr r 26 = Z_to_bv 64 p
      /\ getr r 27 = Z_to_bv 64 cnt
      /\ lkeeps ULB regs r.
  Proof.
    intros regs A B p cnt RC R14 R13 RT21 RT22 RT25 RT1 RK Hp1 Hp2.
    destruct (rd1 (p + 12) ltac:(lia)) as (b12 & Hb12 & Eb12).
    destruct (rd1 (p + 13) ltac:(lia)) as (b13 & Hb13 & Eb13).
    destruct (rd1 (p + 14) ltac:(lia)) as (b14 & Hb14 & Eb14).
    destruct (rd1 (p + 15) ltac:(lia)) as (b15 & Hb15 & Eb15).
    eexists. split.
    - stepz F_1ab7c D_1ab7c.
      stepz F_1ab80 D_1ab80.
      stepz F_1ab84 D_1ab84.
      stepz F_1ab88 D_1ab88.
      stepz F_1ab8c D_1ab8c.
      stepz F_1ab90 D_1ab90.
      stepz F_1ab94 D_1ab94.
      lbu_pl F_1ab98 D_1ab98 Hb12 Eb12.
      lbu_pl F_1ab9c D_1ab9c Hb13 Eb13.
      lbu_pl F_1aba0 D_1aba0 Hb14 Eb14.
      lbu_pl F_1aba4 D_1aba4 Hb15 Eb15.
      stepz F_1aba8 D_1aba8.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ub16_seg3 : forall regs (A B p cnt : Z),
    getr regs 26 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 21 = Z_to_bv 64 (BA (p + 12)) ->
    getr regs 22 = Z_to_bv 64 (BA (p + 13)) ->
    getr regs 25 = Z_to_bv 64 (BA (p + 14)) ->
    getr regs 1 = Z_to_bv 64 (BA (p + 15)) ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1acb4 : word) m rom) (mkst r (0x1acdc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 26 = Z_to_bv 64 (p + 16)
      /\ getr r 27 = Z_to_bv 64 (sx32 ((cnt + 1) mod two32))
      /\ lkeeps ULB regs r.
  Proof.
    intros regs A B p cnt RC R14 R13 RT21 RT22 RT25 RT1 RK Hp1 Hp2.
    eexists. split.
    - stepz F_1abac D_1abac.
      stepz F_1abb0 D_1abb0.
      stepz F_1abb4 D_1abb4.
      stepz F_1abb8 D_1abb8.
      stepz F_1abbc D_1abbc.
      stepz F_1abc0 D_1abc0.
      stepz F_1abc4 D_1abc4.
      stepz F_1abc8 D_1abc8.
      stepz F_1abcc D_1abcc.
      stepz F_1abd0 D_1abd0.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.




  Lemma CKR_ULD : incl CKR ULD. Proof. incl_dec. Qed.
  Lemma CKR_ULB : incl CKR ULB. Proof. incl_dec. Qed.

  Lemma ud16_body : forall regs (A B p c : Z),
    CK16 regs ->
    getr regs 11 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ad74 : word) m rom) (mkst r (0x1ae80 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) (BS p 16)))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) (BS p 16)))
      /\ getr r 11 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ getr r 22 = Z_to_bv 64 (p + 16)
      /\ lkeeps ULD regs r.
  Proof.
    intros regs A B p c HCK RC R14 R13 RN Hp1 Hp2.
    destruct (ud16_chk regs p HCK RC ltac:(lia) ltac:(lia)) as (r0 & M0 & E0). subst r0.
    destruct (ud16_seg0 regs A B p c RC R14 R13 RN Hp1 Hp2) as (r1 & M1 & A1 & B1 & T1 & T2 & T3 & T4 & C1 & N1 & K1).
    destruct (ud16_seg1 r1 _ _ p c C1 A1 B1 T1 T2 T3 T4 N1 Hp1 Hp2) as (r2 & M2 & A2 & B2 & U1 & U2 & U3 & U4 & C2 & N2 & K2).
    destruct (ud16_seg2 r2 _ _ p c C2 A2 B2 U1 U2 U3 U4 N2 Hp1 Hp2) as (r3 & M3 & A3 & B3 & V1 & V2 & V3 & V4 & C3 & N3 & K3).
    destruct (ud16_seg3 r3 _ _ p c C3 A3 B3 V1 V2 V3 V4 N3 Hp1 Hp2) as (r4 & M4 & A4 & B4 & C4 & N4 & S4 & K4).
    exists r4. split.
    - eapply msteps_trans; [exact M0|]. eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
      eapply msteps_trans; [exact M3 | exact M4].
    - rewrite bytes_at_16_list, adler_fold_16_groups. rewrite <- !adler_fold_pair_eta in A4, B4.
      repeat split; try assumption.
      eapply lkeeps_trans; [exact K1|]. eapply lkeeps_trans; [exact K2|]. eapply lkeeps_trans; [exact K3 | exact K4].
  Qed.

  Lemma ub16_body : forall regs (A B p cnt : Z),
    CK16 regs ->
    getr regs 26 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1abd4 : word) m rom) (mkst r (0x1acdc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) (BS p 16)))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) (BS p 16)))
      /\ getr r 26 = Z_to_bv 64 (p + 16)
      /\ getr r 27 = Z_to_bv 64 (sx32 ((cnt + 1) mod two32))
      /\ lkeeps ULB regs r.
  Proof.
    intros regs A B p cnt HCK RC R14 R13 RK Hp1 Hp2.
    destruct (ub16_chk regs p HCK RC ltac:(lia) ltac:(lia)) as (r0 & M0 & E0). subst r0.
    destruct (ub16_seg0 regs A B p cnt RC R14 R13 RK Hp1 Hp2) as (r1 & M1 & A1 & B1 & T1 & T2 & T3 & T4 & C1 & N1 & K1).
    destruct (ub16_seg1 r1 _ _ p cnt C1 A1 B1 T1 T2 T3 T4 N1 Hp1 Hp2) as (r2 & M2 & A2 & B2 & U1 & U2 & U3 & U4 & C2 & N2 & K2).
    destruct (ub16_seg2 r2 _ _ p cnt C2 A2 B2 U1 U2 U3 U4 N2 Hp1 Hp2) as (r3 & M3 & A3 & B3 & V1 & V2 & V3 & V4 & C3 & N3 & K3).
    destruct (ub16_seg3 r3 _ _ p cnt C3 A3 B3 V1 V2 V3 V4 N3 Hp1 Hp2) as (r4 & M4 & A4 & B4 & C4 & N4 & K4).
    exists r4. split.
    - eapply msteps_trans; [exact M0|]. eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
      eapply msteps_trans; [exact M3 | exact M4].
    - rewrite bytes_at_16_list, adler_fold_16_groups. rewrite <- !adler_fold_pair_eta in A4, B4.
      repeat split; try assumption.
      eapply lkeeps_trans; [exact K1|]. eapply lkeeps_trans; [exact K2|]. eapply lkeeps_trans; [exact K3 | exact K4].
  Qed.

  Lemma ud16_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat) (rest : Z),
    CK16 regs ->
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    getr regs 12 = Z_to_bv 64 (16 * Z.of_nat (S k) + rest) ->
    getr regs 21 = Z_to_bv 64 15 ->
    0 <= rest < 16 -> adr0 <= q -> q + Z.of_nat n + 16 * Z.of_nat (S k) + rest <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ad74 : word) m rom) (mkst r (0x1ae84 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S k))
      /\ getr r 22 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S k))
      /\ getr r 12 = Z_to_bv 64 rest
      /\ getr r 21 = Z_to_bv 64 15
      /\ lkeeps ULD regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n rest HCK RC R14 R13 RN R21 Hrest Hq Hfit.
    - destruct (ud16_body regs _ _ (q + Z.of_nat n) _ HCK RC R14 R13 RN ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & N1 & S1 & K1).
      assert (E21 : getr r1 21 = Z_to_bv 64 15) by (rewrite (K1 21%bv) by (cbv; tauto); exact R21).
      eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_1ad78 D_1ad78 ltac:(condZ).
        apply mst_refl.
      + gres. rewrite A1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite B1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite C1. zbv.
      + gres. rewrite S1. zbv.
      + gres. rewrite N1. zbv.
      + gres. exact E21.
      + solve_ka.
    - destruct (ud16_body regs _ _ (q + Z.of_nat n) _ HCK RC R14 R13 RN ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & N1 & S1 & K1).
      assert (E21 : getr r1 21 = Z_to_bv 64 15) by (rewrite (K1 21%bv) by (cbv; tauto); exact R21).
      pose proof (CK16_kept ULD regs r1 HCK K1 CKR_ULD) as HCK1.
      rewrite <- adler_fold_pair_eta, <- adler_fold_bytes_add in A1, B1.
      replace (q + Z.of_nat n + 16) with (q + Z.of_nat (n + 16)) in C1 by lia.
      replace (16 * Z.of_nat (S (S k)) + rest - 16) with (16 * Z.of_nat (S k) + rest) in N1 by lia.
      destruct (IH r1 ab q (n + 16)%nat rest HCK1 C1 A1 B1 N1 E21 Hrest Hq ltac:(lia))
        as (r2 & M2 & A2 & B2 & C2 & S2 & N2 & E2 & K2).
      eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_1ad78 D_1ad78 ltac:(condZ).
        exact M2.
      + rewrite A2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite B2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite C2. zbv.
      + rewrite S2. zbv.
      + exact N2.
      + exact E2.
      + eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  Lemma ub16_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    CK16 regs ->
    getr regs 26 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    getr regs 27 = Z_to_bv 64 (two64 - Z.of_nat (S k)) ->
    (S k <= 347)%nat ->
    adr0 <= q -> q + Z.of_nat n + 16 * Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1abd4 : word) m rom) (mkst r (0x1ace0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + 16 * S k))))
      /\ getr r 26 = Z_to_bv 64 (q + Z.of_nat n + 16 * Z.of_nat (S k))
      /\ lkeeps ULB regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n HCK RC R14 R13 RK Hk Hq Hfit.
    - destruct (ub16_body regs _ _ (q + Z.of_nat n) _ HCK RC R14 R13 RK ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & N1 & K1).
      rewrite ucnt_O in N1.
      eexists. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_1abd4 D_1abd4 ltac:(condZ).
        apply mst_refl.
      + gres. rewrite A1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite B1, <- adler_fold_pair_eta, <- adler_fold_bytes_add. zbv || (f_equal; f_equal; f_equal; lia).
      + gres. rewrite C1. zbv.
      + solve_ka.
    - destruct (ub16_body regs _ _ (q + Z.of_nat n) _ HCK RC R14 R13 RK ltac:(lia) ltac:(lia))
        as (r1 & M1 & A1 & B1 & C1 & N1 & K1).
      rewrite (ucnt_S (S k)) in N1 by lia.
      pose proof (CK16_kept ULB regs r1 HCK K1 CKR_ULB) as HCK1.
      rewrite <- adler_fold_pair_eta, <- adler_fold_bytes_add in A1, B1.
      replace (q + Z.of_nat n + 16) with (q + Z.of_nat (n + 16)) in C1 by lia.
      destruct (IH r1 ab q (n + 16)%nat HCK1 C1 A1 B1 N1 ltac:(lia) Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & C2 & K2).
      eexists. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_1abd4 D_1abd4 ltac:(condZ).
        exact M2.
      + rewrite A2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite B2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite C2. zbv.
      + eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.


  Lemma usb_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    getr regs 12 = Z_to_bv 64 (NEG 1) ->
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 10 = Z_to_bv 64 (q + Z.of_nat n + Z.of_nat (S k)) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    adr0 <= q -> q + Z.of_nat n + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1aad8 : word) m rom) (mkst r (0x1aaf4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps ULS regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R12 R11 R10 R14 R13 Hq Hfit; unfold NEG in R12.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + stepb_ft F_1a9d0 D_1a9d0 ltac:(condZ).
        lbu_pl F_1a9d4 D_1a9d4 Hb0 Eb0.
        stepz F_1a9d8 D_1a9d8. stepz F_1a9dc D_1a9dc. stepz F_1a9e0 D_1a9e0. stepz F_1a9e4 D_1a9e4.
        stepb_ft F_1a9e8 D_1a9e8 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans USEGS _ (fun r => mkst r (0x1aad8 : word) m rom)
               (fun r => getr r 12 = Z_to_bv 64 (NEG 1)
                         /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 10 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps ULS regs r)).
      { eexists. split.
        - stepb_ft F_1a9d0 D_1a9d0 ltac:(condZ).
          lbu_pl F_1a9d4 D_1a9d4 Hb0 Eb0.
          stepz F_1a9d8 D_1a9d8. stepz F_1a9dc D_1a9dc. stepz F_1a9e0 D_1a9e0. stepz F_1a9e4 D_1a9e4.
          stepb_tk F_1a9e8 D_1a9e8 ltac:(condZ).
          apply mst_refl.
        - rewrite adler_fold_bytes_S. cbn [fst snd]. unfold NEG. post. }
      cbv beta. intros r1 (S12 & S11 & S10 & S14 & S13 & K1).
      destruct (IH r1 ab q (S n) S12 S11 S10 S14 S13 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & K2).
      exists r2. split; [exact M2|].
      replace (n + S (S k))%nat with (S n + S k)%nat by lia.
      repeat split; try assumption. eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  Lemma utb_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    getr regs 10 = Z_to_bv 64 (NEG 1) ->
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 12 = Z_to_bv 64 (Z.of_nat (S k)) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    adr0 <= q -> q + Z.of_nat n + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps USEGS (mkst regs (0x1ae90 : word) m rom) (mkst r (0x1aeac : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps ULT regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R10 R11 R12 R14 R13 Hq Hfit; unfold NEG in R10.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + stepb_ft F_1ad88 D_1ad88 ltac:(condZ).
        lbu_pl F_1ad8c D_1ad8c Hb0 Eb0.
        stepz F_1ad90 D_1ad90. stepz F_1ad94 D_1ad94. stepz F_1ad98 D_1ad98. stepz F_1ad9c D_1ad9c.
        stepb_ft F_1ada0 D_1ada0 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans USEGS _ (fun r => mkst r (0x1ae90 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 (NEG 1)
                         /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps ULT regs r)).
      { eexists. split.
        - stepb_ft F_1ad88 D_1ad88 ltac:(condZ).
          lbu_pl F_1ad8c D_1ad8c Hb0 Eb0.
          stepz F_1ad90 D_1ad90. stepz F_1ad94 D_1ad94. stepz F_1ad98 D_1ad98. stepz F_1ad9c D_1ad9c.
          stepb_tk F_1ada0 D_1ada0 ltac:(condZ).
          apply mst_refl.
        - rewrite adler_fold_bytes_S. cbn [fst snd]. unfold NEG. post. }
      cbv beta. intros r1 (S10 & S11 & S12 & S14 & S13 & K1).
      destruct (IH r1 ab q (S n) S10 S11 S12 S14 S13 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & K2).
      exists r2. split; [exact M2|].
      replace (n + S (S k))%nat with (S n + S k)%nat by lia.
      repeat split; try assumption. eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.


  Lemma usmod_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps USEGS (mkst regs (0x1aaf4 : word) m rom) (mkst r (0x1aefc : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((B mod BASE) * 2 ^ 16) (csub A))
      /\ lkeeps ULM regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range B HB) as Ht. pose proof (amag_q_range B HB) as Hq.
    eexists. split; [|split].
    - stepz F_1a9ec D_1a9ec. stepz F_1a9f0 D_1a9f0. step_auipc F_1a9f4 D_1a9f4. stepz F_1a9f8 D_1a9f8.
      stepz F_1a9fc D_1a9fc.
      ld_amag F_1aa00 D_1aa00.
      stepi F_1aa04 D_1aa04; znorm. rewrite (zv_sltu 65520 A) by lia.
      stepz F_1aa08 D_1aa08.
      stepz F_1aa0c D_1aa0c. rewrite land_negflag.
      stepz F_1aa10 D_1aa10. rewrite (csub_machine A) by (lia || reflexivity).
      mulhu_z F_1aa14 D_1aa14 B.
      stepz F_1aa18 D_1aa18.
      srli_z F_1aa1c D_1aa1c (B - amag_t B).
      stepz F_1aa20 D_1aa20.
      srli_z F_1aa24 D_1aa24 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_1aa28 D_1aa28.
      stepz F_1aa2c D_1aa2c.
      stepz F_1aa30 D_1aa30. rewrite (amag_mod B HB).
      stepz F_1aa34 D_1aa34.
      stepz F_1aa38 D_1aa38.
      stepz F_1aa3c D_1aa3c.
      apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma utmod_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps USEGS (mkst regs (0x1aeac : word) m rom) (mkst r (0x1aef4 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ lkeeps ULR regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split]].
    - step_auipc F_1ada4 D_1ada4.
      ld_amag F_1ada8 D_1ada8.
      mulhu_z F_1adac D_1adac A.
      mulhu_z F_1adb0 D_1adb0 B.
      stepz F_1adb4 D_1adb4.
      srli_z F_1adb8 D_1adb8 (A - amag_t A).
      stepz F_1adbc D_1adbc.
      stepz F_1adc0 D_1adc0.
      srli_z F_1adc4 D_1adc4 (B - amag_t B).
      stepz F_1adc8 D_1adc8.
      stepz F_1adcc D_1adcc. stepz F_1add0 D_1add0.
      srli_z F_1add4 D_1add4 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      srli_z F_1add8 D_1add8 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_1addc D_1addc. stepz F_1ade0 D_1ade0.
      stepz F_1ade4 D_1ade4. rewrite (amag_mod A HA).
      stepz F_1ade8 D_1ade8. rewrite (amag_mod B HB).
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma ucomb_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    exists r, msteps USEGS (mkst regs (0x1aef4 : word) m rom) (mkst r (0x1aefc : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor (B * 2 ^ 16) A)
      /\ lkeeps ULR regs r.
  Proof.
    intros regs A B R14 R13.
    eexists. split; [|split].
    - stepz F_1adec D_1adec. stepz F_1adf0 D_1adf0. apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma ubmod_run : forall regs (A B rem : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 23 = Z_to_bv 64 4223091239536077 -> getr regs 24 = Z_to_bv 64 65521 ->
    getr regs 12 = Z_to_bv 64 rem ->
    0 <= A < two64 -> 0 <= B < two64 -> 0 <= rem < two64 ->
    exists r, msteps USEGS (mkst regs (0x1ace0 : word) m rom) (mkst r (0x1ad20 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ getr r 21 = Z_to_bv 64 (Z.shiftr rem 4)
      /\ getr r 22 = Z_to_bv 64 346
      /\ lkeeps ULE regs r.
  Proof.
    intros regs A B rem R14 R13 R23 R24 R12 HA HB Hrem.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split; [|split; [|split]]]].
    - mulhu_z F_1abd8 D_1abd8 A.
      mulhu_z F_1abdc D_1abdc B.
      stepz F_1abe0 D_1abe0.
      srli_z F_1abe4 D_1abe4 (A - amag_t A).
      stepz F_1abe8 D_1abe8.
      stepz F_1abec D_1abec.
      srli_z F_1abf0 D_1abf0 (B - amag_t B).
      stepz F_1abf4 D_1abf4.
      srli_z F_1abf8 D_1abf8 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      stepz F_1abfc D_1abfc.
      stepz F_1ac00 D_1ac00. rewrite (amag_mod A HA).
      srli_z F_1ac04 D_1ac04 rem.
      srli_z F_1ac08 D_1ac08 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_1ac0c D_1ac0c.
      stepz F_1ac10 D_1ac10. rewrite (amag_mod B HB).
      stepz F_1ac14 D_1ac14.
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.
End UADL.
End FXG.
