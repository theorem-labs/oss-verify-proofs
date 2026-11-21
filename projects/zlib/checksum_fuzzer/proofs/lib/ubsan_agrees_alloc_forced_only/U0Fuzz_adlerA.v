(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code FuzzAdlerLib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold csub lo16 hi16 byte_at.

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
  (rewrite (K _) by (apply Hi; cbv; (first [solve [liafast_keep_section; tauto] | tauto]))); (first [solve [liafast_keep_section; tauto] | tauto]).
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
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m).
  #[local] Abbreviation BS := (bytes_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m).

  Lemma rd1 : forall a, adr0 <= a < adr0 + len0 ->
    exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 a) 1 = Some [b] /\ Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (BA a).
  Proof.
    intros a Ha. destruct (Hrd (a - adr0) ltac:(lia)) as [b Hb].
    replace (adr0 + (a - adr0)) with a in Hb by lia.
    exists b. split; [exact Hb | apply (rdn_byte_at_v (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb)), Hb].
  Qed.

  Lemma BA_range : forall a, 0 <= BA a < 256.
  Proof. intros. apply byte_at_range. Qed.

  Lemma rd_amagic : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 AMAG) 8 = Some amag_bs.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14f64 : word) m rom) (mkst r (0x1541c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a [BA adr0])
      /\ lkeeps ULH regs r.
  Proof.
    intros regs a R10 R11 R12 Ha Hl Hadr.
    destruct (rd1 adr0 ltac:(lia)) as (b0 & Hb0 & Eb0).
    pose proof (BA_range adr0) as Hb. pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split; [|split].
    - stepz F_14eb8 D_14eb8. rewrite (hi16_machine a) by lia.
      stepz F_14ebc D_14ebc.
      stepz F_14ec0 D_14ec0.
      stepi F_14ec4 D_14ec4; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_ft F_14ec8 D_14ec8 ltac:(condZ).
      stepb_ft F_14ecc D_14ecc ltac:(condZ).
      lbu_pl F_14ed0 D_14ed0 Hb0 Eb0.
      stepz F_14ed4 D_14ed4. stepz F_14ed8 D_14ed8. stepz F_14edc D_14edc. stepz F_14ee0 D_14ee0.
      stepz F_14ee4 D_14ee4.
      stepi F_14ee8 D_14ee8; znorm. rewrite (zv_sltu 65520 (lo16 a + BA adr0)) by lia.
      stepz F_14eec D_14eec.
      stepz F_14ef0 D_14ef0. rewrite land_negflag.
      stepz F_14ef4 D_14ef4.
      stepz F_14ef8 D_14ef8. rewrite (csub_machine (lo16 a + BA adr0)) by (lia || reflexivity).
      stepz F_14efc D_14efc.
      (* S8AdlerA edit: BA's RunCtx is resolved at the end of the term, AFTER a
         term-level ltac:(lia) runs *)
      pose proof (csub_nonneg (lo16 a + BA adr0)) as Hc1. specialize (Hc1 ltac:(lia)).
      stepi F_14f00 D_14f00; znorm. rewrite (zv_sltu 65520 (csub (lo16 a + BA adr0) + hi16 a)) by lia.
      stepz F_14f04 D_14f04.
      stepz F_14f08 D_14f08.
      stepz F_14f0c D_14f0c.
      stepz F_14f10 D_14f10. rewrite land_negflag.
      stepz F_14f14 D_14f14. rewrite (csub16_machine (csub (lo16 a + BA adr0) + hi16 a)) by (lia || reflexivity).
      stepz F_14f18 D_14f18.
      stepz F_14f1c D_14f1c.
      apply mst_refl.
    - gres. rewrite <- (adler_len1_path a (BA adr0)) by lia. cbv zeta.
      rewrite <- !csub_sltu, <- csub_sltu_shift16. reflexivity.
    - solve_ka.
  Qed.

  Lemma uhalves_run : forall regs (a : Z),
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    0 <= a < two64 -> 0 <= len0 -> len0 <> 1 -> 1 <= adr0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14f64 : word) m rom) (mkst r (0x14fd0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (lo16 a) /\ getr r 13 = Z_to_bv 64 (hi16 a) /\ getr r 10 = Z_to_bv 64 1
      /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 12 = Z_to_bv 64 len0
      /\ lkeeps ULH regs r.
  Proof.
    intros regs a R10 R11 R12 Ha Hl H1 Hadr.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split.
    - stepz F_14eb8 D_14eb8. rewrite (hi16_machine a) by lia.
      stepz F_14ebc D_14ebc.
      stepz F_14ec0 D_14ec0.
      stepi F_14ec4 D_14ec4; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_tk F_14ec8 D_14ec8 ltac:(condZ).
      stepb_ft F_14f20 D_14f20 ltac:(condZ).
      apply mst_refl.
    - post.
  Qed.


  Ltac ck16 H := pose proof H as CK; unfold CK16 in CK;
    destruct CK as (C10 & C15 & C16 & C17 & C5 & C6 & C7 & C28 & C29 & C30 & C31 & C8 & C9 & C18 & C19 & C20).

  Lemma ud16_chk : forall regs (p : Z),
    CK16 regs -> getr regs 11 = Z_to_bv 64 p -> 0 <= p -> p + 17 <= two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15294 : word) m rom) (mkst r (0x152d4 : word) m rom)
      /\ r = regs.
  Proof.
    intros regs p HCK R11 Hp0 Hp. ck16 HCK. unfold NEG in *.
    eexists. split; [|reflexivity].
    stepb_ft F_151e8 D_151e8 ltac:(condZ). stepb_ft F_151ec D_151ec ltac:(condZ).
    stepb_ft F_151f0 D_151f0 ltac:(condZ). stepb_ft F_151f4 D_151f4 ltac:(condZ).
    stepb_ft F_151f8 D_151f8 ltac:(condZ). stepb_ft F_151fc D_151fc ltac:(condZ).
    stepb_ft F_15200 D_15200 ltac:(condZ). stepb_ft F_15204 D_15204 ltac:(condZ).
    stepb_ft F_15208 D_15208 ltac:(condZ). stepb_ft F_1520c D_1520c ltac:(condZ).
    stepb_ft F_15210 D_15210 ltac:(condZ). stepb_ft F_15214 D_15214 ltac:(condZ).
    stepb_ft F_15218 D_15218 ltac:(condZ). stepb_ft F_1521c D_1521c ltac:(condZ).
    stepb_ft F_15220 D_15220 ltac:(condZ). stepb_ft F_15224 D_15224 ltac:(condZ).
    apply mst_refl.
  Qed.

  Lemma ub16_chk : forall regs (p : Z),
    CK16 regs -> getr regs 26 = Z_to_bv 64 p -> 0 <= p -> p + 17 <= two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x150f4 : word) m rom) (mkst r (0x15134 : word) m rom)
      /\ r = regs.
  Proof.
    intros regs p HCK R26 Hp0 Hp. ck16 HCK. unfold NEG in *.
    eexists. split; [|reflexivity].
    stepb_ft F_15048 D_15048 ltac:(condZ). stepb_ft F_1504c D_1504c ltac:(condZ).
    stepb_ft F_15050 D_15050 ltac:(condZ). stepb_ft F_15054 D_15054 ltac:(condZ).
    stepb_ft F_15058 D_15058 ltac:(condZ). stepb_ft F_1505c D_1505c ltac:(condZ).
    stepb_ft F_15060 D_15060 ltac:(condZ). stepb_ft F_15064 D_15064 ltac:(condZ).
    stepb_ft F_15068 D_15068 ltac:(condZ). stepb_ft F_1506c D_1506c ltac:(condZ).
    stepb_ft F_15070 D_15070 ltac:(condZ). stepb_ft F_15074 D_15074 ltac:(condZ).
    stepb_ft F_15078 D_15078 ltac:(condZ). stepb_ft F_1507c D_1507c ltac:(condZ).
    stepb_ft F_15080 D_15080 ltac:(condZ). stepb_ft F_15084 D_15084 ltac:(condZ).
    apply mst_refl.
  Qed.


  Lemma ud16_seg0 : forall regs (A B p c : Z),
    getr regs 11 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x152d4 : word) m rom) (mkst r (0x15314 : word) m rom)
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
    - lbu_pl F_15228 D_15228 Hb0 Eb0.
      lbu_pl F_1522c D_1522c Hb1 Eb1.
      lbu_pl F_15230 D_15230 Hb2 Eb2.
      lbu_pl F_15234 D_15234 Hb3 Eb3.
      stepz F_15238 D_15238.
      stepz F_1523c D_1523c.
      stepz F_15240 D_15240.
      stepz F_15244 D_15244.
      stepz F_15248 D_15248.
      stepz F_1524c D_1524c.
      stepz F_15250 D_15250.
      lbu_pl F_15254 D_15254 Hb4 Eb4.
      lbu_pl F_15258 D_15258 Hb5 Eb5.
      lbu_pl F_1525c D_1525c Hb6 Eb6.
      lbu_pl F_15260 D_15260 Hb7 Eb7.
      stepz F_15264 D_15264.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15314 : word) m rom) (mkst r (0x15344 : word) m rom)
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
    - stepz F_15268 D_15268.
      stepz F_1526c D_1526c.
      stepz F_15270 D_15270.
      stepz F_15274 D_15274.
      stepz F_15278 D_15278.
      stepz F_1527c D_1527c.
      stepz F_15280 D_15280.
      lbu_pl F_15284 D_15284 Hb8 Eb8.
      lbu_pl F_15288 D_15288 Hb9 Eb9.
      lbu_pl F_1528c D_1528c Hb10 Eb10.
      lbu_pl F_15290 D_15290 Hb11 Eb11.
      stepz F_15294 D_15294.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15344 : word) m rom) (mkst r (0x15374 : word) m rom)
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
    - stepz F_15298 D_15298.
      stepz F_1529c D_1529c.
      stepz F_152a0 D_152a0.
      stepz F_152a4 D_152a4.
      stepz F_152a8 D_152a8.
      stepz F_152ac D_152ac.
      stepz F_152b0 D_152b0.
      lbu_pl F_152b4 D_152b4 Hb12 Eb12.
      lbu_pl F_152b8 D_152b8 Hb13 Eb13.
      lbu_pl F_152bc D_152bc Hb14 Eb14.
      lbu_pl F_152c0 D_152c0 Hb15 Eb15.
      stepz F_152c4 D_152c4.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15374 : word) m rom) (mkst r (0x153a0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 11 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ getr r 22 = Z_to_bv 64 (p + 16)
      /\ lkeeps ULD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT22 RT23 RT24 RT25 RN Hp1 Hp2.
    eexists. split.
    - stepz F_152c8 D_152c8.
      stepz F_152cc D_152cc.
      stepz F_152d0 D_152d0.
      stepz F_152d4 D_152d4.
      stepz F_152d8 D_152d8.
      stepz F_152dc D_152dc.
      stepz F_152e0 D_152e0.
      stepz F_152e4 D_152e4.
      stepz F_152e8 D_152e8.
      stepz F_152ec D_152ec.
      stepz F_152f0 D_152f0.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ub16_seg0 : forall regs (A B p cnt : Z),
    getr regs 26 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15134 : word) m rom) (mkst r (0x15174 : word) m rom)
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
    - lbu_pl F_15088 D_15088 Hb0 Eb0.
      lbu_pl F_1508c D_1508c Hb1 Eb1.
      lbu_pl F_15090 D_15090 Hb2 Eb2.
      lbu_pl F_15094 D_15094 Hb3 Eb3.
      stepz F_15098 D_15098.
      stepz F_1509c D_1509c.
      stepz F_150a0 D_150a0.
      stepz F_150a4 D_150a4.
      stepz F_150a8 D_150a8.
      stepz F_150ac D_150ac.
      stepz F_150b0 D_150b0.
      lbu_pl F_150b4 D_150b4 Hb4 Eb4.
      lbu_pl F_150b8 D_150b8 Hb5 Eb5.
      lbu_pl F_150bc D_150bc Hb6 Eb6.
      lbu_pl F_150c0 D_150c0 Hb7 Eb7.
      stepz F_150c4 D_150c4.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15174 : word) m rom) (mkst r (0x151a4 : word) m rom)
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
    - stepz F_150c8 D_150c8.
      stepz F_150cc D_150cc.
      stepz F_150d0 D_150d0.
      stepz F_150d4 D_150d4.
      stepz F_150d8 D_150d8.
      stepz F_150dc D_150dc.
      stepz F_150e0 D_150e0.
      lbu_pl F_150e4 D_150e4 Hb8 Eb8.
      lbu_pl F_150e8 D_150e8 Hb9 Eb9.
      lbu_pl F_150ec D_150ec Hb10 Eb10.
      lbu_pl F_150f0 D_150f0 Hb11 Eb11.
      stepz F_150f4 D_150f4.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x151a4 : word) m rom) (mkst r (0x151d4 : word) m rom)
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
    - stepz F_150f8 D_150f8.
      stepz F_150fc D_150fc.
      stepz F_15100 D_15100.
      stepz F_15104 D_15104.
      stepz F_15108 D_15108.
      stepz F_1510c D_1510c.
      stepz F_15110 D_15110.
      lbu_pl F_15114 D_15114 Hb12 Eb12.
      lbu_pl F_15118 D_15118 Hb13 Eb13.
      lbu_pl F_1511c D_1511c Hb14 Eb14.
      lbu_pl F_15120 D_15120 Hb15 Eb15.
      stepz F_15124 D_15124.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x151d4 : word) m rom) (mkst r (0x151fc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 26 = Z_to_bv 64 (p + 16)
      /\ getr r 27 = Z_to_bv 64 (sx32 ((cnt + 1) mod two32))
      /\ lkeeps ULB regs r.
  Proof.
    intros regs A B p cnt RC R14 R13 RT21 RT22 RT25 RT1 RK Hp1 Hp2.
    eexists. split.
    - stepz F_15128 D_15128.
      stepz F_1512c D_1512c.
      stepz F_15130 D_15130.
      stepz F_15134 D_15134.
      stepz F_15138 D_15138.
      stepz F_1513c D_1513c.
      stepz F_15140 D_15140.
      stepz F_15144 D_15144.
      stepz F_15148 D_15148.
      stepz F_1514c D_1514c.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15294 : word) m rom) (mkst r (0x153a0 : word) m rom)
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x150f4 : word) m rom) (mkst r (0x151fc : word) m rom)
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15294 : word) m rom) (mkst r (0x153a4 : word) m rom)
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
      assert (E21 : getr r1 21 = Z_to_bv 64 15) by (rewrite (K1 21%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R21).
      eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_152f4 D_152f4 ltac:(condZ).
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
      assert (E21 : getr r1 21 = Z_to_bv 64 15) by (rewrite (K1 21%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R21).
      pose proof (CK16_kept ULD regs r1 HCK K1 CKR_ULD) as HCK1.
      rewrite <- adler_fold_pair_eta, <- adler_fold_bytes_add in A1, B1.
      replace (q + Z.of_nat n + 16) with (q + Z.of_nat (n + 16)) in C1 by lia.
      replace (16 * Z.of_nat (S (S k)) + rest - 16) with (16 * Z.of_nat (S k) + rest) in N1 by lia.
      destruct (IH r1 ab q (n + 16)%nat rest HCK1 C1 A1 B1 N1 E21 Hrest Hq ltac:(lia))
        as (r2 & M2 & A2 & B2 & C2 & S2 & N2 & E2 & K2).
      eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + eapply msteps_trans; [exact M1|].
        stepb_tk F_152f4 D_152f4 ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x150f4 : word) m rom) (mkst r (0x15200 : word) m rom)
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
        stepb_ft F_15150 D_15150 ltac:(condZ).
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
        stepb_tk F_15150 D_15150 ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14ff8 : word) m rom) (mkst r (0x15014 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps ULS regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R12 R11 R10 R14 R13 Hq Hfit; unfold NEG in R12.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + stepb_ft F_14f4c D_14f4c ltac:(condZ).
        lbu_pl F_14f50 D_14f50 Hb0 Eb0.
        stepz F_14f54 D_14f54. stepz F_14f58 D_14f58. stepz F_14f5c D_14f5c. stepz F_14f60 D_14f60.
        stepb_ft F_14f64 D_14f64 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x14ff8 : word) m rom)
               (fun r => getr r 12 = Z_to_bv 64 (NEG 1)
                         /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 10 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps ULS regs r)).
      { eexists. split.
        - stepb_ft F_14f4c D_14f4c ltac:(condZ).
          lbu_pl F_14f50 D_14f50 Hb0 Eb0.
          stepz F_14f54 D_14f54. stepz F_14f58 D_14f58. stepz F_14f5c D_14f5c. stepz F_14f60 D_14f60.
          stepb_tk F_14f64 D_14f64 ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x153b0 : word) m rom) (mkst r (0x153cc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps ULT regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R10 R11 R12 R14 R13 Hq Hfit; unfold NEG in R10.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + stepb_ft F_15304 D_15304 ltac:(condZ).
        lbu_pl F_15308 D_15308 Hb0 Eb0.
        stepz F_1530c D_1530c. stepz F_15310 D_15310. stepz F_15314 D_15314. stepz F_15318 D_15318.
        stepb_ft F_1531c D_1531c ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x153b0 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 (NEG 1)
                         /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps ULT regs r)).
      { eexists. split.
        - stepb_ft F_15304 D_15304 ltac:(condZ).
          lbu_pl F_15308 D_15308 Hb0 Eb0.
          stepz F_1530c D_1530c. stepz F_15310 D_15310. stepz F_15314 D_15314. stepz F_15318 D_15318.
          stepb_tk F_1531c D_1531c ltac:(condZ).
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15014 : word) m rom) (mkst r (0x1541c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((B mod BASE) * 2 ^ 16) (csub A))
      /\ lkeeps ULM regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range B HB) as Ht. pose proof (amag_q_range B HB) as Hq.
    eexists. split; [|split].
    - stepz F_14f68 D_14f68. stepz F_14f6c D_14f6c. step_auipc F_14f70 D_14f70. stepz F_14f74 D_14f74.
      stepz F_14f78 D_14f78.
      ld_amag F_14f7c D_14f7c.
      stepi F_14f80 D_14f80; znorm. rewrite (zv_sltu 65520 A) by lia.
      stepz F_14f84 D_14f84.
      stepz F_14f88 D_14f88. rewrite land_negflag.
      stepz F_14f8c D_14f8c. rewrite (csub_machine A) by (lia || reflexivity).
      mulhu_z F_14f90 D_14f90 B.
      stepz F_14f94 D_14f94.
      srli_z F_14f98 D_14f98 (B - amag_t B).
      stepz F_14f9c D_14f9c.
      srli_z F_14fa0 D_14fa0 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_14fa4 D_14fa4.
      stepz F_14fa8 D_14fa8.
      stepz F_14fac D_14fac. rewrite (amag_mod B HB).
      stepz F_14fb0 D_14fb0.
      stepz F_14fb4 D_14fb4.
      stepz F_14fb8 D_14fb8.
      apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma utmod_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x153cc : word) m rom) (mkst r (0x15414 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ lkeeps ULR regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split]].
    - step_auipc F_15320 D_15320.
      ld_amag F_15324 D_15324.
      mulhu_z F_15328 D_15328 A.
      mulhu_z F_1532c D_1532c B.
      stepz F_15330 D_15330.
      srli_z F_15334 D_15334 (A - amag_t A).
      stepz F_15338 D_15338.
      stepz F_1533c D_1533c.
      srli_z F_15340 D_15340 (B - amag_t B).
      stepz F_15344 D_15344.
      stepz F_15348 D_15348. stepz F_1534c D_1534c.
      srli_z F_15350 D_15350 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      srli_z F_15354 D_15354 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_15358 D_15358. stepz F_1535c D_1535c.
      stepz F_15360 D_15360. rewrite (amag_mod A HA).
      stepz F_15364 D_15364. rewrite (amag_mod B HB).
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma ucomb_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15414 : word) m rom) (mkst r (0x1541c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor (B * 2 ^ 16) A)
      /\ lkeeps ULR regs r.
  Proof.
    intros regs A B R14 R13.
    eexists. split; [|split].
    - stepz F_15368 D_15368. stepz F_1536c D_1536c. apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  Lemma ubmod_run : forall regs (A B rem : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 23 = Z_to_bv 64 4223091239536077 -> getr regs 24 = Z_to_bv 64 65521 ->
    getr regs 12 = Z_to_bv 64 rem ->
    0 <= A < two64 -> 0 <= B < two64 -> 0 <= rem < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x15200 : word) m rom) (mkst r (0x15240 : word) m rom)
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
    - mulhu_z F_15154 D_15154 A.
      mulhu_z F_15158 D_15158 B.
      stepz F_1515c D_1515c.
      srli_z F_15160 D_15160 (A - amag_t A).
      stepz F_15164 D_15164.
      stepz F_15168 D_15168.
      srli_z F_1516c D_1516c (B - amag_t B).
      stepz F_15170 D_15170.
      srli_z F_15174 D_15174 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      stepz F_15178 D_15178.
      stepz F_1517c D_1517c. rewrite (amag_mod A HA).
      srli_z F_15180 D_15180 rem.
      srli_z F_15184 D_15184 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_15188 D_15188.
      stepz F_1518c D_1518c. rewrite (amag_mod B HB).
      stepz F_15190 D_15190.
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.
End UADL.
