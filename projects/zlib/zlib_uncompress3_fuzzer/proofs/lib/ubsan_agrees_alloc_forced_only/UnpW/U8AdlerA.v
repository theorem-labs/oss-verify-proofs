(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_ubsan.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Frame OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgentLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SumWalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzZ OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzCk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8AdlerBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Adler_code OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzAdlerLib.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold csub lo16 hi16 byte_at.

(* [comment removed for export] *)
Definition ULD : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 26; 27; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ULB : list reg := [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 23; 24; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ULS : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ULT : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ULM : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ULR : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ULE : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ULH : list reg := ULR.

(* [comment removed for export] *)
Definition NEG (k : Z) : Z := 18446744073709551616 - k.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ua1_run : forall regs (a : Z),
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 1 ->
    0 <= a < two64 -> 1 <= len0 -> 1 <= adr0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17e74 : word) m rom) (mkst r (0x1832c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a [BA adr0])
      /\ lkeeps ULH regs r.
  Proof.
    intros regs a R10 R11 R12 Ha Hl Hadr.
    destruct (rd1 adr0 ltac:(lia)) as (b0 & Hb0 & Eb0).
    pose proof (BA_range adr0) as Hb. pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split; [|split].
    - stepz F_17d50 D_17d50. rewrite (hi16_machine a) by lia.
      stepz F_17d54 D_17d54.
      stepz F_17d58 D_17d58.
      stepi F_17d5c D_17d5c; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_ft F_17d60 D_17d60 ltac:(condZ).
      stepb_ft F_17d64 D_17d64 ltac:(condZ).
      lbu_pl F_17d68 D_17d68 Hb0 Eb0.
      stepz F_17d6c D_17d6c. stepz F_17d70 D_17d70. stepz F_17d74 D_17d74. stepz F_17d78 D_17d78.
      stepz F_17d7c D_17d7c.
      stepi F_17d80 D_17d80; znorm. rewrite (zv_sltu 65520 (lo16 a + BA adr0)) by lia.
      stepz F_17d84 D_17d84.
      stepz F_17d88 D_17d88. rewrite land_negflag.
      stepz F_17d8c D_17d8c.
      stepz F_17d90 D_17d90. rewrite (csub_machine (lo16 a + BA adr0)) by (lia || reflexivity).
      stepz F_17d94 D_17d94.
      (* a worker (A1): BA's RunCtx is resolved at the end of the term, AFTER a term-level ltac:(lia) runs *)
      pose proof (csub_nonneg (lo16 a + BA adr0)) as Hc1. specialize (Hc1 ltac:(lia)).
      stepi F_17d98 D_17d98; znorm. rewrite (zv_sltu 65520 (csub (lo16 a + BA adr0) + hi16 a)) by lia.
      stepz F_17d9c D_17d9c.
      stepz F_17da0 D_17da0.
      stepz F_17da4 D_17da4.
      stepz F_17da8 D_17da8. rewrite land_negflag.
      stepz F_17dac D_17dac. rewrite (csub16_machine (csub (lo16 a + BA adr0) + hi16 a)) by (lia || reflexivity).
      stepz F_17db0 D_17db0.
      stepz F_17db4 D_17db4.
      apply mst_refl.
    - gres. rewrite <- (adler_len1_path a (BA adr0)) by lia. cbv zeta.
      rewrite <- !csub_sltu, <- csub_sltu_shift16. reflexivity.
    - solve_ka.
  Qed.

  (* [comment removed for export] *)
  Lemma uhalves_run : forall regs (a : Z),
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    0 <= a < two64 -> 0 <= len0 -> len0 <> 1 -> 1 <= adr0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17e74 : word) m rom) (mkst r (0x17ee0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (lo16 a) /\ getr r 13 = Z_to_bv 64 (hi16 a) /\ getr r 10 = Z_to_bv 64 1
      /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 12 = Z_to_bv 64 len0
      /\ lkeeps ULH regs r.
  Proof.
    intros regs a R10 R11 R12 Ha Hl H1 Hadr.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    eexists. split.
    - stepz F_17d50 D_17d50. rewrite (hi16_machine a) by lia.
      stepz F_17d54 D_17d54.
      stepz F_17d58 D_17d58.
      stepi F_17d5c D_17d5c; znorm. rewrite (zv_srli_mod (a * 2 ^ 48) 48), (lo16_machine a) by lia.
      stepb_tk F_17d60 D_17d60 ltac:(condZ).
      stepb_ft F_17db8 D_17db8 ltac:(condZ).
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac ck16 H := pose proof H as CK; unfold CK16 in CK;
    destruct CK as (C10 & C15 & C16 & C17 & C5 & C6 & C7 & C28 & C29 & C30 & C31 & C8 & C9 & C18 & C19 & C20).

  (* [comment removed for export] *)
  Lemma ud16_chk : forall regs (p : Z),
    CK16 regs -> getr regs 11 = Z_to_bv 64 p -> 0 <= p -> p + 17 <= two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x181a4 : word) m rom) (mkst r (0x181e4 : word) m rom)
      /\ r = regs.
  Proof.
    intros regs p HCK R11 Hp0 Hp. ck16 HCK. unfold NEG in *.
    eexists. split; [|reflexivity].
    stepb_ft F_18080 D_18080 ltac:(condZ). stepb_ft F_18084 D_18084 ltac:(condZ).
    stepb_ft F_18088 D_18088 ltac:(condZ). stepb_ft F_1808c D_1808c ltac:(condZ).
    stepb_ft F_18090 D_18090 ltac:(condZ). stepb_ft F_18094 D_18094 ltac:(condZ).
    stepb_ft F_18098 D_18098 ltac:(condZ). stepb_ft F_1809c D_1809c ltac:(condZ).
    stepb_ft F_180a0 D_180a0 ltac:(condZ). stepb_ft F_180a4 D_180a4 ltac:(condZ).
    stepb_ft F_180a8 D_180a8 ltac:(condZ). stepb_ft F_180ac D_180ac ltac:(condZ).
    stepb_ft F_180b0 D_180b0 ltac:(condZ). stepb_ft F_180b4 D_180b4 ltac:(condZ).
    stepb_ft F_180b8 D_180b8 ltac:(condZ). stepb_ft F_180bc D_180bc ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma ub16_chk : forall regs (p : Z),
    CK16 regs -> getr regs 26 = Z_to_bv 64 p -> 0 <= p -> p + 17 <= two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18004 : word) m rom) (mkst r (0x18044 : word) m rom)
      /\ r = regs.
  Proof.
    intros regs p HCK R26 Hp0 Hp. ck16 HCK. unfold NEG in *.
    eexists. split; [|reflexivity].
    stepb_ft F_17ee0 D_17ee0 ltac:(condZ). stepb_ft F_17ee4 D_17ee4 ltac:(condZ).
    stepb_ft F_17ee8 D_17ee8 ltac:(condZ). stepb_ft F_17eec D_17eec ltac:(condZ).
    stepb_ft F_17ef0 D_17ef0 ltac:(condZ). stepb_ft F_17ef4 D_17ef4 ltac:(condZ).
    stepb_ft F_17ef8 D_17ef8 ltac:(condZ). stepb_ft F_17efc D_17efc ltac:(condZ).
    stepb_ft F_17f00 D_17f00 ltac:(condZ). stepb_ft F_17f04 D_17f04 ltac:(condZ).
    stepb_ft F_17f08 D_17f08 ltac:(condZ). stepb_ft F_17f0c D_17f0c ltac:(condZ).
    stepb_ft F_17f10 D_17f10 ltac:(condZ). stepb_ft F_17f14 D_17f14 ltac:(condZ).
    stepb_ft F_17f18 D_17f18 ltac:(condZ). stepb_ft F_17f1c D_17f1c ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma ud16_seg0 : forall regs (A B p c : Z),
    getr regs 11 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x181e4 : word) m rom) (mkst r (0x18224 : word) m rom)
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
    - lbu_pl F_180c0 D_180c0 Hb0 Eb0.
      lbu_pl F_180c4 D_180c4 Hb1 Eb1.
      lbu_pl F_180c8 D_180c8 Hb2 Eb2.
      lbu_pl F_180cc D_180cc Hb3 Eb3.
      stepz F_180d0 D_180d0.
      stepz F_180d4 D_180d4.
      stepz F_180d8 D_180d8.
      stepz F_180dc D_180dc.
      stepz F_180e0 D_180e0.
      stepz F_180e4 D_180e4.
      stepz F_180e8 D_180e8.
      lbu_pl F_180ec D_180ec Hb4 Eb4.
      lbu_pl F_180f0 D_180f0 Hb5 Eb5.
      lbu_pl F_180f4 D_180f4 Hb6 Eb6.
      lbu_pl F_180f8 D_180f8 Hb7 Eb7.
      stepz F_180fc D_180fc.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18224 : word) m rom) (mkst r (0x18254 : word) m rom)
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
    - stepz F_18100 D_18100.
      stepz F_18104 D_18104.
      stepz F_18108 D_18108.
      stepz F_1810c D_1810c.
      stepz F_18110 D_18110.
      stepz F_18114 D_18114.
      stepz F_18118 D_18118.
      lbu_pl F_1811c D_1811c Hb8 Eb8.
      lbu_pl F_18120 D_18120 Hb9 Eb9.
      lbu_pl F_18124 D_18124 Hb10 Eb10.
      lbu_pl F_18128 D_18128 Hb11 Eb11.
      stepz F_1812c D_1812c.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18254 : word) m rom) (mkst r (0x18284 : word) m rom)
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
    - stepz F_18130 D_18130.
      stepz F_18134 D_18134.
      stepz F_18138 D_18138.
      stepz F_1813c D_1813c.
      stepz F_18140 D_18140.
      stepz F_18144 D_18144.
      stepz F_18148 D_18148.
      lbu_pl F_1814c D_1814c Hb12 Eb12.
      lbu_pl F_18150 D_18150 Hb13 Eb13.
      lbu_pl F_18154 D_18154 Hb14 Eb14.
      lbu_pl F_18158 D_18158 Hb15 Eb15.
      stepz F_1815c D_1815c.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18284 : word) m rom) (mkst r (0x182b0 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 11 = Z_to_bv 64 (p + 16)
      /\ getr r 12 = Z_to_bv 64 (c - 16)
      /\ getr r 22 = Z_to_bv 64 (p + 16)
      /\ lkeeps ULD regs r.
  Proof.
    intros regs A B p c RC R14 R13 RT22 RT23 RT24 RT25 RN Hp1 Hp2.
    eexists. split.
    - stepz F_18160 D_18160.
      stepz F_18164 D_18164.
      stepz F_18168 D_18168.
      stepz F_1816c D_1816c.
      stepz F_18170 D_18170.
      stepz F_18174 D_18174.
      stepz F_18178 D_18178.
      stepz F_1817c D_1817c.
      stepz F_18180 D_18180.
      stepz F_18184 D_18184.
      stepz F_18188 D_18188.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.

  Lemma ub16_seg0 : forall regs (A B p cnt : Z),
    getr regs 26 = Z_to_bv 64 p ->
    getr regs 14 = Z_to_bv 64 A ->
    getr regs 13 = Z_to_bv 64 B ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18044 : word) m rom) (mkst r (0x18084 : word) m rom)
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
    - lbu_pl F_17f20 D_17f20 Hb0 Eb0.
      lbu_pl F_17f24 D_17f24 Hb1 Eb1.
      lbu_pl F_17f28 D_17f28 Hb2 Eb2.
      lbu_pl F_17f2c D_17f2c Hb3 Eb3.
      stepz F_17f30 D_17f30.
      stepz F_17f34 D_17f34.
      stepz F_17f38 D_17f38.
      stepz F_17f3c D_17f3c.
      stepz F_17f40 D_17f40.
      stepz F_17f44 D_17f44.
      stepz F_17f48 D_17f48.
      lbu_pl F_17f4c D_17f4c Hb4 Eb4.
      lbu_pl F_17f50 D_17f50 Hb5 Eb5.
      lbu_pl F_17f54 D_17f54 Hb6 Eb6.
      lbu_pl F_17f58 D_17f58 Hb7 Eb7.
      stepz F_17f5c D_17f5c.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18084 : word) m rom) (mkst r (0x180b4 : word) m rom)
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
    - stepz F_17f60 D_17f60.
      stepz F_17f64 D_17f64.
      stepz F_17f68 D_17f68.
      stepz F_17f6c D_17f6c.
      stepz F_17f70 D_17f70.
      stepz F_17f74 D_17f74.
      stepz F_17f78 D_17f78.
      lbu_pl F_17f7c D_17f7c Hb8 Eb8.
      lbu_pl F_17f80 D_17f80 Hb9 Eb9.
      lbu_pl F_17f84 D_17f84 Hb10 Eb10.
      lbu_pl F_17f88 D_17f88 Hb11 Eb11.
      stepz F_17f8c D_17f8c.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x180b4 : word) m rom) (mkst r (0x180e4 : word) m rom)
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
    - stepz F_17f90 D_17f90.
      stepz F_17f94 D_17f94.
      stepz F_17f98 D_17f98.
      stepz F_17f9c D_17f9c.
      stepz F_17fa0 D_17fa0.
      stepz F_17fa4 D_17fa4.
      stepz F_17fa8 D_17fa8.
      lbu_pl F_17fac D_17fac Hb12 Eb12.
      lbu_pl F_17fb0 D_17fb0 Hb13 Eb13.
      lbu_pl F_17fb4 D_17fb4 Hb14 Eb14.
      lbu_pl F_17fb8 D_17fb8 Hb15 Eb15.
      stepz F_17fbc D_17fbc.
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
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x180e4 : word) m rom) (mkst r (0x1810c : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold (A, B) [BA (p + 12); BA (p + 13); BA (p + 14); BA (p + 15)]))
      /\ getr r 26 = Z_to_bv 64 (p + 16)
      /\ getr r 27 = Z_to_bv 64 (sx32 ((cnt + 1) mod two32))
      /\ lkeeps ULB regs r.
  Proof.
    intros regs A B p cnt RC R14 R13 RT21 RT22 RT25 RT1 RK Hp1 Hp2.
    eexists. split.
    - stepz F_17fc0 D_17fc0.
      stepz F_17fc4 D_17fc4.
      stepz F_17fc8 D_17fc8.
      stepz F_17fcc D_17fcc.
      stepz F_17fd0 D_17fd0.
      stepz F_17fd4 D_17fd4.
      stepz F_17fd8 D_17fd8.
      stepz F_17fdc D_17fdc.
      stepz F_17fe0 D_17fe0.
      stepz F_17fe4 D_17fe4.
      apply mst_refl.
    - rewrite adler_fold_4. cbn [fst snd]. post.
  Qed.



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma CKR_ULD : incl CKR ULD. Proof. incl_dec. Qed.
  Lemma CKR_ULB : incl CKR ULB. Proof. incl_dec. Qed.

  (* [comment removed for export] *)
  Lemma ud16_body : forall regs (A B p c : Z),
    CK16 regs ->
    getr regs 11 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 12 = Z_to_bv 64 c ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x181a4 : word) m rom) (mkst r (0x182b0 : word) m rom)
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

  (* [comment removed for export] *)
  Lemma ub16_body : forall regs (A B p cnt : Z),
    CK16 regs ->
    getr regs 26 = Z_to_bv 64 p -> getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 27 = Z_to_bv 64 cnt ->
    adr0 <= p -> p + 16 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18004 : word) m rom) (mkst r (0x1810c : word) m rom)
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

  (* [comment removed for export] *)
  Lemma ud16_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat) (rest : Z),
    CK16 regs ->
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    getr regs 12 = Z_to_bv 64 (16 * Z.of_nat (S k) + rest) ->
    getr regs 21 = Z_to_bv 64 15 ->
    0 <= rest < 16 -> adr0 <= q -> q + Z.of_nat n + 16 * Z.of_nat (S k) + rest <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x181a4 : word) m rom) (mkst r (0x182b4 : word) m rom)
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
        stepb_ft F_1818c D_1818c ltac:(condZ).
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
        stepb_tk F_1818c D_1818c ltac:(condZ).
        exact M2.
      + rewrite A2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite B2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite C2. zbv.
      + rewrite S2. zbv.
      + exact N2.
      + exact E2.
      + eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  (* [comment removed for export] *)
  Lemma ub16_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    CK16 regs ->
    getr regs 26 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    getr regs 27 = Z_to_bv 64 (two64 - Z.of_nat (S k)) ->
    (S k <= 347)%nat ->
    adr0 <= q -> q + Z.of_nat n + 16 * Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18004 : word) m rom) (mkst r (0x18110 : word) m rom)
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
        stepb_ft F_17fe8 D_17fe8 ltac:(condZ).
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
        stepb_tk F_17fe8 D_17fe8 ltac:(condZ).
        exact M2.
      + rewrite A2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite B2. zbv || (f_equal; f_equal; f_equal; f_equal; lia).
      + rewrite C2. zbv.
      + eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma usb_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    getr regs 12 = Z_to_bv 64 (NEG 1) ->
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 10 = Z_to_bv 64 (q + Z.of_nat n + Z.of_nat (S k)) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    adr0 <= q -> q + Z.of_nat n + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17f08 : word) m rom) (mkst r (0x17f24 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps ULS regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R12 R11 R10 R14 R13 Hq Hfit; unfold NEG in R12.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + stepb_ft F_17de4 D_17de4 ltac:(condZ).
        lbu_pl F_17de8 D_17de8 Hb0 Eb0.
        stepz F_17dec D_17dec. stepz F_17df0 D_17df0. stepz F_17df4 D_17df4. stepz F_17df8 D_17df8.
        stepb_ft F_17dfc D_17dfc ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x17f08 : word) m rom)
               (fun r => getr r 12 = Z_to_bv 64 (NEG 1)
                         /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 10 = Z_to_bv 64 (q + Z.of_nat (S n) + Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps ULS regs r)).
      { eexists. split.
        - stepb_ft F_17de4 D_17de4 ltac:(condZ).
          lbu_pl F_17de8 D_17de8 Hb0 Eb0.
          stepz F_17dec D_17dec. stepz F_17df0 D_17df0. stepz F_17df4 D_17df4. stepz F_17df8 D_17df8.
          stepb_tk F_17dfc D_17dfc ltac:(condZ).
          apply mst_refl.
        - rewrite adler_fold_bytes_S. cbn [fst snd]. unfold NEG. post. }
      cbv beta. intros r1 (S12 & S11 & S10 & S14 & S13 & K1).
      destruct (IH r1 ab q (S n) S12 S11 S10 S14 S13 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & K2).
      exists r2. split; [exact M2|].
      replace (n + S (S k))%nat with (S n + S k)%nat by lia.
      repeat split; try assumption. eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  (* [comment removed for export] *)
  Lemma utb_loop : forall (k : nat) regs (ab : Z * Z) (q : Z) (n : nat),
    getr regs 10 = Z_to_bv 64 (NEG 1) ->
    getr regs 11 = Z_to_bv 64 (q + Z.of_nat n) ->
    getr regs 12 = Z_to_bv 64 (Z.of_nat (S k)) ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    adr0 <= q -> q + Z.of_nat n + Z.of_nat (S k) <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x182c0 : word) m rom) (mkst r (0x182dc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (n + S k))))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (n + S k))))
      /\ lkeeps ULT regs r.
  Proof.
    induction k as [|k IH]; intros regs ab q n R10 R11 R12 R14 R13 Hq Hfit; unfold NEG in R10.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eexists. split; [|split; [|split]].
      + stepb_ft F_1819c D_1819c ltac:(condZ).
        lbu_pl F_181a0 D_181a0 Hb0 Eb0.
        stepz F_181a4 D_181a4. stepz F_181a8 D_181a8. stepz F_181ac D_181ac. stepz F_181b0 D_181b0.
        stepb_ft F_181b4 D_181b4 ltac:(condZ).
        apply mst_refl.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + gres. replace (n + 1)%nat with (S n) by lia. rewrite adler_fold_bytes_S. cbn [fst snd]. zbv.
      + solve_ka.
    - destruct (rd1 (q + Z.of_nat n) ltac:(lia)) as (b0 & Hb0 & Eb0).
      eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x182c0 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 (NEG 1)
                         /\ getr r 11 = Z_to_bv 64 (q + Z.of_nat (S n))
                         /\ getr r 12 = Z_to_bv 64 (Z.of_nat (S k))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q (S n))))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q (S n))))
                         /\ lkeeps ULT regs r)).
      { eexists. split.
        - stepb_ft F_1819c D_1819c ltac:(condZ).
          lbu_pl F_181a0 D_181a0 Hb0 Eb0.
          stepz F_181a4 D_181a4. stepz F_181a8 D_181a8. stepz F_181ac D_181ac. stepz F_181b0 D_181b0.
          stepb_tk F_181b4 D_181b4 ltac:(condZ).
          apply mst_refl.
        - rewrite adler_fold_bytes_S. cbn [fst snd]. unfold NEG. post. }
      cbv beta. intros r1 (S10 & S11 & S12 & S14 & S13 & K1).
      destruct (IH r1 ab q (S n) S10 S11 S12 S14 S13 Hq ltac:(lia)) as (r2 & M2 & A2 & B2 & K2).
      exists r2. split; [exact M2|].
      replace (n + S (S k))%nat with (S n + S k)%nat by lia.
      repeat split; try assumption. eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma usmod_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x17f24 : word) m rom) (mkst r (0x1832c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((B mod BASE) * 2 ^ 16) (csub A))
      /\ lkeeps ULM regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range B HB) as Ht. pose proof (amag_q_range B HB) as Hq.
    eexists. split; [|split].
    - stepz F_17e00 D_17e00. stepz F_17e04 D_17e04. step_auipc F_17e08 D_17e08. stepz F_17e0c D_17e0c.
      stepz F_17e10 D_17e10.
      ld_amag F_17e14 D_17e14.
      stepi F_17e18 D_17e18; znorm. rewrite (zv_sltu 65520 A) by lia.
      stepz F_17e1c D_17e1c.
      stepz F_17e20 D_17e20. rewrite land_negflag.
      stepz F_17e24 D_17e24. rewrite (csub_machine A) by (lia || reflexivity).
      mulhu_z F_17e28 D_17e28 B.
      stepz F_17e2c D_17e2c.
      srli_z F_17e30 D_17e30 (B - amag_t B).
      stepz F_17e34 D_17e34.
      srli_z F_17e38 D_17e38 (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_17e3c D_17e3c.
      stepz F_17e40 D_17e40.
      stepz F_17e44 D_17e44. rewrite (amag_mod B HB).
      stepz F_17e48 D_17e48.
      stepz F_17e4c D_17e4c.
      stepz F_17e50 D_17e50.
      apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  (* [comment removed for export] *)
  Lemma utmod_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    0 <= A < two64 -> 0 <= B < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x182dc : word) m rom) (mkst r (0x18324 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (A mod BASE)
      /\ getr r 13 = Z_to_bv 64 (B mod BASE)
      /\ lkeeps ULR regs r.
  Proof.
    intros regs A B R14 R13 HA HB.
    pose proof (amag_t_range A HA) as HtA. pose proof (amag_q_range A HA) as HqA.
    pose proof (amag_t_range B HB) as HtB. pose proof (amag_q_range B HB) as HqB.
    eexists. split; [|split; [|split]].
    - step_auipc F_181b8 D_181b8.
      ld_amag F_181bc D_181bc.
      mulhu_z F_181c0 D_181c0 A.
      mulhu_z F_181c4 D_181c4 B.
      stepz F_181c8 D_181c8.
      srli_z F_181cc D_181cc (A - amag_t A).
      stepz F_181d0 D_181d0.
      stepz F_181d4 D_181d4.
      srli_z F_181d8 D_181d8 (B - amag_t B).
      stepz F_181dc D_181dc.
      stepz F_181e0 D_181e0. stepz F_181e4 D_181e4.
      srli_z F_181e8 D_181e8 (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      srli_z F_181ec D_181ec (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_181f0 D_181f0. stepz F_181f4 D_181f4.
      stepz F_181f8 D_181f8. rewrite (amag_mod A HA).
      stepz F_181fc D_181fc. rewrite (amag_mod B HB).
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  (* [comment removed for export] *)
  Lemma ucomb_run : forall regs (A B : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18324 : word) m rom) (mkst r (0x1832c : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor (B * 2 ^ 16) A)
      /\ lkeeps ULR regs r.
  Proof.
    intros regs A B R14 R13.
    eexists. split; [|split].
    - stepz F_18200 D_18200. stepz F_18204 D_18204. apply mst_refl.
    - gres. reflexivity.
    - solve_ka.
  Qed.

  (* [comment removed for export] *)
  Lemma ubmod_run : forall regs (A B rem : Z),
    getr regs 14 = Z_to_bv 64 A -> getr regs 13 = Z_to_bv 64 B ->
    getr regs 23 = Z_to_bv 64 4223091239536077 -> getr regs 24 = Z_to_bv 64 65521 ->
    getr regs 12 = Z_to_bv 64 rem ->
    0 <= A < two64 -> 0 <= B < two64 -> 0 <= rem < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x18110 : word) m rom) (mkst r (0x18150 : word) m rom)
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
    - mulhu_z F_17fec D_17fec A.
      mulhu_z F_17ff0 D_17ff0 B.
      stepz F_17ff4 D_17ff4.
      srli_z F_17ff8 D_17ff8 (A - amag_t A).
      stepz F_17ffc D_17ffc.
      stepz F_18000 D_18000.
      srli_z F_18004 D_18004 (B - amag_t B).
      stepz F_18008 D_18008.
      srli_z F_1800c D_1800c (Z.shiftr (A - amag_t A) 1 + amag_t A).
      change (Z.shiftr (Z.shiftr (A - amag_t A) 1 + amag_t A) 15) with (amag_q A).
      stepz F_18010 D_18010.
      stepz F_18014 D_18014. rewrite (amag_mod A HA).
      srli_z F_18018 D_18018 rem.
      srli_z F_1801c D_1801c (Z.shiftr (B - amag_t B) 1 + amag_t B).
      change (Z.shiftr (Z.shiftr (B - amag_t B) 1 + amag_t B) 15) with (amag_q B).
      stepz F_18020 D_18020.
      stepz F_18024 D_18024. rewrite (amag_mod B HB).
      stepz F_18028 D_18028.
      apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_ka.
  Qed.
End UADL.
