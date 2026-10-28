(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import MemsetLib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanMemset_codeB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

#[local] Ltac cond :=
  rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.

#[local] Ltac pclits :=
  repeat match goal with
         | |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
         end.

#[local] Ltac stepat L F D vv tac :=
  chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl].

Section Walk.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

  #[local] Ltac msb F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sb MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | lia | lia]
      | step_simpl].
  #[local] Ltac msw F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sw MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb4_c32
        | lia | lia]
      | step_simpl].
  #[local] Ltac msd F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sd MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb8_c64
        | lia | lia]
      | step_simpl].

  #[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).

  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

  Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
  Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
  Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

  Lemma A_exit0 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (n = 0)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF []) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_tk Fo_000 Do_000 ltac:(cond).
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_exit2 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (1 <= n <= 2)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L2) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_tk Fo_014 Do_014 ltac:(cond).
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_exit6 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (3 <= n <= 6)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L6) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.
      msb Fo_01c Do_01c 2%Z.
      stepn Fo_020 Do_020.
      msb Fo_024 Do_024 (n-3)%Z.
      msb Fo_028 Do_028 (n-2)%Z.
      stepb_tk Fo_02c Do_02c ltac:(cond).
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_exit8 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (7 <= n <= 8)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.
      msb Fo_01c Do_01c 2%Z.
      stepn Fo_020 Do_020.
      msb Fo_024 Do_024 (n-3)%Z.
      msb Fo_028 Do_028 (n-2)%Z.
      stepb_ft Fo_02c Do_02c ltac:(cond).
      msb Fo_030 Do_030 3%Z.
      stepn Fo_034 Do_034.
      msb Fo_038 Do_038 (n-4)%Z.
      stepb_tk Fo_03c Do_03c ltac:(cond).
      mret.
      apply mst_refl.
    - post.
  Qed.

  Lemma A_cont : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (9 <= n)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' (PC 0x40) (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = cv /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 13 = at_ d n /\ getr regs' 15 = Z_to_bv 64 9 /\ getr regs' 1 = ret
      /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.
      msb Fo_01c Do_01c 2%Z.
      stepn Fo_020 Do_020.
      msb Fo_024 Do_024 (n-3)%Z.
      msb Fo_028 Do_028 (n-2)%Z.
      stepb_ft Fo_02c Do_02c ltac:(cond).
      msb Fo_030 Do_030 3%Z.
      stepn Fo_034 Do_034.
      msb Fo_038 Do_038 (n-4)%Z.
      stepb_ft Fo_03c Do_03c ltac:(cond).
      apply mst_refl.
    - post.
  Qed.

  Section Aligned.
    Variables k n1 : Z.
    Hypothesis Hk : (0 <= k <= 3)%Z.
    Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
    Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
    Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.

    Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
    Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
    Definition LD (s4 : Z) : list (Z * Z) :=
      ((k+n1-16,4) :: (k+n1-20,4) :: (k+n1-24,4) :: (k+n1-28,4)
        :: (k+24,4) :: (k+20,4) :: (k+16,4) :: (k+12,4) :: LC)%Z.

    #[local] Ltac blockB :=
      stepn Fo_040 Do_040;
      stepn Fo_044 Do_044;
      stepn Fo_048 Do_048;
      stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);
      stepn Fo_050 Do_050;
      stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);
      stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);
      stepn Fo_05c Do_05c;
      stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);
      stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);
      msw Fo_068 Do_068 k;
      stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);
      msw Fo_070 Do_070 (k + n1 - 4)%Z.

    Lemma B_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (n1 < 9)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' ret (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_tk Fo_074 Do_074 ltac:(cond).
        mret.
        apply mst_refl.
      - post.
    Qed.

    Lemma B_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (9 <= n1)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' (PC 0x78) (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_ft Fo_074 Do_074 ltac:(cond).
        apply mst_refl.
      - post.
    Qed.

    #[local] Ltac blockC :=
      msw Fo_078 Do_078 (k + 4)%Z;
      msw Fo_07c Do_07c (k + 8)%Z;
      stepn Fo_080 Do_080;
      msw Fo_084 Do_084 (k + n1 - 12)%Z;
      msw Fo_088 Do_088 (k + n1 - 8)%Z.

    Lemma C_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (12 <= n1)%Z -> (n1 < 25)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' ret (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_tk Fo_08c Do_08c ltac:(cond).
        mret.
        apply mst_refl.
      - post.
    Qed.

    Lemma C_cont : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (25 <= n1)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' (PC 0x90) (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
        /\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
        /\ ms_agree regs regs'.
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_ft Fo_08c Do_08c ltac:(cond).
        apply mst_refl.
      - post.
    Qed.

    Section D.
      Variable s4 : Z.
      Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
      Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

      #[local] Ltac blockD :=
        msw Fo_090 Do_090 (k + 12)%Z;
        msw Fo_094 Do_094 (k + 16)%Z;
        msw Fo_098 Do_098 (k + 20)%Z;
        msw Fo_09c Do_09c (k + 24)%Z;
        stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);
        stepn Fo_0a4 Do_0a4;
        stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);
        stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);
        msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;
        msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;
        msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;
        msw Fo_0bc Do_0bc (k + n1 - 16)%Z.

      Lemma D_exit : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (n1 - s4 - 24 < 32)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' ret (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_tk Fo_0c0 Do_0c0 ltac:(cond).
          mret.
          apply mst_refl.
        - post.
      Qed.

      Lemma D_cont : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (32 <= n1 - s4 - 24)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' (PC 0xc4) (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
          /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24) /\ getr regs' 15 = Z_to_bv 64 (s4 + 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_ft Fo_0c0 Do_0c0 ltac:(cond).
          apply mst_refl.
        - post.
      Qed.

      Lemma E_run : forall regs L,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 14 = Z_to_bv 64 (n1 - s4 - 24) -> getr regs 15 = Z_to_bv 64 (s4 + 24) -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0xc4) (CF L) rom) (mkst regs' (PC 0xd8) (CF L) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d (k + s4 + 24) /\ getr regs' 12 = c64 cv
          /\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof.
        intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).
          stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
          stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);
          stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).
          stepn Fo_0d4 Do_0d4.
          apply mst_refl.
        - post.
      Qed.
    End D.
  End Aligned.

  #[local] Ltac ms_cov_eq :=
    intros i Hi; rewrite !ms_cov_cons;
    match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
    rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
    apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

  Lemma loop_run : forall (q : nat) regs L a r,
    getr regs 10 = at_ d 0 -> getr regs 11 = at_ d a -> getr regs 12 = c64 cv ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r -> getr regs 1 = ret ->
    (0 <= a)%Z -> (a + r <= n)%Z ->
    (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xd8) (CF L) rom)
                   (mkst regs' (PC 0xf4) (CF ((a, 32 * (Z.of_nat q + 1))%Z :: L)) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
  Proof.
    induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
      pose proof (u64_range d) as Hd; pclits.
    -
      eexists. split.
      + msd Fo_0d8 Do_0d8 a.
        msd Fo_0dc Do_0dc (a + 8)%Z.
        msd Fo_0e0 Do_0e0 (a + 16)%Z.
        msd Fo_0e4 Do_0e4 (a + 24)%Z.
        stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
        stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
        stepb_ft Fo_0f0 Do_0f0 ltac:(cond).
        replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
          with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        apply mst_refl.
      + post.
    - eapply (runs_trans MSEGS _
                (fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
                (fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
                           /\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
                           /\ ms_agree regs rg)).
      + cbv beta. pclits. eexists. split.
        * msd Fo_0d8 Do_0d8 a.
          msd Fo_0dc Do_0dc (a + 8)%Z.
          msd Fo_0e0 Do_0e0 (a + 16)%Z.
          msd Fo_0e4 Do_0e4 (a + 24)%Z.
          stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
          stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
          stepb_tk Fo_0f0 Do_0f0 ltac:(cond).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
        destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
                    R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
        exists r2. split.
        * replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
            with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
            by (apply cfill_ext; ms_cov_eq).
          revert RUN. pclits. intros RUN. exact RUN.
        * repeat split; try assumption. eapply ms_agree_trans; eassumption.
  Qed.

  Lemma ret_run : forall regs (M : word -> option byte),
    getr regs 1 = ret ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xf4) M rom) (mkst regs' ret M rom)
      /\ regs' = regs.
  Proof.
    intros regs M H1. pclits. eexists. split.
    - mret. apply mst_refl.
    - reflexivity.
  Qed.

End Walk.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
