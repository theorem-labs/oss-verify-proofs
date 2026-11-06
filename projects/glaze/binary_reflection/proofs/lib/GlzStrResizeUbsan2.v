(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMuslMemset1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
(* [comment removed for export] *)
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
(* [comment removed for export] *)
#[local] Ltac cond :=
  rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
(* [comment removed for export] *)
#[local] Ltac pclits :=
  repeat match goal with
         | |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
         end.
(* [comment removed for export] *)
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

  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  #[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).
  (* [comment removed for export] *)
  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

  (* [comment removed for export] *)
  Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
  Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
  Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma A_exit0 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (n = 0)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF []) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hn.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_tk Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      mret.
      pu_refl.
    - post.
  Qed.

  Lemma A_exit2 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (1 <= n <= 2)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L2) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hok Hnw Hn.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      msb Fo_004 Do_004 0%Z.                         (* [comment removed for export] *)
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
      stepn Fo_00c Do_00c.                           (* [comment removed for export] *)
      msb Fo_010 Do_010 (n-1)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_014 Do_014 ltac:(cond).          (* [comment removed for export] *)
      mret.
      pu_refl.
    - post.
  Qed.

  Lemma A_exit6 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (3 <= n <= 6)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L6) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hok Hnw Hn.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.                         (* [comment removed for export] *)
      msb Fo_01c Do_01c 2%Z.                         (* [comment removed for export] *)
      stepn Fo_020 Do_020.                           (* [comment removed for export] *)
      msb Fo_024 Do_024 (n-3)%Z.                     (* [comment removed for export] *)
      msb Fo_028 Do_028 (n-2)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_02c Do_02c ltac:(cond).          (* [comment removed for export] *)
      mret.
      pu_refl.
    - post.
  Qed.

  Lemma A_exit8 : forall regs,
    getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    (7 <= n <= 8)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L8) rom)
      /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
  Proof using Hret Hok Hnw Hn.
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
      msb Fo_030 Do_030 3%Z.                         (* [comment removed for export] *)
      stepn Fo_034 Do_034.                           (* [comment removed for export] *)
      msb Fo_038 Do_038 (n-4)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      mret.
      pu_refl.
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
  Proof using Hok Hnw Hn.
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
      stepb_ft Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      pu_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
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
      stepn Fo_040 Do_040;                           (* [comment removed for export] *)
      stepn Fo_044 Do_044;                           (* [comment removed for export] *)
      stepn Fo_048 Do_048;                           (* [comment removed for export] *)
      stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);   (* [comment removed for export] *)
      stepn Fo_050 Do_050;                           (* [comment removed for export] *)
      stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);          (* [comment removed for export] *)
      stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);  (* [comment removed for export] *)
      stepn Fo_05c Do_05c;                           (* [comment removed for export] *)
      stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);              (* [comment removed for export] *)
      stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);  (* [comment removed for export] *)
      msw Fo_068 Do_068 k;                           (* [comment removed for export] *)
      stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);  (* [comment removed for export] *)
      msw Fo_070 Do_070 (k + n1 - 4)%Z.              (* [comment removed for export] *)

    Lemma B_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
      getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (n1 < 9)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' ret (CF LB) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof using Hn1v Hkv Hn1 Hk Hret Hok Hnw.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_tk Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        mret.
        pu_refl.
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
    Proof using Hn1v Hkv Hn1 Hk Hok Hnw.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_ft Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        pu_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    #[local] Ltac blockC :=
      msw Fo_078 Do_078 (k + 4)%Z;                   (* [comment removed for export] *)
      msw Fo_07c Do_07c (k + 8)%Z;                   (* [comment removed for export] *)
      stepn Fo_080 Do_080;                           (* [comment removed for export] *)
      msw Fo_084 Do_084 (k + n1 - 12)%Z;             (* [comment removed for export] *)
      msw Fo_088 Do_088 (k + n1 - 8)%Z.              (* [comment removed for export] *)

    Lemma C_exit : forall regs,
      getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
      getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
      (9 <= n)%Z -> (12 <= n1)%Z -> (n1 < 25)%Z ->
      exists regs',
        msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' ret (CF LC) rom)
        /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
    Proof using Hn1 Hk Hret Hok Hnw.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_tk Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        mret.
        pu_refl.
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
    Proof using Hn1 Hk Hok Hnw.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_ft Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        pu_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Section D.
      Variable s4 : Z.
      Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
      Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

      #[local] Ltac blockD :=
        msw Fo_090 Do_090 (k + 12)%Z;                (* [comment removed for export] *)
        msw Fo_094 Do_094 (k + 16)%Z;                (* [comment removed for export] *)
        msw Fo_098 Do_098 (k + 20)%Z;                (* [comment removed for export] *)
        msw Fo_09c Do_09c (k + 24)%Z;                (* [comment removed for export] *)
        stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);          (* [comment removed for export] *)
        stepn Fo_0a4 Do_0a4;                         (* [comment removed for export] *)
        stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);  (* [comment removed for export] *)
        stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);  (* [comment removed for export] *)
        msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;           (* [comment removed for export] *)
        msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;           (* [comment removed for export] *)
        msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;           (* [comment removed for export] *)
        msw Fo_0bc Do_0bc (k + n1 - 16)%Z.           (* [comment removed for export] *)

      Lemma D_exit : forall regs,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z -> (n1 - s4 - 24 < 32)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' ret (CF (LD s4)) rom)
          /\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
      Proof using Hs4v Hs4 Hn1 Hk Hret Hok Hnw.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_tk Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          mret.
          pu_refl.
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
      Proof using Hs4v Hs4 Hn1 Hk Hok Hnw.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_ft Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          pu_refl.
        - post.
      Qed.

      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (* [comment removed for export] *)

      Lemma E_run : forall regs L,
        getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
        getr regs 14 = Z_to_bv 64 (n1 - s4 - 24) -> getr regs 15 = Z_to_bv 64 (s4 + 24) -> getr regs 1 = ret ->
        (9 <= n)%Z -> (28 <= n1)%Z ->
        exists regs',
          msteps MSEGS (mkst regs (PC 0xc4) (CF L) rom) (mkst regs' (PC 0xd8) (CF L) rom)
          /\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d (k + s4 + 24) /\ getr regs' 12 = c64 cv
          /\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24)
          /\ getr regs' 1 = ret /\ ms_agree regs regs'.
      Proof using Hs4.
        intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).             (* [comment removed for export] *)
          stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
          stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);             (* [comment removed for export] *)
          stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).                 (* [comment removed for export] *)
          stepn Fo_0d4 Do_0d4.                       (* [comment removed for export] *)
          pu_refl.
        - post.
      Qed.
    End D.
  End Aligned.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Ltac ms_cov_eq :=
    intros i Hi; rewrite !ms_cov_cons;
    match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
    rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
    apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

  (* [comment removed for export] *)
  Lemma loop_run : forall (q : nat) regs L a r,
    getr regs 10 = at_ d 0 -> getr regs 11 = at_ d a -> getr regs 12 = c64 cv ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r -> getr regs 1 = ret ->
    (0 <= a)%Z -> (a + r <= n)%Z ->
    (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xd8) (CF L) rom)
                   (mkst regs' (PC 0xf4) (CF ((a, 32 * (Z.of_nat q + 1))%Z :: L)) rom)
      /\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
  Proof using Hok Hnw.
    induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
      pose proof (u64_range d) as Hd; pclits.
    - (* [comment removed for export] *)
      eexists. split.
      + msd Fo_0d8 Do_0d8 a.                         (* [comment removed for export] *)
        msd Fo_0dc Do_0dc (a + 8)%Z.                 (* [comment removed for export] *)
        msd Fo_0e0 Do_0e0 (a + 16)%Z.                (* [comment removed for export] *)
        msd Fo_0e4 Do_0e4 (a + 24)%Z.                (* [comment removed for export] *)
        stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).  (* [comment removed for export] *)
        stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).               (* [comment removed for export] *)
        stepb_ft Fo_0f0 Do_0f0 ltac:(cond).        (* [comment removed for export] *)
        replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
          with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        pu_refl.
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
          stepb_tk Fo_0f0 Do_0f0 ltac:(cond).      (* [comment removed for export] *)
          pu_refl.
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

  (* [comment removed for export] *)
  Lemma ret_run : forall regs (M : word -> option byte),
    getr regs 1 = ret ->
    exists regs',
      msteps MSEGS (mkst regs (PC 0xf4) M rom) (mkst regs' ret M rom)
      /\ regs' = regs.
  Proof using Hret.
    intros regs M H1. pclits. eexists. split.
    - mret. pu_refl.
    - reflexivity.
  Qed.

End Walk.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMuslMemset1.
Module UbMuslMemset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode UbMuslMemset1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

#[local] Ltac solve_incl :=
  let x := fresh "x" in let H := fresh "H" in
  intros x H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [cbn [In]; repeat first [left; reflexivity | right] |]);
  destruct H.

Section Summary.
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

  (* [comment removed for export] *)
  #[local] Ltac cover L' :=
    apply (cfill_full_chain mem0 d n (cbyte cv) Hn Hnw _ L');
    [ unfold L2, L6, L8, LB, LC, LD; solve_incl
    | cbn [ms_chain]; lia ].

  Theorem memset_summary : forall regs,
    getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    exists regs',
      msteps MSEGS (mkst regs (Z_to_bv 64 ms_base) mem0 rom)
                   (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10 = d /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1.
    pose proof (u64_range d) as Hd.
    rewrite <- (at_0 d) in H10.
    replace (Z_to_bv 64 ms_base) with (PC 0) by (f_equal; lia).
    replace (mkst regs (PC 0) mem0 rom) with (mkst regs (PC 0) (CF []) rom) by (rewrite cfill_nil; reflexivity).
    (* [comment removed for export] *)
    assert (FIN : forall regs' (M : word -> option byte),
              M = wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n)) ->
              msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret M rom) ->
              getr regs' 10 = at_ d 0 -> ms_agree regs regs' ->
              exists regs'',
                msteps MSEGS (mkst regs (PC 0) (CF []) rom)
                       (mkst regs'' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
                /\ getr regs'' 10 = d /\ ms_agree regs regs'').
    { intros regs' M -> RUN P10 AG. exists regs'. rewrite at_0 in P10. auto. }
    destruct (Z.lt_ge_cases n 9) as [Hsmall|Hn9].
    { (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      { destruct (A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption.
        rewrite cfill_nil. rewrite Hz. reflexivity. }
      destruct (Z.lt_ge_cases n 3) as [H3|H3].
      { destruct (A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption. cover ([(0,1); (n-1,1)]%Z). }
      destruct (Z.lt_ge_cases n 7) as [H7|H7].
      { destruct (A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption. cover ([(0,1); (1,1); (2,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
      destruct (A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
      eapply (FIN r1); try eassumption.
      cover ([(0,1); (1,1); (2,1); (3,1); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    (* [comment removed for export] *)
    destruct (A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)
      as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q15 & Q1 & AG1).
    (* [comment removed for export] *)
    set (k := ((- bv_unsigned d) mod 4)%Z).
    pose proof (neg_mod4_range (bv_unsigned d)) as Hk. fold k in Hk.
    pose proof (negw_and3 d) as Hkv. fold k in Hkv.
    set (n1 := (n - k - (n - k) mod 4)%Z).
    set (m1 := ((n - k) / 4)%Z).
    pose proof (Z.div_mod (n - k) 4 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as Hmb.
    assert (Hm1 : (4 * m1 = n1)%Z) by (subst n1 m1; lia).
    assert (Hn1 : (n - k - 3 <= n1 <= n - k)%Z) by (subst n1; lia).
    pose proof (andi_m4 (n - k) ltac:(lia)) as Hn1v. fold n1 in Hn1v.
    clearbody n1 m1. clear Hdm Hmb.
    destruct (Z.lt_ge_cases n1 9) as [HB|HB].
    { (* [comment removed for export] *)
      destruct (B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
        as (r2 & RUN2 & P10 & AG2).
      eapply (FIN r2); [| eapply msteps_trans; [exact RUN1 | exact RUN2] | exact P10 | eapply ms_agree_trans; eassumption].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+n1-4,4); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
      as (r2 & RUN2 & S10 & S11 & S12 & S13 & S14 & S1 & AG2).
    destruct (Z.lt_ge_cases n1 25) as [HC|HC].
    { destruct (C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)
        as (r3 & RUN3 & P10 & AG3).
      eapply (FIN r3); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)
      as (r3 & RUN3 & T10 & T11 & T12 & T13 & T14 & T1 & AG3).
    destruct (andi_4_cases (at_ d k)) as (s4 & Hs4v & Hs4).
    destruct (Z.lt_ge_cases (n1 - s4 - 24) 32) as [HD|HD].
    { destruct (D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
        as (r4 & RUN4 & P10 & AG4).
      eapply (FIN r4); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                            eapply msteps_trans; [exact RUN3 | exact RUN4]]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
              (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
      as (r4 & RUN4 & U10 & U11 & U12 & U14 & U15 & U1 & AG4).
    destruct (E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))
      as (r5 & RUN5 & V10 & V11 & V12 & V13 & V14 & V1 & AG5).
    (* [comment removed for export] *)
    set (r := (n1 - s4 - 24)%Z) in *.
    set (q := Z.to_nat (r / 32 - 1)).
    assert (Hq : (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod r 32 ltac:(lia)). pose proof (Z.mod_pos_bound r 32 ltac:(lia)). lia. }
    destruct (loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
                V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)
      as (r6 & RUN6 & W10 & W1 & AG6).
    destruct (ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)
      as (r7 & RUN7 & ->).
    eapply (FIN r6); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                          eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 |
                          eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]]
                     | exact W10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
    cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
            (k+s4+24, 32 * (Z.of_nat q + 1));
            (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
            (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z).
  Qed.

End Summary.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_entry : word := ltac:(let l := word_lit (Z_to_bv 64 ms_base) in exact l).

Lemma ms_entry_eq : Z_to_bv 64 ms_base = ms_entry.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Corollary memset_summary_lit :
  ltac:(let T := type of memset_summary in
        let l := eval cbv delta [ms_entry] in ms_entry in
        lazymatch T with
        | context C [Z_to_bv 64 ms_base] => let T' := context C [l] in exact T'
        end).
Proof.
  pose proof memset_summary as H. rewrite ms_entry_eq in H. exact H.
Qed.

End FPGen1.
End UbMuslMemset.
Require Stdlib.NArith.NArith LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzStrResizeUbsan.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode UbMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound.PuKin.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac u_norm ::= pu_u_norm.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation USEGS := Ubsan.M.loaded_segments.
#[local] Notation W8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Ltac kin := first [ reflexivity | (left; reflexivity) | (right; kin) ].
(* [comment removed for export] *)
Ltac kin_lit r := lazymatch r with @BV _ ?z _ => kin_lit z | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac kin_lits G := lazymatch G with False => idtac | (?a = ?b) \/ ?R => kin_lit a; kin_lit b; kin_lits R | ?a = ?b => kin_lit a; kin_lit b end.
Ltac kin_nt := lazymatch goal with |- ?G => tryif kin_lits G then fail else tauto end.
(* [comment removed for export] *)
Ltac kin_from Hx := cbv [callee_kept In] in Hx |- *;
  repeat (destruct Hx as [<-|Hx]; [ kin |]); first [ destruct Hx | tauto ].
Ltac kept_in := cbv [callee_kept In]; first [ kin | kin_nt ].

(* [comment removed for export] *)
Ltac okstk :=
  repeat (eapply store_ok_mono; [apply wbytes_grows|]);
  match goal with
  | Hs : store_ok _ ?M0 (Z_to_bv 64 (bv_unsigned ?sp0 - ?F)) ?Fn = true |- _ =>
      eapply (store_ok_sub _ M0 (Z_to_bv 64 (bv_unsigned sp0 - F)) _ Fn 8);
      [u_norm; lia | exact Hs | u_norm; lia | u_norm; cbn; lia]
  end.
(* [comment removed for export] *)
Ltac msd F D aa :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
      | gres; rwH; reflexivity
      | okstk ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac mld8 F D vv RD :=
  chain_step; [reflexivity
    | eapply step_ld with (v := vv);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          lazymatch type of RD with rdn _ _ ?c _ = _ =>
            replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
        exact RD
      | apply bytes_le_to_Z_8 ]
    | step_simpl]; vnorm.

Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
Proof. intros v. apply length_N_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma wbytes_fill_at1 : forall M (a : word) (b : byte), wbytes M a [b] a = Some b.
Proof. intros. cbn [wbytes]. rewrite bv_eqb_refl. reflexivity. Qed.

Section PIECES.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition app_saved : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24].
Ltac kept_in ::= cbv [callee_kept app_saved In]; first [ kin | kin_nt ].
(* [comment removed for export] *)
#[local] Ltac kept_in ::= first [ pu_kept_fast | cbv [callee_kept app_saved In]; first [ kin | kin_nt ] ].
Ltac kin_from Hx ::= cbv [callee_kept app_saved In] in Hx |- *; repeat (destruct Hx as [<-|Hx]; [ kin |]); first [ destruct Hx | tauto ].

Definition app_mem1 (M : word -> option byte) (sp : word) (regs : bvmap 5 word) : word -> option byte :=
  let w (k : Z) (r : bv 5) m := wbytes m (Z_to_bv 64 (bv_unsigned sp - 8 * k)) (W8 (getr regs r)) in
  w 10%Z 24 (w 9%Z 23 (w 8%Z 22 (w 7%Z 21 (w 6%Z 20 (w 5%Z 19 (w 4%Z 18 (w 3%Z 9 (w 2%Z 8 (w 1%Z 1 M))))))))).

Lemma app_mem1_out : forall M sp regs (a : word),
  (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z -> app_mem1 M sp regs a = M a.
Proof using.
  intros M sp regs a Hsp Ha. pose proof (u64_range sp). unfold app_mem1.
  rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
Qed.

Lemma app_mem1_grows : forall M sp regs, mem_grows M (app_mem1 M sp regs).
Proof using.
  intros. unfold app_mem1. repeat (eapply mem_grows_trans; [| apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Lemma app_rd : forall M sp regs k r, (80 <= bv_unsigned sp)%Z ->
  In (k, r) [(1%Z, 1); (2%Z, 8); (3%Z, 9); (4%Z, 18); (5%Z, 19); (6%Z, 20); (7%Z, 21); (8%Z, 22); (9%Z, 23); (10%Z, 24)] ->
  rdn USEGS (app_mem1 M sp regs) (Z_to_bv 64 (bv_unsigned sp - 8 * k)) 8 = Some (W8 (getr regs r)).
Proof using.
  intros M sp regs k r Hsp Hin. pose proof (u64_range sp). unfold app_mem1. cbv [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-;
    repeat (rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia));
    apply rdn_wbytes_hit8; u_norm; lia |]).
  destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma app_pro : forall regs M (sp obj na : word),
  getr regs 2 = sp -> getr regs 10 = obj -> getr regs 11 = na ->
  (bv_unsigned na <> 0)%Z -> (80 <= bv_unsigned sp)%Z ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true ->
  exists r1,
    msteps USEGS (mkst regs (0x5c000 : word) M rom) (mkst r1 (0x5c038 : word) (app_mem1 M sp regs) rom)
    /\ getr r1 2 = Z_to_bv 64 (bv_unsigned sp - 80) /\ getr r1 8 = obj /\ getr r1 9 = na
    /\ getr r1 10 = obj /\ getr r1 12 = getr regs 12
    /\ (forall x : bv 5, In x [3; 4; 25; 26; 27] -> getr r1 x = getr regs x).
Proof using.
  intros regs M sp obj na H2 H10 H11 Hna Hsp Hstk.
  pose proof (u64_range sp) as Hspr. pose proof (u64_range na) as Hnar.
  eexists. split.
  - stepiv F_5bfa0 D_5bfa0 (Z_to_bv 64 (bv_unsigned sp - 80))
      ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).      (* [comment removed for export] *)
    msd F_5bfa4 D_5bfa4 (Z_to_bv 64 (bv_unsigned sp - 8)).           (* [comment removed for export] *)
    msd F_5bfa8 D_5bfa8 (Z_to_bv 64 (bv_unsigned sp - 16)).          (* [comment removed for export] *)
    msd F_5bfac D_5bfac (Z_to_bv 64 (bv_unsigned sp - 24)).          (* [comment removed for export] *)
    msd F_5bfb0 D_5bfb0 (Z_to_bv 64 (bv_unsigned sp - 32)).          (* [comment removed for export] *)
    msd F_5bfb4 D_5bfb4 (Z_to_bv 64 (bv_unsigned sp - 40)).          (* [comment removed for export] *)
    msd F_5bfb8 D_5bfb8 (Z_to_bv 64 (bv_unsigned sp - 48)).          (* [comment removed for export] *)
    msd F_5bfbc D_5bfbc (Z_to_bv 64 (bv_unsigned sp - 56)).          (* [comment removed for export] *)
    msd F_5bfc0 D_5bfc0 (Z_to_bv 64 (bv_unsigned sp - 64)).          (* [comment removed for export] *)
    msd F_5bfc4 D_5bfc4 (Z_to_bv 64 (bv_unsigned sp - 72)).          (* [comment removed for export] *)
    msd F_5bfc8 D_5bfc8 (Z_to_bv 64 (bv_unsigned sp - 80)).          (* [comment removed for export] *)
    stepn F_5bfcc D_5bfcc.                                            (* [comment removed for export] *)
    stepb_ft F_5bfd0 D_5bfd0 ltac:(rwH; apply c_eq_neq; unorm; cbn; lia).  (* [comment removed for export] *)
    stepn F_5bfd4 D_5bfd4.                                            (* [comment removed for export] *)
    rwH. unfold app_mem1. pu_refl.
  - repeat split; gres; rwH; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma app_epi : forall r (M' : word -> option byte) (sp : word) regs0,
  getr r 2 = Z_to_bv 64 (bv_unsigned sp - 80) -> (80 <= bv_unsigned sp)%Z ->
  (forall k x, In (k, x) [(1%Z, 1); (2%Z, 8); (3%Z, 9); (4%Z, 18); (5%Z, 19); (6%Z, 20); (7%Z, 21); (8%Z, 22); (9%Z, 23); (10%Z, 24)] ->
     rdn USEGS M' (Z_to_bv 64 (bv_unsigned sp - 8 * k)) 8 = Some (W8 (getr regs0 x))) ->
  ret_ok (getr regs0 1) ->
  exists r2,
    msteps USEGS (mkst r (0x5c1a0 : word) M' rom) (mkst r2 (getr regs0 1) M' rom)
    /\ getr r2 2 = sp /\ getr r2 10 = getr r 8
    /\ (forall x : bv 5, In x [1; 8; 9; 18; 19; 20; 21; 22; 23; 24] -> getr r2 x = getr regs0 x)
    /\ (forall x : bv 5, In x [3; 4; 25; 26; 27] -> getr r2 x = getr r x).
Proof using.
  intros r M' sp regs0 H2 Hsp RD Hret.
  pose proof (u64_range sp) as Hspr.
  pose proof (RD 1%Z 1 ltac:(kept_in)) as RD1. pose proof (RD 2%Z 8 ltac:(kept_in)) as RD2.
  pose proof (RD 3%Z 9 ltac:(kept_in)) as RD3. pose proof (RD 4%Z 18 ltac:(kept_in)) as RD4.
  pose proof (RD 5%Z 19 ltac:(kept_in)) as RD5. pose proof (RD 6%Z 20 ltac:(kept_in)) as RD6.
  pose proof (RD 7%Z 21 ltac:(kept_in)) as RD7. pose proof (RD 8%Z 22 ltac:(kept_in)) as RD8.
  pose proof (RD 9%Z 23 ltac:(kept_in)) as RD9. pose proof (RD 10%Z 24 ltac:(kept_in)) as RD10.
  cbn [Z.mul Pos.mul] in RD1, RD2, RD3, RD4, RD5, RD6, RD7, RD8, RD9, RD10.
  eexists. split.
  - stepn F_5c140 D_5c140.                                            (* [comment removed for export] *)
    mld8 F_5c144 D_5c144 (getr regs0 1) RD1.                          (* [comment removed for export] *)
    mld8 F_5c148 D_5c148 (getr regs0 8) RD2.                          (* [comment removed for export] *)
    mld8 F_5c14c D_5c14c (getr regs0 9) RD3.
    mld8 F_5c150 D_5c150 (getr regs0 18) RD4.
    mld8 F_5c154 D_5c154 (getr regs0 19) RD5.
    mld8 F_5c158 D_5c158 (getr regs0 20) RD6.
    mld8 F_5c15c D_5c15c (getr regs0 21) RD7.
    mld8 F_5c160 D_5c160 (getr regs0 22) RD8.
    mld8 F_5c164 D_5c164 (getr regs0 23) RD9.
    mld8 F_5c168 D_5c168 (getr regs0 24) RD10.
    stepiv F_5c16c D_5c16c sp
      ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                      (* [comment removed for export] *)
    stepret F_5c170 D_5c170 (getr regs0 1) ltac:(reflexivity).
    pu_refl.
  - repeat split; gres; rwH; try reflexivity; try bveq.
    + intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    + intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lob (w : word) : byte := Z_to_bv 8 (bv_unsigned w).
Lemma rdn1_of_rdn8 : forall M (a : word) (w : word),
  rdn USEGS M a 8 = Some (W8 w) -> rdn USEGS M a 1 = Some [lob w].
Proof using.
  intros M a w H. pose proof (rdn_firstn USEGS M 8 a (W8 w) 1 H ltac:(lia)) as H1.
  rewrite H1. unfold lob. cbn. reflexivity.
Qed.
Lemma u_lob : forall w : word, bv_unsigned (lob w) = (bv_unsigned w mod 256)%Z.
Proof using. intros w. unfold lob. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma land_1 : forall x, (0 <= x)%Z -> Z.land x 1 = (x mod 2)%Z.
Proof using. intros x Hx. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Ltac mlbu F D bb RD :=
  chain_step; [reflexivity
    | eapply (step_lbu _ _ _ _ _ _ _ _ _ bb);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          lazymatch type of RD with rdn _ _ ?c _ = _ =>
            first [exact RD | replace a with c by (unfold v_addi; unorm; first [f_equal; lia | apply bv_eq; u_norm; lia]); exact RD] end end ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac mld F D vv RD :=
  chain_step; [reflexivity
    | eapply step_ld with (v := vv);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          lazymatch type of RD with rdn _ _ ?c _ = _ =>
            first [exact RD | replace a with c by (unfold v_addi; unorm; first [f_equal; lia | apply bv_eq; u_norm; lia]); exact RD] end end
      | apply bytes_le_to_Z_8 ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac msb F D aa bb oktac :=
  chain_step; [reflexivity
    | eapply step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia]
      | gres; rwH; reflexivity
      | u_norm; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]
      | oktac ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac msdg F D aa oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia]
      | gres; rwH; reflexivity
      | oktac ]
    | step_simpl]; vnorm.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma resize_short_le : forall regs M (obj ret : word) (w0 : word) (s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 256 = 2 * s)%Z ->
  (0 <= n <= s)%Z -> (s <= 22)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  store_ok USEGS M obj 1 = true ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  exists r',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom)
                 (mkst r' ret (wbytes (wbytes M obj [Z_to_bv 8 (2 * n)]) (Z_to_bv 64 (bv_unsigned obj + 1 + n)) [Z_to_bv 8 0]) rom)
    /\ (forall x : bv 5, In x [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x).
Proof using.
  intros regs M obj ret w0 s n RD8 Hw0 Hn Hs Hobj ST0 ST1 Hret H1 H10 H11.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr.
  pose proof (rdn1_of_rdn8 M obj w0 RD8) as RD1.
  assert (Ulob : bv_unsigned (lob w0) = (2 * s)%Z) by (rewrite u_lob; exact Hw0).
  eexists. split.
  - mlbu F_5c178 D_5c178 (lob w0) RD1.                                   (* [comment removed for export] *)
    stepiv F_5c17c D_5c17c (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_andi; rewrite Ulob, u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; rewrite Z.mul_comm, Z.mod_mul; lia).   (* [comment removed for export] *)
    stepb_tk F_5c180 D_5c180 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepiv F_5c1a8 D_5c1a8 (Z_to_bv 64 s)
      ltac:(gres; rwH; unfold v_srli; rewrite Ulob, u64_lit by lia; change (bv_unsigned (1%bv : bv 6)) with 1%Z;
            rewrite Z.shiftr_div_pow2 by lia; f_equal; change (2 ^ 1)%Z with 2%Z; rewrite Z.mul_comm, Z.div_mul; lia).
                                                                          (* [comment removed for export] *)
    stepb_tk F_5c1ac D_5c1ac ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).  (* [comment removed for export] *)
    stepb_ft F_5c18c D_5c18c ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepiv F_5c190 D_5c190 (Z_to_bv 64 (bv_unsigned obj + 1))
      ltac:(gres; rwH; unfold v_addi; imm_norm; reflexivity).           (* [comment removed for export] *)
    stepiv F_5c194 D_5c194 (Z_to_bv 64 (2 * n))
      ltac:(gres; rwH; unfold v_slli; u_norm; change (bv_unsigned (1%bv : bv 6)) with 1%Z; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
                                                                          (* [comment removed for export] *)
    msb F_5c198 D_5c198 obj (Z_to_bv 8 (2 * n)) ltac:(exact ST0).        (* [comment removed for export] *)
    stepiv F_5c19c D_5c19c (Z_to_bv 64 (bv_unsigned obj + 1 + n))
      ltac:(gres; rwH; unfold v_add; u_norm; f_equal; lia).             (* [comment removed for export] *)
    msb F_5c1a0 D_5c1a0 (Z_to_bv 64 (bv_unsigned obj + 1 + n)) (Z_to_bv 8 0)
      ltac:(eapply store_ok_mono; [apply wbytes_grows | exact ST1]).    (* [comment removed for export] *)
    stepret F_5c1a4 D_5c1a4 ret ltac:(rwH; reflexivity).
    pu_refl.
  - intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma resize_long_le : forall regs M (obj ret w0 d : word) (s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 2 = 1)%Z ->
  rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
  rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
  (0 <= n <= s)%Z -> (s < 2 ^ 63)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (bv_unsigned d + s < 2 ^ 64)%Z ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned d + n)) 1 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  exists r',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom)
                 (mkst r' ret (wbytes (wbytes M (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 n)))
                                      (Z_to_bv 64 (bv_unsigned d + n)) [Z_to_bv 8 0]) rom)
    /\ (forall x : bv 5, In x [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x).
Proof using.
  intros regs M obj ret w0 d s n RD8 Hw0 RDs RDd Hn Hs Hobj Hd ST8 ST1 Hret H1 H10 H11.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr. pose proof (u64_range d) as Hdr.
  pose proof (rdn1_of_rdn8 M obj w0 RD8) as RD1.
  assert (Ulob1 : (bv_unsigned (lob w0) mod 2 = 1)%Z).
  { rewrite u_lob. rewrite Z.mod_mod_divide by (exists 128%Z; reflexivity). exact Hw0. }
  pose proof (conj (Z.mod_pos_bound (bv_unsigned w0) 256 ltac:(lia)) (u_lob w0)) as Ulr.
  eexists. split.
  - mlbu F_5c178 D_5c178 (lob w0) RD1.                                   (* [comment removed for export] *)
    stepiv F_5c17c D_5c17c (Z_to_bv 64 1)
      ltac:(gres; rwH; unfold v_andi; rewrite u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Ulob1).              (* [comment removed for export] *)
    stepb_ft F_5c180 D_5c180 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    mld F_5c184 D_5c184 (Z_to_bv 64 s) RDs.                               (* [comment removed for export] *)
    stepb_ft F_5c188 D_5c188 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).  (* [comment removed for export] *)
    stepb_tk F_5c18c D_5c18c ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    mld F_5c1b8 D_5c1b8 d RDd.                                            (* [comment removed for export] *)
    msdg F_5c1bc D_5c1bc (Z_to_bv 64 (bv_unsigned obj + 8)) ltac:(exact ST8).   (* [comment removed for export] *)
    stepiv F_5c1c0 D_5c1c0 (Z_to_bv 64 (bv_unsigned d + n))
      ltac:(gres; rwH; unfold v_add; u_norm; f_equal; lia).             (* [comment removed for export] *)
    msb F_5c1c4 D_5c1c4 (Z_to_bv 64 (bv_unsigned d + n)) (Z_to_bv 8 0)
      ltac:(eapply store_ok_mono; [apply wbytes_grows | exact ST1]).    (* [comment removed for export] *)
    stepret F_5c1c8 D_5c1c8 ret ltac:(rwH; reflexivity).
    pu_refl.
  - intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma app_mem1_ext : forall M sp regs regs',
  (forall x : bv 5, In x app_saved -> getr regs' x = getr regs x) -> app_mem1 M sp regs' = app_mem1 M sp regs.
Proof using rom.   (* [comment removed for export] *)
  intros M sp regs regs' H. unfold app_mem1, app_saved in *.
  rewrite !(H 1) by kept_in. rewrite !(H 8) by kept_in. rewrite !(H 9) by kept_in. rewrite !(H 18) by kept_in.
  rewrite !(H 19) by kept_in. rewrite !(H 20) by kept_in. rewrite !(H 21) by kept_in. rewrite !(H 22) by kept_in.
  rewrite !(H 23) by kept_in. rewrite !(H 24) by kept_in. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rs_head_short_gt : forall regs M (obj : word) (w0 : word) (s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 256 = 2 * s)%Z ->
  (0 <= s < n)%Z -> (n < 2 ^ 63)%Z ->
  getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  exists r',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom) (mkst r' (0x5c000 : word) M rom)
    /\ getr r' 11 = Z_to_bv 64 (n - s) /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [1; 2; 3; 4; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x).
Proof using.
  intros regs M obj w0 s n RD8 Hw0 Hn Hn63 H10 H11.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr.
  pose proof (rdn1_of_rdn8 M obj w0 RD8) as RD1.
  assert (Ulob : bv_unsigned (lob w0) = (2 * s)%Z) by (rewrite u_lob; exact Hw0).
  eexists. split.
  - mlbu F_5c178 D_5c178 (lob w0) RD1.                                   (* [comment removed for export] *)
    stepiv F_5c17c D_5c17c (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_andi; rewrite Ulob, u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; rewrite Z.mul_comm, Z.mod_mul; lia).   (* [comment removed for export] *)
    stepb_tk F_5c180 D_5c180 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepiv F_5c1a8 D_5c1a8 (Z_to_bv 64 s)
      ltac:(gres; rwH; unfold v_srli; rewrite Ulob, u64_lit by lia; change (bv_unsigned (1%bv : bv 6)) with 1%Z;
            rewrite Z.shiftr_div_pow2 by lia; f_equal; change (2 ^ 1)%Z with 2%Z; rewrite Z.mul_comm, Z.div_mul; lia).
    stepb_ft F_5c1ac D_5c1ac ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
    stepiv F_5c1b0 D_5c1b0 (Z_to_bv 64 (n - s))
      ltac:(gres; rwH; unfold v_sub; u_norm; f_equal; lia).             (* [comment removed for export] *)
    stepn F_5c1b4 D_5c1b4.                                                (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; try reflexivity.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma shl56_shr57 : forall x, (0 <= x)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 56))) 57 = ((x mod 256) / 2)%Z.
Proof using.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (256 * 2 ^ 56)%Z. rewrite Z.mul_mod_distr_r by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 57)%Z with (2 ^ 56 * 2)%Z.
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma app_body_short : forall r1 M1 (obj spl : word) (w0 cw : word) (s na : Z),
  rdn USEGS M1 obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 256 = 2 * s)%Z ->
  (0 <= s)%Z -> (0 < na)%Z -> (s + na <= 22)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  getr r1 2 = spl -> getr r1 8 = obj -> getr r1 9 = Z_to_bv 64 na -> getr r1 12 = cw ->
  exists r',
    msteps USEGS (mkst r1 (0x5c038 : word) M1 rom) (mkst r' (0x73830 : word) M1 rom)
    /\ getr r' 1 = (0x5c17c : word) /\ getr r' 10 = Z_to_bv 64 (bv_unsigned obj + 1 + s)
    /\ getr r' 11 = cw /\ getr r' 12 = Z_to_bv 64 na
    /\ getr r' 2 = spl /\ getr r' 8 = obj /\ getr r' 9 = Z_to_bv 64 na /\ getr r' 18 = Z_to_bv 64 s
    /\ getr r' 20 = Z_to_bv 64 (bv_unsigned obj + 1) /\ getr r' 22 = Z_to_bv 64 (s + na)
    /\ (forall x : bv 5, In x [3; 4; 19; 21; 24; 25; 26; 27] -> getr r' x = getr r1 x).
Proof using.
  intros r1 M1 obj spl w0 cw s na RD8 Hw0 Hs Hna Hfit Hobj H2 H8 H9 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr.
  pose proof (rdn1_of_rdn8 M1 obj w0 RD8) as RD1.
  assert (Ulob : bv_unsigned (lob w0) = (2 * s)%Z) by (rewrite u_lob; exact Hw0).
  assert (Ev : (bv_unsigned w0 mod 2 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide (bv_unsigned w0) 256 2) by (exists 128%Z; reflexivity). rewrite Hw0, Z.mul_comm. apply Z.mod_mul. lia. }
  eexists. split.
  - mlbu F_5bfd8 D_5bfd8 (lob w0) RD1.                                   (* [comment removed for export] *)
    mld F_5bfdc D_5bfdc w0 RD8.                                            (* [comment removed for export] *)
    stepiv F_5bfe0 D_5bfe0 (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_andi; rewrite Ulob, u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; rewrite Z.mul_comm, Z.mod_mul; lia).   (* [comment removed for export] *)
    stepb_ft F_5bfe4 D_5bfe4 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepn F_5bfe8 D_5bfe8.                                                (* [comment removed for export] *)
    stepiv F_5bfec D_5bfec (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Ev).                 (* [comment removed for export] *)
    stepb_ft F_5bff0 D_5bff0 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepiv F_5bff4 D_5bff4 (Z_to_bv 64 (Z.shiftl (bv_unsigned w0) 56))
      ltac:(gres; rwH; unfold v_slli; reflexivity).                     (* [comment removed for export] *)
    stepiv F_5bff8 D_5bff8 (Z_to_bv 64 s)
      ltac:(gres; rwH; unfold v_srli; change (bv_unsigned (57%bv : bv 6)) with 57%Z; rewrite shl56_shr57 by lia;
            f_equal; rewrite Hw0, Z.mul_comm, Z.div_mul; lia).        (* [comment removed for export] *)
    stepiv F_5bffc D_5bffc (Z_to_bv 64 (22 - s))
      ltac:(gres; rwH; unfold v_sub; u_norm; f_equal; lia).             (* [comment removed for export] *)
    stepb_ft F_5c000 D_5c000 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).  (* [comment removed for export] *)
    stepb_tk F_5c004 D_5c004 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepiv F_5c070 D_5c070 (Z_to_bv 64 (bv_unsigned obj + 1))
      ltac:(gres; rwH; unfold v_addi; imm_norm; reflexivity).           (* [comment removed for export] *)
    stepiv F_5c074 D_5c074 (Z_to_bv 64 (s + na))
      ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).              (* [comment removed for export] *)
    stepn F_5c078 D_5c078.                                                (* [comment removed for export] *)
    stepiv F_5c10c D_5c10c (Z_to_bv 64 (bv_unsigned obj + 1 + s))
      ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).              (* [comment removed for export] *)
    stepn F_5c110 D_5c110.                                                (* [comment removed for export] *)
    stepn F_5c114 D_5c114.                                                (* [comment removed for export] *)
    stepn F_5c118 D_5c118.                                                (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma app_tail_short : forall r M2 (obj : word) (b0 : byte) (n : Z),
  rdn USEGS M2 obj 1 = Some [b0] -> (bv_unsigned b0 mod 2 = 0)%Z ->
  (0 <= n <= 22)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  store_ok USEGS M2 obj 1 = true ->
  store_ok USEGS M2 (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true ->
  getr r 8 = obj -> getr r 20 = Z_to_bv 64 (bv_unsigned obj + 1) -> getr r 22 = Z_to_bv 64 n ->
  exists r',
    msteps USEGS (mkst r (0x5c17c : word) M2 rom)
                 (mkst r' (0x5c1a0 : word) (wbytes (wbytes M2 obj [Z_to_bv 8 (2 * n)]) (Z_to_bv 64 (bv_unsigned obj + 1 + n)) [Z_to_bv 8 0]) rom)
    /\ (forall x : bv 5, In x [1; 2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M2 obj b0 n RD1 Hb0 Hn Hobj ST0 ST1 H8 H20 H22.
  pose proof (u64_range obj) as Hor.
  pose proof (bv_unsigned_in_range _ b0) as Hb0r. change (bv_modulus 8) with 256%Z in Hb0r.
  eexists. split.
  - mlbu F_5c11c D_5c11c b0 RD1.                                         (* [comment removed for export] *)
    stepiv F_5c120 D_5c120 (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_andi; rewrite u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Hb0).                (* [comment removed for export] *)
    stepb_ft F_5c124 D_5c124 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepiv F_5c128 D_5c128 (Z_to_bv 64 (2 * n))
      ltac:(gres; rwH; unfold v_slli; u_norm; change (bv_unsigned (1%bv : bv 6)) with 1%Z; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
                                                                          (* [comment removed for export] *)
    msb F_5c12c D_5c12c obj (Z_to_bv 8 (2 * n)) ltac:(exact ST0).        (* [comment removed for export] *)
    stepn F_5c130 D_5c130.                                                (* [comment removed for export] *)
    stepiv F_5c138 D_5c138 (Z_to_bv 64 (bv_unsigned obj + 1 + n))
      ltac:(gres; rwH; unfold v_add; u_norm; f_equal; lia).             (* [comment removed for export] *)
    msb F_5c13c D_5c13c (Z_to_bv 64 (bv_unsigned obj + 1 + n)) (Z_to_bv 8 0)
      ltac:(eapply store_ok_mono; [apply wbytes_grows | exact ST1]).    (* [comment removed for export] *)
    pu_refl.
  - intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Definition rs_short_fill_mem (M : word -> option byte) (sp : word) (regs : bvmap 5 word) (obj cw : word) (s n : Z) :=
  wbytes (wbytes (wbytes (app_mem1 M sp regs) (Z_to_bv 64 (bv_unsigned obj + 1 + s)) (repeat (cbyte cw) (Z.to_nat (n - s))))
                 obj [Z_to_bv 8 (2 * n)])
         (Z_to_bv 64 (bv_unsigned obj + 1 + n)) [Z_to_bv 8 0].

Theorem resize_short_fill : forall regs M (obj sp ret w0 cw : word) (s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 256 = 2 * s)%Z ->
  (0 <= s < n)%Z -> (n <= 22)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj)%Z ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true ->
  store_ok USEGS M obj 1 = true ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + s)) (Z.to_nat (n - s)) = true ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = cw ->
  exists r',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom) (mkst r' ret (rs_short_fill_mem M sp regs obj cw s n) rom)
    /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x).
Proof using.
  intros regs M obj sp ret w0 cw s n RD8 Hw0 Hsn Hn Hobj Hsp Hapart STF ST0 STM ST1 Hret H1 H2 H10 H11 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range sp) as Hspr.
  (* [comment removed for export] *)
  assert (OBJout : forall a : word, (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24)%Z ->
                   (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z) by (intros a Ha; lia).
  (* [comment removed for export] *)
  destruct (rs_head_short_gt regs M obj w0 s n RD8 Hw0 ltac:(lia) ltac:(lia) H10 H11) as (rA & RUNA & A11 & A10 & AK).
  (* [comment removed for export] *)
  assert (A2 : getr rA 2 = sp) by (rewrite (AK 2) by kept_in; exact H2).
  destruct (app_pro rA M sp obj (Z_to_bv 64 (n - s)) A2 A10 A11 ltac:(u_norm; lia) Hsp STF) as (rB & RUNB & B2 & B8 & B9 & B10 & B12 & BK).
  rewrite (app_mem1_ext M sp regs rA) in RUNB by (intros x Hx; apply AK; unfold app_saved in Hx; kin_from Hx).
  set (M1 := app_mem1 M sp regs) in *.
  assert (M1out : forall a : word, (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z -> M1 a = M a)
    by (intros a Ha; subst M1; apply app_mem1_out; [exact Hsp | exact Ha]).
  assert (RD8' : rdn USEGS M1 obj 8 = Some (W8 w0)).
  { rewrite <- RD8. apply rdn_ext; [cbn; lia|]. intros x Hx. apply M1out. apply OBJout. cbn in Hx. lia. }
  (* [comment removed for export] *)
  assert (B12' : getr rB 12 = cw) by (rewrite B12, (AK 12) by kept_in; exact H12).
  destruct (app_body_short rB M1 obj (Z_to_bv 64 (bv_unsigned sp - 80)) w0 cw s (n - s) RD8' Hw0 ltac:(lia) ltac:(lia) ltac:(lia) Hobj
              B2 B8 B9 B12') as (rC & RUNC & C1 & C10 & C11 & C12 & C2 & C8 & C9 & C18 & C20 & C22 & CK).
  (* [comment removed for export] *)
  assert (STM1 : store_ok USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 1 + s)) (Z.to_nat (n - s)) = true)
    by (eapply store_ok_mono; [subst M1; apply app_mem1_grows | exact STM]).
  destruct (memset_summary_lit M1 (Z_to_bv 64 (bv_unsigned obj + 1 + s)) cw (0x5c17c : word) (n - s) rom
              ltac:(lia) ltac:(u_norm; lia) STM1 ltac:(apply ret_ok_even; reflexivity) rC C10 C11 C12 C1)
    as (rD & RUND & D10 & DAG).
  pose proof (ms_agree_keeps _ _ DAG) as DK.
  set (M2 := wbytes M1 (Z_to_bv 64 (bv_unsigned obj + 1 + s)) (repeat (cbyte cw) (Z.to_nat (n - s)))) in *.
  assert (M2out : forall a : word, (bv_unsigned a < bv_unsigned obj + 1 + s \/ bv_unsigned obj + 1 + n <= bv_unsigned a)%Z -> M2 a = M1 a).
  { intros a Ha. subst M2. apply wbytes_outside; rewrite repeat_length; unfold in_rng; u_norm; lia. }
  (* [comment removed for export] *)
  assert (RD1'' : rdn USEGS M2 obj 1 = Some [lob w0]).
  { rewrite <- (rdn1_of_rdn8 M1 obj w0 RD8'). apply rdn_ext; [cbn; lia|]. intros x Hx. apply M2out. cbn in Hx. lia. }
  assert (Hlob : (bv_unsigned (lob w0) mod 2 = 0)%Z).
  { rewrite u_lob, Hw0, Z.mul_comm. apply Z.mod_mul. lia. }
  (* [comment removed for export] *)
  assert (D8 : getr rD 8 = obj) by (rewrite (DK 8) by kept_in; exact C8).
  assert (D20 : getr rD 20 = Z_to_bv 64 (bv_unsigned obj + 1)) by (rewrite (DK 20) by kept_in; exact C20).
  assert (D22 : getr rD 22 = Z_to_bv 64 n) by (rewrite (DK 22) by kept_in; rewrite C22; f_equal; lia).
  assert (ST0' : store_ok USEGS M2 obj 1 = true).
  { eapply store_ok_mono; [subst M2; apply wbytes_grows|]. eapply store_ok_mono; [subst M1; apply app_mem1_grows | exact ST0]. }
  assert (ST1' : store_ok USEGS M2 (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true).
  { eapply store_ok_mono; [subst M2; apply wbytes_grows|]. eapply store_ok_mono; [subst M1; apply app_mem1_grows | exact ST1]. }
  destruct (app_tail_short rD M2 obj (lob w0) n RD1'' Hlob ltac:(lia) Hobj ST0' ST1' D8 D20 D22) as (rE & RUNE & EK).
  set (M3 := wbytes (wbytes M2 obj [Z_to_bv 8 (2 * n)]) (Z_to_bv 64 (bv_unsigned obj + 1 + n)) [Z_to_bv 8 0]) in *.
  assert (M3out : forall a : word, (bv_unsigned a < bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned a)%Z -> M3 a = M1 a).
  { intros a Ha. subst M3. rewrite !wbytes_outside by (cbn; unfold in_rng; u_norm; lia). apply M2out. lia. }
  (* [comment removed for export] *)
  assert (E2 : getr rE 2 = Z_to_bv 64 (bv_unsigned sp - 80)) by (rewrite (EK 2) by kept_in; rewrite (DK 2) by kept_in; exact C2).
  assert (RDF : forall k x, In (k, x) [(1%Z, 1); (2%Z, 8); (3%Z, 9); (4%Z, 18); (5%Z, 19); (6%Z, 20); (7%Z, 21); (8%Z, 22); (9%Z, 23); (10%Z, 24)] ->
            rdn USEGS M3 (Z_to_bv 64 (bv_unsigned sp - 8 * k)) 8 = Some (W8 (getr regs x))).
  { intros k x Hin. rewrite <- (app_rd M sp regs k x Hsp Hin). fold M1.
    assert (Hk : (1 <= k <= 10)%Z) by (first [ solve [ clear - Hin; cbv [In] in Hin; decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try lia; contradiction ] | cbv [In] in Hin; decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try lia; contradiction ]).
    apply rdn_ext; [cbn; u_norm; lia|]. intros y Hy. revert Hy. u_norm. cbn. intros Hy. apply M3out. lia. }
  assert (Hret1 : ret_ok (getr regs 1)) by (rewrite H1; exact Hret).
  destruct (app_epi rE M3 sp regs E2 Hsp RDF Hret1) as (rF & RUNF & F2 & F10 & FK1 & FK2).
  exists rF. split; [|split].
  - eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUNC|].
    eapply msteps_trans; [exact RUND|]. eapply msteps_trans; [exact RUNE|].
    rewrite H1 in RUNF. unfold rs_short_fill_mem. fold M1. fold M2. fold M3. exact RUNF.
  - rewrite F10, (EK 8) by kept_in. exact D8.
  - intros x Hx. cbv [In] in Hx.
    repeat (destruct Hx as [<-|Hx];
      [ lazymatch goal with |- getr _ ?y = _ =>
          first [ rewrite F2; symmetry; exact H2
                | rewrite (FK1 y ltac:(kept_in)); reflexivity
                | rewrite (FK2 y ltac:(kept_in)), (EK y ltac:(kept_in)), (DK y ltac:(kept_in)), (CK y ltac:(kept_in)), (BK y ltac:(kept_in));
                  apply AK; kept_in ] end |]).
    destruct Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rs_head_long_gt : forall regs M (obj : word) (w0 : word) (s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 2 = 1)%Z ->
  rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
  (0 <= s < n)%Z -> (n < 2 ^ 63)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  exists r',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom) (mkst r' (0x5c000 : word) M rom)
    /\ getr r' 11 = Z_to_bv 64 (n - s) /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [1; 2; 3; 4; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x).
Proof using.
  intros regs M obj w0 s n RD8 Hw0 RDs Hn Hn63 Hobj H10 H11.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr.
  pose proof (rdn1_of_rdn8 M obj w0 RD8) as RD1.
  assert (Ulob1 : (bv_unsigned (lob w0) mod 2 = 1)%Z).
  { rewrite u_lob. rewrite Z.mod_mod_divide by (exists 128%Z; reflexivity). exact Hw0. }
  pose proof (conj (Z.mod_pos_bound (bv_unsigned w0) 256 ltac:(lia)) (u_lob w0)) as Ulr.
  eexists. split.
  - mlbu F_5c178 D_5c178 (lob w0) RD1.                                   (* [comment removed for export] *)
    stepiv F_5c17c D_5c17c (Z_to_bv 64 1)
      ltac:(gres; rwH; unfold v_andi; rewrite u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Ulob1).              (* [comment removed for export] *)
    stepb_ft F_5c180 D_5c180 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    mld F_5c184 D_5c184 (Z_to_bv 64 s) RDs.                               (* [comment removed for export] *)
    stepb_tk F_5c188 D_5c188 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
    stepiv F_5c1b0 D_5c1b0 (Z_to_bv 64 (n - s))
      ltac:(gres; rwH; unfold v_sub; u_norm; f_equal; lia).             (* [comment removed for export] *)
    stepn F_5c1b4 D_5c1b4.                                                (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; try reflexivity.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma app_body_long : forall r1 M1 (obj spl d : word) (w0 cw : word) (cap s na : Z),
  rdn USEGS M1 obj 8 = Some (W8 w0) -> (bv_unsigned w0 = cap + 2)%Z -> ((cap + 1) mod 2 = 0)%Z ->
  rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
  rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
  (0 <= s)%Z -> (0 < na)%Z -> (s + na <= cap)%Z -> (cap < 2 ^ 62)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (bv_unsigned d + cap < 2 ^ 64)%Z ->
  getr r1 2 = spl -> getr r1 8 = obj -> getr r1 9 = Z_to_bv 64 na -> getr r1 12 = cw ->
  exists r',
    msteps USEGS (mkst r1 (0x5c038 : word) M1 rom) (mkst r' (0x73830 : word) M1 rom)
    /\ getr r' 1 = (0x5c17c : word) /\ getr r' 10 = Z_to_bv 64 (bv_unsigned d + s)
    /\ getr r' 11 = cw /\ getr r' 12 = Z_to_bv 64 na
    /\ getr r' 2 = spl /\ getr r' 8 = obj /\ getr r' 9 = Z_to_bv 64 na /\ getr r' 18 = Z_to_bv 64 s
    /\ getr r' 20 = d /\ getr r' 22 = Z_to_bv 64 (s + na)
    /\ (forall x : bv 5, In x [3; 4; 19; 21; 24; 25; 26; 27] -> getr r' x = getr r1 x).
Proof using.
  intros r1 M1 obj spl d w0 cw cap s na RD8 Hw0 Hcap RDs RDd Hs Hna Hfit Hcap62 Hobj Hd H2 H8 H9 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr. pose proof (u64_range d) as Hdr.
  pose proof (rdn1_of_rdn8 M1 obj w0 RD8) as RD1.
  assert (Odd : (bv_unsigned w0 mod 2 = 1)%Z).
  { rewrite Hw0. replace (cap + 2)%Z with (cap + 1 + 1)%Z by lia. rewrite Z.add_mod, Hcap by lia. reflexivity. }
  assert (Ulob1 : (bv_unsigned (lob w0) mod 2 = 1)%Z).
  { rewrite u_lob. rewrite Z.mod_mod_divide by (exists 128%Z; reflexivity). exact Odd. }
  pose proof (conj (Z.mod_pos_bound (bv_unsigned w0) 256 ltac:(lia)) (u_lob w0)) as Ulr.
  eexists. split.
  - mlbu F_5bfd8 D_5bfd8 (lob w0) RD1.                                   (* [comment removed for export] *)
    mld F_5bfdc D_5bfdc w0 RD8.                                            (* [comment removed for export] *)
    stepiv F_5bfe0 D_5bfe0 (Z_to_bv 64 1)
      ltac:(gres; rwH; unfold v_andi; rewrite u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Ulob1).              (* [comment removed for export] *)
    stepb_tk F_5bfe4 D_5bfe4 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    stepiv F_5c010 D_5c010 (Z_to_bv 64 (cap + 1))
      ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 (bv_signed (4094%bv : bv 12))) with (2 ^ 64 - 2 ^ 1)%Z;
            rewrite AX2S.land_highmask by lia; f_equal; change (2 ^ 1)%Z with 2%Z; lia).   (* [comment removed for export] *)
    stepiv F_5c014 D_5c014 (Z_to_bv 64 cap)
      ltac:(gres; rwH; unfold v_addi; u_norm; imm_norm; f_equal; lia).  (* [comment removed for export] *)
    stepiv F_5c018 D_5c018 (Z_to_bv 64 1)
      ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Odd).                (* [comment removed for export] *)
    stepb_ft F_5c01c D_5c01c ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    mld F_5c020 D_5c020 (Z_to_bv 64 s) RDs.                               (* [comment removed for export] *)
    stepiv F_5c024 D_5c024 (Z_to_bv 64 (cap - s))
      ltac:(gres; rwH; unfold v_sub; u_norm; f_equal; lia).             (* [comment removed for export] *)
    stepb_tk F_5c028 D_5c028 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).  (* [comment removed for export] *)
    stepb_ft F_5c004 D_5c004 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    mld F_5c008 D_5c008 d RDd.                                             (* [comment removed for export] *)
    stepn F_5c00c D_5c00c.                                                (* [comment removed for export] *)
    stepiv F_5c074 D_5c074 (Z_to_bv 64 (s + na))
      ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).              (* [comment removed for export] *)
    stepn F_5c078 D_5c078.                                                (* [comment removed for export] *)
    stepiv F_5c10c D_5c10c (Z_to_bv 64 (bv_unsigned d + s))
      ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).              (* [comment removed for export] *)
    stepn F_5c110 D_5c110.                                                (* [comment removed for export] *)
    stepn F_5c114 D_5c114.                                                (* [comment removed for export] *)
    stepn F_5c118 D_5c118.                                                (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma app_tail_long : forall r M2 (obj d : word) (w0 : word) (n : Z),
  rdn USEGS M2 obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 2 = 1)%Z ->
  (0 <= n)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
  store_ok USEGS M2 (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true ->
  store_ok USEGS M2 (Z_to_bv 64 (bv_unsigned d + n)) 1 = true ->
  getr r 8 = obj -> getr r 20 = d -> getr r 22 = Z_to_bv 64 n ->
  exists r',
    msteps USEGS (mkst r (0x5c17c : word) M2 rom)
                 (mkst r' (0x5c1a0 : word) (wbytes (wbytes M2 (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 n)))
                                                   (Z_to_bv 64 (bv_unsigned d + n)) [Z_to_bv 8 0]) rom)
    /\ (forall x : bv 5, In x [1; 2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M2 obj d w0 n RD8 Hw0 Hn Hobj Hd ST8 ST1 H8 H20 H22.
  pose proof (u64_range obj) as Hor. pose proof (u64_range d) as Hdr. pose proof (u64_range w0) as Hwr.
  pose proof (rdn1_of_rdn8 M2 obj w0 RD8) as RD1.
  assert (Ulob1 : (bv_unsigned (lob w0) mod 2 = 1)%Z).
  { rewrite u_lob. rewrite Z.mod_mod_divide by (exists 128%Z; reflexivity). exact Hw0. }
  pose proof (conj (Z.mod_pos_bound (bv_unsigned w0) 256 ltac:(lia)) (u_lob w0)) as Ulr.
  eexists. split.
  - mlbu F_5c11c D_5c11c (lob w0) RD1.                                   (* [comment removed for export] *)
    stepiv F_5c120 D_5c120 (Z_to_bv 64 1)
      ltac:(gres; rwH; unfold v_andi; rewrite u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Ulob1).              (* [comment removed for export] *)
    stepb_tk F_5c124 D_5c124 ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    msdg F_5c134 D_5c134 (Z_to_bv 64 (bv_unsigned obj + 8)) ltac:(exact ST8).   (* [comment removed for export] *)
    stepiv F_5c138 D_5c138 (Z_to_bv 64 (bv_unsigned d + n))
      ltac:(gres; rwH; unfold v_add; u_norm; f_equal; lia).             (* [comment removed for export] *)
    msb F_5c13c D_5c13c (Z_to_bv 64 (bv_unsigned d + n)) (Z_to_bv 8 0)
      ltac:(eapply store_ok_mono; [apply wbytes_grows | exact ST1]).    (* [comment removed for export] *)
    pu_refl.
  - intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Definition rs_long_fill_mem (M : word -> option byte) (sp : word) (regs : bvmap 5 word) (obj d cw : word) (s n : Z) :=
  wbytes (wbytes (wbytes (app_mem1 M sp regs) (Z_to_bv 64 (bv_unsigned d + s)) (repeat (cbyte cw) (Z.to_nat (n - s))))
                 (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 n)))
         (Z_to_bv 64 (bv_unsigned d + n)) [Z_to_bv 8 0].

Theorem resize_long_fill : forall regs M (obj sp ret d w0 cw : word) (cap s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 = cap + 2)%Z -> ((cap + 1) mod 2 = 0)%Z ->
  rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
  rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
  (0 <= s < n)%Z -> (n <= cap)%Z -> (cap < 2 ^ 62)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (bv_unsigned d + cap + 1 <= 2 ^ 64)%Z -> (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj)%Z ->
  (bv_unsigned d + cap + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned d)%Z ->
  (bv_unsigned d + cap + 1 <= bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned d)%Z ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned d + s)) (Z.to_nat (n - s)) = true ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned d + n)) 1 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = cw ->
  exists r',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom) (mkst r' ret (rs_long_fill_mem M sp regs obj d cw s n) rom)
    /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x).
Proof using.
  intros regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd Hsn Hn Hcap62 Hobj Hd Hsp Hapart Hdfr Hdobj STF ST8 STM ST1
         Hret H1 H2 H10 H11 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range sp) as Hspr. pose proof (u64_range d) as Hdr.
  assert (Odd : (bv_unsigned w0 mod 2 = 1)%Z).
  { rewrite Hw0. replace (cap + 2)%Z with (cap + 1 + 1)%Z by lia. rewrite Z.add_mod, Hcap by lia. reflexivity. }
  (* [comment removed for export] *)
  destruct (rs_head_long_gt regs M obj w0 s n RD8 Odd RDs ltac:(lia) ltac:(lia) Hobj H10 H11) as (rA & RUNA & A11 & A10 & AK).
  (* [comment removed for export] *)
  assert (A2 : getr rA 2 = sp) by (rewrite (AK 2) by kept_in; exact H2).
  destruct (app_pro rA M sp obj (Z_to_bv 64 (n - s)) A2 A10 A11 ltac:(u_norm; lia) Hsp STF) as (rB & RUNB & B2 & B8 & B9 & B10 & B12 & BK).
  rewrite (app_mem1_ext M sp regs rA) in RUNB by (intros x Hx; apply AK; unfold app_saved in Hx; kin_from Hx).
  set (M1 := app_mem1 M sp regs) in *.
  assert (M1out : forall a : word, (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z -> M1 a = M a)
    by (intros a Ha; subst M1; apply app_mem1_out; [exact Hsp | exact Ha]).
  assert (M1grows : mem_grows M M1) by (subst M1; apply app_mem1_grows).
  assert (RD8' : rdn USEGS M1 obj 8 = Some (W8 w0)).
  { rewrite <- RD8. apply rdn_ext; [cbn; lia|]. intros x Hx. apply M1out. cbn in Hx. lia. }
  assert (RDs' : rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s))).
  { rewrite <- RDs. apply rdn_ext; [cbn; u_norm; lia|]. intros x Hx. apply M1out. revert Hx. u_norm. cbn. intros Hx. lia. }
  assert (RDd' : rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d)).
  { rewrite <- RDd. apply rdn_ext; [cbn; u_norm; lia|]. intros x Hx. apply M1out. revert Hx. u_norm. cbn. intros Hx. lia. }
  (* [comment removed for export] *)
  assert (B12' : getr rB 12 = cw) by (rewrite B12, (AK 12) by kept_in; exact H12).
  destruct (app_body_long rB M1 obj (Z_to_bv 64 (bv_unsigned sp - 80)) d w0 cw cap s (n - s) RD8' Hw0 Hcap RDs' RDd'
              ltac:(lia) ltac:(lia) ltac:(lia) Hcap62 Hobj ltac:(lia) B2 B8 B9 B12')
    as (rC & RUNC & C1 & C10 & C11 & C12 & C2 & C8 & C9 & C18 & C20 & C22 & CK).
  (* [comment removed for export] *)
  assert (STM1 : store_ok USEGS M1 (Z_to_bv 64 (bv_unsigned d + s)) (Z.to_nat (n - s)) = true)
    by (eapply store_ok_mono; [exact M1grows | exact STM]).
  destruct (memset_summary_lit M1 (Z_to_bv 64 (bv_unsigned d + s)) cw (0x5c17c : word) (n - s) rom
              ltac:(lia) ltac:(u_norm; lia) STM1 ltac:(apply ret_ok_even; reflexivity) rC C10 C11 C12 C1)
    as (rD & RUND & D10 & DAG).
  pose proof (ms_agree_keeps _ _ DAG) as DK.
  set (M2 := wbytes M1 (Z_to_bv 64 (bv_unsigned d + s)) (repeat (cbyte cw) (Z.to_nat (n - s)))) in *.
  assert (M2out : forall a : word, (bv_unsigned a < bv_unsigned d + s \/ bv_unsigned d + n <= bv_unsigned a)%Z -> M2 a = M1 a).
  { intros a Ha. subst M2. apply wbytes_outside; rewrite repeat_length; unfold in_rng; u_norm; lia. }
  assert (M2grows : mem_grows M M2) by (eapply mem_grows_trans; [exact M1grows | subst M2; apply wbytes_grows]).
  assert (RD8'' : rdn USEGS M2 obj 8 = Some (W8 w0)).
  { rewrite <- RD8'. apply rdn_ext; [cbn; lia|]. intros x Hx. apply M2out. cbn in Hx. lia. }
  (* [comment removed for export] *)
  assert (D8 : getr rD 8 = obj) by (rewrite (DK 8) by kept_in; exact C8).
  assert (D20 : getr rD 20 = d) by (rewrite (DK 20) by kept_in; exact C20).
  assert (D22 : getr rD 22 = Z_to_bv 64 n) by (rewrite (DK 22) by kept_in; rewrite C22; f_equal; lia).
  assert (ST8' : store_ok USEGS M2 (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true) by (eapply store_ok_mono; [exact M2grows | exact ST8]).
  assert (ST1' : store_ok USEGS M2 (Z_to_bv 64 (bv_unsigned d + n)) 1 = true) by (eapply store_ok_mono; [exact M2grows | exact ST1]).
  destruct (app_tail_long rD M2 obj d w0 n RD8'' Odd ltac:(lia) Hobj ltac:(lia) ST8' ST1' D8 D20 D22) as (rE & RUNE & EK).
  set (M3 := wbytes (wbytes M2 (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 n))) (Z_to_bv 64 (bv_unsigned d + n)) [Z_to_bv 8 0]) in *.
  assert (M3out : forall a : word,
            (bv_unsigned a < bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned a)%Z ->
            (bv_unsigned a < bv_unsigned d \/ bv_unsigned d + cap + 1 <= bv_unsigned a)%Z -> M3 a = M1 a).
  { intros a Ha Hb. subst M3. rewrite !wbytes_outside by (rewrite ?lenW8; cbn; unfold in_rng; u_norm; lia). apply M2out. lia. }
  (* [comment removed for export] *)
  assert (E2 : getr rE 2 = Z_to_bv 64 (bv_unsigned sp - 80)) by (rewrite (EK 2) by kept_in; rewrite (DK 2) by kept_in; exact C2).
  assert (RDF : forall k x, In (k, x) [(1%Z, 1); (2%Z, 8); (3%Z, 9); (4%Z, 18); (5%Z, 19); (6%Z, 20); (7%Z, 21); (8%Z, 22); (9%Z, 23); (10%Z, 24)] ->
            rdn USEGS M3 (Z_to_bv 64 (bv_unsigned sp - 8 * k)) 8 = Some (W8 (getr regs x))).
  { intros k x Hin. rewrite <- (app_rd M sp regs k x Hsp Hin). fold M1.
    assert (Hk : (1 <= k <= 10)%Z) by (first [ solve [ clear - Hin; cbv [In] in Hin; decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try lia; contradiction ] | cbv [In] in Hin; decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end; try lia; contradiction ]).
    apply rdn_ext; [cbn; u_norm; lia|]. intros y Hy. revert Hy. u_norm. cbn. intros Hy. apply M3out; lia. }
  assert (Hret1 : ret_ok (getr regs 1)) by (rewrite H1; exact Hret).
  destruct (app_epi rE M3 sp regs E2 Hsp RDF Hret1) as (rF & RUNF & F2 & F10 & FK1 & FK2).
  exists rF. split; [|split].
  - eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUNC|].
    eapply msteps_trans; [exact RUND|]. eapply msteps_trans; [exact RUNE|].
    rewrite H1 in RUNF. unfold rs_long_fill_mem. fold M1. fold M2. fold M3. exact RUNF.
  - rewrite F10, (EK 8) by kept_in. exact D8.
  - intros x Hx. cbv [In] in Hx.
    repeat (destruct Hx as [<-|Hx];
      [ lazymatch goal with |- getr _ ?y = _ =>
          first [ rewrite F2; symmetry; exact H2
                | rewrite (FK1 y ltac:(kept_in)); reflexivity
                | rewrite (FK2 y ltac:(kept_in)), (EK y ltac:(kept_in)), (DK y ltac:(kept_in)), (CK y ltac:(kept_in)), (BK y ltac:(kept_in));
                  apply AK; kept_in ] end |]).
    destruct Hx.
Qed.

End PIECES.
End GlzStrResizeUbsan.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode UbMuslMemset GlzStrResizeUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac u_norm ::= pu_u_norm.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation USEGS := Ubsan.M.loaded_segments.
#[local] Notation W8 v := (word_to_le_bytes 8 v).
Ltac kept_in := cbv [callee_kept app_saved In]; first [ kin | kin_nt ].   (* [comment removed for export] *)

Section UNIFORM.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem resize_short_any : forall regs M (obj sp ret w0 cw : word) (s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 256 = 2 * s)%Z ->
  (0 <= s <= 22)%Z -> (0 <= n <= 22)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj)%Z ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true ->
  store_ok USEGS M obj 24 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = cw ->
  exists r' M',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom) (mkst r' ret M' rom)
    /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x)
    /\ (forall a : word, M' a <> M a ->
          (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 \/ bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp)%Z)
    /\ mem_grows M M'
    /\ rdn USEGS M' obj 1 = Some [Z_to_bv 8 (2 * n)]
    /\ M' (Z_to_bv 64 (bv_unsigned obj + 1 + n)) = Some (Z_to_bv 8 0).
Proof using.
  intros regs M obj sp ret w0 cw s n RD8 Hw0 Hs Hn Hobj Hsp Hapart STF STO Hret H1 H2 H10 H11 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range sp) as Hspr.
  assert (STb : forall z m, (0 <= z <= 23)%Z -> (z + Z.of_nat m <= 24)%Z -> store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + z)) m = true).
  { intros z m Hz Hm. eapply (store_ok_sub USEGS M obj _ 24); [cbn; lia | exact STO | u_norm; lia | u_norm; cbn; lia]. }
  assert (ST0 : store_ok USEGS M obj 1 = true).
  { rewrite <- (Z_to_bv_bv_unsigned 64 obj). rewrite <- (Z.add_0_r (bv_unsigned obj)). apply STb; cbn; lia. }
  destruct (Z.le_gt_cases n s) as [Hle|Hgt].
  - (* [comment removed for export] *)
    assert (ST1 : store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true).
    { replace (bv_unsigned obj + 1 + n)%Z with (bv_unsigned obj + (1 + n))%Z by lia. apply STb; cbn; lia. }
    destruct (resize_short_le rom regs M obj ret w0 s n RD8 Hw0 ltac:(lia) ltac:(lia) Hobj ST0 ST1 Hret H1 H10 H11) as (r' & RUN & K).
    exists r', (wbytes (wbytes M obj [Z_to_bv 8 (2 * n)]) (Z_to_bv 64 (bv_unsigned obj + 1 + n)) [Z_to_bv 8 0]).
    split; [exact RUN|]. split; [rewrite (K 10) by kept_in; exact H10|]. split; [intros x Hx; apply K; kin_from Hx|].
    split; [|split; [|split]].
    + intros a Ha. left.
      assert (OUT : (bv_unsigned a < bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned a)%Z -> False).
      { intros O1. apply Ha. rewrite !wbytes_outside by (cbn; unfold in_rng; u_norm; lia). reflexivity. }
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj)) as [L|L]; [exfalso; apply OUT; lia|].
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 24)) as [U|U]; [lia | exfalso; apply OUT; lia].
    + eapply mem_grows_trans; apply wbytes_grows.
    + rewrite rdn_wbytes_out by (cbn; u_norm; lia). apply (rdn_wbytes_hit USEGS [Z_to_bv 8 (2 * n)]). cbn. lia.
    + apply (wbytes_fill_at1 _ _ _). 
  - (* [comment removed for export] *)
    assert (ST1 : store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + n)) 1 = true).
    { replace (bv_unsigned obj + 1 + n)%Z with (bv_unsigned obj + (1 + n))%Z by lia. apply STb; cbn; lia. }
    assert (STM : store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 1 + s)) (Z.to_nat (n - s)) = true).
    { replace (bv_unsigned obj + 1 + s)%Z with (bv_unsigned obj + (1 + s))%Z by lia. apply STb; lia. }
    destruct (resize_short_fill rom regs M obj sp ret w0 cw s n RD8 Hw0 ltac:(lia) ltac:(lia) Hobj Hsp Hapart STF ST0
                STM ST1 Hret H1 H2 H10 H11 H12) as (r' & RUN & A0 & K).
    exists r', (rs_short_fill_mem M sp regs obj cw s n).
    split; [exact RUN|]. split; [exact A0|]. split; [exact K|].
    unfold rs_short_fill_mem. split; [|split; [|split]].
    + intros a Ha.
      assert (OUT : (bv_unsigned a < bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned a)%Z ->
                    (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z -> False).
      { intros O1 O2. apply Ha. rewrite !wbytes_outside by (rewrite ?repeat_length; cbn; unfold in_rng; u_norm; lia).
        apply app_mem1_out; [exact Hsp | exact O2]. }
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj)) as [L|L];
        [| destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 24)) as [U|U]; [left; lia|]];
        right;
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp - 80)) as [L2|L2]; [exfalso; apply OUT; lia|]);
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp)) as [U2|U2]; [lia | exfalso; apply OUT; lia]).
    + eapply mem_grows_trans; [apply app_mem1_grows|]. eapply mem_grows_trans; [apply wbytes_grows|].
      eapply mem_grows_trans; apply wbytes_grows.
    + rewrite rdn_wbytes_out by (cbn; u_norm; lia). apply (rdn_wbytes_hit USEGS [Z_to_bv 8 (2 * n)]). cbn. lia.
    + apply (wbytes_fill_at1 _ _ _).
Qed.

(* [comment removed for export] *)
Theorem resize_long_inplace_any : forall regs M (obj sp ret d w0 cw : word) (cap s n : Z),
  rdn USEGS M obj 8 = Some (W8 w0) -> (bv_unsigned w0 = cap + 2)%Z -> ((cap + 1) mod 2 = 0)%Z ->
  rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
  rdn USEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
  (0 <= s <= cap)%Z -> (0 <= n <= cap)%Z -> (cap < 2 ^ 62)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> (bv_unsigned d + cap + 1 <= 2 ^ 64)%Z -> (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj)%Z ->
  (bv_unsigned d + cap + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned d)%Z ->
  (bv_unsigned d + cap + 1 <= bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned d)%Z ->
  store_ok USEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true ->
  store_ok USEGS M obj 24 = true ->
  store_ok USEGS M d (Z.to_nat (cap + 1)) = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = obj -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = cw ->
  exists r' M',
    msteps USEGS (mkst regs (0x5c1d8 : word) M rom) (mkst r' ret M' rom)
    /\ getr r' 10 = obj
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr regs x)
    /\ (forall a : word, M' a <> M a ->
          (bv_unsigned obj + 8 <= bv_unsigned a < bv_unsigned obj + 16
           \/ bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1
           \/ bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp)%Z)
    /\ mem_grows M M'
    /\ rdn USEGS M' obj 8 = Some (W8 w0)
    /\ rdn USEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n))
    /\ rdn USEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d)
    /\ M' (Z_to_bv 64 (bv_unsigned d + n)) = Some (Z_to_bv 8 0).
Proof using.
  intros regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd Hs Hn Hcap62 Hobj Hd Hsp Hapart Hdfr Hdobj STF STO STD
         Hret H1 H2 H10 H11 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range sp) as Hspr. pose proof (u64_range d) as Hdr.
  assert (Odd : (bv_unsigned w0 mod 2 = 1)%Z).
  { rewrite Hw0. replace (cap + 2)%Z with (cap + 1 + 1)%Z by lia. rewrite Z.add_mod, Hcap by lia. reflexivity. }
  assert (ST8 : store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true).
  { eapply (store_ok_sub USEGS M obj _ 24); [cbn; lia | exact STO | u_norm; lia | u_norm; cbn; lia]. }
  assert (STDb : forall z m, (0 <= z <= cap)%Z -> (z + Z.of_nat m <= cap + 1)%Z -> store_ok USEGS M (Z_to_bv 64 (bv_unsigned d + z)) m = true).
  { intros z m Hz Hm. eapply (store_ok_sub USEGS M d _ (Z.to_nat (cap + 1))); [lia | exact STD | u_norm; lia | u_norm; lia]. }
  assert (ST1 : store_ok USEGS M (Z_to_bv 64 (bv_unsigned d + n)) 1 = true) by (apply STDb; cbn; lia).
  destruct (Z.le_gt_cases n s) as [Hle|Hgt].
  - (* [comment removed for export] *)
    destruct (resize_long_le rom regs M obj ret w0 d s n RD8 Odd RDs RDd ltac:(lia) ltac:(lia) Hobj ltac:(lia) ST8 ST1 Hret H1 H10 H11)
      as (r' & RUN & K).
    exists r', (wbytes (wbytes M (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 n))) (Z_to_bv 64 (bv_unsigned d + n)) [Z_to_bv 8 0]).
    split; [exact RUN|]. split; [rewrite (K 10) by kept_in; exact H10|]. split; [intros x Hx; apply K; kin_from Hx|].
    split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha.
      assert (OUT : (bv_unsigned a < bv_unsigned obj + 8 \/ bv_unsigned obj + 16 <= bv_unsigned a)%Z ->
                    bv_unsigned a <> (bv_unsigned d + n)%Z -> False).
      { intros O1 O2. apply Ha. rewrite !wbytes_outside by (rewrite ?lenW8; cbn; unfold in_rng; u_norm; lia). reflexivity. }
      destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned d + n)) as [E|NE]; [right; left; lia|].
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 8)) as [L|L]; [exfalso; apply OUT; lia|].
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 16)) as [U|U]; [left; lia | exfalso; apply OUT; lia].
    + eapply mem_grows_trans; apply wbytes_grows.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). exact RD8.
    + rewrite rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). apply rdn_wbytes_hit8. u_norm. lia.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). exact RDd.
    + apply (wbytes_fill_at1 _ _ _).
  - (* [comment removed for export] *)
    assert (STM : store_ok USEGS M (Z_to_bv 64 (bv_unsigned d + s)) (Z.to_nat (n - s)) = true) by (apply STDb; lia).
    destruct (resize_long_fill rom regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd ltac:(lia) ltac:(lia) Hcap62 Hobj Hd Hsp
                Hapart Hdfr Hdobj STF ST8 STM ST1 Hret H1 H2 H10 H11 H12) as (r' & RUN & A0 & K).
    exists r', (rs_long_fill_mem M sp regs obj d cw s n).
    split; [exact RUN|]. split; [exact A0|]. split; [exact K|].
    unfold rs_long_fill_mem.
    assert (AOUT : forall a : word, (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z ->
                   app_mem1 M sp regs a = M a) by (intros a Ha; apply app_mem1_out; [exact Hsp | exact Ha]).
    split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha.
      assert (OUT : (bv_unsigned a < bv_unsigned obj + 8 \/ bv_unsigned obj + 16 <= bv_unsigned a)%Z ->
                    (bv_unsigned a < bv_unsigned d \/ bv_unsigned d + cap + 1 <= bv_unsigned a)%Z ->
                    (bv_unsigned a < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a)%Z -> False).
      { intros O1 O2 O3. apply Ha. rewrite !wbytes_outside by (rewrite ?lenW8, ?repeat_length; cbn; unfold in_rng; u_norm; lia).
        apply AOUT. exact O3. }
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned d)) as [L1|L1];
        [| destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned d + cap + 1)) as [U1|U1]; [right; left; lia|]];
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 8)) as [L|L];
          [| destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned obj + 16)) as [U|U]; [left; lia|]]);
        right; right;
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp - 80)) as [L2|L2]; [exfalso; apply OUT; lia|]);
        (destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp)) as [U2|U2]; [lia | exfalso; apply OUT; lia]).
    + eapply mem_grows_trans; [apply app_mem1_grows|]. eapply mem_grows_trans; [apply wbytes_grows|].
      eapply mem_grows_trans; apply wbytes_grows.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8, ?repeat_length; cbn; u_norm; lia).
      rewrite <- RD8. apply rdn_ext; [cbn; lia|]. intros x Hx. apply AOUT. cbn in Hx. lia.
    + rewrite rdn_wbytes_out by (rewrite ?lenW8; cbn; u_norm; lia). apply rdn_wbytes_hit8. u_norm. lia.
    + rewrite !rdn_wbytes_out by (rewrite ?lenW8, ?repeat_length; cbn; u_norm; lia).
      rewrite <- RDd. apply rdn_ext; [cbn; u_norm; lia|]. intros x Hx. apply AOUT. revert Hx. u_norm. cbn. intros Hx. lia.
    + apply (wbytes_fill_at1 _ _ _).
Qed.

End UNIFORM.
