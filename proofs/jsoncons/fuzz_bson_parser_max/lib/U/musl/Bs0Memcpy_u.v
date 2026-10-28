(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.GcFlush03.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
  RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.musl Require Import Bs0MemcpyBase_u Bs0MemcpyAL_u Bs0MemcpyMIS_u Bs0MemcpyC1_u Bs0MemcpyC2_u Bs0MemcpyC3_u.
 From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0_code_r58000_59000_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Section ALL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  (* [comment removed for export] *)
  Ltac conda := rwH; unfold at_; cond.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_finish : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xab5a0 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    set (m := ((n - k) mod 16)%Z).
    pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0xab5dc : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
      subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
    cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0xab5fc : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0xab840 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
    destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mis_run : forall regs (ret : word) k q,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xab4d0 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
    destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
      assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xab4d8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. split.
        * stepn F_a9e9c D_a9e9c.                        (* [comment removed for export] *)
          stepb_ft F_a9ea0 D_a9ea0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        set (m := (n - k)%Z) in *.
        eapply (runs_trans RSEGS _ (fun r => mkst r (0xab840 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
                           /\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
          exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xab4f4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. split.
        * stepn F_a9e9c D_a9e9c.                        (* [comment removed for export] *)
          stepb_tk F_a9ea0 D_a9ea0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
        assert (CASE : exists regs' m,
          msteps RSEGS (mkst r1 (0xab4f4 : word) (MK k) rom)
                       (mkst regs' (0xab840 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
          /\ (0 <= m < 32)%Z
          /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
        { destruct Hq as [-> | [-> | ->]].
          - apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
        destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
        destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
        assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
        destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
        exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
        eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma j_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xab4c8 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    pose proof (u64_range dst).
    set (q := ((bv_unsigned dst + k) mod 4)%Z).
    pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
    destruct (Z.eq_dec q 0) as [Hq0|Hq0].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xab5a0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. split.
        * stepn F_a9e94 D_a9e94.                        (* [comment removed for export] *)
          stepb_tk F_a9e98 D_a9e98 ltac:(conda).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0xab4d0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. split.
        * stepn F_a9e94 D_a9e94.
          stepb_ft F_a9e98 D_a9e98 ltac:(conda).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
          change (bv_wrap 64 3) with 3%Z. reflexivity.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
        destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hl_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
    (Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xab498 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xab4c8 : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. split.
          -- mlbu F_a9e64 D_a9e64 k.                    (* [comment removed for export] *)
             stepn F_a9e68 D_a9e68.                    (* [comment removed for export] *)
             stepn F_a9e6c D_a9e6c.                    (* [comment removed for export] *)
             stepn F_a9e70 D_a9e70.                    (* [comment removed for export] *)
             msb F_a9e74 D_a9e74 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
             stepn F_a9e78 D_a9e78.                    (* [comment removed for export] *)
             stepn F_a9e7c D_a9e7c.                    (* [comment removed for export] *)
             stepb_tk F_a9e80 D_a9e80 ltac:(conda).    (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xab4c8 : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. split.
          -- mlbu F_a9e64 D_a9e64 k.
             stepn F_a9e68 D_a9e68.
             stepn F_a9e6c D_a9e6c.
             stepn F_a9e70 D_a9e70.
             msb F_a9e74 D_a9e74 k ltac:(apply sb_val_plain).
             stepn F_a9e78 D_a9e78.
             stepn F_a9e7c D_a9e7c.
             stepb_ft F_a9e80 D_a9e80 ltac:(conda).    (* [comment removed for export] *)
             stepn F_a9e84 D_a9e84.                    (* [comment removed for export] *)
             stepb_ft F_a9e88 D_a9e88 ltac:(cond).     (* [comment removed for export] *)
             stepn F_a9e8c D_a9e8c.                    (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xab498 : word) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
      + eexists. split.
        * mlbu F_a9e64 D_a9e64 k.
          stepn F_a9e68 D_a9e68.
          stepn F_a9e6c D_a9e6c.
          stepn F_a9e70 D_a9e70.
          msb F_a9e74 D_a9e74 k ltac:(apply sb_val_plain).
          stepn F_a9e78 D_a9e78.
          stepn F_a9e7c D_a9e7c.
          stepb_ft F_a9e80 D_a9e80 ltac:(conda).       (* [comment removed for export] *)
          stepn F_a9e84 D_a9e84.                       (* [comment removed for export] *)
          stepb_tk F_a9e88 D_a9e88 ltac:(cond).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ref_memcpy : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0xab480 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
    assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
    assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
    destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xab5a0 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a9e4c D_a9e4c.                     (* [comment removed for export] *)
             stepb_tk F_a9e50 D_a9e50 ltac:(conda).     (* [comment removed for export] *)
             stepn F_a9f60 D_a9f60.                     (* [comment removed for export] *)
             stepn F_a9f64 D_a9f64.                     (* [comment removed for export] *)
             stepb_ft F_a9f68 D_a9f68 ltac:(cond).      (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xab4d0 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a9e4c D_a9e4c.
             stepb_tk F_a9e50 D_a9e50 ltac:(conda).
             stepn F_a9f60 D_a9f60.
             stepn F_a9f64 D_a9f64.
             stepb_tk F_a9f68 D_a9f68 ltac:(cond).      (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post; try (rewrite at_0; reflexivity).
             unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
          pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
          destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xab4c8 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a9e4c D_a9e4c.                     (* [comment removed for export] *)
             stepb_ft F_a9e50 D_a9e50 ltac:(conda).     (* [comment removed for export] *)
             stepb_tk F_a9e54 D_a9e54 ltac:(cond).      (* [comment removed for export] *)
             stepn F_a9e90 D_a9e90.                     (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
        pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0xab498 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a9e4c D_a9e4c.                     (* [comment removed for export] *)
             stepb_ft F_a9e50 D_a9e50 ltac:(conda).     (* [comment removed for export] *)
             stepb_ft F_a9e54 D_a9e54 ltac:(cond).      (* [comment removed for export] *)
             stepn F_a9e58 D_a9e58.                     (* [comment removed for export] *)
             stepn F_a9e5c D_a9e5c.                     (* [comment removed for export] *)
             stepn F_a9e60 D_a9e60.                     (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
          destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
          { subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

End ALL.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

