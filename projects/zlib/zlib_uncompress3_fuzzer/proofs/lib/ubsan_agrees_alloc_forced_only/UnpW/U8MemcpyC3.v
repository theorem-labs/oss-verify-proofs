(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8MemcpyMIS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8MemcpyMIS.U8MemcpyAL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8MemcpyMIS.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U8Memcpy_code.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C3.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
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
  Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c3_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21580 : word) (MK k) rom) (mkst regs' (0x216b8 : word) (MK (k + 1)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_21428 D_21428 k.                            (* [comment removed for export] *)
      stepn F_2142c D_2142c.                            (* [comment removed for export] *)
      stepb_tk F_21430 D_21430 ltac:(cond).             (* [comment removed for export] *)
      msb F_2154c D_2154c k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      stepn F_21550 D_21550.                            (* [comment removed for export] *)
      stepn F_21554 D_21554.                            (* [comment removed for export] *)
      stepn F_21558 D_21558.                            (* [comment removed for export] *)
      stepn F_2155c D_2155c.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
    (ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x216b8 : word) (MK kk) rom)
                   (mkst regs' (0x21718 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_21560 D_21560.                          (* [comment removed for export] *)
        mlw F_21564 D_21564 (kk + 3)%Z.                 (* [comment removed for export] *)
        mlw F_21568 D_21568 (kk + 7)%Z.                 (* [comment removed for export] *)
        mlw F_2156c D_2156c (kk + 11)%Z.                (* [comment removed for export] *)
        mlw F_21570 D_21570 (kk + 15)%Z.                (* [comment removed for export] *)
        stepn F_21574 D_21574. stepn F_21578 D_21578. stepn F_2157c D_2157c.
        stepn F_21580 D_21580. stepn F_21584 D_21584. stepn F_21588 D_21588.
        stepn F_2158c D_2158c. stepn F_21590 D_21590. stepn F_21594 D_21594.
        stepn F_21598 D_21598. stepn F_2159c D_2159c.
        stepn F_215a0 D_215a0.                          (* [comment removed for export] *)
        msw F_215a4 D_215a4 kk ltac:(m8).
        msw F_215a8 D_215a8 (kk + 4)%Z ltac:(m8).
        msw F_215ac D_215ac (kk + 8)%Z ltac:(m8).
        msw F_215b0 D_215b0 (kk + 12)%Z ltac:(m8).
        stepn F_215b4 D_215b4.                          (* [comment removed for export] *)
        stepn F_215b8 D_215b8.                          (* [comment removed for export] *)
        stepb_ft F_215bc D_215bc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x216b8 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
                         /\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
      + eexists. split.
        * stepn F_21560 D_21560.
          mlw F_21564 D_21564 (kk + 3)%Z.
          mlw F_21568 D_21568 (kk + 7)%Z.
          mlw F_2156c D_2156c (kk + 11)%Z.
          mlw F_21570 D_21570 (kk + 15)%Z.
          stepn F_21574 D_21574. stepn F_21578 D_21578. stepn F_2157c D_2157c.
          stepn F_21580 D_21580. stepn F_21584 D_21584. stepn F_21588 D_21588.
          stepn F_2158c D_2158c. stepn F_21590 D_21590. stepn F_21594 D_21594.
          stepn F_21598 D_21598. stepn F_2159c D_2159c.
          stepn F_215a0 D_215a0.
          msw F_215a4 D_215a4 kk ltac:(m8).
          msw F_215a8 D_215a8 (kk + 4)%Z ltac:(m8).
          msw F_215ac D_215ac (kk + 8)%Z ltac:(m8).
          msw F_215b0 D_215b0 (kk + 12)%Z ltac:(m8).
          stepn F_215b4 D_215b4.
          stepn F_215b8 D_215b8.
          stepb_tk F_215bc D_215bc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21718 : word) (MK kk) rom)
                   (mkst regs' (0x218cc : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x2156c : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_215c0 D_215c0.                        (* [comment removed for export] *)
          stepn F_215c4 D_215c4.                        (* [comment removed for export] *)
          stepb_tk F_215c8 D_215c8 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x217b8 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_215c0 D_215c0.
          stepn F_215c4 D_215c4.
          stepb_ft F_215c8 D_215c8 ltac:(cond).
          stepn F_215cc D_215cc.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) _ (fun r => mkst r (0x21844 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c3_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21580 : word) (MK k) rom)
                   (mkst regs' (0x218cc : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
