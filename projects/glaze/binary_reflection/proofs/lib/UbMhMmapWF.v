(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhMmapW.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma land_negpage : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
  intros x Hx. apply Z.bits_inj'. intros k Hk.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite Z.land_spec, Z.ldiff_spec.
  replace (x - x mod 4096)%Z with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096 ltac:(lia)). lia. }
  rewrite <- (Z.ldiff_ones_r x 12) by lia. rewrite Z.ldiff_spec.
  destruct (Z.lt_ge_cases k 64) as [Hk64|Hk64].
  - rewrite (Z.ones_spec_low 64 k) by lia. cbn [andb]. reflexivity.
  - rewrite (Z.ones_spec_high 64 k) by lia. cbn [andb].
    assert (X0 : Z.testbit x k = false).
    { destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 64); [|lia]. apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))). lia. }
    rewrite X0. reflexivity.
Qed.

Lemma lxor_ones64 : forall r, (0 <= r < 2^64)%Z -> Z.lxor r (2^64 - 1) = (2^64 - 1 - r)%Z.
Proof.
  intros r Hr. change (2^64 - 1)%Z with (Z.ones 64) at 1.
  assert (LG : r = 0%Z \/ (Z.log2 r < 64)%Z).
  { destruct (Z.eq_dec r 0) as [->|]; [left; reflexivity|right]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.ldiff_ones_l_low; [| lia | destruct LG as [->|]; [cbn; lia| assumption]].
  symmetry. change (2^64 - 1)%Z with (Z.ones 64). apply Z.sub_nocarry_ldiff.
  destruct LG as [->|LG]; [reflexivity|]. apply Z.ldiff_ones_r_low; lia.
Qed.

Section MM.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp : Z) (hint len prot flags : Z).
  Hypothesis Hsp : (64 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 64)) 64%nat = true.
  Hypothesis Hhint : (0 <= hint < 2^64)%Z.
  Hypothesis Hlen : (0 < len < 2^62)%Z.
  Hypothesis Hprot : (0 <= prot < 8)%Z.

  (* [comment removed for export] *)
  Definition mm_frame (ra s0 s1 s2 s3 s4 s5 : word) : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 s5).

  Definition clobMM1 : list reg := [2; 5; 6; 8; 9; 16; 17; 18; 19; 20; 21]%bv.

  (* [comment removed for export] *)
  Lemma mmW1_34 : forall regs rom,
    flags = 34%Z ->
    getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 hint -> getr regs 11 = Z_to_bv 64 len ->
    getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = Z_to_bv 64 flags -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps RSEGS (mkst regs (0x682e8 : word) m rom)
                   (mkst regs' (0x683ac : word) (mm_frame (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 17 = Z_to_bv 64 222
      /\ getr regs' 10 = Z_to_bv 64 hint /\ getr regs' 11 = Z_to_bv 64 len /\ getr regs' 12 = Z_to_bv 64 prot
      /\ getr regs' 13 = Z_to_bv 64 flags /\ getr regs' 14 = Z_to_bv 64 (-1) /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 16 = Z_to_bv 64 hint
      /\ keeps_but clobMM1 regs regs'.
  Proof using Hlen SOK Hsp.
    intros regs rom Hf H2 H10 H11 H12 H13 H14 H15. subst flags.
    eexists. split.
    - stepn F_68294 D_68294. rewrite H2. addi_renorm.
      stepSTx F_68298 D_68298 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_6829c D_6829c (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682a0 D_682a0 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682a4 D_682a4 (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682a8 D_682a8 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682ac D_682ac (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682b0 D_682b0 (Z_to_bv 64 (sp - 56)) (getr regs 21) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepn F_682b4 D_682b4. rewrite H15. vals_lit.
      stepb_tk F_682b8 D_682b8 ltac:(cond_compute).
      stepn F_682c8 D_682c8.
      stepn F_682cc D_682cc.
      stepb_tk F_682d0 D_682d0 ltac:(rewrite H11, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_68308 D_68308. rewrite H13. vals_lit.
      stepb_ft F_6830c D_6830c ltac:(cond_compute).
      stepn F_68310 D_68310.
      stepn F_68314 D_68314.
      stepn F_68350 D_68350.
      stepn F_68354 D_68354. rewrite H10.
      unfold mm_frame. pu_refl.
    - repeat split; gres; try reflexivity; try assumption. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma mmW1_50 : forall regs rom,
    flags = 50%Z ->
    getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 hint -> getr regs 11 = Z_to_bv 64 len ->
    getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = Z_to_bv 64 flags -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps RSEGS (mkst regs (0x682e8 : word) m rom)
                   (mkst regs' (0x683ac : word) (mm_frame (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 17 = Z_to_bv 64 222
      /\ getr regs' 10 = Z_to_bv 64 hint /\ getr regs' 11 = Z_to_bv 64 len /\ getr regs' 12 = Z_to_bv 64 prot
      /\ getr regs' 13 = Z_to_bv 64 flags /\ getr regs' 14 = Z_to_bv 64 (-1) /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 16 = Z_to_bv 64 hint
      /\ keeps_but (clobMM1 ++ [1; 21]%bv) regs regs'.
  Proof using Hlen SOK Hsp.
    intros regs rom Hf H2 H10 H11 H12 H13 H14 H15. subst flags.
    eexists. split.
    - stepn F_68294 D_68294. rewrite H2. addi_renorm.
      stepSTx F_68298 D_68298 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_6829c D_6829c (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682a0 D_682a0 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682a4 D_682a4 (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682a8 D_682a8 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682ac D_682ac (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_682b0 D_682b0 (Z_to_bv 64 (sp - 56)) (getr regs 21) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 64%nat); [ | exact SOK | | ]; zsimp; lia).
      stepn F_682b4 D_682b4. rewrite H15. vals_lit.
      stepb_tk F_682b8 D_682b8 ltac:(cond_compute).
      stepn F_682c8 D_682c8.
      stepn F_682cc D_682cc.
      stepb_tk F_682d0 D_682d0 ltac:(rewrite H11, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_68308 D_68308. rewrite H13. vals_lit.
      stepb_tk F_6830c D_6830c ltac:(cond_compute).
      stepn F_68318 D_68318. rewrite H13.
      stepn F_6831c D_6831c. rewrite H15.
      stepn F_68320 D_68320. rewrite H10.
      stepn F_68324 D_68324. rewrite H14.
      stepn F_68328 D_68328. rewrite H12.
      stepn F_6832c D_6832c. rewrite H11.
      stepn F_68330 D_68330.
      stepret F_68290 D_68290 (Z_to_bv 64 0x68388) ltac:(reflexivity).
      stepn F_68334 D_68334.
      stepn F_68338 D_68338.
      stepn F_6833c D_6833c.
      stepn F_68340 D_68340.
      stepn F_68344 D_68344.
      stepn F_68348 D_68348.
      stepn F_6834c D_6834c.
      stepn F_68350 D_68350.
      stepn F_68354 D_68354.
      unfold mm_frame. pu_refl.
    - repeat split; gres; try reflexivity; try assumption. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma mmW2 : forall regs rom (m' : mem) (r : Z) ra s0v s1v s2v s3v s4v s5v,
    (0 <= r < 2^64 - 4095)%Z -> (hint <> 0 \/ r <> 2^64 - 1)%Z -> ret_ok ra ->
    getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 r -> getr regs 16 = Z_to_bv 64 hint ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
    exists regs',
      msteps RSEGS (mkst regs (0x683b0 : word) m' rom) (mkst regs' ra m' rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 r /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ keeps_but [1; 2; 8; 9; 11; 18; 19; 20; 21]%bv regs regs'.
  Proof using Hhint Hsp.
    intros regs rom m' r ra s0v s1v s2v s3v s4v s5v Hr Hnm1 Hra H2 H10 H16 M1 M2 M3 M4 M5 M6 M7.
    assert (NZ : Z.lor hint (2^64 - 1 - r) <> 0%Z).
    { intros E. apply Z.lor_eq_0_iff in E. destruct E as [E1 E2]. destruct Hnm1 as [X|X]; [exact (X E1)|]. apply X. lia. }
    eexists. split.
    - stepn F_6835c D_6835c. rewrite H10.
      replace (v_xori (Z_to_bv 64 r) (-1)) with (Z_to_bv 64 (2^64 - 1 - r)).
      2:{ unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 (-1)) with (2^64 - 1)%Z. rewrite lxor_ones64 by lia. reflexivity. }
      stepn F_68360 D_68360. rewrite H16.
      replace (v_or (Z_to_bv 64 hint) (Z_to_bv 64 (2 ^ 64 - 1 - r))) with (Z_to_bv 64 (Z.lor hint (2^64 - 1 - r))).
      2:{ unfold v_or. rewrite !u_Z2bv by lia. reflexivity. }
      assert (LO : (0 <= Z.lor hint (2 ^ 64 - 1 - r) < 2^64)%Z).
      { assert (LOR0 : (0 <= Z.lor hint (2 ^ 64 - 1 - r))%Z) by (apply Z.lor_nonneg; lia).
        split; [exact LOR0|].
        destruct (Z.eq_dec (Z.lor hint (2 ^ 64 - 1 - r)) 0) as [E|NE]; [rewrite E; lia|].
        apply (proj2 (Z.log2_lt_pow2 (Z.lor hint (2 ^ 64 - 1 - r)) 64 ltac:(lia))).
        rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
        - destruct (Z.eq_dec hint 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
        - destruct (Z.eq_dec (2^64-1-r) 0) as [E0|]; [rewrite E0; cbn; lia|]. apply Z.log2_lt_pow2; lia. }
      stepb_tk F_68364 D_68364 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact NZ).
      stepn F_68378 D_68378.
      stepn F_65f54 D_65f54.
      stepn F_65f58 D_65f58.
      stepb_tk F_65f5c D_65f5c ltac:(rewrite H10, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepret F_65f88 D_65f88 (Z_to_bv 64 0x683d0) ltac:(reflexivity).
      stepn F_6837c D_6837c.
      stepLD8 F_682e4 D_682e4 ra.
      stepLD8 F_682e8 D_682e8 s0v.
      stepLD8 F_682ec D_682ec s1v.
      stepLD8 F_682f0 D_682f0 s2v.
      stepLD8 F_682f4 D_682f4 s3v.
      stepLD8 F_682f8 D_682f8 s4v.
      stepLD8 F_682fc D_682fc s5v.
      stepn F_68300 D_68300. rewrite H2. addi_renorm.
      stepret F_68304 D_68304 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End MM.

Section MP.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp : Z) (addr prot : Z).
  Hypothesis Hsp : (2^20 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 16)) 16%nat = true.
  Hypothesis Haddr : (0 <= addr)%Z /\ (addr + 8192 < 2^64)%Z /\ (addr mod 4096 = 0)%Z.
  Hypothesis M_pg : rdn RSEGS m (Z_to_bv 64 A_PAGESIZE) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).

  Definition mp_frame (ra : word) : mem := wbytes m (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra).

  Lemma mpW1 : forall regs rom,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 4096 -> getr regs 12 = Z_to_bv 64 prot ->
    exists regs',
      msteps RSEGS (mkst regs (0x683d4 : word) m rom) (mkst regs' (0x68404 : word) (mp_frame (getr regs 1)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 16) /\ getr regs' 17 = Z_to_bv 64 226
      /\ getr regs' 10 = Z_to_bv 64 addr /\ getr regs' 11 = Z_to_bv 64 4096 /\ getr regs' 12 = Z_to_bv 64 prot
      /\ keeps_but [2; 11; 13; 14; 17]%bv regs regs'.
  Proof using M_pg Haddr SOK Hsp.
    intros regs rom H2 H10 H11 H12. unfold A_PAGESIZE in *.
    eexists. split.
    - stepn F_68380 D_68380. rewrite H2. addi_renorm.
      stepSTx F_68384 D_68384 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOK | | ]; zsimp; lia).
      stepn F_68388 D_68388.
      stepLD8 F_6838c D_6838c (Z_to_bv 64 4096).
      stepn F_68390 D_68390. rewrite H10, H11. rewrite v_add_ZZ by lia.
      stepn F_68394 D_68394.
      stepn F_68398 D_68398. rewrite v_add_ZZ by lia.
      stepn F_6839c D_6839c. rewrite H10. rewrite v_and_Z by lia.
      rewrite (Z.land_comm 18446744073709547520 addr), land_negpage, (proj2 (proj2 Haddr)), Z.sub_0_r by lia.
      stepn F_683a0 D_683a0. addi_renorm.
      stepn F_683a4 D_683a4. rewrite v_and_Z by lia. rewrite land_negpage by lia.
      match goal with |- context [Z_to_bv 64 (?e - ?e mod 4096)%Z] => replace (e - e mod 4096)%Z with (addr + 4096)%Z end.
      2:{ Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      stepn F_683a8 D_683a8. rewrite v_sub_ZZ by lia. replace (addr + 4096 - addr)%Z with 4096%Z by lia.
      stepn F_683ac D_683ac.
      unfold mp_frame. pu_refl.
    - repeat split; gres; try reflexivity; try assumption. solve_keeps_but.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma mpW2 : forall regs rom (m' : mem) ra,
    ret_ok ra -> getr regs 2 = Z_to_bv 64 (sp - 16) -> getr regs 10 = Z_to_bv 64 0 ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra) ->
    exists regs',
      msteps RSEGS (mkst regs (0x68408 : word) m' rom) (mkst regs' ra m' rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ keeps_but [1; 2; 10; 11]%bv regs regs'.
  Proof using Hsp addr.
    intros regs rom m' ra Hra H2 H10 M1.
    eexists. split.
    - stepn F_683b4 D_683b4.
      stepn F_65f54 D_65f54.
      stepn F_65f58 D_65f58.
      stepb_tk F_65f5c D_65f5c ltac:(rewrite H10; cond_compute).
      stepret F_65f88 D_65f88 (Z_to_bv 64 0x6840c) ltac:(reflexivity).
      stepn F_683b8 D_683b8. rewrite H10. vals_lit.
      stepLD8 F_683bc D_683bc ra.
      stepn F_683c0 D_683c0. rewrite H2. addi_renorm.
      stepret F_683c4 D_683c4 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End MP.
End UbMhMmapW.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac UbMhMmapW OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition errno12 : list (bv 8) := word_to_le_bytes 4 (Z_to_bv 64 12).

Section MMF.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp : Z) (hint : Z).
  Hypothesis Hsp : (80 <= sp)%Z /\ (sp < 2^64)%Z /\ ((A_ERRNO + 4 <= sp - 80)%Z \/ (sp <= A_ERRNO)%Z).
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 80)) 16%nat = true.
  Hypothesis SOKe : store_ok RSEGS m (Z_to_bv 64 A_ERRNO) 4%nat = true.
  Hypothesis Hhint : (0 <= hint < 2^64)%Z.

  (* [comment removed for export] *)
  Definition mm_ffail (s0v : word) : mem :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x683d0)))
      (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 A_ERRNO) errno12.

  (* [comment removed for export] *)
  Lemma mmW2f : forall regs rom ra s0v s1v s2v s3v s4v s5v,
    ret_ok ra ->
    getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 (2^64 - 12) -> getr regs 16 = Z_to_bv 64 hint ->
    getr regs 4 = Z_to_bv 64 TPV ->
    rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra) ->
    rdn RSEGS m (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
    rdn RSEGS m (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
    rdn RSEGS m (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
    rdn RSEGS m (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
    rdn RSEGS m (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
    rdn RSEGS m (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
    exists regs',
      msteps RSEGS (mkst regs (0x683b0 : word) m rom) (mkst regs' ra (mm_ffail (getr regs 8)) rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 (2^64 - 1) /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ keeps_but [1; 2; 8; 9; 10; 11; 18; 19; 20; 21]%bv regs regs'.
  Proof using Hhint SOKe SOK Hsp.
    intros regs rom ra s0v s1v s2v s3v s4v s5v Hra H2 H10 H16 H4 M1 M2 M3 M4 M5 M6 M7.
    unfold A_ERRNO, TPV in *. unfold mm_ffail, errno12, A_ERRNO, TPV.
    assert (NZ : Z.lor hint 11 <> 0%Z).
    { intros E. apply Z.lor_eq_0_iff in E. lia. }
    assert (LO : (0 <= Z.lor hint 11 < 2^64)%Z).
    { split; [apply Z.lor_nonneg; lia|].
      apply (proj2 (Z.log2_lt_pow2 (Z.lor hint 11) 64 ltac:(pose proof (Z.lor_nonneg hint 11); lia))).
      rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [|cbn; lia].
      destruct (Z.eq_dec hint 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    eexists. split.
    - stepn F_6835c D_6835c. rewrite H10.
      replace (v_xori (Z_to_bv 64 (2^64 - 12)) (-1)) with (Z_to_bv 64 11).
      2:{ unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 (-1)) with (2^64 - 1)%Z. rewrite lxor_ones64 by lia. reflexivity. }
      stepn F_68360 D_68360. rewrite H16.
      replace (v_or (Z_to_bv 64 hint) (Z_to_bv 64 11)) with (Z_to_bv 64 (Z.lor hint 11)).
      2:{ unfold v_or. rewrite !u_Z2bv by lia. reflexivity. }
      stepb_tk F_68364 D_68364 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact NZ).
      stepn F_68378 D_68378.
      (* [comment removed for export] *)
      stepn F_65f54 D_65f54.
      stepn F_65f58 D_65f58.
      stepb_ft F_65f5c D_65f5c ltac:(rewrite H10, c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepn F_65f60 D_65f60. rewrite H2. addi_renorm.
      stepSTx F_65f64 D_65f64 (Z_to_bv 64 (sp - 72)) (Z_to_bv 64 0x683d0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_65f68 D_65f68 (Z_to_bv 64 (sp - 80)) (getr regs 8) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOK | | ]; zsimp; lia).
      stepn F_65f6c D_65f6c. rewrite H10.
      replace (v_subw (Z_to_bv 64 0) (Z_to_bv 64 (2 ^ 64 - 12))) with (Z_to_bv 64 12) by (apply bv_eq; vm_compute; reflexivity).
      stepn F_65f70 D_65f70.
      stepn F_65ac4 D_65ac4. rewrite H4.
      stepn F_65ac8 D_65ac8. try addi_renorm.
      stepret F_65acc D_65acc (Z_to_bv 64 0x65fc8) ltac:(reflexivity).
      stepSTx F_65f74 D_65f74 (Z_to_bv 64 568044) (Z_to_bv 64 12) ltac:(store_ok_peel; exact SOKe).
      stepn F_65f78 D_65f78.
      stepLD8 F_65f7c D_65f7c (Z_to_bv 64 0x683d0).
      stepLD8 F_65f80 D_65f80 (getr regs 8).
      stepn F_65f84 D_65f84. addi_renorm.
      stepret F_65f88 D_65f88 (Z_to_bv 64 0x683d0) ltac:(reflexivity).
      stepn F_6837c D_6837c.
      stepLD8 F_682e4 D_682e4 ra.
      stepLD8 F_682e8 D_682e8 s0v.
      stepLD8 F_682ec D_682ec s1v.
      stepLD8 F_682f0 D_682f0 s2v.
      stepLD8 F_682f4 D_682f4 s3v.
      stepLD8 F_682f8 D_682f8 s4v.
      stepLD8 F_682fc D_682fc s5v.
      stepn F_68300 D_68300. addi_renorm.
      stepret F_68304 D_68304 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (apply bv_eq; reflexivity). all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End MMF.

Section MPF.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp : Z).
  Hypothesis Hsp : (32 <= sp)%Z /\ (sp < 2^64)%Z /\ ((A_ERRNO + 4 <= sp - 32)%Z \/ (sp <= A_ERRNO)%Z).
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 32)) 16%nat = true.
  Hypothesis SOKe : store_ok RSEGS m (Z_to_bv 64 A_ERRNO) 4%nat = true.

  Definition mp_ffail (s0v : word) : mem :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x6840c)))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 A_ERRNO) errno12.

  (* [comment removed for export] *)
  Lemma mpW2f : forall regs rom ra,
    ret_ok ra -> getr regs 2 = Z_to_bv 64 (sp - 16) -> getr regs 10 = Z_to_bv 64 (2^64 - 12) ->
    getr regs 4 = Z_to_bv 64 TPV ->
    rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra) ->
    exists regs',
      msteps RSEGS (mkst regs (0x68408 : word) m rom) (mkst regs' ra (mp_ffail (getr regs 8)) rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 (2^64 - 1) /\ getr regs' 1 = ra /\ getr regs' 8 = getr regs 8
      /\ keeps_but [1; 2; 8; 10; 11]%bv regs regs'.
  Proof using SOKe SOK Hsp.
    intros regs rom ra Hra H2 H10 H4 M1.
    unfold A_ERRNO, TPV in *. unfold mp_ffail, errno12, A_ERRNO, TPV.
    eexists. split.
    - stepn F_683b4 D_683b4.
      stepn F_65f54 D_65f54.
      stepn F_65f58 D_65f58.
      stepb_ft F_65f5c D_65f5c ltac:(rewrite H10, c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepn F_65f60 D_65f60. rewrite H2. addi_renorm.
      stepSTx F_65f64 D_65f64 (Z_to_bv 64 (sp - 24)) (Z_to_bv 64 0x6840c) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_65f68 D_65f68 (Z_to_bv 64 (sp - 32)) (getr regs 8) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOK | | ]; zsimp; lia).
      stepn F_65f6c D_65f6c. rewrite H10.
      replace (v_subw (Z_to_bv 64 0) (Z_to_bv 64 (2 ^ 64 - 12))) with (Z_to_bv 64 12) by (apply bv_eq; vm_compute; reflexivity).
      stepn F_65f70 D_65f70.
      stepn F_65ac4 D_65ac4. rewrite H4.
      stepn F_65ac8 D_65ac8. try addi_renorm.
      stepret F_65acc D_65acc (Z_to_bv 64 0x65fc8) ltac:(reflexivity).
      stepSTx F_65f74 D_65f74 (Z_to_bv 64 568044) (Z_to_bv 64 12) ltac:(store_ok_peel; exact SOKe).
      stepn F_65f78 D_65f78.
      stepLD8 F_65f7c D_65f7c (Z_to_bv 64 0x6840c).
      stepLD8 F_65f80 D_65f80 (getr regs 8).
      stepn F_65f84 D_65f84. addi_renorm.
      stepret F_65f88 D_65f88 (Z_to_bv 64 0x6840c) ltac:(reflexivity).
      stepn F_683b8 D_683b8. vals_lit.
      stepLD8 F_683bc D_683bc ra.
      stepn F_683c0 D_683c0. addi_renorm.
      stepret F_683c4 D_683c4 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (apply bv_eq; reflexivity). all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End MPF.
