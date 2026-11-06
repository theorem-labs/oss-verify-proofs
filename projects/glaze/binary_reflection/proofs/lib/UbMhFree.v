(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhFreeB.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Z0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma segZ : forall regs rom (m : mem),
    getr regs 10 = Z_to_bv 64 0 -> ret_ok (getr regs 1) ->
    msteps RSEGS (mkst regs (0x665b4 : word) m rom) (mkst regs (getr regs 1) m rom).
  Proof using.
    intros regs rom m H10 Hra.
    stepb_tk F_66560 D_66560 ltac:(rewrite H10; cond_compute).
    stepret F_66728 D_66728 (getr regs 1) ltac:(reflexivity).
    pu_refl.
  Qed.
End Z0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section N.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (idx freed mask all : Z).
  Hypothesis Hfr : (0 <= freed < 2^32)%Z.
  Hypothesis Hms : (0 <= mask + 2 ^ idx < 2^32)%Z.
  Hypothesis Hall : (0 <= all < 2^32)%Z.
  Hypothesis Hidx : (0 <= idx < 32)%Z.
  (* [comment removed for export] *)
  Hypothesis Hnt : freed = 0%Z \/ (mask + 2 ^ idx = all)%Z.

  Lemma segN : forall regs rom,
    getr regs 15 = s32 freed -> getr regs 16 = s32 mask -> getr regs 12 = s32 (2 ^ idx) ->
    getr regs 13 = s32 all -> getr regs 17 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 idx ->
    exists regs',
      msteps RSEGS (mkst regs (0x666d4 : word) m rom) (mkst regs' (0x66890 : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 idx /\ getr regs' 1 = Z_to_bv 64 0x66728
      /\ keeps_but [1; 11; 16]%bv regs regs'.
  Proof using Hnt Hidx Hfr.
    intros regs rom H15 H16 H12 H13 H17 H8.
    assert (Hpi : (0 < 2 ^ idx)%Z) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.eq_dec freed 0) as [F0|F0].
    - eexists. split.
      + stepb_tk F_66680 D_66680 ltac:(rewrite H15, F0; cond_compute).
        stepb_tk F_666b0 D_666b0 ltac:(rewrite H17; cond_compute).
        stepn F_666cc D_666cc. rewrite H8.
        stepn F_666d0 D_666d0.
        pu_refl.
      + repeat split; gres; try reflexivity. solve_keeps_but.
    - assert (HA : (mask + 2 ^ idx = all)%Z) by (destruct Hnt as [X|X]; [exfalso; exact (F0 X) | exact X]).
      eexists. split.
      + stepb_ft F_66680 D_66680 ltac:(rewrite H15, c_eq_s32_0, Z.mod_small by lia; apply Z.eqb_neq; exact F0).
        stepn F_66684 D_66684. rewrite H16, H12, v_addw_s32.
        stepb_tk F_66688 D_66688 ltac:(rewrite H13, c_eq_s32, HA; apply Z.eqb_refl).
        stepb_tk F_666b0 D_666b0 ltac:(rewrite H17; cond_compute).
        stepn F_666cc D_666cc. rewrite H8.
        stepn F_666d0 D_666d0.
        pu_refl.
      + repeat split; gres; try reflexivity. solve_keeps_but.
  Qed.
End N.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section U.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem).
  Hypothesis M_lock : rdn RSEGS m (Z_to_bv 64 MLOCK) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Lemma segU : forall regs rom,
    exists regs',
      msteps RSEGS (mkst regs (0x66728 : word) m rom) (mkst regs' (0x6673c : word) m rom)
      /\ getr regs' 8 = getr regs 10 /\ getr regs' 9 = getr regs 11
      /\ getr regs' 10 = Z_to_bv 64 MLOCK /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x6673c
      /\ keeps_but [1; 8; 9; 10; 11]%bv regs regs'.
  Proof using M_lock.
    intros regs rom. unfold MLOCK in *.
    eexists. split.
    - stepn F_666d4 D_666d4.
      stepn F_666d8 D_666d8.
      stepn F_666dc D_666dc.
      stepn F_666e0 D_666e0.
      stepn F_666e4 D_666e4.
      stepLD F_73d50 D_73d50 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      vals_lit.
      stepb_ft F_73d54 D_73d54 ltac:(cond_compute).
      stepret F_73d58 D_73d58 (Z_to_bv 64 0x6673c) ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity. solve_keeps_but.
  Qed.
End U.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ep.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp0 : Z) (ra s0v s1v s2v s3v : word).
  Hypothesis Hsp : (CEIL + 48 <= sp0)%Z /\ (sp0 < 2^64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp0 - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp0 - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp0 - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp0 - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp0 - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).

  Definition clobEp : list reg := [1; 2; 8; 9; 18; 19]%bv.

  Lemma segEp : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp0 - 48) ->
    exists regs',
      msteps RSEGS (mkst regs (0x66764 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ keeps_but clobEp regs regs'.
  Proof using M_s3 M_s2 M_s1 M_s0 M_ra Hra Hsp RN.
    intros regs rom H2. ceil.
    eexists. split.
    - stepLD8 F_66710 D_66710 ra.
      stepLD8 F_66714 D_66714 s0v.
      stepLD8 F_66718 D_66718 s1v.
      stepLD8 F_6671c D_6671c s2v.
      stepLD8 F_66720 D_66720 s3v.
      stepn F_66724 D_66724. rewrite H2. addi_renorm.
      stepret F_66728 D_66728 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption.
      all: try (f_equal; lia).
      all: try solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma segE0 : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp0 - 48) -> getr regs 9 = Z_to_bv 64 0 ->
    exists regs',
      msteps RSEGS (mkst regs (0x6673c : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ keeps_but clobEp regs regs'.
  Proof using M_s3 M_s2 M_s1 M_s0 M_ra Hra Hsp RN.
    intros regs rom H2 H9.
    destruct (segEp regs rom H2) as (r' & RUN & P).
    exists r'. split; [|exact P].
    stepb_tk F_666e8 D_666e8 ltac:(rewrite H9; cond_compute).
    exact RUN.
  Qed.
End Ep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section M1.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp0 b len e : Z).
  Hypothesis Hsp : (CEIL + 80 <= sp0)%Z /\ (sp0 < 2^64)%Z.
  Hypothesis Hb : (0 <= b < 2^64)%Z.
  Hypothesis Hlen : (0 < len < 2^64)%Z.
  Hypothesis He : (0 <= e < 2^32)%Z.
  Hypothesis M_err : rdn RSEGS m (Z_to_bv 64 A_ERRNO) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 e)).
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp0 - 80)) 32%nat = true.

  (* [comment removed for export] *)
  Definition m_m1 : mem :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x66758)))
      (Z_to_bv 64 (sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 b)))
      (Z_to_bv 64 (sp0 - 72)) (word_to_le_bytes 8 (Z_to_bv 64 len)).

  Definition clobM1 : list reg := [1; 2; 8; 9; 10; 11; 17; 18; 19]%bv.

  Lemma segM1 : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp0 - 48) -> getr regs 4 = Z_to_bv 64 TPV ->
    getr regs 8 = Z_to_bv 64 b -> getr regs 9 = Z_to_bv 64 len ->
    exists regs',
      msteps RSEGS (mkst regs (0x6673c : word) m rom) (mkst regs' (0x68518 : word) m_m1 rom)
      /\ getr regs' 17 = Z_to_bv 64 215 /\ getr regs' 10 = Z_to_bv 64 b /\ getr regs' 11 = Z_to_bv 64 len
      /\ getr regs' 8 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 b
      /\ getr regs' 18 = Z_to_bv 64 A_ERRNO /\ getr regs' 19 = s32 e
      /\ getr regs' 2 = Z_to_bv 64 (sp0 - 80) /\ getr regs' 1 = Z_to_bv 64 0x6850c
      /\ keeps_but clobM1 regs regs'.
  Proof using SOK M_err He Hlen Hsp RN.
    intros regs rom H2 H4 H8 H9. change A_ERRNO with 568044%Z in *. ceil; unfold TPV in *. unfold m_m1.
    eexists. split.
    - stepb_ft F_666e8 D_666e8 ltac:(rewrite H9, c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_666ec D_666ec.
      stepn F_65ac4 D_65ac4. rewrite H4.
      stepn F_65ac8 D_65ac8.
      stepret F_65acc D_65acc (Z_to_bv 64 0x66744) ltac:(reflexivity).
      stepn F_666f0 D_666f0.
      stepLD F_666f4 D_666f4 (word_to_le_bytes 4 (Z_to_bv 64 e)) (Z_to_bv 64 e)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_666f8 D_666f8. rewrite H8.
      stepn F_666fc D_666fc. rewrite H9.
      stepn F_66700 D_66700.
      stepn F_6849c D_6849c. rewrite H2. addi_renorm.
      stepSTx F_684a0 D_684a0 (Z_to_bv 64 (sp0 - 56)) (Z_to_bv 64 0x66758)
        ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 32%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_684a4 D_684a4 (Z_to_bv 64 (sp0 - 64)) (Z_to_bv 64 b)
        ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 32%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_684a8 D_684a8 (Z_to_bv 64 (sp0 - 72)) (Z_to_bv 64 len)
        ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 32%nat); [ | exact SOK | | ]; zsimp; lia).
      stepn F_684ac D_684ac.
      stepn F_684b0 D_684b0.
      stepn F_684b4 D_684b4.
      stepret F_68290 D_68290 (Z_to_bv 64 0x6850c) ltac:(reflexivity).
      stepn F_684b8 D_684b8.
      stepn F_684bc D_684bc.
      stepn F_684c0 D_684c0.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption.
      all: try (f_equal; lia).
      all: try solve_keeps_but.
  Qed.
End M1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section M2.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp0 e : Z) (ra s0v s1v s2v s3v v1 v2 : word).
  Hypothesis Hsp : (CEIL + 80 <= sp0)%Z /\ (sp0 < 2^64)%Z.
  Hypothesis He : (0 <= e < 2^32)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis SOKe : store_ok RSEGS m (Z_to_bv 64 A_ERRNO) 4%nat = true.
  Hypothesis M_r2 : rdn RSEGS m (Z_to_bv 64 (sp0 - 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66758)).
  Hypothesis M_v1 : rdn RSEGS m (Z_to_bv 64 (sp0 - 64)) 8%nat = Some (word_to_le_bytes 8 v1).
  Hypothesis M_v2 : rdn RSEGS m (Z_to_bv 64 (sp0 - 72)) 8%nat = Some (word_to_le_bytes 8 v2).
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp0 - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp0 - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp0 - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp0 - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp0 - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).

  (* [comment removed for export] *)
  Definition m_m2 : mem := wbytes m (Z_to_bv 64 A_ERRNO) (word_to_le_bytes 4 (s32 e)).

  Lemma w4_errno : word_to_le_bytes 4 (s32 e) = word_to_le_bytes 4 (Z_to_bv 64 e).
  Proof using He. rewrite w2le4_s32. rewrite Z.mod_small by lia. reflexivity. Qed.

  Definition clobM2 : list reg := [1; 2; 8; 9; 10; 11; 18; 19]%bv.

  Lemma segM2 : forall regs rom,
    getr regs 10 = Z_to_bv 64 0 -> getr regs 2 = Z_to_bv 64 (sp0 - 80) ->
    getr regs 18 = Z_to_bv 64 A_ERRNO -> getr regs 19 = s32 e ->
    exists regs',
      msteps RSEGS (mkst regs (0x6851c : word) m rom) (mkst regs' ra m_m2 rom)
      /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ keeps_but clobM2 regs regs'.
  Proof using M_s3 M_s2 M_s1 M_s0 M_ra M_v2 M_v1 M_r2 SOKe Hra Hsp v2 v1 RN.
    intros regs rom H10 H2 H18 H19. change A_ERRNO with 568044%Z in *. ceil. unfold m_m2.
    eexists. split.
    - stepn F_684c8 D_684c8.
      stepn F_65f54 D_65f54.
      stepn F_65f58 D_65f58.
      stepb_tk F_65f5c D_65f5c ltac:(rewrite H10; cond_compute).
      stepret F_65f88 D_65f88 (Z_to_bv 64 0x68520) ltac:(reflexivity).
      stepn F_684cc D_684cc. rewrite H10. vals_lit.
      stepLD8 F_684d0 D_684d0 (Z_to_bv 64 0x66758).
      stepLD8 F_684d4 D_684d4 v1.
      stepLD8 F_684d8 D_684d8 v2.
      stepn F_684dc D_684dc. rewrite H2. addi_renorm.
      stepret F_684e0 D_684e0 (Z_to_bv 64 0x66758) ltac:(reflexivity).
      stepSTx F_66704 D_66704 (Z_to_bv 64 568044) (s32 e) ltac:(exact SOKe).
      stepn F_66708 D_66708.
      stepLD8 F_66710 D_66710 ra.
      stepLD8 F_66714 D_66714 s0v.
      stepLD8 F_66718 D_66718 s1v.
      stepLD8 F_6671c D_6671c s2v.
      stepLD8 F_66720 D_66720 s3v.
      stepn F_66724 D_66724. addi_renorm.
      stepret F_66728 D_66728 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption.
      all: try (f_equal; lia).
      all: try solve_keeps_but.
  Qed.
End M2.
End UbMhFreeB.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhJunk OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhScrib OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhFreePro OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhJunk OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA UbMhFreeB OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhScrib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf.UbMhSub OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac tr_clear_heavy := repeat match goal with
  | H : context [Z.max _ _] |- _ => clear H | H : context [Z.min _ _] |- _ => clear H
  | H : context [Z.div _ _] |- _ => clear H | H : context [Z.modulo _ _] |- _ => clear H end.
#[local] Ltac lia_fast ::= first [ solve [ clear_disj; tr_clear_heavy; lia ] | solve [ clear_disj; lia ] | lia ].
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac lia_pairs ::= fail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; tr_clear_heavy; lia ] | solve [ clear_disj; lia ] | lia ] ].
Section Helpers.
  Context {RN : mh_run}.
  Context {fx : FPState}.



  (* [comment removed for export] *)
  Lemma freed_not63 : forall st L m i, WF st L -> is_group st m -> 0 <= i <= g_lastidx st m ->
    s_slot st m i <> SFreed -> mr_freed (s_meta st m) <> 0 -> g_sc st m <> 63.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros st L m i HWF Hgrp Hi Hs Hfr E. pose proof (wG_each st L (WF_groups st L HWF) m Hgrp) as WG.
    destruct (wg_sc st L m WG) as [H48|(_ & L0 & _)]; [lia|].
    pose proof (wg_frr st L m WG) as FR.
    pose proof (Z.bit_log2 (mr_freed (s_meta st m)) ltac:(lia)) as B. pose proof (Z.log2_nonneg (mr_freed (s_meta st m))) as LN.
    apply (proj1 (wg_fr st L m WG _ LN)) in B. destruct B as [B1 B2].
    assert (i = Z.log2 (mr_freed (s_meta st m))) by lia. subst i. exact (Hs B2).
  Qed.


  Lemma free_mem1_saved : forall (M : mem) sp ra s0 s1 s2 s3, 48 <= sp < 2 ^ 64 ->
    rdn RSEGS (free_mem1 M sp ra s0 s1 s2 s3) (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn RSEGS (free_mem1 M sp ra s0 s1 s2 s3) (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0) /\
    rdn RSEGS (free_mem1 M sp ra s0 s1 s2 s3) (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1) /\
    rdn RSEGS (free_mem1 M sp ra s0 s1 s2 s3) (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2) /\
    rdn RSEGS (free_mem1 M sp ra s0 s1 s2 s3) (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros M sp ra s0 s1 s2 s3 Hsp. unfold free_mem1.
    repeat split; repeat rdn_peel1; apply rdn_wbytes_hit8; zsimp; lia.
  Qed.

  Lemma free_mem1_writes : forall (M : mem) sp ra s0 s1 s2 s3 a, 48 <= sp < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
    free_mem1 M sp ra s0 s1 s2 s3 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sp - 48 <= a < sp.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros M sp ra s0 s1 s2 s3 a Hsp Ha NE. unfold free_mem1 in NE. wdiff NE M a. Qed.

  Lemma free_mem1_grows : forall (M : mem) sp ra s0 s1 s2 s3, mem_grows M (free_mem1 M sp ra s0 s1 s2 s3).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros. unfold free_mem1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
End Helpers.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FSTK : Z := 912.

Section Free.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Definition free_post (st : mst) (L' : list (Z * Z)) (sp : Z) (regs : bvmap 5 word) (M : mem) (mdl : Model)
             (rom : word -> option byte) (c' : config) : Prop :=
    exists regs' M' mdl',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      (getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
       getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\
       getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\
       getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27) /\
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
          (sp - FSTK <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L' a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4)) /\
      defined M' (sp - FSTK) sp /\
      (exists st', WF st' L' /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\ nojunk st' /\ nolimbo st' /\ fsub st st') /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\
      vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl).

  (* [comment removed for export] *)
  Theorem free_null_kat : forall regs (M : mem) mdl rom (Q : config -> Prop),
    m_halted mdl = None -> m_vm_lazy mdl = [] ->
    getr regs 10 = Z_to_bv 64 0 -> ret_ok (getr regs 1) ->
    Q (mkCfg (mkst regs (getr regs 1) M rom) mdl) ->
    kat RSEGS (mkCfg (mkst regs (0x665b4%bv : word) M rom) mdl) Q.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros regs M mdl rom Q Hh Hl H10 Hra HQ.
    eapply kat_msteps; [exact Hh | exact Hl | exact (segZ regs rom M H10 Hra) |]. apply kat_refl. exact HQ.
  Qed.

  (* [comment removed for export] *)
  Theorem free_kat : forall st regs (M : mem) mdl rom L L' (p n sp : Z) (Q : config -> Prop),
    WF st L -> REP st M -> LEDGER st (m_vmmaps mdl) -> nojunk st -> nolimbo st ->
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
    In (p, n) L -> (forall x, In x L' <-> In x L /\ x <> (p, n)) -> NoDup L' -> (length L' <= length L)%nat ->
    getr regs 10 = Z_to_bv 64 p -> ret_ok (getr regs 1) ->
    getr regs 2 = Z_to_bv 64 sp -> sp mod 16 = 0 -> CEIL + FSTK <= sp -> sp < 2 ^ 64 ->
    getr regs 4 = Z_to_bv 64 TPV ->
    defined M (sp - FSTK) sp ->
    (forall c', free_post st L' sp regs M mdl rom c' -> Q c') ->
    kat RSEGS (mkCfg (mkst regs (0x665b4%bv : word) M rom) mdl) Q.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros st regs M mdl rom L L' p n sp Q HWF HREP HLG NJ NL Hh Hlz Hmat Hin HL'in HL'nd HL'len H10 Hra H2 Hsp16 Hsplo Hsphi H4 DEF HQ.
    unfold FSTK in *.
    destruct (wL_in st L (WF_live st L HWF) p n Hin) as (m & i & off & res & Hgrp & Hi & Hslot).
    pose proof (wG_each st L (WF_groups st L HWF) m Hgrp) as WG.
    destruct (group_range st L HWF m Hgrp) as [GR1 GR2].
    destruct (metaU_rng st L HWF m (group_metaU st L HWF m Hgrp)) as (MR1 & MR2 & MR8).
    destruct (U_pure st L HWF p n m i off res Hgrp Hi Hslot) as (Hoff & Hn & Hp & Hres & Hresr & PO & HinL).
    destruct (U_stride st L HWF m Hgrp) as [S16 Smod].
    destruct (U_masks st L HWF p n m i off res Hgrp Hi Hslot) as (AVr & FRr & AVb & FRb).
    pose proof (glast_rng st m) as GL. pose proof (wg_Wr st L m WG) as WR.
    pose proof PO as PO'. destruct PO' as (Pal & Pge & Pmod & Pq & Psc & Pml).
    (* [comment removed for export] *)
    assert (GCp : forall a, p - 4 <= a < p -> gcell st m a).
    { intros a Ha. unfold gcell. right; right; left. exists i, p. unfold slot_ptr. rewrite Hslot. repeat split; lia. }
    assert (PR : HEAPLO + 16 <= p /\ p <= g_slot_end st m i /\ g_slot_end st m i < gspan st m).
    { assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
      assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia).
      unfold gspan, g_span_end, g_slot_end, g_slot_start, UNIT, IB in *. (first [ (clear MR8 Hsp16; lia) | lia ]). }
    destruct PR as (PR1 & PR2 & PR3).
    assert (P16 : p + 16 <= CEIL).
    { ceil. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). (first [ (clear Smod MR8 Hsp16; lia) | lia ]). }
    assert (PI : p + 16 <= IMG_LO \/ IMG_HI <= p).
    { pose proof (group_img st L HWF m Hgrp) as [GI _].
      assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; (first [ (clear GI Pmod Pal MR8 Hsp16; lia) | lia ])).
      assert (GM : g_mem st m + 16 <= p) by (unfold g_slot_start, UNIT, IB in Hp; (first [ (clear Smod MR8 Hsp16; lia) | lia ])).
      destruct GI as [GI|GI]; [left | right; (first [ (clear Smod MR8 Hsp16; lia) | lia ])]. (first [ (clear Smod MR8 Hsp16; lia) | lia ]). }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (Hpg : p <= m \/ m + 40 <= p - 4).
    { destruct (Z.le_gt_cases p m) as [A|A]; [left; exact A | right].
      destruct (Z.le_gt_cases (m + 40) (p - 4)) as [B|B]; [exact B | exfalso].
      destruct (Z.le_gt_cases (p - 4) m) as [C|C].
      - apply (gcell_not_meta st L HWF m m m Hgrp (GCp m ltac:(lia)) (group_metaU st L HWF m Hgrp)). lia.
      - apply (gcell_not_meta st L HWF m m (p - 4) Hgrp (GCp (p - 4) ltac:(lia)) (group_metaU st L HWF m Hgrp)). lia. }
    (* [comment removed for export] *)
    destruct (G_meta_cells st L M HWF HREP m Hgrp) as (ar & k & Har & Hark & Em & Ear & _ & _ & _ & RM & CK & DFar).
    destruct RM as [Rp Rn Rme Rav Rfr RW].
    pose proof (rp_statics st M HREP) as [Snl Spg Slock Scan Sgot Serr Sctz Ssc].
    assert (Mnl : rdn RSEGS M (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0]) by exact (cell1_rdn M A_NEED_LOCKS 0 ltac:(lia) Snl).
    pose proof (meta_store_ok st L M HWF HREP m (group_metaU st L HWF m Hgrp)) as SOKg0.
    (* [comment removed for export] *)
    assert (SOK48 : store_ok RSEGS M (Z_to_bv 64 (sp - 48)) 48%nat = true).
    { eapply store_ok_defined; [exact DEF | (first [ (clear Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]) | cbn; (first [ (clear Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]) | ceil; (first [ (clear H0 Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]) | exact Hsphi]. }
    pose proof (U_free_pre st L M HWF HREP p n m i off res Hgrp Hi Hslot sp ltac:(ceil; lia) SOK48) as PRE.
    destruct (ref_free_pro regs M rom sp p _ _ m i off n _ res _ _ _ _ _ PRE H2 H10)
      as (r1 & RUN1 & A2 & A9 & A8 & A10 & A11 & A14 & A15 & A18 & A19 & A3 & A4 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    set (M1 := free_mem1 M sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) in RUN1.
    assert (G1 : mem_grows M M1) by (unfold M1; apply free_mem1_grows).
    assert (W1 : forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sp - 48 <= a < sp).
    { intros a Hr NE. unfold M1 in NE. exact (free_mem1_writes M sp _ _ _ _ _ a ltac:(ceil; (first [ (clear H0 Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])) Hr NE). }
    destruct (free_mem1_saved M sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(ceil; (first [ (clear H0 Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])))
      as (Mra & Ms0 & Ms1 & Ms2 & Ms3). fold M1 in Mra, Ms0, Ms1, Ms2, Ms3.
    assert (LOW1 : forall a kk, 0 <= a -> a + Z.of_nat kk <= sp - 48 -> rdn RSEGS M1 (Z_to_bv 64 a) kk = rdn RSEGS M (Z_to_bv 64 a) kk).
    { intros a kk Ha Hk. unfold M1. apply free_mem1_rdn; ceil; (first [ (clear H0 Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]). }
    assert (Mav1 : rdn RSEGS M1 (Z_to_bv 64 (m + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (mr_avail (s_meta st m)))))
      by (rewrite LOW1 by (cbn; ceil; unfold HEAPLO in *; lia); exact Rav).
    assert (Mfr1 : rdn RSEGS M1 (Z_to_bv 64 (m + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (mr_freed (s_meta st m)))))
      by (rewrite LOW1 by (cbn; ceil; unfold HEAPLO in *; lia); exact Rfr).
    assert (Mnl1 : rdn RSEGS M1 (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0])
      by (rewrite LOW1 by (cbn; ceil; unfold A_NEED_LOCKS in *; lia); exact Mnl).
    assert (SOKg : store_ok RSEGS M1 (Z_to_bv 64 m) 40%nat = true) by (eapply store_ok_mono; [exact G1 | exact SOKg0]).
    assert (SOKp : store_ok RSEGS M1 (Z_to_bv 64 (p - 4)) 4%nat = true).
    { eapply store_ok_mono; [exact G1|]. pose proof (group_bytes_defined st L M 8 m HWF HREP (wg_depth st L m WG) Hgrp) as DFg.
      pose proof (gcell_in_span st L HWF m (p - 4) Hgrp (GCp (p - 4) ltac:(lia))).
      pose proof (gcell_in_span st L HWF m (p - 1) Hgrp (GCp (p - 1) ltac:(lia))).
      eapply store_ok_defined; [exact DFg | (first [ (clear Ear Smod MR8 Hsp16; lia) | lia ]) | cbn; (first [ (clear Ear Smod MR8 Hsp16; lia) | lia ]) | unfold HEAPLO in *; (first [ (clear Ear Hpg PI Pal Smod MR8 Hsp16; lia) | lia ]) | ceil; (first [ (clear H3 Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])]. }
    (* [comment removed for export] *)
    destruct (junk_close st L L' M p n m i off res HWF HREP Hgrp Hi Hslot HL'in HL'nd HL'len) as [WF1 REP1].
    set (st1 := UbMhJunk.st' st m i off) in WF1, REP1.
    assert (Hslot1 : s_slot st1 m i = SJunk off) by (unfold st1; apply UbMhJunk.e_slot_mi).
    assert (Hgrp1 : is_group st1 m) by exact Hgrp.
    assert (OJ1 : only_junk st1 m i).
    { intros x kk o Hx Hk E. unfold st1 in E. rewrite UbMhJunk.e_slot in E.
      destruct (Z.eqb_spec x m); destruct (Z.eqb_spec kk i); cbn [andb] in E;
        [split; assumption | exfalso; exact (NJ x kk o Hx Hk E) | exfalso; exact (NJ x kk o Hx Hk E) | exfalso; exact (NJ x kk o Hx Hk E)]. }
    assert (REP11 : REP st1 M1).
    { apply (REP_frame st1 L' M WF1 REP1 M1 G1). intros a Hr NE. left. pose proof (W1 a Hr NE). ceil. (first [ (clear Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). }
    assert (Ejq : g_slot_start st1 m i + 16 * off = p) by (symmetry; exact Hp).
    (* [comment removed for export] *)
    assert (HDRown : forall a, p - 4 <= a < p -> HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L' a).
    { intros a Ha. pose proof (gcell_in_span st L HWF m a Hgrp (GCp a Ha)). split; [(first [ (clear Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])|]. split; [pose proof (group_img st L HWF m Hgrp); (first [ (clear H0 Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])|].
      intros (q & nq & Hq & Hqa). apply HL'in in Hq. destruct Hq as [Hq _].
      destruct (wL_in st L (WF_live st L HWF) q nq Hq) as (y & kk & o2 & r2 & Hy & Hkk & Sy).
      apply (ge_app_cell st (WF_geom st L HWF) m a Hgrp (GCp a Ha)). exists y, kk, q, nq, o2, r2. repeat split; try assumption; lia. }
    assert (METAown : forall a, m <= a < m + 40 -> HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L' a).
    { intros a Ha. split; [(first [ (clear Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])|]. split; [pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)); (first [ (clear H Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])|]. intros (q & nq & Hq & Hqa). apply HL'in in Hq. destruct Hq as [Hq _].
      destruct (wL_in st L (WF_live st L HWF) q nq Hq) as (y & kk & o2 & r2 & Hy & Hkk & Sy).
      destruct (metaU_area st L HWF m (group_metaU st L HWF m Hgrp)) as (ar0 & k0 & Har0 & _ & _ & _ & _ & _ & Q1 & Q2 & _).
      apply (ge_app_area st (WF_geom st L HWF) a); [exists y, kk, q, nq, o2, r2; repeat split; try assumption; (first [ (clear Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]) | exists ar0; split; [exact Har0 | (first [ (clear Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])]]. }
    (* [comment removed for export] *)
    destruct (segC M1 p m i (g_W st m) (mr_avail (s_meta st m)) (mr_freed (s_meta st m))
                ltac:(split; [lia | split; [exact P16 | exact PI]]) ltac:(ceil; unfold HEAPLO in *; lia) Hpg Hi WR AVr FRr AVb FRb SOKp Mav1 Mfr1 Mnl1 r1 rom A10 A11 A8 A9)
      as (r2 & RUN2 & C12 & C13 & C11 & C15 & C16 & C17 & C10 & C8 & C9 & K2).
    set (M2 := m2 M1 p) in RUN2.
    assert (G2 : mem_grows M1 M2) by (unfold M2, m2; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (W2 : forall a, 0 <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) <> M1 (Z_to_bv 64 a) -> p - 3 <= a < p).
    { intros a Hr NE. unfold M2, m2 in NE. ceil; unfold HEAPLO in *. wdiff NE M1 a. }
    (* [comment removed for export] *)
    assert (FIN : forall stF (MF : mem) mdlF rF,
      WF stF L' -> REP stF MF -> LEDGER stF (m_vmmaps mdlF) -> nojunk stF -> s_limbo stF = s_limbo st -> fsub st stF ->
      m_halted mdlF = None -> m_vm_lazy mdlF = [] -> m_vm_materialized mdlF = [] -> m_fs mdlF = m_fs mdl -> m_fds mdlF = m_fds mdl ->
      vm_limit (m_vmmaps mdlF) = vm_limit (m_vmmaps mdl) ->
      defined MF (sp - 912) sp ->
      (forall a, 0 <= a < 2 ^ 64 -> MF (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
          (sp - 912 <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L' a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4)) ->
      getr rF 2 = Z_to_bv 64 sp -> getr rF 3 = getr regs 3 -> getr rF 4 = getr regs 4 ->
      getr rF 8 = getr regs 8 -> getr rF 9 = getr regs 9 -> getr rF 18 = getr regs 18 -> getr rF 19 = getr regs 19 ->
      getr rF 20 = getr regs 20 -> getr rF 21 = getr regs 21 -> getr rF 22 = getr regs 22 -> getr rF 23 = getr regs 23 ->
      getr rF 24 = getr regs 24 -> getr rF 25 = getr regs 25 -> getr rF 26 = getr regs 26 -> getr rF 27 = getr regs 27 ->
      Q (mkCfg (mkst rF (getr regs 1) MF rom) mdlF)).
    { intros stF MF mdlF rF W' R' LG' NJ' LB' FS' X1 X2 X3 X4 X5 X6 GR FRM E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27.
      apply HQ. exists rF, MF, mdlF. split; [reflexivity|]. split.
      { rewrite E2, H2. repeat split; try assumption; reflexivity. }
      split; [exact FRM|]. split; [exact GR|].
      split; [exists stF; split; [exact W'|]; split; [exact R'|]; split; [exact LG'|]; split; [exact NJ'|]; split; [unfold nolimbo; rewrite LB'; exact NL | exact FS']|].
      repeat (split; [assumption|]). exact X6. }
    (* [comment removed for export] *)
    assert (NONTRIV : mr_freed (s_meta st m) = 0 \/ Z.lor (mr_avail (s_meta st m)) (mr_freed (s_meta st m)) + 2 ^ i = 2 * 2 ^ g_lastidx st m - 1 ->
                      kat RSEGS (mkCfg (mkst r2 (0x666d4%bv : word) M2 rom) mdl) Q).
    2:{ (* [comment removed for export] *)
      destruct (Z.eq_dec (mr_freed (s_meta st m)) 0) as [F0|F0].
      { eapply kat_msteps; [exact Hh | exact Hlz | exact RUN1 |]. eapply kat_msteps; [exact Hh | exact Hlz | exact RUN2 |]. apply NONTRIV. left. exact F0. }
      destruct (Z.eq_dec (Z.lor (mr_avail (s_meta st m)) (mr_freed (s_meta st m)) + 2 ^ i) (2 * 2 ^ g_lastidx st m - 1)) as [EA|NA].
      { eapply kat_msteps; [exact Hh | exact Hlz | exact RUN1 |]. eapply kat_msteps; [exact Hh | exact Hlz | exact RUN2 |]. apply NONTRIV. right. exact EA. }
      (* [comment removed for export] *)
      destruct (segT M1 sp p m i (g_W st m) (mr_avail (s_meta st m)) (mr_freed (s_meta st m)) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                 ltac:(split; [(first [ (clear NONTRIV Ear Smod MR8 Hsp16; lia) | lia ]) | split; [exact P16 | exact PI]]) ltac:(ceil; unfold HEAPLO in *; (first [ (clear NONTRIV Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])) Hpg ltac:(ceil; (first [ (clear NONTRIV Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])) Hi WR AVr FRr AVb FRb Hra
                 SOKp SOKg Mav1 Mfr1 Mnl1 Mra Ms0 Ms1 Ms2 Ms3 F0 NA r1 rom A10 A11 A8 A9 A2)
        as (r3 & RUN3 & T2 & T1 & T8 & T9 & T18 & T19 & K3).
      set (M3 := m3 M1 p m i (mr_freed (s_meta st m))) in RUN3.
      assert (G13 : mem_grows M1 M3) by (unfold M3, m3, m2; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (W3 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) <> M1 (Z_to_bv 64 a) -> (p - 3 <= a < p) \/ (m + 28 <= a < m + 32)).
      { intros a Hr NE. unfold M3, m3, m2 in NE. ceil; unfold HEAPLO in *. wdiff NE M1 a. }
      set (spb := Z.max sp (CEIL + MSTK)).
      destruct (setbit_close st1 L' M1 M3 m i off spb WF1 REP11 Hgrp1 Hi Hslot1 ltac:(unfold spb; (first [ (clear W3 NONTRIV Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]))) as [WF3 REP3].
      { intros a Hr NE. unfold sb_wr. rewrite Ejq. right. exact (W3 a Hr NE). }
      { exact G13. }
      { unfold cell, M3, m3. change (mr_freed (s_meta st1 m)) with (mr_freed (s_meta st m)).
        rewrite (w4_freed_self i (g_W st m) 0 (mr_freed (s_meta st m)) Hi FRr FRb F0).
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 (mr_freed (s_meta st m) + 2 ^ i))) (m2 M1 p) (Z_to_bv 64 (m + 28))) as RH.
        rewrite length_N_to_le_bytes in RH. apply RH. rewrite u_Z2bv by (ceil; unfold HEAPLO in *; (first [ (clear H0 W3 NONTRIV FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])). ceil; (first [ (clear H0 W3 NONTRIV FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). }
      { apply (freed_not63 st1 L' m i WF1 Hgrp1 Hi); [rewrite Hslot1; discriminate | exact F0]. }
      { left. exact NA. }
      { (* [comment removed for export] *)
        intros S48. destruct (Z.le_gt_cases (UNIT * size_class (g_sc st1 m)) (g_stride st1 m)) as [OK|LT]; [exact OK|]. exfalso.
        pose proof (wG_each st1 L' (WF_groups st1 L' WF1) m Hgrp1) as WG1.
        apply F0. apply Z.bits_inj_0. intros j. destruct (Z.lt_ge_cases j 0) as [Hj|Hj]; [apply Z.testbit_neg_r; exact Hj|].
        destruct (Z.testbit (mr_freed (s_meta st m)) j) eqn:T; [|reflexivity]. exfalso.
        destruct (proj1 (wg_fr st1 L' m WG1 j Hj) T) as [Hjl SF].
        exact (proj2 (wg_fit st1 L' m WG1 S48 LT j (conj Hj Hjl)) SF). }
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN1 |]. eapply kat_msteps; [exact Hh | exact Hlz | exact RUN3 |]. apply kat_refl.
      assert (LG3 : LEDGER (UbMhSetBit.st' st1 m i) (m_vmmaps mdl)) by (apply (LEDGER_same st); [reflexivity | reflexivity | exact HLG]).
      assert (NJ3 : nojunk (UbMhSetBit.st' st1 m i)).
      { intros x kk o Hx Hk E. rewrite UbMhSetBit.e_slot in E. rewrite UbMhSetBit.e_glast in Hk. change (is_group st1 x) in Hx.
        destruct (Z.eqb_spec x m); destruct (Z.eqb_spec kk i); cbn [andb] in E; try discriminate E; destruct (OJ1 x kk o Hx Hk E); congruence. }
      assert (GR3 : mem_grows M M3) by (eapply mem_grows_trans; [exact G1 | exact G13]).
      assert (FRM3 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
          (sp - 912 <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L' a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4)).
      { intros a Hr NE. destruct (decide (M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E|NE3].
        + left. pose proof (W1 a Hr ltac:(congruence)). lia.
        + right; left. destruct (W3 a Hr NE3) as [A|A]; [apply HDRown; lia | apply METAown; lia]. }
      assert (Q3 : getr r3 3 = getr regs 3) by (kept_rw K3; exact A3).
      assert (Q4 : getr r3 4 = getr regs 4) by (kept_rw K3; exact A4).
      assert (Q20 : getr r3 20 = getr regs 20) by (kept_rw K3; exact A20).
      assert (Q21 : getr r3 21 = getr regs 21) by (kept_rw K3; exact A21).
      assert (Q22 : getr r3 22 = getr regs 22) by (kept_rw K3; exact A22).
      assert (Q23 : getr r3 23 = getr regs 23) by (kept_rw K3; exact A23).
      assert (Q24 : getr r3 24 = getr regs 24) by (kept_rw K3; exact A24).
      assert (Q25 : getr r3 25 = getr regs 25) by (kept_rw K3; exact A25).
      assert (Q26 : getr r3 26 = getr regs 26) by (kept_rw K3; exact A26).
      assert (Q27 : getr r3 27 = getr regs 27) by (kept_rw K3; exact A27).
      exact (FIN (UbMhSetBit.st' st1 m i) M3 mdl r3 WF3 REP3 LG3 NJ3 eq_refl (fsub_trans _ _ _ (fsub_junk st m i off) (fsub_setbit st1 m i)) Hh Hlz Hmat eq_refl eq_refl eq_refl (defined_grows M M3 _ _ GR3 DEF) FRM3
                 T2 Q3 Q4 T8 T9 T18 T19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27). }
    (* [comment removed for export] *)
    intros HNT.
    assert (REP12 : REP st1 M2).
    { apply (REP_scribble st1 L' M1 M2 m i off WF1 REP11 Hgrp1 Hi Hslot1 G2). intros a Hr NE. left. rewrite Ejq. exact (W2 a Hr NE). }
    assert (Hms : 0 <= Z.lor (mr_avail (s_meta st m)) (mr_freed (s_meta st m)) + 2 ^ i < 2 ^ 32).
    { pose proof (Z_lor_range32 _ _ AVr FRr) as MR.
      assert (MB : Z.testbit (Z.lor (mr_avail (s_meta st m)) (mr_freed (s_meta st m))) i = false) by (rewrite Z.lor_spec, AVb, FRb; reflexivity).
      pose proof (add_pow2_nocarry32 _ i MR ltac:((first [ (clear FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])) MB). assert (0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia). (first [ (clear FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). }
    assert (Hallr : 0 <= 2 * 2 ^ g_lastidx st m - 1 < 2 ^ 32).
    { assert (2 ^ g_lastidx st m <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ g_lastidx st m) by (apply Z.pow_pos_nonneg; lia).
      change (2 ^ 32) with (2 * 2 ^ 31). (first [ (clear FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). }
    destruct (segN M2 i (mr_freed (s_meta st m)) (Z.lor (mr_avail (s_meta st m)) (mr_freed (s_meta st m))) (2 * 2 ^ g_lastidx st m - 1)
                FRr ltac:((first [ (clear FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])) HNT r2 rom C15 C16 C12 C13 C17 C8) as (r3 & RUN3 & D11 & D1 & K3).
    assert (D10 : getr r3 10 = Z_to_bv 64 m) by (kept_rw K3; exact C10).
    assert (D2 : getr r3 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K3; kept_rw K2; exact A2).
    assert (RET3 : ret_ok (getr r3 1)) by (rewrite D1; apply ret_ok_even; reflexivity).
    assert (DEP1 : nest_depth_le st1 8 m) by (apply (nest_depth_kind st st1 8 m (fun y => eq_refl)); exact (wg_depth st L m WG)).
    assert (DEF2 : defined M2 (sp - 48 - 96 * (Z.of_nat 8 + 1)) (sp - 48)).
    { eapply defined_grows; [eapply mem_grows_trans; [exact G1 | exact G2]|]. intros a Ha. apply DEF. lia. }
    pose proof (@ntf_run _ _ 8) as NTF. unfold NTF_SPEC in NTF.
    destruct (NTF st1 L' M2 r3 rom m i off (sp - 48) WF1 REP12 Hgrp1 Hi Hslot1 DEP1 OJ1 D10 D11 D2 RET3
                  ltac:(change (Z.of_nat 8) with 8; ceil; (first [ (clear HNT Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])) ltac:((first [ (clear HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])) ltac:(rewrite Zminus_mod, Hsp16; reflexivity) DEF2)
      as (st4 & M4 & r4 & RUN4 & WF4 & REP4 & B4 & L4 & C4 & NJ4 & RET4 & K4 & FS4 & FR4).
    clear NTF.
    assert (FS04 : fsub st st4) by exact (fsub_trans _ _ _ (fsub_junk st m i off) FS4).
    rewrite D1 in RUN4. replace (Z_to_bv 64 0x66728) with (0x66728%bv : word) in RUN4 by (apply bv_eq; reflexivity).
    change (Z.of_nat 8) with 8 in FR4. replace (sp - 48 - 96 * (8 + 1)) with (sp - 912) in FR4 by lia.
    destruct FR4 as [G24 W4].
    (* [comment removed for export] *)
    assert (KEEP24 : forall a bs, sp - 48 <= a -> a + 8 <= sp -> rdn RSEGS M2 (Z_to_bv 64 a) 8%nat = Some bs -> rdn RSEGS M4 (Z_to_bv 64 a) 8%nat = Some bs).
    { intros a bs H1 H8 R. apply (FR_rdn_keep L' (sp - 912) (sp - 48) M2 M4 a 8%nat bs (conj G24 W4)); [ceil; (first [ (clear HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]) | cbn; (first [ (clear HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]) | cbn; (first [ (clear HNT Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]) | exact R]. }
    assert (S2 : forall a, sp - 48 <= a -> a + 8 <= sp -> rdn RSEGS M2 (Z_to_bv 64 a) 8%nat = rdn RSEGS M1 (Z_to_bv 64 a) 8%nat).
    { intros a Ha Ha8. unfold M2, m2. ceil; unfold HEAPLO in *. do 2 rdn_peel1. reflexivity. }
    assert (Mra4 : rdn RSEGS M4 (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 (getr regs 1))) by (apply KEEP24; [lia | lia | rewrite S2 by lia; exact Mra]).
    assert (Ms04 : rdn RSEGS M4 (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (apply KEEP24; [lia | lia | rewrite S2 by lia; exact Ms0]).
    assert (Ms14 : rdn RSEGS M4 (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (apply KEEP24; [lia | lia | rewrite S2 by lia; exact Ms1]).
    assert (Ms24 : rdn RSEGS M4 (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (apply KEEP24; [lia | lia | rewrite S2 by lia; exact Ms2]).
    assert (Ms34 : rdn RSEGS M4 (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (apply KEEP24; [lia | lia | rewrite S2 by lia; exact Ms3]).
    (* [comment removed for export] *)
    destruct (segU M4 (rc_lock st4 M4 (rp_statics st4 M4 REP4)) r4 rom) as (r5 & RUN5 & U8 & U9 & U10 & U11 & U1 & K5).
    assert (V2 : getr r5 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K5; kept_rw K4; exact D2).
    assert (GR4 : mem_grows M M4) by (eapply mem_grows_trans; [exact G1 | eapply mem_grows_trans; [exact G2 | exact G24]]).
    (* [comment removed for export] *)
    assert (FRM4 : forall a, 0 <= a < 2 ^ 64 -> M4 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
        (sp - 912 <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L' a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4)).
    { intros a Hr NE. destruct (decide (M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E4|NE4].
      - destruct (decide (M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E3|NE3].
        + left. pose proof (W1 a Hr ltac:(congruence)). lia.
        + right; left. apply HDRown. pose proof (W2 a Hr NE3). lia.
      - destruct (W4 a Hr NE4) as [A|[A|A]]; [left; lia | right; left; exact A | right; right; left; exact A]. }
    (* [comment removed for export] *)
    assert (P3 : getr r5 3 = getr regs 3) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A3).
    assert (P4 : getr r5 4 = getr regs 4) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A4).
    assert (P20 : getr r5 20 = getr regs 20) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A20).
    assert (P21 : getr r5 21 = getr regs 21) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A21).
    assert (P22 : getr r5 22 = getr regs 22) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A22).
    assert (P23 : getr r5 23 = getr regs 23) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A23).
    assert (P24 : getr r5 24 = getr regs 24) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A24).
    assert (P25 : getr r5 25 = getr regs 25) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A25).
    assert (P26 : getr r5 26 = getr regs 26) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A26).
    assert (P27 : getr r5 27 = getr regs 27) by (kept_rw K5; kept_rw K4; kept_rw K3; kept_rw K2; exact A27).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN3 |]. eapply kat_msteps; [exact Hh | exact Hlz | exact RUN4 |].
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN5 |].
    destruct RET4 as [[Z11 RG4]|(b & len & x & PERM & B10 & B11 & LEN)].
    - (* [comment removed for export] *)
      destruct (segE0 M4 sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(ceil; lia) Hra
                  Mra4 Ms04 Ms14 Ms24 Ms34 r5 rom V2 ltac:(rewrite U9; exact Z11)) as (r6 & RUN6 & X2 & X1 & X8 & X9 & X18 & X19 & K6).
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN6 |]. apply kat_refl.
      assert (LG4 : LEDGER st4 (m_vmmaps mdl)) by (apply (LEDGER_same st); [rewrite RG4; reflexivity | exact B4 | exact HLG]).
      assert (Q3 : getr r6 3 = getr regs 3) by (kept_rw K6; exact P3).
      assert (Q4 : getr r6 4 = getr regs 4) by (kept_rw K6; exact P4).
      assert (Q20 : getr r6 20 = getr regs 20) by (kept_rw K6; exact P20).
      assert (Q21 : getr r6 21 = getr regs 21) by (kept_rw K6; exact P21).
      assert (Q22 : getr r6 22 = getr regs 22) by (kept_rw K6; exact P22).
      assert (Q23 : getr r6 23 = getr regs 23) by (kept_rw K6; exact P23).
      assert (Q24 : getr r6 24 = getr regs 24) by (kept_rw K6; exact P24).
      assert (Q25 : getr r6 25 = getr regs 25) by (kept_rw K6; exact P25).
      assert (Q26 : getr r6 26 = getr regs 26) by (kept_rw K6; exact P26).
      assert (Q27 : getr r6 27 = getr regs 27) by (kept_rw K6; exact P27).
      exact (FIN st4 M4 mdl r6 WF4 REP4 LG4 NJ4 L4 FS04 Hh Hlz Hmat eq_refl eq_refl eq_refl (defined_grows M M4 _ _ GR4 DEF) FRM4
                 X2 Q3 Q4 X8 X9 X18 X19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27).
    - (* [comment removed for export] *)
      pose proof (rg_rng st1 st4 L' b len x WF1 PERM) as (R1 & R2 & R3 & R4 & R5). pose proof (rg_img st1 st4 L' b len x WF1 PERM) as RI. ceil; unfold HEAPLO in R1, R2.
      assert (LG1 : LEDGER st1 (m_vmmaps mdl)) by (apply (LEDGER_same st); [reflexivity | reflexivity | exact HLG]).
      pose proof (wc_errno st4 (WF_ctx st4 L' WF4)) as He.
      pose proof (rc_errno st4 M4 (rp_statics st4 M4 REP4)) as Merr.
      assert (DEF4 : defined M4 (sp - 912) sp) by (exact (defined_grows M M4 _ _ GR4 DEF)).
      assert (SOK32 : store_ok RSEGS M4 (Z_to_bv 64 (sp - 80)) 32%nat = true).
      { eapply store_ok_defined; [exact DEF4 | (first [ (clear H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]) | cbn; (first [ (clear H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]) | ceil; (first [ (clear H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]) | exact Hsphi]. }
      assert (V4 : getr r5 4 = Z_to_bv 64 TPV) by (rewrite P4; exact H4).
      destruct (segM1 M4 sp b len (s_errno st4) ltac:(ceil; (first [ (clear RI R5 R3 HNT Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])) ltac:((first [ (clear H0 R3 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])) He Merr SOK32 r5 rom V2 V4
                  ltac:(rewrite U8; exact B10) ltac:(rewrite U9; exact B11))
        as (r6 & RUN6 & Y17 & Y10 & Y11 & Y8 & Y9 & Y18 & Y19 & Y2 & Y1 & K6).
      set (M5 := m_m1 M4 sp b len) in RUN6.
      assert (G45 : mem_grows M4 M5) by (unfold M5, m_m1; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (W5 : forall a, 0 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) <> M4 (Z_to_bv 64 a) -> sp - 80 <= a < sp - 48).
      { intros a Hr NE. unfold M5, m_m1 in NE. ceil. wdiff NE M4 a. }
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN6 |].
      apply (kat_ecall_munmap r6 (0x68518%bv : word) M5 rom mdl W_684c4 (Z_to_bv 64 b) len Q F_684c4 eq_refl Hh Hlz Y17 Y10
               ltac:(rewrite u_Z2bv by (first [ (clear H0 R5 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]); exact R3) Y11 R4 R5 ltac:(rewrite u_Z2bv by (first [ (clear H0 R5 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]); (first [ (clear HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])) (rg_map_has st1 st4 b len x PERM _ LG1)).
      replace (v_addi (0x68518%bv : word) 4) with (0x6851c%bv : word) by (apply bv_eq; reflexivity).
      rewrite (munmap_model_eq (Z_to_bv 64 b) (Z_to_bv 64 len) mdl Hlz Hmat).
      rewrite !(u_Z2bv b), !(u_Z2bv len) by (first [ (clear H0 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]).
      set (vm' := mkVmMapsFull (vm_reserved (m_vmmaps mdl)) (map_remove (vm_maps (m_vmmaps mdl)) (Z_to_bv 64 b))
                    (maps_subtract (vm_noaccess (m_vmmaps mdl)) b (b + len))
                    (vm_start_brk (m_vmmaps mdl)) (vm_brk (m_vmmaps mdl)) (vm_limit (m_vmmaps mdl)) (vm_mmap_base (m_vmmaps mdl))
                    (vm_init_sp (m_vmmaps mdl))).
      destruct (with_vmmaps_facts vm' mdl) as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6).
      set (mdl' := with_vmmaps vm' mdl) in *.
      set (M5u := unfill (Z_to_bv 64 b) (Z_to_bv 64 len) M5).
      (* [comment removed for export] *)
      assert (UO : forall a kk, b + len <= a -> a < 2 ^ 64 -> a + Z.of_nat kk <= 2 ^ 64 -> rdn RSEGS M5u (Z_to_bv 64 a) kk = rdn RSEGS M5 (Z_to_bv 64 a) kk).
      { intros a kk Ha Ha' Hk. unfold M5u. apply rdn_unfill_out; rewrite ?u_Z2bv by (first [ (clear H0 HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]); (first [ (clear H0 HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). }
      assert (UO1 : forall a, (0 <= a < b \/ b + len <= a < 2 ^ 64) -> M5u (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
      { intros a Ha. unfold M5u. apply unfill_out. rewrite !u_Z2bv by (first [ (clear H0 HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). lia. }
      assert (S5 : forall a, sp - 48 <= a -> a + 8 <= sp -> rdn RSEGS M5 (Z_to_bv 64 a) 8%nat = rdn RSEGS M4 (Z_to_bv 64 a) 8%nat).
      { intros a Ha Ha8. unfold M5, m_m1. ceil. do 3 rdn_peel1. reflexivity. }
      assert (Mr2 : rdn RSEGS M5u (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66758))).
      { rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])). unfold M5, m_m1. ceil. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]). }
      assert (Mv1 : rdn RSEGS M5u (Z_to_bv 64 (sp - 64)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 b))).
      { rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])). unfold M5, m_m1. ceil. rdn_peel1. apply rdn_wbytes_hit8. zsimp; (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]). }
      assert (Mv2 : rdn RSEGS M5u (Z_to_bv 64 (sp - 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 len))).
      { rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])). unfold M5, m_m1. ceil. apply rdn_wbytes_hit8. zsimp; (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]). }
      assert (Mra5 : rdn RSEGS M5u (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 (getr regs 1))) by (rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])); rewrite S5 by (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]); exact Mra4).
      assert (Ms05 : rdn RSEGS M5u (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])); rewrite S5 by (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]); exact Ms04).
      assert (Ms15 : rdn RSEGS M5u (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])); rewrite S5 by (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]); exact Ms14).
      assert (Ms25 : rdn RSEGS M5u (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])); rewrite S5 by (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]); exact Ms24).
      assert (Ms35 : rdn RSEGS M5u (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (rewrite UO by (ceil; cbn; (first [ (clear H0 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ])); rewrite S5 by (first [ (clear UO1 H0 RI R5 R3 HNT METAown HDRown Ear Hpg PI Pmod Pal Smod MR8; lia) | lia ]); exact Ms34).
      (* [comment removed for export] *)
      pose proof (store_ok_errno M5u) as SOKe.
      assert (Merr5u : rdn RSEGS M5u (Z_to_bv 64 A_ERRNO) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (s_errno st4)))).
      { unfold M5u. rewrite rdn_unfill_out by (rewrite ?u_Z2bv by (unfold A_ERRNO, TPV; (first [ (clear H0 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])); unfold A_ERRNO, TPV; cbn; (first [ (clear H0 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])).
        unfold M5, m_m1. ceil; unfold A_ERRNO, TPV in *. do 3 rdn_peel1. exact Merr. }
      assert (Z10 : getr (regupd r6 10 (Z_to_bv 64 0)) 10 = Z_to_bv 64 0) by (apply getr_same; intros E; discriminate E).
      assert (Z2 : getr (regupd r6 10 (Z_to_bv 64 0)) 2 = Z_to_bv 64 (sp - 80)) by (rewrite getr_other by (intros E; discriminate E); exact Y2).
      assert (Z18 : getr (regupd r6 10 (Z_to_bv 64 0)) 18 = Z_to_bv 64 A_ERRNO) by (rewrite getr_other by (intros E; discriminate E); exact Y18).
      assert (Z19 : getr (regupd r6 10 (Z_to_bv 64 0)) 19 = s32 (s_errno st4)) by (rewrite getr_other by (intros E; discriminate E); exact Y19).
      destruct (segM2 M5u sp (s_errno st4) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (Z_to_bv 64 b) (Z_to_bv 64 len)
                  ltac:(ceil; lia) Hra SOKe Mr2 Mv1 Mv2 Mra5 Ms05 Ms15 Ms25 Ms35 (regupd r6 10 (Z_to_bv 64 0)) rom Z10 Z2 Z18 Z19)
        as (r7 & RUN7 & X2 & X1 & X8 & X9 & X18 & X19 & K7).
      set (M6 := m_m2 M5u (s_errno st4)) in RUN7.
      eapply kat_msteps; [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN7 |]. apply kat_refl.
      (* [comment removed for export] *)
      assert (E65 : forall y, 0 <= y < 2 ^ 64 -> ~ (A_ERRNO <= y < A_ERRNO + 4) -> M6 (Z_to_bv 64 y) = M5u (Z_to_bv 64 y)).
      { intros y Hy Hny. unfold M6, m_m2. rewrite (w4_errno (s_errno st4) He).
        apply UbMhEnframeBase.wbytes_miss; rewrite ?UbMhEnframeBase.length_wle4, ?u_Z2bv by (unfold A_ERRNO, TPV in *; (first [ (clear UO1 H0 RI R5 R3 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])); unfold A_ERRNO, TPV in *; (first [ (clear UO1 H0 RI R5 R3 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). }
      assert (G56 : mem_grows M5u M6) by (unfold M6, m_m2; apply wbytes_grows).
      (* [comment removed for export] *)
      assert (REP5 : REP st4 M5).
      { apply (REP_frame st4 L' M4 WF4 REP4 M5 G45). intros a Hr NE. left. pose proof (W5 a Hr NE). ceil. (first [ (clear RI R5 R3 HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]). }
      assert (REP5u : REP st4 M5u).
      { apply (REP_agree_but st4 L' M5 M5u b (b + len) WF4 REP5).
        - intros a Hr NE. destruct (Z.lt_ge_cases a b); [exfalso; apply NE; apply UO1; lia|].
          destruct (Z.lt_ge_cases a (b + len)); [lia | exfalso; apply NE; apply UO1; lia].
        - unfold HEAPLO; (first [ (clear H0 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ]).
        - intros a Ha. exact (unmapped_clear st1 st4 L' L' b len x WF1 WF4 PERM a Ha). }
      assert (REP6 : REP st4 M6).
      { unfold M6, m_m2. rewrite (w4_errno (s_errno st4) He). exact (REP_errno_write st4 L' M5u WF4 REP5u). }
      assert (LG6 : LEDGER st4 (m_vmmaps mdl')) by (rewrite MF1; exact (LEDGER_unmap st1 st4 L' L' b len x WF1 WF4 PERM B4 _ LG1)).
      assert (DEF6 : defined M6 (sp - 912) sp).
      { intros y Hy. apply G56. rewrite UO1 by (ceil; (first [ (clear H0 FRM4 W4 HNT FIN METAown HDRown Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])). apply G45. apply DEF4. exact Hy. }
      assert (FRM6 : forall a, 0 <= a < 2 ^ 64 -> M6 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
          (sp - 912 <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L' a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4)).
      { intros a Hr NE. destruct (decide (A_ERRNO <= a < A_ERRNO + 4)) as [EA|NA]; [right; right; right; exact EA|].
        rewrite E65 in NE by assumption.
        destruct (Z.lt_ge_cases a b) as [Bl|Bg]; [|destruct (Z.lt_ge_cases a (b + len)) as [Bi|Bo]].
        2:{ right; left. split; [ceil; unfold HEAPLO; (first [ (clear RI R5 R3 HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])|]. split; [pose proof (rg_img st1 st4 L' b len x WF1 PERM); (first [ (clear H1 H0 RI R5 R3 HNT Ear Hpg PI Pmod Pal Smod MR8 Hsp16; lia) | lia ])|]. intros (q & nq & Hq & Hqa). exact (unmapped_not_app st1 st4 L' L' b len x WF1 WF4 PERM a q nq ltac:(lia) Hq Hqa). }
        all: rewrite UO1 in NE by lia.
        all: destruct (decide (M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a))) as [E5|NE5]; [apply FRM4; [exact Hr | congruence] | left; pose proof (W5 a Hr NE5); lia]. }
      assert (Q3 : getr r7 3 = getr regs 3) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P3).
      assert (Q4 : getr r7 4 = getr regs 4) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P4).
      assert (Q20 : getr r7 20 = getr regs 20) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P20).
      assert (Q21 : getr r7 21 = getr regs 21) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P21).
      assert (Q22 : getr r7 22 = getr regs 22) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P22).
      assert (Q23 : getr r7 23 = getr regs 23) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P23).
      assert (Q24 : getr r7 24 = getr regs 24) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P24).
      assert (Q25 : getr r7 25 = getr regs 25) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P25).
      assert (Q26 : getr r7 26 = getr regs 26) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P26).
      assert (Q27 : getr r7 27 = getr regs 27) by (kept_rw K7; rewrite getr_other by (intros E; discriminate E); kept_rw K6; exact P27).
      apply (FIN st4 M6 mdl' r7 WF4 REP6 LG6 NJ4 L4 FS04); try exact X2; try exact DEF6; try exact FRM6.
      + rewrite MF2. exact Hh.
      + rewrite MF3. exact Hlz.
      + rewrite MF4. exact Hmat.
      + exact MF5.
      + exact MF6.
      + rewrite MF1. reflexivity.
      + exact Q3. + exact Q4. + exact X8. + exact X9. + exact X18. + exact X19.
      + exact Q20. + exact Q21. + exact Q22. + exact Q23. + exact Q24. + exact Q25. + exact Q26. + exact Q27.
  Qed.
End Free.

Ltac lia_pairs ::= idtac.
