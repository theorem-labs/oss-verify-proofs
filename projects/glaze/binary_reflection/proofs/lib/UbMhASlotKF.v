(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhASlotT1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
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
Section G1.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem).

  Lemma tG1 : forall regs rom,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps RSEGS (mkst regs (0x674a8 : word) m rom) (mkst regs' (0x67b10 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (2^64 - 1) /\ getr regs' 9 = Z_to_bv 64 0
      /\ keeps_but [9; 10]%bv regs regs'.
  Proof using.
    intros regs rom H10.
    eexists. split.
    - stepn F_67454 D_67454. rewrite H10.
      stepn F_67458 D_67458.
      stepb_tk F_6745c D_6745c ltac:(apply c_eq_refl).
      pu_refl.
    - repeat split; gres; try reflexivity. all: solve_keeps_but.
  Qed.
End G1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FM.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  (* [comment removed for export] *)
  Variables (m : mem) (sp g fh ft : Z).
  Hypothesis Hsp : (CEIL + 144 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hfh : (0 <= fh < 2^64)%Z.
  Hypothesis Hft : (0 <= ft < 2^64)%Z.
  Hypothesis SOKsp : store_ok RSEGS m (Z_to_bv 64 (sp - 136)) 40%nat = true.
  Hypothesis SOKg : store_ok RSEGS m (Z_to_bv 64 g) 40%nat = true.
  Hypothesis M_fh : rdn RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fh)).
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = true.

  Definition z8' := word_to_le_bytes 8 (Z_to_bv 64 0).
  (* [comment removed for export] *)
  Definition m_fz : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 104)) z8') (Z_to_bv 64 (sp - 136)) z8') (Z_to_bv 64 (sp - 128)) z8') (Z_to_bv 64 (sp - 120)) z8') (Z_to_bv 64 (sp - 112)) z8')
      (Z_to_bv 64 (g + 8)) z8') (Z_to_bv 64 (g + 32)) z8') (Z_to_bv 64 (g + 24)) z8') (Z_to_bv 64 (g + 16)) z8') (Z_to_bv 64 g) z8'.

  (* [comment removed for export] *)
  Definition m_fe : mem :=
    wbytes (wbytes (wbytes m_fz (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 ctx_free_meta_head) (word_to_le_bytes 8 (Z_to_bv 64 g)).

  (* [comment removed for export] *)
  Definition m_fq : mem :=
    wbytes (wbytes (wbytes (wbytes m_fz (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 fh)))
      (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 ft)))
      (Z_to_bv 64 (ft + 8)) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 fh) (word_to_le_bytes 8 (Z_to_bv 64 g)).

  Ltac sok40 SOK := store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOK | | ]; zsimp; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fz3 SOKsp SOKg :=
    stepSTx F_676b4 D_676b4 (Z_to_bv 64 (sp - 104)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_676b8 D_676b8 (Z_to_bv 64 (sp - 136)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_676bc D_676bc (Z_to_bv 64 (sp - 128)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_676c0 D_676c0 (Z_to_bv 64 (sp - 120)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_676c4 D_676c4 (Z_to_bv 64 (sp - 112)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepLD8 F_676c8 D_676c8 (Z_to_bv 64 0);
    stepSTx F_676cc D_676cc (Z_to_bv 64 (g + 8)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_676d0 D_676d0 (Z_to_bv 64 0);
    stepSTx F_676d4 D_676d4 (Z_to_bv 64 (g + 32)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_676d8 D_676d8 (Z_to_bv 64 0);
    stepSTx F_676dc D_676dc (Z_to_bv 64 (g + 24)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_676e0 D_676e0 (Z_to_bv 64 0);
    stepSTx F_676e4 D_676e4 (Z_to_bv 64 (g + 16)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_676e8 D_676e8 (Z_to_bv 64 0);
    stepSTx F_676ec D_676ec (Z_to_bv 64 g) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_676f0 D_676f0 (Z_to_bv 64 0);
    stepb_tk F_676f4 D_676f4 ltac:(apply c_eq_refl);
    stepLD8 F_676fc D_676fc (Z_to_bv 64 0);
    stepn F_67700 D_67700;
    stepb_tk F_67704 D_67704 ltac:(apply c_eq_refl).

  Lemma tG3e : forall regs rom,
    getr regs 10 = Z_to_bv 64 (2^64 - 1) -> getr regs 9 = Z_to_bv 64 g -> getr regs 2 = Z_to_bv 64 (sp - 144) ->
    getr regs 22 = Z_to_bv 64 MLOCK -> fh = 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x67690 : word) m rom) (mkst regs' (0x67b10 : word) m_fe rom)
      /\ getr regs' 10 = Z_to_bv 64 (2^64 - 1) /\ keeps_but [10; 11; 22]%bv regs regs'.
  Proof using SOKc M_fh SOKg SOKsp Hg Hsp RN.
    intros regs rom H10 H9 H2 H22 Hfh0. ceil; unfold HEAPLO, ctx_free_meta_head, CTX, MLOCK in *. unfold m_fe, m_fz, z8', ctx_free_meta_head, CTX.
    eexists. split.
    - stepb_tk F_6763c D_6763c ltac:(rewrite H10; cond_compute).
      fz3 SOKsp SOKg.
      stepLD F_6770c D_6770c (word_to_le_bytes 8 (Z_to_bv 64 fh)) (Z_to_bv 64 fh)
        ltac:(addr_norm; repeat rdn_peel1; exact M_fh) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_67710 D_67710 ltac:(rewrite Hfh0; apply c_eq_refl).
      stepSTx F_677bc D_677bc (Z_to_bv 64 g) (Z_to_bv 64 g) ltac:(sok40 SOKg).
      stepSTx F_677c0 D_677c0 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 g) ltac:(sok40 SOKg).
      stepn F_677c4 D_677c4. rewrite H22. addi_renorm.
      stepSTx F_677c8 D_677c8 (Z_to_bv 64 (700056 + 16)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKc).
      stepn F_677cc D_677cc.
      pu_refl.
    - repeat split; gres; try reflexivity. all: solve_keeps_but.
  Qed.

  Lemma tG3q : forall regs rom,
    (HEAPLO <= fh)%Z -> (fh + 40 <= CEIL)%Z -> (HEAPLO <= ft)%Z -> (ft + 40 <= CEIL)%Z ->
    (g + 40 <= fh \/ fh + 40 <= g)%Z -> (g + 40 <= ft \/ ft + 40 <= g)%Z ->
    rdn RSEGS m (Z_to_bv 64 fh) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ft)) ->
    store_ok RSEGS m (Z_to_bv 64 fh) 8%nat = true -> store_ok RSEGS m (Z_to_bv 64 (ft + 8)) 8%nat = true ->
    getr regs 10 = Z_to_bv 64 (2^64 - 1) -> getr regs 9 = Z_to_bv 64 g -> getr regs 2 = Z_to_bv 64 (sp - 144) ->
    getr regs 22 = Z_to_bv 64 MLOCK -> fh <> 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x67690 : word) m rom) (mkst regs' (0x67b10 : word) m_fq rom)
      /\ getr regs' 10 = Z_to_bv 64 (2^64 - 1) /\ keeps_but [10; 11; 22]%bv regs regs'.
  Proof using M_fh SOKg SOKsp Hft Hfh Hg Hsp.
    intros regs rom Hh1 Hh2 Ht1 Ht2 Dgh Dgt M_ft SOKh SOKt H10 H9 H2 H22 Hnz.
    ceil; unfold HEAPLO, ctx_free_meta_head, CTX, MLOCK in *. unfold m_fq, m_fz, z8', ctx_free_meta_head, CTX.
    eexists. split.
    - stepb_tk F_6763c D_6763c ltac:(rewrite H10; cond_compute).
      fz3 SOKsp SOKg.
      stepLD F_6770c D_6770c (word_to_le_bytes 8 (Z_to_bv 64 fh)) (Z_to_bv 64 fh)
        ltac:(addr_norm; repeat rdn_peel1; exact M_fh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_67710 D_67710 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepSTx F_67714 D_67714 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 fh) ltac:(sok40 SOKg).
      stepLD8 F_67718 D_67718 (Z_to_bv 64 ft).
      stepSTx F_6771c D_6771c (Z_to_bv 64 g) (Z_to_bv 64 ft) ltac:(sok40 SOKg).
      stepSTx F_67720 D_67720 (Z_to_bv 64 (ft + 8)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKt).
      stepLD8 F_67724 D_67724 (Z_to_bv 64 fh).
      stepSTx F_67728 D_67728 (Z_to_bv 64 fh) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKh).
      stepn F_6772c D_6772c.
      pu_refl.
    - repeat split; gres; try reflexivity. all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fz2 SOKsp SOKg :=
    stepSTx F_67a34 D_67a34 (Z_to_bv 64 (sp - 104)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_67a38 D_67a38 (Z_to_bv 64 (sp - 136)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_67a3c D_67a3c (Z_to_bv 64 (sp - 128)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_67a40 D_67a40 (Z_to_bv 64 (sp - 120)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepSTx F_67a44 D_67a44 (Z_to_bv 64 (sp - 112)) (Z_to_bv 64 0) ltac:(sok40 SOKsp);
    stepLD8 F_67a48 D_67a48 (Z_to_bv 64 0);
    stepSTx F_67a4c D_67a4c (Z_to_bv 64 (g + 8)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_67a50 D_67a50 (Z_to_bv 64 0);
    stepSTx F_67a54 D_67a54 (Z_to_bv 64 (g + 32)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_67a58 D_67a58 (Z_to_bv 64 0);
    stepSTx F_67a5c D_67a5c (Z_to_bv 64 (g + 24)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_67a60 D_67a60 (Z_to_bv 64 0);
    stepSTx F_67a64 D_67a64 (Z_to_bv 64 (g + 16)) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_67a68 D_67a68 (Z_to_bv 64 0);
    stepSTx F_67a6c D_67a6c (Z_to_bv 64 g) (Z_to_bv 64 0) ltac:(sok40 SOKg);
    stepLD8 F_67a70 D_67a70 (Z_to_bv 64 0);
    stepb_tk F_67a74 D_67a74 ltac:(apply c_eq_refl);
    stepLD8 F_67a7c D_67a7c (Z_to_bv 64 0);
    stepb_tk F_67a80 D_67a80 ltac:(apply c_eq_refl).

  Lemma tG2e : forall regs rom,
    getr regs 10 = Z_to_bv 64 (2^64 - 1) -> getr regs 18 = Z_to_bv 64 (2^64 - 1) -> getr regs 9 = Z_to_bv 64 g ->
    getr regs 2 = Z_to_bv 64 (sp - 144) -> getr regs 22 = Z_to_bv 64 MLOCK -> fh = 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x67960 : word) m rom) (mkst regs' (0x67b10 : word) m_fe rom)
      /\ getr regs' 10 = Z_to_bv 64 (2^64 - 1) /\ keeps_but [10; 22]%bv regs regs'.
  Proof using SOKc M_fh SOKg SOKsp Hg Hsp RN.
    intros regs rom H10 H18 H9 H2 H22 Hfh0. ceil; unfold HEAPLO, ctx_free_meta_head, CTX, MLOCK in *. unfold m_fe, m_fz, z8', ctx_free_meta_head, CTX.
    eexists. split.
    - stepb_tk F_6790c D_6790c ltac:(rewrite H10, H18; apply c_eq_refl).
      fz2 SOKsp SOKg.
      stepLD F_67a88 D_67a88 (word_to_le_bytes 8 (Z_to_bv 64 fh)) (Z_to_bv 64 fh)
        ltac:(addr_norm; repeat rdn_peel1; exact M_fh) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_67a8c D_67a8c ltac:(rewrite Hfh0; apply c_eq_refl).
      stepSTx F_67aa8 D_67aa8 (Z_to_bv 64 g) (Z_to_bv 64 g) ltac:(sok40 SOKg).
      stepSTx F_67aac D_67aac (Z_to_bv 64 (g + 8)) (Z_to_bv 64 g) ltac:(sok40 SOKg).
      stepn F_67ab0 D_67ab0. rewrite H22. addi_renorm.
      stepSTx F_67ab4 D_67ab4 (Z_to_bv 64 (700056 + 16)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKc).
      stepn F_67ab8 D_67ab8.
      pu_refl.
    - repeat split; gres; try reflexivity. all: solve_keeps_but.
  Qed.

  Lemma tG2q : forall regs rom,
    (HEAPLO <= fh)%Z -> (fh + 40 <= CEIL)%Z -> (HEAPLO <= ft)%Z -> (ft + 40 <= CEIL)%Z ->
    (g + 40 <= fh \/ fh + 40 <= g)%Z -> (g + 40 <= ft \/ ft + 40 <= g)%Z ->
    rdn RSEGS m (Z_to_bv 64 fh) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ft)) ->
    store_ok RSEGS m (Z_to_bv 64 fh) 8%nat = true -> store_ok RSEGS m (Z_to_bv 64 (ft + 8)) 8%nat = true ->
    getr regs 10 = Z_to_bv 64 (2^64 - 1) -> getr regs 18 = Z_to_bv 64 (2^64 - 1) -> getr regs 9 = Z_to_bv 64 g ->
    getr regs 2 = Z_to_bv 64 (sp - 144) -> getr regs 22 = Z_to_bv 64 MLOCK -> fh <> 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x67960 : word) m rom) (mkst regs' (0x67b10 : word) m_fq rom)
      /\ getr regs' 10 = Z_to_bv 64 (2^64 - 1) /\ keeps_but [10; 22]%bv regs regs'.
  Proof using M_fh SOKg SOKsp Hft Hfh Hg Hsp.
    intros regs rom Hh1 Hh2 Ht1 Ht2 Dgh Dgt M_ft SOKh SOKt H10 H18 H9 H2 H22 Hnz.
    ceil; unfold HEAPLO, ctx_free_meta_head, CTX, MLOCK in *. unfold m_fq, m_fz, z8', ctx_free_meta_head, CTX.
    eexists. split.
    - stepb_tk F_6790c D_6790c ltac:(rewrite H10, H18; apply c_eq_refl).
      fz2 SOKsp SOKg.
      stepLD F_67a88 D_67a88 (word_to_le_bytes 8 (Z_to_bv 64 fh)) (Z_to_bv 64 fh)
        ltac:(addr_norm; repeat rdn_peel1; exact M_fh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_67a8c D_67a8c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepSTx F_67a90 D_67a90 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 fh) ltac:(sok40 SOKg).
      stepLD8 F_67a94 D_67a94 (Z_to_bv 64 ft).
      stepSTx F_67a98 D_67a98 (Z_to_bv 64 g) (Z_to_bv 64 ft) ltac:(sok40 SOKg).
      stepSTx F_67a9c D_67a9c (Z_to_bv 64 (ft + 8)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKt).
      stepLD8 F_67aa0 D_67aa0 (Z_to_bv 64 fh).
      stepn F_67aa4 D_67aa4.
      stepSTx F_67ab4 D_67ab4 (Z_to_bv 64 fh) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKh).
      stepn F_67ab8 D_67ab8.
      pu_refl.
    - repeat split; gres; try reflexivity. all: solve_keeps_but.
  Qed.
End FM.
End UbMhASlotT1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 UbMhASlotT1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ASF.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp sc req : Z) (QF : config -> Prop) (d : nat).
  Hypothesis HWF : WF st L.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
  Hypothesis Hlimbo : zlen (s_limbo st) + Z.of_nat d + 1 <= 8.
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64.
  Hypothesis HQF : forall c', as_fail st L sc d sp regs M mdl rom c' -> QF c'.

  #[local] Notation can := (can st).
  #[local] Notation spc := (spc sp d).
  #[local] Notation stk_ok := (stk_ok st regs sp).

  Lemma stk288 : 288 <= ASSTK d. Proof. apply ASSTK_ge. Qed.
  Lemma stk_le : ASSTK d <= 1296.
  Proof. unfold ASSTK, AMSTK. unfold zlen in Hlimbo. lia. Qed.
  Lemma spcF_ok : CEIL + MSTK <= spc. Proof. unfold UbMhASlotKA.spc. lia. Qed.

  (* [comment removed for export] *)
  Record ptF (s1 : mst) (Mc : mem) (mdl1 : Model) (r : bvmap 5 word) : Prop := PTF {
    f_wf : WF s1 L; f_rep : REP s1 Mc; f_lg : LEDGER s1 (m_vmmaps mdl1);
    f_h : m_halted mdl1 = None; f_lz : m_vm_lazy mdl1 = []; f_mat : m_vm_materialized mdl1 = [];
    f_fs : m_fs mdl1 = m_fs mdl; f_fds : m_fds mdl1 = m_fds mdl; f_lim : vm_limit (m_vmmaps mdl1) = vm_limit (m_vmmaps mdl);
    f_can : s_canary s1 = s_canary st;
    f_lmeta : forall x, In x (s_limbo st) -> s_meta s1 x = s_meta st x;
    f_mU : forall x, metaU st x -> metaU s1 x;
    f_fr : forall a, 0 <= a < 2 ^ 64 -> Mc (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
             (sp - ASSTK d <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4);
    f_def : defined Mc (sp - ASSTK d) sp; f_stk : stk_ok Mc;
    f_r2 : getr r 2 = Z_to_bv 64 (sp - 144); f_r20 : getr r 20 = Z_to_bv 64 A_CANARY; f_K : keeps_but BIG regs r }.



  (* [comment removed for export] *)
  Lemma ptF_regs : forall s1 Mc mdl1 r r',
    ptF s1 Mc mdl1 r -> getr r' 2 = getr r 2 -> getr r' 20 = getr r 20 -> keeps_but BIG regs r' -> ptF s1 Mc mdl1 r'.
  Proof. intros s1 Mc mdl1 r r' P E2 E20 K'. destruct P. constructor; try assumption; congruence. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_F : forall s1 Mc mdl1 r,
    ptF s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    getr r 10 = Z_to_bv 64 (2 ^ 64 - 1) ->
    kat RSEGS (mkCfg (mkst r (0x67b10%bv : word) Mc rom) mdl1) QF.
  Proof.
    intros s1 Mc mdl1 r P NJ1 EL A10.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 LM1 MU1 FR1 DF1 SK1 Q2 Q20 KB].
    pose proof SK1 as (Kc & K1 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25).
    pose proof (rc_canary s1 Mc (rp_statics s1 Mc RP1)) as CAN. rewrite Hcan1 in CAN. fold (UbMhASlotKA.can st) in CAN.
    assert (Hsp' : CEIL + 144 <= sp < 2 ^ 64) by (ceil; pose proof stk288; lia).
    destruct (aEpi Mc sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) Hsp' Rra CAN Kc K1 K8 K9 K18 K19 K20 K21 K22 K23 K24 K25
                r rom Q2 Q20) as (r' & RUN & E2 & E10 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K').
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
    apply kat_refl. apply HQF. unfold as_fail.
    exists s1, Mc, mdl1, r'.
    split; [reflexivity|].
    split; [exact W1|]. split; [exact RP1|]. split; [exact LG1|].
    split; [exact Hh1|]. split; [exact Hlz1|]. split; [exact Hmat1|]. split; [exact Hfs1|]. split; [exact Hfds1|]. split; [exact Hlim1|].
    split; [exact NJ1|]. split; [exact EL|]. split; [exact Hcan1|]. split; [exact LM1|]. split; [exact MU1|].
    split; [rewrite E10; exact A10|]. split; [rewrite E2, R2; reflexivity|].
    split.
    { apply keeps_final_as; try assumption.
      - eapply keeps_big; [exact KB | exact K' | reflexivity].
      - rewrite E2, R2. reflexivity. }
    split; [exact FR1 | exact DF1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_G1 : forall s1 Mc mdl1 r,
    ptF s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = s_limbo st ->
    getr r 10 = Z_to_bv 64 0 ->
    kat RSEGS (mkCfg (mkst r (0x674a8%bv : word) Mc rom) mdl1) QF.
  Proof.
    intros s1 Mc mdl1 r P NJ1 EL A10.
    destruct (tG1 Mc r rom A10) as (r' & RUN & E10 & E9 & K').
    eapply kat_msteps; [exact (f_h _ _ _ _ P) | exact (f_lz _ _ _ _ P) | exact RUN |].
    apply (L_F s1 Mc mdl1 r'); try assumption.
    apply (ptF_regs s1 Mc mdl1 r r' P); try (kept_rw K'; reflexivity).
    eapply keeps_big; [exact (f_K _ _ _ _ P) | exact K' | reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma meta_fr : forall s1 x a, WF s1 L -> metaU s1 x -> x <= a < x + 40 ->
    HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a.
  Proof.
    intros s1 x a W Ux Ha. destruct (metaU_area s1 L W x Ux) as (ar & kk & Har & _ & _ & _ & Rlo & Rhi & A1 & A2 & _).
    split; [lia|]. split; [pose proof (metaU_img s1 L W x Ux); lia|].
    intros (p & n & Hin & Hpn). destruct (wL_in s1 L (WF_live s1 L W) p n Hin) as (y & k & o & rr & Hy & Hk & Sy).
    apply (ge_app_area s1 (WF_geom s1 L W) a); [exists y, k, p, n, o, rr; repeat split; try assumption; lia | exists ar; split; [exact Har | lia]].
  Qed.

  Lemma L_FM : forall s1 Mc mdl1 r (m : Z) (pc : word),
    ptF s1 Mc mdl1 r -> nojunk s1 -> s_limbo s1 = m :: s_limbo st -> ~ In m (s_limbo st) ->
    getr r 9 = Z_to_bv 64 m -> getr r 22 = Z_to_bv 64 MLOCK -> getr r 10 = Z_to_bv 64 (2 ^ 64 - 1) ->
    ((pc = (0x67690%bv : word)) \/ (pc = (0x67960%bv : word) /\ getr r 18 = Z_to_bv 64 (2 ^ 64 - 1))) ->
    kat RSEGS (mkCfg (mkst r pc Mc rom) mdl1) QF.
  Proof.
    intros s1 Mc mdl1 r m pc P NJ1 EL NLm0 A9 A22 A10 Hpc.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 LM1 MU1 FR1 DF1 SK1 Q2 Q20 KB].
    pose proof stk288 as S288. pose proof stk_le as SLE. pose proof spcF_ok as F1.
    assert (Lim : In m (s_limbo s1)) by (rewrite EL; left; reflexivity).
    destruct (wG_limbo s1 L (WF_groups s1 L W1) m Lim) as (Um & NGm & NLm & NFm).
    destruct (metaU_rng s1 L W1 m Um) as (MR1 & MR2 & MR8). ceil. unfold HEAPLO in MR1.
    pose proof (meta_store_ok s1 L Mc W1 RP1 m Um) as SOKm.
    assert (Hsp' : CEIL + 144 <= sp < 2 ^ 64) by (ceil; lia).
    assert (SOKsp : store_ok RSEGS Mc (Z_to_bv 64 (sp - 136)) 40%nat = true).
    { ceil. eapply store_ok_defined; [exact DF1 | lia | cbn; lia | lia | lia]. }
    assert (Hg : HEAPLO <= m /\ m + 40 <= CEIL /\ (m + 40 <= IMG_LO \/ IMG_HI <= m)) by (unfold HEAPLO in *; lia).
    set (l := s_flist s1). set (fh := c_free_head (s_ctx s1)).
    assert (Efh : fh = head_of l) by (subst fh l; exact (wc_fhead s1 (WF_ctx s1 L W1))).
    pose proof (rc_fmh s1 Mc (rp_ctx s1 Mc RP1)) as Cfh. fold fh in Cfh.
    assert (FHr : 0 <= fh < 2 ^ 64 /\ (fh <> 0 -> l <> [] /\ In fh l)).
    { rewrite Efh. destruct l as [|a l2] eqn:El; cbn; [lia|].
      assert (Ia : In a (s_flist s1)) by (fold l; rewrite El; left; reflexivity).
      destruct (wl_fU s1 (WF_lists s1 L W1) a Ia) as (Ua & _). destruct (metaU_rng s1 L W1 a Ua). ceil; unfold HEAPLO in *.
      split; [lia|]. intros _. split; [congruence | left; reflexivity]. }
    destruct FHr as [FHr FHin].
    assert (SOKc : store_ok RSEGS Mc (Z_to_bv 64 ctx_free_meta_head) 8%nat = true).
    { eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact (ctx_store_ok s1 Mc RP1) | | ]; unfold ctx_free_meta_head, CTX; rewrite ?u_Z2bv by lia; cbn; lia. }
    (* [comment removed for export] *)
    assert (FIN : forall (r5 : bvmap 5 word) (M5 : mem),
      msteps RSEGS (mkst r pc Mc rom) (mkst r5 (0x67b10%bv : word) M5 rom) ->
      getr r5 10 = Z_to_bv 64 (2 ^ 64 - 1) -> keeps_but [10; 11; 22]%bv r r5 ->
      WF (UbMhFreeMeta.st' s1 m) L -> REP (UbMhFreeMeta.st' s1 m) M5 ->
      mem_grows Mc M5 ->
      (forall a, 0 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) ->
         (sp - 136 <= a < sp - 96) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/ (CTX <= a < CTX_END)) ->
      kat RSEGS (mkCfg (mkst r pc Mc rom) mdl1) QF).
    { intros r5 M5 RUN5 E10 K5 W5 R5 G5 WR5.
      eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN5 |].
      apply (L_F (UbMhFreeMeta.st' s1 m) M5 mdl1 r5); [| | | exact E10].
      - constructor; try assumption.
        + apply (LEDGER_same s1); [reflexivity | reflexivity | exact LG1].
        + intros x Hx. rewrite <- (LM1 x Hx). apply (UbMhFreeMeta.q_meta_offlist s1 m x).
          * intros ->. exact (NLm0 Hx).
          * intros Hin. destruct (wG_limbo s1 L (WF_groups s1 L W1) x ltac:(rewrite EL; right; exact Hx)) as (_ & _ & NLx & _). apply NLx. left. exact Hin.
        + intros a Ha NE. destruct (decide (M5 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E|NE2].
          * apply FR1; [exact Ha | congruence].
          * destruct (WR5 a Ha NE2) as [A|[A|A]]; [left; lia | right; left; exact A | right; right; left; exact A].
        + eapply defined_grows; [exact G5 | exact DF1].
        + apply (stk_transfer st regs sp sc req d Hsc Hreq Hsp Mc M5); [|exact SK1]. intros y Hy.
          destruct (decide (M5 (Z_to_bv 64 y) = Mc (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
          destruct (WR5 y ltac:(ceil; lia) NE) as [A|[A|A]]; ceil; unfold CTX_END, CTX, HEAPLO in *; lia.
        + kept_rw K5. exact Q2.
        + kept_rw K5. exact Q20.
        + eapply keeps_big; [exact KB | exact K5 | reflexivity].
      - intros x k o Hx Hk E. apply UbMhFreeMeta.e_is_group in Hx. rewrite (UbMhFreeMeta.e_glast s1 m NGm x Hx) in Hk.
        rewrite UbMhFreeMeta.e_slot in E. exact (NJ1 x k o Hx Hk E).
      - cbn [s_limbo UbMhFreeMeta.st']. change (zremove m (s_limbo s1) = s_limbo st). rewrite EL. apply zremove_head. exact NLm0. }
    (* [comment removed for export] *)
    assert (FZwr : forall a, 0 <= a < 2 ^ 64 -> m_fz Mc sp m (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) ->
                   (sp - 136 <= a < sp - 96) \/ (m <= a < m + 40)).
    { intros a Hr NE. unfold m_fz, z8' in NE. revert NE. generalize Mc. intros Mb NE. wdiff NE Mb a. }
    assert (FZg : mem_grows Mc (m_fz Mc sp m)) by (unfold m_fz; do 10 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (Z8split' : word_to_le_bytes 8 (Z_to_bv 64 0) = (word_to_le_bytes 4 (Z_to_bv 64 0) ++ word_to_le_bytes 4 (Z_to_bv 64 0))%list) by reflexivity.
    destruct (Z.eq_dec fh 0) as [Fh0|Fh0].
    - (* [comment removed for export] *)
      assert (Lnil : l = []).
      { destruct l as [|a l2] eqn:El; [reflexivity|]. exfalso.
        assert (Ia : In a (s_flist s1)) by (fold l; rewrite El; left; reflexivity).
        destruct (wl_fU s1 (WF_lists s1 L W1) a Ia) as (Ua & _). destruct (metaU_rng s1 L W1 a Ua).
        rewrite Efh in Fh0. cbn in Fh0. unfold HEAPLO in *. lia. }
      assert (Qnil : UbMhFreeMeta.q_nil s1 = true) by (unfold UbMhFreeMeta.q_nil; fold l; rewrite Lnil; reflexivity).
      assert (RUNX : exists r5, msteps RSEGS (mkst r pc Mc rom) (mkst r5 (0x67b10%bv : word) (m_fe Mc sp m) rom)
                                /\ getr r5 10 = Z_to_bv 64 (2 ^ 64 - 1) /\ keeps_but [10; 11; 22]%bv r r5).
      { destruct Hpc as [-> | [-> A18]].
        - destruct (tG3e Mc sp m fh Hsp' Hg SOKsp SOKm Cfh SOKc r rom A10 A9 Q2 A22 Fh0) as (r5 & RUN5 & E10 & K5).
          exists r5. split; [exact RUN5|]. split; [exact E10 | exact K5].
        - destruct (tG2e Mc sp m fh Hsp' Hg SOKsp SOKm Cfh SOKc r rom A10 A18 A9 Q2 A22 Fh0) as (r5 & RUN5 & E10 & K5).
          exists r5. split; [exact RUN5|]. split; [exact E10|]. eapply keeps_but_mono; [exact K5|]. intros x Hx. apply in_regs_dec.
          cbn in Hx. destruct Hx as [<-|[<-|[]]]; reflexivity. }
      destruct RUNX as (r5 & RUN5 & E10 & K5).
      set (M5 := m_fe Mc sp m) in RUN5.
      assert (W5 : forall a, 0 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) ->
                  (sp - 136 <= a < sp - 96) \/ (m <= a < m + 40) \/ (ctx_free_meta_head <= a < ctx_free_meta_head + 8)).
      { intros a Hr NE. unfold M5, m_fe, ctx_free_meta_head, CTX in NE. unfold ctx_free_meta_head, CTX.
        destruct (decide (m_fz Mc sp m (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E0|NE0].
        - rewrite <- E0 in NE. revert NE. generalize (m_fz Mc sp m). intros Mb NE. wdiff NE Mb a.
        - destruct (FZwr a Hr NE0); lia. }
      assert (G5 : mem_grows Mc M5) by (unfold M5, m_fe; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); exact FZg).
      destruct (freemeta_close s1 L Mc M5 m spc W1 RP1 Um NGm NLm NFm F1) as [WF5 REP5].
      { intros a Hr NE. unfold UbMhFreeMeta.q_wr. rewrite Qnil. unfold UbMhASlotKA.spc, MSTK.
        destruct (W5 a Hr NE) as [A|[A|A]]; [left; lia | right; left; exact A | right; right; right; split; [reflexivity | exact A]]. }
      { exact G5. }
      { unfold cell, M5, m_fe, ctx_free_meta_head, CTX, UbMhFreeMeta.q_prev. rewrite Z.eqb_refl, Qnil. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fe, ctx_free_meta_head, CTX, UbMhFreeMeta.q_next. rewrite Z.eqb_refl, Qnil. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 3 rdn_peel1. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 5 rdn_peel1. rewrite Z8split' , wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia). rdn_peel1.
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 5 rdn_peel1. rewrite Z8split', wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia).
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fe, m_fz, z8', ctx_free_meta_head, CTX. do 6 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros X. rewrite Qnil in X. discriminate X. }
      { intros X. rewrite Qnil in X. discriminate X. }
      { intros _. unfold cell, M5, m_fe, ctx_free_meta_head, CTX. apply rdn_wbytes_hit8. zsimp; lia. }
      apply (FIN r5 M5 RUN5 E10 K5 WF5 REP5 G5).
      intros a Hr NE. destruct (W5 a Hr NE) as [A|[A|A]].
      + left. exact A.
      + right; left. exact (meta_fr s1 m a W1 Um A).
      + right; right. unfold ctx_free_meta_head, CTX_END, CTX in *. lia.
    - (* [comment removed for export] *)
      destruct (FHin Fh0) as [Lnn Ifh].
      assert (Qnil : UbMhFreeMeta.q_nil s1 = false) by (unfold UbMhFreeMeta.q_nil; fold l; apply is_nilb_false; exact Lnn).
      set (ft := znth l (zlen l - 1)).
      pose proof (wl_fdll s1 (WF_lists s1 L W1)) as Dl. fold l in Dl.
      destruct (dllf_ends _ _ _ (proj1 (dll_dllf s1 _) Dl) (zlen_pos _ Lnn)) as [Nft Pfh].
      rewrite <- (head_of_znth _ Lnn), <- Efh in Nft, Pfh. fold ft in Nft, Pfh.
      assert (Ift : In ft l) by (subst ft; apply last_In; exact Lnn).
      destruct (wl_fU s1 (WF_lists s1 L W1) fh Ifh) as (Ufh & NGfh & _). destruct (wl_fU s1 (WF_lists s1 L W1) ft Ift) as (Uft & NGft & _).
      assert (Nhm : fh <> m) by (intros E; apply NLm; left; fold l; rewrite <- E; exact Ifh).
      assert (Ntm : ft <> m) by (intros E; apply NLm; left; fold l; rewrite <- E; exact Ift).
      destruct (metaU_rng s1 L W1 fh Ufh) as (Fh1 & Fh2 & _). destruct (metaU_rng s1 L W1 ft Uft) as (Ft1 & Ft2 & _).
      pose proof (metaU_sep s1 L W1 m fh Um Ufh (fun E => Nhm (eq_sym E))) as SEPh.
      pose proof (metaU_sep s1 L W1 m ft Um Uft (fun E => Ntm (eq_sym E))) as SEPt.
      assert (HT : fh = ft \/ fh + 40 <= ft \/ ft + 40 <= fh).
      { destruct (Z.eq_dec fh ft) as [E|NE]; [left; exact E | right; exact (metaU_sep s1 L W1 fh ft Ufh Uft NE)]. }
      unfold HEAPLO in Fh1, Fh2, Ft1, Ft2.
      destruct (meta_cells s1 L Mc W1 RP1 fh Ufh) as (arh & kh & _ & _ & _ & _ & _ & _ & RMh & _).
      pose proof (rm_prev _ _ _ RMh) as Chd0. rewrite Pfh in Chd0. unfold cell in Chd0.
      pose proof (meta_store_ok s1 L Mc W1 RP1 fh Ufh) as SOKh40. pose proof (meta_store_ok s1 L Mc W1 RP1 ft Uft) as SOKt40.
      assert (SOKh : store_ok RSEGS Mc (Z_to_bv 64 fh) 8%nat = true).
      { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKh40 | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
      assert (SOKt : store_ok RSEGS Mc (Z_to_bv 64 (ft + 8)) 8%nat = true).
      { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKt40 | | ]; rewrite ?u_Z2bv by lia; cbn; lia. }
      assert (RUNX : exists r5, msteps RSEGS (mkst r pc Mc rom) (mkst r5 (0x67b10%bv : word) (m_fq Mc sp m fh ft) rom)
                                /\ getr r5 10 = Z_to_bv 64 (2 ^ 64 - 1) /\ keeps_but [10; 11; 22]%bv r r5).
      { destruct Hpc as [-> | [-> A18]].
        - destruct (tG3q Mc sp m fh ft Hsp' Hg FHr ltac:(lia) SOKsp SOKm Cfh r rom
                      ltac:(unfold HEAPLO; lia) ltac:(lia) ltac:(unfold HEAPLO; lia) ltac:(lia) SEPh SEPt Chd0 SOKh SOKt A10 A9 Q2 A22 Fh0)
            as (r5 & RUN5 & E10 & K5).
          exists r5. split; [exact RUN5|]. split; [exact E10 | exact K5].
        - destruct (tG2q Mc sp m fh ft Hsp' Hg FHr ltac:(lia) SOKsp SOKm Cfh r rom
                      ltac:(unfold HEAPLO; lia) ltac:(lia) ltac:(unfold HEAPLO; lia) ltac:(lia) SEPh SEPt Chd0 SOKh SOKt A10 A18 A9 Q2 A22 Fh0)
            as (r5 & RUN5 & E10 & K5).
          exists r5. split; [exact RUN5|]. split; [exact E10|]. eapply keeps_but_mono; [exact K5|]. intros x Hx. apply in_regs_dec.
          cbn in Hx. destruct Hx as [<-|[<-|[]]]; reflexivity. }
      destruct RUNX as (r5 & RUN5 & E10 & K5).
      set (M5 := m_fq Mc sp m fh ft) in RUN5.
      assert (W5 : forall a, 0 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) ->
                  (sp - 136 <= a < sp - 96) \/ (m <= a < m + 40) \/ (ft + 8 <= a < ft + 16) \/ (fh <= a < fh + 8)).
      { intros a Hr NE. unfold M5, m_fq in NE.
        destruct (decide (m_fz Mc sp m (Z_to_bv 64 a) = Mc (Z_to_bv 64 a))) as [E0|NE0].
        - rewrite <- E0 in NE. revert NE. generalize (m_fz Mc sp m). intros Mb NE. wdiff NE Mb a.
        - destruct (FZwr a Hr NE0); lia. }
      assert (G5 : mem_grows Mc M5) by (unfold M5, m_fq; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact FZg).
      assert (Etl : znth (s_flist s1) (zlen (s_flist s1) - 1) = ft) by reflexivity.
      assert (Efh2 : head_of (s_flist s1) = fh) by (symmetry; exact Efh).
      destruct (freemeta_close s1 L Mc M5 m spc W1 RP1 Um NGm NLm NFm F1) as [WF5 REP5].
      { intros a Hr NE. unfold UbMhFreeMeta.q_wr. rewrite Qnil, Etl, Efh2. unfold UbMhASlotKA.spc, MSTK.
        destruct (W5 a Hr NE) as [A|[A|[A|A]]]; [left; lia | right; left; exact A | right; right; left; split; [reflexivity | left; exact A] | right; right; left; split; [reflexivity | right; exact A]]. }
      { exact G5. }
      { unfold cell, M5, m_fq, UbMhFreeMeta.q_prev. rewrite Z.eqb_refl, Qnil, Etl. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fq, UbMhFreeMeta.q_next. rewrite Z.eqb_refl, Qnil, Efh2. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 4 rdn_peel1. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 6 rdn_peel1. rewrite Z8split' , wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia). rdn_peel1.
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 6 rdn_peel1. rewrite Z8split', wbytes_app. unfold at_. rewrite length_N_to_le_bytes, u_Z2bv by lia.
        replace (m + 24 + Z.of_nat 4) with (m + 28) by (cbn; lia).
        pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 0))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      { unfold cell, M5, m_fq, m_fz, z8'. do 7 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros _. rewrite Etl. unfold cell, M5, m_fq. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros _. rewrite Efh2. unfold cell, M5, m_fq. apply rdn_wbytes_hit8. zsimp; lia. }
      { intros X. rewrite Qnil in X. discriminate X. }
      apply (FIN r5 M5 RUN5 E10 K5 WF5 REP5 G5).
      intros a Hr NE. destruct (W5 a Hr NE) as [A|[A|[A|A]]].
      + left. exact A.
      + right; left. exact (meta_fr s1 m a W1 Um A).
      + right; left. apply (meta_fr s1 ft a W1 Uft). lia.
      + right; left. apply (meta_fr s1 fh a W1 Ufh). lia.
  Qed.
End ASF.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MemHelp2.
  Context {fx : FPState}.


  (* [comment removed for export] *)
  Lemma wbytes_outZ : forall (Mb : mem) b bs a, 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
    ~ (b <= a < b + Z.of_nat (length bs)) -> wbytes Mb (Z_to_bv 64 b) bs (Z_to_bv 64 a) = Mb (Z_to_bv 64 a).
  Proof.
    intros Mb b bs a Hb Hbl Ha Hout. destruct (decide (wbytes Mb (Z_to_bv 64 b) bs (Z_to_bv 64 a) = Mb (Z_to_bv 64 a))) as [E|NE]; [exact E|].
    exfalso. apply Hout. exact (wbytes_diff_g Mb b bs a Hb Hbl Ha NE).
  Qed.

  Lemma zfill_diffZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
    zfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) <> Mb (Z_to_bv 64 x) -> a <= x < a + n.
  Proof.
    intros Mb a n x Ha Hn Han Hx NE. destruct (decide (a <= x < a + n)) as [IN|OUT]; [exact IN|]. exfalso. apply NE.
    apply zfill_out. rewrite !u_Z2bv by lia. lia.
  Qed.
  Lemma zfill_inZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> a <= x < a + n ->
    zfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros Mb a n x Ha Hn Han Hx. unfold zfill, zmem. rewrite !u_Z2bv by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  Qed.
  Lemma zfill_grows : forall (a n : word) (Mb : mem), mem_grows Mb (zfill a n Mb).
  Proof. intros a n Mb x Hx. unfold zfill, zmem. destruct (_ && _)%bool; [discriminate | exact Hx]. Qed.
  Lemma unfill_diffZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
    unfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) <> Mb (Z_to_bv 64 x) -> a <= x < a + n.
  Proof.
    intros Mb a n x Ha Hn Han Hx NE. destruct (decide (a <= x < a + n)) as [IN|OUT]; [exact IN|]. exfalso. apply NE.
    apply unfill_out. rewrite !u_Z2bv by lia. lia.
  Qed.
  Lemma unfill_outZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> ~ (a <= x < a + n) ->
    unfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) = Mb (Z_to_bv 64 x).
  Proof. intros Mb a n x Ha Hn Han Hx OUT. apply unfill_out. rewrite !u_Z2bv by lia. lia. Qed.
  Lemma rdn_zfill_outZ : forall (Mb : mem) a n x k, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
    (x + Z.of_nat k <= a \/ a + n <= x) ->
    rdn RSEGS (zfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb) (Z_to_bv 64 x) k = rdn RSEGS Mb (Z_to_bv 64 x) k.
  Proof.
    intros Mb a n x k Ha Hn Han Hx Hk D. destruct k as [|k']; [reflexivity|].
    apply rdn_zfill_out; rewrite !u_Z2bv by lia; lia.
  Qed.
  Lemma rdn_unfill_outZ : forall (Mb : mem) a n x k, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
    (x + Z.of_nat k <= a \/ a + n <= x) ->
    rdn RSEGS (unfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb) (Z_to_bv 64 x) k = rdn RSEGS Mb (Z_to_bv 64 x) k.
  Proof.
    intros Mb a n x k Ha Hn Han Hx Hk D. destruct k as [|k']; [reflexivity|].
    apply rdn_unfill_out; rewrite !u_Z2bv by lia; lia.
  Qed.
End MemHelp2.

(* [comment removed for export] *)
Lemma wbytes_inside_some : forall bs (m : word -> option byte) (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + Z.of_nat (length bs))%Z ->
  wbytes m addr bs x <> None.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hx; cbn [wbytes length] in *; [lia|].
  destruct rest as [|b' rest'].
  - cbn [wbytes length] in *. replace (bv_eqb x addr) with true; [discriminate|].
    symmetry. unfold bv_eqb. apply Z.eqb_eq. lia.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z) by (apply u_add1; cbn [length] in Hnw; lia).
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned addr)) as [E|NE].
    + rewrite wbytes_below; [| rewrite Hu1; cbn [length] in *; lia | rewrite Hu1; lia].
      cbv beta. replace (bv_eqb x addr) with true; [discriminate|]. symmetry. unfold bv_eqb. apply Z.eqb_eq. exact E.
    + apply IH; [rewrite Hu1; cbn [length] in *; lia | rewrite Hu1; cbn [length] in *; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MmapNode.
  Context {fx : FPState}.
  Variables (F : kfam) (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (w : bv 32) (len : Z).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypotheses (Hh : m_halted model = None) (Hl : m_vm_lazy model = []).
  Hypotheses (HF : fetch_word RSEGS pc = Some w) (HE : is_ecall w = true).
  Hypotheses (H17 : getr regs 17 = Z_to_bv 64 222)
             (H11 : getr regs 11 = Z_to_bv 64 len) (Hlen : 0 < len < 2 ^ 64)
             (H12 : getr regs 12 = Z_to_bv 64 3) (H13 : getr regs 13 = Z_to_bv 64 34)
             (H14 : getr regs 14 = Z_to_bv 64 (-1)) (H15 : getr regs 15 = Z_to_bv 64 0).

  Lemma as_kfx_mmap_rw : forall (bi b : bool),
    (exists a, grant_ok (getr regs 10) model a (page_round_up_Z len) = true) ->
    Kf F (mmrw_fail regs pc mem rom model ENOMEM) ->
    (forall a, grant_ok (getr regs 10) model a (page_round_up_Z len) = true -> kfx F bi (mmrw_grant regs pc mem rom model len a)) ->
    kfx F b (mkCfg (mkst regs pc mem rom) model).
  Proof.
    (* [comment removed for export] *)
    intros bi b [a0 Ha0] _ Hg.
    apply (kfx_closed RSEGS F HL b _ unit tt _ (node_sys RSEGS regs pc mem rom model w Hh Hl HF HE)). intros [].
    apply (kfx_grant_node RSEGS F HL bi b _ _ (exist _ a0 Ha0) _
             (node_mmap_rw_grant RSEGS regs pc mem rom model len Hh Hl H17 H11 Hlen H12 H13 H14 H15
                (grant_ok_not_refusable (Z_to_bv 64 34) _ _ _ _ Ha0))).
    intros [a Ha]. exact (Hg a Ha).
  Qed.
End MmapNode.
