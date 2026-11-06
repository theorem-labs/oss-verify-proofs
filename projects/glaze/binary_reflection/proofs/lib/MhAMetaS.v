(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhAMetaW.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1.
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

Ltac sok B SOK := store_ok_peel; eapply (store_ok_sub _ _ _ _ B); [ | exact SOK | | ]; zsimp; lia.

Lemma land_4095_l : forall x, (0 <= x)%Z -> Z.land 4095 x = (x mod 4096)%Z.
Proof. intros x Hx. rewrite Z.land_comm. change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma negmask_aligned : forall B, (0 <= B < 2^64)%Z -> (B mod 4096 = 0)%Z ->
  Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 - B))) = 0%Z.
Proof.
  intros B HB Hal. rewrite land_4095_l by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (0 - B))); lia).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite <- (Znumtheory.Zmod_div_mod 4096 (2^64) (0 - B)); [| lia | lia | exists (2^52)%Z; reflexivity].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section A.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp can : Z).
  Hypothesis Hsp : (CEIL + 64 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 64)) 64%nat = true.
  Hypothesis M_got : rdn RSEGS m (Z_to_bv 64 A_GOT_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY)).
  Hypothesis M_can : rdn RSEGS m (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_init : rdn RSEGS m (Z_to_bv 64 ctx_init_done) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Hypothesis M_pg : rdn RSEGS m (Z_to_bv 64 A_PAGESIZE) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).

  Definition am_frame (ra s0 s1 s2 s3 s4 : word) : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 can)).

  Definition clobA : list reg := [2; 8; 9; 10; 11; 18; 19; 20]%bv.

  Lemma amA : forall regs rom,
    getr regs 2 = Z_to_bv 64 sp ->
    exists regs',
      msteps RSEGS (mkst regs (0x625f8 : word) m rom)
                   (mkst regs' (0x626ac : word) (am_frame (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 19 = Z_to_bv 64 MLOCK /\ getr regs' 8 = Z_to_bv 64 4096
      /\ getr regs' 18 = Z_to_bv 64 A_CANARY
      /\ keeps_but clobA regs regs'.
  Proof using M_pg M_init M_can M_got SOK Hsp RN.
    intros regs rom H2. ceil; unfold A_GOT_CANARY, A_CANARY, ctx_init_done, CTX, A_PAGESIZE, MLOCK in *.
    eexists. split.
    - stepn F_625a4 D_625a4. rewrite H2. addi_renorm.
      stepSTx F_625a8 D_625a8 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(sok 64%nat SOK).
      stepSTx F_625ac D_625ac (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok 64%nat SOK).
      stepSTx F_625b0 D_625b0 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok 64%nat SOK).
      stepSTx F_625b4 D_625b4 (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok 64%nat SOK).
      stepSTx F_625b8 D_625b8 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok 64%nat SOK).
      stepSTx F_625bc D_625bc (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(sok 64%nat SOK).
      stepn F_625c0 D_625c0.
      stepLD8 F_625c4 D_625c4 (Z_to_bv 64 681872).
      stepLD8 F_625c8 D_625c8 (Z_to_bv 64 can).
      stepn F_625cc D_625cc.
      stepSTx F_625d0 D_625d0 (Z_to_bv 64 (sp - 56)) (Z_to_bv 64 can) ltac:(sok 64%nat SOK).
      stepn F_625d4 D_625d4.
      stepLD F_625d8 D_625d8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      vals_lit.
      stepn F_625dc D_625dc.
      stepn F_625e0 D_625e0.
      stepb_tk F_625e4 D_625e4 ltac:(cond_compute).
      stepLD8 F_62648 D_62648 (Z_to_bv 64 4096).
      stepn F_6264c D_6264c.
      stepb_ft F_62650 D_62650 ltac:(cond_compute).
      stepn F_62654 D_62654.
      unfold am_frame. pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp can g : Z) (ra s0v s1v s2v s3v s4v : word).
  Hypothesis Hsp : (CEIL + 64 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hra : ret_ok ra.
  Hypothesis SOKg : store_ok RSEGS m (Z_to_bv 64 g) 16%nat = true.
  Hypothesis M_can : rdn RSEGS m (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_c56 : rdn RSEGS m (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).
  Hypothesis M_s4 : rdn RSEGS m (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 s4v).

  Definition m_E : mem :=
    wbytes (wbytes m (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition clobE : list reg := [1; 2; 8; 9; 11; 12; 18; 19; 20]%bv.

  Lemma amE : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 g -> getr regs 18 = Z_to_bv 64 A_CANARY ->
    exists regs',
      msteps RSEGS (mkst regs (0x6286c : word) m rom) (mkst regs' ra m_E rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but clobE regs regs'.
  Proof using M_s4 M_s3 M_s2 M_s1 M_s0 M_ra M_c56 M_can SOKg Hra Hg Hsp can RN.
    intros regs rom H2 H10 H18. ceil; unfold HEAPLO, A_CANARY in *. unfold m_E.
    eexists. split.
    - stepSTx F_62818 D_62818 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 0) ltac:(sok 16%nat SOKg).
      stepSTx F_6281c D_6281c (Z_to_bv 64 g) (Z_to_bv 64 0) ltac:(sok 16%nat SOKg).
      stepLD8 F_62820 D_62820 (Z_to_bv 64 can).
      stepLD8 F_62824 D_62824 (Z_to_bv 64 can).
      stepb_ft F_62828 D_62828 ltac:(apply c_eq_refl || (rewrite c_eq_Z by lia; apply Z.eqb_refl)).
      stepLD8 F_6282c D_6282c ra.
      stepLD8 F_62830 D_62830 s0v.
      stepLD8 F_62834 D_62834 s1v.
      stepLD8 F_62838 D_62838 s2v.
      stepLD8 F_6283c D_6283c s3v.
      stepLD8 F_62840 D_62840 s4v.
      stepn F_62844 D_62844. rewrite H2. addi_renorm.
      stepret F_62848 D_62848 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End E.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section F.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (fh nx pv : Z).
  Hypothesis Hfh : (HEAPLO <= fh)%Z /\ (fh + 40 <= CEIL)%Z /\ ((fh + 40 <= IMG_LO)%Z \/ (IMG_HI <= fh)%Z).
  Hypothesis Hnz : fh <> 0%Z.
  Hypothesis M_fh : rdn RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fh)).
  Hypothesis M_nx : rdn RSEGS m (Z_to_bv 64 (fh + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 nx)).
  Hypothesis M_pv : rdn RSEGS m (Z_to_bv 64 fh) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pv)).
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = true.

  (* [comment removed for export] *)
  Definition m_F1 : mem := wbytes m (Z_to_bv 64 ctx_free_meta_head) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma amF1 : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> nx = fh ->
    exists regs',
      msteps RSEGS (mkst regs (0x626ac : word) m rom) (mkst regs' (0x6286c : word) m_F1 rom)
      /\ getr regs' 10 = Z_to_bv 64 fh /\ keeps_but [10; 11]%bv regs regs'.
  Proof using SOKc M_nx M_fh Hnz Hfh RN.
    intros regs rom H19 Enx. ceil; unfold HEAPLO, ctx_free_meta_head, CTX, MLOCK in *. unfold m_F1, ctx_free_meta_head, CTX.
    eexists. split.
    - stepLD8 F_62658 D_62658 (Z_to_bv 64 fh).
      stepb_ft F_6265c D_6265c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepLD8 F_62660 D_62660 (Z_to_bv 64 nx).
      stepb_tk F_62664 D_62664 ltac:(rewrite Enx; apply c_eq_refl).
      stepSTx F_626a4 D_626a4 (Z_to_bv 64 682040) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKc).
      stepn F_626a8 D_626a8.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Definition m_F2 : mem :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (pv + 8)) (word_to_le_bytes 8 (Z_to_bv 64 nx)))
      (Z_to_bv 64 nx) (word_to_le_bytes 8 (Z_to_bv 64 pv)))
      (Z_to_bv 64 ctx_free_meta_head) (word_to_le_bytes 8 (Z_to_bv 64 nx)).

  Lemma amF2 : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> nx <> fh ->
    (HEAPLO <= nx)%Z -> (nx + 40 <= CEIL)%Z -> (HEAPLO <= pv)%Z -> (pv + 40 <= CEIL)%Z ->
    ((nx + 40 <= IMG_LO)%Z \/ (IMG_HI <= nx)%Z) -> ((pv + 40 <= IMG_LO)%Z \/ (IMG_HI <= pv)%Z) ->
    (fh + 40 <= nx \/ nx + 40 <= fh)%Z -> (fh + 40 <= pv \/ pv + 40 <= fh)%Z -> (nx = pv \/ nx + 40 <= pv \/ pv + 40 <= nx)%Z ->
    store_ok RSEGS m (Z_to_bv 64 (pv + 8)) 8%nat = true -> store_ok RSEGS m (Z_to_bv 64 nx) 8%nat = true ->
    exists regs',
      msteps RSEGS (mkst regs (0x626ac : word) m rom) (mkst regs' (0x6286c : word) m_F2 rom)
      /\ getr regs' 10 = Z_to_bv 64 fh /\ keeps_but [10; 11; 12]%bv regs regs'.
  Proof using SOKc M_pv M_nx M_fh Hnz Hfh.
    intros regs rom H19 Hne Hn1 Hn2 Hp1 Hp2 In Ip Dfn Dfp Dnp SOKp SOKn.
    ceil; unfold HEAPLO, ctx_free_meta_head, CTX, MLOCK in *. unfold m_F2, ctx_free_meta_head, CTX.
    eexists. split.
    - stepLD8 F_62658 D_62658 (Z_to_bv 64 fh).
      stepb_ft F_6265c D_6265c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepLD8 F_62660 D_62660 (Z_to_bv 64 nx).
      stepb_ft F_62664 D_62664 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hne).
      stepLD8 F_62668 D_62668 (Z_to_bv 64 pv).
      stepSTx F_6266c D_6266c (Z_to_bv 64 (pv + 8)) (Z_to_bv 64 nx) ltac:(store_ok_peel; exact SOKp).
      stepLD8 F_62670 D_62670 (Z_to_bv 64 pv).
      stepLD8 F_62674 D_62674 (Z_to_bv 64 nx).
      stepSTx F_62678 D_62678 (Z_to_bv 64 nx) (Z_to_bv 64 pv) ltac:(store_ok_peel; exact SOKn).
      stepLD8 F_6267c D_6267c (Z_to_bv 64 fh).
      stepb_ft F_62680 D_62680 ltac:(apply c_eq_refl || (rewrite c_eq_Z by lia; apply Z.eqb_refl)).
      stepLD8 F_62684 D_62684 (Z_to_bv 64 nx).
      stepSTx F_62688 D_62688 (Z_to_bv 64 682040) (Z_to_bv 64 nx) ltac:(store_ok_peel; exact SOKc).
      stepn F_6268c D_6268c.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End F.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section R.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (am cnt : Z).
  Hypothesis Ham : (0 <= am)%Z /\ (am + 40 < 2^64)%Z.
  Hypothesis Hcnt : (0 < cnt < 2^64)%Z.
  Hypothesis M_fh : rdn RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis M_cnt : rdn RSEGS m (Z_to_bv 64 ctx_avail_meta_count) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 cnt)).
  Hypothesis M_am : rdn RSEGS m (Z_to_bv 64 ctx_avail_meta) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 am)).
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.

  Definition m_R : mem :=
    wbytes (wbytes m (Z_to_bv 64 ctx_avail_meta) (word_to_le_bytes 8 (Z_to_bv 64 (am + 40))))
      (Z_to_bv 64 ctx_avail_meta_count) (word_to_le_bytes 8 (Z_to_bv 64 (cnt - 1))).

  Lemma amR : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK ->
    exists regs',
      msteps RSEGS (mkst regs (0x626ac : word) m rom) (mkst regs' (0x6286c : word) m_R rom)
      /\ getr regs' 10 = Z_to_bv 64 am /\ keeps_but [10; 11; 12]%bv regs regs'.
  Proof using SOKc M_am M_cnt M_fh Hcnt Ham.
    intros regs rom H19. unfold ctx_free_meta_head, ctx_avail_meta_count, ctx_avail_meta, CTX, MLOCK in *. unfold m_R, ctx_avail_meta_count, ctx_avail_meta, CTX.
    eexists. split.
    - stepLD8 F_62658 D_62658 (Z_to_bv 64 0).
      stepb_tk F_6265c D_6265c ltac:(apply c_eq_refl).
      stepLD8 F_62690 D_62690 (Z_to_bv 64 cnt).
      stepb_ft F_62694 D_62694 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepLD8 F_62698 D_62698 (Z_to_bv 64 am).
      stepn F_6269c D_6269c. addi_renorm.
      stepn F_626a0 D_626a0.
      stepn F_6280c D_6280c. addi_renorm.
      stepSTx F_62810 D_62810 (Z_to_bv 64 682048) (Z_to_bv 64 (am + 40)) ltac:(sok 928%nat SOKc).
      stepSTx F_62814 D_62814 (Z_to_bv 64 682056) (Z_to_bv 64 (cnt - 1)) ltac:(sok 928%nat SOKc).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End R.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NewArea.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem).
  Hypothesis M_fh : rdn RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis M_cnt : rdn RSEGS m (Z_to_bv 64 ctx_avail_meta_count) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Variables (ac brk cur : Z).
  Hypothesis Hac : (0 <= ac < 2^63)%Z.
  Hypothesis Hbrk : (0 <= brk < 2^64)%Z.
  Hypothesis Hcur : (0 <= cur < 2^64)%Z.
  Hypothesis M_ac : rdn RSEGS m (Z_to_bv 64 ctx_avail_meta_area_count) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ac)).
  Hypothesis M_brk : rdn RSEGS m (Z_to_bv 64 ctx_brk) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 brk)).
  Hypothesis M_cur : rdn RSEGS m (Z_to_bv 64 ctx_avail_meta_areas) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 cur)).
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.

  Ltac pre := ceil; unfold HEAPLO, ctx_free_meta_head, ctx_avail_meta_count, ctx_avail_meta, ctx_avail_meta_area_count, ctx_brk,
                ctx_avail_meta_areas, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail, ctx_secret, CTX, MLOCK in *.
  Ltac head19 :=
    stepLD8 F_62658 D_62658 (Z_to_bv 64 0);
    stepb_tk F_6265c D_6265c ltac:(apply c_eq_refl);
    stepLD8 F_62690 D_62690 (Z_to_bv 64 0);
    stepb_tk F_62694 D_62694 ltac:(apply c_eq_refl);
    stepLD8 F_626ac D_626ac (Z_to_bv 64 ac).

  (* [comment removed for export] *)
  Lemma amC1a : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 -> ac <> 0%Z -> (cur mod 4096 = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x626ac : word) m rom) (mkst regs' (0x63d64 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cur /\ getr regs' 11 = Z_to_bv 64 4096 /\ getr regs' 12 = Z_to_bv 64 3
      /\ getr regs' 9 = Z_to_bv 64 cur /\ getr regs' 1 = Z_to_bv 64 0x628b0
      /\ keeps_but [1; 9; 10; 11; 12]%bv regs regs'.
  Proof using M_cur M_ac Hcur Hac M_cnt M_fh RN.
    intros regs rom H19 H8 Hnz Hal. pre.
    eexists. split.
    - head19.
      stepb_tk F_626b0 D_626b0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepb_ft F_62750 D_62750 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepLD8 F_62754 D_62754 (Z_to_bv 64 cur).
      stepn F_62758 D_62758.
      stepn F_627b0 D_627b0. rewrite H8. addi_renorm.
      stepn F_627b4 D_627b4. rewrite v_and_Z by lia. rewrite land_4095_l, Hal by lia.
      stepb_tk F_627b8 D_627b8 ltac:(apply c_eq_refl).
      stepn F_6284c D_6284c.
      stepn F_62850 D_62850.
      stepn F_62854 D_62854. rewrite H8.
      stepn F_62858 D_62858.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amC1b : forall regs rom (m' : mem),
    getr regs 10 = Z_to_bv 64 0 ->
    msteps RSEGS (mkst regs (0x628b0 : word) m' rom) (mkst regs (0x62810 : word) m' rom).
  Proof using.
    intros regs rom m' H10.
    stepb_tk F_6285c D_6285c ltac:(rewrite H10; cond_compute).
    pu_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma amB0 : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 -> ac = 0%Z -> brk = 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x626ac : word) m rom) (mkst regs' (0x6273c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 17 = Z_to_bv 64 214 /\ getr regs' 11 = Z_to_bv 64 4095
      /\ keeps_but [9; 10; 11; 17]%bv regs regs'.
  Proof using M_brk M_ac M_cnt M_fh RN.
    intros regs rom H19 H8 Hac0 Hb0. pre.
    eexists. split.
    - head19.
      stepb_ft F_626b0 D_626b0 ltac:(rewrite Hac0; cond_compute).
      stepLD8 F_626b4 D_626b4 (Z_to_bv 64 brk).
      stepn F_626b8 D_626b8.
      stepb_ft F_626bc D_626bc ltac:(rewrite Hb0; cond_compute).
      stepb_tk F_626c0 D_626c0 ltac:(rewrite Hb0; cond_compute).
      stepn F_626dc D_626dc.
      stepn F_626e0 D_626e0.
      stepn F_626e4 D_626e4. rewrite H8. vals_lit.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amB1 : forall regs rom (B : Z),
    (HEAPLO <= B)%Z -> (B + 8192 <= CEIL)%Z -> (B mod 4096 = 0)%Z ->
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 -> getr regs 10 = Z_to_bv 64 B -> getr regs 11 = Z_to_bv 64 4095 ->
    exists regs',
      msteps RSEGS (mkst regs (0x62740 : word) m rom)
                   (mkst regs' (0x62760 : word) (wbytes m (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 B))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (B + 8192) /\ getr regs' 9 = Z_to_bv 64 (B + 8192) /\ getr regs' 17 = Z_to_bv 64 214
      /\ keeps_but [9; 10; 11; 12; 17]%bv regs regs'.
  Proof using SOKc.
    intros regs rom B HB1 HB2 HBal H19 H8 H10 H11. pre. unfold ctx_brk, CTX.
    eexists. split.
    - stepn F_626ec D_626ec. rewrite H10.
      stepn F_626f0 D_626f0. rewrite H11.
      replace (v_and (Z_to_bv 64 4095) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 B))) with (Z_to_bv 64 0).
      2:{ unfold v_and, v_sub. rewrite (u_Z2bv 4095), (u_Z2bv 0), (u_Z2bv B) by lia. rewrite negmask_aligned by lia. reflexivity. }
      stepn F_626f4 D_626f4. rewrite H8. vals_lit.
      stepn F_626f8 D_626f8. try rewrite H10.
      stepSTx F_626fc D_626fc (Z_to_bv 64 682944) (Z_to_bv 64 B) ltac:(sok 928%nat SOKc).
      stepn F_62700 D_62700. rewrite v_add_ZZ by lia.
      stepn F_62704 D_62704.
      stepn F_62708 D_62708.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amB4 : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 -> ac = 0%Z -> brk <> 0%Z -> (brk <> 2^64 - 1)%Z -> (brk + 4096 < 2^64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x626ac : word) m rom) (mkst regs' (0x62724 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (brk + 4096) /\ getr regs' 9 = Z_to_bv 64 (brk + 4096) /\ getr regs' 17 = Z_to_bv 64 214
      /\ keeps_but [9; 10; 11; 17]%bv regs regs'.
  Proof using M_brk M_ac Hbrk M_cnt M_fh RN.
    intros regs rom H19 H8 Hac0 Hnz Hnm1 Hnw. pre.
    eexists. split.
    - head19.
      stepb_ft F_626b0 D_626b0 ltac:(rewrite Hac0; cond_compute).
      stepLD8 F_626b4 D_626b4 (Z_to_bv 64 brk).
      stepn F_626b8 D_626b8.
      stepb_ft F_626bc D_626bc ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnm1).
      stepb_ft F_626c0 D_626c0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepn F_626c4 D_626c4. rewrite H8. rewrite v_add_ZZ by lia.
      stepn F_626c8 D_626c8.
      stepn F_626cc D_626cc.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amB5g : forall regs rom (m' : mem) (nw : Z),
    (0 <= nw < 2^64)%Z -> getr regs 10 = Z_to_bv 64 nw -> getr regs 9 = Z_to_bv 64 nw ->
    msteps RSEGS (mkst regs (0x62728 : word) m' rom) (mkst regs (0x62784 : word) m' rom).
  Proof using.
    intros regs rom m' nw Hnw H10 H9.
    stepb_tk F_626d4 D_626d4 ltac:(rewrite H10, H9; apply c_eq_refl).
    pu_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma amB5r : forall regs rom (m' : mem) (nw r : Z),
    (0 <= nw < 2^64)%Z -> (0 <= r < 2^64)%Z -> r <> nw -> getr regs 10 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 nw ->
    msteps RSEGS (mkst regs (0x62728 : word) m' rom) (mkst regs (0x62798 : word) m' rom).
  Proof using.
    intros regs rom m' nw r Hnw Hr Hne H10 H9.
    stepb_ft F_626d4 D_626d4 ltac:(rewrite H10, H9, c_eq_Z by lia; apply Z.eqb_neq; exact Hne).
    stepn F_626d8 D_626d8.
    pu_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma amB2g : forall regs rom (m' : mem) (nw B : Z),
    (0 <= nw < 2^64)%Z -> getr regs 10 = Z_to_bv 64 nw -> getr regs 9 = Z_to_bv 64 nw ->
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 ->
    rdn RSEGS m' (Z_to_bv 64 ctx_brk) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 B)) ->
    exists regs',
      msteps RSEGS (mkst regs (0x62764 : word) m' rom) (mkst regs' (0x63c78 : word) m' rom)
      /\ getr regs' 10 = Z_to_bv 64 B /\ getr regs' 11 = Z_to_bv 64 4096 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 50 /\ getr regs' 14 = Z_to_bv 64 (-1) /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 1 = Z_to_bv 64 0x62784
      /\ keeps_but [1; 10; 11; 12; 13; 14; 15]%bv regs regs'.
  Proof using RN.
    intros regs rom m' nw B Hnw H10 H9 H19 H8 M_b. pre. unfold ctx_brk, CTX in M_b.
    eexists. split.
    - stepb_ft F_62710 D_62710 ltac:(rewrite H10, H9; apply c_eq_refl).
      stepLD8 F_62714 D_62714 (Z_to_bv 64 B).
      stepn F_62718 D_62718.
      stepn F_6271c D_6271c.
      stepn F_62720 D_62720. rewrite H8.
      stepn F_62724 D_62724.
      stepn F_62728 D_62728.
      stepn F_6272c D_6272c.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amB2r : forall regs rom (m' : mem) (nw r : Z),
    (0 <= nw < 2^64)%Z -> (0 <= r < 2^64)%Z -> r <> nw -> getr regs 10 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 nw ->
    msteps RSEGS (mkst regs (0x62764 : word) m' rom) (mkst regs (0x62798 : word) m' rom).
  Proof using.
    intros regs rom m' nw r Hnw Hr Hne H10 H9.
    stepb_tk F_62710 D_62710 ltac:(rewrite H10, H9, c_eq_Z by lia; apply Z.eqb_neq; exact Hne).
    pu_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma amB3 : forall regs rom (m' : mem) (nw : Z),
    (4096 <= nw < 2^64)%Z -> getr regs 9 = Z_to_bv 64 nw -> getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 ->
    store_ok RSEGS m' (Z_to_bv 64 CTX) 928%nat = true ->
    exists regs',
      msteps RSEGS (mkst regs (0x62784 : word) m' rom)
                   (mkst regs' (0x62810 : word)
                      (wbytes (wbytes m' (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 nw)))
                              (Z_to_bv 64 ctx_avail_meta_area_count) (word_to_le_bytes 8 (Z_to_bv 64 1))) rom)
      /\ getr regs' 9 = Z_to_bv 64 (nw - 4096) /\ getr regs' 8 = Z_to_bv 64 1
      /\ keeps_but [8; 9]%bv regs regs'.
  Proof using RN.
    intros regs rom m' nw Hnw H9 H19 H8 SOK'. pre. unfold ctx_brk, ctx_avail_meta_area_count, CTX.
    eexists. split.
    - stepSTx F_62730 D_62730 (Z_to_bv 64 682944) (Z_to_bv 64 nw) ltac:(sok 928%nat SOK').
      stepn F_62734 D_62734. rewrite H9, H8. rewrite v_sub_ZZ by lia.
      stepn F_62738 D_62738. rewrite H8. vals_lit.
      stepSTx F_6273c D_6273c (Z_to_bv 64 682064) (Z_to_bv 64 1) ltac:(sok 928%nat SOK').
      stepn F_62740 D_62740.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amRef : forall regs rom (m' : mem) (sh : Z),
    (0 <= sh <= 40)%Z ->
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 ->
    rdn RSEGS m' (Z_to_bv 64 ctx_avail_meta_area_count) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn RSEGS m' (Z_to_bv 64 ctx_meta_alloc_shift) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 sh)) ->
    store_ok RSEGS m' (Z_to_bv 64 CTX) 928%nat = true ->
    exists regs',
      msteps RSEGS (mkst regs (0x62798 : word) m' rom)
                   (mkst regs' (0x63c78 : word) (wbytes m' (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 (2^64 - 1)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 (2 * 2 ^ sh * 4096) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 34 /\ getr regs' 14 = Z_to_bv 64 (-1) /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 9 = Z_to_bv 64 (2 * 2 ^ sh) /\ getr regs' 20 = Z_to_bv 64 (2^64 - 1)
      /\ getr regs' 1 = Z_to_bv 64 0x627dc
      /\ keeps_but [1; 9; 10; 11; 12; 13; 14; 15; 20]%bv regs regs'.
  Proof using RN.
    intros regs rom m' sh Hsh H19 H8 M_ac0 M_sh SOK'. pre. unfold ctx_brk, ctx_avail_meta_area_count, ctx_meta_alloc_shift, CTX in *.
    assert (P1 : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (P2 : (2 ^ sh <= 2 ^ 40)%Z) by (apply Z.pow_le_mono_r; lia).
    eexists. split.
    - stepLD8 F_62744 D_62744 (Z_to_bv 64 0).
      stepn F_62748 D_62748.
      stepSTx F_6274c D_6274c (Z_to_bv 64 682944) (Z_to_bv 64 18446744073709551615) ltac:(sok 928%nat SOK').
      stepb_tk F_62750 D_62750 ltac:(cond_compute).
      stepLD8 F_6275c D_6275c (Z_to_bv 64 sh).
      stepn F_62760 D_62760.
      stepn F_62764 D_62764.
      replace (v_sll (Z_to_bv 64 2) (Z_to_bv 64 sh)) with (Z_to_bv 64 (2 * 2 ^ sh)).
      2:{ unfold v_sll. rewrite !u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small sh 64) by lia. reflexivity. }
      stepn F_62768 D_62768. rewrite H8. rewrite v_mul_Z by lia.
      stepn F_6276c D_6276c.
      stepn F_62770 D_62770.
      stepn F_62774 D_62774.
      stepn F_62778 D_62778.
      stepn F_6277c D_6277c.
      stepn F_62780 D_62780.
      stepn F_62784 D_62784.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amD : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 -> ac = 0%Z -> brk = (2^64 - 1)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x626ac : word) m rom) (mkst regs' (0x627b0 : word) m rom)
      /\ keeps_but [9; 10; 11]%bv regs regs'.
  Proof using M_brk M_ac M_cnt M_fh RN.
    intros regs rom H19 H8 Hac0 Hbm. pre.
    eexists. split.
    - head19.
      stepb_ft F_626b0 D_626b0 ltac:(rewrite Hac0; cond_compute).
      stepLD8 F_626b4 D_626b4 (Z_to_bv 64 brk).
      stepn F_626b8 D_626b8.
      stepb_tk F_626bc D_626bc ltac:(rewrite Hbm; cond_compute).
      stepb_tk F_62750 D_62750 ltac:(rewrite Hac0; cond_compute).
      pu_refl.
    - solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amMM : forall regs rom (m' : mem) (sh : Z),
    (0 <= sh <= 40)%Z ->
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 ->
    rdn RSEGS m' (Z_to_bv 64 ctx_meta_alloc_shift) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 sh)) ->
    exists regs',
      msteps RSEGS (mkst regs (0x627b0 : word) m' rom) (mkst regs' (0x63c78 : word) m' rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 (2 * 2 ^ sh * 4096) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 34 /\ getr regs' 14 = Z_to_bv 64 (-1) /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 9 = Z_to_bv 64 (2 * 2 ^ sh) /\ getr regs' 20 = Z_to_bv 64 (2^64 - 1)
      /\ getr regs' 1 = Z_to_bv 64 0x627dc
      /\ keeps_but [1; 9; 10; 11; 12; 13; 14; 15; 20]%bv regs regs'.
  Proof using RN.
    intros regs rom m' sh Hsh H19 H8 M_sh. pre. unfold ctx_meta_alloc_shift, CTX in *.
    assert (P1 : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (P2 : (2 ^ sh <= 2 ^ 40)%Z) by (apply Z.pow_le_mono_r; lia).
    eexists. split.
    - stepLD8 F_6275c D_6275c (Z_to_bv 64 sh).
      stepn F_62760 D_62760.
      stepn F_62764 D_62764.
      replace (v_sll (Z_to_bv 64 2) (Z_to_bv 64 sh)) with (Z_to_bv 64 (2 * 2 ^ sh)).
      2:{ unfold v_sll. rewrite !u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small sh 64) by lia. reflexivity. }
      stepn F_62768 D_62768. rewrite H8. rewrite v_mul_Z by lia.
      stepn F_6276c D_6276c.
      stepn F_62770 D_62770.
      stepn F_62774 D_62774.
      stepn F_62778 D_62778.
      stepn F_6277c D_6277c.
      stepn F_62780 D_62780.
      stepn F_62784 D_62784.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma amM2 : forall regs rom (m' : mem) (sh p0 : Z),
    (0 <= sh <= 40)%Z -> (HEAPLO <= p0)%Z -> (p0 + 8192 <= CEIL)%Z -> (p0 mod 4096 = 0)%Z ->
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 4096 -> getr regs 10 = Z_to_bv 64 p0 ->
    getr regs 9 = Z_to_bv 64 (2 * 2 ^ sh) -> getr regs 20 = Z_to_bv 64 (2^64 - 1) ->
    rdn RSEGS m' (Z_to_bv 64 ctx_meta_alloc_shift) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 sh)) ->
    store_ok RSEGS m' (Z_to_bv 64 CTX) 928%nat = true ->
    exists regs',
      msteps RSEGS (mkst regs (0x627dc : word) m' rom)
                   (mkst regs' (0x63d64 : word)
                      (wbytes (wbytes (wbytes m'
                         (Z_to_bv 64 ctx_avail_meta_area_count) (word_to_le_bytes 8 (Z_to_bv 64 (2 * 2 ^ sh - 1))))
                         (Z_to_bv 64 ctx_meta_alloc_shift) (word_to_le_bytes 8 (Z_to_bv 64 (sh + 1))))
                         (Z_to_bv 64 ctx_avail_meta_areas) (word_to_le_bytes 8 (Z_to_bv 64 (p0 + 4096)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (p0 + 4096) /\ getr regs' 11 = Z_to_bv 64 4096 /\ getr regs' 12 = Z_to_bv 64 3
      /\ getr regs' 9 = Z_to_bv 64 (p0 + 4096) /\ getr regs' 1 = Z_to_bv 64 0x628b0
      /\ keeps_but [1; 9; 10; 11; 12]%bv regs regs'.
  Proof using.
    intros regs rom m' sh p0 Hsh Hp1 Hp2 Hpal H19 H8 H10 H9 H20 M_sh SOK'. pre.
    unfold ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX in *.
    assert (P1 : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (P2 : (2 ^ sh <= 2 ^ 40)%Z) by (apply Z.pow_le_mono_r; lia).
    eexists. split.
    - stepb_ft F_62788 D_62788 ltac:(rewrite H10, H20, c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_6278c D_6278c. rewrite H9. addi_renorm.
      stepLD8 F_62790 D_62790 (Z_to_bv 64 sh).
      stepn F_62794 D_62794. rewrite H8. vals_lit.
      stepn F_62798 D_62798. rewrite v_mul_Z by lia. rewrite Z.mul_1_r.
      stepn F_6279c D_6279c. rewrite H10, H8. rewrite v_add_ZZ by lia.
      stepn F_627a0 D_627a0. addi_renorm.
      stepSTx F_627a4 D_627a4 (Z_to_bv 64 682064) (Z_to_bv 64 (2 * 2 ^ sh - 1)) ltac:(sok 928%nat SOK').
      stepSTx F_627a8 D_627a8 (Z_to_bv 64 682072) (Z_to_bv 64 (sh + 1)) ltac:(sok 928%nat SOK').
      stepSTx F_627ac D_627ac (Z_to_bv 64 682096) (Z_to_bv 64 (p0 + 4096)) ltac:(sok 928%nat SOK').
      stepn F_627b0 D_627b0. rewrite H8. addi_renorm.
      stepn F_627b4 D_627b4. rewrite v_and_Z by lia. rewrite land_4095_l by lia.
      replace ((p0 + 4096) mod 4096)%Z with 0%Z by (rewrite Z.add_mod, Hpal, Z.mod_same by lia; reflexivity).
      stepb_tk F_627b8 D_627b8 ltac:(apply c_eq_refl).
      stepn F_6284c D_6284c.
      stepn F_62850 D_62850.
      stepn F_62854 D_62854. rewrite H8.
      stepn F_62858 D_62858.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End NewArea.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section T.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (p ac cur tl sec : Z).
  Hypothesis Hp : (HEAPLO <= p)%Z /\ (p + 4096 <= CEIL)%Z /\ ((p + 4096 <= IMG_LO)%Z \/ (IMG_HI <= p)%Z).
  Hypothesis Hac : (0 < ac < 2^63)%Z.
  Hypothesis Hcur : (0 <= cur)%Z /\ (cur + 4096 < 2^64)%Z.
  Hypothesis Htl : (0 <= tl)%Z /\ (tl + 4096 <= CEIL)%Z.
  Hypothesis Hsec : (0 <= sec < 2^64)%Z.
  Hypothesis M_ac : rdn RSEGS m (Z_to_bv 64 ctx_avail_meta_area_count) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ac)).
  Hypothesis M_tl : rdn RSEGS m (Z_to_bv 64 ctx_meta_area_tail) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tl)).
  Hypothesis M_sec : rdn RSEGS m (Z_to_bv 64 ctx_secret) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 sec)).
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.
  Hypothesis SOKp : store_ok RSEGS m (Z_to_bv 64 p) 24%nat = true.

  (* [comment removed for export] *)
  Definition m_T0 : mem :=
    wbytes (wbytes m (Z_to_bv 64 ctx_avail_meta_area_count) (word_to_le_bytes 8 (Z_to_bv 64 (ac - 1))))
      (Z_to_bv 64 ctx_avail_meta_areas) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4096))).
  Definition m_Ttail (mx : mem) : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes mx
      (Z_to_bv 64 ctx_meta_area_tail) (word_to_le_bytes 8 (Z_to_bv 64 p)))
      (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 sec)))
      (Z_to_bv 64 (p + 16)) (word_to_le_bytes 4 (Z_to_bv 64 101)))
      (Z_to_bv 64 ctx_avail_meta) (word_to_le_bytes 8 (Z_to_bv 64 (p + 64))))
      (Z_to_bv 64 ctx_avail_meta_count) (word_to_le_bytes 8 (Z_to_bv 64 100)).
  (* [comment removed for export] *)
  Definition m_Tn : mem := m_Ttail (wbytes m_T0 (Z_to_bv 64 ctx_meta_area_head) (word_to_le_bytes 8 (Z_to_bv 64 p))).
  (* [comment removed for export] *)
  Definition m_Tt : mem := m_Ttail (wbytes m_T0 (Z_to_bv 64 (tl + 8)) (word_to_le_bytes 8 (Z_to_bv 64 p))).

  Ltac pre := ceil; unfold HEAPLO, ctx_avail_meta_count, ctx_avail_meta, ctx_avail_meta_area_count,
                ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_secret, CTX, MLOCK in *.

  Lemma amTn : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 9 = Z_to_bv 64 p -> tl = 0%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x62810 : word) m rom) (mkst regs' (0x6286c : word) m_Tn rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + 24) /\ keeps_but [10; 11; 12]%bv regs regs'.
  Proof using SOKp SOKc M_sec M_tl M_ac Htl Hac Hp RN.
    intros regs rom H19 H9 Htl0. pre. unfold m_Tn, m_Ttail, m_T0. pre. subst tl.
    eexists. split.
    - stepLD8 F_627bc D_627bc (Z_to_bv 64 ac).
      stepn F_627c0 D_627c0.
      stepLD8 F_627c4 D_627c4 (Z_to_bv 64 0).
      stepn F_627c8 D_627c8. rewrite H9. rewrite v_add_ZZ by lia.
      stepn F_627cc D_627cc. addi_renorm.
      stepSTx F_627d0 D_627d0 (Z_to_bv 64 682064) (Z_to_bv 64 (ac - 1)) ltac:(sok 928%nat SOKc).
      stepSTx F_627d4 D_627d4 (Z_to_bv 64 682096) (Z_to_bv 64 (p + 4096)) ltac:(sok 928%nat SOKc).
      stepb_tk F_627d8 D_627d8 ltac:(apply c_eq_refl).
      stepSTx F_627e4 D_627e4 (Z_to_bv 64 682080) (Z_to_bv 64 p) ltac:(sok 928%nat SOKc).
      stepLD8 F_627e8 D_627e8 (Z_to_bv 64 sec).
      stepSTx F_627ec D_627ec (Z_to_bv 64 682088) (Z_to_bv 64 p) ltac:(sok 928%nat SOKc).
      stepSTx F_627f0 D_627f0 (Z_to_bv 64 p) (Z_to_bv 64 sec) ltac:(sok 24%nat SOKp).
      stepLD8 F_627f4 D_627f4 (Z_to_bv 64 p).
      stepn F_627f8 D_627f8.
      stepSTx F_627fc D_627fc (Z_to_bv 64 (p + 16)) (Z_to_bv 64 101) ltac:(sok 24%nat SOKp).
      stepLD8 F_62800 D_62800 (Z_to_bv 64 p).
      stepn F_62804 D_62804. addi_renorm.
      stepn F_62808 D_62808.
      stepn F_6280c D_6280c. addi_renorm.
      stepSTx F_62810 D_62810 (Z_to_bv 64 682048) (Z_to_bv 64 (p + 64)) ltac:(sok 928%nat SOKc).
      stepSTx F_62814 D_62814 (Z_to_bv 64 682056) (Z_to_bv 64 100) ltac:(sok 928%nat SOKc).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.

  Lemma amTt : forall regs rom,
    getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 9 = Z_to_bv 64 p -> tl <> 0%Z -> (HEAPLO <= tl)%Z ->
    ((tl + 4096 <= IMG_LO)%Z \/ (IMG_HI <= tl)%Z) ->
    (tl + 4096 <= p \/ p + 4096 <= tl)%Z ->
    store_ok RSEGS m (Z_to_bv 64 (tl + 8)) 8%nat = true ->
    exists regs',
      msteps RSEGS (mkst regs (0x62810 : word) m rom) (mkst regs' (0x6286c : word) m_Tt rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + 24) /\ keeps_but [10; 11; 12]%bv regs regs'.
  Proof using SOKp SOKc M_sec M_tl M_ac Htl Hac Hp RN.
    intros regs rom H19 H9 Htl0 Htl1 Itl Dtp SOKt. pre. unfold m_Tt, m_Ttail, m_T0. pre.
    eexists. split.
    - stepLD8 F_627bc D_627bc (Z_to_bv 64 ac).
      stepn F_627c0 D_627c0.
      stepLD8 F_627c4 D_627c4 (Z_to_bv 64 tl).
      stepn F_627c8 D_627c8. rewrite H9. rewrite v_add_ZZ by lia.
      stepn F_627cc D_627cc. addi_renorm.
      stepSTx F_627d0 D_627d0 (Z_to_bv 64 682064) (Z_to_bv 64 (ac - 1)) ltac:(sok 928%nat SOKc).
      stepSTx F_627d4 D_627d4 (Z_to_bv 64 682096) (Z_to_bv 64 (p + 4096)) ltac:(sok 928%nat SOKc).
      stepb_ft F_627d8 D_627d8 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Htl0).
      stepSTx F_627dc D_627dc (Z_to_bv 64 (tl + 8)) (Z_to_bv 64 p) ltac:(store_ok_peel; exact SOKt).
      stepn F_627e0 D_627e0.
      stepLD8 F_627e8 D_627e8 (Z_to_bv 64 sec).
      stepSTx F_627ec D_627ec (Z_to_bv 64 682088) (Z_to_bv 64 p) ltac:(sok 928%nat SOKc).
      stepSTx F_627f0 D_627f0 (Z_to_bv 64 p) (Z_to_bv 64 sec) ltac:(sok 24%nat SOKp).
      stepLD8 F_627f4 D_627f4 (Z_to_bv 64 p).
      stepn F_627f8 D_627f8.
      stepSTx F_627fc D_627fc (Z_to_bv 64 (p + 16)) (Z_to_bv 64 101) ltac:(sok 24%nat SOKp).
      stepLD8 F_62800 D_62800 (Z_to_bv 64 p).
      stepn F_62804 D_62804. addi_renorm.
      stepn F_62808 D_62808.
      stepn F_6280c D_6280c. addi_renorm.
      stepSTx F_62810 D_62810 (Z_to_bv 64 682048) (Z_to_bv 64 (p + 64)) ltac:(sok 928%nat SOKc).
      stepSTx F_62814 D_62814 (Z_to_bv 64 682056) (Z_to_bv 64 100) ltac:(sok 928%nat SOKc).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End T.
End MhAMetaW.
Require Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhMSpec3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AM_ENTRY : Z := 0x625f8.
Definition AM_CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition AMSTK : Z := 144.

Section Spec.
  Context {fx : FPState} {RN : run_ceil}.

  (* [comment removed for export] *)
  Definition am_keep (st st' : mst) : Prop :=
    s_groups st' = s_groups st /\ s_slot st' = s_slot st /\ s_alist st' = s_alist st /\
    s_ai st' = s_ai st /\ s_kind st' = s_kind st /\ s_canary st' = s_canary st /\
    c_active (s_ctx st') = c_active (s_ctx st) /\ c_usage (s_ctx st') = c_usage (s_ctx st) /\
    c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st) /\
    c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_mmap_ctr (s_ctx st') = c_mmap_ctr (s_ctx st) /\ c_secret (s_ctx st') = c_secret (s_ctx st) /\
    (forall x, is_group st x -> s_meta st' x = s_meta st x) /\
    (forall x, In x (s_limbo st) -> s_meta st' x = s_meta st x) /\
    (forall x, metaU st x -> metaU st' x).

  (* [comment removed for export] *)
  Definition am_regions (st st' : mst) (X : list (word * word)) : Prop :=
    RSUM (s_regions st') <= RSUM (s_regions st) + 2 ^ 24 /\
    Z.of_nat (length (s_regions st')) <= Z.of_nat (length (s_regions st)) + 1 /\
    (forall r, In r (s_regions st') ->
       (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
       forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\
                                        (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r)).

  (* [comment removed for export] *)
  Definition am_changed (st' : mst) (sp : Z) (a : Z) : Prop :=
    (sp - AMSTK <= a < sp) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4) \/
    (exists r, In r (s_regions st') /\ (forall x, rg_kind r <> RGroup x) /\ rg_base r <= a < rg_base r + rg_len r).

  (* [comment removed for export] *)
  Definition am_holeR (rs : list region) (X : list (word * word)) (a : Z) : Prop :=
    HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\
    (forall r, In r rs -> ~ (rg_base r <= a < rg_base r + rg_len r)) /\
    (forall ea en, In (Z_to_bv 64 ea, Z_to_bv 64 en) X -> HEAPLO <= ea -> 0 < en -> ea + en <= CEIL -> ~ (ea <= a < ea + en)).

  Lemma am_holeR_rng : forall rs X a, am_holeR rs X a -> HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a).
  Proof. intros rs X a (H1 & H2 & _). exact (conj H1 H2). Qed.

  Lemma am_holeR_X : forall rs X a, am_holeR rs X a ->
    forall ea en, In (Z_to_bv 64 ea, Z_to_bv 64 en) X -> HEAPLO <= ea -> 0 < en -> ea + en <= CEIL -> ~ (ea <= a < ea + en).
  Proof. intros rs X a (_ & _ & _ & H4). exact H4. Qed.


  (* [comment removed for export] *)
  Lemma am_holeR_nonapp : forall st' L X a, WF st' L -> am_holeR (s_regions st') X a ->
    HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ (exists p n, In (p, n) L /\ p <= a < p + n)  (* [comment removed for export] *).
  Proof.
    intros st' L X a W (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2|]. intros (b & k & Hin & Ha).
    destruct (wL_in st' L (WF_live st' L W) b k Hin) as (x & j & o2 & rr2 & Hx & Hj & Hs).
    destruct (appb_in_span st' L W a ltac:(exists x, j, b, k, o2, rr2; repeat split; try assumption; lia)) as (y & Hy & Ra).
    destruct (group_in_top st' L W y Hy) as (t & Ht & Kt & T1 & T2 & HinR).
    apply (H3 _ HinR). cbn [rg_base rg_len]. unfold g_map_end in T2. lia.
  Qed.

  (* [comment removed for export] *)
  Definition am_ok (st : mst) (L : list (Z * Z)) (X : list (word * word)) (sp : Z)
             (regs : bvmap 5 word) (M : mem) (mdl : Model) (rom : word -> option byte) (c' : config) : Prop :=
    exists st' M' mdl' regs' (m : Z),
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      WF st' L /\ REP st' M' /\ LEDGERX st' X (m_vmmaps mdl') /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\
      (* [comment removed for export] *)
      s_limbo st' = m :: s_limbo st /\ metaU st' m /\ s_meta st' m = meta_zero /\ ~ In m (s_limbo st) /\
      s_flist st' = match s_flist st with [] => [] | _ :: r => r end /\
      (s_errno st' = s_errno st \/ s_errno st' = 12) /\   (* [comment removed for export] *)
      am_keep st st' /\ am_regions st st' X /\
      (* [comment removed for export] *)
      getr regs' 10 = Z_to_bv 64 m /\ getr regs' 2 = getr regs 2 /\ keeps_but AM_CLOB regs regs' /\
      (* [comment removed for export] *)
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> am_changed st' sp a \/ am_holeR (s_regions st') X a) /\
      defined M' (sp - AMSTK) sp.

  (* [comment removed for export] *)
  Definition am_fail (st : mst) (L : list (Z * Z)) (X : list (word * word)) (sp : Z)
             (regs : bvmap 5 word) (M : mem) (mdl : Model) (rom : word -> option byte) (c' : config) : Prop :=
    exists st' M' mdl' regs',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      WF st' L /\ REP st' M' /\ LEDGERX st' X (m_vmmaps mdl') /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\
      (* [comment removed for export] *)
      s_limbo st' = s_limbo st /\ s_flist st' = s_flist st /\ s_areas st' = s_areas st /\ s_meta st' = s_meta st /\
      s_errno st' = 12 (* [comment removed for export] *) /\
      am_keep st st' /\ am_regions st st' X /\
      (* [comment removed for export] *)
      getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = getr regs 2 /\ keeps_but AM_CLOB regs regs' /\
      (* [comment removed for export] *)
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> am_changed st' sp a) /\
      defined M' (sp - AMSTK) sp.

  (* [comment removed for export] *)
  Definition AM_SPEC3 : Prop :=
    forall (F : kfam) (bi bo : bool) st L X (M : mem) mdl regs rom sp,
      kfam_laws RSEGS F -> (bo = true -> bi = true) ->
      WF st L -> REP st M -> LEDGERX st X (m_vmmaps mdl) -> xok X ->
      m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
      (s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 -> Z.of_nat (length (s_areas st)) + 1 <= AREAMAX) ->
      Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246 ->
      XSUM X + RSUM (s_regions st) + 2 ^ 24 <= vm_limit (m_vmmaps mdl) ->
      getr regs 2 = Z_to_bv 64 sp -> ret_ok (getr regs 1) -> CEIL + AMSTK <= sp -> sp < 2 ^ 64 ->
      getr regs 4 = Z_to_bv 64 TPV ->
      defined M (sp - AMSTK) sp ->
      (forall c', am_ok st L X sp regs M mdl rom c' -> kfx F bi c') ->
      (forall c', am_fail st L X sp regs M mdl rom c' -> Kf F c') ->
      kfx F bo (mkCfg (mkst regs (Z_to_bv 64 AM_ENTRY) M rom) mdl).
End Spec.
End MhMSpec3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMeta1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMeta2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest MhAMetaW OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMeta1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMeta2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX MhMSpec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Flat.
  Context {fx : FPState} {RN : run_ceil}.
  Definition am_post (st : mst) (L : list (Z * Z)) (X : list (word * word)) (sp : Z)
             (regs : bvmap 5 word) (M : mem) (mdl : Model) (rom : word -> option byte) (c' : config) : Prop :=
    exists st' M' mdl' regs' (m : Z),
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      WF st' L /\ REP st' M' /\ LEDGERX st' X (m_vmmaps mdl') /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\
      s_limbo st' = m :: s_limbo st /\ metaU st' m /\ s_meta st' m = meta_zero /\
      s_groups st' = s_groups st /\ s_slot st' = s_slot st /\ s_alist st' = s_alist st /\
      s_ai st' = s_ai st /\ s_kind st' = s_kind st /\ s_flist st' = match s_flist st with [] => [] | _ :: r => r end /\
      (forall x, is_group st x -> s_meta st' x = s_meta st x) /\
      s_canary st' = s_canary st /\ (s_errno st' = s_errno st \/ s_errno st' = 12) /\
      c_active (s_ctx st') = c_active (s_ctx st) /\ c_usage (s_ctx st') = c_usage (s_ctx st) /\
      c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st) /\
      c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_mmap_ctr (s_ctx st') = c_mmap_ctr (s_ctx st) /\ c_secret (s_ctx st') = c_secret (s_ctx st) /\
      (forall x, In x (s_limbo st) -> s_meta st' x = s_meta st x) /\ ~ In m (s_limbo st) /\ (forall x, metaU st x -> metaU st' x) /\
      RSUM (s_regions st') <= RSUM (s_regions st) + 2 ^ 24 /\
      Z.of_nat (length (s_regions st')) <= Z.of_nat (length (s_regions st)) + 1 /\
      (forall r, In r (s_regions st') -> (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
         forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\ (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r)) /\
      getr regs' 10 = Z_to_bv 64 m /\ getr regs' 2 = getr regs 2 /\ keeps_but AM_CLOB regs regs' /\
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
         (sp - AMSTK <= a < sp) \/ (CTX <= a < CTX_END) \/
         (exists r, In r (s_regions st') /\ (forall x, rg_kind r <> RGroup x) /\ rg_base r <= a < rg_base r + rg_len r) \/
         (A_ERRNO <= a < A_ERRNO + 4) \/ am_holeR (s_regions st') X a) /\
      defined M' (sp - AMSTK) sp.

  Lemma am_post_ok : forall st L X sp regs M mdl rom c', am_post st L X sp regs M mdl rom c' -> am_ok st L X sp regs M mdl rom c'.
  Proof.
    intros st L X sp regs M mdl rom c'
      (st' & M' & mdl' & regs' & m & E & W & R & LG & X1 & X2 & X3 & X4 & X5 & X6 & Lm & Um & Zm & G1 & G2 & G3 & G4 & G5 & FL & GM & CA & ER
       & C1 & C2 & C3 & C4 & C5 & C6 & C7 & LM & NL & MU & RS & RL & RR & A10 & A2 & KB & FR & DF).
    exists st', M', mdl', regs', m. repeat (split; [assumption|]).
    split; [repeat (split; [assumption|]); exact MU|].
    split; [split; [exact RS | split; [exact RL | exact RR]]|].
    repeat (split; [assumption|]). split; [|exact DF].
    intros a Ha NE. destruct (FR a Ha NE) as [Y|[Y|[Y|[Y|Y]]]];
      [left; left; exact Y | left; right; left; exact Y | left; right; right; right; exact Y | left; right; right; left; exact Y | right; exact Y].
  Qed.
End Flat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma keeps_join : forall c1 c2 (r0 r1 r2 : bvmap 5 word), keeps_but c1 r0 r1 -> keeps_but c2 r1 r2 -> keeps_but (c1 ++ c2) r0 r2.
Proof.
  intros c1 c2 r0 r1 r2 K1 K2. eapply keeps_but_trans.
  - eapply keeps_but_mono; [exact K1 | intros r Hr; apply in_or_app; left; exact Hr].
  - eapply keeps_but_mono; [exact K2 | intros r Hr; apply in_or_app; right; exact Hr].
Qed.

Definition AM_SAVED : list reg := [1; 2; 8; 9; 18; 19; 20; 21]%bv.

(* [comment removed for export] *)
Definition clobI : list reg := (clobA ++ [1; 5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31])%bv.
Lemma clobA_clobI : forall regs r1, keeps_but clobA regs r1 -> keeps_but clobI regs r1.
Proof. intros regs r1 K. eapply keeps_but_mono; [exact K|]. intros r Hr. unfold clobI. apply in_or_app. left. exact Hr. Qed.

Lemma keeps_final_am : forall (regs r' : bvmap 5 word) big,
  keeps_but big regs r' ->
  forallb (fun r => existsb (fun x => bv_eqb x r) AM_CLOB || existsb (fun x => bv_eqb x r) AM_SAVED)%bool big = true ->
  getr r' 1 = getr regs 1 -> getr r' 2 = getr regs 2 -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
  getr r' 18 = getr regs 18 -> getr r' 19 = getr regs 19 -> getr r' 20 = getr regs 20 -> getr r' 21 = getr regs 21 ->
  keeps_but AM_CLOB regs r'.
Proof.
  intros regs r' big K Hbig E1 E2 E8 E9 E18 E19 E20 E21 r Hr.
  destruct (in_dec (fun x y : reg => bv_eq_dec _ x y) r big) as [I|NI]; [|exact (K r NI)].
  pose proof (proj1 (forallb_forall _ _) Hbig r I) as X. cbn beta in X. apply Bool.orb_true_iff in X.
  destruct X as [X|X]; apply in_regs_dec in X; [exfalso; exact (Hr X)|].
  destruct X as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MemHelp.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma wbytes_diff_g : forall (Mx : mem) (b : Z) bs a, 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
    wbytes Mx (Z_to_bv 64 b) bs (Z_to_bv 64 a) <> Mx (Z_to_bv 64 a) -> b <= a < b + Z.of_nat (length bs).
  Proof.
    intros Mx b bs a Hb Hbl Ha NE.
    destruct (Z.lt_ge_cases a b) as [A|A].
    - exfalso. apply NE. apply wbytes_below; rewrite !u_Z2bv by lia; lia.
    - destruct (Z.lt_ge_cases a (b + Z.of_nat (length bs))) as [B|B]; [lia|].
      exfalso. apply NE. apply wbytes_above. rewrite !u_Z2bv by lia. lia.
  Qed.
End MemHelp.

Ltac wdiff NE Mbase a :=
  repeat match type of NE with wbytes ?Mb (Z_to_bv 64 ?b) _ _ <> _ =>
    destruct (decide (Mb (Z_to_bv 64 a) = Mbase (Z_to_bv 64 a))) as [?E2|?NE2];
    [ (rewrite <- E2 in NE || idtac); apply wbytes_diff_g in NE;
      [ rewrite length_N_to_le_bytes in NE; cbn in NE; lia | lia | rewrite length_N_to_le_bytes; cbn; lia | assumption ]
    | clear NE; rename NE2 into NE ] end;
  exfalso; exact (NE eq_refl).

Section AMS.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp : Z) (Q : config -> Prop).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGERX st X (m_vmmaps mdl).
  Hypothesis XOK : xok X.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis HCNT : s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 -> Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  Hypothesis HLEN : Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246.
  Hypothesis HBUD : XSUM X + RSUM (s_regions st) + 2 ^ 24 <= vm_limit (m_vmmaps mdl).
  Hypothesis H2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Hra : ret_ok (getr regs 1).
  Hypothesis Hsp : CEIL + AMSTK <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - AMSTK) sp.
  Hypothesis HQ : forall c', am_post st L X sp regs M mdl rom c' -> Q c'.

  #[local] Notation cx := (s_ctx st).
  Definition can : Z := s_canary st.
  Definition M1 : mem := am_frame M sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20).
  (* [comment removed for export] *)
  Definition spc : Z := sp - AMSTK + MSTK.

  Lemma can_rng : 0 <= can < 2 ^ 64. Proof. exact (wc_canary st (WF_ctx st L HWF)). Qed.
  Lemma SOK64 : store_ok RSEGS M (Z_to_bv 64 (sp - 64)) 64%nat = true.
  Proof. ceil; unfold AMSTK in *. eapply store_ok_defined; [exact DEF | lia | cbn; lia | lia | lia]. Qed.

  Lemma M1_writes : forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sp - 56 <= a < sp.
  Proof. intros a Ha NE. ceil; unfold M1, am_frame, AMSTK in *. wdiff NE M a. Qed.
  Lemma M1_grows : mem_grows M M1.
  Proof. unfold M1, am_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma M1_REP : REP st M1.
  Proof.
    apply (REP_frame st L M HWF HREP M1 M1_grows). intros a Hr NE. left. pose proof (M1_writes a Hr NE). ceil; unfold AMSTK in *. lia.
  Qed.
  Lemma M1_def : defined M1 (sp - AMSTK) sp.
  Proof. unfold M1, am_frame. repeat apply defined_wbytes. exact DEF. Qed.
  Lemma M1_ra : rdn RSEGS M1 (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 (getr regs 1)).
  Proof. ceil; unfold M1, am_frame, AMSTK in *. rdn_solve. Qed.
  Lemma M1_s0 : rdn RSEGS M1 (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8)).
  Proof. ceil; unfold M1, am_frame, AMSTK in *. rdn_solve. Qed.
  Lemma M1_s1 : rdn RSEGS M1 (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9)).
  Proof. ceil; unfold M1, am_frame, AMSTK in *. rdn_solve. Qed.
  Lemma M1_s2 : rdn RSEGS M1 (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18)).
  Proof. ceil; unfold M1, am_frame, AMSTK in *. rdn_solve. Qed.
  Lemma M1_s3 : rdn RSEGS M1 (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19)).
  Proof. ceil; unfold M1, am_frame, AMSTK in *. rdn_solve. Qed.
  Lemma M1_s4 : rdn RSEGS M1 (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20)).
  Proof. ceil; unfold M1, am_frame, AMSTK in *. rdn_solve. Qed.
  Lemma M1_can : rdn RSEGS M1 (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Proof. ceil; unfold M1, am_frame, AMSTK in *. rdn_solve. Qed.

  (* [comment removed for export] *)
  Lemma am_head : forall (Kont : bvmap 5 word -> Prop),
    (forall r1, getr r1 2 = Z_to_bv 64 (sp - 64) -> getr r1 19 = Z_to_bv 64 MLOCK -> getr r1 8 = Z_to_bv 64 4096 ->
                getr r1 18 = Z_to_bv 64 A_CANARY -> keeps_but clobI regs r1 ->
                kat RSEGS (mkCfg (mkst r1 (0x626ac%bv : word) M1 rom) mdl) Q) ->
    kat RSEGS (mkCfg (mkst regs (0x625f8%bv : word) M rom) mdl) Q.
  Proof.
    intros Kont HK. pose proof (rp_statics st M HREP) as [Snl Spg Slk Scan Sgot Serr Sctz Ssc]. pose proof (rp_ctx st M HREP) as RC.
    destruct (amA M sp can ltac:(unfold AMSTK in Hsp; lia) SOK64 Sgot Scan (rc_init st M RC) Spg regs rom H2) as (r1 & RUN & E2' & E19 & E8 & E18 & K).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |]. fold M1. apply HK; try assumption. apply clobA_clobI. exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ArmA.
    Hypothesis Hnn : s_flist st <> [].
    #[local] Notation fh := (head_of (s_flist st)).
    #[local] Notation nxf := (mr_next (s_meta st fh)).
    #[local] Notation pvf := (mr_prev (s_meta st fh)).

    Lemma A_fh : c_free_head cx = fh. Proof. exact (wc_fhead st (WF_ctx st L HWF)). Qed.
    Lemma A_meta_cells : forall x, metaU st x ->
      cell M1 x 8 (mr_prev (s_meta st x)) /\ cell M1 (x + 8) 8 (mr_next (s_meta st x)) /\
      HEAPLO + 24 <= x /\ x + 40 <= CEIL /\ store_ok RSEGS M1 (Z_to_bv 64 x) 40%nat = true.
    Proof.
      intros x U. pose proof (metaU_area st L HWF x U) as (ar & k & Har & Hk & Hxa & _).
      pose proof (ra_metas st M1 ar (rp_areas st M1 M1_REP ar Har) k Hk) as RM. rewrite <- Hxa in RM. destruct RM as [P N _ _ _ _].
      destruct (metaU_rng st L HWF x U) as (R1 & R2 & _).
      repeat split; try assumption. exact (meta_store_ok st L M1 HWF M1_REP x U).
    Qed.

    Lemma arm_A : forall r1, getr r1 2 = Z_to_bv 64 (sp - 64) -> getr r1 19 = Z_to_bv 64 MLOCK -> getr r1 8 = Z_to_bv 64 4096 ->
      getr r1 18 = Z_to_bv 64 A_CANARY -> keeps_but clobI regs r1 ->
      kat RSEGS (mkCfg (mkst r1 (0x626ac%bv : word) M1 rom) mdl) Q.
    Proof.
      intros r1 G2 G19 G8 G18 K1.
      pose proof (MhAMeta1.fh_facts st L HWF Hnn) as (Ufh & _). pose proof (MhAMeta1.nx_facts st L HWF Hnn) as (Unx & _). pose proof (MhAMeta1.pv_facts st L HWF Hnn) as (Upv & _).
      destruct (A_meta_cells fh Ufh) as (Cpv & Cnx & R1 & R2 & SOKfh).
      pose proof (rc_fmh st M1 (rp_ctx st M1 M1_REP)) as Cfh. rewrite A_fh in Cfh.
      pose proof (ctx_store_ok st M1 M1_REP) as SOKc.
      assert (SOKh : store_ok RSEGS M1 (Z_to_bv 64 ctx_free_meta_head) 8%nat = true).
      { unfold ctx_free_meta_head. eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOKc | | ]; unfold CTX; zsimp; lia. }
      assert (Hnz : fh <> 0) by (unfold HEAPLO in R1; lia).
      pose proof can_rng as CR. pose proof Hsp as [S1 S2]. unfold AMSTK in S1.
      (* [comment removed for export] *)
      assert (MAIN : forall Mf rf (wr : Z -> Prop),
        msteps RSEGS (mkst r1 (0x626ac%bv : word) M1 rom) (mkst rf (0x6286c%bv : word) Mf rom) ->
        getr rf 10 = Z_to_bv 64 fh -> keeps_but [10; 11; 12]%bv r1 rf ->
        mem_grows M1 Mf ->
        (forall a, 0 <= a < 2 ^ 64 -> Mf (Z_to_bv 64 a) <> M1 (Z_to_bv 64 a) -> wr a) ->
        (forall a, wr a -> (single st = false /\ ((pvf + 8 <= a < pvf + 16) \/ (nxf <= a < nxf + 8))) \/ (ctx_free_meta_head <= a < ctx_free_meta_head + 8)) ->
        (single st = false -> cell Mf (pvf + 8) 8 nxf) -> (single st = false -> cell Mf nxf 8 pvf) ->
        cell Mf ctx_free_meta_head 8 (head_of (MhAMeta1.l' st)) ->
        kat RSEGS (mkCfg (mkst r1 (0x626ac%bv : word) M1 rom) mdl) Q).
      { intros Mf rf wr RUN E10 Kf Gf Wf Hwr Cpv' Cnx' Cfh'.
        assert (AGs : forall a n bs, CEIL <= a -> a + Z.of_nat n <= sp -> rdn RSEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn RSEGS Mf (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by (ceil; lia); lia|].
          intros x Hx. rewrite u_Z2bv in Hx by (ceil; lia).
          destruct (decide (Mf x = M1 x)) as [E|NE]; [exact E|]. exfalso.
          pose proof (u64_range x) as Xr. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl) in NE.
          destruct (Hwr _ (Wf (bv_unsigned x) ltac:(lia) NE)) as [[_ [W|W]]|W].
          - destruct (metaU_rng st L HWF _ Upv). ceil. lia.
          - destruct (metaU_rng st L HWF _ Unx). ceil. lia.
          - ceil; unfold ctx_free_meta_head, CTX in *. lia. }
        assert (CANf : rdn RSEGS Mf (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can))).
        { pose proof (rc_canary st M1 (rp_statics st M1 M1_REP)) as C. unfold cell in C. fold can in C. rewrite <- C.
          apply rdn_ext; [rewrite u_Z2bv by (unfold A_CANARY; lia); unfold A_CANARY; lia|].
          intros x Hx. rewrite u_Z2bv in Hx by (unfold A_CANARY; lia). unfold A_CANARY in Hx.
          destruct (decide (Mf x = M1 x)) as [E|NE]; [exact E|]. exfalso.
          rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl) in NE.
          destruct (Hwr _ (Wf (bv_unsigned x) ltac:(lia) NE)) as [[_ [W|W]]|W].
          - destruct (metaU_rng st L HWF _ Upv). unfold HEAPLO in *. lia.
          - destruct (metaU_rng st L HWF _ Unx). unfold HEAPLO in *. lia.
          - unfold ctx_free_meta_head, CTX in *. lia. }
        assert (SOKg : store_ok RSEGS Mf (Z_to_bv 64 fh) 16%nat = true).
        { eapply store_ok_mono; [exact Gf|]. ceil; unfold HEAPLO in *. eapply (store_ok_sub _ _ _ _ 40%nat); [|exact SOKfh| |]; zsimp; lia. }
        destruct (amE Mf sp can fh (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                    ltac:(lia) ltac:(unfold HEAPLO in *; lia) Hra SOKg CANf
                    (AGs (sp - 56) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_can) (AGs (sp - 8) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_ra)
                    (AGs (sp - 16) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s0) (AGs (sp - 24) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s1)
                    (AGs (sp - 32) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s2) (AGs (sp - 40) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s3)
                    (AGs (sp - 48) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s4) rf rom ltac:(kept_rw Kf; exact G2) E10 ltac:(kept_rw Kf; exact G18))
          as (r' & RUNE & F2 & F10 & F1 & F8 & F9 & F18 & F19 & F20 & KE).
        eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |]. eapply kat_msteps; [exact Hh | exact Hlz | exact RUNE |].
        apply kat_refl. apply HQ.
        (* [comment removed for export] *)
        set (M' := m_E Mf fh).
        assert (WFm : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> MhAMeta1.p_wr st spc a).
        { intros a Ha NE. unfold MhAMeta1.p_wr, spc, AMSTK, MSTK.
          destruct (decide (M' (Z_to_bv 64 a) = Mf (Z_to_bv 64 a))) as [E1|NE1].
          - rewrite E1 in NE. destruct (decide (Mf (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E3|NE3].
            + rewrite E3 in NE. pose proof (M1_writes a Ha NE). left. lia.
            + destruct (Hwr _ (Wf a Ha NE3)) as [W|W]; [right; right; left; exact W | right; right; right; exact W].
          - unfold M', m_E in NE1. right; left. ceil; unfold HEAPLO in *. wdiff NE1 Mf a. }
        assert (GR : mem_grows M M') by (eapply mem_grows_trans; [exact M1_grows|]; eapply mem_grows_trans; [exact Gf|]; unfold M', m_E; eapply mem_grows_trans; apply wbytes_grows).
        ceil; unfold HEAPLO in R1, R2.
        assert (Cm0 : cell M' fh 8 0) by (unfold cell, M', m_E; apply rdn_wbytes_hit8; zsimp; lia).
        assert (Cm8 : cell M' (fh + 8) 8 0) by (unfold cell, M', m_E; rdn_peel1; apply rdn_wbytes_hit8; zsimp; lia).
        assert (AGm : forall a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (a + Z.of_nat n <= fh \/ fh + 16 <= a) -> cell Mf a n v -> cell M' a n v).
        { intros a n v Ha Hn D C. unfold cell, M', m_E in *. do 2 rdn_peel1. exact C. }
        destruct (flpop_close st L M M' spc HWF HREP Hnn ltac:(unfold spc, AMSTK, MSTK; lia) WFm GR Cm0 Cm8) as [WF' REP'].
        { intros Hs. apply AGm; [destruct (metaU_rng st L HWF _ Upv); unfold HEAPLO in *; lia | destruct (metaU_rng st L HWF _ Upv); ceil; cbn; lia | | exact (Cpv' Hs)].
          destruct (metaU_sep st L HWF fh pvf Ufh Upv (fun E => MhAMeta1.pv_ne st L HWF Hnn Hs (eq_sym E))); cbn; lia. }
        { intros Hs. apply AGm; [destruct (metaU_rng st L HWF _ Unx); unfold HEAPLO in *; lia | destruct (metaU_rng st L HWF _ Unx); ceil; cbn; lia | | exact (Cnx' Hs)].
          destruct (metaU_sep st L HWF fh nxf Ufh Unx (fun E => MhAMeta1.nx_ne st Hs (eq_sym E))); cbn; lia. }
        { apply AGm; [unfold ctx_free_meta_head, CTX; lia | unfold ctx_free_meta_head, CTX; cbn; lia | unfold ctx_free_meta_head, CTX, HEAPLO in *; cbn; lia | exact Cfh']. }
        exists (MhAMeta1.st' st), M', mdl, r', fh.
        split; [reflexivity|].
        split; [exact WF'|]. split; [exact REP'|]. split; [apply (LEDGERX_same st); [reflexivity | reflexivity | exact HLG]|].
        split; [exact Hh|]. split; [exact Hlz|]. split; [exact Hmat|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [apply MhAMeta1.e_metaU; exact Ufh|]. split; [apply MhAMeta1.e_meta_fh; assumption|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|].
        split; [intros x Hx; apply (MhAMeta1.p_meta_group st L HWF Hnn x Hx)|].
        split; [reflexivity|]. split; [left; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros x Hx; apply (MhAMeta1.p_meta_offlist st L HWF Hnn x); intros IN; exact (proj1 (proj2 (proj2 (wG_limbo st L (WF_groups st L HWF) x Hx))) (or_introl IN))|].
        split; [intros IN; exact (proj1 (proj2 (proj2 (wG_limbo st L (WF_groups st L HWF) _ IN))) (or_introl (MhAMeta1.fh_in st Hnn)))|].
        split; [intros x Ux; apply (proj2 (MhAMeta1.e_metaU st x)); exact Ux|].
        split; [cbn [s_regions MhAMeta1.st']; lia|]. split; [cbn [s_regions MhAMeta1.st']; lia|].
        split; [intros r Hr; left; exists r; split; [exact Hr | split; reflexivity]|].
        split; [exact F10|]. split; [rewrite F2, H2; reflexivity|].
        split.
        { apply (keeps_final_am regs r' (clobI ++ ([10; 11; 12]%bv ++ clobE))).
          - eapply keeps_join; [exact K1|]. eapply keeps_join; [exact Kf | exact KE].
          - reflexivity.
          - exact F1. - rewrite F2, H2; reflexivity. - exact F8. - exact F9. - exact F18. - exact F19. - exact F20.
          - kept_rw KE. kept_rw Kf. kept_rw K1. reflexivity. }
        split.
        { intros a Ha NE. destruct (WFm a Ha NE) as [W|[W|[[_ [W|W]]|W]]].
          - left. unfold spc, MSTK, AMSTK in W |- *. pose proof (M1_writes a Ha). 
            destruct (decide (M' (Z_to_bv 64 a) = Mf (Z_to_bv 64 a))) as [E1|NE1].
            + rewrite E1 in NE. destruct (decide (Mf (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E3|NE3].
              * rewrite E3 in NE. pose proof (M1_writes a Ha NE). lia.
              * destruct (Hwr _ (Wf a Ha NE3)) as [[_ [W2|W2]]|W2].
                -- destruct (metaU_rng st L HWF _ Upv). ceil. lia.
                -- destruct (metaU_rng st L HWF _ Unx). ceil. lia.
                -- ceil; unfold ctx_free_meta_head, CTX in *. lia.
            + unfold M', m_E in NE1. exfalso. ceil; unfold HEAPLO in *. wdiff NE1 Mf a.
          - right; right; left. destruct (metaU_area st L HWF fh Ufh) as (ar & k & Har & Hk & Hxa & _ & _ & _ & Q1 & Q2 & _).
            destruct (area_in_region st L HWF ar Har) as (rr & Hrr & Hk' & Z1 & Z2). exists rr. cbn [s_regions MhAMeta1.st']. repeat split; try assumption; lia.
          - right; right; left. destruct (metaU_area st L HWF pvf Upv) as (ar & k & Har & Hk & Hxa & _ & _ & _ & Q1 & Q2 & _).
            destruct (area_in_region st L HWF ar Har) as (rr & Hrr & Hk' & Z1 & Z2). exists rr. cbn [s_regions MhAMeta1.st']. repeat split; try assumption; lia.
          - right; right; left. destruct (metaU_area st L HWF nxf Unx) as (ar & k & Har & Hk & Hxa & _ & _ & _ & Q1 & Q2 & _).
            destruct (area_in_region st L HWF ar Har) as (rr & Hrr & Hk' & Z1 & Z2). exists rr. cbn [s_regions MhAMeta1.st']. repeat split; try assumption; lia.
          - right; left. unfold ctx_free_meta_head, CTX_END, CTX in *. lia. }
        eapply defined_grows; [|exact M1_def]. eapply mem_grows_trans; [exact Gf|]. unfold M', m_E. eapply mem_grows_trans; apply wbytes_grows. }
      (* [comment removed for export] *)
      destruct (Z.eq_dec nxf fh) as [Enx|NEnx].
      - (* [comment removed for export] *)
        assert (Hs : single st = true) by (unfold MhAMeta1.single; apply Z.eqb_eq; exact Enx).
        destruct (amF1 M1 fh nxf ltac:(unfold HEAPLO in *; lia) Hnz Cfh Cnx SOKh r1 rom G19 Enx) as (rf & RUN & E10 & Kf).
        apply (MAIN (m_F1 M1) rf (fun a => ctx_free_meta_head <= a < ctx_free_meta_head + 8) RUN E10).
        + eapply keeps_but_mono; [exact Kf|]. intros r Hr. cbn in Hr |- *. tauto.
        + unfold m_F1. apply wbytes_grows.
        + intros a Ha NE. unfold m_F1, ctx_free_meta_head, CTX in *. wdiff NE M1 a.
        + intros a W. right. exact W.
        + intros Hs'. rewrite Hs in Hs'. discriminate Hs'.
        + intros Hs'. rewrite Hs in Hs'. discriminate Hs'.
        + rewrite (MhAMeta1.head_l' st L HWF Hnn), Hs. unfold cell, m_F1. apply rdn_wbytes_hit8. unfold ctx_free_meta_head, CTX. zsimp; lia.
      - (* [comment removed for export] *)
        assert (Hs : single st = false) by (unfold MhAMeta1.single; apply Z.eqb_neq; exact NEnx).
        pose proof (MhAMeta1.pv_ne st L HWF Hnn Hs) as NEpv.
        destruct (A_meta_cells nxf Unx) as (_ & _ & N1 & N2 & SOKn). destruct (A_meta_cells pvf Upv) as (_ & _ & P1 & P2 & SOKp).
        pose proof (metaU_sep st L HWF fh nxf Ufh Unx (fun E => NEnx (eq_sym E))) as Dfn.
        pose proof (metaU_sep st L HWF fh pvf Ufh Upv (fun E => NEpv (eq_sym E))) as Dfp.
        assert (Dnp : nxf = pvf \/ nxf + 40 <= pvf \/ pvf + 40 <= nxf).
        { destruct (Z.eq_dec nxf pvf) as [E|NE]; [left; exact E | right]. exact (metaU_sep st L HWF nxf pvf Unx Upv NE). }
        destruct (amF2 M1 fh nxf pvf ltac:(unfold HEAPLO in *; lia) Hnz Cfh Cnx Cpv SOKh r1 rom G19 NEnx
                    ltac:(unfold HEAPLO in *; lia) N2 ltac:(unfold HEAPLO in *; lia) P2
                    ltac:(pose proof (metaU_img st L HWF nxf Unx); lia) ltac:(pose proof (metaU_img st L HWF pvf Upv); lia) Dfn Dfp Dnp
                    ltac:(ceil; unfold HEAPLO in *; eapply (store_ok_sub _ _ _ _ 40%nat); [|exact SOKp| |]; zsimp; lia)
                    ltac:(ceil; unfold HEAPLO in *; eapply (store_ok_sub _ _ _ _ 40%nat); [|exact SOKn| |]; zsimp; lia))
          as (rf & RUN & E10 & Kf).
        apply (MAIN (m_F2 M1 nxf pvf) rf (fun a => (pvf + 8 <= a < pvf + 16) \/ (nxf <= a < nxf + 8) \/ (ctx_free_meta_head <= a < ctx_free_meta_head + 8)) RUN E10 Kf).
        + unfold m_F2. do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
        + intros a Ha NE. ceil; unfold m_F2, ctx_free_meta_head, CTX, HEAPLO in *. wdiff NE M1 a.
        + intros a [W|[W|W]]; [left; split; [exact Hs | left; exact W] | left; split; [exact Hs | right; exact W] | right; exact W].
        + intros _. ceil; unfold cell, m_F2, ctx_free_meta_head, CTX, HEAPLO in *. rdn_peel1.
          destruct Dnp as [E|D].
          * (* [comment removed for export] *) rewrite E. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
          * rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
        + intros _. ceil; unfold cell, m_F2, ctx_free_meta_head, CTX, HEAPLO in *. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
        + rewrite (MhAMeta1.head_l' st L HWF Hnn), Hs. unfold cell, m_F2. apply rdn_wbytes_hit8. unfold ctx_free_meta_head, CTX. zsimp; lia.
    Qed.
  End ArmA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ArmB.
    Hypothesis Hfl : s_flist st = [].
    Hypothesis Hcnt : c_avail_cnt cx > 0.
    #[local] Notation am := (MhAMeta2.m st).

    Lemma arm_B : forall r1, getr r1 2 = Z_to_bv 64 (sp - 64) -> getr r1 19 = Z_to_bv 64 MLOCK -> getr r1 8 = Z_to_bv 64 4096 ->
      getr r1 18 = Z_to_bv 64 A_CANARY -> keeps_but clobI regs r1 ->
      kat RSEGS (mkCfg (mkst r1 (0x626ac%bv : word) M1 rom) mdl) Q.
    Proof.
      intros r1 G2 G19 G8 G18 K1.
      pose proof (MhAMeta2.am_val st L HWF Hcnt) as [AM NE]. pose proof (MhAMeta2.m_U st L HWF Hcnt) as Um.
      pose proof (MhAMeta2.m_rng st L HWF Hcnt) as [R1 R2]. pose proof (MhAMeta2.cnt_rng st L HWF Hcnt) as CR.
      pose proof (rp_ctx st M1 M1_REP) as RC.
      pose proof (rc_fmh st M1 RC) as Cfh. rewrite (wc_fhead st (WF_ctx st L HWF)), Hfl in Cfh. cbn [head_of] in Cfh.
      pose proof (rc_amc st M1 RC) as Ccnt. pose proof (rc_am st M1 RC) as Cam. rewrite AM in Cam.
      pose proof (ctx_store_ok st M1 M1_REP) as SOKc.
      pose proof can_rng as CANR. pose proof Hsp as [S1 S2]. unfold AMSTK in S1. ceil; unfold HEAPLO in R1, R2. unfold NSLOTS in CR.
      destruct (amR M1 am (c_avail_cnt cx) ltac:(lia) ltac:(lia) Cfh Ccnt Cam SOKc r1 rom G19) as (rf & RUN & E10 & Kf).
      set (Mf := m_R M1 am (c_avail_cnt cx)) in RUN.
      assert (Wf : forall a, 0 <= a < 2 ^ 64 -> Mf (Z_to_bv 64 a) <> M1 (Z_to_bv 64 a) -> ctx_avail_meta <= a < ctx_avail_meta + 16).
      { intros a Ha NE0. unfold Mf, m_R, ctx_avail_meta, ctx_avail_meta_count, CTX in *. wdiff NE0 M1 a. }
      assert (Gf : mem_grows M1 Mf) by (unfold Mf, m_R; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
      assert (AGs : forall a n bs, CEIL <= a -> a + Z.of_nat n <= sp -> rdn RSEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn RSEGS Mf (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Ha Hn R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by (ceil; lia); lia|].
        intros x Hx. rewrite u_Z2bv in Hx by (ceil; lia).
        destruct (decide (Mf x = M1 x)) as [E|NE0]; [exact E|]. exfalso. pose proof (u64_range x) as Xr.
        rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl) in NE0.
        pose proof (Wf (bv_unsigned x) ltac:(lia) NE0). ceil; unfold ctx_avail_meta, CTX in *. lia. }
      assert (CANf : rdn RSEGS Mf (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can))).
      { pose proof (rc_canary st M1 (rp_statics st M1 M1_REP)) as C. unfold cell in C. fold can in C. rewrite <- C.
        unfold Mf, m_R, ctx_avail_meta, ctx_avail_meta_count, CTX, A_CANARY. do 2 rdn_peel1. reflexivity. }
      assert (SOKg : store_ok RSEGS Mf (Z_to_bv 64 am) 16%nat = true).
      { eapply store_ok_mono; [exact Gf|]. eapply (store_ok_sub _ _ _ _ 40%nat); [|exact (meta_store_ok st L M1 HWF M1_REP am Um)| |]; zsimp; lia. }
      destruct (amE Mf sp can am (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                  ltac:(lia) ltac:(ceil; unfold HEAPLO; lia) Hra SOKg CANf
                  (AGs (sp - 56) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_can) (AGs (sp - 8) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_ra)
                  (AGs (sp - 16) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s0) (AGs (sp - 24) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s1)
                  (AGs (sp - 32) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s2) (AGs (sp - 40) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s3)
                  (AGs (sp - 48) 8%nat _ ltac:(lia) ltac:(cbn; lia) M1_s4) rf rom ltac:(kept_rw Kf; exact G2) E10 ltac:(kept_rw Kf; exact G18))
        as (r' & RUNE & F2 & F10 & F1 & F8 & F9 & F18 & F19 & F20 & KE).
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN |]. eapply kat_msteps; [exact Hh | exact Hlz | exact RUNE |].
      apply kat_refl. apply HQ.
      set (M' := m_E Mf am).
      assert (WF3 : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
                     (sp - 56 <= a < sp) \/ (am <= a < am + 16) \/ (ctx_avail_meta <= a < ctx_avail_meta + 16)).
      { intros a Ha NE0. destruct (decide (M' (Z_to_bv 64 a) = Mf (Z_to_bv 64 a))) as [E1|NE1].
        - rewrite E1 in NE0. destruct (decide (Mf (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E3|NE3].
          + rewrite E3 in NE0. left. exact (M1_writes a Ha NE0).
          + right; right. exact (Wf a Ha NE3).
        - unfold M', m_E in NE1. right; left. wdiff NE1 Mf a. }
      assert (WFm : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> MhAMeta2.f_wr st spc a).
      { intros a Ha NE0. unfold MhAMeta2.f_wr, spc, AMSTK, MSTK. destruct (WF3 a Ha NE0) as [W|[W|W]]; [left; lia | right; left; exact W | right; right; exact W]. }
      assert (GR : mem_grows M M') by (eapply mem_grows_trans; [exact M1_grows|]; eapply mem_grows_trans; [exact Gf|]; unfold M', m_E; eapply mem_grows_trans; apply wbytes_grows).
      assert (Cm0 : cell M' am 8 0) by (unfold cell, M', m_E; apply rdn_wbytes_hit8; zsimp; lia).
      assert (Cm8 : cell M' (am + 8) 8 0) by (unfold cell, M', m_E; rdn_peel1; apply rdn_wbytes_hit8; zsimp; lia).
      assert (Cam' : cell M' ctx_avail_meta 8 (am + 40)).
      { unfold cell, M', m_E, Mf, m_R, ctx_avail_meta, ctx_avail_meta_count, CTX in *. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      assert (Ccnt' : cell M' ctx_avail_meta_count 8 (c_avail_cnt cx - 1)).
      { unfold cell, M', m_E, Mf, m_R, ctx_avail_meta, ctx_avail_meta_count, CTX in *. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      destruct (fresh_close st L M M' spc HWF HREP Hfl Hcnt ltac:(unfold spc, AMSTK, MSTK; lia) WFm GR Cm0 Cm8 Cam' Ccnt') as [WF' REP'].
      exists (MhAMeta2.st' st), M', mdl, r', am.
      split; [reflexivity|].
      split; [exact WF'|]. split; [exact REP'|]. split; [apply (LEDGERX_same st); [reflexivity | reflexivity | exact HLG]|].
      split; [exact Hh|]. split; [exact Hlz|]. split; [exact Hmat|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [exact Um|]. split; [cbn [s_meta MhAMeta2.st']; exact (MhAMeta2.m_zero st L HWF Hcnt)|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [cbn [s_flist MhAMeta2.st']; rewrite Hfl; reflexivity|].
      split; [intros x Hx; reflexivity|].
      split; [reflexivity|]. split; [left; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros x Hx; reflexivity|].
      split; [intros IN; exact (proj2 (proj2 (proj2 (wG_limbo st L (WF_groups st L HWF) _ IN))) (MhAMeta2.m_fresh st L HWF Hcnt))|].
      split; [intros x Ux; exact Ux|].
      split; [cbn [s_regions MhAMeta2.st']; lia|]. split; [cbn [s_regions MhAMeta2.st']; lia|].
      split; [intros r Hr; left; exists r; split; [exact Hr | split; reflexivity]|].
      split; [exact F10|]. split; [rewrite F2, H2; reflexivity|].
      split.
      { apply (keeps_final_am regs r' (clobI ++ ([10; 11; 12]%bv ++ clobE))).
        - eapply keeps_join; [exact K1|]. eapply keeps_join; [exact Kf | exact KE].
        - reflexivity.
        - exact F1. - rewrite F2, H2; reflexivity. - exact F8. - exact F9. - exact F18. - exact F19. - exact F20.
        - kept_rw KE. kept_rw Kf. kept_rw K1. reflexivity. }
      split.
      { intros a Ha NE0. destruct (WF3 a Ha NE0) as [W|[W|W]].
        - left. unfold AMSTK. lia.
        - right; right; left. destruct (metaU_area st L HWF am Um) as (ar & k & Har & Hk & Hxa & _ & _ & _ & Q1 & Q2 & _).
          destruct (area_in_region st L HWF ar Har) as (rr & Hrr & Hk' & Z1 & Z2). exists rr. cbn [s_regions MhAMeta2.st']. repeat split; try assumption; lia.
        - right; left. unfold ctx_avail_meta, CTX_END, CTX in *. lia. }
      eapply defined_grows; [|exact M1_def]. eapply mem_grows_trans; [exact Gf|]. unfold M', m_E. eapply mem_grows_trans; apply wbytes_grows.
    Qed.
  End ArmB.
End AMS.
