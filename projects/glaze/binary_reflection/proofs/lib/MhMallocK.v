(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhMallocW.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac.MhBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2.
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

(* [comment removed for export] *)
Definition Wbig (n : Z) : Z := Z.lor ((n + 4115) - (n + 4115) mod 2048) 4064.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pro.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp n : Z).
  Hypothesis Hsp : (CEIL + 48 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hn : (0 <= n < 2^40)%Z.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 48)) 48%nat = true.

  Definition mal_frame (ra s0 s1 s2 s3 s4 : word) : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4).

  Definition clobP : list reg := [2; 8; 9; 10; 11]%bv.

  Lemma mPro : forall regs rom,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x628d0 : word) m rom)
                   (mkst regs' (0x62940 : word) (mal_frame (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 8 = Z_to_bv 64 n /\ getr regs' 9 = Z_to_bv 64 MLOCK
      /\ getr regs' 10 = Z_to_bv 64 0x1ffec
      /\ keeps_but clobP regs regs'.
  Proof using SOK Hn Hsp RN.
    intros regs rom H2 H10. ceil; unfold MLOCK in *. unfold mal_frame.
    eexists. split.
    - stepn F_6287c D_6287c. rewrite H2. addi_renorm.
      stepSTx F_62880 D_62880 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(sok 48%nat SOK).
      stepSTx F_62884 D_62884 (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok 48%nat SOK).
      stepSTx F_62888 D_62888 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok 48%nat SOK).
      stepSTx F_6288c D_6288c (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok 48%nat SOK).
      stepSTx F_62890 D_62890 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok 48%nat SOK).
      stepSTx F_62894 D_62894 (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(sok 48%nat SOK).
      stepn F_62898 D_62898.
      stepn F_6289c D_6289c.
      stepn F_628a0 D_628a0. vals_lit.
      stepb_tk F_628a4 D_628a4 ltac:(rewrite H10, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_628d8 D_628d8. rewrite H10.
      stepn F_628dc D_628dc.
      stepn F_628e0 D_628e0. vals_lit.
      stepn F_628e4 D_628e4.
      stepn F_628e8 D_628e8. vals_lit.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End Pro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Big0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (n : Z).
  Hypothesis Hn : (MMAP_THRESHOLD <= n < 2^40)%Z.

  Lemma mBig0 : forall regs rom,
    getr regs 8 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 0x1ffec ->
    exists regs',
      msteps RSEGS (mkst regs (0x62940 : word) m rom) (mkst regs' (0x63c78 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 (n + 20) /\ getr regs' 12 = Z_to_bv 64 3
      /\ getr regs' 13 = Z_to_bv 64 34 /\ getr regs' 14 = Z_to_bv 64 (-1) /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 19 = Z_to_bv 64 (n + 20) /\ getr regs' 18 = Z_to_bv 64 (2^64 - 1) /\ getr regs' 1 = Z_to_bv 64 0x62968
      /\ keeps_but [1; 10; 11; 12; 13; 14; 15; 18; 19]%bv regs regs'.
  Proof using Hn.
    intros regs rom H8 H10. unfold MMAP_THRESHOLD in *.
    eexists. split.
    - stepb_ft F_628ec D_628ec ltac:(rewrite H8, H10, c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepn F_628f0 D_628f0. rewrite H8. addi_renorm.
      stepn F_628f4 D_628f4.
      stepn F_628f8 D_628f8.
      stepn F_628fc D_628fc.
      stepn F_62900 D_62900.
      stepn F_62904 D_62904.
      stepn F_62908 D_62908.
      stepn F_6290c D_6290c.
      stepn F_62910 D_62910.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End Big0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Big1.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (p0 seq : Z).
  Hypothesis Hp0 : (0 <= p0 < 2^64 - 1)%Z.
  Hypothesis Hseq : (0 <= seq < 256)%Z.
  Hypothesis M_nl : rdn RSEGS m (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis M_seq : rdn RSEGS m (Z_to_bv 64 ctx_seq) 1%nat = Some [Z_to_bv 8 seq].
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.

  (* [comment removed for export] *)
  Definition m_S1 : mem := wbytes m (Z_to_bv 64 ctx_seq) (word_to_le_bytes 1 (Z_to_bv 64 (seq + 1))).
  (* [comment removed for export] *)
  Definition m_S2 : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (ctx_unmap_seq 0)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (ctx_unmap_seq 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (ctx_unmap_seq 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (ctx_unmap_seq 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 ctx_seq) (word_to_le_bytes 1 (Z_to_bv 64 1)).

  Ltac pre := unfold ctx_seq, ctx_unmap_seq, CTX, MLOCK, A_NEED_LOCKS in *.

  Lemma mBig1a : forall regs rom,
    getr regs 10 = Z_to_bv 64 p0 -> getr regs 18 = Z_to_bv 64 (2^64 - 1) -> getr regs 9 = Z_to_bv 64 MLOCK -> seq <> 255%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x62968 : word) m rom) (mkst regs' (0x625f8 : word) m_S1 rom)
      /\ getr regs' 20 = Z_to_bv 64 p0 /\ getr regs' 1 = Z_to_bv 64 0x62a5c
      /\ keeps_but [1; 10; 11; 20]%bv regs regs'.
  Proof using SOKc M_seq M_nl Hseq Hp0.
    intros regs rom H10 H18 H9 Hne. pre. unfold m_S1. pre.
    eexists. split.
    - stepb_ft F_62914 D_62914 ltac:(rewrite H10, H18, c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_62918 D_62918. rewrite H10.
      stepn F_6291c D_6291c.
      stepLBU F_62920 D_62920 (Z_to_bv 8 0) ltac:(addr_norm; exact M_nl). vals_lit.
      stepb_tk F_62924 D_62924 ltac:(cond_compute).
      stepLBU F_62934 D_62934 (Z_to_bv 8 seq) ltac:(gres; rewrite ?H9; addr_norm; exact M_seq).
      stepn F_62938 D_62938.
      replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 seq))) with (Z_to_bv 64 seq) by (f_equal; symmetry; apply u8_of_Z; lia).
      stepb_tk F_6293c D_6293c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hne).
      stepn F_629fc D_629fc. addi_renorm.
      stepSTx F_62a00 D_62a00 (Z_to_bv 64 682936) (Z_to_bv 64 (seq + 1)) ltac:(gres; rewrite ?H9; sok 928%nat SOKc).
      stepn F_62a04 D_62a04.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.

  Lemma mBig1b : forall regs rom,
    getr regs 10 = Z_to_bv 64 p0 -> getr regs 18 = Z_to_bv 64 (2^64 - 1) -> getr regs 9 = Z_to_bv 64 MLOCK -> seq = 255%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x62968 : word) m rom) (mkst regs' (0x625f8 : word) m_S2 rom)
      /\ getr regs' 20 = Z_to_bv 64 p0 /\ getr regs' 1 = Z_to_bv 64 0x62a5c
      /\ keeps_but [1; 10; 11; 20]%bv regs regs'.
  Proof using SOKc M_seq M_nl Hseq Hp0.
    intros regs rom H10 H18 H9 Hs. pre. unfold m_S2. pre.
    eexists. split.
    - stepb_ft F_62914 D_62914 ltac:(rewrite H10, H18, c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_62918 D_62918. rewrite H10.
      stepn F_6291c D_6291c.
      stepLBU F_62920 D_62920 (Z_to_bv 8 0) ltac:(addr_norm; exact M_nl). vals_lit.
      stepb_tk F_62924 D_62924 ltac:(cond_compute).
      stepLBU F_62934 D_62934 (Z_to_bv 8 seq) ltac:(gres; rewrite ?H9; addr_norm; exact M_seq).
      stepn F_62938 D_62938.
      replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 seq))) with (Z_to_bv 64 seq) by (f_equal; symmetry; apply u8_of_Z; lia).
      stepb_ft F_6293c D_6293c ltac:(rewrite Hs; cond_compute).
      stepSTx F_62940 D_62940 (Z_to_bv 64 682872) (Z_to_bv 64 0) ltac:(gres; rewrite ?H9; sok 928%nat SOKc).
      stepSTx F_62944 D_62944 (Z_to_bv 64 682880) (Z_to_bv 64 0) ltac:(gres; rewrite ?H9; sok 928%nat SOKc).
      stepSTx F_62948 D_62948 (Z_to_bv 64 682888) (Z_to_bv 64 0) ltac:(gres; rewrite ?H9; sok 928%nat SOKc).
      stepSTx F_6294c D_6294c (Z_to_bv 64 682896) (Z_to_bv 64 0) ltac:(gres; rewrite ?H9; sok 928%nat SOKc).
      stepn F_62950 D_62950.
      stepn F_62954 D_62954.
      stepSTx F_62a00 D_62a00 (Z_to_bv 64 682936) (Z_to_bv 64 1) ltac:(gres; rewrite ?H9; sok 928%nat SOKc).
      stepn F_62a04 D_62a04.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End Big1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Big2.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g p0 n ctr : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hp0 : (HEAPLO <= p0)%Z /\ (p0 + 16 <= CEIL)%Z /\ ((p0 + 16 <= IMG_LO)%Z \/ (IMG_HI <= p0)%Z).
  Hypothesis Hn : (0 <= n < 2^40)%Z.
  Hypothesis Hctr : (0 <= ctr < 2^32)%Z.
  Hypothesis SOKg : store_ok RSEGS m (Z_to_bv 64 g) 40%nat = true.
  Hypothesis SOKp : store_ok RSEGS m (Z_to_bv 64 p0) 8%nat = true.
  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.
  Hypothesis M_ctr : rdn RSEGS m (Z_to_bv 64 ctx_mmap_counter) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ctr)).
  Hypothesis Hgp : (g + 40 <= p0 \/ p0 + 8 <= g)%Z.

  Definition m_B2 : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (g + 16)) (word_to_le_bytes 8 (Z_to_bv 64 p0)))
      (Z_to_bv 64 p0) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 (g + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (Wbig n))))
      (Z_to_bv 64 (g + 28)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (g + 24)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 ctx_mmap_counter) (word_to_le_bytes 4 (Z_to_bv 64 ((ctr + 1) mod 2 ^ 32))).

  Lemma land_hi_mask : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 2048) = (x - x mod 2048)%Z.
  Proof using Hctr Hn ctr n.
    intros x Hx.
    replace (2 ^ 64 - 2048)%Z with (Z.land (Z.ones 64) (Z.lnot (Z.ones 11))) by reflexivity.
    rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
    rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 11)%Z with 2048%Z.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


  Lemma Wbig_val : v_or (v_andi (Z_to_bv 64 (n + 4115)) (-2048)) (Z_to_bv 64 4064) = Z_to_bv 64 (Wbig n).
  Proof using Hctr Hn ctr.
    unfold v_or, v_andi. f_equal.
    assert (E1 : bv_unsigned (Z_to_bv 64 (n + 4115)) = (n + 4115)%Z) by (rewrite u_Z2bv; lia).
    assert (E2 : bv_wrap 64 (-2048) = (2 ^ 64 - 2048)%Z) by reflexivity.
    rewrite E1, E2, land_hi_mask by lia.
    assert (M1 : (0 <= (n + 4115) mod 2048 < 2048)%Z) by (apply Z.mod_pos_bound; lia).
    rewrite u_Z2bv by lia. change (bv_unsigned (Z_to_bv 64 4064)) with 4064%Z. reflexivity.
  Qed.

  Lemma mBig2 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 20 = Z_to_bv 64 p0 -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 MLOCK ->
    exists regs',
      msteps RSEGS (mkst regs (0x62a5c : word) m rom) (mkst regs' (0x6f734 : word) m_B2 rom)
      /\ getr regs' 18 = Z_to_bv 64 g /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 MLOCK
      /\ getr regs' 20 = v_lw (Z_to_bv 64 ((ctr + 1) mod 2 ^ 32)) /\ getr regs' 1 = Z_to_bv 64 0x62c00
      /\ keeps_but [1; 10; 11; 18; 19; 20]%bv regs regs'.
  Proof using M_ctr SOKc SOKp SOKg Hctr Hn Hp0 Hg RN.
    intros regs rom H10 H20 H8 H9. ceil; unfold HEAPLO, ctx_mmap_counter, CTX, MLOCK in *. unfold m_B2, ctx_mmap_counter, CTX.
    eexists. split.
    - stepb_ft F_62a08 D_62a08 ltac:(rewrite H10, c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_62a0c D_62a0c. rewrite H10.
      stepn F_62a10 D_62a10.
      stepSTx F_62a14 D_62a14 (Z_to_bv 64 (g + 16)) (Z_to_bv 64 p0) ltac:(gres; rewrite ?H10; sok 40%nat SOKg).
      stepSTx F_62a18 D_62a18 (Z_to_bv 64 p0) (Z_to_bv 64 g) ltac:(gres; rewrite ?H20; store_ok_peel; exact SOKp).
      stepn F_62a1c D_62a1c.
      stepn F_62a20 D_62a20. vals_lit.
      stepn F_62a24 D_62a24. rewrite H8. rewrite v_add_ZZ by lia.
      stepn F_62a28 D_62a28. addi_renorm. replace (n + 4064 + 51)%Z with (n + 4064 + 51)%Z by lia.
      stepn F_62a2c D_62a2c.
      stepn F_62a30 D_62a30. rewrite Wbig_val.
      stepSTx F_62a34 D_62a34 (Z_to_bv 64 (g + 32)) (Z_to_bv 64 (Wbig n)) ltac:(sok 40%nat SOKg).
      stepSTx F_62a38 D_62a38 (Z_to_bv 64 (g + 28)) (Z_to_bv 64 0) ltac:(sok 40%nat SOKg).
      stepSTx F_62a3c D_62a3c (Z_to_bv 64 (g + 24)) (Z_to_bv 64 0) ltac:(sok 40%nat SOKg).
      stepLD F_62a40 D_62a40 (word_to_le_bytes 4 (Z_to_bv 64 ctr)) (Z_to_bv 64 ctr)
        ltac:(gres; rewrite ?H9; addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_62a44 D_62a44.
      stepSTx F_62a48 D_62a48 (Z_to_bv 64 682036) (v_addi (s32 ctr) 1) ltac:(gres; rewrite ?H9; sok 928%nat SOKc).
      rewrite (w2le4_low (v_addi (s32 ctr) 1) ((ctr + 1) mod 2 ^ 32)).
      2:{ apply Z.mod_pos_bound. lia. }
      2:{ unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite u_s32.
          rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2^32)%Z; reflexivity].
          rewrite <- Zplus_mod_idemp_l, sx32_mod, Zplus_mod_idemp_l. reflexivity. }
      stepn F_62a4c D_62a4c.
      stepLD F_62ba0 D_62ba0 (word_to_le_bytes 4 (Z_to_bv 64 ((ctr + 1) mod 2 ^ 32))) (Z_to_bv 64 ((ctr + 1) mod 2 ^ 32))
        ltac:(gres; rewrite ?H9; addr_norm; pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 ((ctr + 1) mod 2 ^ 32)))) as RH;
              rewrite length_N_to_le_bytes in RH; apply RH; zsimp; lia)
        ltac:(pose proof (Z.mod_pos_bound (ctr + 1) (2 ^ 32) ltac:(lia)); apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_62ba4 D_62ba4. rewrite H9.
      stepn F_62ba8 D_62ba8.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End Big2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section U.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variable m : mem.
  Hypothesis M_lk : rdn RSEGS m (Z_to_bv 64 MLOCK) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Lemma mU : forall regs rom (ra : word),
    getr regs 10 = Z_to_bv 64 MLOCK -> getr regs 1 = ra -> ret_ok ra ->
    exists regs',
      msteps RSEGS (mkst regs (0x6f734 : word) m rom) (mkst regs' ra m rom)
      /\ keeps_but [11]%bv regs regs'.
  Proof using M_lk.
    intros regs rom ra H10 H1 Hra. unfold MLOCK in *.
    eexists. split.
    - stepLD F_6f6e0 D_6f6e0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(gres; rewrite ?H10; addr_norm; exact M_lk) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      vals_lit.
      stepb_ft F_6f6e4 D_6f6e4 ltac:(cond_compute).
      stepret F_6f6e8 D_6f6e8 ra ltac:(rewrite H1; reflexivity).
      pu_refl.
    - solve_keeps_but.
  Qed.
End U.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Big3.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp : Z) (ra s0v s1v s2v s3v s4v : word).
  Hypothesis Hsp : (CEIL + 48 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).
  Hypothesis M_s4 : rdn RSEGS m (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 s4v).

  Lemma mBig3 : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 48) ->
    exists regs',
      msteps RSEGS (mkst regs (0x62c00 : word) m rom) (mkst regs' (0x634e4 : word) m rom)
      /\ getr regs' 10 = getr regs 18 /\ getr regs' 11 = getr regs 19 /\ getr regs' 12 = getr regs 8 /\ getr regs' 13 = getr regs 20
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20]%bv regs regs'.
  Proof using M_s4 M_s3 M_s2 M_s1 M_s0 M_ra Hsp RN.
    intros regs rom H2. ceil.
    eexists. split.
    - stepn F_62bac D_62bac.
      stepn F_62bb0 D_62bb0.
      stepn F_62bb4 D_62bb4.
      stepn F_62bb8 D_62bb8.
      stepLD8 F_62bbc D_62bbc ra.
      stepLD8 F_62bc0 D_62bc0 s0v.
      stepLD8 F_62bc4 D_62bc4 s1v.
      stepLD8 F_62bc8 D_62bc8 s2v.
      stepLD8 F_62bcc D_62bcc s3v.
      stepLD8 F_62bd0 D_62bd0 s4v.
      stepn F_62bd4 D_62bd4. rewrite H2. addi_renorm.
      stepn F_62bd8 D_62bd8.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End Big3.
End MhMallocW.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhMallocKT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac MhMallocW OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2.
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

Section T.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  (* [comment removed for export] *)
  Variables (m : mem) (sp : Z) (ra s0v s1v s2v s3v s4v : word).
  Hypothesis Hsp : (CEIL + 48 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).
  Hypothesis M_s4 : rdn RSEGS m (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 s4v).

  Definition clob0 : list reg := [1; 2; 8; 9; 10; 11; 18; 19; 20]%bv.

  Ltac epi0 H2 :=
    stepn F_628b4 D_628b4;
    stepLD8 F_628b8 D_628b8 ra;
    stepLD8 F_628bc D_628bc s0v;
    stepLD8 F_628c0 D_628c0 s1v;
    stepLD8 F_628c4 D_628c4 s2v;
    stepLD8 F_628c8 D_628c8 s3v;
    stepLD8 F_628cc D_628cc s4v;
    stepn F_628d0 D_628d0; rewrite H2; addi_renorm;
    stepret F_628d4 D_628d4 ra ltac:(reflexivity).

  (* [comment removed for export] *)
  Lemma mEpi0 : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 48) ->
    exists regs',
      msteps RSEGS (mkst regs (0x62908 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but clob0 regs regs'.
  Proof using M_s4 M_s3 M_s2 M_s1 M_s0 M_ra Hra Hsp RN.
    intros regs rom H2. ceil.
    eexists. split.
    - epi0 H2. pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma tY1 : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 (2^64 - 1) -> getr regs 18 = Z_to_bv 64 (2^64 - 1) ->
    exists regs',
      msteps RSEGS (mkst regs (0x62968 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but clob0 regs regs'.
  Proof using M_s4 M_s3 M_s2 M_s1 M_s0 M_ra Hra Hsp RN.
    intros regs rom H2 H10 H18. ceil.
    eexists. split.
    - stepb_tk F_62914 D_62914 ltac:(rewrite H10, H18; apply c_eq_refl).
      epi0 H2. pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Hypothesis M_lk : rdn RSEGS m (Z_to_bv 64 MLOCK) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Lemma tM1 : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 (2^64 - 1) ->
    exists regs',
      msteps RSEGS (mkst regs (0x62be0 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but clob0 regs regs'.
  Proof using M_lk M_s4 M_s3 M_s2 M_s1 M_s0 M_ra Hra Hsp RN.
    intros regs rom H2 H10. ceil; unfold MLOCK in *.
    assert (R1 : exists r1, msteps RSEGS (mkst regs (0x62be0 : word) m rom) (mkst r1 (0x6f734 : word) m rom)
                            /\ getr r1 10 = Z_to_bv 64 MLOCK /\ getr r1 1 = (0x62c3c : word) /\ keeps_but [1; 10]%bv regs r1).
    { eexists. split.
      - stepb_tk F_62b8c D_62b8c ltac:(rewrite H10; cond_compute).
        stepn F_62bdc D_62bdc.
        stepn F_62be0 D_62be0.
        stepn F_62be4 D_62be4.
        pu_refl.
      - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity). all: solve_keeps_but. }
    destruct R1 as (r1 & RUN1 & A10 & A1 & K1).
    destruct (mU m M_lk r1 rom (0x62c3c : word) A10 A1 ltac:(apply ret_ok_even; reflexivity)) as (r2 & RUN2 & K2).
    assert (B2 : getr r2 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K2; kept_rw K1; exact H2).
    destruct (mEpi0 r2 rom B2) as (r3 & RUN3 & E2 & E10 & E1 & E8 & E9 & E18 & E19 & E20 & K3).
    assert (RUNj : msteps RSEGS (mkst r2 (0x62c3c : word) m rom) (mkst r2 (0x62908 : word) m rom)).
    { stepn F_62be8 D_62be8. pu_refl. }
    exists r3. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUNj|]. exact RUN3.
    - repeat split; try assumption.
      eapply keeps_but_trans; [eapply keeps_but_mono; [exact K1|] |].
      { intros r Hr. apply in_regs_dec. cbn in Hr. destruct Hr as [<-|[<-|[]]]; reflexivity. }
      eapply keeps_but_trans; [eapply keeps_but_mono; [exact K2|] | exact K3].
      intros r Hr. apply in_regs_dec. cbn in Hr. destruct Hr as [<-|[]]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma tY2a : forall regs rom (p len : Z),
    getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 len ->
    exists regs',
      msteps RSEGS (mkst regs (0x62a5c : word) m rom) (mkst regs' (0x63e80 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 10 = Z_to_bv 64 p /\ getr regs' 11 = Z_to_bv 64 len
      /\ getr regs' 1 = (0x62b34 : word)
      /\ keeps_but [1; 10; 11]%bv regs regs'.
  Proof using M_lk RN.
    intros regs rom p len H2 H10 H20 H19. ceil; unfold MLOCK in *.
    assert (R1 : exists r1, msteps RSEGS (mkst regs (0x62a5c : word) m rom) (mkst r1 (0x6f734 : word) m rom)
                            /\ getr r1 10 = Z_to_bv 64 MLOCK /\ getr r1 1 = (0x62b28 : word) /\ keeps_but [1; 10]%bv regs r1).
    { eexists. split.
      - stepb_tk F_62a08 D_62a08 ltac:(rewrite H10; apply c_eq_refl).
        stepn F_62ac8 D_62ac8.
        stepn F_62acc D_62acc.
        stepn F_62ad0 D_62ad0.
        pu_refl.
      - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity). all: solve_keeps_but. }
    destruct R1 as (r1 & RUN1 & A10 & A1 & K1).
    destruct (mU m M_lk r1 rom (0x62b28 : word) A10 A1 ltac:(apply ret_ok_even; reflexivity)) as (r2 & RUN2 & K2).
    eexists. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepn F_62ad4 D_62ad4. kept_rw K2. kept_rw K1. rewrite H20.
      stepn F_62ad8 D_62ad8. kept_rw K2. kept_rw K1. rewrite H19.
      stepn F_62adc D_62adc.
      pu_refl.
    - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity).
      + kept_rw K2. kept_rw K1. exact H2.
      + eapply keeps_but_trans; [eapply keeps_but_mono; [exact K1|] |].
        { intros r Hr. apply in_regs_dec. cbn in Hr. destruct Hr as [<-|[<-|[]]]; reflexivity. }
        eapply keeps_but_trans; [eapply keeps_but_mono; [exact K2|] |].
        { intros r Hr. apply in_regs_dec. cbn in Hr. destruct Hr as [<-|[]]; reflexivity. }
        solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma tY2b : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 48) ->
    exists regs',
      msteps RSEGS (mkst regs (0x62b34 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but clob0 regs regs'.
  Proof using M_s4 M_s3 M_s2 M_s1 M_s0 M_ra Hra Hsp RN.
    intros regs rom H2. ceil.
    eexists. split.
    - stepn F_62ae0 D_62ae0.
      epi0 H2. pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Munmap.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  (* [comment removed for export] *)
  Variables (m : mem) (sp p len : Z).
  Hypothesis Hsp : (CEIL + 32 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hp : (0 <= p < 2^64)%Z.
  Hypothesis Hlen : (0 <= len < 2^64)%Z.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 32)) 32%nat = true.

  Definition mu_frame (ra s0v s1v : word) : mem :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v).

  Lemma mUnm1 : forall regs rom,
    getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 len ->
    exists regs',
      msteps RSEGS (mkst regs (0x63e80 : word) m rom)
                   (mkst regs' (0x63ea8 : word) (mu_frame (getr regs 1) (getr regs 8) (getr regs 9)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 32) /\ getr regs' 17 = Z_to_bv 64 215
      /\ getr regs' 10 = Z_to_bv 64 p /\ getr regs' 11 = Z_to_bv 64 len
      /\ getr regs' 8 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 p
      /\ keeps_but [1; 2; 8; 9; 10; 11; 17]%bv regs regs'.
  Proof using SOK Hsp RN.
    intros regs rom H2 H10 H11. ceil. unfold mu_frame.
    eexists. split.
    - stepn F_63e2c D_63e2c. rewrite H2. addi_renorm.
      stepSTx F_63e30 D_63e30 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(sok 32%nat SOK).
      stepSTx F_63e34 D_63e34 (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok 32%nat SOK).
      stepSTx F_63e38 D_63e38 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok 32%nat SOK).
      stepn F_63e3c D_63e3c. rewrite H11.
      stepn F_63e40 D_63e40. rewrite H10.
      stepn F_63e44 D_63e44.
      stepret F_63c20 D_63c20 (Z_to_bv 64 0x63e9c) ltac:(reflexivity).
      stepn F_63e48 D_63e48.
      stepn F_63e4c D_63e4c.
      stepn F_63e50 D_63e50.
      pu_refl.
    - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity). all: try (f_equal; lia). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma mUnm2 : forall regs rom (m' : mem) ra s0v s1v,
    ret_ok ra ->
    getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
    rdn RSEGS m' (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
    exists regs',
      msteps RSEGS (mkst regs (0x63eac : word) m' rom) (mkst regs' ra m' rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ keeps_but [1; 2; 8; 9; 10; 11]%bv regs regs'.
  Proof using Hsp RN.
    intros regs rom m' ra s0v s1v Hra H2 H10 M1 M2 M3. ceil.
    eexists. split.
    - stepn F_63e58 D_63e58.
      stepn F_618e4 D_618e4.
      stepn F_618e8 D_618e8.
      stepb_tk F_618ec D_618ec ltac:(rewrite H10; cond_compute).
      stepret F_61918 D_61918 (Z_to_bv 64 0x63eb0) ltac:(reflexivity).
      stepn F_63e5c D_63e5c. rewrite H10.
      stepLD8 F_63e60 D_63e60 ra.
      stepLD8 F_63e64 D_63e64 s0v.
      stepLD8 F_63e68 D_63e68 s1v.
      stepn F_63e6c D_63e6c. rewrite H2. addi_renorm.
      stepret F_63e70 D_63e70 ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (apply bv_eq; reflexivity). all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End Munmap.
End MhMallocKT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKN OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhCount OSSVerify.Proofs.glaze.binary_reflection.lib.MhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTake OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotK. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKN.MhEnframe OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA.MhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhCount.MhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.MhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhCtz OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac.MhBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhSzc OSSVerify.Proofs.glaze.binary_reflection.lib.MhTake OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA.MhEfh OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS.MhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA.MhASpec3 MhMallocW OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhMallocH OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKN OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotK MhMallocKT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inCS := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Definition SSTK : Z := 48 + ASSTK 6.

Lemma dbound_le6 : forall s, 16 <= s -> (dbound s <= 6)%nat.
Proof.
  intros s Hs. unfold dbound.
  assert (X : 2064 / (s + 16) < 65).
  { apply Z.div_lt_upper_bound; lia. }
  destruct (Z.le_gt_cases (2064 / (s + 16)) 0) as [Z0|P0].
  - rewrite Z.log2_nonpos by lia. lia.
  - assert (Z.log2 (2064 / (s + 16)) <= Z.log2 64) by (apply Z.log2_le_mono; lia). change (Z.log2 64) with 6 in H. lia.
Qed.

Section Spec.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Definition cs_same (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
    getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\
    getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\
    getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

  (* [comment removed for export] *)
  Definition m_wr (stk : Z) (L : list (Z * Z)) (sp a : Z) : Prop :=
    (sp - stk <= a < sp) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/ (CTX <= a < CTX_END) \/ (A_ERRNO <= a < A_ERRNO + 4).

  (* [comment removed for export] *)
  Definition malloc_postk (stk : Z) (L : list (Z * Z)) (n sp : Z) (regs : bvmap 5 word) (M : mem) (mdl : Model)
             (rom : word -> option byte) (c' : config) : Prop :=
    exists regs' M' mdl' (p : Z) st',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      cs_same regs regs' /\ getr regs' 10 = Z_to_bv 64 p /\
      p mod 16 = 0 /\ HEAPLO + 16 <= p /\ p + n <= CEIL /\ (p + n <= IMG_LO \/ IMG_HI <= p) /\ ~ In (p, n) L /\
      (forall b k, In (b, k) L -> p + n <= b \/ b + k <= p) /\
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> m_wr stk L sp a) /\
      defined M' (sp - stk) sp /\ defined M' p (p + n) /\
      WF st' ((p, n) :: L) /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\ nojunk st' /\ nolimbo st' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\
      vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl).

  (* [comment removed for export] *)
  Definition malloc_failk (stk : Z) (L : list (Z * Z)) (sp : Z) (regs : bvmap 5 word) (M : mem) (mdl : Model)
             (rom : word -> option byte) (c' : config) : Prop :=
    exists regs' M' mdl' st',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      cs_same regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> m_wr stk L sp a) /\
      defined M' (sp - stk) sp /\
      WF st' L /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\ nojunk st' /\ nolimbo st' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\
      vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl).

  (* [comment removed for export] *)
  Definition malloc_postkX (PX : mst -> Prop) (stk : Z) (L : list (Z * Z)) (n sp : Z) (regs : bvmap 5 word) (M : mem) (mdl : Model)
             (rom : word -> option byte) (c' : config) : Prop :=
    exists regs' M' mdl' (p : Z) st',
      c' = mkCfg (mkst regs' (getr regs 1) M' rom) mdl' /\
      cs_same regs regs' /\ getr regs' 10 = Z_to_bv 64 p /\
      p mod 16 = 0 /\ HEAPLO + 16 <= p /\ p + n <= CEIL /\ (p + n <= IMG_LO \/ IMG_HI <= p) /\ ~ In (p, n) L /\
      (forall b k, In (b, k) L -> p + n <= b \/ b + k <= p) /\
      (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> m_wr stk L sp a) /\
      defined M' (sp - stk) sp /\ defined M' p (p + n) /\
      WF st' ((p, n) :: L) /\ REP st' M' /\ LEDGER st' (m_vmmaps mdl') /\ nojunk st' /\ nolimbo st' /\
      m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\
      m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl /\
      vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) /\ PX st'.

  Lemma postkX_postk : forall PX stk L n sp regs M mdl rom c',
    malloc_postkX PX stk L n sp regs M mdl rom c' -> malloc_postk stk L n sp regs M mdl rom c'.
  Proof.
    intros PX stk L n sp regs M mdl rom c' (regs' & M' & mdl' & p & st' & X). exists regs', M', mdl', p, st'.
    repeat match goal with |- _ /\ _ => split; [apply (proj1 X) | apply proj2 in X] end. exact (proj1 X).
  Qed.
End Spec.

Section Small.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model) (regs : bvmap 5 word) (rom : word -> option byte).
  Variables (n sp : Z) (F : kfam) (bo : bool).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypothesis HAS : forall d, AS_SPEC3 d.
  Hypothesis SIDE : bo = true -> agf st.
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGER st (m_vmmaps mdl).
  Hypothesis NJ : nojunk st.
  Hypothesis NLB : nolimbo st.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis HBUD : PHI L + MBASE <= vm_limit (m_vmmaps mdl).
  Hypothesis HLL : Z.of_nat (length L) + 1 <= LMAX.
  Hypothesis Hn : 1 <= n < MMAP_THRESHOLD.
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 n.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis R4 : getr regs 4 = Z_to_bv 64 TPV.
  Hypothesis Hsp : CEIL + SSTK <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - SSTK) sp.
  Variable PX : mst -> Prop.
  Hypothesis HQ : forall c', malloc_postkX PX SSTK L n sp regs M mdl rom c' -> Kok F c'.
  Hypothesis HQF : forall c', malloc_failk SSTK L sp regs M mdl rom c' -> Kf F c'.

  (* [comment removed for export] *)
  Lemma HCLS : forall (m : mem) (s : mst) sc0 rr, WF s L -> REP s m -> 0 <= sc0 < 48 ->
    getr rr 20 = Z_to_bv 64 sc0 -> getr rr 9 = Z_to_bv 64 MLOCK ->
    exists rr' sc, msteps RSEGS (mkst rr (0x62adc%bv : word) m rom) (mkst rr' (0x62b98%bv : word) m rom) /\
      0 <= sc < 48 /\ (sc = sc0 \/ (sc = sc0 + 1 /\ sc0 mod 2 = 0 /\ 4 <= sc0 < 32 /\ sc0 <> 6)) /\
      getr rr' 20 = Z_to_bv 64 sc /\ getr rr' 18 = Z_to_bv 64 (head_of (s_alist s sc)) /\
      getr rr' 10 = (if head_of (s_alist s sc) =? 0 then Z_to_bv 64 0 else s32 (mr_avail (s_meta s (head_of (s_alist s sc))))) /\
      keeps_but clobCls rr rr'.
  Proof.
    intros m s sc0' rr W RP Hsc0 G20 G9.
    assert (HD : forall c, 0 <= c < 48 -> head_of (s_alist s c) <> 0 -> is_group s (head_of (s_alist s c)) /\ HEAPLO + 24 <= head_of (s_alist s c) /\ head_of (s_alist s c) + 40 <= CEIL).
    { intros c Hc NZ. destruct (head_facts L c s _ W eq_refl NZ) as (rest & Hl & Hg & _).
      destruct (member_facts L c s _ W ltac:(rewrite Hl; left; reflexivity)) as (_ & _ & _ & A & B). repeat split; assumption. }
    destruct (mCls m (fun c => head_of (s_alist s c)) (c_usage (s_ctx s)) (fun c => mr_avail (s_meta s (head_of (s_alist s c))))
                   (fun c => mr_freed (s_meta s (head_of (s_alist s c))))
                   ltac:(intros c Hc; cbv beta; rewrite <- (wc_active s (WF_ctx s L W) c Hc); exact (rc_active s m (rp_ctx s m RP) c Hc))
                   ltac:(intros c Hc; exact (rc_usage s m (rp_ctx s m RP) c Hc))
                   ltac:(intros c Hc; cbv beta; destruct (Z.eq_dec (head_of (s_alist s c)) 0) as [E|NZ]; [rewrite E; lia|]; destruct (HD c Hc NZ) as (_ & A & B); ceil; unfold HEAPLO in *; lia)
                   ltac:(intros c Hc; exact (wc_usage s (WF_ctx s L W) c))
                   ltac:(intros c Hc NZ; cbv beta; destruct (HD c Hc NZ) as (Hg & _ & _); pose proof (wG_each s L (WF_groups s L W) _ Hg) as WG;
                         destruct (G_meta_cells s L m W RP _ Hg) as (ar1 & k1 & _ & _ & _ & _ & _ & _ & _ & RM1 & _ & _);
                         split; [exact (wg_avr s L _ WG)|]; split; [exact (wg_frr s L _ WG)|]; split; [exact (rm_avail m _ _ RM1) | exact (rm_freed m _ _ RM1)])
                   sc0' rr rom Hsc0 G20 G9) as (rr' & sc & RUN & Hsc & CLS & E20 & E18 & E10 & K).
    exists rr', sc. cbv beta in E18, E10. split; [exact RUN|]. split; [exact Hsc|]. split; [exact CLS|]. split; [exact E20|]. split; [exact E18|]. split; [exact E10 | exact K].
  Qed.

  Definition sc0 : Z := size_to_class n.
  Lemma sc0_rng : 0 <= sc0 < 48. Proof. exact (size_to_class_rng n ltac:(lia)). Qed.
  Lemma sc0_fits : n + 4 <= 16 * size_class sc0. Proof. exact (size_to_class_fits n ltac:(lia)). Qed.
  Lemma SSTK_val : SSTK = 1200. Proof. reflexivity. Qed.

  Definition M1 : mem := mal_frame M sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20).
  Lemma M1_writes : forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sp - 48 <= a < sp.
  Proof. intros a Ha NE. ceil; unfold M1, mal_frame, SSTK, ASSTK, AMSTK in *. wdiff NE M a. Qed.
  Lemma M1_grows : mem_grows M M1.
  Proof. unfold M1, mal_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma M1_REP : REP st M1.
  Proof. apply (REP_frame st L M HWF HREP M1 M1_grows). intros a Hr NE. left. pose proof (M1_writes a Hr NE). ceil; unfold SSTK, ASSTK, AMSTK in *. lia. Qed.
  Lemma M1_def : defined M1 (sp - SSTK) sp.
  Proof. unfold M1, mal_frame. repeat apply defined_wbytes. exact DEF. Qed.

  (* [comment removed for export] *)
  Lemma small_tail : forall s (Mx : mem) mdlx rr (sc g idx : Z),
    WF s L -> REP s Mx -> LEDGER s (m_vmmaps mdlx) -> s_limbo s = [] ->
    m_halted mdlx = None -> m_vm_lazy mdlx = [] -> m_vm_materialized mdlx = [] ->
    m_fs mdlx = m_fs mdl -> m_fds mdlx = m_fds mdl -> vm_limit (m_vmmaps mdlx) = vm_limit (m_vmmaps mdl) ->
    0 <= sc < 48 -> (sc = sc0 \/ (sc = sc0 + 1 /\ sc0 mod 2 = 0 /\ 4 <= sc0 < 32 /\ sc0 <> 6)) ->
    head_of (s_alist s sc) = g -> is_group s g -> g_sc s g = sc -> 0 <= idx <= g_lastidx s g ->
    s_slot s g idx = SJunk 0 -> only_junk s g idx -> n + 4 <= g_stride s g ->
    (forall a, 0 <= a < 2 ^ 64 -> Mx (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> m_wr SSTK L sp a) ->
    defined Mx (sp - SSTK) sp ->
    (forall y, sp - 48 <= y < sp -> Mx (Z_to_bv 64 y) = M1 (Z_to_bv 64 y)) ->
    getr rr 19 = Z_to_bv 64 idx -> getr rr 18 = Z_to_bv 64 g -> getr rr 9 = Z_to_bv 64 MLOCK -> getr rr 8 = Z_to_bv 64 n -> getr rr 2 = Z_to_bv 64 (sp - 48) ->
    keeps_but (AS_CLOB ++ [1; 2; 8; 9; 18; 19; 20]%bv) regs rr ->
    (forall off, PX (MhEnfr.st' s g idx n off)) ->
    kat RSEGS (mkCfg (mkst rr (0x62bf4%bv : word) Mx rom) mdlx) (kfx F false).
  Proof.
    intros s Mx mdlx rr sc g idx W RP LG NL Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hsc CLS Hhd Hg Hgsc Hidx Hsl OJ Hstr FRx DFx STKx T19 T18 T9 T8 T2 K HPX.
    pose proof (wG_each s L (WF_groups s L W) g Hg) as WG. pose proof (glast_rng s g) as GL.
    pose proof (wg_stride s L g WG) as [S16 Smod]. pose proof (wg_q s L g WG ltac:(lia)) as Q20. pose proof (wg_mem s L g WG) as (GM1 & GM2 & GM3).
    ceil; unfold SSTK, ASSTK, AMSTK in Hsp. cbn in Hsp.
    set (ctr := c_mmap_ctr (s_ctx s)). pose proof (wc_ctr s (WF_ctx s L W)) as CTR. fold ctr in CTR.
    pose proof (rc_ctr s Mx (rp_ctx s Mx RP)) as Cctr. fold ctr in Cctr.
    (* [comment removed for export] *)
    destruct (mTail Mx ctr CTR Cctr rr rom T9) as (r1 & RUN1 & E20 & E10 & E1 & K1).
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN1 |].
    pose proof (rc_lock s Mx (rp_statics s Mx RP)) as Mlk.
    destruct (mU Mx Mlk r1 rom (Z_to_bv 64 0x62c00) E10 E1 ltac:(apply ret_ok_even; reflexivity)) as (r2 & RUN2 & K2).
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN2 |].
    replace (Z_to_bv 64 0x62c00) with (0x62c00%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (STK : forall dd v, 8 <= dd <= 48 -> rdn RSEGS M1 (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                  rdn RSEGS Mx (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros dd v Hd R. rewrite (rdn_agreeZ M1 Mx (sp - dd) 8 ltac:(lia) ltac:(cbn; lia)); [exact R|]. intros y Hy. apply STKx. cbn in Hy. lia. }
    assert (G2 : getr r2 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K2; kept_rw K1; exact T2).
    destruct (mBig3 Mx sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(ceil; lia)
                (STK 8 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK 16 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                (STK 24 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK 32 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                (STK 40 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK 48 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                r2 rom G2) as (r3 & RUN3 & I10 & I11 & I12 & I13 & I2 & I1 & I8 & I9 & I18 & I19 & I20 & K3).
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN3 |].
    (* [comment removed for export] *)
    set (cT := getr r3 13).
    destruct (efH_junk s L Mx W RP g idx n cT Hg Hidx ltac:(lia) ltac:(lia) Hstr) as (h3 & o16 & EFH).
    set (strideT := g_stride s g) in *. set (startT := g_slot_start s g idx) in *.
    set (offT := enframe_off (slack_of strideT n) ((if h3 =? 0 then bv_unsigned cT else o16 + 1) mod 256)) in *.
    assert (I10' : getr r3 10 = Z_to_bv 64 g) by (rewrite I10; kept_rw K2; kept_rw K1; exact T18).
    assert (I11' : getr r3 11 = Z_to_bv 64 idx) by (rewrite I11; kept_rw K2; kept_rw K1; exact T19).
    assert (I12' : getr r3 12 = Z_to_bv 64 n) by (rewrite I12; kept_rw K2; kept_rw K1; exact T8).
    destruct (ref_enframe r3 Mx rom (getr regs 1) cT g (g_mem s g) (g_W s g) idx n h3 o16 strideT startT offT EFH I1 Rra I10' I11' I12' eq_refl)
      as (r4 & M4 & RUN4 & KCS & J10 & FRM & POST).
    eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN4 |].
    destruct FRM as [FR4 G4].
    pose proof (slot_in_span s L W g idx Hg Hidx) as [SP1 SP2]. fold startT in SP1.
    assert (Ese : g_slot_end s g idx = startT + strideT - 4) by (unfold g_slot_end, IB; reflexivity). rewrite Ese in SP2.
    destruct (group_range s L W g Hg) as [GR1 GR2].
    assert (M4W : forall a, 0 <= a < 2 ^ 64 -> M4 (Z_to_bv 64 a) <> Mx (Z_to_bv 64 a) -> startT - 3 <= a < startT + strideT - 4).
    { intros a Ha NE. destruct (decide (startT - 3 <= a < startT + strideT - 4)) as [IN|OUT]; [exact IN|]. exfalso. apply NE. apply FR4.
      cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u64_lit by (ceil; lia). lia. }
    (* [comment removed for export] *)
    assert (HX : g_sc s g < 48 -> s_kind s g = GTop -> g_lastidx s g = 0 -> size_class (g_sc s g) <= 255 -> strideT - 4 - n < 16 * size_class (g_sc s g)).
    { intros S48 KT L0 S255. subst strideT.
      pose proof (wg_single s L g WG KT S48 L0) as SG. unfold UNIT in SG. rewrite Hgsc in *.
      destruct SG as [U|[E1' E2']]; [lia|].
      pose proof (hx_malloc n sc0 sc ltac:(lia) eq_refl CLS E2' S255) as HXM.
      pose proof (wg_kind s L g WG) as KD. rewrite KT in KD. destruct KD as (ML & _).
      rewrite (pru_small (16 * size_class sc + 16)) in E1' by lia.
      assert (ES : g_stride s g = g_maplen s g * 4096 - 16).
      { unfold g_stride, slot_stride. rewrite L0. replace (negb (g_maplen s g =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
        cbn [andb Z.eqb]. unfold UNIT. reflexivity. }
      rewrite ES. lia. }
    assert (Hn4 : 0 <= n /\ n + 4 <= g_stride s g) by lia.
    assert (Hs31 : g_stride s g - n < 2 ^ 31) by (unfold g_cnt in Q20; nia).
    destruct (enframe_close s L Mx M4 g idx n offT W RP Hg Hidx Hsl Hn4 Hs31 POST M4W G4 ltac:(intros E63; exfalso; lia) HLL HX) as [W5 RP5].
    pose proof (MhEnfr.L_apart s L M4 g idx n offT W Hg Hidx Hsl Hn4 POST) as APL.
    pose proof (MhEnfr.p_notin_L s L M4 g idx n offT W Hg Hidx Hsl Hn4 POST) as NIL.
    pose proof (MhEnfr.e_ledger s g idx n offT _ LG) as LG5.
    set (s5 := MhEnfr.st' s g idx n offT) in *.
    pose proof (Pr _ _ _ _ _ _ POST) as (PR1 & PR2 & PR3). unfold P_r in PR1. unfold P_q in PR3.
    (* [comment removed for export] *)
    apply kat_refl. apply (kw_of_ok RSEGS F HL). apply HQ. unfold malloc_postkX.
    exists r4, M4, mdlx, (startT + 16 * offT), s5.
    split; [reflexivity|].
    split.
    { unfold cs_same.
      rewrite (KCS 2%bv ltac:(inCS)), (KCS 3%bv ltac:(inCS)), (KCS 4%bv ltac:(inCS)), (KCS 8%bv ltac:(inCS)), (KCS 9%bv ltac:(inCS)),
              (KCS 18%bv ltac:(inCS)), (KCS 19%bv ltac:(inCS)), (KCS 20%bv ltac:(inCS)), (KCS 21%bv ltac:(inCS)), (KCS 22%bv ltac:(inCS)),
              (KCS 23%bv ltac:(inCS)), (KCS 24%bv ltac:(inCS)), (KCS 25%bv ltac:(inCS)), (KCS 26%bv ltac:(inCS)), (KCS 27%bv ltac:(inCS)).
      rewrite I2, I8, I9, I18, I19, I20, R2.
      repeat split; try reflexivity.
      all: kept_rw K3; kept_rw K2; kept_rw K1; kept_rw K; reflexivity. }
    split; [exact J10|].
    split. { subst startT. unfold g_slot_start, UNIT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - GM2 Smod PR2 GM1 S16 Hidx. nia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split; [unfold HEAPLO in *; lia|].
    split; [ceil; lia|].
    split; [lia|].
    split; [exact NIL|].
    split; [exact APL|].
    split.
    { intros a Ha NE. destruct (decide (M4 (Z_to_bv 64 a) = Mx (Z_to_bv 64 a))) as [E|NE4].
      - rewrite E in NE. exact (FRx a Ha NE).
      - pose proof (M4W a Ha NE4) as Wa. right; left. split; [ceil; unfold HEAPLO in *; lia|]. split; [lia|].
        destruct (Z.lt_ge_cases a startT) as [LO|HI].
        + pose proof (MhEnfr.junk_hdr_cell s L g idx Hidx Hsl a ltac:(fold startT; lia)) as GC.
          intros AP. apply (ge_app_cell s (WF_geom s L W) g a Hg GC). exact (app_appb L 0%nat s a W AP).
        + pose proof (MhEnfr.junk_garbage s L g idx Hidx Hsl a ltac:(fold startT strideT; lia)) as GB.
          intros AP. apply (ge_garb_app s (WF_geom s L W) g idx a Hg GB). exact (app_appb L 0%nat s a W AP). }
    split; [eapply defined_grows; [exact G4 | exact DFx]|].
    split.
    { pose proof (group_bytes_defined s L Mx 8 g W RP (wg_depth s L g WG) Hg) as DG. intros y Hy. apply G4. apply DG. lia. }
    split; [exact W5|]. split; [exact RP5|]. split; [exact LG5|].
    split.
    { intros x k o Hx Hk. change (s_slot s5 x k) with (s_slot (set_slot s g idx (SUser (MhEnfr.p s g idx offT) n offT (MhEnfr.res s g n offT))) x k).
      rewrite s_slot_set_slot. destruct (Z.eqb x g && (k =? idx))%bool eqn:B; [discriminate|].
      intros E. destruct (OJ x k o Hx Hk E) as [-> ->]. rewrite !Z.eqb_refl in B. discriminate B. }
    split; [exact NL|].
    split; [exact Hh1|]. split; [exact Hlz1|]. split; [exact Hmat1|]. split; [exact Hfs1|]. split; [exact Hfds1|]. split; [exact Hlim1|].
    apply HPX.
  Qed.

  (* [comment removed for export] *)
  Hypothesis PXT : forall s g idx off, PX (MhEnfr.st' s g idx n off).

  Theorem malloc_small_kfx : kat RSEGS (mkCfg (mkst regs (0x628d0%bv : word) M rom) mdl) (kfx F bo).
  Proof.
    pose proof (rp_statics st M HREP) as [Snl Spg Slk Scan Sgot Serr Sctz Ssc].
    pose proof sc0_rng as SC0. pose proof sc0_fits as FIT0. ceil; unfold SSTK, ASSTK, AMSTK in Hsp. cbn in Hsp.
    assert (SOK48 : store_ok RSEGS M (Z_to_bv 64 (sp - 48)) 48%nat = true).
    { eapply (store_ok_defined M (sp - SSTK) sp); [exact DEF | rewrite SSTK_val; lia | cbn; lia | rewrite SSTK_val; lia | lia]. }
    destruct (mPro M sp n ltac:(ceil; lia) ltac:(unfold MMAP_THRESHOLD in Hn; lia) SOK48 regs rom R2 R10) as (r1 & RUN1 & A2 & A8 & A9 & A10 & K1).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN1 |]. fold M1.
    pose proof M1_REP as RP1. pose proof M1_def as DF1.
    (* [comment removed for export] *)
    assert (SZC : exists r2, msteps RSEGS (mkst r1 (0x62940%bv : word) M1 rom) (mkst r2 (0x62ac4%bv : word) M1 rom) /\
                  getr r2 20 = Z_to_bv 64 sc0 /\ getr r2 19 = Z_to_bv 64 A_TAB_CTZ /\ keeps_but clobSzc r1 r2).
    { destruct (Z.lt_ge_cases n 157) as [LT|GE].
      - destruct (mSzcA M1 n ltac:(lia) r1 rom A8 A10 LT) as (r2 & RUN & X20 & X19 & KX). exists r2. repeat split; assumption.
      - destruct (mSzcB M1 n ltac:(lia) (rc_tab_ctz st M1 (rp_statics st M1 RP1)) (sz_img_of_REP st M1 RP1) r1 rom A8 A10 GE) as (r2 & RUN & X20 & X19 & KX).
        exists r2. repeat split; assumption. }
    destruct SZC as (r2 & RUN2 & B20 & B19 & K2).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN2 |].
    (* [comment removed for export] *)
    destruct (mLck M1 (cell1_rdn M1 A_NEED_LOCKS 0 ltac:(lia) (rc_needlocks st M1 (rp_statics st M1 RP1))) r2 rom) as (r3 & RUN3 & K3).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN3 |].
    (* [comment removed for export] *)
    destruct (HCLS M1 st sc0 r3 HWF RP1 SC0 ltac:(kept_rw K3; exact B20) ltac:(kept_rw K3; kept_rw K2; exact A9)) as (r4 & sc & RUN4 & Hsc & CLS & C20 & C18 & C10 & K4).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN4 |].
    assert (REQ : 0 <= n /\ n + 4 <= 16 * size_class sc).
    { split; [lia|]. destruct CLS as [-> | (-> & _ & R4x & _)]; [exact FIT0|]. pose proof (size_class_mono sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
    pose proof (size_class_pos sc Hsc) as [SC1 SC2].
    assert (C8 : getr r4 8 = Z_to_bv 64 n) by (kept_rw K4; kept_rw K3; kept_rw K2; exact A8).
    assert (C9 : getr r4 9 = Z_to_bv 64 MLOCK) by (kept_rw K4; kept_rw K3; kept_rw K2; exact A9).
    assert (C2 : getr r4 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K4; kept_rw K3; kept_rw K2; exact A2).
    assert (C19 : getr r4 19 = Z_to_bv 64 A_TAB_CTZ) by (kept_rw K4; kept_rw K3; exact B19).
    assert (K14 : keeps_but (AS_CLOB ++ [1; 2; 8; 9; 18; 19; 20]%bv) regs r4).
    { eapply keeps_big || idtac.
      eapply keeps_but_trans; [eapply keeps_but_mono; [exact K1|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
      eapply keeps_but_trans; [eapply keeps_but_mono; [exact K2|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
      eapply keeps_but_trans; [eapply keeps_but_mono; [exact K3|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
      eapply keeps_but_mono; [exact K4|]. intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity. }
    (* [comment removed for export] *)
    assert (ASLOT : forall r4', getr r4' 10 = Z_to_bv 64 0 -> getr r4' 20 = Z_to_bv 64 sc -> getr r4' 8 = Z_to_bv 64 n ->
                    getr r4' 9 = Z_to_bv 64 MLOCK -> getr r4' 2 = Z_to_bv 64 (sp - 48) -> keeps_but (AS_CLOB ++ [1; 2; 8; 9; 18; 19; 20]%bv) regs r4' ->
                    kat RSEGS (mkCfg (mkst r4' (0x62b98%bv : word) M1 rom) mdl) (kfx F bo)).
    { intros r4' D10' D20 D8 D9 D2 K4'.
      destruct (mMsk0 M1 sc n Hsc r4' rom D10' D20 D8) as (r5 & RUN5 & D10 & D11 & D18 & D1 & K5).
      eapply kat_msteps; [exact Hh | exact Hlz | exact RUN5 |].
      set (dd := dbound (16 * size_class sc)). pose proof (dbound_le6 (16 * size_class sc) ltac:(lia)) as D6. fold dd in D6.
      assert (AS6 : ASSTK dd <= 1152) by (unfold ASSTK, AMSTK; lia).
      apply (kat_of_kfx F bo). replace (0x62c40%bv : word) with (Z_to_bv 64 AS_ENTRY) by (apply bv_eq; reflexivity).
      apply (HAS dd F false bo st L M1 mdl r5 rom (sp - 48) sc n HL ltac:(intros Hbo; right; exact (SIDE Hbo)) HWF RP1 HLG NJ Hh Hlz Hmat Hsc).
      { apply le_n. }
      { rewrite NLB. unfold zlen. cbn [length]. lia. }
      { exact REQ. }
      { exact HBUD. }
      { exact D10. }
      { exact D11. }
      { kept_rw K5. exact D2. }
      { rewrite D1. apply ret_ok_even. reflexivity. }
      { kept_rw K5. kept_rw K4'. exact R4. }
      { ceil. lia. }
      { lia. }
      { intros y Hy. apply DF1. rewrite SSTK_val. lia. }
      2: { (* [comment removed for export] *)
        intros c' PF.
        destruct PF as (s3 & M3 & mdl3 & r6 & -> & W3 & RP3 & LG3 & Hh3 & Hlz3 & Hmat3 & Hfs3 & Hfds3 & Hlim3 & NJ3 & EL3 & Hcan3 &
                        LM3 & MU3 & F10 & F2 & K6 & FRM3 & DEF3).
        rewrite D1. replace (Z_to_bv 64 404448) with (0x62be0%bv : word) by (apply bv_eq; reflexivity).
        apply (kf_of_kat F HL).
        assert (STK3 : forall y, sp - 48 <= y < sp -> M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y)).
        { intros y Hy. destruct (decide (M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE3]; [exact E|]. exfalso.
          destruct (FRM3 y ltac:(lia) NE3) as [A|[A|[A|A]]]; [lia | ceil; unfold HEAPLO in A; lia | unfold CTX_END, CTX in A; lia | unfold A_ERRNO, TPV in A; lia]. }
        assert (STK : forall dd' v, 8 <= dd' <= 48 -> rdn RSEGS M1 (Z_to_bv 64 (sp - dd')) 8%nat = Some (word_to_le_bytes 8 v) ->
                      rdn RSEGS M3 (Z_to_bv 64 (sp - dd')) 8%nat = Some (word_to_le_bytes 8 v)).
        { intros dd' v Hd R. rewrite (rdn_agreeZ M1 M3 (sp - dd') 8 ltac:(lia) ltac:(cbn; lia)); [exact R|]. intros y Hy. apply STK3. cbn in Hy. lia. }
        pose proof (rc_lock s3 M3 (rp_statics s3 M3 RP3)) as Mlk.
        destruct (tM1 M3 sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(ceil; lia) Rra
                    (STK 8 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK 16 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                    (STK 24 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK 32 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                    (STK 40 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve)) (STK 48 _ ltac:(lia) ltac:(unfold M1, mal_frame; rdn_solve))
                    Mlk r6 rom ltac:(rewrite F2; kept_rw K5; exact D2) F10)
          as (r7 & RUN7 & E2 & E10 & E1 & E8 & E9 & E18 & E19 & E20 & K7).
        eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN7 |].
        apply kat_refl. apply HQF. unfold malloc_failk.
        exists r7, M3, mdl3, s3.
        split; [reflexivity|].
        split.
        { unfold cs_same. rewrite E2, E8, E9, E18, E19, E20, R2. repeat split; try reflexivity.
          all: kept_rw K7; kept_rw K6; kept_rw K5; kept_rw K4'; reflexivity. }
        split; [exact E10|].
        split.
        { intros a Ha NE. destruct (decide (M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E|NE3].
          - rewrite E in NE. left. pose proof (M1_writes a Ha NE). rewrite SSTK_val. lia.
          - destruct (FRM3 a Ha NE3) as [A|[A|[A|A]]]; [left; rewrite SSTK_val; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A]. }
        split.
        { intros y Hy. rewrite SSTK_val in Hy. destruct (decide (M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE3].
          - rewrite E. apply DF1. rewrite SSTK_val. lia.
          - destruct (FRM3 y ltac:(lia) NE3) as [A|[A|[A|A]]]; [apply DEF3; exact A | exfalso; ceil; unfold HEAPLO in A; lia | exfalso; unfold CTX_END, CTX in A; lia | exfalso; unfold A_ERRNO, TPV in A; lia]. }
        split; [exact W3|]. split; [exact RP3|]. split; [exact LG3|]. split; [exact NJ3|]. split; [unfold nolimbo; rewrite EL3; exact NLB|].
        split; [exact Hh3|]. split; [exact Hlz3|]. split; [exact Hmat3|]. split; [exact Hfs3|]. split; [exact Hfds3|]. exact Hlim3. }
      intros c' POST. apply (kfx_of_kat F HL false).
      destruct POST as (s3 & M3 & mdl3 & r6 & g' & idx & -> & W3 & RP3 & LG3 & Hh3 & Hlz3 & Hmat3 & Hfs3 & Hfds3 & Hlim3 & EL3 & Hcan3 & Herr3 &
                        Hhd3 & Hg3 & Hgsc3 & Hidx3 & Hsl3 & OJ3 & Hstr3 & Hbig3 & BL3 & LM3 & MU3 & F10 & F2 & K6 & FRM3 & DEF3).
      rewrite D1. replace (Z_to_bv 64 404448) with (0x62be0%bv : word) by (apply bv_eq; reflexivity).
      pose proof (glast_rng s3 g') as GL3.
      pose proof (rc_active s3 M3 (rp_ctx s3 M3 RP3) sc Hsc) as Ract. rewrite (wc_active s3 (WF_ctx s3 L W3) sc Hsc), Hhd3 in Ract.
      destruct (mRet M3 sc idx g' Hsc ltac:(lia) Ract r6 rom F10 ltac:(kept_rw K6; exact D18) ltac:(kept_rw K6; kept_rw K5; exact D9)) as (r7 & RUN7 & E19 & E18 & K7).
      eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN7 |].
      apply (small_tail s3 M3 mdl3 r7 sc g' idx W3 RP3 LG3 ltac:(rewrite EL3; exact NLB) Hh3 Hlz3 Hmat3 Hfs3 Hfds3 Hlim3 Hsc CLS Hhd3 Hg3 Hgsc3 Hidx3 Hsl3 OJ3 Hstr3).
      - intros a Ha NE. destruct (decide (M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E|NE3].
        + rewrite E in NE. left. pose proof (M1_writes a Ha NE). rewrite SSTK_val. lia.
        + destruct (FRM3 a Ha NE3) as [A|[A|[A|A]]]; [left; rewrite SSTK_val; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A].
      - intros y Hy. rewrite SSTK_val in Hy. destruct (decide (M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE3].
        + rewrite E. apply DF1. rewrite SSTK_val. lia.
        + destruct (FRM3 y ltac:(lia) NE3) as [A|[A|[A|A]]]; [apply DEF3; exact A | exfalso; ceil; unfold HEAPLO in A; lia | exfalso; unfold CTX_END, CTX in A; lia | exfalso; unfold A_ERRNO, TPV in A; lia].
      - intros y Hy. destruct (decide (M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE3]; [exact E|]. exfalso.
        destruct (FRM3 y ltac:(lia) NE3) as [A|[A|[A|A]]]; [lia | ceil; unfold HEAPLO in A; lia | unfold CTX_END, CTX in A; lia | unfold A_ERRNO, TPV in A; lia].
      - exact E19.
      - exact E18.
      - kept_rw K7. kept_rw K6. kept_rw K5. exact D9.
      - kept_rw K7. kept_rw K6. kept_rw K5. exact D8.
      - kept_rw K7. rewrite F2. kept_rw K5. exact D2.
      - eapply keeps_but_trans; [exact K4'|].
        eapply keeps_but_trans; [eapply keeps_but_mono; [exact K5|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
        eapply keeps_but_trans; [eapply keeps_but_mono; [exact K6|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
        eapply keeps_but_mono; [exact K7|]. intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
      - apply PXT. }
    set (g := head_of (s_alist st sc)) in *.
    destruct (Z.eq_dec g 0) as [G0|GNZ].
    - (* [comment removed for export] *)
      rewrite G0, Z.eqb_refl in C10. exact (ASLOT r4 C10 C20 C8 C9 C2 K14).
    - (* [comment removed for export] *)
      destruct (head_facts L sc st g HWF eq_refl GNZ) as (rest & Hl & Hg & Hgsc).
      replace (g =? 0) with false in C10 by (symmetry; apply Z.eqb_neq; exact GNZ).
      pose proof (wG_each st L (WF_groups st L HWF) g Hg) as WG. pose proof (wg_avr st L g WG) as AVR. pose proof (glast_rng st g) as GL.
      set (av := mr_avail (s_meta st g)) in *.
      destruct (Z.eq_dec av 0) as [AV0|AVNZ].
      + rewrite AV0 in C10. change (s32 0) with (Z_to_bv 64 0) in C10 || (rewrite zero_s32' in C10 || idtac).
        exact (ASLOT r4 ltac:(rewrite C10; apply bv_eq; reflexivity) C20 C8 C9 C2 K14).
      + (* [comment removed for export] *)
        destruct bo. { exfalso. apply AVNZ. subst av. exact (proj1 (SIDE eq_refl g Hg)). }
        destruct (lowbit_pow2 av ltac:(lia)) as (i & Hi & Hlow & Hbit & _).
        pose proof (proj1 (wg_av st L g WG i ltac:(lia))) as AVi. fold av in AVi. destruct (AVi Hbit) as [Hil Hsli].
        destruct (G_meta_cells st L M1 HWF RP1 g Hg) as (ar1 & k1 & _ & _ & _ & _ & Rlo & Rhi & _ & RM1 & _ & _).
        pose proof (meta_store_ok st L M1 HWF RP1 g (group_metaU st L HWF g Hg)) as SOKg.
        assert (SOK24 : store_ok RSEGS M1 (Z_to_bv 64 (g + 24)) 4%nat = true) by (ceil; unfold HEAPLO in *; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia).
        destruct (mMskT M1 g av i ltac:(unfold HEAPLO in *; lia) AVR Hi Hlow Hbit SOK24 (rc_tab_ctz st M1 (rp_statics st M1 RP1)) r4 rom C10 C18 C19)
          as (r5 & RUN5 & E19 & E10 & E18 & K5).
        eapply kat_msteps; [exact Hh | exact Hlz | exact RUN5 |].
        set (M2 := m_take M1 g av i) in *.
        assert (G2 : mem_grows M1 M2) by (unfold M2, m_take; apply wbytes_grows).
        assert (W2 : forall a, 0 <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) <> M1 (Z_to_bv 64 a) -> g + 24 <= a < g + 28).
        { intros a Ha NE. ceil; unfold M2, m_take, HEAPLO in *. wdiff NE M1 a. }
        assert (Hhd' : g = head_of (s_alist st (g_sc st g))) by (rewrite Hgsc; reflexivity).
        destruct (take_close st L M1 M2 g i (sp - SSTK + MSTK) HWF RP1 Hg ltac:(lia) Hsli Hhd' ltac:(rewrite SSTK_val; ceil; unfold MSTK; lia)
                    ltac:(intros a Ha NE; right; exact (W2 a Ha NE)) G2
                    ltac:(unfold M2, m_take; fold av; apply cell_hit; ceil; unfold HEAPLO in *; cbn; lia)) as [W2' RP2].
        set (s2 := MhTake.st' st g i) in *.
        assert (STR : 16 * size_class sc <= g_stride st g).
        { destruct (Z.lt_ge_cases (g_stride st g) (UNIT * size_class (g_sc st g))) as [LT|GE].
          - exfalso. destruct (wg_fit st L g WG ltac:(lia) LT i ltac:(lia)) as [X _]. exact (X Hsli).
          - rewrite Hgsc in GE. unfold UNIT in GE. lia. }
        apply (small_tail s2 M2 mdl r5 sc g i W2' RP2).
        * apply (LEDGER_same st); [reflexivity | reflexivity | exact HLG].
        * exact NLB.
        * exact Hh. * exact Hlz. * exact Hmat. * reflexivity. * reflexivity. * reflexivity.
        * exact Hsc.
        * exact CLS.
        * subst g. reflexivity.
        * exact Hg.
        * change (g_sc s2 g) with (g_sc (MhTake.st' st g i) g). rewrite (MhTake.e_gsc st g i). exact Hgsc.
        * change (g_lastidx s2 g) with (g_lastidx (MhTake.st' st g i) g). rewrite (MhTake.e_glast st g i). lia.
        * apply MhTake.e_slot_mi.
        * intros x k o Hx Hk E. change (is_group st x) in Hx.
          change (g_lastidx s2 x) with (g_lastidx (MhTake.st' st g i) x) in Hk. rewrite (MhTake.e_glast st g i) in Hk.
          change (s_slot s2 x k) with (s_slot (MhTake.st' st g i) x k) in E. rewrite (MhTake.e_slot st g i) in E.
          destruct (Z.eqb_spec x g) as [Ex|Nx]; [destruct (Z.eqb_spec k i) as [Ek|Nk]; [split; assumption|]|]; cbn [andb] in E;
            exfalso; exact (NJ x k o Hx Hk E).
        * change (g_stride s2 g) with (g_stride (MhTake.st' st g i) g). rewrite (MhTake.e_gstride st g i). lia.
        * intros a Ha NE. destruct (decide (M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E|NE2].
          -- rewrite E in NE. left. pose proof (M1_writes a Ha NE). rewrite SSTK_val. lia.
          -- pose proof (W2 a Ha NE2). destruct (meta_WOK L sp 6%nat st g a HWF (group_metaU st L HWF g Hg) ltac:(lia)) as [B|[B|[B|B]]];
               [left; rewrite SSTK_val; unfold ASSTK, AMSTK in B; lia | right; left; exact B | right; right; left; exact B | right; right; right; exact B].
        * eapply defined_grows; [exact G2 | exact DF1].
        * intros y Hy. destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE2]; [exact E|]. exfalso. pose proof (W2 y ltac:(lia) NE2). ceil; unfold HEAPLO in *. lia.
        * exact E19.
        * exact E18.
        * kept_rw K5. exact C9.
        * kept_rw K5. exact C8.
        * kept_rw K5. exact C2.
        * eapply keeps_but_trans; [exact K14|]. eapply keeps_but_mono; [exact K5|]. intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
        * apply PXT.
  Qed.
End Small.
