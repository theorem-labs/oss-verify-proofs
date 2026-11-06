(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhNtfA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
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
Definition ntf_frame (m0 : mem) (sp : Z) (ra s0 s1 s2 s3 can : word) : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m0
    (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 can).

Section N0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m0 : mem) (sp g idx W avail freed can : Z).
  Hypothesis Hsp : (CEIL + 96 <= sp)%Z /\ (sp < 2^64)%Z /\ (sp mod 16 = 0)%Z.
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hidx : (0 <= idx < 32)%Z.
  Hypothesis HW : (0 <= W < 2^64)%Z.
  Hypothesis Hav : (0 <= avail < 2^32)%Z.
  Hypothesis Hfr : (0 <= freed < 2^32)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis SOK : store_ok RSEGS m0 (Z_to_bv 64 (sp - 96)) 96%nat = true.
  Hypothesis M_W : rdn RSEGS m0 (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W)).
  Hypothesis M_av : rdn RSEGS m0 (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail)).
  Hypothesis M_fr : rdn RSEGS m0 (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed)).
  Hypothesis M_got : rdn RSEGS m0 (Z_to_bv 64 A_GOT_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY)).
  Hypothesis M_can : rdn RSEGS m0 (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).

  Definition clobN0 : list reg := [2; 9; 11; 12; 13; 14; 15; 16; 18]%bv.

  Lemma segN0 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx -> getr regs 2 = Z_to_bv 64 sp ->
    exists regs',
      msteps RSEGS (mkst regs (0x66890 : word) m0 rom)
                   (mkst regs' (0x668dc : word)
                         (ntf_frame m0 sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (Z_to_bv 64 can)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 96)
      /\ getr regs' 9 = Z_to_bv 64 A_CANARY
      /\ getr regs' 10 = Z_to_bv 64 g
      /\ getr regs' 11 = s32 (2 ^ idx)
      /\ getr regs' 12 = Z_to_bv 64 (w_sizeclass W)
      /\ getr regs' 13 = s32 (Z.lor avail freed)
      /\ getr regs' 14 = v_slli (Z_to_bv 64 W) 52
      /\ getr regs' 15 = Z_to_bv 64 W
      /\ getr regs' 16 = Z_to_bv 64 (32 * w_freeable W)
      /\ keeps_but clobN0 regs regs'.
  Proof using M_can M_got M_fr M_av M_W SOK Hfr Hav HW Hidx Hg Hsp RN.
    intros regs rom H10 H11 H2.
    ceil; unfold HEAPLO, A_GOT_CANARY, A_CANARY in *.
    eexists. split.
    - stepn F_6683c D_6683c. rewrite H2. addi_renorm.
      stepSTx F_66840 D_66840 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 96%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_66844 D_66844 (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 96%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_66848 D_66848 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 96%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_6684c D_6684c (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 96%nat); [ | exact SOK | | ]; zsimp; lia).
      stepSTx F_66850 D_66850 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 96%nat); [ | exact SOK | | ]; zsimp; lia).
      stepn F_66854 D_66854.
      stepLD8 F_66858 D_66858 (Z_to_bv 64 699904).
      stepLD8 F_6685c D_6685c (Z_to_bv 64 can).
      stepSTx F_66860 D_66860 (Z_to_bv 64 (sp - 48)) (Z_to_bv 64 can) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 96%nat); [ | exact SOK | | ]; zsimp; lia).
      stepLD8 F_66864 D_66864 (Z_to_bv 64 W).
      stepLD F_66868 D_66868 (word_to_le_bytes 4 (Z_to_bv 64 freed)) (Z_to_bv 64 freed)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepLD F_6686c D_6686c (word_to_le_bytes 4 (Z_to_bv 64 avail)) (Z_to_bv 64 avail)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_66870 D_66870.
      stepn F_66874 D_66874. rewrite H11. rewrite v_sllw_Z_s32 by lia. rewrite (Z.mod_small idx 32), Z.mul_1_l by lia.
      stepn F_66878 D_66878.
      stepn F_6687c D_6687c. rewrite v_or_s32.
      stepn F_66880 D_66880.
      rewrite v_andi_Z by lia.
      replace (Z.land W 32) with (32 * w_freeable W)%Z by (unfold w_freeable; symmetry; apply land_32_freeable; lia).
      stepn F_66884 D_66884.
      replace (v_srli (v_slli (Z_to_bv 64 W) 52) 58) with (Z_to_bv 64 (w_sizeclass W)).
      2:{ unfold v_srli, v_slli, w_sizeclass. f_equal. rewrite (u_Z2bv W) by lia.
          rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. symmetry. apply sc_extract. lia. }
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption.
      solve_keeps_but.
  Qed.
End N0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section E.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp can : Z) (ra s0v s1v s2v s3v : word) (base len : word).
  Hypothesis Hsp : (CEIL + 96 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis M_can : rdn RSEGS m (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_c48 : rdn RSEGS m (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).

  Definition clobE : list reg := [1; 2; 8; 9; 10; 13; 18; 19]%bv.

  Lemma segE : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 96) -> getr regs 9 = Z_to_bv 64 A_CANARY ->
    getr regs 12 = base -> getr regs 11 = len ->
    exists regs',
      msteps RSEGS (mkst regs (0x66c38 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ getr regs' 10 = base /\ getr regs' 11 = len
      /\ keeps_but clobE regs regs'.
  Proof using M_s3 M_s2 M_s1 M_s0 M_ra M_c48 M_can Hra Hsp can RN.
    intros regs rom H2 H9 H12 H11. ceil; unfold A_CANARY in *.
    eexists. split.
    - stepLD8 F_66be4 D_66be4 (Z_to_bv 64 can).
      stepLD8 F_66be8 D_66be8 (Z_to_bv 64 can).
      stepb_ft F_66bec D_66bec ltac:(apply c_eq_refl || (rewrite c_eq_Z by lia; apply Z.eqb_refl)).
      stepn F_66bf0 D_66bf0.
      stepLD8 F_66bf4 D_66bf4 ra.
      stepLD8 F_66bf8 D_66bf8 s0v.
      stepLD8 F_66bfc D_66bfc s1v.
      stepLD8 F_66c00 D_66c00 s2v.
      stepLD8 F_66c04 D_66c04 s3v.
      stepn F_66c08 D_66c08. rewrite H2. addi_renorm.
      stepret F_66c0c D_66c0c ra ltac:(reflexivity).
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption.
      all: try (f_equal; lia).
      all: try solve_keeps_but.
  Qed.
End E.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section OR.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g freed self : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z) /\ (g mod 8 = 0)%Z.
  Hypothesis Hfr : (0 <= freed < 2^32)%Z.
  Hypothesis Hself : (0 <= self < 2^32)%Z.
  Hypothesis M_fr : rdn RSEGS m (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed)).
  Hypothesis SOKg : store_ok RSEGS m (Z_to_bv 64 g) 40%nat = true.

  Definition m_or : mem := wbytes m (Z_to_bv 64 (g + 28)) (word_to_le_bytes 4 (s32 (Z.lor freed self))).

  Definition clobOR : list reg := [10; 11; 12; 13; 15]%bv.

  Lemma segOR : forall regs rom,
    getr regs 14 = Z_to_bv 64 (g + 28) -> getr regs 11 = s32 self ->
    exists regs',
      msteps RSEGS (mkst regs (0x66c10 : word) m rom) (mkst regs' (0x66c38 : word) m_or rom)
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 0
      /\ keeps_but clobOR regs regs'.
  Proof using SOKg M_fr Hself Hfr Hg RN.
    intros regs rom H14 H11. ceil; unfold HEAPLO in *.
    assert (Hal : (bv_unsigned (getr regs 14) mod 4 = 0)%Z).
    { rewrite H14. rewrite u_Z2bv by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    eexists. split.
    - stepLD F_66bbc D_66bbc (word_to_le_bytes 4 (Z_to_bv 64 freed)) (Z_to_bv 64 freed)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_66bc0 D_66bc0. rewrite H11, v_or_s32.
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply (step_lr_w RSEGS _ _ _ _ _ true true 13 14 (word_to_le_bytes 4 (Z_to_bv 64 freed)) (Z_to_bv 64 freed));
          [exact F_66bc4 | reflexivity | exact D_66bc4 | gres; exact Hal | gres; rewrite H14; addr_norm; rdn_solve | apply bytes_le_to_Z_4; u_norm; lia ]
        | step_simpl ].
      cbn [bv_eqb]. rewrite v_lw_s32 by lia.
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_66bc8 | reflexivity | exact D_66bc8 | gres; apply c_eq_refl ]
        | step_simpl ].
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_66bcc | reflexivity | exact D_66bcc | gres; exact Hal | gres; reflexivity
            | gres; rewrite H14; store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia ]
        | step_simpl ].
      cbn [bv_eqb]. vnorm. rewrite H14.
      stepb_ft F_66bd0 D_66bd0 ltac:(cond_compute).
      stepn F_66bd4 D_66bd4. rewrite v_addiw_s32, Z.add_0_r.
      stepb_ft F_66bd8 D_66bd8 ltac:(apply c_eq_refl).
      stepn F_66bdc D_66bdc.
      stepn F_66be0 D_66be0.
      unfold m_or. pu_refl.
    - repeat split; gres; try reflexivity. solve_keeps_but.
  Qed.
End OR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ntf_okay (g sc lastidx maplen next bnc usage : Z) : Prop :=
  (48 <= sc \/ maplen = 0 \/ (lastidx = 0 /\ maplen * 4096 - 16 < 16 * size_class sc) \/ next <> g
   \/ sc < 7 \/ 38 < sc \/ bnc < 100 \/ (9 * (lastidx + 1) <= usage /\ lastidx <= 18))%Z.

Section D.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g W avail freed idx next bnc usage : Z).
  #[local] Notation sc := (w_sizeclass W).
  #[local] Notation lastidx := (w_lastidx W).
  #[local] Notation maplen := (w_maplen W).
  #[local] Notation mask := (Z.lor avail freed).
  #[local] Notation self := (2 ^ idx)%Z.
  #[local] Notation all := (2 * 2 ^ (w_lastidx W) - 1)%Z.
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis HW : (0 <= W < 2^64)%Z.
  Hypothesis Hfree : w_freeable W = 1%Z.
  Hypothesis Hidx : (0 <= idx <= w_lastidx W)%Z.
  Hypothesis Hav : (0 <= avail < 2^32)%Z.
  Hypothesis Hfr : (0 <= freed < 2^32)%Z.
  Hypothesis Hmb : Z.testbit (Z.lor avail freed) idx = false.
  Hypothesis Hnext : (0 <= next < 2^64)%Z.
  Hypothesis Hbnc : (0 <= bnc < 256)%Z.
  Hypothesis Husage : (0 <= usage < 2^64)%Z.
  Hypothesis M_next : rdn RSEGS m (Z_to_bv 64 (g + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 next)).
  Hypothesis M_bnc : (7 <= sc <= 38)%Z -> rdn RSEGS m (Z_to_bv 64 (ctx_bounces (sc - 7))) 1%nat = Some [Z_to_bv 8 bnc].
  Hypothesis M_usage : (sc < 48)%Z -> rdn RSEGS m (Z_to_bv 64 (ctx_usage sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 usage)).
  Hypothesis M_img : sz_img m.

  Lemma d_last : (0 <= lastidx < 32)%Z. Proof using. unfold w_lastidx; apply Z.mod_pos_bound; lia. Qed.
  Lemma d_sc : (0 <= sc < 64)%Z. Proof using. unfold w_sizeclass; apply Z.mod_pos_bound; lia. Qed.
  Lemma d_ml : (0 <= maplen < 2^52)%Z.
  Proof using HW. unfold w_maplen. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
  Lemma d_mask : (0 <= mask < 2^32)%Z. Proof using Hfr Hav. apply Z_lor_range32; lia. Qed.
  Lemma d_all : (0 < all < 2^32)%Z.
  Proof using.
    pose proof d_last. assert (0 < 2 ^ lastidx <= 2^31)%Z by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    change (2^32)%Z with (2 * 2^31)%Z. lia.
  Qed.
  Lemma d_self : (0 < self <= 2^31)%Z /\ (mask + self < 2^32)%Z.
  Proof using Hmb Hfr Hav Hidx W.
    pose proof d_last. pose proof d_mask.
    split; [split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]|].
    apply add_pow2_nocarry32; [exact d_mask | lia | exact Hmb].
  Qed.

  Lemma E_last : v_andi (Z_to_bv 64 W) 31 = Z_to_bv 64 lastidx.
  Proof using HW. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia. reflexivity. Qed.
  Lemma E_ml : v_srli (Z_to_bv 64 W) 12 = Z_to_bv 64 maplen.
  Proof using HW. rewrite v_srli_Z by lia. reflexivity. Qed.
  Lemma E_pm : v_and (Z_to_bv 64 W) (Z_to_bv 64 18446744073709547520) = Z_to_bv 64 (maplen * 4096).
  Proof using Husage Hbnc Hnext Hfr Hav HW usage bnc next freed avail.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite v_and_Z by lia. f_equal. rewrite land_pagemask by lia. unfold w_maplen. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  Lemma E_sc2 : v_andi (v_srli (Z_to_bv 64 W) 5) 126 = Z_to_bv 64 (2 * sc).
  Proof using Husage Hbnc Hnext Hfr Hav HW usage bnc next freed avail.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    unfold v_andi, v_srli. f_equal. rewrite (u_Z2bv W) by lia. change (bv_wrap 64 126) with 126%Z.
    assert (HR : (0 <= Z.shiftr W 5 < 2^64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; lia).
    rewrite u_Z2bv by lia. unfold w_sizeclass. apply sc2_extract. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Definition clobD : list reg := [5; 14; 15; 16; 17; 18]%bv.

  Ltac post_tac := repeat split; gres; try reflexivity; try assumption; try solve_keeps_but.

  Definition dregs (r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 g /\ getr r 11 = s32 self /\ getr r 12 = Z_to_bv 64 sc /\ getr r 13 = s32 mask.

  (* [comment removed for export] *)
  Lemma segD_ne : forall regs rom,
    dregs regs -> getr regs 15 = Z_to_bv 64 W -> getr regs 16 = Z_to_bv 64 (32 * w_freeable W) ->
    (mask + self <> all)%Z ->
    exists regs', msteps RSEGS (mkst regs (0x668dc : word) m rom) (mkst regs' (0x669ec : word) m rom)
      /\ dregs regs' /\ keeps_but clobD regs regs'.
  Proof using Hmb Hfr Hav Hidx Hfree HW.
    intros regs rom (H10 & H11 & H12 & H13) H15 H16 Hne.
    pose proof d_last as HL. pose proof d_mask as HMK. pose proof d_all as HA. destruct d_self as [HSf HNC].
    eexists. split.
    - stepb_ft F_66888 D_66888 ltac:(rewrite H16, Hfree; cond_compute).
      stepn F_6688c D_6688c. rewrite H13, H11, v_addw_s32.
      stepn F_66890 D_66890.
      stepn F_66894 D_66894. rewrite H15. rewrite v_sllw_Z_s32 by lia. change (W mod 32)%Z with lastidx.
      stepn F_66898 D_66898. rewrite v_addiw_s32.
      stepb_tk F_6689c D_6689c ltac:(rewrite c_eq_s32; rewrite !Z.mod_small by lia; apply Z.eqb_neq; lia).
      pu_refl.
    - unfold dregs. post_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma segD_pfx : forall regs rom,
    dregs regs -> getr regs 15 = Z_to_bv 64 W -> getr regs 16 = Z_to_bv 64 (32 * w_freeable W) ->
    (mask + self = all)%Z ->
    exists regs', msteps RSEGS (mkst regs (0x668dc : word) m rom) (mkst regs' (0x66900 : word) m rom)
      /\ dregs regs' /\ getr regs' 14 = Z_to_bv 64 47 /\ getr regs' 15 = Z_to_bv 64 W /\ getr regs' 18 = Z_to_bv 64 CTX
      /\ keeps_but clobD regs regs'.
  Proof using Hmb Hfr Hav Hidx Hfree HW.
    intros regs rom (H10 & H11 & H12 & H13) H15 H16 Heq.
    pose proof d_last as HL. pose proof d_mask as HMK. pose proof d_all as HA. destruct d_self as [HSf HNC].
    unfold CTX. eexists. split.
    - stepb_ft F_66888 D_66888 ltac:(rewrite H16, Hfree; cond_compute).
      stepn F_6688c D_6688c. rewrite H13, H11, v_addw_s32.
      stepn F_66890 D_66890.
      stepn F_66894 D_66894. rewrite H15. rewrite v_sllw_Z_s32 by lia. change (W mod 32)%Z with lastidx.
      stepn F_66898 D_66898. rewrite v_addiw_s32.
      stepb_ft F_6689c D_6689c ltac:(rewrite c_eq_s32; rewrite !Z.mod_small by lia; apply Z.eqb_eq; lia).
      stepn F_668a0 D_668a0.
      stepn F_668a4 D_668a4.
      stepn F_668a8 D_668a8.
      pu_refl.
    - unfold dregs. post_tac.
  Qed.

  (* [comment removed for export] *)
  Definition dpost (regs' : bvmap 5 word) (pc' : word) : Prop :=
    (pc' = (0x669a4 : word) /\ ntf_okay g sc lastidx maplen next bnc usage)
    \/ (pc' = (0x669ec : word) /\ (sc < 48)%Z /\ maplen <> 0%Z /\ next = g /\ (7 <= sc <= 38)%Z /\ (100 <= bnc)%Z
        /\ ~ (lastidx = 0 /\ maplen * 4096 - 16 < 16 * size_class sc)%Z).

  Lemma segD_tree : forall regs rom,
    dregs regs -> getr regs 14 = Z_to_bv 64 47 -> getr regs 15 = Z_to_bv 64 W -> getr regs 18 = Z_to_bv 64 CTX ->
    exists regs' pc', msteps RSEGS (mkst regs (0x66900 : word) m rom) (mkst regs' pc' m rom)
      /\ dpost regs' pc' /\ dregs regs' /\ getr regs' 18 = Z_to_bv 64 CTX /\ keeps_but clobD regs regs'.
  Proof using M_img M_usage M_bnc M_next Husage Hbnc Hnext Hfr Hav Hidx HW Hg RN.
    intros regs rom (H10 & H11 & H12 & H13) H14 H15 H18.
    pose proof d_last as HL. pose proof d_sc as HS. pose proof d_ml as HM. pose proof d_mask as HMK. pose proof d_all as HA.
    ceil; unfold HEAPLO, CTX in *.
    (* [comment removed for export] *)
    destruct (Z.lt_ge_cases 47 sc) as [Hsc48 | Hsc48].
    { eexists _, _. split.
      - stepb_tk F_668ac D_668ac ltac:(rewrite H14, H12, c_ltu_Z by lia; apply Z.ltb_lt; lia). pu_refl.
      - split; [left; split; [reflexivity | unfold ntf_okay; left; lia]|]. unfold dregs. post_tac. }
    (* [comment removed for export] *)
    destruct (sz_entry m sc M_img ltac:(lia)) as (sbs & Hsbs & Hsv).
    pose proof (size_class_pos sc ltac:(lia)) as Hszp.
    (* [comment removed for export] *)
    Ltac pre1 H14 H12 H15 :=
      stepb_ft F_668ac D_668ac ltac:(rewrite H14, H12, c_ltu_Z by lia; apply Z.ltb_ge; lia);
      stepn F_668b0 D_668b0; getr_hyps; rewrite E_last;
      stepn F_668b4 D_668b4; getr_hyps; rewrite E_ml;
      stepn F_668b8 D_668b8;
      stepn F_668bc D_668bc.
    (* [comment removed for export] *)
    Ltac sz5 sbs Hsbs Hsv :=
      stepn F_668dc D_668dc; getr_hyps;
      stepn F_668e0 D_668e0; rewrite E_sc2;
      stepn F_668e4 D_668e4; rewrite (v_add_ZZ 145772 (2 * sc)) by lia;
      replace (145772 + 2 * sc)%Z with (0x2396c + 2 * sc)%Z by lia;
      stepLHU F_668e8 D_668e8 sbs (Z_to_bv 64 (size_class sc)) ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia);
      stepn F_668ec D_668ec; rewrite (v_slli_Z (size_class sc) 4) by (change (2^4)%Z with 16%Z; lia); change (2^4)%Z with 16%Z.
    (* [comment removed for export] *)
    Ltac sz6 sbs Hsbs Hsv H12 :=
      stepn F_668f4 D_668f4; getr_hyps; rewrite (v_slli_Z sc 1) by (change (2^1)%Z with 2%Z; lia); change (2^1)%Z with 2%Z;
      stepn F_668f8 D_668f8; rewrite (v_add_ZZ 145772 (sc * 2)) by lia;
      replace (145772 + sc * 2)%Z with (0x2396c + 2 * sc)%Z by lia;
      stepLHU F_668fc D_668fc sbs (Z_to_bv 64 (size_class sc)) ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia);
      stepn F_66900 D_66900; rewrite (v_slli_Z (size_class sc) 4) by (change (2^4)%Z with 16%Z; lia); change (2^4)%Z with 16%Z.
    destruct (Z.eq_dec maplen 0) as [Hml0 | Hml0].
    { (* [comment removed for export] *)
      eexists _, _. split.
      - pre1 H14 H12 H15.
        stepb_tk F_668c0 D_668c0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; exact Hml0).
        sz5 sbs Hsbs Hsv.
        stepb_tk F_668f0 D_668f0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; exact Hml0).
        pu_refl.
      - split; [left; split; [reflexivity | unfold ntf_okay; right; left; exact Hml0]|]. unfold dregs. post_tac. }
    (* [comment removed for export] *)
    assert (TO_ED4 : forall K : Prop,
      ((lastidx = 0 /\ maplen * 4096 - 16 < 16 * size_class sc)%Z -> K) ->
      (forall r2, dregs r2 -> getr r2 14 = Z_to_bv 64 lastidx -> getr r2 18 = Z_to_bv 64 700056 -> keeps_but clobD regs r2 ->
         msteps RSEGS (mkst regs (0x66900 : word) m rom) (mkst r2 (0x6695c : word) m rom) ->
         ~ (lastidx = 0 /\ maplen * 4096 - 16 < 16 * size_class sc)%Z -> K) -> K).
    { intros K Kok Kcont.
      destruct (Z.eq_dec lastidx 0) as [Hl0 | Hl0].
      - (* [comment removed for export] *)
        destruct (Z.lt_ge_cases (maplen * 4096 - 16) (16 * size_class sc)) as [Hlt | Hge].
        + apply Kok. split; assumption.
        + eapply (Kcont _); [ | | | | | lia]; cycle 4.
          * pre1 H14 H12 H15.
            stepb_ft F_668c0 D_668c0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hml0).
            stepb_ft F_668c4 D_668c4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; exact Hl0).
            stepn F_668c8 D_668c8.
            stepn F_668cc D_668cc. getr_hyps. rewrite E_pm.
            stepn F_668d0 D_668d0. addi_renorm.
            stepb_tk F_668d4 D_668d4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hml0).
            sz6 sbs Hsbs Hsv H12.
            stepb_ft F_66904 D_66904 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
            pu_refl.
          * unfold dregs; post_tac.
          * gres; reflexivity.
          * gres; exact H18.
          * solve_keeps_but.
      - (* [comment removed for export] *)
        eapply (Kcont _); [ | | | | | lia]; cycle 4.
        + pre1 H14 H12 H15.
          stepb_ft F_668c0 D_668c0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hml0).
          stepb_tk F_668c4 D_668c4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hl0).
          sz5 sbs Hsbs Hsv.
          stepb_ft F_668f0 D_668f0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hml0).
          sz6 sbs Hsbs Hsv H12.
          stepb_ft F_66904 D_66904 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          pu_refl.
        + unfold dregs; post_tac.
        + gres; reflexivity.
        + gres; exact H18.
        + solve_keeps_but. }
    apply TO_ED4.
    { (* [comment removed for export] *)
      intros [Hl0 Hlt]. eexists _, _. split.
      - pre1 H14 H12 H15.
        stepb_ft F_668c0 D_668c0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hml0).
        stepb_ft F_668c4 D_668c4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; exact Hl0).
        stepn F_668c8 D_668c8.
        stepn F_668cc D_668cc. getr_hyps. rewrite E_pm.
        stepn F_668d0 D_668d0. addi_renorm.
        stepb_tk F_668d4 D_668d4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hml0).
        sz6 sbs Hsbs Hsv H12.
        stepb_tk F_66904 D_66904 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      - split; [left; split; [reflexivity | unfold ntf_okay; right; right; left; split; assumption]|]. unfold dregs. post_tac. }
    intros r2 (B10 & B11 & B12 & B13) B14 B18 K2 RUN2 Hnstride.
    (* [comment removed for export] *)
    destruct (Z.eq_dec next g) as [Hng | Hng].
    2:{ eexists _, _. split.
        - eapply msteps_trans; [exact RUN2|].
          stepLD8 F_66908 D_66908 (Z_to_bv 64 next).
          stepb_tk F_6690c D_6690c ltac:(rewrite B10, c_eq_Z by lia; apply Z.eqb_neq; exact Hng).
          pu_refl.
        - split; [left; split; [reflexivity | unfold ntf_okay; right; right; right; left; exact Hng]|]. unfold dregs. post_tac. }
    (* [comment removed for export] *)
    destruct (Z.lt_ge_cases sc 7) as [Hs7 | Hs7].
    { eexists _, _. split.
      - eapply msteps_trans; [exact RUN2|].
        stepLD8 F_66908 D_66908 (Z_to_bv 64 next).
        stepb_ft F_6690c D_6690c ltac:(rewrite B10, Hng; apply c_eq_refl).
        stepn F_66910 D_66910. getr_hyps. unfold v_addi. rewrite (u_Z2bv sc) by lia.
        replace (Z_to_bv 64 (sc + -7)) with (Z_to_bv 64 (2^64 + sc - 7))
          by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z;
              rewrite (Z.mod_small (2^64 + sc - 7)) by lia; apply (Z.mod_unique (sc + -7) (2^64) (-1)); lia).
        stepn F_66914 D_66914.
        stepb_tk F_66918 D_66918 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      - split; [left; split; [reflexivity | unfold ntf_okay; do 4 right; left; exact Hs7]|]. unfold dregs. post_tac. }
    destruct (Z.lt_ge_cases 38 sc) as [Hs38 | Hs38].
    { eexists _, _. split.
      - eapply msteps_trans; [exact RUN2|].
        stepLD8 F_66908 D_66908 (Z_to_bv 64 next).
        stepb_ft F_6690c D_6690c ltac:(rewrite B10, Hng; apply c_eq_refl).
        stepn F_66910 D_66910. getr_hyps. addi_renorm.
        stepn F_66914 D_66914.
        stepb_tk F_66918 D_66918 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      - split; [left; split; [reflexivity | unfold ntf_okay; do 5 right; left; exact Hs38]|]. unfold dregs. post_tac. }
    (* [comment removed for export] *)
    pose proof (M_bnc ltac:(lia)) as Mb.
    destruct (Z.lt_ge_cases bnc 100) as [Hb | Hb].
    { eexists _, _. split.
      - eapply msteps_trans; [exact RUN2|].
        stepLD8 F_66908 D_66908 (Z_to_bv 64 next).
        stepb_ft F_6690c D_6690c ltac:(rewrite B10, Hng; apply c_eq_refl).
        stepn F_66910 D_66910. getr_hyps. addi_renorm.
        stepn F_66914 D_66914.
        stepb_ft F_66918 D_66918 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_6691c D_6691c. getr_hyps. rewrite (v_add_ZZ 700056 (sc - 7)) by lia.
        stepLBU F_66920 D_66920 (Z_to_bv 8 bnc) ltac:(unfold v_addi; unorm; unfold ctx_bounces, CTX in Mb; replace (700056 + (sc - 7) + 880)%Z with (700056 + 880 + (sc - 7))%Z by lia; exact Mb).
        rewrite (u8_of_Z bnc) by lia.
        stepn F_66924 D_66924.
        stepb_tk F_66928 D_66928 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      - split; [left; split; [reflexivity | unfold ntf_okay; do 6 right; left; exact Hb]|]. unfold dregs. post_tac. }
    (* [comment removed for export] *)
    pose proof (M_usage ltac:(lia)) as Mu.
    assert (Hcnt9 : (0 <= 8 * lastidx + lastidx + 9 < 2^64)%Z) by lia.
    destruct (Z.lt_ge_cases usage (9 * (lastidx + 1))) as [Hu | Hu].
    { eexists _, _. split.
      - eapply msteps_trans; [exact RUN2|].
        stepLD8 F_66908 D_66908 (Z_to_bv 64 next).
        stepb_ft F_6690c D_6690c ltac:(rewrite B10, Hng; apply c_eq_refl).
        stepn F_66910 D_66910. getr_hyps. addi_renorm.
        stepn F_66914 D_66914.
        stepb_ft F_66918 D_66918 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_6691c D_6691c. getr_hyps. rewrite (v_add_ZZ 700056 (sc - 7)) by lia.
        stepLBU F_66920 D_66920 (Z_to_bv 8 bnc) ltac:(unfold v_addi; unorm; unfold ctx_bounces, CTX in Mb; replace (700056 + (sc - 7) + 880)%Z with (700056 + 880 + (sc - 7))%Z by lia; exact Mb).
        rewrite (u8_of_Z bnc) by lia.
        stepn F_66924 D_66924.
        stepb_ft F_66928 D_66928 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_6692c D_6692c. getr_hyps. rewrite (v_slli_Z sc 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
        stepn F_66930 D_66930. getr_hyps. rewrite (v_add_ZZ 700056 (sc * 8)) by lia.
        stepLD F_66934 D_66934 (word_to_le_bytes 8 (Z_to_bv 64 usage)) (Z_to_bv 64 usage)
          ltac:(unfold v_addi; unorm; unfold ctx_usage, CTX in Mu; replace (700056 + sc * 8 + 464)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact Mu)
          ltac:(apply bytes_le_to_Z_8).
        stepn F_66938 D_66938. getr_hyps. rewrite (v_slli_Z lastidx 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
        stepn F_6693c D_6693c. getr_hyps. rewrite (v_add_ZZ (lastidx * 8) lastidx) by lia.
        stepn F_66940 D_66940. unfold v_addi. unorm.
        stepb_tk F_66944 D_66944 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      - split; [right; repeat split; try reflexivity; try assumption; lia|]. unfold dregs. post_tac. }
    destruct (Z.lt_ge_cases 18 lastidx) as [H18l | H18l].
    { eexists _, _. split.
      - eapply msteps_trans; [exact RUN2|].
        stepLD8 F_66908 D_66908 (Z_to_bv 64 next).
        stepb_ft F_6690c D_6690c ltac:(rewrite B10, Hng; apply c_eq_refl).
        stepn F_66910 D_66910. getr_hyps. addi_renorm.
        stepn F_66914 D_66914.
        stepb_ft F_66918 D_66918 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_6691c D_6691c. getr_hyps. rewrite (v_add_ZZ 700056 (sc - 7)) by lia.
        stepLBU F_66920 D_66920 (Z_to_bv 8 bnc) ltac:(unfold v_addi; unorm; unfold ctx_bounces, CTX in Mb; replace (700056 + (sc - 7) + 880)%Z with (700056 + 880 + (sc - 7))%Z by lia; exact Mb).
        rewrite (u8_of_Z bnc) by lia.
        stepn F_66924 D_66924.
        stepb_ft F_66928 D_66928 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_6692c D_6692c. getr_hyps. rewrite (v_slli_Z sc 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
        stepn F_66930 D_66930. getr_hyps. rewrite (v_add_ZZ 700056 (sc * 8)) by lia.
        stepLD F_66934 D_66934 (word_to_le_bytes 8 (Z_to_bv 64 usage)) (Z_to_bv 64 usage)
          ltac:(unfold v_addi; unorm; unfold ctx_usage, CTX in Mu; replace (700056 + sc * 8 + 464)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact Mu)
          ltac:(apply bytes_le_to_Z_8).
        stepn F_66938 D_66938. getr_hyps. rewrite (v_slli_Z lastidx 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
        stepn F_6693c D_6693c. getr_hyps. rewrite (v_add_ZZ (lastidx * 8) lastidx) by lia.
        stepn F_66940 D_66940. unfold v_addi. unorm.
        stepb_ft F_66944 D_66944 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_66948 D_66948.
        stepb_tk F_6694c D_6694c ltac:(rewrite B14, c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      - split; [right; repeat split; try reflexivity; try assumption; lia|]. unfold dregs. post_tac. }
    (* [comment removed for export] *)
    eexists _, _. split.
    - eapply msteps_trans; [exact RUN2|].
      stepLD8 F_66908 D_66908 (Z_to_bv 64 next).
      stepb_ft F_6690c D_6690c ltac:(rewrite B10, Hng; apply c_eq_refl).
      stepn F_66910 D_66910. getr_hyps. addi_renorm.
      stepn F_66914 D_66914.
      stepb_ft F_66918 D_66918 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepn F_6691c D_6691c. getr_hyps. rewrite (v_add_ZZ 700056 (sc - 7)) by lia.
      stepLBU F_66920 D_66920 (Z_to_bv 8 bnc) ltac:(unfold v_addi; unorm; unfold ctx_bounces, CTX in Mb; replace (700056 + (sc - 7) + 880)%Z with (700056 + 880 + (sc - 7))%Z by lia; exact Mb).
      rewrite (u8_of_Z bnc) by lia.
      stepn F_66924 D_66924.
      stepb_ft F_66928 D_66928 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepn F_6692c D_6692c. getr_hyps. rewrite (v_slli_Z sc 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
      stepn F_66930 D_66930. getr_hyps. rewrite (v_add_ZZ 700056 (sc * 8)) by lia.
      stepLD F_66934 D_66934 (word_to_le_bytes 8 (Z_to_bv 64 usage)) (Z_to_bv 64 usage)
        ltac:(unfold v_addi; unorm; unfold ctx_usage, CTX in Mu; replace (700056 + sc * 8 + 464)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact Mu)
        ltac:(apply bytes_le_to_Z_8).
      stepn F_66938 D_66938. getr_hyps. rewrite (v_slli_Z lastidx 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
      stepn F_6693c D_6693c. getr_hyps. rewrite (v_add_ZZ (lastidx * 8) lastidx) by lia.
      stepn F_66940 D_66940. unfold v_addi. unorm.
      stepb_ft F_66944 D_66944 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepn F_66948 D_66948.
      stepb_ft F_6694c D_6694c ltac:(rewrite B14, c_ltu_Z by lia; apply Z.ltb_ge; lia).
      pu_refl.
    - split; [left; split; [reflexivity | unfold ntf_okay; do 7 right; lia]|]. unfold dregs. post_tac.
  Qed.

End D.
End UbMhNtfA.
Module UbMhNtfB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section B.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g sc hd tl mask self : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hmask : (0 <= mask < 2^32)%Z.
  Hypothesis Hsc : (0 <= sc < 64)%Z.
  Hypothesis Hhd : (0 <= hd < 2^64)%Z.
  Hypothesis Htl : (0 <= tl < 2^64)%Z.

  (* [comment removed for export] *)
  Lemma segB3 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 13 = s32 mask -> mask <> 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x669ec : word) m rom) (mkst regs' (0x66c10 : word) m rom)
      /\ getr regs' 14 = Z_to_bv 64 (g + 28) /\ keeps_but [14]%bv regs regs'.
  Proof.
    intros regs rom H10 H13 Hne. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepn F_66998 D_66998. rewrite H10. addi_renorm.
      stepb_tk F_6699c D_6699c ltac:(rewrite H13, c_eq_s32_0; apply Z.eqb_neq; rewrite Z.mod_small by lia; exact Hne).
      apply mst_refl.
    - split; [gres; reflexivity | solve_keeps_but].
  Qed.

  Hypothesis M_img : sz_img m.
  Hypothesis M_act : rdn RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)).

  Definition clobB : list reg := [12; 13; 14; 15]%bv.

  (* [comment removed for export] *)
  Lemma segB2_pfx : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 sc -> getr regs 13 = s32 mask ->
    mask = 0%Z -> (sc < 48)%Z ->
    exists regs', msteps RSEGS (mkst regs (0x669ec : word) m rom) (mkst regs' (0x66a14 : word) m rom)
      /\ getr regs' 14 = Z_to_bv 64 (g + 28) /\ getr regs' 12 = Z_to_bv 64 hd /\ getr regs' 13 = Z_to_bv 64 (CTX + 8 * sc)
      /\ getr regs' 10 = Z_to_bv 64 g /\ keeps_but clobB regs regs'.
  Proof.
    intros regs rom H10 H12 H13 Hm0 H48. ceil; unfold HEAPLO, CTX in *.
    eexists. split.
    - stepn F_66998 D_66998. rewrite H10. addi_renorm.
      stepb_ft F_6699c D_6699c ltac:(rewrite H13, Hm0; apply c_eq_refl).
      stepn F_669a0 D_669a0.
      stepb_tk F_669a4 D_669a4 ltac:(rewrite H12, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_669ac D_669ac. rewrite H12. rewrite (v_slli_Z sc 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
      stepn F_669b0 D_669b0.
      stepn F_669b4 D_669b4.
      stepn F_669b8 D_669b8. rewrite (v_add_ZZ 700056 (sc * 8)) by lia.
      stepLD F_669bc D_669bc (word_to_le_bytes 8 (Z_to_bv 64 hd)) (Z_to_bv 64 hd)
        ltac:(unfold v_addi; unorm; unfold ctx_active, CTX in M_act;
              replace (700056 + sc * 8 + 80)%Z with (700056 + 80 + 8 * sc)%Z by lia; exact M_act)
        ltac:(apply bytes_le_to_Z_8).
      apply mst_refl.
    - repeat split; gres; try reflexivity; try solve_keeps_but. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma segB2h : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 hd -> hd = g ->
    exists regs', msteps RSEGS (mkst regs (0x66a14 : word) m rom) (mkst regs' (0x66c10 : word) m rom)
      /\ keeps_but []%list regs regs'.
  Proof.
    intros regs rom H10 H12 He. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepb_tk F_669c0 D_669c0 ltac:(rewrite H12, H10, He; apply c_eq_refl). apply mst_refl.
    - apply keeps_but_refl.
  Qed.

  Hypothesis M_next : rdn RSEGS m (Z_to_bv 64 (g + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis M_prev : rdn RSEGS m (Z_to_bv 64 g) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis SOKg : store_ok RSEGS m (Z_to_bv 64 g) 16%nat = true.

  (* [comment removed for export] *)
  Definition m_q : mem :=
    wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 hd)))
      (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 tl)))
      (Z_to_bv 64 (tl + 8)) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 hd) (word_to_le_bytes 8 (Z_to_bv 64 g)).

  Lemma segB2q : forall regs rom,
    (HEAPLO <= hd)%Z -> (hd + 40 <= CEIL)%Z -> (HEAPLO <= tl)%Z -> (tl + 40 <= CEIL)%Z ->
    (g + 40 <= hd \/ hd + 40 <= g)%Z -> (g + 40 <= tl \/ tl + 40 <= g)%Z ->
    rdn RSEGS m (Z_to_bv 64 hd) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tl)) ->
    store_ok RSEGS m (Z_to_bv 64 hd) 8%nat = true -> store_ok RSEGS m (Z_to_bv 64 (tl + 8)) 8%nat = true ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 hd -> hd <> g -> hd <> 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66a14 : word) m rom) (mkst regs' (0x66c10 : word) m_q rom)
      /\ keeps_but [12; 15]%bv regs regs'.
  Proof.
    intros regs rom Hh1 Hh2 Ht1 Ht2 Dgh Dgt M_tl SOKh SOKt H10 H12 Hne Hnz. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepb_ft F_669c0 D_669c0 ltac:(rewrite H12, H10, c_eq_Z by lia; apply Z.eqb_neq; exact Hne).
      stepLD8 F_669c4 D_669c4 (Z_to_bv 64 0).
      stepb_tk F_669c8 D_669c8 ltac:(apply c_eq_refl).
      stepLD8 F_669d0 D_669d0 (Z_to_bv 64 0).
      stepb_tk F_669d4 D_669d4 ltac:(apply c_eq_refl).
      stepb_ft F_669dc D_669dc ltac:(rewrite H12, c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepSTx F_669e0 D_669e0 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 hd) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepLD8 F_669e4 D_669e4 (Z_to_bv 64 tl).
      stepSTx F_669e8 D_669e8 (Z_to_bv 64 g) (Z_to_bv 64 tl) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepSTx F_669ec D_669ec (Z_to_bv 64 (tl + 8)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKt).
      stepLD8 F_669f0 D_669f0 (Z_to_bv 64 hd).
      stepn F_669f4 D_669f4.
      stepSTx F_66bb8 D_66bb8 (Z_to_bv 64 hd) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKh).
      unfold m_q. apply mst_refl.
    - solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Definition m_e : mem :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 g)).

  Lemma segB2e : forall regs rom,
    store_ok RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = true ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 hd -> getr regs 13 = Z_to_bv 64 (CTX + 8 * sc) -> hd = 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66a14 : word) m rom) (mkst regs' (0x66c10 : word) m_e rom)
      /\ keeps_but [12; 15]%bv regs regs'.
  Proof.
    intros regs rom SOKa H10 H12 H13 Hz. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_e, ctx_active, CTX.
    eexists. split.
    - stepb_ft F_669c0 D_669c0 ltac:(rewrite H12, H10, c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepLD8 F_669c4 D_669c4 (Z_to_bv 64 0).
      stepb_tk F_669c8 D_669c8 ltac:(apply c_eq_refl).
      stepLD8 F_669d0 D_669d0 (Z_to_bv 64 0).
      stepb_tk F_669d4 D_669d4 ltac:(apply c_eq_refl).
      stepb_tk F_669dc D_669dc ltac:(rewrite H12, Hz; apply c_eq_refl).
      stepn F_66bac D_66bac. rewrite H13.
      replace (v_addi (Z_to_bv 64 (700056 + 8 * sc)) 80) with (Z_to_bv 64 (700056 + 80 + 8 * sc)) by (unfold v_addi; unorm; f_equal; lia).
      stepSTx F_66bb0 D_66bb0 (Z_to_bv 64 g) (Z_to_bv 64 g) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepSTx F_66bb4 D_66bb4 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 g) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepSTx F_66bb8 D_66bb8 (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKa).
      apply mst_refl.
    - solve_keeps_but.
  Qed.
End B.
End UbMhNtfB.
Module UbMhNtfC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
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

Section DQ.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g sc nxt prv hd : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hsc : (0 <= sc < 64)%Z.
  Hypothesis Hnxt : (0 <= nxt < 2^64)%Z.
  Hypothesis Hprv : (0 <= prv < 2^64)%Z.
  Hypothesis Hhd : (0 <= hd < 2^64)%Z.
  Hypothesis M_img : sz_img m.
  Hypothesis M_next : rdn RSEGS m (Z_to_bv 64 (g + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 nxt)).

  (* [comment removed for export] *)
  Lemma segL0 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> nxt = 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x669a4 : word) m rom) (mkst regs' (0x66ab8 : word) m rom)
      /\ keeps_but [13]%bv regs regs'.
  Proof using M_next Hg RN.
    intros regs rom H10 Hz. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepLD8 F_66950 D_66950 (Z_to_bv 64 nxt).
      stepb_tk F_66954 D_66954 ltac:(rewrite Hz; apply c_eq_refl).
      pu_refl.
    - solve_keeps_but.
  Qed.

  Hypothesis M_prev : rdn RSEGS m (Z_to_bv 64 g) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 prv)).
  Hypothesis M_act : rdn RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)).
  Hypothesis SOKg : store_ok RSEGS m (Z_to_bv 64 g) 16%nat = true.
  Hypothesis SOKa : store_ok RSEGS m (Z_to_bv 64 (ctx_active sc)) 8%nat = true.

  Definition clobDQ : list reg := [11; 12; 13; 14]%bv.

  (* [comment removed for export] *)
  Lemma segDQ_pfx : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 sc -> getr regs 18 = Z_to_bv 64 CTX ->
    nxt <> 0%Z -> (sc < 48)%Z ->
    exists regs', msteps RSEGS (mkst regs (0x669a4 : word) m rom) (mkst regs' (0x669c4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 (CTX + 8 * sc) /\ getr regs' 12 = Z_to_bv 64 hd
      /\ getr regs' 13 = Z_to_bv 64 nxt /\ getr regs' 18 = Z_to_bv 64 CTX /\ keeps_but clobDQ regs regs'.
  Proof using M_act M_next Hnxt Hsc Hg RN.
    intros regs rom H10 H12 H18 Hnz H48. ceil; unfold HEAPLO, ctx_active, CTX in *.
    eexists. split.
    - stepLD8 F_66950 D_66950 (Z_to_bv 64 nxt).
      stepb_ft F_66954 D_66954 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepn F_66958 D_66958.
      stepb_tk F_6695c D_6695c ltac:(rewrite H12, c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_66964 D_66964. rewrite H12. rewrite (v_slli_Z sc 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
      stepn F_66968 D_66968. rewrite H18. rewrite (v_add_ZZ 700056 (sc * 8)) by lia.
      stepLD F_6696c D_6696c (word_to_le_bytes 8 (Z_to_bv 64 hd)) (Z_to_bv 64 hd)
        ltac:(unfold v_addi; unorm; replace (700056 + sc * 8 + 80)%Z with (700056 + 80 + 8 * sc)%Z by lia; exact M_act)
        ltac:(apply bytes_le_to_Z_8).
      pu_refl.
    - repeat split; gres; try reflexivity; try solve_keeps_but. f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  Definition m_dqn : mem :=   (* [comment removed for export] *)
    wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (prv + 8)) (word_to_le_bytes 8 (Z_to_bv 64 nxt)))
      (Z_to_bv 64 nxt) (word_to_le_bytes 8 (Z_to_bv 64 prv)))
      (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Definition m_dqh : mem :=   (* [comment removed for export] *)
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (prv + 8)) (word_to_le_bytes 8 (Z_to_bv 64 nxt)))
      (Z_to_bv 64 nxt) (word_to_le_bytes 8 (Z_to_bv 64 prv)))
      (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 nxt)))
      (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Definition m_dqs : mem :=   (* [comment removed for export] *)
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (ctx_active sc)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Hypothesis Rnxt : (HEAPLO <= nxt)%Z /\ (nxt + 40 <= CEIL)%Z /\ ((nxt + 40 <= IMG_LO)%Z \/ (IMG_HI <= nxt)%Z).
  Hypothesis Rprv : (HEAPLO <= prv)%Z /\ (prv + 40 <= CEIL)%Z /\ ((prv + 40 <= IMG_LO)%Z \/ (IMG_HI <= prv)%Z).
  Hypothesis Dgn : (g + 40 <= nxt \/ nxt + 40 <= g)%Z.
  Hypothesis Dgp : (g + 40 <= prv \/ prv + 40 <= g)%Z.
  Hypothesis SOKn : store_ok RSEGS m (Z_to_bv 64 nxt) 8%nat = true.
  Hypothesis SOKp : store_ok RSEGS m (Z_to_bv 64 (prv + 8)) 8%nat = true.

  (* [comment removed for export] *)
  Lemma segDQn : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 (CTX + 8 * sc) -> getr regs 12 = Z_to_bv 64 hd ->
    getr regs 13 = Z_to_bv 64 nxt -> nxt <> g -> hd <> g ->
    exists regs', msteps RSEGS (mkst regs (0x669c4 : word) m rom) (mkst regs' (0x66ab8 : word) m_dqn rom)
      /\ keeps_but [13; 14]%bv regs regs'.
  Proof using SOKp SOKn Dgp Dgn Rprv Rnxt SOKg M_act M_prev M_next Hhd Hprv Hnxt Hsc Hg RN.
    intros regs rom H10 H11 H12 H13 Hng Hhg. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_dqn, ctx_active, CTX.
    eexists. split.
    - stepb_ft F_66970 D_66970 ltac:(rewrite H13, H10, c_eq_Z by lia; apply Z.eqb_neq; exact Hng).
      stepLD8 F_66974 D_66974 (Z_to_bv 64 prv).
      stepSTx F_66978 D_66978 (Z_to_bv 64 (prv + 8)) (Z_to_bv 64 nxt) ltac:(store_ok_peel; exact SOKp).
      stepLD8 F_6697c D_6697c (Z_to_bv 64 prv).
      stepLD8 F_66980 D_66980 (Z_to_bv 64 nxt).
      stepSTx F_66984 D_66984 (Z_to_bv 64 nxt) (Z_to_bv 64 prv) ltac:(store_ok_peel; exact SOKn).
      stepLD F_66988 D_66988 (word_to_le_bytes 8 (Z_to_bv 64 hd)) (Z_to_bv 64 hd)
        ltac:(unfold v_addi; unorm; replace (700056 + 8 * sc + 80)%Z with (700056 + 80 + 8 * sc)%Z by lia; repeat rdn_peel1; exact M_act)
        ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_6698c D_6698c ltac:(rewrite H10, c_eq_Z by lia; apply Z.eqb_neq; exact Hhg).
      stepSTx F_66a00 D_66a00 (Z_to_bv 64 g) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepSTx F_66a04 D_66a04 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepb_tk F_66a08 D_66a08 ltac:(rewrite H12, H10, c_eq_Z by lia; apply Z.eqb_neq; exact Hhg).
      pu_refl.
    - solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma segDQh : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 (CTX + 8 * sc) -> getr regs 12 = Z_to_bv 64 hd ->
    getr regs 13 = Z_to_bv 64 nxt -> nxt <> g -> hd = g ->
    exists regs', msteps RSEGS (mkst regs (0x669c4 : word) m rom) (mkst regs' (0x66a68 : word) m_dqh rom)
      /\ getr regs' 11 = Z_to_bv 64 nxt /\ keeps_but [11; 13; 14]%bv regs regs'.
  Proof using SOKp SOKn Dgp Dgn Rprv Rnxt SOKa SOKg M_act M_prev M_next Hprv Hnxt Hsc Hg RN.
    intros regs rom H10 H11 H12 H13 Hng Hhg. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_dqh, ctx_active, CTX.
    assert (Hnz : nxt <> 0%Z) by lia.
    eexists. split.
    - stepb_ft F_66970 D_66970 ltac:(rewrite H13, H10, c_eq_Z by lia; apply Z.eqb_neq; exact Hng).
      stepLD8 F_66974 D_66974 (Z_to_bv 64 prv).
      stepSTx F_66978 D_66978 (Z_to_bv 64 (prv + 8)) (Z_to_bv 64 nxt) ltac:(store_ok_peel; exact SOKp).
      stepLD8 F_6697c D_6697c (Z_to_bv 64 prv).
      stepLD8 F_66980 D_66980 (Z_to_bv 64 nxt).
      stepSTx F_66984 D_66984 (Z_to_bv 64 nxt) (Z_to_bv 64 prv) ltac:(store_ok_peel; exact SOKn).
      stepLD F_66988 D_66988 (word_to_le_bytes 8 (Z_to_bv 64 hd)) (Z_to_bv 64 hd)
        ltac:(unfold v_addi; unorm; replace (700056 + 8 * sc + 80)%Z with (700056 + 80 + 8 * sc)%Z by lia; repeat rdn_peel1; exact M_act)
        ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_6698c D_6698c ltac:(rewrite H10, Hhg; apply c_eq_refl).
      stepLD8 F_66990 D_66990 (Z_to_bv 64 nxt).
      stepn F_66994 D_66994.
      stepSTx F_669fc D_669fc (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 nxt) ltac:(store_ok_peel; exact SOKa).
      stepSTx F_66a00 D_66a00 (Z_to_bv 64 g) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepSTx F_66a04 D_66a04 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepb_ft F_66a08 D_66a08 ltac:(rewrite H12, H10, Hhg; apply c_eq_refl).
      stepLD F_66a0c D_66a0c (word_to_le_bytes 8 (Z_to_bv 64 nxt)) (Z_to_bv 64 nxt)
        ltac:(unfold v_addi; unorm; replace (700056 + 8 * sc + 80)%Z with (700056 + 80 + 8 * sc)%Z by lia; rdn_solve)
        ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_66a10 D_66a10 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      pu_refl.
    - split; [gres; reflexivity | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  Lemma segDQs : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 (CTX + 8 * sc) -> getr regs 12 = Z_to_bv 64 hd ->
    getr regs 13 = Z_to_bv 64 nxt -> nxt = g ->
    exists regs', msteps RSEGS (mkst regs (0x669c4 : word) m rom) (mkst regs' (0x66ab8 : word) m_dqs rom)
      /\ keeps_but [11; 13]%bv regs regs'.
  Proof using Rnxt SOKa SOKg Hhd Hsc Hg RN.
    intros regs rom H10 H11 H12 H13 Hng. ceil; unfold HEAPLO, ctx_active, CTX in *. unfold m_dqs, ctx_active, CTX.
    Ltac dqs_pfx H13 H10 Hng SOKa SOKg :=
      stepb_tk F_66970 D_66970 ltac:(rewrite H13, H10, Hng; apply c_eq_refl);
      stepn F_669f8 D_669f8;
      stepSTx F_669fc D_669fc (Z_to_bv 64 (700056 + 80 + 8 * sc)) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKa);
      stepSTx F_66a00 D_66a00 (Z_to_bv 64 g) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia);
      stepSTx F_66a04 D_66a04 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 16%nat); [ | exact SOKg | | ]; zsimp; lia).
    (* [comment removed for export] *)
    destruct (Z.eq_dec hd g) as [Hhg|Hhg].
    - eexists. split.
      + dqs_pfx H13 H10 Hng SOKa SOKg.
        stepb_ft F_66a08 D_66a08 ltac:(rewrite H12, H10, Hhg; apply c_eq_refl).
        stepLD F_66a0c D_66a0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(unfold v_addi; unorm; replace (700056 + 8 * sc + 80)%Z with (700056 + 80 + 8 * sc)%Z by lia; rdn_solve)
          ltac:(apply bytes_le_to_Z_8).
        stepb_tk F_66a10 D_66a10 ltac:(apply c_eq_refl).
        pu_refl.
      + solve_keeps_but.
    - eexists. split.
      + dqs_pfx H13 H10 Hng SOKa SOKg.
        stepb_tk F_66a08 D_66a08 ltac:(rewrite H12, H10, c_eq_Z by lia; apply Z.eqb_neq; exact Hhg).
        pu_refl.
      + solve_keeps_but.
  Qed.
End DQ.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACT.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (h memh b fr : Z).
  Hypothesis Hh : (HEAPLO <= h)%Z /\ (h + 40 <= CEIL)%Z /\ ((h + 40 <= IMG_LO)%Z \/ (IMG_HI <= h)%Z) /\ (h mod 8 = 0)%Z.
  Hypothesis Hmemh : (HEAPLO <= memh)%Z /\ (memh + 16 <= CEIL)%Z /\ ((memh + 16 <= IMG_LO)%Z \/ (IMG_HI <= memh)%Z).
  Hypothesis Hb : (0 <= b < 256)%Z.
  Hypothesis Hfr : (0 <= fr < 2^32)%Z.
  Hypothesis M_av : rdn RSEGS m (Z_to_bv 64 (h + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis M_mem : rdn RSEGS m (Z_to_bv 64 (h + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 memh)).
  Hypothesis M_aib : rdn RSEGS m (Z_to_bv 64 (memh + 8)) 1%nat = Some [Z_to_bv 8 b].
  Hypothesis M_fr : rdn RSEGS m (Z_to_bv 64 (h + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr)).
  Hypothesis SOKh : store_ok RSEGS m (Z_to_bv 64 (h + 24)) 8%nat = true.
  #[local] Notation ai := (b mod 32)%Z.

  Definition m_act : mem :=
    wbytes (wbytes m (Z_to_bv 64 (h + 28)) (word_to_le_bytes 4 (Z_to_bv 64 (hi_bits fr (ai + 1)))))
           (Z_to_bv 64 (h + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (lo_bits fr (ai + 1)))).

  Definition clobACT : list reg := [5; 12; 13; 14; 15; 16; 17]%bv.

  Lemma segACT : forall regs rom,
    getr regs 11 = Z_to_bv 64 h ->
    exists regs', msteps RSEGS (mkst regs (0x66a68 : word) m rom) (mkst regs' (0x66ab8 : word) m_act rom)
      /\ keeps_but clobACT regs regs'.
  Proof using SOKh M_fr M_aib M_mem M_av Hfr Hb Hmemh Hh memh RN.
    intros regs rom H11. ceil; unfold HEAPLO in *.
    assert (Hai : (0 <= ai < 32)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Hal : (bv_unsigned (Z_to_bv 64 (h + 28)) mod 4 = 0)%Z).
    { rewrite u_Z2bv by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    eexists. split.
    - stepLD F_66a14 D_66a14 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_tk F_66a18 D_66a18 ltac:(apply c_eq_refl).
      stepLD8 F_66a20 D_66a20 (Z_to_bv 64 memh).
      stepLBU F_66a24 D_66a24 (Z_to_bv 8 b) ltac:(addr_norm; rdn_solve).
      rewrite (u8_of_Z b) by lia.
      stepn F_66a28 D_66a28.
      stepn F_66a2c D_66a2c. rewrite v_sllw_Z_s32 by lia.
      stepn F_66a30 D_66a30. rewrite H11. addi_renorm.
      stepn F_66a34 D_66a34.
      stepLD F_66a38 D_66a38 (word_to_le_bytes 4 (Z_to_bv 64 fr)) (Z_to_bv 64 fr)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_66a3c D_66a3c.
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply (step_lr_w RSEGS _ _ _ _ _ true true 17 13 (word_to_le_bytes 4 (Z_to_bv 64 fr)) (Z_to_bv 64 fr));
          [exact F_66a40 | reflexivity | exact D_66a40 | gres; exact Hal | gres; addr_norm; rdn_solve | apply bytes_le_to_Z_4; u_norm; lia ]
        | step_simpl ].
      cbn [bv_eqb]. rewrite v_lw_s32 by lia.
      chain_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_66a44 | reflexivity | exact D_66a44 | gres; apply c_eq_refl ]
        | step_simpl ].
      chain_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_66a48 | reflexivity | exact D_66a48 | gres; exact Hal | gres; reflexivity
            | gres; store_ok_peel; eapply (store_ok_sub _ _ _ _ 8%nat); [ | exact SOKh | | ]; zsimp; lia ]
        | step_simpl ].
      cbn [bv_eqb]. vnorm.
      stepb_ft F_66a4c D_66a4c ltac:(cond_compute).
      stepn F_66a50 D_66a50. rewrite v_addiw_s32, Z.add_0_r.
      stepb_ft F_66a54 D_66a54 ltac:(apply c_eq_refl).
      stepn F_66a58 D_66a58.
      stepn F_66a5c D_66a5c.
      stepSTx F_66a60 D_66a60 (Z_to_bv 64 (h + 24)) (v_and (s32 fr) (v_addi (s32 (2 * 2 ^ ai)) (-1)))
        ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 8%nat); [ | exact SOKh | | ]; zsimp; lia).
      rewrite (act_hi_word fr ai) by lia. rewrite (act_lo_word fr ai) by lia.
      unfold m_act. pu_refl.
    - solve_keeps_but.
  Qed.
End ACT.
End UbMhNtfC.
Module UbMhNtfD.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
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

Lemma and_pagemask : forall W, (0 <= W < 2^64)%Z ->
  v_and (Z_to_bv 64 W) (Z_to_bv 64 18446744073709547520) = Z_to_bv 64 (w_maplen W * 4096).
Proof.
  intros W HW.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite v_and_Z by lia. f_equal. rewrite land_pagemask by lia. unfold w_maplen. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma sc_of_W : forall W, (0 <= W < 2^64)%Z -> v_srli (v_slli (Z_to_bv 64 W) 52) 58 = Z_to_bv 64 (w_sizeclass W).
Proof.
  intros W HW. unfold v_srli, v_slli, w_sizeclass. f_equal. rewrite (u_Z2bv W) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. apply sc_extract. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FG.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g W usage memg seq : Z).
  #[local] Notation sc := (w_sizeclass W).
  #[local] Notation maplen := (w_maplen W).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis HW : (0 <= W < 2^64)%Z.
  Hypothesis Husage : (0 <= usage < 2^64)%Z.
  Hypothesis Hmemg : (0 <= memg < 2^64)%Z.
  Hypothesis Hseq : (0 <= seq < 256)%Z.
  Hypothesis M_W : rdn RSEGS m (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W)).
  Hypothesis M_mem : rdn RSEGS m (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 memg)).
  Hypothesis M_usage : (sc < 48)%Z -> rdn RSEGS m (Z_to_bv 64 (ctx_usage sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 usage)).
  Hypothesis M_seq : rdn RSEGS m (Z_to_bv 64 ctx_seq) 1%nat = Some [Z_to_bv 8 seq].
  Hypothesis SOKctx : store_ok RSEGS m (Z_to_bv 64 CTX) 928%nat = true.

  Lemma d_sc : (0 <= sc < 64)%Z. Proof using. unfold w_sizeclass; apply Z.mod_pos_bound; lia. Qed.

  (* [comment removed for export] *)
  Definition usage_word : word := v_add (Z_to_bv 64 usage) (v_ori (v_xori (Z_to_bv 64 W) (-1)) (-32)).
  Definition m_u : mem := if (sc <? 48)%Z then wbytes m (Z_to_bv 64 (ctx_usage sc)) (word_to_le_bytes 8 usage_word) else m.

  Lemma segFGu : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 18 = Z_to_bv 64 CTX ->
    exists regs', msteps RSEGS (mkst regs (0x66ab8 : word) m rom) (mkst regs' (0x66aec : word) m_u rom)
      /\ getr regs' 11 = Z_to_bv 64 sc /\ getr regs' 12 = Z_to_bv 64 W /\ keeps_but [11; 12; 13; 14]%bv regs regs'.
  Proof using SOKctx M_usage M_W HW Hg RN.
    intros regs rom H10 H18. pose proof d_sc as HS. ceil; unfold HEAPLO, ctx_usage, CTX in *. unfold m_u, ctx_usage, CTX.
    destruct (Z.lt_ge_cases sc 48) as [H48|H48].
    - replace (sc <? 48)%Z with true by (symmetry; apply Z.ltb_lt; exact H48).
      pose proof (M_usage H48) as Mu.
      eexists. split.
      + stepLD8 F_66a64 D_66a64 (Z_to_bv 64 W).
        stepn F_66a68 D_66a68.
        stepn F_66a6c D_66a6c. rewrite sc_of_W by lia.
        stepn F_66a70 D_66a70.
        stepb_ft F_66a74 D_66a74 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        stepn F_66a78 D_66a78. rewrite (v_slli_Z sc 3) by (change (2^3)%Z with 8%Z; lia). change (2^3)%Z with 8%Z.
        stepn F_66a7c D_66a7c. rewrite H18. rewrite (v_add_ZZ 700056 (sc * 8)) by lia.
        stepLD F_66a80 D_66a80 (word_to_le_bytes 8 (Z_to_bv 64 usage)) (Z_to_bv 64 usage)
          ltac:(unfold v_addi; unorm; replace (700056 + sc * 8 + 464)%Z with (700056 + 464 + 8 * sc)%Z by lia; exact Mu)
          ltac:(apply bytes_le_to_Z_8).
        stepn F_66a84 D_66a84.
        stepn F_66a88 D_66a88.
        stepn F_66a8c D_66a8c.
        stepSTx F_66a90 D_66a90 (Z_to_bv 64 (700056 + 464 + 8 * sc)) usage_word
          ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOKctx | | ]; zsimp; lia).
        stepLD8 F_66a94 D_66a94 (Z_to_bv 64 W).
        pu_refl.
      + repeat split; gres; try reflexivity. solve_keeps_but.
    - replace (sc <? 48)%Z with false by (symmetry; apply Z.ltb_ge; exact H48).
      eexists. split.
      + stepLD8 F_66a64 D_66a64 (Z_to_bv 64 W).
        stepn F_66a68 D_66a68.
        stepn F_66a6c D_66a6c. rewrite sc_of_W by lia.
        stepn F_66a70 D_66a70.
        stepb_tk F_66a74 D_66a74 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
        pu_refl.
      + repeat split; gres; try reflexivity. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Variable m1 : mem.
  Hypothesis M1_W : rdn RSEGS m1 (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W)).
  Hypothesis M1_mem : rdn RSEGS m1 (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 memg)).
  Hypothesis M1_seq : rdn RSEGS m1 (Z_to_bv 64 ctx_seq) 1%nat = Some [Z_to_bv 8 seq].
  Hypothesis SOK1 : store_ok RSEGS m1 (Z_to_bv 64 CTX) 928%nat = true.

  Definition seq' : Z := if (seq =? 255)%Z then 1 else (seq + 1)%Z.
  Definition z8 := word_to_le_bytes 8 (Z_to_bv 64 0).
  Definition m_z : mem :=
    if (seq =? 255)%Z then
      wbytes (wbytes (wbytes (wbytes m1 (Z_to_bv 64 (CTX + 848)) z8) (Z_to_bv 64 (CTX + 856)) z8)
                     (Z_to_bv 64 (CTX + 864)) z8) (Z_to_bv 64 (CTX + 872)) z8
    else m1.
  Definition m_s : mem := wbytes m_z (Z_to_bv 64 ctx_seq) [Z_to_bv 8 seq'].
  Definition m_top : mem :=
    if ((7 <=? sc) && (sc <=? 38))%Z then wbytes m_s (Z_to_bv 64 (ctx_unmap_seq (sc - 7))) [Z_to_bv 8 seq'] else m_s.

  Lemma seq'_rng : (1 <= seq' < 257)%Z /\ (seq' < 256 \/ False)%Z.
  Proof using Hseq. unfold seq'. destruct (Z.eqb_spec seq 255); lia. Qed.

  Lemma segFGtop : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 sc -> getr regs 12 = Z_to_bv 64 W -> getr regs 18 = Z_to_bv 64 CTX ->
    maplen <> 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66aec : word) m1 rom) (mkst regs' (0x66b74 : word) m_top rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 (maplen * 4096) /\ getr regs' 12 = Z_to_bv 64 memg
      /\ getr regs' 18 = Z_to_bv 64 CTX /\ keeps_but [11; 12; 13]%bv regs regs'.
  Proof using SOK1 M1_seq M1_mem M1_W Hseq HW Hg RN.
    intros regs rom H10 H11 H12 H18 Hml. pose proof d_sc as HS.
    assert (HML : (0 < maplen < 2^52)%Z).
    { unfold w_maplen in *. split; [|apply Z.div_lt_upper_bound; lia].
      pose proof (Z.div_pos W 4096 ltac:(lia) ltac:(lia)). unfold w_maplen in Hml. lia. }
    ceil; unfold HEAPLO, ctx_seq, ctx_unmap_seq, CTX in *. unfold m_top, m_s, m_z, ctx_seq, ctx_unmap_seq, CTX.
    (* [comment removed for export] *)
    Ltac pfx H12 M1_seq :=
      stepn F_66a98 D_66a98; rewrite H12; rewrite v_srli_Z by lia; change (2^12)%Z with 4096%Z;
      replace (W / 4096)%Z with maplen by reflexivity;
      stepb_tk F_66a9c D_66a9c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia);
      stepLBU F_66ad0 D_66ad0 (Z_to_bv 8 seq) ltac:(addr_norm; exact M1_seq);
      rewrite (u8_of_Z seq) by lia;
      stepn F_66ad4 D_66ad4.
    Ltac zero4 SOK1 :=
      stepSTx F_66adc D_66adc (Z_to_bv 64 (700056 + 848)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOK1 | | ]; zsimp; lia);
      stepSTx F_66ae0 D_66ae0 (Z_to_bv 64 (700056 + 856)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOK1 | | ]; zsimp; lia);
      stepSTx F_66ae4 D_66ae4 (Z_to_bv 64 (700056 + 864)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOK1 | | ]; zsimp; lia);
      stepSTx F_66ae8 D_66ae8 (Z_to_bv 64 (700056 + 872)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOK1 | | ]; zsimp; lia);
      stepn F_66aec D_66aec;
      stepn F_66af0 D_66af0.
    Ltac tailA H11 SOK1 vv :=   (* [comment removed for export] *)
      stepn F_66af8 D_66af8; rewrite H11;
      stepn F_66afc D_66afc;
      stepSTx F_66b00 D_66b00 (Z_to_bv 64 (700056 + 912)) (Z_to_bv 64 vv) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOK1 | | ]; zsimp; lia).
    Ltac tailC H10 :=       (* [comment removed for export] *)
      stepLD8 F_66b10 D_66b10 (Z_to_bv 64 W);
      stepLD8 F_66b14 D_66b14 (Z_to_bv 64 memg);
      stepn F_66b18 D_66b18;
      stepn F_66b1c D_66b1c; rewrite and_pagemask by lia.
    pose proof seq'_rng as [SR _].
    destruct (Z.eqb_spec seq 255) as [Hs255|Hs255].
    - (* [comment removed for export] *)
      replace (seq =? 255)%Z with true by (symmetry; apply Z.eqb_eq; exact Hs255).
      assert (Es : seq' = 1%Z) by (unfold seq'; rewrite (proj2 (Z.eqb_eq seq 255) Hs255); reflexivity). rewrite Es.
      destruct (Sumbool.sumbool_of_bool ((7 <=? sc) && (sc <=? 38))%Z) as [Hb|Hb]; rewrite Hb.
      + assert (H7 : (7 <= sc <= 38)%Z) by (apply Bool.andb_true_iff in Hb; destruct Hb as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; lia).
        eexists. split.
        * pfx H12 M1_seq.
          stepb_ft F_66ad8 D_66ad8 ltac:(rewrite Hs255; apply c_eq_refl).
          zero4 SOK1.
          tailA H11 SOK1 1%Z.
          addi_renorm.
          stepb_ft F_66b04 D_66b04 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepn F_66b08 D_66b08. rewrite H18. rewrite (v_add_ZZ 700056 (sc - 7)) by lia.
          stepSTx F_66b0c D_66b0c (Z_to_bv 64 (700056 + 848 + (sc - 7))) (Z_to_bv 64 1) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOK1 | | ]; zsimp; lia).
          tailC H10.
          rewrite !(u_Z2bv 1) by lia. unfold z8. pu_refl.
        * repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
      + assert (H7 : ~ (7 <= sc <= 38)%Z).
        { intros H7. apply Bool.andb_false_iff in Hb. destruct Hb as [A|A]; [apply Z.leb_gt in A | apply Z.leb_gt in A]; lia. }
        (* [comment removed for export] *)
        destruct (Z.lt_ge_cases sc 7) as [Hs7|Hs7].
        * eexists. split.
          -- pfx H12 M1_seq.
             stepb_ft F_66ad8 D_66ad8 ltac:(rewrite Hs255; apply c_eq_refl).
             zero4 SOK1.
             tailA H11 SOK1 1%Z.
             unfold v_addi. rewrite (u_Z2bv sc) by lia.
             replace (Z_to_bv 64 (sc + -7)) with (Z_to_bv 64 (2^64 + sc - 7))
               by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z;
                   rewrite (Z.mod_small (2^64 + sc - 7)) by lia; apply (Z.mod_unique (sc + -7) (2^64) (-1)); lia).
             stepb_tk F_66b04 D_66b04 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
             tailC H10.
             rewrite !(u_Z2bv 1) by lia. unfold z8. pu_refl.
          -- repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
        * eexists. split.
          -- pfx H12 M1_seq.
             stepb_ft F_66ad8 D_66ad8 ltac:(rewrite Hs255; apply c_eq_refl).
             zero4 SOK1.
             tailA H11 SOK1 1%Z.
             addi_renorm.
             stepb_tk F_66b04 D_66b04 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
             tailC H10.
             rewrite !(u_Z2bv 1) by lia. unfold z8. pu_refl.
          -- repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
    - (* [comment removed for export] *)
      replace (seq =? 255)%Z with false by (symmetry; apply Z.eqb_neq; exact Hs255).
      assert (Es : seq' = (seq + 1)%Z) by (unfold seq'; rewrite (proj2 (Z.eqb_neq seq 255) Hs255); reflexivity). rewrite Es.
      Ltac mid Hs255 H12 :=
        stepb_tk F_66ad8 D_66ad8 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hs255);
        stepn F_66af4 D_66af4; addi_renorm.
      destruct (Sumbool.sumbool_of_bool ((7 <=? sc) && (sc <=? 38))%Z) as [Hb|Hb]; rewrite Hb.
      + assert (H7 : (7 <= sc <= 38)%Z) by (apply Bool.andb_true_iff in Hb; destruct Hb as [A B]; apply Z.leb_le in A; apply Z.leb_le in B; lia).
        eexists. split.
        * pfx H12 M1_seq. mid Hs255 H12.
          tailA H11 SOK1 (seq + 1)%Z.
          addi_renorm.
          stepb_ft F_66b04 D_66b04 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepn F_66b08 D_66b08. rewrite H18. rewrite (v_add_ZZ 700056 (sc - 7)) by lia.
          stepSTx F_66b0c D_66b0c (Z_to_bv 64 (700056 + 848 + (sc - 7))) (Z_to_bv 64 (seq + 1)) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact SOK1 | | ]; zsimp; lia).
          tailC H10.
          rewrite !(u_Z2bv (seq + 1)) by lia. pu_refl.
        * repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
      + assert (H7 : ~ (7 <= sc <= 38)%Z).
        { intros H7. apply Bool.andb_false_iff in Hb. destruct Hb as [A|A]; [apply Z.leb_gt in A | apply Z.leb_gt in A]; lia. }
        destruct (Z.lt_ge_cases sc 7) as [Hs7|Hs7].
        * eexists. split.
          -- pfx H12 M1_seq. mid Hs255 H12.
             tailA H11 SOK1 (seq + 1)%Z.
             unfold v_addi. rewrite (u_Z2bv sc) by lia.
             replace (Z_to_bv 64 (sc + -7)) with (Z_to_bv 64 (2^64 + sc - 7))
               by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z;
                   rewrite (Z.mod_small (2^64 + sc - 7)) by lia; apply (Z.mod_unique (sc + -7) (2^64) (-1)); lia).
             stepb_tk F_66b04 D_66b04 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
             tailC H10.
             rewrite !(u_Z2bv (seq + 1)) by lia. pu_refl.
          -- repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
        * eexists. split.
          -- pfx H12 M1_seq. mid Hs255 H12.
             tailA H11 SOK1 (seq + 1)%Z.
             addi_renorm.
             stepb_tk F_66b04 D_66b04 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
             tailC H10.
             rewrite !(u_Z2bv (seq + 1)) by lia. pu_refl.
          -- repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma segFGn1 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 12 = Z_to_bv 64 W -> maplen = 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66aec : word) m1 rom) (mkst regs' (0x66780 : word) m1 rom)
      /\ getr regs' 10 = Z_to_bv 64 memg /\ getr regs' 8 = Z_to_bv 64 memg /\ getr regs' 19 = Z_to_bv 64 g
      /\ getr regs' 1 = Z_to_bv 64 0x66b04 /\ keeps_but [1; 8; 10; 12; 19]%bv regs regs'.
  Proof using M1_mem HW Hg RN.
    intros regs rom H10 H12 Hml. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepn F_66a98 D_66a98. rewrite H12. rewrite v_srli_Z by lia. change (2^12)%Z with 4096%Z.
      replace (W / 4096)%Z with maplen by reflexivity. rewrite Hml.
      stepb_ft F_66a9c D_66a9c ltac:(apply c_eq_refl).
      stepLD8 F_66aa0 D_66aa0 (Z_to_bv 64 memg).
      stepn F_66aa4 D_66aa4. rewrite H10.
      stepn F_66aa8 D_66aa8.
      stepn F_66aac D_66aac.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
  Qed.
End FG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FGN2.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (g memg pm3 : Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hmemg : (HEAPLO + 16 <= memg)%Z /\ (memg + 8 <= CEIL)%Z /\ ((memg + 8 <= IMG_LO)%Z \/ (IMG_HI <= memg)%Z).
  Hypothesis Hpm3 : (0 <= pm3 < 256)%Z.
  Hypothesis M_mem : rdn RSEGS m (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 memg)).
  Hypothesis M_pm3 : rdn RSEGS m (Z_to_bv 64 (memg - 3)) 1%nat = Some [Z_to_bv 8 pm3].
  Hypothesis SOKm : store_ok RSEGS m (Z_to_bv 64 memg) 8%nat = true.

  Definition m_n2 : mem := wbytes m (Z_to_bv 64 memg) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma segFGn2 : forall regs rom,
    getr regs 19 = Z_to_bv 64 g -> getr regs 8 = Z_to_bv 64 memg ->
    exists regs', msteps RSEGS (mkst regs (0x66b04 : word) m rom) (mkst regs' (0x66890 : word) m_n2 rom)
      /\ getr regs' 11 = Z_to_bv 64 (pm3 mod 32) /\ getr regs' 1 = Z_to_bv 64 0x66b18
      /\ keeps_but [1; 11; 12]%bv regs regs'.
  Proof using SOKm M_pm3 M_mem Hpm3 Hmemg Hg RN.
    intros regs rom H19 H8. ceil; unfold HEAPLO in *. unfold m_n2.
    eexists. split.
    - stepLD8 F_66ab0 D_66ab0 (Z_to_bv 64 memg).
      stepLBU F_66ab4 D_66ab4 (Z_to_bv 8 pm3) ltac:(addr_norm; exact M_pm3).
      rewrite (u8_of_Z pm3) by lia.
      stepSTx F_66ab8 D_66ab8 (Z_to_bv 64 memg) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKm).
      stepn F_66abc D_66abc. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia.
      change (2^5)%Z with 32%Z.
      stepn F_66ac0 D_66ac0.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma segFGn3 : forall regs rom (m' : mem) base,
    getr regs 19 = Z_to_bv 64 g -> getr regs 10 = base ->
    exists regs', msteps RSEGS (mkst regs (0x66b18 : word) m' rom) (mkst regs' (0x66b74 : word) m' rom)
      /\ getr regs' 12 = base /\ getr regs' 10 = Z_to_bv 64 g /\ keeps_but [10; 12]%bv regs regs'.
  Proof using.
    intros regs rom m' base H19 H10.
    eexists. split.
    - stepn F_66ac4 D_66ac4. rewrite H10.
      stepn F_66ac8 D_66ac8. rewrite H19.
      stepn F_66acc D_66acc.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; solve_keeps_but.
  Qed.
End FGN2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FM.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp g fh ft : Z).
  Hypothesis Hsp : (CEIL + 96 <= sp + 96)%Z /\ (sp + 96 < 2^64)%Z.   (* [comment removed for export] *)
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hfh : (0 <= fh < 2^64)%Z.
  Hypothesis Hft : (0 <= ft < 2^64)%Z.
  Hypothesis SOKsp : store_ok RSEGS m (Z_to_bv 64 sp) 48%nat = true.
  Hypothesis SOKg : store_ok RSEGS m (Z_to_bv 64 g) 40%nat = true.
  Hypothesis M_fh : rdn RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fh)).

  Definition z8' := word_to_le_bytes 8 (Z_to_bv 64 0).
  (* [comment removed for export] *)
  Definition m_fz : mem :=
    wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp + 8)) z8') (Z_to_bv 64 (sp + 16)) z8') (Z_to_bv 64 (sp + 24)) z8') (Z_to_bv 64 (sp + 32)) z8') (Z_to_bv 64 (sp + 40)) z8')
      (Z_to_bv 64 (g + 8)) z8') (Z_to_bv 64 g) z8') (Z_to_bv 64 (g + 16)) z8') (Z_to_bv 64 (g + 24)) z8') (Z_to_bv 64 (g + 32)) z8'.

  Ltac fz SOKsp SOKg :=
    stepSTx F_66b20 D_66b20 (Z_to_bv 64 (sp + 8)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 48%nat); [ | exact SOKsp | | ]; zsimp; lia);
    stepSTx F_66b24 D_66b24 (Z_to_bv 64 (sp + 16)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 48%nat); [ | exact SOKsp | | ]; zsimp; lia);
    stepSTx F_66b28 D_66b28 (Z_to_bv 64 (sp + 24)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 48%nat); [ | exact SOKsp | | ]; zsimp; lia);
    stepSTx F_66b2c D_66b2c (Z_to_bv 64 (sp + 32)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 48%nat); [ | exact SOKsp | | ]; zsimp; lia);
    stepSTx F_66b30 D_66b30 (Z_to_bv 64 (sp + 40)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 48%nat); [ | exact SOKsp | | ]; zsimp; lia);
    stepLD8 F_66b34 D_66b34 (Z_to_bv 64 0);
    stepSTx F_66b38 D_66b38 (Z_to_bv 64 (g + 8)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia);
    stepLD8 F_66b3c D_66b3c (Z_to_bv 64 0);
    stepSTx F_66b40 D_66b40 (Z_to_bv 64 g) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia);
    stepLD8 F_66b44 D_66b44 (Z_to_bv 64 0);
    stepSTx F_66b48 D_66b48 (Z_to_bv 64 (g + 16)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia);
    stepLD8 F_66b4c D_66b4c (Z_to_bv 64 0);
    stepSTx F_66b50 D_66b50 (Z_to_bv 64 (g + 24)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia);
    stepLD8 F_66b54 D_66b54 (Z_to_bv 64 0);
    stepSTx F_66b58 D_66b58 (Z_to_bv 64 (g + 32)) (Z_to_bv 64 0) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia);
    stepLD8 F_66b5c D_66b5c (Z_to_bv 64 0);
    stepb_tk F_66b60 D_66b60 ltac:(apply c_eq_refl);
    stepLD8 F_66b68 D_66b68 (Z_to_bv 64 0);
    stepb_tk F_66b6c D_66b6c ltac:(apply c_eq_refl).

  (* [comment removed for export] *)
  Definition m_fe : mem :=
    wbytes (wbytes (wbytes m_fz (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 ctx_free_meta_head) (word_to_le_bytes 8 (Z_to_bv 64 g)).

  Hypothesis SOKc : store_ok RSEGS m (Z_to_bv 64 ctx_free_meta_head) 8%nat = true.

  Lemma segFMe : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 2 = Z_to_bv 64 sp -> getr regs 18 = Z_to_bv 64 CTX -> fh = 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66b74 : word) m rom) (mkst regs' (0x66c38 : word) m_fe rom)
      /\ keeps_but [13; 18]%bv regs regs'.
  Proof using SOKc M_fh SOKg SOKsp Hg Hsp RN.
    intros regs rom H10 H2 H18 Hfh0. ceil; unfold HEAPLO, ctx_free_meta_head, CTX in *. unfold m_fe, m_fz, z8', ctx_free_meta_head, CTX.
    eexists. split.
    - fz SOKsp SOKg.
      stepLD F_66b74 D_66b74 (word_to_le_bytes 8 (Z_to_bv 64 fh)) (Z_to_bv 64 fh)
        ltac:(addr_norm; repeat rdn_peel1; exact M_fh) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_66b78 D_66b78 ltac:(rewrite Hfh0; apply c_eq_refl).
      stepSTx F_66b98 D_66b98 (Z_to_bv 64 g) (Z_to_bv 64 g) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepSTx F_66b9c D_66b9c (Z_to_bv 64 (g + 8)) (Z_to_bv 64 g) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepn F_66ba0 D_66ba0. rewrite H18. addi_renorm.
      stepSTx F_66ba4 D_66ba4 (Z_to_bv 64 (700056 + 16)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKc).
      stepn F_66ba8 D_66ba8.
      pu_refl.
    - solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Definition m_fq : mem :=
    wbytes (wbytes (wbytes (wbytes m_fz (Z_to_bv 64 (g + 8)) (word_to_le_bytes 8 (Z_to_bv 64 fh)))
      (Z_to_bv 64 g) (word_to_le_bytes 8 (Z_to_bv 64 ft)))
      (Z_to_bv 64 (ft + 8)) (word_to_le_bytes 8 (Z_to_bv 64 g)))
      (Z_to_bv 64 fh) (word_to_le_bytes 8 (Z_to_bv 64 g)).

  Lemma segFMq : forall regs rom,
    (HEAPLO <= fh)%Z -> (fh + 40 <= CEIL)%Z -> (HEAPLO <= ft)%Z -> (ft + 40 <= CEIL)%Z ->
    (g + 40 <= fh \/ fh + 40 <= g)%Z -> (g + 40 <= ft \/ ft + 40 <= g)%Z ->
    rdn RSEGS m (Z_to_bv 64 fh) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ft)) ->
    store_ok RSEGS m (Z_to_bv 64 fh) 8%nat = true -> store_ok RSEGS m (Z_to_bv 64 (ft + 8)) 8%nat = true ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 2 = Z_to_bv 64 sp -> getr regs 18 = Z_to_bv 64 CTX -> fh <> 0%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66b74 : word) m rom) (mkst regs' (0x66c38 : word) m_fq rom)
      /\ keeps_but [13; 18]%bv regs regs'.
  Proof using M_fh SOKg SOKsp Hft Hfh Hg Hsp.
    intros regs rom Hh1 Hh2 Ht1 Ht2 Dgh Dgt M_ft SOKh SOKt H10 H2 H18 Hnz.
    ceil; unfold HEAPLO, ctx_free_meta_head, CTX in *. unfold m_fq, m_fz, z8', ctx_free_meta_head, CTX.
    eexists. split.
    - fz SOKsp SOKg.
      stepLD F_66b74 D_66b74 (word_to_le_bytes 8 (Z_to_bv 64 fh)) (Z_to_bv 64 fh)
        ltac:(addr_norm; repeat rdn_peel1; exact M_fh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_66b78 D_66b78 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; exact Hnz).
      stepSTx F_66b7c D_66b7c (Z_to_bv 64 (g + 8)) (Z_to_bv 64 fh) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepLD8 F_66b80 D_66b80 (Z_to_bv 64 ft).
      stepSTx F_66b84 D_66b84 (Z_to_bv 64 g) (Z_to_bv 64 ft) ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia).
      stepSTx F_66b88 D_66b88 (Z_to_bv 64 (ft + 8)) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKt).
      stepLD8 F_66b8c D_66b8c (Z_to_bv 64 fh).
      stepSTx F_66b90 D_66b90 (Z_to_bv 64 fh) (Z_to_bv 64 g) ltac:(store_ok_peel; exact SOKh).
      stepn F_66b94 D_66b94.
      pu_refl.
    - solve_keeps_but.
  Qed.
End FM.
End UbMhNtfD.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhJunk OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhSub.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhJunk OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record fsub (st st' : mst) : Prop := FSUB {
  fs_grp : forall x, is_group st' x -> is_group st x;
  fs_kind : forall x, is_group st' x -> s_kind st' x = s_kind st x;
  fs_W : forall x, is_group st' x -> g_W st' x = g_W st x;
  fs_mem : forall x, is_group st' x -> mr_mem (s_meta st' x) = mr_mem (s_meta st x) }.

Lemma fsub_refl : forall st, fsub st st.
Proof. intros st. constructor; intros; auto. Qed.

Lemma fsub_trans : forall st1 st2 st3, fsub st1 st2 -> fsub st2 st3 -> fsub st1 st3.
Proof.
  intros st1 st2 st3 A B. constructor; intros x Hx.
  - apply (fs_grp _ _ A), (fs_grp _ _ B), Hx.
  - rewrite (fs_kind _ _ B x Hx). apply (fs_kind _ _ A), (fs_grp _ _ B), Hx.
  - rewrite (fs_W _ _ B x Hx). apply (fs_W _ _ A), (fs_grp _ _ B), Hx.
  - rewrite (fs_mem _ _ B x Hx). apply (fs_mem _ _ A), (fs_grp _ _ B), Hx.
Qed.

(* [comment removed for export] *)
Lemma fsub_same : forall st st', s_groups st' = s_groups st -> s_kind st' = s_kind st -> s_meta st' = s_meta st -> fsub st st'.
Proof.
  intros st st' G K Mt. constructor; intros x Hx.
  - unfold is_group in *. rewrite G in Hx. exact Hx.
  - rewrite K. reflexivity.
  - unfold g_W. rewrite Mt. reflexivity.
  - rewrite Mt. reflexivity.
Qed.

Lemma fsub_setbit : forall st m i, fsub st (UbMhSetBit.st' st m i).
Proof.
  intros st m i. constructor; intros x Hx.
  - unfold is_group in *. rewrite UbMhSetBit.e_groups in Hx. exact Hx.
  - rewrite UbMhSetBit.e_kind. reflexivity.
  - apply UbMhSetBit.e_gW.
  - apply UbMhSetBit.e_mem.
Qed.

Lemma fsub_queue : forall st m sc, fsub st (UbMhQueue.st' st m sc).
Proof.
  intros st m sc. constructor; intros x Hx.
  - unfold is_group in *. rewrite UbMhQueue.e_groups in Hx. exact Hx.
  - rewrite UbMhQueue.e_kind. reflexivity.
  - unfold g_W. apply UbMhQueue.e_Wr.
  - apply UbMhQueue.e_mem.
Qed.

Lemma fsub_dissolve : forall st g, fsub st (UbMhDissolve.st' st g).
Proof.
  intros st g. constructor; intros x Hx.
  - apply (proj1 (proj1 (UbMhDissolve.e_is_group st g x) Hx)).
  - rewrite UbMhDissolve.e_kind. reflexivity.
  - unfold g_W. apply UbMhDissolve.e_Wr.
  - apply UbMhDissolve.e_mem.
Qed.

Lemma fsub_activate : forall st h, fsub st (UbMhActivate.st' st h).
Proof.
  intros st h. constructor; intros x Hx.
  - apply (proj1 (UbMhActivate.e_is_group st h x) Hx).
  - rewrite UbMhActivate.e_kind. reflexivity.
  - unfold g_W. apply UbMhActivate.e_Wr.
  - apply UbMhActivate.e_mem.
Qed.

Lemma fsub_freemeta : forall st m, ~ is_group st m -> fsub st (UbMhFreeMeta.st' st m).
Proof.
  intros st m NG.
  assert (NE : forall x, is_group (UbMhFreeMeta.st' st m) x -> is_group st x /\ x <> m).
  { intros x Hx. apply (proj1 (UbMhFreeMeta.e_is_group st m x)) in Hx. split; [exact Hx | intros ->; exact (NG Hx)]. }
  constructor; intros x Hx; destruct (NE x Hx) as [Gx Nx].
  - exact Gx.
  - rewrite UbMhFreeMeta.e_kind. reflexivity.
  - unfold g_W. apply UbMhFreeMeta.e_Wr. exact Nx.
  - apply UbMhFreeMeta.e_mem. exact Nx.
Qed.

Lemma fsub_policy : forall st u q b sq, fsub st (UbMhPolicy.st' st u q b sq).
Proof. intros. apply fsub_same; reflexivity. Qed.

Lemma fsub_junk : forall st m i off, fsub st (UbMhJunk.st' st m i off).
Proof. intros. apply fsub_same; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Lone.
  Context {RN : mh_run}.

  (* [comment removed for export] *)
  Lemma fsub_glast : forall st st' x, fsub st st' -> is_group st' x -> g_lastidx st' x = g_lastidx st x.
  Proof. intros st st' x F Hx. unfold g_lastidx. rewrite (fs_W _ _ F x Hx). reflexivity. Qed.
  Lemma fsub_gsc : forall st st' x, fsub st st' -> is_group st' x -> g_sc st' x = g_sc st x.
  Proof. intros st st' x F Hx. unfold g_sc. rewrite (fs_W _ _ F x Hx). reflexivity. Qed.
  Lemma fsub_gml : forall st st' x, fsub st st' -> is_group st' x -> g_maplen st' x = g_maplen st x.
  Proof. intros st st' x F Hx. unfold g_maplen. rewrite (fs_W _ _ F x Hx). reflexivity. Qed.
  Lemma fsub_gstride : forall st st' x, fsub st st' -> is_group st' x -> g_stride st' x = g_stride st x.
  Proof.
    intros st st' x F Hx. unfold g_stride.
    rewrite (fsub_gml st st' x F Hx), (fsub_glast st st' x F Hx), (fsub_gsc st st' x F Hx). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma lone_fsub : forall st st' L L' g,
    WF st L -> WF st' L' -> nojunk st' -> fsub st st' -> is_group st' g -> lone st g -> lone st' g.
  Proof.
    intros st st' L L' g W W' NJ F Hg LO.
    pose proof LO as (L0 & K0 & ML & SC & p & n & off & res & S0).
    pose proof (fs_grp _ _ F g Hg) as Hg0.
    pose proof (wG_each st' L' (WF_groups st' L' W') g Hg) as WG'.
    assert (EL : g_lastidx st' g = 0) by (rewrite (fsub_glast st st' g F Hg); exact L0).
    assert (ES : g_sc st' g = g_sc st g) by exact (fsub_gsc st st' g F Hg).
    assert (EM : g_maplen st' g = g_maplen st g) by exact (fsub_gml st st' g F Hg).
    assert (ET : g_stride st' g = g_stride st g) by exact (fsub_gstride st st' g F Hg).
    split; [exact EL|]. split; [rewrite (fs_kind _ _ F g Hg); exact K0|]. split; [rewrite EM; exact ML|].
    split; [rewrite ES, ET; exact SC|].
    (* [comment removed for export] *)
    assert (NF : s_slot st' g 0 <> SAvail /\ s_slot st' g 0 <> SFreed).
    { assert (CASE : forall s, s = s_slot st' g 0 -> (s = SAvail \/ s = SFreed) \/ (s <> SAvail /\ s <> SFreed)).
      { intros s _. destruct s; [left; left; reflexivity | left; right; reflexivity | right; split; discriminate ..]. }
      destruct (CASE _ eq_refl) as [FR|OK]; [exfalso | exact OK].
      assert (ALL : forall k, 0 <= k <= g_lastidx st' g -> s_slot st' g k = SAvail \/ s_slot st' g k = SFreed).
      { intros k Hk. rewrite EL in Hk. replace k with 0 by lia. exact FR. }
      destruct (wg_fullfree st' L' g WG' ALL) as (_ & S48 & _).
      destruct SC as [S|S]; [rewrite <- ES in S; lia|].
      rewrite <- ES, <- ET in S.
      destruct (wg_fit st' L' g WG' S48 S 0 ltac:(rewrite EL; lia)) as [A B].
      destruct FR as [E|E]; [exact (A E) | exact (B E)]. }
    destruct NF as [NA NFR].
    pose proof (wg_slots st' L' g WG' 0 ltac:(rewrite EL; lia)) as SW.
    destruct (s_slot st' g 0) as [| |q k o r|h o|o] eqn:E0.
    - exfalso; exact (NA eq_refl).
    - exfalso; exact (NFR eq_refl).
    - exists q, k, o, r. reflexivity.
    - exfalso. cbn [slot_wf] in SW. destruct SW as (_ & Gh & _ & Kh & _).
      pose proof (fs_grp _ _ F h Gh) as Gh0. rewrite (fs_kind _ _ F h Gh) in Kh.
      pose proof (wg_kind st L h (wG_each st L (WF_groups st L W) h Gh0)) as KD. rewrite Kh in KD.
      destruct KD as (_ & _ & _ & _ & _ & SH & _). rewrite S0 in SH. discriminate SH.
    - exfalso. exact (NJ g 0 o Hg ltac:(rewrite EL; lia) E0).
  Qed.

  (* [comment removed for export] *)
  Lemma lone_all_fsub : forall st st' L L',
    WF st L -> WF st' L' -> nojunk st' -> fsub st st' ->
    (forall g, is_group st g -> lone st g) -> (forall g, is_group st' g -> lone st' g).
  Proof.
    intros st st' L L' W W' NJ F LO g Hg.
    exact (lone_fsub st st' L L' g W W' NJ F Hg (LO g (fs_grp _ _ F g Hg))).
  Qed.
End Lone.
End UbMhSub.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhSetBit OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhActivate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib UbMhNtfA UbMhNtfB UbMhNtfC UbMhNtfD UbMhSub.
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
Ltac keep_only_disj H := repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H H' then fail else clear H' end.
Ltac with_disj1 tac := match goal with H : _ \/ _ |- _ => solve [ keep_only_disj H; tac ] end.
Ltac lia_fast ::= first [ solve [ clear_disj; rnfix; zlia ] | solve [ with_disj1 ltac:(rnfix; zlia) ] | lia ].
(* [comment removed for export] *)
Tactic Notation "rpeel" "-" ne_hyp_list(Hs) := rewrite rdn_wbytes_out_Z by (zlen; clear - Hs; zlia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; rnfix; zlia ] | solve [ with_disj1 ltac:(rnfix; zlia) ] | lia ] ].
Definition NTF_CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Definition app_of (L : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) L /\ p <= a < p + n.
Definition FR `{RN : mh_run} (L : list (Z * Z)) (lo hi : Z) (M M' : mem) : Prop :=
  mem_grows M M' /\
  forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
    (lo <= a < hi) \/ (HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a) \/ (CTX <= a < CTX_END).

Lemma FR_refl `{RN : mh_run} : forall L lo hi M, FR L lo hi M M.
Proof. intros. split; [apply mem_grows_refl | intros a _ H; exfalso; exact (H eq_refl)]. Qed.

Lemma FR_trans `{RN : mh_run} : forall L lo hi M1 M2 M3, FR L lo hi M1 M2 -> FR L lo hi M2 M3 -> FR L lo hi M1 M3.
Proof.
  intros L lo hi M1 M2 M3 [G1 W1] [G2 W2]. split; [eapply mem_grows_trans; eassumption|].
  intros a Hr NE. destruct (decide (M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E|NE2].
  - apply W1; [exact Hr | congruence].
  - apply W2; [exact Hr | exact NE2].
Qed.

Lemma FR_widen `{RN : mh_run} : forall L lo hi lo' hi' M M', lo' <= lo -> hi <= hi' -> FR L lo hi M M' -> FR L lo' hi' M M'.
Proof.
  intros L lo hi lo' hi' M M' H1 H2 [G W]. split; [exact G|]. intros a Hr NE.
  destruct (W a Hr NE) as [A|[A|A]]; [left; lia | right; left; exact A | right; right; exact A].
Qed.


(* [comment removed for export] *)
Definition only_junk (st : mst) (m i : Z) : Prop :=
  forall x k o, is_group st x -> 0 <= k <= g_lastidx st x -> s_slot st x k = SJunk o -> x = m /\ k = i.

(* [comment removed for export] *)
Definition ntf_ret (st st' : mst) (regs' : bvmap 5 word) : Prop :=
     (getr regs' 11 = Z_to_bv 64 0 /\ s_regions st' = s_regions st)
  \/ (exists b len x, Permutation (s_regions st) (RG b len (RGroup x) :: s_regions st') /\
        getr regs' 10 = Z_to_bv 64 b /\ getr regs' 11 = Z_to_bv 64 len /\ 0 < len).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MemHelp0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma wbytes_diff_g : forall (Mx : mem) (b : Z) bs a, 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
    wbytes Mx (Z_to_bv 64 b) bs (Z_to_bv 64 a) <> Mx (Z_to_bv 64 a) -> b <= a < b + Z.of_nat (length bs).
  Proof using.
    intros Mx b bs a Hb Hbl Ha NE.
    destruct (Z.lt_ge_cases a b) as [A|A].
    - exfalso. apply NE. apply wbytes_below; rewrite !u_Z2bv by lia; lia.
    - destruct (Z.lt_ge_cases a (b + Z.of_nat (length bs))) as [B|B]; [lia|].
      exfalso. apply NE. apply wbytes_above. rewrite !u_Z2bv by lia. lia.
  Qed.
End MemHelp0.

Ltac wdiff NE Mbase a :=
  repeat match type of NE with wbytes ?Mb (Z_to_bv 64 ?b) _ _ <> _ =>
    destruct (decide (Mb (Z_to_bv 64 a) = Mbase (Z_to_bv 64 a))) as [?E2|?NE2];
    [ (rewrite <- E2 in NE || idtac); apply wbytes_diff_g in NE;
      [ rewrite length_N_to_le_bytes in NE; cbn in NE; lia | lia | rewrite length_N_to_le_bytes; cbn; lia | assumption ]
    | clear NE; rename NE2 into NE ] end;
  exfalso; exact (NE eq_refl).

Section MemHelp.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Lemma wbytes_same_inside : forall bs (Ma Mb : mem) (addr x : word),
    bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64 ->
    bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + Z.of_nat (length bs) ->
    wbytes Ma addr bs x = wbytes Mb addr bs x.
  Proof using.
    induction bs as [|b rest IH]; intros Ma Mb addr x Hnw Hx; cbn [wbytes length] in *; [lia|].
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned addr)) as [E|Hne].
    - assert (Ex : x = addr) by (apply bv_eq; exact E). subst x.
      destruct rest as [|b' rest'].
      + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
      + assert (Hu1 : bv_unsigned (addr + 1)%bv = bv_unsigned addr + 1) by (apply u_add1; cbn [length] in Hnw; lia).
        rewrite !wbytes_below by (cbn [length] in *; lia). cbv beta. rewrite bv_eqb_refl. reflexivity.
    - destruct rest as [|b' rest']; [cbn [length] in Hx; lia|].
      assert (Hu1 : bv_unsigned (addr + 1)%bv = bv_unsigned addr + 1) by (apply u_add1; cbn [length] in Hnw; lia).
      apply IH; cbn [length] in *; lia.
  Qed.


  Lemma m_q_writes : forall (Mx : mem) g hd tl a,
    0 <= g -> g + 40 < 2 ^ 64 -> 0 <= hd -> hd + 40 < 2 ^ 64 -> 0 <= tl -> tl + 40 < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
    m_q Mx g hd tl (Z_to_bv 64 a) <> Mx (Z_to_bv 64 a) ->
    (g <= a < g + 16) \/ (tl + 8 <= a < tl + 16) \/ (hd <= a < hd + 8).
  Proof using. intros Mx g hd tl a Hg Hg2 Hh Hh2 Ht Ht2 Ha NE. unfold m_q in NE. wdiff NE Mx a. Qed.

  Lemma m_e_writes : forall (Mx : mem) g sc a,
    0 <= g -> g + 40 < 2 ^ 64 -> 0 <= sc < 64 -> 0 <= a < 2 ^ 64 ->
    m_e Mx g sc (Z_to_bv 64 a) <> Mx (Z_to_bv 64 a) ->
    (g <= a < g + 16) \/ (ctx_active sc <= a < ctx_active sc + 8).
  Proof using. intros Mx g sc a Hg Hg2 Hsc Ha NE. unfold m_e, ctx_active, CTX in *. wdiff NE Mx a. Qed.

  (* [comment removed for export] *)
  Lemma FR_rdn_keep : forall L lo hi Ma Mb a n bs,
    FR L lo hi Ma Mb -> CEIL <= a -> a + Z.of_nat n < 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
    rdn RSEGS Ma (Z_to_bv 64 a) n = Some bs -> rdn RSEGS Mb (Z_to_bv 64 a) n = Some bs.
  Proof using.
    intros L lo hi Ma Mb a n bs [G W] Hc Hnw Hout R. rewrite <- R. symmetry.
    apply rdn_ext; [rewrite u_Z2bv by (ceil; lia); lia|].
    intros x Hx. rewrite u_Z2bv in Hx by (ceil; lia).
    destruct (decide (Mb x = Ma x)) as [E|NE]; [symmetry; exact E|]. exfalso.
    pose proof (bv_unsigned_in_range _ x) as XR.
    assert (Ex : x = Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u_Z2bv by (cbn in XR; lia); reflexivity).
    rewrite Ex in NE. destruct (W (bv_unsigned x) ltac:(cbn in XR; lia) NE) as [A|[A|A]]; ceil; unfold HEAPLO, CTX_END, CTX in *; lia.
  Qed.
End MemHelp.



Section Asm.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Lemma lor_clear_bit : forall fr i, 0 <= fr -> 0 <= i -> Z.testbit fr i = false -> Z.lor fr (2 ^ i) = fr + 2 ^ i.
  Proof using.
    intros fr i Hf Hi Hb.
    assert (Hl : Z.land fr (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit fr i Hf Hi)); exact Hb).
    rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Head.
    Variables (st : mst) (L : list (Z * Z)) (M : mem) (m i off : Z) (sp : Z).
    Hypothesis HWF : WF st L.
    Hypothesis HREP : REP st M.
    Hypothesis Hgrp : is_group st m.
    Hypothesis Hi : 0 <= i <= g_lastidx st m.
    Hypothesis Hslot : s_slot st m i = SJunk off.
    Hypothesis Hsp : CEIL + 96 <= sp /\ sp < 2 ^ 64 /\ sp mod 16 = 0.
    Hypothesis SOK : store_ok RSEGS M (Z_to_bv 64 (sp - 96)) 96%nat = true.

    #[local] Notation W := (g_W st m).
    #[local] Notation av := (mr_avail (s_meta st m)).
    #[local] Notation fr := (mr_freed (s_meta st m)).
    #[local] Notation nxt := (mr_next (s_meta st m)).
    #[local] Notation sc := (g_sc st m).
    #[local] Notation mask := (Z.lor av fr).
    #[local] Notation self := (2 ^ i).
    #[local] Notation all := (2 * 2 ^ g_lastidx st m - 1).
    #[local] Notation cx := (s_ctx st).

    Definition M1 (regs : bvmap 5 word) : mem :=
      ntf_frame M sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (Z_to_bv 64 (s_canary st)).

    Lemma hd_wfg : wf_group st L m. Proof using Hgrp HWF RN. exact (wG_each st L (WF_groups st L HWF) m Hgrp). Qed.
    Lemma hd_masks : 0 <= av < 2 ^ 32 /\ 0 <= fr < 2 ^ 32 /\ Z.testbit av i = false /\ Z.testbit fr i = false /\
                     Z.testbit mask i = false.
    Proof using Hslot Hi Hgrp HWF sp off L RN.
      pose proof hd_wfg as WG. pose proof (wg_avr st L m WG) as A. pose proof (wg_frr st L m WG) as F.
      assert (Ta : Z.testbit av i = false).
      { destruct (Z.testbit av i) eqn:E; [|reflexivity]. exfalso.
        apply (proj1 (wg_av st L m WG i ltac:(lia))) in E. destruct E as [_ E]. rewrite Hslot in E. discriminate E. }
      assert (Tf : Z.testbit fr i = false).
      { destruct (Z.testbit fr i) eqn:E; [|reflexivity]. exfalso.
        apply (proj1 (wg_fr st L m WG i ltac:(lia))) in E. destruct E as [_ E]. rewrite Hslot in E. discriminate E. }
      repeat split; try lia; try assumption. rewrite Z.lor_spec, Ta, Tf. reflexivity.
    Qed.

    Lemma wbytes_diff : forall (Mx : mem) (b : Z) bs a, 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
      wbytes Mx (Z_to_bv 64 b) bs (Z_to_bv 64 a) <> Mx (Z_to_bv 64 a) -> b <= a < b + Z.of_nat (length bs).
    Proof using sp.
      intros Mx b bs a Hb Hbl Ha NE.
      destruct (Z.lt_ge_cases a b) as [A|A].
      - exfalso. apply NE. apply wbytes_below; rewrite !u_Z2bv by lia; lia.
      - destruct (Z.lt_ge_cases a (b + Z.of_nat (length bs))) as [B|B]; [lia|].
        exfalso. apply NE. apply wbytes_above. rewrite !u_Z2bv by lia. lia.
    Qed.

    Lemma M1_writes : forall regs a, 0 <= a < 2 ^ 64 -> M1 regs (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sp - 48 <= a < sp.
    Proof using Hsp RN.
      intros regs a Ha NE. unfold M1, ntf_frame in NE. destruct Hsp as (S1 & S2 & S3). ceil.
      repeat match type of NE with
      | wbytes ?Mx (Z_to_bv 64 ?b) ?bs _ <> _ =>
          destruct (decide (wbytes Mx (Z_to_bv 64 b) bs (Z_to_bv 64 a) = Mx (Z_to_bv 64 a))) as [E|NE'];
          [rewrite E in NE; clear E
          | apply wbytes_diff in NE'; [rewrite length_N_to_le_bytes in NE'; cbn in NE'; lia | lia | rewrite length_N_to_le_bytes; cbn; lia | lia] ]
      end.
      exfalso. exact (NE eq_refl).
    Qed.

    Lemma M1_FR : forall regs, FR L (sp - 48) sp M (M1 regs).
    Proof using Hsp.
      intros regs. split; [unfold M1, ntf_frame; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|].
      intros a Hr NE. left. exact (M1_writes regs a Hr NE).
    Qed.

    Lemma M1_REP : forall regs, REP st (M1 regs).
    Proof using Hsp HREP HWF L RN.
      intros regs. destruct (M1_FR regs) as [G _]. apply (REP_frame st L M HWF HREP (M1 regs) G).
      intros a Hr NE. left. pose proof (M1_writes regs a Hr NE). destruct Hsp as (S1 & _). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma keeps_join : forall c1 c2 r0 r1 r2, keeps_but c1 r0 r1 -> keeps_but c2 r1 r2 -> keeps_but (c1 ++ c2) r0 r2.
    Proof using.
      intros c1 c2 r0 r1 r2 K1 K2. eapply keeps_but_trans.
      - eapply keeps_but_mono; [exact K1 | intros r Hr; apply in_or_app; left; exact Hr].
      - eapply keeps_but_mono; [exact K2 | intros r Hr; apply in_or_app; right; exact Hr].
    Qed.

    Lemma hd_rng : HEAPLO + 24 <= m /\ m + 40 <= CEIL /\ m mod 8 = 0.
    Proof using Hgrp HWF L st. exact (metaU_rng st L HWF m (group_metaU st L HWF m Hgrp)). Qed.
    Lemma hd_last : 0 <= g_lastidx st m < 32. Proof using. exact (glast_rng st m). Qed.
    Lemma hd_sc : 0 <= sc < 64. Proof using sp. unfold g_sc, w_sizeclass. apply Z.mod_pos_bound. lia. Qed.

    (* [comment removed for export] *)
    Lemma hd_listed_dec : {In m (s_alist st sc)} + {~ listed st m}.
    Proof using Hgrp HWF L RN.
      destruct (in_dec Z.eq_dec m (s_alist st sc)) as [I|NI]; [left; exact I | right].
      intros [F|A]; [exact (wg_notfree st L m hd_wfg F) | exact (NI (wg_listed_sc st L m hd_wfg A))].
    Qed.
    Lemma hd_next : 0 <= nxt < 2 ^ 64 /\ (nxt <> 0 -> In m (s_alist st sc) /\ In nxt (s_alist st sc) /\ 0 <= sc < 48).
    Proof using Hsp Hi Hgrp HWF sp i L RN.
      destruct hd_listed_dec as [I|NL].
      - destruct (alist_member st L HWF sc m I) as (S48 & _).
        pose proof (wl_adll st (WF_lists st L HWF) sc S48) as D.
        destruct (dllf_links_In _ _ _ m (proj1 (dll_dllf st _) D) I) as [In1 _].
        destruct (alist_member st L HWF sc nxt In1) as (_ & Gn & _ & Un & _).
        destruct (metaU_rng st L HWF nxt Un) as (A & B & _). ceil; unfold HEAPLO in *. split; [lia | intros _; tauto].
      - destruct (wl_link st (WF_lists st L HWF) m (group_metaU st L HWF m Hgrp) NL) as [N0 _]. rewrite N0.
        split; [lia | intros H; exfalso; exact (H eq_refl)].
    Qed.

    Definition head_post (r1 : bvmap 5 word) (pc1 : word) : Prop :=
         (pc1 = (0x669ec%bv : word) /\ (mask + self <> all \/ (sc < 48 /\ g_maplen st m <> 0 /\ nxt = m /\ 7 <= sc <= 38 /\ 100 <= c_bounces cx (sc - 7) /\ ~ (g_lastidx st m = 0 /\ g_maplen st m * 4096 - 16 < 16 * size_class sc))))
      \/ (pc1 = (0x669a4%bv : word) /\ mask + self = all /\ getr r1 18 = Z_to_bv 64 CTX).

    Lemma ntf_head : forall regs rom,
      getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 i -> getr regs 2 = Z_to_bv 64 sp ->
      exists r1 (pc1 : word),
        msteps RSEGS (mkst regs (0x66890%bv : word) M rom) (mkst r1 pc1 (M1 regs) rom) /\
        getr r1 10 = Z_to_bv 64 m /\ getr r1 11 = s32 self /\ getr r1 12 = Z_to_bv 64 sc /\ getr r1 13 = s32 mask /\
        getr r1 2 = Z_to_bv 64 (sp - 96) /\ getr r1 9 = Z_to_bv 64 A_CANARY /\
        keeps_but (clobN0 ++ clobD) regs r1 /\ head_post r1 pc1.
    Proof using SOK Hsp Hslot Hi Hgrp HREP HWF off L RN.
      intros regs rom H10 H11 H2.
      pose proof hd_wfg as WG. destruct hd_masks as (AV & FRr & Ta & Tf & Tm). pose proof hd_rng as (R1 & R2 & R8).
      pose proof hd_last as HL. pose proof hd_sc as HS. pose proof (wg_Wr st L m WG) as WR.
      pose proof (wc_canary st (WF_ctx st L HWF)) as CAN.
      destruct (G_meta_cells st L M HWF HREP m Hgrp) as (ar & k & Har & Hk & Em & Ear & _ & _ & _ & RM & CK & DF).
      destruct RM as [Rp Rn Rme Rav Rfr RW].
      pose proof (rc_got st M (rp_statics st M HREP)) as GOT. pose proof (rc_canary st M (rp_statics st M HREP)) as CANc.
      (* [comment removed for export] *)
      destruct (segN0 M sp m i W av fr (s_canary st) Hsp ltac:(lia) ltac:(lia) WR AV FRr SOK RW Rav Rfr GOT CANc regs rom H10 H11 H2)
        as (r0 & RUN0 & A2 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & K0).
      (* [comment removed for export] *)
      pose proof (M1_REP regs) as HREP1. fold (M1 regs) in RUN0.
      destruct (G_meta_cells st L (M1 regs) HWF HREP1 m Hgrp) as (ar1 & k1 & _ & _ & _ & _ & _ & _ & _ & RM1 & _ & _).
      destruct RM1 as [Rp1 Rn1 Rme1 Rav1 Rfr1 RW1].
      assert (DR : dregs m W av fr i r0) by (split; [exact A10|]; split; [exact A11|]; split; [exact A12 | exact A13]).
      destruct (Z.eq_dec (mask + self) all) as [Hall|Hnall].
      - (* [comment removed for export] *)
        destruct (segD_pfx (M1 regs) m W av fr i WR (wg_freeable st L m WG) Hi AV FRr Tm r0 rom DR A15 A16 Hall)
          as (r2 & RUN2 & DR2 & B14 & B15 & B18 & K2).
        destruct hd_next as [NX _].
        pose proof (wc_bnc st (WF_ctx st L HWF) (sc - 7)) as BN. pose proof (wc_usage st (WF_ctx st L HWF) sc) as US.
        assert (M_bnc : 7 <= sc <= 38 -> rdn RSEGS (M1 regs) (Z_to_bv 64 (ctx_bounces (sc - 7))) 1%nat = Some [Z_to_bv 8 (c_bounces cx (sc - 7))]).
        { intros H7. apply (cell1_rdn (M1 regs)); [exact BN|]. apply (rc_bnc st (M1 regs) (rp_ctx st (M1 regs) HREP1)). lia. }
        assert (M_usage : sc < 48 -> rdn RSEGS (M1 regs) (Z_to_bv 64 (ctx_usage sc)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (c_usage cx sc)))).
        { intros H48. apply (rc_usage st (M1 regs) (rp_ctx st (M1 regs) HREP1)). lia. }
        destruct (segD_tree (M1 regs) m W av fr i nxt (c_bounces cx (sc - 7)) (c_usage cx sc) ltac:(lia) WR Hi AV FRr
                    NX BN US Rn1 M_bnc M_usage (sz_img_of_REP st (M1 regs) HREP1) r2 rom DR2 B14 B15 B18)
          as (r3 & pc3 & RUN3 & DP & DR3 & C18 & K3).
        exists r3, pc3. destruct DR3 as (C10 & C11 & C12 & C13).
        split; [eapply msteps_trans; [exact RUN0 | eapply msteps_trans; [exact RUN2 | exact RUN3]]|].
        assert (K : keeps_but (clobN0 ++ clobD) regs r3).
        { eapply keeps_join; [exact K0|]. eapply keeps_but_trans; [exact K2 | exact K3]. }
        repeat (split; [first [assumption | kept_rw K3; kept_rw K2; assumption]|]).
        destruct DP as [[E OK]|(E & S48 & ML & NG & S7 & BNC & NST)].
        + right. split; [exact E|]. split; [exact Hall | exact C18].
        + left. split; [exact E|]. right. split; [exact S48|]. split; [unfold g_maplen; exact ML|]. split; [exact NG|]. split; [exact S7|]. split; [exact BNC|].
          unfold g_lastidx, g_maplen. exact NST.
      - destruct (segD_ne (M1 regs) m W av fr i WR (wg_freeable st L m WG) Hi AV FRr Tm r0 rom DR A15 A16 Hnall)
          as (r2 & RUN2 & DR2 & K2).
        exists r2, (0x669ec%bv : word). destruct DR2 as (C10 & C11 & C12 & C13).
        split; [eapply msteps_trans; [exact RUN0 | exact RUN2]|].
        assert (K : keeps_but (clobN0 ++ clobD) regs r2) by (eapply keeps_join; [exact K0 | exact K2]).
        repeat (split; [first [assumption | kept_rw K2; assumption]|]).
        left. split; [reflexivity|]. left. exact Hnall.
    Qed.

    (* [comment removed for export] *)
    Lemma M1_saved : forall regs,
      rdn RSEGS (M1 regs) (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn RSEGS (M1 regs) (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn RSEGS (M1 regs) (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn RSEGS (M1 regs) (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn RSEGS (M1 regs) (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn RSEGS (M1 regs) (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (s_canary st))).
    Proof using Hsp RN.
      intros regs. destruct Hsp as (S1 & S2 & S3). ceil. unfold M1, ntf_frame.
      repeat split; rdn_solve.
    Qed.

    (* [comment removed for export] *)
    Definition bs_or : list byte := word_to_le_bytes 4 (s32 (Z.lor fr (2 ^ i))).
    Lemma bs_or_val : bs_or = word_to_le_bytes 4 (Z_to_bv 64 (fr + 2 ^ i)).
    Proof using Hslot Hi Hgrp HWF sp off L RN.
      unfold bs_or. destruct hd_masks as (AV & FRr & Ta & Tf & _). pose proof hd_last.
      rewrite lor_clear_bit by (lia || exact Tf). rewrite w2le4_s32.
      pose proof (add_pow2_nocarry32 fr i ltac:(lia) ltac:(lia) Tf). assert (0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.mod_small by lia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma keeps_final : forall regs r' big,
      keeps_but big regs r' ->
      (forall r, In r big -> In r NTF_CLOB \/ In r [1; 2; 8; 9; 18; 19]%bv) ->
      getr r' 1 = getr regs 1 -> getr r' 2 = getr regs 2 -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
      getr r' 18 = getr regs 18 -> getr r' 19 = getr regs 19 ->
      keeps_but NTF_CLOB regs r'.
    Proof using.
      intros regs r' big K Hbig E1 E2 E8 E9 E18 E19 r Hr.
      destruct (in_dec (fun x y : reg => bv_eq_dec _ x y) r big) as [I|NI]; [|exact (K r NI)].
      destruct (Hbig r I) as [C|C]; [exfalso; exact (Hr C)|].
      destruct C as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma ntf_nofree : forall regs rom r1,
      ret_ok (getr regs 1) ->
      getr regs 2 = Z_to_bv 64 sp ->
      getr r1 10 = Z_to_bv 64 m -> getr r1 11 = s32 self -> getr r1 12 = Z_to_bv 64 sc -> getr r1 13 = s32 mask ->
      getr r1 2 = Z_to_bv 64 (sp - 96) -> getr r1 9 = Z_to_bv 64 A_CANARY ->
      keeps_but (clobN0 ++ clobD) regs r1 ->
      (mask + self <> all \/ (sc < 48 /\ g_maplen st m <> 0 /\ nxt = m /\ 7 <= sc <= 38 /\ 100 <= c_bounces cx (sc - 7) /\ ~ (g_lastidx st m = 0 /\ g_maplen st m * 4096 - 16 < 16 * size_class sc))) ->
      only_junk st m i ->
      exists st' M' r',
        msteps RSEGS (mkst r1 (0x669ec%bv : word) (M1 regs) rom) (mkst r' (getr regs 1) M' rom) /\
        WF st' L /\ REP st' M' /\ s_brk st' = s_brk st /\ s_limbo st' = s_limbo st /\ s_regions st' = s_regions st /\
        s_canary st' = s_canary st /\
        nojunk st' /\ getr r' 11 = Z_to_bv 64 0 /\ keeps_but NTF_CLOB regs r' /\ fsub st st' /\ FR L (sp - 96) (sp - 48) (M1 regs) M'.
    Proof using Hsp Hslot Hi Hgrp HREP HWF off.
      intros regs rom r1 RET H2 C10 C11 C12 C13 C2 C9 K1 PATH OJ.
      pose proof hd_wfg as WG. destruct hd_masks as (AV & FRr & Ta & Tf & Tm). pose proof hd_rng as (R1 & R2 & R8).
      pose proof hd_last as HL. pose proof hd_sc as HS. pose proof (wg_Wr st L m WG) as WR.
      destruct Hsp as (S1 & S2 & S3).
      pose proof R1 as R1n. pose proof R2 as R2n. pose proof S1 as S1n. unfold HEAPLO in R1n. ceil.
      pose proof (M1_REP regs) as HREP1.
      destruct (M1_saved regs) as (SV1 & SV8 & SV9 & SV18 & SV19 & SVc).
      destruct (G_meta_cells st L (M1 regs) HWF HREP1 m Hgrp) as (ar1 & k1 & _ & _ & _ & _ & _ & _ & _ & RM1 & _ & _).
      destruct RM1 as [Rp1 Rn1 Rme1 Rav1 Rfr1 RW1].
      pose proof (meta_store_ok st L (M1 regs) HWF HREP1 m (group_metaU st L HWF m Hgrp)) as SOKm.
      pose proof (rc_canary st (M1 regs) (rp_statics st (M1 regs) HREP1)) as CAN1.
      assert (Hself : 0 <= 2 ^ i < 2 ^ 32).
      { assert (2 ^ i <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). split; [apply Z.pow_nonneg; lia|]. change (2 ^ 32) with (2 * 2 ^ 31). lia. }
      (* [comment removed for export] *)
      assert (H63 : mask + self <> all -> sc <> 63).
      { intros Hne E63. destruct (wg_sc st L m WG) as [H48|(_ & Hl0 & _)]; [lia|].
        apply Hne. rewrite Hl0. assert (Ei0 : i = 0) by lia. rewrite Ei0 in Ta, Tf |- *.
        assert (Z0m : mask = 0).
        { apply Z.bits_inj_0. intros j. destruct (Z.lt_ge_cases j 0) as [Hj|Hj]; [apply Z.testbit_neg_r; exact Hj|].
          rewrite Z.lor_spec. destruct (Z.eq_dec j 0) as [->|Hj0]; [rewrite Ta, Tf; reflexivity|].
          destruct (Z.testbit av j) eqn:TA. { apply (proj1 (wg_av st L m WG j Hj)) in TA. lia. }
          destruct (Z.testbit fr j) eqn:TF. { apply (proj1 (wg_fr st L m WG j Hj)) in TF. lia. }
          reflexivity. }
        rewrite Z0m. reflexivity. }
      assert (HcaseR : sc < 48 /\ g_maplen st m <> 0 /\ nxt = m /\ 7 <= sc <= 38 /\ 100 <= c_bounces cx (sc - 7) /\ ~ (g_lastidx st m = 0 /\ g_maplen st m * 4096 - 16 < 16 * size_class sc) ->
                       s_kind st m = GTop /\ sc < 48 /\ s_alist st sc = [m]).
      { intros (S48 & ML & NG & _). split.
        - pose proof (wg_kind st L m WG) as KD. destruct (s_kind st m); [reflexivity|]. destruct KD as (K1' & _). exfalso. apply ML. exact K1'.
        - split; [exact S48|]. destruct hd_next as [_ NXf]. destruct (NXf ltac:(rewrite NG; unfold HEAPLO in R1; lia)) as (Im & _ & _).
          pose proof (wl_adll st (WF_lists st L HWF) sc ltac:(lia)) as D.
          pose proof (proj1 (dllf_self_iff _ _ _ m (proj1 (dll_dllf st _) D) (proj1 (NoDup_ListNoDup _) (wl_anodup st (WF_lists st L HWF) sc)) Im) NG) as Z1.
          destruct (s_alist st sc) as [|a [|b l2]] eqn:El; [destruct Im | | rewrite !zlen_cons in Z1; pose proof (zlen_nonneg l2); lia].
          destruct Im as [<-|[]]. reflexivity. }
      assert (Hcase : mask + self <> all \/ (s_kind st m = GTop /\ sc < 48 /\ s_alist st sc = [m])).
      { destruct PATH as [P|P]; [left; exact P | right; exact (HcaseR P)]. }
      assert (HNUS : sc < 48 -> UNIT * size_class sc <= g_stride st m).
      { intros S48'. destruct (Z.le_gt_cases (UNIT * size_class sc) (g_stride st m)) as [OK|LT]; [exact OK|]. exfalso.
        pose proof (wg_under st L m WG S48' LT) as L0.
        destruct PATH as [P|(S48 & ML & NG & S7 & BNC & NST)].
        - apply P. rewrite L0. assert (Ei0 : i = 0) by lia. rewrite Ei0 in Ta, Tf |- *.
          assert (Z0m : mask = 0).
          { apply Z.bits_inj_0. intros j. destruct (Z.lt_ge_cases j 0) as [Hj|Hj]; [apply Z.testbit_neg_r; exact Hj|].
            rewrite Z.lor_spec. destruct (Z.eq_dec j 0) as [->|Hj0]; [rewrite Ta, Tf; reflexivity|].
            destruct (Z.testbit av j) eqn:TA. { apply (proj1 (wg_av st L m WG j Hj)) in TA. lia. }
            destruct (Z.testbit fr j) eqn:TF. { apply (proj1 (wg_fr st L m WG j Hj)) in TF. lia. }
            reflexivity. }
          rewrite Z0m. reflexivity.
        - apply NST. split; [exact L0|]. unfold g_stride, slot_stride in LT. rewrite L0 in LT.
          replace (negb (g_maplen st m =? 0)) with true in LT by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact ML).
          cbn [Z.eqb andb] in LT. unfold UNIT in LT. lia. }
      assert (H63' : sc <> 63).
      { destruct PATH as [P|P]; [exact (H63 P)|]. destruct P as (S48 & _). lia. }
      (* [comment removed for export] *)
      assert (TAIL : forall rx Mx,
        getr rx 14 = Z_to_bv 64 (m + 28) -> getr rx 11 = s32 self -> getr rx 2 = Z_to_bv 64 (sp - 96) -> getr rx 9 = Z_to_bv 64 A_CANARY ->
        rdn RSEGS Mx (Z_to_bv 64 (m + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr)) ->
        store_ok RSEGS Mx (Z_to_bv 64 m) 40%nat = true ->
        rdn RSEGS Mx (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (s_canary st))) ->
        FR L (sp - 96) (sp - 48) (M1 regs) Mx ->
        exists r', msteps RSEGS (mkst rx (0x66c10%bv : word) Mx rom) (mkst r' (getr regs 1) (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) rom) /\
          getr r' 11 = Z_to_bv 64 0 /\ getr r' 1 = getr regs 1 /\ getr r' 2 = Z_to_bv 64 sp /\ getr r' 8 = getr regs 8 /\
          getr r' 9 = getr regs 9 /\ getr r' 18 = getr regs 18 /\ getr r' 19 = getr regs 19 /\
          keeps_but (clobOR ++ clobE) rx r' /\ FR L (sp - 96) (sp - 48) (M1 regs) (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or)).
      { intros rx Mx X14 X11 X2 X9 Xfr Xsok Xcan XFR.
        destruct (segOR Mx m fr (2 ^ i) ltac:(ceil; unfold HEAPLO in *; lia) FRr Hself Xfr Xsok rx rom X14 X11) as (ro & RUNo & O12 & O11 & Ko).
        pose proof (wc_canary st (WF_ctx st L HWF)) as CANr.
        assert (XFR2 : FR L (sp - 96) (sp - 48) (M1 regs) (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or)).
        { eapply FR_trans; [exact XFR|]. split; [apply wbytes_grows|]. intros a Hr NE. right; left.
          apply wbytes_diff in NE; [| unfold HEAPLO in *; lia | unfold bs_or; rewrite length_N_to_le_bytes; ceil; cbn; lia | exact Hr].
          unfold bs_or in NE. rewrite length_N_to_le_bytes in NE. cbn in NE.
          split; [ceil; unfold HEAPLO in *; lia|]. split; [ceil; unfold HEAPLO in *; (first [ (clear Hcase H0 S3 R8 PATH Hsp; lia) | lia ])|].
          intros (p & n & Hin & Hpn). destruct (wL_in st L (WF_live st L HWF) p n Hin) as (x & k & o & r & Hx & Hk & Sx).
          apply (ge_app_area st (WF_geom st L HWF) a).
          - exists x, k, p, n, o, r. repeat split; try assumption; lia.
          - destruct (metaU_area st L HWF m (group_metaU st L HWF m Hgrp)) as (ar & kk & Har & _ & _ & _ & _ & _ & A1 & A2 & _).
            exists ar. split; [exact Har | lia]. }
        destruct (segE (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) sp (s_canary st) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) ltac:(lia) RET) with (regs := ro) (rom := rom)
          as (re & RUNe & E2 & E1 & E8 & E9 & E18 & E19 & E10 & E11 & Ke).
        1:{ unfold bs_or. rewrite rdn_wbytes_out_Z; [exact Xcan | rewrite length_N_to_le_bytes; unfold A_CANARY, HEAPLO in *; cbn; (first [ (clear Hcase H0 S3 R8 PATH Hsp; lia) | lia ])]. }
        1-6: eapply (FR_rdn_keep L (sp - 96) (sp - 48) (M1 regs)); [exact XFR2 | ceil; lia | cbn; lia | cbn; lia | assumption].
        1: kept_rw Ko; exact X2. 1: kept_rw Ko; exact X9. 1: exact O12. 1: exact O11.
        exists re. split; [eapply msteps_trans; [exact RUNo | exact RUNe]|].
        repeat (split; [assumption|]). split; [eapply keeps_join; [exact Ko | exact Ke] | exact XFR2]. }
      (* [comment removed for export] *)
      assert (SBwr : forall Mb a, 0 <= a < 2 ^ 64 -> wbytes Mb (Z_to_bv 64 (m + 28)) bs_or (Z_to_bv 64 a) <> Mb (Z_to_bv 64 a) ->
                     sb_wr st m i off (CEIL + MSTK) a).
      { intros Mb a Hr NE. unfold sb_wr. right; right.
        apply wbytes_diff in NE; [| unfold HEAPLO in *; lia | unfold bs_or; rewrite length_N_to_le_bytes; ceil; cbn; lia | exact Hr].
        unfold bs_or in NE. rewrite length_N_to_le_bytes in NE. cbn in NE. lia. }
      assert (SBfr : forall Mb, cell (wbytes Mb (Z_to_bv 64 (m + 28)) bs_or) (m + 28) 4 (fr + 2 ^ i)).
      { intros Mb. unfold cell. rewrite bs_or_val. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 (fr + 2 ^ i))) Mb (Z_to_bv 64 (m + 28))) as RH.
        rewrite length_N_to_le_bytes in RH. apply RH. rewrite u_Z2bv by (ceil; unfold HEAPLO in *; lia). ceil; lia. }
      assert (NJ : nojunk (UbMhSetBit.st' st m i)).
      { intros x k o Hx Hk E. rewrite UbMhSetBit.e_slot in E. rewrite UbMhSetBit.e_glast in Hk.
        change (is_group st x) in Hx.
        destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in E; try discriminate E;
          destruct (OJ x k o Hx Hk E); congruence. }
      assert (COV : forall big : list reg, forallb (fun r => existsb (fun x => bv_eqb x r) NTF_CLOB || existsb (fun x => bv_eqb x r) [1; 2; 8; 9; 18; 19]%bv)%bool big = true ->
                    forall r, In r big -> In r NTF_CLOB \/ In r [1; 2; 8; 9; 18; 19]%bv).
      { intros big Hb r Hr. pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hb'. clear Hb. rename Hb' into Hb. cbn beta in Hb. apply Bool.orb_true_iff in Hb.
        destruct Hb as [Hb|Hb]; [left | right]; apply in_regs_dec; exact Hb. }
      destruct (Z.eq_dec mask 0) as [Hm0|Hm0].
      - (* [comment removed for export] *)
        assert (S48 : sc < 48).
        { destruct PATH as [P|P]; [|exact (proj1 P)]. destruct (wg_sc st L m WG) as [H48|(E63 & Hl0 & _)]; [exact H48|]. exfalso.
          apply P. rewrite Hm0, Hl0. replace i with 0 by lia. reflexivity. }
        set (hd := c_active cx sc).
        assert (Ehd : hd = head_of (s_alist st sc)) by (subst hd; apply (wc_active st (WF_ctx st L HWF)); lia).
        pose proof (rc_active st (M1 regs) (rp_ctx st (M1 regs) HREP1) sc ltac:(lia)) as HDc. fold hd in HDc.
        assert (HDr : 0 <= hd < 2 ^ 64 /\ (hd <> 0 -> In hd (s_alist st sc))).
        { rewrite Ehd. destruct (s_alist st sc) as [|a l] eqn:El; cbn; [lia|].
          assert (Ia : In a (s_alist st sc)) by (rewrite El; left; reflexivity).
          destruct (alist_member st L HWF sc a Ia) as (_ & _ & _ & Ua & _). destruct (metaU_rng st L HWF a Ua). ceil; unfold HEAPLO in *.
          split; [lia | intros _; left; reflexivity]. }
        destruct HDr as [HDr HDin].
        destruct (segB2_pfx (M1 regs) m sc hd mask ltac:(lia) HS HDc r1 rom C10 C12 C13 Hm0 S48) as (r2 & RUN2 & D14 & D12 & D13 & D10 & K2).
        destruct (Z.eq_dec hd m) as [Hhm|Hhm].
        + (* [comment removed for export] *)
          destruct (segB2h (M1 regs) m hd r2 rom D10 D12 Hhm) as (r3 & RUN3 & K3).
          destruct (TAIL r3 (M1 regs)) as (r' & RUN4 & E11 & E1 & E2 & E8 & E9 & E18 & E19 & K4 & FR4).
          1-4: kept_rw K3; try assumption. 1: kept_rw K2; exact C11. 1: kept_rw K2; exact C2. 1: kept_rw K2; exact C9.
          1: exact Rfr1. 1: exact SOKm. 1: exact CAN1. 1: apply FR_refl.
          destruct (setbit_close st L (M1 regs) (wbytes (M1 regs) (Z_to_bv 64 (m + 28)) bs_or) m i off (CEIL + MSTK)
                     HWF HREP1 Hgrp Hi Hslot ltac:(lia) (SBwr (M1 regs)) ltac:(apply wbytes_grows) (SBfr (M1 regs)) H63'
                     ltac:(destruct Hcase as [X|X]; [left; exact X | right; exact X]) HNUS) as [WF' REP'].
          exists (UbMhSetBit.st' st m i), (wbytes (M1 regs) (Z_to_bv 64 (m + 28)) bs_or), r'.
          split; [eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]|].
          split; [exact WF'|]. split; [exact REP'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
          split; [exact NJ|]. split; [exact E11|]. split; [|split; [apply fsub_setbit | exact FR4]].
          apply (keeps_final regs r' ((clobN0 ++ clobD) ++ (clobB ++ ([] ++ (clobOR ++ clobE))))).
          * eapply keeps_join; [exact K1|]. eapply keeps_join; [exact K2|]. eapply keeps_join; [exact K3 | exact K4].
          * apply COV. reflexivity.
          * exact E1. * rewrite E2, H2; reflexivity. * exact E8. * exact E9. * exact E18. * exact E19.
        + (* [comment removed for export] *)
          assert (AV0 : av = 0 /\ fr = 0) by (apply Z.lor_eq_0_iff; exact Hm0). destruct AV0 as [AV0 FR0].
          assert (USED : forall k, 0 <= k <= g_lastidx st m -> s_slot st m k <> SAvail /\ s_slot st m k <> SFreed).
          { intros k Hk. split; intros E.
            - pose proof (proj2 (wg_av st L m WG k ltac:(lia)) (conj (proj2 Hk) E)) as T. rewrite AV0, Z.bits_0 in T. discriminate T.
            - pose proof (proj2 (wg_fr st L m WG k ltac:(lia)) (conj (proj2 Hk) E)) as T. rewrite FR0, Z.bits_0 in T. discriminate T. }
          assert (NL : ~ listed st m).
          { apply (wg_full st L m WG USED). rewrite <- Ehd. intros E. exact (Hhm (eq_sym E)). }
          destruct (wl_link st (WF_lists st L HWF) m (group_metaU st L HWF m Hgrp) NL) as [NX0 PV0].
          assert (PNE : mask + self <> all).
          { destruct PATH as [P|P]; [exact P|]. destruct P as (_ & _ & NG & _). exfalso. rewrite NX0 in NG. unfold HEAPLO in R1. lia. }
          assert (EXK : exists k, 0 <= k <= g_lastidx st m /\ k <> i).
          { destruct (Z.eq_dec (g_lastidx st m) 0) as [E0|E0]; [|exists (if Z.eq_dec i 0 then 1 else 0); destruct (Z.eq_dec i 0); (first [ (clear COV H0 S3 R8 Hsp; lia) | lia ])].
            exfalso. apply PNE. rewrite Hm0, E0. replace i with 0 by lia. reflexivity. }
          pose proof Rn1 as Rn0. rewrite NX0 in Rn0. pose proof Rp1 as Rp0. rewrite PV0 in Rp0.
          assert (SOKm16 : store_ok RSEGS (M1 regs) (Z_to_bv 64 m) 16%nat = true).
          { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKm | | ]; rewrite ?u_Z2bv by (ceil; unfold HEAPLO in *; (first [ (clear COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])); cbn; ceil; (first [ (clear COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]). }
          (* [comment removed for export] *)
          set (stS := UbMhSetBit.st' st m i).
          assert (QnilE : UbMhQueue.q_nil stS sc = is_nilb (s_alist st sc)) by (unfold UbMhQueue.q_nil; subst stS; rewrite UbMhSetBit.e_alist; reflexivity).
          assert (Qgrp : is_group stS m) by (change (is_group st m); exact Hgrp).
          assert (Qsc : g_sc stS m = sc) by (subst stS; rewrite UbMhSetBit.e_gsc; reflexivity).
          assert (Qunl : ~ listed stS m) by (subst stS; rewrite (UbMhSetBit.e_listed st m i Hi Hcase HNUS); exact NL).
          assert (Qrest : UbMhQueue.q_nil stS sc = false -> mr_avail (s_meta stS m) = 0 /\ mr_freed (s_meta stS m) <> 0).
          { intros _. subst stS. rewrite UbMhSetBit.e_avail, UbMhSetBit.e_freed_m, AV0, FR0. split; [reflexivity|].
            assert (0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia). lia. }
          assert (Qnotfull : exists k, 0 <= k <= g_lastidx stS m /\ (s_slot stS m k = SAvail \/ s_slot stS m k = SFreed)).
          { exists i. subst stS. rewrite UbMhSetBit.e_glast, UbMhSetBit.e_slot_mi. split; [exact Hi | right; reflexivity]. }
          assert (Qff : (forall k, 0 <= k <= g_lastidx stS m -> s_slot stS m k = SAvail \/ s_slot stS m k = SFreed) ->
                        s_kind stS m = GTop /\ UbMhQueue.q_nil stS sc = true).
          { intros ALL. exfalso. destruct EXK as (k & Hk & Hki). subst stS. rewrite UbMhSetBit.e_glast in ALL.
            destruct (ALL k Hk) as [E|E]; rewrite (UbMhSetBit.e_slot_other st m i Hi H63' m k (or_intror Hki)) in E; destruct (USED k Hk); congruence. }
          (* [comment removed for export] *)
          destruct (setbit_close st L (M1 regs) (wbytes (M1 regs) (Z_to_bv 64 (m + 28)) bs_or) m i off (CEIL + MSTK)
                     HWF HREP1 Hgrp Hi Hslot ltac:(lia) (SBwr (M1 regs)) ltac:(apply wbytes_grows) (SBfr (M1 regs)) H63'
                     ltac:(destruct Hcase as [X|X]; [left; exact X | right; exact X]) HNUS) as [WFS REPS]. fold stS in WFS, REPS.
          (* [comment removed for export] *)
          assert (QFIN : forall r3 Mx,
            msteps RSEGS (mkst r2 (0x66a14%bv : word) (M1 regs) rom) (mkst r3 (0x66c10%bv : word) Mx rom) ->
            keeps_but [12; 15]%bv r2 r3 ->
            rdn RSEGS Mx (Z_to_bv 64 (m + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fr)) ->
            store_ok RSEGS Mx (Z_to_bv 64 m) 40%nat = true ->
            rdn RSEGS Mx (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (s_canary st))) ->
            FR L (sp - 96) (sp - 48) (M1 regs) Mx ->
            mem_grows (M1 regs) Mx ->
            (forall a, 0 <= a < 2 ^ 64 -> ~ (m + 28 <= a < m + 32) -> Mx (Z_to_bv 64 a) <> M1 regs (Z_to_bv 64 a) -> UbMhQueue.q_wr stS m sc (CEIL + MSTK) a) ->
            cell (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) m 8 (UbMhQueue.q_prev stS m sc m) ->
            cell (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) (m + 8) 8 (UbMhQueue.q_next stS m sc m) ->
            (UbMhQueue.q_nil stS sc = false -> cell (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) (znth (s_alist stS sc) (zlen (s_alist stS sc) - 1) + 8) 8 m) ->
            (UbMhQueue.q_nil stS sc = false -> cell (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) (head_of (s_alist stS sc)) 8 m) ->
            (UbMhQueue.q_nil stS sc = true -> cell (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) (ctx_active sc) 8 m) ->
            exists st' M' r',
              msteps RSEGS (mkst r1 (0x669ec%bv : word) (M1 regs) rom) (mkst r' (getr regs 1) M' rom) /\
              WF st' L /\ REP st' M' /\ s_brk st' = s_brk st /\ s_limbo st' = s_limbo st /\ s_regions st' = s_regions st /\
              s_canary st' = s_canary st /\
              nojunk st' /\ getr r' 11 = Z_to_bv 64 0 /\ keeps_but NTF_CLOB regs r' /\ fsub st st' /\ FR L (sp - 96) (sp - 48) (M1 regs) M').
          { intros r3 Mx RUN3 K3 Xfr Xsok Xcan XFR XG XWR C0 C8 Ctl Chd Cact.
            destruct (TAIL r3 Mx) as (r' & RUN4 & E11 & E1 & E2 & E8 & E9 & E18 & E19 & K4 & FR4).
            1-4: kept_rw K3; try assumption. 1: kept_rw K2; exact C11. 1: kept_rw K2; exact C2. 1: kept_rw K2; exact C9.
            1: exact Xfr. 1: exact Xsok. 1: exact Xcan. 1: exact XFR.
            destruct (queue_close stS L (wbytes (M1 regs) (Z_to_bv 64 (m + 28)) bs_or) (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or) m sc (CEIL + MSTK)
                       WFS REPS Qgrp Qsc ltac:(lia) Qunl Qrest Qnotfull ltac:(lia)) as [WFQ REPQ].
            - intros a Hr NE.
              destruct (decide (m + 28 <= a < m + 32)) as [IN|OUT].
              + exfalso. apply NE. apply wbytes_same_inside; unfold bs_or; rewrite length_N_to_le_bytes, ?u_Z2bv by (ceil; unfold HEAPLO in *; (first [ (clear Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])); cbn; ceil; (first [ (clear Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
              + apply XWR; [exact Hr | exact OUT|]. intros E. apply NE.
                rewrite !wbytes_outside; [exact E | | | |]; unfold in_rng, bs_or; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by (ceil; unfold HEAPLO in *; (first [ (clear Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])); cbn; ceil; (first [ (clear Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            - intros a Hne. destruct (decide (bv_unsigned (Z_to_bv 64 (m + 28)) <= bv_unsigned a < bv_unsigned (Z_to_bv 64 (m + 28)) + 4)) as [IN|OUT].
              + rewrite (wbytes_same_inside bs_or Mx (M1 regs)); [exact Hne | |]; unfold bs_or; rewrite length_N_to_le_bytes; cbn; [|exact IN].
                rewrite u_Z2bv by (ceil; unfold HEAPLO in *; lia). ceil; lia.
              + assert (NI : ~ in_rng a (Z_to_bv 64 (m + 28)) (Z.of_nat (length bs_or))) by (unfold in_rng, bs_or; rewrite length_N_to_le_bytes; cbn; exact OUT).
                assert (NW : bv_unsigned (Z_to_bv 64 (m + 28)) + Z.of_nat (length bs_or) <= 2 ^ 64).
                { unfold bs_or. rewrite length_N_to_le_bytes. rewrite u_Z2bv by (ceil; unfold HEAPLO in *; (first [ (clear Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])). ceil; cbn; (first [ (clear Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]). }
                rewrite (wbytes_outside bs_or Mx _ a NI NW). rewrite (wbytes_outside bs_or (M1 regs) _ a NI NW) in Hne. apply XG. exact Hne.
            - exact C0.
            - exact C8.
            - exact Ctl.
            - exact Chd.
            - exact Cact.
            - exists (UbMhQueue.st' stS m sc), (wbytes Mx (Z_to_bv 64 (m + 28)) bs_or), r'.
              split; [eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]|].
              split; [exact WFQ|]. split; [exact REPQ|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
              split; [intros x k o Hx Hk E; apply (NJ x k o Hx Hk E)|]. split; [exact E11|]. split; [|split; [exact (fsub_trans _ _ _ (fsub_setbit st m i) (fsub_queue stS m sc)) | exact FR4]].
              apply (keeps_final regs r' ((clobN0 ++ clobD) ++ (clobB ++ ([12; 15]%bv ++ (clobOR ++ clobE))))).
              * eapply keeps_join; [exact K1|]. eapply keeps_join; [exact K2|]. eapply keeps_join; [exact K3 | exact K4].
              * apply COV. reflexivity.
              * exact E1. * rewrite E2, H2; reflexivity. * exact E8. * exact E9. * exact E18. * exact E19. }
          (* [comment removed for export] *)
          assert (FRmeta : forall x a, metaU st x -> x <= a < x + 40 -> HEAPLO <= a < CEIL /\ (a < IMG_LO \/ IMG_HI <= a) /\ ~ app_of L a).
          { intros x a Ux Ha. destruct (metaU_area st L HWF x Ux) as (ar & kk & Har & _ & _ & _ & Rlo & Rhi & A1 & A2 & _).
            split; [(first [ (clear Qff Qnotfull COV Hcase S3 R8 PATH; lia) | lia ])|]. split; [pose proof (metaU_img st L HWF x Ux); (first [ (clear H1 Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])|]. intros (p & n & Hin & Hpn). destruct (wL_in st L (WF_live st L HWF) p n Hin) as (y & k & o & r & Hy & Hk & Sy).
            apply (ge_app_area st (WF_geom st L HWF) a); [exists y, k, p, n, o, r; repeat split; try assumption; (first [ (clear COV H0 S3 R8 Hsp; lia) | lia ]) | exists ar; split; [exact Har | (first [ (clear Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])]]. }
          pose proof (metaU_area st L HWF m (group_metaU st L HWF m Hgrp)) as MUm.
          destruct (Z.eq_dec hd 0) as [Hd0|Hd0].
          * (* [comment removed for export] *)
            assert (Lnil : s_alist st sc = []).
            { destruct (s_alist st sc) as [|a l] eqn:El; [reflexivity|]. exfalso.
              assert (Ia : In a (s_alist st sc)) by (rewrite El; left; reflexivity).
              destruct (alist_member st L HWF sc a Ia) as (_ & _ & _ & Ua & _). destruct (metaU_rng st L HWF a Ua).
              rewrite Ehd in Hd0. cbn in Hd0. unfold HEAPLO in *. lia. }
            assert (Qnil : UbMhQueue.q_nil stS sc = true) by (rewrite QnilE, Lnil; reflexivity).
            assert (SOKa : store_ok RSEGS (M1 regs) (Z_to_bv 64 (ctx_active sc)) 8%nat = true).
            { eapply (store_ok_sub _ _ _ _ 928%nat); [ | exact (ctx_store_ok st (M1 regs) HREP1) | | ];
                unfold ctx_active, CTX; rewrite ?u_Z2bv by (first [ (clear MUm FRmeta Qnotfull COV H0 S3 R8 Hsp; lia) | lia ]); cbn; (first [ (clear MUm FRmeta Qnotfull COV H0 S3 R8 Hsp; lia) | lia ]). }
            destruct (segB2e (M1 regs) m sc hd ltac:((first [ (clear Qff Qnotfull COV Hcase S3 R8 PATH; lia) | lia ])) HS HDr Rn0 Rp0 SOKm16 r2 rom SOKa D10 D12 D13 Hd0) as (r3 & RUN3 & K3).
            apply (QFIN r3 (m_e (M1 regs) m sc) RUN3 K3).
            -- unfold m_e, ctx_active, CTX. pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)) as IMm. pose proof ceil_rng as CRN.
               do 3 (rpeel - R1n R2n CRN S48 HS IMm). exact Rfr1.
            -- unfold m_e. do 3 (eapply store_ok_mono; [apply wbytes_grows|]). exact SOKm.
            -- unfold m_e, ctx_active, CTX, A_CANARY in *. pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)) as IMm. pose proof ceil_rng as CRN.
               do 3 (rpeel - R1n R2n CRN S48 HS IMm). exact CAN1.
            -- (* [comment removed for export] *)
               assert (W3 : forall a, 0 <= a < 2 ^ 64 -> m_e (M1 regs) m sc (Z_to_bv 64 a) <> M1 regs (Z_to_bv 64 a) ->
                              (m <= a < m + 16) \/ (ctx_active sc <= a < ctx_active sc + 8)).
               { intros a Hr NE. exact (m_e_writes (M1 regs) m sc a ltac:((first [ (clear MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])) ltac:((first [ (clear MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])) HS Hr NE). }
               split; [unfold m_e; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|].
               intros a Hr NE. destruct (W3 a Hr NE) as [A|A].
               ++ right; left. apply (FRmeta m); [exact (group_metaU st L HWF m Hgrp) | lia].
               ++ right; right. unfold ctx_active, CTX_END, CTX in *. (first [ (clear MUm Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            -- unfold m_e. do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
            -- intros a Hr OUT NE. unfold UbMhQueue.q_wr. rewrite Qnil.
               assert (W3 : (m <= a < m + 16) \/ (ctx_active sc <= a < ctx_active sc + 8)).
               { exact (m_e_writes (M1 regs) m sc a ltac:((first [ (clear MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])) ltac:((first [ (clear MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ])) HS Hr NE). }
               destruct W3 as [A|A]; [right; left; exact A | right; right; right; split; [reflexivity | exact A]].
            -- unfold cell, m_e, ctx_active, CTX. unfold UbMhQueue.q_prev. rewrite Z.eqb_refl, Qnil. unfold bs_or. pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)) as IMm. pose proof ceil_rng as CRN.
               do 3 (rpeel - R1n R2n CRN S48 HS IMm). apply rdn_wbytes_hit8. zsimp; (first [ (clear IMm MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            -- unfold cell, m_e, ctx_active, CTX. unfold UbMhQueue.q_next. rewrite Z.eqb_refl, Qnil. unfold bs_or. pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)) as IMm. pose proof ceil_rng as CRN.
               do 2 (rpeel - R1n R2n CRN S48 HS IMm). apply rdn_wbytes_hit8. zsimp; (first [ (clear IMm MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            -- intros X. rewrite Qnil in X. discriminate X.
            -- intros X. rewrite Qnil in X. discriminate X.
            -- intros _. unfold cell, m_e, ctx_active, CTX, bs_or. pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)) as IMm. pose proof ceil_rng as CRN.
               rpeel - R1n R2n CRN S48 HS IMm. apply rdn_wbytes_hit8. zsimp; (first [ (clear IMm MUm FRmeta Qnotfull COV H0 S3 R8 Hsp; lia) | lia ]).
          * (* [comment removed for export] *)
            pose proof (HDin Hd0) as Ihd.
            assert (Lnn : s_alist st sc <> []) by (intros El; rewrite El in Ihd; exact Ihd).
            assert (Qnil : UbMhQueue.q_nil stS sc = false) by (rewrite QnilE; apply is_nilb_false; exact Lnn).
            set (tl := znth (s_alist st sc) (zlen (s_alist st sc) - 1)).
            pose proof (wl_adll st (WF_lists st L HWF) sc ltac:(lia)) as Dl.
            destruct (dllf_ends _ _ _ (proj1 (dll_dllf st _) Dl) (zlen_pos _ Lnn)) as [Ntl Phd].
            rewrite <- (head_of_znth _ Lnn), <- Ehd in Ntl, Phd. fold tl in Ntl, Phd.
            assert (Itl : In tl (s_alist st sc)) by (subst tl; apply last_In; exact Lnn).
            destruct (alist_member st L HWF sc hd Ihd) as (_ & Ghd & _ & Uhd & Lhd).
            destruct (alist_member st L HWF sc tl Itl) as (_ & Gtl & _ & Utl & Ltl).
            assert (Nhm : hd <> m) by exact Hhm.
            assert (Ntm : tl <> m) by (intros E; apply NL; rewrite <- E; exact Ltl).
            destruct (metaU_rng st L HWF hd Uhd) as (Hh1 & Hh2 & _). destruct (metaU_rng st L HWF tl Utl) as (Ht1 & Ht2 & _).
            pose proof (metaU_sep st L HWF m hd (group_metaU st L HWF m Hgrp) Uhd (fun E => Nhm (eq_sym E))) as SEPh.
            pose proof (metaU_sep st L HWF m tl (group_metaU st L HWF m Hgrp) Utl (fun E => Ntm (eq_sym E))) as SEPt.
            assert (HT : hd = tl \/ hd + 40 <= tl \/ tl + 40 <= hd).
            { destruct (Z.eq_dec hd tl) as [E|NE]; [left; exact E | right; exact (metaU_sep st L HWF hd tl Uhd Utl NE)]. }
            ceil; unfold HEAPLO in Hh1, Hh2, Ht1, Ht2.
            destruct (meta_cells st L (M1 regs) HWF HREP1 hd Uhd) as (arh & kh & _ & _ & _ & _ & _ & _ & RMh & _).
            pose proof (rm_prev _ _ _ RMh) as Chd0. rewrite Phd in Chd0. unfold cell in Chd0.
            pose proof (meta_store_ok st L (M1 regs) HWF HREP1 hd Uhd) as SOKh40.
            pose proof (meta_store_ok st L (M1 regs) HWF HREP1 tl Utl) as SOKt40.
            assert (SOKh : store_ok RSEGS (M1 regs) (Z_to_bv 64 hd) 8%nat = true).
            { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKh40 | | ]; rewrite ?u_Z2bv by (first [ (clear SEPt MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]); cbn; (first [ (clear SEPt MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]). }
            assert (SOKt : store_ok RSEGS (M1 regs) (Z_to_bv 64 (tl + 8)) 8%nat = true).
            { eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKt40 | | ]; rewrite ?u_Z2bv by (first [ (clear SEPh MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]); cbn; (first [ (clear SEPh MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]). }
            pose proof ceil_rng as CRN.
            (* [comment removed for export] *)
            assert (A1q : HEAPLO <= m /\ m + 40 <= CEIL /\ (m + 40 <= IMG_LO \/ IMG_HI <= m)).
            { pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)) as IMm. unfold HEAPLO. clear - R1n R2n IMm. zlia. }
            assert (A3q : 0 <= tl < 2 ^ 64) by (clear - Ht1 Ht2 CRN; zlia).
            assert (A4q : HEAPLO <= hd) by (unfold HEAPLO; clear - Hh1; zlia).
            assert (A6q : HEAPLO <= tl) by (unfold HEAPLO; clear - Ht1; zlia).
            destruct (segB2q (M1 regs) m hd tl A1q HDr A3q Rn0 Rp0 SOKm16 r2 rom A4q Hh2
                        A6q Ht2 SEPh SEPt Chd0 SOKh SOKt D10 D12 Hhm Hd0) as (r3 & RUN3 & K3).
            assert (Etl : znth (s_alist stS sc) (zlen (s_alist stS sc) - 1) = tl) by (subst stS; rewrite UbMhSetBit.e_alist; reflexivity).
            assert (Ehd' : head_of (s_alist stS sc) = hd) by (subst stS; rewrite UbMhSetBit.e_alist; symmetry; exact Ehd).
            assert (MQW : forall a, 0 <= a < 2 ^ 64 -> m_q (M1 regs) m hd tl (Z_to_bv 64 a) <> M1 regs (Z_to_bv 64 a) ->
                          (m <= a < m + 16) \/ (tl + 8 <= a < tl + 16) \/ (hd <= a < hd + 8)).
            { intros a Hr NE. apply (m_q_writes (M1 regs) m hd tl a); [clear - R1n; zlia | clear - R2n CRN; zlia | clear - Hh1; zlia | clear - Hh2 CRN; zlia
                                                                      | clear - Ht1; zlia | clear - Ht2 CRN; zlia | exact Hr | exact NE]. }
            apply (QFIN r3 (m_q (M1 regs) m hd tl) RUN3 K3).
            -- unfold m_q. do 4 (rpeel - R1n R2n CRN Hh1 Hh2 Ht1 Ht2 SEPh SEPt HT). exact Rfr1.
            -- unfold m_q. do 4 (eapply store_ok_mono; [apply wbytes_grows|]). exact SOKm.
            -- unfold m_q, A_CANARY in *. pose proof (metaU_img st L HWF m (group_metaU st L HWF m Hgrp)) as IMm. pose proof (metaU_img st L HWF hd Uhd) as IMh. pose proof (metaU_img st L HWF tl Utl) as IMt.
               do 4 (rpeel - R1n R2n CRN Hh1 Hh2 Ht1 Ht2 SEPh SEPt HT IMm IMh IMt). exact CAN1.
            -- assert (W4 : forall a, 0 <= a < 2 ^ 64 -> m_q (M1 regs) m hd tl (Z_to_bv 64 a) <> M1 regs (Z_to_bv 64 a) ->
                              (m <= a < m + 16) \/ (tl + 8 <= a < tl + 16) \/ (hd <= a < hd + 8)).
               { intros a Hr NE. exact (MQW a Hr NE). }
               split; [unfold m_q; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|].
               intros a Hr NE. right; left. destruct (W4 a Hr NE) as [A|[A|A]].
               ++ apply (FRmeta m); [exact (group_metaU st L HWF m Hgrp) | lia].
               ++ apply (FRmeta tl); [exact Utl | lia].
               ++ apply (FRmeta hd); [exact Uhd | lia].
            -- unfold m_q. do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
            -- intros a Hr OUT NE. unfold UbMhQueue.q_wr. rewrite Qnil, Etl, Ehd'.
               assert (W4 : (m <= a < m + 16) \/ (tl + 8 <= a < tl + 16) \/ (hd <= a < hd + 8)).
               { exact (MQW a Hr NE). }
               destruct W4 as [A|[A|A]]; [right; left; exact A | right; right; left; split; [reflexivity | left; exact A]
                                        | right; right; left; split; [reflexivity | right; exact A]].
            -- unfold cell, m_q, bs_or. unfold UbMhQueue.q_prev. rewrite Z.eqb_refl, Qnil, Etl. do 3 (rpeel - R1n R2n CRN Hh1 Hh2 Ht1 Ht2 SEPh SEPt HT). apply rdn_wbytes_hit8. zsimp; (first [ (clear MQW A1q HT SEPt SEPh MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            -- unfold cell, m_q, bs_or. unfold UbMhQueue.q_next. rewrite Z.eqb_refl, Qnil, Ehd'. do 4 (rpeel - R1n R2n CRN Hh1 Hh2 Ht1 Ht2 SEPh SEPt HT). apply rdn_wbytes_hit8. zsimp; (first [ (clear MQW A1q HT SEPt SEPh MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            -- intros _. rewrite Etl. unfold cell, m_q, bs_or. do 2 (rpeel - R1n R2n CRN Hh1 Hh2 Ht1 Ht2 SEPh SEPt HT). apply rdn_wbytes_hit8. zsimp; (first [ (clear A1q SEPh MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            -- intros _. rewrite Ehd'. unfold cell, m_q, bs_or. rpeel - R1n R2n CRN Hh1 Hh2 Ht1 Ht2 SEPh SEPt HT. apply rdn_wbytes_hit8. zsimp; (first [ (clear A1q SEPt MUm FRmeta Qff Qnotfull COV Hcase H0 S3 R8 PATH Hsp; lia) | lia ]).
            -- intros X. rewrite Qnil in X. discriminate X.
      - (* [comment removed for export] *)
        destruct (segB3 (M1 regs) m mask ltac:((first [ (clear COV Hcase S3 R8 PATH; lia) | lia ])) (Z_lor_range32 _ _ AV FRr) r1 rom C10 C13 Hm0) as (r3 & RUN3 & D14 & K3).
        destruct (TAIL r3 (M1 regs)) as (r' & RUN4 & E11 & E1 & E2 & E8 & E9 & E18 & E19 & K4 & FR4).
        1: exact D14. 1-3: kept_rw K3; assumption.
        1: exact Rfr1. 1: exact SOKm. 1: exact CAN1. 1: apply FR_refl.
        destruct (setbit_close st L (M1 regs) (wbytes (M1 regs) (Z_to_bv 64 (m + 28)) bs_or) m i off (CEIL + MSTK)
                   HWF HREP1 Hgrp Hi Hslot ltac:(lia) (SBwr (M1 regs)) ltac:(apply wbytes_grows) (SBfr (M1 regs)) H63'
                   ltac:(destruct Hcase as [X|X]; [left; exact X | right; exact X]) HNUS) as [WF' REP'].
        exists (UbMhSetBit.st' st m i), (wbytes (M1 regs) (Z_to_bv 64 (m + 28)) bs_or), r'.
        split; [eapply msteps_trans; [exact RUN3 | exact RUN4]|].
        split; [exact WF'|]. split; [exact REP'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact NJ|]. split; [exact E11|]. split; [|split; [apply fsub_setbit | exact FR4]].
        apply (keeps_final regs r' ((clobN0 ++ clobD) ++ ([14]%bv ++ (clobOR ++ clobE)))).
        * eapply keeps_join; [exact K1|]. eapply keeps_join; [exact K3 | exact K4].
        * apply COV. reflexivity.
        * exact E1. * rewrite E2, H2; reflexivity. * exact E8. * exact E9. * exact E18. * exact E19.
    Qed.
  End Head.

  (* [comment removed for export] *)
  Definition NTF_SPEC (d : nat) : Prop :=
    forall st L M regs rom m i off sp,
      WF st L -> REP st M -> is_group st m -> 0 <= i <= g_lastidx st m -> s_slot st m i = SJunk off ->
      nest_depth_le st d m -> only_junk st m i ->
      getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 i -> getr regs 2 = Z_to_bv 64 sp -> ret_ok (getr regs 1) ->
      CEIL + 96 * (Z.of_nat d + 1) <= sp -> sp < 2 ^ 64 -> sp mod 16 = 0 ->
      defined M (sp - 96 * (Z.of_nat d + 1)) sp ->
      exists st' M' regs',
        msteps RSEGS (mkst regs (0x66890%bv : word) M rom) (mkst regs' (getr regs 1) M' rom) /\
        WF st' L /\ REP st' M' /\ s_brk st' = s_brk st /\ s_limbo st' = s_limbo st /\ s_canary st' = s_canary st /\ nojunk st' /\
        ntf_ret st st' regs' /\ keeps_but NTF_CLOB regs regs' /\ fsub st st' /\ FR L (sp - 96 * (Z.of_nat d + 1)) sp M M'.
End Asm.

Ltac lia_pairs ::= idtac.
