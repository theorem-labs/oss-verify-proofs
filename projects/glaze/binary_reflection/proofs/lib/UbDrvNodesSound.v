(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbExit_run1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs.UbExitBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac u_norm ::= pu_u_norm.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.

Lemma w12 : forall regs mem rom,
  exists regs',
    msteps RSEGS (mkst regs (0x65e50 : word) mem rom)
                 (mkst regs' (0x68bb0 : word) mem rom)
    /\ getr regs' 2 = getr regs 2
    /\ getr regs' 8 = getr regs 8
    /\ getr regs' 1 = Z_to_bv 64 0x65e54
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof using.
  intros regs mem rom. eexists. split.
  - (* [comment removed for export] *)
    stepn F_65dfc D_65dfc.
    pu_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbExit_run1.
Module UbExit_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs.UbExitBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
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

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x65e54)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x68bc0)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x65e54 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x79ec8 wp1 rp1 ->
  file_clean mem 0x79dd8 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x68bb0 : word) mem rom)
                 (mkst regs' (0x65bc0 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof using.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_68b5c D_68b5c. rewrite Hsp. sp_renorm.
    stepST F_68b60 D_68b60 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x65e54) ltac:(sok_stack SOK).
    stepST F_68b64 D_68b64 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_68b68 D_68b68.
    stepn F_68ef0 D_68ef0. sp_renorm.
    stepST F_68ef4 D_68ef4 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x68bc0) ltac:(sok_stack SOK).
    stepST F_68ef8 D_68ef8 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_68efc D_68efc.
    stepn F_68f00 D_68f00.
    stepn F_68f04 D_68f04.
    (* [comment removed for export] *)
    stepn F_68f08 D_68f08.
    stepn F_73ac8 D_73ac8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_73acc | reflexivity | exact D_73acc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_73ad0 D_73ad0 ltac:(cond_compute).
    stepret F_73cc0 D_73cc0 (0x68f60 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_68f0c D_68f0c.
    stepLD8 F_68f10 D_68f10 (Z_to_bv 64 0x68bc0).
    stepLD8 F_68f14 D_68f14 code.
    stepn F_68f18 D_68f18. sp_renorm.
    stepret F_68f1c D_68f1c (0x68bc0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_68b6c D_68b6c (Z_to_bv 64 0).
    stepb_ft F_68b70 D_68b70 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_68b74 D_68b74.
    stepLD8 F_68b78 D_68b78 (Z_to_bv 64 0).
    stepb_tk F_68b7c D_68b7c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_68bd0 D_68bd0.
    stepLD8 F_68bd4 D_68bd4 (Z_to_bv 64 0x79ec8).
    stepb_ft F_68bd8 D_68bd8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_68bdc D_68bdc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_68be0 D_68be0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_68bec D_68bec wp1.
    stepLD8 F_68bf0 D_68bf0 wp1.
    stepb_tk F_68bf4 D_68bf4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_68c0c D_68c0c rp1.
    stepLD8 F_68c10 D_68c10 rp1.
    stepb_tk F_68c14 D_68c14 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_68c2c D_68c2c.
    stepLD8 F_68c30 D_68c30 (Z_to_bv 64 0x79dd8).
    stepb_ft F_68c34 D_68c34 ltac:(cond_compute).
    stepLD F_68c38 D_68c38 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_68c3c D_68c3c ltac:(cond_compute).
    stepLD8 F_68c48 D_68c48 wp2.
    stepLD8 F_68c4c D_68c4c wp2.
    stepb_tk F_68c50 D_68c50 ltac:(apply c_eq_refl).
    stepLD8 F_68c68 D_68c68 rp2.
    stepLD8 F_68c6c D_68c6c rp2.
    stepb_tk F_68c70 D_68c70 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_68cf0 D_68cf0 (Z_to_bv 64 0x65e54).
    stepLD8 F_68cf4 D_68cf4 code.
    stepn F_68cf8 D_68cf8. sp_renorm.
    stepret F_68cfc D_68cfc (0x65e54 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_65e00 D_65e00.
    stepn F_65e04 D_65e04.
    stepn F_65b64 D_65b64.
    stepn F_65b68 D_65b68.
    pu_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbExit_run2.
Module UbExit_run3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs.UbExitBase UbExit_run2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
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
Section FPGen1.
Context {fx : FPState}.

Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x79ec8 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x79ec8 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x79ec8 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x79ec8 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x69010)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x65e54 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x68bb0 : word) mem rom)
                 (mkst regs' (0x69010 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x79ec8
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x68c60
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x79ec8
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof using.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_68b5c D_68b5c. rewrite Hsp. sp_renorm.
    stepST F_68b60 D_68b60 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x65e54) ltac:(sok_stack SOK).
    stepST F_68b64 D_68b64 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_68b68 D_68b68.
    stepn F_68ef0 D_68ef0. sp_renorm.
    stepST F_68ef4 D_68ef4 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x68bc0) ltac:(sok_stack SOK).
    stepST F_68ef8 D_68ef8 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_68efc D_68efc.
    stepn F_68f00 D_68f00.
    stepn F_68f04 D_68f04.
    (* [comment removed for export] *)
    stepn F_68f08 D_68f08.
    stepn F_73ac8 D_73ac8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_73acc | reflexivity | exact D_73acc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_73ad0 D_73ad0 ltac:(cond_compute).
    stepret F_73cc0 D_73cc0 (0x68f60 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_68f0c D_68f0c.
    stepLD8 F_68f10 D_68f10 (Z_to_bv 64 0x68bc0).
    stepLD8 F_68f14 D_68f14 code.
    stepn F_68f18 D_68f18. sp_renorm.
    stepret F_68f1c D_68f1c (0x68bc0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_68b6c D_68b6c (Z_to_bv 64 0).
    stepb_ft F_68b70 D_68b70 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_68b74 D_68b74.
    stepLD8 F_68b78 D_68b78 (Z_to_bv 64 0).
    stepb_tk F_68b7c D_68b7c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_68bd0 D_68bd0.
    stepLD8 F_68bd4 D_68bd4 (Z_to_bv 64 0x79ec8).
    stepb_ft F_68bd8 D_68bd8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_68bdc D_68bdc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_68be0 D_68be0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_68bec D_68bec (Z_to_bv 64 wp).
    stepLD8 F_68bf0 D_68bf0 (Z_to_bv 64 wb).
    stepb_ft F_68bf4 D_68bf4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_68bf8 D_68bf8 (Z_to_bv 64 0x69010).
    stepn F_68bfc D_68bfc.
    stepn F_68c00 D_68c00.
    stepn F_68c04 D_68c04.
    stepjr F_68c08 D_68c08 (Z_to_bv 64 0x69010) ltac:(gres; reflexivity). vnorm.
    pu_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x79ec8 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65e54)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x79ec8 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x79ec8 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x79ec0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x79dd8)) ->
  file_clean mem 0x79dd8 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x68c60 : word) mem rom)
                 (mkst regs' (0x65bc0 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof using.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_68c0c D_68c0c rp1.
    stepLD8 F_68c10 D_68c10 rp1.
    stepb_tk F_68c14 D_68c14 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_68c2c D_68c2c.
    stepLD8 F_68c30 D_68c30 (Z_to_bv 64 0x79dd8).
    stepb_ft F_68c34 D_68c34 ltac:(cond_compute).
    stepLD F_68c38 D_68c38 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_68c3c D_68c3c ltac:(cond_compute).
    stepLD8 F_68c48 D_68c48 wp2.
    stepLD8 F_68c4c D_68c4c wp2.
    stepb_tk F_68c50 D_68c50 ltac:(apply c_eq_refl).
    stepLD8 F_68c68 D_68c68 rp2.
    stepLD8 F_68c6c D_68c6c rp2.
    stepb_tk F_68c70 D_68c70 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_68cf0 D_68cf0 (Z_to_bv 64 0x65e54).
    stepLD8 F_68cf4 D_68cf4 code.
    stepn F_68cf8 D_68cf8. rewrite Hsp. sp_renorm.
    stepret F_68cfc D_68cfc (0x65e54 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_65e00 D_65e00.
    stepn F_65e04 D_65e04.
    stepn F_65b64 D_65b64.
    stepn F_65b68 D_65b68.
    pu_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbExit_run3.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbStdioWrite_run1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
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
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.


Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof using. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
  v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof using. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
  v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof using. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof using. intros. unfold v_add. u_norm. reflexivity. Qed.

Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
  v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof using.
  intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
  rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
  pose proof (Z_lxor_range a b Ha Hb) as Hr.
  rewrite u_Z2bv by lia.
  destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof using.
  intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
  rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof using.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof using.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof using.
  intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
  destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof using. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
  v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof using.
  intros a H. unfold v_and. u_norm.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  f_equal. apply Z.mod_small. lia.
Qed.

Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof using.
  intros a b H H2. unfold v_subw. u_norm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (can : word) (wb n : Z) (s l : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (su - 8))  (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (su - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 s4))
    (Z_to_bv 64 (su - 56)) (word_to_le_bytes 8 s5))
    (Z_to_bv 64 (su - 64)) (word_to_le_bytes 8 s6))
    (Z_to_bv 64 (su - 72)) (word_to_le_bytes 8 can))
    (Z_to_bv 64 (su - 104)) (word_to_le_bytes 8 (Z_to_bv 64 wb)))
    (Z_to_bv 64 (su - 96)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (Z_to_bv 64 (su - 88)) (word_to_le_bytes 8 s))
    (Z_to_bv 64 (su - 80)) (word_to_le_bytes 8 l).

Lemma sw_enter : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x69010 : word) mem rom)
      (mkst regs' (0x69098 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 104)
    /\ getr regs' 12 = Z_to_bv 64 2
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
    /\ getr regs' 21 = Z_to_bv 64 0xaae00
    /\ getr regs' 22 = Z_to_bv 64 (wp - wb + bv_unsigned l)
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof using.
  intros regs mem rom su f wb wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WBP WPhi SMALL.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_68fbc D_68fbc. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_68fc0 D_68fc0 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_68fc4 D_68fc4 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_68fc8 D_68fc8 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_68fcc D_68fcc (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_68fd0 D_68fd0 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_68fd4 D_68fd4 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_68fd8 D_68fd8 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_68fdc D_68fdc (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_68fe0 D_68fe0. rewrite Ha2.
    stepn F_68fe4 D_68fe4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_68fe8 D_68fe8.
    stepLD8 F_68fec D_68fec (Z_to_bv 64 0xaae00).
    stepLD8 F_68ff0 D_68ff0 can.
    stepST F_68ff4 D_68ff4 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepLD8 F_68ff8 D_68ff8 (Z_to_bv 64 wp).
    stepLD8 F_68ffc D_68ffc (Z_to_bv 64 wb).
    (* [comment removed for export] *)
    stepn F_69000 D_69000. rewrite (v_sub_Z wp wb) by lia.
    stepn F_69004 D_69004.
    (* [comment removed for export] *)
    stepST F_69008 D_69008 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
    stepST F_6900c D_6900c (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
    stepST F_69010 D_69010 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_69014 D_69014 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_69018 D_69018. rewrite (v_add_Z (wp - wb) l) by lia.
    stepn F_6901c D_6901c. rewrite (sltu0_xor_ne wp wb) by lia.
    (* [comment removed for export] *)
    stepb_ft F_69020 D_69020 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_69024 D_69024.
    replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepn F_69028 D_69028.
    (* [comment removed for export] *)
    stepLD F_69030 D_69030 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_69034 D_69034.
    stepn F_69038 D_69038.
    stepn F_6903c D_6903c.
    stepn F_69040 D_69040.
    pu_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_enter_eq : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  sw_file mem f wp wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  (0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x69010 : word) mem rom)
      (mkst regs' (0x69098 : word)
         (mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                  (getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
    /\ getr regs' 17 = Z_to_bv 64 66
    /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (su - 88)
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 2 = Z_to_bv 64 (su - 112)
    /\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
    /\ getr regs' 21 = Z_to_bv 64 0xaae00
    /\ getr regs' 22 = l
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof using.
  intros regs mem rom su f wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WPhi SMALL.
  pose proof (u64_range l) as Hl.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_68fbc D_68fbc. rewrite Hsp. sp_renorm.
    stepST F_68fc0 D_68fc0 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_68fc4 D_68fc4 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_68fc8 D_68fc8 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_68fcc D_68fcc (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_68fd0 D_68fd0 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_68fd4 D_68fd4 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_68fd8 D_68fd8 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_68fdc D_68fdc (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    stepn F_68fe0 D_68fe0. rewrite Ha2.
    stepn F_68fe4 D_68fe4. rewrite Ha0.
    stepn F_68fe8 D_68fe8.
    stepLD8 F_68fec D_68fec (Z_to_bv 64 0xaae00).
    stepLD8 F_68ff0 D_68ff0 can.
    stepST F_68ff4 D_68ff4 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    stepLD8 F_68ff8 D_68ff8 (Z_to_bv 64 wp).
    stepLD8 F_68ffc D_68ffc (Z_to_bv 64 wp).
    stepn F_69000 D_69000. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
    stepn F_69004 D_69004.
    stepST F_69008 D_69008 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
    stepST F_6900c D_6900c (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
    stepST F_69010 D_69010 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_69014 D_69014 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    stepn F_69018 D_69018.
    stepn F_6901c D_6901c. rewrite sltu0_xor_eq.
    (* [comment removed for export] *)
    stepb_tk F_69020 D_69020 ltac:(apply c_eq_refl).
    stepn F_6902c D_6902c.
    replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepLD F_69030 D_69030 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_69034 D_69034.
    stepn F_69038 D_69038.
    stepn F_6903c D_6903c.
    stepn F_69040 D_69040.
    pu_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbStdioWrite_run1.
Module UbStdioWrite_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs UbStdioWrite_run1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
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
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
  /\ getr regs' 21 = getr regs 21
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
  /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
  /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x6909c : word) mem rom) (mkst regs' (0x690a4 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof using.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_69048 D_69048.
    stepn F_65f54 D_65f54.
    stepn F_65f58 D_65f58.
    stepb_tk F_65f5c D_65f5c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_65f88 D_65f88 (0x690a0 : word) ltac:(bveq).
    stepb_ft F_6904c D_6904c ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    pu_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0x6909c : word) mem rom) (mkst regs' (0x69130 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof using.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_69048 D_69048.
    stepn F_65f54 D_65f54.
    stepn F_65f58 D_65f58.
    stepb_tk F_65f5c D_65f5c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_65f88 D_65f88 (0x690a0 : word) ltac:(bveq).
    stepb_tk F_6904c D_6904c ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    pu_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x69124 : word) mem rom) (mkst regs' (0x690a4 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof using.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_690d0 D_690d0.
    stepn F_65f54 D_65f54.
    stepn F_65f58 D_65f58.
    stepb_tk F_65f5c D_65f5c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_65f88 D_65f88 (0x69128 : word) ltac:(bveq).
    stepn F_690d4 D_690d4.
    stepb_tk F_690d8 D_690d8 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    pu_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0x69124 : word) mem rom) (mkst regs' (0x69130 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof using.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_690d0 D_690d0.
    stepn F_65f54 D_65f54.
    stepn F_65f58 D_65f58.
    stepb_tk F_65f5c D_65f5c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_65f88 D_65f88 (0x69128 : word) ltac:(bveq).
    stepn F_690d4 D_690d4.
    stepb_ft F_690d8 D_690d8 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    pu_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  (su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
  (1 <= ic <= 2)%Z ->
  (1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
  (bv_unsigned b0 + n0 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x69130 : word) mem rom)
      (mkst regs' (0x69120 : word)
        (wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
                (Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
    /\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof using.
  intros regs mem rom su f fd io ic cnt n0 rem b0
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
  pose proof (u64_range b0) as Hb0.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_690dc D_690dc ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_690e0 D_690e0 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_690e4 D_690e4. rewrite Ha0, (sltu_ge n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_690e8 D_690e8.
    stepn F_690ec D_690ec. rewrite Hs3.
    (* [comment removed for export] *)
    stepLD8 F_690f0 D_690f0 b0.
    (* [comment removed for export] *)
    stepn F_690f4 D_690f4.
    stepn F_690f8 D_690f8. rewrite v_and_0_l.
    stepn F_690fc D_690fc. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_69100 D_69100. rewrite (v_add_wZ b0 cnt) by lia.
    (* [comment removed for export] *)
    stepST F_69104 D_69104 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_tk F_69108 D_69108 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    stepn F_690a0 D_690a0.
    stepn F_690a4 D_690a4.
    stepn F_690a8 D_690a8. rewrite Hs3, (v_add_ZZ' io 8) by lia.
    (* [comment removed for export] *)
    stepLD8 F_690ac D_690ac (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_690b0 D_690b0. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_690b4 D_690b4 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_690b8 D_690b8. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_690bc D_690bc. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_690c0 D_690c0 (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_690c4 D_690c4.
    stepn F_690c8 D_690c8.
    pu_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.


(* [comment removed for export] *)
Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  (su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
  (0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
  (bv_unsigned b1 + n1 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x69130 : word) mem rom)
      (mkst regs' (0x69120 : word)
        (wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
                (Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof using.
  intros regs mem rom su f fd io cnt n0 n1 rem b1
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
  pose proof (u64_range b1) as Hb1.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_690dc D_690dc ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_690e0 D_690e0 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_690e4 D_690e4. rewrite Ha0, (sltu_lt n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_690e8 D_690e8.
    stepn F_690ec D_690ec. rewrite Hs3, (v_add_ZZ' io 16) by lia.
    (* [comment removed for export] *)
    stepLD8 F_690f0 D_690f0 b1.
    (* [comment removed for export] *)
    stepn F_690f4 D_690f4.
    stepn F_690f8 D_690f8. rewrite (v_and_m1_l n0) by lia.
    stepn F_690fc D_690fc. rewrite Ha0, (v_sub_Z cnt n0) by lia.
    (* [comment removed for export] *)
    stepn F_69100 D_69100. rewrite (v_add_wZ b1 (cnt - n0)) by lia.
    (* [comment removed for export] *)
    stepST F_69104 D_69104 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_ft F_69108 D_69108 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepn F_6910c D_6910c.
    stepn F_69110 D_69110.
    stepn F_690a4 D_690a4.
    stepn F_690a8 D_690a8. rewrite Hs3, (v_add_ZZ' io 24) by lia.
    (* [comment removed for export] *)
    stepLD8 F_690ac D_690ac (Z_to_bv 64 n1).
    (* [comment removed for export] *)
    stepn F_690b0 D_690b0. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_690b4 D_690b4 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_690b8 D_690b8. rewrite Hs2. vals_lit.
    (* [comment removed for export] *)
    stepn F_690bc D_690bc. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_690c0 D_690c0 (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_690c4 D_690c4.
    stepn F_690c8 D_690c8.
    pu_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
  wbytes (wbytes (wbytes mem1
    (Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
    (Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
    (Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
  getr regs 2 = Z_to_bv 64 (su - 112) ->
  getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
  getr regs 21 = Z_to_bv 64 0xaae00 ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  ret_ok ret ->
  rdn RSEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 0xaae00) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
  exists regs',
    msteps RSEGS (mkst regs (0x690a4 : word) mem rom)
                 (mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
    /\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof using.
  intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
         Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
         M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
  unfold mem_sw2. eexists. split.
  - (* [comment removed for export] *)
    stepLD F_69050 D_69050 (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_69054 D_69054 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_69058 D_69058.
    (* [comment removed for export] *)
    stepST F_6905c D_6905c (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_69060 D_69060 (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_69064 D_69064 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
    (* [comment removed for export] *)
    stepn F_69068 D_69068. rewrite Hs0.
    stepLD F_6906c D_6906c (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_69070 D_69070 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_69074 D_69074 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD F_69078 D_69078 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_6907c D_6907c (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_69080 D_69080 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_69084 D_69084 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_69088 D_69088 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_6908c D_6908c (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_69090 D_69090 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_69094 D_69094 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_69098 D_69098. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_6909c D_6909c ret ltac:(reflexivity).
    pu_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbStdioWrite_run2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbStdioWrite.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.LibWritev OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs UbStdioWrite_run1 UbStdioWrite_run2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac u_norm ::= pu_u_norm.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.
Variable R : shape_rel RSEGS.

Lemma sr_emit_nil0 : forall c K, R c K -> R c (t_emit [] K).
Proof using.
  intros c K H. eapply (sr_conseq RSEGS R); [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (sr_nonempty RSEGS R _ _ H).
Qed.

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof using.
  intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof using.
  intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
  bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
  \/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof using.
  intros b k Hk Hle. unfold at_. pose proof (u64_range b).
  destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
  - right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
  - left. u_norm. reflexivity.
Qed.

Section Loop.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variable model : Model.
  Variable K : TSet.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0x79000 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0xaae00)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : K [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xaae00) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  (* [comment removed for export] *)
  Definition LM (m : word -> option byte) : Prop :=
    (forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

  (* [comment removed for export] *)
  Hypothesis HK : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = e8 -> getr regs' 9 = e9 ->
     getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
     getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
     getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
     getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
     LM m ->
     R (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K.

  (* [comment removed for export] *)
  Definition RI (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
    /\ getr regs 21 = Z_to_bv 64 0xaae00 /\ getr regs 3 = g3 /\ getr regs 4 = g4
    /\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
    /\ getr regs 26 = g26 /\ getr regs 27 = g27.

  Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof using.
    intros regs regs' (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
           (P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
    unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
  Qed.

  Lemma LM_refl : LM mem1.
  Proof using. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma LM_rdn : forall m (a : word) n bs,
    LM m -> rdn RSEGS mem1 a n = Some bs ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    (bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
    rdn RSEGS m a n = Some bs.
  Proof using.
    intros m a n bs [E G] H Hnw D.
    rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
    intros x Hx. apply E. lia.
  Qed.

  Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
  Proof using. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

  Lemma LM_wbytes8 : forall m (a : Z) (v : word),
    LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
    LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof using SUhi SUlo.
    intros m a v [E G] Hlo Hhi. split.
    - intros x Hx. rewrite wbytes_outside.
      + apply E, Hx.
      + unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      + rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  Qed.

  (* [comment removed for export] *)
  Lemma finish : forall regs m,
    RI regs -> LM m ->
    R (mkCfg (mkst regs (0x690a4 : word) m (seg_rom RSEGS)) model) K.
  Proof using HK Mbsz Mbuf Mcan M72 M64 M56 M48 M40 M32 M24 M16 M8 Hret Hlazy Hh Fhi Flo SUhi SUlo e22 e21 e20 e19 e18 e9 e8 ret can bufsz bufp.
    intros regs m RIr LMm.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
      as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
      try assumption.
    all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
    eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    apply HK; try assumption.
    - rewrite Q23; exact R23.
    - rewrite Q24; exact R24.
    - rewrite Q25; exact R25.
    - rewrite Q26; exact R26.
    - rewrite Q27; exact R27.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
  Qed.

  Lemma finish_nil : forall regs m,
    RI regs -> LM m ->
    R (mkCfg (mkst regs (0x690a4 : word) m (seg_rom RSEGS)) model) (t_emit [] K).
  Proof using HK Mbsz Mbuf Mcan M72 M64 M56 M48 M40 M32 M24 M16 M8 Hret Hlazy Hh Fhi Flo SUhi SUlo e22 e21 e20 e19 e18 e9 e8 ret can bufsz bufp. intros. apply sr_emit_nil0. apply finish; assumption. Qed.


  (* [comment removed for export] *)
  Lemma pc_690d0 : v_addi (0x69120 : word) 4 = (0x69124 : word).
  Proof using. apply bv_eq; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma loop1 : forall n regs m (k : nat) (b : word) (bs : list byte),
    (length bs <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
    getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
    (1 <= k < length bs)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
    rdn RSEGS mem1 b (length bs) = Some bs ->
    (bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
    (bv_unsigned b + Z.of_nat (length bs) <= 0x800000000000)%Z ->
    (0 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= 2 ^ 30)%Z ->
    R (mkCfg (mkst regs (0x69130 : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
  Proof using HK Mfd Mbsz Mbuf Mcan M72 M64 M56 M48 M40 M32 M24 M16 M8 SOK1 HKnil Hret Hlazy Hh Hfd FD Fhi Flo SUhi SUlo e22 e21 e20 e19 e18 e9 e8 ret can bufsz bufp.
    induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW MAX M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.
    (* [comment removed for export] *)
    destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
    set (m' := wbytes (wbytes m _ _) _ _).
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    (* [comment removed for export] *)
    eapply (sr_writev1_wall RSEGS R regs1 (0x69120 : word) m' model W_690cc fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
      [ exact F_690cc | exact E_690cc | exact Hh | exact Hlazy | exact Hfd | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - u_norm; unfold TASK_SIZE; lia.
    - u_norm; unfold TASK_SIZE; lia.
    - u_norm. lia.
    - u_norm. lia.
    - u_norm. lia.
    - (* [comment removed for export] *)
      intros k' K1 K2. rewrite pc_690d0. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + (* [comment removed for export] *)
        destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil; [| exact LMm'].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + (* [comment removed for export] *)
        destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
        * rewrite length_skipn. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma loop2 : forall n regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
    (length bs0 + length bs1 <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
    (1 <= k < length bs0 + length bs1)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
    rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
    rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
    rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= 0x800000000000)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= 0x800000000000)%Z ->
    (0 <= Z.of_nat (length bs0) + Z.of_nat (length bs1))%Z ->
    (Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 30)%Z ->
    R (mkCfg (mkst regs (0x69130 : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
  Proof using HK Mfd Mbsz Mbuf Mcan M72 M64 M56 M48 M40 M32 M24 M16 M8 SOK1 HKnil Hret Hlazy Hh Hfd FD Fhi Flo SUhi SUlo e22 e21 e20 e19 e18 e9 e8 ret can bufsz bufp.
    induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 MAX M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - (* [comment removed for export] *)
      destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (sr_writev2_wall RSEGS R regs1 (0x69120 : word) m' model W_690cc fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
        [ exact F_690cc | exact E_690cc | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm; unfold TASK_SIZE; lia.
      + u_norm; unfold TASK_SIZE; lia.
      + u_norm; unfold TASK_SIZE; lia.
      + u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_690d0. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- rewrite length_skipn. lia.
          -- rewrite length_skipn. lia.
    - (* [comment removed for export] *)
      destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (sr_writev1_wall RSEGS R regs1 (0x69120 : word) m' model W_690cc fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K);
        [ exact F_690cc | exact E_690cc | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm; unfold TASK_SIZE; lia.
      + u_norm; unfold TASK_SIZE; lia.
      + u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_690d0. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (loop1 (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
          -- rewrite length_skipn. lia.
  Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen1.


Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPGen2.
Context {fx : FPState}.
Variable R : shape_rel RSEGS.


Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
  sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof using.
  intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
  constructor.
  - intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
    unfold mem_sw2. do 3 wout1.
    rewrite (E x) by lia.
    unfold mem_sw1. do 13 wout1. reflexivity.
  - unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    eapply mem_grows_trans; [|exact G].
    unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    apply mem_grows_refl.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
Qed.

Lemma pc_69048 : v_addi (0x69098 : word) 4 = (0x6909c : word).
Proof using. apply bv_eq; vm_compute; reflexivity. Qed.

Theorem ref_stdio_write_R :
  forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (0 <= Z.of_nat (length pending) + Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     R (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  R (mkCfg (mkst regs (0x69010 : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof using.
  intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hh Hlazy WBP WPhi
         LENP LENE MAX M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  (* [comment removed for export] *)
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xaae00) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  (* [comment removed for export] *)
  assert (HK' : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m ->
     R (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
  { intros. apply HK. all: try assumption.
    eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil R su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1 R su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2 R su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - (* [comment removed for export] *)
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    lazymatch goal with |- sr_rel _ _ (mkCfg (mkst _ _ ?M _) _) _ =>
      replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    + (* [comment removed for export] *)
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (sr_writev1_zero RSEGS R regs1 (0x69098 : word) mem1 model W_69044 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
        [ exact F_69044 | exact E_69044 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | u_norm; unfold TASK_SIZE; lia | unfold TASK_SIZE; lia | unfold rw_bytes_max; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      rewrite pc_69048.
      destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
      apply FIN; [|exact LM1].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + (* [comment removed for export] *)
      eapply (sr_writev1_wall RSEGS R regs1 (0x69098 : word) mem1 model W_69044 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
        [ exact F_69044 | exact E_69044 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * u_norm; unfold TASK_SIZE; lia.
      * u_norm; unfold TASK_SIZE; lia.
      * cbn [length] in LENE. lia.
      * lia.
      * lia.
      * intros k K1 K2. rewrite pc_69048.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - (* [comment removed for export] *)
    destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (sr_writev2_wall RSEGS R regs1 (0x69098 : word) mem1 model W_69044 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
      [ exact F_69044 | exact E_69044 | exact Hh | exact Hlazy | exact Hfd | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + u_norm; unfold TASK_SIZE; lia.
    + u_norm; unfold TASK_SIZE; lia.
    + u_norm; unfold TASK_SIZE; lia.
    + u_norm. lia.
    + u_norm. lia.
    + u_norm. lia.
    + intros k K1 K2. rewrite pc_69048. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply (sr_msteps RSEGS R); [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.
End FPGen2.

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.
Theorem ref_stdio_write :
  forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x79000 <= f)%Z -> (f + 232 <= 0xaae00)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (0 <= Z.of_nat (length pending) + Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     realizes RSEGS (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst regs (0x69010 : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof using.
  intros. eapply (ref_stdio_write_R (SR_realizes RSEGS)); eassumption.
Qed.
End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbStdioWrite.
Module UbExit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.LibWritev OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs UbExit_run1 UbExit_run2 UbExit_run3 UbStdioWrite_run1 UbStdioWrite_run2 UbStdioWrite OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.


Theorem ref_exit_clean :
  forall regs mem model (sp code : word) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp code wp2 rp2 ->
  file_clean mem 0x79ec8 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x65e50 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp code wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  (* [comment removed for export] *)
  destruct (w12 regs mem (seg_rom RSEGS)) as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2tp & R2gp & R2s1).
  rewrite ec_sp in R2sp. rewrite ec_s0 in R2s0.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 mem (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; assumption. }
  1:{ repeat split; assumption. }
  1:{ repeat split; assumption. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_65b6c | exact E_65b6c | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit_flush :
  forall regs mem model (sp code : word) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp code wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x65e50 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  destruct (w12 regs mem (seg_rom RSEGS)) as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2tp & R2gp & R2s1).
  rewrite ec_sp in R2sp. rewrite ec_s0 in R2s0.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w3b1 regs2 mem (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; assumption. }
  1:{ repeat split; assumption. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x68c60) with (0x68c60 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a mem sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x79ec8 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x68c60 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a; sok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_65b6c | exact E_65b6c | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x65e50 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x65e50) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x65e50) with (0x65e50 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbExit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import Ioctl.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs.UbExitBase UbStdioWrite UbExit OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation RSEGS := USEGS (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ioctl_tty_node : forall ms model x8 (fd : Z) ch,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29 ->
  ms_gpr ms 0 = Z_to_bv 64 fd -> 0 <= fd < 2 ^ 32 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel ch) ->
  tty_only_request (cmd32 (ms_gpr ms 1)) = true ->
  node_ok RSEGS (mkCfg ms model) unit (fun _ => [])
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOTTY))) model).
Proof.
  intros ms model x8 fd ch Hh Hlazy Hsvc Hx8 Hfd Hfdr Hlk Htty.
  apply (node_ret_only RSEGS ms model x8 (errno_ret ENOTTY) model []); try assumption.
  intros eff. rewrite check_syscall_ioctl by (rewrite in_sysno_si; exact Hx8).
  rewrite in_arg0_si, in_arg1_si, Hfd, fd32_small by (rewrite u64_lit by lia; lia).
  unfold check_ioctl. rewrite Hlk, Htty. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv_mod64 : forall a, Z_to_bv 64 (a mod two64) = Z_to_bv 64 a.
Proof. intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, two64. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.

(* [comment removed for export] *)
Lemma kreadZ_lit0_sound : forall E M k a (w : nat) z,
  know_ok RSEGS E M k -> kreadZ RSEGS k (ELit 0) a w = Some z ->
  (1 <= w <= 8)%nat -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 z)) /\ 0 <= z < two64.
Proof.
  intros E M k a w z HK H Hw Ha0 Ha8. unfold kreadZ in H.
  destruct (know_lookup RSEGS k (ELit 0) a w false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  assert (Hfl : flat E (SA (ELit 0) a) (Z.of_nat w)) by (unfold flat; rewrite estart_lit0; lia).
  destruct (GCL.lookup_piece RSEGS E M k (ELit 0) a w (ELit zl) hs HK ltac:(lia) HL Hfl) as (bs & Hrd & Hlen & Hbs).
  rewrite estart_lit0 in Hrd. split; [| unfold two64; apply Z.mod_pos_bound; lia].
  rewrite Hrd, <- Hbs. cbn [edenot]. do 2 f_equal. symmetry. apply Z_to_bv_mod64.
Qed.

(* [comment removed for export] *)
Lemma cells_ok_sound : forall E M k cells,
  know_ok RSEGS E M k -> DN.cells_ok RSEGS k cells = true ->
  Forall (fun c => match c with (a, w, v) => (1 <= w <= 8)%nat -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
                     rdn RSEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end) cells.
Proof.
  intros E M k cells HK. induction cells as [|[[a w] v] rest IH]; intros H; [constructor|].
  cbn [DN.cells_ok forallb] in H. apply andb_prop in H as [H1 H2]. constructor; [|exact (IH H2)].
  intros Hw Ha0 Ha8. destruct (kreadZ RSEGS k (ELit 0) a w) as [x|] eqn:Hx; [|discriminate]. apply Z.eqb_eq in H1. subst x.
  destruct (kreadZ_lit0_sound E M k a w (v mod two64) HK Hx Hw Ha0 Ha8) as [R _]. rewrite R. do 2 f_equal.
  apply Z_to_bv_mod64.
Qed.

(* [comment removed for export] *)
Lemma kimg_covers_sound : forall E M k a n,
  know_ok RSEGS E M k -> DN.kimg_covers k a n = true -> forall x, a <= x < a + n -> M (Z_to_bv 64 x) = None.
Proof.
  intros E M k a n HK H x Hx. unfold DN.kimg_covers in H. apply (proj1 (existsb_exists _ _)) in H. destruct H as (K & HK1 & HK2).
  pose proof (proj1 (Forall_forall _ _) HK K HK1) as KO.
  destruct K as [| | |lo hi| | | | | |]; try discriminate. apply andb_prop in HK2 as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [kentry_ok] in KO. destruct KO as (_ & _ & KO). apply KO. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_pristine : forall M lo hi a n bs,
  (forall x, lo <= x < hi -> M (Z_to_bv 64 x) = None) -> lo <= a -> a + Z.of_nat n <= hi -> hi < 2 ^ 64 -> 0 <= lo ->
  rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M lo hi a n bs Hpr Hlo Hhi H64 H0 Hr. rewrite <- Hr. apply rdn_ext; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hpr. lia.
Qed.

Section RC.
Context {RC : run_ceil}.
(* [comment removed for export] *)
Lemma sp_ok_sound : forall PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model fr,
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model -> DN.sp_ok cs fr = true -> 0 <= fr ->
  DN.SPLO + fr <= bv_unsigned (getr R (Z_to_bv 5 2)) <= DN.SPHI
  /\ RiscvSemantics.store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (getr R (Z_to_bv 5 2)) - fr)) (Z.to_nat fr) = true
  /\ getr R (Z_to_bv 5 2) = edenot E (reg cs 2)
  /\ (forall spb spk, split_lit (reg cs 2) = (spb, spk) -> bv_unsigned (getr R (Z_to_bv 5 2)) = bv_unsigned (edenot E spb) + spk).
Proof using.
  intros PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model fr HC H Hfr. unfold DN.sp_ok in H.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  enough (GOAL : DN.SPLO + fr <= bv_unsigned (getr R (Z_to_bv 5 2)) <= DN.SPHI
          /\ RiscvSemantics.store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (getr R (Z_to_bv 5 2)) - fr)) (Z.to_nat fr) = true
          /\ getr R (Z_to_bv 5 2) = edenot E (reg cs 2)
          /\ bv_unsigned (getr R (Z_to_bv 5 2)) = bv_unsigned (edenot E spb) + spk).
  { destruct GOAL as (G1 & G2 & G3 & G4). repeat split; try assumption; try (destruct G1; assumption).
    intros spb' spk' Hs'. injection Hs' as <- <-. exact G4. }
  destruct (xlo (kn cs) (reg cs 2)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H Hwr]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 2 HC ltac:(lia)) as R2. change (Z.of_nat 2) with 2 in R2.
  pose proof (xlo_sound RSEGS E M (kn cs) _ _ (co_know HC) Hlo) as Blo.
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ (co_know HC) Hhi) as Bhi.
  destruct (GCL.kwritable_x_sound RSEGS E M (kn cs) (kn cs) spb (spk - fr) (ELit fr) (co_know HC) (co_know HC) Hwr) as (Wst & Wlo & Whi).
  pose proof (APS.split_lit_denot E (reg cs 2) spb spk Hsq) as Hsd.
  rewrite R2. split; [lia|].
  unfold elenZ in Wst, Whi. cbn [edenot] in Wst, Whi. pose proof (u64_range (edenot E spb)) as Hu. pose proof (u64_range (edenot E (reg cs 2))) as Hu2. unfold DN.SPLO in *.
  rewrite u64_lit in Wst, Whi by lia.
  specialize (Wst (Z.to_nat fr) ltac:(lia)).
  rewrite estart_SA in Wst, Wlo, Whi. rewrite Hsd in Blo |- *.
  destruct (Z.eq_dec (bv_unsigned (edenot E spb) + spk) (2 ^ 64)) as [Heq|Hne].
  { exfalso. rewrite Heq in Blo. change (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in Blo. lia. }
  rewrite u64_lit by lia. split; [|split; reflexivity].
  replace (bv_unsigned (edenot E spb) + spk - fr) with (bv_unsigned (edenot E spb) + (spk - fr)) by lia. exact Wst.
Qed.

(* [comment removed for export] *)
Lemma sp_ok_up_sound : forall PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model fr up,
  GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model -> DN.sp_ok_up cs fr up = true -> 0 <= fr -> 0 <= up ->
  DN.SPLO + fr <= bv_unsigned (getr R (Z_to_bv 5 2)) /\ bv_unsigned (getr R (Z_to_bv 5 2)) + up <= DN.SPHI
  /\ RiscvSemantics.store_ok RSEGS M (Z_to_bv 64 (bv_unsigned (getr R (Z_to_bv 5 2)) - fr)) (Z.to_nat (fr + up)) = true
  /\ getr R (Z_to_bv 5 2) = edenot E (reg cs 2).
Proof using.
  intros PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model fr up HC H Hfr Hup. unfold DN.sp_ok_up in H.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  destruct (xlo (kn cs) (reg cs 2)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H Hwr]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 2 HC ltac:(lia)) as R2. change (Z.of_nat 2) with 2 in R2.
  pose proof (xlo_sound RSEGS E M (kn cs) _ _ (co_know HC) Hlo) as Blo.
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ (co_know HC) Hhi) as Bhi.
  destruct (GCL.kwritable_x_sound RSEGS E M (kn cs) (kn cs) spb (spk - fr) (ELit (fr + up)) (co_know HC) (co_know HC) Hwr) as (Wst & Wlo & Whi).
  pose proof (APS.split_lit_denot E (reg cs 2) spb spk Hsq) as Hsd.
  rewrite R2. split; [lia|]. split; [lia|].
  unfold elenZ in Wst, Whi. cbn [edenot] in Wst, Whi. pose proof (u64_range (edenot E spb)) as Hu. pose proof (u64_range (edenot E (reg cs 2))) as Hu2. unfold DN.SPLO, DN.SPHI in *.
  rewrite u64_lit in Wst, Whi by lia.
  specialize (Wst (Z.to_nat (fr + up)) ltac:(lia)).
  rewrite estart_SA in Wst, Wlo, Whi. rewrite Hsd in Blo |- *.
  destruct (Z.eq_dec (bv_unsigned (edenot E spb) + spk) (2 ^ 64)) as [Heq|Hne].
  { exfalso. rewrite Heq in Blo. change (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in Blo. lia. }
  rewrite u64_lit by lia. split; [|reflexivity].
  replace (bv_unsigned (edenot E spb) + spk - fr) with (bv_unsigned (edenot E spb) + (spk - fr)) by lia. exact Wst.
Qed.
End RC.


Lemma kread8e_lit0_sound : forall E M k a v,
  know_ok RSEGS E M k -> kread8e RSEGS k (ELit 0) a = Some v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros E M k a v HK H Ha0 Ha8.
  assert (Hfl : flat E (SA (ELit 0) a) 8) by (unfold flat; rewrite estart_lit0; lia).
  destruct (GCL.kread8e_piece RSEGS E M k (ELit 0) a v HK H Hfl) as (bs & Hrd & Hlen & Hbs).
  rewrite estart_lit0 in Hrd. rewrite Hrd, Hbs. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ssp_ok_sound : forall E M k,
  know_ok RSEGS E M k -> DN.ssp_ok RSEGS k = true -> exists can, ssp_cells M can.
Proof.
  intros E M k HK H. unfold DN.ssp_ok in H.
  destruct (kreadZ RSEGS k (ELit 0) DN.GOT_CANARY 8) as [g|] eqn:Hg; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) DN.CANARY) as [c|] eqn:Hc; [|discriminate]. apply Z.eqb_eq in H. subst g.
  exists (edenot E c). split.
  - exact (proj1 (kreadZ_lit0_sound E M k DN.GOT_CANARY 8 DN.CANARY HK Hg ltac:(lia) ltac:(unfold DN.GOT_CANARY; lia) ltac:(unfold DN.GOT_CANARY; lia))).
  - exact (kread8e_lit0_sound E M k DN.CANARY c HK Hc ltac:(unfold DN.CANARY; lia) ltac:(unfold DN.CANARY; lia)).
Qed.

(* [comment removed for export] *)
Lemma kbytes_lit0_sound : forall E M k n a zs,
  know_ok RSEGS E M k -> DN.kbytes RSEGS n k (ELit 0) a = Some zs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some (map (Z_to_bv 8) zs) /\ length zs = n /\ Forall (fun z => 0 <= z < 256) zs.
Proof.
  intros E M k n a zs HK H Ha0 Ha8. unfold DN.kbytes in H.
  destruct (GCL.kread_bytes_sound RSEGS E M k n (ELit 0) a zs HK H ltac:(rewrite estart_lit0; lia) ltac:(rewrite estart_lit0; lia)) as (R & L & F).
  rewrite estart_lit0 in R. auto.
Qed.

(* [comment removed for export] *)
Lemma img_stdout_lock : rdn RSEGS (fun _ => None) (Z_to_bv 64 (0x79ec8 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295)).
Proof. vm_refl_bv. Qed.
Lemma img_stdout_wpos : rdn RSEGS (fun _ => None) (Z_to_bv 64 (0x79ec8 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_stdout_wbase : rdn RSEGS (fun _ => None) (Z_to_bv 64 (0x79ec8 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_stdout_rpos : rdn RSEGS (fun _ => None) (Z_to_bv 64 (0x79ec8 + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_stdout_rend : rdn RSEGS (fun _ => None) (Z_to_bv 64 (0x79ec8 + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
Lemma set_pc_set_reg_eq : forall cs n e p,
  set_pc (set_reg cs n e) p = with_ss cs (mk_ss p (sr_upd (s_regs (a_ss cs)) n e) (kn cs) (nxt cs)).
Proof. reflexivity. Qed.

Section Sound.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Hypothesis SR_det : forall c T T', sr_rel RSEGS SR c T -> realizes RSEGS c T' -> t_eq T T'.
(* [comment removed for export] *)
Hypothesis SWINc : forall a, (DN.FILE1 <= a < DN.FILE1 + 232 \/ DN.FILE2 <= a < DN.FILE2 + 232) -> in_wins SWIN a.
(* [comment removed for export] *)
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Lemma FDS12 : forall fd, fd = 1 \/ fd = 2 -> exists ch, fd_lookup FDS0 (Z_to_bv 64 fd) = Some (FdChannel ch).
Proof using FDS2 FDS1. intros fd [-> | ->]; eexists; eassumption. Qed.

#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation cs_ok := (GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation cfg := (cfgF RSEGS).

(* [comment removed for export] *)
Theorem node_ioctl_sound :
  GPS.node1_stmtN RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ GPS.always (DN.node_ioctl RSEGS).
Proof using FDS2 FDS1 AINV_frame SWIN.
  intros cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DN.node_ioctl in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc H11]. apply andb_prop in Hc as [Hsys H10].
  unfold DN.at_sys in Hsys. apply andb_prop in Hsys as [Hec H17].
  unfold DN.reg_is in H17, H10, H11.
  destruct (reg_lit cs 17) as [a7|] eqn:R17; [|discriminate]. apply Z.eqb_eq in H17. subst a7.
  destruct (reg_lit cs 11) as [rq|] eqn:R11; [|discriminate]. apply Z.eqb_eq in H11. subst rq.
  destruct (reg_lit cs 10) as [fd|] eqn:R10; [|discriminate].
  assert (Hfd12 : fd = 1 \/ fd = 2).
  { apply orb_prop in H10 as [H|H]; apply Z.eqb_eq in H; lia. }
  destruct (GPS.is_ecall_at_sound RSEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 17 29 HC ltac:(lia) R17) as [G17 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 fd HC ltac:(lia) R10) as [G10 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 0x5413 HC ltac:(lia) R11) as [G11 _].
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11.
  (* [comment removed for export] *)
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17)).
  (* [comment removed for export] *)
  destruct (FDS12 fd Hfd12) as [ch He].
  eapply (sr_silent1 RSEGS SR).
  { eapply (ioctl_tty_node _ model (getr R 17) fd ch); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | | | lia | |].
    - rewrite G17. apply u64_lit. lia.
    - rewrite ms_gpr_epend0. exact G10.
    - rewrite (co_fds HC). exact He.
    - rewrite ms_gpr_epend1, G11. vm_compute. reflexivity. }
  (* [comment removed for export] *)
  rewrite adv_set_epend. rewrite v_addi_pc4 by (unfold two64 in *; lia).
  specialize (Hk E fx (regupd R 10 (errno_ret ENOTTY)) M model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
  rewrite set_pc_set_reg_eq in Hk. unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc.
  apply Hk; [|reflexivity].
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV);
    [exact HC | | reflexivity | exact (co_know HC) | exact (co_fx HC) | intros a Ha; exfalso; exact (Ha eq_refl)].
  cbn [mk_ss s_regs].
  apply (regs_ok_set_n E (s_regs (a_ss cs)) R 10 (ELit (two64 - 25)) (errno_ret ENOTTY) (co_regs HC) ltac:(lia)).
  cbn [edenot]. apply bv_eq. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fetch_exit_ecall : fetch_word RSEGS (Z_to_bv 64 DN.P_EXIT_ECALL) = Some (Z_to_bv 32 0x73).
Proof using. vm_compute. reflexivity. Qed.

Lemma wtlb1_0 : word_to_le_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof using. reflexivity. Qed.

(* [comment removed for export] *)
Lemma set_pc_set_reg2_eq : forall cs n1 e1 n2 e2 p,
  set_pc (set_reg (set_reg cs n1 e1) n2 e2) p = with_ss cs (mk_ss p (sr_upd (sr_upd (s_regs (a_ss cs)) n1 e1) n2 e2) (kn cs) (nxt cs)).
Proof using. reflexivity. Qed.

Lemma exit_succ_ok : forall E cs fx R M model,
  cs_ok E cs fx R M model -> length (s_regs (a_ss cs)) = 32%nat ->
  cs_ok E (DN.exit_succ cs) fx (regupd (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) (Z_to_bv 5 17) (Z_to_bv 64 94)) M model.
Proof using AINV_frame SWIN.
  intros E cs fx R M model HC Hlen. unfold DN.exit_succ. rewrite set_pc_set_reg2_eq.
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV);
    [exact HC | | reflexivity | exact (co_know HC) | exact (co_fx HC) | intros a Ha; exfalso; exact (Ha eq_refl)].
  cbn [mk_ss s_regs].
  apply (regs_ok_set_n E (sr_upd (s_regs (a_ss cs)) 10 (reg cs 8)) (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) 17 (ELit 94) (Z_to_bv 64 94)); [| lia | reflexivity].
  apply (regs_ok_set_n E (s_regs (a_ss cs)) R 10 (reg cs 8) (getr R (Z_to_bv 5 8)) (co_regs HC) ltac:(lia)).
  symmetry. exact (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 8 HC ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma stdout_pending_sound : forall E M k zs,
  know_ok RSEGS E M k -> DN.stdout_pending RSEGS k = Some zs ->
  Forall (fun z => 0 <= z < 256) zs /\
  ( (zs = [] /\ exists wp1 rp1, file_clean M 0x79ec8 wp1 rp1)
    \/ (exists wb wp bufp bufsz rp1 can, stdout_pending M wb wp bufp bufsz rp1 can (map (Z_to_bv 8) zs)) ).
Proof using.
  intros E M k zs HK H. unfold DN.stdout_pending in H.
  destruct (DN.kimg_covers k DN.FILE1 232) eqn:Himg.
  { injection H as <-. split; [constructor|]. left. split; [reflexivity|].
    pose proof (kimg_covers_sound E M k DN.FILE1 232 HK Himg) as PR. unfold DN.FILE1 in PR.
    exists (Z_to_bv 64 0), (Z_to_bv 64 0). unfold file_clean.
    repeat split; (eapply (rdn_pristine M 0x79ec8 (0x79ec8 + 232)); [exact PR | lia | cbn; lia | lia | lia | ]);
      [exact img_stdout_lock | exact img_stdout_wpos | exact img_stdout_wbase | exact img_stdout_rpos | exact img_stdout_rend]. }
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 140) 4) as [lock|] eqn:Hlock; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 72) 8) as [wr|] eqn:Hwr; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 120) 4) as [fd|] eqn:Hfd; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 88) 8) as [buf|] eqn:Hbuf; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 96) 8) as [bsz|] eqn:Hbsz; [|discriminate].
  match type of H with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in H.
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 56) 8) as [wb|] eqn:Hwb; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 40) 8) as [wp|] eqn:Hwp; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 8) 8) as [rp|] eqn:Hrp; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (DN.FILE1 + 16) 8) as [re|] eqn:Hre; [|discriminate].
  match type of H with (if negb ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end. cbn [negb] in H.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  rename X into Ebsz. rename X0 into Ebuf. rename X1 into Efd. rename X2 into Ewr.
  apply Z.eqb_eq in Hc. apply Z.eqb_eq in Ewr. apply Z.eqb_eq in Efd. apply Z.eqb_eq in Ebuf. apply Z.eqb_eq in Ebsz. subst lock wr fd buf bsz.
  repeat match type of Hc2 with (_ && _)%bool = true => apply andb_prop in Hc2 as [Hc2 ?X] end.
  rename X into Wmax. rename X0 into W3. rename X1 into W2. rename X2 into W1.
  apply Z.eqb_eq in Hc2. apply Z.leb_le in W1. apply Z.leb_le in W2. apply Z.leb_le in W3. apply Z.leb_le in Wmax. subst re.
  unfold DN.FILE1, DN.SBUF, DN.SBUF_SZ, DN.P_STDIO_WRITE, DN.RW_MAX in *.
  pose proof (fun a w z H Hw Ha Ha8 => proj1 (kreadZ_lit0_sound E M k a w z HK H Hw Ha Ha8)) as RD.
  specialize (RD _ _ _ Hlock ltac:(lia) ltac:(lia) ltac:(lia)) as Rlock.
  specialize (RD _ _ _ Hwr ltac:(lia) ltac:(lia) ltac:(lia)) as Rwr.
  specialize (RD _ _ _ Hfd ltac:(lia) ltac:(lia) ltac:(lia)) as Rfd.
  specialize (RD _ _ _ Hbuf ltac:(lia) ltac:(lia) ltac:(lia)) as Rbuf.
  specialize (RD _ _ _ Hbsz ltac:(lia) ltac:(lia) ltac:(lia)) as Rbsz.
  specialize (RD _ _ _ Hwb ltac:(lia) ltac:(lia) ltac:(lia)) as Rwb.
  specialize (RD _ _ _ Hwp ltac:(lia) ltac:(lia) ltac:(lia)) as Rwp.
  specialize (RD _ _ _ Hrp ltac:(lia) ltac:(lia) ltac:(lia)) as Rrp.
  specialize (RD _ _ _ Hre ltac:(lia) ltac:(lia) ltac:(lia)) as Rre.
  destruct (Z.eqb wb wp) eqn:Hwbwp.
  - (* [comment removed for export] *)
    injection H as <-. apply Z.eqb_eq in Hwbwp. subst wp. split; [constructor|]. left. split; [reflexivity|].
    exists (Z_to_bv 64 wb), (Z_to_bv 64 rp). unfold file_clean. repeat split; assumption.
  - destruct (DN.ssp_ok RSEGS k) eqn:Hssp; [|discriminate].
    apply Z.eqb_neq in Hwbwp.
    destruct (kbytes_lit0_sound E M k _ wb zs HK H ltac:(lia) ltac:(lia)) as (Rzs & Lzs & Fzs).
    destruct (ssp_ok_sound E M k HK Hssp) as [can Hcan].
    split; [exact Fzs|]. right.
    exists wb, wp, (Z_to_bv 64 0xab268), (Z_to_bv 64 1024), (Z_to_bv 64 rp), can.
    constructor; try assumption.
    + lia.
    + rewrite length_map. lia.
    + rewrite length_map. unfold rw_bytes_max. lia.
    + rewrite length_map, Lzs. replace (Z.to_nat (wp - wb)) with (length zs) in Rzs by lia. rewrite <- Lzs. 
      rewrite Lzs. rewrite <- Lzs at 1. exact Rzs.
Qed.

Theorem node_exit_sound : forall cs fd ps cs' E fx R M model T,
  cs_ok E cs fx R M model -> DN.node_exit RSEGS cs = Some (fd, ps, cs') -> T [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Proof using FDS1 SR_det AINV_frame SWIN.
  intros cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN.node_exit in Hn.
  destruct (Z.eqb (pc cs) DN.P_EXIT) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 8) as [code|] eqn:R8; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:R4; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 40)) as [w2|] eqn:Hw2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 56)) as [b2|] eqn:Hb2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 8)) as [r2|] eqn:Hr2; [|discriminate].
  destruct (kread8e RSEGS (kn cs) (ELit 0) (DN.FILE2 + 16)) as [e2|] eqn:He2; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN.stdout_pending RSEGS (kn cs)) as [zs|] eqn:Hpend; [|discriminate].
  injection Hn as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hcells]. apply andb_prop in Hc as [Htp Hspok].
  apply Z.eqb_eq in Htp. subst tp. apply Nat.eqb_eq in Hlen.
  apply andb_prop in Hc2 as [E1 E2]. apply expr_eqb_eq in E1. apply expr_eqb_eq in E2. subst b2 e2.
  (* [comment removed for export] *)
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 8 code HC ltac:(lia) R8) as [G8 Hcode].
  change (Z.of_nat 8) with 8 in G8.
  destruct (sp_ok_up_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN.FR_EXIT DN.UP_EXIT HC Hspok ltac:(unfold DN.FR_EXIT; lia) ltac:(unfold DN.UP_EXIT; lia)) as (Hsplo & Hsphi & Hst & _).
  (* [comment removed for export] *)
  pose proof (cells_ok_sound E M (kn cs) DN.exit_cells (co_know HC) Hcells) as CE. unfold DN.exit_cells, DN.FILE1, DN.FILE2 in CE.
  repeat match type of CE with Forall _ (_ :: _) => apply Forall_cons_iff in CE as [?X CE] end. clear CE.
  repeat match goal with X : (1 <= ?w <= 8)%nat -> 0 <= ?a -> ?a + _ <= 2 ^ 64 -> _ |- _ => specialize (X ltac:((first [ (clear SWINc; lia) | lia ])) ltac:((first [ (clear SWINc; lia) | lia ])) ltac:((first [ (clear SWINc; lia) | lia ]))) end.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) Hw2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Rw2.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) Hb2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Rb2.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) Hr2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Rr2.
  pose proof (kread8e_lit0_sound E M (kn cs) _ _ (co_know HC) He2 ltac:(unfold DN.FILE2; lia) ltac:(unfold DN.FILE2; lia)) as Re2.
  destruct (stdout_pending_sound E M (kn cs) zs (co_know HC) Hpend) as [Fzs PEND].
  (* [comment removed for export] *)
  set (spn := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  pose proof (u64_range (getr R (Z_to_bv 5 2))) as Hspu.
  set (spe := Z_to_bv 64 (spn + 16)).
  assert (Hspe : bv_unsigned spe = spn + 16) by (subst spe; unfold DN.SPHI, DN.UP_EXIT in Hsphi; rewrite u64_lit by lia; reflexivity).
  (* [comment removed for export] *)
  assert (EC : exit_common R M spe (Z_to_bv 64 code) (edenot E w2) (edenot E r2)).
  { unfold DN.SPLO, DN.SPHI, DN.FR_EXIT, DN.UP_EXIT, DN.FILE2 in *.
    constructor.   (* [comment removed for export] *)
    - rewrite Hspe. replace (spn + 16 - 16) with spn by lia. subst spn. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact G8.
    - rewrite Hspe. lia.
    - rewrite Hspe. lia.
    - rewrite Hspe. replace (spn + 16 - 144) with (spn - 128) by lia. exact Hst.
    - unfold stdio_globals; repeat split; try assumption;
        (match goal with X : rdn _ _ (Z_to_bv 64 0xaae23) 1%nat = _ |- _ => rewrite X end; rewrite wtlb1_0; reflexivity).
    - unfold file_clean; repeat split; assumption. }
  assert (PRE : exit_pre R M model (Z_to_bv 64 code) (map (Z_to_bv 8) zs)).
  { exists spe, (edenot E w2), (edenot E r2).
    split; [exact EC|]. split; [exact (co_halt HC)|]. split; [exact (co_lazy HC)|].
    destruct PEND as [[-> CL] | PD]; [left; split; [reflexivity | exact CL] | right].
    destruct PD as (wb & wp & bufp & bufsz & rp1 & can & PD). exists wb, wp, bufp, bufsz, rp1, can.
    split; [exact PD | rewrite (co_fds HC); exact FDS1]. }
  (* [comment removed for export] *)
  set (R' := regupd (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) (Z_to_bv 5 17) (Z_to_bv 64 94)).
  assert (G17 : getr R' (Z_to_bv 5 17) = Z_to_bv 64 94) by (unfold R'; apply getr_same; intro; discriminate).
  assert (G10' : getr R' (Z_to_bv 5 10) = Z_to_bv 64 code).
  { unfold R'. transitivity (getr (regupd R (Z_to_bv 5 10) (getr R (Z_to_bv 5 8))) (Z_to_bv 5 10)).
    - unfold getr. rewrite regupd_other by (intro; discriminate). reflexivity.
    - rewrite getr_same by (intro; discriminate). exact G8. }
  pose proof (Hk E fx R' M model (conj (env_agree_refl _ _) (env_agree_refl _ _)) (exit_succ_ok E cs fx R M model HC Hlen) eq_refl) as HKT.
  unfold cfgF in HKT. cbn [pc DN.exit_succ set_pc set_reg with_ss a_ss mk_ss s_pc] in HKT.
  pose proof (LibWritevF.rz_exit_at (fx:=fx) RSEGS R' (Z_to_bv 64 DN.P_EXIT_ECALL) M (seg_rom RSEGS) model (Z_to_bv 32 0x73) (Z_to_bv 64 code)
                fetch_exit_ecall eq_refl (co_halt HC) (co_lazy HC) (or_introl G17) G10') as RX.
  unfold mkstF in HKT. pose proof (SR_det _ _ _ HKT RX) as TEQ.
  (* [comment removed for export] *)
  unfold cfgF, mkstF. rewrite Hpc.
  eapply (sr_conseq RSEGS SR); [apply (sr_of_realizes RSEGS SR); apply (ref_exit_Z (fx:=fx) R M model (Z_to_bv 64 code) (map (Z_to_bv 8) zs) PRE)|].
  assert (HW : Spec4.W 1 (map (Z_to_bv 8) zs) = Wp E 1 match zs with [] => [] | _ :: _ => [SPLit zs] end).
  { unfold Spec4.W, Wp. destruct zs; [reflexivity|]. cbn [flat_map piece_den]. rewrite app_nil_r. reflexivity. }
  rewrite HW. apply Spec4.AgentLib.t_emit_congr. apply t_eq_sym. exact TEQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_nth_seq : forall {A} (l : list A) (d : A), map (fun j => nth j l d) (seq 0 (length l)) = l.
Proof using.
  intros A l d. induction l as [|x l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. exact IH.
Qed.

(* [comment removed for export] *)
Lemma file_lits_sound : forall E M k f fd buf bsz wb wp,
  know_ok RSEGS E M k -> DN.file_lits RSEGS k f = Some (fd, buf, bsz, wb, wp) -> 0 <= f -> f + 232 <= 2 ^ 64 ->
  sw_file M f wb wp fd (Z_to_bv 64 buf) (Z_to_bv 64 bsz) /\ 0 <= fd < two64 /\ 0 <= wb < two64 /\ 0 <= wp < two64 /\ 0 <= buf < two64 /\ 0 <= bsz < two64.
Proof using.
  intros E M k f fd buf bsz wb wp HK H Hf0 Hf8. unfold DN.file_lits in H.
  destruct (kreadZ RSEGS k (ELit 0) (f + 120) 4) as [x1|] eqn:H1; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 88) 8) as [x2|] eqn:H2; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 96) 8) as [x3|] eqn:H3; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 56) 8) as [x4|] eqn:H4; [|discriminate].
  destruct (kreadZ RSEGS k (ELit 0) (f + 40) 8) as [x5|] eqn:H5; [|discriminate].
  injection H as <- <- <- <- <-.
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H1 ltac:(lia) ltac:(lia) ltac:(lia)) as [R1 B1].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H2 ltac:(lia) ltac:(lia) ltac:(lia)) as [R2 B2].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H3 ltac:(lia) ltac:(lia) ltac:(lia)) as [R3 B3].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H4 ltac:(lia) ltac:(lia) ltac:(lia)) as [R4 B4].
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H5 ltac:(lia) ltac:(lia) ltac:(lia)) as [R5 B5].
  split; [constructor; assumption | repeat split; lia].
Qed.

(* [comment removed for export] *)
Lemma range_pieces_sound : forall E M k (se le : expr) sb sk ext,
  know_ok RSEGS E M k -> DN.range_pieces RSEGS k se le = Some ext -> split_lit se = (sb, sk) ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + bv_unsigned (edenot E le) <= 2 ^ 64 -> estart E (SA sb sk) < 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 (estart E (SA sb sk))) (length (flat_map (piece_den E) ext)) = Some (flat_map (piece_den E) ext)
  /\ Z.of_nat (length (flat_map (piece_den E) ext)) = bv_unsigned (edenot E le).
Proof using.
  intros E M k se le sb sk ext HK H Hsq Hlo Hhi H64. unfold DN.range_pieces in H. rewrite Hsq in H.
  destruct (lit_of le) as [m|] eqn:Hm.
  - destruct le as [z| | | | | | |]; try discriminate. cbn [lit_of] in Hm. injection Hm as <-.
    assert (Hul : bv_unsigned (edenot E (ELit z)) = z mod two64).
    { cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. }
    pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as Hzr.
    destruct (z mod two64) as [|pm|nm] eqn:Hz.
    + injection H as <-. cbn [flat_map length Z.of_nat]. split; [reflexivity | lia].
    + destruct (Z.ltb 4096 (Z.pos pm)); [discriminate|].
      destruct (DN.kbytes RSEGS (Z.to_nat (Z.pos pm)) k sb sk) as [bs|] eqn:Hb; [|discriminate]. injection H as <-.
      unfold DN.kbytes in Hb.
      destruct (GCL.kread_bytes_sound RSEGS E M k _ sb sk bs HK Hb Hlo ltac:(lia)) as (R & L & _).
      cbn [flat_map piece_den]. rewrite app_nil_r, length_map, L. split; [exact R | lia].
    + lia.
  - destruct (List.find _ k) as [K|] eqn:HF; [|discriminate].
    apply find_some in HF as [HinK HK2].
    destruct K as [| |[kb ko] kl j| | | | | | |]; try discriminate. injection H as <-.
    apply andb_prop in HK2 as [HK2 El]. apply andb_prop in HK2 as [Eb Eo].
    apply expr_eqb_eq in Eb. apply Z.eqb_eq in Eo. apply expr_eqb_eq in El. subst kb ko kl.
    pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KO. cbn [kentry_ok] in KO. destruct KO as (Hfl & Hlen & Hby).
    cbn [flat_map piece_den]. rewrite app_nil_r. unfold elenZ in Hlen, Hby. split; [|lia].
    rewrite <- (map_nth_seq (eb E j) (Z_to_bv 8 0)) at 2. apply GCL.rdn_of_nth.
    + rewrite u64_lit by lia. lia.
    + intros i Hi. rewrite u64_lit by lia. apply GCL.rdn1_overlay. rewrite <- (Nat2Z.id i) at 2. apply Hby. lia.
Qed.

(* [comment removed for export] *)
Lemma know_after_sw : forall E M M' k spb spk (su f buf bsz : Z),
  know_ok RSEGS E M k ->
  bv_unsigned (edenot E spb) + spk = su -> 112 <= su -> 0 <= f -> f + 232 <= 2 ^ 64 -> 0 <= buf < two64 -> 0 <= bsz < two64 ->
  sw_post M su f (Z_to_bv 64 buf) (Z_to_bv 64 bsz) M' ->
  know_ok RSEGS E M'
    ([KWord (SA (ELit 0) (f + 32)) 8 (ELit (buf + bsz)); KWord (SA (ELit 0) (f + 40)) 8 (ELit buf); KWord (SA (ELit 0) (f + 56)) 8 (ELit buf)]
     ++ kn_havoc (kn_havoc k spb (spk - DN.FR_SW) (ELit DN.FR_SW)) (ELit 0) (f + 32) (ELit 32)).
Proof using.
  intros E M M' k spb spk su f buf bsz HK Hsu Hsu112 Hf0 Hf8 Hbuf Hbsz [AG GR WE WP WB].
  apply Forall_app. split.
  - repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok]; (split; [lia|]); (split; [unfold flat; rewrite estart_lit0; lia|]);
      rewrite GCL.adenot_SA, estart_lit0; cbn [edenot].
    + rewrite WE. do 2 f_equal. apply bv_eq. rewrite (bv_add_unsigned (Z_to_bv 64 buf)). rewrite !Z_to_bv_unsigned.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). unfold two64 in *.
      rewrite (Z.mod_small buf), (Z.mod_small bsz) by lia. reflexivity.
    + exact WP.
    + exact WB.
  - set (M1 := fun x : word => if (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool then M x else M' x).
    apply (know_ok_havoc RSEGS E M1 M').
    + apply (know_ok_havoc RSEGS E M M1); [exact HK| |].
      * intros x Hx. rewrite estart_SA in Hx. unfold elenZ, DN.FR_SW in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia.
        unfold M1. destruct (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool eqn:Hc; [reflexivity|].
        apply Bool.andb_false_iff in Hc. apply AG; [lia| |]; destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc| apply Z.ltb_ge in Hc|apply Z.leb_gt in Hc| apply Z.ltb_ge in Hc]; lia.
      * intros x Hmx HM1. unfold M1 in HM1.
        destruct ((f + 32 <=? bv_unsigned x) && (bv_unsigned x <? f + 64))%bool; [exact (Hmx HM1) | exact (GR x Hmx HM1)].
    + intros x Hx. rewrite estart_lit0 in Hx. unfold elenZ in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia.
      unfold M1. destruct (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool eqn:Hc; [|reflexivity].
      apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
    + intros x HM1 Hm'. unfold M1 in HM1.
      destruct ((f + 32 <=? bv_unsigned x) && (bv_unsigned x <? f + 64))%bool; [exact (GR x HM1 Hm') | exact (HM1 Hm')].
Qed.

(* [comment removed for export] *)
Ltac in_list_solve := cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma kept_ok_intro : forall R R' : bvmap 5 word,
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
  GCL.kept_ok R R'.
Proof using.
  intros R R' H r Hr0 Hncs. pose proof (ridx_range r) as Hr.
  assert (Hz : ridx r <> 0%nat).
  { intros Hz. apply Hr0. rewrite (GCL.reg_of_ridx r _ eq_refl), Hz. apply bv_eq. reflexivity. }
  apply H. rewrite (GCL.reg_of_ridx r (ridx r) eq_refl). unfold caller_saved in Hncs.
  destruct (ridx r) as [|n]; [lia|].
  do 31 (destruct n as [|n]; [first [in_list_solve; fail | exfalso; apply Hncs; cbn [In]; (first [ (clear SWINc; lia) | lia ]) | idtac] |]); [..|(first [ (clear SWINc; lia) | lia ])];
    first [in_list_solve | exfalso; apply Hncs; cbn [In]; lia].
Qed.

Theorem node_stdio_write_sound : forall cs fd ps cs' E fx R M model T,
  cs_ok E cs fx R M model -> DN.node_stdio_write RSEGS nx0 cs = Some (fd, ps, cs') -> T [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Proof using FDS2 FDS1 SWINc UINV_agree AINV_frame SWIN.
  intros cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN.node_stdio_write in Hn.
  destruct (Z.eqb (pc cs) DN.P_STDIO_WRITE) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 10) as [f|] eqn:R10; [|discriminate].
  destruct (ret_lit cs) as [ret|] eqn:Rret; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN.file_lits RSEGS (kn cs) f) as [[[[[fdv buf] bsz] wb] wp]|] eqn:Hfl; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg2; [|discriminate] end. cbn [negb] in Hn.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsqs.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  cbv zeta in Hn.
  destruct (xhi (kn cs) (reg cs 12)) as [lh|] eqn:Hlh; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [sh|] eqn:Hsh; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg3; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN.kbytes RSEGS (Z.to_nat (wp - wb)) (kn cs) (ELit 0) wb) as [pend|] eqn:Hpend; [|discriminate].
  destruct (DN.range_pieces RSEGS (kn cs) (reg cs 11) (reg cs 12)) as [ext|] eqn:Hext; [|discriminate].
  match type of Hn with context [after_call ?a ?b ?c ?d ?e] => destruct (after_call a b c d e) as [cs1|] eqn:Hac; [|discriminate] end.
  injection Hn as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hg1 as [Hg1 Hlen]. apply andb_prop in Hg1 as [Hg1 Hfresh]. apply andb_prop in Hg1 as [Hg1 Hssp].
  apply andb_prop in Hg1 as [Hg1 Hfr]. apply andb_prop in Hg1 as [Hf12 Hspok]. apply Nat.eqb_eq in Hlen.
  apply andb_prop in Hg2 as [Hg2 Wbsz0]. apply andb_prop in Hg2 as [Hg2 Wbufhi]. apply andb_prop in Hg2 as [Hg2 Wbuflo].
  apply andb_prop in Hg2 as [Hg2 Wrng]. apply andb_prop in Hg2 as [Hg2 Wlen]. apply andb_prop in Hg2 as [Hfd Wle].
  apply Z.leb_le in Wbsz0. apply Z.leb_le in Wbufhi. apply Z.leb_le in Wbuflo. apply Z.leb_le in Wlen. apply Z.leb_le in Wle.
  apply andb_prop in Hg3 as [Hg3 Hsd]. apply andb_prop in Hg3 as [Hlok Hs47]. apply andb_prop in Hsd as [Hbflat Hdisj].
  apply Z.leb_le in Hlok. apply Z.leb_le in Hs47.
  assert (Hfdv : (fdv = 1 \/ fdv = 2) /\ (f = DN.FILE1 \/ f = DN.FILE2)).
  { apply orb_prop in Hfd as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_eq in H2; subst; tauto. }
  destruct Hfdv as [Hfdv Hf].
  assert (Hfb : 0x79000 <= f /\ f + 232 <= 0xaae00) by (unfold DN.FILE1, DN.FILE2 in Hf; lia).
  assert (Hwr : (wb = 0 /\ wp = 0) \/ (0x79000 <= wb /\ wp <= 0xac000)).
  { apply orb_prop in Wrng as [H|H]; apply andb_prop in H as [H1 H2]; [apply Z.eqb_eq in H1; apply Z.eqb_eq in H2 | apply Z.leb_le in H1; apply Z.leb_le in H2]; lia. }
  clear Hfd Wrng.
  (* [comment removed for export] *)
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 f HC ltac:(lia) R10) as [G10 _].
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)) as G11.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 12 HC ltac:(lia)) as G12.
  change (Z.of_nat 10) with 10 in G10. change (Z.of_nat 11) with 11 in G11. change (Z.of_nat 12) with 12 in G12.
  destruct (GCL.ret_lit_sound E cs R ret (co_regs HC) Rret) as (G1 & Hretok & Hretr & _).
  destruct (sp_ok_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN.FR_SW HC Hspok ltac:(unfold DN.FR_SW; lia)) as (Hsp & Hst & G2 & Hsu).
  specialize (Hsu spb spk Hsq).
  set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (file_lits_sound E M (kn cs) f fdv buf bsz wb wp (co_know HC) Hfl ltac:(lia) ltac:(lia)) as (SWF & Bfd & Bwb & Bwp & Bbuf & Bbsz).
  destruct (ssp_ok_sound E M (kn cs) (co_know HC) Hssp) as [can Hcan].
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ (co_know HC) Hlh) as Blh.
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ (co_know HC) Hsh) as Bsh.
  destruct (bflat_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) (co_know HC) Hbflat) as (Fs0 & Fsl & Fs64).
  pose proof (u_of_split E (reg cs 11) sb sk Hsqs ltac:(lia)) as Us.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) spb (spk - DN.FR_SW) (ELit DN.FR_SW) (co_know HC) Hdisj) as DISJ.
  rewrite !estart_SA in DISJ. unfold elenZ, DN.FR_SW in DISJ. cbn [edenot] in DISJ. rewrite u64_lit in DISJ by lia. rewrite estart_SA in Us.
  destruct (kbytes_lit0_sound E M (kn cs) _ wb pend (co_know HC) Hpend ltac:((first [ (clear DISJ Hf Hfdv SWINc; lia) | lia ])) ltac:(unfold two64 in *; (first [ (clear DISJ Hf Hfdv SWINc; lia) | lia ]))) as (Rpend & Lpend & Fpend).
  destruct (range_pieces_sound E M (kn cs) (reg cs 11) (reg cs 12) sb sk ext (co_know HC) Hext Hsqs Fs0 Fsl Fs64) as [Rext Lext].
  set (extra := flat_map (piece_den E) ext) in *.
  (* [comment removed for export] *)
  assert (HW : Wp E fdv ((match pend with [] => [] | _ :: _ => [SPLit pend] end) ++ ext) = map (WriteEv (Z_to_bv 64 fdv)) (map (Z_to_bv 8) pend ++ extra)).
  { unfold Wp. f_equal. rewrite flat_map_app. fold extra. destruct pend; [reflexivity|]. cbn [flat_map piece_den]. rewrite app_nil_r. reflexivity. }
  rewrite HW. unfold cfgF, mkstF. rewrite Hpc.
  replace (Z_to_bv 64 DN.P_STDIO_WRITE) with (0x69010%bv : word) by (apply bv_eq; reflexivity).
  apply (ref_stdio_write_R (fx:=fx) SR R M model su f wb wp fdv (edenot E (reg cs 11)) (edenot E (reg cs 12))
           (Z_to_bv 64 buf) (Z_to_bv 64 bsz) can (Z_to_bv 64 ret) (map (Z_to_bv 8) pend) extra T).
  all: try assumption.
  - subst su. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - unfold DN.SPLO, DN.FR_SW in Hsp. lia.
  - unfold DN.SPHI in Hsp. lia.
  - lia.
  - lia.
  - lia.
  - rewrite (co_fds HC). destruct Hfdv as [-> | ->]; [exact FDS1 | exact FDS2].
  - exact (co_halt HC).
  - exact (co_lazy HC).
  - lia.
  - lia.
  - rewrite length_map. (first [ (clear DISJ Hf Hfdv SWINc; lia) | lia ]).
  - lia.
  - rewrite length_map. unfold rw_bytes_max, DN.RW_MAX in *. lia.
  - rewrite length_map. unfold DN.RW_MAX in *. lia.
  - unfold DN.SPLO, DN.FR_SW in Hsp. lia.
  - unfold DN.FR_SW in *. lia.
  - unfold DN.SPHI in *. lia.
  - rewrite length_map, Lpend. exact Rpend.
  - rewrite estart_SA in Rext. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (reg cs 11))), Us. exact Rext.
  - (* [comment removed for export] *)
    intros regs' mem' Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    unfold after_call in Hac.
    match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hcc; [|discriminate] end.
    apply andb_prop in Hcc as [Hcc Hrvv]. apply andb_prop in Hcc as [_ Hkv]. injection Hac as Ecs1.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := GCL.ext_call E (nxt cs) regs').
    pose proof (GCL.ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
    specialize (Hk E' fx regs' mem' model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
    rewrite <- Ecs1 in Hk. unfold cfgF, mkstF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
    pose proof (GPS.cs_ok_agree RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
    assert (KEPT : GCL.kept_ok R regs').
    { apply kept_ok_intro. intros r Hr. cbn [In] in Hr.
      repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] end; [| | | | | | | | | | | | | | | destruct Hr]; try assumption.
      rewrite Q2. subst su. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC1 | | reflexivity | | exact (co_fx HC) |].
    + cbn [mk_ss s_regs]. apply (GCL.regs_after_call E _ R regs' (nxt cs) (Some (reg cs 12)) (co_regs HC) Fsr KEPT).
      split; [exact Hrvv | replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact Q10].
    + cbn [mk_ss s_know]. eapply know_ok_agree'; [exact Hag | exact Hkv |].
      apply (know_after_sw E M mem' (kn cs) spb spk su f buf bsz (co_know HC)); try assumption; try (first [ (clear Hwr Hfdv SWINc; lia) | lia ]).
      unfold DN.SPLO, DN.FR_SW in Hsp. lia.
    + intros a Ha. cbn [a_vis]. rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
      destruct POST as [AG GR _ _ _]. pose proof (u64_range a) as Hau.
      split.
      2:{ intros Hn0. apply Ha. rewrite Hn0. destruct (M a) eqn:Hma; [|reflexivity]. exfalso. exact (GR a ltac:(congruence) Hn0). }
      destruct (Z_lt_le_dec (bv_unsigned a) (su - 112)) as [Hlow|Hhigh]; [|destruct (Z_lt_le_dec (bv_unsigned a) su) as [Hin|Habove]].
      * (* [comment removed for export] *) right. right. right. apply SWINc.
        assert (~ (~ f + 32 <= bv_unsigned a < f + 48 /\ ~ f + 56 <= bv_unsigned a < f + 64)) as Hx by (intros [X1 X2]; apply Ha; apply AG; lia).
        unfold DN.FILE1, DN.FILE2 in *. (first [ (clear HW DISJ Hwr Hf Hfdv Hk Ecs1; lia) | lia ]).
      * (* [comment removed for export] *) right. right. left. rewrite <- (co_top HC).
        unfold DN.frame_ok in Hfr. rewrite Hsq in Hfr.
        assert (Hrng : estart E (SA spb (spk - DN.FR_SW)) <= bv_unsigned a < estart E (SA spb (spk - DN.FR_SW)) + elenZ E (ELit DN.FR_SW)).
        { rewrite estart_SA. unfold elenZ, DN.FR_SW in *. cbn [edenot]. rewrite u64_lit by lia. (first [ (clear Hwr Hf Hfdv; lia) | lia ]). }
        exact (proj1 (GPS.in_floor_sound RSEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - DN.FR_SW) (ELit DN.FR_SW) a (co_know HC) Hfr (co_floor HC) Hrng)).
      * exfalso. unfold DN.SPLO, DN.FR_SW, DN.FILE1, DN.FILE2 in *. apply Ha. apply AG; (first [ (clear HW DISJ Hwr Hfdv; lia) | lia ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem XNd_sound : GPS.ext_stmt RSEGS nx0 (DN.XNd RSEGS) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof using FDS2 FDS1 AINV_frame SWIN.
  intros id args cs cs' E fx R M model T HT HC Hp Hn Hk. unfold DN.XNd in Hn.
  do 63 (destruct id as [|id]; [discriminate|]).
  destruct id as [|id]; [exact (node_ioctl_sound cs cs' E fx R M model T HT HC Hp Hn Hk) | discriminate].
Qed.

Theorem XEd_sound : GPS.emit_stmt RSEGS nx0 (DN.XEd RSEGS nx0) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof using FDS2 FDS1 SWINc SR_det UINV_agree AINV_frame SWIN.
  intros id args cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN.XEd in Hn.
  do 64 (destruct id as [|id]; [discriminate|]).
  destruct id as [|id]; [exact (node_stdio_write_sound cs fd ps cs' E fx R M model T HC Hn HT Hk)|].
  destruct id as [|id]; [exact (node_exit_sound cs fd ps cs' E fx R M model T HC Hn HT Hk)|].
  discriminate.
Qed.

End Sound.
