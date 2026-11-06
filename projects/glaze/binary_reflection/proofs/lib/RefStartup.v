(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep OSSVerify.Proofs.glaze.binary_reflection.lib.PuStepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefMemset.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep OSSVerify.Proofs.glaze.binary_reflection.lib.PuStepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac push_store ::= pu_push_storeP.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof using. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof using. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ok_subG Hok HG :=
  eapply store_ok_sub; [ | exact (store_ok_mono _ _ _ _ _ HG Hok) | | ]; rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.
Ltac gupd m0 HG :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ ?M _) _ =>
      let HG' := fresh "HG" in
      assert (HG' : mem_grows m0 M) by (eapply mem_grows_trans; [exact HG | apply wbytes_grows]);
      clear HG; rename HG' into HG
  end.
Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0x6f1c0 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof using.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  assert (HG : mem_grows mem mem) by apply mem_grows_refl.
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_6f16c D_6f16c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f170 D_6f170 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sv F_6f174 D_6f174 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_6f178 D_6f178.  (* [comment removed for export] *)
    stw F_6f17c D_6f17c (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_6f180 D_6f180 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f184 D_6f184 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f188 D_6f188 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f18c D_6f18c.  (* [comment removed for export] *)
    stw F_6f190 D_6f190 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f194 D_6f194 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_6f198 D_6f198 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f19c D_6f19c (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f1a0 D_6f1a0.  (* [comment removed for export] *)
    stw F_6f1a4 D_6f1a4 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_6f1a8 D_6f1a8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_6f1ac D_6f1ac.  (* [comment removed for export] *)
    sn F_6f1b0 D_6f1b0.  (* [comment removed for export] *)
    sn F_6f1b4 D_6f1b4.  (* [comment removed for export] *)
    stepiv F_6f1b8 D_6f1b8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_6f1bc D_6f1bc.  (* [comment removed for export] *)
    sn F_6f1c0 D_6f1c0.  (* [comment removed for export] *)
    sv F_6f1c4 D_6f1c4 (d).  (* [comment removed for export] *)
    sn F_6f1c8 D_6f1c8.  (* [comment removed for export] *)
    sn F_6f1cc D_6f1cc.  (* [comment removed for export] *)
    sn F_6f1d0 D_6f1d0.  (* [comment removed for export] *)
    stw F_6f1d4 D_6f1d4 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sv F_6f1d8 D_6f1d8 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_6f1dc D_6f1dc (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_6f1e0 D_6f1e0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f1e4 D_6f1e4 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f1e8 D_6f1e8 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f1ec D_6f1ec.  (* [comment removed for export] *)
    stw F_6f1f0 D_6f1f0 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f1f4 D_6f1f4 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_6f1f8 D_6f1f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f1fc D_6f1fc (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f200 D_6f200 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f204 D_6f204 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f208 D_6f208 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepiv F_6f20c D_6f20c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_6f210 D_6f210.  (* [comment removed for export] *)
    sn F_6f214 D_6f214.  (* [comment removed for export] *)
    sn F_6f218 D_6f218.  (* [comment removed for export] *)
    stw F_6f21c D_6f21c (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f220 D_6f220 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f224 D_6f224 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f228 D_6f228 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_6f22c D_6f22c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_6f230 D_6f230.  (* [comment removed for export] *)
    sv F_6f234 D_6f234 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_6f238 D_6f238.  (* [comment removed for export] *)
    sn F_6f23c D_6f23c.  (* [comment removed for export] *)
    sn F_6f240 D_6f240.  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_6f244 D_6f244 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f248 D_6f248 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f24c D_6f24c (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_6f250 D_6f250 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_6f254 D_6f254.  (* [comment removed for export] *)
    sv F_6f258 D_6f258 (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_6f25c D_6f25c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_6f260 D_6f260 ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    pu_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefMemset.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefStartup2.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0.
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.PuPeel.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep OSSVerify.Proofs.glaze.binary_reflection.lib.PuStepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm3.   (* [comment removed for export] *)
#[local] Ltac push_store ::= pu_push_store.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac peel ::= pu_peel.
#[local] Ltac SumsLib.StartupTac.addr_norm ::= addr_norm_fast.
#[local] Existing Instance fx0.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.

Section P3.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0xa67a0) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof using Hva sp0. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof using Hve sp0. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof using Hhi. exact Hhi. Qed.

  Lemma bsb_len : (Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) <= 2240000)%Z.
  Proof using Hve Hva. exact (bsb_bound RPH sp0 av ev uid hw rdraw Hva Hve). Qed.

  (* [comment removed for export] *)
  Lemma rd_above : forall J D (a : Z) n bs,
    (bv_unsigned sp0 <= a)%Z -> (a + Z.of_nat n < 2^64)%Z ->
    rdn SEGS stk (Z_to_bv 64 a) n = Some bs ->
    rdn SEGS (CM J D) (Z_to_bv 64 a) n = Some bs.
  Proof using Hlo.
    intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
    rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). exact H.
  Qed.

  Lemma rd_envp : forall J D k, (k < length ev)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)).
  Proof using Hhi Hlo Hve Hva.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_ptr_k SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' k Hk).
  Qed.

  Lemma rd_envp_null : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof using Hhi Hlo Hve Hva.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_null SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi').
  Qed.

  Lemma rd_auxv : forall J D j w, (j < 20)%nat ->
    nth j (auxv_words RPH rnd uid hw) (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof using Hhi Hlo Hve Hva.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. exact (read_auxv_word SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' j Hj).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma envp_loop : forall G, bwd SEGS G -> forall n k regs J D rom,
    (k + n = length ev)%nat ->
    getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
    (forall regs',
        getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [9; 10]%list) regs regs' ->
        G (mkst regs' (0x60f1c : word) (CM J D) rom)) ->
    G (mkst regs (0x60f10 : word) (CM J D) rom).
  Proof using Hhi Hlo Hve Hva.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_60eb0 D_60eb0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_60eb4 D_60eb4 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_60eb8 D_60eb8 ltac:(pin; cond_compute).
        pu_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      pose proof (cat_envp_ptr_nz RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
      eapply HG.
      { ld_step F_60eb0 D_60eb0 (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_60eb4 D_60eb4 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_60eb8 D_60eb8 ltac:(pin; apply c_eq_0_false; exact Hnz).
        pu_refl. }
      eapply (IH (S k)); [lia | gres; reflexivity |].
      intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
      eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pn_bounds :
    (bv_unsigned sp0 <= bv_unsigned pn)%Z
    /\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
  Proof using Hhi Hve Hva.
    pose proof len_av.
    exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hsp_hi' 0 ltac:(lia)).
  Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
  Proof using Hhi Hlo Hve Hva.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    rewrite <- Hb.
    exact (read_argv_byte_k RPH SEGS sp0 av ev 0 j uid hw rdraw ltac:(lia) Hj
             (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve Hsp_hi')).
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof using. intros; subst; reflexivity. Qed.

  Lemma c_eq_byte47 : forall b : byte,
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 47) = bv_eqb b (Z_to_bv 8 47).
  Proof using sp0.
    intros b. pose proof (u8_range b). unfold c_eq, bv_eqb.
    rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  Lemma c_eq_byte0 : forall b : byte, b <> Z_to_bv 8 0 ->
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false.
  Proof using sp0.
    intros b Hb. pose proof (u8_range b). apply c_eq_0_false. rewrite u_Z2bv by lia.
    intro Hz. apply Hb. apply bv_eq. rewrite Hz. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0xa67a0 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x60fe0 : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x60fd4 : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof using Hhi Hlo Hve Hva.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_60f74 D_60f74 (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_60f78 D_60f78 ltac:(pin; cond_compute).
        stepb_ft F_60f7c D_60f7c ltac:(pin; cond_compute).
        pu_refl. }
      apply Hk0; [gres; pin; f_equal; lia | solve_regs_agree].
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b).
      { rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : b <> Z_to_bv 8 0).
      { intros Hb0. apply Hnz. rewrite <- Hb0, <- Hb, app_nth1 by lia. apply nth_In. lia. }
      assert (Hskip' : skipn (S j) s = l2).
      { replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
      cbn [after_last_slash] in Hk0.
      destruct (bv_eqb b (Z_to_bv 8 47)) eqn:Eb.
      + (* [comment removed for export] *)
        eapply HG.
        { lb_step F_60f74 D_60f74 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_60f78 D_60f78 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_60f6c D_60f6c (Z_to_bv 64 0xa67a0) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_60f70 D_60f70 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          pu_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_60f74 D_60f74 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_60f78 D_60f78 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_60f7c D_60f7c ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_60f70 D_60f70 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          pu_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 av ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x60fe8 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0xa67b0 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x611f8 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x60f04 : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof using Hhi Hlo Hve Hva.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_60ea4 D_60ea4.   (* [comment removed for export] *)
    ld_step F_60ea8 D_60ea8 (word_to_le_bytes 8 (Z_to_bv 64 0x86450)) (Z_to_bv 64 0x86450)
      ltac:(rd_img img_74678_8) ltac:(apply bytes_le_to_Z_8).
    stw F_60eac D_60eac (Z_to_bv 64 0x86450) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      pu_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_60ebc D_60ebc.   (* [comment removed for export] *)
    sn F_60ec0 D_60ec0.   (* [comment removed for export] *)
    stw F_60ec4 D_60ec4 (Z_to_bv 64 0xa67b8)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    (* [comment removed for export] *)
    ld_step F_60ec8 D_60ec8 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_60ecc D_60ecc ltac:(pin; cond_compute).
    sv F_60ed0 D_60ed0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_60ed4 D_60ed4.   (* [comment removed for export] *)
    sv F_60ed8 D_60ed8 (Z_to_bv 64 (bv_unsigned sp0 - 368)).  (* [comment removed for export] *)
    sn F_60edc D_60edc.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 344)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 336)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 328)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 240)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 320)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 280)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 272)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 184)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_60eec D_60eec ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_60ef0 D_60ef0 (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
    sn F_60ef4 D_60ef4.   (* [comment removed for export] *)
    sv F_60ef8 D_60ef8 (Z_to_bv 64 (bv_unsigned sp0 - 168)).   (* [comment removed for export] *)
    stw F_60efc D_60efc (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ).
    sn F_60f00 D_60f00.   (* [comment removed for export] *)
    ld_step F_60ee0 D_60ee0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_60ee4 D_60ee4 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_tk F_60ee8 D_60ee8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_60f04 D_60f04 (word_to_le_bytes 8 hw) hw
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
    ld_step F_60f08 D_60f08 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_60f0c D_60f0c.   (* [comment removed for export] *)
    stw F_60f10 D_60f10 (Z_to_bv 64 0xa6818) hw ltac:(ok_data).   (* [comment removed for export] *)
    stepb_tk F_60f14 D_60f14 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_60f2c D_60f2c (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_60f30 D_60f30 (Z_to_bv 64 0xa67e0) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_60f34 D_60f34 ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
    stepb_tk F_60f3c D_60f3c ltac:(pin; apply c_eq_0_false; lia).
    (* [comment removed for export] *)
    sn F_60f48 D_60f48.
    ld_step F_60f4c D_60f4c (word_to_le_bytes 8 (Z_to_bv 64 0xa67a8)) (Z_to_bv 64 0xa67a8)
      ltac:(rd_img img_74680_8) ltac:(apply bytes_le_to_Z_8).
    sn F_60f50 D_60f50.
    ld_step F_60f54 D_60f54 (word_to_le_bytes 8 (Z_to_bv 64 0xa67a0)) (Z_to_bv 64 0xa67a0)
      ltac:(rd_img img_74688_8) ltac:(apply bytes_le_to_Z_8).
    stw F_60f58 D_60f58 (Z_to_bv 64 0xa67a8) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data).
    sv F_60f5c D_60f5c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
    stw F_60f60 D_60f60 (Z_to_bv 64 0xa67a0) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
    sn F_60f64 D_60f64.   (* [comment removed for export] *)
    sn F_60f68 D_60f68.   (* [comment removed for export] *)
      pu_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_60f80 D_60f80 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_60f84 D_60f84.   (* [comment removed for export] *)
      pu_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefStartup2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Ref_code_611f8_614a8 OSSVerify.Proofs.glaze.binary_reflection.lib.Ref_code_6fdcc_6fdd8.
Module RefStartup3.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.Ref_code_611f8_614a8 OSSVerify.Proofs.glaze.binary_reflection.lib.Ref_code_6fdcc_6fdd8.
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.PuPeel.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep OSSVerify.Proofs.glaze.binary_reflection.lib.PuStepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm3.   (* [comment removed for export] *)
#[local] Ltac push_store ::= pu_push_store.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac peel ::= pu_peel.
#[local] Ltac SumsLib.StartupTac.addr_norm ::= addr_norm_fast.
#[local] Existing Instance fx0.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 397288 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 681904 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 681904) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 681256) ->
getr regs' 13 = (Z_to_bv 64 10) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65600) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x61280 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x611f8 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof using Hhi Hlo.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_611f8 D_611f8 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_611fc D_611fc (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 397288) ltac:(ok_win HJ).
stw F_61200 D_61200 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_61204 D_61204 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_61208 D_61208 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 681904) ltac:(ok_win HJ).
stw F_6120c D_6120c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_61210 D_61210 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_61214 D_61214 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_61218 D_61218 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6121c D_6121c.
sn F_61220 D_61220.
sn F_61224 D_61224.
sn F_61228 D_61228.
stepb_ft F_6122c D_6122c ltac:(pin; cond_compute).
sn F_61230 D_61230.
sn F_61234 D_61234.
sn F_61238 D_61238.
ld_step F_6123c D_6123c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_61240 D_61240 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_61244 D_61244.
sn F_61248 D_61248.
ld_step F_6124c D_6124c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_75948_4) ltac:(vm_compute; reflexivity).
ld_step F_61250 D_61250 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_745b8_8) ltac:(apply bytes_le_to_Z_8).
sn F_61254 D_61254.
sn F_61258 D_61258.
sn F_6125c D_6125c.
sn F_61260 D_61260.
sn F_61264 D_61264.
sn F_61268 D_61268.
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 681904 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 681256 ->
getr regs 13 = Z_to_bv 64 10 ->
getr regs 15 = Z_to_bv 64 65600 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65600 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 681904) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 681256) ->
getr regs' 13 = (Z_to_bv 64 5) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65880) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x61280 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x61280 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_61284 D_61284 ltac:(pin; cond_compute).
ld_step F_6126c D_6126c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_61270 D_61270.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 681904 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 681256 ->
getr regs 13 = Z_to_bv 64 5 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65880 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 681904) ->
getr regs' 11 = (Z_to_bv 64 681256) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x612d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x61280 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_ft F_612a8 D_612a8 ltac:(pin; cond_compute).
ld_step F_612ac D_612ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_612b0 D_612b0 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_ft F_6127c D_6127c ltac:(pin; cond_compute).
ld_step F_61280 D_61280 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_61284 D_61284 ltac:(pin; cond_compute).
stepb_tk F_61288 D_61288 ltac:(pin; cond_compute).
sn F_6129c D_6129c.
stepb_ft F_612a0 D_612a0 ltac:(pin; cond_compute).
sn F_612a4 D_612a4.
stepb_tk F_612a8 D_612a8 ltac:(pin; cond_compute).
sn F_612c8 D_612c8.
sn F_612cc D_612cc.
sn F_61274 D_61274.
sn F_61278 D_61278.
stepb_tk F_6127c D_6127c ltac:(pin; cond_compute).
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 681904 ->
getr regs 11 = Z_to_bv 64 681256 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 550176) ->
getr regs' 10 = (Z_to_bv 64 681256) ->
getr regs' 11 = (Z_to_bv 64 681960) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 549968) ->
getr regs' 15 = (Z_to_bv 64 18446744073709001440) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 549976) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x61454 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x612d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_612d0 D_612d0 ltac:(pin; cond_compute).
ld_step F_61308 D_61308 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_a6538_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6130c D_6130c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_a6548_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_61310 D_61310 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_a6550_8) ltac:(apply bytes_le_to_Z_8).
sn F_61314 D_61314.
sn F_61318 D_61318.
sn F_6131c D_6131c.
sn F_61320 D_61320.
sn F_61324 D_61324.
sn F_61328 D_61328.
sn F_6132c D_6132c.
stw F_61330 D_61330 (Z_to_bv 64 681288) (Z_to_bv 64 0) ltac:(ok_data).
stw F_61334 D_61334 (Z_to_bv 64 681304) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_61338 D_61338 ltac:(pin; cond_compute).
sn F_6133c D_6133c.
stw F_61340 D_61340 (Z_to_bv 64 681296) (Z_to_bv 64 8) ltac:(ok_data).
sn F_61344 D_61344.
sn F_61348 D_61348.
sn F_6134c D_6134c.
sn F_61350 D_61350.
sn F_61354 D_61354.
sn F_61358 D_61358.
stw F_6135c D_6135c (Z_to_bv 64 681928) (Z_to_bv 64 224) ltac:(ok_data).
stw F_61360 D_61360 (Z_to_bv 64 681936) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_61364 D_61364 ltac:(pin; cond_compute).
sn F_61398 D_61398.
ld_step F_6139c D_6139c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_a67c0_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_613a0 D_613a0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_a67d8_8) ltac:(apply bytes_le_to_Z_8).
sn F_613a4 D_613a4.
sn F_613a8 D_613a8.
sn F_613ac D_613ac.
sn F_613b0 D_613b0.
sn F_613b4 D_613b4.
sn F_613b8 D_613b8.
sn F_613bc D_613bc.
sn F_613c0 D_613c0.
sn F_613c4 D_613c4.
sn F_613c8 D_613c8.
sn F_613cc D_613cc.
stepb_tk F_613d0 D_613d0 ltac:(pin; cond_compute).
stw F_61418 D_61418 (Z_to_bv 64 550192) (Z_to_bv 64 0) ltac:(ok_data).
stw F_6141c D_6141c (Z_to_bv 64 550168) (Z_to_bv 64 550192) ltac:(ok_data).
stw F_61420 D_61420 (Z_to_bv 64 549976) (Z_to_bv 64 549976) ltac:(ok_data).
sn F_61424 D_61424.
sn F_61428 D_61428.
sn F_6fdcc D_6fdcc.
sn F_6fdd0 D_6fdd0.
stepret F_6fdd4 D_6fdd4 (0x6142c : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_6142c D_6142c ltac:(pin; cond_compute).
stepb_ft F_61430 D_61430 ltac:(pin; cond_compute).
sn F_61434 D_61434.
stw F_61438 D_61438 (Z_to_bv 64 681904) (Z_to_bv 64 1) ltac:(ok_data).
sn F_6143c D_6143c.
sn F_61440 D_61440.
stw F_61444 D_61444 (Z_to_bv 64 550016) (Z_to_bv 64 2) ltac:(ok_data).
sn F_61448 D_61448.
sn F_6144c D_6144c.
sn F_61450 D_61450.
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 550176 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 681960 ->
getr regs 18 = Z_to_bv 64 549976 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 550176) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x60fe8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x61458 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof using Hhi Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_61458 D_61458.
stw F_6145c D_6145c (Z_to_bv 64 550008) tid ltac:(ok_data).
stw F_61460 D_61460 (Z_to_bv 64 550128) (Z_to_bv 64 681960) ltac:(ok_data).
stw F_61464 D_61464 (Z_to_bv 64 550096) (Z_to_bv 64 550096) ltac:(ok_data).
sn F_61468 D_61468.
ld_step F_6146c D_6146c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_a6798_8) ltac:(apply bytes_le_to_Z_8).
stw F_61470 D_61470 (Z_to_bv 64 549984) (Z_to_bv 64 549976) ltac:(ok_data).
stw F_61474 D_61474 (Z_to_bv 64 549992) (Z_to_bv 64 549976) ltac:(ok_data).
stw F_61478 D_61478 (Z_to_bv 64 550000) (Z_to_bv 64 0) ltac:(ok_data).
sn F_6147c D_6147c.
ld_step F_61484 D_61484 (word_to_le_bytes 8 (Z_to_bv 64 397288)) (Z_to_bv 64 397288) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_61488 D_61488 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6148c D_6148c (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_61490 D_61490 (word_to_le_bytes 8 (Z_to_bv 64 681904)) (Z_to_bv 64 681904) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_61494 D_61494 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_61498 D_61498 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6149c D_6149c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_614a0 D_614a0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_614a4 D_614a4 (0x60fe8 : word) ltac:(pin; first [reflexivity | bveq]).
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefStartup3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefStartup4.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM2.
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.PuPeel.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep OSSVerify.Proofs.glaze.binary_reflection.lib.PuStepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm3.   (* [comment removed for export] *)
#[local] Ltac push_store ::= pu_push_store.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac peel ::= pu_peel.
#[local] Ltac SumsLib.StartupTac.addr_norm ::= addr_norm_fast.
#[local] Existing Instance fx0.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof using Hhi. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof using Hva sp0. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof using Hal Hhi Hlo Hve Hva rdraw hw uid.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (rnd_bytes rdraw))).
  Proof using Hal Hhi Hlo Hve Hva.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w, rnd_bytes. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof using. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    apply (rdn_guard_canary SEGS rdraw); lia.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof using Hva sp0.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 550176 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 550176) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x60ff0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397296))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681872) (rnd_lo4 rdraw)) (Z_to_bv 64 681876) (rnd_hi4 rdraw)) (Z_to_bv 64 681873) ([Z_to_bv 8 0])) (Z_to_bv 64 550160) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x60fe8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof using Hal Hhi Hlo Hve Hva.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_60f88 D_60f88 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_60f8c D_60f8c.  (* [comment removed for export] *)
      sv F_6187c D_6187c (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_61880 D_61880 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 397296) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_61884 D_61884 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_61888 D_61888 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_6188c D_6188c.  (* [comment removed for export] *)
      ld_step F_61890 D_61890 (word_to_le_bytes 8 (Z_to_bv 64 681872)) (Z_to_bv 64 681872) ltac:(rd_img img_746a0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_61894 D_61894.  (* [comment removed for export] *)
      sn F_61898 D_61898.  (* [comment removed for export] *)
      stepiv F_6ebec D_6ebec (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_6ebf0 D_6ebf0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_6ed00 D_6ed00.  (* [comment removed for export] *)
      sn F_6ed04 D_6ed04.  (* [comment removed for export] *)
      stepb_ft F_6ed08 D_6ed08 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_6ed0c D_6ed0c.  (* [comment removed for export] *)
      stepb_tk F_6ed10 D_6ed10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_6ed48 D_6ed48.  (* [comment removed for export] *)
      stepb_ft F_6ed4c D_6ed4c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6ed50 D_6ed50 (firstn 4 (skipn 0 (rnd_bytes rdraw))) (Z_to_bv 64 (lez (rnd_lo4 rdraw))) ltac:(RD_RND 0%nat) ltac:(rewrite rnd_lo4_eq; symmetry; apply u_lez4; apply length_rnd_lo4).  (* [comment removed for export] *)
      ld_step F_6ed54 D_6ed54 (firstn 4 (skipn 4 (rnd_bytes rdraw))) (Z_to_bv 64 (lez (rnd_hi4 rdraw))) ltac:(RD_RND 4%nat) ltac:(rewrite rnd_hi4_eq; symmetry; apply u_lez4; apply length_rnd_hi4).  (* [comment removed for export] *)
      stw F_6ed58 D_6ed58 (Z_to_bv 64 681872) (LWv (rnd_lo4 rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_6ed5c D_6ed5c (Z_to_bv 64 681876) (LWv (rnd_hi4 rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv (rnd_lo4 rdraw) (length_rnd_lo4 rdraw)), (sw_bytes_LWv (rnd_hi4 rdraw) (length_rnd_hi4 rdraw)).
      sn F_6ed60 D_6ed60.  (* [comment removed for export] *)
      sv F_6ed64 D_6ed64 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_6ed68 D_6ed68.  (* [comment removed for export] *)
      stepb_tk F_6ed6c D_6ed6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_6efac D_6efac.  (* [comment removed for export] *)
      stepb_ft F_6efb0 D_6efb0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_6efb4 D_6efb4.  (* [comment removed for export] *)
      stepb_ft F_6efb8 D_6efb8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_6efbc D_6efbc (0x618f0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6189c D_6189c.  (* [comment removed for export] *)
      sn F_618b8 D_618b8.  (* [comment removed for export] *)
      ld_step F_618bc D_618bc (word_to_le_bytes 8 (Z_to_bv 64 681872)) (Z_to_bv 64 681872) ltac:(rd_img img_746a0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_618c0 D_618c0 (Z_to_bv 64 681873) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_618c4 D_618c4 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply canary_w_val).  (* [comment removed for export] *)
      sn F_618c8 D_618c8.  (* [comment removed for export] *)
      stw F_618cc D_618cc (Z_to_bv 64 550160) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_618d0 D_618d0 (word_to_le_bytes 8 (Z_to_bv 64 397296)) (Z_to_bv 64 397296) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_618d4 D_618d4 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_618d8 D_618d8 (0x60ff0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 550176 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 0) ->
        getr regs' 2 = sp0 ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 550176) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 189324) ->
        getr regs' 11 = (argc_w av) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 18 = (Z_to_bv 64 0) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0x611b0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397296))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681872) (rnd_lo4 rdraw)) (Z_to_bv 64 681876) (rnd_hi4 rdraw)) (Z_to_bv 64 681873) ([Z_to_bv 8 0])) (Z_to_bv 64 550160) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x60ff0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397296))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681872) (rnd_lo4 rdraw)) (Z_to_bv 64 681876) (rnd_hi4 rdraw)) (Z_to_bv 64 681873) ([Z_to_bv 8 0])) (Z_to_bv 64 550160) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof using Hal Hhi Hlo Hve Hva.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_60f90 D_60f90 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_60f94 D_60f94 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_60f98 D_60f98 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_60f9c D_60f9c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_60fa0 D_60fa0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_60fa4 D_60fa4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_60fa8 D_60fa8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_60fac D_60fac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6108c D_6108c (word_to_le_bytes 8 (Z_to_bv 64 397700)) (Z_to_bv 64 397700) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_61090 D_61090 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_61094 D_61094 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_61098 D_61098 (word_to_le_bytes 8 (Z_to_bv 64 189324)) (Z_to_bv 64 189324) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6109c D_6109c (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_610a0 D_610a0 (0x61184 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_61124 D_61124.  (* [comment removed for export] *)
      sn F_61128 D_61128.  (* [comment removed for export] *)
      sn F_6112c D_6112c.  (* [comment removed for export] *)
      sv F_61130 D_61130 (argc_w av).  (* [comment removed for export] *)
      sv F_61134 D_61134 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_61138 D_61138 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6113c D_6113c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_61140 D_61140 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_61144 D_61144 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_61148 D_61148 (sp0).  (* [comment removed for export] *)
      stepret F_6114c D_6114c (0x611b0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 550176 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 189324 ->
    getr regs 11 = argc_w av ->
    getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
    getr regs 18 = Z_to_bv 64 0 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 397620) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 550176) ->
        getr regs' 8 = (Z_to_bv 64 463976) ->
        getr regs' 9 = (Z_to_bv 64 463968) ->
        getr regs' 18 = (Z_to_bv 64 189324) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0x2e288 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397296))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 397796))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681872) (rnd_lo4 rdraw)) (Z_to_bv 64 681876) (rnd_hi4 rdraw)) (Z_to_bv 64 681873) ([Z_to_bv 8 0])) (Z_to_bv 64 550160) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x611b0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397296))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681872) (rnd_lo4 rdraw)) (Z_to_bv 64 681876) (rnd_hi4 rdraw)) (Z_to_bv 64 681873) ([Z_to_bv 8 0])) (Z_to_bv 64 550160) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof using Hal Hhi Hlo Hve Hva.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_61150 D_61150 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_61154 D_61154 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_61158 D_61158 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6115c D_6115c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_61160 D_61160 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_61164 D_61164 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_61168 D_61168 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_6116c D_6116c (argc_w av).  (* [comment removed for export] *)
      sn F_61170 D_61170.  (* [comment removed for export] *)
      stepiv F_61174 D_61174 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_61178 D_61178 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_6117c D_6117c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_61180 D_61180.  (* [comment removed for export] *)
      sv F_610a4 D_610a4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_610a8 D_610a8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 397796) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_610ac D_610ac (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_610b0 D_610b0 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_610b4 D_610b4.  (* [comment removed for export] *)
      stepret F_60e74 D_60e74 (0x61118 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_610b8 D_610b8.  (* [comment removed for export] *)
      sn F_610bc D_610bc.  (* [comment removed for export] *)
      ld_step F_610c0 D_610c0 (word_to_le_bytes 8 (Z_to_bv 64 463976)) (Z_to_bv 64 463976) ltac:(rd_img img_74690_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_610c4 D_610c4 (word_to_le_bytes 8 (Z_to_bv 64 463968)) (Z_to_bv 64 463968) ltac:(rd_img img_74698_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_610c8 D_610c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_610cc D_610cc (word_to_le_bytes 8 (Z_to_bv 64 189064)) (Z_to_bv 64 189064) ltac:(rd_img img_71410_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_610d0 D_610d0 (0x2e288 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 397620 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 550176 ->
    getr regs 8 = Z_to_bv 64 463976 ->
    getr regs 9 = Z_to_bv 64 463968 ->
    getr regs 18 = Z_to_bv 64 189324 ->
    getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 397812) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 550176) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 189324) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0x2e38c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397296))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 397796))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 397620))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 463976))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681872) (rnd_lo4 rdraw)) (Z_to_bv 64 681876) (rnd_hi4 rdraw)) (Z_to_bv 64 681873) ([Z_to_bv 8 0])) (Z_to_bv 64 550160) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 481632) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2e288 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397288))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 681904))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 397296))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 397796))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 681288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681304) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681296) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 681928) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 681936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 550192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 550168) (word_to_le_bytes 8 (Z_to_bv 64 550192))) (Z_to_bv 64 549976) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 681904) ([Z_to_bv 8 1])) (Z_to_bv 64 550016) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 550008) (word_to_le_bytes 4 tid)) (Z_to_bv 64 550128) (word_to_le_bytes 8 (Z_to_bv 64 681960))) (Z_to_bv 64 550096) (word_to_le_bytes 8 (Z_to_bv 64 550096))) (Z_to_bv 64 549984) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 549992) (word_to_le_bytes 8 (Z_to_bv 64 549976))) (Z_to_bv 64 550000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 681872) (rnd_lo4 rdraw)) (Z_to_bv 64 681876) (rnd_hi4 rdraw)) (Z_to_bv 64 681873) ([Z_to_bv 8 0])) (Z_to_bv 64 550160) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof using Hal Hhi Hlo Hve Hva.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_2e228 D_2e228 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2e22c D_2e22c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 397620) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2e230 D_2e230 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 463976) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_2e234 D_2e234 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_2e238 D_2e238.  (* [comment removed for export] *)
      sn F_2e23c D_2e23c.  (* [comment removed for export] *)
      lb_step F_2e240 D_2e240 (Z_to_bv 8 0) ltac:(rd_img img_75910_1).  (* [comment removed for export] *)
      sn F_2e244 D_2e244.  (* [comment removed for export] *)
      stepb_tk F_2e248 D_2e248 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2e254 D_2e254.  (* [comment removed for export] *)
      sn F_2e258 D_2e258.  (* [comment removed for export] *)
      sn F_2e25c D_2e25c.  (* [comment removed for export] *)
      stw F_2e260 D_2e260 (Z_to_bv 64 481632) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2e264 D_2e264.  (* [comment removed for export] *)
      ld_step F_2e268 D_2e268 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_74588_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_2e26c D_2e26c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2e28c D_2e28c (word_to_le_bytes 8 (Z_to_bv 64 397620)) (Z_to_bv 64 397620) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2e290 D_2e290 (word_to_le_bytes 8 (Z_to_bv 64 463976)) (Z_to_bv 64 463976) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2e294 D_2e294 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_2e298 D_2e298 (0x61134 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_610d4 D_610d4.  (* [comment removed for export] *)
      stepb_ft F_610d8 D_610d8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_610dc D_610dc (word_to_le_bytes 8 (Z_to_bv 64 397796)) (Z_to_bv 64 397796) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_610e0 D_610e0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_610e4 D_610e4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_610e8 D_610e8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_610ec D_610ec (0x611e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_61184 D_61184 (argc_w av).  (* [comment removed for export] *)
      sv F_61188 D_61188 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_6118c D_6118c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_61190 D_61190 (0x2e38c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefStartup4.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1.RefStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.RefStartup1 RefMemset RefStartup2 RefStartup3 RefStartup4 OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM0.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance fx0.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sr_set_tid : forall (R : shape_rel SEGS) regs (pc : word) mem rom model K w,
  m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
  fetch_word SEGS pc = Some w -> is_ecall w = true ->
  getr regs 17 = Z_to_bv 64 96 ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     R (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  R (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros R regs pc mem rom model K w Hh Hlazy Htid HF HE H17 Hk.
  eapply (sr_step SEGS R); [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption |].
  apply (sr_silent_node SEGS R _ tid_I (exist _ (Z_to_bv 64 1) one_tid_ok)
           (fun i => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem rom (getr regs 17)) (proj1_sig i)))
                           (with_tid (proj1_sig i) model))).
  - apply (node_set_tid SEGS _ model (getr regs 17)); [exact Hh | exact Hlazy | reflexivity | | exact Htid].
    rewrite H17. apply u64_lit. lia.
  - intros [tid Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma bwd_sr : forall (R : shape_rel SEGS) model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd SEGS (fun st => R (mkCfg st model) K).
Proof.
  intros R model K Hh Hlazy st st' Hms Hst'. eapply (sr_msteps SEGS R); eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main (sp0 : word) (av ev : list (list byte)) (uid hw : word) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0x60fe8) (pn_w sp0 av ev) s1v (Z_to_bv 64 0xa67b0)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x60ff0)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x611e4)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x61134)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x71468)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry (sp0 : word) (av ev : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x611f4;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x86520;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x2e38c;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev uid hw s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw) J (D_main sp0 av ev hw rdraw tid)
}.

Section Assembly.
  Variable R : shape_rel SEGS.
  Variable sp : word.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall brk mbase lim inp K,
    in_argv inp = argv -> in_envp inp = envp -> in_uid inp = uid -> in_hwcap inp = hw ->
    (forall tid regs mem,
       (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       main_entry sp argv envp uid hw rdraw tid regs mem ->
       R (mkCfg (mkst regs (0x2e38c : word) mem (seg_rom rsegs))
                (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
    R (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros brk mbase lim inp K Eav Eev Euid Ehw HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. rewrite Eav, Eev, Euid, Ehw.
    set (model := init_model (segments_reserved rsegs) brk mbase sp lim inp).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => R (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_sr; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x2e240 : word) by (apply bv_eq; reflexivity).
    rewrite cmem_init. fold (regs_init sp).
    (* [comment removed for export] *)
    destruct (p1_run sp argv envp uid hw rdraw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply (sr_msteps SEGS R); [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x60f04 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp uid hw rdraw) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x60f04 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
    eapply (sr_msteps SEGS R); [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (R (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp argv envp uid hw rdraw) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
    intros regs3 C1 C2 C10 C18 G3.
    carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
    assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
        clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
    pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
    pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
    pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
    pose proof (Cz 27 ltac:(in_list)) as Z27.
    (* [comment removed for export] *)
    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 sp J0 argv envp uid hw rdraw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (sr_set_tid R regs4 (0x61454 : word) _ (seg_rom SEGS) model K Ref_code_611f8_614a8.W_61454);
      [exact Hh | exact Hlazy | exact Ht0 | exact Ref_code_611f8_614a8.F_61454 | exact Ref_code_611f8_614a8.E_61454 | assumption |].
    intros tid Htid.
    replace (v_addi (0x61454 : word) 4) with (0x61458 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => R (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_sr; [exact Hh' | exact Hlazy']).
    change (R (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall (R : shape_rel SEGS) sp brk mbase (rdraw : EntryDraw) lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     R (mkCfg (mkst regs (0x2e38c : word) mem (seg_rom rsegs))
              (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  R (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros R sp brk mbase rdraw lim inp K Hsp Hva Hve HK.
  exact (ref_startup_sec R sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw Hva Hve Hsp
           brk mbase lim inp K eq_refl eq_refl eq_refl eq_refl HK).
Qed.

(* [comment removed for export] *)
Corollary ref_startup_realizes : forall sp brk mbase rdraw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     realizes rsegs (mkCfg (mkst regs (0x2e38c : word) mem (seg_rom rsegs))
                     (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof. intros. apply (ref_startup (SR_realizes SEGS)); assumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev uid hw rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev uid hw rdraw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev hw rdraw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev hw rdraw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
