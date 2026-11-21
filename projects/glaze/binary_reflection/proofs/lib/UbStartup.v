(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: the start-up proof and main_entry read inp and the mmap base; the rseq-sized auxv tail; AT_GID and AT_EGID from the launching gid; the initial model's vDSO state; the zero stack window from stack_window_lo; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep OSSVerify.Proofs.glaze.binary_reflection.lib.PuStepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMemset.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
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

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
    msteps SEGS (mkst regs (0x73830 : word) mem rom) (mkst regs' ret mem' rom)
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
    stepb_ft F_737dc D_737dc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_737e0 D_737e0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sv F_737e4 D_737e4 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_737e8 D_737e8.  (* [comment removed for export] *)
    stw F_737ec D_737ec (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_737f0 D_737f0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_737f4 D_737f4 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_737f8 D_737f8 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_737fc D_737fc.  (* [comment removed for export] *)
    stw F_73800 D_73800 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73804 D_73804 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_73808 D_73808 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_7380c D_7380c (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_73810 D_73810.  (* [comment removed for export] *)
    stw F_73814 D_73814 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_73818 D_73818 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_7381c D_7381c.  (* [comment removed for export] *)
    sn F_73820 D_73820.  (* [comment removed for export] *)
    sn F_73824 D_73824.  (* [comment removed for export] *)
    stepiv F_73828 D_73828 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_7382c D_7382c.  (* [comment removed for export] *)
    sn F_73830 D_73830.  (* [comment removed for export] *)
    sv F_73834 D_73834 (d).  (* [comment removed for export] *)
    sn F_73838 D_73838.  (* [comment removed for export] *)
    sn F_7383c D_7383c.  (* [comment removed for export] *)
    sn F_73840 D_73840.  (* [comment removed for export] *)
    stw F_73844 D_73844 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sv F_73848 D_73848 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_7384c D_7384c (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_73850 D_73850 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_73854 D_73854 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73858 D_73858 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_7385c D_7385c.  (* [comment removed for export] *)
    stw F_73860 D_73860 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73864 D_73864 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_73868 D_73868 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_7386c D_7386c (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73870 D_73870 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73874 D_73874 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73878 D_73878 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepiv F_7387c D_7387c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_73880 D_73880.  (* [comment removed for export] *)
    sn F_73884 D_73884.  (* [comment removed for export] *)
    sn F_73888 D_73888.  (* [comment removed for export] *)
    stw F_7388c D_7388c (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73890 D_73890 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73894 D_73894 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_73898 D_73898 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stepb_ft F_7389c D_7389c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_738a0 D_738a0.  (* [comment removed for export] *)
    sv F_738a4 D_738a4 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_738a8 D_738a8.  (* [comment removed for export] *)
    sn F_738ac D_738ac.  (* [comment removed for export] *)
    sn F_738b0 D_738b0.  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_738b4 D_738b4 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738b8 D_738b8 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738bc D_738bc (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    stw F_738c0 D_738c0 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_subG Hok HG); gupd mem HG.  (* [comment removed for export] *)
    sn F_738c4 D_738c4.  (* [comment removed for export] *)
    sv F_738c8 D_738c8 (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_738cc D_738cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_738d0 D_738d0 ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    pu_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMemset.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbStartup2.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
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
Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.
Abbreviation RENT := (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)).

Section P3.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).

  Local Notation mem0 := (wrap_mem inp mbase RPH RENT sp0 rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH RENT sp0 rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image inp mbase RPH RENT sp0 rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 rseq av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0xaae10) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof using Hva sp0. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof using Hve sp0. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof using Hhi. exact Hhi. Qed.
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal ].

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
    = Some (word_to_le_bytes 8 (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_ptr_k; first [lctx | exact Hk].
  Qed.

  Lemma rd_envp_null : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_null; lctx.
  Qed.

  Local Notation AUXW := (auxv_words (launch_auxv inp sp0 mbase) RPH RENT (in_uid inp) (in_gid inp) hw rnd
                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (only parsing).

  Lemma rd_auxv : forall J D j w, (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    assert (Hj58 : (j < 58)%nat) by (unfold auxv_count in Hj; destruct (kb_rseq (in_kernel inp)); lia).
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. eapply read_auxv_word; first [lctx | exact Hj].
  Qed.

  (** The auxv's tail: under CONFIG_RSEQ two more pairs, AT_RSEQ_FEATURE_SIZE
      (27, 28) and AT_RSEQ_ALIGN (28, 32), then AT_NULL; without it AT_NULL
      follows AT_EXECFN directly ([StackLayout.auxv_entries]). *)
  Lemma auxw_tail_rseq : rseq = true ->
    nth 52 AUXW (Z_to_bv 64 0) = Z_to_bv 64 27 /\ nth 53 AUXW (Z_to_bv 64 0) = Z_to_bv 64 28
    /\ nth 54 AUXW (Z_to_bv 64 0) = Z_to_bv 64 28 /\ nth 55 AUXW (Z_to_bv 64 0) = Z_to_bv 64 32
    /\ nth 56 AUXW (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof using.
    intros Hrs. unfold auxv_words, auxv_entries.
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)). rewrite Hrs.
    repeat split; reflexivity.
  Qed.

  Lemma auxw_tail_norseq : rseq = false -> nth 52 AUXW (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof using.
    intros Hrs. unfold auxv_words, auxv_entries.
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)). rewrite Hrs.
    reflexivity.
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
        G (mkst regs' (0x6558c : word) (CM J D) rom)) ->
    G (mkst regs (0x65580 : word) (CM J D) rom).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_65520 D_65520 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_65524 D_65524 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_65528 D_65528 ltac:(pin; cond_compute).
        pu_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      assert (Hnz : bv_unsigned (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k) <> 0%Z)
        by (eapply cat_envp_ptr_nz with (ph := RPH) (entry := RENT); first [lctx | exact Hk]).
      eapply HG.
      { ld_step F_65520 D_65520 (word_to_le_bytes 8 (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)) (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_65524 D_65524 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_65528 D_65528 ltac:(pin; apply c_eq_0_false; exact Hnz).
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
  Proof using Hhi Hve Hva Hvl Hlau.
    pose proof len_av.
    eapply argv_ptr_bounds_at; first [lctx | lia].
  Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    rewrite <- Hb.
    exact (read_argv_byte_k Sv48 SEGS inp mbase RPH RENT sp0 brk rdraw 0 j Hlau ltac:(lia) Hj).
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
    getr regs 10 = Z_to_bv 64 0xaae10 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x65650 : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x65644 : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_655e4 D_655e4 (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_655e8 D_655e8 ltac:(pin; cond_compute).
        stepb_ft F_655ec D_655ec ltac:(pin; cond_compute).
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
        { lb_step F_655e4 D_655e4 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_655e8 D_655e8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_655dc D_655dc (Z_to_bv 64 0xaae10) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_655e0 D_655e0 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          pu_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_655e4 D_655e4 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_655e8 D_655e8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_655ec D_655ec ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_655e0 D_655e0 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          pu_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr;
    [apply (rd_auxv _ _ j w); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | reflexivity] | f_equal; lia].
  (* A read in the auxv's tail, whose words depend on CONFIG_RSEQ.  THE CASE
     HYPOTHESIS IS AN ARGUMENT, and it has to be: an Ltac1 body that IS a
     [match goal] is run where the tactic VALUE is built, not on the subgoal
     the caller hands it ([val_interp] evaluates [TacMatchGoal] at once and
     delays everything else), so a [goal]-matching [rdT] inside
     [ltac:(...)] reached [eapply rdn_addr] against [ld_step]'s own [msteps]
     goal.  [p3_run]'s split names the hypothesis at every call site. *)
  Ltac rdT j w Hrs :=
    eapply rdn_addr;
    [apply (rd_auxv _ _ j w);
       [unfold auxv_count; rewrite Hrs; cbn; lia
       | first [ apply (auxw_tail_norseq Hrs)
               | destruct (auxw_tail_rseq Hrs) as (T52 & T53 & T54 & T55 & T56);
                 first [exact T52 | exact T53 | exact T54 | exact T55 | exact T56] ] ]
    | f_equal; lia].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 inp ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x65658 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0xaae20 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x65868 : word) (CM (J_aux sp0 inp mbase rdraw Jf) (D_libc sp0 inp rdraw)) rom)) ->
    G (mkst regs (0x65574 : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof using Hva Hve Hvl Hlau Hlo Hhi Hal.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_65514 D_65514.   (* [comment removed for export] *)
    ld_step F_65518 D_65518 (word_to_le_bytes 8 (Z_to_bv 64 0x8aac0)) (Z_to_bv 64 0x8aac0)
      ltac:(rd_img img_78ce8_8) ltac:(apply bytes_le_to_Z_8).
    stw F_6551c D_6551c (Z_to_bv 64 0x8aac0) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      pu_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_6552c D_6552c.   (* [comment removed for export] *)
    sn F_65530 D_65530.   (* [comment removed for export] *)
    stw F_65534 D_65534 (Z_to_bv 64 0xaae28)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    (* [comment removed for export] *)
    (* the auxv loop: [aux[t] = v] for each pair with t < 38, 26 common pairs *)
    ld_step F_65538 D_65538 (word_to_le_bytes 8 (Z_to_bv 64 33)) (Z_to_bv 64 33) ltac:(rdA 0%nat (Z_to_bv 64 33)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_6553c D_6553c ltac:(pin; cond_compute).
    sv F_65540 D_65540 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_65544 D_65544.
    sv F_65548 D_65548 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
    sn F_6554c D_6554c.
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (ehdr_w sp0 inp mbase)) (ehdr_w sp0 inp mbase) ltac:(rdA 1%nat (ehdr_w sp0 inp mbase)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 104)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 104)) (ehdr_w sp0 inp mbase) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 40)) (Z_to_bv 64 40) ltac:(rdA 2%nat (Z_to_bv 64 40)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 41)) (Z_to_bv 64 41) ltac:(rdA 4%nat (Z_to_bv 64 41)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 42)) (Z_to_bv 64 42) ltac:(rdA 6%nat (Z_to_bv 64 42)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 43)) (Z_to_bv 64 43) ltac:(rdA 8%nat (Z_to_bv 64 43)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 44)) (Z_to_bv 64 44) ltac:(rdA 10%nat (Z_to_bv 64 44)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 45)) (Z_to_bv 64 45) ltac:(rdA 12%nat (Z_to_bv 64 45)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 46)) (Z_to_bv 64 46) ltac:(rdA 14%nat (Z_to_bv 64 46)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 47)) (Z_to_bv 64 47) ltac:(rdA 16%nat (Z_to_bv 64 47)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 51)) (Z_to_bv 64 51) ltac:(rdA 18%nat (Z_to_bv 64 51)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_tk F_6555c D_6555c ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 20%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 176)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 hw) constr:(hw) ltac:(rdA 21%nat constr:(hw)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 240)) constr:(hw) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 22%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 192)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 23%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 17)) (Z_to_bv 64 17) ltac:(rdA 24%nat (Z_to_bv 64 17)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 208)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 100)) (Z_to_bv 64 100) ltac:(rdA 25%nat (Z_to_bv 64 100)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 232)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 232)) (Z_to_bv 64 100) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 26%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 224)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 27%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 28%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 240)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 29%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 30%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 256)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 31%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rdA 32%nat (Z_to_bv 64 7)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 272)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 33%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 312)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 312)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdA 34%nat (Z_to_bv 64 8)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 288)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 35%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 304)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 304)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 9)) (Z_to_bv 64 9) ltac:(rdA 36%nat (Z_to_bv 64 9)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 304)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 0x2e9f8)) (Z_to_bv 64 0x2e9f8) ltac:(rdA 37%nat (Z_to_bv 64 0x2e9f8)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 296)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 296)) (Z_to_bv 64 0x2e9f8) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 38%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 320)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 39%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 280)) (in_uid inp) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 40%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 336)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 41%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 272)) (in_uid inp) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 13)) (Z_to_bv 64 13) ltac:(rdA 42%nat (Z_to_bv 64 13)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 352)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 43%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 264)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 264)) (in_gid inp) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 14)) (Z_to_bv 64 14) ltac:(rdA 44%nat (Z_to_bv 64 14)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 368)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 45%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 256)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 256)) (in_gid inp) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 46%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 384)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 47%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 48%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 400)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 rnd) constr:(rnd) ltac:(rdA 49%nat constr:(rnd)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 168)) constr:(rnd) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdA 50%nat (Z_to_bv 64 31)) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 416)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (execfn_w inp rdraw)) (execfn_w inp rdraw) ltac:(rdA 51%nat (execfn_w inp rdraw)) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 120)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 120)) (execfn_w inp rdraw) ltac:(ok_win HJ).
    sn F_65570 D_65570.
      pu_refl. }
    (* CONFIG_RSEQ (kb_rseq (in_kernel inp), free under valid_input) adds two
       pairs before AT_NULL: both cases are walked. *)
    destruct (Sumbool.sumbool_of_bool (kb_rseq (in_kernel inp))) as [Hrs | Hrs];
      [ unfold J_aux in Hk; rewrite Hrs in Hk
      | rewrite (J_aux_norseq sp0 inp mbase rdraw Jf Hlo Hhi Hrs) in Hk ].
  { eapply HG.
    { ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 27)) (Z_to_bv 64 27) ltac:(rdT 52%nat (Z_to_bv 64 27) Hrs) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdT 53%nat (Z_to_bv 64 28) Hrs) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 152)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 152)) (Z_to_bv 64 28) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdT 54%nat (Z_to_bv 64 28) Hrs) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 448)).
    stepb_ft F_65558 D_65558 ltac:(pin; cond_compute).
    stepb_ft F_6555c D_6555c ltac:(pin; cond_compute).
    ld_step F_65560 D_65560 (word_to_le_bytes 8 (Z_to_bv 64 32)) (Z_to_bv 64 32) ltac:(rdT 55%nat (Z_to_bv 64 32) Hrs) ltac:(apply bytes_le_to_Z_8).
    sn F_65564 D_65564.
    sv F_65568 D_65568 (Z_to_bv 64 (bv_unsigned sp0 - 144)).
    stw F_6556c D_6556c (Z_to_bv 64 (bv_unsigned sp0 - 144)) (Z_to_bv 64 32) ltac:(ok_win HJ).
    sn F_65570 D_65570.
    ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdT 56%nat (Z_to_bv 64 0) Hrs) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 464)).
    stepb_tk F_65558 D_65558 ltac:(pin; cond_compute).   (* AT_NULL: the loop ends *)
    ld_step F_65574 D_65574 (word_to_le_bytes 8 hw) constr:(hw)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
    ld_step F_65578 D_65578 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_6557c D_6557c.   (* [comment removed for export] *)
    stw F_65580 D_65580 (Z_to_bv 64 0xaae88) constr:(hw) ltac:(ok_data).   (* [comment removed for export] *)
    stepb_tk F_65584 D_65584 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_6559c D_6559c (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_655a0 D_655a0 (Z_to_bv 64 0xaae50) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_655a4 D_655a4 ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
    stepb_tk F_655ac D_655ac ltac:(pin; apply c_eq_0_false; lia).
    (* [comment removed for export] *)
    sn F_655b8 D_655b8.
    ld_step F_655bc D_655bc (word_to_le_bytes 8 (Z_to_bv 64 0xaae18)) (Z_to_bv 64 0xaae18)
      ltac:(rd_img img_78cf0_8) ltac:(apply bytes_le_to_Z_8).
    sn F_655c0 D_655c0.
    ld_step F_655c4 D_655c4 (word_to_le_bytes 8 (Z_to_bv 64 0xaae10)) (Z_to_bv 64 0xaae10)
      ltac:(rd_img img_78cf8_8) ltac:(apply bytes_le_to_Z_8).
    stw F_655c8 D_655c8 (Z_to_bv 64 0xaae18) constr:(pn) ltac:(ok_data).
    sv F_655cc D_655cc (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
    stw F_655d0 D_655d0 (Z_to_bv 64 0xaae10) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
    sn F_655d4 D_655d4.   (* [comment removed for export] *)
    sn F_655d8 D_655d8.   (* [comment removed for export] *)
      pu_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_655f0 D_655f0 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_655f4 D_655f4.   (* [comment removed for export] *)
      pu_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  }
  { eapply HG.
    { ld_step F_65550 D_65550 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdT 52%nat (Z_to_bv 64 0) Hrs) ltac:(apply bytes_le_to_Z_8).
    sv F_65554 D_65554 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_tk F_65558 D_65558 ltac:(pin; cond_compute).   (* AT_NULL: the loop ends *)
    ld_step F_65574 D_65574 (word_to_le_bytes 8 hw) constr:(hw)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
    ld_step F_65578 D_65578 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_6557c D_6557c.   (* [comment removed for export] *)
    stw F_65580 D_65580 (Z_to_bv 64 0xaae88) constr:(hw) ltac:(ok_data).   (* [comment removed for export] *)
    stepb_tk F_65584 D_65584 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_6559c D_6559c (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_655a0 D_655a0 (Z_to_bv 64 0xaae50) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_655a4 D_655a4 ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
    stepb_tk F_655ac D_655ac ltac:(pin; apply c_eq_0_false; lia).
    (* [comment removed for export] *)
    sn F_655b8 D_655b8.
    ld_step F_655bc D_655bc (word_to_le_bytes 8 (Z_to_bv 64 0xaae18)) (Z_to_bv 64 0xaae18)
      ltac:(rd_img img_78cf0_8) ltac:(apply bytes_le_to_Z_8).
    sn F_655c0 D_655c0.
    ld_step F_655c4 D_655c4 (word_to_le_bytes 8 (Z_to_bv 64 0xaae10)) (Z_to_bv 64 0xaae10)
      ltac:(rd_img img_78cf8_8) ltac:(apply bytes_le_to_Z_8).
    stw F_655c8 D_655c8 (Z_to_bv 64 0xaae18) constr:(pn) ltac:(ok_data).
    sv F_655cc D_655cc (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
    stw F_655d0 D_655d0 (Z_to_bv 64 0xaae10) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
    sn F_655d4 D_655d4.   (* [comment removed for export] *)
    sn F_655d8 D_655d8.   (* [comment removed for export] *)
      pu_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_655f0 D_655f0 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_655f4 D_655f4.   (* [comment removed for export] *)
      pu_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  }
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbStartup2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Ub_code_65868_65b18 OSSVerify.Proofs.glaze.binary_reflection.lib.Ub_code_7443c_74448.
Module UbStartup3.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Ub_code_65868_65b18 OSSVerify.Proofs.glaze.binary_reflection.lib.Ub_code_7443c_74448.
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
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Abbreviation RENT := (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable rdraw : EntryDraw.
  Variable brk : word.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH RENT sp0 rdraw)) (only parsing).

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 415320 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w inp rdraw ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 699936 ->
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
getr regs' 9 = (Z_to_bv 64 699936) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 699288) ->
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
G (mkst regs' (0x658f0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) ->
G (mkst regs (0x65868 : word) (CM (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (D_libc sp0 inp rdraw)) rom).
Proof using Hhi Hlo.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_65868 D_65868 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_6586c D_6586c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 415320) ltac:(ok_win HJ).
stw F_65870 D_65870 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).
stw F_65874 D_65874 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_65878 D_65878 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 699936) ltac:(ok_win HJ).
stw F_6587c D_6587c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_65880 D_65880 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_65884 D_65884 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_65888 D_65888 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_6588c D_6588c.
sn F_65890 D_65890.
sn F_65894 D_65894.
sn F_65898 D_65898.
stepb_ft F_6589c D_6589c ltac:(pin; cond_compute).
sn F_658a0 D_658a0.
sn F_658a4 D_658a4.
sn F_658a8 D_658a8.
ld_step F_658ac D_658ac (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_658b0 D_658b0 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_658b4 D_658b4.
sn F_658b8 D_658b8.
ld_step F_658bc D_658bc (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_79fb8_4) ltac:(vm_compute; reflexivity).
ld_step F_658c0 D_658c0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_78c28_8) ltac:(apply bytes_le_to_Z_8).
sn F_658c4 D_658c4.
sn F_658c8 D_658c8.
sn F_658cc D_658cc.
sn F_658d0 D_658d0.
sn F_658d4 D_658d4.
sn F_658d8 D_658d8.
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
getr regs 9 = Z_to_bv 64 699936 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 699288 ->
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
getr regs' 9 = (Z_to_bv 64 699936) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 699288) ->
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
G (mkst regs' (0x658f0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) ->
G (mkst regs (0x658f0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
Proof using Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_658f4 D_658f4 ltac:(pin; cond_compute).
ld_step F_658dc D_658dc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_658e0 D_658e0.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 699936 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 699288 ->
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
getr regs' 9 = (Z_to_bv 64 699936) ->
getr regs' 11 = (Z_to_bv 64 699288) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x65940 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) ->
G (mkst regs (0x658f0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
Proof using Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_ft F_65918 D_65918 ltac:(pin; cond_compute).
ld_step F_6591c D_6591c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_65920 D_65920 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_ft F_658ec D_658ec ltac:(pin; cond_compute).
ld_step F_658f0 D_658f0 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_658f4 D_658f4 ltac:(pin; cond_compute).
stepb_tk F_658f8 D_658f8 ltac:(pin; cond_compute).
sn F_6590c D_6590c.
stepb_ft F_65910 D_65910 ltac:(pin; cond_compute).
sn F_65914 D_65914.
stepb_tk F_65918 D_65918 ltac:(pin; cond_compute).
sn F_65938 D_65938.
sn F_6593c D_6593c.
sn F_658e4 D_658e4.
sn F_658e8 D_658e8.
stepb_tk F_658ec D_658ec ltac:(pin; cond_compute).
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 699936 ->
getr regs 11 = Z_to_bv 64 699288 ->
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
getr regs' 4 = (Z_to_bv 64 568208) ->
getr regs' 10 = (Z_to_bv 64 699288) ->
getr regs' 11 = (Z_to_bv 64 699992) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 568000) ->
getr regs' 15 = (Z_to_bv 64 18446744073708983408) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 568008) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x65ac4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x65940 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
Proof using Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_65940 D_65940 ltac:(pin; cond_compute).
ld_step F_65978 D_65978 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_aaba8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_6597c D_6597c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_aabb8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65980 D_65980 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_aabc0_8) ltac:(apply bytes_le_to_Z_8).
sn F_65984 D_65984.
sn F_65988 D_65988.
sn F_6598c D_6598c.
sn F_65990 D_65990.
sn F_65994 D_65994.
sn F_65998 D_65998.
sn F_6599c D_6599c.
stw F_659a0 D_659a0 (Z_to_bv 64 699320) (Z_to_bv 64 0) ltac:(ok_data).
stw F_659a4 D_659a4 (Z_to_bv 64 699336) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_659a8 D_659a8 ltac:(pin; cond_compute).
sn F_659ac D_659ac.
stw F_659b0 D_659b0 (Z_to_bv 64 699328) (Z_to_bv 64 8) ltac:(ok_data).
sn F_659b4 D_659b4.
sn F_659b8 D_659b8.
sn F_659bc D_659bc.
sn F_659c0 D_659c0.
sn F_659c4 D_659c4.
sn F_659c8 D_659c8.
stw F_659cc D_659cc (Z_to_bv 64 699960) (Z_to_bv 64 224) ltac:(ok_data).
stw F_659d0 D_659d0 (Z_to_bv 64 699968) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_659d4 D_659d4 ltac:(pin; cond_compute).
sn F_65a08 D_65a08.
ld_step F_65a0c D_65a0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_aae30_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65a10 D_65a10 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_aae48_8) ltac:(apply bytes_le_to_Z_8).
sn F_65a14 D_65a14.
sn F_65a18 D_65a18.
sn F_65a1c D_65a1c.
sn F_65a20 D_65a20.
sn F_65a24 D_65a24.
sn F_65a28 D_65a28.
sn F_65a2c D_65a2c.
sn F_65a30 D_65a30.
sn F_65a34 D_65a34.
sn F_65a38 D_65a38.
sn F_65a3c D_65a3c.
stepb_tk F_65a40 D_65a40 ltac:(pin; cond_compute).
stw F_65a88 D_65a88 (Z_to_bv 64 568224) (Z_to_bv 64 0) ltac:(ok_data).
stw F_65a8c D_65a8c (Z_to_bv 64 568200) (Z_to_bv 64 568224) ltac:(ok_data).
stw F_65a90 D_65a90 (Z_to_bv 64 568008) (Z_to_bv 64 568008) ltac:(ok_data).
sn F_65a94 D_65a94.
sn F_65a98 D_65a98.
sn F_7443c D_7443c.
sn F_74440 D_74440.
stepret F_74444 D_74444 (0x65a9c : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_65a9c D_65a9c ltac:(pin; cond_compute).
stepb_ft F_65aa0 D_65aa0 ltac:(pin; cond_compute).
sn F_65aa4 D_65aa4.
stw F_65aa8 D_65aa8 (Z_to_bv 64 699936) (Z_to_bv 64 1) ltac:(ok_data).
sn F_65aac D_65aac.
sn F_65ab0 D_65ab0.
stw F_65ab4 D_65ab4 (Z_to_bv 64 568048) (Z_to_bv 64 2) ltac:(ok_data).
sn F_65ab8 D_65ab8.
sn F_65abc D_65abc.
sn F_65ac0 D_65ac0.
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 568208 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 699992 ->
getr regs 18 = Z_to_bv 64 568008 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 568208) ->
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
G (mkst regs' (0x65658 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x65ac8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof using Hhi Hlo.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_65ac8 D_65ac8.
stw F_65acc D_65acc (Z_to_bv 64 568040) tid ltac:(ok_data).
stw F_65ad0 D_65ad0 (Z_to_bv 64 568160) (Z_to_bv 64 699992) ltac:(ok_data).
stw F_65ad4 D_65ad4 (Z_to_bv 64 568128) (Z_to_bv 64 568128) ltac:(ok_data).
sn F_65ad8 D_65ad8.
ld_step F_65adc D_65adc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_aae08_8) ltac:(apply bytes_le_to_Z_8).
stw F_65ae0 D_65ae0 (Z_to_bv 64 568016) (Z_to_bv 64 568008) ltac:(ok_data).
stw F_65ae4 D_65ae4 (Z_to_bv 64 568024) (Z_to_bv 64 568008) ltac:(ok_data).
stw F_65ae8 D_65ae8 (Z_to_bv 64 568032) (Z_to_bv 64 0) ltac:(ok_data).
sn F_65aec D_65aec.
ld_step F_65af4 D_65af4 (word_to_le_bytes 8 (Z_to_bv 64 415320)) (Z_to_bv 64 415320) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65af8 D_65af8 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65afc D_65afc (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65b00 D_65b00 (word_to_le_bytes 8 (Z_to_bv 64 699936)) (Z_to_bv 64 699936) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65b04 D_65b04 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65b08 D_65b08 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_65b0c D_65b0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_65b10 D_65b10 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_65b14 D_65b14 (0x65658 : word) ltac:(pin; first [reflexivity | bveq]).
pu_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbStartup3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbStartup4.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
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
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Abbreviation RENT := (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable rdraw : EntryDraw.
  Variable brk : word.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH RENT sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof using Hhi. exact Hhi. Qed.
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal ].
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof using Hva sp0. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof using Hal Hhi Hlo Hve Hva Hvl Hlau.
    pose proof (rnd_facts SEGS Sv48 inp mbase RPH RENT sp0 brk rdraw) as RF.
    repeat (specialize (RF ltac:(first [lctx | exact Hal]))).
    destruct RF as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) n
    = Some (firstn n (skipn j (rnd_bytes rdraw))).
  Proof using Hal Hhi Hlo Hve Hva Hvl Hlau.
    intros J D j n Hjn.
    pose proof (rnd_facts SEGS Sv48 inp mbase RPH RENT sp0 brk rdraw) as RF.
    repeat (specialize (RF ltac:(first [lctx | exact Hal]))).
    destruct RF as (A & B & C & D' & E).
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

  Lemma slli_argc : v_slli (argc_w inp) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof using Hva sp0.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN inp Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 568208 ->
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
        getr regs' 4 = (Z_to_bv 64 568208) ->
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
        G (mkst regs' (0x65660 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699904) (rnd_lo4 rdraw)) (Z_to_bv 64 699908) (rnd_hi4 rdraw)) (Z_to_bv 64 699905) ([Z_to_bv 8 0])) (Z_to_bv 64 568192) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x65658 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof using Hal Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_655f8 D_655f8 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_655fc D_655fc.  (* [comment removed for export] *)
      sv F_65eec D_65eec (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_65ef0 D_65ef0 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 415328) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_65ef4 D_65ef4 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_65ef8 D_65ef8 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_65efc D_65efc.  (* [comment removed for export] *)
      ld_step F_65f00 D_65f00 (word_to_le_bytes 8 (Z_to_bv 64 699904)) (Z_to_bv 64 699904) ltac:(rd_img img_78d10_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_65f04 D_65f04.  (* [comment removed for export] *)
      sn F_65f08 D_65f08.  (* [comment removed for export] *)
      stepiv F_7325c D_7325c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_73260 D_73260 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_73370 D_73370.  (* [comment removed for export] *)
      sn F_73374 D_73374.  (* [comment removed for export] *)
      stepb_ft F_73378 D_73378 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_7337c D_7337c.  (* [comment removed for export] *)
      stepb_tk F_73380 D_73380 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_733b8 D_733b8.  (* [comment removed for export] *)
      stepb_ft F_733bc D_733bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_733c0 D_733c0 (firstn 4 (skipn 0 (rnd_bytes rdraw))) (Z_to_bv 64 (lez (rnd_lo4 rdraw))) ltac:(RD_RND 0%nat) ltac:(rewrite rnd_lo4_eq; symmetry; apply u_lez4; apply length_rnd_lo4).  (* [comment removed for export] *)
      ld_step F_733c4 D_733c4 (firstn 4 (skipn 4 (rnd_bytes rdraw))) (Z_to_bv 64 (lez (rnd_hi4 rdraw))) ltac:(RD_RND 4%nat) ltac:(rewrite rnd_hi4_eq; symmetry; apply u_lez4; apply length_rnd_hi4).  (* [comment removed for export] *)
      stw F_733c8 D_733c8 (Z_to_bv 64 699904) (LWv (rnd_lo4 rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_733cc D_733cc (Z_to_bv 64 699908) (LWv (rnd_hi4 rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv (rnd_lo4 rdraw) (length_rnd_lo4 rdraw)), (sw_bytes_LWv (rnd_hi4 rdraw) (length_rnd_hi4 rdraw)).
      sn F_733d0 D_733d0.  (* [comment removed for export] *)
      sv F_733d4 D_733d4 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_733d8 D_733d8.  (* [comment removed for export] *)
      stepb_tk F_733dc D_733dc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_7361c D_7361c.  (* [comment removed for export] *)
      stepb_ft F_73620 D_73620 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_73624 D_73624.  (* [comment removed for export] *)
      stepb_ft F_73628 D_73628 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_7362c D_7362c (0x65f60 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_65f0c D_65f0c.  (* [comment removed for export] *)
      sn F_65f28 D_65f28.  (* [comment removed for export] *)
      ld_step F_65f2c D_65f2c (word_to_le_bytes 8 (Z_to_bv 64 699904)) (Z_to_bv 64 699904) ltac:(rd_img img_78d10_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_65f30 D_65f30 (Z_to_bv 64 699905) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_65f34 D_65f34 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply canary_w_val).  (* [comment removed for export] *)
      sn F_65f38 D_65f38.  (* [comment removed for export] *)
      stw F_65f3c D_65f3c (Z_to_bv 64 568192) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_65f40 D_65f40 (word_to_le_bytes 8 (Z_to_bv 64 415328)) (Z_to_bv 64 415328) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_65f44 D_65f44 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_65f48 D_65f48 (0x65660 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 568208 ->
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
        getr regs' 4 = (Z_to_bv 64 568208) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 191300) ->
        getr regs' 11 = (argc_w inp) ->
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
        G (mkst regs' (0x65820 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699904) (rnd_lo4 rdraw)) (Z_to_bv 64 699908) (rnd_hi4 rdraw)) (Z_to_bv 64 699905) ([Z_to_bv 8 0])) (Z_to_bv 64 568192) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x65660 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699904) (rnd_lo4 rdraw)) (Z_to_bv 64 699908) (rnd_hi4 rdraw)) (Z_to_bv 64 699905) ([Z_to_bv 8 0])) (Z_to_bv 64 568192) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof using Hal Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_65600 D_65600 (word_to_le_bytes 8 uid) constr:(uid) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65604 D_65604 (word_to_le_bytes 8 uid) constr:(uid) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_65608 D_65608 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      (* AT_GID and AT_EGID carry the launching gid at 08b1429 (they were absent, so 0) *)
      ld_step F_6560c D_6560c (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65610 D_65610 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_65614 D_65614 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_65618 D_65618 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_6561c D_6561c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_656fc D_656fc (word_to_le_bytes 8 (Z_to_bv 64 415732)) (Z_to_bv 64 415732) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65700 D_65700 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65704 D_65704 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65708 D_65708 (word_to_le_bytes 8 (Z_to_bv 64 191300)) (Z_to_bv 64 191300) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6570c D_6570c (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_65710 D_65710 (0x657f4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_65794 D_65794.  (* [comment removed for export] *)
      sn F_65798 D_65798.  (* [comment removed for export] *)
      sn F_6579c D_6579c.  (* [comment removed for export] *)
      sv F_657a0 D_657a0 (argc_w inp).  (* [comment removed for export] *)
      sv F_657a4 D_657a4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_657a8 D_657a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_657ac D_657ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_657b0 D_657b0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_657b4 D_657b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_657b8 D_657b8 (sp0).  (* [comment removed for export] *)
      stepret F_657bc D_657bc (0x65820 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 568208 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 191300 ->
    getr regs 11 = argc_w inp ->
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
        getr regs' 1 = (Z_to_bv 64 415652) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 568208) ->
        getr regs' 8 = (Z_to_bv 64 482008) ->
        getr regs' 9 = (Z_to_bv 64 482000) ->
        getr regs' 18 = (Z_to_bv 64 191300) ->
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
        G (mkst regs' (0x2ea40 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415328))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 415828))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699904) (rnd_lo4 rdraw)) (Z_to_bv 64 699908) (rnd_hi4 rdraw)) (Z_to_bv 64 699905) ([Z_to_bv 8 0])) (Z_to_bv 64 568192) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x65820 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699904) (rnd_lo4 rdraw)) (Z_to_bv 64 699908) (rnd_hi4 rdraw)) (Z_to_bv 64 699905) ([Z_to_bv 8 0])) (Z_to_bv 64 568192) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof using Hal Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_657c0 D_657c0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_657c4 D_657c4 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_657c8 D_657c8 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_657cc D_657cc (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_657d0 D_657d0 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_657d4 D_657d4 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_657d8 D_657d8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_657dc D_657dc (argc_w inp).  (* [comment removed for export] *)
      sn F_657e0 D_657e0.  (* [comment removed for export] *)
      stepiv F_657e4 D_657e4 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_657e8 D_657e8 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_657ec D_657ec (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_657f0 D_657f0.  (* [comment removed for export] *)
      sv F_65714 D_65714 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_65718 D_65718 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 415828) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6571c D_6571c (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_65720 D_65720 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_65724 D_65724.  (* [comment removed for export] *)
      stepret F_654e4 D_654e4 (0x65788 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_65728 D_65728.  (* [comment removed for export] *)
      sn F_6572c D_6572c.  (* [comment removed for export] *)
      ld_step F_65730 D_65730 (word_to_le_bytes 8 (Z_to_bv 64 482008)) (Z_to_bv 64 482008) ltac:(rd_img img_78d00_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65734 D_65734 (word_to_le_bytes 8 (Z_to_bv 64 482000)) (Z_to_bv 64 482000) ltac:(rd_img img_78d08_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_65738 D_65738 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6573c D_6573c (word_to_le_bytes 8 (Z_to_bv 64 191040)) (Z_to_bv 64 191040) ltac:(rd_img img_75a80_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_65740 D_65740 (0x2ea40 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 415652 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 568208 ->
    getr regs 8 = Z_to_bv 64 482008 ->
    getr regs 9 = Z_to_bv 64 482000 ->
    getr regs 18 = Z_to_bv 64 191300 ->
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
        getr regs' 1 = (Z_to_bv 64 415844) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 568208) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 191300) ->
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
        G (mkst regs' (0x2eb44 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415328))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 415828))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 415652))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 482008))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699904) (rnd_lo4 rdraw)) (Z_to_bv 64 699908) (rnd_hi4 rdraw)) (Z_to_bv 64 699905) ([Z_to_bv 8 0])) (Z_to_bv 64 568192) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 499664) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2ea40 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 699936))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 415328))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 415828))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 699320) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699328) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 699960) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 699968) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 568224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 568200) (word_to_le_bytes 8 (Z_to_bv 64 568224))) (Z_to_bv 64 568008) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 699936) ([Z_to_bv 8 1])) (Z_to_bv 64 568048) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 568040) (word_to_le_bytes 4 tid)) (Z_to_bv 64 568160) (word_to_le_bytes 8 (Z_to_bv 64 699992))) (Z_to_bv 64 568128) (word_to_le_bytes 8 (Z_to_bv 64 568128))) (Z_to_bv 64 568016) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568024) (word_to_le_bytes 8 (Z_to_bv 64 568008))) (Z_to_bv 64 568032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 699904) (rnd_lo4 rdraw)) (Z_to_bv 64 699908) (rnd_hi4 rdraw)) (Z_to_bv 64 699905) ([Z_to_bv 8 0])) (Z_to_bv 64 568192) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof using Hal Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux27, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_2e9e0 D_2e9e0 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2e9e4 D_2e9e4 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 415652) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2e9e8 D_2e9e8 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 482008) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_2e9ec D_2e9ec (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_2e9f0 D_2e9f0.  (* [comment removed for export] *)
      sn F_2e9f4 D_2e9f4.  (* [comment removed for export] *)
      lb_step F_2e9f8 D_2e9f8 (Z_to_bv 8 0) ltac:(rd_img img_79f80_1).  (* [comment removed for export] *)
      sn F_2e9fc D_2e9fc.  (* [comment removed for export] *)
      stepb_tk F_2ea00 D_2ea00 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2ea0c D_2ea0c.  (* [comment removed for export] *)
      sn F_2ea10 D_2ea10.  (* [comment removed for export] *)
      sn F_2ea14 D_2ea14.  (* [comment removed for export] *)
      stw F_2ea18 D_2ea18 (Z_to_bv 64 499664) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2ea1c D_2ea1c.  (* [comment removed for export] *)
      ld_step F_2ea20 D_2ea20 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_78bf8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_2ea24 D_2ea24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2ea44 D_2ea44 (word_to_le_bytes 8 (Z_to_bv 64 415652)) (Z_to_bv 64 415652) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2ea48 D_2ea48 (word_to_le_bytes 8 (Z_to_bv 64 482008)) (Z_to_bv 64 482008) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2ea4c D_2ea4c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_2ea50 D_2ea50 (0x657a4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_65744 D_65744.  (* [comment removed for export] *)
      stepb_ft F_65748 D_65748 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6574c D_6574c (word_to_le_bytes 8 (Z_to_bv 64 415828)) (Z_to_bv 64 415828) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65750 D_65750 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_65754 D_65754 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_65758 D_65758 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_6575c D_6575c (0x65854 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_657f4 D_657f4 (argc_w inp).  (* [comment removed for export] *)
      sv F_657f8 D_657f8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_657fc D_657fc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_65800 D_65800 (0x2eb44 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      pu_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbStartup4.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbImgCells OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1 UbMemset UbStartup2 UbStartup3 UbStartup4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance fx0.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Abbreviation RENT := (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)).
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

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
Record main_entry (sp0 : word) (inp : ProcInput) (mbase : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x65864;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x8ab90;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN inp;
  me_a0  : getr regs 10 = argcN inp;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_s2  : getr regs 18 = Z_to_bv 64 0x2eb44;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  (* the stack frames below sp0 are only ever used through [wfJ]: what start-up
     left in them is not part of the contract *)
  me_mem : exists (J : word -> option byte),
             wfJ sp0 J
             /\ mem = cmem sp0 (wrap_mem inp mbase RPH RENT sp0 rdraw) J (D_main sp0 inp rdraw tid)
}.

Section Assembly.
  Variable R : shape_rel SEGS.
  Variable sp : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvsp : valid_sp sp.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  (* the launch's zero window under sp: [Run.stack_window_lo] up to sp *)
  Let J0 : word -> option byte := stack_zero (stack_window_lo (in_kernel inp) mbase rdraw).
  Lemma wfJ0 : wfJ sp J0.
  Proof. exact (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau). Qed.

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | exact wfJ0 | exact Hvl | exact Hlau
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       main_entry sp inp mbase rdraw tid regs mem ->
       R (mkCfg (mkst regs (0x2eb44 : word) mem (seg_rom rsegs))
                (with_tid tid (with_vdso (vdso_run_init (ed_vdso rdraw))
                                 (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    R (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config.
    set (model := with_vdso (vdso_run_init (ed_vdso rdraw))
                    (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => R (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_sr; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    assert (Epc : Z_to_bv 64 (Z.of_N Ubsan.M.init_pc) = (0x2e9f8 : word)) by (apply bv_eq; reflexivity).
    rewrite Epc at 1.
    rewrite (cmem_init _ _ _ _ _ _ _ Hlau). fold (regs_init sp). fold J0.
    (* [comment removed for export] *)
    destruct (p1_run sp inp mbase brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom SEGS) J0 wfJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply (sr_msteps SEGS R); [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x65574 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH RENT sp rdraw) (J1 sp inp J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x65574 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact wfJ0 | region_side | region_side]. }
    eapply (sr_msteps SEGS R); [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (R (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp inp mbase brk rdraw) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; exact wfJ0. }
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
    change (J1 sp inp J0) with (J_lsm sp inp J0).
    eapply (tls_c1 sp J0 inp mbase rdraw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 inp mbase rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 inp mbase rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 inp mbase rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (sr_set_tid R regs4 (0x65ac4 : word) _ (seg_rom SEGS) model K Ub_code_65868_65b18.W_65ac4);
      [exact Hh | exact Hlazy | exact Ht0 | exact Ub_code_65868_65b18.F_65ac4 | exact Ub_code_65868_65b18.E_65ac4 | assumption |].
    intros tid Htid.
    replace (v_addi (0x65ac4 : word) 4) with (0x65ac8 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => R (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_sr; [exact Hh' | exact Hlazy']).
    change (R (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 inp mbase rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 inp mbase rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 inp mbase rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 inp mbase rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 inp mbase rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists. split; [| unfold D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB; reflexivity].
      unfold J_tls, J_aux, J_aux27, J_lsm, aux_base. repeat apply wfJ_wbytes. exact wfJ0.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall (R : shape_rel SEGS) sp brk mbase (rdraw : EntryDraw) lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp inp mbase rdraw tid regs mem ->
     R (mkCfg (mkst regs (0x2eb44 : word) mem (seg_rom rsegs))
              (with_tid tid (with_vdso (vdso_run_init (ed_vdso rdraw))
                               (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  R (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros R sp brk mbase rdraw lim inp K Hsp Hva Hve Hvl Hlau HK.
  exact (ref_startup_sec R sp inp mbase brk rdraw Hva Hve Hsp Hvl Hlau lim K HK).
Qed.

(* [comment removed for export] *)
Corollary ref_startup_realizes : forall sp brk mbase rdraw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp inp mbase rdraw tid regs mem ->
     realizes rsegs (mkCfg (mkst regs (0x2eb44 : word) mem (seg_rom rsegs))
                     (with_tid tid (with_vdso (vdso_run_init (ed_vdso rdraw))
                                      (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof. intros. apply (ref_startup (SR_realizes SEGS)); assumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH RENT sp0 rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem inp mbase RPH RENT sp0 rdraw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (wok_lo sp0 <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    rewrite cmem_at_win by (unfold in_win; lia). apply HJ. unfold in_win. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply store_ok_cmem_win; [exact HJ | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 inp rdraw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 inp rdraw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & HJ & ->).
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
