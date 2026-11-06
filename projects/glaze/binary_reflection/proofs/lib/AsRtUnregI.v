(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtUnregChk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.





End AsRtUnregChk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg AsRtUnregChk.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition asan_unreg_globs : list (Z * Z) :=
  [(0x22b20, 0x20); (0x22b40, 0x20); (0x22b60, 0x40); (0x22ba0, 0x20); (0x26980, 0x60);
   (0x269e0, 0x60); (0x26a40, 0x20); (0x26a60, 0x60); (0x26ac0, 0x40); (0x31320, 0x40)]%Z.

Definition asan_unreg_tab : unreg_tab :=
  {| ut_dtor := 0xbf028; ut_base := 0x59e48; ut_pt := asan_poison_tab;
     ut_g_start := 0xfff00; ut_g_stop := 0xfff08; ut_p_start := 0x103c20; ut_globs := asan_unreg_globs;
     ut_p_flag := 0x103ec0; ut_g_aflags := 0xff268; ut_p_aflags := 0x104d78; ut_p_mu := 0x104e30;
     ut_g_pgsz := 0xff250; ut_c_inited := 0x108258; ut_c_ro := 0x10470; ut_str := 0x1c56a |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x59e48 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).
Ltac litd a v := replace (at_ (0xbf028 : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

(* [comment removed for export] *)
Ltac gapaddi_tac Fa Da Fb Db :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  let Hx := fresh "Hx" in
  wd_eexists; split;
  [ intros regs mem rom; lit_pc;
    (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
    gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc in G in change_no_check G' end); vals_lit; close_eq
  | intros regs mem rom Hx; lit_pc;
    (chain_step; [ reflexivity | eapply step_addi; [exact Fb | reflexivity | exact Db] | step_simpl ]);
    gres; rewrite Hx; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); vals_lit; close_eq ].

(* [comment removed for export] *)
Ltac gjal_tac Fa Da :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  intros regs mem rom; lit_pc;
  (chain_step; [ reflexivity | exact (step_jal_link _ _ _ _ _ _ _ _ Fa eq_refl Da) | step_simpl ]);
  gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold btgt in G in change_no_check G' end); vals_lit; close_eq.

(* [comment removed for export] *)
Lemma asan_cpm_run : cpm_call ASEGS (0x6f5fc : word) 0x106ddc.
Proof using.
  intros regs mem rom ra cpm Rd Hnz Hret H1.
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_6f5f4 | reflexivity | exact D_6f5f4] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step;
   [ reflexivity
   | eapply step_lb; [exact F_6f5f8 | reflexivity | exact D_6f5f8 | ];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact Rd
   | step_simpl ]).
  gres.
  afence F_6f5fc D_6f5fc.
  an F_6f600 D_6f600.                                   (* [comment removed for export] *)
  aret F_6f604 D_6f604 ra.                              (* [comment removed for export] *)
  rewrite ?regupd_regupd_same.
  lazymatch goal with |- msteps _ (mkst (regupd _ 10 ?v) _ _ _) _ =>
    replace v with (Z_to_bv 64 1 : word) end.
  - wd_refl.
  - pose proof (u_v_lb_nz cpm Hnz) as Hl. pose proof (u64_range (v_lb cpm)).
    (lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end). rewrite u_Z2bv by lia.
    destruct (Z.ltb_spec 0 (bv_unsigned (v_lb cpm))); [reflexivity | lia].
Qed.

Lemma asan_unreg_tab_ok : unreg_tab_ok ASEGS asan_unreg_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_dtor ut_base ut_pt ut_g_start ut_g_stop ut_p_start ut_globs ut_p_flag ut_g_aflags ut_p_aflags ut_p_mu ut_g_pgsz
              ut_c_inited ut_c_ro ut_str asan_unreg_tab pt_base pt_g_shoff pt_g_midbeg pt_g_midend pt_g_hiend pt_g_rms pt_g_cfl pt_c_cpm
              asan_poison_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold unreg_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold dtor_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_poison_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - lit 110180%Z (0x74cac : word). exact asan_inited_run.
  - lit 87988%Z (0x6f5fc : word). exact asan_cpm_run.
  - gload_tac F_59e7c D_59e7c F_59e80 D_59e80.
  - gapaddi_tac F_59e94 D_59e94 F_59ea4 D_59ea4.
  - gauipc_ld_tac F_59f78 D_59f78 F_59f94 D_59f94.
  - gauipc_ld_tac F_59f7c D_59f7c F_59f98 D_59f98.
  - gauipc_ld_tac F_59f80 D_59f80 F_59fa0 D_59fa0.
  - gauipc_ld_tac F_59f84 D_59f84 F_59fa8 D_59fa8.
  - gauipc_ld_tac F_59f88 D_59f88 F_59fb0 D_59fb0.
  - gauipc_ld_tac F_59f8c D_59f8c F_59fb4 D_59fb4.
  - gauipc_ld_tac F_59f90 D_59f90 F_59fb8 D_59fb8.
  - gaddr2_tac F_59fc4 D_59fc4 F_59fc8 D_59fc8.
  - gauipc_ld_tac F_5a230 D_5a230 F_5a240 D_5a240.
  - gauipc_ld_tac F_bf028 D_bf028 F_bf030 D_bf030.
  - gauipc_ld_tac F_bf02c D_bf02c F_bf034 D_bf034.
  - gaddr2_tac F_bf038 D_bf038 F_bf03c D_bf03c.
  - litd 32%Z (0xbf048 : word). lit 1592%Z (0x5a480 : word). gjal_tac F_bf040 D_bf040.
  - imm_norm. split; [vm_compute; reflexivity | lia].
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.




End FPGen1.

