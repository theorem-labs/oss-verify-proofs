(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition asan_poison_tab : poison_tab :=
  {| pt_base := 0x6f610; pt_mset := 0xf56e4;
     pt_g_shoff := 0xff270; pt_p_shoff := 0x107578; pt_g_midbeg := 0xff278; pt_p_midbeg := 0x108268;
     pt_g_midend := 0xff280; pt_p_midend := 0x108270; pt_g_hiend := 0xff288; pt_p_hiend := 0x108260;
     pt_g_rms := 0xff290; pt_p_rms := 0x1011b0; pt_g_cfl := 0xff260; pt_p_cfl := 0x1990a8; pt_c_cpm := 0x106ddc |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_poison_tab_ok : poison_tab_ok ASEGS asan_poison_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend
              pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold poison_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_memset_code.
  - gload_tac F_6f62c D_6f62c F_6f630 D_6f630.
  - gload_tac F_6f644 D_6f644 F_6f648 D_6f648.
  - gload_tac F_6f664 D_6f664 F_6f668 D_6f668.
  - gload_tac F_6f66c D_6f66c F_6f670 D_6f670.
  - gload_tac F_6f688 D_6f688 F_6f68c D_6f68c.
  - gload_tac F_6f84c D_6f84c F_6f850 D_6f850.
  - gload_tac F_6f854 D_6f854 F_6f858 D_6f858.
  - gload_tac F_6f870 D_6f870 F_6f874 D_6f874.
  - gload_tac F_6f88c D_6f88c F_6f890 D_6f890.
  - gload_tac F_6f8b4 D_6f8b4 F_6f8b8 D_6f8b8.
Qed.

(* [comment removed for export] *)
Theorem asan_poison_shadow :
  forall mem rom (addr size value ra sp : word) cpm midend thr regs,
  poisonH ASEGS asan_poison_tab mem addr size value ra sp cpm midend thr ->
  getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = addr -> getr regs 11 = size -> getr regs 12 = value ->
  exists r,
    msteps ASEGS (mkst regs (0x6f610 : word) mem rom)
                 (mkst r ra (wbytes (ps_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                                              (getr regs 20) (getr regs 21))
                                    (Z_to_bv 64 (shad addr)) (repeat (cbyte value) (Z.to_nat (shlen size)))) rom)
    /\ regs_agree (fun r => In r poison_clob) regs r.
Proof using. exact (poison_shadow ASEGS asan_poison_tab asan_poison_tab_ok). Qed.

End FPGen1.
