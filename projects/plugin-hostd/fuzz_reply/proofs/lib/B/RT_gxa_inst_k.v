(* Image B twin of lib/A/RT_gxa_inst_k.v at 2c1f180a413 (sha256 b0d186e6fa4a; internal record): module paths lib.A -> lib.B; 2 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINKB-numerals.tsv sha256 86a76b0550d0; internal record). *) (* The keep-FP twin's closed musl printf theorems (lib/CJ/RL/GXAK, provenance/keepfx/README.md) INSTANTIATED on the
   pinned fuzz_reply.asan-ubsan: RT_gxa_inst.v's two definitions pointed at the twin.
   Copy of lib/A/RT_gxa_inst.v:41-64 and :92-114 at d49bd1db505 (sha256 2adc6e6dd04b; internal record), retargeted to GXAK.

   The image facts are RT_IImgA_ok.v's (vm_compute checks at RT_IImgA.v's instances) and RT_gxa_inst.v's six
   A_img_vsn globals, given EXPLICITLY in declaration order, as RT_gxa_inst.v does (a `first [...]` search over them
   does not finish).  Three facts name a definition the twin copied, so they are re-checked here at the twin's
   constant by the same `inst` tactic: musl vfprintf's code (GXK/G_vfprintf_snf.v PROGAT_CODE_vfprintf), sn_write's
   symbol (GXK K_SN_WRITE), musl vsnprintf's code (GXAK/G_vsnprintf.v PROGAT_CODE_vsnprintf).  The pop_arg /
   pop_arg_x call contracts are the twin's, closed in RT_IImgA_ok_k.v.  What stays a hypothesis is what RT_gxa_inst.v
   leaves: the memcpy / memset / strnlen interceptor call contracts (RT_gxa_calls_mem.v, RT_gxa_calls.v close them),
   the store invariant INV, and VF, musl vsnprintf's call into the vfprintf interceptor (RT_pf_vf_k.v closes it). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require Import SetCall StrnlenCall CopyCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_IImgA RT_IImgA_ok.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vfprintf_snf_closed.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vsnprintf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA_ok_k.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_inst.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation mem := (word -> option byte).

Module GIFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_printf_core_common.G_printf_iface.
Module GVFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_vfprintf_snf.
Module VFCK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Module GVCK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vfprintf_snf_closed.
Module GVSK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.G_vsnprintf.
Module OKK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA_ok_k.
Module GI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_inst.

(* the three image facts at the twin's constants (same checks as RT_IImgA_ok.v:36, :47-48, :92) *)
Lemma frk_CODE_vfprintf : CodeAtT (@img_segs A_img) (@sym A_img 0x7f000400) (GVFK.PROGAT_CODE_vfprintf A_img).
Proof. inst. Qed.
Lemma frk_RS_snw : RelSym (@sym A_img GIFK.K_SN_WRITE). Proof. inst. Qed.
Lemma frk_RB_snw : RelCode (@sym A_img GIFK.K_SN_WRITE) 220. Proof. inst. Qed.
Lemma frkv_CODE_vsnprintf :
  CodeAtT (@img_segs A_img_vsn) (@sym A_img_vsn 0x7f000200) (GVSK.PROGAT_CODE_vsnprintf A_img_vsn).
Proof. inst. Qed.
Lemma frkv_RS_snw : RelSym (@sym A_img_vsn GIFK.K_SN_WRITE). Proof. inst. Qed.

Section S.
(* musl vfprintf's body, printf_core, sn_write, __fwritex at A_img (musl vfprintf 0x93288) *)
Variable copy_ready : mem -> Z -> Z -> Z -> Z -> Prop.
Hypothesis SPEC_memcpy : @memcpy_stack_contract A_img copy_ready.
Variable set_ready : mem -> Z -> Z -> Z -> Prop.
Hypothesis SPEC_memset : @memset_stack_contract A_img set_ready.
Variable strn_ready : mem -> Z -> Z -> Z -> list byte -> Prop.
Hypothesis SPEC_strnlen : @strnlen_stack_contract A_img strn_ready.
Variable INV : mem -> Prop.

Definition fr_vfprintf_guarded_k :=
  @GVCK.vfprintf_snf_a_guarded_closed A_img
    frk_CODE_vfprintf fr_RB_vfprintf fr_RN_printf_core fr_RN_towrite fr_CODE_towrite
    fr_CODE_sn_write frk_RS_snw frk_RB_snw fr_RN_snw_memcpy fr_CODE_fwritex fr_RB_fwritex
    fr_RN_fwritex_memcpy fr_CODE_printf_core fr_RB_printf_core fr_RO_10884
    fr_RN_B_fwritex fr_RN_B_pop_arg fr_RN_B_fmt_fp fr_RN_B_errno_location fr_RN_B_strerror
    fr_RN_B_strnlen fr_RN_B_wctomb fr_RN_B_pad fr_RN_B_memset fr_RN_B_stack_chk_fail
    fr_RS_K_109cc fr_RS_K_10884 fr_RS_K_1029e fr_RS_K_103b3 fr_RS_K_10964 fr_RS_K_10b9c
    fr_RO_states0 fr_RO_pfx fr_RQ_pfx_lo fr_RQ_pfx_got fr_RO_xdigits fr_RO_states
    fr_RS_got_ssp fr_RS_34288 fr_RS_35000 fr_RL0_0 fr_RL0_1 fr_RL1_0
    copy_ready SPEC_memcpy set_ready SPEC_memset strn_ready SPEC_strnlen
    OKK.fr_pop_arg_contract OKK.fr_pop_arg_x_contract INV.

End S.

Section V.
(* musl vsnprintf at A_img_vsn: its vfprintf call lands on the interceptor trampoline 0x42228 *)
Variable set_ready : mem -> Z -> Z -> Z -> Prop.
Variable vf_ready : VFCK.vf_guard.
Hypothesis SPEC_memset : @memset_stack_contract A_img_vsn set_ready.
Hypothesis VF : @VFCK.vfprintf_guarded_stmt A_img_vsn vf_ready.

Definition fr_vsnprintf_x_k : @GVSK.vsnprintf_x_stmt A_img_vsn set_ready vf_ready :=
  @GVSK.vsnprintf_x_proof A_img_vsn
    frkv_CODE_vsnprintf fr_RB_vsnprintf fr_RN_vsn_memset fr_RN_vsn_vfprintf
    GI.frv_RS_got_ssp frkv_RS_snw GI.frv_RS_34288 GI.frv_RS_35000 GI.frv_RL0_0 GI.frv_RL0_1 fr_RQ_vsn_22e18
    set_ready vf_ready SPEC_memset VF.

End V.
