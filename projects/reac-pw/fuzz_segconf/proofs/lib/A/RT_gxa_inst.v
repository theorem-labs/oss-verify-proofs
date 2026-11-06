(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_gxa_inst.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* GXA's two top theorems, instantiated on the pinned fuzz_manifest.asan.

   lib/CJ/RL/GXA holds the format-general ASan printf core, proved and Qed over an abstract image
   record: printf_core_a_proof (G_printf_core.v:1028), vfprintf_snf_a_closed and
   vfprintf_snf_a_guarded_closed (G_vfprintf_snf_closed.v:109, :118) and vsnprintf_x_proof
   (G_vsnprintf.v).  Every image fact they take is discharged for this harness in RT_IImgA_ok.v at
   RT_IImgA.v's instance A_img (and A_img_vsn for musl vsnprintf, whose call to vfprintf lands on
   the link-time wrapper, not on musl vfprintf's body).  This file joins the two: it carries the
   image facts in and leaves exactly three hypotheses open, the ASan interceptor call contracts
   that the wrapper walks supply:

     memcpy_stack_contract copy_ready    (CopyCall.v:30)     at __wrap_memcpy   0x51a64
     memset_stack_contract set_ready     (SetCall.v:29)      at __wrap_memset   0x51a60
     strnlen_stack_contract strn_ready   (StrnlenCall.v:30)  at __wrap_strnlen  0x412cc

   pop_arg, pop_arg_x and __extenddftf2 are NOT hypotheses: this build calls them directly and
   RT_IImgA_ok.v closes their contracts (fr_pop_arg_contract, fr_pop_arg_x_contract).

   The image facts are carried by instance resolution, and the call contracts by name.  Do not
   close these with `unshelve eapply ...; all: first [<long exact list>]`: measured on plugin-hostd/fuzz_reply's
   b4, that backtracks over the guarded theorem's evars and ran 45 minutes without finishing. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad FmtFp StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg GRoTab.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model Printf_zfacts G_pop_arg_x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require Import AsanFacts SetCall StrnlenCall CopyCall VfprintfCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require Import G_sn_write G_printf_snfsink G_vfprintf_snf G_vfprintf_snf_closed.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require G_vsnprintf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import RT_IImgA RT_IImgA_ok.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance A_img.

(* the image facts of the closure, as instances, so the theorems below carry them without a search
   over a list of `exact`s *)
#[local] Existing Instances
  fr_CODE_vfprintf fr_RB_vfprintf fr_RN_printf_core fr_RN_lockfile fr_RN_towrite fr_RN_unlockfile
  fr_RN_stack_chk_fail fr_CODE_towrite fr_RB_towrite
  fr_CODE_sn_write fr_RS_snw fr_RB_snw fr_RN_snw_memcpy
  fr_CODE_fwritex fr_RB_fwritex fr_RN_fwritex_memcpy
  fr_CODE_printf_core fr_RB_printf_core fr_RO_10884
  fr_RN_B_fwritex fr_RN_B_pop_arg fr_RN_B_fmt_fp fr_RN_B_errno_location fr_RN_B_strerror
  fr_RN_B_strnlen fr_RN_B_wctomb fr_RN_B_pad fr_RN_B_memset fr_RN_B_stack_chk_fail
  fr_RS_K_109cc fr_RS_K_10884 fr_RS_K_1029e fr_RS_K_103b3 fr_RS_K_10964 fr_RS_K_10b9c
  fr_RO_states0 fr_RO_pfx fr_RQ_pfx_lo fr_RQ_pfx_got fr_RO_xdigits fr_RO_states
  fr_RS_got_ssp fr_RS_34288 fr_RS_35000 fr_RL0_0 fr_RL0_1 fr_RL1_0
  fr_CODE_pop_arg fr_RB_pop_arg fr_RO_10984 fr_RN_B_extenddftf2 fr_RS_K_10984
  fr_CODE_extenddftf2 fr_RB_extenddftf2.

(* ---- musl vfprintf on the snprintf sink, at fuzz_manifest.asan ---- *)

Definition fm_vfprintf_snf_a_closed
  (copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop)
  (set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop)
  (strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop)
  (INV : (word -> option byte) -> Prop)
  (SPEC_memcpy : @memcpy_stack_contract A_img copy_ready)
  (SPEC_memset : @memset_stack_contract A_img set_ready)
  (SPEC_strnlen : @strnlen_stack_contract A_img strn_ready) :=
  vfprintf_snf_a_closed copy_ready SPEC_memcpy set_ready strn_ready INV
    (IMG := A_img) (SPEC_memset := SPEC_memset) (SPEC_strnlen := SPEC_strnlen)
    (SPEC_pop_arg := fr_pop_arg_contract) (SPEC_pop_arg_x := fr_pop_arg_x_contract).

Definition fm_vfprintf_snf_a_guarded_closed
  (copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop)
  (set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop)
  (strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop)
  (INV : (word -> option byte) -> Prop)
  (SPEC_memcpy : @memcpy_stack_contract A_img copy_ready)
  (SPEC_memset : @memset_stack_contract A_img set_ready)
  (SPEC_strnlen : @strnlen_stack_contract A_img strn_ready) :=
  vfprintf_snf_a_guarded_closed copy_ready SPEC_memcpy set_ready strn_ready INV
    (IMG := A_img) (SPEC_memset := SPEC_memset) (SPEC_strnlen := SPEC_strnlen)
    (SPEC_pop_arg := fr_pop_arg_contract) (SPEC_pop_arg_x := fr_pop_arg_x_contract).

(* the printf core alone, format-general, at this image: GXA's printf_core_a_all, which is
   printf_core_a_stmt for every sink the caller gives *)
Definition fm_printf_core_a_all
  (set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop)
  (strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop)
  (SPEC_memset : @memset_stack_contract A_img set_ready)
  (SPEC_strnlen : @strnlen_stack_contract A_img strn_ready)
  : @printf_core_a_all A_img set_ready strn_ready :=
  snf_printf_core_ok set_ready strn_ready
    (IMG := A_img) (SPEC_memset := SPEC_memset) (SPEC_strnlen := SPEC_strnlen)
    (SPEC_pop_arg := fr_pop_arg_contract) (SPEC_pop_arg_x := fr_pop_arg_x_contract).

(* the string-buffer write callback, which is what carries truncation: its post writes
   firstn cn (pend ++ src) into the destination and moves the cookie by Z.min cn (|pend| + |src|) *)
Definition fm_sn_write_ok
  (copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop)
  (SPEC_memcpy : @memcpy_stack_contract A_img copy_ready)
  : @G_sn_write.sn_write_contract A_img copy_ready :=
  snf_sn_write_ok (IMG := A_img) copy_ready SPEC_memcpy.

(* ---- musl vsnprintf, at the second instance ---- *)
(* The implicit image facts are written positionally here: A_img_vsn is not the ambient instance,
   and its rows are the ones RT_IImgA_ok.v states at that record. *)
Definition fm_vsnprintf_x_proof
  (set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop)
  (vf_ready : vf_guard)
  (SPEC_memset : @memset_stack_contract A_img_vsn set_ready)
  (VF : @vfprintf_guarded_stmt A_img_vsn vf_ready) :=
  @G_vsnprintf.vsnprintf_x_proof A_img_vsn
    fr_CODE_vsnprintf fr_RB_vsnprintf fr_RN_vsn_memset fr_RN_vsn_vfprintf
    fr_RS_vsn_got_ssp fr_RS_vsn_snw fr_RS_vsn_34288 fr_RS_vsn_35000
    fr_RL0_0_vsn fr_RL0_1_vsn fr_RQ_vsn_22e18
    set_ready vf_ready SPEC_memset VF.
