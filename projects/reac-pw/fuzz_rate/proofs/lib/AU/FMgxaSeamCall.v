(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamCall.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMgxaSeamCall.table); names: record RT_IImgA -> A_img RecAsanVfA.N_img_asan_vf. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMgxaSeamCall.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* The GXA side of the seam, packaged: the three ASan interceptor call contracts the released
   theorem leaves open, the readiness predicates its guard asks for, and musl vfprintf's walk at
   fm.asan instantiated on them.

   RT_gxa_inst.v leaves exactly three hypotheses (its header): memcpy_stack_contract at
   __wrap_memcpy 0x51a64, memset_stack_contract at __wrap_memset 0x51a60, strnlen_stack_contract at
   __wrap_strnlen 0x412cc.  h-rw-ide-4 supplies the first two (lib/A/FMgxa_mem.v, relocating
   c-asan-rt-stateio-n's I_memcpyw*.v / I_memsetw.v) and RtPrintf.GxStrn the third.  Each is stated
   over a `*_ready` predicate that says when the interceptor may be called; the released design
   pushes that readiness to the caller (G_vsnprintf.v's vsnprintf_ready does the same one layer up),
   so it is a hypothesis here too, in the shape vf_ready_a asks for.

   Nothing in this file depends on the harness: it is GXA's own vocabulary. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMgxaSeamCall.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMgxaSeamCall.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMgxaSeamCall.v keeps its donor's comment text) is kept as lib/A/FMgxaSeamCall.v writes it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import
SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require Import Prelim Monad FmtFp StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require Import
G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg GRoTab.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GX Require Import Printf_model Printf_zfacts G_pop_arg_x.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA Require Import
AsanFacts SetCall StrnlenCall CopyCall VfprintfCall.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA Require Import
G_sn_write G_printf_snfsink G_vfprintf_snf G_vfprintf_snf_closed.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Import RecAsanVfBR.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RT_IImgA_ok RT_gxa_inst.
Import ListNotations.
Open Scope Z_scope.

Section C.
(* the three interceptor call contracts, with their readiness predicates *)
Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop.
Hypothesis SPEC_memcpy : @memcpy_stack_contract N_img_asan_vf copy_ready.
Hypothesis SPEC_memset : @memset_stack_contract N_img_asan_vf set_ready.
Hypothesis SPEC_strnlen : @strnlen_stack_contract N_img_asan_vf strn_ready.

(* the invariant the walk threads; the seam needs none, so it is True *)
Definition SEAM_INV : (word -> option byte) -> Prop := fun _ => True.

(* musl vfprintf at fm.asan 0x8ede0, in CJ's evt form, under those three contracts, through the
   UNGUARDED released statement (G_vfprintf_snf.v:194): the guard's pieces are separate premises and
   the stack window is VFA_DEPTH = 368 + PC_DEPTH = 5552 below musl vfprintf's entry sp, 48 bytes
   less than the guarded statement's 48 + VF_DEPTH (VfprintfCall.v:36), so the seam's window is
   exactly the VF_DEPTH = 5552 that RtPrintf.Param's vfprintf-interceptor walk calls it at. *)
Definition seam_vfprintf_a :
  @vfprintf_snf_a_stmt N_img_asan_vf (snf_out_ready copy_ready) set_ready strn_ready copy_ready SEAM_INV
  := fm_vfprintf_snf_a_closed copy_ready set_ready strn_ready SEAM_INV
       SPEC_memcpy SPEC_memset SPEC_strnlen.

End C.
