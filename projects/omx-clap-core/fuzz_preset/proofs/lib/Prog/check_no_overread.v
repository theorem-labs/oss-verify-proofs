From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import memcpy_c memset_c same_c pj_free_c PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import parse_noting_c fuzz_alloc_ran_out_c fuzz_alloc_ran_out.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_c check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_glue check_no_overread_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_spec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_a check_no_overread_b check_no_overread_end.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section H.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HMAL : ms_malloc B = 0x178d8.
Hypothesis HFREE : ms_free B = 0x17798.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : forall fx : YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis PARSE : forall fx : YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis SAME : same_contract.

(* The #102 contract (check_no_overread_c): its two flag premises (g_ran_out and g_own_ran_out bytes 0 at the entry)
   are GRO0 / OWN0 of the three phases; fuzz_alloc_ran_out, called by the four out_of_memory() tests, steps through
   its own proved walk (fuzz_alloc_ran_out_holds), so the Section hypotheses stay those of the old top. *)
Theorem check_no_overread_holds : forall fx : YK11.FPState, @check_no_overread_contract fx rc B API F.
Proof.
  intros fx. unfold check_no_overread_contract.
  intros L A regs mem md Lam peak cnt b data x Henv LED CNT G10 G11 XLEN XB XBLK RES ROOM GRO0 OWN0.
  pose proof Henv as (SEG & TP & ERR & GGD & GRD & PRE & SPHI & SPLO & FZ & CELLS).
  pose proof CELLS as (RA & _).
  pose proof fuzz_alloc_ran_out_holds as FAR.
  assert (KC : cno_KC B API F L A regs mem md Lam peak cnt b data x) by (eapply cnoC_holds; eassumption).
  assert (KB : cno_KB B API F L A regs mem md Lam peak cnt b data x) by (eapply cnoB_holds; eassumption).
  eapply cnoA_holds; eassumption.
Qed.

End H.
