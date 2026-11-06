From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memcpy_c memset_c same_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c pj_free_c parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import padded_c padded.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_glue check_no_overread_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_spec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_a check_no_overread_b check_no_overread_end.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* check_no_overread (#102 ubsan 0x13868) from its three phases: cnoA_holds (entry, the three padded copies, the tree
   memsets and the first out_of_memory() test, to the first parse_noting call) needs cno_KB, cnoB_holds (the readings,
   the other out_of_memory() tests and the compares) gives cno_KB from cno_KC, and cnoC_holds (frees, a0 = 0 and
   epilogue) gives cno_KC.  The callees enter as their stated contracts; padded's contract comes from padded_holds on
   the same hypotheses (malloc, memcpy, memset), with errno below the ceiling from the reader environment.  The two
   entry bytes g_ran_out = g_own_ran_out = 0 are the contract's premises. *)

Section H.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HMAL : ms_malloc B = 0x18390.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis PARSE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis SAME : same_contract.

Theorem check_no_overread_holds : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @check_no_overread_contract fx rc B API F.
Proof.
  intros fx. unfold check_no_overread_contract.
  intros L A regs mem md Lam peak cnt b data x Henv LED CNT G10 G11 XLEN XB XBLK RES ROOM GR0 GO0.
  pose proof Henv as (SEG & TP & ERR & GGD & GRD & PRE & SPHI & SPLO & FZ & CELLS).
  pose proof CELLS as (RA & _).
  assert (HERR' : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling).
  { rewrite ERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO.
    pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value. lia. }
  assert (HPAD : forall fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState,
            @padded_contract fx' rc B API F)
    by (intros fx'; exact (padded_holds B API F SEG HERR' HMAL MALLOC MEMCPY MEMSET fx')).
  assert (KC : cno_KC B API F L A regs mem md Lam peak cnt b data x) by (eapply cnoC_holds; eassumption).
  assert (KB : cno_KB B API F L A regs mem md Lam peak cnt b data x) by (eapply cnoB_holds; eassumption).
  eapply cnoA_holds; eassumption.
Qed.

End H.
