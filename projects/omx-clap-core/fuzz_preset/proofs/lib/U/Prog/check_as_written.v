From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes strtod_c ex_value_c ex_ws_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_as_written_c check_as_written_k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require GIInit fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11.
Import ListNotations.
Local Open Scope Z_scope.

Section T.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HMAL : ms_malloc B = 0x18390.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERU : errno_unowned B API.
Hypothesis MALLOC : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState,
  @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState,
  @free_contract_r fx rc B API F.
Hypothesis EXV : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_value_c.ex_value_contract.
Hypothesis EXW : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.ex_ws_c.ex_ws_contract.
Hypothesis HG : globals_free B API GIInit.omx_G.
Hypothesis RANC : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract.

Theorem check_as_written_holds : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState,
  @check_as_written_contract fx rc B API F.
Proof.
  intros fx. unfold check_as_written_contract.
  intros L A regs mem md data rcv doc x lblk t D b ENV R10 R11 R12 R13 Hrcv Hdoc Hlen Hd0 Hd1 HDB HDI HDOC HAG
    HRES HROOM.
  destruct ENV as (HS & HTP & HERR & HGG & HGD & PRE & HSP47 & HGLOB & HFZ & HRD).
  assert (HDB' : bytes_at rsegs mem data x) by (rewrite <- HS; exact HDB).
  assert (HDOC' : rcv = 0 -> pj_node rsegs mem lblk doc t D /\ spZ regs <= doc /\ doc + 56 <= 2 ^ 47 /\
     Forall (fun ak => caw_inside L A (fst ak) (snd ak) /\ fst ak mod 8 = 0) D)
    by (intros H0; rewrite <- HS; exact (HDOC H0)).
  apply (SR_mono _ _ _ _ (caw_main B API F HS AX ERU HERR HTP HGG HGD HMAL HFREE MALLOC FREE EXV EXW HG RANC L A regs mem md
    PRE HSP47 HGLOB fx data rcv doc x lblk t D b HFZ HRD R10 R11 R12 R13 Hrcv Hdoc Hlen Hd0 Hd1 HDB' HDI HDOC' HAG
    HRES HROOM)).
  intros c' (fx' & L' & A' & regs' & mem' & md' & E & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  exists fx', L', A', regs', mem', md'.
  split; [exact E|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. exact H10.
Qed.

End T.
