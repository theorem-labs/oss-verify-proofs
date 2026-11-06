(* put_string's ASan walk, CLOSED: put_string_spec (image A, fs.asan) from the four segments of ZZpsclose.ps_close.
   SEG1 ZZpsg1.psg1 (entry, fake-frame grant, the opening-quote put), SEG2 ZZpsg2.psg2 (the scan loop or the empty
   arm, the run put), SEG3 ZZpsg3.psg3 (the closing-quote put), SEG4 ZZpstail.psg4 (the epilogue to the post).
   The Section hypotheses are the walk's OPEN hypotheses, each with its owner. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame
FSW_frame3 FSW_writer_tbl FSW_writer_model FSW_put_string ZZpsclose ZZpsg1 ZZpsg2 ZZpsg3 ZZpstail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer.
Open Scope Z_scope.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* put's S0 contract: the callee, discharged at composition by the put lane's walk (FSW_put.v) *)
Hypothesis HPUT : FSH_Fn_writer.put_spec B tfibsegs.
(* the shadow-base cell pair (S0's FsShadowSyms; owner RELOC, discharged by S0's FSrtcellsS0 when it lands) *)
Hypothesis HSS : FsShadowSyms B.
(* the unit's runtime laws (owner RUNTIME: the donor's TfibLib) *)
Hypothesis HENV : api_env tfibsegs B.
Hypothesis HML : model_laws (as_universe B).
Hypothesis HSMP : stack_malloc_progressP B.
(* __asan_stack_malloc_0's statement (owner a Theorem Labs lane, walk open) *)
Hypothesis HSM0 : astack_malloc_realizesU tfibsegs B 0.
(* B's code map at class 0 (owner RELOC: TfibLib's tl_code) *)
Hypothesis HSMPC : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0.
(* the fake frame's release laws (owner RUNTIME) *)
Hypothesis HASF : astack_free_law tfibsegs B.
Hypothesis HFFL : frame_flag_lawP tfibsegs B.
(* the use-after-return cell pair (owner RELOC: TfibLib's tl_got_uar / tl_uar_cell) *)
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
(* fs's image facts (owner RELOC / RUNTIME) *)
Hypothesis HIMG : fs_img_facts tfibsegs B.

Theorem ps_put_string_spec : FSH_Fn_writer.put_string_spec B tfibsegs.
Proof.
  apply (ps_close B); [apply (psg1 B) | apply (psg2 B) | apply (psg3 B) | apply (psg4 B)]; assumption.
Qed.

End F.
