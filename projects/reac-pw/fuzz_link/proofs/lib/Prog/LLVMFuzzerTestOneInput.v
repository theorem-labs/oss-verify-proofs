(* LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the slot meets its contract
   (lib/Prog/LLVMFuzzerTestOneInput_c.v, the T form the frame asks at mf_shape), given the contracts of the
   functions it calls. The walk is in lib/Prog/Slot/: the evt segments of the entry, the exit and the six
   operation arms (files LE, LEX, LC0 to LC45), the SR frame (files LFr: the cut, the allocator steps, the
   post), and the glue of each piece (files LGEE, LG0 to LG4, LGMq2, LGMq5), composed by
   LGlue.LLVMFuzzerTestOneInput_of_pieces over the 48-operation loop (LLoop). The callees' contracts are this
   Section's hypotheses; each is proved by its own walk in lib/Prog. *)
From OSSVerify.reac_pw.fuzz_link Require Statements.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
  YM02 YO06 YH00 YH02 YI5b YI5c YL0k YL0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import ZTraceSpec ZComplete ZAllocator FrameProof
  MemFileSink FrameSlotMF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem
  kernel_c model_read_c model_write_c model_decide_c bcmp_c memset_c strcmp_c strlen_c snprintf_c
  snprintf_img_c index_of_c reac_link_alias_read_c reac_link_alias_write_c reac_served_unmark_all_c
  check_socket_c check_refused_c check_bounds_c check_read_c check_write_c
  check_requests_c check_marks_c check_verdict_c text_buf_c text_of_c mark_quietly_c mwrite_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LGlue
  LGEEOp LGEEEnt LGEEExit LG0 LG1 LG3 LG4 LGMq2 LGMq5 LHolds.
Local Open Scope Z_scope.

Section Holds.
Hypothesis KERNEL_C : kernel_contract.
Hypothesis MODEL_READ_C : model_read_contract.
Hypothesis MODEL_WRITE_C : model_write_contract.
Hypothesis MODEL_DECIDE_C : model_decide_contract.
Hypothesis BCMP_C : bcmp_contract.
Hypothesis MEMSET_C : memset_contract.
Hypothesis STRCMP_C : strcmp_contract.
Hypothesis STRLEN_C : strlen_contract.
Hypothesis SNPRINTF_C : snprintf_contract.
Hypothesis SNPRINTF_IMG_C : snprintf_img_contract.
Hypothesis INDEX_OF_C : index_of_contract_P.
Hypothesis ALIAS_READ_C : reac_link_alias_read_contract.
Hypothesis ALIAS_WRITE_C : reac_link_alias_write_contract.
Hypothesis UNMARK_ALL_C : reac_served_unmark_all_contract.
Hypothesis DECIDE_C : reac_served_decide_contract.
Hypothesis CHECK_SOCKET_C : check_socket_contract.
Hypothesis CHECK_REFUSED_C : check_refused_contract.
Hypothesis CHECK_BOUNDS_C : check_bounds_contract.
Hypothesis CHECK_READ_C : check_read_contract.
Hypothesis CHECK_WRITE_C : check_write_contract.
Hypothesis CHECK_REQUESTS_C : check_requests_contract.
Hypothesis CHECK_MARKS_C : check_marks_contract.
Hypothesis CHECK_MARK_C : check_mark_contract.
Hypothesis CHECK_VERDICT_C : check_verdict_contract.

Section Inst.
Variable B : malloc_syms.
Variable APIf : forall rc : YM05.RunCeil, AllocAPI B.
Variables (SH : sink_head) (SK : sink_syms).
(* the three callees that allocate, at this allocator: at every FP state and run ceiling *)
Hypothesis TEXT_BUF_C : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @text_buf_contract fx rc B (APIf rc).
Hypothesis TEXT_OF_C : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @text_of_contract fx rc B (APIf rc).
Hypothesis MARK_QUIETLY_C : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @mark_quietly_contract fx rc B (APIf rc).

Ltac discharge :=
  first [ assumption
        | intros; apply TEXT_BUF_C | intros; apply TEXT_OF_C | intros; apply MARK_QUIETLY_C ].

Theorem LLVMFuzzerTestOneInput_holds : LLVMFuzzerTestOneInput_contract B APIf SH SK.
Proof.
  apply LLVMFuzzerTestOneInput_of_pieces; [| exact glue_lh_op].
  intros rc FF. split; [| split].
  - apply (glue_entry B (APIf rc)); discharge.
  - intros k Hk.
    assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia.
    + apply (glue_arm0 B (APIf rc)); discharge.
    + apply (glue_arm1 B (APIf rc)); discharge.
    + apply (glue_arm2 B (APIf rc)); discharge.
    + apply (glue_arm3 B (APIf rc)); discharge.
    + apply (glue_arm4 B (APIf rc)); discharge.
    + apply (glue_arm5 B (APIf rc)); discharge.
  - apply (glue_exit B (APIf rc)); discharge.
Qed.

End Inst.

(* the plain top: plain_halts from the slot at the frame's own instance (LHolds) and the printf lane's mwrite
   contract, which the frame's __stdio_exit asks *)
Theorem plain_halts_of_callees :
  (forall (fx : YK11.FPState) (rc : YM05.RunCeil), @text_buf_contract fx rc src0_msyms (@zlib_API rc)) ->
  (forall (fx : YK11.FPState) (rc : YM05.RunCeil), @text_of_contract fx rc src0_msyms (@zlib_API rc)) ->
  (forall (fx : YK11.FPState) (rc : YM05.RunCeil), @mark_quietly_contract fx rc src0_msyms (@zlib_API rc)) ->
  mwrite_contract -> Statements.plain_halts.
Proof.
  intros TB TO MQ HMW.
  exact (plain_halts_of_slot HMW
           (LLVMFuzzerTestOneInput_holds src0_msyms (@zlib_API) src0_sink_head src0_sink TB TO MQ)).
Qed.

End Holds.

About LLVMFuzzerTestOneInput_holds.
Print Assumptions LLVMFuzzerTestOneInput_holds.
About plain_halts_of_callees.
Print Assumptions plain_halts_of_callees.
