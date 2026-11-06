(* The crash-free contracts of fuzz_lock.ubsan's two harness functions at the image's own allocator
   (src0_msyms, zlib_API), the crash-free twin of LLVMFuzzerTestOneInput_link.v: check_no_overread_holds_cf and
   check_lookup_holds_cf with the agreement allocator (malloc_contract_ag from AllocCf.v zlib_malloc_contract_cf
   through cno_glue_cf.v malloc_ag_of_cf, free_contract_cf from AllocCf.v zlib_free_contract_cf) and the libc
   walks. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 FrameAPI ZAllocator
  FrameProof SlotAgree AgreeZlib AllocCf.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import
memcpy memcpy_c memchr memchr_c bcmp bcmp_c strlen strlen_c number_c rp_lock_lookup_c rp_lock_lookup
cno_segs cno_glue_cf check_no_overread_c check_no_overread_ccf check_no_overread_cf
check_lookup_c check_lookup_ccf check_lookup_cf.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zlib_limlaw : forall rc : RunCeil, @llvm_limlaw rc src0_msyms (@zlib_API rc).
Proof.
  intros rc L A mem md H. pose proof (zlib_limit rc L A mem md H) as HL.
  unfold SRC_LIM_MIN in HL. lia.
Qed.

Theorem checks_cf_link :
  (forall (rc : RunCeil) (fx : FPState), @check_no_overread_contract_cf fx rc src0_msyms (@zlib_API rc)) /\
  (forall (rc : RunCeil) (fx : FPState), @check_lookup_contract_cf fx rc src0_msyms (@zlib_API rc)).
Proof.
  assert (MALLOC : forall (rc : RunCeil) (fx : FPState), @malloc_contract_ag fx rc src0_msyms (@zlib_API rc))
    by (intros rc fx; exact (malloc_ag_of_cf src0_msyms (@zlib_API rc) (zlib_limlaw rc)
          zlib_malloc_contract_cf)).
  assert (FREE : forall (rc : RunCeil) (fx' : FPState), @free_contract_cf fx' rc src0_msyms (@zlib_API rc))
    by (intros rc fx'; exact zlib_free_contract_cf).
  pose proof (rp_lock_lookup_holds strlen_holds memchr_holds bcmp_holds) as RP.
  pose proof memcpy_holds as MC. pose proof strlen_holds as SLC.
  pose proof memchr_holds as MCH. pose proof bcmp_holds as BC.
  split; intros rc fx.
  - destruct (zlib_frame_allocator rc fx) as (M' & _ & _ & _ & _ & _ & CT' & _).
    eapply (check_no_overread_holds_cf (fx := fx) src0_msyms (@zlib_API rc));
      first [ reflexivity | assumption | exact (errno_below_ceiling rc) | exact zlib_allocator_extra
            | exact (zlib_allocator_extra rc) | exact CT' | exact (MALLOC rc fx) | exact (FREE rc)
            | exact MC | exact RP ].
  - destruct (zlib_frame_allocator rc fx) as (M' & _ & _ & _ & _ & _ & CT' & _).
    eapply (check_lookup_holds_cf (fx := fx) src0_msyms (@zlib_API rc));
      first [ reflexivity | assumption | exact (errno_below_ceiling rc) | exact zlib_allocator_extra
            | exact (zlib_allocator_extra rc) | exact CT' | exact (MALLOC rc fx) | exact (FREE rc)
            | exact MC | exact SLC | exact MCH | exact BC ].
Qed.

