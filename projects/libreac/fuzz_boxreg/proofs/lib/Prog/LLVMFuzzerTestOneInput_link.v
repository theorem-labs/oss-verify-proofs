From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import
memcpy_c memcpy memset memchr bcmp strncmp check reac_boxreg_init
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_exit
LLVMFuzzerTestOneInput_entry LLVMFuzzerTestOneInput_join LLVMFuzzerTestOneInput.
Import ListNotations.
Local Open Scope Z_scope.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis SINK : lf_sink_env B.

Theorem LLVMFuzzerTestOneInput_holds_of_cases :
  llvm_cases_ok B API -> LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros CASES.
  apply (LLVMFuzzerTestOneInput_holds_of B API FREE memcpy_holds ERRNO_LOW SINK).
  - exact (llvm_entry_holds B API MALLOC
      (reac_boxreg_init_holds memset_holds) (check_holds memchr_holds bcmp_holds) ERRNO_LOW).
  - exact CASES.
  - exact (llvm_join_holds B API (check_holds memchr_holds bcmp_holds) bcmp_holds strncmp_holds).
Qed.

End L.
