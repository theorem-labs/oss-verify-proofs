(* fuzz_lock.ubsan's LLVMFuzzerTestOneInput with its callees' contracts discharged by their walks, in the form of
   the plain lib/Prog/LLVMFuzzerTestOneInput_link.v and of libreac/fuzz_decode's released
   lib/Prog/LLVMFuzzerTestOneInput_link.v (25e3d17bdb50): the two harness functions meet the contracts
   Statement.v's checks_hold asks for, from check_no_overread_holds and check_lookup_holds and the libc walks
   (memcpy, strlen, memchr, bcmp, rp_lock_lookup), with check_lookup_exp_seg for check_lookup_exp's segment. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import
memcpy memcpy_c memchr memchr_c bcmp bcmp_c strlen strlen_c number_c rp_lock_lookup_c rp_lock_lookup
cno_segs check_no_overread_c check_no_overread check_lookup_c check_lookup
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr Statement LLVMFuzzerTestOneInput_end.
Import ListNotations.
Local Open Scope Z_scope.

Section L.

Theorem checks_link : checks_hold.
Proof.
  intros rc fx B API SH SK BI FR.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof FR as (FA & ERRNO & _).
  assert (MALPC : ms_malloc B = CNO_MALLOC) by exact HMAL.
  assert (FREEPC : ms_free B = CNO_FREE) by exact HFRE.
  assert (FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API)
    by (intros fx'; exact (proj1 (proj2 (FA fx')))).
  pose proof (rp_lock_lookup_holds strlen_holds memchr_holds bcmp_holds) as RP.
  pose proof memcpy_holds as MC. pose proof strlen_holds as SLC.
  pose proof memchr_holds as MCH. pose proof bcmp_holds as BC.
  destruct (FA fx) as (M' & _ & _ & _ & _ & _ & CT' & _).
  split.
  - eapply (check_no_overread_holds (fx := fx)); eassumption.
  - eapply (check_lookup_holds (fx := fx)); eassumption.
Qed.

End L.
