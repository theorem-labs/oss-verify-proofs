(* fuzz_recv on image A (fuzz_link.asan 0x823cc, listing offset AF_fuzz_recv = 0x200; listing
   (internal path) (internal record, sha256 549eae89aefb)): the walk of its contract
   lib/A/Prog/fuzz_recv_c.v `fuzz_recv_acontract` (link_amem.v `aleaf`, K = 4192, EV 0, SIDE []).

   The walk is cut into pieces whose statements are in lib/A/Prog/fuzz_recv_defs.v; this file puts them together:
   - fuzz_recv_entry.v rv_compose: the contract from RV_AT_ERRNO and RV_AT_MEMCPY (the entry +0x00 .. +0xd0 / +0x220);
   - fuzz_recv_err.v rv_err_ok: RV_AT_ERRNO from RV_RET and RV_FPOST (the call of ___errno_location, the store to
     errno);
   - fuzz_recv_cp.v rv_cp_ok: RV_AT_MEMCPY from RV_AT_MEMSET1 (the call of checked_memcpy);
   - fuzz_recv_m1.v rv_m1_ok: RV_AT_MEMSET1 from RV_RET, RV_LOOP, RV_CPOST (the call of checked_memset, the loop test);
   - fuzz_recv_loop.v rv_loop_ok: RV_LOOP from RV_RET, RV_CPOST (the trailing NLMSG_ERROR records);
   - fuzz_recv_ret.v rv_ret_ok: RV_RET (the epilogue and the apost);
   - fuzz_recv_post.v rv_cpost_ok, rv_fpost_ok: the two Posts.

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts; ERRF (errno is not in the
   runtime's owned static table) is discharged on the image by LinkWalkErrnoInst.v `link_errno_not_static`; ERRNO,
   ___errno_location's contract, by lib/A/Rt/RtErrnoLocClosed.v `link_errno_location_closed` (0x90a7c); MEMCPY,
   checked_memcpy's, by lib/A/AE2q.v (0x52d78); MEMSET, checked_memset's, by lib/A/AE2r.v (0x53214).

   Proves fuzz_recv (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk fuzz_recv_c fuzz_recv_defs fuzz_recv_kit
fuzz_recv_entry fuzz_recv_err fuzz_recv_cp fuzz_recv_m1 fuzz_recv_loop fuzz_recv_ret fuzz_recv_post.
Import ListNotations.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis ERRNO : aerrno_location_realizes SEGS B (pa_sigma LS____errno_location).
Hypothesis MEMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Hypothesis MEMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).

Theorem fuzz_recv_aproof : forall rlo rhi, fuzz_recv_acontract SK SEGS rlo rhi B.
Proof.
apply (rv_compose SK B LAWS TL LV ERRF).
- intros c HC.
  pose proof (rv_ret_ok SK B LAWS TL LV ERRF c HC) as RET.
  pose proof (rv_fpost_ok SK B c HC) as FPOST.
  exact (rv_err_ok SK B LAWS TL ERRF ERRNO c HC RET FPOST).
- intros c HC.
  pose proof (rv_ret_ok SK B LAWS TL LV ERRF c HC) as RET.
  pose proof (rv_cpost_ok SK B c HC) as CPOST.
  pose proof (rv_loop_ok SK B LAWS TL ERRF MEMSET c HC RET CPOST) as LOOP.
  pose proof (rv_m1_ok SK B LAWS TL MEMSET c HC RET LOOP CPOST) as M1.
  exact (rv_cp_ok SK B LAWS TL MEMCPY c HC M1).
Qed.
End w.

Print Assumptions fuzz_recv_aproof.
