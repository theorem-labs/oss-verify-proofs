(* libreac/fuzz_boxreg, build asan-ubsan: boxreg's frozen strncmp contract for image B (lib/B/Rt/StrncmpDefB.v
   abstrncmp_realizes, pa ce9883a29ab) at the trampoline ABSTRNCMP_ENTRY 0x41458, from a Theorem Labs lane's proof relocated
   unchanged onto image B (lib/B/FMstrncmp.v astrncmp_holds; a working branch 445e498a469; SHARED-WALKS.md
   row "strncmp (interceptor + musl)"). Twin of lib/A/Rt/Strncmp.v (a working branch
   e23152c688f).
   This is the one B adapter (a Theorem Labs lane 04:46Z, option B). astrncmp_holds states fm's text, which
   lib/B/Rt/StrncmpFmhB.v carries verbatim: fm's ecall_pre_k and cstr_ok write `alloc_ceiling`, while StrncmpDefB's
   abfm_ecall_pre_k and abfm_cstr_ok write `ASAN_CEIL`. ASAN_CEIL is alloc_ceiling by definition (YG0f.v:15), so the
   two statements are convertible. The proof unfolds both sides, unfolds ASAN_CEIL, and uses astrncmp_holds as it
   stands.
   At a call site: the two read-only premises (abfm_rom_viewN / abfm_rom_viewO) come from a Theorem Labs lane's
   lib/B/Rt/StrncmpViewB.v (abfm_rom_viewN_of_arodata; abfm_rom_viewO_of_AR, whose abfm_ro_owned_pinned premise
   a Theorem Labs lane discharges for the asyms instance in lib/B/Rt/StrncmpViewBInst.v, a working branch
   26f9713ba9c), and the two string premises from lib/B/Rt/StrncmpSiteB.v. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require StrncmpDefB StrncmpFmhB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require FMstrncmp.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : BoxregSyms B.

Theorem boxreg_abstrncmp_B : StrncmpDefB.abstrncmp_realizes tfibsegs B StrncmpDefB.ABSTRNCMP_ENTRY.
Proof.
  pose proof (FMstrncmp.astrncmp_holds B LAWS TB) as H.
  unfold StrncmpFmhB.astrncmp_realizes, StrncmpFmhB.ecall_pre_k, StrncmpFmhB.cstr_ok, StrncmpFmhB.cstr,
    StrncmpFmhB.rt_post_ro in H.
  unfold StrncmpDefB.abstrncmp_realizes, StrncmpDefB.abfm_ecall_pre_k, StrncmpDefB.abfm_cstr_ok, StrncmpDefB.abfm_cstr,
    StrncmpDefB.abfm_rt_post_ro, ASAN_CEIL.
  exact H.
Qed.
End s.

Print Assumptions boxreg_abstrncmp_B.
