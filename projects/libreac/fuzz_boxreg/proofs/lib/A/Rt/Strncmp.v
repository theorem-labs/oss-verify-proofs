(* libreac/fuzz_boxreg, build asan: boxreg's frozen strncmp contract (lib/A/Rt/StrncmpDef.v astrncmp_realizes, pa
   ce9883a29ab) at the trampoline STRNCMP_ENTRY 0x413f8, from a Theorem Labs lane's proof relocated unchanged
   (lib/A/FMstrncmp.v astrncmp_holds; a working branch 445e498a469; SHARED-WALKS.md row "strncmp
   (interceptor + musl)").
   This is the one adapter (a Theorem Labs lane 04:46Z, option B). astrncmp_holds states fm's text, which lib/A/Rt/StrncmpFmh.v
   carries verbatim: fm's ecall_pre_k and cstr_ok write `alloc_ceiling`, while StrncmpDef's fm_ecall_pre_k and
   fm_cstr_ok write `ASAN_CEIL`. ASAN_CEIL is alloc_ceiling by definition (YG0f.v:15), so the two statements are
   convertible. The proof unfolds both sides, unfolds ASAN_CEIL, and uses astrncmp_holds as it stands.
   Why fm's names are not aliases of StrncmpDef's: lia treats ASAN_CEIL and alloc_ceiling as different atoms, so
   fm's unchanged proof stops at FMrt_pre.v:310 over StrncmpDef's text (diagnostic build
   boxreg-strncmp build-20261029T044600Z.log).
   The two read-only premises (fm_rom_viewN / fm_rom_viewO) come at a call site from lib/A/Rt/StrncmpView.v
   (a Theorem Labs lane), and the two string premises from lib/A/Rt/StrncmpSite.v. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require StrncmpDef StrncmpFmh.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require FMstrncmp.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : BoxregSyms B.

Theorem boxreg_astrncmp_A : StrncmpDef.astrncmp_realizes tfibsegs B StrncmpDef.STRNCMP_ENTRY.
Proof.
  pose proof (FMstrncmp.astrncmp_holds B LAWS TB) as H.
  unfold StrncmpFmh.astrncmp_realizes, StrncmpFmh.ecall_pre_k, StrncmpFmh.cstr_ok, StrncmpFmh.cstr,
    StrncmpFmh.rt_post_ro in H.
  unfold StrncmpDef.astrncmp_realizes, StrncmpDef.fm_ecall_pre_k, StrncmpDef.fm_cstr_ok, StrncmpDef.fm_cstr,
    StrncmpDef.fm_rt_post_ro, ASAN_CEIL.
  exact H.
Qed.
End s.

Print Assumptions boxreg_astrncmp_A.
