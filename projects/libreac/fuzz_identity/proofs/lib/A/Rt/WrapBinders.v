(* libreac/fuzz_identity, build asan (image A): the closer's three wrapper binders ASTRLEN, ASTRCMP and AMEMCHR, each as
   one lemma whose statement is the binder's type, proved from the wrapper walk's theorem at the applied core's record.

   The binder types are the A link's hypotheses (lib/A/Prog/IdentEntryLink.v:246, :247, :688), which the A closer
   lib/A/IdentTop.v (Section asan) discharges with the lemmas below, at every fx and rc:
     ASTRLEN (IdentEntryLink.v:246) : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
              @astrlen_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_strlen)
     ASTRCMP (IdentEntryLink.v:247) : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
              @astrcmp_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_strcmp)
     AMEMCHR (IdentEntryLink.v:688) : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
              @amemchr_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_memchr)
   with SEGSr / SIGMAr (IdentTop.v:141-142) the closer's form of the link's SEGS / SIGMA (IdentEntryLink.v:174, :176).
   IdentTop's IdentB is here the applied core's record (lib/A/AD2l.v:15, TfibB renamed IdentB). Each lemma
   is followed by a `Check` of it against that text, so a binder that moves fails this file.

   The arguments, checked by the `change` steps of each proof (closed conversions):
     segs   SEGSr rc = ident_segs = Asan.M.loaded_segments = AB1v.tfibsegs, the walks' segment list;
     B      IdentB, with AR_laws_ok (Reusable/YG0q.v:804) and TfibB_syms : TfibSyms IdentB (lib/A/AD2l.v);
     entry  SIGMAr rc IS_<x> = ident_sigma IS_<x> (lib/A/Prog/IdentAddr.v:29, :30, :24): strlen 0x4218c =
            StrlenDef.STRLEN_ENTRY, strcmp 0x42194 = StrcmpDef.STRCMP_ENTRY, memchr 0x421a4 = MemchrDef.MEMCHR_ENTRY
            (the trampolines).

   The walks (taken by path for this branch, record class TfibSyms):
     strlen  lib/A/Rt/Strlen.v strlen_icpt_contract
     strcmp  lib/A/Rt/Strcmp.v strcmp_icpt_contract, from the trampoline
             0x42194 (r_A_tramp)
     memchr  lib/A/Rt/Memchr.v memchr_icpt_contract

   Porting record (2026-10-28), what each walk is ported from:
     strlen: ported from proofs/coturn/FuzzStunClient/lib/VAsanIcStrlenWalk.v:819
       isl_run (c8557374ad2e), restated in cgif_file's contract form lib/YG0d.v:401-419 astrnlen_realizes without the
       n bound, at fuzz_identity's asan and asan-ubsan addresses.
     strcmp: ported from proofs/coturn/FuzzStunClient/lib/VAsanIcStrcmpWalk.v:1116 isc_run (c8557374ad2e),
       restated the same way.
     memchr: ported from cgif_file lib/A/AE6x.v memchr0_icpt_realizes (:453), relocated to
       fuzz_identity, then extended to the general case (any byte c, found or not found, NUL at k <= 16 with n = 17)
       from projects/leptonica/bilateral_fuzzer/proofs/lib/K5/A02/I_memchrw.v:100 imemchr_spec. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK04 YG00 YG0d YG0q YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym IdentSyms IdentList IdentPa IdentImg.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.A.AB1v
  OSSVerify.Proofs.libreac.fuzz_identity.lib.A.AF0m
  OSSVerify.Proofs.libreac.fuzz_identity.lib.A.AD2l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef StrcmpDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Strlen Strcmp Memchr.
Module RtStrlen := OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt.Strlen.
Module RtStrcmp := OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt.Strcmp.
Module RtMemchr := OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt.Memchr.
Open Scope Z_scope.

Local Notation SEGSr rc := (@pa_segs _ ident_listing (@PI_ident rc)).
Local Notation SIGMAr rc := (@pa_sigma _ ident_listing (@PI_ident rc)).

(* ASTRLEN, the A link's hypothesis at lib/A/Prog/IdentEntryLink.v:246. *)
Lemma astrlen_binder_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrlen_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_strlen).
Proof.
intros fx rc.
change (SEGSr rc) with tfibsegs.
change (SIGMAr rc IS___interceptor_trampoline_strlen) with STRLEN_ENTRY.
exact (RtStrlen.strlen_icpt_contract IdentB (AR_laws_ok tfibsegs IdentB) TfibB_syms).
Qed.
Check (astrlen_binder_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrlen_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_strlen)).

(* ASTRCMP, the A link's hypothesis at lib/A/Prog/IdentEntryLink.v:247. *)
Lemma astrcmp_binder_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrcmp_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_strcmp).
Proof.
intros fx rc.
change (SEGSr rc) with tfibsegs.
change (SIGMAr rc IS___interceptor_trampoline_strcmp) with STRCMP_ENTRY.
exact (RtStrcmp.strcmp_icpt_contract IdentB (AR_laws_ok tfibsegs IdentB) TfibB_syms).
Qed.
Check (astrcmp_binder_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrcmp_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_strcmp)).

(* AMEMCHR, the A link's hypothesis at lib/A/Prog/IdentEntryLink.v:688. *)
Lemma amemchr_binder_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@amemchr_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_memchr).
Proof.
intros fx rc.
change (SEGSr rc) with tfibsegs.
change (SIGMAr rc IS___interceptor_trampoline_memchr) with MEMCHR_ENTRY.
exact (RtMemchr.memchr_icpt_contract IdentB (AR_laws_ok tfibsegs IdentB) TfibB_syms).
Qed.
Check (amemchr_binder_A : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@amemchr_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IS___interceptor_trampoline_memchr)).
