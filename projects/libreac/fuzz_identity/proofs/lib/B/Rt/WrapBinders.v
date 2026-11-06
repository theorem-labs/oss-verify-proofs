(* libreac/fuzz_identity, build asan-ubsan (image B): the closer's three wrapper binders ASTRLEN, ASTRCMP and AMEMCHR,
   each as one lemma whose statement is the binder's type, proved from the wrapper walk's theorem at the applied core's
   record.

   The binder types are the B link's hypotheses (lib/B/Prog/IdentEntryLink.v:252, :253, :706), which the closer
   lib/B/IdentTopB.v (Section asan_ubsan) discharges with the lemmas below, at every fx and rc:
     ASTRLEN (IdentEntryLink.v:252) : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
              @astrlen_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_strlen)
     ASTRCMP (IdentEntryLink.v:253) : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
              @astrcmp_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_strcmp)
     AMEMCHR (IdentEntryLink.v:706) : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
              @amemchr_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_memchr)
   with SEGSr / SIGMAr (IdentTopB.v:161-162) the closer's form of the link's SEGS / SIGMA (IdentEntryLink.v:179,
   :181). IdentB is the applied B core's record (lib/ReusableB/YD2l.v:12, cgif's TfibB renamed IdentB), as in
   IdentTopB.v. Each lemma is followed by a `Check` of it against that text, so a binder that moves fails this file.

   The arguments, checked by the `change` steps of each proof (closed conversions):
     segs   SEGSr rc = identb_segs = AsanUbsan.M.loaded_segments = YB1v.tfibsegs, the walks' segment list;
     B      IdentB, with AR_laws_ok (Reusable/YG0q.v:804) and TfibB_syms : TfibSyms IdentB (lib/ReusableB/YD2l.v);
     entry  SIGMAr rc IB_<x> = identb_sigma IB_<x> (lib/B/Prog/IdentBAddr.v): strlen 0x421f4 = StrlenDef.STRLEN_ENTRY,
            strcmp 0x421fc = StrcmpDef.STRCMP_ENTRY, memchr 0x4220c = MemchrDef.MEMCHR_ENTRY (the trampolines).

   The walks (taken by path for this branch, record class TfibSyms):
     strlen  lib/B/Rt/Strlen.v strlen_icpt_contract
     strcmp  lib/B/Rt/Strcmp.v strcmp_icpt_contract. It starts at the
             trampoline 0x421fc (`j 0x427b0`), not at the interceptor: its proof is strcmp_srr at STRCMP_TRAMP with
             r_A_tramp, the symbolic run from 0x421fc that reaches the same loop-head state eA as the run from
             ___interceptor_strcmp 0x427b0 (r_A_icpt); StrcmpTbl.v's tbl_sc holds the trampoline word (tbl_sc_probe).
             strcmp_icpt_at is the interceptor-entry corollary and is not used here.
     memchr  lib/B/Rt/Memchr.v memchr_icpt_contract

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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBImg.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YB1v
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YF0m
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YD2l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Strlen Strcmp Memchr.
Module RtStrlen := OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt.Strlen.
Module RtStrcmp := OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt.Strcmp.
Module RtMemchr := OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt.Memchr.
Open Scope Z_scope.

Local Notation SEGSr rc := (@pa_segs _ identb_listing (@PI_identb rc)).
Local Notation SIGMAr rc := (@pa_sigma _ identb_listing (@PI_identb rc)).

(* ASTRLEN, the B link's hypothesis at lib/B/Prog/IdentEntryLink.v:252. *)
Lemma astrlen_binder_B : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrlen_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_strlen).
Proof.
intros fx rc.
change (SEGSr rc) with tfibsegs.
change (SIGMAr rc IB___interceptor_trampoline_strlen) with STRLEN_ENTRY.
exact (RtStrlen.strlen_icpt_contract IdentB (AR_laws_ok tfibsegs IdentB) TfibB_syms).
Qed.
Check (astrlen_binder_B : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrlen_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_strlen)).

(* ASTRCMP, the B link's hypothesis at lib/B/Prog/IdentEntryLink.v:253. *)
Lemma astrcmp_binder_B : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrcmp_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_strcmp).
Proof.
intros fx rc.
change (SEGSr rc) with tfibsegs.
change (SIGMAr rc IB___interceptor_trampoline_strcmp) with STRCMP_ENTRY.
exact (RtStrcmp.strcmp_icpt_contract IdentB (AR_laws_ok tfibsegs IdentB) TfibB_syms).
Qed.
Check (astrcmp_binder_B : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@astrcmp_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_strcmp)).

(* AMEMCHR, the B link's hypothesis at lib/B/Prog/IdentEntryLink.v:706. *)
Lemma amemchr_binder_B : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@amemchr_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_memchr).
Proof.
intros fx rc.
change (SEGSr rc) with tfibsegs.
change (SIGMAr rc IB___interceptor_trampoline_memchr) with MEMCHR_ENTRY.
exact (RtMemchr.memchr_icpt_contract IdentB (AR_laws_ok tfibsegs IdentB) TfibB_syms).
Qed.
Check (amemchr_binder_B : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@amemchr_realizes fx rc (SEGSr rc) IdentB (SIGMAr rc IB___interceptor_trampoline_memchr)).
