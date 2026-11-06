(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v (origin/ossv/recipes
   c8557374ad2e) :145-158 tfibX_AMEMSET / tfibX_AMEMCPY / tfibX_ABCMP, and lib/YD2m.v tfib_AICPY, for
   libreac/fuzz_decode's ASan+UBSan image (image B), in the form of image A's lib/A/DecodeARtMem.v
   (a working branch ef8bb79a22c); module paths and names changed. *)
(* Four runtime contracts of fuzz_decode image B's close (rule 24: no function proved; each lemma is an instance of a
   contract of the relocated image-B core, a working branch). The contracts of record are
   the rows '__wrap_memcpy trampoline + ___interceptor_memcpy', '__asan_memcpy / __asan_memset' and 'bcmp / memcmp
   interceptor contracts' of SHARED-WALKS.md (cgif's released core, relocated).

   Each lemma's statement is the text of the lib/B/DecodeBClose.v Section hypothesis of the same name
   (a working branch 45061c42804, :225-235), with the Section's two names bound as the
   composition binds them:
   - segs is decodesegsB0 (DecodeBClose.v:92, lib/A/DecodeTFIB.v:27), the core's tfibsegs (lib/B/YB1v.v:11): both are
     the image's AsanUbsan.M.loaded_segments;
   - B is the image's symbol record TfibB (lib/B/YD2l.v:12), the record the composition binds DecodeBClose.v:117's
     Section variable B to (donor lib/YD2l.v TfibB). The core's contracts take TfibSyms B (lib/B/YF0m.v:321);
     TfibB_syms (lib/B/YD2l.v:68) discharges it, and AR_laws_ok (lib/Reusable/YG0q.v:804) discharges AR_laws.
   No other Section hypothesis of DecodeBClose.v is used.

   The contracts' pcs are the listing's (lib/B/Prog/DecodeBAddr.v decodeb_sigma), checked by computation below:
   asan_memset 0x510f8 (lib/B/YE2r.v:568), asan_memcpy 0x50c5c (lib/B/YE2q.v:145), the bcmp interceptor 0x415a4
   (lib/B/YE2s.v:711). The memcpy interceptor's contract is stated at pc_wrap_memcpy (as_code B) itself
   (lib/B/YD2m.v:16 tfib_AICPY; 0x50c58 in lib/B/YF0l.v:14 Tfib_code). aintrin_realizes OSet orders the premises
   dest_ok, amem_range, range_addressable, shadow_hull_vis, then OSet's arm of the op match (True); the core's
   asan_memset_realizes orders them dest_ok, range_addressable, shadow_hull_vis, amem_range, with no True premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0n YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YF0l YF0m YD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YD2m YE2r YE2q YE2s.
Open Scope Z_scope.

#[local] Abbreviation segs := decodesegsB0.
#[local] Abbreviation B := TfibB.

(* The listing's addresses of the three entries are the pcs the core's contracts are stated at. *)
Remark dec_B_asan_memset_pc : decodeb_sigma DB___asan_memset = 0x510f8.
Proof. reflexivity. Qed.
Remark dec_B_asan_memcpy_pc : decodeb_sigma DB___asan_memcpy = 0x50c5c.
Proof. reflexivity. Qed.
Remark dec_B_bcmp_pc : decodeb_sigma DB___interceptor_trampoline_bcmp = 0x415a4.
Proof. reflexivity. Qed.

(* H_RT_MEMCPY_WRAP (DecodeBClose.v:225): lib/B/YD2m.v:16 tfib_AICPY at TfibB. *)
Lemma H_RT_MEMCPY_WRAP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
  intros rc fx. exact (YD2m.tfib_AICPY B TfibB_syms).
Qed.

(* H_RT_ASAN_MEMSET (DecodeBClose.v:229): lib/B/YE2r.v:568 asan_memset_realizes at TfibB (cgif ACed.v:145). *)
Lemma H_RT_ASAN_MEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset).
Proof.
  intros rc fx. rewrite dec_B_asan_memset_pc.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (YE2r.asan_memset_realizes B (AR_laws_ok tfibsegs B) TfibB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

(* H_RT_ASAN_MEMCPY (DecodeBClose.v:231): lib/B/YE2q.v:145 asan_memcpy_realizes at TfibB (cgif ACed.v:150). *)
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (decodeb_sigma DB___asan_memcpy).
Proof.
  intros rc fx. rewrite dec_B_asan_memcpy_pc.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
  exact (YE2q.asan_memcpy_realizes B (AR_laws_ok tfibsegs B) TfibB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

(* H_RT_BCMP (DecodeBClose.v:234): lib/B/YE2s.v:711 bcmp_icpt_contract at TfibB (cgif ACed.v:157-158). *)
Lemma H_RT_BCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @abcmp_realizes fx rc segs B (decodeb_sigma DB___interceptor_trampoline_bcmp).
Proof.
  intros rc fx. rewrite dec_B_bcmp_pc.
  exact (YE2s.bcmp_icpt_contract B (AR_laws_ok tfibsegs B) TfibB_syms).
Qed.
