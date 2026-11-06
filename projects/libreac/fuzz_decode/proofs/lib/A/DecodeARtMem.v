(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v (origin/ossv/recipes
   c8557374ad2e) :145-158 tfibX_AMEMSET / tfibX_AMEMCPY / tfibX_ABCMP, and lib/A/AD2m.v tfib_AICPY, for
   libreac/fuzz_decode's ASan image (image A); module paths and names changed. *)
(* Four runtime contracts of fuzz_decode image A's close (rule 24: no function proved; each lemma is an instance of a
   contract of the relocated image-A core, a working branch e2ad4d7aa34).

   Each lemma's statement is the text of the lib/A/DecodeClose.v Section hypothesis of the same name
   (a working branch 45061c42804, :231-241), with the Section's two names bound as
   DecodeClose.v binds or intends them:
   - segs is decodesegs0 (DecodeClose.v:92, lib/A/DecodeTFIB.v:19), the core's tfibsegs (lib/A/AB1v.v:13): both are
     the image's Asan.M.loaded_segments;
   - B is the core's symbol record GrantB (lib/A/AD2l.v:16), the record DecodeClose.v:116 names (donor TfibB, owner
     the relocated core). The core's contracts take GrantSyms B (lib/A/AF0m.v:399); GrantB_syms (lib/A/AD2l.v:72)
     discharges it, and AR_laws_ok (lib/Reusable/YG0q.v:804) discharges AR_laws.
   No other Section hypothesis of DecodeClose.v is used.

   The contracts' pcs are the listing's (lib/A/Prog/DecodeAddr.v decode_sigma), checked by computation below:
   asan_memset 0x510ac (lib/A/AE2r.v:568), asan_memcpy 0x50c10 (lib/A/AE2q.v:145), the bcmp interceptor 0x41558
   (lib/A/AE2s.v:712). The memcpy interceptor's contract is stated at pc_wrap_memcpy (as_code B) itself
   (lib/A/AD2m.v:18 tfib_AICPY; 0x50c0c in lib/A/AF0l.v:15 Tfib_code). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0n YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v AF0l AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AD2m AE2r AE2q AE2s.
Open Scope Z_scope.

#[local] Abbreviation segs := decodesegs0.
#[local] Abbreviation B := GrantB.

(* The listing's addresses of the three entries are the pcs the core's contracts are stated at. *)
Remark dec_A_asan_memset_pc : decode_sigma DS___asan_memset = 0x510ac.
Proof. reflexivity. Qed.
Remark dec_A_asan_memcpy_pc : decode_sigma DS___asan_memcpy = 0x50c10.
Proof. reflexivity. Qed.
Remark dec_A_bcmp_pc : decode_sigma DS___interceptor_trampoline_bcmp = 0x41558.
Proof. reflexivity. Qed.

(* H_RT_MEMCPY_WRAP (DecodeClose.v:231): lib/A/AD2m.v:18 tfib_AICPY at GrantB. *)
Lemma H_RT_MEMCPY_WRAP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
  intros rc fx. exact (AD2m.tfib_AICPY B GrantB_syms).
Qed.

(* H_RT_ASAN_MEMSET (DecodeClose.v:235): lib/A/AE2r.v:568 asan_memset_realizes at GrantB (cgif ACed.v:145). *)
Lemma H_RT_ASAN_MEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OSet (decode_sigma DS___asan_memset).
Proof.
  intros rc fx. rewrite dec_A_asan_memset_pc.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (AE2r.asan_memset_realizes B (AR_laws_ok tfibsegs B) GrantB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

(* H_RT_ASAN_MEMCPY (DecodeClose.v:237): lib/A/AE2q.v:145 asan_memcpy_realizes at GrantB (cgif ACed.v:150). *)
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (decode_sigma DS___asan_memcpy).
Proof.
  intros rc fx. rewrite dec_A_asan_memcpy_pc.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
  exact (AE2q.asan_memcpy_realizes B (AR_laws_ok tfibsegs B) GrantB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

(* H_RT_BCMP (DecodeClose.v:240): lib/A/AE2s.v:712 bcmp_icpt_contract at GrantB (cgif ACed.v:157-158). *)
Lemma H_RT_BCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @abcmp_realizes fx rc segs B (decode_sigma DS___interceptor_trampoline_bcmp).
Proof.
  intros rc fx. rewrite dec_A_bcmp_pc.
  exact (AE2s.bcmp_icpt_contract B (AR_laws_ok tfibsegs B) GrantB_syms).
Qed.
