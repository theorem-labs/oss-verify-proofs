(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan-ubsan instance of musl's fread walk inside libreac/fuzz_pcap
   (libreac v1.9.0). The walk frd_walk is image-free, in lib/A/Stdio/PFreadMW.v; this file applies
   it to the asan-ubsan image at PFREAD_U = 0x8ed28, with the callee entries PTOREAD_U /
   TRAMP_MEMCPY_U (all from lib/B/Stdio/PStdioImgB.v, the single home of pcap's asan-ubsan stdio
   pcs; none is declared here). The asan instance is in lib/A/Stdio/PFreadMWA.v; this file Requires
   neither it nor any asan image file. Moved unchanged from PFreadMW.v (a working branch
   6e255f97e0c). rule 24: no function proved (split of a proved file). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal YC85G.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PSourceFrame PFreadArith PFreadCall PFreadPost PFreadMW.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PStdioImgB.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
Import ListNotations.
(* lia guard: the core's Zify flag leak (YE2e.v:29 / AE2e.v:30, ~120 files) sets the euclidean-division flag to false globally *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The image instance's certificate: the listing's words at the image's    *)
(* own addresses, checked by computation against the image's own loaded   *)
(* segments.                                                              *)
(* ---------------------------------------------------------------------- *)
Definition frd_tbl_asan_ubsan : ctable := Eval vm_compute in build_table AsanUbsan.M.loaded_segments PFREAD_U 79 TEmpty.
Lemma frd_tbl_asan_ubsan_eq : frd_tbl_asan_ubsan = build_table AsanUbsan.M.loaded_segments PFREAD_U 79 TEmpty.
Proof. vm_cast_no_check (eq_refl frd_tbl_asan_ubsan). Qed.
Lemma frd_tbl_asan_ubsan_ok : table_ok AsanUbsan.M.loaded_segments frd_tbl_asan_ubsan.
Proof. rewrite frd_tbl_asan_ubsan_eq. apply build_table_ok0. cbv. discriminate. Qed.
Lemma frd_cert_asan_ubsan : pi_check fsym (clookup frd_tbl_asan_ubsan) (frd_val PFREAD_U) (frd_sigma TRAMP_MEMCPY_U PTOREAD_U) frd_listing = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The instance. It takes the facts the composition supplies about its    *)
(* image (the allocator relation's laws, the image below kLowMemEnd, the  *)
(* segment layout, mread's entry, the read stream's image laws) and the   *)
(* three callee contracts at the image's own addresses; the listing's     *)
(* certificate, the code table and the base facts are discharged here.    *)
(* ---------------------------------------------------------------------- *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Theorem rfread_contract_asan_ubsan : forall (B : asyms) (K : asource_syms),
  AR_laws AsanUbsan.M.loaded_segments B ->
  (forall a, in_img AsanUbsan.M.loaded_segments a -> 0 <= a < kLowMemEnd) ->
  wx_segs_nowrap AsanUbsan.M.loaded_segments ->
  0 <= as_read K < 2 ^ 64 /\ as_read K mod 2 = 0 ->
  asource_img_laws SK AsanUbsan.M.loaded_segments B K ->
  aintrin_realizes AsanUbsan.M.loaded_segments B OCpy TRAMP_MEMCPY_U ->
  rtoread_contract AsanUbsan.M.loaded_segments B K PTOREAD_U ->
  rmread_contract AsanUbsan.M.loaded_segments B K (as_read K) ->
  rfread_contract AsanUbsan.M.loaded_segments B K PFREAD_U.
Proof.
intros B K LAWS Hlow Hwx Hmr ASIL HMC HTR HMR.
pose proof (frd_val_ok PFREAD_U ltac:(unfold PFREAD_U; lia)) as (HB & Hvr).
change PFREAD_U with (frd_val PFREAD_U A_TEXT).
apply (frd_walk AsanUbsan.M.loaded_segments B LAWS Hlow Hwx K frd_tbl_asan_ubsan frd_tbl_asan_ubsan_ok
  (frd_val PFREAD_U) (frd_sigma TRAMP_MEMCPY_U PTOREAD_U) frd_cert_asan_ubsan HB Hvr).
all: first [ exact Hmr | exact ASIL | exact HMC | exact HTR | exact HMR | (cbv; discriminate) ].
Qed.
End inst.
