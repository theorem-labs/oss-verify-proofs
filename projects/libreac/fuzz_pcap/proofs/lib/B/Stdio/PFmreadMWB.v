(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan-ubsan instance of musl's mread walk inside libreac/fuzz_pcap
   (libreac v1.9.0). The walk rmread_contract_proved is image-free, in lib/A/Stdio/PFmreadMW.v;
   this file applies it to the asan-ubsan image at PMREAD_U = 0x8e90c / TRAMP_MEMCPY_U = 0x51560
   (lib/B/Stdio/PStdioImgB.v, the single home of pcap's asan-ubsan stdio pcs; none is declared
   here). The asan instance is in lib/A/Stdio/PFmreadMWA.v; this file Requires neither it nor any
   asan image file. The code, image-range and w+x facts are checked by computation on the image.
   Moved unchanged from PFmreadMW.v section 9 (a working branch 77db13765bf).
   rule 24: no function proved (split of a proved file). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP09 YP02 YP03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PFmreadMW.
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
(* The asan-ubsan instance: the code, image-range and w+x facts by         *)
(* computation on the image. The image's mread holds the SAME 51 MR_CODE   *)
(* words as the asan twin (keyed by symbol + offset on the image's own     *)
(* objdump: <mread> at 0x8e90c, <__interceptor_trampoline_memcpy> at       *)
(* 0x51560); only the two jal words are its own (v1.9.0: 0xbf1c20ef /     *)
(* 0xbb1c20ef), since a jal carries its pc-relative offset: the proof     *)
(* reads them, and their offsets, from the image and Symbols.v.           *)
(* ---------------------------------------------------------------------- *)
Definition mr_tbl_u : ctable := Eval vm_compute in build_table AsanUbsan.M.loaded_segments PMREAD_U 53 TEmpty.
Lemma mr_tbl_u_ok : table_ok AsanUbsan.M.loaded_segments mr_tbl_u.
Proof.
replace mr_tbl_u with (build_table AsanUbsan.M.loaded_segments PMREAD_U 53 TEmpty) by (vm_compute; reflexivity).
apply build_table_ok0. unfold PMREAD_U. lia.
Qed.

Lemma mread_code_asan_ubsan : mread_code AsanUbsan.M.loaded_segments PMREAD_U TRAMP_MEMCPY_U.
Proof.
unfold mread_code, PMREAD_U, TRAMP_MEMCPY_U.
split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split.
- intros off w Hin. apply mr_tbl_u_ok. unfold MR_CODE in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; vm_compute; reflexivity|]). destruct Hin.
- intros off [-> | ->].
  + exists (Z_to_bv 32 ltac:(let v := eval vm_compute in (match fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 (PMREAD_U + 0x64)) with
                    Some w => bv_unsigned w | None => 0 end) in exact v)),
      (Z_to_bv 21 ltac:(let i := eval vm_compute in ((TRAMP_MEMCPY_U - (PMREAD_U + 0x64)) mod 2 ^ 21) in exact i)).
    split; [apply mr_tbl_u_ok; vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|]. split; [vm_refl_bv | apply bv_eq; vm_compute; reflexivity].
  + exists (Z_to_bv 32 ltac:(let v := eval vm_compute in (match fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 (PMREAD_U + 0xa4)) with
                    Some w => bv_unsigned w | None => 0 end) in exact v)),
      (Z_to_bv 21 ltac:(let i := eval vm_compute in ((TRAMP_MEMCPY_U - (PMREAD_U + 0xa4)) mod 2 ^ 21) in exact i)).
    split; [apply mr_tbl_u_ok; vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|]. split; [vm_refl_bv | apply bv_eq; vm_compute; reflexivity].
Qed.

Lemma mr_segs_low_asan_ubsan : forall a, in_img AsanUbsan.M.loaded_segments a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
  (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) AsanUbsan.M.loaded_segments))
  by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ sg Hin).
remember (Z.of_N (seg_base sg)) as bb eqn:Eb. remember (Z.of_N (seg_size sg)) as zz eqn:Ez. clear Eb Ez.
vm_compute in H. unfold kLowMemEnd.
repeat (destruct H as [H|H]); try contradiction; injection H as <- <-; lia.
Qed.

Lemma mr_wx_asan_ubsan : wx_segs_nowrap AsanUbsan.M.loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* What is left as a premise is the core's (AR_laws, the stream's image laws, the memcpy trampoline's
   contract), exactly what the composition passes to its program walks. *)
Theorem rmread_contract_asan_ubsan : forall B K,
  AR_laws AsanUbsan.M.loaded_segments B -> asource_img_laws SK AsanUbsan.M.loaded_segments B K ->
  aintrin_realizes AsanUbsan.M.loaded_segments B OCpy TRAMP_MEMCPY_U ->
  rmread_contract AsanUbsan.M.loaded_segments B K PMREAD_U.
Proof.
intros B K LAWS ASIL MEMCPY.
exact (rmread_contract_proved AsanUbsan.M.loaded_segments B K PMREAD_U TRAMP_MEMCPY_U LAWS
  mr_segs_low_asan_ubsan mr_wx_asan_ubsan ASIL mread_code_asan_ubsan MEMCPY).
Qed.
End I.
