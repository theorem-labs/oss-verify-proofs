(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan instance of musl's mread walk inside libreac/fuzz_pcap (libreac
   v1.9.0). The walk rmread_contract_proved is image-free, in lib/A/Stdio/PFmreadMW.v; this file
   applies it to the asan image at PMREAD = 0x8ea40 / TRAMP_MEMCPY = 0x51510 (lib/A/Stdio/
   PStdioImgA.v, the single home of pcap's asan stdio pcs; none is declared here). The asan-ubsan
   instance is in lib/B/Stdio/PFmreadMWB.v. The code, image-range and w+x facts are checked by
   computation on the image. Moved unchanged from PFmreadMW.v section 9 (a working branch
   77db13765bf). rule 24: no function proved (split of a proved file). *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PFmreadMW PStdioImgA.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
Import ListNotations.
(* lia guard: the Zify flag leak at YE2e.v:29 / AE2e.v:30 (~120 files) sets the euclidean-division flag to false globally *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The asan instance: the code, image-range and w+x facts by computation   *)
(* on the image. The image's mread holds the SAME 51 MR_CODE words as the  *)
(* asan-ubsan twin (keyed by symbol + offset on the image's own objdump:   *)
(* <mread> at 0x8ea40, <__interceptor_trampoline_memcpy> at 0x51510); only *)
(* the two jal words are its own (v1.9.0: 0xa6dc20ef / 0xa2dc20ef), since  *)
(* a jal carries its pc-relative offset: the proof reads them, and their    *)
(* offsets, from the image and Symbols.v, so a relink changes no line here. *)
(* ---------------------------------------------------------------------- *)
Definition mr_tbl_a : ctable := Eval vm_compute in build_table Asan.M.loaded_segments PMREAD 53 TEmpty.
Lemma mr_tbl_a_ok : table_ok Asan.M.loaded_segments mr_tbl_a.
Proof.
replace mr_tbl_a with (build_table Asan.M.loaded_segments PMREAD 53 TEmpty) by (vm_compute; reflexivity).
apply build_table_ok0. unfold PMREAD. lia.
Qed.

Lemma mread_code_asan : mread_code Asan.M.loaded_segments PMREAD TRAMP_MEMCPY.
Proof.
unfold mread_code, PMREAD, TRAMP_MEMCPY.
split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split.
- intros off w Hin. apply mr_tbl_a_ok. unfold MR_CODE in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; vm_compute; reflexivity|]). destruct Hin.
- intros off [-> | ->].
  + exists (Z_to_bv 32 ltac:(let v := eval vm_compute in (match fetch_word Asan.M.loaded_segments (Z_to_bv 64 (PMREAD + 0x64)) with
                    Some w => bv_unsigned w | None => 0 end) in exact v)),
      (Z_to_bv 21 ltac:(let i := eval vm_compute in ((TRAMP_MEMCPY - (PMREAD + 0x64)) mod 2 ^ 21) in exact i)).
    split; [apply mr_tbl_a_ok; vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|]. split; [vm_refl_bv | apply bv_eq; vm_compute; reflexivity].
  + exists (Z_to_bv 32 ltac:(let v := eval vm_compute in (match fetch_word Asan.M.loaded_segments (Z_to_bv 64 (PMREAD + 0xa4)) with
                    Some w => bv_unsigned w | None => 0 end) in exact v)),
      (Z_to_bv 21 ltac:(let i := eval vm_compute in ((TRAMP_MEMCPY - (PMREAD + 0xa4)) mod 2 ^ 21) in exact i)).
    split; [apply mr_tbl_a_ok; vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|]. split; [vm_refl_bv | apply bv_eq; vm_compute; reflexivity].
Qed.

Lemma mr_segs_low_asan : forall a, in_img Asan.M.loaded_segments a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
  (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) Asan.M.loaded_segments))
  by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ sg Hin).
remember (Z.of_N (seg_base sg)) as bb eqn:Eb. remember (Z.of_N (seg_size sg)) as zz eqn:Ez. clear Eb Ez.
vm_compute in H. unfold kLowMemEnd.
repeat (destruct H as [H|H]); try contradiction; injection H as <- <-; lia.
Qed.

Lemma mr_wx_asan : wx_segs_nowrap Asan.M.loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* What is left as a premise is the core's (AR_laws, the stream's image laws, the memcpy trampoline's
   contract), exactly what the composition passes to its program walks. *)
Theorem rmread_contract_asan : forall B K,
  AR_laws Asan.M.loaded_segments B -> asource_img_laws SK Asan.M.loaded_segments B K ->
  aintrin_realizes Asan.M.loaded_segments B OCpy TRAMP_MEMCPY ->
  rmread_contract Asan.M.loaded_segments B K PMREAD.
Proof.
intros B K LAWS ASIL MEMCPY.
exact (rmread_contract_proved Asan.M.loaded_segments B K PMREAD TRAMP_MEMCPY LAWS mr_segs_low_asan mr_wx_asan ASIL
  mread_code_asan MEMCPY).
Qed.
End I.
