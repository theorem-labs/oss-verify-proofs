(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the allocation-meter law for libreac/fuzz_pcap's READ stream.

   A COPY of the donor's `afile_meter` (cgif_file_fuzzer lib/YC5n.v:34-43, relocated at
   lib/Reusable/YC5n.v:34-43), with the donor text RENAMED ONLY:
     afile_meter -> asrc_file_meter,   mkAFM -> mkASFM,   afm_* -> asfm_*,
     FILE_BLOCK  -> SRC_FILE_BLOCK  (PSource.v: the 1304-byte block musl fmemopen mallocs for the
                                     FILE and its buffer; cgif's FILE_BLOCK is its fopen sink's).
   The donor's Section also carries `K : asink_syms`, but none of the three laws reads it, so it
   is not carried here: requiring a sink record would make a caller name one for a program that
   has no sink.

   WHY (a Theorem Labs lane, 21:53Z, for the open and the close lanes): afclose_source_spec's post has
   no meter fact, while the callers must give the harness mo_le across the whole call. The donor
   keeps that fact out of the spec, in this separate law, discharged once at the top by
   ameter_triv (cgif lib/A/ACke.v:33). One owner, so both lanes cite one name.

   STATEMENT ONLY: a Record of three laws, no lemma. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI00 YI04 YI09 YI08 YN3v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI5w YI5z YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YO07.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO08 YC5d YC7x YC21.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* SK is EXPLICIT (a Theorem Labs lane, 21:58Z), unlike the donor's {SK}: lib/Reusable/YI5b.v:12
   declares a #[global] instance for the PLAIN image's head, so an implicit SK could be filled
   silently with the wrong head by a consumer whose closure reaches YI5b. *)
Context (SK : YI16.sink_head).
Section d.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.

Record asrc_file_meter : Prop := mkASFM {
asfm_k0 : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md',
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' 0 -> mo_le MT S S' 0;
asfm_open : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' f,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' 1 ->
ablocks B ly' S' = ablocks B ly S ++ [(f, SRC_FILE_BLOCK)] -> mo_le MT S S' (mo_malloc MT SRC_FILE_BLOCK);
asfm_close : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' f rest,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' 2 ->
Permutation (ablocks B ly S) ((f, SRC_FILE_BLOCK) :: rest) -> Permutation (ablocks B ly' S') rest ->
mo_le MT S S' (mo_free MT + mo_free MT) }.

End d.
End c.

(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the
   positional SK would land on the segs argument and this file would stop compiling. *)
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => asrc_file_meter (rc:=rc) SK).
