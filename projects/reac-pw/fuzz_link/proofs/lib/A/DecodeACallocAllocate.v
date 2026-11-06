(* libreac/fuzz_decode image A (fuzz_decode.asan), composition row H_CALLOC_ALLOCATE: the Allocator::Allocate contract the
   calloc walk consumes (lib/A/DecodeCalloc.v decode_aalloc_A), from a Theorem Labs lane's CLOSED primary-size Allocate relocated onto
   this image (lib/A/AGtopcgifC.v and its Require closure, from a working branch 95e6f1d72b6; provenance in
   provenance/alloc-reloc/A/).  Only the record-generic lemma is kept here, over any B with PcapSyms B and the record's
   depot hash; reac-pw/fuzz_link applies it in lib/A/LinkACalloc.v.

   Rule 24: no function is proved here.  AGtopcgifC.aalloc_prim_realizes_cgif_closed at can_fill CF_CALLOC = 0 is
   AllocGcgif.aalloc_prim_realizes_cgif B 0, which is, by conversion, decode_aalloc_A B: the same
   YGAlloc.aalloc_prim_realizes at the same segments (tfibsegs = tfibsegs = Asan.M.loaded_segments), Allocate
   0x324b0 = DEC_A_allocate, TFIB_INST 0xa6dd8 = DEC_A_instance, TFIB_OOM 0x12c6a0 = DEC_A_oom, al 8 = ALLOC_ALIGN,
   atp 1 = AT_FROM_MALLOC.  The depot premise is lib/A/AFem.v tfib_depot_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YGCalloc YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AFl0 AB1v DecodeCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AFem AllocGcgif AGtopcgifC.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* From the record: any B with the image's symbol record and its depot hash. *)
Theorem decode_aalloc_A_of_record : forall B, PcapSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
decode_aalloc_A B.
Proof.
intros B TS HDH.
exact (AGtopcgifC.aalloc_prim_realizes_cgif_closed B TS (AFem.tfib_depot_ok B TS HDH) CF_CALLOC (or_introl eq_refl)).
Qed.
End a.
