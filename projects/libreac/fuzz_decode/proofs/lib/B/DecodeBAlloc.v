(* libreac/fuzz_decode image B (fuzz_decode.asan-ubsan): a Theorem Labs lane's CLOSED primary-size Allocate, relocated onto this
   image (lib/B/AGtopcgifC.v and its Require closure, from a working branch 95e6f1d72b6; provenance in
   provenance/alloc-reloc/B/), in the exact form decode's composition consumes: DecodeBClose.v's premise row
   H_CALLOC_ALLOCATE, `forall (fx : YK11.FPState) (rc : YM05.RunCeil), @decode_aalloc_B fx rc B`.

   Rule 24: no function is proved here.  The theorem applies the already-proved relocated top at the image's record.

   - [dec_b_aalloc]: AGtopcgifC.aalloc_prim_realizes_cgif_closed at can_fill CF_CALLOC = 0 is
     AllocGcgif.aalloc_prim_realizes_cgif B 0, which is, by conversion, lib/A/DecodeCalloc.v's decode_aalloc_B B
     (Reusable/YGCalloc.v aalloc_realizes_cgif, already the primary form YGAlloc.aalloc_prim_realizes): the same
     statement at the same segments (lib/B/YB1v.v tfibsegs = lib/A/DecodeTFIB.v decodesegsB0 =
     AsanUbsan.M.loaded_segments), the same universe (fun tr _ => In tr (as_universe B)), Allocate 0x31298 =
     DEC_B_allocate, TFIB_OOM 0x1235a0 = DEC_B_oom, al 8 = ALLOC_ALIGN, atp 1 = AT_FROM_MALLOC.  The two allocator
     relations agree by conversion too: a Theorem Labs lane's AllocGcgif.ARX_cgif B inst := inst = TFIB_INST /\ AR tfibsegs B ..,
     decode's YGCalloc.ARX_cgif decodesegsB0 B DEC_B_instance inst := inst = DEC_B_instance /\ AR decodesegsB0 B ..,
     with TFIB_INST = DEC_B_instance = 0x9dcd8.
   - Premises: the image's symbol record TfibSyms B (lib/B/YF0m.v), and the depot hash of B being the depot's own hash
     function, forall t, as_dhash B t = tfib_dhash t (Reusable/YF0p.v).  The second is not a field of TfibSyms (its
     ts_hash fixes as_dhash on the two start-up traces TFIB_TR0 0 / 1 only); lib/B/YFem.v tfib_depot_ok needs it for
     every trace to give the closed top's second premise tfib_depot_spec B (lib/B/YFl0.v).
   - [dec_b_aalloc_TfibB]: the same at the image's own record TfibB (lib/B/YD2l.v), whose as_dhash is tfib_dhash by
     definition, so no premise remains. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YGCalloc YF0p.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YF0m YFl0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YFem YD2l AGtopcgifC.
Import ListNotations.
Open Scope Z_scope.

(* H_CALLOC_ALLOCATE, at any record of image B whose depot hash is the depot's. *)
Theorem dec_b_aalloc : forall B : asyms, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
forall (fx : YK11.FPState) (rc : YM05.RunCeil), @decode_aalloc_B fx rc B.
Proof.
intros B TS HDH fx rc.
exact (@AGtopcgifC.aalloc_prim_realizes_cgif_closed fx rc B TS (YFem.tfib_depot_ok B TS HDH) CF_CALLOC (or_introl eq_refl)).
Qed.

(* At the image's own record TfibB. *)
Lemma TfibB_dhash : forall t, as_dhash YD2l.TfibB t = tfib_dhash t.
Proof. intros t. reflexivity. Qed.
Theorem dec_b_aalloc_TfibB : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @decode_aalloc_B fx rc YD2l.TfibB.
Proof. exact (dec_b_aalloc YD2l.TfibB YD2l.TfibB_syms TfibB_dhash). Qed.
