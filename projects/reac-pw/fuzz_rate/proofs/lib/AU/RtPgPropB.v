(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgProp.v at 533bf30ff015 for image B
   (fuzz_rate.asan-ubsan): image B's pieces, pcs and files; the latch has two entries; the shape-7 piece also takes
   pod_write_ent's contract, and pab_piece_int7_B discharges it by pod_write_ent's own walk (lib/AU/PweRun.v). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the four pieces of one turn of the property loop
   of LLVMFuzzerTestOneInput (0x8076c) as lib/AU/RtPgSegB.v states them, gathered for the assembly. Proves no function
   (kind: segment lemma).
     pab_piece_sel   : rsb_piece_W4_sel_stmt    N 0x80fb4 -> SEL7 0x80ff4 / SELK 0x810a4      (lib/AU/RtPgPropBSel.v)
     pab_piece_int7  : rsb_piece_W4_int7_stmt   SEL7 0x80ff4 -> LATCH7 0x8257c                (lib/AU/RtPgPropBInt7.v)
     pab_piece_key   : rsb_piece_W4_key_stmt    SELK 0x810a4 -> SELS 0x81210 / SELI 0x82398   (lib/AU/RtPgPropBKey.v)
     pab_piece_latch : rsb_piece_W4_latch_stmt  LATCH 0x82578 / LATCH7 0x8257c -> N 0x80fb4 / P1 0x82688
                                                                                              (lib/AU/RtPgPropBLatch.v)
   Each takes the Section hypotheses MTL (ameter_laws) and LAWS (AR_laws of image B); pab_piece_int7 also AMEMSET,
   the __asan_memset contract at 0x51d54 (YG0d.aintrin_realizes OSet), and PWE, pod_write_ent's contract at 0x83cc4
   (lib/AU/PweSpec.v pod_write_ent_specX), which the shape-7 pod's body calls. pab_piece_int7_B is pab_piece_int7 with
   PWE given by lib/AU/PweRun.v's pod_write_ent_B, so its premises are those of the other pieces, AMEMSET, the
   __asan_memcpy contract at 0x518b8 and the symbol record's two cells pod_write_ent_B names. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB PweSpec PweKit PweRun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Export RtPgPropBLatch RtPgPropBSel RtPgPropBInt7 RtPgPropBKey.
Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgStepsB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Corollary pab_piece_int7_B : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
  (B : asyms) (MT : ameter_ops),
  ameter_laws MT -> AR_laws rsegs B -> aintrin_realizes rsegs B OSet 0x51d54 ->
  aintrin_realizes rsegs B OCpy PWE_MEMCPY -> as_got_shadow B = PWE_GOT -> as_shadow_cell B = PWE_CELL ->
  rsb_piece_W4_int7_stmt rsegs B MT.
Proof.
intros fx rc SK B MT MTL LAWS AMEMSET AMEMCPY HBgot HBcell.
exact (pab_piece_int7 B MT MTL LAWS AMEMSET (pod_write_ent_B B MT MTL HBgot HBcell AMEMCPY AMEMSET)).
Qed.

Print Assumptions pab_piece_sel.
Print Assumptions pab_piece_int7.
Print Assumptions pab_piece_int7_B.
Print Assumptions pab_piece_key.
Print Assumptions pab_piece_latch.
