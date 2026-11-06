(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:156-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-277 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACim.v:270-271 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530, 1556-1561 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D4.v; 11 of its 49 lines of code are new or changed and 1040 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D4_hand_frame_read.v; 30 of its 67 lines of code are new or changed and 12 lines of the source are left out. *)
(* d4h_block_read: the four read premises of the wrappers (src_ok, amem_range, range_addressable,
   shadow_hull_vis) for m bytes inside a live heap block (p, n). The facts are AR_blocks_law
   (in_app p (req_size n)) and AR_shadow_law (block_shadow and shadow_hull_vis of the whole block),
   lib/Reusable/YG0d.v. The m bytes end at or before the block's last byte, so no byte past the block is read. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_D4_hand_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The shadow hull of a sub-range is inside the shadow hull of the range. *)
Lemma d4bl_hull_sub : forall (rd : Z -> option Z) x N a m,
  shadow_hull_vis rd x N -> x <= a -> a + m <= x + N -> 0 < m -> shadow_hull_vis rd a m.
Proof.
intros rd x N a m H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x a 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (a + m - 1) (x + N - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + a / 8) 8 ltac:(lia) ltac:(lia)) as M1.
pose proof (Z.div_le_mono (SHADOW_OFF + (a + m - 1) / 8) (SHADOW_OFF + (x + N - 1) / 8) 8
  ltac:(lia) ltac:(lia)) as M2.
clear - Hs M1 M2. lia.
Qed.

(* A live block's size n is at most its request size, and the request size is at least 1. *)
Lemma d4bl_req_size : forall n, 0 <= n -> n <= req_size n /\ 1 <= req_size n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
Section c.
Variable B : asyms.

Lemma d4h_block_read : d4h_block_read_stmt B.
Proof.
unfold d4h_block_read_stmt.
intros HL ly S W mem md regs p n a m HAR Hin Hpa Ham Hm Hv Hst.
destruct HL as [HB HS _ _ _ _ _ _ _ _ _ _ _ _].
destruct (HB ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
destruct (HS ly S W mem md p n HAR Hin) as (Hbs & Hhv).
clear HB HS.
assert (Hn0 : 0 <= n) by (clear - Hpa Ham Hm; lia).
pose proof (d4bl_req_size n Hn0) as HN.
split; [|split; [|split]].
- unfold src_ok. intros x Hx. split; [exact (Hv x Hx)|].
  pose proof (Hst x Hx) as Hs. clear - Hs. unfold ESTACK in *. lia.
- pose proof (@alloc_ceiling_lt rc) as HC. unfold amem_range.
  clear - Happ HC Hpa Ham Hm HN. appn. lia.
- exact (block_shadow_range _ _ p (req_size n) a m Hbs Hpa ltac:(clear - Ham HN; lia)).
- intros Hm0. exact (d4bl_hull_sub _ p (req_size n) a m Hhv Hpa ltac:(clear - Ham HN; lia) Hm0).
Qed.

Check (d4h_block_read : d4h_block_read_stmt B).
End c.
End b.
End a.
