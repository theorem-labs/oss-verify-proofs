(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v at 533bf30ff015 for image B (fuzz_rate.asan-ubsan): image B's block SEL7 0x80ff4 -> LATCH7 0x8257c (e into scope, memset(e.body, 0, 96) through lib/AU/RtPgStepsB.v rtsb_intrin_at at 0x51d54, e.size = e.type = 4, the call pod_write_ent(pp, e) 0x81054 through rtsb_pwe_at with lib/AU/PweSpec.v's contract at 0x83cc4 as a Section hypothesis, e out of scope) in three engine runs over the kit lib/AU/RtPgPropBKit.v, with the frame shadow, frame-object and record facts of lib/AU/RtPgMemB.v; the piece is lib/AU/RtPgSegB.v's rsb_piece_W4_int7_stmt with image B's cut lists. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPropBInt7.v at 6aea585e8b5b for
   reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role (lib/AU/Img0.rsegs, lib/A/RPgBase
   and RPgCSpec, lib/AU/RPgSteps.v / RPgStepsU.v / RPgMem.v / RPgSeg.v / RPgPropKit.v / RPgPropLib.v names); every pc is
   role B's (SEL7 0x807b4, the memset call 0x80800 to 0x51608 with return 0x80804, the call of pod_write_ent 0x80818
   to 0x82bac with return 0x8081c, LATCH7 0x81d88); the real frame is 0x200 bytes and its cells are role B's (e.body
   in R+0xa0, &e in R+0xb8, pp in R+0x140); across the calls the block keeps the property index (t1) in s4, what is
   left of the input (t3) in s10 and the cursor (t4) in s8, and at its end it puts the cursor into a7, t3 and t1 back,
   s10 := -8 and `seen` (s2) into a2, so the clobbered set and the block's relation are role B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/AU/RPgPropIntB.v, with its module names changed; 267 of its 329 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5IntP.v at a66696a9b1d1 for the same
   unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the cut vocabulary is lib/AU/RtPgSegB.v's
   (rsb_, SELI 0x82398 -> LATCH7 0x8257c, no LATCHI), the bridge lib/AU/RtPgW5SegB.v's (w5b_) and the memory layer
   lib/AU/RtPgMemB.v's (rtmb_); the core is lib/AU/RtPgW5IntB.v's w5b_int_core, which calls checked_memset and
   pod_write_ent under the Section hypotheses W5B_AMEMSET and W5B_PWE, so the piece carries two call hypotheses
   where image A carried one; the end cut's list carries s8 = -8 and a3 = seen (image A's a6 / s8 / s10 of the
   capacity bound are gone, image B reloading neither the property index nor the bound); the prefixes w5_ / w5i_
   become w5b_ / w5bp_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW5IntPB.v at 2ebedbb4253d for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the cut
   vocabulary is lib/AU/RPgSeg.v's (rs_, SELI 0x81b98 -> LATCH7 0x81d88), the bridge lib/AU/RPgW5Seg.v's (w5_), the
   memory layer lib/AU/RPgMem.v's (rm_) and the core lib/AU/RPgW5Int.v's w5_int_core; the cut's facts are role B's
   (pp in s8, t1 = the property index, t3 / t4 = what is left / the cursor, the cells R+0x60 / 0x68 / 0x78 / 0x130 /
   0x138); the end cut's list carries s10 = -8, s6 = pp + 0x4000, a2 = seen, a7 = the cursor; w5_piece_int_B gives
   the pod_write_ent hypothesis by lib/AU/PweRun.v's pod_write_ent_B; the prefixes w5b_ / w5bp_ become w5_ / w5p_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/AU/RPgW5IntP.v, with its module paths and module names changed; 9 of its 29 lines of code are new or changed and 309 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgProp.v at 533bf30ff015 for image B
   (fuzz_rate.asan-ubsan): image B's pieces, pcs and files; the latch has two entries; the shape-7 piece also takes
   pod_write_ent's contract, and pab_piece_int7_B discharges it by pod_write_ent's own walk (lib/AU/PweRun.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPropB.v at 6aea585e8b5b for reac-pw/fuzz_role
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, image A's file and lemma names (pa_ for pab_;
   the latch piece is in lib/AU/RPgPropSel.v, the selector piece in RPgPropSelB.v), lib/AU/Img0.rsegs, role B's
   pcs, the memset contract at role B's 0x51608 and pod_write_ent's at 0x82bac (lib/AU/PweKit.v's PWE_MEMCPY,
   PWE_GOT, PWE_CELL at role B). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the four pieces of one turn
   of the property loop of LLVMFuzzerTestOneInput (0x80020) as lib/AU/RPgSeg.v states them, gathered for the
   assembly. Proves no function (kind: segment lemma).
     pa_piece_sel   : rs_piece_W4_sel_stmt    N 0x80770 -> SEL7 0x807b4 / SELK 0x8086c       (lib/AU/RPgPropSelB.v)
     pa_piece_int7  : rs_piece_W4_int7_stmt   SEL7 0x807b4 -> LATCH7 0x81d88                 (lib/AU/RPgPropIntB.v)
     pa_piece_key   : rs_piece_W4_key_stmt    SELK 0x8086c -> SELS 0x809d4 / SELI 0x81b98    (lib/AU/RPgPropKeyB.v)
     pa_piece_latch : rs_piece_W4_latch_stmt  LATCH 0x81d84 / LATCH7 0x81d88 -> N 0x80770 / P1 0x81e70
                                                                                             (lib/AU/RPgPropSel.v)
   Each takes the Section hypotheses MTL (ameter_laws) and LAWS (AR_laws of image B); pa_piece_int7 also AMEMSET,
   the memset contract at the runtime's checked memset 0x51608 (YG0d.aintrin_realizes OSet), and PWE, pod_write_ent's
   contract at 0x82bac (lib/AU/PweSpec.v pod_write_ent_specX), which the shape-7 pod's body calls. pa_piece_int7_B is
   pa_piece_int7 with PWE given by lib/AU/PweRun.v's pod_write_ent_B, so its premises are those of the other pieces,
   AMEMSET, the memcpy contract at the runtime's checked memcpy 0x5116c and the symbol record's two cells
   pod_write_ent_B names. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require PweKit PweRun.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import PweSpec RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Export RPgPropSel RPgPropSelB RPgPropIntB RPgPropKeyB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Open Scope Z_scope.

Corollary pa_piece_int7_B : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
  (B : asyms) (MT : ameter_ops),
  ameter_laws MT -> AR_laws rsegs B -> aintrin_realizes rsegs B OSet 0x51608 ->
  aintrin_realizes rsegs B OCpy PweKit.PWE_MEMCPY -> as_got_shadow B = PweKit.PWE_GOT ->
  as_shadow_cell B = PweKit.PWE_CELL ->
  rs_piece_W4_int7_stmt rsegs B MT.
Proof.
intros fx rc SK B MT MTL LAWS AMEMSET AMEMCPY HBgot HBcell.
exact (pa_piece_int7 B MT MTL LAWS AMEMSET (PweRun.pod_write_ent_B B MT MTL HBgot HBcell AMEMCPY AMEMSET)).
Qed.
