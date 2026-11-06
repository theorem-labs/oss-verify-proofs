(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fuzz_reply.asan-ubsan) walk of fuzz_reply's send_line, closed, in
   the form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v (segments joined at cut points).
   Structure ported from image A's lib/A/W_send_line.v (a working branch a78a220dc8e: pb_send_line_g /
   pb_send_line); no theorem crosses images.
   send_line (fuzz_reply.asan-ubsan 0x82854, 168 instructions): the entry segment (W_send_line_entry.v sl_entry)
   closed with the loop segment (W_send_line_loop.v pb_sl_loop_cut: the EINTR, dead and data rounds), whose data round
   is the growth half (W_send_line_grow.v sl_grow, N -> J through realloc) and the copy half (W_send_line_datab.v
   sl_copy, J -> L or X through __asan_memcpy); every exit goes through the epilogue (W_send_line_cx.v sl_epi).
   The Section hypotheses are W_send_line_cx.v's, verbatim: runtime sites AERRNO AMEMCPY AREALLOC; instance LAWS MTL
   TL HG HGR HROMO HGO HERRNO HERRZ HERRW HERRAL; placement HV9..HV12 HH18 HH20..HH25 HRGD. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin W_send_line_rb W_send_line_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_send_line_entry W_send_line_loop W_send_line_grow W_send_line_datab.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes *)
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
(* nothing a callee's journal may change is a read-only image byte (W_journal.v rom_out / ajournal_gx_rom_view); and
   aout_at's three read-only cells are program globals off the allocator's statics, so a realloc keeps them *)
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* runtime and allocator sites *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
(* instance facts: errno is tp - 164 (W_sites.v aerrno_realizes), its shadow is zero, its bytes are writable and
   it is 4-aligned (B's ALIGN4 checks of __errno_location's result) *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
(* placement: the objects send_line reads by PLdHi (g_client, g_client_broken, g_send_eintr, g_nout), and the auipc
   values it stores and loads through (B's listing: 0x828a4 hi18 +1212 g_client_broken; 0x828c4 hi20 +1372
   g_send_eintr; 0x828d0 hi21 +1328 g_send_dead; 0x828dc hi22 +1252 g_send_max; 0x828e4 hi23 +1372 g_nout;
   0x828e8 hi24 +1976 g_capout; 0x828f0 hi25 +2000 g_out) *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_nout RG.
Hypothesis HH18 : VAL (A_HI 18) + 1212 = rg_client_broken RG.
Hypothesis HH20 : VAL (A_HI 20) + 1372 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 1328 = rg_send_dead RG.
Hypothesis HH22 : VAL (A_HI 22) + 1252 = rg_send_max RG.
Hypothesis HH23 : VAL (A_HI 23) + 1372 = rg_nout RG.
Hypothesis HH24 : VAL (A_HI 24) + 1976 = rg_capout RG.
Hypothesis HH25 : VAL (A_HI 25) + 2000 = rg_out RG.
(* placement: the cells send_line reads or writes are pairwise disjoint ((lo, hi) extents, as extent_of_region makes
   them; errno is tp - 164, TFIB_ERRNO 0x5d994c on image B) *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].

(* send_line's walk on image B, closed: the entry (sl_entry), the loop (pb_sl_loop_cut, its three rounds) over the
   data round's two halves (sl_copy, sl_grow).  Each piece is taken by `eapply <theorem>; eassumption` over this
   Section's hypotheses (W_send_line_cx.v's header), so the theorem rests on them alone. *)
Theorem pb_send_line : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Proof.
assert (GROW : sl_grow_stmt B MT MMAX RG) by (eapply W_send_line_grow.sl_grow; eassumption).
assert (COPY : sl_copy_stmt B MT MMAX RG) by (eapply W_send_line_datab.sl_copy; eassumption).
assert (LOOP : sl_loop_stmt B MT MMAX RG) by (eapply W_send_line_loop.pb_sl_loop_cut; eassumption).
assert (ENTRY : sl_entry_stmt B MT MMAX RG) by (eapply W_send_line_entry.sl_entry; eassumption).
exact (ENTRY LOOP).
Qed.

(* An OFF send keeps g_out's block (sl_post's last conjunct, kit cand3 2d0b655a8c7 and later): every final state of
   send_line's walk from a state that meets sl_spec's premises has g_out = out in its aout_at when sl_live is false.
   The entry's off exits give it by sl_off_exit (W_send_line_entry.v: the three early returns to X leave the stream
   untouched), and the dead round by out' = out (W_send_line_loop.v sl_arm_dead: g_send_dead = 1 means capL = cap,
   outL = out).  Stated over the post itself, so it is what a caller (drain's DLS rebuild) cites. *)
Lemma sl_off_out_kept : forall regs ly S W mem md c O mx no cap out Bl W' c',
sl_post B MT RG regs ly S W mem md c O mx no cap out Bl W' c' ->
sl_live c (Z.of_nat (length Bl)) = false ->
exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
aout_at B RG ly' S' W' mem' (sl_ctl c (Z.of_nat (length Bl))) (sl_O c O Bl) mx
  (sl_no c no (Z.of_nat (length Bl))) (sl_cap c mx no cap (Z.of_nat (length Bl))) out.
Proof.
intros regs ly S W mem md c O mx no cap out Bl W' c'
  (ly' & S' & regs' & mem' & md' & k & out' & Hc & _ & _ & _ & _ & _ & HOUT & HOFF) Hoff.
exists ly', S', regs', mem', md'. split; [exact Hc|].
rewrite <- (HOFF Hoff). exact HOUT.
Qed.
End c.
End b.
End a.
