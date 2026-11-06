(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's send_line, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v (segments joined at cut points). *)
(* send_line (fuzz_reply.asan 0x82734, 135 instructions): the entry segment (W_send_line_entry.v sl_entry) closed
   with the loop segment (W_send_line_loop.v sl_loop); both end through the epilogue segment
   (W_send_line_cx.v sl_epi).  The Section hypotheses are W_send_line_cx.v's (runtime sites AERRNO AMEMCPY
   AREALLOC; instance LAWS MTL TL HG HERRNO HERRZ; placement HV9..HV15 HH17..HH24 HSM HRGD). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YP09 YP0b YP0d YI00 YC5d YG00 YG0f YG0d YCbq YM05 YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_frame W_sites W_contract W_send_line_cx W_send_line_loop W_send_line_entry
W_send_line_datab_cx W_send_line_grow_cx W_send_line_datab W_send_line_grow.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
Theorem pb_send_line_of : forall B MT MMAX RG,
sl_loop_stmt B MT MMAX RG -> sl_entry_stmt B MT MMAX RG -> sl_spec B MT MMAX RG A_send_lineP.
Proof. intros B MT MMAX RG HL HE. exact (HE HL). Qed.
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
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
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
(* instance facts: errno is tp - 164 (W_sites.v aerrno_realizes) and its shadow is zero *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : exists r, In r (as_zero_shadow B) /\ fst r <= as_errno B /\ as_errno B + 4 <= fst r + snd r.
(* errno's 4 bytes are writable image bytes in the segments' own view (W_drain_cx.v HERRW, same text) *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
(* placement: the objects send_line reads by PLdHi, and the kept auipc registers it stores and loads through *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
(* g_send_max is not one of the listing's objects: place it in the image band by its address. *)
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
(* placement: the cells send_line reads or writes are pairwise disjoint ((lo, hi) extents, as extent_of_region
   makes them; the pinned placement decides it by vm_compute; errno is tp - 164, TFIB_ERRNO 0x5d93cc). *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
(* send_line's walk from its pieces: the entry (sl_entry), the loop (pb_sl_loop_cut: its three arms, Qed, over the
   data round's two halves), the copy half (sl_copy, a Theorem Labs lane) and the growth half (sl_grow_stmt, the one open
   piece, W_send_line_grow_cx.v).  Each piece is taken by `eapply <theorem>; eassumption` over this Section's
   hypotheses (W_send_line_cx.v's header). *)
Theorem pb_send_line_g : W_send_line_grow_cx.sl_grow_stmt B MT MMAX RG -> sl_spec B MT MMAX RG A_send_lineP.
Proof.
intros GROW.
assert (COPY : W_send_line_datab_cx.sl_copy_stmt B MT MMAX RG) by (eapply W_send_line_datab.sl_copy; eassumption).
assert (LOOP : sl_loop_stmt B MT MMAX RG) by (eapply W_send_line_loop.pb_sl_loop_cut; eassumption).
assert (ENTRY : sl_entry_stmt B MT MMAX RG) by (eapply W_send_line_entry.sl_entry; eassumption).
exact (ENTRY LOOP).
Qed.
(* send_line's walk, closed: the growth half is a Theorem Labs lane's sl_grow (W_send_line_grow.v), so no premise is left -
   the theorem rests only on this Section's hypotheses (W_send_line_cx.v's header). *)
Theorem pb_send_line : sl_spec B MT MMAX RG A_send_lineP.
Proof.
apply pb_send_line_g.
eapply W_send_line_grow.sl_grow; eassumption.
Qed.
End c.
End b.
End a.
