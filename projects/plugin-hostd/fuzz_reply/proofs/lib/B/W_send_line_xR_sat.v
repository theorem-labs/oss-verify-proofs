(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the copy half of a data round of fuzz_reply's send_line loop on IMAGE B
   (fuzz_reply.asan-ubsan), in the form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and
   lib/A/AC8b.v (a loop over concrete cut states).  Proves no function (kind: segment lemma of send_line's image-B walk:
   W_send_line_cx.v sl_copy_stmt, the copy half J -> L or X; reuse search in W_send_line_cx.v's header,
   `R24BSendLine: CONFIRM`).  STRUCTURE ported from image A's closed sl_copy (a working branch a78a220dc8e
   lib/A/W_send_line_datab.v: the seat at the join, the memcpy call, aout_at_copy, the exit); no theorem crosses images.
   From the join A_sl_join = 0x82a08 (W_send_line_cx.v SLM) to the loop head or the epilogue:
     0x82a08 ld a0,24(sp)      the spilled auipc value of g_out (A_HI 25)
     0x82a0c ld a1,2000(a0)    a1 = g_out = outM
     0x82a10 PLdHi s4 <- g_nout (A_OBJ 12, through s6 = A_HI 23): no + sent
     0x82a14 add a0,s4,a1      dst = outM + no + sent
     0x82a18 bltu a0,a1        UBSan PTR_BLTU trap: refuted by W_traps.v trap_ptr_bltu (no + sent + outM < 2 ^ 64)
     0x82a1c snez; seqz; xor; 0x82a28 beqz
                               UBSan NULL_XOR trap: decided by the runner from the seat's facts (W_traps.v seat recipe
                               R1: g_out's atom 33 has the fact [4096, 2^47], so snez folds to 1 and seqz of the sum
                               to 0)
     0x82a2c mv a1,s2; mv a2,s3; 0x82a34 jal __asan_memcpy (AMEMCPY), back at 0x82a38
     0x82a38 add s4,s4,s3; 0x82a3c sd s4,1372(s6)   g_nout := no + sent + n (region rebased onto A_HI 23 + 1372)
     0x82a40 bltz s3; 0x82a44 beqz s3              never taken: n's atom has the fact [1, 2^28] (decided)
     0x82a48 add s7,s3,s7; 0x82a4c j 0x829a4       sent := sent + n
     0x829a4 bltu s7,s0        taken: sent + n < len, the loop head L (sl_loop_at n0);
     0x829a8 j 0x82aa0         not taken: sent + n = len, the epilogue (W_send_line_cx.v sl_epi).
   The memcpy's source check needs the line's bytes addressable and the shadow hull of the line visible (YG0d.v
   aintrin_realizes, OCpy).  A heap line has both (range_addressable_of_block, shadow_hull_vis_of_block); an image
   line has them over all of [line, line + len) by sl_line_ok's ashp (W_shadow_pin.v), and over the round's
   sub-range [line + sent, line + sent + n) by range_addressable_sub and sc_hull_sub.
   The Section header is W_send_line_cx.v's (Sections a / b / c, its Variables and Hypotheses in its order, its Lets). *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, row G-BSL-b):
   the ARx-generic room-form twin of W_send_line_datab.v: sl_copy_x over ARx (a Theorem Labs lane; the B twin of its
   lib/A/W_send_line_datab_x.v) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_send_line_datab_x.v; 27 of its 92 lines of code are new or changed and 970 lines of the source are left out. *)
(* Satisfiability at the real image B of the R contract texts (W_send_line_xR.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_send_line_x.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State
Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15
YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06
YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00
YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_rep W_journal
W_sites W_contract W_frame W_shadow_pin W_send_line_rb W_send_line_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_send_line_cx_x W_send_line_datab_cx_x
W_send_line_grow_cx_x W_send_line_entry_x W_send_line_loop_x W_send_line_grow_x W_send_line_datab_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_send_line_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_send_line_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

(* pb_send_line_xR_sat: sl_spec_xR at R := wle' SEGS RZ_cf, from W_send_line_x.pb_send_line_x by sl_spec_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_send_line_x's own (W_send_line_x.v, Sections a / b / c), unchanged; their comments are left out. *)
Section sat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKM : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 30.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_slr : In [BASE + AF_fr_send_line + 0x1a0] CTX_R.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
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
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
Theorem pb_send_line_xR_sat :
  sl_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX RG A_send_lineP.
Proof.
apply sl_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_send_line_x.pb_send_line_x; eassumption.
Qed.
End sat.
