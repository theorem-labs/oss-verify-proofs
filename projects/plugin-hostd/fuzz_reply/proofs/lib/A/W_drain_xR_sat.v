(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segments FEED and FEEDS of the ASan walk of fuzz_reply's drain -
   reference_feed's byte loop (fuzz_reply.asan 0x8347c .. 0x83550, the call to list_push at 0x834f0) and
   its composition.  The statements are W_drain_cx.v:805 dr_feed_stmt and :851 dr_feeds_stmt; the cut
   predicates are W_drain_cx.v:601 DRB (the loop head, after k of the n bytes) and :619 DE (the loop left).
   The Section header below is W_drain_top.v:44-102 verbatim, so that dr_feed_p / dr_feeds_p carry exactly
   the premises of that file's dr_feed / dr_feeds.

   THE LOOP, as the pinned listing holds it (W_listing.v; address a is entry (a - 0x822ec) / 4, line 41 +
   entry; fr_prog_start = 0x822ec, AF_fr_drain = 0xdf0, AF_fr_list_push = 0x2da4):

     0x8347c  srli a0, s8, 3          the shadow address of the source byte p0 + k
     0x83480  add  a0, a0, s5         s5 = SHADOW_OFF
     0x83484  lb   a0, 0(a0)
     0x83488  bne  a0, zero, 0x83558  -> the partial-granule check, then back to 0x8348c
     0x8348c  lb   a0, 0(s6)          the shadow byte of h->overlong
     0x83490  lbu  a1, 0(s10)         b = *(p0 + k)
     0x83494  bne  a0, zero, 0x83564  -> the 4-byte partial-granule check, then back to 0x83498
     0x83498  lw   a0, 56(s7)         overlong  (s7 = HA = &g_s[j])
     0x8349c  beq  a1, zero, 0x834d0  b = 0: the NUL case
     0x834a0  bne  a0, zero, 0x83544  overlong <> 0: drop the byte
     0x834a4  lbu  a0, 0(s11)         the shadow byte of h->npartial
     0x834a8  bne  a0, zero, 0x83c54  -> __asan_report_load8 (HA + 48)
     0x834ac  ld   a0, 48(s7)         npartial
     0x834b0  lui  a2, 0x1
     0x834b4  addiw a2, a2, 1904      a2 = 6000 = APARTIAL
     0x834b8  bne  a0, a2, 0x83510    npartial <> 6000: the ordinary case
     0x834bc  lb   a0, 0(s6)
     0x834c0  bne  a0, zero, 0x8358c  -> the 4-byte store check, then back to 0x834c4
     0x834c4  addi a0, zero, 1
     0x834c8  sw   a0, 56(s7)         h->overlong = 1
     0x834cc  jal  zero, 0x83544

     the NUL case:
     0x834d0  bne  a0, zero, 0x834f4  overlong <> 0: no push, only the reset
     0x834d4  lbu  a0, 0(s4)          the shadow byte of h->partial
     0x834d8  bne  a0, zero, 0x83c5c  -> __asan_report_load8 (HA + 40)
     0x834dc  lbu  a0, 0(s11)
     0x834e0  bne  a0, zero, 0x83c64  -> __asan_report_load8 (HA + 48)
     0x834e4  ld   a1, 40(s7)         partial
     0x834e8  ld   a2, 48(s7)         npartial
     0x834ec  ld   a0, 72(sp)         &h->expected = HA + 64
     0x834f0  jal  ra, 0x85090        list_push (LPSPEC, BASE + AF_fr_list_push)
     0x834f4  lbu  a0, 0(s11)
     0x834f8  bne  a0, zero, 0x83c6c  -> __asan_report_store8 (HA + 48)
     0x834fc  sd   zero, 48(s7)       h->npartial = 0
     0x83500  lb   a0, 0(s6)
     0x83504  bne  a0, zero, 0x83578  -> the 4-byte store check, then back to 0x83508
     0x83508  sw   zero, 56(s7)       h->overlong = 0
     0x8350c  jal  zero, 0x83544

     the ordinary case:
     0x83510  lbu  a2, 0(s4)
     0x83514  bne  a2, zero, 0x83c74  -> __asan_report_load8 (HA + 40)
     0x83518  lbu  a2, 0(s11)
     0x8351c  bne  a2, zero, 0x83c7c  -> __asan_report_store8 (HA + 48)
     0x83520  ld   a2, 40(s7)         partial
     0x83524  addi a3, a0, 1
     0x83528  sd   a3, 48(s7)         h->npartial = npartial + 1
     0x8352c  add  a0, a2, a0         &partial[npartial]
     0x83530  srli a2, a0, 3
     0x83534  add  a2, a2, s5
     0x83538  lb   a2, 0(a2)
     0x8353c  bne  a2, zero, 0x835a0  -> the 1-byte store check, then back to 0x83540
     0x83540  sb   a1, 0(a0)          partial[npartial] = b

     the loop's tail:
     0x83544  addi s9, s9, -1
     0x83548  addi s8, s8, 1
     0x8354c  addi s10, s10, 1
     0x83550  bne  s9, zero, 0x8347c  -> DRB (S k)
     0x83554  jal  zero, 0x835ac      -> DE (A_dr_fed)

   FEEDS is the composition: by induction on the bytes left, dnum s1 - k.  Each turn of the loop is one
   dr_feed_stmt, and the induction stops because DRB carries `Z.of_nat k < dnum s1`, so a DRB at S k with
   S k = dnum s1 is uninhabited. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_feed.v; 42 of its 117 lines of code are new or changed and 6522 lines of the source are left out. *)
(* Satisfiability at the real image A of the R contract texts (W_contract_xR.v), at R := wle' SEGS RZ_cf: each
   lemma derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block
   is the walk file's (W_drain_pb.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c
RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c RelayRunT RelayRunF
ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_rep W_journal
W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x
W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_drain_pro W_drain_epi W_drain_lines W_drain_outer
W_drain_all W_drain_gs W_drain W_drain_next W_drain_drop W_drain_dropb_cx W_drain_dropb W_drain_rest W_gsfree_scratch
W_gsscan_scratch W_gsscanb_cx W_gsscanb W_gsaddb_cx W_gsaddb W_gsadd_scratch W_drain_feed W_alloc_tail
W_drain_lineb_cx W_drain_lineb W_drain_linea W_drain_topb_cx W_drain_top W_drain_topb.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_drain_pb.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.

(* pb_drain_xR_sat: dr_spec_xR at R := wle' SEGS RZ_cf, from W_drain_pb.pb_drain_x by dr_spec_xR_of_x and YA0nH.wle_wle'. The Section
   hypotheses are pb_drain_x's own (W_drain_pb.v, Sections a / b / cx), unchanged; their comments are left out. *)
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
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ Exists (in_zr a) PST.
Hypothesis PSTO : forall a, inG (G_SL B RG) a \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a ->
  ~ Exists (in_zr a) PST.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x170] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x7e8] CTX_R.
Hypothesis HCTX_fr1 : In [BASE + AF_fr_drain + 0x540] CTX_F.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0x874] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x808] CTX_S.
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Theorem pb_drain_xR_sat :
  dr_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP MMAX RG A_drainP.
Proof.
apply dr_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_drain_pb.pb_drain_x; eassumption.
Qed.
End sat.
