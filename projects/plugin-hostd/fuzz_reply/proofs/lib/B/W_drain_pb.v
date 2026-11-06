(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane, a Theorem Labs lane's dr_sa_align row): pb_drain_of loses the premise dr_sa_align; the kit's dr_spec states SA mod 8 = 0. *)
(* Modified by Theorem Labs, 2026-10: pb_drain_of, the published assembly of the image-B
   (fuzz_reply.asan-ubsan) walk of fuzz_reply's drain: ONE application of lib/B/W_drain.v's dr_assemble.  The
   image-independent compositions are proved on B's cuts and applied here, each by
   `assert (X : <stmt>) by (eapply <thm>; eassumption)` (W7's style on A, lib/A/W_drain_pb.v):
     dr_feeds  lib/B/W_drain_feeds.v   the byte loop, by induction on dnum s1 - k
     dr_lines  lib/B/W_drain_lines.v   the line loop, by induction on |dW s1| - p
     dr_outer  lib/B/W_drain_outer.v   the outer loop, by induction on dneed s1
     dr_all    lib/B/W_drain_all.v     the prologue and the outer loop give dr_spec
     dr_top_of lib/B/W_drain_tophead.v TOP from its head and tail halves, split at 0x83524
   and the walked stages proved so far, applied the same way over the Section hypotheses of
   lib/B/W_drain_cx.v (which therefore become pb_drain_of's own premises, those a stage uses):
     dr_feed   lib/B/W_drain_feed.v    FEED 0x836fc .. 0x8389c -> DRB (S k) / DE  (a Theorem Labs lane,
                                       a working branch f02afb993d6)
     dr_pro    lib/B/W_drain_pro.v     PRO  0x83278 .. 0x833bc -> DI           (a Theorem Labs lane,
                                       a working branch 814e1b83f19)
     dr_epi    lib/B/W_drain_epi.v     EPI  0x83fc8 .. 0x84000                 (a Theorem Labs lane,
     dr_end    lib/B/W_drain_epi.v     END  0x83e94 .. 0x83fc4                  a working branch 1072b214260)
     pb_dr_gs  lib/B/W_drain_gs_top.v  GS   0x83aa4 .. 0x83d98 -> DLN (S q)    (a Theorem Labs lane,
                                       a working branch 63e7043187e)
     dr_next   lib/B/W_drain_next.v    NEXT 0x839d4 .. -> DLL p q / DLR p     (a Theorem Labs lane,
     dr_rest   lib/B/W_drain_rest.v    REST 0x83e34 .. 0x83e90 -> DI          a working branch 6670c18e144)
     dr_linea  lib/B/W_drain_linea.v   LINEA 0x8399c .. 0x839f4 -> DLN (S q) / DLS (a Theorem Labs lane,
     dr_lineb  lib/B/W_drain_lineb.v   DLS  0x839f4 .. 0x83aa0 -> DLN (S q) / DGS   a working branch
                                       81eebc35a0b); dr_linea takes dr_lineb as its LINEB.  Both are Required, not
                                       Imported: dr_linea's W_drain_tr.v and the GS stage's W_drain_gs_aux.v define
                                       some of the same names, so their names are used qualified here.
     dr_toptail lib/B/W_drain_topb.v   TOP tail 0x83524 .. 0x836f8 -> DI (EINTR) / DEND / DRB 0 (a Theorem Labs lane,
                                       a working branch 01c09263227); Required, not Imported.
     dr_drop   lib/B/W_drain_drop.v    DROP 0x838a0 .. 0x83998 -> DLL 0 q / DLR 0, list_drop called at 0x83914 through
                                       W_list_drop.v pb_list_drop_ro_c (a Theorem Labs lane, a working branch
                                       d76927ef99b); Required, not Imported.
     TOP head, by dr_tophead_of from dt_nogrow and dt_grow (lib/B/W_drain_tophead.v; dt_grow is the growth arm,
               realloc #1, 0x833ec .. 0x83434) and dt_scan_of over dt_scan_entry / dt_scan_step
               (lib/B/W_drain_topscan.v, this lane's scan sub-walk), so TOP's head is proved in full.
   The walk owes nothing more: pb_drain_of has no statement premise (dr_sa_align, the entry address's
   8-alignment, is closed: the kit's dr_spec states it, W_drain_cx.v FINDING 1).
   Print Assumptions pb_drain_of: the engine's primitives and functional_extensionality_dep only. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_drain_cx W_drain
W_drain_feeds W_drain_lines W_drain_outer W_drain_all W_drain_topb_cx W_drain_tophead
W_drain_feed W_drain_pro W_drain_epi W_drain_gs_top W_drain_next W_drain_rest W_drain_topscan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_drain_lineb_cx W_drain_lineb W_drain_linea W_drain_topb W_drain_drop.
(* DR_x: the generic kit (YCbqG's laws, W_journal_x's rules and room record, W_sites_x's sites, W_contract_x's specs,
   W_drain_cx_x's statements) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) and the R specs (W_contract_xR.v, W_send_line_xR.v), for pb_drain_xR *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_send_line_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Theorem pb_drain_of :
  dr_spec B MT MMAX RG A_drainP.
Proof.
assert (DROP : dr_drop_stmt B MT MMAX RG) by (eapply W_drain_drop.dr_drop; eassumption).
assert (TAIL : dr_toptail_stmt B MT MMAX RG) by (eapply W_drain_topb.dr_toptail; eassumption).
assert (LINEB : W_drain_lineb_cx.dr_lineb_stmt B MT MMAX RG) by (eapply W_drain_lineb.dr_lineb; eassumption).
assert (LINEA : dr_linea_stmt B MT MMAX RG) by (eapply W_drain_linea.dr_linea; eassumption).
assert (EPI : dr_epi_stmt B RG) by (eapply dr_epi; eassumption).
assert (END : dr_end_stmt B MT MMAX RG) by (eapply dr_end; eassumption).
assert (GS : dr_gs_stmt B MT MMAX RG) by (eapply pb_dr_gs; eassumption).
assert (NEXT : dr_next_stmt B MT MMAX RG) by (eapply dr_next; eassumption).
assert (REST : dr_rest_stmt B MT MMAX RG) by (eapply dr_rest; eassumption).
assert (SENT : dt_scan_entry_stmt B MT MMAX RG) by (eapply dt_scan_entry; eassumption).
assert (SSTEP : dt_scan_step_stmt B MT MMAX RG) by (eapply dt_scan_step; eassumption).
assert (SCAN : dt_scan_stmt B MT MMAX RG) by (eapply dt_scan_of; eassumption).
assert (GROW : dt_grow_stmt B MT MMAX RG) by (eapply dt_grow; eassumption).
assert (NOGROW : dt_nogrow_stmt B MT MMAX RG) by (eapply dt_nogrow; eassumption).
assert (HEAD : dr_tophead_stmt B MT MMAX RG) by (eapply dr_tophead_of; eassumption).
assert (PRO : dr_pro_stmt B MT MMAX RG) by (eapply dr_pro; eassumption).
assert (FEED : dr_feed_stmt B MT MMAX RG) by (eapply dr_feed; eassumption).
assert (TOP : dr_top_stmt B MT MMAX RG) by (eapply dr_top_of; eassumption).
assert (FEEDS : dr_feeds_stmt B MT MMAX RG) by (eapply dr_feeds; eassumption).
assert (LINES : dr_lines_stmt B MT MMAX RG) by (eapply dr_lines; eassumption).
assert (OUTER : dr_outer_stmt B MT MMAX RG) by (eapply dr_outer; eassumption).
assert (ALL : dr_all_stmt B MT MMAX RG) by (eapply dr_all; eassumption).
eapply dr_assemble; eassumption.
Qed.

End c.

(* ---- DR_x: pb_drain_x, drain's contract over any ARx (W_contract_x.v's dr_spec_x at A_drainP), generic in
   W_drain_cx_x.v's Section variables B PST ARx MT RP MMAX RG, from W_drain.v's dr_assemble_x and every generic
   segment and composition theorem (the image-B twin of a Theorem Labs lane's lib/A/W_drain_pb.v pb_drain_x). Its instance at
   (TfibB, [], ARX, MT, RPi, fr_MMAX, fr_RG) is W_LLVMFuzzerTestOneInput_top_x.v's Section hypothesis DR_x
   (A_drainP = BASE + AF_fr_drain by delta).
   The header is W_drain_cx_x.v Section c's text (B's: HERRAL, HVS at A_OBJ 19, HLIT5 / 6 / 7 at A_OBJ 18 / 20 / 21,
   HRGD at A_OBJ 30 / 18 / 20 / 21, HGSB / HSM at IMG_TOP, HSD; the allocator rules in their caller-context forms at
   the tables CTX_R / CTX_F / CTX_S and drain's five call-site facts at B's own offsets, list_drop's free HCTX_ld in
   place of A's free #1), and the stage walks' instance facts HP0 / BLKN / BLKM / PSTR / PSTG / PSTO (BLKM: B's drop
   reads it); ALLOC_TAIL is W_drain_cx_x.alloc_tail_x of LAWS.  Every premise is a Section hypothesis of a cited
   stage; none is a statement premise.  The AR theorem pb_drain_of is kept as it is. ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the stage walks' instance facts (fixed texts) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis BLKM : forall ly S Hp (W : world SEGS) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  n < 2 ^ 30.
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
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
(* the allocator's site rules in their caller-context forms over the generic journal (W_journal_x.v Section hc), one
   table per allocator entry; each drain site hands the rule a cut chain, so each trace is its return address alone *)
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.      (* realloc #1 returns to 0x83414 *)
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.      (* realloc #2 returns to 0x83bec *)
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.      (* free #2 returns to 0x83cd0 *)
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.       (* strndup returns to 0x83c0c *)
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.    (* list_drop's free (drop calls list_drop) *)


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): pb_drain_x at R.  The assembly of the
   stage twins at R: each stage is its file's R twin (lib/B/W_drain_pro / _topb / _topscan / _feed / _feeds / _rest /
   _epi / _drop / _linea / _lineb / _next, and W_drain_gs_top.pb_dr_gs_xR over W_gsadd / W_gsfree), and the compositions are this branch's dr_lines_xR / dr_outer_xR / dr_all_xR /
   dr_assemble_xR.
   The cf rules at R and the facts their call sites owe are stated once here (RO / RO_ARx, HA / HA_call), with the callee specs at R (sl_spec_xR, lp_spec_g_xR), because the add / free / drop / list_drop stages
   take them. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_F R.
Hypothesis ASTRNDUP_R : astrndup_cf_rule_c_xR SEGS B PST ARx MT MMAX RP CTX_S R (SIGMA WS_strndup).
Hypothesis SLSPEC_R : sl_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC_R : lp_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_list_push).

Theorem pb_drain_xR : dr_spec_xR B PST ARx R MT RP MMAX RG A_drainP.
Proof.
pose proof (alloc_tail_x SEGS B ARx LAWS) as ALLOC_TAIL.
assert (PRO : dr_pro_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_pro.dr_pro_xR with (R := R); eassumption).
assert (TAIL : W_drain_topb_cx.dr_toptail_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_topb.dr_toptail_xR with (R := R); eassumption).
assert (TOP : dr_top_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_topscan.dr_top_xR with (R := R) (RO := RO) (HA := HA); eassumption).
assert (FEED : dr_feed_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_feed.dr_feed_xR with (R := R); eassumption).
pose proof (W_drain_feeds.dr_feeds_xR B PST ARx MT RP MMAX RG R) as FEEDS.
assert (GS : dr_gs_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_gs_top.pb_dr_gs_xR with (R := R) (RO := RO) (HA := HA); eassumption).
assert (NEXT : dr_next_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_next.dr_next_xR with (R := R); eassumption).
assert (REST : dr_rest_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_rest.dr_rest_xR with (R := R); eassumption).
assert (EPI : dr_epi_stmt_xR B PST ARx RG R) by (eapply W_drain_epi.dr_epi_xR with (R := R); eassumption).
assert (END : dr_end_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_epi.dr_end_xR with (R := R); eassumption).
assert (LINEB : W_drain_lineb_cx.dr_lineb_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_lineb.dr_lineb_xR with (R := R); eassumption).
assert (LINEA : dr_linea_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_linea.dr_linea_xR with (R := R); eassumption).
assert (DROP : dr_drop_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_drop.dr_drop_xR with (R := R) (RO := RO); eassumption).
pose proof (W_drain_lines.dr_lines_xR B PST ARx MT RP MMAX RG R) as LINES.
pose proof (W_drain_outer.dr_outer_xR B PST ARx MT RP MMAX RG R) as OUTER.
pose proof (W_drain_all.dr_all_xR B PST ARx MT RP MMAX RG R) as ALL.
exact (W_drain.dr_assemble_xR B PST ARx MT RP MMAX RG R PRO TOP FEED FEEDS DROP LINEA GS NEXT REST LINES
  EPI END OUTER ALL).
Qed.
End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
(* the R premises at wle: the R rules from the strict ones (W_journal_x.v afree / arealloc_cf_rule_c_xR_of_x, astrndup_cf_rule_c_x_wle), the R specs from the strict ones (sl_spec_x_wle, lp_spec_g_x_wle), RO / HA := True *)
Local Ltac wle_inst_r := first [ eassumption | intros; exact I | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2]
  | eapply arealloc_cf_rule_c_xR_of_x; eassumption | eapply afree_cf_rule_c_xR_of_x; eassumption
  | rewrite <- astrndup_cf_rule_c_x_wle; eassumption | rewrite <- sl_spec_x_wle; eassumption
  | rewrite <- lp_spec_g_x_wle; eassumption ].
Theorem pb_drain_x : dr_spec_x B PST ARx MT RP MMAX RG A_drainP.
Proof. first [ eapply pb_drain_xR with (R := @wle SEGS) (RO := fun _ => True) (HA := fun _ _ _ _ _ _ => True) | eapply pb_drain_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply pb_drain_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.

End cx.
End b.
End a.

(* ---- DR_x: pb_drain_x's AR-free instance facts at the image-B instance of top_x (PB_fr, B := TfibB, RG := fr_RG,
   PST := []), so that the plug only cites them: the five call-site facts HCTX_* at YCk0.v's CTX_AREALLOC / CTX_AFREE
   and YCej.v's CTX_strndup (the tables the K0 graph names for drain's sites 0x83414 / 0x83bec / 0x83cd0 / 0x83c0c and
   list_drop's free); the static placement facts HCROM / HVS / HV9 / HSD / HGSB / HSM / HRGD / HERRW / HERRNO /
   HERRAL by computation; HERRZ / HGSZ from YF0m.v's zero-shadow table (HGSZ: _G.v's c_HZS); HG / HGO / HGR / HROMO
   from W_LLVMFuzzerTestOneInput_G.v's inclusions into G_fr_c with gx_ok_incl / rom_out_incl (both conditions are
   pointwise in G, so they pass to a sub-list), from errno's cell drain_HEV and G_fr_c's unowned bytes drain_HOWN (top_x's
   top_HEV / top_HOWN texts, restated here so that this file does not Require top_x); and PSTR / PSTG / PSTO at
   PST = [].  HROMO is at the instance's sink head YE2k.tfib_sink_head, the head _G.v's c_rom_out proves.  The
   placement files are required here, for these lemmas only; the generic Sections above stay generic in PI. ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img YCk0 YCej YD2l YF0m YE2k
  W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.

(* gx_ok passes to any G whose bytes lie in a G' it holds of *)
Lemma gx_ok_incl : forall segs B (G G' : list (Z * Z)), (forall a, inG G a -> inG G' a) ->
  gx_ok segs B G' -> gx_ok segs B G.
Proof. intros segs B G G' Hs H a Ha. exact (H a (Hs a Ha)). Qed.
(* rom_out likewise (its G conjunct is `~ inG G a`) *)
Lemma rom_out_incl : forall {SK : YI16.sink_head} segs B (G G' : list (Z * Z)), (forall a, inG G a -> inG G' a) ->
  rom_out segs B G' -> rom_out segs B G.
Proof.
intros SK segs B G G' Hs H a Ha. destruct (H a Ha) as (HnG & Hp & He & Ho).
refine (conj _ (conj Hp (conj He Ho))). intros HG. exact (HnG (Hs a HG)).
Qed.

(* zpairwise_disjoint by computation *)
Fixpoint zall_disjb (a : Z * Z) (l : list (Z * Z)) : bool :=
  match l with [] => true | b :: l' => ((snd a <=? fst b) || (snd b <=? fst a))%bool && zall_disjb a l' end.
Fixpoint zpairwise_disjb (l : list (Z * Z)) : bool :=
  match l with [] => true | a :: l' => zall_disjb a l' && zpairwise_disjb l' end.
Lemma zall_disjb_ok : forall a l, zall_disjb a l = true -> zall_disjoint a l.
Proof.
intros a l. induction l as [|b l IH]; cbn [zall_disjb zall_disjoint]; intros H; [exact I|].
apply andb_prop in H as [Hb Hl]. split; [|exact (IH Hl)].
unfold zdisj. apply orb_prop in Hb as [Hb|Hb]; [left|right]; apply Z.leb_le; exact Hb.
Qed.
Lemma zpairwise_disjb_ok : forall l, zpairwise_disjb l = true -> zpairwise_disjoint l.
Proof.
induction l as [|a l IH]; cbn [zpairwise_disjb zpairwise_disjoint]; intros H; [exact I|].
apply andb_prop in H as [Ha Hl]. exact (conj (zall_disjb_ok a l Ha) (IH Hl)).
Qed.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing W_img.PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing W_img.PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing W_img.PB_fr A_TEXT).
#[local] Notation TfibB := YD2l.TfibB.
#[local] Notation RG := W_LLVMFuzzerTestOneInput_cut.fr_RG.

(* HCTX_* *)
Lemma drain_hctx_re1 : In [BASE + AF_fr_drain + 0x19c] YCk0.CTX_AREALLOC.
Proof. unfold YCk0.CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_re2 : In [BASE + AF_fr_drain + 0x974] YCk0.CTX_AREALLOC.
Proof. unfold YCk0.CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_fr2 : In [BASE + AF_fr_drain + 0xa58] YCk0.CTX_AFREE.
Proof. unfold YCk0.CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_sd : In [BASE + AF_fr_drain + 0x994] YCej.CTX_strndup.
Proof. unfold YCej.CTX_strndup. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_ld : In [BASE + AF_fr_list_drop + 0x9c] YCk0.CTX_AFREE.
Proof. unfold YCk0.CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). Qed.

(* HCROM: memchr's table [0x10350, 0x10370) lies in one read-only segment *)
Lemma drain_HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom segs a.
Proof.
intros a Ha.
assert (Hb : match find_segment segs 0x10350 0x20 with Some sg => negb (seg_writable sg) | None => false end = true)
  by (vm_compute; reflexivity).
destruct (find_segment segs 0x10350 0x20) as [sg|] eqn:Hf; [|discriminate].
destruct (find_segment_hit segs 0x10350 0x20 sg Hf) as (Hin & H1 & H2). exists sg. split; [exact Hin|].
split; [destruct (seg_writable sg); [discriminate | reflexivity] | lia].
Qed.
(* the objects drain reads, at fr_RG *)
Lemma drain_HVS : VAL (A_OBJ 19) = rg_s RG.
Proof. vm_compute. reflexivity. Qed.
Lemma drain_HV9 : VAL (A_OBJ 9) = rg_client RG.
Proof. vm_compute. reflexivity. Qed.
Lemma drain_HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma drain_HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Proof. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity|]. vm_compute. reflexivity. Qed.
Lemma drain_HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma drain_HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno TfibB, as_errno TfibB + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Proof. apply zpairwise_disjb_ok. vm_compute. reflexivity. Qed.
(* errno's cell (top_x's top_HEV) and the start-up symbols' facts at it *)
Lemma drain_HEV : as_errno TfibB = W_LLVMFuzzerTestOneInput_G.TFIB_ERRNO_B.
Proof. rewrite (YF0m.ts_errno TfibB YD2l.TfibB_syms). reflexivity. Qed.
Lemma drain_HERRNO : as_errno TfibB = as_tp TfibB - 164.
Proof. vm_compute. reflexivity. Qed.
Lemma drain_HERRAL : as_errno TfibB mod 4 = 0.
Proof. vm_compute. reflexivity. Qed.
(* HERRZ: errno's four bytes lie in YF0m's zero-shadow range (0x5d90e0, 0x5fc000 - 0x5d90e0) *)
Lemma drain_HERRZ : azs TfibB (as_errno TfibB) 4.
Proof.
exists (0x5d90e0, 0x5fc000 - 0x5d90e0). rewrite (YF0m.ts_zsh TfibB YD2l.TfibB_syms).
split; [unfold YF0m.Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right])|].
cbn [fst snd]. rewrite drain_HEV. unfold W_LLVMFuzzerTestOneInput_G.TFIB_ERRNO_B.
split; [reflexivity|]. split; apply Z.leb_le; vm_compute; reflexivity.
Qed.
(* HERRW: errno's four bytes lie in a writable segment *)
Lemma drain_HERRW : forall i, 0 <= i < 4 -> writable_at segs (fun _ => None) (as_errno TfibB + i).
Proof.
intros i Hi. unfold writable_at.
assert (Hf : forallb (W_LLVMFuzzerTestOneInput_G.rng_all (W_LLVMFuzzerTestOneInput_G.segwb segs))
  [(as_errno TfibB, 4)] = true) by (vm_compute; reflexivity).
apply (W_LLVMFuzzerTestOneInput_G.segwb_ok segs).
apply (W_LLVMFuzzerTestOneInput_G.rng_all_in _ _ _ Hf).
apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* HGSZ: g_s's zero shadow (_G.v's c_HZS) *)
Lemma drain_HGSZ : azs TfibB (rg_s RG) (4 * ASRC).
Proof. exact (W_LLVMFuzzerTestOneInput_G.c_HZS TfibB YD2l.TfibB_syms). Qed.
(* no byte of G_fr_c is an owned static (top_x's top_HOWN) *)
Lemma drain_HOWN : forall a, inG (W_LLVMFuzzerTestOneInput_G.G_fr_c TfibB) a -> ~ Exists (in_zr a) (as_owned_static TfibB).
Proof.
intros a Ha. rewrite (YF0m.ts_owned TfibB YD2l.TfibB_syms).
rewrite (W_LLVMFuzzerTestOneInput_G.G_fr_c_val TfibB drain_HEV) in Ha. intros Hex.
assert (Hb : forallb (fun r => forallb (fun g => (fst g + snd g <=? fst r) || (fst r + snd r <=? fst g))
  (W_LLVMFuzzerTestOneInput_G.G_fr_obj ++ [(W_LLVMFuzzerTestOneInput_G.TFIB_ERRNO_B, 4)])) YF0m.Tfib_owned_static = true)
  by (vm_compute; reflexivity).
apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in Hb.
destruct r as [lo n]. exact (W_LLVMFuzzerTestOneInput_G.apart_of_b _ lo n (Hb (lo, n) Hr) a Ha Hz).
Qed.
(* no byte of G_fr_c is a kept byte (gx_ok's third clause, QMm W0' (B)): _G.v's c_HKEPT *)
Lemma drain_HKEPT : forall a, inG (W_LLVMFuzzerTestOneInput_G.G_fr_c TfibB) a -> ~ Exists (in_zr a) (as_kept TfibB).
Proof.
first [ exact (W_LLVMFuzzerTestOneInput_G.c_HKEPT TfibB YD2l.TfibB_syms drain_HEV)
      | exact (W_LLVMFuzzerTestOneInput_G.c_HKEPT TfibB drain_HEV) ].
Qed.
(* HG / HGO: drain's G and its three gesture globals lie in G_fr_c, which gx_ok holds of *)
Lemma drain_HG : gx_ok segs TfibB (G_DR TfibB RG).
Proof.
apply (gx_ok_incl _ _ _ _ (W_LLVMFuzzerTestOneInput_G.c_HG_DR TfibB)).
exact (W_LLVMFuzzerTestOneInput_G.c_gx_ok TfibB drain_HEV drain_HOWN drain_HKEPT).
Qed.
Lemma drain_HGO : gx_ok segs TfibB [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Proof.
apply (gx_ok_incl _ _ _ (W_LLVMFuzzerTestOneInput_G.G_fr_c TfibB)).
- intros a Ha.
  apply inG_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha;
    exact (W_LLVMFuzzerTestOneInput_G.c_HG_client TfibB a Ha)|].
  apply inG_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha;
    exact (W_LLVMFuzzerTestOneInput_G.c_HG_sdead TfibB a Ha)|].
  apply inG_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha;
    exact (W_LLVMFuzzerTestOneInput_G.c_HG_smax TfibB a Ha)|].
  exfalso. exact (inG_nil a Ha).
- exact (W_LLVMFuzzerTestOneInput_G.c_gx_ok TfibB drain_HEV drain_HOWN drain_HKEPT).
Qed.
(* HGR / HROMO: no read-only byte is in G_fr_c (c_rom_apart / c_rom_out), so none is in drain's G *)
Lemma drain_HGR : forall a, inG (G_DR TfibB RG) a -> ~ in_rom segs a.
Proof.
intros a Ha Hr.
exact (W_LLVMFuzzerTestOneInput_G.c_rom_apart TfibB drain_HEV a Hr (W_LLVMFuzzerTestOneInput_G.c_HG_DR TfibB a Ha)).
Qed.
Lemma drain_HROMO : @rom_out YE2k.tfib_sink_head segs TfibB (G_DR TfibB RG).
Proof.
apply (@rom_out_incl YE2k.tfib_sink_head _ _ _ _ (W_LLVMFuzzerTestOneInput_G.c_HG_DR TfibB)).
exact (W_LLVMFuzzerTestOneInput_G.c_rom_out TfibB YD2l.TfibB_syms drain_HEV).
Qed.
(* PSTR / PSTG / PSTO at the instance's placement PST := [] *)
Lemma drain_PSTR : forall a, in_rom segs a -> ~ Exists (in_zr a) ([] : list (Z * Z)).
Proof. intros a _ H. inversion H. Qed.
Lemma drain_PSTG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ Exists (in_zr a) ([] : list (Z * Z)).
Proof. intros a _ H. inversion H. Qed.
Lemma drain_PSTO : forall a,
  inG (G_SL TfibB RG) a \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a ->
  ~ Exists (in_zr a) ([] : list (Z * Z)).
Proof. intros a _ H. inversion H. Qed.
End inst.
