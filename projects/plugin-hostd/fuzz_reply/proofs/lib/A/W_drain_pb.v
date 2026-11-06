(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: la_callS is ported from the w4 lane's gx_callS, itself the cgif donor's
   cl_callS (proofs/cgif/*/lib/YC85.v:383, Anthropic PBC); the rest is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_linea.v; 213 of its 378 lines of code are new or changed and 3921 lines of the source are left out. *)
(* pb_drain: drain's contract (dr_spec at A_drainP) from W_drain.v dr_assemble and EVERY segment and composition
   theorem by name - no drain-internal premise is left; the theorem rests only on this Section's hypotheses (W_drain_cx.v's
   header: the callee contracts and the placement / instance facts).  Assembled by a Theorem Labs lane, completed by W7Drain-2 as the
   pieces closed.  Each piece is taken by `eapply <theorem>; eassumption` over the Section hypotheses, so a piece that
   gains or loses a Section hypothesis does not break the assembly; ALLOC_TAIL comes from W_alloc_tail.v. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx.
(* DR_x: the generic kit (YCbqG's laws, W_journal_x's rules and room record, W_sites_x's sites, W_contract_x's specs,
   W_drain_cx_x's statements) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) dr_spec_xR / lp_spec_g_xR (W_contract_xR.v) and sl_spec_xR (W_send_line_xR.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_send_line_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_drain_pro W_drain_epi W_drain_lines W_drain_outer W_drain_all W_drain_gs W_drain W_drain_next W_drain_drop
W_drain_dropb_cx W_drain_dropb W_drain_rest W_gsfree_scratch W_gsscan_scratch W_gsscanb_cx W_gsscanb W_gsaddb_cx
W_gsaddb W_gsadd_scratch W_drain_feed W_alloc_tail W_drain_lineb_cx W_drain_lineb W_drain_linea W_drain_topb_cx
W_drain_top W_drain_topb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
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

Theorem pb_drain : dr_spec B MT MMAX RG A_drainP.
Proof.
assert (TAIL : W_drain_topb_cx.dr_toptail_stmt B MT MMAX RG) by (eapply W_drain_topb.dr_toptail; eassumption).
(* ALLOC_TAIL is a theorem of AR (W_alloc_tail.v, a Theorem Labs lane), not a hypothesis of this assembly *)
pose proof (W_alloc_tail.alloc_tail SEGS B) as ALLOC_TAIL.
assert (TOP : dr_top_stmt B MT MMAX RG) by (eapply W_drain_top.dr_top; eassumption).
assert (LINEB : W_drain_lineb_cx.dr_lineb_stmt B MT MMAX RG) by (eapply W_drain_lineb.dr_lineb; eassumption).
assert (LINEA : dr_linea_stmt B MT MMAX RG) by (eapply W_drain_linea.dr_linea; eassumption).
assert (FEED : dr_feed_stmt B MT MMAX RG) by (eapply W_drain_feed.dr_feed_p; eassumption).
assert (FEEDS : dr_feeds_stmt B MT MMAX RG) by (eapply W_drain_feed.dr_feeds_p; eassumption).
assert (ADDB : W_gsaddb_cx.gs_addb_stmt B MT MMAX RG) by (eapply W_gsaddb.gs_addb; eassumption).
assert (SLOOP : W_gsscanb_cx.gs_scan_loop_stmt B MT MMAX RG) by (eapply W_gsscanb.gs_scan_loop; eassumption).
assert (PRO : dr_pro_stmt B MT MMAX RG) by (eapply W_drain_pro.dr_pro; eassumption).
assert (NEXT : dr_next_stmt B MT MMAX RG) by (eapply W_drain_next.dr_next; eassumption).
assert (REST : dr_rest_stmt B MT MMAX RG) by (eapply W_drain_rest.dr_rest; eassumption).
assert (DROPB : W_drain_dropb_cx.dr_dropb_stmt B MT MMAX RG) by (eapply W_drain_dropb.dr_dropb; eassumption).
assert (DROP : dr_drop_stmt B MT MMAX RG)
  by (eapply W_drain_drop.dr_drop_of; first [exact DROPB | eassumption]).
assert (FREE : W_drain_gs.gs_free_stmt B MT MMAX RG) by (eapply W_gsfree_scratch.gs_free; eassumption).
assert (SCAN : W_drain_gs.gs_scan_stmt B MT MMAX RG)
  by (eapply W_gsscan_scratch.gs_scan_of_loop; first [exact SLOOP | eassumption]).
assert (ADD : W_drain_gs.gs_add_stmt B MT MMAX RG)
  by (eapply W_gsadd_scratch.gs_adda; first [exact ADDB | eassumption]).
assert (GS : dr_gs_stmt B MT MMAX RG) by (eapply W_drain_gs.dr_gs_of; first [exact SCAN | exact ADD | exact FREE]).
assert (LINES : dr_lines_stmt B MT MMAX RG) by (eapply W_drain_lines.dr_lines; eassumption).
assert (EPI : dr_epi_stmt B RG) by (eapply W_drain_epi.dr_epi; eassumption).
assert (END : dr_end_stmt B MT MMAX RG) by (eapply W_drain_epi.dr_end; eassumption).
assert (OUTER : dr_outer_stmt B MT MMAX RG) by (eapply W_drain_outer.dr_outer; eassumption).
assert (ALL : dr_all_stmt B MT MMAX RG) by (eapply W_drain_all.dr_all; eassumption).
exact (W_drain.dr_assemble B MT MMAX RG PRO TOP FEED FEEDS DROP LINEA GS NEXT REST LINES EPI END OUTER ALL).
Qed.

End c.

(* ---- DR_x: pb_drain_x, drain's contract over any ARx (W_contract_x.v's dr_spec_x at A_drainP), generic in
   W_drain_cx_x.v's Section variables B PST ARx MT RP MMAX RG, from W_drain.v's dr_assemble_x and every generic
   segment and composition theorem. Its instance at (TfibB, [], ARX, MT, RPi, fr_MMAX, fr_RG) is
   W_LLVMFuzzerTestOneInput_top_x.v's Section hypothesis DR_x (A_drainP = BASE + AF_fr_drain by delta).
   The header is W_drain_cx_x.v Section c's text with the allocator rules in their caller-context `_c` forms at the
   tables CTX_R / CTX_F / CTX_S and drain's five call-site facts (a Theorem Labs lane's ruling 2026-10-30: the A top gives only
   `_c_x` rules), and the stage walks' instance facts HP0 / BLKN / PSTR / PSTG / PSTO; ALLOC_TAIL is
   W_drain_cx_x.alloc_tail_x of LAWS. The AR theorem pb_drain is kept as it is. ---- *)
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
(* the stage walks' instance facts (fixed texts, a Theorem Labs lane 2026-10-30) *)
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
(* the allocator's site rules in their caller-context forms over the generic journal (W_journal_x.v Section hc), one
   table per allocator entry; each drain site hands the rule a cut chain, so each trace is its return address alone *)
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x170] CTX_R.   (* realloc #1 returns to 0x8324c *)
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x7e8] CTX_R.   (* realloc #2 returns to 0x838c4 *)
Hypothesis HCTX_fr1 : In [BASE + AF_fr_drain + 0x540] CTX_F.   (* free #1 returns to 0x8361c *)
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0x874] CTX_F.   (* free #2 returns to 0x83950 *)
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x808] CTX_S.    (* strndup returns to 0x838e4 *)
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

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): pb_drain_xR, drain's contract at R (W_contract_xR.v's dr_spec_xR at A_drainP),
   from W_drain.v's dr_assemble_xR, each stage theorem's and composition's R twin.  pb_drain_x after End wR is it at
   R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the cf rules at R and the call-boundary facts their sites owe (a Theorem Labs lane's texts, as in lib/B's Section wR blocks):
   RO / RO_ARx and HA / HA_call *)
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
assert (PRO : dr_pro_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_pro.dr_pro_xR; eassumption).
assert (TAIL : W_drain_topb_cx.dr_toptail_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_topb.dr_toptail_xR; eassumption).
assert (TOP : dr_top_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_top.dr_top_xR; eassumption).
assert (FEED : dr_feed_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_feed.dr_feed_p_xR; eassumption).
assert (FEEDS : dr_feeds_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_feed.dr_feeds_p_xR; eassumption).
assert (ADDB : W_gsaddb_cx.gs_addb_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_gsaddb.gs_addb_xR; eassumption).
assert (SLOOP : W_gsscanb_cx.gs_scan_loop_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_gsscanb.gs_scan_loop_xR; eassumption).
assert (FREE : W_drain_gs.gs_free_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_gsfree_scratch.gs_free_xR; eassumption).
assert (SCAN : W_drain_gs.gs_scan_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_gsscan_scratch.gs_scan_of_loop_xR; first [exact SLOOP | eassumption]).
assert (ADD : W_drain_gs.gs_add_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_gsadd_scratch.gs_adda_xR; first [exact ADDB | eassumption]).
assert (GS : dr_gs_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_gs.dr_gs_of_xR; first [exact SCAN | exact ADD | exact FREE]).
assert (NEXT : dr_next_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_next.dr_next_xR; eassumption).
assert (REST : dr_rest_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_rest.dr_rest_xR; eassumption).
assert (EPI : dr_epi_stmt_xR B PST ARx RG R) by (eapply W_drain_epi.dr_epi_xR; eassumption).
assert (END : dr_end_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_epi.dr_end_xR; eassumption).
assert (LINEB : W_drain_lineb_cx.dr_lineb_stmt_xR B PST ARx MT RP MMAX RG R)
  by (eapply W_drain_lineb.dr_lineb_xR; eassumption).
assert (LINEA : dr_linea_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_linea.dr_linea_xR; eassumption).
assert (DROP : dr_drop_stmt_xR B PST ARx MT RP MMAX RG R) by (eapply W_drain_drop.dr_drop_xR; eassumption).
pose proof (W_drain_lines.dr_lines_xR B PST ARx MT RP MMAX RG R) as LINES.
pose proof (W_drain_outer.dr_outer_xR B PST ARx MT RP MMAX RG R) as OUTER.
pose proof (W_drain_all.dr_all_xR B PST ARx MT RP MMAX RG R) as ALL.
exact (W_drain.dr_assemble_xR B PST ARx MT RP MMAX RG R PRO TOP FEED FEEDS DROP LINEA GS NEXT REST LINES
  EPI END OUTER ALL).
Qed.

End wR.

(* ---- pb_drain_x is pb_drain_xR at R := wle, with RO / HA trivial and each strict rule or callee spec lifted to its
   R form at wle (W_journal_x.v <rule>_xR_of_x, W_contract_xR.v / W_send_line_xR.v <spec>_x_wle), as W_drain_top.v's
   dr_top_x. ---- *)
Theorem pb_drain_x : dr_spec_x B PST ARx MT RP MMAX RG A_drainP.
Proof.
exact (dr_spec_x_of_xR _ _ _ _ _ _ _ _ (pb_drain_xR (@wle SEGS) (wle_refl SEGS) (wle_trans SEGS)
  (fun W W' (h : @wle SEGS W W') => h) (fun _ => True) (fun _ _ _ _ _ _ => True)
  (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ _ => I)
  ltac:(eapply arealloc_cf_rule_c_xR_of_x; exact AREALLOC)
  ltac:(eapply afree_cf_rule_c_xR_of_x; exact AFREE)
  ASTRNDUP SLSPEC LPSPEC)).
Qed.
End cx.
End b.
End a.

(* ---- DR_x: pb_drain_x's AR-free instance facts at the A image (PB_fr, B := TfibB, RG := fr_RG, PST := []), so that
   the plug (W8Entry-2, 2026-10-30) only cites them: the five call-site facts HCTX_* at ACk0.v's CTX_AREALLOC /
   CTX_AFREE and ACej.v's CTX_strndup; the static placement facts HCROM / HVS / HV9 / HV12 / HGSB / HSM / HRGD / HERRW
   / HERRNO by computation; HGSZ from lib/A/W_LLVMFuzzerTestOneInput_addI.v; HG / HGO / HGR / HROMO from W_LLVMFuzzerTestOneInput_G.v's inclusions
   into G_fr_c with gx_ok_incl / rom_out_incl (both conditions are pointwise in G, so they pass to a sub-list); and
   PSTR / PSTG / PSTO at PST = [].  The placement files are required here, for these lemmas only; the generic
   Sections above stay generic in PI (their closed types abstract PI, checked by About and the base / head
   comparison of their closed types). ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img ACk0 ACej AD2l AE2k W_LLVMFuzzerTestOneInput_cut
  W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_addI.

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
#[local] Notation TfibB := AD2l.TfibB.
#[local] Notation RG := W_LLVMFuzzerTestOneInput_cut.fr_RG.
#[local] Existing Instance AE2k.tfib_sink_head.
#[local] Notation HEV := (W_LLVMFuzzerTestOneInput_addI.zz_HEV AD2l.TfibB AD2l.TfibB_syms).

(* HCTX_* *)
Lemma drain_hctx_re1 : In [BASE + AF_fr_drain + 0x170] ACk0.CTX_AREALLOC.
Proof. unfold ACk0.CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_re2 : In [BASE + AF_fr_drain + 0x7e8] ACk0.CTX_AREALLOC.
Proof. unfold ACk0.CTX_AREALLOC. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_fr1 : In [BASE + AF_fr_drain + 0x540] ACk0.CTX_AFREE.
Proof. unfold ACk0.CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_fr2 : In [BASE + AF_fr_drain + 0x874] ACk0.CTX_AFREE.
Proof. unfold ACk0.CTX_AFREE. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma drain_hctx_sd : In [BASE + AF_fr_drain + 0x808] ACej.CTX_strndup.
Proof. unfold ACej.CTX_strndup. vm_compute. repeat (first [left; reflexivity | right]). Qed.

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
Lemma drain_HVS : VAL (A_OBJ 22) = rg_s RG.
Proof. vm_compute. reflexivity. Qed.
Lemma drain_HV9 : VAL (A_OBJ 9) = rg_client RG.
Proof. vm_compute. reflexivity. Qed.
Lemma drain_HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Proof. vm_compute. reflexivity. Qed.
Lemma drain_HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Proof. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity|]. vm_compute. reflexivity. Qed.
Lemma drain_HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma drain_HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno TfibB, as_errno TfibB + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Proof. apply zpairwise_disjb_ok. vm_compute. reflexivity. Qed.
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
(* HG / HGO: drain's G and its three gesture globals lie in G_fr_c, which gx_ok holds of *)
Lemma drain_HG : gx_ok segs TfibB (G_DR TfibB RG).
Proof.
apply (gx_ok_incl _ _ _ _ (W_LLVMFuzzerTestOneInput_G.c_HG_DR TfibB)).
exact (W_LLVMFuzzerTestOneInput_G.c_gx_ok TfibB (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB AD2l.TfibB_syms)
  (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB AD2l.TfibB_syms)
  (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB AD2l.TfibB_syms)).
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
- exact (W_LLVMFuzzerTestOneInput_G.c_gx_ok TfibB (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB AD2l.TfibB_syms)
    (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB AD2l.TfibB_syms)
    (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB AD2l.TfibB_syms)).
Qed.
(* HGR / HROMO: no read-only byte is in G_fr_c (c_rom_apart / c_rom_out), so none is in drain's G *)
Lemma drain_HGR : forall a, inG (G_DR TfibB RG) a -> ~ in_rom segs a.
Proof.
intros a Ha Hr. exact (W_LLVMFuzzerTestOneInput_G.c_rom_apart TfibB HEV a Hr (W_LLVMFuzzerTestOneInput_G.c_HG_DR TfibB a Ha)).
Qed.
Lemma drain_HROMO : rom_out segs TfibB (G_DR TfibB RG).
Proof.
apply (rom_out_incl _ _ _ _ (W_LLVMFuzzerTestOneInput_G.c_HG_DR TfibB)).
exact (W_LLVMFuzzerTestOneInput_G.c_rom_out TfibB AD2l.TfibB_syms HEV).
Qed.
(* HERRNO / HGSZ: errno's cell and g_s's zero shadow, from the start-up symbols (lib/A/W_LLVMFuzzerTestOneInput_addI.v) *)
Lemma drain_HERRNO : as_errno TfibB = as_tp TfibB - 164.
Proof. vm_compute. reflexivity. Qed.
Lemma drain_HGSZ : azs TfibB (rg_s RG) (4 * ASRC).
Proof. exact (W_LLVMFuzzerTestOneInput_addI.zz_HZS TfibB AD2l.TfibB_syms). Qed.
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
