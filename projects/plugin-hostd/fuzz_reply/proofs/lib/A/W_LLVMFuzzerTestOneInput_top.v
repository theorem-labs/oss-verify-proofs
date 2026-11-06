(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_write of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput - the jump
   table's arm 1 (fuzz_reply.c:704-708), from the arm's entry 0x843bc to the latch 0x84490, in the form of
   lib/A/W_LLVMFuzzerTestOneInput_cut.v's worked dispatch lf_seg_jt (entry state from the cut's facts, paj_run_tok,
   psrr_branch_tok, the next cut re-established) and of lib/A/W_source_reset.v's internal call (the callee's spec at
   its own G, lifted to the caller's journal by W_journal's ajournal_gx_sub).
   The arm: fuzz_u16(&in) (two shadow-checked byte reads of the input block, 0x843bc-0x8445c), fuzz_take(&in, u16, &p)
   (n = min(u16, in.n), 0x84460-0x84474, with in.n stored at F+144), then `if (s && n) list_push(&s->pending, p, n)`
   (0x84478-0x84488), then li s4,10 and the fall into the latch 0x84490.  The arm is also entered with s5 = 0 from
   the no-source path at 0x843b8 (INV_A 1's lregs_D allows it).
   The callee is W2's pb_list_push_g (lib/A/W_list_push.v), taken at list_push's own G (the 16 bytes of
   g_s[si].pending) with MMAX = cf_malloc_max = 2^30 - 2^20, and its journal lifted with ajournal_gx_G_mono and
   composed with W_journal's ajournal_gx_sub.
   What this file takes, and from whom (all Section hypotheses):
     the contract parameters, LAWS, HG, LS, RINV - _cut's Section w, verbatim;
     TL / MLAW / ARE / AMA / AMEMCPY - pb_list_push_g's allocator instance and site rules, verbatim;
     GWR / ERR - _cut's glob_wr_law / errno_law;
     HGs / HZS - the G-coverage and zero-shadow facts of g_s (no gx_rt of G_fr: G_fr holds errno, see _exit.v);
     HGW / HERRS / ROM_ERR - G_fr / errno facts, proved for G_fr_c in W_LLVMFuzzerTestOneInput_G.v (c_HGW, c_HERRS,
                 c_ROM_ERR);
     ROM_PIN - rom_out's pinning conjunct (W_journal.v:397), the start-up instance's debt;
     RI_write_* and LS_write_* - the arm's open model obligations. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_write.v, with its module paths and module names changed; 129 of its 215 lines of code are new or changed and 2247 lines of the source are left out. *)
(* The entry composition of fuzz_reply.asan's LLVMFuzzerTestOneInput at the concrete
   G_fr = G_fr_c B (W_LLVMFuzzerTestOneInput_G.v).  lf_contract_of_segments (_cut.v:650) is applied with every
   segment proved so far plugged in, and each segment still open taken as a Section hypothesis in _cut.v's own text
   at G_fr_c B.  As a piece lands, its hypothesis here is replaced by its theorem; the file must compile at every step
   (that is the check that the piece's statement is the _cut.v text, and that its extra Section hypotheses are
   discharged or carried here by name).

   Plugged in now (ARM_add, a Theorem Labs lane 21c8237aca8; ARM_close / eintr / sendmax / default, a Theorem Labs lane 45f5b1d4122;
   ARM_write, a Theorem Labs lane 3ccac58d123; MMAX pinned to WR_MMAX = 2^30 - 2^20):
     SEG_HEAD  - lf_seg_head (_head.v:1521), its HGnout / HERRNO from _G.v, its model rules carried below;
     SEG_LATCH - lf_seg_latch (_latch.v:799, a Theorem Labs lane), W1_check_bounded from W1's pb_check_bounded
                 (W_check_bounded.v:391, with a working branch 817ce9dd54a's kept clause) by lt_cbk_of_cb, ERRNO_LOW
                 from _G.v.
   Still Section hypotheses: SEG_PRO, the ten arms, SEG_EXIT (FREE-W8.md (sha256 b75e6b922a31; internal record) rows); ARM_drain stays one until
   dr_found_join (_drain.v:1776) is Qed, so that this file rests on no Admitted lemma.
   Instance facts: LAWS; HEV, HOWN (as in _G.v: AF0m's ts_errno / ts_owned); HZS (AF0m's ts_zsh, measured in _G.v's
   header); TL (the allocator instance). The RINV / LS rule families are the NAMED OBLIGATION of FREE-W8.md (sha256 b75e6b922a31; internal record): the
   composition must exhibit RINV and LS at the entry state; until then these rules are hypotheses about Variables. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_check_bounded.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_addI W_LLVMFuzzerTestOneInput_small.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_check_shape_done.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m W_palib_fr ACk0.
(* RelocA's implicit-instance guard (lib/A/ReplyGuard.v, carried by path from a working branch c8b8af5eeeb):
   no sink class resolves by inference after it, so the ASan sink_head is passed with @ below *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyGuard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* check_bounded's objects are apart, at the pinned placement (W_check_bounded.v:52, its CBAP) *)
Lemma orle_of_b : forall a b c d, ((a <=? b) || (c <=? d))%bool = true -> a <= b \/ c <= d.
Proof.
  intros a b c d H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; [left|right]; exact H.
Qed.

Section top.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
Lemma fr_CBAP : cb_objs_apart (PI := PB_fr).
Proof.
  unfold cb_objs_apart. cbv zeta.
  repeat match goal with |- _ /\ _ => split end; apply orle_of_b; vm_compute; reflexivity.
Qed.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
(* W1Verify's ARx check_bounded (a working branch be8158006bd) re-derives pb_check_bounded at ARi0 and takes
   the laws there; the instance builds them once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR LAWS ..) with
   the three AR facts AR_laws_x_of_AR takes (stack bounds 8-aligned, the tail granule, the const cells) *)
Hypothesis LX0 : AR_laws_x segs B (ARi0 segs B) 0.
(* ---- the instance: AF0m's start-up table (HEV, HOWN, HZS, ROMPIN, GSHV, ERRL from it by a Theorem Labs lane's
   lib/A/W_LLVMFuzzerTestOneInput_addI.v; TL by W1Verify's palib_tfib, lib/A/W_palib_fr.v) ---- *)
Hypothesis TS : TfibSyms B.
(* ---- callee contracts still taken as hypotheses: op_add's (W2's pb_op_add_g through zz_OA_from_W2 takes these),
   and the default arm's two libc calls (R5's rt_pthread_mutex_lock / unlock, a working branch b1c048a98a5) ---- *)
Hypothesis MLAW : ameter_laws MT.
Hypothesis AMA : amalloc_cf_rule_c (SK := AE2k.tfib_sink_head) segs B MT WR_MMAX CTX_AMALLOC.
Hypothesis SR : sr_spec_g (SK := AE2k.tfib_sink_head) B MT (BASE + AF_fr_source_reset).
(* relay_add over K0's realloc table CTX_AREALLOC (ACk0.v; the _c rules' caller-context instance) *)
Hypothesis RA : ra_spec_g (SK := AE2k.tfib_sink_head) B MT fr_globals CTX_AREALLOC (BASE + AF_fr_relay_add).
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ---- SEG_HEAD's model rules (_head.v:389, :391, :981, :985), verbatim ---- *)
Hypothesis RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
Hypothesis LS_head_nout : forall cx t m ly S, LS cx t m ly S -> LS cx t (lm_clear_O m) ly S.
Hypothesis RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Hypothesis LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LS cx t m ly S -> LS cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.

(* ---- ARM_add's model rules (_add.v), verbatim ---- *)
Hypothesis RI_add_pre : forall cx t m,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Hypothesis RI_add_open : forall cx t m i q pj ev,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (ad_open m i q pj ev).
Hypothesis RI_add_none : forall cx t m,
  RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None -> RINV cx (t + 1) (ad_none m).
(* the allocator-state facts op_add's contract takes (whether or not a slot is free), read off LS *)
Hypothesis LS_add_room : forall cx t m ly S,
  LS cx t m ly S -> RINV cx t m -> ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S (oa_cost MT).
Hypothesis LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LS cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  LS cx (t + 1) (ad_open m i q pj ev) ly' S'.
Hypothesis LS_add_none : forall cx t m ly S,
  LS cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LS cx (t + 1) (ad_none m) ly S.
(* ---- the small arms' model rules (_small.v, at the walk's choice), verbatim ---- *)
Hypothesis RI_close : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_close cx m i).
Hypothesis RI_eintr : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_eintr cx m i).
Hypothesis RI_sendmax : forall cx t m, RINV cx t m ->
  RINV cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
Hypothesis RI_default : forall cx t m, RINV cx t m -> RINV cx (t + 1) (sm_default cx m (sm_dg cx m)).
Hypothesis LS_close : forall cx t m i ly S, LS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LS cx (t + 1) (sm_close cx m i) ly S.
Hypothesis LS_eintr : forall cx t m i ly S, LS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LS cx (t + 1) (sm_eintr cx m i) ly S.
Hypothesis LS_sendmax : forall cx t m ly S, LS cx t m ly S ->
  LS cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Hypothesis LS_default : forall cx t m ly S, LS cx t m ly S -> LS cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.

(* ---- ARM_write's callee rules and model rules (_write.v, a Theorem Labs lane), verbatim (AMA renamed AMA_w) ---- *)
Hypothesis ARE : arealloc_cf_rule_c (SK := AE2k.tfib_sink_head) segs B MT WR_MMAX CTX_AREALLOC (SIGMA WS_realloc).
Hypothesis AMA_w : amalloc_cf_rule_c (SK := AE2k.tfib_sink_head) segs B MT WR_MMAX CTX_AMALLOC.
Hypothesis AMEMCPY : aintrin_realizes segs B OCpy (SIGMA WS_asan_memcpy).
Hypothesis RI_write_skip : forall cx t m,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
  RINV cx (t + 1) (wr_skip m (wr_k2 cx m)).
Hypothesis LS_write_skip : forall cx t m ly S,
  LS cx t m ly S -> LS cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Hypothesis RI_write_push : forall cx t m si h l' d ev,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev).
Hypothesis LS_write_room : forall cx t m si h ly S,
  LS cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok MT S (lp_cost MT (hs_pending h) (wr_n cx m)).
(* W8Add's proposed text (ReplyLS.v atop_LS_write_push_prop, a working branch f57b3e2d0ca, proved at the
   instance), adopted as the arm states it (a Theorem Labs lane 23184ff5c2a): lp_post's facts about the pushed list l' *)
Hypothesis LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LS cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  LS cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.

(* ---- the segments still open: _cut.v:565-595 at G_fr := G_fr_c B ---- *)
Hypothesis SEG_PRO : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre (G_fr_c B) cx ->
  SRr segs (c_W cx) (lf_entry cx)
    (fun W' c' => INV_H B (G_fr_c B) fr_FP LS RINV cx 0 W' c' \/ INV_X B (G_fr_c B) fr_FP LS RINV cx W' c').
Hypothesis ARM_drain : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre (G_fr_c B) cx ->
  INV_A B (G_fr_c B) fr_FP LS RINV 2 cx t W c -> SRr segs W c (INV_K B (G_fr_c B) fr_FP LS RINV cx t).
(* ARM_remove (a Theorem Labs lane, 008b4688edd) is merged but NOT plugged in this head: its file predates the cut's flag word
   and the req_size clause, and its holder is adapting it; the segment stays a hypothesis until then *)
Hypothesis ARM_remove : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre (G_fr_c B) cx ->
  INV_A B (G_fr_c B) fr_FP LS RINV 4 cx t W c -> SRr segs W c (INV_K B (G_fr_c B) fr_FP LS RINV cx t).
Hypothesis ARM_gone : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre (G_fr_c B) cx ->
  INV_A B (G_fr_c B) fr_FP LS RINV 5 cx t W c -> SRr segs W c (INV_K B (G_fr_c B) fr_FP LS RINV cx t).
Hypothesis ARM_event : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre (G_fr_c B) cx ->
  INV_A B (G_fr_c B) fr_FP LS RINV 7 cx t W c -> SRr segs W c (INV_K B (G_fr_c B) fr_FP LS RINV cx t).
Hypothesis SEG_EXIT : forall cx W c, lf_base B MT XM_LIB RLO RHI fr_live_pre (G_fr_c B) cx ->
  INV_X B (G_fr_c B) fr_FP LS RINV cx W c -> SRr segs W c (lf_post B MT XN_LIB fr_live_post fr_surv (G_fr_c B) fr_FP cx).

(* The lemma (W8Latch.md (sha256 0036a3f1aae1; internal record)): with the kept clause in aleafx_post, cbk_spec is cb_spec's post
   minus two conjuncts *)
Lemma lt_cbk_of_cb :
  @cb_spec fx rc AE2k.tfib_sink_head PB_fr B (A_check_boundedP (PI := PB_fr)) -> cbk_spec B (BASE + AF_fr_check_bounded).
Proof.
  intros HCB W ly S regs mem md ch n P N HPRE Hn Hns Hsr HP Hblk Hent.
  eapply SRr_mono; [exact (HCB W ly S regs mem md ch n P N HPRE Hn Hns Hsr HP Hblk Hent)|].
  intros W' c' _ (regs' & mem' & md' & Hc & HJ & HR & _ & HK & _).
  exists regs', mem', md'. split; [exact Hc|]. split; [exact HJ|]. split; [exact HR | exact HK].
Qed.

Theorem fr_contract_top :
  @fr_lib_contract_cf fx rc checksum_shape B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv (G_fr_c B) fr_FP.
Proof.
  assert (HMMAX : APARTIAL < WR_MMAX) by (pose proof wr_HMMAX; unfold APARTIAL; lia).
  pose proof (zz_HEV B TS) as HEV. pose proof (zz_HOWN B TS) as HOWN. pose proof (zz_HZS B TS) as HZS.
  pose proof (palib_tfib B TS) as TL. pose proof (c_gx_ok B HEV HOWN (zz_HKEPT B TS)) as HG.
  pose proof (zz_HGOBJ B) as HGOBJ. pose proof (zz_ERRL B TS) as ERRL.
  pose proof (zz_ROMPIN B TS) as ROMPIN. pose proof (zz_GSHV B TS) as GSHV.
  pose proof (zz_OA_from_W2 B MT TS LX0 TL MLAW WR_MMAX HMMAX AMA SR RA) as OA.
  pose proof (c_HGs B) as HGs. pose proof (c_HG_smax B) as HGmx. pose proof (c_HG_seintr B) as HGei.
  pose proof (c_HG_sdead B) as HGdd. pose proof (c_HG_gone B) as HGgn. pose proof (c_HG_client B) as HGcl.
  pose proof (c_HGlock B) as HGlk. pose proof (c_HERRHI B HEV) as HERRHI.
  pose proof (lt_cbk_of_cb (@pb_check_bounded fx rc AE2k.tfib_sink_head PB_fr B LX0 TL fr_CBAP)) as HCBK.
  (* ARM_write's placement facts at G_fr_c B *)
  pose proof (c_glob_wr B HEV) as GWR. pose proof (c_HGW B) as HGW. pose proof (c_HERRS B HEV) as HERRS.
  pose proof (c_ROM_ERR B HEV) as ROM_ERR. pose proof ROMPIN as ROM_PIN.
  refine (lf_contract_of_segments B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv (G_fr_c B) fr_FP
    LAWS HG LS RINV SEG_PRO _ _ _ ARM_drain _ ARM_remove ARM_gone _ ARM_event
    _ _ _ SEG_EXIT).
  - exact (lf_seg_head B MT XM_LIB RLO RHI fr_live_pre (G_fr_c B) fr_FP LAWS HG LS RINV (c_HGnout B) (c_HERRNO B HEV)
      RI_head_nout LS_head_nout HZS RI_head_skip LS_head_skip).
  (* the arms Qed: each is applied with its own Section hypotheses, all in context; a Section variable the arm's
     statement does not fix is the composition's own (any value of its type does) *)
  - intros cx t W c HB HA. eapply lf_arm_add; try eassumption.
    Unshelve. all: first [exact XN_LIB | exact fr_live_post | exact fr_surv].
  - intros cx t W c HB HA. eapply lf_arm_write; try eassumption.
    Unshelve. all: first [exact XN_LIB | exact fr_live_post | exact fr_surv].
  - intros cx t W c HB HA. eapply lf_arm_close; try eassumption.
    Unshelve. all: first [exact XN_LIB | exact fr_live_post | exact fr_surv].
  - intros cx t W c HB HA. eapply lf_arm_eintr; try eassumption.
    Unshelve. all: first [exact XN_LIB | exact fr_live_post | exact fr_surv].
  - intros cx t W c HB HA. eapply lf_arm_sendmax; try eassumption.
    Unshelve. all: first [exact XN_LIB | exact fr_live_post | exact fr_surv].
  - intros cx t W c HB HA. eapply lf_arm_default; try eassumption.
    Unshelve. all: first [exact XN_LIB | exact fr_live_post | exact fr_surv].
  - exact (lf_seg_latch B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv (G_fr_c B) fr_FP LAWS HG LS RINV
      HCBK (c_ERRNO_LOW B HEV)).
Qed.
End top.

(* the guard holds in this file's context (every W8 piece loaded): a bare sink binder does not resolve *)
Fail Definition top_bare_head : Z := YI16.sk_ofl_head.
Fail Definition top_bare_lock : Z := YI14.sk_ofl_lock.
