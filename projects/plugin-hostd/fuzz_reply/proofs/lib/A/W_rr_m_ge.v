(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: hop GE of the MATCH segment of the ASan walk of fuzz_reply's relay_remove
   (lib/A/W_rr_match_cx.v hop_ge_stmt): RRG i 0x83f68 -> ld a0, g_src; add a0, a0, s8; jal gestures_end 0x83f70
   (GSE at BASE + AF_fr_gestures_end, ra 0x83f74) -> RRF i 0x83f74.

   rule 24: proves function relay_remove MATCH hop 2 (kind: segment lemma of the W6 walk, PORTED from 2ad36763b22
   relay_remove_p_c_ge_asm.v rrA_stage_c_ge / relay_remove_p_c_ge.v; lookup + CONFIRM in context).

   Where each part comes from (the retired lane form: commit 2ad36763b22, lib/A/Prog/relay_remove_p_c_ge*.v):
   - rgl_live_*: the lane's liveness algebra rrA_ge_no_al / rrA_ge_live_or / rrA_ge_off_br / rrA_live_eq
     (p_c_ge.v:626-876), restated over W_contract.v's ctl (sl_live / sl_ctl / dr_ctl).
   - rgl_sends: new (gse_run, which threads g_nout, against rr_found's sl_sends).
   - rgl_cost_lv / rgl_ge_cost / rgl_tr_sl: the lane's trace algebra ge_gtr_er / rrA_ge_shape (p_c_ge.v:608, :898),
     restated as gse_cost = the cost of the key run plus the held array's free.
   - rgl_fin_no / rgl_match / rgl_trK (rr_tr's key run in the call's g_nout / g_capout): the lane's rrA_sD_no /
     rrA_ge_ocap_all / rrA_ge_noc (p_c_ge.v:790, :933, :954), through the plain model's relay_remove_b_aux.rma_fin_no
     / rma_fin_cap / rma_ge_dead.
   - rgl_fp_* (the footprints of the representation predicates lie in their blocks): new, the form of
     W_rr_tail.v rfz_alist / rfz_asrc / rfz_aentry with the blocks named.
   - rgl_keep_img / rgl_keep_blk / rgl_notfp (what gestures_end's journal keeps): new.
   - the Permutation algebra (gestures_end's entry form from RRG's, RRF's from gse_post's): new (the lane had no
     Permutation, Appendix A §9(2) of PREP.md (sha256 02e2eed258c7; internal record)).
   - rr_m_ge: the lane's rrA_stage_c_ge_of_G2 / rrA_stage_c_ge (p_c_ge_asm.v:271, :623).  Ported: the call's
     premises (the table cell, the held part, the controller, the room and the meter) and the post's G1..G4
     groups (regs and frame, globals and the cleared slot, the harness source, the blocks).  New: the symbolic
     run 0x83f68 -> the callee's entry (W_rr_scan.v's form), the call through W_gestures_end.v gse_callS_x (Section c)
     with the callee journal lifted by rr_lift_SL, RLIVE at the return by
     W_rr_m_kit.v rr_live_call, the callee chain by W_rr_m_kit.v rr_call_chain, and RRF's bookkeeping.
   - rgl_hgroom (gse_spec's gse_room at the call, C3's text: bb moves by each key's tr_net (ge_tr ..) and the free
     of the key's |x| + 1 bytes) and its helpers rgl_tm_f / rgl_ge_tr / rgl_room: new, from RRG's rmbud (the peak
     of the key run, W_tr_peak.v tr_peak_prefix) through rgl_trK; one gesture_end's peak / net / largest request at
     any addresses by W_tr_peak.v tr_sz_measures / gesture_end_tr_sz (the lane's room is rrA_ge_room_call,
     p_c_ge.v:724, over its resource form).
   The " end\0" bytes come from the cx Section's HEND5L. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (a Theorem Labs lane, lane RR_x): hop GE over ANY
   allocator relation ARx (Section c is W_relay_remove_cx.v's generic block, verbatim); rr_m_ge : hop_ge_stmt B PST
   ARx MT RP MMAX RG.  The journal lemmas, the laws and W_gestures_end.v's helpers are their _x twins (gse_callS_x,
   gse_keep_img_x with the PST premise PSTG gives for HRGP's cells, gse_nodup_x); the callee is GSE : gse_spec_x at
   kr := 1 + kr of the entry.  Its room premise comes from RRG's rmbud by RMM_of (rgl_cost_lv, now at any meter, gives
   gestures_end's cost at the counting meter MT_rk as the key run's plus one free; rmtrF charges two frees), its count
   premise is RRG's gse_pk fact; RRF's room is gse_post_x's rp_RM, RRF's count fact cnt_ok follows from RRG's gse_pk
   fact (rgl_cnt_ge: the blocks lose gse_blks and the g_out block, at most one, is replaced). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx W_rr_match_cx W_rr_m_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rr_scan W_gesture_end W_gestures_end W_gse_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
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

(* ---- The seat at 0x83f68 (A_rr_ge): the registers are atoms 0 .. 31 (s8 = 56 i: atom 24, s6 = SB: atom 22);
   atom 32 = G0 = g_src, held by g_src's cell (A_OBJ 8, read by the PLdHi at 0x83f68).  Nothing is stored before
   the jal, so the run's memory is the cut's (W_rr_scan.v's form). ---- *)
Definition RGE_PHI : Z := 140737479966720.
Definition RGE_BX : sv := SOff 22 0.
Definition rge_regions : smem := [ YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
Definition rge_facts : facts := mkFacts [ (32%nat, mkAF 4096 RGE_PHI 4) ] [] [].
Definition rge_sr : list sv := sr_set sr_atoms 25%bv (SOff (A_HI 60) 0).
Definition ss_rge : sstate := mkSS A_rr_ge rge_sr rge_regions None rge_facts.
Definition rge_SH : list shent := [].
Definition rge_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rge_extra (g : Z) : list word := map (Z_to_bv 64) [g].
Definition RGE_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
Ltac rge_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL): K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x, blk_off_imgP_x), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x83ee8 (s7, listing A_HI 59) and 0x83ef8 (s9, A_HI 60).
   The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges both by
   vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH59 : VAL (A_HI 59) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH60 : VAL (A_HI 60) = rg_src RG + RR_HI_SRC.
(* g_wake[1], read at 0x83fe0 by PLdHi (A_OBJ 4) (W5's HV4, verbatim) *)
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal.v ajournal_gx_rom_view) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the live-state meter does not see the fake frame: its seat and its release are set_fs steps (W8's ruling, the
   lead's KF-COUNT #4: the ablocks form is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v / W_journal.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls (W7's drain, W4's gestures_end), by their published _x specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x83f94 with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (W_relay_finish_h.v's PSTR / PSTC form). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

(* ------------------------------------------------------------------ liveness (the lane's rrA_ge_live_or / off_br,
   relay_remove_p_c_ge.v:641-669, over W_contract.v's ctl) *)
Lemma rgl_off_nz : forall cl br x y, x <> 0 -> y <> 0 -> send_line_c.send_off cl br x = send_line_c.send_off cl br y.
Proof.
intros cl br x y Hx Hy. unfold send_line_c.send_off.
rewrite (proj2 (Z.eqb_neq x 0) Hx), (proj2 (Z.eqb_neq y 0) Hy). reflexivity.
Qed.
Lemma rgl_live_nz : forall c x, x <> 0 -> sl_live c x = sl_live c 1.
Proof. intros c x Hx. unfold sl_live, send_line_c.send_live. rewrite (rgl_off_nz _ _ x 1 Hx ltac:(lia)). reflexivity. Qed.
(* a send of len <> 0 leaves g_client_broken = g_send_dead when it is not off: liveness for any length is kept *)
Lemma rgl_live_upd : forall cl br dd len y, len <> 0 -> y <> 0 ->
  send_line_c.send_live cl (if send_line_c.send_off cl br len then br else dd) dd y = send_line_c.send_live cl br dd len.
Proof.
intros cl br dd len y Hl Hy.
destruct (send_line_c.send_off cl br len) eqn:Eo.
- unfold send_line_c.send_live. rewrite (rgl_off_nz cl br y len Hy Hl), Eo. reflexivity.
- unfold send_line_c.send_live. rewrite Eo. unfold send_line_c.send_off in *.
  rewrite (proj2 (Z.eqb_neq y 0) Hy). rewrite (proj2 (Z.eqb_neq len 0) Hl) in Eo.
  apply orb_false_iff in Eo as [Eo _]. apply orb_false_iff in Eo as [Ecl _]. rewrite Ecl. cbn [orb negb andb].
  destruct (Z.eqb_spec dd 0) as [->|Hd]; [reflexivity|]. rewrite andb_false_r. reflexivity.
Qed.
Lemma rgl_live_ctl : forall c len y, len <> 0 -> y <> 0 -> sl_live (sl_ctl c len) y = sl_live c len.
Proof.
intros [cl br dd ei ev] len y Hl Hy. unfold sl_live, sl_ctl. cbv zeta. cbn [ct_cl ct_br ct_dd].
apply rgl_live_upd; assumption.
Qed.
Lemma rgl_live_ge : forall c x y, x <> 0 -> y <> 0 -> sl_live (ge_ctl c x) y = sl_live c 1.
Proof.
intros c x y Hx Hy. unfold ge_ctl. rewrite (rgl_live_ctl (sl_ctl c x) 5 y) by lia.
rewrite (rgl_live_ctl c x 5) by lia. apply rgl_live_nz. exact Hx.
Qed.
Lemma rgl_live_dr : forall c h ev y, y <> 0 -> sl_live (dr_ctl c h ev) y = sl_live c 1.
Proof.
intros [cl br dd ei ev0] h ev y Hy. unfold sl_live, dr_ctl. cbv zeta. cbn [ct_cl ct_br ct_dd].
destruct (Z.eq_dec (dr_tot h) 0) as [E|E].
- assert (E0 : send_line_c.send_off cl br (dr_tot h) = true)
    by (unfold send_line_c.send_off; rewrite E, Z.eqb_refl, orb_true_r; reflexivity).
  rewrite E0. unfold send_line_c.send_live. rewrite (rgl_off_nz cl br y 1 Hy ltac:(lia)). reflexivity.
- rewrite (rgl_live_upd cl br dd (dr_tot h) y E Hy).
  unfold send_line_c.send_live. rewrite (rgl_off_nz cl br (dr_tot h) 1 E ltac:(lia)). reflexivity.
Qed.
Lemma rgl_live_c1 : forall cx i ev y, y <> 0 -> sl_live (rmc1 cx i ev) y = sl_live (rxc cx) 1.
Proof.
intros cx i ev y Hy. unfold rmc1. destruct (rmopen cx i); [apply rgl_live_dr | apply rgl_live_nz]; exact Hy.
Qed.

(* ------------------------------------------------------------------ gse_run as rr_found's sl_sends (new) *)
Lemma rgl_len5 : length END5 = 5%nat.
Proof. reflexivity. Qed.
Lemma rgl_no : forall c O x, Z.of_nat (length (ge_O c O x)) = ge_no c (Z.of_nat (length O)) (Z.of_nat (length x)).
Proof.
intros c O x. unfold ge_O, ge_no, sl_O, sl_no. rewrite rgl_len5. change (Z.of_nat 5) with 5.
destruct (sl_live c (Z.of_nat (length x))), (sl_live (sl_ctl c (Z.of_nat (length x))) 5);
rewrite ?length_app, ?rgl_len5; lia.
Qed.
Lemma rgl_cap : forall c mx O cap x,
  ge_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length x)) =
  sl_cap (sl_ctl c (Z.of_nat (length x))) mx (Z.of_nat (length (sl_O c O x)))
    (sl_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length x))) 5.
Proof.
intros c mx O cap x. unfold ge_cap. f_equal. unfold sl_no, sl_O.
destruct (sl_live c (Z.of_nat (length x))); rewrite ?length_app; lia.
Qed.
Lemma rgl_sends : forall mx (ks : list (Z * list byte * list byte)) c O cap,
  sl_sends mx c O cap (ge_bytes ks) =
  (gse_c (gse_run c O mx (Z.of_nat (length O)) cap (map key_text ks)),
   gse_O (gse_run c O mx (Z.of_nat (length O)) cap (map key_text ks)),
   gse_cap (gse_run c O mx (Z.of_nat (length O)) cap (map key_text ks))).
Proof.
intros mx ks. induction ks as [|k ks IH]; intros c O cap; [reflexivity|].
unfold ge_bytes. cbn [map concat app]. fold (ge_bytes ks).
cbn [sl_sends gse_run map].
rewrite IH. rewrite <- rgl_no, <- rgl_cap. reflexivity.
Qed.

(* ------------------------------------------------------------------ the meter (the lane's ge_gtr_er /
   rrA_ge_shape, relay_remove_p_c_ge.v:608, :898): gse_cost is the key run's cost plus the held array's free *)
Lemma rgl_tc_cons : forall (M : ameter_ops) {P : Type} (ev : RelayRunT.rev P) t,
  tr_cost M (ev :: t) = tr_cost M [ev] + tr_cost M t.
Proof. intros M P ev t. unfold tr_cost. cbn [fold_right]. lia. Qed.
(* at the room round's counting meter MT_rk no trace costs less than 0 *)
Lemma rgl_rk_nonneg : forall {P : Type} (t : list (RelayRunT.rev P)), 0 <= tr_cost MT_rk t.
Proof.
intros P t. induction t as [|ev t IH]; [unfold tr_cost; cbn [fold_right]; lia|].
rewrite rgl_tc_cons. assert (0 <= tr_cost MT_rk [ev]); [|lia].
destruct ev; unfold tr_cost, MT_rk; cbn [fold_right mo_malloc mo_free]; lia.
Qed.
Lemma rgl_tr_sl : forall M f mx no cap rem j o,
  tr_cost M (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run M f mx no cap rem.
Proof.
intros M. induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_cost_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|]. cbv zeta.
match goal with |- context [cap <? ?x] => destruct (cap <? x) end; cbn [fst]; [|apply IH].
rewrite rgl_tc_cons, IH. destruct (cap =? 0); unfold tr_cost at 1; cbn [fold_right]; lia.
Qed.
Lemma rgl_tr_send : forall M live mx no cap len j o,
  tr_cost M (send_line_b_c.send_line_tr live mx no cap len j o) =
  if live then sl_cost_run M (Z.to_nat len) mx no cap len else 0.
Proof.
intros M live mx no cap len j o. unfold send_line_b_c.send_line_tr. destruct live; [apply rgl_tr_sl | reflexivity].
Qed.
Lemma rgl_ge_cost : forall M c mx no cap no' cap' XL j o, XL <> 0 ->
  (sl_live c 1 = true -> no = no' /\ cap = cap') ->
  ge_cost M c mx no cap XL = tr_cost M (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no' cap' XL j o).
Proof.
intros M c mx no cap no' cap' XL j o HX HL. unfold ge_cost, sl_cost, gesture_end_b_c.gesture_end_tr.
rewrite rm_tr_cost_app, !rgl_tr_send. rewrite (rgl_live_ctl c XL 5) by lia. rewrite (rgl_live_nz c XL HX).
destruct (sl_live c 1) eqn:L; [|lia].
destruct (HL eq_refl) as [<- <-]. unfold sl_no, sl_cap. rewrite (rgl_live_nz c XL HX), L. reflexivity.
Qed.
(* at any meter M (the walk's MT and the room round's counting meter MT_rk) *)
Lemma rgl_cost_lv : forall M (xs : list (list byte)) (ka : RelayRunT.addr YO0i.sptr) c mx no cap no' cap' j o lv,
  lv = sl_live c 1 ->
  Forall (fun x : list byte => x <> []) xs ->
  (lv = true -> no = no' /\ cap = cap') ->
  gse_cost M c mx no cap xs =
  tr_cost M (fst (keys_end_run lv mx no' cap' (map (fun x : list byte => (Z.of_nat (length x), ka)) xs) j o))
  + mo_free M.
Proof.
intros M. induction xs as [|x xs IH]; intros ka c mx no cap no' cap' j o lv Elv HX HL; subst lv.
- cbn [gse_cost map keys_end_run fst]. unfold tr_cost. cbn [fold_right]. lia.
- apply Forall_cons_iff in HX as [Hx HX].
  assert (Hxl : Z.of_nat (length x) <> 0) by (destruct x as [|b x]; [congruence | cbn [length]; lia]).
  cbn [gse_cost map keys_end_run]. cbv zeta. cbn [fst].
  rewrite rm_tr_cost_app, rgl_tc_cons.
  assert (Ege : sl_live (ge_ctl c (Z.of_nat (length x))) 1 = sl_live c 1) by (apply rgl_live_ge; lia).
  rewrite (IH ka (ge_ctl c (Z.of_nat (length x))) mx (ge_no c no (Z.of_nat (length x)))
    (ge_cap c mx no cap (Z.of_nat (length x))) (no' + Z.of_nat (length x) + 5)
    (gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no' cap' (Z.of_nat (length x)))
    (j + RelayRunT.nret YO0i.sptr (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no' cap' (Z.of_nat (length x)) j o))%nat
    (gesture_end_b_c.gesture_end_out (sl_live c 1) mx no' cap' (Z.of_nat (length x)) j o) (sl_live c 1)
    (eq_sym Ege) HX).
  + rewrite (rgl_ge_cost M c mx no cap no' cap' (Z.of_nat (length x)) j o Hxl HL).
    assert (EF : tr_cost M [RelayRunT.RFree (Z.of_nat (length x) + 1) ka] = mo_free M)
      by (unfold tr_cost; cbn [fold_right]; lia).
    rewrite EF. lia.
  + intros L. destruct (HL L) as [<- <-].
    assert (L1 : sl_live c (Z.of_nat (length x)) = true) by (rewrite (rgl_live_nz c _ Hxl); exact L).
    assert (L2 : sl_live (sl_ctl c (Z.of_nat (length x))) 5 = true) by (rewrite (rgl_live_ctl c _ 5) by lia; exact L1).
    unfold ge_no, ge_cap, sl_no, sl_cap, gesture_end_b_c.gesture_end_cap. rewrite L1, L2, L.
    split; [lia | reflexivity].
Qed.
Lemma rgl_keys_map : forall (ks : list (Z * list byte * list byte)) (H : list (list Z)) {A : Type} (ka : A),
  drain_b_c.keys_texts ks = H ->
  map (fun x : list byte => (Z.of_nat (length x), ka)) (map key_text ks) = map (fun x : list Z => (Z.of_nat (length x), ka)) H.
Proof.
intros ks H A ka <-. unfold drain_b_c.keys_texts. rewrite !map_map. apply map_ext. intros k.
unfold bzs. rewrite length_map. reflexivity.
Qed.

(* ------------------------------------------------------------------ the key run of rr_tr in the call's terms (the
   lane's rrA_sD_no / rrA_ge_ocap_all / rrA_ge_noc, relay_remove_p_c_ge.v:790, :933, :954): when the run is live,
   g_nout and g_capout after drain are the stream's (relay_remove_b_aux.rma_fin_no / rma_fin_cap) *)
Lemma rgl_nozero : forall (U : list byte), ~ In (Z_to_bv 8 0) U -> RelayModel.nozero (bzs U).
Proof.
intros U HU. unfold RelayModel.nozero, bzs. apply Forall_map. apply Forall_forall. intros b Hb Hz. apply HU.
replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. unfold bz in Hz. rewrite Hz. reflexivity.
Qed.
Lemma rgl_entry : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat ->
  aentry_ok B (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rnth cx i).
Proof.
intros cx i HB Hi. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _). rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hi.
Qed.
Lemma rgl_fin_no : forall cx i lv, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
  rmopen cx i = true ->
  drain_b_c.ds_no (drain_b_c.drain_fin lv (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) = rmno cx + dr_tot (rxh cx).
Proof.
intros cx i lv HB Hi Hfd Ho.
pose proof (rgl_entry cx i HB Hi) as (Eeof & Eskip & _ & _ & _ & Ecap & EU1 & EU2 & EU3 & _).
assert (Ee0 : re_eof (rnth cx i) = 0) by (unfold rmopen in Ho; apply Z.eqb_eq; exact Ho).
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDS & _).
destruct (HDS i Hi Hfd Ee0) as (_ & HAS & _ & _ & HSO & HUW & _).
pose proof HAS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPEND & _ & _ & _ & _ & HOFF & _).
unfold dr_tot, dr_lines. apply relay_remove_b_aux.rma_fin_no.
- unfold RelayModel.J1, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
  split; [rewrite HSO; reflexivity|].
  split; [intros Hs; apply HUW; destruct Eskip as [E|E]; [exact E | rewrite E in Hs; discriminate]|].
  split; [unfold bzs; rewrite length_map; apply Nat2Z.inj_le; rewrite EU1;
    change (Z.of_nat RelayModel.LINE_LIMIT) with 6000; unfold APARTIAL in EU2; exact EU2|].
  apply rgl_nozero. exact EU3.
- unfold relay_remove_b_aux.rma_pok, drain_b_c.drain_init. cbn [drain_b_c.ds_off drain_b_c.ds_pend].
  destruct HOFF as [(Hr & Ho0) | (r & rs & Hr & Ho0)]; rewrite Hr; cbn [map].
  + split; [lia | exact I].
  + split; [lia|]. split; [unfold bzs; rewrite length_map; lia|].
    pose proof HPEND as (_ & _ & _ & _ & _ & _ & _ & _ & HF). rewrite Hr in HF. apply Forall_cons_iff in HF as [_ HF].
    apply Forall_map. eapply Forall_impl; [|exact HF]. intros r' (_ & _ & _ & H4).
    unfold bzs. rewrite length_map. apply H4. reflexivity.
- lia.
Qed.
Lemma rgl_match : forall cx i ly1 S1 W1 m1 e1 h1 LB,
  RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
  rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB -> sl_live (rxc cx) 1 = true ->
  Z.of_nat (length (rmO1 cx i LB)) = drain_b_c.ds_no (rms cx i) /\ rmcap1 cx i = drain_b_c.ds_ocap (rms cx i).
Proof.
intros cx i ly1 S1 W1 m1 e1 h1 LB HB Hi Hfd HDR HL.
unfold rmO1, rmcap1, rms, rmlive. unfold rmdrel in HDR. destruct (rmopen cx i) eqn:Eo.
- destruct HDR as (HDR & _). unfold dr_rel in HDR. cbv zeta in HDR.
  assert (HLB : Z.of_nat (length LB) = dr_tot (rxh cx)).
  { destruct HDR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & HW).
    unfold dr_tot. rewrite <- HW. unfold bzs. rewrite length_map. reflexivity. }
  cbn [andb]. unfold dr_fin. erewrite (rgl_fin_no cx i _ HB Hi Hfd Eo).
  destruct (dr_live (rxc cx) (rxh cx)) eqn:Ed.
  + split; [rewrite length_app, Nat2Z.inj_add, HLB; unfold rmno; reflexivity | reflexivity].
  + assert (HT : dr_tot (rxh cx) = 0).
    { destruct (Z.eq_dec (dr_tot (rxh cx)) 0) as [E|E]; [exact E|]. exfalso.
      unfold dr_live in Ed. rewrite (rgl_live_nz _ _ E), HL in Ed. discriminate. }
    split; [rewrite HT; unfold rmno; lia | symmetry; apply relay_remove_b_aux.rma_fin_cap].
- cbn [andb]. unfold drain_b_c.drain_init. cbn [drain_b_c.ds_no drain_b_c.ds_ocap]. split; reflexivity.
Qed.
Lemma rgl_keys_rms : forall cx i ly1 S1 W1 m1 e1 h1 LB, rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB ->
  drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H (rms cx i).
Proof.
intros cx i ly1 S1 W1 m1 e1 h1 LB HDR. unfold rmdrel, rms in *. destruct (rmopen cx i).
- destruct HDR as (HDR & _). unfold dr_rel in HDR. cbv zeta in HDR. destruct HDR as (_ & _ & _ & _ & _ & _ & HK & _).
  exact HK.
- subst e1. reflexivity.
Qed.
Lemma rgl_trK : forall cx i ly1 S1 W1 m1 e1 h1 LB ev,
  RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
  rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB ->
  rmtrK cx i = fst (keys_end_run (sl_live (rmc1 cx i ev) 1) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i)
    (map (fun x : list byte => (Z.of_nat (length x), drain_b_c.da_out drain_b_c.dadr0)) (gse_keys e1)) 0
    (drain_b_c.da_out drain_b_c.dadr0)).
Proof.
intros cx i ly1 S1 W1 m1 e1 h1 LB ev HB Hi Hfd HDR. unfold rmtrK, gse_keys.
rewrite (rgl_live_c1 cx i ev 1) by lia.
rewrite (rgl_keys_map (re_keys e1) (drain_b_c.ds_H (rms cx i)) _ (rgl_keys_rms cx i ly1 S1 W1 m1 e1 h1 LB HDR)).
destruct (sl_live (rxc cx) 1) eqn:L.
- destruct (rgl_match cx i ly1 S1 W1 m1 e1 h1 LB HB Hi Hfd HDR L) as [E1 E2]. rewrite E1, E2. reflexivity.
- apply relay_remove_b_aux.rma_ge_dead.
Qed.

(* ------------------------------------------------------------------ the footprints of the representation predicates
   lie in their header bytes or in their own blocks (the form of W_rr_tail.v rfz_alist / rfz_asrc / rfz_aentry, with
   the blocks named) *)
Definition rgl_in (bl : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Lemma rgl_in_blk : forall bl p n len a, In (p, n) bl -> 0 <= n -> len <= n -> p <= a < p + len -> rgl_in bl a.
Proof.
intros bl p n len a Hin Hn Hl Ha. exists p, n. split; [exact Hin|]. pose proof (req_size_pos n Hn) as [_ Hr]. lia.
Qed.
Lemma rgl_in_app_l : forall l1 l2 a, rgl_in l1 a -> rgl_in (l1 ++ l2) a.
Proof. intros l1 l2 a (p & n & H & Ha). exists p, n. split; [apply in_or_app; left; exact H | exact Ha]. Qed.
Lemma rgl_in_app_r : forall l1 l2 a, rgl_in l2 a -> rgl_in (l1 ++ l2) a.
Proof. intros l1 l2 a (p & n & H & Ha). exists p, n. split; [apply in_or_app; right; exact H | exact Ha]. Qed.
Lemma rgl_len_bzs : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rgl_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma rgl_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, rgl_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma rgl_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
Lemma rgl_fp_alist : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall r a, In r (alist_fp LA l) -> fst r <= a < snd r -> LA <= a < LA + 16 \/ rgl_in (alist_blks l) a.
Proof.
intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) r a Hr Ha.
rewrite Forall_forall in H9. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn in Ha; lia|]. right.
unfold alist_blks. apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
  destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
  destruct Hr as [<- | []]. cbn [gfp fst snd] in Ha. apply rgl_in_app_l.
  rewrite rgl_len_bzs, length_app, Nat2Z.inj_add, rgl_concat_len, Hj in Ha. unfold hl_n, AREC in *.
  apply (rgl_in_blk _ (hl_v l) (16 * hl_cap l) (16 * hl_cap l) a); [left; reflexivity | lia | lia | lia].
- apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha. apply rgl_in_app_r.
  destruct (H9 x Hx) as (K1 & _). rewrite rgl_len_bzs, length_app in Ha. cbn [length] in Ha.
  apply (rgl_in_blk _ (fst x) (Z.of_nat (length (snd x)) + 1) (Z.of_nat (length (snd x)) + 1) a); [|lia|lia|lia].
  apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx.
Qed.
Lemma rgl_fp_asrc : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
  forall r a, In r (asrc_fp HA h) -> fst r <= a < snd r -> HA <= a < HA + ASRC \/ rgl_in (asrc_blks h) a.
Proof.
intros ly S W mem HA h HS r a Hr Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                  _ & Hexp & Hheld & _).
unfold asrc_fp in Hr. unfold asrc_blks.
destruct Hr as [<- | [<- | Hr]].
- left. cbn in Ha. exact Ha.
- right. cbn [gfp fst snd] in Ha. rewrite rgl_len_bzs, Hpj in Ha.
  apply (rgl_in_blk _ (hs_partial h) APARTIAL APARTIAL a); [left; reflexivity | unfold APARTIAL; lia | lia | lia].
- apply in_app_or in Hr as [Hr | Hr].
  { destruct (rgl_fp_alist _ _ _ _ _ _ _ Hpend r a Hr Ha) as [H | H]; [left; unfold ASRC; lia|].
    right. destruct H as (p & n & Hin & Hpa). exists p, n. split; [right; apply in_or_app; left; exact Hin | exact Hpa]. }
  apply in_app_or in Hr as [Hr | Hr].
  { destruct (rgl_fp_alist _ _ _ _ _ _ _ Hexp r a Hr Ha) as [H | H]; [left; unfold ASRC; lia|].
    right. destruct H as (p & n & Hin & Hpa). exists p, n.
    split; [right; apply in_or_app; right; apply in_or_app; left; exact Hin | exact Hpa]. }
  destruct (rgl_fp_alist _ _ _ _ _ _ _ Hheld r a Hr Ha) as [H | H]; [left; unfold ASRC; lia|].
  right. destruct H as (p & n & Hin & Hpa). exists p, n.
  split; [right; apply in_or_app; right; apply in_or_app; right; exact Hin | exact Hpa].
Qed.
Lemma rgl_fp_aentry : forall ly S W mem e, aentry_ok B ly S W mem e ->
  forall r a, In r (aentry_fp e) -> fst r <= a < snd r -> rgl_in (aentry_blks e) a.
Proof.
intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) r a Hr Ha.
rewrite Forall_forall in K15. unfold aentry_fp in Hr. unfold aentry_blks.
apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|].
  destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
  destruct Hr as [<- | []]. cbn [gfp fst snd] in Ha. apply rgl_in_app_l.
  rewrite rgl_len_bzs, length_app, Nat2Z.inj_add, Hj, K7 in Ha.
  apply (rgl_in_blk _ (re_buf e) (re_cap e) (re_cap e) a); [left; reflexivity | lia | lia | lia].
- apply rgl_in_app_r. destruct Hr as [<- | Hr].
  + cbn [gfp fst snd] in Ha. rewrite rgl_len_bzs, rgl_key_ptrs_len in Ha.
    destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    { rewrite Hks in Ha. cbn [length] in Ha. lia. }
    unfold re_nheld in Hk1. apply rgl_in_app_l.
    assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz). rewrite Ez.
    apply (rgl_in_blk _ (re_hp e) (re_kh e) (Z.of_nat (8 * length (re_keys e))) a); [left; reflexivity | lia | lia | lia].
  + apply in_map_iff in Hr as (k & <- & Hk). cbn [gfp fst snd] in Ha. apply rgl_in_app_r.
    destruct (K15 k Hk) as (M1 & _). rewrite rgl_len_bzs, length_app in Ha. cbn [length] in Ha.
    apply (rgl_in_blk _ (key_addr k) (Z.of_nat (length (key_text k)) + 1) (Z.of_nat (length (key_text k)) + 1) a);
      [|lia|lia|lia].
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps (new): image
   bytes outside its G, its footprint, the allocator's statics and errno; and the bytes of blocks live before and
   after it outside its footprint; with their writability *)
Lemma rgl_keep_img : forall Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k a,
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc 0 [] STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k ->
  apres_kept B W1 m1 W2 m2 ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> fp_spares FP1 a -> ~ inG Gc a -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k a HJ HAK Hi Ho He Hq Hf Hg. split.
- eapply W_gestures_end.gse_keep_img_x; eassumption.
- intros Hw. pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & Hwle & _).
  assert (Ea : bv_unsigned (Z_to_bv 64 a) = a) by (pose proof (pa_img_range a Hi); rewrite unsigned_lit_small by lia; reflexivity).
  unfold arm in *. apply (writable_kept (w_H W2) m1 m2 a).
  + intros (_ & b & Hb). apply HAK; [exact Hi | exact Ho | exact He |].
    split; [apply hidden_not_img; rewrite Ea; exact Hi | exists b; exact Hb].
  + exact (writable_at_mrestrict_hsub SEGS (w_H W1) (w_H W2) m1 a Hwle Hw).
Qed.
Lemma rgl_keep_blk : forall Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a,
  gx_ok SEGS B Gc ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc 0 [] STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k ->
  ARx ly1 S1 Hp1 W1 m1 md1 ->
  In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> ~ inFP FP1 a ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a HGc HJ HAR1 Hin1 Hin2 Ha Hf.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_x; exact HJ).
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 Hin1) as (_ & Hp4096 & Hpceil & _).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia.
  rewrite (F2 p n (a - p) Hin1 Hin2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact Hf)).
  apply (aview_gagree SEGS Gc _ _ _ _ Hag). apply inGb_false.
  rewrite unsigned_lit_small by (pose proof (req_size_pos n) as Hq; lia).
  intros HGa. destruct (HGc _ HGa) as [Himg _].
  apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + (a - p)) HAR1 Hin1); [lia | exact Himg].
- intros _. destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpres a Ha)).
Qed.
(* a byte of a live block is in no other live block's footprint *)
Lemma rgl_notfp : forall ly S Hp W m md bl p n a, ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n -> (forall b, In b bl -> In b (ablocks B ly S) /\ b <> (p, n)) -> ~ inFP (ablocks_fp bl) a.
Proof.
intros ly S Hp W m md bl p n a HAR Hin Ha Hbl Hf. apply inFP_ablocks_fp_inv in Hf as (q & k & Hq & Hqa).
destruct (Hbl _ Hq) as [Hq1 Hne].
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W m md q k p n HAR Hq1 Hin Hne) as D. unfold zdisjoint in D.
cbn [fst snd] in D. lia.
Qed.
Lemma rgl_abk_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof. intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))]. Qed.

(* ---- " end\0" at the call: RLIVE's rom_view shows the image's read-only bytes (HEND5L). ---- *)
Lemma rgl_end5 : forall W mem, rom_view SEGS W mem -> garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5).
Proof.
intros W mem HR j Hj.
assert (Hj5 : (j < 5)%nat) by (unfold bzs in Hj; rewrite length_map in Hj; exact Hj).
destruct (HEND5L j Hj5) as (Hrom & Hseg).
pose proof (HR _ Hrom) as Hv. rewrite Hseg in Hv.
rewrite (nth_error_nth' END5 (Z_to_bv 8 0)) in Hv by (change (length END5) with 5%nat; exact Hj5).
cbn [option_map] in Hv.
assert (Enth : nth j (bzs END5) 0 = bv_unsigned (nth j END5 (Z_to_bv 8 0))).
{ unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth. reflexivity. }
rewrite <- Enth in Hv.
destruct (aview_byte SEGS (w_H W) mem _ _ Hv) as (b & Hb & Hbv & Hr).
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold arm. rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 8) with 256. change (2 ^ 8) with 256.
rewrite !Z.mod_mod by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ---- NoDup of a block list, by parts. ---- *)
Lemma rgl_nd_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x ND H1 H2. apply in_split in H1 as (p & q & ->). rewrite <- app_assoc in ND. cbn [app] in ND.
apply NoDup_remove_2 in ND. apply ND. apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.
Lemma rgl_perm_ge : forall (A G OB SR OU R : list (Z * Z)),
  Permutation ((A ++ G) ++ OB ++ SR ++ OU ++ R) (G ++ OU ++ A ++ OB ++ SR ++ R).
Proof.
intros A G OB SR OU R. rewrite <- app_assoc.
eapply perm_trans; [apply (Permutation_app_swap_app A G)|]. apply Permutation_app_head.
replace (A ++ OB ++ SR ++ OU ++ R) with ((A ++ OB ++ SR) ++ OU ++ R) by (rewrite <- !app_assoc; reflexivity).
replace (OU ++ A ++ OB ++ SR ++ R) with (OU ++ (A ++ OB ++ SR) ++ R) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_swap_app.
Qed.
Lemma rgl_aentry_blks : forall e, aentry_blks e = rmbuf e ++ gse_blks e.
Proof. intros e. reflexivity. Qed.
(* the table before slot i: 56 i bytes *)
Lemma rgl_pads : forall cx, RBASE B ARx MT RP MMAX RG cx ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx).
Proof.
intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
eapply Forall_impl; [|exact HF]. intros e (_ & _ & P1 & P2 & _). split; assumption.
Qed.
Lemma rgl_tpre_len : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i <= length (rxes cx))%nat ->
  Z.of_nat (length (rmTpre cx i)) = AENT * Z.of_nat i.
Proof.
intros cx i HB Hi. pose proof (rgl_pads cx HB) as HP.
rewrite <- (firstn_skipn i (rxes cx)) in HP. apply Forall_app in HP as [HP _].
unfold rmTpre. rewrite (W_rr_scan.rrs_concat_len _ HP), length_firstn. unfold AENT. lia.
Qed.
Lemma rgl_tpost_len : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat ->
  Z.of_nat (length (rmTpost cx i)) = AENT * (Z.of_nat (length (rxes cx)) - Z.of_nat i - 1).
Proof.
intros cx i HB Hi. pose proof (rgl_pads cx HB) as HP.
rewrite <- (firstn_skipn (S i) (rxes cx)) in HP. apply Forall_app in HP as [_ HP].
unfold rmTpost. rewrite (W_rr_scan.rrs_concat_len _ HP), length_skipn. unfold AENT. lia.
Qed.
(* g_s is none of send_line's cells G_SL (HRGP's pairs 1 / 6, 7, 8, 10, 12, 14) *)
(* HRGP's pair i / j, unfolded (W_rr_m_kit.v rr_pair, which is local to the kit's Section) *)
Ltac rgl_pair i j P :=
  pose proof (rr_zpw_nth _ i j HRGP) as P; specialize (P ltac:(cbn [length]; lia));
  cbn [nth] in P; unfold zdisj in P; cbn [fst snd] in P.
Lemma rgl_gs_nSL : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ inG (G_SL B RG) a.
Proof.
intros a Ha HGa. unfold G_SL, inG in HGa. rewrite !Exists_cons, Exists_nil in HGa. unfold in_zr in HGa.
cbn [fst snd] in HGa.
rgl_pair 1%nat 6%nat P1. rgl_pair 1%nat 7%nat P2. rgl_pair 1%nat 8%nat P3. rgl_pair 1%nat 10%nat P4.
rgl_pair 1%nat 12%nat P5. rgl_pair 1%nat 14%nat P6.
clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[]]]]]]]; lia.
Qed.
Lemma rgl_nSL : forall a, ~ inG (G_DR B RG) a -> ~ inG (G_SL B RG) a.
Proof. intros a H HS. apply H. unfold G_DR, inG in *. apply Exists_cons_tl. exact HS. Qed.
Lemma rgl_perm_gf : forall (OU A OB SR R : list (Z * Z)),
  Permutation (OU ++ A ++ OB ++ SR ++ R) (A ++ OB ++ SR ++ OU ++ R).
Proof.
intros OU A OB SR R.
replace (OU ++ A ++ OB ++ SR ++ R) with (OU ++ (A ++ OB ++ SR) ++ R) by (rewrite <- !app_assoc; reflexivity).
replace (A ++ OB ++ SR ++ OU ++ R) with ((A ++ OB ++ SR) ++ OU ++ R) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_swap_app.
Qed.
Lemma rgl_rmhd : forall cx i (regs1 regs2 : bvmap 5 word) F, RMHD RG cx i regs1 F ->
  (forall r, In r (25%bv :: RGE_KEPT) -> getr regs2 r = getr regs1 r) -> RMHD RG cx i regs2 F.
Proof.
intros cx i regs1 regs2 F HM HK. unfold RMHD, rregs_held, rregs_base, spZ in *.
rewrite !HK by (cbv; tauto). exact HM.
Qed.

(* ------------------------------------------------------------------ the room gestures_end asks (gse_spec's gse_room,
   C3's text: bb moves by each key's tr_net (ge_tr ..) less the key's freed |x| + 1), from RRG's rmbud *)
Lemma rgl_tm_f : forall {P : Type} n a (t : list (RelayRunT.rev P)), tr_max (RelayRunT.RFree n a :: t) = tr_max t.
Proof. reflexivity. Qed.
(* one gesture_end of the key run is ge_tr (the run's g_nout / g_capout are the controller's when it is live; the
   addresses play no part) *)
Lemma rgl_ge_tr : forall c mx no cap no' cap' XL j o, XL <> 0 -> (sl_live c 1 = true -> no = no' /\ cap = cap') ->
  tr_peak (ge_tr c mx no cap XL) = tr_peak (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no' cap' XL j o) /\
  tr_net (ge_tr c mx no cap XL) = tr_net (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no' cap' XL j o) /\
  tr_max (ge_tr c mx no cap XL) = tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no' cap' XL j o).
Proof.
intros c mx no cap no' cap' XL j o HX HL. unfold ge_tr. rewrite (rgl_live_nz c XL HX).
destruct (sl_live c 1) eqn:L.
- destruct (HL eq_refl) as [<- <-].
  lazymatch goal with |- tr_peak (gesture_end_b_c.gesture_end_tr ?lv ?m ?n ?cp ?x ?j0 ?o0) = _ /\ _ =>
    destruct (tr_sz_measures _ _ (gesture_end_tr_sz lv m n cp x j0 o0 j o)) as (E1 & E2 & E3 & _) end.
  split; [exact E1|]. split; [exact E2 | exact E3].
- split; [reflexivity|]. split; reflexivity.
Qed.
(* the key run's largest request and peak give gse_room *)
Lemma rgl_room : forall (xs : list (list byte)) (ka : RelayRunT.addr YO0i.sptr) bb c mx no cap no' cap' j o lv,
  lv = sl_live c 1 -> Forall (fun x : list byte => x <> []) xs ->
  (lv = true -> no = no' /\ cap = cap') ->
  tr_max (fst (keys_end_run lv mx no' cap' (map (fun x : list byte => (Z.of_nat (length x), ka)) xs) j o)) < MMAX ->
  bb + tr_peak (fst (keys_end_run lv mx no' cap' (map (fun x : list byte => (Z.of_nat (length x), ka)) xs) j o))
    <= LIVE_MAX ->
  gse_room MMAX bb c mx no cap xs.
Proof.
induction xs as [|x xs IH]; intros ka bb c mx no cap no' cap' j o lv Elv HX HL HM HA; [exact I|]. subst lv.
apply Forall_cons_iff in HX as [Hx HX].
assert (Hxl : Z.of_nat (length x) <> 0) by (destruct x as [|b x]; [congruence | cbn [length]; lia]).
cbn [map keys_end_run] in HM, HA. cbv zeta in HM, HA. cbn [fst] in HM, HA.
rewrite rm_tr_max_app, rgl_tm_f in HM. rewrite tr_peak_app, tr_peak_free in HA.
destruct (rgl_ge_tr c mx no cap no' cap' (Z.of_nat (length x)) j o Hxl HL) as (EP & EN & EM).
assert (Ege : sl_live (ge_ctl c (Z.of_nat (length x))) 1 = sl_live c 1) by (apply rgl_live_ge; lia).
cbn [gse_room]. split.
- unfold ge_room. rewrite EP, EM. lia.
- apply (IH ka (bb + tr_net (ge_tr c mx no cap (Z.of_nat (length x))) - (Z.of_nat (length x) + 1))
    (ge_ctl c (Z.of_nat (length x))) mx
    (ge_no c no (Z.of_nat (length x))) (ge_cap c mx no cap (Z.of_nat (length x))) (no' + Z.of_nat (length x) + 5)
    (gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no' cap' (Z.of_nat (length x)))
    (j + RelayRunT.nret YO0i.sptr (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no' cap' (Z.of_nat (length x)) j o))%nat
    (gesture_end_b_c.gesture_end_out (sl_live c 1) mx no' cap' (Z.of_nat (length x)) j o) (sl_live c 1)
    (eq_sym Ege) HX).
  + intros L. destruct (HL L) as [<- <-].
    assert (L1 : sl_live c (Z.of_nat (length x)) = true) by (rewrite (rgl_live_nz c _ Hxl); exact L).
    assert (L2 : sl_live (sl_ctl c (Z.of_nat (length x))) 5 = true) by (rewrite (rgl_live_ctl c _ 5) by lia; exact L1).
    unfold ge_no, ge_cap, sl_no, sl_cap, gesture_end_b_c.gesture_end_cap. rewrite L1, L2, L.
    split; [lia | reflexivity].
  + lia.
  + rewrite EN. lia.
Qed.
(* gse_spec's gse_room at the call, from RBASE and RRG's meter rmbud (W_contract.v's rr_tr key run, rgl_trK) *)
Lemma rgl_hgroom : forall cx i ly1 S1 W1 m1 e1 h1 ev LB spent,
  RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
  rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB -> aentry_ok B ly1 S1 W1 m1 e1 ->
  rmbud MT RP MMAX cx S1 spent (rmtrK cx i ++ rmtrF cx i) ->
  gse_room MMAX (blocks_bytes S1) (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1).
Proof.
intros cx i ly1 S1 W1 m1 e1 h1 ev LB spent HB Hi Hfd HDR HEO HBUD.
pose proof HBUD as (_ & _ & _ & BTM & BRM & _).
pose proof (tr_peak_prefix (rmtrK cx i) (rmtrF cx i)) as PP.
assert (BK : blocks_bytes S1 + tr_peak (rmtrK cx i) <= LIVE_MAX) by lia.
assert (BM : tr_max (rmtrK cx i) < MMAX) by (rewrite rm_tr_max_app in BTM; lia).
rewrite (rgl_trK cx i ly1 S1 W1 m1 e1 h1 LB ev HB Hi Hfd HDR) in BK, BM.
pose proof HEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EKS).
assert (HXS : Forall (fun x : list byte => x <> []) (gse_keys e1)).
{ unfold gse_keys. apply Forall_map. eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & Hk) Hn.
  rewrite Hn in Hk. cbn in Hk. lia. }
apply (rgl_room (gse_keys e1) (drain_b_c.da_out drain_b_c.dadr0) (blocks_bytes S1) (rmc1 cx i ev) (rxmx cx)
  (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) 0%nat
  (drain_b_c.da_out drain_b_c.dadr0) (sl_live (rmc1 cx i ev) 1) eq_refl HXS).
- intros _. split; reflexivity.
- exact BM.
- exact BK.
Qed.
(* the relay's cells g_s, g_src, g_nsrc, g_capsrc are HRGP's (rr_gcells), so off the program statics PST (PSTG) *)
Lemma rgl_gc : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
  rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ Exists (in_zr a) PST.
Proof.
intros a Ha. apply PSTG. unfold rr_gcells. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
- do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
- do 3 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
- do 4 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
Qed.
(* the room round's count after gestures_end (the step of commit 67327a6003d, W_gse_cut.v gse_cnt_at): the blocks
   lose gse_blks and the g_out block (at most one, aout_blks) is replaced, so a live P-count rises by at most one,
   under gse_pk's 4 *)
Lemma rgl_cnt_ge : forall TB (G : list (Z * Z)) cap out cap' out' R l l',
  Permutation l ((TB, ATABLE) :: G ++ aout_blks cap out ++ R) ->
  Permutation l' ((TB, ATABLE) :: aout_blks cap' out' ++ R) ->
  cnt_ok_pk RP gse_pk l -> cnt_ok RP l'.
Proof.
intros TB G cap out cap' out' R l l' H1 H2 HC. unfold cnt_ok.
apply (cnt_ok_pk_mono RP gse_pk _ l l'); [|exact HC].
intros P. rewrite (ReplyCnt.acnt_perm P _ _ H1), (ReplyCnt.acnt_perm P _ _ H2).
rewrite !acnt_cons, !ReplyCnt.acnt_app.
pose proof (W_gse_cut.gse_acnt_aout P cap' out'). unfold gse_pk. cbv beta. lia.
Qed.

Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].

(* ------------------------------------------------------------------ GE: RRG i 0x83f68 -> RRF i 0x83f74 *)
Theorem rr_m_ge : @hop_ge_stmt fx rc SK PI B PST ARx MT RP MMAX RG.
Proof.
unfold hop_ge_stmt. intros cx i W1 c1 HB HRG K.
destruct HRG as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & e1 & h1 & ev & LB & out1 & spent &
  -> & HMD & HLV & HDR & HEO & HTB & HOUT & HPM & HGS & HBUD & HCNT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMD as (HRH & H25 & H24 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp & H3 & H4 & H8 & H9 & H18 & H20 & H21 & H22 & H26 & H27) & H19 & H23).
pose proof HLV as (fpos & HJ & HROM & HAPK & HFR & HLK & HWK).
pose proof HTB as (TSv & TSw & TNv & TNw & TCv & TCw & TIn & TLen & (tail & Ttl & Tg) & TSA & TOK).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HP16 & HP4096 & HPceil & _).
change (req_size ATABLE) with 896 in HPceil.
pose proof HB as (HPRE & H32 & _ & HRGPL & _).
pose proof HRGPL as (Elock & Ensrc & Esrc & _).
assert (HN : Z.of_nat (length (rxes cx)) <= 16) by (unfold rN, AENT, ATABLE in Ttl; lia).
(* the seat at 0x83f68 *)
remember (Eimg (Ereg regs1 (rge_extra (rxG0 cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rge_extra (rxG0 cx))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E24 : ew E 24 = getr regs1 24)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 24 24%bv eq_refl)).
pose proof (pa_obj_img 8 ltac:(lia)) as HO8.
assert (HS : st_ok_pi SEGS VAL E ss_rge (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_ge)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rge. apply pa_entry_st_ok_full.
- unfold rge_sr. apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H25. apply bv_eq. fold (U E (SOff (A_HI 60) 0)). rewrite (U_img_atom E HEI (A_HI 60)) by (cbv; lia).
  rewrite HH60. unfold w64. rewrite unsigned_lit_small by (unfold RR_HI_SRC; lia). reflexivity.
- vm_compute. reflexivity.
- unfold rge_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite (HEI (A_OBJ 8)) by (cbv; lia). rewrite <- Esrc.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) (rxG0 cx));
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact TSv.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
  + cbn [rge_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by lia. change (2 ^ 4) with 16. unfold RGE_PHI.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rge_facts f_alias alias_ok]. exact I. }
assert (SHOK : sh_ok SEGS RGE_BX rge_SH E (mrestrict (w_H W1) m1)) by (unfold sh_ok, rge_SH; constructor).
clear HE.
unfold cfg_at. change (w64 (BASE + A_rr_ge)) with (Z_to_bv 64 (BASE + A_rr_ge)).
(* ld a0, g_src; add a0, a0, s8; jal gestures_end: to the callee's entry *)
paj_run_to_tok_x RUNTO HS HJ SHOK rge_Bspan AF_fr_gestures_end.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rge_mem Em1.
pmkst HS.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (25%bv : bv 5) R25.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RGE_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK end.
cbn [ms_regs restrict] in HK.
rewrite Em1 in HJ |- *.
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25).
{ change (ew E 340) with (ew E (A_HI 60)) in R25. apply bv_eq. rewrite R25, (HEI (A_HI 60)) by (cbv; lia).
  rewrite H25, HH60. unfold w64. rewrite unsigned_lit_small by (unfold RR_HI_SRC; lia). reflexivity. }
assert (KR : forall r, In r (25%bv :: RGE_KEPT) -> getr (ms_regs ms) r = getr regs1 r)
by (intros r [<- | Hr]; [exact R25' | exact (HK r Hr)]).
clear HK R25 R25'.
(* the call's registers *)
assert (Rsa : getr (ms_regs ms) 10 = w64 (rmSA cx i)).
{ rewrite R10, E24, H24, E32. unfold w64. rewrite YI08.alu64_add_lit. unfold rmSA. f_equal. lia. }
(* the facts at the cut *)
destruct (W_gesture_end.aout_facts B RG ly1 S1 W1 m1 _ _ _ _ _ _ HOUT) as (Hmx & HnoO & Hblk).
pose proof (W_gestures_end.gse_nodup_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 HAR) as ND. apply (Permutation_NoDup HPM) in ND.
destruct (rr_call_chain B PST ARx MT RP MMAX RG HG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HLV) as (ch1 & Hch1).
pose proof HEO as (_ & _ & EP1 & EP2 & _ & _ & _ & _ & _ & EBUF & ENH & EHP & ENDA & ENDT & EKS).
pose proof HPRE as (_ & _ & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSA0 : rxG0 cx <= rmSA cx i /\ rmSA cx i + AENT <= rxG0 cx + ATABLE) by (unfold rmSA, AENT, ATABLE; lia).
assert (HSA8 : rmSA cx i mod 8 = 0).
{ unfold rmSA, AENT. pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D. rewrite D.
  replace (16 * (rxG0 cx / 16) + 56 * Z.of_nat i) with ((2 * (rxG0 cx / 16) + 7 * Z.of_nat i) * 8) by ring.
  apply Z_mod_mult. }
assert (HSL : garr8 SEGS (arm W1 m1) (rmSA cx i) (bzs (entry_bytes e1))).
{ unfold bzs in Tg. rewrite !map_app in Tg. apply garr8_app in Tg as [_ Tg]. apply garr8_app in Tg as [Tg _].
  rewrite length_map, (rgl_tpre_len cx i HB ltac:(lia)) in Tg. unfold rmSA. exact Tg. }
assert (HHELD : aheld_ok B ly1 S1 W1 m1 e1) by exact (conj EP1 (conj EP2 (conj ENH (conj EHP (conj ENDA (conj ENDT EKS)))))).
assert (HPG : Permutation (ablocks B ly1 S1) ((rxG0 cx, ATABLE) :: gse_blks e1 ++ aout_blks (rmcap1 cx i) out1 ++
                (rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx))).
{ eapply perm_trans; [exact HPM|]. apply perm_skip. rewrite rgl_aentry_blks. apply rgl_perm_ge. }
pose proof (rgl_end5 W1 m1 HROM) as HE5.
assert (HXS : Forall (fun x : list byte => x <> []) (gse_keys e1)).
{ unfold gse_keys. apply Forall_map. eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & Hk) Hn.
  rewrite Hn in Hk. cbn in Hk. lia. }
assert (HRM : gse_room MMAX (blocks_bytes S1) (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i)
                (gse_keys e1))
by exact (rgl_hgroom cx i ly1 S1 W1 m1 e1 h1 ev LB spent HB Hi Hfd HDR HEO HBUD).
assert (ECOST : gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1) =
                tr_cost MT (rmtrK cx i) + mo_free MT).
{ rewrite (rgl_trK cx i ly1 S1 W1 m1 e1 h1 LB ev HB Hi Hfd HDR).
  apply (rgl_cost_lv MT (gse_keys e1) (drain_b_c.da_out drain_b_c.dadr0) (rmc1 cx i ev) (rxmx cx) _ _ _ _ 0%nat
    (drain_b_c.da_out drain_b_c.dadr0) (sl_live (rmc1 cx i ev) 1) eq_refl HXS). intros _. split; reflexivity. }
pose proof (mo_free_nonneg MT MLAW) as MF.
assert (TFc : tr_cost MT (rmtrF cx i) = mo_free MT + mo_free MT) by (unfold rmtrF, tr_cost; cbn [fold_right]; lia).
assert (HMOK : mo_ok MT S1 (gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i)
                 (gse_keys e1))).
{ pose proof HBUD as (BLE & B0 & BC & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BMOK & _).
  rewrite rm_tr_cost_app in BC. rewrite ECOST.
  apply (mo_ok_step MT MLAW (rxS cx) S1 spent _); [|exact BLE].
  apply (mo_ok_le MT MLAW (rxS cx) _ _ BMOK). lia. }
(* the room round: gestures_end's room at the counting meter, kr := 1 + kr of the entry (the buf free's 1 is left),
   from rmbud's room for the rest (the key run, then two frees) *)
assert (ECOSTrk : gse_cost MT_rk (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1) =
                  tr_cost MT_rk (rmtrK cx i) + mo_free MT_rk).
{ rewrite (rgl_trK cx i ly1 S1 W1 m1 e1 h1 LB ev HB Hi Hfd HDR).
  apply (rgl_cost_lv MT_rk (gse_keys e1) (drain_b_c.da_out drain_b_c.dadr0) (rmc1 cx i ev) (rxmx cx) _ _ _ _ 0%nat
    (drain_b_c.da_out drain_b_c.dadr0) (sl_live (rmc1 cx i ev) 1) eq_refl HXS). intros _. split; reflexivity. }
assert (HRMg : rp_RM RP S1 (Z.to_nat (gse_cost MT_rk (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB)))
                 (rmcap1 cx i) (gse_keys e1)) + (1 + rxkr cx))).
{ pose proof HBUD as (_ & _ & _ & _ & _ & HRMb).
  pose proof (rgl_rk_nonneg (rmtrK cx i)) as TK0.
  assert (TFrk : tr_cost MT_rk (rmtrF cx i) = 2) by (unfold rmtrF, tr_cost; reflexivity).
  rewrite rm_tr_cost_app_m, TFrk in HRMb.
  refine (RMM_of RP S1 _ _ _ HRMb). rewrite ECOSTrk. change (mo_free MT_rk) with 1. lia. }
assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => remember mdx as mdc eqn:Hmdc end.
(* the call: gestures_end (&g_src[i]) through GSE, its journal lifted to G_RR *)
eapply SRr_bind.
{ eapply (W_gestures_end.gse_callS_x B PST ARx LAWS (G_RR B RG) W1 (ms_regs ms) m1 _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx)
    (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 mdc k1 GSE_STK
    ((rmSA cx i + 40, rmSA cx i + 52) :: ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) (-96)
    (Z_to_bv 64 (BASE + 7304)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => exists Hq k2 out2,
      ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) 0 [] GSE_STK (spZ (ms_regs ms))
        ((rmSA cx i + 40, rmSA cx i + 52) :: ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1))
        ly1 S1 Hp1 W1 m1 mdc [] ly2 S2 Hq W2 mem2 md2 k2 /\
      apres_kept B W1 m1 W2 mem2 /\
      mo_le MT S1 S2 (gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)) /\
      rp_RM RP S2 (1 + rxkr cx) /\
      Permutation (ablocks B ly2 S2) ((rxG0 cx, ATABLE) ::
        aout_blks (gse_cap (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB)))
                             (rmcap1 cx i) (gse_keys e1))) out2 ++
        (rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx)) /\
      aout_at B RG ly2 S2 W2 mem2
        (gse_c (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        (gse_O (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        (rxmx cx)
        (gse_no (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        (gse_cap (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        out2 /\
      garr8 SEGS (arm W2 mem2) (rmSA cx i) (bzs (entry_bytes (entry_cleared e1))) /\ awr W2 mem2 (rmSA cx i) AENT)
    HG HJ).
  - unfold spZ. rewrite (KR 2%bv) by (cbv; tauto). fold (spZ regs1). rewrite Hsp. unfold RR_FRAME. lia.
  - reflexivity.
  - lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - rewrite (KR 3%bv) by (cbv; tauto). rewrite H3. exact Hgp.
  - rewrite (KR 4%bv) by (cbv; tauto). rewrite H4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof pa_B_ok as HBO. pose proof pa_base_lo as HBL. rewrite unsigned_lit_small by lia. lia.
  - replace (rsp0 cx + -96) with (rsp0 cx - RR_FRAME) by (unfold RR_FRAME; lia).
    unfold s0Z. rewrite (KR 8%bv) by (cbv; tauto). rewrite H8. unfold w64.
    rewrite unsigned_lit_small by (unfold rsp0 in *; lia). exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { exact (GSE W1 ly1 S1 Hp1 (ms_regs ms) m1 mdc ch1 (rmSA cx i) (rxG0 cx) e1 (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx)
        (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) out1 (rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx)
        HPRE1 Rsa TIn (proj1 HSA0) (proj2 HSA0) HSA8 HSL TSA HHELD HOUT HPG HE5 HROM HRM HMOK (1 + rxkr cx)%nat HRMg HCNT). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & out2 & -> & HJ2 & HP2 & HAK2 & HM2 & HRM2 & HPm2 &
      HO2 & HSL2 & HSA2).
    exists ly2, S2, Hp2, regs2, mem2, md2, k2. split; [rewrite R1; reflexivity|].
    split; [eapply rr_lift_SL; exact HJ2|]. split; [exact HP2|].
    exists Hp2, k2, out2. split; [exact HJ2|]. split; [exact HAK2|]. split; [exact HM2|]. split; [exact HRM2|].
    split; [exact HPm2|]. split; [exact HO2|]. split; [exact HSL2 | exact HSA2].
  - intros a (r & Hr & Hra). destruct Hr as [<- | Hr].
    + cbn [fst snd] in Hra. left. split.
      * unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
        apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE);
          [left; reflexivity | change (req_size ATABLE) with 896; unfold rmSA, AENT in *; lia].
      * exists (rxG0 cx), ATABLE. split; [exact TIn | change (req_size ATABLE) with 896; unfold rmSA, AENT in *; lia].
    + assert (Ha' : inFP (ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) a) by (exists r; split; assumption).
      apply inFP_ablocks_fp_inv in Ha' as (p & n & Hpn & Hpa).
      assert (Hpn' : In (p, n) ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++
                                 aout_blks (rmcap1 cx i) out1)).
      { right. rewrite rgl_aentry_blks. apply in_app_or in Hpn as [Hpn | Hpn].
        - apply in_or_app. left. apply in_or_app. right. exact Hpn.
        - apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
      assert (Hin1 : In (p, n) (ablocks B ly1 S1)).
      { apply (Permutation_in _ (Permutation_sym HPM)). destruct Hpn' as [E0 | Hpn']; [left; exact E0|].
        right. rewrite !app_assoc. apply in_or_app. left. rewrite <- !app_assoc. exact Hpn'. }
      destruct (in_dec DEC (p, n) (ablocks B (rxly cx) (rxS cx))) as [IN0 | NIN0].
      * left. split; [|exists p, n; split; [exact Hin1 | exact Hpa]].
        pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BPM & _).
        apply (Permutation_in _ BPM) in IN0. unfold rFP, rr_fp. replace a with (p + (a - p)) by lia.
        apply (inFP_ablocks_fp _ p n); [|lia].
        destruct IN0 as [E0 | IN0]; [left; exact E0|]. right.
        assert (IN1 : In (p, n) ((concat (map aentry_blks (rxes cx)) ++
                     (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx))
                     ++ rxrest cx)) by (rewrite <- !app_assoc; exact IN0).
        apply in_app_or in IN1 as [IN1 | IN1]; [exact IN1|]. exfalso.
        apply (rgl_nd_app ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++
                 aout_blks (rmcap1 cx i) out1) (rxrest cx) (p, n)); [|exact Hpn' | exact IN1].
        replace (((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ aout_blks (rmcap1 cx i) out1) ++
                 rxrest cx) with ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++
                 aout_blks (rmcap1 cx i) out1 ++ rxrest cx) by (cbn [app]; rewrite <- !app_assoc; reflexivity).
        exact ND.
      * right. exists p, n. split; [exact Hin1|]. split; [exact NIN0 | exact Hpa]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJ2 & HJc2 & HP2 &
  (Hq & k2 & out2 & HJs & HAK2 & HM2 & HRM2 & HPm2 & HO2 & HSL2 & HSA2)).
(* no ARx state has a hidden head (HP0): the callee's and the caller's head sets after the call are both [] *)
assert (EHq : Hq = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJs).
assert (EHp2 : Hp2 = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJ2).
subst Hq Hp2.
(* ---- back at 0x83f74: what gestures_end kept ---- *)
set (FP1 := (rmSA cx i + 40, rmSA cx i + 52) :: ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) in *.
set (RESTX := rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx) in *.
assert (Usp : spZ (ms_regs ms) = rsp0 cx - RR_FRAME)
by (unfold spZ; rewrite (KR 2%bv) by (cbv; tauto); fold (spZ regs1); exact Hsp).
rewrite Usp in HJs.
assert (HGSL : gx_ok SEGS B (G_SL B RG)) by exact (gx_ok_sub SEGS B _ _ (rr_G_SL_RR B RG) HG).
assert (GA1 : forall b, In b (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPG)). right. rewrite app_assoc. apply in_or_app. left. exact Hb. }
assert (ND' : List.NoDup ((rxG0 cx, ATABLE) :: gse_blks e1 ++ aout_blks (rmcap1 cx i) out1 ++ RESTX))
by (apply (Permutation_NoDup HPG); exact (W_gestures_end.gse_nodup_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 HAR)).
pose proof (proj1 (NoDup_cons_iff _ _) ND') as (TNG & ND2). rewrite app_assoc in TNG, ND2.
assert (FPB : forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
{ intros a (r & Hr & Hra). destruct Hr as [<- | Hr].
  - exists (rxG0 cx), ATABLE. split; [exact TIn|]. change (req_size ATABLE) with 896. cbn [fst snd] in Hra.
    unfold rmSA, AENT in *. lia.
  - assert (Ha' : inFP (ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) a) by (exists r; split; assumption).
    apply inFP_ablocks_fp_inv in Ha' as (p & n & Hpn & Hpa). exists p, n. split; [exact (GA1 _ Hpn) | exact Hpa]. }
assert (HFP0 : Forall (fun r => 0 < fst r) FP1).
{ unfold FP1. constructor; [cbn [fst]; unfold rmSA, AENT in *; lia|].
  apply Forall_forall. intros r Hr. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR (GA1 _ Hpn)) as (_ & Hp & _). lia. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> abyte_kept W1 m1 W2 mem2 a).
{ intros a I1 I2 I3 I4 I5. apply (rgl_keep_img (G_SL B RG) GSE_STK (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 mdc ly2 S2 []
    W2 mem2 md2 k2 a HJs HAK2 I1 I2 I3 I4); [|exact I5].
  apply fp_spares_closed. apply sink_closed_pos. exact HFP0. }
assert (HARc : ARx ly1 S1 Hp1 W1 m1 mdc) by (eapply ajournal_gx_AR_x; exact HJ).
assert (KREST : forall p n a, In (p, n) RESTX -> p <= a < p + req_size n -> abyte_kept W1 m1 W2 mem2 a).
{ intros p n a Hp Ha.
  assert (I1 : In (p, n) (ablocks B ly1 S1)).
  { apply (Permutation_in _ (Permutation_sym HPG)). right. apply in_or_app. right. apply in_or_app. right. exact Hp. }
  assert (I2 : In (p, n) (ablocks B ly2 S2)).
  { apply (Permutation_in _ (Permutation_sym HPm2)). right. apply in_or_app. right. exact Hp. }
  apply (rgl_keep_blk (G_SL B RG) GSE_STK (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 mdc ly2 S2 [] W2 mem2 md2 k2 p n a
    HGSL HJs HARc I1 I2 Ha).
  intros (r & Hr & Hra). destruct Hr as [<- | Hr].
  - assert (Hne : (rxG0 cx, ATABLE) <> (p, n)).
    { intros Eq. apply TNG. apply in_or_app. right. rewrite Eq. exact Hp. }
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE p n HAR TIn I1 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D, Hra. change (req_size ATABLE) with 896 in D.
    unfold rmSA, AENT in *. lia.
  - assert (Hbl : forall b, In b (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1) -> In b (ablocks B ly1 S1) /\ b <> (p, n)).
    { intros b Hb. split; [exact (GA1 _ Hb)|]. intros ->. exact (rgl_nd_app _ _ (p, n) ND2 Hb Hp). }
    exact (rgl_notfp ly1 S1 Hp1 W1 m1 md1 _ p n a HAR I1 Ha Hbl (ex_intro _ r (conj Hr Hra))). }
assert (KTAB : forall a, rxG0 cx <= a < rxG0 cx + ATABLE -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
  abyte_kept W1 m1 W2 mem2 a).
{ intros a Ha Hs.
  assert (T2 : In (rxG0 cx, ATABLE) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPm2)); left; reflexivity).
  assert (Har : rxG0 cx <= a < rxG0 cx + req_size ATABLE) by (change (req_size ATABLE) with 896; unfold ATABLE in Ha; lia).
  apply (rgl_keep_blk (G_SL B RG) GSE_STK (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 mdc ly2 S2 [] W2 mem2 md2 k2 (rxG0 cx)
    ATABLE a
    HGSL HJs HARc TIn T2 Har).
  intros (r & Hr & Hra). destruct Hr as [<- | Hr].
  - cbn [fst snd] in Hra. unfold AENT in Hs. lia.
  - assert (Hbl : forall b, In b (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1) ->
                  In b (ablocks B ly1 S1) /\ b <> (rxG0 cx, ATABLE)).
    { intros b Hb. split; [exact (GA1 _ Hb)|]. intros ->. apply TNG. apply in_or_app. left. exact Hb. }
    exact (rgl_notfp ly1 S1 Hp1 W1 m1 md1 _ (rxG0 cx) ATABLE a HAR TIn Har Hbl (ex_intro _ r (conj Hr Hra))). }
pose proof HRGPL as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HBUD as (BLE & B0 & BC & _). rewrite rm_tr_cost_app in BC.
apply K. unfold RRF.
exists regs2, ly2, S2, (@nil Z), mem2, md2, (k1 + kk), F, FL, e1, h1, ev, LB,
  (gse_c (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1))),
  (gse_O (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1))),
  (gse_cap (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1))),
  out2, (spent + gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)).
split; [unfold cfg_at; reflexivity|].
split.
{ apply (rgl_rmhd cx i regs1 regs2 F HMD). intros r Hr. rewrite <- (KR r Hr). rewrite <- (Z_to_bv_bv_unsigned _ r).
  apply HP2. cbn [In RGE_KEPT] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [match goal with |- acallee_saved (bv_unsigned ?b) => let v := eval vm_compute in (bv_unsigned b) in
       change (bv_unsigned b) with v end; unfold acallee_saved; lia|]).
  destruct Hr. }
split.
{ apply (rr_live_call B PST ARx MT RP MMAX RG LAWS HRGP HROMO PSTR PSTG cx F FL fpos ly1 S1 Hp1 W1 m1 mdc k1 (G_SL B RG)
    GSE_STK FP1 ly2 S2 [] W2 mem2 md2 k2 (k1 + kk) HB HJ HROM HAPK HFR HLK HWK HGSL);
    [| | exact HJs | exact HFP0 | exact FPB | exact HAK2 |
    exact HJ2].
  - intros a Ha. unfold G_DR, inG in *. apply Exists_cons_tl. exact Ha.
  - split; apply Z.leb_le; vm_compute; reflexivity. }
split.
{ pose proof HDR as HDR'. unfold rmdrel in HDR' |- *. destruct (rmopen cx i) eqn:Eo; [|exact HDR'].
  destruct HDR' as (HDR' & HAS). split; [exact HDR'|].
  assert (Ho : re_eof (rnth cx i) = 0) by (unfold rmopen in Eo; apply Z.eqb_eq; exact Eo).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDS & _). destruct (HDS i Hi Hfd Ho) as (Hj4 & _).
  assert (INS : forall b, In b (asrc_blks h1) -> In b RESTX).
  { intros b Hb. unfold RESTX, rmsrc. rewrite Eo. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 mem2 (rmHA RG cx) h1 HAS).
  - intros r Hr a Ha. destruct (rgl_fp_asrc ly1 S1 W1 m1 _ h1 HAS r a Hr Ha) as [Hg | (p & n & Hpn & Hpa)].
    + assert (Hgs : rg_s RG <= a < rg_s RG + 4 * ASRC) by (unfold rmHA, ASRC in *; lia).
      destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (I1 & I2 & I3).
      exact (KIMG a I1 I2 I3 (rgl_gc a (or_introl Hgs)) (rgl_gs_nSL a Hgs)).
    + exact (KREST p n a (INS _ Hpn) Hpa).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPm2)). right. apply in_or_app. right. exact (INS _ Hb). }
split; [exact EP1|]. split; [exact EP2|].
split; [destruct EBUF as [(Hc & Hb & _) | (Hc & _)]; [left; split; assumption | right; exact Hc]|].
split.
{ assert (KC : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
                         rg_capsrc RG <= a < rg_capsrc RG + 4 -> abyte_kept W1 m1 W2 mem2 a).
  { intros a Ha.
    assert (HI : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
    { destruct Ha as [Ha | [Ha | Ha]].
      - apply RGIMG. unfold rg_rng. tauto.
      - apply RGIMG. unfold rg_rng. tauto.
      - destruct (HRGI a ltac:(tauto)) as [I1 I2]. split; [exact I1|]. split; [exact I2|].
        eapply rr_capsrc_nerr; [exact HRGP | exact Ha]. }
    destruct HI as (I1 & I2 & I3). apply (KIMG a I1 I2 I3); [apply rgl_gc; tauto|].
    apply rgl_nSL. eapply rr_nG_DR; [exact HRGP|]. tauto. }
  unfold rmtbl.
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; left; cbn in Hx; lia | exact TSv]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; left; lia | exact TSw]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; right; left; cbn in Hx; lia | exact TNv]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; right; left; lia | exact TNw]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; right; right; cbn in Hx; lia | exact TCv]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; right; right; lia | exact TCw]|].
  split; [apply (Permutation_in _ (Permutation_sym HPm2)); left; reflexivity|].
  pose proof (W_rr_scan.rrs_eb_len e1 EP1 EP2) as LE1.
  pose proof (W_rr_scan.rrs_eb_len (entry_cleared e1) EP1 EP2) as LE2.
  pose proof (rgl_tpre_len cx i HB ltac:(lia)) as LPRE. pose proof (rgl_tpost_len cx i HB Hi) as LPOST.
  split; [rewrite LE2; reflexivity|].
  split.
  { exists tail. split; [exact Ttl|].
    unfold bzs in Tg, HSL2 |- *. rewrite !map_app in Tg |- *.
    apply garr8_app in Tg as [TgA Tg]. apply garr8_app in Tg as [_ TgB].
    rewrite !length_map, LPRE, LE1 in TgB.
    apply garr8_app. split.
    - apply (akept_garr8 W1 m1); [|exact TgA]. intros x Hx. rewrite length_map, LPRE in Hx.
      apply KTAB; unfold rmSA, AENT, ATABLE in *; lia.
    - rewrite length_map, LPRE. apply garr8_app. split.
      + unfold rmSA in HSL2. exact HSL2.
      + rewrite length_map, LE2. apply (akept_garr8 W1 m1); [|exact TgB]. intros x Hx.
        rewrite length_app, !length_map, Nat2Z.inj_add, LPOST, Ttl in Hx. unfold rN in Hx.
        apply KTAB; unfold rmSA, AENT, ATABLE in *; lia. }
  split; [exact HSA2|].
  rewrite Forall_forall in TOK |- *. intros e He.
  assert (INE : forall b, In b (aentry_blks e) -> In b RESTX).
  { intros b Hb. unfold RESTX. apply in_or_app. right. apply in_or_app. left. unfold rmOB. apply in_concat.
    exists (aentry_blks e). split; [apply in_map; exact He | exact Hb]. }
  apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 mem2 e (TOK e He)).
  - intros r Hr a Ha. destruct (rgl_fp_aentry _ _ _ _ e (TOK e He) r a Hr Ha) as (p & n & Hpn & Hpa).
    exact (KREST p n a (INE _ Hpn) Hpa).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPm2)). right. apply in_or_app. right. exact (INE _ Hb). }
split; [unfold gse_keys; rewrite rgl_sends; reflexivity|].
split; [destruct (W_gesture_end.aout_facts B RG ly2 S2 W2 mem2 _ _ _ _ _ _ HO2) as (_ & HnoO2 & _); rewrite HnoO2; exact HO2|].
split; [eapply perm_trans; [exact HPm2|]; apply perm_skip; unfold RESTX; apply rgl_perm_gf|].
split.
{ intros a Ha Hd. apply (rgl_abk_trans (rxW cx) W1 W2 (rxmem cx) m1 mem2 a (HGS a Ha Hd)).
  destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (I1 & I2 & I3).
  exact (KIMG a I1 I2 I3 (rgl_gc a (or_introl Ha)) (rgl_gs_nSL a Ha)). }
split; [exact (mo_le_trans MT MLAW (rxS cx) S1 S2 spent _ BLE HM2)|].
split; [rewrite ECOST; lia|].
(* the room round: gestures_end's post leaves the buf free's 1, then kr; the free's count premise from RRG's gse_pk *)
split; [exact HRM2|].
exact (rgl_cnt_ge (rxG0 cx) (gse_blks e1) (rmcap1 cx i) out1 _ out2 RESTX _ _ HPG HPm2 HCNT).
Qed.

(* ---- route R (a Theorem Labs lane crew, G8-A; a Theorem Labs lane): hop GE at a world relation R, over a Theorem Labs lane 1's
   W_rr_match_cx.v Section wR (hop_ge_stmt_xR, RRG_xR / RRF_xR).  The copied strict proof runs in SRr mode between
   calls (SRr_to_G) over the R journal, makes the gestures_end call in SRrG mode (W_gestures_end.gse_callS_xR with
   GSE_R, gestures_end's contract at R) and returns to the continuation; the changed lines are listed in
   a Theorem Labs lane's routeR/g8/mkge.py. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* gestures_end at R (W_contract_xR.v gse_spec_xR); hop_ge_stmt_xR is over the strict GSE, so this file alone takes it *)
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
Let RUNTOR := paj_run_to_x_xR B PST ARx LAWS R (G_RR B RG) HG 0 [].
(* an SRr walk to a point where the SRrG goal holds is that SRrG goal *)
Lemma SRr_to_G : forall W c (Q : world SEGS -> config -> Prop),
  SRr SEGS W c (fun W' c' => YA0nH.SRrG SEGS R W' c' Q) -> YA0nH.SRrG SEGS R W c Q.
Proof.
intros W c Q H. eapply (YA0nH.SRrG_bind SEGS R R_trans); [apply (YA0nH.SRr_SRrG SEGS R WLE_R); exact H|].
intros W' c' _ HQ. exact HQ.
Qed.
(* the R law of the image (a Theorem Labs lane 00:40Z, exact text): R adds no hidden byte inside the image *)
Hypothesis R_IMG : forall (W W' : world SEGS) (a : word), R W W' -> in_img SEGS (bv_unsigned a) -> w_H W' a = true -> w_H W a = true.
(* writability at one byte needs the hidden sets to agree only there *)
Lemma writable_at_hid_pt : forall (H H' : word -> bool) (m : word -> option byte) a,
  (H' (Z_to_bv 64 a) = true -> H (Z_to_bv 64 a) = true) ->
  writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H' m) a.
Proof.
intros H H' m a Hs Hw. unfold writable_at, wview, mrestrict in *.
destruct (H' (Z_to_bv 64 a)) eqn:E'.
- rewrite (Hs eq_refl) in Hw. exact Hw.
- destruct (H (Z_to_bv 64 a)); [|exact Hw]. destruct (m (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* rgl_keep_img / rgl_keep_blk over the R journal; the image byte's writability by R_IMG *)
Lemma rgl_keep_img_xR : forall Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k a,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc 0 [] STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k ->
  apres_kept B W1 m1 W2 m2 ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> fp_spares FP1 a -> ~ inG Gc a -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k a HJ HAK Hi Ho He Hq Hf Hg. split.
- eapply W_gestures_end.gse_keep_img_xR; eassumption.
- intros Hw. pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & Hwle & _).
  assert (Ea : bv_unsigned (Z_to_bv 64 a) = a) by (pose proof (pa_img_range a Hi); rewrite unsigned_lit_small by lia; reflexivity).
  unfold arm in *. apply (writable_kept (w_H W2) m1 m2 a).
  + intros (_ & b & Hb). apply HAK; [exact Hi | exact Ho | exact He |].
    split; [apply hidden_not_img; rewrite Ea; exact Hi | exists b; exact Hb].
  + exact (writable_at_hid_pt (w_H W1) (w_H W2) m1 a (R_IMG W1 W2 (Z_to_bv 64 a) Hwle ltac:(rewrite Ea; exact Hi)) Hw).
Qed.
Lemma rgl_keep_blk_xR : forall Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a,
  gx_ok SEGS B Gc ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc 0 [] STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k ->
  ARx ly1 S1 Hp1 W1 m1 md1 ->
  In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> ~ inFP FP1 a ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a HGc HJ HAR1 Hin1 Hin2 Ha Hf.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 Hin1) as (_ & Hp4096 & Hpceil & _).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia.
  rewrite (F2 p n (a - p) Hin1 Hin2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact Hf)).
  apply (aview_gagree SEGS Gc _ _ _ _ Hag). apply inGb_false.
  rewrite unsigned_lit_small by (pose proof (req_size_pos n) as Hq; lia).
  intros HGa. destruct (HGc _ HGa) as [Himg _].
  apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + (a - p)) HAR1 Hin1); [lia | exact Himg].
- intros _. destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpres a Ha)).
Qed.
Theorem rr_m_ge_xR : hop_ge_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold hop_ge_stmt_xR. intros cx i W1 c1 HB HRG K. apply SRr_to_G.
destruct HRG as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & e1 & h1 & ev & LB & out1 & spent &
  -> & HMD & HLV & HDR & HEO & HTB & HOUT & HPM & HGS & HBUD & HCNT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMD as (HRH & H25 & H24 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp & H3 & H4 & H8 & H9 & H18 & H20 & H21 & H22 & H26 & H27) & H19 & H23).
pose proof HLV as (fpos & HJ & HROM & HAPK & HFR & HLK & HWK).
pose proof HTB as (TSv & TSw & TNv & TNw & TCv & TCw & TIn & TLen & (tail & Ttl & Tg) & TSA & TOK).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HP16 & HP4096 & HPceil & _).
change (req_size ATABLE) with 896 in HPceil.
pose proof HB as (HPRE & H32 & _ & HRGPL & _).
pose proof HRGPL as (Elock & Ensrc & Esrc & _).
assert (HN : Z.of_nat (length (rxes cx)) <= 16) by (unfold rN, AENT, ATABLE in Ttl; lia).
(* the seat at 0x83f68 *)
remember (Eimg (Ereg regs1 (rge_extra (rxG0 cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rge_extra (rxG0 cx))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E24 : ew E 24 = getr regs1 24)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 24 24%bv eq_refl)).
pose proof (pa_obj_img 8 ltac:(lia)) as HO8.
assert (HS : st_ok_pi SEGS VAL E ss_rge (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_ge)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rge. apply pa_entry_st_ok_full.
- unfold rge_sr. apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H25. apply bv_eq. fold (U E (SOff (A_HI 60) 0)). rewrite (U_img_atom E HEI (A_HI 60)) by (cbv; lia).
  rewrite HH60. unfold w64. rewrite unsigned_lit_small by (unfold RR_HI_SRC; lia). reflexivity.
- vm_compute. reflexivity.
- unfold rge_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite (HEI (A_OBJ 8)) by (cbv; lia). rewrite <- Esrc.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) (rxG0 cx));
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact TSv.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
  + cbn [rge_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by lia. change (2 ^ 4) with 16. unfold RGE_PHI.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rge_facts f_alias alias_ok]. exact I. }
assert (SHOK : sh_ok SEGS RGE_BX rge_SH E (mrestrict (w_H W1) m1)) by (unfold sh_ok, rge_SH; constructor).
clear HE.
unfold cfg_at. change (w64 (BASE + A_rr_ge)) with (Z_to_bv 64 (BASE + A_rr_ge)).
(* ld a0, g_src; add a0, a0, s8; jal gestures_end: to the callee's entry *)
paj_run_to_tok_xR RUNTOR HS HJ SHOK rge_Bspan AF_fr_gestures_end.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rge_mem Em1.
pmkst HS.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (25%bv : bv 5) R25.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RGE_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK end.
cbn [ms_regs restrict] in HK.
rewrite Em1 in HJ |- *.
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25).
{ change (ew E 340) with (ew E (A_HI 60)) in R25. apply bv_eq. rewrite R25, (HEI (A_HI 60)) by (cbv; lia).
  rewrite H25, HH60. unfold w64. rewrite unsigned_lit_small by (unfold RR_HI_SRC; lia). reflexivity. }
assert (KR : forall r, In r (25%bv :: RGE_KEPT) -> getr (ms_regs ms) r = getr regs1 r)
by (intros r [<- | Hr]; [exact R25' | exact (HK r Hr)]).
clear HK R25 R25'.
(* the call's registers *)
assert (Rsa : getr (ms_regs ms) 10 = w64 (rmSA cx i)).
{ rewrite R10, E24, H24, E32. unfold w64. rewrite YI08.alu64_add_lit. unfold rmSA. f_equal. lia. }
(* the facts at the cut *)
destruct (W_gesture_end.aout_facts B RG ly1 S1 W1 m1 _ _ _ _ _ _ HOUT) as (Hmx & HnoO & Hblk).
pose proof (W_gestures_end.gse_nodup_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 HAR) as ND. apply (Permutation_NoDup HPM) in ND.
destruct (rr_call_chain_xR B PST ARx MT RP MMAX RG HG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HLV) as (ch1 & Hch1).
pose proof HEO as (_ & _ & EP1 & EP2 & _ & _ & _ & _ & _ & EBUF & ENH & EHP & ENDA & ENDT & EKS).
pose proof HPRE as (_ & _ & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSA0 : rxG0 cx <= rmSA cx i /\ rmSA cx i + AENT <= rxG0 cx + ATABLE) by (unfold rmSA, AENT, ATABLE; lia).
assert (HSA8 : rmSA cx i mod 8 = 0).
{ unfold rmSA, AENT. pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D. rewrite D.
  replace (16 * (rxG0 cx / 16) + 56 * Z.of_nat i) with ((2 * (rxG0 cx / 16) + 7 * Z.of_nat i) * 8) by ring.
  apply Z_mod_mult. }
assert (HSL : garr8 SEGS (arm W1 m1) (rmSA cx i) (bzs (entry_bytes e1))).
{ unfold bzs in Tg. rewrite !map_app in Tg. apply garr8_app in Tg as [_ Tg]. apply garr8_app in Tg as [Tg _].
  rewrite length_map, (rgl_tpre_len cx i HB ltac:(lia)) in Tg. unfold rmSA. exact Tg. }
assert (HHELD : aheld_ok B ly1 S1 W1 m1 e1) by exact (conj EP1 (conj EP2 (conj ENH (conj EHP (conj ENDA (conj ENDT EKS)))))).
assert (HPG : Permutation (ablocks B ly1 S1) ((rxG0 cx, ATABLE) :: gse_blks e1 ++ aout_blks (rmcap1 cx i) out1 ++
                (rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx))).
{ eapply perm_trans; [exact HPM|]. apply perm_skip. rewrite rgl_aentry_blks. apply rgl_perm_ge. }
pose proof (rgl_end5 W1 m1 HROM) as HE5.
assert (HXS : Forall (fun x : list byte => x <> []) (gse_keys e1)).
{ unfold gse_keys. apply Forall_map. eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & Hk) Hn.
  rewrite Hn in Hk. cbn in Hk. lia. }
assert (HRM : gse_room MMAX (blocks_bytes S1) (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i)
                (gse_keys e1))
by exact (rgl_hgroom cx i ly1 S1 W1 m1 e1 h1 ev LB spent HB Hi Hfd HDR HEO HBUD).
assert (ECOST : gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1) =
                tr_cost MT (rmtrK cx i) + mo_free MT).
{ rewrite (rgl_trK cx i ly1 S1 W1 m1 e1 h1 LB ev HB Hi Hfd HDR).
  apply (rgl_cost_lv MT (gse_keys e1) (drain_b_c.da_out drain_b_c.dadr0) (rmc1 cx i ev) (rxmx cx) _ _ _ _ 0%nat
    (drain_b_c.da_out drain_b_c.dadr0) (sl_live (rmc1 cx i ev) 1) eq_refl HXS). intros _. split; reflexivity. }
pose proof (mo_free_nonneg MT MLAW) as MF.
assert (TFc : tr_cost MT (rmtrF cx i) = mo_free MT + mo_free MT) by (unfold rmtrF, tr_cost; cbn [fold_right]; lia).
assert (HMOK : mo_ok MT S1 (gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i)
                 (gse_keys e1))).
{ pose proof HBUD as (BLE & B0 & BC & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BMOK & _).
  rewrite rm_tr_cost_app in BC. rewrite ECOST.
  apply (mo_ok_step MT MLAW (rxS cx) S1 spent _); [|exact BLE].
  apply (mo_ok_le MT MLAW (rxS cx) _ _ BMOK). lia. }
(* the room round: gestures_end's room at the counting meter, kr := 1 + kr of the entry (the buf free's 1 is left),
   from rmbud's room for the rest (the key run, then two frees) *)
assert (ECOSTrk : gse_cost MT_rk (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1) =
                  tr_cost MT_rk (rmtrK cx i) + mo_free MT_rk).
{ rewrite (rgl_trK cx i ly1 S1 W1 m1 e1 h1 LB ev HB Hi Hfd HDR).
  apply (rgl_cost_lv MT_rk (gse_keys e1) (drain_b_c.da_out drain_b_c.dadr0) (rmc1 cx i ev) (rxmx cx) _ _ _ _ 0%nat
    (drain_b_c.da_out drain_b_c.dadr0) (sl_live (rmc1 cx i ev) 1) eq_refl HXS). intros _. split; reflexivity. }
assert (HRMg : rp_RM RP S1 (Z.to_nat (gse_cost MT_rk (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB)))
                 (rmcap1 cx i) (gse_keys e1)) + (1 + rxkr cx))).
{ pose proof HBUD as (_ & _ & _ & _ & _ & HRMb).
  pose proof (rgl_rk_nonneg (rmtrK cx i)) as TK0.
  assert (TFrk : tr_cost MT_rk (rmtrF cx i) = 2) by (unfold rmtrF, tr_cost; reflexivity).
  rewrite rm_tr_cost_app_m, TFrk in HRMb.
  refine (RMM_of RP S1 _ _ _ HRMb). rewrite ECOSTrk. change (mo_free MT_rk) with 1. lia. }
assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => remember mdx as mdc eqn:Hmdc end.
(* the call: gestures_end (&g_src[i]) through GSE, its journal lifted to G_RR *)
apply SRr_ret. eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (W_gestures_end.gse_callS_xR B PST ARx LAWS R R_trans (G_RR B RG) W1 (ms_regs ms) m1 _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx)
    (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 mdc k1 GSE_STK
    ((rmSA cx i + 40, rmSA cx i + 52) :: ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) (-96)
    (Z_to_bv 64 (BASE + 7304)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => exists Hq k2 out2,
      ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) 0 [] GSE_STK (spZ (ms_regs ms))
        ((rmSA cx i + 40, rmSA cx i + 52) :: ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1))
        ly1 S1 Hp1 W1 m1 mdc [] ly2 S2 Hq W2 mem2 md2 k2 /\
      apres_kept B W1 m1 W2 mem2 /\
      mo_le MT S1 S2 (gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)) /\
      rp_RM RP S2 (1 + rxkr cx) /\
      Permutation (ablocks B ly2 S2) ((rxG0 cx, ATABLE) ::
        aout_blks (gse_cap (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB)))
                             (rmcap1 cx i) (gse_keys e1))) out2 ++
        (rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx)) /\
      aout_at B RG ly2 S2 W2 mem2
        (gse_c (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        (gse_O (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        (rxmx cx)
        (gse_no (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        (gse_cap (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)))
        out2 /\
      garr8 SEGS (arm W2 mem2) (rmSA cx i) (bzs (entry_bytes (entry_cleared e1))) /\ awr W2 mem2 (rmSA cx i) AENT)
    HG HJ).
  - unfold spZ. rewrite (KR 2%bv) by (cbv; tauto). fold (spZ regs1). rewrite Hsp. unfold RR_FRAME. lia.
  - reflexivity.
  - lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - rewrite (KR 3%bv) by (cbv; tauto). rewrite H3. exact Hgp.
  - rewrite (KR 4%bv) by (cbv; tauto). rewrite H4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof pa_B_ok as HBO. pose proof pa_base_lo as HBL. rewrite unsigned_lit_small by lia. lia.
  - replace (rsp0 cx + -96) with (rsp0 cx - RR_FRAME) by (unfold RR_FRAME; lia).
    unfold s0Z. rewrite (KR 8%bv) by (cbv; tauto). rewrite H8. unfold w64.
    rewrite unsigned_lit_small by (unfold rsp0 in *; lia). exact Hch1.
  - intros HPRE1. eapply YA0nH.SRrG_mono.
    { exact (GSE_R W1 ly1 S1 Hp1 (ms_regs ms) m1 mdc ch1 (rmSA cx i) (rxG0 cx) e1 (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx)
        (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) out1 (rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx)
        HPRE1 Rsa TIn (proj1 HSA0) (proj2 HSA0) HSA8 HSL TSA HHELD HOUT HPG HE5 HROM HRM HMOK (1 + rxkr cx)%nat HRMg HCNT). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & out2 & -> & HJ2 & HP2 & HAK2 & HM2 & HRM2 & HPm2 &
      HO2 & HSL2 & HSA2).
    exists ly2, S2, Hp2, regs2, mem2, md2, k2. split; [rewrite R1; reflexivity|].
    split; [eapply rr_lift_SL_xR; exact HJ2|]. split; [exact HP2|].
    exists Hp2, k2, out2. split; [exact HJ2|]. split; [exact HAK2|]. split; [exact HM2|]. split; [exact HRM2|].
    split; [exact HPm2|]. split; [exact HO2|]. split; [exact HSL2 | exact HSA2].
  - intros a (r & Hr & Hra). destruct Hr as [<- | Hr].
    + cbn [fst snd] in Hra. left. split.
      * unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
        apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE);
          [left; reflexivity | change (req_size ATABLE) with 896; unfold rmSA, AENT in *; lia].
      * exists (rxG0 cx), ATABLE. split; [exact TIn | change (req_size ATABLE) with 896; unfold rmSA, AENT in *; lia].
    + assert (Ha' : inFP (ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) a) by (exists r; split; assumption).
      apply inFP_ablocks_fp_inv in Ha' as (p & n & Hpn & Hpa).
      assert (Hpn' : In (p, n) ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++
                                 aout_blks (rmcap1 cx i) out1)).
      { right. rewrite rgl_aentry_blks. apply in_app_or in Hpn as [Hpn | Hpn].
        - apply in_or_app. left. apply in_or_app. right. exact Hpn.
        - apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
      assert (Hin1 : In (p, n) (ablocks B ly1 S1)).
      { apply (Permutation_in _ (Permutation_sym HPM)). destruct Hpn' as [E0 | Hpn']; [left; exact E0|].
        right. rewrite !app_assoc. apply in_or_app. left. rewrite <- !app_assoc. exact Hpn'. }
      destruct (in_dec DEC (p, n) (ablocks B (rxly cx) (rxS cx))) as [IN0 | NIN0].
      * left. split; [|exists p, n; split; [exact Hin1 | exact Hpa]].
        pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BPM & _).
        apply (Permutation_in _ BPM) in IN0. unfold rFP, rr_fp. replace a with (p + (a - p)) by lia.
        apply (inFP_ablocks_fp _ p n); [|lia].
        destruct IN0 as [E0 | IN0]; [left; exact E0|]. right.
        assert (IN1 : In (p, n) ((concat (map aentry_blks (rxes cx)) ++
                     (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx))
                     ++ rxrest cx)) by (rewrite <- !app_assoc; exact IN0).
        apply in_app_or in IN1 as [IN1 | IN1]; [exact IN1|]. exfalso.
        apply (rgl_nd_app ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++
                 aout_blks (rmcap1 cx i) out1) (rxrest cx) (p, n)); [|exact Hpn' | exact IN1].
        replace (((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ aout_blks (rmcap1 cx i) out1) ++
                 rxrest cx) with ((rxG0 cx, ATABLE) :: aentry_blks e1 ++ rmOB cx i ++ rmsrc cx i h1 ++
                 aout_blks (rmcap1 cx i) out1 ++ rxrest cx) by (cbn [app]; rewrite <- !app_assoc; reflexivity).
        exact ND.
      * right. exists p, n. split; [exact Hin1|]. split; [exact NIN0 | exact Hpa]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJ2 & HJc2 & HP2 &
  (Hq & k2 & out2 & HJs & HAK2 & HM2 & HRM2 & HPm2 & HO2 & HSL2 & HSA2)).
apply SRr_to_G.
(* no ARx state has a hidden head (HP0): the callee's and the caller's head sets after the call are both [] *)
assert (EHq : Hq = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJs).
assert (EHp2 : Hp2 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJ2).
subst Hq Hp2.
(* ---- back at 0x83f74: what gestures_end kept ---- *)
set (FP1 := (rmSA cx i + 40, rmSA cx i + 52) :: ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) in *.
set (RESTX := rmbuf e1 ++ rmOB cx i ++ rmsrc cx i h1 ++ rxrest cx) in *.
assert (Usp : spZ (ms_regs ms) = rsp0 cx - RR_FRAME)
by (unfold spZ; rewrite (KR 2%bv) by (cbv; tauto); fold (spZ regs1); exact Hsp).
rewrite Usp in HJs.
assert (HGSL : gx_ok SEGS B (G_SL B RG)) by exact (gx_ok_sub SEGS B _ _ (rr_G_SL_RR B RG) HG).
assert (GA1 : forall b, In b (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPG)). right. rewrite app_assoc. apply in_or_app. left. exact Hb. }
assert (ND' : List.NoDup ((rxG0 cx, ATABLE) :: gse_blks e1 ++ aout_blks (rmcap1 cx i) out1 ++ RESTX))
by (apply (Permutation_NoDup HPG); exact (W_gestures_end.gse_nodup_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 HAR)).
pose proof (proj1 (NoDup_cons_iff _ _) ND') as (TNG & ND2). rewrite app_assoc in TNG, ND2.
assert (FPB : forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
{ intros a (r & Hr & Hra). destruct Hr as [<- | Hr].
  - exists (rxG0 cx), ATABLE. split; [exact TIn|]. change (req_size ATABLE) with 896. cbn [fst snd] in Hra.
    unfold rmSA, AENT in *. lia.
  - assert (Ha' : inFP (ablocks_fp (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1)) a) by (exists r; split; assumption).
    apply inFP_ablocks_fp_inv in Ha' as (p & n & Hpn & Hpa). exists p, n. split; [exact (GA1 _ Hpn) | exact Hpa]. }
assert (HFP0 : Forall (fun r => 0 < fst r) FP1).
{ unfold FP1. constructor; [cbn [fst]; unfold rmSA, AENT in *; lia|].
  apply Forall_forall. intros r Hr. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR (GA1 _ Hpn)) as (_ & Hp & _). lia. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> abyte_kept W1 m1 W2 mem2 a).
{ intros a I1 I2 I3 I4 I5. apply (rgl_keep_img_xR (G_SL B RG) GSE_STK (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 mdc ly2 S2 []
    W2 mem2 md2 k2 a HJs HAK2 I1 I2 I3 I4); [|exact I5].
  apply fp_spares_closed. apply sink_closed_pos. exact HFP0. }
assert (HARc : ARx ly1 S1 Hp1 W1 m1 mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (KREST : forall p n a, In (p, n) RESTX -> p <= a < p + req_size n -> abyte_kept W1 m1 W2 mem2 a).
{ intros p n a Hp Ha.
  assert (I1 : In (p, n) (ablocks B ly1 S1)).
  { apply (Permutation_in _ (Permutation_sym HPG)). right. apply in_or_app. right. apply in_or_app. right. exact Hp. }
  assert (I2 : In (p, n) (ablocks B ly2 S2)).
  { apply (Permutation_in _ (Permutation_sym HPm2)). right. apply in_or_app. right. exact Hp. }
  apply (rgl_keep_blk_xR (G_SL B RG) GSE_STK (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 mdc ly2 S2 [] W2 mem2 md2 k2 p n a
    HGSL HJs HARc I1 I2 Ha).
  intros (r & Hr & Hra). destruct Hr as [<- | Hr].
  - assert (Hne : (rxG0 cx, ATABLE) <> (p, n)).
    { intros Eq. apply TNG. apply in_or_app. right. rewrite Eq. exact Hp. }
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE p n HAR TIn I1 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D, Hra. change (req_size ATABLE) with 896 in D.
    unfold rmSA, AENT in *. lia.
  - assert (Hbl : forall b, In b (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1) -> In b (ablocks B ly1 S1) /\ b <> (p, n)).
    { intros b Hb. split; [exact (GA1 _ Hb)|]. intros ->. exact (rgl_nd_app _ _ (p, n) ND2 Hb Hp). }
    exact (rgl_notfp ly1 S1 Hp1 W1 m1 md1 _ p n a HAR I1 Ha Hbl (ex_intro _ r (conj Hr Hra))). }
assert (KTAB : forall a, rxG0 cx <= a < rxG0 cx + ATABLE -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
  abyte_kept W1 m1 W2 mem2 a).
{ intros a Ha Hs.
  assert (T2 : In (rxG0 cx, ATABLE) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPm2)); left; reflexivity).
  assert (Har : rxG0 cx <= a < rxG0 cx + req_size ATABLE) by (change (req_size ATABLE) with 896; unfold ATABLE in Ha; lia).
  apply (rgl_keep_blk_xR (G_SL B RG) GSE_STK (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 mdc ly2 S2 [] W2 mem2 md2 k2 (rxG0 cx)
    ATABLE a
    HGSL HJs HARc TIn T2 Har).
  intros (r & Hr & Hra). destruct Hr as [<- | Hr].
  - cbn [fst snd] in Hra. unfold AENT in Hs. lia.
  - assert (Hbl : forall b, In b (gse_blks e1 ++ aout_blks (rmcap1 cx i) out1) ->
                  In b (ablocks B ly1 S1) /\ b <> (rxG0 cx, ATABLE)).
    { intros b Hb. split; [exact (GA1 _ Hb)|]. intros ->. apply TNG. apply in_or_app. left. exact Hb. }
    exact (rgl_notfp ly1 S1 Hp1 W1 m1 md1 _ (rxG0 cx) ATABLE a HAR TIn Har Hbl (ex_intro _ r (conj Hr Hra))). }
pose proof HRGPL as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HBUD as (BLE & B0 & BC & _). rewrite rm_tr_cost_app in BC.
apply SRr_ret. apply K. unfold RRF_xR.
exists regs2, ly2, S2, (@nil Z), mem2, md2, (k1 + kk), F, FL, e1, h1, ev, LB,
  (gse_c (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1))),
  (gse_O (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1))),
  (gse_cap (gse_run (rmc1 cx i ev) (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1))),
  out2, (spent + gse_cost MT (rmc1 cx i ev) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB))) (rmcap1 cx i) (gse_keys e1)).
split; [unfold cfg_at; reflexivity|].
split.
{ apply (rgl_rmhd cx i regs1 regs2 F HMD). intros r Hr. rewrite <- (KR r Hr). rewrite <- (Z_to_bv_bv_unsigned _ r).
  apply HP2. cbn [In RGE_KEPT] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [match goal with |- acallee_saved (bv_unsigned ?b) => let v := eval vm_compute in (bv_unsigned b) in
       change (bv_unsigned b) with v end; unfold acallee_saved; lia|]).
  destruct Hr. }
split.
{ apply (rr_live_call_xR B PST ARx MT RP MMAX RG LAWS HRGP HROMO PSTR PSTG R cx F FL fpos ly1 S1 Hp1 W1 m1 mdc k1 (G_SL B RG)
    GSE_STK FP1 ly2 S2 [] W2 mem2 md2 k2 (k1 + kk) HB HJ HROM HAPK HFR HLK HWK HGSL);
    [| | exact HJs | exact HFP0 | exact FPB | exact HAK2 |
    exact HJ2].
  - intros a Ha. unfold G_DR, inG in *. apply Exists_cons_tl. exact Ha.
  - split; apply Z.leb_le; vm_compute; reflexivity. }
split.
{ pose proof HDR as HDR'. unfold rmdrel in HDR' |- *. destruct (rmopen cx i) eqn:Eo; [|exact HDR'].
  destruct HDR' as (HDR' & HAS). split; [exact HDR'|].
  assert (Ho : re_eof (rnth cx i) = 0) by (unfold rmopen in Eo; apply Z.eqb_eq; exact Eo).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDS & _). destruct (HDS i Hi Hfd Ho) as (Hj4 & _).
  assert (INS : forall b, In b (asrc_blks h1) -> In b RESTX).
  { intros b Hb. unfold RESTX, rmsrc. rewrite Eo. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 mem2 (rmHA RG cx) h1 HAS).
  - intros r Hr a Ha. destruct (rgl_fp_asrc ly1 S1 W1 m1 _ h1 HAS r a Hr Ha) as [Hg | (p & n & Hpn & Hpa)].
    + assert (Hgs : rg_s RG <= a < rg_s RG + 4 * ASRC) by (unfold rmHA, ASRC in *; lia).
      destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (I1 & I2 & I3).
      exact (KIMG a I1 I2 I3 (rgl_gc a (or_introl Hgs)) (rgl_gs_nSL a Hgs)).
    + exact (KREST p n a (INS _ Hpn) Hpa).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPm2)). right. apply in_or_app. right. exact (INS _ Hb). }
split; [exact EP1|]. split; [exact EP2|].
split; [destruct EBUF as [(Hc & Hb & _) | (Hc & _)]; [left; split; assumption | right; exact Hc]|].
split.
{ assert (KC : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
                         rg_capsrc RG <= a < rg_capsrc RG + 4 -> abyte_kept W1 m1 W2 mem2 a).
  { intros a Ha.
    assert (HI : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
    { destruct Ha as [Ha | [Ha | Ha]].
      - apply RGIMG. unfold rg_rng. tauto.
      - apply RGIMG. unfold rg_rng. tauto.
      - destruct (HRGI a ltac:(tauto)) as [I1 I2]. split; [exact I1|]. split; [exact I2|].
        eapply rr_capsrc_nerr; [exact HRGP | exact Ha]. }
    destruct HI as (I1 & I2 & I3). apply (KIMG a I1 I2 I3); [apply rgl_gc; tauto|].
    apply rgl_nSL. eapply rr_nG_DR; [exact HRGP|]. tauto. }
  unfold rmtbl.
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; left; cbn in Hx; lia | exact TSv]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; left; lia | exact TSw]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; right; left; cbn in Hx; lia | exact TNv]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; right; left; lia | exact TNw]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; right; right; cbn in Hx; lia | exact TCv]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; right; right; lia | exact TCw]|].
  split; [apply (Permutation_in _ (Permutation_sym HPm2)); left; reflexivity|].
  pose proof (W_rr_scan.rrs_eb_len e1 EP1 EP2) as LE1.
  pose proof (W_rr_scan.rrs_eb_len (entry_cleared e1) EP1 EP2) as LE2.
  pose proof (rgl_tpre_len cx i HB ltac:(lia)) as LPRE. pose proof (rgl_tpost_len cx i HB Hi) as LPOST.
  split; [rewrite LE2; reflexivity|].
  split.
  { exists tail. split; [exact Ttl|].
    unfold bzs in Tg, HSL2 |- *. rewrite !map_app in Tg |- *.
    apply garr8_app in Tg as [TgA Tg]. apply garr8_app in Tg as [_ TgB].
    rewrite !length_map, LPRE, LE1 in TgB.
    apply garr8_app. split.
    - apply (akept_garr8 W1 m1); [|exact TgA]. intros x Hx. rewrite length_map, LPRE in Hx.
      apply KTAB; unfold rmSA, AENT, ATABLE in *; lia.
    - rewrite length_map, LPRE. apply garr8_app. split.
      + unfold rmSA in HSL2. exact HSL2.
      + rewrite length_map, LE2. apply (akept_garr8 W1 m1); [|exact TgB]. intros x Hx.
        rewrite length_app, !length_map, Nat2Z.inj_add, LPOST, Ttl in Hx. unfold rN in Hx.
        apply KTAB; unfold rmSA, AENT, ATABLE in *; lia. }
  split; [exact HSA2|].
  rewrite Forall_forall in TOK |- *. intros e He.
  assert (INE : forall b, In b (aentry_blks e) -> In b RESTX).
  { intros b Hb. unfold RESTX. apply in_or_app. right. apply in_or_app. left. unfold rmOB. apply in_concat.
    exists (aentry_blks e). split; [apply in_map; exact He | exact Hb]. }
  apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 mem2 e (TOK e He)).
  - intros r Hr a Ha. destruct (rgl_fp_aentry _ _ _ _ e (TOK e He) r a Hr Ha) as (p & n & Hpn & Hpa).
    exact (KREST p n a (INE _ Hpn) Hpa).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPm2)). right. apply in_or_app. right. exact (INE _ Hb). }
split; [unfold gse_keys; rewrite rgl_sends; reflexivity|].
split; [destruct (W_gesture_end.aout_facts B RG ly2 S2 W2 mem2 _ _ _ _ _ _ HO2) as (_ & HnoO2 & _); rewrite HnoO2; exact HO2|].
split; [eapply perm_trans; [exact HPm2|]; apply perm_skip; unfold RESTX; apply rgl_perm_gf|].
split.
{ intros a Ha Hd. apply (rgl_abk_trans (rxW cx) W1 W2 (rxmem cx) m1 mem2 a (HGS a Ha Hd)).
  destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (I1 & I2 & I3).
  exact (KIMG a I1 I2 I3 (rgl_gc a (or_introl Ha)) (rgl_gs_nSL a Ha)). }
split; [exact (mo_le_trans MT MLAW (rxS cx) S1 S2 spent _ BLE HM2)|].
split; [rewrite ECOST; lia|].
(* the room round: gestures_end's post leaves the buf free's 1, then kr; the free's count premise from RRG's gse_pk *)
split; [exact HRM2|].
exact (rgl_cnt_ge (rxG0 cx) (gse_blks e1) (rmcap1 cx i) out1 _ out2 RESTX _ _ HPG HPm2 HCNT).
Qed.
End wR.

End c.
End b.
End a.
