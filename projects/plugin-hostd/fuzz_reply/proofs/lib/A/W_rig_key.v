(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segments KEY and KEYS of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82e50 .. 0x82f44), against the segment interface lib/A/W_relay_instance_gone_cx.v (its
   Section-hypothesis block copied verbatim).
   KEY (rig_key_proof): one held key from the inner loop's head RGI i n r: the shadow checks of s->held and held[n],
   strncmp (key, prefix, |prefix|) at 0x82e80 by ASTRNCMP.  A key without the prefix is passed (0x82f20: RGI i (S n)
   r' through 0x82e4c, or RGE i); a key with it is ended: gesture_end (key) at 0x82e8c by GE, free (key) at 0x82eb4
   by AFREE, nheld -= 1 (0x82ed4) and held[n] = held[nheld] (0x82f08), then RGI i n r' or RGE i.  The model side is
   GIN's geik_loop step and the swap-remove of the keys; the meter moves between gbud states through gkrest.
   KEYS (rig_keys_proof): the inner loop by induction on r.
   GE is used at ge_spec as commit ece23323751 states it (W_contract.v: ge_room, the room over
   gesture_end's own request trace), which this branch carries as a cherry-pick.  Written new, with the plain proof
   lib/Prog/relay_instance_gone_b.v (and its list lemmas, relay_instance_gone_b_lem.v) as the template; the
   restarted trace's independence of the addresses is proved here once (rkb_er_tr, rkb_er_eq, rkb_ker_er).
   C3 (475b8a2b569, the peak form): ge_room and gbud's room are over tr_peak; each key's gesture_end takes its room from
   the remaining trace's prefix (rkb_ker_split, rkb_ge_room), and gbud after the key from the NET change of the key's
   gesture_end and free (rkb_ge_net: g_out's growth; the free lowers the live bytes by |key| + 1; rkb_gbud_end). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), the RIG_x
   round: KEY and KEYS over any allocator relation ARx with its laws and the room record RP, against the cx file's
   generic Section (commit 863f3bb0f69, lib/A/W_relay_instance_gone_cx.v; its Section c copied verbatim below).
   Every ARx state of this walk is read at the empty head set (HP0: ARh below), so each journal runs from [] to [].
   strncmp at astrncmp_realizes_x; gesture_end at ge_spec_x with its room premise rp_RM RP S1 (ge's MT_rk charge +
   1 + the room the rest of the trace owes, rk_krn) and its count premise cnt_ok_pk RP ge_pk, both from GIN's gbud
   (rk_room); the free at afree_cf_rule_c_x with rp_RM (1 + rk_krn) and cnt_ok (the live counts after gesture_end are
   at most one above GIN's); after the key, gbud's room is the free's post and its count invariant follows from the
   count change of gesture_end's send chain, exactly cphi P (ge_cap ..) - cphi P cap = tr_netP P (ge_tr ..) (rkc_ge_netP,
   from the round chain's equality rkc_slr_net), and the free's - zb (P (|k| + 1)) (rkb_gbud_end).  The meter lemmas
   that also serve MT_rk are stated over any meter in Section rkm. *)
(* Modified by Theorem Labs, 2026-10: route R (G8 rig, key): Section wR at the end of Section c lifts KEY and KEYS to a
   world relation R, concluding rig_key_stmt_xR / rig_keys_stmt_xR of the cx file's Section wR.  The strict statements
   and proofs are unchanged; two Require lines are added (W_contract_xR, YA0nH). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_frame_x W_kit_x.
(* the count names (acnt, zb, tr_peakP): lib/A/ReplyCnt.v, Required, named qualified; tr_netP / cphi: W_tr_cnt.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem.
(* route R: a Theorem Labs lane's ge_spec_xR / dr_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
(* the program statics of the generic journal (YCbqG.ajournal_x's image clause exempts them) *)
Variable PST : list (Z * Z).
(* the allocator relation, its third argument the head set Hp *)
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts').  Each is either the AR
   walk's (AR-free, verbatim), its _x twin, or an instance fact that the instance supplies where RIG_x is plugged
   (top_x); the AR re-derivation was deleted (W_relay_instance_gone.v's header says why). ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP: the image cover IMGC (frm_off_imgP_x); a live
   block's size is non-negative (W_kit_x.v's BLKN); the owned-low law OWNLOW, the model invariant WFx with its law WFL,
   and the two facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
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
(* the fake frame's laws over ARx: __asan_stack_malloc_1 (class 1), the release's flag store and frame free *)
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 1.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
(* the live-state meter does not see the fake frame (W5's relay_add hypothesis, verbatim) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x82d58 (kept at 72(sp), listing A_HI 44) and 0x82d74
   (s6, A_HI 45).  The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges
   both by vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH44 : VAL (A_HI 44) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH45 : VAL (A_HI 45) = rg_src RG + RIG_HI_SRC.
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
   allocator's calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RIG B RG).
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx, as W_drain_cx_x.v states it; there a theorem
   of the laws, alloc_tail_x): a held key is represented over its |text| + 1 bytes (ruling (A)); a word read of a
   key to the end of its last granule is visible *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP).  snprintf: a Theorem Labs lane's statement at fuzz_reply's
   addresses (W_sites.v asnprintf_realizes, its twin W_sites_x.v asnprintf_realizes_x), which the snprintf chain
   (commit 9067b7156f9, lib/A/RT_pf_vf.v snprintf_chain_ok, through a Theorem Labs lane's evt -> SRr bridge) discharges. *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis ASNPRINTF : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
(* the program functions relay_instance_gone calls (W7's drain, W4's gesture_end), by their published _x room specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* snprintf's stack-protector cells (see the header): the GOT word, a fact of every ARx state (at ARi0: the AR fact
   of lib/A/AE22.v got_canary_of_AR); the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the canary's bytes are image bytes (seg_rom SEGS at FR_GUARD .. + 8 is Some 0), so aview reads them in EVERY state
   through mbyte's seg_rom fallback: aguard_ok's second half needs nothing carried (a Theorem Labs lane's ruling; a Theorem Labs lane's
   pin measurement).  PB_fr decides it by vm_compute. *)
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the two literals of the snprintf call, in W7's dlit_at form (W_drain_cx.v:220): the bytes in .rodata, read-only,
   zero shadow, and the shadow hull visible in every ARx state *)
Definition RIG_FMT : list Z := [37; 115; 32; 37; 100; 32].   (* "%s %d " *)
(* ashp is RomOutPlace's lib/A/W_shadow_pin.v (commit 209a71e66fe), the unit's one definition: range_addressable over
   exactly [a, a + n) and the shadow hull, in every allocator state; glit_at_x states it over ARx (W_contract_x.v
   ashp_x), as the cx file does. *)
Definition glit_at_x (i : nat) (l : list Z) : Prop :=
(forall k, (k < length l)%nat ->
   seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ i) + Z.of_nat k)) = option_map (Z_to_bv 8) (nth_error l k)) /\
(forall x, VAL (A_OBJ i) <= x < VAL (A_OBJ i) + Z.of_nat (length l) -> YG0d.in_rom SEGS x) /\
ashp_x ARx (VAL (A_OBJ i)) (Z.of_nat (length l)) /\
(* the bytes after the literal's NUL to the end of its 8-byte granule are image bytes (snprintf's atail_vis and its
   "%s" argument read to the granule's end; found by BRigTop at 0x82eb8; PB_fr decides it by vm_compute) *)
(forall x, VAL (A_OBJ i) + Z.of_nat (length l) <= x <
   VAL (A_OBJ i) + Z.of_nat (length l) - 1 - (VAL (A_OBJ i) + Z.of_nat (length l) - 1) mod 8 + 8 ->
   seg_rom SEGS (Z_to_bv 64 x) <> None).
Hypothesis HLIT20 : glit_at_x 20 (RIG_FMT ++ [0]).
Hypothesis HLIT21 : glit_at_x 21 (RelayModel.K_GESTURE ++ [0]).
(* the two literals lie in .rodata below the GOT word FR_GOT_GUARD = 0x9e658, |"%s %d "| + 1 = 7 and
   |"param_gesture"| + 1 + 8 = 22 bytes: the location premises M1 / M3 of the narrowed asnprintf_realizes_x
   (W_sites_x.v), which this abstract placement does not fix.  PB_fr decides it by vm_compute: SnpNarrowSites.v
   HLITGOT_PB_fr, whose statement is this text at PI := PB_fr (commit 2f48fc47493's hypothesis, carried here). *)
Hypothesis HLITGOT : VAL (A_OBJ 20) + 7 <= FR_GOT_GUARD /\ VAL (A_OBJ 21) + 22 <= FR_GOT_GUARD.
(* " end\0" (.str.4, A_lit_end5 = A_OBJ 31) in the same form, for gesture_end's / gestures_end's garr8 premise and its
   ashp (instance: W_shadow_pin_fr.v ashp_end5_5_fr): bytes, in_rom, ashp, the granule's tail; HEND5L above gives the
   bytes alone *)
Hypothesis HLIT31 : glit_at_x 31 ([32; 101; 110; 100] ++ [0]).
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x, the literals and " end\0"), and no byte of the
   relay's and the output's global cells (G_RIG, and the cells of HRGP that G_RIG does not name: g_src, g_nsrc,
   g_capsrc, g_send_max, g_client, g_send_dead).  At PST := [] both hold trivially (the template's PSTR / PSTC /
   PSTO, lib/A/W_relay_finish_h.v). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

(* ---- The callees' journals, lifted to relay_instance_gone's globals: drain's at G_DR and gesture_end's at G_SL are
   journals at G_RIG (W_journal_x.v ajournal_gx_G_mono_x), for every call-making segment. ---- *)
Lemma rig_G_DR_RIG : forall a, inG (G_DR B RG) a -> inG (G_RIG B RG) a.
Proof. intros a Ha. unfold G_RIG, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rig_G_SL_RIG : forall a, inG (G_SL B RG) a -> inG (G_RIG B RG) a.
Proof. intros a Ha. apply rig_G_DR_RIG. unfold G_DR, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rig_lift_DR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rig_G_DR_RIG | eassumption]. Qed.
Lemma rig_lift_SL : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rig_G_SL_RIG | eassumption]. Qed.

(* ==== the generic relation at the empty head set ==== *)
(* HP0: every ARx state this walk meets has the head set [], so the walk states its facts at ARh (= ARx at []) and
   each journal from [] to [] (a callee's post state is brought to [] by rk_hp0 / rk_jhp0 as it arrives). The wrappers
   keep the AR walk's argument order: rk_alb is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN). *)
#[local] Notation ARh ly S W mem md := (ARx ly S (@nil Z) W mem md).
Lemma rk_hp0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> ARh ly S W mem md.
Proof. intros ly S Hp W mem md H. pose proof (HP0 _ _ _ _ _ _ H) as E. subst Hp. exact H. Qed.
Lemma rk_jhp0 : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> Hp' = [].
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (HP0 _ _ _ _ _ _ (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
Qed.
Lemma rk_jAR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
ARh ly' S' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
exact (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
Lemma rk_alb : forall ly S W mem md p n, ARh ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
Definition rk_als ly S W mem md (H : ARh ly S W mem md) := alx_sep _ _ _ LAWS ly S [] W mem md H.
Definition rk_alf ly S W mem md cid pos (H : ARh ly S W mem md) := alx_frames _ _ _ LAWS ly S [] W mem md cid pos H.
Definition rk_alo ly S W mem md a (H : ARh ly S W mem md) := alx_owned_image _ _ _ LAWS ly S [] W mem md a H.
Definition rk_alc ly S W mem md a (H : ARh ly S W mem md) := alx_client_img _ _ _ LAWS ly S [] W mem md a H.
Definition rk_fb ly S W mem md cid pos (H : ARh ly S W mem md) := frames_bounds_x SEGS B ARx LAWS ly S [] W mem md cid pos H.
Definition rk_rab ly S W mem md p m a n (H : ARh ly S W mem md) :=
  range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md p m a n H.
Definition rk_shv ly S W mem md p m d n (H : ARh ly S W mem md) :=
  shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md p m d n H.
Definition rk_amr ly S W mem md p m a n (H : ARh ly S W mem md) :=
  YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly S [] W mem md p m a n H.
Definition rk_boi ly S W mem md p n (H : ARh ly S W mem md) := blk_off_imgP_x B ARx LAWS IMGC BLKN ly S [] W mem md p n H.
Definition rk_foi ly S W mem md cid pos (H : ARh ly S W mem md) := frm_off_imgP_x B ARx LAWS IMGC ly S [] W mem md cid pos H.
(* the entry's head set is empty too (GBASE's afn_pre_x states ARx at gxHp) *)
Lemma rk_gxHp : forall cx, GBASE B ARx MT RP MMAX RG cx -> gxHp cx = [].
Proof. intros cx HB. destruct HB as ((HAR & _) & _). exact (HP0 _ _ _ _ _ _ HAR). Qed.

(* ==== budget block (RigKeyBudget) ==== *)
(* ---- rkb: model and budget lemmas for segment KEY (pure: no machine state). ---- *)
(* The trace's requests ask nonnegative sizes. *)
Definition rk_sizes (t : list (RelayRunT.rev YO0i.sptr)) : Prop :=
Forall (fun e => match e with
  | RelayRunT.RMalloc n => 0 <= n
  | RelayRunT.RRealloc _ n _ => 0 <= n
  | RelayRunT.RFree _ _ => True end) t.

(* -- the stream's liveness at one byte is kept by every send and every drain -- *)
Lemma rkb_live_gen : forall cl br dd len,
send_line_c.send_live cl (if send_line_c.send_off cl br len then br else dd) dd 1 = send_line_c.send_live cl br dd 1.
Proof.
intros cl br dd len. unfold send_line_c.send_live, send_line_c.send_off.
destruct (cl <? 0); cbn [orb negb andb]; [reflexivity|].
destruct (br =? 1) eqn:Eb; cbn [orb negb andb]; [rewrite Eb; reflexivity|].
destruct (len =? 0); cbn [orb negb andb]; [rewrite Eb; reflexivity|].
destruct (Z.eqb_spec dd 0) as [->|Hd]; [reflexivity|].
rewrite andb_false_r. reflexivity.
Qed.

Lemma rkb_live_pos : forall c len, 0 < len -> sl_live c len = sl_live c 1.
Proof.
intros c len H. unfold sl_live, send_line_c.send_live, send_line_c.send_off.
replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma rkb_live_ctl : forall c len, sl_live (sl_ctl c len) 1 = sl_live c 1.
Proof. intros c len. unfold sl_live, sl_ctl. cbn [ct_cl ct_br ct_dd]. apply rkb_live_gen. Qed.

Lemma rkb_live_dr : forall c h ev, sl_live (dr_ctl c h ev) 1 = sl_live c 1.
Proof. intros c h ev. unfold sl_live, dr_ctl. cbn [ct_cl ct_br ct_dd]. apply rkb_live_gen. Qed.

Lemma rkb_live_sends : forall mx c O cap Bs, sl_live (fst (fst (sl_sends mx c O cap Bs))) 1 = sl_live c 1.
Proof.
intros mx c O cap Bs. revert c O cap. induction Bs as [|Bl r IH]; intros c O cap; cbn [sl_sends]; [reflexivity|].
rewrite IH. apply rkb_live_ctl.
Qed.

Lemma rkb_live_rel : forall pre mx c O cap ps qs c2 O2 cap2, rig_rel pre mx c O cap ps qs c2 O2 cap2 -> sl_live c2 1 = sl_live c 1.
Proof.
intros pre mx c O cap ps. revert c O cap.
induction ps as [|[e [h j]] r IH]; intros c O cap [|[e' h'] q] c2 O2 cap2 H; cbn [rig_rel] in H; try contradiction.
- destruct H as (-> & _ & _). reflexivity.
- destruct H as (e1 & ev & LB & H). cbv zeta in H. destruct H as (_ & _ & H).
  match type of H with context [sl_sends ?a ?b ?d ?g ?k] =>
    pose proof (rkb_live_sends a b d g k) as HL; revert H HL;
    destruct (sl_sends a b d g k) as [[c3 O3] cap3]; intros H HL end.
  cbn [fst] in HL. cbv beta iota in H. rewrite (IH _ _ _ _ _ _ _ H), HL.
  destruct (re_eof e =? 0); [apply rkb_live_dr | reflexivity].
Qed.

Lemma rkb_live_gin : forall cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
sl_live c2 1 = sl_live (gxc cx) 1.
Proof.
intros cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 H.
unfold GIN in H. cbv zeta in H.
destruct H as (_ & _ & Hrel & Hdr & Hs & _).
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & _).
pose proof (rkb_live_sends (gxmx cx) c1 O1 cap1 (ge_bytes Ed)) as HL. rewrite Hs in HL. cbn [fst] in HL.
rewrite HL, Ec1. rewrite <- (rkb_live_rel _ _ _ _ _ _ _ _ _ _ Hrel).
destruct (re_eof (gnth cx i) =? 0); [apply rkb_live_dr | reflexivity].
Qed.

(* -- the sends -- *)
Lemma rkb_sends_app : forall mx c O cap B1 B2,
sl_sends mx c O cap (B1 ++ B2) = let '(c', O', cap') := sl_sends mx c O cap B1 in sl_sends mx c' O' cap' B2.
Proof.
intros mx c O cap B1. revert c O cap.
induction B1 as [|Bl r IH]; intros c O cap B2; cbn [app sl_sends]; [reflexivity | apply IH].
Qed.

Lemma rkb_ge_bytes_app : forall E1 E2, ge_bytes (E1 ++ E2) = ge_bytes E1 ++ ge_bytes E2.
Proof. intros E1 E2. unfold ge_bytes. rewrite map_app, concat_app. reflexivity. Qed.

Lemma rkb_sl_O_len : forall c O x, Z.of_nat (length (sl_O c O x)) = sl_no c (Z.of_nat (length O)) (Z.of_nat (length x)).
Proof. intros c O x. unfold sl_O, sl_no. destruct (sl_live c _); [rewrite length_app; lia | reflexivity]. Qed.

Lemma rkb_sends_key : forall mx c O cap k,
sl_sends mx c O cap (ge_bytes [k]) =
(ge_ctl c (Z.of_nat (length (key_text k))), ge_O c O (key_text k),
 ge_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length (key_text k)))).
Proof.
intros mx c O cap k. unfold ge_bytes. cbn [map concat app sl_sends]. unfold ge_ctl, ge_O, ge_cap.
rewrite rkb_sl_O_len. reflexivity.
Qed.

Lemma rkb_ge_O_len : forall c O x, Z.of_nat (length (ge_O c O x)) = ge_no c (Z.of_nat (length O)) (Z.of_nat (length x)).
Proof. intros c O x. unfold ge_O, ge_no. rewrite !rkb_sl_O_len. reflexivity. Qed.

(* ---- Section rkm: the meter lemmas over ANY meter M (the walk's MT, and the room round's counting meter MT_rk,
   W_contract_x.v); outside the Section each keeps its AR-walk name at MT through a local notation. ---- *)
Section rkm.
Variable M : ameter_ops.
Hypothesis HM : ameter_laws M.
(* -- the trace measures -- *)
Lemma rkb_tr_max_nonneg : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_max t.
Proof. intros t. unfold tr_max. induction t as [|e t IH]; cbn [fold_right]; [lia|]. destruct e; lia. Qed.

Lemma rkb_tr_app_g : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
tr_cost M (t1 ++ t2) = tr_cost M t1 + tr_cost M t2 /\ tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros t1 t2. pose proof (rkb_tr_max_nonneg t2) as H2. unfold tr_cost, tr_max in *.
induction t1 as [|e t1 IH]; cbn [app fold_right]; [split; lia|].
destruct IH as (IH1 & IH3). rewrite IH1, IH3. destruct e; split; lia.
Qed.

Lemma rkb_tr_free_g : forall n (a : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost M (RelayRunT.RFree n a :: t) = mo_free M + tr_cost M t /\ tr_max (RelayRunT.RFree n a :: t) = tr_max t.
Proof. intros n a t. unfold tr_cost, tr_max. cbn [fold_right]. split; lia. Qed.

Lemma rkb_sizes_cost_g : forall t, rk_sizes t -> 0 <= tr_cost M t.
Proof.
intros t H. unfold rk_sizes in H. unfold tr_cost.
pose proof (mo_free_nonneg M HM) as Hf.
induction H as [|e t He Ht IH]; cbn [fold_right]; [lia|].
destruct e as [n|n a|k n a]; cbv beta iota in He.
- pose proof (mo_malloc_nonneg M HM n He). lia.
- lia.
- pose proof (mo_malloc_nonneg M HM n He). lia.
Qed.

Lemma rkb_sizes_app : forall t1 t2, rk_sizes (t1 ++ t2) <-> rk_sizes t1 /\ rk_sizes t2.
Proof. intros t1 t2. unfold rk_sizes. apply Forall_app. Qed.

(* the sizes alone: the measures ignore the addresses *)
Definition rkb_er (e : RelayRunT.rev YO0i.sptr) : RelayRunT.rev YO0i.sptr :=
match e with
| RelayRunT.RMalloc n => RelayRunT.RMalloc n
| RelayRunT.RFree n _ => RelayRunT.RFree n ga0
| RelayRunT.RRealloc k n _ => RelayRunT.RRealloc k n ga0
end.

Lemma rkb_er_tr_g : forall t, tr_cost M (map rkb_er t) = tr_cost M t /\ tr_max (map rkb_er t) = tr_max t.
Proof.
intros t. unfold tr_cost, tr_max.
induction t as [|e t IH]; cbn [map fold_right]; [split; reflexivity|].
destruct IH as (I1 & I3). rewrite I1, I3. destruct e; cbn [rkb_er]; split; reflexivity.
Qed.

Lemma rkb_er_eq_g : forall t1 t2, map rkb_er t1 = map rkb_er t2 -> tr_cost M t1 = tr_cost M t2 /\ tr_max t1 = tr_max t2.
Proof.
intros t1 t2 E. destruct (rkb_er_tr_g t1) as (A1 & A3). destruct (rkb_er_tr_g t2) as (B1 & B3).
rewrite <- A1, <- A3, <- B1, <- B3, E. split; reflexivity.
Qed.

(* C3: the peak and the net change ignore the addresses too (W_tr_peak.v tr_sz_measures) *)
Lemma rkb_er_sz : forall t, tr_sz (map rkb_er t) = tr_sz t.
Proof.
induction t as [|e t IH]; [reflexivity|]. unfold tr_sz in *. cbn [map]. rewrite IH. destruct e; reflexivity.
Qed.

Lemma rkb_er_pn : forall t1 t2, map rkb_er t1 = map rkb_er t2 -> tr_peak t1 = tr_peak t2 /\ tr_net t1 = tr_net t2.
Proof.
intros t1 t2 E. assert (Es : tr_sz t1 = tr_sz t2) by (rewrite <- (rkb_er_sz t1), <- (rkb_er_sz t2), E; reflexivity).
destruct (tr_sz_measures t1 t2 Es) as (P & N & _). split; assumption.
Qed.

(* -- send_line's rounds -- *)
Lemma rkb_cost_head_g : forall cap C (o : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost M ((if cap =? 0 then RelayRunT.RMalloc C else RelayRunT.RRealloc cap C o) :: t) = mo_malloc M C + mo_free M + tr_cost M t.
Proof. intros. destruct (cap =? 0); reflexivity. Qed.

Lemma rkb_slr_cost_g : forall f mx no cap rem j o,
tr_cost M (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run M f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_cost_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + _); cbn [fst snd]; [|apply IH].
rewrite rkb_cost_head_g, IH. reflexivity.
Qed.

Lemma rkb_slr_sizes : forall f mx no cap rem j o, 0 <= mx -> 0 <= no -> rk_sizes (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
induction f as [|f IH]; intros mx no cap rem j o Hmx Hno; cbn [send_line_b_c.sl_run]; [constructor|].
destruct (rem <=? 0) eqn:Er; [constructor|]. apply Z.leb_gt in Er.
assert (Hn : 0 <= (if negb (mx =? 0) && (mx <? rem) then mx else rem)) by (destruct (negb (mx =? 0) && (mx <? rem)); lia).
destruct (cap <? no + _); cbn [fst snd].
- constructor; [destruct (cap =? 0); cbv beta iota; lia | apply IH; lia].
- apply IH; lia.
Qed.

Lemma rkb_slr_er : forall f mx no cap rem j o j' o',
map rkb_er (fst (send_line_b_c.sl_run f mx no cap rem j o)) = map rkb_er (fst (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [send_line_b_c.sl_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + _); cbn [fst snd map]; [|apply IH].
rewrite (IH mx _ _ _ (S j) (RelayRunT.Ret j) (S j') (RelayRunT.Ret j')). apply (f_equal (fun x => cons x _)).
destruct (cap =? 0); reflexivity.
Qed.

Lemma rkb_slcr_nonneg_g : forall f mx no cap rem, 0 <= cap -> 0 <= sl_cost_run M f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem Hc; cbn [sl_cost_run]; [lia|].
destruct (rem <=? 0); [lia|].
destruct (cap <? no + _) eqn:Eg; [apply Z.ltb_lt in Eg | apply IH; exact Hc].
pose proof (mo_free_nonneg M HM) as Hf.
match goal with |- context [mo_malloc M ?C] => pose proof (mo_malloc_nonneg M HM C ltac:(lia)) as Hm end.
match goal with |- context [sl_cost_run M f mx ?no2 ?c2 ?rem2] => pose proof (IH mx no2 c2 rem2 ltac:(lia)) as Hr end.
lia.
Qed.

Lemma rkb_sl_cap_ge : forall c mx no cap len, 0 <= cap -> cap <= sl_cap c mx no cap len.
Proof.
intros c mx no cap len Hc. rewrite sl_cap_fin. destruct (sl_live c len); [apply sl_fin_ge; exact Hc | lia].
Qed.

Lemma rkb_slt_cost_g : forall live mx no cap len j o,
tr_cost M (send_line_b_c.send_line_tr live mx no cap len j o) = if live then sl_cost_run M (Z.to_nat len) mx no cap len else 0.
Proof. intros. unfold send_line_b_c.send_line_tr. destruct live; [apply rkb_slr_cost_g | reflexivity]. Qed.

Lemma rkb_slt_sizes : forall live mx no cap len j o, 0 <= mx -> 0 <= no -> rk_sizes (send_line_b_c.send_line_tr live mx no cap len j o).
Proof. intros live mx no cap len j o Hmx Hno. unfold send_line_b_c.send_line_tr. destruct live; [apply rkb_slr_sizes; assumption | constructor]. Qed.

(* -- gesture_end -- *)
Lemma rkb_ge_tr_cost_g : forall c mx no cap xl, 0 < xl ->
tr_cost M (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = ge_cost M c mx no cap xl.
Proof.
intros c mx no cap xl Hxl.
unfold gesture_end_b_c.gesture_end_tr, ge_cost, sl_cost, sl_no, sl_cap.
rewrite (rkb_live_pos (sl_ctl c xl) 5 ltac:(lia)), rkb_live_ctl, (rkb_live_pos c xl Hxl).
cbv zeta. rewrite (proj1 (rkb_tr_app_g _ _)), !rkb_slt_cost_g.
destruct (sl_live c 1); reflexivity.
Qed.

Lemma rkb_ge_cost_nonneg_g : forall c mx no cap xl, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= ge_cost M c mx no cap xl.
Proof.
intros c mx no cap xl Hmx Hno Hcap. unfold ge_cost.
assert (H1 : 0 <= sl_cost M c mx no cap xl) by (unfold sl_cost; destruct (sl_live c xl); [apply rkb_slcr_nonneg_g; lia | lia]).
pose proof (rkb_sl_cap_ge c mx no cap xl Hcap) as Hc1.
assert (H2 : 0 <= sl_cost M (sl_ctl c xl) mx (sl_no c no xl) (sl_cap c mx no cap xl) 5)
  by (unfold sl_cost; destruct (sl_live (sl_ctl c xl) 5); [apply rkb_slcr_nonneg_g; lia | lia]).
lia.
Qed.

Lemma rkb_ge_cap_nonneg : forall c mx no cap xl, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= xl -> 0 <= ge_cap c mx no cap xl.
Proof.
intros c mx no cap xl Hmx Hno Hcap Hxl. unfold ge_cap.
pose proof (rkb_sl_cap_ge c mx no cap xl Hcap) as H1.
pose proof (rkb_sl_cap_ge (sl_ctl c xl) mx (sl_no c no xl) (sl_cap c mx no cap xl) 5 ltac:(lia)) as H2.
lia.
Qed.

Lemma rkb_ge_no_nonneg : forall c no xl, 0 <= no -> 0 <= xl -> 0 <= ge_no c no xl.
Proof.
intros c no xl Hno Hxl. unfold ge_no, sl_no.
destruct (sl_live c xl), (sl_live (sl_ctl c xl) 5); cbv beta iota; lia.
Qed.

Lemma rkb_ge_cap_le : forall c mx no cap xl, 0 <= cap -> cap <= ge_cap c mx no cap xl.
Proof.
intros c mx no cap xl Hcap. unfold ge_cap.
pose proof (rkb_sl_cap_ge c mx no cap xl Hcap) as H1.
pose proof (rkb_sl_cap_ge (sl_ctl c xl) mx (sl_no c no xl) (sl_cap c mx no cap xl) 5 ltac:(lia)) as H2.
lia.
Qed.

(* C3: gesture_end's net change of the live bytes is its growth of g_out (W_tr_peak.v ge_tr_net, at the walk's trace:
   the stream's liveness at one byte and the addresses ga0) *)
Lemma rkb_ge_net : forall c mx no cap xl, 0 < xl ->
tr_net (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = ge_cap c mx no cap xl - cap.
Proof.
intros c mx no cap xl Hxl. rewrite <- (rkb_live_pos c xl Hxl).
destruct (tr_sz_measures _ _ (gesture_end_tr_sz (sl_live c xl) mx no cap xl 0 ga0 0 RelayRunF.adr0)) as (_ & E & _).
rewrite E. exact (ge_tr_net c mx no cap xl ltac:(lia)).
Qed.

(* -- the run of key ends -- *)
Lemma rkb_ker_er : forall lv mx xks xks' no cap no' cap' j o j' o',
map fst xks = map fst xks' -> (lv = true -> no = no' /\ cap = cap') ->
map rkb_er (fst (keys_end_run lv mx no cap xks j o)) = map rkb_er (fst (keys_end_run lv mx no' cap' xks' j' o')).
Proof.
intros lv mx xks. induction xks as [|[xl ka] r IH]; intros [|[xl' ka'] r'] no cap no' cap' j o j' o' Ef Hl;
cbn [map fst] in Ef; try discriminate Ef; [reflexivity|].
injection Ef as <- Ef.
cbn [keys_end_run fst]. rewrite !map_app.
assert (EG : map rkb_er (gesture_end_b_c.gesture_end_tr lv mx no cap xl j o) = map rkb_er (gesture_end_b_c.gesture_end_tr lv mx no' cap' xl j' o')).
{ destruct lv; [destruct (Hl eq_refl) as [<- <-] | reflexivity].
  unfold gesture_end_b_c.gesture_end_tr, send_line_b_c.send_line_tr. cbv beta iota zeta. rewrite !map_app.
  rewrite (rkb_slr_er _ mx no cap xl j o j' o'). apply f_equal. apply rkb_slr_er. }
rewrite EG. apply f_equal. cbn [map rkb_er]. apply f_equal.
apply IH; [exact Ef|]. intros Hlv. destruct (Hl Hlv) as [<- <-]. split; reflexivity.
Qed.

Lemma rkb_ker_eq_g : forall lv mx xks no cap no' cap' j o j' o', (lv = true -> no = no' /\ cap = cap') ->
tr_cost M (fst (keys_end_run lv mx no cap xks j o)) = tr_cost M (fst (keys_end_run lv mx no' cap' xks j' o')) /\
tr_max (fst (keys_end_run lv mx no cap xks j o)) = tr_max (fst (keys_end_run lv mx no' cap' xks j' o')).
Proof. intros lv mx xks no cap no' cap' j o j' o' H. apply rkb_er_eq_g. apply rkb_ker_er; [reflexivity | exact H]. Qed.

Lemma rkb_ker_sizes : forall lv mx xks no cap j o, 0 <= mx -> 0 <= no -> Forall (fun x => 0 <= fst x) xks ->
rk_sizes (fst (keys_end_run lv mx no cap xks j o)).
Proof.
intros lv mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o Hmx Hno HF; cbn [keys_end_run fst]; [constructor|].
apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx.
apply rkb_sizes_app. split.
- unfold gesture_end_b_c.gesture_end_tr. cbv zeta. apply rkb_sizes_app. split; apply rkb_slt_sizes; lia.
- constructor; [exact I | apply IH; [exact Hmx | lia | exact HF]].
Qed.

Lemma rkb_ker_step_g : forall c mx no cap xl ka xks, 0 < xl ->
tr_cost M (fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0)) =
  ge_cost M c mx no cap xl + mo_free M +
  tr_cost M (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0)) /\
tr_max (fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0)) =
  Z.max (tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0))
    (tr_max (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0))).
Proof.
intros c mx no cap xl ka xks Hxl.
assert (HP : sl_live c 1 = true -> no + xl + 5 = ge_no c no xl /\ gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no cap xl = ge_cap c mx no cap xl).
{ intros Hlv. unfold ge_no, ge_cap, gesture_end_b_c.gesture_end_cap, sl_cap, sl_no.
  rewrite (rkb_live_pos (sl_ctl c xl) 5 ltac:(lia)), rkb_live_ctl, (rkb_live_pos c xl Hxl), Hlv.
  split; reflexivity. }
cbn [keys_end_run fst].
match goal with |- context [keys_end_run _ mx (no + xl + 5) _ xks ?j2 ?o2] =>
  destruct (rkb_ker_eq_g (sl_live c 1) mx xks (no + xl + 5) (gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no cap xl)
    (ge_no c no xl) (ge_cap c mx no cap xl) j2 o2 0%nat ga0 HP) as (E1 & E3);
  destruct (rkb_tr_free_g (xl + 1) ka
    (fst (keys_end_run (sl_live c 1) mx (no + xl + 5) (gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no cap xl) xks j2 o2)))
    as (F1 & F3) end.
rewrite (proj1 (rkb_tr_app_g _ _)), (proj2 (rkb_tr_app_g _ _)).
rewrite F1, F3, E1, E3, (rkb_ge_tr_cost_g c mx no cap xl Hxl).
split; [lia | reflexivity].
Qed.

(* C3: one key's run is its gesture_end, the free of the key, then the rest of the run at the next g_nout / g_capout,
   up to the addresses (the peak form's split: rkb_gbud_end, rkb_ge_room) *)
Lemma rkb_ker_split : forall c mx no cap xl ka xks, 0 < xl ->
exists T, fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0) =
  gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0 ++ RelayRunT.RFree (xl + 1) ka :: T /\
  map rkb_er T = map rkb_er (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0)).
Proof.
intros c mx no cap xl ka xks Hxl.
assert (HP : sl_live c 1 = true -> no + xl + 5 = ge_no c no xl /\ gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no cap xl = ge_cap c mx no cap xl).
{ intros Hlv. unfold ge_no, ge_cap, gesture_end_b_c.gesture_end_cap, sl_cap, sl_no.
  rewrite (rkb_live_pos (sl_ctl c xl) 5 ltac:(lia)), rkb_live_ctl, (rkb_live_pos c xl Hxl), Hlv.
  split; reflexivity. }
cbn [keys_end_run fst]. eexists. split; [reflexivity|].
apply rkb_ker_er; [reflexivity | exact HP].
Qed.

Lemma rkb_gkrest_nil : forall cx no cap, gkrest cx no cap [] = [].
Proof. intros. reflexivity. Qed.

Lemma rkb_gkrest_sizes : forall cx no cap Er, 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> rk_sizes (gkrest cx no cap Er).
Proof.
intros cx no cap Er Hmx Hno Hcap. unfold gkrest. apply rkb_ker_sizes; [exact Hmx | exact Hno|].
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (k & <- & _). cbn [fst]. lia.
Qed.

Lemma rkb_gkrest_step_g : forall cx c no cap k Er,
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
tr_cost M (gkrest cx no cap (k :: Er)) =
  ge_cost M c (gxmx cx) no cap (Z.of_nat (length (key_text k))) + mo_free M +
  tr_cost M (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er) /\
tr_max (gkrest cx no cap (k :: Er)) =
  Z.max (tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0))
    (tr_max (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
      (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er)).
Proof.
intros cx c no cap k Er Hl Hmx Hno Hcap Hxl.
unfold gkrest. rewrite <- Hl. cbn [map].
exact (rkb_ker_step_g c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0 _ Hxl).
Qed.

End rkm.
#[local] Notation rkb_tr_app := (rkb_tr_app_g MT).
#[local] Notation rkb_tr_free := (rkb_tr_free_g MT).
#[local] Notation rkb_er_tr := (rkb_er_tr_g MT).
#[local] Notation rkb_er_eq := (rkb_er_eq_g MT).
#[local] Notation rkb_cost_head := (rkb_cost_head_g MT).
#[local] Notation rkb_slr_cost := (rkb_slr_cost_g MT).
#[local] Notation rkb_slt_cost := (rkb_slt_cost_g MT).
#[local] Notation rkb_ge_tr_cost := (rkb_ge_tr_cost_g MT).
#[local] Notation rkb_ker_eq := (rkb_ker_eq_g MT).
#[local] Notation rkb_ker_step := (rkb_ker_step_g MT).
#[local] Notation rkb_gkrest_step := (rkb_gkrest_step_g MT).
#[local] Notation rkb_sizes_cost := (rkb_sizes_cost_g MT MLAW).
#[local] Notation rkb_slcr_nonneg := (rkb_slcr_nonneg_g MT MLAW).
#[local] Notation rkb_ge_cost_nonneg := (rkb_ge_cost_nonneg_g MT MLAW).
(* the counting meter MT_rk is lawful (W_relay_finish_h.v rfl_rk_laws) *)
Lemma rkm_rk_laws : ameter_laws MT_rk.
Proof. constructor; cbn [mo_ok mo_le mo_malloc mo_free MT_rk]; intros; solve [exact I | lia]. Qed.

(* ---- rkc: the live counts (ReplyCnt.acnt) across one key's end.  The count peak ignores the addresses (as the
   cost does, rkb_er_tr); a round chain of send_line from cap >= 0 grows g_out only, so its net count is EXACTLY the
   change of g_out's own count (cphi, W_tr_cnt.v; tc_chain there gives one direction); gesture_end's two sends are such
   chains; g_out's block counts cphi P cap; the free of a block of size n lowers the count by zb (P n). ---- *)
(* the count peak of a free, as a rewrite (cbn would leave the fixpoint open) *)
Lemma rkc_peakP_free : forall P kz (ka : RelayRunT.addr YO0i.sptr) (r : list (RelayRunT.rev YO0i.sptr)),
  ReplyCnt.tr_peakP P (RelayRunT.RFree kz ka :: r) = Z.max 0 (ReplyCnt.tr_peakP P r - ReplyCnt.zb (P kz)).
Proof. reflexivity. Qed.
(* the peak of a key's run: gesture_end's trace, the key's free, then the rest - at least the net of the first plus
   the peak of the rest less the freed block's count *)
Lemma rkc_peak_split : forall P (A T G : list (RelayRunT.rev YO0i.sptr)) kz (ka : RelayRunT.addr YO0i.sptr),
  tr_netP P A + ReplyCnt.tr_peakP P (T ++ G) - ReplyCnt.zb (P kz) <=
  ReplyCnt.tr_peakP P (A ++ RelayRunT.RFree kz ka :: (T ++ G)).
Proof.
  intros P A T G kz ka.
  rewrite (tr_peakP_app _ P A (RelayRunT.RFree kz ka :: (T ++ G))), rkc_peakP_free. lia.
Qed.
Lemma rkc_er_peakP : forall P (t : list (RelayRunT.rev YO0i.sptr)), ReplyCnt.tr_peakP P (map rkb_er t) = ReplyCnt.tr_peakP P t.
Proof. intros P t. induction t as [|e t IH]; [reflexivity|]. destruct e; cbn [map rkb_er ReplyCnt.tr_peakP]; rewrite IH; reflexivity. Qed.

Lemma rkc_slr_net : forall P f mx no cap rem j o, 0 <= cap ->
tr_netP P (fst (send_line_b_c.sl_run f mx no cap rem j o)) =
  cphi P (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))) - cphi P cap.
Proof.
intros P f. induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
- cbn [fst snd]. unfold tr_netP, ReplyTrPeakW.tr_net_w. cbn [fold_right]. lia.
- destruct (rem <=? 0); [cbn [fst snd]; unfold tr_netP, ReplyTrPeakW.tr_net_w; cbn [fold_right]; lia|].
  match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
  destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; cbv beta iota; [|apply IH; exact Hc].
  cbn [fst snd].
  pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as I.
  destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota; rewrite tr_netP_cons, I; cbv beta iota.
  + subst cap. rewrite cphi_0, (cphi_nz P ((no + n) * 2)) by lia. lia.
  + rewrite (cphi_nz P cap E), (cphi_nz P ((no + n) * 2)) by lia. lia.
Qed.

Lemma rkc_send_net : forall P live mx no cap len j o, 0 <= cap ->
tr_netP P (send_line_b_c.send_line_tr live mx no cap len j o) =
  cphi P (send_line_b_c.send_line_cap live mx no cap len) - cphi P cap.
Proof.
intros P live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
destruct live; [|unfold tr_netP, ReplyTrPeakW.tr_net_w; cbn [fold_right]; lia].
pose proof (rkc_slr_net P (Z.to_nat len) mx no cap len j o Hc) as H.
rewrite sl_run_fin in H. rewrite sl_run_fin. exact H.
Qed.

Lemma rkc_gend_net : forall P live mx no cap xl j o, 0 <= cap ->
tr_netP P (gesture_end_b_c.gesture_end_tr live mx no cap xl j o) =
  cphi P (gesture_end_b_c.gesture_end_cap live mx no cap xl) - cphi P cap.
Proof.
intros P live mx no cap xl j o Hc. unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap. cbv zeta.
pose proof (tc_chain_nonneg _ _ _ _ _ (tc_send P live mx no cap xl j o Hc)) as Hn.
rewrite tr_netP_app, (rkc_send_net P live mx no cap xl j o Hc). rewrite rkc_send_net by exact Hn. lia.
Qed.

(* gesture_end's count change at the walk's trace (liveness at one byte, addresses ga0) *)
Lemma rkc_ge_netP : forall P c mx no cap xl, 0 < xl -> 0 <= cap ->
tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = cphi P (ge_cap c mx no cap xl) - cphi P cap.
Proof.
intros P c mx no cap xl Hxl Hcap. rewrite <- (rkb_live_pos c xl Hxl), (ge_cap_tr c mx no cap xl ltac:(lia)).
exact (rkc_gend_net P (sl_live c xl) mx no cap xl 0 ga0 Hcap).
Qed.

Lemma rkc_cphi_out : forall P cap out, Z.of_nat (ReplyCnt.acnt P (aout_blks cap out)) = cphi P cap.
Proof.
intros P cap out. unfold aout_blks, cphi. destruct (cap =? 0); [reflexivity|].
unfold ReplyCnt.acnt, ReplyCnt.zb. cbn [map snd List.filter]. destruct (P cap); reflexivity.
Qed.

Lemma rkc_cnt_out : forall P ly1 S1 ly2 S2 cap out cap' out' rest,
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) = Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) - cphi P cap + cphi P cap'.
Proof.
intros P ly1 S1 ly2 S2 cap out cap' out' rest P1 P2.
rewrite (ReplyCnt.acnt_perm P _ _ P1), (ReplyCnt.acnt_perm P _ _ P2), !ReplyCnt.acnt_app, !Nat2Z.inj_add, !rkc_cphi_out.
lia.
Qed.

Lemma rkc_cnt_out_le : forall P ly1 S1 ly2 S2 cap out cap' out' rest,
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
(ReplyCnt.acnt P (ablocks B ly2 S2) <= ReplyCnt.acnt P (ablocks B ly1 S1) + 1)%nat.
Proof.
intros P ly1 S1 ly2 S2 cap out cap' out' rest P1 P2.
pose proof (rkc_cnt_out P ly1 S1 ly2 S2 cap out cap' out' rest P1 P2) as E.
pose proof (cphi_bounds P cap). pose proof (cphi_bounds P cap'). lia.
Qed.

Lemma rkc_cnt_free : forall P ly2 S2 ly3 S3 l1 l2 pa n,
ablocks B ly2 S2 = l1 ++ (pa, n) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) = Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) - ReplyCnt.zb (P n).
Proof.
intros P ly2 S2 ly3 S3 l1 l2 pa n E2 E3. rewrite E2, E3, !ReplyCnt.acnt_app, acnt_cons, !Nat2Z.inj_add.
unfold ReplyCnt.zb. cbn [snd]. destruct (P n); lia.
Qed.

(* one key's end: gesture_end (g_out from cap to its ge_cap) then the free of the key's block (|k| + 1) *)
Lemma rkc_end_cnt : forall P c mx no cap xl ly1 S1 ly2 S2 ly3 S3 out out' rest l1 l2 pa,
0 < xl -> 0 <= cap ->
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap xl) out' ++ rest) ->
ablocks B ly2 S2 = l1 ++ (pa, xl + 1) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
  tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) - ReplyCnt.zb (P (xl + 1)).
Proof.
intros P c mx no cap xl ly1 S1 ly2 S2 ly3 S3 out out' rest l1 l2 pa Hxl Hcap P1 P2 E2 E3.
rewrite (rkc_cnt_free P ly2 S2 ly3 S3 l1 l2 pa (xl + 1) E2 E3), (rkc_cnt_out P ly1 S1 ly2 S2 cap out _ out' rest P1 P2),
  (rkc_ge_netP P c mx no cap xl Hxl Hcap).
lia.
Qed.

(* -- the drain's and the table run's requests ask nonnegative sizes -- *)
Lemma rkb_grow_ok : forall cap used j b, 0 <= cap ->
rk_sizes (fst (drain_b_c.grow_tr cap used j b)) /\ 0 <= fst (snd (drain_b_c.grow_tr cap used j b)).
Proof.
intros cap used j b Hc. unfold drain_b_c.grow_tr.
destruct (cap - used <? 4096); cbn [fst snd]; [|split; [constructor | exact Hc]].
destruct (Z.eqb_spec cap 0); cbn [fst snd]; (split; [constructor; [cbv beta iota; lia | constructor] | lia]).
Qed.

Lemma rkb_seen_sizes : forall H ka l j ha ks, rk_sizes (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
intros H ka l j ha ks. unfold drain_b_c.seen_tr.
lazymatch goal with |- context [match ?t with Some _ => _ | None => _ end] => destruct t as [[g x]|] end;
[destruct g; lazymatch goal with |- context [match ?t with Some _ => _ | None => _ end] => destruct t end|];
cbn [fst].
- constructor.
- constructor; [destruct (ka =? 0); cbv beta iota; lia | constructor; [cbv beta iota; lia | constructor]].
- constructor; [exact I | constructor].
- constructor.
- constructor.
Qed.

Lemma rkb_lines_sizes : forall live mx ls no cap H ka j o ha ks, 0 <= mx -> 0 <= no ->
rk_sizes (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))).
Proof.
intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks Hmx Hno; cbn [drain_b_c.lines_run fst]; [constructor|].
apply rkb_sizes_app. split; [apply rkb_slt_sizes; lia|].
apply rkb_sizes_app. split; [apply rkb_seen_sizes | apply IH; lia].
Qed.

Lemma rkb_push_ok : forall ls n cap j v rs, 0 <= cap ->
rk_sizes (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\ 0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)).
Proof.
induction ls as [|l ls IH]; intros n cap j v rs Hc; cbn [drain_b_c.pushes_run fst snd]; [split; [constructor | exact Hc]|].
assert (Hc' : 0 <= drain_b_c.push_cap n cap) by (unfold drain_b_c.push_cap; destruct (n =? cap), (cap =? 0); cbv beta iota; lia).
match goal with |- context [drain_b_c.pushes_run (n + 1) _ ls ?j1 ?v1 ?rs1] =>
  destruct (IH (n + 1) (drain_b_c.push_cap n cap) j1 v1 rs1 Hc') as [I1 I2] end.
split; [|exact I2]. apply rkb_sizes_app. split; [|exact I1].
unfold ListTr.list_push_tra. apply rkb_sizes_app. split; [|constructor; [cbv beta iota; lia | constructor]].
destruct (n =? cap); [|constructor]. destruct (Z.eqb_spec cap 0); (constructor; [cbv beta iota; lia | constructor]).
Qed.

Definition rkb_dsok (s : drain_b_c.dstate) : Prop :=
0 <= drain_b_c.ds_cap s /\ 0 <= drain_b_c.ds_ecap s /\ 0 <= drain_b_c.ds_no s.

Lemma rkb_drain_ok : forall f live mx s j a, 0 <= mx -> rkb_dsok s ->
rk_sizes (fst (drain_b_c.drain_run f live mx s j a)) /\ rkb_dsok (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
induction f as [|f IH]; intros live mx s j a Hmx Hs; [split; [constructor | exact Hs]|].
cbn [drain_b_c.drain_run].
pose proof Hs as (Hc & He & Hn).
pose proof (rkb_grow_ok (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Hc) as HG.
destruct (drain_b_c.grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a))
  as [tg [cg bg]].
cbn [fst snd] in HG |- *. destruct HG as [Hg Hgc].
destruct (drain_b_c.ds_eintr s).
- match goal with |- context [drain_b_c.drain_run f live mx ?s1 ?j1 ?a1] =>
    assert (Hs1 : rkb_dsok s1) by (unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia);
    destruct (IH live mx s1 j1 a1 Hmx Hs1) as [H1 H2] end.
  cbn [fst snd]. split; [apply rkb_sizes_app; split; assumption | exact H2].
- destruct (drain_b_c.ds_pend s) as [|r0 rs]; cbn [fst snd].
  + split; [exact Hg | unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia].
  + destruct (Z.min _ _ <=? 0); cbn [fst snd].
    * split; [exact Hg | unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia].
    * destruct (RelayModel.chunk _ _ _) as [[u' sk'] rl].
      match goal with |- context [drain_b_c.pushes_run ?n0 ?c0 ?ls0 ?j0 ?v0 ?rs0] =>
        destruct (rkb_push_ok ls0 n0 c0 j0 v0 rs0 He) as [Hp1 Hp2] end.
      match goal with |- context [drain_b_c.lines_run ?lv0 ?mx0 ?no0 ?cap0 ?H0 ?ka0 ?ls0 ?j0 ?o0 ?ha0 ?ks0] =>
        pose proof (rkb_lines_sizes lv0 mx0 ls0 no0 cap0 H0 ka0 j0 o0 ha0 ks0 Hmx Hn) as Hl;
        destruct (snd (fst (drain_b_c.lines_run lv0 mx0 no0 cap0 H0 ka0 ls0 j0 o0 ha0 ks0))) as [[oc' H'] ka'];
        destruct (snd (drain_b_c.lines_run lv0 mx0 no0 cap0 H0 ka0 ls0 j0 o0 ha0 ks0)) as [[o' ha'] ks'] end.
      cbn [fst snd].
      match goal with |- context [drain_b_c.drain_run f live mx ?s1 ?j1 ?a1] =>
        assert (Hs1 : rkb_dsok s1) by (unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia);
        destruct (IH live mx s1 j1 a1 Hmx Hs1) as [H1 H2] end.
      split; [|exact H2].
      repeat (apply rkb_sizes_app; split); try assumption.
      match goal with |- rk_sizes (if ?b then _ else _) => destruct b end; [constructor; [exact I | constructor] | constructor].
Qed.

Lemma rkb_fold5_nonneg : forall (l : list (list Z * RelayRunT.addr YO0i.sptr)),
0 <= fold_right (fun xl acc => xl + 5 + acc) 0 (map fst (map (fun x => (Z.of_nat (length (fst x)), snd x)) l)).
Proof. induction l as [|x l IH]; cbn [map fold_right fst]; lia. Qed.

Lemma rkb_xks_nonneg : forall (l : list (list Z * RelayRunT.addr YO0i.sptr)),
Forall (fun x => 0 <= fst x) (map (fun x => (Z.of_nat (length (fst x)), snd x)) l).
Proof. induction l as [|x l IH]; cbn [map]; constructor; [cbn [fst]; lia | exact IH]. Qed.

Lemma rkb_gone_sizes : forall lv mx pre ps no cap nm j o, 0 <= mx -> 0 <= no ->
Forall (fun p => re_eof (fst p) = 0 -> 0 <= re_cap (fst p) /\ 0 <= hl_cap (hs_expected (fst (snd p)))) ps ->
rk_sizes (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))).
Proof.
intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o Hmx Hno HF; [constructor|].
apply Forall_cons_iff in HF as [He HF]. cbn [fst snd] in He.
assert (Hinit : re_eof e = 0 -> rkb_dsok (drain_b_c.drain_init no cap e (fst hj))).
{ intros E. destruct (He E) as [H1 H2]. unfold rkb_dsok, drain_b_c.drain_init.
  cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]. lia. }
assert (Hs : 0 <= drain_b_c.ds_no (relay_remove_b_c.after_drain lv mx no cap e (fst hj))).
{ unfold relay_remove_b_c.after_drain. destruct (Z.eqb_spec (re_eof e) 0) as [E|E].
  - unfold drain_b_c.drain_fin, drain_b_c.drain_go.
    destruct (rkb_drain_ok (S (S (length (pending_stream (fst hj))))) lv mx (drain_b_c.drain_init no cap e (fst hj))
      0%nat drain_b_c.dadr0 Hmx (Hinit E)) as [_ (_ & _ & H3)]. exact H3.
  - unfold drain_b_c.drain_init. cbn [drain_b_c.ds_no]. exact Hno. }
cbn [relay_instance_gone_b_c.gone_run].
match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?no2 ?cap2 pre r nm ?j2 ?o2] =>
  assert (Hno2 : 0 <= no2) by (match goal with |- context [map fst (map ?F ?L)] => pose proof (rkb_fold5_nonneg L) end; lia);
  pose proof (IH no2 cap2 nm j2 o2 Hmx Hno2 HF) as IH2; revert IH2;
  destruct (relay_instance_gone_b_c.gone_run lv mx no2 cap2 pre r nm j2 o2) as [[[t c] ss] [o' das]]; intros IH2 end.
cbn [fst] in IH2 |- *.
apply rkb_sizes_app. split; [|apply rkb_sizes_app; split; [|exact IH2]].
- destruct (Z.eqb_spec (re_eof e) 0) as [E|E]; [|constructor].
  unfold drain_b_c.drain_tr, drain_b_c.drain_go. exact (proj1 (rkb_drain_ok _ _ _ _ _ _ Hmx (Hinit E))).
- apply rkb_ker_sizes; [exact Hmx | exact Hs | apply rkb_xks_nonneg].
Qed.

Lemma rkb_forall_skipn : forall {X Y : Type} (P : X * Y -> Prop) i (l1 : list X) (l2 : list Y),
Forall P (combine l1 l2) -> Forall P (combine (skipn i l1) (skipn i l2)).
Proof.
intros X Y P i. induction i as [|i IH]; intros l1 l2 H; [exact H|].
destruct l1 as [|x l1], l2 as [|y l2]; cbn [skipn combine]; [constructor | constructor | |].
- rewrite combine_nil. constructor.
- apply Forall_cons_iff in H as [_ H]. apply IH. exact H.
Qed.

Lemma rkb_gbase_facts : forall cx, GBASE B ARx MT RP MMAX RG cx ->
0 <= gxmx cx <= 255 /\
Forall (fun p => re_eof (fst p) = 0 -> 0 <= re_cap (fst p) /\ 0 <= hl_cap (hs_expected (fst (snd p))))
  (combine (gxes cx) (gxhs cx)) /\
mo_ok MT (gxS cx) (tr_cost MT (gtr cx)).
Proof.
intros cx HB.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & Har & Hout & _ & _ & Hsrc & _ & _ & _ & _ & Hok & _ & _).
split; [|split; [|exact Hok]].
- destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmx & _).
  exact Hmx.
- destruct Har as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hent & _).
  unfold gps in Hsrc. apply Forall_forall. intros [e [h j]] Hp Heof. cbn [fst snd] in Heof |- *.
  split.
  + pose proof (in_combine_l _ _ _ _ Hp) as He. rewrite Forall_forall in Hent. specialize (Hent e He).
    destruct Hent as (_ & _ & _ & _ & _ & Hcap & _). lia.
  + rewrite Forall_forall in Hsrc. specialize (Hsrc _ Hp Heof). cbn [fst snd] in Hsrc.
    destruct Hsrc as (_ & Has & _).
    destruct Has as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hex & _).
    destruct Hex as (_ & _ & _ & _ & _ & [(Hc & _) | (Hc & _)] & _); lia.
Qed.

Lemma rkb_grest_sizes : forall cx i no cap, GBASE B ARx MT RP MMAX RG cx -> 0 <= no -> 0 <= cap -> rk_sizes (grest cx i no cap).
Proof.
intros cx i no cap HB Hno Hcap.
destruct (rkb_gbase_facts cx HB) as (Hmx & HF & _).
unfold grest, relay_instance_gone_b_c.relay_instance_gone_tr.
apply rkb_gone_sizes; [lia | exact Hno | apply rkb_forall_skipn; exact HF].
Qed.

(* -- the meter and the budget -- *)
Lemma rkb_mok : forall cx ly1 S1 spent tl c, GBASE B ARx MT RP MMAX RG cx -> gbud B MT RP MMAX cx ly1 S1 spent tl -> 0 <= c ->
c <= tr_cost MT tl -> mo_ok MT S1 c.
Proof.
intros cx ly1 S1 spent tl c HB (Hle & Hsp & Hc & _) Hc0 Hct.
destruct (rkb_gbase_facts cx HB) as (_ & _ & Hok).
exact (mok_station MT (gxS cx) S1 (tr_cost MT (gtr cx)) spent c MLAW Hok Hle Hc0 ltac:(lia)).
Qed.

(* gbud after one key's end: the meter and the bytes as C3 left them; the room is the free's post (HRM3: the room the
   requests after the key owe, on top of gxkr); the counts from the key's count change HCN3 (gesture_end's net count
   less the freed key) against the peak's split tr_peakP (ge ++ RFree :: rest) >= net ge - zb + tr_peakP rest *)
Lemma rkb_gbud_end : forall cx ly1 S1 ly3 S3 spent c no cap k Er G,
gbud B MT RP MMAX cx ly1 S1 spent (gkrest cx no cap (k :: Er) ++ G) ->
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
mo_le MT S1 S3 (ge_cost MT c (gxmx cx) no cap (Z.of_nat (length (key_text k))) + mo_free MT) ->
blocks_bytes S3 <= blocks_bytes S1 +
  tr_net (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) -
  (Z.of_nat (length (key_text k)) + 1) ->
rp_RM RP S3 (Z.to_nat (tr_cost MT_rk (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G)) + gxkr cx) ->
(forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
  tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) -
  ReplyCnt.zb (P (Z.of_nat (length (key_text k)) + 1))) ->
gbud B MT RP MMAX cx ly3 S3 (spent + (ge_cost MT c (gxmx cx) no cap (Z.of_nat (length (key_text k))) + mo_free MT))
  (gkrest cx (ge_no c no (Z.of_nat (length (key_text k)))) (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G).
Proof.
intros cx ly1 S1 ly3 S3 spent c no cap k Er G (Hle & Hsp & Hc & Ha & Hm & Hrm & Hcn) Hl Hmx Hno Hcap Hxl Hle3 Hbb HRM3 HCN3.
(* the peak: the run is the key's gesture_end, its free, then the rest (rkb_ker_split) *)
assert (Hp : blocks_bytes S3 + tr_peak (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G) <= LIVE_MAX).
{ unfold gkrest in Ha |- *. rewrite <- Hl in Ha |- *. cbn [map] in Ha.
  destruct (rkb_ker_split c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0
    (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er) Hxl) as (T & ET & EM).
  rewrite ET, <- app_assoc, <- app_comm_cons, tr_peak_app, tr_peak_free, tr_peak_app in Ha.
  rewrite tr_peak_app. destruct (rkb_er_pn _ _ EM) as (P1 & N1). rewrite P1, N1 in Ha.
  lia. }
(* the count peak, split the same way *)
assert (HK : forall P, ReplyCnt.tr_peakP P (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G) +
  tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) -
  ReplyCnt.zb (P (Z.of_nat (length (key_text k)) + 1)) <= ReplyCnt.tr_peakP P (gkrest cx no cap (k :: Er) ++ G)).
{ intros P. unfold gkrest. rewrite <- Hl. cbn [map].
  destruct (rkb_ker_split c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0
    (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er) Hxl) as (T & ET & EM).
  rewrite ET, <- app_assoc, <- app_comm_cons.
  set (R := fst (keys_end_run (sl_live c 1) (gxmx cx) (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er)
    0 ga0)) in *.
  assert (EP : ReplyCnt.tr_peakP P (T ++ G) = ReplyCnt.tr_peakP P (R ++ G))
    by (rewrite <- (rkc_er_peakP P (T ++ G)), <- (rkc_er_peakP P (R ++ G)), !map_app, EM; reflexivity).
  rewrite <- EP.
  pose proof (rkc_peak_split P
    (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0)
    T G (Z.of_nat (length (key_text k)) + 1) ga0).
  lia. }
destruct (rkb_gkrest_step cx c no cap k Er Hl Hmx Hno Hcap Hxl) as (E1 & E3).
destruct (rkb_tr_app (gkrest cx no cap (k :: Er)) G) as (A1 & A3).
destruct (rkb_tr_app (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er) G) as (B1 & B3).
pose proof (rkb_ge_cost_nonneg c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap) as Hg.
pose proof (mo_free_nonneg MT MLAW) as Hf.
rewrite A1, E1 in Hc. rewrite A3, E3 in Hm.
unfold gbud. rewrite B1, B3.
refine (conj (mo_le_trans MT MLAW _ _ _ _ _ Hle Hle3) (conj _ (conj _ (conj _ (conj _ (conj HRM3 _)))))); [lia | lia | lia | lia |].
apply (cnt_ok_pk_mono RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P (gkrest cx no cap (k :: Er) ++ G)) + 3)%nat) _
  (ablocks B ly1 S1) _); [|exact Hcn].
intros P. pose proof (HK P) as H1. pose proof (HCN3 P) as H2.
pose proof (ReplyCnt.tr_peakP_nonneg _ P (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G)) as H3.
pose proof (ReplyCnt.tr_peakP_nonneg _ P (gkrest cx no cap (k :: Er) ++ G)) as H4.
cbv beta. lia.
Qed.

Lemma rkb_ge_room : forall cx ly1 S1 spent c no cap k Er G,
gbud B MT RP MMAX cx ly1 S1 spent (gkrest cx no cap (k :: Er) ++ G) -> rk_sizes G ->
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) < MMAX /\
blocks_bytes S1 + tr_peak (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) <= LIVE_MAX /\
ge_cost MT c (gxmx cx) no cap (Z.of_nat (length (key_text k))) + mo_free MT <= tr_cost MT (gkrest cx no cap (k :: Er) ++ G).
Proof.
intros cx ly1 S1 spent c no cap k Er G (Hle & Hsp & Hc & Ha & Hm & _) HG Hl Hmx Hno Hcap Hxl.
(* the room: gesture_end's trace is the remaining trace's prefix (rkb_ker_split) *)
assert (Hp : blocks_bytes S1 + tr_peak (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) <= LIVE_MAX).
{ unfold gkrest in Ha. rewrite <- Hl in Ha. cbn [map] in Ha.
  destruct (rkb_ker_split c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0
    (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er) Hxl) as (T & ET & _).
  rewrite ET, <- app_assoc, tr_peak_app in Ha. lia. }
destruct (rkb_gkrest_step cx c no cap k Er Hl Hmx Hno Hcap Hxl) as (E1 & E3).
destruct (rkb_tr_app (gkrest cx no cap (k :: Er)) G) as (A1 & A3).
rewrite A1, E1. rewrite A3, E3 in Hm.
pose proof (rkb_sizes_cost _ HG) as HG1.
pose proof (rkb_sizes_cost _ (rkb_gkrest_sizes cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er Hmx
  (rkb_ge_no_nonneg c no (Z.of_nat (length (key_text k))) Hno ltac:(lia))
  (rkb_ge_cap_nonneg c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap ltac:(lia))))
  as HK1.
split; [lia|]. split; [exact Hp | lia].
Qed.

(* the room gesture_end and the free get from gbud: gbud's budget at the key is exactly gesture_end's MT_rk charge, the
   free's 1, then the room the requests after the key owe on top of gxkr (MT_rk is lawful, so every charge is >= 0) *)
Lemma rkb_ge_rm : forall cx ly1 S1 spent c no cap k Er G,
gbud B MT RP MMAX cx ly1 S1 spent (gkrest cx no cap (k :: Er) ++ G) -> rk_sizes G ->
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
rp_RM RP S1 (Z.to_nat (ge_cost MT_rk c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) +
  S (Z.to_nat (tr_cost MT_rk (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G)) + gxkr cx)).
Proof.
intros cx ly1 S1 spent c no cap k Er G (_ & _ & _ & _ & _ & Hrm & _) HG Hl Hmx Hno Hcap Hxl.
destruct (rkb_gkrest_step_g MT_rk cx c no cap k Er Hl Hmx Hno Hcap Hxl) as (E1 & _).
destruct (rkb_tr_app_g MT_rk (gkrest cx no cap (k :: Er)) G) as (A1 & _).
destruct (rkb_tr_app_g MT_rk (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er) G) as (B1 & _).
pose proof (rkb_ge_cost_nonneg_g MT_rk rkm_rk_laws c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap) as Hg.
pose proof (rkb_sizes_cost_g MT_rk rkm_rk_laws _ HG) as HG1.
pose proof (rkb_sizes_cost_g MT_rk rkm_rk_laws _ (rkb_gkrest_sizes cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er Hmx
  (rkb_ge_no_nonneg c no (Z.of_nat (length (key_text k))) Hno ltac:(lia))
  (rkb_ge_cap_nonneg c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap ltac:(lia))))
  as HK1.
rewrite A1, E1 in Hrm. rewrite B1.
refine (@eq_ind _ _ (rp_RM RP S1) Hrm _ _).
replace (mo_free MT_rk) with 1 by reflexivity. lia.
Qed.

(* the requests still owed at RGI (GIN's last conjunct, the let named): the rest of entry i's key run from index n
   over ks (fuel f), then the entries after i *)
Definition rk_tl (cx : gcx) (i n : nat) (ks : list (Z * list byte * list byte)) (f : nat) (c2 : ctl) (O2 : list byte)
  (cap2 : Z) :=
let Er := fst (geik_loop f (gpre cx) n ks) in
let '(_, O3, cap3) := sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes Er) in
gkrest cx (Z.of_nat (length O2)) cap2 Er ++ grest cx (S i) (Z.of_nat (length O3)) cap3.
(* the room the requests after ending key n owe on top of gxkr: at the next RGI (key n gone, ks swap-removed, the
   stream after the key's gesture_end), which the free's post must leave *)
Definition rk_krn (cx : gcx) (i n : nat) (ks : list (Z * list byte * list byte)) (f : nat) (c2 : ctl) (O2 : list byte)
  (cap2 : Z) : nat :=
(Z.to_nat (tr_cost MT_rk (rk_tl cx i n (swap_remove (0%Z, [], []) n ks) (Nat.pred f)
   (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0%Z, [], []))))))
   (ge_O c2 O2 (key_text (nth n ks (0%Z, [], []))))
   (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0%Z, [], [])))))))) +
 gxkr cx)%nat.

(* -- the live bytes -- *)
Lemma rkb_bb_out : forall ly1 S1 ly2 S2 cap out cap' out' rest,
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
0 <= cap <= cap' -> blocks_bytes S2 = blocks_bytes S1 - cap + cap'.
Proof.
intros ly1 S1 ly2 S2 cap out cap' out' rest P1 P2 Hc.
rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ P1), (bsum_perm _ _ P2), !bsum_app.
unfold aout_blks. destruct (Z.eqb_spec cap 0), (Z.eqb_spec cap' 0); rewrite ?bsum_cons; unfold bsum; cbn [fold_right snd]; lia.
Qed.

Lemma rkb_bb_free : forall ly2 S2 ly3 S3 l1 l2 pa n,
ablocks B ly2 S2 = l1 ++ (pa, n) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 -> blocks_bytes S3 = blocks_bytes S2 - n.
Proof.
intros ly2 S2 ly3 S3 l1 l2 pa n E2 E3.
rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly3 S3), E2, E3, !bsum_app, bsum_cons. cbn [snd]. lia.
Qed.

(* -- gestures_end_instance's loop, one step at a time -- *)
Lemma rkb_geik_pass : forall f pre n ks, (n < length ks)%nat ->
has_prefix pre (bzs (key_text (nth n ks (0, [], [])))) = false ->
geik_loop (S f) pre n ks = geik_loop f pre (S n) ks.
Proof.
intros f pre n ks Hn Hp. cbn [geik_loop]. rewrite (proj2 (Nat.ltb_lt n (length ks)) Hn), Hp. reflexivity.
Qed.

Lemma rkb_geik_end : forall f pre n ks, (n < length ks)%nat ->
has_prefix pre (bzs (key_text (nth n ks (0, [], [])))) = true ->
geik_loop (S f) pre n ks =
(nth n ks (0, [], []) :: fst (geik_loop f pre n (swap_remove (0, [], []) n ks)),
 snd (geik_loop f pre n (swap_remove (0, [], []) n ks))).
Proof.
intros f pre n ks Hn Hp. cbn [geik_loop]. rewrite (proj2 (Nat.ltb_lt n (length ks)) Hn), Hp.
destruct (geik_loop f pre n (swap_remove (0, [], []) n ks)) as [E K]. reflexivity.
Qed.

Lemma rkb_geik_done : forall f pre n ks, (length ks <= n)%nat -> geik_loop f pre n ks = ([], ks).
Proof.
intros f pre n ks H. destruct f as [|f]; cbn [geik_loop]; [reflexivity|].
rewrite (proj2 (Nat.ltb_ge n (length ks)) H). reflexivity.
Qed.

(* -- list facts for the entry's exit -- *)
Lemma rkb_gbase_len : forall cx, GBASE B ARx MT RP MMAX RG cx -> length (gxhs cx) = length (gxes cx).
Proof. intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _). exact HL. Qed.

Lemma rkb_firstn_snoc : forall {X : Type} (l : list X) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros X l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia; cbn [firstn nth app]; [reflexivity|].
rewrite (IH i d ltac:(lia)). reflexivity.
Qed.

Lemma rkb_combine_app : forall {X Y : Type} (l1 : list X) (l2 : list Y) l1' l2', length l1 = length l2 ->
combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] l1' l2' H; cbn [length] in H; try discriminate H;
cbn [app combine]; [reflexivity|].
rewrite IH by lia. reflexivity.
Qed.

Lemma rkb_gdone_snoc : forall ps qd e (hj : hsrc * nat) e' (h' : hsrc), length ps = length qd ->
gdone_srcs (ps ++ [(e, hj)]) (qd ++ [(e', h')]) = gdone_srcs ps qd ++ (if re_eof e =? 0 then asrc_blks h' else []).
Proof.
intros ps qd e hj e' h' H. unfold gdone_srcs. rewrite (rkb_combine_app _ _ _ _ H), map_app, concat_app.
cbn [combine map concat fst snd]. rewrite app_nil_r. reflexivity.
Qed.

Lemma rkb_rel_app : forall pre mx ps qs ps2 qs2 c O cap c' O' cap' c2 O2 cap2,
rig_rel pre mx c O cap ps qs c' O' cap' -> rig_rel pre mx c' O' cap' ps2 qs2 c2 O2 cap2 ->
rig_rel pre mx c O cap (ps ++ ps2) (qs ++ qs2) c2 O2 cap2.
Proof.
intros pre mx ps. induction ps as [|[e [h j]] r IH];
intros [|[e' h'] q] ps2 qs2 c O cap c' O' cap' c2 O2 cap2 H1 H2; cbn [rig_rel app] in H1 |- *; try contradiction.
- destruct H1 as (E1 & E2 & E3). subst c' O' cap'. exact H2.
- destruct H1 as (e1 & ev & LB & H1). exists e1, ev, LB. cbv zeta in H1 |- *.
  destruct H1 as (Ha & Hb & Hc). split; [exact Ha|]. split; [exact Hb|].
  revert Hc. destruct (sl_sends _ _ _ _ _) as [[c3 O3] cap3]. intros Hc.
  eapply IH; [exact Hc | exact H2].
Qed.

Lemma rkb_rel_one : forall pre mx cB OB capB e (hj : hsrc * nat) ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2,
c1 = (if re_eof e =? 0 then dr_ctl cB (fst hj) ev else cB) ->
O1 = (if (re_eof e =? 0) && dr_live cB (fst hj) then OB ++ LB else OB) ->
cap1 = (if (re_eof e =? 0) && dr_live cB (fst hj)
        then drain_b_c.ds_ocap (dr_fin cB mx (Z.of_nat (length OB)) capB e (fst hj)) else capB) ->
(if re_eof e =? 0 then dr_rel cB mx (Z.of_nat (length OB)) capB e (fst hj) e1 h1 LB else e1 = e /\ h1 = fst hj) ->
geik pre (re_keys e1) = (Ed, ks) ->
sl_sends mx c1 O1 cap1 (ge_bytes Ed) = (c2, O2, cap2) ->
rig_rel pre mx cB OB capB [(e, hj)] [(entry_keys e1 ks, h1)] c2 O2 cap2.
Proof.
intros pre mx cB OB capB e [h j] ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2 Ec EO Ecap Hd Hg Hs. cbn [fst] in *.
subst c1 O1 cap1. cbn [rig_rel]. exists e1, ev, LB. cbv zeta. split; [exact Hd|].
rewrite Hg. cbn [fst snd]. split; [reflexivity|]. rewrite Hs. cbn [rig_rel]. repeat split.
Qed.

(* -- KEY's pass: the key lacks the prefix -- *)
Lemma rkb_gin_pass : forall cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GIN B MT RP MMAX RG cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = false ->
exists f', GIN B MT RP MMAX RG cx i (S n) r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f' c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Proof.
intros cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 H Hp.
pose proof H as H0. unfold GIN in H0. cbv zeta in H0.
destruct H0 as (_ & _ & _ & _ & _ & Hk & Hf & _).
destruct f as [|f0]; [exfalso; lia|].
exists f0. unfold GIN in H |- *. cbv zeta in H |- *.
rewrite <- (rkb_geik_pass f0 (gpre cx) n ks ltac:(lia) Hp).
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj _ (conj _ H8))))))); lia.
Qed.

Lemma rkb_gout_pass : forall cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GIN B MT RP MMAX RG cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = false ->
GOUT B MT RP MMAX RG cx (S i) (qd ++ [(entry_keys e1 ks, h1)]) c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Proof.
intros cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HB H Hp.
pose proof (rkb_gbase_len cx HB) as HL.
unfold GIN in H. cbv zeta in H.
destruct H as (Hi & Hq & Hrel & Hdr & Hs & Hk & Hf & Hg & Har & Hout & Hsrc & Hsrc1 & Hdro & Hkept & Hperm & _ & _ & Hbud).
assert (Hgk : geik_loop f (gpre cx) n ks = ([], ks)).
{ destruct f as [|f0]; [lia|]. rewrite (rkb_geik_pass f0 (gpre cx) n ks ltac:(lia) Hp). apply rkb_geik_done. lia. }
rewrite Hgk in Hg, Hbud. cbn [fst snd] in Hg, Hbud. rewrite app_nil_r in Hg.
change (ge_bytes []) with (@nil (list byte)) in Hbud. cbn [sl_sends] in Hbud.
rewrite rkb_gkrest_nil in Hbud. cbn [app] in Hbud.
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & EO1 & Ecap1 & Hd).
assert (Hlt : (i < length (gps cx))%nat) by (unfold gps; rewrite length_combine, HL; lia).
assert (Hnth : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i)).
{ unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HL. }
assert (Hfs : firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)]).
{ rewrite (rkb_firstn_snoc (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) Hlt), Hnth. reflexivity. }
assert (Hlf : length (firstn i (gps cx)) = length qd) by (rewrite length_firstn; lia).
unfold GOUT.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
- lia.
- rewrite length_app. cbn [length]. lia.
- rewrite Hfs. eapply rkb_rel_app; [exact Hrel|].
  exact (rkb_rel_one (gpre cx) (gxmx cx) cB OB capB (gnth cx i) (ghj cx i) ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2
    Ec1 EO1 Ecap1 Hd Hg Hs).
- rewrite (map_app fst qd [(entry_keys e1 ks, h1)]), <- app_assoc.
  change (map fst [(entry_keys e1 ks, h1)] ++ skipn (S i) (gxes cx)) with (entry_keys e1 ks :: skipn (S i) (gxes cx)).
  exact Har.
- exact Hout.
- intros i' Hi' He'. destruct (Nat.lt_ge_cases i' i) as [Hlt' | Hge'].
  + rewrite app_nth1 by lia. exact (Hsrc i' Hlt' He').
  + assert (Ei : i' = i) by lia. subst i'. rewrite app_nth2 by lia. rewrite Hq, Nat.sub_diag. cbn [nth snd].
    apply Hsrc1. apply Z.eqb_eq. exact He'.
- exact Hdro.
- exact Hkept.
- rewrite (map_app fst qd [(entry_keys e1 ks, h1)]), <- app_assoc.
  change (map fst [(entry_keys e1 ks, h1)] ++ skipn (S i) (gxes cx)) with (entry_keys e1 ks :: skipn (S i) (gxes cx)).
  rewrite Hfs, (rkb_gdone_snoc _ _ _ _ _ _ Hlf), <- app_assoc. exact Hperm.
- exact Hbud.
Qed.

(* ==== KEY's end arm: the model and list side ==== *)
Lemma rkb_aout_cap : forall ly S W m c O mx no cap out, aout_at B RG ly S W m c O mx no cap out -> 0 <= cap.
Proof.
intros ly S W m c O mx no cap out H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc).
destruct Hc as [(E & _) | (Hc & _)]; lia.
Qed.

Lemma rkb_perm_front : forall {T : Type} (Y O Z : list T), Permutation (Y ++ O ++ Z) (O ++ Y ++ Z).
Proof. intros T Y O Z. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.

Lemma rkb_perm_out : forall {T : Type} (G : T) (C D I R O gx : list T),
Permutation (G :: C ++ D ++ I ++ R ++ O ++ gx) (O ++ G :: C ++ D ++ I ++ R ++ gx).
Proof.
intros T G C D I R O gx.
transitivity ((G :: C ++ D ++ I ++ R) ++ O ++ gx).
{ cbn [app]. rewrite <- !app_assoc. apply Permutation_refl. }
transitivity (O ++ (G :: C ++ D ++ I ++ R) ++ gx); [apply rkb_perm_front|].
cbn [app]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Lemma rkb_concat_mid : forall {T U : Type} (g : T -> list U) A x Z,
concat (map g (A ++ x :: Z)) = concat (map g A) ++ g x ++ concat (map g Z).
Proof. intros T U g A x Z. rewrite map_app, concat_app. cbn [map concat]. reflexivity. Qed.

(* the ended key's block leaves the entry's blocks *)
Lemma rkb_ablks_swap : forall e ks n, (n < length ks)%nat ->
Permutation (aentry_blks (entry_keys e ks))
  ((key_addr (nth n ks (0, [], [])), Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) :: aentry_blks (entry_keys e (swap_remove (0, [], []) n ks))).
Proof.
intros e ks n H. unfold aentry_blks, entry_keys. cbn [re_cap re_buf re_hp re_kh re_keys].
rewrite !app_assoc.
eapply perm_trans.
{ apply Permutation_app_head. apply Permutation_map. apply relay_instance_gone_b_lem.rigl_swap_perm. exact H. }
cbn [map]. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma rkb_cat_swap : forall A e ks n Z, (n < length ks)%nat ->
Permutation (concat (map aentry_blks (A ++ entry_keys e ks :: Z)))
  ((key_addr (nth n ks (0, [], [])), Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) :: concat (map aentry_blks (A ++ entry_keys e (swap_remove (0, [], []) n ks) :: Z))).
Proof.
intros A e ks n Z H. rewrite !rkb_concat_mid.
eapply perm_trans.
{ apply Permutation_app_head. apply Permutation_app_tail. exact (rkb_ablks_swap e ks n H). }
cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma rkb_perm_end : forall cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent r ly1 S1 W1 mA
  ly2 S2 ly3 S3 l1 l2 rest out2' cap2'',
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ->
  List.NoDup (ablocks B ly1 S1) ->
  Permutation (ablocks B ly1 S1) (aout_blks cap2 out2 ++ rest) ->
  Permutation (ablocks B ly2 S2) (aout_blks cap2'' out2' ++ rest) ->
  ablocks B ly2 S2 = l1 ++ (key_addr (nth n ks (0, [], [])), Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) :: l2 ->
  ablocks B ly3 S3 = l1 ++ l2 ->
  Permutation (ablocks B ly3 S3)
   ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap2'' out2' ++ gxrest cx).
Proof.
intros cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent r ly1 S1 W1 mA
  ly2 S2 ly3 S3 l1 l2 rest out2' cap2'' H _ P1 P2 E2 E3.
unfold GIN in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & _ & Hk & _ & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkb_cat_swap (map fst qd) e1 ks n (skipn (S i) (gxes cx)) Hn) as HC.
set (kb := (key_addr (nth n ks (0, [], [])), Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1)) in *.
set (C := concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx)))) in *.
set (C' := concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)))) in *.
set (D := gdone_srcs (firstn i (gps cx)) qd) in *.
set (I := if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) in *.
set (R := rig_srcs (skipn (S i) (gps cx))) in *.
assert (HX : Permutation rest ((gxG0 cx, ATABLE) :: C ++ D ++ I ++ R ++ gxrest cx)).
{ apply Permutation_app_inv_l with (l := aout_blks cap2 out2).
  eapply perm_trans; [apply Permutation_sym; exact P1|]. eapply perm_trans; [exact Hperm|]. apply rkb_perm_out. }
assert (HX' : Permutation ((gxG0 cx, ATABLE) :: C ++ D ++ I ++ R ++ gxrest cx)
                          (kb :: (gxG0 cx, ATABLE) :: C' ++ D ++ I ++ R ++ gxrest cx)).
{ eapply perm_trans; [apply perm_skip; apply Permutation_app_tail; exact HC|]. cbn [app]. apply perm_swap. }
assert (H2 : Permutation (kb :: l1 ++ l2) (kb :: aout_blks cap2'' out2' ++ (gxG0 cx, ATABLE) :: C' ++ D ++ I ++ R ++ gxrest cx)).
{ eapply perm_trans; [apply Permutation_middle|]. rewrite <- E2. eapply perm_trans; [exact P2|].
  eapply perm_trans; [apply Permutation_app_head; exact (perm_trans HX HX')|].
  apply Permutation_sym. apply Permutation_middle. }
apply Permutation_cons_inv in H2.
rewrite E3. eapply perm_trans; [exact H2|]. apply Permutation_sym. apply rkb_perm_out.
Qed.

(* the model side of one end step, at any r; the room the free's post leaves (rk_krn) and the key's count change *)
Lemma rkb_end_model : forall cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ly3 S3,
  GBASE B ARx MT RP MMAX RG cx ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ->
  has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
  mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) ->
  blocks_bytes S3 <= blocks_bytes S1 +
    tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ->
  rp_RM RP S3 (rk_krn cx i n ks f c2 O2 cap2) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1))) ->
  exists f0, f = S f0 /\
  sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes (Ed ++ [nth n ks (0, [], [])])) = (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))), ge_O c2 O2 (key_text (nth n ks (0, [], []))), ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) /\
  length (swap_remove (0, [], []) n ks) = (n + r)%nat /\ (length (swap_remove (0%Z, [], []) n ks) - n <= f0)%nat /\
  geik (gpre cx) (re_keys e1) =
    ((Ed ++ [nth n ks (0, [], [])]) ++ fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks)), snd (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks))) /\
  (let '(_, O3, cap3) := sl_sends (gxmx cx) (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_bytes (fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks)))) in
   gbud B MT RP MMAX cx ly3 S3 (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT))
     (gkrest cx (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], [])))))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks))) ++
      grest cx (S i) (Z.of_nat (length O3)) cap3)).
Proof.
intros cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ly3 S3 HB H Hp Hle Hbb HRM3 HCN3.
pose proof (rkb_live_gin cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA H) as HL.
destruct (rkb_gbase_facts cx HB) as (Hmx & _ & _).
unfold GIN in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & Hs & Hk & Hf & Hg & Har & Hout & _ & _ & _ & _ & _ & _ & _ & Hbud).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkb_aout_cap _ _ _ _ _ _ _ _ _ _ Hout) as Hcap.
assert (Hxl : 0 < Z.of_nat (length (key_text (nth n ks (0, [], []))))).
{ destruct Har as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hent & _).
  rewrite Forall_forall in Hent.
  assert (Hin : In (entry_keys e1 ks) (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx)))
    by (apply in_or_app; right; left; reflexivity).
  destruct (Hent _ Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF).
  change (re_keys (entry_keys e1 ks)) with ks in HF. rewrite Forall_forall in HF.
  assert (Hk0 : In (nth n ks (0, [], [])) ks) by (apply nth_In; exact Hn).
  destruct (HF _ Hk0) as (_ & _ & _ & Hr). lia. }
destruct f as [|f0]; [lia|]. exists f0.
unfold rk_krn, rk_tl in HRM3. cbn [Nat.pred] in HRM3. cbv zeta in HRM3.
rewrite (rkb_geik_end f0 (gpre cx) n ks Hn Hp) in Hg, Hbud. cbn [fst snd] in Hg, Hbud.
assert (Hs' : sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes (Ed ++ [nth n ks (0, [], [])])) = (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))), ge_O c2 O2 (key_text (nth n ks (0, [], []))), ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))).
{ rewrite rkb_ge_bytes_app, rkb_sends_app, Hs. exact (rkb_sends_key (gxmx cx) c2 O2 cap2 (nth n ks (0, [], []))). }
split; [reflexivity|]. split; [exact Hs'|].
split; [rewrite relay_instance_gone_b_lem.rigl_len_swap; lia|].
split; [rewrite relay_instance_gone_b_lem.rigl_len_swap; lia|].
split; [rewrite Hg, <- app_assoc; reflexivity|].
set (Er := fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks))) in *.
assert (Ek : sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (nth n ks (0, [], []) :: Er)) =
             sl_sends (gxmx cx) (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_bytes Er)).
{ change (ge_bytes (nth n ks (0, [], []) :: Er)) with (ge_bytes [nth n ks (0, [], [])] ++ ge_bytes Er).
  rewrite rkb_sends_app, rkb_sends_key. reflexivity. }
rewrite Ek in Hbud. revert Hbud HRM3.
destruct (sl_sends (gxmx cx) (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_bytes Er)) as [[c3 O3] cap3].
intros Hbud HRM3. cbv beta iota in Hbud, HRM3 |- *. rewrite rkb_ge_O_len. rewrite rkb_ge_O_len in HRM3.
exact (rkb_gbud_end cx ly1 S1 ly3 S3 spent c2 (Z.of_nat (length O2)) cap2 (nth n ks (0, [], [])) Er (grest cx (S i) (Z.of_nat (length O3)) cap3)
  Hbud HL ltac:(lia) ltac:(lia) Hcap Hxl Hle Hbb HRM3 HCN3).
Qed.

Lemma rkb_gin_end : forall cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA
  ly3 S3 W3 mD out2',
  GBASE B ARx MT RP MMAX RG cx ->
  GIN B MT RP MMAX RG cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ->
  has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
  mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) ->
  blocks_bytes S3 <= blocks_bytes S1 +
    tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ->
  rp_RM RP S3 (rk_krn cx i n ks f c2 O2 cap2) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1))) ->
  arelay_at B RG ly3 S3 W3 mD (gxG0 cx) (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)) ->
  aout_at B RG ly3 S3 W3 mD (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (gxmx cx) (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], [])))))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out2' ->
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1) ->
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p))) (skipn (S i) (gps cx)) ->
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 mD a) ->
  Permutation (ablocks B ly3 S3)
   ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx)) ++ aout_blks (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out2' ++ gxrest cx) ->
  garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]) ->
  garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] ->
  exists f', GIN B MT RP MMAX RG cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 (swap_remove (0, [], []) n ks) (Ed ++ [nth n ks (0, [], [])]) f'
    (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out2' (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT)) ly3 S3 W3 mD.
Proof.
intros cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ly3 S3 W3 mD out2'
  HB H Hp Hle Hbb HRM3 HCN3 Har3 Hout3 Hsrc3 Hsrc13 Hdr3 Hkept3 Hperm3 Hg1 Hg2.
destruct (rkb_end_model cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ly3 S3
  HB H Hp Hle Hbb HRM3 HCN3) as (f0 & _ & Hs' & Hk' & Hf' & Hg' & Hbud').
exists f0. unfold GIN in H |- *. cbv zeta in H |- *.
destruct H as (H1 & H2 & H3 & H4 & _).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj Hs' (conj Hk' (conj Hf' (conj Hg' (conj Har3 (conj Hout3
  (conj Hsrc3 (conj Hsrc13 (conj Hdr3 (conj Hkept3 (conj Hperm3 (conj Hg1 (conj Hg2 Hbud'))))))))))))))))).
Qed.

Lemma rkb_gout_end : forall cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA
  ly3 S3 W3 mD out2',
  GBASE B ARx MT RP MMAX RG cx ->
  GIN B MT RP MMAX RG cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ->
  has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
  mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) ->
  blocks_bytes S3 <= blocks_bytes S1 +
    tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ->
  rp_RM RP S3 (rk_krn cx i n ks f c2 O2 cap2) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1))) ->
  arelay_at B RG ly3 S3 W3 mD (gxG0 cx) (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)) ->
  aout_at B RG ly3 S3 W3 mD (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (gxmx cx) (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], [])))))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out2' ->
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1) ->
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p))) (skipn (S i) (gps cx)) ->
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 mD a) ->
  Permutation (ablocks B ly3 S3)
   ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx)) ++ aout_blks (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out2' ++ gxrest cx) ->
  garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]) ->
  garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] ->
  GOUT B MT RP MMAX RG cx (S i) (qd ++ [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]) (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out2' (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT))
    ly3 S3 W3 mD.
Proof.
intros cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ly3 S3 W3 mD out2'
  HB H Hp Hle Hbb HRM3 HCN3 Har3 Hout3 Hsrc3 Hsrc13 Hdr3 Hkept3 Hperm3 _ _.
destruct (rkb_end_model cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ly3 S3
  HB H Hp Hle Hbb HRM3 HCN3) as (f0 & _ & Hs' & Hk' & _ & Hg' & Hbud').
pose proof (rkb_gbase_len cx HB) as HL.
unfold GIN in H. cbv zeta in H. destruct H as (Hi & Hq & Hrel & Hdr & _).
assert (Hgk : geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks) = ([], swap_remove (0, [], []) n ks)) by (apply rkb_geik_done; lia).
rewrite Hgk in Hg', Hbud'. cbn [fst snd] in Hg', Hbud'. rewrite app_nil_r in Hg'.
change (ge_bytes []) with (@nil (list byte)) in Hbud'. cbn [sl_sends] in Hbud'.
rewrite rkb_gkrest_nil in Hbud'. cbn [app] in Hbud'.
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & EO1 & Ecap1 & Hd).
assert (Hlt : (i < length (gps cx))%nat) by (unfold gps; rewrite length_combine, HL; lia).
assert (Hnth : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i)).
{ unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HL. }
assert (Hfs : firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)]).
{ rewrite (rkb_firstn_snoc (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) Hlt), Hnth. reflexivity. }
assert (Hlf : length (firstn i (gps cx)) = length qd) by (rewrite length_firstn; lia).
unfold GOUT.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
- lia.
- rewrite length_app. cbn [length]. lia.
- rewrite Hfs. eapply rkb_rel_app; [exact Hrel|].
  exact (rkb_rel_one (gpre cx) (gxmx cx) cB OB capB (gnth cx i) (ghj cx i) ev LB e1 h1 c1 O1 cap1 (Ed ++ [nth n ks (0, [], [])]) (swap_remove (0, [], []) n ks)
    _ _ _ Ec1 EO1 Ecap1 Hd Hg' Hs').
- rewrite (map_app fst qd [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]), <- app_assoc.
  change (map fst [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)] ++ skipn (S i) (gxes cx)) with (entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)).
  exact Har3.
- exact Hout3.
- intros i' Hi' He'. destruct (Nat.lt_ge_cases i' i) as [Hlt' | Hge'].
  + rewrite app_nth1 by lia. exact (Hsrc3 i' Hlt' He').
  + assert (Ei : i' = i) by lia. subst i'. rewrite app_nth2 by lia. rewrite Hq, Nat.sub_diag. cbn [nth snd].
    apply Hsrc13. apply Z.eqb_eq. exact He'.
- exact Hdr3.
- exact Hkept3.
- rewrite (map_app fst qd [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]), <- app_assoc.
  change (map fst [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)] ++ skipn (S i) (gxes cx)) with (entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)).
  rewrite Hfs, (rkb_gdone_snoc _ _ _ _ _ _ Hlf), <- app_assoc. exact Hperm3.
- exact Hbud'.
Qed.

(* ==== keep block (RigKeyKeep) ==== *)

(* ---- rkk_: the cut predicates' memory facts survive a change of memory only in the scratch window
   [gsp1 cx - DRAIN_STK_x, gsp1 cx) below sp = gsp1 cx (an interceptor call's scratch at a cut after the prologue).
   The window is [gsp0 cx - RIG_STK_x, gsp1 cx) (RIG_STK_x = RIG_FRAME + DRAIN_STK_x): its bottom is at or above
   ly_stk_lo >= alloc_ceiling (GBASE's astk_ok), so every heap block, frame, image byte and shadow byte the predicates
   read lies below it, and every frame slot (gsp1 + 16 .. gsp0) above it. ---- *)
Definition rkk_KEEP (cx : gcx) (W : world SEGS) (m m2 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) ->
  aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a.
Definition rkk_PRES (W : world SEGS) (m m2 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a.

Lemma rkk_aview_mod : forall H (m : word -> option byte) a,
  aview SEGS H m (a mod 2 ^ 64) = aview SEGS H m a.
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv64_mod. reflexivity. Qed.

Lemma rkk_wr : forall W m1 m2 a, rkk_PRES W m1 m2 ->
  writable_at SEGS (arm W m1) a -> writable_at SEGS (arm W m2) a.
Proof.
  intros W m1 m2 a HP. unfold writable_at, wview, arm, mrestrict.
  destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [exact (fun H => H)|].
  destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:E2; [intros _; cbn; discriminate|].
  destruct (m1 (Z_to_bv 64 a)) as [b1|] eqn:E1; [|exact (fun H => H)].
  destruct (HP a (conj EH (ex_intro _ b1 E1))) as [_ [b E]]. rewrite E in E2. discriminate E2.
Qed.

Lemma rkk_bv : forall cx, 0 <= gsp0 cx < 2 ^ 64.
Proof. intros cx. unfold gsp0, spZ. exact (bv_unsigned_in_range 64 _). Qed.

Lemma rkk_view_mod : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 ->
  ~ (gsp1 cx - DRAIN_STK_x <= a mod 2 ^ 64 < gsp1 cx) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
  intros cx W m1 m2 a HK Hw.
  rewrite <- (rkk_aview_mod (w_H W) m2 a), <- (rkk_aview_mod (w_H W) m1 a).
  apply HK; [apply Z.mod_pos_bound; lia | exact Hw].
Qed.

Lemma rkk_view_hi : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 ->
  gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
  intros cx W m1 m2 a HK Ha. apply (rkk_view_mod cx); [exact HK|].
  pose proof (rkk_bv cx) as Hb.
  destruct (Z_le_gt_dec 0 a) as [H0|H0].
  - rewrite Z.mod_small by lia. lia.
  - pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma rkk_view_lo : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 ->
  0 <= a < gsp1 cx - DRAIN_STK_x -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
  intros cx W m1 m2 a HK Ha. apply (rkk_view_mod cx); [exact HK|].
  pose proof (rkk_bv cx) as Hb.
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity. assert (HD : DRAIN_STK_x = 16976) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rkk_kept_hi : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  gsp1 cx <= a < gsp0 cx -> abyte_kept W m1 W m2 a.
Proof.
  intros cx W m1 m2 a HK HP Ha. unfold abyte_kept.
  split; [exact (rkk_view_hi cx W m1 m2 a HK Ha) | exact (rkk_wr W m1 m2 a HP)].
Qed.

Lemma rkk_kept_lo : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  0 <= a < gsp1 cx - DRAIN_STK_x -> abyte_kept W m1 W m2 a.
Proof.
  intros cx W m1 m2 a HK HP Ha. unfold abyte_kept.
  split; [exact (rkk_view_lo cx W m1 m2 a HK Ha) | exact (rkk_wr W m1 m2 a HP)].
Qed.

(* the ASan view decides a cell *)
Lemma rkk_vm : forall W m1 m2 a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x) ->
  val_mem SEGS (arm W m1) a n v -> val_mem SEGS (arm W m2) a n v.
Proof.
  intros W m1 m2 a n v HK Hv k Hk. unfold arm.
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m1 m2 (a + Z.of_nat k)); [exact (Hv k Hk)|].
  exact (HK (a + Z.of_nat k) ltac:(lia)).
Qed.

(* the window's bottom is at or above alloc_ceiling *)
Lemma rkk_ceil : forall cx, GBASE B ARx MT RP MMAX RG cx -> alloc_ceiling <= gsp1 cx - DRAIN_STK_x.
Proof.
  intros cx HB. destruct HB as (HPRE & _).
  destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & _).
  assert (E : RIG_STK_x = RIG_FRAME + DRAIN_STK_x) by reflexivity.
  unfold gsp1, gsp0. lia.
Qed.

Lemma rkk_kept_c : forall cx W m1 m2 a, GBASE B ARx MT RP MMAX RG cx -> rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  0 <= a < alloc_ceiling -> abyte_kept W m1 W m2 a.
Proof.
  intros cx W m1 m2 a HB HK HP Ha. pose proof (rkk_ceil cx HB).
  apply (rkk_kept_lo cx W m1 m2 a HK HP). lia.
Qed.

(* every byte of every range of fp is below alloc_ceiling *)
Definition rkk_low (fp : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.

Lemma rkk_akept : forall cx W m1 m2 fp, GBASE B ARx MT RP MMAX RG cx -> rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  rkk_low fp -> akept W m1 W m2 fp.
Proof. intros cx W m1 m2 fp HB HK HP HL r Hr a Ha. exact (rkk_kept_c cx W m1 m2 a HB HK HP (HL r Hr a Ha)). Qed.

(* ---- where the bytes are ---- *)
Lemma rkk_blk : forall ly S W m md p n a, ARh ly S W m md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + n -> 0 <= a < alloc_ceiling.
Proof.
  intros ly S W m md p n a HAR Hin Ha.
  destruct (rk_alb ly S W m md p n HAR Hin) as (_ & H4 & Hc & _).
  unfold req_size in Hc. destruct (n =? 0) eqn:En; [apply Z.eqb_eq in En; lia | lia].
Qed.

Lemma rkk_img : forall a, in_img SEGS a -> 0 <= a < alloc_ceiling.
Proof.
  intros a H. pose proof (pa_segs_low a H) as Hl. pose proof asan_consts as (C1 & _ & _ & _ & C5).
  rewrite C5 in Hl. lia.
Qed.

Lemma rkk_inG : forall a, inG (G_RIG B RG) a -> 0 <= a < alloc_ceiling.
Proof. intros a H. exact (rkk_img a (proj1 (HGRIG a H))). Qed.

Lemma rkk_glob : forall cx a, GBASE B ARx MT RP MMAX RG cx ->
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/
   rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
   rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
   rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
   rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
   rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
   as_errno B <= a < as_errno B + 4) ->
  0 <= a < alloc_ceiling.
Proof.
  intros cx a HB H.
  destruct HB as (_ & _ & _ & HPL & _). destruct HPL as (_ & _ & _ & _ & _ & _ & Hrng & _).
  assert (HG : forall lo len, In (lo, len) (G_RIG B RG) -> lo <= a < lo + len -> 0 <= a < alloc_ceiling).
  { intros lo len Hin Ha. apply rkk_inG. unfold inG. apply Exists_exists. exists (lo, len).
    split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  assert (HR : rg_rng RG a -> 0 <= a < alloc_ceiling) by (intros Hr; exact (rkk_img a (proj1 (Hrng a Hr)))).
  assert (HI : (rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
    rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) -> 0 <= a < alloc_ceiling)
    by (intros Hr; exact (rkk_img a (proj1 (HRGI a Hr)))).
  unfold rg_rng in HR.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]].
  - apply HR; tauto.
  - apply HR; tauto.
  - apply HR; tauto.
  - apply HR; tauto.
  - apply HI; tauto.
  - apply HI; tauto.
  - apply (HG (rg_nout RG) 8); [unfold G_RIG, G_DR, G_SL; do 4 right; left; reflexivity | exact H].
  - apply (HG (rg_capout RG) 8); [unfold G_RIG, G_DR, G_SL; do 5 right; left; reflexivity | exact H].
  - apply (HG (rg_out RG) 8); [unfold G_RIG, G_DR, G_SL; do 6 right; left; reflexivity | exact H].
  - apply HI; tauto.
  - apply (HG (rg_client_broken RG) 1); [unfold G_RIG, G_DR, G_SL; do 2 right; left; reflexivity | exact H].
  - apply HI; tauto.
  - apply (HG (rg_send_eintr RG) 1); [unfold G_RIG, G_DR, G_SL; do 3 right; left; reflexivity | exact H].
  - apply (HG (as_errno B) 4); [unfold G_RIG, G_DR, G_SL; do 7 right; left; reflexivity | exact H].
Qed.

(* the g_s slot of an open entry is one of g_s[0..3] (drain's source facts at the entry) *)
Lemma rkk_j4 : forall cx i, GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof (gnth cx i) = 0 ->
  (snd (ghj cx i) < 4)%nat.
Proof.
  intros cx i HB Hi He.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & HF & _).
  rewrite Forall_forall in HF.
  assert (E : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i))
    by (unfold gps, gnth, ghj; apply combine_nth; symmetry; exact Hlen).
  assert (Hin : In (gnth cx i, ghj cx i) (gps cx)).
  { rewrite <- E. apply nth_In. unfold gps. rewrite length_combine, Hlen, Nat.min_id. exact Hi. }
  destruct (HF _ Hin He) as (Hj & _). exact Hj.
Qed.

Lemma rkk_slot_loc : forall cx j, GBASE B ARx MT RP MMAX RG cx -> (j < 4)%nat ->
  forall a, rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC -> 0 <= a < alloc_ceiling.
Proof. intros cx j HB Hj a Ha. apply (rkk_glob cx a HB). right; left. unfold ASRC in *. lia. Qed.

Lemma rkk_len_recs : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold text_rec, Mem.le8.
  rewrite length_app, !length_N_to_le_bytes. lia.
Qed.

Lemma rkk_len_ptrs : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold key_ptrs in *. cbn [map concat length]. rewrite length_app, IH. unfold Mem.le8.
  rewrite length_N_to_le_bytes. lia.
Qed.

Lemma rkk_alist : forall ly S W m md LA l lines, ARh ly S W m md -> alist_at B ly S W m LA l lines ->
  (forall a, LA <= a < LA + 16 -> 0 <= a < alloc_ceiling) ->
  rkk_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W m md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA.
  rewrite Forall_forall in H9.
  split.
  - intros rg Hrg a Ha. unfold alist_fp in Hrg. destruct Hrg as [<-|Hrg]; [apply HLA; exact Ha|].
    apply in_app_or in Hrg. destruct Hrg as [Hrg|Hrg].
    + destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)].
      * rewrite Hc in Hrg. cbn in Hrg. destruct Hrg.
      * assert (E : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hrg.
        destruct Hrg as [<-|[]].
        apply (rkk_blk ly S W m md (hl_v l) (AREC * hl_cap l) a HAR Hin).
        unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, rkk_len_recs in Ha.
        unfold hl_n in Hj. unfold AREC in *. lia.
    + apply in_map_iff in Hrg. destruct Hrg as (r & <- & Hr).
      apply (rkk_blk ly S W m md (fst r) (Z.of_nat (length (snd r)) + 1) a HAR (proj1 (H9 r Hr))).
      unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
  - intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + destruct H6 as [(Hc & _) | (Hc & Hin & _)].
      * rewrite Hc in Hb. cbn in Hb. destruct Hb.
      * assert (E : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hb.
        destruct Hb as [<-|[]]. exact Hin.
    + apply in_map_iff in Hb. destruct Hb as (r & <- & Hr). exact (proj1 (H9 r Hr)).
Qed.

Lemma rkk_asrc : forall ly S W m md HA h, ARh ly S W m md -> asrc_at B ly S W m HA h ->
  (forall a, HA <= a < HA + ASRC -> 0 <= a < alloc_ceiling) ->
  rkk_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W m md HA h HAR Hs HHA.
  destruct Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & H19 & _ & _ & H22 & H23 & _).
  destruct (rkk_alist ly S W m md (HA + 16) _ _ HAR H10 ltac:(intros a Ha; apply HHA; unfold ASRC; lia)) as [L1 B1].
  destruct (rkk_alist ly S W m md (HA + 64) _ _ HAR H22 ltac:(intros a Ha; apply HHA; unfold ASRC; lia)) as [L2 B2].
  destruct (rkk_alist ly S W m md (HA + 80) _ _ HAR H23 ltac:(intros a Ha; apply HHA; unfold ASRC; lia)) as [L3 B3].
  split.
  - intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<-|[<-|Hr]].
    + apply HHA. exact Ha.
    + apply (rkk_blk ly S W m md (hs_partial h) APARTIAL a HAR H18).
      unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map in Ha. lia.
    + apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (L1 r Hr a Ha)|].
      apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (L2 r Hr a Ha) | exact (L3 r Hr a Ha)].
  - intros b Hb. unfold asrc_blks in Hb. destruct Hb as [<-|Hb]; [exact H18|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (B1 b Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (B2 b Hb) | exact (B3 b Hb)].
Qed.

Lemma rkk_aentry : forall ly S W m md e, ARh ly S W m md -> aentry_ok B ly S W m e ->
  rkk_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W m md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  rewrite Forall_forall in H15.
  split.
  - intros r Hr a Ha. unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
    + destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)].
      * rewrite Hc in Hr. cbn in Hr. destruct Hr.
      * assert (E : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hr.
        destruct Hr as [<-|[]].
        apply (rkk_blk ly S W m md (re_buf e) (re_cap e) a HAR Hin).
        unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. lia.
    + destruct Hr as [<-|Hr].
      * unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, rkk_len_ptrs in Ha.
        destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)].
        -- rewrite Hk in Ha. cbn [length] in Ha. lia.
        -- apply (rkk_blk ly S W m md (re_hp e) (re_kh e) a HAR Hin). unfold re_nheld in Hk1. lia.
      * apply in_map_iff in Hr. destruct Hr as (k & <- & Hk).
        apply (rkk_blk ly S W m md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR (proj1 (H15 k Hk))).
        unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
  - intros b Hb. unfold aentry_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + destruct H10 as [(Hc & _) | (Hc & Hin & _)].
      * rewrite Hc in Hb. cbn in Hb. destruct Hb.
      * assert (E : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hb.
        destruct Hb as [<-|[]]. exact Hin.
    + apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * destruct H12 as [(Hz & _) | (Hz & Hin & _)].
        -- rewrite Hz in Hb. cbn in Hb. destruct Hb.
        -- assert (E : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz). rewrite E in Hb.
           destruct Hb as [<-|[]]. exact Hin.
      * apply in_map_iff in Hb. destruct Hb as (k & <- & Hk). exact (proj1 (H15 k Hk)).
Qed.

Lemma rkk_arelay : forall cx ly S W m md G es, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m md ->
  arelay_at B RG ly S W m G es ->
  rkk_low (arelay_fp RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros cx ly S W m md G es HB HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  rewrite Forall_forall in H10.
  split.
  - intros r Hr a Ha. unfold arelay_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|Hr]]]]; cbn [fst snd] in Ha.
    + apply (rkk_glob cx a HB). tauto.
    + apply (rkk_glob cx a HB). tauto.
    + apply (rkk_glob cx a HB). tauto.
    + exact (rkk_blk ly S W m md G ATABLE a HAR H8 Ha).
    + apply in_concat in Hr. destruct Hr as (l & Hl & Hr). apply in_map_iff in Hl. destruct Hl as (e & <- & He).
      exact (proj1 (rkk_aentry ly S W m md e HAR (H10 e He)) r Hr a Ha).
  - intros b Hb. unfold arelay_blks in Hb. destruct Hb as [<-|Hb]; [exact H8|].
    apply in_concat in Hb. destruct Hb as (l & Hl & Hb). apply in_map_iff in Hl. destruct Hl as (e & <- & He).
    exact (proj2 (rkk_aentry ly S W m md e HAR (H10 e He)) b Hb).
Qed.

Lemma rkk_aout : forall cx ly S W m md c O mx no cap out, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m md ->
  aout_at B RG ly S W m c O mx no cap out ->
  rkk_low (aout_fp B RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros cx ly S W m md c O mx no cap out HB HAR Ho.
  destruct Ho as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  split.
  - intros r Hr a Ha. unfold aout_fp in Hr.
    do 9 (destruct Hr as [<-|Hr]; [cbn [fst snd] in Ha; apply (rkk_glob cx a HB); tauto|]).
    destruct H26 as [(Hc & _ & _) | (Hc & Hno & Hin & junk & Hj & Hg)].
    + rewrite Hc in Hr. cbn in Hr. destruct Hr.
    + assert (E : (cap =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hr.
      destruct Hr as [<-|[]]. cbn [fst snd] in Ha. exact (rkk_blk ly S W m md out cap a HAR Hin Ha).
  - intros b Hb. unfold aout_blks in Hb.
    destruct H26 as [(Hc & _ & _) | (Hc & Hno & Hin & junk & Hj & Hg)].
    + rewrite Hc in Hb. cbn in Hb. destruct Hb.
    + assert (E : (cap =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hb.
      destruct Hb as [<-|[]]. exact Hin.
Qed.

(* ---- the predicates, across the change ---- *)
Lemma rkk_asrc_m : forall cx ly S W m1 m2 md HA h, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m1 md ->
  rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 -> asrc_at B ly S W m1 HA h ->
  (forall a, HA <= a < HA + ASRC -> 0 <= a < alloc_ceiling) -> asrc_at B ly S W m2 HA h.
Proof.
  intros cx ly S W m1 m2 md HA h HB HAR HK HP Hs HL.
  destruct (rkk_asrc ly S W m1 md HA h HAR Hs HL) as [L Bl].
  exact (asrc_at_kept B ly S W m1 ly S W m2 HA h Hs (rkk_akept cx W m1 m2 _ HB HK HP L) Bl).
Qed.

Lemma rkk_aothers : forall cx W m1 m2 j fd, GBASE B ARx MT RP MMAX RG cx -> rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  aothers_at RG W m1 j fd -> aothers_at RG W m2 j fd.
Proof.
  intros cx W m1 m2 j fd HB HK HP Ho i Hi Hij. destruct (Ho i Hi Hij) as (f & o & Hf & Hof & Hx).
  assert (KS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W m1 W m2 x)
    by (intros x Hx'; apply (rkk_kept_c cx W m1 m2 x HB HK HP); apply (rkk_glob cx x HB); tauto).
  exists f, o. split; [|split; [|exact Hx]].
  - apply (akept_vm W m1); [intros x Hx'; apply KS; unfold ASRC in *; lia | exact Hf].
  - apply (akept_vm W m1); [intros x Hx'; apply KS; unfold ASRC in *; lia | exact Hof].
Qed.

Lemma rkk_drsrc : forall cx ly S W m1 m2 md e h j, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m1 md ->
  rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  dr_src_ok B RG ly S W m1 e h j -> dr_src_ok B RG ly S W m2 e h j.
Proof.
  intros cx ly S W m1 m2 md e h j HB HAR HK HP (Hj & Hs & Ho & Hrest).
  split; [exact Hj|]. split; [|split; [exact (rkk_aothers cx W m1 m2 j _ HB HK HP Ho) | exact Hrest]].
  exact (rkk_asrc_m cx ly S W m1 m2 md _ h HB HAR HK HP Hs (rkk_slot_loc cx j HB Hj)).
Qed.

Lemma rkk_digits : forall f x acc, (length (printf_facts_c.pf_digits f x acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc; cbn [printf_facts_c.pf_digits]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|].
  specialize (IH (x / 10) (48 + x mod 10 :: acc)). cbn [length] in IH. lia.
Qed.

Lemma rkk_pre_len : forall cx, (length (gpre cx) <= 27)%nat.
Proof.
  intros cx. unfold gpre, relay_instance_gone_b_c.instance_prefix, printf_facts_c.pf_dec, RelayModel.K_GESTURE.
  rewrite !length_app.
  destruct (gxID cx <? 0).
  - pose proof (rkk_digits 11 (- gxID cx) []) as H. cbn [length] in H |- *. lia.
  - pose proof (rkk_digits 11 (gxID cx) []) as H. cbn [length] in H |- *. lia.
Qed.

(* the journal's allocator state, and the fake frame among its frames *)
Lemma rkk_jar : forall cx fpos ly1 S1 W1 m1 md1 k1,
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  ARh ly1 S1 W1 m1 md1 /\ In (1, fpos) (frames S1).
Proof.
  intros cx fpos ly1 S1 W1 m1 md1 k1 HJ.
  destruct HJ as (_ & _ & (memS & HJ' & _) & _).
  destruct HJ' as (HAR & _ & _ & _ & _ & Hfrs & _).
  split; [exact HAR|]. rewrite Hfrs. apply in_or_app. left. left. reflexivity.
Qed.

(* ---- 1. GIN ---- *)
Theorem rkk_gin : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 m2,
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  g_frame cx fpos F FL ly1 W1 m1 ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  rkk_KEEP cx W1 m1 m2 -> rkk_PRES W1 m1 m2 ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m2.
Proof.
  intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 md1 k1 m2
    HB HJ HF HG HK HP.
  destruct (rkk_jar cx fpos ly1 S1 W1 m1 md1 k1 HJ) as [HAR Hfr].
  destruct HF as (HFa & _).
  destruct (rk_fb ly1 S1 W1 m1 md1 1 fpos HAR Hfr) as (HF4 & HFc & _).
  rewrite HFa in HF4, HFc. change (fs_frame_bytes 1) with 128 in HFc.
  pose proof asan_consts as (C1 & _).
  assert (KC : forall a, 0 <= a < alloc_ceiling -> abyte_kept W1 m1 W1 m2 a)
    by (intros a Ha; exact (rkk_kept_c cx W1 m1 m2 a HB HK HP Ha)).
  unfold GIN in HG |- *. cbv zeta in HG |- *.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
  do 8 (split; [assumption|]).
  split.
  { destruct (rkk_arelay cx ly1 S1 W1 m1 md1 _ _ HB HAR G9) as [L Bl].
    exact (arelay_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ G9 (rkk_akept cx W1 m1 m2 _ HB HK HP L) Bl). }
  split.
  { destruct (rkk_aout cx ly1 S1 W1 m1 md1 _ _ _ _ _ _ HB HAR G10) as [L Bl].
    exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ _ G10 (rkk_akept cx W1 m1 m2 _ HB HK HP L) Bl). }
  split.
  { intros i' Hi' He. apply (rkk_asrc_m cx ly1 S1 W1 m1 m2 md1 _ _ HB HAR HK HP (G11 i' Hi' He)).
    unfold gslot. apply (rkk_slot_loc cx _ HB). apply (rkk_j4 cx i' HB); [lia | exact He]. }
  split.
  { intros Ho. apply (rkk_asrc_m cx ly1 S1 W1 m1 m2 md1 _ _ HB HAR HK HP (G12 Ho)).
    unfold gslot. apply (rkk_slot_loc cx _ HB). apply (rkk_j4 cx i HB G1). apply Z.eqb_eq. exact Ho. }
  split.
  { rewrite Forall_forall in G13 |- *. intros p Hp Heof.
    exact (rkk_drsrc cx ly1 S1 W1 m1 m2 md1 _ _ _ HB HAR HK HP (G13 p Hp Heof)). }
  split.
  { intros a Ha Hj. destruct (G14 a Ha Hj) as [V Wr].
    destruct (KC a (rkk_glob cx a HB ltac:(tauto))) as [V2 Wr2].
    unfold abyte_kept. split; [rewrite V2; exact V | intros Hw; apply Wr2; apply Wr; exact Hw]. }
  split; [exact G15|].
  split.
  { apply (akept_garr8 W1 m1); [|exact G16]. intros x Hx. apply KC.
    pose proof (rkk_pre_len cx). rewrite length_app in Hx. cbn [length] in Hx. lia. }
  split.
  { apply (akept_garr8 W1 m1); [|exact G17]. intros x Hx. apply KC.
    assert (HF8 : 0 <= F / 8 <= 2 ^ 45) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    cbn [length] in Hx. unfold shadow_addr, SHADOW_OFF in Hx. lia. }
  exact G18.
Qed.

(* ---- 2. GLIVE ---- *)
Theorem rkk_live : forall cx F FL fpos ly1 S1 W1 m1 md1 k1 m2 md2 k2,
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 -> alock_at RG W1 m1 true ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m2 md2 k2 ->
  rkk_KEEP cx W1 m1 m2 -> rkk_PRES W1 m1 m2 ->
  GLIVE B PST ARx RG cx F FL ly1 S1 W1 m2 md2 k2.
Proof.
  intros cx F FL fpos ly1 S1 W1 m1 md1 k1 m2 md2 k2 HB HJ HR HA HF HL HJ2 HK HP.
  destruct (rkk_jar cx fpos ly1 S1 W1 m1 md1 k1 HJ) as [HAR Hfr].
  destruct (rk_fb ly1 S1 W1 m1 md1 1 fpos HAR Hfr) as (HF4 & HFc & _).
  change (fs_frame_bytes 1) with 128 in HFc.
  assert (KC : forall a, 0 <= a < alloc_ceiling -> abyte_kept W1 m1 W1 m2 a)
    by (intros a Ha; exact (rkk_kept_c cx W1 m1 m2 a HB HK HP Ha)).
  assert (KH : forall a, gsp1 cx <= a < gsp0 cx -> abyte_kept W1 m1 W1 m2 a)
    by (intros a Ha; exact (rkk_kept_hi cx W1 m1 m2 a HK HP Ha)).
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  unfold GLIVE. exists fpos, []. split; [rewrite (rk_gxHp cx HB); exact HJ2|].
  split.
  { intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
    destruct (KC a (rkk_img a Hi)) as [V _]. rewrite V. exact (HR a Ha). }
  split.
  { intros a Ha1 Ha2 Ha3 Ha4. apply HP. exact (HA a Ha1 Ha2 Ha3 Ha4). }
  split.
  { destruct HF as (HFa & HFl & H120 & H16 & H24 & H80 & Hsv).
    rewrite HFa in HF4, HFc.
    unfold g_frame. split; [exact HFa|]. split; [exact HFl|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; change (Z.of_nat 8) with 8 in Hx; lia | exact H120]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H16]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H24]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H80]|].
    intros j Hj. apply (akept_vm W1 m1); [|exact (Hsv j Hj)].
    intros x Hx. apply KH. change (Z.of_nat 8) with 8 in Hx. lia. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HL). intros r Hr a Ha. destruct Hr as [<-|[]].
  apply KC. cbn [fst snd] in Ha. apply (rkk_glob cx a HB). tauto.
Qed.

(* ---- 3. the loop's frame slots ---- *)
Theorem rkk_lslots : forall cx F W1 m1 m2, g_lslots RG cx F W1 m1 -> rkk_KEEP cx W1 m1 m2 -> g_lslots RG cx F W1 m2.
Proof.
  intros cx F W1 m1 m2 (H40 & H48 & H56 & H64 & H72) HK.
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  assert (V : forall a, gsp1 cx + 40 <= a < gsp1 cx + 80 -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a)
    by (intros a Ha; apply (rkk_view_hi cx W1 m1 m2 a HK); lia).
  unfold g_lslots.
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H40]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H48]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H56]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H64]|].
  apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H72].
Qed.


Let RUN := paj_run_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let BR := paj_branch (PI := PI).

Definition rk_extra (hp hpn key nh : Z) : list word := map (Z_to_bv 64) [hp; hpn; key; nh].
Definition rk_sh (b : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff b 0) (SLit 3)) (SOff 18 0).
Definition rk_regs : list sv := sr_set (sr_set sr_atoms 27%bv (rk_sh 25)) 22%bv (rk_sh 23).
Definition rk_regions : smem :=
[ YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))] ].
Definition PTRK (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition rk_atoms : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (18%nat, mkAF SB SB 0); (19%nat, mkAF 0 (2^29) 3); (21%nat, mkAF 0 (2^26) 0);
  (23%nat, PTRK 3); (25%nat, PTRK 3); (32%nat, PTRK 3); (33%nat, PTRK 3); (34%nat, PTRK 0); (35%nat, mkAF 1 (2^26) 0) ].
Definition rk_alias : sv * sv := (SAlu ALU_ADD (SOff 32 0) (SOff 19 0), SOff 33 0).
Definition rk_facts : facts := mkFacts rk_atoms [] [rk_alias].
Definition ss_k : sstate := mkSS A_rig_inner rk_regs rk_regions None rk_facts.
Definition rk_SH : list shent := [ mkSHE 25 0 8; mkSHE 23 0 8; mkSHE 33 0 8 ].
Definition rk_Bx : sv := SOff 18 0.
Definition rk_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma rk_add64 : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b Ha Hb Hab. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. lia.
Qed.

(* the three shadow entries of the walk, at any memory where the table and the held array are live blocks *)
Lemma rk_shok : forall E W ly S m md SA G0 hp kh n nh,
ARh ly S W m md ->
ew E 18 = w64 SHADOW_OFF -> ew E 23 = w64 (SA + 48) -> ew E 25 = w64 (SA + 40) -> ew E 33 = Z_to_bv 64 (hp + 8 * n) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh ->
sh_ok SEGS rk_Bx rk_SH E (mrestrict (w_H W) m).
Proof.
intros E W ly S m md SA G0 hp kh n nh HAR E18 E23 E25 E33 HinT HT1 HT2 Hinh Hkh Hn.
destruct (rk_alb ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & _ & _ & _).
destruct (rk_alb ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _ & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
unfold sh_ok, rk_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 25 (SA + 40) 8 (SA + 40) 0 8).
  + apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
  + unfold rk_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E25 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 23 (SA + 48) 8 (SA + 48) 0 8).
  + apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
  + unfold rk_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E23 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 33 (hp + 8 * n) 8 (hp + 8 * n) 0 8).
  + apply (rk_rab ly S W m md hp kh); [exact HAR | exact Hinh | lia | lia].
  + unfold rk_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E33 | lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* The symbolic state at the inner loop's head (RGI, 0x82e50): s9 = SA + 40 (atom 25) and s7 = SA + 48 (atom 23) with
   their shadow addresses in s11 / s6 as formulas over s2 = SHADOW_OFF (atom 18); held = hp (atom 32), held + 8 n
   (atom 33, the alias), held[n] = the key (atom 34), nheld (atom 35). *)
Lemma rk_st_gen : forall pc tl W ly S regs m md sp SA G0 hp kh n nh key,
ARh ly S W m md ->
spZ regs = sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 19 = w64 (8 * n) -> getr regs 21 = w64 n ->
getr regs 23 = w64 (SA + 48) -> getr regs 22 = w64 (SHADOW_OFF + (SA + 48) / 8) ->
getr regs 25 = w64 (SA + 40) -> getr regs 27 = w64 (SHADOW_OFF + (SA + 40) / 8) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE -> SA mod 8 = 0 ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh -> nh < 2 ^ 26 ->
4096 <= key < 140737479966720 ->
(hp + 8 * n + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * n) ->
val_mem SEGS (arm W m) (SA + 40) 8 hp -> val_mem SEGS (arm W m) (SA + 48) 4 nh ->
val_mem SEGS (arm W m) (hp + 8 * n) 8 key ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (map (Z_to_bv 64) ([hp; hp + 8 * n; key; nh] ++ tl)))) (mkSS pc rk_regs rk_regions None rk_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
sh_ok SEGS rk_Bx rk_SH (Eimg (Ereg regs (map (Z_to_bv 64) ([hp; hp + 8 * n; key; nh] ++ tl)))) (mrestrict (w_H W) m).
Proof.
intros pc tl W ly S regs m md sp SA G0 hp kh n nh key HAR Hsp Hsp1 Hsp16 R18 R19 R21 R23 R22 R25 R27 HinT HT1 HT2 HSA8
  Hinh Hkh Hn Hnh Hkey Hdis Mhp Mnh Mkey.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (rk_alb ly S W m md G0 ATABLE HAR HinT) as (HT16 & HT4096 & HTceil & HTapp & HTpres & _ & _).
destruct (rk_alb ly S W m md hp kh HAR Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
change (req_size ATABLE) with 896 in *. unfold AENT, ATABLE in *.
pose proof (req_size_pos kh ltac:(lia)) as [Hrk1 Hrk2].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (map (Z_to_bv 64) ([hp; hp + 8 * n; key; nh] ++ tl)))). pose proof pa_B_ok as HBASE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 (8 * n)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = w64 n) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E23 : ew E 23 = w64 (SA + 48)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = w64 (SA + 40)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (SHEQ : forall b x, ew E b = w64 x -> 0 <= x < 2 ^ 60 ->
  sv_denot E (rk_sh b) = w64 (SHADOW_OFF + x / 8)).
{ intros b x Hb Hx. unfold rk_sh. cbn [sv_denot]. rewrite Hb, E18, !Z.add_0_r, !Z_to_bv_bv_unsigned.
  assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia. }
assert (HS0 : st_ok_pi SEGS VAL E (mkSS pc rk_regs rk_regions None (mkFacts rk_atoms [] [])) (mkst regs (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) m) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  - unfold rk_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
    + rewrite (SHEQ 25%nat (SA + 40) E25) by lia. exact R27.
    + rewrite (SHEQ 23%nat (SA + 48) E23) by lia. exact R22.
  - vm_compute. reflexivity.
  - unfold rk_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 25%nat (SA + 40) E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 40) 0 8 (SOff 32 0) hp);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mhp].
    + rewrite (VB 23%nat (SA + 48) E23) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (HTpres (SA + 48 + o)); lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SA + 48) 0 4 (SOff 35 0) nh);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mnh].
    + rewrite (VB 33%nat (hp + 8 * n) E33) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (Hhpres (hp + 8 * n + o)); lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (hp + 8 * n) 0 8 (SOff 34 0) key);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mkey].
  - apply pairwise_disjoint_of_extents. unfold rk_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 25%nat (SA + 40) E25) by lia. rewrite (VB 23%nat (SA + 48) E23) by lia.
    rewrite (VB 33%nat (hp + 8 * n) E33) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
  - split; [|split; [exact I | exact I]].
    cbn [rk_atoms f_atoms atoms_ok]. unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2].
    rewrite Usp, E18, E19, E21, E23, E25, E32, E33, E34, E35.
    unfold w64. rewrite !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try lia.
    + replace (8 * n) with (n * 8) by lia. apply Z_mod_mult.
    + replace (SA + 48) with ((SA / 8 + 6) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia). apply Z_mod_mult.
    + replace (SA + 40) with ((SA / 8 + 5) * 8) by (pose proof (Z.div_mod SA 8 ltac:(lia)); lia). apply Z_mod_mult.
    + replace hp with ((2 * (hp / 16)) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia). apply Z_mod_mult.
    + replace (hp + 8 * n) with ((2 * (hp / 16) + n) * 8) by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia). apply Z_mod_mult. }
split.
- assert (ALIAS : sv_denot E (SAlu ALU_ADD (SOff 32 0) (SOff 19 0)) = sv_denot E (SOff 33 0)).
  { cbn [sv_denot]. rewrite E32, E19, E33. unfold w64. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
    apply rk_add64; lia. }
  exact (st_ok_pi_add_alias E (mkSS pc rk_regs rk_regions None (mkFacts rk_atoms [] [])) _ _ _ HS0 ALIAS).
- unfold sh_ok, rk_SH. constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 25 (SA + 40) 8 (SA + 40) 0 8).
    * apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
    * unfold rk_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
    * apply U_atom; [exact E25 | lia].
    * lia.
    * lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 23 (SA + 48) 8 (SA + 48) 0 8).
    * apply (rk_rab ly S W m md G0 ATABLE); [exact HAR | exact HinT | lia | change (req_size ATABLE) with 896; lia].
    * unfold rk_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
    * apply U_atom; [exact E23 | lia].
    * lia.
    * lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W) m E rk_Bx 33 (hp + 8 * n) 8 (hp + 8 * n) 0 8).
    * apply (rk_rab ly S W m md hp kh); [exact HAR | exact Hinh | lia | lia].
    * unfold rk_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
    * apply U_atom; [exact E33 | lia].
    * lia.
    * lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma rk_entry_st : forall W ly S regs m md sp SA G0 hp kh n nh key,
ARh ly S W m md ->
spZ regs = sp -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 19 = w64 (8 * n) -> getr regs 21 = w64 n ->
getr regs 23 = w64 (SA + 48) -> getr regs 22 = w64 (SHADOW_OFF + (SA + 48) / 8) ->
getr regs 25 = w64 (SA + 40) -> getr regs 27 = w64 (SHADOW_OFF + (SA + 40) / 8) ->
In (G0, ATABLE) (ablocks B ly S) -> G0 <= SA -> SA + AENT <= G0 + ATABLE -> SA mod 8 = 0 ->
In (hp, kh) (ablocks B ly S) -> 8 * nh <= kh -> 0 <= n < nh -> nh < 2 ^ 26 ->
4096 <= key < 140737479966720 ->
(hp + 8 * n + 8 <= SA + 40 \/ SA + 52 <= hp + 8 * n) ->
val_mem SEGS (arm W m) (SA + 40) 8 hp -> val_mem SEGS (arm W m) (SA + 48) 4 nh ->
val_mem SEGS (arm W m) (hp + 8 * n) 8 key ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh))) ss_k
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rig_inner)) m (seg_rom SEGS))) /\
sh_ok SEGS rk_Bx rk_SH (Eimg (Ereg regs (rk_extra hp (hp + 8 * n) key nh))) (mrestrict (w_H W) m).
Proof. intros. exact (rk_st_gen A_rig_inner [] W ly S regs m md sp SA G0 hp kh n nh key ltac:(assumption)
  ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
  ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
  ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
  ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)). Qed.


(* ---- small list / block facts ---- *)
(* the live blocks are pairwise distinct: their extents are pairwise apart and non-empty (AR_sep_law) *)
Lemma rk_ablocks_nodup : forall ly S W m md, ARh ly S W m md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W m md HAR.
destruct (rk_als ly S W m md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
{ intros [p nn] Hin. destruct (rk_alb ly S W m md p nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  exact (proj1 (req_size_pos nn ltac:(lia))). }
revert Hpw Hpos. generalize (ablocks B ly S). intros l. induction l as [|x l IH]; intros Hpw Hpos; [constructor|].
cbn [map pairwise] in Hpw. destruct Hpw as [H1 H2]. constructor.
- intros Hin. rewrite Forall_forall in H1. pose proof (H1 _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin)) as Hd.
  pose proof (Hpos x (or_introl eq_refl)). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply IH; [exact H2 | intros b Hb; apply Hpos; right; exact Hb].
Qed.
Lemma rk_garr8_aview : forall H (m : word -> option byte) a l j, garr8 SEGS (mrestrict H m) a l -> (j < length l)%nat ->
aview SEGS H m (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H m _ _ Hv Hr). Qed.
Lemma rk_pw_in : forall {A T : Type} (R : T -> T -> Prop) (f : A -> T) l x y,
pairwise R (map f l) -> In x l -> In y l -> x <> y -> R (f x) (f y) \/ R (f y) (f x).
Proof.
intros A T R f l. induction l as [|a l IH]; intros x y Hp Hx Hy Hxy; [destruct Hx|].
cbn [map pairwise] in Hp. destruct Hp as [H1 H2]. rewrite Forall_forall in H1.
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- exfalso. apply Hxy. reflexivity.
- left. apply H1. apply in_map. exact Hy.
- right. apply H1. apply in_map. exact Hx.
- exact (IH x y H2 Hx Hy Hxy).
Qed.
Lemma rk_blk_apart : forall ly S W m md b1 b2, ARh ly S W m md ->
In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
fst b1 + req_size (snd b1) <= fst b2 \/ fst b2 + req_size (snd b2) <= fst b1.
Proof.
intros ly S W m md [p1 n1] [p2 n2] HAR H1 H2 Hne.
destruct (rk_alb ly S W m md p1 n1 HAR H1) as (_ & _ & _ & _ & _ & Hpw & _).
destruct (rk_pw_in zdisjoint (fun b => (fst b, req_size (snd b))) _ _ _ Hpw H1 H2 Hne) as [Hd | Hd];
unfold zdisjoint in Hd; cbn [fst snd] in *; lia.
Qed.
Lemma rk_mod_sp : forall x, x mod 32 = 0 -> (x - 224) mod 16 = 0.
Proof.
intros x Hx. replace (x - 224) with ((2 * (x / 32) - 14) * 16) by (pose proof (Z.div_mod x 32 ltac:(lia)); lia).
apply Z_mod_mult.
Qed.
Lemma rk_mod_sa : forall g i, g mod 16 = 0 -> (g + 56 * i) mod 8 = 0.
Proof.
intros g i Hg. replace (g + 56 * i) with ((2 * (g / 16) + 7 * i) * 8) by (pose proof (Z.div_mod g 16 ltac:(lia)); lia).
apply Z_mod_mult.
Qed.
Lemma rk_pw_app : forall {T : Type} (R : T -> T -> Prop) l1 l2 x y, pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros T R l1. induction l1 as [|a l1 IH]; intros l2 x y Hp Hx Hy; [destruct Hx|].
cbn [app pairwise] in Hp. destruct Hp as [H1 H2]. rewrite Forall_forall in H1.
destruct Hx as [<- | Hx]; [apply H1; apply in_or_app; right; exact Hy | exact (IH l2 x y H2 Hx Hy)].
Qed.
Lemma rk_frame_blk_apart : forall ly S W m md cid pos p nn, ARh ly S W m md -> In (cid, pos) (frames S) ->
In (p, nn) (ablocks B ly S) ->
frame_addr ly cid pos + fs_frame_bytes cid <= p \/ p + req_size nn <= frame_addr ly cid pos.
Proof.
intros ly S W m md cid pos p nn HAR Hf Hb. destruct (rk_als ly S W m md HAR) as [Hpw _].
pose proof (rk_pw_app zdisjoint _ _ (p, req_size nn) (frame_addr ly cid pos, fs_frame_bytes cid) Hpw
  ltac:(apply (in_map (fun b => (fst b, req_size (snd b))) _ (p, nn)); exact Hb)
  ltac:(apply (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos)); exact Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma rk_nodup_app_disj : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 x HN H1 H2; [destruct H1|].
cbn [app] in HN. apply List.NoDup_cons_iff in HN as [Hna HN].
destruct H1 as [<- | H1]; [apply Hna; apply in_or_app; right; exact H2 | exact (IH l2 x HN H1 H2)].
Qed.
Lemma rk_nodup_app_r : forall {A : Type} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 HN; [exact HN|].
cbn [app] in HN. apply List.NoDup_cons_iff in HN as [_ HN]. exact (IH l2 HN).
Qed.
Lemma rk_view_garr8 : forall H (m : word -> option byte) a l k, garr8 SEGS (mrestrict H m) a l -> 0 <= k < Z.of_nat (length l) ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a l k Hg Hk. destruct (Hg (Z.to_nat k) ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r, Z2Nat.id in Hv by lia.
unfold aview. rewrite Hv. discriminate.
Qed.
Lemma rk_garr8_kv : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.
(* the three blocks of entry i the walk reads (table, held array, a key) are three distinct live blocks *)
Lemma rk_perm_entry : forall (X : list (Z * Z)) G T A e C rest k, List.NoDup X ->
Permutation X ((G, T) :: concat (map aentry_blks (A ++ e :: C)) ++ rest) -> re_hp e <> 0 -> In k (re_keys e) ->
(G, T) <> (re_hp e, re_kh e) /\ (G, T) <> (key_addr k, Z.of_nat (length (key_text k)) + 1) /\
(re_hp e, re_kh e) <> (key_addr k, Z.of_nat (length (key_text k)) + 1).
Proof.
intros X G T A e C rest k HN HP Hhp Hk.
pose proof (Permutation_NoDup HP HN) as HN2.
rewrite map_app, concat_app in HN2. cbn [map concat] in HN2.
unfold aentry_blks at 2 in HN2. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) Hhp) in HN2.
set (bp := if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) in HN2.
set (kp := map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1)) (re_keys e)) in HN2.
assert (Hkin : In (key_addr k, Z.of_nat (length (key_text k)) + 1) kp)
  by (apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))); exact Hk).
apply List.NoDup_cons_iff in HN2 as [Hnh HN3].
split; [|split].
- intros Heq. apply Hnh. rewrite Heq. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left.
  apply in_or_app. right. left. reflexivity.
- intros Heq. apply Hnh. rewrite Heq. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left.
  apply in_or_app. right. right. exact Hkin.
- intros Heq. rewrite <- !app_assoc in HN3. apply (rk_nodup_app_r (concat (map aentry_blks A))) in HN3. apply (rk_nodup_app_r bp) in HN3. cbn [app] in HN3.
  apply List.NoDup_cons_iff in HN3 as [Hn _]. apply Hn. rewrite Heq. apply in_or_app. left. exact Hkin.
Qed.

Definition rk_X0 (cx : gcx) : list (Z * Z) :=
(gxG0 cx, ATABLE) :: concat (map aentry_blks (gxes cx)) ++ rig_srcs (gps cx) ++ aout_blks (gxcap cx) (gxout cx).
Lemma rk_wr_blk : forall cx ly1 S1 W1 m1 md1 X own b nb a,
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
Permutation (ablocks B ly1 S1) (X ++ gxrest cx) -> In (b, nb) X -> b <= a < b + req_size nb ->
awr_byte RIG_STK_x (gsp0 cx) (gFP cx) (ablocks B (gxly cx) (gxS cx)) (ablocks B ly1 S1) ly1 own a.
Proof.
intros cx ly1 S1 W1 m1 md1 X own b nb a HAR HPZ0 HP1 HX Ha.
assert (Hin1 : In (b, nb) (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; left; exact HX).
assert (DEC : forall x y : Z * Z, {x = y} + {x <> y})
  by (intros [x1 x2] [y1 y2]; destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
      [left; congruence | right; congruence | right; congruence | right; congruence]).
destruct (in_dec DEC (b, nb) (ablocks B (gxly cx) (gxS cx))) as [Hin0 | Hnin0].
- right. left. split; [|exists b, nb; split; [exact Hin1 | exact Ha]].
  apply (Permutation_in _ HPZ0) in Hin0. apply in_app_or in Hin0 as [HX0 | Hrest].
  + unfold gFP, rig_fp. replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp _ b nb); [exact HX0 | lia].
  + exfalso. pose proof (Permutation_NoDup HP1 (rk_ablocks_nodup _ _ _ _ _ HAR)) as HN.
    exact (rk_nodup_app_disj X (gxrest cx) (b, nb) HN HX Hrest).
- right. right. left. exists b, nb. split; [exact Hin1|]. split; [exact Hnin0 | exact Ha].
Qed.
(* A call to a program function inside the walk (W_gesture_end.v's gx_callS, reproved here because W_gesture_end.v
   does not build under ge_spec's new room premise): the callee's contract applied at its entry, its journal composed
   into the caller's (W_journal.v ajournal_gx_sub). *)
Lemma rk_callS : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc [] W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK1 (spZ regsc) FP1 lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + k1) /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK1 (sp0 + o) FP1 lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee.
  destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S [] W0 memS md own lyc Sc [] W memc mdc k regsc STK1 o ch1 HJi); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub_x SEGS B PST ARx LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
(* a byte of a live block the walk owns (not in gxrest) is in the entry's footprint or in a block made since *)
Lemma rk_fp_blk : forall cx ly1 S1 W1 m1 md1 X b nb a,
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
Permutation (ablocks B ly1 S1) (X ++ gxrest cx) -> In (b, nb) X -> b <= a < b + req_size nb ->
(inFP (gFP cx) a /\ exists b' n', In (b', n') (ablocks B ly1 S1) /\ b' <= a < b' + req_size n') \/
in_tmp_block (ablocks B (gxly cx) (gxS cx)) (ablocks B ly1 S1) a.
Proof.
intros cx ly1 S1 W1 m1 md1 X b nb a HAR HPZ0 HP1 HX Ha.
assert (Hin1 : In (b, nb) (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_or_app; left; exact HX).
assert (DEC : forall x y : Z * Z, {x = y} + {x <> y})
  by (intros [x1 x2] [y1 y2]; destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
      [left; congruence | right; congruence | right; congruence | right; congruence]).
destruct (in_dec DEC (b, nb) (ablocks B (gxly cx) (gxS cx))) as [Hin0 | Hnin0].
- left. split; [|exists b, nb; split; [exact Hin1 | exact Ha]].
  apply (Permutation_in _ HPZ0) in Hin0. apply in_app_or in Hin0 as [HX0 | Hrest].
  + unfold gFP, rig_fp. replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp _ b nb); [exact HX0 | lia].
  + exfalso. pose proof (Permutation_NoDup HP1 (rk_ablocks_nodup _ _ _ _ _ HAR)) as HN.
    exact (rk_nodup_app_disj X (gxrest cx) (b, nb) HN HX Hrest).
- right. exists b, nb. split; [exact Hin1|]. split; [exact Hnin0 | exact Ha].
Qed.
(* W_gesture_end.v's ajgx_keep_high / ajgx_ly_top, reproved (W_gesture_end.v does not build under the new ge_spec) *)
Lemma rk_gx_keep_high : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma rk_gx_ly_top : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k -> ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* the frame-pointer chain at a call from the loop, its frame record named: relay_instance_gone's saved ra / s0
   (slots 216(sp) / 208(sp) of the 224-byte frame, at gsp0 - 8 / gsp0 - 16) pushed on the entry's chain (afn_pre's
   achain), when the entry's frame lies below the layout top *)
Lemma rk_chain2p : forall cx own ly1 S1 W1 m1 md1 k1,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) own ly1 S1 [] W1 m1 md1 k1 ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 8) 8 (bv_unsigned (getr (gxregs cx) 1)) ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 16) 8 (bv_unsigned (getr (gxregs cx) 8)) ->
gsp0 cx < ly_top ly1 - 16 ->
achain ly1 (aview SEGS (w_H W1) m1) (gsp0 cx + -224) (gsp0 cx) ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx).
Proof.
intros cx own ly1 S1 W1 m1 md1 k1 HB HJ V1 V8 Hlt.
pose proof HB as (HPRE0 & H32 & _). pose proof HPRE0 as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity.
pose proof (rk_gx_ly_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as ETop.
fold (gsp0 cx) in *.
apply (achain_ly_top (gxly cx) ly1); [exact ETop|].
apply (achain_push (gxly cx) (aview SEGS (w_H (gxW cx)) (gxmem cx))); [exact Hch | lia | | | | exact Hra4 | lia | | rewrite <- ETop; lia | lia].
- intros a Ha. apply (rk_gx_keep_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGRIG HJ); lia.
- apply (rdword_of_val_mem SEGS). exact V1. apply bv_unsigned_in_range.
- apply (rdword_of_val_mem SEGS). exact V8. apply bv_unsigned_in_range.
- replace (gsp0 cx) with (8 * (2 * (gsp0 cx / 16))) by (pose proof (Z.div_mod (gsp0 cx) 16 ltac:(lia)); lia).
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
(* the frame-pointer chain at a call from the loop, from the two saved words (ra, s0) of relay_instance_gone's frame *)
Lemma rk_chain2 : forall cx own ly1 S1 W1 m1 md1 k1,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) own ly1 S1 [] W1 m1 md1 k1 ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 8) 8 (bv_unsigned (getr (gxregs cx) 1)) ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 16) 8 (bv_unsigned (getr (gxregs cx) 8)) ->
exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (gsp0 cx + -224) (gsp0 cx) ch1.
Proof.
intros cx own ly1 S1 W1 m1 md1 k1 HB HJ V1 V8.
destruct (Z_lt_le_dec (gsp0 cx) (ly_top ly1 - 16)) as [Hlt | Hge].
- exists ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx). exact (rk_chain2p cx own ly1 S1 W1 m1 md1 k1 HB HJ V1 V8 Hlt).
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
(* the two saved words of g_saved used by the chain *)
Lemma rk_saved_ra_s0 : forall cx W1 m1, g_saved cx W1 m1 ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 8) 8 (bv_unsigned (getr (gxregs cx) 1)) /\
val_mem SEGS (arm W1 m1) (gsp0 cx - 16) 8 (bv_unsigned (getr (gxregs cx) 8)).
Proof.
intros cx W1 m1 HSV. split.
- pose proof (HSV 12%nat ltac:(lia)) as V. cbn [nth RIG_SAVED] in V.
  replace (gsp1 cx + 120 + 8 * Z.of_nat 12) with (gsp0 cx - 8) in V by (unfold gsp1, RIG_FRAME; cbn; lia). exact V.
- pose proof (HSV 11%nat ltac:(lia)) as V. cbn [nth RIG_SAVED] in V.
  replace (gsp1 cx + 120 + 8 * Z.of_nat 11) with (gsp0 cx - 16) in V by (unfold gsp1, RIG_FRAME; cbn; lia). exact V.
Qed.
Lemma rk_sends_cap : forall mx c O cap Bs, 0 <= cap -> 0 <= snd (sl_sends mx c O cap Bs).
Proof.
intros mx c O cap Bs. revert c O cap. induction Bs as [|Bl r IH]; intros c O cap Hc; cbn [sl_sends]; [exact Hc|].
apply IH. pose proof (rkb_sl_cap_ge c mx (Z.of_nat (length O)) cap (Z.of_nat (length Bl)) Hc). lia.
Qed.
Lemma rk_aout_blk : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
(cap = 0 /\ out = 0 /\ no = 0) \/ (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S)).
Proof.
intros ly S W mem c O mx no cap out
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmx & Hno & Hd).
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.
(* gesture_end's room and the meter for gesture_end then free, from GIN at a key with the prefix; and the room
   record's premises of both calls: gesture_end's MT_rk charge, then the free's 1, then rk_krn (what the requests after
   the key owe), all inside GIN's budget; gesture_end's count premise (peak 3 under GIN's peak + 3) and the free's
   (the live counts at most one above GIN's, under the same 3) *)
Lemma rk_room : forall cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA,
GBASE B ARx MT RP MMAX RG cx ->
GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ->
has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
tr_max (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) < MMAX /\
blocks_bytes S1 + tr_peak (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) <= LIVE_MAX /\
mo_ok MT S1 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) /\
0 < Z.of_nat (length (key_text (nth n ks (0, [], [])))) /\ 0 <= cap2 /\
rp_RM RP S1 (Z.to_nat (ge_cost MT_rk c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
  + S (rk_krn cx i n ks f c2 O2 cap2)) /\
cnt_ok_pk RP ge_pk (ablocks B ly1 S1) /\
(forall l, (forall P, (ReplyCnt.acnt P l <= ReplyCnt.acnt P (ablocks B ly1 S1) + 1)%nat) -> cnt_ok RP l).
Proof.
intros cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA HB H Hp.
pose proof (rkb_live_gin cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA H) as HL.
destruct (rkb_gbase_facts cx HB) as (Hmx & _ & _).
unfold GIN in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & Hs & Hk & Hf & Hg & Har & Hout & _ & _ & _ & _ & _ & _ & _ & Hbud).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkb_aout_cap _ _ _ _ _ _ _ _ _ _ Hout) as Hcap.
assert (Hxl : 0 < Z.of_nat (length (key_text (nth n ks (0, [], []))))).
{ destruct Har as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hent & _).
  rewrite Forall_forall in Hent.
  assert (Hin : In (entry_keys e1 ks) (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx)))
    by (apply in_or_app; right; left; reflexivity).
  destruct (Hent _ Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF).
  change (re_keys (entry_keys e1 ks)) with ks in HF. rewrite Forall_forall in HF.
  assert (Hk0 : In (nth n ks (0, [], [])) ks) by (apply nth_In; exact Hn).
  destruct (HF _ Hk0) as (_ & _ & _ & Hr). lia. }
destruct f as [|f0]; [lia|].
unfold rk_krn, rk_tl. cbn [Nat.pred]. cbv zeta.
rewrite (rkb_geik_end f0 (gpre cx) n ks Hn Hp) in Hbud. cbn [fst] in Hbud.
set (Er := fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks))) in *.
set (k := nth n ks (0, [], [])) in *.
assert (Ek : sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (k :: Er)) =
  sl_sends (gxmx cx) (ge_ctl c2 (Z.of_nat (length (key_text k)))) (ge_O c2 O2 (key_text k))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text k)))) (ge_bytes Er)).
{ change (ge_bytes (k :: Er)) with (ge_bytes [k] ++ ge_bytes Er). rewrite rkb_sends_app, rkb_sends_key. reflexivity. }
assert (Hc3 : 0 <= snd (sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (k :: Er)))) by (apply rk_sends_cap; exact Hcap).
rewrite Ek in Hbud, Hc3. revert Hbud Hc3.
destruct (sl_sends (gxmx cx) (ge_ctl c2 (Z.of_nat (length (key_text k)))) (ge_O c2 O2 (key_text k))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text k)))) (ge_bytes Er)) as [[c3 O3] cap3].
intros Hbud Hc3. cbv beta iota in Hbud |- *. cbn [snd] in Hc3. rewrite rkb_ge_O_len.
pose proof (rkb_grest_sizes cx (S i) (Z.of_nat (length O3)) cap3 HB ltac:(lia) Hc3) as HGs.
destruct (rkb_ge_room cx ly1 S1 spent c2 (Z.of_nat (length O2)) cap2 k Er (grest cx (S i) (Z.of_nat (length O3)) cap3)
  Hbud HGs HL ltac:(lia) ltac:(lia) Hcap Hxl) as (R1 & R2 & R3).
pose proof (rkb_ge_rm cx ly1 S1 spent c2 (Z.of_nat (length O2)) cap2 k Er (grest cx (S i) (Z.of_nat (length O3)) cap3)
  Hbud HGs HL ltac:(lia) ltac:(lia) Hcap Hxl) as RMg.
pose proof Hbud as (_ & _ & _ & _ & _ & _ & Hcn).
split; [exact R1|]. split; [exact R2|].
split.
{ apply (rkb_mok cx ly1 S1 spent _ _ HB Hbud); [|exact R3].
  pose proof (rkb_ge_cost_nonneg c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text k))) ltac:(lia) ltac:(lia) Hcap).
  pose proof (mo_free_nonneg MT MLAW). lia. }
split; [exact Hxl|]. split; [exact Hcap|]. split; [exact RMg|].
split.
- refine (cnt_ok_pk_mono RP _ ge_pk _ _ _ Hcn).
  intros P. unfold ge_pk. cbv beta. lia.
- intros l Hl. unfold cnt_ok. refine (cnt_ok_pk_mono RP _ _ _ l _ Hcn).
  intros P. pose proof (Hl P). cbv beta. lia.
Qed.
(* a block of the journal's start state, live at its end and outside its footprint, keeps its bytes *)
Lemma rk_keep_blk : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
gx_ok SEGS B G -> ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
destruct (rk_alb ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
pose proof asan_consts as (C1 & _).
rewrite unsigned_lit_small in HGa by lia.
destruct (HGx _ HGa) as [Hi' _].
pose proof (rk_boi ly' S' W' mem' md' p n HAR0 H2) as Hoff.
pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
(* a live block other than the out block survives gesture_end with its bytes *)
Lemma rk_ge_blk : forall XO OUT STK sp0 ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k cap out cap' out' rest p n,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) XO OUT STK sp0 (ablocks_fp (aout_blks cap out)) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 k ->
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) -> Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
In (p, n) (ablocks B ly1 S1) -> ~ In (p, n) (aout_blks cap out) ->
In (p, n) (ablocks B ly2 S2) /\ (forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) m2 (p + i) = aview SEGS (w_H W1) m1 (p + i)).
Proof.
intros XO OUT STK sp0 ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k cap out cap' out' rest p n HJ HAR P1 P2 Hin Hno.
assert (Hr : In (p, n) rest).
{ apply (Permutation_in _ P1) in Hin. apply in_app_or in Hin as [Ho | Hr]; [contradiction | exact Hr]. }
assert (Hin2 : In (p, n) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); apply in_or_app; right; exact Hr).
split; [exact Hin2|]. intros i Hi.
apply (rk_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n i HGRIG HJ Hin Hin2 Hi).
intros Hf. apply inFP_ablocks_fp_inv in Hf as (p' & n' & Hin' & Hpa).
assert (Hin'1 : In (p', n') (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym P1)); apply in_or_app; left; exact Hin').
assert (Hne : (p, n) <> (p', n')) by (intros E; rewrite E in Hno; exact (Hno Hin')).
pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR Hin Hin'1 Hne) as Hd. cbn [fst snd] in Hd. lia.
Qed.
(* gesture_end (key), the internal call, at relay_instance_gone's G_RIG *)
Lemma rk_ge_call : forall W regsc memc mdc STK sp0 FP ly S W0 mem md own lyc Sc k raw c O mx no cap out x q m (o : Z) ch1,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> GE_STK - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
getr regsc 10 = w64 q ->
aout_at B RG lyc Sc W memc c O mx no cap out ->
garr8 SEGS (arm W memc) q (bzs (x ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) x ->
14 <= Z.of_nat (length x) <= APARTIAL ->
In (q, m) (ablocks B lyc Sc) -> q <> out -> Z.of_nat (length x) + 1 <= req_size m ->
garr8 SEGS (arm W memc) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W memc ->
ge_room MMAX (blocks_bytes Sc) c mx no cap (Z.of_nat (length x)) ->
mo_ok MT Sc (ge_cost MT c mx no cap (Z.of_nat (length x))) ->
forall kr : nat,
rp_RM RP Sc (Z.to_nat (ge_cost MT_rk c mx no cap (Z.of_nat (length x))) + kr) ->
cnt_ok_pk RP ge_pk (ablocks B lyc Sc) ->
(forall a, inFP (ablocks_fp (aout_blks cap out)) a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1 out' kg,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + k1) /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] GE_STK (sp0 + o) (ablocks_fp (aout_blks cap out)) lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) 0 [] GE_STK (sp0 + o) (ablocks_fp (aout_blks cap out)) lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 kg /\
 aregs_preserved regsc regs2 /\ apres_kept B W memc W2 mem2 /\
 mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
 (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
   Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
 aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
   (ge_cap c mx no cap (Z.of_nat (length x))) out').
Proof.
intros W regsc memc mdc STK sp0 FP ly S W0 mem md own lyc Sc k raw c O mx no cap out x q m o ch1
  HJ Hsp Hal Hneg HSTK Hgp Htp Hra Hraw Hra4 Hch H10 HOUT GK NZ X1 Hq Hqo Hqm G5 HROM ROOM MOK kr HRM HCN HF.
eapply SRr_mono.
{ eapply (rk_callS (G_RIG B RG) W regsc memc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    GE_STK (ablocks_fp (aout_blks cap out)) o raw ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => exists out' kg,
      ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) 0 [] GE_STK (sp0 + o) (ablocks_fp (aout_blks cap out)) lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 kg /\
      apres_kept B W memc W2 mem2 /\
      mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
      (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
        Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) out')
    HGRIG HJ Hsp Hal Hneg).
  - unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK. lia.
  - exact HSTK.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - exact Hch.
  - intros HPRE1. eapply SRr_mono.
    { exact (GE W lyc Sc [] regsc memc mdc ch1 c O mx no cap out q x q m HPRE1 H10 HOUT GK NZ X1 Hq Hqo
        ltac:(lia) ltac:(lia) G5 HROM ROOM MOK kr HRM HCN). }
    cbv beta. intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & out3 & -> & HJ3 & HP3 & HA3 & HM3 & HRM3 & HPm3 & HO3).
    assert (EH3 : Hp3 = []) by (eapply rk_jhp0; exact HJ3). subst Hp3.
    exists ly3, S3, regs3, mem3, md3, k3. split; [rewrite Hra; reflexivity|].
    split; [exact (rig_lift_SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)|]. split; [exact HP3|].
    exists out3, k3. rewrite <- Hsp. split; [exact HJ3|]. split; [exact HA3|]. split; [exact HM3|]. split; [exact HRM3|].
    split; [exact HPm3 | exact HO3].
  - exact HF. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc2 & HP2 & (out' & kg & HJs & HA & HM & HRM2 & HPm & HO)).
exists ly2, S2, regs2, mem2, md2, k1, out', kg. split; [reflexivity|]. split; [exact HJ2|].
split; [exact HJc2|]. split; [exact HJs|]. split; [exact HP2|]. split; [exact HA|]. split; [exact HM|]. split; [exact HRM2|].
split; [exact HPm | exact HO].
Qed.
(* free (pa), the allocator's site rule on the inner journal, repacked over ajournal_gx *)
Lemma rk_free : forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
forall kr : nat, rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
(forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
 ~ (pa <= a < pa + req_size n) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).
Proof.
intros G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
  (H0 & H1 & (memS & HJi & Hag) & Hout) Hin H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch Hctx HFP MOK kr HRM HCN.
rewrite !Z.add_0_r in HJi.
assert (HSR : ly_bot lyc + ACALL_PREFIX < spZ regsT) by (eapply aj_stack_room_x; [exact HJi | exact Hsp | exact Hst]).
eapply SRr_mono.
{ exact (AFREE W regsT memT STK sp0 FP ly S [] W0 memS md own lyc Sc [] mdc k pa n o raw ch kr HJi Hin H10 Hsp Hal Hneg Hst
    HSR Hgp Htp Hra Hraw Hch Hctx HRM HCN HFP MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HL & HFr & HK & HM & HRM2 & HE & HPr).
assert (EH2 : Hp2 = []) by (exact (HP0 _ _ _ _ _ _ (proj1 HJ2))). subst Hp2.
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
split; [exact HP2|]. split; [exact HL|]. split; [exact HFr|]. split; [exact HK|]. split; [exact HM|]. split; [exact HRM2|].
split; [exact HE | exact HPr].
Qed.
(* a block the walk owns that was live at the entry lies in the entry's footprint *)
Lemma rk_fp_in : forall cx ly1 S1 W1 m1 md1 X b nb i,
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
Permutation (ablocks B ly1 S1) (X ++ gxrest cx) -> In (b, nb) X -> In (b, nb) (ablocks B (gxly cx) (gxS cx)) ->
0 <= i < req_size nb -> inFP (gFP cx) (b + i).
Proof.
intros cx ly1 S1 W1 m1 md1 X b nb i HAR HPZ0 HP1 HX Hin0 Hi.
apply (Permutation_in _ HPZ0) in Hin0. apply in_app_or in Hin0 as [HX0 | Hrest].
- unfold gFP, rig_fp. apply (inFP_ablocks_fp _ b nb); [exact HX0 | lia].
- exfalso. pose proof (Permutation_NoDup HP1 (rk_ablocks_nodup _ _ _ _ _ HAR)) as HN.
  exact (rk_nodup_app_disj X (gxrest cx) (b, nb) HN HX Hrest).
Qed.
Lemma rk_le_add : forall a b, 0 <= b -> a <= a + b.
Proof. intros a b H. lia. Qed.
Lemma rk_nodup_rest : forall {T : Type} (x G : T) (C D I R O gx : list T),
List.NoDup (G :: C ++ D ++ I ++ R ++ O ++ gx) -> In x (G :: C ++ D ++ I ++ R ++ O) -> ~ In x gx.
Proof.
intros T x G C D I R O gx HN Hx Hg. apply (rk_nodup_app_disj (G :: C ++ D ++ I ++ R ++ O) gx x); [| exact Hx | exact Hg].
cbn [app]. rewrite <- !app_assoc. exact HN.
Qed.
Lemma rk_nodup_head_out : forall {T : Type} (G : T) (C D I R O gx : list T),
List.NoDup (G :: C ++ D ++ I ++ R ++ O ++ gx) -> ~ In G O.
Proof.
intros T G C D I R O gx HN Hin. apply List.NoDup_cons_iff in HN as [Hn _]. apply Hn.
apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin.
Qed.
Lemma rk_nodup_far : forall {T : Type} (x y G : T) (C D I R O gx : list T),
List.NoDup (G :: C ++ D ++ I ++ R ++ O ++ gx) -> In x C -> In y O -> x <> y.
Proof.
intros T x y G C D I R O gx HN HC HO <-. apply List.NoDup_cons_iff in HN as [_ HN].
apply (rk_nodup_app_disj C (D ++ I ++ R ++ O ++ gx) x HN HC).
apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact HO.
Qed.
(* a byte of a live block that is not one of the entry's other blocks is the walk's to write *)
Lemma rk_wr_live : forall cx ly2 S2 own b nb a,
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
In (b, nb) (ablocks B ly2 S2) -> ~ In (b, nb) (gxrest cx) -> b <= a < b + req_size nb ->
awr_byte RIG_STK_x (gsp0 cx) (gFP cx) (ablocks B (gxly cx) (gxS cx)) (ablocks B ly2 S2) ly2 own a.
Proof.
intros cx ly2 S2 own b nb a HPZ0 Hin2 Hnr Ha.
assert (DEC : forall x y : Z * Z, {x = y} + {x <> y})
  by (intros [x1 x2] [y1 y2]; destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
      [left; congruence | right; congruence | right; congruence | right; congruence]).
destruct (in_dec DEC (b, nb) (ablocks B (gxly cx) (gxS cx))) as [Hin0 | Hnin0].
- right. left. split; [|exists b, nb; split; [exact Hin2 | exact Ha]].
  apply (Permutation_in _ HPZ0) in Hin0. apply in_app_or in Hin0 as [HX0 | Hrest]; [|contradiction].
  unfold gFP, rig_fp. replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp _ b nb); [exact HX0 | lia].
- right. right. left. exists b, nb. split; [exact Hin2|]. split; [exact Hnin0 | exact Ha].
Qed.
Definition rk_R4 : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 37 0))].
Definition rk_EXPR : sv := SAlu ALU_ADD (SOff 32 (-8)) (SAlu ALU_SLL (SOff 35 0) (SLit 3)).
Lemma rk_awr_k4 : forall E G STK sp0 FP bl0 blc ly own SA hpn,
bv_unsigned (ew E 23) = SA + 48 -> bv_unsigned (ew E 33) = hpn ->
(forall a, SA + 48 <= a < SA + 52 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
(forall a, hpn <= a < hpn + 8 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok_x E (rk_R4 :: rk_regions) G 0 [] STK sp0 FP bl0 blc ly own.
Proof.
intros E G STK sp0 FP bl0 blc ly own SA hpn E23 E33 W1 W2 a (r & Hin & Hr).
cbn [rk_regions In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [rk_R4 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
- lia.
- lia.
- left. split; [apply W1; lia | lia].
- left. split; [apply W2; lia | lia].
Qed.
(* hp - 8 + (nh << 3) = hp + 8 (nh - 1), the address the store's source is read from (0x82edc) *)
Lemma rk_expr_den : forall E hp nh, ew E 32 = Z_to_bv 64 hp -> ew E 35 = Z_to_bv 64 nh ->
8 <= hp -> 1 <= nh < 2 ^ 26 -> hp + 8 * nh < 2 ^ 64 ->
sv_denot E rk_EXPR = Z_to_bv 64 (hp + 8 * (nh - 1)).
Proof.
intros E hp nh E32 E35 Hhp Hnh Hb. unfold rk_EXPR. cbn [sv_denot]. rewrite E32, E35.
replace (bv_unsigned (Z_to_bv 64 hp)) with hp by (symmetry; apply unsigned_lit_small; lia).
replace (bv_unsigned (Z_to_bv 64 nh)) with nh by (symmetry; apply unsigned_lit_small; lia).
rewrite Z.add_0_r.
apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (nh * 8) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rk_awr_win : forall E (rs : list YP09.region) G STK sp0 FP bl0 blc ly own SA hpn,
bv_unsigned (ew E 23) = SA + 48 -> bv_unsigned (ew E 33) = hpn ->
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/ (YP09.r_base r = Some 23%nat /\ YP09.r_wlo r = 0 /\ YP09.r_whi r = 4) \/
  (YP09.r_base r = Some 33%nat /\ YP09.r_wlo r = 0 /\ YP09.r_whi r = 8)) rs ->
(forall a, SA + 48 <= a < SA + 52 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
(forall a, hpn <= a < hpn + 8 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok_x E rs G 0 [] STK sp0 FP bl0 blc ly own.
Proof.
intros E rs G STK sp0 FP bl0 blc ly own SA hpn E23 E33 HF W1 W2 a (r & Hin & Hr).
rewrite Forall_forall in HF. destruct (HF r Hin) as [Hw | [(Hb & Hl & Hh) | (Hb & Hl & Hh)]].
- lia.
- rewrite Hb, Hl, Hh in Hr. cbn [base_val] in Hr. left. split; [apply W1; lia | lia].
- rewrite Hb, Hl, Hh in Hr. cbn [base_val] in Hr. left. split; [apply W2; lia | lia].
Qed.
Ltac rk_win_tac := lazymatch goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end;
repeat (apply Forall_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; first [left; lia | right; left; repeat split; reflexivity | right; right; repeat split; reflexivity] |]); apply Forall_nil.
Ltac rk_in_tac Hin := lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end; cbn [In] in Hin.
Lemma rk_awr_k : forall E G STK sp0 FP bl0 blc ly own SA hpn,
bv_unsigned (ew E 23) = SA + 48 -> bv_unsigned (ew E 33) = hpn ->
(forall a, SA + 48 <= a < SA + 52 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
(forall a, hpn <= a < hpn + 8 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok_x E rk_regions G 0 [] STK sp0 FP bl0 blc ly own.
Proof.
intros E G STK sp0 FP bl0 blc ly own SA hpn E23 E33 W1 W2 a (r & Hin & Hr).
cbn [rk_regions In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
- lia.
- left. split; [apply W1; lia | lia].
- left. split; [apply W2; lia | lia].
Qed.

Lemma rk_blk_not_img : forall ly S W m md p nn a, ARh ly S W m md -> In (p, nn) (ablocks B ly S) ->
p <= a < p + req_size nn -> ~ in_img SEGS a.
Proof.
intros ly S W m md p nn a HAR Hin Ha.
exact (proj2 (rk_alc ly S W m md a HAR (or_introl (ex_intro _ p (ex_intro _ nn (conj Hin Ha)))))).
Qed.
Lemma rk_hull : forall F np s, F mod 32 = 0 -> 1 <= np <= 27 ->
shadow_addr (F + 32) / 8 * 8 <= s < shadow_addr (F + 32 + np - 1) / 8 * 8 + 8 -> shadow_addr F <= s < shadow_addr F + 16.
Proof.
intros F np s HF Hnp Hs. unfold shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_mod F 32 ltac:(lia)) as D0. rewrite HF, Z.add_0_r in D0.
set (t := F / 32) in *.
assert (E1 : (F + 32) / 8 = 4 * t + 4).
{ rewrite D0. replace (32 * t + 32) with ((4 * t + 4) * 8) by lia. apply Z.div_mul. lia. }
assert (E0 : F / 8 = 4 * t).
{ rewrite D0. replace (32 * t) with ((4 * t) * 8) by lia. apply Z.div_mul. lia. }
assert (E2 : (F + 32 + np - 1) / 8 = 4 * t + (31 + np) / 8).
{ rewrite D0. replace (32 * t + 32 + np - 1) with ((31 + np) + (4 * t) * 8) by lia.
  rewrite Z.div_add by lia. lia. }
rewrite E1, E2, E0 in *.
pose proof (Z.div_mod (31 + np) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (31 + np) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (2147450880 + (4 * t + 4)) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (2147450880 + (4 * t + 4)) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (2147450880 + (4 * t + (31 + np) / 8)) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (2147450880 + (4 * t + (31 + np) / 8)) 8 ltac:(lia)) as M3.
lia.
Qed.
Lemma rk_vm2 : forall H (m m' : word -> option byte) a n v,
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v ->
forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x.
Proof.
intros H m m' a n v H1 H2 x Hx. unfold aview.
pose proof (H1 (Z.to_nat (x - a)) ltac:(lia)) as A1. pose proof (H2 (Z.to_nat (x - a)) ltac:(lia)) as A2.
rewrite Z2Nat.id in A1, A2 by lia. replace (a + (x - a)) with x in A1, A2 by lia. rewrite A1, A2. reflexivity.
Qed.
Lemma rk_sll3_add8 : forall x, 0 <= x < 2 ^ 26 ->
alu64 ALU_ADD (alu64 ALU_SLL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 8) = Z_to_bv 64 (8 * x + 8).
Proof.
intros x Hx. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by lia. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (x * 8) (2 ^ 64)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
(* the two writable windows of the walk's state still hold nheld and the key's address *)
Lemma rk_win_vals : forall Ea ss ms (W : world SEGS) SA hpn nh key,
st_ok_pi SEGS VAL Ea ss (restrict (w_H W) ms) -> ss_mem ss = rk_regions ->
bv_unsigned (ew Ea 23) = SA + 48 -> bv_unsigned (ew Ea 33) = hpn -> ew Ea 35 = Z_to_bv 64 nh -> ew Ea 34 = Z_to_bv 64 key ->
0 <= nh < 2 ^ 32 -> 0 <= key < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (SA + 48) 4 nh /\ val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) hpn 8 key.
Proof.
intros Ea ss ms W SA hpn nh key HS Hm E23 E33 E35 E34 Hnh Hk.
pose proof (st_ok_pi_region_nth Ea ss (restrict (w_H W) ms) 1 _ HS ltac:(rewrite Hm; reflexivity)) as HR1.
pose proof (st_ok_pi_region_nth Ea ss (restrict (w_H W) ms) 2 _ HS ltac:(rewrite Hm; reflexivity)) as HR2.
cbn [ms_mem restrict] in HR1, HR2.
split.
- pose proof (field_of_region Ea _ 23 (SA + 48) _ 0 4 0 4 0 4%N (SOff 35 0) nh HR1 E23 ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V.
- pose proof (field_of_region Ea _ 33 hpn _ 0 8 0 8 0 8%N (SOff 34 0) key HR2 E33 ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V.
Qed.
(* the three windows of the walk's state (st_ok form: also a state stopped at a call) *)
Lemma rk_win3 : forall Ea ss ms (W : world SEGS) SA hpn hp nh key,
st_ok SEGS Ea ss (restrict (w_H W) ms) -> ss_mem ss = rk_regions ->
bv_unsigned (ew Ea 25) = SA + 40 -> bv_unsigned (ew Ea 23) = SA + 48 -> bv_unsigned (ew Ea 33) = hpn ->
ew Ea 32 = Z_to_bv 64 hp -> ew Ea 35 = Z_to_bv 64 nh -> ew Ea 34 = Z_to_bv 64 key ->
0 <= hp < 2 ^ 64 -> 0 <= nh < 2 ^ 32 -> 0 <= key < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (SA + 40) 8 hp /\
val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (SA + 48) 4 nh /\ val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) hpn 8 key.
Proof.
intros Ea ss ms W SA hpn hp nh key HS Hm E25 E23 E33 E32 E35 E34 Hhp Hnh Hk.
pose proof (st_ok_region_nth Ea ss (restrict (w_H W) ms) 0 _ HS ltac:(rewrite Hm; reflexivity)) as HR0.
pose proof (st_ok_region_nth Ea ss (restrict (w_H W) ms) 1 _ HS ltac:(rewrite Hm; reflexivity)) as HR1.
pose proof (st_ok_region_nth Ea ss (restrict (w_H W) ms) 2 _ HS ltac:(rewrite Hm; reflexivity)) as HR2.
cbn [ms_mem restrict] in HR0, HR1, HR2.
split; [|split].
- pose proof (field_of_region Ea _ 25 (SA + 40) _ 0 8 0 0 0 8%N (SOff 32 0) hp HR0 E25 ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V.
- pose proof (field_of_region Ea _ 23 (SA + 48) _ 0 4 0 4 0 4%N (SOff 35 0) nh HR1 E23 ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V.
- pose proof (field_of_region Ea _ 33 hpn _ 0 8 0 8 0 8%N (SOff 34 0) key HR2 E33 ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite Z.add_0_r in V. exact V.
Qed.
Lemma rk_keep_join : forall cx (W : world SEGS) m1 mf SA hpn nh key,
(forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ (SA + 48 <= a < SA + 52) ->
   ~ (hpn <= a < hpn + 8) -> aview SEGS (w_H W) mf a = aview SEGS (w_H W) m1 a) ->
val_mem SEGS (mrestrict (w_H W) m1) (SA + 48) 4 nh -> val_mem SEGS (mrestrict (w_H W) mf) (SA + 48) 4 nh ->
val_mem SEGS (mrestrict (w_H W) m1) hpn 8 key -> val_mem SEGS (mrestrict (w_H W) mf) hpn 8 key ->
rkk_KEEP cx W m1 mf.
Proof.
intros cx W m1 mf SA hpn nh key HK V1 V1' V2 V2' a Ha Hns.
destruct (Z_lt_le_dec a (SA + 48)) as [h1|h1]; [|destruct (Z_lt_le_dec a (SA + 52)) as [h2|h2]].
- destruct (Z_lt_le_dec a hpn) as [g1|g1]; [apply HK; lia|destruct (Z_lt_le_dec a (hpn + 8)) as [g2|g2]; [|apply HK; lia]].
  exact (rk_vm2 _ _ _ _ 8 _ V2 V2' a ltac:(cbn; lia)).
- exact (rk_vm2 _ _ _ _ 4 _ V1 V1' a ltac:(cbn; lia)).
- destruct (Z_lt_le_dec a hpn) as [g1|g1]; [apply HK; lia|destruct (Z_lt_le_dec a (hpn + 8)) as [g2|g2]; [|apply HK; lia]].
  exact (rk_vm2 _ _ _ _ 8 _ V2 V2' a ltac:(cbn; lia)).
Qed.
Lemma rk_branch_lt : forall E a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
0 <= va < 2 ^ 63 -> 0 <= vb < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (va <? vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma rk_sh_den : forall E b x, ew E b = w64 x -> ew E 18 = w64 SHADOW_OFF -> 0 <= x < 2 ^ 60 ->
sv_denot E (rk_sh b) = w64 (SHADOW_OFF + x / 8).
Proof.
intros E b x Hb E18 Hx. unfold rk_sh. cbn [sv_denot]. rewrite Hb, E18, !Z.add_0_r, !Z_to_bv_bv_unsigned.
assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Lemma rk_vm1_of_aview : forall H (m : word -> option byte) x v, aview SEGS H m x = Some v -> 0 <= v < 256 ->
val_mem SEGS (mrestrict H m) x 1 v.
Proof.
intros H m x v Hv Hr k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) x) as [b|] eqn:Eb; [|discriminate Hv].
cbn in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with 256. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite <- Hv. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma rk_end5 : forall (W : world SEGS) m, rom_view SEGS W m -> garr8 SEGS (arm W m) (VAL A_lit_end5) (bzs END5).
Proof.
intros W m HR j Hj. change (length (bzs END5)) with 5%nat in Hj.
destruct (HEND5L j Hj) as [Hrom Hseg].
assert (HE5 : bzs END5 = [32; 101; 110; 100; 0]) by (vm_compute; reflexivity).
assert (Hv : aview SEGS (w_H W) m (VAL A_lit_end5 + Z.of_nat j) = Some (nth j (bzs END5) 0)).
{ rewrite (HR _ Hrom), Hseg. destruct j as [|[|[|[|[|j]]]]]; try (vm_compute; reflexivity). lia. }
assert (Hb : 0 <= nth j (bzs END5) 0 < 256) by (rewrite HE5; destruct j as [|[|[|[|[|j]]]]]; cbn [nth]; lia).
split; [exact (rk_vm1_of_aview _ _ _ _ Hv Hb) | exact Hb].
Qed.
Lemma rk_fpos_eq : forall cx p1 p2 ly S W m md k m' md' k',
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, p1)] ly S [] W m md k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, p2)] ly S [] W m' md' k' ->
p1 = p2.
Proof.
intros cx p1 p2 ly S W m md k m' md' k' (_ & _ & (memS1 & HJ1 & _) & _) (_ & _ & (memS2 & HJ2 & _) & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & F1 & _). pose proof HJ2 as (_ & _ & _ & _ & _ & F2 & _).
rewrite F1 in F2. cbn [app] in F2. injection F2 as E. exact E.
Qed.

(* ==== representation block (RigKeyRep) ==== *)
(* ---- RigKeyRep (prefix rkr_): the relay table's representation at the KEY step. ---- *)

(* ------------------------------------------------------------------ bytes *)
Lemma rkr_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma rkr_garr8_le : forall mm a n z, garr8 SEGS mm a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS mm a n z.
Proof.
intros mm a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, rkr_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma rkr_le_garr8 : forall mm a n z, val_mem SEGS mm a n z -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  garr8 SEGS mm a (bzs (Z_to_le_bytes n z)).
Proof.
intros mm a n z Hv Hz j Hj. unfold bzs in Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hj).
rewrite map_nth, rkr_nth_le_bytes by exact Hj. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
split; [|apply Z.mod_pos_bound; lia].
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (Hv j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

(* a byte of a garr8 string, as the reader sees it *)
Lemma rkr_view : forall (W : world SEGS) m a l j, garr8 SEGS (arm W m) a l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv. unfold arm in Hv.
unfold aview. cbv beta. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. repeat rewrite (Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.

Lemma rkr_bz0 : bz (Z_to_bv 8 0) = 0.
Proof. unfold bz. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma rkr_bz_nz : forall b, b <> Z_to_bv 8 0 -> bz b <> 0.
Proof. intros b Hb Hz. apply Hb. apply bv_eq. rewrite <- rkr_bz0 in Hz. exact Hz. Qed.

Lemma rkr_nth_key : forall (kt : list byte) j, (j < length kt)%nat ->
  nth j (bzs (kt ++ [Z_to_bv 8 0])) 0 = bz (nth j kt (Z_to_bv 8 0)).
Proof.
intros kt j Hj. unfold bzs. rewrite map_app, app_nth1 by (rewrite length_map; exact Hj).
rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). apply map_nth.
Qed.

Lemma rkr_nth_key_end : forall (kt : list byte), nth (length kt) (bzs (kt ++ [Z_to_bv 8 0])) 0 = 0.
Proof.
intros kt. unfold bzs. rewrite map_app, app_nth2 by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag.
cbn [nth map]. exact rkr_bz0.
Qed.

Lemma rkr_garr8_app3 : forall mm a (A M C : list byte),
  garr8 SEGS mm a (bzs (A ++ M ++ C)) <->
  garr8 SEGS mm a (bzs A) /\ garr8 SEGS mm (a + Z.of_nat (length A)) (bzs M) /\
  garr8 SEGS mm (a + Z.of_nat (length A) + Z.of_nat (length M)) (bzs C).
Proof. intros mm a A M C. unfold bzs. rewrite !map_app, !garr8_app, !length_map. reflexivity. Qed.

(* ------------------------------------------------------------------ the held keys' pointer array *)
Lemma rkr_kp_app : forall K1 K2, key_ptrs (K1 ++ K2) = key_ptrs K1 ++ key_ptrs K2.
Proof. intros K1 K2. unfold key_ptrs. rewrite map_app, concat_app. reflexivity. Qed.

Lemma rkr_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
rewrite relay_instance_gone_b_lem.rigl_kp_cons, length_app, IH, Mem.length_le8. cbn [length]. lia.
Qed.

Lemma rkr_key_ptr : forall mm hp ks j, garr8 SEGS mm hp (bzs (key_ptrs ks)) -> (j < length ks)%nat ->
  0 <= key_addr (nth j ks (0, [], [])) < 2 ^ 64 ->
  val_mem SEGS mm (hp + 8 * Z.of_nat j) 8 (key_addr (nth j ks (0, [], []))).
Proof.
intros mm hp ks j Hg Hj Hk.
destruct (nth_split ks (0, [], []) Hj) as (l1 & l2 & E & L1).
rewrite E, rkr_kp_app, relay_instance_gone_b_lem.rigl_kp_cons in Hg.
apply rkr_garr8_app3 in Hg as (_ & Hg & _). rewrite rkr_key_ptrs_len, L1 in Hg.
replace (hp + 8 * Z.of_nat j) with (hp + Z.of_nat (8 * j)) by lia.
apply rkr_garr8_le; [|lia].
unfold Mem.le8, word_to_le_bytes in Hg. rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

Lemma rkr_set_nth_mid : forall {A} (l1 : list A) y v r, set_nth (length l1) v (l1 ++ y :: r) = l1 ++ v :: r.
Proof. intros A l1. induction l1 as [|h t IH]; intros y v r; cbn [length app set_nth]; [reflexivity|]. f_equal. apply IH. Qed.

Lemma rkr_nth_last : forall {A} (l : list A) z d, nth (length (l ++ [z]) - 1) (l ++ [z]) d = z.
Proof.
intros A l z d. rewrite length_app. cbn [length]. replace (length l + 1 - 1)%nat with (length l) by lia.
rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

(* swap_remove n: the last element leaves (n the last index), or moves into slot n *)
Lemma rkr_swap_shape : forall {A} (d : A) n l, (n < length l)%nat ->
  exists l1 y l2, l = l1 ++ y :: l2 /\ length l1 = n /\
  ((l2 = [] /\ swap_remove d n l = l1) \/
   (exists l3 z, l2 = l3 ++ [z] /\ swap_remove d n l = l1 ++ z :: l3)).
Proof.
intros A d n l Hn. destruct (nth_split l d Hn) as (l1 & l2 & E & L1).
remember (nth n l d) as y eqn:Ey. clear Ey. subst l n.
exists l1, y, l2. split; [reflexivity|]. split; [reflexivity|]. unfold swap_remove.
destruct l2 as [|w l2'].
- left. split; [reflexivity|]. rewrite last_last, rkr_set_nth_mid.
  apply relay_instance_gone_b_lem.rigl_firstn_app_exact. rewrite length_app. cbn [length]. lia.
- right. destruct (@exists_last A (w :: l2') ltac:(discriminate)) as (l3 & z & E2). exists l3, z. split; [exact E2|].
  rewrite E2.
  assert (Hl : last (l1 ++ y :: l3 ++ [z]) d = z).
  { replace (l1 ++ y :: l3 ++ [z]) with ((l1 ++ y :: l3) ++ [z]) by (rewrite <- app_assoc; reflexivity). apply last_last. }
  rewrite Hl, rkr_set_nth_mid.
  replace (l1 ++ z :: l3 ++ [z]) with ((l1 ++ z :: l3) ++ [z]) by (rewrite <- app_assoc; reflexivity).
  apply relay_instance_gone_b_lem.rigl_firstn_app_exact.
  rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. lia.
Qed.

(* ------------------------------------------------------------------ the entry's bytes *)
(* the 56 bytes of entry_keys e ks: 40 that do not depend on the keys, held, nheld = |ks|, pad2 *)
Lemma rkr_eb_shape : forall e, length (re_pad1 e) = 4%nat -> exists X, length X = 40%nat /\
  forall ks, entry_bytes (entry_keys e ks) =
    X ++ Mem.le8 (Z_to_bv 64 (re_hp e)) ++ Mem.le4 (Z_to_bv 64 (Z.of_nat (length ks))) ++ re_pad2 e.
Proof.
intros e H1.
exists (Mem.le4 (Z_to_bv 64 (re_fd e)) ++ Mem.le4 (Z_to_bv 64 (re_eof e)) ++ Mem.le4 (Z_to_bv 64 (re_skip e)) ++
  re_pad1 e ++ Mem.le8 (Z_to_bv 64 (re_buf e)) ++ Mem.le8 (Z_to_bv 64 (re_used e)) ++ Mem.le8 (Z_to_bv 64 (re_cap e))).
split.
- rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1. reflexivity.
- intros ks. unfold entry_bytes, re_nheld.
  cbn [entry_keys re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2 re_keys].
  rewrite <- !app_assoc. reflexivity.
Qed.

(* ------------------------------------------------------------------ blocks apart *)
Lemma rkr_pw_perm : forall (l l' : list (Z * Z)), Permutation l l' -> pairwise zdisjoint l -> pairwise zdisjoint l'.
Proof.
intros l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; intros Hp.
- exact Hp.
- cbn [pairwise] in Hp |- *. destruct Hp as [Hf Hp]. split; [|exact (IH Hp)].
  rewrite Forall_forall in Hf |- *. intros z Hz. apply Hf. exact (Permutation_in _ (Permutation_sym HP) Hz).
- cbn [pairwise] in Hp |- *. destruct Hp as [Hf1 [Hf2 Hp]]. apply Forall_cons_iff in Hf1 as [Hyx Hf1].
  split; [apply Forall_cons; [unfold zdisjoint in *; lia | exact Hf2] | split; [exact Hf1 | exact Hp]].
- exact (IH2 (IH1 Hp)).
Qed.

Lemma rkr_pw_mid : forall (A C : list (Z * Z)) h y, pairwise zdisjoint (A ++ h :: C) -> In y (A ++ C) -> zdisjoint h y.
Proof.
induction A as [|a A IH]; intros C h y HP Hy; cbn [app pairwise] in HP, Hy.
- destruct HP as [Hf _]. rewrite Forall_forall in Hf. exact (Hf y Hy).
- destruct HP as [Hf HP]. destruct Hy as [<- | Hy].
  + rewrite Forall_forall in Hf.
    pose proof (Hf h ltac:(apply in_or_app; right; left; reflexivity)) as Hd. unfold zdisjoint in *. lia.
  + exact (IH C h y HP Hy).
Qed.

Lemma rkr_pw_mid4 : forall (CP Bx Kx CQ : list (Z * Z)) h y,
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (CP ++ (Bx ++ h :: Kx) ++ CQ)) ->
  In y (CP ++ CQ ++ Bx ++ Kx) -> zdisjoint (fst h, req_size (snd h)) (fst y, req_size (snd y)).
Proof.
intros CP Bx Kx CQ h y HP Hy.
replace (CP ++ (Bx ++ h :: Kx) ++ CQ) with ((CP ++ Bx) ++ h :: (Kx ++ CQ)) in HP by (rewrite <- !app_assoc; reflexivity).
rewrite map_app in HP. cbn [map] in HP.
apply (rkr_pw_mid _ _ _ _ HP).
rewrite <- map_app. apply (in_map (fun b => (fst b, req_size (snd b)))).
rewrite !in_app_iff in Hy |- *. tauto.
Qed.

(* the relay's blocks pairwise apart: a byte of an entry's block is off the table, and a byte of any block but the
   held array's own is off entry e's held block *)
Lemma rkr_disj : forall G0 pre e ks post, re_hp e <> 0 ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (arelay_blks G0 (pre ++ entry_keys e ks :: post))) ->
  (forall b, In b (concat (map aentry_blks (pre ++ entry_keys e ks :: post))) ->
     forall a, fst b <= a < fst b + snd b -> ~ (G0 <= a < G0 + ATABLE)) /\
  (forall b, In b (concat (map aentry_blks pre) ++ concat (map aentry_blks post) ++
       (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
       map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks) ->
     forall a, fst b <= a < fst b + snd b -> ~ (re_hp e <= a < re_hp e + re_kh e)).
Proof.
intros G0 pre e ks post Hhp PW. unfold arelay_blks in PW. cbn [map pairwise] in PW. destruct PW as [PT PR].
assert (RQ : forall b a, fst b <= a < fst b + snd b -> req_size (snd b) = snd b)
  by (intros b a Ha; unfold req_size; destruct (Z.eqb_spec (snd b) 0); lia).
assert (RK : re_kh e <= req_size (re_kh e)) by (unfold req_size; destruct (Z.eqb_spec (re_kh e) 0); lia).
split.
- intros b Hb a Ha HT. rewrite Forall_forall in PT.
  pose proof (PT _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. unfold ATABLE in HT.
  rewrite (RQ b a Ha) in Hd. lia.
- intros b Hb a Ha HH.
  rewrite map_app, concat_app in PR. cbn [map concat] in PR.
  assert (EB : aentry_blks (entry_keys e ks) = (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
     (re_hp e, re_kh e) :: map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks).
  { unfold aentry_blks. cbn [entry_keys re_cap re_buf re_hp re_kh re_keys].
    rewrite (proj2 (Z.eqb_neq _ _) Hhp). reflexivity. }
  rewrite EB in PR.
  pose proof (rkr_pw_mid4 _ _ _ _ (re_hp e, re_kh e) b PR Hb) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (RQ b a Ha) in Hd. lia.
Qed.

(* a byte an entry's predicate reads lies in one of the entry's blocks *)
Lemma rkr_fp_blk : forall ly S W m e, aentry_ok B ly S W m e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks e) /\ fst b <= a < fst b + snd b.
Proof.
intros ly S W m e (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15) r Hr a Ha.
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | [Hr | Hr]].
- revert Hr. destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; intros Hr; [destruct Hr|].
  destruct Hr as [<- | []].
  destruct E10 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
  exists (re_buf e, re_cap e). split.
  + unfold aentry_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc0). apply in_or_app. left. left. reflexivity.
  + unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, length_app in Ha. lia.
- subst r. destruct E12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & Hg)].
  + exfalso. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite Hk in Ha. cbn [key_ptrs map concat length] in Ha. lia.
  + exists (re_hp e, re_kh e). split.
    * unfold aentry_blks. rewrite (proj2 (Z.eqb_neq _ _) Hz). apply in_or_app. right. apply in_or_app. left. left. reflexivity.
    * unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, rkr_key_ptrs_len in Ha. unfold re_nheld in Hk1. lia.
- apply in_map_iff in Hr as (k & <- & Hk). exists (key_addr k, Z.of_nat (length (key_text k)) + 1). split.
  + unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). exact Hk.
  + unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
Qed.

(* ------------------------------------------------------------------ 1. entry i, as KEY reads it *)
Lemma rkr_entry_at : forall ly S W m md G0 pre e ks post n,
  ARh ly S W m md ->
  arelay_at B RG ly S W m G0 (pre ++ entry_keys e ks :: post) -> (n < length ks)%nat ->
  let SA := G0 + AENT * Z.of_nat (length pre) in
  let k := nth n ks (0, [], []) in
  In (G0, ATABLE) (ablocks B ly S) /\ G0 mod 16 = 0 /\ 4096 <= G0 /\ G0 + ATABLE <= alloc_ceiling /\
  SA + AENT <= G0 + ATABLE /\
  val_mem SEGS (arm W m) (SA + 40) 8 (re_hp e) /\ val_mem SEGS (arm W m) (SA + 48) 4 (Z.of_nat (length ks)) /\
  awr W m SA AENT /\
  re_hp e <> 0 /\ In (re_hp e, re_kh e) (ablocks B ly S) /\ 8 * Z.of_nat (length ks) <= re_kh e /\
  garr8 SEGS (arm W m) (re_hp e) (bzs (key_ptrs ks)) /\ awr W m (re_hp e) (8 * Z.of_nat (length ks)) /\
  (forall j, (j < length ks)%nat -> val_mem SEGS (arm W m) (re_hp e + 8 * Z.of_nat j) 8 (key_addr (nth j ks (0, [], [])))) /\
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (ablocks B ly S) /\
  garr8 SEGS (arm W m) (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])) /\
  ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= APARTIAL /\
  Z.of_nat (length ks) < 2 ^ 26 /\ NoDup (map key_addr ks).
Proof.
intros ly S W m md G0 pre e ks post n HAR HR Hn. cbv zeta.
remember (G0 + AENT * Z.of_nat (length pre)) as SA eqn:ESA.
destruct HR as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (tail & T1 & T2 & T3) & H10 & H11).
assert (H7' : (length pre < 16)%nat) by (rewrite length_app in H7; cbn [length] in H7; lia).
apply Forall_app in H10 as [HFpre HF2]. apply Forall_cons_iff in HF2 as [HE HFpost].
unfold aentry_ok, re_nheld in HE.
cbn [entry_keys re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk] in HE.
destruct HE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15).
destruct E12 as [(_ & Hk0) | (Hhp & Hhin & Hkh & Hkh8 & Hgp)]; [rewrite Hk0 in Hn; cbn in Hn; lia|].
destruct (rk_alb ly S W m md G0 ATABLE HAR H8) as (HG16 & HG4 & HGc & _ & HGp & _ & _).
change (req_size ATABLE) with 896 in HGc, HGp.
destruct (rk_alb ly S W m md _ _ HAR Hhin) as (_ & Hh4 & Hhc & _ & Hhpres & _ & Hkh0).
pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hrkh].
pose proof alloc_ceiling_val as [[_ Hceil] _].
rewrite Forall_forall in E15.
assert (KB : forall k, In k ks -> 0 <= key_addr k < 2 ^ 64).
{ intros k Hk. destruct (E15 k Hk) as (K1 & _).
  destruct (rk_alb ly S W m md _ _ HAR K1) as (_ & K4 & Kc & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Kr]. lia. }
destruct (rkr_eb_shape e E3) as (X & HX & EX).
assert (HCP : length (concat (map entry_bytes pre)) = (56 * length pre)%nat).
{ apply relay_instance_gone_b_lem.rigl_concat_len. eapply Forall_impl; [|exact HFpre].
  intros e0 (_ & _ & P1 & P2 & _). exact (relay_instance_gone_b_lem.rig_entry_len e0 P1 P2). }
rewrite map_app, concat_app in T3. cbn [map concat] in T3. rewrite EX in T3. rewrite <- !app_assoc in T3.
unfold bzs in T3. rewrite !map_app in T3.
apply garr8_app in T3 as [_ T3]. apply garr8_app in T3 as [_ T3].
apply garr8_app in T3 as [Ghp T3]. apply garr8_app in T3 as [Gnh _].
rewrite !length_map, HCP, HX in Ghp. rewrite !length_map, HCP, HX, Mem.length_le8 in Gnh.
assert (OA : G0 + Z.of_nat (56 * length pre) + Z.of_nat 40 = SA + 40) by (unfold AENT in ESA; lia).
rewrite OA in Ghp. rewrite OA in Gnh. replace (SA + 40 + Z.of_nat 8) with (SA + 48) in Gnh by lia.
split; [exact H8|]. split; [exact HG16|]. split; [exact HG4|]. split; [unfold ATABLE; lia|].
split; [unfold ATABLE, AENT in *; lia|].
split.
{ unfold Mem.le8, word_to_le_bytes in Ghp. rewrite unsigned_lit_small in Ghp by lia. apply rkr_garr8_le; [exact Ghp | lia]. }
split.
{ unfold Mem.le4 in Gnh. rewrite unsigned_lit_small in Gnh by lia. apply rkr_garr8_le; [exact Gnh | lia]. }
split.
{ intros i Hi. unfold arm. apply apresent_writable. apply (proj1 (HGp (SA + i) ltac:(unfold AENT, ATABLE in *; lia))). }
split; [exact Hhp|]. split; [exact Hhin|]. split; [exact Hkh|]. split; [exact Hgp|].
split.
{ intros i Hi. unfold arm. apply apresent_writable. apply (proj1 (Hhpres (re_hp e + i) ltac:(lia))). }
split.
{ intros j Hj. apply rkr_key_ptr; [exact Hgp | exact Hj | apply KB; apply nth_In; exact Hj]. }
destruct (E15 (nth n ks (0, [], [])) (nth_In _ _ Hn)) as (K1 & K2 & K3 & K4).
split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact E11 | exact E13].
Qed.

(* ------------------------------------------------------------------ 2. the relay after KEY's end-and-move *)
(* Premises beyond the first text (the parent's KEY call site has them: GLIVE's AR at the old state, GBASE's
   rg_place, GIN's Permutation): without them the global cells could overlap the two stored cells, or the held
   block the table or a key, and the lemma is false. *)
Lemma rkr_arelay_swap : forall ly S W m md ly' S' W' m' G0 pre e ks post n rest,
  ARh ly S W m md -> rg_place B RG ->
  Permutation (ablocks B ly S) (arelay_blks G0 (pre ++ entry_keys e ks :: post) ++ rest) ->
  arelay_at B RG ly S W m G0 (pre ++ entry_keys e ks :: post) -> (n < length ks)%nat ->
  let SA := G0 + AENT * Z.of_nat (length pre) in
  let ks' := swap_remove (0, [], []) n ks in
  let es' := pre ++ entry_keys e ks' :: post in
  (forall b, In b (arelay_blks G0 es') -> In b (ablocks B ly' S')) ->
  (forall r, In r (arelay_fp RG G0 es') -> forall a, fst r <= a < snd r ->
     ~ (SA + 48 <= a < SA + 52) -> ~ (re_hp e + 8 * Z.of_nat n <= a < re_hp e + 8 * Z.of_nat n + 8) ->
     abyte_kept W m W' m' a) ->
  val_mem SEGS (arm W' m') (SA + 48) 4 (Z.of_nat (length ks')) ->
  val_mem SEGS (arm W' m') (re_hp e + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], []))) ->
  arelay_at B RG ly' S' W' m' G0 es'.
Proof.
intros ly S W m md ly' S' W' m' G0 pre e ks post n rest HAR HPL HP HR Hn. cbv zeta.
remember (swap_remove (0, [], []) n ks) as ks' eqn:Eks'.
remember (G0 + AENT * Z.of_nat (length pre)) as SA eqn:ESA.
intros HB HK Hnh Hslot.
assert (Hlen' : length ks' = (length ks - 1)%nat) by (rewrite Eks'; apply relay_instance_gone_b_lem.rigl_len_swap).
destruct HR as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (tail & T1 & T2 & T3) & H10 & H11).
assert (Hes : length (pre ++ entry_keys e ks' :: post) = length (pre ++ entry_keys e ks :: post))
  by (rewrite !length_app; reflexivity).
assert (H7' : (length pre < 16)%nat) by (rewrite length_app in H7; cbn [length] in H7; lia).
apply Forall_app in H10 as [HFpre HF2]. apply Forall_cons_iff in HF2 as [HE HFpost].
unfold aentry_ok, re_nheld in HE.
cbn [entry_keys re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk] in HE.
destruct HE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15).
destruct E12 as [(_ & Hk0) | (Hhp & Hhin & Hkh & Hkh8 & Hgp)]; [rewrite Hk0 in Hn; cbn in Hn; lia|].
destruct (rk_alb ly S W m md G0 ATABLE HAR H8) as (_ & _ & _ & _ & _ & HPW & _).
destruct (rk_alb ly S W m md _ _ HAR Hhin) as (_ & Hh4 & Hhc & _ & _ & _ & Hkh0).
pose proof alloc_ceiling_val as [[_ Hceil] _].
rewrite Forall_forall in E15.
assert (KB : forall k, In k ks -> 0 <= key_addr k < 2 ^ 64).
{ intros k Hk. destruct (E15 k Hk) as (K1 & _).
  destruct (rk_alb ly S W m md _ _ HAR K1) as (_ & K4 & Kc & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Kr]. lia. }
(* the relay's blocks are pairwise apart (AR, through the Permutation) *)
assert (PW : pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (arelay_blks G0 (pre ++ entry_keys e ks :: post)))).
{ pose proof (rkr_pw_perm _ _ (Permutation_map (fun b => (fst b, req_size (snd b))) HP) HPW) as Hq.
  rewrite map_app in Hq. exact (proj1 (pairwise_app_l _ _ _ Hq)). }
destruct (rkr_disj G0 pre e ks post Hhp PW) as [DT DH].
assert (NT : forall a, ~ (G0 <= a < G0 + ATABLE) -> ~ (SA + 48 <= a < SA + 52))
  by (intros a Ha Hb; apply Ha; unfold ATABLE, AENT in *; lia).
assert (NL : forall a, ~ (re_hp e <= a < re_hp e + re_kh e) ->
  ~ (re_hp e + 8 * Z.of_nat n <= a < re_hp e + 8 * Z.of_nat n + 8)) by (intros a Ha Hb; apply Ha; lia).
assert (HTH : forall a, re_hp e <= a < re_hp e + re_kh e -> ~ (G0 <= a < G0 + ATABLE)).
{ intros a Ha. apply (DT (re_hp e, re_kh e)); [|cbn [fst snd]; exact Ha].
  rewrite map_app, concat_app. apply in_or_app. right. cbn [map concat]. apply in_or_app. left.
  unfold aentry_blks. cbn [entry_keys re_hp re_kh re_cap re_buf re_keys]. rewrite (proj2 (Z.eqb_neq _ _) Hhp).
  apply in_or_app. right. left. reflexivity. }
(* the global cells are image bytes, so off every block *)
destruct HPL as (_ & _ & _ & _ & _ & _ & HRR & _).
assert (HGL : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
    rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ (G0 <= a < G0 + ATABLE) /\ ~ (re_hp e <= a < re_hp e + re_kh e)).
{ intros a Ha.
  assert (Hi : in_img SEGS a).
  { destruct Ha as [Ha | [Ha | Ha]].
    - exact (proj1 (HRR a ltac:(unfold rg_rng; tauto))).
    - exact (proj1 (HRR a ltac:(unfold rg_rng; tauto))).
    - exact (proj1 (HRGI a (or_introl Ha))). }
  pose proof (pa_img_range a Hi) as Hr.
  pose proof (rk_boi ly S W m md G0 ATABLE HAR H8) as O1.
  pose proof (rk_boi ly S W m md _ _ HAR Hhin) as O2.
  pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hrkh].
  change (req_size ATABLE) with 896 in O1. unfold off_img in O1, O2. unfold ATABLE. split; lia. }
assert (INE : forall e0 r, In e0 (pre ++ entry_keys e ks' :: post) -> In r (aentry_fp e0) ->
  In r (arelay_fp RG G0 (pre ++ entry_keys e ks' :: post))).
{ intros e0 r He0 Hr. unfold arelay_fp. right; right; right; right. apply in_concat.
  exists (aentry_fp e0). split; [apply in_map; exact He0 | exact Hr]. }
assert (BLE : forall e0 b, In e0 (pre ++ entry_keys e ks' :: post) -> In b (aentry_blks e0) -> In b (ablocks B ly' S')).
{ intros e0 b He0 Hb. apply HB. unfold arelay_blks. right. apply in_concat.
  exists (aentry_blks e0). split; [apply in_map; exact He0 | exact Hb]. }
assert (Hx' : In (entry_keys e ks') (pre ++ entry_keys e ks' :: post)) by (apply in_or_app; right; left; reflexivity).
assert (KE : forall r a, In r (arelay_fp RG G0 (pre ++ entry_keys e ks' :: post)) -> fst r <= a < snd r ->
  ~ (G0 <= a < G0 + ATABLE) -> ~ (re_hp e <= a < re_hp e + re_kh e) -> abyte_kept W m W' m' a)
  by (intros r a Hr Ha Q1 Q2; exact (HK r Hr a Ha (NT a Q1) (NL a Q2))).
assert (KT : forall a, G0 <= a < G0 + ATABLE -> ~ (SA + 48 <= a < SA + 52) -> abyte_kept W m W' m' a).
{ intros a Ha HN. apply (HK (G0, G0 + ATABLE)); [right; right; right; left; reflexivity | exact Ha | exact HN |].
  apply NL. intros Hh. exact (HTH a Hh Ha). }
assert (KH : forall a, re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs ks'))) ->
  ~ (re_hp e + 8 * Z.of_nat n <= a < re_hp e + 8 * Z.of_nat n + 8) -> abyte_kept W m W' m' a).
{ intros a Ha HL.
  assert (Hh : re_hp e <= a < re_hp e + re_kh e)
    by (unfold bzs in Ha; rewrite length_map, rkr_key_ptrs_len, Hlen' in Ha; lia).
  apply (HK (gfp (re_hp e) (bzs (key_ptrs ks')))); [| exact Ha | exact (NT a (HTH a Hh)) | exact HL].
  apply (INE _ _ Hx'). unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
(* the old blocks of the other entries, and entry e's buffer and key blocks *)
assert (OBP : forall e0 b, In e0 pre -> In b (aentry_blks e0) ->
  In b (concat (map aentry_blks (pre ++ entry_keys e ks :: post))) /\
  In b (concat (map aentry_blks pre) ++ concat (map aentry_blks post) ++
        (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
        map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks)).
{ intros e0 b He0 Hb. split.
  - apply in_concat. exists (aentry_blks e0). split; [apply in_map; apply in_or_app; left; exact He0 | exact Hb].
  - apply in_or_app. left. apply in_concat. exists (aentry_blks e0). split; [apply in_map; exact He0 | exact Hb]. }
assert (OBQ : forall e0 b, In e0 post -> In b (aentry_blks e0) ->
  In b (concat (map aentry_blks (pre ++ entry_keys e ks :: post))) /\
  In b (concat (map aentry_blks pre) ++ concat (map aentry_blks post) ++
        (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
        map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks)).
{ intros e0 b He0 Hb. split.
  - apply in_concat. exists (aentry_blks e0). split; [apply in_map; apply in_or_app; right; right; exact He0 | exact Hb].
  - apply in_or_app. right. apply in_or_app. left. apply in_concat. exists (aentry_blks e0).
    split; [apply in_map; exact He0 | exact Hb]. }
assert (OBX : forall b, In b ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
                         map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks) ->
  In b (concat (map aentry_blks (pre ++ entry_keys e ks :: post))) /\
  In b (concat (map aentry_blks pre) ++ concat (map aentry_blks post) ++
        (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
        map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks)).
{ intros b Hb. split.
  - apply in_concat. exists (aentry_blks (entry_keys e ks)). split; [apply in_map; apply in_or_app; right; left; reflexivity|].
    replace (aentry_blks (entry_keys e ks)) with ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
      (re_hp e, re_kh e) :: map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks)
      by (unfold aentry_blks; cbn [entry_keys re_cap re_buf re_hp re_kh re_keys];
          rewrite (proj2 (Z.eqb_neq _ _) Hhp); reflexivity).
    apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb].
  - apply in_app_or in Hb. apply in_or_app. right. apply in_or_app. right. apply in_or_app.
    destruct Hb as [Hb|Hb]; [left; exact Hb | right; exact Hb]. }
assert (KO : forall r a b, In r (arelay_fp RG G0 (pre ++ entry_keys e ks' :: post)) -> fst r <= a < snd r ->
  In b (concat (map aentry_blks (pre ++ entry_keys e ks :: post))) /\
  In b (concat (map aentry_blks pre) ++ concat (map aentry_blks post) ++
        (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
        map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks) ->
  fst b <= a < fst b + snd b -> abyte_kept W m W' m' a).
{ intros r a b Hr Ha [Hb1 Hb2] Hab. exact (KE r a Hr Ha (DT b Hb1 a Hab) (DH b Hb2 a Hab)). }
unfold arelay_at.
(* the three global cells *)
split.
{ apply (akept_vm W m); [|exact H1]. intros a Ha. change (Z.of_nat 8) with 8 in Ha.
  destruct (HGL a (or_introl Ha)) as [Q1 Q2].
  exact (KE (rg_src RG, rg_src RG + 8) a ltac:(left; reflexivity) Ha Q1 Q2). }
split.
{ apply (akept_awr W m); [|exact H2]. intros a Ha.
  destruct (HGL a (or_introl Ha)) as [Q1 Q2].
  exact (KE (rg_src RG, rg_src RG + 8) a ltac:(left; reflexivity) Ha Q1 Q2). }
split.
{ rewrite Hes. apply (akept_vm W m); [|exact H3]. intros a Ha. change (Z.of_nat 4) with 4 in Ha.
  destruct (HGL a (or_intror (or_introl Ha))) as [Q1 Q2].
  exact (KE (rg_nsrc RG, rg_nsrc RG + 4) a ltac:(right; left; reflexivity) Ha Q1 Q2). }
split.
{ apply (akept_awr W m); [|exact H4]. intros a Ha.
  destruct (HGL a (or_intror (or_introl Ha))) as [Q1 Q2].
  exact (KE (rg_nsrc RG, rg_nsrc RG + 4) a ltac:(right; left; reflexivity) Ha Q1 Q2). }
split.
{ apply (akept_vm W m); [|exact H5]. intros a Ha. change (Z.of_nat 4) with 4 in Ha.
  destruct (HGL a (or_intror (or_intror Ha))) as [Q1 Q2].
  exact (KE (rg_capsrc RG, rg_capsrc RG + 4) a ltac:(right; right; left; reflexivity) Ha Q1 Q2). }
split.
{ apply (akept_awr W m); [|exact H6]. intros a Ha.
  destruct (HGL a (or_intror (or_intror Ha))) as [Q1 Q2].
  exact (KE (rg_capsrc RG, rg_capsrc RG + 4) a ltac:(right; right; left; reflexivity) Ha Q1 Q2). }
split; [rewrite Hes; exact H7|].
split; [apply HB; left; reflexivity|].
split.
(* the table: its bytes kept, but nheld's four *)
{ destruct (rkr_eb_shape e E3) as (X & HX & EX).
  assert (HCP : length (concat (map entry_bytes pre)) = (56 * length pre)%nat).
  { apply relay_instance_gone_b_lem.rigl_concat_len. eapply Forall_impl; [|exact HFpre].
    intros e0 (_ & _ & P1 & P2 & _). exact (relay_instance_gone_b_lem.rig_entry_len e0 P1 P2). }
  assert (ETB : forall K, concat (map entry_bytes (pre ++ entry_keys e K :: post)) ++ tail =
    (concat (map entry_bytes pre) ++ X ++ Mem.le8 (Z_to_bv 64 (re_hp e))) ++
    Mem.le4 (Z_to_bv 64 (Z.of_nat (length K))) ++ (re_pad2 e ++ concat (map entry_bytes post) ++ tail)).
  { intros K. rewrite map_app, concat_app. cbn [map concat]. rewrite EX. rewrite <- !app_assoc. reflexivity. }
  assert (HLA : Z.of_nat (length (concat (map entry_bytes pre) ++ X ++ Mem.le8 (Z_to_bv 64 (re_hp e)))) = SA - G0 + 48)
    by (rewrite !length_app, HCP, HX, Mem.length_le8; unfold AENT in ESA; lia).
  pose proof (ETB ks) as EO. pose proof (ETB ks') as EN.
  assert (LC : Z.of_nat (length (concat (map entry_bytes pre) ++ X ++ Mem.le8 (Z_to_bv 64 (re_hp e)))) + 4 +
               Z.of_nat (length (re_pad2 e ++ concat (map entry_bytes post) ++ tail)) = ATABLE).
  { pose proof T2 as T2'. rewrite EO in T2'. rewrite length_app, (length_app (Mem.le4 _)), Mem.length_le4 in T2'. lia. }
  exists tail. split; [rewrite Hes; exact T1|]. split.
  { rewrite EN. rewrite length_app, (length_app (Mem.le4 _)), Mem.length_le4. lia. }
  rewrite EN. rewrite EO in T3. apply rkr_garr8_app3 in T3 as (TA & TM & TC).
  rewrite Mem.length_le4 in TC. apply rkr_garr8_app3. rewrite Mem.length_le4.
  split; [|split].
  - apply (akept_garr8 W m); [|exact TA]. intros a Ha. unfold bzs in Ha. rewrite length_map in Ha.
    apply KT; [unfold ATABLE, AENT in *; lia | lia].
  - rewrite HLA. replace (G0 + (SA - G0 + 48)) with (SA + 48) by lia.
    unfold Mem.le4. rewrite unsigned_lit_small by lia. apply rkr_le_garr8; [exact Hnh | lia].
  - apply (akept_garr8 W m); [|exact TC]. intros a Ha. unfold bzs in Ha. rewrite length_map in Ha.
    apply KT; [unfold ATABLE in *; lia | lia]. }
split.
(* the entries *)
{ apply Forall_app. split; [|apply Forall_cons].
  - rewrite Forall_forall. intros e0 He0. rewrite Forall_forall in HFpre.
    apply (aentry_ok_kept B ly S W m); [exact (HFpre e0 He0) | |].
    + intros r Hr a Ha. destruct (rkr_fp_blk ly S W m e0 (HFpre e0 He0) r Hr a Ha) as (b & Hb & Hab).
      exact (KO r a b (INE e0 r (in_or_app _ _ _ (or_introl He0)) Hr) Ha (OBP e0 b He0 Hb) Hab).
    + intros b Hb. exact (BLE e0 b (in_or_app _ _ _ (or_introl He0)) Hb).
  - (* entry i, its keys swap-removed *)
    unfold aentry_ok, re_nheld.
    cbn [entry_keys re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    split; [exact E6|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|].
    split.
    { destruct E10 as [E10 | (Hc & Hbin & Hj & Hg)]; [left; exact E10 | right].
      assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
      split; [exact Hc|].
      split.
      { apply (BLE _ _ Hx'). unfold aentry_blks. cbn [entry_keys re_cap re_buf]. rewrite Ec.
        apply in_or_app. left. left. reflexivity. }
      split; [exact Hj|].
      apply (akept_garr8 W m); [|exact Hg]. intros a Ha.
      apply (KO (gfp (re_buf e) (bzs (re_U e ++ re_junk e))) a (re_buf e, re_cap e)).
      - apply (INE _ _ Hx'). unfold aentry_fp. cbn [entry_keys re_cap re_buf re_U re_junk]. rewrite Ec.
        apply in_or_app. left. left. reflexivity.
      - exact Ha.
      - apply OBX. rewrite Ec. apply in_or_app. left. left. reflexivity.
      - cbn [fst snd]. unfold bzs in Ha. rewrite length_map, length_app in Ha. lia. }
    split; [rewrite Hlen'; lia|].
    split.
    { right. split; [exact Hhp|].
      split.
      { apply (BLE _ _ Hx'). unfold aentry_blks. cbn [entry_keys re_hp re_kh]. rewrite (proj2 (Z.eqb_neq _ _) Hhp).
        apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
      split; [rewrite Hlen'; lia|]. split; [exact Hkh8|].
      destruct (rkr_swap_shape (0, [], []) n ks Hn) as (l1 & y & l2 & Eks & Hl1 & [(-> & Esw) | (l3 & z & -> & Esw)]);
        rewrite Esw in Eks'; subst ks'.
      - (* n was the last index: slot n leaves the array *)
        rewrite Eks, rkr_kp_app in Hgp. unfold bzs in Hgp. rewrite map_app in Hgp. apply garr8_app in Hgp as [Hg1 _].
        apply (akept_garr8 W m); [|exact Hg1]. intros a Ha. apply KH; [exact Ha|].
        unfold bzs in Ha. rewrite length_map, rkr_key_ptrs_len in Ha. lia.
      - (* the last key moved into slot n *)
        assert (Eks2 : ks = (l1 ++ y :: l3) ++ [z]) by (rewrite Eks, <- app_assoc; reflexivity).
        assert (Hz : In z ks) by (rewrite Eks2; apply in_or_app; right; left; reflexivity).
        rewrite Eks2, rkr_nth_last in Hslot.
        rewrite Eks, rkr_kp_app, relay_instance_gone_b_lem.rigl_kp_cons, rkr_kp_app in Hgp.
        apply rkr_garr8_app3 in Hgp as (Hg1 & _ & Hg3).
        unfold bzs in Hg3. rewrite map_app in Hg3. apply garr8_app in Hg3 as [Hg3 _].
        rewrite Mem.length_le8 in Hg3.
        rewrite rkr_kp_app, relay_instance_gone_b_lem.rigl_kp_cons. apply rkr_garr8_app3. rewrite Mem.length_le8.
        split; [|split].
        + apply (akept_garr8 W m); [|exact Hg1]. intros a Ha. unfold bzs in Ha. rewrite length_map, rkr_key_ptrs_len in Ha.
          apply KH; [unfold bzs; rewrite length_map, rkr_key_ptrs_len, length_app; cbn [length]; lia | lia].
        + rewrite rkr_key_ptrs_len, Hl1. replace (re_hp e + Z.of_nat (8 * n)) with (re_hp e + 8 * Z.of_nat n) by lia.
          unfold Mem.le8, word_to_le_bytes. rewrite unsigned_lit_small by exact (KB z Hz).
          apply rkr_le_garr8; [exact Hslot | pose proof (KB z Hz); lia].
        + apply (akept_garr8 W m); [|exact Hg3]. intros a Ha. unfold bzs in Ha. rewrite length_map, !rkr_key_ptrs_len in Ha.
          apply KH; [unfold bzs; rewrite length_map, rkr_key_ptrs_len, length_app; cbn [length]; lia | lia]. }
    split.
    { rewrite Eks', relay_instance_gone_b_lem.rig_swap_map by exact Hn. apply NoDup_ListNoDup.
      apply relay_instance_gone_b_lem.rig_swap_nodup; [rewrite length_map; exact Hn | apply NoDup_ListNoDup; exact E13]. }
    split.
    { rewrite Eks', relay_instance_gone_b_lem.rig_swap_map by exact Hn. apply NoDup_ListNoDup.
      apply relay_instance_gone_b_lem.rig_swap_nodup; [rewrite length_map; exact Hn | apply NoDup_ListNoDup; exact E14]. }
    rewrite Forall_forall. intros k Hk.
    assert (Hk0 : In k ks) by (rewrite Eks' in Hk; exact (relay_instance_gone_b_lem.rig_swap_incl _ _ _ _ Hk)).
    destruct (E15 k Hk0) as (K1 & K2 & K3 & K4).
    split.
    { apply (BLE _ _ Hx'). unfold aentry_blks. cbn [entry_keys re_keys]. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). exact Hk. }
    split; [|split; [exact K3 | exact K4]].
    apply (akept_garr8 W m); [|exact K2]. intros a Ha.
    apply (KO (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) a (key_addr k, Z.of_nat (length (key_text k)) + 1)).
    + apply (INE _ _ Hx'). unfold aentry_fp. cbn [entry_keys re_keys]. apply in_or_app. right. right.
      apply (in_map (fun k0 => gfp (key_addr k0) (bzs (key_text k0 ++ [Z_to_bv 8 0])))). exact Hk.
    + exact Ha.
    + apply OBX. apply in_or_app. right.
      apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). exact Hk0.
    + cbn [fst snd]. unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
  - rewrite Forall_forall. intros e0 He0. rewrite Forall_forall in HFpost.
    apply (aentry_ok_kept B ly S W m); [exact (HFpost e0 He0) | |].
    + assert (He0' : In e0 (pre ++ entry_keys e ks' :: post)) by (apply in_or_app; right; right; exact He0).
      intros r Hr a Ha. destruct (rkr_fp_blk ly S W m e0 (HFpost e0 He0) r Hr a Ha) as (b & Hb & Hab).
      exact (KO r a b (INE e0 r He0' Hr) Ha (OBQ e0 b He0 Hb) Hab).
    + intros b Hb. apply (BLE e0 b); [apply in_or_app; right; right; exact He0 | exact Hb]. }
(* arelay_at's last conjunct (W8's W_rep: NoDup of the fds, and no entry block is the table): the fds as before; an
   entry's blocks after the swap are among its blocks before (its keys are a sublist: rig_swap_incl) *)
destruct H11 as [H11 H12]. split.
{ rewrite map_app in H11 |- *. cbn [map entry_keys re_fd] in H11 |- *. exact H11. }
apply Forall_app in H12 as [G1 G2]. apply Forall_cons_iff in G2 as [G3 G4].
apply Forall_app. split; [exact G1|]. apply Forall_cons; [|exact G4].
intros b Hb. apply G3. unfold aentry_blks in Hb |- *.
cbn [entry_keys re_cap re_buf re_hp re_kh re_keys] in Hb |- *.
apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb|right].
apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb|right].
apply in_map_iff in Hb as (k & <- & Hk).
apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))).
rewrite Eks' in Hk. exact (relay_instance_gone_b_lem.rig_swap_incl _ _ _ _ Hk).
Qed.

(* ------------------------------------------------------------------ 3-5. strncmp's view of a key and the prefix *)
Lemma rkr_agree : forall (W : world SEGS) m x y (kt : list byte) (pre : list Z),
  garr8 SEGS (arm W m) x (bzs (kt ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) kt ->
  garr8 SEGS (arm W m) y (pre ++ [0]) -> ~ In 0 pre ->
  (astrn_agree W m x y (Z.of_nat (length pre)) <-> has_prefix pre (bzs kt) = true).
Proof.
intros W m x y kt pre Hx Hnz Hy Hpz. unfold astrn_agree. split.
- intros HA.
  assert (P : forall i, (i <= length pre)%nat -> forall j, (j < i)%nat ->
    aview SEGS (w_H W) m (x + Z.of_nat j) = Some (nth j pre 0)).
  { induction i as [|i IH]; intros Hi j Hj; [lia|].
    destruct (Nat.lt_ge_cases j i) as [Hji | Hji]; [apply IH; lia|].
    assert (j = i) by lia. subst j.
    rewrite (HA (Z.of_nat i)).
    + pose proof (rkr_view W m y _ i Hy ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
      rewrite app_nth1 in Hv by lia. exact Hv.
    + lia.
    + intros j' Hj' E. rewrite <- (Z2Nat.id j') in E by lia.
      rewrite (IH ltac:(lia) (Z.to_nat j') ltac:(lia)) in E.
      injection E as E. apply Hpz. rewrite <- E. apply nth_In. lia. }
  assert (HL : (length pre <= length kt)%nat).
  { destruct (Nat.le_gt_cases (length pre) (length kt)) as [H|H]; [exact H|exfalso].
    pose proof (P (length pre) (le_n _) (length kt) H) as E1.
    pose proof (rkr_view W m x _ (length kt) Hx ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as E2.
    rewrite rkr_nth_key_end in E2. rewrite E1 in E2. injection E2 as E2. apply Hpz. rewrite <- E2. apply nth_In. exact H. }
  unfold has_prefix.
  replace (firstn (length pre) (bzs kt)) with pre; [apply list_eqb_refl|].
  symmetry. apply (nth_ext _ _ 0 0).
  + rewrite length_firstn. unfold bzs. rewrite length_map. lia.
  + intros j Hj. rewrite length_firstn in Hj. unfold bzs in Hj. rewrite length_map in Hj.
    rewrite relay_instance_gone_b_lem.rigl_nth_firstn by lia.
    pose proof (rkr_view W m x _ j Hx ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as E2.
    rewrite (P (length pre) (le_n _) j ltac:(lia)) in E2.
    unfold bzs in E2 |- *. rewrite map_app, app_nth1 in E2 by (rewrite length_map; lia).
    injection E2 as E2. symmetry. exact E2.
- intros Hh i Hi _.
  unfold has_prefix in Hh. apply list_eqb_true in Hh.
  assert (HL : (length pre <= length kt)%nat).
  { apply (f_equal (@length Z)) in Hh. rewrite length_firstn in Hh. unfold bzs in Hh. rewrite length_map in Hh. lia. }
  rewrite <- (Z2Nat.id i) by lia.
  rewrite (rkr_view W m x _ (Z.to_nat i) Hx ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)).
  rewrite (rkr_view W m y _ (Z.to_nat i) Hy ltac:(rewrite length_app; cbn [length]; lia)).
  f_equal. rewrite app_nth1 by lia. unfold bzs. rewrite map_app, app_nth1 by (rewrite length_map; lia).
  rewrite <- Hh. rewrite relay_instance_gone_b_lem.rigl_nth_firstn by lia. reflexivity.
Qed.

Lemma rkr_first_key : forall (W : world SEGS) m x (kt : list byte) n, 0 <= n ->
  garr8 SEGS (arm W m) x (bzs (kt ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) kt ->
  first_byte SEGS W m x n 0 (Z.min (Z.of_nat (length kt)) n).
Proof.
intros W m x kt n Hn Hg Hnz. unfold first_byte. split; [lia|]. split.
- intros i Hi. assert (Hj : (Z.to_nat i < length kt)%nat) by lia.
  pose proof (rkr_view W m x _ (Z.to_nat i) Hg ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as Hv.
  rewrite Z2Nat.id in Hv by lia. rewrite rkr_nth_key in Hv by exact Hj.
  eexists. split; [exact Hv|]. apply rkr_bz_nz. intros E. apply Hnz. rewrite <- E. apply nth_In. exact Hj.
- intros Hlt. assert (HL : Z.of_nat (length kt) < n) by lia. rewrite Z.min_l by lia.
  pose proof (rkr_view W m x _ (length kt) Hg ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as Hv.
  rewrite rkr_nth_key_end in Hv. exact Hv.
Qed.

Lemma rkr_first_pre : forall (W : world SEGS) m y (pre : list Z),
  garr8 SEGS (arm W m) y (pre ++ [0]) -> ~ In 0 pre ->
  first_byte SEGS W m y (Z.of_nat (length pre)) 0 (Z.of_nat (length pre)).
Proof.
intros W m y pre Hg Hnz. unfold first_byte. split; [lia|]. split; [|intros H; exfalso; lia].
intros i Hi. assert (Hj : (Z.to_nat i < length pre)%nat) by lia.
pose proof (rkr_view W m y _ (Z.to_nat i) Hg ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
rewrite Z2Nat.id in Hv by lia. rewrite app_nth1 in Hv by exact Hj.
eexists. split; [exact Hv|]. intros E. apply Hnz. rewrite <- E. apply nth_In. exact Hj.
Qed.

(* ------------------------------------------------------------------ 6. the prefix "param_gesture <id> " *)
Lemma rkr_digits : forall f x acc, 0 <= x -> ~ In 0 acc ->
  ~ In 0 (printf_facts_c.pf_digits f x acc) /\ (length acc <= length (printf_facts_c.pf_digits f x acc))%nat.
Proof.
induction f as [|f IH]; intros x acc Hx Ha; cbn [printf_facts_c.pf_digits]; [split; [exact Ha | lia]|].
destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. split; [|cbn [length]; lia].
  intros [H|H]; [lia | exact (Ha H)].
- apply Z.ltb_ge in E.
  assert (H10 : 0 <= x mod 10) by (apply Z.mod_pos_bound; lia).
  destruct (IH (x / 10) ((48 + x mod 10) :: acc)) as [H1 H2].
  + apply Z.div_pos; lia.
  + intros [H|H]; [lia | exact (Ha H)].
  + split; [exact H1|]. cbn [length] in H2. lia.
Qed.

Lemma rkr_digits_le : forall f x acc, (length (printf_facts_c.pf_digits f x acc) <= length acc + f)%nat.
Proof.
induction f as [|f IH]; intros x acc; cbn [printf_facts_c.pf_digits]; [lia|].
destruct (x <? 10); [cbn [length]; lia|]. specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma rkr_digits11 : forall x, 0 <= x ->
  ~ In 0 (printf_facts_c.pf_digits 11 x []) /\ (1 <= length (printf_facts_c.pf_digits 11 x []) <= 11)%nat.
Proof.
intros x Hx. destruct (rkr_digits 11 x [] Hx (fun H => H)) as [H1 _]. split; [exact H1|].
pose proof (rkr_digits_le 11 x []) as H3. cbn [length] in H3. split; [|lia].
change (printf_facts_c.pf_digits 11 x []) with
  (if x <? 10 then [48 + x] else printf_facts_c.pf_digits 10 (x / 10) [48 + x mod 10]).
destruct (x <? 10) eqn:E; [cbn [length]; lia|].
apply Z.ltb_ge in E.
destruct (rkr_digits 10 (x / 10) [48 + x mod 10]) as [_ H2].
- apply Z.div_pos; lia.
- assert (Hm : 0 <= x mod 10) by (apply Z.mod_pos_bound; lia). intros [Hd|[]]; lia.
- cbn [length] in H2. lia.
Qed.

Lemma rkr_pre_nz : forall cx, ~ In 0 (gpre cx) /\ (16 <= length (gpre cx))%nat /\ (length (gpre cx) <= 27)%nat.
Proof.
intros cx. unfold gpre, relay_instance_gone_b_c.instance_prefix.
assert (HD : ~ In 0 (printf_facts_c.pf_dec (gxID cx)) /\
             (1 <= length (printf_facts_c.pf_dec (gxID cx)) <= 12)%nat).
{ unfold printf_facts_c.pf_dec. destruct (gxID cx <? 0) eqn:E.
  - apply Z.ltb_lt in E. destruct (rkr_digits11 (- gxID cx) ltac:(lia)) as [H1 H2].
    split; [intros [H|H]; [lia | exact (H1 H)] | cbn [length]; lia].
  - apply Z.ltb_ge in E. destruct (rkr_digits11 (gxID cx) E) as [H1 H2]. split; [exact H1 | lia]. }
destruct HD as [HD1 HD2]. split; [|split].
- rewrite !in_app_iff. intros [H|[H|[H|H]]].
  + unfold RelayModel.K_GESTURE in H. cbn in H. lia.
  + cbn in H. lia.
  + exact (HD1 H).
  + cbn in H. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

(* ==== keep block, END arm (RigKeyKeep): the memory facts after gesture_end, free and the two stores ==== *)
(* ---- generic facts ---- *)
Ltac rkk_infp := repeat (first [left; reflexivity | right]).

Lemma rkk_kept_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof. intros W W1 W2 m m1 m2 a [V1 R1] [V2 R2]. split; [rewrite V2; exact V1 | intros Hw; apply R2; apply R1; exact Hw]. Qed.

Lemma rkk_vm_v : forall (W W' : world SEGS) m m' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v.
Proof.
  intros W W' m m' a n v HK Hv k Hk. unfold arm.
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)); [exact (Hv k Hk)|].
  exact (HK (a + Z.of_nat k) ltac:(lia)).
Qed.

Lemma rkk_garr8_v : forall (W W' : world SEGS) m m' a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (arm W m) a l -> garr8 SEGS (arm W' m') a l.
Proof.
  intros W W' m m' a l HK Hg. apply (garr8_frame SEGS (arm W m) (arm W' m') a l Hg).
  intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (HK x Hx).
Qed.

(* an image byte is never hidden: its writability follows its presence *)
Lemma rkk_img_wr : forall (W W' : world SEGS) m m' a, in_img SEGS a ->
  (apresent (w_H W) m a -> apresent (w_H W') m' a) ->
  writable_at SEGS (arm W m) a -> writable_at SEGS (arm W' m') a.
Proof.
  intros W W' m m' a Hi HP. pose proof (pa_segs_low a Hi) as Hl. pose proof asan_consts as (_ & _ & _ & _ & C5).
  rewrite C5 in Hl.
  assert (Hx : in_img SEGS (bv_unsigned (Z_to_bv 64 a))) by (rewrite unsigned_lit_small by lia; exact Hi).
  pose proof (hidden_not_img SEGS W _ Hx) as H1. pose proof (hidden_not_img SEGS W' _ Hx) as H2.
  unfold writable_at, wview, arm, mrestrict. rewrite H1, H2.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [intros _; discriminate|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|exact (fun H => H)].
  intros _. exfalso. destruct (HP (conj H1 (ex_intro _ b E))) as [_ [b2 E2]]. rewrite E2 in E'. discriminate E'.
Qed.

(* a byte a reader sees, off the read-only segments, is writable (W_gestures_end.v gse_writable_view's argument) *)
Lemma rkk_view_wr : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
  aview SEGS H m a = Some v -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
  intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
  unfold seg_rom, memory_read in Hv.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
  change (Z.of_N 1) with 1 in Ef. rewrite Ef.
  destruct (seg_readable sg); [|discriminate].
  destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
  destruct (seg_writable sg) eqn:Ew.
  - destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
    exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
  - exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.

Lemma rkk_vm_some : forall H (m : word -> option byte) a n v x, val_mem SEGS (mrestrict H m) a n v ->
  a <= x < a + Z.of_nat n -> aview SEGS H m x <> None.
Proof.
  intros H m a n v x Hv Hx. unfold aview. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  rewrite (Hv (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.

(* what a journal at G keeps (W_gestures_end.v's gse_keep_img / gse_keep_high / gse_keep_blk, and the frames) *)
Lemma rkk_jx_img : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST ->
  fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hps Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hps Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma rkk_jx_high : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok SEGS B G -> ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma rkk_jx_blk : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok SEGS B G -> ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (rk_alb ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (rk_boi ly' S' W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
Lemma rkk_jx_frame : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok SEGS B G -> ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (cid, pos) (frames S) ->
  in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    Hf Ha Hfp Hr Hni.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hf Ha Hfp).
  apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia.
  intros HGa. exact (Hni (proj1 (HGx a HGa))).
Qed.
Lemma rkk_jx_lyF : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ly_F ly' = ly_F ly /\ frames S' = own ++ frames S.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & Hly & _ & _ & _ & Hfr & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
  split; [exact HF | exact Hfr].
Qed.
Lemma rkk_fp_spares : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
  intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
Lemma rkk_not_owned : forall ly S W mem md a, ARh ly S W mem md -> in_img SEGS a ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. intros ly S W mem md a HAR Hi Ho Hown. apply Ho. exact (proj1 (rk_alo ly S W mem md a HAR Hi) Hown). Qed.
Lemma rkk_gxSL : gx_ok SEGS B (G_SL B RG).
Proof. intros a Ha. exact (HGRIG a (rig_G_SL_RIG a Ha)). Qed.

(* the global cells, from HRGP / rg_place / HRGI / HGRIG *)
Lemma rkk_zall_in : forall x l y, zall_disjoint x l -> In y l -> zdisj x y.
Proof.
  intros x l. induction l as [|z l IH]; intros y H Hy; [destruct Hy|]. cbn [zall_disjoint] in H. destruct H as [H1 H2].
  destruct Hy as [<-|Hy]; [exact H1 | exact (IH y H2 Hy)].
Qed.
Lemma rkk_zpw_app : forall P Q, zpairwise_disjoint (P ++ Q) -> forall x y, In x P -> In y Q -> zdisj x y.
Proof.
  intros P. induction P as [|z P IH]; intros Q H x y Hx Hy; [destruct Hx|].
  cbn [app zpairwise_disjoint] in H. destruct H as [H1 H2].
  destruct Hx as [<-|Hx]; [apply (rkk_zall_in _ _ y H1); apply in_or_app; right; exact Hy | exact (IH Q H2 x y Hx Hy)].
Qed.

Lemma rkk_errno_off : forall a,
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
   rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
   rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
   rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
   rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
  ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha He.
  pose proof (rkk_zpw_app
    [(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
     (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
     (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
     (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
     (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8)]
    [(as_errno B, as_errno B + 4)] HRGP) as ZD.
  assert (ZE : forall lo hi, In (lo, hi) [(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
     (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
     (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
     (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
     (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8)] ->
     lo <= a < hi -> False).
  { intros lo hi Hin Hlh. pose proof (ZD (lo, hi) (as_errno B, as_errno B + 4) Hin ltac:(left; reflexivity)) as Z.
    unfold zdisj in Z. cbn [fst snd] in Z. lia. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]];
    (refine (ZE _ _ _ Ha); rkk_infp).
Qed.

Lemma rkk_not_SL : forall a,
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
   rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) ->
  ~ inG (G_SL B RG) a.
Proof.
  intros a Ha HG.
  pose proof (rkk_zpw_app
    [(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
     (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4)]
    [(rg_send_max RG, rg_send_max RG + 8);
     (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
     (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
     (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
     (as_errno B, as_errno B + 4)] HRGP) as ZD.
  assert (ZE : forall lo hi lo' n', In (lo, hi) [(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
     (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4)] ->
     In (lo', lo' + n') [(rg_send_max RG, rg_send_max RG + 8);
     (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
     (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
     (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
     (as_errno B, as_errno B + 4)] ->
     lo <= a < hi -> in_zr a (lo', n') -> False).
  { intros lo hi lo' n' Hin Hin' Hlh Hz. pose proof (ZD (lo, hi) (lo', lo' + n') Hin Hin') as Z.
    unfold zdisj, in_zr in *. cbn [fst snd] in *. lia. }
  unfold inG, G_SL in HG. apply Exists_exists in HG as (y & Hy & Hz).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
  (destruct Hy as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (refine (ZE _ _ _ _ _ _ Ha Hz); rkk_infp)).
Qed.

(* the relay's and the output's global cells (not errno): image bytes, not owned, not errno, and (the generic
   journal's image clause exempts the program statics PST) no byte of PST, by the Section's PSTG *)
Lemma rkk_cellP : forall cx a, GBASE B ARx MT RP MMAX RG cx ->
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
   rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
   rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
   rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
   rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ Exists (in_zr a) PST.
Proof.
  intros cx a HB Ha. pose proof (rkk_errno_off a Ha) as He.
  destruct HB as (_ & _ & _ & HPL & _). destruct HPL as (_ & _ & _ & _ & _ & _ & Hrng & _).
  assert (HG : forall lo len, In (lo, len) (G_SL B RG) -> lo <= a < lo + len ->
    in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
  { intros lo len Hin Hl. destruct (HGRIG a (rig_G_SL_RIG a ltac:(unfold inG; apply Exists_exists;
      exists (lo, len); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]))) as (H1 & H2 & _).
    split; [exact H1 | exact H2]. }
  assert (HR : rg_rng RG a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
    by (intros Hr; destruct (Hrng a Hr) as (H1 & H2 & _); split; assumption).
  assert (HI : (rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
    rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
    in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)) by exact (HRGI a).
  unfold rg_rng in HR.
  assert (Hio : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
  { destruct Ha as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]].
    - apply HR; tauto.
    - apply HR; tauto.
    - apply HR; tauto.
    - apply HR; tauto.
    - apply HI; tauto.
    - apply HI; tauto.
    - apply (HG (rg_nout RG) 8); [unfold G_SL; rkk_infp | exact H].
    - apply (HG (rg_capout RG) 8); [unfold G_SL; rkk_infp | exact H].
    - apply (HG (rg_out RG) 8); [unfold G_SL; rkk_infp | exact H].
    - apply HI; tauto.
    - apply (HG (rg_client_broken RG) 1); [unfold G_SL; rkk_infp | exact H].
    - apply HI; tauto.
    - apply (HG (rg_send_eintr RG) 1); [unfold G_SL; rkk_infp | exact H]. }
  destruct Hio as [H1 H2]. split; [exact H1|]. split; [exact H2|]. split; [exact He|].
  apply PSTG. destruct Ha as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]].
  - left. unfold inG, G_RIG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - left. apply rig_G_DR_RIG. unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - right; left. exact H.
  - right; right; left. exact H.
  - right; right; right; left. exact H.
  - right; right; right; right; left. exact H.
  - left. apply rig_G_SL_RIG. unfold inG, G_SL. apply Exists_exists. exists (rg_nout RG, 8).
    split; [rkk_infp | unfold in_zr; cbn [fst snd]; lia].
  - left. apply rig_G_SL_RIG. unfold inG, G_SL. apply Exists_exists. exists (rg_capout RG, 8).
    split; [rkk_infp | unfold in_zr; cbn [fst snd]; lia].
  - left. apply rig_G_SL_RIG. unfold inG, G_SL. apply Exists_exists. exists (rg_out RG, 8).
    split; [rkk_infp | unfold in_zr; cbn [fst snd]; lia].
  - right; right; right; right; right; left. exact H.
  - left. apply rig_G_SL_RIG. unfold inG, G_SL. apply Exists_exists. exists (rg_client_broken RG, 1).
    split; [rkk_infp | unfold in_zr; cbn [fst snd]; lia].
  - right; right; right; right; right; right. exact H.
  - left. apply rig_G_SL_RIG. unfold inG, G_SL. apply Exists_exists. exists (rg_send_eintr RG, 1).
    split; [rkk_infp | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma rkk_errno_G : forall a, as_errno B <= a < as_errno B + 4 -> inG (G_RIG B RG) a.
Proof.
  intros a Ha. apply rig_G_SL_RIG. unfold inG, G_SL. apply Exists_exists. exists (as_errno B, 4).
  split; [rkk_infp | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma rkk_perm_mid3 : forall {A : Type} (P Q R M M' : list A) (x : A), Permutation M (x :: M') ->
  Permutation (P ++ (Q ++ M) ++ R) (x :: P ++ (Q ++ M') ++ R).
Proof.
  intros A P Q R M M' x HM.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; apply Permutation_app_head; exact HM|].
  rewrite <- !app_assoc. cbn [app].
  rewrite (app_assoc P Q (x :: M' ++ R)), (app_assoc P Q (M' ++ R)).
  apply Permutation_sym, Permutation_middle.
Qed.

(* a byte a source's predicate reads: in its struct, or in one of its blocks *)
Lemma rkk_alist_loc : forall ly S W m LA l lines, alist_at B ly S W m LA l lines ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (LA <= a < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= a < fst b + snd b.
Proof.
  intros ly S W m LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) r Hr a Ha.
  rewrite Forall_forall in H9.
  unfold alist_fp in Hr. destruct Hr as [<-|Hr]; [left; exact Ha|]. right.
  apply in_app_or in Hr. destruct Hr as [Hr|Hr].
  - destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)].
    + rewrite Hc in Hr. cbn in Hr. destruct Hr.
    + assert (E : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hr.
      destruct Hr as [<-|[]]. exists (hl_v l, AREC * hl_cap l). split.
      * unfold alist_blks. rewrite E. apply in_or_app. left. left. reflexivity.
      * unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, length_app, rkk_len_recs in Ha.
        unfold hl_n in Hj. unfold AREC in *. lia.
  - apply in_map_iff in Hr. destruct Hr as (r' & <- & Hr').
    exists (fst r', Z.of_nat (length (snd r')) + 1). split.
    + unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hr'.
    + unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
Qed.

Lemma rkk_asrc_loc : forall ly S W m HA h, asrc_at B ly S W m HA h ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r ->
  (HA <= a < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= a < fst b + snd b.
Proof.
  intros ly S W m HA h Hs r Hr a Ha.
  pose proof Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & H19 & _ & _ & H22 & H23 & _).
  assert (LIFT : forall LA l, (forall b, In b (alist_blks l) -> In b (asrc_blks h)) -> HA <= LA -> LA + 16 <= HA + ASRC ->
      ((LA <= a < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= a < fst b + snd b) ->
      (HA <= a < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= a < fst b + snd b).
  { intros LA l Hs' H1 H2 [Hx|(b & Hb & Hx)]; [left; lia | right; exists b; split; [apply Hs'; exact Hb | exact Hx]]. }
  unfold asrc_fp in Hr. destruct Hr as [<-|[<-|Hr]].
  - left. exact Ha.
  - right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|].
    unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map in Ha. lia.
  - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
    + apply (LIFT (HA + 16) (hs_pending h)); [intros b Hb; right; apply in_or_app; left; exact Hb | lia | unfold ASRC; lia |].
      exact (rkk_alist_loc _ _ _ _ _ _ _ H10 r Hr a Ha).
    + apply in_app_or in Hr. destruct Hr as [Hr|Hr].
      * apply (LIFT (HA + 64) (hs_expected h)); [intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb
          | lia | unfold ASRC; lia |].
        exact (rkk_alist_loc _ _ _ _ _ _ _ H22 r Hr a Ha).
      * apply (LIFT (HA + 80) (hs_held h)); [intros b Hb; right; apply in_or_app; right; apply in_or_app; right; exact Hb
          | lia | unfold ASRC; lia |].
        exact (rkk_alist_loc _ _ _ _ _ _ _ H23 r Hr a Ha).
Qed.

(* a byte an entry with fewer held keys reads (rkr_fp_blk's argument, from the entry with all its keys) *)
Lemma rkk_fp_blk_ks : forall ly S W m e ks ks0, aentry_ok B ly S W m (entry_keys e ks) -> (length ks0 <= length ks)%nat ->
  forall r, In r (aentry_fp (entry_keys e ks0)) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks (entry_keys e ks0)) /\ fst b <= a < fst b + snd b.
Proof.
  intros ly S W m e ks ks0 (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15) Hl r Hr a Ha.
  cbn [entry_keys re_cap re_buf re_U re_junk re_used re_hp re_kh re_keys re_nheld] in E7, E10, E12.
  unfold aentry_fp in Hr. cbn [entry_keys re_cap re_buf re_U re_junk re_hp re_keys] in Hr.
  apply in_app_or in Hr. destruct Hr as [Hr | [Hr | Hr]].
  - revert Hr. destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; intros Hr; [destruct Hr|].
    destruct Hr as [<- | []].
    destruct E10 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
    exists (re_buf e, re_cap e). split.
    + unfold aentry_blks. cbn [entry_keys re_cap re_buf]. rewrite (proj2 (Z.eqb_neq _ _) Hc0). apply in_or_app. left. left. reflexivity.
    + unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, length_app in Ha. lia.
  - subst r. destruct E12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    + exfalso. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, rkr_key_ptrs_len in Ha.
      rewrite Hk in Hl. cbn [length] in Hl. lia.
    + exists (re_hp e, re_kh e). split.
      * unfold aentry_blks. cbn [entry_keys re_hp re_kh]. rewrite (proj2 (Z.eqb_neq _ _) Hz).
        apply in_or_app. right. apply in_or_app. left. left. reflexivity.
      * unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, rkr_key_ptrs_len in Ha.
        unfold re_nheld in Hk1. cbn [entry_keys re_keys] in Hk1. lia.
  - apply in_map_iff in Hr as (k & <- & Hk). exists (key_addr k, Z.of_nat (length (key_text k)) + 1). split.
    + unfold aentry_blks. cbn [entry_keys re_keys]. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). exact Hk.
    + unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
Qed.

(* ---- the END arm's states: (ly1, S1, W1, mA) at gesture_end (key), (ly2, S2, W2, mB) after it, mB' at free (key),
   (ly3, S3, W3, mC) after free, mD after the two stores (nheld at SA + 48, held[n] at hp + 8 n) ---- *)
Section e.
Variables (cx : gcx) (i n r : nat) (F FL fpos : Z) (qd : list (rentry * hsrc)) (cB : ctl) (OB : list byte) (capB : Z)
  (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 : Z)
  (ks Ed : list (Z * list byte * list byte)) (f : nat) (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z)
  (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (mA : word -> option byte) (mdA : Model) (kA : Z)
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mB mB' : word -> option byte) (mdB : Model) (kB : Z) (out2' : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mC mD : word -> option byte) (mdC mdD : Model) (kD : Z)
  (l1 l2 : list (Z * Z)) (slo shi : Z).
#[local] Notation ek_k := (nth n ks (0, [], [])).
#[local] Notation ek_kt := (key_text ek_k).
#[local] Notation ek_xl := (Z.of_nat (length ek_kt)).
#[local] Notation ek_ks2 := (swap_remove (0, [], []) n ks).
#[local] Notation ek_SA := (gSA cx i).
#[local] Notation ek_hp := (re_hp e1).
#[local] Notation ek_no2 := (Z.of_nat (length O2)).
#[local] Notation ek_c2 := (ge_ctl c2 ek_xl).
#[local] Notation ek_O2 := (ge_O c2 O2 ek_kt).
#[local] Notation ek_cap2 := (ge_cap c2 (gxmx cx) ek_no2 cap2 ek_xl).
#[local] Notation ek_kl := (nth (length ks - 1) ks (0, [], [])).
#[local] Notation ek_kb := (key_addr ek_k, ek_xl + 1).
#[local] Notation ek_T := (gxG0 cx, ATABLE).
#[local] Notation ek_H := (re_hp e1, re_kh e1).
#[local] Notation ek_es := (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx)).
#[local] Notation ek_es2 := (map fst qd ++ entry_keys e1 ek_ks2 :: skipn (S i) (gxes cx)).
#[local] Notation ek_open := (re_eof (gnth cx i) =? 0).
#[local] Notation ek_src := (gdone_srcs (firstn i (gps cx)) qd ++ (if ek_open then asrc_blks h1 else []) ++
  rig_srcs (skipn (S i) (gps cx))).
#[local] Notation ek_C1 a := (ek_SA + 48 <= a < ek_SA + 52).
#[local] Notation ek_C2 a := (ek_hp + 8 * Z.of_nat n <= a < ek_hp + 8 * Z.of_nat n + 8).

Hypothesis HB : GBASE B ARx MT RP MMAX RG cx.
Hypothesis HJ1 : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx)
  (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 mA mdA kA.
Hypothesis HG : GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA.
Hypothesis HAP1 : apres_kept B (gxW cx) (gxmem cx) W1 mA.
Hypothesis HF1 : g_frame cx fpos F FL ly1 W1 mA.
Hypothesis HL1 : alock_at RG W1 mA true.
Hypothesis HLS1 : g_lslots RG cx F W1 mA.
Hypothesis H32 : val_mem SEGS (arm W1 mA) (gsp1 cx + 32) 8 ((ek_SA + 48) mod 8 + 3).
Hypothesis H88 : val_mem SEGS (arm W1 mA) (gsp1 cx + 88) 8 (Z.of_nat i).
Hypothesis HJG : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) 0 [] GE_STK (gsp1 cx) (ablocks_fp (aout_blks cap2 out2))
  ly1 S1 [] W1 mA mdA [] ly2 S2 [] W2 mB mdB kB.
Hypothesis HAP12 : apres_kept B W1 mA W2 mB.
Hypothesis HPG : exists rest, Permutation (ablocks B ly1 S1) (aout_blks cap2 out2 ++ rest) /\
  Permutation (ablocks B ly2 S2) (aout_blks ek_cap2 out2' ++ rest).
Hypothesis HO2 : aout_at B RG ly2 S2 W2 mB ek_c2 ek_O2 (gxmx cx) (ge_no c2 ek_no2 ek_xl) ek_cap2 out2'.
Hypothesis HK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) ->
  aview SEGS (w_H W2) mB' a = aview SEGS (w_H W2) mB a.
Hypothesis HP2 : forall a, apresent (w_H W2) mB a -> apresent (w_H W2) mB' a.
Hypothesis HAR3 : ARh ly3 S3 W3 mC mdC.
Hypothesis HL2 : ablocks B ly2 S2 = l1 ++ ek_kb :: l2.
Hypothesis HL3 : ablocks B ly3 S3 = l1 ++ l2.
Hypothesis HCK : acall_kept SEGS B ly2 S2 W2 mB' W3 mC slo shi (fun a => key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1)).
Hypothesis Hslo : gsp1 cx - DRAIN_STK_x <= slo.
Hypothesis Hshi : shi <= gsp1 cx.
Hypothesis HERR : forall j, 0 <= j < 4 -> aview SEGS (w_H W3) mC (as_errno B + j) = aview SEGS (w_H W2) mB' (as_errno B + j).
Hypothesis HAPF : forall a, in_img SEGS a -> ~ aowned B ly2 S2 a -> ~ aowned B ly3 S3 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1)) -> apresent (w_H W2) mB' a -> apresent (w_H W3) mC a.
Hypothesis HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ ek_C1 a -> ~ ek_C2 a ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W3) mC a.
Hypothesis HP3 : forall a, apresent (w_H W3) mC a -> apresent (w_H W3) mD a.
Hypothesis HNH : val_mem SEGS (arm W3 mD) (ek_SA + 48) 4 (Z.of_nat (length ek_ks2)).
Hypothesis HSL : val_mem SEGS (arm W3 mD) (ek_hp + 8 * Z.of_nat n) 8 (key_addr ek_kl).
Hypothesis HJ3 : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx)
  (gxmem cx) (gxmd cx) [(1, fpos)] ly3 S3 [] W3 mD mdD kD.

(* ---- GIN's facts, and the three allocator states ---- *)
Lemma ek_gin :
  (i < length (gxes cx))%nat /\ length qd = i /\ length ks = (n + S r)%nat /\
  arelay_at B RG ly1 S1 W1 mA (gxG0 cx) ek_es /\
  aout_at B RG ly1 S1 W1 mA c2 O2 (gxmx cx) ek_no2 cap2 out2 /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly1 S1 W1 mA (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  (ek_open = true -> asrc_at B ly1 S1 W1 mA (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 mA (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W1 mA a) /\
  Permutation (ablocks B ly1 S1) (ek_T :: concat (map aentry_blks ek_es) ++ ek_src ++ aout_blks cap2 out2 ++ gxrest cx) /\
  garr8 SEGS (arm W1 mA) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W1 mA) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
  pose proof HG as HG'. unfold GIN in HG'. cbv zeta in HG'.
  destruct HG' as (G1 & G2 & _ & _ & _ & G6 & _ & _ & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & _).
  split; [exact G1|]. split; [exact G2|]. split; [exact G6|]. split; [exact G9|]. split; [exact G10|].
  split; [exact G11|]. split; [exact G12|]. split; [exact G13|]. split; [exact G14|].
  split; [rewrite <- !app_assoc; exact G15|]. split; [exact G16 | exact G17].
Qed.

Lemma ek_ar1 : ARh ly1 S1 W1 mA mdA.
Proof. eapply rk_jAR. exact HJ1. Qed.
Lemma ek_ar2 : ARh ly2 S2 W2 mB mdB.
Proof. eapply rk_jAR. exact HJG. Qed.
Lemma ek_ar4 : ARh ly3 S3 W3 mD mdD.
Proof. eapply rk_jAR. exact HJ3. Qed.

Lemma ek_nlt : (n < length ks)%nat.
Proof. destruct ek_gin as (_ & _ & E & _). lia. Qed.

(* entry i as KEY reads it (rkr_entry_at) *)
Lemma ek_entry :
  In ek_T (ablocks B ly1 S1) /\ 4096 <= gxG0 cx /\ gxG0 cx + ATABLE <= alloc_ceiling /\
  gxG0 cx <= ek_SA /\ ek_SA + AENT <= gxG0 cx + ATABLE /\
  ek_hp <> 0 /\ In ek_H (ablocks B ly1 S1) /\ 8 * Z.of_nat (length ks) <= re_kh e1 /\
  In ek_kb (ablocks B ly1 S1).
Proof.
  destruct ek_gin as (G1 & G2 & G6 & G9 & _).
  pose proof (rkr_entry_at ly1 S1 W1 mA mdA (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n ek_ar1 G9 ek_nlt) as R.
  cbv zeta in R. rewrite length_map, G2 in R.
  destruct R as (R1 & _ & R3 & R4 & R5 & _ & _ & _ & R9 & R10 & R11 & _ & _ & _ & R15 & _).
  assert (ESA : gSA cx i = gxG0 cx + AENT * Z.of_nat i) by reflexivity.
  split; [exact R1|]. split; [exact R3|]. split; [exact R4|]. split; [rewrite ESA; unfold AENT; lia|].
  split; [rewrite ESA; exact R5|]. split; [exact R9|]. split; [exact R10|]. split; [exact R11 | exact R15].
Qed.

(* ---- the blocks: the key's block leaves; every other block of GIN's list stays ---- *)
#[local] Notation ek_P2 := (ek_T :: concat (map aentry_blks ek_es2) ++ ek_src).

Lemma ek_ae : forall ks0, aentry_blks (entry_keys e1 ks0) =
  ((if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ (if re_hp e1 =? 0 then [] else [ek_H])) ++
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks0.
Proof. intros ks0. unfold aentry_blks. cbn [entry_keys re_cap re_buf re_hp re_kh re_keys]. rewrite app_assoc. reflexivity. Qed.

Lemma ek_perm_kb : Permutation (concat (map aentry_blks ek_es)) (ek_kb :: concat (map aentry_blks ek_es2)).
Proof.
  rewrite !map_app, !concat_app. cbn [map concat]. rewrite !ek_ae.
  apply rkk_perm_mid3.
  exact (Permutation_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))
    (relay_instance_gone_b_lem.rigl_swap_perm (0, [], []) n ks ek_nlt)).
Qed.

Lemma ek_perm1 : Permutation (ablocks B ly1 S1) (ek_kb :: ek_P2 ++ aout_blks cap2 out2 ++ gxrest cx).
Proof.
  destruct ek_gin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  eapply Permutation_trans; [exact HP|].
  eapply Permutation_trans; [apply perm_skip; apply Permutation_app_tail; exact ek_perm_kb|].
  cbn [app]. rewrite <- !app_assoc. apply perm_swap.
Qed.

Lemma ek_nd : List.NoDup (ek_kb :: ek_P2 ++ aout_blks cap2 out2 ++ gxrest cx).
Proof. exact (Permutation_NoDup ek_perm1 (rk_ablocks_nodup _ _ _ _ _ ek_ar1)). Qed.

Lemma ek_inP2 : forall b, In b ek_P2 -> In b (ablocks B ly1 S1) /\ ~ In b (aout_blks cap2 out2) /\ b <> ek_kb.
Proof.
  intros b Hb. pose proof ek_nd as ND. apply List.NoDup_cons_iff in ND as [Hkb ND].
  split; [apply (Permutation_in _ (Permutation_sym ek_perm1)); right; apply in_or_app; left; exact Hb|].
  split; [intros Ho; exact (rk_nodup_app_disj _ _ b ND Hb (in_or_app _ _ _ (or_introl Ho)))|].
  intros ->. apply Hkb. apply in_or_app. left. exact Hb.
Qed.

Lemma ek_kb1 : In ek_kb (ablocks B ly1 S1) /\ ~ In ek_kb (aout_blks cap2 out2).
Proof.
  split; [apply (Permutation_in _ (Permutation_sym ek_perm1)); left; reflexivity|].
  intros Ho. pose proof ek_nd as ND. apply List.NoDup_cons_iff in ND as [Hkb _].
  apply Hkb. apply in_or_app. right. apply in_or_app. left. exact Ho.
Qed.

Lemma ek_to2 : forall b, In b (ablocks B ly1 S1) -> ~ In b (aout_blks cap2 out2) ->
  In b (ablocks B ly2 S2) /\ ~ In b (aout_blks ek_cap2 out2').
Proof.
  intros b Hb Ho. destruct HPG as (rest & P1 & P2).
  pose proof (Permutation_in _ P1 Hb) as H1. apply in_app_or in H1 as [H1|H1]; [exfalso; exact (Ho H1)|].
  split; [apply (Permutation_in _ (Permutation_sym P2)); apply in_or_app; right; exact H1|].
  intros Ho2. pose proof (Permutation_NoDup P2 (rk_ablocks_nodup _ _ _ _ _ ek_ar2)) as ND.
  exact (rk_nodup_app_disj _ _ b ND Ho2 H1).
Qed.

Lemma ek_to3 : forall b, In b (ablocks B ly2 S2) -> b <> ek_kb -> In b (ablocks B ly3 S3).
Proof.
  intros b Hb Hne. rewrite HL2 in Hb. rewrite HL3. apply in_app_or in Hb as [Hb|[Hb|Hb]].
  - apply in_or_app. left. exact Hb.
  - exfalso. apply Hne. symmetry. exact Hb.
  - apply in_or_app. right. exact Hb.
Qed.

Lemma ek_kb2 : In ek_kb (ablocks B ly2 S2).
Proof. rewrite HL2. apply in_or_app. right. left. reflexivity. Qed.

Lemma ek_out1 : forall b, In b (aout_blks cap2 out2) -> In b (ablocks B ly1 S1).
Proof.
  intros b Hb. destruct ek_gin as (_ & _ & _ & _ & G10 & _).
  destruct G10 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  unfold aout_blks in Hb. destruct H26 as [(Hc & _) | (Hc & _ & Hin & _)].
  - rewrite Hc in Hb. cbn in Hb. destruct Hb.
  - destruct (cap2 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. destruct Hb as [<-|[]]. exact Hin.
Qed.

Lemma ek_outB : forall b, In b (aout_blks ek_cap2 out2') -> In b (ablocks B ly2 S2).
Proof.
  intros b Hb.
  destruct HO2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  unfold aout_blks in Hb. destruct H26 as [(Hc & _) | (Hc & _ & Hin & _)].
  - rewrite Hc in Hb. cbn in Hb. destruct Hb.
  - destruct (ek_cap2 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. destruct Hb as [<-|[]]. exact Hin.
Qed.

Lemma ek_H_in : In ek_H (concat (map aentry_blks ek_es2)).
Proof.
  apply in_concat. exists (aentry_blks (entry_keys e1 ek_ks2)). split.
  - apply in_map. apply in_or_app. right. left. reflexivity.
  - rewrite ek_ae. apply in_or_app. left. apply in_or_app. right.
    destruct ek_entry as (_ & _ & _ & _ & _ & Hz & _). rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
Qed.

Lemma ek_src_ne : forall b, In b ek_src -> b <> ek_T /\ b <> ek_H.
Proof.
  intros b Hb. pose proof ek_nd as ND. apply List.NoDup_cons_iff in ND as [_ ND].
  cbn [app] in ND. apply List.NoDup_cons_iff in ND as [HT ND].
  split.
  - intros ->. apply HT. apply in_or_app. left. apply in_or_app. right. exact Hb.
  - intros ->. apply NoDup_app_remove_r in ND. exact (rk_nodup_app_disj _ _ _ ND ek_H_in Hb).
Qed.

(* ---- where the bytes are ---- *)
Lemma ek_frame : In (1, fpos) (frames S1) /\ frame_addr ly1 1 fpos = F /\ 4096 <= F /\ F + 128 <= alloc_ceiling /\
  off_img F 128 /\ In (1, fpos) (frames S2) /\ frame_addr ly2 1 fpos = F /\ frame_addr ly3 1 fpos = F /\
  flag_addr ly3 1 fpos = FL.
Proof.
  destruct (rkk_jar cx fpos ly1 S1 W1 mA mdA kA HJ1) as [_ Hfr].
  destruct HF1 as (HFa & HFl & _).
  destruct (rk_fb ly1 S1 W1 mA mdA 1 fpos ek_ar1 Hfr) as (HF4 & HFc & _).
  pose proof (rk_foi ly1 S1 W1 mA mdA 1 fpos ek_ar1 Hfr) as Hoff.
  rewrite HFa in HF4, HFc, Hoff. change (fs_frame_bytes 1) with 128 in HFc, Hoff.
  pose proof HJG as X2. apply rkk_jx_lyF in X2. destruct X2 as [LF2 FR2].
  pose proof HJ1 as X1. apply rkk_jx_lyF in X1. destruct X1 as [LF1 _].
  pose proof HJ3 as X3. apply rkk_jx_lyF in X3. destruct X3 as [LF3 _].
  split; [exact Hfr|]. split; [exact HFa|]. split; [exact HF4|]. split; [exact HFc|]. split; [exact Hoff|].
  split; [rewrite FR2; exact Hfr|].
  split; [unfold frame_addr in *; rewrite LF2; exact HFa|].
  split; [unfold frame_addr in *; rewrite LF3, <- LF1; exact HFa|].
  unfold flag_addr in *; rewrite LF3, <- LF1; exact HFl.
Qed.

Lemma ek_blk_loc : forall p nn a, In (p, nn) (ablocks B ly1 S1) -> p <= a < p + req_size nn ->
  4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\ ~ (F <= a < F + 128) /\ ~ (shadow_addr F <= a < shadow_addr F + 16).
Proof.
  intros p nn a Hin Ha.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar1 Hin) as (_ & H4 & Hc & Happ & _).
  pose proof (rk_boi ly1 S1 W1 mA mdA p nn ek_ar1 Hin) as Hoff.
  destruct ek_frame as (Hfr & HFa & HF4 & HFc & _).
  pose proof (rk_frame_blk_apart ly1 S1 W1 mA mdA 1 fpos p nn ek_ar1 Hfr Hin) as Hd. rewrite HFa in Hd.
  change (fs_frame_bytes 1) with 128 in Hd.
  pose proof asan_consts as (C1 & _ & C3 & _).
  assert (HF8 : 0 <= F / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  split; [lia|]. split.
  { intros Hi. pose proof (pa_img_range a Hi). unfold off_img in Hoff. lia. }
  split; [lia|].
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. rewrite C3 in Happ. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Lemma ek_cells_in : forall a, ek_C1 a \/ ek_C2 a ->
  (gxG0 cx <= a < gxG0 cx + req_size ATABLE) \/ (ek_hp <= a < ek_hp + req_size (re_kh e1)).
Proof.
  destruct ek_entry as (_ & _ & _ & HSA & HSA2 & _ & _ & Hkh & _). pose proof ek_nlt.
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hr]. change (req_size ATABLE) with 896.
  intros a [Hc|Hc]; [left | right]; unfold AENT, ATABLE in *; lia.
Qed.

Lemma ek_cells_low : forall a, ek_C1 a \/ ek_C2 a ->
  4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\ ~ (F <= a < F + 128) /\ ~ (shadow_addr F <= a < shadow_addr F + 16).
Proof.
  intros a Hc. destruct ek_entry as (HT & _ & _ & _ & _ & _ & HH & _).
  destruct (ek_cells_in a Hc) as [Ha|Ha]; [exact (ek_blk_loc _ _ a HT Ha) | exact (ek_blk_loc _ _ a HH Ha)].
Qed.

Lemma ek_cells_apart : forall ly S W m md b a, ARh ly S W m md -> In ek_T (ablocks B ly S) -> In ek_H (ablocks B ly S) ->
  In b (ablocks B ly S) -> b <> ek_T -> b <> ek_H -> fst b <= a < fst b + snd b -> ~ ek_C1 a /\ ~ ek_C2 a.
Proof.
  intros ly S W m md b a HAR HT HH Hb N1 N2 Ha.
  pose proof (rk_blk_apart ly S W m md b ek_T HAR Hb HT N1) as D1.
  pose proof (rk_blk_apart ly S W m md b ek_H HAR Hb HH N2) as D2.
  cbn [fst snd] in D1, D2.
  assert (Rb : snd b <= req_size (snd b)) by (unfold req_size; destruct (Z.eqb_spec (snd b) 0); lia).
  split; intros Hc.
  - destruct (ek_cells_in a (or_introl Hc)) as [Hx|Hx]; [lia|].
    destruct ek_entry as (_ & _ & _ & HSA & HSA2 & _). change (req_size ATABLE) with 896 in D1. unfold AENT, ATABLE in *. lia.
  - destruct (ek_cells_in a (or_intror Hc)) as [Hx|Hx]; [|lia].
    destruct ek_entry as (_ & _ & _ & _ & _ & _ & _ & Hkh & _). pose proof ek_nlt.
    pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hr]. lia.
Qed.

Lemma ek_ceil : alloc_ceiling <= gsp1 cx - DRAIN_STK_x.
Proof. exact (rkk_ceil cx HB). Qed.

(* ---- the views and the presence, from one state to the next ---- *)
Lemma ek_kb_not_img : forall a, in_img SEGS a -> ~ (key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1)).
Proof. intros a Hi Hk. destruct (ek_blk_loc _ _ a (proj1 ek_kb1) Hk) as (_ & Hn & _). exact (Hn Hi). Qed.

Lemma ek_V24_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W2) mB a.
Proof.
  intros a Hi Ho He. pose proof (rkk_img a Hi) as Ha. pose proof ek_ceil. pose proof asan_consts as (C1 & _).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low a (or_introl Hc)) as (_ & Hn & _); exact (Hn Hi)).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low a (or_intror Hc)) as (_ & Hn & _); exact (Hn Hi)).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  destruct HCK as (_ & _ & K3 & _). rewrite (K3 a Hi Ho He).
  apply HK2; lia.
Qed.

Lemma ek_P24_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W2) mB a -> apresent (w_H W3) mD a.
Proof.
  intros a Hi Ho He Hp. apply HP3. apply HAPF; [exact Hi | exact (rkk_not_owned _ _ _ _ _ a ek_ar2 Hi Ho)
    | exact (rkk_not_owned _ _ _ _ _ a HAR3 Hi Ho) | exact He | exact (ek_kb_not_img a Hi) | exact (HP2 a Hp)].
Qed.

Lemma ek_K24_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept W2 mB W3 mD a.
Proof.
  intros a Hi Ho He. split; [exact (ek_V24_img a Hi Ho He)|].
  apply (rkk_img_wr W2 W3 mB mD a Hi). exact (ek_P24_img a Hi Ho He).
Qed.

Lemma ek_V12_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W2) mB a = aview SEGS (w_H W1) mA a.
Proof.
  intros a Hi Ho He Hps Hg. eapply rkk_jx_img; [exact HJG | exact Hi | exact Ho | exact He | exact Hps | | exact Hg].
  apply rkk_fp_spares. intros [p nn] Hb.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar1 (ek_out1 _ Hb)) as (_ & H4 & _). exact H4.
Qed.

Lemma ek_K14_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> abyte_kept W1 mA W3 mD a.
Proof.
  intros a Hi Ho He Hps Hg. split; [rewrite (ek_V24_img a Hi Ho He); exact (ek_V12_img a Hi Ho He Hps Hg)|].
  apply (rkk_img_wr W1 W3 mA mD a Hi). intros Hp. exact (ek_P24_img a Hi Ho He (HAP12 a Hi Ho He Hp)).
Qed.

Lemma ek_wr3 : forall p nn a, In (p, nn) (ablocks B ly3 S3) -> p <= a < p + nn -> writable_at SEGS (arm W3 mD) a.
Proof.
  intros p nn a Hb Ha. unfold arm. apply apresent_writable.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar4 Hb) as (_ & _ & _ & _ & Hpres & _).
  pose proof (req_size_pos nn ltac:(lia)) as [_ Hr]. exact (proj1 (Hpres a ltac:(lia))).
Qed.

Lemma ek_V24_blk : forall b a, In b (ablocks B ly2 S2) -> b <> ek_kb -> fst b <= a < fst b + snd b -> ~ ek_C1 a -> ~ ek_C2 a ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W2) mB a.
Proof.
  intros [p nn] a Hb Hne Ha N1 N2. cbn [fst snd] in Ha.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar2 Hb) as (_ & H4 & Hc & _).
  pose proof (req_size_pos nn ltac:(lia)) as [_ Hr].
  pose proof ek_ceil. pose proof asan_consts as (C1 & _).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  destruct HCK as (_ & K2 & _).
  pose proof (rk_blk_apart ly2 S2 W2 mB mdB (p, nn) _ ek_ar2 Hb ek_kb2 Hne) as Dk. cbn [fst snd] in Dk.
  replace a with (p + (a - p)) by lia.
  rewrite (K2 p nn (a - p) Hb ltac:(lia) ltac:(cbv beta; lia)).
  apply HK2; lia.
Qed.

Lemma ek_K24_blk : forall b a, In b (ablocks B ly2 S2) -> b <> ek_kb -> fst b <= a < fst b + snd b -> ~ ek_C1 a -> ~ ek_C2 a ->
  abyte_kept W2 mB W3 mD a.
Proof.
  intros b a Hb Hne Ha N1 N2. split; [exact (ek_V24_blk b a Hb Hne Ha N1 N2)|].
  intros _. destruct b as [p nn]. exact (ek_wr3 p nn a (ek_to3 _ Hb Hne) Ha).
Qed.

Lemma ek_V12_blk : forall b a, In b (ablocks B ly1 S1) -> ~ In b (aout_blks cap2 out2) -> fst b <= a < fst b + snd b ->
  aview SEGS (w_H W2) mB a = aview SEGS (w_H W1) mA a.
Proof.
  intros [p nn] a Hb Ho Ha. cbn [fst snd] in Ha.
  destruct (ek_to2 _ Hb Ho) as [Hb2 _].
  pose proof (req_size_pos nn ltac:(lia)) as [_ Hr].
  replace a with (p + (a - p)) by lia.
  eapply rkk_jx_blk; [exact rkk_gxSL | exact HJG | exact Hb | exact Hb2 | lia |].
  intros (r0 & Hr0 & Hx). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([q m] & <- & Hq). cbn [fst snd] in Hx.
  assert (Hne : (p, nn) <> (q, m)) by (intros E; rewrite E in Ho; exact (Ho Hq)).
  pose proof (rk_blk_apart ly1 S1 W1 mA mdA (p, nn) (q, m) ek_ar1 Hb (ek_out1 _ Hq) Hne) as D. cbn [fst snd] in D.
  lia.
Qed.

Lemma ek_K14_blk : forall b a, In b (ablocks B ly1 S1) -> ~ In b (aout_blks cap2 out2) -> b <> ek_kb ->
  fst b <= a < fst b + snd b -> ~ ek_C1 a -> ~ ek_C2 a -> abyte_kept W1 mA W3 mD a.
Proof.
  intros b a Hb Ho Hne Ha N1 N2. destruct (ek_to2 b Hb Ho) as [Hb2 _].
  split; [rewrite (ek_V24_blk b a Hb2 Hne Ha N1 N2); exact (ek_V12_blk b a Hb Ho Ha)|].
  intros _. destruct b as [p nn]. exact (ek_wr3 p nn a (ek_to3 _ Hb2 Hne) Ha).
Qed.

Lemma ek_V14_hi : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) mD a = aview SEGS (w_H W1) mA a.
Proof.
  intros a Ha. pose proof ek_ceil. pose proof (rkk_bv cx) as Hb. assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  assert (HD : DRAIN_STK_x = 16976) by reflexivity. pose proof asan_consts as (C1 & _).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low a (or_introl Hc)) as (Hl & _); lia).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low a (or_intror Hc)) as (Hl & _); lia).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  destruct HCK as (K1 & _). rewrite (K1 a ltac:(lia) ltac:(lia)).
  rewrite (HK2 a ltac:(lia) ltac:(lia)).
  eapply rkk_jx_high; [exact rkk_gxSL | exact HJG | lia | lia].
Qed.

Lemma ek_V14_fr : forall a, (F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16) ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W1) mA a.
Proof.
  intros a Ha. destruct ek_frame as (Hfr1 & HFa1 & HF4 & HFc & Hoff & Hfr2 & HFa2 & _).
  pose proof ek_ceil. pose proof asan_consts as (C1 & _ & C3 & _ & C5).
  assert (HF8 : 0 <= F / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hlo : 4096 <= a < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF in Ha; lia).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low a (or_introl Hc)) as (_ & _ & Hn1 & Hn2); tauto).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low a (or_intror Hc)) as (_ & _ & Hn1 & Hn2); tauto).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  assert (NK : ~ (key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1))).
  { intros Hk. destruct (ek_blk_loc _ _ a (proj1 ek_kb1) Hk) as (_ & _ & Hn1 & Hn2). tauto. }
  destruct HCK as (_ & _ & _ & K4 & _).
  rewrite (K4 1 fpos a Hfr2 ltac:(unfold frame_rng, in_zr; cbn [fst snd]; rewrite HFa2; change (fs_frame_bytes 1) with 128;
    change (128 / 8) with 16; tauto) NK).
  rewrite (HK2 a ltac:(lia) ltac:(lia)).
  eapply rkk_jx_frame; [exact rkk_gxSL | exact HJG | exact Hfr1 | | | lia | ].
  - unfold frame_rng, in_zr; cbn [fst snd]; rewrite HFa1; change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; tauto.
  - intros (r0 & Hr0 & Hx). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([q m] & <- & Hq). cbn [fst snd] in Hx.
    destruct (ek_blk_loc q m a (ek_out1 _ Hq) Hx) as (_ & _ & Hn1 & Hn2). tauto.
  - intros Hi. pose proof (pa_img_range a Hi). unfold off_img in Hoff. unfold shadow_addr, SHADOW_OFF in Ha. lia.
Qed.

(* ---- the memory facts at (ly3, S3, W3, mD) ---- *)
Lemma ek_gsK : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 mA W3 mD a.
Proof.
  intros a Ha. destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps).
  exact (ek_K14_img a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
Qed.

Lemma ek_asrc : forall HA h, asrc_at B ly1 S1 W1 mA HA h ->
  (forall a, HA <= a < HA + ASRC -> rg_s RG <= a < rg_s RG + 4 * ASRC) ->
  (forall b, In b (asrc_blks h) -> In b ek_src) -> asrc_at B ly3 S3 W3 mD HA h.
Proof.
  intros HA h Hs HS HX.
  assert (HXP : forall b, In b (asrc_blks h) -> In b ek_P2) by (intros b Hb; right; apply in_or_app; right; exact (HX b Hb)).
  apply (asrc_at_kept B ly1 S1 W1 mA ly3 S3 W3 mD HA h Hs).
  - intros r0 Hr a Ha. destruct (rkk_asrc_loc _ _ _ _ HA h Hs r0 Hr a Ha) as [Hx | (b & Hb & Hx)].
    + exact (ek_gsK a (HS a Hx)).
    + destruct (ek_inP2 b (HXP b Hb)) as (Hb1 & Ho & Hne).
      destruct (ek_src_ne b (HX b Hb)) as [N1 N2].
      destruct ek_entry as (HT & _ & _ & _ & _ & _ & HH & _).
      destruct (ek_cells_apart ly1 S1 W1 mA mdA b a ek_ar1 HT HH Hb1 N1 N2 Hx) as [C1 C2].
      exact (ek_K14_blk b a Hb1 Ho Hne Hx C1 C2).
  - intros b Hb. destruct (ek_inP2 b (HXP b Hb)) as (Hb1 & Ho & Hne).
    exact (ek_to3 b (proj1 (ek_to2 b Hb1 Ho)) Hne).
Qed.

Lemma ek_done : forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
Proof.
  intros i' Hi' He. destruct ek_gin as (G1 & G2 & _ & _ & _ & G11 & _).
  pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
  apply ek_asrc; [exact (G11 i' Hi' He) | |].
  - pose proof (rkk_j4 cx i' HB ltac:(lia) He) as Hj. unfold gslot. intros a Ha. unfold ASRC in *. lia.
  - intros b Hb. apply in_or_app. left. unfold gdone_srcs. apply in_concat.
    exists (asrc_blks (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))). split; [|exact Hb].
    apply in_map_iff.
    exists (nth i' (combine (firstn i (gps cx)) qd) ((relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj),
      (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
    assert (Lf : length (firstn i (gps cx)) = i) by (rewrite length_firstn; unfold gps; rewrite length_combine; lia).
    split.
    + rewrite combine_nth by lia. cbv beta. cbn [fst snd].
      rewrite nth_firstn, (proj2 (Nat.ltb_lt i' i) Hi'). cbv beta iota.
      unfold gps. rewrite combine_nth by (symmetry; exact Hlen). cbn [fst].
      change (nth i' (gxes cx) relay_remove_b_c.no_entry) with (gnth cx i'). rewrite He. reflexivity.
    + apply nth_In. rewrite length_combine. lia.
Qed.

Lemma ek_open_src : ek_open = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1.
Proof.
  intros Hop. destruct ek_gin as (G1 & _ & _ & _ & _ & _ & G12 & _).
  apply ek_asrc; [exact (G12 Hop) | |].
  - pose proof (rkk_j4 cx i HB G1 (proj1 (Z.eqb_eq _ _) Hop)) as Hj. unfold gslot. intros a Ha. unfold ASRC in *. lia.
  - intros b Hb. apply in_or_app. right. apply in_or_app. left. rewrite Hop. exact Hb.
Qed.

Lemma ek_drsrc : Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)).
Proof.
  destruct ek_gin as (_ & _ & _ & _ & _ & _ & _ & G13 & _).
  rewrite Forall_forall in G13 |- *. intros p Hp He.
  destruct (G13 p Hp He) as (Hj & Hs & Ho & Hrest).
  split; [exact Hj|]. split; [|split; [|exact Hrest]].
  - apply ek_asrc; [exact Hs | |].
    + intros a Ha. unfold ASRC in *. lia.
    + intros b Hb. apply in_or_app. right. apply in_or_app. right. unfold rig_srcs. apply in_concat.
      exists (if re_eof (fst p) =? 0 then asrc_blks (fst (snd p)) else []). split.
      * apply (in_map (fun p => if re_eof (fst p) =? 0 then asrc_blks (fst (snd p)) else [])). exact Hp.
      * rewrite He. exact Hb.
  - intros i0 Hi0 Hne. destruct (Ho i0 Hi0 Hne) as (f0 & o & Hf & Hof & Hx). exists f0, o.
    split; [|split; [|exact Hx]].
    + apply (akept_vm W1 mA); [intros x Hx'; apply ek_gsK; change (Z.of_nat 4) with 4 in Hx'; unfold ASRC in *; lia | exact Hf].
    + apply (akept_vm W1 mA); [intros x Hx'; apply ek_gsK; change (Z.of_nat 4) with 4 in Hx'; unfold ASRC in *; lia | exact Hof].
Qed.

Lemma ek_gs_entry : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
  (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
  abyte_kept (gxW cx) (gxmem cx) W3 mD a.
Proof.
  intros a Ha Hj. destruct ek_gin as (_ & _ & _ & _ & _ & _ & _ & _ & G14 & _).
  exact (rkk_kept_trans _ _ _ _ _ _ a (G14 a Ha Hj) (ek_gsK a Ha)).
Qed.

Lemma ek_fp_blk : forall e' r0 a, In e' ek_es2 -> In r0 (aentry_fp e') -> fst r0 <= a < snd r0 ->
  exists b, In b (aentry_blks e') /\ fst b <= a < fst b + snd b.
Proof.
  intros e' r0 a He Hr Ha. destruct ek_gin as (_ & _ & _ & G9 & _).
  destruct G9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _). rewrite Forall_forall in H10.
  apply in_app_or in He. destruct He as [He | [<- | He]].
  - exact (rkr_fp_blk _ _ _ _ e' (H10 e' ltac:(apply in_or_app; left; exact He)) r0 Hr a Ha).
  - apply (rkk_fp_blk_ks ly1 S1 W1 mA e1 ks ek_ks2 (H10 (entry_keys e1 ks) ltac:(apply in_or_app; right; left; reflexivity))
      ltac:(rewrite relay_instance_gone_b_lem.rigl_len_swap; lia) r0 Hr a Ha).
  - exact (rkr_fp_blk _ _ _ _ e' (H10 e' ltac:(apply in_or_app; right; right; exact He)) r0 Hr a Ha).
Qed.

Lemma ek_relay : arelay_at B RG ly3 S3 W3 mD (gxG0 cx) ek_es2.
Proof.
  destruct ek_gin as (G1 & G2 & G6 & G9 & _ & _ & _ & _ & _ & G15 & _).
  pose proof HB as HB'. destruct HB' as (_ & _ & _ & HPL & _).
  pose proof (rkr_arelay_swap ly1 S1 W1 mA mdA ly3 S3 W3 mD (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n
    (ek_src ++ aout_blks cap2 out2 ++ gxrest cx) ek_ar1 HPL G15 G9 ek_nlt) as R.
  cbv zeta in R. rewrite length_map, G2 in R.
  apply R; [| |exact HNH | exact HSL].
  - intros b Hb. unfold arelay_blks in Hb.
    assert (HbP : In b ek_P2) by (destruct Hb as [<-|Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb]).
    destruct (ek_inP2 b HbP) as (Hb1 & Ho & Hne). exact (ek_to3 b (proj1 (ek_to2 b Hb1 Ho)) Hne).
  - intros r0 Hr a Ha N1 N2. unfold arelay_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|Hr]]]]; cbn [fst snd] in Ha.
    + destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
    + destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
    + destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
    + destruct (ek_inP2 ek_T (or_introl eq_refl)) as (Hb1 & Ho & Hne). exact (ek_K14_blk ek_T a Hb1 Ho Hne Ha N1 N2).
    + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e' & <- & He').
      destruct (ek_fp_blk e' r0 a He' Hr Ha) as (b & Hb & Hab).
      assert (HbP : In b ek_P2)
        by (right; apply in_or_app; left; apply in_concat; exists (aentry_blks e'); split; [apply in_map; exact He' | exact Hb]).
      destruct (ek_inP2 b HbP) as (Hb1 & Ho & Hne). exact (ek_K14_blk b a Hb1 Ho Hne Hab N1 N2).
Qed.

(* the output, from gesture_end's post *)
Lemma ek_K24_err : forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W2 mB W3 mD a.
Proof.
  intros a Ha. destruct (HGRIG a (rkk_errno_G a Ha)) as [Hi _].
  pose proof (rkk_img a Hi) as Hl. pose proof ek_ceil. pose proof asan_consts as (C1 & _).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low a (or_introl Hc)) as (_ & Hn & _); exact (Hn Hi)).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low a (or_intror Hc)) as (_ & Hn & _); exact (Hn Hi)).
  assert (V : aview SEGS (w_H W3) mD a = aview SEGS (w_H W2) mB a).
  { rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
    replace a with (as_errno B + (a - as_errno B)) by lia. rewrite (HERR (a - as_errno B) ltac:(lia)).
    apply HK2; lia. }
  split; [exact V|]. intros _.
  pose proof HO2 as HO.
  destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H17 & _).
  pose proof (rkk_vm_some _ _ _ _ _ a H17 ltac:(change (Z.of_nat 4) with 4; lia)) as Hs.
  destruct (aview SEGS (w_H W2) mB a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
  unfold arm. apply (rkk_view_wr (w_H W3) mD a v ltac:(lia) V).
  intros Hrom. destruct (HROMO a Hrom) as [HnG _]. exact (HnG (rkk_errno_G a Ha)).
Qed.

Lemma ek_TH2 : In ek_T (ablocks B ly2 S2) /\ ~ In ek_T (aout_blks ek_cap2 out2') /\
  In ek_H (ablocks B ly2 S2) /\ ~ In ek_H (aout_blks ek_cap2 out2') /\ ~ In ek_kb (aout_blks ek_cap2 out2').
Proof.
  destruct (ek_inP2 ek_T (or_introl eq_refl)) as (T1 & TO & _).
  destruct (ek_inP2 ek_H ltac:(right; apply in_or_app; left; exact ek_H_in)) as (H1 & HO & _).
  destruct ek_kb1 as [K1 KO].
  destruct (ek_to2 _ T1 TO) as [T2 TO2]. destruct (ek_to2 _ H1 HO) as [H2 HO2']. destruct (ek_to2 _ K1 KO) as [_ KO2].
  split; [exact T2|]. split; [exact TO2|]. split; [exact H2|]. split; [exact HO2' | exact KO2].
Qed.

Lemma ek_out : aout_at B RG ly3 S3 W3 mD ek_c2 ek_O2 (gxmx cx) (Z.of_nat (length ek_O2)) ek_cap2 out2'.
Proof.
  pose proof HO2 as HO.
  assert (EN : Z.of_nat (length ek_O2) = ge_no c2 ek_no2 ek_xl).
  { destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EN & _).
    exact EN. }
  rewrite EN.
  destruct ek_TH2 as (T2 & TO2 & H2 & HO2' & KO2).
  apply (aout_at_kept B RG ly2 S2 W2 mB ly3 S3 W3 mD _ _ _ _ _ _ HO).
  - intros r0 Hr a Ha. unfold aout_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Ha;
      try (destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & _); exact (ek_K24_img a Hi Ho He)).
    + exact (ek_K24_err a Ha).
    + destruct (ek_cap2 =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
      assert (Hb : In (out2', ek_cap2) (aout_blks ek_cap2 out2')) by (unfold aout_blks; rewrite Ec; left; reflexivity).
      pose proof (ek_outB _ Hb) as Hb2.
      assert (NK : (out2', ek_cap2) <> ek_kb) by (intros E; rewrite E in Hb; exact (KO2 Hb)).
      assert (NT : (out2', ek_cap2) <> ek_T) by (intros E; rewrite E in Hb; exact (TO2 Hb)).
      assert (NH : (out2', ek_cap2) <> ek_H) by (intros E; rewrite E in Hb; exact (HO2' Hb)).
      destruct (ek_cells_apart ly2 S2 W2 mB mdB (out2', ek_cap2) a ek_ar2 T2 H2 Hb2 NT NH Ha) as [N1 N2].
      exact (ek_K24_blk (out2', ek_cap2) a Hb2 NK Ha N1 N2).
  - intros b Hb. apply (ek_to3 b (ek_outB b Hb)). intros E. rewrite E in Hb. exact (KO2 Hb).
Qed.

(* the frame, the lock, the slots, the views *)
Lemma ek_frame3 : g_frame cx fpos F FL ly3 W3 mD.
Proof.
  destruct ek_frame as (_ & _ & HF4 & HFc & _ & _ & _ & HFa3 & HFl3).
  pose proof HF1 as HF1'. destruct HF1' as (_ & _ & H120 & H16 & H24 & H80 & Hsv).
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  assert (VH : forall a n0 v, gsp1 cx <= a -> a + Z.of_nat n0 <= gsp0 cx ->
    val_mem SEGS (arm W1 mA) a n0 v -> val_mem SEGS (arm W3 mD) a n0 v)
    by (intros a n0 v Hl Hh Hv; apply (rkk_vm_v W1 W3 mA mD); [intros x Hx; apply ek_V14_hi; lia | exact Hv]).
  split; [exact HFa3|]. split; [exact HFl3|].
  split; [apply (rkk_vm_v W1 W3 mA mD); [intros x Hx; apply ek_V14_fr; change (Z.of_nat 8) with 8 in Hx; lia | exact H120]|].
  split; [apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact H16]|].
  split; [apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact H24]|].
  split; [apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact H80]|].
  intros j Hj. apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact (Hsv j Hj)].
Qed.

Lemma ek_lock3 : alock_at RG W3 mD true.
Proof.
  apply (alock_at_kept RG W1 mA W3 mD true HL1). intros r0 Hr a Ha. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
  destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
Qed.

Lemma ek_VH8 : forall a v, gsp1 cx <= a -> a + 8 <= gsp0 cx -> val_mem SEGS (arm W1 mA) a 8 v -> val_mem SEGS (arm W3 mD) a 8 v.
Proof.
  intros a v Hl Hh Hv. apply (rkk_vm_v W1 W3 mA mD); [|exact Hv].
  intros x Hx. apply ek_V14_hi. change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

Lemma ek_lslots3 : g_lslots RG cx F W3 mD.
Proof.
  pose proof HLS1 as HLS. destruct HLS as (H40 & H48 & H56 & H64 & H72). assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  split; [apply ek_VH8; [lia | lia | exact H40]|].
  split; [apply ek_VH8; [lia | lia | exact H48]|].
  split; [apply ek_VH8; [lia | lia | exact H56]|].
  split; [apply ek_VH8; [lia | lia | exact H64] | apply ek_VH8; [lia | lia | exact H72]].
Qed.

Lemma ek_rom3 : rom_view SEGS W3 mD.
Proof.
  pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrv & _).
  eapply (ajournal_gx_rom_view_x SEGS B PST ARx).
  all: first [exact LAWS | exact pa_segs_low | exact HJ3 | exact HROMO | exact PSTR | exact Hrv].
Qed.

Lemma ek_apres3 : apres_kept B (gxW cx) (gxmem cx) W3 mD.
Proof. intros a Hi Ho He Hp. exact (ek_P24_img a Hi Ho He (HAP12 a Hi Ho He (HAP1 a Hi Ho He Hp))). Qed.

Lemma ek_pre3 : garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]).
Proof.
  destruct ek_gin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G16 & _).
  apply (rkk_garr8_v W1 W3 mA mD); [|exact G16].
  intros x Hx. apply ek_V14_fr. left. pose proof (rkk_pre_len cx). rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma ek_sh3 : garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
  destruct ek_gin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G17).
  apply (rkk_garr8_v W1 W3 mA mD); [|exact G17].
  intros x Hx. apply ek_V14_fr. right. cbn [length] in Hx. lia.
Qed.

Lemma ek_all :
  arelay_at B RG ly3 S3 W3 mD (gxG0 cx) ek_es2 /\
  aout_at B RG ly3 S3 W3 mD ek_c2 ek_O2 (gxmx cx) (Z.of_nat (length ek_O2)) ek_cap2 out2' /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  (ek_open = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p))) (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 mD a) /\
  garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] /\
  rom_view SEGS W3 mD /\ apres_kept B (gxW cx) (gxmem cx) W3 mD /\
  g_frame cx fpos F FL ly3 W3 mD /\ alock_at RG W3 mD true /\ g_lslots RG cx F W3 mD /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 32) 8 ((ek_SA + 48) mod 8 + 3) /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 88) 8 (Z.of_nat i).
Proof.
  split; [exact ek_relay|]. split; [exact ek_out|]. split; [exact ek_done|]. split; [exact ek_open_src|].
  split; [exact ek_drsrc|]. split; [exact ek_gs_entry|]. split; [exact ek_pre3|]. split; [exact ek_sh3|].
  split; [exact ek_rom3|]. split; [exact ek_apres3|]. split; [exact ek_frame3|]. split; [exact ek_lock3|].
  split; [exact ek_lslots3|].
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  split; [apply ek_VH8; [lia | lia | exact H32] | apply ek_VH8; [lia | lia | exact H88]].
Qed.
End e.

(* ---- the END arm's memory facts: what KEY's end-and-move leaves at the loop head (rkb_gin_end's memory premises, and
   GLIVE's, g_lslots' and RGI's slots), from gesture_end's post, the stretch to free, free's post (afree_cf_rule) and
   the two stores ---- *)
Theorem rkk_end_mem : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 mA mdA kA ly2 S2 W2 mB mdB kB out2' mB' ly3 S3 W3 mC mdC l1 l2 slo shi mD mdD kD,
  let d0 : Z * list byte * list byte := (0, [], []) in
  let k := nth n ks d0 in
  let kt := key_text k in
  let xl := Z.of_nat (length kt) in
  let ks' := swap_remove d0 n ks in
  let SA := gSA cx i in
  let hp := re_hp e1 in
  let no2 := Z.of_nat (length O2) in
  let c2' := ge_ctl c2 xl in
  let O2' := ge_O c2 O2 kt in
  let cap2' := ge_cap c2 (gxmx cx) no2 cap2 xl in
  let kl := nth (length ks - 1) ks d0 in
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx)
    [(1, fpos)] ly1 S1 [] W1 mA mdA kA ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ->
  rom_view SEGS W1 mA -> apres_kept B (gxW cx) (gxmem cx) W1 mA ->
  g_frame cx fpos F FL ly1 W1 mA -> alock_at RG W1 mA true -> g_lslots RG cx F W1 mA ->
  val_mem SEGS (arm W1 mA) (gsp1 cx + 32) 8 ((SA + 48) mod 8 + 3) ->
  val_mem SEGS (arm W1 mA) (gsp1 cx + 88) 8 (Z.of_nat i) ->
  has_prefix (gpre cx) (bzs kt) = true ->
  (* gesture_end's post *)
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) 0 [] GE_STK (gsp1 cx) (ablocks_fp (aout_blks cap2 out2))
    ly1 S1 [] W1 mA mdA [] ly2 S2 [] W2 mB mdB kB ->
  apres_kept B W1 mA W2 mB ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks cap2 out2 ++ rest) /\
     Permutation (ablocks B ly2 S2) (aout_blks cap2' out2' ++ rest)) ->
  aout_at B RG ly2 S2 W2 mB c2' O2' (gxmx cx) (ge_no c2 no2 xl) cap2' out2' ->
  (* the stretch to the free call: only the stack window below gsp1 changes *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> aview SEGS (w_H W2) mB' a = aview SEGS (w_H W2) mB a) ->
  (forall a, apresent (w_H W2) mB a -> apresent (w_H W2) mB' a) ->
  (* free's post (afree_cf_rule's conjuncts) *)
  ARh ly3 S3 W3 mC mdC ->
  ablocks B ly2 S2 = l1 ++ (key_addr k, xl + 1) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 -> frames S3 = frames S2 ->
  acall_kept SEGS B ly2 S2 W2 mB' W3 mC slo shi (fun a => key_addr k <= a < key_addr k + req_size (xl + 1)) ->
  gsp1 cx - DRAIN_STK_x <= slo -> shi <= gsp1 cx ->
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W3) mC (as_errno B + j) = aview SEGS (w_H W2) mB' (as_errno B + j)) ->
  (forall a, in_img SEGS a -> ~ aowned B ly2 S2 a -> ~ aowned B ly3 S3 a -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (key_addr k <= a < key_addr k + req_size (xl + 1)) -> apresent (w_H W2) mB' a -> apresent (w_H W3) mC a) ->
  (* the stores: everything else outside the stack window kept, the two cells written *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ (SA + 48 <= a < SA + 52) ->
     ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) mD a = aview SEGS (w_H W3) mC a) ->
  (forall a, apresent (w_H W3) mC a -> apresent (w_H W3) mD a) ->
  val_mem SEGS (arm W3 mD) (SA + 48) 4 (Z.of_nat (length ks')) ->
  val_mem SEGS (arm W3 mD) (hp + 8 * Z.of_nat n) 8 (key_addr kl) ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx)
    [(1, fpos)] ly3 S3 [] W3 mD mdD kD ->
  arelay_at B RG ly3 S3 W3 mD (gxG0 cx) (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)) /\
  aout_at B RG ly3 S3 W3 mD c2' O2' (gxmx cx) (Z.of_nat (length O2')) cap2' out2' /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) ->
        ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 mD a) /\
  garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] /\
  rom_view SEGS W3 mD /\ apres_kept B (gxW cx) (gxmem cx) W3 mD /\
  g_frame cx fpos F FL ly3 W3 mD /\ alock_at RG W3 mD true /\ g_lslots RG cx F W3 mD /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 32) 8 ((SA + 48) mod 8 + 3) /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 88) 8 (Z.of_nat i).
Proof.
  intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 mA mdA kA ly2 S2 W2 mB mdB kB out2' mB' ly3 S3 W3 mC mdC l1 l2 slo shi mD mdD kD. cbv zeta.
  intros HB HJ1 HG _ HAP1 HF1 HL1 HLS1 H32 H88 _ HJG HAP12 HPG HO2 HK2 HP2 HAR3 HL2 HL3 _ HCK _ Hshi HERR HAPF HK3 HP3
    HNH HSL HJ3.
  exact (ek_all cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 mA mdA kA ly2 S2 W2 mB mB' mdB kB out2' ly3 S3 W3 mC mD mdC mdD kD l1 l2 slo shi
    HB HJ1 HG HAP1 HF1 HL1 HLS1 H32 H88 HJG HAP12 HPG HO2 HK2 HP2 HAR3 HL2 HL3 HCK Hshi HERR HAPF HK3 HP3 HNH HSL HJ3).
Qed.

Theorem rig_key_proof : rig_key_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
unfold rig_key_stmt. intros cx i n r W1 c1 HB HC HI KP KE KR.
destruct HI as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 &
  ks & Ed & f & c2 & O2 & cap2 & out2 & spent & -> & HRB & R19 & R20 & R21 & R23 & R22 & R24 & R25 & R27 & M32 & M88 &
  HLV & HLS & HGN).
pose proof HLV as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
assert (EHp1 : Hp1 = []) by (eapply rk_jhp0; exact HJ). subst Hp1.
pose proof HB as (HPRE0 & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof (rk_gxHp cx HB) as EHp0. rewrite EHp0 in HJ, HPRE0.
pose proof HJ as HJ0.
pose proof HGN as (Hi & Hqd & HREL & HDR & HSND & Hks & Hf & HGK & HRLY & HOUT & HSRC & HOPEN & HDRS & HGS & HPERM &
  HPRE & HPSH & HBUD).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof HJ as (HSTK & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SP1 : spZ regs1 = gsp0 cx - 224) by (rewrite Hsp1; reflexivity).
assert (SPR : alloc_ceiling + 12880 <= gsp0 cx - 4320 /\ gsp0 cx <= 2 ^ 47) by (unfold gsp0 in *; rewrite WS in Hslo; lia).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkr_entry_at ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n HAR1 HRLY Hn) as X.
cbv zeta in X. rewrite length_map, Hqd in X. fold (gSA cx i) in X.
destruct X as (HinT & HT16 & HT4096 & HTceil & HTend & Mhp & Mnh & AWT & Hhp0 & Hinh & Hkh & Ghp & AWH & Mslot & Hink &
  Gk & NZk & Lk & Hks26 & NDk).
set (k := nth n ks (0, [], [])) in *.
set (hp := re_hp e1) in *. set (key := key_addr k) in *. set (kt := key_text k) in *.
destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 Hink) as (Hk16 & Hk4096 & Hkceil & Hkapp & Hkpres & _ & _).
destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 HinT) as (_ & _ & _ & HTapp & HTpres & _ & _).
pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [Hrk1 Hrk2].
pose proof (req_size_pos (Z.of_nat (length kt) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (rk_ablocks_nodup _ _ _ _ _ HAR1) as HND1.
pose proof (Permutation_NoDup HPERM HND1) as HNDP.
assert (HinHP : In (hp, re_kh e1) (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))))).
{ apply in_concat. exists (aentry_blks (entry_keys e1 ks)). split.
  - apply in_map. apply in_or_app. right. left. reflexivity.
  - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
    fold hp. destruct (Z.eqb_spec hp 0); [contradiction | left; reflexivity]. }
assert (HTH : (gxG0 cx, ATABLE) <> (hp, re_kh e1)).
{ apply List.NoDup_cons_iff in HNDP. intros Heq.
  apply (proj1 HNDP). rewrite Heq. apply in_or_app. left. exact HinHP. }
pose proof (rk_blk_apart ly1 S1 W1 m1 md1 _ _ HAR1 HinT Hinh HTH) as HTHd. cbn [fst snd] in HTHd.
change (req_size ATABLE) with 896 in HTHd.
assert (HSA : gSA cx i = gxG0 cx + 56 * Z.of_nat i) by reflexivity.
assert (DSH : hp + 8 * Z.of_nat n + 8 <= gSA cx i + 40 \/ gSA cx i + 52 <= hp + 8 * Z.of_nat n)
  by (clear - HTHd HTend HSA Hkh Hrk2 Hn; unfold AENT, ATABLE in *; lia).
pose proof (rk_entry_st W1 ly1 S1 regs1 m1 md1 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
  (Z.of_nat (length ks)) key HAR1 Hsp1 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
  ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32)
  H18 R19 R21 R23 R22 R25 R27 HinT ltac:(clear - HSA; lia) HTend
  ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
  Hinh Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)
  DSH Mhp Mnh (Mslot n Hn)) as [HS SHOK].
clear DSH.
unfold cfg_at. change (w64 (BASE + A_rig_inner)) with (Z_to_bv 64 (BASE + A_rig_inner)).
remember (Eimg (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk0; subst E; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (HAE : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)))) E)
  by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
(* the frame (1, fpos) *)
pose proof HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (rk_alf _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (rk_fb _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in *.
assert (HF8 : 0 <= F / 8 /\ 8 * (F / 8) <= F).
{ split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
(* the three blocks, pairwise apart, and apart from F *)
destruct (rk_perm_entry _ _ _ (map fst qd) (entry_keys e1 ks) (skipn (S i) (gxes cx)) _ k HND1 HPERM
  ltac:(cbn [re_hp entry_keys]; exact Hhp0) ltac:(cbn [re_keys entry_keys]; apply nth_In; exact Hn)) as (NE1 & NE2 & NE3).
cbn [re_hp re_kh entry_keys] in NE1, NE2, NE3. fold hp key kt in NE1, NE2, NE3.
pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 HinT Hink NE2) as DTK. cbn [fst snd] in DTK.
pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 Hinh Hink NE3) as DHK. cbn [fst snd] in DHK.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin HinT) as DFT.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin Hinh) as DFH.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin Hink) as DFK.
change (fs_frame_bytes 1) with 128 in DFT, DFH, DFK. rewrite HFa in DFT, DFH, DFK.
change (req_size ATABLE) with 896 in DTK, DFT.
set (XG := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
  rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap2 out2).
assert (HPX : Permutation (ablocks B ly1 S1) (XG ++ gxrest cx)) by (unfold XG; rewrite <- app_comm_cons, <- !app_assoc; exact HPERM).
assert (HP0X : Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx))
  by (unfold rk_X0; rewrite <- app_comm_cons, <- !app_assoc; exact HPERM0).
paj_run_tok_x RUN HS HJ SHOK rk_Bspan.
{ apply (rk_awr_k E _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
  - rewrite (EE 23%nat 23%bv eq_refl), R23. apply unsigned_lit_small. unfold AENT, ATABLE in *. lia.
  - rewrite E33. apply unsigned_lit_small. lia.
  - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 m1 md1 XG _ (gxG0 cx) ATABLE a HAR1 HP0X HPX).
    + left. reflexivity.
    + change (req_size ATABLE) with 896. unfold AENT, ATABLE in *. lia.
  - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 m1 md1 XG _ hp (re_kh e1) a HAR1 HP0X HPX).
    + right. apply in_or_app. left. exact HinHP.
    + lia. }
(* ---- the call strncmp (key, F + 32, |prefix|) at 0x82e80 ---- *)
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2.
assert (BV23 : base_val E (Some 23%nat) = gSA cx i + 48)
  by (cbn [base_val]; rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
assert (BV25 : base_val E (Some 25%nat) = gSA cx i + 40)
  by (cbn [base_val]; rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
assert (BV33 : base_val E (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (M01 : forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
  ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms0) HFr0 a Ha).
  intros (r0 & Hin & Hr). cbn [ss_mem ss_k rk_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
  rewrite ?BV23, ?BV25, ?BV33 in Hr; lia. }
assert (P01 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; eapply apresent_grows; [exact HG0 | exact Hp]).
assert (HSPc : spZ (ms_regs ms0) = gsp0 cx + -224).
{ unfold spZ at 1. rewrite QSP, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). lia. }
pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
destruct (rkr_pre_nz cx) as (NZp & Lp16 & Lp27).
assert (OUTW : forall a, (key <= a < key + req_size (Z.of_nat (length kt) + 1) \/ F <= a < F + 128) ->
  ~ (gSA cx i + 48 <= a < gSA cx i + 52) /\ ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8)).
{ clear - DTK DHK DFT DFH HTHd HTend HSA Hkh Hrk2 Hn. intros a Ha. unfold AENT, ATABLE in *. split; lia. }
clear DTK DHK DFT DFH DFK HTHd.
assert (GkT : garr8 SEGS (arm W1 (ms_mem ms0)) key (bzs (kt ++ [Z_to_bv 8 0]))).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ Gk). intros b Hb.
  unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
  destruct (OUTW b ltac:(lia)) as [Ow1 Ow2]. apply M01; [lia | exact Ow1 | exact Ow2]. }
assert (GpT : garr8 SEGS (arm W1 (ms_mem ms0)) (F + 32) (gpre cx ++ [0])).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ HPRE). intros b Hb.
  rewrite length_app in Hb. cbn [length] in Hb.
  destruct (OUTW b ltac:(lia)) as [Ow1 Ow2]. apply M01; [lia | exact Ow1 | exact Ow2]. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 key) by (rewrite QA0, E34; reflexivity).
assert (QA1' : getr (ms_regs ms0) 11 = w64 (F + 32)) by (rewrite QA1, (EE 20%nat 20%bv eq_refl); exact R20).
assert (QA2' : getr (ms_regs ms0) 12 = w64 (Z.of_nat (length (gpre cx)))) by (rewrite QA2, (EE 24%nat 24%bv eq_refl); exact R24).
assert (LKT : length (bzs (kt ++ [Z_to_bv 8 0])) = (length kt + 1)%nat) by (unfold bzs; rewrite length_map, length_app; reflexivity).
assert (LPT : length (gpre cx ++ [0]) = (length (gpre cx) + 1)%nat) by (rewrite length_app; reflexivity).
(* the key's and the prefix's bytes are visible *)
assert (VK : forall a, key <= a < key + Z.of_nat (length kt) + 1 -> aview SEGS (w_H W1) (ms_mem ms0) a <> None).
{ intros a Ha. replace a with (key + (a - key)) by lia. apply (rk_view_garr8 (w_H W1) (ms_mem ms0) key _ (a - key) GkT).
  rewrite LKT. lia. }
assert (VP : forall a, F + 32 <= a < F + 32 + Z.of_nat (length (gpre cx)) + 1 -> aview SEGS (w_H W1) (ms_mem ms0) a <> None).
{ intros a Ha. replace a with (F + 32 + (a - (F + 32))) by lia. apply (rk_view_garr8 (w_H W1) (ms_mem ms0) (F + 32) _ (a - (F + 32)) GpT).
  rewrite LPT. lia. }
assert (PSHT : garr8 SEGS (arm W1 (ms_mem ms0)) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ HPSH). intros b Hb. cbn [length] in Hb.
  apply M01; [clear - Hb HF8 HFceil C1; unfold shadow_addr, SHADOW_OFF in *; lia | |].
  - clear - Hb HTapp HTend HSA HFceil HF8 C1 C3. unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT, ATABLE in *.
    change (req_size 896) with 896 in HTapp. lia.
  - clear - Hb Hhapp Hkh Hrk2 Hn HFceil HF8 C1 C3. unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RIG B RG) 0 [] (2 * ESTACK) (SIGMA WS_strncmp) (fun _ => False)
    (fun (regs' : bvmap 5 word) (_ : word -> option byte) =>
       getr regs' 10 = w64 0 <-> astrn_agree W1 (ms_mem ms0) key (F + 32) (Z.of_nat (length (gpre cx))))
    W1 _ _ RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) _ _ _ _ _ _ (-224) _ HGRIG eq_refl HJ).
  - exact HSPc.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl), Hgp1. exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl), Htp1. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE2 HSC.
    apply (ASTRNCMP _ _ _ _ _ _ _ key (F + 32) (Z.of_nat (length (gpre cx)))
      (Z.min (Z.of_nat (length kt)) (Z.of_nat (length (gpre cx)))) (Z.of_nat (length (gpre cx))) HPRE2 HSC QA0' QA1' QA2').
    + lia.
    + lia.
    + lia.
    + lia.
    + exact (rkr_first_key W1 (ms_mem ms0) key kt (Z.of_nat (length (gpre cx))) ltac:(lia) GkT NZk).
    + exact (rkr_first_pre W1 (ms_mem ms0) (F + 32) (gpre cx) GpT NZp).
    + clear - Hkceil Hrq2 C1. unfold alloc_ceiling in *. lia.
    + clear - HFceil C1 Lp27. unfold alloc_ceiling in *. lia.
    + intros a Ha. split; [apply VK; lia | rewrite HSPc; clear - Ha Hkceil Hrq2 SPR; unfold ESTACK; lia].
    + intros a Ha. split; [apply VP; lia | rewrite HSPc; clear - Ha HFceil Lp27 SPR; unfold ESTACK; lia].
    + split; [|split].
      * eapply (rk_amr ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2; lia].
      * eapply (rk_rab ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2; lia].
      * intros _. eapply (rk_shv ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1));
        [exact HAR2 | exact Hink | lia | clear - Hrq2; lia | clear - Lk Lp16; lia].
    + replace (Z.min (Z.of_nat (length (gpre cx))) (Z.of_nat (length (gpre cx)) + 1)) with (Z.of_nat (length (gpre cx))) by lia.
      split; [|split].
      * clear - HFapp C1 C4 C5 Lp27. unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
      * intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
        assert (Ex : x / 8 = F / 8 + 4 + (x - F - 32) / 8).
        { clear - HFal Hx. pose proof (Z.div_mod F 32 ltac:(lia)) as D0. rewrite HFal, Z.add_0_r in D0.
          set (t := F / 32) in *.
          assert (E0 : F / 8 = 4 * t) by (rewrite D0; replace (32 * t) with ((4 * t) * 8) by lia; apply Z.div_mul; lia).
          rewrite E0. replace x with ((x - F - 32) + (4 * t + 4) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
        assert (Hj : 0 <= (x - F - 32) / 8 < 6).
        { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
        pose proof (rk_garr8_aview (w_H W1) (ms_mem ms0) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]
          (Z.to_nat ((x - F - 32) / 8)) PSHT ltac:(cbn [length]; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. unfold shadow_addr in Hv. rewrite Ex. replace (SHADOW_OFF + (F / 8 + 4 + (x - F - 32) / 8)) with (SHADOW_OFF + F / 8 + 4 + (x - F - 32) / 8) by lia.
        rewrite Hv. f_equal. generalize (Z.to_nat ((x - F - 32) / 8)). intros j. destruct j as [|[|[|[|[|[|j]]]]]]; try reflexivity. destruct j; reflexivity.
      * intros _ sx Hsx. pose proof (rk_hull F (Z.of_nat (length (gpre cx))) sx HFal ltac:(lia) Hsx) as Hs'.
        apply aview_some_of_apresent. apply P01. replace sx with (shadow_addr F + (sx - shadow_addr F)) by lia.
        exact (proj1 (HFSpres (sx - shadow_addr F) ltac:(lia))).
    + intros a Hin.
      assert (Hii : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
      pose proof (Hsegs a Hii) as Ha. rewrite M01; [exact (HROM1 a Hin) | clear - Ha C5; unfold kLowMemEnd in *; lia | |].
      * intros Hx. apply (rk_blk_not_img _ _ _ _ _ _ _ a HAR1 HinT); [|exact Hii].
        change (req_size ATABLE) with 896. clear - Hx HTend HSA. unfold AENT, ATABLE in *. lia.
      * intros Hx. apply (rk_blk_not_img _ _ _ _ _ _ _ a HAR1 Hinh); [|exact Hii]. clear - Hx Hkh Hrk2 Hn. lia.
    + split.
      * eapply (rk_amr ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2 Lk; lia].
      * clear - HFapp C1 C4 C5. unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
cbv beta. intros W2 c2x _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HA0 & Hfr2 & Hpres2).
(* ---- back at 0x82e84: a0 = strncmp's result ---- *)
pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
destruct (rk_alb ly1 S1 W1 mem2 _ _ _ HAR3 HinT) as (_ & _ & _ & _ & HTpres3 & _ & _).
destruct (rk_alb ly1 S1 W1 mem2 _ _ _ HAR3 Hinh) as (_ & _ & _ & _ & Hhpres3 & _ & _).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV23, ?BV25, ?BV33;
   [ intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr2;
     [ clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold AENT, ATABLE, alloc_ceiling in *; lia
     | exact (fun H => H)
     | clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn SPR; unfold AENT, ATABLE, ESTACK in *; lia ]
   | intros a Ha _; apply (apresent_writable SEGS);
     first [ apply (HTpres3 a); clear - Ha HTend HSA; change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia
           | apply (Hhpres3 a); clear - Ha Hkh Hrk2 Hn; lia
           | lia ] ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall k0, (k0 < 36)%nat -> ew Ea k0 = ew E k0) by (intros k0 Hk0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hk0).
assert (HAEa : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)))) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOKa : sh_ok SEGS rk_Bx rk_SH Ea (mrestrict (w_H W1) mem2)).
{ apply (rk_shok Ea W1 ly1 S1 mem2 _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HAR3).
  - rewrite OLDa by lia. rewrite (EE 18%nat 18%bv eq_refl). exact H18.
  - rewrite OLDa by lia. rewrite (EE 23%nat 23%bv eq_refl). exact R23.
  - rewrite OLDa by lia. rewrite (EE 25%nat 25%bv eq_refl). exact R25.
  - rewrite OLDa by lia. exact E33.
  - exact HinT.
  - clear - HSA. lia.
  - exact HTend.
  - exact Hinh.
  - exact Hkh.
  - clear - Hn. lia. }
prreg HS (10%bv : bv 5) R10a.
assert (BVa : forall k0, (k0 < 36)%nat -> base_val Ea (Some k0) = base_val E (Some k0))
    by (intros k0 Hk0; cbn [base_val]; rewrite OLDa by exact Hk0; reflexivity).
  assert (NWIN : forall (Wx : world SEGS) E' ss' (mA mB : word -> option byte), (forall k0, (k0 < 36)%nat -> base_val E' (Some k0) = base_val E (Some k0)) ->
    frame_of E' (ss_mem ss') (mrestrict (w_H Wx) mA) (mrestrict (w_H Wx) mB) -> ss_mem ss' = rk_regions ->
    forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) -> ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a).
  { intros Wx E' ss' mA mB HBV HFrx Hm a Ha H1 H2. apply (aview_kept_out E' _ (w_H Wx) mA mB HFrx a Ha).
    rewrite Hm. intros (r0 & Hin & Hr). cbn [rk_regions In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    rewrite ?HBV in Hr by lia; rewrite ?BV23, ?BV25, ?BV33 in Hr; lia. }
  assert (GR : forall k0 (r0 : bv 5), (k0 < 36)%nat -> Z.of_nat k0 = bv_unsigned r0 -> ew Ea k0 = getr regs1 r0)
    by (intros k0 r0 Hk0 Hr0; rewrite OLDa by exact Hk0; apply EE; exact Hr0).
psrr_branch_tok RUN BR HS SHOKa rk_Bspan.
- (* ======== a0 <> 0: the key lacks the prefix (pass) ======== *)
  assert (Ha0ne : getr regs2 10 <> w64 0).
  { intros Hz. rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia.
    rewrite (U_atom Ea 40 0) in Hc; [discriminate Hc | rewrite <- R10a; exact Hz | lia]. }
  assert (HPF : has_prefix (gpre cx) (bzs kt) = false).
  { destruct (has_prefix (gpre cx) (bzs kt)) eqn:Hh; [exfalso|reflexivity].
    apply (proj2 (rkr_agree W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp)) in Hh.
    exact (Ha0ne (proj2 HA0 Hh)). }
  paj_run_tok_x RUN HS HJ2 SHOKa rk_Bspan.
  { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
      + left. reflexivity.
      + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
      + right. apply in_or_app. left. exact HinHP.
      + clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
    psrr_branch_tok RUN BR HS SHOKa rk_Bspan.
  + (* n + 1 < nheld: the next key *)
    paj_run_to_tok_x RUNTO HS HJ2 SHOKa rk_Bspan A_rig_inner.
    { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
      - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
        + left. reflexivity.
        + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
        + right. apply in_or_app. left. exact HinHP.
        + clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    assert (Hn1 : (S n < length ks)%nat).
    { rewrite (rk_branch_lt Ea (SOff 21 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_lt in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 21%nat 21%bv eq_refl), R21 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    destruct r as [|r']; [exfalso; lia|].
    destruct (rk_win_vals Ea _ ms2 W1 (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key HS eq_refl
      ltac:(rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
      ltac:(rewrite OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
      ltac:(rewrite OLDa by lia; exact E35) ltac:(rewrite OLDa by lia; exact E34)
      ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as [VNf VKf].
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { apply (rk_keep_join cx W1 m1 (ms_mem ms2) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact Mnh | exact VNf | exact (Mslot n Hn) | exact VKf].
      intros a Ha Hns H1 H2.
      rewrite (NWIN W1 Ea _ (ms_mem ms1) (ms_mem ms2) BVa HFr2 eq_refl a Ha H1 H2).
      rewrite (NWIN W1 Ea _ mem2 (ms_mem ms1) BVa HFr1 eq_refl a Ha H1 H2).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha H1 H2). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (20%bv : bv 5) T20. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
    prreg_raw HS (19%bv : bv 5) T19. prreg_raw HS (21%bv : bv 5) T21. prreg_raw HS (22%bv : bv 5) T22. prreg_raw HS (27%bv : bv 5) T27.
    pose proof (rkk_gin cx i n (S r') F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 (ms_mem ms2) HB HJ0 HFR HGN KEEPf PRESf) as HGN2.
    destruct (rkb_gin_pass cx i n r' F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms2) HGN2 HPF) as (f' & HGN3).
    apply (KP r' W1 _ eq_refl).
    exists (ms_regs ms2), ly1, S1, (ms_mem ms2). eexists. eexists.
    exists F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, ks, Ed, f', c2, O2, cap2, out2, spent.
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (GR 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp1|].
      split; [rewrite T3, (GR 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp1|].
      split; [rewrite T4, (GR 4%nat 4%bv ltac:(lia) eq_refl); exact Htp1|].
      split; [rewrite T8, (GR 8%nat 8%bv ltac:(lia) eq_refl); exact H8|].
      split; [rewrite T9, (GR 9%nat 9%bv ltac:(lia) eq_refl); exact H9|].
      rewrite T18, (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18. }
    split.
    { rewrite T19. cbn [sv_denot]. rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl), R21. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, rk_sll3_add8 by lia. f_equal. lia. }
    split; [rewrite T20, (GR 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
    split.
    { rewrite T21. cbn [sv_denot]. rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl), R21. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia. }
    split; [rewrite T23, (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23|].
    split.
    { rewrite T22. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 18 0)) with (rk_sh 23).
      apply rk_sh_den; [rewrite (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23 | rewrite (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split; [rewrite T24, (GR 24%nat 24%bv ltac:(lia) eq_refl); exact R24|].
    split; [rewrite T25, (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25|].
    split.
    { rewrite T27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 18 0)) with (rk_sh 25).
      apply rk_sh_den; [rewrite (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25 | rewrite (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M32].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M88].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
    split; [exact (rkk_live cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGN3.
  + (* n + 1 >= nheld: the entry's last key passed; the loop ends *)
    assert (Hn1 : (length ks <= S n)%nat).
    { rewrite (rk_branch_lt Ea (SOff 21 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_ge in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 21%nat 21%bv eq_refl), R21 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    assert (r = 0%nat) by lia. subst r.
    paj_run_to_tok_x RUNTO HS HJ2 SHOKa rk_Bspan A_rig_step.
    { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
      - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
        + left. reflexivity.
        + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
        + right. apply in_or_app. left. exact HinHP.
        + clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    destruct (rk_win_vals Ea _ ms2 W1 (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key HS eq_refl
      ltac:(rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
      ltac:(rewrite OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
      ltac:(rewrite OLDa by lia; exact E35) ltac:(rewrite OLDa by lia; exact E34)
      ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as [VNf VKf].
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { apply (rk_keep_join cx W1 m1 (ms_mem ms2) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact Mnh | exact VNf | exact (Mslot n Hn) | exact VKf].
      intros a Ha Hns H1 H2.
      rewrite (NWIN W1 Ea _ (ms_mem ms1) (ms_mem ms2) BVa HFr2 eq_refl a Ha H1 H2).
      rewrite (NWIN W1 Ea _ mem2 (ms_mem ms1) BVa HFr1 eq_refl a Ha H1 H2).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha H1 H2). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20.
    pose proof (rkk_gin cx i n 0 F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 (ms_mem ms2) HB HJ0 HFR HGN KEEPf PRESf) as HGN2.
    pose proof (rkb_gout_pass cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms2) HB HGN2 HPF) as HGO.
    apply (KR W1 _).
    exists (ms_regs ms2), ly1, S1, (ms_mem ms2). eexists. eexists.
    exists F, FL, (qd ++ [(entry_keys e1 ks, h1)]), c2, O2, cap2, out2, spent.
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (GR 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp1|].
      split; [rewrite T3, (GR 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp1|].
      split; [rewrite T4, (GR 4%nat 4%bv ltac:(lia) eq_refl); exact Htp1|].
      split; [rewrite T8, (GR 8%nat 8%bv ltac:(lia) eq_refl); exact H8|].
      split; [rewrite T9, (GR 9%nat 9%bv ltac:(lia) eq_refl); exact H9|].
      rewrite T18, (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18. }
    split; [rewrite T20, (GR 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M88].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
    split; [exact Hi|].
    split; [exact (rkk_live cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGO.
- (* ======== a0 = 0: the key has the prefix (end it) ======== *)
  assert (U0 : U Ea (SOff 40 0) = 0).
  { rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia. destruct (Z.eqb_spec (U Ea (SOff 40 0)) 0); [assumption | discriminate Hc]. }
  assert (Ha0z : getr regs2 10 = w64 0).
  { rewrite R10a. rewrite U_SOff, Z.add_0_r in U0. pose proof (bv_unsigned_in_range 64 (ew Ea 40)) as Hr64.
    change (bv_modulus 64) with (2 ^ 64) in Hr64. rewrite zcanon_id in U0 by (unfold M64; lia).
    apply bv_eq. rewrite U0. reflexivity. }
  assert (HPT : has_prefix (gpre cx) (bzs kt) = true)
    by exact (proj1 (rkr_agree W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp) (proj1 HA0 Ha0z)).
  paj_run_to_tok_x RUNTO HS HJ2 SHOKa rk_Bspan AF_fr_gesture_end.
  { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
      + left. reflexivity.
      + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
      + right. apply in_or_app. left. exact HinHP.
      + clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  (* ---- the call gesture_end (key) at 0x82e8c ---- *)
  destruct (rk_win_vals Ea _ ms1 W1 (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key HS eq_refl
    ltac:(rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
    ltac:(rewrite OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
    ltac:(rewrite OLDa by lia; exact E35) ltac:(rewrite OLDa by lia; exact E34)
    ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as [VN1 VK1].
  assert (KEEPA : rkk_KEEP cx W1 m1 (ms_mem ms1)).
  { apply (rk_keep_join cx W1 m1 (ms_mem ms1) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact Mnh | exact VN1 | exact (Mslot n Hn) | exact VK1].
    intros a Ha Hns H1 H2.
    rewrite (NWIN W1 Ea _ mem2 (ms_mem ms1) BVa HFr1 eq_refl a Ha H1 H2).
    rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
    exact (M01 a Ha H1 H2). }
  assert (PRESA : rkk_PRES W1 m1 (ms_mem ms1)).
  { intros a Hp. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
  pose proof (rkk_gin cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 m1 md1 k1 (ms_mem ms1) HB HJ0 HFR HGN KEEPA PRESA) as HGNA.
  pose proof (rkk_live cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms1) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPA PRESA) as HLVA.
  pose proof (rkk_lslots cx F W1 m1 (ms_mem ms1) HLS KEEPA) as HLSA.
  pose proof HLVA as (fposA & HpA & HJA & HROMA & HPKA & HFRA & HLKA).
  assert (EHpA : HpA = []) by (eapply rk_jhp0; exact HJA). subst HpA. rewrite EHp0 in HJA.
  pose proof (rk_fpos_eq cx fposA fpos _ _ _ _ _ _ _ _ _ HJA HJ2) as Efp. subst fposA.
  assert (M32A : val_mem SEGS (arm W1 (ms_mem ms1)) (gsp1 cx + 32) 8 ((gSA cx i + 48) mod 8 + 3)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms1) _ 8 _); [|exact M32].
    intros kk Hkk. apply KEEPA; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
  assert (M88A : val_mem SEGS (arm W1 (ms_mem ms1)) (gsp1 cx + 88) 8 (Z.of_nat i)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms1) _ 8 _); [|exact M88].
    intros kk Hkk. apply KEEPA; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
  assert (GkA : garr8 SEGS (arm W1 (ms_mem ms1)) key (bzs (kt ++ [Z_to_bv 8 0]))).
  { apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms1) _ _ Gk). intros b Hb. rewrite LKT in Hb.
    apply KEEPA; [clear - Hb Hk4096 Hkceil Hrq2 C1; unfold alloc_ceiling in *; lia | clear - Hb Hkceil Hrq2 SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, alloc_ceiling in *; lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
  prreg HS (8%bv : bv 5) U8. prreg HS (10%bv : bv 5) U10.
  pose proof HGNA as (_ & _ & _ & _ & _ & _ & _ & _ & HRLYA & HOUTA & _ & _ & _ & _ & HPERMA & _ & _ & _).
  destruct (rk_room cx i n r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1) HB HGNA HPT)
    as (RM1 & RM2 & RM3 & Hxl0 & Hcap2 & RMg & CNg & CNle).
  assert (ROOM : ge_room MMAX (blocks_bytes S1) c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))).
  { unfold ge_room, ge_tr. rewrite (rkb_live_pos c2 (Z.of_nat (length kt)) Hxl0). exact (conj RM1 RM2). }
  assert (MOKG : mo_ok MT S1 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)))).
  { apply (mo_ok_le MT MLAW S1 _ _ RM3). apply rk_le_add. exact (mo_free_nonneg MT MLAW). }
  assert (HinKP : In (key, Z.of_nat (length kt) + 1) (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))))).
  { apply in_concat. exists (aentry_blks (entry_keys e1 ks)). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. right. cbn [re_keys entry_keys].
      apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). apply nth_In. exact Hn. }
  assert (HAR4 : ARh ly1 S1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md2) mat1 md2))
    by exact (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2).
  assert (Hko : key <> out2).
  { destruct (rk_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTA) as [(Hc0 & Ho0 & _) | (Hcp & _ & Hino)].
    - rewrite Ho0. lia.
    - assert (Hne : (key, Z.of_nat (length kt) + 1) <> (out2, cap2)).
      { apply (rk_nodup_far _ _ _ _ _ _ _ _ _ HNDP HinKP). unfold aout_blks. rewrite (proj2 (Z.eqb_neq cap2 0) ltac:(lia)). left. reflexivity. }
      pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 Hink Hino Hne) as Hd. cbn [fst snd] in Hd.
      pose proof (req_size_pos cap2 ltac:(lia)) as [Hc1 Hc2]. intros Heq. lia. }
  pose proof HFRA as (_ & _ & _ & _ & _ & _ & HSVA).
  destruct (rk_saved_ra_s0 cx W1 (ms_mem ms1) HSVA) as [VRA VS0].
  destruct (rk_chain2 cx _ ly1 S1 W1 (ms_mem ms1) _ _ HB HJ2 VRA VS0) as (ch1 & Hch1).
  eapply SRr_bind.
  { eapply (rk_ge_call W1 (ms_regs ms1) (ms_mem ms1) _ RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx) (gxmem cx)
      (gxmd cx) [(1, fpos)] ly1 S1 _ (Z_to_bv 64 (BASE + 2980)) c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 kt key
      (Z.of_nat (length kt) + 1) (-224) ch1 HJ2).
    - unfold spZ at 1. rewrite U2, (GR 2%nat 2%bv ltac:(lia) eq_refl). fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK. lia.
    - rewrite U3, (GR 3%nat 3%bv ltac:(lia) eq_refl), Hgp1. exact Hgp.
    - rewrite U4, (GR 4%nat 4%bv ltac:(lia) eq_refl), Htp1. exact Htp.
    - exact U1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - replace (s0Z (ms_regs ms1)) with (gsp0 cx); [exact Hch1|].
      unfold s0Z. rewrite U8, (GR 8%nat 8%bv ltac:(lia) eq_refl), H8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - rewrite U10, OLDa, E34 by lia. reflexivity.
    - exact HOUTA.
    - exact GkA.
    - exact NZk.
    - exact Lk.
    - exact Hink.
    - exact Hko.
    - lia.
    - exact (rk_end5 W1 (ms_mem ms1) HROMA).
    - exact HROMA.
    - exact ROOM.
    - exact MOKG.
    - exact RMg.
    - exact CNg.
    - intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p0 & n0 & Hin0 & Hpa0).
      apply (rk_fp_blk cx ly1 S1 W1 (ms_mem ms1) _ XG p0 n0 a HAR4 HP0X HPX); [| exact Hpa0].
      unfold XG. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin0. }
  cbv beta. intros W2 c2x _ (ly2 & S2 & regs2' & mem2' & md2' & kk1 & out2' & kg & -> & HJ3 & HJc3 & HJs3 & HP3 & HAK3 & HM3 &
    HRMge & (restG & HPa3 & HPb3) & HO3).
  (* ---- back at 0x82e90 ---- *)
  pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR5.
  assert (NTO : ~ In (gxG0 cx, ATABLE) (aout_blks cap2 out2)) by exact (rk_nodup_head_out _ _ _ _ _ _ _ HNDP).
  assert (NHO : ~ In (hp, re_kh e1) (aout_blks cap2 out2))
    by (intros Hin; exact (rk_nodup_far _ _ _ _ _ _ _ _ _ HNDP HinHP Hin eq_refl)).
  assert (NKO : ~ In (key, Z.of_nat (length kt) + 1) (aout_blks cap2 out2))
    by (intros Hin; exact (rk_nodup_far _ _ _ _ _ _ _ _ _ HNDP HinKP Hin eq_refl)).
  assert (NGT : ~ In (gxG0 cx, ATABLE) (gxrest cx)) by exact (rk_nodup_rest _ _ _ _ _ _ _ _ HNDP (or_introl eq_refl)).
  assert (NGH : ~ In (hp, re_kh e1) (gxrest cx))
    by exact (rk_nodup_rest _ _ _ _ _ _ _ _ HNDP (or_intror (in_or_app _ _ _ (or_introl HinHP)))).
  assert (NGK : ~ In (key, Z.of_nat (length kt) + 1) (gxrest cx))
    by exact (rk_nodup_rest _ _ _ _ _ _ _ _ HNDP (or_intror (in_or_app _ _ _ (or_introl HinKP)))).
  destruct (rk_ge_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 HAR4 HPa3 HPb3 HinT NTO) as (HinT2 & KT2).
  destruct (rk_ge_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 HAR4 HPa3 HPb3 Hinh NHO) as (Hinh2 & KH2).
  destruct (rk_ge_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 HAR4 HPa3 HPb3 Hink NKO) as (Hink2 & KK2).
  destruct (rk_alb ly2 S2 W2 mem2' _ _ _ HAR5 HinT2) as (_ & _ & _ & _ & HTpres5 & _ & _).
  destruct (rk_alb ly2 S2 W2 mem2' _ _ _ HAR5 Hinh2) as (_ & _ & _ & _ & Hhpres5 & _ & _).
  change (req_size ATABLE) with 896 in KT2, HTpres5.
  jafter_call_keep_pi HS 52%nat regs2' (mrestrict (w_H W2) mem2') HP3 [0; 1; 2]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BVa by lia; rewrite ?BV23, ?BV25, ?BV33).
    - intros a Ha. apply (mbyte_of_aview SEGS). replace a with (gxG0 cx + (a - gxG0 cx)) by lia.
      apply KT2. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha _. lia.
    - intros a Ha. apply (mbyte_of_aview SEGS). replace a with (gxG0 cx + (a - gxG0 cx)) by lia.
      apply KT2. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha _. apply (apresent_writable SEGS). replace a with (gxG0 cx + (a - gxG0 cx)) by lia.
      apply HTpres5. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (mbyte_of_aview SEGS). replace a with (hp + (a - hp)) by lia.
      apply KH2. clear - Ha Hkh Hrk2 Hn. lia.
    - intros a Ha _. apply (apresent_writable SEGS). replace a with (hp + (a - hp)) by lia.
      apply Hhpres5. clear - Ha Hkh Hrk2 Hn. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc Ea 52 (map (getr regs2') CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall k0, (k0 < 52)%nat -> ew Eb k0 = ew Ea k0) by (intros k0 Hk0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hk0).
  clear HEb.
  assert (GRb : forall k0 (r0 : bv 5), (k0 < 36)%nat -> Z.of_nat k0 = bv_unsigned r0 -> ew Eb k0 = getr regs1 r0)
    by (intros k0 r0 Hk0 Hr0; rewrite OLDb by lia; apply GR; [exact Hk0 | exact Hr0]).
  assert (SHOKb : sh_ok SEGS rk_Bx rk_SH Eb (mrestrict (w_H W2) mem2')).
  { apply (rk_shok Eb W2 ly2 S2 mem2' _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HAR5).
    - rewrite (GRb 18%nat 18%bv ltac:(lia) eq_refl). exact H18.
    - rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl). exact R23.
    - rewrite (GRb 25%nat 25%bv ltac:(lia) eq_refl). exact R25.
    - rewrite OLDb, OLDa by lia. exact E33.
    - exact HinT2.
    - clear - HSA. lia.
    - exact HTend.
    - exact Hinh2.
    - exact Hkh.
    - clear - Hn. lia. }
  paj_run_tok_x RUN HS HJ3 SHOKb rk_Bspan.
  { apply (rk_awr_k Eb _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl), R23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite OLDb, OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly2 S2 _ (gxG0 cx) ATABLE a HP0X HinT2 NGT).
      change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly2 S2 _ hp (re_kh e1) a HP0X Hinh2 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  (* ---- the call free (key) at 0x82eb4 ---- *)
  assert (BVb : forall k0, (k0 < 36)%nat -> base_val Eb (Some k0) = base_val E (Some k0))
    by (intros k0 Hk0; cbn [base_val]; rewrite OLDb, OLDa by lia; reflexivity).
  pmkst HS.
  prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3. prreg HS (4%bv : bv 5) V4.
  prreg HS (8%bv : bv 5) V8. prreg HS (10%bv : bv 5) V10.
  destruct (rk_win3 Eb _ ms2 W2 (gSA cx i) (hp + 8 * Z.of_nat n) hp (Z.of_nat (length ks)) key HS eq_refl
    ltac:(rewrite (GRb 25%nat 25%bv ltac:(lia) eq_refl), R25; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
    ltac:(rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl), R23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
    ltac:(rewrite OLDb, OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
    ltac:(rewrite OLDb, OLDa by lia; exact E32) ltac:(rewrite OLDb, OLDa by lia; exact E35) ltac:(rewrite OLDb, OLDa by lia; exact E34)
    ltac:(clear - Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia) ltac:(clear - Hks26; lia)
    ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as (VH2 & VN2 & VK2).
  assert (VN2' : val_mem SEGS (arm W2 mem2') (gSA cx i + 48) 4 (Z.of_nat (length ks))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) mem2' _ 4 _); [|exact VN1].
    intros kk Hkk. replace (gSA cx i + 48 + kk) with (gxG0 cx + (gSA cx i + 48 + kk - gxG0 cx)) by lia.
    apply KT2. clear - Hkk HTend HSA. unfold AENT, ATABLE in *. lia. }
  assert (VK2' : val_mem SEGS (arm W2 mem2') (hp + 8 * Z.of_nat n) 8 key).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) mem2' _ 8 _); [|exact VK1].
    intros kk Hkk. replace (hp + 8 * Z.of_nat n + kk) with (hp + (8 * Z.of_nat n + kk)) by lia.
    apply KH2. clear - Hkk Hkh Hrk2 Hn. lia. }
  assert (KEEPS : rkk_KEEP cx W2 mem2' (ms_mem ms2)).
  { apply (rk_keep_join cx W2 mem2' (ms_mem ms2) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact VN2' | exact VN2 | exact VK2' | exact VK2].
    intros a Ha Hns H1 H2. exact (NWIN W2 Eb _ mem2' (ms_mem ms2) BVb HFr2 eq_refl a Ha H1 H2). }
  assert (PRESS : forall a, apresent (w_H W2) mem2' a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Hp; eapply apresent_grows; [exact HG2 | exact Hp]).
  (* the saved ra and s0 words at the free call: kept by gesture_end (above its window) and the run *)
  assert (KHI : forall a, gsp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W1) (ms_mem ms1) a).
  { intros a Ha. rewrite (KEEPS a ltac:(lia) ltac:(lia)).
    apply (rk_gx_keep_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGRIG HJc3); [clear - Ha SPR C1; unfold gsp1, RIG_FRAME in *; lia|].
    clear - Ha. unfold gsp1, RIG_FRAME in *. lia. }
  assert (VRA2 : val_mem SEGS (arm W2 (ms_mem ms2)) (gsp0 cx - 8) 8 (bv_unsigned (getr (gxregs cx) 1))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) (ms_mem ms2) _ 8 _); [|exact VRA].
    intros kk Hkk. apply KHI. clear - Hkk SPR C1. unfold gsp1, RIG_FRAME in *. lia. }
  assert (VS02 : val_mem SEGS (arm W2 (ms_mem ms2)) (gsp0 cx - 16) 8 (bv_unsigned (getr (gxregs cx) 8))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) (ms_mem ms2) _ 8 _); [|exact VS0].
    intros kk Hkk. apply KHI. clear - Hkk SPR C1. unfold gsp1, RIG_FRAME in *. lia. }
  (* the free's caller context (GCTX): the entry's frame is below the layout top, so the chain at 0x82eb4 is the
     entry's chain under relay_instance_gone's frame record (gsp0, ra, s0) *)
  assert (TOP2 : gsp0 cx < ly_top ly2 - 16).
  { pose proof (rk_gx_ly_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as ET2. destruct HC as (HC1 & _).
    unfold gsp0. clear - HC1 ET2. lia. }
  pose proof (rk_chain2p cx _ ly2 S2 W2 (ms_mem ms2) _ _ HB HJ3 VRA2 VS02 TOP2) as Hch2.
  assert (SP2 : spZ (ms_regs ms2) = gsp0 cx + -224).
  { unfold spZ at 1. rewrite V2, (GRb 2%nat 2%bv ltac:(lia) eq_refl). fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia. }
  prreg HS (9%bv : bv 5) V9. prreg HS (18%bv : bv 5) V18. prreg HS (19%bv : bv 5) V19. prreg HS (20%bv : bv 5) V20.
  prreg HS (21%bv : bv 5) V21. prreg HS (23%bv : bv 5) V23. prreg HS (24%bv : bv 5) V24. prreg HS (25%bv : bv 5) V25.
  prreg_raw HS (22%bv : bv 5) V22. prreg_raw HS (27%bv : bv 5) V27.
  rewrite (pal_free B TL).
  eapply SRr_bind.
  { eapply (rk_free (G_RIG B RG) W2 (ms_regs ms2) (ms_mem ms2) RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx)
      (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 _ _ key (Z.of_nat (length kt) + 1) (-224) (Z_to_bv 64 (BASE + 3020))
      ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx) HJ3 Hink2).
    - rewrite V10, OLDb, OLDa, E34 by lia. reflexivity.
    - exact SP2.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ASTACK. lia.
    - rewrite V3, (GRb 3%nat 3%bv ltac:(lia) eq_refl), Hgp1. exact Hgp.
    - rewrite V4, (GRb 4%nat 4%bv ltac:(lia) eq_refl), Htp1. exact Htp.
    - exact V1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - apply (achain_chain_pre ly2 (aview SEGS (w_H W2) (ms_mem ms2)) (gsp0 cx + -224) (gsp0 cx) _ (ms_regs ms2) Hch2).
      + rewrite SP2. clear - SPR C1. lia.
      + unfold s0Z. rewrite V8, (GRb 8%nat 8%bv ltac:(lia) eq_refl), H8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + unfold raZ. rewrite V1, unsigned_lit_small by lia. lia.
    - destruct HC as (_ & HC2). replace (raZ (ms_regs ms2)) with (A_rig_entryP + 652); [exact HC2|].
      unfold raZ. rewrite V1, unsigned_lit_small by lia. unfold A_rig_entryP, A_rig_entry, AF_fr_relay_instance_gone. ring.
    - intros Hin0 i0 Hi0. apply (rk_fp_in cx ly1 S1 W1 m1 md1 XG key (Z.of_nat (length kt) + 1) i0 HAR1 HP0X HPX); [| exact Hin0 | exact Hi0].
      right. apply in_or_app. left. exact HinKP.
    - exact (mo_ok_step MT MLAW S1 S2 _ _ RM3 HM3).
    - exact HRMge.
    - apply CNle. intros P. exact (rkc_cnt_out_le P ly1 S1 ly2 S2 cap2 out2 _ out2' restG HPa3 HPb3). }
  cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ4 & HP4 & (l1 & l2 & EL2 & EL3) & HFS & KF & HMF & HRMf &
    HERR & HPRF).
  (* ---- back at 0x82eb8 after free ---- *)
  pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR6.
  (* the key's count change: gesture_end's send chain moves g_out's own count exactly (rkc_ge_netP), the free drops
     the key's block (rkc_cnt_free) *)
  assert (HCN3 : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length kt) + 1))).
  { intros P. exact (rkc_end_cnt P c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))
      ly1 S1 ly2 S2 ly3 S3 out2 out2' restG l1 l2 key Hxl0 Hcap2 HPa3 HPb3 EL2 EL3). }
  assert (KEEPB : forall b m0, In (b, m0) (ablocks B ly2 S2) -> (b, m0) <> (key, Z.of_nat (length kt) + 1) ->
    In (b, m0) (ablocks B ly3 S3)).
  { intros b m0 Hb Hne. rewrite EL3. rewrite EL2 in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]];
    [apply in_or_app; left; exact Hb | congruence | apply in_or_app; right; exact Hb]. }
  pose proof (KEEPB _ _ HinT2 NE2) as HinT3.
  pose proof (KEEPB _ _ Hinh2 NE3) as Hinh3.
  pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 HinT Hink NE2) as DTK'. cbn [fst snd] in DTK'. change (req_size ATABLE) with 896 in DTK'.
  pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 Hinh Hink NE3) as DHK'. cbn [fst snd] in DHK'.
  pose proof KF as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
  assert (VH3 : val_mem SEGS (arm W3 mem3) (gSA cx i + 40) 8 hp).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 8 _); [|exact VH2].
    intros kk Hkk. replace (gSA cx i + 40 + kk) with (gxG0 cx + (gSA cx i + 40 + kk - gxG0 cx)) by lia.
    apply (KF2 _ _ _ HinT2); change (req_size ATABLE) with 896; clear - Hkk HTend HSA DTK'; unfold AENT, ATABLE in *; lia. }
  assert (VN3 : val_mem SEGS (arm W3 mem3) (gSA cx i + 48) 4 (Z.of_nat (length ks))).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 4 _); [|exact VN2].
    intros kk Hkk. replace (gSA cx i + 48 + kk) with (gxG0 cx + (gSA cx i + 48 + kk - gxG0 cx)) by lia.
    apply (KF2 _ _ _ HinT2); change (req_size ATABLE) with 896; clear - Hkk HTend HSA DTK'; unfold AENT, ATABLE in *; lia. }
  assert (VK3 : val_mem SEGS (arm W3 mem3) (hp + 8 * Z.of_nat n) 8 key).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 8 _); [|exact VK2].
    intros kk Hkk. replace (hp + 8 * Z.of_nat n + kk) with (hp + (8 * Z.of_nat n + kk)) by lia.
    apply (KF2 _ _ _ Hinh2); clear - Hkk Hkh Hrk2 Hn DHK'; lia. }
  assert (P3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs3 r0 = getr (ms_regs ms2) r0).
  { intros r0 Hr0. pose proof (HP4 (bv_unsigned r0) Hr0) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. }
  assert (R3_2 : spZ regs3 = gsp1 cx) by (unfold spZ; rewrite (P3 2%bv ltac:(unfold acallee_saved; change (bv_unsigned (2%bv : bv 5)) with 2; lia)); fold (spZ (ms_regs ms2)); rewrite SP2; unfold gsp1, RIG_FRAME; lia).
  assert (R3_18 : getr regs3 18 = w64 SHADOW_OFF) by (rewrite (P3 18%bv ltac:(unfold acallee_saved; change (bv_unsigned (18%bv : bv 5)) with 18; lia)), V18, (GRb 18%nat 18%bv ltac:(lia) eq_refl); exact H18).
  assert (R3_19 : getr regs3 19 = w64 (8 * Z.of_nat n)) by (rewrite (P3 19%bv ltac:(unfold acallee_saved; change (bv_unsigned (19%bv : bv 5)) with 19; lia)), V19, (GRb 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (R3_21 : getr regs3 21 = w64 (Z.of_nat n)) by (rewrite (P3 21%bv ltac:(unfold acallee_saved; change (bv_unsigned (21%bv : bv 5)) with 21; lia)), V21, (GRb 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (R3_23 : getr regs3 23 = w64 (gSA cx i + 48)) by (rewrite (P3 23%bv ltac:(unfold acallee_saved; change (bv_unsigned (23%bv : bv 5)) with 23; lia)), V23, (GRb 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
  assert (R3_25 : getr regs3 25 = w64 (gSA cx i + 40)) by (rewrite (P3 25%bv ltac:(unfold acallee_saved; change (bv_unsigned (25%bv : bv 5)) with 25; lia)), V25, (GRb 25%nat 25%bv ltac:(lia) eq_refl); exact R25).
  assert (R3_22 : getr regs3 22 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8)).
  { rewrite (P3 22%bv ltac:(unfold acallee_saved; change (bv_unsigned (22%bv : bv 5)) with 22; lia)), V22. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 18 0)) with (rk_sh 23).
    apply rk_sh_den; [rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl); exact R23 | rewrite (GRb 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
    clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
  assert (R3_27 : getr regs3 27 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8)).
  { rewrite (P3 27%bv ltac:(unfold acallee_saved; change (bv_unsigned (27%bv : bv 5)) with 27; lia)), V27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 18 0)) with (rk_sh 25).
    apply rk_sh_den; [rewrite (GRb 25%nat 25%bv ltac:(lia) eq_refl); exact R25 | rewrite (GRb 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
    clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
  pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 HinT Hinh NE1) as DTH'. cbn [fst snd] in DTH'. change (req_size ATABLE) with 896 in DTH'.
  assert (DSH3 : hp + 8 * Z.of_nat n + 8 <= gSA cx i + 40 \/ gSA cx i + 52 <= hp + 8 * Z.of_nat n)
    by (clear - DTH' HTend HSA Hkh Hrk2 Hn; unfold AENT, ATABLE in *; lia).
  assert (R3_3 : getr regs3 3 = getr (gxregs cx) 3) by (rewrite (P3 3%bv ltac:(unfold acallee_saved; change (bv_unsigned (3%bv : bv 5)) with 3; lia)), V3, (GRb 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp1).
  assert (R3_4 : getr regs3 4 = getr (gxregs cx) 4) by (rewrite (P3 4%bv ltac:(unfold acallee_saved; change (bv_unsigned (4%bv : bv 5)) with 4; lia)), V4, (GRb 4%nat 4%bv ltac:(lia) eq_refl); exact Htp1).
  assert (R3_8 : getr regs3 8 = w64 (gsp0 cx)) by (rewrite (P3 8%bv ltac:(unfold acallee_saved; change (bv_unsigned (8%bv : bv 5)) with 8; lia)), V8, (GRb 8%nat 8%bv ltac:(lia) eq_refl); exact H8).
  assert (R3_9 : getr regs3 9 = w64 (gsp1 cx)) by (rewrite (P3 9%bv ltac:(unfold acallee_saved; change (bv_unsigned (9%bv : bv 5)) with 9; lia)), V9, (GRb 9%nat 9%bv ltac:(lia) eq_refl); exact H9).
  assert (R3_20 : getr regs3 20 = w64 (F + 32)) by (rewrite (P3 20%bv ltac:(unfold acallee_saved; change (bv_unsigned (20%bv : bv 5)) with 20; lia)), V20, (GRb 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
  assert (R3_24 : getr regs3 24 = w64 (Z.of_nat (length (gpre cx)))) by (rewrite (P3 24%bv ltac:(unfold acallee_saved; change (bv_unsigned (24%bv : bv 5)) with 24; lia)), V24, (GRb 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
  replace (gsp0 cx + -224) with (gsp1 cx) in HJs3 by (unfold gsp1, RIG_FRAME; lia).
  change (Z_to_bv 64 (BASE + 3020)) with (Z_to_bv 64 (BASE + (A_rig_inner + 104))).
  destruct r as [|r'].
  2:{ (* ======== n + 1 < nheld: the last key moves into slot n ======== *)
  assert (Hkl : (length ks - 1 < length ks)%nat) by lia.
  set (kl := nth (length ks - 1) ks (0, [], [])) in *.
  pose proof (rkr_entry_at ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) (length ks - 1) HAR1 HRLY Hkl) as X.
  cbv zeta in X. fold kl in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinkl & _).
  destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 Hinkl) as (_ & Hkl4096 & Hklceil & _ & _ & _ & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text kl)) + 1) ltac:(lia)) as [Hrl1 Hrl2].
  set (hpl := hp + 8 * Z.of_nat (length ks - 1)) in *.
  assert (VL1 : val_mem SEGS (arm W1 m1) hpl 8 (key_addr kl)) by exact (Mslot _ Hkl).
  assert (VLA : val_mem SEGS (arm W1 (ms_mem ms1)) hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms1) _ 8 _); [|exact VL1].
    intros kk Hkk. apply KEEPA.
    - clear - Hkk Hh4096 Hhceil Hkh Hrk1 Hrk2 Hkl C1. unfold hpl, alloc_ceiling in *. lia.
    - clear - Hkk Hhceil Hkh Hrk1 Hrk2 Hkl SPR C1. unfold hpl, gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, alloc_ceiling in *. lia. }
  assert (VL2' : val_mem SEGS (arm W2 mem2') hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) mem2' _ 8 _); [|exact VLA].
    intros kk Hkk. replace (hpl + kk) with (hp + (hpl - hp + kk)) by lia.
    apply KH2. clear - Hkk Hkh Hrk2 Hkl. unfold hpl in *. lia. }
  assert (VL2 : val_mem SEGS (arm W2 (ms_mem ms2)) hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2' (ms_mem ms2) _ 8 _); [|exact VL2'].
    intros kk Hkk. apply KEEPS.
    - clear - Hkk Hh4096 Hhceil Hkh Hrk1 Hrk2 Hkl C1. unfold hpl, alloc_ceiling in *. lia.
    - clear - Hkk Hhceil Hkh Hrk1 Hrk2 Hkl SPR C1. unfold hpl, gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, alloc_ceiling in *. lia. }
  assert (VL3 : val_mem SEGS (arm W3 mem3) hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 8 _); [|exact VL2].
    intros kk Hkk. replace (hpl + kk) with (hp + (hpl - hp + kk)) by lia.
    apply (KF2 _ _ _ Hinh2); clear - Hkk Hkh Hrk2 Hkl DHK'; unfold hpl in *; lia. }
  destruct (rk_st_gen (A_rig_inner + 104) [hpl; key_addr kl] W3 ly3 S3 regs3 mem3 md3 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1)
    (Z.of_nat n) (Z.of_nat (length ks)) key HAR6 R3_2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32)
    R3_18 R3_19 R3_21 R3_23 R3_22 R3_25 R3_27 HinT3 ltac:(clear - HSA; lia) HTend
    ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
    Hinh3 Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)
    DSH3 VH3 VN3 VK3) as [HS5 SHOK5].
  remember (Eimg (Ereg regs3 (map (Z_to_bv 64) ([hp; hp + 8 * Z.of_nat n; key; Z.of_nat (length ks)] ++ [hpl; key_addr kl])))) as E5 eqn:HE5.
  assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; apply Eimg_env).
  assert (EE5 : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E5 k0 = getr regs3 r0)
    by (intros k0 r0 Hk0; subst E5; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
  assert (E5_32 : ew E5 32 = Z_to_bv 64 hp) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (E5_33 : ew E5 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  assert (E5_34 : ew E5 34 = Z_to_bv 64 key) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
  assert (E5_35 : ew E5 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
  assert (E5_36 : ew E5 36 = Z_to_bv 64 hpl) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 4)).
  assert (E5_37 : ew E5 37 = Z_to_bv 64 (key_addr kl)) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 5)).
  clear HE5.
  assert (Hhpl : hp + 8 * Z.of_nat n + 8 <= hpl /\ hpl + 8 <= hp + re_kh e1) by (unfold hpl; clear - Hkh Hn Hks Hkl; lia).
  assert (AF36 : afact_ok E5 36 (PTRK 3)).
  { unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2]. rewrite E5_36, unsigned_lit_small
      by (clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia).
    split; [clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia|]. split; [|lia].
    change (2 ^ 3) with 8. unfold hpl.
    replace (hp + 8 * Z.of_nat (length ks - 1)) with ((2 * (hp / 16) + Z.of_nat (length ks - 1)) * 8)
      by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia). apply Z_mod_mult. }
  assert (AF37 : afact_ok E5 37 (PTRK 0)).
  { unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2]. rewrite E5_37, unsigned_lit_small
      by (clear - Hkl4096 Hklceil Hrl1 Hrl2 C1; unfold alloc_ceiling in *; lia).
    split; [clear - Hkl4096 Hklceil Hrl1 Hrl2 C1; unfold alloc_ceiling in *; lia|]. split; [|lia].
    rewrite Z.pow_0_r. apply Z.mod_1_r. }
  pose proof (st_ok_pi_add_fact E5 _ _ 36%nat (PTRK 3) HS5 AF36) as HSa.
  pose proof (st_ok_pi_add_fact E5 _ _ 37%nat (PTRK 0) HSa AF37) as HSb.
  assert (BV5_36 : base_val E5 (Some 36%nat) = hpl)
    by (cbn [base_val]; rewrite E5_36; apply unsigned_lit_small; clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia).
  assert (BV5_25 : base_val E5 (Some 25%nat) = gSA cx i + 40)
    by (cbn [base_val]; rewrite (EE5 25%nat 25%bv eq_refl), R3_25; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_23 : base_val E5 (Some 23%nat) = gSA cx i + 48)
    by (cbn [base_val]; rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_33 : base_val E5 (Some 33%nat) = hp + 8 * Z.of_nat n)
    by (cbn [base_val]; rewrite E5_33; apply unsigned_lit_small; clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia).
  assert (RG4 : region_ok SEGS E5 (mrestrict (w_H W3) mem3) rk_R4).
  { unfold region_ok, rk_R4. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV5_36. split; [clear - Hhpl Hh4096; lia|]. split; [clear - Hhpl Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E5 _ hpl 0 8 (SOff 37 0) (key_addr kl));
    [cbn [sv_denot]; rewrite E5_37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VL3]. }
  assert (DJ4 : all_disjoint E5 rk_R4 rk_regions).
  { apply all_disjoint_of_extents. unfold rk_regions, rk_R4, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV5_36, BV5_25, BV5_23, BV5_33.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Hhpl DTH' HTend HSA Hrk1 Hrk2. unfold AENT, ATABLE in *. repeat split; lia. }
  pose proof (st_ok_pi_add_region E5 _ _ rk_R4 HSb eq_refl RG4 DJ4) as HSc.
  assert (ALI : sv_denot E5 rk_EXPR = sv_denot E5 (SOff 36 0)).
  { rewrite (rk_expr_den E5 hp (Z.of_nat (length ks)) E5_32 E5_35)
      by (clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 Hks26 Hkl C1; unfold alloc_ceiling, hpl in *; lia).
    cbn [sv_denot]. rewrite E5_36, Z.add_0_r, Z_to_bv_bv_unsigned. unfold hpl. f_equal. lia. }
  pose proof (st_ok_pi_add_alias E5 _ _ rk_EXPR (SOff 36 0) HSc ALI) as HSd.
  assert (SHOK6 : sh_ok SEGS rk_Bx (rk_SH ++ [mkSHE 36 0 8]) E5 (mrestrict (w_H W3) mem3)).
  { unfold sh_ok in *. apply Forall_app. split; [exact SHOK5|]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W3) mem3 E5 rk_Bx 36 hpl 8 hpl 0 8).
    - apply (rk_rab ly3 S3 W3 mem3 md3 hp (re_kh e1)); [exact HAR6 | exact Hinh3 | clear - Hhpl; lia | clear - Hhpl Hrk2; lia].
    - unfold rk_Bx. apply U_atom; [rewrite (EE5 18%nat 18%bv eq_refl); exact R3_18 | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact E5_36 | clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia].
    - lia.
    - lia.
    - intros x Hx. replace (0 `min` 8) with 0 in Hx by reflexivity. replace (0 `max` 8) with 8 in Hx by reflexivity.
      unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hx Hhpl Hhapp Hrk1 Hrk2. lia. }
  clear HS HS5 HSa HSb HSc. rename HSd into HS.
  paj_run_tok_x RUN HS HJ4 SHOK6 rk_Bspan.
  { apply (rk_awr_k4 E5 _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite E5_33. apply unsigned_lit_small. clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
      change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into msf, mat into matf, HF into HFf, HFr into HFrf, HG into HGf.
  psrr_branch_tok RUN BR HS SHOK6 rk_Bspan.
  + (* n < nheld - 1: back to the loop head with key n replaced by the last *)
    paj_run_to_tok_x RUNTO HS HJ4 SHOK6 rk_Bspan A_rig_inner.
    { apply (rk_awr_win E5 _ _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)); [| | rk_win_tac | |].
      - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite E5_33. apply unsigned_lit_small. clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
        change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into msg, mat into matg, HF into HFg, HFr into HFrg, HG into HGg.
    (* the two cells after the stores *)
    pose proof (st_ok_pi_region_nth E5 _ _ 2 (YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 (-1)))]) HS eq_refl) as HRf2.
    pose proof (st_ok_pi_region_nth E5 _ _ 3 (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 37 0))]) HS eq_refl) as HRf3.
    cbn [ms_mem restrict] in HRf2, HRf3.
    assert (Lks' : Z.of_nat (length (swap_remove (0, [], []) n ks)) = Z.of_nat (length ks) - 1)
      by (rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
    assert (VNf : val_mem SEGS (arm W3 (ms_mem msg)) (gSA cx i + 48) 4 (Z.of_nat (length (swap_remove (0, [], []) n ks)))).
    { rewrite Lks'.
      pose proof (field_of_region E5 _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) HRf2
        ltac:(rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia); reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hks26 Hkl; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    assert (VKf : val_mem SEGS (arm W3 (ms_mem msg)) (hp + 8 * Z.of_nat n) 8 (key_addr kl)).
    { pose proof (field_of_region E5 _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 37 0) (key_addr kl) HRf3
        ltac:(rewrite E5_33; apply unsigned_lit_small; clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hkl4096 Hklceil Hrl1 Hrl2 C1; unfold alloc_ceiling in *; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    (* every other byte is kept by the two runs *)
    assert (KST : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) (ms_mem msg) a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha _ H1 H2.
      rewrite (aview_kept_out E5 _ (w_H W3) (ms_mem msf) (ms_mem msg) HFrg a Ha).
      - apply (aview_kept_out E5 _ (w_H W3) mem3 (ms_mem msf) HFrf a Ha).
        intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_36, ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia.
      - intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_36, ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia. }
    assert (PSTm : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msg) a).
    { intros a Hp. eapply apresent_grows; [exact HGg|]. eapply apresent_grows; [exact HGf | exact Hp]. }
    pose proof (rkk_end_mem cx i n (S r') F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms1) _ _ ly2 S2 W2 mem2' _ _ out2' (ms_mem ms2) ly3 S3 W3 mem3 _ l1 l2 _ _ (ms_mem msg) _ _
      HB HJ2 HGNA HROMA HPKA HFRA HLKA HLSA M32A M88A HPT HJs3 HAK3 (ex_intro _ restG (conj HPa3 HPb3)) HO3 KEEPS PRESS
      HAR6 EL2 EL3 HFS KF
      ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia)
      ltac:(unfold gsp1, RIG_FRAME; lia)
      HERR HPRF KST PSTm VNf VKf HJ4) as RKK.
    cbv zeta in RKK.
    destruct RKK as (RLY & ROUT & RSRC & RSRC1 & RDRS & RGS & RPRE & RPSH & RROM & RPK & RFR & RLK & RLS & RM32 & RM88).
    (* the meter and the live bytes *)
    assert (HMLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HMF).
    pose proof (rkb_ge_cap_le c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as Hcg1.
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { rewrite (rkb_bb_free ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL2 EL3).
      rewrite (rkb_bb_out ly1 S1 ly2 S2 cap2 out2 _ out2' restG HPa3 HPb3 ltac:(lia)).
      rewrite (rkb_ge_net c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl0). lia. }
    destruct (rkb_gin_end cx i n r' F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)
      ly3 S3 W3 (ms_mem msg) out2' HB HGNA HPT HMLE HBB HRMf HCN3 RLY ROUT RSRC RSRC1 RDRS RGS
      (rkb_perm_end cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent (S r') ly1 S1 W1 (ms_mem ms1)
        ly2 S2 ly3 S3 l1 l2 restG out2' _ HGNA HND1 HPa3 HPb3 EL2 EL3) RPRE RPSH) as (f' & HGNf).
    (* the registers *)
    pmkst HS.
    prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4. prreg HS (8%bv : bv 5) Z8.
    prreg HS (9%bv : bv 5) Z9. prreg HS (18%bv : bv 5) Z18. prreg HS (19%bv : bv 5) Z19. prreg HS (20%bv : bv 5) Z20.
    prreg HS (21%bv : bv 5) Z21. prreg HS (23%bv : bv 5) Z23. prreg HS (24%bv : bv 5) Z24. prreg HS (25%bv : bv 5) Z25.
    prreg_raw HS (22%bv : bv 5) Z22. prreg_raw HS (27%bv : bv 5) Z27.
    apply (KE r' W3 _ eq_refl).
    exists (ms_regs msg), ly3, S3, (ms_mem msg). eexists. eexists.
    exists F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, (swap_remove (0, [], []) n ks), (Ed ++ [k]), f',
      (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))),
      out2', (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite Z2, (EE5 2%nat 2%bv eq_refl); exact R3_2|].
      split; [rewrite Z3, (EE5 3%nat 3%bv eq_refl); exact R3_3|].
      split; [rewrite Z4, (EE5 4%nat 4%bv eq_refl); exact R3_4|].
      split; [rewrite Z8, (EE5 8%nat 8%bv eq_refl); exact R3_8|].
      split; [rewrite Z9, (EE5 9%nat 9%bv eq_refl); exact R3_9|].
      rewrite Z18, (EE5 18%nat 18%bv eq_refl); exact R3_18. }
    split; [rewrite Z19, (EE5 19%nat 19%bv eq_refl); exact R3_19|].
    split; [rewrite Z20, (EE5 20%nat 20%bv eq_refl); exact R3_20|].
    split; [rewrite Z21, (EE5 21%nat 21%bv eq_refl); exact R3_21|].
    split; [rewrite Z23, (EE5 23%nat 23%bv eq_refl); exact R3_23|].
    split.
    { rewrite Z22. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 18 0)) with (rk_sh 23).
      apply rk_sh_den; [rewrite (EE5 23%nat 23%bv eq_refl); exact R3_23 | rewrite (EE5 18%nat 18%bv eq_refl); exact R3_18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split; [rewrite Z24, (EE5 24%nat 24%bv eq_refl); exact R3_24|].
    split; [rewrite Z25, (EE5 25%nat 25%bv eq_refl); exact R3_25|].
    split.
    { rewrite Z27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 18 0)) with (rk_sh 25).
      apply rk_sh_den; [rewrite (EE5 25%nat 25%bv eq_refl); exact R3_25 | rewrite (EE5 18%nat 18%bv eq_refl); exact R3_18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split; [exact RM32|].
    split; [exact RM88|].
    split; [exists fpos, []; split; [rewrite EHp0; exact HJ4|]; split; [exact RROM|]; split; [exact RPK|]; split; [exact RFR | exact RLK]|].
    split; [exact RLS|].
    exact HGNf.
  + exfalso. rewrite (rk_branch_lt E5 (SOff 21 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hc0.
    * apply Z.ltb_ge in Hc0. lia.
    * cbn [sv_denot]. rewrite (EE5 21%nat 21%bv eq_refl), R3_21. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    * cbn [sv_denot]. rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia). reflexivity.
    * lia.
    * lia. }
  (* ======== n + 1 = nheld: the ended key was the last; held[nheld - 1] is held[n] ======== *)
  assert (Hnl : (length ks - 1)%nat = n) by lia.
  assert (Ekl : nth (length ks - 1) ks (0, [], []) = k) by (rewrite Hnl; reflexivity).
  destruct (rk_st_gen (A_rig_inner + 104) [] W3 ly3 S3 regs3 mem3 md3 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1)
    (Z.of_nat n) (Z.of_nat (length ks)) key HAR6 R3_2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32)
    R3_18 R3_19 R3_21 R3_23 R3_22 R3_25 R3_27 HinT3 ltac:(clear - HSA; lia) HTend
    ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
    Hinh3 Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)
    DSH3 VH3 VN3 VK3) as [HS5 SHOK5].
  remember (Eimg (Ereg regs3 (map (Z_to_bv 64) ([hp; hp + 8 * Z.of_nat n; key; Z.of_nat (length ks)] ++ [])))) as E5 eqn:HE5.
  assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; apply Eimg_env).
  assert (EE5 : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E5 k0 = getr regs3 r0)
    by (intros k0 r0 Hk0; subst E5; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
  assert (E5_32 : ew E5 32 = Z_to_bv 64 hp) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (E5_33 : ew E5 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  assert (E5_34 : ew E5 34 = Z_to_bv 64 key) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
  assert (E5_35 : ew E5 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
  clear HE5.
  assert (BV5_25 : base_val E5 (Some 25%nat) = gSA cx i + 40)
    by (cbn [base_val]; rewrite (EE5 25%nat 25%bv eq_refl), R3_25; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_23 : base_val E5 (Some 23%nat) = gSA cx i + 48)
    by (cbn [base_val]; rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_33 : base_val E5 (Some 33%nat) = hp + 8 * Z.of_nat n)
    by (cbn [base_val]; rewrite E5_33; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1; unfold alloc_ceiling in *; lia).
  assert (ALI : sv_denot E5 rk_EXPR = sv_denot E5 (SOff 33 0)).
  { rewrite (rk_expr_den E5 hp (Z.of_nat (length ks)) E5_32 E5_35)
      by (clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hks26 Hn C1; unfold alloc_ceiling in *; lia).
    cbn [sv_denot]. rewrite E5_33, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. lia. }
  pose proof (st_ok_pi_add_alias E5 _ _ rk_EXPR (SOff 33 0) HS5 ALI) as HSd.
  clear HS HS5. rename HSd into HS.
  paj_run_tok_x RUN HS HJ4 SHOK5 rk_Bspan.
  { apply (rk_awr_win E5 _ _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)); [| | rk_win_tac | |].
    - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite E5_33. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
      change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into msf, mat into matf, HF into HFf, HFr into HFrf, HG into HGf.
  psrr_branch_tok RUN BR HS SHOK5 rk_Bspan.
  + exfalso. rewrite (rk_branch_lt E5 (SOff 21 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hc0.
    * apply Z.ltb_lt in Hc0. lia.
    * cbn [sv_denot]. rewrite (EE5 21%nat 21%bv eq_refl), R3_21. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    * cbn [sv_denot]. rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia). reflexivity.
    * lia.
    * lia.
  + (* the entry's last key ended: to 0x82f44 *)
    paj_run_to_tok_x RUNTO HS HJ4 SHOK5 rk_Bspan A_rig_step.
    { apply (rk_awr_win E5 _ _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)); [| | rk_win_tac | |].
      - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite E5_33. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
        change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into msg, mat into matg, HF into HFg, HFr into HFrg, HG into HGg.
    pose proof (st_ok_pi_region_nth E5 _ _ 1 (YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 (-1)))]) HS eq_refl) as HRf2.
    pose proof (st_ok_pi_region_nth E5 _ _ 2 (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))]) HS eq_refl) as HRf3.
    cbn [ms_mem restrict] in HRf2, HRf3.
    assert (Lks' : Z.of_nat (length (swap_remove (0, [], []) n ks)) = Z.of_nat (length ks) - 1)
      by (rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
    assert (VNf : val_mem SEGS (arm W3 (ms_mem msg)) (gSA cx i + 48) 4 (Z.of_nat (length (swap_remove (0, [], []) n ks)))).
    { rewrite Lks'.
      pose proof (field_of_region E5 _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) HRf2
        ltac:(rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia); reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hks26 Hn; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    assert (VKf : val_mem SEGS (arm W3 (ms_mem msg)) (hp + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], [])))).
    { rewrite Ekl.
      pose proof (field_of_region E5 _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 34 0) key HRf3
        ltac:(rewrite E5_33; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hk4096 Hkceil Hrq1 Hrq2 C1; unfold alloc_ceiling in *; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    assert (KST : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) (ms_mem msg) a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha _ H1 H2.
      rewrite (aview_kept_out E5 _ (w_H W3) (ms_mem msf) (ms_mem msg) HFrg a Ha).
      - apply (aview_kept_out E5 _ (w_H W3) mem3 (ms_mem msf) HFrf a Ha).
        intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia.
      - intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia. }
    assert (PSTm : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msg) a).
    { intros a Hp. eapply apresent_grows; [exact HGg|]. eapply apresent_grows; [exact HGf | exact Hp]. }
    pose proof (rkk_end_mem cx i n 0 F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms1) _ _ ly2 S2 W2 mem2' _ _ out2' (ms_mem ms2) ly3 S3 W3 mem3 _ l1 l2 _ _ (ms_mem msg) _ _
      HB HJ2 HGNA HROMA HPKA HFRA HLKA HLSA M32A M88A HPT HJs3 HAK3 (ex_intro _ restG (conj HPa3 HPb3)) HO3 KEEPS PRESS
      HAR6 EL2 EL3 HFS KF
      ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia)
      ltac:(unfold gsp1, RIG_FRAME; lia)
      HERR HPRF KST PSTm VNf VKf HJ4) as RKK.
    cbv zeta in RKK.
    destruct RKK as (RLY & ROUT & RSRC & RSRC1 & RDRS & RGS & RPRE & RPSH & RROM & RPK & RFR & RLK & RLS & RM32 & RM88).
    assert (HMLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HMF).
    pose proof (rkb_ge_cap_le c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as Hcg1.
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { rewrite (rkb_bb_free ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL2 EL3).
      rewrite (rkb_bb_out ly1 S1 ly2 S2 cap2 out2 _ out2' restG HPa3 HPb3 ltac:(lia)).
      rewrite (rkb_ge_net c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl0). lia. }
    pose proof (rkb_gout_end cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)
      ly3 S3 W3 (ms_mem msg) out2' HB HGNA HPT HMLE HBB HRMf HCN3 RLY ROUT RSRC RSRC1 RDRS RGS
      (rkb_perm_end cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent 0 ly1 S1 W1 (ms_mem ms1)
        ly2 S2 ly3 S3 l1 l2 restG out2' _ HGNA HND1 HPa3 HPb3 EL2 EL3) RPRE RPSH) as HGOf.
    pmkst HS.
    prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4. prreg HS (8%bv : bv 5) Z8.
    prreg HS (9%bv : bv 5) Z9. prreg HS (18%bv : bv 5) Z18. prreg HS (20%bv : bv 5) Z20.
    apply (KR W3 _).
    exists (ms_regs msg), ly3, S3, (ms_mem msg). eexists. eexists.
    exists F, FL, (qd ++ [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]),
      (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))),
      out2', (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite Z2, (EE5 2%nat 2%bv eq_refl); exact R3_2|].
      split; [rewrite Z3, (EE5 3%nat 3%bv eq_refl); exact R3_3|].
      split; [rewrite Z4, (EE5 4%nat 4%bv eq_refl); exact R3_4|].
      split; [rewrite Z8, (EE5 8%nat 8%bv eq_refl); exact R3_8|].
      split; [rewrite Z9, (EE5 9%nat 9%bv eq_refl); exact R3_9|].
      rewrite Z18, (EE5 18%nat 18%bv eq_refl); exact R3_18. }
    split; [rewrite Z20, (EE5 20%nat 20%bv eq_refl); exact R3_20|].
    split; [exact RM88|].
    split; [exact Hi|].
    split; [exists fpos, []; split; [rewrite EHp0; exact HJ4|]; split; [exact RROM|]; split; [exact RPK|]; split; [exact RFR | exact RLK]|].
    split; [exact RLS|].
    exact HGOf.
Qed.

(* ---- KEYS: the inner loop, by induction on r (W_drain_outer.v's and cgif ACfj.v's pattern): each KEY step
   lowers r by one, and r = 0 leaves only the exit to RGE. ---- *)
Theorem rig_keys_proof : rig_keys_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
unfold rig_keys_stmt. intros KEY cx i n r. revert n.
induction r as [|r IH]; intros n W1 c1 HB HC HI HE.
- apply (KEY cx i n 0%nat W1 c1 HB HC HI); [intros r' W2 c2 Hr; discriminate Hr | intros r' W2 c2 Hr; discriminate Hr | exact HE].
- apply (KEY cx i n (S r) W1 c1 HB HC HI).
  + intros r' W2 c2 Hr H2. injection Hr as <-. exact (IH (S n) W2 c2 HB HC H2 HE).
  + intros r' W2 c2 Hr H2. injection Hr as <-. exact (IH n W2 c2 HB HC H2 HE).
  + exact HE.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this Section's walk at a world relation R, concluding the cx file's
   rig_key_stmt_xR / rig_keys_stmt_xR (W_relay_instance_gone_cx.v Section wR).  Each <name>_xR below is <name> with the
   journal ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the carriers GLIVE / RGI / RGE / gPOST and the
   statements -> their R twins, gesture_end's and free's rules -> GE_R / AFREE_R (the free's call-boundary premise
   RO from RO_ARx), strncmp by aj_gx_entry_at_xR (its strict rule lifted by WLE_R), and the walk on
   W_journal_x.v's G chain (RUNG / RUNTOG, W_kit_x.v's paj_run_tok_xR / paj_run_to_tok_xR, W_kit.v's paj_branch_xR as
   BRR, SRrG_bind / SRrG_mono); every other token is the strict text's.  The lemmas that read no journal and no step
   relation are shared.  The Section hypotheses are the cx file's Section wR, verbatim. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE_R : ge_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gesture_end).
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* W_rig_key.v:229 rig_lift_DR at R *)
Lemma rig_lift_DR_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rig_G_DR_RIG | eassumption]. Qed.
(* W_rig_key.v:233 rig_lift_SL at R *)
Lemma rig_lift_SL_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rig_G_SL_RIG | eassumption]. Qed.

(* ==== the generic relation at the empty head set ==== *)
(* HP0: every ARx state this walk meets has the head set [], so the walk states its facts at ARh (= ARx at []) and
   each journal from [] to [] (a callee's post state is brought to [] by rk_hp0 / rk_jhp0_xR as it arrives). The wrappers
   keep the AR walk's argument order: rk_alb is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN). *)
#[local] Notation ARh ly S W mem md := (ARx ly S (@nil Z) W mem md).
(* W_rig_key.v:245 rk_jhp0 at R *)
Lemma rk_jhp0_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> Hp' = [].
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (HP0 _ _ _ _ _ _ (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
Qed.
(* W_rig_key.v:251 rk_jAR at R *)
Lemma rk_jAR_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
ARh ly' S' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* W_rig_key.v:1855 rkk_jar at R *)
Lemma rkk_jar_xR : forall cx fpos ly1 S1 W1 m1 md1 k1,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  ARh ly1 S1 W1 m1 md1 /\ In (1, fpos) (frames S1).
Proof.
  intros cx fpos ly1 S1 W1 m1 md1 k1 HJ.
  destruct HJ as (_ & _ & (memS & HJ' & _) & _).
  destruct HJ' as (HAR & _ & _ & _ & _ & Hfrs & _).
  split; [exact HAR|]. rewrite Hfrs. apply in_or_app. left. left. reflexivity.
Qed.
(* W_rig_key.v:1866 rkk_gin at R *)
Theorem rkk_gin_xR : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 m2,
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  g_frame cx fpos F FL ly1 W1 m1 ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  rkk_KEEP cx W1 m1 m2 -> rkk_PRES W1 m1 m2 ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m2.
Proof.
  intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 md1 k1 m2
    HB HJ HF HG HK HP.
  destruct (rkk_jar_xR cx fpos ly1 S1 W1 m1 md1 k1 HJ) as [HAR Hfr].
  destruct HF as (HFa & _).
  destruct (rk_fb ly1 S1 W1 m1 md1 1 fpos HAR Hfr) as (HF4 & HFc & _).
  rewrite HFa in HF4, HFc. change (fs_frame_bytes 1) with 128 in HFc.
  pose proof asan_consts as (C1 & _).
  assert (KC : forall a, 0 <= a < alloc_ceiling -> abyte_kept W1 m1 W1 m2 a)
    by (intros a Ha; exact (rkk_kept_c cx W1 m1 m2 a HB HK HP Ha)).
  unfold GIN in HG |- *. cbv zeta in HG |- *.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
  do 8 (split; [assumption|]).
  split.
  { destruct (rkk_arelay cx ly1 S1 W1 m1 md1 _ _ HB HAR G9) as [L Bl].
    exact (arelay_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ G9 (rkk_akept cx W1 m1 m2 _ HB HK HP L) Bl). }
  split.
  { destruct (rkk_aout cx ly1 S1 W1 m1 md1 _ _ _ _ _ _ HB HAR G10) as [L Bl].
    exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ _ G10 (rkk_akept cx W1 m1 m2 _ HB HK HP L) Bl). }
  split.
  { intros i' Hi' He. apply (rkk_asrc_m cx ly1 S1 W1 m1 m2 md1 _ _ HB HAR HK HP (G11 i' Hi' He)).
    unfold gslot. apply (rkk_slot_loc cx _ HB). apply (rkk_j4 cx i' HB); [lia | exact He]. }
  split.
  { intros Ho. apply (rkk_asrc_m cx ly1 S1 W1 m1 m2 md1 _ _ HB HAR HK HP (G12 Ho)).
    unfold gslot. apply (rkk_slot_loc cx _ HB). apply (rkk_j4 cx i HB G1). apply Z.eqb_eq. exact Ho. }
  split.
  { rewrite Forall_forall in G13 |- *. intros p Hp Heof.
    exact (rkk_drsrc cx ly1 S1 W1 m1 m2 md1 _ _ _ HB HAR HK HP (G13 p Hp Heof)). }
  split.
  { intros a Ha Hj. destruct (G14 a Ha Hj) as [V Wr].
    destruct (KC a (rkk_glob cx a HB ltac:(tauto))) as [V2 Wr2].
    unfold abyte_kept. split; [rewrite V2; exact V | intros Hw; apply Wr2; apply Wr; exact Hw]. }
  split; [exact G15|].
  split.
  { apply (akept_garr8 W1 m1); [|exact G16]. intros x Hx. apply KC.
    pose proof (rkk_pre_len cx). rewrite length_app in Hx. cbn [length] in Hx. lia. }
  split.
  { apply (akept_garr8 W1 m1); [|exact G17]. intros x Hx. apply KC.
    assert (HF8 : 0 <= F / 8 <= 2 ^ 45) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    cbn [length] in Hx. unfold shadow_addr, SHADOW_OFF in Hx. lia. }
  exact G18.
Qed.
(* W_rig_key.v:1918 rkk_live at R *)
Theorem rkk_live_xR : forall cx F FL fpos ly1 S1 W1 m1 md1 k1 m2 md2 k2,
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  rom_view SEGS W1 m1 -> apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 -> alock_at RG W1 m1 true ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m2 md2 k2 ->
  rkk_KEEP cx W1 m1 m2 -> rkk_PRES W1 m1 m2 ->
  GLIVE_xR B PST ARx RG R cx F FL ly1 S1 W1 m2 md2 k2.
Proof.
  intros cx F FL fpos ly1 S1 W1 m1 md1 k1 m2 md2 k2 HB HJ HR HA HF HL HJ2 HK HP.
  destruct (rkk_jar_xR cx fpos ly1 S1 W1 m1 md1 k1 HJ) as [HAR Hfr].
  destruct (rk_fb ly1 S1 W1 m1 md1 1 fpos HAR Hfr) as (HF4 & HFc & _).
  change (fs_frame_bytes 1) with 128 in HFc.
  assert (KC : forall a, 0 <= a < alloc_ceiling -> abyte_kept W1 m1 W1 m2 a)
    by (intros a Ha; exact (rkk_kept_c cx W1 m1 m2 a HB HK HP Ha)).
  assert (KH : forall a, gsp1 cx <= a < gsp0 cx -> abyte_kept W1 m1 W1 m2 a)
    by (intros a Ha; exact (rkk_kept_hi cx W1 m1 m2 a HK HP Ha)).
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  unfold GLIVE_xR. exists fpos, []. split; [rewrite (rk_gxHp cx HB); exact HJ2|].
  split.
  { intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
    destruct (KC a (rkk_img a Hi)) as [V _]. rewrite V. exact (HR a Ha). }
  split.
  { intros a Ha1 Ha2 Ha3 Ha4. apply HP. exact (HA a Ha1 Ha2 Ha3 Ha4). }
  split.
  { destruct HF as (HFa & HFl & H120 & H16 & H24 & H80 & Hsv).
    rewrite HFa in HF4, HFc.
    unfold g_frame. split; [exact HFa|]. split; [exact HFl|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; change (Z.of_nat 8) with 8 in Hx; lia | exact H120]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H16]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H24]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H80]|].
    intros j Hj. apply (akept_vm W1 m1); [|exact (Hsv j Hj)].
    intros x Hx. apply KH. change (Z.of_nat 8) with 8 in Hx. lia. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HL). intros r Hr a Ha. destruct Hr as [<-|[]].
  apply KC. cbn [fst snd] in Ha. apply (rkk_glob cx a HB). tauto.
Qed.
(* W_rig_key.v:2315 rk_callS at R *)
Lemma rk_callS_xR : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc [] W regsc memc mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK1 (spZ regsc) FP1 lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK1 (sp0 + o) FP1 lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply (SRrG_mono SEGS R).
{ apply Hcallee.
  destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S [] W0 memS md own lyc Sc [] W memc mdc k regsc STK1 o ch1 HJi); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own).
eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS pa_segs_low R_trans); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.
(* W_rig_key.v:2378 rk_gx_keep_high at R *)
Lemma rk_gx_keep_high_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* W_rig_key.v:2389 rk_gx_ly_top at R *)
Lemma rk_gx_ly_top_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k -> ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* W_rig_key.v:2398 rk_chain2p at R *)
Lemma rk_chain2p_xR : forall cx own ly1 S1 W1 m1 md1 k1,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) own ly1 S1 [] W1 m1 md1 k1 ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 8) 8 (bv_unsigned (getr (gxregs cx) 1)) ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 16) 8 (bv_unsigned (getr (gxregs cx) 8)) ->
gsp0 cx < ly_top ly1 - 16 ->
achain ly1 (aview SEGS (w_H W1) m1) (gsp0 cx + -224) (gsp0 cx) ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx).
Proof.
intros cx own ly1 S1 W1 m1 md1 k1 HB HJ V1 V8 Hlt.
pose proof HB as (HPRE0 & H32 & _). pose proof HPRE0 as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity.
pose proof (rk_gx_ly_top_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as ETop.
fold (gsp0 cx) in *.
apply (achain_ly_top (gxly cx) ly1); [exact ETop|].
apply (achain_push (gxly cx) (aview SEGS (w_H (gxW cx)) (gxmem cx))); [exact Hch | lia | | | | exact Hra4 | lia | | rewrite <- ETop; lia | lia].
- intros a Ha. apply (rk_gx_keep_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGRIG HJ); lia.
- apply (rdword_of_val_mem SEGS). exact V1. apply bv_unsigned_in_range.
- apply (rdword_of_val_mem SEGS). exact V8. apply bv_unsigned_in_range.
- replace (gsp0 cx) with (8 * (2 * (gsp0 cx / 16))) by (pose proof (Z.div_mod (gsp0 cx) 16 ltac:(lia)); lia).
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
(* W_rig_key.v:2422 rk_chain2 at R *)
Lemma rk_chain2_xR : forall cx own ly1 S1 W1 m1 md1 k1,
GBASE B ARx MT RP MMAX RG cx ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) own ly1 S1 [] W1 m1 md1 k1 ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 8) 8 (bv_unsigned (getr (gxregs cx) 1)) ->
val_mem SEGS (arm W1 m1) (gsp0 cx - 16) 8 (bv_unsigned (getr (gxregs cx) 8)) ->
exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (gsp0 cx + -224) (gsp0 cx) ch1.
Proof.
intros cx own ly1 S1 W1 m1 md1 k1 HB HJ V1 V8.
destruct (Z_lt_le_dec (gsp0 cx) (ly_top ly1 - 16)) as [Hlt | Hge].
- exists ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx). exact (rk_chain2p_xR cx own ly1 S1 W1 m1 md1 k1 HB HJ V1 V8 Hlt).
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
(* W_rig_key.v:2523 rk_keep_blk at R *)
Lemma rk_keep_blk_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
gx_ok SEGS B G -> ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
destruct (rk_alb ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
pose proof asan_consts as (C1 & _).
rewrite unsigned_lit_small in HGa by lia.
destruct (HGx _ HGa) as [Hi' _].
pose proof (rk_boi ly' S' W' mem' md' p n HAR0 H2) as Hoff.
pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
(* W_rig_key.v:2539 rk_ge_blk at R *)
Lemma rk_ge_blk_xR : forall XO OUT STK sp0 ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k cap out cap' out' rest p n,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) XO OUT STK sp0 (ablocks_fp (aout_blks cap out)) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 k ->
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) -> Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
In (p, n) (ablocks B ly1 S1) -> ~ In (p, n) (aout_blks cap out) ->
In (p, n) (ablocks B ly2 S2) /\ (forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) m2 (p + i) = aview SEGS (w_H W1) m1 (p + i)).
Proof.
intros XO OUT STK sp0 ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k cap out cap' out' rest p n HJ HAR P1 P2 Hin Hno.
assert (Hr : In (p, n) rest).
{ apply (Permutation_in _ P1) in Hin. apply in_app_or in Hin as [Ho | Hr]; [contradiction | exact Hr]. }
assert (Hin2 : In (p, n) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2)); apply in_or_app; right; exact Hr).
split; [exact Hin2|]. intros i Hi.
apply (rk_keep_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n i HGRIG HJ Hin Hin2 Hi).
intros Hf. apply inFP_ablocks_fp_inv in Hf as (p' & n' & Hin' & Hpa).
assert (Hin'1 : In (p', n') (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym P1)); apply in_or_app; left; exact Hin').
assert (Hne : (p, n) <> (p', n')) by (intros E; rewrite E in Hno; exact (Hno Hin')).
pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR Hin Hin'1 Hne) as Hd. cbn [fst snd] in Hd. lia.
Qed.
(* W_rig_key.v:2558 rk_ge_call at R *)
Lemma rk_ge_call_xR : forall W regsc memc mdc STK sp0 FP ly S W0 mem md own lyc Sc k raw c O mx no cap out x q m (o : Z) ch1,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> GE_STK - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
getr regsc 10 = w64 q ->
aout_at B RG lyc Sc W memc c O mx no cap out ->
garr8 SEGS (arm W memc) q (bzs (x ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) x ->
14 <= Z.of_nat (length x) <= APARTIAL ->
In (q, m) (ablocks B lyc Sc) -> q <> out -> Z.of_nat (length x) + 1 <= req_size m ->
garr8 SEGS (arm W memc) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W memc ->
ge_room MMAX (blocks_bytes Sc) c mx no cap (Z.of_nat (length x)) ->
mo_ok MT Sc (ge_cost MT c mx no cap (Z.of_nat (length x))) ->
forall kr : nat,
rp_RM RP Sc (Z.to_nat (ge_cost MT_rk c mx no cap (Z.of_nat (length x))) + kr) ->
cnt_ok_pk RP ge_pk (ablocks B lyc Sc) ->
(forall a, inFP (ablocks_fp (aout_blks cap out)) a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1 out' kg,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] GE_STK (sp0 + o) (ablocks_fp (aout_blks cap out)) lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (sp0 + o) (ablocks_fp (aout_blks cap out)) lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 kg /\
 aregs_preserved regsc regs2 /\ apres_kept B W memc W2 mem2 /\
 mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
 (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
   Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
 aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
   (ge_cap c mx no cap (Z.of_nat (length x))) out').
Proof.
intros W regsc memc mdc STK sp0 FP ly S W0 mem md own lyc Sc k raw c O mx no cap out x q m o ch1
  HJ Hsp Hal Hneg HSTK Hgp Htp Hra Hraw Hra4 Hch H10 HOUT GK NZ X1 Hq Hqo Hqm G5 HROM ROOM MOK kr HRM HCN HF.
eapply (SRrG_mono SEGS R).
{ eapply (rk_callS_xR (G_RIG B RG) W regsc memc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    GE_STK (ablocks_fp (aout_blks cap out)) o raw ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => exists out' kg,
      ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (sp0 + o) (ablocks_fp (aout_blks cap out)) lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 kg /\
      apres_kept B W memc W2 mem2 /\
      mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
      (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
        Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) out')
    HGRIG HJ Hsp Hal Hneg).
  - unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK. lia.
  - exact HSTK.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - exact Hch.
  - intros HPRE1. eapply (SRrG_mono SEGS R).
    { exact (GE_R W lyc Sc [] regsc memc mdc ch1 c O mx no cap out q x q m HPRE1 H10 HOUT GK NZ X1 Hq Hqo
        ltac:(lia) ltac:(lia) G5 HROM ROOM MOK kr HRM HCN). }
    cbv beta. intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & out3 & -> & HJ3 & HP3 & HA3 & HM3 & HRM3 & HPm3 & HO3).
    assert (EH3 : Hp3 = []) by (eapply rk_jhp0_xR; exact HJ3). subst Hp3.
    exists ly3, S3, regs3, mem3, md3, k3. split; [rewrite Hra; reflexivity|].
    split; [exact (rig_lift_SL_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)|]. split; [exact HP3|].
    exists out3, k3. rewrite <- Hsp. split; [exact HJ3|]. split; [exact HA3|]. split; [exact HM3|]. split; [exact HRM3|].
    split; [exact HPm3 | exact HO3].
  - exact HF. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc2 & HP2 & (out' & kg & HJs & HA & HM & HRM2 & HPm & HO)).
exists ly2, S2, regs2, mem2, md2, k1, out', kg. split; [reflexivity|]. split; [exact HJ2|].
split; [exact HJc2|]. split; [exact HJs|]. split; [exact HP2|]. split; [exact HA|]. split; [exact HM|]. split; [exact HRM2|].
split; [exact HPm | exact HO].
Qed.
(* W_rig_key.v:2628 rk_free at R *)
Lemma rk_free_xR : forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) raw ch,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
forall kr : nat, rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
(forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
 ~ (pa <= a < pa + req_size n) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).
Proof.
intros G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
  (H0 & H1 & (memS & HJi & Hag) & Hout) Hin H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch Hctx HFP MOK kr HRM HCN.
rewrite !Z.add_0_r in HJi.
assert (HSR : ly_bot lyc + ACALL_PREFIX < spZ regsT) by (eapply aj_stack_room_xR; [exact HJi | exact Hsp | exact Hst]).
eapply (SRrG_mono SEGS R).
{ exact (AFREE_R W regsT memT STK sp0 FP ly S [] W0 memS md own lyc Sc [] mdc k pa n o raw ch kr HJi Hin H10 Hsp Hal Hneg Hst
    HSR Hgp Htp Hra Hraw Hch (RO_ARx _ _ _ _ _ _ (proj1 HJi)) Hctx HRM HCN HFP MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HL & HFr & HK & HM & HRM2 & HE & HPr).
assert (EH2 : Hp2 = []) by (exact (HP0 _ _ _ _ _ _ (proj1 HJ2))). subst Hp2.
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
split; [exact HP2|]. split; [exact HL|]. split; [exact HFr|]. split; [exact HK|]. split; [exact HM|]. split; [exact HRM2|].
split; [exact HE | exact HPr].
Qed.
(* W_rig_key.v:2930 rk_fpos_eq at R *)
Lemma rk_fpos_eq_xR : forall cx p1 p2 ly S W m md k m' md' k',
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, p1)] ly S [] W m md k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, p2)] ly S [] W m' md' k' ->
p1 = p2.
Proof.
intros cx p1 p2 ly S W m md k m' md' k' (_ & _ & (memS1 & HJ1 & _) & _) (_ & _ & (memS2 & HJ2 & _) & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & F1 & _). pose proof HJ2 as (_ & _ & _ & _ & _ & F2 & _).
rewrite F1 in F2. cbn [app] in F2. injection F2 as E. exact E.
Qed.
(* W_rig_key.v:3721 rkk_jx_img at R *)
Lemma rkk_jx_img_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST ->
  fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hps Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hps Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* W_rig_key.v:3732 rkk_jx_high at R *)
Lemma rkk_jx_high_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok SEGS B G -> ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* W_rig_key.v:3743 rkk_jx_blk at R *)
Lemma rkk_jx_blk_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok SEGS B G -> ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (rk_alb ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (rk_boi ly' S' W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
(* W_rig_key.v:3758 rkk_jx_frame at R *)
Lemma rkk_jx_frame_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok SEGS B G -> ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (cid, pos) (frames S) ->
  in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    Hf Ha Hfp Hr Hni.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hf Ha Hfp).
  apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia.
  intros HGa. exact (Hni (proj1 (HGx a HGa))).
Qed.
(* W_rig_key.v:3771 rkk_jx_lyF at R *)
Lemma rkk_jx_lyF_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ly_F ly' = ly_F ly /\ frames S' = own ++ frames S.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (_ & Hly & _ & _ & _ & Hfr & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
  split; [exact HF | exact Hfr].
Qed.
(* W_rig_key.v:4016-4688 Section e at R *)
Section eR.
Variables (cx : gcx) (i n r : nat) (F FL fpos : Z) (qd : list (rentry * hsrc)) (cB : ctl) (OB : list byte) (capB : Z)
  (e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 : Z)
  (ks Ed : list (Z * list byte * list byte)) (f : nat) (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z)
  (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (mA : word -> option byte) (mdA : Model) (kA : Z)
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mB mB' : word -> option byte) (mdB : Model) (kB : Z) (out2' : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mC mD : word -> option byte) (mdC mdD : Model) (kD : Z)
  (l1 l2 : list (Z * Z)) (slo shi : Z).
#[local] Notation ek_k := (nth n ks (0, [], [])).
#[local] Notation ek_kt := (key_text ek_k).
#[local] Notation ek_xl := (Z.of_nat (length ek_kt)).
#[local] Notation ek_ks2 := (swap_remove (0, [], []) n ks).
#[local] Notation ek_SA := (gSA cx i).
#[local] Notation ek_hp := (re_hp e1).
#[local] Notation ek_no2 := (Z.of_nat (length O2)).
#[local] Notation ek_c2 := (ge_ctl c2 ek_xl).
#[local] Notation ek_O2 := (ge_O c2 O2 ek_kt).
#[local] Notation ek_cap2 := (ge_cap c2 (gxmx cx) ek_no2 cap2 ek_xl).
#[local] Notation ek_kl := (nth (length ks - 1) ks (0, [], [])).
#[local] Notation ek_kb := (key_addr ek_k, ek_xl + 1).
#[local] Notation ek_T := (gxG0 cx, ATABLE).
#[local] Notation ek_H := (re_hp e1, re_kh e1).
#[local] Notation ek_es := (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx)).
#[local] Notation ek_es2 := (map fst qd ++ entry_keys e1 ek_ks2 :: skipn (S i) (gxes cx)).
#[local] Notation ek_open := (re_eof (gnth cx i) =? 0).
#[local] Notation ek_src := (gdone_srcs (firstn i (gps cx)) qd ++ (if ek_open then asrc_blks h1 else []) ++
  rig_srcs (skipn (S i) (gps cx))).
#[local] Notation ek_C1 a := (ek_SA + 48 <= a < ek_SA + 52).
#[local] Notation ek_C2 a := (ek_hp + 8 * Z.of_nat n <= a < ek_hp + 8 * Z.of_nat n + 8).

Hypothesis HB : GBASE B ARx MT RP MMAX RG cx.
Hypothesis HJ1 : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx)
  (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 mA mdA kA.
Hypothesis HG : GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA.
Hypothesis HAP1 : apres_kept B (gxW cx) (gxmem cx) W1 mA.
Hypothesis HF1 : g_frame cx fpos F FL ly1 W1 mA.
Hypothesis HL1 : alock_at RG W1 mA true.
Hypothesis HLS1 : g_lslots RG cx F W1 mA.
Hypothesis H32 : val_mem SEGS (arm W1 mA) (gsp1 cx + 32) 8 ((ek_SA + 48) mod 8 + 3).
Hypothesis H88 : val_mem SEGS (arm W1 mA) (gsp1 cx + 88) 8 (Z.of_nat i).
Hypothesis HJG : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (gsp1 cx) (ablocks_fp (aout_blks cap2 out2))
  ly1 S1 [] W1 mA mdA [] ly2 S2 [] W2 mB mdB kB.
Hypothesis HAP12 : apres_kept B W1 mA W2 mB.
Hypothesis HPG : exists rest, Permutation (ablocks B ly1 S1) (aout_blks cap2 out2 ++ rest) /\
  Permutation (ablocks B ly2 S2) (aout_blks ek_cap2 out2' ++ rest).
Hypothesis HO2 : aout_at B RG ly2 S2 W2 mB ek_c2 ek_O2 (gxmx cx) (ge_no c2 ek_no2 ek_xl) ek_cap2 out2'.
Hypothesis HK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) ->
  aview SEGS (w_H W2) mB' a = aview SEGS (w_H W2) mB a.
Hypothesis HP2 : forall a, apresent (w_H W2) mB a -> apresent (w_H W2) mB' a.
Hypothesis HAR3 : ARh ly3 S3 W3 mC mdC.
Hypothesis HL2 : ablocks B ly2 S2 = l1 ++ ek_kb :: l2.
Hypothesis HL3 : ablocks B ly3 S3 = l1 ++ l2.
Hypothesis HCK : acall_kept SEGS B ly2 S2 W2 mB' W3 mC slo shi (fun a => key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1)).
Hypothesis Hslo : gsp1 cx - DRAIN_STK_x <= slo.
Hypothesis Hshi : shi <= gsp1 cx.
Hypothesis HERR : forall j, 0 <= j < 4 -> aview SEGS (w_H W3) mC (as_errno B + j) = aview SEGS (w_H W2) mB' (as_errno B + j).
Hypothesis HAPF : forall a, in_img SEGS a -> ~ aowned B ly2 S2 a -> ~ aowned B ly3 S3 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1)) -> apresent (w_H W2) mB' a -> apresent (w_H W3) mC a.
Hypothesis HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ ek_C1 a -> ~ ek_C2 a ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W3) mC a.
Hypothesis HP3 : forall a, apresent (w_H W3) mC a -> apresent (w_H W3) mD a.
Hypothesis HNH : val_mem SEGS (arm W3 mD) (ek_SA + 48) 4 (Z.of_nat (length ek_ks2)).
Hypothesis HSL : val_mem SEGS (arm W3 mD) (ek_hp + 8 * Z.of_nat n) 8 (key_addr ek_kl).
Hypothesis HJ3 : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx)
  (gxmem cx) (gxmd cx) [(1, fpos)] ly3 S3 [] W3 mD mdD kD.

(* ---- GIN's facts, and the three allocator states ---- *)
Lemma ek_gin_xR :
  (i < length (gxes cx))%nat /\ length qd = i /\ length ks = (n + S r)%nat /\
  arelay_at B RG ly1 S1 W1 mA (gxG0 cx) ek_es /\
  aout_at B RG ly1 S1 W1 mA c2 O2 (gxmx cx) ek_no2 cap2 out2 /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly1 S1 W1 mA (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  (ek_open = true -> asrc_at B ly1 S1 W1 mA (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 mA (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W1 mA a) /\
  Permutation (ablocks B ly1 S1) (ek_T :: concat (map aentry_blks ek_es) ++ ek_src ++ aout_blks cap2 out2 ++ gxrest cx) /\
  garr8 SEGS (arm W1 mA) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W1 mA) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
  pose proof HG as HG'. unfold GIN in HG'. cbv zeta in HG'.
  destruct HG' as (G1 & G2 & _ & _ & _ & G6 & _ & _ & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & _).
  split; [exact G1|]. split; [exact G2|]. split; [exact G6|]. split; [exact G9|]. split; [exact G10|].
  split; [exact G11|]. split; [exact G12|]. split; [exact G13|]. split; [exact G14|].
  split; [rewrite <- !app_assoc; exact G15|]. split; [exact G16 | exact G17].
Qed.

Lemma ek_ar1_xR : ARh ly1 S1 W1 mA mdA.
Proof. eapply rk_jAR_xR. exact HJ1. Qed.
Lemma ek_ar2_xR : ARh ly2 S2 W2 mB mdB.
Proof. eapply rk_jAR_xR. exact HJG. Qed.
Lemma ek_ar4_xR : ARh ly3 S3 W3 mD mdD.
Proof. eapply rk_jAR_xR. exact HJ3. Qed.

Lemma ek_nlt_xR : (n < length ks)%nat.
Proof. destruct ek_gin_xR as (_ & _ & E & _). lia. Qed.

(* entry i as KEY reads it (rkr_entry_at) *)
Lemma ek_entry_xR :
  In ek_T (ablocks B ly1 S1) /\ 4096 <= gxG0 cx /\ gxG0 cx + ATABLE <= alloc_ceiling /\
  gxG0 cx <= ek_SA /\ ek_SA + AENT <= gxG0 cx + ATABLE /\
  ek_hp <> 0 /\ In ek_H (ablocks B ly1 S1) /\ 8 * Z.of_nat (length ks) <= re_kh e1 /\
  In ek_kb (ablocks B ly1 S1).
Proof.
  destruct ek_gin_xR as (G1 & G2 & G6 & G9 & _).
  pose proof (rkr_entry_at ly1 S1 W1 mA mdA (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n ek_ar1_xR G9 ek_nlt_xR) as Rk.
  cbv zeta in Rk. rewrite length_map, G2 in Rk.
  destruct Rk as (R1 & _ & R3 & R4 & R5 & _ & _ & _ & R9 & R10 & R11 & _ & _ & _ & R15 & _).
  assert (ESA : gSA cx i = gxG0 cx + AENT * Z.of_nat i) by reflexivity.
  split; [exact R1|]. split; [exact R3|]. split; [exact R4|]. split; [rewrite ESA; unfold AENT; lia|].
  split; [rewrite ESA; exact R5|]. split; [exact R9|]. split; [exact R10|]. split; [exact R11 | exact R15].
Qed.

(* ---- the blocks: the key's block leaves; every other block of GIN's list stays ---- *)
#[local] Notation ek_P2 := (ek_T :: concat (map aentry_blks ek_es2) ++ ek_src).

Lemma ek_ae_xR : forall ks0, aentry_blks (entry_keys e1 ks0) =
  ((if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++ (if re_hp e1 =? 0 then [] else [ek_H])) ++
  map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks0.
Proof. intros ks0. unfold aentry_blks. cbn [entry_keys re_cap re_buf re_hp re_kh re_keys]. rewrite app_assoc. reflexivity. Qed.

Lemma ek_perm_kb_xR : Permutation (concat (map aentry_blks ek_es)) (ek_kb :: concat (map aentry_blks ek_es2)).
Proof.
  rewrite !map_app, !concat_app. cbn [map concat]. rewrite !ek_ae_xR.
  apply rkk_perm_mid3.
  exact (Permutation_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))
    (relay_instance_gone_b_lem.rigl_swap_perm (0, [], []) n ks ek_nlt_xR)).
Qed.

Lemma ek_perm1_xR : Permutation (ablocks B ly1 S1) (ek_kb :: ek_P2 ++ aout_blks cap2 out2 ++ gxrest cx).
Proof.
  destruct ek_gin_xR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  eapply Permutation_trans; [exact HP|].
  eapply Permutation_trans; [apply perm_skip; apply Permutation_app_tail; exact ek_perm_kb_xR|].
  cbn [app]. rewrite <- !app_assoc. apply perm_swap.
Qed.

Lemma ek_nd_xR : List.NoDup (ek_kb :: ek_P2 ++ aout_blks cap2 out2 ++ gxrest cx).
Proof. exact (Permutation_NoDup ek_perm1_xR (rk_ablocks_nodup _ _ _ _ _ ek_ar1_xR)). Qed.

Lemma ek_inP2_xR : forall b, In b ek_P2 -> In b (ablocks B ly1 S1) /\ ~ In b (aout_blks cap2 out2) /\ b <> ek_kb.
Proof.
  intros b Hb. pose proof ek_nd_xR as ND. apply List.NoDup_cons_iff in ND as [Hkb ND].
  split; [apply (Permutation_in _ (Permutation_sym ek_perm1_xR)); right; apply in_or_app; left; exact Hb|].
  split; [intros Ho; exact (rk_nodup_app_disj _ _ b ND Hb (in_or_app _ _ _ (or_introl Ho)))|].
  intros ->. apply Hkb. apply in_or_app. left. exact Hb.
Qed.

Lemma ek_kb1_xR : In ek_kb (ablocks B ly1 S1) /\ ~ In ek_kb (aout_blks cap2 out2).
Proof.
  split; [apply (Permutation_in _ (Permutation_sym ek_perm1_xR)); left; reflexivity|].
  intros Ho. pose proof ek_nd_xR as ND. apply List.NoDup_cons_iff in ND as [Hkb _].
  apply Hkb. apply in_or_app. right. apply in_or_app. left. exact Ho.
Qed.

Lemma ek_to2_xR : forall b, In b (ablocks B ly1 S1) -> ~ In b (aout_blks cap2 out2) ->
  In b (ablocks B ly2 S2) /\ ~ In b (aout_blks ek_cap2 out2').
Proof.
  intros b Hb Ho. destruct HPG as (rest & P1 & P2).
  pose proof (Permutation_in _ P1 Hb) as H1. apply in_app_or in H1 as [H1|H1]; [exfalso; exact (Ho H1)|].
  split; [apply (Permutation_in _ (Permutation_sym P2)); apply in_or_app; right; exact H1|].
  intros Ho2. pose proof (Permutation_NoDup P2 (rk_ablocks_nodup _ _ _ _ _ ek_ar2_xR)) as ND.
  exact (rk_nodup_app_disj _ _ b ND Ho2 H1).
Qed.

Lemma ek_to3_xR : forall b, In b (ablocks B ly2 S2) -> b <> ek_kb -> In b (ablocks B ly3 S3).
Proof.
  intros b Hb Hne. rewrite HL2 in Hb. rewrite HL3. apply in_app_or in Hb as [Hb|[Hb|Hb]].
  - apply in_or_app. left. exact Hb.
  - exfalso. apply Hne. symmetry. exact Hb.
  - apply in_or_app. right. exact Hb.
Qed.

Lemma ek_kb2_xR : In ek_kb (ablocks B ly2 S2).
Proof. rewrite HL2. apply in_or_app. right. left. reflexivity. Qed.

Lemma ek_out1_xR : forall b, In b (aout_blks cap2 out2) -> In b (ablocks B ly1 S1).
Proof.
  intros b Hb. destruct ek_gin_xR as (_ & _ & _ & _ & G10 & _).
  destruct G10 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  unfold aout_blks in Hb. destruct H26 as [(Hc & _) | (Hc & _ & Hin & _)].
  - rewrite Hc in Hb. cbn in Hb. destruct Hb.
  - destruct (cap2 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. destruct Hb as [<-|[]]. exact Hin.
Qed.

Lemma ek_outB_xR : forall b, In b (aout_blks ek_cap2 out2') -> In b (ablocks B ly2 S2).
Proof.
  intros b Hb.
  destruct HO2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  unfold aout_blks in Hb. destruct H26 as [(Hc & _) | (Hc & _ & Hin & _)].
  - rewrite Hc in Hb. cbn in Hb. destruct Hb.
  - destruct (ek_cap2 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. destruct Hb as [<-|[]]. exact Hin.
Qed.

Lemma ek_H_in_xR : In ek_H (concat (map aentry_blks ek_es2)).
Proof.
  apply in_concat. exists (aentry_blks (entry_keys e1 ek_ks2)). split.
  - apply in_map. apply in_or_app. right. left. reflexivity.
  - rewrite ek_ae_xR. apply in_or_app. left. apply in_or_app. right.
    destruct ek_entry_xR as (_ & _ & _ & _ & _ & Hz & _). rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
Qed.

Lemma ek_src_ne_xR : forall b, In b ek_src -> b <> ek_T /\ b <> ek_H.
Proof.
  intros b Hb. pose proof ek_nd_xR as ND. apply List.NoDup_cons_iff in ND as [_ ND].
  cbn [app] in ND. apply List.NoDup_cons_iff in ND as [HT ND].
  split.
  - intros ->. apply HT. apply in_or_app. left. apply in_or_app. right. exact Hb.
  - intros ->. apply NoDup_app_remove_r in ND. exact (rk_nodup_app_disj _ _ _ ND ek_H_in_xR Hb).
Qed.

(* ---- where the bytes are ---- *)
Lemma ek_frame_xR : In (1, fpos) (frames S1) /\ frame_addr ly1 1 fpos = F /\ 4096 <= F /\ F + 128 <= alloc_ceiling /\
  off_img F 128 /\ In (1, fpos) (frames S2) /\ frame_addr ly2 1 fpos = F /\ frame_addr ly3 1 fpos = F /\
  flag_addr ly3 1 fpos = FL.
Proof.
  destruct (rkk_jar_xR cx fpos ly1 S1 W1 mA mdA kA HJ1) as [_ Hfr].
  destruct HF1 as (HFa & HFl & _).
  destruct (rk_fb ly1 S1 W1 mA mdA 1 fpos ek_ar1_xR Hfr) as (HF4 & HFc & _).
  pose proof (rk_foi ly1 S1 W1 mA mdA 1 fpos ek_ar1_xR Hfr) as Hoff.
  rewrite HFa in HF4, HFc, Hoff. change (fs_frame_bytes 1) with 128 in HFc, Hoff.
  pose proof HJG as X2. apply rkk_jx_lyF_xR in X2. destruct X2 as [LF2 FR2].
  pose proof HJ1 as X1. apply rkk_jx_lyF_xR in X1. destruct X1 as [LF1 _].
  pose proof HJ3 as X3. apply rkk_jx_lyF_xR in X3. destruct X3 as [LF3 _].
  split; [exact Hfr|]. split; [exact HFa|]. split; [exact HF4|]. split; [exact HFc|]. split; [exact Hoff|].
  split; [rewrite FR2; exact Hfr|].
  split; [unfold frame_addr in *; rewrite LF2; exact HFa|].
  split; [unfold frame_addr in *; rewrite LF3, <- LF1; exact HFa|].
  unfold flag_addr in *; rewrite LF3, <- LF1; exact HFl.
Qed.

Lemma ek_blk_loc_xR : forall p nn a, In (p, nn) (ablocks B ly1 S1) -> p <= a < p + req_size nn ->
  4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\ ~ (F <= a < F + 128) /\ ~ (shadow_addr F <= a < shadow_addr F + 16).
Proof.
  intros p nn a Hin Ha.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar1_xR Hin) as (_ & H4 & Hc & Happ & _).
  pose proof (rk_boi ly1 S1 W1 mA mdA p nn ek_ar1_xR Hin) as Hoff.
  destruct ek_frame_xR as (Hfr & HFa & HF4 & HFc & _).
  pose proof (rk_frame_blk_apart ly1 S1 W1 mA mdA 1 fpos p nn ek_ar1_xR Hfr Hin) as Hd. rewrite HFa in Hd.
  change (fs_frame_bytes 1) with 128 in Hd.
  pose proof asan_consts as (C1 & _ & C3 & _).
  assert (HF8 : 0 <= F / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  split; [lia|]. split.
  { intros Hi. pose proof (pa_img_range a Hi). unfold off_img in Hoff. lia. }
  split; [lia|].
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. rewrite C3 in Happ. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Lemma ek_cells_in_xR : forall a, ek_C1 a \/ ek_C2 a ->
  (gxG0 cx <= a < gxG0 cx + req_size ATABLE) \/ (ek_hp <= a < ek_hp + req_size (re_kh e1)).
Proof.
  destruct ek_entry_xR as (_ & _ & _ & HSA & HSA2 & _ & _ & Hkh & _). pose proof ek_nlt_xR.
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hr]. change (req_size ATABLE) with 896.
  intros a [Hc|Hc]; [left | right]; unfold AENT, ATABLE in *; lia.
Qed.

Lemma ek_cells_low_xR : forall a, ek_C1 a \/ ek_C2 a ->
  4096 <= a < alloc_ceiling /\ ~ in_img SEGS a /\ ~ (F <= a < F + 128) /\ ~ (shadow_addr F <= a < shadow_addr F + 16).
Proof.
  intros a Hc. destruct ek_entry_xR as (HT & _ & _ & _ & _ & _ & HH & _).
  destruct (ek_cells_in_xR a Hc) as [Ha|Ha]; [exact (ek_blk_loc_xR _ _ a HT Ha) | exact (ek_blk_loc_xR _ _ a HH Ha)].
Qed.

Lemma ek_cells_apart_xR : forall ly S W m md b a, ARh ly S W m md -> In ek_T (ablocks B ly S) -> In ek_H (ablocks B ly S) ->
  In b (ablocks B ly S) -> b <> ek_T -> b <> ek_H -> fst b <= a < fst b + snd b -> ~ ek_C1 a /\ ~ ek_C2 a.
Proof.
  intros ly S W m md b a HAR HT HH Hb N1 N2 Ha.
  pose proof (rk_blk_apart ly S W m md b ek_T HAR Hb HT N1) as D1.
  pose proof (rk_blk_apart ly S W m md b ek_H HAR Hb HH N2) as D2.
  cbn [fst snd] in D1, D2.
  assert (Rb : snd b <= req_size (snd b)) by (unfold req_size; destruct (Z.eqb_spec (snd b) 0); lia).
  split; intros Hc.
  - destruct (ek_cells_in_xR a (or_introl Hc)) as [Hx|Hx]; [lia|].
    destruct ek_entry_xR as (_ & _ & _ & HSA & HSA2 & _). change (req_size ATABLE) with 896 in D1. unfold AENT, ATABLE in *. lia.
  - destruct (ek_cells_in_xR a (or_intror Hc)) as [Hx|Hx]; [|lia].
    destruct ek_entry_xR as (_ & _ & _ & _ & _ & _ & _ & Hkh & _). pose proof ek_nlt_xR.
    pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hr]. lia.
Qed.

Lemma ek_ceil_xR : alloc_ceiling <= gsp1 cx - DRAIN_STK_x.
Proof. exact (rkk_ceil cx HB). Qed.

(* ---- the views and the presence, from one state to the next ---- *)
Lemma ek_kb_not_img_xR : forall a, in_img SEGS a -> ~ (key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1)).
Proof. intros a Hi Hk. destruct (ek_blk_loc_xR _ _ a (proj1 ek_kb1_xR) Hk) as (_ & Hn & _). exact (Hn Hi). Qed.

Lemma ek_V24_img_xR : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W2) mB a.
Proof.
  intros a Hi Ho He. pose proof (rkk_img a Hi) as Ha. pose proof ek_ceil_xR. pose proof asan_consts as (C1 & _).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low_xR a (or_introl Hc)) as (_ & Hn & _); exact (Hn Hi)).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low_xR a (or_intror Hc)) as (_ & Hn & _); exact (Hn Hi)).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  destruct HCK as (_ & _ & K3 & _). rewrite (K3 a Hi Ho He).
  apply HK2; lia.
Qed.

Lemma ek_P24_img_xR : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  apresent (w_H W2) mB a -> apresent (w_H W3) mD a.
Proof.
  intros a Hi Ho He Hp. apply HP3. apply HAPF; [exact Hi | exact (rkk_not_owned _ _ _ _ _ a ek_ar2_xR Hi Ho)
    | exact (rkk_not_owned _ _ _ _ _ a HAR3 Hi Ho) | exact He | exact (ek_kb_not_img_xR a Hi) | exact (HP2 a Hp)].
Qed.

Lemma ek_K24_img_xR : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept W2 mB W3 mD a.
Proof.
  intros a Hi Ho He. split; [exact (ek_V24_img_xR a Hi Ho He)|].
  apply (rkk_img_wr W2 W3 mB mD a Hi). exact (ek_P24_img_xR a Hi Ho He).
Qed.

Lemma ek_V12_img_xR : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W2) mB a = aview SEGS (w_H W1) mA a.
Proof.
  intros a Hi Ho He Hps Hg. eapply rkk_jx_img_xR; [exact HJG | exact Hi | exact Ho | exact He | exact Hps | | exact Hg].
  apply rkk_fp_spares. intros [p nn] Hb.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar1_xR (ek_out1_xR _ Hb)) as (_ & H4 & _). exact H4.
Qed.

Lemma ek_K14_img_xR : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> abyte_kept W1 mA W3 mD a.
Proof.
  intros a Hi Ho He Hps Hg. split; [rewrite (ek_V24_img_xR a Hi Ho He); exact (ek_V12_img_xR a Hi Ho He Hps Hg)|].
  apply (rkk_img_wr W1 W3 mA mD a Hi). intros Hp. exact (ek_P24_img_xR a Hi Ho He (HAP12 a Hi Ho He Hp)).
Qed.

Lemma ek_wr3_xR : forall p nn a, In (p, nn) (ablocks B ly3 S3) -> p <= a < p + nn -> writable_at SEGS (arm W3 mD) a.
Proof.
  intros p nn a Hb Ha. unfold arm. apply apresent_writable.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar4_xR Hb) as (_ & _ & _ & _ & Hpres & _).
  pose proof (req_size_pos nn ltac:(lia)) as [_ Hr]. exact (proj1 (Hpres a ltac:(lia))).
Qed.

Lemma ek_V24_blk_xR : forall b a, In b (ablocks B ly2 S2) -> b <> ek_kb -> fst b <= a < fst b + snd b -> ~ ek_C1 a -> ~ ek_C2 a ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W2) mB a.
Proof.
  intros [p nn] a Hb Hne Ha N1 N2. cbn [fst snd] in Ha.
  destruct (rk_alb _ _ _ _ _ p nn ek_ar2_xR Hb) as (_ & H4 & Hc & _).
  pose proof (req_size_pos nn ltac:(lia)) as [_ Hr].
  pose proof ek_ceil_xR. pose proof asan_consts as (C1 & _).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  destruct HCK as (_ & K2 & _).
  pose proof (rk_blk_apart ly2 S2 W2 mB mdB (p, nn) _ ek_ar2_xR Hb ek_kb2_xR Hne) as Dk. cbn [fst snd] in Dk.
  replace a with (p + (a - p)) by lia.
  rewrite (K2 p nn (a - p) Hb ltac:(lia) ltac:(cbv beta; lia)).
  apply HK2; lia.
Qed.

Lemma ek_K24_blk_xR : forall b a, In b (ablocks B ly2 S2) -> b <> ek_kb -> fst b <= a < fst b + snd b -> ~ ek_C1 a -> ~ ek_C2 a ->
  abyte_kept W2 mB W3 mD a.
Proof.
  intros b a Hb Hne Ha N1 N2. split; [exact (ek_V24_blk_xR b a Hb Hne Ha N1 N2)|].
  intros _. destruct b as [p nn]. exact (ek_wr3_xR p nn a (ek_to3_xR _ Hb Hne) Ha).
Qed.

Lemma ek_V12_blk_xR : forall b a, In b (ablocks B ly1 S1) -> ~ In b (aout_blks cap2 out2) -> fst b <= a < fst b + snd b ->
  aview SEGS (w_H W2) mB a = aview SEGS (w_H W1) mA a.
Proof.
  intros [p nn] a Hb Ho Ha. cbn [fst snd] in Ha.
  destruct (ek_to2_xR _ Hb Ho) as [Hb2 _].
  pose proof (req_size_pos nn ltac:(lia)) as [_ Hr].
  replace a with (p + (a - p)) by lia.
  eapply rkk_jx_blk_xR; [exact rkk_gxSL | exact HJG | exact Hb | exact Hb2 | lia |].
  intros (r0 & Hr0 & Hx). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([q m] & <- & Hq). cbn [fst snd] in Hx.
  assert (Hne : (p, nn) <> (q, m)) by (intros E; rewrite E in Ho; exact (Ho Hq)).
  pose proof (rk_blk_apart ly1 S1 W1 mA mdA (p, nn) (q, m) ek_ar1_xR Hb (ek_out1_xR _ Hq) Hne) as D. cbn [fst snd] in D.
  lia.
Qed.

Lemma ek_K14_blk_xR : forall b a, In b (ablocks B ly1 S1) -> ~ In b (aout_blks cap2 out2) -> b <> ek_kb ->
  fst b <= a < fst b + snd b -> ~ ek_C1 a -> ~ ek_C2 a -> abyte_kept W1 mA W3 mD a.
Proof.
  intros b a Hb Ho Hne Ha N1 N2. destruct (ek_to2_xR b Hb Ho) as [Hb2 _].
  split; [rewrite (ek_V24_blk_xR b a Hb2 Hne Ha N1 N2); exact (ek_V12_blk_xR b a Hb Ho Ha)|].
  intros _. destruct b as [p nn]. exact (ek_wr3_xR p nn a (ek_to3_xR _ Hb2 Hne) Ha).
Qed.

Lemma ek_V14_hi_xR : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) mD a = aview SEGS (w_H W1) mA a.
Proof.
  intros a Ha. pose proof ek_ceil_xR. pose proof (rkk_bv cx) as Hb. assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  assert (HD : DRAIN_STK_x = 16976) by reflexivity. pose proof asan_consts as (C1 & _).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low_xR a (or_introl Hc)) as (Hl & _); lia).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low_xR a (or_intror Hc)) as (Hl & _); lia).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  destruct HCK as (K1 & _). rewrite (K1 a ltac:(lia) ltac:(lia)).
  rewrite (HK2 a ltac:(lia) ltac:(lia)).
  eapply rkk_jx_high_xR; [exact rkk_gxSL | exact HJG | lia | lia].
Qed.

Lemma ek_V14_fr_xR : forall a, (F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16) ->
  aview SEGS (w_H W3) mD a = aview SEGS (w_H W1) mA a.
Proof.
  intros a Ha. destruct ek_frame_xR as (Hfr1 & HFa1 & HF4 & HFc & Hoff & Hfr2 & HFa2 & _).
  pose proof ek_ceil_xR. pose proof asan_consts as (C1 & _ & C3 & _ & C5).
  assert (HF8 : 0 <= F / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hlo : 4096 <= a < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF in Ha; lia).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low_xR a (or_introl Hc)) as (_ & _ & Hn1 & Hn2); tauto).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low_xR a (or_intror Hc)) as (_ & _ & Hn1 & Hn2); tauto).
  rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
  assert (NK : ~ (key_addr ek_k <= a < key_addr ek_k + req_size (ek_xl + 1))).
  { intros Hk. destruct (ek_blk_loc_xR _ _ a (proj1 ek_kb1_xR) Hk) as (_ & _ & Hn1 & Hn2). tauto. }
  destruct HCK as (_ & _ & _ & K4 & _).
  rewrite (K4 1 fpos a Hfr2 ltac:(unfold frame_rng, in_zr; cbn [fst snd]; rewrite HFa2; change (fs_frame_bytes 1) with 128;
    change (128 / 8) with 16; tauto) NK).
  rewrite (HK2 a ltac:(lia) ltac:(lia)).
  eapply rkk_jx_frame_xR; [exact rkk_gxSL | exact HJG | exact Hfr1 | | | lia | ].
  - unfold frame_rng, in_zr; cbn [fst snd]; rewrite HFa1; change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; tauto.
  - intros (r0 & Hr0 & Hx). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([q m] & <- & Hq). cbn [fst snd] in Hx.
    destruct (ek_blk_loc_xR q m a (ek_out1_xR _ Hq) Hx) as (_ & _ & Hn1 & Hn2). tauto.
  - intros Hi. pose proof (pa_img_range a Hi). unfold off_img in Hoff. unfold shadow_addr, SHADOW_OFF in Ha. lia.
Qed.

(* ---- the memory facts at (ly3, S3, W3, mD) ---- *)
Lemma ek_gsK_xR : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 mA W3 mD a.
Proof.
  intros a Ha. destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps).
  exact (ek_K14_img_xR a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
Qed.

Lemma ek_asrc_xR : forall HA h, asrc_at B ly1 S1 W1 mA HA h ->
  (forall a, HA <= a < HA + ASRC -> rg_s RG <= a < rg_s RG + 4 * ASRC) ->
  (forall b, In b (asrc_blks h) -> In b ek_src) -> asrc_at B ly3 S3 W3 mD HA h.
Proof.
  intros HA h Hs HS HX.
  assert (HXP : forall b, In b (asrc_blks h) -> In b ek_P2) by (intros b Hb; right; apply in_or_app; right; exact (HX b Hb)).
  apply (asrc_at_kept B ly1 S1 W1 mA ly3 S3 W3 mD HA h Hs).
  - intros r0 Hr a Ha. destruct (rkk_asrc_loc _ _ _ _ HA h Hs r0 Hr a Ha) as [Hx | (b & Hb & Hx)].
    + exact (ek_gsK_xR a (HS a Hx)).
    + destruct (ek_inP2_xR b (HXP b Hb)) as (Hb1 & Ho & Hne).
      destruct (ek_src_ne_xR b (HX b Hb)) as [N1 N2].
      destruct ek_entry_xR as (HT & _ & _ & _ & _ & _ & HH & _).
      destruct (ek_cells_apart_xR ly1 S1 W1 mA mdA b a ek_ar1_xR HT HH Hb1 N1 N2 Hx) as [C1 C2].
      exact (ek_K14_blk_xR b a Hb1 Ho Hne Hx C1 C2).
  - intros b Hb. destruct (ek_inP2_xR b (HXP b Hb)) as (Hb1 & Ho & Hne).
    exact (ek_to3_xR b (proj1 (ek_to2_xR b Hb1 Ho)) Hne).
Qed.

Lemma ek_done_xR : forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
Proof.
  intros i' Hi' He. destruct ek_gin_xR as (G1 & G2 & _ & _ & _ & G11 & _).
  pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
  apply ek_asrc_xR; [exact (G11 i' Hi' He) | |].
  - pose proof (rkk_j4 cx i' HB ltac:(lia) He) as Hj. unfold gslot. intros a Ha. unfold ASRC in *. lia.
  - intros b Hb. apply in_or_app. left. unfold gdone_srcs. apply in_concat.
    exists (asrc_blks (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))). split; [|exact Hb].
    apply in_map_iff.
    exists (nth i' (combine (firstn i (gps cx)) qd) ((relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj),
      (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
    assert (Lf : length (firstn i (gps cx)) = i) by (rewrite length_firstn; unfold gps; rewrite length_combine; lia).
    split.
    + rewrite combine_nth by lia. cbv beta. cbn [fst snd].
      rewrite nth_firstn, (proj2 (Nat.ltb_lt i' i) Hi'). cbv beta iota.
      unfold gps. rewrite combine_nth by (symmetry; exact Hlen). cbn [fst].
      change (nth i' (gxes cx) relay_remove_b_c.no_entry) with (gnth cx i'). rewrite He. reflexivity.
    + apply nth_In. rewrite length_combine. lia.
Qed.

Lemma ek_open_src_xR : ek_open = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1.
Proof.
  intros Hop. destruct ek_gin_xR as (G1 & _ & _ & _ & _ & _ & G12 & _).
  apply ek_asrc_xR; [exact (G12 Hop) | |].
  - pose proof (rkk_j4 cx i HB G1 (proj1 (Z.eqb_eq _ _) Hop)) as Hj. unfold gslot. intros a Ha. unfold ASRC in *. lia.
  - intros b Hb. apply in_or_app. right. apply in_or_app. left. rewrite Hop. exact Hb.
Qed.

Lemma ek_drsrc_xR : Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)).
Proof.
  destruct ek_gin_xR as (_ & _ & _ & _ & _ & _ & _ & G13 & _).
  rewrite Forall_forall in G13 |- *. intros p Hp He.
  destruct (G13 p Hp He) as (Hj & Hs & Ho & Hrest).
  split; [exact Hj|]. split; [|split; [|exact Hrest]].
  - apply ek_asrc_xR; [exact Hs | |].
    + intros a Ha. unfold ASRC in *. lia.
    + intros b Hb. apply in_or_app. right. apply in_or_app. right. unfold rig_srcs. apply in_concat.
      exists (if re_eof (fst p) =? 0 then asrc_blks (fst (snd p)) else []). split.
      * apply (in_map (fun p => if re_eof (fst p) =? 0 then asrc_blks (fst (snd p)) else [])). exact Hp.
      * rewrite He. exact Hb.
  - intros i0 Hi0 Hne. destruct (Ho i0 Hi0 Hne) as (f0 & o & Hf & Hof & Hx). exists f0, o.
    split; [|split; [|exact Hx]].
    + apply (akept_vm W1 mA); [intros x Hx'; apply ek_gsK_xR; change (Z.of_nat 4) with 4 in Hx'; unfold ASRC in *; lia | exact Hf].
    + apply (akept_vm W1 mA); [intros x Hx'; apply ek_gsK_xR; change (Z.of_nat 4) with 4 in Hx'; unfold ASRC in *; lia | exact Hof].
Qed.

Lemma ek_gs_entry_xR : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
  (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
  abyte_kept (gxW cx) (gxmem cx) W3 mD a.
Proof.
  intros a Ha Hj. destruct ek_gin_xR as (_ & _ & _ & _ & _ & _ & _ & _ & G14 & _).
  exact (rkk_kept_trans _ _ _ _ _ _ a (G14 a Ha Hj) (ek_gsK_xR a Ha)).
Qed.

Lemma ek_fp_blk_xR : forall e' r0 a, In e' ek_es2 -> In r0 (aentry_fp e') -> fst r0 <= a < snd r0 ->
  exists b, In b (aentry_blks e') /\ fst b <= a < fst b + snd b.
Proof.
  intros e' r0 a He Hr Ha. destruct ek_gin_xR as (_ & _ & _ & G9 & _).
  destruct G9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _). rewrite Forall_forall in H10.
  apply in_app_or in He. destruct He as [He | [<- | He]].
  - exact (rkr_fp_blk _ _ _ _ e' (H10 e' ltac:(apply in_or_app; left; exact He)) r0 Hr a Ha).
  - apply (rkk_fp_blk_ks ly1 S1 W1 mA e1 ks ek_ks2 (H10 (entry_keys e1 ks) ltac:(apply in_or_app; right; left; reflexivity))
      ltac:(rewrite relay_instance_gone_b_lem.rigl_len_swap; lia) r0 Hr a Ha).
  - exact (rkr_fp_blk _ _ _ _ e' (H10 e' ltac:(apply in_or_app; right; right; exact He)) r0 Hr a Ha).
Qed.

Lemma ek_relay_xR : arelay_at B RG ly3 S3 W3 mD (gxG0 cx) ek_es2.
Proof.
  destruct ek_gin_xR as (G1 & G2 & G6 & G9 & _ & _ & _ & _ & _ & G15 & _).
  pose proof HB as HB'. destruct HB' as (_ & _ & _ & HPL & _).
  pose proof (rkr_arelay_swap ly1 S1 W1 mA mdA ly3 S3 W3 mD (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n
    (ek_src ++ aout_blks cap2 out2 ++ gxrest cx) ek_ar1_xR HPL G15 G9 ek_nlt_xR) as Rk.
  cbv zeta in Rk. rewrite length_map, G2 in Rk.
  apply Rk; [| |exact HNH | exact HSL].
  - intros b Hb. unfold arelay_blks in Hb.
    assert (HbP : In b ek_P2) by (destruct Hb as [<-|Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb]).
    destruct (ek_inP2_xR b HbP) as (Hb1 & Ho & Hne). exact (ek_to3_xR b (proj1 (ek_to2_xR b Hb1 Ho)) Hne).
  - intros r0 Hr a Ha N1 N2. unfold arelay_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|Hr]]]]; cbn [fst snd] in Ha.
    + destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img_xR a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
    + destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img_xR a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
    + destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img_xR a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
    + destruct (ek_inP2_xR ek_T (or_introl eq_refl)) as (Hb1 & Ho & Hne). exact (ek_K14_blk_xR ek_T a Hb1 Ho Hne Ha N1 N2).
    + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e' & <- & He').
      destruct (ek_fp_blk_xR e' r0 a He' Hr Ha) as (b & Hb & Hab).
      assert (HbP : In b ek_P2)
        by (right; apply in_or_app; left; apply in_concat; exists (aentry_blks e'); split; [apply in_map; exact He' | exact Hb]).
      destruct (ek_inP2_xR b HbP) as (Hb1 & Ho & Hne). exact (ek_K14_blk_xR b a Hb1 Ho Hne Hab N1 N2).
Qed.

(* the output, from gesture_end's post *)
Lemma ek_K24_err_xR : forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W2 mB W3 mD a.
Proof.
  intros a Ha. destruct (HGRIG a (rkk_errno_G a Ha)) as [Hi _].
  pose proof (rkk_img a Hi) as Hl. pose proof ek_ceil_xR. pose proof asan_consts as (C1 & _).
  assert (N1 : ~ ek_C1 a) by (intros Hc; destruct (ek_cells_low_xR a (or_introl Hc)) as (_ & Hn & _); exact (Hn Hi)).
  assert (N2 : ~ ek_C2 a) by (intros Hc; destruct (ek_cells_low_xR a (or_intror Hc)) as (_ & Hn & _); exact (Hn Hi)).
  assert (V : aview SEGS (w_H W3) mD a = aview SEGS (w_H W2) mB a).
  { rewrite (HK3 a ltac:(lia) ltac:(lia) N1 N2).
    replace a with (as_errno B + (a - as_errno B)) by lia. rewrite (HERR (a - as_errno B) ltac:(lia)).
    apply HK2; lia. }
  split; [exact V|]. intros _.
  pose proof HO2 as HO.
  destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H17 & _).
  pose proof (rkk_vm_some _ _ _ _ _ a H17 ltac:(change (Z.of_nat 4) with 4; lia)) as Hs.
  destruct (aview SEGS (w_H W2) mB a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
  unfold arm. apply (rkk_view_wr (w_H W3) mD a v ltac:(lia) V).
  intros Hrom. destruct (HROMO a Hrom) as [HnG _]. exact (HnG (rkk_errno_G a Ha)).
Qed.

Lemma ek_TH2_xR : In ek_T (ablocks B ly2 S2) /\ ~ In ek_T (aout_blks ek_cap2 out2') /\
  In ek_H (ablocks B ly2 S2) /\ ~ In ek_H (aout_blks ek_cap2 out2') /\ ~ In ek_kb (aout_blks ek_cap2 out2').
Proof.
  destruct (ek_inP2_xR ek_T (or_introl eq_refl)) as (T1 & TO & _).
  destruct (ek_inP2_xR ek_H ltac:(right; apply in_or_app; left; exact ek_H_in_xR)) as (H1 & HO & _).
  destruct ek_kb1_xR as [K1 KO].
  destruct (ek_to2_xR _ T1 TO) as [T2 TO2]. destruct (ek_to2_xR _ H1 HO) as [H2 HO2']. destruct (ek_to2_xR _ K1 KO) as [_ KO2].
  split; [exact T2|]. split; [exact TO2|]. split; [exact H2|]. split; [exact HO2' | exact KO2].
Qed.

Lemma ek_out_xR : aout_at B RG ly3 S3 W3 mD ek_c2 ek_O2 (gxmx cx) (Z.of_nat (length ek_O2)) ek_cap2 out2'.
Proof.
  pose proof HO2 as HO.
  assert (EN : Z.of_nat (length ek_O2) = ge_no c2 ek_no2 ek_xl).
  { destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EN & _).
    exact EN. }
  rewrite EN.
  destruct ek_TH2_xR as (T2 & TO2 & H2 & HO2' & KO2).
  apply (aout_at_kept B RG ly2 S2 W2 mB ly3 S3 W3 mD _ _ _ _ _ _ HO).
  - intros r0 Hr a Ha. unfold aout_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Ha;
      try (destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & _); exact (ek_K24_img_xR a Hi Ho He)).
    + exact (ek_K24_err_xR a Ha).
    + destruct (ek_cap2 =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
      assert (Hb : In (out2', ek_cap2) (aout_blks ek_cap2 out2')) by (unfold aout_blks; rewrite Ec; left; reflexivity).
      pose proof (ek_outB_xR _ Hb) as Hb2.
      assert (NK : (out2', ek_cap2) <> ek_kb) by (intros E; rewrite E in Hb; exact (KO2 Hb)).
      assert (NT : (out2', ek_cap2) <> ek_T) by (intros E; rewrite E in Hb; exact (TO2 Hb)).
      assert (NH : (out2', ek_cap2) <> ek_H) by (intros E; rewrite E in Hb; exact (HO2' Hb)).
      destruct (ek_cells_apart_xR ly2 S2 W2 mB mdB (out2', ek_cap2) a ek_ar2_xR T2 H2 Hb2 NT NH Ha) as [N1 N2].
      exact (ek_K24_blk_xR (out2', ek_cap2) a Hb2 NK Ha N1 N2).
  - intros b Hb. apply (ek_to3_xR b (ek_outB_xR b Hb)). intros E. rewrite E in Hb. exact (KO2 Hb).
Qed.

(* the frame, the lock, the slots, the views *)
Lemma ek_frame3_xR : g_frame cx fpos F FL ly3 W3 mD.
Proof.
  destruct ek_frame_xR as (_ & _ & HF4 & HFc & _ & _ & _ & HFa3 & HFl3).
  pose proof HF1 as HF1'. destruct HF1' as (_ & _ & H120 & H16 & H24 & H80 & Hsv).
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  assert (VH : forall a n0 v, gsp1 cx <= a -> a + Z.of_nat n0 <= gsp0 cx ->
    val_mem SEGS (arm W1 mA) a n0 v -> val_mem SEGS (arm W3 mD) a n0 v)
    by (intros a n0 v Hl Hh Hv; apply (rkk_vm_v W1 W3 mA mD); [intros x Hx; apply ek_V14_hi_xR; lia | exact Hv]).
  split; [exact HFa3|]. split; [exact HFl3|].
  split; [apply (rkk_vm_v W1 W3 mA mD); [intros x Hx; apply ek_V14_fr_xR; change (Z.of_nat 8) with 8 in Hx; lia | exact H120]|].
  split; [apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact H16]|].
  split; [apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact H24]|].
  split; [apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact H80]|].
  intros j Hj. apply VH; [lia | change (Z.of_nat 8) with 8; lia | exact (Hsv j Hj)].
Qed.

Lemma ek_lock3_xR : alock_at RG W3 mD true.
Proof.
  apply (alock_at_kept RG W1 mA W3 mD true HL1). intros r0 Hr a Ha. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
  destruct (rkk_cellP cx a HB ltac:(tauto)) as (Hi & Ho & He & Hps). exact (ek_K14_img_xR a Hi Ho He Hps (rkk_not_SL a ltac:(tauto))).
Qed.

Lemma ek_VH8_xR : forall a v, gsp1 cx <= a -> a + 8 <= gsp0 cx -> val_mem SEGS (arm W1 mA) a 8 v -> val_mem SEGS (arm W3 mD) a 8 v.
Proof.
  intros a v Hl Hh Hv. apply (rkk_vm_v W1 W3 mA mD); [|exact Hv].
  intros x Hx. apply ek_V14_hi_xR. change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

Lemma ek_lslots3_xR : g_lslots RG cx F W3 mD.
Proof.
  pose proof HLS1 as HLS. destruct HLS as (H40 & H48 & H56 & H64 & H72). assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  split; [apply ek_VH8_xR; [lia | lia | exact H40]|].
  split; [apply ek_VH8_xR; [lia | lia | exact H48]|].
  split; [apply ek_VH8_xR; [lia | lia | exact H56]|].
  split; [apply ek_VH8_xR; [lia | lia | exact H64] | apply ek_VH8_xR; [lia | lia | exact H72]].
Qed.

Lemma ek_rom3_xR : rom_view SEGS W3 mD.
Proof.
  pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrv & _).
  eapply (ajournal_gx_rom_view_xR SEGS B PST ARx).
  all: first [exact LAWS | exact pa_segs_low | exact HJ3 | exact HROMO | exact PSTR | exact Hrv].
Qed.

Lemma ek_apres3_xR : apres_kept B (gxW cx) (gxmem cx) W3 mD.
Proof. intros a Hi Ho He Hp. exact (ek_P24_img_xR a Hi Ho He (HAP12 a Hi Ho He (HAP1 a Hi Ho He Hp))). Qed.

Lemma ek_pre3_xR : garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]).
Proof.
  destruct ek_gin_xR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G16 & _).
  apply (rkk_garr8_v W1 W3 mA mD); [|exact G16].
  intros x Hx. apply ek_V14_fr_xR. left. pose proof (rkk_pre_len cx). rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma ek_sh3_xR : garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
  destruct ek_gin_xR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G17).
  apply (rkk_garr8_v W1 W3 mA mD); [|exact G17].
  intros x Hx. apply ek_V14_fr_xR. right. cbn [length] in Hx. lia.
Qed.

Lemma ek_all_xR :
  arelay_at B RG ly3 S3 W3 mD (gxG0 cx) ek_es2 /\
  aout_at B RG ly3 S3 W3 mD ek_c2 ek_O2 (gxmx cx) (Z.of_nat (length ek_O2)) ek_cap2 out2' /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  (ek_open = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p))) (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 mD a) /\
  garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] /\
  rom_view SEGS W3 mD /\ apres_kept B (gxW cx) (gxmem cx) W3 mD /\
  g_frame cx fpos F FL ly3 W3 mD /\ alock_at RG W3 mD true /\ g_lslots RG cx F W3 mD /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 32) 8 ((ek_SA + 48) mod 8 + 3) /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 88) 8 (Z.of_nat i).
Proof.
  split; [exact ek_relay_xR|]. split; [exact ek_out_xR|]. split; [exact ek_done_xR|]. split; [exact ek_open_src_xR|].
  split; [exact ek_drsrc_xR|]. split; [exact ek_gs_entry_xR|]. split; [exact ek_pre3_xR|]. split; [exact ek_sh3_xR|].
  split; [exact ek_rom3_xR|]. split; [exact ek_apres3_xR|]. split; [exact ek_frame3_xR|]. split; [exact ek_lock3_xR|].
  split; [exact ek_lslots3_xR|].
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  split; [apply ek_VH8_xR; [lia | lia | exact H32] | apply ek_VH8_xR; [lia | lia | exact H88]].
Qed.
End eR.
(* W_rig_key.v:4693 rkk_end_mem at R *)
Theorem rkk_end_mem_xR : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 mA mdA kA ly2 S2 W2 mB mdB kB out2' mB' ly3 S3 W3 mC mdC l1 l2 slo shi mD mdD kD,
  let d0 : Z * list byte * list byte := (0, [], []) in
  let k := nth n ks d0 in
  let kt := key_text k in
  let xl := Z.of_nat (length kt) in
  let ks' := swap_remove d0 n ks in
  let SA := gSA cx i in
  let hp := re_hp e1 in
  let no2 := Z.of_nat (length O2) in
  let c2' := ge_ctl c2 xl in
  let O2' := ge_O c2 O2 kt in
  let cap2' := ge_cap c2 (gxmx cx) no2 cap2 xl in
  let kl := nth (length ks - 1) ks d0 in
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx)
    [(1, fpos)] ly1 S1 [] W1 mA mdA kA ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 mA ->
  rom_view SEGS W1 mA -> apres_kept B (gxW cx) (gxmem cx) W1 mA ->
  g_frame cx fpos F FL ly1 W1 mA -> alock_at RG W1 mA true -> g_lslots RG cx F W1 mA ->
  val_mem SEGS (arm W1 mA) (gsp1 cx + 32) 8 ((SA + 48) mod 8 + 3) ->
  val_mem SEGS (arm W1 mA) (gsp1 cx + 88) 8 (Z.of_nat i) ->
  has_prefix (gpre cx) (bzs kt) = true ->
  (* gesture_end's post *)
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (gsp1 cx) (ablocks_fp (aout_blks cap2 out2))
    ly1 S1 [] W1 mA mdA [] ly2 S2 [] W2 mB mdB kB ->
  apres_kept B W1 mA W2 mB ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks cap2 out2 ++ rest) /\
     Permutation (ablocks B ly2 S2) (aout_blks cap2' out2' ++ rest)) ->
  aout_at B RG ly2 S2 W2 mB c2' O2' (gxmx cx) (ge_no c2 no2 xl) cap2' out2' ->
  (* the stretch to the free call: only the stack window below gsp1 changes *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> aview SEGS (w_H W2) mB' a = aview SEGS (w_H W2) mB a) ->
  (forall a, apresent (w_H W2) mB a -> apresent (w_H W2) mB' a) ->
  (* free's post (afree_cf_rule's conjuncts) *)
  ARh ly3 S3 W3 mC mdC ->
  ablocks B ly2 S2 = l1 ++ (key_addr k, xl + 1) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 -> frames S3 = frames S2 ->
  acall_kept SEGS B ly2 S2 W2 mB' W3 mC slo shi (fun a => key_addr k <= a < key_addr k + req_size (xl + 1)) ->
  gsp1 cx - DRAIN_STK_x <= slo -> shi <= gsp1 cx ->
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W3) mC (as_errno B + j) = aview SEGS (w_H W2) mB' (as_errno B + j)) ->
  (forall a, in_img SEGS a -> ~ aowned B ly2 S2 a -> ~ aowned B ly3 S3 a -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (key_addr k <= a < key_addr k + req_size (xl + 1)) -> apresent (w_H W2) mB' a -> apresent (w_H W3) mC a) ->
  (* the stores: everything else outside the stack window kept, the two cells written *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ (SA + 48 <= a < SA + 52) ->
     ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) mD a = aview SEGS (w_H W3) mC a) ->
  (forall a, apresent (w_H W3) mC a -> apresent (w_H W3) mD a) ->
  val_mem SEGS (arm W3 mD) (SA + 48) 4 (Z.of_nat (length ks')) ->
  val_mem SEGS (arm W3 mD) (hp + 8 * Z.of_nat n) 8 (key_addr kl) ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx)
    [(1, fpos)] ly3 S3 [] W3 mD mdD kD ->
  arelay_at B RG ly3 S3 W3 mD (gxG0 cx) (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)) /\
  aout_at B RG ly3 S3 W3 mD c2' O2' (gxmx cx) (Z.of_nat (length O2')) cap2' out2' /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 mD (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 mD (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 mD (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) ->
        ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 mD a) /\
  garr8 SEGS (arm W3 mD) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 mD) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] /\
  rom_view SEGS W3 mD /\ apres_kept B (gxW cx) (gxmem cx) W3 mD /\
  g_frame cx fpos F FL ly3 W3 mD /\ alock_at RG W3 mD true /\ g_lslots RG cx F W3 mD /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 32) 8 ((SA + 48) mod 8 + 3) /\
  val_mem SEGS (arm W3 mD) (gsp1 cx + 88) 8 (Z.of_nat i).
Proof.
  intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 mA mdA kA ly2 S2 W2 mB mdB kB out2' mB' ly3 S3 W3 mC mdC l1 l2 slo shi mD mdD kD. cbv zeta.
  intros HB HJ1 HG _ HAP1 HF1 HL1 HLS1 H32 H88 _ HJG HAP12 HPG HO2 HK2 HP2 HAR3 HL2 HL3 _ HCK _ Hshi HERR HAPF HK3 HP3
    HNH HSL HJ3.
  exact (ek_all_xR cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 mA mdA kA ly2 S2 W2 mB mB' mdB kB out2' ly3 S3 W3 mC mD mdC mdD kD l1 l2 slo shi
    HB HJ1 HG HAP1 HF1 HL1 HLS1 H32 H88 HJG HAP12 HPG HO2 HK2 HP2 HAR3 HL2 HL3 HCK Hshi HERR HAPF HK3 HP3 HNH HSL HJ3).
Qed.
(* W_rig_key.v:4769 rig_key_proof at R *)
Theorem rig_key_proof_xR : rig_key_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
unfold rig_key_stmt_xR. intros cx i n r W1 c1 HB HC HI KP KE KR.
destruct HI as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 &
  ks & Ed & f & c2 & O2 & cap2 & out2 & spent & -> & HRB & R19 & R20 & R21 & R23 & R22 & R24 & R25 & R27 & M32 & M88 &
  HLV & HLS & HGN).
pose proof HLV as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
assert (EHp1 : Hp1 = []) by (eapply rk_jhp0_xR; exact HJ). subst Hp1.
pose proof HB as (HPRE0 & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof (rk_gxHp cx HB) as EHp0. rewrite EHp0 in HJ, HPRE0.
pose proof HJ as HJ0.
pose proof HGN as (Hi & Hqd & HREL & HDR & HSND & Hks & Hf & HGK & HRLY & HOUT & HSRC & HOPEN & HDRS & HGS & HPERM &
  HPRE & HPSH & HBUD).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof HJ as (HSTK & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SP1 : spZ regs1 = gsp0 cx - 224) by (rewrite Hsp1; reflexivity).
assert (SPR : alloc_ceiling + 12880 <= gsp0 cx - 4320 /\ gsp0 cx <= 2 ^ 47) by (unfold gsp0 in *; rewrite WS in Hslo; lia).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkr_entry_at ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n HAR1 HRLY Hn) as X.
cbv zeta in X. rewrite length_map, Hqd in X. fold (gSA cx i) in X.
destruct X as (HinT & HT16 & HT4096 & HTceil & HTend & Mhp & Mnh & AWT & Hhp0 & Hinh & Hkh & Ghp & AWH & Mslot & Hink &
  Gk & NZk & Lk & Hks26 & NDk).
set (k := nth n ks (0, [], [])) in *.
set (hp := re_hp e1) in *. set (key := key_addr k) in *. set (kt := key_text k) in *.
destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 Hink) as (Hk16 & Hk4096 & Hkceil & Hkapp & Hkpres & _ & _).
destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 HinT) as (_ & _ & _ & HTapp & HTpres & _ & _).
pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [Hrk1 Hrk2].
pose proof (req_size_pos (Z.of_nat (length kt) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (rk_ablocks_nodup _ _ _ _ _ HAR1) as HND1.
pose proof (Permutation_NoDup HPERM HND1) as HNDP.
assert (HinHP : In (hp, re_kh e1) (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))))).
{ apply in_concat. exists (aentry_blks (entry_keys e1 ks)). split.
  - apply in_map. apply in_or_app. right. left. reflexivity.
  - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
    fold hp. destruct (Z.eqb_spec hp 0); [contradiction | left; reflexivity]. }
assert (HTH : (gxG0 cx, ATABLE) <> (hp, re_kh e1)).
{ apply List.NoDup_cons_iff in HNDP. intros Heq.
  apply (proj1 HNDP). rewrite Heq. apply in_or_app. left. exact HinHP. }
pose proof (rk_blk_apart ly1 S1 W1 m1 md1 _ _ HAR1 HinT Hinh HTH) as HTHd. cbn [fst snd] in HTHd.
change (req_size ATABLE) with 896 in HTHd.
assert (HSA : gSA cx i = gxG0 cx + 56 * Z.of_nat i) by reflexivity.
assert (DSH : hp + 8 * Z.of_nat n + 8 <= gSA cx i + 40 \/ gSA cx i + 52 <= hp + 8 * Z.of_nat n)
  by (clear - HTHd HTend HSA Hkh Hrk2 Hn; unfold AENT, ATABLE in *; lia).
pose proof (rk_entry_st W1 ly1 S1 regs1 m1 md1 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
  (Z.of_nat (length ks)) key HAR1 Hsp1 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
  ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32)
  H18 R19 R21 R23 R22 R25 R27 HinT ltac:(clear - HSA; lia) HTend
  ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
  Hinh Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)
  DSH Mhp Mnh (Mslot n Hn)) as [HS SHOK].
clear DSH.
unfold cfg_at. change (w64 (BASE + A_rig_inner)) with (Z_to_bv 64 (BASE + A_rig_inner)).
remember (Eimg (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk0; subst E; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (HAE : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)))) E)
  by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
(* the frame (1, fpos) *)
pose proof HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (rk_alf _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (rk_fb _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in *.
assert (HF8 : 0 <= F / 8 /\ 8 * (F / 8) <= F).
{ split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
(* the three blocks, pairwise apart, and apart from F *)
destruct (rk_perm_entry _ _ _ (map fst qd) (entry_keys e1 ks) (skipn (S i) (gxes cx)) _ k HND1 HPERM
  ltac:(cbn [re_hp entry_keys]; exact Hhp0) ltac:(cbn [re_keys entry_keys]; apply nth_In; exact Hn)) as (NE1 & NE2 & NE3).
cbn [re_hp re_kh entry_keys] in NE1, NE2, NE3. fold hp key kt in NE1, NE2, NE3.
pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 HinT Hink NE2) as DTK. cbn [fst snd] in DTK.
pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 Hinh Hink NE3) as DHK. cbn [fst snd] in DHK.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin HinT) as DFT.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin Hinh) as DFH.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin Hink) as DFK.
change (fs_frame_bytes 1) with 128 in DFT, DFH, DFK. rewrite HFa in DFT, DFH, DFK.
change (req_size ATABLE) with 896 in DTK, DFT.
set (XG := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
  rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap2 out2).
assert (HPX : Permutation (ablocks B ly1 S1) (XG ++ gxrest cx)) by (unfold XG; rewrite <- app_comm_cons, <- !app_assoc; exact HPERM).
assert (HP0X : Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx))
  by (unfold rk_X0; rewrite <- app_comm_cons, <- !app_assoc; exact HPERM0).
paj_run_tok_xR RUNG HS HJ SHOK rk_Bspan.
{ apply (rk_awr_k E _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
  - rewrite (EE 23%nat 23%bv eq_refl), R23. apply unsigned_lit_small. unfold AENT, ATABLE in *. lia.
  - rewrite E33. apply unsigned_lit_small. lia.
  - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 m1 md1 XG _ (gxG0 cx) ATABLE a HAR1 HP0X HPX).
    + left. reflexivity.
    + change (req_size ATABLE) with 896. unfold AENT, ATABLE in *. lia.
  - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 m1 md1 XG _ hp (re_kh e1) a HAR1 HP0X HPX).
    + right. apply in_or_app. left. exact HinHP.
    + lia. }
(* ---- the call strncmp (key, F + 32, |prefix|) at 0x82e80 ---- *)
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2.
assert (BV23 : base_val E (Some 23%nat) = gSA cx i + 48)
  by (cbn [base_val]; rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
assert (BV25 : base_val E (Some 25%nat) = gSA cx i + 40)
  by (cbn [base_val]; rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
assert (BV33 : base_val E (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (M01 : forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
  ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha H1 H2. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms0) HFr0 a Ha).
  intros (r0 & Hin & Hr). cbn [ss_mem ss_k rk_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
  rewrite ?BV23, ?BV25, ?BV33 in Hr; lia. }
assert (P01 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; eapply apresent_grows; [exact HG0 | exact Hp]).
assert (HSPc : spZ (ms_regs ms0) = gsp0 cx + -224).
{ unfold spZ at 1. rewrite QSP, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). lia. }
pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
destruct (rkr_pre_nz cx) as (NZp & Lp16 & Lp27).
assert (OUTW : forall a, (key <= a < key + req_size (Z.of_nat (length kt) + 1) \/ F <= a < F + 128) ->
  ~ (gSA cx i + 48 <= a < gSA cx i + 52) /\ ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8)).
{ clear - DTK DHK DFT DFH HTHd HTend HSA Hkh Hrk2 Hn. intros a Ha. unfold AENT, ATABLE in *. split; lia. }
clear DTK DHK DFT DFH DFK HTHd.
assert (GkT : garr8 SEGS (arm W1 (ms_mem ms0)) key (bzs (kt ++ [Z_to_bv 8 0]))).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ Gk). intros b Hb.
  unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
  destruct (OUTW b ltac:(lia)) as [Ow1 Ow2]. apply M01; [lia | exact Ow1 | exact Ow2]. }
assert (GpT : garr8 SEGS (arm W1 (ms_mem ms0)) (F + 32) (gpre cx ++ [0])).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ HPRE). intros b Hb.
  rewrite length_app in Hb. cbn [length] in Hb.
  destruct (OUTW b ltac:(lia)) as [Ow1 Ow2]. apply M01; [lia | exact Ow1 | exact Ow2]. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 key) by (rewrite QA0, E34; reflexivity).
assert (QA1' : getr (ms_regs ms0) 11 = w64 (F + 32)) by (rewrite QA1, (EE 20%nat 20%bv eq_refl); exact R20).
assert (QA2' : getr (ms_regs ms0) 12 = w64 (Z.of_nat (length (gpre cx)))) by (rewrite QA2, (EE 24%nat 24%bv eq_refl); exact R24).
assert (LKT : length (bzs (kt ++ [Z_to_bv 8 0])) = (length kt + 1)%nat) by (unfold bzs; rewrite length_map, length_app; reflexivity).
assert (LPT : length (gpre cx ++ [0]) = (length (gpre cx) + 1)%nat) by (rewrite length_app; reflexivity).
(* the key's and the prefix's bytes are visible *)
assert (VK : forall a, key <= a < key + Z.of_nat (length kt) + 1 -> aview SEGS (w_H W1) (ms_mem ms0) a <> None).
{ intros a Ha. replace a with (key + (a - key)) by lia. apply (rk_view_garr8 (w_H W1) (ms_mem ms0) key _ (a - key) GkT).
  rewrite LKT. lia. }
assert (VP : forall a, F + 32 <= a < F + 32 + Z.of_nat (length (gpre cx)) + 1 -> aview SEGS (w_H W1) (ms_mem ms0) a <> None).
{ intros a Ha. replace a with (F + 32 + (a - (F + 32))) by lia. apply (rk_view_garr8 (w_H W1) (ms_mem ms0) (F + 32) _ (a - (F + 32)) GpT).
  rewrite LPT. lia. }
assert (PSHT : garr8 SEGS (arm W1 (ms_mem ms0)) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ HPSH). intros b Hb. cbn [length] in Hb.
  apply M01; [clear - Hb HF8 HFceil C1; unfold shadow_addr, SHADOW_OFF in *; lia | |].
  - clear - Hb HTapp HTend HSA HFceil HF8 C1 C3. unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT, ATABLE in *.
    change (req_size 896) with 896 in HTapp. lia.
  - clear - Hb Hhapp Hkh Hrk2 Hn HFceil HF8 C1 C3. unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RIG B RG) 0 [] (2 * ESTACK) (SIGMA WS_strncmp) (fun _ => False)
    (fun (regs' : bvmap 5 word) (_ : word -> option byte) =>
       getr regs' 10 = w64 0 <-> astrn_agree W1 (ms_mem ms0) key (F + 32) (Z.of_nat (length (gpre cx))))
    W1 _ _ RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) _ _ _ _ _ _ (-224) _ HGRIG eq_refl HJ).
  - exact HSPc.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl), Hgp1. exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl), Htp1. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. right. intros [].
  - intros a [].
  - intros a [].
  - intros HPRE2 HSC.
    apply (ASTRNCMP _ _ _ _ _ _ _ key (F + 32) (Z.of_nat (length (gpre cx)))
      (Z.min (Z.of_nat (length kt)) (Z.of_nat (length (gpre cx)))) (Z.of_nat (length (gpre cx))) HPRE2 HSC QA0' QA1' QA2').
    + lia.
    + lia.
    + lia.
    + lia.
    + exact (rkr_first_key W1 (ms_mem ms0) key kt (Z.of_nat (length (gpre cx))) ltac:(lia) GkT NZk).
    + exact (rkr_first_pre W1 (ms_mem ms0) (F + 32) (gpre cx) GpT NZp).
    + clear - Hkceil Hrq2 C1. unfold alloc_ceiling in *. lia.
    + clear - HFceil C1 Lp27. unfold alloc_ceiling in *. lia.
    + intros a Ha. split; [apply VK; lia | rewrite HSPc; clear - Ha Hkceil Hrq2 SPR; unfold ESTACK; lia].
    + intros a Ha. split; [apply VP; lia | rewrite HSPc; clear - Ha HFceil Lp27 SPR; unfold ESTACK; lia].
    + split; [|split].
      * eapply (rk_amr ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2; lia].
      * eapply (rk_rab ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2; lia].
      * intros _. eapply (rk_shv ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1));
        [exact HAR2 | exact Hink | lia | clear - Hrq2; lia | clear - Lk Lp16; lia].
    + replace (Z.min (Z.of_nat (length (gpre cx))) (Z.of_nat (length (gpre cx)) + 1)) with (Z.of_nat (length (gpre cx))) by lia.
      split; [|split].
      * clear - HFapp C1 C4 C5 Lp27. unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
      * intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
        assert (Ex : x / 8 = F / 8 + 4 + (x - F - 32) / 8).
        { clear - HFal Hx. pose proof (Z.div_mod F 32 ltac:(lia)) as D0. rewrite HFal, Z.add_0_r in D0.
          set (t := F / 32) in *.
          assert (E0 : F / 8 = 4 * t) by (rewrite D0; replace (32 * t) with ((4 * t) * 8) by lia; apply Z.div_mul; lia).
          rewrite E0. replace x with ((x - F - 32) + (4 * t + 4) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
        assert (Hj : 0 <= (x - F - 32) / 8 < 6).
        { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
        pose proof (rk_garr8_aview (w_H W1) (ms_mem ms0) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]
          (Z.to_nat ((x - F - 32) / 8)) PSHT ltac:(cbn [length]; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. unfold shadow_addr in Hv. rewrite Ex. replace (SHADOW_OFF + (F / 8 + 4 + (x - F - 32) / 8)) with (SHADOW_OFF + F / 8 + 4 + (x - F - 32) / 8) by lia.
        rewrite Hv. f_equal. generalize (Z.to_nat ((x - F - 32) / 8)). intros j. destruct j as [|[|[|[|[|[|j]]]]]]; try reflexivity. destruct j; reflexivity.
      * intros _ sx Hsx. pose proof (rk_hull F (Z.of_nat (length (gpre cx))) sx HFal ltac:(lia) Hsx) as Hs'.
        apply aview_some_of_apresent. apply P01. replace sx with (shadow_addr F + (sx - shadow_addr F)) by lia.
        exact (proj1 (HFSpres (sx - shadow_addr F) ltac:(lia))).
    + intros a Hin.
      assert (Hii : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
      pose proof (Hsegs a Hii) as Ha. rewrite M01; [exact (HROM1 a Hin) | clear - Ha C5; unfold kLowMemEnd in *; lia | |].
      * intros Hx. apply (rk_blk_not_img _ _ _ _ _ _ _ a HAR1 HinT); [|exact Hii].
        change (req_size ATABLE) with 896. clear - Hx HTend HSA. unfold AENT, ATABLE in *. lia.
      * intros Hx. apply (rk_blk_not_img _ _ _ _ _ _ _ a HAR1 Hinh); [|exact Hii]. clear - Hx Hkh Hrk2 Hn. lia.
    + split.
      * eapply (rk_amr ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2 Lk; lia].
      * clear - HFapp C1 C4 C5. unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
cbv beta. intros W2 c2x _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HA0 & Hfr2 & Hpres2).
(* ---- back at 0x82e84: a0 = strncmp's result ---- *)
pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
destruct (rk_alb ly1 S1 W1 mem2 _ _ _ HAR3 HinT) as (_ & _ & _ & _ & HTpres3 & _ & _).
destruct (rk_alb ly1 S1 W1 mem2 _ _ _ HAR3 Hinh) as (_ & _ & _ & _ & Hhpres3 & _ & _).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV23, ?BV25, ?BV33;
   [ intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr2;
     [ clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold AENT, ATABLE, alloc_ceiling in *; lia
     | exact (fun H => H)
     | clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn SPR; unfold AENT, ATABLE, ESTACK in *; lia ]
   | intros a Ha _; apply (apresent_writable SEGS);
     first [ apply (HTpres3 a); clear - Ha HTend HSA; change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia
           | apply (Hhpres3 a); clear - Ha Hkh Hrk2 Hn; lia
           | lia ] ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall k0, (k0 < 36)%nat -> ew Ea k0 = ew E k0) by (intros k0 Hk0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hk0).
assert (HAEa : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)))) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOKa : sh_ok SEGS rk_Bx rk_SH Ea (mrestrict (w_H W1) mem2)).
{ apply (rk_shok Ea W1 ly1 S1 mem2 _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HAR3).
  - rewrite OLDa by lia. rewrite (EE 18%nat 18%bv eq_refl). exact H18.
  - rewrite OLDa by lia. rewrite (EE 23%nat 23%bv eq_refl). exact R23.
  - rewrite OLDa by lia. rewrite (EE 25%nat 25%bv eq_refl). exact R25.
  - rewrite OLDa by lia. exact E33.
  - exact HinT.
  - clear - HSA. lia.
  - exact HTend.
  - exact Hinh.
  - exact Hkh.
  - clear - Hn. lia. }
prreg HS (10%bv : bv 5) R10a.
assert (BVa : forall k0, (k0 < 36)%nat -> base_val Ea (Some k0) = base_val E (Some k0))
    by (intros k0 Hk0; cbn [base_val]; rewrite OLDa by exact Hk0; reflexivity).
  assert (NWIN : forall (Wx : world SEGS) E' ss' (mA mB : word -> option byte), (forall k0, (k0 < 36)%nat -> base_val E' (Some k0) = base_val E (Some k0)) ->
    frame_of E' (ss_mem ss') (mrestrict (w_H Wx) mA) (mrestrict (w_H Wx) mB) -> ss_mem ss' = rk_regions ->
    forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) -> ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) ->
    aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a).
  { intros Wx E' ss' mA mB HBV HFrx Hm a Ha H1 H2. apply (aview_kept_out E' _ (w_H Wx) mA mB HFrx a Ha).
    rewrite Hm. intros (r0 & Hin & Hr). cbn [rk_regions In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    rewrite ?HBV in Hr by lia; rewrite ?BV23, ?BV25, ?BV33 in Hr; lia. }
  assert (GR : forall k0 (r0 : bv 5), (k0 < 36)%nat -> Z.of_nat k0 = bv_unsigned r0 -> ew Ea k0 = getr regs1 r0)
    by (intros k0 r0 Hk0 Hr0; rewrite OLDa by exact Hk0; apply EE; exact Hr0).
psrr_branch_tok RUNG BRR HS SHOKa rk_Bspan.
- (* ======== a0 <> 0: the key lacks the prefix (pass) ======== *)
  assert (Ha0ne : getr regs2 10 <> w64 0).
  { intros Hz. rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia.
    rewrite (U_atom Ea 40 0) in Hc; [discriminate Hc | rewrite <- R10a; exact Hz | lia]. }
  assert (HPF : has_prefix (gpre cx) (bzs kt) = false).
  { destruct (has_prefix (gpre cx) (bzs kt)) eqn:Hh; [exfalso|reflexivity].
    apply (proj2 (rkr_agree W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp)) in Hh.
    exact (Ha0ne (proj2 HA0 Hh)). }
  paj_run_tok_xR RUNG HS HJ2 SHOKa rk_Bspan.
  { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
      + left. reflexivity.
      + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
      + right. apply in_or_app. left. exact HinHP.
      + clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
    psrr_branch_tok RUNG BRR HS SHOKa rk_Bspan.
  + (* n + 1 < nheld: the next key *)
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa rk_Bspan A_rig_inner.
    { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
      - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
        + left. reflexivity.
        + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
        + right. apply in_or_app. left. exact HinHP.
        + clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    assert (Hn1 : (S n < length ks)%nat).
    { rewrite (rk_branch_lt Ea (SOff 21 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_lt in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 21%nat 21%bv eq_refl), R21 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    destruct r as [|r']; [exfalso; lia|].
    destruct (rk_win_vals Ea _ ms2 W1 (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key HS eq_refl
      ltac:(rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
      ltac:(rewrite OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
      ltac:(rewrite OLDa by lia; exact E35) ltac:(rewrite OLDa by lia; exact E34)
      ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as [VNf VKf].
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { apply (rk_keep_join cx W1 m1 (ms_mem ms2) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact Mnh | exact VNf | exact (Mslot n Hn) | exact VKf].
      intros a Ha Hns H1 H2.
      rewrite (NWIN W1 Ea _ (ms_mem ms1) (ms_mem ms2) BVa HFr2 eq_refl a Ha H1 H2).
      rewrite (NWIN W1 Ea _ mem2 (ms_mem ms1) BVa HFr1 eq_refl a Ha H1 H2).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha H1 H2). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
    prreg HS (20%bv : bv 5) T20. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
    prreg_raw HS (19%bv : bv 5) T19. prreg_raw HS (21%bv : bv 5) T21. prreg_raw HS (22%bv : bv 5) T22. prreg_raw HS (27%bv : bv 5) T27.
    pose proof (rkk_gin_xR cx i n (S r') F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 (ms_mem ms2) HB HJ0 HFR HGN KEEPf PRESf) as HGN2.
    destruct (rkb_gin_pass cx i n r' F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms2) HGN2 HPF) as (f' & HGN3).
    apply (KP r' W1 _ eq_refl).
    exists (ms_regs ms2), ly1, S1, (ms_mem ms2). eexists. eexists.
    exists F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, ks, Ed, f', c2, O2, cap2, out2, spent.
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (GR 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp1|].
      split; [rewrite T3, (GR 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp1|].
      split; [rewrite T4, (GR 4%nat 4%bv ltac:(lia) eq_refl); exact Htp1|].
      split; [rewrite T8, (GR 8%nat 8%bv ltac:(lia) eq_refl); exact H8|].
      split; [rewrite T9, (GR 9%nat 9%bv ltac:(lia) eq_refl); exact H9|].
      rewrite T18, (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18. }
    split.
    { rewrite T19. cbn [sv_denot]. rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl), R21. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, rk_sll3_add8 by lia. f_equal. lia. }
    split; [rewrite T20, (GR 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
    split.
    { rewrite T21. cbn [sv_denot]. rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl), R21. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia. }
    split; [rewrite T23, (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23|].
    split.
    { rewrite T22. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 18 0)) with (rk_sh 23).
      apply rk_sh_den; [rewrite (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23 | rewrite (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split; [rewrite T24, (GR 24%nat 24%bv ltac:(lia) eq_refl); exact R24|].
    split; [rewrite T25, (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25|].
    split.
    { rewrite T27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 18 0)) with (rk_sh 25).
      apply rk_sh_den; [rewrite (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25 | rewrite (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M32].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M88].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
    split; [exact (rkk_live_xR cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGN3.
  + (* n + 1 >= nheld: the entry's last key passed; the loop ends *)
    assert (Hn1 : (length ks <= S n)%nat).
    { rewrite (rk_branch_lt Ea (SOff 21 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_ge in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 21%nat 21%bv eq_refl), R21 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    assert (r = 0%nat) by lia. subst r.
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa rk_Bspan A_rig_step.
    { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
      - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
        + left. reflexivity.
        + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
        + right. apply in_or_app. left. exact HinHP.
        + clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    destruct (rk_win_vals Ea _ ms2 W1 (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key HS eq_refl
      ltac:(rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
      ltac:(rewrite OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
      ltac:(rewrite OLDa by lia; exact E35) ltac:(rewrite OLDa by lia; exact E34)
      ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as [VNf VKf].
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { apply (rk_keep_join cx W1 m1 (ms_mem ms2) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact Mnh | exact VNf | exact (Mslot n Hn) | exact VKf].
      intros a Ha Hns H1 H2.
      rewrite (NWIN W1 Ea _ (ms_mem ms1) (ms_mem ms2) BVa HFr2 eq_refl a Ha H1 H2).
      rewrite (NWIN W1 Ea _ mem2 (ms_mem ms1) BVa HFr1 eq_refl a Ha H1 H2).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha H1 H2). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20.
    pose proof (rkk_gin_xR cx i n 0 F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 (ms_mem ms2) HB HJ0 HFR HGN KEEPf PRESf) as HGN2.
    pose proof (rkb_gout_pass cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms2) HB HGN2 HPF) as HGO.
    apply (KR W1 _).
    exists (ms_regs ms2), ly1, S1, (ms_mem ms2). eexists. eexists.
    exists F, FL, (qd ++ [(entry_keys e1 ks, h1)]), c2, O2, cap2, out2, spent.
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (GR 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp1|].
      split; [rewrite T3, (GR 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp1|].
      split; [rewrite T4, (GR 4%nat 4%bv ltac:(lia) eq_refl); exact Htp1|].
      split; [rewrite T8, (GR 8%nat 8%bv ltac:(lia) eq_refl); exact H8|].
      split; [rewrite T9, (GR 9%nat 9%bv ltac:(lia) eq_refl); exact H9|].
      rewrite T18, (GR 18%nat 18%bv ltac:(lia) eq_refl); exact H18. }
    split; [rewrite T20, (GR 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M88].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
    split; [exact Hi|].
    split; [exact (rkk_live_xR cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGO.
- (* ======== a0 = 0: the key has the prefix (end it) ======== *)
  assert (U0 : U Ea (SOff 40 0) = 0).
  { rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia. destruct (Z.eqb_spec (U Ea (SOff 40 0)) 0); [assumption | discriminate Hc]. }
  assert (Ha0z : getr regs2 10 = w64 0).
  { rewrite R10a. rewrite U_SOff, Z.add_0_r in U0. pose proof (bv_unsigned_in_range 64 (ew Ea 40)) as Hr64.
    change (bv_modulus 64) with (2 ^ 64) in Hr64. rewrite zcanon_id in U0 by (unfold M64; lia).
    apply bv_eq. rewrite U0. reflexivity. }
  assert (HPT : has_prefix (gpre cx) (bzs kt) = true)
    by exact (proj1 (rkr_agree W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp) (proj1 HA0 Ha0z)).
  paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa rk_Bspan AF_fr_gesture_end.
  { apply (rk_awr_k Ea _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ (gxG0 cx) ATABLE a HAR3 HP0X HPX).
      + left. reflexivity.
      + change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_blk cx ly1 S1 W1 mem2 _ XG _ hp (re_kh e1) a HAR3 HP0X HPX).
      + right. apply in_or_app. left. exact HinHP.
      + clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  (* ---- the call gesture_end (key) at 0x82e8c ---- *)
  destruct (rk_win_vals Ea _ ms1 W1 (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key HS eq_refl
    ltac:(rewrite OLDa, (EE 23%nat 23%bv eq_refl), R23 by lia; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
    ltac:(rewrite OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
    ltac:(rewrite OLDa by lia; exact E35) ltac:(rewrite OLDa by lia; exact E34)
    ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as [VN1 VK1].
  assert (KEEPA : rkk_KEEP cx W1 m1 (ms_mem ms1)).
  { apply (rk_keep_join cx W1 m1 (ms_mem ms1) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact Mnh | exact VN1 | exact (Mslot n Hn) | exact VK1].
    intros a Ha Hns H1 H2.
    rewrite (NWIN W1 Ea _ mem2 (ms_mem ms1) BVa HFr1 eq_refl a Ha H1 H2).
    rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
    exact (M01 a Ha H1 H2). }
  assert (PRESA : rkk_PRES W1 m1 (ms_mem ms1)).
  { intros a Hp. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
  pose proof (rkk_gin_xR cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 m1 md1 k1 (ms_mem ms1) HB HJ0 HFR HGN KEEPA PRESA) as HGNA.
  pose proof (rkk_live_xR cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms1) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPA PRESA) as HLVA.
  pose proof (rkk_lslots cx F W1 m1 (ms_mem ms1) HLS KEEPA) as HLSA.
  pose proof HLVA as (fposA & HpA & HJA & HROMA & HPKA & HFRA & HLKA).
  assert (EHpA : HpA = []) by (eapply rk_jhp0_xR; exact HJA). subst HpA. rewrite EHp0 in HJA.
  pose proof (rk_fpos_eq_xR cx fposA fpos _ _ _ _ _ _ _ _ _ HJA HJ2) as Efp. subst fposA.
  assert (M32A : val_mem SEGS (arm W1 (ms_mem ms1)) (gsp1 cx + 32) 8 ((gSA cx i + 48) mod 8 + 3)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms1) _ 8 _); [|exact M32].
    intros kk Hkk. apply KEEPA; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
  assert (M88A : val_mem SEGS (arm W1 (ms_mem ms1)) (gsp1 cx + 88) 8 (Z.of_nat i)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms1) _ 8 _); [|exact M88].
    intros kk Hkk. apply KEEPA; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; lia]. }
  assert (GkA : garr8 SEGS (arm W1 (ms_mem ms1)) key (bzs (kt ++ [Z_to_bv 8 0]))).
  { apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms1) _ _ Gk). intros b Hb. rewrite LKT in Hb.
    apply KEEPA; [clear - Hb Hk4096 Hkceil Hrq2 C1; unfold alloc_ceiling in *; lia | clear - Hb Hkceil Hrq2 SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, alloc_ceiling in *; lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
  prreg HS (8%bv : bv 5) U8. prreg HS (10%bv : bv 5) U10.
  pose proof HGNA as (_ & _ & _ & _ & _ & _ & _ & _ & HRLYA & HOUTA & _ & _ & _ & _ & HPERMA & _ & _ & _).
  destruct (rk_room cx i n r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1) HB HGNA HPT)
    as (RM1 & RM2 & RM3 & Hxl0 & Hcap2 & RMg & CNg & CNle).
  assert (ROOM : ge_room MMAX (blocks_bytes S1) c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))).
  { unfold ge_room, ge_tr. rewrite (rkb_live_pos c2 (Z.of_nat (length kt)) Hxl0). exact (conj RM1 RM2). }
  assert (MOKG : mo_ok MT S1 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)))).
  { apply (mo_ok_le MT MLAW S1 _ _ RM3). apply rk_le_add. exact (mo_free_nonneg MT MLAW). }
  assert (HinKP : In (key, Z.of_nat (length kt) + 1) (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))))).
  { apply in_concat. exists (aentry_blks (entry_keys e1 ks)). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. right. cbn [re_keys entry_keys].
      apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). apply nth_In. exact Hn. }
  assert (HAR4 : ARh ly1 S1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md2) mat1 md2))
    by exact (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2).
  assert (Hko : key <> out2).
  { destruct (rk_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTA) as [(Hc0 & Ho0 & _) | (Hcp & _ & Hino)].
    - rewrite Ho0. lia.
    - assert (Hne : (key, Z.of_nat (length kt) + 1) <> (out2, cap2)).
      { apply (rk_nodup_far _ _ _ _ _ _ _ _ _ HNDP HinKP). unfold aout_blks. rewrite (proj2 (Z.eqb_neq cap2 0) ltac:(lia)). left. reflexivity. }
      pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 Hink Hino Hne) as Hd. cbn [fst snd] in Hd.
      pose proof (req_size_pos cap2 ltac:(lia)) as [Hc1 Hc2]. intros Heq. lia. }
  pose proof HFRA as (_ & _ & _ & _ & _ & _ & HSVA).
  destruct (rk_saved_ra_s0 cx W1 (ms_mem ms1) HSVA) as [VRA VS0].
  destruct (rk_chain2_xR cx _ ly1 S1 W1 (ms_mem ms1) _ _ HB HJ2 VRA VS0) as (ch1 & Hch1).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (rk_ge_call_xR W1 (ms_regs ms1) (ms_mem ms1) _ RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx) (gxmem cx)
      (gxmd cx) [(1, fpos)] ly1 S1 _ (Z_to_bv 64 (BASE + 2980)) c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 kt key
      (Z.of_nat (length kt) + 1) (-224) ch1 HJ2).
    - unfold spZ at 1. rewrite U2, (GR 2%nat 2%bv ltac:(lia) eq_refl). fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold GE_STK, GE_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK. lia.
    - rewrite U3, (GR 3%nat 3%bv ltac:(lia) eq_refl), Hgp1. exact Hgp.
    - rewrite U4, (GR 4%nat 4%bv ltac:(lia) eq_refl), Htp1. exact Htp.
    - exact U1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - replace (s0Z (ms_regs ms1)) with (gsp0 cx); [exact Hch1|].
      unfold s0Z. rewrite U8, (GR 8%nat 8%bv ltac:(lia) eq_refl), H8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - rewrite U10, OLDa, E34 by lia. reflexivity.
    - exact HOUTA.
    - exact GkA.
    - exact NZk.
    - exact Lk.
    - exact Hink.
    - exact Hko.
    - lia.
    - exact (rk_end5 W1 (ms_mem ms1) HROMA).
    - exact HROMA.
    - exact ROOM.
    - exact MOKG.
    - exact RMg.
    - exact CNg.
    - intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p0 & n0 & Hin0 & Hpa0).
      apply (rk_fp_blk cx ly1 S1 W1 (ms_mem ms1) _ XG p0 n0 a HAR4 HP0X HPX); [| exact Hpa0].
      unfold XG. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin0. }
  cbv beta. intros W2 c2x _ (ly2 & S2 & regs2' & mem2' & md2' & kk1 & out2' & kg & -> & HJ3 & HJc3 & HJs3 & HP3 & HAK3 & HM3 &
    HRMge & (restG & HPa3 & HPb3) & HO3).
  (* ---- back at 0x82e90 ---- *)
  pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR5.
  assert (NTO : ~ In (gxG0 cx, ATABLE) (aout_blks cap2 out2)) by exact (rk_nodup_head_out _ _ _ _ _ _ _ HNDP).
  assert (NHO : ~ In (hp, re_kh e1) (aout_blks cap2 out2))
    by (intros Hin; exact (rk_nodup_far _ _ _ _ _ _ _ _ _ HNDP HinHP Hin eq_refl)).
  assert (NKO : ~ In (key, Z.of_nat (length kt) + 1) (aout_blks cap2 out2))
    by (intros Hin; exact (rk_nodup_far _ _ _ _ _ _ _ _ _ HNDP HinKP Hin eq_refl)).
  assert (NGT : ~ In (gxG0 cx, ATABLE) (gxrest cx)) by exact (rk_nodup_rest _ _ _ _ _ _ _ _ HNDP (or_introl eq_refl)).
  assert (NGH : ~ In (hp, re_kh e1) (gxrest cx))
    by exact (rk_nodup_rest _ _ _ _ _ _ _ _ HNDP (or_intror (in_or_app _ _ _ (or_introl HinHP)))).
  assert (NGK : ~ In (key, Z.of_nat (length kt) + 1) (gxrest cx))
    by exact (rk_nodup_rest _ _ _ _ _ _ _ _ HNDP (or_intror (in_or_app _ _ _ (or_introl HinKP)))).
  destruct (rk_ge_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 HAR4 HPa3 HPb3 HinT NTO) as (HinT2 & KT2).
  destruct (rk_ge_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 HAR4 HPa3 HPb3 Hinh NHO) as (Hinh2 & KH2).
  destruct (rk_ge_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 HAR4 HPa3 HPb3 Hink NKO) as (Hink2 & KK2).
  destruct (rk_alb ly2 S2 W2 mem2' _ _ _ HAR5 HinT2) as (_ & _ & _ & _ & HTpres5 & _ & _).
  destruct (rk_alb ly2 S2 W2 mem2' _ _ _ HAR5 Hinh2) as (_ & _ & _ & _ & Hhpres5 & _ & _).
  change (req_size ATABLE) with 896 in KT2, HTpres5.
  jafter_call_keep_pi HS 52%nat regs2' (mrestrict (w_H W2) mem2') HP3 [0; 1; 2]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BVa by lia; rewrite ?BV23, ?BV25, ?BV33).
    - intros a Ha. apply (mbyte_of_aview SEGS). replace a with (gxG0 cx + (a - gxG0 cx)) by lia.
      apply KT2. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha _. lia.
    - intros a Ha. apply (mbyte_of_aview SEGS). replace a with (gxG0 cx + (a - gxG0 cx)) by lia.
      apply KT2. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha _. apply (apresent_writable SEGS). replace a with (gxG0 cx + (a - gxG0 cx)) by lia.
      apply HTpres5. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (mbyte_of_aview SEGS). replace a with (hp + (a - hp)) by lia.
      apply KH2. clear - Ha Hkh Hrk2 Hn. lia.
    - intros a Ha _. apply (apresent_writable SEGS). replace a with (hp + (a - hp)) by lia.
      apply Hhpres5. clear - Ha Hkh Hrk2 Hn. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc Ea 52 (map (getr regs2') CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall k0, (k0 < 52)%nat -> ew Eb k0 = ew Ea k0) by (intros k0 Hk0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hk0).
  clear HEb.
  assert (GRb : forall k0 (r0 : bv 5), (k0 < 36)%nat -> Z.of_nat k0 = bv_unsigned r0 -> ew Eb k0 = getr regs1 r0)
    by (intros k0 r0 Hk0 Hr0; rewrite OLDb by lia; apply GR; [exact Hk0 | exact Hr0]).
  assert (SHOKb : sh_ok SEGS rk_Bx rk_SH Eb (mrestrict (w_H W2) mem2')).
  { apply (rk_shok Eb W2 ly2 S2 mem2' _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HAR5).
    - rewrite (GRb 18%nat 18%bv ltac:(lia) eq_refl). exact H18.
    - rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl). exact R23.
    - rewrite (GRb 25%nat 25%bv ltac:(lia) eq_refl). exact R25.
    - rewrite OLDb, OLDa by lia. exact E33.
    - exact HinT2.
    - clear - HSA. lia.
    - exact HTend.
    - exact Hinh2.
    - exact Hkh.
    - clear - Hn. lia. }
  paj_run_tok_xR RUNG HS HJ3 SHOKb rk_Bspan.
  { apply (rk_awr_k Eb _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl), R23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite OLDb, OLDa, E33 by lia. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly2 S2 _ (gxG0 cx) ATABLE a HP0X HinT2 NGT).
      change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly2 S2 _ hp (re_kh e1) a HP0X Hinh2 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
  (* ---- the call free (key) at 0x82eb4 ---- *)
  assert (BVb : forall k0, (k0 < 36)%nat -> base_val Eb (Some k0) = base_val E (Some k0))
    by (intros k0 Hk0; cbn [base_val]; rewrite OLDb, OLDa by lia; reflexivity).
  pmkst HS.
  prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3. prreg HS (4%bv : bv 5) V4.
  prreg HS (8%bv : bv 5) V8. prreg HS (10%bv : bv 5) V10.
  destruct (rk_win3 Eb _ ms2 W2 (gSA cx i) (hp + 8 * Z.of_nat n) hp (Z.of_nat (length ks)) key HS eq_refl
    ltac:(rewrite (GRb 25%nat 25%bv ltac:(lia) eq_refl), R25; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
    ltac:(rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl), R23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
    ltac:(rewrite OLDb, OLDa, E33 by lia; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
    ltac:(rewrite OLDb, OLDa by lia; exact E32) ltac:(rewrite OLDb, OLDa by lia; exact E35) ltac:(rewrite OLDb, OLDa by lia; exact E34)
    ltac:(clear - Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia) ltac:(clear - Hks26; lia)
    ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)) as (VH2 & VN2 & VK2).
  assert (VN2' : val_mem SEGS (arm W2 mem2') (gSA cx i + 48) 4 (Z.of_nat (length ks))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) mem2' _ 4 _); [|exact VN1].
    intros kk Hkk. replace (gSA cx i + 48 + kk) with (gxG0 cx + (gSA cx i + 48 + kk - gxG0 cx)) by lia.
    apply KT2. clear - Hkk HTend HSA. unfold AENT, ATABLE in *. lia. }
  assert (VK2' : val_mem SEGS (arm W2 mem2') (hp + 8 * Z.of_nat n) 8 key).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) mem2' _ 8 _); [|exact VK1].
    intros kk Hkk. replace (hp + 8 * Z.of_nat n + kk) with (hp + (8 * Z.of_nat n + kk)) by lia.
    apply KH2. clear - Hkk Hkh Hrk2 Hn. lia. }
  assert (KEEPS : rkk_KEEP cx W2 mem2' (ms_mem ms2)).
  { apply (rk_keep_join cx W2 mem2' (ms_mem ms2) (gSA cx i) (hp + 8 * Z.of_nat n) (Z.of_nat (length ks)) key); [| exact VN2' | exact VN2 | exact VK2' | exact VK2].
    intros a Ha Hns H1 H2. exact (NWIN W2 Eb _ mem2' (ms_mem ms2) BVb HFr2 eq_refl a Ha H1 H2). }
  assert (PRESS : forall a, apresent (w_H W2) mem2' a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Hp; eapply apresent_grows; [exact HG2 | exact Hp]).
  (* the saved ra and s0 words at the free call: kept by gesture_end (above its window) and the run *)
  assert (KHI : forall a, gsp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W1) (ms_mem ms1) a).
  { intros a Ha. rewrite (KEEPS a ltac:(lia) ltac:(lia)).
    apply (rk_gx_keep_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGRIG HJc3); [clear - Ha SPR C1; unfold gsp1, RIG_FRAME in *; lia|].
    clear - Ha. unfold gsp1, RIG_FRAME in *. lia. }
  assert (VRA2 : val_mem SEGS (arm W2 (ms_mem ms2)) (gsp0 cx - 8) 8 (bv_unsigned (getr (gxregs cx) 1))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) (ms_mem ms2) _ 8 _); [|exact VRA].
    intros kk Hkk. apply KHI. clear - Hkk SPR C1. unfold gsp1, RIG_FRAME in *. lia. }
  assert (VS02 : val_mem SEGS (arm W2 (ms_mem ms2)) (gsp0 cx - 16) 8 (bv_unsigned (getr (gxregs cx) 8))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) (ms_mem ms2) _ 8 _); [|exact VS0].
    intros kk Hkk. apply KHI. clear - Hkk SPR C1. unfold gsp1, RIG_FRAME in *. lia. }
  (* the free's caller context (GCTX): the entry's frame is below the layout top, so the chain at 0x82eb4 is the
     entry's chain under relay_instance_gone's frame record (gsp0, ra, s0) *)
  assert (TOP2 : gsp0 cx < ly_top ly2 - 16).
  { pose proof (rk_gx_ly_top_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as ET2. destruct HC as (HC1 & _).
    unfold gsp0. clear - HC1 ET2. lia. }
  pose proof (rk_chain2p_xR cx _ ly2 S2 W2 (ms_mem ms2) _ _ HB HJ3 VRA2 VS02 TOP2) as Hch2.
  assert (SP2 : spZ (ms_regs ms2) = gsp0 cx + -224).
  { unfold spZ at 1. rewrite V2, (GRb 2%nat 2%bv ltac:(lia) eq_refl). fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia. }
  prreg HS (9%bv : bv 5) V9. prreg HS (18%bv : bv 5) V18. prreg HS (19%bv : bv 5) V19. prreg HS (20%bv : bv 5) V20.
  prreg HS (21%bv : bv 5) V21. prreg HS (23%bv : bv 5) V23. prreg HS (24%bv : bv 5) V24. prreg HS (25%bv : bv 5) V25.
  prreg_raw HS (22%bv : bv 5) V22. prreg_raw HS (27%bv : bv 5) V27.
  rewrite (pal_free B TL).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (rk_free_xR (G_RIG B RG) W2 (ms_regs ms2) (ms_mem ms2) RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx)
      (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 _ _ key (Z.of_nat (length kt) + 1) (-224) (Z_to_bv 64 (BASE + 3020))
      ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx) HJ3 Hink2).
    - rewrite V10, OLDb, OLDa, E34 by lia. reflexivity.
    - exact SP2.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ASTACK. lia.
    - rewrite V3, (GRb 3%nat 3%bv ltac:(lia) eq_refl), Hgp1. exact Hgp.
    - rewrite V4, (GRb 4%nat 4%bv ltac:(lia) eq_refl), Htp1. exact Htp.
    - exact V1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - apply (achain_chain_pre ly2 (aview SEGS (w_H W2) (ms_mem ms2)) (gsp0 cx + -224) (gsp0 cx) _ (ms_regs ms2) Hch2).
      + rewrite SP2. clear - SPR C1. lia.
      + unfold s0Z. rewrite V8, (GRb 8%nat 8%bv ltac:(lia) eq_refl), H8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + unfold raZ. rewrite V1, unsigned_lit_small by lia. lia.
    - destruct HC as (_ & HC2). replace (raZ (ms_regs ms2)) with (A_rig_entryP + 652); [exact HC2|].
      unfold raZ. rewrite V1, unsigned_lit_small by lia. unfold A_rig_entryP, A_rig_entry, AF_fr_relay_instance_gone. ring.
    - intros Hin0 i0 Hi0. apply (rk_fp_in cx ly1 S1 W1 m1 md1 XG key (Z.of_nat (length kt) + 1) i0 HAR1 HP0X HPX); [| exact Hin0 | exact Hi0].
      right. apply in_or_app. left. exact HinKP.
    - exact (mo_ok_step MT MLAW S1 S2 _ _ RM3 HM3).
    - exact HRMge.
    - apply CNle. intros P. exact (rkc_cnt_out_le P ly1 S1 ly2 S2 cap2 out2 _ out2' restG HPa3 HPb3). }
  cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ4 & HP4 & (l1 & l2 & EL2 & EL3) & HFS & KF & HMF & HRMf &
    HERR & HPRF).
  (* ---- back at 0x82eb8 after free ---- *)
  pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR6.
  (* the key's count change: gesture_end's send chain moves g_out's own count exactly (rkc_ge_netP), the free drops
     the key's block (rkc_cnt_free) *)
  assert (HCN3 : forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length kt) + 1))).
  { intros P. exact (rkc_end_cnt P c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))
      ly1 S1 ly2 S2 ly3 S3 out2 out2' restG l1 l2 key Hxl0 Hcap2 HPa3 HPb3 EL2 EL3). }
  assert (KEEPB : forall b m0, In (b, m0) (ablocks B ly2 S2) -> (b, m0) <> (key, Z.of_nat (length kt) + 1) ->
    In (b, m0) (ablocks B ly3 S3)).
  { intros b m0 Hb Hne. rewrite EL3. rewrite EL2 in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]];
    [apply in_or_app; left; exact Hb | congruence | apply in_or_app; right; exact Hb]. }
  pose proof (KEEPB _ _ HinT2 NE2) as HinT3.
  pose proof (KEEPB _ _ Hinh2 NE3) as Hinh3.
  pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 HinT Hink NE2) as DTK'. cbn [fst snd] in DTK'. change (req_size ATABLE) with 896 in DTK'.
  pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 Hinh Hink NE3) as DHK'. cbn [fst snd] in DHK'.
  pose proof KF as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
  assert (VH3 : val_mem SEGS (arm W3 mem3) (gSA cx i + 40) 8 hp).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 8 _); [|exact VH2].
    intros kk Hkk. replace (gSA cx i + 40 + kk) with (gxG0 cx + (gSA cx i + 40 + kk - gxG0 cx)) by lia.
    apply (KF2 _ _ _ HinT2); change (req_size ATABLE) with 896; clear - Hkk HTend HSA DTK'; unfold AENT, ATABLE in *; lia. }
  assert (VN3 : val_mem SEGS (arm W3 mem3) (gSA cx i + 48) 4 (Z.of_nat (length ks))).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 4 _); [|exact VN2].
    intros kk Hkk. replace (gSA cx i + 48 + kk) with (gxG0 cx + (gSA cx i + 48 + kk - gxG0 cx)) by lia.
    apply (KF2 _ _ _ HinT2); change (req_size ATABLE) with 896; clear - Hkk HTend HSA DTK'; unfold AENT, ATABLE in *; lia. }
  assert (VK3 : val_mem SEGS (arm W3 mem3) (hp + 8 * Z.of_nat n) 8 key).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 8 _); [|exact VK2].
    intros kk Hkk. replace (hp + 8 * Z.of_nat n + kk) with (hp + (8 * Z.of_nat n + kk)) by lia.
    apply (KF2 _ _ _ Hinh2); clear - Hkk Hkh Hrk2 Hn DHK'; lia. }
  assert (P3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs3 r0 = getr (ms_regs ms2) r0).
  { intros r0 Hr0. pose proof (HP4 (bv_unsigned r0) Hr0) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. }
  assert (R3_2 : spZ regs3 = gsp1 cx) by (unfold spZ; rewrite (P3 2%bv ltac:(unfold acallee_saved; change (bv_unsigned (2%bv : bv 5)) with 2; lia)); fold (spZ (ms_regs ms2)); rewrite SP2; unfold gsp1, RIG_FRAME; lia).
  assert (R3_18 : getr regs3 18 = w64 SHADOW_OFF) by (rewrite (P3 18%bv ltac:(unfold acallee_saved; change (bv_unsigned (18%bv : bv 5)) with 18; lia)), V18, (GRb 18%nat 18%bv ltac:(lia) eq_refl); exact H18).
  assert (R3_19 : getr regs3 19 = w64 (8 * Z.of_nat n)) by (rewrite (P3 19%bv ltac:(unfold acallee_saved; change (bv_unsigned (19%bv : bv 5)) with 19; lia)), V19, (GRb 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (R3_21 : getr regs3 21 = w64 (Z.of_nat n)) by (rewrite (P3 21%bv ltac:(unfold acallee_saved; change (bv_unsigned (21%bv : bv 5)) with 21; lia)), V21, (GRb 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (R3_23 : getr regs3 23 = w64 (gSA cx i + 48)) by (rewrite (P3 23%bv ltac:(unfold acallee_saved; change (bv_unsigned (23%bv : bv 5)) with 23; lia)), V23, (GRb 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
  assert (R3_25 : getr regs3 25 = w64 (gSA cx i + 40)) by (rewrite (P3 25%bv ltac:(unfold acallee_saved; change (bv_unsigned (25%bv : bv 5)) with 25; lia)), V25, (GRb 25%nat 25%bv ltac:(lia) eq_refl); exact R25).
  assert (R3_22 : getr regs3 22 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8)).
  { rewrite (P3 22%bv ltac:(unfold acallee_saved; change (bv_unsigned (22%bv : bv 5)) with 22; lia)), V22. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 18 0)) with (rk_sh 23).
    apply rk_sh_den; [rewrite (GRb 23%nat 23%bv ltac:(lia) eq_refl); exact R23 | rewrite (GRb 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
    clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
  assert (R3_27 : getr regs3 27 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8)).
  { rewrite (P3 27%bv ltac:(unfold acallee_saved; change (bv_unsigned (27%bv : bv 5)) with 27; lia)), V27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 18 0)) with (rk_sh 25).
    apply rk_sh_den; [rewrite (GRb 25%nat 25%bv ltac:(lia) eq_refl); exact R25 | rewrite (GRb 18%nat 18%bv ltac:(lia) eq_refl); exact H18 |].
    clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
  pose proof (rk_blk_apart _ _ _ _ _ _ _ HAR1 HinT Hinh NE1) as DTH'. cbn [fst snd] in DTH'. change (req_size ATABLE) with 896 in DTH'.
  assert (DSH3 : hp + 8 * Z.of_nat n + 8 <= gSA cx i + 40 \/ gSA cx i + 52 <= hp + 8 * Z.of_nat n)
    by (clear - DTH' HTend HSA Hkh Hrk2 Hn; unfold AENT, ATABLE in *; lia).
  assert (R3_3 : getr regs3 3 = getr (gxregs cx) 3) by (rewrite (P3 3%bv ltac:(unfold acallee_saved; change (bv_unsigned (3%bv : bv 5)) with 3; lia)), V3, (GRb 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp1).
  assert (R3_4 : getr regs3 4 = getr (gxregs cx) 4) by (rewrite (P3 4%bv ltac:(unfold acallee_saved; change (bv_unsigned (4%bv : bv 5)) with 4; lia)), V4, (GRb 4%nat 4%bv ltac:(lia) eq_refl); exact Htp1).
  assert (R3_8 : getr regs3 8 = w64 (gsp0 cx)) by (rewrite (P3 8%bv ltac:(unfold acallee_saved; change (bv_unsigned (8%bv : bv 5)) with 8; lia)), V8, (GRb 8%nat 8%bv ltac:(lia) eq_refl); exact H8).
  assert (R3_9 : getr regs3 9 = w64 (gsp1 cx)) by (rewrite (P3 9%bv ltac:(unfold acallee_saved; change (bv_unsigned (9%bv : bv 5)) with 9; lia)), V9, (GRb 9%nat 9%bv ltac:(lia) eq_refl); exact H9).
  assert (R3_20 : getr regs3 20 = w64 (F + 32)) by (rewrite (P3 20%bv ltac:(unfold acallee_saved; change (bv_unsigned (20%bv : bv 5)) with 20; lia)), V20, (GRb 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
  assert (R3_24 : getr regs3 24 = w64 (Z.of_nat (length (gpre cx)))) by (rewrite (P3 24%bv ltac:(unfold acallee_saved; change (bv_unsigned (24%bv : bv 5)) with 24; lia)), V24, (GRb 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
  replace (gsp0 cx + -224) with (gsp1 cx) in HJs3 by (unfold gsp1, RIG_FRAME; lia).
  change (Z_to_bv 64 (BASE + 3020)) with (Z_to_bv 64 (BASE + (A_rig_inner + 104))).
  destruct r as [|r'].
  2:{ (* ======== n + 1 < nheld: the last key moves into slot n ======== *)
  assert (Hkl : (length ks - 1 < length ks)%nat) by lia.
  set (kl := nth (length ks - 1) ks (0, [], [])) in *.
  pose proof (rkr_entry_at ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) (length ks - 1) HAR1 HRLY Hkl) as X.
  cbv zeta in X. fold kl in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinkl & _).
  destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 Hinkl) as (_ & Hkl4096 & Hklceil & _ & _ & _ & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text kl)) + 1) ltac:(lia)) as [Hrl1 Hrl2].
  set (hpl := hp + 8 * Z.of_nat (length ks - 1)) in *.
  assert (VL1 : val_mem SEGS (arm W1 m1) hpl 8 (key_addr kl)) by exact (Mslot _ Hkl).
  assert (VLA : val_mem SEGS (arm W1 (ms_mem ms1)) hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms1) _ 8 _); [|exact VL1].
    intros kk Hkk. apply KEEPA.
    - clear - Hkk Hh4096 Hhceil Hkh Hrk1 Hrk2 Hkl C1. unfold hpl, alloc_ceiling in *. lia.
    - clear - Hkk Hhceil Hkh Hrk1 Hrk2 Hkl SPR C1. unfold hpl, gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, alloc_ceiling in *. lia. }
  assert (VL2' : val_mem SEGS (arm W2 mem2') hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem ms1) mem2' _ 8 _); [|exact VLA].
    intros kk Hkk. replace (hpl + kk) with (hp + (hpl - hp + kk)) by lia.
    apply KH2. clear - Hkk Hkh Hrk2 Hkl. unfold hpl in *. lia. }
  assert (VL2 : val_mem SEGS (arm W2 (ms_mem ms2)) hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2' (ms_mem ms2) _ 8 _); [|exact VL2'].
    intros kk Hkk. apply KEEPS.
    - clear - Hkk Hh4096 Hhceil Hkh Hrk1 Hrk2 Hkl C1. unfold hpl, alloc_ceiling in *. lia.
    - clear - Hkk Hhceil Hkh Hrk1 Hrk2 Hkl SPR C1. unfold hpl, gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, alloc_ceiling in *. lia. }
  assert (VL3 : val_mem SEGS (arm W3 mem3) hpl 8 (key_addr kl)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W3) (ms_mem ms2) mem3 _ 8 _); [|exact VL2].
    intros kk Hkk. replace (hpl + kk) with (hp + (hpl - hp + kk)) by lia.
    apply (KF2 _ _ _ Hinh2); clear - Hkk Hkh Hrk2 Hkl DHK'; unfold hpl in *; lia. }
  destruct (rk_st_gen (A_rig_inner + 104) [hpl; key_addr kl] W3 ly3 S3 regs3 mem3 md3 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1)
    (Z.of_nat n) (Z.of_nat (length ks)) key HAR6 R3_2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32)
    R3_18 R3_19 R3_21 R3_23 R3_22 R3_25 R3_27 HinT3 ltac:(clear - HSA; lia) HTend
    ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
    Hinh3 Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)
    DSH3 VH3 VN3 VK3) as [HS5 SHOK5].
  remember (Eimg (Ereg regs3 (map (Z_to_bv 64) ([hp; hp + 8 * Z.of_nat n; key; Z.of_nat (length ks)] ++ [hpl; key_addr kl])))) as E5 eqn:HE5.
  assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; apply Eimg_env).
  assert (EE5 : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E5 k0 = getr regs3 r0)
    by (intros k0 r0 Hk0; subst E5; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
  assert (E5_32 : ew E5 32 = Z_to_bv 64 hp) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (E5_33 : ew E5 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  assert (E5_34 : ew E5 34 = Z_to_bv 64 key) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
  assert (E5_35 : ew E5 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
  assert (E5_36 : ew E5 36 = Z_to_bv 64 hpl) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 4)).
  assert (E5_37 : ew E5 37 = Z_to_bv 64 (key_addr kl)) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 5)).
  clear HE5.
  assert (Hhpl : hp + 8 * Z.of_nat n + 8 <= hpl /\ hpl + 8 <= hp + re_kh e1) by (unfold hpl; clear - Hkh Hn Hks Hkl; lia).
  assert (AF36 : afact_ok E5 36 (PTRK 3)).
  { unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2]. rewrite E5_36, unsigned_lit_small
      by (clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia).
    split; [clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia|]. split; [|lia].
    change (2 ^ 3) with 8. unfold hpl.
    replace (hp + 8 * Z.of_nat (length ks - 1)) with ((2 * (hp / 16) + Z.of_nat (length ks - 1)) * 8)
      by (pose proof (Z.div_mod hp 16 ltac:(lia)); lia). apply Z_mod_mult. }
  assert (AF37 : afact_ok E5 37 (PTRK 0)).
  { unfold afact_ok, PTRK. cbn [af_lo af_hi af_al2]. rewrite E5_37, unsigned_lit_small
      by (clear - Hkl4096 Hklceil Hrl1 Hrl2 C1; unfold alloc_ceiling in *; lia).
    split; [clear - Hkl4096 Hklceil Hrl1 Hrl2 C1; unfold alloc_ceiling in *; lia|]. split; [|lia].
    rewrite Z.pow_0_r. apply Z.mod_1_r. }
  pose proof (st_ok_pi_add_fact E5 _ _ 36%nat (PTRK 3) HS5 AF36) as HSa.
  pose proof (st_ok_pi_add_fact E5 _ _ 37%nat (PTRK 0) HSa AF37) as HSb.
  assert (BV5_36 : base_val E5 (Some 36%nat) = hpl)
    by (cbn [base_val]; rewrite E5_36; apply unsigned_lit_small; clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia).
  assert (BV5_25 : base_val E5 (Some 25%nat) = gSA cx i + 40)
    by (cbn [base_val]; rewrite (EE5 25%nat 25%bv eq_refl), R3_25; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_23 : base_val E5 (Some 23%nat) = gSA cx i + 48)
    by (cbn [base_val]; rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_33 : base_val E5 (Some 33%nat) = hp + 8 * Z.of_nat n)
    by (cbn [base_val]; rewrite E5_33; apply unsigned_lit_small; clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia).
  assert (RG4 : region_ok SEGS E5 (mrestrict (w_H W3) mem3) rk_R4).
  { unfold region_ok, rk_R4. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV5_36. split; [clear - Hhpl Hh4096; lia|]. split; [clear - Hhpl Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E5 _ hpl 0 8 (SOff 37 0) (key_addr kl));
    [cbn [sv_denot]; rewrite E5_37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VL3]. }
  assert (DJ4 : all_disjoint E5 rk_R4 rk_regions).
  { apply all_disjoint_of_extents. unfold rk_regions, rk_R4, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV5_36, BV5_25, BV5_23, BV5_33.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Hhpl DTH' HTend HSA Hrk1 Hrk2. unfold AENT, ATABLE in *. repeat split; lia. }
  pose proof (st_ok_pi_add_region E5 _ _ rk_R4 HSb eq_refl RG4 DJ4) as HSc.
  assert (ALI : sv_denot E5 rk_EXPR = sv_denot E5 (SOff 36 0)).
  { rewrite (rk_expr_den E5 hp (Z.of_nat (length ks)) E5_32 E5_35)
      by (clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 Hks26 Hkl C1; unfold alloc_ceiling, hpl in *; lia).
    cbn [sv_denot]. rewrite E5_36, Z.add_0_r, Z_to_bv_bv_unsigned. unfold hpl. f_equal. lia. }
  pose proof (st_ok_pi_add_alias E5 _ _ rk_EXPR (SOff 36 0) HSc ALI) as HSd.
  assert (SHOK6 : sh_ok SEGS rk_Bx (rk_SH ++ [mkSHE 36 0 8]) E5 (mrestrict (w_H W3) mem3)).
  { unfold sh_ok in *. apply Forall_app. split; [exact SHOK5|]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W3) mem3 E5 rk_Bx 36 hpl 8 hpl 0 8).
    - apply (rk_rab ly3 S3 W3 mem3 md3 hp (re_kh e1)); [exact HAR6 | exact Hinh3 | clear - Hhpl; lia | clear - Hhpl Hrk2; lia].
    - unfold rk_Bx. apply U_atom; [rewrite (EE5 18%nat 18%bv eq_refl); exact R3_18 | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact E5_36 | clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia].
    - lia.
    - lia.
    - intros x Hx. replace (0 `min` 8) with 0 in Hx by reflexivity. replace (0 `max` 8) with 8 in Hx by reflexivity.
      unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hx Hhpl Hhapp Hrk1 Hrk2. lia. }
  clear HS HS5 HSa HSb HSc. rename HSd into HS.
  paj_run_tok_xR RUNG HS HJ4 SHOK6 rk_Bspan.
  { apply (rk_awr_k4 E5 _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)).
    - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite E5_33. apply unsigned_lit_small. clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
      change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into msf, mat into matf, HF into HFf, HFr into HFrf, HG into HGf.
  psrr_branch_tok RUNG BRR HS SHOK6 rk_Bspan.
  + (* n < nheld - 1: back to the loop head with key n replaced by the last *)
    paj_run_to_tok_xR RUNTOG HS HJ4 SHOK6 rk_Bspan A_rig_inner.
    { apply (rk_awr_win E5 _ _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)); [| | rk_win_tac | |].
      - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite E5_33. apply unsigned_lit_small. clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
        change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into msg, mat into matg, HF into HFg, HFr into HFrg, HG into HGg.
    (* the two cells after the stores *)
    pose proof (st_ok_pi_region_nth E5 _ _ 2 (YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 (-1)))]) HS eq_refl) as HRf2.
    pose proof (st_ok_pi_region_nth E5 _ _ 3 (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 37 0))]) HS eq_refl) as HRf3.
    cbn [ms_mem restrict] in HRf2, HRf3.
    assert (Lks' : Z.of_nat (length (swap_remove (0, [], []) n ks)) = Z.of_nat (length ks) - 1)
      by (rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
    assert (VNf : val_mem SEGS (arm W3 (ms_mem msg)) (gSA cx i + 48) 4 (Z.of_nat (length (swap_remove (0, [], []) n ks)))).
    { rewrite Lks'.
      pose proof (field_of_region E5 _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) HRf2
        ltac:(rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia); reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hks26 Hkl; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    assert (VKf : val_mem SEGS (arm W3 (ms_mem msg)) (hp + 8 * Z.of_nat n) 8 (key_addr kl)).
    { pose proof (field_of_region E5 _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 37 0) (key_addr kl) HRf3
        ltac:(rewrite E5_33; apply unsigned_lit_small; clear - Hhpl Hh4096 Hhceil Hrk1 Hrk2 C1; unfold alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hkl4096 Hklceil Hrl1 Hrl2 C1; unfold alloc_ceiling in *; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    (* every other byte is kept by the two runs *)
    assert (KST : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) (ms_mem msg) a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha _ H1 H2.
      rewrite (aview_kept_out E5 _ (w_H W3) (ms_mem msf) (ms_mem msg) HFrg a Ha).
      - apply (aview_kept_out E5 _ (w_H W3) mem3 (ms_mem msf) HFrf a Ha).
        intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_36, ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia.
      - intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_36, ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia. }
    assert (PSTm : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msg) a).
    { intros a Hp. eapply apresent_grows; [exact HGg|]. eapply apresent_grows; [exact HGf | exact Hp]. }
    pose proof (rkk_end_mem_xR cx i n (S r') F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms1) _ _ ly2 S2 W2 mem2' _ _ out2' (ms_mem ms2) ly3 S3 W3 mem3 _ l1 l2 _ _ (ms_mem msg) _ _
      HB HJ2 HGNA HROMA HPKA HFRA HLKA HLSA M32A M88A HPT HJs3 HAK3 (ex_intro _ restG (conj HPa3 HPb3)) HO3 KEEPS PRESS
      HAR6 EL2 EL3 HFS KF
      ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia)
      ltac:(unfold gsp1, RIG_FRAME; lia)
      HERR HPRF KST PSTm VNf VKf HJ4) as RKK.
    cbv zeta in RKK.
    destruct RKK as (RLY & ROUT & RSRC & RSRC1 & RDRS & RGS & RPRE & RPSH & RROM & RPK & RFR & RLK & RLS & RM32 & RM88).
    (* the meter and the live bytes *)
    assert (HMLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HMF).
    pose proof (rkb_ge_cap_le c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as Hcg1.
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { rewrite (rkb_bb_free ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL2 EL3).
      rewrite (rkb_bb_out ly1 S1 ly2 S2 cap2 out2 _ out2' restG HPa3 HPb3 ltac:(lia)).
      rewrite (rkb_ge_net c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl0). lia. }
    destruct (rkb_gin_end cx i n r' F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)
      ly3 S3 W3 (ms_mem msg) out2' HB HGNA HPT HMLE HBB HRMf HCN3 RLY ROUT RSRC RSRC1 RDRS RGS
      (rkb_perm_end cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent (S r') ly1 S1 W1 (ms_mem ms1)
        ly2 S2 ly3 S3 l1 l2 restG out2' _ HGNA HND1 HPa3 HPb3 EL2 EL3) RPRE RPSH) as (f' & HGNf).
    (* the registers *)
    pmkst HS.
    prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4. prreg HS (8%bv : bv 5) Z8.
    prreg HS (9%bv : bv 5) Z9. prreg HS (18%bv : bv 5) Z18. prreg HS (19%bv : bv 5) Z19. prreg HS (20%bv : bv 5) Z20.
    prreg HS (21%bv : bv 5) Z21. prreg HS (23%bv : bv 5) Z23. prreg HS (24%bv : bv 5) Z24. prreg HS (25%bv : bv 5) Z25.
    prreg_raw HS (22%bv : bv 5) Z22. prreg_raw HS (27%bv : bv 5) Z27.
    apply (KE r' W3 _ eq_refl).
    exists (ms_regs msg), ly3, S3, (ms_mem msg). eexists. eexists.
    exists F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, (swap_remove (0, [], []) n ks), (Ed ++ [k]), f',
      (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))),
      out2', (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite Z2, (EE5 2%nat 2%bv eq_refl); exact R3_2|].
      split; [rewrite Z3, (EE5 3%nat 3%bv eq_refl); exact R3_3|].
      split; [rewrite Z4, (EE5 4%nat 4%bv eq_refl); exact R3_4|].
      split; [rewrite Z8, (EE5 8%nat 8%bv eq_refl); exact R3_8|].
      split; [rewrite Z9, (EE5 9%nat 9%bv eq_refl); exact R3_9|].
      rewrite Z18, (EE5 18%nat 18%bv eq_refl); exact R3_18. }
    split; [rewrite Z19, (EE5 19%nat 19%bv eq_refl); exact R3_19|].
    split; [rewrite Z20, (EE5 20%nat 20%bv eq_refl); exact R3_20|].
    split; [rewrite Z21, (EE5 21%nat 21%bv eq_refl); exact R3_21|].
    split; [rewrite Z23, (EE5 23%nat 23%bv eq_refl); exact R3_23|].
    split.
    { rewrite Z22. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 18 0)) with (rk_sh 23).
      apply rk_sh_den; [rewrite (EE5 23%nat 23%bv eq_refl); exact R3_23 | rewrite (EE5 18%nat 18%bv eq_refl); exact R3_18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split; [rewrite Z24, (EE5 24%nat 24%bv eq_refl); exact R3_24|].
    split; [rewrite Z25, (EE5 25%nat 25%bv eq_refl); exact R3_25|].
    split.
    { rewrite Z27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 18 0)) with (rk_sh 25).
      apply rk_sh_den; [rewrite (EE5 25%nat 25%bv eq_refl); exact R3_25 | rewrite (EE5 18%nat 18%bv eq_refl); exact R3_18 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia. }
    split; [exact RM32|].
    split; [exact RM88|].
    split; [exists fpos, []; split; [rewrite EHp0; exact HJ4|]; split; [exact RROM|]; split; [exact RPK|]; split; [exact RFR | exact RLK]|].
    split; [exact RLS|].
    exact HGNf.
  + exfalso. rewrite (rk_branch_lt E5 (SOff 21 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hc0.
    * apply Z.ltb_ge in Hc0. lia.
    * cbn [sv_denot]. rewrite (EE5 21%nat 21%bv eq_refl), R3_21. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    * cbn [sv_denot]. rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia). reflexivity.
    * lia.
    * lia. }
  (* ======== n + 1 = nheld: the ended key was the last; held[nheld - 1] is held[n] ======== *)
  assert (Hnl : (length ks - 1)%nat = n) by lia.
  assert (Ekl : nth (length ks - 1) ks (0, [], []) = k) by (rewrite Hnl; reflexivity).
  destruct (rk_st_gen (A_rig_inner + 104) [] W3 ly3 S3 regs3 mem3 md3 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1)
    (Z.of_nat n) (Z.of_nat (length ks)) key HAR6 R3_2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32)
    R3_18 R3_19 R3_21 R3_23 R3_22 R3_25 R3_27 HinT3 ltac:(clear - HSA; lia) HTend
    ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
    Hinh3 Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; unfold alloc_ceiling in *; lia)
    DSH3 VH3 VN3 VK3) as [HS5 SHOK5].
  remember (Eimg (Ereg regs3 (map (Z_to_bv 64) ([hp; hp + 8 * Z.of_nat n; key; Z.of_nat (length ks)] ++ [])))) as E5 eqn:HE5.
  assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; apply Eimg_env).
  assert (EE5 : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E5 k0 = getr regs3 r0)
    by (intros k0 r0 Hk0; subst E5; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
  assert (E5_32 : ew E5 32 = Z_to_bv 64 hp) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (E5_33 : ew E5 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  assert (E5_34 : ew E5 34 = Z_to_bv 64 key) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
  assert (E5_35 : ew E5 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E5; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
  clear HE5.
  assert (BV5_25 : base_val E5 (Some 25%nat) = gSA cx i + 40)
    by (cbn [base_val]; rewrite (EE5 25%nat 25%bv eq_refl), R3_25; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_23 : base_val E5 (Some 23%nat) = gSA cx i + 48)
    by (cbn [base_val]; rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia).
  assert (BV5_33 : base_val E5 (Some 33%nat) = hp + 8 * Z.of_nat n)
    by (cbn [base_val]; rewrite E5_33; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1; unfold alloc_ceiling in *; lia).
  assert (ALI : sv_denot E5 rk_EXPR = sv_denot E5 (SOff 33 0)).
  { rewrite (rk_expr_den E5 hp (Z.of_nat (length ks)) E5_32 E5_35)
      by (clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hks26 Hn C1; unfold alloc_ceiling in *; lia).
    cbn [sv_denot]. rewrite E5_33, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. lia. }
  pose proof (st_ok_pi_add_alias E5 _ _ rk_EXPR (SOff 33 0) HS5 ALI) as HSd.
  clear HS HS5. rename HSd into HS.
  paj_run_tok_xR RUNG HS HJ4 SHOK5 rk_Bspan.
  { apply (rk_awr_win E5 _ _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)); [| | rk_win_tac | |].
    - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
    - rewrite E5_33. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
      change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
    - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
  rename ms into msf, mat into matf, HF into HFf, HFr into HFrf, HG into HGf.
  psrr_branch_tok RUNG BRR HS SHOK5 rk_Bspan.
  + exfalso. rewrite (rk_branch_lt E5 (SOff 21 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hc0.
    * apply Z.ltb_lt in Hc0. lia.
    * cbn [sv_denot]. rewrite (EE5 21%nat 21%bv eq_refl), R3_21. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    * cbn [sv_denot]. rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia). reflexivity.
    * lia.
    * lia.
  + (* the entry's last key ended: to 0x82f44 *)
    paj_run_to_tok_xR RUNTOG HS HJ4 SHOK5 rk_Bspan A_rig_step.
    { apply (rk_awr_win E5 _ _ _ _ _ _ _ _ _ (gSA cx i) (hp + 8 * Z.of_nat n)); [| | rk_win_tac | |].
      - rewrite (EE5 23%nat 23%bv eq_refl), R3_23. apply unsigned_lit_small. clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE, alloc_ceiling in *. lia.
      - rewrite E5_33. apply unsigned_lit_small. clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1. unfold alloc_ceiling in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ (gxG0 cx) ATABLE a HP0X HinT3 NGT).
        change (req_size ATABLE) with 896. clear - Ha HTend HSA. unfold AENT, ATABLE in *. lia.
      - intros a Ha. apply (rk_wr_live cx ly3 S3 _ hp (re_kh e1) a HP0X Hinh3 NGH). clear - Ha Hkh Hrk2 Hn. lia. }
    rename ms into msg, mat into matg, HF into HFg, HFr into HFrg, HG into HGg.
    pose proof (st_ok_pi_region_nth E5 _ _ 1 (YP09.mkRegion (Some 23%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 (-1)))]) HS eq_refl) as HRf2.
    pose proof (st_ok_pi_region_nth E5 _ _ 2 (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))]) HS eq_refl) as HRf3.
    cbn [ms_mem restrict] in HRf2, HRf3.
    assert (Lks' : Z.of_nat (length (swap_remove (0, [], []) n ks)) = Z.of_nat (length ks) - 1)
      by (rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
    assert (VNf : val_mem SEGS (arm W3 (ms_mem msg)) (gSA cx i + 48) 4 (Z.of_nat (length (swap_remove (0, [], []) n ks)))).
    { rewrite Lks'.
      pose proof (field_of_region E5 _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) HRf2
        ltac:(rewrite (EE5 23%nat 23%bv eq_refl), R3_23; apply unsigned_lit_small; clear - HTend HSA HT4096 HTceil C1; unfold AENT, ATABLE, alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_35, unsigned_lit_small by (clear - Hks26; lia); reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hks26 Hn; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    assert (VKf : val_mem SEGS (arm W3 (ms_mem msg)) (hp + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], [])))).
    { rewrite Ekl.
      pose proof (field_of_region E5 _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 34 0) key HRf3
        ltac:(rewrite E5_33; apply unsigned_lit_small; clear - Hh4096 Hhceil Hkh Hrk1 Hrk2 Hn C1; unfold alloc_ceiling in *; lia)
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite E5_34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; clear - Hk4096 Hkceil Hrq1 Hrq2 C1; unfold alloc_ceiling in *; lia)) as V.
      rewrite Z.add_0_r in V. exact V. }
    assert (KST : forall a, 0 <= a < 2 ^ 64 -> ~ (gsp1 cx - DRAIN_STK_x <= a < gsp1 cx) -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) (ms_mem msg) a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha _ H1 H2.
      rewrite (aview_kept_out E5 _ (w_H W3) (ms_mem msf) (ms_mem msg) HFrg a Ha).
      - apply (aview_kept_out E5 _ (w_H W3) mem3 (ms_mem msf) HFrf a Ha).
        intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia.
      - intros (r0 & Hin & Hr). rk_in_tac Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
        rewrite ?BV5_25, ?BV5_23, ?BV5_33 in Hr; lia. }
    assert (PSTm : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msg) a).
    { intros a Hp. eapply apresent_grows; [exact HGg|]. eapply apresent_grows; [exact HGf | exact Hp]. }
    pose proof (rkk_end_mem_xR cx i n 0 F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 (ms_mem ms1) _ _ ly2 S2 W2 mem2' _ _ out2' (ms_mem ms2) ly3 S3 W3 mem3 _ l1 l2 _ _ (ms_mem msg) _ _
      HB HJ2 HGNA HROMA HPKA HFRA HLKA HLSA M32A M88A HPT HJs3 HAK3 (ex_intro _ restG (conj HPa3 HPb3)) HO3 KEEPS PRESS
      HAR6 EL2 EL3 HFS KF
      ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia)
      ltac:(unfold gsp1, RIG_FRAME; lia)
      HERR HPRF KST PSTm VNf VKf HJ4) as RKK.
    cbv zeta in RKK.
    destruct RKK as (RLY & ROUT & RSRC & RSRC1 & RDRS & RGS & RPRE & RPSH & RROM & RPK & RFR & RLK & RLS & RM32 & RM88).
    assert (HMLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HMF).
    pose proof (rkb_ge_cap_le c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as Hcg1.
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { rewrite (rkb_bb_free ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL2 EL3).
      rewrite (rkb_bb_out ly1 S1 ly2 S2 cap2 out2 _ out2' restG HPa3 HPb3 ltac:(lia)).
      rewrite (rkb_ge_net c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl0). lia. }
    pose proof (rkb_gout_end cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 (ms_mem ms1)
      ly3 S3 W3 (ms_mem msg) out2' HB HGNA HPT HMLE HBB HRMf HCN3 RLY ROUT RSRC RSRC1 RDRS RGS
      (rkb_perm_end cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent 0 ly1 S1 W1 (ms_mem ms1)
        ly2 S2 ly3 S3 l1 l2 restG out2' _ HGNA HND1 HPa3 HPb3 EL2 EL3) RPRE RPSH) as HGOf.
    pmkst HS.
    prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4. prreg HS (8%bv : bv 5) Z8.
    prreg HS (9%bv : bv 5) Z9. prreg HS (18%bv : bv 5) Z18. prreg HS (20%bv : bv 5) Z20.
    apply (KR W3 _).
    exists (ms_regs msg), ly3, S3, (ms_mem msg). eexists. eexists.
    exists F, FL, (qd ++ [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]),
      (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))),
      out2', (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite Z2, (EE5 2%nat 2%bv eq_refl); exact R3_2|].
      split; [rewrite Z3, (EE5 3%nat 3%bv eq_refl); exact R3_3|].
      split; [rewrite Z4, (EE5 4%nat 4%bv eq_refl); exact R3_4|].
      split; [rewrite Z8, (EE5 8%nat 8%bv eq_refl); exact R3_8|].
      split; [rewrite Z9, (EE5 9%nat 9%bv eq_refl); exact R3_9|].
      rewrite Z18, (EE5 18%nat 18%bv eq_refl); exact R3_18. }
    split; [rewrite Z20, (EE5 20%nat 20%bv eq_refl); exact R3_20|].
    split; [exact RM88|].
    split; [exact Hi|].
    split; [exists fpos, []; split; [rewrite EHp0; exact HJ4|]; split; [exact RROM|]; split; [exact RPK|]; split; [exact RFR | exact RLK]|].
    split; [exact RLS|].
    exact HGOf.
Qed.
(* W_rig_key.v:5861 rig_keys_proof at R *)
Theorem rig_keys_proof_xR : rig_keys_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
unfold rig_keys_stmt_xR. intros KEY cx i n r. revert n.
induction r as [|r IH]; intros n W1 c1 HB HC HI HE.
- apply (KEY cx i n 0%nat W1 c1 HB HC HI); [intros r' W2 c2 Hr; discriminate Hr | intros r' W2 c2 Hr; discriminate Hr | exact HE].
- apply (KEY cx i n (S r) W1 c1 HB HC HI).
  + intros r' W2 c2 Hr H2. injection Hr as <-. exact (IH (S n) W2 c2 HB HC H2 HE).
  + intros r' W2 c2 Hr H2. injection Hr as <-. exact (IH n W2 c2 HB HC H2 HE).
  + exact HE.
Qed.
End wR.
End c.
End b.
End a.
