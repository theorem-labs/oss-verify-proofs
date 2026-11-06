(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment KEY of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan 0x82f08 .. 0x830c4: one held key of the inner loop), against the frozen segment interface
   lib/B/W_relay_instance_gone_cx.v rig_key_stmt.  A new walk of B's code (UBSan trap mode); the proof shape, the
   model, budget, keep and representation lemmas (lib/B/W_rig_key_b / _k / _r.v) follow k3's image-A
   lib/A/W_rig_key.v (a working branch 8cfff43c147); the seats are lib/B/W_rig_key_s.v, the end arm's
   calls lib/B/W_rig_key_e.v, its cut lib/B/W_rig_key_c.v.
   C3 (the peak form; the image-A twin's re-fit of lib/A/W_rig_key.v, mirrored): each key's gesture_end takes its room
   from the remaining trace's prefix (W_rig_key_b.v rkb_ge_room), and after the key the live bytes move by the NET
   change of its gesture_end (W_rig_key_b.v rkb_ge_net: g_out's growth) less the freed |key| + 1. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), the RIGX round on
   image B, as the image-A twin's RIG_x round (lib/A/W_rig_key.v, a Theorem Labs lane f4cd818e98d): KEY over any allocator
   relation ARx with its laws and the room record RP, against the cx file's generic Section
   (lib/B/W_relay_instance_gone_cx.v, commit 258ee8f57ad; its Section c copied below).  Every ARx state of this walk
   is read at the empty head set (HP0: ARh below, with Local wrappers of the laws), so each journal runs from [] to
   [] at the kit's RIG_STK_x (= RIG_STK + 128); GLIVE's head sets are [] (rk_jhp0, rk_gxHp).  The runs are
   paj_run_x_x / paj_run_to_x_x.  strncmp at astrncmp_realizes_x; gesture_end by lib/B/W_rig_key_e.v rk_ge (ge_spec_x)
   with its room premise rp_RM RP S1 (ge's MT_rk charge + 1 + the room the rest of the trace owes, rk_krn) and its
   count premise cnt_ok_pk RP ge_pk, both from GIN's gbud (lib/B/W_rig_key_b.v rk_room); the free by rk_free
   (afree_cf_rule_c_x) with gesture_end's room post rp_RM (1 + rk_krn) and cnt_ok (the live counts after gesture_end
   are at most one above GIN's: rkc_cnt_out_le); after the key, gbud's room is the free's post and its counts follow
   from the key's count change (rkc_end_cnt) in rkb_gin_end / rkb_gout_end.  The journal's image clause exempts PST:
   the image bytes kept through gesture_end's journal take `~ Exists (in_zr a) PST` (rk_keep_img).  The fake frame
   lies off image B's band by rk_frm_off_imgB_x below (W_frame_b.v frm_off_imgB over ARx). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_key_b W_rig_key_k W_rig_key_r W_rig_key_s W_rig_key_e W_rig_key_c.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
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
(* ---- The Section hypotheses of lib/B/W_relay_instance_gone_cx.v, copied (the names are the contracts'). ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP: the image cover IMGC (frm_off_imgP_x; image B's
   bound 0x5fc000, W_kit_x.v's IMGC); a live block's size is non-negative (W_kit_x.v's BLKN); the owned-low law OWNLOW,
   the model invariant WFx with its law WFL, and the two facts the twins read off model_laws / stack_malloc_progressP
   (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
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
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src (PB_fr on AsanUbsan discharges both by vm_compute, as the image-A twin's
   HH44 / HH45) *)
Hypothesis HH41 : VAL (A_HI 41) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH42 : VAL (A_HI 42) = rg_src RG + RIG_HI_SRC.
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
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx, as W_drain_cx_x.v states it): a held key is
   represented over its |text| + 1 bytes (ruling (A)); a word read of a key to the end of its last granule is
   visible *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP).  snprintf: a Theorem Labs lane's statement at fuzz_reply's
   addresses (W_sites.v asnprintf_realizes, its twin W_sites_x.v asnprintf_realizes_x), which the snprintf chain
   (RT_pf_vf.v snprintf_chain_ok, through a Theorem Labs lane's evt -> SRr bridge) discharges. *)
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
(* snprintf's stack-protector cells (see the header): the GOT word, a fact of every ARx state (at ARi0: the AR fact,
   am_const); the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the canary's bytes are image bytes (seg_rom SEGS at FR_GUARD .. + 8 is Some 0), so aview reads them in EVERY state
   through mbyte's seg_rom fallback: aguard_ok's second half needs nothing carried (a Theorem Labs lane's ruling; a Theorem Labs lane's
   pin measurement).  PB_fr decides it by vm_compute. *)
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the two literals of the snprintf call, in W7's dlit_at form (W_drain_cx.v:175): the bytes in .rodata, read-only,
   their shadow as W3's ashp over ARx (never zero shadow: a literal's last granule is partial), the granule's tail
   bytes *)
(* RIG_FMT and glit_at_x (ashp over ARx, W_contract_x.v ashp_x) are the cx file's definitions *)
Hypothesis HLIT17 : glit_at_x ARx 17 (RIG_FMT ++ [0]).
Hypothesis HLIT18 : glit_at_x ARx 18 (RelayModel.K_GESTURE ++ [0]).
(* " end\0" (.str.4, A_lit_end5 = A_OBJ 28) in the same form, for gesture_end's / gestures_end's garr8 premise and its
   ashp (instance: W_shadow_pin_fr.v ashp_end5_5_fr): bytes, in_rom, ashp, the granule's tail; HEND5L above gives the
   bytes alone *)
Hypothesis HLIT28 : glit_at_x ARx 28 ([32; 101; 110; 100] ++ [0]).
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x, the literals and " end\0"), and no byte of the
   relay's and the output's global cells (G_RIG, and the cells of HRGP that G_RIG does not name: g_src, g_nsrc,
   g_capsrc, g_send_max, g_client, g_send_dead).  At PST := [] both hold trivially (image A's PSTR / PSTG). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

#[local] Set Default Proof Using "All".

#[local] Notation rkb_live_gen := (W_rig_key_b.rkb_live_gen B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_live_pos := (W_rig_key_b.rkb_live_pos B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_live_ctl := (W_rig_key_b.rkb_live_ctl B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_live_dr := (W_rig_key_b.rkb_live_dr B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_live_sends := (W_rig_key_b.rkb_live_sends B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_live_rel := (W_rig_key_b.rkb_live_rel B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_live_gin := (W_rig_key_b.rkb_live_gin B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sends_app := (W_rig_key_b.rkb_sends_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_bytes_app := (W_rig_key_b.rkb_ge_bytes_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sl_O_len := (W_rig_key_b.rkb_sl_O_len B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sends_key := (W_rig_key_b.rkb_sends_key B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_O_len := (W_rig_key_b.rkb_ge_O_len B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_tr_max_nonneg := (W_rig_key_b.rkb_tr_max_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_tr_app := (W_rig_key_b.rkb_tr_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_tr_free := (W_rig_key_b.rkb_tr_free B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sizes_cost := (W_rig_key_b.rkb_sizes_cost B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sizes_app := (W_rig_key_b.rkb_sizes_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_er_tr := (W_rig_key_b.rkb_er_tr B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_er_eq := (W_rig_key_b.rkb_er_eq B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_cost_head := (W_rig_key_b.rkb_cost_head B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_slr_cost := (W_rig_key_b.rkb_slr_cost B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_slr_sizes := (W_rig_key_b.rkb_slr_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_slr_er := (W_rig_key_b.rkb_slr_er B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_slcr_nonneg := (W_rig_key_b.rkb_slcr_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sl_cap_ge := (W_rig_key_b.rkb_sl_cap_ge B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_slt_cost := (W_rig_key_b.rkb_slt_cost B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_slt_sizes := (W_rig_key_b.rkb_slt_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_tr_cost := (W_rig_key_b.rkb_ge_tr_cost B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_cost_nonneg := (W_rig_key_b.rkb_ge_cost_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_cap_nonneg := (W_rig_key_b.rkb_ge_cap_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_no_nonneg := (W_rig_key_b.rkb_ge_no_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_cap_le := (W_rig_key_b.rkb_ge_cap_le B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_net := (W_rig_key_b.rkb_ge_net B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ker_er := (W_rig_key_b.rkb_ker_er B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ker_eq := (W_rig_key_b.rkb_ker_eq B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ker_sizes := (W_rig_key_b.rkb_ker_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ker_step := (W_rig_key_b.rkb_ker_step B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gkrest_nil := (W_rig_key_b.rkb_gkrest_nil B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gkrest_sizes := (W_rig_key_b.rkb_gkrest_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gkrest_step := (W_rig_key_b.rkb_gkrest_step B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_grow_ok := (W_rig_key_b.rkb_grow_ok B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_seen_sizes := (W_rig_key_b.rkb_seen_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_lines_sizes := (W_rig_key_b.rkb_lines_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_push_ok := (W_rig_key_b.rkb_push_ok B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_drain_ok := (W_rig_key_b.rkb_drain_ok B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_fold5_nonneg := (W_rig_key_b.rkb_fold5_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_xks_nonneg := (W_rig_key_b.rkb_xks_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gone_sizes := (W_rig_key_b.rkb_gone_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_forall_skipn := (W_rig_key_b.rkb_forall_skipn B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gbase_facts := (W_rig_key_b.rkb_gbase_facts B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_grest_sizes := (W_rig_key_b.rkb_grest_sizes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_mok := (W_rig_key_b.rkb_mok B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gbud_end := (W_rig_key_b.rkb_gbud_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_ge_room := (W_rig_key_b.rkb_ge_room B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_bb_out := (W_rig_key_b.rkb_bb_out B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_bb_free := (W_rig_key_b.rkb_bb_free B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_geik_pass := (W_rig_key_b.rkb_geik_pass B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_geik_end := (W_rig_key_b.rkb_geik_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_geik_done := (W_rig_key_b.rkb_geik_done B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gbase_len := (W_rig_key_b.rkb_gbase_len B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_firstn_snoc := (W_rig_key_b.rkb_firstn_snoc B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_combine_app := (W_rig_key_b.rkb_combine_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gdone_snoc := (W_rig_key_b.rkb_gdone_snoc B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_rel_app := (W_rig_key_b.rkb_rel_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_rel_one := (W_rig_key_b.rkb_rel_one B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gin_pass := (W_rig_key_b.rkb_gin_pass B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gout_pass := (W_rig_key_b.rkb_gout_pass B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_aview_mod := (W_rig_key_k.rkk_aview_mod B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_wr := (W_rig_key_k.rkk_wr B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_bv := (W_rig_key_k.rkk_bv B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_view_mod := (W_rig_key_k.rkk_view_mod B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_view_hi := (W_rig_key_k.rkk_view_hi B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_view_lo := (W_rig_key_k.rkk_view_lo B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_kept_hi := (W_rig_key_k.rkk_kept_hi B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_kept_lo := (W_rig_key_k.rkk_kept_lo B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_vm := (W_rig_key_k.rkk_vm B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_ceil := (W_rig_key_k.rkk_ceil B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_kept_c := (W_rig_key_k.rkk_kept_c B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_akept := (W_rig_key_k.rkk_akept B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_blk := (W_rig_key_k.rkk_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_img := (W_rig_key_k.rkk_img B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_inG := (W_rig_key_k.rkk_inG B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_glob := (W_rig_key_k.rkk_glob B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_j4 := (W_rig_key_k.rkk_j4 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_slot_loc := (W_rig_key_k.rkk_slot_loc B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_len_recs := (W_rig_key_k.rkk_len_recs B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_len_ptrs := (W_rig_key_k.rkk_len_ptrs B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_alist := (W_rig_key_k.rkk_alist B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_asrc := (W_rig_key_k.rkk_asrc B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_aentry := (W_rig_key_k.rkk_aentry B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_arelay := (W_rig_key_k.rkk_arelay B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_aout := (W_rig_key_k.rkk_aout B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_asrc_m := (W_rig_key_k.rkk_asrc_m B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_aothers := (W_rig_key_k.rkk_aothers B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_drsrc := (W_rig_key_k.rkk_drsrc B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_digits := (W_rig_key_k.rkk_digits B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_pre_len := (W_rig_key_k.rkk_pre_len B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_jar := (W_rig_key_k.rkk_jar B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_gin := (W_rig_key_k.rkk_gin B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_live := (W_rig_key_k.rkk_live B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkk_lslots := (W_rig_key_k.rkk_lslots B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_ablocks_nodup := (W_rig_key_r.rk_ablocks_nodup B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_garr8_aview := (W_rig_key_r.rk_garr8_aview B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_pw_in := (W_rig_key_r.rk_pw_in B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_blk_apart := (W_rig_key_r.rk_blk_apart B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_mod_sp := (W_rig_key_r.rk_mod_sp B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_mod_sa := (W_rig_key_r.rk_mod_sa B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_pw_app := (W_rig_key_r.rk_pw_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_frame_blk_apart := (W_rig_key_r.rk_frame_blk_apart B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_nodup_app_disj := (W_rig_key_r.rk_nodup_app_disj B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_nodup_app_r := (W_rig_key_r.rk_nodup_app_r B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_view_garr8 := (W_rig_key_r.rk_view_garr8 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_garr8_kv := (W_rig_key_r.rk_garr8_kv B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_perm_entry := (W_rig_key_r.rk_perm_entry B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_wr_blk := (W_rig_key_r.rk_wr_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_blk_not_img := (W_rig_key_r.rk_blk_not_img B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_hull := (W_rig_key_r.rk_hull B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_vm2 := (W_rig_key_r.rk_vm2 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_sll3_add8 := (W_rig_key_r.rk_sll3_add8 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_branch_lt := (W_rig_key_r.rk_branch_lt B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_nodup_mid := (W_rig_key_r.rk_nodup_mid B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_nth_le_bytes := (W_rig_key_r.rkr_nth_le_bytes B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_garr8_le := (W_rig_key_r.rkr_garr8_le B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_le_garr8 := (W_rig_key_r.rkr_le_garr8 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_view := (W_rig_key_r.rkr_view B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_bz0 := (W_rig_key_r.rkr_bz0 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_bz_nz := (W_rig_key_r.rkr_bz_nz B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_nth_key := (W_rig_key_r.rkr_nth_key B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_nth_key_end := (W_rig_key_r.rkr_nth_key_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_garr8_app3 := (W_rig_key_r.rkr_garr8_app3 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_kp_app := (W_rig_key_r.rkr_kp_app B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_key_ptrs_len := (W_rig_key_r.rkr_key_ptrs_len B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_key_ptr := (W_rig_key_r.rkr_key_ptr B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_set_nth_mid := (W_rig_key_r.rkr_set_nth_mid B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_nth_last := (W_rig_key_r.rkr_nth_last B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_swap_shape := (W_rig_key_r.rkr_swap_shape B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_eb_shape := (W_rig_key_r.rkr_eb_shape B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_pw_perm := (W_rig_key_r.rkr_pw_perm B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_pw_mid := (W_rig_key_r.rkr_pw_mid B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_pw_mid4 := (W_rig_key_r.rkr_pw_mid4 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_disj := (W_rig_key_r.rkr_disj B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_fp_blk := (W_rig_key_r.rkr_fp_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_entry_at := (W_rig_key_r.rkr_entry_at B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_arelay_swap := (W_rig_key_r.rkr_arelay_swap B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_agree := (W_rig_key_r.rkr_agree B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_first_key := (W_rig_key_r.rkr_first_key B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_first_pre := (W_rig_key_r.rkr_first_pre B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_digits := (W_rig_key_r.rkr_digits B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_digits_le := (W_rig_key_r.rkr_digits_le B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_digits11 := (W_rig_key_r.rkr_digits11 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkr_pre_nz := (W_rig_key_r.rkr_pre_nz B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_sh_den := (W_rig_key_s.rk_sh_den B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_shok := (W_rig_key_s.rk_shok B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_seat := (W_rig_key_s.rk_seat B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_end5 := (W_rig_key_e.rk_end5 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_callS := (W_rig_key_e.rk_callS B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_keep_img := (W_rig_key_e.rk_keep_img B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_keep_high := (W_rig_key_e.rk_keep_high B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_keep_blk := (W_rig_key_e.rk_keep_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_keep_frm := (W_rig_key_e.rk_keep_frm B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_ly_top := (W_rig_key_e.rk_ly_top B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_fp_spares := (W_rig_key_e.rk_fp_spares B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_disj := (W_rig_key_e.rk_disj B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_not_owned := (W_rig_key_e.rk_not_owned B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_free := (W_rig_key_e.rk_free B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_achain := (W_rig_key_e.rk_achain B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_achainp := (W_rig_key_e.rk_achainp B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_ge := (W_rig_key_e.rk_ge B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_aout_facts := (W_rig_key_e.rk_aout_facts B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_fp_blk := (W_rig_key_e.rk_fp_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sends_cap_nonneg := (W_rig_key_b.rkb_sends_cap_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sends_cons := (W_rig_key_b.rkb_sends_cons B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gin_end := (W_rig_key_b.rkb_gin_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gout_end := (W_rig_key_b.rkb_gout_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_fp_orig := (W_rig_key_e.rk_fp_orig B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk3_shok := (W_rig_key_s.rk3_shok B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_seat3 := (W_rig_key_s.rk_seat3 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_entry_keys_self := (W_rig_key_c.rkc_entry_keys_self B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_recs_len := (W_rig_key_c.rkc_recs_len B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_key_ptrs_len := (W_rig_key_c.rkc_key_ptrs_len B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_alist_fp_blk := (W_rig_key_c.rkc_alist_fp_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_asrc_fp_blk := (W_rig_key_c.rkc_asrc_fp_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_aentry_fp_sub := (W_rig_key_c.rkc_aentry_fp_sub B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_aentry_fp_blk := (W_rig_key_c.rkc_aentry_fp_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_aout_fp := (W_rig_key_c.rkc_aout_fp B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_kept_trans := (W_rig_key_c.rkc_kept_trans B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_aothers_kept := (W_rig_key_c.rkc_aothers_kept B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_srcs_in := (W_rig_key_c.rkc_srcs_in B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_len_gps := (W_rig_key_c.rkc_len_gps B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_gps_nth := (W_rig_key_c.rkc_gps_nth B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_done_blks := (W_rig_key_c.rkc_done_blks B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_wr_img := (W_rig_key_c.rkc_wr_img B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_abk_img := (W_rig_key_c.rkc_abk_img B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_abk_blk := (W_rig_key_c.rkc_abk_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_writable_view := (W_rig_key_c.rkc_writable_view B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_abk_vis := (W_rig_key_c.rkc_abk_vis B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_win := (W_rig_key_c.rkc_win B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_lyF := (W_rig_key_c.rkc_lyF B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_view_some := (W_rig_key_c.rkc_view_some B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_zall_nth := (W_rig_key_c.rkc_zall_nth B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_zpw_nth := (W_rig_key_c.rkc_zpw_nth B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_notSL := (W_rig_key_c.rkc_notSL B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_out_cell := (W_rig_key_c.rkc_out_cell B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_end := (W_rig_key_c.rkc_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_end2 := (W_rig_key_c.rkc_end2 B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_room := (W_rig_key_b.rk_room B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_cnt_out_le := (W_rig_key_b.rkc_cnt_out_le B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkc_end_cnt := (W_rig_key_b.rkc_end_cnt B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).

(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state this walk meets has the head set [], so the walk states its facts at ARh (= ARx at []) and
   each journal from [] to [] (a callee's post state is brought to [] as it arrives).  The wrappers keep the AR walk's
   argument order: rk_alb is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN). *)
#[local] Notation ARh ly S W mem md := (ARx ly S (@nil Z) W mem md).
Local Lemma rk_jhp0 : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> Hp' = [].
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (HP0 _ _ _ _ _ _ (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
Qed.
Local Lemma rk_jAR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
ARh ly' S' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
exact (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
Local Lemma rk_alb : forall ly S W mem md p n, ARh ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
Local Definition rk_alf ly S W mem md cid pos (H : ARh ly S W mem md) := alx_frames _ _ _ LAWS ly S [] W mem md cid pos H.
Local Definition rk_fb ly S W mem md cid pos (H : ARh ly S W mem md) :=
  frames_bounds_x SEGS B ARx LAWS ly S [] W mem md cid pos H.
Local Definition rk_rab ly S W mem md p m a n (H : ARh ly S W mem md) :=
  range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md p m a n H.
Local Definition rk_shv ly S W mem md p m d n (H : ARh ly S W mem md) :=
  shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md p m d n H.
Local Definition rk_amr ly S W mem md p m a n (H : ARh ly S W mem md) :=
  YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly S [] W mem md p m a n H.
(* the entry's head set is empty too (GBASE's afn_pre_x states ARx at gxHp) *)
Local Lemma rk_gxHp : forall cx, GBASE B ARx MT RP MMAX RG cx -> gxHp cx = [].
Proof. intros cx HB. destruct HB as ((HAR & _) & _). exact (HP0 _ _ _ _ _ _ HAR). Qed.
(* W_frame_b.v frm_off_imgB over ARx (as lib/B/W_rig_pro.v rgp_frm_off_imgB_x): a live fake frame lies off image B's
   [0x10000, 0x5fc000) - at or above the image's top (the image law alx_img), which IMGC puts at or above 0x5fc000
   (W_frame_x.v frm_off_imgP_x states image A's top 0x5fb000, too weak for B's objects) *)
Local Lemma rk_frm_off_imgB_x : forall ly S Hp (W : world SEGS) mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [_ C2].
pose proof (proj2 (alx_img _ _ _ LAWS ly S Hp W mem md HAR) cid pos Hin) as Hf.
right. lia.
Qed.

Let RUN := paj_run_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RIG B RG) HGRIG 0 [].
Let BR := paj_branch (PI := PI).

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

(* the runs of KEY's seat write nothing: every region of rk_regions has an empty write window *)
Lemma rk_nowin : forall E' ss' H (mA mB : word -> option byte),
frame_of E' (ss_mem ss') (mrestrict H mA) (mrestrict H mB) -> ss_mem ss' = rk_regions ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H mB a = aview SEGS H mA a.
Proof.
intros E' ss' H mA mB HFr Hm a Ha. apply (aview_kept_out E' _ H mA mB HFr a Ha).
rewrite Hm. intros (r0 & Hin & Hr). cbn [rk_regions In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma rk_awr : forall E G STK sp0 FP bl0 blc ly own, awr_ok_x E rk_regions G 0 [] STK sp0 FP bl0 blc ly own.
Proof.
intros E G STK sp0 FP bl0 blc ly own a (r & Hin & Hr). cbn [rk_regions In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.



Ltac rkc_rs := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  cbn [In ss_mem ss_k3a ss_k3b rk3a_regions rk3b_regions] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
     first [ left; apply Z.leb_le; reflexivity | right; left; split; [reflexivity | split; reflexivity]
           | right; right; split; [reflexivity | split; reflexivity] ] |]);
  try destruct Hr.

Theorem rig_key_proof : rig_key_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
unfold rig_key_stmt. intros cx i n r W1 c1 HB HCTX HI KP KE KR.
destruct HI as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 &
  ks & Ed & f & c2 & O2 & cap2 & out2 & spent & -> & HRB & R19 & R22 & R20 & R23 & R27 & R24 & R25 & R18 & M80 &
  HLV & HLS & HGN).
pose proof HLV as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
assert (EHp1 : Hp1 = []) by (eapply rk_jhp0; exact HJ). subst Hp1.
pose proof HB as (HPRE0 & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof (rk_gxHp cx HB) as EHp0. rewrite EHp0 in HJ, HPRE0.
pose proof HJ as HJ0.
pose proof HGN as (Hi & Hqd & HREL & HDR & HSND & Hks & Hf & HGK & HRLY & HOUT & HSRC & HOPEN & HDRS & HGS & HPERM &
  HPRE & HPSH & HBUD).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H21).
pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof HJ as (HSTK & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SP1 : spZ regs1 = gsp0 cx - 224) by (rewrite Hsp1; reflexivity).
assert (SPR : alloc_ceiling + 12912 <= gsp0 cx - 4320 /\ gsp0 cx <= 2 ^ 47) by (unfold gsp0 in *; rewrite WS in Hslo; lia).
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
(* the frame (1, fpos) *)
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (rk_alf _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (rk_fb _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in *.
assert (HF8 : 0 <= F / 8 /\ 8 * (F / 8) <= F).
{ split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
pose proof (rk_seat W1 ly1 S1 regs1 m1 md1 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
  (Z.of_nat (length ks)) key (F + 32) A_rig_inner HAR1 Hsp1 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
  ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32) ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
  H9 H21 R19 R22 R20 R23 R27 R25 R18 HinT ltac:(clear - HSA; lia) HTend
  ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
  Hinh Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; lia)
  ltac:(clear - HF4096 HFceil C1; lia)
  DSH Mhp Mnh (Mslot n Hn) L88) as [HS SHOK].
clear DSH.
unfold cfg_at. change (w64 (BASE + A_rig_inner)) with (Z_to_bv 64 (BASE + A_rig_inner)).
remember (Eimg (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (F + 32)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk0; subst E; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (F + 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (HAE : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (F + 32))) E)
  by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
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
(* ---- 0x82f08 -> strncmp (key, F + 32, |prefix|) 0x82f5c: the shadow check of s->held, held + 8 n and its UBSan
   traps (0x82f18 decided by the seated condition, the rest by the seat's facts), held[n]'s shadow check, the key,
   88(sp) = F + 32 ---- *)
paj_run_tok_x RUN HS HJ SHOK rk_Bspan.
{ apply rk_awr. }
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2.
assert (M01 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a)
  by (intros a Ha; exact (rk_nowin E _ (w_H W1) m1 (ms_mem ms0) HFr0 eq_refl a Ha)).
assert (P01 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; eapply apresent_grows; [exact HG0 | exact Hp]).
assert (HSPc : spZ (ms_regs ms0) = gsp0 cx + -224).
{ unfold spZ at 1. rewrite QSP, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). lia. }
pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
destruct (rkr_pre_nz cx) as (NZp & Lp16 & Lp27).
clear DTK DHK DFT DFH DFK HTHd.
assert (GkT : garr8 SEGS (arm W1 (ms_mem ms0)) key (bzs (kt ++ [Z_to_bv 8 0]))).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ Gk). intros b Hb.
  unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
  apply M01. lia. }
assert (GpT : garr8 SEGS (arm W1 (ms_mem ms0)) (F + 32) (gpre cx ++ [0])).
{ apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ HPRE). intros b Hb.
  rewrite length_app in Hb. cbn [length] in Hb. apply M01. lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 key) by (rewrite QA0, E34; reflexivity).
assert (QA1' : getr (ms_regs ms0) 11 = w64 (F + 32)) by (rewrite QA1, E36; reflexivity).
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
  apply M01. clear - Hb HF8 HFceil C1; unfold shadow_addr, SHADOW_OFF in *; lia. }
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
    + clear - Hkceil Hrq2 C1. lia.
    + clear - HFceil C1 Lp27. lia.
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
      pose proof (Hsegs a Hii) as Ha. rewrite M01; [exact (HROM1 a Hin) | clear - Ha C5; unfold kLowMemEnd in *; lia].
    + split.
      * eapply (rk_amr ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2 Lk; lia].
      * clear - HFapp C1 C4 C5. unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
cbv beta. intros W2 c2x _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HA0 & Hfr2 & Hpres2).
(* ---- back at 0x82f60: a0 = strncmp's result ---- *)
pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
destruct (rk_alb ly1 S1 W1 mem2 _ _ _ HAR3 HinT) as (_ & _ & _ & _ & HTpres3 & _ & _).
destruct (rk_alb ly1 S1 W1 mem2 _ _ _ HAR3 Hinh) as (_ & _ & _ & _ & Hhpres3 & _ & _).
jafter_call_keep_pi HS 37%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  assert (BV23 : base_val E (Some 23%nat) = gSA cx i + 48)
    by (cbn [base_val]; rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
  assert (BV25 : base_val E (Some 25%nat) = gSA cx i + 40)
    by (cbn [base_val]; rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
  assert (BV33 : base_val E (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
  assert (BV9 : base_val E (Some 9%nat) = gsp1 cx)
    by (cbn [base_val]; rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; unfold gsp1, RIG_FRAME; lia).
  repeat apply Forall_cons; [| | | | apply Forall_nil];
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV23, ?BV25, ?BV33, ?BV9;
   [ intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr2;
     [ clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn SPR C1; unfold gsp1, RIG_FRAME, AENT, ATABLE in *; lia
     | exact (fun H => H)
     | clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn SPR C1; unfold gsp1, RIG_FRAME, AENT, ATABLE, ESTACK in *; lia ]
   | intros a Ha _; lia ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 37 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall k0, (k0 < 37)%nat -> ew Ea k0 = ew E k0) by (intros k0 Hk0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hk0).
assert (HAEa : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (F + 32))) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOKa : sh_ok SEGS rk_Bx rk_SH Ea (mrestrict (w_H W1) mem2)).
{ apply (rk_shok Ea W1 ly1 S1 mem2 _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HAR3).
  - rewrite OLDa by lia. rewrite (EE 21%nat 21%bv eq_refl). exact H21.
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
psrr_branch_tok RUN BR HS SHOKa rk_Bspan.
- (* ======== a0 <> 0: the key lacks the prefix (pass) ======== *)
  assert (Ha0ne : getr regs2 10 <> w64 0).
  { intros Hz. rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia.
    rewrite (U_atom Ea 41 0) in Hc; [discriminate Hc | rewrite <- R10a; exact Hz | lia]. }
  assert (HPF : has_prefix (gpre cx) (bzs kt) = false).
  { destruct (has_prefix (gpre cx) (bzs kt)) eqn:Hh; [exfalso|reflexivity].
    apply (proj2 (rkr_agree W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp)) in Hh.
    exact (Ha0ne (proj2 HA0 Hh)). }
  (* 0x83098: nheld's shadow check (fast path), nheld, n += 1, 8 n, the loop test *)
  paj_run_tok_x RUN HS HJ2 SHOKa rk_Bspan.
  { apply rk_awr. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  assert (GR : forall k0 (r0 : bv 5), (k0 < 37)%nat -> Z.of_nat k0 = bv_unsigned r0 -> ew Ea k0 = getr regs1 r0)
    by (intros k0 r0 Hk0 Hr0; rewrite OLDa by exact Hk0; apply EE; exact Hr0).
  psrr_branch_tok RUN BR HS SHOKa rk_Bspan.
  + (* n + 1 < nheld: through 0x82f04 (s6 = 8 (n + 1)) to the next key *)
    paj_run_to_tok_x RUNTO HS HJ2 SHOKa rk_Bspan A_rig_inner.
    { apply rk_awr. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    assert (Hn1 : (S n < length ks)%nat).
    { rewrite (rk_branch_lt Ea (SOff 20 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_lt in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 20%nat 20%bv eq_refl), R20 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    destruct r as [|r']; [exfalso; lia|].
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { intros a Ha Hns.
      rewrite (rk_nowin Ea _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 eq_refl a Ha).
      rewrite (rk_nowin Ea _ (w_H W1) mem2 (ms_mem ms1) HFr1 eq_refl a Ha).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (21%bv : bv 5) T21.
    prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
    prreg_raw HS (19%bv : bv 5) T19. prreg_raw HS (22%bv : bv 5) T22. prreg_raw HS (20%bv : bv 5) T20.
    prreg_raw HS (27%bv : bv 5) T27. prreg_raw HS (18%bv : bv 5) T18.
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
      rewrite T21, (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21. }
    split.
    { rewrite T19. cbn [sv_denot]. rewrite (GR 20%nat 20%bv ltac:(lia) eq_refl), R20. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, rk_sll3_add8 by lia. f_equal. lia. }
    split.
    { rewrite T22. cbn [sv_denot]. rewrite (GR 20%nat 20%bv ltac:(lia) eq_refl), R20. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, rk_sll3_add8 by lia. f_equal. lia. }
    split.
    { rewrite T20. cbn [sv_denot]. rewrite (GR 20%nat 20%bv ltac:(lia) eq_refl), R20. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia. }
    split; [rewrite T23, (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23|].
    split.
    { rewrite T27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 21 0)) with (rk_sh 23).
      apply rk_sh_den; [rewrite (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23 | rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split; [rewrite T24, (GR 24%nat 24%bv ltac:(lia) eq_refl); exact R24|].
    split; [rewrite T25, (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25|].
    split.
    { rewrite T18. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 21 0)) with (rk_sh 25).
      apply rk_sh_den; [rewrite (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25 | rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M80].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; unfold gsp1, RIG_FRAME in *; lia]. }
    split; [exact (rkk_live cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGN3.
  + (* n + 1 >= nheld: the entry's last key passed; the loop ends *)
    assert (Hn1 : (length ks <= S n)%nat).
    { rewrite (rk_branch_lt Ea (SOff 20 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_ge in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 20%nat 20%bv eq_refl), R20 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    assert (r = 0%nat) by lia. subst r.
    paj_run_to_tok_x RUNTO HS HJ2 SHOKa rk_Bspan A_rig_step.
    { apply rk_awr. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { intros a Ha Hns.
      rewrite (rk_nowin Ea _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 eq_refl a Ha).
      rewrite (rk_nowin Ea _ (w_H W1) mem2 (ms_mem ms1) HFr1 eq_refl a Ha).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (21%bv : bv 5) T21.
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
      rewrite T21, (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M80].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; unfold gsp1, RIG_FRAME in *; lia]. }
    split; [exact Hi|].
    split; [exact (rkk_live cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGO.
- (* ======== a0 = 0: the key has the prefix (end) ======== *)
  assert (Ha0z : getr regs2 10 = w64 0).
  { rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rv. change (bv_modulus 64) with (2 ^ 64) in Rv.
    rewrite (U_atom Ea 41 (bv_unsigned (getr regs2 10))) in Hc; [| rewrite <- R10a, Z_to_bv_bv_unsigned; reflexivity | exact Rv].
    rewrite <- (Z_to_bv_bv_unsigned _ (getr regs2 10)), Hc. reflexivity. }
  assert (HPT : has_prefix (gpre cx) (bzs kt) = true)
    by exact (proj1 (rkr_agree W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp) (proj1 HA0 Ha0z)).
  (* 0x82f64: mv a0,s10; gesture_end (key) at 0x82f68 *)
  paj_run_to_tok_x RUNTO HS HJ2 SHOKa rk_Bspan AF_fr_gesture_end.
  { apply rk_awr. }
  rename ms into msg, mat into matg, HF into HFg, HFr into HFrg, HG into HGg.
  pmkst HS.
  prreg HS (1%bv : bv 5) G1. prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
  prreg HS (8%bv : bv 5) G8. prreg HS (10%bv : bv 5) G10.
  (* the cut's predicates at gesture_end's call: the strncmp call and the runs wrote only below sp *)
  assert (KEEPg : rkk_KEEP cx W1 m1 (ms_mem msg)).
  { intros a Ha Hns.
    rewrite (rk_nowin Ea _ (w_H W1) mem2 (ms_mem msg) HFrg eq_refl a Ha).
    rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
    exact (M01 a Ha). }
  assert (PRESg : rkk_PRES W1 m1 (ms_mem msg)).
  { intros a Hp. eapply apresent_grows; [exact HGg|]. apply Hpres2. exact (P01 a Hp). }
  pose proof (rkk_gin cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 m1 md1 k1 (ms_mem msg) HB HJ0 HFR HGN KEEPg PRESg) as HGNg.
  pose proof (rkk_live cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem msg) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPg PRESg) as HLVg.
  pose proof (rkk_lslots cx F W1 m1 (ms_mem msg) HLS KEEPg) as HLSg.
  pose proof HLVg as (fposg & Hpg & HJg & HROMg & HPKg & HFRg & HLKg).
  pose proof HFRg as (_ & _ & _ & _ & _ & _ & _ & HSVg).
  pose proof HGNg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOUTg & _).
  pose proof (rkk_ceil cx HB) as HCEIL.
  destruct (rk_achain cx ly1 W1 (ms_mem msg) HB HSVg
    ltac:(eapply rk_ly_top; exact HJ2)
    ltac:(intros a Ha; eapply (rk_keep_high (G_RIG B RG)); [exact HGRIG | exact HJ2 | lia | rewrite WS; lia])) as (ch1 & Hch1).
  destruct (rk_aout_facts _ _ _ _ _ _ _ _ _ _ HOUTg) as (Hmx2 & _ & Hcd2).
  assert (Hcap2 : 0 <= cap2) by (destruct Hcd2 as [(-> & _) | (? & _)]; lia).
  destruct (rkb_gbase_facts cx HB) as (Hmx & _).
  (* entry i's key run: the key ended now, then the rest *)
  destruct f as [|f0]; [exfalso; lia|].
  pose proof (rkb_geik_end f0 (gpre cx) n ks Hn HPT) as EGK.
  set (ks' := swap_remove (0, [], []) n ks) in *.
  set (Er' := fst (geik_loop f0 (gpre cx) n ks')) in *.
  pose proof HBUD as HBUD0. cbv zeta in HBUD0. rewrite EGK in HBUD0. cbn [fst] in HBUD0. fold k in HBUD0.
  remember (sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (k :: Er'))) as SS eqn:ESS in HBUD0.
  destruct SS as [[c3x O3] cap3]. cbn beta iota in HBUD0.
  assert (HGs : rk_sizes (grest cx (S i) (Z.of_nat (length O3)) cap3)).
  { apply rkb_grest_sizes; [exact HB | lia |].
    pose proof (rkb_sends_cap_nonneg (gxmx cx) (ge_bytes (k :: Er')) c2 O2 cap2 Hcap2) as Hc3. rewrite <- ESS in Hc3. exact Hc3. }
  assert (HLV2 : sl_live c2 1 = sl_live (gxc cx) 1)
    by exact (rkb_live_gin cx i n r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent ly1 S1 W1 m1 HGN).
  assert (Hxl : 0 < Z.of_nat (length kt)) by lia.
  destruct (rkb_ge_room cx ly1 S1 spent c2 (Z.of_nat (length O2)) cap2 k Er' _ HBUD0 HGs HLV2 ltac:(lia) ltac:(lia) Hcap2 Hxl)
    as (RM1 & RM2 & RM3).
  fold kt in RM1, RM2, RM3.
  (* the room record's premises of gesture_end (at kr := S (rk_krn ..)) and of the free (the counts at most one above
     GIN's), from GIN's gbud *)
  destruct (rk_room cx i n r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent ly1 S1 W1
    (ms_mem msg) HB HGNg HPT) as (_ & _ & _ & _ & _ & RMg & CNg & CNle).
  assert (ROOMg : ge_room MMAX (blocks_bytes S1) c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))).
  { unfold ge_room, ge_tr. rewrite (rkb_live_pos c2 (Z.of_nat (length kt)) Hxl). split; [exact RM1 | exact RM2]. }
  assert (Hgc0 : 0 <= ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)))
    by (apply rkb_ge_cost_nonneg; lia).
  pose proof (mo_free_nonneg MT MLAW) as Hmf.
  assert (MOKg : mo_ok MT S1 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))))
    by (apply (rkb_mok cx ly1 S1 spent _ _ HB HBUD0 Hgc0); lia).
  (* the key is not the output buffer *)
  assert (HinO2 : cap2 <> 0 -> In (out2, cap2) XG).
  { intros Hcz. unfold XG. right. rewrite !app_assoc. apply in_or_app. right. unfold aout_blks.
    rewrite (proj2 (Z.eqb_neq cap2 0) Hcz). left. reflexivity. }
  assert (HinKA : In (key, Z.of_nat (length kt) + 1)
    (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))))).
  { apply in_concat. exists (aentry_blks (entry_keys e1 ks)). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. right. cbn [re_keys entry_keys].
      apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). apply nth_In. exact Hn. }
  assert (HinKX : In (key, Z.of_nat (length kt) + 1) XG) by (unfold XG; right; apply in_or_app; left; exact HinKA).
  assert (HKO : key <> out2).
  { destruct Hcd2 as [(_ & -> & _) | (Hc0 & _ & HinO)]; [lia|].
    intros Heq.
    assert (Hne : (key, Z.of_nat (length kt) + 1) <> (out2, cap2)).
    { intros Hcq. pose proof HNDP as HND2. apply List.NoDup_cons_iff in HND2 as [_ HND2].
      apply (rk_nodup_app_disj _ _ (key, Z.of_nat (length kt) + 1) HND2 HinKA).
      rewrite Hcq. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq cap2 0) ltac:(lia)). left; reflexivity. }
    destruct (rk_blk_apart ly1 S1 W1 m1 md1 _ _ HAR1 Hink HinO Hne) as [Hd | Hd]; cbn [fst snd] in Hd;
    pose proof (req_size_pos cap2 ltac:(lia)); lia. }
  change (BASE + 14288) with (BASE + AF_fr_gesture_end).
  eapply SRr_bind.
  { eapply (rk_ge W1 (ms_regs msg) (ms_mem msg) _ (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (gxmd cx)
      [(1, fpos)] ly1 S1 _ (Z_to_bv 64 (BASE + A_rig_ge_ret)) ch1 c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 kt key
      (Z.of_nat (length kt) + 1) HJ2).
    - unfold spZ at 1. rewrite G2, OLDa, (EE 2%nat 2%bv eq_refl) by lia. fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia.
    - replace (gsp0 cx) with (2 * (gsp0 cx / 32) * 16) by (pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)); lia). apply Z_mod_mult.
    - rewrite G3, OLDa, (EE 3%nat 3%bv eq_refl), Hgp1 by lia. exact Hgp.
    - rewrite G4, OLDa, (EE 4%nat 4%bv eq_refl), Htp1 by lia. exact Htp.
    - exact G1.
    - unfold A_rig_ge_ret, A_rig_inner, AF_fr_relay_instance_gone. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold A_rig_ge_ret, A_rig_inner, AF_fr_relay_instance_gone. rewrite unsigned_lit_small by lia. lia.
    - replace (gsp0 cx - 224) with (gsp1 cx) by (unfold gsp1, RIG_FRAME; lia).
      replace (s0Z (ms_regs msg)) with (gsp0 cx); [exact Hch1|].
      unfold s0Z. rewrite G8, OLDa, (EE 8%nat 8%bv eq_refl), H8 by lia. unfold w64. rewrite unsigned_lit_small by (unfold gsp0 in *; lia). reflexivity.
    - rewrite G10, OLDa, E34 by lia. reflexivity.
    - exact HOUTg.
    - apply (rk_garr8_kv (w_H W1) (w_H W1) m1 (ms_mem msg) _ _ Gk). intros b Hb.
      unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
      apply KEEPg; lia.
    - exact NZk.
    - exact Lk.
    - exact Hink.
    - exact HKO.
    - lia.
    - exact (rk_end5 W1 (ms_mem msg) HROMg).
    - exact HROMg.
    - exact ROOMg.
    - exact MOKg.
    - exact RMg.
    - exact CNg.
    - intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n0 & Hpin & Hpa).
      unfold aout_blks in Hpin. destruct (Z.eqb_spec cap2 0) as [Hz | Hnz]; [destruct Hpin|].
      destruct Hpin as [Hpe | []]. injection Hpe as <- <-.
      exact (rk_fp_blk cx ly1 S1 W1 m1 md1 XG out2 cap2 a HAR1 HP0X HPX (HinO2 Hnz) Hpa). }
  cbv beta. intros W2 c2x Hwle2 (ly2 & S2 & regs3 & mem3 & md3 & kg & out3 & -> & HJ3 & (ksl & HJsl) & HP3 & HAK3 & HM3 &
    HRMge & (restG & HPa & HPb) & HO3).
  (* ---- back at 0x82f6c ---- *)
  pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARge.
  assert (HGSL : gx_ok SEGS B (G_SL B RG)) by exact (gx_ok_sub SEGS B _ _ (rig_G_SL_RIG B RG) HGRIG).
  set (cap3' := ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))) in *.
  set (XGa := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx))).
  assert (HXG : XG = XGa ++ aout_blks cap2 out2) by (unfold XG, XGa; rewrite <- app_comm_cons, <- !app_assoc; reflexivity).
  assert (HPq1 : Permutation (ablocks B ly1 S1) (XGa ++ aout_blks cap2 out2 ++ gxrest cx))
    by (rewrite app_assoc, <- HXG; exact HPX).
  assert (HND1X : List.NoDup (XGa ++ aout_blks cap2 out2 ++ gxrest cx)) by exact (Permutation_NoDup HPq1 HND1).
  assert (HPR : Permutation restG (XGa ++ gxrest cx)).
  { apply (Permutation_app_inv_l (aout_blks cap2 out2)). eapply perm_trans; [apply Permutation_sym; exact HPa|].
    eapply perm_trans; [exact HPq1|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (HPq2 : Permutation (ablocks B ly2 S2) (XGa ++ aout_blks cap3' out3 ++ gxrest cx)).
  { eapply perm_trans; [exact HPb|]. eapply perm_trans; [apply Permutation_app_head; exact HPR|].
    rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  pose proof (rk_ablocks_nodup _ _ _ _ _ HARge) as HNDge.
  assert (HNDgX : List.NoDup (XGa ++ aout_blks cap3' out3 ++ gxrest cx)) by exact (Permutation_NoDup HPq2 HNDge).
  assert (INX1 : forall b, In b XGa -> In b (ablocks B ly1 S1))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPq1)); apply in_or_app; left; exact Hb).
  assert (INX2 : forall b, In b XGa -> In b (ablocks B ly2 S2))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPq2)); apply in_or_app; left; exact Hb).
  assert (NOX1 : forall b, In b XGa -> ~ In b (aout_blks cap2 out2)).
  { intros b Hb Ho. apply (rk_nodup_app_disj XGa _ b HND1X Hb). apply in_or_app. left. exact Ho. }
  assert (HinT1X : In (gxG0 cx, ATABLE) XGa) by (left; reflexivity).
  assert (Hinh1X : In (hp, re_kh e1) XGa) by (right; apply in_or_app; left; exact HinHP).
  assert (Hink1X : In (key, Z.of_nat (length kt) + 1) XGa) by (right; apply in_or_app; left; exact HinKA).
  pose proof (INX2 _ HinT1X) as HinT2. pose proof (INX2 _ Hinh1X) as Hinh2. pose proof (INX2 _ Hink1X) as Hink2.
  (* what gesture_end kept: the caller's blocks other than the output buffer, the stack above its window *)
  assert (KGEa : forall b, In b XGa -> forall a, fst b <= a < fst b + req_size (snd b) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W1) (ms_mem msg) a).
  { intros [p nb] Hb a Ha. cbn [fst snd] in Ha. replace a with (p + (a - p)) by lia.
    apply (rk_keep_blk (G_SL B RG) 0 [] GE_STK (gsp0 cx - 224) (ablocks_fp (aout_blks cap2 out2)) ly1 S1 W1 (ms_mem msg) _ []
      ly2 S2 W2 mem3 md3 ksl p nb (a - p) HGSL HJsl (INX1 _ Hb) (INX2 _ Hb) ltac:(lia)).
    intros Hcf. apply inFP_ablocks_fp_inv in Hcf as (q & m & Hqin & Hqa).
    assert (Hne : (p, nb) <> (q, m)) by (intros Heq; rewrite Heq in Hb; exact (NOX1 _ Hb Hqin)).
    assert (Hqin1 : In (q, m) (ablocks B ly1 S1))
      by (apply (Permutation_in _ (Permutation_sym HPq1)); apply in_or_app; right; apply in_or_app; left; exact Hqin).
    destruct (rk_disj ly1 S1 W1 m1 md1 p nb q m HAR1 (INX1 _ Hb) Hqin1 Hne); lia. }
  assert (KGEh : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (gsp0 cx - 224 - GE_STK <= a < gsp0 cx - 224) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W1) (ms_mem msg) a).
  { intros a Ha Hno. apply (rk_keep_high (G_SL B RG) 0 [] GE_STK (gsp0 cx - 224) _ ly1 S1 W1 (ms_mem msg) _ []
      ly2 S2 W2 mem3 md3 ksl HGSL HJsl a Ha). lia. }
  assert (BVa : forall k0 v, (k0 < 37)%nat -> ew E k0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val Ea (Some k0) = v).
  { intros k0 v Hk0 Hv Hr. cbn [base_val]. rewrite OLDa by exact Hk0. rewrite Hv. apply unsigned_lit_small. exact Hr. }
  jafter_call_keep_pi HS 53%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2; 3]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    assert (BV23a : base_val Ea (Some 23%nat) = gSA cx i + 48)
      by (apply BVa; [lia | rewrite (EE 23%nat 23%bv eq_refl); exact R23 | unfold AENT, ATABLE in *; lia]).
    assert (BV25a : base_val Ea (Some 25%nat) = gSA cx i + 40)
      by (apply BVa; [lia | rewrite (EE 25%nat 25%bv eq_refl); exact R25 | unfold AENT, ATABLE in *; lia]).
    assert (BV33a : base_val Ea (Some 33%nat) = hp + 8 * Z.of_nat n) by (apply BVa; [lia | exact E33 | lia]).
    assert (BV9a : base_val Ea (Some 9%nat) = gsp1 cx)
      by (apply BVa; [lia | rewrite (EE 9%nat 9%bv eq_refl); exact H9 | unfold gsp1, RIG_FRAME; lia]).
    repeat apply Forall_cons; [| | | | apply Forall_nil];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV23a, ?BV25a, ?BV33a, ?BV9a;
     [ intros a Ha; apply (mbyte_of_aview SEGS);
       first [ apply (KGEa _ HinT1X); cbn [fst snd]; change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia
             | apply (KGEa _ Hinh1X); cbn [fst snd]; lia
             | apply KGEh; [unfold gsp1, RIG_FRAME in *; lia | assert (GE_STK = 16544) by reflexivity; unfold gsp1, RIG_FRAME in *; lia] ]
     | intros a Ha _; lia ]). }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 53 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall k0, (k0 < 53)%nat -> ew Eb k0 = ew Ea k0) by (intros k0 Hk0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hk0).
  clear HEb.
  assert (SHOKb : sh_ok SEGS rk_Bx rk_SH Eb (mrestrict (w_H W2) mem3)).
  { apply (rk_shok Eb W2 ly2 S2 mem3 _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HARge).
    - rewrite OLDb, OLDa by lia. rewrite (EE 21%nat 21%bv eq_refl). exact H21.
    - rewrite OLDb, OLDa by lia. rewrite (EE 23%nat 23%bv eq_refl). exact R23.
    - rewrite OLDb, OLDa by lia. rewrite (EE 25%nat 25%bv eq_refl). exact R25.
    - rewrite OLDb, OLDa by lia. exact E33.
    - exact HinT2.
    - clear - HSA. lia.
    - exact HTend.
    - exact Hinh2.
    - exact Hkh.
    - clear - Hn. lia. }
  (* 0x82f6c: the checks again, held[n], free (key) at 0x82fb4 *)
  paj_run_tok_x RUN HS HJ3 SHOKb rk_Bspan.
  { apply rk_awr. }
  rename ms into msf, mat into matf, HF into HFf, HFr into HFrf, HG into HGf.
  pmkst HS.
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (10%bv : bv 5) F10.
  prreg HS (9%bv : bv 5) F9. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
  prreg HS (23%bv : bv 5) F23. prreg HS (25%bv : bv 5) F25. prreg HS (24%bv : bv 5) F24.
  prreg_raw HS (18%bv : bv 5) F18. prreg_raw HS (22%bv : bv 5) F22. prreg_raw HS (27%bv : bv 5) F27.
  assert (KRf : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem3 a)
    by (intros a Ha; exact (rk_nowin Eb _ (w_H W2) mem3 (ms_mem msf) HFrf eq_refl a Ha)).
  assert (HSVf : g_saved cx W2 (ms_mem msf)).
  { intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem msg) (ms_mem msf) _ 8 _); [|exact (HSVg j Hj)].
    intros kk Hkk. assert (GE_STK = 16544) by reflexivity.
    rewrite KRf by (unfold gsp1, RIG_FRAME in *; lia). apply KGEh; unfold gsp1, RIG_FRAME in *; lia. }
  (* the free's caller context (GCTX): the entry's frame is below the layout top, so the chain at 0x82fb4 is the
     entry's chain under relay_instance_gone's frame record (gsp0, ra, s0) *)
  assert (TOP2 : gsp0 cx < ly_top (gxly cx) - 16) by (destruct HCTX as (HCT1 & _); unfold gsp0; clear - HCT1; lia).
  pose proof (rk_achainp cx ly2 W2 (ms_mem msf) HB HSVf
    ltac:(eapply rk_ly_top; exact HJ3)
    ltac:(intros a Ha; eapply (rk_keep_high (G_RIG B RG)); [exact HGRIG | exact HJ3 | lia | rewrite WS; lia]) TOP2) as Hch2.
  destruct HBUD0 as (Hle0 & Hsp0 & Hc0 & _).
  assert (MOKf : mo_ok MT S2 (mo_free MT))
    by exact (mok_station MT (gxS cx) S2 (tr_cost MT (gtr cx))
      (spent + ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))) (mo_free MT) MLAW HMOK
      (mo_le_trans MT MLAW _ _ _ _ _ Hle0 HM3) Hmf ltac:(lia)).
  rewrite (pal_free B TL).
  eapply SRr_bind.
  { eapply (rk_free (G_RIG B RG) W2 (ms_regs msf) (ms_mem msf) RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx)
      (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 _ _ key (Z.of_nat (length kt) + 1) (-224)
      (Z_to_bv 64 (BASE + A_rig_fr_ret)) ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx) HJ3).
    - exact Hink2.
    - rewrite F10, OLDb, OLDa, E34 by lia. reflexivity.
    - unfold spZ at 1. rewrite F2, OLDb, OLDa, (EE 2%nat 2%bv eq_refl) by lia. fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ASTACK. lia.
    - rewrite F3, OLDb, OLDa, (EE 3%nat 3%bv eq_refl), Hgp1 by lia. exact Hgp.
    - rewrite F4, OLDb, OLDa, (EE 4%nat 4%bv eq_refl), Htp1 by lia. exact Htp.
    - exact F1.
    - unfold A_rig_fr_ret, A_rig_inner, AF_fr_relay_instance_gone. apply ret_ok_codeptr_v; [lia | reflexivity].
    - apply (achain_chain_pre ly2 _ (gsp1 cx) (gsp0 cx) _ (ms_regs msf) Hch2).
      + unfold spZ. rewrite F2, OLDb, OLDa, (EE 2%nat 2%bv eq_refl) by lia. fold (spZ regs1). rewrite Hsp1.
        unfold gsp1, RIG_FRAME in *. lia.
      + unfold s0Z. rewrite F8, OLDb, OLDa, (EE 8%nat 8%bv eq_refl), H8 by lia. unfold w64.
        rewrite unsigned_lit_small by (unfold gsp0 in *; lia). reflexivity.
      + unfold raZ. rewrite F1. unfold A_rig_fr_ret, A_rig_inner, AF_fr_relay_instance_gone.
        rewrite unsigned_lit_small by lia. lia.
    - destruct HCTX as (_ & HCT2). replace (raZ (ms_regs msf)) with (A_rig_entryP + 792); [exact HCT2|].
      unfold raZ. rewrite F1. unfold A_rig_fr_ret, A_rig_inner, A_rig_entryP, A_rig_entry, AF_fr_relay_instance_gone.
      rewrite unsigned_lit_small by lia. ring.
    - intros Hin0 j Hj. exact (rk_fp_orig cx ly1 S1 W1 m1 md1 XG key (Z.of_nat (length kt) + 1) HAR1 HP0X HPX HinKX Hin0 j Hj).
    - exact MOKf.
    - exact HRMge.
    - apply CNle. intros P. exact (rkc_cnt_out_le P ly1 S1 ly2 S2 cap2 out2 _ out3 restG HPa HPb). }
  cbv beta. intros W3 cfr Hwle3 (ly3 & S3 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & EL1 & EL2) & Hfrm3 & HK4 & HM4 &
    HRMf & HE4 & HPK4).
  (* ---- back at 0x82fb8 ---- *)
  pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HARfr.
  (* the key's count change: gesture_end's send chain moves g_out's own count exactly, the free drops the key's block
     (lib/B/W_rig_key_b.v rkc_end_cnt) *)
  pose proof (fun P => rkc_end_cnt P c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))
    ly1 S1 ly2 S2 ly3 S3 out2 out3 restG l1 l2 key Hxl Hcap2 HPa HPb EL1 EL2) as HCN3.
  set (XGb := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx))).
  assert (HXab : Permutation XGa ((key, Z.of_nat (length kt) + 1) :: XGb)).
  { unfold XGa, XGb. eapply perm_trans;
      [apply perm_skip; apply Permutation_app_tail; exact (rk_perm_keys (map fst qd) (skipn (S i) (gxes cx)) e1 ks n Hn)|].
    cbn [app]. apply perm_swap. }
  assert (HPq3 : Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3' out3 ++ gxrest cx)).
  { rewrite EL2. apply Permutation_sym. apply Permutation_cons_app_inv with (a := (key, Z.of_nat (length kt) + 1)).
    rewrite <- EL1. eapply perm_trans; [|apply Permutation_sym; exact HPq2].
    change ((key, Z.of_nat (length kt) + 1) :: XGb ++ aout_blks cap3' out3 ++ gxrest cx)
      with (((key, Z.of_nat (length kt) + 1) :: XGb) ++ aout_blks cap3' out3 ++ gxrest cx).
    apply Permutation_app_tail. apply Permutation_sym. exact HXab. }
  assert (HNDb : List.NoDup ((key, Z.of_nat (length kt) + 1) :: XGb ++ aout_blks cap3' out3 ++ gxrest cx)).
  { apply (Permutation_NoDup (l := XGa ++ aout_blks cap3' out3 ++ gxrest cx)); [|exact HNDgX].
    change ((key, Z.of_nat (length kt) + 1) :: XGb ++ aout_blks cap3' out3 ++ gxrest cx)
      with (((key, Z.of_nat (length kt) + 1) :: XGb) ++ aout_blks cap3' out3 ++ gxrest cx).
    apply Permutation_app_tail. exact HXab. }
  assert (INX3 : forall b, In b XGb -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPq3)); apply in_or_app; left; exact Hb).
  assert (XbA : forall b, In b XGb -> In b XGa)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HXab)); right; exact Hb).
  assert (NKb : forall b, In b XGb -> b <> (key, Z.of_nat (length kt) + 1)).
  { intros b Hb Heq. apply List.NoDup_cons_iff in HNDb as [Hni _]. apply Hni. rewrite <- Heq. apply in_or_app. left. exact Hb. }
  (* every byte of a block the end arm kept, from the cut's state to after free *)
  assert (KALL : forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros [p nb] Hb a Ha. cbn [fst snd] in Ha.
    pose proof HK4 as (_ & K4b & _).
    destruct (rk_alb ly1 S1 W1 m1 md1 p nb HAR1 (INX1 _ (XbA _ Hb))) as (_ & Hp4 & Hpc & _).
    replace a with (p + (a - p)) by lia.
    rewrite (K4b p nb (a - p) (INX2 _ (XbA _ Hb)) ltac:(lia)).
    2: { intros Hka. destruct (rk_disj ly2 S2 W2 mem3 md3 p nb key (Z.of_nat (length kt) + 1) HARge (INX2 _ (XbA _ Hb)) Hink2 (NKb _ Hb)); lia. }
    replace (p + (a - p)) with a by lia.
    rewrite KRf by lia. rewrite (KGEa (p, nb) (XbA _ Hb) a ltac:(cbn [fst snd]; lia)).
    apply KEEPg; lia. }
  assert (HinT3X : In (gxG0 cx, ATABLE) XGb) by (left; reflexivity).
  assert (Hinh3X : In (hp, re_kh e1) XGb).
  { right. apply in_or_app. left. apply in_concat. exists (aentry_blks (entry_keys e1 ks')). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
      fold hp. destruct (Z.eqb_spec hp 0); [contradiction | left; reflexivity]. }
  assert (VKT : forall a, gxG0 cx <= a < gxG0 cx + 896 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a)
    by (intros a Ha; apply (KALL _ HinT3X); cbn [fst snd]; change (req_size ATABLE) with 896; exact Ha).
  assert (VKH : forall a, hp <= a < hp + re_kh e1 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a)
    by (intros a Ha; apply (KALL _ Hinh3X); cbn [fst snd]; lia).
  assert (Mhp4 : val_mem SEGS (arm W3 mem4) (gSA cx i + 40) 8 hp).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 8 _); [|exact Mhp].
    intros kk Hkk. apply VKT. unfold AENT, ATABLE in *. lia. }
  assert (Mnh4 : val_mem SEGS (arm W3 mem4) (gSA cx i + 48) 4 (Z.of_nat (length ks))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 4 _); [|exact Mnh].
    intros kk Hkk. apply VKT. unfold AENT, ATABLE in *. lia. }
  assert (Mkey4 : val_mem SEGS (arm W3 mem4) (hp + 8 * Z.of_nat n) 8 key).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 8 _); [|exact (Mslot n Hn)].
    intros kk Hkk. apply VKH. lia. }
  (* the registers at free's return: the loop head's, preserved by both calls *)
  assert (QV : forall (b : bv 5) rr, bv_unsigned b = rr -> acallee_saved rr -> getr regs4 b = getr (ms_regs msf) b)
    by (intros b rr Hb Hr; exact (rk_pres_reg (ms_regs msf) regs4 rr b HP4 Hb Hr)).
  assert (Q2 : spZ regs4 = gsp1 cx).
  { unfold spZ at 1. rewrite (QV 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia)), F2, OLDb, OLDa, (EE 2%nat 2%bv eq_refl) by lia.
    fold (spZ regs1). exact Hsp1. }
  assert (Q9 : getr regs4 9 = w64 (gsp1 cx))
    by (rewrite (QV 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia)), F9, OLDb, OLDa, (EE 9%nat 9%bv eq_refl) by lia; exact H9).
  assert (Q21 : getr regs4 21 = w64 SHADOW_OFF)
    by (rewrite (QV 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia)), F21, OLDb, OLDa, (EE 21%nat 21%bv eq_refl) by lia; exact H21).
  assert (Q19 : getr regs4 19 = w64 (8 * Z.of_nat n))
    by (rewrite (QV 19%bv 19 eq_refl ltac:(unfold acallee_saved; lia)), F19, OLDb, OLDa, (EE 19%nat 19%bv eq_refl) by lia; exact R19).
  assert (Q20 : getr regs4 20 = w64 (Z.of_nat n))
    by (rewrite (QV 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia)), F20, OLDb, OLDa, (EE 20%nat 20%bv eq_refl) by lia; exact R20).
  assert (Q23 : getr regs4 23 = w64 (gSA cx i + 48))
    by (rewrite (QV 23%bv 23 eq_refl ltac:(unfold acallee_saved; lia)), F23, OLDb, OLDa, (EE 23%nat 23%bv eq_refl) by lia; exact R23).
  assert (Q25 : getr regs4 25 = w64 (gSA cx i + 40))
    by (rewrite (QV 25%bv 25 eq_refl ltac:(unfold acallee_saved; lia)), F25, OLDb, OLDa, (EE 25%nat 25%bv eq_refl) by lia; exact R25).
  assert (Q22 : getr regs4 22 = w64 (8 * Z.of_nat n)).
  { rewrite (QV 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia)), F22. cbn [sv_denot].
    rewrite OLDb, OLDa, (EE 19%nat 19%bv eq_refl), R19 by lia. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (Q18 : getr regs4 18 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8)).
  { rewrite (QV 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia)), F18.
    apply rk_sh_den; [rewrite OLDb, OLDa, (EE 25%nat 25%bv eq_refl) by lia; exact R25
      | rewrite OLDb, OLDa, (EE 21%nat 21%bv eq_refl) by lia; exact H21 | unfold AENT, ATABLE in *; lia]. }
  assert (Q27 : getr regs4 27 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8)).
  { rewrite (QV 27%bv 27 eq_refl ltac:(unfold acallee_saved; lia)), F27.
    apply rk_sh_den; [rewrite OLDb, OLDa, (EE 23%nat 23%bv eq_refl) by lia; exact R23
      | rewrite OLDb, OLDa, (EE 21%nat 21%bv eq_refl) by lia; exact H21 | unfold AENT, ATABLE in *; lia]. }
  assert (HBLK : hp + re_kh e1 <= gSA cx i + 40 \/ gSA cx i + 52 <= hp).
  { pose proof (rk_blk_apart ly1 S1 W1 m1 md1 _ _ HAR1 HinT Hinh HTH) as HTHd2. cbn [fst snd] in HTHd2.
    change (req_size ATABLE) with 896 in HTHd2. clear - HTHd2 HTend HSA Hrk2. unfold AENT, ATABLE in *. lia. }
  pose proof (INX3 _ HinT3X) as HinT4. pose proof (INX3 _ Hinh3X) as Hinh4.
  (* the last key, held[nheld - 1] *)
  assert (Hnl : (length ks - 1 < length ks)%nat) by lia.
  pose proof (rkr_entry_at ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) (length ks - 1) HAR1 HRLY Hnl) as XL.
  cbv zeta in XL. destruct XL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HinkL & _).
  set (klast := key_addr (nth (length ks - 1) ks (0, [], []))) in *.
  destruct (rk_alb ly1 S1 W1 m1 md1 _ _ HAR1 HinkL) as (_ & HkL4096 & HkLceil & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text (nth (length ks - 1) ks (0, [], [])))) + 1) ltac:(lia)) as [HrL1 _].
  assert (MkL4 : val_mem SEGS (arm W3 mem4) (hp + 8 * (Z.of_nat (length ks) - 1)) 8 klast).
  { replace (Z.of_nat (length ks) - 1) with (Z.of_nat (length ks - 1)) by lia.
    apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 8 _); [|exact (Mslot _ Hnl)].
    intros kk Hkk. apply VKH. lia. }
  assert (AWT3 : forall own a, gSA cx i + 48 <= a < gSA cx i + 52 ->
    awr_byte RIG_STK_x (gsp0 cx) (gFP cx) (ablocks B (gxly cx) (gxS cx)) (ablocks B ly3 S3) ly3 own a).
  { intros own a Ha. apply (rk_wr_blk cx ly3 S3 W3 mem4 md4 (XGb ++ aout_blks cap3' out3) own (gxG0 cx) ATABLE a HARfr HP0X);
      [rewrite <- app_assoc; exact HPq3 | apply in_or_app; left; exact HinT3X | change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia]. }
  assert (AWH3 : forall own a, hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8 ->
    awr_byte RIG_STK_x (gsp0 cx) (gFP cx) (ablocks B (gxly cx) (gxS cx)) (ablocks B ly3 S3) ly3 own a).
  { intros own a Ha. apply (rk_wr_blk cx ly3 S3 W3 mem4 md4 (XGb ++ aout_blks cap3' out3) own hp (re_kh e1) a HARfr HP0X);
      [rewrite <- app_assoc; exact HPq3 | apply in_or_app; left; exact Hinh3X | lia]. }
  (* ---- the bytes the end arm keeps, from the cut's state to free's return ---- *)
  assert (Q3 : getr regs4 3 = getr (gxregs cx) 3)
    by (rewrite (QV 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia)), F3, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp1).
  assert (Q4 : getr regs4 4 = getr (gxregs cx) 4)
    by (rewrite (QV 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia)), F4, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia; exact Htp1).
  assert (Q8 : getr regs4 8 = w64 (gsp0 cx))
    by (rewrite (QV 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia)), F8, OLDb, OLDa, (EE 8%nat 8%bv eq_refl) by lia; exact H8).
  assert (Q24 : getr regs4 24 = w64 (Z.of_nat (length (gpre cx))))
    by (rewrite (QV 24%bv 24 eq_refl ltac:(unfold acallee_saved; lia)), F24, OLDb, OLDa, (EE 24%nat 24%bv eq_refl) by lia; exact R24).
  assert (PK14 : apres_kept B W1 m1 W3 mem4).
  { intros a Hiax Hox Hex Hpx. apply (HPK4 a Hiax Hox Hex). eapply apresent_grows; [exact HGf|].
    apply (HAK3 a Hiax Hox Hex). exact (PRESg a Hpx). }
  assert (PK24 : apres_kept B W2 mem3 W3 mem4).
  { intros a Hiax Hox Hex Hpx. apply (HPK4 a Hiax Hox Hex). eapply apresent_grows; [exact HGf | exact Hpx]. }
  pose proof HK4 as (K4h & K4b & K4i & K4f & _ & _).
  assert (HGE : GE_STK = 16544) by reflexivity.
  assert (KST4 : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros a Hax.
    rewrite (K4h a) by (clear - Hax SPR C1; unfold gsp1, RIG_FRAME, ASTACK, ESTACK in *; lia).
    rewrite KRf by (clear - Hax SPR C1; unfold gsp1, RIG_FRAME in *; lia).
    rewrite KGEh by (clear - Hax SPR C1 HGE; unfold gsp1, RIG_FRAME in *; lia).
    apply KEEPg; clear - Hax SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia. }
  assert (LF2 : ly_F ly2 = ly_F ly1) by exact (rkc_lyF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl).
  destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl) as (memS2 & HJi2 & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & Hfrs2 & _). cbn [app] in Hfrs2.
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
  assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
  assert (FNI : forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 -> ~ in_img SEGS a).
  { intros a Hax Hiax. pose proof (pa_segs_low a Hiax) as HLx. rewrite C5 in HLx.
    destruct Hax as [Hax | Hax]; [| rewrite SF in Hax; clear - Hax HLx HF8; lia].
    pose proof (rk_frm_off_imgB_x ly1 S1 [] W1 m1 md1 1 fpos HAR1 Hfin) as Hoffx. rewrite HFa in Hoffx.
    change (fs_frame_bytes 1) with 128 in Hoffx. pose proof (pa_img_range a Hiax) as HRx. clear - Hax Hoffx HRx. lia. }
  assert (FNB : forall p nb a, In (p, nb) (ablocks B ly1 S1) -> p <= a < p + req_size nb ->
     ~ (F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16)).
  { intros p nb a Hinx Hpax Hax. pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin Hinx) as Dx.
    change (fs_frame_bytes 1) with 128 in Dx. rewrite HFa in Dx.
    destruct (rk_alb _ _ _ _ _ p nb HAR1 Hinx) as (_ & _ & _ & Happx & _).
    destruct Hax as [Hax | Hax]; [clear - Hax Hpax Dx; lia|]. rewrite SF in Hax.
    exact (fshadow_not_app F 16 p (req_size nb) a ltac:(clear - HF4096; lia) ltac:(clear - HFceil C1; lia) Happx Hax Hpax). }
  assert (HinO1 : cap2 <> 0 -> In (out2, cap2) (ablocks B ly1 S1))
    by (intros Hczx; apply (Permutation_in _ (Permutation_sym HPX)); apply in_or_app; left; exact (HinO2 Hczx)).
  assert (NFP : forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 ->
    ~ inFP (ablocks_fp (aout_blks cap2 out2)) a).
  { intros a Hax Hfx. apply inFP_ablocks_fp_inv in Hfx as (p & nb & Hpinx & Hpax).
    unfold aout_blks in Hpinx. destruct (Z.eqb_spec cap2 0) as [Hzx | Hnzx]; [destruct Hpinx|].
    destruct Hpinx as [Hpex | []]. injection Hpex as <- <-. exact (FNB _ _ a (HinO1 Hnzx) Hpax Hax). }
  assert (KFR4 : forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros a Hax.
    assert (Hax' : F <= a < F + 128 \/ 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 16) by (rewrite <- SF; exact Hax).
    assert (Ha64x : 0 <= a < 2 ^ 64) by (clear - Hax' HF4096 HFceil C1 HF8; lia).
    assert (Hrngx : forall ly, ly_F ly = ly_F ly1 ->
      in_zr a (frame_rng ly (1, fpos)) \/ in_zr a (shadow_addr (frame_addr ly 1 fpos), fs_frame_bytes 1 / 8)).
    { intros ly Hlyx. assert (EFx : frame_addr ly 1 fpos = F) by (unfold frame_addr in *; rewrite Hlyx; exact HFa).
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFx. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      clear - Hax. lia. }
    rewrite (K4f 1 fpos a Hfin2 (Hrngx ly2 LF2)) by (intros Hkx; exact (FNB _ _ a Hink Hkx Hax)).
    rewrite KRf by exact Ha64x.
    rewrite (rk_keep_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a HJsl Hfin (Hrngx ly1 eq_refl) (NFP a Hax) Ha64x
      ltac:(intros Hgx; exact (FNI a Hax (proj1 (HGSL a Hgx))))).
    apply KEEPg; [exact Ha64x|]. clear - Hax' SPR C1 HFceil HF8. unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *. lia. }
  assert (KIM4 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros a Hiax Hox Hex Hpx Hgx. pose proof (pa_segs_low a Hiax) as HLx. rewrite C5 in HLx.
    assert (FPS : fp_spares (ablocks_fp (aout_blks cap2 out2)) a).
    { apply rk_fp_spares. intros b Hbx. unfold aout_blks in Hbx. destruct (Z.eqb_spec cap2 0) as [Hzx | Hnzx]; [destruct Hbx|].
      destruct Hbx as [<- | []]. cbn [fst]. destruct (rk_alb _ _ _ _ _ _ _ HAR1 (HinO1 Hnzx)) as (_ & Ho4x & _). clear - Ho4x. lia. }
    rewrite (K4i a Hiax Hox Hex). rewrite KRf by (clear - HLx; lia).
    rewrite (rk_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl a Hiax Hox Hex Hpx FPS Hgx).
    apply KEEPg; [clear - HLx; lia|]. clear - HLx SPR C1. unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *. lia. }
  assert (KO2i4 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W2) mem3 a).
  { intros a Hiax Hox. pose proof (pa_segs_low a Hiax) as HLx. rewrite C5 in HLx.
    rewrite <- (KRf a) by (clear - HLx; lia).
    destruct (Z_le_gt_dec (as_errno B) a) as [E1x|E1x]; [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [E2x|E2x]|].
    - pose proof (HE4 (a - as_errno B) ltac:(clear - E1x E2x; lia)) as HExx. replace (as_errno B + (a - as_errno B)) with a in HExx by ring. exact HExx.
    - exact (K4i a Hiax Hox ltac:(clear - E2x; lia)).
    - exact (K4i a Hiax Hox ltac:(clear - E1x; lia)). }
  assert (KO2b4 : forall a, cap3' <> 0 -> out3 <= a < out3 + req_size cap3' ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W2) mem3 a).
  { intros a Hcx Hax.
    assert (HinOa : In (out3, cap3') (aout_blks cap3' out3))
      by (unfold aout_blks; destruct (Z.eqb_spec cap3' 0) as [E0|E0]; [exfalso; exact (Hcx E0) | left; reflexivity]).
    assert (HinO2' : In (out3, cap3') (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym HPq2)). apply in_or_app. right. apply in_or_app. left. exact HinOa. }
    assert (NKO : (out3, cap3') <> (key, Z.of_nat (length kt) + 1)).
    { intros Heqx. apply (rk_nodup_app_disj XGa _ (key, Z.of_nat (length kt) + 1) HNDgX Hink1X). rewrite <- Heqx.
      apply in_or_app. left. exact HinOa. }
    destruct (rk_alb _ _ _ _ _ _ _ HARge HinO2') as (_ & Ho4x & Hocx & _).
    replace a with (out3 + (a - out3)) by ring.
    rewrite (K4b out3 cap3' (a - out3) HinO2' ltac:(clear - Hax; lia)).
    2: { intros Hkx. destruct (rk_disj ly2 S2 W2 mem3 md3 out3 cap3' key (Z.of_nat (length kt) + 1) HARge HinO2' Hink2 NKO) as [Dx|Dx];
         clear - Hkx Hax Dx; lia. }
    apply KRf. clear - Hax Ho4x Hocx C1. lia. }
  destruct r as [|r'].
  + pose proof (rk_seat3 true W3 ly3 S3 regs4 mem4 md4 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
    (Z.of_nat (length ks)) key klast A_rig_fr_ret HARfr Q2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32) ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    Q9 Q21 Q19 Q22 Q20 Q23 Q27 Q25 Q18 HinT4 ltac:(clear - HSA; lia) HTend ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
    Hinh4 Hkh Hks26 ltac:(cbn; lia) ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; lia)
    ltac:(clear - HkL4096 HkLceil HrL1 C1; lia) HBLK Mhp4 Mnh4 Mkey4 ltac:(intros X; discriminate X)) as [HS3 SHOK3].
    cbn beta iota in HS3.
    remember (Eimg (Ereg regs4 (rk_extra3 hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (hp + 8 * (Z.of_nat (length ks) - 1)) klast))) as Ec eqn:HEc.
    assert (HEIc : img_env VAL A_LIM Ec) by (subst Ec; apply Eimg_env).
    assert (Ec32 : ew Ec 32 = Z_to_bv 64 hp) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    assert (Ec33 : ew Ec 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 1)).
    assert (Ec35 : ew Ec 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 3)).
    assert (Ec36 : ew Ec 36 = Z_to_bv 64 (hp + 8 * (Z.of_nat (length ks) - 1))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 4)).
    assert (Ec19 : ew Ec 19 = Z_to_bv 64 (8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl); exact Q19).
    assert (Ec20 : ew Ec 20 = Z_to_bv 64 (Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 20 20%bv eq_refl); exact Q20).
    assert (Ec23 : bv_unsigned (ew Ec 23) = gSA cx i + 48) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 23 23%bv eq_refl), Q23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
    assert (Ec33u : bv_unsigned (ew Ec 33) = hp + 8 * Z.of_nat n) by (rewrite Ec33; apply unsigned_lit_small; lia).
    assert (EEc : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew Ec k0 = getr regs4 r0)
      by (intros k0 r0 Hk0; subst Ec; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
    assert (Ec34 : ew Ec 34 = Z_to_bv 64 key) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 2)).
    assert (Ec37 : ew Ec 37 = Z_to_bv 64 klast) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 5)).
    clear HEc.
    assert (U32 : U Ec (SOff 32 0) = hp) by (apply U_atom; [exact Ec32 | lia]).
    assert (U33 : U Ec (SOff 33 0) = hp + 8 * Z.of_nat n) by (apply U_atom; [exact Ec33 | lia]).
    assert (U36 : U Ec (SOff 36 0) = hp + 8 * (Z.of_nat (length ks) - 1)) by (apply U_atom; [exact Ec36 | lia]).
    assert (U19 : U Ec (SOff 19 0) = 8 * Z.of_nat n) by (apply U_atom; [exact Ec19 | lia]).
    (* 0x82fb8 -> the signed-index check 0x83008 *)
    paj_run_tok_x RUN HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK1, mat into matK1, HF into HFK1, HFr into HFrK1, HG into HGK1.
    psrr_branch_tok RUN BR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU ?p ?o) ?c) (SLit 1))) _ = true |- _ =>
         rewrite (trap_ptr_sovf Ec (SAlu ALU_SLTU p o) c 0
           (trap_U_sltu_ge Ec o p hp _ U32 ltac:(first [exact U33 | exact U36]) ltac:(lia)) ltac:(rewrite U_SLit; reflexivity)) in Hb;
         discriminate Hb end. }
    (* -> the WRAP check `not a2,a1; bltu a2,s3` 0x8302c *)
    paj_run_tok_x RUN HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK2, mat into matK2, HF into HFK2, HFr into HFrK2, HG into HGK2.
    psrr_branch_tok RUN BR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_LTU (sv_denot _ (SAlu ALU_XOR (SOff 32 0) (SLit (-1)))) (sv_denot _ (SOff 19 0)) = true |- _ =>
         rewrite (trap_ptr_wrap_not Ec (SAlu ALU_XOR (SOff 32 0) (SLit (-1))) (SOff 19 0) hp (8 * Z.of_nat n)
           (trap_U_not Ec (SOff 32 0) hp U32) U19 ltac:(lia)) in Hb; discriminate Hb end. }
    (* -> the move, nheld - 1 stored, the loop test 0x83060 *)
    paj_run_tok_x RUN HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK3, mat into matK3, HF into HFK3, HFr into HFrK3, HG into HGK3.
    psrr_branch_tok RUN BR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_LT (sv_denot _ (SOff 20 0)) (sv_denot _ (SOff 35 (-1))) = true |- _ =>
         rewrite (rk_branch_lt Ec (SOff 20 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hb;
         [| cbn [sv_denot]; rewrite Ec20, unsigned_lit_small by lia; f_equal; lia
          | cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by lia; f_equal; lia | lia | lia ]; apply Z.ltb_lt in Hb; lia end. }
    paj_run_to_tok_x RUNTO HS3 HJ4 SHOK3 rk_Bspan A_rig_step.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK4, mat into matK4, HF into HFK4, HFr into HFrK4, HG into HGK4.
    pmkst HS3.
    prreg HS3 (2%bv : bv 5) T2. prreg HS3 (3%bv : bv 5) T3. prreg HS3 (4%bv : bv 5) T4.
    prreg HS3 (8%bv : bv 5) T8. prreg HS3 (9%bv : bv 5) T9. prreg HS3 (21%bv : bv 5) T21.
    (* the move's two stores, the rest kept *)
    assert (BV23 : base_val Ec (Some 23%nat) = gSA cx i + 48) by (cbn [base_val]; exact Ec23).
    assert (BV33 : base_val Ec (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; exact Ec33u).
    assert (WIN : forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) ->
      aview SEGS (w_H W3) (ms_mem msK4) a = aview SEGS (w_H W3) mem4 a).
    { intros a Ha N1 N2.
      assert (N1' : ~ (gSA cx i + 48 <= a < gSA cx i + 48 + 4)) by (clear - N1; lia).
      rewrite (rkc_win Ec _ (w_H W3) (ms_mem msK3) (ms_mem msK4) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK4 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win Ec _ (w_H W3) (ms_mem msK2) (ms_mem msK3) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK3 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win Ec _ (w_H W3) (ms_mem msK1) (ms_mem msK2) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK2 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2).
      exact (rkc_win Ec _ (w_H W3) mem4 (ms_mem msK1) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK1 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2). }
    assert (PRES5 : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem msK4) a).
    { intros a Hp. eapply apresent_grows; [exact HGK4|]. eapply apresent_grows; [exact HGK3|].
      eapply apresent_grows; [exact HGK2|]. eapply apresent_grows; [exact HGK1|]. exact Hp. }
    pose proof (st_ok_pi_region_nth Ec _ _ 1 _ HS3 eq_refl) as RN1.
    pose proof (st_ok_pi_region_nth Ec _ _ 2 _ HS3 eq_refl) as RN2.
    cbn [ms_mem restrict mkst] in RN1, RN2.
    assert (VNH5 : val_mem SEGS (arm W3 (ms_mem msK4)) (gSA cx i + 48) 4 (Z.of_nat (length ks'))).
    { pose proof (field_of_region Ec _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) RN1 Ec23
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by (clear - Hks26; lia); f_equal; ring)
        ltac:(cbn; clear - Hks26 Hn; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. unfold ks'. rewrite relay_instance_gone_b_lem.rigl_len_swap, Nat2Z.inj_sub by (clear - Hn; lia). exact V. }
    assert (VHN5 : val_mem SEGS (arm W3 (ms_mem msK4)) (hp + 8 * Z.of_nat n) 8 klast).
    { pose proof (field_of_region Ec _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 34 0) key RN2 Ec33u
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - Hk4096 Hkceil Hrq1 C1; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. replace klast with key by (unfold klast, key; f_equal; f_equal; clear - Hks; lia). exact V. }
    unfold hp in VHN5.
    assert (HPq3' : Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3' out3 ++ gxrest cx)) by exact HPq3.
    destruct (rkc_end2 cx i n _ F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed _ c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 ly2 S2 W2 mem3 ly3 S3 W3 mem4 (ms_mem msK4) _ _ out3 HB HJ0 HPK HFR HLK HLS M80 HGN HJ4 HPq3' HO3
      PK14 PK24 KST4 KFR4 KIM4 KALL KO2i4 KO2b4 WIN PRES5 VNH5 VHN5) as (GL5 & LS5 & M805 & AR5 & AO5 & SR5 & SR15 & DR5 & GS5 & PR5 & PS5).
    assert (HPG : Permutation (ablocks B ly3 S3)
      ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
       gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
       rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap3' out3 ++ gxrest cx))
      by (unfold XGb in HPq3; rewrite <- app_comm_cons, <- !app_assoc in HPq3; exact HPq3).
    assert (HLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HM4).
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { pose proof (rkb_ge_cap_le c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as GC1.
      pose proof (rkb_bb_free ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL1 EL2) as B1.
      pose proof (rkb_bb_out ly1 S1 ly2 S2 cap2 out2 cap3' out3 restG HPa HPb ltac:(fold cap3' in GC1; clear - GC1 Hcap2; lia)) as B2.
      pose proof (rkb_ge_net c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl) as GN.
      fold cap3' in GC1, GN. clear - GC1 GN B1 B2 Hxl. lia. }
    pose proof (rkb_gout_end cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 ly3 S3 W3 (ms_mem msK4) out3 HB HGN HPT Hcap2 Hxl AR5 AO5 SR5 SR15 DR5 GS5 HPG HLE HBB HRMf HCN3) as HGO5.
    apply (KR W3 _).
    exists (ms_regs msK4), ly3, S3, (ms_mem msK4). eexists. eexists.
    exists F, FL, (qd ++ [(entry_keys e1 ks', h1)]), (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), cap3', out3,
      (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (EEc 2%nat 2%bv eq_refl); exact Q2|].
      split; [rewrite T3, (EEc 3%nat 3%bv eq_refl); exact Q3|].
      split; [rewrite T4, (EEc 4%nat 4%bv eq_refl); exact Q4|].
      split; [rewrite T8, (EEc 8%nat 8%bv eq_refl); exact Q8|].
      split; [rewrite T9, (EEc 9%nat 9%bv eq_refl); exact Q9|].
      rewrite T21, (EEc 21%nat 21%bv eq_refl); exact Q21. }
    split; [exact M805|]. split; [exact Hi|]. split; [exact GL5|]. split; [exact LS5|].
    exact HGO5.
  + pose proof (rk_seat3 false W3 ly3 S3 regs4 mem4 md4 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
    (Z.of_nat (length ks)) key klast A_rig_fr_ret HARfr Q2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp; exact H32) ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    Q9 Q21 Q19 Q22 Q20 Q23 Q27 Q25 Q18 HinT4 ltac:(clear - HSA; lia) HTend ltac:(rewrite HSA; apply rk_mod_sa; exact HT16)
    Hinh4 Hkh Hks26 ltac:(cbn; lia) ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; lia)
    ltac:(clear - HkL4096 HkLceil HrL1 C1; lia) HBLK Mhp4 Mnh4 Mkey4 ltac:(intros _; exact MkL4)) as [HS3 SHOK3].
    cbn beta iota in HS3.
    remember (Eimg (Ereg regs4 (rk_extra3 hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (hp + 8 * (Z.of_nat (length ks) - 1)) klast))) as Ec eqn:HEc.
    assert (HEIc : img_env VAL A_LIM Ec) by (subst Ec; apply Eimg_env).
    assert (Ec32 : ew Ec 32 = Z_to_bv 64 hp) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    assert (Ec33 : ew Ec 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 1)).
    assert (Ec35 : ew Ec 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 3)).
    assert (Ec36 : ew Ec 36 = Z_to_bv 64 (hp + 8 * (Z.of_nat (length ks) - 1))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 4)).
    assert (Ec19 : ew Ec 19 = Z_to_bv 64 (8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl); exact Q19).
    assert (Ec20 : ew Ec 20 = Z_to_bv 64 (Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 20 20%bv eq_refl); exact Q20).
    assert (Ec23 : bv_unsigned (ew Ec 23) = gSA cx i + 48) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 23 23%bv eq_refl), Q23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
    assert (Ec33u : bv_unsigned (ew Ec 33) = hp + 8 * Z.of_nat n) by (rewrite Ec33; apply unsigned_lit_small; lia).
    assert (EEc : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew Ec k0 = getr regs4 r0)
      by (intros k0 r0 Hk0; subst Ec; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
    assert (Ec34 : ew Ec 34 = Z_to_bv 64 key) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 2)).
    assert (Ec37 : ew Ec 37 = Z_to_bv 64 klast) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 5)).
    clear HEc.
    assert (U32 : U Ec (SOff 32 0) = hp) by (apply U_atom; [exact Ec32 | lia]).
    assert (U33 : U Ec (SOff 33 0) = hp + 8 * Z.of_nat n) by (apply U_atom; [exact Ec33 | lia]).
    assert (U36 : U Ec (SOff 36 0) = hp + 8 * (Z.of_nat (length ks) - 1)) by (apply U_atom; [exact Ec36 | lia]).
    assert (U19 : U Ec (SOff 19 0) = 8 * Z.of_nat n) by (apply U_atom; [exact Ec19 | lia]).
    (* 0x82fb8 -> the signed-index check 0x83008 *)
    paj_run_tok_x RUN HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK1, mat into matK1, HF into HFK1, HFr into HFrK1, HG into HGK1.
    psrr_branch_tok RUN BR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU ?p ?o) ?c) (SLit 1))) _ = true |- _ =>
         rewrite (trap_ptr_sovf Ec (SAlu ALU_SLTU p o) c 0
           (trap_U_sltu_ge Ec o p hp _ U32 ltac:(first [exact U33 | exact U36]) ltac:(lia)) ltac:(rewrite U_SLit; reflexivity)) in Hb;
         discriminate Hb end. }
    (* -> the WRAP check `not a2,a1; bltu a2,s3` 0x8302c *)
    paj_run_tok_x RUN HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK2, mat into matK2, HF into HFK2, HFr into HFrK2, HG into HGK2.
    psrr_branch_tok RUN BR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_LTU (sv_denot _ (SAlu ALU_XOR (SOff 32 0) (SLit (-1)))) (sv_denot _ (SOff 19 0)) = true |- _ =>
         rewrite (trap_ptr_wrap_not Ec (SAlu ALU_XOR (SOff 32 0) (SLit (-1))) (SOff 19 0) hp (8 * Z.of_nat n)
           (trap_U_not Ec (SOff 32 0) hp U32) U19 ltac:(lia)) in Hb; discriminate Hb end. }
    (* -> the move, nheld - 1 stored, the loop test 0x83060 *)
    paj_run_tok_x RUN HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK3, mat into matK3, HF into HFK3, HFr into HFrK3, HG into HGK3.
    psrr_branch_tok RUN BR HS3 SHOK3 rk_Bspan.
    2: { exfalso. lazymatch goal with Hb : branch_taken BC_LT (sv_denot _ (SOff 20 0)) (sv_denot _ (SOff 35 (-1))) = false |- _ =>
         rewrite (rk_branch_lt Ec (SOff 20 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hb;
         [| cbn [sv_denot]; rewrite Ec20, unsigned_lit_small by lia; f_equal; lia
          | cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by lia; f_equal; lia | lia | lia ]; apply Z.ltb_ge in Hb; lia end. }
    paj_run_to_tok_x RUNTO HS3 HJ4 SHOK3 rk_Bspan A_rig_inner.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK4, mat into matK4, HF into HFK4, HFr into HFrK4, HG into HGK4.
    pmkst HS3.
    prreg HS3 (2%bv : bv 5) T2. prreg HS3 (3%bv : bv 5) T3. prreg HS3 (4%bv : bv 5) T4.
    prreg HS3 (8%bv : bv 5) T8. prreg HS3 (9%bv : bv 5) T9. prreg HS3 (21%bv : bv 5) T21.
    (* the move's two stores, the rest kept *)
    assert (BV23 : base_val Ec (Some 23%nat) = gSA cx i + 48) by (cbn [base_val]; exact Ec23).
    assert (BV33 : base_val Ec (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; exact Ec33u).
    assert (WIN : forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) ->
      aview SEGS (w_H W3) (ms_mem msK4) a = aview SEGS (w_H W3) mem4 a).
    { intros a Ha N1 N2.
      assert (N1' : ~ (gSA cx i + 48 <= a < gSA cx i + 48 + 4)) by (clear - N1; lia).
      rewrite (rkc_win Ec _ (w_H W3) (ms_mem msK3) (ms_mem msK4) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK4 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win Ec _ (w_H W3) (ms_mem msK2) (ms_mem msK3) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK3 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win Ec _ (w_H W3) (ms_mem msK1) (ms_mem msK2) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK2 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2).
      exact (rkc_win Ec _ (w_H W3) mem4 (ms_mem msK1) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK1 ltac:(rkc_rs) BV23 BV33 a Ha N1' N2). }
    assert (PRES5 : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem msK4) a).
    { intros a Hp. eapply apresent_grows; [exact HGK4|]. eapply apresent_grows; [exact HGK3|].
      eapply apresent_grows; [exact HGK2|]. eapply apresent_grows; [exact HGK1|]. exact Hp. }
    pose proof (st_ok_pi_region_nth Ec _ _ 1 _ HS3 eq_refl) as RN1.
    pose proof (st_ok_pi_region_nth Ec _ _ 2 _ HS3 eq_refl) as RN2.
    cbn [ms_mem restrict mkst] in RN1, RN2.
    assert (VNH5 : val_mem SEGS (arm W3 (ms_mem msK4)) (gSA cx i + 48) 4 (Z.of_nat (length ks'))).
    { pose proof (field_of_region Ec _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) RN1 Ec23
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by (clear - Hks26; lia); f_equal; ring)
        ltac:(cbn; clear - Hks26 Hn; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. unfold ks'. rewrite relay_instance_gone_b_lem.rigl_len_swap, Nat2Z.inj_sub by (clear - Hn; lia). exact V. }
    assert (VHN5 : val_mem SEGS (arm W3 (ms_mem msK4)) (hp + 8 * Z.of_nat n) 8 klast).
    { pose proof (field_of_region Ec _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 37 0) klast RN2 Ec33u
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - HkL4096 HkLceil HrL1 C1; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. exact V. }
    unfold hp in VHN5.
    assert (HPq3' : Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3' out3 ++ gxrest cx)) by exact HPq3.
    destruct (rkc_end2 cx i n _ F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed _ c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 ly2 S2 W2 mem3 ly3 S3 W3 mem4 (ms_mem msK4) _ _ out3 HB HJ0 HPK HFR HLK HLS M80 HGN HJ4 HPq3' HO3
      PK14 PK24 KST4 KFR4 KIM4 KALL KO2i4 KO2b4 WIN PRES5 VNH5 VHN5) as (GL5 & LS5 & M805 & AR5 & AO5 & SR5 & SR15 & DR5 & GS5 & PR5 & PS5).
    assert (HPG : Permutation (ablocks B ly3 S3)
      ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
       gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
       rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap3' out3 ++ gxrest cx))
      by (unfold XGb in HPq3; rewrite <- app_comm_cons, <- !app_assoc in HPq3; exact HPq3).
    assert (HLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HM4).
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { pose proof (rkb_ge_cap_le c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as GC1.
      pose proof (rkb_bb_free ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL1 EL2) as B1.
      pose proof (rkb_bb_out ly1 S1 ly2 S2 cap2 out2 cap3' out3 restG HPa HPb ltac:(fold cap3' in GC1; clear - GC1 Hcap2; lia)) as B2.
      pose proof (rkb_ge_net c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl) as GN.
      fold cap3' in GC1, GN. clear - GC1 GN B1 B2 Hxl. lia. }
    prreg HS3 (19%bv : bv 5) T19. prreg HS3 (20%bv : bv 5) T20. prreg HS3 (23%bv : bv 5) T23. prreg HS3 (24%bv : bv 5) T24.
    prreg HS3 (25%bv : bv 5) T25. prreg_raw HS3 (22%bv : bv 5) T22. prreg_raw HS3 (27%bv : bv 5) T27. prreg_raw HS3 (18%bv : bv 5) T18.
    destruct (rkb_gin_end cx i n r' F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 ly3 S3 W3 (ms_mem msK4) out3 HB HGN HPT Hcap2 Hxl AR5 AO5 SR5 SR15 DR5 GS5 HPG PR5 PS5 HLE HBB HRMf HCN3)
      as (f5 & HGN5).
    apply (KE r' W3 _ eq_refl).
    exists (ms_regs msK4), ly3, S3, (ms_mem msK4). eexists. eexists.
    exists F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, ks', (Ed ++ [nth n ks (0, [], [])]), f5,
      (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), cap3', out3,
      (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (EEc 2%nat 2%bv eq_refl); exact Q2|].
      split; [rewrite T3, (EEc 3%nat 3%bv eq_refl); exact Q3|].
      split; [rewrite T4, (EEc 4%nat 4%bv eq_refl); exact Q4|].
      split; [rewrite T8, (EEc 8%nat 8%bv eq_refl); exact Q8|].
      split; [rewrite T9, (EEc 9%nat 9%bv eq_refl); exact Q9|].
      rewrite T21, (EEc 21%nat 21%bv eq_refl); exact Q21. }
    split; [rewrite T19, (EEc 19%nat 19%bv eq_refl); exact Q19|].
    split; [rewrite T22; cbn [sv_denot]; rewrite (EEc 19%nat 19%bv eq_refl), Q19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite T20, (EEc 20%nat 20%bv eq_refl); exact Q20|].
    split; [rewrite T23, (EEc 23%nat 23%bv eq_refl); exact Q23|].
    split.
    { rewrite T27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 21 0)) with (rk_sh 23).
      apply rk_sh_den; [rewrite (EEc 23%nat 23%bv eq_refl); exact Q23 | rewrite (EEc 21%nat 21%bv eq_refl); exact Q21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split; [rewrite T24, (EEc 24%nat 24%bv eq_refl); exact Q24|].
    split; [rewrite T25, (EEc 25%nat 25%bv eq_refl); exact Q25|].
    split.
    { rewrite T18. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 21 0)) with (rk_sh 25).
      apply rk_sh_den; [rewrite (EEc 25%nat 25%bv eq_refl); exact Q25 | rewrite (EEc 21%nat 21%bv eq_refl); exact Q21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split; [exact M805|]. split; [exact GL5|]. split; [exact LS5|].
    exact HGN5.
Qed.


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): KEY, concluding the cx file's rig_key_stmt_xR at a world relation R.  The strict lemmas above take every Section
   hypothesis (Default Proof Using "All"), the strict AFREE / DRAIN / GE / ALLOC_TAIL included, so this Section copies
   each of them as X_xR (same statement and proof) under a Default Proof Using that leaves those out.  The lemmas that
   read a journal are lifted: ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the journal lemmas ->
   their _xR twins (W_journal_x.v), the runs and the branch -> their SRrG forms (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG with W_kit_x.v paj_run_tok_xR / paj_run_to_tok_xR, W_kit.v paj_branch_xR), the binds -> SRrG_bind SEGS R R_trans, strncmp's entry -> aj_gx_entry_at_xR (W_sites_x.v), and the helpers that read a journal -> their R twins (W_rig_key_e.v / _k.v / _c.v).  The hypothesis list is the cx file's Section wR, verbatim. ---- *)
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
(* every lemma below takes the Section's hypotheses except the strict AFREE / DRAIN / GE / ALLOC_TAIL and R_refl /
   DRAIN_R (KEY needs none of them), so no route-R statement here carries a strict allocator rule *)
#[local] Set Default Proof Using "-(AFREE DRAIN GE ALLOC_TAIL R_refl DRAIN_R)".
#[local] Notation rkb_live_gen_xR := (W_rig_key_b.rkb_live_gen_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_live_pos_xR := (W_rig_key_b.rkb_live_pos_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_live_ctl_xR := (W_rig_key_b.rkb_live_ctl_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_live_dr_xR := (W_rig_key_b.rkb_live_dr_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_live_sends_xR := (W_rig_key_b.rkb_live_sends_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_live_rel_xR := (W_rig_key_b.rkb_live_rel_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_live_gin_xR := (W_rig_key_b.rkb_live_gin_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sends_app_xR := (W_rig_key_b.rkb_sends_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_bytes_app_xR := (W_rig_key_b.rkb_ge_bytes_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sl_O_len_xR := (W_rig_key_b.rkb_sl_O_len_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sends_key_xR := (W_rig_key_b.rkb_sends_key_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_O_len_xR := (W_rig_key_b.rkb_ge_O_len_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_tr_max_nonneg_xR := (W_rig_key_b.rkb_tr_max_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_tr_app_xR := (W_rig_key_b.rkb_tr_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_tr_free_xR := (W_rig_key_b.rkb_tr_free_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sizes_cost_xR := (W_rig_key_b.rkb_sizes_cost_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sizes_app_xR := (W_rig_key_b.rkb_sizes_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_er_tr_xR := (W_rig_key_b.rkb_er_tr_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_er_eq_xR := (W_rig_key_b.rkb_er_eq_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_cost_head_xR := (W_rig_key_b.rkb_cost_head_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_slr_cost_xR := (W_rig_key_b.rkb_slr_cost_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_slr_sizes_xR := (W_rig_key_b.rkb_slr_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_slr_er_xR := (W_rig_key_b.rkb_slr_er_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_slcr_nonneg_xR := (W_rig_key_b.rkb_slcr_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sl_cap_ge_xR := (W_rig_key_b.rkb_sl_cap_ge_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_slt_cost_xR := (W_rig_key_b.rkb_slt_cost_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_slt_sizes_xR := (W_rig_key_b.rkb_slt_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_tr_cost_xR := (W_rig_key_b.rkb_ge_tr_cost_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_cost_nonneg_xR := (W_rig_key_b.rkb_ge_cost_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_cap_nonneg_xR := (W_rig_key_b.rkb_ge_cap_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_no_nonneg_xR := (W_rig_key_b.rkb_ge_no_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_cap_le_xR := (W_rig_key_b.rkb_ge_cap_le_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_net_xR := (W_rig_key_b.rkb_ge_net_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ker_er_xR := (W_rig_key_b.rkb_ker_er_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ker_eq_xR := (W_rig_key_b.rkb_ker_eq_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ker_sizes_xR := (W_rig_key_b.rkb_ker_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ker_step_xR := (W_rig_key_b.rkb_ker_step_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gkrest_nil_xR := (W_rig_key_b.rkb_gkrest_nil_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gkrest_sizes_xR := (W_rig_key_b.rkb_gkrest_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gkrest_step_xR := (W_rig_key_b.rkb_gkrest_step_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_grow_ok_xR := (W_rig_key_b.rkb_grow_ok_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_seen_sizes_xR := (W_rig_key_b.rkb_seen_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_lines_sizes_xR := (W_rig_key_b.rkb_lines_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_push_ok_xR := (W_rig_key_b.rkb_push_ok_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_drain_ok_xR := (W_rig_key_b.rkb_drain_ok_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_fold5_nonneg_xR := (W_rig_key_b.rkb_fold5_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_xks_nonneg_xR := (W_rig_key_b.rkb_xks_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gone_sizes_xR := (W_rig_key_b.rkb_gone_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_forall_skipn_xR := (W_rig_key_b.rkb_forall_skipn_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gbase_facts_xR := (W_rig_key_b.rkb_gbase_facts_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_grest_sizes_xR := (W_rig_key_b.rkb_grest_sizes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_mok_xR := (W_rig_key_b.rkb_mok_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gbud_end_xR := (W_rig_key_b.rkb_gbud_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_ge_room_xR := (W_rig_key_b.rkb_ge_room_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_bb_out_xR := (W_rig_key_b.rkb_bb_out_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_bb_free_xR := (W_rig_key_b.rkb_bb_free_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_geik_pass_xR := (W_rig_key_b.rkb_geik_pass_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_geik_end_xR := (W_rig_key_b.rkb_geik_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_geik_done_xR := (W_rig_key_b.rkb_geik_done_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gbase_len_xR := (W_rig_key_b.rkb_gbase_len_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_firstn_snoc_xR := (W_rig_key_b.rkb_firstn_snoc_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_combine_app_xR := (W_rig_key_b.rkb_combine_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gdone_snoc_xR := (W_rig_key_b.rkb_gdone_snoc_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_rel_app_xR := (W_rig_key_b.rkb_rel_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_rel_one_xR := (W_rig_key_b.rkb_rel_one_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gin_pass_xR := (W_rig_key_b.rkb_gin_pass_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gout_pass_xR := (W_rig_key_b.rkb_gout_pass_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_aview_mod_xR := (W_rig_key_k.rkk_aview_mod_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_wr_xR := (W_rig_key_k.rkk_wr_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_bv_xR := (W_rig_key_k.rkk_bv_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_view_mod_xR := (W_rig_key_k.rkk_view_mod_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_view_hi_xR := (W_rig_key_k.rkk_view_hi_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_view_lo_xR := (W_rig_key_k.rkk_view_lo_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_kept_hi_xR := (W_rig_key_k.rkk_kept_hi_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_kept_lo_xR := (W_rig_key_k.rkk_kept_lo_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_vm_xR := (W_rig_key_k.rkk_vm_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_ceil_xR := (W_rig_key_k.rkk_ceil_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_kept_c_xR := (W_rig_key_k.rkk_kept_c_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_akept_xR := (W_rig_key_k.rkk_akept_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_blk_xR := (W_rig_key_k.rkk_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_img_xR := (W_rig_key_k.rkk_img_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_inG_xR := (W_rig_key_k.rkk_inG_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_glob_xR := (W_rig_key_k.rkk_glob_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_j4_xR := (W_rig_key_k.rkk_j4_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_slot_loc_xR := (W_rig_key_k.rkk_slot_loc_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_len_recs_xR := (W_rig_key_k.rkk_len_recs_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_len_ptrs_xR := (W_rig_key_k.rkk_len_ptrs_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_alist_xR := (W_rig_key_k.rkk_alist_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_asrc_xR := (W_rig_key_k.rkk_asrc_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_aentry_xR := (W_rig_key_k.rkk_aentry_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_arelay_xR := (W_rig_key_k.rkk_arelay_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_aout_xR := (W_rig_key_k.rkk_aout_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_asrc_m_xR := (W_rig_key_k.rkk_asrc_m_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_aothers_xR := (W_rig_key_k.rkk_aothers_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_drsrc_xR := (W_rig_key_k.rkk_drsrc_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_digits_xR := (W_rig_key_k.rkk_digits_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_pre_len_xR := (W_rig_key_k.rkk_pre_len_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_jar_xR := (W_rig_key_k.rkk_jar_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_gin_xR := (W_rig_key_k.rkk_gin_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_live_xR := (W_rig_key_k.rkk_live_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkk_lslots_xR := (W_rig_key_k.rkk_lslots_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_ablocks_nodup_xR := (W_rig_key_r.rk_ablocks_nodup_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_garr8_aview_xR := (W_rig_key_r.rk_garr8_aview_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_pw_in_xR := (W_rig_key_r.rk_pw_in_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_blk_apart_xR := (W_rig_key_r.rk_blk_apart_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_mod_sp_xR := (W_rig_key_r.rk_mod_sp_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_mod_sa_xR := (W_rig_key_r.rk_mod_sa_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_pw_app_xR := (W_rig_key_r.rk_pw_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_frame_blk_apart_xR := (W_rig_key_r.rk_frame_blk_apart_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_nodup_app_disj_xR := (W_rig_key_r.rk_nodup_app_disj_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_nodup_app_r_xR := (W_rig_key_r.rk_nodup_app_r_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_view_garr8_xR := (W_rig_key_r.rk_view_garr8_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_garr8_kv_xR := (W_rig_key_r.rk_garr8_kv_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_perm_entry_xR := (W_rig_key_r.rk_perm_entry_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_wr_blk_xR := (W_rig_key_r.rk_wr_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_blk_not_img_xR := (W_rig_key_r.rk_blk_not_img_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_hull_xR := (W_rig_key_r.rk_hull_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_vm2_xR := (W_rig_key_r.rk_vm2_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_sll3_add8_xR := (W_rig_key_r.rk_sll3_add8_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_branch_lt_xR := (W_rig_key_r.rk_branch_lt_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_nodup_mid_xR := (W_rig_key_r.rk_nodup_mid_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_nth_le_bytes_xR := (W_rig_key_r.rkr_nth_le_bytes_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_garr8_le_xR := (W_rig_key_r.rkr_garr8_le_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_le_garr8_xR := (W_rig_key_r.rkr_le_garr8_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_view_xR := (W_rig_key_r.rkr_view_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_bz0_xR := (W_rig_key_r.rkr_bz0_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_bz_nz_xR := (W_rig_key_r.rkr_bz_nz_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_nth_key_xR := (W_rig_key_r.rkr_nth_key_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_nth_key_end_xR := (W_rig_key_r.rkr_nth_key_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_garr8_app3_xR := (W_rig_key_r.rkr_garr8_app3_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_kp_app_xR := (W_rig_key_r.rkr_kp_app_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_key_ptrs_len_xR := (W_rig_key_r.rkr_key_ptrs_len_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_key_ptr_xR := (W_rig_key_r.rkr_key_ptr_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_set_nth_mid_xR := (W_rig_key_r.rkr_set_nth_mid_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_nth_last_xR := (W_rig_key_r.rkr_nth_last_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_swap_shape_xR := (W_rig_key_r.rkr_swap_shape_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_eb_shape_xR := (W_rig_key_r.rkr_eb_shape_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_pw_perm_xR := (W_rig_key_r.rkr_pw_perm_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_pw_mid_xR := (W_rig_key_r.rkr_pw_mid_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_pw_mid4_xR := (W_rig_key_r.rkr_pw_mid4_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_disj_xR := (W_rig_key_r.rkr_disj_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_fp_blk_xR := (W_rig_key_r.rkr_fp_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_entry_at_xR := (W_rig_key_r.rkr_entry_at_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_arelay_swap_xR := (W_rig_key_r.rkr_arelay_swap_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_agree_xR := (W_rig_key_r.rkr_agree_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_first_key_xR := (W_rig_key_r.rkr_first_key_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_first_pre_xR := (W_rig_key_r.rkr_first_pre_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_digits_xR := (W_rig_key_r.rkr_digits_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_digits_le_xR := (W_rig_key_r.rkr_digits_le_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_digits11_xR := (W_rig_key_r.rkr_digits11_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkr_pre_nz_xR := (W_rig_key_r.rkr_pre_nz_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_sh_den_xR := (W_rig_key_s.rk_sh_den_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_shok_xR := (W_rig_key_s.rk_shok_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_seat_xR := (W_rig_key_s.rk_seat_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_end5_xR := (W_rig_key_e.rk_end5_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_callS_xR := (W_rig_key_e.rk_callS_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_keep_img_xR := (W_rig_key_e.rk_keep_img_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_keep_high_xR := (W_rig_key_e.rk_keep_high_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_keep_blk_xR := (W_rig_key_e.rk_keep_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_keep_frm_xR := (W_rig_key_e.rk_keep_frm_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_ly_top_xR := (W_rig_key_e.rk_ly_top_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_fp_spares_xR := (W_rig_key_e.rk_fp_spares_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_disj_xR := (W_rig_key_e.rk_disj_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_not_owned_xR := (W_rig_key_e.rk_not_owned_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_free_xR := (W_rig_key_e.rk_free_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_achain_xR := (W_rig_key_e.rk_achain_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_achainp_xR := (W_rig_key_e.rk_achainp_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_ge_xR := (W_rig_key_e.rk_ge_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_aout_facts_xR := (W_rig_key_e.rk_aout_facts_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_fp_blk_xR := (W_rig_key_e.rk_fp_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sends_cap_nonneg_xR := (W_rig_key_b.rkb_sends_cap_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sends_cons_xR := (W_rig_key_b.rkb_sends_cons_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gin_end_xR := (W_rig_key_b.rkb_gin_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gout_end_xR := (W_rig_key_b.rkb_gout_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_fp_orig_xR := (W_rig_key_e.rk_fp_orig_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk3_shok_xR := (W_rig_key_s.rk3_shok_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_seat3_xR := (W_rig_key_s.rk_seat3_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_recs_len_xR := (W_rig_key_c.rkc_recs_len_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_key_ptrs_len_xR := (W_rig_key_c.rkc_key_ptrs_len_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_alist_fp_blk_xR := (W_rig_key_c.rkc_alist_fp_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_asrc_fp_blk_xR := (W_rig_key_c.rkc_asrc_fp_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_aentry_fp_sub_xR := (W_rig_key_c.rkc_aentry_fp_sub_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_aentry_fp_blk_xR := (W_rig_key_c.rkc_aentry_fp_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_aout_fp_xR := (W_rig_key_c.rkc_aout_fp_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_kept_trans_xR := (W_rig_key_c.rkc_kept_trans_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_aothers_kept_xR := (W_rig_key_c.rkc_aothers_kept_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_srcs_in_xR := (W_rig_key_c.rkc_srcs_in_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_len_gps_xR := (W_rig_key_c.rkc_len_gps_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_gps_nth_xR := (W_rig_key_c.rkc_gps_nth_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_done_blks_xR := (W_rig_key_c.rkc_done_blks_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_wr_img_xR := (W_rig_key_c.rkc_wr_img_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_abk_img_xR := (W_rig_key_c.rkc_abk_img_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_abk_blk_xR := (W_rig_key_c.rkc_abk_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_writable_view_xR := (W_rig_key_c.rkc_writable_view_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_abk_vis_xR := (W_rig_key_c.rkc_abk_vis_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_win_xR := (W_rig_key_c.rkc_win_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_lyF_xR := (W_rig_key_c.rkc_lyF_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_view_some_xR := (W_rig_key_c.rkc_view_some_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_zall_nth_xR := (W_rig_key_c.rkc_zall_nth_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_zpw_nth_xR := (W_rig_key_c.rkc_zpw_nth_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_notSL_xR := (W_rig_key_c.rkc_notSL_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_out_cell_xR := (W_rig_key_c.rkc_out_cell_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_end_xR := (W_rig_key_c.rkc_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_end2_xR := (W_rig_key_c.rkc_end2_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_room_xR := (W_rig_key_b.rk_room_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_cnt_out_le_xR := (W_rig_key_b.rkc_cnt_out_le_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkc_end_cnt_xR := (W_rig_key_b.rkc_end_cnt_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_RIG B RG) HGRIG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state this walk meets has the head set [], so the walk states its facts at ARh (= ARx at []) and
   each journal from [] to [] (a callee's post state is brought to [] as it arrives).  The wrappers keep the AR walk's
   argument order: rk_alb_xR is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN). *)
Local Lemma rk_jhp0_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> Hp' = [].
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (HP0 _ _ _ _ _ _ (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
Qed.
Local Lemma rk_jAR_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
ARh ly' S' W' mem' md'.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
Local Lemma rk_alb_xR : forall ly S W mem md p n, ARh ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* the entry's head set is empty too (GBASE's afn_pre_x states ARx at gxHp) *)
Local Lemma rk_gxHp_xR : forall cx, GBASE B ARx MT RP MMAX RG cx -> gxHp cx = [].
Proof. intros cx HB. destruct HB as ((HAR & _) & _). exact (HP0 _ _ _ _ _ _ HAR). Qed.
(* W_frame_b.v frm_off_imgB over ARx (as lib/B/W_rig_pro.v rgp_frm_off_imgB_x): a live fake frame lies off image B's
   [0x10000, 0x5fc000) - at or above the image's top (the image law alx_img), which IMGC puts at or above 0x5fc000
   (W_frame_x.v frm_off_imgP_x states image A's top 0x5fb000, too weak for B's objects) *)
Local Lemma rk_frm_off_imgB_x_xR : forall ly S Hp (W : world SEGS) mem md cid pos,
ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [_ C2].
pose proof (proj2 (alx_img _ _ _ LAWS ly S Hp W mem md HAR) cid pos Hin) as Hf.
right. lia.
Qed.


Ltac prreg_raw_xR HS r Hr :=
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

(* the runs of KEY's seat write nothing: every region of rk_regions has an empty write window *)
Lemma rk_nowin_xR : forall E' ss' H (mA mB : word -> option byte),
frame_of E' (ss_mem ss') (mrestrict H mA) (mrestrict H mB) -> ss_mem ss' = rk_regions ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H mB a = aview SEGS H mA a.
Proof.
intros E' ss' H mA mB HFr Hm a Ha. apply (aview_kept_out E' _ H mA mB HFr a Ha).
rewrite Hm. intros (r0 & Hin & Hr). cbn [rk_regions In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma rk_awr_xR : forall E G STK sp0 FP bl0 blc ly own, awr_ok_x E rk_regions G 0 [] STK sp0 FP bl0 blc ly own.
Proof.
intros E G STK sp0 FP bl0 blc ly own a (r & Hin & Hr). cbn [rk_regions In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.



Ltac rkc_rs_xR := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  cbn [In ss_mem ss_k3a ss_k3b rk3a_regions rk3b_regions] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
     first [ left; apply Z.leb_le; reflexivity | right; left; split; [reflexivity | split; reflexivity]
           | right; right; split; [reflexivity | split; reflexivity] ] |]);
  try destruct Hr.

Theorem rig_key_proof_xR : rig_key_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
unfold rig_key_stmt_xR. intros cx i n r W1 c1 HB HCTX HI KP KE KR.
destruct HI as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & cB & OB & capB & e1 & h1 & ev & LB & c1' & O1 & cap1 &
  ks & Ed & f & c2 & O2 & cap2 & out2 & spent & -> & HRB & R19 & R22 & R20 & R23 & R27 & R24 & R25 & R18 & M80 &
  HLV & HLS & HGN).
pose proof HLV as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
assert (EHp1 : Hp1 = []) by (eapply rk_jhp0_xR; exact HJ). subst Hp1.
pose proof HB as (HPRE0 & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof (rk_gxHp_xR cx HB) as EHp0. rewrite EHp0 in HJ, HPRE0.
pose proof HJ as HJ0.
pose proof HGN as (Hi & Hqd & HREL & HDR & HSND & Hks & Hf & HGK & HRLY & HOUT & HSRC & HOPEN & HDRS & HGS & HPERM &
  HPRE & HPSH & HBUD).
pose proof HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H21).
pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17232) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof HJ as (HSTK & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SP1 : spZ regs1 = gsp0 cx - 224) by (rewrite Hsp1; reflexivity).
assert (SPR : alloc_ceiling + 12912 <= gsp0 cx - 4320 /\ gsp0 cx <= 2 ^ 47) by (unfold gsp0 in *; rewrite WS in Hslo; lia).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkr_entry_at_xR ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n HAR1 HRLY Hn) as X.
cbv zeta in X. rewrite length_map, Hqd in X. fold (gSA cx i) in X.
destruct X as (HinT & HT16 & HT4096 & HTceil & HTend & Mhp & Mnh & AWT & Hhp0 & Hinh & Hkh & Ghp & AWH & Mslot & Hink &
  Gk & NZk & Lk & Hks26 & NDk).
set (k := nth n ks (0, [], [])) in *.
set (hp := re_hp e1) in *. set (key := key_addr k) in *. set (kt := key_text k) in *.
destruct (rk_alb_xR ly1 S1 W1 m1 md1 _ _ HAR1 Hink) as (Hk16 & Hk4096 & Hkceil & Hkapp & Hkpres & _ & _).
destruct (rk_alb_xR ly1 S1 W1 m1 md1 _ _ HAR1 Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _ & Hkh0).
destruct (rk_alb_xR ly1 S1 W1 m1 md1 _ _ HAR1 HinT) as (_ & _ & _ & HTapp & HTpres & _ & _).
pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [Hrk1 Hrk2].
pose proof (req_size_pos (Z.of_nat (length kt) + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (rk_ablocks_nodup_xR _ _ _ _ _ HAR1) as HND1.
pose proof (Permutation_NoDup HPERM HND1) as HNDP.
assert (HinHP : In (hp, re_kh e1) (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))))).
{ apply in_concat. exists (aentry_blks (entry_keys e1 ks)). split.
  - apply in_map. apply in_or_app. right. left. reflexivity.
  - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
    fold hp. destruct (Z.eqb_spec hp 0); [contradiction | left; reflexivity]. }
assert (HTH : (gxG0 cx, ATABLE) <> (hp, re_kh e1)).
{ apply List.NoDup_cons_iff in HNDP. intros Heq.
  apply (proj1 HNDP). rewrite Heq. apply in_or_app. left. exact HinHP. }
pose proof (rk_blk_apart_xR ly1 S1 W1 m1 md1 _ _ HAR1 HinT Hinh HTH) as HTHd. cbn [fst snd] in HTHd.
change (req_size ATABLE) with 896 in HTHd.
assert (HSA : gSA cx i = gxG0 cx + 56 * Z.of_nat i) by reflexivity.
assert (DSH : hp + 8 * Z.of_nat n + 8 <= gSA cx i + 40 \/ gSA cx i + 52 <= hp + 8 * Z.of_nat n)
  by (clear - HTHd HTend HSA Hkh Hrk2 Hn; unfold AENT, ATABLE in *; lia).
(* the frame (1, fpos) *)
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (rk_alf _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (rk_fb _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *. rewrite HFa in *.
assert (HF8 : 0 <= F / 8 /\ 8 * (F / 8) <= F).
{ split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
pose proof (rk_seat_xR W1 ly1 S1 regs1 m1 md1 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
  (Z.of_nat (length ks)) key (F + 32) A_rig_inner HAR1 Hsp1 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
  ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp_xR; exact H32) ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
  H9 H21 R19 R22 R20 R23 R27 R25 R18 HinT ltac:(clear - HSA; lia) HTend
  ltac:(rewrite HSA; apply rk_mod_sa_xR; exact HT16)
  Hinh Hkh ltac:(clear - Hn; lia) Hks26 ltac:(clear - Hk4096 Hkceil Hrq1 C1; lia)
  ltac:(clear - HF4096 HFceil C1; lia)
  DSH Mhp Mnh (Mslot n Hn) L88) as [HS SHOK].
clear DSH.
unfold cfg_at. change (w64 (BASE + A_rig_inner)) with (Z_to_bv 64 (BASE + A_rig_inner)).
remember (Eimg (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (F + 32)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk0; subst E; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 key) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (F + 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (HAE : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (F + 32))) E)
  by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
(* the three blocks, pairwise apart, and apart from F *)
destruct (rk_perm_entry_xR _ _ _ (map fst qd) (entry_keys e1 ks) (skipn (S i) (gxes cx)) _ k HND1 HPERM
  ltac:(cbn [re_hp entry_keys]; exact Hhp0) ltac:(cbn [re_keys entry_keys]; apply nth_In; exact Hn)) as (NE1 & NE2 & NE3).
cbn [re_hp re_kh entry_keys] in NE1, NE2, NE3. fold hp key kt in NE1, NE2, NE3.
pose proof (rk_blk_apart_xR _ _ _ _ _ _ _ HAR1 HinT Hink NE2) as DTK. cbn [fst snd] in DTK.
pose proof (rk_blk_apart_xR _ _ _ _ _ _ _ HAR1 Hinh Hink NE3) as DHK. cbn [fst snd] in DHK.
pose proof (rk_frame_blk_apart_xR _ _ _ _ _ _ _ _ _ HAR1 Hfin HinT) as DFT.
pose proof (rk_frame_blk_apart_xR _ _ _ _ _ _ _ _ _ HAR1 Hfin Hinh) as DFH.
pose proof (rk_frame_blk_apart_xR _ _ _ _ _ _ _ _ _ HAR1 Hfin Hink) as DFK.
change (fs_frame_bytes 1) with 128 in DFT, DFH, DFK. rewrite HFa in DFT, DFH, DFK.
change (req_size ATABLE) with 896 in DTK, DFT.
set (XG := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
  rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap2 out2).
assert (HPX : Permutation (ablocks B ly1 S1) (XG ++ gxrest cx)) by (unfold XG; rewrite <- app_comm_cons, <- !app_assoc; exact HPERM).
assert (HP0X : Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx))
  by (unfold rk_X0; rewrite <- app_comm_cons, <- !app_assoc; exact HPERM0).
(* ---- 0x82f08 -> strncmp (key, F + 32, |prefix|) 0x82f5c: the shadow check of s->held, held + 8 n and its UBSan
   traps (0x82f18 decided by the seated condition, the rest by the seat's facts), held[n]'s shadow check, the key,
   88(sp) = F + 32 ---- *)
paj_run_tok_xR RUNG HS HJ SHOK rk_Bspan.
{ apply rk_awr_xR. }
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2.
assert (M01 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a)
  by (intros a Ha; exact (rk_nowin_xR E _ (w_H W1) m1 (ms_mem ms0) HFr0 eq_refl a Ha)).
assert (P01 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
  by (intros a Hp; eapply apresent_grows; [exact HG0 | exact Hp]).
assert (HSPc : spZ (ms_regs ms0) = gsp0 cx + -224).
{ unfold spZ at 1. rewrite QSP, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). lia. }
pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
destruct (rkr_pre_nz_xR cx) as (NZp & Lp16 & Lp27).
clear DTK DHK DFT DFH DFK HTHd.
assert (GkT : garr8 SEGS (arm W1 (ms_mem ms0)) key (bzs (kt ++ [Z_to_bv 8 0]))).
{ apply (rk_garr8_kv_xR (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ Gk). intros b Hb.
  unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
  apply M01. lia. }
assert (GpT : garr8 SEGS (arm W1 (ms_mem ms0)) (F + 32) (gpre cx ++ [0])).
{ apply (rk_garr8_kv_xR (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ HPRE). intros b Hb.
  rewrite length_app in Hb. cbn [length] in Hb. apply M01. lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 key) by (rewrite QA0, E34; reflexivity).
assert (QA1' : getr (ms_regs ms0) 11 = w64 (F + 32)) by (rewrite QA1, E36; reflexivity).
assert (QA2' : getr (ms_regs ms0) 12 = w64 (Z.of_nat (length (gpre cx)))) by (rewrite QA2, (EE 24%nat 24%bv eq_refl); exact R24).
assert (LKT : length (bzs (kt ++ [Z_to_bv 8 0])) = (length kt + 1)%nat) by (unfold bzs; rewrite length_map, length_app; reflexivity).
assert (LPT : length (gpre cx ++ [0]) = (length (gpre cx) + 1)%nat) by (rewrite length_app; reflexivity).
(* the key's and the prefix's bytes are visible *)
assert (VK : forall a, key <= a < key + Z.of_nat (length kt) + 1 -> aview SEGS (w_H W1) (ms_mem ms0) a <> None).
{ intros a Ha. replace a with (key + (a - key)) by lia. apply (rk_view_garr8_xR (w_H W1) (ms_mem ms0) key _ (a - key) GkT).
  rewrite LKT. lia. }
assert (VP : forall a, F + 32 <= a < F + 32 + Z.of_nat (length (gpre cx)) + 1 -> aview SEGS (w_H W1) (ms_mem ms0) a <> None).
{ intros a Ha. replace a with (F + 32 + (a - (F + 32))) by lia. apply (rk_view_garr8_xR (w_H W1) (ms_mem ms0) (F + 32) _ (a - (F + 32)) GpT).
  rewrite LPT. lia. }
assert (PSHT : garr8 SEGS (arm W1 (ms_mem ms0)) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]).
{ apply (rk_garr8_kv_xR (w_H W1) (w_H W1) m1 (ms_mem ms0) _ _ HPSH). intros b Hb. cbn [length] in Hb.
  apply M01. clear - Hb HF8 HFceil C1; unfold shadow_addr, SHADOW_OFF in *; lia. }
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
    + exact (rkr_first_key_xR W1 (ms_mem ms0) key kt (Z.of_nat (length (gpre cx))) ltac:(lia) GkT NZk).
    + exact (rkr_first_pre_xR W1 (ms_mem ms0) (F + 32) (gpre cx) GpT NZp).
    + clear - Hkceil Hrq2 C1. lia.
    + clear - HFceil C1 Lp27. lia.
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
        pose proof (rk_garr8_aview_xR (w_H W1) (ms_mem ms0) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0]
          (Z.to_nat ((x - F - 32) / 8)) PSHT ltac:(cbn [length]; lia)) as Hv.
        rewrite Z2Nat.id in Hv by lia. unfold shadow_addr in Hv. rewrite Ex. replace (SHADOW_OFF + (F / 8 + 4 + (x - F - 32) / 8)) with (SHADOW_OFF + F / 8 + 4 + (x - F - 32) / 8) by lia.
        rewrite Hv. f_equal. generalize (Z.to_nat ((x - F - 32) / 8)). intros j. destruct j as [|[|[|[|[|[|j]]]]]]; try reflexivity. destruct j; reflexivity.
      * intros _ sx Hsx. pose proof (rk_hull_xR F (Z.of_nat (length (gpre cx))) sx HFal ltac:(lia) Hsx) as Hs'.
        apply aview_some_of_apresent. apply P01. replace sx with (shadow_addr F + (sx - shadow_addr F)) by lia.
        exact (proj1 (HFSpres (sx - shadow_addr F) ltac:(lia))).
    + intros a Hin.
      assert (Hii : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
      pose proof (Hsegs a Hii) as Ha. rewrite M01; [exact (HROM1 a Hin) | clear - Ha C5; unfold kLowMemEnd in *; lia].
    + split.
      * eapply (rk_amr ly1 S1 W1 _ _ key (Z.of_nat (length kt) + 1)); [exact HAR2 | exact Hink | lia | clear - Hrq2 Lk; lia].
      * clear - HFapp C1 C4 C5. unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
cbv beta. intros W2 c2x _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HA0 & Hfr2 & Hpres2).
(* ---- back at 0x82f60: a0 = strncmp's result ---- *)
pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
destruct (rk_alb_xR ly1 S1 W1 mem2 _ _ _ HAR3 HinT) as (_ & _ & _ & _ & HTpres3 & _ & _).
destruct (rk_alb_xR ly1 S1 W1 mem2 _ _ _ HAR3 Hinh) as (_ & _ & _ & _ & Hhpres3 & _ & _).
jafter_call_keep_pi HS 37%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  assert (BV23 : base_val E (Some 23%nat) = gSA cx i + 48)
    by (cbn [base_val]; rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
  assert (BV25 : base_val E (Some 25%nat) = gSA cx i + 40)
    by (cbn [base_val]; rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
  assert (BV33 : base_val E (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
  assert (BV9 : base_val E (Some 9%nat) = gsp1 cx)
    by (cbn [base_val]; rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; unfold gsp1, RIG_FRAME; lia).
  repeat apply Forall_cons; [| | | | apply Forall_nil];
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV23, ?BV25, ?BV33, ?BV9;
   [ intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr2;
     [ clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn SPR C1; unfold gsp1, RIG_FRAME, AENT, ATABLE in *; lia
     | exact (fun H => H)
     | clear - Ha HTend HSA HT4096 HTceil Hh4096 Hhceil Hkh Hrk2 Hn SPR C1; unfold gsp1, RIG_FRAME, AENT, ATABLE, ESTACK in *; lia ]
   | intros a Ha _; lia ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 37 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall k0, (k0 < 37)%nat -> ew Ea k0 = ew E k0) by (intros k0 Hk0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hk0).
assert (HAEa : env_agree 32 (Ereg regs1 (rk_extra hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (F + 32))) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (SHOKa : sh_ok SEGS rk_Bx rk_SH Ea (mrestrict (w_H W1) mem2)).
{ apply (rk_shok_xR Ea W1 ly1 S1 mem2 _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HAR3).
  - rewrite OLDa by lia. rewrite (EE 21%nat 21%bv eq_refl). exact H21.
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
psrr_branch_tok RUNG BRR HS SHOKa rk_Bspan.
- (* ======== a0 <> 0: the key lacks the prefix (pass) ======== *)
  assert (Ha0ne : getr regs2 10 <> w64 0).
  { intros Hz. rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia.
    rewrite (U_atom Ea 41 0) in Hc; [discriminate Hc | rewrite <- R10a; exact Hz | lia]. }
  assert (HPF : has_prefix (gpre cx) (bzs kt) = false).
  { destruct (has_prefix (gpre cx) (bzs kt)) eqn:Hh; [exfalso|reflexivity].
    apply (proj2 (rkr_agree_xR W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp)) in Hh.
    exact (Ha0ne (proj2 HA0 Hh)). }
  (* 0x83098: nheld's shadow check (fast path), nheld, n += 1, 8 n, the loop test *)
  paj_run_tok_xR RUNG HS HJ2 SHOKa rk_Bspan.
  { apply rk_awr_xR. }
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  assert (GR : forall k0 (r0 : bv 5), (k0 < 37)%nat -> Z.of_nat k0 = bv_unsigned r0 -> ew Ea k0 = getr regs1 r0)
    by (intros k0 r0 Hk0 Hr0; rewrite OLDa by exact Hk0; apply EE; exact Hr0).
  psrr_branch_tok RUNG BRR HS SHOKa rk_Bspan.
  + (* n + 1 < nheld: through 0x82f04 (s6 = 8 (n + 1)) to the next key *)
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa rk_Bspan A_rig_inner.
    { apply rk_awr_xR. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    assert (Hn1 : (S n < length ks)%nat).
    { rewrite (rk_branch_lt_xR Ea (SOff 20 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_lt in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 20%nat 20%bv eq_refl), R20 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    destruct r as [|r']; [exfalso; lia|].
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { intros a Ha Hns.
      rewrite (rk_nowin_xR Ea _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 eq_refl a Ha).
      rewrite (rk_nowin_xR Ea _ (w_H W1) mem2 (ms_mem ms1) HFr1 eq_refl a Ha).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (21%bv : bv 5) T21.
    prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
    prreg_raw_xR HS (19%bv : bv 5) T19. prreg_raw_xR HS (22%bv : bv 5) T22. prreg_raw_xR HS (20%bv : bv 5) T20.
    prreg_raw_xR HS (27%bv : bv 5) T27. prreg_raw_xR HS (18%bv : bv 5) T18.
    pose proof (rkk_gin_xR cx i n (S r') F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 (ms_mem ms2) HB HJ0 HFR HGN KEEPf PRESf) as HGN2.
    destruct (rkb_gin_pass_xR cx i n r' F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
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
      rewrite T21, (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21. }
    split.
    { rewrite T19. cbn [sv_denot]. rewrite (GR 20%nat 20%bv ltac:(lia) eq_refl), R20. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, rk_sll3_add8_xR by lia. f_equal. lia. }
    split.
    { rewrite T22. cbn [sv_denot]. rewrite (GR 20%nat 20%bv ltac:(lia) eq_refl), R20. unfold w64.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, rk_sll3_add8_xR by lia. f_equal. lia. }
    split.
    { rewrite T20. cbn [sv_denot]. rewrite (GR 20%nat 20%bv ltac:(lia) eq_refl), R20. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal. lia. }
    split; [rewrite T23, (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23|].
    split.
    { rewrite T27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 21 0)) with (rk_sh 23).
      apply rk_sh_den_xR; [rewrite (GR 23%nat 23%bv ltac:(lia) eq_refl); exact R23 | rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split; [rewrite T24, (GR 24%nat 24%bv ltac:(lia) eq_refl); exact R24|].
    split; [rewrite T25, (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25|].
    split.
    { rewrite T18. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 21 0)) with (rk_sh 25).
      apply rk_sh_den_xR; [rewrite (GR 25%nat 25%bv ltac:(lia) eq_refl); exact R25 | rewrite (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M80].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; unfold gsp1, RIG_FRAME in *; lia]. }
    split; [exact (rkk_live_xR cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots_xR cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGN3.
  + (* n + 1 >= nheld: the entry's last key passed; the loop ends *)
    assert (Hn1 : (length ks <= S n)%nat).
    { rewrite (rk_branch_lt_xR Ea (SOff 20 1) (SOff 35 0) (Z.of_nat n + 1) (Z.of_nat (length ks))) in Hc0.
      - apply Z.ltb_ge in Hc0. lia.
      - cbn [sv_denot]. rewrite OLDa, (EE 20%nat 20%bv eq_refl), R20 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      - cbn [sv_denot]. rewrite OLDa, E35 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      - lia.
      - lia. }
    assert (r = 0%nat) by lia. subst r.
    paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa rk_Bspan A_rig_step.
    { apply rk_awr_xR. }
    rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
    assert (KEEPf : rkk_KEEP cx W1 m1 (ms_mem ms2)).
    { intros a Ha Hns.
      rewrite (rk_nowin_xR Ea _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 eq_refl a Ha).
      rewrite (rk_nowin_xR Ea _ (w_H W1) mem2 (ms_mem ms1) HFr1 eq_refl a Ha).
      rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
      exact (M01 a Ha). }
    assert (PRESf : rkk_PRES W1 m1 (ms_mem ms2)).
    { intros a Hp. eapply apresent_grows; [exact HG2|]. eapply apresent_grows; [exact HG1|]. apply Hpres2. exact (P01 a Hp). }
    pmkst HS.
    prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
    prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (21%bv : bv 5) T21.
    pose proof (rkk_gin_xR cx i n 0 F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 (ms_mem ms2) HB HJ0 HFR HGN KEEPf PRESf) as HGN2.
    pose proof (rkb_gout_pass_xR cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
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
      rewrite T21, (GR 21%nat 21%bv ltac:(lia) eq_refl); exact H21. }
    split.
    { apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms2) _ 8 _); [|exact M80].
      intros kk Hkk. apply KEEPf; [clear - Hkk SPR C1; unfold gsp1, RIG_FRAME in *; lia | clear - Hkk; unfold gsp1, RIG_FRAME in *; lia]. }
    split; [exact Hi|].
    split; [exact (rkk_live_xR cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem ms2) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPf PRESf)|].
    split; [exact (rkk_lslots_xR cx F W1 m1 (ms_mem ms2) HLS KEEPf)|].
    exact HGO.
- (* ======== a0 = 0: the key has the prefix (end) ======== *)
  assert (Ha0z : getr regs2 10 = w64 0).
  { rewrite branch_ne_U, (U_lit Ea 0) in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rv. change (bv_modulus 64) with (2 ^ 64) in Rv.
    rewrite (U_atom Ea 41 (bv_unsigned (getr regs2 10))) in Hc; [| rewrite <- R10a, Z_to_bv_bv_unsigned; reflexivity | exact Rv].
    rewrite <- (Z_to_bv_bv_unsigned _ (getr regs2 10)), Hc. reflexivity. }
  assert (HPT : has_prefix (gpre cx) (bzs kt) = true)
    by exact (proj1 (rkr_agree_xR W1 (ms_mem ms0) key (F + 32) kt (gpre cx) GkT NZk GpT NZp) (proj1 HA0 Ha0z)).
  (* 0x82f64: mv a0,s10; gesture_end (key) at 0x82f68 *)
  paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa rk_Bspan AF_fr_gesture_end.
  { apply rk_awr_xR. }
  rename ms into msg, mat into matg, HF into HFg, HFr into HFrg, HG into HGg.
  pmkst HS.
  prreg HS (1%bv : bv 5) G1. prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
  prreg HS (8%bv : bv 5) G8. prreg HS (10%bv : bv 5) G10.
  (* the cut's predicates at gesture_end's call: the strncmp call and the runs wrote only below sp *)
  assert (KEEPg : rkk_KEEP cx W1 m1 (ms_mem msg)).
  { intros a Ha Hns.
    rewrite (rk_nowin_xR Ea _ (w_H W1) mem2 (ms_mem msg) HFrg eq_refl a Ha).
    rewrite (Hfr2 a Ha (fun H => H)) by (clear - Hns SPR; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia).
    exact (M01 a Ha). }
  assert (PRESg : rkk_PRES W1 m1 (ms_mem msg)).
  { intros a Hp. eapply apresent_grows; [exact HGg|]. apply Hpres2. exact (P01 a Hp). }
  pose proof (rkk_gin_xR cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed f c2 O2 cap2 out2 spent
    ly1 S1 W1 m1 md1 k1 (ms_mem msg) HB HJ0 HFR HGN KEEPg PRESg) as HGNg.
  pose proof (rkk_live_xR cx F FL fpos ly1 S1 W1 m1 md1 k1 (ms_mem msg) _ _ HB HJ0 HROM1 HPK HFR HLK HJ2 KEEPg PRESg) as HLVg.
  pose proof (rkk_lslots_xR cx F W1 m1 (ms_mem msg) HLS KEEPg) as HLSg.
  pose proof HLVg as (fposg & Hpg & HJg & HROMg & HPKg & HFRg & HLKg).
  pose proof HFRg as (_ & _ & _ & _ & _ & _ & _ & HSVg).
  pose proof HGNg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOUTg & _).
  pose proof (rkk_ceil_xR cx HB) as HCEIL.
  destruct (rk_achain_xR cx ly1 W1 (ms_mem msg) HB HSVg
    ltac:(eapply rk_ly_top_xR; exact HJ2)
    ltac:(intros a Ha; eapply (rk_keep_high_xR (G_RIG B RG)); [exact HGRIG | exact HJ2 | lia | rewrite WS; lia])) as (ch1 & Hch1).
  destruct (rk_aout_facts_xR _ _ _ _ _ _ _ _ _ _ HOUTg) as (Hmx2 & _ & Hcd2).
  assert (Hcap2 : 0 <= cap2) by (destruct Hcd2 as [(-> & _) | (? & _)]; lia).
  destruct (rkb_gbase_facts_xR cx HB) as (Hmx & _).
  (* entry i's key run: the key ended now, then the rest *)
  destruct f as [|f0]; [exfalso; lia|].
  pose proof (rkb_geik_end_xR f0 (gpre cx) n ks Hn HPT) as EGK.
  set (ks' := swap_remove (0, [], []) n ks) in *.
  set (Er' := fst (geik_loop f0 (gpre cx) n ks')) in *.
  pose proof HBUD as HBUD0. cbv zeta in HBUD0. rewrite EGK in HBUD0. cbn [fst] in HBUD0. fold k in HBUD0.
  remember (sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (k :: Er'))) as SS eqn:ESS in HBUD0.
  destruct SS as [[c3x O3] cap3]. cbn beta iota in HBUD0.
  assert (HGs : rk_sizes (grest cx (S i) (Z.of_nat (length O3)) cap3)).
  { apply rkb_grest_sizes_xR; [exact HB | lia |].
    pose proof (rkb_sends_cap_nonneg_xR (gxmx cx) (ge_bytes (k :: Er')) c2 O2 cap2 Hcap2) as Hc3. rewrite <- ESS in Hc3. exact Hc3. }
  assert (HLV2 : sl_live c2 1 = sl_live (gxc cx) 1)
    by exact (rkb_live_gin_xR cx i n r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent ly1 S1 W1 m1 HGN).
  assert (Hxl : 0 < Z.of_nat (length kt)) by lia.
  destruct (rkb_ge_room_xR cx ly1 S1 spent c2 (Z.of_nat (length O2)) cap2 k Er' _ HBUD0 HGs HLV2 ltac:(lia) ltac:(lia) Hcap2 Hxl)
    as (RM1 & RM2 & RM3).
  fold kt in RM1, RM2, RM3.
  (* the room record's premises of gesture_end (at kr := S (rk_krn ..)) and of the free (the counts at most one above
     GIN's), from GIN's gbud *)
  destruct (rk_room_xR cx i n r F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent ly1 S1 W1
    (ms_mem msg) HB HGNg HPT) as (_ & _ & _ & _ & _ & RMg & CNg & CNle).
  assert (ROOMg : ge_room MMAX (blocks_bytes S1) c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))).
  { unfold ge_room, ge_tr. rewrite (rkb_live_pos_xR c2 (Z.of_nat (length kt)) Hxl). split; [exact RM1 | exact RM2]. }
  assert (Hgc0 : 0 <= ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)))
    by (apply rkb_ge_cost_nonneg_xR; lia).
  pose proof (mo_free_nonneg MT MLAW) as Hmf.
  assert (MOKg : mo_ok MT S1 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))))
    by (apply (rkb_mok_xR cx ly1 S1 spent _ _ HB HBUD0 Hgc0); lia).
  (* the key is not the output buffer *)
  assert (HinO2 : cap2 <> 0 -> In (out2, cap2) XG).
  { intros Hcz. unfold XG. right. rewrite !app_assoc. apply in_or_app. right. unfold aout_blks.
    rewrite (proj2 (Z.eqb_neq cap2 0) Hcz). left. reflexivity. }
  assert (HinKA : In (key, Z.of_nat (length kt) + 1)
    (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))))).
  { apply in_concat. exists (aentry_blks (entry_keys e1 ks)). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. right. cbn [re_keys entry_keys].
      apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). apply nth_In. exact Hn. }
  assert (HinKX : In (key, Z.of_nat (length kt) + 1) XG) by (unfold XG; right; apply in_or_app; left; exact HinKA).
  assert (HKO : key <> out2).
  { destruct Hcd2 as [(_ & -> & _) | (Hc0 & _ & HinO)]; [lia|].
    intros Heq.
    assert (Hne : (key, Z.of_nat (length kt) + 1) <> (out2, cap2)).
    { intros Hcq. pose proof HNDP as HND2. apply List.NoDup_cons_iff in HND2 as [_ HND2].
      apply (rk_nodup_app_disj_xR _ _ (key, Z.of_nat (length kt) + 1) HND2 HinKA).
      rewrite Hcq. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq cap2 0) ltac:(lia)). left; reflexivity. }
    destruct (rk_blk_apart_xR ly1 S1 W1 m1 md1 _ _ HAR1 Hink HinO Hne) as [Hd | Hd]; cbn [fst snd] in Hd;
    pose proof (req_size_pos cap2 ltac:(lia)); lia. }
  change (BASE + 14288) with (BASE + AF_fr_gesture_end).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (rk_ge_xR W1 (ms_regs msg) (ms_mem msg) _ (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (gxmd cx)
      [(1, fpos)] ly1 S1 _ (Z_to_bv 64 (BASE + A_rig_ge_ret)) ch1 c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 kt key
      (Z.of_nat (length kt) + 1) HJ2).
    - unfold spZ at 1. rewrite G2, OLDa, (EE 2%nat 2%bv eq_refl) by lia. fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia.
    - replace (gsp0 cx) with (2 * (gsp0 cx / 32) * 16) by (pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)); lia). apply Z_mod_mult.
    - rewrite G3, OLDa, (EE 3%nat 3%bv eq_refl), Hgp1 by lia. exact Hgp.
    - rewrite G4, OLDa, (EE 4%nat 4%bv eq_refl), Htp1 by lia. exact Htp.
    - exact G1.
    - unfold A_rig_ge_ret, A_rig_inner, AF_fr_relay_instance_gone. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold A_rig_ge_ret, A_rig_inner, AF_fr_relay_instance_gone. rewrite unsigned_lit_small by lia. lia.
    - replace (gsp0 cx - 224) with (gsp1 cx) by (unfold gsp1, RIG_FRAME; lia).
      replace (s0Z (ms_regs msg)) with (gsp0 cx); [exact Hch1|].
      unfold s0Z. rewrite G8, OLDa, (EE 8%nat 8%bv eq_refl), H8 by lia. unfold w64. rewrite unsigned_lit_small by (unfold gsp0 in *; lia). reflexivity.
    - rewrite G10, OLDa, E34 by lia. reflexivity.
    - exact HOUTg.
    - apply (rk_garr8_kv_xR (w_H W1) (w_H W1) m1 (ms_mem msg) _ _ Gk). intros b Hb.
      unfold bzs in Hb. rewrite length_map, length_app in Hb. cbn [length] in Hb.
      apply KEEPg; lia.
    - exact NZk.
    - exact Lk.
    - exact Hink.
    - exact HKO.
    - lia.
    - exact (rk_end5_xR W1 (ms_mem msg) HROMg).
    - exact HROMg.
    - exact ROOMg.
    - exact MOKg.
    - exact RMg.
    - exact CNg.
    - intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n0 & Hpin & Hpa).
      unfold aout_blks in Hpin. destruct (Z.eqb_spec cap2 0) as [Hz | Hnz]; [destruct Hpin|].
      destruct Hpin as [Hpe | []]. injection Hpe as <- <-.
      exact (rk_fp_blk_xR cx ly1 S1 W1 m1 md1 XG out2 cap2 a HAR1 HP0X HPX (HinO2 Hnz) Hpa). }
  cbv beta. intros W2 c2x Hwle2 (ly2 & S2 & regs3 & mem3 & md3 & kg & out3 & -> & HJ3 & (ksl & HJsl) & HP3 & HAK3 & HM3 &
    HRMge & (restG & HPa & HPb) & HO3).
  (* ---- back at 0x82f6c ---- *)
  pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARge.
  assert (HGSL : gx_ok SEGS B (G_SL B RG)) by exact (gx_ok_sub SEGS B _ _ (rig_G_SL_RIG B RG) HGRIG).
  set (cap3' := ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))) in *.
  set (XGa := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx))).
  assert (HXG : XG = XGa ++ aout_blks cap2 out2) by (unfold XG, XGa; rewrite <- app_comm_cons, <- !app_assoc; reflexivity).
  assert (HPq1 : Permutation (ablocks B ly1 S1) (XGa ++ aout_blks cap2 out2 ++ gxrest cx))
    by (rewrite app_assoc, <- HXG; exact HPX).
  assert (HND1X : List.NoDup (XGa ++ aout_blks cap2 out2 ++ gxrest cx)) by exact (Permutation_NoDup HPq1 HND1).
  assert (HPR : Permutation restG (XGa ++ gxrest cx)).
  { apply (Permutation_app_inv_l (aout_blks cap2 out2)). eapply perm_trans; [apply Permutation_sym; exact HPa|].
    eapply perm_trans; [exact HPq1|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (HPq2 : Permutation (ablocks B ly2 S2) (XGa ++ aout_blks cap3' out3 ++ gxrest cx)).
  { eapply perm_trans; [exact HPb|]. eapply perm_trans; [apply Permutation_app_head; exact HPR|].
    rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  pose proof (rk_ablocks_nodup_xR _ _ _ _ _ HARge) as HNDge.
  assert (HNDgX : List.NoDup (XGa ++ aout_blks cap3' out3 ++ gxrest cx)) by exact (Permutation_NoDup HPq2 HNDge).
  assert (INX1 : forall b, In b XGa -> In b (ablocks B ly1 S1))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPq1)); apply in_or_app; left; exact Hb).
  assert (INX2 : forall b, In b XGa -> In b (ablocks B ly2 S2))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPq2)); apply in_or_app; left; exact Hb).
  assert (NOX1 : forall b, In b XGa -> ~ In b (aout_blks cap2 out2)).
  { intros b Hb Ho. apply (rk_nodup_app_disj_xR XGa _ b HND1X Hb). apply in_or_app. left. exact Ho. }
  assert (HinT1X : In (gxG0 cx, ATABLE) XGa) by (left; reflexivity).
  assert (Hinh1X : In (hp, re_kh e1) XGa) by (right; apply in_or_app; left; exact HinHP).
  assert (Hink1X : In (key, Z.of_nat (length kt) + 1) XGa) by (right; apply in_or_app; left; exact HinKA).
  pose proof (INX2 _ HinT1X) as HinT2. pose proof (INX2 _ Hinh1X) as Hinh2. pose proof (INX2 _ Hink1X) as Hink2.
  (* what gesture_end kept: the caller's blocks other than the output buffer, the stack above its window *)
  assert (KGEa : forall b, In b XGa -> forall a, fst b <= a < fst b + req_size (snd b) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W1) (ms_mem msg) a).
  { intros [p nb] Hb a Ha. cbn [fst snd] in Ha. replace a with (p + (a - p)) by lia.
    apply (rk_keep_blk_xR (G_SL B RG) 0 [] GE_STK (gsp0 cx - 224) (ablocks_fp (aout_blks cap2 out2)) ly1 S1 W1 (ms_mem msg) _ []
      ly2 S2 W2 mem3 md3 ksl p nb (a - p) HGSL HJsl (INX1 _ Hb) (INX2 _ Hb) ltac:(lia)).
    intros Hcf. apply inFP_ablocks_fp_inv in Hcf as (q & m & Hqin & Hqa).
    assert (Hne : (p, nb) <> (q, m)) by (intros Heq; rewrite Heq in Hb; exact (NOX1 _ Hb Hqin)).
    assert (Hqin1 : In (q, m) (ablocks B ly1 S1))
      by (apply (Permutation_in _ (Permutation_sym HPq1)); apply in_or_app; right; apply in_or_app; left; exact Hqin).
    destruct (rk_disj_xR ly1 S1 W1 m1 md1 p nb q m HAR1 (INX1 _ Hb) Hqin1 Hne); lia. }
  assert (KGEh : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (gsp0 cx - 224 - GE_STK <= a < gsp0 cx - 224) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W1) (ms_mem msg) a).
  { intros a Ha Hno. apply (rk_keep_high_xR (G_SL B RG) 0 [] GE_STK (gsp0 cx - 224) _ ly1 S1 W1 (ms_mem msg) _ []
      ly2 S2 W2 mem3 md3 ksl HGSL HJsl a Ha). lia. }
  assert (BVa : forall k0 v, (k0 < 37)%nat -> ew E k0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val Ea (Some k0) = v).
  { intros k0 v Hk0 Hv Hr. cbn [base_val]. rewrite OLDa by exact Hk0. rewrite Hv. apply unsigned_lit_small. exact Hr. }
  jafter_call_keep_pi HS 53%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2; 3]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    assert (BV23a : base_val Ea (Some 23%nat) = gSA cx i + 48)
      by (apply BVa; [lia | rewrite (EE 23%nat 23%bv eq_refl); exact R23 | unfold AENT, ATABLE in *; lia]).
    assert (BV25a : base_val Ea (Some 25%nat) = gSA cx i + 40)
      by (apply BVa; [lia | rewrite (EE 25%nat 25%bv eq_refl); exact R25 | unfold AENT, ATABLE in *; lia]).
    assert (BV33a : base_val Ea (Some 33%nat) = hp + 8 * Z.of_nat n) by (apply BVa; [lia | exact E33 | lia]).
    assert (BV9a : base_val Ea (Some 9%nat) = gsp1 cx)
      by (apply BVa; [lia | rewrite (EE 9%nat 9%bv eq_refl); exact H9 | unfold gsp1, RIG_FRAME; lia]).
    repeat apply Forall_cons; [| | | | apply Forall_nil];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV23a, ?BV25a, ?BV33a, ?BV9a;
     [ intros a Ha; apply (mbyte_of_aview SEGS);
       first [ apply (KGEa _ HinT1X); cbn [fst snd]; change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia
             | apply (KGEa _ Hinh1X); cbn [fst snd]; lia
             | apply KGEh; [unfold gsp1, RIG_FRAME in *; lia | assert (GE_STK = 16544) by reflexivity; unfold gsp1, RIG_FRAME in *; lia] ]
     | intros a Ha _; lia ]). }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 53 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall k0, (k0 < 53)%nat -> ew Eb k0 = ew Ea k0) by (intros k0 Hk0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hk0).
  clear HEb.
  assert (SHOKb : sh_ok SEGS rk_Bx rk_SH Eb (mrestrict (w_H W2) mem3)).
  { apply (rk_shok_xR Eb W2 ly2 S2 mem3 _ (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n) (Z.of_nat (length ks)) HARge).
    - rewrite OLDb, OLDa by lia. rewrite (EE 21%nat 21%bv eq_refl). exact H21.
    - rewrite OLDb, OLDa by lia. rewrite (EE 23%nat 23%bv eq_refl). exact R23.
    - rewrite OLDb, OLDa by lia. rewrite (EE 25%nat 25%bv eq_refl). exact R25.
    - rewrite OLDb, OLDa by lia. exact E33.
    - exact HinT2.
    - clear - HSA. lia.
    - exact HTend.
    - exact Hinh2.
    - exact Hkh.
    - clear - Hn. lia. }
  (* 0x82f6c: the checks again, held[n], free (key) at 0x82fb4 *)
  paj_run_tok_xR RUNG HS HJ3 SHOKb rk_Bspan.
  { apply rk_awr_xR. }
  rename ms into msf, mat into matf, HF into HFf, HFr into HFrf, HG into HGf.
  pmkst HS.
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (10%bv : bv 5) F10.
  prreg HS (9%bv : bv 5) F9. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
  prreg HS (23%bv : bv 5) F23. prreg HS (25%bv : bv 5) F25. prreg HS (24%bv : bv 5) F24.
  prreg_raw_xR HS (18%bv : bv 5) F18. prreg_raw_xR HS (22%bv : bv 5) F22. prreg_raw_xR HS (27%bv : bv 5) F27.
  assert (KRf : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem3 a)
    by (intros a Ha; exact (rk_nowin_xR Eb _ (w_H W2) mem3 (ms_mem msf) HFrf eq_refl a Ha)).
  assert (HSVf : g_saved cx W2 (ms_mem msf)).
  { intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) (ms_mem msg) (ms_mem msf) _ 8 _); [|exact (HSVg j Hj)].
    intros kk Hkk. assert (GE_STK = 16544) by reflexivity.
    rewrite KRf by (unfold gsp1, RIG_FRAME in *; lia). apply KGEh; unfold gsp1, RIG_FRAME in *; lia. }
  (* the free's caller context (GCTX): the entry's frame is below the layout top, so the chain at 0x82fb4 is the
     entry's chain under relay_instance_gone's frame record (gsp0, ra, s0) *)
  assert (TOP2 : gsp0 cx < ly_top (gxly cx) - 16) by (destruct HCTX as (HCT1 & _); unfold gsp0; clear - HCT1; lia).
  pose proof (rk_achainp_xR cx ly2 W2 (ms_mem msf) HB HSVf
    ltac:(eapply rk_ly_top_xR; exact HJ3)
    ltac:(intros a Ha; eapply (rk_keep_high_xR (G_RIG B RG)); [exact HGRIG | exact HJ3 | lia | rewrite WS; lia]) TOP2) as Hch2.
  destruct HBUD0 as (Hle0 & Hsp0 & Hc0 & _).
  assert (MOKf : mo_ok MT S2 (mo_free MT))
    by exact (mok_station MT (gxS cx) S2 (tr_cost MT (gtr cx))
      (spent + ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))) (mo_free MT) MLAW HMOK
      (mo_le_trans MT MLAW _ _ _ _ _ Hle0 HM3) Hmf ltac:(lia)).
  rewrite (pal_free B TL).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (rk_free_xR (G_RIG B RG) W2 (ms_regs msf) (ms_mem msf) RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxW cx)
      (gxmem cx) (gxmd cx) [(1, fpos)] ly2 S2 _ _ key (Z.of_nat (length kt) + 1) (-224)
      (Z_to_bv 64 (BASE + A_rig_fr_ret)) ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx) HJ3).
    - exact Hink2.
    - rewrite F10, OLDb, OLDa, E34 by lia. reflexivity.
    - unfold spZ at 1. rewrite F2, OLDb, OLDa, (EE 2%nat 2%bv eq_refl) by lia. fold (spZ regs1). rewrite Hsp1. unfold gsp1, RIG_FRAME. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ASTACK. lia.
    - rewrite F3, OLDb, OLDa, (EE 3%nat 3%bv eq_refl), Hgp1 by lia. exact Hgp.
    - rewrite F4, OLDb, OLDa, (EE 4%nat 4%bv eq_refl), Htp1 by lia. exact Htp.
    - exact F1.
    - unfold A_rig_fr_ret, A_rig_inner, AF_fr_relay_instance_gone. apply ret_ok_codeptr_v; [lia | reflexivity].
    - apply (achain_chain_pre ly2 _ (gsp1 cx) (gsp0 cx) _ (ms_regs msf) Hch2).
      + unfold spZ. rewrite F2, OLDb, OLDa, (EE 2%nat 2%bv eq_refl) by lia. fold (spZ regs1). rewrite Hsp1.
        unfold gsp1, RIG_FRAME in *. lia.
      + unfold s0Z. rewrite F8, OLDb, OLDa, (EE 8%nat 8%bv eq_refl), H8 by lia. unfold w64.
        rewrite unsigned_lit_small by (unfold gsp0 in *; lia). reflexivity.
      + unfold raZ. rewrite F1. unfold A_rig_fr_ret, A_rig_inner, AF_fr_relay_instance_gone.
        rewrite unsigned_lit_small by lia. lia.
    - destruct HCTX as (_ & HCT2). replace (raZ (ms_regs msf)) with (A_rig_entryP + 792); [exact HCT2|].
      unfold raZ. rewrite F1. unfold A_rig_fr_ret, A_rig_inner, A_rig_entryP, A_rig_entry, AF_fr_relay_instance_gone.
      rewrite unsigned_lit_small by lia. ring.
    - intros Hin0 j Hj. exact (rk_fp_orig_xR cx ly1 S1 W1 m1 md1 XG key (Z.of_nat (length kt) + 1) HAR1 HP0X HPX HinKX Hin0 j Hj).
    - exact MOKf.
    - exact HRMge.
    - apply CNle. intros P. exact (rkc_cnt_out_le_xR P ly1 S1 ly2 S2 cap2 out2 _ out3 restG HPa HPb). }
  cbv beta. intros W3 cfr Hwle3 (ly3 & S3 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & EL1 & EL2) & Hfrm3 & HK4 & HM4 &
    HRMf & HE4 & HPK4).
  (* ---- back at 0x82fb8 ---- *)
  pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HARfr.
  (* the key's count change: gesture_end's send chain moves g_out's own count exactly, the free drops the key's block
     (lib/B/W_rig_key_b.v rkc_end_cnt_xR) *)
  pose proof (fun P => rkc_end_cnt_xR P c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt))
    ly1 S1 ly2 S2 ly3 S3 out2 out3 restG l1 l2 key Hxl Hcap2 HPa HPb EL1 EL2) as HCN3.
  set (XGb := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx))).
  assert (HXab : Permutation XGa ((key, Z.of_nat (length kt) + 1) :: XGb)).
  { unfold XGa, XGb. eapply perm_trans;
      [apply perm_skip; apply Permutation_app_tail; exact (rk_perm_keys (map fst qd) (skipn (S i) (gxes cx)) e1 ks n Hn)|].
    cbn [app]. apply perm_swap. }
  assert (HPq3 : Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3' out3 ++ gxrest cx)).
  { rewrite EL2. apply Permutation_sym. apply Permutation_cons_app_inv with (a := (key, Z.of_nat (length kt) + 1)).
    rewrite <- EL1. eapply perm_trans; [|apply Permutation_sym; exact HPq2].
    change ((key, Z.of_nat (length kt) + 1) :: XGb ++ aout_blks cap3' out3 ++ gxrest cx)
      with (((key, Z.of_nat (length kt) + 1) :: XGb) ++ aout_blks cap3' out3 ++ gxrest cx).
    apply Permutation_app_tail. apply Permutation_sym. exact HXab. }
  assert (HNDb : List.NoDup ((key, Z.of_nat (length kt) + 1) :: XGb ++ aout_blks cap3' out3 ++ gxrest cx)).
  { apply (Permutation_NoDup (l := XGa ++ aout_blks cap3' out3 ++ gxrest cx)); [|exact HNDgX].
    change ((key, Z.of_nat (length kt) + 1) :: XGb ++ aout_blks cap3' out3 ++ gxrest cx)
      with (((key, Z.of_nat (length kt) + 1) :: XGb) ++ aout_blks cap3' out3 ++ gxrest cx).
    apply Permutation_app_tail. exact HXab. }
  assert (INX3 : forall b, In b XGb -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPq3)); apply in_or_app; left; exact Hb).
  assert (XbA : forall b, In b XGb -> In b XGa)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HXab)); right; exact Hb).
  assert (NKb : forall b, In b XGb -> b <> (key, Z.of_nat (length kt) + 1)).
  { intros b Hb Heq. apply List.NoDup_cons_iff in HNDb as [Hni _]. apply Hni. rewrite <- Heq. apply in_or_app. left. exact Hb. }
  (* every byte of a block the end arm kept, from the cut's state to after free *)
  assert (KALL : forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros [p nb] Hb a Ha. cbn [fst snd] in Ha.
    pose proof HK4 as (_ & K4b & _).
    destruct (rk_alb_xR ly1 S1 W1 m1 md1 p nb HAR1 (INX1 _ (XbA _ Hb))) as (_ & Hp4 & Hpc & _).
    replace a with (p + (a - p)) by lia.
    rewrite (K4b p nb (a - p) (INX2 _ (XbA _ Hb)) ltac:(lia)).
    2: { intros Hka. destruct (rk_disj_xR ly2 S2 W2 mem3 md3 p nb key (Z.of_nat (length kt) + 1) HARge (INX2 _ (XbA _ Hb)) Hink2 (NKb _ Hb)); lia. }
    replace (p + (a - p)) with a by lia.
    rewrite KRf by lia. rewrite (KGEa (p, nb) (XbA _ Hb) a ltac:(cbn [fst snd]; lia)).
    apply KEEPg; lia. }
  assert (HinT3X : In (gxG0 cx, ATABLE) XGb) by (left; reflexivity).
  assert (Hinh3X : In (hp, re_kh e1) XGb).
  { right. apply in_or_app. left. apply in_concat. exists (aentry_blks (entry_keys e1 ks')). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
      fold hp. destruct (Z.eqb_spec hp 0); [contradiction | left; reflexivity]. }
  assert (VKT : forall a, gxG0 cx <= a < gxG0 cx + 896 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a)
    by (intros a Ha; apply (KALL _ HinT3X); cbn [fst snd]; change (req_size ATABLE) with 896; exact Ha).
  assert (VKH : forall a, hp <= a < hp + re_kh e1 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a)
    by (intros a Ha; apply (KALL _ Hinh3X); cbn [fst snd]; lia).
  assert (Mhp4 : val_mem SEGS (arm W3 mem4) (gSA cx i + 40) 8 hp).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 8 _); [|exact Mhp].
    intros kk Hkk. apply VKT. unfold AENT, ATABLE in *. lia. }
  assert (Mnh4 : val_mem SEGS (arm W3 mem4) (gSA cx i + 48) 4 (Z.of_nat (length ks))).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 4 _); [|exact Mnh].
    intros kk Hkk. apply VKT. unfold AENT, ATABLE in *. lia. }
  assert (Mkey4 : val_mem SEGS (arm W3 mem4) (hp + 8 * Z.of_nat n) 8 key).
  { apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 8 _); [|exact (Mslot n Hn)].
    intros kk Hkk. apply VKH. lia. }
  (* the registers at free's return: the loop head's, preserved by both calls *)
  assert (QV : forall (b : bv 5) rr, bv_unsigned b = rr -> acallee_saved rr -> getr regs4 b = getr (ms_regs msf) b)
    by (intros b rr Hb Hr; exact (rk_pres_reg (ms_regs msf) regs4 rr b HP4 Hb Hr)).
  assert (Q2 : spZ regs4 = gsp1 cx).
  { unfold spZ at 1. rewrite (QV 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia)), F2, OLDb, OLDa, (EE 2%nat 2%bv eq_refl) by lia.
    fold (spZ regs1). exact Hsp1. }
  assert (Q9 : getr regs4 9 = w64 (gsp1 cx))
    by (rewrite (QV 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia)), F9, OLDb, OLDa, (EE 9%nat 9%bv eq_refl) by lia; exact H9).
  assert (Q21 : getr regs4 21 = w64 SHADOW_OFF)
    by (rewrite (QV 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia)), F21, OLDb, OLDa, (EE 21%nat 21%bv eq_refl) by lia; exact H21).
  assert (Q19 : getr regs4 19 = w64 (8 * Z.of_nat n))
    by (rewrite (QV 19%bv 19 eq_refl ltac:(unfold acallee_saved; lia)), F19, OLDb, OLDa, (EE 19%nat 19%bv eq_refl) by lia; exact R19).
  assert (Q20 : getr regs4 20 = w64 (Z.of_nat n))
    by (rewrite (QV 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia)), F20, OLDb, OLDa, (EE 20%nat 20%bv eq_refl) by lia; exact R20).
  assert (Q23 : getr regs4 23 = w64 (gSA cx i + 48))
    by (rewrite (QV 23%bv 23 eq_refl ltac:(unfold acallee_saved; lia)), F23, OLDb, OLDa, (EE 23%nat 23%bv eq_refl) by lia; exact R23).
  assert (Q25 : getr regs4 25 = w64 (gSA cx i + 40))
    by (rewrite (QV 25%bv 25 eq_refl ltac:(unfold acallee_saved; lia)), F25, OLDb, OLDa, (EE 25%nat 25%bv eq_refl) by lia; exact R25).
  assert (Q22 : getr regs4 22 = w64 (8 * Z.of_nat n)).
  { rewrite (QV 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia)), F22. cbn [sv_denot].
    rewrite OLDb, OLDa, (EE 19%nat 19%bv eq_refl), R19 by lia. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (Q18 : getr regs4 18 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8)).
  { rewrite (QV 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia)), F18.
    apply rk_sh_den_xR; [rewrite OLDb, OLDa, (EE 25%nat 25%bv eq_refl) by lia; exact R25
      | rewrite OLDb, OLDa, (EE 21%nat 21%bv eq_refl) by lia; exact H21 | unfold AENT, ATABLE in *; lia]. }
  assert (Q27 : getr regs4 27 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8)).
  { rewrite (QV 27%bv 27 eq_refl ltac:(unfold acallee_saved; lia)), F27.
    apply rk_sh_den_xR; [rewrite OLDb, OLDa, (EE 23%nat 23%bv eq_refl) by lia; exact R23
      | rewrite OLDb, OLDa, (EE 21%nat 21%bv eq_refl) by lia; exact H21 | unfold AENT, ATABLE in *; lia]. }
  assert (HBLK : hp + re_kh e1 <= gSA cx i + 40 \/ gSA cx i + 52 <= hp).
  { pose proof (rk_blk_apart_xR ly1 S1 W1 m1 md1 _ _ HAR1 HinT Hinh HTH) as HTHd2. cbn [fst snd] in HTHd2.
    change (req_size ATABLE) with 896 in HTHd2. clear - HTHd2 HTend HSA Hrk2. unfold AENT, ATABLE in *. lia. }
  pose proof (INX3 _ HinT3X) as HinT4. pose proof (INX3 _ Hinh3X) as Hinh4.
  (* the last key, held[nheld - 1] *)
  assert (Hnl : (length ks - 1 < length ks)%nat) by lia.
  pose proof (rkr_entry_at_xR ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) (length ks - 1) HAR1 HRLY Hnl) as XL.
  cbv zeta in XL. destruct XL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HinkL & _).
  set (klast := key_addr (nth (length ks - 1) ks (0, [], []))) in *.
  destruct (rk_alb_xR ly1 S1 W1 m1 md1 _ _ HAR1 HinkL) as (_ & HkL4096 & HkLceil & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text (nth (length ks - 1) ks (0, [], [])))) + 1) ltac:(lia)) as [HrL1 _].
  assert (MkL4 : val_mem SEGS (arm W3 mem4) (hp + 8 * (Z.of_nat (length ks) - 1)) 8 klast).
  { replace (Z.of_nat (length ks) - 1) with (Z.of_nat (length ks - 1)) by lia.
    apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 mem4 _ 8 _); [|exact (Mslot _ Hnl)].
    intros kk Hkk. apply VKH. lia. }
  assert (AWT3 : forall own a, gSA cx i + 48 <= a < gSA cx i + 52 ->
    awr_byte RIG_STK_x (gsp0 cx) (gFP cx) (ablocks B (gxly cx) (gxS cx)) (ablocks B ly3 S3) ly3 own a).
  { intros own a Ha. apply (rk_wr_blk_xR cx ly3 S3 W3 mem4 md4 (XGb ++ aout_blks cap3' out3) own (gxG0 cx) ATABLE a HARfr HP0X);
      [rewrite <- app_assoc; exact HPq3 | apply in_or_app; left; exact HinT3X | change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia]. }
  assert (AWH3 : forall own a, hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8 ->
    awr_byte RIG_STK_x (gsp0 cx) (gFP cx) (ablocks B (gxly cx) (gxS cx)) (ablocks B ly3 S3) ly3 own a).
  { intros own a Ha. apply (rk_wr_blk_xR cx ly3 S3 W3 mem4 md4 (XGb ++ aout_blks cap3' out3) own hp (re_kh e1) a HARfr HP0X);
      [rewrite <- app_assoc; exact HPq3 | apply in_or_app; left; exact Hinh3X | lia]. }
  (* ---- the bytes the end arm keeps, from the cut's state to free's return ---- *)
  assert (Q3 : getr regs4 3 = getr (gxregs cx) 3)
    by (rewrite (QV 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia)), F3, OLDb, OLDa, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp1).
  assert (Q4 : getr regs4 4 = getr (gxregs cx) 4)
    by (rewrite (QV 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia)), F4, OLDb, OLDa, (EE 4%nat 4%bv eq_refl) by lia; exact Htp1).
  assert (Q8 : getr regs4 8 = w64 (gsp0 cx))
    by (rewrite (QV 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia)), F8, OLDb, OLDa, (EE 8%nat 8%bv eq_refl) by lia; exact H8).
  assert (Q24 : getr regs4 24 = w64 (Z.of_nat (length (gpre cx))))
    by (rewrite (QV 24%bv 24 eq_refl ltac:(unfold acallee_saved; lia)), F24, OLDb, OLDa, (EE 24%nat 24%bv eq_refl) by lia; exact R24).
  assert (PK14 : apres_kept B W1 m1 W3 mem4).
  { intros a Hiax Hox Hex Hpx. apply (HPK4 a Hiax Hox Hex). eapply apresent_grows; [exact HGf|].
    apply (HAK3 a Hiax Hox Hex). exact (PRESg a Hpx). }
  assert (PK24 : apres_kept B W2 mem3 W3 mem4).
  { intros a Hiax Hox Hex Hpx. apply (HPK4 a Hiax Hox Hex). eapply apresent_grows; [exact HGf | exact Hpx]. }
  pose proof HK4 as (K4h & K4b & K4i & K4f & _ & _).
  assert (HGE : GE_STK = 16544) by reflexivity.
  assert (KST4 : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros a Hax.
    rewrite (K4h a) by (clear - Hax SPR C1; unfold gsp1, RIG_FRAME, ASTACK, ESTACK in *; lia).
    rewrite KRf by (clear - Hax SPR C1; unfold gsp1, RIG_FRAME in *; lia).
    rewrite KGEh by (clear - Hax SPR C1 HGE; unfold gsp1, RIG_FRAME in *; lia).
    apply KEEPg; clear - Hax SPR C1; unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *; lia. }
  assert (LF2 : ly_F ly2 = ly_F ly1) by exact (rkc_lyF_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl).
  destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl) as (memS2 & HJi2 & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & Hfrs2 & _). cbn [app] in Hfrs2.
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
  assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
  assert (FNI : forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 -> ~ in_img SEGS a).
  { intros a Hax Hiax. pose proof (pa_segs_low a Hiax) as HLx. rewrite C5 in HLx.
    destruct Hax as [Hax | Hax]; [| rewrite SF in Hax; clear - Hax HLx HF8; lia].
    pose proof (rk_frm_off_imgB_x_xR ly1 S1 [] W1 m1 md1 1 fpos HAR1 Hfin) as Hoffx. rewrite HFa in Hoffx.
    change (fs_frame_bytes 1) with 128 in Hoffx. pose proof (pa_img_range a Hiax) as HRx. clear - Hax Hoffx HRx. lia. }
  assert (FNB : forall p nb a, In (p, nb) (ablocks B ly1 S1) -> p <= a < p + req_size nb ->
     ~ (F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16)).
  { intros p nb a Hinx Hpax Hax. pose proof (rk_frame_blk_apart_xR _ _ _ _ _ _ _ _ _ HAR1 Hfin Hinx) as Dx.
    change (fs_frame_bytes 1) with 128 in Dx. rewrite HFa in Dx.
    destruct (rk_alb_xR _ _ _ _ _ p nb HAR1 Hinx) as (_ & _ & _ & Happx & _).
    destruct Hax as [Hax | Hax]; [clear - Hax Hpax Dx; lia|]. rewrite SF in Hax.
    exact (fshadow_not_app F 16 p (req_size nb) a ltac:(clear - HF4096; lia) ltac:(clear - HFceil C1; lia) Happx Hax Hpax). }
  assert (HinO1 : cap2 <> 0 -> In (out2, cap2) (ablocks B ly1 S1))
    by (intros Hczx; apply (Permutation_in _ (Permutation_sym HPX)); apply in_or_app; left; exact (HinO2 Hczx)).
  assert (NFP : forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 ->
    ~ inFP (ablocks_fp (aout_blks cap2 out2)) a).
  { intros a Hax Hfx. apply inFP_ablocks_fp_inv in Hfx as (p & nb & Hpinx & Hpax).
    unfold aout_blks in Hpinx. destruct (Z.eqb_spec cap2 0) as [Hzx | Hnzx]; [destruct Hpinx|].
    destruct Hpinx as [Hpex | []]. injection Hpex as <- <-. exact (FNB _ _ a (HinO1 Hnzx) Hpax Hax). }
  assert (KFR4 : forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros a Hax.
    assert (Hax' : F <= a < F + 128 \/ 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 16) by (rewrite <- SF; exact Hax).
    assert (Ha64x : 0 <= a < 2 ^ 64) by (clear - Hax' HF4096 HFceil C1 HF8; lia).
    assert (Hrngx : forall ly, ly_F ly = ly_F ly1 ->
      in_zr a (frame_rng ly (1, fpos)) \/ in_zr a (shadow_addr (frame_addr ly 1 fpos), fs_frame_bytes 1 / 8)).
    { intros ly Hlyx. assert (EFx : frame_addr ly 1 fpos = F) by (unfold frame_addr in *; rewrite Hlyx; exact HFa).
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFx. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      clear - Hax. lia. }
    rewrite (K4f 1 fpos a Hfin2 (Hrngx ly2 LF2)) by (intros Hkx; exact (FNB _ _ a Hink Hkx Hax)).
    rewrite KRf by exact Ha64x.
    rewrite (rk_keep_frm_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a HJsl Hfin (Hrngx ly1 eq_refl) (NFP a Hax) Ha64x
      ltac:(intros Hgx; exact (FNI a Hax (proj1 (HGSL a Hgx))))).
    apply KEEPg; [exact Ha64x|]. clear - Hax' SPR C1 HFceil HF8. unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *. lia. }
  assert (KIM4 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W1) m1 a).
  { intros a Hiax Hox Hex Hpx Hgx. pose proof (pa_segs_low a Hiax) as HLx. rewrite C5 in HLx.
    assert (FPS : fp_spares (ablocks_fp (aout_blks cap2 out2)) a).
    { apply rk_fp_spares_xR. intros b Hbx. unfold aout_blks in Hbx. destruct (Z.eqb_spec cap2 0) as [Hzx | Hnzx]; [destruct Hbx|].
      destruct Hbx as [<- | []]. cbn [fst]. destruct (rk_alb_xR _ _ _ _ _ _ _ HAR1 (HinO1 Hnzx)) as (_ & Ho4x & _). clear - Ho4x. lia. }
    rewrite (K4i a Hiax Hox Hex). rewrite KRf by (clear - HLx; lia).
    rewrite (rk_keep_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJsl a Hiax Hox Hex Hpx FPS Hgx).
    apply KEEPg; [clear - HLx; lia|]. clear - HLx SPR C1. unfold gsp1, RIG_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, ESTACK in *. lia. }
  assert (KO2i4 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W2) mem3 a).
  { intros a Hiax Hox. pose proof (pa_segs_low a Hiax) as HLx. rewrite C5 in HLx.
    rewrite <- (KRf a) by (clear - HLx; lia).
    destruct (Z_le_gt_dec (as_errno B) a) as [E1x|E1x]; [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [E2x|E2x]|].
    - pose proof (HE4 (a - as_errno B) ltac:(clear - E1x E2x; lia)) as HExx. replace (as_errno B + (a - as_errno B)) with a in HExx by ring. exact HExx.
    - exact (K4i a Hiax Hox ltac:(clear - E2x; lia)).
    - exact (K4i a Hiax Hox ltac:(clear - E1x; lia)). }
  assert (KO2b4 : forall a, cap3' <> 0 -> out3 <= a < out3 + req_size cap3' ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W2) mem3 a).
  { intros a Hcx Hax.
    assert (HinOa : In (out3, cap3') (aout_blks cap3' out3))
      by (unfold aout_blks; destruct (Z.eqb_spec cap3' 0) as [E0|E0]; [exfalso; exact (Hcx E0) | left; reflexivity]).
    assert (HinO2' : In (out3, cap3') (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym HPq2)). apply in_or_app. right. apply in_or_app. left. exact HinOa. }
    assert (NKO : (out3, cap3') <> (key, Z.of_nat (length kt) + 1)).
    { intros Heqx. apply (rk_nodup_app_disj_xR XGa _ (key, Z.of_nat (length kt) + 1) HNDgX Hink1X). rewrite <- Heqx.
      apply in_or_app. left. exact HinOa. }
    destruct (rk_alb_xR _ _ _ _ _ _ _ HARge HinO2') as (_ & Ho4x & Hocx & _).
    replace a with (out3 + (a - out3)) by ring.
    rewrite (K4b out3 cap3' (a - out3) HinO2' ltac:(clear - Hax; lia)).
    2: { intros Hkx. destruct (rk_disj_xR ly2 S2 W2 mem3 md3 out3 cap3' key (Z.of_nat (length kt) + 1) HARge HinO2' Hink2 NKO) as [Dx|Dx];
         clear - Hkx Hax Dx; lia. }
    apply KRf. clear - Hax Ho4x Hocx C1. lia. }
  destruct r as [|r'].
  + pose proof (rk_seat3_xR true W3 ly3 S3 regs4 mem4 md4 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
    (Z.of_nat (length ks)) key klast A_rig_fr_ret HARfr Q2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp_xR; exact H32) ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    Q9 Q21 Q19 Q22 Q20 Q23 Q27 Q25 Q18 HinT4 ltac:(clear - HSA; lia) HTend ltac:(rewrite HSA; apply rk_mod_sa_xR; exact HT16)
    Hinh4 Hkh Hks26 ltac:(cbn; lia) ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; lia)
    ltac:(clear - HkL4096 HkLceil HrL1 C1; lia) HBLK Mhp4 Mnh4 Mkey4 ltac:(intros X; discriminate X)) as [HS3 SHOK3].
    cbn beta iota in HS3.
    remember (Eimg (Ereg regs4 (rk_extra3 hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (hp + 8 * (Z.of_nat (length ks) - 1)) klast))) as Ec eqn:HEc.
    assert (HEIc : img_env VAL A_LIM Ec) by (subst Ec; apply Eimg_env).
    assert (Ec32 : ew Ec 32 = Z_to_bv 64 hp) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    assert (Ec33 : ew Ec 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 1)).
    assert (Ec35 : ew Ec 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 3)).
    assert (Ec36 : ew Ec 36 = Z_to_bv 64 (hp + 8 * (Z.of_nat (length ks) - 1))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 4)).
    assert (Ec19 : ew Ec 19 = Z_to_bv 64 (8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl); exact Q19).
    assert (Ec20 : ew Ec 20 = Z_to_bv 64 (Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 20 20%bv eq_refl); exact Q20).
    assert (Ec23 : bv_unsigned (ew Ec 23) = gSA cx i + 48) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 23 23%bv eq_refl), Q23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
    assert (Ec33u : bv_unsigned (ew Ec 33) = hp + 8 * Z.of_nat n) by (rewrite Ec33; apply unsigned_lit_small; lia).
    assert (EEc : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew Ec k0 = getr regs4 r0)
      by (intros k0 r0 Hk0; subst Ec; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
    assert (Ec34 : ew Ec 34 = Z_to_bv 64 key) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 2)).
    assert (Ec37 : ew Ec 37 = Z_to_bv 64 klast) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 5)).
    clear HEc.
    assert (U32 : U Ec (SOff 32 0) = hp) by (apply U_atom; [exact Ec32 | lia]).
    assert (U33 : U Ec (SOff 33 0) = hp + 8 * Z.of_nat n) by (apply U_atom; [exact Ec33 | lia]).
    assert (U36 : U Ec (SOff 36 0) = hp + 8 * (Z.of_nat (length ks) - 1)) by (apply U_atom; [exact Ec36 | lia]).
    assert (U19 : U Ec (SOff 19 0) = 8 * Z.of_nat n) by (apply U_atom; [exact Ec19 | lia]).
    (* 0x82fb8 -> the signed-index check 0x83008 *)
    paj_run_tok_xR RUNG HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK1, mat into matK1, HF into HFK1, HFr into HFrK1, HG into HGK1.
    psrr_branch_tok RUNG BRR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU ?p ?o) ?c) (SLit 1))) _ = true |- _ =>
         rewrite (trap_ptr_sovf Ec (SAlu ALU_SLTU p o) c 0
           (trap_U_sltu_ge Ec o p hp _ U32 ltac:(first [exact U33 | exact U36]) ltac:(lia)) ltac:(rewrite U_SLit; reflexivity)) in Hb;
         discriminate Hb end. }
    (* -> the WRAP check `not a2,a1; bltu a2,s3` 0x8302c *)
    paj_run_tok_xR RUNG HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK2, mat into matK2, HF into HFK2, HFr into HFrK2, HG into HGK2.
    psrr_branch_tok RUNG BRR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_LTU (sv_denot _ (SAlu ALU_XOR (SOff 32 0) (SLit (-1)))) (sv_denot _ (SOff 19 0)) = true |- _ =>
         rewrite (trap_ptr_wrap_not Ec (SAlu ALU_XOR (SOff 32 0) (SLit (-1))) (SOff 19 0) hp (8 * Z.of_nat n)
           (trap_U_not Ec (SOff 32 0) hp U32) U19 ltac:(lia)) in Hb; discriminate Hb end. }
    (* -> the move, nheld - 1 stored, the loop test 0x83060 *)
    paj_run_tok_xR RUNG HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK3, mat into matK3, HF into HFK3, HFr into HFrK3, HG into HGK3.
    psrr_branch_tok RUNG BRR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_LT (sv_denot _ (SOff 20 0)) (sv_denot _ (SOff 35 (-1))) = true |- _ =>
         rewrite (rk_branch_lt_xR Ec (SOff 20 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hb;
         [| cbn [sv_denot]; rewrite Ec20, unsigned_lit_small by lia; f_equal; lia
          | cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by lia; f_equal; lia | lia | lia ]; apply Z.ltb_lt in Hb; lia end. }
    paj_run_to_tok_xR RUNTOG HS3 HJ4 SHOK3 rk_Bspan A_rig_step.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK4, mat into matK4, HF into HFK4, HFr into HFrK4, HG into HGK4.
    pmkst HS3.
    prreg HS3 (2%bv : bv 5) T2. prreg HS3 (3%bv : bv 5) T3. prreg HS3 (4%bv : bv 5) T4.
    prreg HS3 (8%bv : bv 5) T8. prreg HS3 (9%bv : bv 5) T9. prreg HS3 (21%bv : bv 5) T21.
    (* the move's two stores, the rest kept *)
    assert (BV23 : base_val Ec (Some 23%nat) = gSA cx i + 48) by (cbn [base_val]; exact Ec23).
    assert (BV33 : base_val Ec (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; exact Ec33u).
    assert (WIN : forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) ->
      aview SEGS (w_H W3) (ms_mem msK4) a = aview SEGS (w_H W3) mem4 a).
    { intros a Ha N1 N2.
      assert (N1' : ~ (gSA cx i + 48 <= a < gSA cx i + 48 + 4)) by (clear - N1; lia).
      rewrite (rkc_win_xR Ec _ (w_H W3) (ms_mem msK3) (ms_mem msK4) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK4 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win_xR Ec _ (w_H W3) (ms_mem msK2) (ms_mem msK3) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK3 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win_xR Ec _ (w_H W3) (ms_mem msK1) (ms_mem msK2) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK2 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2).
      exact (rkc_win_xR Ec _ (w_H W3) mem4 (ms_mem msK1) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK1 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2). }
    assert (PRES5 : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem msK4) a).
    { intros a Hp. eapply apresent_grows; [exact HGK4|]. eapply apresent_grows; [exact HGK3|].
      eapply apresent_grows; [exact HGK2|]. eapply apresent_grows; [exact HGK1|]. exact Hp. }
    pose proof (st_ok_pi_region_nth Ec _ _ 1 _ HS3 eq_refl) as RN1.
    pose proof (st_ok_pi_region_nth Ec _ _ 2 _ HS3 eq_refl) as RN2.
    cbn [ms_mem restrict mkst] in RN1, RN2.
    assert (VNH5 : val_mem SEGS (arm W3 (ms_mem msK4)) (gSA cx i + 48) 4 (Z.of_nat (length ks'))).
    { pose proof (field_of_region Ec _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) RN1 Ec23
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by (clear - Hks26; lia); f_equal; ring)
        ltac:(cbn; clear - Hks26 Hn; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. unfold ks'. rewrite relay_instance_gone_b_lem.rigl_len_swap, Nat2Z.inj_sub by (clear - Hn; lia). exact V. }
    assert (VHN5 : val_mem SEGS (arm W3 (ms_mem msK4)) (hp + 8 * Z.of_nat n) 8 klast).
    { pose proof (field_of_region Ec _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 34 0) key RN2 Ec33u
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - Hk4096 Hkceil Hrq1 C1; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. replace klast with key by (unfold klast, key; f_equal; f_equal; clear - Hks; lia). exact V. }
    unfold hp in VHN5.
    assert (HPq3' : Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3' out3 ++ gxrest cx)) by exact HPq3.
    destruct (rkc_end2_xR cx i n _ F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed _ c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 ly2 S2 W2 mem3 ly3 S3 W3 mem4 (ms_mem msK4) _ _ out3 HB HJ0 HPK HFR HLK HLS M80 HGN HJ4 HPq3' HO3
      PK14 PK24 KST4 KFR4 KIM4 KALL KO2i4 KO2b4 WIN PRES5 VNH5 VHN5) as (GL5 & LS5 & M805 & AR5 & AO5 & SR5 & SR15 & DR5 & GS5 & PR5 & PS5).
    assert (HPG : Permutation (ablocks B ly3 S3)
      ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
       gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
       rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap3' out3 ++ gxrest cx))
      by (unfold XGb in HPq3; rewrite <- app_comm_cons, <- !app_assoc in HPq3; exact HPq3).
    assert (HLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HM4).
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { pose proof (rkb_ge_cap_le_xR c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as GC1.
      pose proof (rkb_bb_free_xR ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL1 EL2) as B1.
      pose proof (rkb_bb_out_xR ly1 S1 ly2 S2 cap2 out2 cap3' out3 restG HPa HPb ltac:(fold cap3' in GC1; clear - GC1 Hcap2; lia)) as B2.
      pose proof (rkb_ge_net_xR c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl) as GN.
      fold cap3' in GC1, GN. clear - GC1 GN B1 B2 Hxl. lia. }
    pose proof (rkb_gout_end_xR cx i n F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 ly3 S3 W3 (ms_mem msK4) out3 HB HGN HPT Hcap2 Hxl AR5 AO5 SR5 SR15 DR5 GS5 HPG HLE HBB HRMf HCN3) as HGO5.
    apply (KR W3 _).
    exists (ms_regs msK4), ly3, S3, (ms_mem msK4). eexists. eexists.
    exists F, FL, (qd ++ [(entry_keys e1 ks', h1)]), (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), cap3', out3,
      (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (EEc 2%nat 2%bv eq_refl); exact Q2|].
      split; [rewrite T3, (EEc 3%nat 3%bv eq_refl); exact Q3|].
      split; [rewrite T4, (EEc 4%nat 4%bv eq_refl); exact Q4|].
      split; [rewrite T8, (EEc 8%nat 8%bv eq_refl); exact Q8|].
      split; [rewrite T9, (EEc 9%nat 9%bv eq_refl); exact Q9|].
      rewrite T21, (EEc 21%nat 21%bv eq_refl); exact Q21. }
    split; [exact M805|]. split; [exact Hi|]. split; [exact GL5|]. split; [exact LS5|].
    exact HGO5.
  + pose proof (rk_seat3_xR false W3 ly3 S3 regs4 mem4 md4 (gsp1 cx) (gSA cx i) (gxG0 cx) hp (re_kh e1) (Z.of_nat n)
    (Z.of_nat (length ks)) key klast A_rig_fr_ret HARfr Q2 ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    ltac:(unfold gsp1, RIG_FRAME; apply rk_mod_sp_xR; exact H32) ltac:(clear - SPR C1; unfold gsp1, RIG_FRAME; lia)
    Q9 Q21 Q19 Q22 Q20 Q23 Q27 Q25 Q18 HinT4 ltac:(clear - HSA; lia) HTend ltac:(rewrite HSA; apply rk_mod_sa_xR; exact HT16)
    Hinh4 Hkh Hks26 ltac:(cbn; lia) ltac:(lia) ltac:(clear - Hk4096 Hkceil Hrq1 C1; lia)
    ltac:(clear - HkL4096 HkLceil HrL1 C1; lia) HBLK Mhp4 Mnh4 Mkey4 ltac:(intros _; exact MkL4)) as [HS3 SHOK3].
    cbn beta iota in HS3.
    remember (Eimg (Ereg regs4 (rk_extra3 hp (hp + 8 * Z.of_nat n) key (Z.of_nat (length ks)) (hp + 8 * (Z.of_nat (length ks) - 1)) klast))) as Ec eqn:HEc.
    assert (HEIc : img_env VAL A_LIM Ec) by (subst Ec; apply Eimg_env).
    assert (Ec32 : ew Ec 32 = Z_to_bv 64 hp) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
    assert (Ec33 : ew Ec 33 = Z_to_bv 64 (hp + 8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 1)).
    assert (Ec35 : ew Ec 35 = Z_to_bv 64 (Z.of_nat (length ks))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 3)).
    assert (Ec36 : ew Ec 36 = Z_to_bv 64 (hp + 8 * (Z.of_nat (length ks) - 1))) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 4)).
    assert (Ec19 : ew Ec 19 = Z_to_bv 64 (8 * Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 19 19%bv eq_refl); exact Q19).
    assert (Ec20 : ew Ec 20 = Z_to_bv 64 (Z.of_nat n)) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 20 20%bv eq_refl); exact Q20).
    assert (Ec23 : bv_unsigned (ew Ec 23) = gSA cx i + 48) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs4 _ 23 23%bv eq_refl), Q23; apply unsigned_lit_small; unfold AENT, ATABLE in *; lia).
    assert (Ec33u : bv_unsigned (ew Ec 33) = hp + 8 * Z.of_nat n) by (rewrite Ec33; apply unsigned_lit_small; lia).
    assert (EEc : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew Ec k0 = getr regs4 r0)
      by (intros k0 r0 Hk0; subst Ec; pose proof (bv_unsigned_in_range 5 r0) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk0).
    assert (Ec34 : ew Ec 34 = Z_to_bv 64 key) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 2)).
    assert (Ec37 : ew Ec 37 = Z_to_bv 64 klast) by (subst Ec; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 5)).
    clear HEc.
    assert (U32 : U Ec (SOff 32 0) = hp) by (apply U_atom; [exact Ec32 | lia]).
    assert (U33 : U Ec (SOff 33 0) = hp + 8 * Z.of_nat n) by (apply U_atom; [exact Ec33 | lia]).
    assert (U36 : U Ec (SOff 36 0) = hp + 8 * (Z.of_nat (length ks) - 1)) by (apply U_atom; [exact Ec36 | lia]).
    assert (U19 : U Ec (SOff 19 0) = 8 * Z.of_nat n) by (apply U_atom; [exact Ec19 | lia]).
    (* 0x82fb8 -> the signed-index check 0x83008 *)
    paj_run_tok_xR RUNG HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK1, mat into matK1, HF into HFK1, HFr into HFrK1, HG into HGK1.
    psrr_branch_tok RUNG BRR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU ?p ?o) ?c) (SLit 1))) _ = true |- _ =>
         rewrite (trap_ptr_sovf Ec (SAlu ALU_SLTU p o) c 0
           (trap_U_sltu_ge Ec o p hp _ U32 ltac:(first [exact U33 | exact U36]) ltac:(lia)) ltac:(rewrite U_SLit; reflexivity)) in Hb;
         discriminate Hb end. }
    (* -> the WRAP check `not a2,a1; bltu a2,s3` 0x8302c *)
    paj_run_tok_xR RUNG HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK2, mat into matK2, HF into HFK2, HFr into HFrK2, HG into HGK2.
    psrr_branch_tok RUNG BRR HS3 SHOK3 rk_Bspan.
    1: { exfalso. lazymatch goal with Hb : branch_taken BC_LTU (sv_denot _ (SAlu ALU_XOR (SOff 32 0) (SLit (-1)))) (sv_denot _ (SOff 19 0)) = true |- _ =>
         rewrite (trap_ptr_wrap_not Ec (SAlu ALU_XOR (SOff 32 0) (SLit (-1))) (SOff 19 0) hp (8 * Z.of_nat n)
           (trap_U_not Ec (SOff 32 0) hp U32) U19 ltac:(lia)) in Hb; discriminate Hb end. }
    (* -> the move, nheld - 1 stored, the loop test 0x83060 *)
    paj_run_tok_xR RUNG HS3 HJ4 SHOK3 rk_Bspan.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK3, mat into matK3, HF into HFK3, HFr into HFrK3, HG into HGK3.
    psrr_branch_tok RUNG BRR HS3 SHOK3 rk_Bspan.
    2: { exfalso. lazymatch goal with Hb : branch_taken BC_LT (sv_denot _ (SOff 20 0)) (sv_denot _ (SOff 35 (-1))) = false |- _ =>
         rewrite (rk_branch_lt_xR Ec (SOff 20 0) (SOff 35 (-1)) (Z.of_nat n) (Z.of_nat (length ks) - 1)) in Hb;
         [| cbn [sv_denot]; rewrite Ec20, unsigned_lit_small by lia; f_equal; lia
          | cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by lia; f_equal; lia | lia | lia ]; apply Z.ltb_ge in Hb; lia end. }
    paj_run_to_tok_xR RUNTOG HS3 HJ4 SHOK3 rk_Bspan A_rig_inner.
    { intros a (rg & Hin & Hr). cbn [ss_mem ss_k3b ss_k3a rk3b_regions rk3a_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
         first [ exfalso; clear - Hr; lia | left; split; [apply AWT3; clear - Hr Ec23; lia | clear - Hr; lia] | left; split; [apply AWH3; clear - Hr Ec33u; lia | clear - Hr; lia] ] | ]); try destruct Hin. }
    rename ms into msK4, mat into matK4, HF into HFK4, HFr into HFrK4, HG into HGK4.
    pmkst HS3.
    prreg HS3 (2%bv : bv 5) T2. prreg HS3 (3%bv : bv 5) T3. prreg HS3 (4%bv : bv 5) T4.
    prreg HS3 (8%bv : bv 5) T8. prreg HS3 (9%bv : bv 5) T9. prreg HS3 (21%bv : bv 5) T21.
    (* the move's two stores, the rest kept *)
    assert (BV23 : base_val Ec (Some 23%nat) = gSA cx i + 48) by (cbn [base_val]; exact Ec23).
    assert (BV33 : base_val Ec (Some 33%nat) = hp + 8 * Z.of_nat n) by (cbn [base_val]; exact Ec33u).
    assert (WIN : forall a, 0 <= a < 2 ^ 64 -> ~ (gSA cx i + 48 <= a < gSA cx i + 52) ->
      ~ (hp + 8 * Z.of_nat n <= a < hp + 8 * Z.of_nat n + 8) ->
      aview SEGS (w_H W3) (ms_mem msK4) a = aview SEGS (w_H W3) mem4 a).
    { intros a Ha N1 N2.
      assert (N1' : ~ (gSA cx i + 48 <= a < gSA cx i + 48 + 4)) by (clear - N1; lia).
      rewrite (rkc_win_xR Ec _ (w_H W3) (ms_mem msK3) (ms_mem msK4) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK4 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win_xR Ec _ (w_H W3) (ms_mem msK2) (ms_mem msK3) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK3 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2).
      rewrite (rkc_win_xR Ec _ (w_H W3) (ms_mem msK1) (ms_mem msK2) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK2 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2).
      exact (rkc_win_xR Ec _ (w_H W3) mem4 (ms_mem msK1) (gSA cx i + 48) (hp + 8 * Z.of_nat n) HFrK1 ltac:(rkc_rs_xR) BV23 BV33 a Ha N1' N2). }
    assert (PRES5 : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem msK4) a).
    { intros a Hp. eapply apresent_grows; [exact HGK4|]. eapply apresent_grows; [exact HGK3|].
      eapply apresent_grows; [exact HGK2|]. eapply apresent_grows; [exact HGK1|]. exact Hp. }
    pose proof (st_ok_pi_region_nth Ec _ _ 1 _ HS3 eq_refl) as RN1.
    pose proof (st_ok_pi_region_nth Ec _ _ 2 _ HS3 eq_refl) as RN2.
    cbn [ms_mem restrict mkst] in RN1, RN2.
    assert (VNH5 : val_mem SEGS (arm W3 (ms_mem msK4)) (gSA cx i + 48) 4 (Z.of_nat (length ks'))).
    { pose proof (field_of_region Ec _ 23 (gSA cx i + 48) _ 0 4 0 4 0 4%N (SOff 35 (-1)) (Z.of_nat (length ks) - 1) RN1 Ec23
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec35, unsigned_lit_small by (clear - Hks26; lia); f_equal; ring)
        ltac:(cbn; clear - Hks26 Hn; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. unfold ks'. rewrite relay_instance_gone_b_lem.rigl_len_swap, Nat2Z.inj_sub by (clear - Hn; lia). exact V. }
    assert (VHN5 : val_mem SEGS (arm W3 (ms_mem msK4)) (hp + 8 * Z.of_nat n) 8 klast).
    { pose proof (field_of_region Ec _ 33 (hp + 8 * Z.of_nat n) _ 0 8 0 8 0 8%N (SOff 37 0) klast RN2 Ec33u
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Ec37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - HkL4096 HkLceil HrL1 C1; lia) ltac:(cbn; apply Z.leb_le; reflexivity)) as V.
      rewrite Z.add_0_r in V. exact V. }
    unfold hp in VHN5.
    assert (HPq3' : Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3' out3 ++ gxrest cx)) by exact HPq3.
    destruct (rkc_end2_xR cx i n _ F FL fpos qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed _ c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 md1 k1 ly2 S2 W2 mem3 ly3 S3 W3 mem4 (ms_mem msK4) _ _ out3 HB HJ0 HPK HFR HLK HLS M80 HGN HJ4 HPq3' HO3
      PK14 PK24 KST4 KFR4 KIM4 KALL KO2i4 KO2b4 WIN PRES5 VNH5 VHN5) as (GL5 & LS5 & M805 & AR5 & AO5 & SR5 & SR15 & DR5 & GS5 & PR5 & PS5).
    assert (HPG : Permutation (ablocks B ly3 S3)
      ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
       gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
       rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap3' out3 ++ gxrest cx))
      by (unfold XGb in HPq3; rewrite <- app_comm_cons, <- !app_assoc in HPq3; exact HPq3).
    assert (HLE : mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT))
      by exact (mo_le_trans MT MLAW _ _ _ _ _ HM3 HM4).
    assert (HBB : blocks_bytes S3 <= blocks_bytes S1 +
      tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) 0 ga0) -
      (Z.of_nat (length kt) + 1)).
    { pose proof (rkb_ge_cap_le_xR c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hcap2) as GC1.
      pose proof (rkb_bb_free_xR ly2 S2 ly3 S3 l1 l2 key (Z.of_nat (length kt) + 1) EL1 EL2) as B1.
      pose proof (rkb_bb_out_xR ly1 S1 ly2 S2 cap2 out2 cap3' out3 restG HPa HPb ltac:(fold cap3' in GC1; clear - GC1 Hcap2; lia)) as B2.
      pose proof (rkb_ge_net_xR c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) Hxl) as GN.
      fold cap3' in GC1, GN. clear - GC1 GN B1 B2 Hxl. lia. }
    prreg HS3 (19%bv : bv 5) T19. prreg HS3 (20%bv : bv 5) T20. prreg HS3 (23%bv : bv 5) T23. prreg HS3 (24%bv : bv 5) T24.
    prreg HS3 (25%bv : bv 5) T25. prreg_raw_xR HS3 (22%bv : bv 5) T22. prreg_raw_xR HS3 (27%bv : bv 5) T27. prreg_raw_xR HS3 (18%bv : bv 5) T18.
    destruct (rkb_gin_end_xR cx i n r' F qd cB OB capB e1 h1 ev LB c1' O1 cap1 ks Ed (S f0) c2 O2 cap2 out2 spent
      ly1 S1 W1 m1 ly3 S3 W3 (ms_mem msK4) out3 HB HGN HPT Hcap2 Hxl AR5 AO5 SR5 SR15 DR5 GS5 HPG PR5 PS5 HLE HBB HRMf HCN3)
      as (f5 & HGN5).
    apply (KE r' W3 _ eq_refl).
    exists (ms_regs msK4), ly3, S3, (ms_mem msK4). eexists. eexists.
    exists F, FL, qd, cB, OB, capB, e1, h1, ev, LB, c1', O1, cap1, ks', (Ed ++ [nth n ks (0, [], [])]), f5,
      (ge_ctl c2 (Z.of_nat (length kt))), (ge_O c2 O2 kt), cap3', out3,
      (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length kt)) + mo_free MT)).
    split; [reflexivity|].
    split.
    { split; [unfold spZ; rewrite T2, (EEc 2%nat 2%bv eq_refl); exact Q2|].
      split; [rewrite T3, (EEc 3%nat 3%bv eq_refl); exact Q3|].
      split; [rewrite T4, (EEc 4%nat 4%bv eq_refl); exact Q4|].
      split; [rewrite T8, (EEc 8%nat 8%bv eq_refl); exact Q8|].
      split; [rewrite T9, (EEc 9%nat 9%bv eq_refl); exact Q9|].
      rewrite T21, (EEc 21%nat 21%bv eq_refl); exact Q21. }
    split; [rewrite T19, (EEc 19%nat 19%bv eq_refl); exact Q19|].
    split; [rewrite T22; cbn [sv_denot]; rewrite (EEc 19%nat 19%bv eq_refl), Q19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite T20, (EEc 20%nat 20%bv eq_refl); exact Q20|].
    split; [rewrite T23, (EEc 23%nat 23%bv eq_refl); exact Q23|].
    split.
    { rewrite T27. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 21 0)) with (rk_sh 23).
      apply rk_sh_den_xR; [rewrite (EEc 23%nat 23%bv eq_refl); exact Q23 | rewrite (EEc 21%nat 21%bv eq_refl); exact Q21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split; [rewrite T24, (EEc 24%nat 24%bv eq_refl); exact Q24|].
    split; [rewrite T25, (EEc 25%nat 25%bv eq_refl); exact Q25|].
    split.
    { rewrite T18. change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 21 0)) with (rk_sh 25).
      apply rk_sh_den_xR; [rewrite (EEc 25%nat 25%bv eq_refl); exact Q25 | rewrite (EEc 21%nat 21%bv eq_refl); exact Q21 |].
      clear - HTend HSA HT4096 HTceil C1. unfold AENT, ATABLE in *. lia. }
    split; [exact M805|]. split; [exact GL5|]. split; [exact LS5|].
    exact HGN5.
Qed.
End wR.

End c.
End b.
End a.
