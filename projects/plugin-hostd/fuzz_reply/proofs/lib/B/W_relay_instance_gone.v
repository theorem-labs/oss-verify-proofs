(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASSEMBLY of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan 0x82ca0): pb_relay_instance_gone_x : rig_spec_x, from the segment statements of
   lib/B/W_relay_instance_gone_cx.v composed by W_rig_all.v rig_all.  Applied: W_rig_pro.v rig_pro, W_rig_top.v
   rig_top_proof, W_rig_tail.v rig_tail, W_rig_step.v rig_step_proof / rig_outer_proof / rig_keys_proof.  No segment is open (KEY: W_rig_key.v rig_key_proof).  The Section block is
   regenerated from the cx file whenever the cx file changes.
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the image-A twin is the RIG_x round, commit f4cd818e98d):
   Section c is the cx file's generic Section (its hypothesis list, verbatim): pb_relay_instance_gone_x proves
   W_contract_x.v rig_spec_x over any allocator relation ARx with its laws, the program statics PST and the room record
   RP.  The AR statement pb_relay_instance_gone is dropped (a Theorem Labs lane's ruling 10:34Z: nothing on image B uses it; the
   B top's arms take rig_spec as a hypothesis), so there is no AR re-derivation (image A's Section cAR).  Beside the
   cx file's list, Section c takes W_rig_top_calls.v's HLITGOT (the window's 4d3f3ddb1df, verbatim), which
   W_rig_top.v rig_top_proof needs for the narrowed snprintf contract. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_all.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_rig_pro W_rig_tail W_rig_step W_rig_top W_rig_key.
(* route R: a Theorem Labs lane's B rig_spec_xR, the B dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* ---- THE GENERIC WALK: the cx file's Section c, verbatim (W_relay_instance_gone_cx.v says what each is). ---- *)
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
(* W_rig_top_calls.v's HLITGOT, verbatim: the two literals below the GOT word, the location premises M1 / M3 of the
   narrowed asnprintf_realizes_x (W_sites_x.v), for W_rig_top.v rig_top_proof.  PB_fr decides it by vm_compute:
   SnpNarrowSites.v HLITGOT_PB_fr. *)
Hypothesis HLITGOT : VAL (A_OBJ 17) + 7 <= FR_GOT_GUARD /\ VAL (A_OBJ 18) + 22 <= FR_GOT_GUARD.
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



Theorem pb_relay_instance_gone_x : rig_spec_x B PST ARx MT RP MMAX RG CTX_AFREE A_rig_entryP.
Proof.
apply (rig_all B PST ARx MT RP MMAX RG CTX_AFREE).
- eapply W_rig_pro.rig_pro; eassumption.
- eapply W_rig_top.rig_top_proof; eassumption.
- eapply W_rig_key.rig_key_proof; eassumption.
- eapply W_rig_step.rig_step_proof; eassumption.
- eapply W_rig_step.rig_keys_proof; eassumption.
- eapply W_rig_step.rig_outer_proof; eassumption.
- eapply W_rig_tail.rig_tail; eassumption.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): pb_relay_instance_gone_x at a world relation R, concluding a Theorem Labs lane's B
   rig_spec_xR (W_contract_xR_relayB.v, 1d0938e98da9) exactly.  The Section's hypotheses are W_relay_instance_gone_cx.v
   Section wR's (the R laws, RO / RO_ARx, AFREE_R, DRAIN_R, GE_R), which the segment walks at R take.  The
   seven segment walks at R, each applied over this Section's hypotheses as pb_relay_instance_gone_x applies the strict
   walks: PRO W_rig_pro.v rig_pro_xR, STEP / KEYS / OUTER W_rig_step.v rig_step_proof_xR / rig_keys_proof_xR /
   rig_outer_proof_xR, TAIL W_rig_tail.v rig_tail_xR (a Theorem Labs lane, 732f33167525), KEY W_rig_key.v rig_key_proof_xR and
   TOP W_rig_top.v rig_top_proof_xR (S3BRigKey, e7a1e1ceb3d: KEY's files state their Proof using, so neither takes a
   strict allocator rule).  No segment premise is left.  The composition is W_rig_all.v rig_all_xR.  Image A's twin:
   lib/A/W_relay_instance_gone.v Section wR. ---- *)
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
Theorem pb_relay_instance_gone_xR : rig_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE A_rig_entryP.
Proof.
apply (rig_all_xR B PST ARx MT RP MMAX RG CTX_AFREE R).
- eapply W_rig_pro.rig_pro_xR; eassumption.
- eapply W_rig_top.rig_top_proof_xR; eassumption.
- eapply W_rig_key.rig_key_proof_xR with (RO := RO); eassumption.
- eapply W_rig_step.rig_step_proof_xR; eassumption.
- eapply W_rig_step.rig_keys_proof_xR; eassumption.
- eapply W_rig_step.rig_outer_proof_xR; eassumption.
- eapply W_rig_tail.rig_tail_xR; eassumption.
Qed.
End wR.
End c.
End b.
End a.
