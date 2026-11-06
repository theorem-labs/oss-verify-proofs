(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan 0x82e1c .. 0x82f08 / 0x830c4), lemma track L: the two memory-frame statements of
   lib/B/W_rig_top_defs.v.  The Section header is W_rig_top_defs.v's, verbatim.  Proof port of k3's image-A track
   (a working branch 80fffa8e840, lib/A/W_rig_top_live.v) to image B's frame.
     live_kept   GLIVE and the loop's frame slots survive a stretch that writes only the bytes P names (the scratch
                 below sp, 80(sp), F + 32 .. F + 80 and F's shadow): ROM bytes, g_lock's 12 bytes, F's flag cell, the
                 frame slots (B: 8, 16, 112 = F, 72 = the id; g_lslots 24 .. 64 and 88) and the saved registers
                 (120(sp) .. 216(sp)) are none of them.
     live_drain  the same across drain's call at 0x82e68: drain's journal keeps every byte above alloc_ceiling
                 outside its window [sp - DRAIN_STK_x, sp), the bytes of F (a frame of S1, apart from every block, so
                 outside drain's footprint dr_fp, which holds block bytes only) and g_lock (an image byte outside
                 G_DR, by HRGP, and off the program statics, PSTG).
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v, commit f4cd818e98d): over ARx
   at W_relay_instance_gone_cx.v's generic Section; the journals are ajournal_gx_x at the kit's RIG_STK_x /
   DRAIN_STK_x, GLIVE carries the cut's head set.
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_top_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
   walk's (AR-free, verbatim) or its _x twin (image A's W_relay_instance_gone_cx.v, the same list). ---- *)
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
(* the two literals of the snprintf call and " end\0" (.str.4, A_lit_end5 = A_OBJ 28), in the cx's glit_at_x form
   over ARx (W_relay_instance_gone_cx.v: bytes, in_rom, ashp_x, the granule's tail) *)
Hypothesis HLIT17 : glit_at_x ARx 17 (RIG_FMT ++ [0]).
Hypothesis HLIT18 : glit_at_x ARx 18 (RelayModel.K_GESTURE ++ [0]).
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

(* ---- The geometry both statements use. ---- *)
(* image bytes lie below the low shadow (kLowMemEnd = SHADOW_OFF) *)
Lemma tl2_img_low : forall a, in_img SEGS a -> 0 <= a < SHADOW_OFF.
Proof.
intros a Hi. pose proof (pa_segs_low a Hi) as H. pose proof asan_consts as (_ & _ & _ & _ & C5).
rewrite C5 in H. unfold SHADOW_OFF. lia.
Qed.
(* the entry sp: GBASE's afn_pre_x window, RIG_STK_x = 17232 bytes above alloc_ceiling (image B's kit: RIG_STK + 128) *)
Lemma tl2_sp : forall cx, GBASE B ARx MT RP MMAX RG cx -> alloc_ceiling + 17232 <= gsp0 cx <= 2 ^ 47.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : RIG_STK_x = 17232) by reflexivity. rewrite WS in Hslo. unfold gsp0. lia.
Qed.
(* the run's own frame (1, fpos): a frame of S1 (the journal's own), below alloc_ceiling, application memory and
   not image bytes *)
Lemma tl2_frm : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
ARx ly1 S1 Hp1 W1 m1 md1 /\ In (1, fpos) (frames S1) /\
4096 <= frame_addr ly1 1 fpos /\ frame_addr ly1 1 fpos + 128 <= alloc_ceiling /\ in_app (frame_addr ly1 1 fpos) 128 /\
(forall a, frame_addr ly1 1 fpos <= a < frame_addr ly1 1 fpos + 128 -> ~ in_img SEGS a).
Proof.
intros cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ.
pose proof (tj_AR B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (H1 & H2 & H3).
change (fs_frame_bytes 1) with 128 in H2, H3.
split; [exact HAR|]. split; [exact Hfin|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left.
exists 1, fpos. split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. exact Ha.
Qed.

(* ---- L1. ---- *)
Lemma live_kept : stmt_live_kept B PST ARx MT RP MMAX RG.
Proof.
unfold stmt_live_kept.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 P HB HJ1 HROM1 HPK HFR HLK HLS HJ2 HPw HK HPR.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
destruct (tl2_frm cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (SF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. unfold SHADOW_OFF in SF.
assert (HF8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
(* the bytes P names (B: the scratch below sp, 80(sp), F + 32 .. F + 80, F's shadow) are none of: image bytes, F's
   flag cell F + 120 .., the frame slots 8(sp) .. 80(sp) and 88(sp) .. 224(sp) (B's g_frame slots 8, 16, 72, 112,
   its g_lslots 24 .. 64 and 88, and the saved registers 120 .. 224) *)
assert (NPI : forall a, in_img SEGS a -> ~ P a).
{ intros a Hi Hp. pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  destruct (HPw a Hp) as [H|[H|[H|H]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | |].
  - exact (HFni a ltac:(lia) Hi).
  - rewrite SF in H. lia. }
assert (NPF : forall a, F + 120 <= a < F + 128 -> ~ P a).
{ intros a Ha Hp. destruct (HPw a Hp) as [H|[H|[H|H]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia |].
  rewrite SF in H. exact (fshadow_not_app F 16 F 128 a HF4 ltac:(lia) HFapp H ltac:(lia)). }
assert (NPS : forall a, gsp1 cx + 8 <= a < gsp1 cx + 80 \/ gsp1 cx + 88 <= a < gsp1 cx + 224 -> ~ P a).
{ intros a Ha Hp. unfold gsp1, RIG_FRAME in Ha.
  destruct (HPw a Hp) as [H|[H|[H|H]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia |].
  rewrite SF in H. lia. }
assert (VK : forall a n v, (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ P (a + k)) ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v Hn Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m2 a n v); [|exact Hv].
  intros k Hk. destruct (Hn k Hk) as (Hr & Hnp). exact (HK (a + k) Hr Hnp). }
split.
- exists fpos, Hp2. split; [exact HJ2|].
  split.
  { intros a Ha.
    assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
    rewrite (HK a ltac:(lia) (NPI a Hi)). exact (HROM1 a Ha). }
  split.
  { intros a Hi Ho He Hp. exact (HPR a (HPK a Hi Ho He Hp)). }
  split.
  { split; [exact HFa|]. split; [exact HFl|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [lia | apply NPF; lia] | exact HFL120]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS8]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS16]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS112]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS72]|].
    intros i Hi. apply VK; [|exact (HSV i Hi)].
    intros k Hk. cbn in Hk. split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia]. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  assert (Hi : in_img SEGS a) by exact (proj1 (RGIMG a ltac:(unfold rg_rng; left; exact Ha))).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split; [exact (HK a ltac:(lia) (NPI a Hi))|].
  unfold arm. apply writable_kept. exact (HPR a).
- pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
  split; [|split; [|split; [|split; [|split; [|split]]]]];
  (apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | assumption]).
Qed.

(* ---- L2. ---- *)
Lemma live_drain : stmt_live_drain B PST ARx MT RP MMAX RG.
Proof.
unfold stmt_live_drain.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3
  HB HJ1 HROM1 HPK HFR HLK HLS HJD HFPB HPK2 HJ2.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & RGWR & _).
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
destruct (tl2_frm cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HGD : gx_ok SEGS B (G_DR B RG)) by exact (gx_ok_sub SEGS B _ _ (rig_G_DR_RIG B RG) HGRIG).
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD) as (memS & HJDi & HagD).
pose proof HJDi as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRM & _).
(* drain's footprint holds only block bytes: no byte of F, and not 0 (the sink stays closed) *)
assert (NFP : forall a, F <= a < F + 128 -> ~ inFP (dr_fp SA e h cap out) a).
{ intros a Ha Hf. destruct (HFPB a Hf) as (b & n & Hin & Hr).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ b n 1 fpos HAR1 Hin Hfin) as Hd.
  rewrite HFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (SPR : forall a, fp_spares (dr_fp SA e h cap out) a).
{ intros a Ho. exfalso. destruct (HFPB 0 Ho) as (b & n & Hin & Hr).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ b n HAR1 Hin) as (_ & H4096 & _). lia. }
(* what drain keeps: the caller's frame slots (above its window), the bytes of F, g_lock *)
assert (KHI : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. unfold gsp1, RIG_FRAME in Ha.
  apply (ajgx_keep_high_x B PST ARx (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGD HJD a); unfold gsp1, RIG_FRAME; lia. }
assert (KFR : forall a, F <= a < F + 128 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha.
  assert (Hrng : in_zr a (frame_rng ly1 (1, fpos)) \/
    in_zr a (shadow_addr (frame_addr ly1 1 fpos), fs_frame_bytes 1 / 8)).
  { left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes 1) with 128. lia. }
  rewrite (FRM 1 fpos a Hfin Hrng (NFP a Ha)).
  apply HagD. rewrite unsigned_lit_small by lia. intros HG. exact (HFni a Ha (proj1 (HGD a HG))). }
assert (KLK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Ho & He).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split.
  - apply (ajgx_keep_img_x B PST ARx (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD a Hi Ho He
      (PSTG a ltac:(left; unfold inG, G_RIG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia)) (SPR a)).
    pose proof HRGP as (HL & _). cbn [zall_disjoint] in HL. unfold zdisj in HL. cbn [fst snd] in HL.
    destruct HL as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _).
    unfold inG, G_DR, G_SL. intros HG. rewrite !Exists_cons, Exists_nil in HG. unfold in_zr in HG. cbn [fst snd] in HG.
    (* G_DR: g_s, then G_SL's g_client_broken, g_send_eintr, g_nout, g_capout, g_out, errno *)
    destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[HG|[]]]]]]]];
    [ clear - D1 Ha HG | clear - D10 Ha HG | clear - D12 Ha HG | clear - D6 Ha HG | clear - D7 Ha HG
    | clear - D8 Ha HG | clear - D14 Ha HG ]; lia.
  - intros _. unfold arm. apply (RGWR (w_H W2) m2 a); [left; exact Ha|].
    apply (hidden_not_img SEGS W2 (Z_to_bv 64 a)). rewrite unsigned_lit_small by lia. exact Hi. }
assert (LF : ly_F ly2 = ly_F ly1) by (destruct Hly as (_ & _ & _ & _ & _ & LF & _); exact LF).
assert (VKH : forall a n v, gsp1 cx <= a -> a + Z.of_nat n <= gsp0 cx ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v).
{ intros a n v H1 H2 Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 a n v); [|exact Hv].
  intros k Hk. apply KHI. lia. }
split.
- exists fpos, Hp3. split; [exact HJ2|].
  split.
  { apply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD);
      [| exact PSTR | exact HROM1].
    intros a Ha. destruct (HROMO a Ha) as (HnG & Hrest). split; [|exact Hrest].
    intros HG. exact (HnG (rig_G_DR_RIG B RG a HG)). }
  split; [exact (apk_trans B _ _ _ _ _ _ HPK HPK2)|].
  split.
  { split; [unfold frame_addr in *; rewrite LF; exact HFa|].
    split; [unfold flag_addr in *; rewrite LF; exact HFl|].
    split.
    { unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 _ 8 _); [|exact HFL120].
      intros k Hk. apply KFR. lia. }
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS8]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS16]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS112]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS72]|].
    intros i Hi. apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact (HSV i Hi)]. }
  apply (alock_at_kept RG W1 m1 W2 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact (KLK a Ha).
- pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
  split; [|split; [|split; [|split; [|split; [|split]]]]];
  (apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | assumption]).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the keeping lemmas at a world relation R.  Each X_xR is X above with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cx file's carriers (GLIVE, RGO, RGI, RGE, gPOST)
   and W_rig_top_defs.v's journal statements -> their R twins, the journal lemmas -> their _xR twins.  Every other token is X's.  The hypothesis list is
   the cx file's Section wR, verbatim. ---- *)
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
(* :196 tl2_frm *)
Lemma tl2_frm_xR : forall cx fpos ly1 S1 Hp1 W1 m1 md1 k1,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
ARx ly1 S1 Hp1 W1 m1 md1 /\ In (1, fpos) (frames S1) /\
4096 <= frame_addr ly1 1 fpos /\ frame_addr ly1 1 fpos + 128 <= alloc_ceiling /\ in_app (frame_addr ly1 1 fpos) 128 /\
(forall a, frame_addr ly1 1 fpos <= a < frame_addr ly1 1 fpos + 128 -> ~ in_img SEGS a).
Proof.
intros cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ.
pose proof (tj_AR_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (H1 & H2 & H3).
change (fs_frame_bytes 1) with 128 in H2, H3.
split; [exact HAR|]. split; [exact Hfin|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left.
exists 1, fpos. split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. exact Ha.
Qed.
(* :216 live_kept *)
Lemma live_kept_xR : stmt_live_kept_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold stmt_live_kept_xR.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 Hp2 m2 md2 P HB HJ1 HROM1 HPK HFR HLK HLS HJ2 HPw HK HPR.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
destruct (tl2_frm_xR cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (SF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity. unfold SHADOW_OFF in SF.
assert (HF8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
(* the bytes P names (B: the scratch below sp, 80(sp), F + 32 .. F + 80, F's shadow) are none of: image bytes, F's
   flag cell F + 120 .., the frame slots 8(sp) .. 80(sp) and 88(sp) .. 224(sp) (B's g_frame slots 8, 16, 72, 112,
   its g_lslots 24 .. 64 and 88, and the saved registers 120 .. 224) *)
assert (NPI : forall a, in_img SEGS a -> ~ P a).
{ intros a Hi Hp. pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  destruct (HPw a Hp) as [H|[H|[H|H]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | |].
  - exact (HFni a ltac:(lia) Hi).
  - rewrite SF in H. lia. }
assert (NPF : forall a, F + 120 <= a < F + 128 -> ~ P a).
{ intros a Ha Hp. destruct (HPw a Hp) as [H|[H|[H|H]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia |].
  rewrite SF in H. exact (fshadow_not_app F 16 F 128 a HF4 ltac:(lia) HFapp H ltac:(lia)). }
assert (NPS : forall a, gsp1 cx + 8 <= a < gsp1 cx + 80 \/ gsp1 cx + 88 <= a < gsp1 cx + 224 -> ~ P a).
{ intros a Ha Hp. unfold gsp1, RIG_FRAME in Ha.
  destruct (HPw a Hp) as [H|[H|[H|H]]]; unfold gsp1, RIG_FRAME, ESTACK in H; [lia | lia | lia |].
  rewrite SF in H. lia. }
assert (VK : forall a n v, (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ P (a + k)) ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W1 m2) a n v).
{ intros a n v Hn Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m2 a n v); [|exact Hv].
  intros k Hk. destruct (Hn k Hk) as (Hr & Hnp). exact (HK (a + k) Hr Hnp). }
split.
- exists fpos, Hp2. split; [exact HJ2|].
  split.
  { intros a Ha.
    assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
    rewrite (HK a ltac:(lia) (NPI a Hi)). exact (HROM1 a Ha). }
  split.
  { intros a Hi Ho He Hp. exact (HPR a (HPK a Hi Ho He Hp)). }
  split.
  { split; [exact HFa|]. split; [exact HFl|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [lia | apply NPF; lia] | exact HFL120]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS8]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS16]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS112]|].
    split; [apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | exact HS72]|].
    intros i Hi. apply VK; [|exact (HSV i Hi)].
    intros k Hk. cbn in Hk. split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia]. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  assert (Hi : in_img SEGS a) by exact (proj1 (RGIMG a ltac:(unfold rg_rng; left; exact Ha))).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split; [exact (HK a ltac:(lia) (NPI a Hi))|].
  unfold arm. apply writable_kept. exact (HPR a).
- pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
  split; [|split; [|split; [|split; [|split; [|split]]]]];
  (apply VK; [intros k Hk; cbn in Hk; split; [unfold gsp1, RIG_FRAME; lia | apply NPS; lia] | assumption]).
Qed.
(* :279 live_drain *)
Lemma live_drain_xR : stmt_live_drain_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold stmt_live_drain_xR.
intros cx fpos F FL ly1 S1 Hp1 W1 m1 md1 k1 SA e h cap out ly2 S2 Hp2 W2 m2 md2 k2 Hp3 k3
  HB HJ1 HROM1 HPK HFR HLK HLS HJD HFPB HPK2 HJ2.
pose proof (tl2_sp cx HB) as SP.
pose proof HB as (_ & _ & _ & RGP & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & RGWR & _).
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
destruct (tl2_frm_xR cx fpos ly1 S1 Hp1 W1 m1 md1 k1 HJ1) as (HAR1 & Hfin & HF4 & HFc & HFapp & HFni).
rewrite HFa in HF4, HFc, HFapp, HFni.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HGD : gx_ok SEGS B (G_DR B RG)) by exact (gx_ok_sub SEGS B _ _ (rig_G_DR_RIG B RG) HGRIG).
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD) as (memS & HJDi & HagD).
pose proof HJDi as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRM & _).
(* drain's footprint holds only block bytes: no byte of F, and not 0 (the sink stays closed) *)
assert (NFP : forall a, F <= a < F + 128 -> ~ inFP (dr_fp SA e h cap out) a).
{ intros a Ha Hf. destruct (HFPB a Hf) as (b & n & Hin & Hr).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ b n 1 fpos HAR1 Hin Hfin) as Hd.
  rewrite HFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (SPR : forall a, fp_spares (dr_fp SA e h cap out) a).
{ intros a Ho. exfalso. destruct (HFPB 0 Ho) as (b & n & Hin & Hr).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ b n HAR1 Hin) as (_ & H4096 & _). lia. }
(* what drain keeps: the caller's frame slots (above its window), the bytes of F, g_lock *)
assert (KHI : forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. unfold gsp1, RIG_FRAME in Ha.
  apply (ajgx_keep_high_xR B PST ARx R (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGD HJD a); unfold gsp1, RIG_FRAME; lia. }
assert (KFR : forall a, F <= a < F + 128 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha.
  assert (Hrng : in_zr a (frame_rng ly1 (1, fpos)) \/
    in_zr a (shadow_addr (frame_addr ly1 1 fpos), fs_frame_bytes 1 / 8)).
  { left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes 1) with 128. lia. }
  rewrite (FRM 1 fpos a Hfin Hrng (NFP a Ha)).
  apply HagD. rewrite unsigned_lit_small by lia. intros HG. exact (HFni a Ha (proj1 (HGD a HG))). }
assert (KLK : forall a, rg_lock RG <= a < rg_lock RG + 12 -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Ho & He).
  pose proof (tl2_img_low a Hi) as Hl. unfold SHADOW_OFF in Hl.
  split.
  - apply (ajgx_keep_img_xR B PST ARx R (G_DR B RG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD a Hi Ho He
      (PSTG a ltac:(left; unfold inG, G_RIG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia)) (SPR a)).
    pose proof HRGP as (HL & _). cbn [zall_disjoint] in HL. unfold zdisj in HL. cbn [fst snd] in HL.
    destruct HL as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _).
    unfold inG, G_DR, G_SL. intros HG. rewrite !Exists_cons, Exists_nil in HG. unfold in_zr in HG. cbn [fst snd] in HG.
    (* G_DR: g_s, then G_SL's g_client_broken, g_send_eintr, g_nout, g_capout, g_out, errno *)
    destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[HG|[]]]]]]]];
    [ clear - D1 Ha HG | clear - D10 Ha HG | clear - D12 Ha HG | clear - D6 Ha HG | clear - D7 Ha HG
    | clear - D8 Ha HG | clear - D14 Ha HG ]; lia.
  - intros _. unfold arm. apply (RGWR (w_H W2) m2 a); [left; exact Ha|].
    apply (hidden_not_img SEGS W2 (Z_to_bv 64 a)). rewrite unsigned_lit_small by lia. exact Hi. }
assert (LF : ly_F ly2 = ly_F ly1) by (destruct Hly as (_ & _ & _ & _ & _ & LF & _); exact LF).
assert (VKH : forall a n v, gsp1 cx <= a -> a + Z.of_nat n <= gsp0 cx ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v).
{ intros a n v H1 H2 Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 a n v); [|exact Hv].
  intros k Hk. apply KHI. lia. }
split.
- exists fpos, Hp3. split; [exact HJ2|].
  split.
  { apply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD);
      [| exact PSTR | exact HROM1].
    intros a Ha. destruct (HROMO a Ha) as (HnG & Hrest). split; [|exact Hrest].
    intros HG. exact (HnG (rig_G_DR_RIG B RG a HG)). }
  split; [exact (apk_trans B _ _ _ _ _ _ HPK HPK2)|].
  split.
  { split; [unfold frame_addr in *; rewrite LF; exact HFa|].
    split; [unfold flag_addr in *; rewrite LF; exact HFl|].
    split.
    { unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 _ 8 _); [|exact HFL120].
      intros k Hk. apply KFR. lia. }
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS8]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS16]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS112]|].
    split; [apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact HS72]|].
    intros i Hi. apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | exact (HSV i Hi)]. }
  apply (alock_at_kept RG W1 m1 W2 m2 true HLK).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact (KLK a Ha).
- pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
  split; [|split; [|split; [|split; [|split; [|split]]]]];
  (apply VKH; [unfold gsp1, RIG_FRAME; lia | cbn; unfold gsp1, RIG_FRAME; lia | assumption]).
Qed.
End wR.

End c.
End b.
End a.
