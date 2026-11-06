(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone, lemma track
   C (RigTopRep): the representation across TOP's steps (top_rep_open, top_rep_closed, gout_kept, gtopm_kept) and
   drain's call premises (top_drain_pre, dr_fp_in), the statements of lib/B/W_rig_top_defs.v.  Ported from k3's
   image-A lib/A/W_rig_top_rep.v (a working branch 80fffa8e840); the helpers it took from lib/A's
   W_rig_tail.v (tinb and the tl_ lemmas) are copied below, unchanged.  The Section header is W_rig_top_defs.v's,
   verbatim.
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v, commit f4cd818e98d): over ARx
   (AR_laws_x's alx_* laws, ajournal_gx_x at DRAIN_STK_x); an image byte drain keeps must also be off the program
   statics PST (tc_o_KG, PSTG at its use).
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

(* ---- Where the representations' bytes are (copied from lib/A/W_rig_tail.v, unchanged; this file does not import
   any W_rig_tail). ---- *)
Definition tinb (ly : alayout) (S : astate) (a : Z) : Prop :=
exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n.
Lemma tinb_of : forall ly S p n a, In (p, n) (ablocks B ly S) -> 0 <= n -> p <= a < p + n -> tinb ly S a.
Proof. intros ly S p n a Hin Hn Ha. exists p, n. split; [exact Hin|]. pose proof (req_size_pos n Hn). lia. Qed.
Lemma tl_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.
Lemma tl_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma tl_alist_fp : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> (LA <= a < LA + 16) \/ tinb ly S a.
Proof.
intros ly S W mem LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|]. right.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app, tl_recs_len in Ha.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (tinb_of ly S (hl_v l) (AREC * hl_cap l) a Hin); [unfold AREC; lia|].
  unfold hl_n, AREC in *. revert Ha Hj Hn Hc. clear. intros. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
  rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
  apply (tinb_of ly S (fst q) (Z.of_nat (length (snd q)) + 1) a Hin); lia.
Qed.
Lemma tl_alist_blks : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W mem LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
- apply in_map_iff in Hb as (q & <- & Hq). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs q Hq)).
Qed.

Lemma tl_asrc_fp : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> (HA <= a < HA + ASRC) \/ tinb ly S a.
Proof.
intros ly S W mem HA h HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Ha. lia.
- right. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (tinb_of ly S (hs_partial h) APARTIAL a Hpb); [unfold APARTIAL; lia | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (tl_alist_fp ly S W mem (HA + 16) _ false Hpend r Hr a Ha) as [H | H]; [left; unfold ASRC; lia | right; exact H].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (tl_alist_fp ly S W mem (HA + 64) _ true Hexp r Hr a Ha) as [H | H]; [left; unfold ASRC; lia | right; exact H].
    * destruct (tl_alist_fp ly S W mem (HA + 80) _ true Hheld r Hr a Ha) as [H | H]; [left; unfold ASRC; lia | right; exact H].
Qed.
Lemma tl_asrc_blks : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W mem HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
  Hexp & Hheld & _).
unfold asrc_blks in Hb. cbn [In] in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [exact (tl_alist_blks _ _ _ _ _ _ _ Hpend b Hb)|].
apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [exact (tl_alist_blks _ _ _ _ _ _ _ Hexp b Hb)|].
exact (tl_alist_blks _ _ _ _ _ _ _ Hheld b Hb).
Qed.

Lemma tl_aentry_fp : forall ly S W mem e, aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> tinb ly S a.
Proof.
intros ly S W mem e HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (tinb_of ly S (re_buf e) (re_cap e) a Hin); lia.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, tl_key_ptrs_len in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. cbn [length] in Ha. lia.
    * apply (tinb_of ly S (re_hp e) (re_kh e) a Hin); [lia|]. unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    apply (tinb_of ly S (key_addr k) (Z.of_nat (length (key_text k)) + 1) a Hin); lia.
Qed.
Lemma tl_aentry_blks : forall ly S W mem e, aentry_ok B ly S W mem e ->
forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W mem e HE b Hb.
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct Hbuf as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
- apply in_app_or in Hb. destruct Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [In] in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in Hks. exact (proj1 (Hks k Hk)).
Qed.

Lemma tl_arelay_fp : forall ly S W mem G es, arelay_at B RG ly S W mem G es ->
forall r, In r (arelay_fp RG G es) -> forall a, fst r <= a < snd r ->
(rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) \/
tinb ly S a.
Proof.
intros ly S W mem G es HR r Hr a Ha.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HG & _ & HE & _).
unfold arelay_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
- left; left; lia.
- left; right; left; lia.
- left; right; right; lia.
- right. apply (tinb_of ly S G ATABLE a HG); [unfold ATABLE; lia | lia].
- right. apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
  rewrite Forall_forall in HE. exact (tl_aentry_fp ly S W mem e (HE e He) r Hr a Ha).
Qed.
Lemma tl_arelay_blks : forall ly S W mem G es, arelay_at B RG ly S W mem G es ->
forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
intros ly S W mem G es HR b Hb.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HG & _ & HE & _).
unfold arelay_blks in Hb. cbn [In] in Hb. destruct Hb as [<- | Hb]; [exact HG|].
apply in_concat in Hb as (bl & Hbl & Hb). apply in_map_iff in Hbl as (e & <- & He).
rewrite Forall_forall in HE. exact (tl_aentry_blks ly S W mem e (HE e He) b Hb).
Qed.

Lemma tl_aout_fp : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
(rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
 rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
 rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ as_errno B <= a < as_errno B + 4) \/ tinb ly S a.
Proof.
intros ly S W mem c O mx no cap out HO r Hr a Ha.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- left; left; lia.
- left; right; left; lia.
- left; right; right; left; lia.
- left; right; right; right; left; lia.
- left; right; right; right; right; left; lia.
- left; right; right; right; right; right; left; lia.
- left; right; right; right; right; right; right; left; lia.
- left; right; right; right; right; right; right; right; left; lia.
- left; right; right; right; right; right; right; right; right; lia.
- right. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [lia|].
  apply (tinb_of ly S out cap a Hin); lia.
Qed.
Lemma tl_aout_blks : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W mem c O mx no cap out HO b Hb.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn [In] in Hb; [destruct Hb|].
destruct Hb as [<- | []]. destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [lia | exact Hin].
Qed.

Lemma tl_kept_trans : forall (W W' W'' : world SEGS) m m' m'' a,
abyte_kept W m W' m' a -> abyte_kept W' m' W'' m'' a -> abyte_kept W m W'' m'' a.
Proof.
intros W W' W'' m m' m'' a (H1 & H2) (H3 & H4). split; [rewrite H3; exact H1 | intros Hw; exact (H4 (H2 Hw))].
Qed.

(* ---- list helpers ---- *)
Lemma tc_firstn_S : forall {A : Type} (l : list A) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros A l. induction l as [|x l IH]; intros i d Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. rewrite (IH i d) by (cbn in Hi; lia). reflexivity.
Qed.
Lemma tc_len_gps : forall cx, length (gxhs cx) = length (gxes cx) -> length (gps cx) = length (gxes cx).
Proof. intros cx HL. unfold gps. rewrite length_combine, HL. lia. Qed.
Lemma tc_gps_nth : forall cx i, length (gxhs cx) = length (gxes cx) ->
  nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i).
Proof. intros cx i HL. unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HL. Qed.
Lemma tc_skipn_es : forall cx i, (i < length (gxes cx))%nat -> skipn i (gxes cx) = gnth cx i :: skipn (S i) (gxes cx).
Proof. intros cx i Hi. unfold gnth. apply skipn_nth. exact Hi. Qed.
Lemma tc_skipn_gps : forall cx i, length (gxhs cx) = length (gxes cx) -> (i < length (gxes cx))%nat ->
  skipn i (gps cx) = (gnth cx i, ghj cx i) :: skipn (S i) (gps cx).
Proof.
intros cx i HL Hi. rewrite (skipn_nth (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj))
  by (rewrite tc_len_gps by exact HL; exact Hi).
rewrite tc_gps_nth by exact HL. reflexivity.
Qed.
Lemma tc_firstn_gps : forall cx i, length (gxhs cx) = length (gxes cx) -> (i < length (gxes cx))%nat ->
  firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)].
Proof.
intros cx i HL Hi. rewrite (tc_firstn_S (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj))
  by (rewrite tc_len_gps by exact HL; exact Hi).
rewrite tc_gps_nth by exact HL. reflexivity.
Qed.
Lemma tc_rig_slots_app : forall l1 l2, rig_slots (l1 ++ l2) = rig_slots l1 ++ rig_slots l2.
Proof. intros l1 l2. unfold rig_slots. rewrite map_app, concat_app. reflexivity. Qed.
Lemma tc_rig_srcs_cons : forall p l,
  rig_srcs (p :: l) = (if re_eof (fst p) =? 0 then asrc_blks (fst (snd p)) else []) ++ rig_srcs l.
Proof. intros p l. reflexivity. Qed.
Lemma tc_slot_lt4 : forall cx i, GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof (gnth cx i) = 0 ->
  (snd (ghj cx i) < 4)%nat.
Proof.
intros cx i HB Hi He. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & HDRS0 & _).
rewrite Forall_forall in HDRS0.
assert (Hin : In (nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj)) (gps cx))
  by (apply nth_In; rewrite tc_len_gps by exact HLEN; exact Hi).
rewrite tc_gps_nth in Hin by exact HLEN.
pose proof (HDRS0 _ Hin) as Hd. cbn [fst snd] in Hd. exact (proj1 (Hd He)).
Qed.

(* ---- keeping bytes ---- *)
(* writability survives a step whose hidden set shrinks and that keeps the byte present if it was *)
Lemma tc_wr_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a,
  hsub (w_H W') (w_H W) -> (apresent (w_H W) m a -> apresent (w_H W') m' a) ->
  writable_at SEGS (arm W m) a -> writable_at SEGS (arm W' m') a.
Proof.
intros W W' m m' a Hs Hp Hw. unfold arm, writable_at, wview, mrestrict in *. revert Hw.
destruct (w_H W' (Z_to_bv 64 a)) eqn:E'.
- rewrite (Hs _ E'). intros Hw. exact Hw.
- destruct (w_H W (Z_to_bv 64 a)) eqn:E.
  + intros Hw. destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; intros Hw.
    * destruct (Hp (conj E (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* the representation's global cells are image bytes *)
Definition tc_glob (a : Z) : Prop :=
  rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 \/
  rg_s RG <= a < rg_s RG + 4 * ASRC \/
  rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
  rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
  rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
  rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ as_errno B <= a < as_errno B + 4.
Lemma tc_glob_img : rg_place B RG -> forall a, tc_glob a -> in_img SEGS a.
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
assert (GI : forall x l, In (x, l) (G_RIG B RG) -> x <= a < x + l -> in_img SEGS a).
{ intros x l Hxl Hx. apply (proj1 (HGRIG a ltac:(unfold inG; apply Exists_exists; exists (x, l); split;
    [exact Hxl | unfold in_zr; cbn [fst snd]; lia]))). }
assert (RI : rg_rng RG a -> in_img SEGS a) by (intros Hr; exact (proj1 (RGIMG a Hr))).
unfold rg_rng in RI. unfold tc_glob in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]].
- apply RI. tauto.
- apply RI. tauto.
- exact (proj1 (HRGI a ltac:(tauto))).
- apply RI. tauto.
- exact (proj1 (HRGI a ltac:(tauto))).
- apply (GI (rg_nout RG) 8); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- apply (GI (rg_capout RG) 8); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- apply (GI (rg_out RG) 8); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- exact (proj1 (HRGI a ltac:(tauto))).
- apply (GI (rg_client_broken RG) 1); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- exact (proj1 (HRGI a ltac:(tauto))).
- apply (GI (rg_send_eintr RG) 1); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
- apply (GI (as_errno B) 4); [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | exact Ha].
Qed.

(* A memory change that keeps every byte below alloc_ceiling outside the fake frame (1, fpos) and its shadow, and
   keeps present bytes present, keeps every byte of a live block and every image byte. *)
Lemma tc_keep_frame : forall ly S Hp W m md m' fpos,
  ARx ly S Hp W m md -> In (1, fpos) (frames S) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly [(1, fpos)] a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  forall a, tinb ly S a \/ in_img SEGS a -> abyte_kept W m W m' a.
Proof.
intros ly S Hp W m md m' fpos HAR Hfin HK HP a Ha.
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in *.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [|unfold arm; apply writable_kept; apply HP].
set (F := frame_addr ly 1 fpos) in *.
assert (Hnf : forall x, ~ (F <= x < F + 128) -> ~ (shadow_addr F <= x < shadow_addr F + 16) ->
  ~ in_frames ly [(1, fpos)] x).
{ intros x N1 N2 (cid & pos & Hin & Hr). destruct Hin as [Heq | []]. injection Heq as <- <-.
  change (fs_frame_bytes 1) with 128 in Hr. change (128 / 8) with 16 in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
  fold F in Hr. tauto. }
assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
destruct Ha as [(p & n & Hin & Ha) | Hi].
- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & Hp4 & Hpc & Happ & _ & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 1 fpos HAR Hin Hfin) as Hd.
  change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  apply HK; [lia|]. apply Hnf; [lia|].
  intros Hs. rewrite SF in Hs. apply (fshadow_not_app F 16 p (req_size n) a); [lia | lia | exact Happ | lia | lia].
- pose proof (pa_segs_low a Hi) as Hl. rewrite C5 in Hl.
  apply HK; [lia|]. apply Hnf.
  + intros Hx. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR _) Hi). right. left. exists 1, fpos.
    split; [exact Hfin|]. change (fs_frame_bytes 1) with 128. fold F. lia.
  + rewrite SF. assert (0 <= F / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* aothers_at survives when the first 8 bytes of every slot but ji are kept, and slot ji passes at the end *)
Lemma tc_aothers_kept : forall W m W' m' (j : nat) fd (ji : nat),
  aothers_at RG W m j fd ->
  (forall i, (i < 4)%nat -> i <> ji -> forall a, rg_s RG + ASRC * Z.of_nat i <= a < rg_s RG + ASRC * Z.of_nat i + 8 ->
     abyte_kept W m W' m' a) ->
  (ji <> j -> exists f o, val_mem SEGS (arm W' m') (rg_s RG + ASRC * Z.of_nat ji) 4 f /\
     val_mem SEGS (arm W' m') (rg_s RG + ASRC * Z.of_nat ji + 4) 4 o /\ (o = 0 \/ f mod 2 ^ 32 <> fd mod 2 ^ 32)) ->
  aothers_at RG W' m' j fd.
Proof.
intros W m W' m' j fd ji HO HK Hji i Hi Hij. destruct (Nat.eq_dec i ji) as [-> | Hne]; [exact (Hji Hij)|].
destruct (HO i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o. split; [|split; [|exact Ho]].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi Hne); cbn in Hx; lia | exact V1].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi Hne); cbn in Hx; lia | exact V2].
Qed.

(* the representation predicates GOUT and GTOPM read, across such a memory change *)
Lemma tc_kept_pack : forall cx ly1 S1 Hp1 W1 m1 md1 m1' fpos,
  GBASE B ARx MT RP MMAX RG cx -> ARx ly1 S1 Hp1 W1 m1 md1 -> In (1, fpos) (frames S1) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ in_frames ly1 [(1, fpos)] a -> aview SEGS (w_H W1) m1' a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m1' a) ->
  (forall G es, arelay_at B RG ly1 S1 W1 m1 G es -> arelay_at B RG ly1 S1 W1 m1' G es) /\
  (forall c O mx no cap out, aout_at B RG ly1 S1 W1 m1 c O mx no cap out -> aout_at B RG ly1 S1 W1 m1' c O mx no cap out) /\
  (forall (j : nat) h, (j < 4)%nat -> asrc_at B ly1 S1 W1 m1 (rg_s RG + ASRC * Z.of_nat j) h ->
     asrc_at B ly1 S1 W1 m1' (rg_s RG + ASRC * Z.of_nat j) h) /\
  (forall e h j, dr_src_ok B RG ly1 S1 W1 m1 e h j -> dr_src_ok B RG ly1 S1 W1 m1' e h j) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 m1' a).
Proof.
intros cx ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP.
pose proof (tc_keep_frame ly1 S1 Hp1 W1 m1 md1 m1' fpos HAR Hfin HK HP) as KA.
pose proof HB as (_ & _ & _ & RGP & _).
assert (KG : forall a, tc_glob a -> abyte_kept W1 m1 W1 m1' a) by (intros a Ha; apply KA; right; exact (tc_glob_img RGP a Ha)).
assert (KS : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 m1' a)
  by (intros a Ha; apply KG; unfold tc_glob; tauto).
assert (AKS : forall (j : nat) h, (j < 4)%nat -> asrc_at B ly1 S1 W1 m1 (rg_s RG + ASRC * Z.of_nat j) h ->
  asrc_at B ly1 S1 W1 m1' (rg_s RG + ASRC * Z.of_nat j) h).
{ intros j h Hj HS. apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m1' _ _ HS); [|exact (tl_asrc_blks _ _ _ _ _ _ HS)].
  intros r Hr a Ha. destruct (tl_asrc_fp _ _ _ _ _ _ HS r Hr a Ha) as [Hg | Hb]; [|exact (KA a (or_introl Hb))].
  apply KS. unfold ASRC in *. lia. }
split.
{ intros G es HR. apply (arelay_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m1' _ _ HR); [|exact (tl_arelay_blks _ _ _ _ _ _ HR)].
  intros r Hr a Ha. destruct (tl_arelay_fp _ _ _ _ _ _ HR r Hr a Ha) as [Hg | Hb]; [|exact (KA a (or_introl Hb))].
  apply KG. unfold tc_glob. tauto. }
split.
{ intros c O mx no cap out HO. apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m1' _ _ _ _ _ _ HO);
    [|exact (tl_aout_blks _ _ _ _ _ _ _ _ _ _ HO)].
  intros r Hr a Ha. destruct (tl_aout_fp _ _ _ _ _ _ _ _ _ _ HO r Hr a Ha) as [Hg | Hb]; [|exact (KA a (or_introl Hb))].
  apply KG. unfold tc_glob. tauto. }
split; [exact AKS|].
split; [|exact KS].
intros e h j (Hj & HS & Hoth & R). split; [exact Hj|]. split; [exact (AKS j h Hj HS)|].
split; [|exact R].
apply (tc_aothers_kept W1 m1 W1 m1' j (re_fd e) j Hoth); [|intros Hc; exfalso; exact (Hc eq_refl)].
intros i' Hi' _ a Ha. apply KS. unfold ASRC in *. lia.
Qed.

Lemma gout_kept : stmt_gout_kept B ARx MT RP MMAX RG.
Proof.
unfold stmt_gout_kept. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP HG.
destruct (tc_kept_pack cx ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP) as (KR & KO & KS & KD & KB).
destruct HG as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
split; [exact Hle|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [exact (KR _ _ Hrly)|]. split; [exact (KO _ _ _ _ _ _ Hout)|].
split.
{ intros i' Hi' He. unfold gslot. apply KS; [|exact (Hsrc i' Hi' He)].
  apply (tc_slot_lt4 cx i' HB); [lia | exact He]. }
split.
{ eapply Forall_impl; [|exact Hdrs]. intros p Hp He. exact (KD _ _ _ (Hp He)). }
split.
{ intros a Ha Hnj. exact (tl_kept_trans _ W1 W1 _ m1 m1' a (Hgs a Ha Hnj) (KB a Ha)). }
split; [exact Hperm | exact Hbud].
Qed.

Lemma gtopm_kept : stmt_gtopm_kept B ARx MT RP MMAX RG.
Proof.
unfold stmt_gtopm_kept. intros cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP HG.
destruct (tc_kept_pack cx ly1 S1 Hp1 W1 m1 md1 m1' fpos HB HAR Hfin HK HP) as (KR & KO & KS & KD & KB).
unfold GTOPM in HG |- *. cbv zeta in HG |- *.
destruct HG as (Hi & Hlq & Hrel & Hgd & Hrly & Hout & Hsrc & Hopen & Hdrs & Hgs & Hperm).
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|]. split; [exact Hgd|].
split; [exact (KR _ _ Hrly)|]. split; [exact (KO _ _ _ _ _ _ Hout)|].
split.
{ intros i' Hi' He. unfold gslot. apply KS; [|exact (Hsrc i' Hi' He)].
  apply (tc_slot_lt4 cx i' HB); [lia | exact He]. }
split.
{ intros Ho. unfold gslot. apply KS; [|exact (Hopen Ho)].
  apply (tc_slot_lt4 cx i HB); [exact Hi | exact (proj1 (Z.eqb_eq _ _) Ho)]. }
split.
{ eapply Forall_impl; [|exact Hdrs]. intros p Hp He. exact (KD _ _ _ (Hp He)). }
split.
{ intros a Ha Hnj. exact (tl_kept_trans _ W1 W1 _ m1 m1' a (Hgs a Ha Hnj) (KB a Ha)). }
exact Hperm.
Qed.

Lemma top_rep_closed : stmt_top_rep_closed B ARx MT RP MMAX RG.
Proof.
unfold stmt_top_rep_closed. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1 HB Hi Heof HG.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
destruct HG as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
assert (Eo : (re_eof (gnth cx i) =? 0) = false) by (apply Z.eqb_neq; exact Heof).
pose proof (tc_skipn_es cx i Hi) as ES.
pose proof (tc_skipn_gps cx i HLEN Hi) as EP.
pose proof (tc_firstn_gps cx i HLEN Hi) as EF.
unfold GTOPM. cbv zeta. rewrite Eo.
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [unfold gdrained; cbv zeta; rewrite Eo; repeat split; reflexivity|].
split; [rewrite <- ES; exact Hrly|].
split; [exact Hout|]. split; [exact Hsrc|].
split; [intros Hc; discriminate Hc|].
split; [rewrite EP in Hdrs; exact (Forall_inv_tail Hdrs)|].
split.
{ intros a Ha Hnj. apply Hgs; [exact Ha|]. intros j Hj. apply Hnj. rewrite EF, tc_rig_slots_app.
  apply in_or_app. left. exact Hj. }
rewrite <- ES. rewrite EP, tc_rig_srcs_cons in Hperm. cbn [fst snd] in Hperm. rewrite Eo in Hperm. exact Hperm.
Qed.

(* ---- the bytes a representation reads lie in its own blocks (W_rig_tail.v tl_*_fp, with the block named) ---- *)
Lemma tc_alist_fp_blk : forall ly S W m LA l lines, alist_at B ly S W m LA l lines ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (LA <= a < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|]. right.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app, tl_recs_len in Ha.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (hl_v l, AREC * hl_cap l). split.
  + unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + cbn [fst snd]. pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as Hrq.
    unfold hl_n, AREC in *. revert Ha Hj Hn Hc Hrq. clear. intros. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
  rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
  exists (fst q, Z.of_nat (length (snd q)) + 1). split.
  + unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
  + cbn [fst snd]. pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)). lia.
Qed.
Lemma tc_asrc_fp_blk : forall ly S W m HA h, asrc_at B ly S W m HA h ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r ->
  (HA <= a < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m HA h HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Ha. lia.
- right. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  exists (hs_partial h, APARTIAL). split; [left; reflexivity|]. cbn [fst snd].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (tc_alist_fp_blk ly S W m (HA + 16) _ false Hpend r Hr a Ha) as [H | (b & Hb & Hab)];
      [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
    unfold asrc_blks. right. apply in_or_app. left. exact Hb.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (tc_alist_fp_blk ly S W m (HA + 64) _ true Hexp r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    * destruct (tc_alist_fp_blk ly S W m (HA + 80) _ true Hheld r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma tc_aentry_fp_blk : forall ly S W m e, aentry_ok B ly S W m e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks e) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m e HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (re_buf e, re_cap e). split.
  + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + cbn [fst snd]. pose proof (req_size_pos (re_cap e) ltac:(lia)). lia.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, tl_key_ptrs_len in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. cbn [length] in Ha. lia.
    * exists (re_hp e, re_kh e). split.
      -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz).
         left. reflexivity.
      -- cbn [fst snd]. pose proof (req_size_pos (re_kh e) ltac:(lia)). unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    exists (key_addr k, Z.of_nat (length (key_text k)) + 1). split.
    * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    * cbn [fst snd]. pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)). lia.
Qed.

(* ---- block lists: permutations by counting, distinctness by NoDup ---- *)
Definition tc_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma tc_cnt_cons : forall (a x : Z * Z) l,
  count_occ tc_dec (a :: l) x = ((if tc_dec a x then 1 else 0) + count_occ tc_dec l x)%nat.
Proof. intros a x l. cbn [count_occ]. destruct (tc_dec a x); lia. Qed.
Lemma tc_cnt_nil : forall x, count_occ tc_dec [] x = 0%nat.
Proof. reflexivity. Qed.
Ltac tc_perm := apply (proj2 (Permutation_count_occ tc_dec _ _)); intros ?x;
  repeat (rewrite count_occ_app || rewrite tc_cnt_cons || rewrite tc_cnt_nil); lia.
Lemma tc_nodup_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x HN H1 H2. induction l1 as [|a l1 IH]; [destruct H1|].
inversion HN as [|a' l' Hna HN']; subst. destruct H1 as [-> | H1].
- apply Hna. apply in_or_app. right. exact H2.
- exact (IH HN' H1).
Qed.
Lemma tc_skipn_combine : forall {X Y : Type} (l1 : list X) (l2 : list Y) n,
  skipn n (combine l1 l2) = combine (skipn n l1) (skipn n l2).
Proof.
intros X Y l1. induction l1 as [|x l1 IH]; intros l2 n; destruct n as [|n]; try reflexivity.
destruct l2 as [|y l2]; cbn [combine skipn].
- destruct (skipn n l1); reflexivity.
- apply IH.
Qed.
Lemma tc_srcs_in : forall p l b, In p l -> re_eof (fst p) = 0 -> In b (asrc_blks (fst (snd p))) -> In b (rig_srcs l).
Proof.
intros p l b Hp He Hb. unfold rig_srcs. apply in_concat. exists (asrc_blks (fst (snd p))). split; [|exact Hb].
apply in_map_iff. exists p. rewrite (proj2 (Z.eqb_eq _ _) He). split; [reflexivity | exact Hp].
Qed.
Lemma tc_slots_in : forall p l, In p l -> re_eof (fst p) = 0 -> In (snd (snd p)) (rig_slots l).
Proof.
intros p l Hp He. unfold rig_slots. apply in_concat. exists [snd (snd p)]. split; [|left; reflexivity].
apply in_map_iff. exists p. rewrite (proj2 (Z.eqb_eq _ _) He). split; [reflexivity | exact Hp].
Qed.
Lemma tc_rig_slots_cons : forall p l,
  rig_slots (p :: l) = (if re_eof (fst p) =? 0 then [snd (snd p)] else []) ++ rig_slots l.
Proof. intros p l. reflexivity. Qed.
Lemma tc_in_firstn_gps : forall cx i i', length (gxhs cx) = length (gxes cx) -> (i' < i)%nat -> (i <= length (gxes cx))%nat ->
  In (gnth cx i', ghj cx i') (firstn i (gps cx)).
Proof.
intros cx i i' HL Hi' Hi.
assert (H : In (nth i' (firstn i (gps cx)) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj)) (firstn i (gps cx)))
  by (apply nth_In; rewrite length_firstn, tc_len_gps by exact HL; lia).
rewrite nth_firstn in H. destruct (Nat.ltb_spec i' i) as [_|Hc]; [|lia]. rewrite tc_gps_nth in H by exact HL. exact H.
Qed.
Lemma tc_done_blks : forall cx qd i i' b, length (gxhs cx) = length (gxes cx) -> length qd = i ->
  (i <= length (gxes cx))%nat -> (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  In b (asrc_blks (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  In b (gdone_srcs (firstn i (gps cx)) qd).
Proof.
intros cx qd i i' b HL Hlq Hle Hi' He Hb. unfold gdone_srcs. apply in_concat.
eexists. split; [|exact Hb]. apply in_map_iff.
exists (nth i' (combine (firstn i (gps cx)) qd)
  ((relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj), (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
split; [|apply nth_In; rewrite length_combine, length_firstn, tc_len_gps by exact HL; lia].
rewrite combine_nth by (rewrite length_firstn, tc_len_gps by exact HL; lia).
rewrite nth_firstn. destruct (Nat.ltb_spec i' i) as [_|Hc]; [|lia]. rewrite tc_gps_nth by exact HL.
cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) He). reflexivity.
Qed.

(* ---- the relay's three cells are none of the bytes drain may change ---- *)
Lemma tc_zall_nth : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; [cbn in Hj; lia|].
destruct H as [Hb Hl]. destruct j as [|j]; [exact Hb|]. apply IH; [exact Hl | cbn in Hj; lia].
Qed.
Lemma tc_zpw_nth : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
  zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; [cbn in Hj; lia|]. destruct H as [Ha Hl].
destruct i as [|i]; destruct j as [|j]; try lia.
- cbn [nth]. apply tc_zall_nth; [exact Ha | cbn in Hj; lia].
- cbn [nth]. apply IH; [exact Hl | lia | cbn in Hj; lia].
Qed.
Ltac tc_dj i j :=
  let D := fresh "D" in
  pose proof (tc_zpw_nth _ i j (0, 0) HRGP ltac:(lia) ltac:(cbn [length]; lia)) as D;
  unfold zdisj in D; cbn [nth fst snd] in D.
Ltac tc_lia_one := match goal with
  | [ Hg : _ <= ?a < _, Ha : _ <= ?a < _, D : _ \/ _ |- False ] => clear - Hg Ha D; lia
  end.
Lemma tc_rel_glob : rg_place B RG -> forall a,
  (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG (G_DR B RG) a.
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). unfold rg_rng in RGIMG.
destruct Ha as [Ha | [Ha | Ha]].
- destruct (RGIMG a ltac:(tauto)) as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  tc_dj 1%nat 2%nat. tc_dj 2%nat 6%nat. tc_dj 2%nat 7%nat. tc_dj 2%nat 8%nat. tc_dj 2%nat 10%nat. tc_dj 2%nat 12%nat.
  tc_dj 2%nat 14%nat.
  intros Hg. unfold inG, G_DR, G_SL in Hg.
  repeat (apply Exists_cons in Hg; destruct Hg as [Hg | Hg]; [unfold in_zr in Hg; cbn [fst snd] in Hg; tc_lia_one | ]).
  apply Exists_nil in Hg. exact Hg.
- destruct (RGIMG a ltac:(tauto)) as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  tc_dj 1%nat 3%nat. tc_dj 3%nat 6%nat. tc_dj 3%nat 7%nat. tc_dj 3%nat 8%nat. tc_dj 3%nat 10%nat. tc_dj 3%nat 12%nat.
  tc_dj 3%nat 14%nat.
  intros Hg. unfold inG, G_DR, G_SL in Hg.
  repeat (apply Exists_cons in Hg; destruct Hg as [Hg | Hg]; [unfold in_zr in Hg; cbn [fst snd] in Hg; tc_lia_one | ]).
  apply Exists_nil in Hg. exact Hg.
- destruct (HRGI a ltac:(tauto)) as (I1 & I2). split; [exact I1|]. split; [exact I2|].
  tc_dj 1%nat 4%nat. tc_dj 4%nat 6%nat. tc_dj 4%nat 7%nat. tc_dj 4%nat 8%nat. tc_dj 4%nat 10%nat. tc_dj 4%nat 12%nat.
  tc_dj 4%nat 14%nat.
  split; [intros He; tc_lia_one|].
  intros Hg. unfold inG, G_DR, G_SL in Hg.
  repeat (apply Exists_cons in Hg; destruct Hg as [Hg | Hg]; [unfold in_zr in Hg; cbn [fst snd] in Hg; tc_lia_one | ]).
  apply Exists_nil in Hg. exact Hg.
Qed.

Lemma tc_aout_no : forall ly S W m c O mx no cap out, aout_at B RG ly S W m c O mx no cap out ->
  aout_at B RG ly S W m c O mx (Z.of_nat (length O)) cap out.
Proof.
intros ly S W m c O mx no cap out H.
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hno & _).
rewrite Hno. exact H.
Qed.

(* ---- entry i's drain step, open entry: GOUT i, drain's journal and DRK give GTOPM at drain's final state ---- *)
Section tc_open.
Variables (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z)
  (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (sp1 : Z)
  (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (m2 : word -> option byte) (md2 : Model) (k2 : Z)
  (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) (rest : list (Z * Z)).
Local Notation oE := (gnth cx i).
Local Notation oH := (fst (ghj cx i)).
Local Notation oJ := (snd (ghj cx i)).
Local Notation oSA := (gSA cx i).
Local Notation ocap := (if dr_live c2 (fst (ghj cx i))
  then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i))) else cap2).
Local Notation oA := (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2).
Local Notation oXt := (concat (map aentry_blks (map fst qd)) ++ concat (map aentry_blks (skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn (S i) (gps cx)) ++ gxrest cx).
Local Notation oX := ((gxG0 cx, ATABLE) :: oXt).
Hypothesis HB : GBASE B ARx MT RP MMAX RG cx.
Hypothesis Hi : (i < length (gxes cx))%nat.
Hypothesis Heof : re_eof (gnth cx i) = 0.
Hypothesis HG : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Hypothesis HAR1 : ARx ly1 S1 Hp1 W1 m1 md1.
Hypothesis HJ : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x sp1
  (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2.
Hypothesis D1 : apres_kept B W1 m1 W2 m2.
Hypothesis D3 : Permutation (ablocks B ly1 S1) (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2 ++ rest).
Hypothesis D4 : Permutation (ablocks B ly2 S2) (aentry_blks e' ++ asrc_blks h' ++ aout_blks ocap out' ++ rest).
Hypothesis D5 : garr8 SEGS (arm W2 m2) (gSA cx i) (bzs (entry_bytes e')).
Hypothesis D6 : aentry_ok B ly2 S2 W2 m2 e'.
Hypothesis D7 : dr_rel c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)) e' h' LB.
Hypothesis D8 : asrc_at B ly2 S2 W2 m2 (gslot RG cx i) h'.
Hypothesis D9 : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (gslot RG cx i <= a < gslot RG cx i + ASRC) ->
  abyte_kept W1 m1 W2 m2 a.
Hypothesis D10 : aout_at B RG ly2 S2 W2 m2 (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) (gxmx cx)
  (if dr_live c2 (fst (ghj cx i)) then Z.of_nat (length O2) + dr_tot (fst (ghj cx i)) else Z.of_nat (length O2)) ocap out'.

Lemma tc_o_eo : (re_eof (gnth cx i) =? 0) = true.
Proof. apply Z.eqb_eq. exact Heof. Qed.
Lemma tc_o_len : length (gxhs cx) = length (gxes cx).
Proof. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _). exact HLEN. Qed.
Lemma tc_o_fd : re_fd e' = re_fd (gnth cx i) /\ hs_fd h' = hs_fd (fst (ghj cx i)).
Proof.
pose proof D7 as D. unfold dr_rel in D. cbv zeta in D.
destruct D as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F13 & _). exact (conj F1 F13).
Qed.
Lemma tc_o_AR2 : ARx ly2 S2 Hp2 W2 m2 md2.
Proof. exact (tj_AR B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). Qed.

Lemma tc_o_P1 : Permutation (ablocks B ly1 S1) (oA ++ oX).
Proof.
destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i tc_o_len Hi), tc_rig_srcs_cons in Hperm.
cbn [fst snd] in Hperm. rewrite tc_o_eo in Hperm. cbv beta iota in Hperm.
eapply Permutation_trans; [exact Hperm|].
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
Lemma tc_o_P2 : Permutation (ablocks B ly1 S1) (oA ++ rest).
Proof. rewrite <- !app_assoc. exact D3. Qed.
Lemma tc_o_PX : Permutation oX rest.
Proof. apply (Permutation_app_inv_l oA). exact (Permutation_trans (Permutation_sym tc_o_P1) tc_o_P2). Qed.
Lemma tc_o_ND : List.NoDup (oA ++ oX).
Proof. exact (Permutation_NoDup tc_o_P1 (ablocks_nodup_x B ARx LAWS BLKN _ _ _ _ _ _ HAR1)). Qed.
Lemma tc_o_inX : forall b, In b oX -> In b (ablocks B ly1 S1) /\ In b (ablocks B ly2 S2) /\ ~ In b oA.
Proof.
intros b Hb. split; [apply (Permutation_in _ (Permutation_sym tc_o_P1)); apply in_or_app; right; exact Hb|].
split.
- apply (Permutation_in _ (Permutation_sym D4)). apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  exact (Permutation_in _ tc_o_PX Hb).
- intros HA. exact (tc_nodup_disj _ _ b tc_o_ND HA Hb).
Qed.
Lemma tc_o_inA : forall c, In c oA -> In c (ablocks B ly1 S1).
Proof. intros c Hc. apply (Permutation_in _ (Permutation_sym tc_o_P1)). apply in_or_app. left. exact Hc. Qed.
Lemma tc_o_table : In (gxG0 cx, ATABLE) (ablocks B ly1 S1) /\ gxG0 cx <= oSA /\ oSA + AENT <= gxG0 cx + ATABLE.
Proof.
destruct HG as (_ & Hlq & _ & Hrly & _). pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
split; [exact HGin|].
rewrite length_app, length_map, length_skipn, Hlq in Hl16. unfold gSA, AENT, ATABLE. lia.
Qed.

(* every byte of a block of oX outside the entry's 56 bytes is kept *)
Lemma tc_o_KB : forall b a, In b oX -> fst b <= a < fst b + req_size (snd b) -> ~ (oSA <= a < oSA + AENT) ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros [p n] a Hb Ha Hsa. destruct (tc_o_inX _ Hb) as (H1 & H2 & HnA). cbn [fst snd] in Ha.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n tc_o_AR2 H2) as (_ & Hp4 & Hpc & _ & Hpo & _).
pose proof asan_consts as (C1 & _).
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia. rewrite (F2 p n (a - p) H1 H2 ltac:(lia)).
  + replace (p + (a - p)) with a by lia. apply Hag. rewrite unsigned_lit_small by lia. intros HGa.
    assert (Hgr : inG (G_RIG B RG) a) by (unfold G_RIG, inG; apply Exists_cons_tl; exact HGa).
    refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a tc_o_AR2 _) (proj1 (HGRIG a Hgr))).
    left. exists p, n. split; [exact H2 | lia].
  + replace (p + (a - p)) with a by lia. intros (r & Hr & Hra). unfold dr_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | Hr]; [cbn [fst snd] in Hra; lia|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in Hra.
    assert (Hne : (p, n) <> (q, m)) by (intros Heq; rewrite Heq in HnA; exact (HnA Hc)).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n q m HAR1 H1 (tc_o_inA _ Hc) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- intros _. apply apresent_writable. exact (proj1 (Hpo a ltac:(lia))).
Qed.
(* a block of oX other than the table is apart from the entry's 56 bytes *)
Lemma tc_o_KBt : forall b a, In b oXt -> fst b <= a < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros b a Hb Ha. apply (tc_o_KB b a (or_intror Hb) Ha).
destruct tc_o_table as (HT & HS1 & HS2).
assert (HbX : In b oX) by (right; exact Hb).
pose proof (proj1 (tc_o_inX b HbX)) as Hb1.
assert (Hne : b <> (gxG0 cx, ATABLE)).
{ intros ->. pose proof (NoDup_app_remove_l _ _ tc_o_ND) as HN. inversion HN as [|x l Hx _]; subst. exact (Hx Hb). }
destruct b as [p n].
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n (gxG0 cx) ATABLE HAR1 Hb1 HT Hne) as Hd.
pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
unfold zdisjoint in Hd. cbn [fst snd] in Hd, Ha. lia.
Qed.
Lemma tc_o_fp_spares : forall a, fp_spares (dr_fp oSA oE oH cap2 out2) a.
Proof.
intros a Ho. exfalso. destruct Ho as (r & Hr & H0). unfold dr_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in H0. destruct tc_o_table as (HT & HS1 & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 HT) as (_ & Hp4 & _). lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in H0.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ q m HAR1 (tc_o_inA _ Hc)) as (_ & Hp4 & _). lia.
Qed.
(* an image byte drain may not change, and off the program statics, is kept *)
Lemma tc_o_KG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros a Hi' Ho He Hps Hg. split.
- exact (ajgx_keep_img_x B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Hi' Ho He Hps (tc_o_fp_spares a) Hg).
- destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  pose proof HJi as (_ & _ & _ & Hwle & _).
  apply (tc_wr_kept W1 W2 m1 m2 a Hwle). exact (D1 a Hi' Ho He).
Qed.

(* the slots: entry i's slot is none of the other open entries' *)
Lemma tc_o_slots : forall j, In j (rig_slots (firstn i (gps cx))) \/ In j (rig_slots (skipn (S i) (gps cx))) -> j <> oJ.
Proof.
intros j Hj ->. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HND & _).
rewrite <- (firstn_skipn i (gps cx)), tc_rig_slots_app, (tc_skipn_gps cx i tc_o_len Hi), tc_rig_slots_cons in HND.
cbn [fst snd] in HND. rewrite tc_o_eo in HND. cbv beta iota in HND. cbn [app] in HND.
apply NoDup_ListNoDup in HND. apply (NoDup_remove_2 _ _ _ HND). apply in_or_app. exact Hj.
Qed.
Lemma tc_o_slot_lt4 : (oJ < 4)%nat.
Proof. exact (tc_slot_lt4 cx i HB Hi Heof). Qed.

(* ---- the conjuncts of GTOPM ---- *)
Lemma tc_o_arelay : arelay_at B RG ly2 S2 W2 m2 (gxG0 cx) (map fst qd ++ e' :: skipn (S i) (gxes cx)).
Proof.
pose proof HB as (_ & _ & _ & RGP & _).
destruct HG as (Hle & Hlq & _ & Hrly & _).
rewrite (tc_skipn_es cx i Hi) in Hrly.
destruct Hrly as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
assert (KR : forall a, (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4) -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (tc_rel_glob RGP a Ha) as (K1 & K2 & K3 & K4).
  exact (tc_o_KG a K1 K2 K3 (PSTG a ltac:(tauto)) K4). }
assert (EL : length (map fst qd ++ e' :: skipn (S i) (gxes cx)) = length (map fst qd ++ gnth cx i :: skipn (S i) (gxes cx)))
  by (rewrite !length_app; reflexivity).
destruct tc_o_table as (HT & HS1 & HS2).
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; left; cbn in Hx; lia | exact R1]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; left; lia | exact R2]|].
split; [rewrite EL; apply (akept_vm W1 m1); [intros x Hx; apply KR; right; left; cbn in Hx; lia | exact R3]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; left; lia | exact R4]|].
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; right; right; cbn in Hx; lia | exact R5]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; right; lia | exact R6]|].
split; [rewrite EL; exact R7|].
split; [exact (proj1 (proj2 (tc_o_inX _ (or_introl eq_refl))))|].
assert (L56 : forall x, aentry_ok B ly1 S1 W1 m1 x -> length (entry_bytes x) = 56%nat)
  by (intros x (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len x P1 P2)).
assert (LE' : length (entry_bytes e') = 56%nat)
  by (destruct D6 as (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len e' P1 P2)).
rewrite Forall_forall in R10.
assert (LE : length (entry_bytes (gnth cx i)) = 56%nat) by (apply L56, R10, in_or_app; right; left; reflexivity).
assert (LP : length (concat (map entry_bytes (map fst qd))) = (56 * i)%nat).
{ rewrite relay_instance_gone_b_lem.rigl_concat_len; [rewrite length_map, Hlq; lia|].
  apply Forall_forall. intros x Hx. apply L56, R10, in_or_app. left. exact Hx. }
split.
{ destruct R9 as (T & T1 & T2 & T3). exists T.
  split; [rewrite EL; exact T1|].
  rewrite map_app, concat_app in T2, T3 |- *. cbn [map concat] in T2, T3 |- *.
  rewrite !length_app, LE, LP in T2.
  split; [rewrite !length_app, LE', LP; exact T2|].
  unfold bzs in T3 |- *. rewrite !map_app in T3 |- *. rewrite <- !app_assoc in T3 |- *.
  apply garr8_app in T3 as (T3a & T3b). apply garr8_app in T3b as (T3b & T3c).
  rewrite !length_map, LP in T3b. rewrite !length_map, LP, LE in T3c.
  apply garr8_app. rewrite !length_map, LP. split.
  - apply (akept_garr8 W1 m1); [|exact T3a]. intros x Hx. rewrite length_map, LP in Hx.
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
    apply (tc_o_KB (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia.
  - apply garr8_app. rewrite !length_map, LE'. split.
    + replace (gxG0 cx + Z.of_nat (56 * i)) with (gSA cx i) by (unfold gSA, AENT; lia). exact D5.
    + apply (akept_garr8 W1 m1); [|exact T3c]. intros x Hx. rewrite length_app, !length_map in Hx.
      pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
      apply (tc_o_KB (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia. }
split.
{ apply Forall_forall. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [<- | Hx]].
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; left; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. left. apply in_concat. exists (aentry_blks x). split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX b (or_intror (Hbl b Hb))))).
  - exact D6.
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; right; right; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. right. apply in_or_app. left. apply in_concat. exists (aentry_blks x).
      split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX b (or_intror (Hbl b Hb))))). }
(* arelay_at's 12th conjunct (the kit's W_rep): the fds as before (drain keeps re_fd); no block of the drained entry e'
   is the table, because the table is in rest (tc_o_PX) and drain's post lists e''s blocks beside rest without
   repetition (D4, AR's NoDup of the live blocks) *)
destruct R11 as [R11 R12]. split.
{ rewrite !map_app in R11 |- *. cbn [map] in R11 |- *. rewrite (proj1 tc_o_fd). exact R11. }
apply Forall_app in R12 as [G1 G2]. apply Forall_cons_iff in G2 as [_ G4].
apply Forall_app. split; [exact G1|]. apply Forall_cons; [|exact G4].
intros b Hb Eb. subst b.
pose proof (Permutation_NoDup D4 (ablocks_nodup_x B ARx LAWS BLKN _ _ _ _ _ _ tc_o_AR2)) as ND2.
apply (tc_nodup_disj _ _ (gxG0 cx, ATABLE) ND2 Hb).
apply in_or_app. right. apply in_or_app. right. exact (Permutation_in _ tc_o_PX (in_eq _ _)).
Qed.

Lemma tc_o_done : forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  asrc_at B ly2 S2 W2 m2 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
Proof.
intros i' Hi' He. destruct HG as (Hle & Hlq & _ & _ & _ & Hsrc & _).
pose proof (Hsrc i' Hi' He) as HS.
assert (Hj4 : (snd (ghj cx i') < 4)%nat) by (apply (tc_slot_lt4 cx i' HB); [lia | exact He]).
assert (Hji : snd (ghj cx i') <> oJ).
{ apply tc_o_slots. left. apply (tc_slots_in (gnth cx i', ghj cx i')); [|exact He].
  apply tc_in_firstn_gps; [exact tc_o_len | exact Hi' | lia]. }
assert (Hji' : Z.of_nat (snd (ghj cx i')) <> Z.of_nat oJ) by lia.
pose proof tc_o_slot_lt4 as HJ4.
unfold gslot in *.
apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
- intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
  + apply D9; unfold ASRC in *; lia.
  + apply (tc_o_KBt b a); [|exact Hab]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len Hlq ltac:(lia) Hi' He Hb).
- intros b Hb. assert (HbX : In b oX).
  { right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len Hlq ltac:(lia) Hi' He Hb). }
  exact (proj1 (proj2 (tc_o_inX b HbX))).
Qed.

Lemma tc_o_later : Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly2 S2 W2 m2 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)).
Proof.
destruct HG as (_ & _ & _ & Hrly & _ & _ & Hdrs & _).
rewrite (tc_skipn_gps cx i tc_o_len Hi) in Hdrs.
pose proof (Forall_inv Hdrs) as Hd0. cbn [fst snd] in Hd0. destruct (Hd0 Heof) as (_ & _ & _ & Hfd0 & _).
apply Forall_inv_tail in Hdrs.
rewrite (tc_skipn_es cx i Hi) in Hrly. pose proof Hrly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rok & (R11 & _)).
rewrite map_app in R11. cbn [map] in R11. apply NoDup_ListNoDup in R11. apply NoDup_remove_2 in R11.
pose proof tc_o_slot_lt4 as HJ4.
rewrite Forall_forall in Hdrs |- *. intros [ep [hp jp]] Hp He. cbn [fst snd] in He |- *.
destruct (Hdrs _ Hp He) as (Hj & HS & Hoth & R). cbn [fst snd] in Hj, HS, Hoth, R.
assert (Hji : jp <> oJ) by (apply tc_o_slots; right; exact (tc_slots_in (ep, (hp, jp)) _ Hp He)).
assert (Hji' : Z.of_nat jp <> Z.of_nat oJ) by lia.
assert (Hfd : re_fd ep <> re_fd (gnth cx i)).
{ intros Heq. apply R11. apply in_or_app. right. rewrite <- Heq. apply in_map.
  unfold gps in Hp. rewrite tc_skipn_combine in Hp. exact (in_combine_l _ _ _ _ Hp). }
assert (HepIn : In ep (skipn (S i) (gxes cx))).
{ pose proof Hp as Hp'. unfold gps in Hp'. rewrite tc_skipn_combine in Hp'. exact (in_combine_l _ _ _ _ Hp'). }
assert (Hfdb : 0 <= re_fd ep < 2 ^ 31 /\ 0 <= re_fd (gnth cx i) < 2 ^ 31).
{ rewrite Forall_forall in Rok. split.
  - destruct (Rok ep ltac:(apply in_or_app; right; right; exact HepIn)) as (_ & _ & _ & _ & Hb & _). exact Hb.
  - destruct (Rok (gnth cx i) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & Hb & _). exact Hb. }
assert (Hbl : forall b, In b (asrc_blks hp) -> In b oXt).
{ intros b Hb. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  exact (tc_srcs_in (ep, (hp, jp)) _ b Hp He Hb). }
split; [exact Hj|]. split.
- apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
  + intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
    * apply D9; [unfold ASRC in Hsl |- *; lia | unfold gslot, ASRC in Hsl |- *; lia].
    * exact (tc_o_KBt b a (Hbl b Hb) Hab).
  + intros b Hb. exact (proj1 (proj2 (tc_o_inX b (or_intror (Hbl b Hb))))).
- split; [|exact R].
  apply (tc_aothers_kept W1 m1 W2 m2 jp (re_fd ep) oJ Hoth).
  + intros i'' Hi'' Hne a Ha. assert (Z.of_nat i'' <> Z.of_nat oJ) by lia.
    apply D9; [unfold ASRC in Ha |- *; lia | unfold gslot, ASRC in Ha |- *; lia].
  + intros _. exists (hs_fd h'), (hs_open h').
    pose proof D8 as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & _). unfold gslot in V1, V2.
    split; [exact V1|]. split; [exact V2|]. right. rewrite (proj2 tc_o_fd), Hfd0, !(Z.mod_small _ (2 ^ 32)) by lia.
    intros Heq. exact (Hfd (eq_sym Heq)).
Qed.

Lemma tc_o_gtopm : GTOPM B RG cx i qd c2 O2 cap2 e' h' ev' LB (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) ocap out' ly2 S2 W2 m2.
Proof.
pose proof HG as (Hle & Hlq & Hrel & _ & _ & _ & _ & Hgs & _).
unfold GTOPM. cbv zeta. rewrite tc_o_eo. cbv beta iota.
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [unfold gdrained; cbv zeta; rewrite tc_o_eo; cbv beta iota; cbn [andb];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | exact D7]|].
split; [exact tc_o_arelay|].
split; [exact (tc_aout_no _ _ _ _ _ _ _ _ _ _ D10)|].
split; [exact tc_o_done|].
split; [intros _; exact D8|].
split; [exact tc_o_later|].
split.
{ intros a Ha Hnj. apply (tl_kept_trans (gxW cx) W1 W2 (gxmem cx) m1 m2 a).
  - apply Hgs; [exact Ha|]. intros j Hj. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len Hi), tc_rig_slots_app.
    apply in_or_app. left. exact Hj.
  - apply D9; [exact Ha|]. unfold gslot. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len Hi), tc_rig_slots_app.
    apply in_or_app. right. rewrite tc_rig_slots_cons. cbn [fst snd]. rewrite tc_o_eo. left. reflexivity. }
eapply Permutation_trans; [exact D4|].
eapply Permutation_trans.
{ apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head. exact (Permutation_sym tc_o_PX). }
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
End tc_open.

Lemma top_rep_open : stmt_top_rep_open B PST ARx MT RP MMAX RG.
Proof.
unfold stmt_top_rep_open. cbv zeta.
intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2 HB Hi Heof HG HAR1 HJ Hsp HD.
unfold DRK in HD. cbv zeta in HD.
destruct HD as (e' & h' & out' & ev' & LB & rest & D1 & _ & D3 & D4 & D5 & _ & D6 & D7 & D8 & D9 & D10).
exists e', h', ev', LB, out'.
eapply tc_o_gtopm; eassumption.
Qed.

(* ---- TOP's drain call: drain's memory premises and footprint ---- *)
Lemma tc_nodup_app_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. intros l1 l2 H. induction l1 as [|a l1 IH]; [exact H|]. inversion H; subst. apply IH. assumption. Qed.

Lemma top_drain_pre : stmt_top_drain_pre B ARx MT RP MMAX RG.
Proof.
unfold stmt_top_drain_pre. cbv zeta. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 HB Hi Heof HG HAR1.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _).
destruct HG as (Hle & Hlq & _ & Hrly & _ & _ & Hdrs & _ & Hperm & _).
pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
rewrite length_app, length_map, length_skipn, Hlq in Hl16.
assert (HSA : gxG0 cx <= gSA cx i /\ gSA cx i + AENT <= gxG0 cx + ATABLE) by (unfold gSA, AENT, ATABLE; lia).
rewrite (tc_skipn_es cx i Hi) in Hrly.
destruct Hrly as (_ & _ & _ & _ & _ & _ & _ & _ & R9 & R10 & _).
rewrite Forall_forall in R10.
assert (L56 : forall x, aentry_ok B ly1 S1 W1 m1 x -> length (entry_bytes x) = 56%nat)
  by (intros x (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len x P1 P2)).
assert (Hok : aentry_ok B ly1 S1 W1 m1 (gnth cx i)) by (apply R10, in_or_app; right; left; reflexivity).
split; [exact HGin|]. split; [exact (proj1 HSA)|]. split; [exact (proj2 HSA)|].
split.
{ destruct R9 as (T & _ & _ & T3).
  assert (LP : length (concat (map entry_bytes (map fst qd))) = (56 * i)%nat).
  { rewrite relay_instance_gone_b_lem.rigl_concat_len; [rewrite length_map, Hlq; lia|].
    apply Forall_forall. intros x Hx. apply L56, R10, in_or_app. left. exact Hx. }
  rewrite map_app, concat_app in T3. cbn [map concat] in T3.
  unfold bzs in T3 |- *. rewrite !map_app in T3. rewrite <- !app_assoc in T3.
  apply garr8_app in T3 as (_ & T3b). apply garr8_app in T3b as (T3b & _).
  rewrite length_map, LP in T3b.
  replace (gSA cx i) with (gxG0 cx + Z.of_nat (56 * i)) by (unfold gSA, AENT; lia). exact T3b. }
split.
{ intros k Hk. apply apresent_writable.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 HGin) as (_ & _ & _ & _ & Hpo & _).
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)).
  exact (proj1 (Hpo (gSA cx i + k) ltac:(unfold AENT, ATABLE in *; lia))). }
split; [exact Hok|].
split.
{ rewrite (tc_skipn_gps cx i HLEN Hi) in Hdrs. pose proof (Forall_inv Hdrs) as Hd0. cbn [fst snd] in Hd0. exact (Hd0 Heof). }
exists (concat (map aentry_blks (map fst qd)) ++ concat (map aentry_blks (skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn (S i) (gps cx)) ++ gxrest cx).
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i HLEN Hi), tc_rig_srcs_cons in Hperm. cbn [fst snd] in Hperm.
rewrite (proj2 (Z.eqb_eq _ _) Heof) in Hperm. cbv beta iota in Hperm.
eapply Permutation_trans; [exact Hperm|]. rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.

Lemma dr_fp_in : stmt_dr_fp_in B ARx MT RP MMAX RG.
Proof.
unfold stmt_dr_fp_in. cbv zeta. intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 HB Hi Heof HG HAR1 a Ha.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _ & _ & HPERM0 & _).
destruct HG as (Hle & Hlq & _ & Hrly & _ & _ & _ & _ & Hperm & _).
pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
rewrite length_app, length_map, length_skipn, Hlq in Hl16.
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i HLEN Hi), tc_rig_srcs_cons in Hperm. cbn [fst snd] in Hperm.
rewrite (proj2 (Z.eqb_eq _ _) Heof) in Hperm. cbv beta iota in Hperm.
assert (HL1 : forall c, In c (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2) ->
  In c (ablocks B ly1 S1)).
{ intros c Hc. apply (Permutation_in _ (Permutation_sym Hperm)). right.
  rewrite map_app, concat_app. cbn [map concat].
  apply in_app_or in Hc. destruct Hc as [Hc | Hc].
  - apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hc.
  - apply in_or_app. right. apply in_or_app. right. apply in_app_or in Hc. destruct Hc as [Hc | Hc].
    + apply in_or_app. left. apply in_or_app. left. exact Hc.
    + apply in_or_app. right. apply in_or_app. left. exact Hc. }
assert (GF : forall b, In b ((gxG0 cx, ATABLE) :: concat (map aentry_blks (gxes cx)) ++ rig_srcs (gps cx) ++
    aout_blks (gxcap cx) (gxout cx)) -> In b (ablocks B ly1 S1) -> fst b <= a < fst b + req_size (snd b) ->
  (inFP (gFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (gxly cx) (gxS cx)) (ablocks B ly1 S1) a).
{ intros [p n] Hb H1 Hpa. cbn [fst snd] in Hpa. left. split; [|exists p, n; split; [exact H1 | exact Hpa]].
  exists (p, p + req_size n). split; [|exact Hpa]. unfold gFP, rig_fp, ablocks_fp.
  exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) Hb). }
destruct Ha as (r & Hr & Hra). unfold dr_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Hra. apply (GF (gxG0 cx, ATABLE)); [left; reflexivity | exact HGin|].
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)). cbn [fst snd]. unfold gSA, AENT, ATABLE in *. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as (c & <- & Hc). cbn [fst snd] in Hra.
  pose proof (HL1 c Hc) as Hc1.
  apply in_app_or in Hc. destruct Hc as [Hc | Hc].
  + apply (GF c); [|exact Hc1 | exact Hra]. right. apply in_or_app. left. apply in_concat. exists (aentry_blks (gnth cx i)).
    split; [apply in_map; unfold gnth; apply nth_In; exact Hi | exact Hc].
  + apply in_app_or in Hc. destruct Hc as [Hc | Hc].
    * apply (GF c); [|exact Hc1 | exact Hra]. right. apply in_or_app. right. apply in_or_app. left.
      apply (tc_srcs_in (gnth cx i, ghj cx i)); [|exact Heof | exact Hc].
      rewrite <- (tc_gps_nth cx i HLEN). apply nth_In. rewrite tc_len_gps by exact HLEN. exact Hi.
    * unfold aout_blks in Hc. destruct (Z.eqb_spec cap2 0) as [Hc0 | Hc0]; [destruct Hc|].
      destruct Hc as [<- | []]. cbn [fst snd] in Hra.
      destruct (in_dec tc_dec (out2, cap2) (ablocks B (gxly cx) (gxS cx))) as [Hin0 | Hnin0].
      -- apply (Permutation_in _ HPERM0) in Hin0. destruct Hin0 as [Heq | Hin0].
         { apply (GF (out2, cap2)); [left; exact Heq | exact Hc1 | exact Hra]. }
         apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
         { apply (GF (out2, cap2)); [right; apply in_or_app; left; exact Hin0 | exact Hc1 | exact Hra]. }
         apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
         { apply (GF (out2, cap2)); [right; apply in_or_app; right; apply in_or_app; left; exact Hin0 | exact Hc1 | exact Hra]. }
         apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
         { apply (GF (out2, cap2)); [right; apply in_or_app; right; apply in_or_app; right; exact Hin0 | exact Hc1 | exact Hra]. }
         exfalso.
         pose proof (Permutation_NoDup Hperm (ablocks_nodup_x B ARx LAWS BLKN _ _ _ _ _ _ HAR1)) as HN.
         apply (tc_nodup_app_r [(gxG0 cx, ATABLE)]) in HN.
         apply tc_nodup_app_r, tc_nodup_app_r, tc_nodup_app_r in HN.
         apply (tc_nodup_disj _ _ (out2, cap2) HN); [|exact Hin0].
         unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
      -- right. exists out2, cap2. split; [exact Hc1|]. split; [exact Hnin0 | exact Hra].
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the open entry's drain step at a world relation R.  Each X_xR is X above with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cx file's carriers (GLIVE, RGO, RGI, RGE, gPOST)
   and W_rig_top_defs.v's journal statements -> their R twins, drain's journal at R; the image bytes' writability by tc_wr_img_xR (hidden_not_img alone).  Every other token is X's.  The hypothesis list is
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
(* an image byte is never hidden, so its writability follows its presence (hidden_not_img alone; no fact about R):
   the R form of tc_wr_kept at an image byte, for tc_o_KG_xR, whose drain journal relates W1 and W2 by R *)
Lemma tc_wr_img_xR : forall (W W' : world SEGS) (m m' : word -> option byte) a, in_img SEGS a ->
  (apresent (w_H W) m a -> apresent (w_H W') m' a) ->
  writable_at SEGS (arm W m) a -> writable_at SEGS (arm W' m') a.
Proof.
intros W W' m m' a Hi Hp Hw.
assert (HL : 0 <= a < 2 ^ 64).
{ pose proof (pa_segs_low a Hi) as H. pose proof asan_consts as (_ & _ & _ & _ & C5). rewrite C5 in H.
  unfold SHADOW_OFF in H. lia. }
assert (E1 : w_H W (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite unsigned_lit_small by lia; exact Hi).
assert (E2 : w_H W' (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite unsigned_lit_small by lia; exact Hi).
unfold arm, writable_at, wview, mrestrict in *. revert Hw. rewrite E1, E2.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; intros Hw.
- destruct (Hp (conj E1 (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* :784 Section tc_open *)
Section tc_open_xR.
Variables (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (c2 : ctl) (O2 : list byte) (cap2 out2 spent : Z)
  (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (sp1 : Z)
  (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (m2 : word -> option byte) (md2 : Model) (k2 : Z)
  (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) (rest : list (Z * Z)).
Local Notation oE := (gnth cx i).
Local Notation oH := (fst (ghj cx i)).
Local Notation oJ := (snd (ghj cx i)).
Local Notation oSA := (gSA cx i).
Local Notation ocap := (if dr_live c2 (fst (ghj cx i))
  then drain_b_c.ds_ocap (dr_fin c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i))) else cap2).
Local Notation oA := (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2).
Local Notation oXt := (concat (map aentry_blks (map fst qd)) ++ concat (map aentry_blks (skipn (S i) (gxes cx))) ++
  gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn (S i) (gps cx)) ++ gxrest cx).
Local Notation oX := ((gxG0 cx, ATABLE) :: oXt).
Hypothesis HB : GBASE B ARx MT RP MMAX RG cx.
Hypothesis Hi : (i < length (gxes cx))%nat.
Hypothesis Heof : re_eof (gnth cx i) = 0.
Hypothesis HG : GOUT B MT RP MMAX RG cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Hypothesis HAR1 : ARx ly1 S1 Hp1 W1 m1 md1.
Hypothesis HJ : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x sp1
  (dr_fp (gSA cx i) (gnth cx i) (fst (ghj cx i)) cap2 out2) ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k2.
Hypothesis D1 : apres_kept B W1 m1 W2 m2.
Hypothesis D3 : Permutation (ablocks B ly1 S1) (aentry_blks (gnth cx i) ++ asrc_blks (fst (ghj cx i)) ++ aout_blks cap2 out2 ++ rest).
Hypothesis D4 : Permutation (ablocks B ly2 S2) (aentry_blks e' ++ asrc_blks h' ++ aout_blks ocap out' ++ rest).
Hypothesis D5 : garr8 SEGS (arm W2 m2) (gSA cx i) (bzs (entry_bytes e')).
Hypothesis D6 : aentry_ok B ly2 S2 W2 m2 e'.
Hypothesis D7 : dr_rel c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (gnth cx i) (fst (ghj cx i)) e' h' LB.
Hypothesis D8 : asrc_at B ly2 S2 W2 m2 (gslot RG cx i) h'.
Hypothesis D9 : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (gslot RG cx i <= a < gslot RG cx i + ASRC) ->
  abyte_kept W1 m1 W2 m2 a.
Hypothesis D10 : aout_at B RG ly2 S2 W2 m2 (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) (gxmx cx)
  (if dr_live c2 (fst (ghj cx i)) then Z.of_nat (length O2) + dr_tot (fst (ghj cx i)) else Z.of_nat (length O2)) ocap out'.

Lemma tc_o_eo_xR : (re_eof (gnth cx i) =? 0) = true.
Proof. apply Z.eqb_eq. exact Heof. Qed.
Lemma tc_o_len_xR : length (gxhs cx) = length (gxes cx).
Proof. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & _). exact HLEN. Qed.
Lemma tc_o_fd_xR : re_fd e' = re_fd (gnth cx i) /\ hs_fd h' = hs_fd (fst (ghj cx i)).
Proof.
pose proof D7 as D. unfold dr_rel in D. cbv zeta in D.
destruct D as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F13 & _). exact (conj F1 F13).
Qed.
Lemma tc_o_AR2_xR : ARx ly2 S2 Hp2 W2 m2 md2.
Proof. exact (tj_AR_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). Qed.

Lemma tc_o_P1_xR : Permutation (ablocks B ly1 S1) (oA ++ oX).
Proof.
destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
rewrite (tc_skipn_es cx i Hi), (tc_skipn_gps cx i tc_o_len_xR Hi), tc_rig_srcs_cons in Hperm.
cbn [fst snd] in Hperm. rewrite tc_o_eo_xR in Hperm. cbv beta iota in Hperm.
eapply Permutation_trans; [exact Hperm|].
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
Lemma tc_o_P2_xR : Permutation (ablocks B ly1 S1) (oA ++ rest).
Proof. rewrite <- !app_assoc. exact D3. Qed.
Lemma tc_o_PX_xR : Permutation oX rest.
Proof. apply (Permutation_app_inv_l oA). exact (Permutation_trans (Permutation_sym tc_o_P1_xR) tc_o_P2_xR). Qed.
Lemma tc_o_ND_xR : List.NoDup (oA ++ oX).
Proof. exact (Permutation_NoDup tc_o_P1_xR (ablocks_nodup_x B ARx LAWS BLKN _ _ _ _ _ _ HAR1)). Qed.
Lemma tc_o_inX_xR : forall b, In b oX -> In b (ablocks B ly1 S1) /\ In b (ablocks B ly2 S2) /\ ~ In b oA.
Proof.
intros b Hb. split; [apply (Permutation_in _ (Permutation_sym tc_o_P1_xR)); apply in_or_app; right; exact Hb|].
split.
- apply (Permutation_in _ (Permutation_sym D4)). apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  exact (Permutation_in _ tc_o_PX_xR Hb).
- intros HA. exact (tc_nodup_disj _ _ b tc_o_ND_xR HA Hb).
Qed.
Lemma tc_o_inA_xR : forall c, In c oA -> In c (ablocks B ly1 S1).
Proof. intros c Hc. apply (Permutation_in _ (Permutation_sym tc_o_P1_xR)). apply in_or_app. left. exact Hc. Qed.
Lemma tc_o_table_xR : In (gxG0 cx, ATABLE) (ablocks B ly1 S1) /\ gxG0 cx <= oSA /\ oSA + AENT <= gxG0 cx + ATABLE.
Proof.
destruct HG as (_ & Hlq & _ & Hrly & _). pose proof Hrly as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & _).
split; [exact HGin|].
rewrite length_app, length_map, length_skipn, Hlq in Hl16. unfold gSA, AENT, ATABLE. lia.
Qed.

(* every byte of a block of oX outside the entry's 56 bytes is kept *)
Lemma tc_o_KB_xR : forall b a, In b oX -> fst b <= a < fst b + req_size (snd b) -> ~ (oSA <= a < oSA + AENT) ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros [p n] a Hb Ha Hsa. destruct (tc_o_inX_xR _ Hb) as (H1 & H2 & HnA). cbn [fst snd] in Ha.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n tc_o_AR2_xR H2) as (_ & Hp4 & Hpc & _ & Hpo & _).
pose proof asan_consts as (C1 & _).
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia. rewrite (F2 p n (a - p) H1 H2 ltac:(lia)).
  + replace (p + (a - p)) with a by lia. apply Hag. rewrite unsigned_lit_small by lia. intros HGa.
    assert (Hgr : inG (G_RIG B RG) a) by (unfold G_RIG, inG; apply Exists_cons_tl; exact HGa).
    refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a tc_o_AR2_xR _) (proj1 (HGRIG a Hgr))).
    left. exists p, n. split; [exact H2 | lia].
  + replace (p + (a - p)) with a by lia. intros (r & Hr & Hra). unfold dr_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | Hr]; [cbn [fst snd] in Hra; lia|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in Hra.
    assert (Hne : (p, n) <> (q, m)) by (intros Heq; rewrite Heq in HnA; exact (HnA Hc)).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n q m HAR1 H1 (tc_o_inA_xR _ Hc) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- intros _. apply apresent_writable. exact (proj1 (Hpo a ltac:(lia))).
Qed.
(* a block of oX other than the table is apart from the entry's 56 bytes *)
Lemma tc_o_KBt_xR : forall b a, In b oXt -> fst b <= a < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros b a Hb Ha. apply (tc_o_KB_xR b a (or_intror Hb) Ha).
destruct tc_o_table_xR as (HT & HS1 & HS2).
assert (HbX : In b oX) by (right; exact Hb).
pose proof (proj1 (tc_o_inX_xR b HbX)) as Hb1.
assert (Hne : b <> (gxG0 cx, ATABLE)).
{ intros ->. pose proof (NoDup_app_remove_l _ _ tc_o_ND_xR) as HN. inversion HN as [|x l Hx _]; subst. exact (Hx Hb). }
destruct b as [p n].
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ p n (gxG0 cx) ATABLE HAR1 Hb1 HT Hne) as Hd.
pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
unfold zdisjoint in Hd. cbn [fst snd] in Hd, Ha. lia.
Qed.
Lemma tc_o_fp_spares_xR : forall a, fp_spares (dr_fp oSA oE oH cap2 out2) a.
Proof.
intros a Ho. exfalso. destruct Ho as (r & Hr & H0). unfold dr_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in H0. destruct tc_o_table_xR as (HT & HS1 & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 HT) as (_ & Hp4 & _). lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hc). cbn [fst snd] in H0.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ q m HAR1 (tc_o_inA_xR _ Hc)) as (_ & Hp4 & _). lia.
Qed.
(* an image byte drain may not change, and off the program statics, is kept *)
Lemma tc_o_KG_xR : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros a Hi' Ho He Hps Hg. split.
- exact (ajgx_keep_img_xR B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Hi' Ho He Hps (tc_o_fp_spares_xR a) Hg).
- apply (tc_wr_img_xR W1 W2 m1 m2 a Hi'). exact (D1 a Hi' Ho He).
Qed.

(* the slots: entry i's slot is none of the other open entries' *)
Lemma tc_o_slots_xR : forall j, In j (rig_slots (firstn i (gps cx))) \/ In j (rig_slots (skipn (S i) (gps cx))) -> j <> oJ.
Proof.
intros j Hj ->. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HND & _).
rewrite <- (firstn_skipn i (gps cx)), tc_rig_slots_app, (tc_skipn_gps cx i tc_o_len_xR Hi), tc_rig_slots_cons in HND.
cbn [fst snd] in HND. rewrite tc_o_eo_xR in HND. cbv beta iota in HND. cbn [app] in HND.
apply NoDup_ListNoDup in HND. apply (NoDup_remove_2 _ _ _ HND). apply in_or_app. exact Hj.
Qed.
Lemma tc_o_slot_lt4_xR : (oJ < 4)%nat.
Proof. exact (tc_slot_lt4 cx i HB Hi Heof). Qed.

(* ---- the conjuncts of GTOPM ---- *)
Lemma tc_o_arelay_xR : arelay_at B RG ly2 S2 W2 m2 (gxG0 cx) (map fst qd ++ e' :: skipn (S i) (gxes cx)).
Proof.
pose proof HB as (_ & _ & _ & RGP & _).
destruct HG as (Hle & Hlq & _ & Hrly & _).
rewrite (tc_skipn_es cx i Hi) in Hrly.
destruct Hrly as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
assert (KR : forall a, (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4) -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. destruct (tc_rel_glob RGP a Ha) as (K1 & K2 & K3 & K4).
  exact (tc_o_KG_xR a K1 K2 K3 (PSTG a ltac:(tauto)) K4). }
assert (EL : length (map fst qd ++ e' :: skipn (S i) (gxes cx)) = length (map fst qd ++ gnth cx i :: skipn (S i) (gxes cx)))
  by (rewrite !length_app; reflexivity).
destruct tc_o_table_xR as (HT & HS1 & HS2).
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; left; cbn in Hx; lia | exact R1]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; left; lia | exact R2]|].
split; [rewrite EL; apply (akept_vm W1 m1); [intros x Hx; apply KR; right; left; cbn in Hx; lia | exact R3]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; left; lia | exact R4]|].
split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; right; right; cbn in Hx; lia | exact R5]|].
split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; right; right; lia | exact R6]|].
split; [rewrite EL; exact R7|].
split; [exact (proj1 (proj2 (tc_o_inX_xR _ (or_introl eq_refl))))|].
assert (L56 : forall x, aentry_ok B ly1 S1 W1 m1 x -> length (entry_bytes x) = 56%nat)
  by (intros x (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len x P1 P2)).
assert (LE' : length (entry_bytes e') = 56%nat)
  by (destruct D6 as (_ & _ & P1 & P2 & _); exact (relay_instance_gone_b_lem.rig_entry_len e' P1 P2)).
rewrite Forall_forall in R10.
assert (LE : length (entry_bytes (gnth cx i)) = 56%nat) by (apply L56, R10, in_or_app; right; left; reflexivity).
assert (LP : length (concat (map entry_bytes (map fst qd))) = (56 * i)%nat).
{ rewrite relay_instance_gone_b_lem.rigl_concat_len; [rewrite length_map, Hlq; lia|].
  apply Forall_forall. intros x Hx. apply L56, R10, in_or_app. left. exact Hx. }
split.
{ destruct R9 as (T & T1 & T2 & T3). exists T.
  split; [rewrite EL; exact T1|].
  rewrite map_app, concat_app in T2, T3 |- *. cbn [map concat] in T2, T3 |- *.
  rewrite !length_app, LE, LP in T2.
  split; [rewrite !length_app, LE', LP; exact T2|].
  unfold bzs in T3 |- *. rewrite !map_app in T3 |- *. rewrite <- !app_assoc in T3 |- *.
  apply garr8_app in T3 as (T3a & T3b). apply garr8_app in T3b as (T3b & T3c).
  rewrite !length_map, LP in T3b. rewrite !length_map, LP, LE in T3c.
  apply garr8_app. rewrite !length_map, LP. split.
  - apply (akept_garr8 W1 m1); [|exact T3a]. intros x Hx. rewrite length_map, LP in Hx.
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
    apply (tc_o_KB_xR (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia.
  - apply garr8_app. rewrite !length_map, LE'. split.
    + replace (gxG0 cx + Z.of_nat (56 * i)) with (gSA cx i) by (unfold gSA, AENT; lia). exact D5.
    + apply (akept_garr8 W1 m1); [|exact T3c]. intros x Hx. rewrite length_app, !length_map in Hx.
      pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as Hrq.
      apply (tc_o_KB_xR (gxG0 cx, ATABLE) x (or_introl eq_refl)); cbn [fst snd]; unfold gSA, AENT, ATABLE in *; lia. }
split.
{ apply Forall_forall. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [<- | Hx]].
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; left; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. left. apply in_concat. exists (aentry_blks x). split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt_xR b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX_xR b (or_intror (Hbl b Hb))))).
  - exact D6.
  - assert (Hok : aentry_ok B ly1 S1 W1 m1 x) by (apply R10, in_or_app; right; right; exact Hx).
    assert (Hbl : forall b, In b (aentry_blks x) -> In b oXt).
    { intros b Hb. apply in_or_app. right. apply in_or_app. left. apply in_concat. exists (aentry_blks x).
      split; [apply in_map; exact Hx | exact Hb]. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 x Hok).
    + intros r Hr a Ha. destruct (tc_aentry_fp_blk _ _ _ _ x Hok r Hr a Ha) as (b & Hb & Hab).
      exact (tc_o_KBt_xR b a (Hbl b Hb) Hab).
    + intros b Hb. exact (proj1 (proj2 (tc_o_inX_xR b (or_intror (Hbl b Hb))))). }
(* arelay_at's 12th conjunct (the kit's W_rep): the fds as before (drain keeps re_fd); no block of the drained entry e'
   is the table, because the table is in rest (tc_o_PX_xR) and drain's post lists e''s blocks beside rest without
   repetition (D4, AR's NoDup of the live blocks) *)
destruct R11 as [R11 R12]. split.
{ rewrite !map_app in R11 |- *. cbn [map] in R11 |- *. rewrite (proj1 tc_o_fd_xR). exact R11. }
apply Forall_app in R12 as [G1 G2]. apply Forall_cons_iff in G2 as [_ G4].
apply Forall_app. split; [exact G1|]. apply Forall_cons; [|exact G4].
intros b Hb Eb. subst b.
pose proof (Permutation_NoDup D4 (ablocks_nodup_x B ARx LAWS BLKN _ _ _ _ _ _ tc_o_AR2_xR)) as ND2.
apply (tc_nodup_disj _ _ (gxG0 cx, ATABLE) ND2 Hb).
apply in_or_app. right. apply in_or_app. right. exact (Permutation_in _ tc_o_PX_xR (in_eq _ _)).
Qed.

Lemma tc_o_done_xR : forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  asrc_at B ly2 S2 W2 m2 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
Proof.
intros i' Hi' He. destruct HG as (Hle & Hlq & _ & _ & _ & Hsrc & _).
pose proof (Hsrc i' Hi' He) as HS.
assert (Hj4 : (snd (ghj cx i') < 4)%nat) by (apply (tc_slot_lt4 cx i' HB); [lia | exact He]).
assert (Hji : snd (ghj cx i') <> oJ).
{ apply tc_o_slots_xR. left. apply (tc_slots_in (gnth cx i', ghj cx i')); [|exact He].
  apply tc_in_firstn_gps; [exact tc_o_len_xR | exact Hi' | lia]. }
assert (Hji' : Z.of_nat (snd (ghj cx i')) <> Z.of_nat oJ) by lia.
pose proof tc_o_slot_lt4_xR as HJ4.
unfold gslot in *.
apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
- intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
  + apply D9; unfold ASRC in *; lia.
  + apply (tc_o_KBt_xR b a); [|exact Hab]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len_xR Hlq ltac:(lia) Hi' He Hb).
- intros b Hb. assert (HbX : In b oX).
  { right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact (tc_done_blks cx qd i i' b tc_o_len_xR Hlq ltac:(lia) Hi' He Hb). }
  exact (proj1 (proj2 (tc_o_inX_xR b HbX))).
Qed.

Lemma tc_o_later_xR : Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly2 S2 W2 m2 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)).
Proof.
destruct HG as (_ & _ & _ & Hrly & _ & _ & Hdrs & _).
rewrite (tc_skipn_gps cx i tc_o_len_xR Hi) in Hdrs.
pose proof (Forall_inv Hdrs) as Hd0. cbn [fst snd] in Hd0. destruct (Hd0 Heof) as (_ & _ & _ & Hfd0 & _).
apply Forall_inv_tail in Hdrs.
rewrite (tc_skipn_es cx i Hi) in Hrly. pose proof Hrly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rok & (R11 & _)).
rewrite map_app in R11. cbn [map] in R11. apply NoDup_ListNoDup in R11. apply NoDup_remove_2 in R11.
pose proof tc_o_slot_lt4_xR as HJ4.
rewrite Forall_forall in Hdrs |- *. intros [ep [hp jp]] Hp He. cbn [fst snd] in He |- *.
destruct (Hdrs _ Hp He) as (Hj & HS & Hoth & Rq). cbn [fst snd] in Hj, HS, Hoth, Rq.
assert (Hji : jp <> oJ) by (apply tc_o_slots_xR; right; exact (tc_slots_in (ep, (hp, jp)) _ Hp He)).
assert (Hji' : Z.of_nat jp <> Z.of_nat oJ) by lia.
assert (Hfd : re_fd ep <> re_fd (gnth cx i)).
{ intros Heq. apply R11. apply in_or_app. right. rewrite <- Heq. apply in_map.
  unfold gps in Hp. rewrite tc_skipn_combine in Hp. exact (in_combine_l _ _ _ _ Hp). }
assert (HepIn : In ep (skipn (S i) (gxes cx))).
{ pose proof Hp as Hp'. unfold gps in Hp'. rewrite tc_skipn_combine in Hp'. exact (in_combine_l _ _ _ _ Hp'). }
assert (Hfdb : 0 <= re_fd ep < 2 ^ 31 /\ 0 <= re_fd (gnth cx i) < 2 ^ 31).
{ rewrite Forall_forall in Rok. split.
  - destruct (Rok ep ltac:(apply in_or_app; right; right; exact HepIn)) as (_ & _ & _ & _ & Hb & _). exact Hb.
  - destruct (Rok (gnth cx i) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & Hb & _). exact Hb. }
assert (Hbl : forall b, In b (asrc_blks hp) -> In b oXt).
{ intros b Hb. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  exact (tc_srcs_in (ep, (hp, jp)) _ b Hp He Hb). }
split; [exact Hj|]. split.
- apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HS).
  + intros r Hr a Ha. destruct (tc_asrc_fp_blk _ _ _ _ _ _ HS r Hr a Ha) as [Hsl | (b & Hb & Hab)].
    * apply D9; [unfold ASRC in Hsl |- *; lia | unfold gslot, ASRC in Hsl |- *; lia].
    * exact (tc_o_KBt_xR b a (Hbl b Hb) Hab).
  + intros b Hb. exact (proj1 (proj2 (tc_o_inX_xR b (or_intror (Hbl b Hb))))).
- split; [|exact Rq].
  apply (tc_aothers_kept W1 m1 W2 m2 jp (re_fd ep) oJ Hoth).
  + intros i'' Hi'' Hne a Ha. assert (Z.of_nat i'' <> Z.of_nat oJ) by lia.
    apply D9; [unfold ASRC in Ha |- *; lia | unfold gslot, ASRC in Ha |- *; lia].
  + intros _. exists (hs_fd h'), (hs_open h').
    pose proof D8 as (V1 & V2 & _ & _ & _ & _ & _ & Hopen & _). unfold gslot in V1, V2.
    split; [exact V1|]. split; [exact V2|]. right. rewrite (proj2 tc_o_fd_xR), Hfd0, !(Z.mod_small _ (2 ^ 32)) by lia.
    intros Heq. exact (Hfd (eq_sym Heq)).
Qed.

Lemma tc_o_gtopm_xR : GTOPM B RG cx i qd c2 O2 cap2 e' h' ev' LB (dr_ctl c2 (fst (ghj cx i)) ev')
  (if dr_live c2 (fst (ghj cx i)) then O2 ++ LB else O2) ocap out' ly2 S2 W2 m2.
Proof.
pose proof HG as (Hle & Hlq & Hrel & _ & _ & _ & _ & Hgs & _).
unfold GTOPM. cbv zeta. rewrite tc_o_eo_xR. cbv beta iota.
split; [exact Hi|]. split; [exact Hlq|]. split; [exact Hrel|].
split; [unfold gdrained; cbv zeta; rewrite tc_o_eo_xR; cbv beta iota; cbn [andb];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | exact D7]|].
split; [exact tc_o_arelay_xR|].
split; [exact (tc_aout_no _ _ _ _ _ _ _ _ _ _ D10)|].
split; [exact tc_o_done_xR|].
split; [intros _; exact D8|].
split; [exact tc_o_later_xR|].
split.
{ intros a Ha Hnj. apply (tl_kept_trans (gxW cx) W1 W2 (gxmem cx) m1 m2 a).
  - apply Hgs; [exact Ha|]. intros j Hj. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len_xR Hi), tc_rig_slots_app.
    apply in_or_app. left. exact Hj.
  - apply D9; [exact Ha|]. unfold gslot. apply Hnj. rewrite (tc_firstn_gps cx i tc_o_len_xR Hi), tc_rig_slots_app.
    apply in_or_app. right. rewrite tc_rig_slots_cons. cbn [fst snd]. rewrite tc_o_eo_xR. left. reflexivity. }
eapply Permutation_trans; [exact D4|].
eapply Permutation_trans.
{ apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head. exact (Permutation_sym tc_o_PX_xR). }
rewrite ?map_app, ?concat_app. cbn [map concat]. tc_perm.
Qed.
End tc_open_xR.

(* :1100 top_rep_open *)
Lemma top_rep_open_xR : stmt_top_rep_open_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold stmt_top_rep_open_xR. cbv zeta.
intros cx i qd c2 O2 cap2 out2 spent ly1 S1 Hp1 W1 m1 md1 sp1 ly2 S2 Hp2 W2 m2 md2 k2 HB Hi Heof HG HAR1 HJ Hsp HD.
unfold DRK in HD. cbv zeta in HD.
destruct HD as (e' & h' & out' & ev' & LB & rest & D1 & _ & D3 & D4 & D5 & _ & D6 & D7 & D8 & D9 & D10).
exists e', h', ev', LB, out'.
eapply tc_o_gtopm_xR; eassumption.
Qed.
End wR.

End c.
End b.
End a.
