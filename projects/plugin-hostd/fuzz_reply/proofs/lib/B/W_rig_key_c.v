(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE-B segment KEY of fuzz_reply's relay_instance_gone: the cut after the end arm
   (the representation's bytes kept through gesture_end, free and the move; GLIVE, GIN / GOUT's memory premises at the
   exit).  The footprint lemmas are BRigTop's lib/B/W_rig_top_rep.v (a working branch ed59c8899b6),
   copied and renamed.  Proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), the RIGX round on
   image B: the end arm's cut over any allocator relation ARx with its laws and the room record RP, against the cx
   file's generic Section (lib/B/W_relay_instance_gone_cx.v; its Section c copied below), as the image-A twin's
   conversion of its end arm (lib/A/W_rig_key.v, a Theorem Labs lane f4cd818e98d).  Every ARx state is read at the empty head
   set (HP0: ARh below, with Local wrappers of the laws), so the walk's journals run from [] to [] (W_journal_x.v
   ajournal_gx_x) at the kit's RIG_STK_x (= RIG_STK + 128), and GLIVE's journal starts at the entry's head set gxHp,
   which is [] by GBASE (rk_gxHp).  The journal's image clause exempts PST, so the image bytes rkc_end / rkc_end2 keep
   from the cut's state take `~ Exists (in_zr a) PST` (the relay's cells are not PST by PSTG); the ROM view at the exit
   is ajournal_gx_rom_view_x with PSTR.  A live block lies off image B's band by W_kit_xb.v blk_off_imgB_x. *)
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
(* blk_off_imgB_x: a live block off image B's band [0x10000, 0x5fc000) (W_kit_x.v's blk_off_imgP_x states the shared
   core's off_img, image A's top 0x5fb000, too weak beside B's pa_img_range) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_xb.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_key_b W_rig_key_k W_rig_key_r W_rig_key_e.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.


Lemma rkc_entry_keys_self : forall e, entry_keys e (re_keys e) = e.
Proof. intros e. destruct e. reflexivity. Qed.


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

(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state these lemmas read has the head set [], so they state their facts at ARh (= ARx at []) and each
   journal from [] to [].  rk_alb is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's
   argument order. *)
#[local] Notation ARh ly S W mem md := (ARx ly S (@nil Z) W mem md).
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
Local Definition rk_fb ly S W mem md cid pos (H : ARh ly S W mem md) :=
  frames_bounds_x SEGS B ARx LAWS ly S [] W mem md cid pos H.
Local Definition rk_boi ly S W mem md p n (H : ARh ly S W mem md) := blk_off_imgB_x B ARx LAWS IMGC BLKN ly S [] W mem md p n H.
(* the entry's head set is empty too (GBASE's afn_pre_x states ARx at gxHp) *)
Local Lemma rk_gxHp : forall cx, GBASE B ARx MT RP MMAX RG cx -> gxHp cx = [].
Proof. intros cx HB. destruct HB as ((HAR & _) & _). exact (HP0 _ _ _ _ _ _ HAR). Qed.

(* ==== The bytes the representations read (copied from lib/B/W_rig_top_rep.v, BRigTop, a working branch
   ed59c8899b6: tc_alist_fp_blk / tc_asrc_fp_blk / tc_aentry_fp_blk / tl_aout_fp / tl_kept_trans / tc_aothers_kept and
   their list helpers, renamed rkc_; this file does not import any W_rig_top) ==== *)
Lemma rkc_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. lia.
Qed.
Lemma rkc_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. lia.
Qed.
Lemma rkc_alist_fp_blk : forall ly S W m LA l lines, alist_at B ly S W m LA l lines ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (LA <= a < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|]. right.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app, rkc_recs_len in Ha.
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
Lemma rkc_asrc_fp_blk : forall ly S W m HA h, asrc_at B ly S W m HA h ->
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
  + destruct (rkc_alist_fp_blk ly S W m (HA + 16) _ false Hpend r Hr a Ha) as [H | (b & Hb & Hab)];
      [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
    unfold asrc_blks. right. apply in_or_app. left. exact Hb.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (rkc_alist_fp_blk ly S W m (HA + 64) _ true Hexp r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    * destruct (rkc_alist_fp_blk ly S W m (HA + 80) _ true Hheld r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
(* KEY's twist of tc_aentry_fp_blk: the entry's held keys replaced by ks', every one of them held before *)
Lemma rkc_aentry_fp_sub : forall ly S W m e ks', aentry_ok B ly S W m e ->
  (forall k, In k ks' -> In k (re_keys e)) -> (length ks' <= length (re_keys e))%nat ->
  forall r, In r (aentry_fp (entry_keys e ks')) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks (entry_keys e ks')) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m e ks' HE Hsub Hlen r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. cbn [entry_keys re_cap re_buf re_hp re_kh re_keys re_U re_junk] in Hr.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (re_buf e, re_cap e). split.
  + unfold aentry_blks. cbn [entry_keys re_cap re_buf]. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + cbn [fst snd]. pose proof (req_size_pos (re_cap e) ltac:(lia)). lia.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, rkc_key_ptrs_len in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Hlen. cbn [length] in Hlen. assert (length ks' = 0%nat) by lia. lia.
    * exists (re_hp e, re_kh e). split.
      -- unfold aentry_blks. cbn [entry_keys re_hp re_kh re_cap re_buf re_keys]. apply in_or_app. right. apply in_or_app. left.
         rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
      -- cbn [fst snd]. pose proof (req_size_pos (re_kh e) ltac:(lia)). unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k (Hsub k Hk)) as (Hin & _).
    exists (key_addr k, Z.of_nat (length (key_text k)) + 1). split.
    * unfold aentry_blks. cbn [entry_keys re_hp re_kh re_cap re_buf re_keys]. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    * cbn [fst snd]. pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)). lia.
Qed.
Lemma rkc_aentry_fp_blk : forall ly S W m e, aentry_ok B ly S W m e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks e) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m e HE r Hr a Ha. rewrite <- (rkc_entry_keys_self e) in Hr |- *.
exact (rkc_aentry_fp_sub ly S W m e (re_keys e) HE (fun k H => H) (le_n _) r Hr a Ha).
Qed.
Lemma rkc_aout_fp : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
  forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
  (rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
   rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
   rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
   rg_send_eintr RG <= a < rg_send_eintr RG + 1) \/ (as_errno B <= a < as_errno B + 4) \/
  (0 < cap /\ out <= a < out + cap /\ In (out, cap) (ablocks B ly S)).
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
- left; right; right; right; right; right; right; right; lia.
- right; left; lia.
- right; right. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [lia|].
  split; [lia|]. split; [lia | exact Hin].
Qed.
Lemma rkc_kept_trans : forall (W W' W'' : world SEGS) m m' m'' a,
abyte_kept W m W' m' a -> abyte_kept W' m' W'' m'' a -> abyte_kept W m W'' m'' a.
Proof.
intros W W' W'' m m' m'' a (H1 & H2) (H3 & H4). split; [rewrite H3; exact H1 | intros Hw; exact (H4 (H2 Hw))].
Qed.
Lemma rkc_aothers_kept : forall W m W' m' (j : nat) fd,
  aothers_at RG W m j fd ->
  (forall i, (i < 4)%nat -> forall a, rg_s RG + ASRC * Z.of_nat i <= a < rg_s RG + ASRC * Z.of_nat i + 8 ->
     abyte_kept W m W' m' a) ->
  aothers_at RG W' m' j fd.
Proof.
intros W m W' m' j fd HO HK i Hi Hij.
destruct (HO i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o. split; [|split; [|exact Ho]].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi); cbn in Hx; lia | exact V1].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi); cbn in Hx; lia | exact V2].
Qed.
Lemma rkc_srcs_in : forall p l b, In p l -> re_eof (fst p) = 0 -> In b (asrc_blks (fst (snd p))) -> In b (rig_srcs l).
Proof.
intros p l b Hp He Hb. unfold rig_srcs. apply in_concat. exists (asrc_blks (fst (snd p))). split; [|exact Hb].
apply in_map_iff. exists p. rewrite (proj2 (Z.eqb_eq _ _) He). split; [reflexivity | exact Hp].
Qed.
Lemma rkc_len_gps : forall cx, length (gxhs cx) = length (gxes cx) -> length (gps cx) = length (gxes cx).
Proof. intros cx H. unfold gps. rewrite length_combine, H, Nat.min_id. reflexivity. Qed.
Lemma rkc_gps_nth : forall cx i, length (gxhs cx) = length (gxes cx) ->
  nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i).
Proof. intros cx i H. unfold gps, gnth, ghj. apply combine_nth. symmetry. exact H. Qed.
Lemma rkc_done_blks : forall cx qd i i' b, length (gxhs cx) = length (gxes cx) -> length qd = i ->
  (i <= length (gxes cx))%nat -> (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  In b (asrc_blks (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  In b (gdone_srcs (firstn i (gps cx)) qd).
Proof.
intros cx qd i i' b HL Hlq Hle Hi' He Hb. unfold gdone_srcs. apply in_concat.
eexists. split; [|exact Hb]. apply in_map_iff.
exists (nth i' (combine (firstn i (gps cx)) qd)
  ((relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj), (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
split; [|apply nth_In; rewrite length_combine, length_firstn, rkc_len_gps by exact HL; lia].
rewrite combine_nth by (rewrite length_firstn, rkc_len_gps by exact HL; lia).
rewrite nth_firstn. destruct (Nat.ltb_spec i' i) as [_|Hc]; [|lia]. rewrite rkc_gps_nth by exact HL.
cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) He). reflexivity.
Qed.

(* ==== abyte_kept from the view, three ways ==== *)
(* an image byte is never hidden: its writability follows its presence *)
Lemma rkc_wr_img : forall (W W' : world SEGS) (m m' : word -> option byte) a, in_img SEGS a ->
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
Lemma rkc_abk_img : forall (W W' : world SEGS) (m m' : word -> option byte) a, in_img SEGS a ->
  aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> (apresent (w_H W) m a -> apresent (w_H W') m' a) ->
  abyte_kept W m W' m' a.
Proof. intros W W' m m' a Hi Hv Hp. split; [exact Hv|]. exact (rkc_wr_img W W' m m' a Hi Hp). Qed.
(* a byte of a block live at the end is writable at the end *)
Lemma rkc_abk_blk : forall (W W' : world SEGS) (m m' : word -> option byte) ly' S' md' p n a,
  ARh ly' S' W' m' md' -> In (p, n) (ablocks B ly' S') -> p <= a < p + req_size n ->
  aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> abyte_kept W m W' m' a.
Proof.
intros W W' m m' ly' S' md' p n a HAR Hin Ha Hv. split; [exact Hv|]. intros _.
destruct (rk_alb _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & Hpres & _ & _).
unfold arm. apply (apresent_writable SEGS). apply (Hpres a). lia.
Qed.
(* a byte seen before, off the read-only segments, is writable wherever it is seen (W4's gsl_abyte_kept) *)
Lemma rkc_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
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
Lemma rkc_abk_vis : forall (W W' : world SEGS) m m' a, 0 <= a < 2 ^ 64 ->
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> aview SEGS (w_H W) m a <> None -> ~ in_rom SEGS a ->
abyte_kept W m W' m' a.
Proof.
intros W W' m m' a Ha He Hs Hr. split; [exact He|]. intros _. unfold arm.
destruct (aview SEGS (w_H W) m a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
exact (rkc_writable_view (w_H W') m' a v Ha He Hr).
Qed.

(* ==== the move's two stores: a run that writes only nheld's 4 bytes and held[n]'s 8 keeps every other byte ==== *)
Lemma rkc_win : forall E rs H (m m' : word -> option byte) w1 w2,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
     (YP09.r_base r = Some 23%nat /\ YP09.r_wlo r = 0 /\ YP09.r_whi r = 4) \/
     (YP09.r_base r = Some 33%nat /\ YP09.r_wlo r = 0 /\ YP09.r_whi r = 8)) ->
  base_val E (Some 23%nat) = w1 -> base_val E (Some 33%nat) = w2 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (w1 <= a < w1 + 4) -> ~ (w2 <= a < w2 + 8) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' w1 w2 HF Hrs E1 E2 a Ha N1 N2. apply (aview_kept_out E rs H m m' HF a Ha).
intros (r & Hin & Hr). destruct (Hrs r Hin) as [Hw | [(Hb & Hl & Hh) | (Hb & Hl & Hh)]];
[lia | rewrite Hb, Hl, Hh, E1 in Hr; lia | rewrite Hb, Hl, Hh, E2 in Hr; lia].
Qed.
Lemma rkc_lyF : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ly_F ly' = ly_F ly.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). exact EF.
Qed.


Lemma rkc_view_some : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma rkc_zall_nth : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; [cbn in Hj; lia|].
destruct H as [Hb Hl]. destruct j as [|j]; [exact Hb|]. apply IH; [exact Hl | cbn in Hj; lia].
Qed.
Lemma rkc_zpw_nth : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
  zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; [cbn in Hj; lia|]. destruct H as [Ha Hl].
destruct i as [|i]; destruct j as [|j]; try lia.
- cbn [nth]. apply rkc_zall_nth; [exact Ha | cbn in Hj; lia].
- cbn [nth]. apply IH; [exact Hl | lia | cbn in Hj; lia].
Qed.
Ltac rkc_dj i j :=
  let D := fresh "D" in
  pose proof (rkc_zpw_nth _ i j (0, 0) HRGP ltac:(lia) ltac:(cbn [length]; lia)) as D;
  unfold zdisj in D; cbn [nth fst snd] in D.
Ltac rkc_sl Y := rkc_dj 0%nat Y; rkc_dj 1%nat Y; rkc_dj 2%nat Y; rkc_dj 3%nat Y; rkc_dj 4%nat Y; lia.
(* the relay's cells, g_lock and g_s are none of send_line's globals, and not errno *)
Lemma rkc_notSL : forall a,
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
   rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) ->
  ~ inG (G_SL B RG) a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. split.
- unfold inG, G_SL. intros HG. rewrite !Exists_cons, Exists_nil in HG. unfold in_zr in HG. cbn [fst snd] in HG.
  destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[]]]]]]];
  [rkc_sl 10%nat | rkc_sl 12%nat | rkc_sl 6%nat | rkc_sl 7%nat | rkc_sl 8%nat | rkc_sl 14%nat].
- intros HE. rkc_sl 14%nat.
Qed.
(* the output's cells are image bytes, not the runtime's, and (but errno) not errno *)
Lemma rkc_out_cell : forall a,
  (rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
   rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
   rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
   rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha.
assert (GI : forall x l, In (x, l) (G_RIG B RG) -> x <= a < x + l -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros x l Hxl Hx. destruct (HGRIG a ltac:(unfold inG; apply Exists_exists; exists (x, l); split;
    [exact Hxl | unfold in_zr; cbn [fst snd]; lia])) as (Gi & Gn & _). exact (conj Gi Gn). }
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]].
- rkc_dj 5%nat 14%nat. destruct (HRGI a ltac:(tauto)) as [H1 H2]. split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj 6%nat 14%nat. destruct (GI (rg_nout RG) 8 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj 7%nat 14%nat. destruct (GI (rg_capout RG) 8 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj 8%nat 14%nat. destruct (GI (rg_out RG) 8 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj 9%nat 14%nat. destruct (HRGI a ltac:(tauto)) as [H1 H2]. split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj 10%nat 14%nat. destruct (GI (rg_client_broken RG) 1 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj 11%nat 14%nat. destruct (HRGI a ltac:(tauto)) as [H1 H2]. split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj 12%nat 14%nat. destruct (GI (rg_send_eintr RG) 1 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
Qed.


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
#[local] Notation rk_ge := (W_rig_key_e.rk_ge B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_aout_facts := (W_rig_key_e.rk_aout_facts B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_fp_blk := (W_rig_key_e.rk_fp_blk B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sends_cap_nonneg := (W_rig_key_b.rkb_sends_cap_nonneg B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_sends_cons := (W_rig_key_b.rkb_sends_cons B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gin_end := (W_rig_key_b.rkb_gin_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rkb_gout_end := (W_rig_key_b.rkb_gout_end B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_fp_orig := (W_rig_key_e.rk_fp_orig B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).


(* ==== The cut after KEY's end arm ====
   At the exit (0x82f08 or 0x830c4), from the cut's state (ly1 S1 W1 m1: GIN), gesture_end's final state (ly2 S2 W2 m2:
   its aout_at) and the final state (ly3 S3 W3 m3: the walk's journal, the block list), and the bytes the walk keeps
   (the K hypotheses), GLIVE, the loop's slots, 80(sp) and the memory half of GIN / GOUT's premises (lib/B/W_rig_key_b.v rkb_gin_end /
   rkb_gout_end) at the exit. *)
Lemma rkc_end : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m3 md3 k3 out3,
  let kk := nth n ks (0, [], []) in
  let ks' := swap_remove (0, [], []) n ks in
  let SA := gSA cx i in
  let cap3 := ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text kk))) in
  let XGb := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx)) in
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 -> alock_at RG W1 m1 true ->
  g_lslots RG cx F W1 m1 -> val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly3 S3 [] W3 m3 md3 k3 ->
  Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3 out3 ++ gxrest cx) ->
  aout_at B RG ly2 S2 W2 m2 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (ge_no c2 (Z.of_nat (length O2)) (Z.of_nat (length (key_text kk)))) cap3 out3 ->
  apres_kept B W1 m1 W3 m3 -> apres_kept B W2 m2 W3 m3 ->
  (forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) -> ~ (SA + 48 <= a < SA + 52) ->
     ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W2) m2 a) ->
  (forall a, cap3 <> 0 -> out3 <= a < out3 + req_size cap3 -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W2) m2 a) ->
  val_mem SEGS (arm W3 m3) (SA + 48) 4 (Z.of_nat (length ks')) ->
  val_mem SEGS (arm W3 m3) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], []))) ->
  GLIVE B PST ARx RG cx F FL ly3 S3 W3 m3 md3 k3 /\ g_lslots RG cx F W3 m3 /\
  val_mem SEGS (arm W3 m3) (gsp1 cx + 80) 8 (Z.of_nat i) /\
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx) (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)) /\
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text kk)))) cap3 out3 /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) /\
  garr8 SEGS (arm W3 m3) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 m3) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m3 md3 k3 out3 kk ks' SA cap3 XGb
  HB HJ1 HPK HFR HLK HLS M80 HGN HJ3 HP3 HO2 HPK13 HPK23 KST KFR KIM KBL KO2i KO2b VNH VHN.

pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof HB as (HPRE0 & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HGN as (Hi & Hq & Hrel & Hdr & Hs & Hk & Hf & Hgk & HRLY & HOUT & HSRC & HOPEN & HDRS & HGS & HPERM & HPRE & HPSH & HBUD).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkr_entry_at ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n HAR1 HRLY Hn) as X.
cbv zeta in X. rewrite length_map, Hq in X. fold (gSA cx i) in X. fold SA in X.
destruct X as (HinT & HT16 & HT4096 & HTceil & HTend & Mhp & Mnh & AWT & Hhp0 & Hinh & Hkh & Ghp & AWH & Mslot & Hink & Gk & NZk & Lk & Hks26 & NDk).
assert (IN3 : forall b, In b XGb -> In b (ablocks B ly3 S3))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HP3)); apply in_or_app; left; exact Hb).
pose proof (rk_ablocks_nodup _ _ _ _ _ HAR3) as HND3.
pose proof (Permutation_NoDup HP3 HND3) as HNDX.

assert (KIMK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> abyte_kept W1 m1 W3 m3 a).
{ intros a Hia Ho He Hps Hg. apply (rkc_abk_img W1 W3 m1 m3 a Hia (KIM a Hia Ho He Hps Hg)). exact (HPK13 a Hia Ho He). }
(* the relay's cells are no byte of the program statics (G_RIG names g_lock and g_s; PSTG the rest) *)
assert (PSR : forall a, (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/
  rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) ->
  ~ Exists (in_zr a) PST).
{ intros a Ha. apply PSTG. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - left. unfold inG, G_RIG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - left. unfold inG, G_RIG, G_DR. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - right; left. exact Ha.
  - right; right; left. exact Ha.
  - right; right; right; left. exact Ha. }
assert (KBK : forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) -> ~ (SA + 48 <= a < SA + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8) -> abyte_kept W1 m1 W3 m3 a).
{ intros [p nb] Hb a Ha N1 N2. apply (rkc_abk_blk W1 W3 m1 m3 ly3 S3 md3 p nb a HAR3 (IN3 _ Hb) Ha). exact (KBL _ Hb a Ha N1 N2). }
assert (HSA0 : gxG0 cx <= SA) by (unfold SA, gSA, AENT; lia).
assert (HinHX : In (re_hp e1, re_kh e1) (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))))).
{ apply in_concat. exists (aentry_blks (entry_keys e1 ks')). split.
  - apply in_map. apply in_or_app. right. left. reflexivity.
  - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
    destruct (Z.eqb_spec (re_hp e1) 0); [contradiction | left; reflexivity]. }
assert (NW : forall b, In b (gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx))) -> forall a, fst b <= a < fst b + req_size (snd b) ->
  ~ (SA + 48 <= a < SA + 52) /\ ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8)).
{ intros [p nb] Hb a Ha. cbn [fst snd] in Ha.
  assert (HbX : In (p, nb) XGb) by (right; apply in_or_app; right; exact Hb).
  pose proof HNDX as HN1. unfold XGb in HN1. rewrite <- app_comm_cons in HN1. apply List.NoDup_cons_iff in HN1 as [Hnh HN2].
  assert (NT : (p, nb) <> (gxG0 cx, ATABLE)).
  { intros Heq. apply Hnh. rewrite <- Heq. apply in_or_app. left. apply in_or_app. right. exact Hb. }
  assert (NH : (p, nb) <> (re_hp e1, re_kh e1)).
  { intros Heq. rewrite <- !app_assoc in HN2. apply (rk_nodup_app_disj _ _ (re_hp e1, re_kh e1) HN2 HinHX).
    rewrite <- Heq. pose proof Hb as Hb'.
    apply in_app_or in Hb' as [Hb'|Hb']; [apply in_or_app; left; exact Hb'|]. apply in_or_app; right.
    apply in_app_or in Hb' as [Hb'|Hb']; [apply in_or_app; left; exact Hb'|]. apply in_or_app; right.
    apply in_or_app; left; exact Hb'. }
  destruct (rk_disj ly3 S3 W3 m3 md3 p nb (gxG0 cx) ATABLE HAR3 (IN3 _ HbX) (IN3 _ (or_introl eq_refl)) NT) as [D1|D1];
  destruct (rk_disj ly3 S3 W3 m3 md3 p nb (re_hp e1) (re_kh e1) HAR3 (IN3 _ HbX) (IN3 _ ltac:(right; apply in_or_app; left; exact HinHX)) NH) as [D2|D2];
  change (req_size ATABLE) with 896 in D1; pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hrk];
  unfold AENT, ATABLE in *; split; lia. }

assert (LF1 : ly_F ly1 = ly_F (gxly cx)) by exact (rkc_lyF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1).
assert (LF3 : ly_F ly3 = ly_F (gxly cx)) by exact (rkc_lyF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3).
assert (VKS : forall a n0 v, gsp1 cx <= a -> a + Z.of_nat n0 <= gsp0 cx ->
  val_mem SEGS (arm W1 m1) a n0 v -> val_mem SEGS (arm W3 m3) a n0 v).
{ intros a n0 v H1 H2 Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 m3 a n0 v); [|exact Hv].
  intros kk0 Hk0. apply KST. lia. }
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
split.
{ exists fpos, []. split; [rewrite (rk_gxHp cx HB); exact HJ3|].
  split; [exact (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROMO PSTR HROM0)|].
  split; [intros a Ha1 Ha2 Ha3 Ha4; exact (HPK13 a Ha1 Ha2 Ha3 (HPK a Ha1 Ha2 Ha3 Ha4))|].
  split.
  { split; [unfold frame_addr in *; rewrite LF3, <- LF1; exact HFa|].
    split; [unfold flag_addr in *; rewrite LF3, <- LF1; exact HFl|].
    split; [unfold arm in *; apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 m3 _ 8 _); [intros kk0 Hk0; apply KFR; left; lia | exact HFL120]|].
    split; [apply VKS; [lia | cbn; lia | exact HS8]|].
    split; [apply VKS; [lia | cbn; lia | exact HS16]|].
    split; [apply VKS; [lia | cbn; lia | exact HS112]|].
    split; [apply VKS; [lia | cbn; lia | exact HS72]|].
    intros j Hj. apply VKS; [lia | cbn; lia | exact (HSV j Hj)]. }
  apply (alock_at_kept RG W1 m1 W3 m3 true HLK). intros rr Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (rkc_notSL a ltac:(left; exact Ha)) as [Hg He].
  destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hia & Ho & _).
  exact (KIMK a Hia Ho He (PSR a ltac:(left; exact Ha)) Hg). }
split.
{ pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
  split; [|split; [|split; [|split; [|split; [|split]]]]]; (apply VKS; [lia | cbn; lia | assumption]). }
split; [apply VKS; [lia | cbn; lia | exact M80]|].

assert (Hsub : forall k, In k ks' -> In k ks).
{ intros k Hkk. apply (Permutation_in _ (Permutation_sym (relay_instance_gone_b_lem.rigl_swap_perm (0, [], []) n ks Hn))).
  right. exact Hkk. }
assert (Hlen' : (length ks' <= length (re_keys (entry_keys e1 ks)))%nat)
  by (cbn [re_keys entry_keys]; unfold ks'; rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
pose proof HRLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOK & _).
apply Forall_app in HOK as [HOKpre HOK2]. apply Forall_cons_iff in HOK2 as [HOKe HOKpost].
rewrite Forall_forall in HOKpre, HOKpost.
assert (FPB : forall rr, In rr (concat (map aentry_fp (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)))) ->
  forall a, fst rr <= a < snd rr -> exists b, In b (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)))) /\
  fst b <= a < fst b + req_size (snd b)).
{ intros rr Hrr a Ha. apply in_concat in Hrr as (fp & Hfp & Hrr). apply in_map_iff in Hfp as (e & <- & He).
  assert (HE : exists bb, In bb (aentry_blks e) /\ fst bb <= a < fst bb + req_size (snd bb)).
  { pose proof He as He0. apply in_app_or in He0 as [He0 | [He0 | He0]].
    - exact (rkc_aentry_fp_blk _ _ _ _ e (HOKpre e He0) rr Hrr a Ha).
    - subst e. exact (rkc_aentry_fp_sub _ _ _ _ (entry_keys e1 ks) ks' HOKe Hsub Hlen' rr Hrr a Ha).
    - exact (rkc_aentry_fp_blk _ _ _ _ e (HOKpost e He0) rr Hrr a Ha). }
  destruct HE as (bb & Hbb & Hab). exists bb. split; [|exact Hab].
  apply in_concat. exists (aentry_blks e). split; [apply in_map; exact He | exact Hbb]. }
split.
{ eapply (rkr_arelay_swap ly1 S1 W1 m1 md1 ly3 S3 W3 m3 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n
    (gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
     rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap2 out2 ++ gxrest cx) HAR1 RGP).
  - unfold arelay_blks. rewrite <- app_comm_cons. exact HPERM.
  - exact HRLY.
  - exact Hn.
  - intros b Hb. apply IN3. unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb].
  - intros rr Hrr a Ha N1 N2. rewrite length_map, Hq in N1. fold (gSA cx i) in N1. fold SA in N1.
    unfold arelay_fp in Hrr. cbn [In] in Hrr.
    destruct Hrr as [<- | [<- | [<- | [<- | Hrr]]]]; cbn [fst snd] in Ha.
    + destruct (rkc_notSL a ltac:(tauto)) as [Hg He]. destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (Hia & Ho & _).
      exact (KIMK a Hia Ho He (PSR a ltac:(tauto)) Hg).
    + destruct (rkc_notSL a ltac:(tauto)) as [Hg He]. destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (Hia & Ho & _).
      exact (KIMK a Hia Ho He (PSR a ltac:(tauto)) Hg).
    + destruct (rkc_notSL a ltac:(tauto)) as [Hg He]. destruct (HRGI a ltac:(tauto)) as [Hia Ho].
      exact (KIMK a Hia Ho He (PSR a ltac:(tauto)) Hg).
    + apply (KBK (gxG0 cx, ATABLE) (or_introl eq_refl) a); [cbn [fst snd]; change (req_size ATABLE) with 896; unfold ATABLE in Ha; lia | exact N1 | exact N2].
    + destruct (FPB rr Hrr a Ha) as (b & Hb & Hab).
      apply (KBK b ltac:(right; apply in_or_app; left; exact Hb) a Hab); [exact N1 | exact N2].
  - rewrite length_map, Hq. exact VNH.
  - exact VHN. }

assert (ERRG : forall a, as_errno B <= a < as_errno B + 4 -> inG (G_RIG B RG) a).
{ intros a Ha. unfold inG. apply Exists_exists. exists (as_errno B, 4).
  split; [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]. }
split.
{ rewrite rkb_ge_O_len.
  apply (aout_at_kept B RG ly2 S2 W2 m2 ly3 S3 W3 m3 _ _ _ _ _ _ HO2).
  - intros rr Hrr a Ha. destruct (rkc_aout_fp _ _ _ _ _ _ _ _ _ _ HO2 rr Hrr a Ha) as [Hc | [He | (Hc0 & Ha' & Hin)]].
    + destruct (rkc_out_cell a Hc) as (Hia & Ho & He). apply (rkc_abk_img W2 W3 m2 m3 a Hia (KO2i a Hia Ho)).
      exact (HPK23 a Hia Ho He).
    + destruct (HGRIG a (ERRG a He)) as (Hia & Ho & _).
      pose proof (pa_segs_low a Hia) as HL. rewrite C5 in HL. unfold SHADOW_OFF in HL.
      pose proof HO2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
      apply (rkc_abk_vis W2 W3 m2 m3 a); [lia | exact (KO2i a Hia Ho) | |].
      * pose proof (rkc_view_some (w_H W2) m2 (as_errno B) 4 _ (a - as_errno B) VE ltac:(cbn; lia)) as Hv.
        replace (as_errno B + (a - as_errno B)) with a in Hv by lia. exact Hv.
      * intros Hrom. destruct (HROMO a Hrom) as (Hng & _). exact (Hng (ERRG a He)).
    + pose proof (req_size_pos cap3 ltac:(lia)) as [_ Hrq].
      assert (HinO : In (out3, cap3) (ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HP3)). apply in_or_app. right. apply in_or_app. left.
        unfold aout_blks. rewrite (proj2 (Z.eqb_neq cap3 0) ltac:(lia)). left. reflexivity. }
      apply (rkc_abk_blk W2 W3 m2 m3 ly3 S3 md3 out3 cap3 a HAR3 HinO ltac:(lia)).
      exact (KO2b a ltac:(lia) ltac:(lia)).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HP3)). apply in_or_app. right. apply in_or_app. left. exact Hb. }

assert (GSK : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W3 m3 a).
{ intros a Ha. destruct (rkc_notSL a ltac:(right; left; exact Ha)) as [Hg He].
  destruct (RGIMG a ltac:(unfold rg_rng; right; right; right; right; exact Ha)) as (Hia & Ho & _).
  exact (KIMK a Hia Ho He (PSR a ltac:(right; left; exact Ha)) Hg). }
split.
{ intros i' Hi' He'. pose proof (HSRC i' Hi' He') as HS.
  assert (Hj4 : (snd (ghj cx i') < 4)%nat) by (apply (rkk_j4 cx i' HB); [lia | exact He']).
  apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 m3 _ _ HS).
  - intros rr Hrr a Ha. destruct (rkc_asrc_fp_blk _ _ _ _ _ _ HS rr Hrr a Ha) as [Hsl | (b & Hb & Hab)].
    + apply GSK. unfold gslot in Hsl. unfold ASRC in *. lia.
    + assert (HbT : In b (gdone_srcs (firstn i (gps cx)) qd)) by exact (rkc_done_blks cx qd i i' b HLEN Hq ltac:(lia) Hi' He' Hb).
      destruct (NW b ltac:(apply in_or_app; left; exact HbT) a Hab) as [N1 N2].
      exact (KBK b ltac:(right; apply in_or_app; right; apply in_or_app; left; exact HbT) a Hab N1 N2).
  - intros b Hb. apply IN3. right. apply in_or_app. right. apply in_or_app. left.
    exact (rkc_done_blks cx qd i i' b HLEN Hq ltac:(lia) Hi' He' Hb). }
split.
{ intros Ho. pose proof (HOPEN Ho) as HS.
  assert (Hj4 : (snd (ghj cx i) < 4)%nat) by (apply (rkk_j4 cx i HB); [lia | apply Z.eqb_eq; exact Ho]).
  assert (HbT : forall b, In b (asrc_blks h1) -> In b (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []))
    by (intros b Hb; rewrite Ho; exact Hb).
  apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 m3 _ _ HS).
  - intros rr Hrr a Ha. destruct (rkc_asrc_fp_blk _ _ _ _ _ _ HS rr Hrr a Ha) as [Hsl | (b & Hb & Hab)].
    + apply GSK. unfold gslot in Hsl. unfold ASRC in *. lia.
    + destruct (NW b ltac:(apply in_or_app; right; apply in_or_app; left; exact (HbT b Hb)) a Hab) as [N1 N2].
      exact (KBK b ltac:(right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact (HbT b Hb)) a Hab N1 N2).
  - intros b Hb. apply IN3. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact (HbT b Hb). }
split.
{ rewrite Forall_forall in HDRS |- *. intros [ep [hq jp]] Hp He. cbn [fst snd] in He |- *.
  destruct (HDRS _ Hp He) as (Hj & HS & Hoth & R). cbn [fst snd] in Hj, HS, Hoth, R.
  assert (Hbl : forall b, In b (asrc_blks hq) -> In b (rig_srcs (skipn (S i) (gps cx))))
    by (intros b Hb; exact (rkc_srcs_in (ep, (hq, jp)) _ b Hp He Hb)).
  split; [exact Hj|]. split.
  - apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 m3 _ _ HS).
    + intros rr Hrr a Ha. destruct (rkc_asrc_fp_blk _ _ _ _ _ _ HS rr Hrr a Ha) as [Hsl | (b & Hb & Hab)].
      * apply GSK. unfold ASRC in *. lia.
      * pose proof (Hbl b Hb) as HbT.
        destruct (NW b ltac:(apply in_or_app; right; apply in_or_app; right; exact HbT) a Hab) as [N1 N2].
        exact (KBK b ltac:(right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact HbT) a Hab N1 N2).
    + intros b Hb. apply IN3. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact (Hbl b Hb).
  - split; [|exact R]. apply (rkc_aothers_kept W1 m1 W3 m3 jp (re_fd ep) Hoth).
    intros i'' Hi'' a Ha. apply GSK. unfold ASRC in *. lia. }
split.
{ intros a Ha Hns. apply (rkc_kept_trans _ _ _ _ _ _ a (HGS a Ha Hns)). apply GSK. exact Ha. }
destruct (rkr_pre_nz cx) as (_ & _ & Lp27).
split.
{ apply (rk_garr8_kv (w_H W1) (w_H W3) m1 m3 _ _ HPRE). intros b Hb. rewrite length_app in Hb. cbn [length] in Hb.
  apply KFR. left. lia. }
{ apply (rk_garr8_kv (w_H W1) (w_H W3) m1 m3 _ _ HPSH). intros b Hb. cbn [length] in Hb. apply KFR. right. lia. }
Qed.


(* rkc_end with the bytes kept stated up to free's return (m4), the move's two stores (WIN) and its presence (PRES5)
   between m4 and the exit's memory m3 *)
Lemma rkc_end2 : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m4 m3 md3 k3 out3,
  let kk := nth n ks (0, [], []) in
  let ks' := swap_remove (0, [], []) n ks in
  let SA := gSA cx i in
  let cap3 := ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text kk))) in
  let XGb := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx)) in
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 -> alock_at RG W1 m1 true ->
  g_lslots RG cx F W1 m1 -> val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly3 S3 [] W3 m3 md3 k3 ->
  Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3 out3 ++ gxrest cx) ->
  aout_at B RG ly2 S2 W2 m2 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (ge_no c2 (Z.of_nat (length O2)) (Z.of_nat (length (key_text kk)))) cap3 out3 ->
  apres_kept B W1 m1 W3 m4 -> apres_kept B W2 m2 W3 m4 ->
  (forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W2) m2 a) ->
  (forall a, cap3 <> 0 -> out3 <= a < out3 + req_size cap3 -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W2) m2 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (SA + 48 <= a < SA + 52) -> ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8) ->
     aview SEGS (w_H W3) m3 a = aview SEGS (w_H W3) m4 a) ->
  (forall a, apresent (w_H W3) m4 a -> apresent (w_H W3) m3 a) ->
  val_mem SEGS (arm W3 m3) (SA + 48) 4 (Z.of_nat (length ks')) ->
  val_mem SEGS (arm W3 m3) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], []))) ->
  GLIVE B PST ARx RG cx F FL ly3 S3 W3 m3 md3 k3 /\ g_lslots RG cx F W3 m3 /\
  val_mem SEGS (arm W3 m3) (gsp1 cx + 80) 8 (Z.of_nat i) /\
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx) (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)) /\
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text kk)))) cap3 out3 /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) /\
  garr8 SEGS (arm W3 m3) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 m3) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m4 m3 md3 k3 out3 kk ks' SA cap3 XGb
  HB HJ1 HPK HFR HLK HLS M80 HGN HJ3 HP3 HO2 HPK14 HPK24 KST KFR KIM KBL KO2i KO2b WIN PRES VNH VHN.
pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
pose proof (rk_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : RIG_STK_x = 17232) by reflexivity. rewrite WS in Hslo. fold (gsp0 cx) in Hslo, Hshi.
assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
pose proof HGN as (_ & Hq & _ & _ & _ & Hk & _ & _ & HRLY & _).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkr_entry_at ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n HAR1 HRLY Hn) as X.
cbv zeta in X. rewrite length_map, Hq in X. fold (gSA cx i) in X. fold SA in X.
destruct X as (HinT & HT16 & HT4096 & HTceil & HTend & _ & _ & _ & Hhp0 & Hinh & Hkh & _).
destruct (rk_alb _ _ _ _ _ _ _ HAR1 HinT) as (_ & _ & _ & HTapp & _ & _ & _).
destruct (rk_alb _ _ _ _ _ _ _ HAR1 Hinh) as (_ & Hh4096 & Hhceil & Hhapp & _ & _ & _).
pose proof (rk_boi ly1 S1 W1 m1 md1 _ _ HAR1 HinT) as OT.
pose proof (rk_boi ly1 S1 W1 m1 md1 _ _ HAR1 Hinh) as OH.
change (req_size ATABLE) with 896 in *.
pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hrk].
assert (HSA0 : gxG0 cx <= SA) by (unfold SA, gSA, AENT; lia).
unfold AENT, ATABLE in HTend, HTceil.
(* the two windows lie in the table and in the held array *)
assert (W1T : forall a, SA + 48 <= a < SA + 52 -> gxG0 cx <= a < gxG0 cx + 896) by (intros; lia).
assert (W2H : forall a, re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8 -> re_hp e1 <= a < re_hp e1 + req_size (re_kh e1))
  by (intros; lia).
(* the fake frame *)
pose proof HFR as (HFa & _).
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (rk_fb _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil. rewrite HFa in HF4096, HFceil.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin HinT) as DFT.
pose proof (rk_frame_blk_apart _ _ _ _ _ _ _ _ _ HAR1 Hfin Hinh) as DFH.
change (fs_frame_bytes 1) with 128 in DFT, DFH. rewrite HFa in DFT, DFH. change (req_size ATABLE) with 896 in DFT.
assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HF8 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8u : F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
(* the output buffer at the exit, apart from both windows *)
assert (OW : forall a, cap3 <> 0 -> out3 <= a < out3 + req_size cap3 ->
  ~ (SA + 48 <= a < SA + 52) /\ ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8)).
{ intros a Hc Ha.
  pose proof (rk_ablocks_nodup _ _ _ _ _ HAR3) as HND3. pose proof (Permutation_NoDup HP3 HND3) as HNDX.
  assert (HinO : In (out3, cap3) (aout_blks cap3 out3 ++ gxrest cx))
    by (apply in_or_app; left; unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap3 0) Hc); left; reflexivity).
  assert (HinHX : In (re_hp e1, re_kh e1) XGb).
  { right. apply in_or_app. left. apply in_concat. exists (aentry_blks (entry_keys e1 ks')). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
      destruct (Z.eqb_spec (re_hp e1) 0); [contradiction | left; reflexivity]. }
  assert (I3 : forall b, In b (XGb ++ aout_blks cap3 out3 ++ gxrest cx) -> In b (ablocks B ly3 S3))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP3) Hb)).
  assert (NT : (out3, cap3) <> (gxG0 cx, ATABLE))
    by (intros Heq; apply (rk_nodup_app_disj _ _ (gxG0 cx, ATABLE) HNDX (or_introl eq_refl)); rewrite <- Heq; exact HinO).
  assert (NH : (out3, cap3) <> (re_hp e1, re_kh e1))
    by (intros Heq; apply (rk_nodup_app_disj _ _ (re_hp e1, re_kh e1) HNDX HinHX); rewrite <- Heq; exact HinO).
  destruct (rk_disj ly3 S3 W3 m3 md3 out3 cap3 (gxG0 cx) ATABLE HAR3 (I3 _ ltac:(apply in_or_app; right; exact HinO))
    (I3 _ ltac:(apply in_or_app; left; left; reflexivity)) NT) as [D1|D1];
  destruct (rk_disj ly3 S3 W3 m3 md3 out3 cap3 (re_hp e1) (re_kh e1) HAR3 (I3 _ ltac:(apply in_or_app; right; exact HinO))
    (I3 _ ltac:(apply in_or_app; left; exact HinHX)) NH) as [D2|D2];
  change (req_size ATABLE) with 896 in D1; split; intros Hw; [pose proof (W1T a Hw) | pose proof (W2H a Hw) | pose proof (W1T a Hw) | pose proof (W2H a Hw)
    | pose proof (W1T a Hw) | pose proof (W2H a Hw) | pose proof (W1T a Hw) | pose proof (W2H a Hw)]; lia. }
apply (rkc_end cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m3 md3 k3 out3 HB HJ1 HPK HFR HLK HLS M80 HGN HJ3 HP3 HO2).
- intros a Hi Ho He Hp. exact (PRES a (HPK14 a Hi Ho He Hp)).
- intros a Hi Ho He Hp. exact (PRES a (HPK24 a Hi Ho He Hp)).
- intros a Ha. rewrite WIN; [exact (KST a Ha) | lia | intros Hw; pose proof (W1T a Hw); lia | intros Hw; pose proof (W2H a Hw); lia].
- intros a Ha. pose proof Ha as Ha'. rewrite SF in Ha'. rewrite WIN; [exact (KFR a Ha) | lia | |].
  + intros Hw. pose proof (W1T a Hw). destruct Ha as [Ha | Ha]; [lia|].
    rewrite SF in Ha. exact (fshadow_not_app F 16 (gxG0 cx) 896 a ltac:(lia) ltac:(lia) HTapp ltac:(lia) ltac:(lia)).
  + intros Hw. pose proof (W2H a Hw). destruct Ha as [Ha | Ha]; [lia|].
    rewrite SF in Ha. exact (fshadow_not_app F 16 (re_hp e1) (req_size (re_kh e1)) a ltac:(lia) ltac:(lia) Hhapp ltac:(lia) ltac:(lia)).
- intros a Hi Ho He Hps Hg. pose proof (pa_img_range a Hi) as HR. pose proof (pa_segs_low a Hi) as HL. rewrite C5 in HL. unfold SHADOW_OFF in HL.
  rewrite WIN; [exact (KIM a Hi Ho He Hps Hg) | lia | intros Hw; pose proof (W1T a Hw); lia | intros Hw; pose proof (W2H a Hw); lia].
- intros b Hb a Ha N1 N2. rewrite WIN; [exact (KBL b Hb a Ha) | | exact N1 | exact N2].
  pose proof (Permutation_in _ (Permutation_sym HP3) (in_or_app _ _ _ (or_introl Hb))) as Hb3. destruct b as [p nb].
  destruct (rk_alb _ _ _ _ _ _ _ HAR3 Hb3) as (_ & Hp4 & Hpc & _). cbn [fst snd] in Ha. lia.
- intros a Hi Ho. pose proof (pa_img_range a Hi) as HR. pose proof (pa_segs_low a Hi) as HL. rewrite C5 in HL. unfold SHADOW_OFF in HL.
  rewrite WIN; [exact (KO2i a Hi Ho) | lia | intros Hw; pose proof (W1T a Hw); lia | intros Hw; pose proof (W2H a Hw); lia].
- intros a Hc Ha. destruct (OW a Hc Ha) as [N1 N2].
  assert (Hb3 : In (out3, cap3) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP3)). apply in_or_app. right. apply in_or_app. left.
    unfold aout_blks. destruct (Z.eqb_spec cap3 0) as [E0|E0]; [exfalso; exact (Hc E0) | left; reflexivity]. }
  destruct (rk_alb _ _ _ _ _ _ _ HAR3 Hb3) as (_ & Hp4 & Hpc & _). unfold cap3, kk in Hpc.
  rewrite WIN; [exact (KO2b a Hc Ha) | lia | exact N1 | exact N2].
- exact VNH.
- exact VHN.
Qed.


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the end arm's journal readers at a world relation R.  The strict lemmas above take every Section
   hypothesis (Default Proof Using "All"), the strict AFREE / DRAIN / GE / ALLOC_TAIL included, so this Section copies
   each of them as X_xR (same statement and proof) under a Default Proof Using that leaves those out.  The lemmas that
   read a journal are lifted: ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the journal lemmas ->
   their _xR twins (W_journal_x.v), GLIVE -> the cx file's GLIVE_xR.  The hypothesis list is the cx file's Section wR, verbatim. ---- *)
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
#[local] Notation rk_ge_xR := (W_rig_key_e.rk_ge_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_aout_facts_xR := (W_rig_key_e.rk_aout_facts_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_fp_blk_xR := (W_rig_key_e.rk_fp_blk_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sends_cap_nonneg_xR := (W_rig_key_b.rkb_sends_cap_nonneg_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_sends_cons_xR := (W_rig_key_b.rkb_sends_cons_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gin_end_xR := (W_rig_key_b.rkb_gin_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rkb_gout_end_xR := (W_rig_key_b.rkb_gout_end_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_fp_orig_xR := (W_rig_key_e.rk_fp_orig_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state these lemmas read has the head set [], so they state their facts at ARh (= ARx at []) and each
   journal from [] to [].  rk_alb_xR is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's
   argument order. *)
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

(* ==== The bytes the representations read (copied from lib/B/W_rig_top_rep.v, BRigTop, a working branch
   ed59c8899b6: tc_alist_fp_blk / tc_asrc_fp_blk / tc_aentry_fp_blk / tl_aout_fp / tl_kept_trans / tc_aothers_kept and
   their list helpers, renamed rkc_; this file does not import any W_rig_top) ==== *)
Lemma rkc_recs_len_xR : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. lia.
Qed.
Lemma rkc_key_ptrs_len_xR : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. lia.
Qed.
Lemma rkc_alist_fp_blk_xR : forall ly S W m LA l lines, alist_at B ly S W m LA l lines ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (LA <= a < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|]. right.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app, rkc_recs_len_xR in Ha.
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
Lemma rkc_asrc_fp_blk_xR : forall ly S W m HA h, asrc_at B ly S W m HA h ->
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
  + destruct (rkc_alist_fp_blk_xR ly S W m (HA + 16) _ false Hpend r Hr a Ha) as [H | (b & Hb & Hab)];
      [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
    unfold asrc_blks. right. apply in_or_app. left. exact Hb.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (rkc_alist_fp_blk_xR ly S W m (HA + 64) _ true Hexp r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    * destruct (rkc_alist_fp_blk_xR ly S W m (HA + 80) _ true Hheld r Hr a Ha) as [H | (b & Hb & Hab)];
        [left; unfold ASRC; lia | right; exists b; split; [|exact Hab]].
      unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
(* KEY's twist of tc_aentry_fp_blk: the entry's held keys replaced by ks', every one of them held before *)
Lemma rkc_aentry_fp_sub_xR : forall ly S W m e ks', aentry_ok B ly S W m e ->
  (forall k, In k ks' -> In k (re_keys e)) -> (length ks' <= length (re_keys e))%nat ->
  forall r, In r (aentry_fp (entry_keys e ks')) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks (entry_keys e ks')) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m e ks' HE Hsub Hlen r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. cbn [entry_keys re_cap re_buf re_hp re_kh re_keys re_U re_junk] in Hr.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  exists (re_buf e, re_cap e). split.
  + unfold aentry_blks. cbn [entry_keys re_cap re_buf]. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + cbn [fst snd]. pose proof (req_size_pos (re_cap e) ltac:(lia)). lia.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, rkc_key_ptrs_len_xR in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Hlen. cbn [length] in Hlen. assert (length ks' = 0%nat) by lia. lia.
    * exists (re_hp e, re_kh e). split.
      -- unfold aentry_blks. cbn [entry_keys re_hp re_kh re_cap re_buf re_keys]. apply in_or_app. right. apply in_or_app. left.
         rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
      -- cbn [fst snd]. pose proof (req_size_pos (re_kh e) ltac:(lia)). unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k (Hsub k Hk)) as (Hin & _).
    exists (key_addr k, Z.of_nat (length (key_text k)) + 1). split.
    * unfold aentry_blks. cbn [entry_keys re_hp re_kh re_cap re_buf re_keys]. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    * cbn [fst snd]. pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)). lia.
Qed.
Lemma rkc_aentry_fp_blk_xR : forall ly S W m e, aentry_ok B ly S W m e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists b, In b (aentry_blks e) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W m e HE r Hr a Ha. rewrite <- (rkc_entry_keys_self e) in Hr |- *.
exact (rkc_aentry_fp_sub_xR ly S W m e (re_keys e) HE (fun k H => H) (le_n _) r Hr a Ha).
Qed.
Lemma rkc_aout_fp_xR : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
  forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
  (rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
   rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
   rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
   rg_send_eintr RG <= a < rg_send_eintr RG + 1) \/ (as_errno B <= a < as_errno B + 4) \/
  (0 < cap /\ out <= a < out + cap /\ In (out, cap) (ablocks B ly S)).
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
- left; right; right; right; right; right; right; right; lia.
- right; left; lia.
- right; right. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [lia|].
  split; [lia|]. split; [lia | exact Hin].
Qed.
Lemma rkc_kept_trans_xR : forall (W W' W'' : world SEGS) m m' m'' a,
abyte_kept W m W' m' a -> abyte_kept W' m' W'' m'' a -> abyte_kept W m W'' m'' a.
Proof.
intros W W' W'' m m' m'' a (H1 & H2) (H3 & H4). split; [rewrite H3; exact H1 | intros Hw; exact (H4 (H2 Hw))].
Qed.
Lemma rkc_aothers_kept_xR : forall W m W' m' (j : nat) fd,
  aothers_at RG W m j fd ->
  (forall i, (i < 4)%nat -> forall a, rg_s RG + ASRC * Z.of_nat i <= a < rg_s RG + ASRC * Z.of_nat i + 8 ->
     abyte_kept W m W' m' a) ->
  aothers_at RG W' m' j fd.
Proof.
intros W m W' m' j fd HO HK i Hi Hij.
destruct (HO i Hi Hij) as (f & o & V1 & V2 & Ho). exists f, o. split; [|split; [|exact Ho]].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi); cbn in Hx; lia | exact V1].
- apply (akept_vm W m); [intros x Hx; apply (HK i Hi); cbn in Hx; lia | exact V2].
Qed.
Lemma rkc_srcs_in_xR : forall p l b, In p l -> re_eof (fst p) = 0 -> In b (asrc_blks (fst (snd p))) -> In b (rig_srcs l).
Proof.
intros p l b Hp He Hb. unfold rig_srcs. apply in_concat. exists (asrc_blks (fst (snd p))). split; [|exact Hb].
apply in_map_iff. exists p. rewrite (proj2 (Z.eqb_eq _ _) He). split; [reflexivity | exact Hp].
Qed.
Lemma rkc_len_gps_xR : forall cx, length (gxhs cx) = length (gxes cx) -> length (gps cx) = length (gxes cx).
Proof. intros cx H. unfold gps. rewrite length_combine, H, Nat.min_id. reflexivity. Qed.
Lemma rkc_gps_nth_xR : forall cx i, length (gxhs cx) = length (gxes cx) ->
  nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i).
Proof. intros cx i H. unfold gps, gnth, ghj. apply combine_nth. symmetry. exact H. Qed.
Lemma rkc_done_blks_xR : forall cx qd i i' b, length (gxhs cx) = length (gxes cx) -> length qd = i ->
  (i <= length (gxes cx))%nat -> (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
  In b (asrc_blks (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  In b (gdone_srcs (firstn i (gps cx)) qd).
Proof.
intros cx qd i i' b HL Hlq Hle Hi' He Hb. unfold gdone_srcs. apply in_concat.
eexists. split; [|exact Hb]. apply in_map_iff.
exists (nth i' (combine (firstn i (gps cx)) qd)
  ((relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj), (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj))).
split; [|apply nth_In; rewrite length_combine, length_firstn, rkc_len_gps_xR by exact HL; lia].
rewrite combine_nth by (rewrite length_firstn, rkc_len_gps_xR by exact HL; lia).
rewrite nth_firstn. destruct (Nat.ltb_spec i' i) as [_|Hc]; [|lia]. rewrite rkc_gps_nth_xR by exact HL.
cbn [fst snd]. rewrite (proj2 (Z.eqb_eq _ _) He). reflexivity.
Qed.

(* ==== abyte_kept from the view, three ways ==== *)
(* an image byte is never hidden: its writability follows its presence *)
Lemma rkc_wr_img_xR : forall (W W' : world SEGS) (m m' : word -> option byte) a, in_img SEGS a ->
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
Lemma rkc_abk_img_xR : forall (W W' : world SEGS) (m m' : word -> option byte) a, in_img SEGS a ->
  aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> (apresent (w_H W) m a -> apresent (w_H W') m' a) ->
  abyte_kept W m W' m' a.
Proof. intros W W' m m' a Hi Hv Hp. split; [exact Hv|]. exact (rkc_wr_img_xR W W' m m' a Hi Hp). Qed.
(* a byte of a block live at the end is writable at the end *)
Lemma rkc_abk_blk_xR : forall (W W' : world SEGS) (m m' : word -> option byte) ly' S' md' p n a,
  ARh ly' S' W' m' md' -> In (p, n) (ablocks B ly' S') -> p <= a < p + req_size n ->
  aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> abyte_kept W m W' m' a.
Proof.
intros W W' m m' ly' S' md' p n a HAR Hin Ha Hv. split; [exact Hv|]. intros _.
destruct (rk_alb_xR _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & Hpres & _ & _).
unfold arm. apply (apresent_writable SEGS). apply (Hpres a). lia.
Qed.
(* a byte seen before, off the read-only segments, is writable wherever it is seen (W4's gsl_abyte_kept) *)
Lemma rkc_writable_view_xR : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
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
Lemma rkc_abk_vis_xR : forall (W W' : world SEGS) m m' a, 0 <= a < 2 ^ 64 ->
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> aview SEGS (w_H W) m a <> None -> ~ in_rom SEGS a ->
abyte_kept W m W' m' a.
Proof.
intros W W' m m' a Ha He Hs Hr. split; [exact He|]. intros _. unfold arm.
destruct (aview SEGS (w_H W) m a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
exact (rkc_writable_view_xR (w_H W') m' a v Ha He Hr).
Qed.

(* ==== the move's two stores: a run that writes only nheld's 4 bytes and held[n]'s 8 keeps every other byte ==== *)
Lemma rkc_win_xR : forall E rs H (m m' : word -> option byte) w1 w2,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
     (YP09.r_base r = Some 23%nat /\ YP09.r_wlo r = 0 /\ YP09.r_whi r = 4) \/
     (YP09.r_base r = Some 33%nat /\ YP09.r_wlo r = 0 /\ YP09.r_whi r = 8)) ->
  base_val E (Some 23%nat) = w1 -> base_val E (Some 33%nat) = w2 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (w1 <= a < w1 + 4) -> ~ (w2 <= a < w2 + 8) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' w1 w2 HF Hrs E1 E2 a Ha N1 N2. apply (aview_kept_out E rs H m m' HF a Ha).
intros (r & Hin & Hr). destruct (Hrs r Hin) as [Hw | [(Hb & Hl & Hh) | (Hb & Hl & Hh)]];
[lia | rewrite Hb, Hl, Hh, E1 in Hr; lia | rewrite Hb, Hl, Hh, E2 in Hr; lia].
Qed.
Lemma rkc_lyF_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ly_F ly' = ly_F ly.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). exact EF.
Qed.


Lemma rkc_view_some_xR : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma rkc_zall_nth_xR : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; [cbn in Hj; lia|].
destruct H as [Hb Hl]. destruct j as [|j]; [exact Hb|]. apply IH; [exact Hl | cbn in Hj; lia].
Qed.
Lemma rkc_zpw_nth_xR : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
  zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; [cbn in Hj; lia|]. destruct H as [Ha Hl].
destruct i as [|i]; destruct j as [|j]; try lia.
- cbn [nth]. apply rkc_zall_nth_xR; [exact Ha | cbn in Hj; lia].
- cbn [nth]. apply IH; [exact Hl | lia | cbn in Hj; lia].
Qed.
Ltac rkc_dj_xR i j :=
  let D := fresh "D" in
  pose proof (rkc_zpw_nth_xR _ i j (0, 0) HRGP ltac:(lia) ltac:(cbn [length]; lia)) as D;
  unfold zdisj in D; cbn [nth fst snd] in D.
Ltac rkc_sl_xR Y := rkc_dj_xR 0%nat Y; rkc_dj_xR 1%nat Y; rkc_dj_xR 2%nat Y; rkc_dj_xR 3%nat Y; rkc_dj_xR 4%nat Y; lia.
(* the relay's cells, g_lock and g_s are none of send_line's globals, and not errno *)
Lemma rkc_notSL_xR : forall a,
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
   rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) ->
  ~ inG (G_SL B RG) a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. split.
- unfold inG, G_SL. intros HG. rewrite !Exists_cons, Exists_nil in HG. unfold in_zr in HG. cbn [fst snd] in HG.
  destruct HG as [HG|[HG|[HG|[HG|[HG|[HG|[]]]]]]];
  [rkc_sl_xR 10%nat | rkc_sl_xR 12%nat | rkc_sl_xR 6%nat | rkc_sl_xR 7%nat | rkc_sl_xR 8%nat | rkc_sl_xR 14%nat].
- intros HE. rkc_sl_xR 14%nat.
Qed.
(* the output's cells are image bytes, not the runtime's, and (but errno) not errno *)
Lemma rkc_out_cell_xR : forall a,
  (rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
   rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
   rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
   rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha.
assert (GI : forall x l, In (x, l) (G_RIG B RG) -> x <= a < x + l -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros x l Hxl Hx. destruct (HGRIG a ltac:(unfold inG; apply Exists_exists; exists (x, l); split;
    [exact Hxl | unfold in_zr; cbn [fst snd]; lia])) as (Gi & Gn & _). exact (conj Gi Gn). }
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]].
- rkc_dj_xR 5%nat 14%nat. destruct (HRGI a ltac:(tauto)) as [H1 H2]. split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj_xR 6%nat 14%nat. destruct (GI (rg_nout RG) 8 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj_xR 7%nat 14%nat. destruct (GI (rg_capout RG) 8 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj_xR 8%nat 14%nat. destruct (GI (rg_out RG) 8 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj_xR 9%nat 14%nat. destruct (HRGI a ltac:(tauto)) as [H1 H2]. split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj_xR 10%nat 14%nat. destruct (GI (rg_client_broken RG) 1 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj_xR 11%nat 14%nat. destruct (HRGI a ltac:(tauto)) as [H1 H2]. split; [exact H1 | split; [exact H2 | lia]].
- rkc_dj_xR 12%nat 14%nat. destruct (GI (rg_send_eintr RG) 1 ltac:(unfold G_RIG, G_DR, G_SL; cbn [In]; tauto) Ha) as [H1 H2].
  split; [exact H1 | split; [exact H2 | lia]].
Qed.




(* ==== The cut after KEY's end arm ====
   At the exit (0x82f08 or 0x830c4), from the cut's state (ly1 S1 W1 m1: GIN), gesture_end's final state (ly2 S2 W2 m2:
   its aout_at) and the final state (ly3 S3 W3 m3: the walk's journal, the block list), and the bytes the walk keeps
   (the K hypotheses), GLIVE, the loop's slots, 80(sp) and the memory half of GIN / GOUT's premises (lib/B/W_rig_key_b.v rkb_gin_end_xR /
   rkb_gout_end_xR) at the exit. *)
Lemma rkc_end_xR : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m3 md3 k3 out3,
  let kk := nth n ks (0, [], []) in
  let ks' := swap_remove (0, [], []) n ks in
  let SA := gSA cx i in
  let cap3 := ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text kk))) in
  let XGb := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx)) in
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 -> alock_at RG W1 m1 true ->
  g_lslots RG cx F W1 m1 -> val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly3 S3 [] W3 m3 md3 k3 ->
  Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3 out3 ++ gxrest cx) ->
  aout_at B RG ly2 S2 W2 m2 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (ge_no c2 (Z.of_nat (length O2)) (Z.of_nat (length (key_text kk)))) cap3 out3 ->
  apres_kept B W1 m1 W3 m3 -> apres_kept B W2 m2 W3 m3 ->
  (forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) -> ~ (SA + 48 <= a < SA + 52) ->
     ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8) -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W2) m2 a) ->
  (forall a, cap3 <> 0 -> out3 <= a < out3 + req_size cap3 -> aview SEGS (w_H W3) m3 a = aview SEGS (w_H W2) m2 a) ->
  val_mem SEGS (arm W3 m3) (SA + 48) 4 (Z.of_nat (length ks')) ->
  val_mem SEGS (arm W3 m3) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], []))) ->
  GLIVE_xR B PST ARx RG R cx F FL ly3 S3 W3 m3 md3 k3 /\ g_lslots RG cx F W3 m3 /\
  val_mem SEGS (arm W3 m3) (gsp1 cx + 80) 8 (Z.of_nat i) /\
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx) (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)) /\
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text kk)))) cap3 out3 /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) /\
  garr8 SEGS (arm W3 m3) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 m3) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m3 md3 k3 out3 kk ks' SA cap3 XGb
  HB HJ1 HPK HFR HLK HLS M80 HGN HJ3 HP3 HO2 HPK13 HPK23 KST KFR KIM KBL KO2i KO2b VNH VHN.

pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof HB as (HPRE0 & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HGN as (Hi & Hq & Hrel & Hdr & Hs & Hk & Hf & Hgk & HRLY & HOUT & HSRC & HOPEN & HDRS & HGS & HPERM & HPRE & HPSH & HBUD).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkr_entry_at_xR ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n HAR1 HRLY Hn) as X.
cbv zeta in X. rewrite length_map, Hq in X. fold (gSA cx i) in X. fold SA in X.
destruct X as (HinT & HT16 & HT4096 & HTceil & HTend & Mhp & Mnh & AWT & Hhp0 & Hinh & Hkh & Ghp & AWH & Mslot & Hink & Gk & NZk & Lk & Hks26 & NDk).
assert (IN3 : forall b, In b XGb -> In b (ablocks B ly3 S3))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HP3)); apply in_or_app; left; exact Hb).
pose proof (rk_ablocks_nodup_xR _ _ _ _ _ HAR3) as HND3.
pose proof (Permutation_NoDup HP3 HND3) as HNDX.

assert (KIMK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> abyte_kept W1 m1 W3 m3 a).
{ intros a Hia Ho He Hps Hg. apply (rkc_abk_img_xR W1 W3 m1 m3 a Hia (KIM a Hia Ho He Hps Hg)). exact (HPK13 a Hia Ho He). }
(* the relay's cells are no byte of the program statics (G_RIG names g_lock and g_s; PSTG the rest) *)
assert (PSR : forall a, (rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/
  rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) ->
  ~ Exists (in_zr a) PST).
{ intros a Ha. apply PSTG. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - left. unfold inG, G_RIG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - left. unfold inG, G_RIG, G_DR. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - right; left. exact Ha.
  - right; right; left. exact Ha.
  - right; right; right; left. exact Ha. }
assert (KBK : forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) -> ~ (SA + 48 <= a < SA + 52) ->
  ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8) -> abyte_kept W1 m1 W3 m3 a).
{ intros [p nb] Hb a Ha N1 N2. apply (rkc_abk_blk_xR W1 W3 m1 m3 ly3 S3 md3 p nb a HAR3 (IN3 _ Hb) Ha). exact (KBL _ Hb a Ha N1 N2). }
assert (HSA0 : gxG0 cx <= SA) by (unfold SA, gSA, AENT; lia).
assert (HinHX : In (re_hp e1, re_kh e1) (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))))).
{ apply in_concat. exists (aentry_blks (entry_keys e1 ks')). split.
  - apply in_map. apply in_or_app. right. left. reflexivity.
  - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
    destruct (Z.eqb_spec (re_hp e1) 0); [contradiction | left; reflexivity]. }
assert (NW : forall b, In b (gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx))) -> forall a, fst b <= a < fst b + req_size (snd b) ->
  ~ (SA + 48 <= a < SA + 52) /\ ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8)).
{ intros [p nb] Hb a Ha. cbn [fst snd] in Ha.
  assert (HbX : In (p, nb) XGb) by (right; apply in_or_app; right; exact Hb).
  pose proof HNDX as HN1. unfold XGb in HN1. rewrite <- app_comm_cons in HN1. apply List.NoDup_cons_iff in HN1 as [Hnh HN2].
  assert (NT : (p, nb) <> (gxG0 cx, ATABLE)).
  { intros Heq. apply Hnh. rewrite <- Heq. apply in_or_app. left. apply in_or_app. right. exact Hb. }
  assert (NH : (p, nb) <> (re_hp e1, re_kh e1)).
  { intros Heq. rewrite <- !app_assoc in HN2. apply (rk_nodup_app_disj_xR _ _ (re_hp e1, re_kh e1) HN2 HinHX).
    rewrite <- Heq. pose proof Hb as Hb'.
    apply in_app_or in Hb' as [Hb'|Hb']; [apply in_or_app; left; exact Hb'|]. apply in_or_app; right.
    apply in_app_or in Hb' as [Hb'|Hb']; [apply in_or_app; left; exact Hb'|]. apply in_or_app; right.
    apply in_or_app; left; exact Hb'. }
  destruct (rk_disj_xR ly3 S3 W3 m3 md3 p nb (gxG0 cx) ATABLE HAR3 (IN3 _ HbX) (IN3 _ (or_introl eq_refl)) NT) as [D1|D1];
  destruct (rk_disj_xR ly3 S3 W3 m3 md3 p nb (re_hp e1) (re_kh e1) HAR3 (IN3 _ HbX) (IN3 _ ltac:(right; apply in_or_app; left; exact HinHX)) NH) as [D2|D2];
  change (req_size ATABLE) with 896 in D1; pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hrk];
  unfold AENT, ATABLE in *; split; lia. }

assert (LF1 : ly_F ly1 = ly_F (gxly cx)) by exact (rkc_lyF_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1).
assert (LF3 : ly_F ly3 = ly_F (gxly cx)) by exact (rkc_lyF_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3).
assert (VKS : forall a n0 v, gsp1 cx <= a -> a + Z.of_nat n0 <= gsp0 cx ->
  val_mem SEGS (arm W1 m1) a n0 v -> val_mem SEGS (arm W3 m3) a n0 v).
{ intros a n0 v H1 H2 Hv. unfold arm in *. apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 m3 a n0 v); [|exact Hv].
  intros kk0 Hk0. apply KST. lia. }
pose proof HFR as (HFa & HFl & HFL120 & HS8 & HS16 & HS112 & HS72 & HSV).
assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
split.
{ exists fpos, []. split; [rewrite (rk_gxHp_xR cx HB); exact HJ3|].
  split; [exact (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROMO PSTR HROM0)|].
  split; [intros a Ha1 Ha2 Ha3 Ha4; exact (HPK13 a Ha1 Ha2 Ha3 (HPK a Ha1 Ha2 Ha3 Ha4))|].
  split.
  { split; [unfold frame_addr in *; rewrite LF3, <- LF1; exact HFa|].
    split; [unfold flag_addr in *; rewrite LF3, <- LF1; exact HFl|].
    split; [unfold arm in *; apply (val_mem_kept SEGS (w_H W1) (w_H W3) m1 m3 _ 8 _); [intros kk0 Hk0; apply KFR; left; lia | exact HFL120]|].
    split; [apply VKS; [lia | cbn; lia | exact HS8]|].
    split; [apply VKS; [lia | cbn; lia | exact HS16]|].
    split; [apply VKS; [lia | cbn; lia | exact HS112]|].
    split; [apply VKS; [lia | cbn; lia | exact HS72]|].
    intros j Hj. apply VKS; [lia | cbn; lia | exact (HSV j Hj)]. }
  apply (alock_at_kept RG W1 m1 W3 m3 true HLK). intros rr Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (rkc_notSL_xR a ltac:(left; exact Ha)) as [Hg He].
  destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hia & Ho & _).
  exact (KIMK a Hia Ho He (PSR a ltac:(left; exact Ha)) Hg). }
split.
{ pose proof HLS as (L24 & L32 & L40 & L48 & L56 & L64 & L88).
  split; [|split; [|split; [|split; [|split; [|split]]]]]; (apply VKS; [lia | cbn; lia | assumption]). }
split; [apply VKS; [lia | cbn; lia | exact M80]|].

assert (Hsub : forall k, In k ks' -> In k ks).
{ intros k Hkk. apply (Permutation_in _ (Permutation_sym (relay_instance_gone_b_lem.rigl_swap_perm (0, [], []) n ks Hn))).
  right. exact Hkk. }
assert (Hlen' : (length ks' <= length (re_keys (entry_keys e1 ks)))%nat)
  by (cbn [re_keys entry_keys]; unfold ks'; rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
pose proof HRLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOK & _).
apply Forall_app in HOK as [HOKpre HOK2]. apply Forall_cons_iff in HOK2 as [HOKe HOKpost].
rewrite Forall_forall in HOKpre, HOKpost.
assert (FPB : forall rr, In rr (concat (map aentry_fp (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)))) ->
  forall a, fst rr <= a < snd rr -> exists b, In b (concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)))) /\
  fst b <= a < fst b + req_size (snd b)).
{ intros rr Hrr a Ha. apply in_concat in Hrr as (fp & Hfp & Hrr). apply in_map_iff in Hfp as (e & <- & He).
  assert (HE : exists bb, In bb (aentry_blks e) /\ fst bb <= a < fst bb + req_size (snd bb)).
  { pose proof He as He0. apply in_app_or in He0 as [He0 | [He0 | He0]].
    - exact (rkc_aentry_fp_blk_xR _ _ _ _ e (HOKpre e He0) rr Hrr a Ha).
    - subst e. exact (rkc_aentry_fp_sub_xR _ _ _ _ (entry_keys e1 ks) ks' HOKe Hsub Hlen' rr Hrr a Ha).
    - exact (rkc_aentry_fp_blk_xR _ _ _ _ e (HOKpost e He0) rr Hrr a Ha). }
  destruct HE as (bb & Hbb & Hab). exists bb. split; [|exact Hab].
  apply in_concat. exists (aentry_blks e). split; [apply in_map; exact He | exact Hbb]. }
split.
{ eapply (rkr_arelay_swap_xR ly1 S1 W1 m1 md1 ly3 S3 W3 m3 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n
    (gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
     rig_srcs (skipn (S i) (gps cx)) ++ aout_blks cap2 out2 ++ gxrest cx) HAR1 RGP).
  - unfold arelay_blks. rewrite <- app_comm_cons. exact HPERM.
  - exact HRLY.
  - exact Hn.
  - intros b Hb. apply IN3. unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb].
  - intros rr Hrr a Ha N1 N2. rewrite length_map, Hq in N1. fold (gSA cx i) in N1. fold SA in N1.
    unfold arelay_fp in Hrr. cbn [In] in Hrr.
    destruct Hrr as [<- | [<- | [<- | [<- | Hrr]]]]; cbn [fst snd] in Ha.
    + destruct (rkc_notSL_xR a ltac:(tauto)) as [Hg He]. destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (Hia & Ho & _).
      exact (KIMK a Hia Ho He (PSR a ltac:(tauto)) Hg).
    + destruct (rkc_notSL_xR a ltac:(tauto)) as [Hg He]. destruct (RGIMG a ltac:(unfold rg_rng; tauto)) as (Hia & Ho & _).
      exact (KIMK a Hia Ho He (PSR a ltac:(tauto)) Hg).
    + destruct (rkc_notSL_xR a ltac:(tauto)) as [Hg He]. destruct (HRGI a ltac:(tauto)) as [Hia Ho].
      exact (KIMK a Hia Ho He (PSR a ltac:(tauto)) Hg).
    + apply (KBK (gxG0 cx, ATABLE) (or_introl eq_refl) a); [cbn [fst snd]; change (req_size ATABLE) with 896; unfold ATABLE in Ha; lia | exact N1 | exact N2].
    + destruct (FPB rr Hrr a Ha) as (b & Hb & Hab).
      apply (KBK b ltac:(right; apply in_or_app; left; exact Hb) a Hab); [exact N1 | exact N2].
  - rewrite length_map, Hq. exact VNH.
  - exact VHN. }

assert (ERRG : forall a, as_errno B <= a < as_errno B + 4 -> inG (G_RIG B RG) a).
{ intros a Ha. unfold inG. apply Exists_exists. exists (as_errno B, 4).
  split; [unfold G_RIG, G_DR, G_SL; cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]. }
split.
{ rewrite rkb_ge_O_len_xR.
  apply (aout_at_kept B RG ly2 S2 W2 m2 ly3 S3 W3 m3 _ _ _ _ _ _ HO2).
  - intros rr Hrr a Ha. destruct (rkc_aout_fp_xR _ _ _ _ _ _ _ _ _ _ HO2 rr Hrr a Ha) as [Hc | [He | (Hc0 & Ha' & Hin)]].
    + destruct (rkc_out_cell_xR a Hc) as (Hia & Ho & He). apply (rkc_abk_img_xR W2 W3 m2 m3 a Hia (KO2i a Hia Ho)).
      exact (HPK23 a Hia Ho He).
    + destruct (HGRIG a (ERRG a He)) as (Hia & Ho & _).
      pose proof (pa_segs_low a Hia) as HL. rewrite C5 in HL. unfold SHADOW_OFF in HL.
      pose proof HO2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
      apply (rkc_abk_vis_xR W2 W3 m2 m3 a); [lia | exact (KO2i a Hia Ho) | |].
      * pose proof (rkc_view_some_xR (w_H W2) m2 (as_errno B) 4 _ (a - as_errno B) VE ltac:(cbn; lia)) as Hv.
        replace (as_errno B + (a - as_errno B)) with a in Hv by lia. exact Hv.
      * intros Hrom. destruct (HROMO a Hrom) as (Hng & _). exact (Hng (ERRG a He)).
    + pose proof (req_size_pos cap3 ltac:(lia)) as [_ Hrq].
      assert (HinO : In (out3, cap3) (ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HP3)). apply in_or_app. right. apply in_or_app. left.
        unfold aout_blks. rewrite (proj2 (Z.eqb_neq cap3 0) ltac:(lia)). left. reflexivity. }
      apply (rkc_abk_blk_xR W2 W3 m2 m3 ly3 S3 md3 out3 cap3 a HAR3 HinO ltac:(lia)).
      exact (KO2b a ltac:(lia) ltac:(lia)).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HP3)). apply in_or_app. right. apply in_or_app. left. exact Hb. }

assert (GSK : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W3 m3 a).
{ intros a Ha. destruct (rkc_notSL_xR a ltac:(right; left; exact Ha)) as [Hg He].
  destruct (RGIMG a ltac:(unfold rg_rng; right; right; right; right; exact Ha)) as (Hia & Ho & _).
  exact (KIMK a Hia Ho He (PSR a ltac:(right; left; exact Ha)) Hg). }
split.
{ intros i' Hi' He'. pose proof (HSRC i' Hi' He') as HS.
  assert (Hj4 : (snd (ghj cx i') < 4)%nat) by (apply (rkk_j4_xR cx i' HB); [lia | exact He']).
  apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 m3 _ _ HS).
  - intros rr Hrr a Ha. destruct (rkc_asrc_fp_blk_xR _ _ _ _ _ _ HS rr Hrr a Ha) as [Hsl | (b & Hb & Hab)].
    + apply GSK. unfold gslot in Hsl. unfold ASRC in *. lia.
    + assert (HbT : In b (gdone_srcs (firstn i (gps cx)) qd)) by exact (rkc_done_blks_xR cx qd i i' b HLEN Hq ltac:(lia) Hi' He' Hb).
      destruct (NW b ltac:(apply in_or_app; left; exact HbT) a Hab) as [N1 N2].
      exact (KBK b ltac:(right; apply in_or_app; right; apply in_or_app; left; exact HbT) a Hab N1 N2).
  - intros b Hb. apply IN3. right. apply in_or_app. right. apply in_or_app. left.
    exact (rkc_done_blks_xR cx qd i i' b HLEN Hq ltac:(lia) Hi' He' Hb). }
split.
{ intros Ho. pose proof (HOPEN Ho) as HS.
  assert (Hj4 : (snd (ghj cx i) < 4)%nat) by (apply (rkk_j4_xR cx i HB); [lia | apply Z.eqb_eq; exact Ho]).
  assert (HbT : forall b, In b (asrc_blks h1) -> In b (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []))
    by (intros b Hb; rewrite Ho; exact Hb).
  apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 m3 _ _ HS).
  - intros rr Hrr a Ha. destruct (rkc_asrc_fp_blk_xR _ _ _ _ _ _ HS rr Hrr a Ha) as [Hsl | (b & Hb & Hab)].
    + apply GSK. unfold gslot in Hsl. unfold ASRC in *. lia.
    + destruct (NW b ltac:(apply in_or_app; right; apply in_or_app; left; exact (HbT b Hb)) a Hab) as [N1 N2].
      exact (KBK b ltac:(right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact (HbT b Hb)) a Hab N1 N2).
  - intros b Hb. apply IN3. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact (HbT b Hb). }
split.
{ rewrite Forall_forall in HDRS |- *. intros [ep [hq jp]] Hp He. cbn [fst snd] in He |- *.
  destruct (HDRS _ Hp He) as (Hj & HS & Hoth & Rq). cbn [fst snd] in Hj, HS, Hoth, Rq.
  assert (Hbl : forall b, In b (asrc_blks hq) -> In b (rig_srcs (skipn (S i) (gps cx))))
    by (intros b Hb; exact (rkc_srcs_in_xR (ep, (hq, jp)) _ b Hp He Hb)).
  split; [exact Hj|]. split.
  - apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 m3 _ _ HS).
    + intros rr Hrr a Ha. destruct (rkc_asrc_fp_blk_xR _ _ _ _ _ _ HS rr Hrr a Ha) as [Hsl | (b & Hb & Hab)].
      * apply GSK. unfold ASRC in *. lia.
      * pose proof (Hbl b Hb) as HbT.
        destruct (NW b ltac:(apply in_or_app; right; apply in_or_app; right; exact HbT) a Hab) as [N1 N2].
        exact (KBK b ltac:(right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact HbT) a Hab N1 N2).
    + intros b Hb. apply IN3. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact (Hbl b Hb).
  - split; [|exact Rq]. apply (rkc_aothers_kept_xR W1 m1 W3 m3 jp (re_fd ep) Hoth).
    intros i'' Hi'' a Ha. apply GSK. unfold ASRC in *. lia. }
split.
{ intros a Ha Hns. apply (rkc_kept_trans_xR _ _ _ _ _ _ a (HGS a Ha Hns)). apply GSK. exact Ha. }
destruct (rkr_pre_nz_xR cx) as (_ & _ & Lp27).
split.
{ apply (rk_garr8_kv_xR (w_H W1) (w_H W3) m1 m3 _ _ HPRE). intros b Hb. rewrite length_app in Hb. cbn [length] in Hb.
  apply KFR. left. lia. }
{ apply (rk_garr8_kv_xR (w_H W1) (w_H W3) m1 m3 _ _ HPSH). intros b Hb. cbn [length] in Hb. apply KFR. right. lia. }
Qed.


(* rkc_end_xR with the bytes kept stated up to free's return (m4), the move's two stores (WIN) and its presence (PRES5)
   between m4 and the exit's memory m3 *)
Lemma rkc_end2_xR : forall cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m4 m3 md3 k3 out3,
  let kk := nth n ks (0, [], []) in
  let ks' := swap_remove (0, [], []) n ks in
  let SA := gSA cx i in
  let cap3 := ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text kk))) in
  let XGb := (gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx))) ++
    gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
    rig_srcs (skipn (S i) (gps cx)) in
  GBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  apres_kept B (gxW cx) (gxmem cx) W1 m1 -> g_frame cx fpos F FL ly1 W1 m1 -> alock_at RG W1 m1 true ->
  g_lslots RG cx F W1 m1 -> val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (Z.of_nat i) ->
  GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
    (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly3 S3 [] W3 m3 md3 k3 ->
  Permutation (ablocks B ly3 S3) (XGb ++ aout_blks cap3 out3 ++ gxrest cx) ->
  aout_at B RG ly2 S2 W2 m2 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (ge_no c2 (Z.of_nat (length O2)) (Z.of_nat (length (key_text kk)))) cap3 out3 ->
  apres_kept B W1 m1 W3 m4 -> apres_kept B W2 m2 W3 m4 ->
  (forall a, gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, F <= a < F + 128 \/ shadow_addr F <= a < shadow_addr F + 16 -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ inG (G_SL B RG) a -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall b, In b XGb -> forall a, fst b <= a < fst b + req_size (snd b) -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W2) m2 a) ->
  (forall a, cap3 <> 0 -> out3 <= a < out3 + req_size cap3 -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W2) m2 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (SA + 48 <= a < SA + 52) -> ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8) ->
     aview SEGS (w_H W3) m3 a = aview SEGS (w_H W3) m4 a) ->
  (forall a, apresent (w_H W3) m4 a -> apresent (w_H W3) m3 a) ->
  val_mem SEGS (arm W3 m3) (SA + 48) 4 (Z.of_nat (length ks')) ->
  val_mem SEGS (arm W3 m3) (re_hp e1 + 8 * Z.of_nat n) 8 (key_addr (nth (length ks - 1) ks (0, [], []))) ->
  GLIVE_xR B PST ARx RG R cx F FL ly3 S3 W3 m3 md3 k3 /\ g_lslots RG cx F W3 m3 /\
  val_mem SEGS (arm W3 m3) (gsp1 cx + 80) 8 (Z.of_nat i) /\
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx) (map fst qd ++ entry_keys e1 ks' :: skipn (S i) (gxes cx)) /\
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text kk)))) (ge_O c2 O2 (key_text kk)) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text kk)))) cap3 out3 /\
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) /\
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) /\
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) /\
  garr8 SEGS (arm W3 m3) (F + 32) (gpre cx ++ [0]) /\
  garr8 SEGS (arm W3 m3) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0].
Proof.
intros cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m4 m3 md3 k3 out3 kk ks' SA cap3 XGb
  HB HJ1 HPK HFR HLK HLS M80 HGN HJ3 HP3 HO2 HPK14 HPK24 KST KFR KIM KBL KO2i KO2b WIN PRES VNH VHN.
pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
pose proof (rk_jAR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : RIG_STK_x = 17232) by reflexivity. rewrite WS in Hslo. fold (gsp0 cx) in Hslo, Hshi.
assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
pose proof HGN as (_ & Hq & _ & _ & _ & Hk & _ & _ & HRLY & _).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkr_entry_at_xR ly1 S1 W1 m1 md1 (gxG0 cx) (map fst qd) e1 ks (skipn (S i) (gxes cx)) n HAR1 HRLY Hn) as X.
cbv zeta in X. rewrite length_map, Hq in X. fold (gSA cx i) in X. fold SA in X.
destruct X as (HinT & HT16 & HT4096 & HTceil & HTend & _ & _ & _ & Hhp0 & Hinh & Hkh & _).
destruct (rk_alb_xR _ _ _ _ _ _ _ HAR1 HinT) as (_ & _ & _ & HTapp & _ & _ & _).
destruct (rk_alb_xR _ _ _ _ _ _ _ HAR1 Hinh) as (_ & Hh4096 & Hhceil & Hhapp & _ & _ & _).
pose proof (rk_boi ly1 S1 W1 m1 md1 _ _ HAR1 HinT) as OT.
pose proof (rk_boi ly1 S1 W1 m1 md1 _ _ HAR1 Hinh) as OH.
change (req_size ATABLE) with 896 in *.
pose proof (req_size_pos (re_kh e1) ltac:(lia)) as [_ Hrk].
assert (HSA0 : gxG0 cx <= SA) by (unfold SA, gSA, AENT; lia).
unfold AENT, ATABLE in HTend, HTceil.
(* the two windows lie in the table and in the held array *)
assert (W1T : forall a, SA + 48 <= a < SA + 52 -> gxG0 cx <= a < gxG0 cx + 896) by (intros; lia).
assert (W2H : forall a, re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8 -> re_hp e1 <= a < re_hp e1 + req_size (re_kh e1))
  by (intros; lia).
(* the fake frame *)
pose proof HFR as (HFa & _).
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as (memS & HJi & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (rk_fb _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil. rewrite HFa in HF4096, HFceil.
pose proof (rk_frame_blk_apart_xR _ _ _ _ _ _ _ _ _ HAR1 Hfin HinT) as DFT.
pose proof (rk_frame_blk_apart_xR _ _ _ _ _ _ _ _ _ HAR1 Hfin Hinh) as DFH.
change (fs_frame_bytes 1) with 128 in DFT, DFH. rewrite HFa in DFT, DFH. change (req_size ATABLE) with 896 in DFT.
assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HF8 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8u : F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
(* the output buffer at the exit, apart from both windows *)
assert (OW : forall a, cap3 <> 0 -> out3 <= a < out3 + req_size cap3 ->
  ~ (SA + 48 <= a < SA + 52) /\ ~ (re_hp e1 + 8 * Z.of_nat n <= a < re_hp e1 + 8 * Z.of_nat n + 8)).
{ intros a Hc Ha.
  pose proof (rk_ablocks_nodup_xR _ _ _ _ _ HAR3) as HND3. pose proof (Permutation_NoDup HP3 HND3) as HNDX.
  assert (HinO : In (out3, cap3) (aout_blks cap3 out3 ++ gxrest cx))
    by (apply in_or_app; left; unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap3 0) Hc); left; reflexivity).
  assert (HinHX : In (re_hp e1, re_kh e1) XGb).
  { right. apply in_or_app. left. apply in_concat. exists (aentry_blks (entry_keys e1 ks')). split.
    - apply in_map. apply in_or_app. right. left. reflexivity.
    - unfold aentry_blks. apply in_or_app. right. apply in_or_app. left. cbn [re_hp re_kh entry_keys].
      destruct (Z.eqb_spec (re_hp e1) 0); [contradiction | left; reflexivity]. }
  assert (I3 : forall b, In b (XGb ++ aout_blks cap3 out3 ++ gxrest cx) -> In b (ablocks B ly3 S3))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP3) Hb)).
  assert (NT : (out3, cap3) <> (gxG0 cx, ATABLE))
    by (intros Heq; apply (rk_nodup_app_disj_xR _ _ (gxG0 cx, ATABLE) HNDX (or_introl eq_refl)); rewrite <- Heq; exact HinO).
  assert (NH : (out3, cap3) <> (re_hp e1, re_kh e1))
    by (intros Heq; apply (rk_nodup_app_disj_xR _ _ (re_hp e1, re_kh e1) HNDX HinHX); rewrite <- Heq; exact HinO).
  destruct (rk_disj_xR ly3 S3 W3 m3 md3 out3 cap3 (gxG0 cx) ATABLE HAR3 (I3 _ ltac:(apply in_or_app; right; exact HinO))
    (I3 _ ltac:(apply in_or_app; left; left; reflexivity)) NT) as [D1|D1];
  destruct (rk_disj_xR ly3 S3 W3 m3 md3 out3 cap3 (re_hp e1) (re_kh e1) HAR3 (I3 _ ltac:(apply in_or_app; right; exact HinO))
    (I3 _ ltac:(apply in_or_app; left; exact HinHX)) NH) as [D2|D2];
  change (req_size ATABLE) with 896 in D1; split; intros Hw; [pose proof (W1T a Hw) | pose proof (W2H a Hw) | pose proof (W1T a Hw) | pose proof (W2H a Hw)
    | pose proof (W1T a Hw) | pose proof (W2H a Hw) | pose proof (W1T a Hw) | pose proof (W2H a Hw)]; lia. }
apply (rkc_end_xR cx i n r F FL fpos qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 md1 k1 ly2 S2 W2 m2 ly3 S3 W3 m3 md3 k3 out3 HB HJ1 HPK HFR HLK HLS M80 HGN HJ3 HP3 HO2).
- intros a Hi Ho He Hp. exact (PRES a (HPK14 a Hi Ho He Hp)).
- intros a Hi Ho He Hp. exact (PRES a (HPK24 a Hi Ho He Hp)).
- intros a Ha. rewrite WIN; [exact (KST a Ha) | lia | intros Hw; pose proof (W1T a Hw); lia | intros Hw; pose proof (W2H a Hw); lia].
- intros a Ha. pose proof Ha as Ha'. rewrite SF in Ha'. rewrite WIN; [exact (KFR a Ha) | lia | |].
  + intros Hw. pose proof (W1T a Hw). destruct Ha as [Ha | Ha]; [lia|].
    rewrite SF in Ha. exact (fshadow_not_app F 16 (gxG0 cx) 896 a ltac:(lia) ltac:(lia) HTapp ltac:(lia) ltac:(lia)).
  + intros Hw. pose proof (W2H a Hw). destruct Ha as [Ha | Ha]; [lia|].
    rewrite SF in Ha. exact (fshadow_not_app F 16 (re_hp e1) (req_size (re_kh e1)) a ltac:(lia) ltac:(lia) Hhapp ltac:(lia) ltac:(lia)).
- intros a Hi Ho He Hps Hg. pose proof (pa_img_range a Hi) as HR. pose proof (pa_segs_low a Hi) as HL. rewrite C5 in HL. unfold SHADOW_OFF in HL.
  rewrite WIN; [exact (KIM a Hi Ho He Hps Hg) | lia | intros Hw; pose proof (W1T a Hw); lia | intros Hw; pose proof (W2H a Hw); lia].
- intros b Hb a Ha N1 N2. rewrite WIN; [exact (KBL b Hb a Ha) | | exact N1 | exact N2].
  pose proof (Permutation_in _ (Permutation_sym HP3) (in_or_app _ _ _ (or_introl Hb))) as Hb3. destruct b as [p nb].
  destruct (rk_alb_xR _ _ _ _ _ _ _ HAR3 Hb3) as (_ & Hp4 & Hpc & _). cbn [fst snd] in Ha. lia.
- intros a Hi Ho. pose proof (pa_img_range a Hi) as HR. pose proof (pa_segs_low a Hi) as HL. rewrite C5 in HL. unfold SHADOW_OFF in HL.
  rewrite WIN; [exact (KO2i a Hi Ho) | lia | intros Hw; pose proof (W1T a Hw); lia | intros Hw; pose proof (W2H a Hw); lia].
- intros a Hc Ha. destruct (OW a Hc Ha) as [N1 N2].
  assert (Hb3 : In (out3, cap3) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP3)). apply in_or_app. right. apply in_or_app. left.
    unfold aout_blks. destruct (Z.eqb_spec cap3 0) as [E0|E0]; [exfalso; exact (Hc E0) | left; reflexivity]. }
  destruct (rk_alb_xR _ _ _ _ _ _ _ HAR3 Hb3) as (_ & Hp4 & Hpc & _). unfold cap3, kk in Hpc.
  rewrite WIN; [exact (KO2b a Hc Ha) | lia | exact N1 | exact N2].
- exact VNH.
- exact VHN.
Qed.
End wR.

End c.
End b.
End a.
