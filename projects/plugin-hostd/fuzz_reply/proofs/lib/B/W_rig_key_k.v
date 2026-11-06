(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE-B segment KEY of fuzz_reply's relay_instance_gone: the keep lemmas (prefix rkk_: the cut predicates'
   memory facts survive a change of memory in the scratch window only), ported from k3's image-A lib/A/W_rig_key.v
   (a working branch 8cfff43c147) to B's frame slots.  Proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the image-A twin is
   a Theorem Labs lane's RIG_x round, commit f4cd818e98d, lib/A/W_rig_key.v's keep block): the keep lemmas over any allocator
   relation ARx, against the cx file's generic Section (copied below).  Every ARx state is read at the empty head set
   (HP0: ARh below, the image-A twin's technique, with Local helpers), so the journal rkk_jar / rkk_gin / rkk_live read
   runs from [] to [] at the kit's RIG_STK_x (= RIG_STK + 128, rig_spec_x's budget); the scratch window is
   [gsp1 cx - DRAIN_STK_x, gsp1 cx) (DRAIN_STK_x = DRAIN_STK + 128, RIG_STK_x = RIG_FRAME + DRAIN_STK_x; the image-A
   twin's bcc0646e8ae), still above GBASE's ly_stk_lo >= alloc_ceiling; GBASE, GIN and GLIVE take the generic
   arguments, and GLIVE's two head sets (gxHp, Hp1) are both [] (rk_gxHp). *)
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
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
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
(* HP0: every ARx state the keep lemmas read has the head set [], so they state their facts at ARh (= ARx at []) and the
   walk's journal from [] to [].  rk_alb is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR
   walk's argument order. *)
#[local] Notation ARh ly S W mem md := (ARx ly S (@nil Z) W mem md).
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
(* the entry's head set is empty too (GBASE's afn_pre_x states ARx at gxHp) *)
Local Lemma rk_gxHp : forall cx, GBASE B ARx MT RP MMAX RG cx -> gxHp cx = [].
Proof. intros cx HB. destruct HB as ((HAR & _) & _). exact (HP0 _ _ _ _ _ _ HAR). Qed.

(* ==== keep block (RigKeyKeep) ==== *)

(* ---- rkk_: the cut predicates' memory facts survive a change of memory only in the scratch window
   [gsp1 cx - DRAIN_STK_x, gsp1 cx) below sp = gsp1 cx (an interceptor call's scratch at a cut after the prologue).
   The window is [gsp0 cx - RIG_STK_x, gsp1 cx) (RIG_STK_x = RIG_FRAME + DRAIN_STK_x): its bottom is at or above
   ly_stk_lo >= alloc_ceiling (GBASE's astk_ok at the kit's RIG_STK_x), so every heap block, frame, image byte and
   shadow byte the predicates read lies below it, and every frame slot (gsp1 + 16 .. gsp0) above it. ---- *)
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
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity. assert (HD : DRAIN_STK_x = 17008) by reflexivity.
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
  { destruct HF as (HFa & HFl & H120 & H8 & H16 & H112 & H72 & Hsv).
    rewrite HFa in HF4, HFc.
    unfold g_frame. split; [exact HFa|]. split; [exact HFl|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; change (Z.of_nat 8) with 8 in Hx; lia | exact H120]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H8]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H16]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H112]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H72]|].
    intros j Hj. apply (akept_vm W1 m1); [|exact (Hsv j Hj)].
    intros x Hx. apply KH. change (Z.of_nat 8) with 8 in Hx. lia. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HL). intros r Hr a Ha. destruct Hr as [<-|[]].
  apply KC. cbn [fst snd] in Ha. apply (rkk_glob cx a HB). tauto.
Qed.

(* ---- 3. the loop's frame slots ---- *)
Theorem rkk_lslots : forall cx F W1 m1 m2, g_lslots RG cx F W1 m1 -> rkk_KEEP cx W1 m1 m2 -> g_lslots RG cx F W1 m2.
Proof.
  intros cx F W1 m1 m2 (H24 & H32 & H40 & H48 & H56 & H64 & H88) HK.
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  assert (V : forall a, gsp1 cx + 24 <= a < gsp1 cx + 96 -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a)
    by (intros a Ha; apply (rkk_view_hi cx W1 m1 m2 a HK); lia).
  unfold g_lslots.
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H24]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H32]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H40]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H48]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H56]|].
  split; [apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H64]|].
  apply (rkk_vm W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H88].
Qed.


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the journal readers at a world relation R.  The strict lemmas above take every Section
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
(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state the keep lemmas read has the head set [], so they state their facts at ARh (= ARx at []) and the
   walk's journal from [] to [].  rk_alb_xR is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR
   walk's argument order. *)
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

(* ==== keep block (RigKeyKeep) ==== *)

(* ---- rkk_: the cut predicates' memory facts survive a change of memory only in the scratch window
   [gsp1 cx - DRAIN_STK_x, gsp1 cx) below sp = gsp1 cx (an interceptor call's scratch at a cut after the prologue).
   The window is [gsp0 cx - RIG_STK_x, gsp1 cx) (RIG_STK_x = RIG_FRAME + DRAIN_STK_x): its bottom is at or above
   ly_stk_lo >= alloc_ceiling (GBASE's astk_ok at the kit's RIG_STK_x), so every heap block, frame, image byte and
   shadow byte the predicates read lies below it, and every frame slot (gsp1 + 16 .. gsp0) above it. ---- *)

Lemma rkk_aview_mod_xR : forall H (m : word -> option byte) a,
  aview SEGS H m (a mod 2 ^ 64) = aview SEGS H m a.
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv64_mod. reflexivity. Qed.

Lemma rkk_wr_xR : forall W m1 m2 a, rkk_PRES W m1 m2 ->
  writable_at SEGS (arm W m1) a -> writable_at SEGS (arm W m2) a.
Proof.
  intros W m1 m2 a HP. unfold writable_at, wview, arm, mrestrict.
  destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [exact (fun H => H)|].
  destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:E2; [intros _; cbn; discriminate|].
  destruct (m1 (Z_to_bv 64 a)) as [b1|] eqn:E1; [|exact (fun H => H)].
  destruct (HP a (conj EH (ex_intro _ b1 E1))) as [_ [b E]]. rewrite E in E2. discriminate E2.
Qed.

Lemma rkk_bv_xR : forall cx, 0 <= gsp0 cx < 2 ^ 64.
Proof. intros cx. unfold gsp0, spZ. exact (bv_unsigned_in_range 64 _). Qed.

Lemma rkk_view_mod_xR : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 ->
  ~ (gsp1 cx - DRAIN_STK_x <= a mod 2 ^ 64 < gsp1 cx) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
  intros cx W m1 m2 a HK Hw.
  rewrite <- (rkk_aview_mod_xR (w_H W) m2 a), <- (rkk_aview_mod_xR (w_H W) m1 a).
  apply HK; [apply Z.mod_pos_bound; lia | exact Hw].
Qed.

Lemma rkk_view_hi_xR : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 ->
  gsp1 cx <= a < gsp0 cx -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
  intros cx W m1 m2 a HK Ha. apply (rkk_view_mod_xR cx); [exact HK|].
  pose proof (rkk_bv_xR cx) as Hb.
  destruct (Z_le_gt_dec 0 a) as [H0|H0].
  - rewrite Z.mod_small by lia. lia.
  - pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma rkk_view_lo_xR : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 ->
  0 <= a < gsp1 cx - DRAIN_STK_x -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
  intros cx W m1 m2 a HK Ha. apply (rkk_view_mod_xR cx); [exact HK|].
  pose proof (rkk_bv_xR cx) as Hb.
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity. assert (HD : DRAIN_STK_x = 17008) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rkk_kept_hi_xR : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  gsp1 cx <= a < gsp0 cx -> abyte_kept W m1 W m2 a.
Proof.
  intros cx W m1 m2 a HK HP Ha. unfold abyte_kept.
  split; [exact (rkk_view_hi_xR cx W m1 m2 a HK Ha) | exact (rkk_wr_xR W m1 m2 a HP)].
Qed.

Lemma rkk_kept_lo_xR : forall cx W m1 m2 a, rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  0 <= a < gsp1 cx - DRAIN_STK_x -> abyte_kept W m1 W m2 a.
Proof.
  intros cx W m1 m2 a HK HP Ha. unfold abyte_kept.
  split; [exact (rkk_view_lo_xR cx W m1 m2 a HK Ha) | exact (rkk_wr_xR W m1 m2 a HP)].
Qed.

(* the ASan view decides a cell *)
Lemma rkk_vm_xR : forall W m1 m2 a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x) ->
  val_mem SEGS (arm W m1) a n v -> val_mem SEGS (arm W m2) a n v.
Proof.
  intros W m1 m2 a n v HK Hv k Hk. unfold arm.
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m1 m2 (a + Z.of_nat k)); [exact (Hv k Hk)|].
  exact (HK (a + Z.of_nat k) ltac:(lia)).
Qed.

(* the window's bottom is at or above alloc_ceiling *)
Lemma rkk_ceil_xR : forall cx, GBASE B ARx MT RP MMAX RG cx -> alloc_ceiling <= gsp1 cx - DRAIN_STK_x.
Proof.
  intros cx HB. destruct HB as (HPRE & _).
  destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & _).
  assert (E : RIG_STK_x = RIG_FRAME + DRAIN_STK_x) by reflexivity.
  unfold gsp1, gsp0. lia.
Qed.

Lemma rkk_kept_c_xR : forall cx W m1 m2 a, GBASE B ARx MT RP MMAX RG cx -> rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  0 <= a < alloc_ceiling -> abyte_kept W m1 W m2 a.
Proof.
  intros cx W m1 m2 a HB HK HP Ha. pose proof (rkk_ceil_xR cx HB).
  apply (rkk_kept_lo_xR cx W m1 m2 a HK HP). lia.
Qed.

(* every byte of every range of fp is below alloc_ceiling *)

Lemma rkk_akept_xR : forall cx W m1 m2 fp, GBASE B ARx MT RP MMAX RG cx -> rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  rkk_low fp -> akept W m1 W m2 fp.
Proof. intros cx W m1 m2 fp HB HK HP HL r Hr a Ha. exact (rkk_kept_c_xR cx W m1 m2 a HB HK HP (HL r Hr a Ha)). Qed.

(* ---- where the bytes are ---- *)
Lemma rkk_blk_xR : forall ly S W m md p n a, ARh ly S W m md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + n -> 0 <= a < alloc_ceiling.
Proof.
  intros ly S W m md p n a HAR Hin Ha.
  destruct (rk_alb_xR ly S W m md p n HAR Hin) as (_ & H4 & Hc & _).
  unfold req_size in Hc. destruct (n =? 0) eqn:En; [apply Z.eqb_eq in En; lia | lia].
Qed.

Lemma rkk_img_xR : forall a, in_img SEGS a -> 0 <= a < alloc_ceiling.
Proof.
  intros a H. pose proof (pa_segs_low a H) as Hl. pose proof asan_consts as (C1 & _ & _ & _ & C5).
  rewrite C5 in Hl. lia.
Qed.

Lemma rkk_inG_xR : forall a, inG (G_RIG B RG) a -> 0 <= a < alloc_ceiling.
Proof. intros a H. exact (rkk_img_xR a (proj1 (HGRIG a H))). Qed.

Lemma rkk_glob_xR : forall cx a, GBASE B ARx MT RP MMAX RG cx ->
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
  { intros lo len Hin Ha. apply rkk_inG_xR. unfold inG. apply Exists_exists. exists (lo, len).
    split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  assert (HR : rg_rng RG a -> 0 <= a < alloc_ceiling) by (intros Hr; exact (rkk_img_xR a (proj1 (Hrng a Hr)))).
  assert (HI : (rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
    rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) -> 0 <= a < alloc_ceiling)
    by (intros Hr; exact (rkk_img_xR a (proj1 (HRGI a Hr)))).
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
Lemma rkk_j4_xR : forall cx i, GBASE B ARx MT RP MMAX RG cx -> (i < length (gxes cx))%nat -> re_eof (gnth cx i) = 0 ->
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

Lemma rkk_slot_loc_xR : forall cx j, GBASE B ARx MT RP MMAX RG cx -> (j < 4)%nat ->
  forall a, rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC -> 0 <= a < alloc_ceiling.
Proof. intros cx j HB Hj a Ha. apply (rkk_glob_xR cx a HB). right; left. unfold ASRC in *. lia. Qed.

Lemma rkk_len_recs_xR : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold text_rec, Mem.le8.
  rewrite length_app, !length_N_to_le_bytes. lia.
Qed.

Lemma rkk_len_ptrs_xR : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold key_ptrs in *. cbn [map concat length]. rewrite length_app, IH. unfold Mem.le8.
  rewrite length_N_to_le_bytes. lia.
Qed.

Lemma rkk_alist_xR : forall ly S W m md LA l lines, ARh ly S W m md -> alist_at B ly S W m LA l lines ->
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
        apply (rkk_blk_xR ly S W m md (hl_v l) (AREC * hl_cap l) a HAR Hin).
        unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, rkk_len_recs_xR in Ha.
        unfold hl_n in Hj. unfold AREC in *. lia.
    + apply in_map_iff in Hrg. destruct Hrg as (r & <- & Hr).
      apply (rkk_blk_xR ly S W m md (fst r) (Z.of_nat (length (snd r)) + 1) a HAR (proj1 (H9 r Hr))).
      unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
  - intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    + destruct H6 as [(Hc & _) | (Hc & Hin & _)].
      * rewrite Hc in Hb. cbn in Hb. destruct Hb.
      * assert (E : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hb.
        destruct Hb as [<-|[]]. exact Hin.
    + apply in_map_iff in Hb. destruct Hb as (r & <- & Hr). exact (proj1 (H9 r Hr)).
Qed.

Lemma rkk_asrc_xR : forall ly S W m md HA h, ARh ly S W m md -> asrc_at B ly S W m HA h ->
  (forall a, HA <= a < HA + ASRC -> 0 <= a < alloc_ceiling) ->
  rkk_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W m md HA h HAR Hs HHA.
  destruct Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & H19 & _ & _ & H22 & H23 & _).
  destruct (rkk_alist_xR ly S W m md (HA + 16) _ _ HAR H10 ltac:(intros a Ha; apply HHA; unfold ASRC; lia)) as [L1 B1].
  destruct (rkk_alist_xR ly S W m md (HA + 64) _ _ HAR H22 ltac:(intros a Ha; apply HHA; unfold ASRC; lia)) as [L2 B2].
  destruct (rkk_alist_xR ly S W m md (HA + 80) _ _ HAR H23 ltac:(intros a Ha; apply HHA; unfold ASRC; lia)) as [L3 B3].
  split.
  - intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<-|[<-|Hr]].
    + apply HHA. exact Ha.
    + apply (rkk_blk_xR ly S W m md (hs_partial h) APARTIAL a HAR H18).
      unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map in Ha. lia.
    + apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (L1 r Hr a Ha)|].
      apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (L2 r Hr a Ha) | exact (L3 r Hr a Ha)].
  - intros b Hb. unfold asrc_blks in Hb. destruct Hb as [<-|Hb]; [exact H18|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (B1 b Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (B2 b Hb) | exact (B3 b Hb)].
Qed.

Lemma rkk_aentry_xR : forall ly S W m md e, ARh ly S W m md -> aentry_ok B ly S W m e ->
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
        apply (rkk_blk_xR ly S W m md (re_buf e) (re_cap e) a HAR Hin).
        unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. lia.
    + destruct Hr as [<-|Hr].
      * unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, rkk_len_ptrs_xR in Ha.
        destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)].
        -- rewrite Hk in Ha. cbn [length] in Ha. lia.
        -- apply (rkk_blk_xR ly S W m md (re_hp e) (re_kh e) a HAR Hin). unfold re_nheld in Hk1. lia.
      * apply in_map_iff in Hr. destruct Hr as (k & <- & Hk).
        apply (rkk_blk_xR ly S W m md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR (proj1 (H15 k Hk))).
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

Lemma rkk_arelay_xR : forall cx ly S W m md G es, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m md ->
  arelay_at B RG ly S W m G es ->
  rkk_low (arelay_fp RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros cx ly S W m md G es HB HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  rewrite Forall_forall in H10.
  split.
  - intros r Hr a Ha. unfold arelay_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|Hr]]]]; cbn [fst snd] in Ha.
    + apply (rkk_glob_xR cx a HB). tauto.
    + apply (rkk_glob_xR cx a HB). tauto.
    + apply (rkk_glob_xR cx a HB). tauto.
    + exact (rkk_blk_xR ly S W m md G ATABLE a HAR H8 Ha).
    + apply in_concat in Hr. destruct Hr as (l & Hl & Hr). apply in_map_iff in Hl. destruct Hl as (e & <- & He).
      exact (proj1 (rkk_aentry_xR ly S W m md e HAR (H10 e He)) r Hr a Ha).
  - intros b Hb. unfold arelay_blks in Hb. destruct Hb as [<-|Hb]; [exact H8|].
    apply in_concat in Hb. destruct Hb as (l & Hl & Hb). apply in_map_iff in Hl. destruct Hl as (e & <- & He).
    exact (proj2 (rkk_aentry_xR ly S W m md e HAR (H10 e He)) b Hb).
Qed.

Lemma rkk_aout_xR : forall cx ly S W m md c O mx no cap out, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m md ->
  aout_at B RG ly S W m c O mx no cap out ->
  rkk_low (aout_fp B RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros cx ly S W m md c O mx no cap out HB HAR Ho.
  destruct Ho as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H26).
  split.
  - intros r Hr a Ha. unfold aout_fp in Hr.
    do 9 (destruct Hr as [<-|Hr]; [cbn [fst snd] in Ha; apply (rkk_glob_xR cx a HB); tauto|]).
    destruct H26 as [(Hc & _ & _) | (Hc & Hno & Hin & junk & Hj & Hg)].
    + rewrite Hc in Hr. cbn in Hr. destruct Hr.
    + assert (E : (cap =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hr.
      destruct Hr as [<-|[]]. cbn [fst snd] in Ha. exact (rkk_blk_xR ly S W m md out cap a HAR Hin Ha).
  - intros b Hb. unfold aout_blks in Hb.
    destruct H26 as [(Hc & _ & _) | (Hc & Hno & Hin & junk & Hj & Hg)].
    + rewrite Hc in Hb. cbn in Hb. destruct Hb.
    + assert (E : (cap =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E in Hb.
      destruct Hb as [<-|[]]. exact Hin.
Qed.

(* ---- the predicates, across the change ---- *)
Lemma rkk_asrc_m_xR : forall cx ly S W m1 m2 md HA h, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m1 md ->
  rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 -> asrc_at B ly S W m1 HA h ->
  (forall a, HA <= a < HA + ASRC -> 0 <= a < alloc_ceiling) -> asrc_at B ly S W m2 HA h.
Proof.
  intros cx ly S W m1 m2 md HA h HB HAR HK HP Hs HL.
  destruct (rkk_asrc_xR ly S W m1 md HA h HAR Hs HL) as [L Bl].
  exact (asrc_at_kept B ly S W m1 ly S W m2 HA h Hs (rkk_akept_xR cx W m1 m2 _ HB HK HP L) Bl).
Qed.

Lemma rkk_aothers_xR : forall cx W m1 m2 j fd, GBASE B ARx MT RP MMAX RG cx -> rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  aothers_at RG W m1 j fd -> aothers_at RG W m2 j fd.
Proof.
  intros cx W m1 m2 j fd HB HK HP Ho i Hi Hij. destruct (Ho i Hi Hij) as (f & o & Hf & Hof & Hx).
  assert (KS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W m1 W m2 x)
    by (intros x Hx'; apply (rkk_kept_c_xR cx W m1 m2 x HB HK HP); apply (rkk_glob_xR cx x HB); tauto).
  exists f, o. split; [|split; [|exact Hx]].
  - apply (akept_vm W m1); [intros x Hx'; apply KS; unfold ASRC in *; lia | exact Hf].
  - apply (akept_vm W m1); [intros x Hx'; apply KS; unfold ASRC in *; lia | exact Hof].
Qed.

Lemma rkk_drsrc_xR : forall cx ly S W m1 m2 md e h j, GBASE B ARx MT RP MMAX RG cx -> ARh ly S W m1 md ->
  rkk_KEEP cx W m1 m2 -> rkk_PRES W m1 m2 ->
  dr_src_ok B RG ly S W m1 e h j -> dr_src_ok B RG ly S W m2 e h j.
Proof.
  intros cx ly S W m1 m2 md e h j HB HAR HK HP (Hj & Hs & Ho & Hrest).
  split; [exact Hj|]. split; [|split; [exact (rkk_aothers_xR cx W m1 m2 j _ HB HK HP Ho) | exact Hrest]].
  exact (rkk_asrc_m_xR cx ly S W m1 m2 md _ h HB HAR HK HP Hs (rkk_slot_loc_xR cx j HB Hj)).
Qed.

Lemma rkk_digits_xR : forall f x acc, (length (printf_facts_c.pf_digits f x acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc; cbn [printf_facts_c.pf_digits]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|].
  specialize (IH (x / 10) (48 + x mod 10 :: acc)). cbn [length] in IH. lia.
Qed.

Lemma rkk_pre_len_xR : forall cx, (length (gpre cx) <= 27)%nat.
Proof.
  intros cx. unfold gpre, relay_instance_gone_b_c.instance_prefix, printf_facts_c.pf_dec, RelayModel.K_GESTURE.
  rewrite !length_app.
  destruct (gxID cx <? 0).
  - pose proof (rkk_digits_xR 11 (- gxID cx) []) as H. cbn [length] in H |- *. lia.
  - pose proof (rkk_digits_xR 11 (gxID cx) []) as H. cbn [length] in H |- *. lia.
Qed.

(* the journal's allocator state, and the fake frame among its frames *)
Lemma rkk_jar_xR : forall cx fpos ly1 S1 W1 m1 md1 k1,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) [] (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 [] W1 m1 md1 k1 ->
  ARh ly1 S1 W1 m1 md1 /\ In (1, fpos) (frames S1).
Proof.
  intros cx fpos ly1 S1 W1 m1 md1 k1 HJ.
  destruct HJ as (_ & _ & (memS & HJ' & _) & _).
  destruct HJ' as (HAR & _ & _ & _ & _ & Hfrs & _).
  split; [exact HAR|]. rewrite Hfrs. apply in_or_app. left. left. reflexivity.
Qed.

(* ---- 1. GIN ---- *)
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
    by (intros a Ha; exact (rkk_kept_c_xR cx W1 m1 m2 a HB HK HP Ha)).
  unfold GIN in HG |- *. cbv zeta in HG |- *.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
  do 8 (split; [assumption|]).
  split.
  { destruct (rkk_arelay_xR cx ly1 S1 W1 m1 md1 _ _ HB HAR G9) as [L Bl].
    exact (arelay_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ G9 (rkk_akept_xR cx W1 m1 m2 _ HB HK HP L) Bl). }
  split.
  { destruct (rkk_aout_xR cx ly1 S1 W1 m1 md1 _ _ _ _ _ _ HB HAR G10) as [L Bl].
    exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ _ G10 (rkk_akept_xR cx W1 m1 m2 _ HB HK HP L) Bl). }
  split.
  { intros i' Hi' He. apply (rkk_asrc_m_xR cx ly1 S1 W1 m1 m2 md1 _ _ HB HAR HK HP (G11 i' Hi' He)).
    unfold gslot. apply (rkk_slot_loc_xR cx _ HB). apply (rkk_j4_xR cx i' HB); [lia | exact He]. }
  split.
  { intros Ho. apply (rkk_asrc_m_xR cx ly1 S1 W1 m1 m2 md1 _ _ HB HAR HK HP (G12 Ho)).
    unfold gslot. apply (rkk_slot_loc_xR cx _ HB). apply (rkk_j4_xR cx i HB G1). apply Z.eqb_eq. exact Ho. }
  split.
  { rewrite Forall_forall in G13 |- *. intros p Hp Heof.
    exact (rkk_drsrc_xR cx ly1 S1 W1 m1 m2 md1 _ _ _ HB HAR HK HP (G13 p Hp Heof)). }
  split.
  { intros a Ha Hj. destruct (G14 a Ha Hj) as [V Wr].
    destruct (KC a (rkk_glob_xR cx a HB ltac:(tauto))) as [V2 Wr2].
    unfold abyte_kept. split; [rewrite V2; exact V | intros Hw; apply Wr2; apply Wr; exact Hw]. }
  split; [exact G15|].
  split.
  { apply (akept_garr8 W1 m1); [|exact G16]. intros x Hx. apply KC.
    pose proof (rkk_pre_len_xR cx). rewrite length_app in Hx. cbn [length] in Hx. lia. }
  split.
  { apply (akept_garr8 W1 m1); [|exact G17]. intros x Hx. apply KC.
    assert (HF8 : 0 <= F / 8 <= 2 ^ 45) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    cbn [length] in Hx. unfold shadow_addr, SHADOW_OFF in Hx. lia. }
  exact G18.
Qed.

(* ---- 2. GLIVE ---- *)
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
    by (intros a Ha; exact (rkk_kept_c_xR cx W1 m1 m2 a HB HK HP Ha)).
  assert (KH : forall a, gsp1 cx <= a < gsp0 cx -> abyte_kept W1 m1 W1 m2 a)
    by (intros a Ha; exact (rkk_kept_hi_xR cx W1 m1 m2 a HK HP Ha)).
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  unfold GLIVE_xR. exists fpos, []. split; [rewrite (rk_gxHp_xR cx HB); exact HJ2|].
  split.
  { intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
    destruct (KC a (rkk_img_xR a Hi)) as [V _]. rewrite V. exact (HR a Ha). }
  split.
  { intros a Ha1 Ha2 Ha3 Ha4. apply HP. exact (HA a Ha1 Ha2 Ha3 Ha4). }
  split.
  { destruct HF as (HFa & HFl & H120 & H8 & H16 & H112 & H72 & Hsv).
    rewrite HFa in HF4, HFc.
    unfold g_frame. split; [exact HFa|]. split; [exact HFl|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; change (Z.of_nat 8) with 8 in Hx; lia | exact H120]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H8]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H16]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H112]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KH; change (Z.of_nat 8) with 8 in Hx; lia | exact H72]|].
    intros j Hj. apply (akept_vm W1 m1); [|exact (Hsv j Hj)].
    intros x Hx. apply KH. change (Z.of_nat 8) with 8 in Hx. lia. }
  apply (alock_at_kept RG W1 m1 W1 m2 true HL). intros r Hr a Ha. destruct Hr as [<-|[]].
  apply KC. cbn [fst snd] in Ha. apply (rkk_glob_xR cx a HB). tauto.
Qed.

(* ---- 3. the loop's frame slots ---- *)
Theorem rkk_lslots_xR : forall cx F W1 m1 m2, g_lslots RG cx F W1 m1 -> rkk_KEEP cx W1 m1 m2 -> g_lslots RG cx F W1 m2.
Proof.
  intros cx F W1 m1 m2 (H24 & H32 & H40 & H48 & H56 & H64 & H88) HK.
  assert (E1 : gsp1 cx = gsp0 cx - 224) by reflexivity.
  assert (V : forall a, gsp1 cx + 24 <= a < gsp1 cx + 96 -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a)
    by (intros a Ha; apply (rkk_view_hi_xR cx W1 m1 m2 a HK); lia).
  unfold g_lslots.
  split; [apply (rkk_vm_xR W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H24]|].
  split; [apply (rkk_vm_xR W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H32]|].
  split; [apply (rkk_vm_xR W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H40]|].
  split; [apply (rkk_vm_xR W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H48]|].
  split; [apply (rkk_vm_xR W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H56]|].
  split; [apply (rkk_vm_xR W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H64]|].
  apply (rkk_vm_xR W1 m1); [intros x Hx; apply V; change (Z.of_nat 8) with 8 in Hx; lia | exact H88].
Qed.
End wR.

End c.
End b.
End a.
