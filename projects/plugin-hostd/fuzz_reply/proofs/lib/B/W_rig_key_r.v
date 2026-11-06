(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE-B segment KEY of fuzz_reply's relay_instance_gone: the block and representation lemmas (prefixes rk_ /
   rkr_: entry i as KEY reads it, the relay after the end-and-move, strncmp's view of a key and the prefix), ported
   from k3's image-A lib/A/W_rig_key.v (a working branch 8cfff43c147).  Proves no function (kind:
   segment lemma). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), the RIGX round on
   image B: the block and representation lemmas over any allocator relation ARx with its laws, against the cx file's
   generic Section (lib/B/W_relay_instance_gone_cx.v; its Section c copied below), as the image-A twin's conversion
   (lib/A/W_rig_key.v).  Every ARx state these lemmas read has the empty head set (HP0), so they state their facts at
   ARh (= ARx at []) through Local wrappers of the laws in the AR argument order (the image-A twin's rk_alb / rk_als /
   rk_alc / rk_boi).  rk_wr_blk's write window is the walk's journal budget, the kit's RIG_STK_x (= RIG_STK + 128). *)
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
(* blk_off_imgB_x: a live block off image B's band [0x10000, 0x5fc000) (W_kit_x.v's blk_off_imgP_x states the shared
   core's off_img, image A's top 0x5fb000, too weak beside B's pa_img_range) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_xb.
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
(* HP0: every ARx state these lemmas read has the head set [], so they state their facts at ARh (= ARx at []).  rk_alb
   is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's argument order. *)
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
Local Definition rk_als ly S W mem md (H : ARh ly S W mem md) := alx_sep _ _ _ LAWS ly S [] W mem md H.
Local Definition rk_alc ly S W mem md a (H : ARh ly S W mem md) := alx_client_img _ _ _ LAWS ly S [] W mem md a H.
Local Definition rk_boi ly S W mem md p n (H : ARh ly S W mem md) := blk_off_imgB_x B ARx LAWS IMGC BLKN ly S [] W mem md p n H.

(* ---- small list / block facts ---- *)
(* the live blocks are pairwise distinct: their extents are pairwise apart and non-empty (ARx_sep_law) *)
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
Lemma rk_branch_lt : forall E a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
0 <= va < 2 ^ 63 -> 0 <= vb < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (va <? vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma rk_nodup_mid : forall {A : Type} (l1 l2 : list A) x y, NoDup (l1 ++ x :: l2) -> In y (l1 ++ l2) -> x <> y.
Proof.
intros A l1 l2 x y HN Hy <-. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN.
exact (List.NoDup_remove_2 _ _ _ HN Hy).
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
(* Premises beyond the first text (the parent's KEY call site has them: GLIVE's ARx at the old state, GBASE's
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
(* the relay's blocks are pairwise apart (ARx's blocks law, through the Permutation) *)
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
  change (req_size ATABLE) with 896 in O1.
  unfold ATABLE. split; lia. }
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
(* arelay_at's 12th conjunct (the kit's W_rep: NoDup of the fds, and no entry block is the table): the fds as before;
   an entry's blocks after the swap are among its blocks before (its keys are a sublist: rig_swap_incl) *)
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


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): KEY's representation lemmas at a world relation R.  The strict lemmas above take every Section
   hypothesis (Default Proof Using "All"), the strict AFREE / DRAIN / GE / ALLOC_TAIL included, so this Section copies
   each of them as X_xR (same statement and proof) under a Default Proof Using that leaves those out.  The lemmas that
   read a journal are lifted: ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the journal lemmas ->
   their _xR twins (W_journal_x.v), nothing else (no lemma here reads a journal).  The hypothesis list is the cx file's Section wR, verbatim. ---- *)
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
(* HP0: every ARx state these lemmas read has the head set [], so they state their facts at ARh (= ARx at []).  rk_alb_xR
   is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's argument order. *)
Local Lemma rk_alb_xR : forall ly S W mem md p n, ARh ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.

(* ---- small list / block facts ---- *)
(* the live blocks are pairwise distinct: their extents are pairwise apart and non-empty (ARx_sep_law) *)
Lemma rk_ablocks_nodup_xR : forall ly S W m md, ARh ly S W m md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W m md HAR.
destruct (rk_als ly S W m md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
{ intros [p nn] Hin. destruct (rk_alb_xR ly S W m md p nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  exact (proj1 (req_size_pos nn ltac:(lia))). }
revert Hpw Hpos. generalize (ablocks B ly S). intros l. induction l as [|x l IH]; intros Hpw Hpos; [constructor|].
cbn [map pairwise] in Hpw. destruct Hpw as [H1 H2]. constructor.
- intros Hin. rewrite Forall_forall in H1. pose proof (H1 _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin)) as Hd.
  pose proof (Hpos x (or_introl eq_refl)). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply IH; [exact H2 | intros b Hb; apply Hpos; right; exact Hb].
Qed.
Lemma rk_garr8_aview_xR : forall H (m : word -> option byte) a l j, garr8 SEGS (mrestrict H m) a l -> (j < length l)%nat ->
aview SEGS H m (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H m _ _ Hv Hr). Qed.
Lemma rk_pw_in_xR : forall {A T : Type} (Rq : T -> T -> Prop) (f : A -> T) l x y,
pairwise Rq (map f l) -> In x l -> In y l -> x <> y -> Rq (f x) (f y) \/ Rq (f y) (f x).
Proof.
intros A T Rq f l. induction l as [|a l IH]; intros x y Hp Hx Hy Hxy; [destruct Hx|].
cbn [map pairwise] in Hp. destruct Hp as [H1 H2]. rewrite Forall_forall in H1.
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- exfalso. apply Hxy. reflexivity.
- left. apply H1. apply in_map. exact Hy.
- right. apply H1. apply in_map. exact Hx.
- exact (IH x y H2 Hx Hy Hxy).
Qed.
Lemma rk_blk_apart_xR : forall ly S W m md b1 b2, ARh ly S W m md ->
In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
fst b1 + req_size (snd b1) <= fst b2 \/ fst b2 + req_size (snd b2) <= fst b1.
Proof.
intros ly S W m md [p1 n1] [p2 n2] HAR H1 H2 Hne.
destruct (rk_alb_xR ly S W m md p1 n1 HAR H1) as (_ & _ & _ & _ & _ & Hpw & _).
destruct (rk_pw_in_xR zdisjoint (fun b => (fst b, req_size (snd b))) _ _ _ Hpw H1 H2 Hne) as [Hd | Hd];
unfold zdisjoint in Hd; cbn [fst snd] in *; lia.
Qed.
Lemma rk_mod_sp_xR : forall x, x mod 32 = 0 -> (x - 224) mod 16 = 0.
Proof.
intros x Hx. replace (x - 224) with ((2 * (x / 32) - 14) * 16) by (pose proof (Z.div_mod x 32 ltac:(lia)); lia).
apply Z_mod_mult.
Qed.
Lemma rk_mod_sa_xR : forall g i, g mod 16 = 0 -> (g + 56 * i) mod 8 = 0.
Proof.
intros g i Hg. replace (g + 56 * i) with ((2 * (g / 16) + 7 * i) * 8) by (pose proof (Z.div_mod g 16 ltac:(lia)); lia).
apply Z_mod_mult.
Qed.
Lemma rk_pw_app_xR : forall {T : Type} (Rq : T -> T -> Prop) l1 l2 x y, pairwise Rq (l1 ++ l2) -> In x l1 -> In y l2 -> Rq x y.
Proof.
intros T Rq l1. induction l1 as [|a l1 IH]; intros l2 x y Hp Hx Hy; [destruct Hx|].
cbn [app pairwise] in Hp. destruct Hp as [H1 H2]. rewrite Forall_forall in H1.
destruct Hx as [<- | Hx]; [apply H1; apply in_or_app; right; exact Hy | exact (IH l2 x y H2 Hx Hy)].
Qed.
Lemma rk_frame_blk_apart_xR : forall ly S W m md cid pos p nn, ARh ly S W m md -> In (cid, pos) (frames S) ->
In (p, nn) (ablocks B ly S) ->
frame_addr ly cid pos + fs_frame_bytes cid <= p \/ p + req_size nn <= frame_addr ly cid pos.
Proof.
intros ly S W m md cid pos p nn HAR Hf Hb. destruct (rk_als ly S W m md HAR) as [Hpw _].
pose proof (rk_pw_app_xR zdisjoint _ _ (p, req_size nn) (frame_addr ly cid pos, fs_frame_bytes cid) Hpw
  ltac:(apply (in_map (fun b => (fst b, req_size (snd b))) _ (p, nn)); exact Hb)
  ltac:(apply (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos)); exact Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma rk_nodup_app_disj_xR : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 x HN H1 H2; [destruct H1|].
cbn [app] in HN. apply List.NoDup_cons_iff in HN as [Hna HN].
destruct H1 as [<- | H1]; [apply Hna; apply in_or_app; right; exact H2 | exact (IH l2 x HN H1 H2)].
Qed.
Lemma rk_nodup_app_r_xR : forall {A : Type} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 HN; [exact HN|].
cbn [app] in HN. apply List.NoDup_cons_iff in HN as [_ HN]. exact (IH l2 HN).
Qed.
Lemma rk_view_garr8_xR : forall H (m : word -> option byte) a l k, garr8 SEGS (mrestrict H m) a l -> 0 <= k < Z.of_nat (length l) ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a l k Hg Hk. destruct (Hg (Z.to_nat k) ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r, Z2Nat.id in Hv by lia.
unfold aview. rewrite Hv. discriminate.
Qed.
Lemma rk_garr8_kv_xR : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.
(* the three blocks of entry i the walk reads (table, held array, a key) are three distinct live blocks *)
Lemma rk_perm_entry_xR : forall (X : list (Z * Z)) G T A e C rest k, List.NoDup X ->
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
- intros Heq. rewrite <- !app_assoc in HN3. apply (rk_nodup_app_r_xR (concat (map aentry_blks A))) in HN3. apply (rk_nodup_app_r_xR bp) in HN3. cbn [app] in HN3.
  apply List.NoDup_cons_iff in HN3 as [Hn _]. apply Hn. rewrite Heq. apply in_or_app. left. exact Hkin.
Qed.

Lemma rk_wr_blk_xR : forall cx ly1 S1 W1 m1 md1 X own b nb a,
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
  + exfalso. pose proof (Permutation_NoDup HP1 (rk_ablocks_nodup_xR _ _ _ _ _ HAR)) as HN.
    exact (rk_nodup_app_disj_xR X (gxrest cx) (b, nb) HN HX Hrest).
- right. right. left. exists b, nb. split; [exact Hin1|]. split; [exact Hnin0 | exact Ha].
Qed.

Lemma rk_blk_not_img_xR : forall ly S W m md p nn a, ARh ly S W m md -> In (p, nn) (ablocks B ly S) ->
p <= a < p + req_size nn -> ~ in_img SEGS a.
Proof.
intros ly S W m md p nn a HAR Hin Ha.
exact (proj2 (rk_alc ly S W m md a HAR (or_introl (ex_intro _ p (ex_intro _ nn (conj Hin Ha)))))).
Qed.
Lemma rk_hull_xR : forall F np s, F mod 32 = 0 -> 1 <= np <= 27 ->
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
Lemma rk_vm2_xR : forall H (m m' : word -> option byte) a n v,
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v ->
forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x.
Proof.
intros H m m' a n v H1 H2 x Hx. unfold aview.
pose proof (H1 (Z.to_nat (x - a)) ltac:(lia)) as A1. pose proof (H2 (Z.to_nat (x - a)) ltac:(lia)) as A2.
rewrite Z2Nat.id in A1, A2 by lia. replace (a + (x - a)) with x in A1, A2 by lia. rewrite A1, A2. reflexivity.
Qed.
Lemma rk_sll3_add8_xR : forall x, 0 <= x < 2 ^ 26 ->
alu64 ALU_ADD (alu64 ALU_SLL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 8) = Z_to_bv 64 (8 * x + 8).
Proof.
intros x Hx. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by lia. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (x * 8) (2 ^ 64)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma rk_branch_lt_xR : forall E a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
0 <= va < 2 ^ 63 -> 0 <= vb < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (va <? vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite !bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma rk_nodup_mid_xR : forall {A : Type} (l1 l2 : list A) x y, NoDup (l1 ++ x :: l2) -> In y (l1 ++ l2) -> x <> y.
Proof.
intros A l1 l2 x y HN Hy <-. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN.
exact (List.NoDup_remove_2 _ _ _ HN Hy).
Qed.

(* ==== representation block (RigKeyRep) ==== *)
(* ---- RigKeyRep (prefix rkr_): the relay table's representation at the KEY step. ---- *)

(* ------------------------------------------------------------------ bytes *)
Lemma rkr_nth_le_bytes_xR : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma rkr_garr8_le_xR : forall mm a n z, garr8 SEGS mm a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS mm a n z.
Proof.
intros mm a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, rkr_nth_le_bytes_xR by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma rkr_le_garr8_xR : forall mm a n z, val_mem SEGS mm a n z -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  garr8 SEGS mm a (bzs (Z_to_le_bytes n z)).
Proof.
intros mm a n z Hv Hz j Hj. unfold bzs in Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hj).
rewrite map_nth, rkr_nth_le_bytes_xR by exact Hj. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
split; [|apply Z.mod_pos_bound; lia].
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (Hv j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

(* a byte of a garr8 string, as the reader sees it *)
Lemma rkr_view_xR : forall (W : world SEGS) m a l j, garr8 SEGS (arm W m) a l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv. unfold arm in Hv.
unfold aview. cbv beta. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. repeat rewrite (Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.

Lemma rkr_bz0_xR : bz (Z_to_bv 8 0) = 0.
Proof. unfold bz. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma rkr_bz_nz_xR : forall b, b <> Z_to_bv 8 0 -> bz b <> 0.
Proof. intros b Hb Hz. apply Hb. apply bv_eq. rewrite <- rkr_bz0_xR in Hz. exact Hz. Qed.

Lemma rkr_nth_key_xR : forall (kt : list byte) j, (j < length kt)%nat ->
  nth j (bzs (kt ++ [Z_to_bv 8 0])) 0 = bz (nth j kt (Z_to_bv 8 0)).
Proof.
intros kt j Hj. unfold bzs. rewrite map_app, app_nth1 by (rewrite length_map; exact Hj).
rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). apply map_nth.
Qed.

Lemma rkr_nth_key_end_xR : forall (kt : list byte), nth (length kt) (bzs (kt ++ [Z_to_bv 8 0])) 0 = 0.
Proof.
intros kt. unfold bzs. rewrite map_app, app_nth2 by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag.
cbn [nth map]. exact rkr_bz0_xR.
Qed.

Lemma rkr_garr8_app3_xR : forall mm a (A M C : list byte),
  garr8 SEGS mm a (bzs (A ++ M ++ C)) <->
  garr8 SEGS mm a (bzs A) /\ garr8 SEGS mm (a + Z.of_nat (length A)) (bzs M) /\
  garr8 SEGS mm (a + Z.of_nat (length A) + Z.of_nat (length M)) (bzs C).
Proof. intros mm a A M C. unfold bzs. rewrite !map_app, !garr8_app, !length_map. reflexivity. Qed.

(* ------------------------------------------------------------------ the held keys' pointer array *)
Lemma rkr_kp_app_xR : forall K1 K2, key_ptrs (K1 ++ K2) = key_ptrs K1 ++ key_ptrs K2.
Proof. intros K1 K2. unfold key_ptrs. rewrite map_app, concat_app. reflexivity. Qed.

Lemma rkr_key_ptrs_len_xR : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
rewrite relay_instance_gone_b_lem.rigl_kp_cons, length_app, IH, Mem.length_le8. cbn [length]. lia.
Qed.

Lemma rkr_key_ptr_xR : forall mm hp ks j, garr8 SEGS mm hp (bzs (key_ptrs ks)) -> (j < length ks)%nat ->
  0 <= key_addr (nth j ks (0, [], [])) < 2 ^ 64 ->
  val_mem SEGS mm (hp + 8 * Z.of_nat j) 8 (key_addr (nth j ks (0, [], []))).
Proof.
intros mm hp ks j Hg Hj Hk.
destruct (nth_split ks (0, [], []) Hj) as (l1 & l2 & E & L1).
rewrite E, rkr_kp_app_xR, relay_instance_gone_b_lem.rigl_kp_cons in Hg.
apply rkr_garr8_app3_xR in Hg as (_ & Hg & _). rewrite rkr_key_ptrs_len_xR, L1 in Hg.
replace (hp + 8 * Z.of_nat j) with (hp + Z.of_nat (8 * j)) by lia.
apply rkr_garr8_le_xR; [|lia].
unfold Mem.le8, word_to_le_bytes in Hg. rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

Lemma rkr_set_nth_mid_xR : forall {A} (l1 : list A) y v r, set_nth (length l1) v (l1 ++ y :: r) = l1 ++ v :: r.
Proof. intros A l1. induction l1 as [|h t IH]; intros y v r; cbn [length app set_nth]; [reflexivity|]. f_equal. apply IH. Qed.

Lemma rkr_nth_last_xR : forall {A} (l : list A) z d, nth (length (l ++ [z]) - 1) (l ++ [z]) d = z.
Proof.
intros A l z d. rewrite length_app. cbn [length]. replace (length l + 1 - 1)%nat with (length l) by lia.
rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

(* swap_remove n: the last element leaves (n the last index), or moves into slot n *)
Lemma rkr_swap_shape_xR : forall {A} (d : A) n l, (n < length l)%nat ->
  exists l1 y l2, l = l1 ++ y :: l2 /\ length l1 = n /\
  ((l2 = [] /\ swap_remove d n l = l1) \/
   (exists l3 z, l2 = l3 ++ [z] /\ swap_remove d n l = l1 ++ z :: l3)).
Proof.
intros A d n l Hn. destruct (nth_split l d Hn) as (l1 & l2 & E & L1).
remember (nth n l d) as y eqn:Ey. clear Ey. subst l n.
exists l1, y, l2. split; [reflexivity|]. split; [reflexivity|]. unfold swap_remove.
destruct l2 as [|w l2'].
- left. split; [reflexivity|]. rewrite last_last, rkr_set_nth_mid_xR.
  apply relay_instance_gone_b_lem.rigl_firstn_app_exact. rewrite length_app. cbn [length]. lia.
- right. destruct (@exists_last A (w :: l2') ltac:(discriminate)) as (l3 & z & E2). exists l3, z. split; [exact E2|].
  rewrite E2.
  assert (Hl : last (l1 ++ y :: l3 ++ [z]) d = z).
  { replace (l1 ++ y :: l3 ++ [z]) with ((l1 ++ y :: l3) ++ [z]) by (rewrite <- app_assoc; reflexivity). apply last_last. }
  rewrite Hl, rkr_set_nth_mid_xR.
  replace (l1 ++ z :: l3 ++ [z]) with ((l1 ++ z :: l3) ++ [z]) by (rewrite <- app_assoc; reflexivity).
  apply relay_instance_gone_b_lem.rigl_firstn_app_exact.
  rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. lia.
Qed.

(* ------------------------------------------------------------------ the entry's bytes *)
(* the 56 bytes of entry_keys e ks: 40 that do not depend on the keys, held, nheld = |ks|, pad2 *)
Lemma rkr_eb_shape_xR : forall e, length (re_pad1 e) = 4%nat -> exists X, length X = 40%nat /\
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
Lemma rkr_pw_perm_xR : forall (l l' : list (Z * Z)), Permutation l l' -> pairwise zdisjoint l -> pairwise zdisjoint l'.
Proof.
intros l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; intros Hp.
- exact Hp.
- cbn [pairwise] in Hp |- *. destruct Hp as [Hf Hp]. split; [|exact (IH Hp)].
  rewrite Forall_forall in Hf |- *. intros z Hz. apply Hf. exact (Permutation_in _ (Permutation_sym HP) Hz).
- cbn [pairwise] in Hp |- *. destruct Hp as [Hf1 [Hf2 Hp]]. apply Forall_cons_iff in Hf1 as [Hyx Hf1].
  split; [apply Forall_cons; [unfold zdisjoint in *; lia | exact Hf2] | split; [exact Hf1 | exact Hp]].
- exact (IH2 (IH1 Hp)).
Qed.

Lemma rkr_pw_mid_xR : forall (A C : list (Z * Z)) h y, pairwise zdisjoint (A ++ h :: C) -> In y (A ++ C) -> zdisjoint h y.
Proof.
induction A as [|a A IH]; intros C h y HP Hy; cbn [app pairwise] in HP, Hy.
- destruct HP as [Hf _]. rewrite Forall_forall in Hf. exact (Hf y Hy).
- destruct HP as [Hf HP]. destruct Hy as [<- | Hy].
  + rewrite Forall_forall in Hf.
    pose proof (Hf h ltac:(apply in_or_app; right; left; reflexivity)) as Hd. unfold zdisjoint in *. lia.
  + exact (IH C h y HP Hy).
Qed.

Lemma rkr_pw_mid4_xR : forall (CP Bx Kx CQ : list (Z * Z)) h y,
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (CP ++ (Bx ++ h :: Kx) ++ CQ)) ->
  In y (CP ++ CQ ++ Bx ++ Kx) -> zdisjoint (fst h, req_size (snd h)) (fst y, req_size (snd y)).
Proof.
intros CP Bx Kx CQ h y HP Hy.
replace (CP ++ (Bx ++ h :: Kx) ++ CQ) with ((CP ++ Bx) ++ h :: (Kx ++ CQ)) in HP by (rewrite <- !app_assoc; reflexivity).
rewrite map_app in HP. cbn [map] in HP.
apply (rkr_pw_mid_xR _ _ _ _ HP).
rewrite <- map_app. apply (in_map (fun b => (fst b, req_size (snd b)))).
rewrite !in_app_iff in Hy |- *. tauto.
Qed.

(* the relay's blocks pairwise apart: a byte of an entry's block is off the table, and a byte of any block but the
   held array's own is off entry e's held block *)
Lemma rkr_disj_xR : forall G0 pre e ks post, re_hp e <> 0 ->
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
  pose proof (rkr_pw_mid4_xR _ _ _ _ (re_hp e, re_kh e) b PR Hb) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (RQ b a Ha) in Hd. lia.
Qed.

(* a byte an entry's predicate reads lies in one of the entry's blocks *)
Lemma rkr_fp_blk_xR : forall ly S W m e, aentry_ok B ly S W m e ->
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
    * unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, rkr_key_ptrs_len_xR in Ha. unfold re_nheld in Hk1. lia.
- apply in_map_iff in Hr as (k & <- & Hk). exists (key_addr k, Z.of_nat (length (key_text k)) + 1). split.
  + unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))). exact Hk.
  + unfold gfp, bzs in Ha. cbn [fst snd] in Ha |- *. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia.
Qed.

(* ------------------------------------------------------------------ 1. entry i, as KEY reads it *)
Lemma rkr_entry_at_xR : forall ly S W m md G0 pre e ks post n,
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
destruct (rk_alb_xR ly S W m md G0 ATABLE HAR H8) as (HG16 & HG4 & HGc & _ & HGp & _ & _).
change (req_size ATABLE) with 896 in HGc, HGp.
destruct (rk_alb_xR ly S W m md _ _ HAR Hhin) as (_ & Hh4 & Hhc & _ & Hhpres & _ & Hkh0).
pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hrkh].
pose proof alloc_ceiling_val as [[_ Hceil] _].
rewrite Forall_forall in E15.
assert (KB : forall k, In k ks -> 0 <= key_addr k < 2 ^ 64).
{ intros k Hk. destruct (E15 k Hk) as (K1 & _).
  destruct (rk_alb_xR ly S W m md _ _ HAR K1) as (_ & K4 & Kc & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Kr]. lia. }
destruct (rkr_eb_shape_xR e E3) as (X & HX & EX).
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
{ unfold Mem.le8, word_to_le_bytes in Ghp. rewrite unsigned_lit_small in Ghp by lia. apply rkr_garr8_le_xR; [exact Ghp | lia]. }
split.
{ unfold Mem.le4 in Gnh. rewrite unsigned_lit_small in Gnh by lia. apply rkr_garr8_le_xR; [exact Gnh | lia]. }
split.
{ intros i Hi. unfold arm. apply apresent_writable. apply (proj1 (HGp (SA + i) ltac:(unfold AENT, ATABLE in *; lia))). }
split; [exact Hhp|]. split; [exact Hhin|]. split; [exact Hkh|]. split; [exact Hgp|].
split.
{ intros i Hi. unfold arm. apply apresent_writable. apply (proj1 (Hhpres (re_hp e + i) ltac:(lia))). }
split.
{ intros j Hj. apply rkr_key_ptr_xR; [exact Hgp | exact Hj | apply KB; apply nth_In; exact Hj]. }
destruct (E15 (nth n ks (0, [], [])) (nth_In _ _ Hn)) as (K1 & K2 & K3 & K4).
split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact E11 | exact E13].
Qed.

(* ------------------------------------------------------------------ 2. the relay after KEY's end-and-move *)
(* Premises beyond the first text (the parent's KEY call site has them: GLIVE's ARx at the old state, GBASE's
   rg_place, GIN's Permutation): without them the global cells could overlap the two stored cells, or the held
   block the table or a key, and the lemma is false. *)
Lemma rkr_arelay_swap_xR : forall ly S W m md ly' S' W' m' G0 pre e ks post n rest,
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
destruct (rk_alb_xR ly S W m md G0 ATABLE HAR H8) as (_ & _ & _ & _ & _ & HPW & _).
destruct (rk_alb_xR ly S W m md _ _ HAR Hhin) as (_ & Hh4 & Hhc & _ & _ & _ & Hkh0).
pose proof alloc_ceiling_val as [[_ Hceil] _].
rewrite Forall_forall in E15.
assert (KB : forall k, In k ks -> 0 <= key_addr k < 2 ^ 64).
{ intros k Hk. destruct (E15 k Hk) as (K1 & _).
  destruct (rk_alb_xR ly S W m md _ _ HAR K1) as (_ & K4 & Kc & _).
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Kr]. lia. }
(* the relay's blocks are pairwise apart (ARx's blocks law, through the Permutation) *)
assert (PW : pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (arelay_blks G0 (pre ++ entry_keys e ks :: post)))).
{ pose proof (rkr_pw_perm_xR _ _ (Permutation_map (fun b => (fst b, req_size (snd b))) HP) HPW) as Hq.
  rewrite map_app in Hq. exact (proj1 (pairwise_app_l _ _ _ Hq)). }
destruct (rkr_disj_xR G0 pre e ks post Hhp PW) as [DT DH].
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
  change (req_size ATABLE) with 896 in O1.
  unfold ATABLE. split; lia. }
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
    by (unfold bzs in Ha; rewrite length_map, rkr_key_ptrs_len_xR, Hlen' in Ha; lia).
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
{ destruct (rkr_eb_shape_xR e E3) as (X & HX & EX).
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
  rewrite EN. rewrite EO in T3. apply rkr_garr8_app3_xR in T3 as (TA & TM & TC).
  rewrite Mem.length_le4 in TC. apply rkr_garr8_app3_xR. rewrite Mem.length_le4.
  split; [|split].
  - apply (akept_garr8 W m); [|exact TA]. intros a Ha. unfold bzs in Ha. rewrite length_map in Ha.
    apply KT; [unfold ATABLE, AENT in *; lia | lia].
  - rewrite HLA. replace (G0 + (SA - G0 + 48)) with (SA + 48) by lia.
    unfold Mem.le4. rewrite unsigned_lit_small by lia. apply rkr_le_garr8_xR; [exact Hnh | lia].
  - apply (akept_garr8 W m); [|exact TC]. intros a Ha. unfold bzs in Ha. rewrite length_map in Ha.
    apply KT; [unfold ATABLE in *; lia | lia]. }
split.
(* the entries *)
{ apply Forall_app. split; [|apply Forall_cons].
  - rewrite Forall_forall. intros e0 He0. rewrite Forall_forall in HFpre.
    apply (aentry_ok_kept B ly S W m); [exact (HFpre e0 He0) | |].
    + intros r Hr a Ha. destruct (rkr_fp_blk_xR ly S W m e0 (HFpre e0 He0) r Hr a Ha) as (b & Hb & Hab).
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
      destruct (rkr_swap_shape_xR (0, [], []) n ks Hn) as (l1 & y & l2 & Eks & Hl1 & [(-> & Esw) | (l3 & z & -> & Esw)]);
        rewrite Esw in Eks'; subst ks'.
      - (* n was the last index: slot n leaves the array *)
        rewrite Eks, rkr_kp_app_xR in Hgp. unfold bzs in Hgp. rewrite map_app in Hgp. apply garr8_app in Hgp as [Hg1 _].
        apply (akept_garr8 W m); [|exact Hg1]. intros a Ha. apply KH; [exact Ha|].
        unfold bzs in Ha. rewrite length_map, rkr_key_ptrs_len_xR in Ha. lia.
      - (* the last key moved into slot n *)
        assert (Eks2 : ks = (l1 ++ y :: l3) ++ [z]) by (rewrite Eks, <- app_assoc; reflexivity).
        assert (Hz : In z ks) by (rewrite Eks2; apply in_or_app; right; left; reflexivity).
        rewrite Eks2, rkr_nth_last_xR in Hslot.
        rewrite Eks, rkr_kp_app_xR, relay_instance_gone_b_lem.rigl_kp_cons, rkr_kp_app_xR in Hgp.
        apply rkr_garr8_app3_xR in Hgp as (Hg1 & _ & Hg3).
        unfold bzs in Hg3. rewrite map_app in Hg3. apply garr8_app in Hg3 as [Hg3 _].
        rewrite Mem.length_le8 in Hg3.
        rewrite rkr_kp_app_xR, relay_instance_gone_b_lem.rigl_kp_cons. apply rkr_garr8_app3_xR. rewrite Mem.length_le8.
        split; [|split].
        + apply (akept_garr8 W m); [|exact Hg1]. intros a Ha. unfold bzs in Ha. rewrite length_map, rkr_key_ptrs_len_xR in Ha.
          apply KH; [unfold bzs; rewrite length_map, rkr_key_ptrs_len_xR, length_app; cbn [length]; lia | lia].
        + rewrite rkr_key_ptrs_len_xR, Hl1. replace (re_hp e + Z.of_nat (8 * n)) with (re_hp e + 8 * Z.of_nat n) by lia.
          unfold Mem.le8, word_to_le_bytes. rewrite unsigned_lit_small by exact (KB z Hz).
          apply rkr_le_garr8_xR; [exact Hslot | pose proof (KB z Hz); lia].
        + apply (akept_garr8 W m); [|exact Hg3]. intros a Ha. unfold bzs in Ha. rewrite length_map, !rkr_key_ptrs_len_xR in Ha.
          apply KH; [unfold bzs; rewrite length_map, rkr_key_ptrs_len_xR, length_app; cbn [length]; lia | lia]. }
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
      intros r Hr a Ha. destruct (rkr_fp_blk_xR ly S W m e0 (HFpost e0 He0) r Hr a Ha) as (b & Hb & Hab).
      exact (KO r a b (INE e0 r He0' Hr) Ha (OBQ e0 b He0 Hb) Hab).
    + intros b Hb. apply (BLE e0 b); [apply in_or_app; right; right; exact He0 | exact Hb]. }
(* arelay_at's 12th conjunct (the kit's W_rep: NoDup of the fds, and no entry block is the table): the fds as before;
   an entry's blocks after the swap are among its blocks before (its keys are a sublist: rig_swap_incl) *)
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
Lemma rkr_agree_xR : forall (W : world SEGS) m x y (kt : list byte) (pre : list Z),
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
    + pose proof (rkr_view_xR W m y _ i Hy ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
      rewrite app_nth1 in Hv by lia. exact Hv.
    + lia.
    + intros j' Hj' E. rewrite <- (Z2Nat.id j') in E by lia.
      rewrite (IH ltac:(lia) (Z.to_nat j') ltac:(lia)) in E.
      injection E as E. apply Hpz. rewrite <- E. apply nth_In. lia. }
  assert (HL : (length pre <= length kt)%nat).
  { destruct (Nat.le_gt_cases (length pre) (length kt)) as [H|H]; [exact H|exfalso].
    pose proof (P (length pre) (le_n _) (length kt) H) as E1.
    pose proof (rkr_view_xR W m x _ (length kt) Hx ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as E2.
    rewrite rkr_nth_key_end_xR in E2. rewrite E1 in E2. injection E2 as E2. apply Hpz. rewrite <- E2. apply nth_In. exact H. }
  unfold has_prefix.
  replace (firstn (length pre) (bzs kt)) with pre; [apply list_eqb_refl|].
  symmetry. apply (nth_ext _ _ 0 0).
  + rewrite length_firstn. unfold bzs. rewrite length_map. lia.
  + intros j Hj. rewrite length_firstn in Hj. unfold bzs in Hj. rewrite length_map in Hj.
    rewrite relay_instance_gone_b_lem.rigl_nth_firstn by lia.
    pose proof (rkr_view_xR W m x _ j Hx ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as E2.
    rewrite (P (length pre) (le_n _) j ltac:(lia)) in E2.
    unfold bzs in E2 |- *. rewrite map_app, app_nth1 in E2 by (rewrite length_map; lia).
    injection E2 as E2. symmetry. exact E2.
- intros Hh i Hi _.
  unfold has_prefix in Hh. apply list_eqb_true in Hh.
  assert (HL : (length pre <= length kt)%nat).
  { apply (f_equal (@length Z)) in Hh. rewrite length_firstn in Hh. unfold bzs in Hh. rewrite length_map in Hh. lia. }
  rewrite <- (Z2Nat.id i) by lia.
  rewrite (rkr_view_xR W m x _ (Z.to_nat i) Hx ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)).
  rewrite (rkr_view_xR W m y _ (Z.to_nat i) Hy ltac:(rewrite length_app; cbn [length]; lia)).
  f_equal. rewrite app_nth1 by lia. unfold bzs. rewrite map_app, app_nth1 by (rewrite length_map; lia).
  rewrite <- Hh. rewrite relay_instance_gone_b_lem.rigl_nth_firstn by lia. reflexivity.
Qed.

Lemma rkr_first_key_xR : forall (W : world SEGS) m x (kt : list byte) n, 0 <= n ->
  garr8 SEGS (arm W m) x (bzs (kt ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) kt ->
  first_byte SEGS W m x n 0 (Z.min (Z.of_nat (length kt)) n).
Proof.
intros W m x kt n Hn Hg Hnz. unfold first_byte. split; [lia|]. split.
- intros i Hi. assert (Hj : (Z.to_nat i < length kt)%nat) by lia.
  pose proof (rkr_view_xR W m x _ (Z.to_nat i) Hg ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as Hv.
  rewrite Z2Nat.id in Hv by lia. rewrite rkr_nth_key_xR in Hv by exact Hj.
  eexists. split; [exact Hv|]. apply rkr_bz_nz_xR. intros E. apply Hnz. rewrite <- E. apply nth_In. exact Hj.
- intros Hlt. assert (HL : Z.of_nat (length kt) < n) by lia. rewrite Z.min_l by lia.
  pose proof (rkr_view_xR W m x _ (length kt) Hg ltac:(unfold bzs; rewrite length_map, length_app; cbn [length]; lia)) as Hv.
  rewrite rkr_nth_key_end_xR in Hv. exact Hv.
Qed.

Lemma rkr_first_pre_xR : forall (W : world SEGS) m y (pre : list Z),
  garr8 SEGS (arm W m) y (pre ++ [0]) -> ~ In 0 pre ->
  first_byte SEGS W m y (Z.of_nat (length pre)) 0 (Z.of_nat (length pre)).
Proof.
intros W m y pre Hg Hnz. unfold first_byte. split; [lia|]. split; [|intros H; exfalso; lia].
intros i Hi. assert (Hj : (Z.to_nat i < length pre)%nat) by lia.
pose proof (rkr_view_xR W m y _ (Z.to_nat i) Hg ltac:(rewrite length_app; cbn [length]; lia)) as Hv.
rewrite Z2Nat.id in Hv by lia. rewrite app_nth1 in Hv by exact Hj.
eexists. split; [exact Hv|]. intros E. apply Hnz. rewrite <- E. apply nth_In. exact Hj.
Qed.

(* ------------------------------------------------------------------ 6. the prefix "param_gesture <id> " *)
Lemma rkr_digits_xR : forall f x acc, 0 <= x -> ~ In 0 acc ->
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

Lemma rkr_digits_le_xR : forall f x acc, (length (printf_facts_c.pf_digits f x acc) <= length acc + f)%nat.
Proof.
induction f as [|f IH]; intros x acc; cbn [printf_facts_c.pf_digits]; [lia|].
destruct (x <? 10); [cbn [length]; lia|]. specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma rkr_digits11_xR : forall x, 0 <= x ->
  ~ In 0 (printf_facts_c.pf_digits 11 x []) /\ (1 <= length (printf_facts_c.pf_digits 11 x []) <= 11)%nat.
Proof.
intros x Hx. destruct (rkr_digits_xR 11 x [] Hx (fun H => H)) as [H1 _]. split; [exact H1|].
pose proof (rkr_digits_le_xR 11 x []) as H3. cbn [length] in H3. split; [|lia].
change (printf_facts_c.pf_digits 11 x []) with
  (if x <? 10 then [48 + x] else printf_facts_c.pf_digits 10 (x / 10) [48 + x mod 10]).
destruct (x <? 10) eqn:E; [cbn [length]; lia|].
apply Z.ltb_ge in E.
destruct (rkr_digits_xR 10 (x / 10) [48 + x mod 10]) as [_ H2].
- apply Z.div_pos; lia.
- assert (Hm : 0 <= x mod 10) by (apply Z.mod_pos_bound; lia). intros [Hd|[]]; lia.
- cbn [length] in H2. lia.
Qed.

Lemma rkr_pre_nz_xR : forall cx, ~ In 0 (gpre cx) /\ (16 <= length (gpre cx))%nat /\ (length (gpre cx) <= 27)%nat.
Proof.
intros cx. unfold gpre, relay_instance_gone_b_c.instance_prefix.
assert (HD : ~ In 0 (printf_facts_c.pf_dec (gxID cx)) /\
             (1 <= length (printf_facts_c.pf_dec (gxID cx)) <= 12)%nat).
{ unfold printf_facts_c.pf_dec. destruct (gxID cx <? 0) eqn:E.
  - apply Z.ltb_lt in E. destruct (rkr_digits11_xR (- gxID cx) ltac:(lia)) as [H1 H2].
    split; [intros [H|H]; [lia | exact (H1 H)] | cbn [length]; lia].
  - apply Z.ltb_ge in E. destruct (rkr_digits11_xR (gxID cx) E) as [H1 H2]. split; [exact H1 | lia]. }
destruct HD as [HD1 HD2]. split; [|split].
- rewrite !in_app_iff. intros [H|[H|[H|H]]].
  + unfold RelayModel.K_GESTURE in H. cbn in H. lia.
  + cbn in H. lia.
  + exact (HD1 H).
  + cbn in H. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
- rewrite !length_app. unfold RelayModel.K_GESTURE. cbn [length]. lia.
Qed.
End wR.

End c.
End b.
End a.
