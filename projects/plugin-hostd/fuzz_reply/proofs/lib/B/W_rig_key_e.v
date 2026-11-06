(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE-B segment KEY of fuzz_reply's relay_instance_gone: the end arm's calls
   (gesture_end, free) over the walk's journal at G_RIG, after W4's image-B lib/B/W_gesture_end.v and
   lib/B/W_gse_loop.v (Qed), and the frame-pointer chain at a call from the loop's frame (k3's lib/A/W_rig_top.v
   tp_achain_call).  Proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), the RIGX round on
   image B: the end arm's calls over any allocator relation ARx with its laws and the room record RP, against the cx
   file's generic Section (lib/B/W_relay_instance_gone_cx.v; its Section c copied below), as the image-A twin's
   conversion (lib/A/W_rig_key.v rk_callS / rk_ge_call / rk_free).  Every ARx state is read at the empty head set
   (HP0: ARh below, with Local wrappers of the laws), so each journal runs from [] to [] (W_journal_x.v
   ajournal_gx_x; a callee's post head set is brought to [] by rk_jhp0 / HP0 as it arrives); the walk's journal is
   at the kit's RIG_STK_x (= RIG_STK + 128).  gesture_end is called at ge_spec_x: its room premise
   rp_RM RP Sc (ge's MT_rk charge + kr) and its count premise cnt_ok_pk RP ge_pk are rk_ge's premises, its post's
   rp_RM RP S2 kr rk_ge's conclusion; the free is afree_cf_rule_c_x (W_journal_x.v Section hc) with rp_RM (1 + kr)
   and cnt_ok, its post's rp_RM RP S2 kr returned the same way, so the caller threads the room and the counts.  The
   journal's image clause exempts PST: rk_keep_img takes `~ Exists (in_zr a) PST`. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rig_key_r.
(* route R: a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* ---- list facts for the end arm's block lists ---- *)
Definition rk_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma rk_cnt_cons : forall (a x : Z * Z) l,
  count_occ rk_dec (a :: l) x = ((if rk_dec a x then 1 else 0) + count_occ rk_dec l x)%nat.
Proof. intros a x l. cbn [count_occ]. destruct (rk_dec a x); lia. Qed.
Lemma rk_cnt_nil : forall x, count_occ rk_dec [] x = 0%nat.
Proof. reflexivity. Qed.
(* the ended key's block leaves the entry's blocks; the moved key stays *)
Lemma rk_perm_keys : forall (A C : list rentry) e ks n, (n < length ks)%nat ->
  Permutation (concat (map aentry_blks (A ++ entry_keys e ks :: C)))
    ((key_addr (nth n ks (0, [], [])), Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ::
     concat (map aentry_blks (A ++ entry_keys e (swap_remove (0, [], []) n ks) :: C))).
Proof.
intros A C e ks n Hn.
pose proof (Permutation_map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1))
  (relay_instance_gone_b_lem.rigl_swap_perm (0, [], []) n ks Hn)) as HPk. cbn [map] in HPk.
assert (AE : forall ks0, aentry_blks (entry_keys e ks0) =
  ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++ (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)])) ++
  map (fun k0 => (key_addr k0, Z.of_nat (length (key_text k0)) + 1)) ks0)
  by (intros ks0; unfold aentry_blks; cbn [entry_keys re_cap re_buf re_hp re_kh re_keys]; rewrite app_assoc; reflexivity).
rewrite !map_app, !concat_app. cbn [map concat]. rewrite !AE.
apply (proj2 (Permutation_count_occ rk_dec _ _)). intros y.
pose proof (proj1 (Permutation_count_occ rk_dec _ _) HPk y) as Hc.
repeat (rewrite count_occ_app in * || rewrite rk_cnt_cons in *). lia.
Qed.
Lemma rk_pres_reg : forall regs regs' r (b : bv 5), aregs_preserved regs regs' -> bv_unsigned b = r -> acallee_saved r ->
  getr regs' b = getr regs b.
Proof. intros regs regs' r b H <- Hr. rewrite <- (Z_to_bv_bv_unsigned _ b). apply H. exact Hr. Qed.

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
#[local] Notation rk_ablocks_nodup := (W_rig_key_r.rk_ablocks_nodup B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_nodup_app_disj := (W_rig_key_r.rk_nodup_app_disj B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).
#[local] Notation rk_blk_apart := (W_rig_key_r.rk_blk_apart B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALLOC_TAIL ALOCK AUNLOCK AFREE ASNPRINTF ASTRLEN ASTRNCMP DRAIN GE HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG) (only parsing).

(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state these lemmas read has the head set [], so they state their facts at ARh (= ARx at []) and each
   journal from [] to [].  rk_alb is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's
   argument order. *)
#[local] Notation ARh ly S W mem md := (ARx ly S (@nil Z) W mem md).
Local Lemma rk_jhp0 : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> Hp' = [].
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (HP0 _ _ _ _ _ _ (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
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
Local Definition rk_alo ly S W mem md a (H : ARh ly S W mem md) := alx_owned_image _ _ _ LAWS ly S [] W mem md a H.
Local Definition rk_boi ly S W mem md p n (H : ARh ly S W mem md) := blk_off_imgB_x B ARx LAWS IMGC BLKN ly S [] W mem md p n H.

(* the bytes of " end\0" (HEND5L) through the ROM view *)
Lemma rk_end5 : forall W m, rom_view SEGS W m -> garr8 SEGS (arm W m) (VAL A_lit_end5) (bzs END5).
Proof.
intros W m HR j Hj. unfold bzs in Hj. rewrite length_map in Hj. change (length END5) with 5%nat in Hj.
destruct (HEND5L j Hj) as [Hrom Hseg].
pose proof (HR _ Hrom) as Hv. rewrite Hseg in Hv.
destruct (nth_error END5 j) as [b|] eqn:Eb; [|apply nth_error_None in Eb; change (length END5) with 5%nat in Eb; lia].
assert (Hn : nth j (bzs END5) 0 = bz b) by (unfold bzs; apply nth_error_nth; rewrite nth_error_map, Eb; reflexivity).
rewrite Hn. pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. unfold bz.
split; [|lia].
unfold aview in Hv. cbn [option_map] in Hv.
destruct (mbyte SEGS (mrestrict (w_H W) m) (VAL A_lit_end5 + Z.of_nat j)) as [b'|] eqn:Eb'; [|discriminate Hv].
injection Hv as Hv. intros kk Hkk. destruct kk as [|kk]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold arm. rewrite Eb'. f_equal.
rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite <- Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rk_aout_facts : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
0 <= mx <= 255 /\ Z.of_nat (length O) = no /\
((cap = 0 /\ out = 0 /\ no = 0) \/ (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S))).
Proof.
intros ly S W mem c O mx no cap out
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmx & Hno & Hd).
split; [exact Hmx|]. split; [exact Hno|].
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.
(* a byte of a block the walk's journal sees now: in the journal's footprint (the block was live at the entry, so it
   is one of the entry's represented blocks), or in a block made since the entry *)
Lemma rk_fp_blk : forall cx ly1 S1 W1 m1 md1 X b nb a,
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
Permutation (ablocks B ly1 S1) (X ++ gxrest cx) -> In (b, nb) X -> b <= a < b + req_size nb ->
(inFP (gFP cx) a /\ exists b0 n0, In (b0, n0) (ablocks B ly1 S1) /\ b0 <= a < b0 + req_size n0) \/
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

(* a block live at the entry and represented now is one of the entry's represented blocks: its bytes are in the
   walk's journal footprint (free's premise) *)
Lemma rk_fp_orig : forall cx ly1 S1 W1 m1 md1 X b nb,
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
Permutation (ablocks B ly1 S1) (X ++ gxrest cx) -> In (b, nb) X ->
In (b, nb) (ablocks B (gxly cx) (gxS cx)) -> forall i, 0 <= i < req_size nb -> inFP (gFP cx) (b + i).
Proof.
intros cx ly1 S1 W1 m1 md1 X b nb HAR HPZ0 HP1 HX Hin0 i Hi.
apply (Permutation_in _ HPZ0) in Hin0. apply in_app_or in Hin0 as [HX0 | Hrest].
- unfold gFP, rig_fp. apply (inFP_ablocks_fp _ b nb); [exact HX0 | lia].
- exfalso. pose proof (Permutation_NoDup HP1 (rk_ablocks_nodup _ _ _ _ _ HAR)) as HN.
  exact (rk_nodup_app_disj X (gxrest cx) (b, nb) HN HX Hrest).
Qed.


(* ---- calls of program functions and the allocator over the walk's journal (lib/B/W_gesture_end.v gx_callS /
   ajgx_*, lib/B/W_gse_loop.v gsl_keep_blk / gsl_disj / gsl_free, W4's Qed image-B files, at G_RIG; over ARx as the
   image-A twin's lib/A/W_rig_key.v rk_callS / rk_gx_keep_high / rkk_jx_*: W_journal_x.v's _x journal lemmas) ---- *)
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
(* a journal keeps the image bytes outside its globals, its footprint and the program statics PST (the image clause
   exempts PST) *)
Lemma rk_keep_img : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
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
Lemma rk_keep_high : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
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
pose proof (pa_img_range _ Hi') as HR. lia.
Qed.
(* a journal keeps the bytes of the caller's frames outside its footprint *)
Lemma rk_keep_frm : forall G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a (HS0 & HX0 & (memS & HJi & Hag) & _) Hfr Hr Hf Ha Hg.
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hfr Hr Hf).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. exact Hg.
Qed.
Lemma rk_ly_top : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k -> ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
Lemma rk_fp_spares : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
Lemma rk_disj : forall ly' S' (W' : world SEGS) mem' md' p n q m,
ARh ly' S' W' mem' md' -> In (p, n) (ablocks B ly' S') -> In (q, m) (ablocks B ly' S') -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly' S' W' mem' md' p n q m HAR H1 H2 Hne.
exact (rk_blk_apart ly' S' W' mem' md' (p, n) (q, m) HAR H1 H2 Hne).
Qed.
Lemma rk_not_owned : forall ly S W mem md a, ARh ly S W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. intros ly S W mem md a HAR Hi Ho Hown. apply Ho. exact (proj1 (rk_alo ly S W mem md a HAR Hi) Hown). Qed.

(* free (pa) of a live block (pa, n), on the walk's journal; the block's bytes are in the journal's footprint when
   the block was live at the journal's start (afree_cf_rule_c_x's premises, as stated: the caller context is the free's
   trace, its return address then the chain's; the room record's rp_RM RP Sc (1 + kr) and the live counts cnt_ok are
   the caller's, the post's room rp_RM RP S2 kr returned) *)
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
apres_kept B W memT W2 mem2).
Proof.
intros G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
  (H0 & H1 & (memS & HJi & Hag) & Hout) Hin H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCTX HFP MOK kr HRM HCN.
rewrite !Z.add_0_r in HJi.
assert (HSR : ly_bot lyc + ACALL_PREFIX < spZ regsT) by (eapply aj_stack_room_x; [exact HJi | exact Hsp | exact Hst]).
eapply SRr_mono.
{ exact (AFREE W regsT memT STK sp0 FP ly S [] W0 memS md own lyc Sc [] mdc k pa n o raw ch kr HJi Hin H10 Hsp Hal Hneg Hst
    HSR Hgp Htp Hra Hraw Hch HCTX HRM HCN HFP MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & Hfr & HK & HM & HRM2 & HE & HPr).
assert (EH2 : Hp2 = []) by (exact (HP0 _ _ _ _ _ _ (proj1 HJ2))). subst Hp2.
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
split; [exact HP2|]. split; [exists l1, l2; split; [exact E1 | exact E2]|]. split; [exact Hfr|].
split; [exact HK|]. split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
intros a Hi Ho He Hp. apply HPr; [exact Hi | exact (rk_not_owned _ _ _ _ _ a (proj1 HJi) Hi Ho)
| exact (rk_not_owned _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hp].
intros Hr. pose proof (rk_boi lyc Sc W memT mdc pa n (proj1 HJi) Hin) as Hoff.
pose proof (pa_img_range a Hi). lia.
Qed.

(* the frame-pointer chain at a call from the loop's frame, its frame record named, when the entry's frame lies below
   the layout top: s0 = the entry sp, its saved ra / s0 at the top of the frame (g_saved's last two slots) pushed on
   the caller's chain (afn_pre_x at the entry) *)
Lemma rk_achainp : forall cx ly1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> g_saved cx W1 m1 -> ly_top ly1 = ly_top (gxly cx) ->
(forall a, gsp0 cx <= a < 2 ^ 64 -> aview SEGS (w_H W1) m1 a = aview SEGS (w_H (gxW cx)) (gxmem cx) a) ->
gsp0 cx < ly_top (gxly cx) - 16 ->
achain ly1 (aview SEGS (w_H W1) m1) (gsp1 cx) (gsp0 cx) ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx).
Proof.
intros cx ly1 W1 m1 HB HSV Htop Hk Hlt.
pose proof HB as (HPRE & H32 & _).
pose proof HPRE as (_ & _ & Hra & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (_ & _ & Hs3 & Hs4 & _ & Hs6 & _ & Hs8 & Hs9).
assert (WS : RIG_STK_x = 17232) by reflexivity.
fold (gsp0 cx) in Hs4, Hs8, Hch.
apply (achain_ly_top (gxly cx)); [exact Htop|].
apply (achain_push (gxly cx) (aview SEGS (w_H (gxW cx)) (gxmem cx)) _ (gsp0 cx) (s0Z (gxregs cx)) (raZ (gxregs cx)) (gxch cx) (gsp1 cx) Hch).
- lia.
- exact Hk.
- replace (gsp0 cx - 8) with (gsp1 cx + 120 + 8 * Z.of_nat 12) by (unfold gsp1, RIG_FRAME; lia).
  apply rdword_of_val_mem; [exact (HSV 12%nat ltac:(lia)) | unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 1)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
- replace (gsp0 cx - 16) with (gsp1 cx + 120 + 8 * Z.of_nat 11) by (unfold gsp1, RIG_FRAME; lia).
  apply rdword_of_val_mem; [exact (HSV 11%nat ltac:(lia)) | unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R].
- exact Hra.
- rewrite WS in Hs4. lia.
- pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
  replace (32 * (gsp0 cx / 32)) with ((4 * (gsp0 cx / 32)) * 8) by ring. apply Z_mod_mult.
- exact Hlt.
- unfold gsp1, RIG_FRAME. lia.
Qed.
(* the same chain, unnamed: the empty chain when the entry's frame is at the layout top *)
Lemma rk_achain : forall cx ly1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> g_saved cx W1 m1 -> ly_top ly1 = ly_top (gxly cx) ->
(forall a, gsp0 cx <= a < 2 ^ 64 -> aview SEGS (w_H W1) m1 a = aview SEGS (w_H (gxW cx)) (gxmem cx) a) ->
exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (gsp1 cx) (gsp0 cx) ch1.
Proof.
intros cx ly1 W1 m1 HB HSV Htop Hk.
destruct (Z_lt_le_dec (gsp0 cx) (ly_top (gxly cx) - 16)) as [Hlt | Hge].
- exists ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx). exact (rk_achainp cx ly1 W1 m1 HB HSV Htop Hk Hlt).
- exists []. left. split; [right; left; rewrite Htop; exact Hge | reflexivity].
Qed.

(* gesture_end (key) from the loop's frame (sp = the entry sp - 224), over the walk's journal at G_RIG: GE's
   contract (ge_spec_x) at its entry, its journal (G_SL) returned for the keep facts and, lifted, composed into the
   walk's; GE's room premise (rp_RM at ge's MT_rk charge + kr) and count premise (cnt_ok_pk RP ge_pk) taken, its post's
   room rp_RM RP S2 kr returned *)
Lemma rk_ge : forall W regsc memc mdc sp0 FP ly S W0 mem md own lyc Sc k raw ch1 c O mx no cap out x q m,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ->
spZ regsc = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 - 224) (s0Z regsc) ch1 ->
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
(forall a, inFP (ablocks_fp (aout_blks cap out)) a ->
 (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1 out',
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + k1) /\
 (exists ksl, ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) 0 [] GE_STK (sp0 - 224) (ablocks_fp (aout_blks cap out))
   lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 ksl) /\
 aregs_preserved regsc regs2 /\ apres_kept B W memc W2 mem2 /\
 mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
 (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
   Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
 aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
   (ge_cap c mx no cap (Z.of_nat (length x))) out').
Proof.
intros W regsc memc mdc sp0 FP ly S W0 mem md own lyc Sc k raw ch1 c O mx no cap out x q m
  HJ Hsp H16 Hgp Htp Hra Hraw Hra4 Hch H10 HOUT GK NZ X1 Hq Hqo Hqm G5 HROM ROOM MOK kr HRM HCN HF.
eapply SRr_mono.
{ eapply (rk_callS (G_RIG B RG) W regsc memc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) RIG_STK_x sp0 FP ly S W0 mem md own
    lyc Sc mdc k GE_STK (ablocks_fp (aout_blks cap out)) (-224) raw ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => exists k1 out',
      ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) 0 [] GE_STK (sp0 - 224) (ablocks_fp (aout_blks cap out))
        lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
      apres_kept B W memc W2 mem2 /\
      mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
      (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
        Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) out')
    HGRIG HJ).
  - lia.
  - reflexivity.
  - lia.
  - assert (E1 : GE_STK = 16544) by reflexivity. rewrite E1. lia.
  - assert (E1 : GE_STK = 16544) by reflexivity. assert (E2 : RIG_STK_x = 17232) by reflexivity. rewrite E1, E2. lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - replace (sp0 + -224) with (sp0 - 224) by lia. exact Hch.
  - intros HPRE1. eapply SRr_mono.
    { exact (GE W lyc Sc [] regsc memc mdc ch1 c O mx no cap out q x q m HPRE1 H10 HOUT GK NZ X1 Hq Hqo
        ltac:(lia) ltac:(lia) G5 HROM ROOM MOK kr HRM HCN). }
    cbv beta. intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & out3 & -> & HJ3 & HP3 & HA3 & HM3 & HRM3 & HPm3 & HO3).
    assert (EH3 : Hp3 = []) by (eapply rk_jhp0; exact HJ3). subst Hp3.
    exists ly3, S3, regs3, mem3, md3, k3. split; [rewrite Hra; reflexivity|].
    split; [eapply rig_lift_SL; exact HJ3|]. split; [exact HP3|].
    exists k3, out3. split; [rewrite Hsp in HJ3; exact HJ3|]. split; [exact HA3|]. split; [exact HM3|].
    split; [exact HRM3|]. split; [exact HPm3 | exact HO3].
  - exact HF. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc2 & HP2 & (k1' & out' & HJs & HA & HM & HRM2 & HPm & HO)).
exists ly2, S2, regs2, mem2, md2, k1, out'. split; [reflexivity|]. split; [exact HJ2|].
split; [exists k1'; exact HJs|]. split; [exact HP2|]. split; [exact HA|]. split; [exact HM|]. split; [exact HRM2|].
split; [exact HPm | exact HO].
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the end arm's calls at a world relation R.  The strict lemmas above take every Section
   hypothesis (Default Proof Using "All"), the strict AFREE / DRAIN / GE / ALLOC_TAIL included, so this Section copies
   each of them as X_xR (same statement and proof) under a Default Proof Using that leaves those out.  The lemmas that
   read a journal are lifted: ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the journal lemmas ->
   their _xR twins (W_journal_x.v), gesture_end's contract -> GE_R : ge_spec_xR (W_contract_xR.v), the free rule -> AFREE_R : afree_cf_rule_c_xR .. RO CTX_AFREE R with its call-boundary premise from ARx (RO_ARx), as lib/B/W_gse_loop.v's gsl_*_xR.  The hypothesis list is the cx file's Section wR, verbatim. ---- *)
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
#[local] Notation rk_ablocks_nodup_xR := (W_rig_key_r.rk_ablocks_nodup_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_nodup_app_disj_xR := (W_rig_key_r.rk_nodup_app_disj_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
#[local] Notation rk_blk_apart_xR := (W_rig_key_r.rk_blk_apart_xR B PST ARx MT RP MMAX RG CTX_AFREE LAWS HP0 TL TLF MLAW IMGC BLKN OWNLOW WFx WFL SFREE SMALLOC ASMP ASF FFL MO_FR HGRIG HH41 HH42 HRGP HRGI HROMO ALOCK AUNLOCK ASNPRINTF ASTRLEN ASTRNCMP HEND5L HGOTG HCANR HLIT17 HLIT18 HLIT28 PSTR PSTG R R_trans WLE_R RO RO_ARx AFREE_R GE_R) (only parsing).
(* ==== the generic relation at the empty head set (the image-A twin's lib/A/W_rig_key.v:236-280; Local here, as every
   key file that needs them defines its own) ==== *)
(* HP0: every ARx state these lemmas read has the head set [], so they state their facts at ARh (= ARx at []) and each
   journal from [] to [].  rk_alb_xR is AR_blocks_law's seven conjuncts (alx_blocks' six and BLKN), in the AR walk's
   argument order. *)
Local Lemma rk_jhp0_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> Hp' = [].
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (HP0 _ _ _ _ _ _ (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
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

(* the bytes of " end\0" (HEND5L) through the ROM view *)
Lemma rk_end5_xR : forall W m, rom_view SEGS W m -> garr8 SEGS (arm W m) (VAL A_lit_end5) (bzs END5).
Proof.
intros W m HR j Hj. unfold bzs in Hj. rewrite length_map in Hj. change (length END5) with 5%nat in Hj.
destruct (HEND5L j Hj) as [Hrom Hseg].
pose proof (HR _ Hrom) as Hv. rewrite Hseg in Hv.
destruct (nth_error END5 j) as [b|] eqn:Eb; [|apply nth_error_None in Eb; change (length END5) with 5%nat in Eb; lia].
assert (Hn : nth j (bzs END5) 0 = bz b) by (unfold bzs; apply nth_error_nth; rewrite nth_error_map, Eb; reflexivity).
rewrite Hn. pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. unfold bz.
split; [|lia].
unfold aview in Hv. cbn [option_map] in Hv.
destruct (mbyte SEGS (mrestrict (w_H W) m) (VAL A_lit_end5 + Z.of_nat j)) as [b'|] eqn:Eb'; [|discriminate Hv].
injection Hv as Hv. intros kk Hkk. destruct kk as [|kk]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold arm. rewrite Eb'. f_equal.
rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite <- Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rk_aout_facts_xR : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
0 <= mx <= 255 /\ Z.of_nat (length O) = no /\
((cap = 0 /\ out = 0 /\ no = 0) \/ (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S))).
Proof.
intros ly S W mem c O mx no cap out
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmx & Hno & Hd).
split; [exact Hmx|]. split; [exact Hno|].
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.
(* a byte of a block the walk's journal sees now: in the journal's footprint (the block was live at the entry, so it
   is one of the entry's represented blocks), or in a block made since the entry *)
Lemma rk_fp_blk_xR : forall cx ly1 S1 W1 m1 md1 X b nb a,
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
Permutation (ablocks B ly1 S1) (X ++ gxrest cx) -> In (b, nb) X -> b <= a < b + req_size nb ->
(inFP (gFP cx) a /\ exists b0 n0, In (b0, n0) (ablocks B ly1 S1) /\ b0 <= a < b0 + req_size n0) \/
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
  + exfalso. pose proof (Permutation_NoDup HP1 (rk_ablocks_nodup_xR _ _ _ _ _ HAR)) as HN.
    exact (rk_nodup_app_disj_xR X (gxrest cx) (b, nb) HN HX Hrest).
- right. exists b, nb. split; [exact Hin1|]. split; [exact Hnin0 | exact Ha].
Qed.

(* a block live at the entry and represented now is one of the entry's represented blocks: its bytes are in the
   walk's journal footprint (free's premise) *)
Lemma rk_fp_orig_xR : forall cx ly1 S1 W1 m1 md1 X b nb,
ARh ly1 S1 W1 m1 md1 ->
Permutation (ablocks B (gxly cx) (gxS cx)) (rk_X0 cx ++ gxrest cx) ->
Permutation (ablocks B ly1 S1) (X ++ gxrest cx) -> In (b, nb) X ->
In (b, nb) (ablocks B (gxly cx) (gxS cx)) -> forall i, 0 <= i < req_size nb -> inFP (gFP cx) (b + i).
Proof.
intros cx ly1 S1 W1 m1 md1 X b nb HAR HPZ0 HP1 HX Hin0 i Hi.
apply (Permutation_in _ HPZ0) in Hin0. apply in_app_or in Hin0 as [HX0 | Hrest].
- unfold gFP, rig_fp. apply (inFP_ablocks_fp _ b nb); [exact HX0 | lia].
- exfalso. pose proof (Permutation_NoDup HP1 (rk_ablocks_nodup_xR _ _ _ _ _ HAR)) as HN.
  exact (rk_nodup_app_disj_xR X (gxrest cx) (b, nb) HN HX Hrest).
Qed.


(* ---- calls of program functions and the allocator over the walk's journal (lib/B/W_gesture_end.v gx_callS /
   ajgx_*, lib/B/W_gse_loop.v gsl_keep_blk / gsl_disj / gsl_free, W4's Qed image-B files, at G_RIG; over ARx as the
   image-A twin's lib/A/W_rig_key.v rk_callS_xR / rk_gx_keep_high / rkk_jx_*: W_journal_x.v's _x journal lemmas) ---- *)
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
eapply SRrG_mono.
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
(* a journal keeps the image bytes outside its globals, its footprint and the program statics PST (the image clause
   exempts PST) *)
Lemma rk_keep_img_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
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
Lemma rk_keep_high_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
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
Lemma rk_keep_blk_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
gx_ok SEGS B G -> ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
destruct (rk_alb_xR ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
pose proof asan_consts as (C1 & _).
rewrite unsigned_lit_small in HGa by lia.
destruct (HGx _ HGa) as [Hi' _].
pose proof (rk_boi ly' S' W' mem' md' p n HAR0 H2) as Hoff.
pose proof (pa_img_range _ Hi') as HR. lia.
Qed.
(* a journal keeps the bytes of the caller's frames outside its footprint *)
Lemma rk_keep_frm_xR : forall G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a (HS0 & HX0 & (memS & HJi & Hag) & _) Hfr Hr Hf Ha Hg.
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hfr Hr Hf).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. exact Hg.
Qed.
Lemma rk_ly_top_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k -> ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
Lemma rk_fp_spares_xR : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
Lemma rk_disj_xR : forall ly' S' (W' : world SEGS) mem' md' p n q m,
ARh ly' S' W' mem' md' -> In (p, n) (ablocks B ly' S') -> In (q, m) (ablocks B ly' S') -> (p, n) <> (q, m) ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly' S' W' mem' md' p n q m HAR H1 H2 Hne.
exact (rk_blk_apart_xR ly' S' W' mem' md' (p, n) (q, m) HAR H1 H2 Hne).
Qed.
Lemma rk_not_owned_xR : forall ly S W mem md a, ARh ly S W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. intros ly S W mem md a HAR Hi Ho Hown. apply Ho. exact (proj1 (rk_alo ly S W mem md a HAR Hi) Hown). Qed.

(* free (pa) of a live block (pa, n), on the walk's journal; the block's bytes are in the journal's footprint when
   the block was live at the journal's start (afree_cf_rule_c_x's premises, as stated: the caller context is the free's
   trace, its return address then the chain's; the room record's rp_RM RP Sc (1 + kr) and the live counts cnt_ok are
   the caller's, the post's room rp_RM RP S2 kr returned) *)
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
apres_kept B W memT W2 mem2).
Proof.
intros G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch
  (H0 & H1 & (memS & HJi & Hag) & Hout) Hin H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCTX HFP MOK kr HRM HCN.
rewrite !Z.add_0_r in HJi.
assert (HSR : ly_bot lyc + ACALL_PREFIX < spZ regsT) by (eapply aj_stack_room_xR; [exact HJi | exact Hsp | exact Hst]).
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
eapply SRrG_mono.
{ exact (AFREE_R W regsT memT STK sp0 FP ly S [] W0 memS md own lyc Sc [] mdc k pa n o raw ch kr HJi Hin H10 Hsp Hal Hneg Hst
    HSR Hgp Htp Hra Hraw Hch HRO HCTX HRM HCN HFP MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & Hfr & HK & HM & HRM2 & HE & HPr).
assert (EH2 : Hp2 = []) by (exact (HP0 _ _ _ _ _ _ (proj1 HJ2))). subst Hp2.
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
split; [exact HP2|]. split; [exists l1, l2; split; [exact E1 | exact E2]|]. split; [exact Hfr|].
split; [exact HK|]. split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
intros a Hi Ho He Hp. apply HPr; [exact Hi | exact (rk_not_owned_xR _ _ _ _ _ a (proj1 HJi) Hi Ho)
| exact (rk_not_owned_xR _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hp].
intros Hr. pose proof (rk_boi lyc Sc W memT mdc pa n (proj1 HJi) Hin) as Hoff.
pose proof (pa_img_range a Hi). lia.
Qed.

(* the frame-pointer chain at a call from the loop's frame, its frame record named, when the entry's frame lies below
   the layout top: s0 = the entry sp, its saved ra / s0 at the top of the frame (g_saved's last two slots) pushed on
   the caller's chain (afn_pre_x at the entry) *)
Lemma rk_achainp_xR : forall cx ly1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> g_saved cx W1 m1 -> ly_top ly1 = ly_top (gxly cx) ->
(forall a, gsp0 cx <= a < 2 ^ 64 -> aview SEGS (w_H W1) m1 a = aview SEGS (w_H (gxW cx)) (gxmem cx) a) ->
gsp0 cx < ly_top (gxly cx) - 16 ->
achain ly1 (aview SEGS (w_H W1) m1) (gsp1 cx) (gsp0 cx) ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx).
Proof.
intros cx ly1 W1 m1 HB HSV Htop Hk Hlt.
pose proof HB as (HPRE & H32 & _).
pose proof HPRE as (_ & _ & Hra & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (_ & _ & Hs3 & Hs4 & _ & Hs6 & _ & Hs8 & Hs9).
assert (WS : RIG_STK_x = 17232) by reflexivity.
fold (gsp0 cx) in Hs4, Hs8, Hch.
apply (achain_ly_top (gxly cx)); [exact Htop|].
apply (achain_push (gxly cx) (aview SEGS (w_H (gxW cx)) (gxmem cx)) _ (gsp0 cx) (s0Z (gxregs cx)) (raZ (gxregs cx)) (gxch cx) (gsp1 cx) Hch).
- lia.
- exact Hk.
- replace (gsp0 cx - 8) with (gsp1 cx + 120 + 8 * Z.of_nat 12) by (unfold gsp1, RIG_FRAME; lia).
  apply rdword_of_val_mem; [exact (HSV 12%nat ltac:(lia)) | unfold raZ; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 1)) as Rq; change (bv_modulus 64) with (2 ^ 64) in Rq; exact Rq].
- replace (gsp0 cx - 16) with (gsp1 cx + 120 + 8 * Z.of_nat 11) by (unfold gsp1, RIG_FRAME; lia).
  apply rdword_of_val_mem; [exact (HSV 11%nat ltac:(lia)) | unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (gxregs cx) 8)) as Rq; change (bv_modulus 64) with (2 ^ 64) in Rq; exact Rq].
- exact Hra.
- rewrite WS in Hs4. lia.
- pose proof (Z.div_mod (gsp0 cx) 32 ltac:(lia)) as D. rewrite H32, Z.add_0_r in D. rewrite D.
  replace (32 * (gsp0 cx / 32)) with ((4 * (gsp0 cx / 32)) * 8) by ring. apply Z_mod_mult.
- exact Hlt.
- unfold gsp1, RIG_FRAME. lia.
Qed.
(* the same chain, unnamed: the empty chain when the entry's frame is at the layout top *)
Lemma rk_achain_xR : forall cx ly1 W1 m1,
GBASE B ARx MT RP MMAX RG cx -> g_saved cx W1 m1 -> ly_top ly1 = ly_top (gxly cx) ->
(forall a, gsp0 cx <= a < 2 ^ 64 -> aview SEGS (w_H W1) m1 a = aview SEGS (w_H (gxW cx)) (gxmem cx) a) ->
exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (gsp1 cx) (gsp0 cx) ch1.
Proof.
intros cx ly1 W1 m1 HB HSV Htop Hk.
destruct (Z_lt_le_dec (gsp0 cx) (ly_top (gxly cx) - 16)) as [Hlt | Hge].
- exists ((gsp0 cx, raZ (gxregs cx), s0Z (gxregs cx)) :: gxch cx). exact (rk_achainp_xR cx ly1 W1 m1 HB HSV Htop Hk Hlt).
- exists []. left. split; [right; left; rewrite Htop; exact Hge | reflexivity].
Qed.

(* gesture_end (key) from the loop's frame (sp = the entry sp - 224), over the walk's journal at G_RIG: GE's
   contract (ge_spec_x) at its entry, its journal (G_SL) returned for the keep facts and, lifted, composed into the
   walk's; GE's room premise (rp_RM at ge's MT_rk charge + kr) and count premise (cnt_ok_pk RP ge_pk) taken, its post's
   room rp_RM RP S2 kr returned *)
Lemma rk_ge_xR : forall W regsc memc mdc sp0 FP ly S W0 mem md own lyc Sc k raw ch1 c O mx no cap out x q m,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ->
spZ regsc = sp0 - 224 -> sp0 mod 16 = 0 ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 - 224) (s0Z regsc) ch1 ->
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
(forall a, inFP (ablocks_fp (aout_blks cap out)) a ->
 (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1 out',
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x sp0 FP ly S [] W0 mem md own ly2 S2 [] W2 mem2 md2 (k + k1) /\
 (exists ksl, ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (sp0 - 224) (ablocks_fp (aout_blks cap out))
   lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 ksl) /\
 aregs_preserved regsc regs2 /\ apres_kept B W memc W2 mem2 /\
 mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
 (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
   Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
 aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
   (ge_cap c mx no cap (Z.of_nat (length x))) out').
Proof.
intros W regsc memc mdc sp0 FP ly S W0 mem md own lyc Sc k raw ch1 c O mx no cap out x q m
  HJ Hsp H16 Hgp Htp Hra Hraw Hra4 Hch H10 HOUT GK NZ X1 Hq Hqo Hqm G5 HROM ROOM MOK kr HRM HCN HF.
eapply SRrG_mono.
{ eapply (rk_callS_xR (G_RIG B RG) W regsc memc (Z_to_bv 64 (BASE + AF_fr_gesture_end)) RIG_STK_x sp0 FP ly S W0 mem md own
    lyc Sc mdc k GE_STK (ablocks_fp (aout_blks cap out)) (-224) raw ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => exists k1 out',
      ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (sp0 - 224) (ablocks_fp (aout_blks cap out))
        lyc Sc [] W memc mdc [] ly2 S2 [] W2 mem2 md2 k1 /\
      apres_kept B W memc W2 mem2 /\
      mo_le MT Sc S2 (ge_cost MT c mx no cap (Z.of_nat (length x))) /\ rp_RM RP S2 kr /\
      (exists rest, Permutation (ablocks B lyc Sc) (aout_blks cap out ++ rest) /\
        Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
      aout_at B RG ly2 S2 W2 mem2 (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) out')
    HGRIG HJ).
  - lia.
  - reflexivity.
  - lia.
  - assert (E1 : GE_STK = 16544) by reflexivity. rewrite E1. lia.
  - assert (E1 : GE_STK = 16544) by reflexivity. assert (E2 : RIG_STK_x = 17232) by reflexivity. rewrite E1, E2. lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - replace (sp0 + -224) with (sp0 - 224) by lia. exact Hch.
  - intros HPRE1. eapply SRrG_mono.
    { exact (GE_R W lyc Sc [] regsc memc mdc ch1 c O mx no cap out q x q m HPRE1 H10 HOUT GK NZ X1 Hq Hqo
        ltac:(lia) ltac:(lia) G5 HROM ROOM MOK kr HRM HCN). }
    cbv beta. intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & out3 & -> & HJ3 & HP3 & HA3 & HM3 & HRM3 & HPm3 & HO3).
    assert (EH3 : Hp3 = []) by (eapply rk_jhp0_xR; exact HJ3). subst Hp3.
    exists ly3, S3, regs3, mem3, md3, k3. split; [rewrite Hra; reflexivity|].
    split; [eapply rig_lift_SL_xR; exact HJ3|]. split; [exact HP3|].
    exists k3, out3. split; [rewrite Hsp in HJ3; exact HJ3|]. split; [exact HA3|]. split; [exact HM3|].
    split; [exact HRM3|]. split; [exact HPm3 | exact HO3].
  - exact HF. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc2 & HP2 & (k1' & out' & HJs & HA & HM & HRM2 & HPm & HO)).
exists ly2, S2, regs2, mem2, md2, k1, out'. split; [reflexivity|]. split; [exact HJ2|].
split; [exists k1'; exact HJs|]. split; [exact HP2|]. split; [exact HA|]. split; [exact HM|]. split; [exact HRM2|].
split; [exact HPm | exact HO].
Qed.
End wR.

End c.
End b.
End a.
