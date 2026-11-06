(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE-B segment KEY of fuzz_reply's relay_instance_gone (lib/B/W_relay_instance_gone_cx.v rig_key_stmt): the
   model and budget lemmas (prefix rkb_; pure, no machine state), ported from k3's image-A lib/A/W_rig_key.v
   (a working branch 8cfff43c147); the cut predicates GIN / GOUT / gbud are the same text on both images.
   Proves no function (kind: segment lemma).
   C3 (the peak form; the image-A twin's re-fit of lib/A/W_rig_key.v, mirrored): ge_room and gbud's room are over
   tr_peak; each key's gesture_end takes its room from the remaining trace's prefix (rkb_ker_split, rkb_ge_room), and
   gbud after the key from the NET change of the key's gesture_end and free (rkb_ge_net: g_out's growth; the free
   lowers the live bytes by |key| + 1; rkb_gbud_end).  The tr_alloc-only helpers (rkb_alloc_head, rkb_slr_cap,
   rkb_slr_fin) are gone; rkb_er_sz / rkb_er_pn carry the peak and the net change across the addresses. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), the RIGX round of
   image B (the image-A twin: a Theorem Labs lane's lib/A/W_rig_key.v at f4cd818e98d, its rkb_ / rkm / rkc_ part): KEY's model
   and budget over any allocator relation ARx with the room record RP, against the cx file's generic Section
   (lib/B/W_relay_instance_gone_cx.v; its Section c copied below).  gbud takes the cut's layout ly1 and carries the room
   round's two facts: the room rp_RM RP S1 (MT_rk's count of the requests still owed, on top of gxkr) and the live
   counts cnt_ok_pk RP (tr_peakP + 3).  The meter lemmas that also serve MT_rk are stated over any meter in Section
   rkm (rkb_tr_app_g .. rkb_gkrest_step_g); the AR walk's names stay, at MT; MT_rk is lawful (rkm_rk_laws).  For the
   end arm (gesture_end at ge_spec_x, then the free of the key at afree_cf_rule_c_x): rk_room gives gesture_end's room
   premise rp_RM RP S1 (its MT_rk charge + 1 + rk_krn, the room the requests after the key owe; rkb_ge_rm), its count
   premise cnt_ok_pk RP ge_pk and the free's cnt_ok (the live counts at most one above GIN's); after the key, gbud's
   room is the free's post rp_RM RP S3 rk_krn and its counts follow from the key's count change: gesture_end's
   cphi P (ge_cap ..) - cphi P cap = tr_netP P (ge_tr ..) (rkc_ge_netP, from the round chain's equality rkc_slr_net)
   less the free's zb (P (|key| + 1)) (rkc_end_cnt), against the count peak's split (rkc_peak_split; rkb_gbud_end,
   rkb_gin_end, rkb_gout_end). *)
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
(* the count names (acnt, zb, tr_peakP): lib/B/ReplyCnt.v, Required, named qualified; tr_netP / cphi / tc_send:
   lib/B/W_tr_cnt.v, the kit twin of image A's W_tr_cnt.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_tr_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_tr_peak.
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

(* -- the trace measures -- *)
Lemma rkb_tr_max_nonneg : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_max t.
Proof. intros t. unfold tr_max. induction t as [|e t IH]; cbn [fold_right]; [lia|]. destruct e; lia. Qed.

Lemma rkb_sizes_app : forall t1 t2, rk_sizes (t1 ++ t2) <-> rk_sizes t1 /\ rk_sizes t2.
Proof. intros t1 t2. unfold rk_sizes. apply Forall_app. Qed.

(* the sizes alone: the measures ignore the addresses *)
Definition rkb_er (e : RelayRunT.rev YO0i.sptr) : RelayRunT.rev YO0i.sptr :=
match e with
| RelayRunT.RMalloc n => RelayRunT.RMalloc n
| RelayRunT.RFree n _ => RelayRunT.RFree n ga0
| RelayRunT.RRealloc k n _ => RelayRunT.RRealloc k n ga0
end.

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

Lemma rkb_sl_cap_ge : forall c mx no cap len, 0 <= cap -> cap <= sl_cap c mx no cap len.
Proof.
intros c mx no cap len Hc. rewrite sl_cap_fin. destruct (sl_live c len); [apply sl_fin_ge; exact Hc | lia].
Qed.

Lemma rkb_slt_sizes : forall live mx no cap len j o, 0 <= mx -> 0 <= no -> rk_sizes (send_line_b_c.send_line_tr live mx no cap len j o).
Proof. intros live mx no cap len j o Hmx Hno. unfold send_line_b_c.send_line_tr. destruct live; [apply rkb_slr_sizes; assumption | constructor]. Qed.

(* -- gesture_end -- *)
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

Lemma rkb_ker_sizes : forall lv mx xks no cap j o, 0 <= mx -> 0 <= no -> Forall (fun x => 0 <= fst x) xks ->
rk_sizes (fst (keys_end_run lv mx no cap xks j o)).
Proof.
intros lv mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o Hmx Hno HF; cbn [keys_end_run fst]; [constructor|].
apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx.
apply rkb_sizes_app. split.
- unfold gesture_end_b_c.gesture_end_tr. cbv zeta. apply rkb_sizes_app. split; apply rkb_slt_sizes; lia.
- constructor; [exact I | apply IH; [exact Hmx | lia | exact HF]].
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

(* ---- Section rkm: the meter lemmas over ANY meter M (the walk's MT, and the room round's counting meter MT_rk,
   W_contract_x.v), image A's Section rkm; after the Section each AR-walk name is kept at MT (below). ---- *)
Section rkm.
Variable M : ameter_ops.
Hypothesis HM : ameter_laws M.
(* -- the trace measures -- *)
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

Lemma rkb_slt_cost_g : forall live mx no cap len j o,
tr_cost M (send_line_b_c.send_line_tr live mx no cap len j o) = if live then sl_cost_run M (Z.to_nat len) mx no cap len else 0.
Proof. intros. unfold send_line_b_c.send_line_tr. destruct live; [apply rkb_slr_cost_g | reflexivity]. Qed.

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

(* -- the run of key ends -- *)
Lemma rkb_ker_eq_g : forall lv mx xks no cap no' cap' j o j' o', (lv = true -> no = no' /\ cap = cap') ->
tr_cost M (fst (keys_end_run lv mx no cap xks j o)) = tr_cost M (fst (keys_end_run lv mx no' cap' xks j' o')) /\
tr_max (fst (keys_end_run lv mx no cap xks j o)) = tr_max (fst (keys_end_run lv mx no' cap' xks j' o')).
Proof. intros lv mx xks no cap no' cap' j o j' o' H. apply rkb_er_eq_g. apply rkb_ker_er; [reflexivity | exact H]. Qed.

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

(* the AR walk's names, at the walk's meter MT (the sibling key files name these) *)
Lemma rkb_tr_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2 /\ tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof. exact (rkb_tr_app_g MT MLAW). Qed.

Lemma rkb_tr_free : forall n (a : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost MT (RelayRunT.RFree n a :: t) = mo_free MT + tr_cost MT t /\ tr_max (RelayRunT.RFree n a :: t) = tr_max t.
Proof. exact (rkb_tr_free_g MT MLAW). Qed.

Lemma rkb_sizes_cost : forall t, rk_sizes t -> 0 <= tr_cost MT t.
Proof. exact (rkb_sizes_cost_g MT MLAW). Qed.

Lemma rkb_er_tr : forall t, tr_cost MT (map rkb_er t) = tr_cost MT t /\ tr_max (map rkb_er t) = tr_max t.
Proof. exact (rkb_er_tr_g MT MLAW). Qed.

Lemma rkb_er_eq : forall t1 t2, map rkb_er t1 = map rkb_er t2 -> tr_cost MT t1 = tr_cost MT t2 /\ tr_max t1 = tr_max t2.
Proof. exact (rkb_er_eq_g MT MLAW). Qed.

Lemma rkb_cost_head : forall cap C (o : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost MT ((if cap =? 0 then RelayRunT.RMalloc C else RelayRunT.RRealloc cap C o) :: t) = mo_malloc MT C + mo_free MT + tr_cost MT t.
Proof. exact (rkb_cost_head_g MT MLAW). Qed.

Lemma rkb_slr_cost : forall f mx no cap rem j o,
tr_cost MT (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run MT f mx no cap rem.
Proof. exact (rkb_slr_cost_g MT MLAW). Qed.

Lemma rkb_slcr_nonneg : forall f mx no cap rem, 0 <= cap -> 0 <= sl_cost_run MT f mx no cap rem.
Proof. exact (rkb_slcr_nonneg_g MT MLAW). Qed.

Lemma rkb_slt_cost : forall live mx no cap len j o,
tr_cost MT (send_line_b_c.send_line_tr live mx no cap len j o) = if live then sl_cost_run MT (Z.to_nat len) mx no cap len else 0.
Proof. exact (rkb_slt_cost_g MT MLAW). Qed.

Lemma rkb_ge_tr_cost : forall c mx no cap xl, 0 < xl ->
tr_cost MT (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = ge_cost MT c mx no cap xl.
Proof. exact (rkb_ge_tr_cost_g MT MLAW). Qed.

Lemma rkb_ge_cost_nonneg : forall c mx no cap xl, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= ge_cost MT c mx no cap xl.
Proof. exact (rkb_ge_cost_nonneg_g MT MLAW). Qed.

Lemma rkb_ker_eq : forall lv mx xks no cap no' cap' j o j' o', (lv = true -> no = no' /\ cap = cap') ->
tr_cost MT (fst (keys_end_run lv mx no cap xks j o)) = tr_cost MT (fst (keys_end_run lv mx no' cap' xks j' o')) /\
tr_max (fst (keys_end_run lv mx no cap xks j o)) = tr_max (fst (keys_end_run lv mx no' cap' xks j' o')).
Proof. exact (rkb_ker_eq_g MT MLAW). Qed.

Lemma rkb_ker_step : forall c mx no cap xl ka xks, 0 < xl ->
tr_cost MT (fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0)) =
  ge_cost MT c mx no cap xl + mo_free MT +
  tr_cost MT (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0)) /\
tr_max (fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0)) =
  Z.max (tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0))
    (tr_max (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0))).
Proof. exact (rkb_ker_step_g MT MLAW). Qed.

Lemma rkb_gkrest_step : forall cx c no cap k Er,
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
tr_cost MT (gkrest cx no cap (k :: Er)) =
  ge_cost MT c (gxmx cx) no cap (Z.of_nat (length (key_text k))) + mo_free MT +
  tr_cost MT (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er) /\
tr_max (gkrest cx no cap (k :: Er)) =
  Z.max (tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0))
    (tr_max (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
      (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er)).
Proof. exact (rkb_gkrest_step_g MT MLAW). Qed.

(* the counting meter MT_rk is lawful (W_relay_finish_h.v rfl_rk_laws) *)
Lemma rkm_rk_laws : ameter_laws MT_rk.
Proof. constructor; cbn [mo_ok mo_le mo_malloc mo_free MT_rk]; intros; solve [exact I | lia]. Qed.

(* ---- rkc: the live counts (ReplyCnt.acnt) across one key's end.  The count peak ignores the addresses (as the
   cost does, rkb_er_tr); a round chain of send_line from cap >= 0 grows g_out only, so its net count is EXACTLY the
   change of g_out's own count (cphi, lib/B/W_tr_cnt.v; tc_chain there gives one direction);
   gesture_end's two sends are such chains; g_out's block counts cphi P cap; the free of a block of size n lowers the
   count by zb (P n). ---- *)
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
destruct (rkb_gkrest_step_g MT_rk rkm_rk_laws cx c no cap k Er Hl Hmx Hno Hcap Hxl) as (E1 & _).
destruct (rkb_tr_app_g MT_rk rkm_rk_laws (gkrest cx no cap (k :: Er)) G) as (A1 & _).
destruct (rkb_tr_app_g MT_rk rkm_rk_laws (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
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


(* ==== KEY's end arm: the model after one key ended (gesture_end, free, the move) ==== *)
Lemma rkb_sends_cap_nonneg : forall mx Bs c O cap, 0 <= cap -> 0 <= snd (sl_sends mx c O cap Bs).
Proof.
intros mx Bs. induction Bs as [|x Bs IH]; intros c O cap Hc; cbn [sl_sends snd]; [exact Hc|].
apply IH. pose proof (rkb_sl_cap_ge c mx (Z.of_nat (length O)) cap (Z.of_nat (length x)) Hc). lia.
Qed.

Lemma rkb_sends_cons : forall mx c O cap k Er,
sl_sends mx c O cap (ge_bytes (k :: Er)) =
sl_sends mx (ge_ctl c (Z.of_nat (length (key_text k)))) (ge_O c O (key_text k))
  (ge_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length (key_text k)))) (ge_bytes Er).
Proof.
intros mx c O cap k Er. change (k :: Er) with ([k] ++ Er). rewrite rkb_ge_bytes_app, rkb_sends_app, rkb_sends_key.
reflexivity.
Qed.

Lemma rkb_aout_cap : forall ly S W m c O mx no cap out, aout_at B RG ly S W m c O mx no cap out -> 0 <= cap.
Proof.
intros ly S W m c O mx no cap out H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc).
destruct Hc as [(E & _) | (Hc & _)]; lia.
Qed.

(* gesture_end's room and the meter for gesture_end then free, from GIN at a key with the prefix; and the room
   record's premises of both calls: gesture_end's MT_rk charge, then the free's 1, then rk_krn (what the requests after
   the key owe), all inside GIN's budget (ge_spec_x at kr := S (rk_krn ..); its post leaves rp_RM (1 + rk_krn ..), the
   free's premise at afree_cf_rule_c_x); gesture_end's count premise (peak 3 under GIN's peak + 3) and the free's (the
   live counts at most one above GIN's, under the same 3; rkc_cnt_out_le gives that from gesture_end's post) *)
Lemma rk_room : forall cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
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
intros cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HB H Hp.
pose proof (rkb_live_gin cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 H) as HL.
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
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text k)))) (ge_bytes Er))
  by exact (rkb_sends_cons (gxmx cx) c2 O2 cap2 k Er).
assert (Hc3 : 0 <= snd (sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (k :: Er)))) by (apply rkb_sends_cap_nonneg; exact Hcap).
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

(* GIN / GOUT after one key's end: the memory half at (ly3 S3 W3 m3), the meter and the live bytes (the last two
   premises of the AR walk), and the room round's two: the free's post room rp_RM RP S3 (rk_krn ..) and the key's
   count change (rkc_end_cnt), which carry gbud's room and counts (rkb_gbud_end) *)
Lemma rkb_gin_end : forall cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 ly3 S3 W3 m3 out3,
  GBASE B ARx MT RP MMAX RG cx ->
  GIN B MT RP MMAX RG cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
  0 <= cap2 -> 0 < Z.of_nat (length (key_text (nth n ks (0, [], [])))) ->
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx)
    (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)) ->
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], []))))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ->
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) ->
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) ->
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) ->
  Permutation (ablocks B ly3 S3)
    ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx))) ++
     gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
     rig_srcs (skipn (S i) (gps cx)) ++
     aout_blks (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ++
     gxrest cx) ->
  garr8 SEGS (arm W3 m3) (F + 32) (gpre cx ++ [0]) ->
  garr8 SEGS (arm W3 m3) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] ->
  mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) ->
  blocks_bytes S3 <= blocks_bytes S1 +
    tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ->
  rp_RM RP S3 (rk_krn cx i n ks f c2 O2 cap2) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1))) ->
  exists f', GIN B MT RP MMAX RG cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1
    (swap_remove (0, [], []) n ks) (Ed ++ [nth n ks (0, [], [])]) f'
    (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], []))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    out3
    (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT))
    ly3 S3 W3 m3.
Proof.
intros cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ly3 S3 W3 m3 out3
  HB HG HP Hcap2 Hxl Har Hout Hsrc Hsrc1 Hdrs Hgs Hperm Hpre Hpsh Hle Hbb HRM3 HCN3.
pose proof (rkb_live_gin cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HG) as HL.
destruct (rkb_gbase_facts cx HB) as (Hmx & _).
pose proof HG as Hg. unfold GIN in Hg. cbv zeta in Hg.
destruct Hg as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G18).
assert (Hn : (n < length ks)%nat) by lia.
destruct f as [|f0]; [lia|].
exists f0.
pose proof (rkb_geik_end f0 (gpre cx) n ks Hn HP) as EGK.
rewrite EGK in G8, G18. cbn [fst snd] in G8, G18.
rewrite rkb_sends_cons in G18.
unfold GIN. cbv zeta.
refine (conj G1 (conj G2 (conj G3 (conj G4 (conj _ (conj _ (conj _ (conj _ (conj Har (conj Hout (conj Hsrc (conj Hsrc1
  (conj Hdrs (conj Hgs (conj Hperm (conj Hpre (conj Hpsh _))))))))))))))))).
- rewrite rkb_ge_bytes_app, rkb_sends_app, G5. apply rkb_sends_key.
- rewrite relay_instance_gone_b_lem.rigl_len_swap. lia.
- rewrite relay_instance_gone_b_lem.rigl_len_swap. lia.
- rewrite G8, <- app_assoc. reflexivity.
- unfold rk_krn, rk_tl in HRM3. cbn [Nat.pred] in HRM3. cbv zeta in HRM3.
  revert G18 HRM3. destruct (sl_sends _ _ _ _ (ge_bytes (fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks)))))
    as [[c3 O3] cap3]. intros G18 HRM3. cbv beta iota in HRM3.
  rewrite rkb_ge_O_len. rewrite rkb_ge_O_len in HRM3.
  apply (rkb_gbud_end cx ly1 S1 ly3 S3 spent c2 (Z.of_nat (length O2)) cap2 (nth n ks (0, [], [])) _ _ G18 HL
    ltac:(lia) ltac:(lia) Hcap2 Hxl Hle Hbb HRM3 HCN3).
Qed.

Lemma rkb_gout_end : forall cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 ly3 S3 W3 m3 out3,
  GBASE B ARx MT RP MMAX RG cx ->
  GIN B MT RP MMAX RG cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
  0 <= cap2 -> 0 < Z.of_nat (length (key_text (nth n ks (0, [], [])))) ->
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx)
    (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)) ->
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], []))))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ->
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) ->
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) ->
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) ->
  Permutation (ablocks B ly3 S3)
    ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx))) ++
     gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
     rig_srcs (skipn (S i) (gps cx)) ++
     aout_blks (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ++
     gxrest cx) ->
  mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) ->
  blocks_bytes S3 <= blocks_bytes S1 +
    tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ->
  rp_RM RP S3 (rk_krn cx i n ks f c2 O2 cap2) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1))) ->
  GOUT B MT RP MMAX RG cx (S i) (qd ++ [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)])
    (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], []))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    out3
    (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT))
    ly3 S3 W3 m3.
Proof.
intros cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ly3 S3 W3 m3 out3
  HB HG HP Hcap2 Hxl Har Hout Hsrc Hsrc1 Hdrs Hgs Hperm Hle Hbb HRM3 HCN3.
pose proof (rkb_gbase_len cx HB) as HLn.
pose proof (rkb_live_gin cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HG) as HL.
destruct (rkb_gbase_facts cx HB) as (Hmx & _).
pose proof HG as Hg. unfold GIN in Hg. cbv zeta in Hg.
destruct Hg as (Hi & Hq & Hrel & Hdr & Hs & Hk & Hf & Hgk & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbud).
assert (Hn : (n < length ks)%nat) by lia.
destruct f as [|f0]; [lia|].
pose proof (rkb_geik_end f0 (gpre cx) n ks Hn HP) as EGK.
assert (Hlen' : length (swap_remove (0, [], []) n ks) = n) by (rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
rewrite (rkb_geik_done f0 (gpre cx) n (swap_remove (0, [], []) n ks) ltac:(lia)) in EGK.
rewrite EGK in Hgk, Hbud. cbn [fst snd] in Hgk, Hbud.
rewrite rkb_sends_cons in Hbud. change (ge_bytes []) with (@nil (list byte)) in Hbud. cbn [sl_sends] in Hbud.
assert (Hgk' : geik (gpre cx) (re_keys e1) = (Ed ++ [nth n ks (0, [], [])], swap_remove (0, [], []) n ks))
  by (rewrite Hgk; reflexivity).
assert (Hs' : sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes (Ed ++ [nth n ks (0, [], [])])) =
  (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))), ge_O c2 O2 (key_text (nth n ks (0, [], []))),
   ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))))
  by (rewrite rkb_ge_bytes_app, rkb_sends_app, Hs; apply rkb_sends_key).
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & EO1 & Ecap1 & Hd).
assert (Hlt : (i < length (gps cx))%nat) by (unfold gps; rewrite length_combine, HLn; lia).
assert (Hnth : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i)).
{ unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HLn. }
assert (Hfs : firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)]).
{ rewrite (rkb_firstn_snoc (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) Hlt), Hnth. reflexivity. }
assert (Hlf : length (firstn i (gps cx)) = length qd) by (rewrite length_firstn; lia).
unfold GOUT.
refine (conj _ (conj _ (conj _ (conj _ (conj Hout (conj _ (conj Hdrs (conj Hgs (conj _ _))))))))).
- lia.
- rewrite length_app. cbn [length]. lia.
- rewrite Hfs. eapply rkb_rel_app; [exact Hrel|].
  exact (rkb_rel_one (gpre cx) (gxmx cx) cB OB capB (gnth cx i) (ghj cx i) ev LB e1 h1 c1 O1 cap1 _ _ _ _ _
    Ec1 EO1 Ecap1 Hd Hgk' Hs').
- rewrite (map_app fst qd [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]), <- app_assoc. exact Har.
- intros i' Hi' He'. destruct (Nat.lt_ge_cases i' i) as [Hlt' | Hge'].
  + rewrite app_nth1 by lia. exact (Hsrc i' Hlt' He').
  + assert (Ei : i' = i) by lia. subst i'. rewrite app_nth2 by lia. rewrite Hq, Nat.sub_diag. cbn [nth snd].
    apply Hsrc1. apply Z.eqb_eq. exact He'.
- rewrite (map_app fst qd [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]), <- app_assoc.
  rewrite Hfs, (rkb_gdone_snoc _ _ _ _ _ _ Hlf), <- app_assoc. exact Hperm.
- rewrite rkb_ge_O_len.
  (* the free's post room: rk_krn at the entry's last key (no key left: Er = []) *)
  assert (HRM3' : rp_RM RP S3 (Z.to_nat (tr_cost MT_rk
      (gkrest cx (ge_no c2 (Z.of_nat (length O2)) (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
         (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) [] ++
       grest cx (S i) (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], []))))))
         (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))))
      + gxkr cx)).
  { rewrite rkb_gkrest_nil. cbn [app].
    unfold rk_krn, rk_tl in HRM3. cbn [Nat.pred] in HRM3. cbv zeta in HRM3.
    rewrite (rkb_geik_done f0 (gpre cx) n (swap_remove (0, [], []) n ks) ltac:(lia)) in HRM3. cbn [fst] in HRM3.
    change (ge_bytes []) with (@nil (list byte)) in HRM3. cbn [sl_sends] in HRM3.
    rewrite rkb_gkrest_nil in HRM3. cbn [app] in HRM3. exact HRM3. }
  pose proof (rkb_gbud_end cx ly1 S1 ly3 S3 spent c2 (Z.of_nat (length O2)) cap2 (nth n ks (0, [], [])) [] _ Hbud HL
    ltac:(lia) ltac:(lia) Hcap2 Hxl Hle Hbb HRM3' HCN3) as G.
  rewrite rkb_gkrest_nil in G. cbn [app] in G. rewrite rkb_ge_O_len in G. exact G.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): KEY's budget and model lemmas at a world relation R.  The strict lemmas above take every Section
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
(* ==== budget block (RigKeyBudget) ==== *)
(* ---- rkb: model and budget lemmas for segment KEY (pure: no machine state). ---- *)
(* The trace's requests ask nonnegative sizes. *)

(* -- the stream's liveness at one byte is kept by every send and every drain -- *)
Lemma rkb_live_gen_xR : forall cl br dd len,
send_line_c.send_live cl (if send_line_c.send_off cl br len then br else dd) dd 1 = send_line_c.send_live cl br dd 1.
Proof.
intros cl br dd len. unfold send_line_c.send_live, send_line_c.send_off.
destruct (cl <? 0); cbn [orb negb andb]; [reflexivity|].
destruct (br =? 1) eqn:Eb; cbn [orb negb andb]; [rewrite Eb; reflexivity|].
destruct (len =? 0); cbn [orb negb andb]; [rewrite Eb; reflexivity|].
destruct (Z.eqb_spec dd 0) as [->|Hd]; [reflexivity|].
rewrite andb_false_r. reflexivity.
Qed.

Lemma rkb_live_pos_xR : forall c len, 0 < len -> sl_live c len = sl_live c 1.
Proof.
intros c len H. unfold sl_live, send_line_c.send_live, send_line_c.send_off.
replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma rkb_live_ctl_xR : forall c len, sl_live (sl_ctl c len) 1 = sl_live c 1.
Proof. intros c len. unfold sl_live, sl_ctl. cbn [ct_cl ct_br ct_dd]. apply rkb_live_gen_xR. Qed.

Lemma rkb_live_dr_xR : forall c h ev, sl_live (dr_ctl c h ev) 1 = sl_live c 1.
Proof. intros c h ev. unfold sl_live, dr_ctl. cbn [ct_cl ct_br ct_dd]. apply rkb_live_gen_xR. Qed.

Lemma rkb_live_sends_xR : forall mx c O cap Bs, sl_live (fst (fst (sl_sends mx c O cap Bs))) 1 = sl_live c 1.
Proof.
intros mx c O cap Bs. revert c O cap. induction Bs as [|Bl r IH]; intros c O cap; cbn [sl_sends]; [reflexivity|].
rewrite IH. apply rkb_live_ctl_xR.
Qed.

Lemma rkb_live_rel_xR : forall pre mx c O cap ps qs c2 O2 cap2, rig_rel pre mx c O cap ps qs c2 O2 cap2 -> sl_live c2 1 = sl_live c 1.
Proof.
intros pre mx c O cap ps. revert c O cap.
induction ps as [|[e [h j]] r IH]; intros c O cap [|[e' h'] q] c2 O2 cap2 H; cbn [rig_rel] in H; try contradiction.
- destruct H as (-> & _ & _). reflexivity.
- destruct H as (e1 & ev & LB & H). cbv zeta in H. destruct H as (_ & _ & H).
  match type of H with context [sl_sends ?a ?b ?d ?g ?k] =>
    pose proof (rkb_live_sends_xR a b d g k) as HL; revert H HL;
    destruct (sl_sends a b d g k) as [[c3 O3] cap3]; intros H HL end.
  cbn [fst] in HL. cbv beta iota in H. rewrite (IH _ _ _ _ _ _ _ H), HL.
  destruct (re_eof e =? 0); [apply rkb_live_dr_xR | reflexivity].
Qed.

Lemma rkb_live_gin_xR : forall cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
sl_live c2 1 = sl_live (gxc cx) 1.
Proof.
intros cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 H.
unfold GIN in H. cbv zeta in H.
destruct H as (_ & _ & Hrel & Hdr & Hs & _).
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & _).
pose proof (rkb_live_sends_xR (gxmx cx) c1 O1 cap1 (ge_bytes Ed)) as HL. rewrite Hs in HL. cbn [fst] in HL.
rewrite HL, Ec1. rewrite <- (rkb_live_rel_xR _ _ _ _ _ _ _ _ _ _ Hrel).
destruct (re_eof (gnth cx i) =? 0); [apply rkb_live_dr_xR | reflexivity].
Qed.

(* -- the sends -- *)
Lemma rkb_sends_app_xR : forall mx c O cap B1 B2,
sl_sends mx c O cap (B1 ++ B2) = let '(c', O', cap') := sl_sends mx c O cap B1 in sl_sends mx c' O' cap' B2.
Proof.
intros mx c O cap B1. revert c O cap.
induction B1 as [|Bl r IH]; intros c O cap B2; cbn [app sl_sends]; [reflexivity | apply IH].
Qed.

Lemma rkb_ge_bytes_app_xR : forall E1 E2, ge_bytes (E1 ++ E2) = ge_bytes E1 ++ ge_bytes E2.
Proof. intros E1 E2. unfold ge_bytes. rewrite map_app, concat_app. reflexivity. Qed.

Lemma rkb_sl_O_len_xR : forall c O x, Z.of_nat (length (sl_O c O x)) = sl_no c (Z.of_nat (length O)) (Z.of_nat (length x)).
Proof. intros c O x. unfold sl_O, sl_no. destruct (sl_live c _); [rewrite length_app; lia | reflexivity]. Qed.

Lemma rkb_sends_key_xR : forall mx c O cap k,
sl_sends mx c O cap (ge_bytes [k]) =
(ge_ctl c (Z.of_nat (length (key_text k))), ge_O c O (key_text k),
 ge_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length (key_text k)))).
Proof.
intros mx c O cap k. unfold ge_bytes. cbn [map concat app sl_sends]. unfold ge_ctl, ge_O, ge_cap.
rewrite rkb_sl_O_len_xR. reflexivity.
Qed.

Lemma rkb_ge_O_len_xR : forall c O x, Z.of_nat (length (ge_O c O x)) = ge_no c (Z.of_nat (length O)) (Z.of_nat (length x)).
Proof. intros c O x. unfold ge_O, ge_no. rewrite !rkb_sl_O_len_xR. reflexivity. Qed.

(* -- the trace measures -- *)
Lemma rkb_tr_max_nonneg_xR : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_max t.
Proof. intros t. unfold tr_max. induction t as [|e t IH]; cbn [fold_right]; [lia|]. destruct e; lia. Qed.

Lemma rkb_sizes_app_xR : forall t1 t2, rk_sizes (t1 ++ t2) <-> rk_sizes t1 /\ rk_sizes t2.
Proof. intros t1 t2. unfold rk_sizes. apply Forall_app. Qed.

(* the sizes alone: the measures ignore the addresses *)

(* C3: the peak and the net change ignore the addresses too (W_tr_peak.v tr_sz_measures) *)
Lemma rkb_er_sz_xR : forall t, tr_sz (map rkb_er t) = tr_sz t.
Proof.
induction t as [|e t IH]; [reflexivity|]. unfold tr_sz in *. cbn [map]. rewrite IH. destruct e; reflexivity.
Qed.

Lemma rkb_er_pn_xR : forall t1 t2, map rkb_er t1 = map rkb_er t2 -> tr_peak t1 = tr_peak t2 /\ tr_net t1 = tr_net t2.
Proof.
intros t1 t2 E. assert (Es : tr_sz t1 = tr_sz t2) by (rewrite <- (rkb_er_sz_xR t1), <- (rkb_er_sz_xR t2), E; reflexivity).
destruct (tr_sz_measures t1 t2 Es) as (P & N & _). split; assumption.
Qed.

(* -- send_line's rounds -- *)
Lemma rkb_slr_sizes_xR : forall f mx no cap rem j o, 0 <= mx -> 0 <= no -> rk_sizes (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
induction f as [|f IH]; intros mx no cap rem j o Hmx Hno; cbn [send_line_b_c.sl_run]; [constructor|].
destruct (rem <=? 0) eqn:Er; [constructor|]. apply Z.leb_gt in Er.
assert (Hn : 0 <= (if negb (mx =? 0) && (mx <? rem) then mx else rem)) by (destruct (negb (mx =? 0) && (mx <? rem)); lia).
destruct (cap <? no + _); cbn [fst snd].
- constructor; [destruct (cap =? 0); cbv beta iota; lia | apply IH; lia].
- apply IH; lia.
Qed.

Lemma rkb_slr_er_xR : forall f mx no cap rem j o j' o',
map rkb_er (fst (send_line_b_c.sl_run f mx no cap rem j o)) = map rkb_er (fst (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [send_line_b_c.sl_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + _); cbn [fst snd map]; [|apply IH].
rewrite (IH mx _ _ _ (S j) (RelayRunT.Ret j) (S j') (RelayRunT.Ret j')). apply (f_equal (fun x => cons x _)).
destruct (cap =? 0); reflexivity.
Qed.

Lemma rkb_sl_cap_ge_xR : forall c mx no cap len, 0 <= cap -> cap <= sl_cap c mx no cap len.
Proof.
intros c mx no cap len Hc. rewrite sl_cap_fin. destruct (sl_live c len); [apply sl_fin_ge; exact Hc | lia].
Qed.

Lemma rkb_slt_sizes_xR : forall live mx no cap len j o, 0 <= mx -> 0 <= no -> rk_sizes (send_line_b_c.send_line_tr live mx no cap len j o).
Proof. intros live mx no cap len j o Hmx Hno. unfold send_line_b_c.send_line_tr. destruct live; [apply rkb_slr_sizes_xR; assumption | constructor]. Qed.

(* -- gesture_end -- *)
Lemma rkb_ge_cap_nonneg_xR : forall c mx no cap xl, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= xl -> 0 <= ge_cap c mx no cap xl.
Proof.
intros c mx no cap xl Hmx Hno Hcap Hxl. unfold ge_cap.
pose proof (rkb_sl_cap_ge_xR c mx no cap xl Hcap) as H1.
pose proof (rkb_sl_cap_ge_xR (sl_ctl c xl) mx (sl_no c no xl) (sl_cap c mx no cap xl) 5 ltac:(lia)) as H2.
lia.
Qed.

Lemma rkb_ge_no_nonneg_xR : forall c no xl, 0 <= no -> 0 <= xl -> 0 <= ge_no c no xl.
Proof.
intros c no xl Hno Hxl. unfold ge_no, sl_no.
destruct (sl_live c xl), (sl_live (sl_ctl c xl) 5); cbv beta iota; lia.
Qed.

Lemma rkb_ge_cap_le_xR : forall c mx no cap xl, 0 <= cap -> cap <= ge_cap c mx no cap xl.
Proof.
intros c mx no cap xl Hcap. unfold ge_cap.
pose proof (rkb_sl_cap_ge_xR c mx no cap xl Hcap) as H1.
pose proof (rkb_sl_cap_ge_xR (sl_ctl c xl) mx (sl_no c no xl) (sl_cap c mx no cap xl) 5 ltac:(lia)) as H2.
lia.
Qed.

(* C3: gesture_end's net change of the live bytes is its growth of g_out (W_tr_peak.v ge_tr_net, at the walk's trace:
   the stream's liveness at one byte and the addresses ga0) *)
Lemma rkb_ge_net_xR : forall c mx no cap xl, 0 < xl ->
tr_net (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = ge_cap c mx no cap xl - cap.
Proof.
intros c mx no cap xl Hxl. rewrite <- (rkb_live_pos_xR c xl Hxl).
destruct (tr_sz_measures _ _ (gesture_end_tr_sz (sl_live c xl) mx no cap xl 0 ga0 0 RelayRunF.adr0)) as (_ & E & _).
rewrite E. exact (ge_tr_net c mx no cap xl ltac:(lia)).
Qed.

(* -- the run of key ends -- *)
Lemma rkb_ker_er_xR : forall lv mx xks xks' no cap no' cap' j o j' o',
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
  rewrite (rkb_slr_er_xR _ mx no cap xl j o j' o'). apply f_equal. apply rkb_slr_er_xR. }
rewrite EG. apply f_equal. cbn [map rkb_er]. apply f_equal.
apply IH; [exact Ef|]. intros Hlv. destruct (Hl Hlv) as [<- <-]. split; reflexivity.
Qed.

Lemma rkb_ker_sizes_xR : forall lv mx xks no cap j o, 0 <= mx -> 0 <= no -> Forall (fun x => 0 <= fst x) xks ->
rk_sizes (fst (keys_end_run lv mx no cap xks j o)).
Proof.
intros lv mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o Hmx Hno HF; cbn [keys_end_run fst]; [constructor|].
apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx.
apply rkb_sizes_app_xR. split.
- unfold gesture_end_b_c.gesture_end_tr. cbv zeta. apply rkb_sizes_app_xR. split; apply rkb_slt_sizes_xR; lia.
- constructor; [exact I | apply IH; [exact Hmx | lia | exact HF]].
Qed.

(* C3: one key's run is its gesture_end, the free of the key, then the rest of the run at the next g_nout / g_capout,
   up to the addresses (the peak form's split: rkb_gbud_end_xR, rkb_ge_room_xR) *)
Lemma rkb_ker_split_xR : forall c mx no cap xl ka xks, 0 < xl ->
exists T, fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0) =
  gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0 ++ RelayRunT.RFree (xl + 1) ka :: T /\
  map rkb_er T = map rkb_er (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0)).
Proof.
intros c mx no cap xl ka xks Hxl.
assert (HP : sl_live c 1 = true -> no + xl + 5 = ge_no c no xl /\ gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no cap xl = ge_cap c mx no cap xl).
{ intros Hlv. unfold ge_no, ge_cap, gesture_end_b_c.gesture_end_cap, sl_cap, sl_no.
  rewrite (rkb_live_pos_xR (sl_ctl c xl) 5 ltac:(lia)), rkb_live_ctl_xR, (rkb_live_pos_xR c xl Hxl), Hlv.
  split; reflexivity. }
cbn [keys_end_run fst]. eexists. split; [reflexivity|].
apply rkb_ker_er_xR; [reflexivity | exact HP].
Qed.

Lemma rkb_gkrest_nil_xR : forall cx no cap, gkrest cx no cap [] = [].
Proof. intros. reflexivity. Qed.

Lemma rkb_gkrest_sizes_xR : forall cx no cap Er, 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> rk_sizes (gkrest cx no cap Er).
Proof.
intros cx no cap Er Hmx Hno Hcap. unfold gkrest. apply rkb_ker_sizes_xR; [exact Hmx | exact Hno|].
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (k & <- & _). cbn [fst]. lia.
Qed.

(* ---- Section rkm: the meter lemmas over ANY meter M (the walk's MT, and the room round's counting meter MT_rk,
   W_contract_x.v), image A's Section rkm; after the Section each AR-walk name is kept at MT (below). ---- *)
Section rkm_xR.
Variable M : ameter_ops.
Hypothesis HM : ameter_laws M.
(* -- the trace measures -- *)
Lemma rkb_tr_app_g_xR : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
tr_cost M (t1 ++ t2) = tr_cost M t1 + tr_cost M t2 /\ tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros t1 t2. pose proof (rkb_tr_max_nonneg_xR t2) as H2. unfold tr_cost, tr_max in *.
induction t1 as [|e t1 IH]; cbn [app fold_right]; [split; lia|].
destruct IH as (IH1 & IH3). rewrite IH1, IH3. destruct e; split; lia.
Qed.

Lemma rkb_tr_free_g_xR : forall n (a : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost M (RelayRunT.RFree n a :: t) = mo_free M + tr_cost M t /\ tr_max (RelayRunT.RFree n a :: t) = tr_max t.
Proof. intros n a t. unfold tr_cost, tr_max. cbn [fold_right]. split; lia. Qed.

Lemma rkb_sizes_cost_g_xR : forall t, rk_sizes t -> 0 <= tr_cost M t.
Proof.
intros t H. unfold rk_sizes in H. unfold tr_cost.
pose proof (mo_free_nonneg M HM) as Hf.
induction H as [|e t He Ht IH]; cbn [fold_right]; [lia|].
destruct e as [n|n a|k n a]; cbv beta iota in He.
- pose proof (mo_malloc_nonneg M HM n He). lia.
- lia.
- pose proof (mo_malloc_nonneg M HM n He). lia.
Qed.

Lemma rkb_er_tr_g_xR : forall t, tr_cost M (map rkb_er t) = tr_cost M t /\ tr_max (map rkb_er t) = tr_max t.
Proof.
intros t. unfold tr_cost, tr_max.
induction t as [|e t IH]; cbn [map fold_right]; [split; reflexivity|].
destruct IH as (I1 & I3). rewrite I1, I3. destruct e; cbn [rkb_er]; split; reflexivity.
Qed.

Lemma rkb_er_eq_g_xR : forall t1 t2, map rkb_er t1 = map rkb_er t2 -> tr_cost M t1 = tr_cost M t2 /\ tr_max t1 = tr_max t2.
Proof.
intros t1 t2 E. destruct (rkb_er_tr_g_xR t1) as (A1 & A3). destruct (rkb_er_tr_g_xR t2) as (B1 & B3).
rewrite <- A1, <- A3, <- B1, <- B3, E. split; reflexivity.
Qed.

(* -- send_line's rounds -- *)
Lemma rkb_cost_head_g_xR : forall cap C (o : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost M ((if cap =? 0 then RelayRunT.RMalloc C else RelayRunT.RRealloc cap C o) :: t) = mo_malloc M C + mo_free M + tr_cost M t.
Proof. intros. destruct (cap =? 0); reflexivity. Qed.

Lemma rkb_slr_cost_g_xR : forall f mx no cap rem j o,
tr_cost M (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run M f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_cost_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + _); cbn [fst snd]; [|apply IH].
rewrite rkb_cost_head_g_xR, IH. reflexivity.
Qed.

Lemma rkb_slcr_nonneg_g_xR : forall f mx no cap rem, 0 <= cap -> 0 <= sl_cost_run M f mx no cap rem.
Proof.
induction f as [|f IH]; intros mx no cap rem Hc; cbn [sl_cost_run]; [lia|].
destruct (rem <=? 0); [lia|].
destruct (cap <? no + _) eqn:Eg; [apply Z.ltb_lt in Eg | apply IH; exact Hc].
pose proof (mo_free_nonneg M HM) as Hf.
match goal with |- context [mo_malloc M ?C] => pose proof (mo_malloc_nonneg M HM C ltac:(lia)) as Hm end.
match goal with |- context [sl_cost_run M f mx ?no2 ?c2 ?rem2] => pose proof (IH mx no2 c2 rem2 ltac:(lia)) as Hr end.
lia.
Qed.

Lemma rkb_slt_cost_g_xR : forall live mx no cap len j o,
tr_cost M (send_line_b_c.send_line_tr live mx no cap len j o) = if live then sl_cost_run M (Z.to_nat len) mx no cap len else 0.
Proof. intros. unfold send_line_b_c.send_line_tr. destruct live; [apply rkb_slr_cost_g_xR | reflexivity]. Qed.

(* -- gesture_end -- *)
Lemma rkb_ge_tr_cost_g_xR : forall c mx no cap xl, 0 < xl ->
tr_cost M (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = ge_cost M c mx no cap xl.
Proof.
intros c mx no cap xl Hxl.
unfold gesture_end_b_c.gesture_end_tr, ge_cost, sl_cost, sl_no, sl_cap.
rewrite (rkb_live_pos_xR (sl_ctl c xl) 5 ltac:(lia)), rkb_live_ctl_xR, (rkb_live_pos_xR c xl Hxl).
cbv zeta. rewrite (proj1 (rkb_tr_app_g_xR _ _)), !rkb_slt_cost_g_xR.
destruct (sl_live c 1); reflexivity.
Qed.

Lemma rkb_ge_cost_nonneg_g_xR : forall c mx no cap xl, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= ge_cost M c mx no cap xl.
Proof.
intros c mx no cap xl Hmx Hno Hcap. unfold ge_cost.
assert (H1 : 0 <= sl_cost M c mx no cap xl) by (unfold sl_cost; destruct (sl_live c xl); [apply rkb_slcr_nonneg_g_xR; lia | lia]).
pose proof (rkb_sl_cap_ge_xR c mx no cap xl Hcap) as Hc1.
assert (H2 : 0 <= sl_cost M (sl_ctl c xl) mx (sl_no c no xl) (sl_cap c mx no cap xl) 5)
  by (unfold sl_cost; destruct (sl_live (sl_ctl c xl) 5); [apply rkb_slcr_nonneg_g_xR; lia | lia]).
lia.
Qed.

(* -- the run of key ends -- *)
Lemma rkb_ker_eq_g_xR : forall lv mx xks no cap no' cap' j o j' o', (lv = true -> no = no' /\ cap = cap') ->
tr_cost M (fst (keys_end_run lv mx no cap xks j o)) = tr_cost M (fst (keys_end_run lv mx no' cap' xks j' o')) /\
tr_max (fst (keys_end_run lv mx no cap xks j o)) = tr_max (fst (keys_end_run lv mx no' cap' xks j' o')).
Proof. intros lv mx xks no cap no' cap' j o j' o' H. apply rkb_er_eq_g_xR. apply rkb_ker_er_xR; [reflexivity | exact H]. Qed.

Lemma rkb_ker_step_g_xR : forall c mx no cap xl ka xks, 0 < xl ->
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
  rewrite (rkb_live_pos_xR (sl_ctl c xl) 5 ltac:(lia)), rkb_live_ctl_xR, (rkb_live_pos_xR c xl Hxl), Hlv.
  split; reflexivity. }
cbn [keys_end_run fst].
match goal with |- context [keys_end_run _ mx (no + xl + 5) _ xks ?j2 ?o2] =>
  destruct (rkb_ker_eq_g_xR (sl_live c 1) mx xks (no + xl + 5) (gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no cap xl)
    (ge_no c no xl) (ge_cap c mx no cap xl) j2 o2 0%nat ga0 HP) as (E1 & E3);
  destruct (rkb_tr_free_g_xR (xl + 1) ka
    (fst (keys_end_run (sl_live c 1) mx (no + xl + 5) (gesture_end_b_c.gesture_end_cap (sl_live c 1) mx no cap xl) xks j2 o2)))
    as (F1 & F3) end.
rewrite (proj1 (rkb_tr_app_g_xR _ _)), (proj2 (rkb_tr_app_g_xR _ _)).
rewrite F1, F3, E1, E3, (rkb_ge_tr_cost_g_xR c mx no cap xl Hxl).
split; [lia | reflexivity].
Qed.

Lemma rkb_gkrest_step_g_xR : forall cx c no cap k Er,
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
exact (rkb_ker_step_g_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0 _ Hxl).
Qed.

End rkm_xR.

(* the AR walk's names, at the walk's meter MT (the sibling key files name these) *)
Lemma rkb_tr_app_xR : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2 /\ tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof. exact (rkb_tr_app_g_xR MT MLAW). Qed.

Lemma rkb_tr_free_xR : forall n (a : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost MT (RelayRunT.RFree n a :: t) = mo_free MT + tr_cost MT t /\ tr_max (RelayRunT.RFree n a :: t) = tr_max t.
Proof. exact (rkb_tr_free_g_xR MT MLAW). Qed.

Lemma rkb_sizes_cost_xR : forall t, rk_sizes t -> 0 <= tr_cost MT t.
Proof. exact (rkb_sizes_cost_g_xR MT MLAW). Qed.

Lemma rkb_er_tr_xR : forall t, tr_cost MT (map rkb_er t) = tr_cost MT t /\ tr_max (map rkb_er t) = tr_max t.
Proof. exact (rkb_er_tr_g_xR MT MLAW). Qed.

Lemma rkb_er_eq_xR : forall t1 t2, map rkb_er t1 = map rkb_er t2 -> tr_cost MT t1 = tr_cost MT t2 /\ tr_max t1 = tr_max t2.
Proof. exact (rkb_er_eq_g_xR MT MLAW). Qed.

Lemma rkb_cost_head_xR : forall cap C (o : RelayRunT.addr YO0i.sptr) (t : list (RelayRunT.rev YO0i.sptr)),
tr_cost MT ((if cap =? 0 then RelayRunT.RMalloc C else RelayRunT.RRealloc cap C o) :: t) = mo_malloc MT C + mo_free MT + tr_cost MT t.
Proof. exact (rkb_cost_head_g_xR MT MLAW). Qed.

Lemma rkb_slr_cost_xR : forall f mx no cap rem j o,
tr_cost MT (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run MT f mx no cap rem.
Proof. exact (rkb_slr_cost_g_xR MT MLAW). Qed.

Lemma rkb_slcr_nonneg_xR : forall f mx no cap rem, 0 <= cap -> 0 <= sl_cost_run MT f mx no cap rem.
Proof. exact (rkb_slcr_nonneg_g_xR MT MLAW). Qed.

Lemma rkb_slt_cost_xR : forall live mx no cap len j o,
tr_cost MT (send_line_b_c.send_line_tr live mx no cap len j o) = if live then sl_cost_run MT (Z.to_nat len) mx no cap len else 0.
Proof. exact (rkb_slt_cost_g_xR MT MLAW). Qed.

Lemma rkb_ge_tr_cost_xR : forall c mx no cap xl, 0 < xl ->
tr_cost MT (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = ge_cost MT c mx no cap xl.
Proof. exact (rkb_ge_tr_cost_g_xR MT MLAW). Qed.

Lemma rkb_ge_cost_nonneg_xR : forall c mx no cap xl, 0 <= mx -> 0 <= no -> 0 <= cap -> 0 <= ge_cost MT c mx no cap xl.
Proof. exact (rkb_ge_cost_nonneg_g_xR MT MLAW). Qed.

Lemma rkb_ker_eq_xR : forall lv mx xks no cap no' cap' j o j' o', (lv = true -> no = no' /\ cap = cap') ->
tr_cost MT (fst (keys_end_run lv mx no cap xks j o)) = tr_cost MT (fst (keys_end_run lv mx no' cap' xks j' o')) /\
tr_max (fst (keys_end_run lv mx no cap xks j o)) = tr_max (fst (keys_end_run lv mx no' cap' xks j' o')).
Proof. exact (rkb_ker_eq_g_xR MT MLAW). Qed.

Lemma rkb_ker_step_xR : forall c mx no cap xl ka xks, 0 < xl ->
tr_cost MT (fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0)) =
  ge_cost MT c mx no cap xl + mo_free MT +
  tr_cost MT (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0)) /\
tr_max (fst (keys_end_run (sl_live c 1) mx no cap ((xl, ka) :: xks) 0 ga0)) =
  Z.max (tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0))
    (tr_max (fst (keys_end_run (sl_live c 1) mx (ge_no c no xl) (ge_cap c mx no cap xl) xks 0 ga0))).
Proof. exact (rkb_ker_step_g_xR MT MLAW). Qed.

Lemma rkb_gkrest_step_xR : forall cx c no cap k Er,
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
tr_cost MT (gkrest cx no cap (k :: Er)) =
  ge_cost MT c (gxmx cx) no cap (Z.of_nat (length (key_text k))) + mo_free MT +
  tr_cost MT (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er) /\
tr_max (gkrest cx no cap (k :: Er)) =
  Z.max (tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0))
    (tr_max (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
      (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er)).
Proof. exact (rkb_gkrest_step_g_xR MT MLAW). Qed.

(* the counting meter MT_rk is lawful (W_relay_finish_h.v rfl_rk_laws) *)
Lemma rkm_rk_laws_xR : ameter_laws MT_rk.
Proof. constructor; cbn [mo_ok mo_le mo_malloc mo_free MT_rk]; intros; solve [exact I | lia]. Qed.

(* ---- rkc: the live counts (ReplyCnt.acnt) across one key's end.  The count peak ignores the addresses (as the
   cost does, rkb_er_tr_xR); a round chain of send_line from cap >= 0 grows g_out only, so its net count is EXACTLY the
   change of g_out's own count (cphi, lib/B/W_tr_cnt.v; tc_chain there gives one direction);
   gesture_end's two sends are such chains; g_out's block counts cphi P cap; the free of a block of size n lowers the
   count by zb (P n). ---- *)
(* the count peak of a free, as a rewrite (cbn would leave the fixpoint open) *)
Lemma rkc_peakP_free_xR : forall P kz (ka : RelayRunT.addr YO0i.sptr) (r : list (RelayRunT.rev YO0i.sptr)),
  ReplyCnt.tr_peakP P (RelayRunT.RFree kz ka :: r) = Z.max 0 (ReplyCnt.tr_peakP P r - ReplyCnt.zb (P kz)).
Proof. reflexivity. Qed.
(* the peak of a key's run: gesture_end's trace, the key's free, then the rest - at least the net of the first plus
   the peak of the rest less the freed block's count *)
Lemma rkc_peak_split_xR : forall P (A T G : list (RelayRunT.rev YO0i.sptr)) kz (ka : RelayRunT.addr YO0i.sptr),
  tr_netP P A + ReplyCnt.tr_peakP P (T ++ G) - ReplyCnt.zb (P kz) <=
  ReplyCnt.tr_peakP P (A ++ RelayRunT.RFree kz ka :: (T ++ G)).
Proof.
  intros P A T G kz ka.
  rewrite (tr_peakP_app _ P A (RelayRunT.RFree kz ka :: (T ++ G))), rkc_peakP_free_xR. lia.
Qed.
Lemma rkc_er_peakP_xR : forall P (t : list (RelayRunT.rev YO0i.sptr)), ReplyCnt.tr_peakP P (map rkb_er t) = ReplyCnt.tr_peakP P t.
Proof. intros P t. induction t as [|e t IH]; [reflexivity|]. destruct e; cbn [map rkb_er ReplyCnt.tr_peakP]; rewrite IH; reflexivity. Qed.

Lemma rkc_slr_net_xR : forall P f mx no cap rem j o, 0 <= cap ->
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

Lemma rkc_send_net_xR : forall P live mx no cap len j o, 0 <= cap ->
tr_netP P (send_line_b_c.send_line_tr live mx no cap len j o) =
  cphi P (send_line_b_c.send_line_cap live mx no cap len) - cphi P cap.
Proof.
intros P live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
destruct live; [|unfold tr_netP, ReplyTrPeakW.tr_net_w; cbn [fold_right]; lia].
pose proof (rkc_slr_net_xR P (Z.to_nat len) mx no cap len j o Hc) as H.
rewrite sl_run_fin in H. rewrite sl_run_fin. exact H.
Qed.

Lemma rkc_gend_net_xR : forall P live mx no cap xl j o, 0 <= cap ->
tr_netP P (gesture_end_b_c.gesture_end_tr live mx no cap xl j o) =
  cphi P (gesture_end_b_c.gesture_end_cap live mx no cap xl) - cphi P cap.
Proof.
intros P live mx no cap xl j o Hc. unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap. cbv zeta.
pose proof (tc_chain_nonneg _ _ _ _ _ (tc_send P live mx no cap xl j o Hc)) as Hn.
rewrite tr_netP_app, (rkc_send_net_xR P live mx no cap xl j o Hc). rewrite rkc_send_net_xR by exact Hn. lia.
Qed.

(* gesture_end's count change at the walk's trace (liveness at one byte, addresses ga0) *)
Lemma rkc_ge_netP_xR : forall P c mx no cap xl, 0 < xl -> 0 <= cap ->
tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) = cphi P (ge_cap c mx no cap xl) - cphi P cap.
Proof.
intros P c mx no cap xl Hxl Hcap. rewrite <- (rkb_live_pos_xR c xl Hxl), (ge_cap_tr c mx no cap xl ltac:(lia)).
exact (rkc_gend_net_xR P (sl_live c xl) mx no cap xl 0 ga0 Hcap).
Qed.

Lemma rkc_cphi_out_xR : forall P cap out, Z.of_nat (ReplyCnt.acnt P (aout_blks cap out)) = cphi P cap.
Proof.
intros P cap out. unfold aout_blks, cphi. destruct (cap =? 0); [reflexivity|].
unfold ReplyCnt.acnt, ReplyCnt.zb. cbn [map snd List.filter]. destruct (P cap); reflexivity.
Qed.

Lemma rkc_cnt_out_xR : forall P ly1 S1 ly2 S2 cap out cap' out' rest,
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) = Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) - cphi P cap + cphi P cap'.
Proof.
intros P ly1 S1 ly2 S2 cap out cap' out' rest P1 P2.
rewrite (ReplyCnt.acnt_perm P _ _ P1), (ReplyCnt.acnt_perm P _ _ P2), !ReplyCnt.acnt_app, !Nat2Z.inj_add, !rkc_cphi_out_xR.
lia.
Qed.

Lemma rkc_cnt_out_le_xR : forall P ly1 S1 ly2 S2 cap out cap' out' rest,
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
(ReplyCnt.acnt P (ablocks B ly2 S2) <= ReplyCnt.acnt P (ablocks B ly1 S1) + 1)%nat.
Proof.
intros P ly1 S1 ly2 S2 cap out cap' out' rest P1 P2.
pose proof (rkc_cnt_out_xR P ly1 S1 ly2 S2 cap out cap' out' rest P1 P2) as E.
pose proof (cphi_bounds P cap). pose proof (cphi_bounds P cap'). lia.
Qed.

Lemma rkc_cnt_free_xR : forall P ly2 S2 ly3 S3 l1 l2 pa n,
ablocks B ly2 S2 = l1 ++ (pa, n) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) = Z.of_nat (ReplyCnt.acnt P (ablocks B ly2 S2)) - ReplyCnt.zb (P n).
Proof.
intros P ly2 S2 ly3 S3 l1 l2 pa n E2 E3. rewrite E2, E3, !ReplyCnt.acnt_app, acnt_cons, !Nat2Z.inj_add.
unfold ReplyCnt.zb. cbn [snd]. destruct (P n); lia.
Qed.

(* one key's end: gesture_end (g_out from cap to its ge_cap) then the free of the key's block (|k| + 1) *)
Lemma rkc_end_cnt_xR : forall P c mx no cap xl ly1 S1 ly2 S2 ly3 S3 out out' rest l1 l2 pa,
0 < xl -> 0 <= cap ->
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks (ge_cap c mx no cap xl) out' ++ rest) ->
ablocks B ly2 S2 = l1 ++ (pa, xl + 1) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 ->
Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
  tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c 1) mx no cap xl 0 ga0) - ReplyCnt.zb (P (xl + 1)).
Proof.
intros P c mx no cap xl ly1 S1 ly2 S2 ly3 S3 out out' rest l1 l2 pa Hxl Hcap P1 P2 E2 E3.
rewrite (rkc_cnt_free_xR P ly2 S2 ly3 S3 l1 l2 pa (xl + 1) E2 E3), (rkc_cnt_out_xR P ly1 S1 ly2 S2 cap out _ out' rest P1 P2),
  (rkc_ge_netP_xR P c mx no cap xl Hxl Hcap).
lia.
Qed.

(* -- the drain's and the table run's requests ask nonnegative sizes -- *)
Lemma rkb_grow_ok_xR : forall cap used j b, 0 <= cap ->
rk_sizes (fst (drain_b_c.grow_tr cap used j b)) /\ 0 <= fst (snd (drain_b_c.grow_tr cap used j b)).
Proof.
intros cap used j b Hc. unfold drain_b_c.grow_tr.
destruct (cap - used <? 4096); cbn [fst snd]; [|split; [constructor | exact Hc]].
destruct (Z.eqb_spec cap 0); cbn [fst snd]; (split; [constructor; [cbv beta iota; lia | constructor] | lia]).
Qed.

Lemma rkb_seen_sizes_xR : forall H ka l j ha ks, rk_sizes (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
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

Lemma rkb_lines_sizes_xR : forall live mx ls no cap H ka j o ha ks, 0 <= mx -> 0 <= no ->
rk_sizes (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))).
Proof.
intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks Hmx Hno; cbn [drain_b_c.lines_run fst]; [constructor|].
apply rkb_sizes_app_xR. split; [apply rkb_slt_sizes_xR; lia|].
apply rkb_sizes_app_xR. split; [apply rkb_seen_sizes_xR | apply IH; lia].
Qed.

Lemma rkb_push_ok_xR : forall ls n cap j v rs, 0 <= cap ->
rk_sizes (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\ 0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)).
Proof.
induction ls as [|l ls IH]; intros n cap j v rs Hc; cbn [drain_b_c.pushes_run fst snd]; [split; [constructor | exact Hc]|].
assert (Hc' : 0 <= drain_b_c.push_cap n cap) by (unfold drain_b_c.push_cap; destruct (n =? cap), (cap =? 0); cbv beta iota; lia).
match goal with |- context [drain_b_c.pushes_run (n + 1) _ ls ?j1 ?v1 ?rs1] =>
  destruct (IH (n + 1) (drain_b_c.push_cap n cap) j1 v1 rs1 Hc') as [I1 I2] end.
split; [|exact I2]. apply rkb_sizes_app_xR. split; [|exact I1].
unfold ListTr.list_push_tra. apply rkb_sizes_app_xR. split; [|constructor; [cbv beta iota; lia | constructor]].
destruct (n =? cap); [|constructor]. destruct (Z.eqb_spec cap 0); (constructor; [cbv beta iota; lia | constructor]).
Qed.


Lemma rkb_drain_ok_xR : forall f live mx s j a, 0 <= mx -> rkb_dsok s ->
rk_sizes (fst (drain_b_c.drain_run f live mx s j a)) /\ rkb_dsok (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
induction f as [|f IH]; intros live mx s j a Hmx Hs; [split; [constructor | exact Hs]|].
cbn [drain_b_c.drain_run].
pose proof Hs as (Hc & He & Hn).
pose proof (rkb_grow_ok_xR (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Hc) as HG.
destruct (drain_b_c.grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a))
  as [tg [cg bg]].
cbn [fst snd] in HG |- *. destruct HG as [Hg Hgc].
destruct (drain_b_c.ds_eintr s).
- match goal with |- context [drain_b_c.drain_run f live mx ?s1 ?j1 ?a1] =>
    assert (Hs1 : rkb_dsok s1) by (unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia);
    destruct (IH live mx s1 j1 a1 Hmx Hs1) as [H1 H2] end.
  cbn [fst snd]. split; [apply rkb_sizes_app_xR; split; assumption | exact H2].
- destruct (drain_b_c.ds_pend s) as [|r0 rs]; cbn [fst snd].
  + split; [exact Hg | unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia].
  + destruct (Z.min _ _ <=? 0); cbn [fst snd].
    * split; [exact Hg | unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia].
    * destruct (RelayModel.chunk _ _ _) as [[u' sk'] rl].
      match goal with |- context [drain_b_c.pushes_run ?n0 ?c0 ?ls0 ?j0 ?v0 ?rs0] =>
        destruct (rkb_push_ok_xR ls0 n0 c0 j0 v0 rs0 He) as [Hp1 Hp2] end.
      match goal with |- context [drain_b_c.lines_run ?lv0 ?mx0 ?no0 ?cap0 ?H0 ?ka0 ?ls0 ?j0 ?o0 ?ha0 ?ks0] =>
        pose proof (rkb_lines_sizes_xR lv0 mx0 ls0 no0 cap0 H0 ka0 j0 o0 ha0 ks0 Hmx Hn) as Hl;
        destruct (snd (fst (drain_b_c.lines_run lv0 mx0 no0 cap0 H0 ka0 ls0 j0 o0 ha0 ks0))) as [[oc' H'] ka'];
        destruct (snd (drain_b_c.lines_run lv0 mx0 no0 cap0 H0 ka0 ls0 j0 o0 ha0 ks0)) as [[o' ha'] ks'] end.
      cbn [fst snd].
      match goal with |- context [drain_b_c.drain_run f live mx ?s1 ?j1 ?a1] =>
        assert (Hs1 : rkb_dsok s1) by (unfold rkb_dsok; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_no]; lia);
        destruct (IH live mx s1 j1 a1 Hmx Hs1) as [H1 H2] end.
      split; [|exact H2].
      repeat (apply rkb_sizes_app_xR; split); try assumption.
      match goal with |- rk_sizes (if ?b then _ else _) => destruct b end; [constructor; [exact I | constructor] | constructor].
Qed.

Lemma rkb_fold5_nonneg_xR : forall (l : list (list Z * RelayRunT.addr YO0i.sptr)),
0 <= fold_right (fun xl acc => xl + 5 + acc) 0 (map fst (map (fun x => (Z.of_nat (length (fst x)), snd x)) l)).
Proof. induction l as [|x l IH]; cbn [map fold_right fst]; lia. Qed.

Lemma rkb_xks_nonneg_xR : forall (l : list (list Z * RelayRunT.addr YO0i.sptr)),
Forall (fun x => 0 <= fst x) (map (fun x => (Z.of_nat (length (fst x)), snd x)) l).
Proof. induction l as [|x l IH]; cbn [map]; constructor; [cbn [fst]; lia | exact IH]. Qed.

Lemma rkb_gone_sizes_xR : forall lv mx pre ps no cap nm j o, 0 <= mx -> 0 <= no ->
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
    destruct (rkb_drain_ok_xR (S (S (length (pending_stream (fst hj))))) lv mx (drain_b_c.drain_init no cap e (fst hj))
      0%nat drain_b_c.dadr0 Hmx (Hinit E)) as [_ (_ & _ & H3)]. exact H3.
  - unfold drain_b_c.drain_init. cbn [drain_b_c.ds_no]. exact Hno. }
cbn [relay_instance_gone_b_c.gone_run].
match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?no2 ?cap2 pre r nm ?j2 ?o2] =>
  assert (Hno2 : 0 <= no2) by (match goal with |- context [map fst (map ?F ?L)] => pose proof (rkb_fold5_nonneg_xR L) end; lia);
  pose proof (IH no2 cap2 nm j2 o2 Hmx Hno2 HF) as IH2; revert IH2;
  destruct (relay_instance_gone_b_c.gone_run lv mx no2 cap2 pre r nm j2 o2) as [[[t c] ss] [o' das]]; intros IH2 end.
cbn [fst] in IH2 |- *.
apply rkb_sizes_app_xR. split; [|apply rkb_sizes_app_xR; split; [|exact IH2]].
- destruct (Z.eqb_spec (re_eof e) 0) as [E|E]; [|constructor].
  unfold drain_b_c.drain_tr, drain_b_c.drain_go. exact (proj1 (rkb_drain_ok_xR _ _ _ _ _ _ Hmx (Hinit E))).
- apply rkb_ker_sizes_xR; [exact Hmx | exact Hs | apply rkb_xks_nonneg_xR].
Qed.

Lemma rkb_forall_skipn_xR : forall {X Y : Type} (P : X * Y -> Prop) i (l1 : list X) (l2 : list Y),
Forall P (combine l1 l2) -> Forall P (combine (skipn i l1) (skipn i l2)).
Proof.
intros X Y P i. induction i as [|i IH]; intros l1 l2 H; [exact H|].
destruct l1 as [|x l1], l2 as [|y l2]; cbn [skipn combine]; [constructor | constructor | |].
- rewrite combine_nil. constructor.
- apply Forall_cons_iff in H as [_ H]. apply IH. exact H.
Qed.

Lemma rkb_gbase_facts_xR : forall cx, GBASE B ARx MT RP MMAX RG cx ->
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

Lemma rkb_grest_sizes_xR : forall cx i no cap, GBASE B ARx MT RP MMAX RG cx -> 0 <= no -> 0 <= cap -> rk_sizes (grest cx i no cap).
Proof.
intros cx i no cap HB Hno Hcap.
destruct (rkb_gbase_facts_xR cx HB) as (Hmx & HF & _).
unfold grest, relay_instance_gone_b_c.relay_instance_gone_tr.
apply rkb_gone_sizes_xR; [lia | exact Hno | apply rkb_forall_skipn_xR; exact HF].
Qed.

(* -- the meter and the budget -- *)
Lemma rkb_mok_xR : forall cx ly1 S1 spent tl c, GBASE B ARx MT RP MMAX RG cx -> gbud B MT RP MMAX cx ly1 S1 spent tl -> 0 <= c ->
c <= tr_cost MT tl -> mo_ok MT S1 c.
Proof.
intros cx ly1 S1 spent tl c HB (Hle & Hsp & Hc & _) Hc0 Hct.
destruct (rkb_gbase_facts_xR cx HB) as (_ & _ & Hok).
exact (mok_station MT (gxS cx) S1 (tr_cost MT (gtr cx)) spent c MLAW Hok Hle Hc0 ltac:(lia)).
Qed.

(* gbud after one key's end: the meter and the bytes as C3 left them; the room is the free's post (HRM3: the room the
   requests after the key owe, on top of gxkr); the counts from the key's count change HCN3 (gesture_end's net count
   less the freed key) against the peak's split tr_peakP (ge ++ RFree :: rest) >= net ge - zb + tr_peakP rest *)
Lemma rkb_gbud_end_xR : forall cx ly1 S1 ly3 S3 spent c no cap k Er G,
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
(* the peak: the run is the key's gesture_end, its free, then the rest (rkb_ker_split_xR) *)
assert (Hp : blocks_bytes S3 + tr_peak (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G) <= LIVE_MAX).
{ unfold gkrest in Ha |- *. rewrite <- Hl in Ha |- *. cbn [map] in Ha.
  destruct (rkb_ker_split_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0
    (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er) Hxl) as (T & ET & EM).
  rewrite ET, <- app_assoc, <- app_comm_cons, tr_peak_app, tr_peak_free, tr_peak_app in Ha.
  rewrite tr_peak_app. destruct (rkb_er_pn_xR _ _ EM) as (P1 & N1). rewrite P1, N1 in Ha.
  lia. }
(* the count peak, split the same way *)
assert (HK : forall P, ReplyCnt.tr_peakP P (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G) +
  tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) -
  ReplyCnt.zb (P (Z.of_nat (length (key_text k)) + 1)) <= ReplyCnt.tr_peakP P (gkrest cx no cap (k :: Er) ++ G)).
{ intros P. unfold gkrest. rewrite <- Hl. cbn [map].
  destruct (rkb_ker_split_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0
    (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er) Hxl) as (T & ET & EM).
  rewrite ET, <- app_assoc, <- app_comm_cons.
  set (Rq := fst (keys_end_run (sl_live c 1) (gxmx cx) (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er)
    0 ga0)) in *.
  assert (EP : ReplyCnt.tr_peakP P (T ++ G) = ReplyCnt.tr_peakP P (Rq ++ G))
    by (rewrite <- (rkc_er_peakP_xR P (T ++ G)), <- (rkc_er_peakP_xR P (Rq ++ G)), !map_app, EM; reflexivity).
  rewrite <- EP.
  pose proof (rkc_peak_split_xR P
    (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0)
    T G (Z.of_nat (length (key_text k)) + 1) ga0).
  lia. }
destruct (rkb_gkrest_step_xR cx c no cap k Er Hl Hmx Hno Hcap Hxl) as (E1 & E3).
destruct (rkb_tr_app_xR (gkrest cx no cap (k :: Er)) G) as (A1 & A3).
destruct (rkb_tr_app_xR (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er) G) as (B1 & B3).
pose proof (rkb_ge_cost_nonneg_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap) as Hg.
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

Lemma rkb_ge_room_xR : forall cx ly1 S1 spent c no cap k Er G,
gbud B MT RP MMAX cx ly1 S1 spent (gkrest cx no cap (k :: Er) ++ G) -> rk_sizes G ->
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
tr_max (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) < MMAX /\
blocks_bytes S1 + tr_peak (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) <= LIVE_MAX /\
ge_cost MT c (gxmx cx) no cap (Z.of_nat (length (key_text k))) + mo_free MT <= tr_cost MT (gkrest cx no cap (k :: Er) ++ G).
Proof.
intros cx ly1 S1 spent c no cap k Er G (Hle & Hsp & Hc & Ha & Hm & _) HG Hl Hmx Hno Hcap Hxl.
(* the room: gesture_end's trace is the remaining trace's prefix (rkb_ker_split_xR) *)
assert (Hp : blocks_bytes S1 + tr_peak (gesture_end_b_c.gesture_end_tr (sl_live c 1) (gxmx cx) no cap (Z.of_nat (length (key_text k))) 0 ga0) <= LIVE_MAX).
{ unfold gkrest in Ha. rewrite <- Hl in Ha. cbn [map] in Ha.
  destruct (rkb_ker_split_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) ga0
    (map (fun k0 => (Z.of_nat (length (key_text k0)), ga0)) Er) Hxl) as (T & ET & _).
  rewrite ET, <- app_assoc, tr_peak_app in Ha. lia. }
destruct (rkb_gkrest_step_xR cx c no cap k Er Hl Hmx Hno Hcap Hxl) as (E1 & E3).
destruct (rkb_tr_app_xR (gkrest cx no cap (k :: Er)) G) as (A1 & A3).
rewrite A1, E1. rewrite A3, E3 in Hm.
pose proof (rkb_sizes_cost_xR _ HG) as HG1.
pose proof (rkb_sizes_cost_xR _ (rkb_gkrest_sizes_xR cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er Hmx
  (rkb_ge_no_nonneg_xR c no (Z.of_nat (length (key_text k))) Hno ltac:(lia))
  (rkb_ge_cap_nonneg_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap ltac:(lia))))
  as HK1.
split; [lia|]. split; [exact Hp | lia].
Qed.

(* the room gesture_end and the free get from gbud: gbud's budget at the key is exactly gesture_end's MT_rk charge, the
   free's 1, then the room the requests after the key owe on top of gxkr (MT_rk is lawful, so every charge is >= 0) *)
Lemma rkb_ge_rm_xR : forall cx ly1 S1 spent c no cap k Er G,
gbud B MT RP MMAX cx ly1 S1 spent (gkrest cx no cap (k :: Er) ++ G) -> rk_sizes G ->
sl_live c 1 = sl_live (gxc cx) 1 -> 0 <= gxmx cx -> 0 <= no -> 0 <= cap -> 0 < Z.of_nat (length (key_text k)) ->
rp_RM RP S1 (Z.to_nat (ge_cost MT_rk c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) +
  S (Z.to_nat (tr_cost MT_rk (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
    (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er ++ G)) + gxkr cx)).
Proof.
intros cx ly1 S1 spent c no cap k Er G (_ & _ & _ & _ & _ & Hrm & _) HG Hl Hmx Hno Hcap Hxl.
destruct (rkb_gkrest_step_g_xR MT_rk rkm_rk_laws_xR cx c no cap k Er Hl Hmx Hno Hcap Hxl) as (E1 & _).
destruct (rkb_tr_app_g_xR MT_rk rkm_rk_laws_xR (gkrest cx no cap (k :: Er)) G) as (A1 & _).
destruct (rkb_tr_app_g_xR MT_rk rkm_rk_laws_xR (gkrest cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er) G) as (B1 & _).
pose proof (rkb_ge_cost_nonneg_g_xR MT_rk rkm_rk_laws_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap) as Hg.
pose proof (rkb_sizes_cost_g_xR MT_rk rkm_rk_laws_xR _ HG) as HG1.
pose proof (rkb_sizes_cost_g_xR MT_rk rkm_rk_laws_xR _ (rkb_gkrest_sizes_xR cx (ge_no c no (Z.of_nat (length (key_text k))))
  (ge_cap c (gxmx cx) no cap (Z.of_nat (length (key_text k)))) Er Hmx
  (rkb_ge_no_nonneg_xR c no (Z.of_nat (length (key_text k))) Hno ltac:(lia))
  (rkb_ge_cap_nonneg_xR c (gxmx cx) no cap (Z.of_nat (length (key_text k))) Hmx Hno Hcap ltac:(lia))))
  as HK1.
rewrite A1, E1 in Hrm. rewrite B1.
refine (@eq_ind _ _ (rp_RM RP S1) Hrm _ _).
replace (mo_free MT_rk) with 1 by reflexivity. lia.
Qed.

(* the requests still owed at RGI (GIN's last conjunct, the let named): the rest of entry i's key run from index n
   over ks (fuel f), then the entries after i *)
(* the room the requests after ending key n owe on top of gxkr: at the next RGI (key n gone, ks swap-removed, the
   stream after the key's gesture_end), which the free's post must leave *)

(* -- the live bytes -- *)
Lemma rkb_bb_out_xR : forall ly1 S1 ly2 S2 cap out cap' out' rest,
Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) ->
Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest) ->
0 <= cap <= cap' -> blocks_bytes S2 = blocks_bytes S1 - cap + cap'.
Proof.
intros ly1 S1 ly2 S2 cap out cap' out' rest P1 P2 Hc.
rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ P1), (bsum_perm _ _ P2), !bsum_app.
unfold aout_blks. destruct (Z.eqb_spec cap 0), (Z.eqb_spec cap' 0); rewrite ?bsum_cons; unfold bsum; cbn [fold_right snd]; lia.
Qed.

Lemma rkb_bb_free_xR : forall ly2 S2 ly3 S3 l1 l2 pa n,
ablocks B ly2 S2 = l1 ++ (pa, n) :: l2 -> ablocks B ly3 S3 = l1 ++ l2 -> blocks_bytes S3 = blocks_bytes S2 - n.
Proof.
intros ly2 S2 ly3 S3 l1 l2 pa n E2 E3.
rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly3 S3), E2, E3, !bsum_app, bsum_cons. cbn [snd]. lia.
Qed.

(* -- gestures_end_instance's loop, one step at a time -- *)
Lemma rkb_geik_pass_xR : forall f pre n ks, (n < length ks)%nat ->
has_prefix pre (bzs (key_text (nth n ks (0, [], [])))) = false ->
geik_loop (S f) pre n ks = geik_loop f pre (S n) ks.
Proof.
intros f pre n ks Hn Hp. cbn [geik_loop]. rewrite (proj2 (Nat.ltb_lt n (length ks)) Hn), Hp. reflexivity.
Qed.

Lemma rkb_geik_end_xR : forall f pre n ks, (n < length ks)%nat ->
has_prefix pre (bzs (key_text (nth n ks (0, [], [])))) = true ->
geik_loop (S f) pre n ks =
(nth n ks (0, [], []) :: fst (geik_loop f pre n (swap_remove (0, [], []) n ks)),
 snd (geik_loop f pre n (swap_remove (0, [], []) n ks))).
Proof.
intros f pre n ks Hn Hp. cbn [geik_loop]. rewrite (proj2 (Nat.ltb_lt n (length ks)) Hn), Hp.
destruct (geik_loop f pre n (swap_remove (0, [], []) n ks)) as [E K]. reflexivity.
Qed.

Lemma rkb_geik_done_xR : forall f pre n ks, (length ks <= n)%nat -> geik_loop f pre n ks = ([], ks).
Proof.
intros f pre n ks H. destruct f as [|f]; cbn [geik_loop]; [reflexivity|].
rewrite (proj2 (Nat.ltb_ge n (length ks)) H). reflexivity.
Qed.

(* -- list facts for the entry's exit -- *)
Lemma rkb_gbase_len_xR : forall cx, GBASE B ARx MT RP MMAX RG cx -> length (gxhs cx) = length (gxes cx).
Proof. intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _). exact HL. Qed.

Lemma rkb_firstn_snoc_xR : forall {X : Type} (l : list X) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros X l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia; cbn [firstn nth app]; [reflexivity|].
rewrite (IH i d ltac:(lia)). reflexivity.
Qed.

Lemma rkb_combine_app_xR : forall {X Y : Type} (l1 : list X) (l2 : list Y) l1' l2', length l1 = length l2 ->
combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] l1' l2' H; cbn [length] in H; try discriminate H;
cbn [app combine]; [reflexivity|].
rewrite IH by lia. reflexivity.
Qed.

Lemma rkb_gdone_snoc_xR : forall ps qd e (hj : hsrc * nat) e' (h' : hsrc), length ps = length qd ->
gdone_srcs (ps ++ [(e, hj)]) (qd ++ [(e', h')]) = gdone_srcs ps qd ++ (if re_eof e =? 0 then asrc_blks h' else []).
Proof.
intros ps qd e hj e' h' H. unfold gdone_srcs. rewrite (rkb_combine_app_xR _ _ _ _ H), map_app, concat_app.
cbn [combine map concat fst snd]. rewrite app_nil_r. reflexivity.
Qed.

Lemma rkb_rel_app_xR : forall pre mx ps qs ps2 qs2 c O cap c' O' cap' c2 O2 cap2,
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

Lemma rkb_rel_one_xR : forall pre mx cB OB capB e (hj : hsrc * nat) ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2,
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
Lemma rkb_gin_pass_xR : forall cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GIN B MT RP MMAX RG cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = false ->
exists f', GIN B MT RP MMAX RG cx i (S n) r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f' c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Proof.
intros cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 H Hp.
pose proof H as H0. unfold GIN in H0. cbv zeta in H0.
destruct H0 as (_ & _ & _ & _ & _ & Hk & Hf & _).
destruct f as [|f0]; [exfalso; lia|].
exists f0. unfold GIN in H |- *. cbv zeta in H |- *.
rewrite <- (rkb_geik_pass_xR f0 (gpre cx) n ks ltac:(lia) Hp).
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj _ (conj _ H8))))))); lia.
Qed.

Lemma rkb_gout_pass_xR : forall cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GIN B MT RP MMAX RG cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = false ->
GOUT B MT RP MMAX RG cx (S i) (qd ++ [(entry_keys e1 ks, h1)]) c2 O2 cap2 out2 spent ly1 S1 W1 m1.
Proof.
intros cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HB H Hp.
pose proof (rkb_gbase_len_xR cx HB) as HL.
unfold GIN in H. cbv zeta in H.
destruct H as (Hi & Hq & Hrel & Hdr & Hs & Hk & Hf & Hg & Har & Hout & Hsrc & Hsrc1 & Hdro & Hkept & Hperm & _ & _ & Hbud).
assert (Hgk : geik_loop f (gpre cx) n ks = ([], ks)).
{ destruct f as [|f0]; [lia|]. rewrite (rkb_geik_pass_xR f0 (gpre cx) n ks ltac:(lia) Hp). apply rkb_geik_done_xR. lia. }
rewrite Hgk in Hg, Hbud. cbn [fst snd] in Hg, Hbud. rewrite app_nil_r in Hg.
change (ge_bytes []) with (@nil (list byte)) in Hbud. cbn [sl_sends] in Hbud.
rewrite rkb_gkrest_nil_xR in Hbud. cbn [app] in Hbud.
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & EO1 & Ecap1 & Hd).
assert (Hlt : (i < length (gps cx))%nat) by (unfold gps; rewrite length_combine, HL; lia).
assert (Hnth : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i)).
{ unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HL. }
assert (Hfs : firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)]).
{ rewrite (rkb_firstn_snoc_xR (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) Hlt), Hnth. reflexivity. }
assert (Hlf : length (firstn i (gps cx)) = length qd) by (rewrite length_firstn; lia).
unfold GOUT.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
- lia.
- rewrite length_app. cbn [length]. lia.
- rewrite Hfs. eapply rkb_rel_app_xR; [exact Hrel|].
  exact (rkb_rel_one_xR (gpre cx) (gxmx cx) cB OB capB (gnth cx i) (ghj cx i) ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2
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
  rewrite Hfs, (rkb_gdone_snoc_xR _ _ _ _ _ _ Hlf), <- app_assoc. exact Hperm.
- exact Hbud.
Qed.


(* ==== KEY's end arm: the model after one key ended (gesture_end, free, the move) ==== *)
Lemma rkb_sends_cap_nonneg_xR : forall mx Bs c O cap, 0 <= cap -> 0 <= snd (sl_sends mx c O cap Bs).
Proof.
intros mx Bs. induction Bs as [|x Bs IH]; intros c O cap Hc; cbn [sl_sends snd]; [exact Hc|].
apply IH. pose proof (rkb_sl_cap_ge_xR c mx (Z.of_nat (length O)) cap (Z.of_nat (length x)) Hc). lia.
Qed.

Lemma rkb_sends_cons_xR : forall mx c O cap k Er,
sl_sends mx c O cap (ge_bytes (k :: Er)) =
sl_sends mx (ge_ctl c (Z.of_nat (length (key_text k)))) (ge_O c O (key_text k))
  (ge_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length (key_text k)))) (ge_bytes Er).
Proof.
intros mx c O cap k Er. change (k :: Er) with ([k] ++ Er). rewrite rkb_ge_bytes_app_xR, rkb_sends_app_xR, rkb_sends_key_xR.
reflexivity.
Qed.

Lemma rkb_aout_cap_xR : forall ly S W m c O mx no cap out, aout_at B RG ly S W m c O mx no cap out -> 0 <= cap.
Proof.
intros ly S W m c O mx no cap out H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc).
destruct Hc as [(E & _) | (Hc & _)]; lia.
Qed.

(* gesture_end's room and the meter for gesture_end then free, from GIN at a key with the prefix; and the room
   record's premises of both calls: gesture_end's MT_rk charge, then the free's 1, then rk_krn (what the requests after
   the key owe), all inside GIN's budget (ge_spec_x at kr := S (rk_krn ..); its post leaves rp_RM (1 + rk_krn ..), the
   free's premise at afree_cf_rule_c_x); gesture_end's count premise (peak 3 under GIN's peak + 3) and the free's (the
   live counts at most one above GIN's, under the same 3; rkc_cnt_out_le_xR gives that from gesture_end's post) *)
Lemma rk_room_xR : forall cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1,
GBASE B ARx MT RP MMAX RG cx ->
GIN B MT RP MMAX RG cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
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
intros cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HB H Hp.
pose proof (rkb_live_gin_xR cx i n r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 H) as HL.
destruct (rkb_gbase_facts_xR cx HB) as (Hmx & _ & _).
unfold GIN in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & Hs & Hk & Hf & Hg & Har & Hout & _ & _ & _ & _ & _ & _ & _ & Hbud).
assert (Hn : (n < length ks)%nat) by lia.
pose proof (rkb_aout_cap_xR _ _ _ _ _ _ _ _ _ _ Hout) as Hcap.
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
rewrite (rkb_geik_end_xR f0 (gpre cx) n ks Hn Hp) in Hbud. cbn [fst] in Hbud.
set (Er := fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks))) in *.
set (k := nth n ks (0, [], [])) in *.
assert (Ek : sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (k :: Er)) =
  sl_sends (gxmx cx) (ge_ctl c2 (Z.of_nat (length (key_text k)))) (ge_O c2 O2 (key_text k))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text k)))) (ge_bytes Er))
  by exact (rkb_sends_cons_xR (gxmx cx) c2 O2 cap2 k Er).
assert (Hc3 : 0 <= snd (sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes (k :: Er)))) by (apply rkb_sends_cap_nonneg_xR; exact Hcap).
rewrite Ek in Hbud, Hc3. revert Hbud Hc3.
destruct (sl_sends (gxmx cx) (ge_ctl c2 (Z.of_nat (length (key_text k)))) (ge_O c2 O2 (key_text k))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text k)))) (ge_bytes Er)) as [[c3 O3] cap3].
intros Hbud Hc3. cbv beta iota in Hbud |- *. cbn [snd] in Hc3. rewrite rkb_ge_O_len_xR.
pose proof (rkb_grest_sizes_xR cx (S i) (Z.of_nat (length O3)) cap3 HB ltac:(lia) Hc3) as HGs.
destruct (rkb_ge_room_xR cx ly1 S1 spent c2 (Z.of_nat (length O2)) cap2 k Er (grest cx (S i) (Z.of_nat (length O3)) cap3)
  Hbud HGs HL ltac:(lia) ltac:(lia) Hcap Hxl) as (R1 & R2 & R3).
pose proof (rkb_ge_rm_xR cx ly1 S1 spent c2 (Z.of_nat (length O2)) cap2 k Er (grest cx (S i) (Z.of_nat (length O3)) cap3)
  Hbud HGs HL ltac:(lia) ltac:(lia) Hcap Hxl) as RMg.
pose proof Hbud as (_ & _ & _ & _ & _ & _ & Hcn).
split; [exact R1|]. split; [exact R2|].
split.
{ apply (rkb_mok_xR cx ly1 S1 spent _ _ HB Hbud); [|exact R3].
  pose proof (rkb_ge_cost_nonneg_xR c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text k))) ltac:(lia) ltac:(lia) Hcap).
  pose proof (mo_free_nonneg MT MLAW). lia. }
split; [exact Hxl|]. split; [exact Hcap|]. split; [exact RMg|].
split.
- refine (cnt_ok_pk_mono RP _ ge_pk _ _ _ Hcn).
  intros P. unfold ge_pk. cbv beta. lia.
- intros l Hl. unfold cnt_ok. refine (cnt_ok_pk_mono RP _ _ _ l _ Hcn).
  intros P. pose proof (Hl P). cbv beta. lia.
Qed.

(* GIN / GOUT after one key's end: the memory half at (ly3 S3 W3 m3), the meter and the live bytes (the last two
   premises of the AR walk), and the room round's two: the free's post room rp_RM RP S3 (rk_krn ..) and the key's
   count change (rkc_end_cnt_xR), which carry gbud's room and counts (rkb_gbud_end_xR) *)
Lemma rkb_gin_end_xR : forall cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 ly3 S3 W3 m3 out3,
  GBASE B ARx MT RP MMAX RG cx ->
  GIN B MT RP MMAX RG cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
  0 <= cap2 -> 0 < Z.of_nat (length (key_text (nth n ks (0, [], [])))) ->
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx)
    (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)) ->
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], []))))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ->
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) ->
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) ->
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) ->
  Permutation (ablocks B ly3 S3)
    ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx))) ++
     gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
     rig_srcs (skipn (S i) (gps cx)) ++
     aout_blks (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ++
     gxrest cx) ->
  garr8 SEGS (arm W3 m3) (F + 32) (gpre cx ++ [0]) ->
  garr8 SEGS (arm W3 m3) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] ->
  mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) ->
  blocks_bytes S3 <= blocks_bytes S1 +
    tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ->
  rp_RM RP S3 (rk_krn cx i n ks f c2 O2 cap2) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1))) ->
  exists f', GIN B MT RP MMAX RG cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1
    (swap_remove (0, [], []) n ks) (Ed ++ [nth n ks (0, [], [])]) f'
    (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], []))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    out3
    (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT))
    ly3 S3 W3 m3.
Proof.
intros cx i n r' F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ly3 S3 W3 m3 out3
  HB HG HP Hcap2 Hxl Har Hout Hsrc Hsrc1 Hdrs Hgs Hperm Hpre Hpsh Hle Hbb HRM3 HCN3.
pose proof (rkb_live_gin_xR cx i n (S r') F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HG) as HL.
destruct (rkb_gbase_facts_xR cx HB) as (Hmx & _).
pose proof HG as Hg. unfold GIN in Hg. cbv zeta in Hg.
destruct Hg as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G18).
assert (Hn : (n < length ks)%nat) by lia.
destruct f as [|f0]; [lia|].
exists f0.
pose proof (rkb_geik_end_xR f0 (gpre cx) n ks Hn HP) as EGK.
rewrite EGK in G8, G18. cbn [fst snd] in G8, G18.
rewrite rkb_sends_cons_xR in G18.
unfold GIN. cbv zeta.
refine (conj G1 (conj G2 (conj G3 (conj G4 (conj _ (conj _ (conj _ (conj _ (conj Har (conj Hout (conj Hsrc (conj Hsrc1
  (conj Hdrs (conj Hgs (conj Hperm (conj Hpre (conj Hpsh _))))))))))))))))).
- rewrite rkb_ge_bytes_app_xR, rkb_sends_app_xR, G5. apply rkb_sends_key_xR.
- rewrite relay_instance_gone_b_lem.rigl_len_swap. lia.
- rewrite relay_instance_gone_b_lem.rigl_len_swap. lia.
- rewrite G8, <- app_assoc. reflexivity.
- unfold rk_krn, rk_tl in HRM3. cbn [Nat.pred] in HRM3. cbv zeta in HRM3.
  revert G18 HRM3. destruct (sl_sends _ _ _ _ (ge_bytes (fst (geik_loop f0 (gpre cx) n (swap_remove (0, [], []) n ks)))))
    as [[c3 O3] cap3]. intros G18 HRM3. cbv beta iota in HRM3.
  rewrite rkb_ge_O_len_xR. rewrite rkb_ge_O_len_xR in HRM3.
  apply (rkb_gbud_end_xR cx ly1 S1 ly3 S3 spent c2 (Z.of_nat (length O2)) cap2 (nth n ks (0, [], [])) _ _ G18 HL
    ltac:(lia) ltac:(lia) Hcap2 Hxl Hle Hbb HRM3 HCN3).
Qed.

Lemma rkb_gout_end_xR : forall cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent
  ly1 S1 W1 m1 ly3 S3 W3 m3 out3,
  GBASE B ARx MT RP MMAX RG cx ->
  GIN B MT RP MMAX RG cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ->
  has_prefix (gpre cx) (bzs (key_text (nth n ks (0, [], [])))) = true ->
  0 <= cap2 -> 0 < Z.of_nat (length (key_text (nth n ks (0, [], [])))) ->
  arelay_at B RG ly3 S3 W3 m3 (gxG0 cx)
    (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx)) ->
  aout_at B RG ly3 S3 W3 m3 (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], [])))) (gxmx cx)
    (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], []))))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ->
  (forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
     asrc_at B ly3 S3 W3 m3 (gslot RG cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) ->
  ((re_eof (gnth cx i) =? 0) = true -> asrc_at B ly3 S3 W3 m3 (gslot RG cx i) h1) ->
  Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly3 S3 W3 m3 (fst p) (fst (snd p)) (snd (snd p)))
    (skipn (S i) (gps cx)) ->
  (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
     (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
     abyte_kept (gxW cx) (gxmem cx) W3 m3 a) ->
  Permutation (ablocks B ly3 S3)
    ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 (swap_remove (0, [], []) n ks) :: skipn (S i) (gxes cx))) ++
     gdone_srcs (firstn i (gps cx)) qd ++ (if re_eof (gnth cx i) =? 0 then asrc_blks h1 else []) ++
     rig_srcs (skipn (S i) (gps cx)) ++
     aout_blks (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) out3 ++
     gxrest cx) ->
  mo_le MT S1 S3 (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT) ->
  blocks_bytes S3 <= blocks_bytes S1 +
    tr_net (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1) ->
  rp_RM RP S3 (rk_krn cx i n ks f c2 O2 cap2) ->
  (forall P, Z.of_nat (ReplyCnt.acnt P (ablocks B ly3 S3)) <= Z.of_nat (ReplyCnt.acnt P (ablocks B ly1 S1)) +
    tr_netP P (gesture_end_b_c.gesture_end_tr (sl_live c2 1) (gxmx cx) (Z.of_nat (length O2)) cap2
      (Z.of_nat (length (key_text (nth n ks (0, [], []))))) 0 ga0) -
    ReplyCnt.zb (P (Z.of_nat (length (key_text (nth n ks (0, [], [])))) + 1))) ->
  GOUT B MT RP MMAX RG cx (S i) (qd ++ [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)])
    (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    (ge_O c2 O2 (key_text (nth n ks (0, [], []))))
    (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
    out3
    (spent + (ge_cost MT c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))) + mo_free MT))
    ly3 S3 W3 m3.
Proof.
intros cx i n F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 ly3 S3 W3 m3 out3
  HB HG HP Hcap2 Hxl Har Hout Hsrc Hsrc1 Hdrs Hgs Hperm Hle Hbb HRM3 HCN3.
pose proof (rkb_gbase_len_xR cx HB) as HLn.
pose proof (rkb_live_gin_xR cx i n 0 F qd cB OB capB e1 h1 ev LB c1 O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1 HG) as HL.
destruct (rkb_gbase_facts_xR cx HB) as (Hmx & _).
pose proof HG as Hg. unfold GIN in Hg. cbv zeta in Hg.
destruct Hg as (Hi & Hq & Hrel & Hdr & Hs & Hk & Hf & Hgk & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbud).
assert (Hn : (n < length ks)%nat) by lia.
destruct f as [|f0]; [lia|].
pose proof (rkb_geik_end_xR f0 (gpre cx) n ks Hn HP) as EGK.
assert (Hlen' : length (swap_remove (0, [], []) n ks) = n) by (rewrite relay_instance_gone_b_lem.rigl_len_swap; lia).
rewrite (rkb_geik_done_xR f0 (gpre cx) n (swap_remove (0, [], []) n ks) ltac:(lia)) in EGK.
rewrite EGK in Hgk, Hbud. cbn [fst snd] in Hgk, Hbud.
rewrite rkb_sends_cons_xR in Hbud. change (ge_bytes []) with (@nil (list byte)) in Hbud. cbn [sl_sends] in Hbud.
assert (Hgk' : geik (gpre cx) (re_keys e1) = (Ed ++ [nth n ks (0, [], [])], swap_remove (0, [], []) n ks))
  by (rewrite Hgk; reflexivity).
assert (Hs' : sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes (Ed ++ [nth n ks (0, [], [])])) =
  (ge_ctl c2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))), ge_O c2 O2 (key_text (nth n ks (0, [], []))),
   ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))))
  by (rewrite rkb_ge_bytes_app_xR, rkb_sends_app_xR, Hs; apply rkb_sends_key_xR).
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & EO1 & Ecap1 & Hd).
assert (Hlt : (i < length (gps cx))%nat) by (unfold gps; rewrite length_combine, HLn; lia).
assert (Hnth : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i)).
{ unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HLn. }
assert (Hfs : firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)]).
{ rewrite (rkb_firstn_snoc_xR (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) Hlt), Hnth. reflexivity. }
assert (Hlf : length (firstn i (gps cx)) = length qd) by (rewrite length_firstn; lia).
unfold GOUT.
refine (conj _ (conj _ (conj _ (conj _ (conj Hout (conj _ (conj Hdrs (conj Hgs (conj _ _))))))))).
- lia.
- rewrite length_app. cbn [length]. lia.
- rewrite Hfs. eapply rkb_rel_app_xR; [exact Hrel|].
  exact (rkb_rel_one_xR (gpre cx) (gxmx cx) cB OB capB (gnth cx i) (ghj cx i) ev LB e1 h1 c1 O1 cap1 _ _ _ _ _
    Ec1 EO1 Ecap1 Hd Hgk' Hs').
- rewrite (map_app fst qd [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]), <- app_assoc. exact Har.
- intros i' Hi' He'. destruct (Nat.lt_ge_cases i' i) as [Hlt' | Hge'].
  + rewrite app_nth1 by lia. exact (Hsrc i' Hlt' He').
  + assert (Ei : i' = i) by lia. subst i'. rewrite app_nth2 by lia. rewrite Hq, Nat.sub_diag. cbn [nth snd].
    apply Hsrc1. apply Z.eqb_eq. exact He'.
- rewrite (map_app fst qd [(entry_keys e1 (swap_remove (0, [], []) n ks), h1)]), <- app_assoc.
  rewrite Hfs, (rkb_gdone_snoc_xR _ _ _ _ _ _ Hlf), <- app_assoc. exact Hperm.
- rewrite rkb_ge_O_len_xR.
  (* the free's post room: rk_krn at the entry's last key (no key left: Er = []) *)
  assert (HRM3' : rp_RM RP S3 (Z.to_nat (tr_cost MT_rk
      (gkrest cx (ge_no c2 (Z.of_nat (length O2)) (Z.of_nat (length (key_text (nth n ks (0, [], []))))))
         (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], [])))))) [] ++
       grest cx (S i) (Z.of_nat (length (ge_O c2 O2 (key_text (nth n ks (0, [], []))))))
         (ge_cap c2 (gxmx cx) (Z.of_nat (length O2)) cap2 (Z.of_nat (length (key_text (nth n ks (0, [], []))))))))
      + gxkr cx)).
  { rewrite rkb_gkrest_nil_xR. cbn [app].
    unfold rk_krn, rk_tl in HRM3. cbn [Nat.pred] in HRM3. cbv zeta in HRM3.
    rewrite (rkb_geik_done_xR f0 (gpre cx) n (swap_remove (0, [], []) n ks) ltac:(lia)) in HRM3. cbn [fst] in HRM3.
    change (ge_bytes []) with (@nil (list byte)) in HRM3. cbn [sl_sends] in HRM3.
    rewrite rkb_gkrest_nil_xR in HRM3. cbn [app] in HRM3. exact HRM3. }
  pose proof (rkb_gbud_end_xR cx ly1 S1 ly3 S3 spent c2 (Z.of_nat (length O2)) cap2 (nth n ks (0, [], [])) [] _ Hbud HL
    ltac:(lia) ltac:(lia) Hcap2 Hxl Hle Hbb HRM3' HCN3) as G.
  rewrite rkb_gkrest_nil_xR in G. cbn [app] in G. rewrite rkb_ge_O_len_xR in G. exact G.
Qed.
End wR.

End c.
End b.
End a.
