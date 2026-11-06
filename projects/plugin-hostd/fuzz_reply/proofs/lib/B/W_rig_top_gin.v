(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the IMAGE-B walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan-ubsan 0x82e1c .. 0x82f08 / 0x830c4), lemma track G: the state after entry i's drain step (GTOPM)
   and the budget after it (gtop_bud) give GIN i 0 r when entry i holds S r keys (gin_top) and GOUT (S i) when it
   holds none (gout_top).  Statements: lib/B/W_rig_top_defs.v stmt_gin_top / stmt_gout_top.  The Section header is
   W_rig_top_defs.v's, verbatim.  Proof port of k3's image-A track (a working branch 80fffa8e840,
   lib/A/W_rig_top_gin.v): GTOPM / GIN / GOUT have image A's text, so only the imports change.
   ROUTE (b), STEP 3 (the image-A twin: a Theorem Labs lane's RIG_x round of lib/A/W_rig_top.v, commit f4cd818e98d): at
   W_relay_instance_gone_cx.v's generic Section; gbud's room and count conjuncts pass through unchanged.
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

(* ---- tg_: list and model facts for entry i's start (pure: no machine state). ---- *)

(* an entry with its own keys put back is itself *)
Lemma tg_entry_keys_self : forall e, entry_keys e (re_keys e) = e.
Proof. intros e. destruct e. reflexivity. Qed.

(* nheld is the number of held keys *)
Lemma tg_nheld_len : forall e, re_nheld e = Z.of_nat (length (re_keys e)).
Proof. intros e. reflexivity. Qed.

(* nothing ended sends nothing *)
Lemma tg_sends_nil : forall mx c O cap, sl_sends mx c O cap (ge_bytes []) = (c, O, cap).
Proof. intros. reflexivity. Qed.

Lemma tg_geik_nil : forall pre, geik pre [] = ([], []).
Proof. intros. reflexivity. Qed.

Lemma tg_gkrest_nil : forall cx no cap, gkrest cx no cap [] = [].
Proof. intros. reflexivity. Qed.

(* GBASE: one harness source per entry *)
Lemma tg_gbase_len : forall cx, GBASE B ARx MT RP MMAX RG cx -> length (gxhs cx) = length (gxes cx).
Proof. intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _). exact HL. Qed.

Lemma tg_firstn_snoc : forall {X : Type} (l : list X) i d, (i < length l)%nat ->
firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros X l i d. revert l. induction i as [|i IH]; intros [|x l] H; cbn [length] in H; try lia.
- reflexivity.
- change (x :: firstn (S i) l = (x :: firstn i l) ++ [nth i l d]).
  rewrite (IH l ltac:(lia)). reflexivity.
Qed.

Lemma tg_combine_app : forall {X Y : Type} (l1 : list X) (l2 : list Y) l1' l2', length l1 = length l2 ->
combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
intros X Y l1. induction l1 as [|x l1 IH]; intros l2 l1' l2' H; destruct l2 as [|y l2]; cbn [length] in H.
- reflexivity.
- discriminate H.
- discriminate H.
- cbn [app combine]. rewrite (IH l2 l1' l2' ltac:(lia)). reflexivity.
Qed.

(* entry i's harness source joins the done sources when entry i was open *)
Lemma tg_gdone_snoc : forall ps qd e (hj : hsrc * nat) e' (h' : hsrc), length ps = length qd ->
gdone_srcs (ps ++ [(e, hj)]) (qd ++ [(e', h')]) = gdone_srcs ps qd ++ (if re_eof e =? 0 then asrc_blks h' else []).
Proof.
intros ps qd e hj e' h' H. unfold gdone_srcs.
rewrite (tg_combine_app ps qd [(e, hj)] [(e', h')] H), map_app, concat_app.
cbn [combine map concat fst snd]. rewrite app_nil_r. reflexivity.
Qed.

(* rig_rel over a list split in two *)
Lemma tg_rel_app : forall pre mx ps qs ps2 qs2 c O cap c' O' cap' c2 O2 cap2,
rig_rel pre mx c O cap ps qs c' O' cap' -> rig_rel pre mx c' O' cap' ps2 qs2 c2 O2 cap2 ->
rig_rel pre mx c O cap (ps ++ ps2) (qs ++ qs2) c2 O2 cap2.
Proof.
intros pre mx ps. induction ps as [|[e [h j]] r IH];
intros qs ps2 qs2 c O cap c' O' cap' c2 O2 cap2 H1 H2; destruct qs as [|[e' h'] q];
cbn [rig_rel app] in H1 |- *; try contradiction.
- destruct H1 as (Ec & EO & Ecap). subst c' O' cap'. exact H2.
- destruct H1 as (e1 & ev & LB & H1). exists e1, ev, LB. cbv zeta in H1 |- *.
  destruct H1 as (Ha & Hb & Hc). split; [exact Ha|]. split; [exact Hb|].
  revert Hc. destruct (sl_sends _ _ _ _ _) as [[c3 O3] cap3]. intros Hc.
  exact (IH q ps2 qs2 c3 O3 cap3 c' O' cap' c2 O2 cap2 Hc H2).
Qed.

(* rig_rel of one entry: its drain (gdrained's equations), its key run (geik) and the run's sends *)
Lemma tg_rel_one : forall pre mx cB OB capB e (hj : hsrc * nat) ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2,
c1 = (if re_eof e =? 0 then dr_ctl cB (fst hj) ev else cB) ->
O1 = (if (re_eof e =? 0) && dr_live cB (fst hj) then OB ++ LB else OB) ->
cap1 = (if (re_eof e =? 0) && dr_live cB (fst hj)
        then drain_b_c.ds_ocap (dr_fin cB mx (Z.of_nat (length OB)) capB e (fst hj)) else capB) ->
(if re_eof e =? 0 then dr_rel cB mx (Z.of_nat (length OB)) capB e (fst hj) e1 h1 LB else e1 = e /\ h1 = fst hj) ->
geik pre (re_keys e1) = (Ed, ks) ->
sl_sends mx c1 O1 cap1 (ge_bytes Ed) = (c2, O2, cap2) ->
rig_rel pre mx cB OB capB [(e, hj)] [(entry_keys e1 ks, h1)] c2 O2 cap2.
Proof.
intros pre mx cB OB capB e hj ev LB e1 h1 c1 O1 cap1 Ed ks c2 O2 cap2 Ec EO Ecap Hd Hg Hs.
destruct hj as [h j]. cbn [fst] in Ec, EO, Ecap, Hd. subst c1 O1 cap1.
cbn [rig_rel]. exists e1, ev, LB. cbv zeta. split; [exact Hd|].
rewrite Hg. cbn [fst snd]. split; [reflexivity|].
rewrite Hs. cbn [rig_rel]. repeat split.
Qed.

(* ---- G1: entry i's key loop starts (nheld = S r): GIN at n = 0, ks = re_keys e1, Ed = [], fuel |ks|. ---- *)
Lemma gin_top : stmt_gin_top B ARx MT RP MMAX RG.
Proof.
unfold stmt_gin_top.
intros cx i r F qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1 HB HG Hbud Hn Hpre Hsh.
exists (re_keys e1), (length (re_keys e1)).
unfold GTOPM in HG. cbv zeta in HG.
destruct HG as (Hi & Hq & Hrel & Hdr & Har & Hout & Hsrc & Hsrc1 & Hdro & Hkept & Hperm).
unfold gtop_bud in Hbud. cbv zeta in Hbud.
rewrite tg_nheld_len in Hn.
unfold GIN. cbv zeta. rewrite tg_entry_keys_self.
refine (conj Hi (conj Hq (conj Hrel (conj Hdr (conj (tg_sends_nil _ _ _ _) (conj _ (conj _ (conj _
  (conj Har (conj Hout (conj Hsrc (conj Hsrc1 (conj Hdro (conj Hkept (conj Hperm (conj Hpre (conj Hsh _))))))))))))))))).
- lia.
- lia.
- unfold geik. rewrite app_nil_l. apply surjective_pairing.
- exact Hbud.
Qed.

(* ---- G2: entry i holds no key (nheld <= 0): GOUT (S i), entry i done as e1 with its source h1. ---- *)
Lemma gout_top : stmt_gout_top B ARx MT RP MMAX RG.
Proof.
unfold stmt_gout_top.
intros cx i qd cB OB capB e1 h1 ev LB c1 O1 cap1 out1 spent ly1 S1 W1 m1 HB HG Hbud Hn.
assert (Hk : re_keys e1 = []).
{ rewrite tg_nheld_len in Hn. destruct (re_keys e1) as [|k ks]; [reflexivity|]. cbn [length] in Hn. lia. }
pose proof (tg_gbase_len cx HB) as HL.
unfold GTOPM in HG. cbv zeta in HG.
destruct HG as (Hi & Hq & Hrel & Hdr & Har & Hout & Hsrc & Hsrc1 & Hdro & Hkept & Hperm).
unfold gtop_bud in Hbud. cbv zeta in Hbud. rewrite Hk, tg_geik_nil in Hbud. cbn [fst] in Hbud.
rewrite tg_sends_nil in Hbud. cbv beta iota in Hbud. rewrite tg_gkrest_nil, app_nil_l in Hbud.
unfold gdrained in Hdr. cbv zeta in Hdr. destruct Hdr as (Ec1 & EO1 & Ecap1 & Hd).
assert (Hlt : (i < length (gps cx))%nat) by (unfold gps; rewrite length_combine, HL; lia).
assert (Hnth : nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) = (gnth cx i, ghj cx i)).
{ unfold gps, gnth, ghj. apply combine_nth. symmetry. exact HL. }
assert (Hfs : firstn (S i) (gps cx) = firstn i (gps cx) ++ [(gnth cx i, ghj cx i)]).
{ rewrite (tg_firstn_snoc (gps cx) i (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj) Hlt), Hnth.
  reflexivity. }
assert (Hlf : length (firstn i (gps cx)) = length qd) by (rewrite length_firstn; lia).
assert (Hone : rig_rel (gpre cx) (gxmx cx) cB OB capB [(gnth cx i, ghj cx i)] [(e1, h1)] c1 O1 cap1).
{ pose proof (tg_rel_one (gpre cx) (gxmx cx) cB OB capB (gnth cx i) (ghj cx i) ev LB e1 h1 c1 O1 cap1 [] (re_keys e1)
    c1 O1 cap1 Ec1 EO1 Ecap1 Hd ltac:(rewrite Hk; apply tg_geik_nil) (tg_sends_nil _ _ _ _)) as H1.
  rewrite tg_entry_keys_self in H1. exact H1. }
exists (qd ++ [(e1, h1)]).
unfold GOUT.
refine (conj _ (conj _ (conj _ (conj _ (conj Hout (conj _ (conj Hdro (conj Hkept (conj _ Hbud))))))))).
- lia.
- rewrite length_app. cbn [length]. lia.
- rewrite Hfs. exact (tg_rel_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel Hone).
- rewrite (map_app fst qd [(e1, h1)]), <- app_assoc. exact Har.
- intros i' Hi' He'. destruct (Nat.lt_ge_cases i' i) as [Hlt' | Hge'].
  + rewrite app_nth1 by lia. exact (Hsrc i' Hlt' He').
  + assert (Ei : i' = i) by lia. subst i'. rewrite app_nth2 by lia. rewrite Hq, Nat.sub_diag. cbn [nth snd].
    apply Hsrc1. apply Z.eqb_eq. exact He'.
- rewrite (map_app fst qd [(e1, h1)]), <- app_assoc.
  rewrite Hfs, (tg_gdone_snoc _ _ _ _ _ _ Hlf), <- app_assoc. exact Hperm.
Qed.

End c.
End b.
End a.
