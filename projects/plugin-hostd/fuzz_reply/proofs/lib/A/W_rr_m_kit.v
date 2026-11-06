(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: shared helpers of the MATCH hops of the ASan walk of fuzz_reply's relay_remove
   (lib/A/W_rr_match_cx.v; hop files W_rr_m_drain.v, W_rr_m_ge.v, W_rr_m_free.v, W_rr_m_cpy.v).  A hop lane that needs
   a helper another hop also needs asks MatchCx to add it here rather than copy it.
   The hops cite the generic AR helpers where they are published: W_gestures_end.v Section ark (gse_callS,
   gse_keep_high, gse_keep_img, gse_nodup) and W_gesture_end.v (ge_garr8_kept, aout_facts, apk_trans).  One helper has
   no AR original any more and stays copied here (Section gecopy): rrk_ajgx_ly_top, W_gesture_end.v ajgx_ly_top of
   commit 475b8a2b569, verbatim but for the prefix (W_gesture_end.v now states it over the ARx journal). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (a Theorem Labs lane, lane RR_x): the helpers over ARx (Section c is
   W_relay_remove_cx.v's generic block): the journal ajournal_gx_x with the head sets, W_gestures_end.v's _x helpers
   (gse_keep_high_x, gse_keep_img_x: an image byte is kept when it is also off PST, PSTG), the laws' twins
   (frames_bounds_x, frm_img_x, sep_block_frame_x, ajournal_gx_rom_view_x with PSTR); rrk_ajgx_ly_top over
   ajournal_gx_x. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx W_rr_match_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_gesture_end W_gestures_end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* pairwise-apart ranges (YA0q.v zpairwise_disjoint): any two of them *)
Lemma rr_zall_nth : forall a l j, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l (0, 0)).
Proof.
intros a l. induction l as [|b l IH]; intros j H Hj; cbn [length] in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
Lemma rr_zpw_nth : forall l i j, zpairwise_disjoint l -> (i < j < length l)%nat ->
  zdisj (nth i l (0, 0)) (nth j l (0, 0)).
Proof.
induction l as [|a l IH]; intros i j H Hij; cbn [length] in Hij; [lia|].
destruct H as [H1 H2]. destruct i as [|i]; destruct j as [|j]; [lia | | lia |].
- cbn [nth]. apply rr_zall_nth; [exact H1 | lia].
- cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* writability across two worlds: a writable byte stays writable when its presence is kept (W_frame.v
   writable_kept, with the hidden set changing) *)
Lemma rr_writable2 : forall H H2 (m m2 : word -> option byte) a,
  (apresent H m a -> apresent H2 m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H2 m2) a.
Proof.
intros H H2 m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw.
- destruct (H2 (Z_to_bv 64 a)); [exact Hw|]. destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [EH2 [b2 Hb2]]. rewrite EH2, Hb2. discriminate.
  + destruct (H2 (Z_to_bv 64 a)); [exact Hw|]. destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* ---- the one helper copied from W_gesture_end.v (commit 475b8a2b569), verbatim but for the rrk_ prefix ---- *)
Section gecopy.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* W_gesture_end.v ajgx_ly_top (room sha 475b8a2b569), over ajournal_gx_x: a journal keeps the top of the stack
   layout. *)
Lemma rrk_ajgx_ly_top : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* route R: rrk_ajgx_ly_top over the journal at a world relation R (the layout conjunct reads no world) *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Lemma rrk_ajgx_ly_top_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
End wR.
End gecopy.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL): K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x, blk_off_imgP_x), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x83ee8 (s7, listing A_HI 59) and 0x83ef8 (s9, A_HI 60).
   The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges both by
   vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH59 : VAL (A_HI 59) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH60 : VAL (A_HI 60) = rg_src RG + RR_HI_SRC.
(* g_wake[1], read at 0x83fe0 by PLdHi (A_OBJ 4) (W5's HV4, verbatim) *)
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
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
   allocator's calls (W_journal.v ajournal_gx_rom_view) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the live-state meter does not see the fake frame: its seat and its release are set_fs steps (W8's ruling, the
   lead's KF-COUNT #4: the ablocks form is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v / W_journal.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls (W7's drain, W4's gestures_end), by their published _x specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x83f94 with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (W_relay_finish_h.v's PSTR / PSTC form). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

(* ---- The callee chain at relay_remove's frame (s0 = the entry sp; ra at s0 - 8, the caller's s0 at s0 - 16):
   at every internal jal of the walk (drain 0x83f64, gestures_end 0x83f70) sp = the entry sp - 96. ---- *)
Lemma rr_call_chain : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1,
  RBASE B ARx MT RP MMAX RG cx -> RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (rsp0 cx - RR_FRAME) (rsp0 cx) ch1.
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL.
destruct HB as (HPRE & Hsp32 & _).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HL as (fpos & HJ & _ & _ & (_ & _ & _ & HSV) & _).
assert (ET : ly_top ly1 = ly_top (rxly cx)) by (eapply rrk_ajgx_ly_top; exact HJ).
pose proof asan_consts as (C1 & _).
unfold rsp0 in *. unfold RR_FRAME.
destruct (Z_lt_le_dec (spZ (rxregs cx)) (ly_top ly1 - 16)) as [Hlt | Hge].
2:{ exists []. left. split; [right; left; lia | reflexivity]. }
exists ((spZ (rxregs cx), raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx).
apply (achain_push ly1 (aview SEGS (w_H (rxW cx)) (rxmem cx))).
- exact (achain_ly_top _ _ _ _ _ _ ET Hch).
- rewrite ET. unfold RR_STK_x, RR_STK in *. lia.
- intros a Ha. eapply W_gestures_end.gse_keep_high_x; [exact HG | exact HJ | lia | lia].
- pose proof (HSV 10%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 10) with (spZ (rxregs cx) - 8) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 1)) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R.
- pose proof (HSV 9%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 9) with (spZ (rxregs cx) - 16) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 8)) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R.
- exact Hra4.
- lia.
- pose proof (Z.div_mod (spZ (rxregs cx)) 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
  replace (32 * (spZ (rxregs cx) / 32)) with ((4 * (spZ (rxregs cx) / 32)) * 8) by ring. apply Z_mod_mult.
- exact Hlt.
- lia.
Qed.
(* ---- The same chain as a runtime call site's chain_pre (free 0x83f94, __asan_memcpy 0x83fc0): sp = the entry
   sp - 96, s0 = the entry sp, ra >= 4096. ---- *)
Lemma rr_call_chain_pre : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1 (regsT : bvmap 5 word),
  RBASE B ARx MT RP MMAX RG cx -> RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  spZ regsT = rsp0 cx - RR_FRAME -> s0Z regsT = rsp0 cx -> 4096 <= raZ regsT ->
  exists ch1, chain_pre ly1 (aview SEGS (w_H W1) m1) regsT ch1.
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 regsT HB HL Hsp Hs0 Hra.
destruct (rr_call_chain cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL) as (ch1 & Hc).
exists ch1. apply (achain_chain_pre _ _ _ _ _ _ Hc); [|exact Hs0 | exact Hra].
destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
rewrite Hsp. unfold rsp0 in *. unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK in *. lia.
Qed.
(* ---- The same chain, NAMED, for the _c allocator rules' context premise (RCTX's In fact is about this exact
   list): when the entry frame lies below the layout top, the chain is the entry's record pushed onto the
   caller's chain, so its spine is raZ (rxregs cx) :: spine (rxch cx). ---- *)
Lemma rr_call_chain_ctx : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1,
  RBASE B ARx MT RP MMAX RG cx -> RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  spZ (rxregs cx) + 16 < ly_top (rxly cx) ->
  achain ly1 (aview SEGS (w_H W1) m1) (rsp0 cx - RR_FRAME) (rsp0 cx)
    ((rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx).
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL Hlt0.
destruct HB as (HPRE & Hsp32 & _).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HL as (fpos & HJ & _ & _ & (_ & _ & _ & HSV) & _).
assert (ET : ly_top ly1 = ly_top (rxly cx)) by (eapply rrk_ajgx_ly_top; exact HJ).
pose proof asan_consts as (C1 & _).
unfold rsp0 in *. unfold RR_FRAME.
apply (achain_push ly1 (aview SEGS (w_H (rxW cx)) (rxmem cx))).
- exact (achain_ly_top _ _ _ _ _ _ ET Hch).
- rewrite ET. unfold RR_STK_x, RR_STK in *. lia.
- intros a Ha. eapply W_gestures_end.gse_keep_high_x; [exact HG | exact HJ | lia | lia].
- pose proof (HSV 10%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 10) with (spZ (rxregs cx) - 8) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 1)) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R.
- pose proof (HSV 9%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 9) with (spZ (rxregs cx) - 16) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 8)) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R.
- exact Hra4.
- lia.
- pose proof (Z.div_mod (spZ (rxregs cx)) 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
  replace (32 * (spZ (rxregs cx) / 32)) with ((4 * (spZ (rxregs cx) / 32)) * 8) by ring. apply Z_mod_mult.
- rewrite ET. lia.
- lia.
Qed.
Lemma rr_call_chain_pre_ctx : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1 (regsT : bvmap 5 word),
  RBASE B ARx MT RP MMAX RG cx -> RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  spZ (rxregs cx) + 16 < ly_top (rxly cx) ->
  spZ regsT = rsp0 cx - RR_FRAME -> s0Z regsT = rsp0 cx -> 4096 <= raZ regsT ->
  chain_pre ly1 (aview SEGS (w_H W1) m1) regsT
    ((rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx).
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 regsT HB HL Hlt0 Hsp Hs0 Hra.
pose proof (rr_call_chain_ctx cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL Hlt0) as Hc.
apply (achain_chain_pre _ _ _ _ _ _ Hc); [|exact Hs0 | exact Hra].
destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
rewrite Hsp. unfold rsp0 in *. unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK in *. lia.
Qed.


(* ------------------------------------------------------------------ the globals drain's G leaves alone *)
(* g_lock, g_src, g_nsrc, g_capsrc and g_wake[1] are none of G_DR's cells (HRGP's pairs) *)
Ltac rr_pair i j P :=
  pose proof (rr_zpw_nth _ i j HRGP) as P; specialize (P ltac:(cbn [length]; lia));
  cbn [nth] in P; unfold zdisj in P; cbn [fst snd] in P.
Lemma rr_nG_DR : forall a,
  (rg_lock RG <= a < rg_lock RG + 12 \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
   rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_wake RG + 4 <= a < rg_wake RG + 8) -> ~ inG (G_DR B RG) a.
Proof.
intros a Ha HGa. unfold G_DR, G_SL, inG in HGa. rewrite !Exists_cons, Exists_nil in HGa. unfold in_zr in HGa.
cbn [fst snd] in HGa.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- rr_pair 0%nat 1%nat P1. rr_pair 0%nat 6%nat P2. rr_pair 0%nat 7%nat P3. rr_pair 0%nat 8%nat P4.
  rr_pair 0%nat 10%nat P5. rr_pair 0%nat 12%nat P6. rr_pair 0%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 2%nat P1. rr_pair 2%nat 6%nat P2. rr_pair 2%nat 7%nat P3. rr_pair 2%nat 8%nat P4.
  rr_pair 2%nat 10%nat P5. rr_pair 2%nat 12%nat P6. rr_pair 2%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 3%nat P1. rr_pair 3%nat 6%nat P2. rr_pair 3%nat 7%nat P3. rr_pair 3%nat 8%nat P4.
  rr_pair 3%nat 10%nat P5. rr_pair 3%nat 12%nat P6. rr_pair 3%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 4%nat P1. rr_pair 4%nat 6%nat P2. rr_pair 4%nat 7%nat P3. rr_pair 4%nat 8%nat P4.
  rr_pair 4%nat 10%nat P5. rr_pair 4%nat 12%nat P6. rr_pair 4%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
- rr_pair 1%nat 13%nat P1. rr_pair 6%nat 13%nat P2. rr_pair 7%nat 13%nat P3. rr_pair 8%nat 13%nat P4.
  rr_pair 10%nat 13%nat P5. rr_pair 12%nat 13%nat P6. rr_pair 13%nat 14%nat P7.
  clear HRGP. destruct HGa as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; lia.
Qed.
(* g_capsrc is not errno (HRGP's pair 4 / 14) *)
Lemma rr_capsrc_nerr : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. rr_pair 4%nat 14%nat P. clear HRGP. lia. Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps *)
(* an image byte outside the callee's G (inside G_DR), the allocator's statics and errno *)
Lemma rr_img_kept : forall Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
  (forall x, inG Gc x -> inG (G_DR B RG) x) ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  Forall (fun r => 0 < fst r) FP -> apres_kept B W mem W' mem' ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W mem W' mem' a.
Proof.
intros Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a Hs HJ HF HPK Hi Ho He Hq Hg.
split.
- eapply W_gestures_end.gse_keep_img_x; [exact HJ | exact Hi | exact Ho | exact He | exact Hq | |].
  + apply fp_spares_closed. apply sink_closed_pos. exact HF.
  + intros H. exact (Hg (Hs a H)).
- intros Hw. unfold arm in *. apply (rr_writable2 (w_H W) (w_H W') mem mem' a); [|exact Hw].
  intros Hpr. exact (HPK a Hi Ho He Hpr).
Qed.

(* ------------------------------------------------------------------ RLIVE across a program callee *)
(* The walk calls a program function at sp = the entry sp - 96 (drain, gestures_end).  RLIVE at the call, the
   callee's own journal (at its globals Gc, inside G_DR, from sp = rsp0 - 96, with a footprint of block bytes) and
   the caller's composed journal give RLIVE at the callee's return: the fake frame's F + 56 by the callee's frames
   clause (the footprint names blocks, which lie apart from the frames), the saved registers above the callee's
   stack, g_lock and g_wake[1] as image bytes outside Gc (HRGP). *)
Lemma rr_live_call : forall cx F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2,
  RBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
  rom_view SEGS W1 m1 -> apres_kept B (rxW cx) (rxmem cx) W1 m1 -> rr_frame cx fpos F FL ly1 W1 m1 ->
  alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
  gx_ok SEGS B Gc -> (forall a, inG Gc a -> inG (G_DR B RG) a) -> 0 <= STK1 <= DRAIN_STK_x ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc 0 [] STK1 (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 md1 []
    ly2 S2 Hp2 W2 m2 md2 kc ->
  Forall (fun r => 0 < fst r) FP1 ->
  (forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) ->
  apres_kept B W1 m1 W2 m2 ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly2 S2 Hp2 W2 m2 md2 k2 ->
  RLIVE B PST ARx RG cx F FL ly2 S2 Hp2 W2 m2 md2 k2.
Proof.
intros cx F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2 HB HJ1 HROM1 HPK1 HFR1 HLK1 HWK1
  HGc HGcs HSTK1 HJc HFP0 HFPb HPK HJ2.
destruct HB as (HPRE & _ & _ & RGP & _).
destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ1).
assert (HIN : In (0, fpos) (frames S1)).
{ destruct HJ1 as (_ & _ & (memS1 & HJ1i & _) & _). pose proof HJ1i as (_ & _ & _ & _ & _ & HFS & _).
  rewrite HFS. left. reflexivity. }
pose proof HJc as HJcin. apply ajournal_gx_inner_x in HJcin. destruct HJcin as (memS & HJi & HAG).
pose proof HJi as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFRM & _).
destruct HFR1 as (EF & EFL & VFL & HSV).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR1 HIN) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in HFceil. rewrite EF in HF4096, HFceil.
assert (GK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a).
{ intros a Hi Ho He Hq Hg. eapply rr_img_kept;
    [exact HGcs | exact HJc | exact HFP0 | exact HPK | exact Hi | exact Ho | exact He | exact Hq | exact Hg]. }
exists fpos. split; [exact HJ2|].
split.
{ eapply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low); [exact HJc | | exact PSTR | exact HROM1].
  intros a Ha. destruct (HROMO a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
  intros Hg. apply R1. apply rr_G_DR_RR. exact (HGcs a Hg). }
split; [exact (W_gesture_end.apk_trans B _ _ _ _ _ _ HPK1 HPK)|].
split.
{ destruct Hly as (_ & _ & _ & _ & _ & LF & _).
  split; [unfold frame_addr in *; rewrite LF; exact EF|].
  split; [unfold flag_addr in *; rewrite LF; exact EFL|].
  split.
  - apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 (F + 56) 8 FL); [|exact VFL].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    rewrite (HFRM 0 fpos (F + 56 + k) HIN).
    + apply HAG. rewrite unsigned_lit_small by lia. intros Hg.
      apply (frm_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 0 fpos (F + 56 + k) HAR1 HIN);
        [rewrite EF; change (fs_frame_bytes 0) with 64; lia|].
      exact (proj1 (HGc _ Hg)).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
    + intros Hf. destruct (HFPb _ Hf) as (b & n & Hb & Hr).
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n 0 fpos HAR1 Hb HIN) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF in D. change (fs_frame_bytes 0) with 64 in D. lia.
  - intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact (HSV j Hj)].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    eapply W_gestures_end.gse_keep_high_x; [exact HGc | exact HJc | |].
    + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia.
    + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia. }
split.
{ apply (alock_at_kept RG W1 m1 W2 m2 true HLK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
{ apply (awake_at_kept RG W1 m1 W2 m2 HWK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. do 13 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the journal helpers above at a world relation R, for the MATCH hops' R walks.
   Each <name>_xR is <name> with the journal ajournal_gx_x -> ajournal_gx_xR .. R and RLIVE -> W_relay_remove_cx's
   RLIVE_xR (a Theorem Labs lane's text); the proofs are the strict ones over the R twins of the journal helpers they cite
   (rrk_ajgx_ly_top_xR above, W_gestures_end.v gse_keep_high_xR / gse_keep_img_xR, W_journal_x.v ajournal_gx_AR_xR /
   ajournal_gx_inner_xR / ajournal_gx_rom_view_xR).  None reads the world conjunct, so none takes a law of R.  The
   journal-free helpers (rr_zall_nth, rr_zpw_nth, rr_writable2, rr_nG_DR, rr_capsrc_nerr) serve both forms. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :189 rr_call_chain at R *)
Lemma rr_call_chain_xR : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1,
  RBASE B ARx MT RP MMAX RG cx -> RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  exists ch1, achain ly1 (aview SEGS (w_H W1) m1) (rsp0 cx - RR_FRAME) (rsp0 cx) ch1.
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL.
destruct HB as (HPRE & Hsp32 & _).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HL as (fpos & HJ & _ & _ & (_ & _ & _ & HSV) & _).
assert (ET : ly_top ly1 = ly_top (rxly cx)) by (eapply rrk_ajgx_ly_top_xR; exact HJ).
pose proof asan_consts as (C1 & _).
unfold rsp0 in *. unfold RR_FRAME.
destruct (Z_lt_le_dec (spZ (rxregs cx)) (ly_top ly1 - 16)) as [Hlt | Hge].
2:{ exists []. left. split; [right; left; lia | reflexivity]. }
exists ((spZ (rxregs cx), raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx).
apply (achain_push ly1 (aview SEGS (w_H (rxW cx)) (rxmem cx))).
- exact (achain_ly_top _ _ _ _ _ _ ET Hch).
- rewrite ET. unfold RR_STK_x, RR_STK in *. lia.
- intros a Ha. eapply W_gestures_end.gse_keep_high_xR; [exact HG | exact HJ | lia | lia].
- pose proof (HSV 10%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 10) with (spZ (rxregs cx) - 8) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 1)) as R0. change (bv_modulus 64) with (2 ^ 64) in R0. exact R0.
- pose proof (HSV 9%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 9) with (spZ (rxregs cx) - 16) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 8)) as R0. change (bv_modulus 64) with (2 ^ 64) in R0. exact R0.
- exact Hra4.
- lia.
- pose proof (Z.div_mod (spZ (rxregs cx)) 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
  replace (32 * (spZ (rxregs cx) / 32)) with ((4 * (spZ (rxregs cx) / 32)) * 8) by ring. apply Z_mod_mult.
- exact Hlt.
- lia.
Qed.
(* :225 rr_call_chain_pre at R *)
Lemma rr_call_chain_pre_xR : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1 (regsT : bvmap 5 word),
  RBASE B ARx MT RP MMAX RG cx -> RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  spZ regsT = rsp0 cx - RR_FRAME -> s0Z regsT = rsp0 cx -> 4096 <= raZ regsT ->
  exists ch1, chain_pre ly1 (aview SEGS (w_H W1) m1) regsT ch1.
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 regsT HB HL Hsp Hs0 Hra.
destruct (rr_call_chain_xR cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL) as (ch1 & Hc).
exists ch1. apply (achain_chain_pre _ _ _ _ _ _ Hc); [|exact Hs0 | exact Hra].
destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
rewrite Hsp. unfold rsp0 in *. unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK in *. lia.
Qed.
(* :240 rr_call_chain_ctx at R *)
Lemma rr_call_chain_ctx_xR : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1,
  RBASE B ARx MT RP MMAX RG cx -> RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  spZ (rxregs cx) + 16 < ly_top (rxly cx) ->
  achain ly1 (aview SEGS (w_H W1) m1) (rsp0 cx - RR_FRAME) (rsp0 cx)
    ((rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx).
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL Hlt0.
destruct HB as (HPRE & Hsp32 & _).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HL as (fpos & HJ & _ & _ & (_ & _ & _ & HSV) & _).
assert (ET : ly_top ly1 = ly_top (rxly cx)) by (eapply rrk_ajgx_ly_top_xR; exact HJ).
pose proof asan_consts as (C1 & _).
unfold rsp0 in *. unfold RR_FRAME.
apply (achain_push ly1 (aview SEGS (w_H (rxW cx)) (rxmem cx))).
- exact (achain_ly_top _ _ _ _ _ _ ET Hch).
- rewrite ET. unfold RR_STK_x, RR_STK in *. lia.
- intros a Ha. eapply W_gestures_end.gse_keep_high_xR; [exact HG | exact HJ | lia | lia].
- pose proof (HSV 10%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 10) with (spZ (rxregs cx) - 8) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 1)) as R0. change (bv_modulus 64) with (2 ^ 64) in R0. exact R0.
- pose proof (HSV 9%nat ltac:(lia)) as V. cbn [nth RR_SAVED] in V. unfold RR_FRAME, rsp0 in V.
  replace (spZ (rxregs cx) - 96 + 8 + 8 * Z.of_nat 9) with (spZ (rxregs cx) - 16) in V by lia.
  apply (rdword_of_val_mem SEGS _ _ _ _ V).
  pose proof (bv_unsigned_in_range 64 (getr (rxregs cx) 8)) as R0. change (bv_modulus 64) with (2 ^ 64) in R0. exact R0.
- exact Hra4.
- lia.
- pose proof (Z.div_mod (spZ (rxregs cx)) 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
  replace (32 * (spZ (rxregs cx) / 32)) with ((4 * (spZ (rxregs cx) / 32)) * 8) by ring. apply Z_mod_mult.
- rewrite ET. lia.
- lia.
Qed.
(* :273 rr_call_chain_pre_ctx at R *)
Lemma rr_call_chain_pre_ctx_xR : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1 (regsT : bvmap 5 word),
  RBASE B ARx MT RP MMAX RG cx -> RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  spZ (rxregs cx) + 16 < ly_top (rxly cx) ->
  spZ regsT = rsp0 cx - RR_FRAME -> s0Z regsT = rsp0 cx -> 4096 <= raZ regsT ->
  chain_pre ly1 (aview SEGS (w_H W1) m1) regsT
    ((rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx).
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 regsT HB HL Hlt0 Hsp Hs0 Hra.
pose proof (rr_call_chain_ctx_xR cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HL Hlt0) as Hc.
apply (achain_chain_pre _ _ _ _ _ _ Hc); [|exact Hs0 | exact Hra].
destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
rewrite Hsp. unfold rsp0 in *. unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK in *. lia.
Qed.
(* :332 rr_img_kept at R *)
Lemma rr_img_kept_xR : forall Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
  (forall x, inG Gc x -> inG (G_DR B RG) x) ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc 0 [] STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  Forall (fun r => 0 < fst r) FP -> apres_kept B W mem W' mem' ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W mem W' mem' a.
Proof.
intros Gc STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a Hs HJ HF HPK Hi Ho He Hq Hg.
split.
- eapply W_gestures_end.gse_keep_img_xR; [exact HJ | exact Hi | exact Ho | exact He | exact Hq | |].
  + apply fp_spares_closed. apply sink_closed_pos. exact HF.
  + intros H. exact (Hg (Hs a H)).
- intros Hw. unfold arm in *. apply (rr_writable2 (w_H W) (w_H W') mem mem' a); [|exact Hw].
  intros Hpr. exact (HPK a Hi Ho He Hpr).
Qed.
(* :354 rr_live_call at R: the caller's journal, the callee's own and the composed one at R *)
Lemma rr_live_call_xR : forall cx F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2,
  RBASE B ARx MT RP MMAX RG cx ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
  rom_view SEGS W1 m1 -> apres_kept B (rxW cx) (rxmem cx) W1 m1 -> rr_frame cx fpos F FL ly1 W1 m1 ->
  alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
  gx_ok SEGS B Gc -> (forall a, inG Gc a -> inG (G_DR B RG) a) -> 0 <= STK1 <= DRAIN_STK_x ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc 0 [] STK1 (rsp0 cx - RR_FRAME) FP1 ly1 S1 Hp1 W1 m1 md1 []
    ly2 S2 Hp2 W2 m2 md2 kc ->
  Forall (fun r => 0 < fst r) FP1 ->
  (forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) ->
  apres_kept B W1 m1 W2 m2 ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly2 S2 Hp2 W2 m2 md2 k2 ->
  RLIVE_xR B PST ARx RG R cx F FL ly2 S2 Hp2 W2 m2 md2 k2.
Proof.
intros cx F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 Gc STK1 FP1 ly2 S2 Hp2 W2 m2 md2 kc k2 HB HJ1 HROM1 HPK1 HFR1 HLK1 HWK1
  HGc HGcs HSTK1 HJc HFP0 HFPb HPK HJ2.
destruct HB as (HPRE & _ & _ & RGP & _).
destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ1).
assert (HIN : In (0, fpos) (frames S1)).
{ destruct HJ1 as (_ & _ & (memS1 & HJ1i & _) & _). pose proof HJ1i as (_ & _ & _ & _ & _ & HFS & _).
  rewrite HFS. left. reflexivity. }
pose proof HJc as HJcin. apply ajournal_gx_inner_xR in HJcin. destruct HJcin as (memS & HJi & HAG).
pose proof HJi as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFRM & _).
destruct HFR1 as (EF & EFL & VFL & HSV).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR1 HIN) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in HFceil. rewrite EF in HF4096, HFceil.
assert (GK : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 m2 a).
{ intros a Hi Ho He Hq Hg. eapply rr_img_kept_xR;
    [exact HGcs | exact HJc | exact HFP0 | exact HPK | exact Hi | exact Ho | exact He | exact Hq | exact Hg]. }
exists fpos. split; [exact HJ2|].
split.
{ eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low); [exact HJc | | exact PSTR | exact HROM1].
  intros a Ha. destruct (HROMO a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
  intros Hg. apply R1. apply rr_G_DR_RR. exact (HGcs a Hg). }
split; [exact (W_gesture_end.apk_trans B _ _ _ _ _ _ HPK1 HPK)|].
split.
{ destruct Hly as (_ & _ & _ & _ & _ & LF & _).
  split; [unfold frame_addr in *; rewrite LF; exact EF|].
  split; [unfold flag_addr in *; rewrite LF; exact EFL|].
  split.
  - apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2 (F + 56) 8 FL); [|exact VFL].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    rewrite (HFRM 0 fpos (F + 56 + k) HIN).
    + apply HAG. rewrite unsigned_lit_small by lia. intros Hg.
      apply (frm_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 0 fpos (F + 56 + k) HAR1 HIN);
        [rewrite EF; change (fs_frame_bytes 0) with 64; lia|].
      exact (proj1 (HGc _ Hg)).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
    + intros Hf. destruct (HFPb _ Hf) as (b & n & Hb & Hr).
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n 0 fpos HAR1 Hb HIN) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF in D. change (fs_frame_bytes 0) with 64 in D. lia.
  - intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact (HSV j Hj)].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    eapply W_gestures_end.gse_keep_high_xR; [exact HGc | exact HJc | |].
    + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia.
    + unfold rsp0, RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK in *. lia. }
split.
{ apply (alock_at_kept RG W1 m1 W2 m2 true HLK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
{ apply (awake_at_kept RG W1 m1 W2 m2 HWK1). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct (RGIMG a ltac:(unfold rg_rng; lia)) as (Hi & Ho & He). apply GK; [exact Hi | exact Ho | exact He | |].
  - apply PSTG. unfold rr_gcells. do 13 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia.
  - apply rr_nG_DR. lia. }
Qed.
End wR.

End c.
End b.
End a.
