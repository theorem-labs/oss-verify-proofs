(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   relay_finish, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)),
   after lib/A/W_relay_finish_h.v (a working branch a3987bff22c: its loop rf_loop and its tail rf_tail), in the
   form of the B walks lib/B/W_check_bounded.v (a working branch 7e062bb9b9c) and lib/B/W_gse_loop.v
   (a working branch bb5ed8a0689). *)
(* Modified by Theorem Labs, 2026-10: the room `_x` form (a Theorem Labs lane, RoomRFB): the walk is pb_relay_finish_x,
   stated over any allocator relation ARx with its laws as W_contract_x.v rf_spec_x (Section c below: PST / ARx / hl /
   LAWS / HP0 / BLKN, the callees' and the allocator rules' `_x` twins, PSTR / PSTC), and it threads rf_spec_x's room
   round: the budget rp_RM RP (each round: the free's 1, then gestures_end's charge) and the count premise
   cnt_ok_pk RP rf_pk (rf_pk = 5) to the free (cnt_ok) and to gestures_end (gse_pk = 4); the round's room bound follows
   rf_room's `- cap` threading (the round frees the old g_out block).  The room argument is lib/A/W_relay_finish_h.v's
   (a working branch 9e4f84a8fb9), the ARx form that of lib/B/W_list_free.v / W_source_reset.v
   (a working branch dfa1a225350).
   B's relay_finish sets no frame pointer and calls no __asan_stack_malloc, so A's fake-frame seat, its set_fs step and rp_RPF across the seat do not apply.
   pb_relay_finish keeps its statement, byte-identical, and its Section hypotheses (the same terms in the same order;
   HPLAIN / HWSEG write rf_cells as rf_cells RG GTU GL): it is re-derived from pb_relay_finish_x at ARx := ARi0,
   PST := [], RP := RP_AR (Section cAR); pb_relay_finish_fr / _fr_tfib are unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_relay_finish.v, with its module paths and module names changed; 30 of its 116 lines of code are new or changed and 4257 lines of the source are left out. *)
(* Theorem Labs, 2026-10: LX0 for image B (asan-ubsan) of plugin-hostd/fuzz_reply, the B twin of lib/A/ReplyATop.v
   atop_LX0 (commit 5ab58d26200, :176).  One writer: a Theorem Labs lane (a Theorem Labs lane's placement, 2026-10-30 00:30Z).

   LX0 is the laws a re-derived (ARx) walk takes in place of LAWS : AR_laws, stated at cgif's AR with an empty ghost list
   (W_journal_x.v ARi0).  The Section lx below is WBIntegrate's draft (LX0-B-draft.v),
   taken whole: the B-side restatement of lib/A/W_laws_x.v AR_laws_x_ARi0_of (XcfFinish, commit
   17dd7592e52) and of the lemma it rests on, lib/A/W_alloc_tail.v alloc_tail (W7 / a Theorem Labs lane).  Both are generic in
   segs and B and use Reusable modules only, so the text is A's with names prefixed lx_; lib/B carries neither file.
   AR_laws_x_of_AR (Reusable/YCbqG.v) takes three facts beyond AR_laws, each a theorem of cgif's AR itself: the 8-aligned
   stack bounds (layout_ok's lo_top, carried by ARm's am_layout), a live block's tail granule viewable (lx_alloc_tail),
   and the const cells (am_const).

   b_LX0 is the instance: the laws at B := YD2l.TfibB, for any segment list, from Reusable/YG0q.v AR_laws_ok (which holds
   at any segs and B, as atop_LAWS uses it).  Consumers: the image-B drain (W_drain_drop.v's list_drop call through
   W_list_drop.v pb_list_drop_ro_c), WBIntegrate's W_asm.v, and a Theorem Labs lane's ARx walks. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_kit W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_journal_x YD2l.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- LX0, the laws a re-derived (ARx) walk takes in place of LAWS : AR_laws.  B-side twin of lib/A/W_laws_x.v
   AR_laws_x_ARi0_of (XcfFinish, commit 17dd7592e52) and of the lemma it rests on,
   lib/A/W_alloc_tail.v alloc_tail (W7 / a Theorem Labs lane).  Both are generic in segs and B and use Reusable modules only, so
   the text is A's; lib/B carries neither file, hence the restatement here.  AR_laws_x_of_AR (Reusable/YCbqG.v:1677)
   takes three facts beyond AR_laws, each a theorem of cgif's AR itself: the 8-aligned stack bounds (layout_ok's lo_top,
   carried by ARm's am_layout), a live block's tail granule viewable (lx_alloc_tail), and the const cells (am_const). ---- *)
Section lx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0s.
Lemma lx_in_zseq : forall lo n a, lo <= a < lo + n -> In a (YG0n.zseq lo n).
Proof.
intros lo n a H. unfold YG0n.zseq. apply in_map_iff. exists (Z.to_nat (a - lo)). split.
- rewrite Z2Nat.id by lia. lia.
- apply in_seq. lia.
Qed.
Lemma lx_cls8 : forall c, 1 <= c <= 30 -> class_size c mod 8 = 0.
Proof.
intros c Hc.
assert (A : forallb (fun c => class_size c mod 8 =? 0) (YG0n.zseq 1 30) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. apply Z.eqb_eq. apply A. apply lx_in_zseq. lia.
Qed.
Lemma lx_ext8 : forall (B : asyms) ly S k, cfacts B ly S k -> ck_extent k mod 8 = 0.
Proof.
intros B ly S k (_ & _ & _ & _ & _ & _ & _ & _ & G9).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct G9].
- cbv beta iota zeta in G9. destruct G9 as (Hc & _ & _ & He & _). rewrite He. apply lx_cls8. exact Hc.
- cbv beta iota in G9. destruct G9 as (_ & _ & _ & He & _). rewrite He. unfold sec_map_size, round_up, kPage.
  assert (E : forall q, (q * 4096 + 4096 - 4096) mod 8 = 0)
    by (intros q; replace (q * 4096 + 4096 - 4096) with (q * 512 * 8) by lia; apply Z.mod_mul; lia).
  apply E.
Qed.
Lemma lx_alloc_tail : forall (segs : list Segment) (B : asyms) ly S (W : world segs) mem md p n a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros segs B ly S W mem md p n a HAR Hin Ha.
destruct HAR as (HM & _).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr).
pose proof (chunk_facts B ly S _ k HM Hk) as CF.
pose proof (lx_ext8 B ly S k CF) as E8.
destruct CF as (_ & _ & G3 & G4 & _ & _ & _ & G8 & _).
assert (HJ : In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S)).
{ unfold ajunk. right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_junk.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ HM) _ HJ) as V.
unfold range_vis in V. cbn [fst snd] in V.
rewrite aeval_aoff in V by (intros e' Ee; destruct (ck_beg k); cbn in Ee; discriminate Ee).
change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
unfold ck_n in V. rewrite <- Hu, G4, <- Hr in Ha.
pose proof (Z.div_mod (ck_base B ly k) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (ck_extent k) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (ck_base B ly k + ck_rz k + req_size (ck_req k) - 1) 8 ltac:(lia)) as D4.
specialize (V (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k))))).
replace (ck_base B ly k + (ck_rz k + req_size (ck_req k)) + (a - (ck_base B ly k + (ck_rz k + req_size (ck_req k)))))
  with a in V by lia.
apply V. lia.
Qed.
Lemma lx_stk8 : forall segs B ly S W mem md, AR segs B ly S W mem md -> ly_stk_lo ly mod 8 = 0 /\ ly_stk_hi ly mod 8 = 0.
Proof.
intros segs B ly S W mem md (HM & _).
pose proof (lo_top _ (am_layout _ _ _ _ HM)) as (_ & _ & _ & _ & H1 & H2 & _).
unfold page_aligned in H1, H2. try unfold page_size in H1, H2.
assert (D : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->].
  replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult. }
split; apply D; assumption.
Qed.
Lemma lx_tail : forall segs B ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n <= a < (p + req_size n + 7) / 8 * 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros segs B ly S W mem md p n a HAR Hin Ha.
apply (lx_alloc_tail segs B ly S W mem md p n a HAR Hin).
assert (E : (p + req_size n + 7) / 8 * 8 = p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8).
{ replace (p + req_size n + 7) with (p + req_size n - 1 + 1 * 8) by lia.
  rewrite Z.div_add by lia. pose proof (Z.div_mod (p + req_size n - 1) 8 ltac:(lia)). lia. }
lia.
Qed.
Lemma lx_const : forall segs B ly S W mem md, AR segs B ly S W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly).
Proof. intros segs B ly S W mem md (HM & _). exact (am_const _ _ _ _ HM). Qed.
(* A's AR_laws_x_ARi0_of, at any segs and B *)
Lemma lx_AR_laws_x_ARi0_of : forall segs B, AR_laws segs B ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbqG.AR_laws_x segs B (W_journal_x.ARi0 segs B) 0.
Proof.
intros segs B L.
exact (W_journal_x.AR_laws_x_ARi0 segs B
  (OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbqG.AR_laws_x_of_AR segs B L
     (lx_stk8 segs B) (lx_tail segs B) (lx_const segs B))).
Qed.
End lx.

(* ---- b_LX0: the instance at image B's symbols YD2l.TfibB (atop_LX0's twin; AR_laws_ok holds at any segs and B, as
   ReplyATop.v:103-104 atop_LAWS uses it).  Stated for every segment list, so each consumer takes it at its own SEGS. ---- *)
Lemma b_LX0 : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (segs : list Segment),
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbqG.AR_laws_x (rc := rc) segs YD2l.TfibB
    (W_journal_x.ARi0 (rc := rc) segs YD2l.TfibB) 0.
Proof.
intros fx rc segs.
exact (@lx_AR_laws_x_ARi0_of fx rc segs YD2l.TfibB (YG0q.AR_laws_ok _ _)).
Qed.
