(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the TAIL segment of the ASan walk of fuzz_reply's relay_remove
   (W_relay_remove_cx.v rr_tail_stmt): from the unlock cut RRU oi (0x83fc4) through pthread_mutex_unlock (g_lock)
   0x83fd0, the wake byte 0x83fd8-0x83fdc, the wake test 0x83fe8 (g_wake[1] = -1: the write 0x83ff4 is not taken),
   the fake frame's release 0x83ff8-0x84038 (retired magic, shadow 0xf5, *flag = 0) and the epilogue 0x84060 to
   the return, in the form of lane W7's W_drain_epi.v (a fresh symbolic state seated at the cut). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (a Theorem Labs lane, lane RR_x): TAIL over ARx in the room form
   (Section c is W_relay_remove_cx.v's generic block); the journal is ajournal_gx_x (the head set after each state),
   the laws and frame lemmas their _x twins, the unlock at aunlock_realizes_x through aj_gx_entry_at_x, the release
   at aj_flag_store_pi_x.  The room: RRU None's RHELD budget gives rp_RM RP S1 kr by RMM_of, RRU (Some i)'s RDONE
   carries it; the unlock keeps S1 and the release is a stack_free_state step (RPF_stack_free), so rr_post_x's
   rp_RM RP S' kr holds.  The helpers the match lanes and RIG cite keep their statements. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_relay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
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

(* ---- What the walk from 0x83fc4 to the return delivers (rr_tail_walk), and what rr_post_x is made of
   (rr_tail_post).  The tail writes only g_lock's lock word (the unlock: 16 -> 0), the fake frame F (the byte
   F + 32 at 0x83fdc, the retired magic at F + 0), F's eight shadow bytes and the flag cell FL (the release), and
   the unlock's scratch below sp; every other byte keeps its ASan view and every present byte stays present.
   The journal ends owning nothing: the frame (0, fpos) is released (stack_free_state); the head set stays Hp1. ---- *)
Definition rr_tail_out (cx : rcx) (fpos F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (regs' : bvmap 5 word) (m' : word -> option byte) (md' : Model) (k' : Z) : Prop :=
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 (stack_free_state 0 fpos S1) Hp1 W1 m' md' k' /\
aregs_preserved (rxregs cx) regs' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> ~ (F <= a < F + 64) ->
   ~ (shadow_addr F <= a < shadow_addr F + 8) -> a <> FL ->
   ~ (rsp0 cx - RR_FRAME - ESTACK <= a < rsp0 cx - RR_FRAME) ->
   aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m1 a) /\
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m' a) /\
val_mem SEGS (arm W1 m') (rg_lock RG + 4) 4 0.

(* ---- rr_tail_post's helpers. ----
   rkz: the bytes rr_tail_out keeps (image bytes off the lock word, the bytes of live blocks); rfz: a footprint all
   of whose bytes are such. *)
Definition rkz (ly : alayout) (S : astate) (a : Z) : Prop :=
  (in_img SEGS a /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)) \/
  (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n).
Definition rfz (ly : alayout) (S : astate) (fp : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> rkz ly S a.
Lemma rfz_nil : forall ly S, rfz ly S [].
Proof. intros ly S r []. Qed.
Lemma rfz_cons : forall ly S r fp,
  (forall a, fst r <= a < snd r -> rkz ly S a) -> rfz ly S fp -> rfz ly S (r :: fp).
Proof. intros ly S r fp H1 H2 r' [<- | Hr]; [exact H1 | exact (H2 r' Hr)]. Qed.
Lemma rfz_app : forall ly S f1 f2, rfz ly S f1 -> rfz ly S f2 -> rfz ly S (f1 ++ f2).
Proof. intros ly S f1 f2 H1 H2 r Hr. apply in_app_or in Hr as [Hr | Hr]; [exact (H1 r Hr) | exact (H2 r Hr)]. Qed.
Lemma rkz_blk : forall ly S p n len a,
  In (p, n) (ablocks B ly S) -> 0 <= n -> len <= n -> p <= a < p + len -> rkz ly S a.
Proof.
intros ly S p n len a Hin Hn Hl Ha. right. exists p, n. split; [exact Hin|].
pose proof (req_size_pos n Hn) as [_ Hr]. lia.
Qed.
Lemma rr_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rr_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma rr_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, rr_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma rr_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.

(* the footprints of the representation predicates are kept bytes, and name live blocks *)
Lemma rfz_alist : forall ly S W mem LA l lines,
  alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> rkz ly S a) ->
  rfz ly S (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA.
rewrite Forall_forall in H9.
unfold alist_fp, alist_blks. split.
- apply rfz_cons; [exact HLA|]. apply rfz_app.
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply rfz_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    apply rfz_cons; [|apply rfz_nil]. cbn [gfp fst snd]. intros a Ha.
    rewrite rr_bzs_len, length_app, Nat2Z.inj_add, rr_concat_len, Hj in Ha. unfold hl_n, AREC in *.
    apply (rkz_blk ly S (hl_v l) (16 * hl_cap l) (16 * hl_cap l) a Hin); lia.
  + intros r Hr. apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd]. intros a Ha.
    destruct (H9 x Hx) as (K1 & _). rewrite rr_bzs_len, length_app in Ha. cbn [length] in Ha.
    apply (rkz_blk ly S (fst x) (Z.of_nat (length (snd x)) + 1) (Z.of_nat (length (snd x)) + 1) a K1); lia.
- intros b Hb. apply in_app_or in Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  + apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)).
Qed.
Lemma rfz_asrc : forall ly S W mem HA h,
  asrc_at B ly S W mem HA h -> (forall a, HA <= a < HA + ASRC -> rkz ly S a) ->
  rfz ly S (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem HA h HS HHA.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                  _ & Hexp & Hheld & _).
assert (K16 : forall a, HA + 16 <= a < HA + 16 + 16 -> rkz ly S a) by (intros a Ha; apply HHA; unfold ASRC; lia).
assert (K64 : forall a, HA + 64 <= a < HA + 64 + 16 -> rkz ly S a) by (intros a Ha; apply HHA; unfold ASRC; lia).
assert (K80 : forall a, HA + 80 <= a < HA + 80 + 16 -> rkz ly S a) by (intros a Ha; apply HHA; unfold ASRC; lia).
destruct (rfz_alist ly S W mem (HA + 16) (hs_pending h) false Hpend K16) as [A1 A2].
destruct (rfz_alist ly S W mem (HA + 64) (hs_expected h) true Hexp K64) as [E1 E2].
destruct (rfz_alist ly S W mem (HA + 80) (hs_held h) true Hheld K80) as [L1 L2].
unfold asrc_fp, asrc_blks. split.
- apply rfz_cons; [exact HHA|]. apply rfz_cons.
  + cbn [gfp fst snd]. intros a Ha. rewrite rr_bzs_len, Hpj in Ha.
    apply (rkz_blk ly S (hs_partial h) APARTIAL APARTIAL a Hpb); unfold APARTIAL in *; lia.
  + apply rfz_app; [exact A1|]. apply rfz_app; [exact E1 | exact L1].
- intros b [<- | Hb]; [exact Hpb|]. apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (L2 b Hb)].
Qed.
Lemma rfz_aentry : forall ly S W mem e,
  aentry_ok B ly S W mem e ->
  rfz ly S (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
rewrite Forall_forall in K15.
unfold aentry_fp, aentry_blks. split.
- apply rfz_app.
  + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply rfz_nil|].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
    apply rfz_cons; [|apply rfz_nil]. cbn [gfp fst snd]. intros a Ha.
    rewrite rr_bzs_len, length_app, Nat2Z.inj_add, Hj, K7 in Ha.
    apply (rkz_blk ly S (re_buf e) (re_cap e) (re_cap e) a Hin); lia.
  + apply rfz_cons.
    * cbn [gfp fst snd]. intros a Ha. rewrite rr_bzs_len, rr_key_ptrs_len in Ha.
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      { rewrite Hks in Ha. cbn [length] in Ha. lia. }
      unfold re_nheld in Hk1.
      apply (rkz_blk ly S (re_hp e) (re_kh e) (Z.of_nat (8 * length (re_keys e))) a Hin); lia.
    * intros r Hr. apply in_map_iff in Hr as (k & <- & Hk). cbn [gfp fst snd]. intros a Ha.
      destruct (K15 k Hk) as (M1 & _). rewrite rr_bzs_len, length_app in Ha. cbn [length] in Ha.
      apply (rkz_blk ly S (key_addr k) (Z.of_nat (length (key_text k)) + 1) (Z.of_nat (length (key_text k)) + 1) a M1);
        lia.
- intros b Hb. apply in_app_or in Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  + apply in_app_or in Hb as [Hb | Hb].
    * destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    * apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)).
Qed.
Lemma rfz_arelay : forall ly S W mem G es,
  arelay_at B RG ly S W mem G es ->
  (forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
             rg_capsrc RG <= a < rg_capsrc RG + 4 -> rkz ly S a) ->
  rfz ly S (arelay_fp RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HC.
rewrite Forall_forall in R10.
unfold arelay_fp, arelay_blks. split.
- apply rfz_cons; [cbn [fst snd]; intros a Ha; apply HC; left; exact Ha|].
  apply rfz_cons; [cbn [fst snd]; intros a Ha; apply HC; right; left; exact Ha|].
  apply rfz_cons; [cbn [fst snd]; intros a Ha; apply HC; right; right; exact Ha|].
  apply rfz_cons; [cbn [fst snd]; intros a Ha; apply (rkz_blk ly S G ATABLE ATABLE a R8); unfold ATABLE in *; lia|].
  intros r Hr. apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
  exact (proj1 (rfz_aentry ly S W mem e (R10 e He)) r Hr).
- intros b [<- | Hb]; [exact R8|]. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
  exact (proj2 (rfz_aentry ly S W mem e (R10 e He)) b Hb).
Qed.
(* W_gesture_end.v's aout_fp_cases (W4Gesture) *)
Lemma rr_aout_fp_cases : forall cap out r, In r (aout_fp B RG cap out) ->
  In r (aout_fp B RG 0 0) \/ (cap <> 0 /\ r = (out, out + cap)).
Proof.
intros cap out r Hr. unfold aout_fp in Hr |- *. cbn [Z.eqb] in *.
do 9 (destruct Hr as [Hr | Hr]; [left; subst r; cbn; tauto|]).
destruct (Z.eqb_spec cap 0); [destruct Hr | destruct Hr as [<- | []]; right; split; [exact n | reflexivity]].
Qed.
Lemma rfz_aout : forall ly S W mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> rfz ly S (aout_fp B RG 0 0) ->
  rfz ly S (aout_fp B RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem c O mx no cap out HO HC.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Hblk).
split.
- intros r Hr a Ha. destruct (rr_aout_fp_cases cap out r Hr) as [Hr0 | (Hc & ->)]; [exact (HC r Hr0 a Ha)|].
  destruct Hblk as [(Hc0 & _) | (Hcp & _ & Hin & _)]; [lia|].
  cbn [fst snd] in Ha. apply (rkz_blk ly S out cap cap a Hin); lia.
- intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
  destruct Hb as [<- | []]. destruct Hblk as [(Hc0 & _) | (_ & _ & Hin & _)]; [lia | exact Hin].
Qed.

(* the global cells the post reads (rr_post's g_s, the table's and the stream's cells, g_wake[1]): image bytes
   (rg_place, gx_ok, HRGI) apart from g_lock (HRGP) *)
Definition rr_cells (a : Z) : Prop :=
  rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
  rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
  rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
  rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
  rg_wake RG + 4 <= a < rg_wake RG + 8 \/ as_errno B <= a < as_errno B + 4.
Ltac rr_exists := repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Lemma rrt_cell_img : rg_place B RG -> forall a, rr_cells a -> in_img SEGS a.
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). unfold rr_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
first [ exact (proj1 (RGIMG a ltac:(unfold rg_rng; tauto)))
      | exact (proj1 (HRGI a ltac:(tauto)))
      | exact (proj1 (HG a ltac:(unfold inG, G_RR, G_DR, G_SL; rr_exists))) ].
Qed.
Lemma rrt_cell_nlock : forall a, rr_cells a -> ~ (rg_lock RG <= a < rg_lock RG + 12).
Proof.
intros a Ha. pose proof HRGP as [HL _]. cbn [zall_disjoint] in HL. unfold zdisj in HL. cbn [fst snd] in HL.
destruct HL as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _).
unfold rr_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
[revert D1 Ha | revert D2 Ha | revert D3 Ha | revert D4 Ha | revert D5 Ha | revert D6 Ha | revert D7 Ha |
 revert D8 Ha | revert D9 Ha | revert D10 Ha | revert D11 Ha | revert D12 Ha | revert D13 Ha | revert D14 Ha];
clear; intros; lia.
Qed.
Lemma rrt_cell_kz : forall ly S a, rg_place B RG -> rr_cells a -> rkz ly S a.
Proof.
intros ly S a RGP Ha. left. split; [exact (rrt_cell_img RGP a Ha)|].
pose proof (rrt_cell_nlock a Ha) as Hn. lia.
Qed.

(* THE KEEP: a byte rkz at the cut keeps its view through the tail (rr_tail_out's third conjunct: it is none of the
   lock word, the frame F, its shadow, the flag cell and the scratch) and its writability (presence grows). *)
Lemma rrt_kept : forall ly1 S1 Hp1 W1 m1 md1 m' fpos F FL sp0 a,
  ARx ly1 S1 Hp1 W1 m1 md1 -> In (0, fpos) (frames S1) ->
  frame_addr ly1 0 fpos = F -> flag_addr ly1 0 fpos = FL ->
  alloc_ceiling <= sp0 - RR_FRAME - ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> ~ (F <= a < F + 64) ->
     ~ (shadow_addr F <= a < shadow_addr F + 8) -> a <> FL ->
     ~ (sp0 - RR_FRAME - ESTACK <= a < sp0 - RR_FRAME) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m' a) ->
  (forall a, rg_lock RG + 4 <= a < rg_lock RG + 8 -> in_img SEGS a) ->
  rkz ly1 S1 a -> abyte_kept W1 m1 W1 m' a.
Proof.
intros ly1 S1 Hp1 W1 m1 md1 m' fpos F FL sp0 a HAR HIN EF EFL HSC V P HLI Ha.
split; [|intros Hw; unfold arm in *; exact (writable_kept (w_H W1) m1 m' a (P a) Hw)].
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR HIN) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in HFceil. rewrite EF in HF4096, HFceil.
pose proof (shadow_addr_bounds F ltac:(lia)) as (SH1 & _).
pose proof (shadow_range_end F 64 ltac:(lia)) as SH2. change (64 / 8) with 8 in SH2.
pose proof (shadow_addr_bounds (F + 64) ltac:(lia)) as (_ & SH3).
destruct (FFL _ _ _ _ _ _ 0 fpos HAR HIN) as (_ & HFLo & (_ & HFLi) & _). rewrite EFL in HFLo, HFLi.
destruct Ha as [(Himg & Hnl) | (p & n & Hin & Hpa)].
- pose proof (Hsegs a Himg) as Hl.
  apply V.
  + revert Hl C5. clear. intros. lia.
  + exact Hnl.
  + intros Hf. refine (proj2 (alx_client_img _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 a HAR _) Himg).
    right. left. exists 0, fpos. split; [exact HIN|]. change (fs_frame_bytes 0) with 64. rewrite EF. exact Hf.
  + intros Hs. revert Hl SH1 Hs. clear. intros. lia.
  + intros ->. exact (HFLi Himg).
  + intros Hs. revert Hl HSC C1 C5 Hs. clear. intros. lia.
- destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR Hin) as (_ & Hp4096 & Hpceil & Happ & Hpno & _).
  pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 p n HAR Hin) as Hn.
  apply V.
  + revert Hp4096 Hpceil Hpa C1 Hn. clear. intros. pose proof (req_size_pos n ltac:(lia)). lia.
  + intros Hw. refine (proj2 (alx_client_img _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 a HAR _) (HLI a Hw)).
    left. exists p, n. split; [exact Hin | exact Hpa].
  + intros Hf. pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 0 fpos HAR Hin HIN) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. rewrite EF in Hd.
    revert Hd Hf Hpa. clear. intros. lia.
  + intros Hs. revert Happ Hs Hpa SH1 SH2 SH3. clear.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd. intros. lia.
  + intros ->. exact (proj2 (Hpno FL Hpa) HFLo).
  + intros Hs. revert Hpceil Hpa HSC Hs. clear. intros. lia.
Qed.

Lemma abyte_kept_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof.
intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))].
Qed.
Lemma rr_find_none : forall es FD, (forall e, In e es -> re_fd e <> FD) -> find (fun e => re_fd e =? FD) es = None.
Proof.
induction es as [|e es IH]; intros FD NM; [reflexivity|]. cbn [find].
destruct (Z.eqb_spec (re_fd e) FD) as [E|E]; [exfalso; exact (NM e (or_introl eq_refl) E)|].
apply IH. intros e' He'. apply NM. right. exact He'.
Qed.
(* no entry of fd: no request *)
Lemma rr_tr_none : forall c mx no cap FD es h, (forall e, In e es -> re_fd e <> FD) ->
  tr_cost MT (rr_tr c mx no cap FD es h) = 0.
Proof.
intros c mx no cap FD es h NM. unfold rr_tr, relay_remove_b_c.relay_remove_tr.
destruct (FD <? 0); [reflexivity|]. rewrite (rr_find_none es FD NM). reflexivity.
Qed.

(* rr_found survives the tail: its predicates sit on kept bytes and on blocks the release keeps *)
Lemma rr_found_kept : forall ly S W mem ly1 S1 W1 m1 S' m' G0 es i j h c O mx cap out,
  rg_place B RG ->
  (forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W1 m' a) ->
  ablocks B ly1 S' = ablocks B ly1 S1 ->
  (re_eof (nth i es relay_remove_b_c.no_entry) = 0 -> (j < 4)%nat) ->
  rr_found B RG ly S W mem ly1 S1 W1 m1 G0 es i j h c O mx cap out ->
  rr_found B RG ly S W mem ly1 S' W1 m' G0 es i j h c O mx cap out.
Proof.
intros ly S W mem ly1 S1 W1 m1 S' m' G0 es i j h c O mx cap out RGP KEEP EBL HJ4 HF.
assert (AK : forall fp, rfz ly1 S1 fp -> akept W1 m1 W1 m' fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (BLK : forall b, In b (ablocks B ly1 S1) -> In b (ablocks B ly1 S')) by (intros b Hb; rewrite EBL; exact Hb).
assert (CKZ : forall a, rr_cells a -> rkz ly1 S1 a) by (intros a Ha; exact (rrt_cell_kz ly1 S1 a RGP Ha)).
assert (OUTC : rfz ly1 S1 (aout_fp B RG 0 0)).
{ intros r Hr a Ha. apply CKZ. unfold aout_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
  [cbn [fst snd] in Ha; unfold rr_cells; tauto .. | simpl in Hr; destruct Hr]. }
unfold rr_found in HF |- *. cbv zeta in HF |- *.
destruct HF as (e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & rest & HSRC & HSL & HREL & HOUT & HPa & HPb).
exists e1, h1, ev, LB, c2, O2, cap2, out2, rest.
split.
{ destruct (re_eof (nth i es relay_remove_b_c.no_entry) =? 0) eqn:Eo; [|exact HSRC].
  destruct HSRC as (HDR & HAS). split; [exact HDR|].
  apply Z.eqb_eq in Eo. pose proof (HJ4 Eo) as Hj4.
  assert (HHA : forall a, rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC -> rkz ly1 S1 a).
  { intros a Ha. apply CKZ. unfold rr_cells. left. unfold ASRC in *. lia. }
  destruct (rfz_asrc ly1 S1 W1 m1 _ h1 HAS HHA) as [F1 F2].
  exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S' W1 m' _ h1 HAS (AK _ F1) (fun b Hb => BLK b (F2 b Hb))). }
split; [exact HSL|].
split.
{ assert (HC : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
                          rg_capsrc RG <= a < rg_capsrc RG + 4 -> rkz ly1 S1 a)
    by (intros a Ha; apply CKZ; unfold rr_cells; tauto).
  destruct (rfz_arelay ly1 S1 W1 m1 G0 _ HREL HC) as [R1 R2].
  exact (arelay_at_kept B RG ly1 S1 W1 m1 ly1 S' W1 m' _ _ HREL (AK _ R1) (fun b Hb => BLK b (R2 b Hb))). }
split.
{ destruct (rfz_aout ly1 S1 W1 m1 _ _ _ _ _ _ HOUT OUTC) as [O1' O2'].
  exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S' W1 m' _ _ _ _ _ _ HOUT (AK _ O1') (fun b Hb => BLK b (O2' b Hb))). }
split; [exact HPa|].
rewrite EBL. exact HPb.
Qed.

Lemma rr_tail_post : forall cx oi W1 ly1 S1 Hp1 m1 md1 k1 F FL fpos regs' m' md' k',
RBASE B ARx MT RP MMAX RG cx -> 0 <= rxFD cx ->
match oi with
| None => RHELD B PST ARx MT RP RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE B PST ARx MT RP RG cx i F FL ly1 S1 Hp1 W1 m1 md1 k1
end ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rr_frame cx fpos F FL ly1 W1 m1 ->
rr_tail_out cx fpos F FL ly1 S1 Hp1 W1 m1 regs' m' md' k' ->
rPOST B PST ARx MT RP RG cx W1 (mkCfg (mkst regs' (getr (rxregs cx) 1) m' (seg_rom SEGS)) md').
Proof.
intros cx oi W1 ly1 S1 Hp1 m1 md1 k1 F FL fpos regs' m' md' k' HB HFD HOI HJ HFR HOUT.
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & _ & HSRC0 & HPERM0 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
destruct HFR as (EF & EFL & _ & _).
destruct HOUT as (J' & HRGS & V & P & L).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
assert (HIN : In (0, fpos) (frames S1)).
{ pose proof HJ as (_ & _ & (memS & HJd & _) & _). pose proof HJd as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity. }
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK).
{ assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
  assert (WE : ESTACK = 4096) by reflexivity.
  revert Hceil Hslo WS WF WE. clear. unfold rsp0. intros. lia. }
assert (HLI : forall a, rg_lock RG + 4 <= a < rg_lock RG + 8 -> in_img SEGS a).
{ intros a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). apply (RGIMG a). unfold rg_rng. left. lia. }
assert (KEEP : forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W1 m' a)
  by (intros a Ha; exact (rrt_kept ly1 S1 Hp1 W1 m1 md1 m' fpos F FL (rsp0 cx) a HAR HIN EF EFL HSC V P HLI Ha)).
assert (AK : forall fp, rfz ly1 S1 fp -> akept W1 m1 W1 m' fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (EBL : ablocks B ly1 (stack_free_state 0 fpos S1) = ablocks B ly1 S1)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (BLK : forall b, In b (ablocks B ly1 S1) -> In b (ablocks B ly1 (stack_free_state 0 fpos S1)))
  by (intros b Hb; rewrite EBL; exact Hb).
assert (CKZ : forall a, rr_cells a -> rkz ly1 S1 a) by (intros a Ha; exact (rrt_cell_kz ly1 S1 a RGP Ha)).
assert (HLV : apres_kept B (rxW cx) (rxmem cx) W1 m1 /\ alock_at RG W1 m1 true /\ awake_at RG W1 m1).
{ destruct oi as [i|].
  - destruct HOI as ((fpos' & _ & _ & HPK & _ & HLK1 & HWK1) & _). exact (conj HPK (conj HLK1 HWK1)).
  - destruct HOI as (((fpos' & _ & _ & HPK & _ & HLK1 & HWK1) & _) & _). exact (conj HPK (conj HLK1 HWK1)). }
destruct HLV as (HPK & HLK1 & HWK1).
unfold rPOST, rr_post_x. cbv beta.
exists ly1, (stack_free_state 0 fpos S1), Hp1, regs', m', md', k'.
split; [reflexivity|].
split; [exact J'|].
split; [exact HRGS|].
split; [intros a H1 H2 H3 H4; apply P; exact (HPK a H1 H2 H3 H4)|].
(* the meter: MO_FR for the release, a set_fs of S1 (YG01.v stack_free_state) *)
split.
{ destruct oi as [i|].
  - destruct HOI as (_ & _ & _ & HMO1 & _).
    apply (mle_weaken MT (rxS cx) _ (tr_cost MT (rtr cx) + 0)); [exact MLAW | | unfold rtr; lia].
    apply (mle_station MT _ S1 _ _ _ MLAW HMO1).
    exact (MO_FR S1 (mkFS (fs_hint (st_fs S1)) (del_pos (fs_live (st_fs S1)) 0 fpos))).
  - destruct HOI as ((_ & _ & _ & _ & _ & _ & HMO1 & _) & NM).
    apply (mle_weaken MT (rxS cx) _ (0 + 0)); [exact MLAW | | rewrite (rr_tr_none _ _ _ _ _ _ _ NM); lia].
    apply (mle_station MT _ S1 _ _ _ MLAW HMO1).
    exact (MO_FR S1 (mkFS (fs_hint (st_fs S1)) (del_pos (fs_live (st_fs S1)) 0 fpos))). }
(* the room: RRU (Some i)'s RDONE carries kr, RRU None's RHELD the whole budget (RMM_of down to kr); the unlock kept
   S1 and the release is a stack_free_state step *)
split.
{ apply RPF_stack_free. destruct oi as [i|].
  - destruct HOI as (_ & _ & _ & _ & _ & _ & HRM1). exact HRM1.
  - destruct HOI as ((_ & _ & _ & _ & _ & _ & _ & _ & HRM1 & _) & _).
    eapply RMM_of; [|exact HRM1]. lia. }
(* g_lock free: its type and waiters words kept, the lock word 0 *)
split.
{ destruct HLK1 as (LK0 & LK4 & LK8 & LKW).
  assert (KL : forall x, rg_lock RG <= x < rg_lock RG + 4 \/ rg_lock RG + 8 <= x < rg_lock RG + 12 ->
    abyte_kept W1 m1 W1 m' x).
  { intros x Hx. apply KEEP. left. split; [|lia]. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
    apply (RGIMG x). unfold rg_rng. left. lia. }
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KL; cbn in Hx; lia | exact LK0]|].
  split; [exact L|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KL; cbn in Hx; lia | exact LK8]|].
  intros i Hi. unfold arm in *. exact (writable_kept (w_H W1) m1 m' _ (P _) (LKW i Hi)). }
(* g_wake[1] *)
split.
{ eapply awake_at_kept; [exact HWK1|]. apply AK. apply rfz_cons; [|apply rfz_nil]. cbn [fst snd].
  intros a Ha. apply CKZ. unfold rr_cells. tauto. }
(* g_s *)
split.
{ intros a Ha Hj.
  assert (K2 : abyte_kept W1 m1 W1 m' a) by (apply KEEP; apply CKZ; unfold rr_cells; left; exact Ha).
  assert (K1 : abyte_kept (rxW cx) (rxmem cx) W1 m1 a).
  { destruct oi as [i|].
    - destruct HOI as (_ & _ & _ & _ & HGS1 & _). exact (HGS1 a Ha Hj).
    - destruct HOI as ((_ & _ & _ & _ & HGS1 & _) & _). exact (HGS1 a Ha). }
  exact (abyte_kept_trans _ _ _ _ _ _ a K1 K2). }
(* no entry of fd *)
split.
{ intros HNM. destruct oi as [i|].
  - exfalso. destruct HOI as (_ & Hi & Hfd & _).
    destruct HNM as [Hlt | HNM]; [lia|].
    apply (HNM (rnth cx i)); [unfold rnth; apply nth_In; exact Hi | exact Hfd].
  - destruct HOI as ((_ & HREL1 & HOUT1 & HPERM1 & _) & _).
    assert (OUTC : rfz ly1 S1 (aout_fp B RG 0 0)).
    { intros r Hr a Ha. apply CKZ. unfold aout_fp in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
      [cbn [fst snd] in Ha; unfold rr_cells; tauto .. | simpl in Hr; destruct Hr]. }
    assert (HC : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
                            rg_capsrc RG <= a < rg_capsrc RG + 4 -> rkz ly1 S1 a)
      by (intros a Ha; apply CKZ; unfold rr_cells; tauto).
    split; [|split].
    + destruct (rfz_arelay ly1 S1 W1 m1 (rxG0 cx) (rxes cx) HREL1 HC) as [R1 R2].
      exact (arelay_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 m' _ _ HREL1 (AK _ R1) (fun b Hb => BLK b (R2 b Hb))).
    + destruct (rfz_aout ly1 S1 W1 m1 _ _ _ _ _ _ HOUT1 OUTC) as [O1 O2].
      exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 m' _ _ _ _ _ _ HOUT1 (AK _ O1) (fun b Hb => BLK b (O2 b Hb))).
    + rewrite EBL. eapply Permutation_trans; [exact HPERM1 | apply Permutation_sym; exact HPERM0]. }
(* the entry of fd: entry i (NoDup of the fds) *)
intros i' Hi' _ Hfd'. destruct oi as [i|].
- destruct HOI as (_ & Hi & Hfd & _ & _ & HFND & _).
  assert (Ei : i' = i).
  { destruct HREL0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HND & _)).
    apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HND.
    apply (proj1 (@NoDup_nth _ (map re_fd (rxes cx)) (re_fd relay_remove_b_c.no_entry)) HND);
      [rewrite length_map; exact Hi' | rewrite length_map; exact Hi|].
    rewrite !map_nth. unfold rnth in Hfd. rewrite Hfd, Hfd'. reflexivity. }
  subst i'.
  assert (HJ4 : re_eof (nth i (rxes cx) relay_remove_b_c.no_entry) = 0 -> (rxj cx < 4)%nat)
    by (intros He; exact (proj1 (HSRC0 i Hi Hfd He))).
  exact (rr_found_kept (rxly cx) (rxS cx) (rxW cx) (rxmem cx) ly1 S1 W1 m1 (stack_free_state 0 fpos S1) m'
    (rxG0 cx) (rxes cx) i (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) RGP KEEP EBL HJ4 HFND).
- exfalso. destruct HOI as (_ & NM). exact (NM _ (nth_In _ _ Hi') Hfd').
Qed.

(* ---- The walk's runners (W_relay_remove.v's Lets), their _x twins. ---- *)
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let RUNC := SRr_run_pi_AJ_call_x (PL := PL_fr) B PST ARx LAWS.
Let RUNF := aj_flag_store_pi_x (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE.
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- The seat at 0x83fc4 (W7's W_drain_epi.v dr_epi_entry form).
   Atoms: the registers 0 .. 31 of the cut (s0 = the entry sp: atom 8; s4 = F: atom 20; s5 = F's shadow:
   atom 21), then the eleven saved registers of the entry (32 .. 42, in RR_SAVED order) and the flag cell FL (43).
   s2 is seated as atom 20 (it holds F too), so the release's `ld a0, 56(s2)` finds F's region.
   Regions: the frame's saved slots, read through s0 by the epilogue (sp = s0 - 96 there), and g_wake[1]
   (A_OBJ 4), read-only.  F, its shadow and FL are seated after the unlock (they are written only after it). ---- *)
Definition rrt_stack : YP09.region :=
YP09.mkRegion (Some 8%nat) (-88) 0 (-88) (-88)
  (map (fun i => YP09.mkChunk (-88 + 8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 11)).
Definition rrt_wake : YP09.region := YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 4294967295))].
Definition rrt_regions0 : smem := [rrt_stack; rrt_wake].
Definition rrt_facts0 : facts := mkFacts [(20%nat, HPTR 5)] [] [].
Definition rrt_sr : list sv := sr_set sr_atoms 18%bv (SOff 20 0).
Definition rrt_ss0 : sstate := mkSS A_rr_unlock rrt_sr rrt_regions0 None rrt_facts0.
Definition rrt_extra (regsE : bvmap 5 word) (FL : Z) : list word := map (getr regsE) RR_SAVED ++ [Z_to_bv 64 FL].
Lemma nth_rrt_extra : forall regsE FL i, (i < 11)%nat ->
  nth i (rrt_extra regsE FL) (Z_to_bv 64 0) = getr regsE (nth i RR_SAVED 0%bv).
Proof.
intros regsE FL i Hi. unfold rrt_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
Lemma nth_rrt_extra_fl : forall regsE FL, nth 11 (rrt_extra regsE FL) (Z_to_bv 64 0) = Z_to_bv 64 FL.
Proof. intros regsE FL. reflexivity. Qed.
Lemma regs_ok_same : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr He r'. pose proof (Hr r') as Hr'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [exact Hr'|].
unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr'|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr'].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact He.
Qed.
Lemma rrt_entry : forall (W : world SEGS) regs1 m1 regsE sp0 F FL,
  getr regs1 8 = w64 sp0 -> getr regs1 18 = w64 F -> getr regs1 20 = w64 F ->
  alloc_ceiling + 88 <= sp0 <= 2 ^ 47 ->
  4096 <= F <= 140737479966720 -> F mod 32 = 0 ->
  (forall i, (i < 11)%nat ->
   val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 88 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regsE (nth i RR_SAVED 0%bv)))) ->
  val_mem SEGS (mrestrict (w_H W) m1) (VAL (A_OBJ 4)) 4 4294967295 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rrt_extra regsE FL))) rrt_ss0
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_unlock)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 regsE sp0 F FL R8 R18 R20 Hsp HF HF32 HSV HWK.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img 4 ltac:(lia)) as HO4. pose proof (pa_val_range (A_OBJ 4)) as HV4r.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (rrt_extra regsE FL))).
assert (E8 : ew E 8 = getr regs1 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 8 8%bv eq_refl)).
assert (E20 : ew E 20 = getr regs1 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 20 20%bv eq_refl)).
assert (E245 : ew E (A_OBJ 4) = Z_to_bv 64 (VAL (A_OBJ 4))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U8 : base_val E (Some 8%nat) = sp0) by (cbn [base_val]; rewrite E8, R8; apply unsigned_lit_small; lia).
assert (U245 : base_val E (Some (A_OBJ 4)) = VAL (A_OBJ 4)) by (cbn [base_val]; rewrite E245; apply unsigned_lit_small; lia).
unfold rrt_ss0, A_rr_unlock. apply pa_entry_st_ok_full.
- unfold rrt_sr. apply regs_ok_same; [apply regs_ok_Eimg_Ereg|].
  cbn [sv_denot]. rewrite E20, R20, R18, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- vm_compute. reflexivity.
- unfold rrt_regions0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, rrt_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
    apply (chunk_ok_val SEGS E _ sp0 (-88 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i RR_SAVED 0%bv)))).
    * cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite ew_Ereg_extra, nth_rrt_extra by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (getr regsE (nth i RR_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
    * zside.
    * replace (sp0 + (-88 + 8 * Z.of_nat i)) with (sp0 - 88 + 8 * Z.of_nat i) by lia. exact (HSV i ltac:(lia)).
  + unfold region_ok, rrt_wake. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U245. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 4)) 0 4 (SLit 4294967295) 4294967295); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact HWK.
- apply pairwise_disjoint_of_extents. unfold rrt_regions0, rrt_stack, rrt_wake, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U8, U245.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hsp HO4 C1. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rrt_facts0 f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite E20, R20, unsigned_lit_small by lia. change (2 ^ 5) with 32.
  revert HF HF32. clear. intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* g_lock's 12 bytes and g_wake[1]'s 4 are apart (HRGP's pair 0 / 13). *)
Lemma rrt_lock_wake : rg_lock RG + 12 <= rg_wake RG + 4 \/ rg_wake RG + 8 <= rg_lock RG.
Proof.
pose proof HRGP as H. cbn [zpairwise_disjoint zall_disjoint] in H. unfold zdisj in H. cbn [fst snd] in H.
destruct H as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H.
Qed.

Lemma rr_tail_walk : forall cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 F FL fpos,
RBASE B ARx MT RP MMAX RG cx ->
rregs_base cx regs1 F ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rr_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1)
  (fun W' c' => W' = W1 /\ exists regs' m' md' k',
     c' = mkCfg (mkst regs' (getr (rxregs cx) 1) m' (seg_rom SEGS)) md' /\
     rr_tail_out cx fpos F FL ly1 S1 Hp1 W1 m1 regs' m' md' k').
Proof.
intros cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 F FL fpos HB HRB HJ HFR HLK HWK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK0 & HWAKE0 & HREL & HOUT & HROM & HSRC & HPERM & HTRM & HLIVE & HMOK).
destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HRB as (Hsp1 & Hgp1 & Htp1 & Hs0 & Hs1 & Hs2 & Hs4 & Hs5 & Hs6 & Hs10 & Hs11).
destruct HFR as (EF & EFL & HFL56 & HSV).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres.
(* the donor journal under RLIVE's, and the frame (0, fpos) it owns *)
pose proof HJ as (_ & _ & (memS & HJd & Hag) & _). rewrite !Z.add_0_r in HJd.
pose proof (proj1 HJd) as HAR1.
assert (Hfin : In (0, fpos) (frames S1)).
{ pose proof HJd as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
change (fs_frame_bytes 0) with 64 in HF4096, HFceil, HFhigh, HFapp, HFpres, HFSpres.
change (64 / 8) with 8 in HFSpres. rewrite EF in HF4096, HFceil, HFhigh, HFal, HFapp, HFpres, HFSpres.
unfold arm in HFL56, HLK, HWK.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rrt_extra (rxregs cx) FL))) rrt_ss0
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_unlock)) m1 (seg_rom SEGS)))).
{ apply (rrt_entry W1 regs1 m1 (rxregs cx) (rsp0 cx) F FL Hs0 Hs2 Hs4).
  - rewrite WS in Hslo. lia.
  - lia.
  - exact HFal.
  - intros i Hi. replace (rsp0 cx - 88 + 8 * Z.of_nat i) with (rsp0 cx - RR_FRAME + 8 + 8 * Z.of_nat i) by (rewrite WF; lia).
    exact (HSV i Hi).
  - rewrite HV4. exact HWK. }
remember (Eimg (Ereg regs1 (rrt_extra (rxregs cx) FL))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 11)%nat -> ew E (32 + i) = getr (rxregs cx) (nth i RR_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_rrt_extra (rxregs cx) FL i Hi). }
assert (E43 : ew E 43 = Z_to_bv 64 FL).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 11). }
clear HE.
unfold cfg_at. change (w64 (BASE + A_rr_unlock)) with (Z_to_bv 64 (BASE + A_rr_unlock)).
(* 0x83fc4 .. 0x83fd0: s3 = F + 32, a0 = &g_lock, the call to pthread_mutex_unlock *)
paj_run_shc_x RUNP RUNC HS HJd.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
(* the run wrote nothing (both regions are read-only): every byte keeps its view *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha). intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
pose proof (pa_obj_img 6 ltac:(lia)) as HL6. rewrite <- RGLOCK in HL6.
assert (HLA : rg_lock RG mod 4 = 0).
{ destruct (Z.mod_divide (rg_lock RG) 8 ltac:(lia)) as [Hd _]. destruct (Hd RGAL8) as [q Hq]. rewrite Hq.
  replace (q * 8) with ((q * 2) * 4) by lia. apply Z_mod_mult. }
pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8. unfold awr, arm in LKW.
assert (LKM : forall a n v, rg_lock RG <= a -> a + Z.of_nat n <= rg_lock RG + 12 ->
  val_mem SEGS (mrestrict (w_H W1) m1) a n v -> val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) a n v).
{ intros a n v Ha Hn Hv. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms) a n v); [|exact Hv].
  intros j Hj. apply KEEP1. lia. }
pose proof (LKM (rg_lock RG) 4%nat 0 ltac:(lia) ltac:(cbn; lia) LK0) as MK0.
pose proof (LKM (rg_lock RG + 4) 4%nat _ ltac:(lia) ltac:(cbn; lia) LK4) as MK4.
pose proof (LKM (rg_lock RG + 8) 4%nat 0 ltac:(lia) ltac:(cbn; lia) LK8) as MK8.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W1) (ms_mem ms) a <> None).
{ intros a Ha. rewrite (KEEP1 a ltac:(lia)). unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKI : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; apply RGIMG; unfold rg_rng; left; exact Ha).
assert (HJg : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 (ms_mem ms)
  (with_vm_backing (m_vm_lazy md1) mat md1) k1)
by (apply (ajournal_gx_pack_x SEGS B PST ARx _ 0 [] RR_STK_x (rsp0 cx) (rFP cx) _ _ _ _ _ _ _ ly1 S1 Hp1 W1 _ _ k1 memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJd | exact Hag | intros a Ha; lia]).
pose proof (proj1 HJd) as HARm.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
assert (HSPc : spZ (ms_regs ms) = rsp0 cx + -96).
{ unfold spZ at 1. rewrite QSP, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). rewrite Hsp1, WF. lia. }
assert (QA0' : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 247%nat with (A_OBJ 6). rewrite (img_env_atomP E (A_OBJ 6) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite RGLOCK. reflexivity. }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RR B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
       getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W1) mem') (rg_lock RG + 4) 4 0)
    W1 _ _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) _ _ _ _ _ _ (-96) _ HG
    eq_refl HJg).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl), Hgp1. exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl), Htp1. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
    + exact QA0'.
    + lia.
    + exact HLA.
    + lia.
    + exact MK0.
    + exact MK4.
    + exact MK8.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. revert Ha HL6 Hslo Hceil C1 WS Hes. clear. intros. lia.
    + intros a Ha. split; [|split].
      * apply (writable_kept _ m1 (ms_mem ms) a); [intros Hp; exact (apresent_grows _ _ _ a HG0 Hp)|].
        replace a with (rg_lock RG + (a - rg_lock RG)) by lia. apply LKW. lia.
      * intros Ho. destruct (LKI a ltac:(lia)) as (Hi & Hno & _).
        exact (Hno (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Ho)).
      * rewrite HSPc. revert Ha HL6 Hslo Hceil C1 WS Hes. clear. intros. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HK))). unfold G_RR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPR3 & Hfr3 & Hpres3).
(* ---- back at 0x83fd4: s-registers kept, the caller-saved ones fresh atoms 48 .. 63 ---- *)
assert (U8 : bv_unsigned (ew E 8) = rsp0 cx) by (rewrite (EE 8%nat 8%bv eq_refl), Hs0; apply unsigned_lit_small; lia).
assert (U245 : bv_unsigned (ew E (A_OBJ 4)) = VAL (A_OBJ 4)) by exact (HEI (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
pose proof (pa_obj_img 4 ltac:(lia)) as HO4.
pose proof rrt_lock_wake as HLW.
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (region_kept_aview E (w_H W1) (ms_mem ms) mem3 8 (rsp0 cx)); [exact U8 | | exact Hpres3].
    intros a Ha. apply Hfr3;
    [ revert Ha Hslo Hshi H47 Hceil C1 WS; clear; intros; lia
    | revert Ha HL6 Hslo Hceil C1 WS; clear; intros; lia
    | revert Ha Hes; clear; intros; lia ].
  - apply (region_kept_aview E (w_H W1) (ms_mem ms) mem3 (A_OBJ 4) (VAL (A_OBJ 4))); [exact U245 | | exact Hpres3].
    intros a Ha. apply Hfr3;
    [ revert Ha HO4; clear; intros; lia
    | revert Ha HLW HV4; clear; intros; lia
    | revert Ha HO4 Hslo Hceil C1 WS Hes; clear; intros; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
(* the state at the unlock's return: ARx there (S1, Hp1 kept), the frame (0, fpos) and its flag cell *)
pose proof HJ3 as HAR3. apply (ajournal_gx_AR_x SEGS B PST ARx) in HAR3.
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HAR3 Hfin) as (_ & _ & HFpres3 & HFSpres3).
destruct (FFL _ _ _ _ _ _ 0 fpos HAR3 Hfin) as (HFLp3 & HFLo3 & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HAR3 Hfin) as HFimg.
change (fs_frame_bytes 0) with 64 in HFpres3, HFSpres3, HFimg. change (64 / 8) with 8 in HFSpres3.
rewrite EF in HFpres3, HFSpres3, HFimg. rewrite EFL in HFLp3, HFLo3, HFLapp, HFLimg, HFL4096, HFLz, HFLc.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (U20a : bv_unsigned (ew Ea 20) = F) by (rewrite OLDa, (EE 20%nat 20%bv eq_refl), Hs4 by lia; apply unsigned_lit_small; lia).
assert (U21a : bv_unsigned (ew Ea 21) = shadow_addr F)
by (rewrite OLDa, (EE 21%nat 21%bv eq_refl), Hs5 by lia; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U43a : bv_unsigned (ew Ea 43) = FL) by (rewrite OLDa, E43 by lia; apply unsigned_lit_small; lia).
assert (U8a : bv_unsigned (ew Ea 8) = rsp0 cx) by (rewrite OLDa by lia; exact U8).
assert (U245a : bv_unsigned (ew Ea 245%nat) = VAL (A_OBJ 4)) by exact (HEIa (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
(* F + 56 holds FL at the unlock's return: kept by the run (nothing written) and by the call (F is no lock byte
   and lies below the stack) *)
assert (KF : forall a, F <= a < F + 64 -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. rewrite (Hfr3 a ltac:(lia) ltac:(revert Ha HL6 HFimg; clear; unfold off_img; intros; lia)
    ltac:(revert Ha HFceil Hslo Hceil C1 WS Hes; clear; intros; lia)). apply KEEP1. lia. }
assert (HFL56' : val_mem SEGS (mrestrict (w_H W1) mem3) (F + (64 - 8)) 8 FL).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 mem3 (F + (64 - 8)) 8 FL); [|replace (F + (64 - 8)) with (F + 56) by lia; exact HFL56].
  intros j Hj. apply KF. cbn in Hj. lia. }
(* seat F (atom 20), its shadow (atom 21) and the flag cell (atom 43) *)
pose proof (st_ok_pi_add_region Ea _ _ (fframe_region 20 43 0 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0) with 64; rewrite U20a; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ea _ F (64 - 8) 8 _ FL);
  [cbn [sv_denot]; rewrite OLDa, E43, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity | zside | zside | exact HFL56'] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite U20a, U8a, U245a;
revert HFceil HFimg Hslo Hceil C1 WS HO4; clear; unfold off_img; intros; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (fshadow_region 21 0 0 8 []) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
change (fs_frame_bytes 0 / 8) with 8; rewrite U21a; split; [unfold shadow_addr, SHADOW_OFF; lia|]; split; [unfold shadow_addr, SHADOW_OFF; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFSpres3 o ltac:(lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite U21a, U20a, U8a, U245a;
revert HFceil HFimg HFapp HF4096 HFq HF8 Hslo Hceil C1 C3 WS HO4; clear;
unfold shadow_addr, SHADOW_OFF, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 43%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U43a; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp3)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U43a, U21a, U20a, U8a, U245a;
repeat split;
lazymatch goal with
| |- ?fl + 1 <= F + ?l \/ F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFpres3 FL ltac:(lia)) HFLo3)
| |- ?fl + 1 <= shadow_addr F + ?l \/ shadow_addr F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (shadow_addr F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (shadow_addr F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFSpres3 (FL - shadow_addr F) ltac:(lia)) ltac:(replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia; exact HFLo3))
| |- ?g => revert HFLc HFLz Hslo Hceil C1 WS HO4; clear; unfold zone2, off_img; intros; lia
end)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* ---- 0x83fd4 .. 0x84094: the wake byte, the wake test (g_wake[1] = -1: not taken), the release (retired magic,
   shadow 0xf5, *flag = 0) and the epilogue, one plain run ending at the ret ---- *)
pose proof HJ3 as (_ & _ & (memS3 & HJd3 & Hag3) & _). rewrite !Z.add_0_r in HJd3.
paj_run_flag_sh_x RUNF HS HJd3.
{ lia. }
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8a, ?U20a, ?U21a, ?U43a, ?U245a in Hr;
    first [ lia
    | right; rewrite EFL; lia
    | left; right; right; right; exists 0, fpos; split; [left; reflexivity|]; rewrite EF; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
{ intros msr HSr. rewrite EFL.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U43a
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
(* ---- the return ---- *)
prreg HS (1%bv : bv 5) Rr1. prreg HS (2%bv : bv 5) Rr2. prreg HS (3%bv : bv 5) Rr3. prreg HS (4%bv : bv 5) Rr4.
prreg HS (8%bv : bv 5) Rr8. prreg HS (9%bv : bv 5) Rr9. prreg HS (18%bv : bv 5) Rr18. prreg HS (19%bv : bv 5) Rr19.
prreg HS (20%bv : bv 5) Rr20. prreg HS (21%bv : bv 5) Rr21. prreg HS (22%bv : bv 5) Rr22. prreg HS (23%bv : bv 5) Rr23.
prreg HS (24%bv : bv 5) Rr24. prreg HS (25%bv : bv 5) Rr25. prreg HS (26%bv : bv 5) Rr26. prreg HS (27%bv : bv 5) Rr27.
assert (EXa : forall i, (i < 11)%nat -> ew Ea (32 + i) = getr (rxregs cx) (nth i RR_SAVED 0%bv))
by (intros i Hi; rewrite OLDa by lia; exact (EX i Hi)).
assert (RA : getr (ms_regs ms0) 1 = getr (rxregs cx) 1) by (rewrite Rr1; exact (EXa 10%nat ltac:(lia))).
(* what the second run kept: everything outside F, its shadow and FL *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 64) -> ~ (shadow_addr F <= a < shadow_addr F + 8) -> a <> FL ->
  aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem3 a).
{ intros a Ha H1 H2 H3. apply (aview_kept_out Ea _ (w_H W1) mem3 (ms_mem ms0) HFr0 a Ha). intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U8a, ?U20a, ?U21a, ?U43a, ?U245a in Hr; lia | ]).
  destruct Hin. }
eapply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
exists (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat0 md3)) mat'
  (with_vm_backing (m_vm_lazy md3) mat0 md3)), k1.
split; [rewrite RA, Hra; reflexivity|].
split.
{ apply (ajournal_gx_pack_x SEGS B PST ARx _ 0 [] RR_STK_x (rsp0 cx) (rFP cx) _ _ _ _ _ _ _ ly1 _ _ W1 _ _ k1 memS3);
  [lia | lia | | exact Hag3 | intros a Ha; lia].
  rewrite !Z.add_0_r. apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs). exact HJd3. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr2, OLDa, (EE 8%nat 8%bv eq_refl), Hs0 by lia. unfold rsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr3, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp1.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr4, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp1.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr8. exact (EXa 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr9. exact (EXa 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr18. exact (EXa 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr19. exact (EXa 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr20. exact (EXa 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr21. exact (EXa 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr22. exact (EXa 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr23. exact (EXa 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr24. exact (EXa 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr25. exact (EXa 0%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr26, OLDa, (EE 26%nat 26%bv eq_refl) by lia. exact Hs10.
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr27, OLDa, (EE 27%nat 27%bv eq_refl) by lia. exact Hs11. }
split.
{ intros a Ha Hl HFa HSa HFLa Hsc. rewrite (KEEP3 a Ha HFa HSa HFLa).
  rewrite (Hfr3 a Ha Hl ltac:(rewrite WF in Hsc; lia)). exact (KEEP1 a Ha). }
split.
{ intros a Hp. apply (apresent_grows _ _ _ a HG1). apply Hpres3. exact (apresent_grows _ _ _ a HG0 Hp). }
destruct HPR3 as (_ & HL40). unfold arm.
apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem3 (ms_mem ms0) (rg_lock RG + 4) 4 0); [|exact HL40].
intros j Hj. cbn in Hj. apply KEEP3;
[ lia
| revert Hj HL6 HFimg; clear; unfold off_img; intros; lia
| revert Hj HL6 HF4096; clear; unfold shadow_addr, SHADOW_OFF; intros; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia
| intros He; revert He Hj HL6 HFLz; clear; unfold zone2, off_img; intros; lia ].
Qed.

Theorem rr_tail : rr_tail_stmt B PST ARx MT RP MMAX RG.
Proof.
unfold rr_tail_stmt. intros cx oi W1 c1 HB HU.
destruct HU as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & -> & HRB & HFD0 & HOI).
assert (HLV : RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1)
by (destruct oi as [i|]; [exact (proj1 HOI) | exact (proj1 (proj1 HOI))]).
destruct HLV as (fpos & HJ & HROM & HPK & HFR & HLK & HWK).
eapply SRr_mono; [exact (rr_tail_walk cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 F FL fpos HB HRB HJ HFR HLK HWK)|].
cbv beta. intros W2 c2 _ (-> & regs' & m' & md' & k' & -> & HOUT).
exact (rr_tail_post cx oi W1 ly1 S1 Hp1 m1 md1 k1 F FL fpos regs' m' md' k' HB HFD0 HOI HJ HFR HOUT).
Qed.

(* ---- ROUTE R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the TAIL at a world relation R, W_relay_remove_cx.v's Section wR texts
   (rr_tail_stmt_xR; RRU_xR, RHELD_xR, RDONE_xR, RLIVE_xR; the post rPOST_xR = W_contract_xR_relay.rr_post_xR).
   Names X -> X_xR; the strict text above is kept.  Against the strict proofs only the engine changes: the journal
   ajournal_gx_x -> ajournal_gx_xR R (its pack / AR / materialize at R), the step relation SRr SEGS -> SRrG SEGS R
   (SRrG_bind reads R_trans), the runs their G twins (W_frame_x.v SRrG_run_pi_AJ_xG, SRrG_run_pi_AJ_call_xG,
   aj_flag_store_pi_xG), the unlock aj_gx_entry_at_xR (W_sites_x.v; R_trans, WLE_R) and the ret a strict step lifted
   by SRr_SRrG (WLE_R).  The unlock returns at W1, so the walk's post keeps W' = W1.  The journal-free helpers above
   (rkz, rfz_*, rrt_kept, rr_found_kept, rrt_entry, ...) are reused. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the walk's runners at R: the Lets RUNP / RUNC / RUNF above, their G twins (W_frame_x.v; they conclude SRrG SEGS R
   over the journal at R and take the strict runs' binders, so paj_run_shc_x / paj_run_flag_sh_x drive them) *)
Let RUNPR := SRrG_run_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNCR := SRrG_run_pi_AJ_call_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNFR := aj_flag_store_pi_xG (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE (R := R).
(* rr_tail_out at R: the journal ajournal_gx_xR R *)
Definition rr_tail_out_xR (cx : rcx) (fpos F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (regs' : bvmap 5 word) (m' : word -> option byte) (md' : Model) (k' : Z) : Prop :=
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 (stack_free_state 0 fpos S1) Hp1 W1 m' md' k' /\
aregs_preserved (rxregs cx) regs' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> ~ (F <= a < F + 64) ->
   ~ (shadow_addr F <= a < shadow_addr F + 8) -> a <> FL ->
   ~ (rsp0 cx - RR_FRAME - ESTACK <= a < rsp0 cx - RR_FRAME) ->
   aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m1 a) /\
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m' a) /\
val_mem SEGS (arm W1 m') (rg_lock RG + 4) 4 0.

(* rr_tail_post at R *)
Lemma rr_tail_post_xR : forall cx oi W1 ly1 S1 Hp1 m1 md1 k1 F FL fpos regs' m' md' k',
RBASE B ARx MT RP MMAX RG cx -> 0 <= rxFD cx ->
match oi with
| None => RHELD_xR B PST ARx MT RP RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE_xR B PST ARx MT RP RG R cx i F FL ly1 S1 Hp1 W1 m1 md1 k1
end ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rr_frame cx fpos F FL ly1 W1 m1 ->
rr_tail_out_xR cx fpos F FL ly1 S1 Hp1 W1 m1 regs' m' md' k' ->
rPOST_xR B PST ARx MT RP RG R cx W1 (mkCfg (mkst regs' (getr (rxregs cx) 1) m' (seg_rom SEGS)) md').
Proof.
intros cx oi W1 ly1 S1 Hp1 m1 md1 k1 F FL fpos regs' m' md' k' HB HFD HOI HJ HFR HOUT.
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & _ & HSRC0 & HPERM0 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
destruct HFR as (EF & EFL & _ & _).
destruct HOUT as (J' & HRGS & V & P & L).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HIN : In (0, fpos) (frames S1)).
{ pose proof HJ as (_ & _ & (memS & HJd & _) & _). pose proof HJd as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity. }
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK).
{ assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
  assert (WE : ESTACK = 4096) by reflexivity.
  revert Hceil Hslo WS WF WE. clear. unfold rsp0. intros. lia. }
assert (HLI : forall a, rg_lock RG + 4 <= a < rg_lock RG + 8 -> in_img SEGS a).
{ intros a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). apply (RGIMG a). unfold rg_rng. left. lia. }
assert (KEEP : forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W1 m' a)
  by (intros a Ha; exact (rrt_kept ly1 S1 Hp1 W1 m1 md1 m' fpos F FL (rsp0 cx) a HAR HIN EF EFL HSC V P HLI Ha)).
assert (AK : forall fp, rfz ly1 S1 fp -> akept W1 m1 W1 m' fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (EBL : ablocks B ly1 (stack_free_state 0 fpos S1) = ablocks B ly1 S1)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (BLK : forall b, In b (ablocks B ly1 S1) -> In b (ablocks B ly1 (stack_free_state 0 fpos S1)))
  by (intros b Hb; rewrite EBL; exact Hb).
assert (CKZ : forall a, rr_cells a -> rkz ly1 S1 a) by (intros a Ha; exact (rrt_cell_kz ly1 S1 a RGP Ha)).
assert (HLV : apres_kept B (rxW cx) (rxmem cx) W1 m1 /\ alock_at RG W1 m1 true /\ awake_at RG W1 m1).
{ destruct oi as [i|].
  - destruct HOI as ((fpos' & _ & _ & HPK & _ & HLK1 & HWK1) & _). exact (conj HPK (conj HLK1 HWK1)).
  - destruct HOI as (((fpos' & _ & _ & HPK & _ & HLK1 & HWK1) & _) & _). exact (conj HPK (conj HLK1 HWK1)). }
destruct HLV as (HPK & HLK1 & HWK1).
unfold rPOST_xR, rr_post_xR. cbv beta.
exists ly1, (stack_free_state 0 fpos S1), Hp1, regs', m', md', k'.
split; [reflexivity|].
split; [exact J'|].
split; [exact HRGS|].
split; [intros a H1 H2 H3 H4; apply P; exact (HPK a H1 H2 H3 H4)|].
(* the meter: MO_FR for the release, a set_fs of S1 (YG01.v stack_free_state) *)
split.
{ destruct oi as [i|].
  - destruct HOI as (_ & _ & _ & HMO1 & _).
    apply (mle_weaken MT (rxS cx) _ (tr_cost MT (rtr cx) + 0)); [exact MLAW | | unfold rtr; lia].
    apply (mle_station MT _ S1 _ _ _ MLAW HMO1).
    exact (MO_FR S1 (mkFS (fs_hint (st_fs S1)) (del_pos (fs_live (st_fs S1)) 0 fpos))).
  - destruct HOI as ((_ & _ & _ & _ & _ & _ & HMO1 & _) & NM).
    apply (mle_weaken MT (rxS cx) _ (0 + 0)); [exact MLAW | | rewrite (rr_tr_none _ _ _ _ _ _ _ NM); lia].
    apply (mle_station MT _ S1 _ _ _ MLAW HMO1).
    exact (MO_FR S1 (mkFS (fs_hint (st_fs S1)) (del_pos (fs_live (st_fs S1)) 0 fpos))). }
(* the room: RRU (Some i)'s RDONE carries kr, RRU None's RHELD the whole budget (RMM_of down to kr); the unlock kept
   S1 and the release is a stack_free_state step *)
split.
{ apply RPF_stack_free. destruct oi as [i|].
  - destruct HOI as (_ & _ & _ & _ & _ & _ & HRM1). exact HRM1.
  - destruct HOI as ((_ & _ & _ & _ & _ & _ & _ & _ & HRM1 & _) & _).
    eapply RMM_of; [|exact HRM1]. lia. }
(* g_lock free: its type and waiters words kept, the lock word 0 *)
split.
{ destruct HLK1 as (LK0 & LK4 & LK8 & LKW).
  assert (KL : forall x, rg_lock RG <= x < rg_lock RG + 4 \/ rg_lock RG + 8 <= x < rg_lock RG + 12 ->
    abyte_kept W1 m1 W1 m' x).
  { intros x Hx. apply KEEP. left. split; [|lia]. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
    apply (RGIMG x). unfold rg_rng. left. lia. }
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KL; cbn in Hx; lia | exact LK0]|].
  split; [exact L|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KL; cbn in Hx; lia | exact LK8]|].
  intros i Hi. unfold arm in *. exact (writable_kept (w_H W1) m1 m' _ (P _) (LKW i Hi)). }
(* g_wake[1] *)
split.
{ eapply awake_at_kept; [exact HWK1|]. apply AK. apply rfz_cons; [|apply rfz_nil]. cbn [fst snd].
  intros a Ha. apply CKZ. unfold rr_cells. tauto. }
(* g_s *)
split.
{ intros a Ha Hj.
  assert (K2 : abyte_kept W1 m1 W1 m' a) by (apply KEEP; apply CKZ; unfold rr_cells; left; exact Ha).
  assert (K1 : abyte_kept (rxW cx) (rxmem cx) W1 m1 a).
  { destruct oi as [i|].
    - destruct HOI as (_ & _ & _ & _ & HGS1 & _). exact (HGS1 a Ha Hj).
    - destruct HOI as ((_ & _ & _ & _ & HGS1 & _) & _). exact (HGS1 a Ha). }
  exact (abyte_kept_trans _ _ _ _ _ _ a K1 K2). }
(* no entry of fd *)
split.
{ intros HNM. destruct oi as [i|].
  - exfalso. destruct HOI as (_ & Hi & Hfd & _).
    destruct HNM as [Hlt | HNM]; [lia|].
    apply (HNM (rnth cx i)); [unfold rnth; apply nth_In; exact Hi | exact Hfd].
  - destruct HOI as ((_ & HREL1 & HOUT1 & HPERM1 & _) & _).
    assert (OUTC : rfz ly1 S1 (aout_fp B RG 0 0)).
    { intros r Hr a Ha. apply CKZ. unfold aout_fp in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
      [cbn [fst snd] in Ha; unfold rr_cells; tauto .. | simpl in Hr; destruct Hr]. }
    assert (HC : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
                            rg_capsrc RG <= a < rg_capsrc RG + 4 -> rkz ly1 S1 a)
      by (intros a Ha; apply CKZ; unfold rr_cells; tauto).
    split; [|split].
    + destruct (rfz_arelay ly1 S1 W1 m1 (rxG0 cx) (rxes cx) HREL1 HC) as [R1 R2].
      exact (arelay_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 m' _ _ HREL1 (AK _ R1) (fun b Hb => BLK b (R2 b Hb))).
    + destruct (rfz_aout ly1 S1 W1 m1 _ _ _ _ _ _ HOUT1 OUTC) as [O1 O2].
      exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 m' _ _ _ _ _ _ HOUT1 (AK _ O1) (fun b Hb => BLK b (O2 b Hb))).
    + rewrite EBL. eapply Permutation_trans; [exact HPERM1 | apply Permutation_sym; exact HPERM0]. }
(* the entry of fd: entry i (NoDup of the fds) *)
intros i' Hi' _ Hfd'. destruct oi as [i|].
- destruct HOI as (_ & Hi & Hfd & _ & _ & HFND & _).
  assert (Ei : i' = i).
  { destruct HREL0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HND & _)).
    apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HND.
    apply (proj1 (@NoDup_nth _ (map re_fd (rxes cx)) (re_fd relay_remove_b_c.no_entry)) HND);
      [rewrite length_map; exact Hi' | rewrite length_map; exact Hi|].
    rewrite !map_nth. unfold rnth in Hfd. rewrite Hfd, Hfd'. reflexivity. }
  subst i'.
  assert (HJ4 : re_eof (nth i (rxes cx) relay_remove_b_c.no_entry) = 0 -> (rxj cx < 4)%nat)
    by (intros He; exact (proj1 (HSRC0 i Hi Hfd He))).
  exact (rr_found_kept (rxly cx) (rxS cx) (rxW cx) (rxmem cx) ly1 S1 W1 m1 (stack_free_state 0 fpos S1) m'
    (rxG0 cx) (rxes cx) i (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) RGP KEEP EBL HJ4 HFND).
- exfalso. destruct HOI as (_ & NM). exact (NM _ (nth_In _ _ Hi') Hfd').
Qed.

(* rr_tail_walk at R *)
Lemma rr_tail_walk_xR : forall cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 F FL fpos,
RBASE B ARx MT RP MMAX RG cx ->
rregs_base cx regs1 F ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
rr_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
SRrG SEGS R W1 (cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1)
  (fun W' c' => W' = W1 /\ exists regs' m' md' k',
     c' = mkCfg (mkst regs' (getr (rxregs cx) 1) m' (seg_rom SEGS)) md' /\
     rr_tail_out_xR cx fpos F FL ly1 S1 Hp1 W1 m1 regs' m' md' k').
Proof.
intros cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 F FL fpos HB HRB HJ HFR HLK HWK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK0 & HWAKE0 & HREL & HOUT & HROM & HSRC & HPERM & HTRM & HLIVE & HMOK).
destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HRB as (Hsp1 & Hgp1 & Htp1 & Hs0 & Hs1 & Hs2 & Hs4 & Hs5 & Hs6 & Hs10 & Hs11).
destruct HFR as (EF & EFL & HFL56 & HSV).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres.
(* the donor journal under RLIVE's, and the frame (0, fpos) it owns *)
pose proof HJ as (_ & _ & (memS & HJd & Hag) & _). rewrite !Z.add_0_r in HJd.
pose proof (proj1 HJd) as HAR1.
assert (Hfin : In (0, fpos) (frames S1)).
{ pose proof HJd as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
change (fs_frame_bytes 0) with 64 in HF4096, HFceil, HFhigh, HFapp, HFpres, HFSpres.
change (64 / 8) with 8 in HFSpres. rewrite EF in HF4096, HFceil, HFhigh, HFal, HFapp, HFpres, HFSpres.
unfold arm in HFL56, HLK, HWK.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rrt_extra (rxregs cx) FL))) rrt_ss0
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_unlock)) m1 (seg_rom SEGS)))).
{ apply (rrt_entry W1 regs1 m1 (rxregs cx) (rsp0 cx) F FL Hs0 Hs2 Hs4).
  - rewrite WS in Hslo. lia.
  - lia.
  - exact HFal.
  - intros i Hi. replace (rsp0 cx - 88 + 8 * Z.of_nat i) with (rsp0 cx - RR_FRAME + 8 + 8 * Z.of_nat i) by (rewrite WF; lia).
    exact (HSV i Hi).
  - rewrite HV4. exact HWK. }
remember (Eimg (Ereg regs1 (rrt_extra (rxregs cx) FL))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 11)%nat -> ew E (32 + i) = getr (rxregs cx) (nth i RR_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_rrt_extra (rxregs cx) FL i Hi). }
assert (E43 : ew E 43 = Z_to_bv 64 FL).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 11). }
clear HE.
unfold cfg_at. change (w64 (BASE + A_rr_unlock)) with (Z_to_bv 64 (BASE + A_rr_unlock)).
(* 0x83fc4 .. 0x83fd0: s3 = F + 32, a0 = &g_lock, the call to pthread_mutex_unlock *)
paj_run_shc_x RUNPR RUNCR HS HJd.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
(* the run wrote nothing (both regions are read-only): every byte keeps its view *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha). intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
pose proof (pa_obj_img 6 ltac:(lia)) as HL6. rewrite <- RGLOCK in HL6.
assert (HLA : rg_lock RG mod 4 = 0).
{ destruct (Z.mod_divide (rg_lock RG) 8 ltac:(lia)) as [Hd _]. destruct (Hd RGAL8) as [q Hq]. rewrite Hq.
  replace (q * 8) with ((q * 2) * 4) by lia. apply Z_mod_mult. }
pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8. unfold awr, arm in LKW.
assert (LKM : forall a n v, rg_lock RG <= a -> a + Z.of_nat n <= rg_lock RG + 12 ->
  val_mem SEGS (mrestrict (w_H W1) m1) a n v -> val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) a n v).
{ intros a n v Ha Hn Hv. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms) a n v); [|exact Hv].
  intros j Hj. apply KEEP1. lia. }
pose proof (LKM (rg_lock RG) 4%nat 0 ltac:(lia) ltac:(cbn; lia) LK0) as MK0.
pose proof (LKM (rg_lock RG + 4) 4%nat _ ltac:(lia) ltac:(cbn; lia) LK4) as MK4.
pose proof (LKM (rg_lock RG + 8) 4%nat 0 ltac:(lia) ltac:(cbn; lia) LK8) as MK8.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W1) (ms_mem ms) a <> None).
{ intros a Ha. rewrite (KEEP1 a ltac:(lia)). unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKI : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; apply RGIMG; unfold rg_rng; left; exact Ha).
assert (HJg : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 (ms_mem ms)
  (with_vm_backing (m_vm_lazy md1) mat md1) k1)
by (apply (ajournal_gx_pack_xR SEGS B PST ARx _ 0 [] RR_STK_x (rsp0 cx) (rFP cx) _ _ _ _ _ _ _ ly1 S1 Hp1 W1 _ _ k1 memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJd | exact Hag | intros a Ha; lia]).
pose proof (proj1 HJd) as HARm.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
assert (HSPc : spZ (ms_regs ms) = rsp0 cx + -96).
{ unfold spZ at 1. rewrite QSP, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). rewrite Hsp1, WF. lia. }
assert (QA0' : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 247%nat with (A_OBJ 6). rewrite (img_env_atomP E (A_OBJ 6) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite RGLOCK. reflexivity. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RR B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
       getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W1) mem') (rg_lock RG + 4) 4 0)
    W1 _ _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) _ _ _ _ _ _ (-96) _ HG
    eq_refl HJg).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl), Hgp1. exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl), Htp1. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
    + exact QA0'.
    + lia.
    + exact HLA.
    + lia.
    + exact MK0.
    + exact MK4.
    + exact MK8.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. revert Ha HL6 Hslo Hceil C1 WS Hes. clear. intros. lia.
    + intros a Ha. split; [|split].
      * apply (writable_kept _ m1 (ms_mem ms) a); [intros Hp; exact (apresent_grows _ _ _ a HG0 Hp)|].
        replace a with (rg_lock RG + (a - rg_lock RG)) by lia. apply LKW. lia.
      * intros Ho. destruct (LKI a ltac:(lia)) as (Hi & Hno & _).
        exact (Hno (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Ho)).
      * rewrite HSPc. revert Ha HL6 Hslo Hceil C1 WS Hes. clear. intros. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HK))). unfold G_RR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPR3 & Hfr3 & Hpres3).
(* ---- back at 0x83fd4: s-registers kept, the caller-saved ones fresh atoms 48 .. 63 ---- *)
assert (U8 : bv_unsigned (ew E 8) = rsp0 cx) by (rewrite (EE 8%nat 8%bv eq_refl), Hs0; apply unsigned_lit_small; lia).
assert (U245 : bv_unsigned (ew E (A_OBJ 4)) = VAL (A_OBJ 4)) by exact (HEI (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
pose proof (pa_obj_img 4 ltac:(lia)) as HO4.
pose proof rrt_lock_wake as HLW.
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (region_kept_aview E (w_H W1) (ms_mem ms) mem3 8 (rsp0 cx)); [exact U8 | | exact Hpres3].
    intros a Ha. apply Hfr3;
    [ revert Ha Hslo Hshi H47 Hceil C1 WS; clear; intros; lia
    | revert Ha HL6 Hslo Hceil C1 WS; clear; intros; lia
    | revert Ha Hes; clear; intros; lia ].
  - apply (region_kept_aview E (w_H W1) (ms_mem ms) mem3 (A_OBJ 4) (VAL (A_OBJ 4))); [exact U245 | | exact Hpres3].
    intros a Ha. apply Hfr3;
    [ revert Ha HO4; clear; intros; lia
    | revert Ha HLW HV4; clear; intros; lia
    | revert Ha HO4 Hslo Hceil C1 WS Hes; clear; intros; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
(* the state at the unlock's return: ARx there (S1, Hp1 kept), the frame (0, fpos) and its flag cell *)
pose proof HJ3 as HAR3. apply (ajournal_gx_AR_xR SEGS B PST ARx) in HAR3.
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HAR3 Hfin) as (_ & _ & HFpres3 & HFSpres3).
destruct (FFL _ _ _ _ _ _ 0 fpos HAR3 Hfin) as (HFLp3 & HFLo3 & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HAR3 Hfin) as HFimg.
change (fs_frame_bytes 0) with 64 in HFpres3, HFSpres3, HFimg. change (64 / 8) with 8 in HFSpres3.
rewrite EF in HFpres3, HFSpres3, HFimg. rewrite EFL in HFLp3, HFLo3, HFLapp, HFLimg, HFL4096, HFLz, HFLc.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (U20a : bv_unsigned (ew Ea 20) = F) by (rewrite OLDa, (EE 20%nat 20%bv eq_refl), Hs4 by lia; apply unsigned_lit_small; lia).
assert (U21a : bv_unsigned (ew Ea 21) = shadow_addr F)
by (rewrite OLDa, (EE 21%nat 21%bv eq_refl), Hs5 by lia; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U43a : bv_unsigned (ew Ea 43) = FL) by (rewrite OLDa, E43 by lia; apply unsigned_lit_small; lia).
assert (U8a : bv_unsigned (ew Ea 8) = rsp0 cx) by (rewrite OLDa by lia; exact U8).
assert (U245a : bv_unsigned (ew Ea 245%nat) = VAL (A_OBJ 4)) by exact (HEIa (A_OBJ 4) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
(* F + 56 holds FL at the unlock's return: kept by the run (nothing written) and by the call (F is no lock byte
   and lies below the stack) *)
assert (KF : forall a, F <= a < F + 64 -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. rewrite (Hfr3 a ltac:(lia) ltac:(revert Ha HL6 HFimg; clear; unfold off_img; intros; lia)
    ltac:(revert Ha HFceil Hslo Hceil C1 WS Hes; clear; intros; lia)). apply KEEP1. lia. }
assert (HFL56' : val_mem SEGS (mrestrict (w_H W1) mem3) (F + (64 - 8)) 8 FL).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 mem3 (F + (64 - 8)) 8 FL); [|replace (F + (64 - 8)) with (F + 56) by lia; exact HFL56].
  intros j Hj. apply KF. cbn in Hj. lia. }
(* seat F (atom 20), its shadow (atom 21) and the flag cell (atom 43) *)
pose proof (st_ok_pi_add_region Ea _ _ (fframe_region 20 43 0 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0) with 64; rewrite U20a; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres3 (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ea _ F (64 - 8) 8 _ FL);
  [cbn [sv_denot]; rewrite OLDa, E43, Z.add_0_r, Z_to_bv_bv_unsigned by lia; reflexivity | zside | zside | exact HFL56'] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite U20a, U8a, U245a;
revert HFceil HFimg Hslo Hceil C1 WS HO4; clear; unfold off_img; intros; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (fshadow_region 21 0 0 8 []) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
change (fs_frame_bytes 0 / 8) with 8; rewrite U21a; split; [unfold shadow_addr, SHADOW_OFF; lia|]; split; [unfold shadow_addr, SHADOW_OFF; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFSpres3 o ltac:(lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite U21a, U20a, U8a, U245a;
revert HFceil HFimg HFapp HF4096 HFq HF8 Hslo Hceil C1 C3 WS HO4; clear;
unfold shadow_addr, SHADOW_OFF, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Ea _ _ (YP09.mkRegion (Some 43%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U43a; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp3)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U43a, U21a, U20a, U8a, U245a;
repeat split;
lazymatch goal with
| |- ?fl + 1 <= F + ?l \/ F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFpres3 FL ltac:(lia)) HFLo3)
| |- ?fl + 1 <= shadow_addr F + ?l \/ shadow_addr F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (shadow_addr F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (shadow_addr F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFSpres3 (FL - shadow_addr F) ltac:(lia)) ltac:(replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia; exact HFLo3))
| |- ?g => revert HFLc HFLz Hslo Hceil C1 WS HO4; clear; unfold zone2, off_img; intros; lia
end)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* ---- 0x83fd4 .. 0x84094: the wake byte, the wake test (g_wake[1] = -1: not taken), the release (retired magic,
   shadow 0xf5, *flag = 0) and the epilogue, one plain run ending at the ret ---- *)
pose proof HJ3 as (_ & _ & (memS3 & HJd3 & Hag3) & _). rewrite !Z.add_0_r in HJd3.
paj_run_flag_sh_x RUNFR HS HJd3.
{ lia. }
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8a, ?U20a, ?U21a, ?U43a, ?U245a in Hr;
    first [ lia
    | right; rewrite EFL; lia
    | left; right; right; right; exists 0, fpos; split; [left; reflexivity|]; rewrite EF; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
{ intros msr HSr. rewrite EFL.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U43a
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
(* ---- the return: a strict step, lifted to R (SRr_SRrG, WLE_R) ---- *)
prreg HS (1%bv : bv 5) Rr1. prreg HS (2%bv : bv 5) Rr2. prreg HS (3%bv : bv 5) Rr3. prreg HS (4%bv : bv 5) Rr4.
prreg HS (8%bv : bv 5) Rr8. prreg HS (9%bv : bv 5) Rr9. prreg HS (18%bv : bv 5) Rr18. prreg HS (19%bv : bv 5) Rr19.
prreg HS (20%bv : bv 5) Rr20. prreg HS (21%bv : bv 5) Rr21. prreg HS (22%bv : bv 5) Rr22. prreg HS (23%bv : bv 5) Rr23.
prreg HS (24%bv : bv 5) Rr24. prreg HS (25%bv : bv 5) Rr25. prreg HS (26%bv : bv 5) Rr26. prreg HS (27%bv : bv 5) Rr27.
assert (EXa : forall i, (i < 11)%nat -> ew Ea (32 + i) = getr (rxregs cx) (nth i RR_SAVED 0%bv))
by (intros i Hi; rewrite OLDa by lia; exact (EX i Hi)).
assert (RA : getr (ms_regs ms0) 1 = getr (rxregs cx) 1) by (rewrite Rr1; exact (EXa 10%nat ltac:(lia))).
(* what the second run kept: everything outside F, its shadow and FL *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 64) -> ~ (shadow_addr F <= a < shadow_addr F + 8) -> a <> FL ->
  aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem3 a).
{ intros a Ha H1 H2 H3. apply (aview_kept_out Ea _ (w_H W1) mem3 (ms_mem ms0) HFr0 a Ha). intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U8a, ?U20a, ?U21a, ?U43a, ?U245a in Hr; lia | ]).
  destruct Hin. }
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
exists (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat0 md3)) mat'
  (with_vm_backing (m_vm_lazy md3) mat0 md3)), k1.
split; [rewrite RA, Hra; reflexivity|].
split.
{ apply (ajournal_gx_pack_xR SEGS B PST ARx _ 0 [] RR_STK_x (rsp0 cx) (rFP cx) _ _ _ _ _ _ _ ly1 _ _ W1 _ _ k1 memS3);
  [lia | lia | | exact Hag3 | intros a Ha; lia].
  rewrite !Z.add_0_r. apply (ajournal_x_materializeR SEGS B PST ARx LAWS Hsegs). exact HJd3. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr2, OLDa, (EE 8%nat 8%bv eq_refl), Hs0 by lia. unfold rsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr3, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp1.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr4, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp1.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr8. exact (EXa 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr9. exact (EXa 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr18. exact (EXa 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr19. exact (EXa 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr20. exact (EXa 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr21. exact (EXa 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr22. exact (EXa 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr23. exact (EXa 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr24. exact (EXa 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr25. exact (EXa 0%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr26, OLDa, (EE 26%nat 26%bv eq_refl) by lia. exact Hs10.
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr27, OLDa, (EE 27%nat 27%bv eq_refl) by lia. exact Hs11. }
split.
{ intros a Ha Hl HFa HSa HFLa Hsc. rewrite (KEEP3 a Ha HFa HSa HFLa).
  rewrite (Hfr3 a Ha Hl ltac:(rewrite WF in Hsc; lia)). exact (KEEP1 a Ha). }
split.
{ intros a Hp. apply (apresent_grows _ _ _ a HG1). apply Hpres3. exact (apresent_grows _ _ _ a HG0 Hp). }
destruct HPR3 as (_ & HL40). unfold arm.
apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem3 (ms_mem ms0) (rg_lock RG + 4) 4 0); [|exact HL40].
intros j Hj. cbn in Hj. apply KEEP3;
[ lia
| revert Hj HL6 HFimg; clear; unfold off_img; intros; lia
| revert Hj HL6 HF4096; clear; unfold shadow_addr, SHADOW_OFF; intros; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia
| intros He; revert He Hj HL6 HFLz; clear; unfold zone2, off_img; intros; lia ].
Qed.

(* rr_tail at R *)
Theorem rr_tail_xR : rr_tail_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold rr_tail_stmt_xR. intros cx oi W1 c1 HB HU.
destruct HU as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & -> & HRB & HFD0 & HOI).
assert (HLV : RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1)
by (destruct oi as [i|]; [exact (proj1 HOI) | exact (proj1 (proj1 HOI))]).
destruct HLV as (fpos & HJ & HROM & HPK & HFR & HLK & HWK).
eapply (SRrG_mono SEGS R); [exact (rr_tail_walk_xR cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 F FL fpos HB HRB HJ HFR HLK HWK)|].
cbv beta. intros W2 c2 _ (-> & regs' & m' & md' & k' & -> & HOUT).
exact (rr_tail_post_xR cx oi W1 ly1 S1 Hp1 m1 md1 k1 F FL fpos regs' m' md' k' HB HFD0 HOI HJ HFR HOUT).
Qed.
End wR.

End c.
End b.
End a.
