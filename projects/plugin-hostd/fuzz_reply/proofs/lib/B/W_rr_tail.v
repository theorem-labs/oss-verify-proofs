(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the TAIL segment of the IMAGE-B (fuzz_reply.asan-ubsan) walk of relay_remove
   (lib/B/W_relay_remove_cx.v rr_tail_stmt): from the unlock cut RRU oi (0x843c0) through pthread_mutex_unlock
   (g_lock) 0x843c8 (AUNLOCK, W_sites.v aj_gx_entry_at), the epilogue 0x843cc-0x843e4 (ra, s0 .. s4 from their
   slots, sp = the entry sp) and the tail call `j wake` 0x843e8: WAKE (W_wake_c.v wk_spec) at the entry sp, its
   journal (G = []) lifted to G_RR (rr_lift_WK) and composed with the walk's (W_journal.v ajournal_gx_sub).  Proof
   SHAPE from the image-A twin lib/A/W_rr_tail.v (a working branch) and lane W7's W_drain_epi.v (a fresh symbolic
   state seated at the cut); the instruction run is B's (no fake frame in B's relay_remove: wake keeps its byte in
   its own frame).  No trap edge in this segment. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (lane RRX, the image-A twin a Theorem Labs lane f4cd818e98d
   lib/A/W_rr_tail.v): TAIL over ANY allocator relation ARx in the room form, IN PLACE (the AR theorem is dropped).
   Section c is W_relay_remove_cx.v's generic block; the journal is W_journal_x.v ajournal_gx_x at RR_STK_x (the head
   set after each state), the laws and journal lemmas their _x twins (alx_*, ajournal_gx_nil_x / _pack_x / _inner_x /
   _AR_x / _sub_x, YCbqG.v afn_pre_x_at), the runners W_frame_x.v's, the unlock at aunlock_realizes_x through
   W_sites_x.v aj_gx_entry_at_x (S1 and its head set kept), and the tail-called wake at W_wake_c_x.v wk_spec_x.  The
   kept set rkz asks its image bytes off PST (the generic journal's image clause keeps only those; PSTG gives it for
   the cells of rr_gcells).  rr_tail_out carries wake's seat fact `exists f, S' = set_fs f S1` in place of the meter:
   MO_FR gives rr_post_x's meter and RPF_of its room rp_RM RP S' kr, from RRU (Some i)'s RDONE (rp_RM RP S1 kr) or
   from RRU None's RHELD (the whole budget, down to kr by RMM_of). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
(* route R (the Section wR below): SRrG, and the R contract texts (W_contract_xR.v dr_spec_xR / gse_spec_xR,
   W_contract_xR_relayB.v rr_post_xR) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_remove_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
(* the allocator rules on the _c form (W_journal.v Section hc; a Theorem Labs lane 21:24Z): one table CTX_AFREE for free and
   free(NULL), which enter the same interceptor pc0.  Image B's relay_remove keeps NO frame pointer: at its free
   (0x8435c, ra 0x84360 = entry + 0x164) s0 holds fd, an integer below alloc_ceiling, so chain_pre's chain is cut by
   the register and the trace is the CLOSED singleton [0x84360] (a Theorem Labs lane 21:32Z; K0's B CTX_AFREE row, lib/B/YCk0.v:19).  The
   kit's B rr_spec_x takes it as its LAST premise `In [pc + 356] CTX_AFREE` (W4's b_facts, a Theorem Labs lane 21:5xZ); RCTX
   below carries it to MATCH's free (no ly_top conjunct: the chain is []). *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (image B's top, W_wake_x.v's form), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC); ASMP / ASF / FFL are the class-0
   fake frame's laws (image B's relay_remove takes none: wake does, W_wake_x.v) *)
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
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src (the abstract placement does not fix them against the objects; PB_fr on
   AsanUbsan discharges both by vm_compute, as the image-A twin's HH59 / HH60) *)
Hypothesis HH53 : VAL (A_HI 53) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH54 : VAL (A_HI 54) = rg_src RG + RR_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are unowned image bytes (the image-A twin's HRGP / HRGI, verbatim) *)
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
(* no read-only image byte is owned by the runtime: rom_view survives the calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs;
   image B meets it at wake's return (W_wake_c_x.v wk_post_x's seat fact S' = set_fs f S) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (image B calls free's interceptor directly, WS_free) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) and wake (W_wake_c_x.v) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* B only: wake, tail-called at 0x843e8 (image A inlines it); W_relay_remove.v builds it by W_wake_x.v pb_wake_x *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (the image-A twin's PSTR / PSTG, verbatim). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

(* ---- The bytes the tail keeps (rkz): image bytes outside g_lock's lock word, the allocator's statics, errno and the
   program statics PST (the unlock writes only the lock word; wake's generic journal keeps such bytes: its image
   clause exempts PST), errno (wake's post keeps its view), and the bytes of the live blocks.  rfz: a footprint all of
   whose bytes are such. ---- *)
Definition rkz (ly : alayout) (S : astate) (a : Z) : Prop :=
  (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
   ~ Exists (in_zr a) PST /\ ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)) \/
  (as_errno B <= a < as_errno B + 4) \/
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
intros ly S p n len a Hin Hn Hl Ha. right. right. exists p, n. split; [exact Hin|].
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

(* the footprints of the representation predicates are kept bytes, and name live blocks (the image-A twin's) *)
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

(* the global cells the post reads (rr_post's g_s, the table's and the stream's cells, g_wake[1], errno): image bytes
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
Lemma rrt_cell_nown : rg_place B RG -> forall a, rr_cells a -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). unfold rr_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
first [ exact (proj1 (proj2 (RGIMG a ltac:(unfold rg_rng; tauto))))
      | exact (proj2 (HRGI a ltac:(tauto)))
      | exact (proj1 (proj2 (HG a ltac:(unfold inG, G_RR, G_DR, G_SL; rr_exists)))) ].
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
(* the cells are off the program statics: they are cells of rr_gcells (PSTG) *)
Lemma rrt_cell_npst : forall a, rr_cells a -> ~ Exists (in_zr a) PST.
Proof.
intros a Ha. apply PSTG. unfold rr_gcells. unfold rr_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
repeat (first [apply Exists_cons_hd; cbv beta; cbn [fst snd]; lia | apply Exists_cons_tl]).
Qed.
Lemma rrt_cell_kz : forall ly S a, rg_place B RG -> rr_cells a -> rkz ly S a.
Proof.
intros ly S a RGP Ha.
assert (He : (as_errno B <= a < as_errno B + 4) \/ ~ (as_errno B <= a < as_errno B + 4)) by lia.
destruct He as [He | He]; [right; left; exact He|].
left. split; [exact (rrt_cell_img RGP a Ha)|]. split; [exact (rrt_cell_nown RGP a Ha)|]. split; [exact He|].
split; [exact (rrt_cell_npst a Ha)|].
pose proof (rrt_cell_nlock a Ha). lia.
Qed.
(* g_lock's twelve bytes are off the program statics: the first cell of rr_gcells (PSTG) *)
Lemma rrt_lock_npst : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ Exists (in_zr a) PST.
Proof. intros a Ha. apply PSTG. unfold rr_gcells. apply Exists_cons_hd. cbv beta. cbn [fst snd]. lia. Qed.
(* g_lock's 12 bytes are apart from errno's 4 and g_wake[1]'s 4 (HRGP's pairs 0 / 14 and 0 / 13) *)
Lemma rrt_lock_errno : rg_lock RG + 12 <= as_errno B \/ as_errno B + 4 <= rg_lock RG.
Proof.
pose proof HRGP as H. cbn [zpairwise_disjoint zall_disjoint] in H. unfold zdisj in H. cbn [fst snd] in H.
destruct H as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H.
Qed.
Lemma rrt_lock_wake : rg_lock RG + 12 <= rg_wake RG + 4 \/ rg_wake RG + 8 <= rg_lock RG.
Proof.
pose proof HRGP as H. cbn [zpairwise_disjoint zall_disjoint] in H. unfold zdisj in H. cbn [fst snd] in H.
destruct H as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H.
Qed.

(* ---- Frame lemmas. ---- *)
(* writability survives a change of world when presence does *)
Lemma writable_kept2 : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  (apresent H m a -> apresent H' m' a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H' m') a.
Proof.
intros H H' m m' a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; [|destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em].
- intros Hw. destruct (H' (Z_to_bv 64 a)); [exact Hw|]. destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
- intros _. destruct (Hp (conj EH (ex_intro _ b Em))) as [EH' [b2 Hb2]]. rewrite EH', Hb2. discriminate.
- intros Hw. destruct (H' (Z_to_bv 64 a)); [exact Hw|]. destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
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
intros c mx no cap FD es h NM. unfold rr_tr.
destruct (FD <? 0); [reflexivity|]. rewrite (rr_find_none es FD NM). reflexivity.
Qed.

(* rr_found survives the tail: its predicates sit on kept bytes and on blocks the tail keeps *)
Lemma rr_found_kept : forall ly S W mem ly1 S1 W1 m1 ly2 S2 W2 m2 G0 es i j h c O mx cap out,
  rg_place B RG ->
  (forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W2 m2 a) ->
  ablocks B ly2 S2 = ablocks B ly1 S1 ->
  (re_eof (nth i es relay_remove_b_c.no_entry) = 0 -> (j < 4)%nat) ->
  rr_found B RG ly S W mem ly1 S1 W1 m1 G0 es i j h c O mx cap out ->
  rr_found B RG ly S W mem ly2 S2 W2 m2 G0 es i j h c O mx cap out.
Proof.
intros ly S W mem ly1 S1 W1 m1 ly2 S2 W2 m2 G0 es i j h c O mx cap out RGP KEEP EBL HJ4 HF.
assert (AK : forall fp, rfz ly1 S1 fp -> akept W1 m1 W2 m2 fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (BLK : forall b, In b (ablocks B ly1 S1) -> In b (ablocks B ly2 S2)) by (intros b Hb; rewrite EBL; exact Hb).
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
  exact (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ h1 HAS (AK _ F1) (fun b Hb => BLK b (F2 b Hb))). }
split; [exact HSL|].
split.
{ assert (HC : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
                          rg_capsrc RG <= a < rg_capsrc RG + 4 -> rkz ly1 S1 a)
    by (intros a Ha; apply CKZ; unfold rr_cells; tauto).
  destruct (rfz_arelay ly1 S1 W1 m1 G0 _ HREL HC) as [R1 R2].
  exact (arelay_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HREL (AK _ R1) (fun b Hb => BLK b (R2 b Hb))). }
split.
{ destruct (rfz_aout ly1 S1 W1 m1 _ _ _ _ _ _ HOUT OUTC) as [O1' O2'].
  exact (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT (AK _ O1') (fun b Hb => BLK b (O2' b Hb))). }
split; [exact HPa|].
rewrite EBL. exact HPb.
Qed.

(* ---- What the walk from 0x843c0 to wake's return delivers (rr_tail_walk): the journal from relay_remove's entry
   (own = []), the callee-saved registers, the live blocks unchanged and the allocator state a set_fs of the cut's
   (wake's seat fact: the meter by MO_FR, the room by RPF_of), every rkz byte kept, the presence of image bytes grown,
   the lock word 0 and g_wake[1] still -1. ---- *)
Definition rr_tail_out (cx : rcx) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (regs2 : bvmap 5 word) (m2 : word -> option byte)
(md2 : Model) (k2 : Z) : Prop :=
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 /\
aregs_preserved (rxregs cx) regs2 /\
ablocks B ly2 S2 = ablocks B ly1 S1 /\
(exists f, S2 = set_fs f S1) /\
(forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W2 m2 a) /\
(forall a, in_img SEGS a -> apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) /\
val_mem SEGS (arm W2 m2) (rg_lock RG + 4) 4 0 /\
awake_at RG W2 m2.

(* ---- The seat at 0x843c0 (W7's W_drain_epi.v dr_epi_entry form).
   Atoms: the registers 0 .. 31 of the cut, then the six saved registers of the entry (32 .. 37, in RR_SAVED order:
   s4, s3, s2, s1, s0, ra).  One region: the frame's six slots at sp (atom 2), read-only (the epilogue's loads
   0x843cc-0x843e0); the tail writes nothing itself. ---- *)
Definition rrt_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 48 0 0
  (map (fun i => YP09.mkChunk (8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 6)).
Definition rrt_ss0 : sstate := mkSS A_rr_unlock sr_atoms [rrt_stack] None (mkFacts [] [] []).
Definition rrt_extra (regsE : bvmap 5 word) : list word := map (getr regsE) RR_SAVED.
Lemma nth_rrt_extra : forall regsE i, (i < 6)%nat ->
  nth i (rrt_extra regsE) (Z_to_bv 64 0) = getr regsE (nth i RR_SAVED 0%bv).
Proof.
intros regsE i Hi. unfold rrt_extra.
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
Lemma rrt_entry : forall (W : world SEGS) regs1 m1 regsE sp1,
  spZ regs1 = sp1 -> alloc_ceiling <= sp1 -> sp1 + 48 <= 2 ^ 47 ->
  (forall i, (i < 6)%nat ->
   val_mem SEGS (mrestrict (w_H W) m1) (sp1 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regsE (nth i RR_SAVED 0%bv)))) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rrt_extra regsE))) rrt_ss0
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_unlock)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 regsE sp1 Hsp Hlo Hhi HSV.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (rrt_extra regsE))).
assert (E2 : ew E 2 = getr regs1 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (U2 : base_val E (Some 2%nat) = sp1) by (cbn [base_val]; rewrite E2; exact Hsp).
unfold rrt_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, rrt_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
  apply (chunk_ok_val SEGS E _ sp1 (8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i RR_SAVED 0%bv)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite ew_Ereg_extra, nth_rrt_extra by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regsE (nth i RR_SAVED 0%bv))) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. zside.
  + zside.
  + exact (HSV i ltac:(lia)).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. cbn. first [exact I | constructor | tauto].
Qed.

(* ---- The walk's runners (W_frame_x.v's AJ runners over the inner journal ajournal_x). ---- *)
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let RUNC := SRr_run_pi_AJ_call_x (PL := PL_fr) B PST ARx LAWS.
Let RUNTOP := SRr_run_to_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.

(* ---- ROUTE R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form, lib/B/W_bx_reset_x.v): the tail at a
   world relation R.  Each X_xR is X with ajournal_gx_x SEGS B PST ARx -> ajournal_gx_xR SEGS B PST ARx R, SRr SEGS ->
   SRrG SEGS R, the spine's RLIVE / RHELD / RDONE / rPOST / rr_tail_stmt -> their _xR (W_relay_remove_cx.v Section wR;
   rr_post_x -> W_contract_xR_relayB.v rr_post_xR), the journal lemmas -> their _xR twins (W_journal_x.v, YCbqG.v
   afn_pre_x_atR), the runners -> W_frame_x.v's SRrG forms, the unlock -> W_sites_x.v aj_gx_entry_at_xR (AUNLOCK stays
   strict), and this file's journal helpers -> the _xR twins below.  wake has no R contract: WAKE (wk_spec_x) stays
   strict, its SRr fact is lifted by SRr_SRrG (WLE_R), its journal (G = []) by ajournal_gx_xR_mono and rr_lift_WK_xR,
   and composed with the walk's by ajournal_gx_sub_xR.  At R := wle each twin is its strict text: the strict lemmas
   after the Section are these at wle (moved below the Section; their statements are unchanged).
   Census rows (a Theorem Labs lane's G8b-relayrm-B.tsv (sha256 4c7c7e01243b; internal record)) -> twins: :131 AFREE -> AFREE_R, :135 DRAIN -> DRAIN_R,
   :136 GSE -> GSE_R, :138 AFREEN -> AFREEN_R (declared with the spine's texts; the tail calls no free, drain or
   gestures_end, so no lemma takes them), :392 ajgx_nil_keep_img, :403 ajgx_nil_keep_blk, :414 ajgx_keep_high,
   :427 ajgx_ly_top, :440 rrt_kept, :546 rr_tail_out, :559 rr_tail_post, :668 rrt_wake, :772 rr_tail_walk,
   :1041 rr_tail -> their _xR. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary set RO (an argument of their texts) *)
Variable RO : (word -> option byte) -> Prop.
(* :131 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :135 DRAIN, :136 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :138 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :392 ajgx_nil_keep_img *)
Lemma ajgx_nil_keep_img_xR : forall STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R [] 0 [] STK sp0 [] ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k a HJ Hi Ho He Hps.
apply ajournal_gx_nil_xR in HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply (F3 a Hi Ho He Hps). apply fp_spares_closed. intros (r & Hr & _). destruct Hr.
Qed.
(* :403 ajgx_nil_keep_blk *)
Lemma ajgx_nil_keep_blk_xR : forall STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n a,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R [] 0 [] STK sp0 [] ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> p <= a < p + req_size n ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n a HJ H1 H2 Ha.
apply ajournal_gx_nil_xR in HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
replace a with (p + (a - p)) by lia. apply (F2 p n (a - p) H1 H2); [lia | exact (inFP_nil _)].
Qed.
(* :414 ajgx_keep_high *)
Lemma ajgx_keep_high_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  gx_ok SEGS B G ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* :427 ajgx_ly_top *)
Lemma ajgx_ly_top_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ly_top ly' = ly_top ly.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET.
Qed.
(* :440 rrt_kept *)
Lemma rrt_kept_xR : forall ly1 S1 Hp1 W1 m1 md1 mw mdw ly2 S2 Hp2 W2 m2 md2 k STK sp0 sp1,
  ARx ly1 S1 Hp1 W1 m1 md1 -> rg_place B RG -> alloc_ceiling <= sp1 - ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> ~ (sp1 - ESTACK <= a < sp1) ->
     aview SEGS (w_H W1) mw a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mw a) ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R [] 0 [] STK sp0 [] ly1 S1 Hp1 W1 mw mdw [] ly2 S2 Hp2 W2 m2 md2 k ->
  ablocks B ly2 S2 = ablocks B ly1 S1 ->
  (forall a, in_img SEGS a -> apresent (w_H W1) mw a -> apresent (w_H W2) m2 a) ->
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) mw (as_errno B + i)) ->
  forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W2 m2 a.
Proof.
intros ly1 S1 Hp1 W1 m1 md1 mw mdw ly2 S2 Hp2 W2 m2 md2 k STK sp0 sp1 HAR RGP HSC V P1 HJk EBL P2 ERR a Ha.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJk) as HAR2.
assert (WI : in_img SEGS a -> writable_at SEGS (arm W1 m1) a -> writable_at SEGS (arm W2 m2) a)
  by (intros Hi Hw; unfold arm in *; exact (writable_kept2 _ _ m1 m2 a (fun Hp => P2 a Hi (P1 a Hp)) Hw)).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
assert (HLI : forall x, rg_lock RG + 4 <= x < rg_lock RG + 8 -> in_img SEGS x)
  by (intros x Hx; exact (proj1 (RGIMG x ltac:(unfold rg_rng; left; lia)))).
destruct Ha as [(Himg & Hno & Hne & Hnp & Hnl) | [Herr | (p & n & Hin & Hpa)]].
- split; [|exact (WI Himg)].
  pose proof (Hsegs a Himg) as Hl.
  rewrite (ajgx_nil_keep_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJk Himg Hno Hne Hnp).
  apply V; [revert Hl C5; clear; intros; lia | exact Hnl | revert Hl HSC C1 C5; clear; intros; lia].
- assert (Hei : in_img SEGS a) by (exact (proj1 (HG a ltac:(unfold inG, G_RR, G_DR, G_SL; rr_exists)))).
  split; [|exact (WI Hei)].
  pose proof (Hsegs a Hei) as Hl. pose proof rrt_lock_errno as HLE.
  replace a with (as_errno B + (a - as_errno B)) by lia. rewrite (ERR (a - as_errno B) ltac:(lia)).
  replace (as_errno B + (a - as_errno B)) with a by lia.
  apply V; [revert Hl C5; clear; intros; lia | revert Herr HLE; clear; intros; lia | revert Hl HSC C1 C5; clear; intros; lia].
- split.
  + destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR Hin) as (_ & Hp4096 & Hpceil & Happ & Hpno & _).
    pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 p n HAR Hin) as Hn.
    rewrite (ajgx_nil_keep_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n a HJk Hin ltac:(rewrite EBL; exact Hin) Hpa).
    apply V.
    * revert Hp4096 Hpceil Hpa C1 Hn. clear. intros. pose proof (req_size_pos n ltac:(lia)). lia.
    * intros Hw. refine (proj2 (alx_client_img _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 a HAR _) (HLI a Hw)).
      left. exists p, n. split; [exact Hin | exact Hpa].
    * intros Hs. revert Hpceil Hpa HSC Hs. clear. intros. lia.
  + intros _.
    destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 ltac:(rewrite EBL; exact Hin))
      as (_ & _ & _ & _ & HPr2 & _).
    unfold arm. apply (apresent_writable SEGS). exact (proj1 (HPr2 a Hpa)).
Qed.
(* :546 rr_tail_out at R *)
Definition rr_tail_out_xR (cx : rcx) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS) (regs2 : bvmap 5 word) (m2 : word -> option byte)
(md2 : Model) (k2 : Z) : Prop :=
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 /\
aregs_preserved (rxregs cx) regs2 /\
ablocks B ly2 S2 = ablocks B ly1 S1 /\
(exists f, S2 = set_fs f S1) /\
(forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W2 m2 a) /\
(forall a, in_img SEGS a -> apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) /\
val_mem SEGS (arm W2 m2) (rg_lock RG + 4) 4 0 /\
awake_at RG W2 m2.
(* :559 rr_tail_post *)
Lemma rr_tail_post_xR : forall cx oi W1 ly1 S1 Hp1 m1 md1 k1 W2 ly2 S2 Hp2 regs2 m2 md2 k2,
RBASE B ARx MT RP MMAX RG cx -> 0 <= rxFD cx ->
match oi with
| None => RHELD_xR B PST ARx R MT RP RG cx ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE_xR B PST ARx R MT RP RG cx i ly1 S1 Hp1 W1 m1 md1 k1
end ->
rr_tail_out_xR cx ly1 S1 W1 m1 ly2 S2 Hp2 W2 regs2 m2 md2 k2 ->
rPOST_xR B PST ARx R MT RP RG cx W2 (mkCfg (mkst regs2 (getr (rxregs cx) 1) m2 (seg_rom SEGS)) md2).
Proof.
intros cx oi W1 ly1 S1 Hp1 m1 md1 k1 W2 ly2 S2 Hp2 regs2 m2 md2 k2 HB HFD HOI HOUT.
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & _ & HSRC0 & HPERM0 & _).
destruct HOUT as (J' & HRGS & EBL & HSEAT & KEEP & P & L & HWK2).
(* the meter across wake: its end state is a set_fs of S1 (the seat fact), which MO_FR does not count *)
assert (HMO : mo_le MT S1 S2 0) by (destruct HSEAT as (f & ->); exact (MO_FR S1 f)).
assert (AK : forall fp, rfz ly1 S1 fp -> akept W1 m1 W2 m2 fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (BLK : forall b, In b (ablocks B ly1 S1) -> In b (ablocks B ly2 S2)) by (intros b Hb; rewrite EBL; exact Hb).
assert (CKZ : forall a, rr_cells a -> rkz ly1 S1 a) by (intros a Ha; exact (rrt_cell_kz ly1 S1 a RGP Ha)).
assert (HLV : apres_kept B (rxW cx) (rxmem cx) W1 m1 /\ alock_at RG W1 m1 true).
{ destruct oi as [i|].
  - destruct HOI as ((_ & _ & HPK & _ & HLK1 & _) & _). exact (conj HPK HLK1).
  - destruct HOI as (((_ & _ & HPK & _ & HLK1 & _) & _) & _). exact (conj HPK HLK1). }
destruct HLV as (HPK & HLK1).
unfold rPOST_xR, rr_post_xR. cbv beta.
exists ly2, S2, Hp2, regs2, m2, md2, k2.
split; [reflexivity|].
split; [exact J'|].
split; [exact HRGS|].
split; [intros a H1 H2 H3 H4; apply P; [exact H1 | exact (HPK a H1 H2 H3 H4)]|].
(* the meter: the cut's charge, then MO_FR for wake *)
split.
{ destruct oi as [i|].
  - destruct HOI as (_ & _ & _ & HMO1 & _).
    apply (mle_weaken MT (rxS cx) _ (tr_cost MT (rtr cx) + 0)); [exact MLAW | | unfold rtr; lia].
    exact (mle_station MT _ S1 _ _ _ MLAW HMO1 HMO).
  - destruct HOI as ((_ & _ & _ & _ & _ & _ & HMO1 & _) & NM).
    apply (mle_weaken MT (rxS cx) _ (0 + 0)); [exact MLAW | | rewrite (rr_tr_none _ _ _ _ _ _ _ NM); lia].
    exact (mle_station MT _ S1 _ _ _ MLAW HMO1 HMO). }
(* the room: RRU (Some i)'s RDONE carries kr, RRU None's RHELD the whole budget (RMM_of down to kr); the unlock kept
   S1 and wake's end state is a set_fs of S1 (the seat fact), which keeps rp_RM (RPF_of) *)
split.
{ destruct HSEAT as (f & ->). apply RPF_of. destruct oi as [i|].
  - destruct HOI as (_ & _ & _ & _ & _ & _ & HRM1). exact HRM1.
  - destruct HOI as ((_ & _ & _ & _ & _ & _ & _ & _ & HRM1 & _) & _).
    eapply RMM_of; [|exact HRM1]. lia. }
(* g_lock free: its type and waiters words kept, the lock word 0 *)
split.
{ destruct HLK1 as (LK0 & LK4 & LK8 & LKW).
  assert (KL : forall x, rg_lock RG <= x < rg_lock RG + 4 \/ rg_lock RG + 8 <= x < rg_lock RG + 12 ->
    abyte_kept W1 m1 W2 m2 x).
  { intros x Hx. apply KEEP. left. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
    destruct (RGIMG x ltac:(unfold rg_rng; left; lia)) as (Hi & Ho & He).
    split; [exact Hi|]. split; [exact Ho|]. split; [exact He|]. split; [exact (rrt_lock_npst x ltac:(lia))|]. lia. }
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KL; cbn in Hx; lia | exact LK0]|].
  split; [exact L|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KL; cbn in Hx; lia | exact LK8]|].
  intros i Hi. unfold arm in *. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
  exact (writable_kept2 _ _ m1 m2 _ (P _ (proj1 (RGIMG (rg_lock RG + i) ltac:(unfold rg_rng; left; lia)))) (LKW i Hi)). }
(* g_wake[1] *)
split; [exact HWK2|].
(* g_s *)
split.
{ intros a Ha Hj.
  assert (K2 : abyte_kept W1 m1 W2 m2 a) by (apply KEEP; apply CKZ; unfold rr_cells; left; exact Ha).
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
      exact (arelay_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ HREL1 (AK _ R1) (fun b Hb => BLK b (R2 b Hb))).
    + destruct (rfz_aout ly1 S1 W1 m1 _ _ _ _ _ _ HOUT1 OUTC) as [O1 O2].
      exact (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT1 (AK _ O1) (fun b Hb => BLK b (O2 b Hb))).
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
  exact (rr_found_kept (rxly cx) (rxS cx) (rxW cx) (rxmem cx) ly1 S1 W1 m1 ly2 S2 W2 m2
    (rxG0 cx) (rxes cx) i (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) RGP KEEP EBL HJ4 HFND).
- exfalso. destruct HOI as (_ & NM). exact (NM _ (nth_In _ _ Hi') Hfd').
Qed.
(* :668 rrt_wake: WAKE strict (no wk_spec_xR), lifted by SRr_SRrG; wake's journal to R by ajournal_gx_xR_mono, to
   G_RR by rr_lift_WK_xR, composed with the walk's by ajournal_gx_sub_xR *)
Lemma rrt_wake_xR : forall W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw ch1,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 -> WK_STK <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) sp0 (s0Z regsc) ch1 ->
count_cid 0 (frames Sc) < fs_frames 0 -> awake_at RG W memc -> rom_view SEGS W memc ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_wake)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2
   (k + k1) /\
 ajournal_gx_xR (SK := SK) SEGS B PST ARx R [] 0 [] WK_STK sp0 [] lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
 (forall a, in_img SEGS a -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\ awake_at RG W2 mem2 /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memc (as_errno B + i)) /\
 (exists f, S2 = set_fs f Sc)).
Proof.
intros W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw ch1 HJ Hsp HSTK Hgp Htp Hra Hraw Hra4 Hch
  Hcnt Hwk Hrom.
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
rewrite !Z.add_0_r in HJi.
assert (HPRE1 : afn_pre_x SEGS B ARx WK_STK lyc Sc Hpc W regsc memc mdc ch1).
{ eapply afn_pre_x_atR with (STK1 := WK_STK) (o := 0) (ch1 := ch1).
  - exact HJi.
  - rewrite Hsp. lia.
  - reflexivity.
  - lia.
  - unfold WK_STK, WK_FRAME, ASTACK. lia.
  - lia.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - exact Hgp.
  - exact Htp.
  - rewrite Hsp. exact Hch. }
eapply SRrG_mono.
{ exact (SRr_SRrG SEGS R WLE_R _ _ _ (WAKE W lyc Sc Hpc regsc memc mdc ch1 HPRE1 Hcnt Hwk Hrom)). }
cbv beta. intros W2 c2 _ (regs2 & ly2 & S2 & Hp2 & mem2 & md2 & k1 & -> & HJw & HP & HBL & HPR & HWK & HER & HFS).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [rewrite Hra; reflexivity|].
rewrite Hsp in HJw.
(* wake's journal (strict, G = []) at R (WLE_R) *)
assert (HJwR : ajournal_gx_xR (SK := SK) SEGS B PST ARx R [] 0 [] WK_STK sp0 [] lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1)
  by (eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJw]).
split.
{ change own with ([] ++ own).
  eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS pa_segs_low R_trans (G_RR B RG));
  [ exact HJ
  | eapply rr_lift_WK_xR; exact HJwR
  | unfold WK_STK, WK_FRAME, ASTACK in *; lia | lia | lia
  | intros a (r & Hr & _); destruct Hr
  | exact HG
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]. }
split; [exact HJwR|]. split; [exact HP|]. split; [exact HBL|]. split; [exact HPR|]. split; [exact HWK|]. split; [exact HER | exact HFS].
Qed.
(* the walk's runners at R (W_frame_x.v's SRrG runners over the inner journal ajournal_xR) *)
Let RUNPR := SRrG_run_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNCR := SRrG_run_pi_AJ_call_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNTOPR := SRrG_run_to_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
(* :772 rr_tail_walk *)
Lemma rr_tail_walk_xR : forall cx W1 regs1 ly1 S1 Hp1 m1 md1 k1,
RBASE B ARx MT RP MMAX RG cx ->
rregs_base cx regs1 ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> rr_saved cx W1 m1 -> alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
SRrG SEGS R W1 (cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1)
  (fun W' c' => exists ly' S' Hp' regs' m' md' k',
     c' = mkCfg (mkst regs' (getr (rxregs cx) 1) m' (seg_rom SEGS)) md' /\
     rr_tail_out_xR cx ly1 S1 W1 m1 ly' S' Hp' W' regs' m' md' k').
Proof.
intros cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 HB HRB HJ HROM1 HSV HLK HWK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & H32 & HCNT & RGP & _).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HRB as (Hsp1 & Hgp1 & Htp1 & Hs5).
assert (WS : RR_STK_x = 17056) by reflexivity. assert (WF : RR_FRAME = 48) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. assert (WK : WK_STK = 16448) by reflexivity.
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres, Hch.
(* the journal under RLIVE's, and the frames (own = []) *)
pose proof HJ as (_ & _ & (memS & HJd & Hag) & _). rewrite !Z.add_0_r in HJd.
pose proof HJd as (_ & _ & _ & _ & _ & Hfrs1 & _).
unfold arm in HLK, HWK.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rrt_extra (rxregs cx)))) rrt_ss0
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_unlock)) m1 (seg_rom SEGS)))).
{ apply (rrt_entry W1 regs1 m1 (rxregs cx) (rsp0 cx - 48)).
  - rewrite Hsp1, WF. reflexivity.
  - rewrite WS in Hslo. lia.
  - lia.
  - intros i Hi. replace (rsp0 cx - 48 + 8 * Z.of_nat i) with (rsp0 cx - RR_FRAME + 8 * Z.of_nat i) by (rewrite WF; lia).
    exact (HSV i Hi). }
remember (Eimg (Ereg regs1 (rrt_extra (rxregs cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 6)%nat -> ew E (32 + i) = getr (rxregs cx) (nth i RR_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  exact (nth_rrt_extra (rxregs cx) i Hi). }
clear HE.
assert (U2 : bv_unsigned (ew E 2) = rsp0 cx - 48).
{ rewrite (EE 2%nat 2%bv eq_refl). change (bv_unsigned (getr regs1 2)) with (spZ regs1). rewrite Hsp1, WF. reflexivity. }
unfold cfg_at. change (w64 (BASE + A_rr_unlock)) with (Z_to_bv 64 (BASE + A_rr_unlock)).
(* 0x843c0 .. 0x843c8: a0 = &g_lock, the call to pthread_mutex_unlock *)
paj_run_shc_x RUNPR RUNCR HS HJd.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
(* the run wrote nothing (the region is read-only): every byte keeps its view *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha). intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
pose proof (pa_obj_img 3 ltac:(lia)) as HL3. rewrite <- RGLOCK in HL3.
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
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 (ms_mem ms)
  (with_vm_backing (m_vm_lazy md1) mat md1) k1)
by (apply (ajournal_gx_pack_xR SEGS B PST ARx _ 0 [] RR_STK_x (rsp0 cx) (rFP cx) _ _ _ _ _ _ _ ly1 S1 Hp1 W1 _ _ k1 memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJd | exact Hag | intros a Ha; lia]).
pose proof (proj1 HJd) as HARm.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
assert (HSPc : spZ (ms_regs ms) = rsp0 cx + -48).
{ unfold spZ at 1. rewrite QSP, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). rewrite Hsp1, WF. lia. }
assert (QA0' : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 244%nat with (A_OBJ 3).
  rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite RGLOCK. reflexivity. }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RR B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
       getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W1) mem') (rg_lock RG + 4) 4 0)
    W1 _ _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) _ _ _ _ _ _ (-48) _ HG
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
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. revert Ha HL3 Hslo Hceil C1 WS Hes. clear. intros. lia.
    + intros a Ha. split; [|split].
      * apply (writable_kept _ m1 (ms_mem ms) a); [intros Hp; exact (apresent_grows _ _ _ a HG0 Hp)|].
        replace a with (rg_lock RG + (a - rg_lock RG)) by lia. apply LKW. lia.
      * intros Ho. destruct (LKI a ltac:(lia)) as (Hi & Hno & _).
        exact (Hno (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Ho)).
      * rewrite HSPc. revert Ha HL3 Hslo Hceil C1 WS Hes. clear. intros. lia.
    + (* QMm W1 (B engine 9015b6a6f732): the lock word is in G_RR, and gx_ok's kept clause puts it off as_kept *)
      intros a Ha HK. exact (proj2 (proj2 (HG a ltac:(unfold G_RR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))) (proj1 (proj2 HK))). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPR3 & Hfr3 & Hpres3).
(* ---- back at 0x843cc: s-registers kept, the caller-saved ones fresh atoms 48 .. 63; the slots kept ---- *)
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_aview E (w_H W1) (ms_mem ms) mem3 2 (rsp0 cx - 48)); [exact U2 | | exact Hpres3].
  intros a Ha. apply Hfr3;
  [ revert Ha Hslo Hshi H47 Hceil C1 WS; clear; intros; lia
  | revert Ha HL3 Hslo Hceil C1 WS; clear; intros; lia
  | revert Ha Hes; clear; intros; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
(* ---- 0x843cc .. 0x843e8: the epilogue (ra, s0 .. s4 from the slots, sp += 48) and `j wake` ---- *)
pose proof HJ3 as (_ & _ & (memS3 & HJd3 & Hag3) & _). rewrite !Z.add_0_r in HJd3.
paj_run_to_shc_x RUNTOPR HS HJd3 AF_fr_wake.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem3 a).
{ intros a Ha. apply (aview_kept_out Ea _ (w_H W1) mem3 (ms_mem ms0) HFr0 a Ha). intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]). destruct Hin. }
(* what the unlock and the two runs kept: everything but the lock word and the unlock's scratch *)
assert (V : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  ~ (rsp0 cx - 48 - ESTACK <= a < rsp0 cx - 48) ->
  aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hl Hs. rewrite (KEEP3 a Ha). rewrite (Hfr3 a Ha Hl ltac:(lia)). exact (KEEP1 a Ha). }
assert (P1 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a).
{ intros a Hp. apply (apresent_grows _ _ _ a HG1). apply Hpres3. exact (apresent_grows _ _ _ a HG0 Hp). }
(* ---- at wake's entry ---- *)
pmkst HS.
prreg HS (1%bv : bv 5) Rr1. prreg HS (2%bv : bv 5) Rr2. prreg HS (3%bv : bv 5) Rr3. prreg HS (4%bv : bv 5) Rr4.
prreg HS (8%bv : bv 5) Rr8. prreg HS (9%bv : bv 5) Rr9. prreg HS (18%bv : bv 5) Rr18. prreg HS (19%bv : bv 5) Rr19.
prreg HS (20%bv : bv 5) Rr20. prreg HS (21%bv : bv 5) Rr21. prreg HS (22%bv : bv 5) Rr22. prreg HS (23%bv : bv 5) Rr23.
prreg HS (24%bv : bv 5) Rr24. prreg HS (25%bv : bv 5) Rr25. prreg HS (26%bv : bv 5) Rr26. prreg HS (27%bv : bv 5) Rr27.
assert (EXa : forall i, (i < 6)%nat -> ew Ea (32 + i) = getr (rxregs cx) (nth i RR_SAVED 0%bv))
by (intros i Hi; rewrite OLDa by lia; exact (EX i Hi)).
assert (RA : getr (ms_regs ms0) 1 = getr (rxregs cx) 1) by (rewrite Rr1; exact (EXa 5%nat ltac:(lia))).
assert (R8 : getr (ms_regs ms0) 8 = getr (rxregs cx) 8) by (rewrite Rr8; exact (EXa 4%nat ltac:(lia))).
assert (RSP : getr (ms_regs ms0) 2 = getr (rxregs cx) 2).
{ rewrite Rr2, OLDa by lia. rewrite U2. replace (rsp0 cx - 48 + 48) with (rsp0 cx) by lia.
  unfold rsp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (HPw : aregs_preserved (rxregs cx) (ms_regs ms0)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact RSP.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr3, OLDa, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp1.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr4, OLDa, (EE 4%nat 4%bv eq_refl) by lia. exact Htp1.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact R8.
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr9. exact (EXa 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr18. exact (EXa 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr19. exact (EXa 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Rr20. exact (EXa 0%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr21, OLDa, (EE 21%nat 21%bv eq_refl) by lia. exact (Hs5 21%bv ltac:(split; vm_compute; discriminate)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr22, OLDa, (EE 22%nat 22%bv eq_refl) by lia. exact (Hs5 22%bv ltac:(split; vm_compute; discriminate)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr23, OLDa, (EE 23%nat 23%bv eq_refl) by lia. exact (Hs5 23%bv ltac:(split; vm_compute; discriminate)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr24, OLDa, (EE 24%nat 24%bv eq_refl) by lia. exact (Hs5 24%bv ltac:(split; vm_compute; discriminate)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr25, OLDa, (EE 25%nat 25%bv eq_refl) by lia. exact (Hs5 25%bv ltac:(split; vm_compute; discriminate)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr26, OLDa, (EE 26%nat 26%bv eq_refl) by lia. exact (Hs5 26%bv ltac:(split; vm_compute; discriminate)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rr27, OLDa, (EE 27%nat 27%bv eq_refl) by lia. exact (Hs5 27%bv ltac:(split; vm_compute; discriminate)). }
(* the journal at wake's entry *)
assert (HJw : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 (ms_mem ms0)
  (with_vm_backing (m_vm_lazy md3) mat0 md3) k1)
by (apply (ajournal_gx_pack_xR SEGS B PST ARx _ 0 [] RR_STK_x (rsp0 cx) (rFP cx) _ _ _ _ _ _ _ ly1 S1 Hp1 W1 _ _ k1 memS3);
    [lia | lia | rewrite !Z.add_0_r; exact HJd3 | exact Hag3 | intros a Ha; lia]).
(* g_wake[1] and the .rodata view at wake's entry: image bytes off the lock word *)
assert (AWK : awake_at RG W1 (ms_mem ms0)).
{ unfold awake_at, arm. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms0) (rg_wake RG + 4) 4 _); [|exact HWK].
  intros j Hj. cbn in Hj. pose proof rrt_lock_wake as HLW.
  pose proof (proj1 (RGIMG (rg_wake RG + 4 + j) ltac:(unfold rg_rng; right; right; right; left; lia))) as Hi.
  pose proof (Hsegs _ Hi) as Hl.
  apply V; [revert Hl C5; clear; intros; lia | revert Hj HLW; clear; intros; lia |
            revert Hl Hslo Hceil C1 C5 WS Hes; clear; intros; lia]. }
assert (AROM : rom_view SEGS W1 (ms_mem ms0)).
{ intros a Hin.
  assert (Hi : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (Hsegs a Hi) as Hl.
  rewrite V; [exact (HROM1 a Hin) | revert Hl C5; clear; intros; lia | |
              revert Hl Hslo Hceil C1 C5 WS Hes; clear; intros; lia].
  intros Hlk. apply (proj1 (HROMO a Hin)). unfold G_RR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
eapply SRrG_mono.
{ eapply (rrt_wake_xR W1 (ms_regs ms0) (ms_mem ms0) _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx)
    (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 k1 (getr (rxregs cx) 1) (rxch cx) HJw).
  - unfold spZ at 1. rewrite RSP. reflexivity.
  - rewrite WK, WS. lia.
  - rewrite Rr3, OLDa, (EE 3%nat 3%bv eq_refl), Hgp1 by lia. exact Hgp.
  - rewrite Rr4, OLDa, (EE 4%nat 4%bv eq_refl), Htp1 by lia. exact Htp.
  - exact RA.
  - exact Hra.
  - exact Hra4.
  - replace (s0Z (ms_regs ms0)) with (s0Z (rxregs cx)) by (unfold s0Z; rewrite R8; reflexivity).
    apply (achain_ly_top (rxly cx) ly1); [exact (ajgx_ly_top_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw)|].
    apply (achain_kept (rxly cx) (aview SEGS (w_H (rxW cx)) (rxmem cx)) _ (rsp0 cx) (s0Z (rxregs cx)) (rxch cx) (rsp0 cx) Hch);
      [lia | lia |].
    intros a Ha. apply (ajgx_keep_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG HJw a); [lia | rewrite WS; lia].
  - rewrite Hfrs1. exact HCNT.
  - exact AWK.
  - exact AROM. }
cbv beta. intros W2 c2 _
  (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & -> & HJc & HJk & HP2 & EBL2 & Hpres2 & HWK2 & HER2 & (fw & ES2)).
exists ly2, S2, Hp2, regs2, mem2, md2, (k1 + k2). split; [reflexivity|].
unfold rr_tail_out_xR.
split; [exact HJc|].
split; [exact (aregs_preserved_trans _ _ _ HPw HP2)|].
split; [exact EBL2|].
(* the allocator state: wake changes it only by a set_fs (wk_post_x's seat fact) *)
split; [exists fw; exact ES2|].
split.
{ eapply (rrt_kept_xR ly1 S1 Hp1 W1 m1 md1 (ms_mem ms0) _ ly2 S2 Hp2 W2 mem2 md2 k2 WK_STK (rsp0 cx) (rsp0 cx - 48)
    (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) RGP);
    [| exact V | exact P1 | exact HJk | exact EBL2 | exact Hpres2 | exact HER2].
  rewrite WS in Hslo. lia. }
split; [intros a Hi Hp; exact (Hpres2 a Hi (P1 a Hp))|].
split.
{ destruct HPR3 as (_ & HL40). unfold arm.
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) mem3 mem2 (rg_lock RG + 4) 4 0); [|exact HL40].
  intros j Hj. cbn in Hj. destruct (LKI (rg_lock RG + 4 + j) ltac:(lia)) as (Hi & Hno & He).
  pose proof (Hsegs _ Hi) as Hl.
  rewrite (ajgx_nil_keep_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJk Hi Hno He
    (rrt_lock_npst (rg_lock RG + 4 + j) ltac:(lia))).
  apply KEEP3. revert Hl C5; clear; intros; lia. }
exact HWK2.
Qed.
(* :1041 rr_tail *)
Theorem rr_tail_xR : rr_tail_stmt_xR B PST ARx R MT RP MMAX RG.
Proof.
unfold rr_tail_stmt_xR. intros cx oi W1 c1 HB HU.
destruct HU as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & -> & HRB & HFD0 & HOI).
assert (HLV : RLIVE_xR B PST ARx R RG cx ly1 S1 Hp1 W1 m1 md1 k1)
by (destruct oi as [i|]; [exact (proj1 HOI) | exact (proj1 (proj1 HOI))]).
destruct HLV as (HJ & HROM & HPK & HSV & HLK & HWK).
eapply SRrG_mono; [exact (rr_tail_walk_xR cx W1 regs1 ly1 S1 Hp1 m1 md1 k1 HB HRB HJ HROM HSV HLK HWK)|].
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & m2 & md2 & k2 & -> & HOUT).
exact (rr_tail_post_xR cx oi W1 ly1 S1 Hp1 m1 md1 k1 W2 ly2 S2 Hp2 regs2 m2 md2 k2 HB HFD0 HOI HOUT).
Qed.
End wR.
(* the strict texts below are the R section's at R := wle (route R's rule: one walk text): each R premise at wle is
   the strict hypothesis of the same name, and the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* a journal at G = [] keeps the image bytes outside the allocator's statics, errno and the program statics PST, and
   the bytes of the blocks live at both ends *)
Lemma ajgx_nil_keep_img : forall STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k a,
  ajournal_gx_x (SK := SK) SEGS B PST ARx [] 0 [] STK sp0 [] ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof. eapply (ajgx_nil_keep_img_xR (@wle SEGS)); wle_inst. Qed.
Lemma ajgx_nil_keep_blk : forall STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n a,
  ajournal_gx_x (SK := SK) SEGS B PST ARx [] 0 [] STK sp0 [] ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> p <= a < p + req_size n ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof. eapply (ajgx_nil_keep_blk_xR (@wle SEGS)); wle_inst. Qed.
(* W_gesture_end.v's ajgx_keep_high and ajgx_ly_top (W4), over ajournal_gx_x *)
Lemma ajgx_keep_high : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  gx_ok SEGS B G ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof. eapply (ajgx_keep_high_xR (@wle SEGS)); wle_inst. Qed.
Lemma ajgx_ly_top : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_gx_x (SK := SK) SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ly_top ly' = ly_top ly.
Proof. eapply (ajgx_ly_top_xR (@wle SEGS)); wle_inst. Qed.

(* THE KEEP: a byte rkz at the cut keeps its view through the tail, and its writability.  V: the unlock wrote only
   the lock word and its scratch below sp1 (the two runs write nothing); then wake's journal (its image clause for an
   image byte off PST) and its errno clause.  Writability: an image byte (or errno) by presence, which wake keeps for
   image bytes; a byte of a live block by the laws' block clause at wake's post state (the block is still live: wake
   keeps the live blocks). *)
Lemma rrt_kept : forall ly1 S1 Hp1 W1 m1 md1 mw mdw ly2 S2 Hp2 W2 m2 md2 k STK sp0 sp1,
  ARx ly1 S1 Hp1 W1 m1 md1 -> rg_place B RG -> alloc_ceiling <= sp1 - ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> ~ (sp1 - ESTACK <= a < sp1) ->
     aview SEGS (w_H W1) mw a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mw a) ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx [] 0 [] STK sp0 [] ly1 S1 Hp1 W1 mw mdw [] ly2 S2 Hp2 W2 m2 md2 k ->
  ablocks B ly2 S2 = ablocks B ly1 S1 ->
  (forall a, in_img SEGS a -> apresent (w_H W1) mw a -> apresent (w_H W2) m2 a) ->
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) mw (as_errno B + i)) ->
  forall a, rkz ly1 S1 a -> abyte_kept W1 m1 W2 m2 a.
Proof. eapply (rrt_kept_xR (@wle SEGS)); wle_inst. Qed.

(* rr_tail_out at wle is rr_tail_out_xR (by conversion) *)
Lemma rr_tail_out_wle : rr_tail_out = rr_tail_out_xR (@wle SEGS).
Proof. reflexivity. Qed.

Lemma rr_tail_post : forall cx oi W1 ly1 S1 Hp1 m1 md1 k1 W2 ly2 S2 Hp2 regs2 m2 md2 k2,
RBASE B ARx MT RP MMAX RG cx -> 0 <= rxFD cx ->
match oi with
| None => RHELD B PST ARx MT RP RG cx ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE B PST ARx MT RP RG cx i ly1 S1 Hp1 W1 m1 md1 k1
end ->
rr_tail_out cx ly1 S1 W1 m1 ly2 S2 Hp2 W2 regs2 m2 md2 k2 ->
rPOST B PST ARx MT RP RG cx W2 (mkCfg (mkst regs2 (getr (rxregs cx) 1) m2 (seg_rom SEGS)) md2).
Proof. eapply (rr_tail_post_xR (@wle SEGS)); wle_inst. Qed.

(* ---- wake (), the tail call at the entry sp: WAKE (W_wake_c_x.v wk_spec_x, at G = []: wake writes no global), its
   journal lifted to G_RR (rr_lift_WK) and composed with the walk's (W_journal_x.v ajournal_gx_sub_x), in the form of
   W_gesture_end.v gx_callS with o = 0; the seat fact `exists f, S2 = set_fs f Sc` is wk_post_x's last conjunct. ---- *)
Lemma rrt_wake : forall W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw ch1,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 -> WK_STK <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) sp0 (s0Z regsc) ch1 ->
count_cid 0 (frames Sc) < fs_frames 0 -> awake_at RG W memc -> rom_view SEGS W memc ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_wake)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2
   (k + k1) /\
 ajournal_gx_x (SK := SK) SEGS B PST ARx [] 0 [] WK_STK sp0 [] lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
 (forall a, in_img SEGS a -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\ awake_at RG W2 mem2 /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memc (as_errno B + i)) /\
 (exists f, S2 = set_fs f Sc)).
Proof. eapply (rrt_wake_xR (@wle SEGS)); wle_inst. Qed.

Lemma rr_tail_walk : forall cx W1 regs1 ly1 S1 Hp1 m1 md1 k1,
RBASE B ARx MT RP MMAX RG cx ->
rregs_base cx regs1 ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
rom_view SEGS W1 m1 -> rr_saved cx W1 m1 -> alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1)
  (fun W' c' => exists ly' S' Hp' regs' m' md' k',
     c' = mkCfg (mkst regs' (getr (rxregs cx) 1) m' (seg_rom SEGS)) md' /\
     rr_tail_out cx ly1 S1 W1 m1 ly' S' Hp' W' regs' m' md' k').
Proof. eapply (rr_tail_walk_xR (@wle SEGS)); wle_inst. Qed.

Theorem rr_tail : rr_tail_stmt B PST ARx MT RP MMAX RG.
Proof. eapply (rr_tail_xR (@wle SEGS)); wle_inst. Qed.

End c.
End b.
End a.
