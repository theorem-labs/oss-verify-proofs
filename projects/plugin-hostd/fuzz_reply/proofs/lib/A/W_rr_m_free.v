(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the FREE hop of the MATCH segment of the ASan walk of fuzz_reply's relay_remove
   (lib/A/W_rr_match_cx.v hop_free_stmt): RRF i 0x83f74 -> ld a1, g_src; add a1,a1,s8; the shadow check of the buf
   field 0x83f7c-0x83f8c (the report 0x840ac is not taken); ld a0,16(a1); jal free 0x83f94 (AFREE when the entry has
   a buffer, cap > 0; AFREEN, s->buf = NULL, cap = 0) -> RRC i 0x83f98.

   rule 24: proves function relay_remove MATCH hop 3 (kind: segment lemma of the W6 walk, PORTED from 2ad36763b22
   relay_remove_p_c_free.v rrf_hop_proved; lookup + CONFIRM in context).

   Where each part comes from (the retired lane form: commit 2ad36763b22, lib/A/Prog/relay_remove_p_c_free.v):
   - rmf_buf_cell: the lane's rrf_buf_cell (:70-100: the buffer pointer at offset 16 of the cleared slot), restated
     over garr8 (the lane's rw_cells / rrf_ec_bytes are not needed: W6's entry_cleared is the lane's rrf_ec).
   - the case split in rr_m_free: the lane's rrf_call (:227: cap = 0 /\ buf = 0 -> free (NULL); cap > 0 -> the
     block), with the case data from RRF (W6's aentry_ok form) and the block from RRF's Permutation.
   - rmf_nth_le_bytes, rmf_eb_len, rmf_concat_len, rmf_garr8_le, the Ltac rmf_mem: copied from lib/A/W_rr_scan.v
     rrs_nth_le_bytes / rrs_eb_len / rrs_concat_len / rrs_garr8_le / rrs_mem.
   - rmf_bzs_len, rmf_text_rec_len, rmf_concat_trec_len, rmf_key_ptrs_len, rmf_aout_fp_cases, rmf_abk_trans, the
     Ltac rmf_exists: copied from lib/A/W_rr_tail.v rr_bzs_len / rr_text_rec_len / rr_concat_len / rr_key_ptrs_len /
     rr_aout_fp_cases / abyte_kept_trans / rr_exists.
   - rmf_writable_view, rmf_view_some, rmf_vm_kept, rmf_not_owned, rmf_nodup: copied from lib/A/W_gestures_end.v
     gse_writable_view / gse_view_some / gse_vm_kept / gse_not_owned / gse_nodup.
   - rmf_free: the form of lib/A/W_gestures_end.v gse_free (AFREE / AFREEN over ajournal_gx); new: the footprint
     premise is AFREE's own (the block was live at the entry), since drain may have given s->buf a new block.
   - rmf_fz_alist, rmf_fz_asrc, rmf_fz_aentry, rmf_fz_aout: the form of lib/A/W_rr_tail.v rfz_alist / rfz_asrc /
     rfz_aentry / rfz_aout over any byte predicate (new: the predicate is a parameter).
   - the symbolic state at 0x83f74 (ss_rmf .. RMF_REGS) and the run: the form of W_rr_scan.v rr_scan's seat (new
     atoms: g_src's region through the image atom A_HI 60, the slot alias, the buf field's shadow entry).
   - rmf_writable_kept, rmf_zall_In, rmf_in, rmf_nerr, rmf_cell, rmf_cell_img, rmf_bk_sub, rmf_keep, rmf_ap,
     rr_m_free: new.  The call chain free's rule asks for (chain_pre) is lib/A/W_rr_m_kit.v rr_call_chain_pre. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (a Theorem Labs lane, lane RR_x): FREE over ANY
   allocator relation ARx (Section c is W_relay_remove_cx.v's generic block): the journal ajournal_gx_x with the head
   sets, the laws' and frame / block twins (alx_blocks, alx_owned_image, alx_sep, blk_off_imgP_x, sep_blocks_x,
   sep_block_frame_x, range_addressable_of_block_hp0_x, ajournal_gx_rom_view_x with PSTR), RUN = paj_run_x_x; rmf_free
   over the _c_x free rules in W_gestures_end.v gse_free_x's form (the stack room by aj_stack_room_x), still with
   AFREE's own footprint premise; rmf_nodup reads a block's size bound off BLKN (alx_blocks has no MALLOC_MAX
   conjunct).  The room round: the free is applied at kr := rxkr cx with RRF's rp_RM RP S1 (1 + rxkr cx) and
   cnt_ok RP (ablocks B ly1 S1) (the hop only loads and checks shadow before the jal, so RRF's state is the call's);
   the rule's post rp_RM RP S2 (rxkr cx) is RRC's last conjunct. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx W_rr_match_cx W_rr_m_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Notation rmf_le8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Notation rmf_le4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.

(* ------------------------------------------------------------------ byte lists *)
Lemma rmf_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma rmf_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
intros e P1 P2. unfold entry_bytes.
rewrite !length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, P1, P2. reflexivity.
Qed.
Lemma rmf_concat_len : forall l, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
induction l as [|e l IH]; intros HF; [reflexivity|].
apply Forall_cons_iff in HF as [[P1 P2] HF]. cbn [map concat length]. rewrite length_app, (rmf_eb_len e P1 P2), (IH HF). lia.
Qed.
Lemma rmf_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rmf_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma rmf_concat_trec_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, rmf_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma rmf_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
(* zall_disjoint names every pair of its list *)
Lemma rmf_zall_In : forall p l q, zall_disjoint p l -> In q l -> zdisj p q.
Proof.
intros p l q. induction l as [|x l IH]; intros H Hq; [destruct Hq|].
cbn [zall_disjoint] in H. destruct H as [H1 H2]. destruct Hq as [<- | Hq]; [exact H1 | exact (IH H2 Hq)].
Qed.
Ltac rmf_in := repeat (first [left; reflexivity | right]).

(* a run over read-only regions leaves the memory as it was (W_rr_scan.v rrs_mem) *)
Ltac rmf_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Lemma rmf_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, rmf_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

(* the buffer pointer of the cleared slot: its fifth field, 16 bytes into the slot (the lane's rrf_buf_cell) *)
Lemma rmf_buf_cell : forall M G (pre rest : list byte) e,
  garr8 SEGS M G (bzs (pre ++ entry_bytes (entry_cleared e) ++ rest)) ->
  length (re_pad1 e) = 4%nat -> 0 <= re_buf e < 2 ^ 64 ->
  val_mem SEGS M (G + Z.of_nat (length pre) + 16) 8 (re_buf e).
Proof.
intros M G pre rest e Hg P1 Hb.
assert (EB : entry_bytes (entry_cleared e) =
  (rmf_le4 (Z_to_bv 64 (re_fd e)) ++ rmf_le4 (Z_to_bv 64 (re_eof e)) ++ rmf_le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e) ++
  rmf_le8 (Z_to_bv 64 (re_buf e)) ++
  (rmf_le8 (Z_to_bv 64 (re_used e)) ++ rmf_le8 (Z_to_bv 64 (re_cap e)) ++
   rmf_le8 (Z_to_bv 64 (re_hp (entry_cleared e))) ++ rmf_le4 (Z_to_bv 64 (re_nheld (entry_cleared e))) ++ re_pad2 e)).
{ unfold entry_bytes. rewrite <- !app_assoc. reflexivity. }
rewrite EB in Hg. unfold bzs in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _]. apply garr8_app in Hg as [_ Hg].
apply garr8_app in Hg as [Hg _].
match type of Hg with garr8 _ _ ?b _ => replace b with (G + Z.of_nat (length pre) + 16) in Hg end.
2:{ repeat (rewrite length_app || rewrite length_map).
    rewrite !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4, P1. lia. }
apply rmf_garr8_le; [|exact Hb].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8, word_to_le_bytes in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

(* A byte a reader sees, off the read-only segments, is writable (W_gestures_end.v gse_writable_view). *)
Lemma rmf_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
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
Lemma rmf_view_some : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma rmf_vm_kept : forall H H' (m m' : word -> option byte) a n v, val_mem SEGS (mrestrict H m) a n v ->
(forall b, a <= b < a + Z.of_nat n -> aview SEGS H' m' b = aview SEGS H m b) -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Hk. apply (val_mem_kept SEGS H H' m m' a n v); [|exact Hv]. intros k Hk'. apply Hk. lia.
Qed.
(* writability follows presence, across two hidden sets *)
Lemma rmf_writable_kept : forall H H' (m m' : word -> option byte) a,
(apresent H m a -> apresent H' m' a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H' m') a.
Proof.
intros H H' m m' a Hp Hw. unfold writable_at, wview, mrestrict in *.
destruct (H' (Z_to_bv 64 a)) eqn:EH'; destruct (H (Z_to_bv 64 a)) eqn:EH.
- exact Hw.
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
  destruct (Hp (conj EH (ex_intro _ b Em))) as [Hf _]. rewrite EH' in Hf. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

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

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].

(* ------------------------------------------------------------------ journal and allocator helpers *)
Lemma rmf_not_owned : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho.
exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown).
Qed.
(* W_gestures_end.v gse_nodup_x: a live block's size is non-negative by BLKN *)
Lemma rmf_nodup : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR. destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _].
apply pairwise_app_l in Hpw as [Hpw _].
assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
  cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. inversion Hpos as [|? ? Hb Hl]; subst.
apply List.NoDup_cons; [|exact (IH Hpw Hl)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Definition rmf_hpblk (hp kh : Z) : list (Z * Z) := if hp =? 0 then [] else [(hp, kh)].
(* free (hp): the null rule when hp = 0, else the block rule for (hp, kh); both on the inner journal, repacked
   (W_gestures_end.v gse_free_x's form, with AFREE's own footprint premise).  The room round: the rule's kr, its RM
   and count premises at the call's state Sc, and its post's RM, are the lemma's; the stack room is the inner
   journal's (aj_stack_room_x). *)
Lemma rmf_free : forall G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l (o : Z) raw ch
  (kr : nat),
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
Permutation (ablocks B lyc Sc) (rmf_hpblk hp kh ++ l) ->
getr regsT 10 = w64 hp ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
rp_RM RP Sc (1 + kr) ->
cnt_ok RP (ablocks B lyc Sc) ->
(hp <> 0 -> In (hp, kh) (ablocks B ly S) -> forall i, 0 <= i < req_size kh -> inFP FP (hp + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_x (SK := SK) SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) l /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => hp <> 0 /\ hp <= a < hp + req_size kh) /\
mo_le MT Sc S2 (mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
intros G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l o raw ch kr
  (H0 & H1 & (memS & HJi & Hag) & Hout) HP H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCT HRM HCNT HFP MOK.
rewrite !Z.add_0_r in HJi.
pose proof (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Hsp Hst) as Hroom.
unfold rmf_hpblk in HP. destruct (Z.eqb_spec hp 0) as [Hz | Hnz].
- subst hp. cbn [app] in HP. eapply SRr_mono.
  { exact (AFREEN W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k o raw ch kr HJi H10 Hsp Hal Hneg Hst
      Hroom Hgp Htp Hra Hraw Hch HCT HRM HCNT MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPm & _ & HK & HM & HRM2 & HE & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|]. split; [eapply Permutation_trans; [exact HPm | exact HP]|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a []]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hpa. apply HPr; [exact Hi | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | exact Hpa].
- assert (Hin : In (hp, kh) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
  eapply SRr_mono.
  { apply (AFREE W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k hp kh o raw ch kr HJi Hin H10 Hsp Hal
      Hneg Hst Hroom Hgp Htp Hra Hraw Hch HCT HRM HCNT); [intros Hin0 i Hi; exact (HFP Hnz Hin0 i Hi) | exact MOK]. }
  cbv beta.
  intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & _ & HK & HM & HRM2 & HE
    & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|].
  split; [rewrite E2; apply Permutation_sym; apply (@Permutation_cons_app_inv _ l l1 l2 (hp, kh)); rewrite <- E1;
    apply Permutation_sym; exact HP|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a Ha; split; [exact Hnz | exact Ha]]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hpa. apply HPr; [exact Hi | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hpa].
  intros Hr. pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc W memT mdc hp kh (proj1 HJi) Hin) as Hoff.
  pose proof (pa_img_range a Hi). unfold off_img in Hoff. lia.
Qed.

(* ------------------------------------------------------------------ what the free keeps *)
(* The bytes free keeps, as abyte_kept: image bytes off the allocator's statics and errno; the bytes of every block
   still live after it (the freed one is apart from them); errno's bytes the program sees. *)
Lemma rmf_keep : forall lyc Sc Hpc W1 m1 mdc ly2 S2 Hp2 W2 m2 md2 slo shi hp kh l,
ARx lyc Sc Hpc W1 m1 mdc -> ARx ly2 S2 Hp2 W2 m2 md2 ->
Permutation (ablocks B lyc Sc) (rmf_hpblk hp kh ++ l) -> Permutation (ablocks B ly2 S2) l ->
acall_kept SEGS B lyc Sc W1 m1 W2 m2 slo shi (fun a => hp <> 0 /\ hp <= a < hp + req_size kh) ->
apres_kept B W1 m1 W2 m2 ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) m2 (as_errno B + i) = aview SEGS (w_H W1) m1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept W1 m1 W2 m2 a) /\
(forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> abyte_kept W1 m1 W2 m2 a) /\
(forall a, as_errno B <= a < as_errno B + 4 -> aview SEGS (w_H W1) m1 a <> None -> abyte_kept W1 m1 W2 m2 a).
Proof.
intros lyc Sc Hpc W1 m1 mdc ly2 S2 Hp2 W2 m2 md2 slo shi hp kh l HAR1 HAR2 HP HP2 (K1 & K2 & K3 & K4 & K5 & K6) HPK HE.
split; [|split].
- intros a Hi Ho He. split; [exact (K3 a Hi Ho He)|].
  intros Hw. unfold arm in *. apply (rmf_writable_kept (w_H W1) (w_H W2) m1 m2 a); [|exact Hw].
  intros Hp. exact (HPK a Hi Ho He Hp).
- intros p n a Hin Ha.
  assert (Hl : In (p, n) l) by (eapply Permutation_in; [exact HP2 | exact Hin]).
  assert (Hc : In (p, n) (ablocks B lyc Sc))
    by (eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; right; exact Hl]).
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 Hin) as (_ & _ & _ & _ & Hpr & _).
  split.
  + replace a with (p + (a - p)) by lia. apply (K2 p n (a - p)); [exact Hc | lia |].
    intros (Hnz & Hr).
    assert (Hhk : In (hp, kh) (ablocks B lyc Sc)).
    { eapply Permutation_in; [apply Permutation_sym; exact HP|]. unfold rmf_hpblk.
      rewrite (proj2 (Z.eqb_neq _ _) Hnz). left. reflexivity. }
    assert (Hne : (hp, kh) <> (p, n)).
    { intros Heq. pose proof (rmf_nodup _ _ _ _ _ _ HAR1) as ND. apply (Permutation_NoDup HP) in ND.
      unfold rmf_hpblk in ND. rewrite (proj2 (Z.eqb_neq _ _) Hnz) in ND. cbn [app] in ND.
      apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. rewrite Heq. exact Hl. }
    pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc W1 m1 mdc hp kh p n HAR1 Hhk Hc Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  + intros _. unfold arm. apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)).
- intros a Ha Hv.
  assert (Hva : aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a)
    by (replace a with (as_errno B + (a - as_errno B)) by lia; apply HE; lia).
  split; [exact Hva|]. intros _. unfold arm.
  destruct (aview SEGS (w_H W1) m1 a) as [v|] eqn:Ev; [|exfalso; exact (Hv eq_refl)].
  pose proof (proj1 (proj2 (pal_env B TL)) a Ha) as Hi. pose proof (pa_img_range a Hi) as HIR.
  apply (rmf_writable_view (w_H W2) m2 a v); [lia | exact Hva|].
  intros Hr. destruct (HROMO a Hr) as (_ & _ & Hne & _). exact (Hne Ha).
Qed.

(* the relay's and the output's cells that are not in rg_rng: image bytes off the statics and errno *)
Definition rmf_cell (a : Z) : Prop :=
  rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
  rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
  rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
  rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1.
Ltac rmf_exists := repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Lemma rmf_nerr : forall a, rmf_cell a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He. pose proof HRGP as H. cbn [zpairwise_disjoint] in H.
destruct H as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & _).
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R5 ltac:(rmf_in)) as D5.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R6 ltac:(rmf_in)) as D6.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R7 ltac:(rmf_in)) as D7.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R8 ltac:(rmf_in)) as D8.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R9 ltac:(rmf_in)) as D9.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R10 ltac:(rmf_in)) as D10.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R11 ltac:(rmf_in)) as D11.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R12 ltac:(rmf_in)) as D12.
pose proof (rmf_zall_In _ _ (as_errno B, as_errno B + 4) R13 ltac:(rmf_in)) as D13.
unfold zdisj in D5, D6, D7, D8, D9, D10, D11, D12, D13. cbn [fst snd] in D5, D6, D7, D8, D9, D10, D11, D12, D13.
unfold rmf_cell in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]];
[ clear - D5 Ha He | clear - D6 Ha He | clear - D7 Ha He | clear - D8 Ha He | clear - D9 Ha He | clear - D10 Ha He
| clear - D11 Ha He | clear - D12 Ha He | clear - D13 Ha He ]; lia.
Qed.
Lemma rmf_cell_img : forall a, rmf_cell a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. pose proof (rmf_nerr a Ha) as Hne. unfold rmf_cell in Ha.
(* QMm W0': gx_ok has a third clause (~ as_kept); project its first two here *)
assert (HG2 : forall x, inG (G_RR B RG) x -> in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
  by (intros x Hx; destruct (HG x Hx) as (H1 & H2 & _); exact (conj H1 H2)).
assert (HI : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]];
  first [ apply HRGI; lia | apply HG2; unfold inG, G_RR, G_DR, G_SL; rmf_exists ]. }
destruct HI as [Hi Ho]. split; [exact Hi | split; [exact Ho | exact Hne]].
Qed.

(* ------------------------------------------------------------------ footprints covered by blocks *)
Definition rmf_fz (K : Z -> Prop) (fp : list (Z * Z)) : Prop := forall r, In r fp -> forall a, fst r <= a < snd r -> K a.
Definition rmf_bk (K : Z -> Prop) (bl : list (Z * Z)) : Prop :=
  forall p n a, In (p, n) bl -> p <= a < p + req_size n -> K a.
Lemma rmf_bk_sub : forall K bl bl', rmf_bk K bl' -> (forall b, In b bl -> In b bl') -> rmf_bk K bl.
Proof. intros K bl bl' H Hs p n a Hin Ha. exact (H p n a (Hs _ Hin) Ha). Qed.
Lemma rmf_fz_alist : forall (K : Z -> Prop) ly S W mem LA l lines,
  alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> K a) -> rmf_bk K (alist_blks l) ->
  rmf_fz K (alist_fp LA l).
Proof.
intros K ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA HB.
rewrite Forall_forall in H9.
intros r Hr a Ha. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact (HLA a Ha)|].
apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
  destruct Hr as [<- | []]. destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
  cbn [gfp fst snd] in Ha. rewrite rmf_bzs_len, length_app, Nat2Z.inj_add, rmf_concat_trec_len, Hj in Ha.
  apply (HB (hl_v l) (AREC * hl_cap l) a).
  + unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). apply in_or_app. left. left. reflexivity.
  + pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hrq]. unfold hl_n, AREC in *. lia.
- apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha.
  rewrite rmf_bzs_len, length_app in Ha. cbn [length] in Ha.
  apply (HB (fst x) (Z.of_nat (length (snd x)) + 1) a).
  + unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx.
  + pose proof (req_size_pos (Z.of_nat (length (snd x)) + 1) ltac:(lia)) as [_ Hrq]. lia.
Qed.
Lemma rmf_fz_asrc : forall (K : Z -> Prop) ly S W mem HA h,
  asrc_at B ly S W mem HA h -> (forall a, HA <= a < HA + ASRC -> K a) -> rmf_bk K (asrc_blks h) ->
  rmf_fz K (asrc_fp HA h).
Proof.
intros K ly S W mem HA h HS HHA HB.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                  _ & Hexp & Hheld & _).
assert (B1 : rmf_bk K (alist_blks (hs_pending h)))
  by (apply (rmf_bk_sub K _ _ HB); intros b Hb; right; apply in_or_app; left; exact Hb).
assert (B2 : rmf_bk K (alist_blks (hs_expected h)))
  by (apply (rmf_bk_sub K _ _ HB); intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (B3 : rmf_bk K (alist_blks (hs_held h)))
  by (apply (rmf_bk_sub K _ _ HB); intros b Hb; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
pose proof (rmf_fz_alist K ly S W mem (HA + 16) _ false Hpend ltac:(intros a Ha; apply HHA; unfold ASRC; lia) B1) as A1.
pose proof (rmf_fz_alist K ly S W mem (HA + 64) _ true Hexp ltac:(intros a Ha; apply HHA; unfold ASRC; lia) B2) as A2.
pose proof (rmf_fz_alist K ly S W mem (HA + 80) _ true Hheld ltac:(intros a Ha; apply HHA; unfold ASRC; lia) B3) as A3.
intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
- exact (HHA a Ha).
- cbn [gfp fst snd] in Ha. rewrite rmf_bzs_len, Hpj in Ha. apply (HB (hs_partial h) APARTIAL a); [left; reflexivity|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hrq]. lia.
- apply in_app_or in Hr as [Hr | Hr]; [exact (A1 r Hr a Ha)|].
  apply in_app_or in Hr as [Hr | Hr]; [exact (A2 r Hr a Ha) | exact (A3 r Hr a Ha)].
Qed.
Lemma rmf_fz_aentry : forall (K : Z -> Prop) ly S W mem e,
  aentry_ok B ly S W mem e -> rmf_bk K (aentry_blks e) -> rmf_fz K (aentry_fp e).
Proof.
intros K ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) HB.
rewrite Forall_forall in K15.
intros r Hr a Ha. unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|].
  destruct Hr as [<- | []]. destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
  cbn [gfp fst snd] in Ha. rewrite rmf_bzs_len, length_app, Nat2Z.inj_add, Hj, K7 in Ha.
  apply (HB (re_buf e) (re_cap e) a).
  + unfold aentry_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). apply in_or_app. left. left. reflexivity.
  + pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hrq]. lia.
- destruct Hr as [<- | Hr].
  + cbn [gfp fst snd] in Ha. rewrite rmf_bzs_len, rmf_key_ptrs_len in Ha.
    destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    { rewrite Hks in Ha. cbn [length] in Ha. lia. }
    unfold re_nheld in Hk1.
    apply (HB (re_hp e) (re_kh e) a).
    * unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
    * pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hrq]. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). cbn [gfp fst snd] in Ha.
    rewrite rmf_bzs_len, length_app in Ha. cbn [length] in Ha.
    apply (HB (key_addr k) (Z.of_nat (length (key_text k)) + 1) a).
    * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    * pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Hrq]. lia.
Qed.
(* W_rr_tail.v's rr_aout_fp_cases *)
Lemma rmf_aout_fp_cases : forall cap out r, In r (aout_fp B RG cap out) ->
  In r (aout_fp B RG 0 0) \/ (cap <> 0 /\ r = (out, out + cap)).
Proof.
intros cap out r Hr. unfold aout_fp in Hr |- *. cbn [Z.eqb] in *.
do 9 (destruct Hr as [Hr | Hr]; [left; subst r; cbn; tauto|]).
destruct (Z.eqb_spec cap 0); [destruct Hr | destruct Hr as [<- | []]; right; split; [exact n | reflexivity]].
Qed.
Lemma rmf_fz_aout : forall (K : Z -> Prop) ly S W mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> rmf_fz K (aout_fp B RG 0 0) -> rmf_bk K (aout_blks cap out) ->
  rmf_fz K (aout_fp B RG cap out).
Proof.
intros K ly S W mem c O mx no cap out HO HC HB.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Hblk).
intros r Hr a Ha. destruct (rmf_aout_fp_cases cap out r Hr) as [Hr0 | (Hc & ->)]; [exact (HC r Hr0 a Ha)|].
destruct Hblk as [(Hc0 & _) | (Hcp & _ & Hin & _)]; [lia|].
cbn [fst snd] in Ha. apply (HB out cap a).
- unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
- pose proof (req_size_pos cap ltac:(lia)) as [_ Hrq]. lia.
Qed.

(* ------------------------------------------------------------------ the state at 0x83f74 *)
(* a0 .. a2 are free; s6 = SB (atom 22), s8 = 56 i (24), s9 = g_src's register image (the image atom A_HI 60, so the
   PLdHi at 0x83f74 reads g_src's region); atom 32 = G0 (the g_src cell), 33 = &g_src[i] (the alias G0 + s8),
   34 = the slot's buf field.  The shadow entry over the slot's buf field takes the check's fast path. *)
Definition RMF_PHI : Z := 140737479966720.
Definition BxF : sv := SOff 22 0.
Definition rmf_sr : list sv := sr_set sr_atoms 25%bv (SOff (A_HI 60) 0).
Definition rmf_regions : smem :=
[ YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 33%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 34 0))] ].
Definition rmf_facts : facts :=
mkFacts [ (22%nat, mkAF SB SB 0); (33%nat, mkAF 4096 RMF_PHI 3) ] []
  [ (SAlu ALU_ADD (SOff 32 0) (SOff 24 0), SOff 33 0) ].
Definition ss_rmf : sstate := mkSS A_rr_free rmf_sr rmf_regions None rmf_facts.
Definition rmf_SH : list shent := [ mkSHE 33 16 24 ].
Definition rmf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rmf_extra (g sa bf : Z) : list word := map (Z_to_bv 64) [g; sa; bf].
Definition RMF_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.
Definition RMF_REGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma rmf_ap : forall r1 r2 (r : bv 5), aregs_preserved r1 r2 -> In r RMF_REGS -> getr r2 r = getr r1 r.
Proof.
intros r1 r2 r H Hr. pose proof (H (bv_unsigned r)) as E. rewrite Z_to_bv_bv_unsigned in E. apply E.
unfold acallee_saved. unfold RMF_REGS in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
     change (bv_unsigned x) with v end; lia |]).
destruct Hr.
Qed.
Lemma rmf_abk_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof.
intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))].
Qed.

Theorem rr_m_free : hop_free_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
unfold hop_free_stmt. intros cx i W1 c1 HB HCT HF KC.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (WA : ASTACK = 16384) by reflexivity.
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK0 & HWAKE0 & HREL0 & HOUT0 & HROM0 & HSRC0 & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres.
destruct HF as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & spent &
  -> & HMH & HLV & HDR & HP1 & HP2 & HCASE & HTB & HSL & HOUT & HPERM & HGS & HMO & HSP & HRMF & HCNF).
destruct HMH as (HRH & H25 & H24 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp1 & Hgp1 & Htp1 & Hs0 & Hs1 & Hs2 & Hs4 & Hs5 & Hs6 & Hs10 & Hs11) & Hs3 & Hs7).
pose proof HLV as (fpos & HJ0 & HROM1 & HPK1 & HFR & HLK & HWK).
pose proof HFR as (EF & EFL & HFL56 & HSV).
destruct HTB as (TS & TSW & TN & TNW & TC & TCW & TIn & TXL & (tail & TTL & TG) & TSA & TOK).
(* ---- facts at the cut ---- *)
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ0).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as (HG16 & HG4096 & HGceil & HGia & _ & _).
change (req_size ATABLE) with 896 in HGceil, HGia.
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as HGoff.
change (req_size ATABLE) with 896 in HGoff. unfold off_img in HGoff.
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & RL16 & _ & _ & ROK & RND).
assert (Hpads : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx))
  by (eapply Forall_impl; [|exact ROK]; intros e (_ & _ & Q1 & Q2 & _); split; assumption).
assert (ESA : rmSA cx i = rxG0 cx + 56 * Z.of_nat i) by reflexivity.
assert (LPRE : length (rmTpre cx i) = (56 * i)%nat).
{ unfold rmTpre. rewrite rmf_concat_len, length_firstn by (rewrite <- (firstn_skipn i (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [Hp _]; exact Hp). lia. }
assert (LPOST : length (rmTpost cx i) = (56 * (length (rxes cx) - S i))%nat).
{ unfold rmTpost. rewrite rmf_concat_len, length_skipn by (rewrite <- (firstn_skipn (S i) (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [_ Hp]; exact Hp). lia. }
assert (LX : length (entry_bytes (entry_cleared e1)) = 56%nat) by (apply rmf_eb_len; [exact HP1 | exact HP2]).
assert (LTAB : Z.of_nat (length (bzs (rmTpre cx i ++ entry_bytes (entry_cleared e1) ++ rmTpost cx i ++ tail))) = 896).
{ rewrite rmf_bzs_len, !length_app, LPRE, LX, LPOST. unfold rN, AENT, ATABLE in TTL. lia. }
assert (HBUF : (re_cap e1 = 0 /\ re_buf e1 = 0) \/
  (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\ 4096 <= re_buf e1 /\
   re_buf e1 + req_size (re_cap e1) <= alloc_ceiling)).
{ destruct HCASE as [HC0 | HCP]; [left; exact HC0|right].
  assert (Hin : In (re_buf e1, re_cap e1) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. right. apply in_or_app. left. unfold rmbuf.
    rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)). left. reflexivity. }
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hin) as (_ & Hb4096 & Hbceil & _).
  split; [exact HCP|]. split; [exact Hin|]. split; lia. }
assert (EHP : rmbuf e1 = rmf_hpblk (re_buf e1) (re_cap e1)).
{ unfold rmbuf, rmf_hpblk. destruct HBUF as [(Hc & Hb) | (Hc & _ & Hb & _)].
  - rewrite Hc, Hb. reflexivity.
  - rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)), (proj2 (Z.eqb_neq (re_buf e1) 0) ltac:(lia)). reflexivity. }
assert (HBR : 0 <= re_buf e1 < 2 ^ 64).
{ destruct HBUF as [(_ & Hb) | (Hc & _ & Hb & Hb2)]; [rewrite Hb; lia|].
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as [Hr1 _]. lia. }
assert (MB : val_mem SEGS (arm W1 m1) (rmSA cx i + 16) 8 (re_buf e1)).
{ pose proof (rmf_buf_cell (arm W1 m1) (rxG0 cx) (rmTpre cx i) (rmTpost cx i ++ tail) e1 TG HP1 HBR) as M.
  rewrite LPRE in M. rewrite ESA. replace (rxG0 cx + 56 * Z.of_nat i + 16) with (rxG0 cx + Z.of_nat (56 * i) + 16) by lia.
  exact M. }
assert (Hi16 : (S i <= 16)%nat) by lia.
(* ---- the symbolic state at 0x83f74 ---- *)
remember (Eimg (Ereg regs1 (rmf_extra (rxG0 cx) (rmSA cx i) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmf_extra (rxG0 cx) (rmSA cx i) (re_buf e1))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact Hs6).
assert (E24 : ew E 24 = Z_to_bv 64 (AENT * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rmSA cx i))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E249 : ew E (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E340 : ew E (A_HI 60) = Z_to_bv 64 (VAL (A_HI 60))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 8 ltac:(lia)) as HO8. rewrite <- RGSRC in HO8.
assert (UB8 : base_val E (Some (A_OBJ 8)) = rg_src RG)
by (cbn [base_val]; rewrite E249, <- RGSRC; apply unsigned_lit_small; lia).
assert (UB33 : base_val E (Some 33%nat) = rmSA cx i) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_rmf (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_free)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmf. apply pa_entry_st_ok_full.
- unfold rmf_sr. apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. rewrite E340, H25, HH60. rewrite unsigned_lit_small by (rewrite <- HH60; apply pa_val_range).
  rewrite Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- unfold rmf_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) (rxG0 cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact TS.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rmSA cx i) 16 8 (SOff 34 0) (re_buf e1));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact MB.
- apply pairwise_disjoint_of_extents. unfold rmf_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite UB8, UB33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert HO8 HGoff ESA Hi16. clear. intros. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [rmf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E33, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((rmSA cx i) mod 8 = 0).
    { rewrite ESA. pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
      rewrite D. replace (16 * (rxG0 cx / 16) + 56 * Z.of_nat i) with ((2 * (rxG0 cx / 16) + 7 * Z.of_nat i) * 8) by ring.
      apply Z_mod_mult. }
    unfold RMF_PHI, SB, SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rmf_facts f_alias alias_ok]. split; [|exact I].
    apply bv_eq. change (U E (SAlu ALU_ADD (SOff 32 0) (SOff 24 0)) = U E (SOff 33 0)).
    rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 24 _ E24), (U_atom E 33 _ E33) by (unfold AENT; lia).
    cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). rewrite ESA. unfold AENT. reflexivity. }
clear HE.
assert (HBx : U E BxF = SHADOW_OFF) by (unfold BxF; rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxF rmf_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE (rmSA cx i + 16) 8
      HAR1 TIn);
    [lia | change (req_size ATABLE) with 896; lia].
  + exact HBx.
  + rewrite (U_atom E 33 _ E33) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
pose proof HJ0 as HJr.
unfold cfg_at. change (w64 (BASE + A_rr_free)) with (Z_to_bv 64 (BASE + A_rr_free)).
(* 0x83f74 .. 0x83f94: g_src, the slot, the buf field's shadow check (fast path), the buf, the call to free *)
paj_run_tok_x RUN HS HJr SHOK rmf_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rmf_mem Em1.
rewrite Em1 in HJr.
pmkst HS. rewrite Em1, (pal_free B TL).
prreg HS (1%bv : bv 5) QRA. prreg HS (10%bv : bv 5) QA0. prreg HS (25%bv : bv 5) Q25.
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 _ RMF_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (Q25' : getr (ms_regs ms) 25%bv = getr regs1 25%bv).
{ rewrite Q25. change 340%nat with (A_HI 60). rewrite E340, H25, HH60. reflexivity. }
assert (HR : forall r, In r RMF_REGS -> getr (ms_regs ms) r = getr regs1 r).
{ intros r Hr. unfold RMF_REGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [first [exact Q25' | apply HK; cbv; tauto] |]). destruct Hr. }
assert (QSP : spZ (ms_regs ms) = rsp0 cx - RR_FRAME) by (unfold spZ; rewrite (HR 2%bv) by (cbv; tauto); exact Hsp1).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (HR 3%bv) by (cbv; tauto); rewrite Hgp1; exact Hgp).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (HR 4%bv) by (cbv; tauto); rewrite Htp1; exact Htp).
assert (Q8 : getr (ms_regs ms) 8 = w64 (rsp0 cx)) by (rewrite (HR 8%bv) by (cbv; tauto); exact Hs0).
assert (QRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite QRA, unsigned_lit_small by lia; lia).
assert (QS0 : s0Z (ms_regs ms) = rsp0 cx).
{ unfold s0Z. rewrite Q8. apply unsigned_lit_small. lia. }
pose proof HCT as (HCTtop & HCTin).
assert (HCH : chain_pre ly1 (aview SEGS (w_H W1) m1) (ms_regs ms)
  ((rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx)) by (eapply rr_call_chain_pre_ctx; eassumption).
set (ch := (rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx) in HCH.
assert (HINC : In (raZ (ms_regs ms) :: spine ch) CTX_AFREE).
{ unfold ch, spine. cbn [map fst snd]. fold (spine (rxch cx)).
  replace (raZ (ms_regs ms)) with (A_rr_entryP + 436); [exact HCTin|].
  unfold raZ. rewrite QRA, unsigned_lit_small by lia.
  unfold A_rr_entryP, A_rr_entry, A_rr_cpy, AF_fr_relay_remove. lia. }
assert (MOK : mo_ok MT S1 (mo_free MT)).
{ apply (mok_station MT (rxS cx) S1 (tr_cost MT (rtr cx)) spent (mo_free MT) MLAW HMOK HMO);
  [exact (mo_free_nonneg MT MLAW) | exact HSP]. }
assert (HPERM' : Permutation (ablocks B ly1 S1) (rmf_hpblk (re_buf e1) (re_cap e1) ++
  (rxG0 cx, ATABLE) :: (rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx))).
{ rewrite <- EHP. eapply Permutation_trans; [exact HPERM | apply Permutation_middle]. }
assert (HFP : re_buf e1 <> 0 -> In (re_buf e1, re_cap e1) (ablocks B (rxly cx) (rxS cx)) ->
  forall j, 0 <= j < req_size (re_cap e1) -> inFP (rFP cx) (re_buf e1 + j)).
{ intros Hnz Hin0 j Hj. unfold rFP, rr_fp. apply (inFP_ablocks_fp _ (re_buf e1) (re_cap e1) j); [|exact Hj].
  pose proof (Permutation_in _ HPERM0 Hin0) as Hc0.
  assert (Hnr : ~ In (re_buf e1, re_cap e1) (rxrest cx)).
  { intros Hr. pose proof (rmf_nodup _ _ _ _ _ _ HAR1) as ND. apply (Permutation_NoDup HPERM') in ND.
    unfold rmf_hpblk in ND. rewrite (proj2 (Z.eqb_neq (re_buf e1) 0) Hnz) in ND. cbn [app] in ND.
    apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. right.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hr. }
  destruct Hc0 as [Hc0 | Hc0]; [left; exact Hc0|]. right.
  apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [exact Hc0 | exfalso; exact (Hnr Hc0)]. }
(* free (s->buf) at 0x83f94 *)
eapply SRr_bind.
{ apply (rmf_free (G_RR B RG) W1 (ms_regs ms) m1 RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx)
    (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 _ k1 (re_buf e1) (re_cap e1) _ (-96) (getr (ms_regs ms) 1) ch (rxkr cx)
    HJr HPERM').
  - rewrite QA0, E34. reflexivity.
  - rewrite QSP, WF. lia.
  - reflexivity.
  - lia.
  - rewrite WA, WS. lia.
  - exact Q3.
  - exact Q4.
  - reflexivity.
  - rewrite QRA. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCH.
  - exact HINC.
  - exact HRMF.
  - exact HCNF.
  - exact HFP.
  - exact MOK. }
cbv beta. intros W2 c3 Hwle (ly2 & S2 & Hp2 & regs2 & m2 & md2 & -> & HJ2 & HPR2 & HPm2 & HK2 & HM2 & HRM2 & HE2 & HPr2).
(* ---- back at 0x83f98: RRC ---- *)
pose proof HJr as HARm. apply ajournal_gx_AR_x in HARm.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
destruct (rmf_keep ly1 S1 Hp1 W1 m1 _ ly2 S2 Hp2 W2 m2 md2 _ _ (re_buf e1) (re_cap e1) _ HARm HAR2 HPERM' HPm2 HK2 HPr2
  HE2)
  as (KI & KB & KE).
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HJ2 as (_ & _ & (memS2 & HJd2 & _) & _). pose proof HJd2 as (_ & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & LF2 & _).
pose proof HJ0 as (_ & _ & (memS1 & HJd1 & _) & _). pose proof HJd1 as (_ & Hly1 & _ & _ & _ & Hfrs1 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & LF1 & _).
assert (HIN : In (0, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (KR : forall a, rg_rng RG a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (RGIMG a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (KCL : forall a, rmf_cell a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (rmf_cell_img a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (BLK2 : forall b, In b ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
  In b (ablocks B ly2 S2)) by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPm2) Hb)).
assert (KBL : forall bl, (forall b, In b bl -> In b (ablocks B ly2 S2)) -> rmf_bk (abyte_kept W1 m1 W2 m2) bl)
  by (intros bl Hs p n a Hin Ha; exact (KB p n a (Hs _ Hin) Ha)).
assert (KF : forall b, F <= b < F + 64 -> aview SEGS (w_H W2) m2 b = aview SEGS (w_H W1) m1 b).
{ intros b Hb. apply (K4 0 fpos b HIN).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  - intros (Hnz & Hr). destruct HBUF as [(_ & Hb0) | (_ & Hin & _)]; [exact (Hnz Hb0)|].
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ 0 fpos HAR1 Hin HIN) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 0) with 64 in Hd. lia. }
apply KC. unfold RRC.
exists regs2, ly2, S2, Hp2, m2, md2, (k1 + 1), F, FL, e1, h1, ev, LB, c2, O2, cap2, out2,
  (entry_bytes (entry_cleared e1)).
(* the return point *)
split.
{ unfold cfg_at, w64, A_rr_cpy, AF_fr_relay_remove. rewrite QRA. reflexivity. }
(* the registers *)
assert (HR2 : forall r, In r RMF_REGS -> getr regs2 r = getr regs1 r)
  by (intros r Hr; rewrite (rmf_ap _ _ r HPR2 Hr); exact (HR r Hr)).
split.
{ split; [unfold rregs_held, rregs_base, spZ; rewrite !HR2 by (cbv; tauto); exact HRH|].
  split; [rewrite HR2 by (cbv; tauto); exact H25|].
  split; [rewrite HR2 by (cbv; tauto); exact H24|].
  split; [exact HFD0|]. split; [exact Hi | exact Hfd]. }
(* RLIVE *)
split.
{ exists fpos. split; [exact HJ2|].
  split; [eapply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low);
    [exact HJ2 | exact HROMO | exact PSTR | exact HROM0]|].
  split; [intros a Hi' Ho He Hp; apply HPr2; [exact Hi' | exact Ho | exact He | apply HPK1; assumption]|].
  split.
  { split; [unfold frame_addr in *; rewrite LF2, <- LF1; exact EF|].
    split; [unfold flag_addr in *; rewrite LF2, <- LF1; exact EFL|].
    split.
    - unfold arm in *. apply (rmf_vm_kept (w_H W1) (w_H W2) m1 m2 _ _ _ HFL56). intros b Hb. apply KF. cbn in Hb. lia.
    - intros j Hj. pose proof (HSV j Hj) as V. unfold arm in *. apply (rmf_vm_kept (w_H W1) (w_H W2) m1 m2 _ _ _ V).
      intros b Hb. apply K1; [| rewrite WF in *; lia].
      rewrite WS in Hslo. rewrite WF in Hb. lia. }
  split.
  { eapply alock_at_kept; [exact HLK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. lia. }
  { eapply awake_at_kept; [exact HWK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. lia. } }
(* drain's relation and the harness source *)
split.
{ unfold rmdrel in HDR |- *. destruct (rmopen cx i) eqn:Eo; [|exact HDR].
  destruct HDR as (HDR & HAS). split; [exact HDR|].
  assert (Heof : re_eof (rnth cx i) = 0) by (unfold rmopen in Eo; apply Z.eqb_eq; exact Eo).
  pose proof (proj1 (HSRC0 i Hi Hfd Heof)) as Hj4.
  assert (HSB : forall b, In b (asrc_blks h1) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply BLK2. right. apply in_or_app. right. apply in_or_app. left. unfold rmsrc. rewrite Eo. exact Hb. }
  apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ h1 HAS); [|exact HSB].
  apply (rmf_fz_asrc _ ly1 S1 W1 m1 _ h1 HAS); [|exact (KBL _ HSB)].
  intros a Ha. apply KR. unfold rg_rng, rmHA, ASRC in *. lia. }
(* the table *)
split.
{ split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; lia | exact TS]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; lia | exact TSW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; lia | exact TN]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; lia | exact TNW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; cbn in Hx; lia | exact TC]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; lia | exact TCW]|].
  split; [apply BLK2; left; reflexivity|].
  split; [exact TXL|].
  split.
  { exists tail. split; [exact TTL|]. apply (akept_garr8 W1 m1); [|exact TG]. intros x Hx. rewrite LTAB in Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity | change (req_size ATABLE) with 896; lia]. }
  split.
  { apply (akept_awr W1 m1); [|exact TSA]. intros x Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity|].
    change (req_size ATABLE) with 896. rewrite ESA in Hx. unfold AENT in Hx. lia. }
  rewrite Forall_forall in TOK |- *. intros e He.
  assert (HEB : forall b, In b (aentry_blks e) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply BLK2. right. apply in_or_app. left. unfold rmOB. apply in_concat.
    exists (aentry_blks e). split; [apply in_map; exact He | exact Hb]. }
  apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 e (TOK e He)); [|exact HEB].
  exact (rmf_fz_aentry _ ly1 S1 W1 m1 e (TOK e He) (KBL _ HEB)). }
split; [exact HSL|].
(* the stream *)
split.
{ assert (HOB : forall b, In b (aout_blks cap2 out2) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply BLK2. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT); [|exact HOB].
  apply (rmf_fz_aout _ ly1 S1 W1 m1 _ _ _ _ _ _ HOUT); [|exact (KBL _ HOB)].
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOE & _).
  intros r Hr a Ha. unfold aout_fp in Hr. cbn [Z.eqb] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]; cbn [fst snd] in Ha;
  try (apply KCL; unfold rmf_cell; lia).
  apply KE; [exact Ha|]. unfold arm in HOE.
  replace a with (as_errno B + (a - as_errno B)) by lia. apply (rmf_view_some (w_H W1) m1 _ 4 _ _ HOE). lia. }
split; [exact HPm2|].
(* g_s *)
split.
{ intros a Ha Hj. apply (rmf_abk_trans _ W1 _ _ m1 _ a (HGS a Ha Hj)). apply KR. unfold rg_rng. lia. }
(* the meter: the whole trace; the room round: kr left (the free's post) *)
split.
{ apply (mle_weaken MT (rxS cx) S2 (spent + mo_free MT)); [exact MLAW | | exact HSP].
  exact (mle_station MT (rxS cx) S1 S2 spent (mo_free MT) MLAW HMO HM2). }
exact HRM2.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the FREE hop at a world relation R, stated as W_rr_match_cx.v hop_free_stmt_xR
   (RRF_xR / RRC_xR over RLIVE_xR's journal ajournal_gx_xR .. R; the step relation YA0nH.SRrG SEGS R).  rmf_free_xR is
   rmf_free over the R free rules (W_journal_x.v afree_cf_rule_c_xR / afree_null_cf_rule_c_xR .. RO CTX_AFREE R) in
   W_gestures_end.v gse_free_xR's form: their call-boundary premise RO at the call memory comes from the call state's
   ARx (RO_ARx; part 3c removed their memnorm premise), the stack room from aj_stack_room_xR, the repack from
   ajournal_gx_pack_xR.  The run is the G run (paj_run_x_xG, paj_run_tok_xR), the chain W_rr_m_kit.v
   rr_call_chain_pre_ctx_xR; the rest is rr_m_free's proof.  No step reads the world relation across the free (each
   kept fact moves by the rule's acall_kept / apres_kept / errno view at W2), so the journal-free helpers (rmf_keep,
   rmf_cell_img, rmf_fz_* ..) serve both forms.  rr_m_free above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Let RUN_R := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].

(* :331 rmf_free *)
Lemma rmf_free_xR : forall G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l (o : Z) raw ch
  (kr : nat),
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
Permutation (ablocks B lyc Sc) (rmf_hpblk hp kh ++ l) ->
getr regsT 10 = w64 hp ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
rp_RM RP Sc (1 + kr) ->
cnt_ok RP (ablocks B lyc Sc) ->
(hp <> 0 -> In (hp, kh) (ablocks B ly S) -> forall i, 0 <= i < req_size kh -> inFP FP (hp + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_xR (SK := SK) SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) l /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => hp <> 0 /\ hp <= a < hp + req_size kh) /\
mo_le MT Sc S2 (mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
intros G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l o raw ch kr
  (H0 & H1 & (memS & HJi & Hag) & Hout) HP H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCT HRM HCNT HFP MOK.
rewrite !Z.add_0_r in HJi.
pose proof (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Hsp Hst) as Hroom.
(* the R rules' call-boundary premise at the call memory memT, from the call state's ARx (the inner journal's first
   conjunct) *)
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
unfold rmf_hpblk in HP. destruct (Z.eqb_spec hp 0) as [Hz | Hnz].
- subst hp. cbn [app] in HP. eapply SRrG_mono.
  { exact (AFREEN_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k o raw ch kr HJi H10 Hsp Hal Hneg Hst
      Hroom Hgp Htp Hra Hraw Hch HRO HCT HRM HCNT MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPm & _ & HK & HM & HRM2 & HE & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|]. split; [eapply Permutation_trans; [exact HPm | exact HP]|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a []]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hpa. apply HPr; [exact Hi | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | exact Hpa].
- assert (Hin : In (hp, kh) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
  eapply SRrG_mono.
  { apply (AFREE_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k hp kh o raw ch kr HJi Hin H10 Hsp Hal
      Hneg Hst Hroom Hgp Htp Hra Hraw Hch HRO HCT HRM HCNT); [intros Hin0 i Hi; exact (HFP Hnz Hin0 i Hi) | exact MOK]. }
  cbv beta.
  intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & _ & HK & HM & HRM2 & HE
    & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|].
  split; [rewrite E2; apply Permutation_sym; apply (@Permutation_cons_app_inv _ l l1 l2 (hp, kh)); rewrite <- E1;
    apply Permutation_sym; exact HP|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a Ha; split; [exact Hnz | exact Ha]]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hpa. apply HPr; [exact Hi | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (rmf_not_owned _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hpa].
  intros Hr. pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc W memT mdc hp kh (proj1 HJi) Hin) as Hoff.
  pose proof (pa_img_range a Hi). unfold off_img in Hoff. lia.
Qed.

(* :614 rr_m_free *)
Theorem rr_m_free_xR : hop_free_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
unfold hop_free_stmt_xR. intros cx i W1 c1 HB HCT HF KC.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (WA : ASTACK = 16384) by reflexivity.
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK0 & HWAKE0 & HREL0 & HOUT0 & HROM0 & HSRC0 & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres.
destruct HF as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & spent &
  -> & HMH & HLV & HDR & HP1 & HP2 & HCASE & HTB & HSL & HOUT & HPERM & HGS & HMO & HSP & HRMF & HCNF).
destruct HMH as (HRH & H25 & H24 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp1 & Hgp1 & Htp1 & Hs0 & Hs1 & Hs2 & Hs4 & Hs5 & Hs6 & Hs10 & Hs11) & Hs3 & Hs7).
pose proof HLV as (fpos & HJ0 & HROM1 & HPK1 & HFR & HLK & HWK).
pose proof HFR as (EF & EFL & HFL56 & HSV).
destruct HTB as (TS & TSW & TN & TNW & TC & TCW & TIn & TXL & (tail & TTL & TG) & TSA & TOK).
(* ---- facts at the cut ---- *)
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ0).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as (HG16 & HG4096 & HGceil & HGia & _ & _).
change (req_size ATABLE) with 896 in HGceil, HGia.
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as HGoff.
change (req_size ATABLE) with 896 in HGoff. unfold off_img in HGoff.
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & RL16 & _ & _ & ROK & RND).
assert (Hpads : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx))
  by (eapply Forall_impl; [|exact ROK]; intros e (_ & _ & Q1 & Q2 & _); split; assumption).
assert (ESA : rmSA cx i = rxG0 cx + 56 * Z.of_nat i) by reflexivity.
assert (LPRE : length (rmTpre cx i) = (56 * i)%nat).
{ unfold rmTpre. rewrite rmf_concat_len, length_firstn by (rewrite <- (firstn_skipn i (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [Hp _]; exact Hp). lia. }
assert (LPOST : length (rmTpost cx i) = (56 * (length (rxes cx) - S i))%nat).
{ unfold rmTpost. rewrite rmf_concat_len, length_skipn by (rewrite <- (firstn_skipn (S i) (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [_ Hp]; exact Hp). lia. }
assert (LX : length (entry_bytes (entry_cleared e1)) = 56%nat) by (apply rmf_eb_len; [exact HP1 | exact HP2]).
assert (LTAB : Z.of_nat (length (bzs (rmTpre cx i ++ entry_bytes (entry_cleared e1) ++ rmTpost cx i ++ tail))) = 896).
{ rewrite rmf_bzs_len, !length_app, LPRE, LX, LPOST. unfold rN, AENT, ATABLE in TTL. lia. }
assert (HBUF : (re_cap e1 = 0 /\ re_buf e1 = 0) \/
  (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\ 4096 <= re_buf e1 /\
   re_buf e1 + req_size (re_cap e1) <= alloc_ceiling)).
{ destruct HCASE as [HC0 | HCP]; [left; exact HC0|right].
  assert (Hin : In (re_buf e1, re_cap e1) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. right. apply in_or_app. left. unfold rmbuf.
    rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)). left. reflexivity. }
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hin) as (_ & Hb4096 & Hbceil & _).
  split; [exact HCP|]. split; [exact Hin|]. split; lia. }
assert (EHP : rmbuf e1 = rmf_hpblk (re_buf e1) (re_cap e1)).
{ unfold rmbuf, rmf_hpblk. destruct HBUF as [(Hc & Hb) | (Hc & _ & Hb & _)].
  - rewrite Hc, Hb. reflexivity.
  - rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)), (proj2 (Z.eqb_neq (re_buf e1) 0) ltac:(lia)). reflexivity. }
assert (HBR : 0 <= re_buf e1 < 2 ^ 64).
{ destruct HBUF as [(_ & Hb) | (Hc & _ & Hb & Hb2)]; [rewrite Hb; lia|].
  pose proof (req_size_pos (re_cap e1) ltac:(lia)) as [Hr1 _]. lia. }
assert (MB : val_mem SEGS (arm W1 m1) (rmSA cx i + 16) 8 (re_buf e1)).
{ pose proof (rmf_buf_cell (arm W1 m1) (rxG0 cx) (rmTpre cx i) (rmTpost cx i ++ tail) e1 TG HP1 HBR) as M.
  rewrite LPRE in M. rewrite ESA. replace (rxG0 cx + 56 * Z.of_nat i + 16) with (rxG0 cx + Z.of_nat (56 * i) + 16) by lia.
  exact M. }
assert (Hi16 : (S i <= 16)%nat) by lia.
(* ---- the symbolic state at 0x83f74 ---- *)
remember (Eimg (Ereg regs1 (rmf_extra (rxG0 cx) (rmSA cx i) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmf_extra (rxG0 cx) (rmSA cx i) (re_buf e1))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact Hs6).
assert (E24 : ew E 24 = Z_to_bv 64 (AENT * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rmSA cx i))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E249 : ew E (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E340 : ew E (A_HI 60) = Z_to_bv 64 (VAL (A_HI 60))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 8 ltac:(lia)) as HO8. rewrite <- RGSRC in HO8.
assert (UB8 : base_val E (Some (A_OBJ 8)) = rg_src RG)
by (cbn [base_val]; rewrite E249, <- RGSRC; apply unsigned_lit_small; lia).
assert (UB33 : base_val E (Some 33%nat) = rmSA cx i) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_rmf (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_free)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmf. apply pa_entry_st_ok_full.
- unfold rmf_sr. apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. rewrite E340, H25, HH60. rewrite unsigned_lit_small by (rewrite <- HH60; apply pa_val_range).
  rewrite Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- unfold rmf_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) (rxG0 cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact TS.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rmSA cx i) 16 8 (SOff 34 0) (re_buf e1));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact MB.
- apply pairwise_disjoint_of_extents. unfold rmf_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite UB8, UB33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert HO8 HGoff ESA Hi16. clear. intros. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [rmf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E33, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((rmSA cx i) mod 8 = 0).
    { rewrite ESA. pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
      rewrite D. replace (16 * (rxG0 cx / 16) + 56 * Z.of_nat i) with ((2 * (rxG0 cx / 16) + 7 * Z.of_nat i) * 8) by ring.
      apply Z_mod_mult. }
    unfold RMF_PHI, SB, SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rmf_facts f_alias alias_ok]. split; [|exact I].
    apply bv_eq. change (U E (SAlu ALU_ADD (SOff 32 0) (SOff 24 0)) = U E (SOff 33 0)).
    rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 24 _ E24), (U_atom E 33 _ E33) by (unfold AENT; lia).
    cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). rewrite ESA. unfold AENT. reflexivity. }
clear HE.
assert (HBx : U E BxF = SHADOW_OFF) by (unfold BxF; rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxF rmf_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE (rmSA cx i + 16) 8
      HAR1 TIn);
    [lia | change (req_size ATABLE) with 896; lia].
  + exact HBx.
  + rewrite (U_atom E 33 _ E33) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
pose proof HJ0 as HJr.
unfold cfg_at. change (w64 (BASE + A_rr_free)) with (Z_to_bv 64 (BASE + A_rr_free)).
(* 0x83f74 .. 0x83f94: g_src, the slot, the buf field's shadow check (fast path), the buf, the call to free *)
paj_run_tok_xR RUN_R HS HJr SHOK rmf_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rmf_mem Em1.
rewrite Em1 in HJr.
pmkst HS. rewrite Em1, (pal_free B TL).
prreg HS (1%bv : bv 5) QRA. prreg HS (10%bv : bv 5) QA0. prreg HS (25%bv : bv 5) Q25.
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 _ RMF_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (Q25' : getr (ms_regs ms) 25%bv = getr regs1 25%bv).
{ rewrite Q25. change 340%nat with (A_HI 60). rewrite E340, H25, HH60. reflexivity. }
assert (HR : forall r, In r RMF_REGS -> getr (ms_regs ms) r = getr regs1 r).
{ intros r Hr. unfold RMF_REGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [first [exact Q25' | apply HK; cbv; tauto] |]). destruct Hr. }
assert (QSP : spZ (ms_regs ms) = rsp0 cx - RR_FRAME) by (unfold spZ; rewrite (HR 2%bv) by (cbv; tauto); exact Hsp1).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (HR 3%bv) by (cbv; tauto); rewrite Hgp1; exact Hgp).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (HR 4%bv) by (cbv; tauto); rewrite Htp1; exact Htp).
assert (Q8 : getr (ms_regs ms) 8 = w64 (rsp0 cx)) by (rewrite (HR 8%bv) by (cbv; tauto); exact Hs0).
assert (QRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite QRA, unsigned_lit_small by lia; lia).
assert (QS0 : s0Z (ms_regs ms) = rsp0 cx).
{ unfold s0Z. rewrite Q8. apply unsigned_lit_small. lia. }
pose proof HCT as (HCTtop & HCTin).
assert (HCH : chain_pre ly1 (aview SEGS (w_H W1) m1) (ms_regs ms)
  ((rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx)) by (eapply rr_call_chain_pre_ctx_xR; eassumption).
set (ch := (rsp0 cx, raZ (rxregs cx), s0Z (rxregs cx)) :: rxch cx) in HCH.
assert (HINC : In (raZ (ms_regs ms) :: spine ch) CTX_AFREE).
{ unfold ch, spine. cbn [map fst snd]. fold (spine (rxch cx)).
  replace (raZ (ms_regs ms)) with (A_rr_entryP + 436); [exact HCTin|].
  unfold raZ. rewrite QRA, unsigned_lit_small by lia.
  unfold A_rr_entryP, A_rr_entry, A_rr_cpy, AF_fr_relay_remove. lia. }
assert (MOK : mo_ok MT S1 (mo_free MT)).
{ apply (mok_station MT (rxS cx) S1 (tr_cost MT (rtr cx)) spent (mo_free MT) MLAW HMOK HMO);
  [exact (mo_free_nonneg MT MLAW) | exact HSP]. }
assert (HPERM' : Permutation (ablocks B ly1 S1) (rmf_hpblk (re_buf e1) (re_cap e1) ++
  (rxG0 cx, ATABLE) :: (rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx))).
{ rewrite <- EHP. eapply Permutation_trans; [exact HPERM | apply Permutation_middle]. }
assert (HFP : re_buf e1 <> 0 -> In (re_buf e1, re_cap e1) (ablocks B (rxly cx) (rxS cx)) ->
  forall j, 0 <= j < req_size (re_cap e1) -> inFP (rFP cx) (re_buf e1 + j)).
{ intros Hnz Hin0 j Hj. unfold rFP, rr_fp. apply (inFP_ablocks_fp _ (re_buf e1) (re_cap e1) j); [|exact Hj].
  pose proof (Permutation_in _ HPERM0 Hin0) as Hc0.
  assert (Hnr : ~ In (re_buf e1, re_cap e1) (rxrest cx)).
  { intros Hr. pose proof (rmf_nodup _ _ _ _ _ _ HAR1) as ND. apply (Permutation_NoDup HPERM') in ND.
    unfold rmf_hpblk in ND. rewrite (proj2 (Z.eqb_neq (re_buf e1) 0) Hnz) in ND. cbn [app] in ND.
    apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. right.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hr. }
  destruct Hc0 as [Hc0 | Hc0]; [left; exact Hc0|]. right.
  apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [exact Hc0 | exfalso; exact (Hnr Hc0)]. }
(* free (s->buf) at 0x83f94 *)
eapply (SRrG_bind SEGS R R_trans).
{ apply (rmf_free_xR (G_RR B RG) W1 (ms_regs ms) m1 RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx)
    (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 _ k1 (re_buf e1) (re_cap e1) _ (-96) (getr (ms_regs ms) 1) ch (rxkr cx)
    HJr HPERM').
  - rewrite QA0, E34. reflexivity.
  - rewrite QSP, WF. lia.
  - reflexivity.
  - lia.
  - rewrite WA, WS. lia.
  - exact Q3.
  - exact Q4.
  - reflexivity.
  - rewrite QRA. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCH.
  - exact HINC.
  - exact HRMF.
  - exact HCNF.
  - exact HFP.
  - exact MOK. }
cbv beta. intros W2 c3 HRW (ly2 & S2 & Hp2 & regs2 & m2 & md2 & -> & HJ2 & HPR2 & HPm2 & HK2 & HM2 & HRM2 & HE2 & HPr2).
(* ---- back at 0x83f98: RRC_xR ---- *)
pose proof HJr as HARm. apply ajournal_gx_AR_xR in HARm.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
destruct (rmf_keep ly1 S1 Hp1 W1 m1 _ ly2 S2 Hp2 W2 m2 md2 _ _ (re_buf e1) (re_cap e1) _ HARm HAR2 HPERM' HPm2 HK2 HPr2
  HE2)
  as (KI & KB & KE).
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HJ2 as (_ & _ & (memS2 & HJd2 & _) & _). pose proof HJd2 as (_ & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & LF2 & _).
pose proof HJ0 as (_ & _ & (memS1 & HJd1 & _) & _). pose proof HJd1 as (_ & Hly1 & _ & _ & _ & Hfrs1 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & LF1 & _).
assert (HIN : In (0, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (KR : forall a, rg_rng RG a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (RGIMG a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (KCL : forall a, rmf_cell a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (rmf_cell_img a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (BLK2 : forall b, In b ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
  In b (ablocks B ly2 S2)) by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPm2) Hb)).
assert (KBL : forall bl, (forall b, In b bl -> In b (ablocks B ly2 S2)) -> rmf_bk (abyte_kept W1 m1 W2 m2) bl)
  by (intros bl Hs p n a Hin Ha; exact (KB p n a (Hs _ Hin) Ha)).
assert (KF : forall b, F <= b < F + 64 -> aview SEGS (w_H W2) m2 b = aview SEGS (w_H W1) m1 b).
{ intros b Hb. apply (K4 0 fpos b HIN).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  - intros (Hnz & Hr). destruct HBUF as [(_ & Hb0) | (_ & Hin & _)]; [exact (Hnz Hb0)|].
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ 0 fpos HAR1 Hin HIN) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 0) with 64 in Hd. lia. }
apply KC. unfold RRC_xR.
exists regs2, ly2, S2, Hp2, m2, md2, (k1 + 1), F, FL, e1, h1, ev, LB, c2, O2, cap2, out2,
  (entry_bytes (entry_cleared e1)).
(* the return point *)
split.
{ unfold cfg_at, w64, A_rr_cpy, AF_fr_relay_remove. rewrite QRA. reflexivity. }
(* the registers *)
assert (HR2 : forall r, In r RMF_REGS -> getr regs2 r = getr regs1 r)
  by (intros r Hr; rewrite (rmf_ap _ _ r HPR2 Hr); exact (HR r Hr)).
split.
{ split; [unfold rregs_held, rregs_base, spZ; rewrite !HR2 by (cbv; tauto); exact HRH|].
  split; [rewrite HR2 by (cbv; tauto); exact H25|].
  split; [rewrite HR2 by (cbv; tauto); exact H24|].
  split; [exact HFD0|]. split; [exact Hi | exact Hfd]. }
(* RLIVE_xR *)
split.
{ exists fpos. split; [exact HJ2|].
  split; [eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low);
    [exact HJ2 | exact HROMO | exact PSTR | exact HROM0]|].
  split; [intros a Hi' Ho He Hp; apply HPr2; [exact Hi' | exact Ho | exact He | apply HPK1; assumption]|].
  split.
  { split; [unfold frame_addr in *; rewrite LF2, <- LF1; exact EF|].
    split; [unfold flag_addr in *; rewrite LF2, <- LF1; exact EFL|].
    split.
    - unfold arm in *. apply (rmf_vm_kept (w_H W1) (w_H W2) m1 m2 _ _ _ HFL56). intros b Hb. apply KF. cbn in Hb. lia.
    - intros j Hj. pose proof (HSV j Hj) as V. unfold arm in *. apply (rmf_vm_kept (w_H W1) (w_H W2) m1 m2 _ _ _ V).
      intros b Hb. apply K1; [| rewrite WF in *; lia].
      rewrite WS in Hslo. rewrite WF in Hb. lia. }
  split.
  { eapply alock_at_kept; [exact HLK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. lia. }
  { eapply awake_at_kept; [exact HWK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. lia. } }
(* drain's relation and the harness source *)
split.
{ unfold rmdrel in HDR |- *. destruct (rmopen cx i) eqn:Eo; [|exact HDR].
  destruct HDR as (HDR & HAS). split; [exact HDR|].
  assert (Heof : re_eof (rnth cx i) = 0) by (unfold rmopen in Eo; apply Z.eqb_eq; exact Eo).
  pose proof (proj1 (HSRC0 i Hi Hfd Heof)) as Hj4.
  assert (HSB : forall b, In b (asrc_blks h1) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply BLK2. right. apply in_or_app. right. apply in_or_app. left. unfold rmsrc. rewrite Eo. exact Hb. }
  apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 _ h1 HAS); [|exact HSB].
  apply (rmf_fz_asrc _ ly1 S1 W1 m1 _ h1 HAS); [|exact (KBL _ HSB)].
  intros a Ha. apply KR. unfold rg_rng, rmHA, ASRC in *. lia. }
(* the table *)
split.
{ split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; lia | exact TS]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; lia | exact TSW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; lia | exact TN]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; lia | exact TNW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; cbn in Hx; lia | exact TC]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; lia | exact TCW]|].
  split; [apply BLK2; left; reflexivity|].
  split; [exact TXL|].
  split.
  { exists tail. split; [exact TTL|]. apply (akept_garr8 W1 m1); [|exact TG]. intros x Hx. rewrite LTAB in Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity | change (req_size ATABLE) with 896; lia]. }
  split.
  { apply (akept_awr W1 m1); [|exact TSA]. intros x Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity|].
    change (req_size ATABLE) with 896. rewrite ESA in Hx. unfold AENT in Hx. lia. }
  rewrite Forall_forall in TOK |- *. intros e He.
  assert (HEB : forall b, In b (aentry_blks e) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply BLK2. right. apply in_or_app. left. unfold rmOB. apply in_concat.
    exists (aentry_blks e). split; [apply in_map; exact He | exact Hb]. }
  apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 e (TOK e He)); [|exact HEB].
  exact (rmf_fz_aentry _ ly1 S1 W1 m1 e (TOK e He) (KBL _ HEB)). }
split; [exact HSL|].
(* the stream *)
split.
{ assert (HOB : forall b, In b (aout_blks cap2 out2) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply BLK2. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT); [|exact HOB].
  apply (rmf_fz_aout _ ly1 S1 W1 m1 _ _ _ _ _ _ HOUT); [|exact (KBL _ HOB)].
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOE & _).
  intros r Hr a Ha. unfold aout_fp in Hr. cbn [Z.eqb] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]; cbn [fst snd] in Ha;
  try (apply KCL; unfold rmf_cell; lia).
  apply KE; [exact Ha|]. unfold arm in HOE.
  replace a with (as_errno B + (a - as_errno B)) by lia. apply (rmf_view_some (w_H W1) m1 _ 4 _ _ HOE). lia. }
split; [exact HPm2|].
(* g_s *)
split.
{ intros a Ha Hj. apply (rmf_abk_trans _ W1 _ _ m1 _ a (HGS a Ha Hj)). apply KR. unfold rg_rng. lia. }
(* the meter: the whole trace; the room round: kr left (the free's post) *)
split.
{ apply (mle_weaken MT (rxS cx) S2 (spent + mo_free MT)); [exact MLAW | | exact HSP].
  exact (mle_station MT (rxS cx) S1 S2 spent (mo_free MT) MLAW HMO HM2). }
exact HRM2.
Qed.
End wR.

End c.
End b.
End a.
