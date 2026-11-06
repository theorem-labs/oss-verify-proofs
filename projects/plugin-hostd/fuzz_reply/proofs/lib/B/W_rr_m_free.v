(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the FREE hop of the MATCH segment of the IMAGE-B walk of fuzz_reply's
   relay_remove (lib/B/W_rr_match_cx.v hop_free_stmt, fuzz_reply.asan-ubsan): RRF i 0x84318 -> ld a0,-1288(s4)
   (g_src); a1 = a0 + s3 (&g_src[i]); the UBSan traps 0x84320 (pointer overflow), 0x84330 (null consistency), 0x84334
   (g_src null), 0x84340 (slot alignment), none taken; the shadow check of the slot's buf field 0x84344-0x84354 (the
   report 0x84404 is not taken: an 8-byte aligned load's check has no slow path); ld a0,16(a1); jal free 0x8435c
   (AFREE when the entry has a buffer, cap > 0; AFREEN, s->buf = NULL, cap = 0) -> RRC i 0x84360.

   Proves no function (kind: segment lemma of the B walk).  The image-A twin is lib/A/W_rr_m_free.v on
   a working branch (same statement shape, A's instruction run and register map).

   Where each part comes from:
   - rmf_buf_cell, rmf_writable_view, rmf_view_some, rmf_vm_kept, rmf_not_owned, rmf_hpblk, rmf_free, rmf_keep,
     rmf_cell, rmf_nerr, rmf_cell_img, rmf_fz / rmf_bk / rmf_bk_sub / rmf_fz_alist / rmf_fz_asrc / rmf_fz_aentry /
     rmf_fz_aout, rmf_abk_trans, rmf_ap, the Ltacs rmf_in / rmf_exists / rmf_mem, rmf_bzs_len, rmf_text_rec_len,
     rmf_concat_trec_len, rmf_key_ptrs_len, rmf_zall_In: the A twin's, verbatim but the import paths; the A twin's
     byte-list lemmas, rmf_writable_kept, rmf_nodup and rmf_aout_fp_cases are the kit's (lib/B/W_rr_m_kit.v)
     rm_nth_le_bytes / rm_eb_len / rm_concat_len / rm_garr8_le, rr_writable2, rm_ablocks_nodup, rm_aout_fp_cases.
   - the call chain free's rule asks for: the kit's rr_chain_pre_fd (image B keeps fd in s0: the chain is empty), so
     the _c rules' context is the closed singleton [ra], ra = entry + 0x164: the Section's HCTX_rr_free.
   - rr_m_free: the A twin's, less the fake frame (image B's RLIVE owns no frame: own = [], the saved registers are
     rr_saved), over B's run and B's registers (s2 = the shadow offset, s3 = 56 i, s4 = g_src's register image).
   NEW for image B:
   - the seat at 0x84318: s4 is NOT pinned; g_src's cell is a region based on the s4 register's own atom 20 at
     offsets -1288 .. -1280 (`ld a0,-1288(s4)` is a plain listing word, not a PLdHi), whose chunk is the G0 atom 32;
     the slot &g_src[i] is atom 33, with both sum orders G0 + s3 / s3 + G0 in f_alias (W_traps.v seat recipe R2),
     and atoms 32 / 33 carry R1's pointer fact (al2 4 / 3), so the runner decides the null and alignment traps;
   - the trap edges: the runner leaves ONE branch case, 0x84320 `bltu a1,a0` (pointer overflow), closed by
     W_traps.v trap_ptr_wrap_atom (G0 + 56 i does not wrap: G0 + 896 <= alloc_ceiling); it decides 0x84330 (null
     consistency), 0x84334 (g_src null) and 0x84340 (slot alignment) itself from the atom facts. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (lane Rrm, the image-A twin a Theorem Labs lane
   f4cd818e98d lib/A/W_rr_m_free.v): FREE over ANY allocator relation ARx, in place (Section c is
   W_relay_remove_cx.v's generic block, as in W_rr_m_kit.v): the journal ajournal_gx_x with the head sets, the laws'
   and block twins (alx_blocks, alx_owned_image, sep_blocks_x, range_addressable_of_block_hp0_x,
   ajournal_gx_rom_view_x with PSTR), RUN = paj_run_x_x with paj_run_tok_x; rmf_free over the _c_x free rules (the
   stack room by aj_stack_room_x), still with AFREE's own footprint premise.  The room round: the free is applied at
   kr := rxkr cx with RRF's rp_RM RP S1 (1 + rxkr cx) and cnt_ok RP (ablocks B ly1 S1) (the hop only loads and checks
   shadow before the jal, so RRF's state is the call's); the rule's post rp_RM RP S2 (rxkr cx) is RRC's last
   conjunct.  Image B against the A twin: the journal is at RR_STK_x (W_contract_x.v: 128 bytes above RR_STK; A:
   RR_STK), RLIVE owns no frame (own = [], the saved registers rr_saved; A: the fake frame, sep_block_frame_x), the
   call chain is the kit's rr_chain_pre_fd (A: rr_call_chain_pre_ctx), rmf_nodup is the kit's rm_ablocks_nodup
   (already over ARx), and a block's off-image fact is rmf_blk_off_img at image B's top 0x5fc000 (the kit's
   blk_off_imgP_x states the shared core's off_img at image A's top 0x5fb000; the AR text read W_kit.v blk_off_imgP at
   lib/B/YCbq.v's). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_remove_cx W_rr_match_cx W_rr_m_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
(* route R (the Section wR below) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Notation rmf_le8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Notation rmf_le4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.

(* ------------------------------------------------------------------ byte lists (the A twin's) *)
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
(* the run's awr_ok_x obligation over the two read-only regions of the seat *)
Ltac rmf_awr :=
apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia|];
apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil].

(* the registers the run does not write (it writes a0 .. a3 and ra): every callee-saved register *)
Definition RMF_KEPT : list (bv 5) := [21; 22; 23; 24; 25; 26; 27; 2; 3; 4; 8; 9; 18; 19; 20]%bv.
Lemma rmf_hi_in : forall r : bv 5, 21 <= bv_unsigned r <= 27 -> In r RMF_KEPT.
Proof.
intros r Hr. unfold RMF_KEPT. cbn [In].
assert (Hc : bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/
  bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
destruct Hc as [E|[E|[E|[E|[E|[E|E]]]]]];
[left | right; left | do 2 right; left | do 3 right; left | do 4 right; left | do 5 right; left | do 6 right; left];
apply bv_eq; rewrite E; reflexivity.
Qed.
Lemma rmf_ap : forall r1 r2 (r : bv 5), aregs_preserved r1 r2 -> In r RMF_KEPT -> getr r2 r = getr r1 r.
Proof.
intros r1 r2 r H Hr. pose proof (H (bv_unsigned r)) as E. rewrite Z_to_bv_bv_unsigned in E. apply E.
unfold acallee_saved. unfold RMF_KEPT in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
     change (bv_unsigned x) with v end; lia |]).
destruct Hr.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

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
apply rm_garr8_le; [|exact Hb].
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

(* ---- The seat at 0x84318 (B text base 0x82344; AF_fr_relay_remove = 0x1eb8).
   a0 .. a3 are free; s2 = the shadow offset (atom 18), s3 = 56 i (atom 19), s4 = g_src's register image (atom 20,
   NOT pinned): g_src's cell is the region based on atom 20 at -1288 .. -1280, holding G0 (atom 32); atom 33 =
   &g_src[i] (the alias G0 + s3, both orders), atom 34 = the slot's buf field.  The shadow entry over the slot's buf
   field takes the 8-byte check's fast path. *)
Definition RMF_PHI : Z := 140737479966720.
Definition BxF : sv := SOff 18 0.
Definition rmf_regions : smem :=
[ YP09.mkRegion (Some 20%nat) (-1288) (-1280) (-1288) (-1288) [YP09.mkChunk (-1288) (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 33%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 34 0))] ].
Definition rmf_facts : facts :=
mkFacts [ (18%nat, mkAF SB SB 0); (32%nat, mkAF 4096 RMF_PHI 4); (33%nat, mkAF 4096 RMF_PHI 3) ] []
  [ (SAlu ALU_ADD (SOff 32 0) (SOff 19 0), SOff 33 0); (SAlu ALU_ADD (SOff 19 0) (SOff 32 0), SOff 33 0) ].
Definition ss_rmf : sstate := mkSS A_rr_free sr_atoms rmf_regions None rmf_facts.
Definition rmf_SH : list shent := [ mkSHE 33 16 24 ].
Definition rmf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rmf_extra (g sa bf : Z) : list word := map (Z_to_bv 64) [g; sa; bf].

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL); image B's closed singleton row) *)
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

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ------------------------------------------------------------------ journal and allocator helpers *)
Lemma rmf_not_owned : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho.
exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown).
Qed.
(* W_kit_x.v blk_off_imgP_x's proof at image B's top 0x5fc000 (IMGC's; lib/B/YCbq.v IMG_TOP_B), its off_img written
   out: the kit's blk_off_imgP_x states the shared core's off_img (Reusable/YCbq.v, image A's top 0x5fb000), while the
   AR text read W_kit.v blk_off_imgP at lib/B/YCbq.v's off_img (W_cshe_hd.v cshe_blk_off_img, over ARx) *)
Lemma rmf_blk_off_img : forall ly S Hp (W : world SEGS) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n <= 0x10000 \/ 0x5fc000 <= p.
Proof.
intros ly S Hp W mem md p n HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [C1 C2].
pose proof (req_size_pos n (BLKN ly S Hp W mem md p n HAR Hin)) as [Q _].
destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases 0x5fc000 p) as [|H2]; [right; lia|]. exfalso.
assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
{ refine (proj1 (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max p 0x10000) HAR _)).
  left. exists p, n. split; [exact Hin | lia]. }
apply Hc. unfold in_zr. lia.
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
  (H0 & H1 & (memS & HJi & Hag) & Hout) HP H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCX HRM HCNT HFP MOK.
rewrite !Z.add_0_r in HJi.
pose proof (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Hsp Hst) as Hroom.
unfold rmf_hpblk in HP. destruct (Z.eqb_spec hp 0) as [Hz | Hnz].
- subst hp. cbn [app] in HP. eapply SRr_mono.
  { exact (AFREEN W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k o raw ch kr HJi H10 Hsp Hal Hneg Hst
      Hroom Hgp Htp Hra Hraw Hch HCX HRM HCNT MOK). }
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
      Hneg Hst Hroom Hgp Htp Hra Hraw Hch HCX HRM HCNT); [intros Hin0 i Hi; exact (HFP Hnz Hin0 i Hi) | exact MOK]. }
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
  intros Hr. pose proof (rmf_blk_off_img lyc Sc Hpc W memT mdc hp kh (proj1 HJi) Hin) as Hoff.
  pose proof (pa_img_range a Hi). hnf in Hoff. lia.
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
  intros Hw. unfold arm in *. apply (rr_writable2 (w_H W1) (w_H W2) m1 m2 a); [|exact Hw].
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
    { intros Heq. assert (ND : List.NoDup (ablocks B lyc Sc)) by (eapply rm_ablocks_nodup; eassumption).
      apply (Permutation_NoDup HP) in ND.
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
assert (HI : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]];
  first [ apply HRGI; lia | refine ((fun H => conj (proj1 H) (proj1 (proj2 H))) (HG a _)); unfold inG, G_RR, G_DR, G_SL; rmf_exists ]. }
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
Lemma rmf_fz_aout : forall (K : Z -> Prop) ly S W mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> rmf_fz K (aout_fp B RG 0 0) -> rmf_bk K (aout_blks cap out) ->
  rmf_fz K (aout_fp B RG cap out).
Proof.
intros K ly S W mem c O mx no cap out HO HC HB.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Hblk).
intros r Hr a Ha. destruct (rm_aout_fp_cases B RG cap out r Hr) as [Hr0 | (Hc & ->)]; [exact (HC r Hr0 a Ha)|].
destruct Hblk as [(Hc0 & _) | (Hcp & _ & Hin & _)]; [lia|].
cbn [fst snd] in Ha. apply (HB out cap a).
- unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
- pose proof (req_size_pos cap ltac:(lia)) as [_ Hrq]. lia.
Qed.
Lemma rmf_abk_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof.
intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))].
Qed.

(* ------------------------------------------------------------------ FREE: RRF i 0x84318 -> RRC i 0x84360 *)
Theorem rr_m_free : hop_free_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
unfold hop_free_stmt. intros cx i W1 c1 HB HRCTX HF KC.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* image B's journal is at RR_STK_x (the A twin: RR_STK) *)
assert (WS : RR_STK_x = 17056) by reflexivity. assert (WF : RR_FRAME = 48) by reflexivity.
assert (WA : ASTACK = 16384) by reflexivity.
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK0 & HWAKE0 & HREL0 & HOUT0 & HROM0 & HSRC0 & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres.
assert (SPB : alloc_ceiling + RR_STK_x <= rsp0 cx /\ rsp0 cx <= 2 ^ 47) by lia.
destruct HF as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & spent &
  -> & HMH & HLV & HDR & HP1 & HP2 & HCASE & HTB & HSL & HOUT & HPERM & HGS & HMO & HSP & HRMF & HCNF).
destruct HMH as (HRH & H19 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp1 & Hgp1 & Htp1 & Hhi1) & H8 & H9 & H18 & H20).
pose proof HLV as (HJ0 & HROM1 & HPK1 & HSV & HLK & HWK).
destruct HTB as (TS & TSW & TN & TNW & TC & TCW & TIn & TXL & (tail & TTL & TG) & TSA & TOK).
(* ---- facts at the cut ---- *)
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ0).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as (HG16 & HG4096 & HGceil & HGia & _ & _).
change (req_size ATABLE) with 896 in HGceil, HGia.
pose proof (rmf_blk_off_img ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as HGoff.
change (req_size ATABLE) with 896 in HGoff. hnf in HGoff.
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & RL16 & _ & _ & ROK & RND).
assert (Hpads : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx))
  by (eapply Forall_impl; [|exact ROK]; intros e (_ & _ & Q1 & Q2 & _); split; assumption).
assert (ESA : rmSA cx i = rxG0 cx + AENT * Z.of_nat i) by reflexivity.
assert (LPRE : length (rmTpre cx i) = (56 * i)%nat).
{ unfold rmTpre. rewrite rm_concat_len, length_firstn by (rewrite <- (firstn_skipn i (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [Hp _]; exact Hp). lia. }
assert (LPOST : length (rmTpost cx i) = (56 * (length (rxes cx) - S i))%nat).
{ unfold rmTpost. rewrite rm_concat_len, length_skipn by (rewrite <- (firstn_skipn (S i) (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [_ Hp]; exact Hp). lia. }
assert (LX : length (entry_bytes (entry_cleared e1)) = 56%nat) by (apply rm_eb_len; [exact HP1 | exact HP2]).
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
  rewrite LPRE in M. rewrite ESA. replace (rxG0 cx + AENT * Z.of_nat i + 16) with (rxG0 cx + Z.of_nat (56 * i) + 16)
    by (unfold AENT; lia).
  exact M. }
assert (Hi16 : (S i <= 16)%nat) by lia.
assert (GB : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= 140737479966720) by (unfold ASAN_CEIL in *; lia).
assert (HSA : rxG0 cx <= rxG0 cx + AENT * Z.of_nat i /\ rxG0 cx + AENT * Z.of_nat i + 24 <= rxG0 cx + 896)
  by (unfold AENT; lia).
assert (SA8 : (rxG0 cx + AENT * Z.of_nat i) mod 8 = 0).
{ unfold AENT. pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D. rewrite D.
  replace (16 * (rxG0 cx / 16) + 56 * Z.of_nat i) with ((2 * (rxG0 cx / 16) + 7 * Z.of_nat i) * 8) by ring.
  apply Z_mod_mult. }
assert (HO5 : 0x10000 <= rg_src RG /\ rg_src RG + 8 <= 0x5fc000)
  by (rewrite RGSRC; exact (pa_obj_img 5 ltac:(lia))).
(* ---- the symbolic state at 0x84318 ---- *)
remember (Eimg (Ereg regs1 (rmf_extra (rxG0 cx) (rxG0 cx + AENT * Z.of_nat i) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmf_extra (rxG0 cx) (rxG0 cx + AENT * Z.of_nat i) (re_buf e1))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 (AENT * Z.of_nat i)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 (rg_src RG + RR_HI_SRC)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat i))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (UB20 : base_val E (Some 20%nat) = rg_src RG + RR_HI_SRC)
by (cbn [base_val]; rewrite E20; apply unsigned_lit_small; unfold RR_HI_SRC; lia).
assert (UB33 : base_val E (Some 33%nat) = rxG0 cx + AENT * Z.of_nat i)
by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_rmf (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_free)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmf. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rmf_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB20. split; [unfold RR_HI_SRC; lia|]. split; [unfold RR_HI_SRC; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rg_src RG + RR_HI_SRC) (-1288) 8 (SOff 32 0) (rxG0 cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (rg_src RG + RR_HI_SRC + -1288) with (rg_src RG) by (unfold RR_HI_SRC; lia). exact TS.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rxG0 cx + AENT * Z.of_nat i) 16 8 (SOff 34 0) (re_buf e1));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact MB.
- apply pairwise_disjoint_of_extents. unfold rmf_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite UB20, UB33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear - HO5 HGoff HSA. unfold RR_HI_SRC. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [rmf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold RMF_PHI, SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rmf_facts f_alias alias_ok]. split; [|split; [|exact I]].
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 32 0) (SOff 19 0)) = U E (SOff 33 0)).
      rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 19 _ E19), (U_atom E 33 _ E33) by (unfold AENT; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). reflexivity.
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) = U E (SOff 33 0)).
      rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 19 _ E19), (U_atom E 33 _ E33) by (unfold AENT; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). lia. }
clear HE.
assert (HBx : U E BxF = SHADOW_OFF) by (unfold BxF; rewrite (U_atom E 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxF rmf_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE
      (rxG0 cx + AENT * Z.of_nat i + 16) 8 HAR1 TIn);
    [lia | change (req_size ATABLE) with 896; lia].
  + exact HBx.
  + rewrite (U_atom E 33 _ E33) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
(* ---- the closer of the trap edge 0x84320 bltu a1,a0 (pointer overflow of g_src + 56 i) ---- *)
assert (T1 : branch_taken BC_LTU (sv_denot E (SOff 33 0)) (sv_denot E (SOff 32 0)) = false)
by (apply (trap_ptr_wrap_atom E 33 32 (rxG0 cx) (AENT * Z.of_nat i) E33 E32); unfold AENT; lia).
pose proof HJ0 as HJr.
unfold cfg_at. change (w64 (BASE + A_rr_free)) with (Z_to_bv 64 (BASE + A_rr_free)).
(* 0x84318 ld a0,-1288(s4); add a1,a0,s3: to the overflow check 0x84320 *)
paj_run_tok_x RUN HS HJr SHOK rmf_Bspan.
{ rmf_awr. }
rmf_mem Em1.
(* TRAP EDGE 0x84320 bltu a1,a0 -> unimp: never taken *)
psrr_branch_tok RUN BR HS SHOK rmf_Bspan.
{ exfalso. rewrite T1 in Hc. discriminate. }
(* the traps 0x84330 / 0x84334 / 0x84340 (decided by the runner), the shadow check of the buf field (fast path: the
   report 0x84404 is not reached), ld a0,16(a1), to the call to free 0x8435c *)
paj_run_tok_x RUN HS HJr SHOK rmf_Bspan.
{ rmf_awr. }
rmf_mem Em2.
lazymatch type of HS with
| context [restrict _ ?m] => set (msF := m) in *; clearbody msF
| ?T => idtac "rr_m_free: HS is" T; fail
end.
pmkst HS.
rewrite Em2, Em1 in HJr |- *.
rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) QRA. prreg HS (10%bv : bv 5) QA0.
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 _ RMF_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (QSP : spZ (ms_regs msF) = rsp0 cx - RR_FRAME) by (unfold spZ; rewrite (HK 2%bv) by (cbv; tauto); exact Hsp1).
assert (Q3 : getr (ms_regs msF) 3 = w64 (as_gp B)) by (rewrite (HK 3%bv) by (cbv; tauto); rewrite Hgp1; exact Hgp).
assert (Q4 : getr (ms_regs msF) 4 = w64 (as_tp B)) by (rewrite (HK 4%bv) by (cbv; tauto); rewrite Htp1; exact Htp).
assert (Q8 : getr (ms_regs msF) 8 = w64 (rxFD cx)) by (rewrite (HK 8%bv) by (cbv; tauto); exact H8).
assert (QRA4 : 4096 <= raZ (ms_regs msF)) by (unfold raZ; rewrite QRA, unsigned_lit_small by lia; lia).
assert (HCH : chain_pre ly1 (aview SEGS (w_H W1) m1) (ms_regs msF) []).
{ eapply rr_chain_pre_fd; [exact HB | exact HFD0 | | exact Q8 | exact QRA4].
  rewrite QSP. clear - SPB WS WF. lia. }
(* the free's context: the closed singleton [ra] (fd in s0 cuts the chain), ra = entry + 0x164: RCTX, the B rr_spec's
   last premise carried by the entry context *)
assert (HCX : In (raZ (ms_regs msF) :: spine []) CTX_AFREE).
{ assert (ER : raZ (ms_regs msF) = A_rr_entryP + 356)
    by (unfold raZ, A_rr_entryP; rewrite QRA, unsigned_lit_small by lia; unfold A_rr_entry, AF_fr_relay_remove; lia).
  rewrite ER. exact HRCTX. }
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
  { intros Hr. assert (ND : List.NoDup (ablocks B ly1 S1)) by (eapply rm_ablocks_nodup; eassumption).
    apply (Permutation_NoDup HPERM') in ND.
    unfold rmf_hpblk in ND. rewrite (proj2 (Z.eqb_neq (re_buf e1) 0) Hnz) in ND. cbn [app] in ND.
    apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. right.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hr. }
  destruct Hc0 as [Hc0 | Hc0]; [left; exact Hc0|]. right.
  apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [exact Hc0 | exfalso; exact (Hnr Hc0)]. }
(* free (s->buf) at 0x8435c *)
eapply SRr_bind.
{ apply (rmf_free (G_RR B RG) W1 (ms_regs msF) m1 RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx)
    (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 _ k1 (re_buf e1) (re_cap e1) _ (-48) (getr (ms_regs msF) 1) [] (rxkr cx)
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
  - exact HCX.
  - exact HRMF.
  - exact HCNF.
  - exact HFP.
  - exact MOK. }
cbv beta. intros W2 c3 Hwle (ly2 & S2 & Hp2 & regs2 & m2 & md2 & -> & HJ2 & HPR2 & HPm2 & HK2 & HM2 & HRM2 & HE2 & HPr2).
(* ---- back at 0x84360: RRC ---- *)
assert (HARm : exists mdm, ARx ly1 S1 Hp1 W1 m1 mdm) by (eexists; eapply ajournal_gx_AR_x; exact HJr).
destruct HARm as (mdm & HARm).
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
destruct (rmf_keep ly1 S1 Hp1 W1 m1 _ ly2 S2 Hp2 W2 m2 md2 _ _ (re_buf e1) (re_cap e1) _ HARm HAR2 HPERM' HPm2 HK2 HPr2
  HE2)
  as (KI & KB & KE).
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KR : forall a, rg_rng RG a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (RGIMG a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (KCL : forall a, rmf_cell a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (rmf_cell_img a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (BLK2 : forall b, In b ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
  In b (ablocks B ly2 S2)) by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPm2) Hb)).
assert (KBL : forall bl, (forall b, In b bl -> In b (ablocks B ly2 S2)) -> rmf_bk (abyte_kept W1 m1 W2 m2) bl)
  by (intros bl Hs p n a Hin Ha; exact (KB p n a (Hs _ Hin) Ha)).
assert (HR2 : forall r, In r RMF_KEPT -> getr regs2 r = getr regs1 r)
  by (intros r Hr; rewrite (rmf_ap _ _ r HPR2 Hr); exact (HK r Hr)).
apply KC. unfold RRC.
exists regs2, ly2, S2, Hp2, m2, md2, (k1 + 1), e1, h1, ev, LB, c2, O2, cap2, out2, (entry_bytes (entry_cleared e1)).
(* the return point *)
split.
{ unfold cfg_at, w64, A_rr_cpy, AF_fr_relay_remove. rewrite QRA. reflexivity. }
(* the registers *)
split.
{ split; [|split; [rewrite (HR2 19%bv) by (cbv; tauto); exact H19 | exact (conj HFD0 (conj Hi Hfd))]].
  split; [|rewrite (HR2 8%bv), (HR2 9%bv), (HR2 18%bv), (HR2 20%bv) by (cbv; tauto);
    exact (conj H8 (conj H9 (conj H18 H20)))].
  split; [unfold spZ in Hsp1 |- *; rewrite (HR2 2%bv) by (cbv; tauto); exact Hsp1|].
  split; [rewrite (HR2 3%bv) by (cbv; tauto); exact Hgp1|].
  split; [rewrite (HR2 4%bv) by (cbv; tauto); exact Htp1|].
  intros r Hr. rewrite (HR2 r (rmf_hi_in r Hr)). exact (Hhi1 r Hr). }
(* RLIVE *)
split.
{ split; [exact HJ2|].
  split; [eapply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low);
    [exact HJ2 | exact HROMO | exact PSTR | exact HROM0]|].
  split; [eapply rm_apk_trans; [exact HPK1 | exact HPr2]|].
  split.
  { intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact (HSV j Hj)].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K1.
    - clear - SPB Hj Hk WS WF. lia.
    - clear - SPB Hj Hk WS WF WA. lia. }
  split.
  { eapply alock_at_kept; [exact HLK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. clear - Ha. lia. }
  { eapply awake_at_kept; [exact HWK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. clear - Ha. lia. } }
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
  intros a Ha. apply KR. unfold rg_rng, ASRC. unfold rmHA, ASRC in Ha. clear - Ha Hj4. lia. }
(* the table *)
split.
{ split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; clear - Hx; lia | exact TS]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; clear - Hx; lia | exact TSW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; clear - Hx; lia | exact TN]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; clear - Hx; lia | exact TNW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; cbn in Hx; clear - Hx; lia | exact TC]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; clear - Hx; lia | exact TCW]|].
  split; [apply BLK2; left; reflexivity|].
  split; [exact TXL|].
  split.
  { exists tail. split; [exact TTL|]. apply (akept_garr8 W1 m1); [|exact TG]. intros x Hx. rewrite LTAB in Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity | change (req_size ATABLE) with 896; clear - Hx; lia]. }
  split.
  { apply (akept_awr W1 m1); [|exact TSA]. intros x Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity|].
    change (req_size ATABLE) with 896. rewrite ESA in Hx. unfold AENT in Hx |- *. clear - Hx Hi16. lia. }
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
  try (apply KCL; unfold rmf_cell; clear - Ha; lia).
  apply KE; [exact Ha|]. unfold arm in HOE.
  replace a with (as_errno B + (a - as_errno B)) by ring. apply (rmf_view_some (w_H W1) m1 _ 4 _ _ HOE).
  clear - Ha. lia. }
split; [exact HPm2|].
(* g_s *)
split.
{ intros a Ha Hj. apply (rmf_abk_trans _ W1 _ _ m1 _ a (HGS a Ha Hj)). apply KR. unfold rg_rng. clear - Ha. lia. }
(* the meter: the whole trace; the room round: kr left (the free's post) *)
split.
{ apply (mle_weaken MT (rxS cx) S2 (spent + mo_free MT)); [exact MLAW | | exact HSP].
  exact (mle_station MT (rxS cx) S1 S2 spent (mo_free MT) MLAW HMO HM2). }
exact HRM2.
Qed.

(* ---- route R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form, lib/B/W_bx_order_x.v): the FREE hop at
   a world relation R, over lib/B/W_rr_match_cx.v's Section wR twins (hop_free_stmt_xR, RRF_xR / RRC_xR, rPOST_xR) and
   the R free rules (W_journal_x.v afree_cf_rule_c_xR / afree_null_cf_rule_c_xR .. RO CTX_AFREE R), whose call-boundary
   premise RO comes from the journal's ARx at the call state (RO_ARx; part 3c removed their memnorm premise;
   lib/B/W_gestures_end.v gse_free_xR's pattern).  Against the strict texts only these change: ajournal_gx_x ->
   ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, hop_free_stmt / RRC -> their _xR, RUN / BR -> RUNG / BRR
   (W_journal_x.v paj_run_x_xG, W_kit.v paj_branch_xR), AFREE / AFREEN -> AFREE_R / AFREEN_R (with RO_ARx), and each
   engine step -> its _xR.
   Census rows (a Theorem Labs lane's G8b-relayrm-B.tsv (sha256 4c7c7e01243b; internal record)) -> twins: :280 AFREE -> AFREE_R, :284 DRAIN -> DRAIN_R,
   :285 GSE -> GSE_R, :287 AFREEN -> AFREEN_R, :332 rmf_free -> rmf_free_xR, :577 rr_m_free -> rr_m_free_xR.
   The strict rmf_free and rr_m_free keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary premise RO, from the journal's ARx at the call state (part 3c removed their memnorm
   premise) *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
(* :280 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :284 DRAIN, :285 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :287 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.

Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* :332 rmf_free at R *)
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
  (H0 & H1 & (memS & HJi & Hag) & Hout) HP H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCX HRM HCNT HFP MOK.
rewrite !Z.add_0_r in HJi.
pose proof (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Hsp Hst) as Hroom.
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
unfold rmf_hpblk in HP. destruct (Z.eqb_spec hp 0) as [Hz | Hnz].
- subst hp. cbn [app] in HP. eapply SRrG_mono.
  { exact (AFREEN_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k o raw ch kr HJi H10 Hsp Hal Hneg Hst
      Hroom Hgp Htp Hra Hraw Hch HRO HCX HRM HCNT MOK). }
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
      Hneg Hst Hroom Hgp Htp Hra Hraw Hch HRO HCX HRM HCNT); [intros Hin0 i Hi; exact (HFP Hnz Hin0 i Hi) | exact MOK]. }
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
  intros Hr. pose proof (rmf_blk_off_img lyc Sc Hpc W memT mdc hp kh (proj1 HJi) Hin) as Hoff.
  pose proof (pa_img_range a Hi). hnf in Hoff. lia.
Qed.

(* :577 rr_m_free at R: FREE, RRF_xR i 0x84318 -> RRC_xR i 0x84360 *)
Theorem rr_m_free_xR : hop_free_stmt_xR B PST ARx R MT RP MMAX RG CTX_AFREE.
Proof.
unfold hop_free_stmt_xR. intros cx i W1 c1 HB HRCTX HF KC.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* image B's journal is at RR_STK_x (the A twin: RR_STK) *)
assert (WS : RR_STK_x = 17056) by reflexivity. assert (WF : RR_FRAME = 48) by reflexivity.
assert (WA : ASTACK = 16384) by reflexivity.
pose proof HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK0 & HWAKE0 & HREL0 & HOUT0 & HROM0 & HSRC0 & HPERM0 &
  HTRM & HLIVE & HMOK & HRM0 & HCN0).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres.
assert (SPB : alloc_ceiling + RR_STK_x <= rsp0 cx /\ rsp0 cx <= 2 ^ 47) by lia.
destruct HF as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & spent &
  -> & HMH & HLV & HDR & HP1 & HP2 & HCASE & HTB & HSL & HOUT & HPERM & HGS & HMO & HSP & HRMF & HCNF).
destruct HMH as (HRH & H19 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp1 & Hgp1 & Htp1 & Hhi1) & H8 & H9 & H18 & H20).
pose proof HLV as (HJ0 & HROM1 & HPK1 & HSV & HLK & HWK).
destruct HTB as (TS & TSW & TN & TNW & TC & TCW & TIn & TXL & (tail & TTL & TG) & TSA & TOK).
(* ---- facts at the cut ---- *)
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ0).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as (HG16 & HG4096 & HGceil & HGia & _ & _).
change (req_size ATABLE) with 896 in HGceil, HGia.
pose proof (rmf_blk_off_img ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 TIn) as HGoff.
change (req_size ATABLE) with 896 in HGoff. hnf in HGoff.
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & RL16 & _ & _ & ROK & RND).
assert (Hpads : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx))
  by (eapply Forall_impl; [|exact ROK]; intros e (_ & _ & Q1 & Q2 & _); split; assumption).
assert (ESA : rmSA cx i = rxG0 cx + AENT * Z.of_nat i) by reflexivity.
assert (LPRE : length (rmTpre cx i) = (56 * i)%nat).
{ unfold rmTpre. rewrite rm_concat_len, length_firstn by (rewrite <- (firstn_skipn i (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [Hp _]; exact Hp). lia. }
assert (LPOST : length (rmTpost cx i) = (56 * (length (rxes cx) - S i))%nat).
{ unfold rmTpost. rewrite rm_concat_len, length_skipn by (rewrite <- (firstn_skipn (S i) (rxes cx)) in Hpads;
    apply Forall_app in Hpads as [_ Hp]; exact Hp). lia. }
assert (LX : length (entry_bytes (entry_cleared e1)) = 56%nat) by (apply rm_eb_len; [exact HP1 | exact HP2]).
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
  rewrite LPRE in M. rewrite ESA. replace (rxG0 cx + AENT * Z.of_nat i + 16) with (rxG0 cx + Z.of_nat (56 * i) + 16)
    by (unfold AENT; lia).
  exact M. }
assert (Hi16 : (S i <= 16)%nat) by lia.
assert (GB : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= 140737479966720) by (unfold ASAN_CEIL in *; lia).
assert (HSA : rxG0 cx <= rxG0 cx + AENT * Z.of_nat i /\ rxG0 cx + AENT * Z.of_nat i + 24 <= rxG0 cx + 896)
  by (unfold AENT; lia).
assert (SA8 : (rxG0 cx + AENT * Z.of_nat i) mod 8 = 0).
{ unfold AENT. pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D. rewrite D.
  replace (16 * (rxG0 cx / 16) + 56 * Z.of_nat i) with ((2 * (rxG0 cx / 16) + 7 * Z.of_nat i) * 8) by ring.
  apply Z_mod_mult. }
assert (HO5 : 0x10000 <= rg_src RG /\ rg_src RG + 8 <= 0x5fc000)
  by (rewrite RGSRC; exact (pa_obj_img 5 ltac:(lia))).
(* ---- the symbolic state at 0x84318 ---- *)
remember (Eimg (Ereg regs1 (rmf_extra (rxG0 cx) (rxG0 cx + AENT * Z.of_nat i) (re_buf e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmf_extra (rxG0 cx) (rxG0 cx + AENT * Z.of_nat i) (re_buf e1))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 (AENT * Z.of_nat i)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 (rg_src RG + RR_HI_SRC)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat i))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (UB20 : base_val E (Some 20%nat) = rg_src RG + RR_HI_SRC)
by (cbn [base_val]; rewrite E20; apply unsigned_lit_small; unfold RR_HI_SRC; lia).
assert (UB33 : base_val E (Some 33%nat) = rxG0 cx + AENT * Z.of_nat i)
by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_rmf (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_free)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmf. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rmf_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB20. split; [unfold RR_HI_SRC; lia|]. split; [unfold RR_HI_SRC; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rg_src RG + RR_HI_SRC) (-1288) 8 (SOff 32 0) (rxG0 cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (rg_src RG + RR_HI_SRC + -1288) with (rg_src RG) by (unfold RR_HI_SRC; lia). exact TS.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite UB33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rxG0 cx + AENT * Z.of_nat i) 16 8 (SOff 34 0) (re_buf e1));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact MB.
- apply pairwise_disjoint_of_extents. unfold rmf_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite UB20, UB33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear - HO5 HGoff HSA. unfold RR_HI_SRC. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [rmf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold RMF_PHI, SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rmf_facts f_alias alias_ok]. split; [|split; [|exact I]].
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 32 0) (SOff 19 0)) = U E (SOff 33 0)).
      rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 19 _ E19), (U_atom E 33 _ E33) by (unfold AENT; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). reflexivity.
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) = U E (SOff 33 0)).
      rewrite U_SAlu, (U_atom E 32 _ E32), (U_atom E 19 _ E19), (U_atom E 33 _ E33) by (unfold AENT; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). lia. }
clear HE.
assert (HBx : U E BxF = SHADOW_OFF) by (unfold BxF; rewrite (U_atom E 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxF rmf_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE
      (rxG0 cx + AENT * Z.of_nat i + 16) 8 HAR1 TIn);
    [lia | change (req_size ATABLE) with 896; lia].
  + exact HBx.
  + rewrite (U_atom E 33 _ E33) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
(* ---- the closer of the trap edge 0x84320 bltu a1,a0 (pointer overflow of g_src + 56 i) ---- *)
assert (T1 : branch_taken BC_LTU (sv_denot E (SOff 33 0)) (sv_denot E (SOff 32 0)) = false)
by (apply (trap_ptr_wrap_atom E 33 32 (rxG0 cx) (AENT * Z.of_nat i) E33 E32); unfold AENT; lia).
pose proof HJ0 as HJr.
unfold cfg_at. change (w64 (BASE + A_rr_free)) with (Z_to_bv 64 (BASE + A_rr_free)).
(* 0x84318 ld a0,-1288(s4); add a1,a0,s3: to the overflow check 0x84320 *)
paj_run_tok_xR RUNG HS HJr SHOK rmf_Bspan.
{ rmf_awr. }
rmf_mem Em1.
(* TRAP EDGE 0x84320 bltu a1,a0 -> unimp: never taken *)
psrr_branch_tok RUNG BRR HS SHOK rmf_Bspan.
{ exfalso. rewrite T1 in Hc. discriminate. }
(* the traps 0x84330 / 0x84334 / 0x84340 (decided by the runner), the shadow check of the buf field (fast path: the
   report 0x84404 is not reached), ld a0,16(a1), to the call to free 0x8435c *)
paj_run_tok_xR RUNG HS HJr SHOK rmf_Bspan.
{ rmf_awr. }
rmf_mem Em2.
lazymatch type of HS with
| context [restrict _ ?m] => set (msF := m) in *; clearbody msF
| ?T => idtac "rr_m_free: HS is" T; fail
end.
pmkst HS.
rewrite Em2, Em1 in HJr |- *.
rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) QRA. prreg HS (10%bv : bv 5) QA0.
pose proof (regs_kept_of_st_ok SEGS E _ _ regs1 _ RMF_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (QSP : spZ (ms_regs msF) = rsp0 cx - RR_FRAME) by (unfold spZ; rewrite (HK 2%bv) by (cbv; tauto); exact Hsp1).
assert (Q3 : getr (ms_regs msF) 3 = w64 (as_gp B)) by (rewrite (HK 3%bv) by (cbv; tauto); rewrite Hgp1; exact Hgp).
assert (Q4 : getr (ms_regs msF) 4 = w64 (as_tp B)) by (rewrite (HK 4%bv) by (cbv; tauto); rewrite Htp1; exact Htp).
assert (Q8 : getr (ms_regs msF) 8 = w64 (rxFD cx)) by (rewrite (HK 8%bv) by (cbv; tauto); exact H8).
assert (QRA4 : 4096 <= raZ (ms_regs msF)) by (unfold raZ; rewrite QRA, unsigned_lit_small by lia; lia).
assert (HCH : chain_pre ly1 (aview SEGS (w_H W1) m1) (ms_regs msF) []).
{ eapply rr_chain_pre_fd; [exact HB | exact HFD0 | | exact Q8 | exact QRA4].
  rewrite QSP. clear - SPB WS WF. lia. }
(* the free's context: the closed singleton [ra] (fd in s0 cuts the chain), ra = entry + 0x164: RCTX, the B rr_spec's
   last premise carried by the entry context *)
assert (HCX : In (raZ (ms_regs msF) :: spine []) CTX_AFREE).
{ assert (ER : raZ (ms_regs msF) = A_rr_entryP + 356)
    by (unfold raZ, A_rr_entryP; rewrite QRA, unsigned_lit_small by lia; unfold A_rr_entry, AF_fr_relay_remove; lia).
  rewrite ER. exact HRCTX. }
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
  { intros Hr. assert (ND : List.NoDup (ablocks B ly1 S1)) by (eapply rm_ablocks_nodup; eassumption).
    apply (Permutation_NoDup HPERM') in ND.
    unfold rmf_hpblk in ND. rewrite (proj2 (Z.eqb_neq (re_buf e1) 0) Hnz) in ND. cbn [app] in ND.
    apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. right.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hr. }
  destruct Hc0 as [Hc0 | Hc0]; [left; exact Hc0|]. right.
  apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [apply in_or_app; left; exact Hc0|].
  apply in_or_app. right. apply in_app_or in Hc0 as [Hc0 | Hc0]; [exact Hc0 | exfalso; exact (Hnr Hc0)]. }
(* free (s->buf) at 0x8435c *)
eapply (SRrG_bind SEGS R R_trans).
{ apply (rmf_free_xR (G_RR B RG) W1 (ms_regs msF) m1 RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx)
    (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 _ k1 (re_buf e1) (re_cap e1) _ (-48) (getr (ms_regs msF) 1) [] (rxkr cx)
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
  - exact HCX.
  - exact HRMF.
  - exact HCNF.
  - exact HFP.
  - exact MOK. }
cbv beta. intros W2 c3 HRw (ly2 & S2 & Hp2 & regs2 & m2 & md2 & -> & HJ2 & HPR2 & HPm2 & HK2 & HM2 & HRM2 & HE2 & HPr2).
(* ---- back at 0x84360: RRC ---- *)
assert (HARm : exists mdm, ARx ly1 S1 Hp1 W1 m1 mdm) by (eexists; eapply ajournal_gx_AR_xR; exact HJr).
destruct HARm as (mdm & HARm).
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
destruct (rmf_keep ly1 S1 Hp1 W1 m1 _ ly2 S2 Hp2 W2 m2 md2 _ _ (re_buf e1) (re_cap e1) _ HARm HAR2 HPERM' HPm2 HK2 HPr2
  HE2)
  as (KI & KB & KE).
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KR : forall a, rg_rng RG a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (RGIMG a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (KCL : forall a, rmf_cell a -> abyte_kept W1 m1 W2 m2 a)
  by (intros a Ha; destruct (rmf_cell_img a Ha) as (Hi' & Ho & He); exact (KI a Hi' Ho He)).
assert (BLK2 : forall b, In b ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
  In b (ablocks B ly2 S2)) by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPm2) Hb)).
assert (KBL : forall bl, (forall b, In b bl -> In b (ablocks B ly2 S2)) -> rmf_bk (abyte_kept W1 m1 W2 m2) bl)
  by (intros bl Hs p n a Hin Ha; exact (KB p n a (Hs _ Hin) Ha)).
assert (HR2 : forall r, In r RMF_KEPT -> getr regs2 r = getr regs1 r)
  by (intros r Hr; rewrite (rmf_ap _ _ r HPR2 Hr); exact (HK r Hr)).
apply KC. unfold RRC_xR.
exists regs2, ly2, S2, Hp2, m2, md2, (k1 + 1), e1, h1, ev, LB, c2, O2, cap2, out2, (entry_bytes (entry_cleared e1)).
(* the return point *)
split.
{ unfold cfg_at, w64, A_rr_cpy, AF_fr_relay_remove. rewrite QRA. reflexivity. }
(* the registers *)
split.
{ split; [|split; [rewrite (HR2 19%bv) by (cbv; tauto); exact H19 | exact (conj HFD0 (conj Hi Hfd))]].
  split; [|rewrite (HR2 8%bv), (HR2 9%bv), (HR2 18%bv), (HR2 20%bv) by (cbv; tauto);
    exact (conj H8 (conj H9 (conj H18 H20)))].
  split; [unfold spZ in Hsp1 |- *; rewrite (HR2 2%bv) by (cbv; tauto); exact Hsp1|].
  split; [rewrite (HR2 3%bv) by (cbv; tauto); exact Hgp1|].
  split; [rewrite (HR2 4%bv) by (cbv; tauto); exact Htp1|].
  intros r Hr. rewrite (HR2 r (rmf_hi_in r Hr)). exact (Hhi1 r Hr). }
(* RLIVE *)
split.
{ split; [exact HJ2|].
  split; [eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low);
    [exact HJ2 | exact HROMO | exact PSTR | exact HROM0]|].
  split; [eapply rm_apk_trans; [exact HPK1 | exact HPr2]|].
  split.
  { intros j Hj. apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact (HSV j Hj)].
    intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K1.
    - clear - SPB Hj Hk WS WF. lia.
    - clear - SPB Hj Hk WS WF WA. lia. }
  split.
  { eapply alock_at_kept; [exact HLK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. clear - Ha. lia. }
  { eapply awake_at_kept; [exact HWK|]. intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply KR. unfold rg_rng. clear - Ha. lia. } }
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
  intros a Ha. apply KR. unfold rg_rng, ASRC. unfold rmHA, ASRC in Ha. clear - Ha Hj4. lia. }
(* the table *)
split.
{ split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; clear - Hx; lia | exact TS]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; clear - Hx; lia | exact TSW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KR; unfold rg_rng; cbn in Hx; clear - Hx; lia | exact TN]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KR; unfold rg_rng; clear - Hx; lia | exact TNW]|].
  split; [apply (akept_vm W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; cbn in Hx; clear - Hx; lia | exact TC]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KCL; unfold rmf_cell; clear - Hx; lia | exact TCW]|].
  split; [apply BLK2; left; reflexivity|].
  split; [exact TXL|].
  split.
  { exists tail. split; [exact TTL|]. apply (akept_garr8 W1 m1); [|exact TG]. intros x Hx. rewrite LTAB in Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity | change (req_size ATABLE) with 896; clear - Hx; lia]. }
  split.
  { apply (akept_awr W1 m1); [|exact TSA]. intros x Hx.
    apply (KB (rxG0 cx) ATABLE x); [apply BLK2; left; reflexivity|].
    change (req_size ATABLE) with 896. rewrite ESA in Hx. unfold AENT in Hx |- *. clear - Hx Hi16. lia. }
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
  try (apply KCL; unfold rmf_cell; clear - Ha; lia).
  apply KE; [exact Ha|]. unfold arm in HOE.
  replace a with (as_errno B + (a - as_errno B)) by ring. apply (rmf_view_some (w_H W1) m1 _ 4 _ _ HOE).
  clear - Ha. lia. }
split; [exact HPm2|].
(* g_s *)
split.
{ intros a Ha Hj. apply (rmf_abk_trans _ W1 _ _ m1 _ a (HGS a Ha Hj)). apply KR. unfold rg_rng. clear - Ha. lia. }
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
