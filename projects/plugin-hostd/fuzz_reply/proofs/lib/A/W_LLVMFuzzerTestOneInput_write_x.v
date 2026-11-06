(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_write (lib/A/W_LLVMFuzzerTestOneInput_write.v lf_arm_write), the
   jump table's arm 1 of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput, from the arm's entry 0x843bc to the latch
   0x84490 (a Theorem Labs lane's route (b), step 7). The AR file is NOT edited; this file Requires it and cites its AR-free
   definitions and lemmas (the arm's addresses, its model records and rules, the entry states' sstates, the register,
   frame-byte, coverage, permutation and keep lemmas); every lemma of it that names AR, AR_laws, ajournal_gx, lcut or an
   INV_* is restated here over ARx, with its proof converted (al_X -> alx_X, the journal lemmas -> W_journal_x's _x, the
   run tactics -> paj_run_tok_x / paj_run_to_tok_x, Hp after S, Hp3 after S3, Hp' after S').
   - The Section header is cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235), so lf_arm_write_x's
     statement is cut_x's ARM_write hypothesis (cut_x.v:303) at that Section's variables (checked at the end).
   - list_push is taken as its _x callee spec, lp_spec_g_x B PST ARx MT WR_MMAX (BASE + AF_fr_list_push) (W_contract_x.v
     Section w2g; W2 proves it as pb_list_push_g_x), at its own G (wr_G1 si), lifted with ajournal_gx_G_mono_x and composed
     with ajournal_gx_sub_x: the AR walk's call site has lp_spec's shape (it calls pb_list_push_g, whose statement is
     lp_spec_g). The AR walk's allocator hypotheses MLAW / ARE / AMA / AMEMCPY were pb_list_push_g's arguments only and are
     gone with it.
   - The other Section hypotheses are the AR file's, over ARx where they name AR (ERR is cut_x's errno_law_x), and
     three that the generic relation and the placement PST force: BLKN (a live block's request size is >= 0, the last
     conjunct of AR's al_blocks that AR_laws_x does not carry; W_kit_x.v's BLKN text), PST_ROM and PST_GFR (the ROM bytes
     and the bytes of G_fr lie outside PST: the generic journal's image clause and ajournal_gx_rom_view_x keep only bytes
     outside PST). At the cf instance PST = [] (top_x), so PST_ROM / PST_GFR hold by `inversion`.
   - The latch's AR helpers this walk reads (W_LLVMFuzzerTestOneInput_latch.v lt_blk .. lt_aout, lt_amodel_kept,
     lt_ainput_kept, lt_afn_pre_at) are restated over ARx as wrx_*; their AR-free neighbours are cited.
   - ROUTE R (Section wrxR, at the end of Section wrx): lf_arm_write_xR, the arm at a world relation R, whose statement
     is cut_x's ARM_write_R (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section wR, checked in Section checkR).  list_push reallocs its vector, so its call
     takes list_push's R contract LP_R : lp_spec_g_xR (W_contract_xR.v; a Theorem Labs lane's pb_list_push_g_xR proves it) in
     place of LP.  The strict lf_arm_write_x keeps its proof. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame W_list_push.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyGuard.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
(* route R (Section wrxR below): SRrG and its laws, and list_push's contract at R (lp_spec_g_xR) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
Import ListNotations.
(* the ASan image's sink instance, the one _cut's and cut_x's journals name (the AR file's line 57) *)
#[local] Existing Instance AE2k.tfib_sink_head.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as the latch file's proofs expect it (its imports leave it true); set to false below, before the
   write file's proofs, as that file sets it (its line 60) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section wrx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:194-235), verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2): the allocator rules' room record RP, whose room invariant is the
   cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ => room_live_cf S = NP) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.

(* ---- the AR file's Section hypotheses (W_LLVMFuzzerTestOneInput_write.v:146-174), over ARx where they name AR ---- *)
(* the allocator instance: errno's place (pal_env) *)
Hypothesis TL : PALib B.
(* list_push's contract at its own G, over ARx (W_contract_x.v:395; W2's pb_list_push_g_x); it replaces the AR walk's
   pb_list_push_g B LAWS TL MT MLAW WR_MMAX wr_HMMAX ARE AMA AMEMCPY; at the room record RP *)
Hypothesis LP : lp_spec_g_x (PI := PB_fr) B PST ARx MT RP WR_MMAX (BASE + AF_fr_list_push).
Hypothesis GWR : glob_wr_law G_fr.
(* _cut's errno_law, over ARx: cut_x's errno_law_x *)
Hypothesis ERR : errno_law_x B ARx.
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis HGW : forall a, inG wr_G a -> inG G_fr a.
Hypothesis HERRS : forall a, inG ((rg_s fr_RG, 4 * ASRC) :: wr_G) a -> ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ROM_ERR : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ROM_PIN : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct). The text is W_kit_x.v:45's BLKN (and W1Verify's W_check_bounded.v BLKN). *)
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the ROM bytes lie outside PST: ajournal_gx_rom_view_x's premise (W_journal_x.v:329) *)
Hypothesis PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
(* G_fr's bytes lie outside PST: the generic journal's image clause (YCbqG.v:254-256) keeps only bytes outside PST, and
   list_push's journal must keep the model's globals (all in G_fr: HGW / HGs) *)
Hypothesis PST_GFR : forall a, inG G_fr a -> ~ Exists (in_zr a) PST.

(* ---- the arm's open model obligations (W_LLVMFuzzerTestOneInput_write.v:230-264), verbatim (LS is cut_x's LSx) ---- *)
Hypothesis RI_write_skip : forall cx t m,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
  RINV cx (t + 1) (wr_skip m (wr_k2 cx m)).
Hypothesis LS_write_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Hypothesis RI_write_push : forall cx t m si h l' d ev,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev).
Hypothesis LS_write_room : forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok MT S (lp_cost MT (hs_pending h) (wr_n cx m)).
(* the push rule at W8Add's PROPOSED text (lib/A/ReplyLS.v atop_LS_write_push_prop), in this Section's form; see
   _write.v's LS_write_push *)
Hypothesis LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
(* the room round's count row (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c); lib/A/ReplyLScnt.v fr_LS3cp_cnt_write at
   commit ba8e99b5bd2): at the cut, the live counts plus list_push's premise peak lp_peak stay under RP's bounds.  The
   guards are the walk's facts at the cut (the model's sizes come from amodel_at) *)
Hypothesis LS_cnt : forall cx t m si h ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (lp_peak (hs_pending h) (wr_n cx m)) (ablocks B ly S).

Local Notation AJG := (ajournal_gx_x segs B PST ARx G_fr 0 []).
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* ------------------------------------------------------------------ the latch's AR helpers, over ARx
   (W_LLVMFuzzerTestOneInput_latch.v:60-243, :329-384, :445-457, :632-705; AR -> ARx, Hp after S; lt_blk's size conjunct
   from BLKN; lt_afn_pre_at over YCbqG's afn_pre_x_at and W_frame_x's aview_above_of_journal_x) *)
Ltac wrx_low :=
  cbn [fst snd gfp]; unfold CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lt_ceil_lo; lia.
Lemma wrx_blk : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S Hp W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H1 & H2 & _).
  pose proof (BLKN ly S Hp W mem md p n HAR Hin) as H3.
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma wrx_alist : forall ly S Hp (W : world segs) mem md LA l lines,
  ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= CEIL8 ->
  lt_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lt_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (wrx_blk ly S Hp W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; lia|]. apply lt_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (wrx_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
    cbn [gfp fst snd]. rewrite lt_bzs_len, length_app, lt_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
Lemma wrx_asrc : forall ly S Hp (W : world segs) mem md HA h,
  ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= CEIL8 ->
  lt_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (wrx_alist ly S Hp W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (wrx_alist ly S Hp W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (wrx_alist ly S Hp W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (wrx_blk ly S Hp W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply lt_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite lt_bzs_len, Hpj. unfold APARTIAL, CEIL8 in *. lia.
    + apply lt_fp_low_app; [exact A1|]. apply lt_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
Lemma wrx_aentry : forall ly S Hp (W : world segs) mem md e,
  ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  lt_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lt_fp_low (map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (wrx_blk ly S Hp W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lt_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (wrx_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
      cbn [gfp snd]. rewrite lt_bzs_len, length_app. unfold CEIL8 in *. lia.
    + apply lt_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (wrx_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lt_bzs_len, lt_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold CEIL8. pose proof lt_ceil_lo. lia. }
        destruct (wrx_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan's globals ---- *)
Lemma wrx_arelay : forall ly S Hp (W : world segs) mem md G es,
  ARx ly S Hp W mem md -> arelay_at B fr_globals ly S W mem G es ->
  lt_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (wrx_blk ly S Hp W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : lt_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (wrx_aentry ly S Hp W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lt_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (wrx_aentry ly S Hp W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lt_fp_low_cons; [wrx_low | wrx_low|].
    apply lt_fp_low_cons; [wrx_low | wrx_low|].
    apply lt_fp_low_cons; [wrx_low | wrx_low|].
    apply lt_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
Lemma wrx_aout : forall ly S Hp (W : world segs) mem md c O mx no cap out,
  ARx ly S Hp W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  lt_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lt_fp_low_cons; [wrx_low | wrx_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (wrx_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | cbn; unfold CEIL8 in *; lia | apply lt_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
Lemma wrx_amodel_kept : forall ly S Hp (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S Hp W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= CEIL8)
      by (unfold fr_RG, CEIL8; cbn; unfold ASRC; pose proof lt_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (wrx_asrc ly S Hp W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lt_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (wrx_arelay ly S Hp W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (wrx_aout ly S Hp W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. lia.
Qed.
Lemma wrx_ainput_kept : forall cx ly S Hp (W : world segs) mem md (W' : world segs) mem',
  ARx ly S Hp W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S Hp W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hpz) | (Hn & Hin)]; [lia|].
  destruct (wrx_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold CEIL8. lia.
Qed.
Lemma wrx_afn_pre_at : forall cx Hp full ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hp full ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* the write file's proofs ran with the flag false (W_LLVMFuzzerTestOneInput_write.v:66) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* ------------------------------------------------------------------ the arm's entry states, over ARx (the AR file's
   :298-528; al_blocks / al_shadow -> alx_blocks / alx_shadow, the latter's no-hidden-head premise from HP0) *)
(* the entry state at the arm, with two bytes of input left *)
Lemma wr_entry2_x : forall (cx : lfcx) (m : lmod) ly S Hp (W : world segs) regs mem md,
  ARx ly S Hp W mem md ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a) ->
  astk_ok LLVMF_STK (c_ly cx) (spZ (c_regs cx)) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 26 = w64 SB ->
  getr regs 28 = w64 (c_p cx + wr_k1 cx m) ->
  In (c_p cx, c_n cx) (ablocks B ly S) ->
  garr8 segs (arm W mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  c_n cx = Z.of_nat (length (c_pl cx)) -> 0 < c_n cx < 2 ^ 26 ->
  0 <= wr_k1 cx m -> wr_k1 cx m + 2 <= c_n cx ->
  st_ok_pi segs VAL (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1))))) wr_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs wr_Bx (wr_SH 2)
       (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1)))))
       (mrestrict (w_H W) mem).
Proof.
  intros cx m ly S Hp W regs mem md HAR Hpres Hstk R2 R9 R26 R28 Hin Hg Hlen Hcn Hk0 Hk2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _).
  pose proof (wr_F_mod32 cx) as HFm. pose proof (wr_F_range cx) as HFr.
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil, Hpapp.
  set (b0 := in_byte cx (wr_k1 cx m)). set (b1 := in_byte cx (wr_k1 cx m + 1)).
  assert (Hb0 : 0 <= b0 < 256) by (unfold b0, in_byte; apply u8_range).
  assert (Hb1 : 0 <= b1 < 256) by (unfold b1, in_byte; apply u8_range).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (wr_extra b0 b1))). pose proof pa_B_ok as HBASE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
  assert (E32 : ew E 32 = Z_to_bv 64 b0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 b1)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
    by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
  assert (HF46 : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (Hp2 : c_p cx + wr_k1 cx m + 2 <= c_p cx + c_n cx) by lia.
  split.
  - unfold wr_ss2, A_wr_arm. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 9%nat (lf_F cx) E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. unfold LLVMF_STK in *. lia.
      * rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val segs E _ (c_p cx + wr_k1 cx m) 0 1 (SOff 32 0) b0);
           [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat.
           replace (c_p cx + wr_k1 cx m) with (c_p cx + wr_k1 cx m) by reflexivity.
           exact (wr_byte cx W mem (wr_k1 cx m) Hg ltac:(lia)).
        -- apply (chunk_ok_val segs E _ (c_p cx + wr_k1 cx m) 1 1 (SOff 33 0) b1);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           change (N.to_nat 1) with 1%nat.
           replace (c_p cx + wr_k1 cx m + 1) with (c_p cx + (wr_k1 cx m + 1)) by lia.
           exact (wr_byte cx W mem (wr_k1 cx m + 1) Hg ltac:(lia)).
    + apply pairwise_disjoint_of_extents.
      unfold extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 9%nat (lf_F cx) E9) by lia. rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold LLVMF_STK in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [wr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E26, E28, E32, E33, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
      unfold SB, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; try lia; try (apply mod32_mod16; exact HFm).
  - unfold sh_ok, wr_SH. constructor; [|constructor].
    destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md (c_p cx) (c_n cx) HAR Hin
      (hp_off_block_hp0 segs ARx HP0 ly S Hp W mem md (c_p cx) (c_n cx) HAR)) as [Hbs _].
    eapply (shent_ok_of_range segs (w_H W) mem E wr_Bx 28 (c_p cx) (c_n cx) (c_p cx + wr_k1 cx m) 0 2).
    + eapply block_shadow_range; [exact Hbs | lia | rewrite Hreq; lia].
    + unfold U, wr_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      cbn [Z.min Z.max] in Hx. lia.
Qed.

(* the entry state at the arm, with one byte of input left *)
Lemma wr_entry1_x : forall (cx : lfcx) (m : lmod) ly S Hp (W : world segs) regs mem md,
  ARx ly S Hp W mem md ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a) ->
  astk_ok LLVMF_STK (c_ly cx) (spZ (c_regs cx)) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 26 = w64 SB ->
  getr regs 28 = w64 (c_p cx + wr_k1 cx m) ->
  In (c_p cx, c_n cx) (ablocks B ly S) ->
  garr8 segs (arm W mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  c_n cx = Z.of_nat (length (c_pl cx)) -> 0 < c_n cx < 2 ^ 26 ->
  0 <= wr_k1 cx m -> wr_k1 cx m + 1 <= c_n cx ->
  st_ok_pi segs VAL (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0))) wr_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs wr_Bx (wr_SH 1) (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0))) (mrestrict (w_H W) mem).
Proof.
  intros cx m ly S Hp W regs mem md HAR Hpres Hstk R2 R9 R26 R28 Hin Hg Hlen Hcn Hk0 Hk2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _).
  pose proof (wr_F_mod32 cx) as HFm. pose proof (wr_F_range cx) as HFr.
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil, Hpapp.
  set (b0 := in_byte cx (wr_k1 cx m)).
  assert (Hb0 : 0 <= b0 < 256) by (unfold b0, in_byte; apply u8_range).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (wr_extra b0 0))). pose proof pa_B_ok as HBASE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
  assert (E32 : ew E 32 = Z_to_bv 64 b0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
    by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
  assert (HF46 : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  split.
  - unfold wr_ss1, A_wr_arm. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite (VB 9%nat (lf_F cx) E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. unfold LLVMF_STK in *. lia.
      * rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        apply (chunk_ok_val segs E _ (c_p cx + wr_k1 cx m) 0 1 (SOff 32 0) b0);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat.
        exact (wr_byte cx W mem (wr_k1 cx m) Hg ltac:(lia)).
    + apply pairwise_disjoint_of_extents.
      unfold extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 9%nat (lf_F cx) E9) by lia. rewrite (VB 28%nat (c_p cx + wr_k1 cx m) E28) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold LLVMF_STK in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [wr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E26, E28, E32, E33, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
      unfold SB, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; try lia; try (apply mod32_mod16; exact HFm).
  - unfold sh_ok, wr_SH. constructor; [|constructor].
    destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md (c_p cx) (c_n cx) HAR Hin
      (hp_off_block_hp0 segs ARx HP0 ly S Hp W mem md (c_p cx) (c_n cx) HAR)) as [Hbs _].
    eapply (shent_ok_of_range segs (w_H W) mem E wr_Bx 28 (c_p cx) (c_n cx) (c_p cx + wr_k1 cx m) 0 1).
    + eapply block_shadow_range; [exact Hbs | lia | rewrite Hreq; lia].
    + unfold U, wr_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      cbn [Z.min Z.max] in Hx. lia.
Qed.

(* the entry state at the arm, with no input left: no region of the input, no shadow check *)
Lemma wr_entry0_x : forall (cx : lfcx) (m : lmod) ly S Hp (W : world segs) regs mem md,
  ARx ly S Hp W mem md ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a) ->
  astk_ok LLVMF_STK (c_ly cx) (spZ (c_regs cx)) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 26 = w64 SB ->
  getr regs 28 = w64 (c_p cx + wr_k1 cx m) ->
  In (c_p cx, c_n cx) (ablocks B ly S) -> 0 < c_n cx < 2 ^ 26 ->
  0 <= wr_k1 cx m <= c_n cx ->
  st_ok_pi segs VAL (Eimg (Ereg regs (wr_extra 0 0))) wr_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_wr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs wr_Bx [] (Eimg (Ereg regs (wr_extra 0 0))) (mrestrict (w_H W) mem).
Proof.
  intros cx m ly S Hp W regs mem md HAR Hpres Hstk R2 R9 R26 R28 Hin Hcn Hk0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _).
  pose proof (wr_F_mod32 cx) as HFm. pose proof (wr_F_range cx) as HFr.
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil, Hpapp.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (wr_extra 0 0))). pose proof pa_B_ok as HBASE.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
  assert (E32 : ew E 32 = Z_to_bv 64 0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 0)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
    by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
  assert (HF46 : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  split.
  - unfold wr_ss0, A_wr_arm. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 9%nat (lf_F cx) E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. unfold LLVMF_STK in *. lia.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [wr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E9, E26, E28, E32, E33, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
      unfold SB, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; try lia; try (apply mod32_mod16; exact HFm).
  - unfold sh_ok. constructor.
Qed.
(* a run's write obligation: the in.n cell [F+144, F+152) is in the function's own stack window, every other
   region is read-only *)
Ltac wr_awr U9 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
       first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ] |] ].
(* the bytes a run writes lie in the in.n cell *)
Ltac wr_wr U9 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia;
     rewrite ?U9 in Hr; unfold WR_N; lia |]);
  destruct Hin.
(* after a run: the memory agrees with the arm's entry memory outside the in.n cell, and only grew *)
Ltac wr_upd U9 MEQ MG :=
  lazymatch goal with HFx : frame_of ?Ev ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
  lazymatch goal with HGx : mem_grows (mrestrict H m0) (mrestrict H m1) |- _ =>
    let MEQn := fresh "MEQn" in let MGn := fresh "MGn" in
    lazymatch type of MEQ with forall x, ~ (?lo <= _ < ?hi) -> mrestrict _ _ x = mrestrict _ ?mo x =>
    assert (MEQn : forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m1 x = mrestrict H mo x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          rewrite (wr_frame_win Ev rs _ _ lo hi HFx ltac:(wr_wr U9) x Hx); exact (MEQ x Hx)) end;
    pose proof (wr_mg_trans _ _ _ MG HGx) as MGn;
    clear MEQ MG HFx HGx; rename MEQn into MEQ; rename MGn into MG end end;
  repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end.
Ltac wr_pin Hnew Hold n v :=
  lazymatch goal with
  | HS0 : st_ok_pi _ _ ?Ev _ _ |- _ =>
      assert (Hnew : ew Ev n = Z_to_bv 64 v) by (rewrite ?ew_ewset_other by lia; exact Hold)
  end.
(* the journal's stack window is present *)
Lemma wr_pres_x : forall cx Hp own ly3 S3 Hp3 (W : world segs) mem md k,
  AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 Hp3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a.
Proof.
  intros cx Hp own ly3 S3 Hp3 W mem md k HJ a Ha.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _). exact (Hpr a Ha).
Qed.
(* the cut point 0x84478 (the AR file's :600 WST), over the generic cut *)
Definition WST_x (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + A_wr_tst) regs mem md /\ jt_rom W mem /\
    lcut_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t true (lregs_T B cx t) regs mem md W.
(* everything lcut says of the memory, carried across a run whose only store is the in.n cell (_drain.v
   de_carry) *)
Lemma wr_store_kept_x : forall cx (W : world segs) mem mem' md ly3 S3 Hp3 fpos m,
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + WR_N <= a < lf_F cx + WR_N + 8) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem' /\
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 Hp3 fpos m HAR Hfin Hlen Hsp HFR HFL HMOD HIN HRV HJT KEEP WK.
  pose proof lt_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320) by (pose proof (wr_F_range cx); lia).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold WR_N, CEIL8 in *; lia. }
  split.
  { apply (wr_aframe_kept cx true _ W W mem mem' HFR KEEP WK); unfold CEIL8, SB in *; lia. }
  split; [exact (wrx_amodel_kept ly3 S3 Hp3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (wrx_ainput_kept cx ly3 S3 Hp3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (lt_rom_kept W W mem mem' HRV KL)|].
  split; [exact (lt_jt_kept W W mem mem' HJT KL)|].
  (* the fake frame's flag word (lcut's conjunct after aframe_at): below CEIL8, so kept *)
  unfold sv8 in *. apply (akept_vm W mem); [|exact HFL].
  intros x Hx. apply KL. cbn in Hx. unfold CEIL8, SB in *. lia.
Qed.
(* the facts of the cut point 0x84478, at the memory the walk ends in *)
Lemma wr_mid_facts_x : forall cx Hp t (W : world segs) mem md mem' md' ly3 S3 Hp3 k m fpos regs',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem' md' k ->
  (forall x : word, ~ (lf_F cx + WR_N <= bv_unsigned x < lf_F cx + WR_N + 8) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> jt_rom W mem ->
  lregs_T B cx t m (frame_addr ly3 1 fpos) regs' W mem' ->
  jt_rom W mem' /\ lcut_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t true (lregs_T B cx t) regs' mem' md' W.
Proof.
  intros cx Hp t W mem md mem' md' ly3 S3 Hp3 k m fpos regs' HB HJ HJ' MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HJT HR.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hfp : In (1, fpos) (frames S3)).
  { destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ _ ly3 S3 Hp3 W mem md k HJ) as (memS & HJi & _).
    pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  pose proof HB as (_ & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + WR_N <= a < lf_F cx + WR_N + 8) ->
      abyte_kept W mem W mem' a).
  { intros a Ha Hna. split.
    - apply aview_eq_of. apply MEQ. rewrite unsigned_lit_small by lia. exact Hna.
    - intros Hw. apply (writable_kept (w_H W) mem mem' a); [|exact Hw].
      intros Hpr. exact (wr_pres_grows W mem mem' a MG Hpr). }
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a).
  { intros a Hw. apply (writable_kept (w_H W) mem mem' a); [|exact Hw].
    intros Hpr. exact (wr_pres_grows W mem mem' a MG Hpr). }
  destruct (wr_store_kept_x cx W mem mem' md ly3 S3 Hp3 fpos m HAR Hfp (eq_sym Hnlen) ltac:(unfold LLVMF_STK in *; lia)
              HFR HFL HMOD HIN HRV HJT KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2 & HFL2).
  split; [exact HJT2|].
  exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
  split; [exact HJ'|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
  split; [exact HIN2|].
  split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|]. exact HR.
Qed.
Ltac wr_prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.
(* the registers the walk kept, read off the final symbolic state *)
Ltac wr_kept HS HAE KR2 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    lazymatch type of HAE with env_agree 32 ?er _ =>
      let HAE2 := fresh "HAE2" in
      assert (HAE2 : env_agree 32 er Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]);
      pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ WR_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR2;
      cbn [ms_regs restrict] in KR2; clear HAE2
    end
  end.
(* ------------------------------------------------------------------ fuzz_u16 and fuzz_take (the AR file's :784-1091) *)
(* fuzz_u16 and fuzz_take, 0x843bc-0x84474 *)
Lemma wr_head_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx Hp t W c -> SRr segs W c (WST_x cx Hp t).
Proof.
  intros cx Hp t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  subst own. clear HJOUR.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R6 & R7 & R27 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2' & C3' & C4' & C5).
  (* the operation is 1 *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 1).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 1) with true in HPK.
  destruct HPK as (R28 & R29 & HSRC).
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (wr_k1 cx m) in R28, R29.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (wr_kb cx m) in HSRC.
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  (* the arm's registers are the dispatch's *)
  assert (KR : forall r, In r jt_kept -> getr regs r = getr regsD r) by exact KR0.
  assert (R2 : getr regs 2 = w64 (lf_F cx)) by (rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2).
  assert (R9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26).
  assert (R28' : getr regs 28 = w64 (c_p cx + wr_k1 cx m)) by (rewrite (KR 28%bv ltac:(cbv; tauto)); exact R28).
  assert (R29' : getr regs 29 = w64 (wr_rem cx m)) by (rewrite (KR 29%bv ltac:(cbv; tauto)); exact R29).
  assert (R7' : getr regs 7 = w64 1) by (rewrite (KR 7%bv ltac:(cbv; tauto)); exact R7).
  (* the contract's facts *)
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof (wr_pres_x cx Hp _ ly3 S3 Hp3 W mem md k HJ) as Hpres.
  pose proof HJ as HJ0.
  pose proof HIN as (Hblk & Hg).
  destruct Hblk as [(Hn0 & _) | (Hcn & Hin)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (c_p cx) (c_n cx) HAR Hin) as (_ & Hp4096 & Hpceil & _).
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil.
  pose proof (wr_F_range cx) as HFr. pose proof (wr_F_mod32 cx) as HFm.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  assert (MEQ : forall x : word, ~ (lf_F cx + WR_N <= bv_unsigned x < lf_F cx + WR_N + 8) ->
    mrestrict (w_H W) mem x = mrestrict (w_H W) mem x) by reflexivity.
  assert (MG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem)) by apply mem_grows_refl.
  assert (Hrem : 0 <= wr_rem cx m < 2 ^ 26) by (unfold wr_rem; lia).
  assert (Hb0 : 0 <= in_byte cx (wr_k1 cx m) < 256) by (unfold in_byte; apply u8_range).
  assert (Hb1 : 0 <= in_byte cx (wr_k1 cx m + 1) < 256) by (unfold in_byte; apply u8_range).
  destruct (Z_lt_le_dec (wr_rem cx m) 2) as [Hr2 | Hr2].
  1: destruct (Z.eq_dec (wr_rem cx m) 0) as [Hr0 | Hr1].
  - (* ---- no byte left ---- *)
    destruct (wr_entry0_x cx m ly3 S3 Hp3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hcn ltac:(unfold wr_rem in *; lia))
      as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra 0 0))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra 0 0)) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: taken, no byte left *)
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + clear Hc.
      paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      assert (Mu : wr_u cx m = 0) by (unfold wr_u; rewrite Hr0; reflexivity).
      assert (Mc : wr_c cx m = 0) by (unfold wr_c; rewrite Hr0; reflexivity).
      assert (Mn : wr_n cx m = 0) by (unfold wr_n; rewrite Mu, Mc, Hr0; reflexivity).
      assert (Mk2 : wr_k2 cx m = wr_k1 cx m) by (unfold wr_k2; rewrite Mc, Mn; lia).
      assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m) by (unfold wr_src; rewrite Mc; lia).
      wr_kept HS HAE KR2.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
      wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
        assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
        [ unfold sv8, WR_N;
          eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
          [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
          | apply wr_sv_of_U; [rewrite U_lit by lia; unfold wr_rem in Hr0; lia | unfold wr_rem in Hr0; lia]
          | unfold wr_rem in Hr0; lia | zside ]
        | ];
        assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
          by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [apply U_lit; lia | lia]);
        assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
          by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia]);
        assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
          by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia])
      end.
      pmkst HS. apply SRr_ret.
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|].
      apply (wr_mid_facts_x cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
      exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
  - (* ---- one byte left ---- *)
    destruct (wr_entry1_x cx m ly3 S3 Hp3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hg Hnlen Hcn
      ltac:(lia) ltac:(unfold wr_rem in *; lia)) as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0)) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (E7 : ew E 7 = Z_to_bv 64 1) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7').
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: not taken *)
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      (* the shadow-checked byte read, to 0x843d8 bne t4,t2 *)
      paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      wr_pin A29 E29 29%nat (wr_rem cx m). wr_pin A7 E7 7%nat 1.
      psrr_branch_tok RUN BR HS SHOK wr_Bspan.
      * exfalso. rewrite branch_ne_U, (U_atom _ 29 (wr_rem cx m) A29), (U_atom _ 7 1 A7) in Hc by lia.
        apply Bool.negb_true_iff, Z.eqb_neq in Hc. lia.
      * clear Hc. paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
        wr_upd U9 MEQ MG.
        assert (Hr1' : wr_rem cx m = 1) by lia.
        assert (Mc : wr_c cx m = 1) by (unfold wr_c; rewrite Hr1'; reflexivity).
        assert (Mn : wr_n cx m = 0).
        { unfold wr_n. rewrite Mc, Hr1'. apply Z.min_r. unfold wr_u. rewrite Hr1'.
          destruct (Z.leb_spec 2 1); [lia|]. destruct (Z.eqb_spec 1 1); lia. }
        assert (Mk2 : wr_k2 cx m = wr_k1 cx m + 1) by (unfold wr_k2; rewrite Mc, Mn; lia).
        assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m + 1) by (unfold wr_src; rewrite Mc; lia).
        wr_kept HS HAE KR2.
        pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
        wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
        wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
          assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
          [ unfold sv8, WR_N;
            eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
            [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
            | apply wr_sv_of_U; [rewrite U_lit by lia; unfold wr_rem in Hr1'; lia | unfold wr_rem in Hr1'; lia]
            | unfold wr_rem in Hr1'; lia | zside ]
          | ];
          assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
            by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [apply U_lit; lia | lia]);
          assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
            by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 1 A28) by lia; lia | lia]);
          assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
            by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 1 A28) by lia; lia | lia])
        end.
        pmkst HS. apply SRr_ret.
        lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
        split; [reflexivity|].
        apply (wr_mid_facts_x cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
        exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
  - (* ---- two bytes or more left ---- *)
    destruct (wr_entry2_x cx m ly3 S3 Hp3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hg Hnlen Hcn
      ltac:(lia) ltac:(unfold wr_rem in *; lia)) as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1))))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1)))) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (E7 : ew E 7 = Z_to_bv 64 1) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7').
    assert (E32 : ew E 32 = Z_to_bv 64 (in_byte cx (wr_k1 cx m)))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (E33 : ew E 33 = Z_to_bv 64 (in_byte cx (wr_k1 cx m + 1)))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: not taken *)
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      (* the first shadow-checked byte read, to 0x843d8 bne t4,t2 *)
      paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      wr_pin A29 E29 29%nat (wr_rem cx m). wr_pin A7 E7 7%nat 1.
      psrr_branch_tok RUN BR HS SHOK wr_Bspan.
      * clear Hc.
        (* the second shadow-checked byte read, the u16, to 0x84464 bltu a2,a3 *)
        paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { wr_awr U9. }
        wr_upd U9 MEQ MG.
        wr_pin A32 E32 32%nat (in_byte cx (wr_k1 cx m)).
        wr_pin A33 E33 33%nat (in_byte cx (wr_k1 cx m + 1)).
        wr_pin A29b E29 29%nat (wr_rem cx m).
        assert (Mu : wr_u cx m = in_byte cx (wr_k1 cx m) + 256 * in_byte cx (wr_k1 cx m + 1))
          by (unfold wr_u; rewrite (proj2 (Z.leb_le 2 (wr_rem cx m)) ltac:(lia)); reflexivity).
        assert (Mc : wr_c cx m = 2) by (unfold wr_c; lia).
        assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m + 2) by (unfold wr_src; rewrite Mc; lia).
        psrr_branch_tok RUN BR HS SHOK wr_Bspan.
        -- (* u16 < in.n: n = u16 *)
           rewrite branch_ltu_U, (wr_u16 _ _ _ A32 A33 Hb0 Hb1) in Hc.
           rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29b) in Hc by lia.
           apply Z.ltb_lt in Hc.
           paj_run_to_tok_x RUNTO HS HJ SHOK wr_Bspan A_wr_tst. { wr_awr U9. }
           wr_upd U9 MEQ MG.
           assert (Mn : wr_n cx m = in_byte cx (wr_k1 cx m) + 256 * in_byte cx (wr_k1 cx m + 1))
             by (unfold wr_n; rewrite Mu, Mc; lia).
           assert (Mk2 : wr_k2 cx m = wr_k1 cx m + 2 + wr_n cx m) by (unfold wr_k2; rewrite Mc; lia).
           wr_kept HS HAE KR2.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
           wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
           wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
           wr_pin A32b E32 32%nat (in_byte cx (wr_k1 cx m)).
           wr_pin A33b E33 33%nat (in_byte cx (wr_k1 cx m + 1)).
           wr_pin A29c E29 29%nat (wr_rem cx m).
           lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
             assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
             [ unfold sv8, WR_N;
               eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
               [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
               | apply wr_sv_of_U;
                 [ rewrite U_SAlu, (U_atom_off _ 29 (wr_rem cx m) (-2) A29c), (wr_u16 _ _ _ A32b A33b Hb0 Hb1) by lia;
                   cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; lia); rewrite Mk2, Mn; unfold wr_rem; lia
                 | rewrite Mk2, Mn; unfold wr_rem in *; lia ]
               | rewrite Mk2, Mn; unfold wr_rem in *; lia | zside ]
             | ];
             assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
               by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [exact (wr_u16 _ _ _ A32b A33b Hb0 Hb1) | lia]);
             assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
               by (rewrite Q22, Mk2, Mn; unfold w64; apply wr_sv_of_U;
                   [ rewrite U_SAlu, (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28), (wr_u16 _ _ _ A32b A33b Hb0 Hb1)
                       by lia;
                     cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; unfold wr_rem in *; lia); lia
                   | unfold wr_rem in *; lia ]);
             assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
               by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28) by lia; lia | lia])
           end.
           pmkst HS. apply SRr_ret.
           lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
           split; [reflexivity|].
           apply (wr_mid_facts_x cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
           exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
        -- (* u16 >= in.n: n = in.n *)
           rewrite branch_ltu_U, (wr_u16 _ _ _ A32 A33 Hb0 Hb1) in Hc.
           rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29b) in Hc by lia.
           apply Z.ltb_ge in Hc.
           paj_run_to_tok_x RUNTO HS HJ SHOK wr_Bspan A_wr_tst. { wr_awr U9. }
           wr_upd U9 MEQ MG.
           assert (Mn : wr_n cx m = wr_rem cx m - 2) by (unfold wr_n; rewrite Mu, Mc; lia).
           assert (Mk2 : wr_k2 cx m = c_n cx) by (unfold wr_k2; rewrite Mc, Mn; unfold wr_rem; lia).
           wr_kept HS HAE KR2.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
           wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
           wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
           wr_pin A29c E29 29%nat (wr_rem cx m).
           lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
             assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
             [ unfold sv8, WR_N;
               eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
               [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
               | apply wr_sv_of_U; [rewrite U_lit by lia; lia | lia]
               | lia | zside ]
             | ];
             assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
               by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29c) by lia; lia | lia]);
             assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
               by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U;
                   [ rewrite U_SAlu, (U_atom _ 28 (c_p cx + wr_k1 cx m) A28), (U_atom _ 29 (wr_rem cx m) A29c) by lia;
                     cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; unfold wr_rem in *; lia); unfold wr_rem; lia
                   | lia ]);
             assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
               by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28) by lia; lia | lia])
           end.
           pmkst HS. apply SRr_ret.
           lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
           split; [reflexivity|].
           apply (wr_mid_facts_x cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
           exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
      * exfalso. rewrite branch_ne_U, (U_atom _ 29 (wr_rem cx m) A29), (U_atom _ 7 1 A7) in Hc by lia.
        apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia.
Qed.
(* ------------------------------------------------------------------ 0x8448c li s4,10, to the latch (the AR file's :1114-1217) *)
Definition JST_x (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + A_wr_li) regs mem md /\ jt_rom W mem /\
    lcut_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp (t + 1) true (lregs_K B cx t) regs mem md W.
(* a run over read-only regions leaves the memory as it was (_cut's jt_mem) *)
Ltac wr_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Lemma wr_join_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  JST_x cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  destruct (wj_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs wj_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs wj_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_wr_li)) with (Z_to_bv 64 (BASE + A_wr_li)).
  paj_run_to_tok_x RUNTO HS HJ SHOK wr_Bspan AF_LLVM_latch. { apply awr_ok_x_nil. }
  wr_mem HF Em. clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (20%bv : bv 5) Q20.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht & R22 & SVN & Hk).
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite Q20; reflexivity|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
  split; [exact SVN | exact Hk].
Qed.
(* ------------------------------------------------------------------ what a callee's journal keeps
   (lib/A/W_op_add.v oa_call_keep / oa_call_keep_blk / oa_call_keep_hi and lib/A/W_source_reset.v gx_keep_*, at
   any callee G1: the donor journal's clauses read through ajournal_g's overlay) *)
Lemma wrx_ck_img : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  ajournal_gx_x segs B PST ARx G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP1 ->
  forall a, in_img segs a -> ~ inG G1 a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HJx Hsk a Him HnG Hno He Hpst.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He Hpst ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
Lemma wrx_ck_blk : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 ->
  ajournal_gx_x segs B PST ARx G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP1 (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G1 (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img_x segs B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
Lemma wrx_ck_hi : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 ->
  ajournal_gx_x segs B PST ARx G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK <= a < sp1) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
(* the caller's fake frame and its shadow, outside the callee's FP *)
Lemma wrx_ck_frm : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 -> ARx ly0 S0 Hp0 W0 m0 md0 ->
  ajournal_gx_x segs B PST ARx G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  forall cid pos a, In (cid, pos) (frames S0) ->
  (frame_addr ly0 cid pos <= a < frame_addr ly0 cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly0 cid pos) <= a < shadow_addr (frame_addr ly0 cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP FP1 a -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HAR0 HJx cid pos a Hf Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x segs B ARx LAWS ly0 S0 Hp0 W0 m0 md0 cid pos HAR0 Hf) as (HF1 & HF2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as HFB.
  assert (HSA : SHADOW_OFF <= shadow_addr (frame_addr ly0 cid pos) /\
                shadow_addr (frame_addr ly0 cid pos) + fs_frame_bytes cid / 8 <= SHADOW_OFF + alloc_ceiling).
  { unfold shadow_addr.
    assert (H1 : 0 <= frame_addr ly0 cid pos / 8 <= frame_addr ly0 cid pos)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (H2 : 0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    lia. }
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hf ltac:(unfold frame_rng, in_zr; cbn [fst snd]; exact Ha) Hno).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  unfold SHADOW_OFF in HSA.
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  destruct Ha as [Ha | Ha].
  - destruct (alx_client_img _ _ _ LAWS ly0 S0 Hp0 W0 m0 md0 a HAR0
      ltac:(right; left; exists cid, pos; split; [exact Hf | lia])) as [_ Hni].
    exact (Hni (proj1 (HGok a Hin))).
  - pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
Ltac wr_inG := unfold wr_G, inG;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd fr_RG fr_globals rg_src rg_nsrc rg_capsrc
    rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr rg_gone rg_lock
    rg_wake] in *; unfold AG_NFD, AG_THREAD_UP, AG_LISTEN in *; lia | apply Exists_cons_tl]).
(* the model across list_push: slot si is the pushed source h', every other part is carried (the content of the
   donor's a1c_relay / a1c_out / a1_globals, over the representation of lib/A/W_rep.v) *)
Lemma wrx_amodel_tr : forall ly S Hp (W : world segs) mem md ly' S' (W' : world segs) mem' m (si : nat) h h' OTH
    hs1 hs2 k',
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  lm_hs m = hs1 ++ Some h :: hs2 -> length hs1 = si -> (si < 4)%nat ->
  (forall a, wr_glob (rg_s fr_RG + ASRC * Z.of_nat si) a -> abyte_kept W mem W' mem' a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mem W' mem' a) ->
  (forall b n, In (b, n) OTH -> In (b, n) (ablocks B ly' S') /\
     forall j, 0 <= j < req_size n -> abyte_kept W mem W' mem' (b + j)) ->
  incl ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1) ++
        concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)) OTH ->
  asrc_at B ly' S' W' mem' (rg_s fr_RG + ASRC * Z.of_nat si) h' ->
  amodel_at B ly' S' W' mem' (wr_push m k' si (h') (ct_ev (lm_c m))).
Proof.
  intros ly S Hp W mem md ly' S' W' mem' m si h h' OTH hs1 hs2 k' HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10)
    Ehs Hl1 Hsi KG KE KB Hincl HSRC.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (AK : forall fp (P : Z -> Prop) bl, (forall r, In r fp -> forall a, fst r <= a < snd r -> P a \/ blk_cov bl a) ->
      (forall a, P a -> wr_glob HA a) -> incl bl OTH -> akept W mem W' mem' fp).
  { intros fp P bl HC HP Hbl. apply (wr_akept_cov W W' mem mem' fp P bl HC).
    - intros a Ha. apply KG, HP, Ha.
    - intros b n Hb j Hj. exact (proj2 (KB b n (Hbl _ Hb)) j Hj). }
  assert (KL : forall b, In b OTH -> In b (ablocks B ly' S')) by (intros [b n] Hb; exact (proj1 (KB b n Hb))).
  assert (KGg : forall a, inG wr_G a -> abyte_kept W mem W' mem' a) by (intros a Ha; apply KG; left; exact Ha).
  unfold amodel_at, wr_push. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite set_nth_length; exact M1|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
    - rewrite set_nth_same by (rewrite M1; exact Hi). exact HSRC.
    - rewrite set_nth_other by (intros E; apply Hne; symmetry; exact E).
      specialize (M2 i Hi). unfold aslot in *.
      assert (Hne' : Z.of_nat i <> Z.of_nat si) by lia.
      assert (HGi : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
          wr_glob HA a).
      { intros a Ha. right. unfold HA. unfold fr_RG, ASRC in *. cbn [rg_s fr_globals] in *.
        clear - Ha Hi Hsi Hne'. split; lia. }
      destruct (nth i (lm_hs m) None) as [hj|] eqn:Ehj.
      + apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ hj M2).
        * apply (AK (asrc_fp _ hj) (fun a => rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC)
                    (asrc_blks hj) (wr_cov_asrc B ly S W mem _ hj M2) HGi).
          intros b Hb. apply Hincl.
          assert (Hb' : In b (slot_blks (nth i (hs1 ++ Some h :: hs2) None))) by (rewrite <- Ehs, Ehj; exact Hb).
          destruct (wr_slot_split hs1 hs2 (Some h) i b ltac:(lia) Hb') as [H1 | H2];
            [right; apply in_or_app; right; apply in_or_app; left; exact H1
            | right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact H2].
        * intros b Hb. apply KL. apply Hincl.
          assert (Hb' : In b (slot_blks (nth i (hs1 ++ Some h :: hs2) None))) by (rewrite <- Ehs, Ehj; exact Hb).
          destruct (wr_slot_split hs1 hs2 (Some h) i b ltac:(lia) Hb') as [H1 | H2];
            [right; apply in_or_app; right; apply in_or_app; left; exact H1
            | right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact H2].
      + destruct M2 as [G1 G2]. split.
        * apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
          apply KG, HGi. unfold ASRC in *. lia.
        * apply (akept_awr W mem); [|exact G2]. intros x Hx. apply KG, HGi. lia. }
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ M3).
    - apply (AK _ _ _ (wr_cov_arelay B ly S W mem _ _ M3)); [intros a Ha; apply wr_inG_rel; exact Ha|].
      intros b Hb. apply Hincl. unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
      right. apply in_or_app. left. exact Hb.
    - intros b Hb. apply KL. apply Hincl. unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
      right. apply in_or_app. left. exact Hb. }
  split.
  { destruct (lm_c m) as [cl br dd ei ev]. cbn [set_ev ct_ev].
    apply (aout_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ _ _ _ _ M4).
    - apply (wr_akept_cov W W' mem mem' _ (fun a => inG wr_out_G a \/ (as_errno B <= a < as_errno B + 4))
               (aout_blks (lm_cap m) (lm_out m))).
      + intros r Hr a Ha. destruct (wr_cov_aout B ly S W mem _ _ _ _ _ _ M4 r Hr a Ha) as [H1 | [H1 | H1]];
          [left; left; exact H1 | left; right; exact H1 | right; exact H1].
      + intros a [Ha | Ha]; [apply KG, wr_inG_out, Ha | apply KE, Ha].
      + intros b n Hb j Hj. apply (proj2 (KB b n (Hincl _ ltac:(right; apply in_or_app; right; apply in_or_app;
          right; apply in_or_app; right; exact Hb)))). exact Hj.
    - intros b Hb. apply KL. apply Hincl. right. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hb. }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r Hr a Ha. destruct Hr as [<- | []].
    apply KGg. cbn [fst snd] in Ha. wr_inG. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []].
    apply KGg. cbn [fst snd] in Ha. wr_inG. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r Hr a Ha. destruct Hr as [<- | []].
    apply KGg. cbn [fst snd] in Ha. wr_inG. }
  split; [apply (akept_vm W mem); [intros x Hx; apply KGg; cbn in Hx; wr_inG | exact M8]|].
  destruct M10 as (M11 & M12 & M13 & M14).
  split; [apply (akept_awr W mem); [intros x Hx; apply KGg; wr_inG | exact M9]|].
  split; [exact M11|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KGg; cbn in Hx; wr_inG | exact M12]|].
  split; [destruct M13 as [lst M13]; exists lst;
          apply (akept_vm W mem); [intros x Hx; apply KGg; cbn in Hx; wr_inG | exact M13]|].
  apply (akept_awr W mem); [intros x Hx; apply KGg; wr_inG | exact M14].
Qed.
(* ------------------------------------------------------------------ the live blocks: distinct, one per address *)
(* lib/A/W_gesture_end.v ablocks_nodup *)
Lemma wrx_ablocks_nodup : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S Hp W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
    cbn [snd]. apply req_size_pos. lia. }
  destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hps _]. apply pairwise_app_l in Hps as [Hps _].
  revert Hpos Hps. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hps; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hps. destruct Hps as [Hf Hps]. constructor; [|exact (IH Hl Hps)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* two live blocks at one address are one block (the donor's a1_uniq) *)
Lemma wrx_uniq : forall ly S Hp (W : world segs) mem md p n n', ARx ly S Hp W mem md ->
  In (p, n) (ablocks B ly S) -> In (p, n') (ablocks B ly S) -> n = n'.
Proof.
  intros ly S Hp W mem md p n n' HAR H1 H2. destruct (Z.eq_dec n n') as [E|Hne]; [exact E|]. exfalso.
  pose proof (BLKN ly S Hp W mem md p n HAR H1) as Hn.
  pose proof (BLKN ly S Hp W mem md p n' HAR H2) as Hn'.
  pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos n' ltac:(lia)).
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md p n p n' HAR H1 H2 ltac:(intros E; injection E; lia)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* a live block other than the vector is apart from list_push's FP *)
Lemma wrx_nohit : forall ly S Hp (W : world segs) mem md p n v c, ARx ly S Hp W mem md ->
  In (p, n) (ablocks B ly S) -> In (v, AREC * c) (ablocks B ly S) -> 0 < c -> (p, n) <> (v, AREC * c) ->
  forall j, 0 <= j < req_size n -> ~ inFP [(v, v + AREC * c)] (p + j).
Proof.
  intros ly S Hp W mem md p n v c HAR H1 H2 Hc Hne j Hj (r & Hr & Hra). destruct Hr as [<- | []].
  cbn [fst snd] in Hra.
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md p n v (AREC * c) HAR H1 H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hrq : req_size (AREC * c) = AREC * c) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * c) 0); lia).
  rewrite Hrq in Hd. lia.
Qed.
(* the AR file's :1858 list normaliser (a Section-local Ltac there) *)
Ltac wr_app_norm := repeat (rewrite <- app_assoc || rewrite <- app_comm_cons || rewrite app_nil_l).
(* a concrete register is callee-saved (_latch.v lt_cs, whose Ltac is local to its Section) *)
Ltac wr_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* ------------------------------------------------------------------ 0x84478-0x84488, the list_push call *)
(* the call: list_push(&g_s[si].pending, in.p + k1 + c, n) at 0x85090, back at 0x8448c *)
Lemma wr_call_x : forall cx Hp t (W : world segs) (regs : bvmap 5 word) mem md ly3 S3 Hp3 k m fpos si h,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> jt_rom W mem ->
  lregs_common B cx (frame_addr ly3 1 fpos) regs -> getr regs 27 = w64 t -> 0 <= t < OPS_MAX ->
  getr regs 22 = w64 (c_p cx + wr_k2 cx m) -> sv8 W mem (lf_F cx + WR_N) (c_n cx - wr_k2 cx m) ->
  getr regs 1 = w64 (BASE + A_wr_li) ->
  getr regs 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat si + 16) -> getr regs 11 = w64 (wr_src cx m) ->
  getr regs 12 = w64 (wr_n cx m) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  SRr segs W (cfg_at segs (BASE + AF_fr_list_push) regs mem md) (JST_x cx Hp t).
Proof.
  intros cx Hp t W regs mem md ly3 S3 Hp3 k m fpos si h HB HJ HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM HCOM R27 Ht R22 SVN R1 R10
    R11 R12 Hk HO Hop HPK Hn.
  pose proof HPK as (Hpk & Hsi & Hh).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  pose proof HB as (_ & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (HAR0 & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof (wr_F_range cx) as HFr.
  assert (HFb : (spZ (c_regs cx)) - 352 < lf_F cx <= (spZ (c_regs cx)) - 320) by lia.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (Hsp1 : spZ regs = lf_F cx) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
  (* the journal from the entry to the call *)
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ _ ly3 S3 Hp3 W mem md k HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & HGONE & _).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* slot si and its pending list *)
  pose proof HMOD as (M1 & M2 & _ & M4 & _).
  pose proof (M2 si Hsi) as HS0. unfold aslot in HS0. rewrite Hh in HS0.
  pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
  destruct (@nth_split _ si (lm_hs m) None ltac:(rewrite M1; exact Hsi)) as (hs1 & hs2 & Ehs & Hl1).
  rewrite Hh in Ehs.
  (* the input and fuzz_take's numbers *)
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (wr_n_range cx m ltac:(lia)) as (Hnr & Hc1 & Hc2).
  assert (Hwc0 : 0 <= wr_c cx m) by (unfold wr_c, wr_rem; lia).
  assert (Hlenx : Z.of_nat (length (wr_x cx m)) = wr_n cx m) by (apply wr_x_len; lia).
  pose proof HIN as (Hblk & Hgin).
  destruct Hblk as [(Hz & _) | (Hcn & Hinb)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (c_p cx) (c_n cx) HAR Hinb) as (_ & Hp4096 & Hpceil & _).
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  destruct (LS_write_room cx t m si h ly3 S3 HLS HPK Hn) as (Hroom1 & Hroom2 & Hroom3).
  (* the live blocks: the input, the model with slot si's pending list apart, the rest *)
  destruct HSEP as ((rest0 & Hperm0) & HSEP2).
  assert (EIB : input_blks cx = [(c_p cx, c_n cx)])
    by (unfold input_blks; destruct (Z.eqb_spec (c_n cx) 0); [lia | reflexivity]).
  set (l := hs_pending h) in *.
  set (V := if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]).
  set (R := map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)).
  assert (EAL : alist_blks l = V ++ R) by reflexivity.
  set (A0 := wr_A0 m hs1 h). set (B0 := wr_B0 m hs2 h).
  set (P := [(c_p cx, c_n cx)] ++ A0 ++ R ++ B0 ++ rest0).
  assert (HP3 : Permutation (ablocks B ly3 S3) (V ++ P)).
  { eapply Permutation_trans; [exact Hperm0|]. rewrite EIB, (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
    exact (wr_perm_pre [(c_p cx, c_n cx)] A0 V R B0 rest0). }
  pose proof (Permutation_NoDup HP3 (wrx_ablocks_nodup ly3 S3 Hp3 W mem md HAR)) as HNDVP.
  (* the input block is not the vector *)
  assert (Hqv : c_p cx <> hl_v l).
  { intros E. pose proof HL as (_ & _ & _ & _ & _ & [(_ & Hv0) | (Hcap & Hvin & _)] & _); [lia|].
    pose proof (wrx_uniq ly3 S3 Hp3 W mem md (c_p cx) (c_n cx) (AREC * hl_cap l) HAR Hinb
      ltac:(rewrite E; exact Hvin)) as En.
    apply (wr_nodup_disj V P (c_p cx, c_n cx) HNDVP).
    - unfold V. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0'|Hc0']; [lia|]. left. rewrite E, En. reflexivity.
    - unfold P. apply in_or_app. left. left. reflexivity. }
  (* the bytes list_push copies, read off the input *)
  assert (Hgx : garr8 segs (mrestrict (w_H W) mem) (wr_src cx m) (bzs (wr_x cx m))).
  { unfold wr_src, wr_x.
    replace (c_p cx + wr_k1 cx m + wr_c cx m) with (c_p cx + Z.of_nat (Z.to_nat (wr_k1 cx m + wr_c cx m))) by lia.
    apply wr_garr8_x; [exact Hgin | unfold wr_k2 in Hc2; lia]. }
  (* list_push's afn_pre (wrx_afn_pre_at, the twin of _latch.v lt_afn_pre_at) *)
  destruct (wrx_afn_pre_at cx Hp true ly3 S3 Hp3 fpos k W mem md regs LP_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite R1. apply ret_ok_codeptr_v; [unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite R1. unfold w64.
    rewrite unsigned_lit_small by (unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput in *; lia).
    unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput in *. lia. }
  { exact C3. } { exact C4. } { exact C8. }
  { unfold LP_STK, ASTACK. lia. } { unfold LP_STK, ASTACK, LLVMF_STK. lia. }
  (* the call: lp_spec_g_x (LP) at list_push's own G *)
  eapply SRr_bind.
  { refine (LP (wr_G1 si) (wr_gx_ok1 B G_fr HG HGs si Hsi)
      (wr_gx_rt1 B HERRS si Hsi) W ly3 S3 Hp3 regs mem md ch (wr_LA si) (wr_src cx m) l false (wr_x cx m) (c_p cx) (c_n cx)
      HPREc R10 R11 _ (wr_LA8 si) HL _ (wr_azs1 B HZS si Hsi) Hroom1 _ _ Hinb Hqv _ _ Hgx _ _ _
      (* the room round: the room from the cut's NP (kr := 0), the counts from LS_cnt *)
      0%nat (proj2 (RP_NP S3 _) HNP) _).
    - rewrite Hlenx. exact R12.
    - intros a Ha. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
    - rewrite Hlenx. lia.
    - (* the room round's C3 text: list_push's byte premise at its trace's peak, within LS_write_room's sum
         (W_tr_peak.v lp_tr_peak_le) *)
      rewrite Hlenx.
      assert (Hc0 : 0 <= hl_cap l) by (pose proof HL as (_ & _ & _ & _ & _ & [(Hc & _) | (Hc & _)] & _); lia).
      pose proof (W_tr_peak.lp_tr_peak_le l (wr_n cx m) Hc0 ltac:(lia)) as Htrpk. lia.
    - unfold wr_src. lia.
    - rewrite Hlenx, Hreq. unfold wr_src, wr_k2 in *. lia.
    - discriminate.
    - intros _. lia.
    - rewrite Hlenx. exact Hroom3.
    - rewrite Hlenx. exact (LS_cnt cx t m si h ly3 S3 W mem HLS HRI HPK Hn HMOD Ht). }
  intros W2 c2 Hwle (ly' & S' & Hp' & regs' & mem' & md' & kk & l' & d & -> & HJc & HPRS & HL' & HREC & HCAP & HVV & HPERM
    & HPRES & HERRV & HFRS & HMO & HRM2).
  (* the room after list_push: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S' 0%nat) HRM2) as HNP2.
  rewrite Hsp1 in HJc.
  apply SRr_ret.
  set (n1 := Z.of_nat (length (wr_x cx m)) + 1) in *.
  (* list_push's journal *)
  assert (HAR' : ARx ly' S' Hp' W2 mem' md') by (eapply ajournal_gx_AR_x; exact HJc).
  destruct (ajournal_gx_inner_x segs B PST ARx (wr_G1 si) 0 [] LP_STK _ _ _ _ _ _ _ _ _ ly' S' Hp' W2 mem' md' kk HJc)
    as (memS1 & HJci & _).
  pose proof HJci as (_ & HLY & _).
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. pose proof HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames S')) by (rewrite HFRS; exact Hin1).
  (* the callee's footprint: the vector, a model block, so a temporary block or inside the entry's FP *)
  assert (HFP1 : forall a, inFP (lp_FP l) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    assert (Hvm : In (hl_v l, AREC * hl_cap l) (model_blks m)).
    { rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL. apply in_or_app. right. apply in_or_app. left.
      apply in_or_app. left. unfold V. try rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity. }
    assert (Hrq : req_size (AREC * hl_cap l) = AREC * hl_cap l)
      by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    destruct (HSEP2 _ Hvm) as [Hne | Hall].
    - right. exists (hl_v l), (AREC * hl_cap l). split; [exact Hvin|]. split; [exact Hne|]. rewrite Hrq. lia.
    - left. split; [apply Hall; cbn [fst snd]; lia|].
      exists (hl_v l), (AREC * hl_cap l). split; [exact Hvin | rewrite Hrq; lia]. }
  pose proof (ajournal_gx_G_mono_x segs B PST ARx (wr_G1 si) G_fr 0 [] LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md [] ly' S'
    Hp' W2 mem' md' kk (wr_G1_fr G_fr HGs si Hsi) HJc) as HJcG.
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k
     LP_STK (lf_F cx) 0 [] (lp_FP l) [] ly' S' Hp' W2 mem' md' kk HJ HJcG
     ltac:(unfold LP_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a (r & [] & _)) HG HFP1) as HJ2.
  cbn [app] in HJ2.
  (* ROM and the jump table *)
  pose proof (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low (wr_G1 si) 0 [] LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W
    mem md [] ly' S' Hp' W2 mem' md' kk HJc (wr_rom_out1 B ROM_ERR ROM_PIN si Hsi) PST_ROM HRV) as HRV2.
  pose proof (wr_jt_rom_kept W W2 mem mem' HROM HRV HRV2) as HROM2.
  (* the frame window [F, (spZ (c_regs cx))) and the fake frame *)
  assert (KST : forall a, lf_F cx <= a < (spZ (c_regs cx)) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (wrx_ck_hi (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk
      (wr_gx_ok1 B G_fr HG HGs si Hsi) HJc a); unfold LP_STK, ASTACK, LLVMF_STK in *; lia. }
  pose proof (wr_pres_x cx Hp [(1, fpos)] ly' S' Hp' W2 mem' md' (k + kk) HJ2) as KPR.
  assert (KSTb : forall a, lf_F cx <= a < (spZ (c_regs cx)) -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split; [exact (KST a Ha)|]. intros _. apply (apresent_writable segs). apply KPR.
    unfold LLVMF_STK. lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & HFFapp).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFapp.
  assert (HFF8 : 8 * ((frame_addr ly3 1 fpos) / 8) <= (frame_addr ly3 1 fpos) < 8 * ((frame_addr ly3 1 fpos) / 8) + 8)
    by (pose proof (Z.div_mod (frame_addr ly3 1 fpos) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (frame_addr ly3 1 fpos) 8 ltac:(lia)); lia).
  assert (NFF : forall a, (frame_addr ly3 1 fpos) <= a < (frame_addr ly3 1 fpos) + 128 \/ SB + (frame_addr ly3 1 fpos) / 8 <= a < SB + (frame_addr ly3 1 fpos) / 8 + 16 -> ~ inFP (lp_FP l) a).
  { intros a Ha (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    assert (Hrq : req_size (AREC * hl_cap l) = AREC * hl_cap l)
      by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md _ _ HAR Hvin) as (_ & _ & _ & Hvapp & _).
    rewrite Hrq in Hvapp.
    destruct Ha as [Ha | Ha].
    - pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 Hp3 W mem md _ _ 1 fpos HAR Hvin Hin1) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      clear - Ha Hra Hd. lia.
    - clear - Ha Hra Hvapp HFFapp HFF8 HFF1 CA1. unfold in_app, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  assert (KFF : forall a, (frame_addr ly3 1 fpos) <= a < (frame_addr ly3 1 fpos) + 128 \/ SB + (frame_addr ly3 1 fpos) / 8 <= a < SB + (frame_addr ly3 1 fpos) / 8 + 16 -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split.
    - apply (wrx_ck_frm (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk (wr_gx_ok1 B G_fr HG HGs si Hsi)
        HAR HJc 1 fpos a Hin1); [| exact (NFF a Ha)].
      change (fs_frame_bytes 1) with 128. destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact Ha].
    - intros _. apply (apresent_writable segs).
      destruct (alx_frames _ _ _ LAWS ly' S' Hp' W2 mem' md' 1 fpos HAR' Hin1') as (_ & _ & HP1 & HP2).
      rewrite HFA in HP1, HP2. change (fs_frame_bytes 1) with 128 in HP1, HP2.
      destruct Ha as [Ha | Ha]; [exact (proj1 (HP1 a Ha))|].
      replace a with (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) by ring.
      apply HP2. clear - Ha. unfold shadow_addr, SHADOW_OFF, SB in *. change (128 / 8) with 16. lia. }
  assert (HFR2 : aframe_at cx true (frame_addr ly3 1 fpos) W2 mem').
  { apply (wr_aframe_call cx true (frame_addr ly3 1 fpos) W W2 mem mem' HFR).
    - intros a Ha. apply KST. lia.
    - intros a Ha. apply KPR. unfold LLVMF_STK. lia.
    - exact KFF. }
  (* the fake frame's flag word across list_push: inside KFF's 128 bytes, and ly' keeps ly_F *)
  assert (HFL2 : sv8 W2 mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { assert (EFL : flag_addr ly' 1 fpos = flag_addr ly3 1 fpos).
    { unfold flag_addr. pose proof HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    rewrite EFL. unfold sv8 in *. apply (akept_vm W mem); [|exact HFL].
    intros x Hx. apply KFF. left. cbn in Hx. lia. }
  (* the callee's journal keeps the image bytes the model reads *)
  assert (HSK : ~ YI16.sink_open_fp (lp_FP l)).
  { intros (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md _ _ HAR Hvin) as (_ & Hv4096 & _). lia. }
  assert (KG : forall a, wr_glob (rg_s fr_RG + ASRC * Z.of_nat si) a -> abyte_kept W mem W2 mem' a).
  { intros a Ha.
    assert (HaG : inG G_fr a) by (destruct Ha as [Ha | [Ha _]]; [exact (HGW a Ha) | exact (HGs a Ha)]).
    assert (HaE : ~ (as_errno B <= a < as_errno B + 4)).
    { apply HERRS. apply inG_cons.
      destruct Ha as [Ha | [Ha _]]; [right; exact Ha | left; unfold in_zr; cbn [fst snd]; lia]. }
    assert (HaN : ~ inG (wr_G1 si) a).
    { intros H1. destruct (wr_G1_gs si a Hsi H1) as [H1a H1b]. destruct Ha as [Ha | [_ Ha]].
      - exact (wr_G_gs a Ha H1b).
      - apply Ha. unfold wr_LA, ASRC in *. lia. }
    split.
    - exact (wrx_ck_img (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk HJc HSK a
        (proj1 (HG a HaG)) HaN (proj1 (proj2 (HG a HaG))) HaE (PST_GFR a HaG)).
    - intros _. exact (GWR (w_H W2) mem' a HaG). }
  assert (KE : forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split.
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HERRV. lia.
    - intros _. destruct (ERR ly' S' Hp' W2 mem' md' HAR') as [_ Hw].
      replace a with (as_errno B + (a - as_errno B)) by lia. apply Hw. lia. }
  (* the live blocks after the call *)
  set (V' := if hl_cap l' =? 0 then [] else [(hl_v l', AREC * hl_cap l')]).
  assert (HP' : Permutation (ablocks B ly' S') ([(d, n1)] ++ V' ++ P)).
  { unfold V'. clear HJc HJcG HJ2 HJci.
    destruct (lp_grow l) eqn:Eg.
    - assert (Hc' : hl_cap l' <> 0).
      { rewrite HCAP. unfold grow_cap. unfold lp_grow in Eg. rewrite Eg. destruct (Z.eqb_spec (hl_cap l) 0); lia. }
      rewrite (proj2 (Z.eqb_neq _ _) Hc'). try rewrite Eg in HPERM.
      destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0].
      + try rewrite (proj2 (Z.eqb_eq _ _) Hc0) in HPERM. cbn [andb negb] in HPERM.
        apply (HPERM P). unfold V in HP3. try rewrite (proj2 (Z.eqb_eq _ _) Hc0) in HP3. exact HP3.
      + try rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HPERM. cbn [andb negb] in HPERM.
        apply (HPERM P). unfold V in HP3. try rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HP3. exact HP3.
    - assert (Hc' : hl_cap l' = hl_cap l).
      { rewrite HCAP. unfold grow_cap. unfold lp_grow in Eg. rewrite Eg. reflexivity. }
      assert (Hv' : hl_v l' = hl_v l) by (apply HVV; first [exact Eg | reflexivity]).
      rewrite Hc', Hv'. fold V. try rewrite Eg in HPERM. cbn [andb] in HPERM.
      apply (HPERM (V ++ P)). exact HP3. }
  pose proof (Permutation_NoDup HP' (wrx_ablocks_nodup ly' S' Hp' W2 mem' md' HAR')) as HNDP'.
  assert (EAL' : alist_blks l' = V' ++ R ++ [(d, n1)]).
  { unfold alist_blks, V', R, n1. rewrite HREC, map_app. reflexivity. }
  (* a block live at and after the call, not the vector, is kept *)
  assert (KBLK : forall b n, In (b, n) (ablocks B ly3 S3) -> In (b, n) (ablocks B ly' S') -> ~ In (b, n) V ->
     forall j, 0 <= j < req_size n -> abyte_kept W mem W2 mem' (b + j)).
  { intros b n H3 H' HnV j Hj. split.
    - apply (wrx_ck_blk (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk
        (wr_gx_ok1 B G_fr HG HGs si Hsi) HJc b n j H3 H' Hj).
      intros (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
      refine (wrx_nohit ly3 S3 Hp3 W mem md b n (hl_v l) (hl_cap l) HAR H3 Hvin Hcp _ j Hj _).
      + intros E. apply HnV. unfold V. try rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. symmetry. exact E.
      + exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity | exact Hra].
    - intros _. apply (apresent_writable segs).
      destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W2 mem' md' b n HAR' H') as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr (b + j) ltac:(lia))). }
  assert (HXP : forall b, In b (A0 ++ B0) -> In b P).
  { intros b Hb. unfold P. apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; right; apply in_or_app;
      [left; exact Hb | right; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
  assert (KBX : forall b n, In (b, n) (A0 ++ B0) -> In (b, n) (ablocks B ly' S') /\
     forall j, 0 <= j < req_size n -> abyte_kept W mem W2 mem' (b + j)).
  { intros b n Hb. pose proof (HXP _ Hb) as HbP.
    assert (H3 : In (b, n) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HP3)); apply in_or_app; right; exact HbP).
    assert (H' : In (b, n) (ablocks B ly' S'))
      by (apply (Permutation_in _ (Permutation_sym HP')); apply in_or_app; right; apply in_or_app; right; exact HbP).
    split; [exact H'|]. apply KBLK; [exact H3 | exact H' |]. intros HV. exact (wr_nodup_disj V P (b, n) HNDVP HV HbP). }
  (* the input after the call *)
  assert (Hinb' : In (c_p cx, c_n cx) (ablocks B ly' S')).
  { apply (Permutation_in _ (Permutation_sym HP')). apply in_or_app. right. apply in_or_app. right.
    unfold P. apply in_or_app. left. left. reflexivity. }
  assert (HIN2 : ainput_at B cx ly' S' W2 mem').
  { split; [right; split; [exact Hcn | exact Hinb'] |].
    apply (akept_garr8 W mem); [| exact Hgin]. intros a Ha. rewrite length_map, <- HlenP in Ha.
    replace a with (c_p cx + (a - c_p cx)) by lia.
    eapply KBLK; [exact Hinb | exact Hinb' | | rewrite Hreq; lia].
    intros HV. apply (wr_nodup_disj V P (c_p cx, c_n cx) HNDVP HV). unfold P. apply in_or_app. left. left. reflexivity. }
  (* slot si after the call: list_push's l' as its pending list *)
  set (A1 := (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1)).
  set (S2 := concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)).
  set (L' := alist_blks l' ++ [(hs_partial h, APARTIAL)] ++ alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  assert (HPL : Permutation ([(d, n1)] ++ V' ++ P) (L' ++ ([(c_p cx, c_n cx)] ++ A1 ++ S2 ++ rest0))).
  { assert (EA0 : A0 = A1 ++ [(hs_partial h, APARTIAL)]) by (unfold A0, A1, wr_A0; wr_app_norm; reflexivity).
    assert (EB0 : B0 = alist_blks (hs_expected h) ++ alist_blks (hs_held h) ++ S2) by reflexivity.
    unfold P, L'. rewrite EA0, EB0, EAL'.
    exact (wr_perm_src (d, n1) (hs_partial h, APARTIAL) V' [(c_p cx, c_n cx)] A1 R
      (alist_blks (hs_expected h)) (alist_blks (hs_held h)) S2 rest0). }
  assert (HL'in : forall b, In b L' -> In b (ablocks B ly' S')).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP')). apply (Permutation_in _ (Permutation_sym HPL)).
    apply in_or_app. left. exact Hb. }
  assert (HNDH : NoDup (hs_blocks (set_pending h l'))).
  { assert (EL : hs_blocks (set_pending h l') = map fst L').
    { unfold hs_blocks, L'. cbn [set_pending hs_pending hs_partial hs_expected hs_held].
      rewrite !map_app, !wr_map_fst_alist_blks. reflexivity. }
    rewrite EL. apply NoDup_ListNoDup. apply NoDup_map_NoDup_ForallPairs.
    - intros [b1 n1'] [b2 n2'] Hb1 Hb2 Eb. cbn [fst] in Eb. subst b2.
      f_equal. exact (wrx_uniq ly' S' Hp' W2 mem' md' b1 n1' n2' HAR' (HL'in _ Hb1) (HL'in _ Hb2)).
    - exact (wr_nodup_app_l L' _ (Permutation_NoDup HPL HNDP')). }
  assert (HSRC' : asrc_at B ly' S' W2 mem' (rg_s fr_RG + ASRC * Z.of_nat si) (set_pending h l')).
  { apply (wr_asrc_push B ly3 S3 W mem ly' S' W2 mem' (rg_s fr_RG + ASRC * Z.of_nat si) h l' d (wr_x cx m) HS0).
    - intros a Ha1 Ha2. apply KG. right. split; [|exact Ha2].
      unfold ASRC in *. assert (Z.of_nat si <= 3) by lia. lia.
    - intros a Ha1. apply (GWR (w_H W2) mem' a). apply HGs.
      unfold ASRC in *. assert (Z.of_nat si <= 3) by lia. lia.
    - intros b n Hb. apply KBX. apply in_app_iff. unfold A0, B0, wr_A0, wr_B0.
      destruct Hb as [Hb | Hb].
      + left. right. apply in_app_iff. right. apply in_app_iff. right. left. exact Hb.
      + right. apply in_app_iff in Hb as [Hb | Hb]; apply in_app_iff;
          [left; exact Hb | right; apply in_app_iff; left; exact Hb].
    - exact HL'.
    - exact HREC.
    - lia.
    - exact HNDH. }
  (* the model after the call *)
  assert (Hincl : incl ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1) ++
        concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)) (A0 ++ B0)).
  { intros b Hb. unfold A0, B0, wr_A0, wr_B0. destruct Hb as [<- | Hb]; [left; reflexivity|].
    right.
    apply in_app_iff in Hb as [Hb | Hb];
      [apply in_app_iff; left; apply in_app_iff; left; exact Hb|].
    apply in_app_iff in Hb as [Hb | Hb];
      [apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hb|].
    apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hb.
    - apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact Hb. }
  pose proof (wrx_amodel_tr ly3 S3 Hp3 W mem md ly' S' W2 mem' m si h (set_pending h l') (A0 ++ B0) hs1 hs2 (wr_k2 cx m)
    HAR HMOD Ehs Hl1 Hsi KG KE KBX Hincl HSRC') as HMOD2.
  (* the separation after the call *)
  assert (NB : forall b, In b ([(d, n1)] ++ V') -> ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
      (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)).
  { intros [b n] Hb.
    destruct (in_dec zz_dec (b, n) (ablocks B (c_ly cx) (c_S cx))) as [Hen | Hen]; [|left; exact Hen].
    destruct (in_dec zz_dec (b, n) (ablocks B ly3 S3)) as [H3 | H3].
    - apply (Permutation_in _ HP3) in H3. apply in_app_iff in H3 as [HV | HPb].
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
        apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact HV.
      + exfalso. apply (wr_nodup_disj ([(d, n1)] ++ V') P (b, n)); [rewrite <- app_assoc; exact HNDP' | exact Hb | exact HPb].
    - right. intros a Ha. cbn [fst snd] in Ha.
      pose proof (BLKN (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) b n HAR0 Hen) as Hn0.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (b + (a - b)) by lia. apply (HGONE b n (a - b) Hen H3). lia. }
  assert (HSEP' : ablocks_sep B fr_FP cx (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))) ly' S').
  { split.
    - exists rest0. rewrite EIB, (wr_model_split' m hs1 h hs2 (wr_k2 cx m) si l' (ct_ev (lm_c m)) Ehs Hl1), EAL'.
      eapply Permutation_trans; [exact HP'|]. exact (wr_perm_post (d, n1) [(c_p cx, c_n cx)] A0 V' R B0 rest0).
    - intros b Hb. rewrite (wr_model_split' m hs1 h hs2 (wr_k2 cx m) si l' (ct_ev (lm_c m)) Ehs Hl1), EAL' in Hb.
      rewrite !in_app_iff in Hb.
      destruct Hb as [Hb | [[Hb | [Hb | Hb]] | Hb]].
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). apply in_or_app. left. exact Hb.
      + apply NB. apply in_or_app. right. exact Hb.
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
        apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact Hb.
      + apply NB. apply in_or_app. left. exact Hb.
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). apply in_or_app. right. apply in_or_app. right.
        exact Hb. }
  (* LS and the relational invariant *)
  assert (HMO' : mo_le MT S3 S' (lp_cost MT l (wr_n cx m))) by (rewrite <- Hlenx; exact HMO).
  pose proof (LS_write_push cx t m si h l' d (ct_ev (lm_c m)) ly3 S3 ly' S' HLS HPK Hn HREC HCAP HVV HPERM HMO' Ht) as HLS'.
  pose proof (RI_write_push cx t m si h l' d (ct_ev (lm_c m)) HRI Hk Hop HPK Hn HREC HCAP Hev) as HRI'.
  (* the registers list_push preserves *)
  assert (RPK : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r)
    by (intros r Hr; exact (lt_pres regs regs' r HPRS Hr)).
  assert (HRK : lregs_K B cx t (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))) (frame_addr ly3 1 fpos) regs' W2 mem').
  { split.
    { split; [rewrite (RPK 2%bv ltac:(wr_cs)); exact C2|].
      split; [rewrite (RPK 8%bv ltac:(wr_cs)); exact C8|].
      split; [rewrite (RPK 9%bv ltac:(wr_cs)); exact C9|].
      split; [rewrite (RPK 18%bv ltac:(wr_cs)); exact C18|].
      split; [rewrite (RPK 19%bv ltac:(wr_cs)); exact C19|].
      split; [rewrite (RPK 20%bv ltac:(wr_cs)); exact C20|].
      split; [rewrite (RPK 23%bv ltac:(wr_cs)); exact C23|].
      split; [rewrite (RPK 24%bv ltac:(wr_cs)); exact C24|].
      split; [rewrite (RPK 25%bv ltac:(wr_cs)); exact C25|].
      split; [rewrite (RPK 26%bv ltac:(wr_cs)); exact C26|].
      split; [rewrite (RPK 3%bv ltac:(wr_cs)); exact C3|].
      rewrite (RPK 4%bv ltac:(wr_cs)); exact C4. }
    split; [rewrite (RPK 27%bv ltac:(wr_cs)); exact R27|].
    split; [exact Ht|].
    cbn [lm_k wr_push].
    split; [rewrite (RPK 22%bv ltac:(wr_cs)); exact R22|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KSTb; unfold WR_N in *; lia | exact SVN]|].
    lia. }
  (* INV_K's facts at 0x8448c *)
  exists regs', mem', md'.
  split; [unfold cfg_at; rewrite R1; reflexivity|].
  split; [exact HROM2|].
  exists [(1, fpos)], ly', S', Hp', (k + kk), (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))), fpos.
  rewrite HFA.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
  split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP'|]. split; [exact HLS'|]. split; [exact HNP2|].
  split; [exact HRI'|].
  exact HRK.
Qed.
(* 0x84478 beqz s5; 0x8447c beqz a2; addi a0,s5,16; mv a1,t3; jal list_push *)
Lemma wr_tst_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  WST_x cx Hp t W c -> SRr segs W c (JST_x cx Hp t).
Proof.
  intros cx Hp t W c HB (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  destruct HR as (HCOM & R27 & Ht & Hk & HO & Hop & HSRC & R12 & R28 & R22 & SVN).
  pose proof HJ as HJ0.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (wr_n_range cx m ltac:(lia)) as (Hn & Hc1 & Hc2).
  destruct (wt_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs wj_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs wj_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn0; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn0).
  assert (E12 : ew E 12 = Z_to_bv 64 (wr_n cx m)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  clear HE.
  (* the skip: the model after the operation, the cut facts unchanged (no store) *)
  assert (SKIP : forall regs' md', (forall r, In r WJ_KEPT -> getr regs' r = getr regs r) ->
      getr regs' 20 = getr regs 20 ->
      AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md' k ->
      (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
      SRr segs W (cfg_at segs (fr_B0 + A_wr_li) regs' mem md') (JST_x cx Hp t)).
  { intros regs' md' KR R20 HJ' Hsk. apply SRr_ret.
    exists regs', mem, md'. split; [reflexivity|]. split; [exact HROM|].
    exists [(1, fpos)], ly3, S3, Hp3, k, (wr_skip m (wr_k2 cx m)), fpos.
    split; [exact HJ'|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
    split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
    split; [exact (LS_write_skip cx t m ly3 S3 HLS)|].
    split; [exact HNP|].
    split; [exact (RI_write_skip cx t m HRI Hk Hop Hsk)|].
    pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
    split.
    { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact C18|].
      split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite R20; exact C20|].
      split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact C23|].
      split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KR 4%bv ltac:(cbv; tauto)); exact C4. }
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
    split; [exact SVN|]. cbn [wr_skip lm_k]. lia. }
  unfold cfg_at. change (w64 (fr_B0 + A_wr_tst)) with (Z_to_bv 64 (BASE + A_wr_tst)).
  paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { apply awr_ok_x_nil. }
  wr_mem HF Em. clear HF HFr HG0.
  (* 0x84478 beqz s5 *)
  destruct HSRC as [(si & Hpk & R21) | (Hpk & R21)].
  - assert (E21 : ew E 21 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat si))
      by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
    destruct (wr_pick_some (lm_hs m) (wr_kb cx m) si Hpk) as [Hsi [h Hh]].
    pose proof HMOD as (Hlen4 & _). rewrite Hlen4 in Hsi.
    assert (Hs0 : 0 < rg_s fr_RG + ASRC * Z.of_nat si < 2 ^ 64)
      by (unfold fr_RG, ASRC; cbn [rg_s fr_globals]; lia).
    psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom _ 21 _ E21), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      paj_run_tok_x RUN HS HJ SHOK wr_Bspan. { apply awr_ok_x_nil. }
      wr_mem HF Em2. clear HF HFr HG0.
      wr_pin A12 E12 12%nat (wr_n cx m).
      (* 0x8447c beqz a2 *)
      psrr_branch_tok RUN BR HS SHOK wr_Bspan.
      * rewrite branch_eq_U, (U_atom _ 12 _ A12), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
        paj_run_to_tok_x RUNTO HS HJ SHOK wr_Bspan A_wr_li. { apply awr_ok_x_nil. }
        wr_mem HF Em3. clear HF HFr HG0.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
            by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                       | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE2
          ltac:(vm_compute; reflexivity)) as KR.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra [20%bv] HS HAE2
          ltac:(vm_compute; reflexivity) 20%bv ltac:(left; reflexivity)) as K20.
        cbn [ms_regs restrict] in KR, K20.
        pmkst HS. rewrite Em3, Em2, Em in *.
        apply (SKIP _ _ KR K20 HJ). right. exact Hc.
      * rewrite branch_eq_U, (U_atom _ 12 _ A12), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
        paj_run_to_tok_x RUNTO HS HJ SHOK wr_Bspan AF_fr_list_push. { apply awr_ok_x_nil. }
        wr_mem HF Em3. clear HF HFr HG0.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
            by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                       | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra
          [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (1%bv : bv 5) Q1.
        wr_prreg_raw HS (10%bv : bv 5) Q10. wr_prreg_raw HS (11%bv : bv 5) Q11. wr_prreg_raw HS (12%bv : bv 5) Q12.
        assert (E28 : ew E 28 = Z_to_bv 64 (wr_src cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
        wr_pin A21 E21 21%nat (rg_s fr_RG + ASRC * Z.of_nat si).
        wr_pin A28 E28 28%nat (wr_src cx m).
        wr_pin A12b E12 12%nat (wr_n cx m).
        assert (Hsrc : 0 <= wr_src cx m < 2 ^ 64)
          by (pose proof HIN as ([(Hz & _) | (_ & Hin)] & _); [lia|];
              destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md _ _ (ajournal_gx_AR_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _
                _ _ _ ly3 S3 Hp3 W mem md k HJ0) Hin) as (_ & H4096 & Hce & _);
              pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq];
              pose proof asan_consts as (C1 & _); unfold wr_src; lia).
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
          assert (R10 : getr (ms_regs msx) 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat si + 16))
            by (rewrite Q10; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 21 _ 16 A21) by (unfold fr_RG, ASRC; cbn [rg_s fr_globals]; lia); lia
                | unfold fr_RG, ASRC in *; cbn [rg_s fr_globals] in *; lia]);
          assert (R11 : getr (ms_regs msx) 11 = w64 (wr_src cx m))
            by (rewrite Q11; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia]);
          assert (R12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
            by (rewrite Q12; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A12b | lia] | lia])
        end.
        pmkst HS. rewrite Em3, Em2, Em in *.
        pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
        eapply (wr_call_x cx Hp t W _ mem _ ly3 S3 Hp3 k m fpos si h HB HJ HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
        -- split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2|].
           split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact C8|].
           split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9|].
           split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact C18|].
           split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact C19|].
           split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact C20|].
           split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact C23|].
           split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact C24|].
           split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact C25|].
           split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26|].
           split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact C3|].
           rewrite (KR 4%bv ltac:(cbv; tauto)); exact C4.
        -- rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27.
        -- exact Ht.
        -- rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22.
        -- exact SVN.
        -- exact Q1.
        -- exact R10.
        -- exact R11.
        -- exact R12'.
        -- exact Hk.
        -- exact HO.
        -- exact Hop.
        -- split; [exact Hpk | split; [exact Hsi | exact Hh]].
        -- lia.
  - psrr_branch_tok RUN BR HS SHOK wr_Bspan.
    + clear Hc.
      paj_run_to_tok_x RUNTO HS HJ SHOK wr_Bspan A_wr_li. { apply awr_ok_x_nil. }
      wr_mem HF Em2. clear HF HFr HG0.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE2
        ltac:(vm_compute; reflexivity)) as KR.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra [20%bv] HS HAE2
        ltac:(vm_compute; reflexivity) 20%bv ltac:(left; reflexivity)) as K20.
      cbn [ms_regs restrict] in KR, K20.
      pmkst HS. rewrite Em2, Em in *.
      apply (SKIP _ _ KR K20 HJ). left. exact Hpk.
    + exfalso. assert (E21 : ew E 21 = Z_to_bv 64 0) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
      rewrite branch_eq_U, (U_atom _ 21 _ E21), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.
(* ------------------------------------------------------------------ the arm: cut_x's ARM_write (cut_x.v:303) *)
Theorem lf_arm_write_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  eapply SRr_bind; [exact (wr_head_x cx Hp t W c HB HA)|].
  intros W1 c1 _ HT. eapply SRr_bind; [exact (wr_tst_x cx Hp t W1 c1 HB HT)|].
  intros W2 c2 _ HJ. exact (wr_join_x cx Hp t W2 c2 HB HJ).
Qed.
(* ------------------------------------------------------------------ ROUTE R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the arm at a world
   relation R.  The cut's journal runs from the entry, so across earlier operations' frees / reallocs: at R := wle' segs
   RZ_cf it is the re-hiding form, and the arm's invariants are cut_x's Section wR texts INV_A_xR / INV_K_xR (lcut_xR).
   Each <name>_xR below is <name> above with: the journal AJG -> AJGR (ajournal_gx_xR .. R), lcut_x / INV_A_x / INV_K_x ->
   cut_x's lcut_xR / INV_A_xR / INV_K_xR, the journal lemmas -> their _xR twins (W_journal_x.v, YCbqG.v afn_pre_x_atR,
   W_frame_x.v aview_above_of_journal_xR).  The two straight-line segments (wr_head_xR, wr_join_xR) are the strict walks
   over the R journal (W_journal_x.v paj_run_x_xR / paj_run_to_x_xR, concluding SRr), lifted by SRr_SRrG (WLE_R).  The
   segment with the call (wr_tst_xR, wr_call_xR) concludes SRrG segs R: its runs are the G runs (paj_run_x_xG /
   paj_run_to_x_xG with W_kit_x.v's paj_run_tok_xR / paj_run_to_tok_xR), its branches W_kit.v's paj_branch_xR, the call
   list_push's R contract LP_R composed by SRrG_bind (R_trans), its post journal by ajournal_gx_sub_xR (R_trans), the
   returns SRrG_ret (R_refl).  Every other token is the strict text's (wr_call_x's local list R is renamed Rr).  The
   AR-free and ARx-only helpers above (wr_entry*_x, wr_store_kept_x, wrx_amodel_tr, ...) are cited. *)
Section wrxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* list_push's contract at its own G, at R (W_contract_xR.v:235; a Theorem Labs lane's pb_list_push_g_xR proves it): list_push
   reallocs its vector, and a realloc that frees re-hides the dead shadow.  It replaces LP *)
Hypothesis LP_R : lp_spec_g_xR (PI := PB_fr) B PST ARx R MT RP WR_MMAX (BASE + AF_fr_list_push).
Local Notation AJGR := (ajournal_gx_xR segs B PST ARx R G_fr 0 []).
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (PI := PB_fr) (R := R).
(* wrx_afn_pre_at at R; its proof runs with the zify flag true, as the strict one above (before the flag is set false) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma wrx_afn_pre_at_xR : forall cx Hp full ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hp full ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* wr_pres_x at R *)
Lemma wr_pres_xR : forall cx Hp own ly3 S3 Hp3 (W : world segs) mem md k,
  AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 Hp3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a.
Proof.
  intros cx Hp own ly3 S3 Hp3 W mem md k HJ a Ha.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _). exact (Hpr a Ha).
Qed.
(* WST_x at R: the cut point 0x84478 over cut_x's lcut_xR *)
Definition WST_xR (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + A_wr_tst) regs mem md /\ jt_rom W mem /\
    lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t true (lregs_T B cx t) regs mem md W.
(* JST_x at R: 0x8448c over cut_x's lcut_xR *)
Definition JST_xR (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + A_wr_li) regs mem md /\ jt_rom W mem /\
    lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp (t + 1) true (lregs_K B cx t) regs mem md W.
(* wr_mid_facts_x at R *)
Lemma wr_mid_facts_xR : forall cx Hp t (W : world segs) mem md mem' md' ly3 S3 Hp3 k m fpos regs',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem' md' k ->
  (forall x : word, ~ (lf_F cx + WR_N <= bv_unsigned x < lf_F cx + WR_N + 8) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> jt_rom W mem ->
  lregs_T B cx t m (frame_addr ly3 1 fpos) regs' W mem' ->
  jt_rom W mem' /\ lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t true (lregs_T B cx t) regs' mem' md' W.
Proof.
  intros cx Hp t W mem md mem' md' ly3 S3 Hp3 k m fpos regs' HB HJ HJ' MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HJT HR.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfp : In (1, fpos) (frames S3)).
  { destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ _ ly3 S3 Hp3 W mem md k HJ) as (memS & HJi & _).
    pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  pose proof HB as (_ & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + WR_N <= a < lf_F cx + WR_N + 8) ->
      abyte_kept W mem W mem' a).
  { intros a Ha Hna. split.
    - apply aview_eq_of. apply MEQ. rewrite unsigned_lit_small by lia. exact Hna.
    - intros Hw. apply (writable_kept (w_H W) mem mem' a); [|exact Hw].
      intros Hpr. exact (wr_pres_grows W mem mem' a MG Hpr). }
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a).
  { intros a Hw. apply (writable_kept (w_H W) mem mem' a); [|exact Hw].
    intros Hpr. exact (wr_pres_grows W mem mem' a MG Hpr). }
  destruct (wr_store_kept_x cx W mem mem' md ly3 S3 Hp3 fpos m HAR Hfp (eq_sym Hnlen) ltac:(unfold LLVMF_STK in *; lia)
              HFR HFL HMOD HIN HRV HJT KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2 & HFL2).
  split; [exact HJT2|].
  exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
  split; [exact HJ'|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
  split; [exact HIN2|].
  split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|]. exact HR.
Qed.
(* wr_head_x at R: fuzz_u16 and fuzz_take, 0x843bc-0x84474, a strict walk over the R journal (RUNR / RUNTOR) *)
Lemma wr_head_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx Hp t W c -> SRr segs W c (WST_xR cx Hp t).
Proof.
  intros cx Hp t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  subst own. clear HJOUR.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R6 & R7 & R27 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2' & C3' & C4' & C5).
  (* the operation is 1 *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 1).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 1) with true in HPK.
  destruct HPK as (R28 & R29 & HSRC).
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (wr_k1 cx m) in R28, R29.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (wr_kb cx m) in HSRC.
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  (* the arm's registers are the dispatch's *)
  assert (KR : forall r, In r jt_kept -> getr regs r = getr regsD r) by exact KR0.
  assert (R2 : getr regs 2 = w64 (lf_F cx)) by (rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2).
  assert (R9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26).
  assert (R28' : getr regs 28 = w64 (c_p cx + wr_k1 cx m)) by (rewrite (KR 28%bv ltac:(cbv; tauto)); exact R28).
  assert (R29' : getr regs 29 = w64 (wr_rem cx m)) by (rewrite (KR 29%bv ltac:(cbv; tauto)); exact R29).
  assert (R7' : getr regs 7 = w64 1) by (rewrite (KR 7%bv ltac:(cbv; tauto)); exact R7).
  (* the contract's facts *)
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof (wr_pres_xR cx Hp _ ly3 S3 Hp3 W mem md k HJ) as Hpres.
  pose proof HJ as HJ0.
  pose proof HIN as (Hblk & Hg).
  destruct Hblk as [(Hn0 & _) | (Hcn & Hin)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (c_p cx) (c_n cx) HAR Hin) as (_ & Hp4096 & Hpceil & _).
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreq in Hpceil.
  pose proof (wr_F_range cx) as HFr. pose proof (wr_F_mod32 cx) as HFm.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  assert (MEQ : forall x : word, ~ (lf_F cx + WR_N <= bv_unsigned x < lf_F cx + WR_N + 8) ->
    mrestrict (w_H W) mem x = mrestrict (w_H W) mem x) by reflexivity.
  assert (MG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem)) by apply mem_grows_refl.
  assert (Hrem : 0 <= wr_rem cx m < 2 ^ 26) by (unfold wr_rem; lia).
  assert (Hb0 : 0 <= in_byte cx (wr_k1 cx m) < 256) by (unfold in_byte; apply u8_range).
  assert (Hb1 : 0 <= in_byte cx (wr_k1 cx m + 1) < 256) by (unfold in_byte; apply u8_range).
  destruct (Z_lt_le_dec (wr_rem cx m) 2) as [Hr2 | Hr2].
  1: destruct (Z.eq_dec (wr_rem cx m) 0) as [Hr0 | Hr1].
  - (* ---- no byte left ---- *)
    destruct (wr_entry0_x cx m ly3 S3 Hp3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hcn ltac:(unfold wr_rem in *; lia))
      as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra 0 0))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra 0 0)) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: taken, no byte left *)
    psrr_branch_tok RUNR BR HS SHOK wr_Bspan.
    + clear Hc.
      paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      assert (Mu : wr_u cx m = 0) by (unfold wr_u; rewrite Hr0; reflexivity).
      assert (Mc : wr_c cx m = 0) by (unfold wr_c; rewrite Hr0; reflexivity).
      assert (Mn : wr_n cx m = 0) by (unfold wr_n; rewrite Mu, Mc, Hr0; reflexivity).
      assert (Mk2 : wr_k2 cx m = wr_k1 cx m) by (unfold wr_k2; rewrite Mc, Mn; lia).
      assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m) by (unfold wr_src; rewrite Mc; lia).
      wr_kept HS HAE KR2.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
      wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
        assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
        [ unfold sv8, WR_N;
          eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
          [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
          | apply wr_sv_of_U; [rewrite U_lit by lia; unfold wr_rem in Hr0; lia | unfold wr_rem in Hr0; lia]
          | unfold wr_rem in Hr0; lia | zside ]
        | ];
        assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
          by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [apply U_lit; lia | lia]);
        assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
          by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia]);
        assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
          by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia])
      end.
      pmkst HS. apply SRr_ret.
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|].
      apply (wr_mid_facts_xR cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
      exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
  - (* ---- one byte left ---- *)
    destruct (wr_entry1_x cx m ly3 S3 Hp3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hg Hnlen Hcn
      ltac:(lia) ltac:(unfold wr_rem in *; lia)) as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) 0)) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (E7 : ew E 7 = Z_to_bv 64 1) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7').
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: not taken *)
    psrr_branch_tok RUNR BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      (* the shadow-checked byte read, to 0x843d8 bne t4,t2 *)
      paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      wr_pin A29 E29 29%nat (wr_rem cx m). wr_pin A7 E7 7%nat 1.
      psrr_branch_tok RUNR BR HS SHOK wr_Bspan.
      * exfalso. rewrite branch_ne_U, (U_atom _ 29 (wr_rem cx m) A29), (U_atom _ 7 1 A7) in Hc by lia.
        apply Bool.negb_true_iff, Z.eqb_neq in Hc. lia.
      * clear Hc. paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
        wr_upd U9 MEQ MG.
        assert (Hr1' : wr_rem cx m = 1) by lia.
        assert (Mc : wr_c cx m = 1) by (unfold wr_c; rewrite Hr1'; reflexivity).
        assert (Mn : wr_n cx m = 0).
        { unfold wr_n. rewrite Mc, Hr1'. apply Z.min_r. unfold wr_u. rewrite Hr1'.
          destruct (Z.leb_spec 2 1); [lia|]. destruct (Z.eqb_spec 1 1); lia. }
        assert (Mk2 : wr_k2 cx m = wr_k1 cx m + 1) by (unfold wr_k2; rewrite Mc, Mn; lia).
        assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m + 1) by (unfold wr_src; rewrite Mc; lia).
        wr_kept HS HAE KR2.
        pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
        wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
        wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
          assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
          [ unfold sv8, WR_N;
            eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
            [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
            | apply wr_sv_of_U; [rewrite U_lit by lia; unfold wr_rem in Hr1'; lia | unfold wr_rem in Hr1'; lia]
            | unfold wr_rem in Hr1'; lia | zside ]
          | ];
          assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
            by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [apply U_lit; lia | lia]);
          assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
            by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 1 A28) by lia; lia | lia]);
          assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
            by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 1 A28) by lia; lia | lia])
        end.
        pmkst HS. apply SRr_ret.
        lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
        split; [reflexivity|].
        apply (wr_mid_facts_xR cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
        exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
  - (* ---- two bytes or more left ---- *)
    destruct (wr_entry2_x cx m ly3 S3 Hp3 W regs mem md HAR Hpres Hstk R2 R9 R26 R28' Hin Hg Hnlen Hcn
      ltac:(lia) ltac:(unfold wr_rem in *; lia)) as [HS SHOK].
    remember (Eimg (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1))))) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (wr_extra (in_byte cx (wr_k1 cx m)) (in_byte cx (wr_k1 cx m + 1)))) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
      by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
          change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
          apply ew_Ereg_nat; exact Hn).
    assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + wr_k1 cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (wr_rem cx m)) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29').
    assert (E7 : ew E 7 = Z_to_bv 64 1) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7').
    assert (E32 : ew E 32 = Z_to_bv 64 (in_byte cx (wr_k1 cx m)))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (E33 : ew E 33 = Z_to_bv 64 (in_byte cx (wr_k1 cx m + 1)))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
    assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
    clear HE.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 1)) with (Z_to_bv 64 (BASE + A_wr_arm)).
    paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
    wr_upd U9 MEQ MG.
    (* 0x843bc beqz t4: not taken *)
    psrr_branch_tok RUNR BR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 (wr_rem cx m) E29) in Hc by lia.
      rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      (* the first shadow-checked byte read, to 0x843d8 bne t4,t2 *)
      paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
      wr_upd U9 MEQ MG.
      wr_pin A29 E29 29%nat (wr_rem cx m). wr_pin A7 E7 7%nat 1.
      psrr_branch_tok RUNR BR HS SHOK wr_Bspan.
      * clear Hc.
        (* the second shadow-checked byte read, the u16, to 0x84464 bltu a2,a3 *)
        paj_run_tok_x RUNR HS HJ SHOK wr_Bspan. { wr_awr U9. }
        wr_upd U9 MEQ MG.
        wr_pin A32 E32 32%nat (in_byte cx (wr_k1 cx m)).
        wr_pin A33 E33 33%nat (in_byte cx (wr_k1 cx m + 1)).
        wr_pin A29b E29 29%nat (wr_rem cx m).
        assert (Mu : wr_u cx m = in_byte cx (wr_k1 cx m) + 256 * in_byte cx (wr_k1 cx m + 1))
          by (unfold wr_u; rewrite (proj2 (Z.leb_le 2 (wr_rem cx m)) ltac:(lia)); reflexivity).
        assert (Mc : wr_c cx m = 2) by (unfold wr_c; lia).
        assert (Ms : wr_src cx m = c_p cx + wr_k1 cx m + 2) by (unfold wr_src; rewrite Mc; lia).
        psrr_branch_tok RUNR BR HS SHOK wr_Bspan.
        -- (* u16 < in.n: n = u16 *)
           rewrite branch_ltu_U, (wr_u16 _ _ _ A32 A33 Hb0 Hb1) in Hc.
           rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29b) in Hc by lia.
           apply Z.ltb_lt in Hc.
           paj_run_to_tok_x RUNTOR HS HJ SHOK wr_Bspan A_wr_tst. { wr_awr U9. }
           wr_upd U9 MEQ MG.
           assert (Mn : wr_n cx m = in_byte cx (wr_k1 cx m) + 256 * in_byte cx (wr_k1 cx m + 1))
             by (unfold wr_n; rewrite Mu, Mc; lia).
           assert (Mk2 : wr_k2 cx m = wr_k1 cx m + 2 + wr_n cx m) by (unfold wr_k2; rewrite Mc; lia).
           wr_kept HS HAE KR2.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
           wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
           wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
           wr_pin A32b E32 32%nat (in_byte cx (wr_k1 cx m)).
           wr_pin A33b E33 33%nat (in_byte cx (wr_k1 cx m + 1)).
           wr_pin A29c E29 29%nat (wr_rem cx m).
           lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
             assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
             [ unfold sv8, WR_N;
               eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
               [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
               | apply wr_sv_of_U;
                 [ rewrite U_SAlu, (U_atom_off _ 29 (wr_rem cx m) (-2) A29c), (wr_u16 _ _ _ A32b A33b Hb0 Hb1) by lia;
                   cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; lia); rewrite Mk2, Mn; unfold wr_rem; lia
                 | rewrite Mk2, Mn; unfold wr_rem in *; lia ]
               | rewrite Mk2, Mn; unfold wr_rem in *; lia | zside ]
             | ];
             assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
               by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U; [exact (wr_u16 _ _ _ A32b A33b Hb0 Hb1) | lia]);
             assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
               by (rewrite Q22, Mk2, Mn; unfold w64; apply wr_sv_of_U;
                   [ rewrite U_SAlu, (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28), (wr_u16 _ _ _ A32b A33b Hb0 Hb1)
                       by lia;
                     cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; unfold wr_rem in *; lia); lia
                   | unfold wr_rem in *; lia ]);
             assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
               by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28) by lia; lia | lia])
           end.
           pmkst HS. apply SRr_ret.
           lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
           split; [reflexivity|].
           apply (wr_mid_facts_xR cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
           exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
        -- (* u16 >= in.n: n = in.n *)
           rewrite branch_ltu_U, (wr_u16 _ _ _ A32 A33 Hb0 Hb1) in Hc.
           rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29b) in Hc by lia.
           apply Z.ltb_ge in Hc.
           paj_run_to_tok_x RUNTOR HS HJ SHOK wr_Bspan A_wr_tst. { wr_awr U9. }
           wr_upd U9 MEQ MG.
           assert (Mn : wr_n cx m = wr_rem cx m - 2) by (unfold wr_n; rewrite Mu, Mc; lia).
           assert (Mk2 : wr_k2 cx m = c_n cx) by (unfold wr_k2; rewrite Mc, Mn; unfold wr_rem; lia).
           wr_kept HS HAE KR2.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
           wr_prreg_raw HS (12%bv : bv 5) Q12. wr_prreg_raw HS (22%bv : bv 5) Q22. wr_prreg_raw HS (28%bv : bv 5) Q28.
           wr_pin A28 E28 28%nat (c_p cx + wr_k1 cx m).
           wr_pin A29c E29 29%nat (wr_rem cx m).
           lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
             assert (SVN : sv8 W (ms_mem msx) (lf_F cx + WR_N) (c_n cx - wr_k2 cx m));
             [ unfold sv8, WR_N;
               eapply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N _ (c_n cx - wr_k2 cx m) RG0);
               [ rewrite ?ew_ewset_other by lia; exact U9 | left; reflexivity
               | apply wr_sv_of_U; [rewrite U_lit by lia; lia | lia]
               | lia | zside ]
             | ];
             assert (Q12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
               by (rewrite Q12, Mn; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 29 (wr_rem cx m) (-2) A29c) by lia; lia | lia]);
             assert (Q22' : getr (ms_regs msx) 22 = w64 (c_p cx + wr_k2 cx m))
               by (rewrite Q22, Mk2; unfold w64; apply wr_sv_of_U;
                   [ rewrite U_SAlu, (U_atom _ 28 (c_p cx + wr_k1 cx m) A28), (U_atom _ 29 (wr_rem cx m) A29c) by lia;
                     cbn [zalu_raw]; rewrite zcanon_id by (unfold M64; unfold wr_rem in *; lia); unfold wr_rem; lia
                   | lia ]);
             assert (Q28' : getr (ms_regs msx) 28 = w64 (wr_src cx m))
               by (rewrite Q28, Ms; unfold w64; apply wr_sv_of_U;
                   [rewrite (U_atom_off _ 28 (c_p cx + wr_k1 cx m) 2 A28) by lia; lia | lia])
           end.
           pmkst HS. apply SRr_ret.
           lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
           split; [reflexivity|].
           apply (wr_mid_facts_xR cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos _ HB HJ0 HJ MEQ MG HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
           exact (wr_regs_T B XM_LIB XN_LIB RLO cx t m _ regs regsD _ W _ HCOM R27 Ht Hk HO Hop HSRC KR0 KR2 Q12' Q28' Q22' SVN).
      * exfalso. rewrite branch_ne_U, (U_atom _ 29 (wr_rem cx m) A29), (U_atom _ 7 1 A7) in Hc by lia.
        apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia.
Qed.
(* wr_join_x at R: 0x8448c li s4,10, to the latch, a strict walk over the R journal (RUNTOR) *)
Lemma wr_join_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  JST_xR cx Hp t W c -> SRr segs W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hp t W c HB (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  destruct (wj_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs wj_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs wj_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_wr_li)) with (Z_to_bv 64 (BASE + A_wr_li)).
  paj_run_to_tok_x RUNTOR HS HJ SHOK wr_Bspan AF_LLVM_latch. { apply awr_ok_x_nil. }
  wr_mem HF Em. clear HF HFr HG0.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (20%bv : bv 5) Q20.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht & R22 & SVN & Hk).
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite Q20; reflexivity|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
  split; [exact SVN | exact Hk].
Qed.
(* wrx_ck_img / _blk / _hi / _frm at R: what a callee's journal at R keeps (list_push's post journal is lp_post_xR's) *)
Lemma wrx_ck_img_xR : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  ajournal_gx_xR segs B PST ARx R G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP1 ->
  forall a, in_img segs a -> ~ inG G1 a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HJx Hsk a Him HnG Hno He Hpst.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He Hpst ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
Lemma wrx_ck_blk_xR : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 ->
  ajournal_gx_xR segs B PST ARx R G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP1 (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G1 (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img_x segs B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
Lemma wrx_ck_hi_xR : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 ->
  ajournal_gx_xR segs B PST ARx R G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK <= a < sp1) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
Lemma wrx_ck_frm_xR : forall G1 STK sp1 FP1 ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G1 -> ARx ly0 S0 Hp0 W0 m0 md0 ->
  ajournal_gx_xR segs B PST ARx R G1 0 [] STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  forall cid pos a, In (cid, pos) (frames S0) ->
  (frame_addr ly0 cid pos <= a < frame_addr ly0 cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly0 cid pos) <= a < shadow_addr (frame_addr ly0 cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP FP1 a -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G1 STK sp1 FP1 ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HAR0 HJx cid pos a Hf Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x segs B ARx LAWS ly0 S0 Hp0 W0 m0 md0 cid pos HAR0 Hf) as (HF1 & HF2 & _).
  pose proof (fs_frame_bytes_nonneg cid) as HFB.
  assert (HSA : SHADOW_OFF <= shadow_addr (frame_addr ly0 cid pos) /\
                shadow_addr (frame_addr ly0 cid pos) + fs_frame_bytes cid / 8 <= SHADOW_OFF + alloc_ceiling).
  { unfold shadow_addr.
    assert (H1 : 0 <= frame_addr ly0 cid pos / 8 <= frame_addr ly0 cid pos)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (H2 : 0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    lia. }
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hf ltac:(unfold frame_rng, in_zr; cbn [fst snd]; exact Ha) Hno).
  apply (aview_gagree segs G1 (w_H W0) m0 memS a HAG).
  unfold SHADOW_OFF in HSA.
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  destruct Ha as [Ha | Ha].
  - destruct (alx_client_img _ _ _ LAWS ly0 S0 Hp0 W0 m0 md0 a HAR0
      ltac:(right; left; exists cid, pos; split; [exact Hf | lia])) as [_ Hni].
    exact (Hni (proj1 (HGok a Hin))).
  - pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
(* wr_call_x at R: the call list_push(&g_s[si].pending, in.p + k1 + c, n) at 0x85090, back at 0x8448c, by LP_R, composed
   by SRrG_bind (R_trans); list_push's post journal (at R) into the cut's by ajournal_gx_sub_xR (R_trans) *)
Lemma wr_call_xR : forall cx Hp t (W : world segs) (regs : bvmap 5 word) mem md ly3 S3 Hp3 k m fpos si h,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> jt_rom W mem ->
  lregs_common B cx (frame_addr ly3 1 fpos) regs -> getr regs 27 = w64 t -> 0 <= t < OPS_MAX ->
  getr regs 22 = w64 (c_p cx + wr_k2 cx m) -> sv8 W mem (lf_F cx + WR_N) (c_n cx - wr_k2 cx m) ->
  getr regs 1 = w64 (BASE + A_wr_li) ->
  getr regs 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat si + 16) -> getr regs 11 = w64 (wr_src cx m) ->
  getr regs 12 = w64 (wr_n cx m) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  SRrG segs R W (cfg_at segs (BASE + AF_fr_list_push) regs mem md) (JST_xR cx Hp t).
Proof.
  intros cx Hp t W regs mem md ly3 S3 Hp3 k m fpos si h HB HJ HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM HCOM R27 Ht R22 SVN R1 R10
    R11 R12 Hk HO Hop HPK Hn.
  pose proof HPK as (Hpk & Hsi & Hh).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  pose proof HB as (_ & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (HAR0 & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof (wr_F_range cx) as HFr.
  assert (HFb : (spZ (c_regs cx)) - 352 < lf_F cx <= (spZ (c_regs cx)) - 320) by lia.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (Hsp1 : spZ regs = lf_F cx) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
  (* the journal from the entry to the call *)
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ _ ly3 S3 Hp3 W mem md k HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & HGONE & _).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* slot si and its pending list *)
  pose proof HMOD as (M1 & M2 & _ & M4 & _).
  pose proof (M2 si Hsi) as HS0. unfold aslot in HS0. rewrite Hh in HS0.
  pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
  destruct (@nth_split _ si (lm_hs m) None ltac:(rewrite M1; exact Hsi)) as (hs1 & hs2 & Ehs & Hl1).
  rewrite Hh in Ehs.
  (* the input and fuzz_take's numbers *)
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (wr_n_range cx m ltac:(lia)) as (Hnr & Hc1 & Hc2).
  assert (Hwc0 : 0 <= wr_c cx m) by (unfold wr_c, wr_rem; lia).
  assert (Hlenx : Z.of_nat (length (wr_x cx m)) = wr_n cx m) by (apply wr_x_len; lia).
  pose proof HIN as (Hblk & Hgin).
  destruct Hblk as [(Hz & _) | (Hcn & Hinb)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (c_p cx) (c_n cx) HAR Hinb) as (_ & Hp4096 & Hpceil & _).
  assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  destruct (LS_write_room cx t m si h ly3 S3 HLS HPK Hn) as (Hroom1 & Hroom2 & Hroom3).
  (* the live blocks: the input, the model with slot si's pending list apart, the rest *)
  destruct HSEP as ((rest0 & Hperm0) & HSEP2).
  assert (EIB : input_blks cx = [(c_p cx, c_n cx)])
    by (unfold input_blks; destruct (Z.eqb_spec (c_n cx) 0); [lia | reflexivity]).
  set (l := hs_pending h) in *.
  set (V := if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]).
  set (Rr := map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)).
  assert (EAL : alist_blks l = V ++ Rr) by reflexivity.
  set (A0 := wr_A0 m hs1 h). set (B0 := wr_B0 m hs2 h).
  set (P := [(c_p cx, c_n cx)] ++ A0 ++ Rr ++ B0 ++ rest0).
  assert (HP3 : Permutation (ablocks B ly3 S3) (V ++ P)).
  { eapply Permutation_trans; [exact Hperm0|]. rewrite EIB, (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
    exact (wr_perm_pre [(c_p cx, c_n cx)] A0 V Rr B0 rest0). }
  pose proof (Permutation_NoDup HP3 (wrx_ablocks_nodup ly3 S3 Hp3 W mem md HAR)) as HNDVP.
  (* the input block is not the vector *)
  assert (Hqv : c_p cx <> hl_v l).
  { intros E. pose proof HL as (_ & _ & _ & _ & _ & [(_ & Hv0) | (Hcap & Hvin & _)] & _); [lia|].
    pose proof (wrx_uniq ly3 S3 Hp3 W mem md (c_p cx) (c_n cx) (AREC * hl_cap l) HAR Hinb
      ltac:(rewrite E; exact Hvin)) as En.
    apply (wr_nodup_disj V P (c_p cx, c_n cx) HNDVP).
    - unfold V. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0'|Hc0']; [lia|]. left. rewrite E, En. reflexivity.
    - unfold P. apply in_or_app. left. left. reflexivity. }
  (* the bytes list_push copies, read off the input *)
  assert (Hgx : garr8 segs (mrestrict (w_H W) mem) (wr_src cx m) (bzs (wr_x cx m))).
  { unfold wr_src, wr_x.
    replace (c_p cx + wr_k1 cx m + wr_c cx m) with (c_p cx + Z.of_nat (Z.to_nat (wr_k1 cx m + wr_c cx m))) by lia.
    apply wr_garr8_x; [exact Hgin | unfold wr_k2 in Hc2; lia]. }
  (* list_push's afn_pre (wrx_afn_pre_at_xR) *)
  destruct (wrx_afn_pre_at_xR cx Hp true ly3 S3 Hp3 fpos k W mem md regs LP_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite R1. apply ret_ok_codeptr_v; [unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite R1. unfold w64.
    rewrite unsigned_lit_small by (unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput in *; lia).
    unfold A_wr_li, AF_fr_LLVMFuzzerTestOneInput in *. lia. }
  { exact C3. } { exact C4. } { exact C8. }
  { unfold LP_STK, ASTACK. lia. } { unfold LP_STK, ASTACK, LLVMF_STK. lia. }
  (* the call: lp_spec_g_xR (LP_R) at list_push's own G *)
  eapply (SRrG_bind segs R R_trans).
  { refine (LP_R (wr_G1 si) (wr_gx_ok1 B G_fr HG HGs si Hsi)
      (wr_gx_rt1 B HERRS si Hsi) W ly3 S3 Hp3 regs mem md ch (wr_LA si) (wr_src cx m) l false (wr_x cx m) (c_p cx) (c_n cx)
      HPREc R10 R11 _ (wr_LA8 si) HL _ (wr_azs1 B HZS si Hsi) Hroom1 _ _ Hinb Hqv _ _ Hgx _ _ _
      (* the room round: the room from the cut's NP (kr := 0), the counts from LS_cnt *)
      0%nat (proj2 (RP_NP S3 _) HNP) _).
    - rewrite Hlenx. exact R12.
    - intros a Ha. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
    - rewrite Hlenx. lia.
    - (* the room round's C3 text: list_push's byte premise at its trace's peak, within LS_write_room's sum
         (W_tr_peak.v lp_tr_peak_le) *)
      rewrite Hlenx.
      assert (Hc0 : 0 <= hl_cap l) by (pose proof HL as (_ & _ & _ & _ & _ & [(Hc & _) | (Hc & _)] & _); lia).
      pose proof (W_tr_peak.lp_tr_peak_le l (wr_n cx m) Hc0 ltac:(lia)) as Htrpk. lia.
    - unfold wr_src. lia.
    - rewrite Hlenx, Hreq. unfold wr_src, wr_k2 in *. lia.
    - discriminate.
    - intros _. lia.
    - rewrite Hlenx. exact Hroom3.
    - rewrite Hlenx. exact (LS_cnt cx t m si h ly3 S3 W mem HLS HRI HPK Hn HMOD Ht). }
  intros W2 c2 HRW (ly' & S' & Hp' & regs' & mem' & md' & kk & l' & d & -> & HJc & HPRS & HL' & HREC & HCAP & HVV & HPERM
    & HPRES & HERRV & HFRS & HMO & HRM2).
  (* the room after list_push: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S' 0%nat) HRM2) as HNP2.
  rewrite Hsp1 in HJc.
  apply (SRrG_ret segs R R_refl).
  set (n1 := Z.of_nat (length (wr_x cx m)) + 1) in *.
  (* list_push's journal *)
  assert (HAR' : ARx ly' S' Hp' W2 mem' md') by (eapply ajournal_gx_AR_xR; exact HJc).
  destruct (ajournal_gx_inner_xR segs B PST ARx (wr_G1 si) 0 [] LP_STK _ _ _ _ _ _ _ _ _ ly' S' Hp' W2 mem' md' kk HJc)
    as (memS1 & HJci & _).
  pose proof HJci as (_ & HLY & _).
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. pose proof HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames S')) by (rewrite HFRS; exact Hin1).
  (* the callee's footprint: the vector, a model block, so a temporary block or inside the entry's FP *)
  assert (HFP1 : forall a, inFP (lp_FP l) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    assert (Hvm : In (hl_v l, AREC * hl_cap l) (model_blks m)).
    { rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL. apply in_or_app. right. apply in_or_app. left.
      apply in_or_app. left. unfold V. try rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity. }
    assert (Hrq : req_size (AREC * hl_cap l) = AREC * hl_cap l)
      by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    destruct (HSEP2 _ Hvm) as [Hne | Hall].
    - right. exists (hl_v l), (AREC * hl_cap l). split; [exact Hvin|]. split; [exact Hne|]. rewrite Hrq. lia.
    - left. split; [apply Hall; cbn [fst snd]; lia|].
      exists (hl_v l), (AREC * hl_cap l). split; [exact Hvin | rewrite Hrq; lia]. }
  pose proof (ajournal_gx_G_mono_xR segs B PST ARx (wr_G1 si) G_fr 0 [] LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md [] ly' S'
    Hp' W2 mem' md' kk (wr_G1_fr G_fr HGs si Hsi) HJc) as HJcG.
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k
     LP_STK (lf_F cx) 0 [] (lp_FP l) [] ly' S' Hp' W2 mem' md' kk HJ HJcG
     ltac:(unfold LP_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a (r & [] & _)) HG HFP1) as HJ2.
  cbn [app] in HJ2.
  (* ROM and the jump table *)
  pose proof (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low (wr_G1 si) 0 [] LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W
    mem md [] ly' S' Hp' W2 mem' md' kk HJc (wr_rom_out1 B ROM_ERR ROM_PIN si Hsi) PST_ROM HRV) as HRV2.
  pose proof (wr_jt_rom_kept W W2 mem mem' HROM HRV HRV2) as HROM2.
  (* the frame window [F, (spZ (c_regs cx))) and the fake frame *)
  assert (KST : forall a, lf_F cx <= a < (spZ (c_regs cx)) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (wrx_ck_hi_xR (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk
      (wr_gx_ok1 B G_fr HG HGs si Hsi) HJc a); unfold LP_STK, ASTACK, LLVMF_STK in *; lia. }
  pose proof (wr_pres_xR cx Hp [(1, fpos)] ly' S' Hp' W2 mem' md' (k + kk) HJ2) as KPR.
  assert (KSTb : forall a, lf_F cx <= a < (spZ (c_regs cx)) -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split; [exact (KST a Ha)|]. intros _. apply (apresent_writable segs). apply KPR.
    unfold LLVMF_STK. lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & HFFapp).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFapp.
  assert (HFF8 : 8 * ((frame_addr ly3 1 fpos) / 8) <= (frame_addr ly3 1 fpos) < 8 * ((frame_addr ly3 1 fpos) / 8) + 8)
    by (pose proof (Z.div_mod (frame_addr ly3 1 fpos) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (frame_addr ly3 1 fpos) 8 ltac:(lia)); lia).
  assert (NFF : forall a, (frame_addr ly3 1 fpos) <= a < (frame_addr ly3 1 fpos) + 128 \/ SB + (frame_addr ly3 1 fpos) / 8 <= a < SB + (frame_addr ly3 1 fpos) / 8 + 16 -> ~ inFP (lp_FP l) a).
  { intros a Ha (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    assert (Hrq : req_size (AREC * hl_cap l) = AREC * hl_cap l)
      by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md _ _ HAR Hvin) as (_ & _ & _ & Hvapp & _).
    rewrite Hrq in Hvapp.
    destruct Ha as [Ha | Ha].
    - pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 Hp3 W mem md _ _ 1 fpos HAR Hvin Hin1) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      clear - Ha Hra Hd. lia.
    - clear - Ha Hra Hvapp HFFapp HFF8 HFF1 CA1. unfold in_app, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  assert (KFF : forall a, (frame_addr ly3 1 fpos) <= a < (frame_addr ly3 1 fpos) + 128 \/ SB + (frame_addr ly3 1 fpos) / 8 <= a < SB + (frame_addr ly3 1 fpos) / 8 + 16 -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split.
    - apply (wrx_ck_frm_xR (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk (wr_gx_ok1 B G_fr HG HGs si Hsi)
        HAR HJc 1 fpos a Hin1); [| exact (NFF a Ha)].
      change (fs_frame_bytes 1) with 128. destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact Ha].
    - intros _. apply (apresent_writable segs).
      destruct (alx_frames _ _ _ LAWS ly' S' Hp' W2 mem' md' 1 fpos HAR' Hin1') as (_ & _ & HP1 & HP2).
      rewrite HFA in HP1, HP2. change (fs_frame_bytes 1) with 128 in HP1, HP2.
      destruct Ha as [Ha | Ha]; [exact (proj1 (HP1 a Ha))|].
      replace a with (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) by ring.
      apply HP2. clear - Ha. unfold shadow_addr, SHADOW_OFF, SB in *. change (128 / 8) with 16. lia. }
  assert (HFR2 : aframe_at cx true (frame_addr ly3 1 fpos) W2 mem').
  { apply (wr_aframe_call cx true (frame_addr ly3 1 fpos) W W2 mem mem' HFR).
    - intros a Ha. apply KST. lia.
    - intros a Ha. apply KPR. unfold LLVMF_STK. lia.
    - exact KFF. }
  (* the fake frame's flag word across list_push: inside KFF's 128 bytes, and ly' keeps ly_F *)
  assert (HFL2 : sv8 W2 mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { assert (EFL : flag_addr ly' 1 fpos = flag_addr ly3 1 fpos).
    { unfold flag_addr. pose proof HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    rewrite EFL. unfold sv8 in *. apply (akept_vm W mem); [|exact HFL].
    intros x Hx. apply KFF. left. cbn in Hx. lia. }
  (* the callee's journal keeps the image bytes the model reads *)
  assert (HSK : ~ YI16.sink_open_fp (lp_FP l)).
  { intros (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
    destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md _ _ HAR Hvin) as (_ & Hv4096 & _). lia. }
  assert (KG : forall a, wr_glob (rg_s fr_RG + ASRC * Z.of_nat si) a -> abyte_kept W mem W2 mem' a).
  { intros a Ha.
    assert (HaG : inG G_fr a) by (destruct Ha as [Ha | [Ha _]]; [exact (HGW a Ha) | exact (HGs a Ha)]).
    assert (HaE : ~ (as_errno B <= a < as_errno B + 4)).
    { apply HERRS. apply inG_cons.
      destruct Ha as [Ha | [Ha _]]; [right; exact Ha | left; unfold in_zr; cbn [fst snd]; lia]. }
    assert (HaN : ~ inG (wr_G1 si) a).
    { intros H1. destruct (wr_G1_gs si a Hsi H1) as [H1a H1b]. destruct Ha as [Ha | [_ Ha]].
      - exact (wr_G_gs a Ha H1b).
      - apply Ha. unfold wr_LA, ASRC in *. lia. }
    split.
    - exact (wrx_ck_img_xR (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk HJc HSK a
        (proj1 (HG a HaG)) HaN (proj1 (proj2 (HG a HaG))) HaE (PST_GFR a HaG)).
    - intros _. exact (GWR (w_H W2) mem' a HaG). }
  assert (KE : forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mem W2 mem' a).
  { intros a Ha. split.
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HERRV. lia.
    - intros _. destruct (ERR ly' S' Hp' W2 mem' md' HAR') as [_ Hw].
      replace a with (as_errno B + (a - as_errno B)) by lia. apply Hw. lia. }
  (* the live blocks after the call *)
  set (V' := if hl_cap l' =? 0 then [] else [(hl_v l', AREC * hl_cap l')]).
  assert (HP' : Permutation (ablocks B ly' S') ([(d, n1)] ++ V' ++ P)).
  { unfold V'. clear HJc HJcG HJ2 HJci.
    destruct (lp_grow l) eqn:Eg.
    - assert (Hc' : hl_cap l' <> 0).
      { rewrite HCAP. unfold grow_cap. unfold lp_grow in Eg. rewrite Eg. destruct (Z.eqb_spec (hl_cap l) 0); lia. }
      rewrite (proj2 (Z.eqb_neq _ _) Hc'). try rewrite Eg in HPERM.
      destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0].
      + try rewrite (proj2 (Z.eqb_eq _ _) Hc0) in HPERM. cbn [andb negb] in HPERM.
        apply (HPERM P). unfold V in HP3. try rewrite (proj2 (Z.eqb_eq _ _) Hc0) in HP3. exact HP3.
      + try rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HPERM. cbn [andb negb] in HPERM.
        apply (HPERM P). unfold V in HP3. try rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HP3. exact HP3.
    - assert (Hc' : hl_cap l' = hl_cap l).
      { rewrite HCAP. unfold grow_cap. unfold lp_grow in Eg. rewrite Eg. reflexivity. }
      assert (Hv' : hl_v l' = hl_v l) by (apply HVV; first [exact Eg | reflexivity]).
      rewrite Hc', Hv'. fold V. try rewrite Eg in HPERM. cbn [andb] in HPERM.
      apply (HPERM (V ++ P)). exact HP3. }
  pose proof (Permutation_NoDup HP' (wrx_ablocks_nodup ly' S' Hp' W2 mem' md' HAR')) as HNDP'.
  assert (EAL' : alist_blks l' = V' ++ Rr ++ [(d, n1)]).
  { unfold alist_blks, V', Rr, n1. rewrite HREC, map_app. reflexivity. }
  (* a block live at and after the call, not the vector, is kept *)
  assert (KBLK : forall b n, In (b, n) (ablocks B ly3 S3) -> In (b, n) (ablocks B ly' S') -> ~ In (b, n) V ->
     forall j, 0 <= j < req_size n -> abyte_kept W mem W2 mem' (b + j)).
  { intros b n H3 H' HnV j Hj. split.
    - apply (wrx_ck_blk_xR (wr_G1 si) LP_STK (lf_F cx) (lp_FP l) ly3 S3 Hp3 W mem md ly' S' Hp' W2 mem' md' kk
        (wr_gx_ok1 B G_fr HG HGs si Hsi) HJc b n j H3 H' Hj).
      intros (r & Hr & Hra). unfold lp_FP in Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      pose proof HL as (_ & _ & _ & _ & _ & [(Hcz & _) | (Hcp & Hvin & _)] & _); [lia|].
      refine (wrx_nohit ly3 S3 Hp3 W mem md b n (hl_v l) (hl_cap l) HAR H3 Hvin Hcp _ j Hj _).
      + intros E. apply HnV. unfold V. try rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. symmetry. exact E.
      + exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity | exact Hra].
    - intros _. apply (apresent_writable segs).
      destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W2 mem' md' b n HAR' H') as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr (b + j) ltac:(lia))). }
  assert (HXP : forall b, In b (A0 ++ B0) -> In b P).
  { intros b Hb. unfold P. apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; right; apply in_or_app;
      [left; exact Hb | right; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
  assert (KBX : forall b n, In (b, n) (A0 ++ B0) -> In (b, n) (ablocks B ly' S') /\
     forall j, 0 <= j < req_size n -> abyte_kept W mem W2 mem' (b + j)).
  { intros b n Hb. pose proof (HXP _ Hb) as HbP.
    assert (H3 : In (b, n) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HP3)); apply in_or_app; right; exact HbP).
    assert (H' : In (b, n) (ablocks B ly' S'))
      by (apply (Permutation_in _ (Permutation_sym HP')); apply in_or_app; right; apply in_or_app; right; exact HbP).
    split; [exact H'|]. apply KBLK; [exact H3 | exact H' |]. intros HV. exact (wr_nodup_disj V P (b, n) HNDVP HV HbP). }
  (* the input after the call *)
  assert (Hinb' : In (c_p cx, c_n cx) (ablocks B ly' S')).
  { apply (Permutation_in _ (Permutation_sym HP')). apply in_or_app. right. apply in_or_app. right.
    unfold P. apply in_or_app. left. left. reflexivity. }
  assert (HIN2 : ainput_at B cx ly' S' W2 mem').
  { split; [right; split; [exact Hcn | exact Hinb'] |].
    apply (akept_garr8 W mem); [| exact Hgin]. intros a Ha. rewrite length_map, <- HlenP in Ha.
    replace a with (c_p cx + (a - c_p cx)) by lia.
    eapply KBLK; [exact Hinb | exact Hinb' | | rewrite Hreq; lia].
    intros HV. apply (wr_nodup_disj V P (c_p cx, c_n cx) HNDVP HV). unfold P. apply in_or_app. left. left. reflexivity. }
  (* slot si after the call: list_push's l' as its pending list *)
  set (A1 := (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1)).
  set (S2 := concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)).
  set (L' := alist_blks l' ++ [(hs_partial h, APARTIAL)] ++ alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  assert (HPL : Permutation ([(d, n1)] ++ V' ++ P) (L' ++ ([(c_p cx, c_n cx)] ++ A1 ++ S2 ++ rest0))).
  { assert (EA0 : A0 = A1 ++ [(hs_partial h, APARTIAL)]) by (unfold A0, A1, wr_A0; wr_app_norm; reflexivity).
    assert (EB0 : B0 = alist_blks (hs_expected h) ++ alist_blks (hs_held h) ++ S2) by reflexivity.
    unfold P, L'. rewrite EA0, EB0, EAL'.
    exact (wr_perm_src (d, n1) (hs_partial h, APARTIAL) V' [(c_p cx, c_n cx)] A1 Rr
      (alist_blks (hs_expected h)) (alist_blks (hs_held h)) S2 rest0). }
  assert (HL'in : forall b, In b L' -> In b (ablocks B ly' S')).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP')). apply (Permutation_in _ (Permutation_sym HPL)).
    apply in_or_app. left. exact Hb. }
  assert (HNDH : NoDup (hs_blocks (set_pending h l'))).
  { assert (EL : hs_blocks (set_pending h l') = map fst L').
    { unfold hs_blocks, L'. cbn [set_pending hs_pending hs_partial hs_expected hs_held].
      rewrite !map_app, !wr_map_fst_alist_blks. reflexivity. }
    rewrite EL. apply NoDup_ListNoDup. apply NoDup_map_NoDup_ForallPairs.
    - intros [b1 n1'] [b2 n2'] Hb1 Hb2 Eb. cbn [fst] in Eb. subst b2.
      f_equal. exact (wrx_uniq ly' S' Hp' W2 mem' md' b1 n1' n2' HAR' (HL'in _ Hb1) (HL'in _ Hb2)).
    - exact (wr_nodup_app_l L' _ (Permutation_NoDup HPL HNDP')). }
  assert (HSRC' : asrc_at B ly' S' W2 mem' (rg_s fr_RG + ASRC * Z.of_nat si) (set_pending h l')).
  { apply (wr_asrc_push B ly3 S3 W mem ly' S' W2 mem' (rg_s fr_RG + ASRC * Z.of_nat si) h l' d (wr_x cx m) HS0).
    - intros a Ha1 Ha2. apply KG. right. split; [|exact Ha2].
      unfold ASRC in *. assert (Z.of_nat si <= 3) by lia. lia.
    - intros a Ha1. apply (GWR (w_H W2) mem' a). apply HGs.
      unfold ASRC in *. assert (Z.of_nat si <= 3) by lia. lia.
    - intros b n Hb. apply KBX. apply in_app_iff. unfold A0, B0, wr_A0, wr_B0.
      destruct Hb as [Hb | Hb].
      + left. right. apply in_app_iff. right. apply in_app_iff. right. left. exact Hb.
      + right. apply in_app_iff in Hb as [Hb | Hb]; apply in_app_iff;
          [left; exact Hb | right; apply in_app_iff; left; exact Hb].
    - exact HL'.
    - exact HREC.
    - lia.
    - exact HNDH. }
  (* the model after the call *)
  assert (Hincl : incl ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs1) ++
        concat (map slot_blks hs2) ++ aout_blks (lm_cap m) (lm_out m)) (A0 ++ B0)).
  { intros b Hb. unfold A0, B0, wr_A0, wr_B0. destruct Hb as [<- | Hb]; [left; reflexivity|].
    right.
    apply in_app_iff in Hb as [Hb | Hb];
      [apply in_app_iff; left; apply in_app_iff; left; exact Hb|].
    apply in_app_iff in Hb as [Hb | Hb];
      [apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hb|].
    apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hb.
    - apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact Hb. }
  pose proof (wrx_amodel_tr ly3 S3 Hp3 W mem md ly' S' W2 mem' m si h (set_pending h l') (A0 ++ B0) hs1 hs2 (wr_k2 cx m)
    HAR HMOD Ehs Hl1 Hsi KG KE KBX Hincl HSRC') as HMOD2.
  (* the separation after the call *)
  assert (NB : forall b, In b ([(d, n1)] ++ V') -> ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
      (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)).
  { intros [b n] Hb.
    destruct (in_dec zz_dec (b, n) (ablocks B (c_ly cx) (c_S cx))) as [Hen | Hen]; [|left; exact Hen].
    destruct (in_dec zz_dec (b, n) (ablocks B ly3 S3)) as [H3 | H3].
    - apply (Permutation_in _ HP3) in H3. apply in_app_iff in H3 as [HV | HPb].
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
        apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact HV.
      + exfalso. apply (wr_nodup_disj ([(d, n1)] ++ V') P (b, n)); [rewrite <- app_assoc; exact HNDP' | exact Hb | exact HPb].
    - right. intros a Ha. cbn [fst snd] in Ha.
      pose proof (BLKN (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) b n HAR0 Hen) as Hn0.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (b + (a - b)) by lia. apply (HGONE b n (a - b) Hen H3). lia. }
  assert (HSEP' : ablocks_sep B fr_FP cx (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))) ly' S').
  { split.
    - exists rest0. rewrite EIB, (wr_model_split' m hs1 h hs2 (wr_k2 cx m) si l' (ct_ev (lm_c m)) Ehs Hl1), EAL'.
      eapply Permutation_trans; [exact HP'|]. exact (wr_perm_post (d, n1) [(c_p cx, c_n cx)] A0 V' Rr B0 rest0).
    - intros b Hb. rewrite (wr_model_split' m hs1 h hs2 (wr_k2 cx m) si l' (ct_ev (lm_c m)) Ehs Hl1), EAL' in Hb.
      rewrite !in_app_iff in Hb.
      destruct Hb as [Hb | [[Hb | [Hb | Hb]] | Hb]].
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). apply in_or_app. left. exact Hb.
      + apply NB. apply in_or_app. right. exact Hb.
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). fold l. rewrite EAL.
        apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact Hb.
      + apply NB. apply in_or_app. left. exact Hb.
      + apply HSEP2. rewrite (wr_model_split m hs1 h hs2 Ehs). apply in_or_app. right. apply in_or_app. right.
        exact Hb. }
  (* LS and the relational invariant *)
  assert (HMO' : mo_le MT S3 S' (lp_cost MT l (wr_n cx m))) by (rewrite <- Hlenx; exact HMO).
  pose proof (LS_write_push cx t m si h l' d (ct_ev (lm_c m)) ly3 S3 ly' S' HLS HPK Hn HREC HCAP HVV HPERM HMO' Ht) as HLS'.
  pose proof (RI_write_push cx t m si h l' d (ct_ev (lm_c m)) HRI Hk Hop HPK Hn HREC HCAP Hev) as HRI'.
  (* the registers list_push preserves *)
  assert (RPK : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r)
    by (intros r Hr; exact (lt_pres regs regs' r HPRS Hr)).
  assert (HRK : lregs_K B cx t (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))) (frame_addr ly3 1 fpos) regs' W2 mem').
  { split.
    { split; [rewrite (RPK 2%bv ltac:(wr_cs)); exact C2|].
      split; [rewrite (RPK 8%bv ltac:(wr_cs)); exact C8|].
      split; [rewrite (RPK 9%bv ltac:(wr_cs)); exact C9|].
      split; [rewrite (RPK 18%bv ltac:(wr_cs)); exact C18|].
      split; [rewrite (RPK 19%bv ltac:(wr_cs)); exact C19|].
      split; [rewrite (RPK 20%bv ltac:(wr_cs)); exact C20|].
      split; [rewrite (RPK 23%bv ltac:(wr_cs)); exact C23|].
      split; [rewrite (RPK 24%bv ltac:(wr_cs)); exact C24|].
      split; [rewrite (RPK 25%bv ltac:(wr_cs)); exact C25|].
      split; [rewrite (RPK 26%bv ltac:(wr_cs)); exact C26|].
      split; [rewrite (RPK 3%bv ltac:(wr_cs)); exact C3|].
      rewrite (RPK 4%bv ltac:(wr_cs)); exact C4. }
    split; [rewrite (RPK 27%bv ltac:(wr_cs)); exact R27|].
    split; [exact Ht|].
    cbn [lm_k wr_push].
    split; [rewrite (RPK 22%bv ltac:(wr_cs)); exact R22|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KSTb; unfold WR_N in *; lia | exact SVN]|].
    lia. }
  (* INV_K's facts at 0x8448c *)
  exists regs', mem', md'.
  split; [unfold cfg_at; rewrite R1; reflexivity|].
  split; [exact HROM2|].
  exists [(1, fpos)], ly', S', Hp', (k + kk), (wr_push m (wr_k2 cx m) si (set_pending h l') (ct_ev (lm_c m))), fpos.
  rewrite HFA.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
  split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP'|]. split; [exact HLS'|]. split; [exact HNP2|].
  split; [exact HRI'|].
  exact HRK.
Qed.
(* wr_tst_x at R: 0x84478 beqz s5; 0x8447c beqz a2; addi a0,s5,16; mv a1,t3; jal list_push.  The runs and the branches
   conclude SRrG segs R (RUNG / RUNTOG, BRR), since the call arm ends in wr_call_xR *)
Lemma wr_tst_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  WST_xR cx Hp t W c -> SRrG segs R W c (JST_xR cx Hp t).
Proof.
  intros cx Hp t W c HB (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  destruct HR as (HCOM & R27 & Ht & Hk & HO & Hop & HSRC & R12 & R28 & R22 & SVN).
  pose proof HJ as HJ0.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  assert (Hk1 : lm_k m + 1 <= wr_k1 cx m <= c_n cx)
    by (unfold wr_k1; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (wr_n_range cx m ltac:(lia)) as (Hn & Hc1 & Hc2).
  destruct (wt_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs wj_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs wj_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn0; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn0).
  assert (E12 : ew E 12 = Z_to_bv 64 (wr_n cx m)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  clear HE.
  (* the skip: the model after the operation, the cut facts unchanged (no store) *)
  assert (SKIP : forall regs' md', (forall r, In r WJ_KEPT -> getr regs' r = getr regs r) ->
      getr regs' 20 = getr regs 20 ->
      AJGR LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md' k ->
      (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
      SRrG segs R W (cfg_at segs (fr_B0 + A_wr_li) regs' mem md') (JST_xR cx Hp t)).
  { intros regs' md' KR R20 HJ' Hsk. apply (SRrG_ret segs R R_refl).
    exists regs', mem, md'. split; [reflexivity|]. split; [exact HROM|].
    exists [(1, fpos)], ly3, S3, Hp3, k, (wr_skip m (wr_k2 cx m)), fpos.
    split; [exact HJ'|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
    split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
    split; [exact (LS_write_skip cx t m ly3 S3 HLS)|].
    split; [exact HNP|].
    split; [exact (RI_write_skip cx t m HRI Hk Hop Hsk)|].
    pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
    split.
    { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact C18|].
      split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite R20; exact C20|].
      split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact C23|].
      split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KR 4%bv ltac:(cbv; tauto)); exact C4. }
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
    split; [exact SVN|]. cbn [wr_skip lm_k]. lia. }
  unfold cfg_at. change (w64 (fr_B0 + A_wr_tst)) with (Z_to_bv 64 (BASE + A_wr_tst)).
  paj_run_tok_xR RUNG HS HJ SHOK wr_Bspan. { apply awr_ok_x_nil. }
  wr_mem HF Em. clear HF HFr HG0.
  (* 0x84478 beqz s5 *)
  destruct HSRC as [(si & Hpk & R21) | (Hpk & R21)].
  - assert (E21 : ew E 21 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat si))
      by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
    destruct (wr_pick_some (lm_hs m) (wr_kb cx m) si Hpk) as [Hsi [h Hh]].
    pose proof HMOD as (Hlen4 & _). rewrite Hlen4 in Hsi.
    assert (Hs0 : 0 < rg_s fr_RG + ASRC * Z.of_nat si < 2 ^ 64)
      by (unfold fr_RG, ASRC; cbn [rg_s fr_globals]; lia).
    psrr_branch_tok RUNG BRR HS SHOK wr_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom _ 21 _ E21), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + clear Hc.
      paj_run_tok_xR RUNG HS HJ SHOK wr_Bspan. { apply awr_ok_x_nil. }
      wr_mem HF Em2. clear HF HFr HG0.
      wr_pin A12 E12 12%nat (wr_n cx m).
      (* 0x8447c beqz a2 *)
      psrr_branch_tok RUNG BRR HS SHOK wr_Bspan.
      * rewrite branch_eq_U, (U_atom _ 12 _ A12), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
        paj_run_to_tok_xR RUNTOG HS HJ SHOK wr_Bspan A_wr_li. { apply awr_ok_x_nil. }
        wr_mem HF Em3. clear HF HFr HG0.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
            by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                       | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE2
          ltac:(vm_compute; reflexivity)) as KR.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra [20%bv] HS HAE2
          ltac:(vm_compute; reflexivity) 20%bv ltac:(left; reflexivity)) as K20.
        cbn [ms_regs restrict] in KR, K20.
        pmkst HS. rewrite Em3, Em2, Em in *.
        apply (SKIP _ _ KR K20 HJ). right. exact Hc.
      * rewrite branch_eq_U, (U_atom _ 12 _ A12), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
        paj_run_to_tok_xR RUNTOG HS HJ SHOK wr_Bspan AF_fr_list_push. { apply awr_ok_x_nil. }
        wr_mem HF Em3. clear HF HFr HG0.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
            by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                       | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra
          [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (1%bv : bv 5) Q1.
        wr_prreg_raw HS (10%bv : bv 5) Q10. wr_prreg_raw HS (11%bv : bv 5) Q11. wr_prreg_raw HS (12%bv : bv 5) Q12.
        assert (E28 : ew E 28 = Z_to_bv 64 (wr_src cx m)) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
        wr_pin A21 E21 21%nat (rg_s fr_RG + ASRC * Z.of_nat si).
        wr_pin A28 E28 28%nat (wr_src cx m).
        wr_pin A12b E12 12%nat (wr_n cx m).
        assert (Hsrc : 0 <= wr_src cx m < 2 ^ 64)
          by (pose proof HIN as ([(Hz & _) | (_ & Hin)] & _); [lia|];
              destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md _ _ (ajournal_gx_AR_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _
                _ _ _ ly3 S3 Hp3 W mem md k HJ0) Hin) as (_ & H4096 & Hce & _);
              pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq];
              pose proof asan_consts as (C1 & _); unfold wr_src; lia).
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
          assert (R10 : getr (ms_regs msx) 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat si + 16))
            by (rewrite Q10; unfold w64; apply wr_sv_of_U;
                [rewrite (U_atom_off _ 21 _ 16 A21) by (unfold fr_RG, ASRC; cbn [rg_s fr_globals]; lia); lia
                | unfold fr_RG, ASRC in *; cbn [rg_s fr_globals] in *; lia]);
          assert (R11 : getr (ms_regs msx) 11 = w64 (wr_src cx m))
            by (rewrite Q11; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A28 | lia] | lia]);
          assert (R12' : getr (ms_regs msx) 12 = w64 (wr_n cx m))
            by (rewrite Q12; unfold w64; apply wr_sv_of_U; [apply U_atom; [exact A12b | lia] | lia])
        end.
        pmkst HS. rewrite Em3, Em2, Em in *.
        pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
        eapply (wr_call_xR cx Hp t W _ mem _ ly3 S3 Hp3 k m fpos si h HB HJ HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
        -- split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact C2|].
           split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact C8|].
           split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact C9|].
           split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact C18|].
           split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact C19|].
           split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact C20|].
           split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact C23|].
           split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact C24|].
           split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact C25|].
           split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact C26|].
           split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact C3|].
           rewrite (KR 4%bv ltac:(cbv; tauto)); exact C4.
        -- rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27.
        -- exact Ht.
        -- rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22.
        -- exact SVN.
        -- exact Q1.
        -- exact R10.
        -- exact R11.
        -- exact R12'.
        -- exact Hk.
        -- exact HO.
        -- exact Hop.
        -- split; [exact Hpk | split; [exact Hsi | exact Hh]].
        -- lia.
  - psrr_branch_tok RUNG BRR HS SHOK wr_Bspan.
    + clear Hc.
      paj_run_to_tok_xR RUNTOG HS HJ SHOK wr_Bspan A_wr_li. { apply awr_ok_x_nil. }
      wr_mem HF Em2. clear HF HFr HG0.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs wj_extra) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra WJ_KEPT HS HAE2
        ltac:(vm_compute; reflexivity)) as KR.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs wj_extra [20%bv] HS HAE2
        ltac:(vm_compute; reflexivity) 20%bv ltac:(left; reflexivity)) as K20.
      cbn [ms_regs restrict] in KR, K20.
      pmkst HS. rewrite Em2, Em in *.
      apply (SKIP _ _ KR K20 HJ). left. exact Hpk.
    + exfalso. assert (E21 : ew E 21 = Z_to_bv 64 0) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
      rewrite branch_eq_U, (U_atom _ 21 _ E21), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.
(* ------------------------------------------------------------------ the arm at R: cut_x's ARM_write_R (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section
   wR).  head and join are strict walks lifted by SRr_SRrG (WLE_R); the three steps compose by SRrG_bind (R_trans) *)
Theorem lf_arm_write_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx Hp t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R W c _ (wr_head_xR cx Hp t W c HB HA))|].
  intros W1 c1 _ HT. eapply (SRrG_bind segs R R_trans); [exact (wr_tst_xR cx Hp t W1 c1 HB HT)|].
  intros W2 c2 _ HJ. exact (SRr_SRrG segs R WLE_R W2 c2 _ (wr_join_xR cx Hp t W2 c2 HB HJ)).
Qed.
End wrxR.
End wrx.

(* ------------------------------------------------------------------ THE CHECK, in cut_x's scope: at cut_x's Section w
   variables, lf_arm_write_x's type is cut_x's ARM_write hypothesis (cut_x.v:303, restated and closed by `exact`), and the
   theorem fills the ARM_write argument of cut_x's composition lf_contract_of_segments_x (cut_x.v:371). *)
Section check.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2): the allocator rules' room record RP, whose room invariant is the
   cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ => room_live_cf S = NP) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis TL : PALib B.
Hypothesis LP : lp_spec_g_x (PI := PB_fr) B PST ARx MT RP WR_MMAX (BASE + AF_fr_list_push).
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis ERR : errno_law_x B ARx.
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis HGW : forall a, inG wr_G a -> inG G_fr a.
Hypothesis HERRS : forall a, inG ((rg_s fr_RG, 4 * ASRC) :: wr_G) a -> ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ROM_ERR : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ROM_PIN : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Hypothesis PST_GFR : forall a, inG G_fr a -> ~ Exists (in_zr a) PST.
Hypothesis RI_write_skip : forall cx t m,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (wr_kb cx m) = None \/ wr_n cx m = 0) ->
  RINV cx (t + 1) (wr_skip m (wr_k2 cx m)).
Hypothesis LS_write_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Hypothesis RI_write_push : forall cx t m si h l' d ev,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev).
Hypothesis LS_write_room : forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok MT S (lp_cost MT (hs_pending h) (wr_n cx m)).
Hypothesis LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
(* the room round's count row (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c); lib/A/ReplyLScnt.v fr_LS3cp_cnt_write at
   commit ba8e99b5bd2): at the cut, the live counts plus list_push's premise peak lp_peak stay under RP's bounds.  The
   guards are the walk's facts at the cut (the model's sizes come from amodel_at) *)
Hypothesis LS_cnt : forall cx t m si h ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (lp_peak (hs_pending h) (wr_n cx m)) (ablocks B ly S).
(* cut_x.v:303, at Section w's variables *)
Lemma lf_arm_write_x_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  exact (lf_arm_write_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx
    RINV RP RP_NP TL LP GWR ERR HGs HZS HGW HERRS ROM_ERR ROM_PIN BLKN PST_ROM PST_GFR RI_write_skip LS_write_skip RI_write_push
    LS_write_room LS_write_push LS_cnt).
Qed.
(* the theorem in the ARM_write slot of cut_x's composition (cut_x.v:371-373): this term type-checks only if
   lf_arm_write_x's type is convertible to that Section hypothesis *)
Definition lf_arm_write_x_slot :=
  fun SEG_PRO SEG_HEAD ARM_add ARM_drain ARM_close ARM_remove ARM_gone ARM_eintr ARM_event ARM_sendmax ARM_default
      SEG_LATCH SEG_EXIT =>
  @lf_contract_of_segments_x fx rc B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST
    ARx hl LAWS HG LSx RINV SEG_PRO SEG_HEAD ARM_add
    (lf_arm_write_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx
    RINV RP RP_NP TL LP GWR ERR HGs HZS HGW HERRS ROM_ERR ROM_PIN BLKN PST_ROM PST_GFR RI_write_skip LS_write_skip RI_write_push
    LS_write_room LS_write_push LS_cnt)
    ARM_drain ARM_close ARM_remove ARM_gone ARM_eintr ARM_event
    ARM_sendmax ARM_default SEG_LATCH SEG_EXIT.
(* ---- route R: at cut_x's Section wR variables (R and its three laws after Section w's), lf_arm_write_xR's type is
   cut_x's ARM_write_R (restated and closed by `exact`, with the twin's arguments in the order top_x passes them: the
   strict lemma's, LP dropped, then R R_refl R_trans WLE_R LP_R), and the theorem fills the ARM_write_R slot of
   cut_x's composition lf_contract_of_segments_xR ---- *)
Section checkR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis LP_R : lp_spec_g_xR (PI := PB_fr) B PST ARx R MT RP WR_MMAX (BASE + AF_fr_list_push).
(* lib/A/W_LLVMFuzzerTestOneInput_cut_x.v ARM_write_R, at Section wR's variables *)
Lemma lf_arm_write_xR_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx Hp t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  exact (lf_arm_write_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG
    LSx RINV RP RP_NP TL GWR ERR HGs HZS HGW HERRS ROM_ERR ROM_PIN BLKN PST_ROM PST_GFR RI_write_skip LS_write_skip
    RI_write_push LS_write_room LS_write_push LS_cnt R R_refl R_trans WLE_R LP_R).
Qed.
Definition lf_arm_write_xR_slot :=
  fun SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_drain_R ARM_close_R ARM_remove_R ARM_gone_R ARM_eintr_R ARM_event_R
      ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R =>
  @lf_contract_of_segments_xR fx rc B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST
    ARx hl LAWS HG LSx RINV R R_refl R_trans WLE_R SEG_PRO_R SEG_HEAD_R ARM_add_R
    (lf_arm_write_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG
    LSx RINV RP RP_NP TL GWR ERR HGs HZS HGW HERRS ROM_ERR ROM_PIN BLKN PST_ROM PST_GFR RI_write_skip LS_write_skip
    RI_write_push LS_write_room LS_write_push LS_cnt R R_refl R_trans WLE_R LP_R)
    ARM_drain_R ARM_close_R ARM_remove_R ARM_gone_R ARM_eintr_R ARM_event_R
    ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R.
End checkR.
End check.
