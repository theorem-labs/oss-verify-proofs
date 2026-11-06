(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain (op 2) of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's LLVMFuzzerTestOneInput over the GENERIC allocator relation ARx - THE CLOSING FILE of the arm's ARx
   conversion: lf_arm_drain_x, whose statement is the text of the Section hypothesis ARM_drain of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v Section w (:422), checked at the end (lf_arm_drain_x_check).
   The AR proof is a Theorem Labs lane's (a working branch af5c712458a: lib/B/W_LLVMFuzzerTestOneInput_drain.v
   lf_arm_drain over _drain_defs.v / _drain_entry.v / _drain_calls.v); of those four files the room round edits only
   LS_drain_pre's text (drain.v, _drain_defs.v) and its one use (_drain_calls.v dc_stB), as image A's.  Template:
   AddX's lib/A/W_LLVMFuzzerTestOneInput_drain_x.v (W8 integ 60c0b278422), with its HPST / BLKR facts.
   Proves no function (kind: segment walk - a segment of the entry function; its callees are named contracts).
   The conversion, file by file (each the ARx twin of the AR file of the same stem, each Requiring it and citing what
   it can):
     _drain_defs_x.v   DLK over ajournal_gx_x (Hpe at the entry, Hp3 beside S3), the interface record dr_env_x (the
                       callee contracts in their kit _x forms, the facts and rules verbatim, HPST / BLKR);
     _drain_entry_x.v  dr_stage_entry over ARx: RSRC_x (cut_x's relay_source contract) for the AR file's RSRC, the
                       de_ transport kit converted after A's latch_x lt_*_x, the stage lemmas with the ghost lists;
     _drain_calls_x.v  dr_stage_calls over ARx: AddX's dc_st* conversion merged with B's port (per item, 3-way:
                       A's AR item, AddX's ARx item, B's AR item), every in-Section item restated (the AR file
                       generalizes them over its EV and LAWS, so none can be cited);
     this file         the Section hypotheses (each callee contract's kit _x form at the walk's PST / ARx, the
                       G-coverage and image facts and the RI_ / LS_ families in the AR file's text with LS -> LSx,
                       cut_x's RSRC_x and errno_law_x, HPST / BLKR), the bundle dr_EV_x, and lf_arm_drain_x.
   Section hypotheses beyond cut_x's Section w header (B .. RINV, verbatim):
     MMAX / TL / HGs / HG_DR / HGlock / HG_GK / HERR_HI / GWR / DR_ROM_OUT / HZS / HAP / RI_* / LS_* - the AR file's,
       verbatim (LS is cut_x's LSx), except RI_drain_step (restated, below);
     DRAIN / ALOCK / AUNLOCK / CNLR / CSD / CNL - dr_spec_x / alock_realizes_x / aunlock_realizes_x / cnlr_spec_x /
       csd_spec_x / cnl_spec_x at the walk's PST / ARx;  ERR - cut_x's errno_law_x;  RSRC_x - cut_x's (:363);
     HPST - the image is off PST (W_op_add.v Section x's text; trivial at the instance's PST := []);
     BLKR - a live block's request is in [0, 2 ^ 30) (AR's al_blocks carries 0 <= n < MALLOC_MAX = 2 ^ 28, which
       AR_laws_x's alx_blocks does not; the cf instance has 0 <= n < cf_malloc_max as AR_blocks_law_cf's last
       conjunct and cf_malloc_max + 15 <= 2 ^ 30 as YG08cf.v cf_malloc_max_bound).
   THE ROOM ROUND (an internal work row: the image-B twin of W8's A re-fit a working branch b5892edd1cb,
   on the B top a working branch e43cf0c7bef and the B cut's room text a working branch): the
   cut's invariants take NP (lcut_x's NP S after LSx; DLK carries it); DRAIN / CNL take the room record RP (RP_NP ties
   its rp_RM to NP) and their count premises cnt_ok_pk RP (dr_pk ..) / (cnl_pk ..), the first from LS_cnt at the cut,
   the second at the state the drain leaves through the two pure model rules DR_CNT_grow / DR_CNT_cnl; LS_drain_pre's
   conjunct 5 is the peak form (with the three premises s5-r1d's rows take); LS_cnl_pre / LS_drain_step are
   a Theorem Labs lane's TX_LS_cnl_pre / TX_LS_drain_step_t (d0d75bf92db, 1318828167d, image A's texts), whose premises
   dc_stB (dcB_out) and dc_stE export. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_entry W_LLVMFuzzerTestOneInput_drain_calls.
(* the room round: the live counts (lib/B/ReplyCnt.v), Required and named qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_entry_x W_LLVMFuzzerTestOneInput_drain_calls_x.
(* LAST, so the names this file cites from the AR file are not shadowed by a kit file's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the cut's own Local Notation, which does not leave its file *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.


Section drx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w (W_LLVMFuzzerTestOneInput_cut_x.v:199-244), verbatim ---- *)
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
(* ---- the arm's own parameter ---- *)
Variable MMAX : Z.                                   (* W7's request bound, dr_spec_x's parameter *)
(* ---- the callees, each the kit's _x form at the walk's PST / ARx ---- *)
(* relay_source: cut_x's Section hypothesis RSRC_x (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:583), verbatim *)
Hypothesis RSRC_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre_x segs B ARx RSRC_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
    (aleafx_post_x B PST ARx RSRC_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).
(* the allocator instance (lib/B/W_kit.v PALib), a Theorem Labs lane's working branch *)
Hypothesis TL : PALib (PI := PB_fr) B.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (a), (d)): drain's and check_no_loss's room record RP, at RM := the cut's
   NP (the cf instance: rp_RM := fun S _ => room_live_cf S = NP, so RP_NP is iff_refl) *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* drain: the kit's dr_spec_x (lib/B/W_contract_x.v Section s7), W7's text at image B over ARx *)
Hypothesis DRAIN : dr_spec_x (PI := PB_fr) B PST ARx MT RP MMAX fr_RG (BASE + AF_fr_drain).
(* the two mutex entries: the kit's _x forms (lib/B/W_sites_x.v Section c) *)
Hypothesis ALOCK : alock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_unlock).
(* check_no_loss_read: the kit's cnlr_spec_x (lib/B/W_contract_x.v Section cnlr) *)
Hypothesis CNLR : cnlr_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_no_loss_read).
(* check_shape_done: the kit's csd_spec_x (lib/B/W_contract_x.v Section c) *)
Hypothesis CSD : csd_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_shape_done).
(* check_no_loss: the kit's cnl_spec_x (lib/B/W_contract_x.v Section w3n), at the G its proof takes *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt (PI := PB_fr) B G -> rom_out segs B G ->
  cnl_spec_x (PI := PB_fr) B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).

(* ---- the G-coverage facts (lib/B/W_LLVMFuzzerTestOneInput_G.v proves each for G_fr_c), the AR file's text ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a.
Hypothesis HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Hypothesis HG_GK : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
  (rg_send_max fr_RG, 8); (rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1);
  (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G_fr a.
Hypothesis HERR_HI : rg_out fr_RG + 8 <= as_errno B.
(* cut_x's errno_law_x *)
Hypothesis ERR : errno_law_x B ARx.
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis DR_ROM_OUT : rom_out segs B G_fr.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
                 (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= rg_s fr_RG).
(* ---- the two facts the AR proof read off AR itself (see the file header; AddX's A drain_x text) ---- *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
Hypothesis BLKR : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n < 2 ^ 30.

(* ---- the arm's open model obligations (pure, over lmod and the plain records); the AR file's texts ---- *)
Hypothesis RI_drain_skip : forall cx t m si h,
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
(* B restatement: a Theorem Labs lane's RI_drain_step_btop_restated (a working branch 713767bda40,
   lib/B/ReplyRINVB_exit.v:788-798), the B top_x's text: the AR file's text plus t's bound, the held list's count bound,
   the new entry's paddings and the held capacity, which B's dr_step_ok (lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v:224-249) lacks and without which
   the AR text is false on B (a Theorem Labs lane's _false_pad / _false_cap).  dr_stage_calls (_drain_calls_x.v) holds all four. *)
Hypothesis RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  RINV cx t m -> 0 <= t < OPS_MAX ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h'))
    (2 * (hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h')))))) ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
(* ---- the drain's count growth (the room round's count rule).  check_no_loss's count premise is at the state the
   drain leaves; LS_cnt bounds the counts at the cut.  dr_post's two Permutations (W_contract_x.v dr_post_x) make the
   change of every count the change over the drained entry's, source's and g_out's blocks, with the same rest; this
   rule says that change is at most the drain trace's count peak, for every count predicate P.  A PURE MODEL rule
   (no astate; W8Entry-2's 04:20Z pattern, as the gone arm's GN_CNT_step), with the premises the walk holds at the
   drain's return (dc_stB): the cut's model facts at the call (dc_static, LS_cnt's guards, the dr3 / ls3 bundles of the
   entry and the source) and dr_post's model clauses (dr_dfun, dr3_epost, dr3_hpost, ls3_dpost) ---- *)
Hypothesis DR_CNT_grow : forall cx t m si h j e' h' LB out' (P : Z -> bool),
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
  dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  dr_dfun m si h j e' h' LB ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h ->
  (* added: the held-array clause of the entry drain leaves (aentry_ok e', W_rep.v:133-134) *)
  ((re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')) ->
  dr3_hpost h h' ->
  ls3_dpost m j h e' h' ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
   ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
   Z.to_nat (ReplyCnt.tr_peakP P
     (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat.
Hypothesis RI_src : forall cx t m si h,
  RINV cx t m -> dr_pick cx m si h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
Hypothesis RI_fds : forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Hypothesis RI_pair : forall cx t m si h j,
  RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
  length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat.
Hypothesis RI_gone : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).

(* ---- the allocator-state facts the two allocating calls take, read off LSx ---- *)
(* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3), image A's
   text: conjunct 5 is s5-r1d's fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:942 on image A), and the three premises
   after re_eof are the ones its rows take (fr_LS3_drain_pre_c4 lib/A/ReplyLS3Arms.v:790, fr_LS_drain_pre_c5p):
   dc_regs' Ht, aentry_ok's |re_U| bound and the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was
   FALSE at reachable states. *)
Hypothesis LS_drain_pre : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
(* after the drain: what check_no_loss takes of the state it is called in.  A Theorem Labs lane's TX_LS_cnl_pre
   (commit d0d75bf92db, lib/A/ReplyLS3cTopxPost.v:146 on image A; proved as ReplyLS3Arms.v:841 fr_LS3_cnl_pre_p), as
   image A's drain arm states it: the binders e' cap' out' and nine premises after the old ten, each held at
   dr_stage_calls (dc_regs' Ht, dr_at_op's lm_O m = [], and dc_stB's dcB_out: the cut's entry and source at the call,
   dr_post's frame and its entry / source clauses); and, last in the conclusion, check_no_loss's memmove bound
   `AREC * capb .. < 2 ^ 32`, as the B top_x's LS_cnl_pre states it (a Theorem Labs lane's TX_LS_cnl_pre,
   lib/B/ReplyB3LS3cTopxPost.v:173-201 at a working branch 92b82c11331) *)
Hypothesis LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h''))
    (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Hypothesis LS_drain_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
(* the drain charges the meter dr_cost of the entry and source it was called with (S to S1), check_no_loss
   cnl_cost of the lists it was called with (S1 to S').  A Theorem Labs lane's TX_LS_drain_step (commit d0d75bf92db,
   lib/A/ReplyLS3cTopxPost.v:118 on image A; proved as ReplyLS3cArms.v:118 fr_LS3c_drain_step_p), as image A's drain
   arm states it: the binders ly1 h1 E' H' and twenty premises after the old five, each held at dr_stage_calls (the
   drain's and check_no_loss's frames, dcB_out and dc_stE's exports); and, last, dc_regs' `0 <= t < OPS_MAX`, as
   s5-r1d's TX_LS_drain_step_t (1318828167d lib/A/ReplyLSI.v:134, its LS instance's lsi_LS_drain_step :509) *)
Hypothesis LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
  dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 ->
  ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
(* the live counts at the cut leave room for the arm's peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2):
   a Theorem Labs lane's row fr_LS3cp_cnt_drain (commit ba8e99b5bd2, lib/A/ReplyLScnt.v:371 on image A) with its guards,
   over the room record's count fields (at the cf instance they are ReplyCnt's Psec / P24 / Lsec / L24 / Pcls / LPRIM;
   image A's top plugs it with ReplyLScntRP.v's lsc_rp_of_acnt).  Its peak is the row's pk_drain m h j
   (ReplyLScnt.v:151) with check_no_loss's part the parameter dr_cnl_pk (below): drain's trace peak +
   check_no_loss's peak over the drained lines + 2, which covers dr_spec's count premise (dr_pk) at the cut and
   cnl_spec's (cnl_pk) at the state the drain leaves (DR_CNT_grow, DR_CNT_cnl) *)
(* check_no_loss's count peak after the drain, a function of the source the drain was called with: at image A's top
   it is ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) (the row's part of pk_drain) *)
Variable dr_cnl_pk : hsrc -> (Z -> bool) -> nat.
(* the kit's check_no_loss trace after a drain has at most that peak: the expected list was empty at the operation's
   start (RI_src) and the drain appended the lines (dr_dfun), the held list is kept (a PURE MODEL rule; at image A's
   top ReplyLScnt.lsc_cnl_call proves it with = at j := 0, nm := fun _ => RelayRunF.adr0) *)
Hypothesis DR_CNT_cnl : forall (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  (Z.to_nat (ReplyCnt.tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) <= dr_cnl_pk h P)%nat.
Hypothesis LS_cnt : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP
    (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
       (dr_cnl_pk h P + 2))%nat)
    (ablocks B ly S).

(* ------------------------------------------------------------------ the bundle the two stages read *)
Definition dr_EV_x : dr_env_x B MT NP G_fr PST ARx LSx RINV MMAX RP dr_cnl_pk :=
  {| dre_TL := TL; dre_RP_NP := RP_NP; dre_DRAIN := DRAIN; dre_ALOCK := ALOCK; dre_AUNLOCK := AUNLOCK;
     dre_CNLR := CNLR; dre_CSD := CSD; dre_CNL := CNL;
     dre_HGs := HGs; dre_HG_DR := HG_DR; dre_HGlock := HGlock; dre_HG_GK := HG_GK;
     dre_HERR_HI := HERR_HI; dre_ERR := ERR; dre_GWR := GWR; dre_ROM_OUT := DR_ROM_OUT;
     dre_HZS := HZS; dre_HAP := HAP; dre_HPST := HPST; dre_BLKR := BLKR;
     dre_RI_drain_skip := RI_drain_skip; dre_RI_drain_step := RI_drain_step; dre_DR_CNT_grow := DR_CNT_grow;
     dre_RI_src := RI_src; dre_RI_fds := RI_fds; dre_RI_pair := RI_pair; dre_RI_gone := RI_gone;
     dre_LS_drain_pre := LS_drain_pre; dre_LS_cnl_pre := LS_cnl_pre;
     dre_LS_drain_skip := LS_drain_skip; dre_LS_drain_step := LS_drain_step;
     dre_DR_CNT_cnl := DR_CNT_cnl; dre_LS_cnt := LS_cnt |}.

(* ------------------------------------------------------------------ the arm *)
(* the text of cut_x's Section w hypothesis ARM_drain (W_LLVMFuzzerTestOneInput_cut_x.v:639, the room round's cut:
   INV_A_x / INV_K_x take the cut's NP after B).  0x8489c -> the latch 0x84804: the entry stage leaves either the
   latch (the two skips) or the state at `jal pthread_mutex_lock`, and the calls stage takes that one to the latch. *)
Theorem lf_arm_drain_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 2 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hpe t W c HB HA.
  eapply SRr_bind;
    [ exact (dr_stage_entry B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
               LAWS HP0 HG LSx RINV MMAX RP dr_cnl_pk dr_EV_x RSRC_x cx Hpe t W c HB HA) |].
  cbv beta. intros W1 c1 _ [HK | (m & j & si & h & fpos & ly3 & S3 & Hp3 & k & HD)].
  - exact (SRr_ret segs W1 c1 _ HK).
  - exact (dr_stage_calls B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
             LAWS HG LSx RINV MMAX RP dr_cnl_pk dr_EV_x cx Hpe t m j si h fpos ly3 S3 Hp3 k W1 c1 HB HD).
Qed.

(* CHECK (cut_x's scope): lf_arm_drain_x's type is the Section w hypothesis ARM_drain of
   W_LLVMFuzzerTestOneInput_cut_x.v:639, restated with the generic invariants at this Section's variables *)
Lemma lf_arm_drain_x_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 2 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof. exact lf_arm_drain_x. Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): lf_arm_drain_xR, the R twin of lf_arm_drain_x, whose statement is the text of
   cut_x's Section wR hypothesis ARM_drain_R.  The two re-hiding callees take their R specs (DRAIN_R : dr_spec_xR,
   CNL_R : cnl_spec_xR); the other callees keep the strict Section hypotheses above (relay_source, the mutex entries,
   check_no_loss_read, check_shape_done), lifted inside the stages.  The entry stage moves no world and is lifted by
   SRr_SRrG; the calls stage is at R.  Strict text above unchanged. ---- *)
Section drxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* drain at R: lib/B/W_contract_xR.v dr_spec_xR *)
Hypothesis DRAIN_R : dr_spec_xR (PI := PB_fr) B PST ARx R MT RP MMAX fr_RG (BASE + AF_fr_drain).
(* check_no_loss at R: lib/B/W_contract_xR_g6.v cnl_spec_xR, at the G its proof takes *)
Hypothesis CNL_R : forall G, gx_ok segs B G -> gx_rt (PI := PB_fr) B G -> rom_out segs B G ->
  cnl_spec_xR (PI := PB_fr) B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).

Definition dr_EV_xR : dr_env_xR B MT NP G_fr PST ARx LSx RINV MMAX RP dr_cnl_pk R :=
  {| dreR_TL := TL; dreR_RP_NP := RP_NP; dreR_DRAIN := DRAIN_R; dreR_ALOCK := ALOCK; dreR_AUNLOCK := AUNLOCK;
     dreR_CNLR := CNLR; dreR_CSD := CSD; dreR_CNL := CNL_R;
     dreR_HGs := HGs; dreR_HG_DR := HG_DR; dreR_HGlock := HGlock; dreR_HG_GK := HG_GK;
     dreR_HERR_HI := HERR_HI; dreR_ERR := ERR; dreR_GWR := GWR; dreR_ROM_OUT := DR_ROM_OUT;
     dreR_HZS := HZS; dreR_HAP := HAP; dreR_HPST := HPST; dreR_BLKR := BLKR;
     dreR_RI_drain_skip := RI_drain_skip; dreR_RI_drain_step := RI_drain_step; dreR_DR_CNT_grow := DR_CNT_grow;
     dreR_RI_src := RI_src; dreR_RI_fds := RI_fds; dreR_RI_pair := RI_pair; dreR_RI_gone := RI_gone;
     dreR_LS_drain_pre := LS_drain_pre; dreR_LS_cnl_pre := LS_cnl_pre;
     dreR_LS_drain_skip := LS_drain_skip; dreR_LS_drain_step := LS_drain_step;
     dreR_DR_CNT_cnl := DR_CNT_cnl; dreR_LS_cnt := LS_cnt |}.

Theorem lf_arm_drain_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 2 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hpe t W c HB HA.
  eapply (YA0nH.SRrG_bind segs R R_trans);
    [ apply (YA0nH.SRr_SRrG segs R WLE_R);
      exact (dr_stage_entry_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
               LAWS HP0 HG LSx RINV MMAX RP dr_cnl_pk RSRC_x R R_trans WLE_R dr_EV_xR cx Hpe t W c HB HA) |].
  cbv beta. intros W1 c1 _ [HK | (m & j & si & h & fpos & ly3 & S3 & Hp3 & k & HD)].
  - exact (YA0nH.SRrG_ret segs R R_refl W1 c1 _ HK).
  - exact (dr_stage_calls_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
             LAWS HG LSx RINV MMAX RP dr_cnl_pk R R_refl R_trans WLE_R dr_EV_xR cx Hpe t m j si h fpos ly3 S3 Hp3 k W1 c1 HB HD).
Qed.

End drxR.

End drx.
