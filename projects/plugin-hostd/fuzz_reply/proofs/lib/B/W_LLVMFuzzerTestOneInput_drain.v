(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's LLVMFuzzerTestOneInput - the jump table's arm 2 (op_drain, fuzz_reply.c:596-609), from the arm's
   entry 0x8489c (BASE + AF_arm_drain 0x2558) to the latch 0x84804 (BASE + AF_LLVM_latch).  THE CLOSING FILE:
   it declares, by name, everything the arm takes, and composes the two stage walks into the cut's ARM_drain
   (lib/B/W_LLVMFuzzerTestOneInput_cut.v:954), which it discharges by `exact lf_arm_drain`.
   Proves no function (kind: segment walk - a segment of the entry function; its callees are named contracts).

   Image: the pinned asan-ubsan objdump of fuzz_reply (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) beside the pinned ELF),
   sha256 17f5c434bf5755fb1ceaed0ac3e631e85a2eae980ed9983d0ee03955bf5307ac; the ELF beside it is the pin
   sha256 10ffb5f9202ae2bd... that lib/B/W_LLVMFuzzerTestOneInput_cut.v:18 names.

   The three files of this arm:
     lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v   the interface: addresses, model notions, register predicates,
                                                   DLK (the state at `jal pthread_mutex_lock`, 0x84900), the
                                                   dr_env bundle, the pure model lemmas;
     lib/B/W_LLVMFuzzerTestOneInput_drain_entry.v  dr_stage_entry: 0x8489c -> the latch (both skips) or DLK,
                                                   through the relay_source call at 0x848c0;
     lib/B/W_LLVMFuzzerTestOneInput_drain_calls.v  dr_stage_calls: DLK -> the latch, the six calls
                                                   (lock, drain, unlock, check_no_loss_read, check_no_loss,
                                                   check_shape_done).
   The B code of the arm, and how B differs from image A's twin (lib/A/W_LLVMFuzzerTestOneInput_drain.v at
   a working branch a86c2788a94, every lemma Qed), are listed in _drain_defs.v's header.

   ------------------------------------------------------------------ the trap table (the cut header's
   ARM_drain rows; every branch is to the one UBSan landing pad `unimp` at 0x850fc)
     pc        branch                                shape     closed by
     0x8489c   beqz s5         (s5 = g_s + 96 i)     NONNULL   the runner, from atom 21's seat fact on s5
                                                               (W_traps.v recipe R1: mkAF 4096 140737479966720 3)
     0x848a4   bnez a0         (andi a0,s5,7)        ALIGN8    the runner, same atom 21 fact (al2 = 3)
     0x848d4   bnez a0         (andi a0,a0,7; a0 =   ALIGN8    the runner, from atom 10's seat fact on the entry
               relay_source's result T + 56 j)                 T + 56 j (recipe R1/R2: its own atom, mkAF 4096
                                                               140737479966720 3); the walk splits on RSRC's two
                                                               answers before it re-enters the engine at 0x848c4
   No W_traps.v lemma is cited for a trap: the runner decides all three after the seat (dr_stage_entry,
   _drain_entry.v).  The non-trap `beqz a0` at 0x848c8 is split by the walk, and its fall-through edge under
   a0 = 0 is refuted with the kit's value lemma W_traps.v trap_br_eq.  The two ASan shadow checks (0x848b8 for
   s->fd, 0x848e8 for r->eof) are not UBSan traps; the runs decide them from shadow entries over the whole
   object - mkSHE 21 0 96 (the source, in g_s's zero-shadow range HZS) and mkSHE 10 0 56 (the entry, inside the
   relay table's live 896-byte block).

   ------------------------------------------------------------------ the placement / instance table
   (every hypothesis below that is not a callee contract or a model rule; TRUE / FALSE / undecidable, and how)
     TL        PALib B                     instance, undecidable here - PLACED with a Theorem Labs lane
                                           (a working branch); A_OBJ 0 = 0x9df50, A_OBJ 30 = 0xa6638.
     HGs       g_s in G_fr                 TRUE at the pin: lib/B/W_LLVMFuzzerTestOneInput_G.v c_HGs.
     HGlock    g_lock's 12 bytes in G_fr    TRUE: _G.v c_HGlock.
     HG_DR     drain's G_DR in G_fr         TRUE: _G.v c_HG_DR.
     HG_GK     the model's other cells      TRUE at the pin: all eleven ranges are objects of _G.v's G_fr_obj
                                           (g_src, g_nsrc, g_capsrc, g_send_max, g_client, g_send_dead, g_gone,
                                           g_wake, g_nfd, g_thread_up, g_listen), so _G.v's rng_cover recipe
                                           proves it; _G.v states the per-object twins (c_HG_nfd, c_HG_smax,
                                           c_HG_client, c_HG_gone, c_HG_sdead, ...).
     HERR_HI   g_out + 8 <= errno           TRUE: _G.v c_HERRHI (errno 0x5d994c, g_out 0x5d90c0).
     ERR       errno_law B                  instance (the api_env's errno cell), undecidable here.
     GWR       glob_wr_law G_fr             TRUE: _G.v c_glob_wr.
     ROM_OUT   rom_out segs B G_fr          TRUE: _G.v c_rom_apart + owned_rom_pinned_ok.
     HZS       azs B g_s (4 * ASRC)         TRUE at the pin: _G.v's measurement (Tfib_zero_shadow holds
                                           (0x5d8e60, 384)).
     HAP       g_s apart from A_OBJ 0 / 30  TRUE: _G.v c_HAP (vm_compute at PB_fr).
   No hypothesis of this arm is a missing premise.  Two premises of the kit's cnl_spec (lib/B/W_contract.v:2054)
   are proved at the call in _drain_calls.v rather than taken: its memmove bound `AREC * capb (hs_held h)
   (hs_expected h) < 2 ^ 32` (:2018, dcE_capb: the held vector is empty or an allocator block below MALLOC_MAX =
   2 ^ 28, and the count bound LS_cnl_pre gives covers the other term), and its last premise, the caller's stack
   readable from sp = F up to ly_top (:2023, dcF_stk_rd: [F, sp0) is the arm's own window, present at the end of
   its journal; [sp0, ly_top) is the cut's STKR - fr_lib_pre_cf's 18th conjunct, before HB, read from lf_base - kept to the
   call by the journal's view clause above its window, and no stack byte is a G_fr byte).
   The model rules (RI_ and LS_ families) and the callee contracts (RSRC, DRAIN, ALOCK, AUNLOCK, CNLR, CNL,
   CSD) are their owners'; each is stated below in its owner's text. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_entry.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_calls.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the cut's own Local Notations, which do not leave its file (_cut.v:153-156) *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section dr.
(* ---- _cut.v's Section w, verbatim (so ARM_drain's type is this file's lf_arm_drain's) ---- *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ---- the arm's own parameters ---- *)
Variable MMAX : Z.                                   (* W7's request bound, dr_spec's parameter *)

(* ---- the callees, each in its owner's text ---- *)
(* relay_source: the cut's own Section hypothesis (_cut.v:691-701), a Theorem Labs lane's agreed text, VERBATIM *)
Hypothesis RSRC : forall W ly S (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre segs B RSRC_STK ly S W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
    (aleafx_post B RSRC_STK regs ly S W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).
(* the allocator instance (lib/B/W_kit.v PALib), a Theorem Labs lane's working branch *)
Hypothesis TL : PALib (PI := PB_fr) B.
(* drain: the kit's dr_spec (lib/B/W_contract.v:1027), W7's text at image B *)
Hypothesis DRAIN : dr_spec (PI := PB_fr) B MT MMAX fr_RG (BASE + AF_fr_drain).
(* the two mutex entries: the kit's forms (lib/B/W_sites.v:90 / :105), R5's proofs *)
Hypothesis ALOCK : alock_realizes (PI := PB_fr) B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes (PI := PB_fr) B (SIGMA WS_pthread_mutex_unlock).
(* check_no_loss_read: the kit's cnlr_spec (lib/B/W_contract.v:484); the B walk pb_check_no_loss_read is in
   bint (a Theorem Labs lane, a working branch 7df4d90b544), so the B top discharges this *)
Hypothesis CNLR : cnlr_spec (PI := PB_fr) B (BASE + AF_fr_check_no_loss_read).
(* check_shape_done: the kit's csd_spec (lib/B/W_contract.v:157) *)
Hypothesis CSD : csd_spec (PI := PB_fr) B (BASE + AF_fr_check_shape_done).
(* check_no_loss: the kit's cnl_spec (lib/B/W_contract.v:2054, cnl_post :1967, CNL_STK :1966, Section w3n), at the
   G its proof takes (pb_check_no_loss's G-dependent hypotheses are gx_ok, gx_rt and, through its callees,
   rom_out); the call takes it at the slot's own list headers [(HA + 64, 32)] *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt (PI := PB_fr) B G -> rom_out segs B G ->
  cnl_spec (PI := PB_fr) B MT G MMAX (BASE + AF_fr_check_no_loss).

(* ---- the G-coverage facts (lib/B/W_LLVMFuzzerTestOneInput_G.v proves each for G_fr_c) ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a.
Hypothesis HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Hypothesis HG_GK : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
  (rg_send_max fr_RG, 8); (rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1);
  (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G_fr a.
Hypothesis HERR_HI : rg_out fr_RG + 8 <= as_errno B.
Hypothesis ERR : errno_law B.
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis DR_ROM_OUT : rom_out segs B G_fr.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
                 (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= rg_s fr_RG).

(* ---- the arm's open model obligations (pure, over lmod and the plain records); image A's texts ---- *)
Hypothesis RI_drain_skip : forall cx t m si h,
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
Hypothesis RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
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

(* ---- the allocator-state facts the two allocating calls take, read off LS ---- *)
(* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3), image A's
   text (W8's drain arm b5892edd1cb lib/A/W_LLVMFuzzerTestOneInput_drain.v): conjunct 5 is s5-r1d's
   fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:942 on image A), and the three premises after re_eof are the ones its
   rows take (fr_LS3_drain_pre_c4 lib/A/ReplyLS3Arms.v:790, fr_LS_drain_pre_c5p): dc_regs' Ht, aentry_ok's |re_U|
   bound and the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was FALSE at reachable states. *)
Hypothesis LS_drain_pre : forall cx t m ly S si h j,
  LS cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
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
Hypothesis LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'',
  LS cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h''))
    (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')).
Hypothesis LS_drain_skip : forall cx t m ly S,
  LS cx t m ly S -> LS cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Hypothesis LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist),
  LS cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  LS cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.

(* ------------------------------------------------------------------ the bundle the two stages read *)
Definition dr_EV : dr_env B MT G_fr LS RINV MMAX :=
  {| dre_TL := TL; dre_DRAIN := DRAIN; dre_ALOCK := ALOCK; dre_AUNLOCK := AUNLOCK;
     dre_CNLR := CNLR; dre_CSD := CSD; dre_CNL := CNL;
     dre_HGs := HGs; dre_HG_DR := HG_DR; dre_HGlock := HGlock; dre_HG_GK := HG_GK;
     dre_HERR_HI := HERR_HI; dre_ERR := ERR; dre_GWR := GWR; dre_ROM_OUT := DR_ROM_OUT;
     dre_HZS := HZS; dre_HAP := HAP;
     dre_RI_drain_skip := RI_drain_skip; dre_RI_drain_step := RI_drain_step; dre_RI_src := RI_src;
     dre_RI_fds := RI_fds; dre_RI_pair := RI_pair; dre_RI_gone := RI_gone;
     dre_LS_drain_pre := LS_drain_pre; dre_LS_cnl_pre := LS_cnl_pre;
     dre_LS_drain_skip := LS_drain_skip; dre_LS_drain_step := LS_drain_step |}.

(* ------------------------------------------------------------------ the arm *)
(* 0x8489c -> the latch 0x84804: the entry stage leaves either the latch (the two skips: no relay entry for the
   source's fd, or its entry at end of file) or the state at `jal pthread_mutex_lock`, and the calls stage takes
   that one to the latch. *)
Theorem lf_arm_drain : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_A B G_fr fr_FP LS RINV 2 cx t W c -> SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
  (* both stage lemmas take every header variable in header order, then the bundle (the entry stage also RSRC) *)
  eapply SRr_bind;
    [ exact (dr_stage_entry B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv G_fr fr_FP LAWS HG
               LS RINV MMAX dr_EV RSRC cx t W c HB HA) |].
  cbv beta. intros W1 c1 _ [HK | (m & j & si & h & fpos & ly3 & S3 & k & HD)].
  - exact (SRr_ret segs W1 c1 _ HK).
  - exact (dr_stage_calls B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv G_fr fr_FP LAWS HG
             LS RINV MMAX dr_EV cx t m j si h fpos ly3 S3 k W1 c1 HB HD).
Qed.

(* the cut's ARM_drain (lib/B/W_LLVMFuzzerTestOneInput_cut.v:954), copied, discharged by the theorem above *)
Definition ARM_drain_text : Prop :=
  forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_A B G_fr fr_FP LS RINV 2 cx t W c -> SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Lemma lf_arm_drain_is_ARM_drain : ARM_drain_text.
Proof. exact lf_arm_drain. Qed.
End dr.
