(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC conversion of the event arm of fuzz_reply's LLVMFuzzerTestOneInput
   (lib/A/W_LLVMFuzzerTestOneInput_event.v, a Theorem Labs lane's lf_arm_event adapted to W8's cut at c3d5cbd2c52, Qed at
   a working branch 5632cc43ae4) to the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v (a Theorem Labs lane's
   route (b), step 7). lf_arm_event_x is exactly cut_x's Section w hypothesis ARM_event. Neither _event.v nor cut_x is
   edited.
   - The Section header is cut_x's Section w header (B .. RINV, with PST / ARx / hl / LAWS / HP0 / HG / LSx). The
     piece's own hypotheses follow: _event.v's AR-free ones verbatim (MMAX, TL, GWR, ET_ROM_OUT, HGlock, HG_SL,
     HG_carry, HERR_AP, and the RI_event_* / LS_event_* model rules with LS renamed LSx); ERRL at cut_x's errno_law_x;
     the callees at their kit forms: AMALLOC / AFREE at W_journal_x's caller-context rules amalloc_cf_rule_c_x /
     afree_cf_rule_c_x, each at ITS OWN K0 table CTX_AMALLOC / CTX_AFREE (lib/A/ACk0.v; a Theorem Labs lane 20:04Z, one CTX
     per entry), AMEMCPY at W_sites_x's aintrin_realizes_x, RE at W_contract_x's re_spec_x, CSE at cse_spec_x.
   - OWED (kit has no twin): ASTRNLEN's spec et_strnlen_spec_x, _event.v's et_strnlen_spec (the StrnlenDef
     text) in the kit's form: ecall_pre -> FCiface.ecall_pre_x, AR -> ARx, the ghost list Hp after S (the form of
     W_sites_x.aintrin_realizes_x). BLKN, add_x's text (AR's al_blocks has 0 <= n, ARx_blocks_law does not).
   - HPST (forced by the generic placement, add_x's text): the image is off PST, so a callee's journal keeps every
     image byte outside its G (at the instance's PST := [] it holds trivially).
   - _event.v's ALLOC_TAIL (an instance hypothesis there) is not a hypothesis here: it is the laws' field 15,
     ARx_blocks_tail_law, at this ARx (ALLOC_TAIL_x).
   - HP0 makes every ghost list of the walk empty, so the converted helpers are stated at Hp = []: AR0 is _event.v's AR
     at [], AJ0 / AJi0 its journals. The AR-free lemmas and definitions of _event.v are CITED from it (with their
     section arguments, through local abbreviations); each one that reads AR is converted here under its name + _x,
     with _event.v's proof: AR's laws -> AR_laws_x's fields, cgif's journal lemmas -> W_journal_x's, the runs ->
     paj_run_x_x / paj_run_to_x_x, the entry liftings -> W_sites_x.aj_gx_entry_at_x.
   - Two kit steps are re-derived locally rather than taken as hypotheses: blk_off_imgP (by small_x's sm_blk_off_x)
     and YCbq.aftok_new_block (ev_aftok_new_block0, its proof over ajournal_x / sep_blocks_pos_x).
   - The allocator entries' caller contexts are rows of the K0 table: malloc at return site 0x84ad0 and free at
     0x84b20, each with the chain [] or the entry frame's [RA_LLVMF] (et_afn_pre_at_x names the chain's spine).
   - ROUTE R (Section evxR) carries the walk's proofs at a world relation R. Since part 3c (memnorm out of the
     allocator rules), ev_aftok_new_block0, ajournal_gx_rom_view0, ev_P1_of_x, ev_to_P1_x, et_afn_pre_at_x,
     et_gx_keep_x, et_cr_gx_x, ev_tail_x and lf_arm_event_x are their *R / *_xR twins at R := wle, stated after
     Section evxR with their statements unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x ACk0.
(* route R (Section evxR): the step relation SRrG and relay_event's R contract re_spec_xR *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
(* acnt, the one count definition (the room round's cnt_ok / cnt_ok_pk count with it) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
(* sl_tr_peak_le_alloc: re_spec_x's byte peak premise from LS_event_relay's sum form *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
(* fr_img_cover_x: the image law's cover of the image (blk_off_imgP0) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* _event.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section evx.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:192-235) *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
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
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling, W_journal_x at 0c4d57d9bf1;
   fuzz_reply calls no poison routine): the driver reads the post's Hp' = [] from the journal's ARx through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* ---------------------------------------------------------------- the event arm's own hypotheses *)
(* the request bound of the allocator's live-state rules (W_journal.v:697, the instance's cf_malloc_max) *)
Variable MMAX : Z.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (a), (d)): the allocator rules' and relay_event's room record RP, at
   RM := the cut's NP (the cf instance: rp_RM := fun S _ => room_live_cf S = NP, so RP_NP is iff_refl) *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* the allocator instance, W_kit.v:356 PALib @ 5180fc7d18d: SIGMA WS_malloc / WS_free are its wrappers *)
Hypothesis TL : PALib B.
(* _cut.v's two shared facts (W_LLVMFuzzerTestOneInput_cut.v:309 glob_wr_law, :214 errno_law; _G.v c_glob_wr proves the
   first for G_fr_c) *)
Hypothesis GWR : glob_wr_law G_fr.
(* _cut.v's errno_law over ARx: cut_x's errno_law_x *)
Hypothesis ERRL : errno_law_x B ARx.
(* .rodata is outside G_fr, the allocator's statics, errno and the sink's overflow head: W_journal.v:376 rom_out, the
   text W_xrf.v:191 XRF_ROM_OUT takes (_G.v c_rom_apart proves its G_fr conjunct) *)
Hypothesis ET_ROM_OUT : rom_out segs B G_fr.
(* G_fr facts, proved for G_fr_c in W_LLVMFuzzerTestOneInput_G.v: the lock and send_line's G (c_HGlock, c_HG_SL) *)
Hypothesis HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
(* G_fr facts, proved for G_fr_c in W_LLVMFuzzerTestOneInput_G.v (c_HG_carry, c_HERR_AP): those globals are in G_fr,
   and apart from errno's cell *)
Hypothesis HG_carry : forall a, inG et_GL a -> inG G_fr a.
Hypothesis HERR_AP : forall a, inG et_GL a -> ~ (as_errno B <= a < as_errno B + 4).
(* ---- _event.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation et_GRE := (W_LLVMFuzzerTestOneInput_event.et_GRE B).
Local Notation ev_byte := (W_LLVMFuzzerTestOneInput_event.ev_byte B).
Local Notation lregs_P1 := (W_LLVMFuzzerTestOneInput_event.lregs_P1 B).
Local Notation et_kept_G := (W_LLVMFuzzerTestOneInput_event.et_kept_G G_fr GWR).
Local Notation et_GLr_GL := (W_LLVMFuzzerTestOneInput_event.et_GLr_GL XM_LIB XN_LIB RLO).
Local Notation et_GLr_G := (W_LLVMFuzzerTestOneInput_event.et_GLr_G XM_LIB XN_LIB RLO G_fr HG_carry).
Local Notation et_lock_GL := (W_LLVMFuzzerTestOneInput_event.et_lock_GL XM_LIB XN_LIB RLO).
Local Notation et_errno_G := (W_LLVMFuzzerTestOneInput_event.et_errno_G B XM_LIB XN_LIB RLO G_fr HG_SL).
Local Notation et_alist := (W_LLVMFuzzerTestOneInput_event.et_alist B).
Local Notation et_asrc := (W_LLVMFuzzerTestOneInput_event.et_asrc B).
Local Notation et_aentry := (W_LLVMFuzzerTestOneInput_event.et_aentry B).
Local Notation et_arelay := (W_LLVMFuzzerTestOneInput_event.et_arelay B).
Local Notation et_model_kept := (W_LLVMFuzzerTestOneInput_event.et_model_kept B).
Local Notation et_input_kept := (W_LLVMFuzzerTestOneInput_event.et_input_kept B).
Local Notation ev_aview_in := (W_LLVMFuzzerTestOneInput_event.ev_aview_in B).
Local Notation ev_evt_of := (W_LLVMFuzzerTestOneInput_event.ev_evt_of B).
Local Notation et_carry := (W_LLVMFuzzerTestOneInput_event.et_carry B).
Local Notation et_carry_out := (W_LLVMFuzzerTestOneInput_event.et_carry_out B).
Local Notation et_GO_GL := (W_LLVMFuzzerTestOneInput_event.et_GO_GL XM_LIB XN_LIB RLO).
(* ---- the tail's callees at their kit forms ---- *)
(* malloc (0x84acc) and free (0x84b1c): W_journal_x.v's caller-context rules, each at its own K0 table (lib/A/ACk0.v) *)
Hypothesis AMALLOC : amalloc_cf_rule_c_x segs B PST ARx MT MMAX RP CTX_AMALLOC.
Hypothesis AFREE : afree_cf_rule_c_x segs B PST ARx MT RP CTX_AFREE.
(* __asan_memcpy (0x84ae0): W_sites_x.v:126 aintrin_realizes_x *)
Hypothesis AMEMCPY : aintrin_realizes_x segs B ARx OCpy (SIGMA WS_asan_memcpy).
(* strnlen (0x84ac0). OWED (kit has no twin): _event.v:79 et_strnlen_spec (the StrnlenDef text, at lo / hi =
   0x10350 / 0x10370) in the kit's form - ecall_pre -> FCiface.ecall_pre_x, AR -> ARx, Hp after S, the post's ARx at
   the pre's Hp (as W_sites_x.aintrin_realizes_x) *)
Definition et_strnlen_spec_x (lo hi pc : Z) : Prop :=
forall ly S Hp W regs mem md x n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
et_consts_view lo hi W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n 0 k /\ getr regs' 10 = w64 k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Hypothesis ASTRNLEN : et_strnlen_spec_x 0x10350 0x10370 (SIGMA WS_strnlen).
(* relay_event (0x84b0c): W_contract_x.v:810 re_spec_x at relay_event's own G (_event.v's et_GRE) *)
Hypothesis RE : re_spec_x (PI := PB_fr) B PST ARx MT RP MMAX et_GRE fr_RG (BASE + AF_fr_relay_event).
(* check_shape_event (0x84b14): W_contract_x.v:539 cse_spec_x *)
Hypothesis CSE : cse_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_shape_event).
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct). The text is W_kit_x.v:45's BLKN (add_x's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): a callee's journal keeps every image byte outside its own G *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.

(* ---- the arm's open model obligations (pure, over lmod and the plain records) ---- *)
(* the projection of the plain invariant's gone clause (Prog/SlotInv.v globals_at): it gives check_shape_event's
   `(gone = 1 /\ O = 0) \/ (gone = 0 /\ ob = e ++ [0])` through send_line's live test *)
Hypothesis RI_event_live : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).
(* the operation relayed the event line e; errno is v and the stream's block is out' *)
Hypothesis RI_event_step : forall cx t m e v out',
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  RINV cx (t + 1) (ev_step cx m e v out').
(* ---- the allocator-state facts the three calls take, read off LSx; the instance discharges them ---- *)
Hypothesis LS_event_malloc : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  re_len e < MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e)).
(* _event.v's LS_event_relay (relay_event's room after malloc, the stream empty), LS -> LSx *)
Hypothesis LS_event_relay : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Hypothesis LS_event_free : forall cx t m ly S (S1 S2 : astate) e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).
(* s5-r1d's text (fr_LS3c_event_step_p, commit 6d19e580568, lib/A/ReplyLS3cArms.v:91), LS -> LSx: the three states
   are tied to the calls' posts - S1 by the malloc rule's ablocks equation, S1 / S2 by relay_event's (send_line's)
   aout Permutations, S3 by the free's split with the event's block removed *)
Hypothesis LS_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (ev_step cx m e v out') ly3 S3.
(* the live counts at the arm's entry leave room for its peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2; the row
   fr_LS3cp_cnt_event, commit ba8e99b5bd2, lib/A/ReplyLScnt.v:265, with its peak pk_event e P = [P (re_len e)] + 2 and
   its guards, msz_ok inline): malloc (re_len e) at the entry's counts, relay_event's count premise (re_pk = 2) at the
   entry's blocks plus the event's, free at relay_event's post (g_out replaced: at most one block more).  Stated over
   the room record's count fields; at the cf instance they are ReplyCnt's Psec / P24 / Lsec / L24 / Pcls / LPRIM *)
Hypothesis LS_cnt : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  Forall (fun e0 => 0 <= re_cap e0 <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e0)) (lm_es m) /\
  Forall (fun o => match o with
                   | Some h => Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_expected h)) /\
                               Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_held h))
                   | None => True end) (lm_hs m) ->
  0 <= t < OPS_MAX ->
  (ReplyCnt.acnt (rp_Psec RP) (ablocks B ly S) + ((if rp_Psec RP (re_len e) then 1 else 0) + 2) <= rp_Lsec RP)%nat /\
  (ReplyCnt.acnt (rp_P24 RP) (ablocks B ly S) + ((if rp_P24 RP (re_len e) then 1 else 0) + 2) <= rp_L24 RP)%nat /\
  (forall c, 1 <= c <= 30 ->
     (ReplyCnt.acnt (rp_Pcls RP c) (ablocks B ly S) + ((if rp_Pcls RP c (re_len e) then 1 else 0) + 2)
        <= rp_LPRIM RP c)%nat).

(* ---- the arithmetic of the cursor ---- *)

(* ---------------------------------------------------------------- the walk at the empty ghost list
   HP0: every ARx state's ghost list is [], so the walk runs at Hp = []: AR0 is _event.v's AR, AJ0 its journal at
   G, AJi0 the inner journal *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* a concrete context is a row of a concrete K0 table *)
Ltac et_in_tab := vm_compute; repeat (first [left; reflexivity | right]).
(* the AR lemmas _event.v cites, at AR0 (cgif's al_* -> AR_laws_x's alx_*, YCbq.v's lemmas -> their _x twins) *)
Local Notation al0_frames ly S W mem md := (alx_frames _ _ _ LAWS ly S [] W mem md).
Local Notation al0_sep ly S W mem md := (alx_sep _ _ _ LAWS ly S [] W mem md).
Local Notation frames_bounds0 ly S W mem md := (frames_bounds_x _ _ _ LAWS ly S [] W mem md).
Local Notation blk_img0 ly S W mem md := (blk_img_x _ _ _ LAWS ly S [] W mem md).
Local Notation frm_img0 ly S W mem md := (frm_img_x _ _ _ LAWS ly S [] W mem md).
Local Notation sep_blocks0 ly S W mem md := (sep_blocks_x _ _ _ LAWS ly S [] W mem md).
Local Notation sep_block_frame0 ly S W mem md := (sep_block_frame_x _ _ _ LAWS ly S [] W mem md).
Local Notation sep_blocks_pos0 ly S W mem md := (sep_blocks_pos_x _ _ _ LAWS ly S [] W mem md).
Local Notation amem_range_of_block0 ly S W mem md := (amem_range_of_block_x _ _ _ LAWS ly S [] W mem md).
Local Notation range_addressable_of_block0 ly S W mem md :=
  (range_addressable_of_block_hp0_x _ _ _ LAWS HP0 ly S [] W mem md).
Local Notation shadow_hull_vis_of_block0 ly S W mem md :=
  (shadow_hull_vis_of_block_hp0_x _ _ _ LAWS HP0 ly S [] W mem md).
Local Notation ajournal_gx_AR0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_pack0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k memS :=
  (ajournal_gx_pack_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k memS).
Local Notation ajournal_gx_nil0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_nil_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_G_mono0 G G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_x segs B PST ARx G G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation aj_gx_entry_at0 G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc :=
  (aj_gx_entry_at_x (PI := PB_fr) B PST ARx LAWS G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S [] W0 mem md own
     lyc Sc []).
Local Notation awr_new_block_any0 STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 :=
  (awr_new_block_any_x segs B PST ARx LAWS STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ly2 S2 []).
(* cgif's al_blocks at AR0: ARx_blocks_law's six conjuncts and BLKN's size *)
Lemma al0_blocks : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* W_kit.v:375 blk_off_imgP at AR0: W_kit_x's blk_off_imgP_x proof, with IMGC from the image law (W_img_x.v
   fr_img_cover_x) and BLKN's size (the proof of small_x's sm_blk_off_x, restated here so this arm does not depend on
   the small arms' file) *)
Lemma blk_off_imgP0 : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) -> YCbq.off_img p (req_size n).
Proof.
  intros ly S W mem md p n HAR Hin. pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn. unfold off_img.
  destruct (W_img_x.fr_img_cover_x B ARx LAWS ly S [] W mem md HAR) as [C1 C2].
  pose proof (req_size_pos n Hn) as [Q _].
  destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fb000 p) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S [] W mem md (Z.max p 0x10000) HAR _)).
    left. exists p, n. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.
(* _event.v:106 ALLOC_TAIL (an instance hypothesis there): the laws' field 15, ARx_blocks_tail_law *)
Lemma ALLOC_TAIL_x : forall ly S (W : world segs) mem md p n a,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
  aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  apply (alx_blocks_tail _ _ _ LAWS ly S [] W mem md p n a HAR Hin).
  assert (E : (p + req_size n + 7) / 8 = (p + req_size n - 1) / 8 + 1).
  { replace (p + req_size n + 7) with ((p + req_size n - 1) + 1 * 8) by lia. apply Z.div_add. lia. }
  rewrite E. pose proof (Z.div_mod (p + req_size n - 1) 8 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (p + req_size n - 1) 8 ltac:(lia)) as Hm.
  set (q0 := (p + req_size n - 1) / 8) in *. set (r0 := (p + req_size n - 1) mod 8) in *. lia.
Qed.
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* _event.v's section-local tactics, restated *)
Ltac ev_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac ev_awr :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha; lia |] ].
Ltac ev_prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.
Ltac ev_V HS EQ V :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    lazymatch type of EQ with ew _ ?n = ?v =>
      assert (V : ew Ev n = v) by (rewrite ?ew_ewset_other by lia; exact EQ) end end.
Ltac et_inG := unfold inG, et_GLr, et_GL, AG_NFD, AG_THREAD_UP, AG_LISTEN, fr_RG, ASRC in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Ltac et_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

Lemma ev1_entry_x : forall (W : world segs) regs mem nb q lo hi ly St md p n,
  (nb <= 2)%nat ->
  getr regs 28 = w64 q -> getr regs 26 = w64 SB ->
  AR0 ly St W mem md -> In (p, n) (ablocks B ly St) -> p <= q -> q + Z.of_nat nb <= p + n ->
  ((1 <= nb)%nat -> val_mem segs (mrestrict (w_H W) mem) q 1 lo) ->
  ((2 <= nb)%nat -> val_mem segs (mrestrict (w_H W) mem) (q + 1) 1 hi) ->
  0 <= lo < 256 -> 0 <= hi < 256 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (ev1_extra lo hi))) (ss_ev1 nb)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_event)) mem (seg_rom segs)))
  /\ sh_ok segs EBx (ev1_SH nb) (Eimg (Ereg regs (ev1_extra lo hi))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem nb q lo hi ly St md p n Hnb H28 H26 HAR Hin Hpq Hqn Mlo Mhi Rlo Rhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al0_blocks ly St W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _).
  pose proof (proj1 Hph_ia) as Hph.
  pose proof (blk_off_imgP0 _ _ _ _ _ p n HAR Hin) as Hph_img.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (ev1_extra lo hi))).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
  assert (E28 : ew E 28 = Z_to_bv 64 q)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact H28).
  assert (E32 : ew E 32 = Z_to_bv 64 lo) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 hi) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (Hreq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  pose proof (pa_B_ok) as HBASE.
  assert (Usp28 : base_val E (Some 28%nat) = q) by (cbn [base_val]; rewrite E28; apply unsigned_lit_small; lia).
  assert (HqA : q + Z.of_nat nb <= alloc_ceiling) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hph; lia).
  split.
  - unfold ss_ev1, ev1_regions, ev1_chunks. destruct nb as [|[|nb']].
    + (* nb = 0: no region *)
      apply pa_entry_st_ok_full.
      * apply regs_ok_Eimg_Ereg.
      * vm_compute. reflexivity.
      * apply Forall_nil.
      * apply pairwise_disjoint_of_extents. cbn [map]. constructor.
      * split; [|split; [exact I | exact I]].
        cbn [ev1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E26, E28, E32, E33, !unsigned_lit_small by (unfold SB; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
        repeat match goal with |- _ /\ _ => split end; lia.
    + (* nb = 1 *)
      apply pa_entry_st_ok_full.
      * apply regs_ok_Eimg_Ereg.
      * vm_compute. reflexivity.
      * apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite Usp28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ q 0 1 (SOff 32 0) lo);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (Mlo ltac:(lia)).
      * apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
      * split; [|split; [exact I | exact I]].
        cbn [ev1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E26, E28, E32, E33, !unsigned_lit_small by (unfold SB; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
        repeat match goal with |- _ /\ _ => split end; lia.
    + (* nb = 2 *)
      assert (nb' = 0%nat) by lia; subst nb'.
      apply pa_entry_st_ok_full.
      * apply regs_ok_Eimg_Ereg.
      * vm_compute. reflexivity.
      * apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite Usp28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val segs E _ q 0 1 (SOff 32 0) lo);
             [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
           rewrite Z.add_0_r. exact (Mlo ltac:(lia)).
        -- apply (chunk_ok_val segs E _ q 1 1 (SOff 33 0) hi);
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
           exact (Mhi ltac:(lia)).
      * apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
      * split; [|split; [exact I | exact I]].
        cbn [ev1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E26, E28, E32, E33, !unsigned_lit_small by (unfold SB; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
        repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, ev1_SH, EBx. destruct nb as [|nb'].
    + constructor.
    + constructor; [|constructor].
      eapply (shent_ok_of_range segs (w_H W) mem E (SOff 26 0) 28 q (Z.of_nat (S nb')) q 0 (Z.of_nat (S nb'))).
      * apply (range_addressable_of_block0 ly St W mem md p n q (Z.of_nat (S nb')) HAR Hin); lia.
      * unfold U. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia).
        unfold SHADOW_OFF, SB. reflexivity.
      * unfold U. cbn [sv_denot]. rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * intros x Hx. unfold SHADOW_OFF.
        destruct Hph_ia as (Hp4 & [HAlo | [HAhi HAc]]);
          [unfold kLowShadowBeg in HAlo | unfold kHighMemBeg in HAhi]; lia.
Qed.

(* the state at the strnlen call: the cut invariant carried from the arm's entry (the arm reads, does not write, up
   to here), with the registers the tail reads. *)
Definition ev_P1_x (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_ev_call_strnlen) regs mem md /\
    lcut_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t true (lregs_P1 cx t) regs mem md W.

(* every carried byte is below the allocator's ceiling, or inside this function's frame *)
Lemma et_carry_low_x : forall cx m FF ly S (W : world segs) mem md pos a,
  AR0 ly S W mem md ->
  (forall b, In b (et_blks cx m) -> In b (ablocks B ly S)) ->
  In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  et_carry cx m FF a ->
  0 <= a < alloc_ceiling \/ (lf_F cx <= a < spZ (c_regs cx) /\ ~ (lf_F cx + 144 <= a < lf_F cx + 152)).
Proof.
  intros cx m FF ly S W mem md pos a HAR HBL Hfr HFF Hc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds0 ly S W mem md 1 pos HAR Hfr) as (HF0 & HF1 & _).
  replace (fs_frame_bytes 1) with 128 in HF1 by reflexivity. rewrite <- HFF in HF0, HF1.
  destruct Hc as [Hg | [He | [(b & n & Hb & Hr) | [Hf | [Hff | Hsh]]]]].
  - left. pose proof (pa_segs_low a (proj1 (HG a (HG_carry a Hg)))) as Hl.
    unfold kLowMemEnd in Hl. lia.
  - left. pose proof (pa_segs_low a (proj1 (HG a (et_errno_G a He)))) as Hl.
    unfold kLowMemEnd in Hl. lia.
  - left. destruct (al0_blocks ly S W mem md b n HAR (HBL (b, n) Hb)) as (_ & H4096 & Hceil & _).
    cbn [fst snd] in *. lia.
  - right. exact Hf.
  - left. lia.
  - left. pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd.
    pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hd0. unfold SB in *. lia.
Qed.

(* no carried byte lies in a block the tail allocates or frees (the block is read at its own state, which
   for malloc's new block is the state after the call) *)
Lemma et_carry_off_block_x : forall cx m FF ly S (W : world segs) mem md pos
    lyq Sq (Wq : world segs) memq mdq qq n0 a,
  AR0 ly S W mem md -> AR0 lyq Sq Wq memq mdq ->
  (forall b, In b (et_blks cx m) -> In b (ablocks B ly S)) ->
  In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  In (qq, n0) (ablocks B lyq Sq) ->
  (forall b n1, In (b, n1) (et_blks cx m) -> b + req_size n1 <= qq \/ qq + req_size n0 <= b) ->
  (forall x, (FF <= x < FF + 128 \/ SB + FF / 8 <= x < SB + FF / 8 + 16) -> ~ (qq <= x < qq + req_size n0)) ->
  alloc_ceiling + 32000 <= lf_F cx ->
  et_carry cx m FF a -> ~ (qq <= a < qq + req_size n0).
Proof.
  intros cx m FF ly S W mem md pos lyq Sq Wq memq mdq qq n0 a HAR HARq HBL Hfr HFF Hqin HQB HQF HFlo Hc Hq.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al0_blocks lyq Sq Wq memq mdq qq n0 HARq Hqin) as (_ & Hq4096 & Hqceil & _).
  destruct Hc as [Hg | [He | [(b & n1 & Hb & Hr) | [Hf | [Hff | Hsh]]]]].
  - exact (blk_img0 lyq Sq Wq memq mdq qq n0 a HARq Hqin Hq (proj1 (HG a (HG_carry a Hg)))).
  - exact (blk_img0 lyq Sq Wq memq mdq qq n0 a HARq Hqin Hq (proj1 (HG a (et_errno_G a He)))).
  - destruct (HQB b n1 Hb) as [Hd | Hd]; lia.
  - lia.
  - exact (HQF a (or_introl Hff) Hq).
  - exact (HQF a (or_intror Hsh) Hq).
Qed.

(* the carried bytes across an allocator call (malloc / free): its acall_kept and its errno clause *)
Lemma et_carry_acall_x : forall cx m FF ly S (W W' : world segs) mem mem' md pos
    lyq Sq (Wq : world segs) memq mdq qq n0 slo shi,
  AR0 ly S W mem md -> AR0 lyq Sq Wq memq mdq ->
  acall_kept segs B ly S W mem W' mem' slo shi (fun a => qq <= a < qq + req_size n0) ->
  (forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)) ->
  (forall b, In b (et_blks cx m) -> In b (ablocks B ly S)) ->
  In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  In (qq, n0) (ablocks B lyq Sq) ->
  (forall b n1, In (b, n1) (et_blks cx m) -> b + req_size n1 <= qq \/ qq + req_size n0 <= b) ->
  (forall x, (FF <= x < FF + 128 \/ SB + FF / 8 <= x < SB + FF / 8 + 16) -> ~ (qq <= x < qq + req_size n0)) ->
  alloc_ceiling + 32000 <= lf_F cx -> alloc_ceiling <= slo -> shi <= lf_F cx ->
  spZ (c_regs cx) <= 2 ^ 47 ->
  forall a, et_carry cx m FF a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros cx m FF ly S W W' mem mem' md pos lyq Sq Wq memq mdq qq n0 slo shi
    HAR HARq HK HERR HBL Hfr HFF Hqin HQB HQF HFlo Hslo Hshi Hsp47 a Hc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (et_carry_off_block_x cx m FF ly S W mem md pos lyq Sq Wq memq mdq qq n0 a
    HAR HARq HBL Hfr HFF Hqin HQB HQF HFlo Hc) as Hoff.
  destruct HK as (KA1 & KA2 & KA3 & KA4 & _ & _).
  destruct Hc as [Hg | [He | [(b & n1 & Hb & Hr) | [Hf | [Hff | Hsh]]]]].
  - apply KA3; [exact (proj1 (HG a (HG_carry a Hg))) | exact (proj1 (proj2 (HG a (HG_carry a Hg))))
    | exact (HERR_AP a Hg)].
  - replace a with (as_errno B + (a - as_errno B)) by lia. apply HERR. lia.
  - replace a with (b + (a - b)) by lia. apply (KA2 b n1 (a - b) (HBL (b, n1) Hb)); [lia|].
    cbv beta. replace (b + (a - b)) with a by lia. exact Hoff.
  - apply KA1; [|lia]. destruct Hf as (Hf1 & _). lia.
  - apply (KA4 1 pos a Hfr); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HFF;
      replace (fs_frame_bytes 1) with 128 by reflexivity; lia | cbv beta; exact Hoff].
  - apply (KA4 1 pos a Hfr); [right; unfold in_zr; cbn [fst snd]; rewrite <- HFF;
      replace (fs_frame_bytes 1 / 8) with 16 by reflexivity;
      unfold shadow_addr, SHADOW_OFF, SB in *; lia | cbv beta; exact Hoff].
Qed.

(* the carried bytes across an entry call (strnlen / memcpy): everything outside its written set and its
   scratch window below F *)
Lemma et_carry_entry_x : forall cx m FF ly S (W : world segs) mem md mem' pos (Wr : Z -> Prop) stk,
  AR0 ly S W mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (lf_F cx - stk <= a < lf_F cx) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall b, In b (et_blks cx m) -> In b (ablocks B ly S)) ->
  In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  (forall a, et_carry cx m FF a -> ~ Wr a) ->
  alloc_ceiling + 32000 <= lf_F cx -> spZ (c_regs cx) <= 2 ^ 47 -> 0 <= stk ->
  alloc_ceiling <= lf_F cx - stk ->
  forall a, et_carry cx m FF a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a.
Proof.
  intros cx m FF ly S W mem md mem' pos Wr stk HAR HK HBL Hfr HFF HWr HFlo Hsp Hstk Hstk2 a Hc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (et_carry_low_x cx m FF ly S W mem md pos a HAR HBL Hfr HFF Hc) as [Hlow | (Hfrm & _)];
    apply HK; solve [lia | exact (HWr a Hc)].
Qed.

(* a carried byte is kept: its view by the calls, its writability by GWR (a global), by the new state's own
   block presence (a live block), or by the journal's stack presence / the frame law (the frame) *)
Lemma et_carry_kept_x : forall cx m FF ly' S' (W W' : world segs) mem mem' md' pos',
  AR0 ly' S' W' mem' md' ->
  (forall b, In b (et_blks cx m) -> In b (ablocks B ly' S')) ->
  In (1, pos') (frames S') -> FF = frame_addr ly' 1 pos' ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W') mem' a) ->
  lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= lf_F cx + 352 ->
  (forall a, et_carry cx m FF a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  forall a, et_carry cx m FF a -> abyte_kept W mem W' mem' a.
Proof.
  intros cx m FF ly' S' W W' mem mem' md' pos' HAR HBL Hfr HFF HPRES HF1 HF2 KV a Hc.
  destruct (al0_frames ly' S' W' mem' md' 1 pos' HAR Hfr) as (_ & _ & HFFp & HFFsh).
  rewrite <- HFF in HFFp, HFFsh. replace (fs_frame_bytes 1) with 128 in HFFp by reflexivity.
  replace (fs_frame_bytes 1 / 8) with 16 in HFFsh by reflexivity.
  pose proof (KV a Hc) as Hv.
  destruct Hc as [Hg | [He | [(b & n1 & Hb & Hr) | [Hf | [Hff | Hsh]]]]].
  - exact (et_kept_G W W' mem mem' a (HG_carry a Hg) Hv).
  - exact (et_kept_G W W' mem mem' a (et_errno_G a He) Hv).
  - apply et_kept_apres; [exact Hv|].
    destruct (al0_blocks ly' S' W' mem' md' b n1 HAR (HBL (b, n1) Hb)) as (_ & _ & _ & _ & Hpres & _).
    exact (proj1 (Hpres a Hr)).
  - apply et_kept_apres; [exact Hv|]. apply HPRES. unfold LLVMF_STK. lia.
  - apply et_kept_apres; [exact Hv|]. exact (proj1 (HFFp a Hff)).
  - apply et_kept_apres; [exact Hv|].
    replace a with (shadow_addr FF + (a - SB - FF / 8)) by (unfold shadow_addr, SHADOW_OFF, SB in *; lia).
    exact (proj1 (HFFsh (a - SB - FF / 8) ltac:(lia))).
Qed.

(* no carried byte is the in.n slot the tail stores to *)
Lemma et_carry_off_slot_x : forall cx m FF ly S (W : world segs) mem md pos a,
  AR0 ly S W mem md -> (forall b, In b (et_blks cx m) -> In b (ablocks B ly S)) ->
  In (1, pos) (frames S) -> FF = frame_addr ly 1 pos -> alloc_ceiling + 32000 <= lf_F cx ->
  et_carry cx m FF a -> ~ (lf_F cx + 144 <= a < lf_F cx + 152).
Proof.
  intros cx m FF ly S W mem md pos a HAR HBL Hfr HFF HFlo Hc.
  destruct (et_carry_low_x cx m FF ly S W mem md pos a HAR HBL Hfr HFF Hc) as [Hlow | (_ & Hns)];
    [lia | exact Hns].
Qed.

(* the frame at a later state, from the bytes the calls kept and the new state's own presence *)
Lemma et_frame_at_x : forall cx FF ly S (Wc W : world segs) memc mem' md' pos,
  aframe_at cx true FF Wc memc -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= lf_F cx + 352 ->
  alloc_ceiling + 32000 <= lf_F cx ->
  AR0 ly S W mem' md' -> In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) ->
     aview segs (w_H W) mem' a = aview segs (w_H Wc) memc a) ->
  (forall a, FF <= a < FF + 128 -> aview segs (w_H W) mem' a = aview segs (w_H Wc) memc a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> aview segs (w_H W) mem' a = aview segs (w_H Wc) memc a) ->
  aframe_at cx true FF W mem'.
Proof.
  intros cx FF ly S Wc W memc mem' md' pos Hfa HF1 HF2 HFlo HAR Hfr HFF HPRES KH KF KS.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al0_frames ly S W mem' md' 1 pos HAR Hfr) as (_ & _ & HFFp & HFFsh).
  rewrite <- HFF in HFFp, HFFsh. replace (fs_frame_bytes 1) with 128 in HFFp, HFFsh by reflexivity.
  apply (et_frame_kept cx true FF Wc W memc mem' Hfa HF1).
  - intros x Hx Hx144. apply et_kept_apres; [apply KH; assumption | apply HPRES; unfold LLVMF_STK; lia].
  - intros x Hx _. exact (apresent_writable segs _ _ _ (HPRES x ltac:(unfold LLVMF_STK; lia))).
  - intros x Hx. apply et_kept_apres; [apply KF; assumption | exact (proj1 (HFFp x Hx))].
  - intros x Hx. apply et_kept_apres; [apply KS; assumption |].
    replace x with (shadow_addr FF + (x - SB - FF / 8)) by (unfold shadow_addr, SHADOW_OFF, SB in *; lia).
    exact (proj1 (HFFsh (x - SB - FF / 8) ltac:(lia))).
Qed.

(* the fake frame's flag word (lcut's conjunct after aframe_at) at a later state: its 8 bytes are fake-frame bytes,
   kept like the rest of the fake frame (et_frame_at's KF) *)
Lemma et_flag_at_x : forall FF ly S (Wc W : world segs) memc mem' md' pos v,
  sv8 Wc memc (FF + 120) v ->
  AR0 ly S W mem' md' -> In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  (forall a, FF <= a < FF + 128 -> aview segs (w_H W) mem' a = aview segs (w_H Wc) memc a) ->
  sv8 W mem' (FF + 120) v.
Proof.
  intros FF ly S Wc W memc mem' md' pos v Hv HAR Hfr HFF KF.
  destruct (al0_frames ly S W mem' md' 1 pos HAR Hfr) as (_ & _ & HFFp & _).
  rewrite <- HFF in HFFp. replace (fs_frame_bytes 1) with 128 in HFFp by reflexivity.
  apply (et_sv8_kept Wc W memc mem'); [|exact Hv].
  intros x Hx. apply et_kept_apres; [apply KF; lia | exact (proj1 (HFFp x ltac:(lia)))].
Qed.

(* the new block of an allocator call is disjoint from every block before it (W_lp_tail.v lpt_new_disj) *)
Lemma et_new_disj_x : forall ly2 S2 (W2 : world segs) mem2 md2 lyc Sc res n b m0,
  AR0 ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] ->
  In (b, m0) (ablocks B lyc Sc) ->
  b + req_size m0 <= res \/ res + req_size n <= b.
Proof.
  intros ly2 S2 W2 mem2 md2 lyc Sc res n b m0 HAR2 Ebl Hin. apply in_split in Hin as (l1 & l2 & E1).
  pose proof (sep_blocks_pos0 ly2 S2 W2 mem2 md2 (b, m0) (res, n) l1 l2 [] HAR2) as Hd.
  rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

Lemma et5_entry_x : forall (W : world segs) regs mem ly S md F qq sl,
  AR0 ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 23 = w64 sl -> getr regs 25 = w64 qq -> getr regs 26 = w64 SB ->
  alloc_ceiling + 32000 <= F -> F + 320 <= 2 ^ 47 -> 0 <= sl <= 2 ^ 26 ->
  In (qq, sl + 1) (ablocks B ly S) ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (et5_extra (qq + sl)))) ss_et5
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_ev_ret_memcpy)) mem (seg_rom segs)))
  /\ sh_ok segs etBx et5_SH (Eimg (Ereg regs (et5_extra (qq + sl)))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem ly S md F qq sl HAR R9 R23 R25 R26 HF1 HF2 Hsl Hqin HWF.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hreq : req_size (sl + 1) = sl + 1) by (unfold req_size; destruct (Z.eqb_spec (sl + 1) 0); lia).
  destruct (al0_blocks ly S W mem md _ _ HAR Hqin) as (_ & Hq4096 & Hqceil & Hqapp & Hqpres & _).
  rewrite Hreq in Hqceil, Hqapp, Hqpres.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs (et5_extra (qq + sl)))) as E eqn:HE.
  assert (EEn : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
  { intros n0 r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEn 9%nat 9%bv eq_refl); exact R9).
  assert (E23 : ew E 23 = Z_to_bv 64 sl) by (rewrite (EEn 23%nat 23%bv eq_refl); exact R23).
  assert (E25 : ew E 25 = Z_to_bv 64 qq) by (rewrite (EEn 25%nat 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEn 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (qq + sl))
    by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = qq + sl) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (UB : U E etBx = SHADOW_OFF).
  { unfold etBx. rewrite (U_atom E 26 SB E26) by (unfold SB; lia). reflexivity. }
  split.
  - unfold ss_et5. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold et5_rE, et5_rF. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). exact (proj1 (Hqpres (qq + sl + o) ltac:(lia))).
      * rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply HWF. lia.
    + apply pairwise_disjoint_of_extents. unfold et5_rE, et5_rF, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; try exact I; try lia.
    + split; [|split; [exact I | split; [|exact I]]].
      * cbn [et5_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E9, E23, E25, E26, E32, !unsigned_lit_small by (unfold SB; lia).
        rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [et5_facts f_alias alias_ok et5_alias sv_denot]. rewrite E23, E25, E32.
        rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r, zalu64_sound.
        unfold zalu64, zcanon, M64. cbn [zalu_raw].
        rewrite (Z.mod_small qq), (Z.mod_small sl) by lia. rewrite (Z.mod_small (qq + sl)) by lia. reflexivity.
  - unfold sh_ok, et5_SH. constructor; [|constructor].
    apply (shent_ok_of_range segs (w_H W) mem E etBx 32 (qq + sl) 1 (qq + sl) 0 1).
    + apply (range_addressable_of_block0 ly S W mem md qq (sl + 1));
        [exact HAR | exact Hqin | lia | rewrite Hreq; lia].
    + exact UB.
    + rewrite (U_atom E 32 (qq + sl) E32) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hqapp.
      unfold SHADOW_OFF. lia.
Qed.

(* ---- the tail after relay_event (rep-2's plan, steps 1-5): the transport across relay_event, check_shape_event
   and free, the stream's errno rebuilt, the latch's entry state ---- *)
(* the live blocks are pairwise distinct (W_gesture_end.v ablocks_nodup) *)
Lemma et_nodup_x : forall ly S (W : world segs) mem md, AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    destruct (al0_blocks ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al0_sep ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* across an allocator call (free) *)
Lemma et_cr_acall_x : forall cx FF Gs bl ly S (W W' : world segs) mem mem' md pos qq n0,
  AR0 ly S W mem md ->
  acall_kept segs B ly S W mem W' mem' (lf_F cx - ASTACK) (lf_F cx) (fun a => qq <= a < qq + req_size n0) ->
  In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  (forall a, inG Gs a -> inG G_fr a /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  (forall b n, In (b, n) bl -> In (b, n) (ablocks B ly S) /\ (forall a, b <= a < b + req_size n -> ~ (qq <= a < qq + req_size n0))) ->
  (forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) -> ~ (qq <= a < qq + req_size n0)) ->
  alloc_ceiling + 32000 <= lf_F cx -> spZ (c_regs cx) <= 2 ^ 47 ->
  forall a, et_cr cx FF Gs bl a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros cx FF Gs bl ly S W W' mem mem' md pos qq n0 HAR HK Hfr HFF HGs Hbl HQF HFlo Hsp a Hc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HK as (KA1 & KA2 & KA3 & KA4 & _ & _).
  destruct Hc as [Hg | [(b & n & Hb & Hr) | [Hf | [Hff | Hsh]]]].
  - destruct (HGs a Hg) as (HGf & He). destruct (HG a HGf) as (Hi & Ho & _). exact (KA3 a Hi Ho He).
  - destruct (Hbl b n Hb) as (Hin & Hnq).
    replace a with (b + (a - b)) by lia. apply (KA2 b n (a - b) Hin); [lia|].
    cbv beta. replace (b + (a - b)) with a by lia. exact (Hnq a Hr).
  - apply KA1; [|unfold ASTACK]; lia.
  - apply (KA4 1 pos a Hfr); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HFF;
      replace (fs_frame_bytes 1) with 128 by reflexivity; lia | cbv beta; exact (HQF a (or_introl Hff))].
  - apply (KA4 1 pos a Hfr); [right; unfold in_zr; cbn [fst snd]; rewrite <- HFF;
      replace (fs_frame_bytes 1 / 8) with 16 by reflexivity;
      unfold shadow_addr, SHADOW_OFF, SB in *; lia | cbv beta; exact (HQF a (or_intror Hsh))].
Qed.

Lemma et_aout_errno_x : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' c O mx no cap out v,
  AR0 ly S W mem md ->
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  (forall x, inG et_GO x -> abyte_kept W mem W' mem' x) ->
  (forall b n i, In (b, n) (aout_blks cap out) -> 0 <= i < n -> abyte_kept W mem W' mem' (b + i)) ->
  (forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S')) ->
  val_mem segs (arm W' mem') (as_errno B) 4 v -> awr W' mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
  aout_at B fr_RG ly' S' W' mem' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) v) O mx no cap out.
Proof.
  intros ly S W mem md ly' S' W' mem' c O mx no cap out v HAR
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) KC KB HB Hv Hw Hvr.
  assert (KR : forall lo n, (forall x, lo <= x < lo + n -> inG et_GO x) ->
    forall x, lo <= x < lo + Z.of_nat (Z.to_nat n) -> abyte_kept W mem W' mem' x)
    by (intros lo n H x Hx; apply KC; apply H; lia).
  assert (KR' : forall lo n, (forall x, lo <= x < lo + n -> inG et_GO x) ->
    forall x, lo <= x < lo + n -> abyte_kept W mem W' mem' x) by (intros lo n H x Hx; exact (KC x (H x Hx))).
  unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm W mem); [apply (KR (rg_send_max fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H1]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_send_max fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H2]|].
  split; [apply (akept_vm W mem); [apply (KR (rg_nout fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H3]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_nout fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H4]|].
  split; [apply (akept_vm W mem); [apply (KR (rg_capout fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H5]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_capout fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H6]|].
  split; [apply (akept_vm W mem); [apply (KR (rg_out fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H7]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_out fr_RG) 8); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H8]|].
  split; [apply (akept_vm W mem); [apply (KR (rg_client fr_RG) 4); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H9]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_client fr_RG) 4); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H10]|].
  split; [apply (akept_vm W mem); [apply (KR (rg_client_broken fr_RG) 1); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H11]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_client_broken fr_RG) 1); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H12]|].
  split; [apply (akept_vm W mem); [apply (KR (rg_send_dead fr_RG) 1); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H13]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_send_dead fr_RG) 1); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H14]|].
  split; [apply (akept_vm W mem); [apply (KR (rg_send_eintr fr_RG) 1); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H15]|].
  split; [apply (akept_awr W mem); [apply (KR' (rg_send_eintr fr_RG) 1); intros x Hx; clear - Hx; unfold et_GO; et_inG | exact H16]|].
  split; [exact Hv|]. split; [exact Hw|]. split; [exact Hvr|].
  do 6 (split; [assumption|]).
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|].
  split; [apply HB; unfold aout_blks; rewrite Ec; left; reflexivity|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  replace x with (out + (x - out)) by lia. apply (KB out cap (x - out)); [|lia].
  unfold aout_blks. rewrite Ec. left. reflexivity.
Qed.

(* LS_cnt's guard (s5-r1d's msz_ok, ReplyLSCntM.v:50) at a cut's model: the relay's entries have a capacity and
   key texts of bounded length (aentry_ok, W_rep.v:118 / :139), and each held slot's two line lists have records of
   bounded length (alist_at .. true, W_rep.v:103) *)
Lemma ev_msz_x : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  Forall (fun e0 => 0 <= re_cap e0 <= 16384 /\
    Forall (fun kk => Z.of_nat (length (gestures_end_b_c.key_text kk)) <= APARTIAL) (re_keys e0)) (lm_es m) /\
  Forall (fun o => match o with
                   | Some h => Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_expected h)) /\
                               Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_held h))
                   | None => True end) (lm_hs m).
Proof.
  intros ly S W mem m (Hlen & Hslots & HREL & _).
  assert (Hlist : forall LA l, alist_at B ly S W mem LA l true ->
      Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs l)).
  { intros LA l (_ & _ & _ & _ & _ & _ & _ & _ & HF). revert HF. apply Forall_impl.
    intros r (_ & _ & Hr & _). exact (proj2 (Hr eq_refl)). }
  split.
  - pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE & _). revert HAE. apply Forall_impl.
    intros e0 He0.
    pose proof He0 as (_ & _ & _ & _ & _ & Hcap & _). split; [lia|].
    pose proof He0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK).
    revert HK. apply Forall_impl. intros kk (_ & _ & _ & Hkk). lia.
  - apply Forall_forall. intros o Ho.
    destruct (In_nth_error _ _ Ho) as (i & Hi).
    assert (Hi4 : (i < 4)%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (Hslots i Hi4) as Hsl.
    rewrite (nth_error_nth _ _ None Hi) in Hsl.
    destruct o as [h|]; [|exact I]. cbn [aslot] in Hsl.
    pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEX & HHD & _).
    split; [exact (Hlist _ _ HEX) | exact (Hlist _ _ HHD)].
Qed.

(* ---------------------------------------------------------------- route R
   (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sections 0, 4, 5): the arm at a world relation R.  relay_event's send_line reallocs and the free
   re-hides the dead shadow, so at R := wle' segs RZ_cf a call step gives only `R W W'`.  The lemmas below are the
   strict walk (_event.v's, converted to ARx) at R, with: the cut's journal ajournal_gx_xR R (cut_x Section wR's
   lcut_xR / INV_A_xR / INV_K_xR); the step relation SRrG segs R; the tail's runs W_journal_x.v paj_run_x_xG /
   paj_run_to_x_xG (branches W_kit.v paj_branch_xR); malloc and free by their R rules AMALLOC_R / AFREE_R
   (W_journal_x.v Section hc), whose call-boundary premise RO at the call memory RO_ARx gives from the call state's
   ARx (part 3c took memnorm out of the rules); relay_event by its R contract RE_R (W_contract_xR.v re_spec_xR); and
   the engine's R twins (ajournal_gx_*_xR, aj_gx_entry_at_xR, awr_new_block_any_xR, afn_pre_x_atR,
   aview_above_of_journal_xR).  strnlen, __asan_memcpy and check_shape_event cannot free: they keep their strict
   contracts (ASTRNLEN, AMEMCPY, CSE), lifted by SRr_SRrG (WLE_R) and, for check_shape_event's post journal,
   ajournal_gx_xR_mono (ev_gx_lift_xR).  The arm entry's straight run (ev_to_P1_xR) moves no world: its strict run
   over the R journal (paj_run_x_xR) lifts by SRr_SRrG.  After this Section, the strict lemmas that have a twin here
   are the twin at R := wle (no premise is missing at wle since part 3c). *)
Section evxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* the R rules' call-boundary premises (QMm fit (1)), at the call memory: from the call state's ARx *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> RO mem.
(* malloc (0x84acc) and free (0x84b1c) at R: W_journal_x.v Section hc's R rules, at the same K0 tables *)
Hypothesis AMALLOC_R : amalloc_cf_rule_c_xR segs B PST ARx MT MMAX RP RO CTX_AMALLOC R.
Hypothesis AFREE_R : afree_cf_rule_c_xR segs B PST ARx MT RP RO CTX_AFREE R.
(* relay_event (0x84b0c) at R: W_contract_xR.v re_spec_xR at relay_event's own G (_event.v's et_GRE) *)
Hypothesis RE_R : re_spec_xR (PI := PB_fr) B PST ARx R MT RP MMAX et_GRE fr_RG (BASE + AF_fr_relay_event).
(* the R journal at the empty ghost list, and the engine's R twins at it *)
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR (R := R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
Local Notation ajournal_gx_AR0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_xR (R := R) segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_xR (R := R) segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_pack0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k memS :=
  (ajournal_gx_pack_xR (R := R) segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k memS).
Local Notation ajournal_gx_G_mono0R G G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_xR (R := R) segs B PST ARx G G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation aj_gx_entry_at0R G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc :=
  (aj_gx_entry_at_xR (PI := PB_fr) B PST ARx LAWS R_trans WLE_R G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S []
     W0 mem md own lyc Sc []).
Local Notation awr_new_block_any0R STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 :=
  (awr_new_block_any_xR (R := R) segs B PST ARx LAWS STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k ly2 S2 []).
(* the strict runs over the R journal (ev_to_P1_xR, lifted) and the runs concluding SRrG segs R (the tail) *)
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRG := paj_branch_xR (PI := PB_fr) (R := R).
(* a strict gx journal (a strict callee's post journal) is one at R (W_journal_x.v ajournal_gx_xR_mono, WLE_R) *)
Lemma ev_gx_lift_xR {Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq} :
  ajournal_gx_x segs B PST ARx Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq ->
  ajournal_gx_xR segs B PST ARx R Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq.
Proof. intros HJ. eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ]. Qed.
(* ev_aftok_new_block0 at AJi0R: its proof (the freed clause is no world clause) *)
Lemma ev_aftok_new_block0R : forall STK sp0 FP ly S W0 mem md own lyc Sc (W : world segs) memc mdc k ly2 S2
    (W2 : world segs) mem2 md2 res n,
  AJi0R STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  AR0 ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> 0 <= n ->
  aftok FP (ablocks B ly S) (res, n).
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n HJ HAR2 Ebl Hn H0 i Hi.
  cbn [fst snd] in *.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B lyc Sc)) as [Hc | Hc].
  - exfalso. apply in_split in Hc as (l1 & l2 & E1).
    pose proof (sep_blocks_pos_x segs B ARx LAWS ly2 S2 [] W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR2) as Hd.
    rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
    assert (0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); cbn; lia). lia.
  - exact (Hgone res n i H0 Hc Hi).
Qed.
(* ajournal_gx_rom_view0 at AJ0R: W_journal_x's ajournal_gx_rom_view_xR *)
Lemma ajournal_gx_rom_view0R : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_out segs B G -> rom_view segs W mem -> rom_view segs W' mem'.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR Hrv.
  apply (ajournal_gx_rom_view_xR (R := R) segs B PST ARx LAWS pa_segs_low G XO OUT STK sp0 FP ly S [] W mem md own ly' S' []
    W' mem' md' k HJ HR); [|exact Hrv].
  intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr].
Qed.
(* ev_P1_x at R: the cut lcut_xR (cut_x Section wR), its journal at R *)
Definition ev_P1_xR (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_ev_call_strnlen) regs mem md /\
    lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t true (lregs_P1 cx t) regs mem md W.

(* ev_P1_of_x at R: its proof *)
Lemma ev_P1_of_xR : forall cx t W (regsD regs regs' : bvmap 5 word) mem md' own ly3 S3 k m fpos,
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) own ly3 S3 W mem md' k ->
  own = [(1, fpos)] -> aframe_at cx true (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 ->
  NP S3 -> RINV cx t m ->
  (forall r, In r EV_KEPT -> getr regs' r = getr regs r) ->
  (forall r, In r jt_kept -> getr regs r = getr regsD r) ->
  lregs_common B cx (frame_addr ly3 1 fpos) regsD -> getr regsD 27 = w64 t -> 0 <= t < OPS_MAX ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  getr regs' 10 = w64 (ev_parg cx m) -> getr regs' 11 = w64 (ev_len cx m) -> getr regs' 22 = w64 (ev_parg cx m) ->
  getr regs' 20 = w64 (c_n cx - ev_k1 cx m) -> getr regs' 21 = w64 (ev_len cx m) ->
  ev_P1_xR cx t W (cfg_at segs (fr_B0 + AF_ev_call_strnlen) regs' mem md').
Proof.
  intros cx t W regsD regs regs' mem md' own ly3 S3 k m fpos HJ Hown HFR HFL HMOD HIN HRV HSEP HLS HNP HRI KR KD
    (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4) R27 Ht Hk HO Hop7 Q10 Q11 Q22 Q20 Q21.
  assert (K : forall r, In r EV_KEPT -> getr regs' r = getr regsD r).
  { intros r Hr. rewrite (KR r Hr). apply KD. cbv [EV_KEPT In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbv; tauto|]). destruct Hr. }
  exists regs', mem, md'. split; [reflexivity|].
  exists own, ly3, S3, [], k, m, fpos.
  do 11 (split; [assumption|]).
  split; [rewrite (K 2%bv ltac:(cbv; tauto)); exact C2|].
  split; [rewrite (K 8%bv ltac:(cbv; tauto)); exact C8|].
  split; [rewrite (K 9%bv ltac:(cbv; tauto)); exact C9|].
  split; [rewrite (K 18%bv ltac:(cbv; tauto)); exact C18|].
  split; [rewrite (K 19%bv ltac:(cbv; tauto)); exact C19|].
  split; [rewrite (K 23%bv ltac:(cbv; tauto)); exact C23|].
  split; [rewrite (K 24%bv ltac:(cbv; tauto)); exact C24|].
  split; [rewrite (K 25%bv ltac:(cbv; tauto)); exact C25|].
  split; [rewrite (K 26%bv ltac:(cbv; tauto)); exact C26|].
  split; [rewrite (K 3%bv ltac:(cbv; tauto)); exact C3|].
  split; [rewrite (K 4%bv ltac:(cbv; tauto)); exact C4|].
  split; [rewrite (K 27%bv ltac:(cbv; tauto)); exact R27|].
  repeat (split; [assumption|]). assumption.
Qed.

(* ev_to_P1_x at R: the run moves no world, so its strict run over the R journal (RUNR / RUNTOR) lifts by SRr_SRrG *)
Lemma ev_to_P1_xR : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 7 cx [] t W c -> SRrG segs R W c (ev_P1_xR cx t).
Proof.
  intros cx t W c HB HA.
  apply (SRr_SRrG segs R WLE_R).
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & Hop11 & Hjour & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HAF & HFL & HAM & HAI & HROMc & HSEP & HLS & HNP & HRI & HRD).
  hp0gR HJ.
  destruct HRD as (HRC & Hr6 & Hr7 & Hr27 & Ht & Hk & HO & HRDop).
  set (op := in_byte cx (lm_k m) mod 10) in *.
  assert (Hopb : 0 <= op < 10) by (unfold op; apply Z.mod_pos_bound; lia).
  destruct HRDop as (Hop & HRDrest).
  assert (Hoe : op = 7).
  { assert (He : w64 op = w64 7) by (rewrite <- Hop, <- Hop11; reflexivity).
    apply (f_equal bv_unsigned) in He. unfold w64 in He.
    rewrite !unsigned_lit_small in He by lia. exact He. }
  assert (Hpicks : picks op = false) by (rewrite Hoe; reflexivity).
  rewrite Hpicks in HRDrest. destruct HRDrest as (H28 & H29 & H21).
  subst c.
  destruct HRC as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HB as (HAI0 & HPRE).
  pose proof HPRE as (_ & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof (ajournal_gx_AR0R G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ own ly3 S3 W mem md k HJ) as HAR.
  pose proof HAI as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (al0_blocks ly3 S3 W mem md (c_p cx) (c_n cx) HAR Hblk) as (Hp16 & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
  set (nb := Z.to_nat (Z.min (c_n cx - lm_k m - 1) 2)).
  set (lo := if 1 <=? c_n cx - lm_k m - 1 then in_byte cx (lm_k m + 1) else 0).
  set (hi := if 2 <=? c_n cx - lm_k m - 1 then in_byte cx (lm_k m + 2) else 0).
  assert (Rlo : 0 <= lo < 256) by (unfold lo; destruct (1 <=? _); [apply ev_in_byte_range | lia]).
  assert (Rhi : 0 <= hi < 256) by (unfold hi; destruct (2 <=? _); [apply ev_in_byte_range | lia]).
  assert (Mlo : (1 <= nb)%nat -> val_mem segs (mrestrict (w_H W) mem) (c_p cx + lm_k m + 1) 1 lo).
  { intros Hn1. assert (Hr1 : 1 <= c_n cx - lm_k m - 1) by (unfold nb in Hn1; lia).
    unfold lo. rewrite (proj2 (Z.leb_le _ _) Hr1). rewrite <- Z.add_assoc.
    apply (ev_byte cx ly3 S3 W mem (lm_k m + 1) Hnlen HAI). lia. }
  assert (Mhi : (2 <= nb)%nat -> val_mem segs (mrestrict (w_H W) mem) (c_p cx + lm_k m + 1 + 1) 1 hi).
  { intros Hn2. assert (Hr2 : 2 <= c_n cx - lm_k m - 1) by (unfold nb in Hn2; lia).
    unfold hi. rewrite (proj2 (Z.leb_le _ _) Hr2).
    replace (c_p cx + lm_k m + 1 + 1) with (c_p cx + (lm_k m + 2)) by lia.
    apply (ev_byte cx ly3 S3 W mem (lm_k m + 2) Hnlen HAI). lia. }
  assert (R28 : getr regs 28 = w64 (c_p cx + lm_k m + 1)) by (rewrite (Hkept 28%bv ltac:(cbv; tauto)); exact H28).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (Hkept 26%bv ltac:(cbv; tauto)); exact C26).
  destruct (ev1_entry_x W regs mem nb (c_p cx + lm_k m + 1) lo hi ly3 S3 md (c_p cx) (c_n cx)
    ltac:(unfold nb; lia) R28 R26 HAR Hblk ltac:(lia) ltac:(unfold nb; lia) Mlo Mhi Rlo Rhi) as [HS SHOK].
  remember (Eimg (Ereg regs (ev1_extra lo hi))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ev1_extra lo hi)) E)
    by (rewrite HE; split; [intros q0 Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q0 (rr : bv 5), Z.of_nat q0 = bv_unsigned rr -> ew E q0 = getr regs rr)
    by (intros q0 rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E7 : ew E 7 = Z_to_bv 64 1)
    by (rewrite (EEo 7%nat 7%bv eq_refl), (Hkept 7%bv ltac:(cbv; tauto)); exact Hr7).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + lm_k m + 1)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1))
    by (rewrite (EEo 29%nat 29%bv eq_refl), (Hkept 29%bv ltac:(cbv; tauto)); exact H29).
  assert (E32 : ew E 32 = Z_to_bv 64 lo)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 hi)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 7)) with (Z_to_bv 64 (BASE + AF_arm_event)).
  assert (Hc3 : c_n cx - lm_k m - 1 = 0 \/ c_n cx - lm_k m - 1 = 1 \/ 2 <= c_n cx - lm_k m - 1) by lia.
  destruct Hc3 as [Hr | [Hr | Hr]].
  - (* rem = 0: beqz t4 to 0x846d0 (s4 = a1 = a2 = 0), to 0x84aa8, s5 = 0, a0 = s6 = t3 *)
    assert (Enb : nb = 0%nat) by (unfold nb; lia). rewrite Enb in HS, SHOK.
    norm_ss HS. cbn [ev1_SH] in SHOK.
    psrr_branch_tok RUNR BR HS SHOK EBspan.
    2: { exfalso. rewrite branch_eq_U, (U_atom E 29 _ E29), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia. }
    paj_run_to_tok_x RUNTOR HS HJ SHOK EBspan AF_ev_call_strnlen.
    { ev_awr. }
    ev_meq HF Em.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (ev1_extra lo hi)) Ev)
        by (split; [intros q0 Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q0 Hq) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ EV_KEPT HS HAEv ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    ev_prreg_raw HS (10%bv : bv 5) Q10. ev_prreg_raw HS (11%bv : bv 5) Q11. ev_prreg_raw HS (20%bv : bv 5) Q20.
    ev_prreg_raw HS (21%bv : bv 5) Q21. ev_prreg_raw HS (22%bv : bv 5) Q22.
    pmkst HS. rewrite Em in *.
    apply SRr_ret.
    lazymatch goal with |- ev_P1_xR _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} =>
      change (ev_P1_xR cx t W (cfg_at segs (fr_B0 + AF_ev_call_strnlen) r mm d)) end.
    assert (Hpg : ev_parg cx m = c_p cx + lm_k m + 1) by (unfold ev_parg, ev_cons2; lia).
    assert (Hln : ev_len cx m = 0)
      by (unfold ev_len; destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); [lia | reflexivity]).
    assert (Hk1 : c_n cx - ev_k1 cx m = 0) by (unfold ev_k1, ev_cons2; lia).
    apply (ev_P1_of_xR cx t W regsD regs _ mem _ own ly3 S3 k m fpos HJ Hown HAF HFL HAM HAI HROMc HSEP HLS HNP HRI KR Hkept
      (conj C2 (conj C8 (conj C9 (conj C18 (conj C19 (conj C20 (conj C23 (conj C24 (conj C25 (conj C26 (conj C3 C4)))))))))))
      Hr27 Ht Hk HO Hoe).
    + rewrite Q10, Hpg. apply ev_sv_of_U; [apply (U_atom E 28 _ E28) | ]; lia.
    + rewrite Q11, Hln. reflexivity.
    + rewrite Q22, Hpg. apply ev_sv_of_U; [apply (U_atom E 28 _ E28) | ]; lia.
    + rewrite Q20, Hk1. reflexivity.
    + rewrite Q21, Hln. reflexivity.
  - (* rem = 1: the shadow check of p0 (report 0x84b9c refuted), lo = p0[0]; bne t4,t2 falls through: s4 = a2 = 0,
       t3 = p0 + 1; 0x84aa8 s5 = lo, bltu s5,0 not taken, s5 = 0 *)
    assert (Enb : nb = 1%nat) by (unfold nb; lia). rewrite Enb in HS, SHOK.
    norm_ss HS. cbn [ev1_SH] in SHOK.
    psrr_branch_tok RUNR BR HS SHOK EBspan.
    { exfalso. rewrite branch_eq_U, (U_atom E 29 _ E29), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia. }
    clear Hc.
    paj_run_tok_x RUNR HS HJ SHOK EBspan.
    { ev_awr. }
    ev_meq HF Em1. clear HF HFr HG0.
    ev_V HS E7 V7. ev_V HS E29 V29.
    psrr_branch_tok RUNR BR HS SHOK EBspan.
    { exfalso. rewrite branch_ne_U, (U_atom _ 29 _ V29), (U_atom _ 7 _ V7) in Hc by lia.
      apply negb_true_iff, Z.eqb_neq in Hc. lia. }
    clear Hc V7 V29.
    paj_run_to_tok_x RUNTOR HS HJ SHOK EBspan AF_ev_call_strnlen.
    { ev_awr. }
    ev_meq HF Em2.
    ev_V HS E28 V28.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (ev1_extra lo hi)) Ev)
        by (split; [intros q0 Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q0 Hq) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ EV_KEPT HS HAEv ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    ev_prreg_raw HS (10%bv : bv 5) Q10. ev_prreg_raw HS (11%bv : bv 5) Q11. ev_prreg_raw HS (20%bv : bv 5) Q20.
    ev_prreg_raw HS (21%bv : bv 5) Q21. ev_prreg_raw HS (22%bv : bv 5) Q22.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret.
    lazymatch goal with |- ev_P1_xR _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} =>
      change (ev_P1_xR cx t W (cfg_at segs (fr_B0 + AF_ev_call_strnlen) r mm d)) end.
    assert (Hpg : ev_parg cx m = c_p cx + lm_k m + 1 + 1) by (unfold ev_parg, ev_cons2; lia).
    assert (Hln : ev_len cx m = 0)
      by (unfold ev_len; destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); [lia | reflexivity]).
    assert (Hk1 : c_n cx - ev_k1 cx m = 0) by (unfold ev_k1, ev_cons2; lia).
    apply (ev_P1_of_xR cx t W regsD regs _ mem _ own ly3 S3 k m fpos HJ Hown HAF HFL HAM HAI HROMc HSEP HLS HNP HRI KR Hkept
      (conj C2 (conj C8 (conj C9 (conj C18 (conj C19 (conj C20 (conj C23 (conj C24 (conj C25 (conj C26 (conj C3 C4)))))))))))
      Hr27 Ht Hk HO Hoe).
    + rewrite Q10, Hpg. apply ev_sv_of_U; [apply (U_atom_off _ 28 _ 1 V28) | ]; lia.
    + rewrite Q11, Hln. reflexivity.
    + rewrite Q22, Hpg. apply ev_sv_of_U; [apply (U_atom_off _ 28 _ 1 V28) | ]; lia.
    + rewrite Q20, Hk1. reflexivity.
    + rewrite Q21, Hln. reflexivity.
  - (* rem >= 2: as rem = 1 to bne t4,t2, which jumps to 0x84a88: the shadow check of p0 + 1 (report 0x84bec
       refuted), hi = p0[1], s4 = rem - 2, t3 = p0 + 2, a2 = hi << 8; 0x84aa8 s5 = a2 | a1 = the u16;
       bltu s5,s4: len = min (u16, rem - 2) *)
    assert (Enb : nb = 2%nat) by (unfold nb; lia). rewrite Enb in HS, SHOK.
    norm_ss HS. cbn [ev1_SH] in SHOK.
    psrr_branch_tok RUNR BR HS SHOK EBspan.
    { exfalso. rewrite branch_eq_U, (U_atom E 29 _ E29), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia. }
    clear Hc.
    paj_run_tok_x RUNR HS HJ SHOK EBspan.
    { ev_awr. }
    ev_meq HF Em1. clear HF HFr HG0.
    ev_V HS E7 V7. ev_V HS E29 V29.
    psrr_branch_tok RUNR BR HS SHOK EBspan.
    2: { exfalso. rewrite branch_ne_U, (U_atom _ 29 _ V29), (U_atom _ 7 _ V7) in Hc by lia.
         apply negb_false_iff, Z.eqb_eq in Hc. lia. }
    clear Hc V7 V29.
    paj_run_tok_x RUNR HS HJ SHOK EBspan.
    { ev_awr. }
    ev_meq HF Em2. clear HF HFr HG0.
    ev_V HS E29 V29. ev_V HS E32 V32. ev_V HS E33 V33.
    assert (Hu16 : ev_u16 cx m = lo + 256 * hi) by reflexivity.
    psrr_branch_tok RUNR BR HS SHOK EBspan.
    + (* s5 < s4: len = the u16 *)
      rewrite branch_ltu_U, (ev_u16_U _ lo hi V32 V33 Rlo Rhi), (U_atom_off _ 29 _ (-2) V29) in Hc by lia.
      apply Z.ltb_lt in Hc.
      clear V29 V32 V33.
      paj_run_to_tok_x RUNTOR HS HJ SHOK EBspan AF_ev_call_strnlen.
      { ev_awr. }
      ev_meq HF Em3.
      ev_V HS E28 V28. ev_V HS E29 V29. ev_V HS E32 V32. ev_V HS E33 V33.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (ev1_extra lo hi)) Ev)
          by (split; [intros q0 Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q0 Hq) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ EV_KEPT HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      ev_prreg_raw HS (10%bv : bv 5) Q10. ev_prreg_raw HS (11%bv : bv 5) Q11. ev_prreg_raw HS (20%bv : bv 5) Q20.
      ev_prreg_raw HS (21%bv : bv 5) Q21. ev_prreg_raw HS (22%bv : bv 5) Q22.
      pmkst HS. rewrite Em3 in *. rewrite Em2 in *. rewrite Em1 in *.
      apply SRr_ret.
      lazymatch goal with |- ev_P1_xR _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} =>
        change (ev_P1_xR cx t W (cfg_at segs (fr_B0 + AF_ev_call_strnlen) r mm d)) end.
      assert (Hpg : ev_parg cx m = c_p cx + lm_k m + 1 + 2) by (unfold ev_parg, ev_cons2; lia).
      assert (Hln : ev_len cx m = lo + 256 * hi)
        by (unfold ev_len; rewrite (proj2 (Z.leb_le 2 _) Hr), Hu16; cbv beta iota; lia).
      assert (Hk1 : c_n cx - ev_k1 cx m = c_n cx - lm_k m - 1 + -2) by (unfold ev_k1, ev_cons2; lia).
      apply (ev_P1_of_xR cx t W regsD regs _ mem _ own ly3 S3 k m fpos HJ Hown HAF HFL HAM HAI HROMc HSEP HLS HNP HRI KR Hkept
        (conj C2 (conj C8 (conj C9 (conj C18 (conj C19 (conj C20 (conj C23 (conj C24 (conj C25 (conj C26 (conj C3 C4)))))))))))
        Hr27 Ht Hk HO Hoe).
      * rewrite Q10, Hpg. apply ev_sv_of_U; [apply (U_atom_off _ 28 _ 2 V28) | ]; lia.
      * rewrite Q11, Hln. apply ev_sv_of_U; [|lia].
        rewrite U_SAlu, (ev_u16_U _ lo hi V32 V33 Rlo Rhi), U_lit by lia.
        cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
      * rewrite Q22, Hpg. apply ev_sv_of_U; [apply (U_atom_off _ 28 _ 2 V28) | ]; lia.
      * rewrite Q20, Hk1. apply ev_sv_of_U; [apply (U_atom_off _ 29 _ (-2) V29) | ]; lia.
      * rewrite Q21, Hln. apply ev_sv_of_U; [apply (ev_u16_U _ lo hi V32 V33 Rlo Rhi) | lia].
    + (* s5 >= s4: s5 := s4, len = rem - 2 *)
      rewrite branch_ltu_U, (ev_u16_U _ lo hi V32 V33 Rlo Rhi), (U_atom_off _ 29 _ (-2) V29) in Hc by lia.
      apply Z.ltb_ge in Hc.
      clear V29 V32 V33.
      paj_run_to_tok_x RUNTOR HS HJ SHOK EBspan AF_ev_call_strnlen.
      { ev_awr. }
      ev_meq HF Em3.
      ev_V HS E28 V28. ev_V HS E29 V29.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (ev1_extra lo hi)) Ev)
          by (split; [intros q0 Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q0 Hq) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ EV_KEPT HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      ev_prreg_raw HS (10%bv : bv 5) Q10. ev_prreg_raw HS (11%bv : bv 5) Q11. ev_prreg_raw HS (20%bv : bv 5) Q20.
      ev_prreg_raw HS (21%bv : bv 5) Q21. ev_prreg_raw HS (22%bv : bv 5) Q22.
      pmkst HS. rewrite Em3 in *. rewrite Em2 in *. rewrite Em1 in *.
      apply SRr_ret.
      lazymatch goal with |- ev_P1_xR _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} =>
        change (ev_P1_xR cx t W (cfg_at segs (fr_B0 + AF_ev_call_strnlen) r mm d)) end.
      assert (Hpg : ev_parg cx m = c_p cx + lm_k m + 1 + 2) by (unfold ev_parg, ev_cons2; lia).
      assert (Hln : ev_len cx m = c_n cx - lm_k m - 1 + -2)
        by (unfold ev_len; rewrite (proj2 (Z.leb_le 2 _) Hr), Hu16; cbv beta iota; lia).
      assert (Hk1 : c_n cx - ev_k1 cx m = c_n cx - lm_k m - 1 + -2) by (unfold ev_k1, ev_cons2; lia).
      apply (ev_P1_of_xR cx t W regsD regs _ mem _ own ly3 S3 k m fpos HJ Hown HAF HFL HAM HAI HROMc HSEP HLS HNP HRI KR Hkept
        (conj C2 (conj C8 (conj C9 (conj C18 (conj C19 (conj C20 (conj C23 (conj C24 (conj C25 (conj C26 (conj C3 C4)))))))))))
        Hr27 Ht Hk HO Hoe).
      * rewrite Q10, Hpg. apply ev_sv_of_U; [apply (U_atom_off _ 28 _ 2 V28) | ]; lia.
      * rewrite Q11, Hln. apply ev_sv_of_U; [apply (U_atom_off _ 29 _ (-2) V29) | ]; lia.
      * rewrite Q22, Hpg. apply ev_sv_of_U; [apply (U_atom_off _ 28 _ 2 V28) | ]; lia.
      * rewrite Q20, Hk1. apply ev_sv_of_U; [apply (U_atom_off _ 29 _ (-2) V29) | ]; lia.
      * rewrite Q21, Hln. apply ev_sv_of_U; [apply (U_atom_off _ 29 _ (-2) V29) | ]; lia.
Qed.
(* et_afn_pre_at_x over the R journal: its proof, with the journal lemmas' R twins *)
Lemma et_afn_pre_at_xR : forall cx full ly3 S3 fpos k0 (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k0 ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch /\ (spine ch = [] \/ spine ch = [RA_LLVMF]).
Proof.
  intros cx full ly3 S3 fpos k0 W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HRA : raZ (c_regs cx) = RA_LLVMF) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k0 HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0) by (apply et_F_mod16; exact Hal16).
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) (R := R) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k0 HJ0) as HAB.
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
    split; [| right; cbn [spine map fst snd]; unfold raZ in HRA; rewrite HRA; reflexivity].
    eapply (afn_pre_x_atR (R := R) segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k0 regs STK1 (lf_F cx - sp0) _ HJ0);
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
  - exists []. split; [| left; reflexivity].
    eapply (afn_pre_x_atR (R := R) segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k0 regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
(* et_gx_keep_x over the R journal: its proof (the kept-byte clauses are no world clause) *)
Lemma et_gx_keep_xR : forall G STK sp0 FP ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' k a,
  AJ0R G 0 [] STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k ->
  0 <= a < 2 ^ 64 -> ~ inG G a ->
  ((alloc_ceiling <= a /\ ~ (sp0 - STK <= a < sp0)) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G STK sp0 FP ly S W mem md ly' S' W' mem' md' k a (H0 & H1 & (memS & HJ & Hag) & _) Ha HnG Hc.
  rewrite !Z.add_0_r in HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
  transitivity (aview segs (w_H W) memS a).
  2: { apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG. }
  destruct Hc as [(Hh & Hw) | [(p & n & Hin & Hin' & Hr & Hf) | [(Hi & Ho & He & Hs) | (cid & pos & Hin & Hz & Hf)]]].
  - apply F1; lia.
  - replace a with (p + (a - p)) by lia. apply (F2 p n (a - p) Hin Hin'); [lia|].
    replace (p + (a - p)) with a by lia. exact Hf.
  - exact (F3 a Hi Ho He (HPST a Hi) Hs).
  - exact (F4 cid pos a Hin Hz Hf).
Qed.

(* et_cr_gx_x over the R journal: its proof, through et_gx_keep_xR *)
Lemma et_cr_gx_xR : forall cx FF Gs bl G STK FP ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' k pos,
  gx_ok segs B G ->
  AJ0R G 0 [] STK (lf_F cx) FP ly S W mem md [] ly' S' W' mem' md' k ->
  AR0 ly S W mem md -> In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  (forall a, inG Gs a -> inG G_fr a /\ ~ inG G a /\ ~ (as_errno B <= a < as_errno B + 4) /\ fp_spares FP a) ->
  (forall b n, In (b, n) bl -> In (b, n) (ablocks B ly S) /\ In (b, n) (ablocks B ly' S') /\
     (forall a, b <= a < b + req_size n -> ~ inFP FP a)) ->
  (forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) -> ~ inFP FP a) ->
  0 <= STK <= 32000 -> alloc_ceiling + 32000 <= lf_F cx -> spZ (c_regs cx) <= 2 ^ 47 ->
  forall a, et_cr cx FF Gs bl a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros cx FF Gs bl G STK FP ly S W mem md ly' S' W' mem' md' k pos HGx HJ HAR Hfr HFF HGs Hbl HFP HSTK HFlo Hsp a Hc.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds0 ly S W mem md 1 pos HAR Hfr) as (HF0 & HF1 & _).
  replace (fs_frame_bytes 1) with 128 in HF1 by reflexivity. rewrite <- HFF in HF0, HF1.
  assert (HlowG : forall x, inG G x -> 0 <= x < kLowMemEnd) by (intros x Hx; exact (inG_low segs B pa_segs_low G x HGx Hx)).
  destruct Hc as [Hg | [(b & n & Hb & Hr) | [Hf | [Hff | Hsh]]]].
  - destruct (HGs a Hg) as (HGf & HnG & He & Hs). destruct (HG a HGf) as (Hi & Ho & _).
    pose proof (pa_segs_low a Hi) as Hl.
    apply (et_gx_keep_xR G STK (lf_F cx) FP ly S W mem md ly' S' W' mem' md' k a HJ ltac:(lia) HnG).
    right. right. left. repeat split; assumption.
  - destruct (Hbl b n Hb) as (Hin & Hin' & Hnf).
    destruct (al0_blocks ly S W mem md b n HAR Hin) as (_ & H4096 & Hceil & _).
    pose proof (blk_img0 ly S W mem md b n a HAR Hin Hr) as Hni.
    apply (et_gx_keep_xR G STK (lf_F cx) FP ly S W mem md ly' S' W' mem' md' k a HJ ltac:(lia)
      ltac:(intros HGa; exact (Hni (proj1 (HGx a HGa))))).
    right. left. exists b, n. split; [exact Hin|]. split; [exact Hin'|]. split; [exact Hr | exact (Hnf a Hr)].
  - apply (et_gx_keep_xR G STK (lf_F cx) FP ly S W mem md ly' S' W' mem' md' k a HJ ltac:(lia)
      ltac:(intros HGa; pose proof (HlowG a HGa); lia)).
    left. lia.
  - pose proof (frm_img0 ly S W mem md 1 pos a HAR Hfr ltac:(rewrite <- HFF; replace (fs_frame_bytes 1) with 128 by reflexivity; lia)) as Hni.
    apply (et_gx_keep_xR G STK (lf_F cx) FP ly S W mem md ly' S' W' mem' md' k a HJ ltac:(lia)
      ltac:(intros HGa; exact (Hni (proj1 (HGx a HGa))))).
    right. right. right. exists 1, pos. split; [exact Hfr|]. split; [|exact (HFP a (or_introl Hff))].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- HFF. replace (fs_frame_bytes 1) with 128 by reflexivity. lia.
  - pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd. pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hd0.
    apply (et_gx_keep_xR G STK (lf_F cx) FP ly S W mem md ly' S' W' mem' md' k a HJ ltac:(unfold SB in *; lia)
      ltac:(intros HGa; pose proof (HlowG a HGa); unfold SB in *; lia)).
    right. right. right. exists 1, pos. split; [exact Hfr|]. split; [|exact (HFP a (or_intror Hsh))].
    right. unfold in_zr. cbn [fst snd]. rewrite <- HFF. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity.
    unfold shadow_addr, SHADOW_OFF, SB in *. lia.
Qed.
(* ev_tail_x at R: its proof, the calls by SRrG_bind (R_trans) *)
Lemma ev_tail_xR : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ev_P1_xR cx t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t).
Proof.
  intros cx t W c HB (regs & mem & md & -> & HL).
  destruct HL as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  hp0gR HJ.
  destruct HR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Ht & Hk & HO &
    R10 & R11 & R22 & R20 & R21 & Hop7).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (Has : ASTACK = 16384) by reflexivity.
  assert (Hls : LLVMF_STK = 32768) by reflexivity.
  (* ---- the entry's numbers ---- *)
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hn26 : c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf_x in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  (* ---- the cut's AR, the input block and the cursor ---- *)
  pose proof HJ as (_ & _ & (memS & HJi & HAG) & _).
  pose proof (proj1 HJi) as HAR3.
  assert (Hnpos : 0 < c_n cx) by lia.
  assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (destruct HIN as ([(Hn0 & _) | (Hn & Hin)] & _); [lia | exact Hin]).
  destruct (al0_blocks ly3 S3 W mem md _ _ HAR3 Hpin) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _).
  assert (Hreqp : req_size (c_n cx) = c_n cx)
    by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hreqp in Hpceil, Hpapp, Hppres.
  pose proof (ev_cursor cx m Hk) as (CU1 & CU2 & CU3).
  assert (Hparg : ev_parg cx m = c_p cx + ev_k1 cx m) by (unfold ev_parg, ev_k1; lia).
  (* ---- 0x84ac0 `jal strnlen` ---- *)
  destruct (et0_entry W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
  { intros n0 r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_ev_call_strnlen)) with (Z_to_bv 64 (BASE + AF_ev_call_strnlen)).
  paj_run_tok_x RUNG HS HJ SHOK etspan.
  { apply awr_ok_x_nil. }
  pmkst HS.
  ev_meq HF Em1. clear HF HFr HG0.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  rewrite (EE 2%nat 2%bv eq_refl) in Q2. rewrite (EE 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE 4%nat 4%bv eq_refl) in Q4. rewrite (EE 10%nat 10%bv eq_refl) in Q10.
  rewrite (EE 11%nat 11%bv eq_refl) in Q11.
  rewrite Em1 in *.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. lia. }
  (* ---- strnlen(parg, ev_len), the text lifted through the journal ---- *)
  assert (Hpr1 : c_p cx <= ev_parg cx m) by lia.
  assert (Hpr2 : ev_parg cx m + ev_len cx m <= c_p cx + c_n cx) by lia.
  assert (HOFF : forall a, ev_parg cx m <= a < ev_parg cx m + ev_len cx m ->
      ~ (spZ (ms_regs ms) - 2 * ESTACK <= a < spZ (ms_regs ms))) by (rewrite Hsp1; lia).
  assert (HSRC : src_ok segs W (ms_regs ms) mem (ev_parg cx m) (ev_len cx m)).
  { intros a Ha. split.
    - replace a with (c_p cx + (a - c_p cx)) by lia.
      rewrite (ev_aview_in cx ly3 S3 W mem (a - c_p cx) HlenP HIN ltac:(lia)). discriminate.
    - rewrite Hsp1. lia. }
  assert (HAMR : amem_range (ev_parg cx m) (ev_len cx m))
    by (eapply (amem_range_of_block0 ly3 S3 W mem md (c_p cx) (c_n cx));
        [exact HAR3 | exact Hpin | lia | rewrite Hreqp; lia]).
  assert (HRADDR : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ev_parg cx m) (ev_len cx m))
    by (eapply (range_addressable_of_block0 ly3 S3 W mem md (c_p cx) (c_n cx));
        [exact HAR3 | exact Hpin | lia | rewrite Hreqp; lia]).
  assert (HSHV : 0 < ev_len cx m -> shadow_hull_vis (aview segs (w_H W) mem) (ev_parg cx m) (ev_len cx m))
    by (intros Hpos; eapply (shadow_hull_vis_of_block0 ly3 S3 W mem md (c_p cx) (c_n cx));
        [exact HAR3 | exact Hpin | lia | rewrite Hreqp; lia | exact Hpos]).
  eapply (SRrG_bind segs R R_trans).
  { eapply (aj_gx_entry_at0R G_fr 0 [] (2 * ESTACK) (SIGMA WS_strnlen)
      (fun _ => False)
      (fun regs' (_ : word -> option byte) =>
         exists kk, first_byte segs W mem (ev_parg cx m) (ev_len cx m) 0 kk /\ getr regs' 10 = w64 kk)
      W (ms_regs ms) mem LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 _ k
      (lf_F cx - spZ (c_regs cx)) _
      HG eq_refl HJ ltac:(rewrite Hsp1; lia) (et_F_mod16 cx Hal16) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Q3; exact R3) ltac:(rewrite Q4; exact R4) Q1
      (ret_ok_codeptr_v 10200 ltac:(lia) eq_refl)).
    - intros a. right. intros [].
    - intros a [].
    - intros a [].
    - intros HPRE2 HSC2.
      eapply SRr_mono.
      { exact (ASTRNLEN ly3 S3 [] W (ms_regs ms) mem _ (ev_parg cx m) (ev_len cx m) HPRE2
          (proj1 HSC2) (proj2 HSC2)
          ltac:(rewrite Q10; exact R10) ltac:(rewrite Q11; exact R11)
          ltac:(lia) ltac:(lia) ltac:(lia) HSRC HOFF HAMR HRADDR HSHV (et_consts_of_rom W mem HRV)). }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hmat2 & Hfb & Hfr2 & Hpres2).
      split; [reflexivity|]. exists regs2, mem2, md2.
      split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP2|]. split; [exact Hmat2|].
      split; [exact Hfb|].
      split; [intros a Ha _ Hno; exact (Hfr2 a Ha Hno)|].
      exact Hpres2. }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (slen & Hfb & Hslen10) & Hkeep2 & Hpres2).
  (* ---- what the cut carries across the call, and the frame at the return ---- *)
  pose proof (aregs_preserved_of_st_ok segs (w_H W) E _ _ regs [] HS HAE ltac:(vm_compute; reflexivity)) as KPS.
  cbn [ms_regs] in KPS.
  assert (HPR2 : aregs_preserved regs regs2)
    by (apply (aregs_preserved_trans regs (ms_regs ms) regs2); [exact KPS | exact HP2]).
  assert (P2 : getr regs2 2 = w64 (lf_F cx)) by (rewrite (et_pres regs regs2 2%bv HPR2 ltac:(et_cs)); exact R2).
  assert (P3 : getr regs2 3 = w64 (as_gp B)) by (rewrite (et_pres regs regs2 3%bv HPR2 ltac:(et_cs)); exact R3).
  assert (P4 : getr regs2 4 = w64 (as_tp B)) by (rewrite (et_pres regs regs2 4%bv HPR2 ltac:(et_cs)); exact R4).
  assert (P8 : getr regs2 8 = getr (c_regs cx) 2) by (rewrite (et_pres regs regs2 8%bv HPR2 ltac:(et_cs)); exact R8).
  assert (P26 : getr regs2 26 = w64 SB) by (rewrite (et_pres regs regs2 26%bv HPR2 ltac:(et_cs)); exact R26).
  assert (Hsp2 : spZ regs2 = lf_F cx) by (unfold spZ; rewrite P2; unfold w64; apply unsigned_lit_small; lia).
  assert (Hin1 : In (1, fpos) (frames S3))
    by (pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (HBLK : forall b, In b (et_blks cx m) -> In b (ablocks B ly3 S3)).
  { intros b Hb. destruct HSEP as ((rest & Hperm) & _).
    apply (Permutation_in _ (Permutation_sym Hperm)).
    unfold et_blks in Hb. destruct Hb as [<- | Hb].
    - apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity.
    - apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (KV2 : forall a, et_carry cx m FF a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
  { apply (et_carry_entry_x cx m FF ly3 S3 W mem md mem2 fpos (fun _ => False) (2 * ESTACK) HAR3
      ltac:(intros a Ha _ Hs; apply Hkeep2; [exact Ha | intros [] | lia]) HBLK Hin1 eq_refl
      ltac:(intros a _ []) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & HAG2) & _). rewrite !Z.add_0_r in HJi2.
  pose proof HJi2 as (HAR2j & _ & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _).
  assert (Hin2 : In (1, fpos) (frames S3)) by exact Hin1.
  assert (HFR2 : aframe_at cx true FF W mem2).
  { apply (et_frame_at_x cx FF ly3 S3 W W mem mem2 md2 fpos HFR ltac:(lia) ltac:(lia) ltac:(lia)
      HAR2j Hin2 eq_refl HPRES2).
    - intros a Ha Ha144. apply KV2. right. right. right. left. split; [exact Ha | exact Ha144].
    - intros a Ha. apply KV2. right. right. right. right. left. exact Ha.
    - intros a Ha. apply KV2. right. right. right. right. right. exact Ha. }
  (* ---- 0x84ac4: s7 := slen; a0 := slen + 1; `jal malloc` ---- *)
  pose proof (proj1 Hfb) as Hslenr.
  destruct (ev_evt_of cx ly3 S3 W mem m slen HlenP HIN Hk Hfb) as (HEVT & HELEN).
  assert (Hrelen : re_len (ev_line cx m slen) = slen + 1) by (unfold re_len; lia).
  destruct (et_regs_entry AF_ev_ret_strnlen W regs2 mem2 P26) as [HS2 SHOK2].
  remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (HAE2 : env_agree 32 (Ereg regs2 []) E2)
    by (rewrite HE2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE2 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E2 n0 = getr regs2 r).
  { intros n0 r Hn. rewrite HE2. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  clear HE2.
  change (Z_to_bv 64 (BASE + 10200)) with (Z_to_bv 64 (BASE + AF_ev_ret_strnlen)).
  paj_run_tok_x RUNG HS2 HJ2 SHOK2 etspan.
  { apply awr_ok_x_nil. }
  pmkst HS2.
  ev_meq HF Em2. clear HF HFr HG0.
  prreg HS2 (1%bv : bv 5) N1. prreg HS2 (2%bv : bv 5) N2. prreg HS2 (3%bv : bv 5) N3.
  prreg HS2 (4%bv : bv 5) N4. prreg HS2 (10%bv : bv 5) N10.
  rewrite (EE2 2%nat 2%bv eq_refl) in N2. rewrite (EE2 3%nat 3%bv eq_refl) in N3.
  rewrite (EE2 4%nat 4%bv eq_refl) in N4.
  try rewrite Em2 in *.
  assert (E2_10 : ew E2 10 = Z_to_bv 64 slen) by (rewrite (EE2 10%nat 10%bv eq_refl); exact Hslen10).
  assert (N10' : getr (ms_regs ms0) 10 = w64 (slen + 1)).
  { rewrite N10, E2_10, unsigned_lit_small by lia. reflexivity. }
  assert (Hsp3 : spZ (ms_regs ms0) = lf_F cx)
    by (unfold spZ; rewrite N2, P2; unfold w64; apply unsigned_lit_small; lia).
  prreg HS2 (8%bv : bv 5) N8. rewrite (EE2 8%nat 8%bv eq_refl) in N8.
  pose proof HJ2 as (_ & _ & (memS3 & HJi3 & HAG3) & _). rewrite !Z.add_0_r in HJi3.
  destruct (et_afn_pre_at_xR cx true ly3 S3 fpos k W mem2 _ (ms_regs ms0) ASTACK HB HJ2 HFR2
      Hsp3 ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
      ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
      ltac:(rewrite N3, P3; reflexivity) ltac:(rewrite N4, P4; reflexivity)
      ltac:(rewrite N8, P8; reflexivity) ltac:(lia) ltac:(lia)) as (chM & HPREM & HSPM).
  pose proof HPREM as (_ & _ & _ & _ & _ & _ & _ & HchM & _).
  assert (HCHM : chain_pre ly3 (aview segs (w_H W) mem2) (ms_regs ms0) chM).
  { apply (achain_chain_pre ly3 (aview segs (w_H W) mem2) (spZ (ms_regs ms0)) (s0Z (ms_regs ms0))
      chM (ms_regs ms0) HchM); [rewrite Hsp3; lia | reflexivity |
      unfold raZ; rewrite N1, unsigned_lit_small by lia; lia]. }
  pose proof (LS_event_malloc cx t m ly3 S3 (ev_line cx m slen) HLS HRI HEVT) as (LM1 & LM2 & LM3).
  rewrite Hrelen in LM1, LM2, LM3.
  (* ---- the room round: the cut's NP gives each call's rp_RM (RP_NP), and LS_cnt's peak gives each call's counts ---- *)
  pose proof (ev_msz_x ly3 S3 W mem m HMOD) as HMSZ.
  assert (HCNTpk : cnt_ok_pk RP (fun P => ((if P (re_len (ev_line cx m slen)) then 1 else 0) + 2)%nat)
      (ablocks B ly3 S3))
    by (unfold cnt_ok_pk; exact (LS_cnt cx t m ly3 S3 (ev_line cx m slen) HLS HRI HEVT HMSZ Ht)).
  (* malloc runs at the entry's blocks, with no peak of its own *)
  assert (HCNT3 : cnt_ok RP (ablocks B ly3 S3)).
  { unfold cnt_ok. apply (cnt_ok_pk_mono RP (fun P => ((if P (re_len (ev_line cx m slen)) then 1 else 0) + 2)%nat) (fun _ => 0%nat) (ablocks B ly3 S3) (ablocks B ly3 S3)); [|exact HCNTpk].
    intros P. cbv beta. lia. }
  assert (HRM3 : rp_RM RP S3 (1 + 0)%nat) by (apply RP_NP; exact HNP).
  (* the allocator entry's context: malloc's return site 0x84ad0 over the chain's spine, a row of the K0 table *)
  assert (HCTXM : In (raZ (ms_regs ms0) :: spine chM) CTX_AMALLOC).
  { assert (Hra : raZ (ms_regs ms0) = BASE + AF_ev_ret_malloc)
      by (unfold raZ; rewrite N1, unsigned_lit_small by lia; reflexivity).
    rewrite Hra. destruct HSPM as [-> | ->]; et_in_tab. }
  (* the room round's rules also ask that the call frame is above the layout's bottom: the entry journal's astk_ok
     (LLVMF_STK at the entry sp) and the call's ASTACK - o <= STK *)
  assert (HLYB3 : ly_bot ly3 + ACALL_PREFIX < spZ (ms_regs ms0)).
  { pose proof HJi3 as (_ & HLE3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK3 & _).
    unfold astk_ok in HSTK3. unfold layout_le in HLE3. unfold ly_bot in *.
    rewrite Hsp3. unfold LLVMF_STK, ASTACK, kStackSpan in *. lia. }
  (* the R rule's call-boundary premise RO at the call memory, from the call state's ARx *)
  pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi3)) as HRO3.
  eapply (SRrG_bind segs R R_trans).
  { rewrite (pal_malloc B TL).
    eapply (AMALLOC_R W (ms_regs ms0) mem2 LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS3 (c_md cx) [(1, fpos)] ly3 S3 [] _ k (slen + 1)
      (lf_F cx - spZ (c_regs cx)) _ chM 0%nat HJi3 N10' ltac:(lia) LM2 HCNT3
      ltac:(rewrite Hsp3; lia) (et_F_mod16 cx Hal16) ltac:(lia) ltac:(lia) HLYB3
      ltac:(rewrite N3, P3; reflexivity) ltac:(rewrite N4, P4; reflexivity) N1
      (ret_ok_codeptr_v 10212 ltac:(lia) eq_refl) HCHM HRO3 HCTXM HRM3 LM3). }
  cbv beta. intros W3 c3 Hwle3
    (ly4 & S4 & Hp4 & regs3 & mem3 & md3 & q & -> & HJi4 & HPq & Hq10 & Hfrq & Hq4096 & Hblq & Hkeptq & Hmleq & HRM4
     & Herrq & Hpresq).
  hp0a (proj1 HJi4).
  (* ---- after malloc: the new block q, the journal repacked, the cut's bytes still kept ---- *)
  assert (HJ3 : AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 W3 mem3 md3 (k + 1)).
  { apply (ajournal_gx_pack0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 W3 mem3 md3 (k + 1) memS3);
      [lia | lia | rewrite !Z.add_0_r; exact HJi4 | exact HAG3 | apply out_none]. }
  pose proof (proj1 HJi4) as HAR4.
  assert (Hreqq : req_size (slen + 1) = slen + 1)
    by (unfold req_size; destruct (Z.eqb_spec (slen + 1) 0); lia).
  assert (Hqin : In (q, slen + 1) (ablocks B ly4 S4))
    by (rewrite Hblq; apply in_or_app; right; left; reflexivity).
  destruct (al0_blocks ly4 S4 W3 mem3 md3 _ _ HAR4 Hqin) as (Hq16 & _ & Hqceil & Hqapp & Hqpres & _).
  rewrite Hreqq in Hqceil, Hqapp, Hqpres.
  assert (Hold4 : forall b n0, In (b, n0) (ablocks B ly3 S3) -> In (b, n0) (ablocks B ly4 S4))
    by (intros b n0 Hb; rewrite Hblq; apply in_or_app; left; exact Hb).
  assert (HQB : forall b n0, In (b, n0) (ablocks B ly3 S3) -> b + req_size n0 <= q \/ q + (slen + 1) <= b).
  { intros b n0 Hb. rewrite <- Hreqq.
    exact (et_new_disj_x ly4 S4 W3 mem3 md3 ly3 S3 q (slen + 1) b n0 HAR4 Hblq Hb). }
  assert (HQF : forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) ->
      ~ (q <= a < q + (slen + 1))).
  { intros a Ha Hq.
    assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrq; exact Hin1).
    pose proof (sep_block_frame0 ly4 S4 W3 mem3 md3 q (slen + 1) 1 fpos HAR4 Hqin Hin4) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqq in Hd.
    replace (fs_frame_bytes 1) with 128 in Hd by reflexivity.
    assert (HFFeq : frame_addr ly4 1 fpos = FF).
    { pose proof HJi4 as (_ & Hly4 & _). pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _).
      pose proof HJi as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
      unfold FF, frame_addr. rewrite EF4, <- EF3. reflexivity. }
    rewrite HFFeq in Hd.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    destruct (frames_bounds0 ly4 S4 W3 mem3 md3 1 fpos HAR4 Hin4) as (HFa & HFb & _).
    rewrite HFFeq in HFa, HFb. replace (fs_frame_bytes 1) with 128 in HFb by reflexivity.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hdv.
    pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hdv0.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hqapp.
    unfold SB in *. lia. }
  assert (KV3 : forall a, et_carry cx m FF a -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mem a).
  { intros a Hc. rewrite <- (KV2 a Hc).
    exact (et_carry_acall_x cx m FF ly3 S3 W W3 mem2 mem3 _ fpos ly4 S4 W3 mem3 md3 q (slen + 1) _ _
      (proj1 HJi3) HAR4 Hkeptq Herrq HBLK Hin1 eq_refl Hqin
      ltac:(intros b n1 Hb; rewrite Hreqq; exact (HQB b n1 (HBLK (b, n1) Hb)))
      ltac:(intros x Hx; rewrite Hreqq; exact (HQF x Hx))
      ltac:(lia) ltac:(unfold ASTACK; lia) ltac:(lia) ltac:(lia) a Hc). }
  pose proof HJi4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES4 & _).
  assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrq; exact Hin1).
  assert (HFFeq4 : frame_addr ly4 1 fpos = FF).
  { pose proof HJi4 as (_ & Hly4 & _). pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _).
    pose proof HJi as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
    unfold FF, frame_addr. rewrite EF4, <- EF3. reflexivity. }
  assert (HFR3 : aframe_at cx true FF W3 mem3).
  { apply (et_frame_at_x cx FF ly4 S4 W W3 mem mem3 md3 fpos HFR ltac:(lia) ltac:(lia) ltac:(lia)
      HAR4 Hin4 ltac:(symmetry; exact HFFeq4) HPRES4).
    - intros a Ha Ha144. apply KV3. right. right. right. left. split; [exact Ha | exact Ha144].
    - intros a Ha. apply KV3. right. right. right. right. left. exact Ha.
    - intros a Ha. apply KV3. right. right. right. right. right. exact Ha. }
  (* ---- the registers through the malloc call ---- *)
  pose proof (regs_kept_of_st_ok segs E2 _ _ regs2 [] EV_KEEP2 HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HS2 (23%bv : bv 5) N23. rewrite E2_10 in N23.
  assert (RG3 : forall r, In r EV_KEEP2 -> getr regs3 r = getr regs r).
  { intros r Hr. rewrite (et_pres (ms_regs ms0) regs3 r HPq (EV_KEEP2_cs r Hr)), (KR2 r Hr).
    exact (et_pres regs regs2 r HPR2 (EV_KEEP2_cs r Hr)). }
  assert (R3_23 : getr regs3 23 = w64 slen)
    by (rewrite (et_pres (ms_regs ms0) regs3 23%bv HPq ltac:(et_cs)), N23; reflexivity).
  assert (R3_26 : getr regs3 26 = w64 SB) by (rewrite (RG3 26%bv ltac:(cbv; tauto)); exact R26).
  assert (R3_2 : getr regs3 2 = w64 (lf_F cx)) by (rewrite (RG3 2%bv ltac:(cbv; tauto)); exact R2).
  assert (R3_22 : getr regs3 22 = w64 (ev_parg cx m)) by (rewrite (RG3 22%bv ltac:(cbv; tauto)); exact R22).
  (* ---- 0x84ad0: `beqz a0` (refuted by 4096 <= q); s9 := q; a1 := parg; a2 := slen; `jal __asan_memcpy` ---- *)
  destruct (et_regs_entry AF_ev_ret_malloc W3 regs3 mem3 R3_26) as [HS3 SHOK3].
  remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
  assert (HAE3 : env_agree 32 (Ereg regs3 []) E3)
    by (rewrite HE3; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE3 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E3 n0 = getr regs3 r).
  { intros n0 r Hn. rewrite HE3. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  clear HE3.
  assert (E3_10 : ew E3 10 = Z_to_bv 64 q) by (rewrite (EE3 10%nat 10%bv eq_refl); exact Hq10).
  change (Z_to_bv 64 (BASE + 10212)) with (Z_to_bv 64 (BASE + AF_ev_ret_malloc)).
  psrr_branch_tok RUNG BRG HS3 SHOK3 etspan.
  { exfalso. rewrite branch_eq_U, (U_atom E3 10 q E3_10), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. lia. }
  paj_run_tok_x RUNG HS3 HJ3 SHOK3 etspan.
  { apply awr_ok_x_nil. }
  pmkst HS3.
  ev_meq HF Em3. clear HF HFr HG0.
  try rewrite Em3 in *.
  prreg HS3 (1%bv : bv 5) M1. prreg HS3 (2%bv : bv 5) M2. prreg HS3 (3%bv : bv 5) M3.
  prreg HS3 (4%bv : bv 5) M4. prreg HS3 (8%bv : bv 5) M8. prreg HS3 (10%bv : bv 5) M10.
  prreg HS3 (11%bv : bv 5) M11. prreg HS3 (12%bv : bv 5) M12. prreg HS3 (25%bv : bv 5) M25.
  rewrite (EE3 2%nat 2%bv eq_refl) in M2. rewrite (EE3 3%nat 3%bv eq_refl) in M3.
  rewrite (EE3 4%nat 4%bv eq_refl) in M4. rewrite (EE3 8%nat 8%bv eq_refl) in M8.
  rewrite (EE3 10%nat 10%bv eq_refl) in M10. rewrite (EE3 22%nat 22%bv eq_refl) in M11.
  rewrite (EE3 23%nat 23%bv eq_refl) in M12. rewrite (EE3 10%nat 10%bv eq_refl) in M25.
  pose proof (regs_kept_of_st_ok segs E3 _ _ regs3 [] EV_KEEP2 HS3 HAE3 ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  assert (Hsp4 : spZ (ms_regs ms1) = lf_F cx)
    by (unfold spZ; rewrite M2, R3_2; unfold w64; apply unsigned_lit_small; lia).
  (* ---- __asan_memcpy(q, parg, slen): the donor's intrinsic form, lifted through the journal ---- *)
  assert (M10' : getr (ms_regs ms1) 10 = w64 q) by (rewrite M10; exact Hq10).
  assert (M11' : getr (ms_regs ms1) 11 = w64 (ev_parg cx m)) by (rewrite M11; exact R3_22).
  assert (M12' : getr (ms_regs ms1) 12 = w64 slen) by (rewrite M12; exact R3_23).
  assert (Hpin4 : In (c_p cx, c_n cx) (ablocks B ly4 S4)) by (apply Hold4; exact Hpin).
  assert (HQP : c_p cx + c_n cx <= q \/ q + (slen + 1) <= c_p cx).
  { destruct (HQB (c_p cx) (c_n cx) Hpin) as [Hd | Hd]; rewrite ?Hreqp in Hd; lia. }
  assert (KVin : forall a, c_p cx <= a < c_p cx + c_n cx -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KV3. right. right. left. exists (c_p cx), (c_n cx).
    split; [left; reflexivity | rewrite Hreqp; exact Ha]. }
  assert (HSRC4 : src_ok segs W3 (ms_regs ms1) mem3 (ev_parg cx m) slen).
  { intros a Ha. split.
    - rewrite (KVin a ltac:(lia)). replace a with (c_p cx + (a - c_p cx)) by lia.
      rewrite (ev_aview_in cx ly3 S3 W mem (a - c_p cx) HlenP HIN ltac:(lia)). discriminate.
    - rewrite Hsp4. lia. }
  assert (HDEST : dest_ok segs B ly4 S4 W3 (ms_regs ms1) mem3 q slen).
  { intros a Ha. destruct (Hqpres a ltac:(lia)) as [Hp Hno].
    split; [exact (apresent_writable segs _ _ _ Hp)|]. split; [exact Hno|]. rewrite Hsp4. lia. }
  assert (HAMRq : amem_range q slen)
    by (eapply (amem_range_of_block0 ly4 S4 W3 mem3 md3 q (slen + 1));
        [exact HAR4 | exact Hqin | lia | rewrite Hreqq; lia]).
  assert (HRAq : range_addressable (aview segs (w_H W3) mem3) SHADOW_OFF q slen)
    by (eapply (range_addressable_of_block0 ly4 S4 W3 mem3 md3 q (slen + 1));
        [exact HAR4 | exact Hqin | lia | rewrite Hreqq; lia]).
  assert (HSHVq : 0 < slen -> shadow_hull_vis (aview segs (w_H W3) mem3) q slen)
    by (intros Hpos; eapply (shadow_hull_vis_of_block0 ly4 S4 W3 mem3 md3 q (slen + 1));
        [exact HAR4 | exact Hqin | lia | rewrite Hreqq; lia | exact Hpos]).
  assert (HCPY : 0 <= ev_parg cx m /\ ev_parg cx m + slen <= 2 ^ 63 /\
      src_ok segs W3 (ms_regs ms1) mem3 (ev_parg cx m) slen /\
      (q + slen <= ev_parg cx m \/ ev_parg cx m + slen <= q) /\ amem_range (ev_parg cx m) slen /\
      range_addressable (aview segs (w_H W3) mem3) SHADOW_OFF (ev_parg cx m) slen /\
      (0 < slen -> shadow_hull_vis (aview segs (w_H W3) mem3) (ev_parg cx m) slen)).
  { split; [lia|]. split; [lia|]. split; [exact HSRC4|]. split; [lia|].
    split; [eapply (amem_range_of_block0 ly4 S4 W3 mem3 md3 (c_p cx) (c_n cx));
            [exact HAR4 | exact Hpin4 | lia | rewrite Hreqp; lia]|].
    split; [eapply (range_addressable_of_block0 ly4 S4 W3 mem3 md3 (c_p cx) (c_n cx));
            [exact HAR4 | exact Hpin4 | lia | rewrite Hreqp; lia]|].
    intros Hpos; eapply (shadow_hull_vis_of_block0 ly4 S4 W3 mem3 md3 (c_p cx) (c_n cx));
      [exact HAR4 | exact Hpin4 | lia | rewrite Hreqp; lia | exact Hpos]. }
  eapply (SRrG_bind segs R R_trans).
  { eapply (aj_gx_entry_at0R G_fr 0 [] ESTACK (SIGMA WS_asan_memcpy)
      (fun a => q <= a < q + slen)
      (fun (regs' : bvmap 5 word) mem' => forall i, 0 <= i < slen ->
         aview segs (w_H W3) mem' (q + i) = aview segs (w_H W3) mem3 (ev_parg cx m + i))
      W3 (ms_regs ms1) mem3 LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 _ (k + 1)
      (lf_F cx - spZ (c_regs cx)) _
      HG eq_refl HJ3 ltac:(rewrite Hsp4; lia) (et_F_mod16 cx Hal16) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite M3, (RG3 3%bv ltac:(cbv; tauto)); exact R3)
      ltac:(rewrite M4, (RG3 4%bv ltac:(cbv; tauto)); exact R4) M1
      (ret_ok_codeptr_v 10232 ltac:(lia) eq_refl)).
    - intros a. lia.
    - intros a Ha HGa. exfalso.
      apply (blk_img0 ly4 S4 W3 mem3 md3 q (slen + 1) a HAR4 Hqin ltac:(rewrite Hreqq; lia)).
      exact (proj1 (HG a HGa)).
    - intros a Ha _. split; [|lia]. replace a with (q + (a - q)) by lia.
      eapply (awr_new_block_any0R LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
        (c_ly cx) (c_S cx) (c_W cx) memS3 (c_md cx) [(1, fpos)] ly3 S3 W mem2 _ k
        ly4 S4 W3 mem3 md3 q (slen + 1) (ablocks B ly4 S4) (a - q) ly4 [(1, fpos)] HJi3 HAR4 Hblq);
        [lia | exact Hqin | rewrite Hreqq; lia].
    - intros HPRE4 HSC4.
      eapply SRr_mono.
      { exact (AMEMCPY ly4 S4 [] W3 (ms_regs ms1) mem3 _ q (ev_parg cx m) slen HPRE4 M10' M11' M12'
          ltac:(lia) ltac:(lia) ltac:(lia) HDEST HAMRq
          (fun a Ha HK => blk_img0 ly4 S4 W3 mem3 md3 q (slen + 1) a HAR4 Hqin ltac:(rewrite Hreqq; lia) (proj1 HK))
          HRAq HSHVq HCPY). }
      cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR5 & HP5 & Hmat5 & _ & Hcpy & Hfr5 & Hpres5).
      split; [reflexivity|]. exists regs4, mem4, md4.
      split; [reflexivity|]. split; [exact HAR5|]. split; [exact HP5|]. split; [exact Hmat5|].
      split; [exact Hcpy|].
      split; [intros a Ha Hw Hs; exact (Hfr5 a Ha Hw Hs)|].
      exact Hpres5. }
  cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hcpy & Hkeep4 & Hpres4).
  (* ---- 0x84ae4: the partial-granule shadow check of q + slen, in.n := s4 - s5, s6 += s5, the NUL ---- *)
  prreg HS3 (9%bv : bv 5) M9. prreg HS3 (23%bv : bv 5) M23. prreg HS3 (26%bv : bv 5) M26.
  rewrite (EE3 9%nat 9%bv eq_refl) in M9. rewrite (EE3 23%nat 23%bv eq_refl) in M23.
  rewrite (EE3 26%nat 26%bv eq_refl) in M26.
  assert (R4_9 : getr regs4 9 = w64 (lf_F cx)).
  { rewrite (et_pres (ms_regs ms1) regs4 9%bv HP4 ltac:(et_cs)), M9, (RG3 9%bv ltac:(cbv; tauto)). exact R9. }
  assert (R4_23 : getr regs4 23 = w64 slen).
  { rewrite (et_pres (ms_regs ms1) regs4 23%bv HP4 ltac:(et_cs)), M23. exact R3_23. }
  assert (R4_25 : getr regs4 25 = w64 q).
  { rewrite (et_pres (ms_regs ms1) regs4 25%bv HP4 ltac:(et_cs)), M25. exact Hq10. }
  assert (R4_26 : getr regs4 26 = w64 SB).
  { rewrite (et_pres (ms_regs ms1) regs4 26%bv HP4 ltac:(et_cs)), M26, (RG3 26%bv ltac:(cbv; tauto)). exact R26. }
  pose proof HJ4 as (_ & _ & (memS5 & HJi5 & HAG5) & _). rewrite !Z.add_0_r in HJi5.
  pose proof HJi5 as (HAR6 & _ & _ & _ & _ & Hfrs5 & _ & _ & _ & _ & _ & _ & _ & HPRES5 & _).
  assert (HWF4 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W3 mem4) a).
  { intros a Ha. apply (apresent_writable segs). apply HPRES5. unfold LLVMF_STK in *. lia. }
  destruct (et5_entry_x W3 regs4 mem4 ly4 S4 md4 (lf_F cx) q slen HAR6 R4_9 R4_23 R4_25 R4_26
      ltac:(lia) ltac:(lia) ltac:(lia) Hqin HWF4) as [HS4 SHOK4].
  remember (Eimg (Ereg regs4 (et5_extra (q + slen)))) as E4 eqn:HEx.
  assert (HEIx : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
  assert (HAEx : env_agree 32 (Ereg regs4 (et5_extra (q + slen))) E4)
    by (rewrite HEx; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEx : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E4 n0 = getr regs4 r).
  { intros n0 r Hn. rewrite HEx. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  assert (Ex32 : ew E4 32 = Z_to_bv 64 (q + slen))
    by (rewrite HEx; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
  clear HEx.
  assert (Ux32 : bv_unsigned (ew E4 32) = q + slen) by (rewrite Ex32; apply unsigned_lit_small; lia).
  assert (Ux9 : bv_unsigned (ew E4 9) = lf_F cx)
    by (rewrite (EEx 9%nat 9%bv eq_refl), R4_9; unfold w64; apply unsigned_lit_small; lia).
  change (Z_to_bv 64 (BASE + 10232)) with (Z_to_bv 64 (BASE + AF_ev_ret_memcpy)).
  paj_run_to_tok_x RUNTOG HS4 HJ4 SHOK4 etspan AF_fr_relay_event.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ux32 in Ha.
      left. split; [|lia]. replace a with (q + (a - q)) by lia.
      eapply (awr_new_block_any0R LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
        (c_ly cx) (c_S cx) (c_W cx) memS3 (c_md cx) [(1, fpos)] ly3 S3 W mem2 _ k
        ly4 S4 W3 mem3 md3 q (slen + 1) (ablocks B ly4 S4) (a - q) ly4 [(1, fpos)] HJi3 HAR4 Hblq);
        [lia | exact Hqin | rewrite Hreqq; lia]. }
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ux9 in Ha.
      left. split; [left; unfold LLVMF_STK; lia | lia]. }
    apply awr_ok_x_nil. }
  pmkst HS4.
  (* ---- at relay_event's entry: the cut's bytes across the two stores, the frame, the registers ---- *)
  assert (HBLK4 : forall b, In b (et_blks cx m) -> In b (ablocks B ly4 S4))
    by (intros [b n1] Hb; apply Hold4; exact (HBLK (b, n1) Hb)).
  assert (HOFFQ : forall a, et_carry cx m FF a -> ~ (q <= a < q + (slen + 1))).
  { intros a Hcr.
    pose proof (et_carry_off_block_x cx m FF ly4 S4 W3 mem3 md3 fpos ly4 S4 W3 mem3 md3 q (slen + 1) a
      HAR4 HAR4 HBLK4 Hin4 ltac:(symmetry; exact HFFeq4) Hqin
      ltac:(intros b n1 Hb; rewrite Hreqq; exact (HQB b n1 (HBLK (b, n1) Hb)))
      ltac:(intros x Hx; rewrite Hreqq; exact (HQF x Hx)) ltac:(lia) Hcr) as Hoff.
    rewrite Hreqq in Hoff. exact Hoff. }
  assert (HOFFS : forall a, et_carry cx m FF a -> ~ (lf_F cx + 144 <= a < lf_F cx + 152))
    by (intros a Hcr; exact (et_carry_off_slot_x cx m FF ly4 S4 W3 mem3 md3 fpos a HAR4 HBLK4 Hin4
          ltac:(symmetry; exact HFFeq4) ltac:(lia) Hcr)).
  assert (KV5 : forall a, et_carry cx m FF a -> aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W) mem a).
  { intros a Hcr. rewrite <- (KV3 a Hcr).
    assert (Hb64 : 0 <= a < 2 ^ 64).
    { pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
      destruct (et_carry_low_x cx m FF ly4 S4 W3 mem3 md3 fpos a HAR4 HBLK4 Hin4
        ltac:(symmetry; exact HFFeq4) Hcr) as [Hl | (Hl & _)]; lia. }
    assert (Hlow4 : 0 <= a < alloc_ceiling \/ lf_F cx <= a < spZ (c_regs cx)).
    { destruct (et_carry_low_x cx m FF ly4 S4 W3 mem3 md3 fpos a HAR4 HBLK4 Hin4
        ltac:(symmetry; exact HFFeq4) Hcr) as [Hl | (Hl & _)]; [left; exact Hl | right; exact Hl]. }
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    rewrite <- (Hkeep4 a Hb64 ltac:(pose proof (HOFFQ a Hcr) as Hx; lia) ltac:(lia)).
    apply (aview_kept_out E4 _ (w_H W3) mem4 (ms_mem ms2) HFr a Hb64).
    apply et_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?Ux32, ?Ux9.
    - pose proof (HOFFQ a Hcr) as Hx. lia.
    - pose proof (HOFFS a Hcr) as Hx. lia. }
  pose proof HJ4 as (_ & _ & (memS6 & HJi6 & HAG6) & _). rewrite !Z.add_0_r in HJi6.
  pose proof HJi6 as (HAR7 & _ & _ & _ & _ & Hfrs6 & _ & _ & _ & _ & _ & _ & _ & HPRES6 & _).
  assert (HFR4 : aframe_at cx true FF W3 (ms_mem ms2)).
  { apply (et_frame_at_x cx FF ly4 S4 W W3 mem (ms_mem ms2) _ fpos HFR ltac:(lia) ltac:(lia) ltac:(lia)
      HAR7 Hin4 ltac:(symmetry; exact HFFeq4) HPRES6).
    - intros a Ha Ha144. apply KV5. right. right. right. left. split; [exact Ha | exact Ha144].
    - intros a Ha. apply KV5. right. right. right. right. left. exact Ha.
    - intros a Ha. apply KV5. right. right. right. right. right. exact Ha. }
  assert (HFL4 : sv8 W3 (ms_mem ms2) (FF + 120) (flag_addr ly3 1 fpos)).
  { apply (et_flag_at_x FF ly4 S4 W W3 mem (ms_mem ms2) _ fpos _ HFL HAR7 Hin4 ltac:(symmetry; exact HFFeq4)).
    intros a Ha. apply KV5. right. right. right. right. left. exact Ha. }
  assert (KB5 : forall a, et_carry cx m FF a -> abyte_kept W mem W3 (ms_mem ms2) a)
    by (apply (et_carry_kept_x cx m FF ly4 S4 W W3 mem (ms_mem ms2) _ fpos HAR7 HBLK4 Hin4
          ltac:(symmetry; exact HFFeq4) HPRES6 ltac:(lia) ltac:(lia) KV5)).
  (* ---- 0x84b0c `jal relay_event`: the registers, the line q (its bytes and NUL), the stream and the lock carried
     to relay_event's entry, then W5's re_spec ---- *)
  prreg HS4 (1%bv : bv 5) T1. prreg HS4 (2%bv : bv 5) T2. prreg HS4 (3%bv : bv 5) T3. prreg HS4 (4%bv : bv 5) T4.
  prreg HS4 (8%bv : bv 5) T8. prreg HS4 (10%bv : bv 5) T10. prreg HS4 (22%bv : bv 5) T22. prreg HS4 (23%bv : bv 5) T23.
  prreg HS4 (9%bv : bv 5) T9. prreg HS4 (18%bv : bv 5) T18. prreg HS4 (19%bv : bv 5) T19. prreg HS4 (20%bv : bv 5) T20.
  prreg HS4 (21%bv : bv 5) T21. prreg HS4 (24%bv : bv 5) T24. prreg HS4 (25%bv : bv 5) T25. prreg HS4 (26%bv : bv 5) T26.
  prreg HS4 (27%bv : bv 5) T27.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS4 eq_refl) as RNUL. cbn [ms_mem restrict] in RNUL.
  assert (Ux32' : bv_unsigned (ew (ewset (ewset E4 512 w) 513 w0) 32) = q + slen)
    by (rewrite !ew_ewset_other by lia; exact Ux32).
  assert (VNUL : val_mem segs (mrestrict (w_H W3) (ms_mem ms2)) (q + slen + 0) (N.to_nat 1) 0).
  { eapply (field_of_region _ _ 32 (q + slen));
      [exact RNUL | exact Ux32' | cbn [In]; left; reflexivity | reflexivity | zside | zside]. }
  rewrite Z.add_0_r in VNUL.
  assert (RG4 : forall r, In r EV_KEEP2 -> getr regs4 r = getr regs r).
  { intros r Hr. rewrite (et_pres (ms_regs ms1) regs4 r HP4 (EV_KEEP2_cs r Hr)), (KR3 r Hr). exact (RG3 r Hr). }
  assert (V2 : getr (ms_regs ms2) 2 = w64 (lf_F cx))
    by (rewrite T2, (EEx 2%nat 2%bv eq_refl), (RG4 2%bv ltac:(cbv; tauto)); exact R2).
  assert (V3 : getr (ms_regs ms2) 3 = w64 (as_gp B))
    by (rewrite T3, (EEx 3%nat 3%bv eq_refl), (RG4 3%bv ltac:(cbv; tauto)); exact R3).
  assert (V4 : getr (ms_regs ms2) 4 = w64 (as_tp B))
    by (rewrite T4, (EEx 4%nat 4%bv eq_refl), (RG4 4%bv ltac:(cbv; tauto)); exact R4).
  assert (V8 : getr (ms_regs ms2) 8 = getr (c_regs cx) 2)
    by (rewrite T8, (EEx 8%nat 8%bv eq_refl), (RG4 8%bv ltac:(cbv; tauto)); exact R8).
  assert (V10 : getr (ms_regs ms2) 10 = w64 q) by (rewrite T10, (EEx 25%nat 25%bv eq_refl); exact R4_25).
  assert (Hsp5 : spZ (ms_regs ms2) = lf_F cx) by (unfold spZ; rewrite V2; unfold w64; apply unsigned_lit_small; lia).
  (* fr_lib_pre_cf_x: LIBROOM and NP after fr_live_pre, so rom_view is the 13th conjunct *)
  pose proof HPRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROM0 & _).
  assert (ROM5 : rom_view segs W3 (ms_mem ms2))
    by (eapply ajournal_gx_rom_view0R; first [exact HJ4 | exact ET_ROM_OUT | exact HROM0 | exact LAWS | exact pa_segs_low]).
  assert (HRES : RE_STK = 16544) by reflexivity.
  assert (HFR4' : aframe_at cx true (frame_addr ly4 1 fpos) W3 (ms_mem ms2)) by (rewrite HFFeq4; exact HFR4).
  destruct (et_afn_pre_at_xR cx true ly4 S4 fpos (k + 1) W3 (ms_mem ms2) _ (ms_regs ms2) RE_STK HB HJ4 HFR4' Hsp5
      ltac:(rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity])
      ltac:(unfold raZ; rewrite T1, unsigned_lit_small by lia; lia)
      V3 V4 V8 ltac:(lia) ltac:(lia)) as (chR & HPRER & _).
  assert (KS5 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + slen <= a < q + slen + 1) -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem4 a).
  { intros a Ha H1 H2. apply (aview_kept_out E4 _ (w_H W3) mem4 (ms_mem ms2) HFr a Ha).
    apply et_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?Ux32, ?Ux9; lia. }
  assert (HLn : length (ev_line cx m slen) = Z.to_nat slen) by lia.
  assert (HOBQ : ob_at W3 (ms_mem ms2) q (ev_line cx m slen ++ [Z_to_bv 8 0])).
  { intros i Hi. rewrite length_app, HLn in Hi. cbn [length] in Hi.
    destruct (Z.eq_dec i slen) as [-> | Hne].
    - rewrite app_nth2 by lia. rewrite HLn, Nat.sub_diag. cbn [nth].
      specialize (VNUL 0%nat ltac:(lia)). cbn [Z.of_nat] in VNUL. rewrite Z.add_0_r in VNUL.
      unfold aview. rewrite VNUL. reflexivity.
    - assert (Hi' : 0 <= i < slen) by lia.
      rewrite app_nth1 by lia.
      rewrite (ev_line_nth cx m slen i Hk Hi').
      rewrite (KS5 (q + i) ltac:(lia) ltac:(lia) ltac:(lia)), (Hcpy i Hi'), (KVin (ev_parg cx m + i) ltac:(lia)).
      replace (ev_parg cx m + i) with (c_p cx + (ev_k1 cx m + i)) by lia.
      rewrite (ev_aview_in cx ly3 S3 W mem (ev_k1 cx m + i) HlenP HIN ltac:(lia)). reflexivity. }
  pose proof HMOD as (_ & _ & _ & HAO & HGN & HLK & _).
  assert (HAO5 : aout_at B fr_RG ly4 S4 W3 (ms_mem ms2) (lm_c m) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
      (lm_cap m) (lm_out m)).
  { apply (aout_at_kept B fr_RG ly3 S3 W mem ly4 S4 W3 (ms_mem ms2) _ _ _ _ _ _ HAO).
    - intros r Hr a Ha. apply KB5. apply et_carry_out. exists r. split; [exact Hr | exact Ha].
    - intros b Hb. apply HBLK4. unfold et_blks, model_blks. right. right.
      apply in_or_app. right. apply in_or_app. right. exact Hb. }
  assert (HLK5 : alock_at fr_RG W3 (ms_mem ms2) false).
  { apply (alock_at_kept fr_RG W mem W3 (ms_mem ms2) false HLK).
    intros r [<- | []] a Ha. apply KB5. left. apply et_lock_GL. cbn [fst snd] in Ha. lia. }
  assert (HQO : q <> lm_out m).
  { pose proof HAO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoc).
    destruct Hoc as [(_ & Ho & _) | (Hcp & _ & Hoin & _)]; [lia|].
    intros Hq. destruct (HQB (lm_out m) (lm_cap m) Hoin) as [Hd | Hd]; unfold req_size in Hd;
      destruct (Z.eqb_spec (lm_cap m) 0); lia. }
  assert (HTAIL5 : forall a, q + Z.of_nat (length (ev_line cx m slen)) < a <
      q + Z.of_nat (length (ev_line cx m slen)) - (q + Z.of_nat (length (ev_line cx m slen))) mod 8 + 8 ->
      aview segs (w_H W3) (ms_mem ms2) a <> None).
  { intros a Ha. rewrite HELEN in Ha. apply (ALLOC_TAIL_x ly4 S4 W3 (ms_mem ms2) _ q (slen + 1) a HAR7 Hqin).
    rewrite Hreqq. replace (q + (slen + 1) - 1) with (q + slen) by lia. exact Ha. }
  pose proof (LS_event_relay cx t m ly3 S3 S4 (ev_line cx m slen) ly4 q HLS HRI HEVT
    ltac:(rewrite Hrelen; exact Hmleq) HO ltac:(rewrite Hrelen; exact Hblq)) as (LR1 & LR2 & LR3).
  (* re_spec_x's byte premise is the byte peak of send_line's trace; LS_event_relay's sum form bounds it
     (W_tr_peak.v sl_tr_peak_le_alloc, at aout_at's 0 <= cap) *)
  assert (Hcap0 : 0 <= lm_cap m)
    by (pose proof HAO5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
          _ & _ & _ & [(Hcz & _) | (Hcz & _)]); lia).
  assert (HLR2 : blocks_bytes S4 + tr_peak (sl_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
      (re_len (ev_line cx m slen))) <= LIVE_MAX).
  { pose proof (W_tr_peak.sl_tr_peak_le_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
      (re_len (ev_line cx m slen)) Hcap0). lia. }
  (* relay_event's count premise (its peak re_pk = 2) at the state after the malloc: the entry's blocks and the
     event's line block *)
  assert (HCNT4 : cnt_ok_pk RP re_pk (ablocks B ly4 S4)).
  { apply (cnt_ok_pk_mono RP (fun P => ((if P (re_len (ev_line cx m slen)) then 1 else 0) + 2)%nat) re_pk (ablocks B ly3 S3) (ablocks B ly4 S4)); [|exact HCNTpk].
    intros P. cbv beta. rewrite Hblq, ReplyCnt.acnt_app, acnt_cons, acnt_nil.
    cbn [snd]. rewrite Hrelen. unfold re_pk. lia. }
  assert (HRM4' : rp_RM RP S4 (Z.to_nat (sl_cost MT_rk (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
      (re_len (ev_line cx m slen))) + 0)%nat) by (apply RP_NP; apply RP_NP in HRM4; exact HRM4).
  assert (HGRE1 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG et_GRE a)
    by (intros a Ha; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
  assert (HGRE2 : forall a, inG (G_SL B fr_RG) a -> inG et_GRE a) by (intros a Ha; apply Exists_cons_tl; exact Ha).
  assert (HGRE3 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ (as_errno B <= a < as_errno B + 4))
    by (intros a Ha; exact (HERR_AP a (et_lock_GL a Ha))).
  eapply (SRrG_bind segs R R_trans).
  { change (Z_to_bv 64 (BASE + 1016)) with (w64 (BASE + AF_fr_relay_event)).
    exact (RE_R W3 ly4 S4 [] (ms_regs ms2) (ms_mem ms2) _ chR (lm_c m) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
      (lm_cap m) (lm_out m) q (ev_line cx m slen) q (slen + 1) HPRER V10 (et_garr8_of_ob _ _ _ _ HOBQ)
      (proj1 (proj2 (proj2 HEVT))) Hqin HQO (Z.le_refl q) ltac:(rewrite Hrelen, Hreqq; lia) HTAIL5 HAO5 HLK5 ROM5
      HGRE1 HGRE2 HGRE3 LR1 HLR2 LR3 0%nat HRM4' HCNT4). }
  cbv beta. intros W5 c5 Hwle5
    (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & out' & -> & HJR & HPR5 & HAPK5 & HMLE5 & HRM5 & HPERM5 & HAO6 & HLK6).
  hp0gR HJR.
  (* the journal: relay_event's, lifted to G_fr and composed (its FP is g_out's block, which ablocks_sep puts in the
     entry's footprint or makes new) *)
  assert (HGsub : forall a, inG et_GRE a -> inG G_fr a).
  { intros a Ha. unfold W_LLVMFuzzerTestOneInput_event.et_GRE, inG in Ha. apply Exists_cons in Ha as [Ha | Ha].
    - apply HGlock. unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
    - apply HG_SL. exact Ha. }
  assert (HOUTB : forall b, In b (aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  assert (HJ5 : AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly5 S5 W5 mem5 md5 (k + 1 + k5)).
  { eapply (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans);
      [exact HJ4 | exact (ajournal_gx_G_mono0R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGsub HJR) | lia | lia | lia
      | intros a (r & Hr & _); destruct Hr | exact HG | ].
    intros a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hb).
    cbn [fst snd] in Ha.
    assert (Hbn : In (b, n) (aout_blks (lm_cap m) (lm_out m))) by exact Hb.
    unfold aout_blks in Hb. destruct (Z.eqb_spec (lm_cap m) 0) as [Hc0 | Hc0]; [destruct Hb|].
    destruct Hb as [Hb | []]. injection Hb as <- <-.
    destruct HSEP as (_ & HSEP2).
    destruct (HSEP2 (lm_out m, lm_cap m) (HOUTB _ Hbn)) as [Hn | Hf].
    - right. exists (lm_out m), (lm_cap m). split; [apply HBLK4; right; exact (HOUTB _ Hbn)|].
      split; [exact Hn | exact Ha].
    - left. split.
      + apply Hf. cbn [fst snd]. lia.
      + exists (lm_out m), (lm_cap m). split; [apply HBLK4; right; exact (HOUTB _ Hbn) | exact Ha]. }
  cbn [app] in HJ5.
  (* ---- 0x84b10 `mv a0,s9; jal check_shape_event` ---- *)
  assert (W5_26 : getr regs5 26 = w64 SB)
    by (rewrite (et_pres (ms_regs ms2) regs5 26%bv HPR5 ltac:(et_cs)), T26, (EEx 26%nat 26%bv eq_refl),
          (RG4 26%bv ltac:(cbv; tauto)); exact R26).
  destruct (et_regs_entry AF_ev_ret_relay W5 regs5 mem5 W5_26) as [HS6 SHOK6].
  remember (Eimg (Ereg regs5 [])) as E6 eqn:HE6.
  assert (HEI6 : img_env VAL A_LIM E6) by (subst E6; apply Eimg_env).
  assert (HAE6 : env_agree 32 (Ereg regs5 []) E6)
    by (rewrite HE6; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE6 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E6 n0 = getr regs5 r).
  { intros n0 r Hn. rewrite HE6. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  clear HE6.
  unfold cfg_at. rewrite T1. change (Z_to_bv 64 (BASE + 10276)) with (Z_to_bv 64 (BASE + AF_ev_ret_relay)).
  paj_run_to_tok_x RUNTOG HS6 HJ5 SHOK6 etspan AF_fr_check_shape_event.
  { apply awr_ok_x_nil. }
  pmkst HS6.
  ev_meq HF0 Em6. clear HF0 HFr0 HG1. rewrite Em6 in *.
  prreg HS6 (1%bv : bv 5) U1. prreg HS6 (2%bv : bv 5) U2. prreg HS6 (3%bv : bv 5) U3. prreg HS6 (4%bv : bv 5) U4.
  prreg HS6 (8%bv : bv 5) U8. prreg HS6 (10%bv : bv 5) U10.
  (* ---- what relay_event kept: the globals the tail carries but the lock and send_line's, the line's block, the
     input's and the model's blocks but g_out's, the frame, the fake frame and its shadow ---- *)
  rewrite Hsp5 in HJR.
  assert (HGxR : gx_ok segs B et_GRE) by (intros a Ha; exact (HG a (HGsub a Ha))).
  destruct HPERM5 as (restR & HPR4 & HPR5b).
  pose proof (et_nodup_x ly3 S3 W mem md HAR3) as ND3.
  pose proof HSEP as ((rest0 & HP3) & HSEP2).
  pose proof (Permutation_NoDup HP3 ND3) as ND3'.
  replace (input_blks cx) with [(c_p cx, c_n cx)] in ND3'
    by (unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); reflexivity).
  rewrite et_model_blks in ND3'.
  assert (HNO : forall b, In b ((c_p cx, c_n cx) :: et_rest_blks m) -> ~ In b (aout_blks (lm_cap m) (lm_out m))).
  { intros b Hb Ho. pose proof ND3' as ND.
    apply YG04.NoDup_app_iff in ND as (_ & ND4 & HD4).
    destruct Hb as [<- | Hb].
    - exact (HD4 _ (or_introl eq_refl) (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_intror Ho))))).
    - apply YG04.NoDup_app_iff in ND4 as (ND5 & _ & _). apply YG04.NoDup_app_iff in ND5 as (_ & _ & HD5).
      exact (HD5 b Hb Ho). }
  assert (HSURV : forall b, In b (ablocks B ly4 S4) -> ~ In b (aout_blks (lm_cap m) (lm_out m)) ->
      In b (ablocks B ly5 S5)).
  { intros b Hb Hno. apply (Permutation_in _ HPR4) in Hb. apply in_app_or in Hb as [Hb | Hb]; [contradiction|].
    apply (Permutation_in _ (Permutation_sym HPR5b)). apply in_or_app. right. exact Hb. }
  assert (HOFP : forall b n, In (b, n) (ablocks B ly4 S4) -> ~ In (b, n) (aout_blks (lm_cap m) (lm_out m)) ->
      forall a, b <= a < b + req_size n -> ~ inFP (ablocks_fp (aout_blks (lm_cap m) (lm_out m))) a).
  { intros b n Hb Hno a Ha (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([o c] & <- & Ho).
    cbn [fst snd] in Hra.
    assert (Hoin : In (o, c) (ablocks B ly4 S4)) by (apply HBLK4; right; apply HOUTB; exact Ho).
    assert (Hne : (b, n) <> (o, c)) by (intros Eq; rewrite Eq in Hno; exact (Hno Ho)).
    pose proof (sep_blocks0 ly4 S4 W3 _ _ b n o c HAR7 Hb Hoin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (HFFO : forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) ->
      ~ inFP (ablocks_fp (aout_blks (lm_cap m) (lm_out m))) a).
  { intros a Ha (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([o c] & <- & Ho).
    cbn [fst snd] in Hra.
    assert (Hoin : In (o, c) (ablocks B ly4 S4)) by (apply HBLK4; right; apply HOUTB; exact Ho).
    pose proof (sep_block_frame0 ly4 S4 W3 _ _ o c 1 fpos HAR7 Hoin Hin4) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFFeq4 in Hd.
    replace (fs_frame_bytes 1) with 128 in Hd by reflexivity.
    destruct (al0_blocks ly4 S4 W3 _ _ o c HAR7 Hoin) as (_ & _ & Hoceil & Hoapp & _).
    destruct (frames_bounds0 ly4 S4 W3 _ _ 1 fpos HAR7 Hin4) as (HFa & HFb & HFapp).
    rewrite HFFeq4 in HFa, HFb, HFapp. replace (fs_frame_bytes 1) with 128 in HFb, HFapp by reflexivity.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hdv. pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hdv0.
    clear - Ha Hra Hd Hoceil Hoapp HFa HFb HFapp D1 D2 D3 D4 D5 Hdv Hdv0.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. unfold SB in *. lia. }
  assert (HGLr_GRE : forall a, inG et_GLr a -> ~ inG et_GRE a).
  { intros a Ha HGa. pose proof (HERR_AP a (et_GLr_GL a Ha)) as He.
    clear - Ha HGa He. unfold W_LLVMFuzzerTestOneInput_event.et_GRE, G_SL, inG in HGa. unfold inG, et_GLr in Ha.
    unfold AG_NFD, AG_THREAD_UP, AG_LISTEN, fr_RG, ASRC in *.
    cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
         rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.
    repeat match goal with H : Exists _ (_ :: _) |- _ => apply Exists_cons in H as [H | H]
                         | H : Exists _ [] |- _ => inversion H end;
      unfold in_zr in *; cbn [fst snd] in *; lia. }
  assert (HOUT0 : forall b, In b (aout_blks (lm_cap m) (lm_out m)) -> 0 < fst b).
  { intros [o c] Ho. assert (Hoin : In (o, c) (ablocks B ly4 S4)) by (apply HBLK4; right; apply HOUTB; exact Ho).
    destruct (al0_blocks ly4 S4 W3 _ _ o c HAR7 Hoin) as (_ & Ho4096 & _). cbn [fst]. lia. }
  assert (KR6 : forall a, et_cr cx FF et_GLr ((q, slen + 1) :: (c_p cx, c_n cx) :: et_rest_blks m) a ->
      aview segs (w_H W5) mem5 a = aview segs (w_H W3) (ms_mem ms2) a).
  { apply (et_cr_gx_xR cx FF et_GLr _ et_GRE RE_STK _ ly4 S4 W3 (ms_mem ms2) _ ly5 S5 W5 mem5 _ k5 fpos HGxR HJR HAR7 Hin4
      ltac:(symmetry; exact HFFeq4)).
    - intros a Ha. split; [exact (et_GLr_G a Ha)|]. split; [exact (HGLr_GRE a Ha)|].
      split; [exact (HERR_AP a (et_GLr_GL a Ha))|]. apply fp_spares_closed. apply sink_closed_ablocks_fp.
      apply Forall_forall. exact HOUT0.
    - intros b n Hb.
      assert (Hb4 : In (b, n) (ablocks B ly4 S4)).
      { destruct Hb as [Hb | Hb]; [injection Hb as <- <-; exact Hqin|].
        apply HBLK4. unfold et_blks. destruct Hb as [<- | Hb]; [left; reflexivity|].
        right. rewrite et_model_blks. apply in_or_app. left. exact Hb. }
      assert (Hno : ~ In (b, n) (aout_blks (lm_cap m) (lm_out m))).
      { destruct Hb as [Hb | Hb]; [|exact (HNO _ Hb)]. injection Hb as <- <-. intros Ho.
        unfold aout_blks in Ho. destruct (lm_cap m =? 0); [destruct Ho|]. destruct Ho as [Ho | []].
        injection Ho as Ho _. exact (HQO (eq_sym Ho)). }
      split; [exact Hb4|]. split; [exact (HSURV _ Hb4 Hno)|]. exact (HOFP b n Hb4 Hno).
    - exact HFFO.
    - rewrite HRES. lia.
    - exact HFlo.
    - lia. }
  (* ---- the frame at relay_event's return, the registers at check_shape_event's entry ---- *)
  pose proof HJ5 as (_ & _ & (memS7 & HJi7 & HAG7) & _). rewrite !Z.add_0_r in HJi7.
  pose proof HJi7 as (HAR8 & _ & _ & _ & _ & Hfrs7 & _ & _ & _ & _ & _ & _ & _ & HPRES7 & _).
  assert (Hin5 : In (1, fpos) (frames S5)) by (rewrite Hfrs7; left; reflexivity).
  assert (HFFeq5 : frame_addr ly5 1 fpos = FF).
  { pose proof HJi7 as (_ & Hly5 & _). pose proof Hly5 as (_ & _ & _ & _ & _ & EF5 & _).
    pose proof HJi as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
    unfold FF, frame_addr. rewrite EF5, <- EF3. reflexivity. }
  assert (HFR5 : aframe_at cx true FF W5 mem5).
  { apply (et_frame_at_x cx FF ly5 S5 W3 W5 (ms_mem ms2) mem5 _ fpos HFR4 ltac:(lia) ltac:(lia) ltac:(lia)
      HAR8 Hin5 ltac:(symmetry; exact HFFeq5) HPRES7).
    - intros a Ha _. apply KR6. right. right. left. exact Ha.
    - intros a Ha. apply KR6. right. right. right. left. exact Ha.
    - intros a Ha. apply KR6. right. right. right. right. exact Ha. }
  assert (W5_2 : getr regs5 2 = w64 (lf_F cx)) by (rewrite (et_pres (ms_regs ms2) regs5 2%bv HPR5 ltac:(et_cs)); exact V2).
  assert (W5_3 : getr regs5 3 = w64 (as_gp B)) by (rewrite (et_pres (ms_regs ms2) regs5 3%bv HPR5 ltac:(et_cs)); exact V3).
  assert (W5_4 : getr regs5 4 = w64 (as_tp B)) by (rewrite (et_pres (ms_regs ms2) regs5 4%bv HPR5 ltac:(et_cs)); exact V4).
  assert (W5_8 : getr regs5 8 = getr (c_regs cx) 2)
    by (rewrite (et_pres (ms_regs ms2) regs5 8%bv HPR5 ltac:(et_cs)); exact V8).
  assert (W5_9 : getr regs5 9 = w64 (lf_F cx))
    by (rewrite (et_pres (ms_regs ms2) regs5 9%bv HPR5 ltac:(et_cs)), T9, (EEx 9%nat 9%bv eq_refl),
          (RG4 9%bv ltac:(cbv; tauto)); exact R9).
  assert (W5_18 : getr regs5 18 = w64 HI_G_SRC)
    by (rewrite (et_pres (ms_regs ms2) regs5 18%bv HPR5 ltac:(et_cs)), T18, (EEx 18%nat 18%bv eq_refl),
          (RG4 18%bv ltac:(cbv; tauto)); exact R18).
  assert (W5_19 : getr regs5 19 = w64 (FF + 32))
    by (rewrite (et_pres (ms_regs ms2) regs5 19%bv HPR5 ltac:(et_cs)), T19, (EEx 19%nat 19%bv eq_refl),
          (RG4 19%bv ltac:(cbv; tauto)); exact R19).
  assert (W5_24 : getr regs5 24 = w64 (SB + FF / 8))
    by (rewrite (et_pres (ms_regs ms2) regs5 24%bv HPR5 ltac:(et_cs)), T24, (EEx 24%nat 24%bv eq_refl),
          (RG4 24%bv ltac:(cbv; tauto)); exact R24).
  assert (W5_27 : getr regs5 27 = w64 t)
    by (rewrite (et_pres (ms_regs ms2) regs5 27%bv HPR5 ltac:(et_cs)), T27, (EEx 27%nat 27%bv eq_refl),
          (RG4 27%bv ltac:(cbv; tauto)); exact R27).
  assert (W5_25 : getr regs5 25 = w64 q)
    by (rewrite (et_pres (ms_regs ms2) regs5 25%bv HPR5 ltac:(et_cs)), T25, (EEx 25%nat 25%bv eq_refl); exact R4_25).
  assert (W5_22 : getr regs5 22 = w64 (c_p cx + ev_k2 cx m))
    by (rewrite (et_pres (ms_regs ms2) regs5 22%bv HPR5 ltac:(et_cs)), T22, (EEx 21%nat 21%bv eq_refl),
          (EEx 22%nat 22%bv eq_refl), (RG4 21%bv ltac:(cbv; tauto)), (RG4 22%bv ltac:(cbv; tauto)), R21, R22;
        unfold w64; rewrite YK1e.alu64_add_lit; f_equal; unfold ev_k2, ev_parg, ev_k1; lia).
  (* ---- check_shape_event(q): W3's cse_spec ---- *)
  assert (U2' : getr (ms_regs ms3) 2 = w64 (lf_F cx)) by (rewrite U2, (EE6 2%nat 2%bv eq_refl); exact W5_2).
  assert (U3' : getr (ms_regs ms3) 3 = w64 (as_gp B)) by (rewrite U3, (EE6 3%nat 3%bv eq_refl); exact W5_3).
  assert (U4' : getr (ms_regs ms3) 4 = w64 (as_tp B)) by (rewrite U4, (EE6 4%nat 4%bv eq_refl); exact W5_4).
  assert (U8' : getr (ms_regs ms3) 8 = getr (c_regs cx) 2) by (rewrite U8, (EE6 8%nat 8%bv eq_refl); exact W5_8).
  assert (U10' : getr (ms_regs ms3) 10 = w64 q) by (rewrite U10, (EE6 25%nat 25%bv eq_refl); exact W5_25).
  assert (Hsp6 : spZ (ms_regs ms3) = lf_F cx) by (unfold spZ; rewrite U2'; unfold w64; apply unsigned_lit_small; lia).
  assert (HFR5' : aframe_at cx true (frame_addr ly5 1 fpos) W5 mem5) by (rewrite HFFeq5; exact HFR5).
  assert (HCSES : CSE_STK = 8304) by reflexivity.
  destruct (et_afn_pre_at_xR cx true ly5 S5 fpos (k + 1 + k5) W5 mem5 _ (ms_regs ms3) CSE_STK HB HJ5 HFR5' Hsp6
      ltac:(rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity])
      ltac:(unfold raZ; rewrite U1, unsigned_lit_small by lia; lia)
      U3' U4' U8' ltac:(lia) ltac:(lia)) as (chC & HPREC & _).
  assert (Hq5 : In (q, slen + 1) (ablocks B ly5 S5)).
  { apply HSURV; [exact Hqin|]. intros Ho. unfold aout_blks in Ho. destruct (lm_cap m =? 0); [destruct Ho|].
    destruct Ho as [Ho | []]. injection Ho as Ho _. exact (HQO (eq_sym Ho)). }
  assert (HOBQ6 : ob_at W5 mem5 q (ev_line cx m slen ++ [Z_to_bv 8 0])).
  { intros i Hi. rewrite length_app, HLn in Hi. cbn [length] in Hi.
    rewrite (KR6 (q + i)); [exact (HOBQ i ltac:(rewrite length_app, HLn; cbn [length]; lia))|].
    right. left. exists q, (slen + 1). split; [left; reflexivity | rewrite Hreqq; lia]. }
  pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
  assert (HGN6 : agone_at fr_RG W5 mem5 (lm_gn m)).
  { apply (agone_at_kept fr_RG W mem W5 mem5 _ HGN). intros r [<- | []] x Hx.
    assert (Hx' : inG et_GLr x) by (cbn [fst snd] in Hx; clear - Hx; et_inG).
    apply (et_kept_G W W5 mem mem5 x (et_GLr_G x Hx')).
    rewrite (KR6 x (or_introl Hx')). apply KV5. left. exact (et_GLr_GL x Hx'). }
  pose proof HAO6 as (O1 & _ & O3 & _ & O5 & _ & O7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & O25 & O26).
  pose proof HGN6 as (G1 & _ & G3).
  assert (Hno' : sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen)) <= slen + 1).
  { rewrite HO, Hrelen. unfold sl_no. cbn [length Z.of_nat]. destruct (sl_live (lm_c m) (slen + 1)); lia. }
  assert (HOBO : ob_at W5 mem5 out' (sl_O (lm_c m) (lm_O m) (ev_line cx m slen ++ [Z_to_bv 8 0]))).
  { destruct O26 as [(_ & _ & Hno0) | (Hcp & Hnoc & Hoin & junk & Hj & Hg)].
    - intros i Hi. lia.
    - pose proof (et_ob_of_garr8 W5 mem5 out' _ Hg) as Hob. intros i Hi.
      specialize (Hob i ltac:(rewrite length_app; lia)). rewrite app_nth1 in Hob by lia. exact Hob. }
  assert (HSTR : 0 < sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen)) ->
      0 < out' /\ out' + sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen)) + 8 <= 2 ^ 63 /\
      sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen)) < 2 ^ 32 /\
      amem_range out' (sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen)) + 8) /\
      range_addressable (aview segs (w_H W5) mem5) SHADOW_OFF out'
        (sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen))) /\
      shadow_hull_vis (aview segs (w_H W5) mem5) out'
        (sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen))) /\
      (forall a, out' <= a < out' + sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen)) ->
         aview segs (w_H W5) mem5 a <> None /\ ~ (spZ (ms_regs ms3) - CSE_STK <= a < spZ (ms_regs ms3)))).
  { intros Hpos. destruct O26 as [(_ & _ & Hno0) | (Hcp & Hnoc & Hoin & junk & Hj & Hg)]; [lia|].
    destruct (al0_blocks ly5 S5 W5 mem5 _ out' _ HAR8 Hoin) as (Ho16 & Ho4096 & Hoceil & Hoapp & _).
    assert (Hreqo : req_size (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen)))
        = sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen)))
      by (unfold req_size; destruct (Z.eqb_spec (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
            (re_len (ev_line cx m slen))) 0); lia).
    rewrite Hreqo in Hoceil, Hoapp.
    split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { clear - Hoapp Hoceil Hnoc D1 D2 D3 D4 D5. unfold amem_range.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hoapp.
      destruct Hoapp as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia. }
    split; [eapply (range_addressable_of_block0 ly5 S5 W5 mem5 _ out' _); [exact HAR8 | exact Hoin | lia | rewrite Hreqo; lia]|].
    split; [eapply (shadow_hull_vis_of_block0 ly5 S5 W5 mem5 _ out' _); [exact HAR8 | exact Hoin | lia | rewrite Hreqo; lia | exact Hpos]|].
    intros a Ha. split; [|rewrite Hsp6; lia].
    pose proof (et_ob_of_garr8 W5 mem5 out' _ Hg (a - out') ltac:(rewrite length_app; lia)) as Hv.
    replace (out' + (a - out')) with a in Hv by lia. rewrite Hv. discriminate. }
  assert (HGS : (lm_gn m = 1 /\ sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen)) = 0) \/
      (lm_gn m = 0 /\ sl_O (lm_c m) (lm_O m) (ev_line cx m slen ++ [Z_to_bv 8 0]) = ev_line cx m slen ++ [Z_to_bv 8 0])).
  { destruct (RI_event_live cx t m HRI) as (RL0 & RL1).
    assert (Hlen1 : Z.of_nat (length (ev_line cx m slen ++ [Z_to_bv 8 0])) = slen + 1)
      by (rewrite length_app, HLn; cbn [length]; lia).
    unfold sl_O, sl_no, sl_live, send_line_c.send_live, send_line_c.send_off. rewrite Hlen1, Hrelen, HO.
    destruct G3 as [Hg0 | Hg1].
    - right. split; [exact Hg0|]. destruct (RL0 Hg0) as (Hcl & Hbr & Hdd). rewrite Hcl, Hbr, Hdd.
      replace (slen + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - left. split; [exact Hg1|].
      destruct (RL1 Hg1) as [Hx | [Hx | Hx]]; rewrite Hx;
        [replace (-1 <? 0) with true by reflexivity | rewrite Bool.orb_comm with (b1 := (ct_cl (lm_c m) <? 0)); cbn | ];
        rewrite ?Bool.orb_true_r, ?Bool.orb_true_l; cbn; try reflexivity;
        destruct ((ct_cl (lm_c m) <? 0) || (ct_br (lm_c m) =? 1) || (slen + 1 =? 0)); reflexivity. }
  assert (ROM6 : rom_view segs W5 mem5)
    by (eapply ajournal_gx_rom_view0R; first [exact HJ5 | exact ET_ROM_OUT | exact HROM0 | exact LAWS | exact pa_segs_low]).
  eapply (SRrG_bind segs R R_trans).
  { change (Z_to_bv 64 (BASE + 15540)) with (w64 (BASE + AF_fr_check_shape_event)).
    (* check_shape_event frees nothing: its strict contract, lifted *)
    apply (SRr_SRrG segs R WLE_R).
    exact (CSE W5 ly5 S5 [] (ms_regs ms3) mem5 _ chC q (ev_line cx m slen) (lm_gn m)
      (sl_no (lm_c m) (Z.of_nat (length (lm_O m))) (re_len (ev_line cx m slen))) out'
      (sl_O (lm_c m) (lm_O m) (ev_line cx m slen ++ [Z_to_bv 8 0]))
      HPREC U10' (proj1 (proj2 (proj2 HEVT))) HOBQ6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Hsp6, HCSES, HELEN; intros a Ha; lia)
      ltac:(rewrite HELEN; eapply (amem_range_of_block0 ly5 S5 W5 mem5 _ q (slen + 1)); [exact HAR8 | exact Hq5 | lia | rewrite Hreqq; lia])
      ltac:(clear - Hqapp Hq16 Hqceil Hslenr D1 D2 D3 D4 D5; unfold amem_range;
            unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hqapp;
            destruct Hqapp as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia)
      ltac:(rewrite HELEN; eapply (range_addressable_of_block0 ly5 S5 W5 mem5 _ q (slen + 1)); [exact HAR8 | exact Hq5 | lia | rewrite Hreqq; lia])
      ltac:(rewrite HELEN; eapply (shadow_hull_vis_of_block0 ly5 S5 W5 mem5 _ q (slen + 1)); [exact HAR8 | exact Hq5 | lia | rewrite Hreqq; lia | lia])
      ltac:(rewrite HELEN; intros a Ha; split;
            [apply (ALLOC_TAIL_x ly5 S5 W5 mem5 _ q (slen + 1) a HAR8 Hq5); rewrite Hreqq; replace (q + (slen + 1) - 1) with (q + slen) by lia; exact Ha
            | rewrite Hsp6, HCSES; pose proof (Z.mod_pos_bound (q + slen) 8 ltac:(lia)); lia])
      ROM6 G1 G3 O3 O7 O25 HOBO HSTR HGS). }
  cbv beta. intros W6 c6 Hwle6 (regs6 & mem6 & md6 & -> & HJC & HPR6 & _ & HPRES6').
  (* the journal: check_shape_event's strict leaf journal (G = [], FP = []), lifted to G_fr and to R, and composed *)
  assert (HJ6 : AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly5 S5 W6 mem6 md6 (k + 1 + k5 + 0)).
  { eapply (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans);
      [exact HJ5 | exact (ev_gx_lift_xR (ajournal_gx_G_mono0 [] G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                            (fun a Ha => False_ind _ (inG_nil a Ha)) (proj2 (ajournal_gx_nil0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJC)))
      | rewrite Hsp6; lia | rewrite Hsp6; lia | rewrite Hsp6; lia
      | intros a (r & Hr & _); destruct Hr | exact HG | intros a (r & Hr & _); destruct Hr]. }
  cbn [app] in HJ6.
  assert (HBL5 : forall b, In b ((c_p cx, c_n cx) :: et_rest_blks m) -> In b (ablocks B ly5 S5)).
  { intros b Hb. apply HSURV; [|exact (HNO b Hb)]. apply HBLK4. unfold et_blks.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. rewrite et_model_blks. apply in_or_app. left. exact Hb. }
  assert (HBO5 : forall b, In b (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') -> In b (ablocks B ly5 S5)).
  { intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) 0) as [|Hcz]; [destruct Hb|].
    destruct Hb as [<- | []]. destruct O26 as [(Hc0 & _) | (_ & _ & Hoin & _)]; [lia | exact Hoin]. }
  assert (HGF : forall a, inG (et_GLr ++ et_GO) a -> inG G_fr a /\ ~ (as_errno B <= a < as_errno B + 4)).
  { intros a Ha. unfold inG in Ha. apply Exists_app in Ha as [Ha | Ha].
    - exact (conj (et_GLr_G a Ha) (HERR_AP a (et_GLr_GL a Ha))).
    - exact (conj (HG_carry a (et_GO_GL a Ha)) (HERR_AP a (et_GO_GL a Ha))). }
  assert (KC7 : forall a, et_cr cx FF (et_GLr ++ et_GO)
      ((q, slen + 1) :: ((c_p cx, c_n cx) :: et_rest_blks m) ++ aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') a ->
      aview segs (w_H W6) mem6 a = aview segs (w_H W5) mem5 a).
  { pose proof (proj2 (ajournal_gx_nil0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJC) as HJC'. rewrite Hsp6 in HJC'.
    apply (et_cr_gx_xR cx FF _ _ [] CSE_STK [] ly5 S5 W5 mem5 _ ly5 S5 W6 mem6 md6 0 fpos (gx_ok_nil segs B) (ev_gx_lift_xR HJC') HAR8 Hin5
      ltac:(symmetry; exact HFFeq5)).
    - intros a Ha. destruct (HGF a Ha) as (H1 & H2). split; [exact H1|]. split; [intros Hn; exact (inG_nil a Hn)|].
      split; [exact H2|]. apply fp_spares_closed. exact (sink_closed_ablocks_fp [] (Forall_nil _)).
    - intros b n Hb. assert (Hb5 : In (b, n) (ablocks B ly5 S5)).
      { destruct Hb as [Hb | Hb]; [injection Hb as <- <-; exact Hq5|].
        apply in_app_or in Hb as [Hb | Hb]; [exact (HBL5 _ Hb) | exact (HBO5 _ Hb)]. }
      split; [exact Hb5|]. split; [exact Hb5|]. intros a _ (r & Hr & _). destruct Hr.
    - intros a _ (r & Hr & _). destruct Hr.
    - rewrite HCSES. lia.
    - exact HFlo.
    - lia. }
  (* ---- 0x84b18 `mv a0,s9; jal free` ---- *)
  assert (W6_26 : getr regs6 26 = w64 SB)
    by (rewrite (et_pres (ms_regs ms3) regs6 26%bv HPR6 ltac:(et_cs)); prreg HS6 (26%bv : bv 5) U26;
        rewrite U26, (EE6 26%nat 26%bv eq_refl); exact W5_26).
  destruct (et_regs_entry AF_ev_ret_cse W6 regs6 mem6 W6_26) as [HS7 SHOK7].
  remember (Eimg (Ereg regs6 [])) as Ef eqn:HEf.
  assert (HEIf : img_env VAL A_LIM Ef) by (subst Ef; apply Eimg_env).
  assert (HAEf : env_agree 32 (Ereg regs6 []) Ef)
    by (rewrite HEf; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEf : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew Ef n0 = getr regs6 r).
  { intros n0 r Hn. rewrite HEf. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  clear HEf.
  rewrite U1. change (Z_to_bv 64 (BASE + 10284)) with (Z_to_bv 64 (BASE + AF_ev_ret_cse)).
  paj_run_tok_x RUNG HS7 HJ6 SHOK7 etspan.
  { apply awr_ok_x_nil. }
  pmkst HS7.
  ev_meq HF0 Em7. clear HF0 HFr0 HG1. rewrite Em7 in *.
  prreg HS7 (1%bv : bv 5) Y1. prreg HS7 (2%bv : bv 5) Y2. prreg HS7 (3%bv : bv 5) Y3. prreg HS7 (4%bv : bv 5) Y4.
  prreg HS7 (8%bv : bv 5) Y8. prreg HS7 (10%bv : bv 5) Y10.
  prreg HS6 (25%bv : bv 5) U25.
  assert (W6_2 : getr regs6 2 = w64 (lf_F cx)) by (rewrite (et_pres (ms_regs ms3) regs6 2%bv HPR6 ltac:(et_cs)); exact U2').
  assert (W6_3 : getr regs6 3 = w64 (as_gp B)) by (rewrite (et_pres (ms_regs ms3) regs6 3%bv HPR6 ltac:(et_cs)); exact U3').
  assert (W6_4 : getr regs6 4 = w64 (as_tp B)) by (rewrite (et_pres (ms_regs ms3) regs6 4%bv HPR6 ltac:(et_cs)); exact U4').
  assert (W6_8 : getr regs6 8 = getr (c_regs cx) 2)
    by (rewrite (et_pres (ms_regs ms3) regs6 8%bv HPR6 ltac:(et_cs)); exact U8').
  assert (W6_25 : getr regs6 25 = w64 q)
    by (rewrite (et_pres (ms_regs ms3) regs6 25%bv HPR6 ltac:(et_cs)), U25, (EE6 25%nat 25%bv eq_refl); exact W5_25).
  assert (Y2' : getr (ms_regs ms4) 2 = w64 (lf_F cx)) by (rewrite Y2, (EEf 2%nat 2%bv eq_refl); exact W6_2).
  assert (Y3' : getr (ms_regs ms4) 3 = w64 (as_gp B)) by (rewrite Y3, (EEf 3%nat 3%bv eq_refl); exact W6_3).
  assert (Y4' : getr (ms_regs ms4) 4 = w64 (as_tp B)) by (rewrite Y4, (EEf 4%nat 4%bv eq_refl); exact W6_4).
  assert (Y8' : getr (ms_regs ms4) 8 = getr (c_regs cx) 2) by (rewrite Y8, (EEf 8%nat 8%bv eq_refl); exact W6_8).
  assert (Y10' : getr (ms_regs ms4) 10 = w64 q) by (rewrite Y10, (EEf 25%nat 25%bv eq_refl); exact W6_25).
  assert (Hsp7 : spZ (ms_regs ms4) = lf_F cx) by (unfold spZ; rewrite Y2'; unfold w64; apply unsigned_lit_small; lia).
  pose proof HJ6 as (_ & _ & (memS8 & HJi8 & HAG8) & _). rewrite !Z.add_0_r in HJi8.
  pose proof HJi8 as (HAR9 & _ & _ & _ & _ & Hfrs8 & _ & _ & _ & _ & _ & _ & _ & HPRES8 & _).
  assert (HFR6 : aframe_at cx true FF W6 mem6).
  { apply (et_frame_at_x cx FF ly5 S5 W3 W6 (ms_mem ms2) mem6 _ fpos HFR4 ltac:(lia) ltac:(lia) ltac:(lia)
      HAR9 Hin5 ltac:(symmetry; exact HFFeq5) HPRES8).
    - intros a Ha _. rewrite (KC7 a ltac:(right; right; left; exact Ha)). apply KR6. right. right. left. exact Ha.
    - intros a Ha. rewrite (KC7 a ltac:(right; right; right; left; exact Ha)). apply KR6. right. right. right. left. exact Ha.
    - intros a Ha. rewrite (KC7 a ltac:(right; right; right; right; exact Ha)). apply KR6. right. right. right. right. exact Ha. }
  assert (HFR6' : aframe_at cx true (frame_addr ly5 1 fpos) W6 mem6) by (rewrite HFFeq5; exact HFR6).
  destruct (et_afn_pre_at_xR cx true ly5 S5 fpos (k + 1 + k5 + 0) W6 mem6 _ (ms_regs ms4) ASTACK HB HJ6 HFR6'
      Hsp7 ltac:(rewrite Y1; apply ret_ok_codeptr_v; [lia | reflexivity])
      ltac:(unfold raZ; rewrite Y1, unsigned_lit_small by lia; lia)
      Y3' Y4' Y8' ltac:(lia) ltac:(lia)) as (chF & HPREF & HSPF).
  pose proof HPREF as (_ & _ & _ & _ & _ & _ & _ & HchF & _).
  assert (HCHF : chain_pre ly5 (aview segs (w_H W6) mem6) (ms_regs ms4) chF).
  { apply (achain_chain_pre ly5 (aview segs (w_H W6) mem6) (spZ (ms_regs ms4)) (s0Z (ms_regs ms4))
      chF (ms_regs ms4) HchF); [rewrite Hsp7; lia | reflexivity |
      unfold raZ; rewrite Y1, unsigned_lit_small by lia; lia]. }
  pose proof (LS_event_free cx t m ly3 S3 S4 S5 (ev_line cx m slen) HLS HRI HEVT HO
    ltac:(rewrite Hrelen; exact Hmleq) HMLE5) as LF1.
  (* the free runs at relay_event's post: g_out's block is replaced, so at most one block more than the state after
     the malloc, which LS_cnt's peak (+ 2) covers *)
  assert (HCNT5 : cnt_ok RP (ablocks B ly5 S5)).
  { unfold cnt_ok. apply (cnt_ok_pk_mono RP (fun P => ((if P (re_len (ev_line cx m slen)) then 1 else 0) + 2)%nat) (fun _ => 0%nat) (ablocks B ly3 S3) (ablocks B ly5 S5)); [|exact HCNTpk].
    intros P. cbv beta.
    assert (Hout : forall c o, (ReplyCnt.acnt P (aout_blks c o) <= 1)%nat).
    { intros c o. unfold aout_blks. destruct (c =? 0); [rewrite acnt_nil; lia|].
      rewrite acnt_cons, acnt_nil. destruct (P (snd (o, c))); lia. }
    rewrite (ReplyCnt.acnt_perm P _ _ HPR5b), ReplyCnt.acnt_app.
    pose proof (ReplyCnt.acnt_perm P _ _ HPR4) as EQ4. rewrite ReplyCnt.acnt_app in EQ4.
    rewrite Hblq, ReplyCnt.acnt_app, acnt_cons, acnt_nil in EQ4. cbn [snd] in EQ4.
    rewrite <- Hrelen in EQ4.
    pose proof (Hout (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
      (re_len (ev_line cx m slen))) out'). lia. }
  assert (HRM5' : rp_RM RP S5 (1 + 0)%nat) by (apply RP_NP; apply RP_NP in HRM5; exact HRM5).
  pose proof (ev_aftok_new_block0R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi3 HAR4 Hblq ltac:(lia)) as HTOK.
  (* free's entry context: return site 0x84b20 over the chain's spine, a row of the K0 table *)
  assert (HCTXF : In (raZ (ms_regs ms4) :: spine chF) CTX_AFREE).
  { assert (Hra : raZ (ms_regs ms4) = BASE + AF_ev_ret_free)
      by (unfold raZ; rewrite Y1, unsigned_lit_small by lia; reflexivity).
    rewrite Hra. destruct HSPF as [-> | ->]; et_in_tab. }
  (* as at the malloc: the free's call frame is above the layout's bottom *)
  assert (HLYB5 : ly_bot ly5 + ACALL_PREFIX < spZ (ms_regs ms4)).
  { pose proof HJi8 as (_ & HLE8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK8 & _).
    unfold astk_ok in HSTK8. unfold layout_le in HLE8. unfold ly_bot in *.
    rewrite Hsp7. unfold LLVMF_STK, ASTACK, kStackSpan in *. lia. }
  (* the R rule's call-boundary premise RO at the call memory, from the call state's ARx *)
  pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi8)) as HRO8.
  eapply (SRrG_bind segs R R_trans).
  { rewrite (pal_free B TL).
    eapply (AFREE_R W6 (ms_regs ms4) mem6 LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS8 (c_md cx) [(1, fpos)] ly5 S5 [] _ (k + 1 + k5) q (slen + 1)
      (lf_F cx - spZ (c_regs cx)) _ chF 0%nat HJi8 Hq5 Y10'
      ltac:(rewrite Hsp7; lia) (et_F_mod16 cx Hal16) ltac:(lia) ltac:(lia) HLYB5
      Y3' Y4' Y1 (ret_ok_codeptr_v 10292 ltac:(lia) eq_refl) HCHF HRO8 HCTXF HRM5' HCNT5 HTOK LF1). }
  cbv beta. intros W7 c7 Hwle7
    (ly7 & S7 & Hp7 & regs7 & mem7 & md7 & -> & HJi9 & HPR7 & (l1 & l2 & Hbl5 & Hbl7) & Hfr7 & HKF & HMLE7 & HRM7
     & HERRF & HPRF).
  hp0a (proj1 HJi9).
  (* ---- after free: the journal repacked, what free kept, the frame ---- *)
  assert (HJ7 : AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly7 S7 W7 mem7 md7 (k + 1 + k5 + 1)).
  { apply (ajournal_gx_pack0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly7 S7 W7 mem7 md7 (k + 1 + k5 + 1) memS8);
      [lia | lia | rewrite !Z.add_0_r; exact HJi9 | exact HAG8 | apply out_none]. }
  replace (spZ (c_regs cx) + (lf_F cx - spZ (c_regs cx))) with (lf_F cx) in HKF by lia.
  assert (HqR : In (q, slen + 1) restR).
  { pose proof (Permutation_in _ HPR4 Hqin) as Hq. apply in_app_or in Hq as [Hq | Hq]; [|exact Hq].
    exfalso. unfold aout_blks in Hq. destruct (lm_cap m =? 0); [destruct Hq|].
    destruct Hq as [Hq | []]. injection Hq as Hq _. exact (HQO (eq_sym Hq)). }
  assert (HOQ : forall b n, In (b, n) (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') -> b + req_size n <= q \/ q + (slen + 1) <= b).
  { intros b n Hb.
    pose proof (Permutation_NoDup HPR5b (et_nodup_x ly5 S5 W5 mem5 _ HAR8)) as ND5.
    apply YG04.NoDup_app_iff in ND5 as (_ & _ & HD5).
    assert (Hne : (b, n) <> (q, slen + 1)) by (intros Eq; rewrite Eq in Hb; exact (HD5 _ Hb HqR)).
    pose proof (sep_blocks0 ly5 S5 W5 mem5 _ b n q (slen + 1) HAR8 (HBO5 _ Hb) Hq5 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqq in Hd. lia. }
  assert (KF7 : forall a, et_cr cx FF (et_GLr ++ et_GO) (((c_p cx, c_n cx) :: et_rest_blks m) ++ aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') a ->
      aview segs (w_H W7) mem7 a = aview segs (w_H W6) mem6 a).
  { apply (et_cr_acall_x cx FF _ _ ly5 S5 W6 W7 mem6 mem7 _ fpos q (slen + 1) HAR9 HKF Hin5
      ltac:(symmetry; exact HFFeq5) HGF).
    - intros b n Hb. apply in_app_or in Hb as [Hb | Hb].
      + split; [exact (HBL5 _ Hb)|]. intros a Ha. rewrite Hreqq.
        assert (Hb3 : In (b, n) (ablocks B ly3 S3)).
        { apply HBLK. unfold et_blks. destruct Hb as [Hb | Hb]; [left; exact Hb|].
          right. rewrite et_model_blks. apply in_or_app. left. exact Hb. }
        destruct (HQB b n Hb3) as [Hd | Hd]; lia.
      + split; [exact (HBO5 _ Hb)|]. intros a Ha. rewrite Hreqq. destruct (HOQ b n Hb) as [Hd | Hd]; lia.
    - intros a Ha. rewrite Hreqq. exact (HQF a Ha).
    - exact HFlo.
    - lia. }
  pose proof HJi9 as (HAR10 & _ & _ & _ & _ & Hfrs9 & _ & _ & _ & _ & _ & _ & _ & HPRES9 & _).
  assert (Hin7 : In (1, fpos) (frames S7)) by (rewrite Hfr7; exact Hin5).
  assert (HFFeq7 : frame_addr ly7 1 fpos = FF).
  { pose proof HJi9 as (_ & Hly7 & _). pose proof Hly7 as (_ & _ & _ & _ & _ & EF7 & _).
    pose proof HJi as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
    unfold FF, frame_addr. rewrite EF7, <- EF3. reflexivity. }
  assert (KFR : forall a, (lf_F cx <= a < spZ (c_regs cx) \/ FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) ->
      aview segs (w_H W7) mem7 a = aview segs (w_H W3) (ms_mem ms2) a).
  { intros a Ha.
    rewrite (KF7 a ltac:(right; right; exact Ha)), (KC7 a ltac:(right; right; exact Ha)).
    apply KR6. right. right. exact Ha. }
  assert (HFR7 : aframe_at cx true FF W7 mem7).
  { apply (et_frame_at_x cx FF ly7 S7 W3 W7 (ms_mem ms2) mem7 _ fpos HFR4 ltac:(lia) ltac:(lia) ltac:(lia)
      HAR10 Hin7 ltac:(symmetry; exact HFFeq7) HPRES9).
    - intros a Ha _. apply KFR. left. exact Ha.
    - intros a Ha. apply KFR. right. left. exact Ha.
    - intros a Ha. apply KFR. right. right. exact Ha. }
  assert (HFL7 : sv8 W7 mem7 (FF + 120) (flag_addr ly7 1 fpos)).
  { assert (HFLeq7 : flag_addr ly7 1 fpos = flag_addr ly3 1 fpos).
    { pose proof HJi9 as (_ & Hly7 & _). pose proof Hly7 as (_ & _ & _ & _ & _ & EF7 & _).
      pose proof HJi as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
      unfold flag_addr. rewrite EF7, <- EF3. reflexivity. }
    rewrite HFLeq7.
    apply (et_flag_at_x FF ly7 S7 W3 W7 (ms_mem ms2) mem7 _ fpos _ HFL4 HAR10 Hin7 ltac:(symmetry; exact HFFeq7)).
    intros a Ha. apply KFR. right. left. exact Ha. }
  (* ---- 0x84b20 `ld s7,120(s1); li s4,10; ld s9,104(s1); j 0x84490` ---- *)
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs5 _ EV_KEEP2 HS6 HAE6 ltac:(vm_compute; reflexivity)) as KR6'.
  cbn [ms_regs restrict] in KR6'.
  pose proof (regs_kept_of_st_ok segs Ef _ _ regs6 [] EV_KEEP2 HS7 HAEf ltac:(vm_compute; reflexivity)) as KR7'.
  cbn [ms_regs restrict] in KR7'.
  assert (R57 : forall r, In r EV_KEEP2 -> getr regs7 r = getr regs5 r).
  { intros r Hr. rewrite (et_pres (ms_regs ms4) regs7 r HPR7 (EV_KEEP2_cs r Hr)), (KR7' r Hr),
      (et_pres (ms_regs ms3) regs6 r HPR6 (EV_KEEP2_cs r Hr)), (KR6' r Hr). reflexivity. }
  pose proof HFR7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ffull & _).
  destruct (Ffull eq_refl) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
  assert (R7_9 : getr regs7 9 = w64 (lf_F cx)) by (rewrite (R57 9%bv ltac:(cbv; tauto)); exact W5_9).
  assert (R7_26 : getr regs7 26 = w64 SB) by (rewrite (R57 26%bv ltac:(cbv; tauto)); exact W5_26).
  destruct (et_lt_entry W7 regs7 mem7 (lf_F cx) R7_9 R7_26 ltac:(lia) ltac:(lia) F104 F120) as [HS8 SHOK8].
  remember (Eimg (Ereg regs7 [])) as El eqn:HEl.
  assert (HEIl : img_env VAL A_LIM El) by (subst El; apply Eimg_env).
  assert (HAEl : env_agree 32 (Ereg regs7 []) El)
    by (rewrite HEl; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEl : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew El n0 = getr regs7 r).
  { intros n0 r Hn. rewrite HEl. pose proof (bv_unsigned_in_range 5 r) as Hr5.
    change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  clear HEl.
  unfold cfg_at. change (Z_to_bv 64 (BASE + 10292)) with (Z_to_bv 64 (BASE + AF_ev_ret_free)).
  paj_run_to_tok_x RUNTOG HS8 HJ7 SHOK8 etspan AF_LLVM_latch.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  pmkst HS8.
  (* ---- at the latch 0x84490 ---- *)
  ev_meq HF0 Em8. clear HF0 HFr0 HG1. rewrite Em8 in *.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs7 _ [2;3;4;8;9;18;19;21;22;24;26;27]%bv HS8 HAEl
    ltac:(vm_compute; reflexivity)) as KR8.
  cbn [ms_regs restrict] in KR8.
  prreg HS8 (20%bv : bv 5) Z20. prreg HS8 (23%bv : bv 5) Z23. prreg HS8 (25%bv : bv 5) Z25.
  (* ---- the in.n slot, as the run to relay_event stored it (s4 - s5 = c_n - ev_k2) ---- *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS4 eq_refl) as RSLOT. cbn [ms_mem restrict] in RSLOT.
  assert (Ux9' : bv_unsigned (ew (ewset (ewset E4 512 w) 513 w0) 9) = lf_F cx)
    by (rewrite !ew_ewset_other by lia; exact Ux9).
  assert (Ex20 : ew (ewset (ewset E4 512 w) 513 w0) 20 = Z_to_bv 64 (c_n cx - ev_k1 cx m))
    by (rewrite !ew_ewset_other by lia; rewrite (EEx 20%nat 20%bv eq_refl), (RG4 20%bv ltac:(cbv; tauto)); exact R20).
  assert (Ex21 : ew (ewset (ewset E4 512 w) 513 w0) 21 = Z_to_bv 64 (ev_len cx m))
    by (rewrite !ew_ewset_other by lia; rewrite (EEx 21%nat 21%bv eq_refl), (RG4 21%bv ltac:(cbv; tauto)); exact R21).
  assert (Hk2 : 0 <= ev_k2 cx m <= c_n cx) by (clear - CU1 CU2 CU3 Hk; unfold ev_k2; lia).
  assert (HUS : U (ewset (ewset E4 512 w) 513 w0) (SAlu ALU_ADD (SOff 20 0) (SMd M_MUL (SOff 21 0) (SLit (-1))))
      = c_n cx - ev_k2 cx m).
  { rewrite U_SAlu, U_SMd.
    rewrite (U_atom _ 20 _ Ex20) by (clear - CU1 CU2 CU3 Hk Hn26; lia).
    rewrite (U_atom _ 21 _ Ex21) by (clear - CU1 CU2 CU3 Hk Hn26; lia).
    assert (Hm1 : U (ewset (ewset E4 512 w) 513 w0) (SLit (-1)) = 2 ^ 64 - 1)
      by (unfold U; cbn [sv_denot]; rewrite Z_to_bv_unsigned; reflexivity).
    rewrite Hm1. unfold zcanon, zalu_raw, zmd_raw, M64. rewrite Z.add_mod_idemp_r by lia.
    replace (c_n cx - ev_k1 cx m + ev_len cx m * (2 ^ 64 - 1)) with ((c_n cx - ev_k2 cx m) + ev_len cx m * 2 ^ 64)
      by (unfold ev_k2; ring).
    rewrite Z.mod_add by lia. apply Z.mod_small. clear - Hk2 Hn26. lia. }
  assert (VSLOT : val_mem segs (mrestrict (w_H W3) (ms_mem ms2)) (lf_F cx + 144) (N.to_nat 8) (c_n cx - ev_k2 cx m)).
  { eapply (field_of_region _ _ 9 (lf_F cx)); [exact RSLOT | exact Ux9' | cbn [In]; left; reflexivity | | | lia].
    - apply ev_sv_of_U; [exact HUS | clear - Hk2 Hn26; lia].
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Hk2 Hn26. lia. }
  (* ---- the cut at the latch: the blocks after free, the bytes kept from the cut and from relay_event's post ---- *)
  destruct (ERRL ly7 S7 [] W7 mem7 _ HAR10) as ((v & Hv & Hvr) & Hw).
  assert (ROMf : rom_view segs W7 mem7)
    by (eapply ajournal_gx_rom_view0R; first [exact HJ7 | exact ET_ROM_OUT | exact HROM0 | exact LAWS | exact pa_segs_low]).
  assert (Hrm : forall b, In b (ablocks B ly5 S5) -> b <> (q, slen + 1) -> In b (ablocks B ly7 S7)).
  { intros b Hb Hne. rewrite Hbl5 in Hb. rewrite Hbl7. apply in_app_or in Hb as [Hb | [Hb | Hb]];
      [apply in_or_app; left; exact Hb | exfalso; exact (Hne (eq_sym Hb)) | apply in_or_app; right; exact Hb]. }
  assert (HBL7 : forall b, In b ((c_p cx, c_n cx) :: et_rest_blks m) -> In b (ablocks B ly7 S7)).
  { intros [b n] Hb. apply (Hrm _ (HBL5 _ Hb)). intros Eq. injection Eq as -> ->.
    assert (Hb3 : In (q, slen + 1) (ablocks B ly3 S3)).
    { apply HBLK. unfold et_blks. destruct Hb as [Hb | Hb]; [left; exact Hb|].
      right. rewrite et_model_blks. apply in_or_app. left. exact Hb. }
    destruct (HQB q (slen + 1) Hb3) as [Hd | Hd]; try rewrite Hreqq in Hd; clear - Hd Hslenr; lia. }
  assert (HBO7 : forall b, In b (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') -> In b (ablocks B ly7 S7)).
  { intros [b n] Hb. apply (Hrm _ (HBO5 _ Hb)). intros Eq. injection Eq as -> ->.
    destruct (HOQ q (slen + 1) Hb) as [Hd | Hd]; try rewrite Hreqq in Hd; clear - Hd Hslenr; lia. }
  assert (KG : forall a, inG et_GLr a -> aview segs (w_H W7) mem7 a = aview segs (w_H W) mem a).
  { intros a Ha. assert (Ha' : inG (et_GLr ++ et_GO) a) by (unfold inG; apply Exists_app; left; exact Ha).
    rewrite (KF7 a (or_introl Ha')), (KC7 a (or_introl Ha')), (KR6 a (or_introl Ha)).
    apply KV5. left. exact (et_GLr_GL a Ha). }
  assert (KBk : forall b n a, In (b, n) ((c_p cx, c_n cx) :: et_rest_blks m) -> b <= a < b + req_size n ->
      aview segs (w_H W7) mem7 a = aview segs (w_H W) mem a).
  { intros b n a Hb Ha.
    rewrite (KF7 a ltac:(right; left; exists b, n; split; [apply in_or_app; left; exact Hb | exact Ha])).
    rewrite (KC7 a ltac:(right; left; exists b, n; split; [right; apply in_or_app; left; exact Hb | exact Ha])).
    rewrite (KR6 a ltac:(right; left; exists b, n; split; [right; exact Hb | exact Ha])).
    apply KV5. right. right. left. exists b, n. split; [|exact Ha]. unfold et_blks.
    destruct Hb as [Hb | Hb]; [left; exact Hb|]. right. rewrite et_model_blks. apply in_or_app. left. exact Hb. }
  assert (KGO : forall a, inG et_GO a -> aview segs (w_H W7) mem7 a = aview segs (w_H W5) mem5 a).
  { intros a Ha. assert (Ha' : inG (et_GLr ++ et_GO) a) by (unfold inG; apply Exists_app; right; exact Ha).
    rewrite (KF7 a (or_introl Ha')). exact (KC7 a (or_introl Ha')). }
  assert (KBO : forall b n a, In (b, n) (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') -> b <= a < b + req_size n ->
      aview segs (w_H W7) mem7 a = aview segs (w_H W5) mem5 a).
  { intros b n a Hb Ha.
    rewrite (KF7 a ltac:(right; left; exists b, n; split; [apply in_or_app; right; exact Hb | exact Ha])).
    exact (KC7 a ltac:(right; left; exists b, n; split; [right; apply in_or_app; right; exact Hb | exact Ha])). }
  (* the model after the operation: the cut's slots, table and flags, relay_event's stream with errno v *)
  assert (HPRB : forall b n a, In (b, n) (ablocks B ly7 S7) -> b <= a < b + req_size n -> apresent (w_H W7) mem7 a).
  { intros b n a Hb Ha. destruct (al0_blocks ly7 S7 W7 mem7 _ b n HAR10 Hb) as (_ & _ & _ & _ & Hp & _).
    exact (proj1 (Hp a Ha)). }
  assert (HAO6' := HAO6). rewrite <- O25 in HAO6'.
  assert (HMODf : amodel_at B ly7 S7 W7 mem7 (ev_step cx m (ev_line cx m slen) v out')).
  { apply (et_model_kept ly3 S3 W mem ly7 S7 W7 mem7 m (ev_k2 cx m) _ _ _ out' HMOD).
    - intros x Hx. exact (et_kept_G W W7 mem mem7 x (et_GLr_G x Hx) (KG x Hx)).
    - intros b n i Hb Hi. apply et_kept_apres; [exact (KBk b n (b + i) (or_intror Hb) ltac:(lia))|].
      exact (HPRB b n (b + i) (HBL7 _ (or_intror Hb)) ltac:(lia)).
    - intros b Hb. exact (HBL7 _ (or_intror Hb)).
    - apply (et_aout_errno_x ly5 S5 W5 mem5 _ ly7 S7 W7 mem7 _ _ _ _ _ _ v HAR8 HAO6').
      + intros x Hx. exact (et_kept_G W5 W7 mem5 mem7 x (HG_carry x (et_GO_GL x Hx)) (KGO x Hx)).
      + intros b n i Hb Hi.
        destruct (al0_blocks ly7 S7 W7 mem7 _ b n HAR10 (HBO7 _ Hb)) as (_ & _ & _ & _ & _ & _ & Hn).
        pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
        apply et_kept_apres; [exact (KBO b n (b + i) Hb ltac:(lia))|].
        exact (HPRB b n (b + i) (HBO7 _ Hb) ltac:(lia)).
      + exact HBO7.
      + exact Hv.
      + exact Hw.
      + exact Hvr.
    - apply (alock_at_kept fr_RG W5 mem5 W7 mem7 false HLK6). intros r [<- | []] a Ha.
      assert (Ha' : inG et_GO a) by (cbn [fst snd] in Ha; clear - Ha; unfold et_GO; et_inG).
      exact (et_kept_G W5 W7 mem5 mem7 a (HG_carry a (et_GO_GL a Ha')) (KGO a Ha')). }
  assert (HINf : ainput_at B cx ly7 S7 W7 mem7).
  { apply (et_input_kept cx ly3 S3 W mem ly7 S7 W7 mem7 HIN (eq_sym HlenP)).
    - intros i Hi. apply et_kept_apres.
      + apply (KBk (c_p cx) (c_n cx) (c_p cx + i) (or_introl eq_refl)). rewrite Hreqp. lia.
      + apply (HPRB (c_p cx) (c_n cx) (c_p cx + i) (HBL7 _ (or_introl eq_refl))). rewrite Hreqp. lia.
    - intros _. exact (HBL7 _ (or_introl eq_refl)). }
  (* the live blocks after the operation: the cut's, with g_out's block as relay_event left it and q freed *)
  assert (Hinp : input_blks cx = [(c_p cx, c_n cx)])
    by (unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); reflexivity).
  assert (Hm' : model_blks (ev_step cx m (ev_line cx m slen) v out') = et_rest_blks m ++ aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out')
    by (rewrite et_model_blks; reflexivity).
  assert (HP3' : Permutation (ablocks B ly3 S3)
      (aout_blks (lm_cap m) (lm_out m) ++ (c_p cx, c_n cx) :: et_rest_blks m ++ rest0)).
  { pose proof HP3 as HP3c. rewrite Hinp, et_model_blks in HP3c.
    eapply perm_trans; [exact HP3c|]. cbn [app].
    eapply perm_trans; [|apply Permutation_middle]. apply perm_skip.
    rewrite <- (app_assoc (et_rest_blks m) (aout_blks (lm_cap m) (lm_out m)) rest0).
    rewrite (app_assoc (et_rest_blks m) (aout_blks (lm_cap m) (lm_out m)) rest0).
    rewrite (app_assoc (aout_blks (lm_cap m) (lm_out m)) (et_rest_blks m) rest0).
    apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (PR : Permutation restR (((c_p cx, c_n cx) :: et_rest_blks m ++ rest0) ++ [(q, slen + 1)])).
  { apply (Permutation_app_inv_l (aout_blks (lm_cap m) (lm_out m))).
    eapply perm_trans; [apply Permutation_sym; exact HPR4|].
    rewrite Hblq.
    rewrite (app_assoc (aout_blks (lm_cap m) (lm_out m)) ((c_p cx, c_n cx) :: et_rest_blks m ++ rest0) [(q, slen + 1)]).
    apply Permutation_app_tail. exact HP3'. }
  assert (P5 : Permutation (ablocks B ly5 S5)
      (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out' ++ ((c_p cx, c_n cx) :: et_rest_blks m ++ rest0) ++ [(q, slen + 1)]))
    by (eapply perm_trans; [exact HPR5b | apply Permutation_app_head; exact PR]).
  assert (P7 : Permutation (ablocks B ly7 S7) (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out' ++ (c_p cx, c_n cx) :: et_rest_blks m ++ rest0)).
  { rewrite Hbl7. rewrite Hbl5 in P5.
    apply (Permutation_cons_inv (a := (q, slen + 1))).
    eapply perm_trans; [apply Permutation_middle|].
    eapply perm_trans; [exact P5|].
    rewrite (app_assoc (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') ((c_p cx, c_n cx) :: et_rest_blks m ++ rest0) [(q, slen + 1)]).
    apply Permutation_sym, Permutation_cons_append. }
  assert (HSEPf : ablocks_sep B fr_FP cx (ev_step cx m (ev_line cx m slen) v out') ly7 S7).
  { split.
    - exists rest0. rewrite Hinp, Hm'. cbn [app].
      eapply perm_trans; [exact P7|].
      eapply perm_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
      rewrite (app_assoc (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len (ev_line cx m slen))) out') (et_rest_blks m) rest0).
      apply Permutation_app_tail, Permutation_app_comm.
    - intros b Hb. rewrite Hm' in Hb. apply in_app_or in Hb as [Hb | Hb].
      + apply HSEP2. rewrite et_model_blks. apply in_or_app. left. exact Hb.
      + destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B ly4 S4))
          as [Hin4b | Hnin4b].
        * apply (Permutation_in _ HPR4) in Hin4b. apply in_app_or in Hin4b as [Ho | Hr].
          -- apply HSEP2. rewrite et_model_blks. apply in_or_app. right. exact Ho.
          -- exfalso. pose proof (Permutation_NoDup HPR5b (et_nodup_x ly5 S5 W5 mem5 _ HAR8)) as ND5.
             apply YG04.NoDup_app_iff in ND5 as (_ & _ & HD5). exact (HD5 b Hb Hr).
        * destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B (c_ly cx) (c_S cx)))
            as [Hine | Hnine]; [right | left; exact Hnine].
          destruct b as [o c]. intros a Ha. cbn [fst snd] in Ha.
          pose proof HJi6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
          destruct (al0_blocks ly5 S5 W5 mem5 _ o c HAR8 (HBO5 _ Hb)) as (_ & _ & _ & _ & _ & _ & Hc0).
          pose proof (req_size_pos c ltac:(lia)) as (_ & Hrq).
          replace a with (o + (a - o)) by lia. apply (Hgone o c (a - o) Hine Hnin4b). lia. }
  (* ---- INV_K (t + 1 operations): the model step, the registers the latch reads ---- *)
  (* s5-r1d's text: the three states are tied to the calls' posts - S4 by the malloc rule's ablocks equation, S4 / S5
     by relay_event's aout Permutations, S7 by the free's split *)
  pose proof (LS_event_step cx t m ly3 S3 S4 S5 S7 ly7 (ev_line cx m slen) v out' ly4 ly5 q HLS HEVT
    ltac:(rewrite Hrelen; exact Hmleq) HMLE5 HMLE7 Hk HO Hcap0
    ltac:(rewrite Hrelen; exact Hblq) (ex_intro _ restR (conj HPR4 HPR5b))
    ltac:(rewrite Hrelen; exact (ex_intro _ l1 (ex_intro _ l2 (conj Hbl5 Hbl7)))) Ht) as LSf.
  pose proof (RI_event_step cx t m (ev_line cx m slen) v out' HRI Hk HO Hop7 HEVT Hvr) as RIf.
  assert (SV144 : sv8 W7 mem7 (lf_F cx + 144) (c_n cx - ev_k2 cx m)).
  { unfold sv8. apply (akept_vm W3 (ms_mem ms2)); [|exact VSLOT].
    intros x Hx. cbn in Hx. apply et_kept_apres; [apply KFR; left; lia|].
    apply HPRES9. unfold LLVMF_STK. lia. }
  apply (SRrG_ret segs R R_refl).
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact (et_jt_of_rom W7 mem7 ROMf)|].
  exists [(1, fpos)], ly7, S7, [], (k + 1 + k5 + 1), (ev_step cx m (ev_line cx m slen) v out'), fpos.
  split; [exact HJ7|]. split; [reflexivity|].
  rewrite HFFeq7.
  split; [exact HFR7|]. split; [exact HFL7|]. split; [exact HMODf|]. split; [exact HINf|]. split; [exact ROMf|].
  split; [exact HSEPf|]. split; [exact LSf|]. split; [apply RP_NP in HRM7; exact HRM7|]. split; [exact RIf|].
  unfold lregs_K, lregs_common. cbn [ev_step lm_k].
  split.
  { split; [rewrite (KR8 2%bv ltac:(cbv; tauto)), (R57 2%bv ltac:(cbv; tauto)); exact W5_2|].
    split; [rewrite (KR8 8%bv ltac:(cbv; tauto)), (R57 8%bv ltac:(cbv; tauto)); exact W5_8|].
    split; [rewrite (KR8 9%bv ltac:(cbv; tauto)), (R57 9%bv ltac:(cbv; tauto)); exact W5_9|].
    split; [rewrite (KR8 18%bv ltac:(cbv; tauto)), (R57 18%bv ltac:(cbv; tauto)); exact W5_18|].
    split; [rewrite (KR8 19%bv ltac:(cbv; tauto)), (R57 19%bv ltac:(cbv; tauto)); exact W5_19|].
    split; [rewrite Z20; reflexivity|].
    split; [rewrite Z23; reflexivity|].
    split; [rewrite (KR8 24%bv ltac:(cbv; tauto)), (R57 24%bv ltac:(cbv; tauto)); exact W5_24|].
    split; [rewrite Z25; reflexivity|].
    split; [rewrite (KR8 26%bv ltac:(cbv; tauto)), (R57 26%bv ltac:(cbv; tauto)); exact W5_26|].
    split; [rewrite (KR8 3%bv ltac:(cbv; tauto)), (R57 3%bv ltac:(cbv; tauto)); exact W5_3|].
    rewrite (KR8 4%bv ltac:(cbv; tauto)), (R57 4%bv ltac:(cbv; tauto)); exact W5_4. }
  split; [rewrite (KR8 27%bv ltac:(cbv; tauto)), (R57 27%bv ltac:(cbv; tauto)); exact W5_27|].
  split; [exact Ht|].
  split; [rewrite (KR8 22%bv ltac:(cbv; tauto)), (R57 22%bv ltac:(cbv; tauto)); exact W5_22|].
  split; [exact SV144 | exact Hk2].
Qed.

(* the arm at R: cut_x Section wR's ARM_event_R (W_LLVMFuzzerTestOneInput_cut_x.v:463), lf_base_x / INV_A_xR / INV_K_xR *)
Theorem lf_arm_event_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 7 cx Hp t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  (* the entry's ghost list is empty (HP0 on the pre's ARx): the walk runs at [] *)
  pose proof HB as (_ & HPRE). hp0a (proj1 (proj1 HPRE)).
  eapply (SRrG_bind segs R R_trans); [exact (ev_to_P1_xR cx t W c HB HA)|].
  intros W1 c1 _ HP. exact (ev_tail_xR cx t W1 c1 HB HP).
Qed.
End evxR.

(* ---------------------------------------------------------------- the strict lemmas at R := wle
   Part 3c took memnorm out of the allocator rules at R, so every strict lemma that has an R twin above is that twin
   at R := wle (R_refl / R_trans / WLE_R by wle_refl / wle_trans / the identity), RO := fun _ => True (RO_ARx holds
   trivially), AMALLOC_R / AFREE_R from the strict rules by W_journal_x's amalloc_cf_rule_c_xR_of_x /
   afree_cf_rule_c_xR_of_x, and RE_R the strict RE (W_contract_xR.v re_spec_x_wle: re_spec_xR at wle IS re_spec_x).
   The statements are the strict ones unchanged; at wle the R texts are the strict texts by conversion
   (ajournal_x_wle, ajournal_gx_x_wle, SRrG at wle is SRr, cut_x Section wR at wle is Section w). *)
(* YCbq.v:2730 aftok_new_block at AJi0 / AR0: ev_aftok_new_block0R at wle *)
Lemma ev_aftok_new_block0 : forall STK sp0 FP ly S W0 mem md own lyc Sc (W : world segs) memc mdc k ly2 S2
    (W2 : world segs) mem2 md2 res n,
  AJi0 STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  AR0 ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> 0 <= n ->
  aftok FP (ablocks B ly S) (res, n).
Proof. exact (ev_aftok_new_block0R (@wle segs)). Qed.
(* W_journal.v:399 ajournal_gx_rom_view at AJ0: ajournal_gx_rom_view0R at wle *)
Lemma ajournal_gx_rom_view0 : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_out segs B G -> rom_view segs W mem -> rom_view segs W' mem'.
Proof. exact (ajournal_gx_rom_view0R (@wle segs)). Qed.
(* the cut ev_P1 at the strnlen call, from the entry's lcut: ev_P1_of_xR at wle *)
Lemma ev_P1_of_x : forall cx t W (regsD regs regs' : bvmap 5 word) mem md' own ly3 S3 k m fpos,
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) own ly3 S3 W mem md' k ->
  own = [(1, fpos)] -> aframe_at cx true (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 ->
  NP S3 -> RINV cx t m ->
  (forall r, In r EV_KEPT -> getr regs' r = getr regs r) ->
  (forall r, In r jt_kept -> getr regs r = getr regsD r) ->
  lregs_common B cx (frame_addr ly3 1 fpos) regsD -> getr regsD 27 = w64 t -> 0 <= t < OPS_MAX ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  getr regs' 10 = w64 (ev_parg cx m) -> getr regs' 11 = w64 (ev_len cx m) -> getr regs' 22 = w64 (ev_parg cx m) ->
  getr regs' 20 = w64 (c_n cx - ev_k1 cx m) -> getr regs' 21 = w64 (ev_len cx m) ->
  ev_P1_x cx t W (cfg_at segs (fr_B0 + AF_ev_call_strnlen) regs' mem md').
Proof. exact (ev_P1_of_xR (@wle segs)). Qed.
(* the arm entry's straight run to the strnlen call: ev_to_P1_xR at wle *)
Lemma ev_to_P1_x : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 7 cx [] t W c -> SRr segs W c (ev_P1_x cx t).
Proof. exact (ev_to_P1_xR (@wle segs) (fun W W' H => H)). Qed.
(* a callee's afn_pre at sp = F (W_LLVMFuzzerTestOneInput_latch.v lt_afn_pre_at): et_afn_pre_at_xR at wle *)
Lemma et_afn_pre_at_x : forall cx full ly3 S3 fpos k0 (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k0 ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch /\ (spine ch = [] \/ spine ch = [RA_LLVMF]).
Proof. exact (et_afn_pre_at_xR (@wle segs)). Qed.
(* what a callee's journal at G (no out-parameter) keeps: high bytes outside its window, the bytes of a block live
   before and after outside its footprint, the image bytes outside G, the statics, errno and the sink head, and a
   frame live before outside its footprint: et_gx_keep_xR at wle *)
Lemma et_gx_keep_x : forall G STK sp0 FP ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' k a,
  AJ0 G 0 [] STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k ->
  0 <= a < 2 ^ 64 -> ~ inG G a ->
  ((alloc_ceiling <= a /\ ~ (sp0 - STK <= a < sp0)) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. exact (et_gx_keep_xR (@wle segs)). Qed.
(* across a callee's journal at G whose window lies below F: et_cr_gx_xR at wle *)
Lemma et_cr_gx_x : forall cx FF Gs bl G STK FP ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' k pos,
  gx_ok segs B G ->
  AJ0 G 0 [] STK (lf_F cx) FP ly S W mem md [] ly' S' W' mem' md' k ->
  AR0 ly S W mem md -> In (1, pos) (frames S) -> FF = frame_addr ly 1 pos ->
  (forall a, inG Gs a -> inG G_fr a /\ ~ inG G a /\ ~ (as_errno B <= a < as_errno B + 4) /\ fp_spares FP a) ->
  (forall b n, In (b, n) bl -> In (b, n) (ablocks B ly S) /\ In (b, n) (ablocks B ly' S') /\
     (forall a, b <= a < b + req_size n -> ~ inFP FP a)) ->
  (forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) -> ~ inFP FP a) ->
  0 <= STK <= 32000 -> alloc_ceiling + 32000 <= lf_F cx -> spZ (c_regs cx) <= 2 ^ 47 ->
  forall a, et_cr cx FF Gs bl a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. exact (et_cr_gx_xR (@wle segs)). Qed.
(* the tail from the strnlen call to the latch: ev_tail_xR at wle *)
Lemma ev_tail_x : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ev_P1_x cx t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t).
Proof.
  exact (ev_tail_xR (@wle segs) (wle_refl segs) (wle_trans segs) (fun W W' H => H) (fun _ => True)
    (fun _ _ _ _ _ _ _ => I) ltac:(apply amalloc_cf_rule_c_xR_of_x; exact AMALLOC)
    ltac:(apply afree_cf_rule_c_xR_of_x; exact AFREE) RE).
Qed.
(* the arm (cut_x Section w's ARM_event): lf_arm_event_xR at wle *)
Theorem lf_arm_event_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 7 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  exact (lf_arm_event_xR (@wle segs) (wle_refl segs) (wle_trans segs) (fun W W' H => H) (fun _ => True)
    (fun _ _ _ _ _ _ _ => I) ltac:(apply amalloc_cf_rule_c_xR_of_x; exact AMALLOC)
    ltac:(apply afree_cf_rule_c_xR_of_x; exact AFREE) RE).
Qed.
End evx.

(* ---------------------------------------------------------------- THE CHECK
   In cut_x's scope (its Section w header and this piece's hypotheses): lf_arm_event_x's type is cut_x's Section w
   hypothesis ARM_event (W_LLVMFuzzerTestOneInput_cut_x.v:559), restated and closed by `exact`, and it fills that slot
   of cut_x's composition lf_contract_of_segments_x. *)
Section chk.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:192-235) *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
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
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling, W_journal_x at 0c4d57d9bf1;
   fuzz_reply calls no poison routine): the driver reads the post's Hp' = [] from the journal's ARx through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* ---------------------------------------------------------------- the event arm's own hypotheses *)
(* the request bound of the allocator's live-state rules (W_journal.v:697, the instance's cf_malloc_max) *)
Variable MMAX : Z.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (a), (d)): the allocator rules' and relay_event's room record RP, at
   RM := the cut's NP (the cf instance: rp_RM := fun S _ => room_live_cf S = NP, so RP_NP is iff_refl) *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* the allocator instance, W_kit.v:356 PALib @ 5180fc7d18d: SIGMA WS_malloc / WS_free are its wrappers *)
Hypothesis TL : PALib B.
(* _cut.v's two shared facts (W_LLVMFuzzerTestOneInput_cut.v:309 glob_wr_law, :214 errno_law; _G.v c_glob_wr proves the
   first for G_fr_c) *)
Hypothesis GWR : glob_wr_law G_fr.
(* _cut.v's errno_law over ARx: cut_x's errno_law_x *)
Hypothesis ERRL : errno_law_x B ARx.
(* .rodata is outside G_fr, the allocator's statics, errno and the sink's overflow head: W_journal.v:376 rom_out, the
   text W_xrf.v:191 XRF_ROM_OUT takes (_G.v c_rom_apart proves its G_fr conjunct) *)
Hypothesis ET_ROM_OUT : rom_out segs B G_fr.
(* G_fr facts, proved for G_fr_c in W_LLVMFuzzerTestOneInput_G.v: the lock and send_line's G (c_HGlock, c_HG_SL) *)
Hypothesis HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
(* G_fr facts, proved for G_fr_c in W_LLVMFuzzerTestOneInput_G.v (c_HG_carry, c_HERR_AP): those globals are in G_fr,
   and apart from errno's cell *)
Hypothesis HG_carry : forall a, inG et_GL a -> inG G_fr a.
Hypothesis HERR_AP : forall a, inG et_GL a -> ~ (as_errno B <= a < as_errno B + 4).
(* ---- _event.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation et_GRE := (W_LLVMFuzzerTestOneInput_event.et_GRE B).
Local Notation ev_byte := (W_LLVMFuzzerTestOneInput_event.ev_byte B).
Local Notation lregs_P1 := (W_LLVMFuzzerTestOneInput_event.lregs_P1 B).
Local Notation et_kept_G := (W_LLVMFuzzerTestOneInput_event.et_kept_G G_fr GWR).
Local Notation et_GLr_GL := (W_LLVMFuzzerTestOneInput_event.et_GLr_GL XM_LIB XN_LIB RLO).
Local Notation et_GLr_G := (W_LLVMFuzzerTestOneInput_event.et_GLr_G XM_LIB XN_LIB RLO G_fr HG_carry).
Local Notation et_lock_GL := (W_LLVMFuzzerTestOneInput_event.et_lock_GL XM_LIB XN_LIB RLO).
Local Notation et_errno_G := (W_LLVMFuzzerTestOneInput_event.et_errno_G B XM_LIB XN_LIB RLO G_fr HG_SL).
Local Notation et_alist := (W_LLVMFuzzerTestOneInput_event.et_alist B).
Local Notation et_asrc := (W_LLVMFuzzerTestOneInput_event.et_asrc B).
Local Notation et_aentry := (W_LLVMFuzzerTestOneInput_event.et_aentry B).
Local Notation et_arelay := (W_LLVMFuzzerTestOneInput_event.et_arelay B).
Local Notation et_model_kept := (W_LLVMFuzzerTestOneInput_event.et_model_kept B).
Local Notation et_input_kept := (W_LLVMFuzzerTestOneInput_event.et_input_kept B).
Local Notation ev_aview_in := (W_LLVMFuzzerTestOneInput_event.ev_aview_in B).
Local Notation ev_evt_of := (W_LLVMFuzzerTestOneInput_event.ev_evt_of B).
Local Notation et_carry := (W_LLVMFuzzerTestOneInput_event.et_carry B).
Local Notation et_carry_out := (W_LLVMFuzzerTestOneInput_event.et_carry_out B).
Local Notation et_GO_GL := (W_LLVMFuzzerTestOneInput_event.et_GO_GL XM_LIB XN_LIB RLO).
(* ---- the tail's callees at their kit forms ---- *)
(* malloc (0x84acc) and free (0x84b1c): W_journal_x.v's caller-context rules, each at its own K0 table (lib/A/ACk0.v) *)
Hypothesis AMALLOC : amalloc_cf_rule_c_x segs B PST ARx MT MMAX RP CTX_AMALLOC.
Hypothesis AFREE : afree_cf_rule_c_x segs B PST ARx MT RP CTX_AFREE.
(* __asan_memcpy (0x84ae0): W_sites_x.v:126 aintrin_realizes_x *)
Hypothesis AMEMCPY : aintrin_realizes_x segs B ARx OCpy (SIGMA WS_asan_memcpy).
(* strnlen (0x84ac0). OWED (kit has no twin): _event.v:79 et_strnlen_spec (the StrnlenDef text, at lo / hi =
   0x10350 / 0x10370) in the kit's form - ecall_pre -> FCiface.ecall_pre_x, AR -> ARx, Hp after S, the post's ARx at
   the pre's Hp (as W_sites_x.aintrin_realizes_x) *)
Hypothesis ASTRNLEN : et_strnlen_spec_x B ARx 0x10350 0x10370 (SIGMA WS_strnlen).
(* relay_event (0x84b0c): W_contract_x.v:810 re_spec_x at relay_event's own G (_event.v's et_GRE) *)
Hypothesis RE : re_spec_x (PI := PB_fr) B PST ARx MT RP MMAX et_GRE fr_RG (BASE + AF_fr_relay_event).
(* check_shape_event (0x84b14): W_contract_x.v:539 cse_spec_x *)
Hypothesis CSE : cse_spec_x (PI := PB_fr) B PST ARx (BASE + AF_fr_check_shape_event).
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct). The text is W_kit_x.v:45's BLKN (add_x's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): a callee's journal keeps every image byte outside its own G *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.

(* ---- the arm's open model obligations (pure, over lmod and the plain records) ---- *)
(* the projection of the plain invariant's gone clause (Prog/SlotInv.v globals_at): it gives check_shape_event's
   `(gone = 1 /\ O = 0) \/ (gone = 0 /\ ob = e ++ [0])` through send_line's live test *)
Hypothesis RI_event_live : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).
(* the operation relayed the event line e; errno is v and the stream's block is out' *)
Hypothesis RI_event_step : forall cx t m e v out',
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  RINV cx (t + 1) (ev_step cx m e v out').
(* ---- the allocator-state facts the three calls take, read off LSx; the instance discharges them ---- *)
Hypothesis LS_event_malloc : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  re_len e < MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e)).
Hypothesis LS_event_relay : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Hypothesis LS_event_free : forall cx t m ly S (S1 S2 : astate) e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).
(* s5-r1d's text (fr_LS3c_event_step_p, commit 6d19e580568, lib/A/ReplyLS3cArms.v:91), LS -> LSx: the three states
   are tied to the calls' posts - S1 by the malloc rule's ablocks equation, S1 / S2 by relay_event's (send_line's)
   aout Permutations, S3 by the free's split with the event's block removed *)
Hypothesis LS_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (ev_step cx m e v out') ly3 S3.
(* the live counts at the arm's entry leave room for its peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2; the row
   fr_LS3cp_cnt_event, commit ba8e99b5bd2, lib/A/ReplyLScnt.v:265, with its peak pk_event e P = [P (re_len e)] + 2 and
   its guards, msz_ok inline): malloc (re_len e) at the entry's counts, relay_event's count premise (re_pk = 2) at the
   entry's blocks plus the event's, free at relay_event's post (g_out replaced: at most one block more).  Stated over
   the room record's count fields; at the cf instance they are ReplyCnt's Psec / P24 / Lsec / L24 / Pcls / LPRIM *)
Hypothesis LS_cnt : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  Forall (fun e0 => 0 <= re_cap e0 <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e0)) (lm_es m) /\
  Forall (fun o => match o with
                   | Some h => Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_expected h)) /\
                               Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_held h))
                   | None => True end) (lm_hs m) ->
  0 <= t < OPS_MAX ->
  (ReplyCnt.acnt (rp_Psec RP) (ablocks B ly S) + ((if rp_Psec RP (re_len e) then 1 else 0) + 2) <= rp_Lsec RP)%nat /\
  (ReplyCnt.acnt (rp_P24 RP) (ablocks B ly S) + ((if rp_P24 RP (re_len e) then 1 else 0) + 2) <= rp_L24 RP)%nat /\
  (forall c, 1 <= c <= 30 ->
     (ReplyCnt.acnt (rp_Pcls RP c) (ablocks B ly S) + ((if rp_Pcls RP c (re_len e) then 1 else 0) + 2)
        <= rp_LPRIM RP c)%nat).

(* ---- the arithmetic of the cursor ---- *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IA := (INV_A_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IK := (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV).
Lemma ARM_event_check : forall cx Hp t W c, BASEx cx Hp -> IA 7 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Proof.
  exact (lf_arm_event_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS
    HP0 HG LSx RINV MMAX RP RP_NP TL GWR ERRL ET_ROM_OUT HGlock HG_SL HG_carry HERR_AP AMALLOC AFREE AMEMCPY ASTRNLEN
    RE CSE BLKN HPST RI_event_live RI_event_step LS_event_malloc LS_event_relay LS_event_free LS_event_step LS_cnt).
Qed.
Definition event_x_slot :=
  fun SEG_PRO SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_remove ARM_gone ARM_eintr ARM_sendmax ARM_default
    SEG_LATCH SEG_EXIT =>
  lf_contract_of_segments_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV SEG_PRO SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_remove ARM_gone ARM_eintr
    ARM_event_check ARM_sendmax ARM_default SEG_LATCH SEG_EXIT.
(* route R: lf_arm_event_xR's type is cut_x's Section wR hypothesis ARM_event_R (W_LLVMFuzzerTestOneInput_cut_x.v:463),
   restated and closed by `exact`, and it fills that slot of cut_x's composition lf_contract_of_segments_xR.  The twin's
   arguments: the strict lemma's, without its AMALLOC / AFREE / RE, then R R_refl R_trans WLE_R RO RO_ARx
   AMALLOC_R AFREE_R RE_R. *)
Section chkR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AMALLOC_R : amalloc_cf_rule_c_xR segs B PST ARx MT MMAX RP RO CTX_AMALLOC R.
Hypothesis AFREE_R : afree_cf_rule_c_xR segs B PST ARx MT RP RO CTX_AFREE R.
Hypothesis RE_R : re_spec_xR (PI := PB_fr) B PST ARx R MT RP MMAX et_GRE fr_RG (BASE + AF_fr_relay_event).
Local Notation IAR := (INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation IKR := (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Lemma ARM_event_R_check : forall cx Hp t W c, BASEx cx Hp -> IAR 7 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Proof.
  exact (lf_arm_event_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS
    HP0 HG LSx RINV MMAX RP RP_NP TL GWR ERRL ET_ROM_OUT HGlock HG_SL HG_carry HERR_AP AMEMCPY ASTRNLEN
    CSE BLKN HPST RI_event_live RI_event_step LS_event_malloc LS_event_relay LS_event_free LS_event_step LS_cnt
    R R_refl R_trans WLE_R RO RO_ARx AMALLOC_R AFREE_R RE_R).
Qed.
Definition event_xR_slot :=
  fun SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R ARM_remove_R ARM_gone_R ARM_eintr_R
    ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R =>
  lf_contract_of_segments_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV R R_refl R_trans WLE_R SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R
    ARM_remove_R ARM_gone_R ARM_eintr_R ARM_event_R_check ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R.
End chkR.
End chk.
