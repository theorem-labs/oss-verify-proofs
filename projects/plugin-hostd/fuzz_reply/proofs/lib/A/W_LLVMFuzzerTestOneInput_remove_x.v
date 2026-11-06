(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_remove (lib/A/W_LLVMFuzzerTestOneInput_remove.v lf_arm_remove),
   the jump table's arm 4 of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput (op_remove, fuzz_reply.c:619-631:
   the inlined relay_source search, relay_remove, check_no_loss_read when the entry was open, check_no_loss,
   check_shape_ends, check_shape_done, source_reset, back to the latch), a Theorem Labs lane's route (b), step 7.
   - The AR proof is a Theorem Labs lane's: a working branch 30d91cacb63 (lf_arm_remove Qed on base ebe8aee727b,
     fresh rc=0 wall 826, remove.vo real 182.87 s, Print Assumptions 13 Prim* + funext), adapted to the current cut and
     kit on a working branch ddbe0ec6590 (statement unchanged).  The AR file is NOT edited here;
     this file Requires it and cites every AR-free definition and lemma of it (the arm's addresses, sstates, model
     records and rules, register / frame-byte / permutation / keep lemmas); each lemma of it that reads AR, AR_laws, an
     AR journal, afn_pre, lf_base, an INV_* or RCUT, errno_law, ashp or gx_prog is restated here over ARx as NAME_x,
     with its proof converted.
   - THE AR0 LAYER: HP0 forces the ghost list of every ARx state to [] (the entry's by lf_base_x, the cut's by its
     journal, each callee's post by its journal), so the converted lemmas are stated over AR0 := ARx at [] and the
     journals AJ0 / AJI0 := W_journal_x's ajournal_gx_x / YCbqG's ajournal_x at [] (Local Notations), and the AR
     journal / law lemmas they cite become one-line wrappers of the kit's _x lemmas with the AR argument layout
     (ajournal_gx_AR0 .. al_blocks_0).  Each callee spec is the kit's _x form taken at Hp := []; its post's Hp' is []
     by HP0.
   - The Section header is cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235), so lf_arm_remove_x's
     statement is cut_x's ARM_remove hypothesis (cut_x.v:306) at that Section's variables (checked at the end).
   - Section hypotheses: the AR file's, over ARx where they name AR (callee specs in their kit _x forms, errno_law_x,
     gx_prog_x), the model rules verbatim (LS is cut_x's LSx), and those the generic relation and PST force: BLKN30
     (a live block's request size is in [0, 2^30): AR_blocks_law's last conjunct at a bound true at the cf instance,
     AR_blocks_law_cf's cf_malloc_max <= 2^30; ARx_blocks_law has no size conjunct), PST_ROM / PST_IMG (the ROM bytes,
     and the image bytes outside the allocator's owned statics, lie outside PST: W_journal_x's image clause and
     ajournal_gx_rom_view_x keep only bytes outside PST; at the cf instance PST = []), and HSTR2S, the OWED kit _x twin
     of W_shadow_pin_fr.ashp_str2_1_fr.
   - ROUTE R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0; a Theorem Labs lane's top_x at R): the arm at a world relation R, lf_arm_remove_xR, whose
     statement is cut_x's ARM_remove_R (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section wR).  relay_remove, check_no_loss, check_shape_ends and
     source_reset free (re-hide the dead shadow), so they are taken at R by their R texts rr_spec_xR
     (W_contract_xR_relay.v), cnl_spec_xR / cshe_spec_xR (W_contract_xR_g6.v) and sr_spec_g_xR (W_contract_srlf_xR.v);
     the leaves check_shape_done / check_no_loss_read stay strict and are lifted inside (SRr_SRrG, ajournal_xR_mono).
     Section wR below holds every lemma that reads the arm's journal (the AR0 layer's journal wrappers, the K-lemmas,
     the nine segment walks), stated once over ajournal_gx_xR R: a segment that calls no freeing callee is its walk
     over the R journal (paj_run_x_xR), lifted by SRr_SRrG; a segment around a freeing call runs at R (paj_run_x_xG)
     and composes the callee's R journal by ajournal_gx_sub_xR (R_trans).  STRICT PROOFS COLLAPSED: lf_arm_remove_x
     keeps its statement and argument list and is lf_arm_remove_xR at R := wle (each R callee text from the strict one
     by X_xR_of_x at WLE_R := id). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel relay_remove_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_check_no_loss W_check_shape_ends.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0m W_shadow_pin_fr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_remove.
(* route R: SRrG, the R contract texts of the freeing callees *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_contract_xR_g6 W_contract_srlf_xR W_contract_xR_relay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section wrx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* the arm's count peak (the room round, a Theorem Labs lane's ROOM-TEXTS (c)): a Theorem Labs lane's pk_rm (lib/A/ReplyLScnt.v,
   commit ba8e99b5bd2) word for word: relay_remove's premise peak (its trace's peak + 4), plus check_no_loss's own peak
   over the lines the drain appended when the entry is open (its premise's + 2 is inside the 4); check_shape_ends and
   source_reset have premise peak 0.  check_no_loss's trace is ReplyTrPeakCnl.v:119-124's cnl_nm / cnl_tr / cnl_pk,
   restated here (that file Requires the AR arms) *)
Definition rm_cnl_nm (_ : Z) : RelayRunT.addr YO0i.sptr := RelayRunT.Known ListTr.pdefT.
Definition rm_cnl_tr (H : hlist) (xs : list (list byte)) : list (RelayRunT.rev YO0i.sptr) :=
  HarnessTr.check_no_loss_tr 0 (ListTr.sh_of rm_cnl_nm H) (map (fun x => (rm_cnl_nm 0, bzs x)) xs).
Definition rm_cnl_pk (H : hlist) (xs : list (list byte)) (P : Z -> bool) : nat :=
  Z.to_nat (ReplyCnt.tr_peakP P (rm_cnl_tr H xs)).
Definition rm_pk (m : lmod) (h : hsrc) (j0 : nat) (P : Z -> bool) : nat :=
  (Z.to_nat (ReplyCnt.tr_peakP P (rm_rr_tr m h)) +
   (if (re_eof (rm_ent m j0) =? 0)%Z
    then rm_cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P else 0) + 4)%nat.
(* the open entry's and the slot's facts the count rules RM_CNT_* read (a Theorem Labs lane's bundle), in W_rep.v's order:
   aentry_ok's skip, fd sign, capacity, partial-line and key-array clauses (W_rep.v:121, 123, 124, 125, 131-132) and the
   pending list's non-empty records (alist_at at lines = false, W_rep.v:91); the walk reads them off amodel_at at the
   arm's start.  The fd sign matters: rr_tr is [] at a negative fd (W_contract.v:1295) *)
Definition rm3_pre (e : rentry) (h : hsrc) : Prop :=
  (re_skip e = 0 \/ re_skip e = 1) /\
  0 <= re_fd e /\
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) <= APARTIAL /\ ~ In (Z_to_bv 8 0) (re_U e) /\
  ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 <= re_kh e)) /\
  Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h)).

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

(* ---- the AR file's Section hypotheses (W_LLVMFuzzerTestOneInput_remove.v Section rmw), over ARx ---- *)
(* ------------------------------------------------------------------ what the other lanes owe *)
Variable MMAX : Z.                                  (* W6's request bound, rr_spec's parameter *)
Hypothesis TL : PALib B.                            (* the allocator instance (W_kit.v) *)
Hypothesis ML : ameter_laws MT.                     (* the allocator instance's meter *)
Variable CTX_AFREE : list (list Z).
Hypothesis HCTX_rr0 : In [BASE + AF_fr_relay_remove + 436; BASE + RET_RR1] CTX_AFREE.
Hypothesis HCTX_rr1 : In [BASE + AF_fr_relay_remove + 436; BASE + RET_RR1; RA_LLVMF] CTX_AFREE.
Hypothesis RGP : rg_place B fr_RG.
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Hypothesis HGnsrc : forall a, rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 -> inG G_fr a.
Hypothesis HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
                 (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= rg_s fr_RG).
Hypothesis HGRT_s : gx_rt B [(rg_s fr_RG, 4 * ASRC)].
Hypothesis HRO : rom_out segs B G_fr.
Hypothesis HMG : forall a, rm_mglob a ->
  in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis RI_rm_found : forall cx t m si h,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 4 ->
  pick (lm_hs m) (rm_kb cx m) = Some si -> nth si (lm_hs m) None = Some h ->
  exists j, (j < length (lm_es m))%nat /\ re_fd (rm_ent m j) = hs_fd h.
Hypothesis RI_rm_rr_fds : forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Hypothesis RI_rm_rr_pair : forall cx t m si h j0,
  RINV cx t m -> rm_at cx m si h j0 -> re_eof (rm_ent m j0) = 0 ->
  re_skip (rm_ent m j0) = hs_overlong h /\ (re_skip (rm_ent m j0) = 0 -> bzs (re_U (rm_ent m j0)) = bzs (hs_W h)).
(* the removed slot's expected list is empty at the arm's start (drain_x's RI_src's first conjunct, at rm_at; the
   plain proof's pair_ok, Prog/SlotInv.v:253-263) *)
Hypothesis RI_rm_src : forall cx t m si h j0,
  RINV cx t m -> rm_at cx m si h j0 -> hl_recs (hs_expected h) = [].
(* relay_remove's sizes and budget: a Theorem Labs lane's TX_LS_rm_rr_pre (lib/A/ReplyLS3Peak.v:152, commit 1318828167d)
   in this Section's names (MMAX for CfParamsReply.fr_MMAX; its ent_capout_ok0 (c_W cx) (c_mem cx), ReplyLS3eCap.v:134,
   stated by its body: that file Requires the AR arms); conjuncts 3 and 6 in rr_spec_x's peak form *)
Hypothesis LS_rm_rr_pre : forall cx t m ly S si h j0,
  LSx cx t m ly S -> RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (rm_rr_tr m h) < MMAX /\ blocks_bytes S + tr_peak (rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok MT S ((rm_rr_cost MT) m h) /\ lm_cap m < MMAX /\
  blocks_bytes S + tr_peak (rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (rm_rr_tr m h)) <= LIVE_MAX.
Hypothesis RI_rm_cnl_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
(* check_no_loss's allocator facts after relay_remove's charge: a Theorem Labs lane's TX_LS_rm_cnl_pre (lib/A/
   ReplyLS3cTopxPost.v:178, commit d0d75bf92db) in this Section's names: the start model's block sizes (rm_mfacts) and
   the composed frame to the call's state (rm_fr).  LS_rm_cnl_pre, LS_rm_cshe_pre and LS_rm_sr_pre take, after rm_rr_ok,
   the arm's t bound (lregs_rmc's last conjunct) and the removed entry's partial-line bound (rm_Qc's rm3_pre);
   LS_rm_step takes the partial-line bound after LSx *)
Hypothesis LS_rm_cnl_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).
Hypothesis RI_rm_cnlr_eof : forall cx t m si h j0,
  RINV cx t m -> rm_at cx m si h j0 -> 0 <= re_eof (rm_ent m j0) <= 1.
Hypothesis RI_rm_cshe_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Hypothesis LS_rm_cshe_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  LSx cx t m ly0 S0 -> RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  rm_cnl_ok h1 E' H' ->
  mo_le MT S0 S ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1)) ->
  mo_ok MT S ((rm_cshe_cost MT) H').
Hypothesis HT : AF0m.TfibSyms B.
Hypothesis RI_rm_csd : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  0 <= lm_gn m <= 1 ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).
Hypothesis LS_rm_sr_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  LSx cx t m ly0 S0 -> RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  rm_cnl_ok h1 E' H' -> rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  mo_le MT S0 S ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H') ->
  mo_ok MT S (sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))).
Hypothesis RI_rm_step : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  RINV cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2).
Hypothesis LS_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
(* the room round's count row (a Theorem Labs lane's ROOM-TEXTS (c); a Theorem Labs lane's lib/A/ReplyLScnt.v fr_LS3cp_cnt_rm at
   commit ba8e99b5bd2): at the arm's start, the live counts plus the arm's peak rm_pk stay under RP's bounds.  The
   guards are the walk's facts there (the model's sizes come from amodel_at) *)
Hypothesis LS_cnt : forall cx t m ly S (W : world segs) mem si h j0,
  LSx cx t m ly S -> RINV cx t m -> rm_at cx m si h j0 -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (rm_pk m h j0) (ablocks B ly S).
(* the count rules (W8Entry-2's pattern decision): a later callee's count premise is LS_cnt's at the arm's start
   moved by the composed frame (rm_fr: the call's live blocks are the input, the model's blocks at the call and the
   start's rest), so what it needs beyond LS_cnt is a fact of the MODEL alone: the model's count at the call plus the
   callee's premise peak stays under the start model's count plus rm_pk, for every count predicate P.  Pure model
   rules (no astate); the premises are what the walk holds at the call *)
Hypothesis RM_CNT_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_mfacts m ->
  rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) +
     W_contract_x.cnl_pk (hs_expected h1) (hs_held h1) P <= ReplyCnt.acnt P (model_blks m) + rm_pk m h j0 P)%nat.
Hypothesis RM_CNT_cshe : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_mfacts m -> rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2)) +
     W_contract_x.cshe_pk P <= ReplyCnt.acnt P (model_blks m) + rm_pk m h j0 P)%nat.
Hypothesis RM_CNT_sr : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc (P : Z -> bool),
  RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc -> rm_mfacts m ->
  rm3_pre (rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2)) +
     W_contract_x.sr_pk P <= ReplyCnt.acnt P (model_blks m) + rm_pk m h j0 P)%nat.
(* the callee specs, in their kit _x forms (W_contract_x.v; each owner proves its _x twin) *)
Hypothesis RR : rr_spec_x B PST ARx MT RP MMAX fr_RG CTX_AFREE (BASE + AF_fr_relay_remove).
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
Hypothesis CNLR : cnlr_spec_x B PST ARx (BASE + AF_fr_check_no_loss_read).
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt B G -> cnl_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE : forall G, gx_ok segs B G -> cshe_spec_x B PST ARx MT RP G (BASE + AF_fr_check_shape_ends).
Hypothesis SR : sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset).
(* source_reset's G, the slot (W_contract_x.v gx_prog_x) *)
Hypothesis HGP : forall si, (si < 4)%nat -> gx_prog_x B ARx [(rm_HA si, ASRC)].
(* _cut's errno_law over ARx: cut_x's errno_law_x *)
Hypothesis ERR : errno_law_x B ARx.
(* OWED: kit _x twin of W_shadow_pin_fr.ashp_str2_1_fr (W_shadow_pin_fr.v:44, `ashp (PI := PB_fr) B (VAL (A_OBJ 28))
   1`), over ARx: .str.2's shadow facts in every allocator state (W_contract_x.v ashp_x) *)
Hypothesis HSTR2S : ashp_x ARx (VAL (A_OBJ 28)) 1.
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441), at a bound true at the cf
   instance (YG0dcf.v:623 AR_blocks_law_cf: 0 <= n < cf_malloc_max = 2^30 - 2^20); ARx_blocks_law has no size
   conjunct *)
Hypothesis BLKN30 : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n < 2 ^ 30.
(* the ROM bytes lie outside PST: ajournal_gx_rom_view_x's premise (W_journal_x.v:329) *)
Hypothesis PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
(* the image bytes outside the allocator's owned statics lie outside PST (the generic journal's image clause keeps only
   bytes outside PST; the AR journal's keeps every image byte outside G, the owned statics and errno) *)
Hypothesis PST_IMG : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ Exists (in_zr a) PST.

(* ------------------------------------------------------------------ THE AR0 LAYER (ARx at the ghost list []) *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation afn_pre0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
Local Notation lf_base0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).

(* ------------------------------------------------------------------ ROUTE R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0)
   The arm's journal is ajournal_gx_xR R from the entry (the cut journal of cut_x's Section wR), so every lemma that
   reads it is stated here, once, over R; lf_arm_remove_x after this Section is lf_arm_remove_xR at R := wle.  The
   freeing callees are taken at R by their R texts, in the order of the strict hypotheses RR, CNL, CSHE, SR. *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis RR_R : rr_spec_xR B PST ARx R MT RP MMAX fr_RG CTX_AFREE (BASE + AF_fr_relay_remove).
Hypothesis CNL_R : forall G, gx_ok segs B G -> gx_rt B G ->
  cnl_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE_R : forall G, gx_ok segs B G -> cshe_spec_xR B PST ARx R MT RP G (BASE + AF_fr_check_shape_ends).
Hypothesis SR_R : sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJI0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).

(* the AR journal lemmas the AR proof cites, over AJ0 / AJI0 with their AR argument layout (W_journal.v / YCbq.v),
   each one application of its W_journal_x.v / YCbqG.v R twin *)
Lemma ajournal_gx_AR0 : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> AR0 ly' S' W' mem' md'.
Proof. intros. eapply ajournal_gx_AR_xR. eassumption. Qed.
Lemma ajournal_gx_inner0 : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  exists memS, AJI0 (STK + XO) (sp0 + XO) FP ly S W memS md own ly' S' W' mem' md' k /\
  (forall a, ~ inG G (bv_unsigned (Z_to_bv 64 a)) -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
Proof. intros. eapply ajournal_gx_inner_xR. eassumption. Qed.
Lemma ajournal_gx_G_mono0 : forall G G' XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  (forall a, inG G a -> inG G' a) ->
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  AJ0 G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; eassumption. Qed.
Lemma ajournal_gx_rom_view0 : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> rom_out segs B G ->
  rom_view segs W mem -> rom_view segs W' mem'.
Proof. intros. eapply (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low); eassumption. Qed.
Lemma ajournal_gx_nil0 : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k,
  AJ0 [] 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k <->
  AJI0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof. intros. exact (ajournal_gx_nil_xR segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k). Qed.
(* a strict leaf's post journal (aleaf_post_x's ajournal_x, at []) is a journal at R (WLE_R) *)
Lemma aji0_of_x : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k,
  ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  AJI0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  eapply ajournal_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma ajournal_gx_sub0 : forall G STK sp0 XO0 OUT0 FP ly S (W : world segs) mem md own lyc Sc (Wc : world segs) memc mdc
    k STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 (W2 : world segs) mem2 md2 k1,
  AJ0 G XO0 OUT0 STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  AJ0 G XO1 OUT1 STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 -> sp1 + XO1 <= sp0 + XO0 ->
  (forall a, inFP OUT1 a -> sp0 - STK <= a < sp0 \/ inFP OUT0 a) -> gx_ok segs B G ->
  (forall a, inFP FP1 a -> inFP FP a /\ (exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  AJ0 G XO0 OUT0 STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof. intros. eapply (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans); eassumption. Qed.
Lemma afn_pre_at0 : forall STK sp0 FP ly S (W0 : world segs) mem md own lyc Sc (W : world segs) memc mdc k regsc STK1
    (o : Z) ch1,
  AJI0 STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview segs (w_H W) memc) (spZ regsc) (s0Z regsc) ch1 ->
  afn_pre0 STK1 lyc Sc W regsc memc mdc ch1.
Proof. intros. eapply afn_pre_x_atR; eassumption. Qed.
(* the AR laws the AR proof cites (YG0d.v AR_laws / YCbq.v), at AR0, from AR_laws_x (YCbqG.v) *)
Lemma frames_bounds0 : forall ly S (W : world segs) mem md cid pos,
  AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
  in_app (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof. intros. eapply frames_bounds_x; eassumption. Qed.
Lemma sep_blocks0 : forall ly S (W : world segs) mem md b m p n,
  AR0 ly S W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
  zdisjoint (b, req_size m) (p, req_size n).
Proof. intros. eapply sep_blocks_x; eassumption. Qed.
Lemma sep_block_frame0 : forall ly S (W : world segs) mem md b m cid pos,
  AR0 ly S W mem md -> In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  zdisjoint (b, req_size m) (frame_addr ly cid pos, fs_frame_bytes cid).
Proof. intros. eapply sep_block_frame_x; eassumption. Qed.
Lemma range_addressable_of_block0 : forall ly S (W : world segs) mem md p m a n,
  AR0 ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof. intros. eapply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0); eassumption. Qed.
Lemma azs_range_addressable0 : forall ly S (W : world segs) mem md a n,
  AR0 ly S W mem md -> azs B a n -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof. intros. eapply (azs_range_addressable_x B ARx LAWS); eassumption. Qed.
Lemma al_blocks_0 : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\
  0 <= n < 2 ^ 30.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat (split; [assumption|]). exact (BLKN30 ly S [] W mem md p n HAR Hin).
Qed.
Lemma al_sep_0 : forall ly S (W : world segs) mem md, AR0 ly S W mem md ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)
    ++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (frames S)) /\
  Forall (fun f => 4096 <= frame_addr ly (fst f) (snd f) /\
    frame_addr ly (fst f) (snd f) + fs_frame_bytes (fst f) <= alloc_ceiling) (frames S).
Proof. intros. exact (alx_sep _ _ _ LAWS ly S [] W mem md H). Qed.
Lemma al_client_img_0 : forall ly S (W : world segs) mem md a, AR0 ly S W mem md ->
  ((exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) \/
   (exists cid pos, In (cid, pos) (frames S) /\ a = flag_addr ly cid pos)) ->
  ~ in_zr a (ly_img ly) /\ ~ in_img segs a.
Proof. intros. exact (alx_client_img _ _ _ LAWS ly S [] W mem md a H H0). Qed.
Lemma al_zshadow_0 : forall ly S (W : world segs) mem md r,
  AR0 ly S W mem md -> In r (zero_shadow_ranges B ly) ->
  zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Proof. intros. exact (alx_zshadow _ _ _ LAWS ly S [] W mem md r H H0). Qed.

(* the runs of a segment that calls no freeing callee: the strict walk over the R journal (W_journal_x.v Section g) *)
Let RUN := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTO := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
Ltac rm_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Lemma rm_loopX_x : forall (k : nat) (j j0 n G fd : Z) (fds eofs : Z -> Z) W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk,
  Z.of_nat k = n - j -> 0 <= j <= j0 -> j0 < n -> n <= 16 ->
  AJ0 G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk ->
  In (G, ATABLE) (ablocks B lyc Sc) ->
  (forall q, j <= q < n -> val_mem segs (mrestrict (w_H W) memc) (G + 56 * q) 4 (fds q) /\
     val_mem segs (mrestrict (w_H W) memc) (G + 56 * q + 4) 4 (eofs q) /\ 0 <= fds q < 2 ^ 31 /\ 0 <= eofs q <= 1) ->
  fds j0 = fd -> (forall q, j <= q < j0 -> fds q <> fd) ->
  getr regs 10 = w64 fd -> getr regs 11 = w64 (G + 56 * j) -> getr regs 12 = w64 (G + 56 * j + 4) ->
  getr regs 13 = w64 (n - j) -> getr regs 14 = w64 (SB + (G + 56 * j) / 8) -> getr regs 26 = w64 SB ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_rm_loop)) memc (seg_rom segs)) mdc)
  (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_fr_relay_remove)) mem' (seg_rom segs)) md' /\
    AJ0 G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' kk /\
    (forall r, In r RML_KEPT -> getr regs' r = getr regs r) /\
    getr regs' 20 = w64 (eofs j0) /\ getr regs' 22 = getr regs 28 /\ getr regs' 1 = Z_to_bv 64 (BASE + RET_RR1) /\
    mrestrict (w_H W) mem' = mrestrict (w_H W) memc).
Proof.
  induction k as [|k IH]; intros j j0 n G fd fds eofs W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk
    Hk Hj Hj0 Hn HJ HGin HENT Hfd0 Hne H10 H11 H12 H13 H14 H26; [lia|].
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ajournal_gx_AR0 G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk HJ) as HAR.
  destruct (al_blocks_0 lyc Sc W memc mdc G ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPh_ia & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPh_ia. pose proof (proj1 HPh_ia) as HPh.
  assert (G8 : G = 8 * (G / 8)).
  { pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
  assert (XQ : (G + 56 * j) / 8 = G / 8 + 7 * j).
  { rewrite G8 at 1. replace (8 * (G / 8) + 56 * j) with ((G / 8 + 7 * j) * 8) by ring. apply Z.div_mul. lia. }
  destruct (HENT j ltac:(lia)) as (Mu & Mc & Ru & Rc).
  destruct (HENT j0 ltac:(lia)) as (_ & _ & Rfd & _). rewrite Hfd0 in Rfd.
  set (u := fds j) in *. set (c := eofs j) in *.
  remember (Eimg (Ereg regs (rml_extra (G + 56 * j) u c))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (rml_extra (G + 56 * j) u c)) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E10 : ew E 10 = Z_to_bv 64 fd) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E13 : ew E 13 = Z_to_bv 64 (n - j)) by (rewrite (EEo 13%nat 13%bv eq_refl); exact H13).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact H26).
  assert (E32 : ew E 32 = Z_to_bv 64 (G + 56 * j))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 u) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3))) = SB + (G + 56 * j) / 8).
  { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 32 _ E32), U_lit by (unfold SB; lia). cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite XQ. rewrite (Z.mod_small (G / 8 + 7 * j)) by lia. rewrite Z.mod_small by (unfold SB; lia). reflexivity. }
  assert (HS : st_ok_pi segs VAL E ss_rml (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rm_loop)) memc (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_rml. apply pa_entry_st_ok_full.
    - unfold rml_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |];
        rewrite <- HE.
      + rewrite H11. apply bv_eq. fold (U E (SOff 32 0)). rewrite (U_atom E 32 _ E32) by lia.
        apply unsigned_lit_small. lia.
      + rewrite H12. apply bv_eq. fold (U E (SOff 32 4)). rewrite (U_atom_off E 32 _ 4 E32) by lia.
        apply unsigned_lit_small. lia.
      + rewrite H14. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3)))). rewrite USH.
        apply unsigned_lit_small. unfold SB. lia.
    - vm_compute. reflexivity.
    - unfold rml_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite E32, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      + apply (chunk_ok_val segs E _ (G + 56 * j) 0 4 (SOff 33 0) u);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mu.
      + apply (chunk_ok_val segs E _ (G + 56 * j) 4 4 (SOff 34 0) c);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact Mc.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [rml_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E10, E13, E26, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia).
      all: rewrite G8; replace (8 * (G / 8) + 56 * j) with ((G / 8 + 7 * j) * 8) by ring; apply Z_mod_mult. }
  clear HE.
  assert (HBx : U E rml_Bx = SHADOW_OFF) by (unfold rml_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs rml_Bx rml_SH E (mrestrict (w_H W) memc)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block0 lyc Sc W memc mdc G ATABLE (G + 56 * j) 8 HAR HGin); rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 32 _ E32) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  unfold A_rm_loop in HS |- *.
  paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rm_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* fd found at entry j: j = j0, on to relay_remove *)
    rewrite branch_eq_U, (U_atom E 33 u E33), (U_atom E 10 fd E10) in Hc by lia. apply Z.eqb_eq in Hc.
    assert (Hjj : j = j0) by (destruct (Z.eq_dec j j0) as [|Hne']; [assumption | exfalso; exact (Hne j ltac:(lia) Hc)]).
    subst j0.
    paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_relay_remove.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rm_meq HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (rml_extra (G + 56 * j) u c)) Ev)
        by (destruct HAE as [HA1 HA2]; split; [intros m Hm; rewrite !ew_ewset_other by lia; exact (HA1 m Hm) | exact HA2]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ RML_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    prreg HS (20%bv : bv 5) R20. prreg HS (22%bv : bv 5) R22. prreg HS (1%bv : bv 5) R1.
    pmkst HS. apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
    split; [reflexivity|]. split; [exact HJ|].
    split; [exact KR|].
    split; [rewrite R20, E34; reflexivity|].
    split; [rewrite R22; exact (EEo 28%nat 28%bv eq_refl)|].
    split; [exact R1|].
    rewrite Em2, Em1. reflexivity.
  - (* not this entry *)
    rewrite branch_eq_U, (U_atom E 33 u E33), (U_atom E 10 fd E10) in Hc by lia. apply Z.eqb_neq in Hc.
    assert (Hjlt : j < j0) by (destruct (Z.eq_dec j j0) as [->|]; [exfalso; exact (Hc Hfd0) | lia]).
    paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rm_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    + (* entries left: back to the head *)
      rewrite branch_ne_U, (U_atom_off E 13 (n - j) (-1) E13), U_lit in Hc0 by lia.
      paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_LLVMFuzzerTestOneInput + 0x438).
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      rm_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ RML_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
      prreg HS (13%bv : bv 5) N13. prreg HS (26%bv : bv 5) N26.
      assert (XQ1 : (G + 56 * (j + 1)) / 8 = G / 8 + 7 * j + 7).
      { rewrite G8 at 1. replace (8 * (G / 8) + 56 * (j + 1)) with ((G / 8 + 7 * j + 7) * 8) by ring.
        apply Z.div_mul. lia. }
      assert (V14 : getr (ms_regs ms1) 14 = w64 (SB + (G + 56 * (j + 1)) / 8)).
      { pose proof (st_ok_pi_restrict_reg (PI := PB_fr) _ _ _ _ (14%bv : bv 5) HS) as Q.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
          let e := eval vm_compute in (sr_get (ss_regs ss) (14%bv : bv 5)) in
          change (sr_get (ss_regs ss) (14%bv : bv 5)) with e in Q end.
        rewrite Q. apply bv_eq.
        lazymatch goal with |- bv_unsigned (sv_denot E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end.
        rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 32 _ E32), !U_lit by (unfold SB; lia). cbn [zalu_raw].
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
        rewrite XQ. rewrite (Z.mod_small (G / 8 + 7 * j)) by lia.
        rewrite (Z.mod_small (SB + (G / 8 + 7 * j))) by (unfold SB; lia).
        rewrite Z.mod_small by (unfold SB; lia).
        unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). lia. }
      pmkst HS.
      eapply SRr_mono.
      { eapply (IH (j + 1) j0 n G fd fds eofs W (ms_regs ms1) (ms_mem ms1) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk);
          [ lia | lia | lia | lia | exact HJ | exact HGin
          | intros q Hq; rewrite Em3, Em2, Em1; apply HENT; lia
          | exact Hfd0 | intros q Hq; apply Hne; lia
          | rewrite N10, E10; reflexivity
          | rewrite N11, E32, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | rewrite N12, E32, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | rewrite N13, E13, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | exact V14
          | rewrite N26, E26; reflexivity ]. }
      cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & R20 & R22 & R1 & MEQ).
      split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
      split; [intros r Hr; rewrite (HK3 r Hr); exact (KR r Hr)|].
      split; [exact R20|]. split; [rewrite R22; exact (KR 28%bv ltac:(cbv; tauto))|]. split; [exact R1|].
      rewrite MEQ, Em3, Em2, Em1. reflexivity.
    + (* no entry left: j was the last one, so the entry j0 was j *)
      exfalso. rewrite branch_ne_U, (U_atom_off E 13 (n - j) (-1) E13), U_lit in Hc0 by lia.
      destruct (Z.eqb_spec (n - j + -1) 0); [lia | discriminate].
Qed.


(* ================================================================== the arm, 0x844b4 -> 0x84490 *)
(* op_remove (fuzz_reply.c:619-631) on the found path: at = 0 (F+192); the inlined relay_source(s->fd) search
   (rm_loopX_x); relay_remove(fd); check_no_loss_read(s) when the entry was not at end of file; check_no_loss(s, &at);
   check_shape_ends(s, "", &at); check_shape_done(at); source_reset(s); then `li s4,10` and the latch.  The
   not-found path (0x846bc, from the blez at 0x844d4 and the loop's exit 0x8450c) is refuted by RI_rm_found: every
   open source has its relay entry (the plain invariant's relay_at, Prog/SlotInv.v:265-276, pairs every entry with
   an open slot of the same fd and every open slot with an entry). *)
Definition RCUT_x (cx : lfcx) (m : lmod) (Q : alayout -> astate -> Prop)
    (RC : Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop) (pc : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly3 S3 k fpos,
    c = cfg_at segs (fr_B0 + pc) regs mem md /\ jt_rom W mem /\
    AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k /\
    aframe_at cx true (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly3 S3 W mem m /\ ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\
    ablocks_sep B fr_FP cx m ly3 S3 /\ Q ly3 S3 /\
    (* the room round: the cut's room invariant NP at the state, threaded through every allocator call's post *)
    NP S3 /\ RC (frame_addr ly3 1 fpos) regs W mem.
(* rm_Q (the AR file's: the cut's LSx at the arm's start, the meter charged acc since, the start model's facts and the
   composed frame) with the arm's count at its start (LS_cnt's), which the later callees' count premises move by the
   frame and the count rules RM_CNT_* *)
Definition rm_Qc (h : hsrc) (j0 : nat) (cx : lfcx) (t : Z) (m m' : lmod) (acc : Z) : alayout -> astate -> Prop :=
  fun ly S => exists ly0 S0, LSx cx t m ly0 S0 /\ mo_le MT S0 S acc /\ rm_mfacts m /\ rm_fr B cx ly0 S0 m m' ly S /\
    cnt_ok_pk RP (rm_pk m h j0) (ablocks B ly0 S0) /\ rm3_pre (rm_ent m j0) h.
(* a later callee's count premise from the arm's start count, the composed frame and a model inequality *)
Lemma rm_cnt_step : forall cx ly0 S0 m m' ly S pk pk',
  rm_fr B cx ly0 S0 m m' ly S ->
  (forall P, (ReplyCnt.acnt P (model_blks m') + pk' P <= ReplyCnt.acnt P (model_blks m) + pk P)%nat) ->
  cnt_ok_pk RP pk (ablocks B ly0 S0) -> cnt_ok_pk RP pk' (ablocks B ly S).
Proof.
  intros cx ly0 S0 m m' ly S pk pk' (rest & H0 & H1) Hle HC.
  apply (cnt_ok_pk_mono RP pk pk' (ablocks B ly0 S0) (ablocks B ly S)); [|exact HC].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ H0), (ReplyCnt.acnt_perm P _ _ H1), !ReplyCnt.acnt_app.
  specialize (Hle P). lia.
Qed.
(* the allocator state after the arm's calls: the cut's LSx at the arm's start, and the meter charged acc since *)
Lemma rmk_aview_above_x : forall STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  AJI0 STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
  forall a, sp0 <= a < 2 ^ 64 -> aview segs (w_H W') mem' a = aview segs (w_H W0) mem a.
Proof.
  intros STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k HJ a Ha.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _).
  apply F1; lia.
Qed.
Lemma rmk_ablocks_nodup_x : forall ly S (W : world segs) mem md, AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (al_sep_0 ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
  { intros [p n] Hb. destruct (al_blocks_0 ly S W mem md p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
    exact (proj1 (req_size_pos n ltac:(lia))). }
  revert Hp Hpos. generalize (ablocks B ly S) as l. induction l as [|b l IH]; intros Hp Hpos; [constructor|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp].
  constructor.
  - intros Hin. rewrite Forall_forall in Hf.
    specialize (Hf (fst b, req_size (snd b)) (in_map (fun b0 => (fst b0, req_size (snd b0))) l b Hin)).
    pose proof (Hpos b (or_introl eq_refl)). unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
  - apply IH; [exact Hp | intros b' Hb'; apply Hpos; right; exact Hb'].
Qed.
(* the lengths of the byte strings the model's footprints name *)
Lemma rm_afn_pre_at_sp_x : forall cx full ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre0 STK1 ly3 S3 W regs mem md ch /\ spZ regs + 16 < ly_top ly3 /\
    (spine ch = [] \/ spine ch = [RA_LLVMF]).
Proof.
  intros cx full ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HRA : raZ (c_regs cx) = RA_LLVMF) by exact (proj1 (proj2 HPRE)).
  assert (HPREE : afn_pre0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by exact (proj1 HPRE).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
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
  - pose proof (rmk_aview_above_x LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rmk_rdword (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rmk_rdword (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    split; [| split; [rewrite Hsp, HTOPeq, HF32; lia
                     | right; cbn [spine map fst snd]; unfold raZ in HRA; rewrite HRA; reflexivity]].
    eapply (afn_pre_at0 LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016 | | | | | ].
    + unfold raZ in Hra40. lia.
    + lia.
    + pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
      replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult.
    + lia.
    + rewrite HF32. lia.
  - exists []. split; [| split; [rewrite Hsp, HTOPeq, HF32; lia | left; reflexivity]].
    eapply (afn_pre_at0 LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
Lemma rm_afn_pre_at_x : forall cx full ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx full ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct (rm_afn_pre_at_sp_x cx full ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0
    HSTKb) as (ch & HPRE & _). exists ch. exact HPRE.
Qed.
(* the readable stack check_no_loss's last premise asks (W_contract.v:2076, cut's STKR): from F, the arm's frame is
   present (the journal's stack window) and from the entry's sp up the entry's view is kept (the journal's view clause
   above the window, G_fr being image bytes) and readable (STKR, fr_lib_pre_cf_x's last conjunct) *)
Lemma rm_stkr_x : forall cx ly3 S3 fpos k (W : world segs) mem md,
  lf_base0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  forall a, lf_F cx <= a < ly_top ly3 -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx ly3 S3 fpos k W mem md HB HJ a Ha.
  destruct HB as (_ & HPRE).
  assert (HSTKR : forall a, spZ (c_regs cx) <= a < ly_top (c_ly cx) -> aview segs (w_H (c_W cx)) (c_mem cx) a <> None)
    by (destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _); exact Hk).
  destruct (ajournal_gx_inner0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof asan_consts as (C1 & _).
  destruct (Z_lt_le_dec a (spZ (c_regs cx))) as [Hlo | Hhi].
  - assert (Hp : apresent (w_H W) mem a) by (apply Hpres; unfold LLVMF_STK; rewrite HF32 in Ha; lia).
    destruct Hp as [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
  - unfold LLVMF_STK in *.
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    rewrite (rmk_aview_above_x 32768 (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k HJ0 a ltac:(lia)).
    rewrite Hmg; [apply HSTKR; rewrite <- Etop; lia|].
    rewrite unsigned_lit_small by exact Ha64. intros HGa. pose proof (pa_segs_low a (proj1 (HG a HGa))).
    unfold kLowMemEnd in *. lia.
Qed.
(* (K2) a callee's journal at sp = F, over its own globals G1 (inside G_fr), its out cells OUT in [F, F + XO) and its
   footprint FP1 (live blocks, each allocated in this call or inside the entry's footprint), inside the arm's *)
Lemma rm_compose_x : forall cx fpos ly3 S3 (W : world segs) mem md k G1 XO OUT STK1 FP1
    ly' S' (W' : world segs) mem' md' k1,
  lf_base0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  AJ0 G1 XO OUT STK1 (lf_F cx) FP1 ly3 S3 W mem md [] ly' S' W' mem' md' k1 ->
  (forall a, inG G1 a -> inG G_fr a) -> 0 <= XO <= 320 -> 0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  (forall a, inFP OUT a -> lf_F cx <= a < lf_F cx + XO) ->
  (forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n /\
     (~ In (b, n) (ablocks B (c_ly cx) (c_S cx)) \/ inFP (lf_FP fr_FP cx) a)) ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' W' mem' md' (k + k1).
Proof.
  intros cx fpos ly3 S3 W mem md k G1 XO OUT STK1 FP1 ly' S' W' mem' md' k1 HB HJ HJc HG1 HXO HS0 HS1 HOUT HFP.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  (* the callee's journal lifted from its own G1 to G_fr, then composed into the arm's (_latch.v lf_seg_latch) *)
  pose proof (ajournal_gx_G_mono0 G1 G_fr XO OUT STK1 (lf_F cx) FP1 ly3 S3 W mem md [] ly' S' W' mem' md' k1
    HG1 HJc) as HJc'.
  pose proof (ajournal_gx_sub0 G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k
     STK1 (lf_F cx) XO OUT FP1 [] ly' S' W' mem' md' k1 HJ HJc') as HJ2.
  cbn [app] in HJ2. apply HJ2; [unfold LLVMF_STK in *; lia | lia | lia | | exact HG |].
  - intros a Ha. left. pose proof (HOUT a Ha). unfold LLVMF_STK in *. lia.
  - intros a Ha. destruct (HFP a Ha) as (b & n & Hin & Hr & [Hn | Hf]).
    + right. exists b, n. split; [exact Hin|]. split; [exact Hn | exact Hr].
    + left. split; [exact Hf|]. exists b, n. split; [exact Hin | exact Hr].
Qed.
(* (K3) the model's blocks meet K2's footprint premise (ablocks_sep; req_size n = n for n > 0) *)
Lemma rm_kept_x : forall cx fpos ly3 S3 (W : world segs) mem md k G1 XO OUT STK1 FP1
    ly' S' (W' : world segs) mem' md' k1,
  lf_base0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  AJ0 G1 XO OUT STK1 (lf_F cx) FP1 ly3 S3 W mem md [] ly' S' W' mem' md' k1 ->
  (forall a, inG G1 a -> inG G_fr a) ->
  0 <= XO <= 320 -> 0 <= STK1 -> STK1 + 352 <= LLVMF_STK -> ~ YI16.sink_open_fp FP1 ->
  (forall a, in_img segs a -> ~ inG G1 a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a /\
     ((forall m, writable_at segs m a) -> abyte_kept W mem W' mem' a)) /\
  (forall p n i, In (p, n) (ablocks B ly3 S3) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP1 (p + i) -> abyte_kept W mem W' mem' (p + i)) /\
  (forall a, lf_F cx <= a < 2 ^ 64 -> (lf_F cx + XO <= a \/ ~ inFP OUT a) -> abyte_kept W mem W' mem' a) /\
  (forall a, (in_zr a (frame_rng ly3 (1, fpos)) \/
              in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)) ->
     ~ inFP FP1 a -> abyte_kept W mem W' mem' a) /\
  frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\ frames S' = frames S3 /\ AR0 ly' S' W' mem' md'.
Proof.
  intros cx fpos ly3 S3 W mem md k G1 XO OUT STK1 FP1 ly' S' W' mem' md' k1 HB HJ HJc HG1 HXO HS0 HS1 Hsink.
  (* F is 320..351 bytes below the entry sp, which is LLVMF_STK above ly_stk_lo >= alloc_ceiling *)
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by exact (proj1 HPRE).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= 2 ^ 47) by lia.
  (* the arm's state: AR, and the fake frame (1, fpos) is one of its frames *)
  pose proof (ajournal_gx_AR0 G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as HAR3.
  destruct (ajournal_gx_inner0 G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memA & HJA & _).
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJA as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  (* the callee's journal; its start memory memS is the arm's outside G1, and G1 lies in the image *)
  destruct HJc as (_ & _ & (memS & HJi & Hag) & Hout).
  pose proof HJi as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & F2 & F3 & F4 & _).
  assert (HnG : forall a, ~ in_img segs a -> ~ inG G1 a).
  { intros a Hni HGa. apply Hni. exact (proj1 (HG a (HG1 a HGa))). }
  assert (Hm : forall a, 0 <= a < 2 ^ 64 -> ~ inG G1 a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { intros a Ha Hn. apply (aview_gagree segs G1 _ _ _ a Hag). rewrite unsigned_lit_small by lia.
    apply inGb_false. exact Hn. }
  assert (Hlow : forall a, kLowMemEnd <= a -> ~ in_img segs a).
  { intros a Ha Hi. pose proof (pa_segs_low a Hi). lia. }
  split.
  { intros a Hi Hn Hno He.
    pose proof (pa_segs_low a Hi) as Ha.
    assert (E : aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
    { rewrite (F3 a Hi Hno He (PST_IMG a Hi Hno) (fp_spares_closed FP1 a Hsink)). apply Hm; [lia | exact Hn]. }
    split; [exact E|]. intros Hw. split; [exact E | intros _; apply Hw]. }
  split.
  { intros p n i H1 H2 Hi Hnf.
    destruct (al_blocks_0 ly3 S3 W mem md p n HAR3 H1) as (_ & H4096 & Hpc & _).
    assert (Hni : ~ in_img segs (p + i)).
    { refine (proj2 (al_client_img_0 ly3 S3 W mem md (p + i) HAR3 _)).
      left. exists p, n. split; [exact H1 | lia]. }
    apply rmk_kept_noimg; [lia | exact Hni|].
    rewrite (F2 p n i H1 H2 Hi Hnf). apply Hm; [lia | exact (HnG _ Hni)]. }
  split.
  { intros a Ha Hor.
    assert (Hni : ~ in_img segs a) by (apply Hlow; lia).
    apply rmk_kept_noimg; [lia | exact Hni|].
    destruct (Z_lt_le_dec a (lf_F cx + XO)) as [Hlt | Hge].
    - apply Hout; [lia|]. destruct Hor as [Hor | Hor]; [lia | exact Hor].
    - rewrite (F1 a ltac:(lia) ltac:(lia)). apply Hm; [lia | exact (HnG _ Hni)]. }
  split.
  { intros a Hr Hnf.
    destruct (frames_bounds0 ly3 S3 W mem md 1 fpos HAR3 Hin1) as (HFF0 & HFF1 & _).
    replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity.
    assert (Hni : ~ in_img segs a /\ 0 <= a < 2 ^ 64).
    { destruct Hr as [Hr | Hr].
      - unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
        replace (fs_frame_bytes 1) with 128 in Hr by reflexivity.
        split; [|lia].
        refine (proj2 (al_client_img_0 ly3 S3 W mem md a HAR3 _)).
        right. left. exists 1, fpos. split; [exact Hin1|].
        replace (fs_frame_bytes 1) with 128 by reflexivity. lia.
      - unfold in_zr in Hr. cbn [fst snd] in Hr. replace (fs_frame_bytes 1 / 8) with 16 in Hr by reflexivity.
        unfold shadow_addr, SHADOW_OFF in Hr.
        assert (0 <= frame_addr ly3 1 fpos / 8) by (apply Z.div_pos; lia).
        assert (frame_addr ly3 1 fpos / 8 <= frame_addr ly3 1 fpos) by (apply Z.div_le_upper_bound; lia).
        split; [apply Hlow; lia | lia]. }
    destruct Hni as [Hni Ha].
    apply rmk_kept_noimg; [exact Ha | exact Hni|].
    rewrite (F4 1 fpos a Hin1 Hr Hnf). apply Hm; [exact Ha | exact (HnG _ Hni)]. }
  split.
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  split; [rewrite Hfrs; reflexivity | exact HAR'].
Qed.
(* (K5) where the bytes a model predicate reads live: its globals, or one of the blocks it names *)
Lemma rm_asrc_fp_in_x : forall ly S (W : world segs) mem md HA h,
  AR0 ly S W mem md -> asrc_at B ly S W mem HA h ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r ->
    (HA <= a < HA + ASRC) \/ exists p n, In (p, n) (asrc_blks h) /\ p <= a < p + n.
Proof.
  intros ly S W mem md HA h _ Hs r Hr a Ha.
  pose proof Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & H19 & _ & _ &
    H22 & H23 & _).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  - left. cbn [fst snd] in Ha. exact Ha.
  - right. exists (hs_partial h), APARTIAL. split; [left; reflexivity|].
    unfold gfp in Ha; cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, H19 in Ha. exact Ha.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + destruct ((rmk_alist_fp_in B) ly S W mem _ _ _ H10 r Hr a Ha) as [Hl | (p & n & Hin & Hpn)];
        [left; unfold ASRC; lia|].
      right. exists p, n. split; [right; apply in_or_app; left; exact Hin | exact Hpn].
    + destruct ((rmk_alist_fp_in B) ly S W mem _ _ _ H22 r Hr a Ha) as [Hl | (p & n & Hin & Hpn)];
        [left; unfold ASRC; lia|].
      right. exists p, n. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hin | exact Hpn].
    + destruct ((rmk_alist_fp_in B) ly S W mem _ _ _ H23 r Hr a Ha) as [Hl | (p & n & Hin & Hpn)];
        [left; unfold ASRC; lia|].
      right. exists p, n. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hin | exact Hpn].
Qed.
Lemma rm_arelay_fp_in_x : forall ly S (W : world segs) mem md G es,
  AR0 ly S W mem md -> arelay_at B fr_RG ly S W mem G es ->
  forall r, In r (arelay_fp fr_RG G es) -> forall a, fst r <= a < snd r ->
    (rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
     rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4) \/
    exists p n, In (p, n) (arelay_blks G es) /\ p <= a < p + n.
Proof.
  intros ly S W mem md G es _ Hrl r Hr a Ha.
  pose proof Hrl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _).
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
  - left. left. exact Ha.
  - left. right. left. exact Ha.
  - left. right. right. exact Ha.
  - right. exists G, ATABLE. split; [left; reflexivity | exact Ha].
  - right. apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
    rewrite Forall_forall in H10.
    destruct ((rmk_aentry_fp_in B) ly S W mem e (H10 e He) r Hr a Ha) as (p & n & Hpn & Hr2).
    exists p, n. split; [|exact Hr2]. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map; exact He | exact Hpn].
Qed.
Lemma rm_aout_fp_in_x : forall ly S (W : world segs) mem md c O mx no cap out,
  AR0 ly S W mem md -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  forall r, In r (aout_fp B fr_RG cap out) -> forall a, fst r <= a < snd r ->
    (exists r', In r' (aout_fp B fr_RG 0 out) /\ fst r' <= a < snd r') \/
    exists p n, In (p, n) (aout_blks cap out) /\ p <= a < p + n.
Proof.
  intros ly S W mem md c O mx no cap out _ _ r Hr a Ha.
  destruct (Z.eqb_spec cap 0) as [-> | Hc]; [left; exists r; split; [exact Hr | exact Ha]|].
  assert (E : aout_fp B fr_RG cap out = aout_fp B fr_RG 0 out ++ [(out, out + cap)]).
  { unfold aout_fp. rewrite (proj2 (Z.eqb_neq cap 0) Hc). reflexivity. }
  rewrite E in Hr. apply in_app_or in Hr as [Hr | [<- | []]].
  - left. exists r. split; [exact Hr | exact Ha].
  - right. exists out, cap. split; [unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) Hc); left; reflexivity|].
    cbn [fst snd] in Ha. exact Ha.
Qed.
(* (K6) the block separation after a callee whose blocks are the model's and the same rest before and after *)
Lemma rm_sep_step_x : forall cx fpos ly3 S3 (W : world segs) mem md k m m' ly' S' (W' : world segs) mem' md' rest,
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  ablocks_sep B fr_FP cx m ly3 S3 -> AR0 ly' S' W' mem' md' ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest) ->
  ablocks_sep B fr_FP cx m' ly' S'.
Proof.
  intros cx fpos ly3 S3 W mem md k m m' ly' S' W' mem' md' rest HJ [_ Hmod] HAR' Hp3 Hp'.
  assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  split; [exists rest; exact Hp'|].
  intros b Hb.
  destruct (in_dec Hdec b (model_blks m)) as [Hbm | Hbm]; [exact (Hmod b Hbm)|].
  (* a block of m' outside m is no block of the input or the rest (ablocks has no duplicate), so it is new since
     (ly3, S3) *)
  assert (Hn3 : ~ In b (ablocks B ly3 S3)).
  { intros Hin3.
    assert (Hin : In b (input_blks cx ++ model_blks m ++ rest)) by (eapply Permutation_in; [exact Hp3 | exact Hin3]).
    assert (Hnd : List.NoDup (input_blks cx ++ model_blks m' ++ rest))
      by (eapply Permutation_NoDup; [exact Hp' | exact (rmk_ablocks_nodup_x ly' S' W' mem' md' HAR')]).
    apply in_app_or in Hin as [Hi | Hin].
    - exact (rmk_nodup_app _ _ _ b Hnd Hi (in_or_app _ _ _ (or_introl Hb))).
    - apply in_app_or in Hin as [Hm | Hr]; [exact (Hbm Hm)|].
      apply List.NoDup_app_remove_l in Hnd. exact (rmk_nodup_app _ _ _ b Hnd Hb Hr). }
  (* live at the entry but not at (ly3, S3): freed since, so its bytes are in the entry's footprint *)
  destruct (in_dec Hdec b (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc]; [|left; exact Hc].
  right. destruct b as [p n]. cbn [fst snd]. intros a Ha.
  destruct (ajournal_gx_inner0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJA & _).
  pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
  replace a with (p + (a - p)) by lia. apply (Hgone p n (a - p) Hc Hn3).
  lia.
Qed.

(* ------------------------------------------------------------------ the pieces *)
(* ================================================================== (1)-(2): the helpers of rm_entry_x / rm_scan_x *)
(* ---- copied from W_frame.v (this file does not load it): st_ok_region_nth, st_ok_pi_region_nth,
   field_of_region, writable_kept, at this image's segs ---- *)
(* copied from W_frame.v st_ok_region_nth *)
Ltac rme_low :=
  cbn [fst snd gfp]; unfold RME_CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof rme_ceil_lo; lia.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_fp_low_nil *)
Lemma rme_blk_x : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks_0 ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_bzs_len *)
Lemma rme_alist_x : forall ly S (W : world segs) mem md LA l lines,
  AR0 ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= RME_CEIL8 ->
  rme_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : rme_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite rme_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (rme_blk_x ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite rme_bzs_len, length_app. cbn [length].
      unfold RME_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply rme_fp_low_cons; [cbn; lia | cbn; lia|]. apply rme_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply rme_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (rme_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply rme_fp_low_cons; [cbn; lia | | apply rme_fp_low_nil].
    cbn [gfp fst snd]. rewrite rme_bzs_len, length_app, rme_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold RME_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_asrc *)
Lemma rme_asrc_x : forall ly S (W : world segs) mem md HA h,
  AR0 ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= RME_CEIL8 ->
  rme_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (rme_alist_x ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (rme_alist_x ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (rme_alist_x ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (rme_blk_x ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply rme_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply rme_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite rme_bzs_len, Hpj. unfold APARTIAL, RME_CEIL8 in *. lia.
    + apply rme_fp_low_app; [exact A1|]. apply rme_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_aentry *)
Lemma rme_aentry_x : forall ly S (W : world segs) mem md e,
  AR0 ly S W mem md -> aentry_ok B ly S W mem e ->
  rme_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : rme_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                     Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite rme_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (rme_blk_x ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite rme_bzs_len, length_app. cbn [length].
      unfold RME_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply rme_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply rme_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (rme_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply rme_fp_low_cons; [cbn; lia | | apply rme_fp_low_nil].
      cbn [gfp snd]. rewrite rme_bzs_len, length_app. unfold RME_CEIL8 in *. lia.
    + apply rme_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (rme_blk_x ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite rme_bzs_len, rme_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold RME_CEIL8. pose proof rme_ceil_lo. lia. }
        destruct (rme_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold RME_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_arelay *)
Lemma rme_arelay_x : forall ly S (W : world segs) mem md G es,
  AR0 ly S W mem md -> arelay_at B fr_globals ly S W mem G es ->
  rme_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (rme_blk_x ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : rme_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite rme_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (rme_aentry_x ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite rme_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (rme_aentry_x ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply rme_fp_low_cons; [rme_low | rme_low|].
    apply rme_fp_low_cons; [rme_low | rme_low|].
    apply rme_fp_low_cons; [rme_low | rme_low|].
    apply rme_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, RME_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_aout *)
Lemma rme_aout_x : forall ly S (W : world segs) mem md c O mx no cap out,
  AR0 ly S W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= RME_CEIL8 ->
  rme_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply rme_fp_low_cons; [rme_low | rme_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply rme_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (rme_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply rme_fp_low_cons; [cbn; lia | cbn; unfold RME_CEIL8 in *; lia | apply rme_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_akept_rng *)
Lemma rme_amodel_kept_x : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR0 ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= RME_CEIL8 ->
  (forall a, 0 <= a < RME_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= RME_CEIL8)
      by (unfold fr_RG, RME_CEIL8; cbn; unfold ASRC; pose proof rme_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (rme_asrc_x ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (rme_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (rme_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (rme_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (rme_arelay_x ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (rme_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (rme_aout_x ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (rme_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply rme_akept_rng; [exact KEEP | cbn; lia | unfold RME_CEIL8; cbn; pose proof rme_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply rme_akept_rng; [exact KEEP | cbn; lia | unfold RME_CEIL8; cbn; pose proof rme_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply rme_akept_rng; [exact KEEP | cbn; lia | unfold RME_CEIL8; cbn; pose proof rme_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, RME_CEIL8 in *. pose proof rme_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, RME_CEIL8 in *. pose proof rme_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, RME_CEIL8 in *. pose proof rme_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, RME_CEIL8 in *. pose proof rme_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, RME_CEIL8 in *. pose proof rme_ceil_lo. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_sv8_kept *)
Lemma rme_ainput_kept_x : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR0 ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < RME_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (rme_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold RME_CEIL8. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_drain.v dr_rom_kept *)
Lemma rme_carry_x : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  AR0 ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) -> ~ (lf_F cx + 192 <= a < lf_F cx + 200) ->
     abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof rme_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds0 ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < RME_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold RME_CEIL8 in *; lia. }
  split.
  { apply (rme_aframe_kept cx true _ W W mem mem' HFR KEEP WK); unfold RME_CEIL8, SB in *; lia. }
  split; [exact (rme_amodel_kept_x ly3 S3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold RME_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (rme_ainput_kept_x cx ly3 S3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (rme_rom_kept W W mem mem' HRV KL)|].
  exact (rme_jt_kept W W mem mem' HJT KL).
Qed.
(* a memory with the same ASan view keeps every byte *)
Let rme_RUN := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let rme_RUNTO := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let rme_BR := paj_branch (PI := PB_fr).
(* a run's write obligation: the two cells are in the function's own stack window, the other regions read-only *)
Ltac rme_awr U9 :=
  cbn [ss_mem add_cond ss_rme rme_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the two cells is outside every region's writable window *)
Ltac rme_nowr U9 Hna1 Hna2 :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_rme rme_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.

(* (1) 0x844b4-0x844e4: at = 0, s->fd, g_nsrc, in.n, g_src; the blez refuted.  No call: the strict walk over the R
   journal, lifted by SRr_SRrG *)
Lemma rm_entry_xR : forall cx t W c,
  lf_base0 cx ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 4 cx [] t W c ->
  SRrG segs R W c (fun W' c' => exists m si h j0, RINV cx t m /\ rm_at cx m si h j0 /\
    RCUT_x cx m (LSx cx t m) ((lregs_rml B) cx t m si h) A_rm_loop W' c').
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  apply (SRr_SRrG segs R WLE_R).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP
    & HRI & HR).
  subst own.
  (* the cut state's ghost list is [] (HP0 on its journal's ARx) *)
  assert (EHp3 : Hp3 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJ). subst Hp3.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4) & R6 & R7 & R27 & Ht & Hk & HO
    & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof rme_ceil_lo as HCL.
  (* the operation is 4, and pick() gave slot si, which holds h *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 4).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 4) with true in HPK.
  destruct HPK as (R28 & R29 & [(si & Hpk & R21) | (Hf & _)]); [|lia].
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (rm_k' cx m) in R28, R29.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (rm_kb cx m) in Hpk.
  assert (Hk' : 0 <= rm_k' cx m <= c_n cx)
    by (unfold rm_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  destruct (rme_pick_some (lm_hs m) (rm_kb cx m) si Hpk) as [Hsi [h Hh]].
  rewrite Hlen4 in Hsi.
  pose proof (HSL si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
  pose proof HREL as (Msrc & _ & Mnsrc & _ & _ & _ & Hl16 & HGin & _).
  (* j0: the first relay entry with h's fd; RI_rm_found gives one *)
  destruct (RI_rm_found cx t m si h HRI Hk HO Hop Hpk Hh) as (j1 & Hj1 & Hfd1).
  unfold rm_ent in Hfd1.
  destruct (rme_first (lm_es m) relay_remove_b_c.no_entry (hs_fd h) j1 Hj1 Hfd1) as (j0 & Hj0 & Hfd0 & Hmin).
  assert (HAT : rm_at cx m si h j0)
    by exact (conj Hk (conj HO (conj Hop (conj Hpk (conj Hsi (conj Hh (conj Hj0 (conj Hfd0 Hmin)))))))).
  (* AR, the relay's block, the stack window, errno, the fake frame *)
  pose proof (ajournal_gx_AR0 G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 W mem md k HJ) as HAR.
  destruct (al_blocks_0 ly3 S3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds0 ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (HAr : 0x5d88e0 <= HA <= 0x5d88e0 + 288 /\ HA mod 8 = 0).
  { unfold HA. rewrite VS. unfold ASRC. split; [lia|].
    replace (0x5d88e0 + 96 * Z.of_nat si) with ((0xbb11c + 12 * Z.of_nat si) * 8) by lia. apply Z_mod_mult. }
  (* the entry state *)
  remember (Eimg (Ereg regs (rme_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (rme_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx))
    by (rewrite (EEo 9%nat 9%bv eq_refl), (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (VN : rg_nsrc fr_RG = 0x5d87a0) by reflexivity.
  assert (VG : rg_src fr_RG = 0x5d87c0) by reflexivity.
  assert (EO7 : ew E (A_OBJ 7) = Z_to_bv 64 (rg_nsrc fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj1 (proj2 (proj2 probe_hi))); reflexivity).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj1 (proj2 (proj2 (proj2 probe_hi)))); reflexivity).
  assert (E21 : ew E 21 = Z_to_bv 64 HA)
    by (rewrite (EEo 21%nat 21%bv eq_refl), (KR0 21%bv ltac:(cbv; tauto)); exact R21).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (rewrite (EEo 26%nat 26%bv eq_refl), (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - rm_k' cx m))
    by (rewrite (EEo 29%nat 29%bv eq_refl), (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (E32 : ew E 32 = Z_to_bv 64 (hs_fd h))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (lm_es m))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (lm_G m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = HA) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (UO7 : bv_unsigned (ew E (A_OBJ 7)) = rg_nsrc fr_RG) by (rewrite EO7; apply unsigned_lit_small; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG) by (rewrite EO8; apply unsigned_lit_small; lia).
  pose proof HFR as (_ & HAWR & _).
  assert (HS : st_ok_pi segs VAL E ss_rme
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_remove)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_rme. apply pa_entry_st_ok_full.
    - unfold rme_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE.
      + rewrite (KR0 23%bv ltac:(cbv; tauto)), C23. apply bv_eq. fold (U E (SOff (A_HI 74) 0)).
        rewrite (U_img_atom E HEI (A_HI 74)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        unfold w64. rewrite ?unsigned_lit_small by (unfold HI_G_NSRC; lia).
        first [exact (proj1 probe_hi) | exact (eq_sym (proj1 probe_hi))].
      + rewrite (KR0 18%bv ltac:(cbv; tauto)), C18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
        rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        unfold w64. rewrite ?unsigned_lit_small by (unfold HI_G_SRC; lia).
        first [exact (proj1 (proj2 probe_hi)) | exact (eq_sym (proj1 (proj2 probe_hi)))].
    - vm_compute. reflexivity.
    - unfold rme_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ HA 0 4 (SOff 32 0) (hs_fd h));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mfd.
      + rewrite UO7. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_nsrc fr_RG) 0 4 (SOff 33 0) (Z.of_nat (length (lm_es m))));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mnsrc.
      + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 34 0) (lm_G m));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Msrc.
    - unfold rme_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21, UO7, UO8.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [rme_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E21, E26, E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (EH74 : ew E 354 = Z_to_bv 64 HI_G_NSRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 probe_hi))).
  assert (EH75 : ew E 355 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia);
        exact (f_equal (Z_to_bv 64) (proj1 (proj2 probe_hi)))).
  clear HE.
  assert (HBx : U E rme_Bx = SHADOW_OFF)
    by (unfold rme_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  (* the shadow check of s5 passes: g_s is in the instance's zero-shadow ranges (HZS) *)
  assert (SHOK : sh_ok segs rme_Bx rme_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    - apply (azs_range_addressable0 ly3 S3 W mem md HA 4 HAR).
      destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold ASRC in Hzhi.
      exists zr. refine (conj Hzin (conj Hz8 _)). lia.
    - exact HBx.
    - rewrite (U_atom E 21 _ E21) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold SHADOW_OFF in *. lia. }
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 4)) with (Z_to_bv 64 (BASE + AF_arm_remove)).
  (* 0x844b4-0x844d0: sd zero -> F+192, the shadow check of s5, lw a3 = g_nsrc, lw a0 = s->fd, sd t4 -> F+144,
     to the blez *)
  paj_run_tok_x rme_RUN HS HJ SHOK rme_span.
  { rme_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) ->
      ~ (lf_F cx + 192 <= a < lf_F cx + 200) -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna1 Hna2; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); rme_nowr U9 Hna1 Hna2).
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (rme_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (S33 : bv_signed (sv_denot Ev (SOff 33 0)) = Z.of_nat (length (lm_es m)))
      by (assert (U33 : U Ev (SOff 33 0) = Z.of_nat (length (lm_es m)))
            by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E33 | lia]);
          unfold U in U33; rewrite bv_signed_small; [exact U33 | rewrite U33; lia]);
    assert (S0 : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity
  end.
  (* blez a3: g_nsrc <= 0; refuted, entry j0 lies below g_nsrc = |es| *)
  psrr_branch_tok rme_RUN rme_BR HS SHOK rme_span.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S33 in Hc.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc. exfalso. lia.
  - (* 0x844d8-0x844e4: a1 = g_src, a4 = SB + a1 / 8, a2 = a1 + 4, to the loop's head *)
    paj_run_to_tok_x rme_RUNTO HS HJ SHOK rme_span A_rm_loop.
    { rme_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) ->
        ~ (lf_F cx + 192 <= a < lf_F cx + 200) -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna1 Hna2; rewrite (aview_kept_out _ _ _ _ _ HFr a Ha) by (rme_nowr U9 Hna1 Hna2);
          exact (K1 a Ha Hna1 Hna2)).
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (rme_writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (rme_pres_grows W _ _ a HG0 (P1 a Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) ->
        ~ (lf_F cx + 192 <= a < lf_F cx + 200) -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna1 Hna2; split; [exact (K2 a Ha Hna1 Hna2) | apply WK]).
    destruct (rme_carry_x cx W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    assert (HFL2 : sv8 W (ms_mem ms0) (FF + 120) (flag_addr ly3 1 fpos)).
    { apply (rm_flag_kept W W mem (ms_mem ms0)); [|exact HFL]. intros a Ha. apply KEEP; lia. }
    pose proof (rme_st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (rme_st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (SVN : sv8 W (ms_mem ms0) (lf_F cx + 144) (c_n cx - rm_k' cx m)).
    { unfold sv8.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (rme_field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - rm_k' cx m) RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (SVZ : sv8 W (ms_mem ms0) (lf_F cx + 192) 0).
    { unfold sv8.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (rme_field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 192 8%N (SLit 0) 0 RG1) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - reflexivity.
      - zside.
      - zside. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (rme_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ RME_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KK : forall rr, In rr RME_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
    { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [RME_KEPT In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. rewrite EH75 in Q18. rewrite EH74 in Q23.
    pmkst HS. apply SRr_ret.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
    exists m, si, h, j0. split; [exact HRI|]. split; [exact HAT|].
    unfold RCUT_x. cbv beta.
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    exists ly3, S3, k, fpos.
    split; [reflexivity|].
    split; [exact HROM2|]. split; [exact HJ|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|].
    split.
    { split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [exact Q18|].
      split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [exact Q23|].
      split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
      split; [rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4|].
      split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27 | exact Ht]. }
    split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
    split; [rewrite (KK 21%bv ltac:(cbv; tauto)); exact R21|].
    split; [rewrite (KK 28%bv ltac:(cbv; tauto)); exact R28|].
    split; [exact SVN|]. split; [exact SVZ|].
    split; [rewrite Q10, E32; reflexivity|].
    split; [rewrite Q11, E34; reflexivity|].
    pose proof alloc_ceiling_lt as HACL.
    assert (HG8 : 0 <= lm_G m / 8 <= lm_G m) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    split; [rewrite Q12, E34, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q13, E33; reflexivity|].
    assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) = SB + lm_G m / 8).
    { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 34 _ E34), U_lit by (unfold SB; lia). cbn [zalu_raw].
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
      rewrite (Z.mod_small (lm_G m / 8)) by lia. rewrite Z.mod_small by (unfold SB; lia). reflexivity. }
    assert (Hsd : sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) =
                  alu64 ALU_ADD (ew E 26) (alu64 ALU_SRL (ew E 34) (Z_to_bv 64 3)))
      by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
    rewrite <- Hsd in Q14. rewrite Q14. apply bv_eq.
    fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3)))).
    rewrite USH. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
Qed.

(* (2) the search loop 0x844e8 (rm_loopX_x), on to relay_remove's entry from 0x849dc.  No call: the strict walk over
   the R journal, lifted by SRr_SRrG *)
Lemma rm_scan_xR : forall cx t m si h j0 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  RCUT_x cx m (LSx cx t m) ((lregs_rml B) cx t m si h) A_rm_loop W c ->
  SRrG segs R W c (RCUT_x cx m (LSx cx t m) ((lregs_rr B) cx t m si j0 h) AF_fr_relay_remove).
Proof.
  intros cx t m si h j0 W c HB HRI HAT
    (regs & mem & md & ly3 & S3 & k & fpos & -> & HROM & HJ & HFR & HFL & HMOD & HIN & HRV & HSEP & HQ & HNP & HR).
  apply (SRr_SRrG segs R WLE_R).
  pose proof HAT as (Hk & HO & Hop & Hpk & Hsi & Hh & Hj0 & Hfd0 & Hmin).
  pose proof HR as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C25 & C26 & C3 & C4 & C27 & Ht) & R20 & R21 & R28 &
    SV144 & SV192 & R10 & R11 & R12 & R13 & R14).
  pose proof HMOD as (_ & _ & HREL & _).
  pose proof HREL as (_ & _ & _ & _ & _ & _ & Hl16 & HGin & (tl & HTAB) & _).
  destruct ((rme_relay_entries B) ly3 S3 W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS & HEOF).
  pose proof (ajournal_gx_AR0 G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 W mem md k HJ) as HAR.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  unfold cfg_at. change (w64 (fr_B0 + A_rm_loop)) with (Z_to_bv 64 (BASE + A_rm_loop)).
  eapply SRr_mono.
  { apply (rm_loopX_x (length (lm_es m)) 0 (Z.of_nat j0) (Z.of_nat (length (lm_es m))) (lm_G m)
      (hs_fd h) (fun q => re_fd (rm_ent m (Z.to_nat q))) (fun q => re_eof (rm_ent m (Z.to_nat q)))
      W regs mem md LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [(1, fpos)] ly3 S3 k);
      [ lia | lia | lia | lia | exact HJ | exact HGin | | | | | | | | | ].
    - intros q Hq. cbv beta. unfold rm_ent.
      pose proof (rme_tbl_fd W mem (lm_G m) (lm_es m) tl relay_remove_b_c.no_entry (Z.to_nat q) HTAB HPAD HFDS
                    ltac:(lia)) as Mu.
      pose proof (rme_tbl_eof W mem (lm_G m) (lm_es m) tl relay_remove_b_c.no_entry (Z.to_nat q) HTAB HPAD HEOF
                    ltac:(lia)) as Mc.
      rewrite Z2Nat.id in Mu, Mc by lia. unfold AENT in Mu, Mc.
      assert (Rq : In (nth (Z.to_nat q) (lm_es m) relay_remove_b_c.no_entry) (lm_es m)) by (apply nth_In; lia).
      rewrite Forall_forall in HFDS, HEOF.
      split; [exact Mu|]. split; [exact Mc|]. split; [exact (HFDS _ Rq) | exact (HEOF _ Rq)].
    - cbv beta. rewrite Nat2Z.id. exact Hfd0.
    - intros q Hq. cbv beta. apply Hmin. lia.
    - exact R10.
    - rewrite R11. replace (lm_G m + 56 * 0) with (lm_G m) by lia. reflexivity.
    - rewrite R12. replace (lm_G m + 56 * 0 + 4) with (lm_G m + 4) by lia. reflexivity.
    - rewrite R13. replace (Z.of_nat (length (lm_es m)) - 0) with (Z.of_nat (length (lm_es m))) by lia. reflexivity.
    - rewrite R14. replace (lm_G m + 56 * 0) with (lm_G m) by lia. reflexivity.
    - exact C26. }
  cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HK & Q20 & Q22 & Q1 & MEQ).
  rewrite Nat2Z.id in Q20.
  pose proof (rme_keep_eq W mem mem' MEQ) as KA.
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a)
    by (intros a; exact (proj2 (KA a))).
  destruct (rme_carry_x cx W mem mem' md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HIN HRV HROM (fun a _ _ _ => KA a) WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
  assert (SVa : forall a v, sv8 W mem a v -> sv8 W mem' a v)
    by (intros a v Hv; apply (rme_sv8_kept W W mem mem'); [intros x _; exact (KA x) | exact Hv]).
  exists regs', mem', md', ly3, S3, k, fpos.
  split; [reflexivity|].
  split; [exact HROM2|]. split; [exact HJ'|]. split; [exact HFR2|]. split; [exact (SVa _ _ HFL)|].
  split; [exact HMOD2|].
  split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HQ|]. split; [exact HNP|].
  split.
  { split; [rewrite (HK 2%bv ltac:(cbv; tauto)); exact C2|].
    split; [rewrite (HK 8%bv ltac:(cbv; tauto)); exact C8|].
    split; [rewrite (HK 9%bv ltac:(cbv; tauto)); exact C9|].
    split; [rewrite (HK 18%bv ltac:(cbv; tauto)); exact C18|].
    split; [rewrite (HK 19%bv ltac:(cbv; tauto)); exact C19|].
    split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact C23|].
    split; [rewrite (HK 24%bv ltac:(cbv; tauto)); exact C24|].
    split; [rewrite (HK 25%bv ltac:(cbv; tauto)); exact C25|].
    split; [rewrite (HK 26%bv ltac:(cbv; tauto)); exact C26|].
    split; [rewrite (HK 3%bv ltac:(cbv; tauto)); exact C3|].
    split; [rewrite (HK 4%bv ltac:(cbv; tauto)); exact C4|].
    split; [rewrite (HK 27%bv ltac:(cbv; tauto)); exact C27 | exact Ht]. }
  split; [exact Q20|].
  split; [rewrite (HK 21%bv ltac:(cbv; tauto)); exact R21|].
  split; [rewrite Q22; exact R28|].
  split; [exact (SVa _ _ SV144)|]. split; [exact (SVa _ _ SV192)|].
  split; [rewrite (HK 10%bv ltac:(cbv; tauto)); exact R10|].
  exact Q1.
Qed.
(* (3) relay_remove(fd), back at 0x849e0 *)
(* (3) relay_remove(fd), back at 0x849e0 *)
(* ---- the model obligations relay_remove's call takes (pure, over lmod and the plain records) ---- *)
(* RI: two open sources have distinct fds, so relay_remove's aothers_at holds of the three other slots.  The text of
   _drain.v RI_fds.  Plain fact: Prog/SlotInv.v relay_at :270-275 (NoDup (map re_fd es); Forall2 pair_ok es hj with
   hs_fd h = re_fd e, :257; NoDup (map snd hj); every open slot is paired): two open slots pair with two entries,
   whose fds differ.  Discharged with drain's RI_fds. *)
Lemma rr_nums_x : forall cx ly3 S3 W mem md k fpos,
  lf_base0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) <= 2 ^ 47 /\ lf_F cx mod 32 = 0 /\
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\
  4096 <= frame_addr ly3 1 fpos /\ frame_addr ly3 1 fpos + 128 <= alloc_ceiling /\
  in_app (frame_addr ly3 1 fpos) 128 /\ frames S3 = [(1, fpos)] /\ AR0 ly3 S3 W mem md.
Proof.
  intros cx ly3 S3 W mem md k fpos (HAI & HPRE) HJ.
  pose proof HPRE as (HFN & _ & _ & _ & _ & _ & _ & Hfr0 & _).
  pose proof (ajournal_gx_AR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  rewrite !Z.add_0_r in *.
  destruct HSTK as (Hal & _ & Hceil & Hlo & Hhi & H47 & _).
  rewrite Hfr0, app_nil_r in Hfrs.
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frames_bounds0 _ _ _ _ _ 1 fpos HAR Hin) as (H4 & Hc & Happ).
  change (fs_frame_bytes 1) with 128 in Hc, Happ.
  pose proof (YM05.alloc_ceiling_value) as AC.
  unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)).
  split; [exact Hal|]. split; [unfold LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Happ|]. split; [exact Hfrs | exact HAR].
Qed.
(* a callee-saved register across the call (_latch.v lt_pres) *)
Ltac rr_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* the slots, written with rm_set_nth (the lemmas of _drain.v set_nth) *)
Ltac rr_cnt :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ rr_zz_dec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ rr_zz_dec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app in *; cbn [count_occ] in *);
  repeat match goal with
    | |- context [rr_zz_dec ?a ?b] => destruct (rr_zz_dec a b)
    | H : context [rr_zz_dec ?a ?b] |- _ => destruct (rr_zz_dec a b) end;
  lia.
Lemma rr_nfp_x : forall ly S (W : world segs) mem md (FL : list (Z * Z)) p n a,
  AR0 ly S W mem md -> (forall b, In b FL -> In b (ablocks B ly S)) ->
  In (p, n) (ablocks B ly S) -> ~ In (p, n) FL -> p <= a < p + req_size n -> ~ inFP (ablocks_fp FL) a.
Proof.
  intros ly S W mem md FL p n a HAR HFL Hin Hnot Ha (r & Hr & Hra).
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q kq] & <- & Hq). cbn [fst snd] in Hra.
  assert (Hne : (p, n) <> (q, kq)) by (intros E; apply Hnot; rewrite E; exact Hq).
  pose proof (sep_blocks0 ly S W mem md p n q kq HAR Hin (HFL _ Hq) Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* the fake frame and its shadow are outside every live block *)
Lemma rr_nfp_fr_x : forall ly S (W : world segs) mem md (FL : list (Z * Z)) fpos a,
  AR0 ly S W mem md -> (forall b, In b FL -> In b (ablocks B ly S)) -> In (1, fpos) (frames S) ->
  (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
   SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) -> ~ inFP (ablocks_fp FL) a.
Proof.
  intros ly S W mem md FL fpos a HAR HFL Hfr Ha (r & Hr & Hra).
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q kq] & <- & Hq). cbn [fst snd] in Hra.
  pose proof (HFL _ Hq) as Hq'.
  pose proof (sep_block_frame0 ly S W mem md q kq 1 fpos HAR Hq' Hfr) as Hd.
  destruct (al_blocks_0 ly S W mem md q kq HAR Hq') as (_ & _ & _ & Happ & _).
  destruct (frames_bounds0 ly S W mem md 1 fpos HAR Hfr) as (_ & Hc & Happf).
  change (fs_frame_bytes 1) with 128 in Hd, Hc, Happf.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  unfold in_app, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  assert (Hv0 : 0 <= frame_addr ly 1 fpos / 8) by (apply Z.div_pos; lia).
  assert (Hv1 : frame_addr ly 1 fpos / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  destruct Ha as [Ha | Ha]; clear - Ha Hra Happ Hd Hv0 Hv1; lia.
Qed.
(* the model's blocks are not empty (K3's premise) *)
Lemma rr_src_kept_x : forall ly3 S3 (W : world segs) mem md ly' S' (W' : world segs) mem' HA h',
  AR0 ly3 S3 W mem md -> asrc_at B ly3 S3 W mem HA h' ->
  (forall a, HA <= a < HA + ASRC -> abyte_kept W mem W' mem' a) ->
  (forall p n, In (p, n) (asrc_blks h') ->
     In (p, n) (ablocks B ly' S') /\ forall a, p <= a < p + n -> abyte_kept W mem W' mem' a) ->
  asrc_at B ly' S' W' mem' HA h'.
Proof.
  intros ly3 S3 W mem md ly' S' W' mem' HA h' HAR Hs KH KBk.
  apply (asrc_at_kept B ly3 S3 W mem ly' S' W' mem' HA h' Hs).
  - intros r Hr a Ha. destruct (rm_asrc_fp_in_x ly3 S3 W mem md HA h' HAR Hs r Hr a Ha) as [Ha' | (p & n & Hin & Hpn)];
      [exact (KH a Ha') | exact (proj2 (KBk p n Hin) a Hpn)].
  - intros [p n] Hb. exact (proj1 (KBk p n Hb)).
Qed.
(* the arm's frame across a callee that keeps the stack from F up, the fake frame and its shadow *)
Ltac rr_notG Ha He :=
  let HGa := fresh "HGa" in intros HGa;
  unfold G_RR, G_DR, G_SL in HGa; rewrite !inG_cons in HGa; unfold in_zr in HGa; cbn [fst snd] in HGa;
  cbn [fr_RG fr_globals rg_lock rg_nsrc rg_s rg_client_broken rg_send_eintr rg_nout rg_capout rg_out rg_gone]
    in HGa, Ha;
  unfold ASRC, AG_NFD, AG_THREAD_UP, AG_LISTEN in *;
  repeat (destruct HGa as [HGa | HGa]; [clear - HGa Ha He; lia|]); exact (inG_nil _ HGa).
(* relay_remove frees: the call at R (RR_R), its R journal composed into the arm's by rm_compose_x *)
Lemma rm_rr_xR : forall cx t m si h j0 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  RCUT_x cx m (LSx cx t m) ((lregs_rr B) cx t m si j0 h) AF_fr_relay_remove W c ->
  SRrG segs R W c (fun W' c' => exists e1 h1 ev LB c2 O2 cap2 out2,
    rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\
    RCUT_x cx (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)
      ((rm_Qc h j0) cx t m (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ((rm_rr_cost MT) m h))
      ((lregs_rmc B) cx t m si j0 0) RET_RR1 W' c').
Proof.
  intros cx t m si h j0 W c HB HRI HAT HC.
  pose proof HAT as (_ & _ & _ & _ & Hsi & Hh & Hj0 & Hfd & Hfirst).
  destruct HC as (regs & mem & md & ly3 & S3 & k & fpos & -> & HJT & HJ & HFR & HFG & HMOD & HIN & HRV & HSEP & HLS & HNP & HR).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Rt) &
    R20 & R21 & R22 & R144 & R192 & R10 & R1).
  destruct (rr_nums_x cx ly3 S3 W mem md k fpos HB HJ) as (_ & Hsp & HF32 & HFr & _ & _ & _ & Hfrs & HAR).
  pose proof HMOD as (Hlen & Hslots & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDw & HNFDr & HTU & HLST & HLSTw).
  pose proof (Hslots si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & Hfdr & _).
  pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNDfd & _).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (AC1 & _).
  pose proof HB as (_ & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE0)))))).
  assert (HspF : spZ regs = lf_F cx).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HSTK : 0 <= RR_STK_x /\ RR_STK_x + 352 <= LLVMF_STK)
    by (unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK; lia).
  (* the entry of h's fd that relay_remove's find returns is j0 *)
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (apply rr_find_first; assumption).
  remember (re_eof (rm_ent m j0) =? 0) as op eqn:Eop.
  assert (Hdrains : rr_drains (hs_fd h) (lm_es m) = op).
  { unfold rr_drains. rewrite Hfind. replace (0 <=? hs_fd h) with true by (symmetry; apply Z.leb_le; lia).
    rewrite Eop. reflexivity. }
  (* the live blocks: relay_remove's (FL) and the rest *)
  remember (concat (map slot_blks (rm_set_nth si None (lm_hs m)))) as OS eqn:HeqOS.
  remember (if op then asrc_blks h else []) as X eqn:HeqX.
  remember (if op then [] else asrc_blks h) as Xc eqn:HeqXc.
  pose proof HSEP as [[restS P0] _].
  assert (PM : Permutation (model_blks m) ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
                 asrc_blks h ++ OS ++ aout_blks (lm_cap m) (lm_out m))).
  { pose proof (rr_mb_split m si ltac:(lia)) as Q. rewrite Hh, <- HeqOS in Q. exact Q. }
  assert (HX : Permutation (asrc_blks h) (X ++ Xc))
    by (rewrite HeqX, HeqXc; destruct op; [rewrite app_nil_r|]; apply Permutation_refl).
  pose proof (rr_perm_pre _ _ _ _ _ _ _ _ _ _ _ P0 PM HX) as C1.
  remember ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ X ++ aout_blks (lm_cap m) (lm_out m))
    as FL eqn:HeqFL.
  assert (HFL : forall b, In b FL -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym C1)). rewrite HeqFL in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity | right]. rewrite !in_app_iff in Hb. rewrite !in_app_iff. tauto. }
  assert (HFP1 : rr_fp (lm_G m) (hs_fd h) (lm_es m) h (lm_cap m) (lm_out m) = ablocks_fp FL)
    by (rewrite HeqFL, HeqX; unfold rr_fp; rewrite Hdrains; reflexivity).
  pose proof (rmk_ablocks_nodup_x ly3 S3 W mem md HAR) as HND.
  (* relay_remove's afn_pre at sp = F *)
  destruct (rm_afn_pre_at_sp_x cx true ly3 S3 fpos k W mem md regs RR_STK_x HB HJ HFR HspF) as (ch & HPRE & HROOM & HSPN).
  { rewrite R1. apply ret_ok_codeptr_v; [unfold RET_RR1; lia | reflexivity]. }
  { unfold raZ. rewrite R1, unsigned_lit_small by (unfold RET_RR1; lia). unfold RET_RR1. lia. }
  { exact R3. } { exact R4. } { exact R8. } { lia. } { lia. }
  (* LS_rm_rr_pre's guards and LS_cnt (the arm's count at its start), from amodel_at and the registers' t bound *)
  assert (HU : Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL).
  { pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEOK & _). rewrite Forall_forall in HEOK.
    assert (Hn : In (rm_ent m j0) (lm_es m)) by (unfold rm_ent; apply nth_In; exact Hj0).
    destruct (HEOK _ Hn) as (_ & _ & _ & _ & _ & _ & Hu1 & Hu2 & _). lia. }
  pose proof (rm_mfacts_of B ly3 S3 W mem m HMOD) as HMF0.
  (* the count rules' bundle at the arm's start: the open entry's aentry_ok and the slot's pending list *)
  assert (HR3 : rm3_pre (rm_ent m j0) h).
  { pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEOK & _). rewrite Forall_forall in HEOK.
    assert (Hn : In (rm_ent m j0) (lm_es m)) by (unfold rm_ent; apply nth_In; exact Hj0).
    destruct (HEOK _ Hn) as (_ & Hsk & _ & _ & Hfd0 & Hcp & Hu1 & Hu2 & HuN & _ & _ & Hhp & _).
    pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
    pose proof HPL as (_ & _ & _ & _ & _ & _ & _ & _ & HPr).
    unfold rm3_pre. split; [exact Hsk|]. split; [lia|]. split; [exact Hcp|]. split; [lia|]. split; [exact HuN|].
    split.
    - destruct Hhp as [Hh0 | (Hh1 & _ & _ & H8 & _)]; [left; exact Hh0 | right; split; [exact Hh1 | exact H8]].
    - eapply Forall_impl; [|exact HPr]. intros r (_ & _ & _ & Hf). exact (Hf eq_refl). }
  assert (HCAP0 : exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX)
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  destruct (LS_rm_rr_pre cx t m ly3 S3 si h j0 HLS HRI HAT Rt HU (proj1 HMF0) (proj2 (proj2 HMF0) si h Hh) HCAP0)
    as (Hsz & Htrmax & Hlive & Hmok & _ & _).
  pose proof (LS_cnt cx t m ly3 S3 W mem si h j0 HLS HRI HAT HMOD Rt) as HCNT0.
  pose proof (RR_R W ly3 S3 [] regs mem md ch (lm_G m) (hs_fd h) (lm_es m) si h (lm_c m) (lm_O m) (lm_mx m)
    (lm_cap m) (lm_out m)) as HRR.
  cbv zeta in HRR. rewrite BASE_B0 in HRR.
  eapply SRrG_mono; [apply HRR with (kr := 0%nat); clear HRR|].
  - exact HPRE.
  - rewrite HspF. exact HF32.
  - rewrite Hfrs. vm_compute. reflexivity.
  - exact RGP.
  - exact R10.
  - lia.
  - exact HLOCK.
  - exact HWAKE.
  - exact HREL.
  - exact HOUT.
  - exact HRV.
  - intros i Hi Hfdi Heofi.
    assert (Eij : i = j0) by (apply (rr_fd_unique (lm_es m) i j0 HNDfd Hi Hj0); rewrite Hfdi; symmetry; exact Hfd).
    subst i. change (nth j0 (lm_es m) relay_remove_b_c.no_entry) with (rm_ent m j0) in *.
    unfold dr_src_ok.
    split; [exact Hsi|]. split; [exact HSRC|].
    split.
    { rewrite Hfd. apply ((rr_others B) ly3 S3 W mem (lm_hs m) si (hs_fd h) Hfdr Hslots).
      intros i' h' Hi' Hne Ei. exact (RI_rm_rr_fds cx t m i' si h' h HRI Hi' Hsi Hne Ei Hh). }
    split; [symmetry; exact Hfd|].
    destruct (RI_rm_rr_pair cx t m si h j0 HRI HAT Heofi) as [Q1 Q2].
    split; [exact Q1|]. split; [exact Q2|]. exact (Hsz Heofi).
  - exists (input_blks cx ++ Xc ++ OS ++ restS). rewrite Hdrains, <- HeqX. exact C1.
  - exact Htrmax.
  - exact Hlive.
  - exact Hmok.
  - apply RP_NP. exact HNP.
  - apply (cnt_ok_pk_mono RP (rm_pk m h j0) _ (ablocks B ly3 S3) _); [|exact HCNT0].
    intros P. unfold rr_pk, rm_pk, rm_rr_tr. lia.
  - exact HROOM.
  - (* the caller context (HCTX_rr0 / HCTX_rr1): the free's return, relay_remove's return 0x849e0, the chain's spine *)
    replace (raZ regs) with (BASE + RET_RR1)
      by (unfold raZ; rewrite R1, unsigned_lit_small by (unfold RET_RR1; lia); reflexivity).
    rewrite <- BASE_B0. destruct HSPN as [-> | ->]; [exact HCTX_rr0 | exact HCTX_rr1].
  - (* back at 0x849e0: rr_post *)
    intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k1 & -> & HJc & HPRES & _ & HMO & HRM' & HLOCK' & HWAKE' & HGS & _
      & HFOUND).
    assert (EHp' : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
    rewrite HspF, HFP1 in HJc. rewrite Hdrains in HGS.
    destruct (HFOUND j0 Hj0 ltac:(lia) Hfd)
      as (e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & rest0 & HDR & HSL & HREL' & HOUT' & HP1 & HP2).
    clear HFOUND.
    change (nth j0 (lm_es m) relay_remove_b_c.no_entry) with (rm_ent m j0) in HDR, HSL, HP1, HP2.
    rewrite <- Eop in HDR, HSL, HP1, HP2. rewrite <- HeqX in HP1.
    (* K4: what relay_remove keeps *)
    assert (Hsink : ~ YI16.sink_open_fp (ablocks_fp FL)).
    { apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hb.
      destruct (al_blocks_0 ly3 S3 W mem md p n HAR (HFL _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
    destruct (rm_kept_x cx fpos ly3 S3 W mem md k (G_RR B fr_RG) 0 [] RR_STK_x (ablocks_fp FL) ly' S' W' mem' md' k1
      HB HJ HJc (rr_G1 B G_fr HGlock HGnsrc HG_DR) ltac:(lia) (proj1 HSTK) (proj2 HSTK) Hsink)
      as (KIMG & KBLK & KSTK & KFR & HFFeq & _ & HAR').
    (* K2 / K3: its journal inside the arm's *)
    assert (Hbs : forall b, In b FL -> In b (model_blks m) /\ 0 < snd b).
    { intros b Hb. assert (Hm : In b (model_blks m)).
      { apply (Permutation_in _ (Permutation_sym PM)). rewrite HeqFL in Hb.
        destruct Hb as [<- | Hb]; [left; reflexivity | right]. rewrite !in_app_iff in Hb. rewrite !in_app_iff.
        destruct Hb as [Hb | [Hb | Hb]];
          [left; exact Hb
          | right; left; exact (Permutation_in _ (Permutation_sym HX) (in_or_app _ _ _ (or_introl Hb)))
          | right; right; right; exact Hb]. }
      split; [exact Hm | exact ((rr_blks_pos B) ly3 S3 W mem m b HMOD Hm)]. }
    pose proof (rm_compose_x cx fpos ly3 S3 W mem md k (G_RR B fr_RG) 0 [] RR_STK_x (ablocks_fp FL) ly' S' W' mem' md' k1
      HB HJ HJc (rr_G1 B G_fr HGlock HGnsrc HG_DR) ltac:(lia) (proj1 HSTK) (proj2 HSTK) (fun a Ha => False_ind _ (inFP_nil a Ha))
      ((rm_fp_sep B fr_FP) cx m ly3 S3 FL HSEP Hbs)) as HJ'.
    assert (HRV' : rom_view segs W' mem').
    { pose proof (ajournal_gx_G_mono0 (G_RR B fr_RG) G_fr 0 [] RR_STK_x (lf_F cx) (ablocks_fp FL)
        ly3 S3 W mem md [] ly' S' W' mem' md' k1 (rr_G1 B G_fr HGlock HGnsrc HG_DR) HJc) as HJG.
      exact (ajournal_gx_rom_view0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJG HRO HRV). }
    (* the live blocks after the call *)
    assert (HX' : Permutation (asrc_blks (if op then h1 else h)) ((if op then asrc_blks h1 else []) ++ Xc))
      by (rewrite HeqXc; destruct op; [rewrite app_nil_r|]; apply Permutation_refl).
    assert (PM' : Permutation (model_blks (rm_mk cx m si (Some (if op then h1 else h)) j0 c2 O2 cap2 out2))
      ((lm_G m, ATABLE) :: concat (map aentry_blks (relay_remove_b_c.remove_at j0 (lm_es m))) ++
       asrc_blks (if op then h1 else h) ++ OS ++ aout_blks cap2 out2)).
    { assert (Hsi' : (si < length (rm_set_nth si (Some (if op then h1 else h)) (lm_hs m)))%nat)
        by (rewrite rr_set_len; lia).
      pose proof (rr_mb_split (rm_mk cx m si (Some (if op then h1 else h)) j0 c2 O2 cap2 out2) si Hsi') as Q.
      unfold rm_mk in Q |- *. cbn [lm_hs lm_G lm_es lm_cap lm_out] in Q.
      rewrite rr_set_same in Q by lia. rewrite rr_set_set, <- HeqOS in Q. exact Q. }
    pose proof (rr_perm_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 HP1 HP2 HX' PM') as C2.
    (* the blocks relay_remove does not touch: in both states, every byte kept *)
    assert (KB : forall p n, In (p, n) (input_blks cx ++ Xc ++ OS) ->
                 In (p, n) (ablocks B ly' S') /\ forall a, p <= a < p + n -> abyte_kept W mem W' mem' a).
    { intros p n Hb.
      assert (Hin3 : In (p, n) (ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym C1)). right. rewrite !in_app_iff in Hb. rewrite !in_app_iff. tauto. }
      assert (Hin' : In (p, n) (ablocks B ly' S')).
      { apply (Permutation_in _ (Permutation_sym C2)). rewrite in_app_iff.
        rewrite !in_app_iff in Hb. destruct Hb as [Hb | Hb]; [left; exact Hb | right]. apply in_or_app. left.
        apply (Permutation_in _ (Permutation_sym PM')). right. rewrite !in_app_iff.
        destruct Hb as [Hb | Hb];
          [right; left; exact (Permutation_in _ (Permutation_sym HX') (in_or_app _ _ _ (or_intror Hb)))
          | right; right; left; exact Hb]. }
      split; [exact Hin'|].
      assert (Hnot : ~ In (p, n) FL).
      { rewrite HeqFL. apply (rr_notin _ _ _ _ _ _ _ HND C1). rewrite !in_app_iff in Hb. rewrite !in_app_iff. tauto. }
      intros a Ha.
      destruct (al_blocks_0 ly3 S3 W mem md p n HAR Hin3) as (_ & _ & _ & _ & _ & _ & Hn).
      assert (Hrq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
      replace a with (p + (a - p)) by lia.
      apply (KBLK p n (a - p)); [exact Hin3 | exact Hin' | lia |].
      apply (rr_nfp_x ly3 S3 W mem md FL p n); [exact HAR | exact HFL | exact Hin3 | exact Hnot | lia]. }
    (* g_s: every slot but si's when relay_remove drained it *)
    assert (KS : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC ->
                 ~ (op = true /\ rm_HA si <= a < rm_HA si + ASRC) -> abyte_kept W mem W' mem' a).
    { intros a Ha Hn. apply HGS; [exact Ha|]. intros Hop' Ha'. apply Hn. split; [exact Hop' | unfold rm_HA; exact Ha']. }
    (* the stack from F up *)
    assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
      by (intros a Ha; apply KSTK; [exact Ha | left; lia]).
    (* fuzz_reply's own globals outside relay_remove's G *)
    destruct ((rr_globs B HMG) W W' mem mem' KIMG) as (KGONE & KNFD & KTU & KLST).
    (* slot si after the call: drained (rr_found), or kept when the entry was at end of file *)
    assert (HSI : asrc_at B ly' S' W' mem' (rm_HA si) (if op then h1 else h)).
    { destruct op.
      - exact (proj2 HDR).
      - apply (rr_src_kept_x ly3 S3 W mem md ly' S' W' mem' (rm_HA si) h HAR HSRC).
        + intros a Ha. apply KS; [exact (rr_slot_in si a Hsi Ha) | intros [E _]; discriminate E].
        + intros p n Hb. apply KB. rewrite !in_app_iff. right; left. rewrite HeqXc. exact Hb. }
    assert (HOK : rm_rr_ok m h j0 e1 (if op then h1 else h) ev LB c2 O2 cap2).
    { unfold rm_rr_ok. cbv zeta. rewrite <- Eop. destruct op.
      - split; [exact (proj1 HDR) | exact HSL].
      - split; [split; [exact HDR | reflexivity] | exact HSL]. }
    (* the model after the call *)
    assert (HMOD' : amodel_at B ly' S' W' mem' (rm_mk cx m si (Some (if op then h1 else h)) j0 c2 O2 cap2 out2)).
    { unfold rm_mk, amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
      split; [rewrite rr_set_len; exact Hlen|].
      split.
      { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
        - rewrite rr_set_same by lia. exact HSI.
        - rewrite rr_set_other by congruence. pose proof (Hslots i Hi) as Hs. unfold aslot in Hs |- *.
          destruct (nth i (lm_hs m) None) as [h'|] eqn:Ei.
          + apply (rr_src_kept_x ly3 S3 W mem md ly' S' W' mem' _ h' HAR Hs).
            * intros a Ha. apply KS; [exact (rr_slot_in i a Hi Ha)|]. intros [_ Ha']. exact (rr_slot_disj i si a Hne Ha Ha').
            * intros p n Hb. apply KB. rewrite !in_app_iff. right; right. rewrite HeqOS.
              apply (rr_in_os (lm_hs m) si i (p, n)); [lia | exact Hne | rewrite Ei; exact Hb].
          + destruct Hs as [Hg Hw]. split.
            * apply (akept_garr8 W mem); [|exact Hg]. intros x Hx.
              rewrite repeat_length, Z2Nat.id in Hx by (unfold ASRC; lia).
              apply KS; [exact (rr_slot_in i x Hi Hx)|]. intros [_ Hx']. exact (rr_slot_disj i si x Hne Hx Hx').
            * apply (akept_awr W mem); [|exact Hw]. intros x Hx.
              apply KS; [exact (rr_slot_in i x Hi Hx)|]. intros [_ Hx']. exact (rr_slot_disj i si x Hne Hx Hx'). }
      split; [exact HREL'|].
      split; [exact HOUT'|].
      split.
      { destruct HGONE as (G1 & G2 & G3).
        split; [apply (akept_vm W mem); [intros x Hx; apply KGONE; change (Z.of_nat 1) with 1 in Hx; lia | exact G1]|].
        split; [apply (akept_awr W mem); [intros x Hx; apply KGONE; lia | exact G2] | exact G3]. }
      split; [exact HLOCK'|].
      split; [exact HWAKE'|].
      split; [apply (akept_vm W mem); [intros x Hx; apply KNFD; change (Z.of_nat 4) with 4 in Hx; lia | exact HNFD]|].
      split; [apply (akept_awr W mem); [intros x Hx; apply KNFD; lia | exact HNFDw]|].
      split; [exact HNFDr|].
      split; [apply (akept_vm W mem); [intros x Hx; apply KTU; change (Z.of_nat 1) with 1 in Hx; lia | exact HTU]|].
      split; [destruct HLST as (lst & HL); exists lst;
              apply (akept_vm W mem); [intros x Hx; apply KLST; change (Z.of_nat 4) with 4 in Hx; lia | exact HL]|].
      apply (akept_awr W mem); [intros x Hx; apply KLST; lia | exact HLSTw]. }
    (* the input block *)
    assert (HIN' : ainput_at B cx ly' S' W' mem').
    { destruct HIN as (I1 & I2).
      assert (Hinp : 0 < c_n cx -> In (c_p cx, c_n cx) (input_blks cx ++ Xc ++ OS)).
      { intros Hn. apply in_or_app. left. unfold input_blks.
        replace (c_n cx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      split.
      { destruct I1 as [I1 | (I1a & I1b)]; [left; exact I1 | right; split; [exact I1a|]].
        exact (proj1 (KB _ _ (Hinp ltac:(lia)))). }
      apply (akept_garr8 W mem); [|exact I2]. intros x Hx. rewrite length_map, <- HlenP in Hx.
      destruct I1 as [(Hn0 & _) | (Hn0 & _)]; [lia|].
      exact (proj2 (KB _ _ (Hinp ltac:(lia))) x Hx). }
    (* the registers *)
    assert (KR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r)
      by (intros r Hr; exact (rr_pres regs regs' r HPRES Hr)).
    assert (V8 : forall a v, lf_F cx <= a -> a + 8 <= 2 ^ 64 -> sv8 W mem a v -> sv8 W' mem' a v).
    { intros a v H1 H2 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv]. intros x Hx. apply KH. cbn in Hx. lia. }
    exists e1, (if op then h1 else h), ev, LB, c2, O2, cap2, out2.
    split; [exact HOK|].
    exists regs', mem', md', ly', S', (k + k1), fpos.
    split; [unfold cfg_at; rewrite R1, BASE_B0; reflexivity|].
    split; [exact (rr_jt W W' mem mem' HJT HRV HRV')|].
    split; [exact HJ'|].
    rewrite HFFeq.
    split.
    { apply (rr_aframe_kept cx (frame_addr ly3 1 fpos) W W' mem mem' HFR KH); [|lia|lia].
      intros a Ha. apply KFR.
      - unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        change (fs_frame_bytes 1) with 128. unfold SB in Ha. unfold SHADOW_OFF. lia.
      - exact (rr_nfp_fr_x ly3 S3 W mem md FL fpos a HAR HFL ltac:(rewrite Hfrs; left; reflexivity) Ha). }
    split.
    { rewrite (rm_flag_addr ly3 ly' fpos HFFeq). apply (rm_flag_kept W W' mem mem'); [|exact HFG].
      intros a Ha. apply KFR.
      - left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
      - exact (rr_nfp_fr_x ly3 S3 W mem md FL fpos a HAR HFL ltac:(rewrite Hfrs; left; reflexivity) (or_introl Ha)). }
    split; [exact HMOD'|].
    split; [exact HIN'|].
    split; [exact HRV'|].
    split; [exact (rm_sep_step_x cx fpos ly3 S3 W mem md k m _ ly' S' W' mem' md' restS HJ HSEP HAR' P0 C2)|].
    split; [exists ly3, S3; split; [exact HLS|]; split; [exact HMO|];
            split; [exact HMF0|]; split; [exists restS; split; [exact P0 | exact C2]|];
            split; [exact HCNT0 | exact HR3]|].
    split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
    unfold lregs_rmc, rm_regs_base. rewrite !KR by rr_cs.
    refine (conj (conj R2 (conj R8 (conj R9 (conj R18 (conj R19 (conj R23 (conj R24 (conj R25 (conj R26
      (conj R3 (conj R4 (conj R27 Rt)))))))))))) (conj R20 (conj R21 (conj R22 (conj _ _))))).
    + apply V8; [lia | lia | exact R144].
    + apply V8; [lia | lia | exact R192].
Qed.
(* (5) check_no_loss(s, &at) *)
Lemma cn_ablocks_nodup_x : forall ly S (W : world segs) mem md, AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (al_sep_0 ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
  { intros [p n] Hb. destruct (al_blocks_0 ly S W mem md p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
    exact (proj1 (req_size_pos n ltac:(lia))). }
  revert Hp Hpos. generalize (ablocks B ly S) as l. induction l as [|b l IH]; intros Hp Hpos; [constructor|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp].
  constructor.
  - intros Hin. rewrite Forall_forall in Hf.
    specialize (Hf (fst b, req_size (snd b)) (in_map (fun b0 => (fst b0, req_size (snd b0))) l b Hin)).
    pose proof (Hpos b (or_introl eq_refl)). unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
  - apply IH; [exact Hp | intros b' Hb'; apply Hpos; right; exact Hb'].
Qed.
(* a block outside the callee's lists L1 is live after it (L1' is what the lists hold after) and its bytes are
   kept (K4's block clause; it is apart from every block of L1) *)
Lemma cn_keep_y_x : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' L1 L1' Y,
  AR0 ly S W mem md ->
  Permutation (ablocks B ly S) (L1 ++ Y) -> Permutation (ablocks B ly' S') (L1' ++ Y) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP (blk_FP L1) (p + i) -> abyte_kept W mem W' mem' (p + i)) ->
  forall b, In b Y -> In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a).
Proof.
  intros ly S W mem md ly' S' W' mem' L1 L1' Y HAR Hp Hp' KB [p n] Hb.
  assert (Hin3 : In (p, n) (ablocks B ly S))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hp | apply in_or_app; right; exact Hb]).
  assert (Hin' : In (p, n) (ablocks B ly' S'))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hp' | apply in_or_app; right; exact Hb]).
  split; [exact Hin'|]. cbn [fst snd]. intros a Ha.
  assert (Hnd : List.NoDup (L1 ++ Y)) by (eapply Permutation_NoDup; [exact Hp | exact (cn_ablocks_nodup_x ly S W mem md HAR)]).
  replace a with (p + (a - p)) by lia.
  apply (KB p n (a - p)); [exact Hin3 | exact Hin' | unfold req_size; destruct (Z.eqb_spec n 0); lia |].
  intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q k] & <- & Hq). cbn [fst snd] in Hra.
  assert (Hq3 : In (q, k) (ablocks B ly S))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hp | apply in_or_app; left; exact Hq]).
  assert (Hne : (q, k) <> (p, n)) by (intros E; rewrite E in Hq; exact (cn_nodup_app _ _ _ (p, n) Hnd Hq Hb)).
  pose proof (sep_blocks0 ly S W mem md q k p n HAR Hq3 Hin3 Hne) as Hd.
  destruct (al_blocks_0 ly S W mem md q k HAR Hq3) as (_ & _ & _ & _ & _ & _ & Hk0).
  pose proof (req_size_pos k (proj1 Hk0)) as [Rk _].
  assert (Rn : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rn in Hd. clear - Hd Ha Hra Rk. lia.
Qed.
(* the frame and its shadow are no byte of a live block *)
Lemma cn_frame_not_fp_x : forall ly S (W : world segs) mem md L1 cid pos a,
  AR0 ly S W mem md -> In (cid, pos) (frames S) -> (forall b, In b L1 -> In b (ablocks B ly S)) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP (blk_FP L1) a.
Proof.
  intros ly S W mem md L1 cid pos a HAR Hin HL1 Hr (r & Hr1 & Hra).
  unfold blk_FP in Hr1. apply in_map_iff in Hr1 as ([b m] & <- & Hb). cbn [fst snd] in Hra.
  pose proof (HL1 _ Hb) as Hbin.
  destruct (frames_bounds0 ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
  destruct (al_blocks_0 ly S W mem md b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame0 ly S W mem md b m cid pos HAR Hbin Hin) as Hd.
  unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr.
  pose proof asan_consts as (C1 & _). pose proof (fs_frame_bytes_nonneg cid) as Hfn.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
  pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
  pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  destruct Hr as [Hr|Hr]; zlia.
Qed.

(* ---- bytes kept across the call ---- *)
(* a byte stays writable when it stays present: where it is not present, writability is the segment's
   (W_check_no_loss.v nls_awr_kept) *)
Lemma cn_aslot_kept_x : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' i o,
  AR0 ly S W mem md -> aslot B ly S W mem i o ->
  (forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
     abyte_kept W mem W' mem' a) ->
  (forall b, In b (slot_blks o) ->
     In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  aslot B ly' S' W' mem' i o.
Proof.
  intros ly S W mem md ly' S' W' mem' i o HAR Hs KH KBk. destruct o as [h|]; cbn [aslot slot_blks] in *.
  - apply (asrc_at_kept B ly S W mem); [exact Hs | | intros b Hb; exact (proj1 (KBk b Hb))].
    intros r Hr a Ha. destruct (rm_asrc_fp_in_x ly S W mem md _ h HAR Hs r Hr a Ha) as [Hg | (p & n & Hpn & Hpa)].
    + apply KH. exact Hg.
    + exact (proj2 (KBk (p, n) Hpn) a Hpa).
  - destruct Hs as [Hg Hw]. split.
    + apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. rewrite repeat_length in Hx.
      change (Z.of_nat (Z.to_nat ASRC)) with ASRC in Hx. apply KH. exact Hx.
    + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KH. exact Hx.
Qed.
Lemma cn_arelay_kept_x : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' G es,
  AR0 ly S W mem md -> arelay_at B fr_RG ly S W mem G es ->
  (forall a, rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
     rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (arelay_blks G es) ->
     In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  arelay_at B fr_RG ly' S' W' mem' G es.
Proof.
  intros ly S W mem md ly' S' W' mem' G es HAR Hr KG KBk.
  apply (arelay_at_kept B fr_RG ly S W mem); [exact Hr | | intros b Hb; exact (proj1 (KBk b Hb))].
  intros r Hin a Ha. destruct (rm_arelay_fp_in_x ly S W mem md G es HAR Hr r Hin a Ha) as [Hg | (p & n & Hpn & Hpa)].
  - apply KG. exact Hg.
  - exact (proj2 (KBk (p, n) Hpn) a Hpa).
Qed.

(* ---- the image cells the model reads, outside slot si: image, not the allocator's, not errno (HMG, RGP) ---- *)
Lemma cn_model_kept_x : forall cx m si h1 h1' j0 c ev O cap out ly S (W : world segs) mem md ly' S' (W' : world segs) mem',
  AR0 ly S W mem md -> (si < 4)%nat ->
  amodel_at B ly S W mem (rm_mk cx m si (Some h1) j0 c O cap out) ->
  asrc_at B ly' S' W' mem' (rm_HA si) h1' ->
  (forall a, (rm_mglob a \/ rg_rng fr_RG a) -> ~ (rm_HA si <= a < rm_HA si + ASRC) -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (cn_rest m si j0 cap out) ->
     In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  amodel_at B ly' S' W' mem' (rm_mk cx m si (Some h1') j0 (rm_cev c ev) O cap out).
Proof.
  intros cx m si h1 h1' j0 c ev O cap out ly S W mem md ly' S' W' mem' HAR Hsi HMOD HSRC KG KY Hev Hew Hevr.
  assert (KGm : forall a, rm_mglob a -> abyte_kept W mem W' mem' a).
  { intros a Ha. apply KG; [left; exact Ha|]. pose proof (cn_mglob_out_s a Ha) as Ho. clear - Ho Hsi.
    unfold rm_HA, ASRC in *. lia. }
  assert (KGr : forall a, (rg_lock fr_RG <= a < rg_lock fr_RG + 12 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
      rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8) ->
      abyte_kept W mem W' mem' a).
  { intros a Ha. apply KG.
    - right. unfold rg_rng. tauto.
    - pose proof (cn_rg_out_s a Ha) as Ho. clear - Ho Hsi. unfold rm_HA, ASRC in *. lia. }
  assert (KGs : forall i, (i < 4)%nat -> i <> si -> forall a,
      rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC -> abyte_kept W mem W' mem' a).
  { intros i Hi Hne a Ha. apply KG.
    - right. unfold rg_rng. right; right; right; right. clear - Ha Hi. unfold ASRC in *. lia.
    - clear - Ha Hi Hsi Hne. unfold rm_HA, ASRC in *. lia. }
  unfold rm_mk in HMOD |- *. unfold amodel_at in HMOD |- *.
  cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd] in HMOD |- *.
  destruct HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  rewrite cn_rsn_length in M1.
  assert (KYs : forall i h b, (i < 4)%nat -> nth i (rm_set_nth si None (lm_hs m)) None = Some h ->
     In b (asrc_blks h) ->
     In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros i h b Hi Hn Hb. apply KY. unfold cn_rest. right. apply in_or_app. right. apply in_or_app. left.
    apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
    rewrite <- Hn. apply in_map. apply nth_In. rewrite cn_rsn_length. lia. }
  split; [rewrite cn_rsn_length; exact M1|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
    - rewrite cn_rsn_same by lia. cbn [aslot]. exact HSRC.
    - rewrite cn_rsn_other by lia. pose proof (M2 i Hi) as Mi. rewrite cn_rsn_other in Mi by lia.
      apply (cn_aslot_kept_x ly S W mem md ly' S' W' mem' i _ HAR Mi).
      + exact (KGs i Hi Hne).
      + intros b Hb. destruct (nth i (lm_hs m) None) as [h|] eqn:En; [|cbn in Hb; destruct Hb].
        apply (KYs i h b Hi); [rewrite cn_rsn_other by lia; exact En | exact Hb]. }
  split.
  { apply (cn_arelay_kept_x ly S W mem md ly' S' W' mem' _ _ HAR M3).
    - intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
      + apply KGr. right; right; left. exact Ha.
      + apply KGr. right; left. exact Ha.
      + apply KGm. unfold rm_mglob. left. exact Ha.
    - intros b Hb. apply KY. unfold cn_rest. unfold arelay_blks in Hb.
      destruct Hb as [<- | Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb]. }
  split.
  { apply ((cn_aout_kept B) ly S W mem ly' S' W' mem' _ _ _ _ _ _ ev M4); [| |exact Hev|exact Hew|exact Hevr].
    - intros a Ha. apply KGm. unfold rm_mglob. tauto.
    - intros b Hb. apply KY. unfold cn_rest. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r [<- | []] a Ha. apply KGm. unfold rm_mglob.
    cbn [fst snd] in Ha. tauto. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r [<- | []] a Ha. apply KGr. cbn [fst snd] in Ha. tauto. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r [<- | []] a Ha. apply KGr. cbn [fst snd] in Ha. tauto. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KGm. unfold rm_mglob.
    assert (AG_NFD <= x < AG_NFD + 4) by lia. tauto. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KGm. unfold rm_mglob. tauto. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KGm. unfold rm_mglob.
    assert (AG_THREAD_UP <= x < AG_THREAD_UP + 1) by lia. tauto. }
  split.
  { destruct M12 as [lst Hl]. exists lst. apply (akept_vm W mem); [|exact Hl]. intros x Hx. apply KGm.
    unfold rm_mglob. assert (AG_LISTEN <= x < AG_LISTEN + 4) by lia. tauto. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KGm. unfold rm_mglob. tauto.
Qed.

(* ---- the read-only image: the jump table and gesture_model's three literals (fuzz_reply.asan's first segment
   [0x10000, 0x30000) is read-only; vm_compute over pa_segs PB_fr) ---- *)
Lemma cn_out_pre_x : forall cx m si h1 j0 c O cap out ly S (W : world segs) mem md,
  AR0 ly S W mem md -> (si < 4)%nat ->
  amodel_at B ly S W mem (rm_mk cx m si (Some h1) j0 c O cap out) ->
  ablocks_sep B fr_FP cx (rm_mk cx m si (Some h1) j0 c O cap out) ly S ->
  asrc_at B ly S W mem (rm_HA si) h1 /\
  val_mem segs (arm W mem) (VAL A_g_gone) 1 (lm_gn m) /\ 0 <= lm_gn m < 256 /\
  val_mem segs (arm W mem) (VAL A_g_nout) 8 (Z.of_nat (length O)) /\ val_mem segs (arm W mem) (VAL A_g_out) 8 out /\
  ob_at W mem out O /\ amem_range out (Z.of_nat (length O) + 8) /\
  (O = [] \/ exists CO, Z.of_nat (length O) <= CO /\ In (out, CO) (ablocks B ly S) /\ ~ In out (hs_blocks h1)).
Proof.
  intros cx m si h1 j0 c O cap out ly S W mem md HAR Hsi HMOD HSEP.
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & _).
  unfold rm_mk in M1, M2, M4, M5. cbn [lm_hs lm_c lm_O lm_mx lm_cap lm_out lm_gn] in M1, M2, M4, M5.
  rewrite cn_rsn_length in M1.
  assert (Hsil : (si < length (lm_hs m))%nat) by lia.
  split.
  { pose proof (M2 si Hsi) as Ms. rewrite cn_rsn_same in Ms by lia. exact Ms. }
  destruct M5 as (G1 & _ & G3).
  replace (VAL A_g_gone) with (rg_gone fr_RG) by (vm_compute; reflexivity).
  replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity).
  replace (VAL A_g_out) with (rg_out fr_RG) by (vm_compute; reflexivity).
  split; [exact G1|]. split; [clear - G3; lia|].
  pose proof M4 as (_ & _ & O3 & _ & _ & _ & O7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & O26).
  split; [exact O3|]. split; [exact O7|].
  destruct O26 as [(Hc & Ho & Hn) | (Hc & Hno & Hin & junk & Hj & Hg)].
  - assert (HO : O = []) by (destruct O as [|x O]; [reflexivity | cbn [length] in Hn; lia]).
    subst O out. split; [intros i Hi; cbn [length] in Hi; lia|].
    split; [unfold amem_range, kLowMemEnd; cbn [length]; lia|]. left; reflexivity.
  - split; [exact (cn_ob_of_garr8 W mem out O junk Hg)|].
    destruct (al_blocks_0 ly S W mem md out cap HAR Hin) as (_ & H4096 & Hceil & Hap & _).
    assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
    rewrite Hrq in Hceil, Hap. pose proof asan_consts as (C1 & _).
    split.
    { clear - Hap Hceil C1 Hno.
      unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
    right. exists cap. split; [exact Hno|]. split; [exact Hin|].
    intros Hh. destruct (cn_hs_blocks_in h1 out Hh) as ([p n] & Hb & Hfb). cbn [fst] in Hfb. subst p.
    destruct HSEP as [[rest Hp] _].
    assert (Hp' : Permutation (ablocks B ly S) (input_blks cx ++ (asrc_blks h1 ++ cn_rest m si j0 cap out) ++ rest)).
    { eapply Permutation_trans; [exact Hp|]. apply Permutation_app_head. apply Permutation_app_tail.
      exact (cn_model_perm cx m si (Some h1) j0 c O cap out Hsil). }
    assert (Hnd : List.NoDup (input_blks cx ++ (asrc_blks h1 ++ cn_rest m si j0 cap out) ++ rest))
      by (eapply Permutation_NoDup; [exact Hp' | exact (cn_ablocks_nodup_x ly S W mem md HAR)]).
    assert (Hoc : In (out, cap) (cn_rest m si j0 cap out)).
    { unfold cn_rest. right. apply in_or_app. right. apply in_or_app. right. unfold aout_blks.
      replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left; reflexivity. }
    assert (Hne : (out, n) <> (out, cap)).
    { intros E. rewrite E in Hb. apply cn_nodup_r in Hnd. rewrite <- app_assoc in Hnd.
      exact (cn_nodup_app _ _ _ (out, cap) Hnd Hb (in_or_app _ _ _ (or_introl Hoc))). }
    assert (Hb3 : In (out, n) (ablocks B ly S)).
    { eapply Permutation_in; [apply Permutation_sym; exact Hp'|].
      apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact Hb. }
    pose proof (sep_blocks0 ly S W mem md out n out cap HAR Hb3 Hin Hne) as Hd.
    destruct (al_blocks_0 ly S W mem md out n HAR Hb3) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos n (proj1 Hn0)) as [Rn _]. pose proof (req_size_pos cap ltac:(lia)) as [Rc _].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Rn Rc. lia.
Qed.
Lemma cn_nums_x : forall cx ly3 S3 (W : world segs) mem md k fpos,
  lf_base0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) <= 2 ^ 47 /\ lf_F cx mod 32 = 0 /\
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\
  4096 <= frame_addr ly3 1 fpos /\ frame_addr ly3 1 fpos + 128 <= alloc_ceiling /\
  frames S3 = [(1, fpos)] /\ AR0 ly3 S3 W mem md.
Proof.
  intros cx ly3 S3 W mem md k fpos (HAI & HPRE) HJ.
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
  pose proof (ajournal_gx_AR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  rewrite !Z.add_0_r in *.
  destruct HSTK as (Hal & _ & Hceil & Hlo & Hhi & H47 & _).
  rewrite Hfr0, app_nil_r in Hfrs.
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frames_bounds0 _ _ _ _ _ 1 fpos HAR Hin) as (H4 & Hc & _).
  change (fs_frame_bytes 1) with 128 in Hc.
  unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)).
  split; [exact Hal|]. split; [unfold LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Hfrs|exact HAR].
Qed.

(* ---- the 3-instruction walk 0x849ec: a1 = F + 192, a0 = s5, jal check_no_loss (no memory read) ---- *)
(* cn_RUNTO: a run of a segment lifted to R (its callee a strict leaf); cn_RUNTOG: a run at R (paj_run_to_x_xG), up
   to a freeing callee taken at R *)
Let cn_RUNTO := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let cn_RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Ltac cn_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac cn_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac cn_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* check_no_loss frees: the walk runs at R up to the call, CNL_R's R journal is composed by rm_compose_x *)
Lemma rm_cnl_xR : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 ev1 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  RCUT_x cx (rm_mk cx m si (Some h1) j0 (rm_cev c2 ev1) O2 cap2 out2)
    ((rm_Qc h j0) cx t m (rm_mk cx m si (Some h1) j0 (rm_cev c2 ev1) O2 cap2 out2) ((rm_rr_cost MT) m h))
    ((lregs_rmc B) cx t m si j0 0) A_rm_cnl W c ->
  SRrG segs R W c (fun W' c' => exists E' H' ev2, rm_cnl_ok h1 E' H' /\
    RCUT_x cx (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2)
      ((rm_Qc h j0) cx t m (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2)
        ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1)))
      ((lregs_rmc B) cx t m si j0 (rm_A1 m h1)) A_rm_cshe W' c').
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 ev1 W c HB HRI HAT HRR HRC.
  destruct HRC as (regs & mem & md & ly3 & S3 & k & fpos & -> & HROM & HJ & HFR & HFL & HMOD & HIN & HRV & HSEP & HQ & HNP & HR).
  pose proof HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Rt) & R20 & R21 & R22 &
    R144 & R192).
  assert (Hsi : (si < 4)%nat) by (destruct HAT as (_ & _ & _ & _ & Hs & _); exact Hs).
  (* ---- the walk to check_no_loss's entry ---- *)
  destruct (cn_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs cn_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs cn_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + A_rm_cnl)) with (Z_to_bv 64 (BASE + A_rm_cnl)).
  paj_run_to_tok_xR cn_RUNTOG HS HJ SHOK cn_span AF_fr_check_no_loss.
  { apply awr_ok_x_nil. }
  pmkst HS.
  cn_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs cn_extra cn_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  clear HS SHOK HF HFr.
  (* ---- the frame's numbers and the call's registers ---- *)
  destruct (cn_nums_x cx ly3 S3 W mem mdc k fpos HB HJ) as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & Hfrs & HAR).
  pose proof asan_consts as (C1 & _).
  assert (HFn : alloc_ceiling + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) <= 2 ^ 47)
    by (unfold LLVMF_STK in Hsp0; lia).
  assert (Q10' : getr (ms_regs ms) 10 = w64 (rm_HA si)) by (rewrite Q10, (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (Q11' : getr (ms_regs ms) 11 = w64 (lf_F cx + 192)).
  { rewrite Q11, (EEo 9%nat 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (HCS : 0 <= CNL_STK /\ CNL_STK + 352 <= LLVMF_STK) by (split; vm_compute; intro Hc; discriminate Hc).
  (* K1: check_no_loss's afn_pre *)
  destruct (rm_afn_pre_at_x cx true ly3 S3 fpos k W mem mdc (ms_regs ms) CNL_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { exact (proj1 HCS). }
  { exact (proj2 HCS). }
  (* the arm's journal: the stack below the entry sp is present, ly_top is the entry's *)
  destruct (ajournal_gx_inner0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc k HJ) as (memS & HJ0 & _).
  rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  assert (Etop : ly_top ly3 = ly_top (c_ly cx)) by (pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
  assert (Htop : spZ (c_regs cx) <= ly_top (c_ly cx)) by (pose proof Hstk as (_ & _ & _ & _ & _ & _ & _ & Ht & _); exact Ht).
  clear Hly Hstk HJ0.
  (* ---- check_no_loss's G: slot si's expected and held heads ---- *)
  set (Gc := [(rm_HA si + 64, 32)]).
  assert (HGc : forall a, inG Gc a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
  { intros a Ha. unfold Gc, inG in Ha. apply Exists_exists in Ha as (r & [<- | []] & Hz). unfold in_zr in Hz.
    cbn [fst snd] in Hz. clear - Hz Hsi. unfold rm_HA, ASRC in *. lia. }
  assert (HGok : gx_ok segs B Gc) by (intros a Ha; exact (HG a (HGs a (HGc a Ha)))).
  assert (HGrt : gx_rt B Gc).
  { eapply gx_rt_sub; [|exact HGRT_s]. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact (HGc a Ha). }
  pose proof (CNL_R Gc HGok HGrt) as HCNL.
  (* ---- the premises ---- *)
  assert (P4 : spZ (ms_regs ms) + 208 <= ly_top ly3) by (rewrite Hsp1, Etop; lia).
  assert (P5 : forall a, spZ (ms_regs ms) <= a < spZ (ms_regs ms) + 208 -> apresent (w_H W) mem a)
    by (intros a Ha; apply Hpres; rewrite Hsp1 in Ha; unfold LLVMF_STK; lia).
  assert (P8 : rm_HA si = VAL A_g_s + ASRC * Z.of_nat si) by (unfold rm_HA; f_equal; vm_compute; reflexivity).
  assert (P10 : (lf_F cx + 192) mod 8 = 0).
  { clear - HF32. pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 192) with ((4 * (lf_F cx / 32) + 24) * 8) by ring. apply Z_mod_mult. }
  assert (P11 : spZ (ms_regs ms) <= lf_F cx + 192) by (rewrite Hsp1; lia).
  assert (P12 : lf_F cx + 192 + 8 <= spZ (ms_regs ms) + 208) by (rewrite Hsp1; lia).
  assert (P14 : forall a, rm_HA si + 64 <= a < rm_HA si + 96 -> inG Gc a)
    by (intros a Ha; unfold Gc, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
  assert (P15 : azs B (rm_HA si + 64) 32).
  { apply ((cn_azs_sub B) (rg_s fr_RG) (4 * ASRC)); [exact HZS | |]; clear - Hsi; unfold rm_HA, ASRC; lia. }
  assert (P20 : 0 <= 0 <= Z.of_nat (length O2)) by lia.
  assert (HSRC1 : asrc_at B ly3 S3 W mem (rm_HA si) h1)
    by exact (proj1 (cn_out_pre_x cx m si h1 j0 (rm_cev c2 ev1) O2 cap2 out2 ly3 S3 W mem mdc HAR Hsi HMOD HSEP)).
  eapply SRrG_mono.
  { destruct (cn_out_pre_x cx m si h1 j0 (rm_cev c2 ev1) O2 cap2 out2 ly3 S3 W mem mdc HAR Hsi HMOD HSEP)
      as (_ & P21 & P22 & P23 & P24 & P25 & P29 & P30).
    destruct HQ as (ly0 & S0 & HLS & HLE & HMF & HFR0 & HC0 & HR3).
    pose proof HMF as (HMP & HK14 & _).
    destruct (RI_rm_cnl_pre cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI HAT HRR HK14) as (P16 & P17 & P18 & P38 & PO & P31).
    (* the removed entry's partial line fits APARTIAL (rm3_pre's fourth conjunct) and Rt is lregs_rmc's t bound *)
    pose proof HR3 as (_ & _ & _ & HU & _).
    destruct (LS_rm_cnl_pre cx t m ly0 S0 S3 si h j0 e1 h1 ev LB c2 O2 cap2 ly3 out2 HLS HRI HAT HRR Rt HU HLE HMP
      (rm_fr_all B _ _ _ _ _ _ _ HFR0)) as (P36 & P37).
    destruct ((cn_lits XM_LIB XN_LIB RLO HAP) W mem HRV) as (P33 & P34 & P35).
    apply (HCNL W ly3 S3 [] (ms_regs ms) mem mdc ch 208 (rm_HA si) si (lf_F cx + 192) h1 (lm_gn m) 0
      (Z.of_nat (length O2)) out2 O2 HPREc ltac:(lia) eq_refl P4 P5 Q10' Q11' P8 Hsi P10 P11 P12 HSRC1 P14 P15
      P16 P17 P18 R192 P20 P21 P22 P23 P24 P25 eq_refl ltac:(lia) ltac:(lia) P29 P30) with (kr := 0%nat);
      [| exact HRV | exact P33 | exact P34 | exact P35 | exact P36 | exact P37
      | apply RP_NP; exact HNP
      | exact (rm_cnt_step cx ly0 S0 m _ ly3 S3 _ _ HFR0
          (fun P => RM_CNT_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 P HRI HAT HRR HMF HR3
             (RI_rm_src cx t m si h j0 HRI HAT)) HC0)
      | exact P38
      | intros a Ha; rewrite Hsp1 in Ha; exact (rm_stkr_x cx ly3 S3 fpos k W mem mdc HB HJ a Ha)].
    intros Hg. destruct (P31 Hg) as (rest & Hr). exists rest. exact Hr. }
  (* ---- after check_no_loss ---- *)
  cbv beta. intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & kk & E' & H' & -> & HJc & HPR & HPK & _ & HSRC &
    HE1 & HE2 & HE3 & HH1 & HH2 & HH3 & HAT' & _ & _ & _ & _ & HPERM & HFRS & HMO & HRM' & _).
  assert (EHp' : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
  assert (HOK : rm_cnl_ok h1 E' H') by exact (conj HE1 (conj HE2 (conj HE3 (conj HH1 (conj HH2 HH3))))).
  clear HE1 HE2 HE3 HH1 HH2 HH3.
  rewrite Hsp1 in HJc.
  set (L1 := list_blks (hs_expected h1) ++ list_blks (hs_held h1)) in *.
  set (m1 := rm_mk cx m si (Some h1) j0 (rm_cev c2 ev1) O2 cap2 out2) in *.
  assert (Hsil : (si < length (lm_hs m))%nat).
  { pose proof HMOD as (M1 & _). unfold m1, rm_mk in M1. cbn [lm_hs] in M1. rewrite cn_rsn_length in M1. lia. }
  pose proof HSEP as [[rest0 Hp3] _].
  set (P0 := (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1)).
  set (RB := cn_rest m si j0 cap2 out2).
  assert (HM1 : Permutation (model_blks m1) ((list_blks (hs_expected h1) ++ list_blks (hs_held h1) ++ P0) ++ RB)).
  { eapply Permutation_trans; [exact (cn_model_perm cx m si (Some h1) j0 (rm_cev c2 ev1) O2 cap2 out2 Hsil)|].
    apply Permutation_app_tail. exact (cn_asrc_perm h1). }
  (* K2 / K4's premises *)
  assert (HG1 : forall a, inG Gc a -> inG G_fr a) by (intros a Ha; exact (HGs a (HGc a Ha))).
  assert (HOUT : forall a, inFP [(lf_F cx + 192, lf_F cx + 192 + 8)] a -> lf_F cx <= a < lf_F cx + 208).
  { intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
  assert (HL1a : forall b, In b L1 -> In b (model_blks m1)).
  { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HM1|]. apply in_or_app. left.
    rewrite app_assoc. apply in_or_app. left. exact Hb. }
  assert (HL1m : forall b, In b L1 -> In b (model_blks m1) /\ 0 < snd b).
  { intros b Hb. split; [exact (HL1a b Hb)|].
    pose proof HSRC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HLE & HLH & _).
    unfold L1 in Hb. apply in_app_or in Hb as [Hb | Hb].
    - exact (cn_list_blks_pos _ ((cn_alist_cap B) _ _ _ _ _ _ _ HLE) b Hb).
    - exact (cn_list_blks_pos _ ((cn_alist_cap B) _ _ _ _ _ _ _ HLH) b Hb). }
  assert (HL13 : forall b, In b L1 -> In b (ablocks B ly3 S3)).
  { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hp3|]. apply in_or_app. right.
    apply in_or_app. left. exact (HL1a b Hb). }
  pose proof ((rm_fp_sep B fr_FP) cx m1 ly3 S3 L1 HSEP HL1m) as HFP.
  assert (Hsink : ~ YI16.sink_open_fp (blk_FP L1)).
  { intros (r & Hr & Hra). destruct (HFP 0 (ex_intro _ r (conj Hr Hra))) as (b & n & Hb & Hba & _).
    destruct (al_blocks_0 ly3 S3 W mem mdc b n HAR Hb) as (_ & H4096 & _). clear - Hba H4096. lia. }
  pose proof (rm_compose_x cx fpos ly3 S3 W mem mdc k Gc 208 [(lf_F cx + 192, lf_F cx + 192 + 8)] CNL_STK (blk_FP L1)
    ly' S' W' mem' md' kk HB HJ HJc HG1 ltac:(lia) (proj1 HCS) (proj2 HCS) HOUT HFP) as HJ'.
  destruct (rm_kept_x cx fpos ly3 S3 W mem mdc k Gc 208 [(lf_F cx + 192, lf_F cx + 192 + 8)] CNL_STK (blk_FP L1)
    ly' S' W' mem' md' kk HB HJ HJc HG1 ltac:(lia) (proj1 HCS) (proj2 HCS) Hsink) as (KA & KB & KC & KD & KE & KF & KAR).
  (* errno after the call *)
  destruct (ERR ly' S' [] W' mem' md' KAR) as ((ev2 & Hev & Hevr) & Hew).
  exists E', H', ev2. split; [exact HOK|]. clear HOK.
  (* the blocks: the lists' before and after, and the rest Y the call keeps *)
  pose proof (Permutation_trans Hp3 (cn_perm_out (input_blks cx) (model_blks m1) (list_blks (hs_expected h1))
    (list_blks (hs_held h1)) P0 RB rest0 HM1)) as Hp3'.
  pose proof (HPERM _ Hp3') as Hp'.
  assert (HM2 : Permutation (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2))
      ((list_blks E' ++ list_blks H' ++ P0) ++ RB)).
  { eapply Permutation_trans;
      [exact (cn_model_perm cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2 Hsil)|].
    apply Permutation_app_tail. exact (cn_asrc_perm (set_exp_held h1 E' H')). }
  pose proof (cn_perm_in _ (input_blks cx) _ (list_blks E') (list_blks H') P0 RB rest0 HM2 Hp') as Hp''.
  pose proof (rm_sep_step_x cx fpos ly3 S3 W mem mdc k m1
    (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2) ly' S' W' mem' md' rest0
    HJ HSEP KAR Hp3 Hp'') as HSEP'.
  rewrite app_assoc in Hp3', Hp'.
  pose proof (cn_keep_y_x ly3 S3 W mem mdc ly' S' W' mem' L1 (list_blks E' ++ list_blks H')
    (P0 ++ input_blks cx ++ RB ++ rest0) HAR Hp3' Hp' KB) as KY.
  assert (KYR : forall b, In b RB ->
      In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros b Hb. apply KY. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (KYI : forall b, In b (input_blks cx) ->
      In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros b Hb. apply KY. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  (* the image cells outside slot si: their view (K4) and their presence (apres_kept) *)
  assert (KG : forall a, (rm_mglob a \/ rg_rng fr_RG a) -> ~ (rm_HA si <= a < rm_HA si + ASRC) ->
      abyte_kept W mem W' mem' a).
  { intros a Ha Hns. destruct ((cn_glob_facts B RGP HMG) a Ha) as (I1 & I2 & I3).
    split; [exact (proj1 (KA a I1 (cn_notG si a Hns) I2 I3))|].
    apply cn_awr_kept. exact (HPK a I1 I2 I3). }
  (* ---- the cut at 0x849f8 ---- *)
  assert (HMOD' : amodel_at B ly' S' W' mem'
      (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2))
    by exact (cn_model_kept_x cx m si h1 (set_exp_held h1 E' H') j0 (rm_cev c2 ev1) ev2 O2 cap2 out2 ly3 S3 W mem mdc
      ly' S' W' mem' HAR Hsi HMOD HSRC KG KYR Hev Hew Hevr).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFR' : aframe_at cx true (frame_addr ly' 1 fpos) W' mem').
  { rewrite KE. apply (cn_aframe_kept cx true (frame_addr ly3 1 fpos) W W' mem mem' HFR).
    - intros a Ha Hn. apply KC; [exact Ha|]. right. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
    - intros a Ha.
      destruct (ajournal_gx_inner0 Gc 208 [(lf_F cx + 192, lf_F cx + 192 + 8)] CNL_STK (lf_F cx) (blk_FP L1)
        ly3 S3 W mem mdc [] ly' S' W' mem' md' kk HJc) as (memS2 & HJi2 & _).
      pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
      apply (apresent_writable segs (w_H W') mem' a). apply Hpres2. pose proof (proj1 HCS). lia.
    - intros a Ha. apply KD.
      + left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
      + apply (cn_frame_not_fp_x ly3 S3 W mem mdc L1 1 fpos a HAR Hin1 HL13). left.
        unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
    - intros a Ha.
      assert (Hs : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
      { unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        cbv [SB SHADOW_OFF] in Ha |- *. lia. }
      apply KD; [right; exact Hs|].
      exact (cn_frame_not_fp_x ly3 S3 W mem mdc L1 1 fpos a HAR Hin1 HL13 (or_intror Hs)).
    - lia.
    - lia. }
  assert (HFL' : sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { rewrite KE, (rm_flag_addr ly3 ly' fpos KE). apply (rm_flag_kept W W' mem mem'); [|exact HFL].
    intros a Ha. apply KD.
    - left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
    - apply (cn_frame_not_fp_x ly3 S3 W mem mdc L1 1 fpos a HAR Hin1 HL13). left.
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia. }
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx)))
    by (destruct HB as (_ & HPRE0); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE0))))))).
  pose proof ((cn_input_kept B) cx ly3 S3 W mem ly' S' W' mem' HIN (eq_sym HlenP) KYI) as HIN'.
  assert (HRV' : rom_view segs W' mem').
  { pose proof (ajournal_gx_G_mono0 Gc G_fr 208 [(lf_F cx + 192, lf_F cx + 192 + 8)] CNL_STK (lf_F cx)
      (blk_FP L1) ly3 S3 W mem mdc [] ly' S' W' mem' md' kk HG1 HJc) as HJcG.
    exact (ajournal_gx_rom_view0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJcG HRO HRV). }
  assert (HQ' : (rm_Qc h j0) cx t m (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2)
      ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1)) ly' S').
  { destruct HQ as (ly0 & S0 & HLS & HLE & HMF & HFR0 & HC0 & HR3). exists ly0, S0. split; [exact HLS|].
    split; [exact (mo_le_trans MT ML _ _ _ _ _ HLE HMO)|]. split; [exact HMF|].
    split; [exact (rm_fr_step B _ _ _ _ _ _ _ _ _ _ rest0 HFR0 Hp3 Hp'')|]. split; [exact HC0 | exact HR3]. }
  assert (KRR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r cn_kept -> getr regs' r = getr regs r).
  { intros r H1 H2. pose proof (HPR _ H1) as Hp. rewrite !Z_to_bv_bv_unsigned in Hp. rewrite Hp. exact (KR r H2). }
  assert (HAT'' : sv8 W' mem' (lf_F cx + 192) (rm_A1 m h1)).
  { unfold sv8, rm_A1. revert HAT'. destruct (lm_gn m =? 0); intros HAT'; [rewrite Z.add_0_l in HAT'|]; exact HAT'. }
  assert (H144 : sv8 W' mem' (lf_F cx + 144) (c_n cx - rm_k' cx m)).
  { apply (cn_sv8_kept W W' mem mem'); [|exact R144]. intros x Hx. apply KC; [lia|]. right.
    intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
  assert (HR' : (lregs_rmc B) cx t m si j0 (rm_A1 m h1) (frame_addr ly' 1 fpos) regs' W' mem').
  { rewrite KE. unfold lregs_rmc, rm_regs_base.
    repeat split;
      first [ match goal with |- getr regs' ?r = _ => rewrite (KRR r ltac:(cn_cs) ltac:(unfold cn_kept; cn_in)) end;
              assumption
            | exact H144 | exact HAT'' | lia ]. }
  exists regs', mem', md', ly', S', (k + kk), fpos.
  split.
  { unfold cfg_at. rewrite Q1. change (w64 (fr_B0 + A_rm_cshe)) with (Z_to_bv 64 (BASE + A_rm_cshe)). reflexivity. }
  split; [exact ((cn_jt XM_LIB XN_LIB RLO HAP) W W' mem mem' HRV HRV' HROM)|].
  split; [exact HJ'|].
  split; [exact HFR'|].
  split; [exact HFL'|].
  split; [exact HMOD'|].
  split; [exact HIN'|].
  split; [exact HRV'|].
  split; [exact HSEP'|].
  split; [exact HQ'|].
  split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
  exact HR'.
Qed.
(* ---- (4)'s walk: 0x849e0 `bnez s4,0x849ec` (s4 = the removed entry's eof), else `mv a0,s5; jal
   check_no_loss_read` (ret 0x849ec) ---- *)
(* the entry relay_remove took out was at eof or not.  Mirrors the plain invariant's relay_at (Prog/SlotInv.v:269,
   Forall entry_ok es) and entry_ok's eof clause (the same range aentry_ok gives, (rme_relay_entries B)); the arm's model no
   longer holds the entry after relay_remove, so it is read off RINV at the arm's start.  Discharged from RINV. *)
Let rl_RUN := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let rl_BR := paj_branch (PI := PB_fr).
(* check_no_loss_read is a strict leaf (CNLR): the segment is its strict walk over the R journal, lifted by SRr_SRrG,
   the leaf's post journal weakened to R by aji0_of_x *)
Lemma rm_cnlr_xR : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  RCUT_x cx (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)
    ((rm_Qc h j0) cx t m (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ((rm_rr_cost MT) m h))
    ((lregs_rmc B) cx t m si j0 0) RET_RR1 W c ->
  SRrG segs R W c (fun W' c' => exists ev1,
    RCUT_x cx (rm_mk cx m si (Some h1) j0 (rm_cev c2 ev1) O2 cap2 out2)
      ((rm_Qc h j0) cx t m (rm_mk cx m si (Some h1) j0 (rm_cev c2 ev1) O2 cap2 out2) ((rm_rr_cost MT) m h))
      ((lregs_rmc B) cx t m si j0 0) A_rm_cnl W' c').
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 W c HB HRI HAT HRR HRC.
  destruct HRC as (regs & mem & md & ly3 & S3 & k & fpos & -> & HROM & HJ & HFR & HFL & HMOD & HIN & HRV & HSEP & HQ & HNP & HR).
  apply (SRr_SRrG segs R WLE_R).
  pose proof HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Rt) & R20 & R21 & R22 &
    R144 & R192).
  assert (Hsi : (si < 4)%nat) by (destruct HAT as (_ & _ & _ & _ & Hs & _); exact Hs).
  pose proof (RI_rm_cnlr_eof cx t m si h j0 HRI HAT) as He.
  destruct (rl_entry W regs mem _ R20 He) as [HS SHOK].
  remember (Eimg (Ereg regs cn_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs cn_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (re_eof (rm_ent m j0))) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + RET_RR1)) with (Z_to_bv 64 (BASE + RET_RR1)).
  psrr_branch_tok rl_RUN rl_BR HS SHOK cn_span.
  - (* s4 <> 0: the entry was at eof; the branch goes to 0x849ec and nothing else runs *)
    paj_run_to_tok_x cn_RUNTO HS HJ SHOK cn_span A_rm_cnl.
    { apply awr_ok_x_nil. }
    pmkst HS. cn_meq HF Em.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs cn_extra rl_all HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    rewrite Em in *.
    apply SRr_ret. exists (ct_ev c2). rewrite rl_cev_id.
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    exists ly3, S3, k, fpos.
    split; [reflexivity|]. split; [exact HROM|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact HFL|].
    split; [exact HMOD|].
    split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|]. split; [exact HQ|]. split; [exact HNP|].
    unfold lregs_rmc, rm_regs_base.
    repeat split;
      first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(unfold rl_all; cn_in)) end; assumption
            | assumption | lia ].
  - (* s4 = 0: the entry was open (drained): check_no_loss_read(s) *)
    rewrite branch_ne_U, (U_atom E 20 _ E20), U_lit in Hc by lia.
    destruct (Z.eqb_spec (re_eof (rm_ent m j0)) 0) as [Hz | Hnz]; [|discriminate Hc].
    paj_run_to_tok_x cn_RUNTO HS HJ SHOK cn_span AF_fr_check_no_loss_read.
    { apply awr_ok_x_nil. }
    pmkst HS. cn_meq HF Em.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs cn_extra rl_call HS HAE ltac:(vm_compute; reflexivity)) as KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    cbn [ms_regs restrict] in KR.
    rewrite Em in *.
    set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
    clear HS SHOK HF HFr.
    destruct (cn_nums_x cx ly3 S3 W mem mdc k fpos HB HJ) as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & Hfrs & HAR).
    pose proof asan_consts as (C1 & _).
    assert (HFn : alloc_ceiling + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) <= 2 ^ 47)
      by (unfold LLVMF_STK in Hsp0; lia).
    assert (Q10' : getr (ms_regs ms) 10 = w64 (rm_HA si)) by (rewrite Q10, (EEo 21%nat 21%bv eq_refl); exact R21).
    assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
    assert (HCS : 0 <= CNLR_STK /\ CNLR_STK + 352 <= LLVMF_STK) by (split; vm_compute; intro Hc'; discriminate Hc').
    destruct (rm_afn_pre_at_x cx true ly3 S3 fpos k W mem mdc (ms_regs ms) CNLR_STK HB HJ HFR Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
    { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
    { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
    { exact (proj1 HCS). }
    { exact (proj2 HCS). }
    (* the premises: slot si is a 16-aligned g_s slot apart from the shadow cells, its pending list is empty *)
    assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
    assert (Pmod : rm_HA si mod 16 = 0).
    { unfold rm_HA, ASRC. rewrite VS. replace (0x5d88e0 + 96 * Z.of_nat si) with ((0x5d88e + 6 * Z.of_nat si) * 16) by lia.
      apply Z_mod_mult. }
    assert (Prng : 0x10000 <= rm_HA si /\ rm_HA si + 28 <= 0x5fb000) by (clear - Hsi VS; unfold rm_HA, ASRC; rewrite VS; lia).
    assert (Pazs : azs B (rm_HA si) 28).
    { apply ((cn_azs_sub B) (rg_s fr_RG) (4 * ASRC)); [exact HZS | |]; clear - Hsi; unfold rm_HA, ASRC; lia. }
    assert (Pap : (rm_HA si + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rm_HA si) /\
                  (rm_HA si + 28 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= rm_HA si)).
    { destruct HAP as [H0 H32]. clear - H0 H32 Hsi. unfold rm_HA, ASRC in *. lia. }
    assert (HSRC1 : asrc_at B ly3 S3 W mem (rm_HA si) h1)
      by exact (proj1 (cn_out_pre_x cx m si h1 j0 c2 O2 cap2 out2 ly3 S3 W mem mdc HAR Hsi HMOD HSEP)).
    assert (Hpend : hl_recs (hs_pending h1) = []).
    { destruct HRR as [HRel _]. cbv zeta in HRel. rewrite Hz in HRel. cbn [Z.eqb] in HRel.
      unfold dr_rel in HRel. cbv zeta in HRel.
      destruct HRel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
    assert (Pv : val_mem segs (mrestrict (w_H W) mem) (rm_HA si + 24) 4 0).
    { pose proof HSRC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
      pose proof HPL as (_ & HPn & _). unfold hl_n in HPn. rewrite Hpend in HPn. cbn [length Z.of_nat] in HPn.
      replace (rm_HA si + 24) with (rm_HA si + 16 + 8) by lia. exact HPn. }
    eapply SRr_mono.
    { exact (CNLR W ly3 S3 [] (ms_regs ms) mem mdc ch (rm_HA si) 0 HPREc Q10' Pmod (proj1 Prng) (proj2 Prng) Pazs
        (proj1 Pap) (proj2 Pap) Pv ltac:(lia) (or_introl eq_refl)). }
    cbv beta. intros W' c' _ (regs' & mem' & md' & -> & HJl & HPR & _ & HPRES & _).
    rewrite Hsp1 in HJl. apply aji0_of_x in HJl.
    apply (proj2 (ajournal_gx_nil0 CNLR_STK (lf_F cx) [] ly3 S3 W mem mdc [] ly3 S3 W' mem' md' 0)) in HJl.
    assert (HG1 : forall a, inG [] a -> inG G_fr a) by (intros a Ha; exfalso; exact (inG_nil a Ha)).
    assert (HOUT : forall a, inFP [] a -> lf_F cx <= a < lf_F cx + 0) by (intros a Ha; exfalso; exact (inFP_nil a Ha)).
    assert (HFP : forall a, inFP [] a -> exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n /\
        (~ In (b, n) (ablocks B (c_ly cx) (c_S cx)) \/ inFP (lf_FP fr_FP cx) a))
      by (intros a Ha; exfalso; exact (inFP_nil a Ha)).
    assert (Hsink : ~ YI16.sink_open_fp []) by (intros (r & Hr & _); destruct Hr).
    pose proof (rm_compose_x cx fpos ly3 S3 W mem mdc k [] 0 [] CNLR_STK [] ly3 S3 W' mem' md' 0 HB HJ HJl HG1
      ltac:(lia) (proj1 HCS) (proj2 HCS) HOUT HFP) as HJ'.
    destruct (rm_kept_x cx fpos ly3 S3 W mem mdc k [] 0 [] CNLR_STK [] ly3 S3 W' mem' md' 0 HB HJ HJl HG1
      ltac:(lia) (proj1 HCS) (proj2 HCS) Hsink) as (KA & KB & KC & KD & KE & KF & KAR).
    destruct (ERR ly3 S3 [] W' mem' md' KAR) as ((ev1 & Hev & Hevr) & Hew).
    exists ev1.
    (* the kept bytes: the model's image cells (view by K4, writability by presence), every live block *)
    assert (KG : forall a, (rm_mglob a \/ rg_rng fr_RG a) -> abyte_kept W mem W' mem' a).
    { intros a Ha. destruct ((cn_glob_facts B RGP HMG) a Ha) as (I1 & I2 & I3).
      split; [exact (proj1 (KA a I1 (fun H => inG_nil a H) I2 I3))|].
      apply cn_awr_kept. exact (HPRES a). }
    assert (KBL : forall b, In b (ablocks B ly3 S3) ->
        In b (ablocks B ly3 S3) /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
    { intros [p n] Hb. split; [exact Hb|]. cbn [fst snd]. intros a Ha.
      destruct (al_blocks_0 ly3 S3 W mem mdc p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n (proj1 Hn0)) as [_ Rn].
      replace a with (p + (a - p)) by lia.
      apply (KB p n (a - p) Hb Hb); [lia|]. intros Hf. exact (inFP_nil _ Hf). }
    set (m1 := rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) in *.
    assert (Hsil : (si < length (lm_hs m))%nat).
    { pose proof HMOD as (M1 & _). unfold m1, rm_mk in M1. cbn [lm_hs] in M1. rewrite cn_rsn_length in M1. lia. }
    pose proof HSEP as [[rest0 Hp3] _].
    assert (HMB : forall b, In b (model_blks m1) -> In b (ablocks B ly3 S3))
      by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hp3 |
          apply in_or_app; right; apply in_or_app; left; exact Hb]).
    pose proof (cn_model_perm cx m si (Some h1) j0 c2 O2 cap2 out2 Hsil) as HM1.
    assert (KYR : forall b, In b (cn_rest m si j0 cap2 out2) ->
        In b (ablocks B ly3 S3) /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
    { intros b Hb. apply KBL. apply HMB. eapply Permutation_in; [apply Permutation_sym; exact HM1|].
      apply in_or_app. right. exact Hb. }
    assert (HSRC : asrc_at B ly3 S3 W' mem' (rm_HA si) h1).
    { refine (cn_aslot_kept_x ly3 S3 W mem mdc ly3 S3 W' mem' si (Some h1) HAR HSRC1 _ _).
      - intros a Ha. apply KG. right. unfold rg_rng. right; right; right; right. clear - Ha Hsi. unfold ASRC in *. lia.
      - intros b Hb. apply KBL. apply HMB. eapply Permutation_in; [apply Permutation_sym; exact HM1|].
        apply in_or_app. left. exact Hb. }
    assert (HMOD' : amodel_at B ly3 S3 W' mem' (rm_mk cx m si (Some h1) j0 (rm_cev c2 ev1) O2 cap2 out2))
      by exact (cn_model_kept_x cx m si h1 h1 j0 c2 ev1 O2 cap2 out2 ly3 S3 W mem mdc ly3 S3 W' mem' HAR Hsi HMOD HSRC
        (fun a Ha _ => KG a Ha) KYR Hev Hew Hevr).
    assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
    assert (HFR' : aframe_at cx true (frame_addr ly3 1 fpos) W' mem').
    { pose proof HFR as (_ & HAWR & _).
      apply (cn_aframe_kept cx true (frame_addr ly3 1 fpos) W W' mem mem' HFR).
      - intros a Ha _. apply KC; [exact Ha | left; lia].
      - intros a Ha. assert (Hk : abyte_kept W mem W' mem' a) by (apply KC; [lia | left; lia]).
        apply (proj2 Hk).
        replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia.
      - intros a Ha. apply KD; [| intros Hf; exact (inFP_nil _ Hf)].
        left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
      - intros a Ha. apply KD; [| intros Hf; exact (inFP_nil _ Hf)].
        right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        cbv [SB SHADOW_OFF] in Ha |- *. lia.
      - lia.
      - lia. }
    assert (HFL' : sv8 W' mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
    { apply (rm_flag_kept W W' mem mem'); [|exact HFL].
      intros a Ha. apply KD; [| intros Hf; exact (inFP_nil _ Hf)].
      left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia. }
    assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx)))
      by (destruct HB as (_ & HPRE0); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE0))))))).
    assert (KYI : forall b, In b (input_blks cx) ->
        In b (ablocks B ly3 S3) /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
    { intros b Hb. apply KBL. eapply Permutation_in; [apply Permutation_sym; exact Hp3|]. apply in_or_app. left. exact Hb. }
    pose proof ((cn_input_kept B) cx ly3 S3 W mem ly3 S3 W' mem' HIN (eq_sym HlenP) KYI) as HIN'.
    assert (HRV' : rom_view segs W' mem').
    { pose proof (ajournal_gx_G_mono0 [] G_fr 0 [] CNLR_STK (lf_F cx) [] ly3 S3 W mem mdc [] ly3 S3 W' mem' md' 0
        HG1 HJl) as HJcG.
      exact (ajournal_gx_rom_view0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJcG HRO HRV). }
    assert (KRR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r rl_call -> getr regs' r = getr regs r).
    { intros r H1 H2. pose proof (HPR _ H1) as Hp. rewrite !Z_to_bv_bv_unsigned in Hp. rewrite Hp. exact (KR r H2). }
    assert (H144 : sv8 W' mem' (lf_F cx + 144) (c_n cx - rm_k' cx m)).
    { apply (cn_sv8_kept W W' mem mem'); [|exact R144]. intros x Hx. apply KC; [lia | left; lia]. }
    assert (H192 : sv8 W' mem' (lf_F cx + 192) 0).
    { apply (cn_sv8_kept W W' mem mem'); [|exact R192]. intros x Hx. apply KC; [lia | left; lia]. }
    assert (HR' : (lregs_rmc B) cx t m si j0 0 (frame_addr ly3 1 fpos) regs' W' mem').
    { unfold lregs_rmc, rm_regs_base.
      repeat split;
        first [ match goal with |- getr regs' ?r = _ => rewrite (KRR r ltac:(cn_cs) ltac:(unfold rl_call; cn_in)) end;
                assumption
              | exact H144 | exact H192 | lia ]. }
    exists regs', mem', md', ly3, S3, (k + 0), fpos.
    split.
    { unfold cfg_at. rewrite Q1. change (w64 (fr_B0 + A_rm_cnl)) with (Z_to_bv 64 (BASE + A_rm_cnl)). reflexivity. }
    split; [exact ((cn_jt XM_LIB XN_LIB RLO HAP) W W' mem mem' HRV HRV' HROM)|].
    split; [exact HJ'|].
    split; [exact HFR'|].
    split; [exact HFL'|].
    split; [exact HMOD'|].
    split; [exact HIN'|].
    split; [exact HRV'|].
    split; [exact HSEP|].
    split; [exact HQ|].
    split; [exact HNP|].
    exact HR'.
Qed.
(* (6) check_shape_ends(s, "", &at) *)
Lemma cs_disj_x : forall ly S (W : world segs) mem md L1 L2,
  AR0 ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) ->
  forall b1 b2, In b1 L1 -> In b2 L2 -> zdisjoint (fst b1, req_size (snd b1)) (fst b2, req_size (snd b2)).
Proof.
  intros ly S W mem md L1 L2 HAR HP b1 b2 H1 H2.
  destruct (al_sep_0 ly S W mem md HAR) as [Hpw _].
  apply pairwise_app_l in Hpw as [Hpw _].
  assert (Hpw' : YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) L1 ++
    map (fun b => (fst b, req_size (snd b))) L2)).
  { rewrite <- map_app.
    apply (cs_pw_perm zdisjoint) with (l := map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)).
    - intros x y [Hxy | Hxy]; [right | left]; exact Hxy.
    - apply Permutation_map. exact HP.
    - exact Hpw. }
  exact (cs_pw_cross zdisjoint _ _ Hpw' _ _ (in_map _ _ _ H1) (in_map _ _ _ H2)).
Qed.
(* a live block and a live frame are apart (AR_sep_law) *)
Lemma cs_frame_disj_x : forall ly S (W : world segs) mem md b cid pos,
  AR0 ly S W mem md -> In b (ablocks B ly S) -> In (cid, pos) (frames S) ->
  zdisjoint (fst b, req_size (snd b)) (frame_addr ly cid pos, fs_frame_bytes cid).
Proof.
  intros ly S W mem md b cid pos HAR Hb Hf.
  destruct (al_sep_0 ly S W mem md HAR) as [Hpw _].
  exact (cs_pw_cross zdisjoint _ _ Hpw _ _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb)
    (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf)).
Qed.
(* a live block (AR_blocks_law; the size bound is BLKN30's 2 ^ 30, the AR law's MALLOC_MAX = 2 ^ 28 does not hold at
   the cf instance) *)
Lemma cs_blk_x : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n /\ in_app p (req_size n) /\ n < 2 ^ 30.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks_0 ly S W mem md p n HAR Hin) as (_ & H1 & H2 & H4 & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact H4 | lia].
Qed.
(* ---- memory helpers ---- *)
(* the real stack is addressable: ARx's byte form of the stack's zero shadow (YCbqG.v ARx_zshadow_byte_law; the AR
   proof's range form needs the page-aligned stack bounds of AR's layout, which AR_laws_x does not carry) *)
Lemma cs_ra_stack_x : forall ly1 S1 (W1 : world segs) mem1 md1 a len,
  AR0 ly1 S1 W1 mem1 md1 -> ly_stk_lo ly1 <= a -> a + len <= ly_stk_hi ly1 -> 0 <= len ->
  range_addressable (aview segs (w_H W1) mem1) SHADOW_OFF a len.
Proof.
  intros ly1 S1 W1 mem1 md1 a len HAR Hlo Hhi Hlen x Hx.
  exists 0. split; [|left; reflexivity].
  exact (alx_zshadow_byte _ _ _ LAWS ly1 S1 [] W1 mem1 md1 x HAR ltac:(lia)).
Qed.
(* a frame's shadow is not in an application block (in_app: the two never meet) *)
Ltac cs_zn H := cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
(* the stream's cells but errno, kept, and errno re-read: the stream with errno's new value *)
Ltac cs_in := cbn [cs_aout_g In]; repeat (first [left; reflexivity | right]).
Ltac cs_inw := cbn [cs_wranges In]; repeat (first [left; reflexivity | right]).
(* a slot's blocks are among the slots' blocks *)
Ltac cs_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* the model's cells outside g_s are apart from check_shape_ends' globals (g_s[si] + 64 .. + 96) *)
Ltac cs_wrg lo n := apply (cs_wr_glob lo n); [cs_inw | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
(* a fact lia does not unfold (lia case-splits every arithmetic disjunction in its context) *)
(* the run up to check_shape_ends, at R (its callee frees) *)
Let cs_RUNTO := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
(* every register but ra, a0, a1 and a2 *)
Ltac cs_ink := cbn [cs_kept In]; repeat (first [left; reflexivity | right]).
Ltac cs_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* check_shape_ends frees: the walk runs at R up to the call, CSHE_R's R journal is composed by rm_compose_x *)
Lemma rm_cshe_xR : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' ev2 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  RCUT_x cx (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2)
    ((rm_Qc h j0) cx t m (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2)
      ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1)))
    ((lregs_rmc B) cx t m si j0 (rm_A1 m h1)) A_rm_cshe W c ->
  SRrG segs R W c (fun W' c' => exists H'' ds cc ev3,
    rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc /\
    RCUT_x cx (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev3) O2 cap2 out2)
      ((rm_Qc h j0) cx t m (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev3) O2 cap2 out2)
        ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H'))
      ((lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc)) A_rm_csd W' c').
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' ev2 W c HB HRI HAT HRR HCN HRC.
  destruct HRC as (regs & mem & md & ly3 & S3 & k & fpos & -> & HROM & HJ & HFR & HFL & HMOD & HIN & HRV & HSEP & HQ & HNP & HRG).
  destruct (cs_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs cs_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs cs_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (EO28 : ew E (A_OBJ 28) = Z_to_bv 64 0x20ee0)
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj2 (proj2 (proj2 (proj2 (proj2 probe_hi))))); reflexivity).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + A_rm_cshe)) with (Z_to_bv 64 (BASE + A_rm_cshe)).
  paj_run_to_tok_xR cs_RUNTO HS HJ SHOK cs_span AF_fr_check_shape_ends.
  { apply awr_ok_x_nil. }
  pmkst HS.
  cs_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs cs_extra cs_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  (* ---- the facts the call takes ---- *)
  pose proof HAT as (Hk & HO & Hop & Hpick & Hsi & Hnth & Hj0 & Hfd & Hfirst).
  pose proof HRG as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Rt) & R20 & R21 & R22 & R144 & R192).
  pose proof HCN as (HE0 & HEv & HEc & HND & HTX & HCAP).
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & _ & _ & _ & _ & HlenP & _ & HfrS0 & _).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & Htop0 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = 32 * ((spZ (c_regs cx) - 320) / 32)).
  { unfold lf_F. pose proof (Z.div_mod (spZ (c_regs cx) - 320) 32 ltac:(lia)) as D. lia. }
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  unfold LLVMF_STK in Hslo.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by lia.
  destruct (ajournal_gx_inner0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc k HJ) as (memS & HJ0 & _).
  rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (HAR3 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  rewrite HfrS0, app_nil_r in Hfrs.
  pose proof HMOD as (ML4 & MSL & MREL & MOUT & MGN & MLK & MWK & MNFD & MNFDw & MNFDb & MTU & MLST & MLSTw).
  cbn [rm_mk lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd] in ML4, MSL, MREL, MOUT, MGN, MNFD, MNFDb.
  assert (Hlen4 : length (lm_hs m) = 4%nat)
    by (rewrite <- (cs_rsn_length si (Some (set_exp_held h1 E' H')) (lm_hs m)); exact ML4).
  assert (HSRC : asrc_at B ly3 S3 W mem (rm_HA si) (set_exp_held h1 E' H')).
  { pose proof (MSL si Hsi) as X. rewrite cs_rsn_same in X by lia. exact X. }
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHL & _).
  cbn [hs_held set_exp_held] in HHL.
  pose proof HHL as (_ & _ & _ & _ & Hncap & Hvec & _ & _ & Hrecs).
  (* RI_rm_cshe_pre's NUL premise: the held list's texts are lines (alist_at at lines = true) *)
  assert (HNUL : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H')).
  { eapply Forall_impl; [|exact Hrecs]. intros r (_ & _ & Hl & _). exact (proj1 (Hl eq_refl)). }
  pose proof MOUT as (_ & _ & Ono & _ & _ & _ & Oout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    Olen & Oblk).
  assert (Ers : rg_s fr_RG = 0x5d88e0) by reflexivity.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cs_ink)), R2. unfold w64. apply unsigned_lit_small. lia. }
  (* check_shape_ends' own globals: the source's held list (g_s[si] + 64 .. + 96), inside G_fr *)
  set (G := [(rm_HA si + 64, 32)]).
  assert (HGsub : forall a, inG G a -> inG G_fr a).
  { intros a Ha. apply HGs. unfold G in Ha. apply inG_cons in Ha as [Ha|Ha]; [|exfalso; exact (inG_nil a Ha)].
    unfold in_zr in Ha; cbn [fst snd] in Ha. unfold rm_HA, ASRC in *. lia. }
  assert (HGx : gx_ok segs B G) by (intros a Ha; exact (HG a (HGsub a Ha))).
  (* K1 *)
  destruct (rm_afn_pre_at_x cx true ly3 S3 fpos k W mem mdc (ms_regs ms) CSHE_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cs_ink)). exact R3. }
  { rewrite (KR 4%bv ltac:(cs_ink)). exact R4. }
  { rewrite (KR 8%bv ltac:(cs_ink)). exact R8. }
  { unfold CSHE_STK, CSHE_FRAME, ASTACK. lia. }
  { unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK. lia. }
  (* the stream: empty, or a live block that holds the bytes the controller read (cs_hide: kept out of lia's sight) *)
  assert (HOB : cs_hide ((O2 = [] /\ cap2 = 0 /\ out2 = 0) \/
    (0 < cap2 < 2 ^ 30 /\ Z.of_nat (length O2) <= cap2 /\ In (out2, cap2) (ablocks B ly3 S3) /\
     in_app out2 cap2 /\ ob_at W mem out2 O2))).
  { unfold cs_hide. destruct Oblk as [(Hc0 & Ho0 & Hn0) | (Hcp & Hno & Hin & junk & Hj & Hg)].
    - left. split; [destruct O2; [reflexivity | cbn [length] in Hn0; lia] | split; assumption].
    - right. destruct (cs_blk_x ly3 S3 W mem mdc out2 cap2 HAR3 Hin) as (B1 & B2 & B3 & B4 & B5).
      unfold req_size in B4. replace (cap2 =? 0) with false in B4 by (symmetry; apply Z.eqb_neq; lia).
      split; [lia|]. split; [lia|]. split; [exact Hin|]. split; [exact B4|].
      exact (cs_ob_of_garr8 W mem out2 O2 junk Hg). }
  clear Oblk.
  (* the held list's blocks and their bound *)
  assert (HHn : hl_n H' < 2 ^ 26 /\
    (forall a, hl_v H' <= a < hl_v H' + AREC * hl_cap H' -> a < alloc_ceiling) /\
    (forall r, In r (hl_recs H') -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 -> a < alloc_ceiling)).
  { split; [|split].
    - destruct Hvec as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|].
      destruct (cs_blk_x ly3 S3 W mem mdc _ _ HAR3 Hin) as (_ & _ & _ & _ & B5). unfold AREC in B5. lia.
    - intros a Ha. destruct Hvec as [(Hc0 & _) | (Hcp & Hin & _)]; [unfold AREC in Ha; lia|].
      destruct (cs_blk_x ly3 S3 W mem mdc _ _ HAR3 Hin) as (_ & B2 & B3 & _). lia.
    - intros r Hr a Ha. rewrite Forall_forall in Hrecs. destruct (Hrecs r Hr) as (Hin & _).
      destruct (cs_blk_x ly3 S3 W mem mdc _ _ HAR3 Hin) as (_ & B2 & B3 & _). lia. }
  assert (Hcap0 : 0 <= hl_cap H') by (clear - Hvec; destruct Hvec as [(Hc0 & _) | (Hcp & _)]; lia).
  clear Hvec.
  (* the permutation that puts the stream's block apart from the source's *)
  pose proof HSEP as ((rest0 & HPm) & HSEP2).
  assert (MO : Permutation (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2))
    (aout_blks cap2 out2 ++ asrc_blks (set_exp_held h1 E' H') ++ ((lm_G m, ATABLE) ::
      concat (map aentry_blks (relay_remove_b_c.remove_at j0 (lm_es m))) ++
      concat (map slot_blks (rm_set_nth si None (lm_hs m)))))).
  { unfold model_blks. cbn [rm_mk lm_G lm_es lm_hs lm_cap lm_out]. apply cs_mblks_out. lia. }
  pose proof (Permutation_trans HPm (cs_perm3 _ _ rest0 _ _ _ MO)) as HPo.
  (* ---- check_shape_ends(s = g_s[si], "", &at) at its own G ---- *)
  pose proof (CSHE_R G HGx W ly3 S3 [] (ms_regs ms) mem mdc ch 208 (lf_F cx + 192) (rm_HA si) si 0x20ee0
    (set_exp_held h1 E' H') [] (rm_A1 m h1) (lm_gn m) (Z.of_nat (length O2)) out2 O2) as HCALL.
  cbv zeta in HCALL.
  eapply (SRrG_bind segs R R_trans); [apply HCALL with (kr := 0%nat); clear HCALL|].
  - exact HPREc.
  - lia.
  - reflexivity.
  - rewrite Hsp1, Etop. lia.
  - intros a Ha. rewrite Hsp1 in Ha. apply Hpres0. unfold LLVMF_STK. lia.
  - rewrite Q10, (EEo 21%nat 21%bv eq_refl). exact R21.
  - rewrite Q11. exact EO28.
  - rewrite Q12, (EEo 9%nat 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - exact HSRC.
  - unfold rm_HA, ASRC. rewrite Ers.
    replace (6129888 + 96 * Z.of_nat si) with ((766236 + 12 * Z.of_nat si) * 8) by lia. apply Z_mod_mult.
  - unfold rm_HA, ASRC. rewrite Ers. lia.
  - unfold rm_HA, ASRC, kLowMemEnd. rewrite Ers. lia.
  - intros a Ha. unfold G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - destruct HZS as (r & Hin & H8 & Hlo & Hhi). exists r. split; [exact Hin|]. split; [exact H8|].
    unfold rm_HA, ASRC in *. split; lia.
  - unfold rm_HA. replace (VAL (A_OBJ 22)) with (rg_s fr_RG) by (vm_compute; reflexivity). reflexivity.
  - exact Hsi.
  - intros a Ha. rewrite Hsp1. unfold rm_HA, ASRC, CSHE_STK, CSHE_FRAME, ASTACK in *. rewrite Ers in Ha. lia.
  - intros a Ha. unfold cshe_home. right. left.
    destruct RGP as (_ & _ & _ & _ & _ & _ & RGr & _ & _).
    apply RGr. unfold rg_rng. right. right. right. right. unfold rm_HA, ASRC in *. lia.
  - exact HND.
  - exact (proj1 HHn).
  - intros a Ha. rewrite Hsp1. pose proof (proj1 (proj2 HHn) a Ha). unfold CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - intros r Hr a Ha. rewrite Hsp1. pose proof (proj2 (proj2 HHn) r Hr a Ha). unfold CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - rewrite HF32. replace (32 * ((spZ (c_regs cx) - 320) / 32) + 192) with ((4 * ((spZ (c_regs cx) - 320) / 32) + 24) * 8)
      by lia. apply Z_mod_mult.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - apply (cs_ra_stack_x ly3 S3 W mem mdc); [exact HAR3 | rewrite Eslo; lia | rewrite Eshi; lia | lia].
  - exact R192.
  - intros [].
  - cbn [length Z.of_nat]. lia.
  - lia.
  - cbn [length Z.of_nat]. lia.
  - cbn [length Z.of_nat]. intros i Hi. lia.
  - cbn [length Z.of_nat]. rewrite Z.add_0_r. apply ((cs_pf_view XM_LIB XN_LIB RLO HAP) W mem HRV). lia.
  - (* .str.2 and the 7 bytes strlen's word read may touch: present (read-only image), off the callee's window *)
    cbn [length Z.of_nat]. intros a Ha.
    split; [rewrite ((cs_pf_view XM_LIB XN_LIB RLO HAP) W mem HRV a ltac:(lia)); discriminate|].
    rewrite Hsp1. unfold CSHE_STK, CSHE_FRAME, ASTACK. lia.
  - unfold amem_range, kLowMemEnd. left. cbn [length Z.of_nat]. lia.
  - unfold amem_range, kLowMemEnd. left. lia.
  - cbn [length Z.of_nat]. change (0 + 1) with 1.
    replace 134880 with (VAL (A_OBJ 28)) by (vm_compute; reflexivity).
    exact (proj1 (HSTR2S ly3 S3 [] W mem mdc HAR3)).
  - cbn [length Z.of_nat]. change (0 + 1) with 1.
    replace 134880 with (VAL (A_OBJ 28)) by (vm_compute; reflexivity).
    exact (proj2 (HSTR2S ly3 S3 [] W mem mdc HAR3) ltac:(lia)).
  - (* P's home (cshe_spec's disjunction): the read-only literal .str.2, its shadow a const cell (ashp) *)
    left. cbn [length Z.of_nat]. split; [intros a Ha; apply (cs_rom_lo XM_LIB XN_LIB RLO HAP); lia|].
    change (0 + 1) with 1.
    replace 134880 with (VAL (A_OBJ 28)) by (vm_compute; reflexivity). exact HSTR2S.
  - exact ((cs_end5 XM_LIB XN_LIB RLO HAP) W mem HRV).
  - exact HRV.
  - replace (VAL A_g_gone) with (rg_gone fr_RG) by (vm_compute; reflexivity). exact (proj1 MGN).
  - destruct MGN as (_ & _ & [G0|G0]); lia.
  - replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity). exact Ono.
  - replace (VAL A_g_out) with (rg_out fr_RG) by (vm_compute; reflexivity). exact Oout.
  - destruct HOB as [(-> & _ & _) | (_ & _ & _ & _ & Hob)]; [intros i Hi; cbn in Hi; lia | exact Hob].
  - reflexivity.
  - destruct HOB as [(-> & _ & _) | (Hc & Hl & _)]; [cbn; lia | lia].
  - intros Hpos. destruct HOB as [(-> & _ & _) | (Hc & Hl & _)]; [cbn in Hpos; lia | lia].
  - destruct HOB as [(-> & _ & ->) | (Hc & Hl & Hin & Happ & _)].
    + unfold amem_range, kLowMemEnd. left. cbn. lia.
    + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
      destruct Happ as (Hlo4 & [Hl1 | (Hh1 & Hh2)]); [left | right]; lia.
  - destruct HOB as [(-> & _ & _) | (Hc & Hl & Hin & Happ & Hob)]; [left; reflexivity | right].
    exists cap2. split; [lia|]. split; [exact Hin|].
    intros Hb. destruct (cs_hsb _ _ Hb) as (n & Hn).
    assert (Hin1 : In (out2, cap2) (aout_blks cap2 out2))
      by (unfold aout_blks; replace (cap2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); left; reflexivity).
    assert (Hin2 : In (out2, n) (asrc_blks (set_exp_held h1 E' H') ++ input_blks cx ++
        ((lm_G m, ATABLE) :: concat (map aentry_blks (relay_remove_b_c.remove_at j0 (lm_es m))) ++
         concat (map slot_blks (rm_set_nth si None (lm_hs m)))) ++ rest0))
      by (apply in_or_app; left; exact Hn).
    pose proof (cs_disj_x ly3 S3 W mem mdc _ _ HAR3 HPo (out2, cap2) (out2, n) Hin1 Hin2) as D.
    assert (Hab : In (out2, n) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HPo)); apply in_or_app; right; exact Hin2).
    destruct (cs_blk_x ly3 S3 W mem mdc _ _ HAR3 Hab) as (_ & _ & Hn0 & _).
    pose proof (req_size_pos cap2 ltac:(lia)) as [Rc _]. pose proof (req_size_pos n ltac:(lia)) as [Rn _].
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
  - destruct (Z.eq_dec (lm_gn m) 0) as [G0|G0].
    + destruct (RI_rm_cshe_pre cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI HAT HRR HCN G0 HNUL) as [HA1 _].
      split; [unfold rm_A1; destruct (lm_gn m =? 0); lia | exact HA1].
    + unfold rm_A1. rewrite (proj2 (Z.eqb_neq _ _) G0). lia.
  - intros G0. exact (proj2 (RI_rm_cshe_pre cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI HAT HRR HCN G0 HNUL)).
  - destruct HQ as (ly0 & S0 & HLS & HMle & _ & _ & _ & HR3). pose proof HR3 as (_ & _ & _ & HU & _).
    exact (LS_rm_cshe_pre cx t m ly0 S0 S3 si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HLS HRI HAT HRR Rt HU HCN HMle).
  - apply RP_NP. exact HNP.
  - destruct HQ as (ly0 & S0 & _ & _ & HMF & HFR0 & HC0 & HR3).
    exact (rm_cnt_step cx ly0 S0 m _ ly3 S3 _ _ HFR0
      (fun P => RM_CNT_cshe cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' P HRI HAT HRR HCN HMF HR3
         (RI_rm_src cx t m si h j0 HRI HAT)) HC0).
  - (* ---- the post: back at 0x84a0c ---- *)
    intros W2 c' Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk & H'' & ds & cc & -> & HJc & HP2 & _ & HSRC' & HHv
      & HHc & HND'' & HDJ & Hcc & HAT2 & HGN2 & HPERM & HFRS & HMO & HRM').
    assert (EHp' : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
    rewrite Hsp1 in HJc.
    cbn [hs_held set_exp_held] in HJc, HHv, HHc, HDJ, HMO.
    assert (RCOK : rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc).
    { unfold rm_cshe_ok. cbn [hs_held set_exp_held].
      split; [exact HHv|]. split; [exact HHc|]. split; [exact HND''|]. split; [exact Hcc|]. exact HDJ. }
    (* keep lia's context free of disjunctions *)
    clear HOB.
    assert (ELB : forall l, list_blks l = alist_blks l) by reflexivity.
    (* the blocks: the held list's, apart from the rest of the model's *)
    pose (MR := cs_MR (lm_G m) (relay_remove_b_c.remove_at j0 (lm_es m)) (lm_hs m) si (set_exp_held h1 E' H') cap2 out2).
    assert (MH : Permutation (model_blks (rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 (rm_cev c2 ev2) O2 cap2 out2))
      (alist_blks H' ++ MR)).
    { unfold model_blks, MR. cbn [rm_mk lm_G lm_es lm_hs lm_cap lm_out]. apply (cs_mblks _ _ _ si). lia. }
    assert (HPh : Permutation (ablocks B ly3 S3) (alist_blks H' ++ (input_blks cx ++ MR ++ rest0)))
      by exact (Permutation_trans HPm (cs_perm3 _ _ _ _ [] _ MH)).
    assert (HRP : Permutation (hl_recs H') (hl_recs H'' ++ ds)).
    { destruct HDJ as [(G1 & Hr'' & Hds & Hc0) | (G0 & ER)].
      - rewrite Hr'', Hds, cs_filter_none, cs_filter_all. apply Permutation_refl.
      - exact (cs_ends_perm _ _ _ _ _ _ _ ER). }
    pose proof (cs_lblks_perm H' H'' ds HHv HHc HRP) as HLB. clear HDJ.
    assert (MH3 : forall cv, Permutation (model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 cv O2 cap2 out2))
      (alist_blks H'' ++ MR)).
    { intros cv. unfold model_blks. cbn [rm_mk lm_G lm_es lm_hs lm_cap lm_out].
      eapply Permutation_trans; [apply (cs_mblks _ _ _ si (set_held (set_exp_held h1 E' H') H'')); lia|].
      unfold MR, cs_MR, cs_nh. cbn [hs_held set_held set_exp_held hs_partial hs_pending hs_expected].
      apply Permutation_refl. }
    assert (HP3 : forall cv, Permutation (ablocks B ly3 S3) (cshe_ds_blks ds ++
      (input_blks cx ++ model_blks (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 cv O2 cap2 out2) ++ rest0))).
    { intros cv. eapply Permutation_trans; [exact HPm|].
      eapply Permutation_trans.
      { apply (cs_perm3 _ _ _ (cshe_ds_blks ds) [] (alist_blks H'' ++ MR)).
        eapply Permutation_trans; [exact MH|]. cbn [app]. rewrite app_assoc. apply Permutation_app_tail. exact HLB. }
      cbn [app]. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_tail.
      apply Permutation_sym. exact (MH3 cv). }
    (* what check_shape_ends kept (K4) *)
    assert (Hsink : ~ YI16.sink_open_fp (blk_FP (list_blks H'))).
    { intros (r & Hr & Ha). unfold blk_FP in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
      rewrite ELB in Hb.
      assert (Hab : In b (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPh)); apply in_or_app; left; exact Hb).
      destruct b as [p n]. destruct (cs_blk_x ly3 S3 W mem mdc p n HAR3 Hab) as (Hp & _). cbn [fst] in Ha. lia. }
    destruct (rm_kept_x cx fpos ly3 S3 W mem mdc k G 208 [(lf_F cx + 192, lf_F cx + 192 + 8)] CSHE_STK
      (blk_FP (list_blks H')) ly' S' W2 mem' md' kk HB HJ HJc HGsub ltac:(lia)
      ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK; lia) ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK; lia) Hsink)
      as (KG1 & KB2 & KS3 & KF4 & Efa & Efr & HAR').
    destruct (ERR ly' S' [] W2 mem' md' HAR') as ((ev3 & Hev3 & Hev3r) & Hev3w).
    pose (m3 := rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev3) O2 cap2 out2).
    pose proof (HPERM _ (HP3 (rm_cev c2 ev3))) as HP'.
    (* the image cells outside check_shape_ends' globals *)
    assert (KG : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
      ~ (rm_HA si + 64 <= a < rm_HA si + 96) -> (forall mm, writable_at segs mm a) -> abyte_kept W mem W2 mem' a).
    { intros a H1 H2 H3 H4 H5.
      assert (Hng : ~ inG G a).
      { intros Hg. apply H4. unfold G in Hg. apply inG_cons in Hg as [Hg|Hg]; [|exfalso; exact (inG_nil a Hg)].
        unfold in_zr in Hg; cbn [fst snd] in Hg. lia. }
      exact (proj2 (KG1 a H1 Hng H2 H3) H5). }
    destruct RGP as (_ & _ & _ & _ & _ & _ & RGr & _ & _).
    assert (KGR : forall a, rg_rng fr_RG a -> ~ (rm_HA si + 64 <= a < rm_HA si + 96) -> (forall mm, writable_at segs mm a) ->
      abyte_kept W mem W2 mem' a).
    { intros a Ha H4 H5. destruct (RGr a Ha) as (H1 & H2 & H3). exact (KG a H1 H2 H3 H4 H5). }
    assert (KGM : forall a, rm_mglob a -> (forall mm, writable_at segs mm a) -> abyte_kept W mem W2 mem' a).
    { intros a Ha H5. destruct (HMG a Ha) as (H1 & H2 & H3). apply (KG a H1 H2 H3); [|exact H5].
      exact (cs_mglob_far si a Hsi Ha). }
    (* the live blocks outside the held list's *)
    assert (NFP : forall b a, In b (input_blks cx ++ MR ++ rest0) -> fst b <= a < fst b + req_size (snd b) ->
      ~ inFP (blk_FP (list_blks H')) a).
    { intros b a Hb Ha (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as (b' & <- & Hb'). cbn [fst snd] in Hra.
      rewrite ELB in Hb'. pose proof (cs_disj_x ly3 S3 W mem mdc _ _ HAR3 HPh b' b Hb' Hb) as D. unfold zdisjoint in D.
      cbn [fst snd] in D. lia. }
    assert (BL2 : forall b, In b (input_blks cx ++ MR ++ rest0) -> In b (ablocks B ly' S') /\
      (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem' a)).
    { intros [p n] Hb.
      assert (Hab : In (p, n) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPh)); apply in_or_app; right; exact Hb).
      assert (Hab' : In (p, n) (ablocks B ly' S')).
      { apply (Permutation_in _ (Permutation_sym HP')). apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|].
        apply in_or_app; right. apply in_app_or in Hb as [Hb|Hb]; [|apply in_or_app; right; exact Hb].
        apply in_or_app; left. apply (Permutation_in _ (Permutation_sym (MH3 (rm_cev c2 ev3)))).
        apply in_or_app; right; exact Hb. }
      split; [exact Hab'|]. intros a Ha. cbn [fst snd] in Ha.
      destruct (cs_blk_x ly3 S3 W mem mdc p n HAR3 Hab) as (_ & _ & Hn & _).
      replace a with (p + (a - p)) by lia.
      apply (KB2 p n (a - p) Hab Hab'); [lia|].
      replace (p + (a - p)) with a by lia. apply (NFP (p, n) a Hb). cbn [fst snd]. lia. }
    (* where the model's blocks are: the slots' (slot si closed), the relay's, the stream's *)
    assert (MSN : forall b, In b (concat (map slot_blks (rm_set_nth si None (lm_hs m)))) -> In b (input_blks cx ++ MR ++ rest0)).
    { intros b Hb. apply in_or_app. right. apply in_or_app. left. unfold MR, cs_MR. right.
      apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact Hb. }
    assert (MRE : forall b, In b (arelay_blks (lm_G m) (relay_remove_b_c.remove_at j0 (lm_es m))) ->
      In b (input_blks cx ++ MR ++ rest0)).
    { intros b Hb. apply in_or_app. right. apply in_or_app. left. unfold MR, cs_MR.
      destruct Hb as [<-|Hb]; [left; reflexivity|]. right. apply in_or_app. left. exact Hb. }
    assert (MAO : forall b, In b (aout_blks cap2 out2) -> In b (input_blks cx ++ MR ++ rest0)).
    { intros b Hb. apply in_or_app. right. apply in_or_app. left. unfold MR, cs_MR. right.
      apply in_or_app. right. apply in_or_app. right. exact Hb. }
    (* the callee's own window is present after it (its journal's window clause) *)
    destruct (ajournal_gx_inner0 G 208 [(lf_F cx + 192, lf_F cx + 192 + 8)] CSHE_STK (lf_F cx)
      (blk_FP (list_blks H')) ly3 S3 W mem mdc [] ly' S' W2 mem' md' kk HJc) as (memS2 & HJc0 & _).
    pose proof HJc0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
    assert (HROG : rom_out segs B G).
    { intros a Ha. destruct (HRO a Ha) as (Hn & Hr). split; [intros Hg; exact (Hn (HGsub a Hg)) | exact Hr]. }
    pose proof (ajournal_gx_rom_view0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HROG HRV) as HRV'.
    assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
    destruct (frames_bounds0 ly3 S3 W mem mdc 1 fpos HAR3 Hin1) as (HFF0 & HFF1 & HFFa).
    replace (fs_frame_bytes 1) with 128 in HFF1, HFFa by reflexivity.
    (* the fake frame and its shadow are apart from the held list's blocks *)
    assert (NFF : forall a, (in_zr a (frame_rng ly3 (1, fpos)) \/
        in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)) -> ~ inFP (blk_FP (list_blks H')) a).
    { intros a Ha (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as (b' & <- & Hb'). cbn [fst snd] in Hra.
      rewrite ELB in Hb'.
      assert (Hab : In b' (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPh)); apply in_or_app; left; exact Hb').
      destruct Ha as [Ha | Ha].
      - pose proof (cs_frame_disj_x ly3 S3 W mem mdc b' 1 fpos HAR3 Hab Hin1) as D.
        unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. unfold zdisjoint in D. cbn [fst snd] in D. lia.
      - destruct b' as [p n]. destruct (cs_blk_x ly3 S3 W mem mdc p n HAR3 Hab) as (_ & _ & _ & Happ & _).
        unfold in_zr, shadow_addr in Ha. cbn [fst snd] in Ha, Hra.
        replace (fs_frame_bytes 1 / 8) with 16 in Ha by reflexivity.
        apply (cs_sh_apart (frame_addr ly3 1 fpos) p (req_size n) (a - (SB + frame_addr ly3 1 fpos / 8)) HFFa Happ);
          unfold SB, SHADOW_OFF in *; lia. }
    apply (SRrG_ret segs R R_refl).
    exists H'', ds, cc, ev3. split; [exact RCOK|].
    exists regs', mem', md', ly', S', (k + kk), fpos.
    split.
    { unfold cfg_at. rewrite Q1. change (w64 (fr_B0 + A_rm_csd)) with (Z_to_bv 64 (BASE + A_rm_csd)). reflexivity. }
    split; [exact ((cs_jt XM_LIB XN_LIB RLO HAP) W W2 mem mem' HRV HRV' HROM)|].
    split.
    { (* K2: check_shape_ends' journal inside the arm's *)
      apply (rm_compose_x cx fpos ly3 S3 W mem mdc k G 208 [(lf_F cx + 192, lf_F cx + 192 + 8)] CSHE_STK
        (blk_FP (list_blks H')) ly' S' W2 mem' md' kk HB HJ HJc HGsub ltac:(lia)
        ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK; lia) ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK; lia)).
      - intros a (r & [<-|[]] & Ha). cbn [fst snd] in Ha. lia.
      - apply ((rm_fp_sep B fr_FP) cx _ ly3 S3 (list_blks H') HSEP).
        intros b Hb. rewrite ELB in Hb. split.
        + apply (Permutation_in _ (Permutation_sym MH)). apply in_or_app. left. exact Hb.
        + unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
          * destruct (hl_cap H' =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<-|[]]. cbn [snd].
            apply Z.eqb_neq in Ec. unfold AREC. lia.
          * apply in_map_iff in Hb as (r & <- & _). cbn [snd]. lia. }
    split.
    { (* the frame: kept but the out cell, which the callee left present *)
      rewrite Efa. apply (cs_aframe_kept cx true (frame_addr ly3 1 fpos) W W2 mem mem' HFR).
      - intros a Ha Hna. apply (KS3 a Ha). right. intros (r & [<-|[]] & Har). cbn [fst snd] in Har. lia.
      - intros a Ha. apply cs_wr_of_pres. apply Hpresc. unfold CSHE_STK, CSHE_FRAME, ASTACK. lia.
      - intros a Ha.
        assert (Hfr : in_zr a (frame_rng ly3 (1, fpos)))
          by (unfold in_zr, frame_rng; cbn [fst snd]; replace (fs_frame_bytes 1) with 128 by reflexivity; lia).
        apply KF4; [left; exact Hfr | apply NFF; left; exact Hfr].
      - intros a Ha.
        assert (Hsh : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
        { unfold in_zr, shadow_addr. cbn [fst snd]. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity.
          unfold SB, SHADOW_OFF in *. lia. }
        apply KF4; [right; exact Hsh | apply NFF; right; exact Hsh].
      - lia.
      - lia. }
    split.
    { (* the fake frame's flag word, kept with the fake frame *)
      rewrite Efa, (rm_flag_addr ly3 ly' fpos Efa). apply (rm_flag_kept W W2 mem mem'); [|exact HFL].
      intros a Ha.
      assert (Hfr : in_zr a (frame_rng ly3 (1, fpos)))
        by (unfold in_zr, frame_rng; cbn [fst snd]; replace (fs_frame_bytes 1) with 128 by reflexivity; lia).
      apply KF4; [left; exact Hfr | apply NFF; left; exact Hfr]. }
    split.
    { (* the model *)
      unfold amodel_at. cbn [rm_mk lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
      split; [rewrite cs_rsn_length; exact Hlen4|].
      split.
      { intros i Hi. destruct (Nat.eq_dec i si) as [->|Hne].
        - rewrite cs_rsn_same by lia. exact HSRC'.
        - rewrite cs_rsn_other by lia. pose proof (MSL i Hi) as X. rewrite cs_rsn_other in X by lia.
          assert (KSi : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
              abyte_kept W mem W2 mem' a).
          { intros a Ha. destruct (HGP i Hi) as (_ & _ & _ & _ & Hwr & _). destruct (RGr a) as (H1 & H2 & H3).
            { unfold rg_rng. right. right. right. right. unfold ASRC in *. lia. }
            apply (KG a H1 H2 H3).
            - unfold rm_HA, ASRC in *. lia.
            - intros mm. apply Hwr. unfold rm_HA. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
          assert (Hsl : forall b, In b (slot_blks (nth i (lm_hs m) None)) -> In b (input_blks cx ++ MR ++ rest0)).
          { intros b Hb. apply MSN. apply (cs_slot_in _ i). rewrite cs_rsn_other by lia. exact Hb. }
          destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; cbn [aslot] in X |- *.
          + apply (asrc_at_kept B ly3 S3 W mem ly' S' W2 mem' _ hi X).
            * intros r Hr a Ha.
              destruct (rm_asrc_fp_in_x ly3 S3 W mem mdc _ hi HAR3 X r Hr a Ha) as [Hg | (p & n & Hpn & Hpa)].
              -- apply KSi. exact Hg.
              -- apply (proj2 (BL2 (p, n) (Hsl _ Hpn))). cbn [fst snd]. lia.
            * intros b Hb. exact (proj1 (BL2 b (Hsl b Hb))).
          + destruct X as (Xg & Xw). split.
            * apply (akept_garr8 W mem); [|exact Xg]. intros x Hx. rewrite repeat_length in Hx. apply KSi.
              unfold ASRC in *. lia.
            * apply (akept_awr W mem); [|exact Xw]. intros x Hx. apply KSi. lia. }
      split.
      { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly' S' W2 mem' _ _ MREL).
        - intros r Hr a Ha.
          destruct (rm_arelay_fp_in_x ly3 S3 W mem mdc _ _ HAR3 MREL r Hr a Ha) as [Hg | (p & n & Hpn & Hpa)].
          + destruct Hg as [Hg | [Hg | Hg]].
            * apply KGR; [unfold rg_rng; right; right; left; exact Hg | apply (cs_rng_far si a Hsi); clear - Hg; tauto |
                cs_wrg (rg_src fr_RG) 8%nat].
            * apply KGR; [unfold rg_rng; right; left; exact Hg | apply (cs_rng_far si a Hsi); clear - Hg; tauto |
                cs_wrg (rg_nsrc fr_RG) 4%nat].
            * apply KGM; [unfold rm_mglob; clear - Hg; tauto | cs_wrg (rg_capsrc fr_RG) 4%nat].
          + apply (proj2 (BL2 (p, n) (MRE _ Hpn))). cbn [fst snd]. lia.
        - intros b Hb. exact (proj1 (BL2 b (MRE b Hb))). }
      split.
      { assert (KAO : akept W mem W2 mem' cs_aout_g).
        { intros r Hr a Ha. cbn [cs_aout_g In] in Hr.
          destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd] in Ha;
            (apply KGM; [unfold rm_mglob; clear - Ha; tauto|]).
          - cs_wrg (rg_send_max fr_RG) 8%nat.
          - cs_wrg (rg_nout fr_RG) 8%nat.
          - cs_wrg (rg_capout fr_RG) 8%nat.
          - cs_wrg (rg_out fr_RG) 8%nat.
          - cs_wrg (rg_client fr_RG) 4%nat.
          - cs_wrg (rg_client_broken fr_RG) 1%nat.
          - cs_wrg (rg_send_dead fr_RG) 1%nat.
          - cs_wrg (rg_send_eintr fr_RG) 1%nat. }
        apply ((cs_aout_ev B) ly3 S3 W mem ly' S' W2 mem' _ _ _ _ _ _ ev3 MOUT KAO); [| | exact Hev3 | exact Hev3w | exact Hev3r].
        - intros a Hc Ha.
          assert (Hb : In (out2, cap2) (aout_blks cap2 out2))
            by (unfold aout_blks; replace (cap2 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc); left; reflexivity).
          apply (proj2 (BL2 _ (MAO _ Hb))). cbn [fst snd]. lia.
        - intros b Hb. exact (proj1 (BL2 b (MAO b Hb))). }
      split.
      { apply (agone_at_kept fr_RG W mem W2 mem' _ MGN). intros r [<-|[]] a Ha. cbn [fst snd] in Ha.
        apply KGM; [unfold rm_mglob; clear - Ha; tauto | cs_wrg (rg_gone fr_RG) 1%nat]. }
      split.
      { apply (alock_at_kept fr_RG W mem W2 mem' _ MLK). intros r [<-|[]] a Ha. cbn [fst snd] in Ha.
        apply KGR; [unfold rg_rng; left; exact Ha | apply (cs_rng_far si a Hsi); clear - Ha; tauto | cs_wrg (rg_lock fr_RG) 12%nat]. }
      split.
      { apply (awake_at_kept fr_RG W mem W2 mem' MWK). intros r [<-|[]] a Ha. cbn [fst snd] in Ha.
        apply KGR; [unfold rg_rng; right; right; right; left; exact Ha | apply (cs_rng_far si a Hsi); clear - Ha; tauto |
          cs_wrg (rg_wake fr_RG + 4) 4%nat]. }
      assert (KN : forall x, AG_NFD <= x < AG_NFD + 4 -> abyte_kept W mem W2 mem' x)
        by (intros x Hx; apply KGM; [unfold rm_mglob; clear - Hx; tauto | cs_wrg AG_NFD 4%nat]).
      assert (KL : forall x, AG_LISTEN <= x < AG_LISTEN + 4 -> abyte_kept W mem W2 mem' x)
        by (intros x Hx; apply KGM; [unfold rm_mglob; clear - Hx; tauto | cs_wrg AG_LISTEN 4%nat]).
      split; [apply (akept_vm W mem); [intros x Hx; apply KN; cs_zn Hx; lia | exact MNFD]|].
      split; [apply (akept_awr W mem); [exact KN | exact MNFDw]|].
      split; [exact MNFDb|].
      split; [apply (akept_vm W mem); [|exact MTU]; intros x Hx; cs_zn Hx;
        apply KGM; [unfold rm_mglob; clear - Hx; tauto | cs_wrg AG_THREAD_UP 1%nat]|].
      split; [destruct MLST as (lst & Hlst); exists lst; apply (akept_vm W mem); [intros x Hx; apply KL; cs_zn Hx; lia | exact Hlst]|].
      apply (akept_awr W mem); [exact KL | exact MLSTw]. }
    split; [exact ((cs_input_kept B) cx ly3 S3 W mem ly' S' W2 mem' HIN (eq_sym HlenP)
      (fun b Hb => BL2 b (in_or_app _ _ _ (or_introl Hb))))|].
    split; [exact HRV'|].
    split; [exact (rm_sep_step_x cx fpos ly3 S3 W mem mdc k _ _ ly' S' W2 mem' md' rest0 HJ HSEP HAR' HPm HP')|].
    split.
    { destruct HQ as (ly0 & S0 & HLS & HMle & HMF & HFR0 & HC0 & HR3). exists ly0, S0. split; [exact HLS|].
      split; [unfold rm_cshe_cost; exact (mo_le_trans MT ML S0 S3 S' _ _ HMle HMO)|]. split; [exact HMF|].
      split; [exact (rm_fr_step B _ _ _ _ _ _ _ _ _ _ rest0 HFR0 HPm HP')|]. split; [exact HC0 | exact HR3]. }
    split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
    (* the registers *)
    rewrite Efa. unfold lregs_rmc, rm_regs_base.
    repeat split.
    all: try (match goal with |- getr _ ?r = _ =>
      rewrite (cs_pres _ _ r HP2 ltac:(cs_cs)), (KR r ltac:(cs_ink)); assumption end).
    all: try exact (proj1 Rt). all: try exact (proj2 Rt).
    { apply (cs_sv8_kept W W2 mem mem'); [|exact R144]. intros x Hx. apply (KS3 x); [lia|]. right.
      intros (r & [<-|[]] & Hr). cbn [fst snd] in Hr. lia. }
    { exact HAT2. }
Qed.
(* (7) at = *(F+192); check_shape_done(at) *)
(* (7) at = *(F+192); check_shape_done(at) *)
(* ---- (7)'s walk: 0x84a0c `ld a0,192(s1); jal check_shape_done` (ret 0x84a14 = A_rm_sr).  s1 = F (atom 9, the
   band rm_entry's rme_facts gives it) with the cell at = F + 192, read only here, holding av (atom 33); atom 32 = SB
   is the shadow base.  check_shape_done is a strict leaf (CSD): the segment is its strict walk over the R journal,
   lifted by SRr_SRrG, the leaf's post journal weakened to R by aji0_of_x ---- *)
Lemma rm_csd_xR : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev3 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  RCUT_x cx (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev3) O2 cap2 out2)
    ((rm_Qc h j0) cx t m (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev3) O2 cap2 out2)
      ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H'))
    ((lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc)) A_rm_csd W c ->
  SRrG segs R W c (fun W' c' => exists ev4,
    RCUT_x cx (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev4) O2 cap2 out2)
      ((rm_Qc h j0) cx t m (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev4) O2 cap2 out2)
        ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H'))
      ((lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc)) A_rm_sr W' c').
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev3 W c HB HRI HAT HRR HCN HCS HRC.
  destruct HRC as (regs & mem & md & ly3 & S3 & k & fpos & -> & HROM & HJ & HFR & HFL & HMOD & HIN & HRV & HSEP & HQ & HNP & HR).
  apply (SRr_SRrG segs R WLE_R).
  pose proof HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Rt) & R20 & R21 & R22 &
    R144 & R192).
  assert (Hsi : (si < 4)%nat) by (destruct HAT as (_ & _ & _ & _ & Hs & _); exact Hs).
  set (h2 := set_held (set_exp_held h1 E' H') H'') in *.
  (* ---- the frame's numbers, and at = g_nout = |O2| < 2 ^ 64 ---- *)
  destruct (cn_nums_x cx ly3 S3 W mem md k fpos HB HJ) as (_ & Hsp00 & _ & HFb0 & _ & _ & _ & HAR0).
  pose proof asan_consts as (C1 & _).
  assert (HFn : alloc_ceiling + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) <= 2 ^ 47)
    by (unfold LLVMF_STK in Hsp00; lia).
  clear Hsp00 HFb0.
  assert (HF46 : 2 ^ 46 <= lf_F cx) by (pose proof rme_ceil_lo; lia).
  assert (HF47 : lf_F cx + 320 <= 2 ^ 47) by lia.
  assert (Hgn01 : 0 <= lm_gn m <= 1)
    by (pose proof HMOD as (_ & _ & _ & _ & (_ & _ & Hg) & _); cbn [rm_mk lm_gn] in Hg; clear - Hg;
        destruct Hg as [Hg|Hg]; lia).
  pose proof (RI_rm_csd cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HRI HAT HRR HCN HCS Hgn01) as HAV.
  destruct (cn_out_pre_x cx m si h2 j0 (rm_cev c2 ev3) O2 cap2 out2 ly3 S3 W mem md HAR0 Hsi HMOD HSEP)
    as (HSRC1 & _ & _ & HVN & _ & _ & HRNG & HOB).
  assert (HOn : Z.of_nat (length O2) < 2 ^ 64).
  { destruct HOB as [HO0 | (CO & _ & Hin & _)]; [rewrite HO0; cbn [length Z.of_nat]; lia|].
    destruct (al_blocks_0 ly3 S3 W mem md out2 CO HAR0 Hin) as (_ & H4096 & _).
    clear - HRNG H4096. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HRNG. lia. }
  clear HOB HRNG HAR0.
  assert (Hav : 0 <= rm_A1 m h1 + cc < 2 ^ 64) by (rewrite HAV; lia).
  assert (HVN' : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 (rm_A1 m h1 + cc)) by (rewrite HAV; exact HVN).
  clear HVN.
  (* ---- the walk to check_shape_done's entry ---- *)
  destruct (cd_entry W regs mem (lf_F cx) (rm_A1 m h1 + cc) R9 HF46 HF47 R192 Hav) as [HS SHOK].
  remember (Eimg (Ereg regs (cd_extra (rm_A1 m h1 + cc)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (cd_extra (rm_A1 m h1 + cc))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E33 : ew E 33 = Z_to_bv 64 (rm_A1 m h1 + cc))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + A_rm_csd)) with (Z_to_bv 64 (BASE + A_rm_csd)).
  paj_run_to_tok_x cn_RUNTO HS HJ SHOK cn_span AF_fr_check_shape_done.
  { cbn [ss_mem add_cond cd_ss cd_regions]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  pmkst HS.
  cn_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (cd_extra (rm_A1 m h1 + cc)) cd_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  clear HS SHOK HF HFr.
  destruct (cn_nums_x cx ly3 S3 W mem mdc k fpos HB HJ) as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & Hfrs & HAR).
  (* ---- the call's registers and check_shape_done's afn_pre (K1) ---- *)
  assert (Q10' : getr (ms_regs ms) 10 = w64 (rm_A1 m h1 + cc)) by (rewrite Q10, E33; reflexivity).
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (HCS0 : 0 <= CSD_STK /\ CSD_STK + 352 <= LLVMF_STK) by (split; vm_compute; intro Hc'; discriminate Hc').
  destruct (rm_afn_pre_at_x cx true ly3 S3 fpos k W mem mdc (ms_regs ms) CSD_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { exact (proj1 HCS0). }
  { exact (proj2 HCS0). }
  eapply SRr_mono.
  { exact (CSD W ly3 S3 [] (ms_regs ms) mem mdc ch (rm_A1 m h1 + cc) HPREc Q10' Hav HVN'). }
  (* ---- after check_shape_done: its journal at G = [], XO = 0, OUT = [], FP = [] composed (K2), kept bytes (K4) ---- *)
  cbv beta. intros W' c' _ (regs' & mem' & md' & -> & HJl & HPR & _ & HPRES & _).
  rewrite Hsp1 in HJl. apply aji0_of_x in HJl.
  apply (proj2 (ajournal_gx_nil0 CSD_STK (lf_F cx) [] ly3 S3 W mem mdc [] ly3 S3 W' mem' md' 0)) in HJl.
  assert (HG1 : forall a, inG [] a -> inG G_fr a) by (intros a Ha; exfalso; exact (inG_nil a Ha)).
  assert (HOUT : forall a, inFP [] a -> lf_F cx <= a < lf_F cx + 0) by (intros a Ha; exfalso; exact (inFP_nil a Ha)).
  assert (HFP : forall a, inFP [] a -> exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n /\
      (~ In (b, n) (ablocks B (c_ly cx) (c_S cx)) \/ inFP (lf_FP fr_FP cx) a))
    by (intros a Ha; exfalso; exact (inFP_nil a Ha)).
  assert (Hsink : ~ YI16.sink_open_fp []) by (intros (r & Hr & _); destruct Hr).
  pose proof (rm_compose_x cx fpos ly3 S3 W mem mdc k [] 0 [] CSD_STK [] ly3 S3 W' mem' md' 0 HB HJ HJl HG1
    ltac:(lia) (proj1 HCS0) (proj2 HCS0) HOUT HFP) as HJ'.
  destruct (rm_kept_x cx fpos ly3 S3 W mem mdc k [] 0 [] CSD_STK [] ly3 S3 W' mem' md' 0 HB HJ HJl HG1
    ltac:(lia) (proj1 HCS0) (proj2 HCS0) Hsink) as (KA & KB & KC & KD & KE & KF & KAR).
  (* errno after the call *)
  destruct (ERR ly3 S3 [] W' mem' md' KAR) as ((ev4 & Hev & Hevr) & Hew).
  exists ev4.
  (* the kept bytes: the model's image cells (view by K4, writability by presence), every live block *)
  assert (KG : forall a, (rm_mglob a \/ rg_rng fr_RG a) -> abyte_kept W mem W' mem' a).
  { intros a Ha. destruct ((cn_glob_facts B RGP HMG) a Ha) as (I1 & I2 & I3).
    split; [exact (proj1 (KA a I1 (fun H0 => inG_nil a H0) I2 I3))|].
    apply cn_awr_kept. exact (HPRES a). }
  assert (KBL : forall b, In b (ablocks B ly3 S3) ->
      In b (ablocks B ly3 S3) /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros [p n] Hb. split; [exact Hb|]. cbn [fst snd]. intros a Ha.
    destruct (al_blocks_0 ly3 S3 W mem mdc p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos n (proj1 Hn0)) as [_ Rn].
    replace a with (p + (a - p)) by lia.
    apply (KB p n (a - p) Hb Hb); [lia|]. intros Hf. exact (inFP_nil _ Hf). }
  set (m1 := rm_mk cx m si (Some h2) j0 (rm_cev c2 ev3) O2 cap2 out2) in *.
  assert (Hsil : (si < length (lm_hs m))%nat).
  { pose proof HMOD as (M1 & _). unfold m1, rm_mk in M1. cbn [lm_hs] in M1. rewrite cn_rsn_length in M1. lia. }
  pose proof HSEP as [[rest0 Hp3] _].
  assert (HMB : forall b, In b (model_blks m1) -> In b (ablocks B ly3 S3))
    by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hp3 |
        apply in_or_app; right; apply in_or_app; left; exact Hb]).
  pose proof (cn_model_perm cx m si (Some h2) j0 (rm_cev c2 ev3) O2 cap2 out2 Hsil) as HM1.
  assert (KYR : forall b, In b (cn_rest m si j0 cap2 out2) ->
      In b (ablocks B ly3 S3) /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros b Hb. apply KBL. apply HMB. eapply Permutation_in; [apply Permutation_sym; exact HM1|].
    apply in_or_app. right. exact Hb. }
  assert (HSRC : asrc_at B ly3 S3 W' mem' (rm_HA si) h2).
  { refine (cn_aslot_kept_x ly3 S3 W mem mdc ly3 S3 W' mem' si (Some h2) HAR HSRC1 _ _).
    - intros a Ha. apply KG. right. unfold rg_rng. right; right; right; right. clear - Ha Hsi. unfold ASRC in *. lia.
    - intros b Hb. apply KBL. apply HMB. eapply Permutation_in; [apply Permutation_sym; exact HM1|].
      apply in_or_app. left. exact Hb. }
  (* ---- the cut at 0x84a14 ---- *)
  assert (HMOD' : amodel_at B ly3 S3 W' mem' (rm_mk cx m si (Some h2) j0 (rm_cev c2 ev4) O2 cap2 out2))
    by exact (cn_model_kept_x cx m si h2 h2 j0 (rm_cev c2 ev3) ev4 O2 cap2 out2 ly3 S3 W mem mdc ly3 S3 W' mem' HAR Hsi
      HMOD HSRC (fun a Ha _ => KG a Ha) KYR Hev Hew Hevr).
  assert (HFR' : aframe_at cx true (frame_addr ly3 1 fpos) W' mem').
  { pose proof HFR as (_ & HAWR & _).
    apply (cn_aframe_kept cx true (frame_addr ly3 1 fpos) W W' mem mem' HFR).
    - intros a Ha _. apply KC; [exact Ha | left; lia].
    - intros a Ha. assert (Hk : abyte_kept W mem W' mem' a) by (apply KC; [lia | left; lia]).
      apply (proj2 Hk).
      replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia.
    - intros a Ha. apply KD; [| intros Hf; exact (inFP_nil _ Hf)].
      left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
    - intros a Ha. apply KD; [| intros Hf; exact (inFP_nil _ Hf)].
      right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      cbv [SB SHADOW_OFF] in Ha |- *. lia.
    - lia.
    - lia. }
  assert (HFL' : sv8 W' mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
  { apply (rm_flag_kept W W' mem mem'); [|exact HFL].
    intros a Ha. apply KD; [| intros Hf; exact (inFP_nil _ Hf)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia. }
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx)))
    by (destruct HB as (_ & HPRE0); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE0))))))).
  assert (KYI : forall b, In b (input_blks cx) ->
      In b (ablocks B ly3 S3) /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros b Hb. apply KBL. eapply Permutation_in; [apply Permutation_sym; exact Hp3|]. apply in_or_app. left. exact Hb. }
  pose proof ((cn_input_kept B) cx ly3 S3 W mem ly3 S3 W' mem' HIN (eq_sym HlenP) KYI) as HIN'.
  assert (HRV' : rom_view segs W' mem').
  { pose proof (ajournal_gx_G_mono0 [] G_fr 0 [] CSD_STK (lf_F cx) [] ly3 S3 W mem mdc [] ly3 S3 W' mem' md' 0
      HG1 HJl) as HJcG.
    exact (ajournal_gx_rom_view0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJcG HRO HRV). }
  assert (KRR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r cd_kept -> getr regs' r = getr regs r).
  { intros r H1 H2. pose proof (HPR _ H1) as Hp. rewrite !Z_to_bv_bv_unsigned in Hp. rewrite Hp. exact (KR r H2). }
  assert (H144 : sv8 W' mem' (lf_F cx + 144) (c_n cx - rm_k' cx m)).
  { apply (cn_sv8_kept W W' mem mem'); [|exact R144]. intros x Hx. apply KC; [lia | left; lia]. }
  assert (H192 : sv8 W' mem' (lf_F cx + 192) (rm_A1 m h1 + cc)).
  { apply (cn_sv8_kept W W' mem mem'); [|exact R192]. intros x Hx. apply KC; [lia | left; lia]. }
  assert (HR' : (lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc) (frame_addr ly3 1 fpos) regs' W' mem').
  { unfold lregs_rmc, rm_regs_base.
    repeat split;
      first [ match goal with |- getr regs' ?r = _ => rewrite (KRR r ltac:(cn_cs) ltac:(unfold cd_kept; cn_in)) end;
              assumption
            | exact H144 | exact H192 | lia ]. }
  exists regs', mem', md', ly3, S3, (k + 0), fpos.
  split.
  { unfold cfg_at. rewrite Q1. change (w64 (fr_B0 + A_rm_sr)) with (Z_to_bv 64 (BASE + A_rm_sr)). reflexivity. }
  split; [exact ((cn_jt XM_LIB XN_LIB RLO HAP) W W' mem mem' HRV HRV' HROM)|].
  split; [exact HJ'|].
  split; [exact HFR'|].
  split; [exact HFL'|].
  split; [exact HMOD'|].
  split; [exact HIN'|].
  split; [exact HRV'|].
  split; [exact HSEP|].
  split; [exact HQ|].
  split; [exact HNP|].
  exact HR'.
Qed.
(* (8) source_reset(s): the slot is closed *)
(* ================================================================== (8) rm_sr_x: helpers (rsr_) *)
(* source_reset's blocks (W_contract.v hs_blks) are slot si's (asrc_blks), in another order *)
Lemma rsr_model_kept_x : forall cx m si h3 j0 c ev O cap out ly S (W : world segs) mem md ly' S' (W' : world segs) mem',
  AR0 ly S W mem md -> (si < 4)%nat ->
  amodel_at B ly S W mem (rm_mk cx m si (Some h3) j0 c O cap out) ->
  asrc_closed W' mem' (rm_HA si) ->
  (forall a, (rm_mglob a \/ rg_rng fr_RG a) -> ~ (rm_HA si <= a < rm_HA si + ASRC) -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (cn_rest m si j0 cap out) ->
     In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  amodel_at B ly' S' W' mem' (rm_mk cx m si None j0 (rm_cev c ev) O cap out).
Proof.
  intros cx m si h3 j0 c ev O cap out ly S W mem md ly' S' W' mem' HAR Hsi HMOD HCL KG KY Hev Hew Hevr.
  assert (KGm : forall a, rm_mglob a -> abyte_kept W mem W' mem' a).
  { intros a Ha. apply KG; [left; exact Ha|]. pose proof (cn_mglob_out_s a Ha) as Ho. clear - Ho Hsi.
    unfold rm_HA, ASRC in *. lia. }
  assert (KGr : forall a, (rg_lock fr_RG <= a < rg_lock fr_RG + 12 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
      rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8) ->
      abyte_kept W mem W' mem' a).
  { intros a Ha. apply KG.
    - right. unfold rg_rng. tauto.
    - pose proof (cn_rg_out_s a Ha) as Ho. clear - Ho Hsi. unfold rm_HA, ASRC in *. lia. }
  assert (KGs : forall i, (i < 4)%nat -> i <> si -> forall a,
      rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC -> abyte_kept W mem W' mem' a).
  { intros i Hi Hne a Ha. apply KG.
    - right. unfold rg_rng. right; right; right; right. clear - Ha Hi. unfold ASRC in *. lia.
    - clear - Ha Hi Hsi Hne. unfold rm_HA, ASRC in *. lia. }
  unfold rm_mk in HMOD |- *. unfold amodel_at in HMOD |- *.
  cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd] in HMOD |- *.
  destruct HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  rewrite cn_rsn_length in M1.
  assert (KYs : forall i h b, (i < 4)%nat -> nth i (rm_set_nth si None (lm_hs m)) None = Some h ->
     In b (asrc_blks h) ->
     In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros i h b Hi Hn Hb. apply KY. unfold cn_rest. right. apply in_or_app. right. apply in_or_app. left.
    apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
    rewrite <- Hn. apply in_map. apply nth_In. rewrite cn_rsn_length. lia. }
  split; [rewrite cn_rsn_length; exact M1|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
    - rewrite cn_rsn_same by lia. cbn [aslot]. exact HCL.
    - rewrite cn_rsn_other by lia. pose proof (M2 i Hi) as Mi. rewrite cn_rsn_other in Mi by lia.
      apply (cn_aslot_kept_x ly S W mem md ly' S' W' mem' i _ HAR Mi).
      + exact (KGs i Hi Hne).
      + intros b Hb. destruct (nth i (lm_hs m) None) as [h|] eqn:En; [|cbn in Hb; destruct Hb].
        apply (KYs i h b Hi); [rewrite cn_rsn_other by lia; exact En | exact Hb]. }
  split.
  { apply (cn_arelay_kept_x ly S W mem md ly' S' W' mem' _ _ HAR M3).
    - intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
      + apply KGr. right; right; left. exact Ha.
      + apply KGr. right; left. exact Ha.
      + apply KGm. unfold rm_mglob. left. exact Ha.
    - intros b Hb. apply KY. unfold cn_rest. unfold arelay_blks in Hb.
      destruct Hb as [<- | Hb]; [left; reflexivity | right; apply in_or_app; left; exact Hb]. }
  split.
  { apply ((cn_aout_kept B) ly S W mem ly' S' W' mem' _ _ _ _ _ _ ev M4); [| |exact Hev|exact Hew|exact Hevr].
    - intros a Ha. apply KGm. unfold rm_mglob. tauto.
    - intros b Hb. apply KY. unfold cn_rest. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r [<- | []] a Ha. apply KGm. unfold rm_mglob.
    cbn [fst snd] in Ha. tauto. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r [<- | []] a Ha. apply KGr. cbn [fst snd] in Ha. tauto. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r [<- | []] a Ha. apply KGr. cbn [fst snd] in Ha. tauto. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KGm. unfold rm_mglob.
    assert (AG_NFD <= x < AG_NFD + 4) by lia. tauto. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KGm. unfold rm_mglob. tauto. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KGm. unfold rm_mglob.
    assert (AG_THREAD_UP <= x < AG_THREAD_UP + 1) by lia. tauto. }
  split.
  { destruct M12 as [lst Hl]. exists lst. apply (akept_vm W mem); [|exact Hl]. intros x Hx. apply KGm.
    unfold rm_mglob. assert (AG_LISTEN <= x < AG_LISTEN + 4) by lia. tauto. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KGm. unfold rm_mglob. tauto.
Qed.

(* ---- the 2-instruction walk 0x84a14: a0 = s5, jal source_reset (no memory read); cn_entry's shape at A_rm_sr.
   source_reset frees: the walk runs at R up to the call, SR_R's R journal is composed by rm_compose_x ---- *)
Lemma rm_sr_xR : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev4 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  RCUT_x cx (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev4) O2 cap2 out2)
    ((rm_Qc h j0) cx t m (rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 (rm_cev c2 ev4) O2 cap2 out2)
      ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H'))
    ((lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc)) A_rm_sr W c ->
  SRrG segs R W c (fun W' c' => exists ev5,
    RCUT_x cx (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2)
      ((rm_Qc h j0) cx t m (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2)
        ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H' +
         sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))))
      ((lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc)) A_rm_end W' c').
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev4 W c HB HRI HAT HRR HCN HCS HRC.
  destruct HRC as (regs & mem & md & ly3 & S3 & k & fpos & -> & HROM & HJ & HFR & HFL & HMOD & HIN & HRV & HSEP & HQ & HNP & HR).
  pose proof HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Rt) & R20 & R21 & R22 &
    R144 & R192).
  assert (Hsi : (si < 4)%nat) by (destruct HAT as (_ & _ & _ & _ & Hs & _); exact Hs).
  (* ---- the walk to source_reset's entry ---- *)
  destruct (rsr_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs cn_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs cn_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + A_rm_sr)) with (Z_to_bv 64 (BASE + A_rm_sr)).
  paj_run_to_tok_xR cn_RUNTOG HS HJ SHOK cn_span AF_fr_source_reset.
  { apply awr_ok_x_nil. }
  pmkst HS.
  cn_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs cn_extra rsr_kept HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  clear HS SHOK HF HFr.
  (* ---- the frame's numbers and the call's registers ---- *)
  destruct (cn_nums_x cx ly3 S3 W mem mdc k fpos HB HJ) as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & Hfrs & HAR).
  pose proof asan_consts as (C1 & _).
  assert (HFn : alloc_ceiling + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) <= 2 ^ 47)
    by (unfold LLVMF_STK in Hsp0; lia).
  assert (Q10' : getr (ms_regs ms) 10 = w64 (rm_HA si)) by (rewrite Q10, (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (HSS : 0 <= SR_STK /\ SR_STK + 352 <= LLVMF_STK) by (split; vm_compute; intro Hc; discriminate Hc).
  (* K1: source_reset's afn_pre *)
  destruct (rm_afn_pre_at_x cx true ly3 S3 fpos k W mem mdc (ms_regs ms) SR_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { exact (proj1 HSS). }
  { exact (proj2 HSS). }
  (* ---- source_reset's G: slot si, a range of program globals (gx_prog from HGP) ---- *)
  set (h3 := set_held (set_exp_held h1 E' H') H'') in *.
  set (Gs := [(rm_HA si, ASRC)]).
  assert (HGc : forall a, inG Gs a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
  { intros a Ha. unfold Gs, inG in Ha. apply Exists_exists in Ha as (r & [<- | []] & Hz). unfold in_zr in Hz.
    cbn [fst snd] in Hz. clear - Hz Hsi. unfold rm_HA, ASRC in *. lia. }
  pose proof (SR_R Gs (HGP si Hsi)) as HSR.
  (* ---- the premises ---- *)
  assert (HGin : forall a, rm_HA si <= a < rm_HA si + ASRC -> inG Gs a)
    by (intros a Ha; unfold Gs, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
  assert (HAZ : azs B (rm_HA si) ASRC).
  { apply ((cn_azs_sub B) (rg_s fr_RG) (4 * ASRC)); [exact HZS | |]; clear - Hsi; unfold rm_HA, ASRC; lia. }
  assert (HSRC3 : asrc_at B ly3 S3 W mem (rm_HA si) h3)
    by exact (proj1 (cn_out_pre_x cx m si h3 j0 (rm_cev c2 ev4) O2 cap2 out2 ly3 S3 W mem mdc HAR Hsi HMOD HSEP)).
  assert (HMOk : mo_ok MT S3 (sr_cost MT (Some h3))).
  { destruct HQ as (ly0 & S0 & HLS & HLE & _ & _ & _ & HR3). pose proof HR3 as (_ & _ & _ & HU & _).
    exact (LS_rm_sr_pre cx t m ly0 S0 S3 si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HLS HRI HAT HRR Rt HU HCN
      HCS HLE). }
  assert (HCNT : cnt_ok_pk RP sr_pk (ablocks B ly3 S3)).
  { destruct HQ as (ly0 & S0 & _ & _ & HMF & HFR0 & HC0 & HR3).
    exact (rm_cnt_step cx ly0 S0 m _ ly3 S3 _ _ HFR0
      (fun P => RM_CNT_sr cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc P HRI HAT HRR HCN HCS HMF HR3
         (RI_rm_src cx t m si h j0 HRI HAT)) HC0). }
  eapply SRrG_mono.
  { assert (HA8 : rm_HA si mod 8 = 0).
    { unfold rm_HA, ASRC. change (rg_s fr_RG) with 0x5d88e0.
      replace (0x5d88e0 + 96 * Z.of_nat si) with ((0xbb11c + 12 * Z.of_nat si) * 8) by lia. apply Z_mod_mult. }
    apply (HSR W ly3 S3 [] (ms_regs ms) mem mdc ch (rm_HA si) (Some h3) HPREc Q10' HA8 HSRC3 HGin HAZ HRV HMOk 0%nat
      (proj2 (RP_NP S3 _) HNP) HCNT). }
  (* ---- after source_reset ---- *)
  cbv beta. intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & kk & -> & HJc & HPR & HCL & HPERM & HPK & _ & HFRS
    & HMO & HRM').
  assert (EHp' : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
  cbn [sr_blks] in HJc, HPERM.
  rewrite Hsp1 in HJc.
  set (m1 := rm_mk cx m si (Some h3) j0 (rm_cev c2 ev4) O2 cap2 out2) in *.
  assert (Hsil : (si < length (lm_hs m))%nat).
  { pose proof HMOD as (M1 & _). unfold m1, rm_mk in M1. cbn [lm_hs] in M1. rewrite cn_rsn_length in M1. lia. }
  pose proof HSEP as [[rest0 Hp3] _].
  set (RB := cn_rest m si j0 cap2 out2).
  assert (HM1 : Permutation (model_blks m1) (hs_blks h3 ++ RB)).
  { eapply Permutation_trans; [exact (cn_model_perm cx m si (Some h3) j0 (rm_cev c2 ev4) O2 cap2 out2 Hsil)|].
    apply Permutation_app_tail. exact (rsr_asrc_hs h3). }
  pose proof (Permutation_trans Hp3 (rsr_perm_out (input_blks cx) (model_blks m1) (hs_blks h3) RB rest0 HM1))
    as Hp3'.
  (* K2 / K4's premises *)
  assert (HG1 : forall a, inG Gs a -> inG G_fr a) by (intros a Ha; exact (HGs a (HGc a Ha))).
  assert (HOUT : forall a, inFP [] a -> lf_F cx <= a < lf_F cx + 0) by (intros a (r & [] & _)).
  assert (HL1m : forall b, In b (hs_blks h3) -> In b (model_blks m1) /\ 0 < snd b).
  { intros b Hb.
    assert (Hba : In b (asrc_blks h3))
      by (eapply Permutation_in; [apply Permutation_sym; exact (rsr_asrc_hs h3) | exact Hb]).
    split; [|exact ((rr_asrc_pos B) _ _ _ _ _ _ _ HSRC3 Hba)].
    eapply Permutation_in; [apply Permutation_sym; exact HM1 | apply in_or_app; left; exact Hb]. }
  assert (HL13 : forall b, In b (hs_blks h3) -> In b (ablocks B ly3 S3)).
  { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hp3' | apply in_or_app; left; exact Hb]. }
  pose proof ((rm_fp_sep B fr_FP) cx m1 ly3 S3 (hs_blks h3) HSEP HL1m) as HFP.
  assert (Hsink : ~ YI16.sink_open_fp (blk_FP (hs_blks h3))).
  { intros (r & Hr & Hra). destruct (HFP 0 (ex_intro _ r (conj Hr Hra))) as (b & n & Hb & Hba & _).
    destruct (al_blocks_0 ly3 S3 W mem mdc b n HAR Hb) as (_ & H4096 & _). clear - Hba H4096. lia. }
  pose proof (rm_compose_x cx fpos ly3 S3 W mem mdc k Gs 0 [] SR_STK (blk_FP (hs_blks h3))
    ly' S' W' mem' md' kk HB HJ HJc HG1 ltac:(lia) (proj1 HSS) (proj2 HSS) HOUT HFP) as HJ'.
  destruct (rm_kept_x cx fpos ly3 S3 W mem mdc k Gs 0 [] SR_STK (blk_FP (hs_blks h3))
    ly' S' W' mem' md' kk HB HJ HJc HG1 ltac:(lia) (proj1 HSS) (proj2 HSS) Hsink) as (KA & KB & KC & KD & KE & KF & KAR).
  (* errno after the call *)
  destruct (ERR ly' S' [] W' mem' md' KAR) as ((ev5 & Hev & Hevr) & Hew).
  exists ev5.
  set (m2 := rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2).
  (* the blocks: slot si's leave, the rest Y the call keeps *)
  pose proof (HPERM _ Hp3') as Hp'.
  assert (Hp'' : Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m2 ++ rest0)).
  { eapply Permutation_trans; [exact Hp'|]. apply Permutation_app_head. apply Permutation_app_tail.
    apply Permutation_sym. exact (cn_model_perm cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2 Hsil). }
  pose proof (rm_sep_step_x cx fpos ly3 S3 W mem mdc k m1 m2 ly' S' W' mem' md' rest0 HJ HSEP KAR Hp3 Hp'') as HSEP'.
  pose proof (cn_keep_y_x ly3 S3 W mem mdc ly' S' W' mem' (hs_blks h3) [] (input_blks cx ++ RB ++ rest0)
    HAR Hp3' Hp' KB) as KY.
  assert (KYR : forall b, In b RB ->
      In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros b Hb. apply KY. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (KYI : forall b, In b (input_blks cx) ->
      In b (ablocks B ly' S') /\ (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)).
  { intros b Hb. apply KY. apply in_or_app. left. exact Hb. }
  (* the image cells outside slot si: their view (K4) and their presence (apres_kept) *)
  assert (KG : forall a, (rm_mglob a \/ rg_rng fr_RG a) -> ~ (rm_HA si <= a < rm_HA si + ASRC) ->
      abyte_kept W mem W' mem' a).
  { intros a Ha Hns. destruct ((cn_glob_facts B RGP HMG) a Ha) as (I1 & I2 & I3).
    split; [exact (proj1 (KA a I1 (rsr_notG si a Hns) I2 I3))|].
    apply cn_awr_kept. exact (HPK a I1 I2 I3). }
  (* ---- the cut at 0x84a1c ---- *)
  assert (HMOD' : amodel_at B ly' S' W' mem' m2)
    by exact (rsr_model_kept_x cx m si h3 j0 (rm_cev c2 ev4) ev5 O2 cap2 out2 ly3 S3 W mem mdc
      ly' S' W' mem' HAR Hsi HMOD HCL KG KYR Hev Hew Hevr).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFR' : aframe_at cx true (frame_addr ly' 1 fpos) W' mem').
  { rewrite KE. apply (rr_aframe_kept cx (frame_addr ly3 1 fpos) W W' mem mem' HFR).
    - intros a Ha. apply KC; [exact Ha | left; lia].
    - intros a [Ha | Ha].
      + apply KD.
        * left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
        * apply (cn_frame_not_fp_x ly3 S3 W mem mdc (hs_blks h3) 1 fpos a HAR Hin1 HL13). left.
          unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
      + assert (Hs : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
        { unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
          cbv [SB SHADOW_OFF] in Ha |- *. lia. }
        apply KD; [right; exact Hs|].
        exact (cn_frame_not_fp_x ly3 S3 W mem mdc (hs_blks h3) 1 fpos a HAR Hin1 HL13 (or_intror Hs)).
    - lia.
    - lia. }
  assert (HFL' : sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { rewrite KE, (rm_flag_addr ly3 ly' fpos KE). apply (rm_flag_kept W W' mem mem'); [|exact HFL].
    intros a Ha. apply KD.
    - left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
    - apply (cn_frame_not_fp_x ly3 S3 W mem mdc (hs_blks h3) 1 fpos a HAR Hin1 HL13). left.
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia. }
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx)))
    by (destruct HB as (_ & HPRE0); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE0))))))).
  pose proof ((cn_input_kept B) cx ly3 S3 W mem ly' S' W' mem' HIN (eq_sym HlenP) KYI) as HIN'.
  assert (HRV' : rom_view segs W' mem').
  { pose proof (ajournal_gx_G_mono0 Gs G_fr 0 [] SR_STK (lf_F cx)
      (blk_FP (hs_blks h3)) ly3 S3 W mem mdc [] ly' S' W' mem' md' kk HG1 HJc) as HJcG.
    exact (ajournal_gx_rom_view0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJcG HRO HRV). }
  assert (HQ' : (rm_Qc h j0) cx t m m2 ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H' +
      sr_cost MT (Some h3)) ly' S').
  { destruct HQ as (ly0 & S0 & HLS & HLE & HMF & HFR0 & HC0 & HR3). exists ly0, S0. split; [exact HLS|].
    split; [exact (mo_le_trans MT ML _ _ _ _ _ HLE HMO)|]. split; [exact HMF|].
    split; [exact (rm_fr_step B _ _ _ _ _ _ _ _ _ _ rest0 HFR0 Hp3 Hp'')|]. split; [exact HC0 | exact HR3]. }
  assert (KRR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r rsr_kept -> getr regs' r = getr regs r).
  { intros r H1 H2. pose proof (HPR _ H1) as Hp. rewrite !Z_to_bv_bv_unsigned in Hp. rewrite Hp. exact (KR r H2). }
  assert (H144 : sv8 W' mem' (lf_F cx + 144) (c_n cx - rm_k' cx m)).
  { apply (cn_sv8_kept W W' mem mem'); [|exact R144]. intros x Hx. apply KC; [lia | left; lia]. }
  assert (H192 : sv8 W' mem' (lf_F cx + 192) (rm_A1 m h1 + cc)).
  { apply (cn_sv8_kept W W' mem mem'); [|exact R192]. intros x Hx. apply KC; [lia | left; lia]. }
  assert (HR' : (lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc) (frame_addr ly' 1 fpos) regs' W' mem').
  { rewrite KE. unfold lregs_rmc, rm_regs_base.
    repeat split;
      first [ match goal with |- getr regs' ?r = _ => rewrite (KRR r ltac:(cn_cs) ltac:(unfold rsr_kept; cn_in)) end;
              assumption
            | exact H144 | exact H192 | lia ]. }
  exists regs', mem', md', ly', S', (k + kk), fpos.
  split.
  { unfold cfg_at. rewrite Q1. change (w64 (fr_B0 + A_rm_end)) with (Z_to_bv 64 (BASE + A_rm_end)). reflexivity. }
  split; [exact ((cn_jt XM_LIB XN_LIB RLO HAP) W W' mem mem' HRV HRV' HROM)|].
  split; [exact HJ'|].
  split; [exact HFR'|].
  split; [exact HFL'|].
  split; [exact HMOD'|].
  split; [exact HIN'|].
  split; [exact HRV'|].
  split; [exact HSEP'|].
  split; [exact HQ'|].
  split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
  exact HR'.
Qed.
(* ---- (9)'s two model steps: the operation's end, after the five calls ---- *)
(* RI_rm_step: op 4 removed relay entry j0 and closed slot si.  The plain op-4 step proves the same fact of its
   invariant: Prog/SlotPass4.v r_fin :3033-3132 rebuilds relay_at (Prog/SlotInv.v:265-276) at es' = remove_at q es and
   hj' = remove_at q hj (REL4 :3054-3066: the entry and its pair gone, slot i zero by fin_zero) and the RI of the new
   view (RI7 / p4_lv4 :3113-3131), both entry-at-eof cases (r_h1 :1789).  Mirrors _drain.v RI_drain_step :618 (out2
   free, as out' there).  errno floats (ev5, the value source_reset left): the plain invariant holds errno's value
   only existentially (Prog/SlotInv.v:238), and RI_drain_step's ev' is universal too.  No call: the strict walk over
   the R journal, lifted by SRr_SRrG, to cut_x's INV_K_xR *)
Let RF_RUNTO := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Lemma rm_fin_xR : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 W c,
  lf_base0 cx -> RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  RCUT_x cx (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2)
    ((rm_Qc h j0) cx t m (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2)
      ((rm_rr_cost MT) m h + (rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (rm_cshe_cost MT) H' +
       sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))))
    ((lregs_rmc B) cx t m si j0 (rm_A1 m h1 + cc)) A_rm_end W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 W c HB HRI HAT HRR HCN HCS
    (regs & mem & md & ly3 & S3 & k & fpos & -> & HROM & HJ & HFR & HFL & HMOD & HIN & HRV & HSEP & HQ & HNP & HR).
  apply (SRr_SRrG segs R WLE_R).
  destruct HQ as (ly0 & S0 & HLS0 & HMO & (HP1 & HP3 & HP4) & HFR0 & _ & HR3).
  pose proof HR3 as (_ & _ & _ & HU & _).
  pose proof HAT as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27 & Ht) &
    _ & _ & R22 & SVN & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof HAT as (Hk0 & _).
  assert (Hk' : 0 <= rm_k' cx m <= c_n cx)
    by (unfold rm_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (rf_entry W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_rm_end)) with (Z_to_bv 64 (BASE + A_rm_end)).
  (* j 0x8448c ; li s4,10 *)
  paj_run_to_tok_x RF_RUNTO HS HJ SHOK rf_Bspan AF_LLVM_latch.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?Ev ?rs ?m0 ?m1 =>
    pose proof (frame_of_read_only Ev rs m0 m1 ltac:(vm_compute; reflexivity) HF) as Em end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ RF_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (20%bv : bv 5) Q20.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, [], k, (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2), fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
  split; [exact (LS_rm_step cx t m ly0 S0 ly3 S3 si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5
                   HLS0 HU HMO HRI HAT HRR HCN HCS (rm_fr_all B _ _ _ _ _ _ _ HFR0) HP1
                   (proj1 (Forall_forall _ _) HP3 _ (nth_In _ relay_remove_b_c.no_entry Hj0)) (HP4 si h Hh) Ht)|].
  split; [exact HNP|].
  split; [exact (RI_rm_step cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5
                   HRI HAT HRR HCN HCS)|].
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
  cbn [lm_k rm_mk].
  split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
  split; [exact SVN|]. exact Hk'.
Qed.

(* ------------------------------------------------------------------ the arm at R: cut_x's ARM_remove_R (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v
   Section wR), the nine segments composed by SRrG_bind (R_trans) *)
Theorem lf_arm_remove_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 4 cx Hp t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  (* the entry's ghost list is [] (HP0 on the pre's ARx) *)
  assert (EHp : Hp = []).
  { pose proof HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. destruct HPRE as ((HAR0 & _) & _).
    exact (HP0 _ _ _ _ _ _ HAR0). }
  subst Hp.
  eapply (SRrG_bind segs R R_trans); [exact (rm_entry_xR cx t W c HB HA)|].
  intros W1 c1 _ (m & si & h & j0 & HRI & HAT & HL).
  eapply (SRrG_bind segs R R_trans); [exact (rm_scan_xR cx t m si h j0 W1 c1 HB HRI HAT HL)|].
  intros W2 c2 _ HR2.
  eapply (SRrG_bind segs R R_trans); [exact (rm_rr_xR cx t m si h j0 W2 c2 HB HRI HAT HR2)|].
  intros W3 c3 _ (e1 & h1 & ev & LB & cc2 & O2 & cap2 & out2 & HRR & HR3).
  eapply (SRrG_bind segs R R_trans);
    [exact (rm_cnlr_xR cx t m si h j0 e1 h1 ev LB cc2 O2 cap2 out2 W3 c3 HB HRI HAT HRR HR3)|].
  intros W4 c4 _ (ev1 & HR4).
  eapply (SRrG_bind segs R R_trans);
    [exact (rm_cnl_xR cx t m si h j0 e1 h1 ev LB cc2 O2 cap2 out2 ev1 W4 c4 HB HRI HAT HRR HR4)|].
  intros W5 c5 _ (E' & H' & ev2 & HCN & HR5).
  eapply (SRrG_bind segs R R_trans);
    [exact (rm_cshe_xR cx t m si h j0 e1 h1 ev LB cc2 O2 cap2 out2 E' H' ev2 W5 c5 HB HRI HAT HRR HCN HR5)|].
  intros W6 c6 _ (H'' & ds & cc & ev3 & HCS & HR6).
  eapply (SRrG_bind segs R R_trans);
    [exact (rm_csd_xR cx t m si h j0 e1 h1 ev LB cc2 O2 cap2 out2 E' H' H'' ds cc ev3 W6 c6
              HB HRI HAT HRR HCN HCS HR6)|].
  intros W7 c7 _ (ev4 & HR7).
  eapply (SRrG_bind segs R R_trans);
    [exact (rm_sr_xR cx t m si h j0 e1 h1 ev LB cc2 O2 cap2 out2 E' H' H'' ds cc ev4 W7 c7
              HB HRI HAT HRR HCN HCS HR7)|].
  intros W8 c8 _ (ev5 & HR8).
  eapply (SRrG_bind segs R R_trans);
    [exact (rm_fin_xR cx t m si h j0 e1 h1 ev LB cc2 O2 cap2 out2 E' H' H'' ds cc ev5 W8 c8 HB HRI HAT HRR HCN HCS HR8)|].
  intros W9 c9 _ HK. exact (SRrG_ret segs R R_refl W9 c9 _ HK).
Qed.
(* THE R CHECK: lf_arm_remove_xR in the ARM_remove_R slot of cut_x's lf_contract_of_segments_xR, a term that
   type-checks only if its type is that Section hypothesis *)
Definition lf_arm_remove_xR_slot :=
  fun SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R ARM_gone_R ARM_eintr_R ARM_event_R
      ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R =>
  @lf_contract_of_segments_xR fx rc B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST
    ARx hl LAWS HG LSx RINV R R_refl R_trans WLE_R SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R
    lf_arm_remove_xR ARM_gone_R ARM_eintr_R ARM_event_R ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R.
End wR.

(* ------------------------------------------------------------------ the arm: cut_x's ARM_remove (cut_x.v:306), the R
   arm at R := wle (route R's one walk text): its three laws hold for wle, and each strict callee text gives its R text
   at wle (X_xR_of_x at WLE_R := id) *)
Theorem lf_arm_remove_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 4 cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  assert (L1 : forall W0, @wle segs W0 W0) by (intros ?; apply wle_refl).
  assert (L2 : forall W1 W2 W3, @wle segs W1 W2 -> @wle segs W2 W3 -> @wle segs W1 W3)
    by (intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2]).
  assert (L3 : forall W0 W1, @wle segs W0 W1 -> @wle segs W0 W1) by (intros ? ? Hw; exact Hw).
  assert (RR0 : rr_spec_xR B PST ARx (@wle segs) MT RP MMAX fr_RG CTX_AFREE (BASE + AF_fr_relay_remove))
    by (apply rr_spec_xR_of_x; [exact L3 | exact RR]).
  assert (CNL0 : forall G, gx_ok segs B G -> gx_rt B G ->
      cnl_spec_xR B PST ARx (@wle segs) MT RP G MMAX (BASE + AF_fr_check_no_loss))
    by (intros G H1 H2; apply cnl_spec_xR_of_x; [exact L3 | exact (CNL G H1 H2)]).
  assert (CSHE0 : forall G, gx_ok segs B G ->
      cshe_spec_xR B PST ARx (@wle segs) MT RP G (BASE + AF_fr_check_shape_ends))
    by (intros G H1; apply cshe_spec_xR_of_x; [exact L3 | exact (CSHE G H1)]).
  assert (SR0 : sr_spec_g_xR B PST ARx (@wle segs) MT RP (BASE + AF_fr_source_reset))
    by (apply sr_spec_g_xR_of_x; [exact L3 | exact SR]).
  exact (lf_arm_remove_xR (@wle segs) L1 L2 L3 RR0 CNL0 CSHE0 SR0 cx Hp t W c HB HA).
Qed.

(* ------------------------------------------------------------------ THE CHECK, at cut_x's Section w variables: the
   ARM_remove hypothesis (cut_x.v:306), restated and closed by `exact`, and the theorem in the ARM_remove slot of
   cut_x's composition lf_contract_of_segments_x (cut_x.v:371-373), a term that type-checks only if lf_arm_remove_x's
   type is convertible to that Section hypothesis *)
Lemma lf_arm_remove_x_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 4 cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof. exact lf_arm_remove_x. Qed.
Definition lf_arm_remove_x_slot :=
  fun SEG_PRO SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_gone ARM_eintr ARM_event ARM_sendmax ARM_default
      SEG_LATCH SEG_EXIT =>
  @lf_contract_of_segments_x fx rc B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST
    ARx hl LAWS HG LSx RINV SEG_PRO SEG_HEAD ARM_add ARM_write ARM_drain ARM_close lf_arm_remove_x ARM_gone ARM_eintr
    ARM_event ARM_sendmax ARM_default SEG_LATCH SEG_EXIT.
End wrx.
