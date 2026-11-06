(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain (op 2) of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput over the
   GENERIC allocator relation ARx: the ARx conversion of lib/A/W_LLVMFuzzerTestOneInput_drain.v's lf_arm_drain.
   The AR proof is a Theorem Labs lane's: a working branch 129f255c729 (dr_found_join / lf_arm_drain Qed on W8
   base ec4dd616ed1: fresh rc=0 wall 604, Print Assumptions 13 Prim* + funext), adapted to the current cut on
   a working branch cdc87da7be0 (b5 w8c rc=0).  lf_arm_drain_x's statement is the text of the
   Section hypothesis ARM_drain of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section w (:349), checked at the end
   (lf_arm_drain_x_check).
   THE ROOM ROUND (a working branch, on meet 393c0b2cb2a): the cut's invariants take NP
   (lcut_x's NP S after LSx; DLK carries it); DRAIN / CNL take the room record RP (RP_NP ties its rp_RM to NP) and
   their count premises cnt_ok_pk RP (dr_pk ..) / (cnl_pk ..), the first from LS_cnt at the cut, the second at the
   state the drain leaves through the two pure model rules DR_CNT_grow / DR_CNT_cnl; LS_drain_pre's conjunct 5 is
   the peak form (with the three premises s5-r1d's rows take); LS_cnl_pre / LS_drain_step are a Theorem Labs lane's
   TX_LS_cnl_pre / TX_LS_drain_step (d0d75bf92db), whose premises dc_stB (dcB_out) and dc_stE export.
   The method (W8Entry-2's add_x method): this file Requires _drain.v and CITES every item of it that reads no AR
   and no Section variable (the model notions, the symbolic states, the pure list / byte lemmas); every item that
   reads a Section variable but no AR is restated VERBATIM (same name, same proof, up to cut_x's LS -> LSx and the
   local names Hp / Hp1 / Hp2 / HP0 -> Hpo / Hp1o / Hp2o / HPm0, which the ghost lists and HP0 take); every
   AR-reading item is CONVERTED, keeping its name: AR -> ARx with the ghost head list (Hpe at the entry, Hp / Hp2 /
   Hp3 / Hpc after the state they belong to), al_* -> alx_*, the journal lemmas -> W_journal_x / YCbqG / W_frame_x's
   _x twins (the journal's image clause takes `~ Exists (in_zr a) PST`, from HPST), paj_run(_to)_tok ->
   paj_run(_to)_tok_x, the callee specs -> their kit _x forms (W_contract_x / W_sites_x), aj_gx_entry_at ->
   aj_gx_entry_at_x.  The arm's states DST / DLK / dc_at / dcB_post take the entry's Hpe beside cx and the state's
   Hp beside S; dr_callZ's post predicate K takes the callee's Hp2 beside S2.
   Section hypotheses beyond cut_x's Section w header (B .. RINV, verbatim):
     MMAX / TL / the G-coverage and image facts (HGs, HG_DR, HGlock, HG_GK, HERR_HI, DR_ROM_OUT, GWR, HZS, HAP) /
       RI_* / LS_* (LS is cut_x's LSx) - _drain.v's, verbatim;
     DRAIN / CSD / CNLR / CNL - dr_spec_x / csd_spec_x / cnlr_spec_x / cnl_spec_x at the walk's PST / ARx;
     ALOCK / AUNLOCK - alock_realizes_x / aunlock_realizes_x;  ERR - cut_x's errno_law_x;
     HPST - the image is off PST (W_op_add.v Section x's text; trivial at the instance's PST := []);
     BLKR - a live block's request is in [0, 2 ^ 30) (AR's al_blocks carries 0 <= n < MALLOC_MAX = 2 ^ 28, which
       AR_laws_x's alx_blocks does not; the cf instance has 0 <= n < cf_malloc_max as AR_blocks_law_cf's last
       conjunct and cf_malloc_max + 15 <= 2 ^ 30 as YG08cf.v cf_malloc_max_bound).
   ARM_drain takes no allocator rule directly, so it takes no caller-context table.
   ROUTE R (Section drxR at the end; a Theorem Labs lane's segment-twin round, 2026-10-31): lf_arm_drain_xR is the R twin of
   lf_arm_drain_x, stated as cut_x's Section wR hypothesis ARM_drain_R (checked: lf_arm_drain_xR_check).  It takes the
   strict lemma's Section hypotheses without DRAIN and CNL and, after them, R R_refl R_trans WLE_R, then DRAIN_R
   (W_contract_xR.v's dr_spec_xR: drain reallocs and frees, so it may re-hide) and CNL_R (W_contract_xR_g6.v's
   cnl_spec_xR: check_no_loss frees).  The leaves lock / unlock / check_no_loss_read / check_shape_done free nothing and
   keep their strict specs, lifted inside the walk (W_sites_x.v aj_gx_entry_at_xR; SRr_SRrG with WLE_R and YCbqG.v
   ajournal_xR_mono).  Each item of the strict walk that reads the cut's or a callee's journal has an R twin, its name
   suffixed R, whose proof is the strict one over the R twins of the journal lemmas (W_journal_x / YCbqG / W_frame_x /
   W_sites_x / W_kit's paj_branch_xR); the call-free segments (dr_entryR, dr_scanR, dr_nf_joinR, dr_join_latchR) conclude
   strict SRr over the R journal (paj_run_x_xR) and are lifted by SRr_SRrG; the stages with a call conclude SRrG segs R
   (paj_run_x_xG runs, SRrG_bind / SRrG_mono).  The strict lemmas and their proofs are unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_drain_x.v, with its module paths and module names changed; 156 of its 217 lines of code are new or changed and 6985 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3cArms.v (sha256
   e836fd1dfc9c; internal record) at d9e8f914caaf (the same blob as at 1b1e21bdbd40), for
   row G-BLS3-port: A's lemmas under A's names and statements over lib/B's records, with these swaps:
   - the Require header is lib/B/ReplyB3LS3c.v's plus lib/B/ReplyB3LS3Arms.v's (lib/A ReplyLSArms / ReplyRINV /
     ReplyLSDrainPre / ReplyLS3Arms / ReplyLSCntL / ReplyLS3c -> lib/B ReplyLSBArms / ReplyRINVB / ReplyLSBDrainPre /
     ReplyB3LS3Arms / ReplyB3LSCntL / ReplyB3LS3c; A's _drain arm model -> lib/B W_LLVMFuzzerTestOneInput_drain_defs;
     A's ReplyLSDrain3 / ReplyLSRemove3 / ReplyLSEvent3 facts are the ones ReplyB3LS3Arms.v ports under A's names);
   - fr_LS3c B -> fr_LS3c B CALL_ROOM_B: the Section takes the Variable CALL_ROOM_B after B, as ReplyB3LS3c.v and
     ReplyB3LS3Arms.v Section arms3 do; fr_CNT reads no room (fr_CNT_same_rest B);
   - rm_rr_cost m h -> rm_rr_cost MT m h (lib/B/ReplyLSBArms.v's copy takes the meter first);
   - KF-COUNT (the meter pattern of a Theorem Labs lane, A #6): A's MT := ameter_triv -> Section c3arms's Context
     {MT : ameter_ops}, implicit (read off the rules' mo_le arguments, which no proof reads); rm_cnl_cost /
     rm_cshe_cost are lib/B/W_LLVMFuzzerTestOneInput_remove.v's (pinned below), which take the meter first;
   - A's ev3_model_blks is lib/B/ReplyLSBArms.v bt_model_blks (bt_pfx for ev3_pfx);
   - fr_LS3c_sat: at the B instance CALL_ROOM_B := YCfn_cf.CALL_ROOM_B (2 ^ 33, A's ACfn_cf.CALL_ROOM), the proof
     lib/B/ReplyB3LS3.v fr_LS3_sat's.
   No lemma here reads CALL_ROOM_B's value but fr_LS3c_sat. *)
(* The count half of LS v3, part 3b: fr_LS3c (ReplyLS3c.v) at the arm rules whose v3 text frames the whole model
   (input ++ model ++ rest): remove's step.  Its frame keeps the rest, so fr_CNT carries over (fr_CNT_same_rest);
   npend only falls (the slot is closed).  The drain and event steps frame pieces (entry, source, out buffer) and need
   the model permutation re-derived, as fr_LS3c_write_push does (fr_LS3c_event_step_p, fr_LS3c_drain_step_p). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv
  SlotDrain3Aux SlotPass2Aux relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3Base ReplyB3LS3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3Arms ReplyB3LSCntL ReplyB3LS3c.
Import ListNotations.
(* the remove arm notions lib/B/ReplyLSBArms.v copied are lib/B's arm files' (s5-r1d's cutover; ev_* stay
   ReplyLSBArms's until an internal work row, a Theorem Labs lane 08:09Z), pinned here *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Notation rm_rr_cost := W_LLVMFuzzerTestOneInput_remove.rm_rr_cost.
Local Notation rm_cnl_cost := W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost.
Local Notation rm_cshe_cost := W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

Section c3arms.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.
(* the meter (KF-COUNT): a Variable, implicit, read off the rules' mo_le arguments *)
Context {MT : ameter_ops}.

(* A :61 *)
Lemma fr_LS3c_rm_step_p : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_LS3c B CALL_ROOM_B cx t m ly0 S0 ->
  mo_le MT S0 S (rm_rr_cost MT m h + rm_cnl_cost MT (hs_expected h1) (hs_held h1) + rm_cshe_cost MT H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  fr_LS3c B CALL_ROOM_B cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 (H1 & H2) Hmo HRI Hat Hrr Hcn
    Hcs Hfr Hpos H14 Hoffc.
  split; [exact (fr_LS3_rm_step_p B CALL_ROOM_B cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H''
    ds cc ev5 H1 Hmo HRI Hat Hrr Hcn Hcs Hfr Hpos H14 Hoffc)|].
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & _).
  destruct H1 as (rest & e0 & HPm & _).
  apply (fr_CNT_same_rest B cx t (t + 1) m _ ly0 S0 ly S rest HPm (Hfr rest HPm)); [| exact H2].
  pose proof (nth_some_error _ _ _ Hh) as Hi.
  pose proof (rm3_set_zsum _ slot_npend si None (Some h) (lm_hs m) Hi) as Z4.
  assert (N4 : slot_npend None = 0) by reflexivity. pose proof (slot_npend_nonneg (Some h)) as P4.
  unfold npend. cbn [rm_mk lm_hs]. lia.
Qed.
(* the event's step: the event buffer is malloc'd and freed, the out buffer may move; the model's other blocks stay
   (A :91) *)
Lemma fr_LS3c_event_step_p : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_LS3c B CALL_ROOM_B cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q (H1 & H2) HE M1 M2 M3 Hk HO Hc0 Hm HRR Hf.
  split; [exact (fr_LS3_event_step_p B CALL_ROOM_B cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H1 HE M1 M2 M3 Hk
    HO Hc0 Hm HRR Hf)|].
  destruct HRR as (restR & HR1 & HR2). destruct Hf as (l1 & l2 & Hf2 & Hf3).
  destruct H1 as (rest & e0 & HP & _).
  set (cap' := sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in *.
  assert (EM' : model_blks (ev_step cx m e v out') = bt_pfx m ++ aout_blks cap' out')
    by (rewrite bt_model_blks; reflexivity).
  assert (HP' : Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks (ev_step cx m e v out') ++ rest)).
  { rewrite Hf3, EM'. rewrite Hf2 in HR2. rewrite Hm in HR1. rewrite bt_model_blks in HP.
    clear - HP HR1 HR2. ls3_perm. }
  apply (fr_CNT_same_rest B cx t (t + 1) m _ ly S ly3 S3 rest HP HP'); [| exact H2].
  assert (En : npend (ev_step cx m e v out') = npend m) by reflexivity. lia.
Qed.

(* A :118 *)
Lemma fr_LS3c_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3c B CALL_ROOM_B cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (* dr_post :949-950, :966 *)
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  (* the arm calls check_no_loss on the drained source's lists (drain.v:5472) and cnl_post :238-239 *)
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  (* v3: dr_at_op (Hatop), RINV (HRI), the pair's fd and eof (Hfdj, Hef0): drain.v:5413-5414 *)
  dr_at_op cx m -> fr_RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  (* v3: the entry's and the source's model clauses at the drain call (aentry_ok W_rep.v:126-141, asrc_at :91,
     :101-105, :111-112 with alist_at :81, aout_at :187-188) *)
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  (* v3: dr_post :943 *)
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  (* v3: dr_post :952 (aentry_ok e'), :957-959; :966, :967, :964; :954, :956, :966, :970, :972, :961; cnl_post *)
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  fr_LS3c B CALL_ROOM_B cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' (HLS & HCN) Hpick Hj M1 M2
    HPd Hpend HEq HHq Hcnl Hh'' Hat HRI Hfd Heof Hepre Hkh Hhpre Hhn Hcap0 Hcap' Hepost Hhpost Hdpost Hcpost.
  split; [exact (fr_LS3_drain_step_p B CALL_ROOM_B cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1
    E' H' HLS Hpick Hj M1 M2 HPd Hpend HEq HHq Hcnl Hh'' Hat HRI Hfd Heof Hepre Hkh Hhpre Hhn Hcap0 Hcap' Hepost
    Hhpost Hdpost Hcpost)|].
  destruct HPd as (rest_d & HPd1 & HPd2).
  subst E H h''.
  pose proof Hpick as (_ & Hsi & Hh).
  destruct HLS as (rest & e0 & HP & _).
  set (e := nth j (lm_es m) dr_e0) in *.
  set (h'' := set_exp_held h1 E' H') in *.
  set (m' := dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') in *.
  assert (Hej : nth_error (lm_es m) j = Some e) by (unfold e; apply nth_error_nth'; exact Hj).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  assert (LB : forall l, list_blks l = alist_blks l) by reflexivity.
  assert (Ha1 : asrc_blks h1 = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                               alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) by reflexivity.
  assert (Ha'' : asrc_blks h'' = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                                 alist_blks E' ++ alist_blks H') by reflexivity.
  pose proof (Hcnl ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++
                    aout_blks cap' out' ++ rest_d)) as HP3.
  rewrite !LB in HP3.
  assert (HP2' : Permutation (ablocks B ly1 S1) (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1) ++
                   (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++ aout_blks cap' out' ++
                   rest_d)).
  { rewrite Ha1 in HPd2. clear - HPd2. ls3_perm. }
  specialize (HP3 HP2'). clear HP2' Hcnl.
  pose proof (dr3_dset_perm aentry_blks j e' e (lm_es m) Hej) as PA.
  pose proof (dr3_dset_perm slot_blks si (Some h'') (Some h) (lm_hs m) Hhi) as PS.
  change (slot_blks (Some h'')) with (asrc_blks h'') in PS. change (slot_blks (Some h)) with (asrc_blks h) in PS.
  rewrite Ha'' in PS.
  assert (HP' : Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest)).
  { unfold model_blks in HP |- *. unfold m'. cbn [dr_step lm_G lm_es lm_hs lm_cap lm_out].
    change (list_blks E') with (alist_blks E') in HP3. change (list_blks H') with (alist_blks H') in HP3.
    clear - HP HPd1 HP3 PA PS. ls3_perm. }
  apply (fr_CNT_same_rest B cx t (t + 1) m m' ly S ly' S' rest HP HP'); [| exact HCN].
  unfold npend, m'. cbn [dr_step lm_hs].
  pose proof (dr3_dset_zsum slot_npend si (Some h'') (Some h) (lm_hs m) Hhi) as Z1.
  cbn [slot_npend] in Z1.
  assert (E0 : hl_n (hs_pending h'') = 0)
    by (unfold h''; cbn [set_exp_held hs_pending]; unfold hl_n; rewrite Hpend; reflexivity).
  assert (E1 : 0 <= hl_n (hs_pending h)) by (unfold hl_n; lia).
  lia.
Qed.

End c3arms.

(* ------------------------------------------------------------------ fr_LS3c is satisfiable at a concrete state *)
(* fr_LS3_sat's first-head state (ReplyB3LS3.v sat3: a 1-byte input block, the table, one open source's partial
   buffer; nothing else live): its rest is empty, so the rest's counts are 0, and no pending record is held at t = 0.
   B: at the B instance's call room CALL_ROOM_B := YCfn_cf.CALL_ROOM_B (A :199-228) *)
Section sat3c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma fr_LS3c_sat : exists (cx : lfcx (rc := rc)) t m ly S, fr_LS3c B YCfn_cf.CALL_ROOM_B cx t m ly S.
Proof.
  exists (ls3_cx B), 0, (ls3_m B), ls3_ly, ls3_S.
  assert (EA : ablocks B ls3_ly ls3_S = input_blks (ls3_cx B) ++ model_blks (ls3_m B) ++ []) by reflexivity.
  split.
  - exists [], 0.
    assert (Hbb : blocks_bytes ls3_S = 1 + ATABLE + APARTIAL) by (vm_compute; reflexivity).
    assert (Hin : bsum (input_blks (ls3_cx B)) = 1) by reflexivity.
    assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
    assert (HS : c_S (ls3_cx B) = ls3_S) by reflexivity.
    assert (Hn : c_n (ls3_cx B) = 1) by reflexivity.
    assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
    assert (HL : LIVE_MAX = 17179869184) by reflexivity.
    assert (En : npend (ls3_m B) = 0) by reflexivity.
    assert (Ek : kk (ls3_cx B) (ls3_m B) = 0) by reflexivity.
    assert (Eo : nopen (lm_hs (ls3_m B)) = 1) by reflexivity.
    assert (Ep : PHI3 (ls3_m B) = ATABLE + APARTIAL + E_ENT + K0) by reflexivity.
    rewrite EA, HS, Hbb, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
    split; [apply Permutation_refl|].
    unfold W_OPEN, MB_K, MB_C, ATABLE, APARTIAL, E_ENT, K0.
    refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
  - unfold fr_CNT. rewrite EA, !cnt_sec_app, cnt_sec_nil.
    assert (En : npend (ls3_m B) = 0) by reflexivity.
    split; [unfold SEC0; lia | split; [| rewrite En; lia]].
    intros c. rewrite !cnt_cls_app, cnt_cls_nil. unfold CLS0. lia.
Qed.
End sat3c.
