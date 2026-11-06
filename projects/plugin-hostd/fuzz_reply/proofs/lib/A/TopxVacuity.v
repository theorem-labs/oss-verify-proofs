(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput - the
   jump table's arm 2 (op_drain, fuzz_reply.c:596-609), from the arm's entry 0x84520 to the latch 0x84490, in the
   form of lib/A/W_LLVMFuzzerTestOneInput_cut.v's worked dispatch lf_seg_jt and of the loop walk
   lib/A/W_check_bounded.v (cb_loopX: a loop from a fresh symbolic state at its head, by induction on the trips
   left, spliced back with jafter_stretch_pi).
   The arm: relay_source(s->fd) scans g_src[0 .. g_nsrc) for the entry whose fd is the picked source's
   (0x84520-0x84584); with no entry, or with r->eof set, the operation is a no-op (0x846c8 / 0x84a40, both joining
   at 0x84a80); otherwise pthread_mutex_lock(&g_lock), drain(r), pthread_mutex_unlock(&g_lock),
   check_no_loss_read(s), check_no_loss(s, &at), check_shape_done(at) (0x84a44-0x84a7c), then the same join.
   The out-parameter `at` is the frame cell F+192: check_no_loss runs under its journal at XO = 208 with
   OUT = [(F+192, F+200)] (W_journal.v; the cell is inside the caller's own window, and ajournal_gx_sub carries it).
   The eof = 0 path is cut at the six return points into stages dc_stA .. dc_stF over dc_at (composed in dc_calls).
   What this file takes, and from whom (all Section hypotheses, none proved here):
     LAWS / HG / RINV / LS / the contract parameters - _cut's Section w, verbatim; GWR / ERR - _cut's glob_wr_law
       / errno_law, verbatim;
     TL : PALib B - the allocator instance (W_kit.v);
     DRAIN - W7's dr_spec B MT MMAX fr_RG, verbatim (lib/A/W_contract.v);
     ALOCK / AUNLOCK - W6's alock_realizes / aunlock_realizes (lib/A/W_sites.v), proved by R5
       (rt_pthread_mutex_lock / rt_pthread_mutex_unlock, a working branch);
     CSD - check_shape_done, proved (W_check_shape_done.v pb_check_shape_done);
     CNLR - W_contract.v's cnlr_spec, proved (W_check_no_loss_read.v pb_check_no_loss_read);
     CNL - check_no_loss, W3's cnl_spec as lib/A/W_contract.v Section w3n publishes it (the readable-stack premise
       LAST, passed from the cut's STKR by dr_stkr), at every G with gx_ok / gx_rt, taken at the slot's two list headers;
     the G-coverage and image facts (HGs, HG_DR, HGlock, HG_GK, HERR_HI, DR_ROM_OUT, HZS, HAP), and
     the model obligations RI_* / LS_* (pure, over lmod and the plain records). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_drain.v, with its module paths and module names changed; 137 of its 198 lines of code are new or changed and 5326 lines of the source are left out. *)
(* REGRESSION CHECKS ABOUT RETIRED TEXTS.  The rules below are byte copies of top_x's PRE-ROOM texts (integ b4343cabfa9 /
   riplug 5dfdaedea77; this file's commits 2a368424fed and 8b3470dfded), NOT of today's top_x.  The room round restated
   LS_event_step, LS_cnl_pre, LS_drain_step and LS_rm_cnl_pre (they now tie the result state to the start state).
   Checked 2026-10-30 08:49Z (a Theorem Labs lane's settling check): with the six rules re-copied byte for byte from top_x at
   03b02fb0cf3, each of the four proofs below FAILS, at its use of the restated rule (LS_event_step, LS_cnl_pre,
   LS_rm_cnl_pre, LS_drain_step).  So nothing here says today's texts are false.  The file stays so that a revert to
   the old texts is caught: at the instance's meter MT := ameter_triv (Reusable/YCbp.v: mo_ok / mo_le are True), the
   OLD rules are inconsistent with two consecutive event ops (or a drain / remove leaving an expected record, or a
   drain then an event) from any state where LSx / RINV hold, because a result state only mo_le bounds may have more
   than LIVE_MAX live bytes (vac_state).
   proves no function (kind: model and invariant lemmas). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_addI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x W_contract_x W_check_bounded W_palib_fr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_top.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* the start-up table's facts (ts_owned, ts_errno, Tfib_owned_static), as addI uses them *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m.
(* the AR arm files for the model functions the RI_* / LS_* rules name (sm_*, ad_*, wr_*, WR_MMAX); Require Import
   is not transitive through _top.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_write.
(* SEG_PRO: the AR file for pro_m and its model texts, and SmallX's conversion, with the frame kit its facts name
   (W_frame's PALibF, W_frame_x's astack_malloc_pres_x / frame_flag_lawP_x, YGcallx's laws, YG01cf / YG05cf's Wf_cf and
   stack_malloc progress); imported BEFORE W_op_add so that W_op_add's oa_first / oa_cost / oa_spec_g_x (the names
   below) are not shadowed by _pro.v's / _pro_x.v's copies *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_latch_x W_LLVMFuzzerTestOneInput_small_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_op_add W_list_push ACk0 W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write_x.
(* ARM_event: the AR file for et_GL / et_GRE / ev_* (Require Import is not transitive), and SmallX's conversion *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_event W_LLVMFuzzerTestOneInput_event_x.
(* SEG_HEAD: the AR file for hd_kb / hd_k', and HeadX's conversion *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x.
(* ARM_drain: Prog's CheckRep (texts / count_begin / set_exp_held, which its rules name), the AR file for the drain
   model (dr_at_op / dr_pick / dr_step / dr_cost ..., DR_GK), and AddX's conversion; last, and they define none of
   the names above (checked: their only clashes are Local notations) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_drain W_LLVMFuzzerTestOneInput_drain_x.
(* SEG_EXIT: the AR file (its model functions lx_* / xr_GM, cited qualified below), LatchX's conversion, the kit's
   YE01_x.v that conversion cites, _Gx.v's XR_HGM witness, AD1u.v's tfib_AIL and YG0tcf.v's stack_free law; Require
   without Import, so none of their names shadows a name the text above uses *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_exit W_LLVMFuzzerTestOneInput_exit_x YE01_x W_LLVMFuzzerTestOneInput_Gx AD1u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
(* ARM_remove: the AR file (its model functions rm_*, cited qualified below), WriteX's conversion, the .str.2 shadow
   lemma over ARx and W6's rg_place assembly; Require without Import, as SEG_EXIT's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_shadow_pin_x W_rg_place.
(* ARM_gone: the AR files (gone_base's model texts GN_*, cited qualified below) and SmallX's conversion; Require
   without Import, as SEG_EXIT's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_sites W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone W_LLVMFuzzerTestOneInput_gone_x.
(* C1 (a Theorem Labs lane's 922a710cda0; relay_event re-proved by AddX's C3 88557c15170): relay_add's, relay_event's and
   relay_finish's _x proofs, which build RA_x / RE_x / RF_x below; Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_relay_add W_relay_event W_relay_finish_h.
(* W3's check_shape_done and check_no_loss_read _x walks, which build CSD_x / CNLR_x below; Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_check_shape_done W_check_no_loss_read.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* the ASan image's sink instance, the one cut_x's journals and the arm files name (write_x.v:60) *)
#[local] Existing Instance AE2k.tfib_sink_head.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_top_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
Local Notation ARX := W_LLVMFuzzerTestOneInput_top_x.ARX.

(* a state whose live bytes are N: init_state with one allocated chunk of N bytes *)
Definition vac_state (N : Z) : astate :=
  let s := init_state in
  mkA (st_regions s) (st_cache_inited s) (st_cache s) [mkChunk PNull N CAllocated] (st_secs s) (st_sec_arr s)
    (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Lemma vac_state_bytes : forall N, blocks_bytes (vac_state N) = N.
Proof. intros N. unfold blocks_bytes, vac_state. cbn. lia. Qed.

Section v.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation MT := ameter_triv.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Hypothesis RI_event_step : forall cx t m e v out',
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  RINV cx (t + 1) (ev_step cx m e v out').
Hypothesis LS_event_malloc : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e)).
Hypothesis LS_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out',
  LSx cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  LSx cx (t + 1) (ev_step cx m e v out') ly3 S3.

Theorem topx_two_events_false : forall cx t m ly S e v out' e',
  LSx cx t m ly S -> RINV cx t m ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  ev_evt cx (ev_step cx m e v out') e' ->
  False.
Proof.
  intros cx t m ly S e v out' e' HL HR Hk HO Hb He Hv He'.
  set (S3 := vac_state (LIVE_MAX + 1 + Z.abs (re_len e'))).
  assert (HL3 : LSx cx (t + 1) (ev_step cx m e v out') ly S3)
    by exact (LS_event_step cx t m ly S S S S3 ly e v out' HL He I I I).
  assert (HR3 : RINV cx (t + 1) (ev_step cx m e v out'))
    by exact (RI_event_step cx t m e v out' HR Hk HO Hb He Hv).
  destruct (LS_event_malloc cx (t + 1) (ev_step cx m e v out') ly S3 e' HL3 HR3 He') as (_ & Hbb & _).
  subst S3. rewrite vac_state_bytes in Hbb. lia.
Qed.
(* ---- the same collapse for three more of top_x's rules (a Theorem Labs lane's constructions, 03:42Z), each a rule whose
   result state only mo_le binds ---- *)
Hypothesis LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'',
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
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h''))
    (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Hypothesis LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Hypothesis LS_rm_cnl_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).

(* cnl_room of a state with more than LIVE_MAX live bytes fails once the record list is non-empty *)
Lemma vac_cnl_room_big : forall MMAX T cap r rs,
  ~ cnl_room MMAX (blocks_bytes (vac_state (LIVE_MAX + 1 +
      Z.abs (if Z.of_nat (length T) =? cap then AREC * grow_cap (Z.of_nat (length T)) cap else 0))))
    T cap (r :: rs).
Proof.
  intros MMAX T cap r rs (_ & Hb & _). rewrite vac_state_bytes in Hb.
  pose proof (Zle_0_nat (length (snd r))) as L.
  destruct (Z.of_nat (length T) =? cap); lia.
Qed.

(* (A) one drain op whose source yields a line, from a state where LSx / RINV hold *)
Theorem topx_cnl_pre_false : forall cx t m ly S si h j h'',
  LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  hl_recs (hs_expected h'') <> [] ->
  False.
Proof.
  intros cx t m ly S si h j h'' HL HR Hp Hj Hfd Heof E1 E2 E3 Hne.
  set (T := texts (hs_held h'')). set (cap := hl_cap (hs_held h'')).
  set (S' := vac_state (LIVE_MAX + 1 +
      Z.abs (if Z.of_nat (length T) =? cap then AREC * grow_cap (Z.of_nat (length T)) cap else 0))).
  destruct (LS_cnl_pre cx t m ly S ly S' si h j h'' HL HR Hp Hj Hfd Heof I E1 E2 E3) as (_ & _ & _ & Hc & _).
  destruct (hl_recs (hs_expected h'')) as [|r rs]; [exact (Hne eq_refl)|].
  exact (vac_cnl_room_big _ T cap r rs Hc).
Qed.

(* (B) one remove op whose rm_rr_ok leaves an expected record *)
Theorem topx_rm_cnl_pre_false : forall cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  hl_recs (hs_expected h1) <> [] ->
  False.
Proof.
  intros cx t m ly0 S0 si h j0 e1 h1 ev LB c2 O2 cap2 HL HR Ha Hr Hne.
  set (T := texts (hs_held h1)). set (cap := hl_cap (hs_held h1)).
  set (S := vac_state (LIVE_MAX + 1 +
      Z.abs (if Z.of_nat (length T) =? cap then AREC * grow_cap (Z.of_nat (length T)) cap else 0))).
  destruct (LS_rm_cnl_pre cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 HL HR Ha Hr I) as (Hc & _).
  destruct (hl_recs (hs_expected h1)) as [|r rs]; [exact (Hne eq_refl)|].
  exact (vac_cnl_room_big _ T cap r rs Hc).
Qed.

(* (C) a drain step, then an event op: LS_drain_step's result state is free, LS_event_malloc bounds it *)
Theorem topx_drain_then_event_false : forall cx t m ly S si h j h'' e' c' O' cap' out' (E H : hlist) e,
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ->
  ev_evt cx (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') e ->
  False.
Proof.
  intros cx t m ly S si h j h'' e' c' O' cap' out' E H e HL Hp Hj HR He.
  set (S' := vac_state (LIVE_MAX + 1 + Z.abs (re_len e))).
  pose proof (LS_drain_step cx t m ly S S ly S' si h j h'' e' c' O' cap' out' E H HL Hp Hj I I) as HL'.
  destruct (LS_event_malloc cx (t + 1) _ ly S' e HL' HR He) as (_ & Hbb & _).
  subst S'. rewrite vac_state_bytes in Hbb. lia.
Qed.
End v.
