(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 949 of its 1032 lines of code are new or changed and 695 lines of the source are left out. *)
(* R-FORM PORT (WalkRtt102-2's wave 1 on 448ecd157e57; the R-form brief, CrtFit's WLE contract): every journal
   is ajournal_xR / ajournal_xwR at RZW := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (AJ / AJW below, Rtt102Cut.v's rtt_J),
   the step relation is YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf, and cmp_pn concludes SRr'. parse_noting's Step-2 text
   concludes SRr' with fpostFbm (= YCbqGwild.apost_base_xbFR at wle'), so pn_call_atF is aj_call_xbF_spR's proof at a
   concrete state at RZW (afn_pre_x_atR, ajournal_xw_subR); the materializations are ajournal_x_materializeR; the
   journal is read through ajxR_*. The text's new HULL BUDGET premise (PresetHullBudget.hull_budget S (parse_evs ..
   tb [])) is paid from the run position RT_K_R (pn_hull_budget: the cut's iface_room_pos count conjunct, the run's
   next events, at most 4 calls by Rtt102Cut.rtt_pre_os4, PresetSecTotalRun's prefix bounds) within cp's caps, the
   added Section hypothesis HI_hull (CrsSeg_W1 / X1 / Z's form; witness CrsSeg_W1.crs_W1_HI_hull at CfParams_preset).
   Its new post conjunct hull_used is not read. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): THE INNER SEGMENT PN of
   stretch CMP of round_trip_text's walk ON THE #102 PINS (lane CmpPN of RttCmp, WalkRtt102, the text owner): cmp_pn,
   from the +772 cut cmp_at_len to the +788 cut cmp_at_pn (both Rtt102CmpDefs.v), RE-FITTED TO THE BATCH KIT'S CUT 7cdbb61b5fa0
   (PRH_FnCheck blob c40cf3fdcd2a; GRANTED path only) on WalkRtt102b's shared layer 80a1d52c32c7. The pre-cut form was
   GREEN at 0d042ecb926 (pins102) on two premises that the
   cut retires (below).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma); the function-level lookup is the
   brief's (proof-index round_trip_text EXIT=0, no released ASan proof).
   THE CODE (A' +0x304 .. +0x314, A' capstone listing :195-198):
     +772 mv a1, a0 ; +776 mv a0, s6 ; +780 mv a2, s7 ; +784 jal parse_noting   (text, len, &back)   -> +788
   The three moves are Rtt102FR1KitA.v fr_addi, the jal fr_jal, the call pn_call_atF below (YCbqGwild.v aj_call_xbF_spR
   at RZW at a concrete state, as Rtt102FR1Kit.v fr_call_at transcribes YCbqGcall.v aj_call_x_sp: parse_noting reaches
   musl strtod, so the continuation runs at the callee's float state fx2, and its post is BUDGETED, so the caller's
   journal after it is at the callee's budget WS1), the callee's text the kit's tparse_noting_specX (the Section hypothesis
   TPN, category (b), at every float state); the call's chain is Rtt102FR1Kit.v rtt_chain_at, the journal is
   re-established across the four steps' materializations by ajournal_x_materializeR.
   THE TEXT AT EVERY FLOAT STATE: the call is made at the cut's fxc, and rtt_fx gives only frm_zero fxc and
   fregs_kept_x fx fxc, never fxc = fx (STATEMENT DEFECT CAUGHT earlier in this lane, the text owner's FPState trap: the
   text taken at the Section's fx cannot be applied at the jal). PROOF-CONTEXT FPState CHECK: two FPStates besides fx
   are in the proof's context, fxc (bound by the statement) and fx2 (destructed from the call's post); every predicate
   that takes an FPState is written through the notations PRE / RCARRY / AT_LEN / AT_PN / POST, which pass
   (fx := fx) by name, or takes fxc / fx2 as an explicit argument (mkst, TPN, rtt_fx, HK); fpre's frm_zero is ONE line
   (proj1 HFX, rtt_fx of rtt_carry).
   THE TEXT'S ROOM COUNTS (post-implication form): the peak secondary / class-24 counts along the reading's
   all-granted events from S's live set. pn_pkR_pos derives each from a model-run position whose next events are
   those events: P8's live-set premise in iface_room_pos (the model's live list plus at most 3) and
   PresetLiveSec.live_sec / live_c24 at every prefix of the run, PresetRun.pkR read prefix by prefix (pn_pkR_bound).
   THE OUTCOME, GRANTED: parse_noting's own OUTCOME clause (PRH_FnCheck.v:672-681) at the cut's position RT_K_R, the
   run's next events (rtt_pre's prh_run_at split by prh_run_at_app_iff, pn_run_parse), their consumer window
   (rtt_pre's prh_cons_from split by prh_cons_from_app_iff, pn_cons_parse) and g_fail_at = SIZE_MAX gives ran' = 0,
   the all-granted reading and the exact advance; its ran-out outcome is thereby refuted at the call (no refusal arm,
   and DeadK1's prh_refute_parse_noting is not cited). The run's sm is ReaderRes.jr_strtod, as the cut writes it.
   THE READ-BACK TREE'S FREE ORDER: the text's Some arm gives pj_free's order list against PresetReqAt.pj_frees
   jr_strtod ok tb at any depth bound >= depth t (rtt_pre: depth t <= 32 < DOC_D); the outcome ok of a granted reading
   gives the all-granted list (pn_pj_frees_agree: ok agrees with [] on the reading's calls, PjGrammar.agrees, so jfv /
   jfl read the same answers). That is cmp_out's every-depth conjunct (rtt_rb's at the batch kit's cut); at DOC_D
   PresetFreeFo.pj_frees_wdoc_t (under pj_wf jr_strtod t, rtt_pre's) gives fo t, cmp_out's DOC_D conjunct. The Some
   arm's K0-CAP pj_ncapR is cmp_out's last conjunct.
   THE TWO PRE-CUT PREMISES ARE GONE (cmp_pn takes none):
   - K0-SRC-CEIL: the cut's src_rd (PRH_Base.v:1660) asks `p + Z.of_nat (length l) <= YM05.alloc_ceiling`, no `+ 8`.
     At text = q it is the named assert HSRC_CEIL: the text block (q - cf_head, capw + cf_head) is live (prh_ledger's
     harness block), so AR_laws_x's alx_blocks (YCbqG.v:113-116, ARx_blocks_law: p + req_size n <= alloc_ceiling)
     gives q - cf_head + req_size (capw + cf_head) <= alloc_ceiling, req_size n >= n, and len < capw (rtt_at_cmp,
     Rtt102Cut.v:575).
   - K0-UNIV-END: the cut's tparse_noting_specX (PRH_FnCheck.v:596-730) takes no membership of the cursor end
     (PRH_FnCheck.v:615-616: prh_univ_closure's clause 4b holds the cursor traces at every word).
   THE WILD BUDGET: the text's entry room `wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S)` (= 2) is
   Rtt102Cut.rtt_wild_room at n = RTT_WK_T (rtt_at_cmp's last conjunct; 32 - 30 = 2) and YCbqGwild.wild_room_le; after
   the call Rtt102Cut.rtt_J_redepot gives rtt_J at the new state and rtt_wild_keep gives rtt_wild .. 32 (30 + 2), the
   carry's last conjunct (pn_carry_keep takes it).
   THE REQUEST BOUND AT THE CALL is the named assert HREQ_PN (g_most = ri_most D, the ledger field, and
   RQA_rtt t p <= ri_most D, rtt_pre's, which bounds RQ_pj_parse tb); the callee's peak equality reaches
   peak <= peak' only through pn_peak_le.
   THE CARRY ACROSS THE CALL: the callee's footprint [back, back + 56) lies INSIDE the fake frame F (back = F + 32), so
   Rtt102FR1Kit.v rtt_carry_keep (whose rtt_off forbids every byte of a live frame) does not apply. pn_carry_keep is
   rtt_carry_keep with the write set allowed in the RT_CID frame's back bytes and in no other frame byte (pn_off): the
   carried facts that read frame bytes are the flag pointer (F + 120, outside back) and doc's node and *copy (other
   frames of the entry, rtt_pre_facts).
   THE CLASS-24 COUNT AT +788 (cmp_at_pn): from the exact position after the reading
   (PresetRoomCounts.counts_of_room_pos_rl, the cut's home of the lemma PresetCfnA carried before).
   Numerals: 772 / 788 (DERIVED: byte offsets inside round_trip_text, Rtt102CmpDefs RT_C2 / RT_C3, with the slots
   + 4 between); 1 / 10 / 11 / 12 / 21 / 22 / 23 / 27 (WORD: register numbers); 32 (LENGTH: back at F + 32, RT_BACK;
   and PjGrammar.MAXD, the reader's depth bound), 56 (LENGTH: struct pj), 128 / 16 (LENGTH: fs_frame_bytes 1 by
   computation and its shadow bytes), 120 (LENGTH: RT_FLAGP), 160 / 176 (LENGTH: the realigned sp below sp0), 104
   (LENGTH: the 13 saves), 4096 / 2048 (LENGTH: the writer's first capacity and its half), 8 / 7 (LENGTH: a granule
   and its last byte), 63 / 64 (LENGTH: newcap's fuel), 3 (LENGTH: P8's driver blocks, PresetLiveBounds.DRV),
   123 / 91 (WORD: the bytes { and [ the reader dispatches on), 44 (WORD: the byte , ), 2 / 30 / 32 (LENGTH: wild trace
   counts, prh_wk F_parse_noting / RTT_WK_T / prh_wk F_round_trip_text), 2 ^ 28 / 2 ^ 30 / 2 ^ 32 / 2 ^ 36 / 2 ^ 40 /
   2 ^ 47 / 2 ^ 62 / 2 ^ 64 (LENGTH). No ADDRESS literal: every pc is pa_sigma / pa_val of the listing. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YG00cf YGcfStr YGcfTreeVis YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetLiveBounds PresetLiveSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetFreeFo PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterSpec WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102FR1Kit Rtt102FR1KitA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102CmpLib Rtt102CmpDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal PresetSecTotalRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- pure lemmas ---- *)

(* the writer's capacities double from 4096 (WriterSpec.v:29-43): a list of k of them ends at least 2048 * 2 ^ k, so
   the writer's call count is small when its last capacity is below the ceiling *)
Lemma pn_dbl_S : forall f c need, WriterSpec.dbl (S f) c need =
  if need <=? c then c else WriterSpec.dbl f (2 * c) need.
Proof. reflexivity. Qed.

Lemma pn_dbl_ge : forall f c need, 0 <= c -> c <= WriterSpec.dbl f c need.
Proof.
induction f as [|f IH]; intros c need Hc; [cbn [WriterSpec.dbl]; lia|].
rewrite pn_dbl_S. destruct (need <=? c); [lia|]. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma pn_newcap_ge : forall c need, (c = 0 \/ 4096 <= c) -> c < need ->
  4096 <= WriterSpec.newcap c need /\ 2 * c <= WriterSpec.newcap c need.
Proof.
intros c need Hc Hn. unfold WriterSpec.newcap.
destruct Hc as [-> | Hc].
- change (if 0 =? 0 then 4096 else 0) with 4096.
  pose proof (pn_dbl_ge 64 4096 need ltac:(lia)). lia.
- assert (Ec : (c =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Ec.
  assert (E : WriterSpec.dbl 64 (if false then 4096 else c) need = WriterSpec.dbl 63 (2 * c) need).
  { change (WriterSpec.dbl 64 (if false then 4096 else c) need) with (WriterSpec.dbl (S 63) c need).
    rewrite pn_dbl_S. rewrite (proj2 (Z.leb_gt need c) Hn). reflexivity. }
  rewrite E. pose proof (pn_dbl_ge 63 (2 * c) need ltac:(lia)). lia.
Qed.

Lemma pn_gc_last : forall ls x c, (c = 0 \/ 4096 <= c) ->
  WriterSpec.grow_calls x c ls = [] \/
  Z.max c 2048 * 2 ^ Z.of_nat (length (WriterSpec.grow_calls x c ls)) <= last (WriterSpec.grow_calls x c ls) 0.
Proof.
induction ls as [|l ls IH]; intros x c Hc; cbn [WriterSpec.grow_calls]; [left; reflexivity|].
destruct (Z.ltb_spec c (x + l + 1)) as [Hlt | Hge]; cbv iota.
- right. destruct (pn_newcap_ge c (x + l + 1) Hc Hlt) as [H1 H2].
  set (c' := WriterSpec.newcap c (x + l + 1)) in *.
  assert (HM : Z.max c 2048 * 2 <= c') by lia.
  destruct (WriterSpec.grow_calls (x + l) c' ls) as [|g gs] eqn:Eg.
  + cbn [length last]. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. exact HM.
  + destruct (IH (x + l) c' (or_intror H1)) as [E | E]; rewrite Eg in E; [discriminate E|].
    change (last (c' :: g :: gs) 0) with (last (g :: gs) 0).
    rewrite (Z.max_l c' 2048) in E by lia.
    assert (Hl : Z.of_nat (length (c' :: g :: gs)) = 1 + Z.of_nat (length (g :: gs))) by (cbn [length]; lia).
    rewrite Hl, Z.pow_add_r by lia. rewrite Z.pow_1_r.
    pose proof (Z.pow_nonneg 2 (Z.of_nat (length (g :: gs))) ltac:(lia)) as Hp.
    pose proof (Z.mul_le_mono_nonneg_r _ _ _ Hp HM) as HM2.
    lia.
- apply IH. exact Hc.
Qed.

Lemma pn_wcalls_lt : forall t p, last (PresetReqAt.wcaps t p) 0 < 2 ^ 47 -> PjWriteHyp.wcalls t p < 2 ^ 36.
Proof.
intros t p H. unfold PresetReqAt.wcaps in H. unfold PjWriteHyp.wcalls.
destruct (pn_gc_last (WriterSpec.piece_lens (WriterValue.wdpieces t p)) 0 0 (or_introl eq_refl)) as [E | E].
- rewrite E. cbn [length]. lia.
- pose proof (Nat2Z.is_nonneg (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces t p)))))
    as Hn.
  pose proof (Z.pow_gt_lin_r 2 _ ltac:(lia) Hn) as Hlt.
  change (Z.max 0 2048) with 2048 in E.
  assert (E47 : (2 : Z) ^ 47 = 2048 * 2 ^ 36) by reflexivity.
  lia.
Qed.

(* a register move *)
Lemma pn_vaddi0 : forall z, v_addi (w64 z) 0 = w64 z.
Proof. intros z. unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* the realigned sp (`addi sp, sp, -0xa0; andi sp, sp, -0x20`) lies 160 or 176 below a 16-aligned sp0 *)
Lemma pn_sp1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 176 <= RT_R sp0 <= sp0 - 160 /\ (RT_R sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H. unfold RT_R, RT_FRAME.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd2. rewrite H in Hd2.
set (r := (sp0 - 160) mod 32) in *. set (q1 := (sp0 - 160) / 32) in *. set (q2 := sp0 / 16) in *.
assert (Hr : r = 0 \/ r = 16) by lia.
split; [lia|].
replace (sp0 - 160 - r - sp0) with (- 160 - r) by lia.
destruct Hr as [Er | Er]; rewrite Er; reflexivity.
Qed.

(* THE ONE NAMED PEAK LEMMA for parse_noting (the brief: a callee's peak equality reaches peak <= peak' only through one
   named local lemma per callee; the E sweep restates those equalities). The text's peak' is the granted run's peak
   joined with the refusal peak, PRH_FnCheck.v:674-676 *)
Lemma pn_peak_le : forall peak peak' a b, peak' = Z.max (Z.max peak a) b -> peak <= peak'.
Proof. intros peak peak' a b ->. lia. Qed.

(* ---- A GRANTED READING'S OUTCOMES GIVE THE ALL-GRANTED FREE LIST. The reader monad's outcome list ok is consumed
   one answer per call; PjGrammar.agrees says a computation run on an ok that grants its first calls answers as on []
   (the same result and trace, the rest of ok after those calls). jfv / jfl (PresetReqAt.v:261-294) call grow,
   jr_name and jrv on the same ok in the same order as jrv / jrl, so they read the same answers too. ---- *)
Lemma pn_ag_some : forall A Bt (m : PjGrammar.M A) (k : A -> PjGrammar.M Bt) ok a t ok0,
  PjGrammar.agrees m -> m [] = (Some a, t, ok0) ->
  PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jbind m k [])))) ->
  ok0 = [] /\ PjGrammar.ok_upto ok (PjGrammar.calls t) /\ m ok = (Some a, t, skipn (PjGrammar.calls t) ok) /\
  PjGrammar.ok_upto (skipn (PjGrammar.calls t) ok) (PjGrammar.calls (snd (fst (k a [])))).
Proof.
intros A Bt m k ok a t ok0 Hm E Hu.
assert (E0 : ok0 = []).
{ pose proof (PjGrammar.agrees_nil A m Hm) as N. rewrite E in N. cbn [fst snd] in N. congruence. }
subst ok0.
assert (Ht : snd (fst (PjGrammar.jbind m k [])) = t ++ snd (fst (k a []))).
{ unfold PjGrammar.jbind. rewrite E. cbv beta iota. destruct (k a []) as [[r t'] ok2]. reflexivity. }
rewrite Ht, PjGrammar.calls_app in Hu.
assert (Hut : PjGrammar.ok_upto ok (PjGrammar.calls t)) by (eapply PjGrammar.ok_upto_le; [exact Hu | lia]).
split; [reflexivity|]. split; [exact Hut|]. split.
- pose proof (proj1 (Hm ok)) as H. rewrite E in H. cbn [fst snd] in H. exact (H Hut).
- apply PjGrammar.ok_upto_skipn. exact Hu.
Qed.

Lemma pn_ag_none : forall A Bt (m : PjGrammar.M A) (k : A -> PjGrammar.M Bt) ok t ok0,
  PjGrammar.agrees m -> m [] = (None, t, ok0) ->
  PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jbind m k [])))) ->
  PjGrammar.ok_upto ok (PjGrammar.calls t) /\ m ok = (None, t, skipn (PjGrammar.calls t) ok).
Proof.
intros A Bt m k ok t ok0 Hm E Hu.
assert (Hut : PjGrammar.ok_upto ok (PjGrammar.calls t)).
{ unfold PjGrammar.jbind in Hu. rewrite E in Hu. cbv beta iota in Hu. exact Hu. }
split; [exact Hut|].
pose proof (proj1 (Hm ok)) as H. rewrite E in H. cbn [fst snd] in H. exact (H Hut).
Qed.

Lemma pn_jf_cont_agree : forall (sm : list Z -> Z * Z) f d o x ok,
  (forall d o n cap acc af y ok,
     PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jrl sm f d o n cap acc y [])))) ->
     PresetReqAt.jfl sm f d o n cap af y ok = PresetReqAt.jfl sm f d o n cap af y []) ->
  PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jr_cont (PjGrammar.jrl sm f) d o x [])))) ->
  PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x ok = PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x [].
Proof.
intros sm f d o x ok IHl Hu. revert Hu. unfold PresetReqAt.jf_cont, PjGrammar.jr_cont.
destruct (Nat.ltb PjGrammar.MAXD (S d)); [intros _; reflexivity|].
cbv zeta. destruct (PjGrammar.skip (tl x)) as [|c r].
- intros Hu. eapply IHl. exact Hu.
- destruct (c =? PjGrammar.closer o); [intros _; reflexivity|]. intros Hu. eapply IHl. exact Hu.
Qed.

Lemma pn_jf_agree : forall (sm : list Z -> Z * Z) f,
  (forall d x ok, PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jrv sm f d x [])))) ->
     PresetReqAt.jfv sm f d x ok = PresetReqAt.jfv sm f d x []) /\
  (forall d o n cap acc af y ok,
     PjGrammar.ok_upto ok (PjGrammar.calls (snd (fst (PjGrammar.jrl sm f d o n cap acc y [])))) ->
     PresetReqAt.jfl sm f d o n cap af y ok = PresetReqAt.jfl sm f d o n cap af y []).
Proof.
intros sm f. induction f as [|f [IHv IHl]].
- split; intros; reflexivity.
- split.
  + intros d x ok Hu.
    pose proof (proj1 (proj1 (PjGrammar.agrees_fuel sm (S f)) d x ok) Hu) as Hag.
    cbn [PjGrammar.jrv] in Hu. revert Hu. cbn [PresetReqAt.jfv].
    destruct (PjGrammar.skip x) as [|b y]; [intros _; reflexivity|].
    destruct (b =? 123).
    { intros Hu. exact (pn_jf_cont_agree sm f d true (b :: y) ok IHl Hu). }
    destruct (b =? 91).
    { intros Hu. exact (pn_jf_cont_agree sm f d false (b :: y) ok IHl Hu). }
    intros _. rewrite Hag. reflexivity.
  + intros d o n cap acc af y ok Hu.
    cbn [PjGrammar.jrl] in Hu. cbn [PresetReqAt.jfl].
    destruct (PjGrammar.grow o n cap []) as [[[cap1|] tg] okg] eqn:Eg.
    * destruct (pn_ag_some _ _ _ _ ok cap1 tg okg (PjGrammar.agrees_grow o n cap) Eg Hu) as (E0 & _ & Eg1 & Hu1).
      subst okg. rewrite Eg1. cbv beta iota zeta in Hu1 |- *.
      destruct (PjGrammar.jr_name o y []) as [[[[nm y1]|] tn] okn] eqn:En.
      -- destruct (pn_ag_some _ _ _ _ _ (nm, y1) tn okn (PjGrammar.agrees_jr_name o y) En Hu1)
           as (E0n & _ & En1 & Hu2).
         subst okn. rewrite En1. cbv beta iota zeta in Hu2 |- *.
         destruct (PjGrammar.jrv sm f d y1 []) as [[[[v r]|] tv] okv] eqn:Ev.
         ++ destruct (pn_ag_some _ _ _ _ _ (v, r) tv okv (proj1 (PjGrammar.agrees_fuel sm f) d y1) Ev Hu2)
              as (E0v & Hut & Ev1 & Hu3).
            subst okv.
            pose proof (IHv d y1 (skipn (PjGrammar.calls tn) (skipn (PjGrammar.calls tg) ok))) as Hv.
            rewrite Ev in Hv. cbn [fst snd] in Hv. rewrite (Hv Hut), Ev1. cbv beta iota zeta in Hu3 |- *.
            revert Hu3. destruct (PjGrammar.skip r) as [|c r1]; [intros _; reflexivity|].
            destruct (c =? 44); [|intros _; reflexivity]. intros Hu3. eapply IHl. exact Hu3.
         ++ destruct (pn_ag_none _ _ _ _ _ tv okv (proj1 (PjGrammar.agrees_fuel sm f) d y1) Ev Hu2) as (Hut & Ev1).
            pose proof (IHv d y1 (skipn (PjGrammar.calls tn) (skipn (PjGrammar.calls tg) ok))) as Hv.
            rewrite Ev in Hv. cbn [fst snd] in Hv. rewrite (Hv Hut), Ev1. reflexivity.
      -- destruct (pn_ag_none _ _ _ _ _ tn okn (PjGrammar.agrees_jr_name o y) En Hu1) as (_ & En1).
         rewrite En1. reflexivity.
    * destruct (pn_ag_none _ _ _ _ ok tg okg (PjGrammar.agrees_grow o n cap) Eg Hu) as (_ & Eg1).
      rewrite Eg1. reflexivity.
Qed.

(* pj_free's list of a reading whose outcomes grant all its calls is the all-granted list *)
Lemma pn_pj_frees_agree : forall (sm : list Z -> Z * Z) x ok, PjGrammar.ok_upto ok (PjGrammar.ncalls sm x) ->
  PresetReqAt.pj_frees sm ok x = PresetReqAt.pj_frees sm [] x.
Proof.
intros sm x ok Hu. unfold PresetReqAt.pj_frees. apply (proj1 (pn_jf_agree sm _)).
unfold PjGrammar.ncalls in Hu. rewrite PjGrammar.jr_run_eq in Hu. cbn [snd] in Hu.
unfold PjGrammar.jr_value in Hu. exact Hu.
Qed.

(* a reading that returned a tree granted every call of the all-granted reading (PjGrammar.G7_2) *)
Lemma pn_ok_upto_some : forall (sm : list Z -> Z * Z) x ok t tr, PjGrammar.jr_run sm x ok = (Some t, tr) ->
  PjGrammar.ok_upto ok (PjGrammar.ncalls sm x).
Proof.
intros sm x ok t tr E.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls sm x)) as [H | (j & Hj & Hf & Hu)]; [exact H|].
exfalso. destruct (PjGrammar.G7_2 sm x ok j Hj Hf Hu) as [H0 _]. rewrite E in H0. discriminate H0.
Qed.

(* a callee-saved index is none of the four the segment writes *)
Ltac pn_ncs H := unfold acallee_saved in H;
  lazymatch type of H with context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v in H end; clear - H; lia.

(* the listing offset of round_trip_text's entry (DERIVED: 4 * its slot; = Rtt102R1A.v's RTT_K, Rtt102CmpS1.v's
   RTT_PC) *)
Definition RTT_K : Z := 4 * Z.of_nat (A_prog_slot AS_round_trip_text).

(* ======================================================================================================== *)
Section pn. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKR := (@STK_round_trip_text prh_img_A).
#[local] Notation STKP := (@STK_parse_noting prh_img_A).
#[local] Existing Instance prh_img_A.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
(* every journal of the walk is at RZW := YA0nH.wle' SEGS RZ_cf (Rtt102Cut.v's rtt_J) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild budget WS (YCbqG.v ajournal_xwR; AJ is it at WS = []) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
(* the cut's predicates at the Section's float state fx, BY NAME (a bound fxc / fx2 must not be picked for it) *)
#[local] Notation PRE := (rtt_pre (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx CTX0).
#[local] Notation RJ := (rtt_J (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RCARRY := (rtt_carry (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation POST := (rtt_post (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_LEN := (cmp_at_len (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_PN := (cmp_at_pn (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Abbreviation LEN D := (Z.of_nat (length (ri_tb D))).
#[local] Abbreviation BACK ly pos := (frame_addr ly RT_CID pos + RT_BACK).
#[local] Abbreviation FPB ly pos := [(frame_addr ly RT_CID pos + RT_BACK, frame_addr ly RT_CID pos + RT_BACK + 56)].
#[local] Abbreviation SP1 D := (RT_R (ri_sp D)).

(* ---- Section hypotheses (the brief's category (a), each with its owner) ---- *)
(* (a) the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x; S10TxString.v:163) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* (a) PRH_Base.v prh_head_wide (ONE spelling a walk takes; owner: the cf instance owner's preset_head_wide, cf_head = 16) *)
Hypothesis HW : prh_head_wide.
(* (b) the callee's kit text, parse_noting (PRH_FnCheck.v at the batch kit's cut 7cdbb61b5fa0, blob c40cf3fdcd2a; owned by the kit), at
   EVERY float state: the call is made at the cut's fxc, which rtt_fx does not equate to fx *)
Hypothesis TPN : forall fx0 : YK11.FPState,
  tparse_noting_specX (fx := fx0) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
(* (a) the preset instance's head (CfParams_preset's cf_head = 16 = alloc.c's HEAD; WalkRtt102's ruling: a Section
   hypothesis, owner the preset instantiation; RttCmp's Rtt102CmpA.v HHEAD) *)
Hypothesis HHEAD : cf_head = PresetReqAt.HEAD.
(* (a) the run's two meter caps within cp's caps (CrsSeg_W1.v / CrsSeg_X1.v / CrsSeg_Z.v HI_hull, an instance fact;
   witness CrsSeg_W1.crs_W1_HI_hull at CfParams_preset): the run position pays parse_noting's hull budget
   (pn_hull_budget) *)
Hypothesis HI_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax cp /\ PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max cp.

(* ---- a call of a BUDGETED FLOAT text from a concrete state (YCbqGwild.v aj_call_xbF_spR without its symbolic-state
   premise, at RZW, at a caller journal of the empty budget; the proof is aj_call_xbF_spR's, as Rtt102FR1Kit.v
   fr_call_at is YCbqGcall.v aj_call_x_sp's at RZW): the callee concludes SRr' with its journal at RZW
   (apost_base_xbFR, = PRH_Base's fpostFbm); the caller's journal after the call is at the callee's budget WS1, of
   which the text states P WS1 ---- *)
Lemma pn_call_atF : forall (fxc : YK11.FPState) W regs memc STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1
  FP1 (o : Z) raw ch1 pc (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJ STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regs = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regs) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regs memc mdc ch1 ->
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
     (YCbqGwild.apost_base_xbFR (fx := fxc) (SK := SK) SEGS B PST ARx RZW P STK1 FP1 regs lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK0 sp0 FP FP1 ly S own lyc Sc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
   (fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
    c2 = mkCfg (@YK11.mkst fx2 regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
    frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fxc fx2 /\ P WS1 /\
    AJW STK0 sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS1 /\
    AJW STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
    aregs_preserved regs regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros fxc W regs memc STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 pc P Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ apply Hcallee.
  exact (afn_pre_x_atR (SK := SK) SEGS B PST ARx RZW STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regs
    STK1 o ch1
    HJ Hsp' Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp'; exact Hch)). }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP & HQ).
exists fx2, ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HPW|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). change WS1 with ([] ++ WS1).
eapply (ajournal_xw_subR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf));
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* ---- the harness-block facts of a ledger entry (PRH_Base.v prh_ledger_blocks, the named projection) ---- *)
Lemma pn_hblock : forall ly S Hp W mem Lam peak cnt fail ran most own a k,
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin.
pose proof (proj1 (Forall_forall _ _)
  (prh_ledger_blocks (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) (a, k) Hin) as Hb.
cbn [fst snd] in Hb. destruct Hb as (Hk0 & Hab & Hhp & _). split; [exact Hk0|]. split; [exact Hab | exact Hhp].
Qed.

(* ---- what a BUDGETED callee's journal keeps (Rtt102FR1Kit.v rtt_kept_of_journal at any budget WS: the kept bytes are
   the journal's ajxR_hi / ajxR_blk / ajxR_img / ajxR_frm conjuncts, which read neither the budget nor the world
   conjunct) ---- *)
Lemma pn_kept_of_journal : forall STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS,
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  ~ YI16.sink_open_fp FP1 ->
  rtt_kept B lyc Sc Wc memc ly2 S2 W2 mem2 (sp1 - STK1) sp1 (inFP FP1) PST.
Proof.
intros STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS HJ Hcl.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3.
pose proof (ajxR_frm HJ) as F4.
split; [exact F1|]. split; [exact F2|].
split; [intros a Hi Ho He Hp; exact (F3 a Hi Ho He Hp (fp_spares_closed FP1 a Hcl))|].
exact F4.
Qed.

(* ---- the bytes the call's write set may meet: none of an entry harness block, none of a live frame but the RT_CID
   frame's back bytes ---- *)
Definition pn_off (D : rtt_in (L := A_prog_listing) (PA := PA)) (lyc : alayout) (Sc : astate) (pos x : Z) : Prop :=
  (forall a k, In (a, k) (ri_Lam D) -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) /\
  (forall cid pos', In (cid, pos') (frames Sc) -> in_zr x (frame_rng lyc (cid, pos')) ->
     cid = RT_CID /\ pos' = pos /\ BACK lyc pos <= x < BACK lyc pos + 56).

(* a live frame's bytes are none of its own shadow bytes (frames are application memory; Rtt102FR1Kit.v
   rtt_blk_off_sh's argument, for a frame) *)
Lemma pn_frame_off_sh : forall lyc Sc Hpc Wc memc mdc cid pos x,
  ARx lyc Sc Hpc Wc memc mdc -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid ->
  ~ in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8).
Proof.
intros lyc Sc Hpc Wc memc mdc cid pos x HARc Hf Hx Hz. unfold in_zr in Hz. cbn [fst snd] in Hz.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HARc Hf) as (Hf4 & Hfc & Happ).
pose proof (fs_frame_bytes_nonneg cid) as Hfb. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold shadow_addr, SHADOW_OFF in Hz.
set (F := frame_addr lyc cid pos) in *. set (fb := fs_frame_bytes cid) in *.
assert (Hd1 : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (Hd2 : 8 * (fb / 8) <= fb) by (apply Z.mul_div_le; lia).
assert (Hd3 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (Hd4 : 0 <= fb / 8) by (apply Z.div_pos; lia).
set (qF := F / 8) in *. set (qb := fb / 8) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold kHighMemBeg in C3. lia.
Qed.

(* a byte of back misses the entry's harness blocks and every live frame but its own *)
Lemma pn_back_off : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos Lamc peakc cntc failc ranc mostc ownc x,
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  prh_ledger (PI := prh_img_A) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> incl (ri_Lam D) Lamc ->
  BACK lyc pos <= x < BACK lyc pos + 56 ->
  pn_off D lyc Sc pos x.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos Lamc peakc cntc failc ranc mostc ownc x HC HLc Hinc Hx.
pose proof HC as (_ & HJc & (Efr & _) & _).
pose proof HJc as (HARc & _).
assert (Hin : In (RT_CID, pos) (frames Sc)) by (rewrite Efr; left; reflexivity).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HARc) as [Hpw _].
unfold RT_BACK in Hx.
split.
- intros a k Hk Hx2.
  destruct (pn_hblock lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc a k HLc (Hinc _ Hk)) as (_ & Hbc & _).
  pose proof (fr_pairwise_app zdisjoint _ _ _ _ Hpw (in_map (fun b0 => (fst b0, req_size (snd b0))) _ _ Hbc)
    (in_map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hin)) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. rewrite Efs1 in Hd. lia.
- intros cid pos' Hf Hz. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
  destruct (Z.eq_dec cid RT_CID) as [Ec | Nc]; [destruct (Z.eq_dec pos' pos) as [Ep | Np]|].
  + subst cid pos'. split; [reflexivity|]. split; [reflexivity|]. unfold RT_BACK. lia.
  + exfalso. assert (Hne : (cid, pos') <> (RT_CID, pos)) by (intros E0; injection E0; intros; contradiction).
    pose proof (pairwise_app_l zdisjoint _ _ Hpw) as [_ Hpf].
    destruct (fr_pairwise_in_map zdisjoint (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f)))
      _ _ _ Hpf Hf Hin Hne) as [Hd | Hd]; unfold zdisjoint in Hd; cbn [fst snd] in Hd; rewrite Efs1 in Hd; lia.
  + exfalso. assert (Hne : (cid, pos') <> (RT_CID, pos)) by (intros E0; injection E0; intros; contradiction).
    pose proof (pairwise_app_l zdisjoint _ _ Hpw) as [_ Hpf].
    destruct (fr_pairwise_in_map zdisjoint (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f)))
      _ _ _ Hpf Hf Hin Hne) as [Hd | Hd]; unfold zdisjoint in Hd; cbn [fst snd] in Hd; rewrite Efs1 in Hd; lia.
Qed.

(* back as parse_noting's out place: 8-aligned and ck_out_ok (in the fake frame, writable, addressable, its shadow
   hull inside the frame's shadow) *)
Lemma pn_back_ok : forall lyc Sc Hpc Wc regsc memc mdc pos STK1,
  ARx lyc Sc Hpc Wc memc mdc -> In (RT_CID, pos) (frames Sc) ->
  rtt_back lyc Wc memc pos ->
  YM05.alloc_ceiling <= spZ regsc - STK1 ->
  0 < BACK lyc pos /\ BACK lyc pos mod 8 = 0 /\
  ck_out_ok B STK1 lyc Sc Wc regsc memc (BACK lyc pos) 56.
Proof.
intros lyc Sc Hpc Wc regsc memc mdc pos STK1 HAR Hin HB Hstk.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc RT_CID pos HAR Hin) as (F32 & Happ & Hpr & Hsh).
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc RT_CID pos HAR Hin) as (Hf4 & Hfc & _).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
rewrite Efs1 in Happ, Hpr, Hsh, Hfc.
change (128 / 8) with 16 in Hsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rtt_back, RT_BACK in *.
set (F := frame_addr lyc RT_CID pos) in *.
apply Z.mod_divide in F32; [|lia]. destruct F32 as [f Ef].
split; [lia|].
split.
{ apply Z.mod_divide; [lia|]. exists (4 * f + 4). lia. }
split.
{ exists RT_CID, pos. split; [exact Hin|]. rewrite Efs1. lia. }
split; [lia|]. split; [lia|]. split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ.
  destruct Happ as (_ & [Hlo | (Hhb & Hhe)]); [left; rewrite C5; lia | right; rewrite C4; split; lia]. }
split.
{ intros a Ha. destruct (Hpr a ltac:(lia)) as (Hpa & Hno).
  split; [apply apresent_writable; exact Hpa|]. split; [exact Hno | lia]. }
split; [exact HB|].
intros _ s Hs.
assert (E0 : F / 8 = 4 * f) by (rewrite Ef; symmetry; apply (Z.div_unique _ _ _ 0); lia).
assert (E1 : (F + 32) / 8 = 4 * f + 4) by (rewrite Ef; symmetry; apply (Z.div_unique _ _ _ 0); lia).
assert (E2 : (F + 32 + 56 - 1) / 8 = 4 * f + 10) by (rewrite Ef; symmetry; apply (Z.div_unique _ _ _ 7); lia).
unfold shadow_addr in Hs, Hsh. rewrite E1, E2 in Hs. rewrite E0 in Hsh.
assert (Hr : SHADOW_OFF + 4 * f <= s < SHADOW_OFF + 4 * f + 16).
{ pose proof (Z.div_mod (SHADOW_OFF + (4 * f + 4)) 8 ltac:(lia)) as DA.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * f + 4)) 8 ltac:(lia)) as MA.
  pose proof (Z.div_mod (SHADOW_OFF + (4 * f + 10)) 8 ltac:(lia)) as DB.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * f + 10)) 8 ltac:(lia)) as MB.
  set (qa := (SHADOW_OFF + (4 * f + 4)) / 8) in *.
  set (qb := (SHADOW_OFF + (4 * f + 10)) / 8) in *.
  set (ra := (SHADOW_OFF + (4 * f + 4)) mod 8) in *.
  set (rb := (SHADOW_OFF + (4 * f + 10)) mod 8) in *.
  unfold SHADOW_OFF in *. lia. }
destruct (Hsh (s - (SHADOW_OFF + 4 * f)) ltac:(lia)) as (Hps & _).
assert (Es : SHADOW_OFF + 4 * f + (s - (SHADOW_OFF + 4 * f)) = s) by lia.
rewrite Es in Hps. exact (fr_aview_of_apresent SEGS _ _ _ Hps).
Qed.

(* ---- THE CARRIED STATE ACROSS parse_noting: Rtt102FR1Kit.v rtt_carry_keep with the write set allowed in the RT_CID
   frame's back bytes (pn_off), the float state moved to the callee's fx2, and the wild traces since the entry (rtt_carry's
   last conjunct) given at the new state: parse_noting's post is budgeted, so the caller derives them (rtt_wild_keep) ---- *)
Lemma pn_carry_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2,
  PRE D ->
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  rtt_fx (fx := fx) fx2 ->
  RJ D ly2 S2 Hp2 W2 mem2 md2 k2 pos ->
  frames S2 = frames Sc ->
  rtt_kept B lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  shi <= ri_sp D - 104 ->
  (forall a, Exists (in_zr a) P -> Exists (in_zr a) PST) ->
  (forall x, E x -> pn_off D lyc Sc pos x) ->
  prh_ledger (PI := prh_img_A) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> incl (ri_Lam D) Lamc ->
  prh_ledger (PI := prh_img_A) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 -> incl (ri_Lam D) Lam2 ->
  rtt_cregs B D ly2 regs2 pos ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  rtt_room D S2 ->
  rtt_wild (PA := PA) B D S2 (prh_wk F_round_trip_text) ->
  RCARRY D fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2
  HP HC HFX2 HJ2 HFR HK Hshi HPP HEoff HLc Hincc HL2 Hinc2 HCR2 HMN2 HROOM2 HW2.
pose proof (rtt_pre_facts B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & _ & HDL & _ & Hhome & _).
pose proof rtt_stkr_A as HSTKR.
pose proof HC as (_ & HJc & HFRc & HSVc & _ & HMNc & HRODc & _ & HNODEc & HVISc & _).
pose proof HK as (K1 & K2 & K3 & K4).
pose proof HJ2 as (HAR2 & _).
destruct (rtt_fa_eq B ARx SK D lyc Sc Hpc Wc memc mdc kc pos HJc) as (Fac & Flc).
destruct (rtt_fa_eq B ARx SK D ly2 S2 Hp2 W2 mem2 md2 k2 pos HJ2) as (Fa2 & Fl2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
pose proof HFRc as (Efr0 & Hni0 & _).
(* the entry's frames are live at both states *)
assert (HF0c : forall cid pos', In (cid, pos') (frames (ri_S D)) -> In (cid, pos') (frames Sc)).
{ intros cid pos' Hf. rewrite Efr0. right. exact Hf. }
assert (HF02 : forall cid pos', In (cid, pos') (frames (ri_S D)) -> In (cid, pos') (frames S2)).
{ intros cid pos' Hf. rewrite HFR. exact (HF0c cid pos' Hf). }
(* a byte of an entry frame is kept: the entry's frames are not the fake frame of this call's caller *)
assert (KF : forall cid pos' x, In (cid, pos') (frames (ri_S D)) ->
  frame_addr (ri_ly D) cid pos' <= x < frame_addr (ri_ly D) cid pos' + fs_frame_bytes cid ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
{ intros cid pos' x Hf Hx. apply (K4 cid pos' x (HF0c cid pos' Hf)).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac. lia.
  - intros HE. destruct (HEoff x HE) as (_ & Hfr).
    destruct (Hfr cid pos' (HF0c cid pos' Hf) ltac:(unfold in_zr, frame_rng; cbn [fst snd]; rewrite Fac; lia))
      as (-> & -> & _).
    exact (Hni0 Hf). }
(* a byte of an entry harness block is kept *)
assert (KB : forall a k x, In (a, k) (ri_Lam D) -> a - cf_head <= x < a - cf_head + req_size (k + cf_head) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
{ intros a k x Hin Hx.
  destruct (pn_hblock lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc a k HLc (Hincc _ Hin))
    as (_ & Hbc & _).
  destruct (pn_hblock ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k HL2 (Hinc2 _ Hin))
    as (_ & Hb2 & _).
  replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (K2 (a - cf_head) (k + cf_head) (x - (a - cf_head)) Hbc Hb2); [lia|].
  intros HE. destruct (HEoff _ HE) as (Hbl & _). apply (Hbl a k Hin). lia. }
split; [exact HFX2|].
split; [exact HJ2|].
split.
{ (* rtt_frame: the flag pointer at F + 120 is outside back *)
  destruct HFRc as (Efr & Hni & Hflag & _).
  split; [rewrite HFR; exact Efr|]. split; [exact Hni|]. split.
  - rewrite Fa2, Fl2. rewrite Fac, Flc in Hflag. rewrite <- Hflag. apply ts_rdword_keep. intros j Hj.
    apply (K4 RT_CID pos); [rewrite Efr; left; reflexivity | left | ].
    + unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac, Efs1. unfold RT_FLAGP. lia.
    + intros HE. destruct (HEoff _ HE) as (_ & Hfr).
      destruct (Hfr RT_CID pos ltac:(rewrite Efr; left; reflexivity)
        ltac:(unfold in_zr, frame_rng; cbn [fst snd]; rewrite Fac, Efs1; unfold RT_FLAGP; lia)) as (_ & _ & Hb).
      rewrite Fac in Hb. unfold RT_FLAGP, RT_BACK in *. lia.
  - intros a Ha. destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 RT_CID pos HAR2
      ltac:(rewrite HFR, Efr; left; reflexivity)) as (_ & _ & Hpr & _).
    exact (proj1 (Hpr a Ha)). }
split.
{ (* rtt_saved *)
  intros j Hj. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2); [|exact (HSVc j Hj)].
  intros i Hi. apply K1; unfold ri_sp in *; lia. }
split; [exact HCR2|].
split; [intros H; exact (HMN2 (HMNc H))|].
split.
{ (* the read-only view *)
  intros a Hro Hown Herr. rewrite (K3 a (rtt_ro_img a Hro) Hown Herr).
  - exact (HRODc a Hro Hown Herr).
  - intros HPa. exact (pst_not_ro_A a (HPP a HPa) Hro). }
split; [exact HROOM2|].
split.
{ (* doc's tree *)
  apply (pj_nodeR_frame SEGS _ _ _ _ _ _ HNODEc). intros x Hx.
  destruct Hhome as (cid & pos' & Hf & Hlo & Hhi).
  destruct Hx as [Hx | ((a, k) & HinD & Hx)].
  - assert (Hx' : frame_addr (ri_ly D) cid pos' <= x < frame_addr (ri_ly D) cid pos' + fs_frame_bytes cid) by lia.
    split; [apply mbyte_of_aview; exact (KF cid pos' x Hf Hx')|].
    intros _. apply apresent_writable.
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2 (HF02 cid pos' Hf)) as (_ & _ & Hpr & _).
    apply (Hpr x). rewrite Fa2. exact Hx'.
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (HDL _ HinD) as HinL.
    destruct (pn_hblock ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k HL2 (Hinc2 _ HinL))
      as (Hk0 & Hb2 & _).
    pose proof cf_head_nonneg as Hch0.
    assert (Hrq : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
    assert (Hx' : a - cf_head <= x < a - cf_head + req_size (k + cf_head)) by lia.
    split; [apply mbyte_of_aview; exact (KB a k x HinL Hx')|].
    intros _. apply apresent_writable.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2)
      as (_ & _ & _ & _ & Hpr & _).
    exact (proj1 (Hpr x Hx')). }
split.
{ (* the tree's visibility, re-derived at the new state from the harness-block laws *)
  unfold PRH_FnWriter.prhWriter_tree_vis, YGcfTreeVis.tree_vis_cf in *. intros a k HinD.
  destruct (HVISc a k HinD) as (V1 & V2 & V3 & V4 & _ & _ & _).
  pose proof (HDL _ HinD) as HinL.
  destruct (pn_hblock ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k HL2 (Hinc2 _ HinL))
    as (Hk0 & Hb2 & Hh2).
  pose proof cf_head_nonneg as Hch.
  assert (Hrq : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
  destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2 Hh2)
    as (Hbs & Hhull).
  replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2)
    as (_ & _ & _ & _ & Hpr & _).
  split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|].
  split.
  { intros x Hx. exact (block_shadow_range _ _ _ _ a k Hbs ltac:(lia) ltac:(lia) x Hx). }
  split.
  { intros Hk. assert (Er : req_size (k + cf_head) = k + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    rewrite Er in Hhull. replace (k + cf_head - cf_head) with k in Hhull by lia. apply Hhull. lia. }
  intros x Hx.
  destruct (Z_lt_le_dec x (a - cf_head + req_size (k + cf_head))) as [Hin | Hge].
  - apply fr_aview_of_apresent. exact (proj1 (Hpr x ltac:(lia))).
  - assert (Hmono : (a + k + 7) / 8 <= (a - cf_head + req_size (k + cf_head) + 7) / 8) by (apply Z.div_le_mono; lia).
    apply (alx_blocks_tail SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) x HAR2 Hb2).
    split; [exact Hge | lia]. }
exact HW2.
Qed.

(* *copy's 56 bytes (an entry frame, not the call's caller's fake frame) survive the call *)
Lemma pn_copy_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P,
  PRE D -> RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  rtt_kept B lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P -> (forall x, E x -> pn_off D lyc Sc pos x) ->
  rtt_copy_kept D Wc memc -> rtt_copy_kept D W2 mem2.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P HP HC HK HEoff HCK Hc0 a Ha.
pose proof (rtt_pre_facts B ARx CTX0 D HP) as (_ & _ & _ & _ & _ & _ & _ & Hcopy).
destruct Hcopy as [H0 | (cid & pos' & Hf & Hlo & Hhi)]; [exfalso; exact (Hc0 H0)|].
destruct (rtt_entry_frame B ARx SK D fxc lyc Sc Hpc Wc regsc memc mdc kc pos cid pos' HC Hf) as (Hfc & Fac).
pose proof HC as (_ & _ & (_ & Hni & _) & _).
pose proof HK as (_ & _ & _ & K4).
rewrite <- (HCK Hc0 a Ha). apply (K4 cid pos' a Hfc).
- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac. lia.
- intros HE. destruct (HEoff a HE) as (_ & Hfr).
  destruct (Hfr cid pos' Hfc ltac:(unfold in_zr, frame_rng; cbn [fst snd]; rewrite Fac; lia)) as (-> & -> & _).
  exact (Hni Hf).
Qed.

(* the reading's run events at the +772 position (rtt_pre's entry run events split by PRH_Base.prh_run_at_app_iff:
   ck_rtt_evs = rt_text ++ .., rt_text = w_evs ++ r_evs ++ parse_evs ++ r_free ++ w_free, PresetReqAt.v:310-311), over
   the instance's strtod model ReaderRes.jr_strtod, as the cut and parse_noting's text name it *)
Lemma pn_run_parse : forall D, PRE D ->
  prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_R D)%nat
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) []).
Proof.
intros D HP.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRUN & _).
unfold ck_rtt_evs in HRUN. apply prh_run_at_app_iff in HRUN as [HRUN _].
unfold PresetReqAt.rt_text in HRUN.
apply prh_run_at_app_iff in HRUN as [_ HRUN].
apply prh_run_at_app_iff in HRUN as [_ HRUN].
apply prh_run_at_app_iff in HRUN as [HRUN _].
unfold RT_K_R. rewrite Nat.add_assoc. exact HRUN.
Qed.

(* ... and their consumer window: rtt_pre's prh_cons_from over ck_rtt_evs (its last conjunct), split the same way by
   PRH_Base.prh_cons_from_app_iff *)
Lemma pn_cons_parse : forall D, PRE D ->
  prh_cons_from ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_R D)%nat
    (length (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) [])).
Proof.
intros D HP.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & HC & _).
unfold ck_rtt_evs in HC. rewrite length_app in HC. apply prh_cons_from_app_iff in HC as [HC _].
unfold PresetReqAt.rt_text in HC. rewrite !length_app in HC.
apply prh_cons_from_app_iff in HC as [_ HC].
apply prh_cons_from_app_iff in HC as [_ HC].
apply prh_cons_from_app_iff in HC as [HC _].
unfold RT_K_R. rewrite Nat.add_assoc. exact HC.
Qed.

(* ---- THE ROOM COUNTS FROM A POSITION (the text's position-free pkR premises, PRH_FnCheck.v:641-644) ---- *)
(* PresetRun.pkR read prefix by prefix: a bound at every prefix of the events bounds the peak *)
Lemma pn_pkR_bound : forall f s es (Bd : nat),
  (forall j, (j <= length es)%nat -> (PresetReqAt.cnt f (PresetReqAt.hlive_from s (firstn j es)) <= Bd)%nat) ->
  (PresetRun.pkR f s es <= Bd)%nat.
Proof.
intros f s es. revert s. induction es as [|e r IH]; intros s Bd H.
- cbn [PresetRun.pkR]. exact (H 0%nat (Nat.le_0_l _)).
- cbn [PresetRun.pkR]. apply Nat.max_lub.
  + exact (H 0%nat (Nat.le_0_l _)).
  + apply IH. intros j Hj. exact (H (Datatypes.S j) ltac:(cbn [length]; lia)).
Qed.

(* a prefix of a list then a prefix of what follows is a longer prefix *)
Lemma pn_firstn_add : forall {X : Type} (l : list X) i j, firstn i l ++ firstn j (skipn i l) = firstn (i + j) l.
Proof.
intros X l. induction l as [|a l IH]; intros i j.
- rewrite skipn_nil, !firstn_nil. reflexivity.
- destruct i as [|i]; cbn [firstn skipn app Nat.add]; [reflexivity|]. f_equal. apply IH.
Qed.

(* a count only grows along the sub-multiset order *)
Lemma pn_cnt_subm : forall f a b, PresetReqAt.subm a b -> (PresetReqAt.cnt f a <= PresetReqAt.cnt f b)%nat.
Proof.
intros f a b [d Hd]. rewrite (PresetReqAt.cnt_perm f _ _ Hd), PresetReqAt.cnt_app. lia.
Qed.

(* THE PEAK COUNT ALONG A RUN'S NEXT EVENTS, from a model-run position (named for other lanes): at a position i of
   the model run whose next events are E, the live set is the model's at i plus at most 3 driver blocks, and each
   prefix of E is a prefix of the run; a bound B on the model's count at every prefix of the run (PresetLiveSec
   live_sec / live_c24, for |x| <= MAXB) bounds the peak by B + 3. Above MAXB the run is empty
   (PresetRoomCounts.iface_hruns_big). *)
Lemma pn_pkR_pos : forall sm x os i H0 hist S E f Bn,
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> prh_run_at sm x os i E ->
  (Z.of_nat (length x) <= PresetReqAt.MAXB -> forall k,
     Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn k (PresetRun.hruns sm x os)))) <= Bn) ->
  0 <= Bn ->
  Z.of_nat (PresetRun.pkR f (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E) <= Bn + 3.
Proof.
intros sm x os i H0 hist S E f Bn ((d & Hd & Hp) & _) Hrun HB HB0.
set (Hr := PresetRun.hruns sm x os) in *.
set (L := PresetRoom.rs_live (YGcfRoom.room_of_cf S)) in *.
assert (HM : forall k, Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn k Hr))) <= Bn).
{ intros k. destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx | Hx]; [exact (HB Hx k)|].
  assert (E0 : Hr = []) by (unfold Hr; apply PresetRoomCounts.iface_hruns_big; lia).
  rewrite E0, firstn_nil. change (PresetReqAt.cnt f (PresetReqAt.hlive [])) with 0%nat. lia. }
assert (Hbd : (PresetRun.pkR f L E <= Z.to_nat Bn + 3)%nat).
{ apply pn_pkR_bound. intros j Hj.
  set (A := PresetReqAt.hlive (firstn i Hr)).
  assert (S1 : PresetReqAt.subm (PresetReqAt.hlive_from L (firstn j E))
                 (PresetReqAt.hlive_from (A ++ d) (firstn j E))).
  { apply PresetReqAt.hlive_from_mono. exists []. rewrite app_nil_r. exact (Permutation_sym Hp). }
  pose proof (PresetReqAt.hlive_from_le (firstn j E) A d) as S2.
  pose proof (pn_cnt_subm f _ _ (PresetReqAt.subm_trans _ _ _ S1 S2)) as C1.
  rewrite PresetReqAt.cnt_app in C1.
  pose proof (PresetLiveSec.cnt_le_len f d) as C2.
  assert (Ej : firstn j E = firstn j (skipn i Hr)).
  { unfold prh_run_at in Hrun. fold Hr in Hrun. rewrite <- Hrun at 1.
    rewrite firstn_firstn, Nat.min_l by exact Hj. reflexivity. }
  assert (EA : PresetReqAt.hlive_from A (firstn j E) = PresetReqAt.hlive (firstn (i + j) Hr)).
  { unfold A, PresetReqAt.hlive. rewrite <- PresetReqAt.hlive_from_app, Ej, pn_firstn_add. reflexivity. }
  rewrite EA in C1.
  pose proof (HM (i + j)%nat) as C3.
  lia. }
lia.
Qed.

(* THE HULL BUDGET OF A RUN'S NEXT EVENTS, from a model-run position (the Step-2 text's hull premise,
   PRH_FnCheck.v tparse_noting_specX; PresetHullPay.v hull_budget_of_room_pos's arithmetic at the Section's cp): the
   position's count conjunct (PresetRoomPos.rp_count) bounds the two meters by the run's prefix up to i, the next
   events E extend that prefix to i + |E| (prh_run_at, pn_firstn_add), a run of at most 4 calls makes at most 4 NCALL /
   4 TCALL in every prefix (PresetSecTotalRun.nsec_run_prefix / tsec_run_prefix), and the run's caps are within cp's
   (HI_hull). No bound on |E|'s input is needed: E is a piece of the run itself. *)
Lemma pn_hull_budget : forall sm x os i H0 hist S E, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> prh_run_at sm x os i E ->
  PresetHullBudget.hull_budget S E.
Proof.
intros sm x os i H0 hist S E Hlos Hpos Hrun.
pose proof Hpos as (_ & _ & _ & _ & _ & HC).
destruct (HC YGcfSecsStep.secs_steps_cf_holds) as [N T]. rewrite PresetRoomPos.rp_nsec_layer in N.
assert (EA : firstn i (PresetRun.hruns sm x os) ++ E = firstn (i + length E) (PresetRun.hruns sm x os)).
{ transitivity (firstn i (PresetRun.hruns sm x os) ++ firstn (length E) (skipn i (PresetRun.hruns sm x os)));
    [unfold prh_run_at in Hrun; rewrite Hrun; reflexivity | apply pn_firstn_add]. }
pose proof (PresetSecTotalRun.nsec_run_prefix sm x os (i + length E) Hlos) as Np.
pose proof (PresetSecTotalRun.tsec_run_prefix sm x os (i + length E) Hlos) as Tp.
rewrite <- EA, PresetSecTotal.nsec_app, Nat2Z.inj_add in Np. rewrite <- EA, PresetSecTotal.tsec_app in Tp.
rewrite PresetSecTotal.NCALL_value in Np. rewrite PresetSecTotal.TCALL_value in Tp.
unfold PresetRoomPos.rp_NB in N. unfold PresetRoomPos.rp_TB in T. change (2 ^ 30) with 1073741824 in T.
destruct HI_hull as [HCN HCT]. unfold PresetSecTotal.SEC_N_CAP, PresetSecTotal.SEC_T_CAP in HCN, HCT.
change (2 ^ 17) with 131072 in HCN. change (2 ^ 36) with 68719476736 in HCT.
unfold PresetHullBudget.hull_budget. split; lia.
Qed.

(* ======================================================================================================== *)
(* ---- THE SEGMENT: from +772 (strlen returned) through parse_noting (text, len, &back) to +788 ---- *)
Lemma cmp_pn : forall D, PRE D ->
  forall fxc ly S Hp W regs mem md k pos,
  AT_LEN D fxc ly S Hp W regs mem md k pos ->
  (* (no premise beyond the cut: K0-SRC-CEIL and K0-UNIV-END are retired at the batch kit's cut, header) *)
  (forall fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     AT_PN D fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (RTT_K + RT_C3))) mem2 (YK11.seg_rom SEGS)) md2)
       (POST D)) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_K + RT_C2))) mem (YK11.seg_rom SEGS)) md)
    (POST D).
Proof.
intros D HP fxc ly S Hp W regs mem md k pos HLEN HK.
destruct HLEN as (HCm & R10 & R23).
destruct HCm as (HCA & HBK & HS11 & HCK & q & capw & peakw & want & cap & R22 & R21 & Hq0 & Hw0 & (HLED & Hpk) &
  HNEW & HLENW & HLIVEW & HBQ & HBW & HWB & HLT & HAMR & HCAP & HCAPW & HPERM & HBB & HPOS & HW30).
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof (rtt_pre_facts B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & _ & _ & _).
pose proof HP as (HFPRE & HMN0 & HUNIV & _ & _ & _ & _ & _ & _ & _ & HWF & HDEP & HWLEN & _ & _ & HCNT & HRUN & HRAN &
  HRQA & HLIVE & HRQ & HFRN & _ & _ & _ & _ & _).
pose proof HCA as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HNODE & HVIS & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof HFR as (Efr & Hni & _).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HWB as (Hcap0 & Hwin & Hwnew & Hwhp & Hctx).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof rtt_stkr_A as HSTKR.
pose proof cf_head_nonneg as Hch.
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
assert (HinF : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
assert (HSTKP0 : 0 <= STKP) by (vm_compute; discriminate).
assert (HSTKPB : STKP + 176 <= STKR) by (vm_compute; discriminate).
destruct (pn_sp1 (ri_sp D) Hsp16) as (Hsp1 & Ho16).
(* the text's block: the harness block (q - cf_head, capw + cf_head), at the head of the ledger *)
destruct (pn_hblock ly S Hp W mem ((q, capw) :: ri_Lam D) peakw (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D))
  SIZE_MAXZ (ri_ran D) (ri_most D) 0 q capw HLED (or_introl eq_refl)) as (Hcw0 & Hqb & Hqh).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (q - cf_head) (capw + cf_head) HAR Hqb)
  as (_ & Hq4096 & Hqceil & _).
assert (Hrqw : capw + cf_head <= req_size (capw + cf_head))
  by (pose proof (req_size_pos (capw + cf_head)) as Hr; clear - Hr Hcw0 Hch; lia).
(* K0-SRC-CEIL RETIRED: the cut's src_rd (PRH_Base.v:1660) bounds the text's own bytes by the ceiling, and the text
   block is live: alx_blocks (YCbqG.v:113-116) ends it at or below the ceiling, and len < capw (rtt_at_cmp) *)
assert (HSRC_CEIL : q + LEN D <= YM05.alloc_ceiling) by (clear - Hqceil Hrqw HLENW; lia).
(* parse_noting's WILD ROOM (its 2 = prh_wk F_parse_noting): the text's entry room less the rendering's RTT_WK_T,
   Rtt102Cut.rtt_wild_room at rtt_at_cmp's last conjunct *)
assert (HWR : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S)).
{ apply (YCbqGwild.wild_room_le _ _ (prh_wk F_round_trip_text - RTT_WK_T)); [vm_compute; lia|].
  exact (rtt_wild_room (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx CTX0 D S RTT_WK_T HP HW30
    ltac:(vm_compute; lia)). }
pose proof YM05.alloc_ceiling_lt as Hceil47.
destruct (rcl_hblk_str B ARx LAWS HW ly S Hp W mem md ((q, capw) :: ri_Lam D) peakw
  (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D)) SIZE_MAXZ (ri_ran D) (ri_most D) 0 q capw (LEN D)
  HAR HLED (or_introl eq_refl) ltac:(lia) HLENW) as (_ & _ & Hqc & HAMRq & HRAq & HHVq & _).
assert (Hlen28 : LEN D + 1 <= 2 ^ 28) by exact HWLEN.
assert (HWC : PjWriteHyp.wcalls (ri_t D) (ri_p D) < 2 ^ 36) by (apply pn_wcalls_lt; rewrite <- HCAPW; lia).
assert (HWC0 : 0 <= PjWriteHyp.wcalls (ri_t D) (ri_p D)) by (unfold PjWriteHyp.wcalls; lia).
assert (Hncb : Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod (ri_tb D)) <= 2 * LEN D + 2).
{ pose proof (rcl_ncalls_len ReaderRes.jr_strtod (ri_tb D)) as H. lia. }
assert (Enc : ck_ncalls (ri_tb D) = Z.of_nat (PjRoundTrip.tcalls (ri_t D)))
  by exact (proj2 (rcl_read_back (ri_t D) (ri_p D) HWF)).
assert (Ecr : ck_read (ri_tb D) = Some (ri_t D)) by exact (proj1 (rcl_read_back (ri_t D) (ri_p D) HWF)).
pose proof (prh_ledger_bounds (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (_ & _ & HcntB & _).
(* THE REQUEST BOUND AT THE parse_noting CALL (the brief: library texts stand only where the request bound is carried):
   g_most is the entry's (the ledger field) and RQA_rtt t p <= most (rtt_pre), which bounds RQ_pj_parse tb *)
assert (HREQ_PN : prh_most (PI := prh_img_A) W mem (ri_most D) /\ RQA_rtt (ri_t D) (ri_p D) <= ri_most D).
{ split; [exact (prh_ledger_most (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ _ _ HLED) | exact HRQA]. }
unfold RT_C2.
(* +772 mv a1, a0 *)
eapply (fr_addi (fx := fxc) W regs mem md _ _ (RTT_K + 772) _ _ _ 11%bv 10%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity |].
intros mat1.
(* +776 mv a0, s6 *)
eapply (fr_addi (fx := fxc) W _ mem _ _ _ (RTT_K + 772 + 4) _ _ _ 10%bv 22%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity |].
intros mat2.
(* +780 mv a2, s7 *)
eapply (fr_addi (fx := fxc) W _ mem _ _ _ (RTT_K + 772 + 4 + 4) _ _ _ 12%bv 23%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity |].
intros mat3.
(* +784 jal parse_noting *)
eapply (fr_jal (fx := fxc) W _ mem _ _ _ (RTT_K + 772 + 4 + 4 + 4) (SIGMA AS_parse_noting));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | unfold RTT_K; vm_compute; discriminate | unfold RTT_K; vm_compute; reflexivity | vm_compute; reflexivity |].
intros mat4.
match goal with |- YA0nH.SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regsT := r); set (md4 := m) end.
assert (HJm : RJ D ly S Hp W mem md4 k pos).
{ unfold md4. repeat (apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW)). exact HJ. }
pose proof HJm as (HAR4 & _).
assert (HC4 : RCARRY D fxc ly S Hp W regs mem md4 k pos)
  by exact (rtt_carry_md (fx := fx) B ARx SK D fxc ly S Hp W regs mem md k pos md4 HCA HJm).
(* the call's registers: a0 = q, a1 = len, a2 = back, ra = the return site, the rest the cut's *)
assert (FK : forall r : bv 5, r <> 1%bv -> r <> 12%bv -> r <> 10%bv -> r <> 11%bv -> getr regsT r = getr regs r).
{ intros r H1 H12 H10 H11. unfold regsT.
  rewrite (getr_other _ 1%bv _ r) by exact H1. rewrite (getr_other _ 12%bv _ r) by exact H12.
  rewrite (getr_other _ 10%bv _ r) by exact H10. rewrite (getr_other _ 11%bv _ r) by exact H11. reflexivity. }
assert (G10 : getr regsT 10 = w64 q).
{ unfold regsT. rewrite (getr_other _ 1%bv _ 10%bv), (getr_other _ 12%bv _ 10%bv) by reg_neq_tac.
  rewrite (getr_same _ 10%bv) by reg_neq_tac. rewrite (getr_other _ 11%bv _ 22%bv) by reg_neq_tac.
  rewrite R22. apply pn_vaddi0. }
assert (G11 : getr regsT 11 = w64 (LEN D)).
{ unfold regsT. rewrite (getr_other _ 1%bv _ 11%bv), (getr_other _ 12%bv _ 11%bv), (getr_other _ 10%bv _ 11%bv)
    by reg_neq_tac.
  rewrite (getr_same _ 11%bv) by reg_neq_tac. rewrite R10. apply pn_vaddi0. }
assert (G12 : getr regsT 12 = w64 (BACK ly pos)).
{ unfold regsT. rewrite (getr_other _ 1%bv _ 12%bv) by reg_neq_tac. rewrite (getr_same _ 12%bv) by reg_neq_tac.
  rewrite (getr_other _ 10%bv _ 23%bv), (getr_other _ 11%bv _ 23%bv) by reg_neq_tac.
  rewrite R23. apply pn_vaddi0. }
assert (F1 : getr regsT 1 = Z_to_bv 64 (BASE + (RTT_K + RT_C3))).
{ unfold regsT. rewrite (getr_same _ 1%bv) by reg_neq_tac. unfold RT_C3. f_equal; lia. }
assert (F2 : spZ regsT = ri_sp D + (SP1 D - ri_sp D)).
{ unfold spZ. rewrite FK by reg_neq_tac. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (F8 : s0Z regsT = ri_sp D).
{ unfold s0Z. rewrite FK by reg_neq_tac. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (HRA : YK0s.ret_ok (Z_to_bv 64 (BASE + (RTT_K + RT_C3)))).
{ apply (ret_ok_codeptr_v (PI := PA)).
  - unfold RTT_K, RT_C3. split; vm_compute; first [discriminate | reflexivity].
  - unfold RTT_K, RT_C3. vm_compute. reflexivity. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + RT_C3)))) by (vm_compute; discriminate).
assert (HRAc : bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + RT_C3))) < YM05.alloc_ceiling).
{ assert (E : bv_unsigned (Z_to_bv 64 (BASE + (RTT_K + RT_C3))) < 2 ^ 32) by (vm_compute; reflexivity). lia. }
(* the chain at the call *)
destruct (rtt_chain_at B ARx SK CTX0 rtt_stkr_A D ly S Hp W mem md4 k pos (SP1 D) HP HJm HSV ltac:(lia))
  as (ch1 & Hach & _).
(* back as the out place *)
destruct (pn_back_ok ly S Hp W regsT mem md4 pos STKP HAR4 HinF HBK ltac:(rewrite F2; lia)) as (Hb0 & Hb8 & Hbout).
(* the write set misses what the carry reads *)
assert (HEoff : forall x, inFP (FPB ly pos) x -> pn_off D ly S pos x).
{ intros x (rg & [<- | []] & Hx). cbn [fst snd] in Hx.
  exact (pn_back_off D fxc ly S Hp W regs mem md4 k pos _ _ _ _ _ _ _ x HC4 HLED
    ltac:(intros bk Hbk; right; exact Hbk) Hx). }
assert (Hcl : ~ YI16.sink_open_fp (FPB ly pos)).
{ apply sink_closed_pos. constructor; [cbn [fst]; lia | constructor]. }
destruct HPOS as (hist & HIRP).
(* THE TEXT'S ROOM COUNTS at the call, from the exact position RT_K_R and the run's next events (pn_pkR_pos) *)
assert (HRSEC : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ unfold PresetLiveBounds.DRV.
  apply (pn_pkR_pos ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_R D)%nat (ri_H0 D) hist S _ _
    PresetLiveBounds.LSEC HIRP (pn_run_parse D HP)).
  - intros Hx k0. exact (PresetLiveSec.live_sec ReaderRes.jr_strtod (ri_x D) (ri_os D) k0 Hx).
  - rewrite PresetLiveBounds.LSEC_value. lia. }
assert (HR24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ unfold PresetLiveBounds.DRV.
  apply (pn_pkR_pos ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_R D)%nat (ri_H0 D) hist S _ _
    PresetLiveBounds.L24 HIRP (pn_run_parse D HP)).
  - intros Hx k0. exact (PresetLiveSec.live_c24 ReaderRes.jr_strtod (ri_x D) (ri_os D) k0 Hx).
  - rewrite PresetLiveBounds.L24_value. lia. }
(* THE TEXT'S HULL BUDGET at the call (its Step-2 premise), from the same position and next events: the run has at
   most 4 calls (Rtt102Cut.rtt_pre_os4) and its caps are within cp's (HI_hull; pn_hull_budget) *)
assert (HHULL : PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod (ri_tb D) [])).
{ exact (pn_hull_budget ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_R D)%nat (ri_H0 D) hist S _
    (rtt_pre_os4 B ARx CTX0 D HP) HIRP (pn_run_parse D HP)). }
(* the BUDGETED call (the caller's journal is rtt_J, the empty-budget journal from the depot-moved entry) *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (pn_call_atF fxc W regsT mem STKR (ri_sp D) (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D)) (ri_Hp D)
    (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp md4 k STKP (FPB ly pos) (SP1 D - ri_sp D)
    (Z_to_bv 64 (BASE + (RTT_K + RT_C3))) ch1 (SIGMA AS_parse_noting)).
  - exact HJm.
  - exact F2.
  - exact Ho16.
  - lia.
  - exact HSTKP0.
  - lia.
  - rewrite FK by reg_neq_tac. exact R3.
  - rewrite FK by reg_neq_tac. exact R4.
  - exact F1.
  - exact HRA.
  - exact HRA4.
  - replace (ri_sp D + (SP1 D - ri_sp D)) with (SP1 D) by lia. rewrite F8. exact Hach.
  - intros HAF.
    pose proof (TPN fxc (ri_most D) 0
      ly S Hp W regsT mem md4 ch1 q (ri_tb D) (BACK ly pos) ((q, capw) :: ri_Lam D) peakw
      (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D)) SIZE_MAXZ (ri_ran D)) as HT.
    cbv zeta in HT. apply HT; clear HT.
    + (* fpre, with the rounding mode 0 at entry (K0-FRM0-ENTRY) from rtt_fx: one line, proj1 HFX *)
      split; [exact HAF|]. split; [exact HROD|]. split; [rewrite F2; lia|].
      split; [unfold raZ; rewrite F1; exact HRAc | exact (proj1 HFX)].
    + exact (HMN HMN0).
    + exact HUNIV.
    + exact G10.
    + exact G11.
    + exact G12.
    + lia.
    + lia.
    + lia.
    + (* src_rd at q: the text's bytes, the block's bounds, the ceiling at the text's end (HSRC_CEIL) *)
      split.
      { unfold bytes_at in HBQ |- *. apply garr8_app in HBQ as [H0 _]. exact H0. }
      split; [lia|]. split; [exact HSRC_CEIL|]. split.
      { unfold YGcfStr.amem_range8 in HAMRq. unfold amem_range. lia. }
      split.
      { intros x Hx. apply HRAq. lia. }
      intros Hpos. apply (rcl_hull_sub _ q (LEN D + 1) q (LEN D)); [exact HHVq | lia | lia | exact Hpos].
    + (* prhReader_home by its first arm: kept_at in the ledger's harness block (q, capw) *)
      left. left. exists q, capw. split; [left; reflexivity | lia].
    + exact (rcl_maxrun (ri_t D) (ri_p D) HWLEN).
    + exact Hb8.
    + exact Hbout.
    + exact HRAN.
    + exact HLED.
    + lia.
    + unfold ri_tb. unfold LIVE_round_trip_text in HLIVE. lia.
    + unfold ri_tb. unfold RQ_rtt, zmaxl in HRQ. cbn [fold_right] in HRQ. lia.
    + (* the reading's requests are within g_most: RQ_pj_parse tb is a term of RQA_rtt t p (HREQ_PN) *)
      pose proof (proj2 HREQ_PN) as H. unfold RQA_rtt, zmaxl in H. cbn [fold_right] in H. unfold ri_tb.
      clear - H. lia.
    + rewrite Efr. cbn [length].
      assert (Ecap : ck_FRAMES_CAP - FR_round_trip_text + 1 <= ck_FRAMES_CAP - FR_parse_noting)
        by (vm_compute; discriminate).
      lia.
    + exact (proj1 HFX).
    + exact HROOM.
    + (* the wild room, 2 = prh_wk F_parse_noting fresh traces (HWR) *)
      exact HWR.
    + exact HRSEC.
    + exact HR24.
    + (* the hull budget of the reading's all-granted events (HHULL) *)
      exact HHULL.
  - (* the footprint is back, inside the function's own fake frame *)
    intros a (rg & [<- | []] & Ha). cbn [fst snd] in Ha.
    right. right. left. exists (RT_CID, pos). split; [left; reflexivity|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efs1. unfold RT_BACK in Ha. lia. }
(* ---- the post ---- *)
cbv beta. intros W3 c3 Hwle3 (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md5 & k1 & WS1 & -> & HFZ & HFK & HBUD & HJ3 & HJ1 &
  HP3 & (HQ & HMN3)).
destruct HQ as (_ & HRL2 & Lam' & peak' & cnt' & fail' & ran' & ok & res & tr & Hrun & _ & _ & Hout & _ &
  Hcnt & Hfa & Hpk' & _ & _ & _ & Hread & _ & HL2 & Hres).
pose proof (ajxR_ar HJ3) as HAR5.
pose proof (ajxR_frs HJ1) as HFR2.
(* THE JOURNAL AND THE WILD TRACES after the budgeted call: the caller's journal from the depot-moved entry at the
   callee's budget WS1 is rtt_J at the new state (rtt_J_redepot), and the wild traces since the entry are within
   RTT_WK_T + prh_wk F_parse_noting = 32 = prh_wk F_round_trip_text (rtt_wild_keep at the text's wbudget [] 2) *)
assert (HJ3r : RJ D ly2 S2 Hp2 W3 mem2 md5 (k + k1) pos)
  by exact (rtt_J_redepot B ARx SK D (st_depot S) WS1 ly2 S2 Hp2 W3 mem2 md5 (k + k1) pos HJ3).
assert (HW32 : rtt_wild (PA := PA) B D S2 (RTT_WK_T + prh_wk F_parse_noting)).
{ eapply (rtt_wild_keep B ARx SK D S RTT_WK_T); [| exact HW30 | exact HJ3 | exact HBUD]. reflexivity. }
pose proof (pn_peak_le _ _ _ _ Hpk') as Hpk2.
(* THE OUTCOME, GRANTED: parse_noting's outcome clause at the cut's position RT_K_R, the run's next events, their
   consumer window, and no injected failure (g_fail_at = SIZE_MAX); its ran-out outcome is refuted here *)
assert (Hfc : SIZE_MAXZ < ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) \/
  ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + ck_ncalls (ri_tb D) <= SIZE_MAXZ)
  by (right; unfold ck_ncalls, SIZE_MAXZ; clear - HCNT HWC Hncb Hlen28; lia).
destruct (Hout ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_R D)%nat (ri_H0 D) hist HIRP (pn_run_parse D HP)
  (pn_cons_parse D HP) Hfc) as (E0 & Hjr0 & _ & hist3 & HIRP3).
destruct (Hread E0 Hfc) as (Eres & Ecalls).
rewrite Ecr in Eres. rewrite Eres in Hrun, Hjr0, Hres.
rewrite E0 in HL2.
assert (Efail : fail' = SIZE_MAXZ).
{ destruct Hfa as [Fa1 Fa2].
  destruct (Z_lt_le_dec SIZE_MAXZ (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + Z.of_nat (PjGrammar.calls tr)))
    as [Hgt | Hle].
  - rewrite Fa1 by (clear - HcntB Hgt; unfold SIZE_MAXZ in *; lia). reflexivity.
  - apply Fa2. clear - Hle. lia. }
rewrite Efail in HL2.
destruct Hres as (R10' & D' & HLD & HlszD & HnlD & HrdD & HfoD & HnewD & HabD & HnodeD & HncapD).
(* the reading is the writer's tree's (PjRoundTrip.G9_trace) *)
assert (Etr' : tr = PjRoundTrip.ttrace (ri_t D)).
{ assert (Etr : tr = snd (PjGrammar.jr_run ReaderRes.jr_strtod (ri_tb D) [])) by (rewrite Hjr0; reflexivity).
  rewrite Etr. exact (PjRoundTrip.G9_trace ReaderRes.jr_strtod (ri_t D) HWF (ri_p D)). }
rewrite Etr' in HlszD, HnlD.
(* the outcome list ok of the granted reading reads as the all-granted one: its trace, and pj_free's list *)
assert (Ertr : PresetReqAt.rtr ReaderRes.jr_strtod ok (ri_tb D) = PresetReqAt.rtr ReaderRes.jr_strtod [] (ri_tb D)).
{ unfold PresetReqAt.rtr. rewrite Hrun, Hjr0. reflexivity. }
assert (Efrees : PresetReqAt.pj_frees ReaderRes.jr_strtod ok (ri_tb D) = PresetReqAt.fo (ri_t D)).
{ rewrite (pn_pj_frees_agree ReaderRes.jr_strtod (ri_tb D) ok (pn_ok_upto_some _ _ _ _ _ Hrun)).
  exact (PresetFreeFo.pj_frees_wdoc_t ReaderRes.jr_strtod (ri_t D) (ri_p D) HWF). }
assert (Hdep : (PjTree.depth (ri_t D) <= DOC_D)%nat) by (unfold DOC_D, PjGrammar.MAXD; clear - HDEP; lia).
(* the registers after the call *)
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite (ts_ap _ _ r HP3 Hr). apply FK; intros E; subst r; pn_ncs Hr. }
destruct (rtt_fa_eq B ARx SK D ly2 S2 Hp2 W3 mem2 md5 (k + k1) pos HJ3r) as (Fa3 & _).
destruct (rtt_fa_eq B ARx SK D ly S Hp W mem md4 k pos HJm) as (Fac & _).
assert (Fa : forall cid pos', frame_addr ly2 cid pos' = frame_addr ly cid pos')
  by (intros cid pos'; rewrite Fa3, Fac; reflexivity).
assert (R22' : getr regs2 22 = w64 q) by (rewrite KP by ts_cs; exact R22).
assert (R21' : getr regs2 21 = w64 want) by (rewrite KP by ts_cs; exact R21).
assert (R23' : getr regs2 23 = w64 (BACK ly2 pos)) by (rewrite KP by ts_cs; rewrite Fa; exact R23).
assert (HS11' : rtt_s11 regs2) by (unfold rtt_s11 in HS11 |- *; rewrite KP by ts_cs; exact HS11).
assert (HCR2 : rtt_cregs B D ly2 regs2 pos).
{ pose proof HCR as HCR'. unfold rtt_cregs in HCR' |- *. cbv zeta in HCR' |- *.
  rewrite !Fa. rewrite !KP by ts_cs. exact HCR'. }
(* the ledger list and the blocks after the call: the text's D' on top of the entry's *)
assert (HinLw' : forall bk, In bk ((q, capw) :: ri_Lam D) -> In bk Lam')
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym HLD)); apply in_or_app; right; exact Hbk).
assert (HabIn : forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HabD)); apply in_or_app; left; exact Hb).
assert (HLcase : forall a k0, In (a, k0) Lam' ->
    In (a, k0) ((q, capw) :: ri_Lam D) \/ ~ In (a - cf_head, k0 + cf_head) (ablocks B ly S)).
{ intros a k0 Hin. apply (Permutation_in _ HLD) in Hin. apply in_app_or in Hin as [Hin | Hin];
    [right; exact (HnewD a k0 Hin) | left; exact Hin]. }
assert (HinL' : incl (ri_Lam D) Lam') by (intros bk Hbk; apply HinLw'; right; exact Hbk).
(* want's block after the call: live, not a harness block *)
assert (Hwhp2 : ~ In want Hp2).
{ intros Hin.
  apply (Permutation_in _ (prh_ledger_heads (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ _ _ HL2)) in Hin.
  apply in_map_iff in Hin as ([a k0] & Ea & Hak). cbn [fst] in Ea.
  destruct (HLcase a k0 Hak) as [HinW | Hnot].
  - apply Hwhp. apply (Permutation_in _ (Permutation_sym (prh_ledger_heads (PI := prh_img_A) B _ _ _ _ _ _ _ _ _ _ _ _
      HLED))).
    apply in_map_iff. exists (a, k0). split; [exact Ea | exact HinW].
  - destruct (pn_hblock ly2 S2 Hp2 W3 mem2 Lam' peak' cnt' SIZE_MAXZ 0 (ri_most D) 0 a k0 HL2 Hak)
      as (Hk0 & Hab2 & _).
    assert (Hne : (want, cap) <> (a - cf_head, k0 + cf_head)) by (intros E; apply Hnot; rewrite <- E; exact Hwin).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W3 mem2 md5 want cap (a - cf_head) (k0 + cf_head) HAR5
      (HabIn _ Hwin) Hab2 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos cap) as Hr1. pose proof (req_size_pos (k0 + cf_head)) as Hr2.
    clear - Ea Hd Hr1 Hr2 Hcap0 Hk0 Hch. lia. }
assert (HWB5 : rtt_wblk B D ly2 S2 Hp2 want cap).
{ split; [exact Hcap0|]. split; [exact (HabIn _ Hwin)|]. split; [exact Hwnew|]. split; [exact Hwhp2 | exact Hctx]. }
(* the carried state *)
pose proof (pn_kept_of_journal STKP (ri_sp D + (SP1 D - ri_sp D)) (FPB ly pos) ly S Hp W mem md4 ly2 S2
  Hp2 W3 mem2 md5 k1 WS1 HJ1 Hcl) as HKj.
replace (ri_sp D + (SP1 D - ri_sp D)) with (SP1 D) in HKj by ring.
assert (HC5 : RCARRY D fx2 ly2 S2 Hp2 W3 regs2 mem2 md5 (k + k1) pos).
{ apply (pn_carry_keep D fxc ly S Hp W regs mem md4 k pos fx2 ly2 S2 Hp2 W3 regs2 mem2 md5 (k + k1)
    (SP1 D - STKP) (SP1 D) (inFP (FPB ly pos)) PST
    ((q, capw) :: ri_Lam D) peakw (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D)) SIZE_MAXZ (ri_ran D) (ri_most D) 0
    Lam' peak' cnt' SIZE_MAXZ 0 (ri_most D) 0 HP HC4).
  - split; [exact HFZ | exact (rcl_fregs_trans fx fxc fx2 (proj2 HFX) HFK)].
  - exact HJ3r.
  - exact HFR2.
  - exact HKj.
  - clear - Hsp1. lia.
  - exact (fun a Ha => Ha).
  - exact HEoff.
  - exact HLED.
  - intros bk Hbk. right. exact Hbk.
  - exact HL2.
  - exact HinL'.
  - exact HCR2.
  - exact HMN3.
  - exact HRL2.
  - (* 30 + 2 = 32 *)
    exact HW32. }
assert (HBK5 : rtt_back ly2 W3 mem2 pos).
{ apply (rtt_back_keep B ARx SK LAWS D fxc ly S Hp W regs mem md4 k pos ly2 S2 W3 mem2 _ _ (inFP (FPB ly pos)) PST
    HC4 HKj); [| exact Fa | exact HBK].
  intros x (rg & [<- | []] & Hx). cbn [fst snd] in Hx.
  apply (pn_frame_off_sh ly S Hp W mem md4 RT_CID pos x HAR4 HinF).
  rewrite Efs1. unfold RT_BACK in Hx. clear - Hx. lia. }
assert (HCK5 : rtt_copy_kept D W3 mem2)
  by exact (pn_copy_keep D fxc ly S Hp W regs mem md4 k pos ly2 S2 W3 mem2 _ _ (inFP (FPB ly pos)) PST HP HC4 HKj
    HEoff HCK).
(* ---- the +788 cut, granted ---- *)
apply (HK fx2 ly2 S2 Hp2 W3 regs2 mem2 md5 (k + k1)).
split; [exact HC5|]. split; [exact HBK5|]. split; [exact HS11'|]. split; [exact HCK5|]. split; [exact R23'|].
exists q, capw, want, cap, 0, Lam', peak', cnt', 0.
split; [exact R22'|]. split; [exact R21'|]. split; [exact R10'|]. split; [exact Hq0|]. split; [exact Hw0|].
split; [split; [exact HL2 | clear - Hpk Hpk2; lia]|].
split; [exact HWB5|].
split; [exact HNEW|].
split; [exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ S2 HIRP3))|].
split.
{ unfold cmp_out. cbv zeta.
  split; [rewrite HRAN; reflexivity|].
  split; [reflexivity|].
  split; [rewrite Hcnt, Ecalls, Enc; reflexivity|].
  exists D'.
  split; [exact HLD|].
  split.
  { intros a k0 Hin Hab0. apply (HnewD a k0 Hin). apply (Permutation_in _ (Permutation_sym HPERM)).
    right. right. exact Hab0. }
  split; [exact HlszD|].
  split.
  { (* the tree's blocks over the reader's own list, at ok's trace = the all-granted trace *)
    intros HH. pose proof (HrdD HH) as H1. rewrite Ertr in H1. exact H1. }
  split.
  { (* the tree's free order (the text's Some arm at n := DOC_D), whose list is fo t *)
    destruct (HfoD HHEAD DOC_D Hdep) as (F & HF1 & HF2).
    exists F. split; [rewrite Fa; exact HF1 | rewrite HF2; exact Efrees]. }
  split; [exact HnlD|].
  split.
  { eapply Permutation_trans; [exact HabD|]. rewrite app_assoc. apply Permutation_app_tail. exact HPERM. }
  split; [rewrite Fa; exact HnodeD|].
  split.
  { (* the tree's free order at every depth bound (the text's Some arm), over the all-granted reading's pj_frees *)
    intros HH nn Hnn. destruct (HfoD HH nn Hnn) as (F & HF1 & HF2).
    exists F. split; [rewrite Fa; exact HF1|]. rewrite HF2.
    exact (pn_pj_frees_agree ReaderRes.jr_strtod (ri_tb D) ok (pn_ok_upto_some _ _ _ _ _ Hrun)). }
  (* K0-CAP: the Some arm's pj_ncapR of back's tree *)
  rewrite Fa. exact HncapD. }
split.
{ (* the exact position after the reading (the text's outcome clause) *)
  exists hist3. unfold RT_K_P. rewrite Nat.add_assoc. exact HIRP3. }
split; [exact HCAP | exact HCAPW].
Qed.

End pn.

(* ---- THE STATEMENT CHECK (the text owner's rule of 2026-10-29, amended form): cmp_pn is a THEOREM, so its TYPE is the
   statement and `Check @` prints it with every implicit; pn_off is a DEFINITION, so its BODY is printed. PASS is the
   Section's fx in every class-implicit FPState position of a cut predicate (rtt_pre, cmp_at_len, cmp_at_pn,
   rtt_post, rtt_carry, rtt_fx), fx0 only under the TPN hypothesis's `forall fx0` (tparse_noting_specX), and fxc /
   fx' / fx2 only where the statement passes them explicitly ---- *)
Set Printing Implicit.
Unset Printing Notations.
Check @cmp_pn.
Check @pn_carry_keep.
Check @pn_pkR_pos.
Print pn_off.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions cmp_pn.
