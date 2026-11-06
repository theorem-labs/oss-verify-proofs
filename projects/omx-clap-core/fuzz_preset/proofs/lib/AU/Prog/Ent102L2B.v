(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b):
   SEGMENT L2 of LLVMFuzzerTestOneInput (entry 0x816cc): listing +0x14c .. +0x174 (0x81818 .. 0x81840), proved against
   lib/AU/Ent102CutsB.v's `seg_L2_stmt` (ec_laneR WLE' (cut_cno E fk) (cut_pno E fk \/ cut_exitR WLE' E fk)), the EXACT
   room position: cut_cno binds the grant triple trp with the tie `r = 1 <-> ec_ranout E trp = true`; the r = 1 arm
   ends the call's events (cut_exitR at the whole ec_call_evs E trp, = ec_cno_evs E trp by Ent102PosB's
   ec_call_evs_ranout_true); the r = 0 arm reads (parse_noting at e_i0 E + |ec_cno_evs E trp|, cut_pno + |ec_pn E| with
   ec_ranout E trp = false). The room-position reasoning is section 0'. The wild budget: cut_cno's journal at
   ec_wk_cno, parse_noting's budgeted
   post adds prh_wk F_parse_noting (cut_pno at ec_wk_pno = ec_wk_cno + prh_wk F_parse_noting), the accessors add
   nothing, and the r = 1 arm raises ec_wk_cno to ec_wk_exit (ec_wk_values). Every no-call stretch (a model
   materialization, the r = 1 budget growth) is Ent102CutsB's shared ec_inv_wk_growR (l2_inv_grow).
   THE WORLD RELATION (the re-hiding move): check_no_overread, before this segment, frees, so every cut here carries
   ec_invR at WLE' = wle' segs RZ_cf and the segment is SRrG at WLE' (SRr' segs RZ_cf). Plain step runs are opened by
   lib/Reusable/YGcfRhLift.v's ra_rh_of_SRr (l2_addi_step, the `jal` steps) and closed by l2_ret; the branch is
   Ent102CallB's ec_step_branchR; the call rules and the frame keep are Ent102L2BHelp's R forms at WLE'.
   THE B' TWIN of seg_L2_A in Ent102L2A.v (sha256 77a67220a8b2; internal record), ported by port/a2b.py
   (sha256 f5113cbc90e503da) and then by hand (L := B_prog_listing, lib/B / lib/AU modules, ei_empty's B' bounds
   IMG_LO_B / IMG_TOP_B; the segment's only pc-relative fields are its four `jal`s, the listing's symbolic PCall slots, so
   no slot word or offset changes).
   THE CODE (listing slots 83 .. 93):
     +0x14c bnez a0,+0x1c4          check_no_overread's r: r = 1 -> EXIT (cut_exit), r = 0 falls through
     +0x150 addi s5,s11,0x20        s5 = &doc = fk + 32
     +0x154 jal fuzz_alloc_live     +0x158 mv s6,a0   (live = 0: no harness block is live)
     +0x15c jal fuzz_alloc_count    +0x160 mv s7,a0   (the count before the reading)
     +0x164 jal fuzz_alloc_peak_reset
     +0x168 mv a0,s4; +0x16c mv a1,s3; +0x170 mv a2,s5; +0x174 jal parse_noting   (return site +0x178 = cut_pno)
   Each call is closed by the callee's batch-kit text from ec_texts (et_fuzz_alloc_live, et_fuzz_alloc_count,
   et_fuzz_alloc_peak_reset; et_parse_noting through lib/A/Prog/Ent102OfPost.v's tparse_noting_grantedX_of_post, the
   zero-hypothesis bridge to lib/A/Prog/Ent102GrantA.v's granted entry-keyed form), applied at its entry by
   lib/AU/Prog/Ent102L2BHelp.v's l2_callR (the accessors, empty budget, their plain texts read at WLE' by l2_lift_call,
   through Ent102CutsB's shared ec_journal_rebaseR / ec_journal_unbaseR) / l2_callbFR (parse_noting, budgeted, its
   text at SRr' segs RZ_cf); parse_noting's universe is ec_univ's eu_pno; its consumer window is
   lib/A/Prog/Ent102Win.v's cons_from_after_cno (l2_win_pn); its wild room is Ent102CutsB.ec_room_atR at ec_wk_cno; its
   hull budget is ec_hyps' ech_hull_pay at the cut's position with lib/A/PresetHullPay.v's hull_nt_parse (l2_arm0);
   the count and live budgets of cut_pno are paid by
   ec_pay's epay_pno and its live entry premise covered by ecov_pno; the ledger's two #102 cells (most own) are set
   at each call by Ent102CallB's shared ec_ledger_cells (section 0''); cut_pno's free order ec_pjf is supplied from
   the text's free-order conjunct by the kit's bridge PRH_FnPj.prhPj_frees_acc (section 6). No provisional argument.
   The slot steps and the frame geometry are lib/AU/Prog/Ent102L6BfLem.v's, the frame chain, the payload's home
   (ec_src_home_cutR), the branch step (ec_step_branchR) and ec_ledger_cells lib/AU/Prog/Ent102CallB.v's; the call's
   run premise and the two call_evs arm equations are lib/AU/Ent102PosB.v's (blob 853ec706aac5); the consumer window
   and the parse_noting bridge are the image-free lib/A/Prog/Ent102Win.v / Ent102OfPost.v.
   STATEMENT: lib/AU/Ent102CutsB.v (section 9 ec_laneR WLE' from cut_s1 on), written against
   Ent102CutsB.v (sha256 3e64c335b1db; internal record), with the primed texts of
   Ent102GrantA.v (sha256 bbc52b36b13e; internal record) and Ent102OfPost.v (sha256 8956803bd0b5; internal record)
   and CallB's R projections.
   LISTING: lib/B/Listing_prog.v (blob c97cc46b3e13; slot k = byte offset 4k from the entry), run with the PAListing
   PL_102_B of lib/B/Ent102PLB.v (blob e0348e1212c9); the image half stays generic ({PA : PAImg B_prog_listing};
   lib/B/PAImg_prog.v is not loaded, no vm_compute on pa_val / pa_sigma).
   The batch kit's TEXTS (generic over the listing class, the same files on both images): lib/A/PRH_FnAlloc.v
   (tfuzz_alloc_live_specX, tfuzz_alloc_count_specX, tfuzz_alloc_peak_reset_specX), lib/A/PRH_FnCheck.v
   (tparse_noting_specX), lib/A/PRH_Base.v (fpre, fpostm, fpostFbm, prh_ledger and its named projections, prh_run_at,
   prh_cons_from, prh_oks), lib/A/PRH_FnPj.v (prhPj_frees_acc); YCbqG's wild journal ajournal_xw and
   lib/Reusable/YCbqGwild.v (wbudget, wbudget_app).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L2 on image B' (reuse search: the released-proof index by
   name LLVMFuzzerTestOneInput exit 0, only the released plain / ubsan contract definitions; by address 0x815e0 exit
   4; check CONFIRM 14:51Z: no released ASan proof, NEW walk; the A' twin is lib/A/Prog/Ent102L2A.v).
   NUMERALS: 332 .. 376 are the slot offsets of this segment (DERIVED: EC_AR_CNO - EC_BASE = 0x14c .. EC_AR_PNO - EC_BASE
   = 0x178, four bytes a slot, the same on both images) and 452 the branch's target slot (EC_EXIT - EC_BASE = 0x1c4); 128 / 144 / 104 / 56 /
   32 / 16 / 8 are LENGTHs of this frame (EC_SAVE, EC_SAVE + 16, the saved block, the document, its offset in the fake
   frame, the frame shadow, the word); 32768 is LLVMF_STK; 2 ^ 40 / 2 ^ 47 / 2 ^ 62 / 2 ^ 64 are the engine's ranges.
   No ADDRESS. *)
From stdpp Require Import list.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PjRoundTrip PjReqBoundW PresetReqAt
  PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnAlloc PRH_FnCheck PRH_FnPj
  PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102PosB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102GrantA Ent102Win.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import Ent102L6BfLem Ent102CallB Ent102L2BHelp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102OfPost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjReqBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section L2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variables ec_ccut ec_lcut : @ecx rc B_prog_listing PA -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo rc B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi rc B_prog_listing PA).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp B_prog_listing PA B).
#[local] Notation ECX := (@ecx rc B_prog_listing PA).
(* THE WORLD RELATION AFTER check_no_overread's FREES (lib/AU/Ent102CutsB.v: cut_cno, cut_pno and cut_exitR carry
   ec_invR at wle' segs RZ_cf, and seg_L2_stmt is ec_laneR WLE'): the cut invariant and the journal are at WLE' *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).
#[local] Notation EINV := (@ec_invR fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO WLE').
#[local] Notation EPRE := (@ec_pre fx rc ci cp PI RL B_prog_listing PA B EC_RA EC_EMPTY EC_SIO).
(* the call's journal from entry at a WILD BUDGET WS, at WLE' (YCbqG's ajournal_xwR; ec_invR's first conjunct) *)
#[local] Notation EJ E own ly S Hp W mem md k WS := (ajournal_xwR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E)
  [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own ly S Hp W mem md k WS).
(* a run of plain steps in a segment at WLE': YGcfRhLift.ra_rh_of_SRr opens it (the steps keep the world, YA0n's SRr), and
   l2_ret closes it at the next SRr' goal *)
Local Ltac l2_ret := apply SRr_ret; cbv beta.
(* one conjunct of ec_pre by its TYPE (Ent102CallB.v ec_conj_pick). The conjuncts after e_i0's are read this way:
   the two texts of ec_pre put `(length (e_os E) <= 3)%nat` at different positions (after e_i0's conjunct, or after
   the count headroom `e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30`) *)
Local Ltac l2_pre H := clear - H; unfold ec_pre in H; ec_conj_pick H.

(* parse_noting's text: NO provisional argument. ec_texts' et_parse_noting is the kit's tparse_noting_specX; the
   granted entry-keyed form the walk applies is DERIVED from it by lib/A/Prog/Ent102OfPost.v's
   tparse_noting_grantedX_of_post (no hypothesis: the batch kit's own outcome clause fixes ran' = 0 under the window and the pick
   condition). *)

(* ---------------------------------------------------------------------- *)
(* 0''. THE LEDGER'S TWO #102 CELLS (the kit's PRH_Base.v (sha256 d27268feabfe; internal record): prh_ledger carries
       g_most / g_own_ran_out as its `most own`
       fields; a text that leaves them alone states the same most / own in its post). Each call of this body is made
       with the ledger's cells set to the values the cut reads (ec_most's PJ_ALLOC_BOUND (e_n E), ec_own_is's 0) by
       lib/AU/Prog/Ent102CallB.v's shared ec_ledger_cells, so the post's ledger gives ec_most / ec_own_is back by
       PRH_Base's projections. *)
(* every request of the reading is within g_most: each call's request of any reading of x is at most 56 |x| + 448
   (PjReqBound.jr_req_bound_56), below PJ_ALLOC_BOUND |x| *)
Lemma l2_reqs_most : forall sm x ok i,
  nth i (prh_ev_reqs (snd (jr_run sm x ok))) 0 <= PJ_ALLOC_BOUND (Z.of_nat (length x)).
Proof.
intros sm x ok i.
assert (Hall : forall y, In y (prh_ev_reqs (snd (jr_run sm x ok))) ->
  y <= PJ_ALLOC_BOUND (Z.of_nat (length x))).
{ intros y Hy. unfold prh_ev_reqs in Hy. apply in_map_iff in Hy as (e & He & Hin).
  apply list_elem_of_In, list_elem_of_filter in Hin as [_ Hin]. apply list_elem_of_In in Hin.
  pose proof (PjReqBound.jr_req_bound_56 sm ok x e Hin) as Hb. unfold PJ_ALLOC_BOUND. lia. }
destruct (Nat.lt_ge_cases i (length (prh_ev_reqs (snd (jr_run sm x ok))))) as [Hi|Hi].
- apply Hall. apply nth_In. exact Hi.
- rewrite nth_overflow by exact Hi. unfold PJ_ALLOC_BOUND. lia.
Qed.

(* the reading met no refusal and no injected failure in its range (the batch kit's outcome clause, 8-argument prh_oks: a
   refusal of a request within g_most sets g_ran_out): its outcomes are the all-granted ones *)
Lemma l2_agree : forall ok cnt fail k ns most ran', prh_oks ok cnt fail k ns most 0 ran' -> ran' = 0 ->
  cnt + Z.of_nat k <= fail -> (forall i, nth i ns 0 <= most) ->
  PRH_FnReader.prhReader_agree ok [] k.
Proof.
intros ok cnt fail k ns most ran' (_ & _ & H3) Hr Hk Hns j Hj. destruct j as [|j]; cbn [nth];
  destruct (nth _ ok true) eqn:E; try reflexivity; exfalso.
- assert (Hrf : prh_refused ok cnt fail 0 = true).
  { unfold prh_refused. rewrite E. cbn [negb andb]. apply negb_true_iff, Z.eqb_neq. lia. }
  pose proof (H3 0%nat Hj Hrf (Hns 0%nat)). lia.
- assert (Hrf : prh_refused ok cnt fail (S j) = true).
  { unfold prh_refused. cbn [nth]. rewrite E. cbn [negb andb]. apply negb_true_iff, Z.eqb_neq. lia. }
  pose proof (H3 (S j) Hj Hrf (Hns (S j))). lia.
Qed.

(* all granted: the refusal peak is 0 (PRH_Base.prh_refused_peak_granted) *)
Lemma l2_granted_of_agree : forall ok cnt fail k, PRH_FnReader.prhReader_agree ok [] k -> prh_granted ok cnt fail k.
Proof.
intros ok cnt fail k HA i Hi Hf. pose proof (HA i Hi) as H. rewrite Hf in H. destruct i; discriminate H.
Qed.

(* ---------------------------------------------------------------------- *)
(* 0'. THE ROOM POSITION of this segment, kept apart from the stepping. cut_cno binds the grant triple trp and ties
      check_no_overread's return to it (`r = 1 <-> ec_ranout E trp = true`). Under e_n E <= EC_NMAX = MAXB the two
      arms of call_evs are Ent102PosB's ec_call_evs_ranout_true / _false: r = 1, the call's events END with
      check_no_overread's; r = 0, call_rest follows them, and its first piece is the reading. *)
Lemma l2_maxb : forall (E : ECX), EPRE E -> e_n E <= EC_NMAX -> Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB.
Proof.
intros E HPRE HnMAX. pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hnlen & _).
unfold e_x, ec_bytes. rewrite length_map, <- Hnlen. unfold PresetReqAt.MAXB. unfold EC_NMAX in HnMAX. lia.
Qed.

(* r = 0: parse_noting's run premise at cut_cno's position, from the call's run (Ent102PosB's ec_supply_run, by
   construction) split by ec_run_split *)
Lemma l2_run_pn : forall (E : ECX) (trp : ec_trip),
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  ec_call_evs E trp = ec_cno_evs E trp ++ PresetRun.call_rest (e_sm E) (e_x E) ->
  PRH_Base.prh_run_at (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp)) (ec_pn E).
Proof.
intros E [[o1 o2] o0] Hi0 Heq.
pose proof (Ent102PosB.ec_supply_run (e_sm E) (e_x E) (e_os E) o1 o2 o0) as Hrun.
change (PresetRun.call_evs (e_sm E) (e_x E) o1 o2 o0) with (ec_call_evs E (o1, o2, o0)) in Hrun.
rewrite Heq in Hrun. unfold PresetRun.call_rest in Hrun. cbv zeta in Hrun.
rewrite Hi0. unfold ec_pn.
exact (Ent102PosB.ec_run_split _ _ _ _ _ _ _ Hrun).
Qed.

(* r = 0: parse_noting's CONSUMER WINDOW (the batch kit's outcome-clause premise) over the reading's events at cut_cno's position,
   by the shared lib/A/Prog/Ent102Win.v cons_from_after_cno: none of check_no_overread's readings ran out *)
Lemma l2_win_pn : forall (E : ECX) (trp : ec_trip),
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB -> ec_ranout E trp = false ->
  PRH_Base.prh_cons_from (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp))
    (length (PresetReqAt.parse_evs (e_sm E) (e_x E) [])).
Proof.
intros E [[o1 o2] o0] Hi0 Hx Hro.
unfold ec_ranout in Hro. apply orb_false_iff in Hro as [Hro H0]. apply orb_false_iff in Hro as [H1 H2].
pose proof (Ent102PosB.ec_call_evs_ranout_false _ _ _ E (o1, o2, o0) Hx
  ltac:(unfold ec_ranout; rewrite H1, H2, H0; reflexivity)) as Heq.
change (ec_cno_evs E (o1, o2, o0)) with (Ent102Win.cno_part (e_sm E) (e_x E) o1 o2 o0) in *.
apply (Ent102Win.cons_from_after_cno (e_sm E) (e_x E) (e_os E) o1 o2 o0); [exact Hx | exact H1 | exact H2 | exact H0 | lia|].
rewrite Ent102Win.hruns_snoc, length_app, <- Hi0.
change (PresetRun.call_evs (e_sm E) (e_x E) o1 o2 o0) with (ec_call_evs E (o1, o2, o0)).
rewrite Heq, length_app. unfold PresetRun.call_rest. cbv zeta. rewrite length_app. lia.
Qed.

(* r = 0: the position after the reading is cut_pno's index *)
Lemma l2_pos_pn : forall (E : ECX) (trp : ec_trip) hist S,
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
    (e_i0 E + length (ec_cno_evs E trp) + length (PresetReqAt.parse_evs (e_sm E) (e_x E) [])) (e_H0 E) hist S ->
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E))
    (e_H0 E) hist S.
Proof. intros E trp hist S H. unfold ec_pn. rewrite length_app, Nat.add_assoc. exact H. Qed.

(* r = 1: cut_cno's position is the end of the call's events, cut_exit's index *)
Lemma l2_pos_exit : forall (E : ECX) (trp : ec_trip) (os_c : list ec_trip) S,
  ec_call_evs E trp = ec_cno_evs E trp ->
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os_c (e_i0 E + length (ec_cno_evs E trp)) (e_H0 E)
     hist S) ->
  exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os_c (e_i0 E + length (ec_call_evs E trp)) (e_H0 E)
    hist S.
Proof. intros E trp os_c S Heq H. rewrite Heq. exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. A call site of this body: the facts l2_call asks of the caller's state after the `jal` (ra = the slot after it).
      The callee's sp is A (ec_rk), 128 or 144 bytes below sp0; the frame chain the callee sees is the one s0 = sp0
      starts (the saved ra / s0 at sp0 - 8 / sp0 - 16, ec_saved), or empty when sp0 is at the stack's top. *)
Lemma l2_site : forall (E : ECX) fk ly S Hp (W : world SEGS) regs mem md own kj WS kr,
  EJ E own ly S Hp W mem md kj WS ->
  EPRE E -> ec_rk E fk regs -> ec_frame E fk W mem ->
  0 <= kr < 2 ^ 40 -> kr mod 2 = 0 -> plookup (@pl_tpi _ PL_102_B) kr <> None ->
  exists ch,
    spZ (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) = e_sp0 E + (e_B E - e_sp0 E) /\
    (e_B E - e_sp0 E) mod 16 = 0 /\ e_B E <= e_sp0 E - EC_SAVE /\ e_sp0 E - e_B E <= EC_SAVE + 16 /\
    YK0s.ret_ok (getr (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) 1) /\
    4096 <= raZ (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) /\
    raZ (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) < YM05.alloc_ceiling /\
    getr (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) 3 = w64 (as_gp B) /\
    getr (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) 4 = w64 (as_tp B) /\
    achain ly (aview SEGS (w_H W) mem) (spZ (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))))
      (s0Z (regupd regs 1%bv (Z_to_bv 64 (BASE + kr)))) ch /\
    spZ (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) + 64 <= ly_stk_hi ly /\
    YM05.alloc_ceiling + LLVMF_STK - (EC_SAVE + 16) <= e_B E.
Proof.
intros E fk ly S Hp W regs mem md own kj WS kr HJ HPRE Hrk Hfrm Hkr Hkr2 Hpl.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HPRE as (HPREX & Hs0 & _).
pose proof HPREX as (_ & _ & Hra4E & HgpE & HtpE & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & _).
destruct Hrk as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27).
destruct Hfrm as (Hsaved & _ & _).
destruct Hsaved as (Sra & S8 & _).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & HB4).
unfold LLVMF_STK, EC_SAVE in *.
assert (HA : e_B E = (e_sp0 E - 128) / 32 * 32).
{ unfold e_B, ec_B, EC_SAVE. apply l6f_land_neg32. lia. }
assert (HA1 : e_sp0 E - 160 < e_B E <= e_sp0 E - 128).
{ rewrite HA. pose proof (Z.mul_div_le (e_sp0 E - 128) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (e_sp0 E - 128) 32 ltac:(lia)). pose proof (Z.div_mod (e_sp0 E - 128) 32 ltac:(lia)).
  lia. }
assert (HA2 : (e_B E - e_sp0 E) mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). exists (2 * ((e_sp0 E - 128) / 32) - e_sp0 E / 16).
  rewrite HA. pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)). lia. }
assert (HA4 : e_sp0 E - e_B E <= 144).
{ pose proof (proj1 (Z.mod_divide _ 16 ltac:(lia)) HA2) as (q & Hq). lia. }
assert (E1 : getr (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) 1 = Z_to_bv 64 (BASE + kr))
  by (apply l2_getr_upd_same; reflexivity).
assert (Eo : forall r : bv 5, r <> 1%bv -> getr (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) r = getr regs r)
  by (intros r Hr; apply l2_getr_upd_other; exact Hr).
assert (Esp : spZ (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) = e_B E).
{ unfold spZ. rewrite (Eo 2%bv ltac:(l6f_regne)), R2. apply unsigned_lit_small. lia. }
assert (Es0 : s0Z (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) = e_sp0 E).
{ unfold s0Z. rewrite (Eo 8%bv ltac:(l6f_regne)), R8. apply unsigned_lit_small. lia. }
assert (Era : raZ (regupd regs 1%bv (Z_to_bv 64 (BASE + kr))) = BASE + kr).
{ unfold raZ. rewrite E1. apply unsigned_lit_small. lia. }
destruct (plookup (@pl_tpi _ PL_102_B) kr) as [e|] eqn:Hpe; [|exfalso; exact (Hpl eq_refl)].
pose proof (l6f_slot_img (PA := PA) kr e Hkr Hpe) as Himg.
pose proof (pa_segs_low _ Himg) as Hlow.
destruct HAR as (HARcf & HXS).
pose proof (l6f_img_bounds (cp := cp) B ly S Hp W mem md _ (conj HARcf HXS) Himg) as (Hilo & _).
assert (Hrng8 : 0 <= bv_unsigned (getr (e_regs E) 8) < 2 ^ 64) by apply u64_range.
assert (Hrng1 : 0 <= raZ (e_regs E) < 2 ^ 64) by apply u64_range.
assert (Hal8 : e_sp0 E mod 8 = 0).
{ pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)). apply (proj2 (Z.mod_divide _ 8 ltac:(lia))).
  exists (2 * (e_sp0 E / 16)). lia. }
destruct (ec_chain_at ly (aview SEGS (w_H W) mem) (e_B E) (e_sp0 E) (raZ (e_regs E)) (s0Z (e_regs E))
  Sra S8 Hrng1 Hrng8 Hs0 Hra4E ltac:(lia) Hal8 ltac:(lia) ltac:(lia)) as (ch & HCH & _).
exists ch.
rewrite Esp, Es0, Era, E1.
split; [lia|]. split; [exact HA2|]. split; [lia|]. split; [lia|].
split; [apply (ret_ok_codeptr_v (PI := PA)); [lia | exact Hkr2]|].
split; [unfold kImgLo in Hilo; lia|].
split; [rewrite C5 in Hlow; lia|].
split; [rewrite (Eo 3%bv ltac:(l6f_regne)), R3; exact HgpE|].
split; [rewrite (Eo 4%bv ltac:(l6f_regne)), R4; exact HtpE|].
split; [exact HCH|].
split; [rewrite Eshi; lia|].
lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The image bytes across a call whose footprint does not open the sink: the musl stdio half and the read-only
      bytes are image bytes, not runtime-owned, not errno and not a ledger cell (ec_img's ei_sio / ei_pst_ro), so the
      callee's journal keeps them. *)
Lemma l2_imgkeep : forall (Rel : world SEGS -> world SEGS -> Prop) STK1 A FP1 ly S Hp (W : world SEGS) mem md ly2 S2
  Hp2 (W2 : world SEGS) mem2 md2 k1 WS1,
  ajournal_xwR (SK := SK) SEGS B PST ARc Rel STK1 A FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ~ YI16.sink_open_fp FP1 ->
  (forall a, EC_SIO_IMG a ->
     (~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
     in_img SEGS a /\ ~ Exists (in_zr a) PST) ->
  (forall rd rd' : reader, (forall a, EC_SIO_IMG a -> rd' a = rd a) -> EC_SIO rd -> EC_SIO rd') ->
  (forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a) ->
  EC_SIO (aview SEGS (w_H W) mem) -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  EC_SIO (aview SEGS (w_H W2) mem2) /\ arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
Proof.
intros Rel STK1 A FP1 ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HJ1 Hs0 Hsio Hsioframe Hpstro HSIO HRO.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
assert (FS : forall a, fp_spares FP1 a) by (intros a; apply fp_spares_closed; exact Hs0).
split.
- apply (Hsioframe (aview SEGS (w_H W) mem)); [|exact HSIO].
  intros a Ha. destruct (Hsio a Ha) as ((Hn1 & Hn2) & Hi & Hp').
  exact (G3 a Hi Hn1 Hn2 Hp' (FS a)).
- intros a Hro Hn1 Hn2.
  assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hin & _ & Hr) | Hr];
      [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
  assert (Hp' : ~ Exists (in_zr a) PST) by (intros Hx; exact (Hpstro a Hx Hro)).
  rewrite (G3 a Hi Hn1 Hn2 Hp' (FS a)). exact (HRO a Hro Hn1 Hn2).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The state after an ACCESSOR call (fuzz_alloc_live / _count / _peak_reset: no block, no footprint, S, Hp and the
      blocks kept, the ledger at a new peak): ec_inv and ec_frame hold again, the journal being the composed one at
      the SAME wild budget WS (an accessor stores no wild trace: ec_journal_unbase). The accessors make no model event
      and keep S, so the room position (os_c, i_c) is kept as it is. *)
Lemma l2_rebuild : forall (E : ECX) fk ly S (W : world SEGS) mem md own peak cnt kj WS STK1 A
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 peak2 os_c i_c wk most own',
  EINV E fk ly S [] W mem md own [] peak cnt 0 kj os_c i_c wk -> ec_frame E fk W mem ->
  EJ E own ly S [] W mem md kj WS -> YCbqGwild.wbudget [] wk WS ->
  EJ E own ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS ->
  ajournal_xR (SK := SK) SEGS B PST ARc WLE' STK1 A [] ly S [] W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  A <= e_sp0 E - EC_SAVE ->
  (forall a, EC_SIO_IMG a ->
     (~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
     in_img SEGS a /\ ~ Exists (in_zr a) PST) ->
  (forall rd rd' : reader, (forall a, EC_SIO_IMG a -> rd' a = rd a) -> EC_SIO rd -> EC_SIO rd') ->
  (forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a) ->
  S2 = S -> Hp2 = [] -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 [] peak2 cnt SIZE_MAX 0 most own' ->
  (room_live_cf S -> room_live_cf S2) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  EINV E fk ly2 S2 Hp2 W2 mem2 md2 own [] peak2 cnt 0 (kj + k1) os_c i_c wk /\ ec_frame E fk W2 mem2.
Proof.
intros E fk ly S W mem md own peak cnt kj WS STK1 A ly2 S2 Hp2 W2 mem2 md2 k1 peak2 os_c i_c wk most own' HINV HFRM
  HJ Hwb HJ' HJ1 HA Hsio Hsioframe Hpstro HS2 HHp2 Hab HLED2 Hroom Hmn.
subst S2 Hp2.
destruct HINV as (_ & HOWN & HLED & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY & HPERM & HBYTES & HMN).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HfrE & _).
destruct (l2_keepR B PST WLE' E fk ly S [] W mem md own kj WS STK1 A [] ly2 S [] W2 mem2 md2 k1 [] HJ HfrE HOWN HFRM
  HJ1 HA ltac:(intros a Ha; destruct (inFP_nil a Ha))) as (HOWN2 & HFRM2).
destruct (l2_imgkeep WLE' STK1 A [] ly S [] W mem md ly2 S [] W2 mem2 md2 k1 [] HJ1
  ltac:(intros (r & Hr & _); destruct Hr) Hsio Hsioframe Hpstro HSIO HRO) as (HSIO2 & HRO2).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
split; [|exact HFRM2].
split; [exists WS; split; [exact HJ' | exact Hwb]|].
split; [exact HOWN2|]. split; [exists most, own'; exact HLED2|]. split; [exact HSIO2|].
split; [exact HRO2|].
split; [exact (Hroom HLIVE)|]. split; [exact HROOM|]. split; [exact HCNT|]. split; [exact HPRE|].
split; [rewrite Hab; exact HPAY|]. split; [rewrite Hab; exact HPERM|].
split; [|exact (Hmn HMN)].
intros i Hi. rewrite <- (HBYTES i Hi).
destruct HPAY as [Hn0 | Hin]; [lia|].
pose proof (req_size_pos (e_n E) ltac:(lia)) as (_ & Hrq).
apply (G2 (e_p E) (e_n E) i Hin); [rewrite Hab; exact Hin | lia | intros Hf; destruct (inFP_nil _ Hf)].
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE ACCESSOR TEXTS in one shape: no block, no footprint, S / Hp / the blocks kept, the room kept, the ledger at
      a new peak with its two #102 cells kept (most own); POST names what the text says of a0 and of the new peak. *)
Definition l2_acc_text (fy : YK11.FPState) (s : asym) (STKf : Z)
  (POST : list (Z * Z) -> Z -> Z -> bvmap 5 word -> Z -> Prop) : Prop :=
  forall ly S Hp (W : world SEGS) regs mem md ch Lam peak cnt fail ran most own,
  fpre B ARc STKf ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr SEGS W (cfg_at (fx := fy) SEGS (SIGMA s) regs mem md)
    (apost_base_x (fx := fy) (SK := SK) SEGS B PST ARc STKf [] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
        ((room_live_cf S -> room_live_cf S') /\
         (exists peak', POST Lam peak cnt regs' peak' /\
            prh_ledger B ly' S' Hp' W' mem' Lam peak' cnt fail ran most own) /\
         Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S) /\
        (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem'))).

Lemma l2_text_live : forall fy, @tfuzz_alloc_live_specX fy rc cp PI RL B_prog_listing PA B ARc SK ->
  l2_acc_text fy AS_fuzz_alloc_live STK_fuzz_alloc_live
    (fun Lam peak _ regs' peak' => getr regs' 10 = w64 (Ledger.lsum Lam) /\ peak' = peak).
Proof.
intros fy HT ly S Hp W regs mem md ch Lam peak cnt fail ran most own Hpre HL.
eapply SRr_mono; [exact (HT ly S Hp W regs mem md ch Lam peak cnt fail ran most own Hpre HL)|].
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & (HQ & Hmn)).
destruct HQ as (Hr & Ha0 & HHp & HS & Hab & HL').
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|].
split; [|exact Hmn].
split; [exact Hr|].
split; [exists peak; split; [split; [exact Ha0 | reflexivity] | exact HL']|].
split; [exact HHp|]. split; [exact HS | exact Hab].
Qed.

Lemma l2_text_count : forall fy, @tfuzz_alloc_count_specX fy rc cp PI RL B_prog_listing PA B ARc SK ->
  l2_acc_text fy AS_fuzz_alloc_count STK_fuzz_alloc_count
    (fun _ peak cnt regs' peak' => getr regs' 10 = w64 cnt /\ peak' = peak).
Proof.
intros fy HT ly S Hp W regs mem md ch Lam peak cnt fail ran most own Hpre HL.
eapply SRr_mono; [exact (HT ly S Hp W regs mem md ch Lam peak cnt fail ran most own Hpre HL)|].
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & (HQ & Hmn)).
destruct HQ as (Hr & Ha0 & HHp & HS & Hab & HL').
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|].
split; [|exact Hmn].
split; [exact Hr|].
split; [exists peak; split; [split; [exact Ha0 | reflexivity] | exact HL']|].
split; [exact HHp|]. split; [exact HS | exact Hab].
Qed.

Lemma l2_text_peak_reset : forall fy, @tfuzz_alloc_peak_reset_specX fy rc cp PI RL B_prog_listing PA B ARc SK ->
  l2_acc_text fy AS_fuzz_alloc_peak_reset STK_fuzz_alloc_peak_reset
    (fun Lam _ _ _ peak' => peak' = Ledger.lsum Lam).
Proof.
intros fy HT ly S Hp W regs mem md ch Lam peak cnt fail ran most own Hpre HL.
eapply SRr_mono; [exact (HT ly S Hp W regs mem md ch Lam peak cnt fail ran most own Hpre HL)|].
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & (HQ & Hmn)).
destruct HQ as (Hr & HHp & HS & Hab & HL').
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|].
split; [|exact Hmn].
split; [exact Hr|].
split; [exists (Ledger.lsum Lam); split; [reflexivity | exact HL']|].
split; [exact HHp|]. split; [exact HS | exact Hab].
Qed.

(* ec_inv across a stretch with NO call (a model materialization, and the spent budget grown to the next cut's): its
   journal by Ent102CutsB's shared ec_inv_wk_grow, every other conjunct as it is *)
Lemma l2_inv_grow : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk wk' X,
  (wk <= wk')%nat ->
  EINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  EINV E fk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) own Lam peak cnt ran k os_c i_c wk'.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk wk' X Hle ((WS & HJ & Hb) & R). split; [|exact R].
exact (ec_inv_wk_growR B SK WLE' (l6f_LAWS B) E own ly S Hp W mem md k WS wk wk' X HJ Hb Hle).
Qed.

(* a model materialization keeps ec_inv (l2_inv_grow at the same budget) *)
Lemma l2_inv_mat : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk X,
  EINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  EINV E fk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) own Lam peak cnt ran k os_c i_c wk.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk X.
exact (l2_inv_grow E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk wk X (Nat.le_refl wk)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. AN ACCESSOR CALL at the body's slot kc (`jal ra, s`), returning to kc + 4: the jal, the text by l2_call on the
      cut's journal taken to the plain journal by Ent102CutsB's shared ec_journal_rebase (an accessor stores no wild
      trace), the post's journal back at the SAME budget by ec_journal_unbase, and the state rebuilt by l2_rebuild. *)
Lemma l2_acc : forall fy s STKf POST kc (E : ECX) fk ly S (W : world SEGS) regs mem md own peak cnt kj os_c i_c wk
  (R : world SEGS -> config -> Prop),
  l2_acc_text fy s STKf POST ->
  0 <= STKf -> STKf + EC_SAVE + 16 <= LLVMF_STK ->
  0 <= kc -> kc + 4 < 2 ^ 40 -> kc mod 2 = 0 ->
  plookup (@pl_tpi _ PL_102_B) kc = Some (PCall s 1%bv) -> plookup (@pl_tpi _ PL_102_B) (kc + 4) <> None ->
  (forall a, EC_SIO_IMG a ->
     (~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
     in_img SEGS a /\ ~ Exists (in_zr a) PST) ->
  (forall rd rd' : reader, (forall a, EC_SIO_IMG a -> rd' a = rd a) -> EC_SIO rd -> EC_SIO rd') ->
  (forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a) ->
  EINV E fk ly S [] W mem md own [] peak cnt 0 kj os_c i_c wk -> ec_rk E fk regs -> ec_frame E fk W mem ->
  ec_most E W mem -> ec_own_is W mem 0 -> YK0o.frm_zero (@YK11.fp_csr fy) ->
  (forall (W2 : world SEGS) ly2 regs2 mem2 md2 k1 peak2, WLE' W W2 ->
     EINV E fk ly2 S [] W2 mem2 md2 own [] peak2 cnt 0 (kj + k1) os_c i_c wk -> ec_frame E fk W2 mem2 ->
     (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     POST [] peak cnt regs2 peak2 ->
     ec_most E W2 mem2 -> ec_own_is W2 mem2 0 ->
     SRrG SEGS WLE' W2 (mkCfg (@YK11.mkst fy regs2 (Z_to_bv 64 (BASE + (kc + 4))) mem2 (YK11.seg_rom SEGS)) md2) R) ->
  SRrG SEGS WLE' W (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 (BASE + kc)) mem (YK11.seg_rom SEGS)) md) R.
Proof.
intros fy s STKf POST kc E fk ly S W regs mem md own peak cnt kj os_c i_c wk R HT HS0 HS1 Hk0 Hk1 Hk2 Hpl Hpl4
  Hsio Hsioframe Hpstro HINV Hrk Hfrm Hmost Hownis Hfz HK.
apply YGcfRhLift.ra_rh_of_SRr.
apply (l6f_step_call (fx := fy) W regs mem md _ kc s 1%bv 1%bv ltac:(lia) Hpl eq_refl).
intros X. l2_ret.
pose proof HINV as ((WS0 & HJ0 & Hwb0) & _).
destruct (ec_inv_wk_growR B SK WLE' (l6f_LAWS B) E own ly S [] W mem md kj WS0 wk wk X HJ0 Hwb0 (Nat.le_refl wk))
  as (WSm & HJm & Hwbm).
pose proof (ec_journal_rebaseR B SK WLE' E own ly S [] W mem _ kj WSm HJm) as HJr.
pose proof (l2_inv_mat E fk ly S [] W mem md own [] peak cnt 0 kj os_c i_c wk X HINV) as HINVm.
pose proof HINV as (_ & _ & (most0 & own0 & HLED0) & _ & HRO & _ & _ & _ & HPRE & _).
(* the ledger's two #102 cells at the values the cut reads (CallB's shared ec_ledger_cells) *)
pose proof (ec_ledger_cells _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED0 Hmost Hownis) as HLED.
assert (Hk4 : (kc + 4) mod 2 = 0) by (rewrite Z.add_mod by lia; rewrite Hk2; reflexivity).
destruct (l2_site E fk ly S [] W regs mem (with_vm_backing (m_vm_lazy md) X md) own kj WSm (kc + 4) HJm HPRE Hrk Hfrm
  ltac:(lia) Hk4 Hpl4) as (ch & Hsp & Hal & HA & Hlo & Hret & Hra4 & Hrac & Hgp & Htp & Hch & Hhi & Hceil).
change (mkCfg (YK11.mkst (regupd regs 1%bv (Z_to_bv 64 (BASE + (kc + 4)))) (Z_to_bv 64 (SIGMA s)) mem
  (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md))
  with (cfg_at (fx := fy) SEGS (SIGMA s) (regupd regs 1%bv (Z_to_bv 64 (BASE + (kc + 4)))) mem
    (with_vm_backing (m_vm_lazy md) X md)).
unfold EC_SAVE, LLVMF_STK in *.
eapply (l2_callR (fx := fy) (SK := SK) SEGS B PST ARc (l6f_LAWS B) pa_segs_low WLE' (wle'_trans SEGS _) W
  (regupd regs 1%bv (Z_to_bv 64 (BASE + (kc + 4)))) mem (with_vm_backing (m_vm_lazy md) X md)
  LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E) own ly S [] kj
  STKf [] (e_B E - e_sp0 E) ch (SIGMA s) _ R HJr Hsp Hal ltac:(lia) HS0 ltac:(unfold LLVMF_STK; lia) Hret Hra4 Hgp Htp
  Hch).
- intros Hpre. apply (l2_lift_call (fx := fy) (SK := SK) SEGS B PST ARc WLE' (wle_wle' SEGS _)).
  eapply HT; [|exact HLED].
  split; [exact Hpre|]. split; [exact HRO|]. split; [exact Hhi|]. split; [exact Hrac | exact Hfz].
- intros a Ha. destruct (inFP_nil a Ha).
- intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HJr' HJ1 HP ((Hr & (peak2 & HPOST & HL2) & HHp2 & HS2 & Hab) & Hmn).
  pose proof (ec_journal_unbaseR B SK WLE' E own ly S [] W mem _ kj WSm ly2 S2 Hp2 W2 mem2 md2 (kj + k1) own HJm HJr')
    as HJ'.
  subst Hp2 S2.
  rewrite (l2_getr_upd_same regs 1%bv _ eq_refl).
  destruct (l2_rebuild E fk ly S W mem (with_vm_backing (m_vm_lazy md) X md) own peak cnt kj WSm STKf
    (e_sp0 E + (e_B E - e_sp0 E)) ly2 S [] W2 mem2 md2 k1 peak2 os_c i_c wk (PJ_ALLOC_BOUND (e_n E)) 0 HINVm Hfrm
    HJm Hwbm HJ' HJ1 ltac:(unfold EC_SAVE; lia) Hsio Hsioframe Hpstro eq_refl eq_refl Hab HL2 Hr Hmn)
    as (HINV2 & HFRM2).
  apply (HK W2 ly2 regs2 mem2 md2 k1 peak2 Hle HINV2 HFRM2); [| exact HPOST |
    exact (PRH_Base.prh_ledger_most _ _ _ _ _ _ _ _ _ _ _ _ _ HL2) | exact (PRH_Base.prh_ledger_own _ _ _ _ _ _ _ _ _ _ _ _ _ HL2)].
  intros r Hr'. rewrite (HP r Hr'). apply l2_getr_upd_other. exact (l2_cs_ne1 r Hr').
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. THE STATE AT parse_noting's RETURN SITE (+0x178) is cut_pno: from the call's two journals, the frame keep, the
      image keep, the text's post (the reading, the ledger, the doc, THE BUILT TREE'S FREE ORDER) and the step-2 -> 3
      pay of ec_pay. ec_pjf is SUPPLIED here (rebind-plan "ec_pjf: LL2 supplies"): the kit's free-order conjunct of the
      Some arm under ei_head (cf_head = HEAD), with its list at the reading's own outcomes ok moved to [] by the kit's
      bridge PRH_FnPj.prhPj_frees_acc (= PresetFreeFo.pj_frees_acc, an accepted reading) and e_sm E = jr_strtod
      (ec_pre). *)
Lemma l2_pno_post : forall (E : ECX) fk ly S (W : world SEGS) mem md own cnt kj (fy fx' : YK11.FPState)
  regs (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 k1 STK1 A Lam' peak' cnt' ran' ok res tr (trp : ec_trip) most own0
  WS0 WS1,
  (forall a, EC_SIO_IMG a ->
     (~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
     in_img SEGS a /\ ~ Exists (in_zr a) PST) ->
  (forall rd rd' : reader, (forall a, EC_SIO_IMG a -> rd' a = rd a) -> EC_SIO rd -> EC_SIO rd') ->
  (forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a) ->
  Z.of_nat (calls tr) + ec_ccut E 3 <= ec_ccut E 2 ->
  ReaderRes.hpeak tr + cf_head * ReaderRes.nlive tr + ec_lcut E 3 <= ec_lcut E 2 ->
  ec_lcut E 3 <= ec_lcut E 2 -> 0 <= ec_ccut E 3 ->
  cnt + ck_ncalls (e_x E) <= SIZE_MAX ->
  fregs_kept_x fx fy -> YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fy fx' -> cf_head = PresetReqAt.HEAD ->
  EINV E fk ly S [] W mem md own [] 0 cnt 0 kj (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp))%nat
    ec_wk_cno ->
  EJ E own ly S [] W mem md kj WS0 -> YCbqGwild.wbudget [] ec_wk_cno WS0 ->
  ec_ranout E trp = false ->
  cnt + ec_ccut E 2 <= e_cnt E + LCNT -> blocks_bytes S + ec_lcut E 2 <= LIVE_MAX ->
  ec_rkd E fk regs -> ec_frame E fk W mem -> e_n E <= EC_NMAX ->
  getr regs 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)) -> getr regs 22 = w64 0 -> getr regs 23 = w64 cnt ->
  ec_most E W mem -> ec_own_is W mem 0 ->
  EJ E own ly2 S2 Hp2 W2 mem2 md2 (kj + k1) (WS0 ++ WS1) -> YCbqGwild.wbudget [] (prh_wk F_parse_noting) WS1 ->
  ajournal_xwR (SK := SK) SEGS B PST ARc WLE' STK1 A [(ec_doc fk, ec_doc fk + 56)] ly S [] W mem md []
    ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  A <= e_sp0 E - EC_SAVE ->
  (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  ec_most E W2 mem2 -> ec_own_is W2 mem2 0 ->
  room_live_cf S2 ->
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
     (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E))%nat (e_H0 E) hist S2) ->
  jr_run ReaderRes.jr_strtod (e_x E) ok = (res, tr) ->
  cnt' = cnt + Z.of_nat (calls tr) ->
  peak' = Z.max 0 (Ledger.lsum [] + ReaderRes.hpeak tr) ->
  ReaderRes.hpeak tr <= 224 * Z.of_nat (length (e_x E)) + 16384 ->
  ran' = 0 ->
  (ran' = 0 -> SIZE_MAX < cnt \/ cnt + ck_ncalls (e_x E) <= SIZE_MAX ->
     res = ck_read (e_x E) /\ Z.of_nat (calls tr) = ck_ncalls (e_x E)) ->
  bytes_at W2 mem2 (e_p E) (e_x E) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' SIZE_MAX ran' most own0 ->
  match res with
  | Some t => getr regs2 10 = w64 0 /\ exists D, Permutation Lam' (D ++ []) /\
      Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr /\
      (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) D)
         (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod ok (e_x E)))) /\
      (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
         exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') n (ec_doc fk) D F /\
           map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok (e_x E)) /\
      (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
      Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks D) /\
      pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam') (ec_doc fk) t D
  | None => getr regs2 10 = w64 (-1) /\ Permutation Lam' [] /\ Permutation (ablocks B ly2 S2) (ablocks B ly S) /\
      pj_zeroR SEGS (mrestrict (w_H W2) mem2) (ec_doc fk)
  end ->
  @cut_pno fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO ec_ccut ec_lcut E fk W2
    (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + 376)) mem2 (YK11.seg_rom SEGS)) md2).
Proof.
intros E fk ly S W mem md own cnt kj fy fx' regs W2 ly2 S2 Hp2 regs2 mem2 md2 k1 STK1 A Lam' peak' cnt' ran' ok res tr trp
  most own0 WS0 WS1
  Hsio Hsioframe Hpstro Hpc Hpl Hlc32 Hcc3 Hnc Hkept Hfz' Hkept' Hhead HINV HJ Hwb0 Hro HCC HLIV Hrkd Hfrm HnMAX R25
  R22 R23 Hmost Hownis HJ' HPW HJ1 HA HP Hmn Hmost2 Hown2 Hlive2 Hroom2 Hjr Hcnt' Hpk Hhp Hr1 Hr0 Hby HL' Hres.
subst ran'.
destruct HINV as (_ & HOWN & HLED & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY & HPERM & HBYTES & HMN).
assert (HWB : YCbqGwild.wbudget [] ec_wk_pno (WS0 ++ WS1)) by exact (YCbqGwild.wbudget_app [] _ _ _ _ Hwb0 HPW).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & HNC & Hnlen & Hgarr & HfrE & _).
assert (Hsm : e_sm E = ReaderRes.jr_strtod) by l2_pre HPRE.
destruct Hrkd as (Hrk & R21).
assert (Hlx : Z.of_nat (length (e_x E)) = e_n E) by (unfold e_x, ec_bytes; rewrite length_map; symmetry; exact Hnlen).
pose proof HOWN as (pos & Hown & Hfkeq & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, HfrE, Hown; left; reflexivity).
destruct HAR as (HARcf & _).
destruct (l6f_geom B ly S [] W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh).
destruct (l2_keepR B PST WLE' E fk ly S [] W mem md own kj WS0 STK1 A [(ec_doc fk, ec_doc fk + 56)] ly2 S2 Hp2 W2 mem2
  md2 k1 WS1 HJ HfrE HOWN Hfrm HJ1 HA) as (HOWN2 & HFRM2).
{ intros a Ha. apply (proj1 (inFP_cons _ _ _ _)) in Ha. destruct Ha as [Ha | Ha].
  - unfold ec_doc, EC_FRAME_BYTES in *. lia.
  - destruct (inFP_nil a Ha). }
destruct (l2_imgkeep WLE' STK1 A [(ec_doc fk, ec_doc fk + 56)] ly S [] W mem md ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HJ1
  ltac:(intros (r & Hr & H0); destruct Hr as [<-|[]]; unfold ec_doc in H0; cbn [fst snd] in H0; lia)
  Hsio Hsioframe Hpstro HSIO HRO) as (HSIO2 & HRO2).
assert (HBY2 : forall i, 0 <= i < e_n E ->
  aview SEGS (w_H W2) mem2 (e_p E + i) = aview SEGS (w_H (e_W E)) (e_mem E) (e_p E + i)).
{ intros i Hi. apply (l2_garr8_eq (w_H (e_W E)) (w_H W2) (e_mem E) mem2 (e_p E) (e_x E) Hgarr Hby). lia. }
assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr regs 21) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23 = getr regs 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr regs 25) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27 = getr regs 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
assert (HRK2 : ec_rkd E fk regs2).
{ destruct Hrk as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q26 & Q27).
  split; [|rewrite P21; exact R21].
  split; [rewrite P2; exact Q2|]. split; [rewrite P3; exact Q3|]. split; [rewrite P4; exact Q4|].
  split; [rewrite P8; exact Q8|]. split; [rewrite P9; exact Q9|]. split; [rewrite P18; exact Q18|].
  split; [rewrite P19; exact Q19|]. split; [rewrite P20; exact Q20|]. split; [rewrite P26; exact Q26|].
  rewrite P27; exact Q27. }
assert (HC' : cnt' + ec_ccut E 3 <= e_cnt E + LCNT) by lia.
assert (HCNT' : e_cnt E <= cnt' <= e_cnt E + LCNT) by lia.
assert (HKEPT : fregs_kept_x fx fx') by (intros r Hr; rewrite (Hkept' r Hr); exact (Hkept r Hr)).
assert (HPK : peak' <= PJ_ALLOC_BOUND (e_n E)).
{ rewrite Hpk. cbn [Ledger.lsum]. unfold PJ_ALLOC_BOUND. rewrite <- Hlx. lia. }
unfold cut_pno.
destruct res as [t|].
- destruct Hres as (Ha0 & D & HLD & HDs & HDn & _ & HFO & _ & HabD & Hnode).
  rewrite app_nil_r in HLD.
  pose proof (ReaderRes.lsz_counts D tr HDs HDn) as Hheld.
  pose proof (l2_held_hpeak tr) as Hhh.
  assert (HBB : blocks_bytes S2 = blocks_bytes S + Ledger.lsum D + cf_head * ReaderRes.nlive tr).
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HabD), bsum_app, <- (blocks_bytes_bsum B ly S).
    rewrite l2_bsum_hblks, HDn. lia. }
  exists ly2, S2, Hp2, regs2, mem2, md2, own, Lam', peak', cnt, cnt', (kj + k1), ok, (Some t), tr, D, trp.
  split; [exists fx'; split; [exact Hfz'|]; split; [exact HKEPT | reflexivity]|].
  split.
  { split; [exists (WS0 ++ WS1); split; [exact HJ' | exact HWB]|].
    split; [exact HOWN2|]. split; [exists most, own0; exact HL'|]. split; [exact HSIO2|].
    split; [exact HRO2|]. split; [exact Hlive2|]. split; [exact Hroom2|]. split; [exact HCNT'|].
    split; [exact HPRE|].
    split; [destruct HPAY as [Hn0|Hin0]; [left; exact Hn0|];
            right; apply (Permutation_in _ (Permutation_sym HabD)); apply in_or_app; left; exact Hin0|].
    split; [|split; [exact HBY2 | exact (Hmn HMN)]].
    eapply Permutation_trans; [exact HabD|].
    eapply Permutation_trans; [apply Permutation_app_comm|].
    apply Permutation_app; [unfold ck_hblks; apply Permutation_map; apply Permutation_sym; exact HLD | exact HPERM]. }
  split; [exact Hro|]. split; [exact HC'|]. split; [rewrite P25; exact R25|].
  split; [rewrite HBB; lia|].
  split; [exact HRK2|]. split; [exact HFRM2|]. split; [exact HnMAX|].
  split; [rewrite P22; exact R22|]. split; [rewrite P23; exact R23|].
  split; [exact Hcnt'|].
  split; [split; [exact Hjr | split; [exact HDs | exact HDn]]|].
  split; [split; [exact HLD | exact Hnode]|].
  split.
  { (* ec_pjf: the kit's free order at the reading's outcomes ok, moved to [] (accepted reading) *)
    intros n Hn. destruct (HFO Hhead n Hn) as (F & HF & HFl). exists F. split; [exact HF|].
    rewrite HFl, Hsm. exact (PRH_FnPj.prhPj_frees_acc ReaderRes.jr_strtod (e_x E) ok t tr Hjr). }
  split; [exact Ha0|]. split; [exact HPK|].
  split; [apply Hr0; [reflexivity | right; exact Hnc]|].
  split; [exact Hmost2 | exact Hown2].
- destruct Hres as (Ha0 & HLP & HabN & Hzero).
  assert (HL0 : Lam' = []) by exact (Permutation_nil (Permutation_sym HLP)).
  subst Lam'.
  assert (HBB : blocks_bytes S2 = blocks_bytes S).
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HabN), <- (blocks_bytes_bsum B ly S). reflexivity. }
  exists ly2, S2, Hp2, regs2, mem2, md2, own, [], peak', cnt, cnt', (kj + k1), ok, None, tr, [], trp.
  split; [exists fx'; split; [exact Hfz'|]; split; [exact HKEPT | reflexivity]|].
  split.
  { split; [exists (WS0 ++ WS1); split; [exact HJ' | exact HWB]|].
    split; [exact HOWN2|]. split; [exists most, own0; exact HL'|]. split; [exact HSIO2|].
    split; [exact HRO2|]. split; [exact Hlive2|]. split; [exact Hroom2|]. split; [exact HCNT'|].
    split; [exact HPRE|].
    split; [destruct HPAY as [Hn0|Hin0]; [left; exact Hn0|];
            right; apply (Permutation_in _ (Permutation_sym HabN)); exact Hin0|].
    split; [|split; [exact HBY2 | exact (Hmn HMN)]].
    eapply Permutation_trans; [exact HabN | exact HPERM]. }
  split; [exact Hro|]. split; [exact HC'|]. split; [rewrite P25; exact R25|].
  split; [rewrite HBB; lia|].
  split; [exact HRK2|]. split; [exact HFRM2|]. split; [exact HnMAX|].
  split; [rewrite P22; exact R22|]. split; [rewrite P23; exact R23|].
  split; [exact Hcnt'|].
  split; [split; [exact Hjr | exact I]|].
  split; [split; [reflexivity | split; [reflexivity | exact Hzero]]|].
  split; [exact I|].
  split; [exact Ha0|]. split; [exact HPK|].
  split; [apply Hr0; [reflexivity | right; exact Hnc]|].
  split; [exact Hmost2 | exact Hown2].
Qed.

(* ---------------------------------------------------------------------- *)
(* 7. THE CALL OF parse_noting (+0x174 `jal parse_noting`, a0 = p, a1 = n, a2 = &doc): its batch-kit text in the granted
      entry-keyed form (Ent102GrantA's tparse_noting_grantedX, DERIVED from ec_texts' et_parse_noting by Ent102OfPost's
      tparse_noting_grantedX_of_post in l2_arm0; no hypothesis) at the call, with every premise discharged from the
      state (the payload's src_rd / home at n > 0 by Ent102CallB.v's ec_src_home_cut, at n = 0 the empty payload by
      ec_img's ei_empty; the live and request premises by ecov_pno and ei_malloc_max; the count headroom by ec_pre; the
      run premise by l2_run_pn from the r = 0 arm equation; the consumer window by l2_win_pn; the pick condition from
      the count headroom at g_fail_at = SIZE_MAX; the wild room by Ent102CutsB.ec_room_at at the cut's spent budget
      ec_wk_cno), composed by l2_callbF (the budget adds: ec_wk_cno + prh_wk F_parse_noting = ec_wk_pno), then
      l2_pno_post at the return site. *)
Lemma l2_pno : forall (fy : YK11.FPState) (E : ECX) fk ly S (W : world SEGS) regs mem md own cnt kj
  (trp : ec_trip),
  Ent102GrantA.tparse_noting_grantedX (fx := fy) (rc := rc) (ci := ci) (cp := cp) (PI := PI) (RL := RL)
    (L := B_prog_listing) (PA := PA) B ARc SK (ec_ctx0 EC_RA) ->
  ec_ranout E trp = false ->
  @prh_univ_closure PI B ci (ec_ctx0 EC_RA) ->
  0 <= STK_parse_noting -> STK_parse_noting + EC_SAVE + 16 <= LLVMF_STK ->
  (forall a, EC_SIO_IMG a ->
     (~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
     in_img SEGS a /\ ~ Exists (in_zr a) PST) ->
  (forall rd rd' : reader, (forall a, EC_SIO_IMG a -> rd' a = rd a) -> EC_SIO rd -> EC_SIO rd') ->
  (forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a) ->
  (YImgTop.IMG_LO_B + 64 <= EC_EMPTY /\ EC_EMPTY + 64 <= YImgTop.IMG_TOP_B) /\
  (@pa_lo rc B_prog_listing PA + 64 <= EC_EMPTY /\ EC_EMPTY + 64 <= @pa_hi rc B_prog_listing PA) ->
  PRH_FnWriter.prhWriter_WMAX + cf_head < cf_malloc_max -> cf_head = PresetReqAt.HEAD ->
  (forall ok res tr, jr_run ReaderRes.jr_strtod (e_x E) ok = (res, tr) ->
     Z.of_nat (calls tr) + ec_ccut E 3 <= ec_ccut E 2 /\
     ReaderRes.hpeak tr + cf_head * ReaderRes.nlive tr + ec_lcut E 3 <= ec_lcut E 2) ->
  PRH_FnPj.LIVE_pj_parse (e_x E) <= ec_lcut E 2 ->
  ec_lcut E 3 <= ec_lcut E 2 -> 0 <= ec_ccut E 3 ->
  YK0o.frm_zero (@YK11.fp_csr fy) -> fregs_kept_x fx fy ->
  EINV E fk ly S [] W mem md own [] 0 cnt 0 kj (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp))%nat
    ec_wk_cno ->
  cnt + ec_ccut E 2 <= e_cnt E + LCNT -> blocks_bytes S + ec_lcut E 2 <= LIVE_MAX ->
  ec_rkd E fk regs -> ec_frame E fk W mem -> e_n E <= EC_NMAX ->
  getr regs 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)) -> getr regs 22 = w64 0 -> getr regs 23 = w64 cnt ->
  getr regs 10 = w64 (e_p E) -> getr regs 11 = w64 (e_n E) -> getr regs 12 = w64 (ec_doc fk) ->
  ec_most E W mem -> ec_own_is W mem 0 ->
  (* THE HULL BUDGET of the reading's all-granted events (GrantA's text, its last premise): l2_arm0 pays it from the
     cut's position by ec_hyps' ech_hull_pay *)
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod (e_x E) []) ->
  SRrG SEGS WLE' W (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 (BASE + 372)) mem (YK11.seg_rom SEGS)) md)
    (@cut_pno fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO ec_ccut ec_lcut E fk).
Proof.
intros fy E fk ly S W regs mem md own cnt kj trp HT Hro HU HS0 HS1 Hsio Hsioframe Hpstro Hempty Hwmax HHD Hpay Hcov
  Hlc32 Hcc3 Hfz Hkept HINV HCC HLIV Hrkd Hfrm HnMAX R25 R22 R23 R10 R11 R12 Hmost Hownis Hhull.
assert (Hpl : plookup (@pl_tpi _ PL_102_B) 372 = Some (PCall AS_parse_noting 1%bv)) by (vm_compute; reflexivity).
assert (Hpl4 : plookup (@pl_tpi _ PL_102_B) 376 <> None) by (vm_compute; discriminate).
apply YGcfRhLift.ra_rh_of_SRr.
apply (l6f_step_call (fx := fy) W regs mem md _ 372 AS_parse_noting 1%bv 1%bv ltac:(lia) Hpl eq_refl).
intros X. l2_ret.
pose proof HINV as HINV0.
pose proof HINV as ((WS0 & HJ0 & Hwb0) & _).
destruct (ec_inv_wk_growR B SK WLE' (l6f_LAWS B) E own ly S [] W mem md kj WS0 ec_wk_cno ec_wk_cno X HJ0 Hwb0
  (Nat.le_refl _)) as (WSm & HJm & Hwbm).
pose proof (l2_inv_mat E fk ly S [] W mem md own [] 0 cnt 0 kj _ _ _ X HINV) as HINVm.
destruct HINV as (_ & HOWN & (most0 & own0 & HLED) & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY & HPERM & HBYTES &
  HMN).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & HNC & Hnlen & Hgarr & HfrE & _ & _ & Hi0 & _).
assert (Hsm : e_sm E = ReaderRes.jr_strtod) by l2_pre HPRE.
assert (Hhead : e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30) by l2_pre HPRE.
pose proof Hrkd as (Hrk & R21).
pose proof Hfrm as (_ & Hshv & _).
destruct (l2_site E fk ly S [] W regs mem (with_vm_backing (m_vm_lazy md) X md) own kj WSm 376 HJm HPRE Hrk Hfrm
  ltac:(lia) eq_refl Hpl4) as (ch & Hsp & Hal & HA & Hlo & Hret & Hra4 & Hrac & Hgp & Htp & Hch & Hhi & Hceil).
pose proof HOWN as (pos & Hown & Hfkeq & _).
pose proof HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, HfrE, Hown; left; reflexivity).
destruct HAR as (HARcf & _).
destruct (l6f_geom B ly S [] W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh).
assert (HFB : fs_frame_bytes LLVMF_FS_CLASS = 128) by (vm_compute; reflexivity).
assert (Hlx : Z.of_nat (length (e_x E)) = e_n E) by (unfold e_x, ec_bytes; rewrite length_map; symmetry; exact Hnlen).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E10 : getr (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) 10 = w64 (e_p E))
  by (rewrite l2_getr_upd_other by l6f_regne; exact R10).
assert (E11 : getr (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) 11 = w64 (Z.of_nat (length (e_x E))))
  by (rewrite l2_getr_upd_other by l6f_regne; rewrite Hlx; exact R11).
assert (E12 : getr (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) 12 = w64 (ec_doc fk))
  by (rewrite l2_getr_upd_other by l6f_regne; exact R12).
(* the payload: its bytes, range and home *)
assert (PSH : src_rd W mem (e_p E) (e_x E) /\
  PRH_FnReader.prhReader_home B ly S [] [] (e_p E) (Z.of_nat (length (e_x E)))).
{ destruct (Z_lt_le_dec 0 (e_n E)) as [Hn0 | Hn0].
  - rewrite Hlx.
    exact (ec_src_home_cutR B SK EC_RA EC_EMPTY EC_SIO WLE' E fk ly S [] W mem md own [] 0 cnt 0 kj _ _ _ HINV0 Hn0).
  - destruct HNC as [(Hn & Hp0) | (Hn & _)]; [|lia].
    destruct (e_x E) as [|b x'] eqn:Ex; [|cbn [length] in Hlx; lia].
    rewrite Hp0. destruct Hempty as ((He1 & He2) & (Hq1 & Hq2)). unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in He1, He2.
    cbn [length Z.of_nat].
    split.
    + unfold src_rd, bytes_at. cbn [length Z.of_nat].
      split; [apply garr8_nil|]. split; [lia|]. split; [lia|].
      split; [left; unfold kLowMemEnd; lia|]. split; [apply range_addressable_nil; lia | intros H0; lia].
    + left. right; right. unfold kept_img. cbn [Z.of_nat]. split; [lia|]. split; [lia|].
      intros a Ha; lia. }
destruct PSH as (Psrc & Phome).
assert (Ppos : 0 < e_p E /\ e_p E + Z.of_nat (length (e_x E)) < 2 ^ 62).
{ destruct Psrc as (_ & P4096 & P8 & _). split; lia. }
assert (Pmaxrun : Z.of_nat (PjRoundTrip.maxrun (e_x E)) < 2 ^ 30).
{ pose proof (PjRoundTrip.G12_1 (e_x E)). unfold EC_NMAX in HnMAX. lia. }
assert (Pdoc8 : ec_doc fk mod 8 = 0).
{ unfold ec_doc. pose proof (proj1 (Z.mod_divide _ 32 ltac:(lia)) Gal) as (q & Hq). rewrite Hq.
  replace (q * 32 + 32) with ((4 * q + 4) * 8) by lia. apply Z_mod_mult. }
assert (Pout : ck_out_ok B STK_parse_noting ly S W (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) mem (ec_doc fk) 56).
{ split.
  - exists LLVMF_FS_CLASS, pos. split; [exact Hin|]. rewrite <- Hfkeq, HFB. unfold ec_doc. lia.
  - destruct (l2_doc_shadow (w_H W) mem fk Gal ltac:(lia) Hshv) as (Hra & Hhv).
    { intros i Hi. destruct (Gsh i ltac:(change (EC_FRAME_BYTES / 8) with 16; lia)) as (Hp & _). exact Hp. }
    unfold wdest_ok, ec_doc. unfold EC_FRAME_BYTES in Gceil, Gapp, Gfr.
    split; [lia|]. split; [lia|].
    split; [destruct Gapp as (_ & [Hlow | (Hhigh & Hc)]); [left | right; split];
            unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
    split; [|split; [exact Hra | intros _; exact Hhv]].
    intros a Ha. destruct (Gfr a ltac:(lia)) as (Gp & Go & _).
    split; [apply (YCbq.apresent_writable SEGS); exact Gp|]. split; [exact Go|].
    rewrite Hsp. unfold LLVMF_STK, EC_SAVE in *. lia. }
assert (Pcnt : cnt + 2 * Z.of_nat (length (e_x E)) + 2 < 2 ^ 64 - 1).
{ rewrite Hlx. unfold EC_NMAX in HnMAX. unfold LCNT in *. lia. }
assert (Plive : blocks_bytes S + PRH_FnPj.LIVE_pj_parse (e_x E) <= LIVE_MAX) by lia.
assert (Prq : PRH_FnPj.RQ_pj_parse (e_x E) + cf_head < cf_malloc_max).
{ pose proof (PjReqBoundW.rq_read_bound_56 prh_jr_strtod (e_x E)) as Hrq.
  change (PRH_FnPj.RQ_pj_parse (e_x E)) with (PjReqBoundW.rq_read prh_jr_strtod (e_x E)).
  unfold PRH_FnWriter.prhWriter_WMAX in Hwmax. unfold EC_NMAX in HnMAX. lia. }
assert (Pframes : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_parse_noting).
{ rewrite Hfrs, HfrE, Hown. cbn [app length]. apply Z.leb_le. vm_compute. reflexivity. }
(* the ledger's two #102 cells at the values the cut reads (CallB's shared ec_ledger_cells), and every reading
   request within g_most (PjReqBoundW.rq_read_bound) *)
pose proof (ec_ledger_cells _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED Hmost Hownis) as HLEDm.
assert (Prm : PRH_FnPj.RQ_pj_parse (e_x E) <= PJ_ALLOC_BOUND (e_n E)).
{ pose proof (PjReqBoundW.rq_read_bound prh_jr_strtod (e_x E)) as Hrq.
  change (PRH_FnPj.RQ_pj_parse (e_x E)) with (PjReqBoundW.rq_read prh_jr_strtod (e_x E)).
  unfold PJ_ALLOC_BOUND. rewrite <- Hlx. lia. }
destruct HROOM as (hist & Hrp).
pose proof (Ent102PosB.ec_call_evs_ranout_false _ _ _ E trp (l2_maxb E HPRE HnMAX) Hro) as Htie.
pose proof (l2_run_pn E trp Hi0 Htie) as Hrun.
pose proof (l2_win_pn E trp Hi0 (l2_maxb E HPRE HnMAX) Hro) as Hwin.
(* the count headroom of the reading (ec_pay's step 2 -> 3 at the all-granted run, under ec_pre's LCNT headroom):
   no injected failure (g_fail_at = SIZE_MAX) falls in its window - the text's pick condition *)
destruct (jr_run ReaderRes.jr_strtod (e_x E) []) as (r0 & t0) eqn:E0.
pose proof (proj1 (Hpay [] r0 t0 E0)) as Hp0.
assert (Hnc : cnt + ck_ncalls (e_x E) <= SIZE_MAX).
{ unfold ck_ncalls, ncalls. rewrite E0. cbn [snd]. unfold SIZE_MAX, LCNT in *. lia. }
(* the wild room of the call: the cut's spent budget ec_wk_cno plus parse_noting's prh_wk is ec_wk_pno, within
   K_LLVMF (ec_wk_values) *)
assert (Hwk : (ec_wk_cno + prh_wk F_parse_noting <= YCbqGwild.K_LLVMF)%nat).
{ change (ec_wk_cno + prh_wk F_parse_noting)%nat with ec_wk_pno.
  destruct ec_wk_values as (_ & Hp & _ & _ & _ & _ & _ & _ & _ & Hk). rewrite Hp, Hk. lia. }
pose proof (ec_room_atR B SK EC_RA EC_EMPTY EC_SIO WLE' E own ly S [] W mem md kj WS0 ec_wk_cno F_parse_noting HPRE HJ0
  Hwb0 Hwk) as Hwild.
change (mkCfg (YK11.mkst (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) (Z_to_bv 64 (SIGMA AS_parse_noting)) mem
  (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md))
  with (cfg_at (fx := fy) SEGS (SIGMA AS_parse_noting) (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) mem
    (with_vm_backing (m_vm_lazy md) X md)).
eapply (l2_callbFR (fx := fy) (SK := SK) SEGS B PST ARc (l6f_LAWS B) pa_segs_low WLE' (wle'_trans SEGS _) W
  (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) mem (with_vm_backing (m_vm_lazy md) X md)
  LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own ly S [] kj WSm STK_parse_noting
  [(ec_doc fk, ec_doc fk + 56)] (e_B E - e_sp0 E) ch (SIGMA AS_parse_noting) _ _ _ HJm Hsp Hal
  ltac:(unfold EC_SAVE in *; lia) HS0 ltac:(unfold LLVMF_STK, EC_SAVE in *; lia) Hret Hra4 Hgp Htp Hch).
- intros Hpre.
  exact (HT (e_sm E) (e_x E) (e_os E ++ [trp])
    (e_i0 E + length (ec_cno_evs E trp))%nat
    (e_H0 E) hist (PJ_ALLOC_BOUND (e_n E)) 0 ly S [] W (regupd regs 1%bv (Z_to_bv 64 (BASE + 376))) mem
    (with_vm_backing (m_vm_lazy md) X md) ch (e_p E) (e_x E) (ec_doc fk) [] 0 cnt SIZE_MAX 0 Hsm
    (conj Hpre (conj HRO (conj Hhi (conj Hrac Hfz)))) HMN HU E10 E11 E12
    ltac:(rewrite Hlx; unfold EC_NMAX in HnMAX; lia) (proj1 Ppos) (proj2 Ppos) Psrc Phome
    Pmaxrun Pdoc8 Pout
    eq_refl HLEDm Pcnt Plive Prq Prm Pframes Hfz HLIVE Hrp Hrun Hwin (or_intror Hnc) Hwild Hhull).
- intros a Ha. right; right; left. exists (LLVMF_FS_CLASS, pos). split; [rewrite Hown; left; reflexivity|].
  apply (proj1 (inFP_cons _ _ _ _)) in Ha. destruct Ha as [Ha | Ha]; [|destruct (inFP_nil a Ha)].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq, HFB. unfold ec_doc in Ha. lia.
- intros fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 WS1 Hle Hfz' Hkept' HPW HJ' HJ1 HP (HQ & Hmn).
  destruct HQ as (Hlive2 & Lam' & peak' & cnt' & fail' & ran' & ok & res & tr & Hadv &
    Hjr & Hoks & Hcnt' & Hfa & Hpk & Hhp & Hcf & Hran1 & Hran0 & Hbytes' & HL' & Hres).
  assert (Hf' : fail' = SIZE_MAX).
  { destruct Hfa as (F1 & F2). unfold SIZE_MAX in *.
    destruct (Z_lt_le_dec (2 ^ 64 - 1) (cnt + Z.of_nat (calls tr))) as [Hlt|Hge].
    - destruct (Z_le_gt_dec cnt (2 ^ 64 - 1)) as [Hle'|Hgt'].
      + apply F1. split; assumption.
      + rewrite F2 by lia. reflexivity.
    - rewrite F2 by lia. reflexivity. }
  subst fail'.
  rewrite (l2_getr_upd_same regs 1%bv _ eq_refl).
  destruct (Hpay ok res tr Hjr) as (Hpc & Hpl').
  (* the reading's outcomes are the all-granted ones (granted: ran' = 0; no injected failure: fail = SIZE_MAX beyond
     its calls; every request within g_most by l2_reqs_most), so the text's exact advance applies and the refusal
     peak is 0 *)
  destruct (Hran0 Hran1 (or_intror Hnc)) as (_ & Hcalls).
  assert (Hns : forall i, nth i (prh_ev_reqs tr) 0 <= PJ_ALLOC_BOUND (e_n E)).
  { intros i. pose proof (l2_reqs_most ReaderRes.jr_strtod (e_x E) ok i) as H. rewrite Hjr in H. cbn [snd] in H.
    rewrite Hlx in H. exact H. }
  pose proof (l2_agree ok cnt SIZE_MAX (calls tr) (prh_ev_reqs tr) (PJ_ALLOC_BOUND (e_n E)) ran' Hoks Hran1
    ltac:(rewrite Hcalls; exact Hnc) Hns) as HAG.
  destruct (Hadv HAG) as (rph & Hrp').
  assert (Hpk0 : peak' = Z.max 0 (Ledger.lsum [] + ReaderRes.hpeak tr)).
  { rewrite Hpk, (prh_refused_peak_granted ok cnt SIZE_MAX (calls tr) _ (l2_granted_of_agree _ _ _ _ HAG)).
    apply Z.max_l. lia. }
  apply (SRrG_ret SEGS _ (wle'_refl SEGS _)).
  apply (l2_pno_post E fk ly S W mem (with_vm_backing (m_vm_lazy md) X md) own cnt kj fy fx' regs W2 ly2 S2 Hp2
    regs2 mem2 md2 k1 STK_parse_noting (e_sp0 E + (e_B E - e_sp0 E)) Lam' peak' cnt' ran' ok res tr trp
    (PJ_ALLOC_BOUND (e_n E)) 0 WSm WS1
    Hsio Hsioframe Hpstro Hpc Hpl' Hlc32 Hcc3 Hnc Hkept Hfz' Hkept' HHD HINVm HJm Hwbm Hro HCC HLIV Hrkd Hfrm HnMAX R25
    R22 R23 Hmost Hownis HJ' HPW HJ1 ltac:(unfold EC_SAVE in *; lia)); [| exact Hmn |
    exact (PRH_Base.prh_ledger_most _ _ _ _ _ _ _ _ _ _ _ _ _ HL') |
    exact (PRH_Base.prh_ledger_own _ _ _ _ _ _ _ _ _ _ _ _ _ HL') | exact Hlive2 | |
    exact Hjr | exact Hcnt' | exact Hpk0 | exact Hhp | exact Hran1 | exact Hran0 | exact Hbytes' | exact HL' |
    exact Hres].
  + intros r Hr. rewrite (HP r Hr). apply l2_getr_upd_other. exact (l2_cs_ne1 r Hr).
  + exists rph. exact (l2_pos_pn E trp rph S2 Hrp').
Qed.

(* ---------------------------------------------------------------------- *)
(* 8. Small facts of the r = 0 arm: `mv rd, rs` (addi rd, rs, 0) copies, a write to a register the cut does not name
      keeps ec_rk, a call keeps it (all callee-saved), a model materialization keeps ec_inv, and the stack each callee
      of this body may ask is within LLVMF_STK below the callee's sp. *)
Lemma l2_addi0 : forall x : word, v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma l2_rk_upd : forall (E : ECX) fk regs (r : bv 5) v,
  (forall k : bv 5, In k [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 26%bv; 27%bv] -> k <> r) ->
  ec_rk E fk regs -> ec_rk E fk (regupd regs r v).
Proof.
intros E fk regs r v Hne (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q26 & Q27). unfold ec_rk.
rewrite !l2_getr_upd_other by (apply Hne; cbn; auto 20).
repeat split; assumption.
Qed.

Ltac l2_ne := intros ? Hk; repeat (destruct Hk as [<-|Hk]; [l6f_regne|]); destruct Hk.

Lemma l2_rk_pres : forall (E : ECX) fk regs regs2,
  (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  ec_rk E fk regs -> ec_rk E fk regs2.
Proof.
intros E fk regs regs2 HP (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q26 & Q27).
split; [transitivity (getr regs 2); [exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact Q2]|].
split; [transitivity (getr regs 3); [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact Q3]|].
split; [transitivity (getr regs 4); [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact Q4]|].
split; [transitivity (getr regs 8); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact Q8]|].
split; [transitivity (getr regs 9); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact Q9]|].
split; [transitivity (getr regs 18); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact Q18]|].
split; [transitivity (getr regs 19); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact Q19]|].
split; [transitivity (getr regs 20); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact Q20]|].
split; [transitivity (getr regs 26); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact Q26]|].
transitivity (getr regs 27); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact Q27].
Qed.

Lemma l2_stk : @STK_LLVMFuzzerTestOneInput PI <= LLVMF_STK ->
  EC_SAVE + 16 <= @pi_frame PI F_LLVMFuzzerTestOneInput ->
  forall X, In X [STK_RT_ECALL; STK_check_as_written; STK_check_bounded_alloc;
    STK_check_no_overread; STK_check_reject_clean; STK_check_reject_clean_starved; STK_check_round_trip;
    STK_fuzz_alloc_count; STK_fuzz_alloc_live; STK_fuzz_alloc_most; STK_fuzz_alloc_peak; STK_fuzz_alloc_peak_reset;
    STK_fuzz_alloc_ran_out; STK_fuzz_alloc_ran_out_reset; STK_parse_noting; STK_pj_free DOC_D; STK_read_members] ->
  X + EC_SAVE + 16 <= LLVMF_STK.
Proof.
intros Hs Hf X HX. pose proof (l6f_zmaxl_in X _ HX). unfold STK_LLVMFuzzerTestOneInput in Hs. lia.
Qed.

Ltac l2_in := repeat (first [left; reflexivity | right]).

(* one `addi rd, rs, imm` slot at offset k, with the decoder's own register terms identified with rd / rs by bv_eq
   (the decoded bit-vectors and the literals agree as values, not as terms: Ent102L6Af.v's form). The goal is at WLE':
   the step is opened by YGcfRhLift.ra_rh_of_SRr, and the caller closes it with l2_ret after `intros X` *)
Ltac l2_addi_step fy W regs mem md k rdl rsl immv v :=
  let Hpl := fresh "Hpl" in let Hd := fresh "Hd" in
  apply YGcfRhLift.ra_rh_of_SRr; l6f_fd k Hpl Hd;
  eapply (l6f_step_addi (fx := fy) W regs mem md _ k _ _ _ _ rdl v ltac:(lia) Hpl Hd);
  [ vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity
  | lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
      replace rs with rsl by (apply bv_eq; vm_compute; reflexivity);
      replace (bv_signed im) with immv by (vm_compute; reflexivity) end
  | ].

(* ---------------------------------------------------------------------- *)
(* 9. THE r = 0 ARM, +0x150 .. +0x174: `addi s5,s11,0x20`, fuzz_alloc_live / `mv s6,a0`, fuzz_alloc_count /
      `mv s7,a0`, fuzz_alloc_peak_reset, `mv a0,s4; mv a1,s3; mv a2,s5`, then parse_noting (l2_pno). *)
Lemma l2_arm0 : forall (fy : YK11.FPState) (E : ECX) fk ly S (W : world SEGS) regs mem md own peak cnt kj
  (trp : ec_trip),
  @ec_hyps rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut ->
  ec_ranout E trp = false ->
  YK0o.frm_zero (@YK11.fp_csr fy) -> fregs_kept_x fx fy ->
  EINV E fk ly S [] W mem md own [] peak cnt 0 kj (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp))%nat
    ec_wk_cno ->
  cnt + ec_ccut E 2 <= e_cnt E + LCNT -> getr regs 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)) ->
  blocks_bytes S + ec_lcut E 2 <= LIVE_MAX -> ec_rk E fk regs -> ec_frame E fk W mem -> e_n E <= EC_NMAX ->
  ec_most E W mem -> ec_own_is W mem 0 ->
  SRrG SEGS WLE' W (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 (BASE + 336)) mem (YK11.seg_rom SEGS)) md)
    (@cut_pno fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO ec_ccut ec_lcut E fk).
Proof.
intros fy E fk ly S W regs mem md own peak cnt kj trp HYP Hro Hfz Hkept HINV HCC R25 HLIV Hrk Hfrm HnMAX Hmost
  Hownis.
pose proof (ech_texts _ _ _ _ _ _ _ _ _ _ HYP) as HTX. pose proof (ech_img _ _ _ _ _ _ _ _ _ _ HYP) as HIMG.
pose proof (ech_univ _ _ _ _ _ _ _ _ _ _ HYP) as HUNIV.
pose proof (ech_ccut_ok _ _ _ _ _ _ _ _ _ _ HYP) as HCCOK.
pose proof (ech_lcut_ok _ _ _ _ _ _ _ _ _ _ HYP) as HLCOK. pose proof (ech_pay _ _ _ _ _ _ _ _ _ _ HYP) as HPAYR.
pose proof (ei_sio _ _ _ _ _ _ HIMG) as Hsio. pose proof (ei_sio_frame _ _ _ _ _ _ HIMG) as Hsioframe.
pose proof (ei_pst_ro _ _ _ _ _ _ HIMG) as Hpstro.
pose proof (l2_stk (et_stk _ _ _ _ _ HTX) (ei_frame _ _ _ _ _ _ HIMG)) as HSTK.
pose proof HINV as ((WS0 & HJ & _) & HOWN & HLED & _ & _ & _ & _ & HCNT & HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hnlen & _ & HfrE & _).
assert (Hlx : Z.of_nat (length (e_x E)) = e_n E) by (unfold e_x, ec_bytes; rewrite length_map; symmetry; exact Hnlen).
pose proof HOWN as (pos & Hown & Hfkeq & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, HfrE, Hown; left; reflexivity).
destruct HAR as (HARcf & _).
destruct (l6f_geom B ly S [] W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & _ & _).
pose proof YCbq.asan_consts as (C1 & _).
pose proof Hrk as (_ & _ & _ & _ & _ & _ & R19 & R20 & _ & R27).
(* THE HULL BUDGET of parse_noting's reading (route (b)): ec_hyps' ech_hull_pay at the cut's position (this call's
   triple after at most 3 earlier calls, ec_pre) and lib/A/PresetHullPay.v's bounds hull_nt_parse; S is the cut's,
   which the three accessors keep *)
pose proof HINV as (_ & _ & _ & _ & _ & _ & (histc & Hrpc) & _).
assert (Hos3 : (length (e_os E) <= 3)%nat) by l2_pre HPRE.
assert (Hhull : PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod (e_x E) [])).
{ destruct (PresetHullPay.hull_nt_parse ReaderRes.jr_strtod (e_x E) [] (l2_maxb E HPRE HnMAX)) as (HN & HT).
  refine (ech_hull_pay _ _ _ _ _ _ _ _ _ _ HYP (e_sm E) (e_x E) (e_os E ++ [trp]) _ (e_H0 E) histc S _ _ Hrpc HN HT).
  rewrite length_app. cbn [length]. lia. }
(* +0x150 addi s5,s11,0x20 *)
l2_addi_step fy W regs mem md 336 (21%bv : bv 5) (27%bv : bv 5) 32 (w64 (ec_doc fk)).
{ rewrite R27. unfold v_addi, ec_doc, w64. rewrite unsigned_lit_small by (unfold EC_FRAME_BYTES in Gceil; lia).
  reflexivity. }
intros X1. l2_ret.
set (regs1 := regupd regs 21%bv (w64 (ec_doc fk))).
assert (Hrk1 : ec_rk E fk regs1) by (apply l2_rk_upd; [l2_ne | exact Hrk]).
assert (R21a : getr regs1 21 = w64 (ec_doc fk)) by (apply l2_getr_upd_same; reflexivity).
assert (R25a : getr regs1 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)))
  by (unfold regs1; rewrite l2_getr_upd_other by l6f_regne; exact R25).
(* +0x154 jal fuzz_alloc_live *)
apply (l2_acc fy AS_fuzz_alloc_live STK_fuzz_alloc_live _ (336 + 4) E fk ly S W regs1 mem
  (with_vm_backing (m_vm_lazy md) X1 md) own peak cnt kj _ _ _ _
  (l2_text_live fy (et_fuzz_alloc_live _ _ _ _ _ HTX fy))
  ltac:(unfold STK_fuzz_alloc_live; apply pi_frame_nonneg) (HSTK STK_fuzz_alloc_live ltac:(l2_in)) ltac:(lia)
  ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hsio Hsioframe Hpstro
  (l2_inv_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HINV)
  Hrk1 Hfrm Hmost Hownis Hfz).
intros W2 ly2 regs2 mem2 md2 k2 peak2 Hle2 HINV2 Hfrm2 HP2 (Ha02 & Hpk2) Hmost2 Hown2.
pose proof (l2_rk_pres E fk regs1 regs2 HP2 Hrk1) as Hrk2.
assert (R21b : getr regs2 21 = w64 (ec_doc fk))
  by (transitivity (getr regs1 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21a]).
assert (R25b : getr regs2 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)))
  by (transitivity (getr regs1 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25a]).
(* +0x158 mv s6,a0 *)
l2_addi_step fy W2 regs2 mem2 md2 (336 + 4 + 4) (22%bv : bv 5) (10%bv : bv 5) 0 (getr regs2 10).
{ apply l2_addi0. }
intros X2. l2_ret.
set (regs3 := regupd regs2 22%bv (getr regs2 10)).
assert (Hrk3 : ec_rk E fk regs3) by (apply l2_rk_upd; [l2_ne | exact Hrk2]).
assert (R22c : getr regs3 22 = w64 0) by (unfold regs3; rewrite l2_getr_upd_same by reflexivity; exact Ha02).
assert (R21c : getr regs3 21 = w64 (ec_doc fk)) by (unfold regs3; rewrite l2_getr_upd_other by l6f_regne; exact R21b).
assert (R25c : getr regs3 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)))
  by (unfold regs3; rewrite l2_getr_upd_other by l6f_regne; exact R25b).
(* +0x15c jal fuzz_alloc_count *)
apply (l2_acc fy AS_fuzz_alloc_count STK_fuzz_alloc_count _ (336 + 4 + 4 + 4) E fk ly2 S W2 regs3 mem2
  (with_vm_backing (m_vm_lazy md2) X2 md2) own peak2 cnt (kj + k2) _ _ _ _
  (l2_text_count fy (et_fuzz_alloc_count _ _ _ _ _ HTX fy))
  ltac:(unfold STK_fuzz_alloc_count; apply pi_frame_nonneg) (HSTK STK_fuzz_alloc_count ltac:(l2_in)) ltac:(lia)
  ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hsio Hsioframe Hpstro
  (l2_inv_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HINV2) Hrk3 Hfrm2 Hmost2 Hown2 Hfz).
intros W4 ly4 regs4 mem4 md4 k4 peak4 Hle4 HINV4 Hfrm4 HP4 (Ha04 & Hpk4) Hmost4 Hown4.
pose proof (l2_rk_pres E fk regs3 regs4 HP4 Hrk3) as Hrk4.
assert (R21d : getr regs4 21 = w64 (ec_doc fk))
  by (transitivity (getr regs3 21); [exact (HP4 21 ltac:(unfold acallee_saved; lia)) | exact R21c]).
assert (R22d : getr regs4 22 = w64 0)
  by (transitivity (getr regs3 22); [exact (HP4 22 ltac:(unfold acallee_saved; lia)) | exact R22c]).
assert (R25d : getr regs4 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)))
  by (transitivity (getr regs3 25); [exact (HP4 25 ltac:(unfold acallee_saved; lia)) | exact R25c]).
(* +0x160 mv s7,a0 *)
l2_addi_step fy W4 regs4 mem4 md4 (336 + 4 + 4 + 4 + 4) (23%bv : bv 5) (10%bv : bv 5) 0 (getr regs4 10).
{ apply l2_addi0. }
intros X3. l2_ret.
set (regs5 := regupd regs4 23%bv (getr regs4 10)).
assert (Hrk5 : ec_rk E fk regs5) by (apply l2_rk_upd; [l2_ne | exact Hrk4]).
assert (R23e : getr regs5 23 = w64 cnt) by (unfold regs5; rewrite l2_getr_upd_same by reflexivity; exact Ha04).
assert (R22e : getr regs5 22 = w64 0) by (unfold regs5; rewrite l2_getr_upd_other by l6f_regne; exact R22d).
assert (R21e : getr regs5 21 = w64 (ec_doc fk)) by (unfold regs5; rewrite l2_getr_upd_other by l6f_regne; exact R21d).
assert (R25e : getr regs5 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)))
  by (unfold regs5; rewrite l2_getr_upd_other by l6f_regne; exact R25d).
(* +0x164 jal fuzz_alloc_peak_reset *)
apply (l2_acc fy AS_fuzz_alloc_peak_reset STK_fuzz_alloc_peak_reset _ (336 + 4 + 4 + 4 + 4 + 4) E fk ly4 S W4 regs5
  mem4 (with_vm_backing (m_vm_lazy md4) X3 md4) own peak4 cnt (kj + k2 + k4) _ _ _ _
  (l2_text_peak_reset fy (et_fuzz_alloc_peak_reset _ _ _ _ _ HTX fy))
  ltac:(unfold STK_fuzz_alloc_peak_reset; apply pi_frame_nonneg) (HSTK STK_fuzz_alloc_peak_reset ltac:(l2_in))
  ltac:(lia) ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hsio Hsioframe Hpstro
  (l2_inv_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HINV4) Hrk5 Hfrm4 Hmost4 Hown4 Hfz).
intros W6 ly6 regs6 mem6 md6 k6 peak6 Hle6 HINV6 Hfrm6 HP6 Hpk6 Hmost6 Hown6.
cbn [Ledger.lsum] in Hpk6. subst peak6.
pose proof (l2_rk_pres E fk regs5 regs6 HP6 Hrk5) as Hrk6.
assert (R21f : getr regs6 21 = w64 (ec_doc fk))
  by (transitivity (getr regs5 21); [exact (HP6 21 ltac:(unfold acallee_saved; lia)) | exact R21e]).
assert (R22f : getr regs6 22 = w64 0)
  by (transitivity (getr regs5 22); [exact (HP6 22 ltac:(unfold acallee_saved; lia)) | exact R22e]).
assert (R23f : getr regs6 23 = w64 cnt)
  by (transitivity (getr regs5 23); [exact (HP6 23 ltac:(unfold acallee_saved; lia)) | exact R23e]).
assert (R25f : getr regs6 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4)))
  by (transitivity (getr regs5 25); [exact (HP6 25 ltac:(unfold acallee_saved; lia)) | exact R25e]).
pose proof Hrk6 as (_ & _ & _ & _ & _ & _ & R19f & R20f & _).
(* +0x168 mv a0,s4; +0x16c mv a1,s3; +0x170 mv a2,s5 *)
l2_addi_step fy W6 regs6 mem6 md6 (336 + 4 + 4 + 4 + 4 + 4 + 4) (10%bv : bv 5) (20%bv : bv 5) 0 (getr regs6 20).
{ apply l2_addi0. }
intros X4. l2_ret.
set (regs7 := regupd regs6 10%bv (getr regs6 20)).
l2_addi_step fy W6 regs7 mem6 (with_vm_backing (m_vm_lazy md6) X4 md6) (336 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
  (11%bv : bv 5) (19%bv : bv 5) 0 (getr regs7 19).
{ apply l2_addi0. }
intros X5. l2_ret.
set (regs8 := regupd regs7 11%bv (getr regs7 19)).
l2_addi_step fy W6 regs8 mem6 (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md6) X4 md6)) X5
  (with_vm_backing (m_vm_lazy md6) X4 md6)) (336 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
  (12%bv : bv 5) (21%bv : bv 5) 0 (getr regs8 21).
{ apply l2_addi0. }
intros X6. l2_ret.
set (regs9 := regupd regs8 12%bv (getr regs8 21)).
assert (Hrk9 : ec_rk E fk regs9).
{ unfold regs9, regs8, regs7. apply l2_rk_upd; [l2_ne|]. apply l2_rk_upd; [l2_ne|]. apply l2_rk_upd; [l2_ne|].
  exact Hrk6. }
assert (G21 : getr regs9 21 = w64 (ec_doc fk)).
{ unfold regs9, regs8, regs7. rewrite !l2_getr_upd_other by l6f_regne. exact R21f. }
assert (G22 : getr regs9 22 = w64 0).
{ unfold regs9, regs8, regs7. rewrite !l2_getr_upd_other by l6f_regne. exact R22f. }
assert (G23 : getr regs9 23 = w64 cnt).
{ unfold regs9, regs8, regs7. rewrite !l2_getr_upd_other by l6f_regne. exact R23f. }
assert (G25 : getr regs9 25 = w64 (@pa_val rc B_prog_listing PA (A_HI 4))).
{ unfold regs9, regs8, regs7. rewrite !l2_getr_upd_other by l6f_regne. exact R25f. }
assert (G10 : getr regs9 10 = w64 (e_p E)).
{ unfold regs9, regs8, regs7. rewrite !l2_getr_upd_other by l6f_regne.
  rewrite l2_getr_upd_same by reflexivity. exact R20f. }
assert (G11 : getr regs9 11 = w64 (e_n E)).
{ unfold regs9, regs8, regs7. rewrite l2_getr_upd_other by l6f_regne. rewrite l2_getr_upd_same by reflexivity.
  rewrite l2_getr_upd_other by l6f_regne. exact R19f. }
assert (G12 : getr regs9 12 = w64 (ec_doc fk)).
{ unfold regs9, regs8, regs7. rewrite l2_getr_upd_same by reflexivity. rewrite !l2_getr_upd_other by l6f_regne.
  exact R21f. }
(* +0x174 jal parse_noting *)
assert (Hlen : Z.of_nat (length (e_x E)) <= EC_NMAX) by lia.
replace (336 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4) with 372 by reflexivity.
apply (l2_pno fy E fk ly6 S W6 regs9 mem6 _ own cnt (kj + k2 + k4 + k6) trp
  (Ent102OfPost.tparse_noting_grantedX_of_post (fx := fy) B ARc SK _ (et_parse_noting _ _ _ _ _ HTX fy)) Hro
  (eu_pno _ _ HUNIV) ltac:(unfold STK_parse_noting; pose proof (pi_frame_nonneg F_parse_noting);
                         pose proof (l6f_zmaxl_nonneg [STK_check_reject_clean; STK_fuzz_alloc_live;
                           STK_fuzz_alloc_ran_out; STK_pj_parse]); lia)
  (HSTK STK_parse_noting ltac:(l2_in)) Hsio Hsioframe Hpstro (ei_empty _ _ _ _ _ _ HIMG)
  (ei_malloc_max _ _ _ _ _ _ HIMG) (ei_head _ _ _ _ _ _ HIMG)
  (fun ok res tr Hr => epay_pno _ _ HPAYR E ok res tr Hlen Hr) (ecov_pno _ _ HPAYR E Hlen)
  (proj2 (HLCOK E 2%nat 3%nat) ltac:(lia)) (proj1 (proj1 (HCCOK E 3%nat 3%nat))) Hfz Hkept
  (l2_inv_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6 (l2_inv_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5
    (l2_inv_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HINV6)))
  HCC HLIV (conj Hrk9 G21) Hfrm6 HnMAX G25 G22 G23 G10 G11 G12
  Hmost6 Hown6 Hhull).
Qed.

(* the `bnez a0` slot's decoded registers are a0 / x0 as values; name them so the branch condition computes *)
Ltac l2_brv H :=
  lazymatch type of H with branch_taken _ (getr _ ?a) (getr _ ?b) = _ =>
    replace a with (10%bv : bv 5) in H by (apply bv_eq; vm_compute; reflexivity);
    replace b with (0%bv : bv 5) in H by (apply bv_eq; vm_compute; reflexivity) end.

(* a cut's ec_inv at another index of the same run, given the room position there *)
Lemma l2_inv_repos : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk i_c',
  EINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os_c i_c' (e_H0 E) hist S) ->
  EINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c' wk.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk i_c' (A1 & A2 & A3 & A4 & A5 & A6 & _ & A8) H.
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj H A8))))))).
Qed.

(* ---------------------------------------------------------------------- *)
(* 10. THE SEGMENT. cut_cno's tie gives the arm equation of the call's events on each arm of the `bnez a0`; the
       r = 1 arm raises the spent budget from ec_wk_cno to ec_wk_exit (ec_wk_values: 6 <= 76, nothing is called). *)
Theorem seg_L2_B :
  @seg_L2_stmt fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L2_stmt, ec_laneR.
intros E fk HYP W c Hcut.
pose proof (ech_ccut_ok _ _ _ _ _ _ _ _ _ _ HYP) as HCCOK. pose proof (ech_lcut_ok _ _ _ _ _ _ _ _ _ _ HYP) as HLCOK.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & peak & cnt & ran & k & r & trp & Hat & Hinv & HHp & Htie &
  HCC & H25 & HLIV & Hrk & Hfrm & HnMAX & Hmost & Ha0 & o & Hown_is & Hr).
subst Hp.
destruct Hat as (fy & Hfz & Hkept & Hc). subst c.
pose proof Hinv as (_ & _ & _ & _ & _ & _ & HROOM & _ & HPRE & _).
pose proof (l2_maxb E HPRE HnMAX) as Hlen.
unfold cfg_at. change (w64 EC_AR_CNO) with (Z_to_bv 64 (BASE + 332)).
l6f_fd 332 Hpl' Hd.
assert (G0 : getr regs 0%bv = Z_to_bv 64 0) by reflexivity.
apply (ec_step_branchR (fx := fy) WLE' W regs mem md _ 332 _ 452 _ _ _ _ ltac:(lia) ltac:(lia) Hpl' Hd
  ltac:(vm_compute; reflexivity)).
- (* taken: r = 1, EXIT; the call's events end with check_no_overread's *)
  intros Htk X.
  destruct Hr as [(Hr1 & _) | (Hr0 & _ & _)].
  + pose proof (Ent102PosB.ec_call_evs_ranout_true _ _ _ E trp Hlen (proj1 Htie Hr1)) as Heq1.
    apply (SRrG_ret SEGS _ (wle'_refl SEGS _)). right.
    exists ly, S, [], regs, mem, (with_vm_backing (m_vm_lazy md) X md), own, peak, cnt, ran, k, trp.
    split; [exists fy; split; [exact Hfz|]; split; [exact Hkept | reflexivity]|].
    assert (Hwk : (ec_wk_cno <= ec_wk_exit)%nat).
    { destruct ec_wk_values as (Hc & _ & _ & _ & _ & _ & _ & _ & He & _). rewrite Hc, He. lia. }
    split; [exact (l2_inv_repos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (l2_inv_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Hwk Hinv) (l2_pos_exit E trp _ S Heq1 HROOM))|].
    split; [reflexivity|].
    split; [pose proof (proj2 (HCCOK E 2%nat 11%nat) ltac:(lia)); lia|].
    split; [pose proof (proj2 (HLCOK E 2%nat 11%nat) ltac:(lia)); lia|].
    split; [exact Hrk | exact Hfrm].
  + exfalso. subst r. l2_brv Htk. rewrite Ha0, G0 in Htk. vm_compute in Htk. discriminate Htk.
- (* not taken: r = 0, the reading; call_rest follows check_no_overread's events *)
  intros Hft X.
  destruct Hr as [(Hr1 & _) | (Hr0 & Ho0 & Hran0)].
  + exfalso. subst r. l2_brv Hft. rewrite Ha0, G0 in Hft. vm_compute in Hft. discriminate Hft.
  + subst r o ran.
    assert (Hro : ec_ranout E trp = false).
    { destruct (ec_ranout E trp) eqn:Ho; [|reflexivity]. pose proof (proj2 Htie eq_refl). lia. }
    apply (SRrG_mono SEGS WLE' W _
      (@cut_pno fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO ec_ccut ec_lcut E fk));
      [|intros W' c' _ H; left; exact H].
    replace (332 + 4) with 336 by reflexivity.
    exact (l2_arm0 fy E fk ly S W regs mem (with_vm_backing (m_vm_lazy md) X md) own peak cnt k trp HYP
      Hro Hfz Hkept (l2_inv_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Hinv) HCC H25 HLIV Hrk Hfrm HnMAX Hmost Hown_is).
Qed.

End L2.

Print Assumptions seg_L2_B.
Set Printing Implicit.
About seg_L2_B.
Unset Printing Implicit.
