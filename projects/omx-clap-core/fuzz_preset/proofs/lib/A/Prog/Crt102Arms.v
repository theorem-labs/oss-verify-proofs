(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Loop_kitQ.v, with its module paths and module names changed; 1533 of its 1572 lines of code are new or changed and 157 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): this slice runs at the world-relation contract (note
   the internal file WLE-CONTRACT.md). Its journals sit at R := YA0nH.wle' SEGS
   YGcfRehidePost.RZ_cf (AJ / AJW below), every stretch statement concludes `YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf ..`,
   round_trip_text's post (fpostFbm, at wle') is crossed by YCbqGwild.aj_call_xbFR at R, and the length bound
   round_trip_text's text now asks after ck_frm0 is the Section hypothesis HOS4 (check_round_trip's own premise). *)
(* base: commit 2fdcfd7be069 (post-landing line). kb round (brief
   the internal file wild-budget-kb-reshape.md): crt_live carries its budget kb (M at 0, after
   rtt1 at 32, U at 64, J at 66 = prh_wk F_check_round_trip) and its journal at a budget WS with wbudget [] kb WS;
   arms_wild_budget is RESTATED in that form and DISCHARGED here (arms_wild_budget_goal, Qed, from the text's entry room
   HWR0), so crt102_arms is Qed. *)
(* fuzz_preset, walk of check_round_trip, Crt102Arms: its ARMS on the #102 pins, image A'
   (asan, pin 1be0f53d96cb9d6c, twin bff8519bbe3ea0e4). From the cut M (+0x194: a0 = doc, a1 = 0, a2 = &copy) through
   the two round_trip_text calls (RTT1 at +0x1a0, RTT2 at +0x1c0), the tests R1 (+0x1a4), R2 (+0x1c4) and the type test T
   (+0x1c8 .. +0x1e0), to the three exits C1 (rtt1 = 1), C2 (rtt2 = 1), C3 (doc is not an object), each closed into the
   lane's crt_at_J, and the fall-through at U (+0x1e4), handed to the next slice (Crt102Rewrite) as crt_at_U.
   Against the contract text tcheck_round_trip_specX (lib/A/PRH_FnCheck.v), citing tround_trip_text_specX at both calls.

   INPUTS OF RECORD (taken by path; every file of this lane repeats them):
   - pins: A' asan 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin c90d4fa54d43160b).
   - base commit 3f43a64dfc31 (tail Qed; later merged at its descendant commit b21eb25a9c7): commit
     c52965a03881 (the #102 pins) + the contract texts and Spec by path at the
     kit tip 3ac20a5c9e30 (PRH_FnCheck.v 0844ed8c0608, PRH_Base.v ee2f5cd7ed35; model
     PresetReqAt.v 43c958024221, the record; Spec/PresetFreeFo.v 50bc9df2f2de by path from
     commit 815203ee06e) + the image files of record (YGcfStr 3aabb6857229 pin-free, PSstrlen
     d2c60d9c2c9f, AF0l dfca6bb1a8d7, record YImgTop, listing v3). The ledger carries g_most and g_own_ran_out
     (prh_ledger .. ran most own); fpre carries frm_zero. AT THE LANDING CUT (PRH_FnCheck.v:1172-1301) round_trip_text is
     keyed on ReaderRes.jr_strtod (no rp_sm binder; this slice keeps check_round_trip's rp_sm with crt_pos's strtod
     tie `rp_sm = ReaderRes.jr_strtod` and re-keys at the call, arms_rtt_call), takes its consumer window
     prh_cons_from and the wild room `wild_room (as_universe B) [] (prh_wk F_round_trip_text) (st_depot S)`, and posts
     a BUDGETED journal (fpostFbm .. (wbudget [] (prh_wk F_round_trip_text))); its post states `r = 0` (THE r = 1 ARM
     IS DEAD: C1 and C2 are unreachable, cited by that arm); its r = 0 arm gives the EXACT advance by ck_rtt_evs and,
     with a copy, the read-back's block sizes up to permutation against the reader's own list rd_blocks (rtr jr_strtod
     [] (wdoc t p)) - with rd_blocks_wdoc and fo_tblk that is the glue's `.. ~ tblk t` at C3 and U - copy's ORDERED
     free list (FREEORD-COPY) and its capacities (CAP, pj_ncapR), which arms_rtt_bridge carries to the glue's
     forms. Its run events and window are given by ck_rtt_evs_supply / prh_cons_from_app_iff. Its last premise at the
     kit text 4b8f95c0455c (PRH_FnCheck.v:1241), the UNGUARDED `YGcallStackUp.astack_up_x segs ly W (spZ regs) mem`
     at the callee's sp, is given at both calls from check_round_trip's own last premise (Section hypothesis HUP0,
     :1390) through the journal from the entry (YGcallStackUp.astack_up_at_x; the measured witness
     rtt_up_at_call_A, commit 5208cc4f6eb0). + the lane's glue
     lib/A/Prog/Crt102Glue.v (unchanged here; crt_at_J's r = 0 arm carries copy's ORDERED free list, crt_at_U copy's
     header cap) + S10Env.v + the siblings' Crt102Model.v and Crt102Img.v.
   - WHAT IS PROVED AND WHAT IS ASSUMED (measured on this file's build): every lemma is Qed. At the landing cut
     arms_wild_budget_goal and crt102_arms ended in `Abort` at ONE named goal, arms_wild_budget (the A' twin of
     Crt102B_RRT.crtb_wild_budget: the wild room and the call's budgeted journals `AJW .. WS1` back as the glue's
     `AJ`, unreachable: the only budgeted call rule, YCbqGwild.aj_call_xbF / _sp, leaves the caller at
     `AJW .. (WS0 ++ WS1)`). At the kb re-shape of the contract texts (brief
     the internal file wild-budget-kb-reshape.md) it is restated in the kb form and
     discharged here from the text's entry room HWR0 (arms_wild_budget_goal); arms_rtt_call, arms_after_rtt1 and
     arms_at_M stay Qed implications from it.
   - listing of record: v3, commit 74dcda1eda12 (lib/A/Listing_prog.v 7ed1529926bd,
     lib/A/PAImg_prog.v 505a51ff7d08, = d42e123915ae's data); the segment cut DESIGN.md (sha256 d05697dd088c; internal record) (from
     DESIGN.md (sha256 d05697dd088c; internal record)); the listing read
     the internal file crt.A.s; source
     src-102/new/fuzz_preset.c (sha256 c7b4007bba7bab3e) new:772-781.
   - build route pins102: the internal file zfb-targets.85055e6079bccb28.sh (self-hashing), FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - rule 24: no function proved, by the unit owner's INDEX lookup only (proof-index check_round_trip, exit 0,
     an internal record of that lookup; the index snapshot dates from 04:58Z): the released proofs are
     plain (lib/Prog) and ubsan (lib/U/Prog) only, concluding in SR, not consumable here. [UNMEASURED as a cold/*
     sweep: the unit owner's r24-crt102.py (sha256 1c6d15a8084f; internal record) is that sweep; an old-framework donor
    (commit 8fdc81e94c63) is reported by the walk's owner and not read here.] Written new.
   - VACUITY (the walk's owner, 22:32Z): this statement goes through `prh_univ_closure`, whose clause 4 is false on B' for
     data words; it is vacuous at its instance until a batch of the contract texts lands the 4a / 4b split (4a: the
     code word stays a fixed `In`; 4b: `inU (as_universe B) (prh_trace pc_free_ra0 r [w])`) and removes `DW`. This
     file is A' only (on A' both cursor traces read the code word), so its vacuity closes with the split; it threads
     `DW` only as the Section variable the texts take today (prh_univ_closure B CTX0, tround_trip_text_specX .. CTX0).

   LIBRARY TEXTS ARE CITED ONLY UNDER THE REQUEST BOUND: each round_trip_text call is made with its request bound
   `RQA_rtt t p <= most` a premise of the call lemma arms_rtt_call, given at each call site from the text's own
   `RQA_crt t <= most` by Crt102Model.cm_rqa_rtt0 / cm_rqa_rtt1; that is what makes citing round_trip_text's text
   legitimate while prh_oks' third conjunct and the peak equalities wait on the E sweep. No peak equality is used.

   THE __asan_report_load4 SLOW PATH AT +0x6e4 IS UNREACHABLE: at T the inline check (srli a0,s5,3; add a0,a0,s10;
   lb a0,0(a0); bnez a0) reads doc's shadow byte; the run's token rule asks only that doc's 4 bytes be addressable
   (range_addressable), and doc's 56 bytes are: doc's home is a live fake frame of the entry (the text's ck_tree_ok /
   ck_obj_home), whose shadow the journal from the entry keeps (FP = [], the frame clause; arms_home_keep). So the
   shadow byte is 0, bnez falls through, and neither the slow path nor its report is entered.

   NUMERALS. DERIVED: the cut offsets (Crt102Img's CRT_*_OFF, 4 * the slot inside the function), the realigned sp
   (CRT_sp1), shadow_addr, the stack budgets 27392 / 27632 (STK_round_trip_text / STK_check_round_trip of prh_img_A,
   by computation) and 224 / 240 (the realignment's drop). LENGTH: 224 / 280 / 28 (copy = F + 0xe0, the glue's
   CRT_OFF_COPY, its end, its offset in words), 56 (struct pj), 55 / 6 / 7 (its last byte, its granule count), 4 (the
   type word), 8 / 16 / 32 (saved slots, alignment), 512 / 64 (fs_frame_bytes 3 and its shadow, computed), 4096 (the
   null page), 2 ^ 31 / 2 ^ 40 / 2 ^ 44 / 2 ^ 47 / 2 ^ 64 (image, text, shadow and address spans), 2 ^ 32 (a block's
   size bound), 2 ^ 62, 2 ^ 28, 3 * 2 ^ 20 (the text's bounds). WORD: 6 (PJ_OBJECT), 0 / 1 (the pretty flag, the
   return values). No ADDRESS literal: every code address is pa_sigma / pa_val of PAImg_prog.v, read by computation. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcfTreeVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetFreeFo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA Crt102Glue Crt102Model Crt102Img.
(* kb round: Crt102Kit's AJW runners (crt_run_xw / crt_run_to_xw), used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* the re-hiding move's world relation and its bind / branch over R, used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- the tree predicates: a node is freeable by pj_free to its depth, and deeper (transcribed from an earlier walk's
   lib/A/Prog/H5CrtS7.v at commit 1934271f1f40, cx_fshape_mono .. cx_nodeR_fd; that file is not in this tree; the same
   bodies over PRH_Reader.v's R predicates) ---- *)
Section rd.
Variable segs : list Segment.

Lemma arms_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (H _ _ _ _ _ H6).
Qed.
Lemma arms_pf_items_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *; [exact Hp|].
destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.
Lemma arms_fd_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (Datatypes.S d) p D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
- eapply (arms_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
- eapply (arms_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di Hi. cbv beta in Hi |- *.
  apply (arms_pf_items_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi]. intros a D1 H1. exact (IH a D1 H1).
Qed.
(* duplicate of Crt102Rewrite.crt102rw_fdR_mono, going to the kit; delete when the kit name lands *)
Lemma arms_fd_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof. intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|]. apply arms_fd_succ. apply IH. exact H. Qed.
Lemma arms_items_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma arms_mems_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
  pj_memsR segs m lblk P a ka l D -> pf_itemsR segs m lblk Q true a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
split; [exact E|].
split; [unfold pj_keyR; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.
(* duplicate of Crt102Rewrite.crt102rw_nodeR_fdR, going to the kit; delete when the kit name lands *)
Lemma arms_nodeR_fd : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (PjTree.depth t) p D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H;
  cbn [pj_nodeR] in H.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
  { rewrite En, Nat2Z.id. apply (arms_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 Hu HP. rewrite Forall_forall in IH. apply (arms_fd_mono m lblk (PjTree.depth u)); [|exact (IH u Hu m lblk a D1 HP)].
    pose proof (PjTree.depth_item items u Hu). lia. }
  destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
  + subst cap. exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. exact HI.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
  + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia]. cbn [pj_memsR] in Hi.
    exists (PjTree.tag (PjTree.JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. rewrite En, Nat2Z.id. apply (arms_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (arms_fd_mono m lblk (PjTree.depth u)); [|exact (IH m lblk a D1 HP)]. pose proof (PjTree.depth_member members nm u Hu). lia.
Qed.
(* the header word of a node is its tag (pj_nodeR's pj_hdrR clause; H2H5's H5CrtS2.v s2_node_hdr) *)
Lemma arms_node_hdr : forall m lblk p t D, pj_nodeR segs m lblk p t D -> rd_u32 segs m p (PjTree.tag t).
Proof.
intros m lblk p t D H.
destruct t; cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & (_ & Hty & _) & _);
exact Hty.
Qed.
(* the tree under a larger block predicate (Lam' a permutation of Lam names the same blocks) *)
Lemma arms_memsR_lblk : forall m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall x k, lblk x k -> lblk' x k) ->
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> P' a u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D HL HP H; cbn [pj_memsR] in *; [exact H|].
destruct H as (x & k & D1 & D2 & E & Hx & (Hb & Hc) & H1 & H2). exists x, k, D1, D2.
split; [exact E|]. split; [exact Hx|]. split; [split; [exact (HL _ _ Hb) | exact Hc]|].
split; [apply (HP a u D1); [exists nm; left; reflexivity | exact H1]|].
apply IH; [exact HL | intros a' v D3 (nm' & Hv) HP3; apply (HP a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact H2].
Qed.
Lemma arms_nodeR_lblk : forall t m lblk lblk' p D, (forall x k, lblk x k -> lblk' x k) ->
  pj_nodeR segs m lblk p t D -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk lblk' p D HL H;
  cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [split; [exact (HL _ _ Hl) | exact Hc] | exact ED].
- destruct Hb as (E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [split; [exact (HL _ _ Hl) | exact Hc] | exact ED].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hc0 & Hl)]; [left; exact Hcap | right; split; [exact Hc0 | exact (HL _ _ Hl)]]|].
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH. exact (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HL HP).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hc0 & Hl0 & Hl1)];
    [left; exact Hcap | right; split; [exact Hc0|]; split; [exact (HL _ _ Hl0) | exact (HL _ _ Hl1)]]|].
  exists Di. split; [exact ED|].
  apply (arms_memsR_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di HL); [|exact Hi].
  intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
  exact (IH m lblk lblk' a D1 HL HP).
Qed.
End rd.

(* the tag of an object is 6, of anything else not *)
Lemma arms_tag_obj : forall t, PjTree.tag t = 6 -> exists ms, t = PjTree.JObj ms.
Proof. intros t H. destruct t; cbn in H; try discriminate H. exists members. reflexivity. Qed.
Lemma arms_tag_nobj : forall t, PjTree.tag t <> 6 -> forall ms, t <> PjTree.JObj ms.
Proof. intros t H ms E. apply H. rewrite E. reflexivity. Qed.
Lemma arms_tag_range : forall t, 0 <= PjTree.tag t <= 6.
Proof. intros t. destruct t; cbn; lia. Qed.

(* ---- the model's event lists (PresetReqAt.v 379c33e9e482, PRH_FnCheck.v f7be7f968195's ck_rtt_evs) ---- *)
(* round_trip_text's list with a copy is the model's rt_text; without one it adds back's free *)
Lemma arms_ck_rtt_nz : forall sm t p c, c <> 0 -> ck_rtt_evs sm t p c = PresetReqAt.rt_text sm t p.
Proof. intros sm t p c Hc. unfold ck_rtt_evs. rewrite (proj2 (Z.eqb_neq c 0) Hc). apply app_nil_r. Qed.
(* round_trip is the first call's list, the second call's (back's free included), and the tail: the rewrite and
   pj_free (&copy) for an object, pj_free (&copy) otherwise - Crt102Glue's crt_evs_U / crt_evs_J *)
Lemma arms_rt_tail : forall sm t, PresetReqAt.round_trip sm t =
  (PresetReqAt.rt_text sm t false ++ ck_rtt_evs sm t true 0) ++
  match t with PjTree.JObj ms => crt_evs_U (rp_sm := sm) ms | _ => crt_evs_J (t := t) end.
Proof.
intros sm t. unfold PresetReqAt.round_trip, ck_rtt_evs, crt_evs_U, crt_evs_J. rewrite Z.eqb_refl.
rewrite <- !app_assoc. destruct t; reflexivity.
Qed.
Lemma arms_tail_nobj : forall sm t, (forall ms, t <> PjTree.JObj ms) ->
  match t with PjTree.JObj ms => crt_evs_U (rp_sm := sm) ms | _ => crt_evs_J (t := t) end = crt_evs_J (t := t).
Proof. intros sm t Hn. destruct t; try reflexivity. exfalso. exact (Hn members eq_refl). Qed.
(* the tree copy holds at J for a non-object is t itself (Crt102Glue's crt_tree_J) *)
Lemma arms_tree_J_nobj : forall t, (forall ms, t <> PjTree.JObj ms) -> crt_tree_J (t := t) = t.
Proof. intros t Hn. destruct t; try reflexivity. exfalso. exact (Hn members eq_refl). Qed.

(* the callee-saved float registers kept twice are kept *)
Lemma arms_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

(* a word read back through the view (transcribed from Reusable/YCem.v rdword_of_val_mem, which this lane cannot
   Require: its YCeh is an image-specific file that does not build on pins102) *)
Lemma arms_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ======================================================================================================== *)
(* ---- THE WRITER'S TREE VISIBILITY AT ANY ARx STATE (the walk's ruling: derivable, no lane hypothesis).
   prhWriter_tree_vis W mem Dt (= YGcfTreeVis.tree_vis_cf) for a list of HARNESS blocks the ledger at that state
   lists: per block (a, k), prh_hblock gives the allocator block (a - cf_head, k + cf_head) with its base in Hp and
   a mod 16 = 0; the user range's shadow and hull are AR_laws_x field 14 (alx_hshadow at hl = cf_head), the user bytes
   are present by field 1 (alx_blocks), the granule after them by field 15 (alx_blocks_tail; the block's end
   a - cf_head + (k + cf_head) IS a + k). The four memory-free conjuncts are a per-block hypothesis: for the
   document's blocks they come from the text's own entry premise ck_tree_ok, for a block a callee made from its
   request bound. Model: walk S10's S10TxState.v s10_bvis_lam. ---- *)
Section tv. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {PI : PrhImg}.
#[local] Existing Instance CfParams_preset.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.

Lemma crt_tree_vis_keep : forall ly S Hp W mem md Lamc peakc cntc failc ranc mostc ownc Dt,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lamc peakc cntc failc ranc mostc ownc ->
  (forall bk, In bk Dt -> In bk Lamc) ->
  (forall a k, In (a, k) Dt -> 4096 <= a /\ 0 <= k < 2 ^ 32 /\ (a + k + 7) / 8 * 8 <= YM05.alloc_ceiling /\
     amem_range a ((a + k + 7) / 8 * 8 - a)) ->
  PRH_FnWriter.prhWriter_tree_vis W mem Dt.
Proof.
intros ly S Hp W mem md Lamc peakc cntc failc ranc mostc ownc Dt HAR HL HDt HP a k Hin.
destruct (HP a k Hin) as (H4096 & Hk & Hceil & Hamr).
pose proof (proj1 (Forall_forall _ _)
  (prh_ledger_blocks B ly S Hp W mem Lamc peakc cntc failc ranc mostc ownc HL) (a, k) (HDt _ Hin))
  as (Hk0 & Hab & Hhp & H16 & _).
cbn [fst snd] in Hk0, Hab, Hhp, H16.
assert (Hh0 : @cf_head CfParams_preset = 16) by reflexivity.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & Hpres & _).
assert (Hrq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_hshadow segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab Hhp) as [Hbs Hhull].
rewrite Hrq in Hbs, Hhull, Hpres. replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
split; [exact H4096|]. split; [exact Hk|]. split; [exact Hceil|]. split; [exact Hamr|].
split; [exact (block_shadow_range (aview segs (w_H W) mem) SHADOW_OFF a k a k Hbs ltac:(lia) ltac:(lia))|].
split; [intros Hkp; apply Hhull; lia|].
intros x Hx. destruct (Z_lt_le_dec x (a + k)) as [Hlt|Hge].
- destruct (proj1 (Hpres x ltac:(lia))) as (Hh & bb & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
- apply (alx_blocks_tail segs B ARx LAWS ly S Hp W mem md _ _ x HAR Hab). rewrite Hrq.
  replace (a - cf_head + (k + cf_head)) with (a + k) by lia. lia.
Qed.
End tv.

(* ======================================================================================================== *)
(* ---- IMAGE A' ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).
#[local] Notation STKR := (@STK_round_trip_text prh_img_A).

(* the cut offsets are Crt102Img's (CRT_PC_A, CRT_M_OFF 0x194, CRT_R1_OFF 0x1a4, CRT_R2_OFF 0x1c4, CRT_T_OFF 0x1c8,
   CRT_U_OFF 0x1e4, CRT_J_OFF 0x340; the listing words at each cut are its crt_cut_<X>_A) *)
(* the stack budget of a call made at the realigned sp: STK_round_trip_text = 27392 and STK_check_round_trip = 27632
   (DERIVED, the generated PrhImg's values, by computation), and the realigned sp is 224 or 240 bytes below the entry
   sp (arms_sp1), so `STK1 - o <= STK` of the call rule holds, exactly at 240 *)
Lemma arms_stk : 0 <= STKR /\ STKR + 240 <= STKC.
Proof.
assert (E1 : STKR = 27392) by (vm_compute; reflexivity). assert (E2 : STKC = 27632) by (vm_compute; reflexivity).
rewrite E1, E2. lia.
Qed.
(* check_round_trip keeps a frame pointer, and its two return sites from round_trip_text are R1 and R2 *)
Lemma arms_fp : @pi_fp prh_img_A F_check_round_trip = true.
Proof. vm_compute. reflexivity. Qed.
Lemma arms_rets : @pi_call_rets prh_img_A F_check_round_trip F_round_trip_text =
  [BASE + (CRT_PC_A + CRT_R1_OFF); BASE + (CRT_PC_A + CRT_R2_OFF)].
Proof. exact (proj1 crt_img_A). Qed.

(* a context's one-element prefix is a context (prh_ctx is prefix-closed by its definition) *)
Lemma arms_ctx_head : forall CTX0 F r rest, prh_ctx (PI := prh_img_A) CTX0 F (r :: rest) -> prh_ctx (PI := prh_img_A) CTX0 F [r].
Proof.
intros CTX0 F r rest (c & j & HR & E). exists c, 1%nat. split; [exact HR|].
destruct j as [|j]; [discriminate E|]. destruct c as [|c0 c]; [discriminate E|]. cbn [firstn] in E |- *.
injection E as E1 _. rewrite E1. reflexivity.
Qed.

(* a frame-pointer chain survives a memory change that keeps every word at or above lo (H2H5's H5CrtS1.v
   crt_fpchain_keep): the chain reads only fp - 8 and fp - 16 of frames that climb away from lo *)
Lemma arms_fpchain_keep : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r. rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12].
  apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the journals at the contract's world relation R := wle' SEGS RZ_cf, as Crt102Glue's
   crt_live_journal and Crt102Kit's runners state them *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW; AJ is it at WS = []) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
(* the allocator laws at hl = cf_head (the engine fold's 18 fields; projections by name only) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Variable CTX0 : list (list Z).
(* round_trip_text's text (the contract text, PRH_FnCheck.v 0844ed8c0608; walked in its own walk), at ANY float
   state: rtt2 is entered at the float state rtt1 returned in (aj_call_xF's fx'), so the text is taken at every fxk,
   as the repo's callers take a callee's float-dependent contract *)
Hypothesis RTT : forall fxk : YK11.FPState,
  @tround_trip_text_specX fxk rc CfImg_A CfParams_preset prh_img_A RL A_prog_listing PA B ARx SK CTX0.

Section g.
(* ---- the entry: tcheck_round_trip_specX's binders and the premises this slice uses (each is the text's own) ---- *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (x : list Z) (Lam : list (Z * Z)) (peak cnt ran most : Z).
#[local] Notation sp0 := (spZ regs).
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HRAN : ran = 0.
Hypothesis HRQA : RQA_crt t <= most.
Hypothesis HLIVE : blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX.
Hypothesis HRQ : RQ_crt t + cf_head < cf_malloc_max.
Hypothesis HFR : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip.
(* the text's wild room at entry (PRH_FnCheck.v:1366, kb round): 66 = prh_wk F_check_round_trip fresh wild slots, of
   which each round_trip_text call takes prh_wk F_round_trip_text = 32; read only by arms_wild_budget_goal *)
Hypothesis HWR0 : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S).
(* the live real stack above the entry sp (the text's last premise at the 4b8f95c0455c kit text, PRH_FnCheck.v:1390,
   unguarded); read only at the round_trip_text calls (arms_rtt_call), whose text takes it at the callee's sp *)
Hypothesis HUP0 : YGcallStackUp.astack_up_x SEGS ly W (spZ regs) mem.

(* the glue's names at this walk's binders *)
#[local] Notation LIVE := (crt_live (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA)
  (B := B) (ARx := ARx)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation SIDE := (crt_side (rc := rc) (PI := prh_img_A) (RL := RL) (L := A_prog_listing) (PA := PA) (B := B)
  (doc := doc) (t := t) (D := D) (peak := peak) (most := most)).
#[local] Notation CPOS := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation EVSJ := (crt_evs_J (t := t)).
#[local] Notation EVSU := (crt_evs_U (rp_sm := rp_sm)).
#[local] Notation ATJ := (crt_at_J (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation ATU := (crt_at_U (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation QFF := (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation CFG := (crt_cfg (rc := rc) (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A)).
#[local] Notation BREGS := (crt_bregs (regs := regs)).
#[local] Notation DREGS := (crt_dregs (regs := regs) (doc := doc)).
#[local] Notation SAVED := (crt_saved (rc := rc) (L := A_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation FRAME := (crt_frame (rc := rc) (L := A_prog_listing) (PA := PA)).
#[local] Notation SPILL := (crt_spill (rc := rc) (L := A_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation SP1 := (CRT_sp1 (regs := regs)).
#[local] Notation COPYZ := (crt_copy_zero (rc := rc) (L := A_prog_listing) (PA := PA)).
#[local] Notation COPYT := (crt_copy_tree (rc := rc) (L := A_prog_listing) (PA := PA)).

(* ---- the realigned sp: 224 or 240 bytes below the entry sp, 32-aligned ---- *)
Lemma arms_sp1 : SP1 mod 32 = 0 /\ sp0 - 240 <= SP1 <= sp0 - 224 /\ 0 <= SP1.
Proof.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof arms_stk as (S1 & S2).
unfold CRT_sp1, CRT_FRAME, CRT_ALIGN. pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
assert ((sp0 - 224) mod 32 = 0 \/ (sp0 - 224) mod 32 = 16).
{ apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. lia. }
split; [apply Z.mod_mul; lia|]. split; [lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

(* ---- the document's home is a live fake frame of the entry, so its 56 bytes stay addressable at every state the
   journal from the entry reaches (FP = []: the frame clause keeps the frame's shadow) ---- *)
Lemma arms_home_keep : forall own lyc Sc Hpc Wc memc mdc kj WS,
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS -> ck_obj_home lyc Sc Wc memc doc.
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ.
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & Hd8 & (cid & pos & Hfin & Hfa1 & Hfa2) & HRA).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR Hly) as (_ & Efa & _).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (F32 & _).
split; [exact Hd8|]. split.
- exists cid, pos. rewrite Efa. split; [rewrite Hfrs; apply in_or_app; right; exact Hfin|]. split; lia.
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr. apply (F4 cid pos); [exact Hfin | right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd].
  assert (E8 : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 = frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
  { apply Z.mod_divide in F32; [|lia]. destruct F32 as [q Hq]. rewrite Hq.
    replace (q * 32 + fs_frame_bytes cid) with (fs_frame_bytes cid + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
    replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Hd : (doc + 56) / 8 = doc / 8 + 7).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 56) with ((q + 7) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  pose proof (Z.div_le_mono (frame_addr ly cid pos) a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (doc + 55) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (doc + 56) (frame_addr ly cid pos + fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  assert ((doc + 55) / 8 = doc / 8 + 6).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 55) with (7 + (q + 6) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. cbn. lia. }
  lia.
Qed.

(* ---- the document's tree as round_trip_text asks it (ck_tree_ok) at any live state: the node and its blocks from
   crt_side, the blocks' visibility from crt_tree_vis_keep (its memory-free facts from the entry's ck_tree_ok), the
   home from arms_home_keep ---- *)
Lemma arms_tree_ok : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> ck_tree_ok lyc Sc Lamc Wc memc doc t D.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg HL.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_doc HSD) as HND.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HTREE as (_ & _ & HTV & _).
split; [exact HND|]. split; [exact HDL|]. split; [|exact (arms_home_keep _ _ _ _ _ _ _ _ _ HJ)].
apply (crt_tree_vis_keep B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ ranc most ownc D (proj1 HJ) HLED HDL).
intros a k Hin. destruct (HTV a k Hin) as (H1 & H2 & H3 & H4 & _). auto.
Qed.

(* ---- the frame-pointer chain at a call made at the realigned sp with s0 = the entry sp: check_round_trip's own
   record (its ra at sp0 - 8 and the caller's s0 at sp0 - 16, crt_saved's first two slots) pushed onto the chain it
   was given, unless the entry sp is within 16 of the layout's top (H2H5's H5CrtS1.v crt_chain) ---- *)
Lemma arms_chain : forall own lyc Sc Hpc Wc memc mdc kj WS,
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS -> SAVED Wc memc ->
  exists ch1, achain lyc (aview SEGS (w_H Wc) memc) SP1 sp0 ch1 /\
    (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch).
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ HSV.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct arms_sp1 as (Hs32 & Hs1 & Hs0).
assert (H8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr1. change (bv_modulus 64) with (2 ^ 64) in Hr1.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr8. change (bv_modulus 64) with (2 ^ 64) in Hr8.
assert (Hw1 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 8) = Some (raZ regs)).
{ apply arms_rdword_of_val_mem; [|unfold raZ; lia]. exact (HSV 0%nat ltac:(lia)). }
assert (Hw8 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 16) = Some (s0Z regs)).
{ apply arms_rdword_of_val_mem; [|unfold s0Z; lia]. exact (HSV 1%nat ltac:(lia)). }
destruct (Z_le_gt_dec (ly_top lyc - 16) sp0) as [Hbad|Hgood].
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hbad | reflexivity].
- exists ((sp0, raZ regs, s0Z regs) :: ch). split; [|right; reflexivity]. right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, sp0 <= a -> a < ly_top ly ->
            rdword (aview SEGS (w_H Wc) memc) a = rdword (aview SEGS (w_H W) mem) a).
  { intros a Ha Hat. apply ts_rdword_keep. intros j Hj. apply F1; lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next sp0 (ly_top lyc) (s0Z regs)) eqn:Eb.
    * destruct Hch as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12].
        - apply Z.leb_le in Eb11. lia.
        - apply Z.leb_le in Eb12. lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * destruct Hch as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
        apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
        apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
        destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (arms_fpchain_keep (aview SEGS (w_H W) mem) (aview SEGS (w_H Wc) memc) sp0);
        [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbv beta. intros r Hr. lia.
Qed.

(* ---- the return sites of the two calls: text addresses, below the ceiling, the listed call returns ---- *)
Lemma arms_ret : forall off, off = CRT_R1_OFF \/ off = CRT_R2_OFF ->
  4096 <= BASE + (CRT_PC_A + off) < 2 ^ 31 /\ (CRT_PC_A + off) mod 2 = 0 /\ 0 <= CRT_PC_A + off < 2 ^ 40 /\
  In (BASE + (CRT_PC_A + off)) (@pi_call_rets prh_img_A F_check_round_trip F_round_trip_text).
Proof.
intros off [-> | ->]; rewrite arms_rets;
  (split; [split; vm_compute; first [discriminate | reflexivity]|]);
  (split; [vm_compute; reflexivity|]); (split; [split; vm_compute; first [discriminate | reflexivity]|]).
- left. reflexivity.
- right. left. reflexivity.
Qed.

(* ---- the room position on the r = 0 path (Crt102Glue's crt_pos). At M it is the whole of round_trip (pre = []);
   after both calls returned 0 it is round_trip's tail: crt_evs_U for an object, crt_evs_J otherwise. crt_pos also
   carries the strtod tie and the consumer window prh_cons_from, split at each call like the run premise ---- *)
Lemma arms_pos_entry : forall Sc, CPOS Sc (PresetReqAt.round_trip rp_sm t) ->
  rp_sm = ReaderRes.jr_strtod /\
  exists hist, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist Sc /\
    prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) /\
    PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)).
Proof.
intros Sc HP.
pose proof (crt_pos_strtod HP) as Hsm. destruct (crt_pos_ex HP) as (pre & hist & HA).
pose proof (crt_pos_split HA) as E. pose proof (crt_pos_room HA) as HI.
pose proof (crt_pos_run HA) as HR. pose proof (crt_pos_cons HA) as HC.
assert (Hl : length pre = 0%nat).
{ pose proof (f_equal (@length _) E) as El. rewrite length_app in El. lia. }
rewrite Hl, Nat.add_0_r in HI, HR, HC. split; [exact Hsm|]. exists hist. split; [exact HI|]. split; [exact HR | exact HC].
Qed.
(* the consumer window of the two calls: round_trip's first piece (rtt1, copy <> 0) and second (rtt2, copy = 0) *)
Lemma arms_cons_split : forall c, c <> 0 ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (ck_rtt_evs rp_sm t false c)) /\
  PRH_Base.prh_cons_from rp_sm rp_x rp_os (rp_i + length (ck_rtt_evs rp_sm t false c))
    (length (ck_rtt_evs rp_sm t true 0)).
Proof.
intros c Hc HC. rewrite (arms_ck_rtt_nz rp_sm t false c Hc).
rewrite (arms_rt_tail rp_sm t), !length_app in HC.
apply (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [HC1 _].
exact (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _) HC1).
Qed.
Lemma arms_pos_tail : forall S2 hist,
  rp_sm = ReaderRes.jr_strtod ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length (PresetReqAt.rt_text rp_sm t false) + length (ck_rtt_evs rp_sm t true 0))%nat rp_H0 hist S2 ->
  CPOS S2 (match t with PjTree.JObj ms => EVSU ms | _ => EVSJ end).
Proof.
intros S2 hist Hsm HR HC HI.
pose proof (arms_rt_tail rp_sm t) as E.
rewrite E in HR, HC. apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HR as [_ HR].
rewrite length_app in HC. apply (proj1 (PRH_Base.prh_cons_from_app_iff _ _ _ _ _ _)) in HC as [_ HC].
refine {| crt_pos_strtod := Hsm; crt_pos_ex := _ |}.
exists (PresetReqAt.rt_text rp_sm t false ++ ck_rtt_evs rp_sm t true 0), hist.
refine {| crt_pos_split := E; crt_pos_room := _; crt_pos_run := HR; crt_pos_cons := HC |}.
rewrite length_app, Nat.add_assoc. exact HI.
Qed.
Lemma arms_pos_U : forall S2 hist ms, t = PjTree.JObj ms ->
  rp_sm = ReaderRes.jr_strtod ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length (PresetReqAt.rt_text rp_sm t false) + length (ck_rtt_evs rp_sm t true 0))%nat rp_H0 hist S2 ->
  CPOS S2 (EVSU ms).
Proof.
intros S2 hist ms Et Hsm HR HC HI. pose proof (arms_pos_tail S2 hist Hsm HR HC HI) as H.
assert (E : match t with PjTree.JObj ms0 => EVSU ms0 | _ => EVSJ end = EVSU ms) by (rewrite Et; reflexivity).
rewrite E in H. exact H.
Qed.
Lemma arms_pos_J : forall S2 hist, (forall ms, t <> PjTree.JObj ms) ->
  rp_sm = ReaderRes.jr_strtod ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length (PresetReqAt.rt_text rp_sm t false) + length (ck_rtt_evs rp_sm t true 0))%nat rp_H0 hist S2 ->
  CPOS S2 EVSJ.
Proof.
intros S2 hist Hn Hsm HR HC HI. pose proof (arms_pos_tail S2 hist Hsm HR HC HI) as H.
rewrite (arms_tail_nobj rp_sm t Hn) in H. exact H.
Qed.

(* ---- round_trip_text's post at a call from a live state: the text's own Q (tround_trip_text_specX's post, the landing
   cut's PRH_FnCheck.v:1241-1301) at the call's binders, VERBATIM but for the run's strtod model, written rp_sm here
   where the cut's text writes ReaderRes.jr_strtod (the call lemma arms_rtt_call takes `rp_sm = ReaderRes.jr_strtod`,
   crt_pos's strtod tie, and rewrites with it); the call rule hands it over as fQmn of it. `rpi` is the call's
   position. THE r = 1 ARM IS DEAD (`r = 0 /\` in front, the text's statement under its entry premise
   prh_cons_from); the r = 0 arm gives the room at the EXACT advance by the call's own list and, with a copy, the
   read-back's block sizes UP TO PERMUTATION against the reader's own list rd_blocks (rtr jr_strtod [] (wdoc t p)),
   under CFHEAD-16 (cf_head = HEAD), copy's ORDERED free list at every depth bound (FREEORD-COPY, :1290-1293)
   and copy's capacities (CAP, PRH_Reader.pj_ncapR, :1301) ---- *)
Definition arms_rtt_Q (rpi : nat) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (Lamc : list (Z * Z)) (peakc cntc ranc copy : Z) (p : bool)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       peakc <= peak' /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\
       exists r, getr regs' 10 = w64 r /\
         r = 0 /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\
           cntc <= cnt' <= cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\
           (copy <> 0 -> forall a, copy <= a < copy + 56 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a)) \/
          (r = 0 /\ own' = 0 /\
           cnt' = cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ran' = ranc /\
           (exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rpi + length (ck_rtt_evs rp_sm t p copy))%nat
              rp_H0 hist' S') /\
           (copy = 0 -> Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc)) /\
           (copy <> 0 ->
              exists Db, Permutation Lam' (Db ++ Lamc) /\
                (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) /\
                Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
                (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db)
                   (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
                (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
                   exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') nn copy Db F /\
                     map (fun b => snd b + cf_head) F =
                       PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
                Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
                Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ ck_hblks Db) /\
                pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') copy t Db /\
                pj_ncapR SEGS (mrestrict (w_H W') mem') copy t))).

(* ---- the read-back's block sizes against tblk t up to permutation, from the text's reader-side conjunct:
   cf_head = HEAD (16 = 16, the preset's parameter), PresetFreeFo.rd_blocks_wdoc (pj_wf t: the reader's
   live blocks after reading wdoc t p are fo t) and PresetReqAtNoMiss.fo_tblk (fo t ~ tblk t) ---- *)
Lemma arms_tblk_of_rb : forall (Db : list (Z * Z)) p, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db)
     (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) ->
  Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk t).
Proof.
intros Db p Hw HRB.
eapply perm_trans; [exact (HRB ltac:(vm_compute; reflexivity))|].
eapply perm_trans; [exact (PresetFreeFo.rd_blocks_wdoc ReaderRes.jr_strtod t p Hw)|].
exact (PresetReqAtNoMiss.fo_tblk t).
Qed.

(* ---- THE SAME POST IN THE FORM THE SEGMENT LEMMAS READ, at the call's own post state and pointer, inside the
   copy <> 0 existential: the text's conjuncts in this order, the free order (FREEORD-COPY) moved after pj_nodeR,
   and CAP (pj_ncapR) read as copy's HEADER CAP for an object, ncap (length ms) (the glue's crt_at_U last conjunct):
   FREEORD-COPY - copy's ORDERED free list, against the reader's pj_free list of wdoc t p (PresetReqAt.pj_frees),
     under CFHEAD-16 like the block conjunct beside it; with PresetFreeFo.pj_frees_wdoc_t it is fo t (the glue's
     crt_at_J r = 0 field at C3, crt_tree_J = t);
   CAP - from the cut's pj_ncapR (its object clause's first conjunct, the cap word, PRH_Reader.v:247) by the glue's
     bridge Crt102Glue.crt_copy_cap_of_ncap48. Neither is derivable from pj_nodeR and the block permutations (pj_nodeR
     leaves a container's cap and a string block's size free above their minimum; the CRT-B-UGKO1 / Crt102Model's
     counterexamples); the landing cut's text states both, and arms_rtt_bridge carries arms_rtt_Q into this form. ---- *)
Definition arms_rtt_Q_k0 (rpi : nat) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (Lamc : list (Z * Z)) (peakc cntc ranc copy : Z) (p : bool)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       peakc <= peak' /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\
       exists r, getr regs' 10 = w64 r /\
         r = 0 /\
         ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\
           cntc <= cnt' <= cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\
           (copy <> 0 -> forall a, copy <= a < copy + 56 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a)) \/
          (r = 0 /\ own' = 0 /\
           cnt' = cntc + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ran' = ranc /\
           (exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rpi + length (ck_rtt_evs rp_sm t p copy))%nat
              rp_H0 hist' S') /\
           (copy = 0 -> Permutation Lam' Lamc /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc)) /\
           (copy <> 0 ->
              exists Db, Permutation Lam' (Db ++ Lamc) /\
                (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) /\
                Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
                (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) Db)
                   (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
                Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
                Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ ck_hblks Db) /\
                pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') copy t Db /\
                (* FREEORD-COPY, the cut's text's conjunct verbatim (PRH_FnCheck.v:1290-1293; its local abbreviation
                   rdW W' mem' written out): at EVERY depth bound nn, as the kit's pj_set entry premise and the glue's
                   crt_at_U_copy_fo take it *)
                (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
                   exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') nn copy Db F /\
                     map (fun b => snd b + cf_head) F =
                       PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
                (* CAP (pj_ncapR) *)
                (forall ms, t = PjTree.JObj ms -> forall ty num str kids keys n cap,
                   pj_hdrR SEGS (mrestrict (w_H W') mem') copy ty num str kids keys n cap ->
                   cap = Z.of_nat (PresetReqAt.ncap (length ms)))))).

(* ---- the bridge: rtt's post in the text's form (arms_rtt_Q) carried conjunct by conjunct into the form the segment
   lemmas read (arms_rtt_Q_k0); the copy arm's two facts from the cut's own conjuncts, FREEORD-COPY verbatim
   (PRH_FnCheck.v:1290-1293) and CAP from pj_ncapR's object clause (:1301; PRH_Reader.v:247) through the glue's
   Crt102Glue.crt_copy_cap_of_ncap48 ---- *)
Lemma arms_rtt_bridge : forall rpi lyc Sc Wc memc Lamc peakc cntc ranc copy p ly' S' Hp' W' regs' mem' md',
  arms_rtt_Q rpi lyc Sc Wc memc Lamc peakc cntc ranc copy p ly' S' Hp' W' regs' mem' md' ->
  arms_rtt_Q_k0 rpi lyc Sc Wc memc Lamc peakc cntc ranc copy p ly' S' Hp' W' regs' mem' md'.
Proof.
intros rpi lyc Sc Wc memc Lamc peakc cntc ranc copy p ly' S' Hp' W' regs' mem' md' HQ. unfold arms_rtt_Q_k0. cbv beta.
destruct HQ as (HR & Lam' & peak' & cnt' & ran' & own' & HLd & Hpk & HNd & r & H10 & Hr0 & Harm).
split; [exact HR|]. exists Lam', peak', cnt', ran', own'. split; [exact HLd|]. split; [exact Hpk|].
split; [exact HNd|]. exists r. split; [exact H10|]. split; [exact Hr0|].
destruct Harm as [H1 | (Er & Ho & Ec & Era & Hpos & Hc0 & Hcopy)]; [left; exact H1 | right].
split; [exact Er|]. split; [exact Ho|]. split; [exact Ec|]. split; [exact Era|]. split; [exact Hpos|].
split; [exact Hc0|].
(* the copy arm's conjuncts at the cut, one name each (PRH_FnCheck.v:1265-1301) *)
intros Hnz. destruct (Hcopy Hnz) as (Db & HPm & Hfr & Hlsz & HRB & HFO & Hnl & HPab & HNd2 & HNC).
exists Db. split; [exact HPm|]. split; [exact Hfr|]. split; [exact Hlsz|]. split; [exact HRB|].
split; [exact Hnl|]. split; [exact HPab|]. split; [exact HNd2|].
(* FREEORD-COPY: the text's free-order conjunct, the same term *)
split; [exact HFO|].
(* CAP: pj_ncapR at an object is its cap word and its kids' clause; the cap word fixes the header's cap *)
intros ms Et ty num str kids keys n cap Hhdr. rewrite Et in HNC. cbn [pj_ncapR] in HNC.
destruct HNC as [HCAPW _].
exact (crt_copy_cap_of_ncap48 _ _ _ _ ms ty num str kids keys n cap HCAPW Hhdr).
Qed.

(* ---- copy's free list against fo t at every depth bound, from the FREEORD-COPY form: cf_head = HEAD (16 = 16, the
   preset's parameter) and PresetFreeFo.pj_frees_wdoc_t (pj_wf t: pj_free's list of the tree the reader
   builds from the writer's text of t is fo t) ---- *)
Lemma arms_fo_of_frees : forall (m : word -> option byte) lblk p Db, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS m lblk nn p Db F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t false)) ->
  forall nn, (PjTree.depth t <= nn)%nat ->
    exists F, PRH_PjOrder.pj_foR SEGS m lblk nn p Db F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo t.
Proof.
intros m lblk p Db Hw H nn Hd. destruct (H ltac:(vm_compute; reflexivity) nn Hd) as (F & HF & HM).
exists F. split; [exact HF|]. rewrite HM. exact (PresetFreeFo.pj_frees_wdoc_t ReaderRes.jr_strtod t false Hw).
Qed.

(* the class-3 frame's facts at a live state: on the frame list, its bytes present and not the runtime's, its 64
   shadow bytes present, 32-aligned, at or above 4096 and below the ceiling, in one application range *)
Lemma arms_frame_facts : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  let F := frame_addr lyc CRT_CID pos in
  In (CRT_CID, pos) (frames Sc) /\ F mod 32 = 0 /\ 4096 <= F /\ F + 512 <= YM05.alloc_ceiling /\ in_app F 512 /\
  (forall a, F <= a < F + 512 -> apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr F + i)).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg HL F.
destruct (crt_live_journal HL) as (? & (HARc & _) & _).
pose proof (crt_frame_listed (crt_live_frame HL)) as Hin3.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin3) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin3) as (F32 & Fapp & Ffr & Fsh).
change (fs_frame_bytes CRT_CID) with 512 in *. change (512 / 8) with 64 in Fsh.
split; [exact Hin3|]. split; [exact F32|]. split; [exact Fb1|]. split; [exact Fb2|]. split; [exact Fapp|].
split; [exact Ffr|]. intros i Hi. exact (proj1 (Fsh i Hi)).
Qed.

(* ---- THE WILD BUDGET AT A round_trip_text CALL, the A' TWIN of Crt102B_RRT.crtb_wild_budget, RESTATED AT THE kb
   RE-SHAPE (brief, the internal file wild-budget-kb-reshape.md, on the contract texts). The cut's text
   (PRH_FnCheck.v:1216) asks at the call the room `wild_room (as_universe B) [] (prh_wk F_round_trip_text)
   (st_depot Sc)` and posts fpostFbm .. (wbudget [] (prh_wk F_round_trip_text)) (:1256): through
   YCbqGwild.aj_call_xbFR (at R) the caller's journal after the call is at WS0 ++ WS1, WS0 the live state's budget and
   `wbudget [] (prh_wk F_round_trip_text) WS1` the call's. The glue's crt_live now carries its budget kb and its
   journal at a budget WS with `wbudget [] kb WS` (Crt102Glue.v crt_live_journal), so this Prop states, at every live
   state at a kb that leaves the call its 32 (kb + 32 <= 66 = prh_wk F_check_round_trip: rtt1 at kb = 0, rtt2 at
   kb = 32), the room the text asks and the landing of the composed journal at kb + 32. It is the premise of
   arms_rtt_call and of every lemma that reaches it (arms_after_rtt1, arms_at_M), and it is DISCHARGED below by
   arms_wild_budget_goal (Qed) from the text's entry room HWR0 (YCbqGwild.ajournal_xw_roomR, wild_room_le,
   wbudget_app). ---- *)
Definition arms_wild_budget : Prop :=
  forall (kb : nat) lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc,
  LIVE kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 ran ->
  (kb + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_round_trip_text) (st_depot Sc) /\
  (forall ly2 S2 Hp2 W2 mem2 md2 k1 (WS0 WS1 : list (list Z)),
     YCbqGwild.wbudget [] kb WS0 ->
     YCbqGwild.wbudget [] (prh_wk F_round_trip_text) WS1 ->
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) (WS0 ++ WS1) ->
     exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
       YCbqGwild.wbudget [] (kb + prh_wk F_round_trip_text) WS).

(* the brief's per-boundary arithmetic (prh_wk F_check_round_trip = 66 = 32 + 32 + 2, PRH_Base.v:151-160): rtt1 at
   kb = 0 and rtt2 at kb = 32 each leave the call its 32; U's 64 is within J's 66 *)
Lemma arms_kb_rtt1 : (0 + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.
Lemma arms_kb_rtt2 : (prh_wk F_round_trip_text + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat.
Proof. cbn. lia. Qed.

(* the live state at a budget kb is a live state at every larger budget (wbudget is an upper bound) *)
Lemma arms_live_mono : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kb kb',
  LIVE kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> (kb <= kb')%nat ->
  LIVE kb' lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kb kb' HL Hk.
destruct (crt_live_journal HL) as (WS & HJ & HB).
exact {| crt_live_journal := ex_intro _ WS (conj HJ (Nat.le_trans _ _ _ HB Hk)); crt_live_side := crt_live_side HL;
         crt_live_lam_perm := crt_live_lam_perm HL; crt_live_blocks_perm := crt_live_blocks_perm HL;
         crt_live_dx_apart := crt_live_dx_apart HL; crt_live_saved := crt_live_saved HL;
         crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
         crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
         crt_live_memnorm := crt_live_memnorm HL |}.
Qed.

(* THE LENGTH BOUND, check_round_trip's own text premise (PRH_FnCheck.v:2363); round_trip_text's
   text asks it after ck_frm0 (`(length rp_os <= 4)%nat`, the callee's rp_os is this walk's). Declared here, after
   the lemmas that do not read it, and read only at the two round_trip_text calls (arms_rtt_call). lia's zify picks up
   a nat premise in context, so the lemmas below that do not reach arms_rtt_call and run lia (or a tactic that may)
   start with `clear HOS4`: it is abstracted only into arms_rtt_call, arms_after_rtt1, arms_at_M and crt102_arms
   (measured at this file's probe build c03f6006f19f: Check of arms_after_rtt2, which uses every lemma between here
   and arms_after_rtt1 except arms_rtt_call, shows no HOS4) *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* ---- THE round_trip_text CALL, from the state a run leaves at `jal round_trip_text` (A' +0x1a0 and +0x1c0): the
   live state with the call next, the argument registers, and the per-call model bounds, each given by the caller
   from the text's own premises (Crt102Model.v): the REQUEST BOUND `RQA_rtt t p <= most` is a premise of this lemma,
   so every call site states where it came from; so are the call's position `rpi` (the room there) and its run
   events (ck_rtt_evs, supplied by ck_rtt_evs_supply from round_trip). The text is keyed on ReaderRes.jr_strtod: the
   premise `rp_sm = ReaderRes.jr_strtod` (crt_pos's strtod tie) re-keys the position, run and window to it and the
   text's post back to rp_sm. The continuation receives the callee's journal, the composed journal from the entry,
   the kept registers, the float state the callee left, and the text's post. Over YCbqGwild.v's aj_call_xbFR at
   R := wle' SEGS RZ_cf (the text's post is budgeted at the cut and at wle'), the caller's
   journal at the live state's budget WS0 (crt_live at kb); the
   call's room and the landing of the composed journal at kb + 32 are arms_wild_budget, its first premise. Model:
   walk S10's S10TxStrGlue.v ts_put_call (the callee reaches musl strtod). ---- *)
Lemma arms_rtt_call : arms_wild_budget -> forall (fxk : YK11.FPState) (pretty copy off : Z) Wc E ss ms mdc lyc Sc
    Hpc kj pos Dx Lamc peakc cntc rpi rph (kb : nat),
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_round_trip_text ->
  bv_unsigned (ew E 2) = sp0 ->
  LIVE kb lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 ran ->
  (kb + prh_wk F_round_trip_text <= prh_wk F_check_round_trip)%nat ->
  DREGS (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 10 = w64 doc -> getr (ms_regs ms) 11 = w64 pretty -> getr (ms_regs ms) 12 = w64 copy ->
  (pretty = 0 \/ pretty = 1) ->
  (off = CRT_R1_OFF \/ off = CRT_R2_OFF) -> getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) ->
  (copy = 0 \/ copy = frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ->
  cntc < 2 ^ 62 ->
  RQA_rtt t (negb (pretty =? 0)) <= most ->
  blocks_bytes Sc + LIVE_round_trip_text t (negb (pretty =? 0)) <= LIVE_MAX ->
  RQ_rtt t (negb (pretty =? 0)) + cf_head < cf_malloc_max ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rpi rp_H0 rph Sc ->
  prh_run_at rp_sm rp_x rp_os rpi (ck_rtt_evs rp_sm t (negb (pretty =? 0)) copy) ->
  rp_sm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rpi (length (ck_rtt_evs rp_sm t (negb (pretty =? 0)) copy)) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS ->
     YCbqGwild.wbudget [] (kb + prh_wk F_round_trip_text) WS ->
     AJW STKR SP1 (if copy =? 0 then [] else [(copy, copy + 56)]) lyc Sc Hpc Wc (ms_mem ms) mdc []
       ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     aregs_preserved (ms_regs ms) regs2 ->
     arms_rtt_Q rpi lyc Sc Wc (ms_mem ms) Lamc peakc cntc ran copy (negb (pretty =? 0)) ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem2) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 (YK11.seg_rom SEGS)) md2) QFF) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFF.
Proof.
intros HGAP fxk pretty copy off Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc rpi rph kb HFZ HS Hrv Hpcs HE2 HL
  Hkb HDR Ha0 Ha1 Ha2 Hpr Hoff Hra Hcopy Hcnt HRQAr HLIVEr HRQr HRP HRUN HSM HCONS HK.
destruct (HGAP kb lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc HL Hkb) as [HWR HLAND].
(* the text is keyed on ReaderRes.jr_strtod: its position, run and window premises at that key *)
rewrite HSM in HRP, HRUN, HCONS.
destruct (crt_live_journal HL) as (WS0 & HJ & HB0). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPm. pose proof (crt_live_blocks_perm HL) as HPab.
pose proof (crt_live_dx_apart HL) as HDap. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSP.
pose proof (crt_live_copy_open HL) as HCS. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (crt_dregs_bregs HDR) as HBR. pose proof (crt_dregs_s5 HDR) as R21.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof arms_stk as (HS0 & HS1). destruct arms_sp1 as (Hs32 & Hs1 & Hs0).
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (arms_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (Hin3 & F32 & Fb1 & Fb2 & Fapp & Ffr & Fsh).
cbv zeta in Fb1, Fb2, Fapp, Ffr, Fsh, F32.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (arms_ret off Hoff) as (Hr1 & Hr2 & Hr3 & Hr4).
destruct (arms_chain _ _ _ _ _ _ _ _ _ HJ HSV) as (ch1 & Hch1 & Ech1).
set (o := SP1 - sp0).
assert (Hspz : spZ (ms_regs ms) = SP1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspc : getr (ms_regs ms) 2 = sv_denot E (SOff 2 o)).
{ apply bv_eq. rewrite denot_SOff, HE2, R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by (unfold o; lia). unfold o. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_A + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
(* the document is at or above 4096 (its home frame is a live frame of the entry) *)
assert (Hdoc0 : doc <> 0).
{ pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & _) & _).
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hfin) as (Hf1 & _). lia. }
(* the model premises, from the text's own *)
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ refine (@YCbqGwild.aj_call_xbFR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc A_prog_listing PA) RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms
    STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WS0 STKR
    (if copy =? 0 then [] else [(copy, copy + 56)]) o (ew E 2) (getr (ms_regs ms) 1) ch1
    (YCbqGwild.wbudget [] (prh_wk F_round_trip_text)) _ HS Hrv HJ Hspc eq_refl HE2 _ _ HS0 _ _ _ eq_refl _ _ _ _ _).
  - unfold o. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. apply Z.mod_divide in Hs32; [|lia].
    destruct Hs32 as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - unfold o. lia.
  - unfold o. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + o) with SP1 by (unfold o; lia). rewrite Hs0z. exact Hch1.
  - (* the callee: round_trip_text's text at the call's binders (keyed on ReaderRes.jr_strtod: no rp_sm binder) *)
    intros HPRE1. rewrite Hpcs.
    pose proof HPRE1 as (_ & _ & _ & _ & _ & Hstk1 & _).
    pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & _).
    assert (Hhi1 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyc) by (rewrite Hspz, Eshi; lia).
    assert (Hrac1 : raZ (ms_regs ms) < YM05.alloc_ceiling) by (rewrite Hraz; lia).
    assert (HCTX1 : prh_ctx CTX0 F_round_trip_text (raZ (ms_regs ms) :: spine ch1)).
    { pose proof (prh_ctx_call CTX0 F_check_round_trip F_round_trip_text _ _ HCTX (eq_ind_r (fun r => In r _) Hr4 Hraz))
        as Hc. rewrite arms_fp in Hc.
      destruct Ech1 as [-> | ->]; [exact (arms_ctx_head _ _ _ _ Hc) | exact Hc]. }
    assert (HCOPY : copy = 0 \/ (copy <> 0 /\ copy mod 8 = 0 /\
      ck_out_ok B STKR lyc Sc Wc (ms_regs ms) (ms_mem ms) copy 56 /\ (copy + 56 <= doc \/ doc + 56 <= copy))).
    { destruct Hcopy as [-> | ->]; [left; reflexivity|]. right.
      split; [unfold CRT_OFF_COPY; lia|]. split; [unfold CRT_OFF_COPY; apply Z.mod_divide in F32; [|lia];
        destruct F32 as [q Hq]; apply Z.mod_divide; [lia|]; exists (4 * q + 28); lia|].
      split; [split|].
      - exists CRT_CID, pos. split; [exact Hin3|]. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY. lia.
      - unfold CRT_OFF_COPY. split; [lia|]. split; [lia|].
        split; [unfold in_app, amem_range, kLowShadowBeg in *; unfold ASAN_CEIL in Fapp; lia|].
        split; [intros a Ha; destruct (Ffr a ltac:(lia)) as (Hp1 & Hp2); split; [apply apresent_writable; exact Hp1|];
          split; [exact Hp2 | rewrite Hspz; lia]|].
        split; [exact HCS | intros _; exact HCH].
      - (* copy is in the class-3 frame, the document in a frame of the entry: the frames are apart *)
        pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _).
        destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa & _).
        destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) mdc HARc) as (Hsep & _).
        apply pairwise_app_l in Hsep as [_ Hsep]. rewrite HFRc in Hsep. cbn [app map pairwise] in Hsep.
        destruct Hsep as (Hsep & _). rewrite Forall_map in Hsep.
        pose proof (proj1 (Forall_forall _ _) Hsep (cid, pos') Hfin) as Hd. cbn [fst snd] in Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (Efa cid pos') in Hd.
        change (fs_frame_bytes CRT_CID) with 512 in Hd. unfold CRT_OFF_COPY. fold F in Hd. lia. }
    assert (HFRS : Z.of_nat (length (frames Sc)) <= ck_FRAMES_CAP - FR_round_trip_text).
    { rewrite HFRc. cbn [app length]. pose proof (cm_frames_before (length (frames S)) HFR). lia. }
    (* THE LIVE REAL STACK ABOVE THE CALLEE'S sp (the text's last premise at the 4b8f95c0455c kit text,
       PRH_FnCheck.v:1241): from check_round_trip's own entry fact HUP0 through the journal from the entry
       (YGcallStackUp.astack_up_at_xwR at R, at the journal's budget), the callee's sp SP1 inside the entry's window
       (arms_sp1, arms_stk). The proof of the measured witness rtt_up_at_call_A (RttStackUpA.v at
       commit 5208cc4f6eb0, a file not in this tree), done here at the walk's binders *)
    assert (HUPc : YGcallStackUp.astack_up_x SEGS lyc Wc (spZ (ms_regs ms)) (ms_mem ms)).
    { rewrite Hspz. pose proof arms_stk as (Sk0 & Sk1). pose proof arms_sp1 as (_ & (Sp1 & Sp2) & _).
      (* the journal at its budget WS0 and at R: astack_up_at_xwR reads neither the budget nor
         the world conjunct *)
      pose proof (YGcallStackUp.astack_up_at_xwR SEGS B PST ARx (@pa_segs_low rc A_prog_listing PA) RZW STKC sp0 [] ly
        S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms) mdc kj WS0 SP1 STKR HJ HUP0
        ltac:(lia) Sk0 ltac:(lia)) as Hd.
      intros a Ha. apply Hd. lia. }
    exact (RTT fxk rp_x rp_os rpi rp_H0 rph lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 doc pretty copy t D
      Lamc peakc cntc ran most (conj HPRE1 (conj HRO (conj Hhi1 (conj Hrac1 HFZ)))) (HMNc HMN) HCL HCTX1 Ha0 Ha1 Ha2 Hpr Hdoc0
      (arms_tree_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) (cm_in_wf x t HIN) (cm_in_depth32 x t HIN) (cm_in_wlen x t _ HIN)
      HCOPY HLED Hcnt HRUN HRAN HRQAr HLIVEr HRQr HFRS HROOM HRP HFZ HOS4 HWR HCONS HUPc).
  - (* the callee's footprint: copy's window, a slot of the frame this function took *)
    intros a Hfa. destruct (Z.eqb_spec copy 0) as [E0|E0].
    + exfalso. exact (inFP_nil a Hfa).
    + apply inFP_cons in Hfa as [Hfa | Hfa]; [|exfalso; exact (inFP_nil a Hfa)].
      right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes CRT_CID) with 512.
      destruct Hcopy as [-> | ->]; [lia|]. fold F. unfold CRT_OFF_COPY in Hfa. lia. }
cbv beta. intros W2 c2 _
  (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2 & HJ1 & HP & HQ & HMN2).
replace (sp0 + o) with SP1 in HJ1 by (unfold o; lia).
(* the composed journal (at WS0 ++ WS1) at the budget kb + 32: arms_wild_budget's landing *)
destruct (HLAND ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1 HB0 HPW HJ2) as (WS & HJ2a & HBa).
(* the text's post, keyed on ReaderRes.jr_strtod, back at rp_sm *)
assert (HQ' : arms_rtt_Q rpi lyc Sc Wc (ms_mem ms) Lamc peakc cntc ran copy (negb (pretty =? 0))
  ly2 S2 Hp2 W2 regs2 mem2 md2) by (unfold arms_rtt_Q; rewrite HSM; exact HQ).
rewrite Hra. exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1 HFZ2 HFK2 HJ2a HBa HJ1 HP HQ' HMN2).
Qed.

(* ---- the live state after a round_trip_text call: the journal from the entry the call rule composed, the side
   facts from the text's post, the read-back words (saves, flag word, spill) above the callee's window or off its
   footprint, the frame's bytes present again by the frames law, copy's shadow kept by the frame clause; the block
   relations the caller gives per arm ---- *)
Lemma arms_live_after : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc copy
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Dx' Lam2 peak2 cnt2 own2 ran2 kbg kbg' WS WS1,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (copy = 0 \/ copy = frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2' (kj + k1) WS ->
  YCbqGwild.wbudget [] kbg' WS ->
  AJW STKR SP1 (if copy =? 0 then [] else [(copy, copy + 56)]) lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  room_live_cf S2 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 most own2 -> peakc <= peak2 ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) doc t D ->
  (forall bk, In bk Lamc -> In bk Lam2) ->
  Permutation Lam2 (Dx' ++ Lam) -> Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') ->
  (forall bk, In bk Dx' -> ~ In bk D) ->
  LIVE kbg' ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Dx' Lam2 peak2 cnt2 own2 ran2.
Proof.
clear HOS4.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc copy ly2 S2 Hp2 W2 mem2 md2 md2' k1 Dx' Lam2 peak2
  cnt2 own2 ran2 kbg kbg' WS WS1 HL Hcopy HJ2 HB2 HJ1 HMN12 HROOM2 HLED2 Hpk2 HND2 HLam HPm2 HPab2 HDap2.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPm. pose proof (crt_live_blocks_perm HL) as HPab.
pose proof (crt_live_dx_apart HL) as HDap. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSP.
pose proof (crt_live_copy_open HL) as HCS. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _).
pose proof HJ1 as (HAR2 & HLY1 & _ & _ & _ & HFR1 & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _ & _ & Etop & Eslo & Eshi & _).
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof arms_stk as (HS0 & HS1). destruct arms_sp1 as (Hs32 & Hs1 & Hs0).
destruct (arms_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (Hin3 & F32 & Fb1 & Fb2 & Fapp & Ffr & Fsh).
cbv zeta in Fb1, Fb2, Fapp, Ffr, Fsh, F32.
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 HARc HLY1) as (_ & Efa & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by apply Efa.
assert (EFL : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos) by (unfold flag_addr; rewrite EFF; reflexivity).
pose proof (crt_frame_flag_word HFRM) as Hflag.
set (F := frame_addr lyc CRT_CID pos) in *.
(* the call's footprint is copy's window or nothing *)
assert (HnFP : forall a, inFP (if copy =? 0 then [] else [(copy, copy + 56)]) a -> F + 224 <= a < F + 280).
{ intros a Ha. destruct (Z.eqb_spec copy 0) as [E0|E0]; [exfalso; exact (inFP_nil a Ha)|].
  apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
  destruct Hcopy as [-> | ->]; [lia|]. unfold CRT_OFF_COPY in Ha. lia. }
(* every byte at or above the realigned sp is above the callee's window: kept *)
assert (Kst : forall a, SP1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply G1; lia. }
(* the class-3 frame's bytes and shadow off copy's window: kept by the frame clause *)
assert (Kfr : forall a, (F <= a < F + 512 \/ shadow_addr F <= a < shadow_addr F + 64) -> ~ (F + 224 <= a < F + 280) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply (G4 CRT_CID pos a Hin3).
  - unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes CRT_CID) with 512. change (512 / 8) with 64. fold F. lia.
  - intros Hf. exact (Hn (HnFP a Hf)). }
(* copy's shadow bytes lie in the frame's shadow, far from copy's own window *)
assert (Hsh : forall s, shadow_addr (F + CRT_OFF_COPY) / 8 * 8 <= s < shadow_addr (F + CRT_OFF_COPY + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr F <= s < shadow_addr F + 64 /\ ~ (F + 224 <= s < F + 280)).
{ intros s Hs. unfold shadow_addr, CRT_OFF_COPY in *. unfold in_app, kLowShadowBeg, ASAN_CEIL in Fapp.
  unfold SHADOW_OFF in *. split; lia. }
refine {| crt_live_journal := ex_intro _ WS (conj HJ2 HB2); crt_live_side := _; crt_live_lam_perm := HPm2;
          crt_live_blocks_perm := HPab2; crt_live_dx_apart := HDap2; crt_live_saved := _;
          crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _; crt_live_copy_hull := _;
          crt_live_memnorm := _ |}.
{ refine {| crt_side_ledger := HLED2; crt_side_peak := _; crt_side_room := HROOM2; crt_side_arodata := _;
            crt_side_doc := HND2; crt_side_doc_blocks := _ |}.
  - lia.
  - intros a Hro Hno Her. rewrite (G3 a); [exact (HRO a Hro Hno Her) | | exact Hno | exact Her | |].
    + destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
    + intros Hps. exact (pst_not_ro_A a Hps Hro).
    + apply fp_spares_closed. apply sink_closed_pos. destruct (Z.eqb_spec copy 0) as [E0|E0]; [constructor|].
      constructor; [cbn [fst]; destruct Hcopy as [-> | ->]; [lia | unfold CRT_OFF_COPY; lia] | constructor].
  - intros bk Hbk; apply HLam; apply HDL; exact Hbk. }
{ intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros i Hi. apply Kst. lia. }
{ refine {| crt_frame_listed := _; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite HFR1; exact Hin3.
  - rewrite EF, EFL. rewrite <- Hflag. apply ts_rdword_keep. intros j Hj. fold F. apply Kfr; [left | ];
      change (fs_frame_bytes CRT_CID) with 512; lia.
  - intros a Ha. rewrite EF in Ha.
    assert (Hin2 : In (CRT_CID, pos) (frames S2)) by (rewrite HFR1; exact Hin3).
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CRT_CID pos HAR2 Hin2) as (_ & _ & Ffr2 & _).
    rewrite EF in Ffr2. exact (proj1 (Ffr2 a Ha)). }
{ unfold crt_spill. rewrite EF. eapply ts_vm_av; [|exact HSP]. intros i Hi. apply Kst. unfold CRT_SP_F. lia. }
{ rewrite EF. intros a Ha. destruct (HCS a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok]. rewrite <- Hs.
  fold F in Ha |- *. unfold CRT_OFF_COPY in Ha. apply Kfr.
  - right. unfold shadow_of_addr, shadow_addr. unfold SHADOW_OFF. lia.
  - unfold shadow_of_addr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Fapp. unfold SHADOW_OFF in *. lia. }
{ rewrite EF. intros s Hs. fold F in Hs |- *. destruct (Hsh s Hs) as [H1 H2]. rewrite (Kfr s (or_intror H1) H2).
  exact (HCH s Hs). }
intros Hm. exact (HMN12 (HMNc Hm)).
Qed.

(* a register a run did not write keeps its start value (S10TxString.v's tskeep) *)
Ltac arms_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* the kept registers carry a boundary's register snapshot (a call: the callee-saved ones; a run: the ones it did not
   write) *)
Lemma arms_dregs_pres : forall rg rg' F, DREGS rg F -> aregs_preserved rg rg' -> DREGS rg' F.
Proof.
clear HOS4.
intros rg rg' F HDR HP.
pose proof (crt_dregs_bregs HDR) as HBR.
refine {| crt_dregs_bregs := _; crt_dregs_s5 := _ |}.
- refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}.
  + rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. exact (crt_bregs_sp HBR).
  + rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. exact (crt_bregs_gp HBR).
  + rewrite (ts_ap rg rg' 4%bv HP) by ts_cs. exact (crt_bregs_tp HBR).
  + rewrite (ts_ap rg rg' 8%bv HP) by ts_cs. exact (crt_bregs_s0 HBR).
  + rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. exact (crt_bregs_s1 HBR).
  + rewrite (ts_ap rg rg' 18%bv HP) by ts_cs. exact (crt_bregs_s2 HBR).
  + rewrite (ts_ap rg rg' 20%bv HP) by ts_cs. exact (crt_bregs_s4 HBR).
  + rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. exact (crt_bregs_s3 HBR).
  + rewrite (ts_ap rg rg' 23%bv HP) by ts_cs. exact (crt_bregs_s7 HBR).
  + rewrite (ts_ap rg rg' 26%bv HP) by ts_cs. exact (crt_bregs_s10 HBR).
  + rewrite (ts_ap rg rg' 27%bv HP) by ts_cs. exact (crt_bregs_s11 HBR).
- rewrite (ts_ap rg rg' 21%bv HP) by ts_cs. exact (crt_dregs_s5 HDR).
Qed.
Definition ARMS_DREGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv.
Lemma arms_dregs_eq : forall rg rg' F, DREGS rg F -> (forall r, In r ARMS_DREGS -> getr rg' r = getr rg r) -> DREGS rg' F.
Proof.
clear HOS4.
intros rg rg' F HDR HK.
pose proof (crt_dregs_bregs HDR) as HBR. unfold ARMS_DREGS in HK.
refine {| crt_dregs_bregs := _; crt_dregs_s5 := _ |}.
- refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}.
  + rewrite (HK 2%bv) by (cbn [In]; tauto). exact (crt_bregs_sp HBR).
  + rewrite (HK 3%bv) by (cbn [In]; tauto). exact (crt_bregs_gp HBR).
  + rewrite (HK 4%bv) by (cbn [In]; tauto). exact (crt_bregs_tp HBR).
  + rewrite (HK 8%bv) by (cbn [In]; tauto). exact (crt_bregs_s0 HBR).
  + rewrite (HK 9%bv) by (cbn [In]; tauto). exact (crt_bregs_s1 HBR).
  + rewrite (HK 18%bv) by (cbn [In]; tauto). exact (crt_bregs_s2 HBR).
  + rewrite (HK 20%bv) by (cbn [In]; tauto). exact (crt_bregs_s4 HBR).
  + rewrite (HK 19%bv) by (cbn [In]; tauto). exact (crt_bregs_s3 HBR).
  + rewrite (HK 23%bv) by (cbn [In]; tauto). exact (crt_bregs_s7 HBR).
  + rewrite (HK 26%bv) by (cbn [In]; tauto). exact (crt_bregs_s10 HBR).
  + rewrite (HK 27%bv) by (cbn [In]; tauto). exact (crt_bregs_s11 HBR).
- rewrite (HK 21%bv) by (cbn [In]; tauto). exact (crt_dregs_s5 HDR).
Qed.
Lemma arms_live_md : forall lyc Sc Hpc Wc memc mdc mdc' kj pos Dx Lamc peakc cntc ownc ranc kbg WS,
  LIVE kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc' kj WS ->
  YCbqGwild.wbudget [] kbg WS ->
  LIVE kbg lyc Sc Hpc Wc memc mdc' kj pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc mdc' kj pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ HB.
exact {| crt_live_journal := ex_intro _ WS (conj HJ HB); crt_live_side := crt_live_side HL;
         crt_live_lam_perm := crt_live_lam_perm HL; crt_live_blocks_perm := crt_live_blocks_perm HL;
         crt_live_dx_apart := crt_live_dx_apart HL; crt_live_saved := crt_live_saved HL;
         crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
         crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
         crt_live_memnorm := crt_live_memnorm HL |}.
Qed.

Section arms.
(* the tail and the next slice, as this chain's two exits (Crt102Tail's crt102_tail; Crt102Rewrite's chain), at the
   contract's step relation SRr' SEGS RZ_cf *)
Hypothesis HTAIL : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  ATJ fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF rg memc mdc) QFF.
Hypothesis HNEXT : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  ATU fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_U_OFF rg memc mdc) QFF.

(* ---- copy's footprint across rtt (doc, 1): its call has copy = 0, so FP = [], and the journal keeps copy's node (the
   frame clause: a slot of the class-3 frame) and the bytes of its blocks Db (the block clause: harness blocks live at
   both ends, by the two ledgers). Both directions of the byte agreement: forward over the tree's whole footprint
   (writable after: the frame and the blocks are present at the new state), backward over the 56-byte node (writable
   before: the frame is present at the old state) ---- *)
Lemma arms_copy_agree : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos /\
  (forall a k, prh_lin Lam1 a k -> prh_lin Lam2 a k) /\
  (forall bk, In bk Db -> In bk Lam2) /\
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2)
    (pj_footR (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db) /\
  pj_agreeR SEGS (mrestrict (w_H W2) mem2) (mrestrict (w_H Wc) memc)
    (fun y => frame_addr lyc CRT_CID pos + CRT_OFF_COPY <= y < frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 56).
Proof.
clear HOS4.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  kb1 kb2 WS1 HL1 HL2 HJ1.
destruct (crt_live_journal HL1) as (WSj & HJ & HBj). pose proof (crt_live_lam_perm HL1) as HPm1.
pose proof (crt_frame_present (crt_live_frame HL1)) as Hfp1.
pose proof (crt_side_ledger (crt_live_side HL1)) as HLED1.
destruct (crt_live_journal HL2) as (? & (HAR2 & _) & _). pose proof (crt_live_lam_perm HL2) as HPm2.
pose proof (crt_frame_present (crt_live_frame HL2)) as Hfp2.
pose proof (crt_side_ledger (crt_live_side HL2)) as HLED2.
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & _ & G2 & _ & G4 & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 (proj1 HJ) HLY1) as (_ & Efa & _).
destruct (arms_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL1) as (Hin3 & _).
rewrite (Efa CRT_CID pos) in Hfp2.
assert (HDL : forall bk, In bk Db -> In bk Lam1 /\ In bk Lam2).
{ intros bk Hbk. split; [apply (Permutation_in _ (Permutation_sym HPm1)) | apply (Permutation_in _ (Permutation_sym HPm2))];
  apply in_or_app; left; exact Hbk. }
assert (Kfr : forall y, frame_addr lyc CRT_CID pos + CRT_OFF_COPY <= y < frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 56 ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y).
{ intros y Hy. apply (G4 CRT_CID pos y Hin3); [|apply inFP_nil].
  left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY in Hy. lia. }
split; [exact (Efa CRT_CID pos)|].
split.
{ intros a k Hk. unfold prh_lin in *. apply (Permutation_in _ (Permutation_sym HPm2)).
  apply (Permutation_in _ HPm1) in Hk. exact Hk. }
split; [intros bk Hbk; exact (proj2 (HDL bk Hbk))|].
split.
- intros y Hy. destruct Hy as [Hy | ([a k] & Hb & Hy)].
  + split.
    * apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2). exact (Kfr y Hy).
    * intros _. apply apresent_writable. apply Hfp2. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY in Hy. lia.
  + unfold pj_holdsR in Hy. cbn [fst snd] in Hy. destruct (HDL _ Hb) as [Hb1 Hb2].
    pose proof (proj1 (Forall_forall _ _)
      (prh_ledger_blocks B lyc Sc Hpc Wc memc Lam1 peak1 cnt1 SIZE_MAXZ ran1 most own1 HLED1) _ Hb1)
      as (Hk0 & Hab1 & _). cbn [fst snd] in Hk0, Hab1.
    pose proof (proj1 (Forall_forall _ _)
      (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 most own2 HLED2) _ Hb2)
      as (_ & Hab2 & _). cbn [fst snd] in Hab2.
    change (@cf_head CfParams_preset) with 16 in Hab1, Hab2.
    assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
    split.
    * apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2).
      replace y with ((a - 16) + (y - a + 16)) by lia. apply (G2 _ _ _ Hab1 Hab2); [rewrite Hrq; lia | apply inFP_nil].
    * intros _. apply apresent_writable.
      destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 _ _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpres & _).
      rewrite Hrq in Hpres. exact (proj1 (Hpres y ltac:(lia))).
- intros y Hy. split.
  + apply (mbyte_of_aview SEGS (w_H W2) (w_H Wc) mem2 memc). symmetry. exact (Kfr y Hy).
  + intros _. apply apresent_writable. apply Hfp1. change (fs_frame_bytes CRT_CID) with 512. unfold CRT_OFF_COPY in Hy. lia.
Qed.

(* ---- copy's compact tree across rtt (doc, 1) - this is how crt_copy_tree survives the second call ---- *)
Lemma arms_copy_keep : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  COPYT Wc memc Lam1 (frame_addr lyc CRT_CID pos) t Db ->
  COPYT W2 mem2 Lam2 (frame_addr ly2 CRT_CID pos) t Db.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  kb1 kb2 WS1 HL1 HL2 HJ1 HCT.
destruct (arms_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1
  Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1 HL1 HL2 HJ1) as (EF & Hlin & _ & Hag & _).
unfold crt_copy_tree in *. rewrite EF.
apply (arms_nodeR_lblk SEGS t _ (prh_lin Lam1)); [exact Hlin|].
exact (pj_nodeR_frame SEGS t _ _ (prh_lin Lam1) _ Db HCT Hag).
Qed.

(* ---- copy's ordered free list across rtt (doc, 1), at every depth bound nn above dd, by PRH_PjOrder.pj_foR_frame over
   the same agreement ---- *)
Lemma arms_fo_keep : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 (dd : nat) (Fo : list Z) kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall nn, (dd <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lam1) nn
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F /\ map (fun b => snd b + cf_head) F = Fo) ->
  forall nn, (dd <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) nn
     (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY) Db F /\ map (fun b => snd b + cf_head) F = Fo.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  dd Fo kb1 kb2 WS1 HL1 HL2 HJ1 HFO nn Hnn.
destruct (HFO nn Hnn) as (Fc & HFo & HM).
destruct (arms_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1
  Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1 HL1 HL2 HJ1) as (EF & _ & HDL2 & Hag & _).
rewrite EF. exists Fc. split; [|exact HM].
apply (PRH_PjOrder.pj_foR_frame SEGS nn _ _ (prh_lin Lam1) (prh_lin Lam2) _ Db Fc HFo); [|exact Hag].
intros a k Hin. unfold prh_lin. exact (HDL2 (a, k) Hin).
Qed.

(* ---- copy's header cap across rtt (doc, 1): a header read at the new state is the header at the old one
   (PRH_Reader.pj_hdrR_frame, backward over the 56-byte node) ---- *)
Lemma arms_cap_keep : forall lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1
    ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2 (N : Z) kb1 kb2 WS1,
  LIVE kb1 lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ->
  LIVE kb2 ly2 S2 Hp2 W2 mem2 md2' (kj + k1) pos Db Lam2 peak2 cnt2 own2 ran2 ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall ty num str kids keys n cap,
     pj_hdrR SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ty num str kids keys n cap ->
     cap = N) ->
  forall ty num str kids keys n cap,
    pj_hdrR SEGS (mrestrict (w_H W2) mem2) (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY) ty num str kids keys n cap ->
    cap = N.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1 Lam2 peak2 cnt2 own2 ran2
  N kb1 kb2 WS1 HL1 HL2 HJ1 HCAP ty num str kids keys n cap Hh.
destruct (arms_copy_agree lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 own1 ran1 ly2 S2 Hp2 W2 mem2 md2 md2' k1
  Lam2 peak2 cnt2 own2 ran2 kb1 kb2 WS1 HL1 HL2 HJ1) as (EF & _ & _ & _ & Hag').
rewrite EF in Hh. apply (HCAP ty num str kids keys n cap).
exact (pj_hdrR_frame SEGS _ _ _ ty num str kids keys n cap Hh Hag').
Qed.

(* ---- the join from a state where copy holds the compact tree over Db (C3: r = 0, t not an object): pj_free frees
   Db, copy's tree is crt_tree_J = t, its block sizes against tblk t up to permutation, its ordered free list fo t,
   its depth below DOC_D (Crt102Model.cm_in_depth_doc) ---- *)
Lemma arms_atJ_copy : forall fxJ ly2 S2 Hp2 W2 mem2 md2 kj2 pos Db Lam2 peak2 cnt2 rgJ,
  frm_zero (@YK11.fp_csr fxJ) -> fregs_kept_x fx fxJ ->
  LIVE (prh_wk F_check_round_trip) ly2 S2 Hp2 W2 mem2 md2 kj2 pos Db Lam2 peak2 cnt2 0 ran ->
  COPYT W2 mem2 Lam2 (frame_addr ly2 CRT_CID pos) t Db ->
  BREGS rgJ (frame_addr ly2 CRT_CID pos) -> getr rgJ 22 = w64 0 ->
  cnt2 = cnt + ck_crt_count t 0 -> CPOS S2 EVSJ -> (forall ms, t <> PjTree.JObj ms) ->
  Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk t) ->
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) DOC_D
     (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY) Db Fc /\ map (fun b => snd b + cf_head) Fc = PresetReqAt.fo t) ->
  ATJ fxJ ly2 S2 Hp2 W2 mem2 md2 kj2 pos Lam2 peak2 cnt2 0 ran Db rgJ 0.
Proof.
clear HOS4.
intros fxJ ly2 S2 Hp2 W2 mem2 md2 kj2 pos Db Lam2 peak2 cnt2 rgJ HFZ HFK HL HCT HBR R22 Ecnt HPOS Hn Htb HFO.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
refine {| crt_at_J_live := HL; crt_at_J_frm_zero := HFZ; crt_at_J_fregs := HFK; crt_at_J_bregs := HBR;
          crt_at_J_ret := R22; crt_at_J_copy_fd := _; crt_at_J_r0 := _; crt_at_J_count := _ |}.
- exact (arms_fd_mono SEGS _ _ _ _ _ _ (cm_in_depth_doc x t HIN) (arms_nodeR_fd SEGS t _ _ _ _ HCT)).
- reflexivity.
- exists 0. split; [lia|]. split; [intros; reflexivity|]. right.
  rewrite (arms_tree_J_nobj t Hn).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Ecnt|]. split; [exact HPOS|].
  split; [exact HCT|]. split; [exact Htb|]. split; [exact HFO|]. exact (cm_in_depth_doc x t HIN).
Qed.

(* ---- after rtt (doc, 1): R2 (+0x1c4, bnez a0) - taken (r = 1): arm C2, UNREACHABLE (round_trip_text's dead r = 1
   arm); else T (+0x1c8 .. +0x1e0), the inline shadow check of doc, `lw a0,0(s5)`, `addi a1,zero,6`, `bne a0,a1` -
   taken (not an object): +0x260 `mv s6,zero; j J`, arm C3; fall-through (an object): U (+0x1e4). `rpi` is rtt2's
   position: round_trip's first piece done ---- *)
Lemma arms_after_rtt2 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 rg1
    fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 rpi WS WS1,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE (prh_wk F_round_trip_text) lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 0 ran ->
  DREGS rg1 (frame_addr lyc CRT_CID pos) -> getr rg1 22 = w64 1 ->
  COPYT Wc memc Lam1 (frame_addr lyc CRT_CID pos) t Db ->
  (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  cnt1 = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk t) ->
  (forall nn, (PjTree.depth t <= nn)%nat -> exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lam1) nn
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Db F /\ map (fun b => snd b + cf_head) F = PresetReqAt.fo t) ->
  (forall ms, t = PjTree.JObj ms -> forall ty num str kids keys n cap,
     pj_hdrR SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) ty num str kids keys n cap ->
     cap = Z.of_nat (PresetReqAt.ncap (length ms))) ->
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS ->
  YCbqGwild.wbudget [] (prh_wk F_round_trip_text + prh_wk F_round_trip_text) WS ->
  AJW STKR SP1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  aregs_preserved rg1 regs2 ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) ->
  rp_sm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  rpi = (rp_i + length (PresetReqAt.rt_text rp_sm t false))%nat ->
  arms_rtt_Q rpi lyc Sc Wc memc Lam1 peak1 cnt1 ran 0 true ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_R2_OFF))) mem2 (YK11.seg_rom SEGS)) md2) QFF.
Proof.
clear HOS4.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 rg1 fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 rpi WS WS1 HFZ HFK HL
  HDR R22 HCT HFRESH HLSZ HNL Ecnt1 HTB HFO1 HCAP1 HFZ2 HFK2 HJ2 HB2 HJ1 HP HRUN0 HSM HCONS0 Erpi HQ HMN2.
(* round_trip_text's post: tround_trip_text_specX's DEAD r = 1 ARM - the text states `r = 0` in front of its arm
   split (HRTT_R1_DEAD), under its entry premise prh_cons_from *)
pose proof HQ as (HROOM2 & Lam2 & peak2 & cnt2 & ran2 & own2 & HLED2 & Hpk2 & HND2 & r & HR10 & HRTT_R1_DEAD & Harms).
pose proof (arms_dregs_pres _ _ _ HDR HP) as HDR2.
assert (R22' : getr regs2 22 = w64 1) by (rewrite (ts_ap rg1 regs2 22%bv HP) by ts_cs; exact R22).
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPm. pose proof (crt_live_blocks_perm HL) as HPab.
pose proof (crt_live_dx_apart HL) as HDap.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
assert (Hblk : Permutation Lam2 Lam1 /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc)).
{ destruct Harms as [(_ & _ & H1 & H2 & _) | (_ & _ & _ & _ & _ & Hc0 & _)]; [split; assumption | exact (Hc0 eq_refl)]. }
destruct Hblk as [HPm2 HPab2].
assert (Hr01 : r = 0 \/ r = 1) by (destruct Harms as [(-> & _) | (-> & _)]; [right | left]; reflexivity).
(* the live state after the second call: the walk still holds exactly Db beyond the entry's blocks *)
assert (HL2 : LIVE (prh_wk F_round_trip_text + prh_wk F_round_trip_text) ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Db Lam2
  peak2 cnt2 own2 ran2).
{ refine (arms_live_after lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 0 ran 0 ly2 S2 Hp2 W2 mem2 md2 md2 k1 Db Lam2
    peak2 cnt2 own2 ran2 _ _ _ _ HL (or_introl eq_refl) HJ2 HB2 HJ1 HMN2 HROOM2 HLED2 Hpk2 HND2 _ _ _ HDap).
  - intros bk Hbk. exact (Permutation_in _ (Permutation_sym HPm2) Hbk).
  - eapply perm_trans; [exact HPm2 | exact HPm].
  - eapply perm_trans; [exact HPab2 | exact HPab]. }
pose proof (arms_copy_keep lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 0 ran ly2 S2 Hp2 W2 mem2 md2 md2 k1 Lam2 peak2
  cnt2 own2 ran2 _ _ _ HL HL2 HJ1 HCT) as HCT2.
(* copy's ordered free list (at every depth bound above depth t) and its header cap, kept by the same agreement *)
pose proof (arms_fo_keep lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 0 ran ly2 S2 Hp2 W2 mem2 md2 md2 k1 Lam2 peak2
  cnt2 own2 ran2 (PjTree.depth t) _ _ _ _ HL HL2 HJ1 HFO1) as HFO2.
assert (HCAP2 : forall ms, t = PjTree.JObj ms -> forall ty num str kids keys n cap,
  pj_hdrR SEGS (mrestrict (w_H W2) mem2) (frame_addr ly2 CRT_CID pos + CRT_OFF_COPY) ty num str kids keys n cap ->
  cap = Z.of_nat (PresetReqAt.ncap (length ms))).
{ intros ms Et. exact (arms_cap_keep lyc Sc Hpc Wc memc mdc kj pos Db Lam1 peak1 cnt1 0 ran ly2 S2 Hp2 W2 mem2 md2 md2 k1
    Lam2 peak2 cnt2 own2 ran2 _ _ _ _ HL HL2 HJ1 (HCAP1 ms Et)). }
pose proof HJ1 as (_ & HLY1 & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 (proj1 HJ) HLY1) as (_ & Efa & _).
rewrite <- (Efa CRT_CID pos) in HDR2.
pose proof (crt_dregs_bregs HDR2) as HBR2. pose proof (crt_dregs_s5 HDR2) as R21.
pose proof (crt_bregs_sp HBR2) as R2. pose proof (crt_bregs_gp HBR2) as R3.
pose proof (crt_bregs_tp HBR2) as R4. pose proof (crt_bregs_s0 HBR2) as R8.
pose proof (crt_bregs_s1 HBR2) as R9. pose proof (crt_bregs_s2 HBR2) as R18.
pose proof (crt_bregs_s4 HBR2) as R20. pose proof (crt_bregs_s3 HBR2) as R19.
pose proof (crt_bregs_s7 HBR2) as R23. pose proof (crt_bregs_s10 HBR2) as R26.
pose proof (crt_bregs_s11 HBR2) as R27.
(* the document: its type word is its tag (pj_nodeR's header), its home a live fake frame of the entry *)
pose proof (arms_node_hdr SEGS _ _ _ _ _ HND2) as (Hty32 & Htyv).
pose proof (arms_home_keep _ _ _ _ _ _ _ _ _ HJ2) as (Hd8 & (cid' & pos' & Hfin' & Hfa1' & Hfa2') & HRA).
destruct (frames_bounds_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid' pos' (proj1 HJ2) Hfin') as (Fd1 & Fd2 & _).
pose proof (arms_tag_range t) as Htg.
set (E := TE regs regs2 [w64 (PjTree.tag t)]).
assert (X53 : bv_unsigned (ew E (xr 21)) = doc).
{ unfold E, xr. rewrite (te_cur regs regs2 _ 21%bv 21) by reflexivity. rewrite R21. apply unsigned_lit_small. lia. }
assert (X58 : bv_unsigned (ew E (xr 26)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs regs2 _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E64 : ew E 64 = w64 (PjTree.tag t)) by exact (te_more_lt regs regs2 [w64 (PjTree.tag t)] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = PjTree.tag t) by (rewrite E64; apply unsigned_lit_small; lia).
assert (A42 : bv_unsigned (ew E 42) = r).
{ unfold E. rewrite (te_cur regs regs2 _ 10%bv 10) by reflexivity. rewrite HR10. apply unsigned_lit_small. lia. }
unfold crt_cfg.
assert (HS : @st_ok_pi SEGS VAL fx' E (mkSS (CRT_PC_A + CRT_R2_OFF) cur_atoms
    [YP09.mkRegion (Some (xr 21)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 64 0))]] None
    (mkFacts [(xr 21, mkAF 0 (kHighMemEnd - 56) 3); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0); (64%nat, mkAF 0 6 0)] [] []))
  (restrict (w_H W2) (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_R2_OFF))) mem2 (YK11.seg_rom SEGS)))).
{ apply (@ts_st_ok fx'); try change (TE regs regs2 [w64 (PjTree.tag t)]) with E.
  - apply te_regs_ok.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (ts_rok E _ (xr 21) doc); [exact X53 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 4 (SOff 64 0) (PjTree.tag t));
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Htyv.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite X53, X58, X64.
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok SEGS (SOff (xr 26) 0) [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (X53' : bv_unsigned (ew E 53) = doc) by exact X53.
assert (X58' : bv_unsigned (ew E 58) = SHADOW_OFF) by exact X58.
subst E.
(* the runs carry the caller's journal at its budget WS (Crt102Kit's AJW runners) *)
pose (RUN := @Crt102Kit.crt_run_xw fx' rc SK A_prog_listing PL PA B PST ARx _ LAWS WS).
pose (RUNTO := @Crt102Kit.crt_run_to_xw fx' rc SK A_prog_listing PL PA B PST ARx _ LAWS WS).
pose (BR := YSRrG.paj_branchR (fx := fx') (rc := rc) (L := A_prog_listing) (PI := PA) RZW).
pose proof (arms_fregs_trans fx fxk fx' HFK HFK2) as HFKJ.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- (* R2 taken: a0 <> 0 - arm C2 is UNREACHABLE: round_trip_text (doc, 1) returns 0 by tround_trip_text_specX's DEAD
     r = 1 ARM (its post states r = 0, HRTT_R1_DEAD, under its entry premise prh_cons_from) *)
  rewrite branch_ne_U, !ts_U0, U_SLit, A42 in Hc. rewrite YP0m.zcanon_small in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  exfalso. exact (Hc HRTT_R1_DEAD).
- (* R2 not taken: a0 = 0, rtt (doc, 1) returned 0; T *)
  rewrite branch_ne_U, !ts_U0, U_SLit, A42 in Hc. rewrite YP0m.zcanon_small in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hr2z.
  destruct Harms as [(Er & _) | (Er & HOWN0 & Ecnt2 & Eran2 & (hist2 & HIFC2) & _)]; [exfalso; lia|].
  subst own2 ran2 rpi.
  paj_run_tok_x RUN HS HJ2 SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  { (* THE INLINE SHADOW CHECK of doc (A' +0x1c8 .. +0x1d4: srli a0,s5,3; add a0,a0,s10; lb a0,0(a0); bnez a0 to the slow
       path at +0x6e4). The token rule leaves exactly one obligation: doc's 4 bytes are addressable. doc's home is a
       live fake frame of the entry and its 56 bytes stay addressable (ck_obj_home, arms_home_keep), so the run takes
       the fall-through: the slow path at +0x6e4 (the re-check `(doc & 7) + 3 < shadow byte`) and its
       __asan_report_load4 are never entered. *)
    cbn [ms_mem mkst restrict]. rewrite !ts_U0. rewrite X58, X53'.
    exact (range_addressable_sub _ SHADOW_OFF doc 56 doc 4 HRA ltac:(lia) ltac:(lia)). }
  { eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  subst mem2. rename ms into ms1.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (A64 : bv_unsigned (ew E1 64) = PjTree.tag t) by (rewrite !ew_ewset_other by lia; exact X64) end.
  psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + (* bne taken: doc->type <> PJ_OBJECT, t is not an object: +0x260 `mv s6, zero; j J` - arm C3 *)
    (* the room position after both calls: round_trip's tail, pj_free (&copy) (arms_pos_J) *)
    rewrite branch_ne_U, !ts_U0, U_SLit, A64 in Hc. rewrite YP0m.zcanon_small in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_x RUNTO HS HJ2 SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_A + CRT_J_OFF).
    { eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ2.
    prreg HS (22%bv : bv 5) Q22.
    assert (X22 : getr (ms_regs ms) 22 = w64 0) by (rewrite Q22; reflexivity).
    assert (HDRJ : DREGS (ms_regs ms) (frame_addr ly2 CRT_CID pos)).
    { apply (arms_dregs_eq regs2); [exact HDR2|]. intros r0 Hr. unfold ARMS_DREGS in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [arms_keep HS|]); destruct Hr. }
    pmkst HS. rewrite HF.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] => replace n with (CRT_PC_A + CRT_J_OFF) by (vm_compute; reflexivity) end.
    apply (HTAIL fx' ly2 S2 Hp2 W2 (ms_mem ms1) _ (kj + k1) pos Lam2 peak2 cnt2 0 ran Db (ms_regs ms) 0).
    (* the count: both calls exact, and ck_crt_count has no object term for a non-object (Crt102Model.cm_arm_C3);
       copy's tree is t, its blocks Db against tblk t up to permutation (rtt1's r = 0 post, arms_tblk_of_rb), its
       ordered free list at the J field's depth DOC_D: the every-depth form at nn := DOC_D, depth t <= DOC_D
       (Crt102Model.cm_in_depth_doc) *)
    (* J's budget: 64 <= 66 = prh_wk F_check_round_trip (the brief's table: C3 lands at J, kb 66) *)
    exact (arms_atJ_copy fx' ly2 S2 Hp2 W2 (ms_mem ms1) _ (kj + k1) pos Db Lam2 peak2 cnt2 (ms_regs ms) HFZ2 HFKJ
      (arms_live_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (arms_live_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ2 HB2)
         arms_kb_rtt2) HCT2 (crt_dregs_bregs HDRJ) X22
      (cm_arm_C3 t 0 cnt cnt1 cnt2 (cm_tag_nobj t Hc) Ecnt1 Ecnt2)
      (arms_pos_J S2 hist2 (cm_tag_nobj t Hc) HSM HRUN0 HCONS0 HIFC2) (cm_tag_nobj t Hc) HTB
      (HFO2 DOC_D (cm_in_depth_doc x t (cm_in_intro x t HREAD HLENX HWL0 HWL1)))).
  + (* bne not taken: doc->type = PJ_OBJECT, t = JObj ms: the head of the inlined round_trip_rewrite, U *)
    rewrite branch_ne_U, !ts_U0, U_SLit, A64 in Hc. rewrite YP0m.zcanon_small in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    destruct (cm_tag_obj t Hc) as (mso & Ems).
    paj_run_to_tok_x RUNTO HS HJ2 SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_A + CRT_U_OFF).
    { eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ2.
    assert (HDRU : DREGS (ms_regs ms) (frame_addr ly2 CRT_CID pos)).
    { apply (arms_dregs_eq regs2); [exact HDR2|]. intros r0 Hr. unfold ARMS_DREGS in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [arms_keep HS|]); destruct Hr. }
    pose proof (arms_live_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ2 HB2) as HL2'.
    pmkst HS. rewrite HF.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] => replace n with (CRT_PC_A + CRT_U_OFF) by (vm_compute; reflexivity) end.
    apply (HNEXT fx' ly2 S2 Hp2 W2 (ms_mem ms1) _ (kj + k1) pos Db Lam2 peak2 cnt2 (ms_regs ms) mso).
    refine {| crt_at_U_live := HL2'; crt_at_U_frm_zero := HFZ2; crt_at_U_fregs := HFKJ;
              crt_at_U_dregs := HDRU; crt_at_U_obj := Ems;
              crt_at_U_tree_ok := arms_tree_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2';
              crt_at_U_copy := HCT2; crt_at_U_db_fresh := HFRESH; crt_at_U_db_lsz := HLSZ;
              crt_at_U_db_nlive := HNL; crt_at_U_cnt := _;
              (* the room position after both calls: the rewrite and pj_free (&copy) are left (arms_pos_U) *)
              crt_at_U_pos := arms_pos_U S2 hist2 mso Ems HSM HRUN0 HCONS0 HIFC2;
              (* copy's blocks against tblk t up to permutation: rtt1's r = 0 post (arms_tblk_of_rb) *)
              crt_at_U_copy_tblk := HTB;
              (* copy's header cap: rtt1's post in the CAP (pj_ncapR) form, kept across rtt2 (arms_cap_keep) *)
              crt_at_U_copy_cap := HCAP2 mso Ems;
              (* copy's ordered free list at every depth bound: rtt1's post in the FREEORD-COPY form
                 (arms_fo_of_frees), kept across rtt2 (arms_fo_keep); t = JObj mso *)
              crt_at_U_copy_fo := _ |}.
    * rewrite Ecnt2, Ecnt1; lia.
    * intros _ nn Hd. rewrite <- Ems in Hd |- *. exact (HFO2 nn Hd).
Qed.

(* ---- after rtt (doc, 0): R1 (+0x1a4, beqz a0). Taken (r = 0): s6 = 1 and the second call, at the position
   round_trip's first piece reached; not taken (r = 1): arm C1, UNREACHABLE (round_trip_text's dead r = 1 arm).
   rtt1 was made at rp_i (crt_pos at M, pre = []). The second call is arms_rtt_call, so this lemma takes its premise
   arms_wild_budget ---- *)
Lemma arms_after_rtt1 : arms_wild_budget ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos rg1 fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE 0%nat lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran ->
  DREGS rg1 (frame_addr lyc CRT_CID pos) ->
  rp_sm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS ->
  YCbqGwild.wbudget [] (prh_wk F_round_trip_text) WS ->
  AJW STKR SP1 (if (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) =? 0 then []
    else [(frame_addr lyc CRT_CID pos + CRT_OFF_COPY, frame_addr lyc CRT_CID pos + CRT_OFF_COPY + 56)])
    lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  aregs_preserved rg1 regs2 ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) ->
  arms_rtt_Q_k0 rp_i lyc Sc Wc memc Lam peak cnt ran (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) false
    ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
    (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_R1_OFF))) mem2 (YK11.seg_rom SEGS)) md2) QFF.
Proof.
intros HGAP fxk lyc Sc Hpc Wc memc mdc kj pos rg1 fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1 HFZ HFK HL HDR HSM HCONS0
  HFZ2 HFK2 HJ2 HB2 HJ1 HP HRUN0 HQ HMN2.
(* round_trip_text's post: tround_trip_text_specX's DEAD r = 1 ARM - the text states `r = 0` in front of its arm
   split (HRTT_R1_DEAD), under its entry premise prh_cons_from *)
pose proof HQ as (HROOM2 & Lam1 & peak1 & cnt1 & ran1 & own1 & HLED1 & Hpk1 & HND1 & r & HR10 & HRTT_R1_DEAD & Harms).
pose proof (arms_dregs_pres _ _ _ HDR HP) as HDR2.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPm. pose proof (crt_live_blocks_perm HL) as HPab.
pose proof (crt_live_dx_apart HL) as HDap.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (arms_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (_ & _ & Fb1 & _).
cbv zeta in Fb1.
assert (Hr01 : r = 0 \/ r = 1) by (destruct Harms as [(-> & _) | (-> & _)]; [right | left]; reflexivity).
unfold crt_cfg.
assert (HS : @st_ok_pi SEGS VAL fx' (TE regs regs2 []) (mkSS (CRT_PC_A + CRT_R1_OFF) cur_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_R1_OFF))) mem2 (YK11.seg_rom SEGS)))).
{ apply (@ts_st_ok fx'); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs regs2 []) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE regs regs2 [])) by apply te_env.
assert (A42 : bv_unsigned (ew (TE regs regs2 []) 42) = r).
{ rewrite (te_cur regs regs2 [] 10%bv 10) by reflexivity. rewrite HR10. unfold w64. apply unsigned_lit_small. lia. }
(* the runs carry the caller's journal at its budget WS (Crt102Kit's AJW runners) *)
pose (RUN := @Crt102Kit.crt_run_xw fx' rc SK A_prog_listing PL PA B PST ARx _ LAWS WS).
pose (RUNTO := @Crt102Kit.crt_run_to_xw fx' rc SK A_prog_listing PL PA B PST ARx _ LAWS WS).
pose (BR := YSRrG.paj_branchR (fx := fx') (rc := rc) (L := A_prog_listing) (PI := PA) RZW).
assert (HE2 : bv_unsigned (ew (TE regs regs2 []) 2) = sp0) by (rewrite (te_entry regs regs2 [] 2%bv 2) by reflexivity; reflexivity).
pose proof (crt_dregs_bregs HDR2) as HBR2. pose proof (crt_dregs_s5 HDR2) as R21.
pose proof (crt_bregs_sp HBR2) as R2. pose proof (crt_bregs_gp HBR2) as R3.
pose proof (crt_bregs_tp HBR2) as R4. pose proof (crt_bregs_s0 HBR2) as R8.
pose proof (crt_bregs_s1 HBR2) as R9. pose proof (crt_bregs_s2 HBR2) as R18.
pose proof (crt_bregs_s4 HBR2) as R20. pose proof (crt_bregs_s3 HBR2) as R19.
pose proof (crt_bregs_s7 HBR2) as R23. pose proof (crt_bregs_s10 HBR2) as R26.
pose proof (crt_bregs_s11 HBR2) as R27.
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* taken: a0 = 0, rtt (doc, 0) returned 0 with the compact read-back tree in copy over Db; s6 = 1, to RTT2 *)
  rewrite branch_eq_U, !ts_U0, U_SLit, A42 in Hc. rewrite YP0m.zcanon_small in Hc by lia. apply Z.eqb_eq in Hc.
  destruct Harms as [(E1 & _) | (Er & HOWN0 & Ecnt1 & Eran1 & (hist1 & HIFC1) & _ & Hcopy)]; [exfalso; lia|].
  destruct (Hcopy ltac:(unfold CRT_OFF_COPY; lia)) as (Db & HPm1 & Hfresh & Hlsz & HRB & Hnl & HPab1 & HCT1 & HFR1 & HCAP1).
  pose proof (cm_in_wf x t (cm_in_intro x t HREAD HLENX HWL0 HWL1)) as Hwf.
  (* the read-back's block sizes against tblk t up to permutation, from the text's reader-side conjunct *)
  pose proof (arms_tblk_of_rb Db false Hwf HRB) as HTB.
  (* copy's ordered free list against fo t at every depth bound, from the FREEORD-COPY form *)
  pose proof (arms_fo_of_frees _ _ _ Db Hwf HFR1) as HFO1.
  subst own1 ran1.
  (* the blocks the walk holds beyond the entry's are now Db, apart from the document's *)
  assert (Hfresh' : forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)).
  { intros a k Hin Hab. apply (Hfresh a k Hin). apply (Permutation_in _ (Permutation_sym HPab)). rewrite app_nil_r.
    exact Hab. }
  assert (HDap1 : forall bk, In bk Db -> ~ In bk D).
  { intros [a k] Hin HinD. pose proof (crt_side_doc_blocks HSD) as HDL.
    pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B lyc Sc Hpc Wc memc Lam peak cnt SIZE_MAXZ ran most 0 HLED)
      (a, k) (HDL _ HinD)) as (_ & Hab & _). exact (Hfresh a k Hin Hab). }
  assert (HL2 : LIVE (prh_wk F_round_trip_text) ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Db Lam1 peak1 cnt1 0 ran).
  { refine (arms_live_after lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran _ ly2 S2 Hp2 W2 mem2 md2 md2 k1 Db Lam1
      peak1 cnt1 0 ran _ _ _ _ HL (or_intror eq_refl) HJ2 HB2 HJ1 HMN2 HROOM2 HLED1 Hpk1 HND1 _ HPm1 _
      HDap1).
    - intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPm1)). apply in_or_app. right. exact Hbk.
    - eapply perm_trans; [exact HPab1|]. apply Permutation_app_tail. rewrite <- (app_nil_r (ablocks B ly S)). exact HPab. }
  paj_run_tok_x RUN HS HJ2 SHOK (0, 0).
  { apply awr_ok_nil. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  rewrite HF in HJ2.
  pose proof (arms_live_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ2 HB2) as HL2'.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
  prreg HS (22%bv : bv 5) Q22.
  assert (X10 : getr (ms_regs ms) 10 = w64 doc) by (rewrite Q10, <- R21; te_close).
  assert (X11 : getr (ms_regs ms) 11 = w64 1) by (rewrite Q11; reflexivity).
  assert (X12 : getr (ms_regs ms) 12 = w64 0) by (rewrite Q12; reflexivity).
  assert (X22 : getr (ms_regs ms) 22 = w64 1) by (rewrite Q22; reflexivity).
  assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_R2_OFF))) by (rewrite Q1; vm_compute; reflexivity).
  assert (HDR3 : DREGS (ms_regs ms) (frame_addr lyc CRT_CID pos)).
  { apply (arms_dregs_eq regs2); [exact HDR2|]. intros r0 Hr. unfold ARMS_DREGS in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [arms_keep HS|]); destruct Hr. }
  pose proof HJ1 as (_ & HLY1 & _).
  destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc ly2 (proj1 HJ) HLY1) as (_ & Efa & _).
  rewrite <- (Efa CRT_CID pos) in HDR3, HCT1, HFO1, HCAP1.
  pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as HIN.
  pose proof (prh_ledger_bounds B lyc Sc Hpc Wc memc Lam peak cnt SIZE_MAXZ ran most 0 HLED) as (_ & _ & Hcnt0 & _).
  (* rtt2's position, run events and consumer window: where rtt1's exact advance left the room, and round_trip's
     second piece (ck_rtt_evs_supply / arms_cons_split, from the run premise and the window crt_pos carries) *)
  assert (Hc0 : frame_addr lyc CRT_CID pos + CRT_OFF_COPY <> 0) by (unfold CRT_OFF_COPY; lia).
  pose proof (proj2 (ck_rtt_evs_supply rp_sm rp_x rp_os rp_i t _ Hc0 HRUN0)) as HRUN2.
  pose proof (proj2 (arms_cons_split _ Hc0 HCONS0)) as HCONS2.
  (* rtt2 at kb = prh_wk F_round_trip_text: 32 + 32 <= 66 *)
  refine (arms_rtt_call HGAP fx' 1 0 CRT_R2_OFF W2 (TE regs regs2 []) _ ms _ ly2 S2 Hp2 (kj + k1) pos Db Lam1 peak1 cnt1
    (rp_i + length (ck_rtt_evs rp_sm t false (frame_addr lyc CRT_CID pos + CRT_OFF_COPY)))%nat hist1
    (prh_wk F_round_trip_text) HFZ2 HS eq_refl _ HE2 _ arms_kb_rtt2 HDR3 X10 X11 X12 (or_intror eq_refl) (or_intror eq_refl) X1 (or_introl eq_refl) _ _ _ _
    HIFC1 HRUN2 HSM HCONS2 _).
  + reflexivity.
  + rewrite HF. exact HL2'.
  + rewrite Ecnt1. pose proof (cm_cnt_rtt1 x t cnt HIN ltac:(lia)). lia.
  + (* THE REQUEST BOUND of round_trip_text (doc, 1): Crt102Model.cm_rqa_rtt1, from the text's own RQA_crt t <= most *)
    exact (cm_rqa_rtt1 t most HRQA).
  + (* the copy over Db is live during the second call: Crt102Model.cm_copy_room_rtt / cm_live_rtt1 *)
    apply (cm_live_rtt1 t (blocks_bytes S) (blocks_bytes S2) HLIVE).
    rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S).
  pose proof (crt_live_blocks_perm HL2) as HPab2. rewrite (YCbq.bsum_perm _ _ HPab2), YCbq.bsum_app.
    pose proof (cm_copy_room_rtt t Db (cm_in_wf x t HIN) Hlsz Hnl). lia.
  + exact (cm_rq_rtt1 t HRQ).
  + intros fx'' ly3 S3 Hp3 W3 regs3 mem3 md3 k2 WS3 WS31 HFZ3 HFK3 HJ3 HB3 HJ31 HP3 HQ3 HMN3.
    rewrite HF in HJ31, HQ3, HMN3.
    exact (arms_after_rtt2 fx' ly2 S2 Hp2 W2 mem2 _ (kj + k1) pos Db Lam1 peak1 cnt1 (ms_regs ms) fx'' ly3 S3 Hp3 W3 regs3
      mem3 md3 k2 _ WS3 WS31 HFZ2 (arms_fregs_trans fx fxk fx' HFK HFK2) HL2' HDR3 X22 HCT1 Hfresh' Hlsz Hnl Ecnt1 HTB HFO1
      HCAP1 HFZ3 HFK3
      HJ3 HB3 HJ31 HP3 HRUN0 HSM HCONS0 (f_equal (fun l => (rp_i + length l)%nat) (arms_ck_rtt_nz rp_sm t false _ Hc0))
      HQ3 HMN3).
- (* not taken: a0 <> 0 - arm C1 is UNREACHABLE: round_trip_text (doc, 0) returns 0 by tround_trip_text_specX's DEAD
     r = 1 ARM (its post states r = 0, HRTT_R1_DEAD, under its entry premise prh_cons_from) *)
  rewrite branch_eq_U, !ts_U0, U_SLit, A42 in Hc. rewrite YP0m.zcanon_small in Hc by lia. apply Z.eqb_neq in Hc.
  exfalso. exact (Hc HRTT_R1_DEAD).
Qed.

(* ---- M (+0x194): a0 = doc, a1 = 0, a2 = &copy, jal round_trip_text (RTT1), at rp_i with the whole of round_trip to
   come (crt_pos at M, Crt102Entry's continuation). rtt1's post in the TEXT's form is carried into the form the
   segment lemmas read by arms_rtt_bridge (from the cut's own conjuncts). Its last premise is arms_wild_budget (the
   premise of arms_rtt_call, both calls), discharged by arms_wild_budget_goal below (kb round) ---- *)
Lemma arms_at_M : forall fxk lyc Sc Hpc Wc memc mdc kj pos rg,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE 0%nat lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran ->
  DREGS rg (frame_addr lyc CRT_CID pos) ->
  COPYZ Wc memc (frame_addr lyc CRT_CID pos) ->
  CPOS Sc (PresetReqAt.round_trip rp_sm t) ->
  arms_wild_budget ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_M_OFF rg memc mdc) QFF.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HCZ HPOS HGAP.
destruct (arms_pos_entry Sc HPOS) as (HSM & hist0 & HIFC0 & HRUN0 & HCONS0).
unfold crt_cfg.
assert (HS : @st_ok_pi SEGS VAL fxk (TE regs rg []) (mkSS (CRT_PC_A + CRT_M_OFF) cur_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_M_OFF))) memc (YK11.seg_rom SEGS)))).
{ apply (@ts_st_ok fxk); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
destruct (crt_live_journal HL) as (WS0 & HJ & HB0).
pose proof (crt_dregs_bregs HDR) as HBR. pose proof (crt_dregs_s5 HDR) as R21.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
(* the run carries the journal at its budget WS0 (Crt102Kit's AJW runner) *)
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS WS0).
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ apply awr_ok_nil. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rewrite HF in HJ.
pose proof (arms_live_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ HB0) as HL1.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
assert (X10 : getr (ms_regs ms) 10 = w64 doc) by (rewrite Q10, <- R21; te_close).
assert (X11 : getr (ms_regs ms) 11 = w64 0) by (rewrite Q11; reflexivity).
assert (X12 : getr (ms_regs ms) 12 = w64 (frame_addr lyc CRT_CID pos + CRT_OFF_COPY)) by (rewrite Q12, <- R20; te_close).
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + CRT_R1_OFF))) by (rewrite Q1; vm_compute; reflexivity).
assert (HDR1 : DREGS (ms_regs ms) (frame_addr lyc CRT_CID pos)).
{ apply (arms_dregs_eq rg); [exact HDR|]. intros r Hr. unfold ARMS_DREGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [arms_keep HS|]); destruct Hr. }
assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg [] 2%bv 2) by reflexivity; reflexivity).
pose proof (crt_live_side HL) as HSD. pose proof (crt_live_lam_perm HL) as HPm.
pose proof (crt_live_blocks_perm HL) as HPab.
destruct (arms_frame_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL) as (_ & _ & Fb1 & _). cbv zeta in Fb1.
assert (Hbb : blocks_bytes Sc = blocks_bytes S).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S). rewrite (bsum_perm _ _ HPab), bsum_app.
  cbn [ck_hblks map]. unfold bsum at 2. cbn [fold_right]. lia. }
(* rtt1's run events and consumer window: round_trip's first piece (ck_rtt_evs_supply / arms_cons_split, from the
   run premise and the window crt_pos carries) *)
assert (Hc0 : frame_addr lyc CRT_CID pos + CRT_OFF_COPY <> 0) by (unfold CRT_OFF_COPY; lia).
pose proof (proj1 (ck_rtt_evs_supply rp_sm rp_x rp_os rp_i t _ Hc0 HRUN0)) as HRUN1.
pose proof (proj1 (arms_cons_split _ Hc0 HCONS0)) as HCONS1.
(* rtt1 at kb = 0 (the brief's table: M at 0): 0 + 32 <= 66 *)
refine (arms_rtt_call HGAP fxk 0 (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) CRT_R1_OFF Wc (TE regs rg []) _ ms _ lyc Sc
  Hpc kj pos [] Lam peak cnt rp_i hist0 0%nat HFZ HS eq_refl _ HE2 _ arms_kb_rtt1 HDR1 X10 X11 X12 (or_introl eq_refl) (or_introl eq_refl)
  X1 (or_intror eq_refl) _ _ _ _ HIFC0 HRUN1 HSM HCONS1 _).
- reflexivity.
- rewrite HF. exact HL1.
- lia.
- (* THE REQUEST BOUND of round_trip_text (doc, 0): Crt102Model.cm_rqa_rtt0, from the text's own RQA_crt t <= most *)
  exact (cm_rqa_rtt0 t most HRQA).
- exact (cm_live_rtt0 t (blocks_bytes S) (blocks_bytes Sc) HLIVE ltac:(lia)).
- exact (cm_rq_rtt0 t HRQ).
- intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1 HFZ2 HFK2 HJ2 HB2 HJ1 HP HQ HMN2.
  rewrite HF in HJ1, HQ, HMN2.
  exact (arms_after_rtt1 HGAP fxk lyc Sc Hpc Wc memc _ kj pos (ms_regs ms) fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS WS1 HFZ
    HFK HL1 HDR1 HSM HCONS0 HFZ2 HFK2 HJ2 HB2 HJ1 HP HRUN0 (arms_rtt_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HQ) HMN2).
Qed.
End arms.

(* ---- THE WILD BUDGET, DISCHARGED (kb round): arms_wild_budget from the text's entry room HWR0 (PRH_FnCheck.v:1366).
   The room: the live state's journal is at a budget WS with wfresh [] WS <= kb, so the entry room 66 leaves
   66 - wfresh [] WS >= 66 - kb >= 32 at Sc (YCbqGwild.ajournal_xw_roomR, wild_room_le). The landing: the call rule's
   journal at WS0 ++ WS1 is at the budget kb + 32 (YCbqGwild.wbudget_app). ---- *)
Lemma arms_wild_budget_goal : arms_wild_budget.
Proof using HWR0.
unfold arms_wild_budget. intros kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc HL Hkb.
destruct (crt_live_journal HL) as (WS & HJ & HB). unfold YCbqGwild.wbudget in HB. split.
- apply (YCbqGwild.wild_room_le _ _ (prh_wk F_check_round_trip - YCbqGwild.wfresh [] WS)); [clear - HB Hkb; lia|].
  eapply YCbqGwild.ajournal_xw_roomR; [exact HJ | exact HWR0 | clear - HB Hkb; lia].
- intros ly2 S2 Hp2 W2 mem2 md2 k1 WS0 WS1 HB0 HB1 HJ2. exists (WS0 ++ WS1). split; [exact HJ2|].
  exact (YCbqGwild.wbudget_app [] kb (prh_wk F_round_trip_text) WS0 WS1 HB0 HB1).
Qed.

(* ---- THE ARMS OF check_round_trip, image A' (the cuts M -> R1 -> R2 -> T): from the cut M the run reaches QF, given
   that it does from every crt_at_J state (the join; Crt102Tail's crt102_tail) and from every crt_at_U state (the
   inlined round_trip_rewrite; Crt102Rewrite's chain). C1 (rtt (doc, 0) = 1) and C2 (rtt (doc, 1) = 1) are
   UNREACHABLE by tround_trip_text_specX's dead r = 1 arm; C3 (doc->type <> PJ_OBJECT) lands in crt_at_J's r = 0 arm,
   the object case in crt_at_U. The M-side premises are exactly Crt102Entry's continuation (crt_live at kb = 0), the
   room position last (crt_pos Sc (round_trip rp_sm t), with the strtod tie and the consumer window). Both r = 0 exits
   name copy's block sizes against tblk t up to permutation, from round_trip_text's reader-side r = 0 conjunct by
   PresetFreeFo.rd_blocks_wdoc and PresetReqAtNoMiss.fo_tblk (arms_tblk_of_rb); copy's free order and header cap come
   from the landing cut's own copy-arm conjuncts (FREEORD-COPY verbatim, PRH_FnCheck.v:1290-1293; CAP from pj_ncapR,
   :1301) through arms_rtt_bridge. CLOSED (kb round): arms_at_M's last premise arms_wild_budget is
   arms_wild_budget_goal. ---- *)
Lemma crt102_arms :
  (forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
     ATJ fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF rg memc mdc) QFF) ->
  (forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
     ATU fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_U_OFF rg memc mdc) QFF) ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos rg,
  frm_zero (@YK11.fp_csr fxk) -> fregs_kept_x fx fxk ->
  LIVE 0%nat lyc Sc Hpc Wc memc mdc kj pos [] Lam peak cnt 0 ran ->
  DREGS rg (frame_addr lyc CRT_CID pos) ->
  COPYZ Wc memc (frame_addr lyc CRT_CID pos) ->
  CPOS Sc (PresetReqAt.round_trip rp_sm t) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_M_OFF rg memc mdc) QFF.
Proof.
intros HT HN fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HCZ HPOS.
exact (arms_at_M HT HN fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HCZ HPOS arms_wild_budget_goal).
Qed.

End g.
End f.
End w.

Print Assumptions arms_at_M.
Print Assumptions arms_rtt_call.
Print Assumptions arms_rtt_bridge.
Print Assumptions crt_tree_vis_keep.
(* kb round: the wild budget is discharged, so the slice and its named item are constants (Qed) *)
Check crt102_arms.
Check arms_wild_budget_goal.
Print Assumptions crt102_arms.
Print Assumptions arms_wild_budget_goal.

(* the FPState elaboration check (rule of the walk's owner, 2026-10-29, amended: Print for Prop-bodied definitions,
   Check for theorems; implicits on, notations off), re-run on every build. In the post every constant that takes an
   FPState must read the contract's entry fx (it binds no other), in the theorems every QF / crt_at_J / crt_at_U must
   read fx and every fregs_kept_x fx then the boundary's own float state. *)
Set Printing Implicit.
Unset Printing Notations.
Print arms_rtt_Q.
Print arms_rtt_Q_k0.
Print arms_wild_budget.
Check @arms_at_M.
Check @arms_after_rtt2.
Set Printing Notations.
Unset Printing Implicit.
