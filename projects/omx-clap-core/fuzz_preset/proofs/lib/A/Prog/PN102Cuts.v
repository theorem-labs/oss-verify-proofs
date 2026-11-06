(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PN102Cuts.v, with its module paths changed; 174 of its 323 lines of code are new or changed and 163 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE CUT TABLE of
   the walk of parse_noting (A' 0x81f14, 120 bytes, 30 instructions, frame 48; row N10-PNA). STATEMENTS ONLY: the
   entry record of the batch kit's text, the six cuts and the six segment statements, and the listing witnesses of the cut pcs.
   There is no Admitted, no Axiom and no Parameter in this file.
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; R24Pna CONFIRM 2026-10-29 18:2xZ; own signed walk 13970867e0c9, its one
   announced re-bind). This file: the cut table of that walk.
   THE BATCH KIT'S RE-BIND: a Theorem Labs lane's signed A' file of the same role (a working branch 13970867e0c9),
   re-fit to the batch kit's cut (commit 7cdbb61b5fa0) as the B' twin was re-fit
   (a working branch c7276d935095 lib/B/Prog/PN102B<same role>.v, read back at PI_prog_A / prh_img_A).
   The cut pcs are the signed walk's (unchanged).

   SOURCES (record keys).
   - Program text: the merged #102 source fuzz_preset.c :498-507 (provenance/port/projects/omx-clap-core/fuzz_preset.c)
     `live = fuzz_alloc_live (); rc = pj_parse (text, size, doc); if (fuzz_alloc_ran_out ()) check_reject_clean (rc,
     doc, live); return rc;`.
   - LISTING: lib/A/Listing_prog.v / PAImg_prog.v (a Theorem Labs lane, A' v3; slot k = byte offset 4k from
     LLVMFuzzerTestOneInput). parse_noting is slot 589 (PAImg_prog.v A_entry_parse_noting); its 30 slots, read on the
     listing (and on the unstripped twin's objdump):
       +0x00 addi sp,sp,-48; +0x04 .. +0x14 sd ra,40 / s0,32 / s1,24 / s2,16 / s3,8 (sp); +0x18 mv s0,a2;
       +0x1c mv s2,a1; +0x20 mv s3,a0; +0x24 jal fuzz_alloc_live;                                    [S1]
       +0x28 mv s1,a0; +0x2c mv a0,s3; +0x30 mv a1,s2; +0x34 mv a2,s0; +0x38 jal pj_parse;              [S2]
       +0x3c mv s2,a0; +0x40 jal fuzz_alloc_ran_out;                                                    [S3]
       +0x44 beqz a0, +0x58;                                                                            [S4]
       +0x48 mv a0,s2; +0x4c mv a1,s0; +0x50 mv a2,s1; +0x54 jal check_reject_clean;                    [S5]
       +0x58 mv a0,s2; +0x5c .. +0x6c ld ra / s0 / s1 / s2 / s3; +0x70 addi sp,sp,48; +0x74 ret          [S6]
     No ASan check remains in the body: its only memory accesses are the ten of its own frame. Section 6 checks
     every call slot, the branch slot and the ret slot on the listing by vm_compute (PL_prog_A).
   - The batch kit's TEXTS (the kit's cut 7cdbb61b5fa0): the statement lib/A/PRH_FnCheck.v
     tparse_noting_specX :596-730; the callees lib/A/PRH_FnAlloc.v tfuzz_alloc_live_specX (S1, owner a Theorem Labs lane) and
     tfuzz_alloc_ran_out_specX (S3, owner a Theorem Labs lane); lib/A/PRH_FnPj.v tpj_parse_specX (S2, owned by the kit owner a Theorem Labs lane);
     PRH_FnCheck.v tcheck_reject_clean_specX :566-580 (S5, owned by the kit owner). S4 and S6 call nothing.
   - THE STATEMENT. The walk proves the batch kit's tparse_noting_specX ITSELF (PRH_FnCheck.tparse_noting_specX), with no _FIX
     twin and no premise of its own. Against the signed walk's tparse_noting_exactX_FIX (13970867e0c9 PN102Cuts.v
     :160-219), the batch kit:
       DROPS rp_sm .. rp_hist, `rp_sm = ReaderRes.jr_strtod`, iface_room_pos and prh_run_at at entry (the position
         is now a post-implication, quantified over every run: the post's two `forall sm x os i H0 hist` conjuncts);
       DROPS DW: `prh_univ_closure B CTX0` (no data words) and FIX (4) `In (text + len) DW` are gone - pj_parse takes
         a cursor set CW instead (tpj_parse_specX CTX0 CW), met here by pn_cw X (section 2b);
       DROPS FIX (5) F6 `doc + 56 + 8 <= alloc_ceiling`: tcheck_reject_clean_specX's doc premise is now src_rd, whose
         own bound `doc + 56 <= alloc_ceiling` ck_out_ok's wdest_ok gives (PRH_Base.v src_rd);
       KEEPS FIX P4.2 `RQ_pj_parse tb <= most` as its own premise;
       ADDS the premises `wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S)` and the two room counts
         (pkR of the secondary and of class 24 along the all-granted events); the post at a budget, fpostFbm
         (wbudget [] (prh_wk F_parse_noting)); the exact live set; THE OUTCOME conjunct (the granted reading under
         the run hypothesis); prh_oks with (prh_ev_reqs tr) most; peak' with prh_refused_peak; and on the Some arm
         the reader's block sizes rd_blocks (rtr ok tb), the free order pj_foR / pj_frees and K0-CAP pj_ncapR, the
         last three from tpj_parse_specX's Some arm (F8's source).
       K0-CFHEAD-16 is NOT a Section hypothesis of this walk: the text guards both of its HEAD-sized conjuncts (the
         reader's block sizes, the free order) with `cf_head = PresetReqAt.HEAD ->` itself.
     THE RE-HIDING MOVE AND THE HULL (the text's current form): the text concludes SRr' segs RZ_cf (its run crosses
       pj_parse, which frees: YA0nH.SRr', every continuation at wle' segs RZ_cf); its post fpostFbm is already at
       wle'; it takes the hull budget PresetHullBudget.hull_budget S (parse_evs .. tb []) (pn_pre's pp_hull) and its
       post states the hull use (pn_Q's pn_hull). The budget is pj_parse's own at the call (the state at S2 is the
       entry's); pj_parse's post gives the use at S3, which the later cuts keep.
   - THE CALLEE pj_parse's CW (S2): pn_cw X below, ONE TRACE PER CURSOR FREE SITE, the one arm of each conjunct
     of PRH_Base.prh_cw_pj (the cursor end text + len for parse_items, the never-written slot word at pj_parse's
     sp - pi_frame F_pj_parse for parse_string). |pn_cw X| = 2 = prh_wk F_parse_noting at A' (pn_free_sites_A,
     pn_wk_A), so the room of the text's premise pays it (YCbqGwild.wild_room_set) and the post's budget is met by
     normalising pj_parse's budget to pn_cw X (YCbqGwild.ajournal_xw_norm). (On A' the frees actually store the
     code-word traces, which are fixed; the text quantifies pj_parse at every CW, HPJ, so this CW is as good.)

   THE CUTS. Each cut is a predicate on the world and the configuration at a pc of the body, stated over the entry
   record pnx (section 2): the journal of parse_noting from its entry (STK_parse_noting, FP [(doc, doc + 56)]) at a
   budget WS ([] before pj_parse, pn_cw X after it) and at a world relation (wle before pj_parse, pn_frame; wle' segs
   RZ_cf after it, pn_frameR), the frame (sp = entry sp - 48, the five saved words at entry sp - 8
   .. - 40, every other callee-saved register as at entry), the float state (frm 0, fs kept), the memnorm keep, the
   read-only view, and the cut's own registers, ledger and reading (and the hull use after pj_parse). Segment Sk is
   the statement `cut k -> SRr .. (cut k + 1)` (SRr' segs RZ_cf for S2, which crosses pj_parse); S4 branches to S5 or
   S6; S6 ends in the post of the batch kit's text (pn_post). The cut S2 also states that
   pj_parse's slot word (the entry sp - 96) is the entry's, which S2's CW needs and S1 gives.
   Numerals: 48 (the frame, LENGTH), 8 .. 40 (the save slots, LENGTH), the instruction offsets (LENGTH), 56 (struct pj),
   instruction words in the witnesses. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG01cf YG00cf YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoom
  PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnReader PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. The pcs of the body, as offsets from parse_noting's entry (LENGTHs read on the listing, section 6). *)
Definition PN_FRAME : Z := 48.
Definition PN_CALL_LIVE : Z := 0x24.   (* jal fuzz_alloc_live *)
Definition PN_S2 : Z := 0x28.          (* fuzz_alloc_live returns: mv s1,a0 *)
Definition PN_CALL_PJ : Z := 0x38.     (* jal pj_parse *)
Definition PN_S3 : Z := 0x3c.          (* pj_parse returns: mv s2,a0 *)
Definition PN_CALL_RO : Z := 0x40.     (* jal fuzz_alloc_ran_out *)
Definition PN_S4 : Z := 0x44.          (* fuzz_alloc_ran_out returns: beqz a0, +0x58 *)
Definition PN_S5 : Z := 0x48.          (* the ran-out arm: mv a0,s2 *)
Definition PN_CALL_CRC : Z := 0x54.    (* jal check_reject_clean *)
Definition PN_S6 : Z := 0x58.          (* the join (beqz's target and check_reject_clean's return): mv a0,s2 *)
Definition PN_RET : Z := 0x74.         (* ret *)

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------- *)
(* 1. THE TEXT THIS WALK PROVES: the batch kit's tparse_noting_specX (lib/A/PRH_FnCheck.v :596-730 on the kit's cut 7cdbb61b5fa0) AS IT IS.
      It is not restated here; pn_intro below reads it into the walk's entry record. *)

(* ---------------------------------------------------------------------- *)
(* 2. THE ENTRY RECORD: every binder of the batch kit's text, by name. *)
Record pnx : Type := mkPnx {
  px_most : Z; px_own : Z;
  px_ly : alayout; px_S : astate; px_Hp : list Z; px_W : world segs; px_regs : bvmap 5 word;
  px_mem : word -> option byte; px_md : Model; px_ch : list (Z * Z * Z);
  px_text : Z; px_tb : list Z; px_doc : Z; px_Lam : list (Z * Z); px_peak : Z; px_cnt : Z; px_fail : Z; px_ran : Z }.
Definition pn_len (X : pnx) : Z := Z.of_nat (length (px_tb X)).

(* The batch kit's premises, each by name, in the text's order *)
Record pn_pre (CTX0 : list (list Z)) (X : pnx) : Prop := {
  pp_fpre : fpre B ARx STK_parse_noting (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_regs X) (px_mem X) (px_md X) (px_ch X);
  pp_mn : YAkMemnorm.memnorm segs (px_mem X);
  pp_univ : prh_univ_closure B CTX0;
  pp_a0 : getr (px_regs X) 10 = w64 (px_text X);
  pp_a1 : getr (px_regs X) 11 = w64 (pn_len X);
  pp_a2 : getr (px_regs X) 12 = w64 (px_doc X);
  pp_len : pn_len X < 2 ^ 40;
  pp_text0 : 0 < px_text X;
  pp_texthi : px_text X + pn_len X < 2 ^ 62;
  pp_src : src_rd (px_W X) (px_mem X) (px_text X) (px_tb X);
  pp_home : PRH_FnReader.prhReader_home B (px_ly X) (px_S X) (px_Hp X) (px_Lam X) (px_text X) (pn_len X);
  pp_maxrun : Z.of_nat (PjRoundTrip.maxrun (px_tb X)) < 2 ^ 30;
  pp_doc8 : px_doc X mod 8 = 0;
  pp_out : ck_out_ok B STK_parse_noting (px_ly X) (px_S X) (px_W X) (px_regs X) (px_mem X) (px_doc X) 56;
  pp_ran : px_ran X = 0;
  pp_ledger : prh_ledger B (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_Lam X) (px_peak X) (px_cnt X)
    (px_fail X) (px_ran X) (px_most X) (px_own X);
  pp_cnt : px_cnt X + 2 * pn_len X + 2 < 2 ^ 64 - 1;
  pp_live : blocks_bytes (px_S X) + PRH_FnPj.LIVE_pj_parse (px_tb X) <= LIVE_MAX;
  pp_rq : PRH_FnPj.RQ_pj_parse (px_tb X) + cf_head < cf_malloc_max;
  pp_most : PRH_FnPj.RQ_pj_parse (px_tb X) <= px_most X;
  pp_frames : Z.of_nat (length (frames (px_S X))) <= ck_FRAMES_CAP - FR_parse_noting;
  pp_frm : ck_frm0;
  pp_room : room_live_cf (px_S X);
  pp_wild : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot (px_S X));
  pp_sec : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (px_S X)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV;
  pp_c24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (px_S X)))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV;
  (* THE HULL BUDGET of the batch kit's text (route (b)): the room for the reading's all-granted events, the list the room
     counts name; it is the budget pj_parse's text takes at the call (S2: the state is the entry's) *)
  pp_hull : PresetHullBudget.hull_budget (px_S X) (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) [])
}.

(* The batch kit's post, its body over the reading's data with the return register as an argument r10 *)
Definition pn_R (X : pnx) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) (ok : list bool)
  (res : option PjTree.jv) (tr : list PjGrammar.ev) (r10 : word)
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) : Prop :=
  PjGrammar.jr_run ReaderRes.jr_strtod (px_tb X) ok = (res, tr) /\
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (px_S X)))
       (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) ok)) /\
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (px_S X) ->
       PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) ok) ->
       exists hist', PresetRoomPos.iface_room_pos sm x os
         (i + length ((PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) ok)))%nat H0 hist' S') /\
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (px_S X) ->
       PRH_Base.prh_run_at sm x os i (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) []) ->
       PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) [])) ->
       (px_fail X < px_cnt X \/ px_cnt X + ck_ncalls (px_tb X) <= px_fail X) ->
       ran' = 0 /\ PjGrammar.jr_run ReaderRes.jr_strtod (px_tb X) [] = (res, tr) /\
       PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) ok = PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) [] /\
       exists hist', PresetRoomPos.iface_room_pos sm x os
         (i + length (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) []))%nat H0 hist' S') /\
  prh_oks ok (px_cnt X) (px_fail X) (PjGrammar.calls tr) (prh_ev_reqs tr) (px_most X) 0 ran' /\
  cnt' = px_cnt X + Z.of_nat (PjGrammar.calls tr) /\
  ReaderRes.fail_after (px_cnt X) (px_fail X) (PjGrammar.calls tr) fail' /\
  peak' = Z.max (Z.max (px_peak X) (Ledger.lsum (px_Lam X) + ReaderRes.hpeak tr))
    (prh_refused_peak ok (px_cnt X) (px_fail X) (PjGrammar.calls tr)
       (map (Z.add (Ledger.lsum (px_Lam X))) (prh_ev_helds (PRH_FnPj.prhPj_ptrace (px_tb X))))) /\
  ReaderRes.hpeak tr <= 224 * pn_len X + 16384 /\
  (px_cnt X <= px_fail X < px_cnt X + ck_ncalls (px_tb X) -> res = None) /\
  (ran' <> 0 -> res = None) /\
  (ran' = 0 -> px_fail X < px_cnt X \/ px_cnt X + ck_ncalls (px_tb X) <= px_fail X ->
     res = ck_read (px_tb X) /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls (px_tb X)) /\
  bytes_at W' mem' (px_text X) (px_tb X) /\
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' (px_most X) (px_own X) /\
  match res with
  | Some t =>
      r10 = w64 0 /\
      exists D, Permutation Lam' (D ++ px_Lam X) /\
        Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr /\
        (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) D)
           (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod ok (px_tb X)))) /\
        (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
           exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n (px_doc X) D F /\
             map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok (px_tb X)) /\
        (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B (px_ly X) (px_S X))) /\
        Permutation (ablocks B ly' S') (ablocks B (px_ly X) (px_S X) ++ ck_hblks D) /\
        pj_nodeR segs (rdW W' mem') (prh_lin Lam') (px_doc X) t D /\
        pj_ncapR segs (rdW W' mem') (px_doc X) t
  | None =>
      r10 = w64 (-1) /\ Permutation Lam' (px_Lam X) /\ Permutation (ablocks B ly' S') (ablocks B (px_ly X) (px_S X)) /\
      pj_zeroR segs (rdW W' mem') (px_doc X)
  end.

(* THE HULL USE of the batch kit's post, from the entry state: at most the reading's all-granted events. pj_parse's post states
   it at S3; fuzz_alloc_ran_out and check_reject_clean keep the state, and no callee after pj_parse takes a hull
   budget, so the cuts S3 .. S6 carry it and nothing is paid between the calls *)
Definition pn_hull (X : pnx) (S' : astate) : Prop :=
  PresetHullBudget.hull_used (px_S X) S' (PresetReqAt.parse_evs ReaderRes.jr_strtod (px_tb X) []).

(* the hull use and the live room, then the reading's data, in the text's order *)
Definition pn_Q (X : pnx) : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) ->
  Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    pn_hull X S' /\
    room_live_cf S' /\ exists Lam' peak' cnt' fail' ran' ok res tr,
      pn_R X Lam' peak' cnt' fail' ran' ok res tr (getr regs' 10) ly' S' Hp' W' mem'.

(* the post of the batch kit's text: fpostFbm, whose journal is at wle' segs RZ_cf (PRH_Base.v, the AFTER-FREE-ONLY families) *)
Definition pn_post (X : pnx) : world segs -> config -> Prop :=
  fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_parse_noting)) STK_parse_noting [(px_doc X, px_doc X + 56)]
    (px_regs X) (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) (pn_Q X).

(* pn_R's conjuncts the segments read, BY NAME (the batch kit grew pn_R; read it through these, never positionally) *)
Lemma pnR_ledger : forall X Lam' peak' cnt' fail' ran' ok res tr r10 ly' S' Hp' W' mem',
  pn_R X Lam' peak' cnt' fail' ran' ok res tr r10 ly' S' Hp' W' mem' ->
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' (px_most X) (px_own X).
Proof.
intros X Lam' peak' cnt' fail' ran' ok res tr r10 ly' S' Hp' W' mem'
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.
Lemma pnR_ran_none : forall X Lam' peak' cnt' fail' ran' ok res tr r10 ly' S' Hp' W' mem',
  pn_R X Lam' peak' cnt' fail' ran' ok res tr r10 ly' S' Hp' W' mem' -> ran' <> 0 -> res = None.
Proof.
intros X Lam' peak' cnt' fail' ran' ok res tr r10 ly' S' Hp' W' mem'
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.
Lemma pnR_none : forall X Lam' peak' cnt' fail' ran' ok tr r10 ly' S' Hp' W' mem',
  pn_R X Lam' peak' cnt' fail' ran' ok None tr r10 ly' S' Hp' W' mem' ->
  r10 = w64 (-1) /\ Permutation Lam' (px_Lam X) /\ Permutation (ablocks B ly' S') (ablocks B (px_ly X) (px_S X)) /\
  pj_zeroR segs (rdW W' mem') (px_doc X).
Proof.
intros X Lam' peak' cnt' fail' ran' ok tr r10 ly' S' Hp' W' mem'
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H.
Qed.

(* The batch kit's text from the walk's form: one SRr' segs RZ_cf per entry record (the text's conclusion: its run crosses
   pj_parse, which frees) *)
Lemma pn_intro : forall CTX0,
  (forall X, pn_pre CTX0 X ->
     SRr' segs YGcfRehidePost.RZ_cf (px_W X) (cfg_at segs (pa_sigma AS_parse_noting) (px_regs X) (px_mem X) (px_md X))
       (pn_post X)) ->
  tparse_noting_specX B ARx SK CTX0.
Proof.
intros CTX0 H. unfold tparse_noting_specX.
intros most own ly S Hp W regs mem md ch text tb doc Lam peak cnt fail ran
  Hpre Hmn Huniv H10 H11 H12 Hlen Ht0 Hthi Hsrc Hhome Hmax Hd8 Hout Hran Hled Hcnt Hlive Hrq Hmost
  Hfr Hfrm Hroom Hwild Hsec Hc24 Hhull.
pose (X := mkPnx most own ly S Hp W regs mem md ch text tb doc Lam peak cnt fail ran).
exact (H X (Build_pn_pre CTX0 X Hpre Hmn Huniv H10 H11 H12 Hlen Ht0 Hthi Hsrc Hhome Hmax Hd8 Hout Hran
  Hled Hcnt Hlive Hrq Hmost Hfr Hfrm Hroom Hwild Hsec Hc24 Hhull)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2b. pj_parse's CURSOR SET at this call (S2): one trace per cursor free site, the one arm of each conjunct of
       PRH_Base.prh_cw_pj - parse_items' with the cursor end text + len, parse_string's with the never-written slot
       word at pj_parse's sp - pi_frame F_pj_parse = the entry sp - 96, whose value is the entry's (pn_cut_S2's last
       conjunct). *)
Definition pn_slotw (X : pnx) : Z :=
  match rdword (aview segs (w_H (px_W X)) (px_mem X)) (spZ (px_regs X) - pi_frame F_parse_noting - pi_frame F_pj_parse)
  with Some w => w | None => 0 end.
Definition pn_cw (X : pnx) : list (list Z) :=
  map (fun r => prh_trace (pc_free_ra0 (as_code B)) r [px_text X + pn_len X]) (prh_free_sites F_parse_items) ++
  map (fun r => prh_trace (pc_free_ra0 (as_code B)) r [pn_slotw X]) (prh_free_sites F_parse_string).

(* pn_cw X meets prh_cw_pj at pj_parse's entry, from the slot word's equation: PRH_Base.prh_cw_pj names exactly one
   trace per cursor function (no code-word disjunct) - parse_items' by the cursor end, parse_string's by the slot
   word *)
Lemma pn_cw_pj : forall X (W' : world segs) mem' (regs' : bvmap 5 word),
  spZ regs' - pi_frame F_pj_parse = spZ (px_regs X) - pi_frame F_parse_noting - pi_frame F_pj_parse ->
  rdword (aview segs (w_H W') mem') (spZ (px_regs X) - pi_frame F_parse_noting - pi_frame F_pj_parse) =
    rdword (aview segs (w_H (px_W X)) (px_mem X)) (spZ (px_regs X) - pi_frame F_parse_noting - pi_frame F_pj_parse) ->
  prh_cw_pj B (pn_cw X) W' mem' regs' (px_text X) (pn_len X).
Proof.
intros X W' mem' regs' Esp Eslot. split.
- intros r Hr. apply in_or_app. left. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
- intros r Hr w0 Hw. rewrite Esp, Eslot in Hw.
  apply in_or_app. right. apply in_map_iff. exists r. split; [|exact Hr].
  unfold pn_slotw. rewrite Hw. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE FRAME AT A CUT: the journal from the entry at budget WS, sp 48 below the entry sp, the five saved words,
      every other callee-saved register as at entry, the float state (frm 0, fs0-fs11 kept), the memnorm keep, the
      read-only view. *)
Definition pn_frame (X : pnx) (fy : YK11.FPState) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) (ly' : alayout) (S' : astate) (Hp' : list Z) (k : Z)
  (WS : list (list Z)) : Prop :=
  ajournal_xw (SK := SK) segs B prh_pst ARx STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
    (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly' S' Hp' W' mem' md' k WS /\
  spZ regs' = spZ (px_regs X) - PN_FRAME /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 8) (raZ (px_regs X)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 16) (bv_unsigned (getr (px_regs X) 8)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 24) (bv_unsigned (getr (px_regs X) 9)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 32) (bv_unsigned (getr (px_regs X) 18)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 40) (bv_unsigned (getr (px_regs X) 19)) /\
  (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
     getr regs' (Z_to_bv 5 r) = getr (px_regs X) (Z_to_bv 5 r)) /\
  YK0o.frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy /\
  (YAkMemnorm.memnorm segs (px_mem X) -> YAkMemnorm.memnorm segs mem') /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').

(* pn_frame over a world relation R: a COPY of pn_frame's body with the journal ajournal_xwR R (the segment proofs
   unfold pn_frame and read its body, so pn_frame stays); pn_frame_R_wle checks by reflexivity that pn_frame is
   pn_frameR at wle. The cuts before pj_parse use pn_frame (wle); the cuts after it use pn_frameR at the text's
   relation wle' segs RZ_cf, since pj_parse frees (its text concludes SRr' segs RZ_cf). *)
Definition pn_frameR (R : world segs -> world segs -> Prop) (X : pnx) (fy : YK11.FPState) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (k : Z) (WS : list (list Z)) : Prop :=
  ajournal_xwR (SK := SK) segs B prh_pst ARx R STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
    (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly' S' Hp' W' mem' md' k WS /\
  spZ regs' = spZ (px_regs X) - PN_FRAME /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 8) (raZ (px_regs X)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 16) (bv_unsigned (getr (px_regs X) 8)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 24) (bv_unsigned (getr (px_regs X) 9)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 32) (bv_unsigned (getr (px_regs X) 18)) /\
  rd64 (aview segs (w_H W') mem') (spZ (px_regs X) - 40) (bv_unsigned (getr (px_regs X) 19)) /\
  (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
     getr regs' (Z_to_bv 5 r) = getr (px_regs X) (Z_to_bv 5 r)) /\
  YK0o.frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy /\
  (YAkMemnorm.memnorm segs (px_mem X) -> YAkMemnorm.memnorm segs mem') /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').
Lemma pn_frame_R_wle : forall X fy W' regs' mem' md' ly' S' Hp' k WS,
  pn_frame X fy W' regs' mem' md' ly' S' Hp' k WS = pn_frameR (@wle segs) X fy W' regs' mem' md' ly' S' Hp' k WS.
Proof. reflexivity. Qed.

(* the configuration at offset off of the body, at float state fy *)
Definition pn_cfg (fy : YK11.FPState) (off : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  : config :=
  cfg_at (fx := fy) segs (pa_sigma AS_parse_noting + off) regs' mem' md'.

(* ---------------------------------------------------------------------- *)
(* 4. THE CUTS. S1 is the entry itself: pn_pre at cfg_at (pa_sigma AS_parse_noting). *)
(* S2 (+0x28, fuzz_alloc_live returned): s0 = doc, s2 = len, s3 = text, a0 = g_live; the allocator state, the blocks
   and the ledger as at entry; the journal at the empty budget; and pj_parse's slot word, the entry sp - 96, as at
   entry (pn_cw's arm 2) *)
Definition pn_cut_S2 (X : pnx) : world segs -> config -> Prop :=
  fun W' c => exists regs' mem' md' ly' S' Hp' k,
    c = pn_cfg fx PN_S2 regs' mem' md' /\ pn_frame X fx W' regs' mem' md' ly' S' Hp' k [] /\
    getr regs' 8 = w64 (px_doc X) /\ getr regs' 18 = w64 (pn_len X) /\ getr regs' 19 = w64 (px_text X) /\
    getr regs' 10 = w64 (Ledger.lsum (px_Lam X)) /\
    S' = px_S X /\ Hp' = px_Hp X /\ ablocks B ly' S' = ablocks B (px_ly X) (px_S X) /\
    prh_ledger B ly' S' Hp' W' mem' (px_Lam X) (px_peak X) (px_cnt X) (px_fail X) (px_ran X) (px_most X) (px_own X) /\
    rdword (aview segs (w_H W') mem') (spZ (px_regs X) - pi_frame F_parse_noting - pi_frame F_pj_parse) =
      rdword (aview segs (w_H (px_W X)) (px_mem X)) (spZ (px_regs X) - pi_frame F_parse_noting - pi_frame F_pj_parse).

(* S3 (+0x3c, pj_parse returned; the float state is pj_parse's): s0 = doc, s1 = g_live at entry, the reading's data
   with the return code in a0; the journal at the budget pn_cw X and at the relation wle' segs RZ_cf; the hull use *)
Definition pn_cut_S3 (X : pnx) : world segs -> config -> Prop :=
  fun W' c => exists fy regs' mem' md' ly' S' Hp' k Lam' peak' cnt' fail' ran' ok res tr,
    c = pn_cfg fy PN_S3 regs' mem' md' /\
    pn_frameR (wle' segs YGcfRehidePost.RZ_cf) X fy W' regs' mem' md' ly' S' Hp' k (pn_cw X) /\
    getr regs' 8 = w64 (px_doc X) /\ getr regs' 9 = w64 (Ledger.lsum (px_Lam X)) /\
    pn_hull X S' /\ room_live_cf S' /\ pn_R X Lam' peak' cnt' fail' ran' ok res tr (getr regs' 10) ly' S' Hp' W' mem'.

(* S4 (+0x44, fuzz_alloc_ran_out returned): the return code in s2, g_ran_out in a0 *)
Definition pn_cut_S4 (X : pnx) : world segs -> config -> Prop :=
  fun W' c => exists fy regs' mem' md' ly' S' Hp' k Lam' peak' cnt' fail' ran' ok res tr,
    c = pn_cfg fy PN_S4 regs' mem' md' /\
    pn_frameR (wle' segs YGcfRehidePost.RZ_cf) X fy W' regs' mem' md' ly' S' Hp' k (pn_cw X) /\
    getr regs' 8 = w64 (px_doc X) /\ getr regs' 9 = w64 (Ledger.lsum (px_Lam X)) /\ getr regs' 10 = w64 ran' /\
    pn_hull X S' /\ room_live_cf S' /\ pn_R X Lam' peak' cnt' fail' ran' ok res tr (getr regs' 18) ly' S' Hp' W' mem'.

(* S5 (+0x48, the reading ran out: g_ran_out <> 0) *)
Definition pn_cut_S5 (X : pnx) : world segs -> config -> Prop :=
  fun W' c => exists fy regs' mem' md' ly' S' Hp' k Lam' peak' cnt' fail' ran' ok res tr,
    c = pn_cfg fy PN_S5 regs' mem' md' /\
    pn_frameR (wle' segs YGcfRehidePost.RZ_cf) X fy W' regs' mem' md' ly' S' Hp' k (pn_cw X) /\
    getr regs' 8 = w64 (px_doc X) /\ getr regs' 9 = w64 (Ledger.lsum (px_Lam X)) /\ ran' <> 0 /\
    pn_hull X S' /\ room_live_cf S' /\ pn_R X Lam' peak' cnt' fail' ran' ok res tr (getr regs' 18) ly' S' Hp' W' mem'.

(* S6 (+0x58, the join): the return code in s2 *)
Definition pn_cut_S6 (X : pnx) : world segs -> config -> Prop :=
  fun W' c => exists fy regs' mem' md' ly' S' Hp' k Lam' peak' cnt' fail' ran' ok res tr,
    c = pn_cfg fy PN_S6 regs' mem' md' /\
    pn_frameR (wle' segs YGcfRehidePost.RZ_cf) X fy W' regs' mem' md' ly' S' Hp' k (pn_cw X) /\
    pn_hull X S' /\ room_live_cf S' /\ pn_R X Lam' peak' cnt' fail' ran' ok res tr (getr regs' 18) ly' S' Hp' W' mem'.

(* ---------------------------------------------------------------------- *)
(* 5. THE SEGMENTS, each with the callee text it uses as its premise (pj_parse's at every CW: the call supplies
      pn_cw X). S2 crosses pj_parse, whose text concludes SRr' segs RZ_cf, so S2 does too; S1 runs before it and
      S3 .. S6 call no freeing function, so they stay plain SRr (lifted into the walk by YA0nH.SRr_SRr'). *)
Definition pn_seg_S1_stmt (CTX0 : list (list Z)) : Prop :=
  tfuzz_alloc_live_specX B ARx SK ->
  forall X, pn_pre CTX0 X ->
  SRr segs (px_W X) (cfg_at segs (pa_sigma AS_parse_noting) (px_regs X) (px_mem X) (px_md X)) (pn_cut_S2 X).
Definition pn_seg_S2_stmt (CTX0 : list (list Z)) : Prop :=
  (forall CW : list (list Z), tpj_parse_specX B ARx SK CTX0 CW) ->
  forall X W' c, pn_pre CTX0 X -> pn_cut_S2 X W' c -> SRr' segs YGcfRehidePost.RZ_cf W' c (pn_cut_S3 X).
Definition pn_seg_S3_stmt (CTX0 : list (list Z)) : Prop :=
  (forall fy : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fy) B ARx SK) ->
  forall X W' c, pn_pre CTX0 X -> pn_cut_S3 X W' c -> SRr segs W' c (pn_cut_S4 X).
Definition pn_seg_S4_stmt (CTX0 : list (list Z)) : Prop :=
  forall X W' c, pn_pre CTX0 X -> pn_cut_S4 X W' c ->
  SRr segs W' c (fun W'' c'' => pn_cut_S5 X W'' c'' \/ pn_cut_S6 X W'' c'').
Definition pn_seg_S5_stmt (CTX0 : list (list Z)) : Prop :=
  (forall fy : YK11.FPState, tcheck_reject_clean_specX (fx := fy) B ARx SK) ->
  forall X W' c, pn_pre CTX0 X -> pn_cut_S5 X W' c -> SRr segs W' c (pn_cut_S6 X).
Definition pn_seg_S6_stmt (CTX0 : list (list Z)) : Prop :=
  forall X W' c, pn_pre CTX0 X -> pn_cut_S6 X W' c -> SRr segs W' c (pn_post X).
End X.

(* ---------------------------------------------------------------------- *)
(* 6. THE LISTING WITNESSES at A' (PL_prog_A of lib/A/PAImg_prog.v, the listing lib/A/Listing_prog.v): parse_noting's
      byte offset in the whole-program listing, its call slots with their callees, the branch, the ret. *)
Definition PN_SLOT0 : Z := PAImg_prog.A_prog_sigma AS_parse_noting - Listing_prog.A_prog_base.
Lemma pn_slot_live : YP0a.plookup (@pl_tpi _ PAImg_prog.PL_prog_A) (PN_SLOT0 + PN_CALL_LIVE) =
  Some (PCall AS_fuzz_alloc_live (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma pn_slot_pj : YP0a.plookup (@pl_tpi _ PAImg_prog.PL_prog_A) (PN_SLOT0 + PN_CALL_PJ) =
  Some (PCall AS_pj_parse (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma pn_slot_ro : YP0a.plookup (@pl_tpi _ PAImg_prog.PL_prog_A) (PN_SLOT0 + PN_CALL_RO) =
  Some (PCall AS_fuzz_alloc_ran_out (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma pn_slot_crc : YP0a.plookup (@pl_tpi _ PAImg_prog.PL_prog_A) (PN_SLOT0 + PN_CALL_CRC) =
  Some (PCall AS_check_reject_clean (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
(* +0x44 beqz a0, +0x14 (to +0x58); +0x74 ret (jalr zero, 0(ra)) *)
Lemma pn_slot_br : YP0a.plookup (@pl_tpi _ PAImg_prog.PL_prog_A) (PN_SLOT0 + PN_S4) = Some (PW 0x50a63).
Proof. vm_compute. reflexivity. Qed.
Lemma pn_slot_ret : YP0a.plookup (@pl_tpi _ PAImg_prog.PL_prog_A) (PN_SLOT0 + PN_RET) = Some (PW 0x8067).
Proof. vm_compute. reflexivity. Qed.
(* the frames are the kit's generated own-frame lengths at A' (lib/A/PRH_Img.v): parse_noting 48, pj_parse 48, and the
   two accessors 0 (so their calls leave every word below the caller's sp as it was) *)
Lemma pn_frame_A : @pi_frame PRH_Img.prh_img_A F_parse_noting = PN_FRAME.
Proof. vm_compute. reflexivity. Qed.
Lemma pn_frame_pj_A : @pi_frame PRH_Img.prh_img_A F_pj_parse = 48.
Proof. vm_compute. reflexivity. Qed.
Lemma pn_frame_live_A : @pi_frame PRH_Img.prh_img_A F_fuzz_alloc_live = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma pn_frame_ro_A : @pi_frame PRH_Img.prh_img_A F_fuzz_alloc_ran_out = 0.
Proof. vm_compute. reflexivity. Qed.
(* the cursor free sites at A': one per cursor function, so |pn_cw X| = 2 = prh_wk F_parse_noting *)
Lemma pn_free_sites_A : length (@prh_free_sites PRH_Img.prh_img_A F_parse_items) = 1%nat /\
  length (@prh_free_sites PRH_Img.prh_img_A F_parse_string) = 1%nat.
Proof. split; vm_compute; reflexivity. Qed.
Lemma pn_wk_A : prh_wk F_parse_noting = 2%nat.
Proof. reflexivity. Qed.

(* the closure of the reading lemma: no Axiom *)
Print Assumptions pn_intro.
