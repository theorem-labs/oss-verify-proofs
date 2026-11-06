(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset (both images; generic over the listing and the PAImg): THE ONE HOME of the PROVISIONAL
   GRANTED forms of the kit texts the walk of LLVMFuzzerTestOneInput calls after check_no_overread (a Theorem Labs lane's request
   18:21Z). Each is replaced by the kit's restated text (with its grant condition) by citation when it lands; the kit owner proves its
   corollaries against exactly these bytes.
   WHY (a Theorem Labs lane's decision 18:08Z, record fix 9a4f89c34639): after cut_cno the cuts keep only the no-refusal arms; a
   the kit text's refusal arm is not yet excluded by ec_hyps' ech_noref, because the texts do not take a grant condition.
   Until the kit owner restates them, a row that meets such an arm carries ONE named theorem argument: that text word for word
   with the refusal disjunct deleted.
   DECISION (A) (owner 22:35Z; the rule-2 review of 1301c67aaef0): the batch kit states the refusal arm DEAD under named
   premises (the entry-keyed crt / crcs texts under rp_sm = jr_strtod and the consumer window prh_cons_from; the
   post-form texts' outcome clauses under the window and the pick condition), so the granted forms of
   check_round_trip and check_reject_clean_starved are RETIRED (rows LL4 / LL5b / LL5c cite ec_texts' batch-kit texts). What
   remains here. NO LONGER PROVISIONAL for the first two: each is DERIVED from the batch kit's text in lib/A/Prog/Ent102OfPost.v
   (Qed, zero hypotheses), so a row citing it owes nothing:
   - tcheck_no_overread_grantedX: the entry-keyed form with own' = 0, under `rp_x = x` and R1
     `rp_i = length (PresetRun.hruns rp_sm rp_x rp_os)`. R1 is REQUIRED (measured): the batch kit's post gives own' = 0 only by its
     copies clause (PRH_FnCheck.v:801-804), whose window `prh_cons_from .. rp_i 3` holds only at the call boundary; the
     exact form without own' = 0 needs no R1. Derived: Ent102OfPost.tcheck_no_overread_grantedX_of_post.
   - tparse_noting_grantedX: the entry-keyed form with `ran' = 0`, under the batch kit's outcome-clause premises (the window over
     the reading's events and the pick condition); `ran' = 0` is the batch kit's own outcome conjunct (PRH_FnCheck.v:678), so no
     grant condition and no ec_noref is needed. Derived: Ent102OfPost.tparse_noting_grantedX_of_post.
   - tcheck_as_written_grantX: the batch kit's text's r = 0 arm under its window `prh_cons_from .. rp_i 2`, with the entry
     position in place of the batch kit's two room counts (PresetRoomCounts.counts_of_room_pos_rl gives them). Row LL3. DERIVED:
     Ent102OfPost.tcheck_as_written_grantX_of_post (Qed, zero hypotheses); neither text is budgeted (both post
     fpostFm), so this one takes no wild room.
   Both derived texts carry THE BATCH KIT'S WILD ROOM premise and its BUDGETED post (prh_wk per callee), as the cut file's texts do.
   THE RE-HIDING MOVE AND THE HULL (the primed callee texts of PRH_FnCheck.v): each text the three are derived from
   concludes SRr' segs RZ_cf (check_no_overread frees, so every later lane runs at wle') and takes the hull budget of
   its all-granted events (tcheck_no_overread_specX, tparse_noting_specX, tcheck_as_written_specX). The three granted
   forms state the same SRr' and take that hull premise word for word; tcheck_as_written_grantX also takes
   `(length rp_os <= 4)%nat`, which with its position and run gives the callee text's run position at entry (HPOS).
   The walk pays each hull from its position (the cut file's ech_hull_pay).
   rule 24: proves no function (kind: statement text, PROVISIONAL). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnReader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation ck_frm0 := (@PRH_FnCheck.ck_frm0 fx).



Definition tparse_noting_grantedX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk) most own,
  forall ly S Hp W regs mem md ch text (tb : list Z) doc Lam peak cnt fail ran,
  let len := Z.of_nat (length tb) in
  rp_sm = ReaderRes.jr_strtod ->
  fpre B ARx STK_parse_noting ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 text -> getr regs 11 = w64 len -> getr regs 12 = w64 doc ->
  len < 2 ^ 40 -> 0 < text -> text + len < 2 ^ 62 ->
  src_rd W mem text tb -> PRH_FnReader.prhReader_home B ly S Hp Lam text len ->
  Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 ->
  doc mod 8 = 0 -> ck_out_ok B STK_parse_noting ly S W regs mem doc 56 ->
  ran = 0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> cnt + 2 * len + 2 < 2 ^ 64 - 1 ->
  blocks_bytes S + PRH_FnPj.LIVE_pj_parse tb <= LIVE_MAX -> PRH_FnPj.RQ_pj_parse tb + cf_head < cf_malloc_max ->
  PRH_FnPj.RQ_pj_parse tb <= most ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_parse_noting -> ck_frm0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* EXACT (1): the reading's model events are the next ones of the run *)
  PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.parse_evs rp_sm tb []) ->
  (* The batch kit's outcome-clause premises (PRH_FnCheck.v:680-681; PRH_OfPost.v's header (iii); rule-2 review (a)): the
     reading's events are consumer events of the run, and no injected failure falls in the reading's window *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.parse_evs rp_sm tb [])) ->
  (fail < cnt \/ cnt + ck_ncalls tb <= fail) ->
  (* THE WILD ROOM and THE BUDGETED POST (the batch kit, PRH_FnCheck.v:637 / :648) *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S) ->
  (* THE HULL BUDGET of the reading's all-granted events (tparse_noting_specX's, word for word) *)
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod tb []) ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_parse_noting) regs mem md)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_parse_noting))
      STK_parse_noting [(doc, doc + 56)] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       (* EXACT (2): the position advanced by exactly those events *)
       exists Lam' peak' cnt' fail' ran' ok res tr,
       (* the advance is CONDITIONAL on the reading's outcomes agreeing with the model's all-granted run: an
          injected refusal (fail = cnt) makes no allocator call (a Theorem Labs lane, owner 18:3xZ) *)
       (PRH_FnReader.prhReader_agree ok [] (PjGrammar.calls tr) ->
          exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (PresetReqAt.parse_evs rp_sm tb [])) rp_H0 rp_hist' S') /\
       PjGrammar.jr_run ReaderRes.jr_strtod tb ok = (res, tr) /\
       prh_oks ok cnt fail (PjGrammar.calls tr) (prh_ev_reqs tr) most 0 ran' /\
       cnt' = cnt + Z.of_nat (PjGrammar.calls tr) /\ ReaderRes.fail_after cnt fail (PjGrammar.calls tr) fail' /\
       peak' = Z.max (Z.max peak (Ledger.lsum Lam + ReaderRes.hpeak tr))
         (prh_refused_peak ok cnt fail (PjGrammar.calls tr)
            (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (PRH_FnPj.prhPj_ptrace tb)))) /\
       ReaderRes.hpeak tr <= 224 * len + 16384 /\
       (cnt <= fail < cnt + ck_ncalls tb -> res = None) /\
       ran' = 0 /\
       (ran' = 0 -> fail < cnt \/ cnt + ck_ncalls tb <= fail ->
          res = ck_read tb /\ Z.of_nat (PjGrammar.calls tr) = ck_ncalls tb) /\
       bytes_at W' mem' text tb /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' fail' ran' most own /\
       match res with
       | Some t =>
           getr regs' 10 = w64 0 /\
           exists D, Permutation Lam' (D ++ Lam) /\
             Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr /\
             (* THE KIT'S TWO TREE CONJUNCTS, VERBATIM (kit candidate de5e947c224b PRH_FnCheck.v tparse_noting_specX
                :714-724 at the batch kit; the kit owner confirmed 21:22Z): the blocks up to permutation over the reader's own list, and THE BUILT
                TREE'S FREE ORDER (the cut file's ec_pjf is supplied from it). CFHEAD-16 guards both. *)
             (cf_head = PresetReqAt.HEAD -> Permutation (map (fun b => snd b + cf_head) D)
                (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod ok tb))) /\
             (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
                exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') n doc D F /\
                  map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok tb) /\
             (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
             Permutation (ablocks B ly' S') (ablocks B ly S ++ ck_hblks D) /\
             pj_nodeR segs (rdW W' mem') (prh_lin Lam') doc t D
       | None =>
           getr regs' 10 = w64 (-1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
           pj_zeroR segs (rdW W' mem') doc
       end)).

Definition tcheck_as_written_grantX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch data (x : list Z) rc doc t D Lam peak cnt fail ran most,
  let size := Z.of_nat (length x) in
  fpre B ARx STK_check_as_written ly S Hp W regs mem md ch ->
  (* the memory is normal at entry: this function's subtree reaches musl strtod (measured on BOTH rebuilt pins:
     strtod's only callers are ex_value and parse_value, and this text's subtree reaches one of them), whose row
     consumes it, and nothing below supplies it - it is seeded at main and threaded down. Same spelling and same
     reason as tex_value_specX's; see its comment for the suppliers and for the two halves of the route. *)
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size -> getr regs 12 = w64 rc -> getr regs 13 = w64 doc ->
  - 2 ^ 31 <= rc < 2 ^ 31 -> 0 <= doc < 2 ^ 64 ->
  size <= 3 * 2 ^ 20 -> 0 < data -> data + size < 2 ^ 62 ->
  src_rd W mem data x -> (0 < size -> PRH_FnEx.prhex_inblk B ly S Hp data size) ->
  (rc = 0 /\ ck_read x = Some t \/ rc <> 0 /\ ck_read x = None) ->
  (rc = 0 -> ck_tree_ok ly S Lam W mem doc t D) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most 0 ->
  (* ITS RUN EVENTS, as an entry premise: expected ()'s scratch, malloc (size + 1) then free (the model's
     [HMal (n + 1); HFr (n + 1)], PresetReqAt.v:272: a raw __wrap_malloc, no head); supplied by
     LLVMFuzzerTestOneInput's walk *)
  prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] ->
  (* The batch kit (21:3xZ, its batch ec4020b3da9c / 56d62ccaf185): the kit excludes the scratch's refusal arm ONLY when its two
     events are CONSUMER events of the run, so the grant text takes that window at entry *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i 2 ->
  (* THE FLAGS ARE CLEAR AT ENTRY (h-hpreset-7's ruling on the third #102 defect, 2026-10-29): g_own_ran_out = 0 and
     g_ran_out = 0, so out_of_memory() is 0 at entry and any 1 at the return comes from THIS call. Its only call is new:820, `out_of_memory () || check_as_written (..)`, so it runs only
     when out_of_memory () is 0. No request bound: it makes no ledger request (its scratch is noted (malloc ..)). *)
  ran = 0 ->
  blocks_bytes S + LIVE_check_as_written size <= LIVE_MAX -> size + 1 < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_as_written ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* at most 4 calls in the run: with the position and the run above, tcheck_as_written_specX's run position at
     entry (its existential HPOS premise) *)
  (length rp_os <= 4)%nat ->
  (* THE HULL BUDGET of expected ()'s scratch pair (tcheck_as_written_specX's, word for word) *)
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (size + 1); PresetReqAt.HFr (size + 1)] ->
  ck_frm0 ->
  (* #102 (merged fuzz_preset.c, src-102/new, sha256 c7b4007bba7bab3e, verified against src-102/SHA256SUMS; its :570
     against the base's :519): check_as_written RETURNS int and has a NEW EARLY-RETURN ARM. The harness's own comment
     is "1 when memory ran out, and the call ends": `if (out_of_memory()) return 1;` (new:574) is taken AFTER
     expected(...) has run, so neither abort check runs on that arm; otherwise both run and it returns 0 (new:589).
     The OLD post was the void form with ONE arm and no return conjunct: it is FALSE on the new binary, not merely
     incomplete, because a text's arms are a PARTITION.
     THE CONDITION, now that g_own_ran_out has its generated row (Batch 1): r = out_of_memory () at new:574, and the
     ledger is unchanged (ran stays 0), so r = 1 exactly when expected ()'s scratch was refused (noted, own' = 1). *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_as_written) regs mem md)
    (fpostFm B ARx SK STK_check_as_written [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
       exists own', prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' /\
       bytes_at W' mem' data x /\
       exists r, getr regs' 10 = w64 r /\
         (* THE EXACT ADVANCE per arm: r = 1 is the scratch REFUSED (noted, own' = 1): no event, the position kept;
            r = 0 made both events *)
          (r = 0 /\ own' = 0 /\ (exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + 2)%nat rp_H0 hist' S') /\
           (rc = 0 -> pj_nodeR segs (rdW W' mem') (prh_lin Lam) doc t D)))).

(* tcheck_no_overread_grantedX (row LL1): the cut file's PROVISIONAL l1_tcno_exactX (lib/A/Ent102CutsA.v section 0'),
   the name; in the post, `((r = 1 /\ (own' = 1 \/ ran' = 1)) \/ (r = 0 /\ own' = 0 /\ ran' = 0))` becomes
   `own' = 0 /\ ((r = 1 /\ ran' = 1) \/ (r = 0 /\ ran' = 0))`: the padded copies are granted (a refused copy is
   the driver's excluded refusal; the kit owner restates check_no_overread with a named grant condition in its next batch). *)
Definition tcheck_no_overread_grantedX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch data (x : list Z) Lam peak cnt ran most,
  rp_sm = ReaderRes.jr_strtod ->
  let size := Z.of_nat (length x) in
  fpre B ARx STK_check_no_overread ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm segs mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_no_overread (raZ regs :: spine ch) ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size ->
  size <= 3 * 2 ^ 20 ->
  src_rd W mem data x -> (0 < size -> PRH_FnReader.prhReader_home B ly S Hp Lam data size) ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  ran = 0 ->
  PRH_FnPj.RQ_pj_parse x <= most ->
  blocks_bytes S + LIVE_check_no_overread x <= LIVE_MAX ->
  size + 16 < cf_malloc_max -> PRH_FnPj.RQ_pj_parse x + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_no_overread ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE EXACT FORM'S ENTRY PREMISE: the call's run, for every grant triple of the three readings *)
  (forall o1 o2 o0, prh_run_at rp_sm rp_x (rp_os ++ [(o1, o2, o0)]) rp_i (PresetRun.call_evs rp_sm x o1 o2 o0)) ->
  (* The batch kit (21:4xZ): l1_tcno_exactX_of_post needs the position and the run at the same input - the run's bytes ARE the
     call's (LL1 supplies it from ec_pre: e_x E is both) *)
  rp_x = x ->
  (* R1 (rule-2 review, 21:5xZ): the entry position is the call boundary (LL1 holds it as HI0T) *)
  rp_i = length (PresetRun.hruns rp_sm rp_x rp_os) ->
  ck_frm0 ->
  (* THE WILD ROOM and THE BUDGETED POST (the batch kit, PRH_FnCheck.v:770 / :786) *)
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot S) ->
  (* THE HULL BUDGET of the call's all-granted events (tcheck_no_overread_specX's, word for word) *)
  PresetHullBudget.hull_budget S (ck_cno_evs ReaderRes.jr_strtod x None None None) ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_check_no_overread) regs mem md)
    (fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread))
      STK_check_no_overread [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists Lam' peak' cnt' ran' own',
       Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       peak <= peak' /\ cnt <= cnt' <= cnt + 3 * ck_ncalls x /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
       bytes_at W' mem' data x /\
       exists r, getr regs' 10 = w64 r /\
         own' = 0 /\ ((r = 1 /\ ran' = 1) \/ (r = 0 /\ ran' = 0)) /\
         (* THE TRIPLE, THE EXACT ADVANCE AND THE RETURN TIE hold when no padded copy was refused (own' = 0), as
            the kit gives them (PRH_FnCheck.v:690; the kit owner 18:54Z): a refused copy (own' = 1, noted (malloc ..) NULL)
            makes no HMal the model's COPY3 has, and then no triple ties r = 1 to a reading that ran out (e.g. an
            input whose readings allocate nothing: ranout is false for every o, while r = 1). Under own' = 0 the
            tie holds in the no-allocation case too, with (None, None, None): r = 1 needs ran' = 1, a refused
            reading allocation, which a reading that allocates nothing cannot have. The copies' grant (own' = 0)
            comes from the driver's no-refusal fact through GrantA's tcheck_no_overread_grantedX. *)
         (own' = 0 -> exists o1 o2 o0,
            (exists rp_hist', PresetRoomPos.iface_room_pos rp_sm rp_x (rp_os ++ [(o1, o2, o0)])
               (rp_i + length (Ent102CutsA.l1_cno_evs rp_sm x o1 o2 o0))%nat rp_H0 rp_hist' S') /\
            (r = 1 <-> (PresetRun.ranout rp_sm x o1 || PresetRun.ranout rp_sm x o2 || PresetRun.ranout rp_sm x o0) = true)))).

End c.
