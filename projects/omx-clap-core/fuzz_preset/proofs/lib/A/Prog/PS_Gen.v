(* fuzz_preset, parse_string (preset_file.c:117-181): the walk's IMAGE-GENERIC layer, for image A's walk (WalkS4,
   lib/A/Prog/S4_Ps*.v) and image B's walk (BParseString, lib/B/Prog/PSB_*.v). Nothing here reads a listing: it is
   generic over {L : ptable asym} {PA : PAImg L} and the image's PrhImg, so each image writes only its RUN lemmas.
   rule 24: proves no function (kind: statement text / segment glue).
   SOURCE, VERBATIM but for the instance binding: WalkS4's lib/A/Prog/S4_PsBase.v (a working branch
   83f3e37ac7e): ps_in, ps_x, ps_pre, ps_Qres, ps_Q, ps_post, PS_FRAME / PS_WSTK / PS_WSP / PS_SP, ps_saved, ps_carry,
   ps_gptp, ps_dec_rel, ps_alloc, ps_at_ret0. There the image instances are local Instances of image A; here they are
  Context, so the same text serves image B. The goal is the KIT TEXT tparse_string_specX of the announced the kit cut
  7cdbb61b5fa0 (owner 06:11Z; PRH_FnReader.v blob f1ae32e3b2cd :517-681; prepped on the batch kit's
  preset-tree-at-2026-10-30T02-01-18Z.tsv (sha256 a12cae64b2b5; internal record), then rebuilt on the cut): POST-IMPLICATION, the cursor set CW (prh_cw_ok in the slot prh_cur_ok
  vacated, `wild_room (as_universe B) CW 0 (st_depot S)` at entry) and the post BUDGETED at wbudget CW 0. The earlier
  statement (PS_Draft.v, the f97c text with the callee's refusal ledger) is deleted, and the change from it was NOT a
  conversion: the kit's refused arm adds the outcome-exclusion conjunct (:622-629) and counts ((cnt + 1) mod 2 ^ 64)
  (:633-635); both are proved here (ps_excl_of_malloc from fuzz_malloc's outcome clause; the mod is prh_alloc_post's).
   ONE DIFFERENCE: the caller-window kit is the ENGINE's lib/Reusable/YCbqGcallW.v (a working branch 63997a07aa6: fwin_x,
   fpostW_x, cj_kept, fpostW_x_of_kept; WalkS4's PRW_CallerJ.v moved there with the same bodies, its credit line
   :6), not lib/A/Prog/PRW_CallerJ.v, so the call rules aj_call_xW / aj_call_xW_sp of the engine produce these very
   predicates.
   ADDED HERE (image-free glue, Qed): ps_holds_of_entryP (the entry stretch at every record, at P := ps_mn D, is the kit's
   m-form budgeted text), ps_K0_of_records (the kit text from the records), ps_close / ps_closeP / ps_closePw (the state
   after parse_string's `ret` with the carried journal and kept relation is ps_post / ps_postP, at budget [] or at the
   bad escape's budget).
   THE HULL BUDGET (lib/Spec/PresetHullBudget.v): the text takes `hull_budget S (prhPs_evs x [])` at entry (ps_pre's
   ninth conjunct, after the two live counts) and states `hull_used S S' (prhPs_evs x [])` in its post. ps_hull_mal
   gives fuzz_malloc's budget [HMal ..], ps_hull_free the bad escape's fuzz_free's [] from what the malloc's use
   leaves; the cut layer's transfer ps_rpos carries the use since the entry at the all-granted list
   (ps_hull_used_mal), and ps_QresK_of_res hands it to the post (ps_QK; ps_QT is the text's conjunct order).
   THE IMAGE-SPECIFIC REST (register maps differ between the images): the cut offsets, ps_sh_regs, ps_dec_consts,
   ps_at_scan, ps_at_dec, ps_at_retok and the stretch statements stay in each image's base file.
   Numerals: the frame-slot offsets 40 .. 136 (LENGTH: the 13 callee-saved slots of parse_string's 144-byte frame,
   the same in both images: A 0x8794c and B 0x880fc `sd ra, 136(sp)` .. `sd s11, 40(sp)`), register numbers 3, 4, 8,
   9, 18 .. 27 (WORD: gp, tp, s0, s1, s2 .. s11), 34 (WORD: the double-quote byte), 24 / 8 (LENGTH: struct pj_in and
   its p field),
   2 ^ 64, 4096, 16, 1, 2 (LENGTH). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
(* the generic-P carriers (from a working branch 161f89a71b4d, whose YSRrMemnorm.v a1c1ece77b14 had srr_inv_laws,
   srr_inv_laws_imp, srr_inv_call, srr_inv_call_imp, srr_inv_mn; YAkMemnorm.v 96c72061b4d4; no LiaTwx2 `lia ::=`) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* srr_inv_laws lives in YC80x since the s1b collapse (preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record)); YSRrMemnorm keeps the lemmas *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt
  PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
(* the P'' room count and the budgeted posts (the batch text's post is at wbudget CW 0), qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
(* the re-hiding move: SRrG / SRr' / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf (the kit's primed
   tparse_string_specX concludes SRr' segs RZ_cf with fpostWbm at wle') *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section ps. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the non-primary room invariant room_live_cf (PRH_Base.v's class PrhRoomLive, owner a Theorem Labs lane) *)
Context {RL : PrhRoomLive}.
(* the image: its PrhImg data and its whole-program listing instance, bound by each image's base file *)
Context {PI : PrhImg} {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation PST := (prh_pst).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
#[local] Notation AJW := (ajournal_xw (SK := SK) segs B PST ARx).
#[local] Notation KEPT := (cj_kept (SK := SK) segs B PST).
#[local] Notation LEDGER := (prh_ledger B).

(* ---- THE ENTRY DATA: one record, so every stretch names the same entry state ---- *)
Record ps_in : Type := mkPsIn {
  pi_ly : alayout; pi_S : astate; pi_Hp : list Z; pi_W : world segs;
  pi_regs : bvmap 5 word; pi_mem : word -> option byte; pi_md : Model; pi_ch : list (Z * Z * Z);
  pi_e : Z; pi_q : Z; pi_text : Z; pi_len : Z; pi_p : Z; pi_d : Z; pi_tb : list Z;
  pi_Lam : list (Z * Z); pi_peak : Z; pi_cnt : Z; pi_fail : Z; pi_ran : Z;
  (* the text's ledger binders (#102 Batch 2, walkkit-next preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record); at the cut PRH_FnReader.v f1ae32e3b2cd :518):
     g_most and g_own_ran_out, kept by parse_string *)
  pi_most : Z; pi_own : Z
}.
(* the text after the opening quote: the model's argument everywhere *)
Definition ps_x (D : ps_in) : list Z := rest_atR (pi_tb D) (pi_text D) (pi_p D + 1).

(* THE POSITION, POST-IMPLICATION (preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record): PRH_FnReader.v's header, FAMILY / THE MODEL-RUN POSITION): no
   position at entry; a later state S transfers ANY position of ANY model run whose next events are E, by EXACTLY
   length E. ps_rposK is the text's forall clause verbatim; the text's arms (ps_QresK) state it at
   prhPs_evs (ps_x D) okA *)
Definition ps_rposK (D : ps_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
    PRH_Base.prh_run_at sm x os i E ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length E)%nat H0 hist' S.
(* THE CUT LAYER'S TRANSFER: the hull use since the entry, at most the ALL-GRANTED events prhPs_evs x [] (the text's
   hull_used conjunct; one list for every arm, since each arm's events are among them), and the position transfer by
   the arm's explicit event list E (E = [] where no allocator event happened, [HMal m] after the granted fuzz_malloc,
   [HMal m; HFr m] after it and the bad escape's fuzz_free, m = Q + 1 + cf_head); ps_QresK_of_res turns each list
   into the text's prhPs_evs (ps_x D) okA *)
Definition ps_rpos (D : ps_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  PresetHullBudget.hull_used (pi_S D) S (prhPs_evs (ps_x D) []) /\ ps_rposK D E S.
(* THE LIVE REQUESTS after E (the text's chaining fact, EXACT up to Permutation): it follows from each arm's own blocks
   facts, so the cut layer does not carry it (ps_QresK_of_res derives it) *)
Definition ps_live (D : ps_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) E).

(* tparse_string_specX's premises (the kit cut 7cdbb61b5fa0, PRH_FnReader.v f1ae32e3b2cd :520-576), at one record, in the
   text's order: no position and no run premise. ONE CONJUNCT PER PREMISE but two: the fourth is prh_cur_low and the
   fifth prh_cw_ok (the cursor set CW, in the slot prh_cur_ok vacated, :539 / :544), the eighth the wild room (:550),
   and the ninth carries the two live counts (the PEAK along the all-granted events, :554-557) and the hull budget over
   the same events, so the conjuncts keep their positions in every stretch's destruct. The LAST is the cut's per-event
   form (:566-576): the request bound and prh_live_evs over the all-granted events (it replaced K1-tip e45217a4c7ba's
   entry sum `blocks_bytes S + LIVE_parse_string Q <= LIVE_MAX`; ps_room_entry below gives the walk's fuzz_malloc room
   from its event 0) *)
Definition ps_pre (CTX : list (list Z)) (CW : list (list Z)) (D : ps_in) : Prop :=
  fpre B ARx STK_parse_string (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_regs D) (pi_mem D) (pi_md D) (pi_ch D) /\
  prh_univ_closure B CTX /\
  (exists ch, achain (pi_ly D) (aview segs (w_H (pi_W D)) (pi_mem D)) (spZ (pi_regs D) - pi_frame F_parse_string)
     (prh_s0 F_parse_string (pi_q D)) ch) /\
  prh_cur_low (pi_W D) (pi_mem D) F_parse_string (pi_q D) /\ prh_cw_ok B CW (pi_W D) (pi_mem D) F_parse_string (pi_q D) /\
  spZ (pi_regs D) + 16 <= pi_q D /\
  room_live_cf (pi_S D) /\
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot (pi_S D)) /\
  (Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D)))
     (prhPs_evs (ps_x D) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
   Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D)))
     (prhPs_evs (ps_x D) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
   PresetHullBudget.hull_budget (pi_S D) (prhPs_evs (ps_x D) [])) /\
  getr (pi_regs D) 10 = w64 (pi_q D) /\
  pj_in_okR segs (rdW (pi_W D) (pi_mem D)) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  pi_p D < pi_text D + pi_len D /\
  nth_error (pi_tb D) (Z.to_nat (pi_p D - pi_text D)) = Some 34 /\
  fwin (pi_ly D) (pi_W D) (pi_regs D) (pi_mem D) (pi_e D) /\
  spZ (pi_regs D) <= pi_q D /\ pi_q D + 24 <= spZ (pi_regs D) + pi_e D /\
  range_addressable (aview segs (w_H (pi_W D)) (pi_mem D)) SHADOW_OFF (pi_q D) 24 /\
  src_rd (pi_W D) (pi_mem D) (pi_text D) (pi_tb D) /\
  prhReader_home B (pi_ly D) (pi_S D) (pi_Hp D) (pi_Lam D) (pi_text D) (pi_len D) /\
  LEDGER (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D)
    (pi_most D) (pi_own D) /\
  pi_cnt D + 1 < 2 ^ 64 - 1 /\
  ((forall Q, PjGrammar.scan (ps_x D) = Some Q -> LIVE_parse_string Q < cf_malloc_max) /\
   prh_live_evs (pi_S D) (prhPs_evs (ps_x D) [])).

(* THE REFUSED ARM'S OUTCOME EXCLUSION (PRH_FnReader f1ae32e3b2cd :625-629, verbatim at one record): no model run and
   position whose next events are the ALL-GRANTED list prhPs_evs x [], its malloc a CONSUMER event, meets the arm *)
Definition ps_excl (D : ps_in) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
    PRH_Base.prh_run_at sm x os i (prhPs_evs (ps_x D) []) ->
    PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (ps_x D) [])) -> False.

(* the post body of the cut layer: the text's arms, each with its OWN explicit event list for the position; no
   live-request conjunct (ps_QresK_of_res derives it from the blocks facts) *)
Definition ps_Qres (D : ps_in) (res : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  match PjGrammar.scan (ps_x D) with
  | None =>
      res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
      LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
      pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
      ps_rpos D [] S'
  | Some Q =>
      (pi_cnt D = pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D + 1) SIZE_MAXZ (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_rpos D [] S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       (exists regsc memc mdc Wc cc,
          YG0dcf.malloc_cf_null_post segs B (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regsc memc mdc
            (Z.of_nat Q + 1 + cf_head) (PNull, S') Wc cc) /\
       rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
       (* THE OUTCOME (PRH_FnReader f1ae32e3b2cd :622-629): no model run whose next events are the all-granted ones
          meets this refused arm at a consumer position *)
       ps_excl D /\
       (* the ledger: fuzz_malloc's refusal arm verbatim (:633-635), the count kept mod 2 ^ 64 *)
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Z.min SIZE_MAXZ (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1)))) ((pi_cnt D + 1) mod 2 ^ 64)
         (pi_fail D) (if Z.of_nat Q + 1 <=? pi_most D then 1 else pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_rpos D [] S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ PjGrammar.decode (ps_x D) = None /\
       Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
         (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)] S')
      \/
      (pi_cnt D <> pi_fail D /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
       exists s r, PjGrammar.decode (ps_x D) = Some (s, r) /\
       Hp' = (res - cf_head) :: pi_Hp D /\
       ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
       prhReader_vis W' mem' res (Z.of_nat Q + 1) /\
       pj_cbytesR segs (rdW W' mem') res s /\
       LEDGER ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
         (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D + Z.of_nat Q + 2) (pi_d D) (pi_tb D) /\
       ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] S')
  end.
(* THE TEXT'S ARMS (the kit cut 7cdbb61b5fa0, PRH_FnReader.v f1ae32e3b2cd :584-681), VERBATIM at one record: the chosen
   failure and the refusal also state blocks_bytes S' = blocks_bytes S, the refusal its outcome exclusion (ps_excl),
   and every arm states the live requests and the position after its own events prhPs_evs x okA (ps_live / ps_rposK /
   ps_excl unfold to the text's Permutation and forall clauses) *)
Definition ps_QresK (D : ps_in) (res : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  match PjGrammar.scan (ps_x D) with
  | None =>
      res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
      LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
      pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
      ps_live D (prhPs_evs (ps_x D) []) S' /\ ps_rposK D (prhPs_evs (ps_x D) []) S'
  | Some Q =>
      (pi_cnt D = pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       blocks_bytes S' = blocks_bytes (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D) (pi_peak D) (pi_cnt D + 1) SIZE_MAXZ (pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [false]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [false]) S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       blocks_bytes S' = blocks_bytes (pi_S D) /\
       (exists regsc memc mdc Wc cc,
          YG0dcf.malloc_cf_null_post segs B (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regsc memc mdc
            (Z.of_nat Q + 1 + cf_head) (PNull, S') Wc cc) /\
       rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\
       ps_excl D /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Z.min SIZE_MAXZ (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1)))) ((pi_cnt D + 1) mod 2 ^ 64)
         (pi_fail D) (if Z.of_nat Q + 1 <=? pi_most D then 1 else pi_ran D) (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [false]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [false]) S')
      \/
      (pi_cnt D <> pi_fail D /\ res = 0 /\ PjGrammar.decode (ps_x D) = None /\
       Hp' = pi_Hp D /\ ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) /\
       LEDGER ly' S' Hp' W' mem' (pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
         (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [true]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [true]) S')
      \/
      (pi_cnt D <> pi_fail D /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\
       exists s r, PjGrammar.decode (ps_x D) = Some (s, r) /\
       Hp' = (res - cf_head) :: pi_Hp D /\
       ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)] /\
       prhReader_vis W' mem' res (Z.of_nat Q + 1) /\
       pj_cbytesR segs (rdW W' mem') res s /\
       LEDGER ly' S' Hp' W' mem' ((res, Z.of_nat Q + 1) :: pi_Lam D)
         (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
         (pi_most D) (pi_own D) /\
       pj_in_okR segs (rdW W' mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D + Z.of_nat Q + 2) (pi_d D) (pi_tb D) /\
       ps_live D (prhPs_evs (ps_x D) [true]) S' /\ ps_rposK D (prhPs_evs (ps_x D) [true]) S')
  end.
(* the text's hull use (its third post conjunct) with the text's arms: the last conjunct of ps_Q, so a stretch that
   closes the post builds it with ps_QresK_of_res alone *)
Definition ps_QK (D : ps_in) (res : Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  PresetHullBudget.hull_used (pi_S D) S' (prhPs_evs (ps_x D) []) /\ ps_QresK D res ly' S' Hp' W' mem' md'.
(* the text's post: each arm states its own live requests and position; the hull use is in the last conjunct
   (ps_QT below is the text's order) *)
Definition ps_Q (D : ps_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
  blocks_bytes S' <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_QK D res ly' S' Hp' W' mem' md'.
(* the text's post in the text's conjunct order (PRH_FnReader.v tparse_string_specX: the hull use third) *)
Definition ps_QT (D : ps_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
  PresetHullBudget.hull_used (pi_S D) S' (prhPs_evs (ps_x D) []) /\
  blocks_bytes S' <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_QresK D res ly' S' Hp' W' mem' md'.
Lemma ps_QT_of_Q : forall D ly' S' Hp' W' regs' mem' md',
  ps_Q D ly' S' Hp' W' regs' mem' md' -> ps_QT D ly' S' Hp' W' regs' mem' md'.
Proof.
intros D ly' S' Hp' W' regs' mem' md' (res & H1 & H2 & H3 & H4 & H5).
(* ps_QT is the text's post (tparse_string_specX's, in its conjunct order): BUILT BY NAME through the kit's projection
   layer (PRH_FnReader.v tpstP_Q_of_R from the record tpstP_R, field by field); md' is the one argument of the post
   that its body does not mention, so it is given *)
refine (tpstP_Q_of_R md' (res := res) _).
exact {| tpstP_ret := H1; tpstP_room := H2; tpstP_hull := H4; tpstP_bytes_le := H3; tpstP_arm := H5 |}.
Qed.

(* ---- the events and the live requests of each arm, from its own facts ---- *)
(* the live requests are the block sizes of ablocks (YGcfRoom.room_of_cf, YG0d.v ablocks) *)
Lemma ps_live_ab : forall ly S, PresetRoom.rs_live (YGcfRoom.room_of_cf S) = map snd (ablocks B ly S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.
Lemma ps_live_keep : forall D ly' S', ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) -> ps_live D [] S'.
Proof.
intros D ly' S' Hab. unfold ps_live. rewrite (ps_live_ab ly' S'), (ps_live_ab (pi_ly D) (pi_S D)), Hab.
apply Permutation_refl.
Qed.
Lemma ps_live_bad : forall D ly' S' m, ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ->
  ps_live D [PresetReqAt.HMal m; PresetReqAt.HFr m] S'.
Proof.
intros D ly' S' m Hab. unfold ps_live. rewrite (ps_live_ab ly' S'), (ps_live_ab (pi_ly D) (pi_S D)), Hab.
unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep PresetReqAt.rm1]. rewrite Z.eqb_refl.
apply Permutation_refl.
Qed.
Lemma ps_live_app : forall D ly' S' a m,
  ablocks B ly' S' = ablocks B (pi_ly D) (pi_S D) ++ [(a, m)] -> ps_live D [PresetReqAt.HMal m] S'.
Proof.
intros D ly' S' a m Hab. unfold ps_live. rewrite (ps_live_ab ly' S'), (ps_live_ab (pi_ly D) (pi_S D)), Hab.
unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep]. rewrite map_app. cbn [map snd].
apply Permutation_sym, Permutation_cons_append.
Qed.
Lemma ps_evs_none : forall x ok, PjGrammar.scan x = None -> prhPs_evs x ok = [].
Proof. intros x ok H. unfold prhPs_evs. rewrite H. reflexivity. Qed.
Lemma ps_evs_false : forall x Q, PjGrammar.scan x = Some Q -> prhPs_evs x [false] = [].
Proof. intros x Q H. unfold prhPs_evs. rewrite H. reflexivity. Qed.
Lemma ps_evs_bad : forall x Q, PjGrammar.scan x = Some Q -> PjGrammar.decode x = None ->
  prhPs_evs x [true] = [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)].
Proof. intros x Q H Hd. unfold prhPs_evs. rewrite H, Hd. reflexivity. Qed.
Lemma ps_evs_ok : forall x Q sr, PjGrammar.scan x = Some Q -> PjGrammar.decode x = Some sr ->
  prhPs_evs x [true] = [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)].
Proof. intros x Q sr H Hd. unfold prhPs_evs. rewrite H, Hd. reflexivity. Qed.
(* the position before any event, and no hull use *)
Lemma ps_rpos_nil : forall D, ps_rpos D [] (pi_S D).
Proof.
intros D. split; [apply PresetHullBudget.hull_used_refl|].
intros sm x os i H0 hist Hp _. exists hist. rewrite Nat.add_0_r. exact Hp.
Qed.

(* THE REFUSED ARM'S OUTCOME EXCLUSION from fuzz_malloc's own outcome clause (PRH_FnAlloc 4d8aeba047e5 :302-312;
   PsRebindA's A' lemma, same name): the malloc's clause is stated over the one-event list [HMal m]; the text's over the
   all-granted list prhPs_evs x [], which starts with that event (a closed quote), so the run premise splits by
   prh_run_at_app_iff and the consumer premise restricts to its first event *)
Lemma ps_cons_from_le : forall sm x os i k k', (k' <= k)%nat ->
  PRH_Base.prh_cons_from sm x os i k -> PRH_Base.prh_cons_from sm x os i k'.
Proof. intros sm x os i k k' Hle H j e Hj He. exact (H j e ltac:(lia) He). Qed.
Lemma ps_evs_all_head : forall x Q, PjGrammar.scan x = Some Q ->
  exists rest, prhPs_evs x [] = [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ++ rest.
Proof.
intros x Q H. unfold prhPs_evs. rewrite H. cbn [nth].
exists (match PjGrammar.decode x with None => [PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)] | Some _ => [] end).
reflexivity.
Qed.
(* THE HULL AT THE fuzz_malloc CALL: the text's budget over the all-granted events, at their first event (a closed
   quote: prhPs_evs x [] starts with the malloc's HMal, ps_evs_all_head) *)
Lemma ps_hull_of_pre : forall CTX CW D, ps_pre CTX CW D ->
  PresetHullBudget.hull_budget (pi_S D) (prhPs_evs (ps_x D) []).
Proof. intros CTX CW D (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & H) & _). exact H. Qed.
Lemma ps_hull_mal : forall CTX CW D Q, ps_pre CTX CW D -> PjGrammar.scan (ps_x D) = Some Q ->
  PresetHullBudget.hull_budget (pi_S D) [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)].
Proof.
intros CTX CW D Q HPRE HS. pose proof (ps_hull_of_pre CTX CW D HPRE) as HB.
destruct (ps_evs_all_head (ps_x D) Q HS) as (rest & Erest). rewrite Erest in HB.
exact (PresetHullBudget.hull_budget_infix (pi_S D) (pi_S D) [] [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] rest HB
  (PresetHullBudget.hull_used_refl (pi_S D) [])).
Qed.
(* fuzz_malloc's use (its post's hull_used at [HMal ..]) is a use at the all-granted list, which starts with it *)
Lemma ps_hull_used_mal : forall D Q S1, PjGrammar.scan (ps_x D) = Some Q ->
  PresetHullBudget.hull_used (pi_S D) S1 [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ->
  PresetHullBudget.hull_used (pi_S D) S1 (prhPs_evs (ps_x D) []).
Proof.
intros D Q S1 HS HU. destruct (ps_evs_all_head (ps_x D) Q HS) as (rest & Erest). rewrite Erest.
exact (PresetHullBudget.hull_used_infix (pi_S D) S1 [] [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] rest HU).
Qed.
Lemma ps_excl_of_malloc : forall D Q S1 res, PjGrammar.scan (ps_x D) = Some Q -> pi_cnt D <> pi_fail D -> res = 0 ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
     PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ->
     PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)]) ->
     pi_cnt D <> pi_fail D ->
     res <> 0 /\
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)])%nat
       H0 hist' S1) ->
  ps_excl D.
Proof.
intros D Q S1 res HS Hcf Hr HOUT sm x os i H0 hist Hp Hrun Hcons.
destruct (ps_evs_all_head (ps_x D) Q HS) as (rest & Erest). rewrite Erest in Hrun, Hcons.
apply (proj1 (PRH_Base.prh_run_at_app_iff sm x os i _ rest)) in Hrun. destruct Hrun as [Hrun _].
apply (ps_cons_from_le sm x os i _ 1) in Hcons; [|rewrite length_app; cbn [length]; lia].
destruct (HOUT sm x os i H0 hist Hp Hrun Hcons Hcf) as [Hnz _]. exact (Hnz Hr).
Qed.

(* the blocks_bytes conjunct follows from the arm facts (blocks_bytes is the sum of ablocks, YCbq.v
   blocks_bytes_bsum), so the stretches need not carry it; the live requests follow from the same facts (above); the
   hull use is every arm's ps_rpos's *)
Lemma ps_QresK_of_res : forall D res ly' S' Hp' W' mem' md',
  ps_Qres D res ly' S' Hp' W' mem' md' -> ps_QK D res ly' S' Hp' W' mem' md'.
Proof.
intros D res ly' S' Hp' W' mem' md' HQ. unfold ps_Qres in HQ. unfold ps_QK, ps_QresK.
(* each arm of the text's post is BUILT BY NAME through the kit's arm records (PRH_FnReader.v tpstP_RNone, tpstP_RSome1 ..
   tpstP_RSome4 and tpstP_ANone_of_R / tpstP_ASome1_of_R .. tpstP_ASome4_of_R); the live requests and the position
   at the arm's own events prhPs_evs (ps_x D) okA come from the arm's blocks facts and its explicit event list *)
destruct (PjGrammar.scan (ps_x D)) as [Q|] eqn:Hs.
2:{ destruct HQ as (H1 & H2 & H3 & H4 & H5 & HH & H6). split; [exact HH|].
    refine (tpstP_ANone_of_R _).
    assert (HL : ps_live D (prhPs_evs (ps_x D) []) S')
      by (rewrite (ps_evs_none (ps_x D) [] Hs); exact (ps_live_keep D ly' S' H3)).
    assert (HP : ps_rposK D (prhPs_evs (ps_x D) []) S') by (rewrite (ps_evs_none (ps_x D) [] Hs); exact H6).
    exact {| tpstPn_res0 := H1; tpstPn_hp := H2; tpstPn_ablocks := H3; tpstPn_ledger := H4; tpstPn_in_ok := H5;
             tpstPn_live := HL; tpstPn_pos := HP |}. }
destruct HQ as [(H1 & H2 & H3 & H4 & H5 & H6 & HH & H7) | [(H1 & H2 & H3 & H4 & H5 & H6 & HX & H7 & H8 & HH & H9) |
  [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & HH & H8) |
   (H1 & H2 & H3 & s & r & H4 & H5 & H6 & H7 & H8 & H9 & H10 & HH & H11)]]];
  (split; [exact HH|]).
- left. refine (tpstP_ASome1_of_R _).
  assert (HB : blocks_bytes S' = blocks_bytes (pi_S D))
    by (rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), H4; reflexivity).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [false]) S')
    by (rewrite (ps_evs_false (ps_x D) Q Hs); exact (ps_live_keep D ly' S' H4)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [false]) S') by (rewrite (ps_evs_false (ps_x D) Q Hs); exact H7).
  exact {| tpstPs1_chosen := H1; tpstPs1_res0 := H2; tpstPs1_hp := H3; tpstPs1_ablocks := H4; tpstPs1_bytes := HB;
           tpstPs1_ledger := H5; tpstPs1_in_ok := H6; tpstPs1_live := HL; tpstPs1_pos := HP |}.
- right; left. refine (tpstP_ASome2_of_R _).
  assert (HB : blocks_bytes S' = blocks_bytes (pi_S D))
    by (rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), H4; reflexivity).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [false]) S')
    by (rewrite (ps_evs_false (ps_x D) Q Hs); exact (ps_live_keep D ly' S' H4)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [false]) S') by (rewrite (ps_evs_false (ps_x D) Q Hs); exact H9).
  exact {| tpstPs2_notchosen := H1; tpstPs2_res0 := H2; tpstPs2_hp := H3; tpstPs2_ablocks := H4; tpstPs2_bytes := HB;
           tpstPs2_evidence := H5; tpstPs2_errno := H6; tpstPs2_outcome := HX; tpstPs2_ledger := H7;
           tpstPs2_in_ok := H8; tpstPs2_live := HL; tpstPs2_pos := HP |}.
- right; right; left. refine (tpstP_ASome3_of_R _).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [true]) S')
    by (rewrite (ps_evs_bad (ps_x D) Q Hs H3); exact (ps_live_bad D ly' S' _ H5)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [true]) S') by (rewrite (ps_evs_bad (ps_x D) Q Hs H3); exact H8).
  exact {| tpstPs3_notchosen := H1; tpstPs3_res0 := H2; tpstPs3_bad := H3; tpstPs3_hp := H4; tpstPs3_ablocks := H5;
           tpstPs3_ledger := H6; tpstPs3_in_ok := H7; tpstPs3_live := HL; tpstPs3_pos := HP |}.
- right; right; right. refine (tpstP_ASome4_of_R (s := s) (r := r) _).
  assert (HL : ps_live D (prhPs_evs (ps_x D) [true]) S')
    by (rewrite (ps_evs_ok (ps_x D) Q (s, r) Hs H4); exact (ps_live_app D ly' S' _ _ H6)).
  assert (HP : ps_rposK D (prhPs_evs (ps_x D) [true]) S') by (rewrite (ps_evs_ok (ps_x D) Q (s, r) Hs H4); exact H11).
  exact {| tpstPs4_notchosen := H1; tpstPs4_res_min := H2; tpstPs4_res_align := H3; tpstPs4_decode := H4;
           tpstPs4_hp := H5; tpstPs4_ablocks := H6; tpstPs4_vis := H7; tpstPs4_cbytes := H8; tpstPs4_ledger := H9;
           tpstPs4_in_ok := H10; tpstPs4_live := HL; tpstPs4_pos := HP |}.
Qed.

Lemma ps_Q_of_res : forall D res ly' S' Hp' W' regs' mem' md',
  getr regs' 10 = w64 res -> room_live_cf S' -> ps_Qres D res ly' S' Hp' W' mem' md' ->
  ps_Q D ly' S' Hp' W' regs' mem' md'.
Proof.
intros D res ly' S' Hp' W' regs' mem' md' H10 HR HQ. exists res. split; [exact H10|]. split; [exact HR|].
split; [|exact (ps_QresK_of_res D res ly' S' Hp' W' mem' md' HQ)].
pose proof (cf_head_nonneg) as Hh.
rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B (pi_ly D) (pi_S D)).
unfold ps_Qres in HQ. unfold PRH_Charge.prh_held, PRH_Charge.prhPs_gtrace, PjGrammar.jr_string.
destruct (PjGrammar.scan (ps_x D)) as [Q|] eqn:Hs.
- destruct (PjGrammar.decode (ps_x D)) as [sr|] eqn:Hd;
    cbn [PjGrammar.jbind PjGrammar.jalloc PjGrammar.take PjGrammar.jret PjGrammar.jfree PjGrammar.jrefuse
         fst snd app PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call].
  + destruct HQ as [(_ & _ & _ & Hab & _) | [(_ & _ & _ & Hab & _) | [(_ & _ & Hdn & _) |
      (_ & _ & _ & s & r & _ & _ & Hab & _)]]].
    * rewrite Hab. lia.
    * rewrite Hab. lia.
    * discriminate Hdn.
    * rewrite Hab, bsum_app. cbn [bsum fold_right snd]. lia.
  + destruct HQ as [(_ & _ & _ & Hab & _) | [(_ & _ & _ & Hab & _) | [(_ & _ & _ & _ & Hab & _) |
      (_ & _ & _ & s & r & Hds & _)]]].
    * rewrite Hab. lia.
    * rewrite Hab. lia.
    * rewrite Hab. lia.
    * discriminate Hds.
- cbn [PjGrammar.jrefuse fst snd PjGrammar.held PjGrammar.calls].
  destruct HQ as (_ & _ & Hab & _). rewrite Hab. lia.
Qed.

(* THE ONE GOAL every stretch ends in: the text's conclusion at the entry state, BUDGETED at the cursor set CW (the
   batch text's post is fpostWbm .. (YCbqGwild.wbudget CW 0) ..: the journal from the entry at a budget WS of which it
   states wbudget CW 0 WS; only the bad escape's fuzz_free can store a trace outside the fixed ones) *)
Definition ps_post (CW : list (list Z)) (D : ps_in) : world segs -> config -> Prop :=
  YCbqGwild.fpostW_xb (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_Q D).
(* ps_post over a world relation R (a copy of its body at YCbqGwild.fpostW_xbR; ps_post is its instance at wle,
   ps_post_R_wle). A run that crosses the bad escape's fuzz_free ends at YA0nH.wle' segs RZ_cf, so the stretches that
   may reach it end in ps_postR (wle' segs RZ_cf) *)
Definition ps_postR (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) :
  world segs -> config -> Prop :=
  YCbqGwild.fpostW_xbR (SK := SK) segs B PST ARx R (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_Q D).
Lemma ps_post_R_wle : forall CW D, ps_post CW D = ps_postR (@wle segs) CW D.
Proof. reflexivity. Qed.

(* the widened window the stretches' journals run at, and the body's sp *)
(* LENGTH: parse_string's own frame, the N of its `addi sp, sp, -N` (PRH_Img / PRH_ImgB pi_frame F_parse_string) *)
Definition PS_FRAME : Z := pi_frame F_parse_string.
Definition PS_WSTK (D : ps_in) : Z := STK_parse_string + pi_e D.
Definition PS_WSP (D : ps_in) : Z := spZ (pi_regs D) + pi_e D.
Definition PS_SP (D : ps_in) : Z := spZ (pi_regs D) - PS_FRAME.

(* ---- what every cut carries: the journal from the entry state, the kept relation from the entry state (its out
   cells are the one caller word [q, q + 8)), the saved registers in the frame, and the text still readable ---- *)
Definition ps_saved (D : ps_in) (W : world segs) (mem : word -> option byte) : Prop :=
  let sp := PS_SP D in
  val_mem segs (rdW W mem) (sp + 136) 8%nat (raZ (pi_regs D)) /\
  val_mem segs (rdW W mem) (sp + 128) 8%nat (bv_unsigned (getr (pi_regs D) 8)) /\
  val_mem segs (rdW W mem) (sp + 120) 8%nat (bv_unsigned (getr (pi_regs D) 9)) /\
  val_mem segs (rdW W mem) (sp + 112) 8%nat (bv_unsigned (getr (pi_regs D) 18)) /\
  val_mem segs (rdW W mem) (sp + 104) 8%nat (bv_unsigned (getr (pi_regs D) 19)) /\
  val_mem segs (rdW W mem) (sp + 96) 8%nat (bv_unsigned (getr (pi_regs D) 20)) /\
  val_mem segs (rdW W mem) (sp + 88) 8%nat (bv_unsigned (getr (pi_regs D) 21)) /\
  val_mem segs (rdW W mem) (sp + 80) 8%nat (bv_unsigned (getr (pi_regs D) 22)) /\
  val_mem segs (rdW W mem) (sp + 72) 8%nat (bv_unsigned (getr (pi_regs D) 23)) /\
  val_mem segs (rdW W mem) (sp + 64) 8%nat (bv_unsigned (getr (pi_regs D) 24)) /\
  val_mem segs (rdW W mem) (sp + 56) 8%nat (bv_unsigned (getr (pi_regs D) 25)) /\
  val_mem segs (rdW W mem) (sp + 48) 8%nat (bv_unsigned (getr (pi_regs D) 26)) /\
  val_mem segs (rdW W mem) (sp + 40) 8%nat (bv_unsigned (getr (pi_regs D) 27)).

Definition ps_carry (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) : Prop :=
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D).
(* the same carry with the journal at a BUDGET WS (YCbqG.ajournal_xw): only the NULL return after the bad escape's
   fuzz_free needs it, the one wild site of parse_string; ps_carry is ps_carryw at WS = [] by conversion *)
Definition ps_carryw (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  AJW (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D).
(* ps_carryw over a world relation R (a copy of its body: the journal at R, ajournal_xwR, and the kept relation at R,
   cj_keptR; ps_carryw is its instance at wle, ps_carryw_R_wle): the cut after the bad escape's fuzz_free carries it
   at wle' segs RZ_cf *)
Definition ps_carrywR (R : world segs -> world segs -> Prop) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  ajournal_xwR (SK := SK) segs B PST ARx R (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  cj_keptR (SK := SK) segs B PST R STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D).
Lemma ps_carryw_R_wle : forall D ly S Hp W mem md k FPs WS,
  ps_carryw D ly S Hp W mem md k FPs WS = ps_carrywR (@wle segs) D ly S Hp W mem md k FPs WS.
Proof. reflexivity. Qed.
(* a kept relation at R1 is one at every R2 that contains R1 (only its world conjunct reads R) *)
Lemma ps_keptR_mono : forall (R1 R2 : world segs -> world segs -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2,
  cj_keptR (SK := SK) segs B PST R1 STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  cj_keptR (SK := SK) segs B PST R2 STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros R1 R2 H12 STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 (H1 & H2 & H3 & H4).
exact (conj H1 (conj H2 (conj (H12 W W2 H3) H4))).
Qed.
(* the empty budget is within the cursor set's *)
Lemma ps_wb_nil : forall CW, YCbqGwild.wbudget CW 0 [].
Proof. intros CW. unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia. Qed.

(* ---- gp and tp: never written by parse_string, so at every cut they are the entry's (aregs_preserved asks them) ---- *)
Definition ps_gptp (D : ps_in) (regs : bvmap 5 word) : Prop :=
  getr regs 3 = getr (pi_regs D) 3 /\ getr regs 4 = getr (pi_regs D) 4.

(* ---- decode's progress: `done` is what decode has already written: the bytes at out, w - out of them, and
   decoding the text from p + 1 is those bytes followed by decoding from r ---- *)
Definition ps_dec_rel (D : ps_in) (W : world segs) (mem : word -> option byte) (out w r : Z) (Q : nat) : Prop :=
  exists done,
    bytes_at W mem out done /\ Z.of_nat (length done) = w - out /\
    (forall sx rx, PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = Some (sx, rx) ->
       PjGrammar.decode (ps_x D) = Some (done ++ sx, rx)) /\
    (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None -> PjGrammar.decode (ps_x D) = None) /\
    pi_p D + 1 <= r <= pi_p D + 1 + Z.of_nat Q /\ out <= w /\ w - out <= r - (pi_p D + 1) /\
    (* decode stays in step with scan: the closing quote is Q - (r - (p + 1)) bytes on *)
    PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) = Some (Q - Z.to_nat (r - (pi_p D + 1)))%nat.
(* the room position after the one fuzz_malloc returned a block: fuzz_malloc's post-implication arm at
   res <> 0 transfers any position by its own event HMal (Q + 1 + cf_head) (PRH_FnAlloc.v 4d8aeba047e5 tfuzz_malloc_specX,
   the res <> 0 arm), so the cut carries that implication; the bad escape's fuzz_free extends it by HFr (same size) *)
Definition ps_rpos_mal (D : ps_in) (Q : nat) (S : astate) : Prop :=
  ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] S.
(* the allocator state after the one fuzz_malloc: the new block is live, the ledger has it *)
Definition ps_alloc (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (out : Z) (Q : nat) : Prop :=
  pi_cnt D <> pi_fail D /\ 4096 + cf_head <= out /\ out mod 16 = 0 /\
  Hp = (out - cf_head) :: pi_Hp D /\
  ablocks B ly S = ablocks B (pi_ly D) (pi_S D) ++ [(out - cf_head, Z.of_nat Q + 1 + cf_head)] /\
  LEDGER ly S Hp W mem ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
    (pi_most D) (pi_own D) /\
  prhReader_vis W mem out (Z.of_nat Q + 1) /\
  room_live_cf S /\ ps_rpos_mal D Q S /\
  (* the bytes the one malloc added to the live blocks, its head included (the post's prh_held clause) *)
  blocks_bytes S <= blocks_bytes (pi_S D) + (Z.of_nat Q + 1 + cf_head).
(* THE HULL AT THE BAD ESCAPE'S fuzz_free: the text's budget less the malloc's use (ps_alloc's ps_rpos_mal) is the
   free's budget for no event *)
Lemma ps_hull_free : forall CTX CW D Q S1, ps_pre CTX CW D -> ps_rpos_mal D Q S1 -> PresetHullBudget.hull_budget S1 [].
Proof.
intros CTX CW D Q S1 HPRE (HU & _).
exact (PresetHullBudget.hull_budget_used (pi_S D) S1 _ (ps_hull_of_pre CTX CW D HPRE) HU).
Qed.

(* ---- THE LIVE COUNTS AT THE TWO INNER CALLS (preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record), PRH_FnReader.v's header THE LIVE COUNTS AT THE INNER
   CALLS: they replace a Theorem Labs lane's counts_of_room_pos_rl). ps_pre's two peak premises are over the all-granted events
   prhPs_evs x []; the fuzz_malloc's state is their first state, the bad escape's fuzz_free's their second. The
   bridge to the leaves' sec_cnt / ccnt24 is conversion (YGcfRoomLive.v: sec_cnt filters rl_sec_req, ccnt24 is
   PresetRoom.ccnt kBatchClass; PresetReqAt.cnt is the length of a filter). AGREE-PREFIX is NOT needed on this
   form: the implications are applied after the calls, at the run the caller picks. ---- *)
Lemma ps_counts_entry : forall CTX CW D Q, ps_pre CTX CW D -> PjGrammar.scan (ps_x D) = Some Q ->
  YGcfRoomLive.sec_cnt (pi_S D) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 (pi_S D) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros CTX CW D Q HPRE HQ.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & (HSEC & H24 & _) & _).
pose proof (PresetRun.pkR_prefix YGcfRoomLive.rl_sec_req (prhPs_evs (ps_x D) [])
  (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) 0) as P1.
pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass) (prhPs_evs (ps_x D) [])
  (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) 0) as P2.
cbn [firstn] in P1, P2. rewrite PresetReqAt.hlive_from_nil in P1, P2.
assert (E1 : YGcfRoomLive.sec_cnt (pi_S D) =
  Z.of_nat (PresetReqAt.cnt YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D)))))
  by reflexivity.
assert (E2 : YGcfRoomLive.ccnt24 (pi_S D) =
  Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D)))))
  by reflexivity.
rewrite E1, E2. split; lia.
Qed.
(* ---- THE ROOM AT THE fuzz_malloc CALL (the kit cut 7cdbb61b5fa0, PRH_FnReader.v f1ae32e3b2cd :566-576): the text's
   prh_live_evs over the all-granted events, at its event 0 (the fuzz_malloc of Q + 1 + cf_head bytes, the head of
   prhPs_evs x [] for a closed quote, ps_evs_all_head), is `prh_live_at S E 0 + (Q + 1 + cf_head) <= LIVE_MAX`; the
   live bytes at event 0 are the entry's live requests (firstn 0 = [], hlive_from_nil), whose sum is blocks_bytes S
   (ps_live_ab, YCbq.blocks_bytes_bsum). That is the leaf's own per-call room (PRH_FnAlloc 4d8aeba047e5 :283). The
   request half is the text's unchanged ---- *)
Lemma ps_sum_map_snd : forall l : list (Z * Z), fold_right Z.add 0 (map snd l) = bsum l.
Proof. induction l as [|[a b] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma ps_room_entry : forall CTX CW D Q, ps_pre CTX CW D -> PjGrammar.scan (ps_x D) = Some Q ->
  LIVE_parse_string Q < cf_malloc_max /\ blocks_bytes (pi_S D) + (Z.of_nat Q + 1 + cf_head) <= LIVE_MAX.
Proof.
intros CTX CW D Q HPRE HQ.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HREQ & HEVS)).
split; [exact (HREQ Q HQ)|].
destruct (ps_evs_all_head (ps_x D) Q HQ) as (rest & Erest).
specialize (HEVS 0%nat (PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head))). rewrite Erest in HEVS.
specialize (HEVS eq_refl).
unfold prh_live_at, prh_ev_req in HEVS. cbn [firstn] in HEVS. rewrite PresetReqAt.hlive_from_nil in HEVS.
rewrite (ps_live_ab (pi_ly D) (pi_S D)), ps_sum_map_snd, <- (blocks_bytes_bsum B (pi_ly D) (pi_S D)) in HEVS.
exact HEVS.
Qed.
Lemma ps_count24_free : forall CTX CW D Q ly S a, ps_pre CTX CW D -> PjGrammar.scan (ps_x D) = Some Q ->
  PjGrammar.decode (ps_x D) = None ->
  ablocks B ly S = ablocks B (pi_ly D) (pi_S D) ++ [(a, Z.of_nat Q + 1 + cf_head)] ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros CTX CW D Q ly S a HPRE HQ HD Hab.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & H24 & _) & _).
pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass) (prhPs_evs (ps_x D) [])
  (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) 1) as P2.
assert (Hev : prhPs_evs (ps_x D) [] =
  [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)])
  by (unfold prhPs_evs; rewrite HQ, HD; reflexivity).
rewrite Hev in P2, H24. cbn [firstn] in P2.
unfold PresetReqAt.hlive_from in P2. cbn [fold_left PresetReqAt.hstep] in P2.
pose proof (ps_live_app D ly S a (Z.of_nat Q + 1 + cf_head) Hab) as HL. unfold ps_live in HL.
unfold PresetReqAt.hlive_from in HL. cbn [fold_left PresetReqAt.hstep] in HL.
rewrite <- (PresetReqAt.cnt_perm _ _ _ HL) in P2.
assert (E2 : YGcfRoomLive.ccnt24 S =
  Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))))
  by reflexivity.
rewrite E2. lia.
Qed.

(* ---- the NULL return: s2 = 0 is about to be moved to a0 and the frame restored. Its arm fact is the whole of ps_Q
   but for the return value; the cut names no register but sp, gp and tp, so it is the same in both images ---- *)
Definition ps_at_ret0 (CW : list (list Z)) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryw D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
(* the NULL return's cut over a world relation R (its carry at R, ps_carrywR; ps_at_ret0 is its instance at wle,
   ps_at_ret0_R_wle): the refusing paths reach it at wle, the bad escape after its fuzz_free at wle' segs RZ_cf *)
Definition ps_at_ret0R (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) (ly : alayout)
  (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carrywR R D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
Lemma ps_at_ret0_R_wle : forall CW D ly S Hp W regs mem md,
  ps_at_ret0 CW D ly S Hp W regs mem md = ps_at_ret0R (@wle segs) CW D ly S Hp W regs mem md.
Proof. reflexivity. Qed.

(* ---- THE CHAIN FROM q AT A CALL (WalkS4's S4_PsBase.v 91d94986c47 transfer, restated on walkkit 4eb03b7b7e8, where
   the kit's text gives the chain from prh_s0 F_parse_string q, the cursor facts (prh_cw_ok / prh_cur_low since the batch kit;
   prh_cur_ok before it) and the gap
   spZ regs + 16 <= q, so the PS_CHAIN / PS_QGAP stand-ins are GONE). parse_string's four calls (fuzz_malloc, hex4,
   put_utf8, fuzz_free) all run with s0 = prh_s0 F_parse_string q, so each callee's afn_pre_x needs a frame chain from
   there at the call's sp (the entry sp less the frame) in the CALL view. The text gives it at the ENTRY view; it
   transfers to a call view when the chain reads no byte the walk wrote before the call, i.e. none of its own frame
   [sp - 144, sp): every read is at or above prh_s0 F_parse_string q - 16, which is >= sp when the image's s0 offset
   is non-negative (pi_s0cur F_parse_string = Some 0 on both images: the image file proves the premise by
   computation). ---- *)
Definition ps_chain0 (D : ps_in) : Prop :=
  exists ch, achain (pi_ly D) (aview segs (w_H (pi_W D)) (pi_mem D)) (spZ (pi_regs D) - pi_frame F_parse_string)
    (prh_s0 F_parse_string (pi_q D)) ch.
Lemma ps_chain0_of_pre : forall CTX CW D, ps_pre CTX CW D -> ps_chain0 D.
Proof. intros CTX CW D (_ & _ & HCH & _). exact HCH. Qed.
(* the gap bound, now the kit's premise *)
Definition ps_qgap (D : ps_in) : Prop := spZ (pi_regs D) + 16 <= pi_q D.
Lemma ps_qgap_of_pre : forall CTX CW D, ps_pre CTX CW D -> ps_qgap D.
Proof. intros CTX CW D (_ & _ & _ & _ & _ & HG & _). exact HG. Qed.
(* THE TRANSFER (a theorem under its agreement premise, which every call site meets): parse_string writes nothing at
   or above sp before its last call - only its frame [sp - 144, sp), the hex4 slot inside it, and the new heap block;
   the cursor store (each image's PS_CURSOR_STORE) comes after the last call. *)
Lemma ps_chain_call : forall D (rd : reader),
  ps_chain0 D -> spZ (pi_regs D) + 16 <= prh_s0 F_parse_string (pi_q D) -> ly_top (pi_ly D) <= 2 ^ 64 ->
  (forall a, spZ (pi_regs D) <= a < 2 ^ 64 -> rd a = aview segs (w_H (pi_W D)) (pi_mem D) a) ->
  exists ch, achain (pi_ly D) rd (spZ (pi_regs D) - pi_frame F_parse_string) (prh_s0 F_parse_string (pi_q D)) ch.
Proof.
intros D rd (ch & [(Hv & Ech) | (H1 & H2 & H3 & H4 & H5)]) Hgap Htop Hrd; exists ch; [left; exact (conj Hv Ech)|].
right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
eapply fpchain_ext; [|lia|exact H4].
intros a Ha Ha2. apply rdword_ext. intros k Hk. apply Hrd. lia.
Qed.
(* the two cursor facts the free's trace needs (prh_cw_ok: the trace at the word s0 - 8 is in CW or the word is a
   pj_parse code word; prh_cur_low: the word at s0 - 16 is below the ceiling) at a call view that agrees with the entry
   view at and above sp *)
Lemma ps_cur_call : forall CTX CW D (rd : reader),
  ps_pre CTX CW D -> spZ (pi_regs D) + 16 <= prh_s0 F_parse_string (pi_q D) -> prh_s0 F_parse_string (pi_q D) <= 2 ^ 64 ->
  (forall a, spZ (pi_regs D) <= a < 2 ^ 64 -> rd a = aview segs (w_H (pi_W D)) (pi_mem D) a) ->
  (forall r w, In r (prh_free_sites F_parse_string) -> rdword rd (prh_s0 F_parse_string (pi_q D) - 8) = Some w ->
     In (prh_trace (pc_free_ra0 (as_code B)) r [w]) CW \/ In w (pi_call_rets F_pj_parse F_parse_value)) /\
  (forall w, rdword rd (prh_s0 F_parse_string (pi_q D) - 16) = Some w -> w < YM05.alloc_ceiling).
Proof.
intros CTX CW D rd (_ & _ & _ & HLOW & HCW & _) Hgap Htop Hrd. split.
- intros r w Hr Hw. apply (HCW r w Hr). rewrite <- Hw. symmetry. apply rdword_ext. intros k Hk. apply Hrd. lia.
- intros w Hw. apply (HLOW w). rewrite <- Hw. symmetry. apply rdword_ext. intros k Hk. apply Hrd. lia.
Qed.

(* ---- THE CHAIN AND THE CURSOR WORDS AT A CALL, OFF THE CALLER WORD (PsbTail2's lemmas, a working branch
   1585744db56 PSB_Tail.v:72-118, moved here verbatim). ps_chain_call / ps_cur_call ask the call view to be the entry
   view on all of [sp, 2 ^ 64); a cut whose carried relations exempt FP = [(q, q + 8)] gives it only off the caller
   word [q, q + 8). That suffices: the chain from s0 = prh_s0 F_parse_string q <= q is at most ONE record, because its
   next frame word (at s0 - 16) is below alloc_ceiling (the kit's prh_cur_low) and so at or below s0 (bad_next stops the
   walk); the record and the two cursor words read only [s0 - 16, s0), below q. ---- *)
Lemma ps_chain_call_offq : forall CTX CW (D : ps_in) (rd : reader),
  ps_pre CTX CW D -> spZ (pi_regs D) + 16 <= prh_s0 F_parse_string (pi_q D) ->
  prh_s0 F_parse_string (pi_q D) <= pi_q D -> ly_top (pi_ly D) <= 2 ^ 64 ->
  (forall a, spZ (pi_regs D) <= a < 2 ^ 64 -> ~ (pi_q D <= a < pi_q D + 8) ->
     rd a = aview segs (w_H (pi_W D)) (pi_mem D) a) ->
  exists ch, achain (pi_ly D) rd (spZ (pi_regs D) - pi_frame F_parse_string) (prh_s0 F_parse_string (pi_q D)) ch.
Proof.
intros CTX CW D rd HPRE Hgap Hs0q Htop Hrd.
pose proof HPRE as (((_ & _ & _ & _ & _ & Hstk & _) & _) & _ & (ch & HCH) & HLOW & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HWIN & Hqlo & Hqhi & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof HWIN as (_ & _ & Hetop & _).
unfold prh_cur_low in HLOW.
assert (Hrw : forall a, prh_s0 F_parse_string (pi_q D) - 16 <= a < prh_s0 F_parse_string (pi_q D) ->
  rd a = aview segs (w_H (pi_W D)) (pi_mem D) a) by (intros a Ha; apply Hrd; lia).
destruct HCH as [(Hv & Ech) | (H1 & H2 & H3 & H4 & H5)].
- exists ch. left. exact (conj Hv Ech).
- destruct ch as [|[[fp ra] nfp] rest].
  + exists []. right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
    cbn [fpchain] in H4 |- *. destruct H4 as (r0 & Hr0 & Hr0b). exists r0. split; [|exact Hr0b].
    rewrite <- Hr0. apply rdword_ext. intros kk Hkk. apply Hrw. lia.
  + cbn [fpchain] in H4. destruct H4 as (Efp & Hfp8 & Hra & Hnfp & Hra4 & Hrest).
    assert (Hn : nfp < YM05.alloc_ceiling) by (apply HLOW; rewrite <- Efp; exact Hnfp).
    assert (Hbad : bad_next fp (ly_top (pi_ly D)) nfp = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hbad in Hrest. subst rest.
    exists [(fp, ra, nfp)]. right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
    cbn [fpchain]. split; [exact Efp|]. split; [exact Hfp8|].
    split; [rewrite <- Hra; apply rdword_ext; intros kk Hkk; apply Hrw; lia|].
    split; [rewrite <- Hnfp; apply rdword_ext; intros kk Hkk; apply Hrw; lia|].
    split; [exact Hra4|]. rewrite Hbad. reflexivity.
Qed.

Lemma ps_cur_call_offq : forall CTX CW (D : ps_in) (rd : reader),
  ps_pre CTX CW D -> spZ (pi_regs D) + 16 <= prh_s0 F_parse_string (pi_q D) ->
  prh_s0 F_parse_string (pi_q D) <= 2 ^ 64 -> prh_s0 F_parse_string (pi_q D) <= pi_q D ->
  (forall a, spZ (pi_regs D) <= a < 2 ^ 64 -> ~ (pi_q D <= a < pi_q D + 8) ->
     rd a = aview segs (w_H (pi_W D)) (pi_mem D) a) ->
  (forall r w, In r (prh_free_sites F_parse_string) -> rdword rd (prh_s0 F_parse_string (pi_q D) - 8) = Some w ->
     In (prh_trace (pc_free_ra0 (as_code B)) r [w]) CW \/ In w (pi_call_rets F_pj_parse F_parse_value)) /\
  (forall w, rdword rd (prh_s0 F_parse_string (pi_q D) - 16) = Some w -> w < YM05.alloc_ceiling).
Proof.
intros CTX CW D rd HPRE Hgap Htop Hs0q Hrd.
pose proof HPRE as (_ & _ & _ & HLOW & HCW & _). split.
- intros r w Hr Hw. apply (HCW r w Hr). rewrite <- Hw. symmetry. apply rdword_ext. intros kk Hkk. apply Hrd; lia.
- intros w Hw. apply (HLOW w). rewrite <- Hw. symmetry. apply rdword_ext. intros kk Hkk. apply Hrd; lia.
Qed.

(* ---- THE CLOSE: the state after parse_string's `ret` (the entry's callee-saved registers, sp, gp, tp restored),
   with the carried journal (budget []) and kept relation and the post body, is ps_post CW D at the empty budget ---- *)
Lemma ps_close : forall CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs,
  0 <= STK_parse_string ->
  ps_carry D ly2 S2 Hp2 W2 mem2 md2 k FPs ->
  aregs_preserved (pi_regs D) regs2 ->
  ps_Q D ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  ps_post CW D W2 (mkCfg (YK11.mkst regs2 (YK11.getr (pi_regs D) 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs HSTK (HJ & HK & _) HP HQ.
unfold ps_post.
exact (YCbqGwild.fpostW_xb_of_kept (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
  [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_Q D)
  [(pi_q D, pi_q D + 8)] FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k [] HSTK (ps_wb_nil CW) HJ HK (fun a H => H) HP HQ).
Qed.


(* ==== THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z; WalkS4's S4_PsBase.v be8c964d45c, mirrored). An SRr post is
   OPAQUE once Qed, so an end-state invariant must be in the segment's statement: every stretch is stated over an
   invariant P of the memory with srr_inv_laws segs P (and srr_inv_call segs P where it crosses a kit call), carried at
   every cut (ps_carryP: ps_carry with `/\ P mem` last) and at the post (ps_postP: ps_Q /\ P mem'). The function's top
   instantiates P ONCE as ps_mn D (memnorm of the entry memory gives memnorm at every later memory: the memnorm keep of
   the kit's m-form post). Every definition above stays byte-identical; the stable statements are the P := (fun _ => True)
   corollaries (the *_T lemmas here and PSB_Base's psb_seg_*_of_True). ==== *)
Definition ps_mn (D : ps_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm segs (pi_mem D) -> YAkMemnorm.memnorm segs m.
Lemma ps_mn_laws : forall D, srr_inv_laws segs (ps_mn D).
Proof. intros D. exact (srr_inv_laws_imp segs (YAkMemnorm.memnorm segs) (pi_mem D) (srr_inv_laws_memnorm_k segs)). Qed.
Lemma ps_mn_call : forall D, srr_inv_call segs (ps_mn D).
Proof. intros D. exact (srr_inv_call_imp segs (pi_mem D)). Qed.
Lemma ps_mn_entry : forall D, ps_mn D (pi_mem D).
Proof. intros D H. exact H. Qed.
Lemma srr_inv_laws_True : srr_inv_laws segs (fun _ => True).
Proof. split; intros; exact I. Qed.
Lemma srr_inv_call_True : srr_inv_call segs (fun _ => True).
Proof. intros m m' _ _. exact I. Qed.

(* ---- THE HAND-OFF to a stretch that may cross the bad escape's fuzz_free. A stretch runs at wle (SRr, the engine's
   runners and call rules) and hands its last state to the next stretch's SRr' fact (ps_hand); ps_SRr'_of_SRr turns
   the whole into SRr' (YA0nH.SRr_SRr', then SRrG_bind at wle'). ---- *)
Lemma ps_SRr'_of_SRr : forall W c (Q : world segs -> config -> Prop),
  SRr segs W c (fun W' c' => SRr' segs YGcfRehidePost.RZ_cf W' c' Q) -> SRr' segs YGcfRehidePost.RZ_cf W c Q.
Proof.
intros W c Q H. unfold SRr'.
eapply (SRrG_bind segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf));
  [exact (SRr_SRr' segs YGcfRehidePost.RZ_cf W c _ H)|].
intros W' c' _ HQ. exact HQ.
Qed.
Lemma ps_hand : forall W c (Q : world segs -> config -> Prop),
  SRr' segs YGcfRehidePost.RZ_cf W c Q -> SRr segs W c (fun W' c' => SRr' segs YGcfRehidePost.RZ_cf W' c' Q).
Proof. intros W c Q H. apply SRr_ret. exact H. Qed.

Section gp.
Variable P : (word -> option byte) -> Prop.
Definition ps_carryP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) : Prop :=
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) /\
  P mem.
(* the same at a BUDGET WS (the NULL return after the bad escape's fuzz_free, ps_carryw's twin) *)
Definition ps_carryPw (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  AJW (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) /\
  P mem.
(* ps_carryPw over a world relation R (a copy of its body with the journal and the kept relation at R; ps_carryPw is
   its instance at wle, ps_carryPw_R_wle): the bad escape's NULL return carries it at wle' segs RZ_cf *)
Definition ps_carryPwR (R : world segs -> world segs -> Prop) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (k : Z) (FPs : list (Z * Z)) (WS : list (list Z)) : Prop :=
  ajournal_xwR (SK := SK) segs B PST ARx R (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md k WS /\
  cj_keptR (SK := SK) segs B PST R STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md /\
  ps_saved D W mem /\
  src_rd W mem (pi_text D) (pi_tb D) /\
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) /\
  P mem.
Lemma ps_carryPw_R_wle : forall D ly S Hp W mem md k FPs WS,
  ps_carryPw D ly S Hp W mem md k FPs WS = ps_carryPwR (@wle segs) D ly S Hp W mem md k FPs WS.
Proof. reflexivity. Qed.
Definition ps_QP (D : ps_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  ps_Q D ly' S' Hp' W' regs' mem' md' /\ P mem'.
Definition ps_postP (CW : list (list Z)) (D : ps_in) : world segs -> config -> Prop :=
  YCbqGwild.fpostW_xb (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QP D).
(* ps_postP over a world relation R (a copy of its body at YCbqGwild.fpostW_xbR; ps_postP is its instance at wle,
   ps_postP_R_wle) *)
Definition ps_postPR (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) :
  world segs -> config -> Prop :=
  YCbqGwild.fpostW_xbR (SK := SK) segs B PST ARx R (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
    [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QP D).
Lemma ps_postP_R_wle : forall CW D, ps_postP CW D = ps_postPR (@wle segs) CW D.
Proof. reflexivity. Qed.
(* a post at wle is the post at wle' segs RZ_cf (the journal's world conjunct, YA0nH.wle_wle') *)
Lemma ps_postP_lift : forall CW D W' c',
  ps_postP CW D W' c' -> ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D W' c'.
Proof.
intros CW D W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ).
exists ly', S', Hp', regs', mem', md', k, WS. split; [exact Hc|]. split; [exact HB|].
split; [exact (ajournal_xwR_mono (SK := SK) segs B PST ARx (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
  (wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)|].
split; [exact HX|]. split; [exact HP | exact HQ].
Qed.
(* THE HAND-OFF FORM: a stretch runs at wle (SRr) into ps_finP, the SRr' fact of the stretch it hands its last state
   to; ps_finP_SRr' makes the whole an SRr' fact. A hand-off to a stretch that may cross the bad escape's fuzz_free is
   ps_finP_hand; to one that ends at wle (retok; ret0 before the free), ps_finP_of_postP. *)
Definition ps_finP (CW : list (list Z)) (D : ps_in) : world segs -> config -> Prop :=
  fun W' c' => SRr' segs YGcfRehidePost.RZ_cf W' c' (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Lemma ps_finP_SRr' : forall CW D W c, SRr segs W c (ps_finP CW D) ->
  SRr' segs YGcfRehidePost.RZ_cf W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Proof.
intros CW D W c H. exact (ps_SRr'_of_SRr W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D) H).
Qed.
Lemma ps_finP_hand : forall CW D W c,
  SRr' segs YGcfRehidePost.RZ_cf W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D) -> SRr segs W c (ps_finP CW D).
Proof.
intros CW D W c H. exact (ps_hand W c (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D) H).
Qed.
Lemma ps_finP_of_postP : forall CW D W c, SRr segs W c (ps_postP CW D) -> SRr segs W c (ps_finP CW D).
Proof.
intros CW D W c H. eapply SRr_mono; [exact H|].
intros W' c' _ HQ. unfold ps_finP, SRr'.
apply (SRrG_ret segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf)).
exact (ps_postP_lift CW D W' c' HQ).
Qed.
Definition ps_at_ret0P (CW : list (list Z)) (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPw D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
(* ps_at_ret0P over a world relation R (its carry at R, ps_carryPwR; ps_at_ret0P is its instance at wle,
   ps_at_ret0P_R_wle) *)
Definition ps_at_ret0PR (R : world segs -> world segs -> Prop) (CW : list (list Z)) (D : ps_in) (ly : alayout)
  (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPwR R D ly S Hp W mem md k [] WS) /\ ps_gptp D regs /\
  getr regs 2 = w64 (PS_SP D) /\
  room_live_cf S /\
  blocks_bytes S <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) /\
  ps_Qres D 0 ly S Hp W mem md.
Lemma ps_at_ret0P_R_wle : forall CW D ly S Hp W regs mem md,
  ps_at_ret0P CW D ly S Hp W regs mem md = ps_at_ret0PR (@wle segs) CW D ly S Hp W regs mem md.
Proof. reflexivity. Qed.
(* a carry at budget [] is a budgeted carry within any cursor set (every cut but the bad escape's NULL return) *)
Lemma ps_carryPw_nil : forall CW D ly S Hp W mem md, (exists k, ps_carryP D ly S Hp W mem md k []) ->
  exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPw D ly S Hp W mem md k [] WS.
Proof. intros CW D ly S Hp W mem md (k & H). exists k, []. split; [apply ps_wb_nil | exact H]. Qed.
(* THE CLOSE at P: the state after `ret` with ps_carryP (budget []) and the post body is ps_postP CW D *)
Lemma ps_closeP : forall CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs,
  0 <= STK_parse_string ->
  ps_carryP D ly2 S2 Hp2 W2 mem2 md2 k FPs ->
  aregs_preserved (pi_regs D) regs2 ->
  ps_Q D ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  ps_postP CW D W2 (mkCfg (YK11.mkst regs2 (YK11.getr (pi_regs D) 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs HSTK (HJ & HK & _ & _ & _ & HPm) HP HQ.
unfold ps_postP.
exact (YCbqGwild.fpostW_xb_of_kept (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
  [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QP D)
  [(pi_q D, pi_q D + 8)] FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k [] HSTK (ps_wb_nil CW) HJ HK (fun a H => H) HP
  (conj HQ HPm)).
Qed.
(* THE CLOSE at P from a REBASED journal (the NULL return after the bad escape: its cut carries a budgeted journal,
   the run takes it rebased, YCbqGwild.ajournal_xw_rebase, so the run's journal is from the entry with the cut's depot
   d); the post puts the budget back (ajournal_xw_unbase0 at the cut's wild-part inclusion) *)
Lemma ps_closePw : forall CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs WS d,
  0 <= STK_parse_string ->
  YCbqGwild.wbudget CW 0 WS ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (set_depot d (pi_S D)) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly2 S2 Hp2 W2 mem2 md2 k ->
  incl (wild_part (as_universe B) d) (wild_part (as_universe B) (st_depot (pi_S D)) ++ WS) ->
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly2 S2 W2 mem2 md2 ->
  aregs_preserved (pi_regs D) regs2 ->
  ps_Q D ly2 S2 Hp2 W2 regs2 mem2 md2 -> P mem2 ->
  ps_postP CW D W2 (mkCfg (YK11.mkst regs2 (YK11.getr (pi_regs D) 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs WS d HSTK HB HJ Hinc HK HP HQ HPm.
unfold ps_postP.
exact (YCbqGwild.fpostW_xb_of_kept (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
  [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QP D)
  [(pi_q D, pi_q D + 8)] FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS HSTK HB
  (YCbqGwild.ajournal_xw_unbase0 (SK := SK) segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d WS HJ Hinc)
  HK (fun a H => H) HP (conj HQ HPm)).
Qed.
(* ps_closePw over a world relation R (the NULL return after the bad escape's fuzz_free, its journal and kept relation
   at wle' segs RZ_cf): the engine's closer and budget adapter over R *)
Lemma ps_closePwR : forall (R : world segs -> world segs -> Prop) CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs WS d,
  0 <= STK_parse_string ->
  YCbqGwild.wbudget CW 0 WS ->
  ajournal_xR (SK := SK) segs B PST ARx R (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (set_depot d (pi_S D)) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly2 S2 Hp2 W2 mem2 md2 k ->
  incl (wild_part (as_universe B) d) (wild_part (as_universe B) (st_depot (pi_S D)) ++ WS) ->
  cj_keptR (SK := SK) segs B PST R STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly2 S2 W2 mem2 md2 ->
  aregs_preserved (pi_regs D) regs2 ->
  ps_Q D ly2 S2 Hp2 W2 regs2 mem2 md2 -> P mem2 ->
  ps_postPR R CW D W2 (mkCfg (YK11.mkst regs2 (YK11.getr (pi_regs D) 1) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros R CW D ly2 S2 Hp2 W2 regs2 mem2 md2 k FPs WS d HSTK HB HJ Hinc HK HP HQ HPm.
unfold ps_postPR.
exact (YCbqGwild.fpostW_xb_of_keptR (SK := SK) segs B PST ARx R (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D)
  [(pi_q D, pi_q D + 8)] (pi_regs D) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QP D)
  [(pi_q D, pi_q D + 8)] FPs ly2 S2 Hp2 W2 regs2 mem2 md2 k WS HSTK HB
  (YCbqGwild.ajournal_xw_unbase0R (SK := SK) segs B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d WS HJ Hinc)
  HK (fun a H => H) HP (conj HQ HPm)).
Qed.
End gp.

(* ---- the stable statements are the P := (fun _ => True) instances, both ways ---- *)
Lemma ps_carryP_T : forall D ly S Hp W mem md k FPs,
  ps_carry D ly S Hp W mem md k FPs <-> ps_carryP (fun _ => True) D ly S Hp W mem md k FPs.
Proof.
intros. split; [intros (H1 & H2 & H3 & H4 & H5); exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 I)))))|].
intros (H1 & H2 & H3 & H4 & H5 & _); exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.
Lemma ps_ex_carryP_T : forall D ly S Hp W mem md,
  (exists k, ps_carry D ly S Hp W mem md k []) <-> (exists k, ps_carryP (fun _ => True) D ly S Hp W mem md k []).
Proof. intros. split; intros (k & H); exists k; apply ps_carryP_T; exact H. Qed.
Lemma ps_ex_carryPw_T : forall CW D ly S Hp W mem md,
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryw D ly S Hp W mem md k [] WS) <->
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPw (fun _ => True) D ly S Hp W mem md k [] WS).
Proof.
intros. split; intros (k & WS & HB & H1 & H2 & H3 & H4 & H5); exists k, WS; split; try exact HB.
- exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 I))))).
- destruct H5 as [H5 _]. exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.
Lemma ps_postP_T : forall CW D W' c', ps_postP (fun _ => True) CW D W' c' <-> ps_post CW D W' c'.
Proof.
intros CW D W' c'. split.
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ & _).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP HQ))))).
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP (conj HQ I)))))).
Qed.
Lemma ps_at_ret0P_T : forall CW D ly S Hp W regs mem md,
  ps_at_ret0 CW D ly S Hp W regs mem md <-> ps_at_ret0P (fun _ => True) CW D ly S Hp W regs mem md.
Proof.
intros. split; intros (Hc & H); (split; [apply ps_ex_carryPw_T; exact Hc | exact H]) +
  (split; [apply (proj2 (ps_ex_carryPw_T _ _ _ _ _ _ _ _)); exact Hc | exact H]).
Qed.
Lemma ps_postPR_T : forall R CW D W' c', ps_postPR (fun _ => True) R CW D W' c' <-> ps_postR R CW D W' c'.
Proof.
intros R CW D W' c'. split.
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ & _).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP HQ))))).
- intros (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ).
  exists ly', S', Hp', regs', mem', md', k, WS. exact (conj Hc (conj HB (conj HJ (conj HX (conj HP (conj HQ I)))))).
Qed.
Lemma ps_ex_carryPwR_T : forall R CW D ly S Hp W mem md,
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carrywR R D ly S Hp W mem md k [] WS) <->
  (exists k WS, YCbqGwild.wbudget CW 0 WS /\ ps_carryPwR (fun _ => True) R D ly S Hp W mem md k [] WS).
Proof.
intros. split; intros (k & WS & HB & H1 & H2 & H3 & H4 & H5); exists k, WS; split; try exact HB.
- exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 I))))).
- destruct H5 as [H5 _]. exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.
Lemma ps_at_ret0PR_T : forall R CW D ly S Hp W regs mem md,
  ps_at_ret0R R CW D ly S Hp W regs mem md <-> ps_at_ret0PR (fun _ => True) R CW D ly S Hp W regs mem md.
Proof.
intros R CW D ly S Hp W regs mem md. split; intros (Hc & H); split; try exact H.
- exact (proj1 (ps_ex_carryPwR_T R CW D ly S Hp W mem md) Hc).
- exact (proj2 (ps_ex_carryPwR_T R CW D ly S Hp W mem md) Hc).
Qed.

(* the entry stretch at one record, at the top instance P := ps_mn D, IS the kit's m-form budgeted text AT THAT RECORD
   (the kit cut 7cdbb61b5fa0, PRH_FnReader.v f1ae32e3b2cd, primed: SRr' segs RZ_cf, and fpostWbm, AFTER-FREE-ONLY, is at
   wle' segs RZ_cf; ps_pre is its premises in its order, fpostWbm .. (wbudget CW 0) .. (ps_QT D) its post):
   fpostWbm .. Q is fpostW_xbR (wle' ..) .. (fQmn mem Q), and ps_QP (ps_mn D) D gives fQmn (pi_mem D) (ps_QT D) with
   ps_Q's conjuncts put in the text's order (ps_QT_of_Q) *)
Lemma ps_postm_is_K0 : forall CW D W' c',
  ps_postPR (ps_mn D) (wle' segs YGcfRehidePost.RZ_cf) CW D W' c' ->
  fpostWbm B ARx SK (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D) [(pi_q D, pi_q D + 8)] (pi_regs D)
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QT D) W' c'.
Proof.
intros CW D W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HX & HP & HQ & HMN).
exists ly', S', Hp', regs', mem', md', k, WS.
exact (conj Hc (conj HB (conj HJ (conj HX (conj HP (conj (ps_QT_of_Q D ly' S' Hp' W' regs' mem' md' HQ) HMN)))))).
Qed.
Lemma ps_holds_of_entryP : forall CTX CW,
  (forall D, ps_pre CTX CW D ->
     SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (pa_sigma AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
       (ps_postPR (ps_mn D) (wle' segs YGcfRehidePost.RZ_cf) CW D)) ->
  forall D, ps_pre CTX CW D ->
  SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (pa_sigma AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
    (fpostWbm B ARx SK (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D) [(pi_q D, pi_q D + 8)] (pi_regs D)
       (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QT D)).
Proof.
intros CTX CW H D HP. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (H D HP)|].
intros W' c' _ HQ. exact (ps_postm_is_K0 CW D W' c' HQ).
Qed.

(* THE TEXT FROM THE RECORDS: the per-record statement at every record is the KIT TEXT tparse_string_specX (the kit cut
   7cdbb61b5fa0). This type-checks only because ps_pre is exactly its premises (24, in its order; the two live counts
   and the hull budget are ps_pre's ninth conjunct) over the record's fields and fpostWbm .. (ps_QT D) exactly its post
   (ps_live / ps_rposK / ps_excl unfold to its Permutation / forall clauses). No per-record premise: the
   post-implication form needs none *)
Lemma ps_K0_of_records : forall CTX CW,
  (forall D, ps_pre CTX CW D ->
     SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (pa_sigma AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
       (fpostWbm B ARx SK (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D) [(pi_q D, pi_q D + 8)] (pi_regs D)
          (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) (ps_QT D))) ->
  tparse_string_specX B ARx SK CTX CW.
Proof.
intros CTX CW H. unfold tparse_string_specX.
intros most own ly S Hp W regs mem md ch e q text len p d tb Lam peak cnt fail ran
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.
pose (D := mkPsIn ly S Hp W regs mem md ch e q text len p d tb Lam peak cnt fail ran most own).
exact (H D
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj (conj H9 (conj H10 H11)) (conj H12
  (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22 (conj H23
  H24)))))))))))))))))))))).
Qed.

End ps.
