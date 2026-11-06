(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_head.v, with its module paths and module names changed; 4555 of its 4719 lines of code are new or changed and 1142 lines of the source are left out. *)
(* Theorem Labs, 2026-10: block KEY of parse_items' image-B walk.
   PI_O_KEY (0x87bc0) through PI_O_VAL (0x87cd8): skip_ws, the quote test, parse_string, the store into keys[n],
   skip_ws, the colon test, in->p++. The pres and the specs are in lib/B/Prog/PItems_pres.v; the
   preamble below is lib/B/Prog/PItems_body.v's, verbatim, so the proof inlines there unchanged.
   REBOUND to the kit walkkit-next f97c8b2f046b (form (b), post-implication; lane PItemsB.SegBody): no rp_*
   binders, the ledger's most / own, fpre's frm_zero, parse_string's per-arm post (pik_ps_postX), the travelling
   PItems_posb.pi_posb / pi_live composed at every call, and the missing-colon hand-off's class-24 count derived in
   place (pik_cc24).
   REBOUND to the batch kit 240b06ed4fd4 (lane PItemsB.K1Body.K1Key): the cursor set CW and the BUDGETED journal
   the cursor set CW and the BUDGETED journal (pi_aj .. WS0 at wbudget CW 0; runs on the rebased empty-budget journal,
   YCbqGwild.ajournal_xw_rebase / unbase0; skip_ws by YCbqGcallW.aj_call_xW_sp on the rebased journal, parse_string by
   wbudget CW 0), parse_string's batch-kit post (its refused arm's OUTCOME exclusion and ledger), the batch-kit post's OUTCOME,
   the kit post's OUTCOME, ledger move over the all-granted trace and free order at each exit, and the loop invariants
   pi_grant / cap / pi_ncaps / pi_forder with the free-list model carried across the key (pik_inner, pik_inner2).
   THE RE-HIDING MOVE (the texts' current form): parse_string's text concludes YA0nH.SRr' segs RZ_cf, so every stretch
   runs at the world relation wle' SEGS RZ_cf (journals ajournal_xwR, the R runners and call rules, SRr'); skip_ws's
   plain text is lifted into the R call rule (pik_skw_lift). THE HULL (route (b)): parse_string's hull budget is paid
   from pi_ent's at the block (PItems_posb.pi_posb_budget), its use extends the travelling pi_posb, and each exit's post
   carries the use over the call's all-granted list. THE INJECTED READING (tpiP_injected): granted at every all-granted
   exit; at parse_string's refused arm the chosen failure is the only refused outcome, and the allocator's refusal is
   refuted by parse_string's own exclusion (pik_inj_excl). The post is built through the text's record tpiP_R.
   Numerals: 4, 8, 16, 24, 32, 40, 56, 144 are LENGTHs (frame / structure byte offsets); 34, 58 are WORDs (ASCII);
   every pc is PI_AT PI_O_* (plus a LENGTH inside the block) at the image-B listing instance.
   rule 24: no function proved
   proves no function (kind: segment lemma of an existing walk; the top theorem that proves parse_items is in
   another file) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
(* the batch's travelling overlay invariant (memnorm) and its carrier across a runner run (srr_inv_laws_memnorm_k) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
(* the request bound of the harness allocator: cf_malloc_max + 15 <= 2 ^ 30 (the key string's length bound) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_ledk1 PItems_forder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_kept PItems_agr.
(* PItems_value_model.v's pure container lemmas (pi_cont_fd, pi_cont_frame, pi_cont_frame_slot) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_value_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_shape.
(* the travelling run position and live requests of form (b), and the live-count model *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
Import ListNotations.
(* the walk's world relation wle' SEGS RZ_cf: SRrG / SRr' and the R lemmas (YA0nH, YSRrG), the zone (YGcfRehidePost);
   the hull budget and use (PresetHullBudget) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section body. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PLb := PL_prog_B.
#[local] Notation PIb := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ Lb PIb).
#[local] Notation VALb := (@pa_val _ Lb PIb).
#[local] Notation PIATb o := (@PI_AT _ Lb PIb o).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib (PI := PIb) B.

(* the epilogue, PItems_entry.v's pi_epi_holds (the top supplies it as EPI : forall d, pi_epi_spec B ARx SK d); the value
   segment is NOT a Section hypothesis: each step takes pi_val_spec at its own d / N, as PItems_top.v consumes it *)
Hypothesis HEPI : forall d, pi_epi_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d.

(* the callee texts (the kit's, lib/A), at this image and at EVERY float state the run can reach *)
Hypothesis TSKW : forall fy : YK11.FPState, tskip_ws_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK.
Hypothesis TGROW : forall (fy : YK11.FPState) CTX0,
  tgrow_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0.
(* The batch kit (240b06ed4fd4): parse_string's text takes the cursor set CW (prh_cw_ok, wild_room, post at wbudget CW 0).
   OWNER: the kit owner (lib/A/PRH_FnReader.v tparse_string_specX). *)
Hypothesis TPSTR : forall (fy : YK11.FPState) CTX0 CW,
  tparse_string_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0 CW.
Hypothesis TFREE : forall fy : YK11.FPState, tfuzz_free_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK.

(* the instance's harness head is the model's (PresetReqAt.HEAD, alloc.c's 16): parse_string's arm lists prhPs_evs
   (over cf_head) are rd_hevs of jr_string's traces (over HEAD) by prhPs_evs_model under it.
   OWNER: the instance (CfParams_preset's cf_head; reflexivity at the instance). *)
Hypothesis PIK_HEAD : cf_head = PresetReqAt.HEAD.

(* ---- the image fact the walk needs of the abstract PrhImg instance (PItems_body_free.v's FRPI, same text): image B's
   parse_items frame is the listing's (PI_FRAME, the `addi sp, sp, -144` of the prologue).
   OWNER: lane PItemsB (the preamble); discharged at PIi := prh_img_B by reflexivity. *)
Hypothesis PIK_FR : PRH_Base.pi_frame F_parse_items = PI_FRAME.

(* the frames of the abstract PrhImg are lengths. At PIi := prh_img_B each
   pi_frame value is a non-negative literal. *)
Hypothesis PIK_FR0 : forall F, 0 <= PRH_Base.pi_frame F.

(* the return site of the first skip_ws call, a byte offset inside the block *)
Definition PIK_O_SKW1R : Z := PI_O_KEY + 8.

(* the data inside pi_body_pre's existential, at its witnesses (PItems_pres.v pi_body_pre, verbatim) *)
Definition pik_inner (ly : alayout) (S : astate) (regs0 : bvmap 5 word) (e q v : Z) (o : bool) (text len : Z)
  (tb : list Z) (p : Z) (d : nat)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (kr : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z)
  (Wc : world SEGS) (memc : word -> option byte) (N : nat)
  (f n cap : nat) (acc : list (list Z * jv)) (kids keys : Z) (Di : list (Z * Z)) (pc : Z) (ok0 : list bool)
  (tr0 : list ev) (D0 Lamc : list (Z * Z)) (peakc cntc failc ranc : Z) : Prop :=
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own /\
  (length (rest_atR tb text pc) <= N)%nat /\ (n < cap)%nat /\
  pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) (prh_lin Lamc) o v kids keys n cap acc Di /\
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
  pj_apartR (pi_sblk o kids keys cap) v /\
  Permutation D0 (pi_sblk o kids keys cap ++ Di) /\
  (2 * length (rest_atR tb text pc) + 1 <= f)%nat /\
  pi_run_eqB d o (rest_atR tb text p) ok0 tr0 f n cap (rev acc) (rest_atR tb text pc) /\
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
  rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
  PItems_posb.pi_posb S Sc tr0 /\
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
  blocks_bytes Sc <= blocks_bytes S + PRH_Charge.prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
  Ledger.lsum D0 = PjGrammar.held tr0 /\
  rd_room Sc (snd (fst (pi_jrb f (Nat.succ d) o n cap (rev acc) (rest_atR tb text pc) []))) /\
  (* THE BATCH KIT'S INVARIANTS (pi_body_pre's tail, verbatim): the granted prefix, the capacities, the free order and its
     model after the member's grow *)
  pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap (Nat.succ n) /\
  pi_ncaps (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) kids acc /\
  exists af, pi_forder (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) (prh_lin Lamc) o kids keys n Di acc af /\
    pi_fl_eqB d o (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc).

(* ---- THE STRETCH AFTER THE FIRST skip_ws (0x87bc8 .. PI_O_VAL): the call state's pre (memory memc, the run
   before the call wrote nothing there: memr agrees with it on the world's reader), skip_ws's widened journal from
   that state, its window clause and its post, and the caller's journal at the return state. ---- *)
Definition pik_k1_spec (d : nat) (CTX0 CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v text len tb p
    Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc memr mdc k (regs : bvmap 5 word)
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc
    ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 (regs2 : bvmap 5 word) WS0,
  pi_fpok fx0 fxc ->
  pi_ent (L := Lb) (PA := PIb) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v
    true CTX0 CW ->
  (* the overlay's normality at the return state, and skip_ws's post S' = S (tskip_ws_specX): the travelling position
     and live requests of the call state (pik_inner) are the return state's *)
  YAkMemnorm.memnorm SEGS mem2 -> S2 = Sc ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  pi_regs regs q v true -> pi_regs_body (L := Lb) (PA := PIb) regs Wc memc v -> getr regs 21 = w64 (-1) ->
  pik_inner ly S regs0 e q v true text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc N
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  mrestrict (w_H Wc) memr = mrestrict (w_H Wc) memc -> ARx lyc Sc Hpc Wc memr mdc ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_skip_ws + (PI_FRAME + e))
    (spZ regs + (PI_FRAME + e)) [(q, q + 8)] lyc Sc Hpc Wc memr mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs <= a < spZ regs + (PI_FRAME + e) -> ~ inFP [(q, q + 8)] a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memr a) ->
  aregs_preserved regs regs2 ->
  (room_live_cf Sc -> room_live_cf S2) -> Hp2 = Hpc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 mem2 Lamc peakc cntc failc ranc most own ->
  pj_in_okR SEGS (mrestrict (w_H W2) mem2) q text len
    (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text pc)))) (Z.of_nat d + 1) tb ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIK_O_SKW1R) regs2 mem2 md2)
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)).

(* the `mv a0, s1` before the parse_string call, a byte offset inside the block *)
Definition PIK_O_STR : Z := PI_O_KEY + 72.

(* ---- THE STRETCH FROM THE OPENING QUOTE (0x87c08 .. PI_O_VAL): the block's own pre (pik_inner) at the cursor pc,
   which is on a quote ---- *)
Definition pik_k2_spec (d : nat) (CTX0 CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v text len tb p
    Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc mdc k (regs : bvmap 5 word)
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc WS0,
  pi_ajR (L := Lb) (PA := PIb) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc
    memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_fpok fx0 fxc ->
  pi_ent (L := Lb) (PA := PIb) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v
    true CTX0 CW ->
  (* the overlay's normality at the state this stretch starts from (its position and live requests: pik_inner) *)
  YAkMemnorm.memnorm SEGS memc ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  pi_regs regs q v true -> pi_regs_body (L := Lb) (PA := PIb) regs Wc memc v -> getr regs 21 = w64 (-1) ->
  pik_inner ly S regs0 e q v true text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc N
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  pc < text + len -> nth_error tb (Z.to_nat (pc - text)) = Some 34 ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIK_O_STR) regs memc mdc)
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)).


(* the return site of the parse_string call, a byte offset inside the block *)
Definition PIK_O_STRR : Z := PI_O_KEY + 80.
(* the `mv a0, s1` before the second skip_ws call (0x87c7c), a byte offset inside the block *)
Definition PIK_O_SKW2 : Z := PI_O_KEY + 188.

(* parse_string's post: the text's own named post lib/A/PRH_FnReader.v tpstP_Q (tpstP_Q_check: it IS the inner Q of
   tparse_string_specX's m-form), in this file's argument order: what the call rule's Q must be, letter for letter.
   No top-level position: each arm (tpstP_ANone / tpstP_ASome1 .. 4) ends with its live-request permutation and its
   position implication over prhPs_evs .. [the arm's outcomes: [] / [false] / [true]]; the REFUSED arm carries THE
   OUTCOME's exclusion over the all-granted list prhPs_evs .. [] and fuzz_malloc's refusal-arm ledger. Read its hull
   use by pik_ps_hull. *)
Definition pik_ps_postX (fy : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (Lam : list (Z * Z)) (peak cnt fail ran most own q text len p d : Z) (tb : list Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tpstP_Q (fx := fy) (L := Lb) (PA := PIb) B most own ly S Hp W q text len p d tb Lam peak cnt fail ran.

(* ---- THE STRETCH AFTER parse_string (0x87c10 .. PI_O_VAL): the call state's pre (memory memr agrees with memc on
   the world's reader), parse_string's widened journal from that state, its window clause and its post ---- *)
Definition pik_k3_spec (d : nat) (CTX0 CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v text len tb p
    Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc memr mdc k (regs : bvmap 5 word)
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc
    ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 (regs2 : bvmap 5 word) WS0 WS1,
  pi_fpok fx0 fxc ->
  pi_ent (L := Lb) (PA := PIb) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v
    true CTX0 CW ->
  (* the overlay's normality at the return state; the position and live requests there are parse_string's post's
     (pik_ps_postX, per arm) composed on the call state's (pik_inner) *)
  YAkMemnorm.memnorm SEGS mem2 ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  pi_regs regs q v true -> pi_regs_body (L := Lb) (PA := PIb) regs Wc memc v -> getr regs 21 = w64 (-1) ->
  pik_inner ly S regs0 e q v true text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc N
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  pc < text + len -> nth_error tb (Z.to_nat (pc - text)) = Some 34 ->
  mrestrict (w_H Wc) memr = mrestrict (w_H Wc) memc -> ARx lyc Sc Hpc Wc memr mdc ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_string + (PI_FRAME + e))
    (spZ regs + (PI_FRAME + e)) [(q, q + 8)] lyc Sc Hpc Wc memr mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, spZ regs <= a < spZ regs + (PI_FRAME + e) -> ~ inFP [(q, q + 8)] a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memr a) ->
  aregs_preserved regs regs2 ->
  pik_ps_postX fxc lyc Sc Hpc Wc Lamc peakc cntc failc ranc most own q text len pc (Z.of_nat d + 1) tb
    ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIK_O_STRR) regs2 mem2 md2)
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)).


(* ---- AFTER THE NULL TEST (0x87c78), parse_string's block arm: the K3 pre, the store's effect (the slot holds
   parse_string's result, every other byte as at the return), at the second skip_ws (0x87c7c) ---- *)
Definition pik_k3n_spec (d : nat) (CTX0 CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v text len tb p
    Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc memr mdc k (regs : bvmap 5 word)
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc
    ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 (regs2 : bvmap 5 word) memx' mdx' kx' (regs' : bvmap 5 word) WS0 WS1,
  pi_fpok fx0 fxc ->
  pi_ent (L := Lb) (PA := PIb) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v
    true CTX0 CW ->
  (* the overlay's normality at the store's memory; the position and live requests: parse_string's post's (below)
     composed on the call state's (pik_inner) *)
  YAkMemnorm.memnorm SEGS memx' ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  pi_regs regs q v true -> pi_regs_body (L := Lb) (PA := PIb) regs Wc memc v -> getr regs 21 = w64 (-1) ->
  pik_inner ly S regs0 e q v true text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc N
    f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  pc < text + len -> nth_error tb (Z.to_nat (pc - text)) = Some 34 ->
  mrestrict (w_H Wc) memr = mrestrict (w_H Wc) memc -> ARx lyc Sc Hpc Wc memr mdc ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_string + (PI_FRAME + e))
    (spZ regs + (PI_FRAME + e)) [(q, q + 8)] lyc Sc Hpc Wc memr mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, spZ regs <= a < spZ regs + (PI_FRAME + e) -> ~ inFP [(q, q + 8)] a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memr a) ->
  aregs_preserved regs regs2 ->
  pik_ps_postX fxc lyc Sc Hpc Wc Lamc peakc cntc failc ranc most own q text len pc (Z.of_nat d + 1) tb
    ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 memx' mdx' kx' WS0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (keys + 8 * Z.of_nat n <= a < keys + 8 * Z.of_nat n + 8) ->
     mrestrict (w_H W2) memx' (Z_to_bv 64 a) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a)) ->
  val_mem SEGS (mrestrict (w_H W2) memx') (keys + 8 * Z.of_nat n) 8 (bv_unsigned (getr regs2 10)) ->
  aregs_preserved regs2 regs' ->
  bv_unsigned (getr regs2 10) <> 0 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIK_O_SKW2) regs' memx' mdx')
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)).


(* the rest of an object's member after its key string: jr_name's colon test (PjGrammar.v:239-252), then the value
   (pi_val_k); k is the key string's block size (jr_name frees it when no colon follows) *)
Definition pik_after_name (f D : nat) (n cap : nat) (accr : list (list Z * jv)) (nm : list Z) (k : nat) (y : list Z)
  : M (jv * list Z) :=
  match PjGrammar.skip y with
  | c :: r1 => if c =? 58 then pi_val_k f D true n cap accr nm r1 else jbind (jfree k) (fun _ => jrefuse)
  | [] => jbind (jfree k) (fun _ => jrefuse)
  end.

(* the free-list twin of pik_after_name (the kit's model PresetReqAt.jfl after the key string, pi_jfb's jr_name arms): at
   the colon the value's model pi_jfv_k with the key's own free lk; else jr_name refuses and the container's list is
   decided, the completed slots then the arrays *)
Definition pik_fl_after (f D : nat) (n cap : nat) (af lk : list Z) (y : list Z) (ok1 : list bool) : list Z :=
  match PjGrammar.skip y with
  | c :: r1 => if c =? 58 then pi_jfv_k f D true n cap af lk r1 ok1 else af ++ PresetReqAt.arrz true cap
  | [] => af ++ PresetReqAt.arrz true cap
  end.

(* the block's data after the key string: pi_cur at the cursor after the string, the container, the key read (its
   block (kx, kk) new since the entry), the run split at pik_after_name, the prefix's ledger and blocks moved by the
   string's allocation, the travelling position and live requests over that prefix, and the room of the rest *)
Definition pik_inner2 (ly : alayout) (S : astate) (regs0 : bvmap 5 word) (e q v : Z) (text len : Z) (tb : list Z)
  (p : Z) (d : nat) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z) (lyc : alayout) (Sc : astate) (Hpc : list Z)
  (Wc : world SEGS) (memc : word -> option byte) (N : nat)
  (f n cap : nat) (acc : list (list Z * jv)) (kids keys : Z) (Di : list (Z * Z)) (nm : list Z) (kx kk : Z) (pc : Z)
  (ok0 : list bool) (tr0 : list ev) (D0 Lamc : list (Z * Z)) (peakc cntc failc ranc : Z) : Prop :=
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own /\
  (length (rest_atR tb text pc) <= N)%nat /\ (n < cap)%nat /\
  pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) (prh_lin Lamc) true v kids keys n cap acc Di /\
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc /\
  pj_apartR (pi_sblk true kids keys cap) v /\
  pi_key (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) (prh_lin Lamc) true keys n nm [(kx, kk)] /\
  Permutation D0 (pi_sblk true kids keys cap ++ Di ++ [(kx, kk)]) /\
  In (kx, kk) Lamc /\ ~ In (kx, kk) Lam /\ 0 <= kk /\
  ~ (exists b m, In (b, m) (ablocks B ly S) /\ b <= kx - cf_head < b + m) /\
  (2 * length (rest_atR tb text pc) + 1 <= f)%nat /\
  (forall ok1 r t ok2, pik_after_name f (Nat.succ d) n cap (rev acc) nm (Z.to_nat kk) (rest_atR tb text pc) ok1 = (r, t, ok2) ->
     jr_items prh_jr_strtod d true (rest_atR tb text p) (ok0 ++ ok1) = (r, tr0 ++ t, ok2)) /\
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc /\
  rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d /\
  PItems_posb.pi_posb S Sc tr0 /\
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 /\
  blocks_bytes Sc <= blocks_bytes S + PRH_Charge.prh_held tr0 /\ length ok0 = PjGrammar.calls tr0 /\
  Ledger.lsum D0 = PjGrammar.held tr0 /\
  rd_room Sc (snd (fst (pik_after_name f (Nat.succ d) n cap (rev acc) nm (Z.to_nat kk) (rest_atR tb text pc) []))) /\
  (* THE BATCH KIT'S INVARIANTS after the key: the granted prefix (the string's granted malloc appended), the capacities, the
     completed slots' free order, and the free-list model past the kept key (pi_jfb_key: lk = PresetReqAt.lf of the
     key's trace, the key block's request) *)
  pi_grant ok0 tr0 /\ cap = PresetReqAt.ncap (Nat.succ n) /\
  pi_ncaps (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) kids acc /\
  exists af lk, pi_forder (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) (prh_lin Lamc) true kids keys n Di acc af /\
    (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) [(kx, kk)] = lk) /\
    (forall ok1, prhPi_frees d true (rest_atR tb text p) (ok0 ++ ok1) =
       pik_fl_after f (Nat.succ d) n cap af lk (rest_atR tb text pc) ok1).

(* ---- FROM THE SECOND skip_ws (0x87c7c) with the key in hand ---- *)
Definition pik_k4_spec (d : nat) (CTX0 CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v text len tb p
    Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc mdc k (regs : bvmap 5 word)
    f n cap acc kids keys Di nm kx kk pc ok0 tr0 D0 Lamc peakc cntc failc ranc WS0,
  pi_ajR (L := Lb) (PA := PIb) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc
    memc mdc k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  pi_fpok fx0 fxc ->
  pi_ent (L := Lb) (PA := PIb) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v
    true CTX0 CW ->
  (* the overlay's normality at the state this stretch starts from (its position and live requests: pik_inner2) *)
  YAkMemnorm.memnorm SEGS memc ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  pi_regs regs q v true -> pi_regs_body (L := Lb) (PA := PIb) regs Wc memc v -> getr regs 21 = w64 (-1) ->
  pik_inner2 ly S regs0 e q v text len tb p d Lam peak cnt fail ran most own lyc Sc Hpc Wc memc N
    f n cap acc kids keys Di nm kx kk pc ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIK_O_SKW2) regs memc mdc)
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)).


(* the return site of the second skip_ws call (0x87c84), a byte offset inside the block *)
Definition PIK_O_SKW2R : Z := PI_O_KEY + 196.
(* the in->p++ store (0x87cd0), a byte offset inside the block *)
Definition PIK_O_PP : Z := PI_O_KEY + 276.

(* ---- FROM THE SECOND skip_ws's RETURN (0x87c84): the colon test, in->p++, the two exits to PI_O_FREE and the fall
   to PI_O_VAL ---- *)
Definition pik_k5_spec (d : nat) (CTX0 CW : list (list Z)) (N : nat) : Prop :=
  forall (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v text len tb p
    Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc memr mdc k (regs : bvmap 5 word)
    f n cap acc kids keys Di nm kx kk pc ok0 tr0 D0 Lamc peakc cntc failc ranc
    ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 (regs2 : bvmap 5 word) WS0,
  pi_fpok fx0 fxc ->
  pi_ent (L := Lb) (PA := PIb) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v
    true CTX0 CW ->
  (* the overlay's normality at the return state, and skip_ws's post S' = S (tskip_ws_specX): the travelling position
     and live requests of the call state (pik_inner2) are the return state's *)
  YAkMemnorm.memnorm SEGS mem2 -> S2 = Sc ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  pi_regs regs q v true -> pi_regs_body (L := Lb) (PA := PIb) regs Wc memc v -> getr regs 21 = w64 (-1) ->
  pik_inner2 ly S regs0 e q v text len tb p d Lam peak cnt fail ran most own lyc Sc Hpc Wc memc N
    f n cap acc kids keys Di nm kx kk pc ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  mrestrict (w_H Wc) memr = mrestrict (w_H Wc) memc -> ARx lyc Sc Hpc Wc memr mdc ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_skip_ws + (PI_FRAME + e))
    (spZ regs + (PI_FRAME + e)) [(q, q + 8)] lyc Sc Hpc Wc memr mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs <= a < spZ regs + (PI_FRAME + e) -> ~ inFP [(q, q + 8)] a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memr a) ->
  aregs_preserved regs regs2 ->
  (room_live_cf Sc -> room_live_cf S2) -> Hp2 = Hpc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 mem2 Lamc peakc cntc failc ranc most own ->
  pj_in_okR SEGS (mrestrict (w_H W2) mem2) q text len
    (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text pc)))) (Z.of_nat d + 1) tb ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIK_O_SKW2R) regs2 mem2 md2)
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)).

(* ---- THE MISSING-COLON HAND-OFF TO PI_O_FREE (PItems_pres.v's pi_free_pre): in form (b) it owes, besides the travelling
   pi_posb / pi_live over the prefix trace tr0, only the class-24 live count at the hand-off state (the entry-keyed
   form's run-event conjunct is gone: the kit's f97c tfuzz_free_specX keys its post position on its own HFr event). The
   count is DERIVED here, not a premise: ccnt24 Sc is cnt (in_cls kBatchClass) (rs_live Sc) by conversion, pi_live
   moves the live list to the entry's after rd_hevs tr0 (cnt_perm), rd_hevs tr0 is a prefix of the whole call's
   all-granted events (pvm_gt_pref at the block's run split K), the count after a prefix is at most the peak
   (pkR_prefix), and that peak is bounded by pi_ent's class-24 premise. ---- *)
Lemma pik_cc24 : forall d x0 ok0 tr0 (K : M (jv * list Z)) S Sc,
  (forall ok1 r t ok2, K ok1 = (r, t, ok2) -> jr_items prh_jr_strtod d true x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2)) ->
  length ok0 = PjGrammar.calls tr0 ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (PRH_Charge.prhPi_gtrace d true x0))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros d x0 ok0 tr0 K S Sc HK Hlen Hl Hb.
destruct (pvm_gt_pref d true x0 ok0 tr0 K HK Hlen) as (E & EG).
change (YGcfRoomLive.ccnt24 Sc) with
  (Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)))).
unfold PItems_posb.pi_live in Hl. rewrite (PresetReqAt.cnt_perm _ _ _ Hl).
pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass)
  (PresetReqAt.rd_hevs (PRH_Charge.prhPi_gtrace d true x0))
  (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (length (PresetReqAt.rd_hevs tr0))) as Hp.
rewrite EG in Hp, Hb. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all in Hp.
apply Nat2Z.inj_le in Hp. clear - Hp Hb. lia.
Qed.


(* image B's parse_string keeps the cursor in s0 (k = 0, PRH_Base.v prh_s0's note).
   OWNER: lane PItemsB (the preamble); discharged at PIi := prh_img_B by reflexivity. *)
Hypothesis PIK_S0STR : pi_s0cur F_parse_string = Some 0.

Lemma pik_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y l IH]; intros H; [destruct H|]. cbn [zmaxl fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH H). fold (zmaxl l). lia.
Qed.

Lemma pik_zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. intros l. induction l as [|y l IH]; cbn [zmaxl fold_right]; [lia|]. fold (zmaxl l). lia. Qed.

(* the stack budget of the skip_ws call: its frame and parse_items' own fit in parse_items' bound *)
Lemma pik_stk_skw : forall d, STK_skip_ws + PI_FRAME <= STK_parse_items d.
Proof.
intros d. unfold STK_parse_items, LEAF_pv_pi. rewrite PIK_FR.
pose proof (pik_zmaxl_in STK_skip_ws [STK_RT_ECALL; STK_RT_STRTOD; STK_fuzz_malloc; STK_fuzz_free; STK_literal;
  STK_parse_string; STK_grow; STK_skip_ws] ltac:(cbn; tauto)) as H1.
pose proof (PIK_FR0 F_parse_value) as H2. pose proof (PIK_FR0 F_parse_items) as H3.
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)) as H4.
assert (H5 : 0 <= Z.of_nat (PjGrammar.MAXD - d) * (PRH_Base.pi_frame F_parse_value + PRH_Base.pi_frame F_parse_items)) by nia.
lia.
Qed.
(* the same for the parse_string call *)
Lemma pik_stk_str : forall d, STK_parse_string + PI_FRAME <= STK_parse_items d.
Proof.
intros d. unfold STK_parse_items, LEAF_pv_pi. rewrite PIK_FR.
pose proof (pik_zmaxl_in STK_parse_string [STK_RT_ECALL; STK_RT_STRTOD; STK_fuzz_malloc; STK_fuzz_free; STK_literal;
  STK_parse_string; STK_grow; STK_skip_ws] ltac:(cbn; tauto)) as H1.
pose proof (PIK_FR0 F_parse_value) as H2. pose proof (PIK_FR0 F_parse_items) as H3.
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)) as H4.
assert (H5 : 0 <= Z.of_nat (PjGrammar.MAXD - d) * (PRH_Base.pi_frame F_parse_value + PRH_Base.pi_frame F_parse_items)) by nia.
lia.
Qed.

(* a word read through two readers that agree on its eight bytes *)
Lemma pik_rdword_ext : forall (rd1 rd2 : reader) a, (forall k, 0 <= k < 8 -> rd1 (a + k) = rd2 (a + k)) ->
  rdword rd1 a = rdword rd2 a.
Proof.
intros rd1 rd2 a H. unfold rdword.
assert (E0 : rd1 a = rd2 a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* the trace of a bind starts with the trace of its first computation *)
Lemma pik_jbind_prefix : forall (A Bt : Type) (m : M A) (kk : A -> M Bt) ok,
  exists t, snd (fst (jbind m kk ok)) = snd (fst (m ok)) ++ t.
Proof.
intros A Bt m kk ok. unfold jbind. destruct (m ok) as [[[a|] t1] ok1]; cbn [fst snd].
- destruct (kk a ok1) as [[r t2] ok2]. exists t2. reflexivity.
- exists []. rewrite app_nil_r. reflexivity.
Qed.

(* the granted run of a member whose rest opens a scanned string starts with the string's allocation *)
Lemma pik_gt_alloc : forall f D n cap acc z Q, PjGrammar.scan z = Some Q ->
  exists t, snd (fst (pi_jrb f D true n cap acc (34 :: z) [])) = EAlloc (S Q) :: t.
Proof.
intros f D n cap acc z Q Hs. unfold pi_jrb.
lazymatch goal with |- exists t, snd (fst (jbind ?m ?k [])) = _ =>
  destruct (pik_jbind_prefix _ _ m k []) as (t1 & E1) end.
rewrite E1. unfold jr_name.
replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity. rewrite Z.eqb_refl.
lazymatch goal with |- exists t, snd (fst (jbind ?m ?k [])) ++ _ = _ =>
  destruct (pik_jbind_prefix _ _ m k []) as (t2 & E2) end.
rewrite E2. unfold jr_string. rewrite Hs.
lazymatch goal with |- exists t, (snd (fst (jbind ?m ?k [])) ++ _) ++ _ = _ =>
  destruct (pik_jbind_prefix _ _ m k []) as (t3 & E3) end.
rewrite E3. exists (t3 ++ t2 ++ t1). rewrite <- !app_assoc. reflexivity.
Qed.

(* the granted run of a member whose rest opens with the quote starts with the string's granted run *)
Lemma pik_gt_str : forall f D n cap acc z,
  exists t, snd (fst (pi_jrb f D true n cap acc (34 :: z) [])) = snd (fst (jr_string z [])) ++ t.
Proof.
intros f D n cap acc z. unfold pi_jrb.
lazymatch goal with |- exists t, snd (fst (jbind ?m ?k [])) = _ =>
  destruct (pik_jbind_prefix _ _ m k []) as (t1 & E1) end.
rewrite E1. unfold jr_name.
replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity. rewrite Z.eqb_refl.
lazymatch goal with |- exists t, snd (fst (jbind ?m ?k [])) ++ _ = _ =>
  destruct (pik_jbind_prefix _ _ m k []) as (t2 & E2) end.
rewrite E2. exists (t2 ++ t1). rewrite <- app_assoc. reflexivity.
Qed.

(* parse_string's arm lists ARE the model's: prhPs_evs z ok (over cf_head) is rd_hevs of jr_string's trace under ok
   (over PresetReqAt.HEAD), at the instance's head (PRH_FnReader.v prhPs_evs_model) *)
Lemma pik_ps_evs_of : forall z ok r t ok', jr_string z ok = (r, t, ok') -> PresetReqAt.rd_hevs t = prhPs_evs z ok.
Proof. intros z ok r t ok' H. rewrite (prhPs_evs_model z ok PIK_HEAD), H. reflexivity. Qed.

Lemma pik_rdword_of_val : forall (H : word -> bool) (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bb : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bb 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bb 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bb 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bb 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bb 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bb 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bb 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bb 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* a word of the cursor's chain at the call view is the entry view's word, or the ra / s0 the prologue saved (the
   form prh_cur_entry states, PRH_Base.v prh_word_entry) *)
Lemma pik_word_call : forall (regs0 regs : bvmap 5 word) (W : world SEGS) mem (Wc : world SEGS) memc e q v a w,
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  spZ regs0 - 16 <= a -> a + 8 <= q -> a mod 8 = 0 -> spZ regs0 mod 8 = 0 ->
  q + 24 <= spZ regs0 + e -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  rdword (aview SEGS (w_H Wc) memc) a = Some w -> prh_word_entry W mem regs0 a w.
Proof.
intros regs0 regs W mem Wc memc e q v a w HFR Ha1 Ha2 Ha8 Hs8 Hqe Hvw Hr.
pose proof HFR as (Fsp & _ & _ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fw & _).
unfold PI_FRAME in Fsp.
unfold prh_word_entry.
destruct (Z.eqb_spec a (spZ regs0 - 8)) as [Ea | Ea].
- replace a with (spZ regs + 136) in Hr by lia.
  pose proof (bv_unsigned_in_range 64 (getr regs0 1)) as RR. unfold bv_modulus in RR. change (Z.of_N 64) with 64 in RR.
  rewrite (pik_rdword_of_val _ _ _ _ V1 RR) in Hr. injection Hr as <-. reflexivity.
- destruct (Z.eqb_spec a (spZ regs0 - 16)) as [Eb | Eb].
  + replace a with (spZ regs + 128) in Hr by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs0 8)) as RR. unfold bv_modulus in RR. change (Z.of_N 64) with 64 in RR.
    rewrite (pik_rdword_of_val _ _ _ _ V2 RR) in Hr. injection Hr as <-. reflexivity.
  + rewrite <- Hr. apply pik_rdword_ext. intros kk Hk. symmetry. apply Fw; [lia|].
    intros (r & Hin & Hra). cbn [rd_fp In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia.
Qed.

(* the same words are present at the call view (the saved ra / s0, or a window word, present at the entry by fwin) *)
Lemma pik_word_call_some : forall ly (regs0 regs : bvmap 5 word) (W : world SEGS) mem (Wc : world SEGS) memc e q v a,
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v -> fwin ly W regs0 mem e ->
  spZ regs0 - 16 <= a -> a + 8 <= q -> a mod 8 = 0 -> spZ regs0 mod 8 = 0 ->
  q + 24 <= spZ regs0 + e -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  exists w, rdword (aview SEGS (w_H Wc) memc) a = Some w.
Proof.
intros ly regs0 regs W mem Wc memc e q v a HFR HFW Ha1 Ha2 Ha8 Hs8 Hqe Hvw.
pose proof HFR as (Fsp & _ & _ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fw & _).
pose proof HFW as (_ & _ & _ & HP).
unfold PI_FRAME in Fsp.
destruct (Z.eqb_spec a (spZ regs0 - 8)) as [Ea | Ea].
- replace a with (spZ regs + 136) by lia.
  pose proof (bv_unsigned_in_range 64 (getr regs0 1)) as RR. unfold bv_modulus in RR. change (Z.of_N 64) with 64 in RR.
  eexists. exact (pik_rdword_of_val _ _ _ _ V1 RR).
- destruct (Z.eqb_spec a (spZ regs0 - 16)) as [Eb | Eb].
  + replace a with (spZ regs + 128) by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs0 8)) as RR. unfold bv_modulus in RR. change (Z.of_N 64) with 64 in RR.
    eexists. exact (pik_rdword_of_val _ _ _ _ V2 RR).
  + assert (PB : forall kk, 0 <= kk < 8 -> exists b, aview SEGS (w_H Wc) memc (a + kk) = Some b).
    { intros kk Hk. rewrite Fw; [| lia |].
      - destruct (HP (a + kk) ltac:(lia)) as [Hh [b Hb]]. exists (bv_unsigned b).
        unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
      - intros (r & Hin & Hra). cbn [rd_fp In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; lia. }
    destruct (PB 0 ltac:(lia)) as (b0 & B0). rewrite Z.add_0_r in B0.
    destruct (PB 1 ltac:(lia)) as (b1 & B1). destruct (PB 2 ltac:(lia)) as (b2 & B2).
    destruct (PB 3 ltac:(lia)) as (b3 & B3). destruct (PB 4 ltac:(lia)) as (b4 & B4).
    destruct (PB 5 ltac:(lia)) as (b5 & B5). destruct (PB 6 ltac:(lia)) as (b6 & B6).
    destruct (PB 7 ltac:(lia)) as (b7 & B7).
    unfold rdword. rewrite B0, B1, B2, B3, B4, B5, B6, B7. eexists. reflexivity.
Qed.

Lemma pik_aview_range : forall (H : word -> bool) (m : word -> option byte) a b,
  aview SEGS H m a = Some b -> 0 <= b < 256.
Proof.
intros H m a b E. unfold aview in E. destruct (mbyte SEGS (mrestrict H m) a) as [x|]; cbn [option_map] in E;
  [|discriminate E]. injection E as <-. pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R.
change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma pik_rdword_range : forall (H : word -> bool) (m : word -> option byte) a w,
  rdword (aview SEGS H m) a = Some w -> 0 <= w < 2 ^ 64.
Proof.
intros H m a w Hw. unfold rdword in Hw.
destruct (aview SEGS H m a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H m (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H m (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H m (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H m (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H m (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H m (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H m (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
pose proof (pik_aview_range _ _ _ _ E0). pose proof (pik_aview_range _ _ _ _ E1). pose proof (pik_aview_range _ _ _ _ E2).
pose proof (pik_aview_range _ _ _ _ E3). pose proof (pik_aview_range _ _ _ _ E4). pose proof (pik_aview_range _ _ _ _ E5).
pose proof (pik_aview_range _ _ _ _ E6). pose proof (pik_aview_range _ _ _ _ E7).
lia.
Qed.

(* the reader of a world sees memory only through the world's restriction *)
Lemma pik_aview_eq : forall (Wx : world SEGS) (m m' : word -> option byte),
  mrestrict (w_H Wx) m' = mrestrict (w_H Wx) m -> aview SEGS (w_H Wx) m' = aview SEGS (w_H Wx) m.
Proof. intros Wx m m' E. apply functional_extensionality. intros a. unfold aview, mbyte. rewrite E. reflexivity. Qed.

(* pi_cur is a reader predicate: it survives a memory with the same restricted reader (PItems_head.v's hd_cur_rdeq) *)
Lemma pik_cur_rdeq : forall (regs0 : bvmap 5 word) e q v text len tb dd lyc Sc Hpc (Wc : world SEGS) memc memc' pc
  Lamc peakc cntc failc ranc most own,
  mrestrict (w_H Wc) memc' = mrestrict (w_H Wc) memc ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd lyc Sc Hpc Wc memc' pc Lamc peakc cntc failc ranc most own.
Proof.
intros regs0 e q v text len tb dd lyc Sc Hpc Wc memc memc' pc Lamc peakc cntc failc ranc most own Heq H.
unfold pi_cur, src_rd, bytes_at, prh_ledger, prh_glob, prh_most, prh_own, prh_hblock, aview in H |- *.
rewrite Heq. exact H.
Qed.

(* the program's statics are not read-only. At PIi := prh_img_B it is
   S1ImgB.v pst_not_ro_B. *)
Hypothesis HPSTRO : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.

(* the allocator's statics are image bytes. At PIi := prh_img_B it is
   pv_pst_in_img (PItems_value.v, by computation). *)
Hypothesis PIK_PSTIMG : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.

(* the harness head is at least one shadow granule wide (the kit's spelling PRH_Base.v prh_head_wide; PItemsValue's HW).
   OWNER: preset_head_wide (lib/A/CfParamsPreset.v) at the instance. *)
Hypothesis HW : prh_head_wide.

(* fpre's read-only view rides through a journal (at the walk's relation) whose footprint does not open the sink (its
   image clause) *)
Lemma pik_rod_kept : forall STK sp0 FP ly S Hp (W : world SEGS) mem md own lyc Sc Hpc (W' : world SEGS) mem' md' k,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc
    W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
- intros Hp'. exact (HPSTRO a Hp' Hro).
Qed.

(* ================================================================================================== *)
(* THE STATE AFTER THE FIRST skip_ws (0x87bc8): the image's shadow expression pi_shx (PItems_agr.v, (x >> 3) + s10)
   for every cached shadow register, s0 / s4 the cursor's depth / end words (q + 16, q + 8), s2 = 1 (an object); the
   cursor's p field (atom 32) and end word (atom 33) read-only, and, when the cursor is on a byte, that byte (atom 34)
   as its own read-only region. PItems_head.v's hd_sregs / hd_smem / hd_facts with s4 and s7 added (this block reads
   them at 0x87bd0 / 0x87bd8). *)
Definition pik1_sregs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 9 16)) 20%bv (SOff 9 8))
    23%bv (pi_shx (SOff 9 8))) 25%bv (pi_shx (SOff 9 16))) 27%bv (pi_shx (SOff 9 0))) 18%bv (SLit 1).
Definition pik1_smem (bt : bool) : smem :=
  (if bt then [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]] else []) ++
  [ YP09.mkRegion (Some 9%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))] ].
Definition pik1_facts : list (nat * afact) :=
 [ (9%nat, mkAF 4096 (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0); (34%nat, mkAF 0 255 0) ].
Definition pik1_ss (bt : bool) (pc : Z) : sstate := mkSS pc pik1_sregs (pik1_smem bt) None (mkFacts pik1_facts [] []).
Definition pik1_SH (bt : bool) : list shent := (if bt then [mkSHE 32 0 1] else []) ++ [mkSHE 9 0 24].
Definition pik_Bx1 : sv := SOff 26 0.

Lemma pik1_st_ok : forall (fy : YK11.FPState) (Wx : world SEGS) memc (regs : bvmap 5 word) q p1 ed c (bt : bool) off,
  getr regs 9 = w64 q -> getr regs 8 = w64 (q + 16) -> getr regs 20 = w64 (q + 8) -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 27 = w64 (pi_sh q) -> getr regs 25 = w64 (pi_sh (q + 16)) -> getr regs 23 = w64 (pi_sh (q + 8)) ->
  getr regs 18 = w64 1 ->
  4096 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= p1 <= 2 ^ 47 - 2 -> 4096 <= ed <= 2 ^ 47 - 1 ->
  0 <= c < 256 -> (bt = true -> q + 16 <= p1 \/ p1 + 1 <= q) ->
  val_mem SEGS (mrestrict (w_H Wx) memc) q 8 p1 -> val_mem SEGS (mrestrict (w_H Wx) memc) (q + 8) 8 ed ->
  (bt = true -> val_mem SEGS (mrestrict (w_H Wx) memc) p1 1 c) ->
  st_ok_pi (fx := fy) SEGS VALb (Eimg (PI := PIb) (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c]))
    (pik1_ss bt off)
    (restrict (w_H Wx) (@YK11.mkst fy regs (Z_to_bv 64 (VALb A_TEXT + off)) memc (seg_rom SEGS))).
Proof.
intros fy Wx memc regs q p1 ed c bt off H9 H8 H20 H26 H27 H25 H23 H18 Hq Hq8 Hp1 Hed Hc Hdj Vp Ve Vc.
set (E := Eimg (PI := PIb) (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c])).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 p1) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ed) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = ed) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x)).
{ intros x Hx. rewrite denot_lit_U, U_SOff, U9, zcanon_id by (unfold M64; lia). reflexivity. }
rewrite (restrict_mkst_fx (fx := fy)). unfold pik1_ss. apply (pa_entry_st_ok_full (fx := fy) (L := Lb) (PI := PIb)).
- unfold pik1_sregs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
    [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg| |]| |]| |]| |]| |]| |];
  try (intros X; discriminate X).
  + rewrite H8, D9 by lia. reflexivity.
  + rewrite H20, D9 by lia. reflexivity.
  + rewrite H23, (pi_denot_shx E (SOff 9 8) SHADOW_OFF (q + 8) (D9 8 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H25, (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H27, (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26)
      by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H18. reflexivity.
- destruct bt; vm_compute; reflexivity.
- unfold pik1_smem. destruct bt; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ p1 0 1 (SOff 34 0) c);
    [rewrite denot_lit_U, U_SOff, U34, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
    | rewrite Z.add_0_r; exact (Vc eq_refl)].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
      | rewrite Z.add_0_r; exact Vp].
    * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) ed);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Ve].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
      | rewrite Z.add_0_r; exact Vp].
    * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) ed);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Ve].
- apply pairwise_disjoint_of_extents. unfold pik1_smem. destruct bt;
  [pose proof (Hdj eq_refl) as Hdj'|]; cbn [app map]; unfold extent_of_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U32;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok pik1_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U26, U32, U33, U34. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* the state at the second skip_ws's return (0x87c84): pik1's, with the cursor's p word writable (in->p++ at 0x87cd4) *)
Definition pik5_smem (bt : bool) : smem :=
  (if bt then [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]] else []) ++
  [ YP09.mkRegion (Some 9%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))] ].
Definition pik5_ss (bt : bool) (pc : Z) : sstate := mkSS pc pik1_sregs (pik5_smem bt) None (mkFacts pik1_facts [] []).

Lemma pik5_st_ok : forall (fy : YK11.FPState) (Wx : world SEGS) memc (regs : bvmap 5 word) q p1 ed c (bt : bool) off,
  getr regs 9 = w64 q -> getr regs 8 = w64 (q + 16) -> getr regs 20 = w64 (q + 8) -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 27 = w64 (pi_sh q) -> getr regs 25 = w64 (pi_sh (q + 16)) -> getr regs 23 = w64 (pi_sh (q + 8)) ->
  getr regs 18 = w64 1 ->
  4096 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= p1 <= 2 ^ 47 - 2 -> 4096 <= ed <= 2 ^ 47 - 1 ->
  0 <= c < 256 -> (bt = true -> q + 16 <= p1 \/ p1 + 1 <= q) ->
  val_mem SEGS (mrestrict (w_H Wx) memc) q 8 p1 -> val_mem SEGS (mrestrict (w_H Wx) memc) (q + 8) 8 ed ->
  (bt = true -> val_mem SEGS (mrestrict (w_H Wx) memc) p1 1 c) ->
  (forall a, q <= a < q + 8 -> writable_at SEGS (mrestrict (w_H Wx) memc) a) ->
  st_ok_pi (fx := fy) SEGS VALb (Eimg (PI := PIb) (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c]))
    (pik5_ss bt off)
    (restrict (w_H Wx) (@YK11.mkst fy regs (Z_to_bv 64 (VALb A_TEXT + off)) memc (seg_rom SEGS))).
Proof.
intros fy Wx memc regs q p1 ed c bt off H9 H8 H20 H26 H27 H25 H23 H18 Hq Hq8 Hp1 Hed Hc Hdj Vp Ve Vc Hwq.
set (E := Eimg (PI := PIb) (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c])).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 p1) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ed) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = ed) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x)).
{ intros x Hx. rewrite denot_lit_U, U_SOff, U9, zcanon_id by (unfold M64; lia). reflexivity. }
rewrite (restrict_mkst_fx (fx := fy)). unfold pik5_ss. apply (pa_entry_st_ok_full (fx := fy) (L := Lb) (PI := PIb)).
- unfold pik1_sregs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
    [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg| |]| |]| |]| |]| |]| |];
  try (intros X; discriminate X).
  + rewrite H8, D9 by lia. reflexivity.
  + rewrite H20, D9 by lia. reflexivity.
  + rewrite H23, (pi_denot_shx E (SOff 9 8) SHADOW_OFF (q + 8) (D9 8 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H25, (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H27, (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26)
      by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H18. reflexivity.
- destruct bt; vm_compute; reflexivity.
- unfold pik5_smem. destruct bt; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U32. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ p1 0 1 (SOff 34 0) c);
    [rewrite denot_lit_U, U_SOff, U34, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
    | rewrite Z.add_0_r; exact (Vc eq_refl)].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; apply Hwq; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
      | rewrite Z.add_0_r; exact Vp].
    * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) ed);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Ve].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Ho; apply Hwq; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
      | rewrite Z.add_0_r; exact Vp].
    * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) ed);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Ve].
- apply pairwise_disjoint_of_extents. unfold pik5_smem. destruct bt;
  [pose proof (Hdj eq_refl) as Hdj'|]; cbn [app map]; unfold extent_of_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U32;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok pik1_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U26, U32, U33, U34. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* ================================================================================================== *)
(* THE STATE AFTER parse_string (0x87c10), PItems_body_free.v's pif_ss form: the frame's three words at sp (the 2 ^ 60
   guard and the keys field's address and shadow), the keys field (atom 32 = keys), n through s6 (atom 33 = n),
   s8 = shadow (v + 40), and the key slot keys + 8 n (atom 34) as a WRITABLE region with no content (the block
   writes it at 0x87c74), its two address forms aliased to atom 34. *)
Definition pik_slot : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SLL (SOff 33 0) (SLit 3)).
Definition pik_slot2 : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 3)) (SOff 32 0).
Definition pik3_regs : list sv := sr_set sr_atoms 24%bv (pi_shx (SOff 19 40)).
Definition pik3_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 24 0 0
    [YP09.mkChunk 0 (CVal 8 (SLit (2 ^ 60))); YP09.mkChunk 8 (CVal 8 (pi_shx (SOff 19 32)));
     YP09.mkChunk 16 (CVal 8 (SOff 19 32))];
  YP09.mkRegion (Some 19%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
  YP09.mkRegion (Some 34%nat) 0 8 0 8 [] ].
Definition pik3_atoms : list (nat * afact) :=
[ (19%nat, mkAF 0 (2 ^ 47 - 56) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (32%nat, mkAF 4096 (2 ^ 47 - 8) 3); (34%nat, mkAF 4096 (2 ^ 47 - 8) 3) ].
Definition pik3_facts : facts := mkFacts pik3_atoms [] [(pik_slot, SOff 34 0); (pik_slot2, SOff 34 0)].
Definition pik3_ss (pc : Z) : sstate := mkSS pc pik3_regs pik3_regions None pik3_facts.
Definition pik3_SH : list shent := [mkSHE 19 0 56; mkSHE 34 0 8].
Definition pik3_extra (keys n : Z) : list word := map (Z_to_bv 64) [keys; n; keys + 8 * n].

Lemma pik3_st_ok : forall (fy : YK11.FPState) (Wx : world SEGS) memc (regs : bvmap 5 word) v keys n pc,
  getr regs 19 = w64 v -> getr regs 22 = w64 (v + 40) -> getr regs 24 = w64 (pi_sh (v + 40)) ->
  getr regs 26 = w64 SHADOW_OFF ->
  0 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 ->
  4096 <= keys -> keys mod 8 = 0 -> 0 <= n -> keys + 8 * n + 8 <= 2 ^ 47 ->
  2 ^ 46 <= spZ regs -> spZ regs + 24 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H Wx) memc) (spZ regs) 8 (2 ^ 60) ->
  val_mem SEGS (mrestrict (w_H Wx) memc) (spZ regs + 8) 8 (pi_sh (v + 32)) ->
  val_mem SEGS (mrestrict (w_H Wx) memc) (spZ regs + 16) 8 (v + 32) ->
  rd_u64 SEGS (mrestrict (w_H Wx) memc) (v + 32) keys ->
  rd_u64 SEGS (mrestrict (w_H Wx) memc) (v + 40) n ->
  (forall a, keys + 8 * n <= a < keys + 8 * n + 8 -> writable_at SEGS (mrestrict (w_H Wx) memc) a) ->
  (spZ regs + 24 <= v + 32 \/ v + 48 <= spZ regs) ->
  (keys + 8 * n + 8 <= v + 32 \/ v + 48 <= keys + 8 * n) ->
  keys + 8 * n + 8 <= spZ regs ->
  st_ok_pi (fx := fy) SEGS VALb (Eimg (PI := PIb) (Ereg regs (pik3_extra keys n))) (pik3_ss pc)
    (restrict (w_H Wx) (@YK11.mkst fy regs (Z_to_bv 64 (VALb A_TEXT + pc)) memc (seg_rom SEGS))).
Proof.
intros fy Wx memc regs v keys n pc H19 H22 H24 H26 Hv Hv8 Hk4 Hk8 Hn Hkn Hsp1 Hsp2
  V0 V8 V16 [Hkr Vk] [Hnr Vn] Hwr D1 D2 D3.
set (E := Eimg (PI := PIb) (Ereg regs (pik3_extra keys n))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (pik3_extra keys n)) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 (v + 40)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 keys) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (keys + 8 * n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U19 : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = v + 40) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = keys) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = keys + 8 * n) by (rewrite E34; apply unsigned_lit_small; lia).
assert (D19 : forall c, 0 <= v + c < 2 ^ 64 -> sv_denot E (SOff 19 c) = Z_to_bv 64 (v + c)).
{ intros c Hc. rewrite denot_lit_U, U_SOff, U19, zcanon_id by (unfold M64; lia). reflexivity. }
assert (DS : sv_denot E pik_slot = sv_denot E (SOff 34 0) /\ sv_denot E pik_slot2 = sv_denot E (SOff 34 0)).
{ assert (UK : U E (SOff 34 0) = keys + 8 * n) by (rewrite U_SOff, U34, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity).
  assert (US : U E (SAlu ALU_SLL (SOff 33 0) (SLit 3)) = 8 * n).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U33, Z.add_0_r.
    change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (zcanon_id n) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (UK32 : U E (SOff 32 0) = keys) by (rewrite U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity).
  split; apply U_inj; unfold pik_slot, pik_slot2; rewrite U_SAlu; cbn [zalu_raw]; rewrite ?UK32, ?US, UK;
  rewrite zcanon_id by (unfold M64; lia); lia. }
rewrite (restrict_mkst_fx (fx := fy)). unfold pik3_ss.
apply (pa_entry_st_ok_full (fx := fy) (L := Lb) (PI := PIb)).
- unfold pik3_regs. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H24, (pi_denot_shx E (SOff 19 40) SHADOW_OFF (v + 40) (D19 40 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
  reflexivity.
- vm_compute. reflexivity.
- unfold pik3_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 (SLit (2 ^ 60)) (2 ^ 60)); [reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact V0].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 (pi_shx (SOff 19 32)) (pi_sh (v + 32)));
        [ rewrite (pi_denot_shx E (SOff 19 32) SHADOW_OFF (v + 32) (D19 32 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia); reflexivity
        | unfold pi_sh, SHADOW_OFF; cbn; Z.div_mod_to_equations; lia | zside | exact V8].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 16 8 (SOff 19 32) (v + 32)); [apply D19; lia | cbn; lia | zside | exact V16].
  + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ v 32 8 (SOff 32 0) keys);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Vk].
  + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (v + 40) 0 8 (SOff 33 0) n);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vn].
  + rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|]. constructor.
- apply pairwise_disjoint_of_extents. unfold pik3_regions. cbn [map]. unfold extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U19, U22, U34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok pik3_facts pik3_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U26, U32, U34. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia.
  + cbn [f_alias pik3_facts alias_ok]. destruct DS as [DS1 DS2]. split; [exact DS1|]. split; [exact DS2 | exact I].
Qed.

(* ---- THE CURSOR INVARIANT ACROSS A CALL: the statement of PItems_kept.v (sha256 92a19b545b6e; internal record), its exact
   name, as a Section hypothesis until its proof lands. ---- *)
(* the three shadow laws of the kept proofs (PItems_kept.v (sha256 c87d37fff15c; internal record)), their exact texts.
   OWNERS: HSH (YGcfHeadSh.v ARx_hshadow_law_cf_ok at ARcf); HZS (the zero-shadow ranges at ARcf);
   HIMG (the image strings' shadow at ARcf) *)
Hypothesis HSH : pi_hshadow_law (L := Lb) (PA := PIb) B ARx cf_head.
Hypothesis HZS : pi_zs_law (L := Lb) (PA := PIb) B ARx.
Hypothesis HIMG : pi_img_law (L := Lb) (PA := PIb) B ARx.
(* the three call-keep statements over a world relation R (the callee journal an R call rule gives); the walk applies
   them at wle' SEGS RZ_cf *)
Lemma HKC : pi_cur_kept_callR_stmt (L := Lb) (PA := PIb) (SKq := SK) B ARx.
Proof. exact (pi_cur_kept_callR (L := Lb) (PA := PIb) (SKq := SK) B ARx LAWS HSH HZS HIMG HPSTRO). Qed.
Lemma HKM : pi_curmem_kept_callR_stmt (L := Lb) (PA := PIb) (SKq := SK) B ARx.
Proof. exact (pi_curmem_kept_callR (L := Lb) (PA := PIb) (SKq := SK) B ARx LAWS HSH HZS HIMG HPSTRO). Qed.
(* the proof of pi_node_kept_callR_stmt (PItems_kept.v) *)
Lemma HKN : pi_node_kept_callR_stmt (L := Lb) (PA := PIb) (SKq := SK) B ARx.
Proof. exact (pi_node_kept_callR (L := Lb) (PA := PIb) (SKq := SK) B ARx). Qed.

(* where the node lives survives a call that keeps the allocator's blocks and the fake frames (the layout's frame
   base is a layout_le invariant) *)
Lemma pik_at_kept : forall (nl : nat) ly1 S1 ly2 S2 Lam (regs0 : bvmap 5 word) e v n,
  layout_le nl ly1 ly2 -> ablocks B ly2 S2 = ablocks B ly1 S1 -> frames S2 = frames S1 ->
  prhReader_at B ly1 S1 Lam regs0 e v n -> prhReader_at B ly2 S2 Lam regs0 e v n.
Proof.
intros nl ly1 S1 ly2 S2 Lam regs0 e v n HL Hab Hfr H. unfold prhReader_at in *. rewrite Hab, Hfr.
assert (EF : forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos).
{ intros cid pos. unfold frame_addr. destruct HL as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct H as [H | [H | [(cid & pos & Hin & H1 & H2) | H]]]; [left | right; left | right; right; left | right; right; right];
  try exact H.
exists cid, pos. rewrite !EF. auto.
Qed.

(* ---- the grammar's white-space skip on the text: skip drops a prefix, so after it the rest is the text's rest at
   the cursor skip_ws leaves ---- *)
Lemma pik_skip_skipn : forall y, PjGrammar.skip y = skipn (length y - length (PjGrammar.skip y)) y.
Proof.
induction y as [|b r IH]; [reflexivity|]. cbn [PjGrammar.skip].
destruct (PjGrammar.ws b).
- pose proof (PjGrammar.skip_len r). cbn [length].
  replace (S (length r) - length (PjGrammar.skip r))%nat with (S (length r - length (PjGrammar.skip r))) by lia.
  cbn [skipn]. exact IH.
- cbn [length]. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma pik_skip_rest : forall (tb : list Z) text pc,
  text <= pc <= text + Z.of_nat (length tb) ->
  PjGrammar.skip (rest_atR tb text pc) =
  rest_atR tb text (text + Z.of_nat (length tb) - Z.of_nat (length (PjGrammar.skip (rest_atR tb text pc)))).
Proof.
intros tb text pc Hpc.
pose proof (PjGrammar.skip_len (rest_atR tb text pc)) as Hs.
assert (Hl : length (rest_atR tb text pc) = (length tb - Z.to_nat (pc - text))%nat)
  by (unfold rest_atR; rewrite length_skipn; reflexivity).
transitivity (skipn (length (rest_atR tb text pc) - length (PjGrammar.skip (rest_atR tb text pc)))
  (rest_atR tb text pc)); [apply pik_skip_skipn|].
remember (length (PjGrammar.skip (rest_atR tb text pc))) as ls eqn:Els.
rewrite Hl. unfold rest_atR. rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma pik_rest_cons : forall (tb : list Z) text p, text <= p < text + Z.of_nat (length tb) ->
  rest_atR tb text p = nth (Z.to_nat (p - text)) tb 0 :: rest_atR tb text (p + 1).
Proof.
intros tb text p Hp. unfold rest_atR.
replace (Z.to_nat (p + 1 - text)) with (S (Z.to_nat (p - text))) by lia.
assert (Hk : (Z.to_nat (p - text) < length tb)%nat) by lia.
revert Hk. generalize (Z.to_nat (p - text)) as k. clear. induction tb as [|b r IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma pik_rest_end : forall (tb : list Z) text, rest_atR tb text (text + Z.of_nat (length tb)) = [].
Proof. intros tb text. unfold rest_atR. replace (Z.to_nat (text + Z.of_nat (length tb) - text)) with (length tb) by lia.
apply skipn_all. Qed.

(* jr_name of an object refuses with no event when no quote follows the white space *)
Lemma pik_name_refuse : forall y, match PjGrammar.skip y with [] => True | c :: _ => c <> 34 end ->
  forall ok, jr_name true y ok = (None, [], ok).
Proof.
intros y H ok. unfold jr_name. destruct (PjGrammar.skip y) as [|c z]; [reflexivity|].
destruct (Z.eqb_spec c 34); [contradiction | reflexivity].
Qed.

(* the rest of an object's member reads its rest only through the white-space skip *)
Lemma pik_jrb_skip : forall f D n cap acc y y', PjGrammar.skip y = PjGrammar.skip y' ->
  forall ok, pi_jrb f D true n cap acc y ok = pi_jrb f D true n cap acc y' ok.
Proof. intros f D n cap acc y y' E ok. unfold pi_jrb, jr_name. rewrite E. reflexivity. Qed.

(* ... and so does the free-list model of its rest (pi_jfb reads it through jr_name) *)
Lemma pik_jfb_skip : forall f D n cap af y y', PjGrammar.skip y = PjGrammar.skip y' ->
  forall ok, pi_jfb f D true n cap af y ok = pi_jfb f D true n cap af y' ok.
Proof. intros f D n cap af y y' E ok. unfold pi_jfb, jr_name. rewrite E. reflexivity. Qed.

(* the ledger is a reader predicate *)
Lemma pik_ledger_rdeq : forall ly S Hp (W : world SEGS) m m' Lam peak cnt fail ran most own,
  mrestrict (w_H W) m' = mrestrict (w_H W) m ->
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W m Lam peak cnt fail ran most own ->
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Lam peak cnt fail ran most own E H.
unfold prh_ledger, prh_glob, prh_most, prh_own, prh_hblock in *. rewrite E. exact H.
Qed.

(* bytes read through one world's reader agree with another's wherever their views agree *)
Lemma pik_val_win : forall (W1 W2 : world SEGS) m1 m2 a n x,
  (forall k, (k < n)%nat -> aview SEGS (w_H W2) m2 (a + Z.of_nat k) = aview SEGS (w_H W1) m1 (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H W1) m1) a n x -> val_mem SEGS (mrestrict (w_H W2) m2) a n x.
Proof.
intros W1 W2 m1 m2 a n x HA HV kk Hk.
rewrite (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 (a + Z.of_nat kk) (HA kk Hk)). exact (HV kk Hk).
Qed.

(* parse_items' frame across a stretch that keeps its view on [sp + 40, entry sp + e) but for q's p field: the
   frame cells and the caller window outside rd_fp (q's cells lie at or above the entry sp) *)
Lemma pik_frame_win : forall (regs0 regs regs' : bvmap 5 word) (W : world SEGS) mem (Wc W' : world SEGS) memc mem' e q v,
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> spZ regs0 <= q ->
  (forall a, spZ regs <= a < spZ regs0 + e -> ~ (q <= a < q + 8) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs' W mem W' mem' e q v.
Proof.
intros regs0 regs regs' W mem Wc W' memc mem' e q v
  (Fsp & F3 & F4 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & Fw & Fr & He0 & He16)
  Hsp H3 H4 Hq HWN.
unfold PI_FRAME in Fsp.
assert (VW : forall o x, 40 <= o -> o + 8 <= 144 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs + o) 8 x -> val_mem SEGS (mrestrict (w_H W') mem') (spZ regs' + o) 8 x).
{ intros o x Ho1 Ho2 Hv. rewrite Hsp. apply (pik_val_win Wc W' memc mem'); [|exact Hv].
  intros kk Hk. apply HWN; lia. }
split; [rewrite Hsp; unfold PI_FRAME; lia|]. split; [rewrite H3; exact F3|]. split; [rewrite H4; exact F4|].
split; [apply VW; [lia | lia | exact V1]|]. split; [apply VW; [lia | lia | exact V2]|].
split; [apply VW; [lia | lia | exact V3]|]. split; [apply VW; [lia | lia | exact V4]|].
split; [apply VW; [lia | lia | exact V5]|]. split; [apply VW; [lia | lia | exact V6]|].
split; [apply VW; [lia | lia | exact V7]|]. split; [apply VW; [lia | lia | exact V8]|].
split; [apply VW; [lia | lia | exact V9]|]. split; [apply VW; [lia | lia | exact V10]|].
split; [apply VW; [lia | lia | exact V11]|]. split; [apply VW; [lia | lia | exact V12]|].
split; [apply VW; [lia | lia | exact V13]|].
split; [|split; [exact Fr | split; [exact He0 | exact He16]]].
intros a Ha Hn. rewrite <- (Fw a Ha Hn). apply HWN; [lia|].
intros Hqa. apply Hn. exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

(* the text's post reads memory only through the world's reader (as PItems_entry.v pi_post_stable); read and rebuilt
   through the text's record tpiP_R *)
Lemma pik_post_stable : forall ly S d o tb text len p q v Lam peak cnt fail ran most own kr,
  pi_Qstable (L := Lb) (PA := PIb) (pi_post (L := Lb) (PA := PIb) B ly S d o tb text len p q v Lam peak cnt fail ran
    most own kr).
Proof.
intros ly S d o tb text len p q v Lam peak cnt fail ran most own kr
  ly' S' Hp' W' regs m m' md md' Hm HQ.
assert (Em : mrestrict (w_H W') m' = mrestrict (w_H W') m) by (apply functional_extensionality; exact Hm).
unfold pi_post in HQ |- *.
apply tpiP_R_of in HQ. destruct HQ as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
apply tpiP_Q_of_R with (ok := ok) (res := res) (tr := tr) (okr := okr) (D := D) (Lam' := Lam') (peak' := peak')
  (cnt' := cnt') (fail' := fail') (ran' := ran').
refine {| tpiP_run := tpiP_run HR;
  tpiP_ledger := pik_ledger_rdeq ly' S' Hp' W' m m' Lam' peak' cnt' fail' ran' most own Em (tpiP_ledger HR);
  tpiP_room := tpiP_room HR; tpiP_hull := tpiP_hull HR; tpiP_live := tpiP_live HR; tpiP_pos := tpiP_pos HR;
  tpiP_outcome := tpiP_outcome HR; tpiP_injected := tpiP_injected HR; tpiP_ledger_move := tpiP_ledger_move HR;
  tpiP_blocks_move := tpiP_blocks_move HR; tpiP_bytes := tpiP_bytes HR; tpiP_lsum := tpiP_lsum HR;
  tpiP_arm := _ |}.
pose proof (tpiP_arm HR) as HA.
destruct res as [[t r]|]; cbv iota in HA |- *.
- unfold tpiP_ASome in HA |- *. rewrite Em. exact HA.
- unfold tpiP_ANone in HA |- *. rewrite Em. exact HA.
Qed.

(* a jump to the epilogue with s5 = -1: PItems_pres.v's pi_epi_spec (generic in the budget predicate P), given the
   journal at a budget WS0 with P WS0, the frame at the jump and the refused post for a0 = -1 *)
Lemma pik_epi_exit : forall d (P : list (list Z) -> Prop) (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md
  (regs0 : bvmap 5 word) e q v tb text len p Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc mdc k
  (regs : bvmap 5 word) WS0,
  pi_ajR (L := Lb) (PA := PIb) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc
    memc mdc k WS0 -> P WS0 ->
  pi_fpok fx0 fxc -> YAkMemnorm.memnorm SEGS memc ->
  pi_frame (L := Lb) (PA := PIb) regs0 regs W mem Wc memc e q v -> getr regs 21 = w64 (-1) ->
  (forall regs', getr regs' 10 = w64 (-1) ->
     pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr lyc Sc Hpc Wc regs'
       memc mdc) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PI_O_EPI) regs memc mdc)
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros d P fxc fx0 ly S Hp W mem md regs0 e q v tb text len p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc
  k regs WS0 HJ HP HFP HMN HFR H21 HQ.
apply (HEPI d P fxc fx0 ly S Hp W mem md regs0 e q v
  (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr)
  lyc Sc Hpc Wc memc mdc k regs (-1) WS0 HJ HP).
split; [exact HFP|]. split; [exact HMN|]. split; [exact HFR|]. split; [exact H21|].
split; [apply pik_post_stable | exact HQ].
Qed.

(* off the image, two equal views are two equal readers: the same byte and the same writability *)
Lemma pik_agree_view : forall (W1 W2 : world SEGS) m1 m2 x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x ->
  mbyte SEGS (mrestrict (w_H W2) m2) x = mbyte SEGS (mrestrict (w_H W1) m1) x /\
  (writable_at SEGS (mrestrict (w_H W1) m1) x -> writable_at SEGS (mrestrict (w_H W2) m2) x).
Proof.
intros W1 W2 m1 m2 x Hx Hn E.
pose proof (mbyte_of_aview SEGS _ _ _ _ x E) as EM. split; [exact EM|].
unfold mbyte in EM. rewrite (seg_rom_none SEGS x Hx Hn) in EM.
unfold writable_at, wview. revert EM.
destruct (mrestrict (w_H W1) m1 (Z_to_bv 64 x)) as [b|] eqn:E1;
  destruct (mrestrict (w_H W2) m2 (Z_to_bv 64 x)) as [b'|] eqn:E2; intros EM Hw.
- intros C; discriminate C.
- discriminate EM.
- intros C; discriminate C.
- exfalso. apply Hw. rewrite unsigned_lit_small by lia. rewrite (find_segment_none SEGS x Hn). reflexivity.
Qed.

(* ---- WHAT A CALL KEEPS OF THE HALF-BUILT CONTAINER: the node's bytes (PItems_kept.v pi_node_kept_callR_stmt) and
   the bytes of every ledger block of Dx (the journal's block clause), off the image, so the two readers agree on
   the container's footprint. The callee journal at the walk's relation and any budget WS1 (parse_string's is
   budgeted; skip_ws's is at []) ---- *)
Lemma pik_agree_call : forall (regs0 : bvmap 5 word) e v lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc
  most own STK1 sp1 e1 FP1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 (Dx : list (Z * Z)) WS1,
  prh_ledger (L := Lb) (PA := PIb) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc most own ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 ->
  (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK1 + e1) (sp1 + e1) FP1 lyc Sc Hpc Wc
    memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, sp1 <= a < sp1 + e1 -> ~ inFP FP1 a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  0 <= e1 -> sp1 + e1 <= spZ regs0 + e -> sp1 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  (forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) ->
  incl Dx Lamc ->
  (forall a, (exists b, In b Dx /\ pj_holdsR b a) -> ~ inFP FP1 a) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pj_footR v Dx).
Proof.
intros regs0 e v lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own STK1 sp1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dx
  WS1 HLG HAT Hwin Hv0 Hv1 HJ HX He1 Hs1 Hs2 Hs3 HnF Hab HDx HDF.
pose proof HJ as (HAR2 & HLY & _ & _ & _ & HFRS & _ & _ & _ & HKB & _).
cbn [app] in HFRS.
pose proof (@cf_head_nonneg cp) as CH0.
assert (RS : forall z, 0 <= z -> z <= req_size z) by (intros z Hz; unfold req_size; destruct (Z.eqb_spec z 0); lia).
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HHB.
intros x [Hx | (b & Hb & Hxb)].
- (* the node: kept by the call (PItems_kept.v's statement), off the image (a block or a fake frame) *)
  assert (EV : aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
  { apply (HKN (wle' SEGS YGcfRehidePost.RZ_cf) regs0 e v lyc Sc Hpc Wc memc mdc STK1 sp1 e1 FP1 [] ly2 S2 Hp2 W2 mem2
      md2 k1 Lamc WS1 HAT HJ HX He1 Hs1 Hs2
      Hs3 HnF); [intros b m Hbm _ _; exact (Hab _ Hbm) | | exact Hwin | exact Hx].
    intros a0 k0 Hin0. exact (proj1 (proj2 (proj1 (Forall_forall _ _) HHB (a0, k0) Hin0))). }
  apply pik_agree_view; [lia | | exact EV].
  destruct HAT as [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
  + pose proof (proj1 (Forall_forall _ _) HHB (a, k) Hin) as (Hk0 & Hab0 & _ & _ & _). cbn [fst snd] in Hk0, Hab0.
    apply Hab in Hab0. assert (RSk : k + cf_head <= req_size (k + cf_head)) by (apply RS; lia).
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) x HAR2 Hab0 ltac:(lia)).
  + apply Hab in Hin.
    assert (Hm0 : 0 <= m) by lia. pose proof (RS m Hm0).
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m x HAR2 Hin ltac:(lia)).
  + rewrite <- HFRS in Hin. pose proof HLY as (_ & _ & _ & _ & _ & EF & _).
    assert (HF2 : exists cid0 pos0, In (cid0, pos0) (frames S2) /\
      frame_addr ly2 cid0 pos0 <= x < frame_addr ly2 cid0 pos0 + fs_frame_bytes cid0).
    { exists cid, pos. split; [exact Hin|]. unfold frame_addr in *. rewrite EF. lia. }
    exact (proj2 (alx_client_img SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 x HAR2 (or_intror (or_introl HF2)))).
  + exfalso. lia.
- (* a block of Dx: a harness block of the ledger, kept by the call outside its footprint *)
  destruct b as [a k]. unfold pj_holdsR in Hxb. cbn [fst snd] in Hxb.
  pose proof (proj1 (Forall_forall _ _) HHB (a, k) (HDx _ Hb)) as (Hk0 & Hab0 & _ & _ & _). cbn [fst snd] in Hk0, Hab0.
  assert (RSk : k + cf_head <= req_size (k + cf_head)) by (apply RS; lia).
  assert (Hab2 : In (a - cf_head, k + cf_head) (ablocks B ly2 S2)) by exact (Hab _ Hab0).
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & B2 & B3 & _).
  assert (EV : aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
  { replace x with (a - cf_head + (x - (a - cf_head))) by lia.
    apply (HKB (a - cf_head) (k + cf_head) (x - (a - cf_head)) Hab0 Hab2); [lia|].
    replace (a - cf_head + (x - (a - cf_head))) with x by lia. apply HDF. exists (a, k). split; [exact Hb|].
    unfold pj_holdsR; cbn [fst snd]; lia. }
  pose proof (@YM05.alloc_ceiling_lt rc) as AC1.
  apply pik_agree_view; [lia | | exact EV].
  exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) x HAR2 Hab2 ltac:(lia)).
Qed.

(* ---- THE BATCH-KIT FREE ORDER AT A REFUSAL EXIT: the readers of the order list (pi_forder) across a memory, and the open
   container's order list (PItems_forder.v's pis_fo_open) at every depth bound the post's None arm asks ---- *)
(* the bytes pi_cont reads (PItems_value_model.pvm_cont_ufoot) lie in the container's footprint *)
Lemma pik_agree_ufoot : forall m m' v kids keys (n cap : nat) Di, (n <= cap)%nat ->
  pj_agreeR SEGS m m' (pj_footR v (pi_sblk true kids keys cap ++ Di)) ->
  pj_agreeR SEGS m m' (pvm_cont_ufoot true v kids keys n Di).
Proof.
intros m m' v kids keys n cap Di Hn H. apply (PRH_PjOrder.pf_agree_mono SEGS _ _ _ _ H).
intros x Hx. exact (pvm_ufoot_foot true v kids keys n cap Di x Hn Hx).
Qed.

(* a container with free slots has its arrays, so its block list is not empty *)
Lemma pik_sblk_cons : forall kids keys (cap : nat) (Di D0 : list (Z * Z)), (0 < cap)%nat ->
  Permutation D0 (pi_sblk true kids keys cap ++ Di) -> D0 <> [].
Proof.
intros kids keys cap Di D0 Hc HP E. subst D0. apply Permutation_nil in HP.
unfold pi_sblk, kids_blkR in HP. replace (Z.of_nat cap =? 0) with false in HP by (symmetry; apply Z.eqb_neq; lia).
discriminate HP.
Qed.

(* the open container's free order at a refusal exit (the post's None arm, every n >= MAXD - d): the completed
   slots' order list from pi_forder, then the arrays, whose requests are PresetReqAt.arrz (PItems_forder.v's pis_fo_open,
   pi_forder_at, pis_fo_slots_hb_nat; PItems_value_model.v's pvm_cont_open, pvm_foR_perm) *)
Lemma pik_fo_none : forall d (m : word -> option byte) Lamx v kids keys (n cap : nat) acc Di af D0,
  pi_cont (L := Lb) (PA := PIb) m (prh_lin Lamx) true v kids keys n cap acc Di ->
  Forall (fun mb => (PjTree.depth (snd mb) <= PjGrammar.MAXD - Nat.succ d)%nat) acc ->
  pj_apartR (pi_sblk true kids keys cap) v -> NoDup (pi_sblk true kids keys cap ++ Di) ->
  Permutation D0 (pi_sblk true kids keys cap ++ Di) -> (d < PjGrammar.MAXD)%nat ->
  pi_forder (L := Lb) (PA := PIb) m (prh_lin Lamx) true kids keys n Di acc af ->
  cf_head = PresetReqAt.HEAD -> forall n0, (PjGrammar.MAXD - d <= n0)%nat ->
  exists F, PRH_PjOrder.pj_foR SEGS m (prh_lin Lamx) n0 v D0 F /\
    map (fun b => snd b + cf_head) F = af ++ PresetReqAt.arrz true cap.
Proof.
intros d m Lamx v kids keys n cap acc Di af D0 HC HDEP HAP HND HP Hd HF Hh n0 Hn0.
destruct (PItems_forder.pi_forder_at m (prh_lin Lamx) true kids keys n Di acc af d HF Hh Hd HDEP n0 Hn0)
  as (nn & Facc & -> & _ & HO & HM).
pose proof (pvm_cont_open (L := Lb) (PA := PIb) m (prh_lin Lamx) true v kids keys n cap acc Di HC HAP HND) as HOP.
pose proof HC as (_ & Hnacc & _).
assert (EL : n = length (map snd acc)) by (rewrite length_map; exact Hnacc).
rewrite EL in HOP, HO.
pose proof (PItems_forder.pis_fo_open SEGS m (prh_lin Lamx) v true 0 kids keys (Z.of_nat cap) (map snd acc) (map fst acc)
  Di nn Facc HOP HO) as HFO.
exists (Facc ++ pis_slots true kids keys (Z.of_nat cap)). split.
- apply (pvm_foR_perm SEGS m (prh_lin Lamx) (S nn) v (pis_slots true kids keys (Z.of_nat cap) ++ Di) D0); [|exact HFO].
  apply Permutation_sym. exact HP.
- rewrite map_app, HM, (PItems_forder.pis_fo_slots_hb_nat cf_head true kids keys cap Hh). reflexivity.
Qed.

(* ---- THE RE-HIDING MOVE AT skip_ws: its text concludes the plain SRr with its post at wle; the walk's R call rule at
   wle' SEGS RZ_cf takes the callee at wle' (YA0nH.SRr_SRrG at YA0nH.wle_wle', the post's journal conjunct by
   YCbqG.ajournal_xwR_mono) ---- *)
Lemma pik_skw_lift : forall (fy : YK11.FPState) (W : world SEGS) c STK dd FP (regs : bvmap 5 word) ly S Hp
  (W0 : world SEGS) mem md Q,
  SRr SEGS W c (fpostW (fx := fy) (L := Lb) (PA := PIb) B ARx SK STK dd FP regs ly S Hp W0 mem md Q) ->
  SRrG SEGS (wle' SEGS YGcfRehidePost.RZ_cf) W c
    (fpostW_xR (fx := fy) (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK dd FP regs ly S Hp W0 mem
       md Q).
Proof.
intros fy W c STK dd FP regs ly S Hp W0 mem md Q H.
apply (SRr_SRrG SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf)).
eapply SRr_mono; [exact H|].
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Ec & HJ & HWn & HP & HQ).
hnf. exists ly', S', Hp', regs', mem', md', k. split; [exact Ec|]. split; [|exact (conj HWn (conj HP HQ))].
exact (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* ---- THE HULL USE OF parse_string's POST (pik_ps_postX's third conjunct, read by name), and the string's granted
   events as parse_string's prhPs_evs .. [] ---- *)
Lemma pik_ps_hull {fy ly S Hp W Lam peak cnt fail ran most own q text len p dd tb ly' S' Hp' W' regs' mem' md'} :
  pik_ps_postX fy ly S Hp W Lam peak cnt fail ran most own q text len p dd tb ly' S' Hp' W' regs' mem' md' ->
  PresetHullBudget.hull_used S S' (prhPs_evs (rest_atR tb text (p + 1)) []).
Proof. intros (res & _ & _ & H & _). exact H. Qed.

Lemma pik_gts_evs : forall z, PresetReqAt.rd_hevs (PRH_Charge.prhPs_gtrace z) = prhPs_evs z [].
Proof.
intros z. unfold PRH_Charge.prhPs_gtrace. destruct (jr_string z []) as [[r0 t0] o0] eqn:EJ0. cbn [fst snd].
exact (pik_ps_evs_of _ _ _ _ _ EJ0).
Qed.

(* ---- THE POSITION HALF of PItems_posb.pi_posb: a refused callee's arm gives the position over its own events, but its
   hull use only over its all-granted list, so the block's composed relation at that arm is the position alone ---- *)
Definition pik_pos (S Sc : astate) (tr : list ev) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' Sc.

Lemma pik_pos_call : forall S Sc1 Sc2 tr0 trc, PItems_posb.pi_posb S Sc1 tr0 -> pik_pos Sc1 Sc2 trc ->
  pik_pos S Sc2 (tr0 ++ trc).
Proof.
intros S Sc1 Sc2 tr0 trc H0p Hc sm x os i H0 hist Hi Hr. rewrite PresetReqAt.rd_hevs_app in Hr |- *.
apply prh_run_at_app_iff in Hr. destruct Hr as [Hr1 Hr2].
destruct (PItems_posb.pi_posb_post S Sc1 tr0 H0p sm x os i H0 hist Hi Hr1) as (hist1 & Hi1).
destruct (Hc sm x os _ H0 hist1 Hi1 Hr2) as (hist2 & Hi2).
exists hist2. rewrite length_app, Nat.add_assoc. exact Hi2.
Qed.

(* ---- THE INJECTED READING (tpiP_injected) at parse_string's refused arms ---- *)
(* the chosen failure: a granted prefix, then the one refused outcome, at the chosen index *)
Lemma pik_granted_app1 : forall (ok0 : list bool) (cnt fail : Z) (k : nat), ok0 = repeat true (length ok0) ->
  cnt + Z.of_nat (length ok0) = fail -> prh_granted (ok0 ++ [false]) cnt fail k.
Proof.
intros ok0 cnt fail k E Hf i _ Hn.
destruct (Nat.lt_ge_cases i (length ok0)) as [Hl | Hg].
- rewrite app_nth1 in Hn by exact Hl. rewrite E, nth_repeat in Hn. discriminate Hn.
- rewrite app_nth2 in Hn by exact Hg. destruct (i - length ok0)%nat as [|j] eqn:Ej.
  + replace i with (length ok0) by lia. exact Hf.
  + destruct j; cbn in Hn; discriminate Hn.
Qed.

(* the allocator's refusal: the model's run with its chosen failure k past the granted prefix tr0 and the callee's
   granted events gts (calls tr0 + calls gts <= k) makes those events first (PjGrammar.agrees_jr_items), so a callee
   whose post excludes a consumer window over gts at the call state Sc refutes the reading *)
Lemma pik_inj_excl : forall d x tr0 gts rest (S Sc : astate) (k : nat) sm xs os i H0 hist,
  PRH_Charge.prhPi_gtrace d true x = tr0 ++ gts ++ rest ->
  (PjGrammar.calls tr0 + PjGrammar.calls gts <= k)%nat ->
  (k < PjGrammar.calls (PRH_Charge.prhPi_gtrace d true x))%nat ->
  PItems_posb.pi_posb S Sc tr0 ->
  (forall sm xs os i H0 hist, PresetRoomPos.iface_room_pos sm xs os i H0 hist Sc ->
     PRH_Base.prh_run_at sm xs os i (PresetReqAt.rd_hevs gts) ->
     PRH_Base.prh_cons_from sm xs os i (length (PresetReqAt.rd_hevs gts)) -> False) ->
  PresetRoomPos.iface_room_pos sm xs os i H0 hist S ->
  PRH_Base.prh_run_at sm xs os i
    (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true x (PresetReqAt.okk k))))) ->
  PRH_Base.prh_cons_from sm xs os i
    (length (PresetReqAt.rd_hevs (snd (fst (jr_items prh_jr_strtod d true x (PresetReqAt.okk k)))))) ->
  False.
Proof.
intros d x tr0 gts rest S Sc k sm xs os i H0 hist HGT Hk1 Hk2 HPOSB HX Hpos Hrun Hcons.
unfold PRH_Charge.prhPi_gtrace in HGT, Hk2.
destruct (proj2 (PjGrammar.agrees_jr_items prh_jr_strtod d true x (PresetReqAt.okk k)) k Hk2
  (PresetRun.okk_false k) (fun i0 Hi0 => PresetRun.okk_true k i0 Hi0)) as (P & E & R1 & E2 & EG & HcP & HcE).
rewrite E2 in Hrun, Hcons. cbn [fst snd] in Hrun, Hcons.
rewrite HGT, app_assoc in EG.
assert (HP : exists Y, P = tr0 ++ gts ++ Y).
{ destruct (app_eq_app _ _ _ _ EG) as (l & [(E1 & E3) | (E1 & _)]).
  - destruct l as [|e l].
    + exists []. rewrite app_nil_r in E1. rewrite app_nil_r, <- app_assoc in *. symmetry. exact E1.
    + exfalso. cbn [app] in E3. injection E3 as Ee _. subst e.
      apply (f_equal PjGrammar.calls) in E1. rewrite !calls_app in E1. cbn [PjGrammar.calls] in E1.
      rewrite HcE in E1. lia.
  - exists l. rewrite E1, app_assoc. reflexivity. }
destruct HP as (Y & ->).
rewrite <- !app_assoc in Hrun, Hcons. rewrite !PresetReqAt.rd_hevs_app in Hrun, Hcons.
apply prh_run_at_app_iff in Hrun as [Hr0 Hr1]. apply prh_run_at_app_iff in Hr1 as [Hr1 _].
destruct (PItems_posb.pi_posb_post S Sc tr0 HPOSB sm xs os i H0 hist Hpos Hr0) as (hist1 & Hpos1).
apply (HX sm xs os _ H0 hist1 Hpos1 Hr1).
rewrite !length_app in Hcons.
lazymatch type of Hcons with PRH_Base.prh_cons_from _ _ _ _ ?kk =>
  apply (prh_cons_from_sub sm xs os i kk); [lia | exact Hcons] end.
Qed.

(* ---- A REFUSAL BEFORE THE KEY'S BLOCK: jr_name refuses with no event (no byte after the white space, or not a
   quote), so the call's run is the prefix's and the kit's post takes its None arm with the prefix's ledger, blocks and the
   half-built container. The batch kit: the prefix is granted (pi_grant), so this run IS the all-granted one (THE OUTCOME:
   PItems_ledk1.pik1_run_granted, pik1_move_ran), its ledger move is priced over gtrace = tr0, and the free order is
   the open container's with the model's jr_name-refused arm (pi_jfb) ---- *)
Lemma pik_refuse : forall d ly S tb text len p q v Lam peak cnt fail ran most own kr lyc Sc (Wc : world SEGS) memc
  f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc ly' S' Hp' (W' : world SEGS) mem' p' af,
  pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) (prh_lin Lamc) true v kids keys n cap acc Di ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc ->
  pj_apartR (pi_sblk true kids keys cap) v ->
  Permutation D0 (pi_sblk true kids keys cap ++ Di) ->
  pi_run_eqB d true (rest_atR tb text p) ok0 tr0 f n cap (rev acc) (rest_atR tb text pc) ->
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d ->
  blocks_bytes Sc <= blocks_bytes S + PRH_Charge.prh_held tr0 ->
  Ledger.lsum D0 = PjGrammar.held tr0 ->
  (d <= PjGrammar.MAXD)%nat -> (n < cap)%nat ->
  (forall ok1, jr_name true (rest_atR tb text pc) ok1 = (None, [], ok1)) ->
  pi_grant ok0 tr0 ->
  pi_forder (L := Lb) (PA := PIb) (mrestrict (w_H Wc) memc) (prh_lin Lamc) true kids keys n Di acc af ->
  pi_fl_eqB d true (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc) ->
  prh_ledger (L := Lb) (PA := PIb) B ly' S' Hp' W' mem' Lamc peakc cntc failc ranc most own ->
  room_live_cf S' -> PItems_posb.pi_posb S S' tr0 ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) tr0 ->
  ablocks B ly' S' = ablocks B lyc Sc -> frames S' = frames Sc ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W') mem') (pj_footR v (pi_sblk true kids keys cap ++ Di)) ->
  pj_in_okR SEGS (mrestrict (w_H W') mem') q text len p' (Z.of_nat d + 1) tb ->
  forall (regs' : bvmap 5 word) md', getr regs' 10 = w64 (-1) ->
  pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr
    ly' S' Hp' W' regs' mem' md'.
Proof.
intros d ly S tb text len p q v Lam peak cnt fail ran most own kr lyc Sc Wc memc
  f n cap acc kids keys Di pc ok0 tr0 D0
  Lamc peakc cntc failc ranc ly' S' Hp' W' mem' p' af
  HCONT HDEP HAP HPERM HEQ HLED HBLK HBB HLS HdM Hncap HNAME HGR HFO HFL HLG' HRL' HPOSB' HLIVE' HAB' HFR' HAGR HIN'
  regs' md' H10.
assert (HJR : jr_items prh_jr_strtod d true (rest_atR tb text p) ok0 = (None, tr0, [])).
{ assert (Hb : pi_jrb f (Nat.succ d) true n cap (rev acc) (rest_atR tb text pc) [] = (None, [], [])).
  { unfold pi_jrb, jbind. rewrite (HNAME []). reflexivity. }
  pose proof (HEQ [] None [] [] Hb) as HJ. rewrite !app_nil_r in HJ. exact HJ. }
pose proof HLED as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
pose proof (prh_ledger_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ HLG') as HND'.
assert (HNDD : NoDup D0).
{ apply NoDup_ListNoDup. apply NoDup_ListNoDup in HND'.
  assert (HN1 : List.NoDup (map fst (D0 ++ Lam))).
  { apply (Permutation_NoDup (Permutation_map fst L4)). exact HND'. }
  rewrite map_app in HN1. apply List.NoDup_app_remove_r in HN1. exact (List.NoDup_map_inv fst D0 HN1). }
assert (HDD : (d < PjGrammar.MAXD)%nat \/ D0 = []).
{ destruct (Nat.lt_ge_cases d PjGrammar.MAXD) as [Hl | Hg]; [left; exact Hl | right].
  assert (Ed : d = PjGrammar.MAXD) by lia. subst d.
  assert (Hr : jr_items prh_jr_strtod PjGrammar.MAXD true (rest_atR tb text p) ok0 = (None, [], ok0)) by reflexivity.
  rewrite Hr in HJR. injection HJR as Et _. subst tr0.
  cbn [nliveR] in L6. destruct D0 as [|b D0']; [reflexivity | cbn [length] in L6; lia]. }
assert (Hd : (d < PjGrammar.MAXD)%nat).
{ destruct HDD as [Hd | E0]; [exact Hd|]. exfalso. exact (pik_sblk_cons kids keys cap Di D0 ltac:(lia) HPERM E0). }
(* THE GRANTED RUN: the prefix ate one grant per call, and jr_name's refusal makes no call *)
assert (HGNT : prh_granted ok0 cnt fail (PjGrammar.calls tr0)) by (rewrite HGR; apply PItems_ledk1.pik1_grant_granted).
assert (HGRUN : fst (jr_items prh_jr_strtod d true (rest_atR tb text p) []) = (None, tr0)).
{ pose proof HJR as HJR'. rewrite HGR in HJR'.
  exact (PItems_ledk1.pik1_run_granted _ _ _ _ _ _ (PjGrammar.agrees_jr_items _ _ _ _) HJR'). }
assert (HGT : PRH_Charge.prhPi_gtrace d true (rest_atR tb text p) = tr0)
  by (unfold PRH_Charge.prhPi_gtrace; rewrite HGRUN; reflexivity).
assert (HRAN : ranc = ran) by exact (PItems_ledk1.pik1_move_ran _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGNT HLED).
unfold pi_post.
apply tpiP_Q_of_R with (ok := ok0) (res := None) (tr := tr0) (okr := []) (D := D0) (Lam' := Lamc) (peak' := peakc)
  (cnt' := cntc) (fail' := failc) (ran' := ranc).
(* no event after the prefix: the post's live requests and position transfer are the prefix's (pi_live, pi_posb) *)
refine {| tpiP_run := HJR; tpiP_ledger := HLG'; tpiP_room := HRL'; tpiP_hull := _; tpiP_live := HLIVE';
  tpiP_pos := PItems_posb.pi_posb_post S S' tr0 HPOSB'; tpiP_outcome := _; tpiP_injected := _;
  tpiP_ledger_move := _; tpiP_blocks_move := _; tpiP_bytes := _; tpiP_lsum := HLS; tpiP_arm := _ |}.
- (* THE HULL USE: the prefix's, and the prefix is the all-granted run *)
  rewrite HGT. exact (PItems_posb.pi_posb_hull S S' tr0 HPOSB').
- (* THE OUTCOME: this run is the all-granted one *)
  intros sm x os i H0 hist Hpos Hrun _ _. split; [exact HRAN|]. split; [exact HGRUN|].
  rewrite HGT in Hrun |- *. exact (PItems_posb.pi_posb_post _ _ _ HPOSB' sm x os i H0 hist Hpos Hrun).
- (* THE INJECTED READING: every outcome granted *)
  intros sm x os i H0 hist _ _ _ _. exact (pi_grant_granted ok0 tr0 cnt fail _ HGR).
- rewrite HGT; exact HLED.
- destruct HBLK as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [rewrite HAB'; exact B2|].
  split; [rewrite HFR'; exact B3 | exact B4].
- rewrite (blocks_bytes_bsum B ly' S'), HAB', <- (blocks_bytes_bsum B lyc Sc); exact HBB.
- (* the None arm, through the text's arm record (tpiP_RNone) *)
  apply tpiP_ANone_of_R.
  refine {| tpiPn_ret := H10; tpiPn_freeord := _; tpiPn_in_after := _; tpiPn_fd := _ |}.
  + (* THE PARTIAL FREE ORDER: the model's jr_name-refused arm, the completed slots then the arrays *)
    intros Hh n0 Hn0.
    assert (HM : prhPi_frees d true (rest_atR tb text p) ok0 = af ++ PresetReqAt.arrz true cap).
    { pose proof (HFL []) as E. rewrite app_nil_r in E. rewrite E. unfold pi_jfb. rewrite (HNAME []). reflexivity. }
    rewrite HM.
    apply (pik_fo_none d (mrestrict (w_H W') mem') Lamc v kids keys n cap acc Di af D0); [| exact HDEP | exact HAP | |
      exact HPERM | exact Hd | | exact Hh | exact Hn0].
    * exact (pi_cont_frame (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di HCONT HAGR).
    * apply NoDup_ListNoDup. apply NoDup_ListNoDup in HNDD. exact (Permutation_NoDup HPERM HNDD).
    * apply (pvm_forder_frame _ _ _ _ _ v _ _ _ _ _ _ HFO (fun x k H => H)).
      exact (pik_agree_ufoot _ _ v kids keys n cap Di ltac:(lia) HAGR).
  + destruct HIN' as (V1 & V2 & V3 & V4 & _ & _ & _ & V8 & _).
    exists p', (Z.of_nat d + 1). unfold PjGrammar.MAXD in HdM. split; [lia|]. split; [lia|].
    split; [exact V1|]. split; [exact V2|]. split; [exact V3 | exact V4].
  + apply (pi_cont_fd (L := Lb) (PA := PIb) (mrestrict (w_H W') mem') Lamc true v kids keys n cap acc Di D0 d);
      [|exact HDEP | exact HAP | exact HPERM | exact HNDD | exact HDD].
    exact (pi_cont_frame (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di HCONT HAGR).
Qed.
(* ---- THE KEY SLOT STORE (0x87c74) and what it leaves: one memory equal to another at every address but the
   slot's eight bytes keeps every reader predicate whose bytes lie elsewhere ---- *)
Lemma pik_pt : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a).
Proof. intros m m' a E. unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | exact (fun H => H)]. Qed.

(* the ledger reads only the statics and the head words (PItems_value.v's pv_ledger_kept, at the abstract image) *)
Lemma pik_ledger_kept : forall ly S Hp (W : world SEGS) mem mem' Lam peak cnt fail ran most own,
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst ->
     mbyte SEGS (mrestrict (w_H W) mem') a = mbyte SEGS (mrestrict (w_H W) mem) a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     mbyte SEGS (mrestrict (w_H W) mem') (a - cf_head + i) = mbyte SEGS (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' Lam peak cnt fail ran most own HLG Hs Hh.
pose proof (prh_ledger_live _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as G1.
pose proof (prh_ledger_peak _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as G2.
pose proof (prh_ledger_count _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as G3.
pose proof (prh_ledger_fail _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as G4.
pose proof (prh_ledger_ran _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as G5.
(* the E sweep's two cells, g_most and g_own_ran_out, by their named projections *)
pose proof (prh_ledger_most _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as (G6 & M6).
pose proof (prh_ledger_own _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as (G7 & O7).
pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as GR.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HB.
split; [|split; [exact (prh_ledger_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ HLG)
  |split; [|exact (prh_ledger_heads _ _ _ _ _ _ _ _ _ _ _ _ _ HLG)]]].
-
  assert (VK : forall a n w, (forall kk, (kk < n)%nat -> Exists (in_zr (a + Z.of_nat kk)) prh_pst) ->
    val_mem SEGS (mrestrict (w_H W) mem) a n w -> val_mem SEGS (mrestrict (w_H W) mem') a n w).
  { intros a n w Hin Hv kk Hk. rewrite (Hs _ (Hin kk Hk)). exact (Hv kk Hk). }
  refine (conj (VK _ _ _ _ G1) (conj (VK _ _ _ _ G2) (conj (VK _ _ _ _ G3) (conj (VK _ _ _ _ G4)
    (conj (VK _ _ _ _ G5) (conj (conj (VK _ _ _ _ G6) M6) (conj (conj (VK _ _ _ _ G7) O7) GR))))))).
  all: intros kk Hk; unfold prh_pst;
    repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl].
- rewrite Forall_forall in HB |- *. intros [a k] Hin. destruct (HB (a, k) Hin) as (K0 & Kin & Khp & Kal & Kv).
  cbn [fst snd] in *. refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  intros kk Hk. rewrite (Hh a k (Z.of_nat kk) Hin) by lia. exact (Kv kk Hk).
Qed.

(* the cursor reads its 24 bytes and the text *)
Lemma pik_in_ok_kept : forall m m' q text len p dd tb,
  pj_in_okR SEGS m q text len p dd tb ->
  (forall x, q <= x < q + 24 \/ text <= x < text + len ->
     mbyte SEGS m' x = mbyte SEGS m x /\ (writable_at SEGS m x -> writable_at SEGS m' x)) ->
  pj_in_okR SEGS m' q text len p dd tb.
Proof.
intros m m' q text len p dd tb (V1 & V2 & V3 & Hrw & Hq8 & Ht0 & Htl & Hp & Hlen & HG & Hdj & Hd) HA.
split; [apply (pj_valR_frame SEGS m m' q 8 p V1); intros x Hx; apply HA; lia|].
split; [apply (pj_valR_frame SEGS m m' (q + 8) 8 _ V2); intros x Hx; apply HA; lia|].
split; [apply (pj_valR_frame SEGS m m' (q + 16) 4 _ V3); intros x Hx; apply HA; lia|].
split; [intros x Hx; apply (proj2 (HA x (or_introl Hx))); exact (Hrw x Hx)|].
split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hp|]. split; [exact Hlen|].
split; [apply (garr8R_frame SEGS m m' text tb HG); intros x Hx; apply HA; right; lia|].
split; [exact Hdj | exact Hd].
Qed.

(* two entries of a list with distinct first components share their second when the firsts agree *)
Lemma pik_nodup_fst : forall (l : list (Z * Z)) a b1 b2, List.NoDup (map fst l) -> In (a, b1) l -> In (a, b2) l -> b1 = b2.
Proof.
induction l as [|[x y] l IH]; intros a b1 b2 HN H1 H2; [destruct H1|]. cbn [map] in HN.
inversion HN as [|x0 l0 Hn Hd]; subst.
destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
- injection E1 as <- <-. injection E2 as E. exact E.
- injection E1 as <- <-. exfalso. apply Hn. apply in_map_iff. exists (x, b2). auto.
- injection E2 as <- <-. exfalso. apply Hn. apply in_map_iff. exists (x, b1). auto.
- exact (IH a b1 b2 Hd H1 H2).
Qed.

Lemma pik_nodup_app_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|]. cbn [app] in H.
inversion H as [|y0 l0 Hn Hd]; subst.
destruct H1 as [<- | H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 x Hd H1 H2)].
Qed.

(* two harness blocks of one ledger with distinct bases have apart allocator blocks *)
Lemma pik_lam_disj : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a1 k1 a2 k2,
  ARx ly S Hp W mem md -> prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a1, k1) Lam -> In (a2, k2) Lam -> a1 <> a2 ->
  a1 - cf_head + req_size (k1 + cf_head) <= a2 - cf_head \/ a2 - cf_head + req_size (k2 + cf_head) <= a1 - cf_head.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a1 k1 a2 k2 HAR HLG H1 H2 Hne.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HB.
pose proof (proj1 (Forall_forall _ _) HB (a1, k1) H1) as (_ & B1 & _). pose proof (proj1 (Forall_forall _ _) HB (a2, k2) H2) as (_ & B2 & _).
cbn [fst snd] in B1, B2.
assert (Hne' : (a1 - cf_head, k1 + cf_head) <> (a2 - cf_head, k2 + cf_head)) by (intros E; injection E as E1 _; lia).
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR B1 B2 Hne') as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma pik_req_ge : forall z, 0 <= z -> z <= req_size z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

Lemma pik_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
Qed.

(* a byte inside a block of the entry state, or inside the image, is not a byte of a block the call allocated
   (PItems_value.v's pv_home_apart) *)
Lemma pik_home_apart : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own lyc Sc Hpc (Wc : world SEGS)
  memc mdc D0
  p0 n0 bK nK,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger (L := Lb) (PA := PIb) B ly S Hp W mem Lam peak cnt fail ran most own ->
  Permutation (ablocks B lyc Sc) (prhReader_ab D0 ++ ablocks B ly S) ->
  In (bK, nK) (ablocks B lyc Sc) -> ~ In (bK, nK) (ablocks B ly S) ->
  prhReader_home B ly S Hp Lam p0 n0 ->
  forall a, p0 <= a < p0 + n0 -> ~ (bK <= a < bK + req_size nK).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own lyc Sc Hpc Wc memc mdc D0 p0 n0 bK nK HAR HLg HP HinK HnK Hh a Ha HaK.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (Hold : forall b m, In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> False).
{ intros b m Hin Hr.
  assert (Hin' : In (b, m) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
  assert (Hne : (b, m) <> (bK, nK)) by (intros Ee; rewrite Ee in Hin; exact (HnK Hin)).
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hin' HinK Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Himg : in_img SEGS a -> False) by (intros Hi; exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ a HAR HinK HaK Hi)).
unfold prhReader_home, kept_at, kept_img in Hh.
destruct Hh as [[(b & m & Hin & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & H1 & H2)].
- destruct HLg as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hab & _).
  cbn [fst snd] in Hm0, Hab.
  apply (Hold _ _ Hab). assert (Hmh : 0 <= m + cf_head) by lia. pose proof (pik_req_ge (m + cf_head) Hmh). lia.
- apply Himg. destruct (Hro a Ha) as (Hr & _). exact (pik_ro_img a Hr).
- apply Himg. destruct (Hro a Ha) as (Hr & _). exact (pik_ro_img a Hr).
- apply (Hold b m Hin). assert (Hm : 0 <= m \/ m < 0) by lia.
  destruct Hm as [Hm | Hm]; [pose proof (pik_req_ge m Hm); lia | lia].
Qed.

(* the peak of one allocation of S Q bytes, against the member's text *)
Lemma pik_hpeak1 : forall (Q lz D : nat), (Nat.succ Q <= lz)%nat ->
  0 `max` (Z.of_nat (Nat.succ Q) + 0) <= 224 * Z.of_nat (Nat.succ lz) + 512 * Z.of_nat D.
Proof. intros Q lz D H. apply Nat2Z.inj_le in H. rewrite !Nat2Z.inj_succ in *. pose proof (Nat2Z.is_nonneg D). lia. Qed.

(* a bind whose first computation refuses refuses with its events (PItems_body_loop.v's pil_jbind_none) *)
Lemma pik_jbind_none : forall (A Bt : Type) (m : M A) (kk : A -> M Bt) ok t ok1,
  m ok = (None, t, ok1) -> jbind m kk ok = (None, t, ok1).
Proof. intros A Bt m kk ok t ok1 H1. unfold jbind. rewrite H1. reflexivity. Qed.

(* a bind whose first computation succeeds runs its continuation (PItems_body_loop.v's pil_jbind_some) *)
Lemma pik_jbind_some : forall (A Bt : Type) (m : M A) (kk : A -> M Bt) ok a t ok1 r t' ok2,
  m ok = (Some a, t, ok1) -> kk a ok1 = (r, t', ok2) -> jbind m kk ok = (r, t ++ t', ok2).
Proof. intros A Bt m kk ok a t ok1 r t' ok2 H1 H2. unfold jbind. rewrite H1, H2. reflexivity. Qed.

(* the member whose key string parses: the string's allocation, then pik_after_name on the rest after the string *)
Lemma pik_jrb_str_some : forall f D n cap acc z Q sn r' okin ok1,
  PjGrammar.scan z = Some Q -> PjGrammar.decode z = Some (sn, r') -> PjGrammar.take okin = (true, ok1) ->
  forall r t ok2, pik_after_name f D n cap acc sn (Nat.succ Q) r' ok1 = (r, t, ok2) ->
  pi_jrb f D true n cap acc (34 :: z) okin = (r, EAlloc (Nat.succ Q) :: t, ok2).
Proof.
intros f D n cap acc z Q sn r' okin ok1 Hs Hd Ht r t ok2 H.
assert (HS : jr_string z okin = (Some (sn, r'), [EAlloc (Nat.succ Q)], ok1)).
{ unfold jr_string. rewrite Hs. unfold jbind, jalloc. rewrite Ht. rewrite Hd. reflexivity. }
assert (Hsb : PjGrammar.sblock z = Nat.succ Q) by (unfold PjGrammar.sblock; rewrite Hs; reflexivity).
unfold pi_jrb. unfold pik_after_name in H.
destruct (PjGrammar.skip r') as [|c r1] eqn:Esk.
- unfold jbind, jfree, jrefuse in H. injection H as <- <- <-.
  apply pik_jbind_none. unfold jr_name. replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity.
  rewrite Z.eqb_refl. rewrite (pik_jbind_some _ _ _ _ okin (sn, r') [EAlloc (Nat.succ Q)] ok1 None [EFree (Nat.succ Q)] ok1 HS).
  + reflexivity.
  + rewrite Esk, Hsb. reflexivity.
- destruct (Z.eqb_spec c 58) as [Ec | Ec].
  + assert (HN : jr_name true (34 :: z) okin = (Some (sn, r1), [EAlloc (Nat.succ Q)], ok1)).
    { unfold jr_name. replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity. rewrite Z.eqb_refl.
      rewrite (pik_jbind_some _ _ _ _ okin (sn, r') [EAlloc (Nat.succ Q)] ok1 (Some (sn, r1)) [] ok1 HS).
      - rewrite app_nil_r. reflexivity.
      - rewrite Esk. rewrite (proj2 (Z.eqb_eq c 58) Ec). reflexivity. }
    exact (pik_jbind_some _ _ _ _ okin (sn, r1) [EAlloc (Nat.succ Q)] ok1 r t ok2 HN H).
  + unfold jbind, jfree, jrefuse in H. injection H as <- <- <-.
    apply pik_jbind_none. unfold jr_name. replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity.
    rewrite Z.eqb_refl. rewrite (pik_jbind_some _ _ _ _ okin (sn, r') [EAlloc (Nat.succ Q)] ok1 None [EFree (Nat.succ Q)] ok1 HS).
    * reflexivity.
    * rewrite Esk, Hsb. rewrite (proj2 (Z.eqb_neq c 58) Ec). reflexivity.
Qed.

(* the free-list twin: past a key string granted its block, the kit's jfl body (pi_jfb) is pik_fl_after with the key's own
   free lk = PresetReqAt.lf of the string's trace (pi_jfb_key at the colon, jr_name's refusal arms otherwise) *)
Lemma pik_jfb_str_some : forall f D n cap af z Q sn r' ok1,
  PjGrammar.scan z = Some Q -> PjGrammar.decode z = Some (sn, r') ->
  pi_jfb f D true n cap af (34 :: z) (true :: ok1) =
  pik_fl_after f D n cap af (PresetReqAt.lf [EAlloc (Nat.succ Q)]) r' ok1.
Proof.
intros f D n cap af z Q sn r' ok1 Hs Hd.
assert (Ht : PjGrammar.take (true :: ok1) = (true, ok1)) by reflexivity.
assert (HS : jr_string z (true :: ok1) = (Some (sn, r'), [EAlloc (Nat.succ Q)], ok1)).
{ unfold jr_string. rewrite Hs. unfold jbind, jalloc. rewrite Ht. rewrite Hd. reflexivity. }
assert (Hsb : PjGrammar.sblock z = Nat.succ Q) by (unfold PjGrammar.sblock; rewrite Hs; reflexivity).
unfold pik_fl_after. destruct (PjGrammar.skip r') as [|c r1] eqn:Esk.
- assert (HN : jr_name true (34 :: z) (true :: ok1) = (None, [EAlloc (Nat.succ Q)] ++ [EFree (Nat.succ Q)], ok1)).
  { unfold jr_name. replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity. rewrite Z.eqb_refl.
    apply (pik_jbind_some _ _ _ _ (true :: ok1) (sn, r') [EAlloc (Nat.succ Q)] ok1 None [EFree (Nat.succ Q)] ok1 HS).
    cbv beta iota. rewrite Esk, Hsb. reflexivity. }
  unfold pi_jfb. rewrite HN. reflexivity.
- destruct (Z.eqb_spec c 58) as [Ec | Ec].
  + apply (pi_jfb_key f D true n cap af (34 :: z) (true :: ok1) sn r1 [EAlloc (Nat.succ Q)] ok1).
    unfold jr_name. replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity. rewrite Z.eqb_refl.
    rewrite (pik_jbind_some _ _ _ _ (true :: ok1) (sn, r') [EAlloc (Nat.succ Q)] ok1 (Some (sn, r1)) [] ok1 HS).
    * rewrite app_nil_r. reflexivity.
    * cbv beta iota. rewrite Esk. rewrite (proj2 (Z.eqb_eq c 58) Ec). reflexivity.
  + assert (HN : jr_name true (34 :: z) (true :: ok1) = (None, [EAlloc (Nat.succ Q)] ++ [EFree (Nat.succ Q)], ok1)).
    { unfold jr_name. replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity. rewrite Z.eqb_refl.
      apply (pik_jbind_some _ _ _ _ (true :: ok1) (sn, r') [EAlloc (Nat.succ Q)] ok1 None [EFree (Nat.succ Q)] ok1 HS).
      cbv beta iota. rewrite Esk, Hsb, (proj2 (Z.eqb_neq c 58) Ec). reflexivity. }
    unfold pi_jfb. rewrite HN. reflexivity.
Qed.

(* pis_open at num 0 is pi_cont (PItems_body_loop.v's pil_cont_of_open, copied) *)
Lemma pik_cont_of_open : forall m lblk (o : bool) v kids keys (n cap : nat) acc Di,
  pis_open SEGS m lblk v o 0 kids keys (Z.of_nat cap) (Z.of_nat n) (map snd acc) (map fst acc) Di ->
  n = length acc -> (n <= cap)%nat -> Z.of_nat cap <= 2 ^ 54 ->
  pi_cont (L := Lb) (PA := PIb) m lblk o v kids keys n cap acc Di.
Proof.
intros m lblk o v kids keys n cap acc Di (HN & Hap & Hh & Hsl & Hk0 & Hit) Hn Hle H54.
split; [destruct o; exact Hh|]. split; [exact Hn|]. split; [exact Hle|]. split; [exact H54|].
destruct Hsl as (_ & _ & Hc0 & Hcp).
split.
{ destruct (Nat.eq_dec cap 0) as [E|E].
  - left. subst cap. destruct (Hc0 eq_refl) as [Hk Hy]. split; [reflexivity|]. split; [exact Hk|].
    destruct o; [apply Hy; reflexivity | apply Hk0; reflexivity].
  - right. destruct (Hcp ltac:(lia)) as [Hk Hy]. split; [lia|]. split; [exact Hk|].
    intros ->. apply Hy. reflexivity. }
split; [exact Hk0|]. split; [exact (pis_nodup_r _ _ _ HN)|].
split; [intros b x Hb; apply (Hap b x); apply in_or_app; right; exact Hb|].
unfold pis_items in Hit. destruct o.
- destruct Hit as [_ Hit]. rewrite pis_combine_map in Hit. exact Hit.
- exact Hit.
Qed.

(* pi_cont over a larger block predicate *)
Lemma pik_cont_lblk : forall m lblk lblk' (o : bool) v kids keys n cap acc Di,
  pi_cont (L := Lb) (PA := PIb) m lblk o v kids keys n cap acc Di ->
  NoDup (pi_sblk o kids keys cap ++ Di) -> pj_apartR (pi_sblk o kids keys cap) v ->
  (forall a k, lblk a k -> lblk' a k) ->
  pi_cont (L := Lb) (PA := PIb) m lblk' o v kids keys n cap acc Di.
Proof.
intros m lblk lblk' o v kids keys n cap acc Di HC HND HAP HL.
pose proof (pvm_cont_open (L := Lb) (PA := PIb) m lblk o v kids keys n cap acc Di HC HAP HND) as HO.
pose proof HC as (Hh & Hn & Hle & H54 & _).
apply (pik_cont_of_open m lblk' o v kids keys n cap acc Di); [|exact Hn | exact Hle | exact H54].
apply (pis_frame SEGS m lblk m lblk' v o 0 kids keys (Z.of_nat cap) (Z.of_nat n) (map snd acc) (map fst acc) Di
  0 (Z.of_nat n) HO).
- destruct o; exact Hh.
- lia.
- intros a k Hak. apply HL. exact (pis_open_lblk SEGS _ _ _ _ _ _ _ _ _ _ _ _ HO a k Hak).
- intros x _. split; [reflexivity | exact (fun H => H)].
Qed.

(* ---- address arithmetic (PItems_value.v's pv_shadow_low / pv_shadow_app / pv_hull_low / pv_hull_app, copied: a walk
   file is not imported) ---- *)
Lemma pik_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma pik_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
lia.
Qed.

Lemma pik_shadow_app : forall p len x, in_app p len -> 0 <= x < 2 ^ 47 -> ~ (p <= shadow_of_addr SHADOW_OFF x < p + len).
Proof.
intros p len x Happ Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma pik_hull_app : forall p len x n s, in_app p len -> 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ (p <= s < p + len).
Proof.
intros p len x n s Happ Hx Hn Hxn Hs. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *. lia.
Qed.

(* pi_cur across a store of eight bytes s .. s + 8 inside an allocator block past its head: the cursor and the frame
   are above the block, the text is apart from the slot, the shadow bytes and the statics are elsewhere, and every
   ledger head word is below its own user range *)
Lemma pik_cur_slot : forall (regs0 : bvmap 5 word) e q v text len tb dd ly2 S2 Hp2 (W2 : world SEGS) mem2 memx md2 pc
  Lam2 peak2 cnt2 fail2 ran2 most own kb km s,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd ly2 S2 Hp2 W2 mem2 pc Lam2 peak2 cnt2 fail2 ran2 most own ->
  In (kb, km) (ablocks B ly2 S2) -> kb + 8 <= s -> s + 8 <= kb + req_size km ->
  (forall x, text <= x < text + len -> ~ (s <= x < s + 8)) ->
  kb + req_size km <= q -> q + 24 <= 2 ^ 47 -> 0 <= v -> v + 56 <= 2 ^ 47 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (s <= x < s + 8) ->
     mrestrict (w_H W2) memx (Z_to_bv 64 x) = mrestrict (w_H W2) mem2 (Z_to_bv 64 x)) ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd ly2 S2 Hp2 W2 memx pc Lam2 peak2 cnt2 fail2 ran2 most own.
Proof.
intros regs0 e q v text len tb dd ly2 S2 Hp2 W2 mem2 memx md2 pc Lam2 peak2 cnt2 fail2 ran2 most own kb km s
  HAR (HIN & HRA & HSRC & HHOME & HAT & HRAV & HLG & HCNT) Hkb Hs1 Hs2 Htx Hq Hq47 Hv0 Hv47 MQ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as CH0.
pose proof HW as HW8. unfold prh_head_wide in HW8.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 kb km HAR Hkb) as (_ & K4 & Kc & Kapp & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
assert (MP : forall x, 0 <= x < 2 ^ 64 -> ~ (s <= x < s + 8) ->
  mbyte SEGS (mrestrict (w_H W2) memx) x = mbyte SEGS (mrestrict (w_H W2) mem2) x /\
  (writable_at SEGS (mrestrict (w_H W2) mem2) x -> writable_at SEGS (mrestrict (w_H W2) memx) x))
  by (intros x Hx Hn; exact (pik_pt _ _ x (MQ x Hx Hn))).
assert (AV : forall x, 0 <= x < 2 ^ 64 -> ~ (s <= x < s + 8) ->
  aview SEGS (w_H W2) memx x = aview SEGS (w_H W2) mem2 x)
  by (intros x Hx Hn; unfold aview; rewrite (proj1 (MP x Hx Hn)); reflexivity).
assert (XS : forall x, 0 <= x < 2 ^ 47 ->
  aview SEGS (w_H W2) memx (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (pik_shadow_low x Hx). pose proof (pik_shadow_app _ _ x Kapp Hx). apply AV; lia. }
pose proof HIN as (V1 & V2 & V3 & Hrw & Hq8 & Ht0 & Htl & Hpr & Hlen & HG & Hdj & Hd).
pose proof HSRC as (Hby & Ht4 & Htc & Htam & Htra & Hth).
rewrite Hlen in Htc, Htam, Htra, Hth.
refine (conj _ (conj _ (conj _ (conj HHOME (conj HAT (conj _ (conj _ HCNT))))))).
- apply (pik_in_ok_kept _ _ q text len pc _ tb HIN). intros x [Hx | Hx]; apply MP.
  + lia.
  + lia.
  + lia.
  + exact (Htx x Hx).
- eapply range_addressable_agree; [|exact HRA]. intros x Hx. apply XS. lia.
- refine (conj _ (conj Ht4 (conj _ (conj _ (conj _ _))))).
  + unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ Hby). intros x Hx. apply MP; [lia|]. apply Htx. lia.
  + rewrite Hlen. exact Htc.
  + rewrite Hlen. exact Htam.
  + eapply range_addressable_agree; [|rewrite Hlen; exact Htra]. intros x Hx. apply XS. lia.
  + intros Hn0 s0 Hs0. rewrite Hlen in Hn0, Hs0. rewrite AV; [exact (Hth Hn0 s0 Hs0)| |].
    * pose proof (pik_hull_low text len s0 ltac:(lia) Hn0 ltac:(lia) Hs0). lia.
    * pose proof (pik_hull_app _ _ text len s0 Kapp ltac:(lia) Hn0 ltac:(lia) Hs0). lia.
- eapply range_addressable_agree; [|exact HRAV]. intros x Hx. apply XS. lia.
- apply (pik_ledger_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HLG).
  + intros a Ha. pose proof (PIK_PSTIMG a Ha) as Hi. pose proof (pa_segs_low (PAImg := PIb) a Hi) as Hlow.
    unfold kLowMemEnd in Hlow. apply MP; [lia|]. intros Hsa.
    exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ a HAR Hkb ltac:(lia) Hi).
  + intros a k i Hin Hi. pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HB.
    pose proof (proj1 (Forall_forall _ _) HB (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & A4 & Ac & _).
    assert (Hkh : 0 <= k + cf_head) by lia. pose proof (pik_req_ge (k + cf_head) Hkh) as RSa.
    apply MP; [lia|].
    destruct (Z.eq_dec (a - cf_head) kb) as [E | Hne]; [lia|].
    assert (Hne' : (a - cf_head, k + cf_head) <> (kb, km)) by (intros E; injection E as E1 _; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hkb Hne') as Hdz.
    unfold zdisjoint in Hdz. cbn [fst snd] in Hdz. lia.
Qed.

(* pi_cur across the in->p++ store: the cursor's p word at q takes p1', every other byte as it was (the text, the
   shadow, the statics and the ledger's head words all lie below q) *)
Lemma pik_cur_qstore : forall (regs0 : bvmap 5 word) e q v text len tb dd ly2 S2 Hp2 (W2 : world SEGS) mem2 memx pc
  pc' Lam2 peak2 cnt2 fail2 ran2 most own,
  (forall a k, In (a, k) Lam2 -> 0 <= k /\ 4096 <= a - cf_head /\ a - cf_head + req_size (k + cf_head) <= YM05.alloc_ceiling) ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd ly2 S2 Hp2 W2 mem2 pc Lam2 peak2 cnt2 fail2 ran2 most own ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (q <= x < q + 8) ->
     mrestrict (w_H W2) memx (Z_to_bv 64 x) = mrestrict (w_H W2) mem2 (Z_to_bv 64 x)) ->
  val_mem SEGS (mrestrict (w_H W2) memx) q 8 pc' ->
  (forall x, q <= x < q + 8 -> writable_at SEGS (mrestrict (w_H W2) memx) x) ->
  text <= pc' <= text + len -> (length (rest_atR tb text pc') <= length (rest_atR tb text pc))%nat ->
  YM05.alloc_ceiling <= q -> q + 24 <= 2 ^ 47 -> 0 <= v -> v + 56 <= 2 ^ 47 ->
  pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb dd ly2 S2 Hp2 W2 memx pc' Lam2 peak2 cnt2 fail2 ran2 most own.
Proof.
intros regs0 e q v text len tb dd ly2 S2 Hp2 W2 mem2 memx pc pc' Lam2 peak2 cnt2 fail2 ran2 most own HBND
  (HIN & HRA & HSRC & HHOME & HAT & HRAV & HLG & HCNT) MQ Vq Wq Hpc' Hlr Hq0 Hq47 Hv0 Hv47.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
assert (MP : forall x, 0 <= x < 2 ^ 64 -> ~ (q <= x < q + 8) ->
  mbyte SEGS (mrestrict (w_H W2) memx) x = mbyte SEGS (mrestrict (w_H W2) mem2) x /\
  (writable_at SEGS (mrestrict (w_H W2) mem2) x -> writable_at SEGS (mrestrict (w_H W2) memx) x))
  by (intros x Hx Hn; exact (pik_pt _ _ x (MQ x Hx Hn))).
assert (AV : forall x, 0 <= x < 2 ^ 64 -> ~ (q <= x < q + 8) ->
  aview SEGS (w_H W2) memx x = aview SEGS (w_H W2) mem2 x)
  by (intros x Hx Hn; unfold aview; rewrite (proj1 (MP x Hx Hn)); reflexivity).
assert (XS : forall x, 0 <= x < 2 ^ 47 ->
  aview SEGS (w_H W2) memx (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (pik_shadow_low x Hx). apply AV; lia. }
pose proof HIN as (V1 & V2 & V3 & Hrw & Hq8 & Ht0 & Htl & Hpr & Hlen & HG & Hdj & Hd).
pose proof HSRC as (Hby & Ht4 & Htc & Htam & Htra & Hth).
rewrite Hlen in Htc, Htam, Htra, Hth.
refine (conj _ (conj _ (conj _ (conj HHOME (conj HAT (conj _ (conj _ _))))))).
- refine (conj Vq (conj _ (conj _ (conj _ (conj Hq8 (conj Ht0 (conj Htl (conj Hpc' (conj Hlen (conj _ (conj Hdj Hd))))))))))).
  + apply (pj_valR_frame SEGS _ _ _ _ _ V2). intros x Hx. apply MP; lia.
  + apply (pj_valR_frame SEGS _ _ _ _ _ V3). intros x Hx. apply MP; lia.
  + intros x Hx. destruct (Z_lt_le_dec x (q + 8)) as [Hl | Hl]; [apply Wq; lia|].
    apply (proj2 (MP x ltac:(lia) ltac:(lia))). exact (Hrw x Hx).
  + apply (garr8R_frame SEGS _ _ _ _ HG). intros x Hx. apply MP; [lia|]. rewrite <- Hlen in Hdj. lia.
- eapply range_addressable_agree; [|exact HRA]. intros x Hx. apply XS. lia.
- refine (conj _ (conj Ht4 (conj _ (conj _ (conj _ _))))).
  + unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ Hby). intros x Hx. apply MP; lia.
  + rewrite Hlen. exact Htc.
  + rewrite Hlen. exact Htam.
  + eapply range_addressable_agree; [|rewrite Hlen; exact Htra]. intros x Hx. apply XS. lia.
  + intros Hn0 s0 Hs0. rewrite Hlen in Hn0, Hs0. rewrite AV; [exact (Hth Hn0 s0 Hs0)| |].
    * pose proof (pik_hull_low text len s0 ltac:(lia) Hn0 ltac:(lia) Hs0). lia.
    * pose proof (pik_hull_low text len s0 ltac:(lia) Hn0 ltac:(lia) Hs0). lia.
- eapply range_addressable_agree; [|exact HRAV]. intros x Hx. apply XS. lia.
- apply (pik_ledger_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HLG).
  + intros a Ha. pose proof (PIK_PSTIMG a Ha) as Hi. pose proof (pa_segs_low (PAImg := PIb) a Hi) as Hlow.
    unfold kLowMemEnd in Hlow. apply MP; lia.
  + intros a k i Hin Hi. pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HB.
    destruct (HBND a k Hin) as (Hk0 & A4 & Ac).
    pose proof HW as HW8. unfold prh_head_wide in HW8.
    assert (Hkh : 0 <= k + cf_head) by lia. pose proof (pik_req_ge (k + cf_head) Hkh) as RSa.
    apply MP; lia.
- apply Nat2Z.inj_le in Hlr. lia.
Qed.

(* ---- A REFUSAL AT parse_string: the member's run refuses with the string's own events ts (none, a failed
   allocation, or an allocation and its free), so the call's run is the prefix's then ts, and the kit's post takes its None
   arm with the composed ledger, the prefix's blocks and the half-built container; its live requests and position
   transfer are the travelling facts over tr0 ++ ts (the caller composes parse_string's arm post onto the prefix's).
   The batch kit: the ledger move is the granted prefix's composed with the string's over its all-granted trace gts
   (PItems_value_model.pvm_ledger_app, the whole call's granted trace tr0 ++ gts ++ rest); THE OUTCOME per arm: a
   granted arm (no allocation, or the bad escape's malloc and free) is the all-granted run; the chosen failure at the
   string's malloc is excluded by the window premise; the allocator's refusal by parse_string's own exclusion at the
   call state, the run hypothesis split at the prefix; the free order is the open container's (pi_jfb's
   jr_name-refused arm) ---- *)
Lemma pik_null_post : forall d ly S tb text len p q v Lam peak cnt fail ran most own kr lyc Sc
  f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc oks ts gts peak2 cnt2 fail2 ran2 af
  ly' S' Hp' (W' : world SEGS) mem' p',
  pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H W') mem') (prh_lin Lamc) true v kids keys n cap acc Di ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) acc ->
  pj_apartR (pi_sblk true kids keys cap) v ->
  Permutation D0 (pi_sblk true kids keys cap ++ Di) ->
  pi_run_eqB d true (rest_atR tb text p) ok0 tr0 f n cap (rev acc) (rest_atR tb text pc) ->
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  rd_blocks_move B ly S lyc Sc D0 tr0 (rest_atR tb text p) d ->
  blocks_bytes Sc <= blocks_bytes S + PRH_Charge.prh_held tr0 ->
  length ok0 = PjGrammar.calls tr0 -> Ledger.lsum D0 = PjGrammar.held tr0 ->
  (d <= PjGrammar.MAXD)%nat -> (n < cap)%nat -> rest_atR tb text p <> [] ->
  0 <= cnt < 2 ^ 64 -> cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1 -> 0 <= fail < 2 ^ 64 ->
  jr_name true (rest_atR tb text pc) oks = (None, ts, []) ->
  length oks = PjGrammar.calls ts -> pvm_wf ts -> PjGrammar.held ts = 0 -> 0 <= PRH_Charge.prh_held ts ->
  (PjGrammar.calls ts <= PjGrammar.calls gts)%nat ->
  (exists rest, PRH_Charge.prhPi_gtrace d true (rest_atR tb text p) = tr0 ++ gts ++ rest) ->
  rd_ledger_move Lamc peakc cntc failc ranc most oks gts ts [] Lamc peak2 cnt2 fail2 ran2 ->
  pi_grant ok0 tr0 ->
  ((oks = repeat true (PjGrammar.calls ts) /\ ran2 = ranc) \/
   (cntc = failc /\ (1 <= PjGrammar.calls gts)%nat /\ oks = [false]) \/
   (cntc <> failc /\ PjGrammar.calls gts = 1%nat /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist Sc -> PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs gts) ->
       PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs gts)) -> False))) ->
  pi_forder (L := Lb) (PA := PIb) (mrestrict (w_H W') mem') (prh_lin Lamc) true kids keys n Di acc af ->
  pi_fl_eqB d true (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc) ->
  prh_ledger (L := Lb) (PA := PIb) B ly' S' Hp' W' mem' Lamc peak2 cnt2 fail2 ran2 most own ->
  room_live_cf S' -> PItems_posb.pi_posb S Sc tr0 ->
  (* the string's hull use over its all-granted events, and the position over its own events (its arm's) *)
  PresetHullBudget.hull_used Sc S' (PresetReqAt.rd_hevs gts) -> pik_pos S S' (tr0 ++ ts) ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (tr0 ++ ts) ->
  ablocks B ly' S' = ablocks B lyc Sc -> frames S' = frames Sc ->
  pj_in_okR SEGS (mrestrict (w_H W') mem') q text len p' (Z.of_nat d + 1) tb ->
  forall (regs' : bvmap 5 word) md', getr regs' 10 = w64 (-1) ->
  pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr
    ly' S' Hp' W' regs' mem' md'.
Proof.
intros d ly S tb text len p q v Lam peak cnt fail ran most own kr lyc Sc
  f n cap acc kids keys Di pc ok0 tr0 D0
  Lamc peakc cntc failc ranc oks ts gts peak2 cnt2 fail2 ran2 af ly' S' Hp' W' mem' p'
  HCONT HDEP HAP HPERM HEQ HLED HBLK HBB HOK HLS HdM Hncap Hx0 Hc0 Hc1 Hf0 HNM Hlo Hwf Hheld Hph Hcg HGTs HSM HGR HARM
  HFO HFL HLG' HRL' HPOSB0 HHU HPOSB' HLIVE' HAB' HFR' HIN'
  regs' md' H10.
assert (HSJ : pi_jrb f (Nat.succ d) true n cap (rev acc) (rest_atR tb text pc) oks = (None, ts, [])).
{ unfold pi_jrb. apply pik_jbind_none. exact HNM. }
(* the whole call's run: the prefix's, then the string's refused events *)
assert (HJR : jr_items prh_jr_strtod d true (rest_atR tb text p) (ok0 ++ oks) = (None, tr0 ++ ts, [])).
{ pose proof (HEQ oks None ts [] HSJ) as HJ. exact HJ. }
assert (HWF : pvm_wf (tr0 ++ ts)).
{ pose proof (pvm_wf_items d true (rest_atR tb text p) (ok0 ++ oks)) as W. rewrite HJR in W. exact W. }
assert (HW0 : pvm_wf tr0) by (unfold pvm_wf in HWF |- *; exact (proj1 (proj1 (pvm_wf_from_app [] tr0 ts) HWF))).
assert (HCB : (PjGrammar.calls (tr0 ++ ts) <= 2 * length (rest_atR tb text p))%nat).
{ destruct (rest_atR tb text p) as [|b y0] eqn:Ex; [exfalso; exact (Hx0 eq_refl)|].
  pose proof (PjGrammar.G7_4_items prh_jr_strtod d true b y0 (ok0 ++ oks)) as HB. rewrite HJR in HB.
  cbn [fst snd] in HB. exact HB. }
rewrite calls_app in HCB.
pose proof HLED as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
(* the prefix is granted: its move makes no refusal *)
assert (HGNT : prh_granted ok0 cnt fail (PjGrammar.calls tr0)) by (rewrite HGR; apply PItems_ledk1.pik1_grant_granted).
assert (HRAN0 : ranc = ran) by exact (PItems_ledk1.pik1_move_ran _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGNT HLED).
destruct HGTs as (rest & HGT).
(* the whole move over the call's ALL-GRANTED trace tr0 ++ gts ++ rest *)
assert (HLED' : rd_ledger_move Lam peak cnt fail ran most (ok0 ++ oks) (tr0 ++ gts ++ rest) (tr0 ++ ts) ([] ++ D0)
  Lamc peak2 cnt2 fail2 ran2).
{ apply (pvm_ledger_app Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc oks gts ts [] Lamc peak2 cnt2
    fail2 ran2 rest HW0 Hwf HOK); [lia | unfold SIZE_MAXZ; lia | lia | exact HGNT | exact Hcg | exact HLED | exact HSM]. }
rewrite <- HGT in HLED'. cbn [app] in HLED'.
pose proof (prh_ledger_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ HLG') as HND'.
assert (HNDD : NoDup D0).
{ apply NoDup_ListNoDup. apply NoDup_ListNoDup in HND'.
  assert (HN1 : List.NoDup (map fst (D0 ++ Lam))).
  { apply (Permutation_NoDup (Permutation_map fst L4)). exact HND'. }
  rewrite map_app in HN1. apply List.NoDup_app_remove_r in HN1. exact (List.NoDup_map_inv fst D0 HN1). }
assert (HDD : (d < PjGrammar.MAXD)%nat \/ D0 = []).
{ destruct (Nat.lt_ge_cases d PjGrammar.MAXD) as [Hl | Hg]; [left; exact Hl | right].
  assert (Ed : d = PjGrammar.MAXD) by lia. subst d.
  assert (Hr : jr_items prh_jr_strtod PjGrammar.MAXD true (rest_atR tb text p) (ok0 ++ oks) =
    (None, [], ok0 ++ oks)) by reflexivity.
  rewrite Hr in HJR. injection HJR as Et _. destruct tr0 as [|e0 tr0']; [|discriminate Et].
  cbn [nliveR] in L6. destruct D0 as [|b D0']; [reflexivity | cbn [length] in L6; lia]. }
assert (Hd : (d < PjGrammar.MAXD)%nat).
{ destruct HDD as [Hd | E0]; [exact Hd|]. exfalso. exact (pik_sblk_cons kids keys cap Di D0 ltac:(lia) HPERM E0). }
pose proof (pvm_hpeak_items d true (rest_atR tb text p) (ok0 ++ oks) None (tr0 ++ ts) [] Hx0 HJR) as HPK.
unfold pi_post.
apply tpiP_Q_of_R with (ok := ok0 ++ oks) (res := None) (tr := tr0 ++ ts) (okr := []) (D := D0) (Lam' := Lamc)
  (peak' := peak2) (cnt' := cnt2) (fail' := fail2) (ran' := ran2).
refine {| tpiP_run := HJR; tpiP_ledger := HLG'; tpiP_room := HRL'; tpiP_hull := _; tpiP_live := HLIVE';
  tpiP_pos := HPOSB'; tpiP_outcome := _; tpiP_injected := _; tpiP_ledger_move := HLED'; tpiP_blocks_move := _;
  tpiP_bytes := _; tpiP_lsum := _; tpiP_arm := _ |}.
- (* THE HULL USE: the prefix's, then parse_string's over its all-granted events, inside the call's list *)
  rewrite HGT, !PresetReqAt.rd_hevs_app.
  exact (PItems_posb.pi_posb_hull_call S Sc S' tr0 _ _ _ HPOSB0 eq_refl HHU).
- (* THE OUTCOME, per arm of the string *)
  intros sm x os i H0 hist Hpos Hrun Hcons Hwin.
  destruct HARM as [(Eoks & Eran) | [(Hcf & Hc1g & _) | (_ & _ & HX)]].
  + (* a granted arm: the run eats grants only, so it IS the all-granted run *)
    assert (HGRUN : fst (jr_items prh_jr_strtod d true (rest_atR tb text p) []) = (None, tr0 ++ ts)).
    { pose proof HJR as HJR'. rewrite HGR, Eoks, <- repeat_app, <- calls_app in HJR'.
      exact (PItems_ledk1.pik1_run_granted _ _ _ _ _ _ (PjGrammar.agrees_jr_items _ _ _ _) HJR'). }
    assert (HGT' : PRH_Charge.prhPi_gtrace d true (rest_atR tb text p) = tr0 ++ ts)
      by (unfold PRH_Charge.prhPi_gtrace; rewrite HGRUN; reflexivity).
    split; [rewrite Eran; exact HRAN0|]. split; [exact HGRUN|].
    rewrite HGT' in Hrun |- *. exact (HPOSB' sm x os i H0 hist Hpos Hrun).
  + (* the chosen failure at the string's malloc: one of the granted trace's calls, against the window premise *)
    exfalso. rewrite HGT, !calls_app in Hwin.
    assert (Ec : cntc = cnt + Z.of_nat (PjGrammar.calls tr0)) by (rewrite L2; apply Z.mod_small; lia).
    unfold fail_afterR, SIZE_MAXZ in L3. destruct L3 as (F1a & F1b).
    destruct (Z_lt_dec fail cnt) as [Hlt | Hge].
    * rewrite (F1b ltac:(lia)) in Hcf. lia.
    * destruct (Z_lt_dec fail (cnt + Z.of_nat (PjGrammar.calls tr0))) as [Hlt2 | Hge2].
      -- rewrite (F1a ltac:(lia)) in Hcf. lia.
      -- rewrite (F1b ltac:(lia)) in Hcf. lia.
  + (* the allocator's refusal: parse_string's own exclusion, at the call state the prefix reached *)
    exfalso. rewrite HGT, !PresetReqAt.rd_hevs_app in Hrun, Hcons.
    apply prh_run_at_app_iff in Hrun as [Hr0 Hr1]. apply prh_run_at_app_iff in Hr1 as [Hr1 _].
    destruct (PItems_posb.pi_posb_post S Sc tr0 HPOSB0 sm x os i H0 hist Hpos Hr0) as (hist1 & Hpos1).
    apply (HX sm x os _ H0 hist1 Hpos1 Hr1).
    rewrite !length_app in Hcons.
    lazymatch type of Hcons with PRH_Base.prh_cons_from _ _ _ _ ?kk =>
      apply (prh_cons_from_sub sm x os i kk); [lia | exact Hcons] end.
- (* THE INJECTED READING, per arm of the string *)
  intros sm x os i H0 hist Hpos Hrun Hcons Hwin.
  destruct HARM as [(Eoks & _) | [(Hcf & _ & Eoks) | (Hcf & Hcg1 & HX)]].
  + (* a granted arm: every outcome granted *)
    apply (pi_grant_granted (ok0 ++ oks) (tr0 ++ ts)). unfold pi_grant in HGR |- *.
    rewrite HGR, Eoks, calls_app, repeat_app. reflexivity.
  + (* the chosen failure: the granted prefix, then the one refused outcome at the chosen index *)
    subst oks.
    assert (Ec : cntc = cnt + Z.of_nat (PjGrammar.calls tr0)) by (rewrite L2; apply Z.mod_small; lia).
    unfold fail_afterR, SIZE_MAXZ in L3. destruct L3 as (F1a & F1b).
    apply pik_granted_app1; [rewrite HOK; exact HGR|]. rewrite HOK.
    destruct (Z_lt_dec fail cnt) as [Hlt | Hge]; [rewrite (F1b ltac:(lia)) in Hcf; lia|].
    destruct (Z_lt_dec fail (cnt + Z.of_nat (PjGrammar.calls tr0))) as [Hlt2 | Hge2];
      [rewrite (F1a ltac:(lia)) in Hcf; lia | rewrite (F1b ltac:(lia)) in Hcf; lia].
  + (* the allocator's refusal: the reading's chosen failure lies past the string's malloc, and parse_string's
       exclusion refutes it (pik_inj_excl) *)
    exfalso.
    assert (Ec : cntc = cnt + Z.of_nat (PjGrammar.calls tr0)) by (rewrite L2; apply Z.mod_small; lia).
    pose proof L1 as (L1a & _).
    unfold fail_afterR in L3. destruct L3 as (_ & F1b).
    destruct (Z_lt_dec fail (cnt + Z.of_nat (PjGrammar.calls tr0))) as [Hlt | Hge].
    * (* inside the granted prefix: the prefix refused nothing *)
      pose proof (L1a (Z.to_nat (fail - cnt)) ltac:(lia) ltac:(lia)) as Hn.
      unfold pi_grant in HGR. rewrite HGR, nth_repeat in Hn. discriminate Hn.
    * destruct (Z.eq_dec fail (cnt + Z.of_nat (PjGrammar.calls tr0))) as [Heq | Hne].
      -- apply Hcf. rewrite (F1b ltac:(lia)). lia.
      -- apply (pik_inj_excl d (rest_atR tb text p) tr0 gts rest S Sc (Z.to_nat (fail - cnt)) sm x os i H0 hist HGT);
           [lia | lia | exact HPOSB0 | exact HX | exact Hpos | exact Hrun | exact Hcons].
- destruct HBLK as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [rewrite HAB'; exact B2|].
  split; [rewrite HFR'; exact B3 | exact HPK].
- rewrite (blocks_bytes_bsum B ly' S'), HAB', <- (blocks_bytes_bsum B lyc Sc), pvm_prh_held_app; lia.
- rewrite held_app; lia.
- (* the None arm, through the text's arm record (tpiP_RNone) *)
  apply tpiP_ANone_of_R.
  refine {| tpiPn_ret := H10; tpiPn_freeord := _; tpiPn_in_after := _; tpiPn_fd := _ |}.
  + (* THE PARTIAL FREE ORDER: the model's jr_name-refused arm, the completed slots then the arrays *)
    intros Hh n0 Hn0.
    assert (HM : prhPi_frees d true (rest_atR tb text p) (ok0 ++ oks) = af ++ PresetReqAt.arrz true cap).
    { rewrite (HFL oks). unfold pi_jfb. rewrite HNM. reflexivity. }
    rewrite HM.
    apply (pik_fo_none d (mrestrict (w_H W') mem') Lamc v kids keys n cap acc Di af D0 HCONT HDEP HAP); [| exact HPERM
      | exact Hd | exact HFO | exact Hh | exact Hn0].
    apply NoDup_ListNoDup. apply NoDup_ListNoDup in HNDD. exact (Permutation_NoDup HPERM HNDD).
  + destruct HIN' as (V1 & V2 & V3 & V4 & _ & _ & _ & V8 & _).
    exists p', (Z.of_nat d + 1). unfold PjGrammar.MAXD in HdM. split; [lia|]. split; [lia|].
    split; [exact V1|]. split; [exact V2|]. split; [exact V3 | exact V4].
  + exact (pi_cont_fd (L := Lb) (PA := PIb) (mrestrict (w_H W') mem') Lamc true v kids keys n cap acc Di D0 d HCONT HDEP
      HAP HPERM HNDD HDD).
Qed.

(* jr_name refuses with the string's events when the string refuses *)
Lemma pik_name_str_none : forall z ok t ok', jr_string z ok = (None, t, ok') -> jr_name true (34 :: z) ok = (None, t, ok').
Proof.
intros z ok t ok' H. unfold jr_name. replace (PjGrammar.skip (34 :: z)) with (34 :: z) by reflexivity.
rewrite Z.eqb_refl. apply pik_jbind_none. exact H.
Qed.

(* THE CALL'S ALL-GRANTED TRACE at a quoted key: the granted prefix (pi_grant: its run is the all-granted one,
   PItems_ledk1.pik1_run_granted), then the string's all-granted trace (pik_gt_str), then the rest *)
Lemma pik_gtrace_split : forall d x ok0 tr0 f n cap accr z,
  pi_run_eqB d true x ok0 tr0 f n cap accr (34 :: z) -> pi_grant ok0 tr0 ->
  exists rest, PRH_Charge.prhPi_gtrace d true x = tr0 ++ PRH_Charge.prhPs_gtrace z ++ rest.
Proof.
intros d x ok0 tr0 f n cap accr z HEQ HGR.
destruct (pi_jrb f (Nat.succ d) true n cap accr (34 :: z) []) as [[r t] o'] eqn:Eb.
pose proof (HEQ [] r t o' Eb) as HJ. rewrite app_nil_r in HJ. unfold pi_grant in HGR. rewrite HGR in HJ.
pose proof (PItems_ledk1.pik1_run_granted _ _ _ _ _ _ (PjGrammar.agrees_jr_items _ _ _ _) HJ) as HG.
destruct (pik_gt_str f (Nat.succ d) n cap accr z) as (rest & Et). rewrite Eb in Et. cbn [fst snd] in Et. subst t.
exists rest. unfold PRH_Charge.prhPi_gtrace. rewrite HG. reflexivity.
Qed.

(* the string's ALL-GRANTED trace when the scan finds a closing quote: the malloc, then the free of a bad escape or
   nothing (its one call, and the held bytes after it) *)
Lemma pik_gts_some : forall z Q, PjGrammar.scan z = Some Q ->
  exists g', PRH_Charge.prhPs_gtrace z = EAlloc (Nat.succ Q) :: g' /\ PjGrammar.calls g' = 0%nat /\ prh_ev_helds g' = [].
Proof.
intros z Q Hs. destruct (PjGrammar.decode z) as [sr|] eqn:Hd.
- exists []. split; [|split; reflexivity]. unfold PRH_Charge.prhPs_gtrace, jr_string. rewrite Hs.
  unfold jbind, jalloc. cbn [PjGrammar.take]. rewrite Hd. reflexivity.
- exists [EFree (Nat.succ Q)]. split; [|split; reflexivity]. unfold PRH_Charge.prhPs_gtrace, jr_string. rewrite Hs.
  unfold jbind, jalloc. cbn [PjGrammar.take]. rewrite Hd. reflexivity.
Qed.

(* ---- parse_string's four refusal arms (a0 = 0): the string's own booleans and events, its ledger move over its
   ALL-GRANTED trace (the batch kit: refused arm at fuzz_malloc's refusal ledger), the return state's ledger, blocks and cursor,
   the arm's live-request move and position transfer over the string's own events (prhPs_evs .. [the arm's
   outcomes] = rd_hevs ts, pik_ps_evs_of), and the arm's kind for THE OUTCOME: granted, the chosen failure, or the
   allocator's refusal with parse_string's exclusion over its granted events ---- *)
Lemma pik_str_none : forall (fy : YK11.FPState)
  lyc Sc Hpc (Wc : world SEGS) Lamc peakc cntc failc ranc most own q text len pc dd
  tb ly2 S2 Hp2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
  pik_ps_postX fy lyc Sc Hpc Wc Lamc peakc cntc failc ranc most own q text len pc dd tb
    ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  ARx ly2 S2 Hp2 W2 mem2 md2 -> bv_unsigned (getr regs2 10) = 0 ->
  0 <= cntc -> cntc + 1 < 2 ^ 64 -> 0 <= Ledger.lsum Lamc <= peakc ->
  exists oks ts peak2 cnt2 fail2 ran2,
    jr_string (rest_atR tb text (pc + 1)) oks = (None, ts, []) /\
    length oks = PjGrammar.calls ts /\ pvm_wf ts /\ PjGrammar.held ts = 0 /\ 0 <= PRH_Charge.prh_held ts /\
    (PjGrammar.calls ts <= PjGrammar.calls (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1))))%nat /\
    rd_ledger_move Lamc peakc cntc failc ranc most oks (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1))) ts []
      Lamc peak2 cnt2 fail2 ran2 /\
    ((oks = repeat true (PjGrammar.calls ts) /\ ran2 = ranc) \/
     (cntc = failc /\ (1 <= PjGrammar.calls (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1))))%nat /\
      oks = [false]) \/
     (cntc <> failc /\ PjGrammar.calls (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1))) = 1%nat /\
      (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
         PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1)))) ->
         PRH_Base.prh_cons_from sm x os i
           (length (PresetReqAt.rd_hevs (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1))))) -> False))) /\
    prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 mem2 Lamc peak2 cnt2 fail2 ran2 most own /\ room_live_cf S2 /\
    ablocks B ly2 S2 = ablocks B lyc Sc /\ Hp2 = Hpc /\
    pj_in_okR SEGS (mrestrict (w_H W2) mem2) q text len pc dd tb /\
    Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
      (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) (PresetReqAt.rd_hevs ts)) /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist Sc ->
       PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs ts) ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs ts))%nat H0 hist' S2).
Proof.
intros fy lyc Sc Hpc Wc Lamc peakc cntc failc ranc most own q text len pc dd tb
  ly2 S2 Hp2 W2 regs2 mem2 md2 HPOST HAR H0
  Hc0 Hc1 Hpk.
pose proof (@cf_head_nonneg cp) as CH0. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
destruct HPOST as (res & R10 & HRL & _ & _ & HARM).
unfold tpstP_ANone, tpstP_ASome1, tpstP_ASome2, tpstP_ASome3, tpstP_ASome4 in HARM.
assert (Hres0 : 0 <= res < 2 ^ 47 -> res = 0).
{ intros Hr. rewrite R10 in H0. unfold w64 in H0. rewrite unsigned_lit_small in H0 by lia. exact H0. }
assert (HPH0 : forall t, 0 <= PjGrammar.held t -> 0 <= PRH_Charge.prh_held t).
{ intros t Ht. unfold PRH_Charge.prh_held. pose proof (Nat2Z.is_nonneg (PjGrammar.calls t)). nia. }
set (z := rest_atR tb text (pc + 1)) in *.
(* the string's granted events are parse_string's prhPs_evs .. [] *)
assert (EVg : PresetReqAt.rd_hevs (PRH_Charge.prhPs_gtrace z) = prhPs_evs z []).
{ unfold PRH_Charge.prhPs_gtrace. destruct (jr_string z []) as [[r0 t0] o0] eqn:EJ0. cbn [fst snd].
  exact (pik_ps_evs_of _ _ _ _ _ EJ0). }
assert (ER : forall Q, prh_ev_reqs [EFail (Nat.succ Q)] = [Z.of_nat (Nat.succ Q)]) by (intros Q0; reflexivity).
destruct (PjGrammar.scan z) as [Q|] eqn:HSC.
- destruct (pik_gts_some z Q HSC) as (g' & Eg & Cg & Hg').
  destruct HARM as [(Hcf & -> & EH & EA & _ & HL & HIN & HPM & HPI) |
    [(Hcf & -> & EH & EA & _ & _ & _ & HOUT & HL & HIN & HPM & HPI) |
    [(Hcf & -> & HDC & EH & EA & HL & HIN & HPM & HPI) | (Hcf & Hr4 & Hr16 & s & r & HDC & EH & EA & _)]]].
  + (* the chosen failure: g_count reaches g_fail_at *)
    assert (EJ : jr_string z [false] = (None, [EFail (Nat.succ Q)], [])) by (unfold jr_string; rewrite HSC; reflexivity).
    exists [false], [EFail (Nat.succ Q)], peakc, (cntc + 1), SIZE_MAXZ, ranc.
    split; [exact EJ|].
    split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; [apply HPH0; cbn; lia|].
    split; [rewrite Eg; cbn [PjGrammar.calls PjGrammar.is_call]; rewrite Cg; lia|].
    split.
    { unfold rd_ledger_move, prh_oks, fail_afterR. rewrite Eg.
      cbn [PjGrammar.calls PjGrammar.is_call prh_ev_helds app]. rewrite Hg'.
      cbn [lszR fold_left lsz_evR nliveR nlive_evR hpeakR held_ev map length Ledger.lsum app].
      split; [split; [intros i Hi _; destruct i; [reflexivity | lia] | split; [left; reflexivity|]]|].
      { intros i Hi Hr _. destruct i; [|lia]. unfold prh_refused in Hr. cbn [nth negb andb] in Hr.
        apply Bool.negb_true_iff, Z.eqb_neq in Hr. lia. }
      split; [rewrite Z.mod_small by lia; lia|].
      split; [split; [intros _; reflexivity | intros Hn; exfalso; lia]|].
      split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
      unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth negb andb].
      repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; cbn [negb andb]; lia. }
    split; [right; left; split; [exact Hcf | split; [rewrite Eg; cbn [PjGrammar.calls PjGrammar.is_call]; rewrite Cg; lia
      | reflexivity]]|].
    split; [exact HL|]. split; [exact HRL|]. split; [exact EA|]. split; [exact EH|]. split; [exact HIN|].
    rewrite (pik_ps_evs_of _ _ _ _ _ EJ). exact (conj HPM HPI).
  + (* the allocator's refusal: fuzz_malloc's refusal arm; THE OUTCOME's exclusion over the granted events *)
    assert (EJ : jr_string z [false] = (None, [EFail (Nat.succ Q)], [])) by (unfold jr_string; rewrite HSC; reflexivity).
    exists [false], [EFail (Nat.succ Q)], (Z.max peakc (Z.min SIZE_MAXZ (Ledger.lsum Lamc + (Z.of_nat Q + 1)))),
      ((cntc + 1) mod 2 ^ 64), failc, (if Z.of_nat Q + 1 <=? most then 1 else ranc).
    split; [exact EJ|].
    split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; [apply HPH0; cbn; lia|].
    split; [rewrite Eg; cbn [PjGrammar.calls PjGrammar.is_call]; rewrite Cg; lia|].
    split.
    { unfold rd_ledger_move, prh_oks, fail_afterR. rewrite Eg, (ER Q).
      cbn [PjGrammar.calls PjGrammar.is_call prh_ev_helds app]. rewrite Hg'.
      cbn [lszR fold_left lsz_evR nliveR nlive_evR hpeakR held_ev map length Ledger.lsum app].
      split; [split; [intros i Hi Hf; destruct i; [reflexivity | lia] | split]|].
      { destruct (Z.leb_spec (Z.of_nat Q + 1) most) as [Hm | Hm]; [right | left; reflexivity].
        split; [reflexivity|]. exists 0%nat. split; [lia|]. split.
        - unfold prh_refused. cbn [nth negb andb]. apply Bool.negb_true_iff, Z.eqb_neq. lia.
        - cbn [nth]. rewrite Nat2Z.inj_succ. exact Hm. }
      { intros i Hi Hr Hm'. destruct i; [|clear - Hi; lia]. cbn [nth] in Hm'.
        destruct (Z.leb_spec (Z.of_nat Q + 1) most) as [_ | Hlt]; [reflexivity | exfalso].
        rewrite Nat2Z.inj_succ in Hm'. clear - Hm' Hlt. lia. }
      split; [reflexivity|].
      split; [split; [intros Hn; exfalso; lia | intros _; reflexivity]|].
      split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
      unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth negb andb]. unfold SIZE_MAXZ.
      rewrite ?Nat2Z.inj_succ.
      repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; cbn [negb andb]; lia. }
    split.
    { right; right. split; [exact Hcf|].
      split; [rewrite Eg; cbn [PjGrammar.calls PjGrammar.is_call]; rewrite Cg; lia|].
      intros sm x os i H1 hist Hp Hr Hc. apply (HOUT sm x os i H1 hist Hp); rewrite <- EVg; assumption. }
    split; [exact HL|]. split; [exact HRL|]. split; [exact EA|]. split; [exact EH|]. split; [exact HIN|].
    rewrite (pik_ps_evs_of _ _ _ _ _ EJ). exact (conj HPM HPI).
  + (* decode refuses: the block is allocated and freed (granted) *)
    assert (EJ : jr_string z [true] = (None, [EAlloc (Nat.succ Q); EFree (Nat.succ Q)], []))
      by (unfold jr_string, jbind; rewrite HSC; cbn [jalloc take]; rewrite HDC; reflexivity).
    assert (EG : PRH_Charge.prhPs_gtrace z = [EAlloc (Nat.succ Q); EFree (Nat.succ Q)]).
    { unfold PRH_Charge.prhPs_gtrace, jr_string, jbind. rewrite HSC. cbn [jalloc take]. rewrite HDC. reflexivity. }
    exists [true], [EAlloc (Nat.succ Q); EFree (Nat.succ Q)], (Z.max peakc (Ledger.lsum Lamc + (Z.of_nat Q + 1))),
      (cntc + 1), failc, ranc.
    split; [exact EJ|].
    split; [reflexivity|].
    split; [cbn [pvm_wf pvm_wf_from lsz_evR]; split; [left; reflexivity | exact I]|].
    split; [cbn [PjGrammar.held held_ev]; lia|]. split; [apply HPH0; cbn [PjGrammar.held held_ev]; lia|].
    split; [rewrite EG; lia|].
    split.
    { unfold rd_ledger_move, prh_oks, fail_afterR. rewrite EG. cbn [PjGrammar.calls PjGrammar.is_call].
      split; [split; [intros i Hi Hf; destruct i; [lia | lia] | split; [left; reflexivity|]]|].
      { intros i Hi Hn Hne. destruct i; [|lia]. unfold prh_refused in Hn. cbn [nth negb andb] in Hn. discriminate Hn. }
      split; [rewrite Z.mod_small by lia; lia|].
      split; [split; [intros Hn; exfalso; lia | intros _; reflexivity]|].
      split; [apply Permutation_refl|].
      split; [unfold lszR; cbn [fold_left lsz_evR rm1nR]; rewrite Nat.eqb_refl; apply Permutation_refl|].
      split; [cbn [nliveR nlive_evR length]; reflexivity|].
      unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth negb andb].
      cbn [hpeakR held_ev]. rewrite !Nat2Z.inj_succ. lia. }
    split; [left; split; reflexivity|].
    split; [exact HL|]. split; [exact HRL|]. split; [exact EA|]. split; [exact EH|]. split; [exact HIN|].
    rewrite (pik_ps_evs_of _ _ _ _ _ EJ). exact (conj HPM HPI).
  + (* the success arm: a0 is the block, not 0 *)
    exfalso.
    assert (Hin : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S2))
      by (rewrite EA; apply in_or_app; right; left; reflexivity).
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR Hin) as (_ & B4 & Bc & _).
    assert (RS : Z.of_nat Q + 1 + cf_head <= req_size (Z.of_nat Q + 1 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
    pose proof (Hres0 ltac:(lia)). lia.
- (* scan refuses: no event, no call *)
  destruct HARM as (-> & EH & EA & HL & HIN & HPM & HPI).
  assert (EJ : jr_string z [] = (None, [], [])) by (unfold jr_string; rewrite HSC; reflexivity).
  assert (EG : PRH_Charge.prhPs_gtrace z = []) by (unfold PRH_Charge.prhPs_gtrace; rewrite EJ; reflexivity).
  exists [], [], peakc, cntc, failc, ranc.
  split; [exact EJ|].
  split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; [apply HPH0; cbn; lia|].
  split; [rewrite EG; lia|].
  split; [rewrite EG; apply pvm_ledger_nil; lia|].
  split; [left; split; reflexivity|].
  split; [exact HL|]. split; [exact HRL|]. split; [exact EA|]. split; [exact EH|]. split; [exact HIN|].
  rewrite (pik_ps_evs_of _ _ _ _ _ EJ). exact (conj HPM HPI).
Qed.


(* ---- K3 CORE (0x87c10 .. 0x87c78): the shadow checks of the keys and n fields (0x87c18, 0x87c20), the slot
   address keys + 8 n and its five UBSan checks (0x87c40 result non-zero, 0x87c50 the 2 ^ 60 guard, 0x87c54 wrap,
   0x87c58 null, 0x87c60 alignment), the slot's shadow check (0x87c70), the store of parse_string's result, and the
   NULL test (0x87c78); the continuation K takes both arms. The batch kit: the caller's journal at a budget WS0 with P WS0 (the
   runs take it rebased, and K receives it back at WS0), the post at P ---- *)
Lemma pik_k3_core : forall d (P : list (list Z) -> Prop) (fxc fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md
  (regs0 : bvmap 5 word) e q v
  (Qp : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  lyx Sx Hpx (Wx : world SEGS) memx mdx kx (regs2 : bvmap 5 word) keys n res kb km WS0,
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] lyx Sx Hpx Wx memx mdx kx WS0 ->
  YAkMemnorm.memnorm SEGS memx ->
  getr regs2 19 = w64 v -> getr regs2 22 = w64 (v + 40) -> getr regs2 24 = w64 (pi_sh (v + 40)) ->
  getr regs2 26 = w64 SHADOW_OFF -> getr regs2 10 = w64 res -> 0 <= res < 2 ^ 64 ->
  0 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 ->
  4096 <= keys -> keys mod 8 = 0 -> 0 <= n <= 2 ^ 54 -> keys + 8 * n + 8 <= 2 ^ 47 ->
  2 ^ 46 <= spZ regs2 -> spZ regs2 + 24 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H Wx) memx) (spZ regs2) 8 (2 ^ 60) ->
  val_mem SEGS (mrestrict (w_H Wx) memx) (spZ regs2 + 8) 8 (pi_sh (v + 32)) ->
  val_mem SEGS (mrestrict (w_H Wx) memx) (spZ regs2 + 16) 8 (v + 32) ->
  rd_u64 SEGS (mrestrict (w_H Wx) memx) (v + 32) keys ->
  rd_u64 SEGS (mrestrict (w_H Wx) memx) (v + 40) n ->
  (forall a, keys + 8 * n <= a < keys + 8 * n + 8 -> writable_at SEGS (mrestrict (w_H Wx) memx) a) ->
  (spZ regs2 + 24 <= v + 32 \/ v + 48 <= spZ regs2) ->
  (keys + 8 * n + 8 <= v + 32 \/ v + 48 <= keys + 8 * n) ->
  keys + 8 * n + 8 <= spZ regs2 ->
  In (kb, km) (ablocks B lyx Sx) -> ~ In (kb, km) (ablocks B ly S) ->
  kb <= keys + 8 * n -> keys + 8 * n + 8 <= kb + req_size km ->
  range_addressable (aview SEGS (w_H Wx) memx) SHADOW_OFF v 56 ->
  range_addressable (aview SEGS (w_H Wx) memx) SHADOW_OFF (keys + 8 * n) 8 ->
  (forall x, v <= x < v + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) ->
  (forall x, keys + 8 * n <= x < keys + 8 * n + 8 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) ->
  (forall memx' mdx' kx' (regs' : bvmap 5 word) off,
     ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e)
       (spZ regs0 + e) (rd_fp q v) ly S Hp W mem md [] lyx Sx Hpx Wx memx' mdx' kx' WS0 ->
     YAkMemnorm.memnorm SEGS memx' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (keys + 8 * n <= a < keys + 8 * n + 8) ->
        mrestrict (w_H Wx) memx' (Z_to_bv 64 a) = mrestrict (w_H Wx) memx (Z_to_bv 64 a)) ->
     val_mem SEGS (mrestrict (w_H Wx) memx') (keys + 8 * n) 8 res ->
     aregs_preserved regs2 regs' ->
     ((res = 0 /\ off = PI_O_EPI) \/ (res <> 0 /\ off = PIK_O_SKW2)) ->
     SRr' SEGS YGcfRehidePost.RZ_cf Wx (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb off) regs' memx' mdx')
       (fpostWFb (fx := fx0) (L := Lb) (PA := PIb) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs0 ly S Hp W mem md
          Qp)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wx (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PIK_O_STRR) regs2 memx mdx)
    (fpostWFb (fx := fx0) (L := Lb) (PA := PIb) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs0 ly S Hp W mem md Qp).
Proof.
intros d P fxc fx0 ly S Hp W mem md regs0 e q v Qp lyx Sx Hpx Wx memx mdx kx regs2 keys n res kb km WS0
  HJw HMN R19 R22 R24 R26 R10 Hres Hv Hv8 Hk4 Hk8 Hn Hkn Hsp1 Hsp2 V0 V8 V16 Vk Vn Hwr D1 D2 D3 Hkb1 Hkb2 Hkb3 Hkb4
  RAv RAs NSv NSs K.
(* the runs take the empty-budget journal, rebased at this block's depot; K takes it back at WS0 *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pik3_st_ok fxc Wx memx regs2 v keys n (PIATb PIK_O_STRR) R19 R22 R24 R26 Hv Hv8 Hk4 Hk8 ltac:(lia) Hkn
  Hsp1 Hsp2 V0 V8 V16 Vk Vn Hwr D1 D2 D3) as HS.
remember (Eimg (PI := PIb) (Ereg regs2 (pik3_extra keys n))) as E eqn:HE in HS.
assert (HEI : img_env VALb A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs2 rk).
{ intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ nk rk Hk). }
assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite (EK 19%nat 19%bv eq_refl); exact R19).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EK 26%nat 26%bv eq_refl); exact R26).
assert (E10 : ew E 10 = Z_to_bv 64 res) by (rewrite (EK 10%nat 10%bv eq_refl); exact R10).
assert (E32 : ew E 32 = Z_to_bv 64 keys) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (keys + 8 * n))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (U32 : bv_unsigned (ew E 32) = keys) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = keys + 8 * n) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = res) by (rewrite E10; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS pik_Bx1 pik3_SH E (mrestrict (w_H Wx) memx)).
{ unfold pik3_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range SEGS (w_H Wx) memx E pik_Bx1 19 v 56 v 0 56 RAv);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 19 v E19) by lia; reflexivity | lia | lia
      | intros x Hx; apply NSv; lia].
  - apply (shent_ok_of_range SEGS (w_H Wx) memx E pik_Bx1 34 (keys + 8 * n) 8 (keys + 8 * n) 0 8 RAs);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 34 _ E34) by lia; reflexivity | lia | lia | intros x Hx; apply NSs; lia]. }
clear HE.
unfold SRr', cfg_at.
change (w64 (VALb A_TEXT + PIATb PIK_O_STRR)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_STRR)).
(* the runner carrying the overlay's normality from the run's start memory to its end (YC1fPx's _inv twin) *)
pose (RUN := paj_run_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fxc) (L := Lb) (PI := PIb) (wle' SEGS YGcfRehidePost.RZ_cf)).
paj_run_tok_x_inv RUN HS HJ SHOK HMN BAND_SPAN.
{ unfold pik3_ss; cbn [ss_mem]; unfold pik3_regions.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U34 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
  exists kb, km. split; [exact Hkb1|]. split; [exact Hkb2 | lia]. }
assert (MQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (keys + 8 * n <= a < keys + 8 * n + 8) ->
  mrestrict (w_H Wx) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H Wx) memx (Z_to_bv 64 a)).
{ intros a Ha Hn'. apply HFr. intros (r & Hin & Hra). unfold pik3_ss in Hin; cbn [ss_mem] in Hin.
  unfold pik3_regions in Hin. rewrite unsigned_lit_small in Hra by lia.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hra; [lia | lia | lia|].
  rewrite U34 in Hra. lia. }
clear HF HFr HG.
(* 0x87c50 bnez ((n + 2 ^ 60) >> 61): NOT TAKEN, n <= 2 ^ 54 *)
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
{ exfalso. rewrite branch_ne_U, U_SAlu, U_SOff, U33 in Hc. cbn [zalu_raw] in Hc.
  rewrite (zcanon_id (n + 1152921504606846976)) in Hc by (unfold M64; lia).
  change (Z.land (U E (SLit 61)) 63) with 61 in Hc. rewrite Z.shiftr_div_pow2 in Hc by lia.
  rewrite (Z.div_small (n + 1152921504606846976) (2 ^ 61)) in Hc by lia.
  vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok_x_inv RUN HS HJ SHOK HMN BAND_SPAN.
{ unfold pik3_ss; cbn [ss_mem add_cond]; unfold pik3_regions.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U34 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
  exists kb, km. split; [exact Hkb1|]. split; [exact Hkb2 | lia]. }
assert (MQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (keys + 8 * n <= a < keys + 8 * n + 8) ->
  mrestrict (w_H Wx) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H Wx) memx (Z_to_bv 64 a)).
{ intros a Ha Hn'. rewrite <- (MQ1 a Ha Hn'). apply HFr. intros (r & Hin & Hra). unfold pik3_ss in Hin;
  cbn [ss_mem add_cond] in Hin. unfold pik3_regions in Hin. rewrite unsigned_lit_small in Hra by lia.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hra; [lia | lia | lia|].
  rewrite U34 in Hra. lia. }
clear HF HFr HG.
(* 0x87c54 bltu slot, keys (UBSan wrap): NOT TAKEN, keys + 8 n >= keys *)
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
{ exfalso. rewrite branch_ltu_U, (U_atom E 34 _ E34), (U_atom E 32 _ E32) in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x87c58 beqz keys (null), 0x87c60 alignment, 0x87c70 the slot's shadow: decided by the run (atom 32 >= 4096,
   atom 34 8-aligned, the shadow entry of atom 34); 0x87c74 the store; 0x87c78 the NULL test stops it *)
paj_run_tok_x_inv RUN HS HJ SHOK HMN BAND_SPAN.
{ unfold pik3_ss; cbn [ss_mem add_cond]; unfold pik3_regions.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U34 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
  exists kb, km. split; [exact Hkb1|]. split; [exact Hkb2 | lia]. }
assert (MQ3 : forall a, 0 <= a < 2 ^ 64 -> ~ (keys + 8 * n <= a < keys + 8 * n + 8) ->
  mrestrict (w_H Wx) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H Wx) memx (Z_to_bv 64 a)).
{ intros a Ha Hn'. rewrite <- (MQ2 a Ha Hn'). apply HFr. intros (r & Hin & Hra). unfold pik3_ss in Hin;
  cbn [ss_mem add_cond] in Hin. unfold pik3_regions in Hin. rewrite unsigned_lit_small in Hra by lia.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hra; [lia | lia | lia|].
  rewrite U34 in Hra. lia. }
clear HF HFr HG.
assert (E24 : sv_denot E (pi_shx (SOff 19 40)) = getr regs2 24).
{ rewrite R24. apply (pi_denot_shx E (SOff 19 40) SHADOW_OFF (v + 40)); [| exact E26 | lia | unfold SHADOW_OFF; lia].
  rewrite denot_lit_U, U_SOff, E19, unsigned_lit_small, zcanon_id by (unfold M64; lia). reflexivity. }
(* 0x87c78 beqz a0: both arms; the continuation takes each at its target *)
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
{ (* TAKEN: parse_string returned NULL *)
  assert (Hr0 : res = 0).
  { rewrite branch_eq_U, U_SOff, U10, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
    change (U E (SLit 0)) with 0 in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN BAND_SPAN (PIATb PI_O_EPI).
  { unfold pik3_ss; cbn [ss_mem add_cond]; unfold pik3_regions.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact U34 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
    exists kb, km. split; [exact Hkb1|]. split; [exact Hkb2 | lia]. }
  lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (msF := msx) in * end.
  assert (MQ4 : forall a, 0 <= a < 2 ^ 64 -> ~ (keys + 8 * n <= a < keys + 8 * n + 8) ->
    mrestrict (w_H Wx) (ms_mem msF) (Z_to_bv 64 a) = mrestrict (w_H Wx) memx (Z_to_bv 64 a)).
  { intros a Ha Hn'. rewrite <- (MQ3 a Ha Hn'). apply HFr. intros (r & Hin & Hra). unfold pik3_ss in Hin.
    cbn [ss_mem add_cond] in Hin. unfold pik3_regions in Hin. rewrite unsigned_lit_small in Hra by lia.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hra;
    [lia | lia | lia | rewrite U34 in Hra; lia]. }
  pose proof (pi_region_nth _ _ _ _ _ 3 _ HS eq_refl) as RG3. cbn [ms_mem restrict] in RG3.
  pose proof (pi_field SEGS _ _ 34%nat (keys + 8 * n) _ _ _ _ _ 0 8 (SOff 10 0) res RG3 U34 ltac:(left; reflexivity)
    ltac:(rewrite denot_lit_U, U_SOff, U10, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity) ltac:(cbn; lia)
    ltac:(zside)) as VS. rewrite Z.add_0_r in VS.
  assert (HKS : aregs_preserved regs2 (ms_regs msF)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 24) by lia.
    destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    rewrite (st_ok_restrict_reg SEGS (w_H Wx) E _ msF _ HS);
    lazymatch goal with |- context [sr_get ?l ?r] => let x := eval vm_compute in (sr_get l r) in
      change (sr_get l r) with x end;
    first [ exact E24
          | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity ]. }
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  apply (K _ _ _ _ PI_O_EPI
    (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD)
    HMN MQ4 VS HKS). left; split; [exact Hr0 | reflexivity]. }
{ (* NOT TAKEN: a block *)
  assert (Hr0 : res <> 0).
  { rewrite branch_eq_U, U_SOff, U10, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
    change (U E (SLit 0)) with 0 in Hc. apply Z.eqb_neq in Hc. exact Hc. }
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN BAND_SPAN (PIATb PIK_O_SKW2).
  { unfold pik3_ss; cbn [ss_mem add_cond]; unfold pik3_regions.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact U34 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
    exists kb, km. split; [exact Hkb1|]. split; [exact Hkb2 | lia]. }
  lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (msF := msx) in * end.
  assert (MQ4 : forall a, 0 <= a < 2 ^ 64 -> ~ (keys + 8 * n <= a < keys + 8 * n + 8) ->
    mrestrict (w_H Wx) (ms_mem msF) (Z_to_bv 64 a) = mrestrict (w_H Wx) memx (Z_to_bv 64 a)).
  { intros a Ha Hn'. rewrite <- (MQ3 a Ha Hn'). apply HFr. intros (r & Hin & Hra). unfold pik3_ss in Hin.
    cbn [ss_mem add_cond] in Hin. unfold pik3_regions in Hin. rewrite unsigned_lit_small in Hra by lia.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hra;
    [lia | lia | lia | rewrite U34 in Hra; lia]. }
  pose proof (pi_region_nth _ _ _ _ _ 3 _ HS eq_refl) as RG3. cbn [ms_mem restrict] in RG3.
  pose proof (pi_field SEGS _ _ 34%nat (keys + 8 * n) _ _ _ _ _ 0 8 (SOff 10 0) res RG3 U34 ltac:(left; reflexivity)
    ltac:(rewrite denot_lit_U, U_SOff, U10, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity) ltac:(cbn; lia)
    ltac:(zside)) as VS. rewrite Z.add_0_r in VS.
  assert (HKS : aregs_preserved regs2 (ms_regs msF)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 24) by lia.
    destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    rewrite (st_ok_restrict_reg SEGS (w_H Wx) E _ msF _ HS);
    lazymatch goal with |- context [sr_get ?l ?r] => let x := eval vm_compute in (sr_get l r) in
      change (sr_get l r) with x end;
    first [ exact E24
          | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity ]. }
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VALb A_TEXT + PIATb PIK_O_SKW2)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  apply (K _ _ _ _ PIK_O_SKW2
    (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD)
    HMN MQ4 VS HKS). right; split; [exact Hr0 | reflexivity]. }
Qed.

(* two zdisjoint-pairwise lists: the last block of a list is none of the others when it is not empty *)
Lemma pik_pairwise_last : forall (l : list (Z * Z)) x, pairwise zdisjoint (l ++ [x]) -> 0 < snd x -> ~ In x l.
Proof.
induction l as [|y l IH]; intros x HP Hx Hin; [destruct Hin|]. cbn [app pairwise] in HP. destruct HP as (HF & HP).
destruct Hin as [<- | Hin].
- rewrite Forall_forall in HF. assert (Hy : In y (l ++ [y])) by (apply in_or_app; right; left; reflexivity).
  specialize (HF y Hy). unfold zdisjoint in HF. lia.
- exact (IH x HP Hx Hin).
Qed.

(* two ranges with no common byte are apart (PItems_body_free.v's pif_disj) *)
Lemma pik_disj : forall lo1 hi1 lo2 hi2, (forall a, lo1 <= a < hi1 -> lo2 <= a < hi2 -> False) ->
  lo1 < hi1 -> lo2 < hi2 -> hi1 <= lo2 \/ hi2 <= lo1.
Proof.
intros lo1 hi1 lo2 hi2 H H1 H2. destruct (Z_le_gt_dec hi1 lo2) as [E|E]; [left; exact E|].
destruct (Z_le_gt_dec hi2 lo1) as [E'|E']; [right; exact E'|].
exfalso. apply (H (Z.max lo1 lo2)); lia.
Qed.

(* the same: the last block is apart from every other *)
Lemma pik_pairwise_last_disj : forall (l : list (Z * Z)) x y, pairwise zdisjoint (l ++ [x]) -> In y l -> zdisjoint y x.
Proof.
induction l as [|z l IH]; intros x y HP Hy; [destruct Hy|]. cbn [app pairwise] in HP. destruct HP as (HF & HP).
destruct Hy as [<- | Hy].
- rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
- exact (IH x y HP Hy).
Qed.

(* a block shadow gives the addressability of one 8-aligned granule inside it (PItems_body_free.v's pif_ra_of_bs) *)
Lemma pik_ra_of_bs : forall (rd : Z -> option Z) Bz p m a,
  block_shadow rd Bz p m -> p <= a -> a mod 8 = 0 -> a + 8 <= p + m -> range_addressable rd Bz a 8.
Proof.
intros rd Bz p m a (Hp8 & Hm & Hbs) Hpa Ha8 Ham x Hx.
exists 0. split; [|left; reflexivity].
assert (Ei : shadow_of_addr Bz x = shadow_of_addr Bz p + (a - p) / 8).
{ unfold shadow_of_addr. Z.div_mod_to_equations. lia. }
rewrite Ei. assert (Hi : 0 <= (a - p) / 8 < m / 8) by (Z.div_mod_to_equations; lia).
rewrite (Hbs ((a - p) / 8) ltac:(Z.div_mod_to_equations; lia)).
replace ((a - p) / 8 <? m / 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* ---- K5: from the second skip_ws's return (0x87c84): the shadow checks of the cursor and the end word, the end
   test (0x87c9c, to PI_O_FREE), the null check (0x87ca0), the byte's shadow check (0x87cb0, slow path 0x87e38), the
   colon test (0x87cbc, to PI_O_FREE), the -1 check (0x87cc4), the cursor's shadow check (0x87ccc), in->p++
   (0x87cd0 .. 0x87cd4), and the fall to PI_O_VAL ---- *)
Lemma pik_k5_holds : forall d CTX0 CW N,
  pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pik_k5_spec d CTX0 CW N.
Proof.
intros d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc memr mdc k regs f n cap acc kids keys Di nm kx kk pc ok0 tr0 D0 Lamc peakc cntc failc ranc
  ly2 S2 Hp2 W2 mem2 md2 k1 regs2 WS0
  HFP HENT HMN HSeq HFRM HREGS HRB H21 HIN MEQ HARm HJ2w HWS HJ1 HX HKS Hrk HHp Hab Hled2 Hin2.
(* THE BUDGETED JOURNAL: the runs take it rebased at the return state's depot; every hand-off steps back to WS0 *)
pose proof (ajxR_wild HJ2w) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2w) as HJ2.
pose proof HIN as HI2.
destruct HIN as (HCUR & HN & Hncap & HCONT & HDEP & HAP & HKEY & HPERM & HKIN & HKNL & Hkk0 & HKNB & HFU & HEQ & HLED
  & HBLK & HPOSB & HLIVE & HBB & HOK & HLS & HROOM & HGR & Hcapn & HNCAPS & af & lk & HFORD & HLK & HFLA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HENT as (Emn & _ & Epk2 & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & _).
(* the travelling position and live requests at the return state: skip_ws keeps the state (S2 = Sc) *)
assert (HPOSB2 : PItems_posb.pi_posb S S2 tr0) by exact (PItems_posb.pi_posb_eq S Sc S2 tr0 HSeq HPOSB).
assert (HLIVE2 : PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
  (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) tr0) by (rewrite HSeq; exact HLIVE).
pose proof RDP as (_ & _ & _ & _ & _ & Hfwin & Hspq & Hqe & _ & _ & _ & _ & HPV & Hqv & Htv & Hvw & _ & HdM & _).
pose proof HPV as (Hv4096 & Hv8 & _ & _ & _ & Hvam & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
pose proof HJ2w as (HAR2 & HLY2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo2 & Eshi2 & _).
pose proof HJ1 as (HAR1 & HLY1 & _ & _ & _ & Hfrs1 & _). cbn [app] in Hfrs1.
pose proof (pik_stk_skw d) as HSTKB. pose proof (PIK_FR0 F_skip_ws) as HSKW0.
unfold STK_skip_ws, PI_FRAME in HSTKB.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold ASAN_CEIL in CR.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
(* the disjunctions this block does not use: lia would split on them *)
clear Ecur Htv Hd032.
(* the registers at the return site: skip_ws keeps every callee-saved one *)
assert (R9 : getr regs2 9 = w64 q) by (rewrite <- Q9; exact (HKS 9 ltac:(unfold acallee_saved; lia))).
assert (R8 : getr regs2 8 = w64 (q + 16)) by (rewrite <- Q8; exact (HKS 8 ltac:(unfold acallee_saved; lia))).
assert (R18 : getr regs2 18 = w64 1) by (rewrite <- Q18; exact (HKS 18 ltac:(unfold acallee_saved; lia))).
assert (R19 : getr regs2 19 = w64 v) by (rewrite <- Q19; exact (HKS 19 ltac:(unfold acallee_saved; lia))).
assert (R20 : getr regs2 20 = w64 (q + 8)) by (rewrite <- Q20; exact (HKS 20 ltac:(unfold acallee_saved; lia))).
assert (R21 : getr regs2 21 = w64 (-1)) by (rewrite <- H21; exact (HKS 21 ltac:(unfold acallee_saved; lia))).
assert (R23 : getr regs2 23 = w64 (pi_sh (q + 8))) by (rewrite <- Q23; exact (HKS 23 ltac:(unfold acallee_saved; lia))).
assert (R25 : getr regs2 25 = w64 (pi_sh (q + 16))) by (rewrite <- Q25; exact (HKS 25 ltac:(unfold acallee_saved; lia))).
assert (R26 : getr regs2 26 = w64 SHADOW_OFF) by (rewrite <- Q26; exact (HKS 26 ltac:(unfold acallee_saved; lia))).
assert (R27 : getr regs2 27 = w64 (pi_sh q)) by (rewrite <- Q27; exact (HKS 27 ltac:(unfold acallee_saved; lia))).
assert (R2 : getr regs2 2 = getr regs 2) by exact (HKS 2 ltac:(unfold acallee_saved; lia)).
assert (R3 : getr regs2 3 = getr regs 3) by exact (HKS 3 ltac:(unfold acallee_saved; lia)).
assert (R4 : getr regs2 4 = getr regs 4) by exact (HKS 4 ltac:(unfold acallee_saved; lia)).
assert (R22 : getr regs2 22 = getr regs 22) by exact (HKS 22 ltac:(unfold acallee_saved; lia)).
assert (R24 : getr regs2 24 = getr regs 24) by exact (HKS 24 ltac:(unfold acallee_saved; lia)).
(* the cursor skip_ws left *)
set (y := rest_atR tb text pc) in *.
set (p1 := text + len - Z.of_nat (length (PjGrammar.skip y))) in *.
pose proof Hin2 as (Vp2 & Ve2 & Vd2 & Hrw2 & _ & _ & _ & Hple2 & _ & HG2 & _ & _).
pose proof (PjGrammar.skip_len y) as Hsk.
assert (Hly : Z.of_nat (length y) = text + len - pc) by (unfold y, rest_atR; rewrite length_skipn; lia).
assert (Hlr1 : length (rest_atR tb text p1) = length (PjGrammar.skip y)) by (unfold rest_atR; rewrite length_skipn; lia).
assert (HSK : PjGrammar.skip y = rest_atR tb text p1).
{ unfold y. etransitivity; [apply pik_skip_rest; lia|]. f_equal. unfold p1, y. lia. }
assert (Ep1 : p1 = text + len - Z.of_nat (length (PjGrammar.skip y))) by reflexivity.
assert (Ey : y = rest_atR tb text pc) by reflexivity.
assert (HLe2 : (length (rest_atR tb text (p1 + 1)) <= length (rest_atR tb text pc))%nat).
{ assert (Hsk' : (length (PjGrammar.skip y) <= length tb - Z.to_nat (pc - text))%nat)
    by (unfold y, rest_atR in Hsk; rewrite length_skipn in Hsk; exact Hsk).
  assert (Hpcp : pc <= p1) by (unfold p1; clear - Hsk' Hple Hlen; lia).
  unfold rest_atR. rewrite !length_skipn. clear - Hpcp Hple Hlen. lia. }
clearbody p1 y.
(* the cursor, the text, the node's place and the ledger at the return state (the shared kept statement) *)
assert (HCUR2 : pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 p1 Lamc peakc cntc failc ranc
  most own).
{ apply (HKC (wle' SEGS YGcfRehidePost.RZ_cf) regs0 e q v text len tb d lyc Sc Hpc Wc memr mdc pc Lamc peakc cntc
    failc ranc most own
    STK_skip_ws (spZ regs) (PI_FRAME + e) [(q, q + 8)] [] ly2 S2 Hp2 W2 mem2 md2 k1 p1 Lamc peakc cntc failc ranc most own
    []).
  - exact (pik_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc memr pc Lamc peakc cntc failc ranc most own MEQ HCUR).
  - exact HJ1.
  - exact HX.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - lia.
  - destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | Hro] | (b & m & Hbin & _ & Hb1 & Hb2)].
    + right; right. pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HHB.
      pose proof (proj1 (Forall_forall _ _) HHB _ Hbin) as (K0 & Kin & _). cbn [fst snd] in K0, Kin.
      exists (b - cf_head), (m + cf_head). split; [exact Kin | lia].
    + destruct Hro as [Hro | Hki]; [left; exact Hro | right; left; exact Hki].
    + right; right. exists b, m. auto.
  - intros b m Hbin _. rewrite Hab, HHp. split; [exact Hbin | tauto].
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    assert (Ha47 : 0 <= a < 2 ^ 47) by (clear - Ha Htc Ht0 ACL; lia).
    pose proof (pik_shadow_low a Ha47) as HSl. clear - Hra HSl Hq0 CR. lia.
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    assert (Ha47 : 0 <= a < 2 ^ 47)
      by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; clear - Hvam Ha Hv4096; lia).
    pose proof (pik_shadow_low a Ha47) as HSl. clear - Hra HSl Hq0 CR. lia.
  - intros (r & Hr & H0). destruct Hr as [<- | []]. cbn [fst snd] in H0. lia.
  - left. exact Hin2.
  - exact Hled2.
  - rewrite Hlr1. lia.
  - left. reflexivity.
  - intros a k' Hk' _. exact Hk'.
  - lia.
  - lia.
  - intros a k' Hk'. left. exact Hk'.
  - exact HARm. }
pose proof HCUR2 as (_ & HRA2 & HSRC2 & HHOME2 & HPLAT2 & HRAV2 & HLG2 & HCNT2).
pose proof HSRC2 as (_ & _ & _ & _ & Htra2 & _). rewrite Hlen in Htra2.
assert (Hqb : 4096 <= q <= 2 ^ 47 - 24) by lia.
assert (AVR : forall (H : word -> bool) m m' a, mrestrict H m' = mrestrict H m -> aview SEGS H m' a = aview SEGS H m a)
  by (intros H m m' a Em; unfold aview; rewrite Em; reflexivity).
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HHBc.
pose proof HLED as (_ & _ & _ & HLP & _).
assert (HINCL : incl (pi_sblk true kids keys cap ++ Di ++ [(kx, kk)]) Lamc).
{ intros b Hb. apply (Permutation_in b (Permutation_sym HLP)). apply in_or_app. left.
  exact (Permutation_in b (Permutation_sym HPERM) Hb). }
(* the container and the key at the return state: skip_ws writes the cursor only *)
assert (AGR2 : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2)
  (pj_footR v (pi_sblk true kids keys cap ++ Di ++ [(kx, kk)]))).
{ rewrite <- MEQ.
  apply (pik_agree_call regs0 e v lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own STK_skip_ws (spZ regs)
    (PI_FRAME + e) [(q, q + 8)] ly2 S2 Hp2 W2 mem2 md2 k1 (pi_sblk true kids keys cap ++ Di ++ [(kx, kk)]) []).
  - exact (pik_ledger_rdeq lyc Sc Hpc Wc memc memr Lamc peakc cntc failc ranc most own MEQ HLG).
  - exact HPLAT.
  - exact Hvw.
  - lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. clear - Hvam Hv4096. lia.
  - exact HJ1.
  - exact HX.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - intros b Hb. rewrite Hab. exact Hb.
  - exact HINCL.
  - intros a ((a0 & k0) & Hb & Hab0) (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    unfold pj_holdsR in Hab0. cbn [fst snd] in Hab0.
    pose proof (proj1 (Forall_forall _ _) HHBc (a0, k0) (HINCL _ Hb)) as (Hk0 & Hb0 & _ & _ & _).
    cbn [fst snd] in Hk0, Hb0. rewrite <- Hab in Hb0.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 Hb0) as (_ & B2 & B3 & _).
    assert (RSk : k0 + cf_head <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    lia. }
assert (HCONT2 : pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H W2) mem2) (prh_lin Lamc) true v kids keys n cap acc Di).
{ apply (pi_cont_frame (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di HCONT).
  intros x [Hx | (b & Hb & Hh)]; apply AGR2; [left; exact Hx|]. right. exists b. split; [|exact Hh].
  apply in_app_or in Hb. destruct Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
(* The batch kit's invariants at the return state: the completed slots' capacities and free order, read through the bytes
   pi_cont reads, which skip_ws kept (PItems_value_model.v's pvm_ncaps_frame / pvm_forder_frame) *)
assert (AGU2 : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pvm_cont_ufoot true v kids keys n Di)).
{ apply (pik_agree_ufoot _ _ v kids keys n cap Di ltac:(lia)).
  apply (PRH_PjOrder.pf_agree_mono SEGS _ _ _ _ AGR2). intros x [Hx | (b & Hb & Hh)]; [left; exact Hx|].
  right. exists b. split; [|exact Hh].
  apply in_app_or in Hb. destruct Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
pose proof (pvm_ncaps_frame (w_H Wc) memc (mrestrict (w_H W2) mem2) (prh_lin Lamc) true v kids keys n cap acc Di
  HCONT HNCAPS AGU2) as HNCAPS2.
pose proof (pvm_forder_frame _ _ _ _ _ v _ _ _ _ _ _ HFORD (fun x k H => H) AGU2) as HFORD2.
assert (Hkin : In (keys, 8 * Z.of_nat cap) (pi_sblk true kids keys cap)).
{ pose proof HCONT as (_ & _ & Hnc & _ & Hsl & _). destruct Hsl as [(Hc0 & _ & _) | (Hcp & _ & _)]; [lia|].
  unfold pi_sblk, kids_blkR, keys_blkR. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn. right. left. reflexivity. }
assert (HKEY2 : pi_key (L := Lb) (PA := PIb) (mrestrict (w_H W2) mem2) (prh_lin Lamc) true keys n nm [(kx, kk)]).
{ unfold pi_key in HKEY |- *. destruct HKEY as (x & kx' & Ex & (Hx0 & Hx) & Hcs). exists x, kx'. split; [exact Ex|].
  injection Ex as <- <-. split.
  - split; [exact Hx0|]. apply (pj_valR_frame SEGS _ _ _ _ _ Hx). intros y0 Hy0.
    assert (Hf : pj_footR v (pi_sblk true kids keys cap ++ Di ++ [(kx, kk)]) y0).
    { right. exists (keys, 8 * Z.of_nat cap). split; [apply in_or_app; left; exact Hkin|]. unfold pj_holdsR.
      cbn [fst snd]. pose proof HCONT as (_ & _ & Hnc & _). lia. }
    exact (proj1 (AGR2 y0 Hf)).
  - apply (pj_cstrR_frame SEGS _ _ _ _ _ _ Hcs). intros y0 Hy0.
    assert (Hf : pj_footR v (pi_sblk true kids keys cap ++ Di ++ [(kx, kk)]) y0).
    { right. exists (kx, kk). split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
      unfold pj_holdsR. cbn [fst snd]. lia. }
    exact (proj1 (AGR2 y0 Hf)). }
assert (KS2 : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HKS.
(* ---- A JUMP TO PI_O_FREE (no colon after the key): pi_free_spec's pre ---- *)
assert (FREE : forall mem' md' k' (regs' : bvmap 5 word),
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem' md' k' WS0 ->
  YAkMemnorm.memnorm SEGS mem' ->
  mrestrict (w_H W2) mem' = mrestrict (w_H W2) mem2 ->
  (forall r : Z, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  (forall ok1, pik_after_name f (Nat.succ d) n cap (rev acc) nm (Z.to_nat kk) y ok1 =
     (None, [EFree (Z.to_nat kk)], ok1)) ->
  (forall ok1, pik_fl_after f (Nat.succ d) n cap af lk y ok1 = af ++ PresetReqAt.arrz true cap) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PI_O_FREE) regs' mem' md')
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr))).
{ intros mem' md' k' regs' HJx HMNx MEQx KKx HAN HAF.
  assert (KK : forall r : Z, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (intros r Hr; etransitivity; [exact (KKx r Hr) | exact (KS2 r Hr)]).
  assert (R2x : getr regs' 2 = getr regs 2) by exact (KK 2 ltac:(unfold acallee_saved; lia)).
  assert (Rsp' : spZ regs' = spZ regs) by (unfold spZ; rewrite R2x; reflexivity).
  assert (WINx : forall a, spZ regs <= a < spZ regs0 + e -> ~ (q <= a < q + 8) ->
    aview SEGS (w_H W2) mem' a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn. rewrite (AVR _ _ _ a MEQx), (AVR _ _ _ a (eq_sym MEQ)).
    apply HX; [unfold PI_FRAME; lia|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia. }
  apply (HFREE fxc fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p Lam peak cnt fail ran most own kr
    ly2 S2 Hp2 W2 mem' md' k' regs' WS0 HJx HWS).
  pose proof HRB as (B22 & B24 & BV0 & BV32 & BV24 & BV16 & BV8).
  refine (conj eq_refl (conj HFP (conj HENT (conj HMNx (conj _ (conj _ (conj _ (conj _ _)))))))).
  - exact (pik_frame_win regs0 regs regs' W mem Wc W2 memc mem' e q v HFRM Rsp'
      (KK 3 ltac:(unfold acallee_saved; lia)) (KK 4 ltac:(unfold acallee_saved; lia)) Hspq WINx).
  - unfold pi_regs.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    + etransitivity; [exact (KK 9 ltac:(unfold acallee_saved; lia)) | exact Q9].
    + etransitivity; [exact (KK 19 ltac:(unfold acallee_saved; lia)) | exact Q19].
    + etransitivity; [exact (KK 18 ltac:(unfold acallee_saved; lia)) | exact Q18].
    + etransitivity; [exact (KK 8 ltac:(unfold acallee_saved; lia)) | exact Q8].
    + etransitivity; [exact (KK 20 ltac:(unfold acallee_saved; lia)) | exact Q20].
    + etransitivity; [exact (KK 26 ltac:(unfold acallee_saved; lia)) | exact Q26].
    + etransitivity; [exact (KK 27 ltac:(unfold acallee_saved; lia)) | exact Q27].
    + etransitivity; [exact (KK 25 ltac:(unfold acallee_saved; lia)) | exact Q25].
    + etransitivity; [exact (KK 23 ltac:(unfold acallee_saved; lia)) | exact Q23].
  - unfold pi_regs_body. rewrite Rsp'.
    assert (VWx : forall a x, spZ regs <= a -> a + 8 <= spZ regs + 40 ->
      val_mem SEGS (mrestrict (w_H Wc) memc) a 8 x -> val_mem SEGS (mrestrict (w_H W2) mem') a 8 x).
    { intros a x Ha1 Ha2 Hv. apply (pik_val_win Wc W2 memc mem' a 8 x); [|exact Hv].
      intros kk' Hk. apply WINx; lia. }
    split; [etransitivity; [exact (KK 22 ltac:(unfold acallee_saved; lia)) | exact B22]|].
    split; [etransitivity; [exact (KK 24 ltac:(unfold acallee_saved; lia)) | exact B24]|].
    split; [apply VWx; [lia | lia | exact BV0]|]. split; [apply VWx; [lia | lia | exact BV32]|].
    split; [apply VWx; [lia | lia | exact BV24]|]. split; [apply VWx; [lia | lia | exact BV16]|].
    apply VWx; [lia | lia | exact BV8].
  - etransitivity; [exact (KK 21 ltac:(unfold acallee_saved; lia)) | exact H21].
  - exists n, cap, acc, kids, keys, Di, ok0, tr0, D0, Lamc, peakc, cntc, failc, ranc, kx, kk.
    pose proof HKEY2 as (x & kx' & Ex & (_ & VK) & _). injection Ex as <- <-.
    split.
    { exists p1, (Z.of_nat d + 1). unfold PjGrammar.MAXD in HdM. split; [lia|]. split; [lia|].
      rewrite MEQx. split; [exact Vp2|]. split; [exact Ve2|]. split; [exact Vd2 | exact Hrw2]. }
    split; [exact HPLAT2|].
    split; [eapply range_addressable_agree; [|exact HRAV2]; intros x0 Hx0; exact (AVR _ _ _ _ MEQx)|].
    split; [exact (pik_ledger_rdeq ly2 S2 Hp2 W2 mem2 mem' Lamc peakc cntc failc ranc most own MEQx Hled2)|].
    split; [exact Hncap|].
    split; [rewrite MEQx; exact HCONT2|].
    split; [exact HDEP|]. split; [exact HAP|]. split; [exact HPERM|].
    split; [rewrite MEQx; exact VK|].
    split; [exact HKIN|]. split; [exact HKNL|]. split; [exact HKNB|].
    split; [intros ok1; apply HEQ; exact (HAN ok1)|].
    split; [exact HLED|].
    split.
    { destruct HBLK as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [rewrite Hab; exact B2|].
      split; [rewrite Hfrs1; exact B3 | exact B4]. }
    (* the travelling position and live requests at the hand-off state: skip_ws made no event and kept the state *)
    split; [exact HPOSB2|]. split; [exact HLIVE2|].
    split; [rewrite (blocks_bytes_bsum B ly2 S2), Hab, <- (blocks_bytes_bsum B lyc Sc); exact HBB|].
    split; [exact HOK|]. split; [exact HLS|].
    split; [exact (Hrk (proj1 HROOM))|].
    (* the class-24 live count at the hand-off state (pik_cc24): pi_live there, the run split at the key's rest
       (pik_after_name, pik_inner2's run equation) and pi_ent's class-24 peak *)
    split; [exact (pik_cc24 d (rest_atR tb text p) ok0 tr0 (pik_after_name f (Nat.succ d) n cap (rev acc) nm (Z.to_nat kk) y)
      S S2 HEQ HOK HLIVE2 Epk2)|].
    (* THE BATCH KIT'S TAIL: the granted prefix, the capacity, and the decided free list (no colon: the completed slots'
       order list, then the arrays) *)
    split; [exact HGR|]. split; [exact Hcapn|].
    exists af. split; [rewrite MEQx; exact HFORD2|].
    intros ok1. rewrite (HFLA ok1). exact (HAF ok1). }
unfold SRr', cfg_at.
(* the runner carrying the overlay's normality from the run's start memory to its end (YC1fPx's _inv twin) *)
pose (RUN := paj_run_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fxc) (L := Lb) (PI := PIb) (wle' SEGS YGcfRehidePost.RZ_cf)).
(* the runs below take the rebased journal HJ2; every hand-off steps back to WS0 (HWD) *)
assert (Hwq2 : forall a, q <= a < q + 8 -> writable_at SEGS (mrestrict (w_H W2) mem2) a) by (intros a Ha; apply Hrw2; lia).
destruct (Z_lt_dec p1 (text + len)) as [Hlt | Hge].
- (* THE CURSOR IS ON A BYTE c *)
  set (c := nth (Z.to_nat (p1 - text)) tb 0).
  destruct (HG2 (Z.to_nat (p1 - text)) ltac:(lia)) as [Vc0 Hc256].
  replace (text + Z.of_nat (Z.to_nat (p1 - text))) with p1 in Vc0 by lia.
  pose proof (pik1_st_ok fxc W2 mem2 regs2 q p1 (text + len) c true (PIATb PIK_O_SKW2R) R9 R8 R20 R26 R27 R25 R23 R18
    Hqb Hq8 ltac:(lia) ltac:(lia) Hc256 ltac:(intros _; lia) Vp2 Ve2 (fun _ => Vc0)) as HS.
  remember (Eimg (PI := PIb) (Ereg regs2 [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 c])) as E eqn:HE in HS.
  assert (HEI : img_env VALb A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs2 rk).
  { intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
    rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ nk rk Hk). }
  assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (EK 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EK 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 p1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 c) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x)).
  { intros x Hx. rewrite denot_lit_U, U_SOff, E9, unsigned_lit_small, zcanon_id by (unfold M64; lia). reflexivity. }
  assert (SHOK : sh_ok SEGS pik_Bx1 (pik1_SH true) E (mrestrict (w_H W2) mem2)).
  { unfold pik1_SH. cbn [app]. constructor; [|constructor; [|constructor]].
    - apply (shent_ok_of_range SEGS (w_H W2) mem2 E pik_Bx1 32 text len p1 0 1 Htra2);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 32 p1 E32) by lia; reflexivity | lia | lia
      | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; unfold SHADOW_OFF; lia].
    - apply (shent_ok_of_range SEGS (w_H W2) mem2 E pik_Bx1 9 q 24 q 0 24 HRA2);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  clear HE.
  change (w64 (VALb A_TEXT + PIATb PIK_O_SKW2R)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_SKW2R)).
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN BAND_SPAN.
  { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ1 : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) mem2).
  { apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
    unfold pik1_ss in Hin; cbn [ss_mem] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
  clear HF HFr HG.
  (* 0x87c9c bgeu p1, end: the cursor is on a byte, so the branch to PI_O_FREE is not taken *)
  psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
  { exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec p1 (text + len)); [discriminate Hc | lia]. }
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN BAND_SPAN.
  { unfold pik1_ss; cbn [ss_mem add_cond]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (ms2 := msx) in * end.
  assert (MEQ2 : mrestrict (w_H W2) (ms_mem ms2) = mrestrict (w_H W2) mem2).
  { rewrite <- MEQ1. apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
    unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
  clear HF HFr HG Hc.
  rewrite (pik_rest_cons tb text p1) in HSK by lia. fold c in HSK.
  (* 0x87cbc bne c, 58 *)
  psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
  { (* TAKEN: no colon after the key: jr_name frees the key and refuses; pi_free_spec at PI_O_FREE *)
    assert (Hc58 : c <> 58).
    { intros Ec. rewrite branch_ne_U, U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
      rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). rewrite Ec in Hc. vm_compute in Hc.
      discriminate Hc. }
    paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN BAND_SPAN (PIATb PI_O_FREE).
    { unfold pik1_ss; cbn [ss_mem add_cond]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
    lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (ms3 := msx) in * end.
    assert (MEQ3 : mrestrict (w_H W2) (ms_mem ms3) = mrestrict (w_H W2) mem2).
    { rewrite <- MEQ2. apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
      unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
    assert (KSx : forall r : Z, acallee_saved r -> getr (ms_regs ms3) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
    { intros r Hr. unfold acallee_saved in Hr.
      assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms3 _ HS);
      lazymatch goal with |- context [sv_denot ?E' (sr_get ?l ?r)] =>
        let x := eval vm_compute in (sr_get l r) in change (sr_get l r) with x;
        replace (sv_denot E' x) with (sv_denot E x) by (cbn [sv_denot ew ewset extK Nat.eqb]; reflexivity) end;
      first
      [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity
      | rewrite D9 by lia; symmetry; first [exact R8 | exact R20]
      | etransitivity; [exact (pi_denot_shx E (SOff 9 8) SHADOW_OFF (q + 8) (D9 8 ltac:(lia)) E26 ltac:(lia)
          ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R23]
      | etransitivity; [exact (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26 ltac:(lia)
          ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R25]
      | etransitivity; [exact (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26
          ltac:(lia) ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R27]
      | symmetry; exact R18 ]. }
    assert (HAN : forall ok1, pik_after_name f (Nat.succ d) n cap (rev acc) nm (Z.to_nat kk) y ok1 =
      (None, [EFree (Z.to_nat kk)], ok1)).
    { intros ok1. unfold pik_after_name. rewrite HSK. rewrite (proj2 (Z.eqb_neq c 58) Hc58). reflexivity. }
    assert (HAF : forall ok1, pik_fl_after f (Nat.succ d) n cap af lk y ok1 = af ++ PresetReqAt.arrz true cap).
    { intros ok1. unfold pik_fl_after. rewrite HSK. rewrite (proj2 (Z.eqb_neq c 58) Hc58). reflexivity. }
    clearbody ms3. pmkst HS.
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
      replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_FREE)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
    exact (FREE _ _ _ _
      (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD)
      HMN MEQ3 KSx HAN HAF). }
  (* 0x87cbc NOT TAKEN: a colon *)
  assert (Hc58 : c = 58).
  { rewrite branch_ne_U, U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.eqb_spec c 58) as [Ec | Ec]; [exact Ec|]. exfalso.
    change (U (ewset (ewset E 512 w) 513 w0) (SLit 58)) with 58 in Hc.
    rewrite (proj2 (Z.eqb_neq c 58) Ec) in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN BAND_SPAN.
  { unfold pik1_ss; cbn [ss_mem add_cond]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  (* 0x87cd0 addi a0, a0, 1; 0x87cd4 sd a0, 0(s1): the cursor's p word, writable *)
  lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (ms3 := msx) in * end.
  assert (MEQ3 : mrestrict (w_H W2) (ms_mem ms3) = mrestrict (w_H W2) mem2).
  { rewrite <- MEQ2. apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
    unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
  assert (R10a : getr (ms_regs ms3) 10 = w64 (p1 + 1)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms3 _ HS).
    lazymatch goal with |- context [sv_denot ?E' (sr_get ?l ?r)] =>
      let x := eval vm_compute in (sr_get l r) in change (sr_get l r) with x;
      replace (sv_denot E' x) with (sv_denot E x) by (cbn [sv_denot ew ewset extK Nat.eqb]; reflexivity) end.
    rewrite denot_lit_U, U_SOff, U32, zcanon_id by (unfold M64; lia). reflexivity. }
  assert (KS3 : forall r : Z, acallee_saved r -> getr (ms_regs ms3) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms3 _ HS);
    lazymatch goal with |- context [sv_denot ?E' (sr_get ?l ?r)] =>
      let x := eval vm_compute in (sr_get l r) in change (sr_get l r) with x;
      replace (sv_denot E' x) with (sv_denot E x) by (cbn [sv_denot ew ewset extK Nat.eqb]; reflexivity) end;
    first
    [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity
    | rewrite D9 by lia; symmetry; first [exact R8 | exact R20]
    | etransitivity; [exact (pi_denot_shx E (SOff 9 8) SHADOW_OFF (q + 8) (D9 8 ltac:(lia)) E26 ltac:(lia)
        ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R23]
    | etransitivity; [exact (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26 ltac:(lia)
        ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R25]
    | etransitivity; [exact (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26
        ltac:(lia) ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R27]
    | symmetry; exact R18 ]. }
  assert (R9x : getr (ms_regs ms3) 9 = w64 q)
    by (etransitivity; [exact (KS3 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
  assert (R8x : getr (ms_regs ms3) 8 = w64 (q + 16))
    by (etransitivity; [exact (KS3 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
  assert (R20x : getr (ms_regs ms3) 20 = w64 (q + 8))
    by (etransitivity; [exact (KS3 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
  assert (R26x : getr (ms_regs ms3) 26 = w64 SHADOW_OFF)
    by (etransitivity; [exact (KS3 26 ltac:(unfold acallee_saved; lia)) | exact R26]).
  assert (R27x : getr (ms_regs ms3) 27 = w64 (pi_sh q))
    by (etransitivity; [exact (KS3 27 ltac:(unfold acallee_saved; lia)) | exact R27]).
  assert (R25x : getr (ms_regs ms3) 25 = w64 (pi_sh (q + 16)))
    by (etransitivity; [exact (KS3 25 ltac:(unfold acallee_saved; lia)) | exact R25]).
  assert (R23x : getr (ms_regs ms3) 23 = w64 (pi_sh (q + 8)))
    by (etransitivity; [exact (KS3 23 ltac:(unfold acallee_saved; lia)) | exact R23]).
  assert (R18x : getr (ms_regs ms3) 18 = w64 1)
    by (etransitivity; [exact (KS3 18 ltac:(unfold acallee_saved; lia)) | exact R18]).
  assert (Vp3 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) q 8 p1) by (rewrite MEQ3; exact Vp2).
  assert (Ve3 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (q + 8) 8 (text + len)) by (rewrite MEQ3; exact Ve2).
  assert (Vc3 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) p1 1 c) by (rewrite MEQ3; exact Vc0).
  assert (Hwq3 : forall a, q <= a < q + 8 -> writable_at SEGS (mrestrict (w_H W2) (ms_mem ms3)) a)
    by (intros a Ha; rewrite MEQ3; exact (Hwq2 a Ha)).
  pose proof (pik5_st_ok fxc W2 (ms_mem ms3) (ms_regs ms3) q p1 (text + len) c true (PIATb PIK_O_PP) R9x R8x R20x R26x
    R27x R25x R23x R18x Hqb Hq8 ltac:(lia) ltac:(lia) Hc256 ltac:(intros _; lia) Vp3 Ve3 (fun _ => Vc3) Hwq3) as HS5.
  remember (Eimg (PI := PIb) (Ereg (ms_regs ms3) [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 c]))
    as E5 eqn:HE5 in HS5.
  assert (HEI5 : img_env VALb A_LIM E5) by (rewrite HE5; apply Eimg_env).
  assert (EK5 : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E5 nk = getr (ms_regs ms3) rk).
  { intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
    rewrite HE5, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat (ms_regs ms3) _ nk rk Hk). }
  assert (E9b : ew E5 9 = Z_to_bv 64 q) by (rewrite (EK5 9%nat 9%bv eq_refl); exact R9x).
  assert (E26b : ew E5 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EK5 26%nat 26%bv eq_refl); exact R26x).
  assert (E32b : ew E5 32 = Z_to_bv 64 p1)
    by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
  assert (E33b : ew E5 33 = Z_to_bv 64 (text + len))
    by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
  assert (U32b : bv_unsigned (ew E5 32) = p1) by (rewrite E32b; apply unsigned_lit_small; lia).
  assert (U9b : bv_unsigned (ew E5 9) = q) by (rewrite E9b; apply unsigned_lit_small; lia).
  assert (SHOK5 : sh_ok SEGS pik_Bx1 (pik1_SH true) E5 (mrestrict (w_H W2) (ms_mem ms3))).
  { unfold pik1_SH. cbn [app]. constructor; [|constructor; [|constructor]].
    - assert (Htra3 : range_addressable (aview SEGS (w_H W2) (ms_mem ms3)) SHADOW_OFF text len)
        by (unfold range_addressable, aview; rewrite MEQ3; exact Htra2).
      apply (shent_ok_of_range SEGS (w_H W2) (ms_mem ms3) E5 pik_Bx1 32 text len p1 0 1 Htra3);
      [unfold pik_Bx1; rewrite (U_atom E5 26 SHADOW_OFF E26b) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E5 32 p1 E32b) by lia; reflexivity | lia | lia
      | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; unfold SHADOW_OFF; lia].
    - assert (HRA3 : range_addressable (aview SEGS (w_H W2) (ms_mem ms3)) SHADOW_OFF q 24)
        by (unfold range_addressable, aview; rewrite MEQ3; exact HRA2).
      apply (shent_ok_of_range SEGS (w_H W2) (ms_mem ms3) E5 pik_Bx1 9 q 24 q 0 24 HRA3);
      [unfold pik_Bx1; rewrite (U_atom E5 26 SHADOW_OFF E26b) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E5 9 q E9b) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  clear HE5 HF HFr HG.
  clearbody ms3. pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_PP)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  paj_run_tok_x_inv RUN HS5 HJ2 SHOK5 HMN BAND_SPAN.
  { unfold pik5_ss; cbn [ss_mem]; unfold pik5_smem; cbn [app].
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact U9b | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left.
    pose proof (pik_zmaxl_nonneg [STK_RT_ECALL; STK_RT_STRTOD; STK_fuzz_malloc; STK_fuzz_free; STK_literal;
      STK_parse_string; STK_grow; STK_skip_ws]) as HZ. pose proof (PIK_FR0 F_parse_value) as HF2.
    pose proof (PIK_FR0 F_parse_items) as HF3. pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)) as HN4.
    assert (HM : 0 <= Z.of_nat (PjGrammar.MAXD - d) * (PRH_Base.pi_frame F_parse_value + PRH_Base.pi_frame F_parse_items))
      by nia.
    unfold STK_parse_items, LEAF_pv_pi. rewrite PIK_FR. unfold PI_FRAME in *. lia. }
  (* the cursor's p word now holds p1 + 1 *)
  lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (msw := msx) in * end.
  assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
    mrestrict (w_H W2) (ms_mem msw) (Z_to_bv 64 a) = mrestrict (w_H W2) (ms_mem ms3) (Z_to_bv 64 a)).
  { intros a Ha Hn. apply HFr. intros (r & Hin & Hra). rewrite unsigned_lit_small in Hra by lia.
    unfold pik5_ss in Hin; cbn [ss_mem] in Hin; unfold pik5_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hra; [lia|].
    rewrite U9b in Hra. lia. }
  pose proof (pi_region_nth _ _ _ _ _ 1 _ HS5 eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  assert (D10 : sv_denot E5 (SOff 10 0) = Z_to_bv 64 (p1 + 1)).
  { rewrite denot_lit_U, U_SOff, Z.add_0_r, (EK5 10%nat 10%bv eq_refl), R10a, unsigned_lit_small, zcanon_id
      by (unfold M64; lia). reflexivity. }
  pose proof (pi_field SEGS _ _ 9%nat q _ _ _ _ _ 0 8 (SOff 10 0) (p1 + 1) RG1 U9b ltac:(left; reflexivity)
    D10 ltac:(cbn; lia) ltac:(zside)) as VS4. rewrite Z.add_0_r in VS4.
  assert (KS4 : forall r : Z, acallee_saved r -> getr (ms_regs msw) (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ msw _ HS5);
    lazymatch goal with |- context [sv_denot ?E' (sr_get ?l ?r)] =>
      let x := eval vm_compute in (sr_get l r) in change (sr_get l r) with x;
      replace (sv_denot E' x) with (sv_denot E5 x) by (cbn [sv_denot ew ewset extK Nat.eqb]; reflexivity) end;
    first
    [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK5; reflexivity
    | rewrite (denot_lit_U E5 (SOff 9 8)), U_SOff, U9b, zcanon_id by (unfold M64; lia); symmetry; exact R20x
    | rewrite (denot_lit_U E5 (SOff 9 16)), U_SOff, U9b, zcanon_id by (unfold M64; lia); symmetry; exact R8x
    | etransitivity; [exact (pi_denot_shx E5 (SOff 9 8) SHADOW_OFF (q + 8)
        ltac:(rewrite denot_lit_U, U_SOff, U9b, zcanon_id by (unfold M64; lia); reflexivity) E26b ltac:(lia)
        ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R23x]
    | etransitivity; [exact (pi_denot_shx E5 (SOff 9 16) SHADOW_OFF (q + 16)
        ltac:(rewrite denot_lit_U, U_SOff, U9b, zcanon_id by (unfold M64; lia); reflexivity) E26b ltac:(lia)
        ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R25x]
    | etransitivity; [exact (pi_denot_shx E5 (SOff 9 0) SHADOW_OFF q
        ltac:(rewrite denot_lit_U, U_SOff, U9b, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity) E26b
        ltac:(lia) ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R27x]
    | symmetry; exact R18x ]. }
  assert (KK4 : forall r : Z, acallee_saved r -> getr (ms_regs msw) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. etransitivity; [exact (KS4 r Hr)|]. etransitivity; [exact (KS3 r Hr) | exact (HKS r Hr)]. }
  assert (R2v : getr (ms_regs msw) 2 = getr regs 2) by exact (KK4 2 ltac:(unfold acallee_saved; lia)).
  assert (Rspv : spZ (ms_regs msw) = spZ regs) by (unfold spZ; rewrite R2v; reflexivity).
  (* the window at the store's memory: outside q's word, the call's view *)
  assert (WINv : forall a, spZ regs <= a < spZ regs0 + e -> ~ (q <= a < q + 8) ->
    aview SEGS (w_H W2) (ms_mem msw) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn.
    assert (E1 : aview SEGS (w_H W2) (ms_mem msw) a = aview SEGS (w_H W2) (ms_mem ms3) a)
      by (unfold aview, mbyte; rewrite (MEQ4 a ltac:(lia) Hn); reflexivity).
    rewrite E1, (AVR _ _ _ a MEQ3), <- (AVR _ _ _ a MEQ). apply HX; [unfold PI_FRAME; lia|].
    intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia. }
  (* the cursor at the store's memory, one byte on *)
  assert (Hple3 : text <= p1 + 1 <= text + len) by lia.
  assert (Hlrp : (length (rest_atR tb text (p1 + 1)) <= length (rest_atR tb text p1))%nat)
    by (unfold rest_atR; rewrite !length_skipn; lia).
  assert (HCURv : pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 (ms_mem msw) (p1 + 1) Lamc
    peakc cntc failc ranc most own).
  { apply (pik_cur_qstore regs0 e q v text len tb d ly2 S2 Hp2 W2 (ms_mem ms3) (ms_mem msw) p1 (p1 + 1)
      Lamc peakc cntc failc ranc most own).
    - intros a k' Hin. pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG2) as HB2.
      pose proof (proj1 (Forall_forall _ _) HB2 (a, k') Hin) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
      destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 Hab2) as (_ & Ab4 & Abc & _). auto.
    - exact (pik_cur_rdeq regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 (ms_mem ms3) p1 Lamc peakc cntc failc ranc most own
        MEQ3 HCUR2).
    - exact MEQ4.
    - exact VS4.
    - intros a Ha. pose proof RG1 as (_ & _ & Hw & _). cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hw.
      rewrite U9b in Hw. replace a with (q + (a - q)) by lia. apply Hw. lia.
    - exact Hple3.
    - exact Hlrp.
    - lia.
    - lia.
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. clear - Hvam Hv4096. lia.
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. clear - Hvam Hv4096. lia. }
  (* the container, the key and the frame at the store's memory *)
  pose proof HRB as (B22 & B24 & BV0 & BV32 & BV24 & BV16 & BV8).
  assert (MQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
    mbyte SEGS (mrestrict (w_H W2) (ms_mem msw)) a = mbyte SEGS (mrestrict (w_H W2) mem2) a /\
    (writable_at SEGS (mrestrict (w_H W2) mem2) a -> writable_at SEGS (mrestrict (w_H W2) (ms_mem msw)) a)).
  { intros a Ha Hn. pose proof (pik_pt _ _ a (MEQ4 a Ha Hn)) as (E1 & E2).
    assert (E3 : mbyte SEGS (mrestrict (w_H W2) (ms_mem ms3)) a = mbyte SEGS (mrestrict (w_H W2) mem2) a)
      by (unfold mbyte; rewrite MEQ3; reflexivity).
    assert (E4 : writable_at SEGS (mrestrict (w_H W2) mem2) a -> writable_at SEGS (mrestrict (w_H W2) (ms_mem ms3)) a)
      by (unfold writable_at, wview; rewrite MEQ3; exact (fun H => H)).
    split; [rewrite E1; exact E3 | intros Hwr; exact (E2 (E4 Hwr))]. }
  assert (AGRv : pj_agreeR SEGS (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem msw))
    (pj_footR v (pi_sblk true kids keys cap ++ Di))).
  { intros x Hx.
    assert (HB : 0 <= x < 2 ^ 64 /\ ~ (q <= x < q + 8)).
    { destruct Hx as [Hx | ((a0 & k0) & Hb & Hh)].
      - split; [clear - Hvw Hspq Hqe Fsp' Hx Hv4096 Hvam C1 C2 C3 C4 C5;
          unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia
        | clear - Hvw Hspq Hqe Fsp' Hx; lia].
      - unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
        assert (Hl : In (a0, k0) Lamc) by (apply HINCL; apply in_or_app; destruct (in_app_or _ _ _ Hb) as [H' | H'];
          [left; exact H' | right; apply in_or_app; left; exact H']).
        pose proof (proj1 (Forall_forall _ _) HHBc (a0, k0) Hl) as (Hk0 & Hb0 & _ & _ & _). cbn [fst snd] in Hk0, Hb0.
        destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memr mdc _ _ HARm Hb0) as (_ & Bb4 & Bbc & _).
        assert (RSk : k0 + cf_head <= req_size (k0 + cf_head)) by (apply pik_req_ge; lia).
        split; [clear - Hh Hk0 Bb4 Bbc RSk CH0 ACL; lia | clear - Hh Hk0 Bb4 Bbc RSk CH0 Hq0; lia]. }
    exact (MQ2 x (proj1 HB) (proj2 HB)). }
  assert (HCONTv : pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H W2) (ms_mem msw)) (prh_lin Lamc) true v kids keys n cap
    acc Di) by exact (pi_cont_frame (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di HCONT2 AGRv).
  pose proof (pik_agree_ufoot _ _ v kids keys n cap Di ltac:(lia) AGRv) as AGUv.
  pose proof (pvm_ncaps_frame (w_H W2) mem2 (mrestrict (w_H W2) (ms_mem msw)) (prh_lin Lamc) true v kids keys n cap acc Di
    HCONT2 HNCAPS2 AGUv) as HNCAPSv.
  pose proof (pvm_forder_frame _ _ _ _ _ v _ _ _ _ _ _ HFORD2 (fun x k H => H) AGUv) as HFORDv.
  assert (HKEYv : pi_key (L := Lb) (PA := PIb) (mrestrict (w_H W2) (ms_mem msw)) (prh_lin Lamc) true keys n nm
    [(kx, kk)]).
  { unfold pi_key in HKEY2 |- *. destruct HKEY2 as (x & kx' & Ex & (Hx0 & Hx) & Hcs). exists x, kx'.
    injection Ex as <- <-. split; [reflexivity|].
    assert (HB1 : forall a0 k0, In (a0, k0) Lamc -> forall y0, a0 <= y0 < a0 + k0 ->
      mbyte SEGS (mrestrict (w_H W2) (ms_mem msw)) y0 = mbyte SEGS (mrestrict (w_H W2) mem2) y0 /\
      (writable_at SEGS (mrestrict (w_H W2) mem2) y0 -> writable_at SEGS (mrestrict (w_H W2) (ms_mem msw)) y0)).
    { intros a0 k0 Hl y0 Hy0. pose proof (proj1 (Forall_forall _ _) HHBc (a0, k0) Hl) as (Hk0 & Hb0 & _ & _ & _).
      cbn [fst snd] in Hk0, Hb0.
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memr mdc _ _ HARm Hb0) as (_ & Bb4 & Bbc & _).
      assert (RSk : k0 + cf_head <= req_size (k0 + cf_head)) by (apply pik_req_ge; lia). apply MQ2; lia. }
    split.
    - split; [exact Hx0|]. apply (pj_valR_frame SEGS _ _ _ _ _ Hx). intros y0 Hy0.
      apply (HB1 keys (8 * Z.of_nat cap) (HINCL _ ltac:(apply in_or_app; left; exact Hkin))).
      pose proof HCONT as (_ & _ & Hnc & _). lia.
    - apply (pj_cstrR_frame SEGS _ _ _ _ _ _ Hcs). intros y0 Hy0.
      apply (HB1 kx kk (HINCL _ ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity))). lia. }
  assert (HFRv : pi_frame (L := Lb) (PA := PIb) regs0 (ms_regs msw) W mem W2 (ms_mem msw) e q v).
  { apply (pik_frame_win regs0 regs (ms_regs msw) W mem Wc W2 memc (ms_mem msw) e q v HFRM Rspv
      (KK4 3 ltac:(unfold acallee_saved; lia)) (KK4 4 ltac:(unfold acallee_saved; lia)) Hspq WINv). }
  assert (VWv : forall a x, spZ regs <= a -> a + 8 <= spZ regs + 40 ->
    val_mem SEGS (mrestrict (w_H Wc) memc) a 8 x -> val_mem SEGS (mrestrict (w_H W2) (ms_mem msw)) a 8 x).
  { intros a x Ha1 Ha2 Hv. apply (pik_val_win Wc W2 memc (ms_mem msw) a 8 x); [|exact Hv].
    intros kk' Hk. apply WINv; lia. }
  (* ---- the fall to PI_O_VAL ---- *)
  clearbody msw. pmkst HS5.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_VAL)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  apply (HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p Lam peak cnt fail ran most own kr
    ly2 S2 Hp2 W2 (ms_mem msw) _ _ (ms_regs msw) WS0
    (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD) HWS).
  refine (conj HFP (conj HENT (conj HMN (conj HFRv (conj _ (conj _ (conj _ _))))))).
  + unfold pi_regs.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    * etransitivity; [exact (KK4 9 ltac:(unfold acallee_saved; lia)) | exact Q9].
    * etransitivity; [exact (KK4 19 ltac:(unfold acallee_saved; lia)) | exact Q19].
    * etransitivity; [exact (KK4 18 ltac:(unfold acallee_saved; lia)) | exact Q18].
    * etransitivity; [exact (KK4 8 ltac:(unfold acallee_saved; lia)) | exact Q8].
    * etransitivity; [exact (KK4 20 ltac:(unfold acallee_saved; lia)) | exact Q20].
    * etransitivity; [exact (KK4 26 ltac:(unfold acallee_saved; lia)) | exact Q26].
    * etransitivity; [exact (KK4 27 ltac:(unfold acallee_saved; lia)) | exact Q27].
    * etransitivity; [exact (KK4 25 ltac:(unfold acallee_saved; lia)) | exact Q25].
    * etransitivity; [exact (KK4 23 ltac:(unfold acallee_saved; lia)) | exact Q23].
  + unfold pi_regs_body. rewrite Rspv.
    split; [etransitivity; [exact (KK4 22 ltac:(unfold acallee_saved; lia)) | exact B22]|].
    split; [etransitivity; [exact (KK4 24 ltac:(unfold acallee_saved; lia)) | exact B24]|].
    split; [apply VWv; [lia | lia | exact BV0]|]. split; [apply VWv; [lia | lia | exact BV32]|].
    split; [apply VWv; [lia | lia | exact BV24]|]. split; [apply VWv; [lia | lia | exact BV16]|].
    apply VWv; [lia | lia | exact BV8].
  + etransitivity; [exact (KK4 21 ltac:(unfold acallee_saved; lia)) | exact H21].
  + exists f, n, cap, acc, kids, keys, Di, nm, [(kx, kk)], (p1 + 1), ok0, tr0, D0, Lamc, peakc, cntc, failc, ranc.
    assert (HAFT : forall ok1, pik_after_name f (Nat.succ d) n cap (rev acc) nm (Z.to_nat kk) y ok1 =
      pi_val_k f (Nat.succ d) true n cap (rev acc) nm (rest_atR tb text (p1 + 1)) ok1).
    { intros ok1. unfold pik_after_name. rewrite HSK, (proj2 (Z.eqb_eq c 58) Hc58). reflexivity. }
    split; [exact HCURv|].
    split; [rewrite Ey in HN; clear - HN HLe2; lia|].
    split; [exact Hncap|]. split; [exact HCONTv|]. split; [exact HDEP|]. split; [exact HAP|].
    split; [exact HKEYv|]. split; [exact HPERM|].
    split; [rewrite Ey in HFU; clear - HFU HLe2; lia|].
    split; [intros ok1 r0 t0 ok2 Hj; apply HEQ; rewrite HAFT; exact Hj|].
    split; [exact HLED|].
    split.
    { destruct HBLK as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [rewrite Hab; exact B2|].
      split; [rewrite Hfrs1; exact B3 | exact B4]. }
    (* the travelling position and live requests: skip_ws made no event and kept the state *)
    split; [exact HPOSB2|]. split; [exact HLIVE2|].
    split; [rewrite (blocks_bytes_bsum B ly2 S2), Hab, <- (blocks_bytes_bsum B lyc Sc); exact HBB|].
    split; [exact HOK|]. split; [exact HLS|].
    split.
    { unfold rd_room in HROOM |- *. rewrite (HAFT []) in HROOM.
      destruct HROOM as (RM1 & RM2 & RM3). split; [exact (Hrk RM1)|]. split; [exact RM2|].
      (* the live bytes per event: skip_ws kept the state (S2 = Sc) *)
      rewrite HSeq. exact RM3. }
    (* THE BATCH KIT'S TAIL at the value: the granted prefix, the capacities, the completed slots' free order and the model past
       the kept key (pi_jfv_k after the colon) *)
    split; [exact HGR|]. split; [exact Hcapn|]. split; [exact HNCAPSv|].
    exists af, lk. split; [exact HFORDv|]. split; [exact HLK|].
    intros ok1. rewrite (HFLA ok1). unfold pik_fl_after. rewrite HSK, (proj2 (Z.eqb_eq c 58) Hc58). reflexivity.
- (* THE CURSOR IS AT THE END: no colon after the key; pi_free_spec at PI_O_FREE *)
  assert (Ep1e : p1 = text + len) by lia.
  pose proof (pik1_st_ok fxc W2 mem2 regs2 q p1 (text + len) 0 false (PIATb PIK_O_SKW2R) R9 R8 R20 R26 R27 R25 R23 R18
    Hqb Hq8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros C; discriminate C) Vp2 Ve2 ltac:(intros C; discriminate C))
    as HS.
  remember (Eimg (PI := PIb) (Ereg regs2 [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 0])) as E eqn:HE in HS.
  assert (HEI : img_env VALb A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs2 rk).
  { intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
    rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ nk rk Hk). }
  assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (EK 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EK 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 p1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x)).
  { intros x Hx. rewrite denot_lit_U, U_SOff, E9, unsigned_lit_small, zcanon_id by (unfold M64; lia). reflexivity. }
  assert (SHOK : sh_ok SEGS pik_Bx1 (pik1_SH false) E (mrestrict (w_H W2) mem2)).
  { unfold pik1_SH. cbn [app]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W2) mem2 E pik_Bx1 9 q 24 q 0 24 HRA2);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  clear HE.
  change (w64 (VALb A_TEXT + PIATb PIK_O_SKW2R)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_SKW2R)).
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN BAND_SPAN.
  { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ1 : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) mem2).
  { apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
    unfold pik1_ss in Hin; cbn [ss_mem] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | []]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
  clear HF HFr HG.
  (* 0x87c9c bgeu p1, end: TAKEN, the cursor is at the end *)
  psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
  { paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN BAND_SPAN (PIATb PI_O_FREE).
    { unfold pik1_ss; cbn [ss_mem add_cond]; unfold pik1_smem; cbn [app];
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
    lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (ms3 := msx) in * end.
    assert (MEQ3 : mrestrict (w_H W2) (ms_mem ms3) = mrestrict (w_H W2) mem2).
    { rewrite <- MEQ1. apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
      unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
      destruct Hin as [<- | []]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
    assert (KSx : forall r : Z, acallee_saved r -> getr (ms_regs ms3) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
    { intros r Hr. unfold acallee_saved in Hr.
      assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms3 _ HS);
      lazymatch goal with |- context [sv_denot ?E' (sr_get ?l ?r)] =>
        let x := eval vm_compute in (sr_get l r) in change (sr_get l r) with x;
        replace (sv_denot E' x) with (sv_denot E x) by (cbn [sv_denot ew ewset extK Nat.eqb]; reflexivity) end;
      first
      [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity
      | rewrite D9 by lia; symmetry; first [exact R8 | exact R20]
      | etransitivity; [exact (pi_denot_shx E (SOff 9 8) SHADOW_OFF (q + 8) (D9 8 ltac:(lia)) E26 ltac:(lia)
          ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R23]
      | etransitivity; [exact (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26 ltac:(lia)
          ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R25]
      | etransitivity; [exact (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26
          ltac:(lia) ltac:(unfold SHADOW_OFF; lia)) | symmetry; exact R27]
      | symmetry; exact R18 ]. }
    assert (HAN : forall ok1, pik_after_name f (Nat.succ d) n cap (rev acc) nm (Z.to_nat kk) y ok1 =
      (None, [EFree (Z.to_nat kk)], ok1)).
    { intros ok1. unfold pik_after_name. rewrite HSK, Ep1e.
      replace len with (Z.of_nat (length tb)) by lia. rewrite pik_rest_end. reflexivity. }
    assert (HAF : forall ok1, pik_fl_after f (Nat.succ d) n cap af lk y ok1 = af ++ PresetReqAt.arrz true cap).
    { intros ok1. unfold pik_fl_after. rewrite HSK, Ep1e.
      replace len with (Z.of_nat (length tb)) by lia. rewrite pik_rest_end. reflexivity. }
    clearbody ms3. pmkst HS.
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
      replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_FREE)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
    exact (FREE _ _ _ _
      (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD)
      HMN MEQ3 KSx HAN HAF). }
  { (* 0x87c9c not taken: impossible, p1 = end *)
    exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec p1 (text + len)); [lia | discriminate Hc]. }
Qed.

(* ---- K4: from 0x87c7c, `mv a0, s1`, `jal skip_ws` (the second call, the kit's tskip_ws_specX at the caller window
   PI_FRAME + e), then K5 at the return site ---- *)
Lemma pik_k4_holds : forall d CTX0 CW N,
  pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pik_k4_spec d CTX0 CW N.
Proof.
intros d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc mdc k regs f n cap acc kids keys Di nm kx kk pc ok0 tr0 D0 Lamc peakc cntc failc ranc WS0
  HJw HWS HFP HENT HMN HFRM HREGS HRB H21 HI2.
unfold pi_ajR in HJw.
(* THE BUDGETED JOURNAL: the run and the skip_ws call (an empty-budget callee) take it rebased at this block's depot;
   the return state steps back to WS0 (skip_ws stores nothing) *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof HI2 as (HCUR & HN & Hncap & HCONT & HDEP & HAP & HKEY & HPERM & HKIN & HKNL & Hkk0 & HKNB & HFU & HEQ & HLED
  & HBLK & HPOSB & HLIVE & HBB & HOK & HLS & HROOM & _).
pose proof HENT as (Emn & _ & _ & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & _).
pose proof RDP as (_ & _ & _ & _ & _ & Hfwin & Hspq & Hqe & _ & _ & _ & _ & HPV & _ & _ & _ & _ & _).
pose proof HPV as (Hv4096 & Hv8 & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof (pik_stk_skw d) as HSTKB.
pose proof (PIK_FR0 F_skip_ws) as HSKW0.
unfold SRr', cfg_at.
remember (Eimg (PI := PIb) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env VALb A_LIM E0) by (subst E0; apply Eimg_env).
assert (E2 : ew E0 2 = getr regs 2) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E0 3 = getr regs 3) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E0 8 = getr regs 8) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E0 9 = getr regs 9) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (HS : st_ok_pi (fx := fxc) SEGS VALb E0
  (mkSS (PIATb PIK_O_SKW2) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxc regs (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_SKW2)) memc (seg_rom SEGS)))).
{ rewrite (restrict_mkst_fx (fx := fxc)). apply (pa_entry_st_ok_full (fx := fxc) (L := Lb) (PI := PIb)).
  - subst E0. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - cbn; exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E0 (mrestrict (w_H Wc) memc)) by constructor.
(* the runner carrying the overlay's normality from the run's start memory to its end (YC1fPx's _inv twin) *)
pose (RUN := paj_run_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
change (w64 (VALb A_TEXT + PIATb PIK_O_SKW2)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_SKW2)).
paj_run_tok_x_inv RUN HS HJ SHOK HMN BAND_SPAN.
{ apply awr_ok_nil. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
cbn [ss_mem] in HF, HFr.
assert (MEQ : mrestrict (w_H Wc) (ms_mem ms) = mrestrict (w_H Wc) memc).
{ apply functional_extensionality; intros x. apply HFr. intros (r & Hin & _). exact (in_nil Hin). }
clear HF HFr HG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
unfold STK_skip_ws, PI_FRAME in HSTKB.
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
assert (Hqb : 4096 <= q /\ q + 24 <= 2 ^ 47) by lia.
pose proof (pik_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc (ms_mem ms) pc Lamc peakc cntc failc ranc most own MEQ
  HCUR) as HCURm.
pose proof HCURm as (HINm & HRAm & HSRCm & _ & _ & _ & HLGm & _).
assert (Usp : spZ (ms_regs ms) = spZ regs) by (unfold spZ; rewrite R2, E2; reflexivity).
assert (Us0 : s0Z (ms_regs ms) = q + 16).
{ unfold s0Z. rewrite R8, E8, Q8. apply unsigned_lit_small. lia. }
assert (Ra0 : getr (ms_regs ms) 10 = w64 q) by (rewrite R10, E9; exact Q9).
(* the frame-pointer chain the call sees: s0 = q + 16, whose two words below are the end and the cursor (the
   cursor lies in the text, below alloc_ceiling and so below q, so the chain stops there) *)
assert (HCH : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ regs) (q + 16) ch1).
{ destruct (Z_lt_le_dec (q + 16) (ly_top lyc - 16)) as [Hlt | Hge].
  - exists [(q + 16, text + len, pc)]. right.
    split; [lia|]. split; [exact Hlt|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
    split.
    + cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
      split; [replace (q + 16 - 8) with (q + 8) by lia;
              apply (pik_rdword_of_val (w_H Wc) (ms_mem ms) (q + 8) (text + len)); [rewrite MEQ; exact Ve | lia]|].
      split; [replace (q + 16 - 16) with q by lia;
              apply (pik_rdword_of_val (w_H Wc) (ms_mem ms) q pc); [rewrite MEQ; exact Vp | lia]|].
      split; [lia|].
      unfold bad_next. replace (pc <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + constructor; [cbn [fst]; lia | constructor].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH as (ch1 & HCH).
(* skip_ws, an empty-budget callee, on the rebased journal (its start state is S at this block's depot), by the call
   rule over the walk's relation; its plain text lifted (pik_skw_lift) *)
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (aj_call_xW_spR (SK := SK) SEGS B prh_pst ARx LAWS (pa_segs_low (PAImg := PIb))
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    Wc E0 _ ms
    (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly _ Hp W mem md [] lyc Sc Hpc _ k
    STK_skip_ws (PI_FRAME + e) [(q, q + 8)] (- (PI_FRAME + e)) (Z_to_bv 64 (VALb A_TEXT + 26040)) ch1
    (fQmn (L := Lb) (PA := PIb) (ms_mem ms) (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf Sc -> room_live_cf S') /\ Hp' = Hpc /\ S' = Sc /\ ablocks B ly' S' = ablocks B lyc Sc /\
       prh_ledger (L := Lb) (PA := PIb) B ly' S' Hp' W' mem' Lamc peakc cntc failc ranc most own /\
       pj_in_okR SEGS (mrestrict (w_H W') mem') q text len
         (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text pc)))) (Z.of_nat d + 1) tb))
    HS eq_refl HJ).
  - rewrite Usp, Fsp. unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, He16 by lia; reflexivity].
  - unfold PI_FRAME. lia.
  - exact HSKW0.
  - unfold STK_skip_ws, PI_FRAME. lia.
  - unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.add_mod, He16 by lia; reflexivity.
  - lia.
  - rewrite R3, E3, F3. exact Egp.
  - rewrite R4, E4, F4. exact Etp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (pa_B_ok (PAImg := PIb)) as HB. pose proof (pa_val_range (PAImg := PIb) A_TEXT) as HBr.
    rewrite unsigned_lit_small by lia. vm_compute. discriminate.
  - replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) by (unfold PI_FRAME; lia). rewrite Us0. exact HCH.
  - intros HAF HWIN. cbn [ss_pc setpc].
    apply pik_skw_lift.
    refine (TSKW fxc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 (PI_FRAME + e) q text len pc (Z.of_nat d + 1) tb
      Lamc peakc cntc failc ranc most own _ _ _ _ _ _ _ _ _ _).
    + split; [exact HAF|]. split.
      { apply (pik_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact Erod].
        intros (r & Hr & H0). cbn [rd_fp In] in Hr.
        destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia. }
      pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
      split; [rewrite Usp; lia|].
      (* fpre's frm_zero at the call (FRM0-ENTRY): the block's own float state, pi_fpok's first half *)
      split; [|exact (proj1 HFP)].
      (* the jal's own return pc, a literal of the listing, is below the allocation ceiling (fpre's fourth conjunct,
         the kit owner's 2026-10-29 ruling; PItems_entry.v:1485-1489's discharge) *)
      unfold raZ. rewrite R1.
      pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CRr. unfold ASAN_CEIL in CRr.
      let w := eval vm_compute in (VALb A_TEXT) in change (VALb A_TEXT) with w.
      rewrite unsigned_lit_small by lia. lia.
    + exact Ra0.
    + exact HINm.
    + exact HWIN.
    + rewrite Usp. lia.
    + rewrite Usp, Fsp. unfold PI_FRAME. lia.
    + exact HRAm.
    + exact HSRCm.
    + exact HHOME.
    + exact HLGm.
  - intros a (r & Hr & Ha). left. exists r. split; [|exact Ha].
    destruct Hr as [<- | []]. left. reflexivity. }
(* back at the return site: the callee-saved registers are the call's, which are the block's own *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HP &
  (Hrk & HHp & HSeq & Hab & Hled2 & Hin2) & HMNk).
pose proof (HMNk HMN) as HMN2. clear HMNk.
assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E0 nk = getr regs rk).
{ intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] nk rk Hk). }
assert (HKS : aregs_preserved regs regs2).
{ intros r Hr. rewrite (HP r Hr). unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  rewrite (st_ok_restrict_reg SEGS (w_H Wc) E0 _ ms _ HS);
  lazymatch goal with |- context [sr_get ?l ?r] => let x := eval vm_compute in (sr_get l r) in
    change (sr_get l r) with x end;
  cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity. }
replace (Z_to_bv 64 (VALb A_TEXT + 26040)) with (w64 (VALb A_TEXT + PIATb PIK_O_SKW2R))
  by (unfold w64; f_equal; vm_compute; reflexivity).
replace (spZ regs0 + e + - (PI_FRAME + e) + (PI_FRAME + e)) with (spZ regs + (PI_FRAME + e)) in HJ1
  by (unfold PI_FRAME; lia).
apply (pik_k5_holds d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt
  fail ran most own kr lyc Sc Hpc Wc memc (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc) k regs f n cap acc kids
  keys Di nm kx kk pc ok0 tr0 D0 Lamc peakc cntc failc ranc
  ly2 S2 Hp2 W2 mem2 md2 k1 regs2 WS0 HFP HENT HMN2 HSeq HFRM HREGS HRB H21 HI2).
- exact MEQ.
- exact HARc.
- exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD).
- exact HWS.
- exact HJ1.
- intros a Ha Hn. apply HX; [unfold PI_FRAME in *; lia | exact Hn].
- exact HKS.
- exact Hrk.
- exact HHp.
- exact Hab.
- exact Hled2.
- exact Hin2.
Qed.

(* ---- K3N: parse_string's block arm after the store and the NULL test: the key read, the string's allocation added to
   the prefix, every datum moved to the store's memory, then K4 at 0x87c7c ---- *)
Lemma pik_k3n_holds : forall d CTX0 CW N,
  pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pik_k3n_spec d CTX0 CW N.
Proof.
intros d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc memr mdc k regs f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc
  ly2 S2 Hp2 W2 mem2 md2 k1 regs2 memx' mdx' kx' regs' WS0 WS1
  HFP HENT HMN HFRM HREGS HRB H21 HIN Hpcl Hq34 MEQ HARm HJ2 HWS HJ1 HX HKS HPOST HJx MQ VS HKSx H0.
pose proof HIN as (HCUR & HN & Hncap & HCONT & HDEP & HAP & HPERM & HFU & HEQ & HLED & HBLK & HPOSB & HLIVE & HBB & HOK
  & HLS & HROOM & HGR & Hcapn & HNCAPS & af & HFORD & HFLB).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HENT as (Emn & _ & _ & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & _).
pose proof RDP as (_ & _ & _ & _ & _ & Hfwin & Hspq & Hqe & _ & _ & _ & _ & HPV & Hqv & Htv & Hvw & _ & HdM & _).
pose proof HPV as (Hv4096 & Hv8 & _ & _ & _ & Hvam & HNOWN & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HRB as (B22 & B24 & BV0 & BV32 & BV24 & BV16 & BV8).
pose proof HCUR as (HIN0 & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN0 as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof HCONT as (HHDR & Hnacc & Hnc & Hcap54 & Hslots & Hko & HNDi & HAPDi & HMEMS).
pose proof HHDR as (Hrwv & HTy & HNum & HStr & HKd & HKy & HNn & HCp).
pose proof (prh_ledger_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HND.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HHB.
pose proof HJ2 as (HAR2 & HLY2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo2 & Eshi2 & _).
pose proof HJ1 as (HAR1 & HLY1 & _ & _ & _ & HFRS1 & _). cbn [app] in HFRS1.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
pose proof (pik_stk_str d) as HSTKB. unfold PI_FRAME in HSTKB. pose proof (PIK_FR0 F_parse_string) as HPS0.
assert (HPSN : 0 <= STK_parse_string).
{ unfold STK_parse_string. pose proof (pik_zmaxl_nonneg [STK_fuzz_free; STK_fuzz_malloc; STK_hex4; STK_put_utf8]).
  lia. }
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
assert (RS : forall z, 0 <= z -> z <= req_size z) by (intros z Hz; unfold req_size; destruct (Z.eqb_spec z 0); lia).
(* the keys block: a harness block of the call ledger, new since the entry *)
destruct Hslots as [(Hc0 & _ & _) | (Hcp & Hkids & Hkeys)]; [lia|].
specialize (Hkeys eq_refl). unfold prh_lin in Hkids, Hkeys.
pose proof (proj1 (Forall_forall _ _) HHB _ Hkeys) as (K0 & Kin & Khp & K16 & Kv). cbn [fst snd] in K0, Kin, Khp, K16, Kv.
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memr mdc _ _ HARm Kin) as (KB16 & KB4096 & KBc & KBapp & _).
assert (RSk : 8 * Z.of_nat cap + cf_head <= req_size (8 * Z.of_nat cap + cf_head)) by (apply RS; lia).
assert (Hkin : In (keys, 8 * Z.of_nat cap) (pi_sblk true kids keys cap)).
{ unfold pi_sblk, kids_blkR, keys_blkR. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn. right. left. reflexivity. }
pose proof HW as HW8. unfold prh_head_wide in HW8.
(* the disjunctions and alignments this block does not use: lia would split on them *)
clear Ecur Hqv Htv Hdqt Hq8 Hv8 He16 K16 KB16 Hd032.
(* ---- parse_string's block arm ---- *)
destruct HPOST as (res & R10 & HRL2 & HHU2 & HBB2 & HARM).
unfold tpstP_ANone, tpstP_ASome1, tpstP_ASome2, tpstP_ASome3, tpstP_ASome4 in HARM.
assert (HU0 : getr regs2 10 = w64 0 -> False).
{ intros E. apply H0. rewrite E. unfold w64. apply unsigned_lit_small. lia. }
destruct (PjGrammar.scan (rest_atR tb text (pc + 1))) as [Q|] eqn:HSC;
  [| destruct HARM as (-> & _); exfalso; exact (HU0 R10)].
destruct HARM as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) |
  (Hcf & Hr4 & Hr16 & sn & r' & HDC & EH & EA & HVIS & HCB & HLG2 & HIN2 & HPM2 & HPI2)]]];
  [exfalso; exact (HU0 R10) | exfalso; exact (HU0 R10) | exfalso; exact (HU0 R10) |].
(* the new block and the key string's facts *)
assert (HNB2 : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S2))
  by (rewrite EA; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 HNB2) as (NB16 & NB4096 & NBc & NBapp & _).
clear Hr16 NB16.
assert (RSq : Z.of_nat Q + 1 + cf_head <= req_size (Z.of_nat Q + 1 + cf_head)) by (apply RS; lia).
assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
assert (VSr : val_mem SEGS (mrestrict (w_H W2) memx') (keys + 8 * Z.of_nat n) 8 res).
{ rewrite R10 in VS. unfold w64 in VS. rewrite unsigned_lit_small in VS by lia. exact VS. }
destruct (PjGrammar.G1_4 _ _ _ HDC) as (q' & Hq' & Hr' & Hsn & H0s). rewrite HSC in Hq'. injection Hq' as <-.
set (z := rest_atR tb text (pc + 1)) in *.
assert (Hy : rest_atR tb text pc = 34 :: z).
{ unfold z. rewrite (pik_rest_cons tb text pc) by lia. f_equal. apply nth_error_nth. exact Hq34. }
assert (HSg : jr_string z [] = (Some (sn, r'), [EAlloc (Nat.succ Q)], [])).
{ unfold jr_string. rewrite HSC. unfold jbind, jalloc. cbn [PjGrammar.take]. rewrite HDC. reflexivity. }
pose proof (PjGrammar.jr_string_spec z []) as HSP. rewrite HSg in HSP.
destruct HSP as (q2 & Hq2 & _ & _ & HLz). rewrite HSC in Hq2. injection Hq2 as <-.
set (pc2 := pc + Z.of_nat Q + 2).
assert (Hpc2 : rest_atR tb text pc2 = r').
{ rewrite Hr'. unfold z, pc2, rest_atR. rewrite skipn_skipn. f_equal. lia. }
assert (HLy : length (rest_atR tb text pc) = Nat.succ (length z)) by (rewrite Hy; reflexivity).
assert (HLr : (length (rest_atR tb text pc2) + Nat.succ Q = length z)%nat) by (rewrite Hpc2; exact HLz).
assert (Epc2 : pc2 = pc + Z.of_nat Q + 2) by reflexivity. clearbody pc2 z.
(* the new block is none of the call state's: the allocator's blocks are pairwise apart *)
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 HNB2) as (_ & _ & _ & _ & _ & HPW).
rewrite EA, map_app in HPW. cbn [map] in HPW.
assert (HNBold : ~ In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B lyc Sc)).
{ intros Hin. apply (pik_pairwise_last _ _ HPW); [cbn [fst snd]; lia|].
  apply in_map_iff. exists (res - cf_head, Z.of_nat Q + 1 + cf_head). split; [reflexivity | exact Hin]. }
assert (HNBap : forall b m, In (b, m) (ablocks B lyc Sc) ->
  b + req_size m <= res - cf_head \/ res - cf_head + req_size (Z.of_nat Q + 1 + cf_head) <= b).
{ intros b m Hin. pose proof (pik_pairwise_last_disj _ _ _ HPW (in_map (fun b0 => (fst b0, req_size (snd b0))) _ _ Hin)) as HZ.
  unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia. }
set (Lam2' := (res, Z.of_nat Q + 1) :: Lamc).
set (peak2' := Z.max peakc (Ledger.lsum Lamc + (Z.of_nat Q + 1))).
(* ---- pi_cur at the return (Lam2': the string's block added), then at the store's memory ---- *)
assert (HBK : forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2))
  by (intros b Hb; rewrite EA; apply in_or_app; left; exact Hb).
pose proof (pik_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc memr pc Lamc peakc cntc failc ranc most own MEQ HCUR)
  as HCURr.
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
assert (HKMr : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF q 24 /\ src_rd W2 mem2 text tb /\
  prhReader_home B ly2 S2 Hp2 Lam2' text len /\ prhReader_at B ly2 S2 Lam2' regs0 e v 56 /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56).
{ apply (HKM (wle' SEGS YGcfRehidePost.RZ_cf) regs0 e q v text len tb d lyc Sc Hpc Wc memr mdc pc Lamc peakc cntc
    failc ranc most own
    STK_parse_string (spZ regs) (PI_FRAME + e) [(q, q + 8)] [] ly2 S2 Hp2 W2 mem2 md2 k1 Lam2' peak2' (cntc + 1) failc ranc
    most own WS1
    HCURr HJ1 HX).
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - lia.
  - destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | Hro] | (b & m & Hbin & _ & Hb1 & Hb2)].
    + right; right. pose proof (proj1 (Forall_forall _ _) HHB _ Hbin) as (KK0 & KKin & _). cbn [fst snd] in KK0, KKin.
      exists (b - cf_head), (m + cf_head). split; [exact KKin | lia].
    + destruct Hro as [Hro | Hki]; [left; exact Hro | right; left; exact Hki].
    + right; right. exists b, m. auto.
  - intros b m Hbin Hrng. split; [exact (HBK _ Hbin)|]. rewrite EH.
    split; [intros Hb; right; exact Hb|]. intros [Eb | Hb]; [|exact Hb]. exfalso.
    assert (Rm : 0 < req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    assert (Rn : 0 < req_size (Z.of_nat Q + 1 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
    destruct (HNBap b m Hbin) as [Hd | Hd]; lia.
  - intros a0 Ha (r0 & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - intros a0 Ha (r0 & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    assert (Ha47 : 0 <= a0 < 2 ^ 47) by (clear - Ha Htc Ht0 ACL; lia).
    pose proof (pik_shadow_low a0 Ha47) as HSl. pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR'.
    unfold ASAN_CEIL in CR'. clear - Hra HSl Hq0 CR'. lia.
  - intros a0 Ha (r0 & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    assert (Ha47 : 0 <= a0 < 2 ^ 47)
      by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; clear - Hvam Ha Hv4096; lia).
    pose proof (pik_shadow_low a0 Ha47) as HSl. pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR'.
    unfold ASAN_CEIL in CR'. clear - Hra HSl Hq0 CR'. lia.
  - intros (r0 & Hr & H0'). destruct Hr as [<- | []]. cbn [fst snd] in H0'. lia.
  - exact HLG2.
  - left. reflexivity.
  - intros a0 k' Hk' _. right. exact Hk'.
  - lia.
  - lia.
  - intros a0 k' [E | Hk']; [right; injection E as <- <-; exact HNBold | left; exact Hk'].
  - exact HARm. }
destruct HKMr as (RAq2 & SRC2 & HOME2 & AT2 & RAv2).
assert (HLe : (length (rest_atR tb text pc2) + 2 <= length (rest_atR tb text pc))%nat).
{ rewrite HLy, <- HLr, <- Nat.add_succ_r. apply Nat.add_le_mono_l. apply le_n_S. apply le_n_S. apply Nat.le_0_l. }
assert (HCNT2 : cntc + 1 + 2 * Z.of_nat (length (rest_atR tb text pc2)) + 2 < 2 ^ 64 - 1).
{ apply Nat2Z.inj_le in HLe. rewrite Nat2Z.inj_add in HLe. lia. }
assert (HCUR2 : pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 pc2 Lam2' peak2' (cntc + 1)
  failc ranc most own).
{ refine (conj _ (conj RAq2 (conj SRC2 (conj HOME2 (conj AT2 (conj RAv2 (conj HLG2 HCNT2))))))).
  rewrite Epc2. exact HIN2. }
(* the whole call's granted run through the key: the string's allocation, then pik_after_name *)
destruct (pik_after_name f (Nat.succ d) n cap (rev acc) sn (Nat.succ Q) r' []) as [[rg tg] okg] eqn:EG.
assert (HJG : pi_jrb f (Nat.succ d) true n cap (rev acc) (rest_atR tb text pc) [true] = (rg, EAlloc (Nat.succ Q) :: tg, okg)).
{ rewrite Hy. exact (pik_jrb_str_some f (Nat.succ d) n cap (rev acc) z Q sn r' [true] [] HSC HDC eq_refl rg tg okg EG). }
pose proof (HEQ [true] rg (EAlloc (Nat.succ Q) :: tg) okg HJG) as HJR.
pose proof (pvm_wf_items d true (rest_atR tb text p) (ok0 ++ [true])) as HWF. rewrite HJR in HWF.
assert (HW0 : pvm_wf tr0) by (unfold pvm_wf in HWF |- *; exact (proj1 (proj1 (pvm_wf_from_app [] tr0 _) HWF))).
pose proof RDP as (_ & _ & _ & _ & HIN00 & _ & _ & _ & _ & _ & HHOME0 & _ & _ & _ & _ & _ & HLG0 & _ & HCNT0 & _).
pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HLG0) as (_ & _ & GC0 & GF0 & _).
pose proof HIN00 as (_ & _ & _ & _ & _ & _ & _ & Hp0 & Hlen0 & _).
assert (Hx0 : rest_atR tb text p <> []).
{ unfold rest_atR. intros E. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn [length] in E. lia. }
assert (HCLB : (PjGrammar.calls (tr0 ++ EAlloc (Nat.succ Q) :: tg) <= 2 * length (rest_atR tb text p))%nat).
{ destruct (rest_atR tb text p) as [|b0 y0] eqn:Ex; [exfalso; exact (Hx0 eq_refl)|].
  pose proof (PjGrammar.G7_4_items prh_jr_strtod d true b0 y0 (ok0 ++ [true])) as HB. rewrite HJR in HB.
  cbn [fst snd] in HB. exact HB. }
rewrite calls_app in HCLB. cbn [PjGrammar.calls PjGrammar.is_call] in HCLB.
pose proof (pvm_hpeak_items d true (rest_atR tb text p) (ok0 ++ [true]) rg (tr0 ++ EAlloc (Nat.succ Q) :: tg) okg Hx0 HJR)
  as HPKg.
pose proof (pvm_hpeak_prefix (tr0 ++ [EAlloc (Nat.succ Q)]) tg) as HPKp. rewrite <- app_assoc in HPKp.
cbn [app] in HPKp.
(* the string's ledger move, and the prefix's extended by it *)
pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as (GLP & GP & GC & GF & GR).
assert (HSM : rd_ledger_move Lamc peakc cntc failc ranc most [true] [EAlloc (Nat.succ Q)] [EAlloc (Nat.succ Q)]
  [(res, Z.of_nat Q + 1)] Lam2' peak2' (cntc + 1) failc ranc).
{ unfold rd_ledger_move, prh_oks, fail_afterR. cbn [PjGrammar.calls PjGrammar.is_call].
  split; [split; [intros i Hi Hf; destruct i; [lia | lia] | split; [left; reflexivity|]]|].
  { intros i Hi Hn' Hne. destruct i; [|lia]. unfold prh_refused in Hn'. cbn [nth negb andb] in Hn'. discriminate Hn'. }
  split; [rewrite Z.mod_small by lia; lia|].
  split; [split; [intros Hn'; exfalso; lia | intros _; reflexivity]|].
  split; [apply Permutation_refl|].
  split; [unfold lszR; cbn [fold_left lsz_evR map snd]; rewrite Nat2Z.inj_succ; apply Permutation_refl|].
  split; [cbn [nliveR nlive_evR length]; reflexivity|].
  unfold peak2', prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth negb andb hpeakR held_ev].
  rewrite ?Nat2Z.inj_succ. lia. }
(* the prefix is granted (pi_grant), and the string's malloc granted: the whole prefix move over its own trace *)
assert (HGNT : prh_granted ok0 cnt fail (PjGrammar.calls tr0)) by (rewrite HGR; apply PItems_ledk1.pik1_grant_granted).
assert (HLED2 : rd_ledger_move Lam peak cnt fail ran most (ok0 ++ [true]) (tr0 ++ [EAlloc (Nat.succ Q)])
  (tr0 ++ [EAlloc (Nat.succ Q)]) ([(res, Z.of_nat Q + 1)] ++ D0) Lam2' peak2' (cntc + 1) failc ranc).
{ pose proof (pvm_ledger_app Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc [true] [EAlloc (Nat.succ Q)]
    [EAlloc (Nat.succ Q)] [(res, Z.of_nat Q + 1)] Lam2' peak2' (cntc + 1) failc ranc [] HW0 I HOK) as G.
  rewrite app_nil_r in G.
  apply G; [lia | unfold SIZE_MAXZ; cbn; lia | lia | exact HGNT | lia | exact HLED | exact HSM]. }
(* the prefix's blocks moved by the string's allocation *)
pose proof HBLK as (BNEW & BPERM & BFR & BPK).
assert (HBMs : rd_blocks_move B lyc Sc ly2 S2 [(res, Z.of_nat Q + 1)] [EAlloc (Nat.succ Q)] (rest_atR tb text pc)
  (Nat.succ d)).
{ split; [intros a k' [E | []]; injection E as <- <-; exact HNBold|].
  split; [rewrite EA; cbn [prhReader_ab map fst snd]; apply Permutation_app_comm|].
  split; [rewrite HFRS1; apply Permutation_refl|].
  cbn [hpeakR held_ev]. rewrite HLy. apply pik_hpeak1. rewrite <- HLz. apply Nat.le_add_l. }
assert (HBM2 : rd_blocks_move B ly S ly2 S2 ([(res, Z.of_nat Q + 1)] ++ D0) (tr0 ++ [EAlloc (Nat.succ Q)])
  (rest_atR tb text p) d).
{ eapply pvm_blocks_move_app; [exact HBLK | exact HBMs | lia]. }
assert (HGT : PRH_Charge.prhPs_gtrace z = [EAlloc (Nat.succ Q)])
  by (unfold PRH_Charge.prhPs_gtrace; rewrite HSg; reflexivity).
rewrite HGT in HBB2.
assert (HBB3 : blocks_bytes S2 <= blocks_bytes S + PRH_Charge.prh_held (tr0 ++ [EAlloc (Nat.succ Q)]))
  by (rewrite pvm_prh_held_app; lia).
assert (HOK2 : length (ok0 ++ [true]) = PjGrammar.calls (tr0 ++ [EAlloc (Nat.succ Q)]))
  by (rewrite length_app, calls_app, HOK; reflexivity).
assert (HLS2 : Ledger.lsum ([(res, Z.of_nat Q + 1)] ++ D0) = PjGrammar.held (tr0 ++ [EAlloc (Nat.succ Q)])).
{ rewrite pvm_lsum_app, held_app, <- HLS. cbn [Ledger.lsum PjGrammar.held held_ev]. rewrite Nat2Z.inj_succ. lia. }
(* the room of the rest: the granted run is the string's allocation, then pik_after_name *)
assert (HJG0 : pi_jrb f (Nat.succ d) true n cap (rev acc) (rest_atR tb text pc) [] =
  (rg, EAlloc (Nat.succ Q) :: tg, okg)).
{ rewrite Hy. exact (pik_jrb_str_some f (Nat.succ d) n cap (rev acc) z Q sn r' [] [] HSC HDC eq_refl rg tg okg EG). }
rewrite HJG0 in HROOM. cbn [fst snd] in HROOM.
assert (HROOM2 : rd_room S2 tg).
{ pose proof HROOM as (_ & RQk & RLk). split; [exact HRL2|]. split.
  - unfold PRH_Charge.prh_maxreq in RQk |- *. cbn [map fold_right PjGrammar.esize] in RQk.
    rewrite ?Nat2Z.inj_succ in RQk. clear - RQk. lia.
  - (* the live bytes per event after the string's malloc: the call state's, moved by its one event (HPM2) *)
    assert (EV1 : PresetReqAt.rd_hevs [EAlloc (Nat.succ Q)] = prhPs_evs z [true]).
    { rewrite (prhPs_evs_arm z [true] [] (or_intror eq_refl)). exact (pik_ps_evs_of _ _ _ _ _ HSg). }
    change (EAlloc (Nat.succ Q) :: tg) with ([EAlloc (Nat.succ Q)] ++ tg) in RLk.
    rewrite PresetReqAt.rd_hevs_app in RLk.
    apply (PItems_ledk1.pik1_live_evs_after Sc S2 _ _ RLk). rewrite EV1. exact HPM2. }
(* the store's memory: the key slot is apart from everything pi_cur reads *)
assert (HKB2 : In (keys - cf_head, 8 * Z.of_nat cap + cf_head) (ablocks B ly2 S2)) by exact (HBK _ Kin).
assert (HNEW : ~ In (keys - cf_head, 8 * Z.of_nat cap + cf_head) (ablocks B ly S)).
{ apply (BNEW keys (8 * Z.of_nat cap)). apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left.
  exact Hkin. }
pose proof HBM2 as (_ & BPERM2 & _ & _).
assert (HTXS : forall x, text <= x < text + len -> ~ (keys + 8 * Z.of_nat n <= x < keys + 8 * Z.of_nat n + 8)).
{ intros x Hx Hs. apply (pik_home_apart ly S Hp W mem Lam peak cnt fail ran most own ly2 S2 Hp2 W2 mem2 md2
    ([(res, Z.of_nat Q + 1)] ++ D0) text len (keys - cf_head) (8 * Z.of_nat cap + cf_head) HAR1 HLG0 BPERM2 HKB2 HNEW
    HHOME0 x Hx). lia. }
assert (HCURx : pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 memx' pc2 Lam2' peak2' (cntc + 1)
  failc ranc most own).
{ apply (pik_cur_slot regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 memx' md2 pc2 Lam2' peak2' (cntc + 1) failc ranc most own
    (keys - cf_head) (8 * Z.of_nat cap + cf_head) (keys + 8 * Z.of_nat n) HAR1 HCUR2 HKB2).
  - lia.
  - lia.
  - exact HTXS.
  - lia.
  - lia.
  - lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. lia.
  - exact MQ. }
(* ---- the container at the store's memory (as the NULL arm), over the larger ledger ---- *)
pose proof (pik_ledger_rdeq lyc Sc Hpc Wc memc memr Lamc peakc cntc failc ranc most own MEQ HLG) as HLGr.
assert (HLB : forall a k', In (a, k') Lamc -> 0 <= k' /\ 4096 <= a - cf_head /\
  a - cf_head + req_size (k' + cf_head) <= YM05.alloc_ceiling /\ In (a - cf_head, k' + cf_head) (ablocks B lyc Sc)).
{ intros a k' Hin. pose proof (proj1 (Forall_forall _ _) HHB (a, k') Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memr mdc _ _ HARm Hab) as (_ & H4 & Hc & _). auto. }
assert (MQP : forall x, 0 <= x < 2 ^ 64 -> ~ (keys + 8 * Z.of_nat n <= x < keys + 8 * Z.of_nat n + 8) ->
  mbyte SEGS (mrestrict (w_H W2) memx') x = mbyte SEGS (mrestrict (w_H W2) mem2) x /\
  (writable_at SEGS (mrestrict (w_H W2) mem2) x -> writable_at SEGS (mrestrict (w_H W2) memx') x))
  by (intros x Hx Hn'; exact (pik_pt _ _ x (MQ x Hx Hn'))).
pose proof HND as HNDf.
assert (HNDD : NoDup (pi_sblk true kids keys cap ++ Di)).
{ apply NoDup_ListNoDup. apply NoDup_ListNoDup in HNDf. pose proof HLED as (_ & _ & _ & L4 & _).
  assert (HN1 : List.NoDup (map fst (D0 ++ Lam))) by (apply (Permutation_NoDup (Permutation_map fst L4)); exact HNDf).
  rewrite map_app in HN1. apply List.NoDup_app_remove_r in HN1. apply (List.NoDup_map_inv fst) in HN1.
  exact (Permutation_NoDup HPERM HN1). }
assert (HINCL : incl (pi_sblk true kids keys cap ++ Di) Lamc).
{ intros b Hb. pose proof HLED as (_ & _ & _ & L4 & _). apply (Permutation_in b (Permutation_sym L4)).
  apply in_or_app. left. exact (Permutation_in b (Permutation_sym HPERM) Hb). }
assert (AGRD : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2)
  (pj_footR v (pi_sblk true kids keys cap ++ Di))).
{ rewrite <- MEQ.
  apply (pik_agree_call regs0 e v lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own STK_parse_string (spZ regs)
    (PI_FRAME + e) [(q, q + 8)] ly2 S2 Hp2 W2 mem2 md2 k1 (pi_sblk true kids keys cap ++ Di) WS1).
  - exact HLGr.
  - exact HPLAT.
  - exact Hvw.
  - lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. lia.
  - exact HJ1.
  - exact HX.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - intros a Ha (r0 & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - exact HBK.
  - exact HINCL.
  - intros a ((a0 & k0) & Hb & Hab0) (r0 & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    unfold pj_holdsR in Hab0. cbn [fst snd] in Hab0. destruct (HLB a0 k0 (HINCL _ Hb)) as (Hk0 & H4 & Hc & _).
    assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia). lia. }
pose proof (pi_cont_frame (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di HCONT AGRD) as HC2.
assert (Hkk : kids <> keys).
{ intros Ek. apply NoDup_ListNoDup in HND. rewrite Ek in Hkids.
  pose proof (pik_nodup_fst _ _ _ _ HND Hkids Hkeys) as E56. lia. }
assert (HCONTx : pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H W2) memx') (prh_lin Lamc) true v kids keys n cap acc Di).
{ apply (pi_cont_frame_slot_gen (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di
    (keys + 8 * Z.of_nat n) (keys + 8 * Z.of_nat n + 8) HC2).
  - intros x Hx. split; [left; lia|]. split.
    + destruct (HLB kids (56 * Z.of_nat cap) Hkids) as (Hk0 & H4 & Hc & _).
      assert (RSa : 56 * Z.of_nat cap + cf_head <= req_size (56 * Z.of_nat cap + cf_head)) by (apply RS; lia).
      destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap) keys
        (8 * Z.of_nat cap) HARm HLGr Hkids Hkeys Hkk); lia.
    + split.
      * intros (a0 & k0) Hb Hh. unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
        assert (Hl : In (a0, k0) Lamc) by (apply HINCL; apply in_or_app; right; exact Hb).
        destruct (HLB a0 k0 Hl) as (Hk0 & H4 & Hc & _).
        assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia).
        destruct (Z.eq_dec a0 keys) as [-> | Hne].
        -- apply NoDup_ListNoDup in HND. pose proof (pik_nodup_fst _ _ _ _ HND Hl Hkeys) as E8. subst k0.
           apply NoDup_ListNoDup in HNDD. exact (pik_nodup_app_disj _ _ _ HNDD Hkin Hb).
        -- destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own a0 k0 keys (8 * Z.of_nat cap)
             HARm HLGr Hl Hkeys Hne); lia.
      * intros Hv. exact (HAP _ x Hkin ltac:(unfold pj_holdsR; cbn [fst snd]; lia) Hv).
  - intros x (Hf & Hns). apply MQP; [|exact Hns].
    destruct Hf as [Hx | ((a0 & k0) & Hb & Hh)].
    + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. clear - Hvam Hx Hv4096. lia.
    + unfold pj_holdsR in Hh. cbn [fst snd] in Hh. destruct (HLB a0 k0 (HINCL _ Hb)) as (Hk0 & H4 & Hc & _).
      assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia). lia. }
assert (HCONTx2 : pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H W2) memx') (prh_lin Lam2') true v kids keys n cap acc Di)
  by exact (pik_cont_lblk _ _ _ true v kids keys n cap acc Di HCONTx HNDD HAP (fun a k' H => or_intror H)).
(* ---- The batch kit's invariants at the store's memory: the completed slots' capacities and free order are read through the
   bytes pi_cont reads, which parse_string kept (AGRD) and the store left (the key slot n is none of them) ---- *)
assert (AGS : pj_agreeR SEGS (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memx') (pvm_cont_ufoot true v kids keys n Di)).
{ intros x Hx.
  assert (Hf : pj_footR v (pi_sblk true kids keys cap ++ Di) x)
    by exact (pvm_ufoot_foot true v kids keys n cap Di x ltac:(lia) Hx).
  assert (Hns : ~ (keys + 8 * Z.of_nat n <= x < keys + 8 * Z.of_nat n + 8)).
  { intros Hs. destruct Hx as [Hx | [(i & Hi & Hx) | [(_ & i & Hi & Hx) | (b & Hb & Hx)]]].
    - exact (HAP _ x Hkin ltac:(unfold pj_holdsR; cbn [fst snd]; lia) Hx).
    - destruct (HLB kids (56 * Z.of_nat cap) Hkids) as (Hk0 & H4 & Hc & _).
      assert (RSa : 56 * Z.of_nat cap + cf_head <= req_size (56 * Z.of_nat cap + cf_head)) by (apply RS; lia).
      destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap) keys
        (8 * Z.of_nat cap) HARm HLGr Hkids Hkeys Hkk); lia.
    - lia.
    - destruct b as (a0 & k0). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      assert (Hl : In (a0, k0) Lamc) by (apply HINCL; apply in_or_app; right; exact Hb).
      destruct (HLB a0 k0 Hl) as (Hk0 & H4 & Hc & _).
      assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia).
      destruct (Z.eq_dec a0 keys) as [-> | Hne].
      + apply NoDup_ListNoDup in HND. pose proof (pik_nodup_fst _ _ _ _ HND Hl Hkeys) as E8. subst k0.
        apply NoDup_ListNoDup in HNDD. exact (pik_nodup_app_disj _ _ _ HNDD Hkin Hb).
      + destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own a0 k0 keys (8 * Z.of_nat cap)
          HARm HLGr Hl Hkeys Hne); lia. }
  apply MQP; [|exact Hns].
  destruct Hf as [Hx' | ((a0 & k0) & Hb & Hh)].
  + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. clear - Hvam Hx' Hv4096. lia.
  + unfold pj_holdsR in Hh. cbn [fst snd] in Hh. destruct (HLB a0 k0 (HINCL _ Hb)) as (Hk0 & H4 & Hc & _).
    assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia). lia. }
pose proof (pik_agree_ufoot _ _ v kids keys n cap Di ltac:(lia) AGRD) as AGU.
pose proof (pvm_ncaps_frame (w_H Wc) memc (mrestrict (w_H W2) mem2) (prh_lin Lamc) true v kids keys n cap acc Di
  HCONT HNCAPS AGU) as HNCAPS2.
pose proof (pvm_ncaps_frame (w_H W2) mem2 (mrestrict (w_H W2) memx') (prh_lin Lamc) true v kids keys n cap acc Di
  HC2 HNCAPS2 AGS) as HNCAPSx.
pose proof (pvm_forder_frame _ _ _ _ _ v _ _ _ _ _ _ HFORD (fun x k H => H) AGU) as HFORD2.
pose proof (pvm_forder_frame _ _ (prh_lin Lamc) (prh_lin Lam2') _ v _ _ _ _ _ _ HFORD2 (fun x k H => or_intror H) AGS)
  as HFORDx.
(* the string is shorter than 2 ^ 32 - 1 (pj_cstrR's bound, PRH_Reader.v 2026-10-29): its block is ONE allocation of
   the member's granted run, and the room bound keeps every request under cf_malloc_max *)
assert (HQ32 : Z.of_nat Q + 1 < 2 ^ 32).
{ pose proof HROOM as (_ & RM32 & _).
  unfold PRH_Charge.prh_maxreq in RM32. cbn [map fold_right PjGrammar.esize] in RM32.
  pose proof (@cf_head_nonneg cp) as CH32. pose proof YG08cf.cf_malloc_max_bound as MMB.
  rewrite ?Nat2Z.inj_succ in RM32. clear - RM32 CH32 MMB. lia. }
(* ---- the key read: its slot holds the string's block, and the string at the store's memory ---- *)
assert (HKEY : pi_key (L := Lb) (PA := PIb) (mrestrict (w_H W2) memx') (prh_lin Lam2') true keys n sn
  [(res, Z.of_nat Q + 1)]).
{ unfold pi_key. exists res, (Z.of_nat Q + 1). split; [reflexivity|]. split; [split; [lia | exact VSr]|].
  pose proof HCB as (HCc & HCg). split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HCc|].
  apply (garr8R_frame SEGS _ _ _ _ HCg). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  destruct (HNBap _ _ Kin) as [Hd | Hd]; (apply MQP; [lia | lia]). }
(* ---- the registers and the frame at the store's memory ---- *)
assert (KK : forall r : Z, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by (intros r Hr; etransitivity; [exact (HKSx r Hr) | exact (HKS r Hr)]).
assert (R2x : getr regs' 2 = getr regs 2) by exact (KK 2 ltac:(unfold acallee_saved; lia)).
assert (Rsp' : spZ regs' = spZ regs) by (unfold spZ; rewrite R2x; reflexivity).
assert (AVR : forall (H : word -> bool) m m' a, mrestrict H m' = mrestrict H m -> aview SEGS H m' a = aview SEGS H m a)
  by (intros H m m' a Em; unfold aview; rewrite Em; reflexivity).
assert (HWIN : forall a, spZ regs <= a < spZ regs0 + e -> ~ (q <= a < q + 8) ->
  aview SEGS (w_H W2) memx' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn'.
  assert (E1 : aview SEGS (w_H W2) memx' a = aview SEGS (w_H W2) mem2 a).
  { unfold aview. rewrite (proj1 (MQP a ltac:(lia) ltac:(lia))). reflexivity. }
  rewrite E1, <- (AVR _ _ _ a MEQ). apply HX; [unfold PI_FRAME; lia|].
  intros (r0 & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia. }
assert (HFRx : pi_frame (L := Lb) (PA := PIb) regs0 regs' W mem W2 memx' e q v).
{ apply (pik_frame_win regs0 regs regs' W mem Wc W2 memc memx' e q v HFRM Rsp'
    (KK 3 ltac:(unfold acallee_saved; lia)) (KK 4 ltac:(unfold acallee_saved; lia)) Hspq HWIN). }
assert (HREGSx : pi_regs regs' q v true).
{ unfold pi_regs.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - etransitivity; [exact (KK 9 ltac:(unfold acallee_saved; lia)) | exact Q9].
  - etransitivity; [exact (KK 19 ltac:(unfold acallee_saved; lia)) | exact Q19].
  - etransitivity; [exact (KK 18 ltac:(unfold acallee_saved; lia)) | exact Q18].
  - etransitivity; [exact (KK 8 ltac:(unfold acallee_saved; lia)) | exact Q8].
  - etransitivity; [exact (KK 20 ltac:(unfold acallee_saved; lia)) | exact Q20].
  - etransitivity; [exact (KK 26 ltac:(unfold acallee_saved; lia)) | exact Q26].
  - etransitivity; [exact (KK 27 ltac:(unfold acallee_saved; lia)) | exact Q27].
  - etransitivity; [exact (KK 25 ltac:(unfold acallee_saved; lia)) | exact Q25].
  - etransitivity; [exact (KK 23 ltac:(unfold acallee_saved; lia)) | exact Q23]. }
assert (VWx : forall a x, spZ regs <= a -> a + 8 <= spZ regs + 40 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a 8 x -> val_mem SEGS (mrestrict (w_H W2) memx') a 8 x).
{ intros a x Ha1 Ha2 Hv. apply (pik_val_win Wc W2 memc memx' a 8 x); [|exact Hv].
  intros kk Hk. apply HWIN; lia. }
assert (HRBx : pi_regs_body (L := Lb) (PA := PIb) regs' W2 memx' v).
{ unfold pi_regs_body. rewrite Rsp'.
  split; [etransitivity; [exact (KK 22 ltac:(unfold acallee_saved; lia)) | exact B22]|].
  split; [etransitivity; [exact (KK 24 ltac:(unfold acallee_saved; lia)) | exact B24]|].
  split; [apply VWx; [lia | lia | exact BV0]|]. split; [apply VWx; [lia | lia | exact BV32]|].
  split; [apply VWx; [lia | lia | exact BV24]|]. split; [apply VWx; [lia | lia | exact BV16]|].
  apply VWx; [lia | lia | exact BV8]. }
assert (R21x : getr regs' 21 = w64 (-1)) by (etransitivity; [exact (KK 21 ltac:(unfold acallee_saved; lia)) | exact H21]).
(* the travelling position and live requests after the string's block: parse_string's arm post (its position
   implication and live requests over prhPs_evs .. [true], which is rd_hevs [EAlloc (S Q)] by prhPs_evs_model at
   PIK_HEAD) composed on the block's own over tr0 (PItems_posb.pi_posb_call / pi_live_call); its hull use over its
   all-granted list, which on this arm is the same list (prhPs_evs_arm) *)
assert (EVs : PresetReqAt.rd_hevs [EAlloc (Nat.succ Q)] = prhPs_evs z [true]).
{ rewrite (prhPs_evs_arm z [true] [] (or_intror eq_refl)). exact (pik_ps_evs_of _ _ _ _ _ HSg). }
assert (HHU3 : PresetHullBudget.hull_used Sc S2 (PresetReqAt.rd_hevs [EAlloc (Nat.succ Q)])).
{ rewrite EVs, (prhPs_evs_arm z [true] [] (or_intror eq_refl)). exact HHU2. }
rewrite <- EVs in HPM2, HPI2.
pose proof (PItems_posb.pi_posb_call S Sc S2 tr0 [EAlloc (Nat.succ Q)] HPOSB HPI2 HHU3) as HPOSB2.
pose proof (PItems_posb.pi_live_call _ _ _ tr0 [EAlloc (Nat.succ Q)] HLIVE HPM2) as HLIVE2.
(* ---- K4 ---- *)
apply (pik_k4_holds d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail
  ran most own kr ly2 S2 Hp2 W2 memx' mdx' kx' regs' f n cap acc kids keys Di sn res (Z.of_nat Q + 1) pc2 (ok0 ++ [true])
  (tr0 ++ [EAlloc (Nat.succ Q)]) ([(res, Z.of_nat Q + 1)] ++ D0) Lam2' peak2' (cntc + 1) failc ranc WS0
  HJx HWS HFP HENT HMN HFRx HREGSx HRBx R21x).
assert (EQk : Z.to_nat (Z.of_nat Q + 1) = Nat.succ Q)
  by (rewrite Z2Nat.inj_add, Nat2Z.id by lia; rewrite Nat.add_1_r; reflexivity).
refine (conj HCURx (conj _ (conj Hncap (conj HCONTx2 (conj HDEP (conj HAP (conj HKEY (conj _ (conj _ (conj _
  (conj _ (conj _ (conj _ (conj _ (conj HLED2 (conj HBM2 (conj HPOSB2 (conj HLIVE2 (conj HBB3 (conj HOK2
  (conj HLS2 _))))))))))))))))))))).
- clear - HN HLe. lia.
- eapply perm_trans; [apply Permutation_app_comm|]. rewrite app_assoc. apply Permutation_app_tail. exact HPERM.
- left. reflexivity.
- intros Hin. pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG0) as HB0. pose proof (proj1 (Forall_forall _ _) HB0 _ Hin) as (_ & Hab0 & _).
  cbn [fst snd] in Hab0. apply HNBold. apply (Permutation_in _ (Permutation_sym BPERM)). apply in_or_app. right.
  exact Hab0.
- lia.
- intros (b & m & Hin & Hb1 & Hb2).
  assert (Hin' : In (b, m) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym BPERM)); apply in_or_app; right; exact Hin).
  assert (Hm0 : 0 <= m \/ m < 0) by lia. destruct Hm0 as [Hm0 | Hm0]; [|lia].
  pose proof (RS m Hm0). destruct (HNBap b m Hin') as [Hd | Hd]; lia.
- clear - HFU HLe. lia.
- intros ok1 r0 t0 ok2 Hj. rewrite EQk, Hpc2 in Hj.
  assert (HJB : pi_jrb f (Nat.succ d) true n cap (rev acc) (rest_atR tb text pc) (true :: ok1) =
    (r0, EAlloc (Nat.succ Q) :: t0, ok2)).
  { rewrite Hy. exact (pik_jrb_str_some f (Nat.succ d) n cap (rev acc) z Q sn r' (true :: ok1) ok1 HSC HDC eq_refl
      r0 t0 ok2 Hj). }
  pose proof (HEQ (true :: ok1) r0 (EAlloc (Nat.succ Q) :: t0) ok2 HJB) as HJ'.
  rewrite <- !app_assoc. exact HJ'.
- split; [rewrite EQk, Hpc2, EG; exact HROOM2|].
  (* THE BATCH KIT'S TAIL after the key: the string's malloc granted, the capacities and the completed slots' free order
     carried, and the model past the kept key (pi_jfb's colon arms) *)
  split; [unfold pi_grant in HGR |- *; rewrite HGR, calls_app, repeat_app; reflexivity|].
  split; [exact Hcapn|]. split; [exact HNCAPSx|].
  exists af, (PresetReqAt.lf [EAlloc (Nat.succ Q)]).
  split; [exact HFORDx|].
  split; [intros Hh; rewrite Hh; cbn [map snd PresetReqAt.lf]; rewrite ?Nat2Z.inj_succ; f_equal; lia|].
  intros ok1. rewrite <- app_assoc. cbn [app]. rewrite (HFLB (true :: ok1)), Hy, Hpc2.
  exact (pik_jfb_str_some f (Nat.succ d) n cap af z Q sn r' ok1 HSC HDC).
Qed.

(* ---- K3: from parse_string's return (0x87c10): the K3 core, then K3N after the NULL test ---- *)
Lemma pik_k3_holds : forall d CTX0 CW N,
  pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pik_k3_spec d CTX0 CW N.
Proof.
intros d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc memr mdc k regs f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc
  ly2 S2 Hp2 W2 mem2 md2 k1 regs2 WS0 WS1
  HFP HENT HMN HFRM HREGS HRB H21 HIN Hpcl Hq34 MEQ HARm HJ2 HWS HJ1 HX HKS HPOST.
pose proof HIN as (HCUR & HN & Hncap & HCONT & HDEP & HAP & HPERM & HFU & HEQ & HLED & HBLK & HPOSB & HLIVE & HBB & HOK
  & HLS & HROOM & HGR & Hcapn & HNCAPS & af & HFORD & HFLB).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HENT as (Emn & _ & _ & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & _).
pose proof RDP as (_ & _ & _ & _ & _ & Hfwin & Hspq & Hqe & _ & _ & _ & _ & HPV & Hqv & Htv & Hvw & _ & HdM & _).
pose proof HPV as (Hv4096 & Hv8 & _ & _ & _ & Hvam & HNOWN & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HRB as (B22 & B24 & BV0 & BV32 & BV24 & BV16 & BV8).
pose proof HCUR as (HIN0 & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN0 as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof HCONT as (HHDR & Hnacc & Hnc & Hcap54 & Hslots & Hko & HNDi & HAPDi & HMEMS).
pose proof HHDR as (Hrwv & HTy & HNum & HStr & HKd & HKy & HNn & HCp).
pose proof (prh_ledger_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HND.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HHB.
pose proof HJ2 as (HAR2 & HLY2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo2 & Eshi2 & _).
pose proof HJ1 as (HAR1 & HLY1 & _ & _ & _ & HFRS1 & _). cbn [app] in HFRS1.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
pose proof (pik_stk_str d) as HSTKB. unfold PI_FRAME in HSTKB. pose proof (PIK_FR0 F_parse_string) as HPS0.
assert (HPSN : 0 <= STK_parse_string).
{ unfold STK_parse_string. pose proof (pik_zmaxl_nonneg [STK_fuzz_free; STK_fuzz_malloc; STK_hex4; STK_put_utf8]).
  lia. }
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
assert (RS : forall z, 0 <= z -> z <= req_size z) by (intros z Hz; unfold req_size; destruct (Z.eqb_spec z 0); lia).
(* the keys block: a harness block of the call ledger, new since the entry *)
destruct Hslots as [(Hc0 & _ & _) | (Hcp & Hkids & Hkeys)]; [lia|].
specialize (Hkeys eq_refl). unfold prh_lin in Hkids, Hkeys.
pose proof (proj1 (Forall_forall _ _) HHB _ Hkeys) as (K0 & Kin & Khp & K16 & Kv). cbn [fst snd] in K0, Kin, Khp, K16, Kv.
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memr mdc _ _ HARm Kin) as (KB16 & KB4096 & KBc & KBapp & _).
assert (RSk : 8 * Z.of_nat cap + cf_head <= req_size (8 * Z.of_nat cap + cf_head)) by (apply RS; lia).
assert (Hkin : In (keys, 8 * Z.of_nat cap) (pi_sblk true kids keys cap)).
{ unfold pi_sblk, kids_blkR, keys_blkR. replace (Z.of_nat cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn. right. left. reflexivity. }
(* what parse_string keeps, in every arm of its post *)
assert (HBK : forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)).
{ intros b Hb. destruct HPOST as (res & _ & _ & _ & _ & HARM).
  unfold tpstP_ANone, tpstP_ASome1, tpstP_ASome2, tpstP_ASome3, tpstP_ASome4 in HARM.
  destruct (PjGrammar.scan (rest_atR tb text (pc + 1))) as [Q|].
  - destruct HARM as [(_ & _ & _ & EA & _) | [(_ & _ & _ & EA & _) | [(_ & _ & _ & _ & EA & _) |
      (_ & _ & _ & s & r & _ & _ & EA & _)]]]; rewrite EA; [exact Hb | exact Hb | exact Hb |].
    apply in_or_app. left. exact Hb.
  - destruct HARM as (_ & _ & EA & _). rewrite EA. exact Hb. }
assert (HHPK : In (keys - cf_head) Hp2).
{ destruct HPOST as (res & _ & _ & _ & _ & HARM).
  unfold tpstP_ANone, tpstP_ASome1, tpstP_ASome2, tpstP_ASome3, tpstP_ASome4 in HARM.
  destruct (PjGrammar.scan (rest_atR tb text (pc + 1))) as [Q|].
  - destruct HARM as [(_ & _ & EH & _) | [(_ & _ & EH & _) | [(_ & _ & _ & EH & _) |
      (_ & _ & _ & s & r & _ & EH & _)]]]; rewrite EH; [exact Khp | exact Khp | exact Khp |]. right. exact Khp.
  - destruct HARM as (_ & EH & _). rewrite EH. exact Khp. }
assert (HL2 : exists Lam2 peak2 cnt2 fail2 ran2,
  prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most own /\
  (forall a k, In (a, k) Lamc -> In (a, k) Lam2) /\
  (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc))).
{ destruct HPOST as (res & _ & _ & _ & _ & HARM).
  unfold tpstP_ANone, tpstP_ASome1, tpstP_ASome2, tpstP_ASome3, tpstP_ASome4 in HARM.
  destruct (PjGrammar.scan (rest_atR tb text (pc + 1))) as [Q|].
  - destruct HARM as [(_ & _ & _ & _ & _ & HL & _) | [(_ & _ & _ & _ & _ & _ & _ & _ & HL & _) |
      [(_ & _ & _ & _ & _ & HL & _) | (_ & _ & _ & s & r & _ & _ & EA & _ & _ & HL & _)]]].
    + exists Lamc, peakc, (cntc + 1), SIZE_MAXZ, ranc. split; [exact HL|]. split; [auto | intros a k' H; left; exact H].
    + eexists Lamc, _, _, failc, _. split; [exact HL|]. split; [auto | intros a k' H; left; exact H].
    + eexists Lamc, _, (cntc + 1), failc, ranc. split; [exact HL|]. split; [auto | intros a k' H; left; exact H].
    + eexists ((res, Z.of_nat Q + 1) :: Lamc), _, (cntc + 1), failc, ranc. split; [exact HL|].
      split; [intros a k' H; right; exact H|].
      intros a k' [Ek | H]; [|left; exact H]. injection Ek as <- <-. right. intros Hin.
      destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 (HBK _ Hin)) as (_ & _ & _ & _ & _ & HPW).
      rewrite EA, map_app in HPW. cbn [map] in HPW.
      assert (RSq : Z.of_nat Q + 1 + cf_head <= req_size (Z.of_nat Q + 1 + cf_head)) by (apply RS; lia).
      apply (pik_pairwise_last _ _ HPW); [cbn [fst snd]; lia|].
      apply in_map_iff. exists (res - cf_head, Z.of_nat Q + 1 + cf_head). split; [reflexivity | exact Hin].
  - destruct HARM as (_ & _ & _ & HL & _).
    exists Lamc, peakc, cntc, failc, ranc. split; [exact HL|]. split; [auto | intros a k' H; left; exact H]. }
destruct HL2 as (Lam2 & peak2 & cnt2 & fail2 & ran2 & HLG2 & HLin & HLnew).
pose proof (pik_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc memr pc Lamc peakc cntc failc ranc most own MEQ HCUR)
  as HCURr.
(* the node's place and shadow at the return (PItems_kept.v's memory-kept statement) *)
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
assert (HKMr : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF q 24 /\ src_rd W2 mem2 text tb /\
  prhReader_home B ly2 S2 Hp2 Lam2 text len /\ prhReader_at B ly2 S2 Lam2 regs0 e v 56 /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56).
{ apply (HKM (wle' SEGS YGcfRehidePost.RZ_cf) regs0 e q v text len tb d lyc Sc Hpc Wc memr mdc pc Lamc peakc cntc
    failc ranc most own
    STK_parse_string (spZ regs) (PI_FRAME + e) [(q, q + 8)] [] ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most own
    WS1 HCURr HJ1 HX).
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - lia.
  - destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | Hro] | (b & m & Hbin & _ & Hb1 & Hb2)].
    + right; right. pose proof (proj1 (Forall_forall _ _) HHB _ Hbin) as (KK0 & KKin & _). cbn [fst snd] in KK0, KKin.
      exists (b - cf_head), (m + cf_head). split; [exact KKin | lia].
    + destruct Hro as [Hro | Hki]; [left; exact Hro | right; left; exact Hki].
    + right; right. exists b, m. auto.
  - intros b m Hbin Hrng. split; [exact (HBK _ Hbin)|].
    destruct HPOST as (res & _ & _ & _ & _ & HARM).
    unfold tpstP_ANone, tpstP_ASome1, tpstP_ASome2, tpstP_ASome3, tpstP_ASome4 in HARM.
    destruct (PjGrammar.scan (rest_atR tb text (pc + 1))) as [Q|].
    + destruct HARM as [(_ & _ & EH & _) | [(_ & _ & EH & _) | [(_ & _ & _ & EH & _) |
        (_ & _ & _ & s & r & _ & EH & EA & _)]]]; rewrite EH; [tauto | tauto | tauto |].
      split; [intros Hb; right; exact Hb|]. intros [Eb | Hb]; [|exact Hb]. exfalso.
      destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 (HBK _ Hbin)) as (_ & _ & _ & _ & _ & HPW).
      rewrite EA, map_app in HPW. cbn [map] in HPW.
      pose proof (pik_pairwise_last_disj _ _ _ HPW (in_map (fun b0 => (fst b0, req_size (snd b0))) _ _ Hbin)) as HZD.
      unfold zdisjoint in HZD. cbn [fst snd] in HZD.
      assert (Rm : 0 < req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
      assert (Rn : 0 < req_size (Z.of_nat Q + 1 + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
      lia.
    + destruct HARM as (_ & EH & _). rewrite EH. tauto.
  - intros a0 Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - intros a0 Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. unfold shadow_of_addr in Hra.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - intros a0 Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. unfold shadow_of_addr in Hra.
    unfold amem_range in Hvam. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - intros (r & Hr & H0). destruct Hr as [<- | []]. cbn [fst snd] in H0. lia.
  - exact HLG2.
  - left. reflexivity.
  - intros a0 k' Hk' _. exact (HLin a0 k' Hk').
  - lia.
  - lia.
  - exact HLnew.
  - exact HARm. }
destruct HKMr as (RAq2 & SRC2 & HOME2 & AT2 & RAv2).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold ASAN_CEIL in CR.
assert (R2' : getr regs2 2 = getr regs 2) by exact (HKS 2 ltac:(unfold acallee_saved; lia)).
assert (Rsp2 : spZ regs2 = spZ regs) by (unfold spZ; rewrite R2'; reflexivity).
assert (AVR : forall (H : word -> bool) m m' a, mrestrict H m' = mrestrict H m -> aview SEGS H m' a = aview SEGS H m a)
  by (intros H m m' a Em; unfold aview; rewrite Em; reflexivity).
assert (VW : forall a x, spZ regs <= a -> a + 8 <= spZ regs + 40 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a 8 x -> val_mem SEGS (mrestrict (w_H W2) mem2) a 8 x).
{ intros a x Ha1 Ha2 Hv. apply (pik_val_win Wc W2 memc mem2 a 8 x); [|exact Hv].
  intros kk Hk. rewrite <- (AVR _ _ _ _ MEQ). apply HX; [unfold PI_FRAME; lia|].
  intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia. }
(* the node's bytes at the return: kept by parse_string (the call agreement, footprint the node only) *)
assert (AGRN : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pj_footR v [])).
{ rewrite <- MEQ.
  apply (pik_agree_call regs0 e v lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own STK_parse_string (spZ regs)
    (PI_FRAME + e) [(q, q + 8)] ly2 S2 Hp2 W2 mem2 md2 k1 [] WS1).
  - exact (pik_ledger_rdeq lyc Sc Hpc Wc memc memr Lamc peakc cntc failc ranc most own MEQ HLG).
  - exact HPLAT.
  - exact Hvw.
  - lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. lia.
  - exact HJ1.
  - exact HX.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - exact HBK.
  - intros b Hb. destruct Hb.
  - intros a ((a0 & k0) & Hb & _). destruct Hb. }
assert (NODE : forall x, v <= x < v + 56 -> mbyte SEGS (mrestrict (w_H W2) mem2) x = mbyte SEGS (mrestrict (w_H Wc) memc) x)
  by (intros x Hx; exact (proj1 (AGRN x (or_introl Hx)))).
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 (HBK _ Kin)) as (_ & _ & _ & _ & KP2 & _).
destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 (HBK _ Kin) HHPK) as [HBS _].
replace (keys - cf_head + cf_head) with keys in HBS by lia.
apply (pik_k3_core d (YCbqGwild.wbudget CW 0) fxc fx0 ly S Hp W mem md regs0 e q v
  (fQmn (L := Lb) (PA := PIb) mem
     (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr))
  ly2 S2 Hp2 W2 mem2 md2 (k + k1) regs2 keys (Z.of_nat n) (bv_unsigned (getr regs2 10))
  (keys - cf_head) (8 * Z.of_nat cap + cf_head) WS0 HJ2 HMN).
- etransitivity; [exact (HKS 19 ltac:(unfold acallee_saved; lia)) | exact Q19].
- etransitivity; [exact (HKS 22 ltac:(unfold acallee_saved; lia)) | exact B22].
- etransitivity; [exact (HKS 24 ltac:(unfold acallee_saved; lia)) | exact B24].
- etransitivity; [exact (HKS 26 ltac:(unfold acallee_saved; lia)) | exact Q26].
- unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as RR. unfold bv_modulus in RR. change (Z.of_N 64) with 64 in RR. exact RR.
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. lia.
- exact Hv8.
- lia.
- lia.
- lia.
- lia.
- rewrite Rsp2. lia.
- rewrite Rsp2. lia.
- rewrite Rsp2. apply VW; [lia | lia | exact BV0].
- rewrite Rsp2. apply VW; [lia | lia | exact BV8].
- rewrite Rsp2. apply VW; [lia | lia | exact BV16].
- apply (rd_u64_frame SEGS (mrestrict (w_H Wc) memc)); [exact HKy|]. intros x Hx. apply NODE. lia.
- apply (rd_u64_frame SEGS (mrestrict (w_H Wc) memc)); [exact HNn|]. intros x Hx. apply NODE. lia.
- intros a Ha. apply (apresent_writable SEGS (w_H W2) mem2 a). apply (KP2 a). lia.
- rewrite Rsp2. apply pik_disj; [|lia|lia]. intros a Ha1 Ha2. apply (proj2 (HNOWN a ltac:(lia))). lia.
- apply pik_disj; [|lia|lia]. intros a Ha1 Ha2. apply (HAP _ a Hkin); [unfold pj_holdsR; cbn [fst snd]; lia | lia].
- rewrite Rsp2. lia.
- exact (HBK _ Kin).
- apply (proj1 HBLK keys (8 * Z.of_nat cap)). apply (Permutation_in _ (Permutation_sym HPERM)).
  apply in_or_app. left. exact Hkin.
- lia.
- lia.
- exact RAv2.
- apply (pik_ra_of_bs _ _ keys (req_size (8 * Z.of_nat cap + cf_head) - cf_head)); [exact HBS | lia | lia | lia].
- intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. unfold SHADOW_OFF. lia.
- intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in KBapp. unfold SHADOW_OFF. lia.
- intros memx' mdx' kx' regs' off HJx HMNx MQ VS HKSx Harm.
  destruct Harm as [(H0 & ->) | (H0 & ->)];
    [|exact (pik_k3n_holds d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak
       cnt fail ran most own kr lyc Sc Hpc Wc memc memr mdc k regs f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc
       failc ranc ly2 S2 Hp2 W2 mem2 md2 k1 regs2 memx' mdx' kx' regs' WS0 WS1
       HFP HENT HMNx HFRM HREGS HRB H21 HIN Hpcl Hq34 MEQ HARm HJ2 HWS HJ1
       HX HKS HPOST HJx MQ VS HKSx H0)].
  (* ---- 0x87c78 TAKEN: parse_string returned NULL; the kit's None arm at the epilogue ---- *)
  pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as (GLP & GP & GC & GF & GR).
  assert (Hcn1 : 0 <= cntc) by lia. assert (Hcn2 : cntc + 1 < 2 ^ 64) by lia.
  destruct (pik_str_none fxc lyc Sc Hpc Wc Lamc peakc cntc failc ranc most own q text len pc (Z.of_nat d + 1) tb
    ly2 S2 Hp2 W2 regs2 mem2 md2 HPOST HAR1 H0 Hcn1 Hcn2 GLP)
    as (oks & ts & peak2' & cnt2' & fail2' & ran2' & HSJ & Hlo & Hwf & Hheld & Hph & Hcg & HSM & HARMs & HLGs & HRLs
      & EAs & EHs & HINs & HPMs & HPIs).
  (* the entry's counter and text *)
  pose proof RDP as (_ & _ & _ & _ & HIN00 & _ & _ & _ & _ & _ & HHOME0 & _ & _ & _ & _ & _ & HLG0 & _ & HCNT0 & _).
  pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HLG0) as (_ & _ & GC0 & GF0 & _).
  pose proof HIN00 as (_ & _ & _ & _ & _ & _ & _ & Hp0 & Hlen0 & _).
  assert (Hx0 : rest_atR tb text p <> []).
  { unfold rest_atR. intros E. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn [length] in E. lia. }
  (* the key slot keys + 8 n, inside the keys block, is apart from everything the post reads *)
  assert (Hsl : keys + 8 * Z.of_nat n + 8 <= keys + 8 * Z.of_nat cap) by lia.
  assert (HKB2 : In (keys - cf_head, 8 * Z.of_nat cap + cf_head) (ablocks B ly2 S2)) by exact (HBK _ Kin).
  assert (SNI : forall x, keys + 8 * Z.of_nat n <= x < keys + 8 * Z.of_nat n + 8 -> ~ in_img SEGS x).
  { intros x Hx Hi. exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR1 HKB2 ltac:(lia) Hi). }
  assert (MQP : forall x, 0 <= x < 2 ^ 64 -> ~ (keys + 8 * Z.of_nat n <= x < keys + 8 * Z.of_nat n + 8) ->
    mbyte SEGS (mrestrict (w_H W2) memx') x = mbyte SEGS (mrestrict (w_H W2) mem2) x /\
    (writable_at SEGS (mrestrict (w_H W2) mem2) x -> writable_at SEGS (mrestrict (w_H W2) memx') x))
    by (intros x Hx Hn'; exact (pik_pt _ _ x (MQ x Hx Hn'))).
  pose proof (pik_ledger_rdeq lyc Sc Hpc Wc memc memr Lamc peakc cntc failc ranc most own MEQ HLG) as HLGr.
  assert (HLB : forall a k', In (a, k') Lamc -> 0 <= k' /\ 4096 <= a - cf_head /\
    a - cf_head + req_size (k' + cf_head) <= YM05.alloc_ceiling /\ In (a - cf_head, k' + cf_head) (ablocks B lyc Sc)).
  { intros a k' Hin. pose proof (proj1 (Forall_forall _ _) HHB (a, k') Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memr mdc _ _ HARm Hab) as (_ & H4 & Hc & _). auto. }
  pose proof HW as HW8. unfold prh_head_wide in HW8.
  (* the ledger at the store's memory: the statics are image bytes, the head words are below their own user range *)
  assert (HLGx : prh_ledger (L := Lb) (PA := PIb) B ly2 S2 Hp2 W2 memx' Lamc peak2' cnt2' fail2' ran2' most own).
  { apply (pik_ledger_kept ly2 S2 Hp2 W2 mem2 memx' Lamc peak2' cnt2' fail2' ran2' most own HLGs).
    - intros a Ha. pose proof (PIK_PSTIMG a Ha) as Hi. pose proof (pa_segs_low (PAImg := PIb) a Hi) as Hlow.
      unfold kLowMemEnd in Hlow. apply MQP; [lia|]. intros Hs. exact (SNI a Hs Hi).
    - intros a k' i Hin Hi. destruct (HLB a k' Hin) as (Hk0 & H4 & Hc & Hab).
      assert (RSa : k' + cf_head <= req_size (k' + cf_head)) by (apply RS; lia).
      apply MQP; [lia|]. destruct (Z.eq_dec a keys) as [-> | Hne]; [lia|].
      destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own a k' keys (8 * Z.of_nat cap)
        HARm HLGr Hin Hkeys Hne); lia. }
  (* the cursor at the store's memory: its 24 bytes on the stack, the text in its entry home *)
  pose proof HBLK as (BNEW & BPERM & BFR & BPK).
  assert (HNEW : ~ In (keys - cf_head, 8 * Z.of_nat cap + cf_head) (ablocks B ly S)).
  { apply (BNEW keys (8 * Z.of_nat cap)). apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left.
    exact Hkin. }
  assert (HINx : pj_in_okR SEGS (mrestrict (w_H W2) memx') q text len pc (Z.of_nat d + 1) tb).
  { apply (pik_in_ok_kept _ _ q text len pc (Z.of_nat d + 1) tb HINs). intros x [Hx | Hx]; apply MQP.
    - lia.
    - lia.
    - lia.
    - intros Hs. apply (pik_home_apart ly S Hp W mem Lam peak cnt fail ran most own ly2 S2 Hp2 W2 mem2 md2 D0 text len
        (keys - cf_head) (8 * Z.of_nat cap + cf_head) HAR1 HLG0) with (a := x); [| exact HKB2 | exact HNEW | exact HHOME0
        | exact Hx | lia].
      rewrite EAs. exact BPERM. }
  (* the half-built container: kept by parse_string (the call agreement), then by the store outside the slot *)
  pose proof HND as HNDf.
  assert (HNDD : NoDup (pi_sblk true kids keys cap ++ Di)).
  { apply NoDup_ListNoDup. apply NoDup_ListNoDup in HNDf. pose proof HLED as (_ & _ & _ & L4 & _).
    assert (HN1 : List.NoDup (map fst (D0 ++ Lam))) by (apply (Permutation_NoDup (Permutation_map fst L4)); exact HNDf).
    rewrite map_app in HN1. apply List.NoDup_app_remove_r in HN1. apply (List.NoDup_map_inv fst) in HN1.
    exact (Permutation_NoDup HPERM HN1). }
  assert (HINCL : incl (pi_sblk true kids keys cap ++ Di) Lamc).
  { intros b Hb. pose proof HLED as (_ & _ & _ & L4 & _). apply (Permutation_in b (Permutation_sym L4)).
    apply in_or_app. left. exact (Permutation_in b (Permutation_sym HPERM) Hb). }
  assert (AGRD : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2)
    (pj_footR v (pi_sblk true kids keys cap ++ Di))).
  { rewrite <- MEQ.
    apply (pik_agree_call regs0 e v lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own STK_parse_string (spZ regs)
      (PI_FRAME + e) [(q, q + 8)] ly2 S2 Hp2 W2 mem2 md2 k1 (pi_sblk true kids keys cap ++ Di) WS1).
    - exact HLGr.
    - exact HPLAT.
    - exact Hvw.
    - lia.
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. lia.
    - exact HJ1.
    - exact HX.
    - unfold PI_FRAME; lia.
    - unfold PI_FRAME; lia.
    - lia.
    - lia.
    - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
    - exact HBK.
    - exact HINCL.
    - intros a ((a0 & k0) & Hb & Hab0) (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      unfold pj_holdsR in Hab0. cbn [fst snd] in Hab0. destruct (HLB a0 k0 (HINCL _ Hb)) as (Hk0 & H4 & Hc & _).
      assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia). lia. }
  pose proof (pi_cont_frame (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di HCONT AGRD) as HC2.
  assert (Hkk : kids <> keys).
  { intros Ek. apply NoDup_ListNoDup in HND. rewrite Ek in Hkids.
    pose proof (pik_nodup_fst _ _ _ _ HND Hkids Hkeys) as E56. lia. }
  assert (HCONTx : pi_cont (L := Lb) (PA := PIb) (mrestrict (w_H W2) memx') (prh_lin Lamc) true v kids keys n cap acc Di).
  { apply (pi_cont_frame_slot_gen (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di
      (keys + 8 * Z.of_nat n) (keys + 8 * Z.of_nat n + 8) HC2).
    - intros x Hx. split; [left; lia|]. split.
      + destruct (HLB kids (56 * Z.of_nat cap) Hkids) as (Hk0 & H4 & Hc & _).
        assert (RSa : 56 * Z.of_nat cap + cf_head <= req_size (56 * Z.of_nat cap + cf_head)) by (apply RS; lia).
        destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap) keys
          (8 * Z.of_nat cap) HARm HLGr Hkids Hkeys Hkk); lia.
      + split.
        * intros (a0 & k0) Hb Hh. unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
          assert (Hl : In (a0, k0) Lamc) by (apply HINCL; apply in_or_app; right; exact Hb).
          destruct (HLB a0 k0 Hl) as (Hk0 & H4 & Hc & _).
          assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia).
          destruct (Z.eq_dec a0 keys) as [-> | Hne].
          -- apply NoDup_ListNoDup in HND. pose proof (pik_nodup_fst _ _ _ _ HND Hl Hkeys) as E8. subst k0.
             apply NoDup_ListNoDup in HNDD. exact (pik_nodup_app_disj _ _ _ HNDD Hkin Hb).
          -- destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own a0 k0 keys (8 * Z.of_nat cap)
               HARm HLGr Hl Hkeys Hne); lia.
        * intros Hv. exact (HAP _ x Hkin ltac:(unfold pj_holdsR; cbn [fst snd]; lia) Hv).
    - intros x (Hf & Hns). apply MQP; [|exact Hns].
      destruct Hf as [Hx | ((a0 & k0) & Hb & Hh)].
      + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. clear - Hvam Hx Hv4096. lia.
      + unfold pj_holdsR in Hh. cbn [fst snd] in Hh. destruct (HLB a0 k0 (HINCL _ Hb)) as (Hk0 & H4 & Hc & _).
        assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia). lia. }
  (* the frame at the store's memory *)
  assert (R2x : getr regs' 2 = getr regs 2)
    by (etransitivity; [exact (HKSx 2 ltac:(unfold acallee_saved; lia)) | exact R2']).
  assert (R3x : getr regs' 3 = getr regs 3)
    by (etransitivity; [exact (HKSx 3 ltac:(unfold acallee_saved; lia)) | exact (HKS 3 ltac:(unfold acallee_saved; lia))]).
  assert (R4x : getr regs' 4 = getr regs 4)
    by (etransitivity; [exact (HKSx 4 ltac:(unfold acallee_saved; lia)) | exact (HKS 4 ltac:(unfold acallee_saved; lia))]).
  assert (R21x : getr regs' 21 = w64 (-1)).
  { etransitivity; [exact (HKSx 21 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact (HKS 21 ltac:(unfold acallee_saved; lia)) | exact H21]. }
  assert (HFRx : pi_frame (L := Lb) (PA := PIb) regs0 regs' W mem W2 memx' e q v).
  { apply (pik_frame_win regs0 regs regs' W mem Wc W2 memc memx' e q v HFRM); [unfold spZ; rewrite R2x; reflexivity
      | exact R3x | exact R4x | exact Hspq |].
    intros a Ha Hn'.
    assert (E1 : aview SEGS (w_H W2) memx' a = aview SEGS (w_H W2) mem2 a).
    { unfold aview. rewrite (proj1 (MQP a ltac:(lia) ltac:(lia))). reflexivity. }
    rewrite E1, <- (AVR _ _ _ a MEQ). apply HX; [unfold PI_FRAME; lia|].
    intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia. }
  (* the batch-kit free order at the store's memory: the completed slots' order list, read through the bytes pi_cont reads,
     which parse_string kept (AGRD) and the store left (the key slot n is none of them) *)
  assert (AGS : pj_agreeR SEGS (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memx')
    (pvm_cont_ufoot true v kids keys n Di)).
  { intros x Hx.
    assert (Hf : pj_footR v (pi_sblk true kids keys cap ++ Di) x)
      by exact (pvm_ufoot_foot true v kids keys n cap Di x ltac:(lia) Hx).
    assert (Hns : ~ (keys + 8 * Z.of_nat n <= x < keys + 8 * Z.of_nat n + 8)).
    { intros Hs. destruct Hx as [Hx | [(i & Hi & Hx) | [(_ & i & Hi & Hx) | (b & Hb & Hx)]]].
      - exact (HAP _ x Hkin ltac:(unfold pj_holdsR; cbn [fst snd]; lia) Hx).
      - destruct (HLB kids (56 * Z.of_nat cap) Hkids) as (Hk0 & H4 & Hc & _).
        assert (RSa : 56 * Z.of_nat cap + cf_head <= req_size (56 * Z.of_nat cap + cf_head)) by (apply RS; lia).
        destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own kids (56 * Z.of_nat cap) keys
          (8 * Z.of_nat cap) HARm HLGr Hkids Hkeys Hkk); lia.
      - lia.
      - destruct b as (a0 & k0). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
        assert (Hl : In (a0, k0) Lamc) by (apply HINCL; apply in_or_app; right; exact Hb).
        destruct (HLB a0 k0 Hl) as (Hk0 & H4 & Hc & _).
        assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia).
        destruct (Z.eq_dec a0 keys) as [-> | Hne].
        + apply NoDup_ListNoDup in HND. pose proof (pik_nodup_fst _ _ _ _ HND Hl Hkeys) as E8. subst k0.
          apply NoDup_ListNoDup in HNDD. exact (pik_nodup_app_disj _ _ _ HNDD Hkin Hb).
        + destruct (pik_lam_disj lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own a0 k0 keys (8 * Z.of_nat cap)
            HARm HLGr Hl Hkeys Hne); lia. }
    apply MQP; [|exact Hns].
    destruct Hf as [Hx' | ((a0 & k0) & Hb & Hh)].
    + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. clear - Hvam Hx' Hv4096. lia.
    + unfold pj_holdsR in Hh. cbn [fst snd] in Hh. destruct (HLB a0 k0 (HINCL _ Hb)) as (Hk0 & H4 & Hc & _).
      assert (RSa : k0 + cf_head <= req_size (k0 + cf_head)) by (apply RS; lia). lia. }
  pose proof (pik_agree_ufoot _ _ v kids keys n cap Di ltac:(lia) AGRD) as AGU.
  pose proof (pvm_forder_frame _ _ _ _ _ v _ _ _ _ _ _ HFORD (fun x k H => H) AGU) as HFORD2.
  pose proof (pvm_forder_frame _ _ _ _ _ v _ _ _ _ _ _ HFORD2 (fun x k H => H) AGS) as HFORDx.
  (* the member's text past the opening quote, and the call's all-granted trace through the string's *)
  assert (Hy34 : rest_atR tb text pc = 34 :: rest_atR tb text (pc + 1)).
  { rewrite (pik_rest_cons tb text pc) by lia. rewrite (nth_error_nth tb (Z.to_nat (pc - text)) 0 Hq34). reflexivity. }
  assert (HNMx : jr_name true (rest_atR tb text pc) oks = (None, ts, [])).
  { rewrite Hy34. exact (pik_name_str_none _ _ _ _ HSJ). }
  assert (HGTs : exists rest, PRH_Charge.prhPi_gtrace d true (rest_atR tb text p) =
    tr0 ++ PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1)) ++ rest).
  { apply (pik_gtrace_split d _ ok0 tr0 f n cap (rev acc)); [rewrite <- Hy34; exact HEQ | exact HGR]. }
  apply (pik_epi_exit d (YCbqGwild.wbudget CW 0) fxc fx0 ly S Hp W mem md regs0 e q v tb text len p Lam peak cnt fail
    ran most own kr ly2 S2 Hp2 W2 memx' mdx' kx' regs' WS0 HJx HWS HFP HMNx HFRx R21x).
  intros regsx H10.
  (* the travelling position and live requests through the refused string: parse_string's arm post (its position
     implication and live requests over the string's own events ts) composed on the block's own over tr0; its hull use
     over its all-granted list (pik_ps_hull, pik_gts_evs) *)
  assert (HHUs : PresetHullBudget.hull_used Sc S2
    (PresetReqAt.rd_hevs (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1))))).
  { rewrite pik_gts_evs. exact (pik_ps_hull HPOST). }
  exact (pik_null_post d ly S tb text len p q v Lam peak cnt fail ran most own kr lyc Sc
    f n cap acc kids keys Di pc ok0 tr0 D0
    Lamc peakc cntc failc ranc oks ts (PRH_Charge.prhPs_gtrace (rest_atR tb text (pc + 1))) peak2' cnt2' fail2' ran2' af
    ly2 S2 Hp2 W2 memx' pc HCONTx HDEP HAP HPERM HEQ HLED
    HBLK HBB HOK HLS HdM Hncap Hx0 GC0 HCNT0 GF0 HNMx Hlo Hwf Hheld Hph Hcg HGTs HSM HGR HARMs HFORDx HFLB HLGx HRLs HPOSB
    HHUs (pik_pos_call S Sc S2 tr0 ts HPOSB HPIs) (PItems_posb.pi_live_call _ _ _ tr0 ts HLIVE HPMs)
    EAs HFRS1 HINx regsx mdx' H10).
Qed.


(* ---- K2: from the opening quote (0x87c08): `mv a0, s1`, `jal parse_string` (the kit's tparse_string_specX at the
   caller window PI_FRAME + e, a BUDGETED callee at wbudget CW 0: YCbqGwild.aj_call_xWb_spR at wle' SEGS RZ_cf), then
   K3 at the return
   site with the caller's journal at WS0 ++ WS1 ---- *)
Lemma pik_k2_holds : forall d CTX0 CW N,
  pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pik_k2_spec d CTX0 CW N.
Proof.
intros d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc mdc k regs f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc WS0
  HJw HWS HFP HENT HMN HFRM HREGS HRB H21 HIN Hpcl Hq34.
unfold pi_ajR in HJw.
(* THE BUDGETED JOURNAL: the run takes it rebased; the call takes it back at WS0 *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof HIN as (HCUR & HN & Hncap & HCONT & HDEP & HAP & HPERM & HFU & HEQ & HLED & HBLK & HPOSB & HLIVE & HBB & HOK
  & HLS & HROOM & _).
pose proof HENT as (Emn & Epk1 & Epk2 & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & _).
(* the room for CW at the call state: the entry's, across the prefix's journal, whose wild traces are all CW's *)
pose proof (YCbqGwild.ajournal_xw_roomR (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CW 0 HJw Ewr
  HWS)
  as HWRc.
change (0 - YCbqGwild.wfresh CW WS0)%nat with 0%nat in HWRc.
pose proof RDP as (_ & _ & _ & _ & _ & Hfwin & Hspq & Hqe & _ & _ & _ & _ & HPV & Hqv & Htv & Hvw & _ & HdM & _).
pose proof HPV as (Hv4096 & Hv8 & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HCUR as (HIN0 & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN0 as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof (pik_stk_str d) as HSTKB. pose proof (PIK_FR0 F_parse_string) as HPS0.
unfold SRr', cfg_at.
remember (Eimg (PI := PIb) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env VALb A_LIM E0) by (subst E0; apply Eimg_env).
assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E0 nk = getr regs rk).
{ intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] nk rk Hk). }
assert (HS : st_ok_pi (fx := fxc) SEGS VALb E0
  (mkSS (PIATb PIK_O_STR) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxc regs (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_STR)) memc (seg_rom SEGS)))).
{ rewrite (restrict_mkst_fx (fx := fxc)). apply (pa_entry_st_ok_full (fx := fxc) (L := Lb) (PI := PIb)).
  - subst E0. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - cbn; exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E0 (mrestrict (w_H Wc) memc)) by constructor.
(* the runner carrying the overlay's normality from the run's start memory to its end (YC1fPx's _inv twin) *)
pose (RUN := paj_run_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
change (w64 (VALb A_TEXT + PIATb PIK_O_STR)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_STR)).
paj_run_tok_x_inv RUN HS HJ SHOK HMN BAND_SPAN.
{ apply awr_ok_nil. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
cbn [ss_mem] in HF, HFr.
assert (MEQ : mrestrict (w_H Wc) (ms_mem ms) = mrestrict (w_H Wc) memc).
{ apply functional_extensionality; intros x. apply HFr. intros (r & Hin & _). exact (in_nil Hin). }
clear HF HFr HG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
unfold PI_FRAME in HSTKB.
assert (HPSN : 0 <= STK_parse_string).
{ unfold STK_parse_string. pose proof (pik_zmaxl_nonneg [STK_fuzz_free; STK_fuzz_malloc; STK_hex4; STK_put_utf8]).
  lia. }
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
pose proof (pik_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc (ms_mem ms) pc Lamc peakc cntc failc ranc most own MEQ
  HCUR)
  as HCURm.
pose proof HCURm as (HINm & HRAm & HSRCm & _ & _ & _ & HLGm & _).
assert (Usp : spZ (ms_regs ms) = spZ regs) by (unfold spZ; rewrite R2, (EK 2%nat 2%bv eq_refl); reflexivity).
assert (Us0 : s0Z (ms_regs ms) = q + 16).
{ unfold s0Z. rewrite R8, (EK 8%nat 8%bv eq_refl), Q8. apply unsigned_lit_small. lia. }
assert (Ra0 : getr (ms_regs ms) 10 = w64 q) by (rewrite R10, (EK 9%nat 9%bv eq_refl); exact Q9).
assert (AVM : aview SEGS (w_H Wc) (ms_mem ms) = aview SEGS (w_H Wc) memc) by exact (pik_aview_eq Wc memc (ms_mem ms) MEQ).
assert (Hs8 : spZ regs0 mod 8 = 0) by (rewrite Fsp' in *; lia).
(* the frame-pointer chain the call sees: s0 = q + 16 (as at the first skip_ws) *)
assert (HCH : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ regs) (q + 16) ch1).
{ destruct (Z_lt_le_dec (q + 16) (ly_top lyc - 16)) as [Hlt | Hge].
  - exists [(q + 16, text + len, pc)]. right.
    split; [lia|]. split; [exact Hlt|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
    split.
    + cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
      split; [replace (q + 16 - 8) with (q + 8) by lia;
              apply (pik_rdword_of_val (w_H Wc) (ms_mem ms) (q + 8) (text + len)); [rewrite MEQ; exact Ve | lia]|].
      split; [replace (q + 16 - 16) with q by lia;
              apply (pik_rdword_of_val (w_H Wc) (ms_mem ms) q pc); [rewrite MEQ; exact Vp | lia]|].
      split; [lia|].
      unfold bad_next. replace (pc <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + constructor; [cbn [fst]; lia | constructor].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH as (ch1 & HCH).
(* the cursor's chain word at the call view, as the entry premise prh_cur_entry states it (its next-frame word) *)
assert (PS0 : prh_s0 F_parse_string q = q) by (unfold prh_s0; rewrite PIK_S0STR; lia).
assert (HCLO : prh_cur_low Wc (ms_mem ms) F_parse_string q).
{ intros w Hw. rewrite PS0, AVM in Hw. apply ((proj2 Ecent) F_parse_string (or_introl eq_refl)). rewrite PS0.
  apply (pik_word_call regs0 regs W mem Wc memc e q v (q - 16) w HFRM); first [lia | exact Hvw | exact Hw]. }
(* parse_string's own chain, from its s0 = q: one record (or none), its next frame word below alloc_ceiling *)
assert (HCH2 : exists ch2, achain lyc (aview SEGS (w_H Wc) (ms_mem ms))
  (spZ (ms_regs ms) - PRH_Base.pi_frame F_parse_string) (prh_s0 F_parse_string q) ch2).
{ rewrite PS0, Usp.
  destruct (Z_lt_le_dec q (ly_top lyc - 16)) as [Hlt | Hge]; [|exists []; left; split; [right; left; lia | reflexivity]].
  assert (X8 : exists r, rdword (aview SEGS (w_H Wc) memc) (q - 8) = Some r).
  { apply (pik_word_call_some ly regs0 regs W mem Wc memc e q v (q - 8) HFRM Hfwin); first [lia | exact Hvw]. }
  assert (X16 : exists r, rdword (aview SEGS (w_H Wc) memc) (q - 16) = Some r).
  { apply (pik_word_call_some ly regs0 regs W mem Wc memc e q v (q - 16) HFRM Hfwin); first [lia | exact Hvw]. }
  destruct X8 as (r & Er). destruct X16 as (nfp & En).
  rewrite <- AVM in Er, En.
  pose proof (pik_rdword_range _ _ _ _ Er) as Rr.
  pose proof (HCLO nfp ltac:(rewrite PS0; exact En)) as Hnfp.
  destruct (Z_lt_le_dec r 4096) as [Hr | Hr].
  - exists []. right. split; [lia|]. split; [exact Hlt|]. split; [exact Hq8|].
    split; [cbn [fpchain]; exists r; split; [exact Er | lia] | constructor].
  - exists [(q, r, nfp)]. right. split; [lia|]. split; [exact Hlt|]. split; [exact Hq8|].
    split.
    + cbn [fpchain]. split; [reflexivity|]. split; [exact Hq8|]. split; [exact Er|]. split; [exact En|].
      split; [exact Hr|]. unfold bad_next. replace (nfp <=? q) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity.
    + constructor; [cbn [fst]; lia | constructor]. }
(* the room of the string's call (tparse_string_specX's last premise, the batch kit's tip 03fcabb582d0): the request of its
   malloc, the first event of the member's granted run (rd_room's request bound), and the live bytes at each of its
   own all-granted events, a prefix of the member's (rd_room's per-event room, PItems_ledk1.pik1_live_evs_pre) *)
assert (Hy34 : rest_atR tb text pc = 34 :: rest_atR tb text (pc + 1)).
{ rewrite (pik_rest_cons tb text pc) by lia. f_equal. apply nth_error_nth. exact Hq34. }
assert (HRQ : forall Q, PjGrammar.scan (rest_atR tb text (pc + 1)) = Some Q -> LIVE_parse_string Q < cf_malloc_max).
{ intros Q HQ.
  destruct (pik_gt_alloc f (Nat.succ d) n cap (rev acc) (rest_atR tb text (pc + 1)) Q HQ) as (t & Et).
  pose proof HROOM as (_ & RM2 & _). rewrite Hy34, Et in RM2.
  unfold PRH_Charge.prh_maxreq in RM2. cbn [map fold_right PjGrammar.esize] in RM2.
  unfold LIVE_parse_string. rewrite ?Nat2Z.inj_succ in RM2. clear - RM2. lia. }
assert (HLV : PRH_Base.prh_live_evs Sc (prhPs_evs (rest_atR tb text (pc + 1)) [])).
{ rewrite (prhPs_evs_model _ [] PIK_HEAD).
  pose proof HROOM as (_ & _ & RM3). rewrite Hy34 in RM3.
  destruct (pik_gt_str f (Nat.succ d) n cap (rev acc) (rest_atR tb text (pc + 1))) as (t & Et).
  rewrite Et, PresetReqAt.rd_hevs_app in RM3.
  exact (PItems_ledk1.pik1_live_evs_pre _ _ _ RM3). }
destruct HCH2 as (ch2 & HCH2).
(* the live counts at the call (form (b)): parse_string's two peak premises over its own all-granted events
   prhPs_evs .. [] (rd_hevs of jr_string's granted trace, prhPs_evs_model at PIK_HEAD), from pi_ent's over the whole
   call's at the block's pi_live (PItems_value_model.v pvm_lc_call): the member's granted run begins with jr_string's,
   pc being on the quote (pik_gt_str) *)
assert (LC : forall (f0 : Z -> bool) b,
  Z.of_nat (PresetRun.pkR f0 (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (PRH_Charge.prhPi_gtrace d true (rest_atR tb text p)))) <= b ->
  Z.of_nat (PresetRun.pkR f0 (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (prhPs_evs (rest_atR tb text (pc + 1)) [])) <= b).
{ intros f0 b Hb. rewrite (prhPs_evs_model _ [] PIK_HEAD).
  apply (pvm_lc_call f0 _ _ d true (rest_atR tb text p) ok0 tr0
    (pi_jrb f (Nat.succ d) true n cap (rev acc) (rest_atR tb text pc)) _ b HEQ HOK HLIVE); [|exact Hb].
  rewrite (pik_rest_cons tb text pc) by (clear - Hple Hlen Hpcl; lia).
  rewrite (nth_error_nth tb (Z.to_nat (pc - text)) 0 Hq34).
  exact (pik_gt_str f (Nat.succ d) n cap (rev acc) (rest_atR tb text (pc + 1))). }
(* THE HULL BUDGET of the call (tparse_string_specX's hull premise): paid from pi_ent's over the whole call's
   all-granted events at the split the live counts use (the prefix's events, then jr_string's granted ones,
   PItems_value_model.pvm_gt_pref / pik_gt_str), by PItems_posb.pi_posb_budget at the block's travelling pi_posb *)
assert (HHB : PresetHullBudget.hull_budget Sc (prhPs_evs (rest_atR tb text (pc + 1)) [])).
{ rewrite (prhPs_evs_model _ [] PIK_HEAD).
  destruct (pvm_gt_pref d true (rest_atR tb text p) ok0 tr0
    (pi_jrb f (Nat.succ d) true n cap (rev acc) (rest_atR tb text pc)) HEQ HOK) as (E & EG).
  destruct (pik_gt_str f (Nat.succ d) n cap (rev acc) (rest_atR tb text (pc + 1))) as (t & Et).
  rewrite Hy34, Et, PresetReqAt.rd_hevs_app, <- app_assoc in EG.
  pose proof HENT as HB0. apply pi_ent_hull in HB0. rewrite EG in HB0.
  exact (PItems_posb.pi_posb_budget S Sc tr0 _ _ _ HB0 HPOSB eq_refl). }
(* back to the budgeted journal at WS0 (the run stored nothing), then the call of the BUDGETED callee parse_string by
   the call rule over the walk's relation (its text concludes SRr' segs RZ_cf, its post at wle') *)
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD)
  as HJb.
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YCbqGwild.aj_call_xWb_spR (SK := SK) SEGS B prh_pst ARx LAWS (pa_segs_low (PAImg := PIb))
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    Wc E0 _ ms
    (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly S Hp W mem md [] lyc Sc Hpc _ k WS0
    STK_parse_string (PI_FRAME + e) [(q, q + 8)] (- (PI_FRAME + e)) (Z_to_bv 64 (VALb A_TEXT + 25924)) ch1
    (YCbqGwild.wbudget CW 0)
    (fQmn (L := Lb) (PA := PIb) (ms_mem ms)
       (pik_ps_postX fxc lyc Sc Hpc Wc Lamc peakc cntc failc ranc most own q text len pc (Z.of_nat d + 1) tb))
    HS eq_refl HJb).
  - rewrite Usp, Fsp. unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, He16 by lia; reflexivity].
  - unfold PI_FRAME. lia.
  - exact HPSN.
  - unfold PI_FRAME. lia.
  - unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.add_mod, He16 by lia; reflexivity.
  - lia.
  - rewrite R3, (EK 3%nat 3%bv eq_refl), F3. exact Egp.
  - rewrite R4, (EK 4%nat 4%bv eq_refl), F4. exact Etp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (pa_B_ok (PAImg := PIb)) as HB. pose proof (pa_val_range (PAImg := PIb) A_TEXT) as HBr.
    rewrite unsigned_lit_small by lia. vm_compute. discriminate.
  - replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) by (unfold PI_FRAME; lia). rewrite Us0. exact HCH.
  - intros HAF HWIN. cbn [ss_pc setpc].
    refine (TPSTR fxc CTX0 CW most own lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 (PI_FRAME + e) q text len pc
      (Z.of_nat d + 1) tb Lamc peakc cntc failc ranc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + split; [exact HAF|]. split.
      { apply (pik_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact Erod].
        intros (r & Hr & H0). cbn [rd_fp In] in Hr.
        destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia. }
      pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
      split; [rewrite Usp; lia|].
      (* fpre's frm_zero at the call (FRM0-ENTRY): the block's own float state, pi_fpok's first half *)
      split; [|exact (proj1 HFP)].
      (* the jal's own return pc, a literal of the listing, is below the allocation ceiling (fpre's fourth conjunct,
         the kit owner's 2026-10-29 ruling; PItems_entry.v:1485-1489's discharge) *)
      unfold raZ. rewrite R1.
      pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CRr. unfold ASAN_CEIL in CRr.
      let w := eval vm_compute in (VALb A_TEXT) in change (VALb A_TEXT) with w.
      rewrite unsigned_lit_small by lia. lia.
    + exact Eclo.
    + exact (ex_intro _ ch2 HCH2).
    + exact HCLO.
    + (* THE CURSOR SET: the trace of parse_string's free reads the word at s0 - 8 = q - 8, the entry's (prh_cw_entry) *)
      intros r w Hr Hw. rewrite PS0, AVM in Hw. apply (Ecw F_parse_string r w (or_introl eq_refl) Hr). rewrite PS0.
      apply (pik_word_call regs0 regs W mem Wc memc e q v (q - 8) w HFRM); first [lia | exact Hvw | exact Hw].
    + rewrite Usp. lia.
    + exact (proj1 HROOM).
    + exact HWRc.
    + exact (LC _ _ Epk1).
    + exact (LC _ _ Epk2).
    + exact HHB.
    + exact Ra0.
    + exact HINm.
    + exact Hpcl.
    + exact Hq34.
    + exact HWIN.
    + rewrite Usp. lia.
    + rewrite Usp, Fsp. unfold PI_FRAME. lia.
    + exact HRAm.
    + exact HSRCm.
    + exact HHOME.
    + exact HLGm.
    + lia.
    + exact (conj HRQ HLV).
  - intros a (r & Hr & Ha). left. exists r. split; [|exact Ha].
    destruct Hr as [<- | []]. left. reflexivity. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW1 & HJ2 & HJ1 & HX & HP & HPOST & HMNk).
(* the caller's budget after the call: parse_string's own is at wbudget CW 0 (the SAME CW) *)
assert (HWS2 : YCbqGwild.wbudget CW 0 (WS0 ++ WS1)).
{ change 0%nat with (0 + 0)%nat. apply YCbqGwild.wbudget_app; [exact HWS | exact HPW1]. }
pose proof (HMNk HMN) as HMN2. clear HMNk.
assert (HKS : aregs_preserved regs regs2).
{ intros r Hr. rewrite (HP r Hr). unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  rewrite (st_ok_restrict_reg SEGS (w_H Wc) E0 _ ms _ HS);
  lazymatch goal with |- context [sr_get ?l ?r] => let x := eval vm_compute in (sr_get l r) in
    change (sr_get l r) with x end;
  cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity. }
replace (Z_to_bv 64 (VALb A_TEXT + 25924)) with (w64 (VALb A_TEXT + PIATb PIK_O_STRR))
  by (unfold w64; f_equal; vm_compute; reflexivity).
replace (spZ regs0 + e + - (PI_FRAME + e) + (PI_FRAME + e)) with (spZ regs + (PI_FRAME + e)) in HJ1
  by (unfold PI_FRAME; lia).
apply (pik_k3_holds d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail
  ran most own kr lyc Sc Hpc Wc memc (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc) k regs f n cap acc kids keys
  Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc ly2 S2 Hp2 W2 mem2 md2 k1 regs2 (WS0 ++ WS1) WS1
  HFP HENT HMN2 HFRM HREGS HRB H21 HIN Hpcl Hq34 MEQ HARc HJ2 HWS2 HJ1).
- intros a Ha Hn. apply HX; [unfold PI_FRAME in *; lia | exact Hn].
- exact HKS.
- exact HPOST.
Qed.

(* ---- The batch kit: from the first skip_ws's return (0x87bc8) on ---- *)
Lemma pik_k1_holds : forall d CTX0 CW N,
  pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pik_k1_spec d CTX0 CW N.
Proof.
intros d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail ran most own
  kr lyc Sc Hpc Wc memc memr mdc k regs f n cap acc kids keys Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc
  ly2 S2 Hp2 W2 mem2 md2 k1 regs2 WS0
  HFP HENT HMN HSeq HFRM HREGS HRB H21 HIN MEQ HARm HJ2w HWS HJ1 HX HKS Hrk HHp Hab Hled2 Hin2.
(* THE BUDGETED JOURNAL: the runs take it rebased at the return state's depot; every hand-off steps back to WS0 *)
pose proof (ajxR_wild HJ2w) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2w) as HJ2.
destruct HIN as (HCUR & HN & Hncap & HCONT & HDEP & HAP & HPERM & HFU & HEQ & HLED & HBLK & HPOSB & HLIVE & HBB & HOK & HLS
  & HROOM & HGR & Hcapn & HNCAPS & af & HFORD & HFLB).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HENT as (Emn & _ & _ & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & _).
(* the travelling position and live requests at the return state: skip_ws keeps the state (S2 = Sc) *)
assert (HPOSB2 : PItems_posb.pi_posb S S2 tr0) by exact (PItems_posb.pi_posb_eq S Sc S2 tr0 HSeq HPOSB).
assert (HLIVE2 : PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
  (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) tr0) by (rewrite HSeq; exact HLIVE).
pose proof RDP as (_ & _ & _ & _ & _ & Hfwin & Hspq & Hqe & _ & _ & _ & _ & HPV & Hqv & Htv & Hvw & _ & HdM & _).
pose proof HPV as (Hv4096 & Hv8 & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
pose proof HJ2 as (HAR2 & HLY2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo2 & Eshi2 & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs1 & _).
pose proof (pik_stk_skw d) as HSTKB. pose proof (PIK_FR0 F_skip_ws) as HSKW0.
unfold STK_skip_ws, PI_FRAME in HSTKB.
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
(* the registers at the return site: skip_ws keeps every callee-saved one *)
assert (R9 : getr regs2 9 = w64 q) by (rewrite <- Q9; exact (HKS 9 ltac:(unfold acallee_saved; lia))).
assert (R8 : getr regs2 8 = w64 (q + 16)) by (rewrite <- Q8; exact (HKS 8 ltac:(unfold acallee_saved; lia))).
assert (R18 : getr regs2 18 = w64 1) by (rewrite <- Q18; exact (HKS 18 ltac:(unfold acallee_saved; lia))).
assert (R19 : getr regs2 19 = w64 v) by (rewrite <- Q19; exact (HKS 19 ltac:(unfold acallee_saved; lia))).
assert (R20 : getr regs2 20 = w64 (q + 8)) by (rewrite <- Q20; exact (HKS 20 ltac:(unfold acallee_saved; lia))).
assert (R21 : getr regs2 21 = w64 (-1)) by (rewrite <- H21; exact (HKS 21 ltac:(unfold acallee_saved; lia))).
assert (R23 : getr regs2 23 = w64 (pi_sh (q + 8))) by (rewrite <- Q23; exact (HKS 23 ltac:(unfold acallee_saved; lia))).
assert (R25 : getr regs2 25 = w64 (pi_sh (q + 16))) by (rewrite <- Q25; exact (HKS 25 ltac:(unfold acallee_saved; lia))).
assert (R26 : getr regs2 26 = w64 SHADOW_OFF) by (rewrite <- Q26; exact (HKS 26 ltac:(unfold acallee_saved; lia))).
assert (R27 : getr regs2 27 = w64 (pi_sh q)) by (rewrite <- Q27; exact (HKS 27 ltac:(unfold acallee_saved; lia))).
assert (R2 : getr regs2 2 = getr regs 2) by exact (HKS 2 ltac:(unfold acallee_saved; lia)).
assert (R3 : getr regs2 3 = getr regs 3) by exact (HKS 3 ltac:(unfold acallee_saved; lia)).
assert (R4 : getr regs2 4 = getr regs 4) by exact (HKS 4 ltac:(unfold acallee_saved; lia)).
(* the cursor skip_ws left *)
set (y := rest_atR tb text pc) in *.
set (p1 := text + len - Z.of_nat (length (PjGrammar.skip y))) in *.
pose proof Hin2 as (Vp2 & Ve2 & Vd2 & Hrw2 & _ & _ & _ & Hple2 & _ & HG2 & _ & _).
pose proof (PjGrammar.skip_len y) as Hsk.
assert (Hly : Z.of_nat (length y) = text + len - pc) by (unfold y, rest_atR; rewrite length_skipn; lia).
assert (Hlr1 : length (rest_atR tb text p1) = length (PjGrammar.skip y)) by (unfold rest_atR; rewrite length_skipn; lia).
pose proof HJ1 as (_ & HLY1 & _). cbn [app] in Hfrs1.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold ASAN_CEIL in CR.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof HPV as (_ & _ & _ & _ & _ & Hvam & _).
(* the cursor, the text, the node's place and the ledger at the return state (the shared kept statement) *)
assert (HCUR2 : pi_cur (L := Lb) (PA := PIb) B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 p1 Lamc peakc cntc failc ranc
  most own).
{ apply (HKC (wle' SEGS YGcfRehidePost.RZ_cf) regs0 e q v text len tb d lyc Sc Hpc Wc memr mdc pc Lamc peakc cntc
    failc ranc most own
    STK_skip_ws (spZ regs) (PI_FRAME + e) [(q, q + 8)] [] ly2 S2 Hp2 W2 mem2 md2 k1 p1 Lamc peakc cntc failc ranc most own
    []).
  - exact (pik_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc memr pc Lamc peakc cntc failc ranc most own MEQ HCUR).
  - exact HJ1.
  - exact HX.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - lia.
  - destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | Hro] | (b & m & Hbin & _ & Hb1 & Hb2)].
    + right; right. pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HHB.
      pose proof (proj1 (Forall_forall _ _) HHB _ Hbin) as (K0 & Kin & _). cbn [fst snd] in K0, Kin.
      exists (b - cf_head), (m + cf_head). split; [exact Kin | lia].
    + destruct Hro as [Hro | Hki]; [left; exact Hro | right; left; exact Hki].
    + right; right. exists b, m. auto.
  - intros b m Hbin _. rewrite Hab, HHp. split; [exact Hbin | tauto].
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. unfold shadow_of_addr in Hra.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. unfold shadow_of_addr in Hra.
    unfold amem_range in Hvam. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - intros (r & Hr & H0). destruct Hr as [<- | []]. cbn [fst snd] in H0. lia.
  - left. exact Hin2.
  - exact Hled2.
  - rewrite Hlr1. lia.
  - left. reflexivity.
  - intros a k' Hk' _. exact Hk'.
  - lia.
  - lia.
  - intros a k' Hk'. left. exact Hk'.
  - exact HARm. }
pose proof HCUR2 as (_ & HRA2 & HSRC2 & HHOME2 & HPLAT2 & HRAV2 & HLG2 & HCNT2).
pose proof HSRC2 as (_ & _ & _ & _ & Htra2 & _). rewrite Hlen in Htra2.
assert (Hqb : 4096 <= q <= 2 ^ 47 - 24) by lia.
assert (AVR : forall (H : word -> bool) m m' a, mrestrict H m' = mrestrict H m -> aview SEGS H m' a = aview SEGS H m a)
  by (intros H m m' a Em; unfold aview; rewrite Em; reflexivity).
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLG) as HHBc.
pose proof HLED as (_ & _ & _ & HLP & _).
assert (HINCL : incl (pi_sblk true kids keys cap ++ Di) Lamc).
{ intros b Hb. apply (Permutation_in b (Permutation_sym HLP)). apply in_or_app. left.
  exact (Permutation_in b (Permutation_sym HPERM) Hb). }
pose proof HJ1 as (HAR1 & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
(* the container's footprint at the return state is what it was at the call (skip_ws writes the cursor only) *)
assert (AGR2 : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2)
  (pj_footR v (pi_sblk true kids keys cap ++ Di))).
{ rewrite <- MEQ.
  apply (pik_agree_call regs0 e v lyc Sc Hpc Wc memr mdc Lamc peakc cntc failc ranc most own STK_skip_ws (spZ regs)
    (PI_FRAME + e) [(q, q + 8)] ly2 S2 Hp2 W2 mem2 md2 k1 (pi_sblk true kids keys cap ++ Di) []).
  - exact (pik_ledger_rdeq lyc Sc Hpc Wc memc memr Lamc peakc cntc failc ranc most own MEQ HLG).
  - exact HPLAT.
  - exact Hvw.
  - lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. lia.
  - exact HJ1.
  - exact HX.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - intros a Ha (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - intros b Hb. rewrite Hab. exact Hb.
  - exact HINCL.
  - intros a ((a0 & k0) & Hb & Hab0) (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    unfold pj_holdsR in Hab0. cbn [fst snd] in Hab0.
    pose proof (proj1 (Forall_forall _ _) HHBc (a0, k0) (HINCL _ Hb)) as (Hk0 & Hb0 & _ & _ & _).
    cbn [fst snd] in Hk0, Hb0. rewrite <- Hab in Hb0.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR1 Hb0) as (_ & B2 & B3 & _).
    assert (RSk : k0 + cf_head <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    lia. }
(* A REFUSAL AT THE EPILOGUE before the key's block: s5 = -1, the frame and the kit's None arm (the journal back at WS0) *)
assert (EXIT : forall mem' md' k' (regs' : bvmap 5 word),
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem' md' k' WS0 ->
  YAkMemnorm.memnorm SEGS mem' ->
  mrestrict (w_H W2) mem' = mrestrict (w_H W2) mem2 ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 21 = w64 (-1) ->
  (forall ok1, jr_name true y ok1 = (None, [], ok1)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fxc) SEGS (VALb A_TEXT + PIATb PI_O_EPI) regs' mem' md')
    (fpostWFbm (fx := fx0) (L := Lb) (PA := PIb) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v)
       regs0 ly S Hp W mem md
       (pi_post (L := Lb) (PA := PIb) B ly S d true tb text len p q v Lam peak cnt fail ran most own kr))).
{ intros mem' md' k' regs' HJx HMNx MEQx Rsp R3x R4x R21x HNAME.
  apply (pik_epi_exit d (YCbqGwild.wbudget CW 0) fxc fx0 ly S Hp W mem md regs0 e q v tb text len p Lam peak cnt fail
    ran most own kr ly2 S2 Hp2 W2 mem' md' k' regs' WS0 HJx HWS HFP HMNx).
  - apply (pik_frame_win regs0 regs regs' W mem Wc W2 memc mem' e q v HFRM Rsp R3x R4x Hspq).
    intros a Ha Hn. rewrite (AVR _ _ _ a MEQx), (AVR _ _ _ a (eq_sym MEQ)).
    apply HX; [unfold PI_FRAME; lia|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia.
  - exact R21x.
  - intros regsx H10.
    apply (pik_refuse d ly S tb text len p q v Lam peak cnt fail ran most own kr lyc Sc Wc memc
      f n cap acc kids keys Di pc
      ok0 tr0 D0 Lamc peakc cntc failc ranc ly2 S2 Hp2 W2 mem' p1 af HCONT HDEP HAP HPERM HEQ HLED HBLK HBB HLS HdM
      Hncap HNAME HGR HFORD HFLB).
    + exact (pik_ledger_rdeq ly2 S2 Hp2 W2 mem2 mem' Lamc peakc cntc failc ranc most own MEQx Hled2).
    + exact (Hrk (proj1 HROOM)).
    + exact HPOSB2.
    + exact HLIVE2.
    + exact Hab.
    + exact Hfrs1.
    + rewrite MEQx. exact AGR2.
    + rewrite MEQx. exact Hin2.
    + exact H10. }
unfold SRr', cfg_at.
(* the runner carrying the overlay's normality from the run's start memory to its end (YC1fPx's _inv twin) *)
pose (RUN := paj_run_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fxc) (L := Lb) (PI := PIb) (wle' SEGS YGcfRehidePost.RZ_cf)).
assert (HSK : PjGrammar.skip y = rest_atR tb text p1).
{ unfold y. etransitivity; [apply pik_skip_rest; lia|]. f_equal. unfold p1, y. lia. }
destruct (Z_lt_dec p1 (text + len)) as [Hlt | Hge].
- (* THE CURSOR IS ON A BYTE c *)
  set (c := nth (Z.to_nat (p1 - text)) tb 0).
  destruct (HG2 (Z.to_nat (p1 - text)) ltac:(lia)) as [Vc0 Hc256].
  replace (text + Z.of_nat (Z.to_nat (p1 - text))) with p1 in Vc0 by lia.
  pose proof (pik1_st_ok fxc W2 mem2 regs2 q p1 (text + len) c true (PIATb PIK_O_SKW1R) R9 R8 R20 R26 R27 R25 R23 R18
    Hqb Hq8 ltac:(lia) ltac:(lia) Hc256 ltac:(intros _; lia) Vp2 Ve2 (fun _ => Vc0)) as HS.
  remember (Eimg (PI := PIb) (Ereg regs2 [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 c])) as E eqn:HE in HS.
  assert (HEI : img_env VALb A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 p1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 c) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (SHOK : sh_ok SEGS pik_Bx1 (pik1_SH true) E (mrestrict (w_H W2) mem2)).
  { unfold pik1_SH. cbn [app]. constructor; [|constructor; [|constructor]].
    - apply (shent_ok_of_range SEGS (w_H W2) mem2 E pik_Bx1 32 text len p1 0 1 Htra2);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 32 p1 E32) by lia; reflexivity | lia | lia
      | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; unfold SHADOW_OFF; lia].
    - apply (shent_ok_of_range SEGS (w_H W2) mem2 E pik_Bx1 9 q 24 q 0 24 HRA2);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs2 rk).
  { intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
    rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ nk rk Hk). }
  clear HE.
  change (w64 (VALb A_TEXT + PIATb PIK_O_SKW1R)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_SKW1R)).
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN BAND_SPAN.
  { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ1 : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) mem2).
  { apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
    unfold pik1_ss in Hin; cbn [ss_mem] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
  clear HF HFr HG.
  (* 0x87be4 bgeu p1, end: the cursor is on a byte, so the branch to the epilogue is not taken *)
  psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
  { exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec p1 (text + len)); [discriminate Hc | lia]. }
  (* 0x87be8 beqz p1 (UBSan null check): NOT TAKEN, decided by the run from atom 32's fact p1 >= 4096; the 1-byte
     shadow probe of *p1 (0x87bf8) is covered by the entry mkSHE 32 0 1; then the byte and the quote test *)
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN BAND_SPAN.
  { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ2 : mrestrict (w_H W2) (ms_mem ms0) = mrestrict (w_H W2) mem2).
  { rewrite <- MEQ1. apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
    unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
  clear HF HFr HG.
  rewrite (pik_rest_cons tb text p1) in HSK by lia. fold c in HSK.
  (* 0x87c04 bne c, 34 *)
  psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
  { (* 0x87c04 TAKEN: the byte is not a quote; jr_name refuses with no event: the kit's None arm at the epilogue *)
    assert (Hc34 : c <> 34).
    { intros Ec. rewrite branch_ne_U, U_SOff in Hc0. cbn [ew ewset extK Nat.eqb] in Hc0.
      rewrite U34, Z.add_0_r, zcanon_id in Hc0 by (unfold M64; lia). rewrite Ec in Hc0. vm_compute in Hc0.
      discriminate Hc0. }
    paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN BAND_SPAN (PIATb PI_O_EPI).
    { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
    lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
      assert (MEQ3 : mrestrict (w_H W2) (ms_mem msx) = mrestrict (w_H W2) mem2) end.
    { rewrite <- MEQ2. apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
      unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
    prreg HS (21%bv : bv 5) R21'. prreg HS (2%bv : bv 5) R2'. prreg HS (3%bv : bv 5) R3'.
    prreg HS (4%bv : bv 5) R4'.
    pmkst HS.
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
      replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
    apply (EXIT _ _ _ _
      (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD)
      HMN MEQ3).
    - unfold spZ. rewrite R2', (EK 2%nat 2%bv eq_refl), R2. reflexivity.
    - rewrite R3', (EK 3%nat 3%bv eq_refl), R3. reflexivity.
    - rewrite R4', (EK 4%nat 4%bv eq_refl), R4. reflexivity.
    - rewrite R21'. apply bv_eq. reflexivity.
    - apply pik_name_refuse. rewrite HSK. exact Hc34. }
  (* 0x87c04 NOT TAKEN: the byte is a quote; 0x87c08 mv a0, s1; 0x87c0c jal parse_string *)
  assert (Hq34 : c = 34).
  { rewrite branch_ne_U, U_SOff in Hc0. cbn [ew ewset extK Nat.eqb] in Hc0.
    rewrite U34, Z.add_0_r, zcanon_id in Hc0 by (unfold M64; lia).
    destruct (Z.eqb_spec c 34) as [Ec | Ec]; [exact Ec|]. exfalso.
    change (U (ewset (ewset E 512 w) 513 w0) (SLit 34)) with 34 in Hc0.
    rewrite (proj2 (Z.eqb_neq c 34) Ec) in Hc0. discriminate Hc0. }
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN BAND_SPAN (PIATb PIK_O_STR).
  { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  lazymatch goal with HS' : st_ok_pi _ _ ?E' _ (restrict _ ?msx) |- _ =>
    assert (MEQ3 : mrestrict (w_H W2) (ms_mem msx) = mrestrict (w_H W2) mem2);
    [ rewrite <- MEQ2; apply functional_extensionality; intros x; apply HFr; intros (r & Hin & Ha);
      unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin;
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia
    | ];
    assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E' (SOff 9 x) = Z_to_bv 64 (q + x));
    [ intros x Hx; rewrite denot_lit_U, U_SOff; cbn [ew ewset extK Nat.eqb];
      rewrite E9, unsigned_lit_small, zcanon_id by (unfold M64; lia); reflexivity
    | ];
    assert (D26 : ew E' 26 = Z_to_bv 64 SHADOW_OFF) by (cbn [ew ewset extK Nat.eqb]; exact E26)
  end.
  prreg HS (2%bv : bv 5) R2'. prreg HS (3%bv : bv 5) R3'. prreg HS (4%bv : bv 5) R4'.
  prreg HS (8%bv : bv 5) R8'. prreg HS (9%bv : bv 5) R9'. prreg HS (18%bv : bv 5) R18'.
  prreg HS (19%bv : bv 5) R19'. prreg HS (20%bv : bv 5) R20'. prreg HS (21%bv : bv 5) R21'.
  prreg HS (22%bv : bv 5) R22'. prreg HS (24%bv : bv 5) R24'. prreg HS (26%bv : bv 5) R26'.
  prregx HS (23%bv : bv 5) R23'. prregx HS (25%bv : bv 5) R25'. prregx HS (27%bv : bv 5) R27'.
  assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (WIN : forall a, spZ regs <= a < spZ regs0 + e -> ~ (q <= a < q + 8) ->
    aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn. rewrite (AVR _ _ _ a MEQ3), (AVR _ _ _ a (eq_sym MEQ)).
    apply HX; [unfold PI_FRAME; lia|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra. lia. }
  assert (Rsp : spZ (ms_regs ms1) = spZ regs) by (unfold spZ; rewrite R2', (EK 2%nat 2%bv eq_refl), R2; reflexivity).
  assert (R22 : getr regs2 22 = getr regs 22) by exact (HKS 22 ltac:(unfold acallee_saved; lia)).
  assert (R24 : getr regs2 24 = getr regs 24) by exact (HKS 24 ltac:(unfold acallee_saved; lia)).
  pose proof HRB as (B22 & B24 & BV0 & BV32 & BV24 & BV16 & BV8).
  assert (VW : forall a x, spZ regs <= a -> a + 8 <= spZ regs + 40 ->
    val_mem SEGS (mrestrict (w_H Wc) memc) a 8 x -> val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) a 8 x).
  { intros a x Ha1 Ha2 Hv. apply (pik_val_win Wc W2 memc (ms_mem ms1) a 8 x); [|exact Hv].
    intros kk Hk. apply WIN; lia. }
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VALb A_TEXT + PIATb PIK_O_STR)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  apply (pik_k2_holds d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt
    fail ran most own kr ly2 S2 Hp2 W2 (ms_mem ms1) _ (k + k1) (ms_regs ms1) f n cap acc kids keys Di p1 ok0 tr0 D0 Lamc
    peakc cntc failc ranc WS0).
  + unfold pi_ajR.
    exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD).
  + exact HWS.
  + exact HFP.
  + exact HENT.
  + exact HMN.
  + apply (pik_frame_win regs0 regs (ms_regs ms1) W mem Wc W2 memc (ms_mem ms1) e q v HFRM Rsp); [| | exact Hspq |].
    * rewrite R3', (EK 3%nat 3%bv eq_refl), R3. reflexivity.
    * rewrite R4', (EK 4%nat 4%bv eq_refl), R4. reflexivity.
    * intros a Ha Hn. apply WIN; [lia | exact Hn].
  + unfold pi_regs. rewrite R9', R19', R18', R8', R20', R26', R27', R25', R23', U9.
    rewrite (EK 9%nat 9%bv eq_refl), (EK 19%nat 19%bv eq_refl), (EK 26%nat 26%bv eq_refl), R9, R19, R26.
    rewrite (pi_denot_shx' _ 9 0 SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) D26 ltac:(lia)
      ltac:(unfold SHADOW_OFF; lia)).
    rewrite (pi_denot_shx' _ 9 16 SHADOW_OFF (q + 16) ltac:(apply D9; lia) D26 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
    rewrite (pi_denot_shx' _ 9 8 SHADOW_OFF (q + 8) ltac:(apply D9; lia) D26 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
    unfold pi_sh, w64. repeat split; reflexivity.
  + unfold pi_regs_body. rewrite R22', R24', (EK 22%nat 22%bv eq_refl), (EK 24%nat 24%bv eq_refl), R22, R24, Rsp.
    split; [exact B22|]. split; [exact B24|].
    split; [apply VW; [lia | lia | exact BV0]|]. split; [apply VW; [lia | lia | exact BV32]|].
    split; [apply VW; [lia | lia | exact BV24]|]. split; [apply VW; [lia | lia | exact BV16]|].
    apply VW; [lia | lia | exact BV8].
  + rewrite R21'. apply bv_eq. reflexivity.
  + split; [exact (pik_cur_rdeq regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 (ms_mem ms1) p1 Lamc peakc cntc failc
      ranc most own MEQ3 HCUR2)|].
    pose proof (PjGrammar.skip_len y) as Hsky.
    split; [rewrite Hlr1; lia|].
    split; [exact Hncap|].
    split; [rewrite MEQ3; exact (pi_cont_frame (L := Lb) (PA := PIb) _ _ _ true v kids keys n cap acc Di HCONT AGR2)|].
    split; [exact HDEP|]. split; [exact HAP|]. split; [exact HPERM|].
    split; [rewrite Hlr1; lia|].
    assert (HSK2 : PjGrammar.skip y = PjGrammar.skip (rest_atR tb text p1)).
    { rewrite HSK, (pik_rest_cons tb text p1) by lia. fold c. rewrite Hq34. reflexivity. }
    split.
    { unfold pi_run_eqB. intros ok1 r t ok2 Hj. apply HEQ.
      rewrite (pik_jrb_skip f (Nat.succ d) n cap (rev acc) y _ HSK2 ok1). exact Hj. }
    split; [exact HLED|].
    split.
    { destruct HBLK as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [rewrite Hab; exact B2|].
      split; [rewrite Hfrs1; exact B3 | exact B4]. }
    (* the travelling position and live requests: skip_ws made no event and kept the state *)
    split; [exact HPOSB2|]. split; [exact HLIVE2|].
    split; [rewrite (blocks_bytes_bsum B ly2 S2), Hab, <- (blocks_bytes_bsum B lyc Sc); exact HBB|].
    split; [exact HOK|]. split; [exact HLS|].
    split.
    { destruct HROOM as (RM1 & RM2 & RM3).
      unfold rd_room. rewrite <- (pik_jrb_skip f (Nat.succ d) n cap (rev acc) y _ HSK2 []).
      split; [exact (Hrk RM1)|]. split; [exact RM2|].
      (* the live bytes per event: skip_ws kept the state (S2 = Sc) *)
      rewrite HSeq. exact RM3. }
    (* THE BATCH KIT'S TAIL: the granted prefix and the capacity unchanged; the completed slots' capacities and free order
       read through the bytes pi_cont reads, which skip_ws kept; the model reads the rest through the skip *)
    pose proof (pik_agree_ufoot _ _ v kids keys n cap Di ltac:(lia) AGR2) as AGU2.
    split; [exact HGR|]. split; [exact Hcapn|].
    split; [rewrite MEQ3; exact (pvm_ncaps_frame (w_H Wc) memc (mrestrict (w_H W2) mem2) (prh_lin Lamc) true v kids keys
      n cap acc Di HCONT HNCAPS AGU2)|].
    exists af. split.
    * rewrite MEQ3. exact (pvm_forder_frame _ _ _ _ _ v _ _ _ _ _ _ HFORD (fun x k H => H) AGU2).
    * intros ok1. rewrite (HFLB ok1). apply pik_jfb_skip. exact HSK2.
  + lia.
  + rewrite <- Hq34. unfold c. apply nth_error_nth'. lia.
- (* THE CURSOR IS AT THE END: skip_ws found no byte, jr_name refuses *)
  assert (Ep1 : p1 = text + len) by lia.
  pose proof (pik1_st_ok fxc W2 mem2 regs2 q p1 (text + len) 0 false (PIATb PIK_O_SKW1R) R9 R8 R20 R26 R27 R25 R23 R18
    Hqb Hq8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros C; discriminate C) Vp2 Ve2 ltac:(intros C; discriminate C))
    as HS.
  remember (Eimg (PI := PIb) (Ereg regs2 [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 0])) as E eqn:HE in HS.
  assert (HEI : img_env VALb A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E nk = getr regs2 rk).
  { intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
    rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ nk rk Hk). }
  assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (EK 9%nat 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EK 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 p1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (SHOK : sh_ok SEGS pik_Bx1 (pik1_SH false) E (mrestrict (w_H W2) mem2)).
  { unfold pik1_SH. cbn [app]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W2) mem2 E pik_Bx1 9 q 24 q 0 24 HRA2);
      [unfold pik_Bx1; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
      | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  clear HE.
  change (w64 (VALb A_TEXT + PIATb PIK_O_SKW1R)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PIK_O_SKW1R)).
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN BAND_SPAN.
  { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ1 : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) mem2).
  { apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
    unfold pik1_ss in Hin; cbn [ss_mem] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
    destruct Hin as [<- | []]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
  clear HF HFr HG.
  (* 0x87be4 bgeu p1, end: TAKEN, the cursor is at the end *)
  psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
  { paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN BAND_SPAN (PIATb PI_O_EPI).
    { unfold pik1_ss; cbn [ss_mem]; unfold pik1_smem; cbn [app];
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
    lazymatch goal with HS' : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
      assert (MEQ3 : mrestrict (w_H W2) (ms_mem msx) = mrestrict (w_H W2) mem2) end.
    { rewrite <- MEQ1. apply functional_extensionality; intros x. apply HFr. intros (r & Hin & Ha).
      unfold pik1_ss in Hin; cbn [ss_mem add_cond] in Hin; unfold pik1_smem in Hin; cbn [app] in Hin.
      destruct Hin as [<- | []]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
    prreg HS (21%bv : bv 5) R21'. prreg HS (2%bv : bv 5) R2'. prreg HS (3%bv : bv 5) R3'.
    prreg HS (4%bv : bv 5) R4'.
    pmkst HS.
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
      replace pcw with (w64 (VALb A_TEXT + PIATb PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
    apply (EXIT _ _ _ _
      (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD)
      HMN MEQ3).
    - unfold spZ. rewrite R2', (EK 2%nat 2%bv eq_refl), R2. reflexivity.
    - rewrite R3', (EK 3%nat 3%bv eq_refl), R3. reflexivity.
    - rewrite R4', (EK 4%nat 4%bv eq_refl), R4. reflexivity.
    - rewrite R21'. apply bv_eq. reflexivity.
    - apply pik_name_refuse. rewrite HSK, Ep1. replace len with (Z.of_nat (length tb)) by lia.
      rewrite pik_rest_end. exact I. }
  { (* 0x87be4 not taken: impossible, p1 = end *)
    exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec p1 (text + len)); [lia | discriminate Hc]. }
Qed.

Theorem pi_key_holds : forall d CTX0 CW N,
  pi_free_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pi_key_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N.
Proof.
intros d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most
  own kr lyc Sc Hpc Wc memc mdc k regs WS0 HJw HWS HPRE.
unfold pi_ajR in HJw.
(* THE BUDGETED JOURNAL: the run and the skip_ws call (an empty-budget callee) take it rebased at this block's depot;
   the batch kit takes the caller's journal back at WS0 (skip_ws stores nothing) *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
pose proof HPRE as (Ho & HFP & HENT & HMN & HFRM & HREGS & HRB & H21 & f & n & cap & acc & kids & keys & Di & pc & ok0 & tr0
  & D0 & Lamc & peakc & cntc & failc & ranc & HCUR & HN & Hncap & HCONT & HDEP & HAP & HPERM & HFU & HEQ & HLED
  & HBLK & HPOSB & HLIVE & HBB & HOK & HLS & HROOM & HGR & Hcapn & HNCAPS & af & HFORD & HFLB).
subst o.
pose proof HENT as (Emn & _ & _ & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & _).
pose proof RDP as (_ & _ & _ & _ & _ & Hfwin & Hspq & Hqe & _ & _ & _ & _ & HPV & _ & _ & _ & _ & _).
pose proof HPV as (Hv4096 & Hv8 & _).
pose proof HFRM as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
assert (Fsp' : spZ regs = spZ regs0 - 144) by (rewrite Fsp; reflexivity).
pose proof HREGS as (Q9 & Q19 & Q18 & Q8 & Q20 & Q26 & Q27 & Q25 & Q23).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof (pik_stk_skw d) as HSTKB.
pose proof (PIK_FR0 F_skip_ws) as HSKW0.
unfold pi_goalR, cfg_at.
remember (Eimg (PI := PIb) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env VALb A_LIM E0) by (subst E0; apply Eimg_env).
assert (E2 : ew E0 2 = getr regs 2) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E0 3 = getr regs 3) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E0 8 = getr regs 8) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E0 9 = getr regs 9) by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (HS : st_ok_pi (fx := fxc) SEGS VALb E0
  (mkSS (PIATb PI_O_KEY) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@YK11.mkst fxc regs (Z_to_bv 64 (VALb A_TEXT + PIATb PI_O_KEY)) memc (seg_rom SEGS)))).
{ rewrite (restrict_mkst_fx (fx := fxc)). apply (pa_entry_st_ok_full (fx := fxc) (L := Lb) (PI := PIb)).
  - subst E0. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - cbn; exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E0 (mrestrict (w_H Wc) memc)) by constructor.
(* the runner carrying the overlay's normality from the run's start memory to its end (YC1fPx's _inv twin) *)
pose (RUN := paj_run_x_invR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
change (w64 (VALb A_TEXT + PIATb PI_O_KEY)) with (Z_to_bv 64 (VALb A_TEXT + PIATb PI_O_KEY)).
paj_run_tok_x_inv RUN HS HJ SHOK HMN BAND_SPAN.
{ apply awr_ok_nil. }
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
cbn [ss_mem] in HF, HFr.
assert (MEQ : mrestrict (w_H Wc) (ms_mem ms) = mrestrict (w_H Wc) memc).
{ apply functional_extensionality; intros x. apply HFr. intros (r & Hin & _). exact (in_nil Hin). }
clear HF HFr HG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
unfold STK_skip_ws, PI_FRAME in HSTKB.
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
assert (Hqb : 4096 <= q /\ q + 24 <= 2 ^ 47) by lia.
pose proof (pik_cur_rdeq regs0 e q v text len tb d lyc Sc Hpc Wc memc (ms_mem ms) pc Lamc peakc cntc failc ranc most own MEQ HCUR)
  as HCURm.
pose proof HCURm as (HINm & HRAm & HSRCm & _ & _ & _ & HLGm & _).
assert (Usp : spZ (ms_regs ms) = spZ regs) by (unfold spZ; rewrite R2, E2; reflexivity).
assert (Us0 : s0Z (ms_regs ms) = q + 16).
{ unfold s0Z. rewrite R8, E8, Q8. apply unsigned_lit_small. lia. }
assert (Ra0 : getr (ms_regs ms) 10 = w64 q) by (rewrite R10, E9; exact Q9).
(* the frame-pointer chain the call sees: s0 = q + 16, whose two words below are the end and the cursor (the
   cursor lies in the text, below alloc_ceiling and so below q, so the chain stops there) *)
assert (HCH : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ regs) (q + 16) ch1).
{ destruct (Z_lt_le_dec (q + 16) (ly_top lyc - 16)) as [Hlt | Hge].
  - exists [(q + 16, text + len, pc)]. right.
    split; [lia|]. split; [exact Hlt|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
    split.
    + cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
      split; [replace (q + 16 - 8) with (q + 8) by lia;
              apply (pik_rdword_of_val (w_H Wc) (ms_mem ms) (q + 8) (text + len)); [rewrite MEQ; exact Ve | lia]|].
      split; [replace (q + 16 - 16) with q by lia;
              apply (pik_rdword_of_val (w_H Wc) (ms_mem ms) q pc); [rewrite MEQ; exact Vp | lia]|].
      split; [lia|].
      unfold bad_next. replace (pc <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + constructor; [cbn [fst]; lia | constructor].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH as (ch1 & HCH).
(* skip_ws, an empty-budget callee, on the rebased journal (its start state is S at this block's depot), by the call
   rule over the walk's relation; its plain text lifted (pik_skw_lift) *)
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (aj_call_xW_spR (SK := SK) SEGS B prh_pst ARx LAWS (pa_segs_low (PAImg := PIb))
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    Wc E0 _ ms
    (STK_parse_items d + e) (spZ regs0 + e) (rd_fp q v) ly _ Hp W mem md [] lyc Sc Hpc _ k
    STK_skip_ws (PI_FRAME + e) [(q, q + 8)] (- (PI_FRAME + e)) (Z_to_bv 64 (VALb A_TEXT + 25852)) ch1
    (fQmn (L := Lb) (PA := PIb) (ms_mem ms) (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf Sc -> room_live_cf S') /\ Hp' = Hpc /\ S' = Sc /\ ablocks B ly' S' = ablocks B lyc Sc /\
       prh_ledger (L := Lb) (PA := PIb) B ly' S' Hp' W' mem' Lamc peakc cntc failc ranc most own /\
       pj_in_okR SEGS (mrestrict (w_H W') mem') q text len
         (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text pc)))) (Z.of_nat d + 1) tb))
    HS eq_refl HJ).
  - rewrite Usp, Fsp. unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, He16 by lia; reflexivity].
  - unfold PI_FRAME. lia.
  - exact HSKW0.
  - unfold STK_skip_ws, PI_FRAME. lia.
  - unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.add_mod, He16 by lia; reflexivity.
  - lia.
  - rewrite R3, E3, F3. exact Egp.
  - rewrite R4, E4, F4. exact Etp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (pa_B_ok (PAImg := PIb)) as HB. pose proof (pa_val_range (PAImg := PIb) A_TEXT) as HBr.
    rewrite unsigned_lit_small by lia. vm_compute. discriminate.
  - replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) by (unfold PI_FRAME; lia). rewrite Us0. exact HCH.
  - intros HAF HWIN. cbn [ss_pc setpc].
    apply pik_skw_lift.
    refine (TSKW fxc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 (PI_FRAME + e) q text len pc (Z.of_nat d + 1) tb
      Lamc peakc cntc failc ranc most own _ _ _ _ _ _ _ _ _ _).
    + split; [exact HAF|]. split.
      { apply (pik_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact Erod].
        intros (r & Hr & H0). cbn [rd_fp In] in Hr.
        destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia. }
      pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
      split; [rewrite Usp; lia|].
      (* fpre's frm_zero at the call (FRM0-ENTRY): the block's own float state, pi_fpok's first half *)
      split; [|exact (proj1 HFP)].
      (* the jal's own return pc, a literal of the listing, is below the allocation ceiling (fpre's fourth conjunct,
         the kit owner's 2026-10-29 ruling; PItems_entry.v:1485-1489's discharge) *)
      unfold raZ. rewrite R1.
      pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CRr. unfold ASAN_CEIL in CRr.
      let w := eval vm_compute in (VALb A_TEXT) in change (VALb A_TEXT) with w.
      rewrite unsigned_lit_small by lia. lia.
    + exact Ra0.
    + exact HINm.
    + exact HWIN.
    + rewrite Usp. lia.
    + rewrite Usp, Fsp. unfold PI_FRAME. lia.
    + exact HRAm.
    + exact HSRCm.
    + exact HHOME.
    + exact HLGm.
  - intros a (r & Hr & Ha). left. exists r. split; [|exact Ha].
    destruct Hr as [<- | []]. left. reflexivity. }
(* back at the return site: the callee-saved registers are the call's, which are the block's own *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HP &
  (Hrk & HHp & HSeq & Hab & Hled2 & Hin2) & HMNk).
pose proof (HMNk HMN) as HMN2. clear HMNk.
assert (EK : forall nk (rk : bv 5), Z.of_nat nk = bv_unsigned rk -> ew E0 nk = getr regs rk).
{ intros nk rk Hk. pose proof (bv_unsigned_in_range 5 rk) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] nk rk Hk). }
assert (HKS : aregs_preserved regs regs2).
{ intros r Hr. rewrite (HP r Hr). unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  rewrite (st_ok_restrict_reg SEGS (w_H Wc) E0 _ ms _ HS);
  lazymatch goal with |- context [sr_get ?l ?r] => let x := eval vm_compute in (sr_get l r) in
    change (sr_get l r) with x end;
  cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EK; reflexivity. }
replace (Z_to_bv 64 (VALb A_TEXT + 25852)) with (w64 (VALb A_TEXT + PIATb PIK_O_SKW1R))
  by (unfold w64; f_equal; vm_compute; reflexivity).
replace (spZ regs0 + e + - (PI_FRAME + e) + (PI_FRAME + e)) with (spZ regs + (PI_FRAME + e)) in HJ1
  by (unfold PI_FRAME; lia).
apply (pik_k1_holds d CTX0 CW N HFREE HVALN fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p Lam peak cnt fail
  ran most own kr lyc Sc Hpc Wc memc (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc) k regs f n cap acc kids keys
  Di pc ok0 tr0 D0 Lamc peakc cntc failc ranc
  ly2 S2 Hp2 W2 mem2 md2 k1 regs2 WS0 HFP HENT HMN2 HSeq HFRM HREGS HRB H21).
- exact (conj HCUR (conj HN (conj Hncap (conj HCONT (conj HDEP (conj HAP (conj HPERM (conj HFU (conj HEQ
    (conj HLED (conj HBLK (conj HPOSB (conj HLIVE (conj HBB (conj HOK (conj HLS (conj HROOM
    (conj HGR (conj Hcapn (conj HNCAPS (ex_intro _ af (conj HFORD HFLB)))))))))))))))))))))).
- exact MEQ.
- exact HARc.
- exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HWD).
- exact HWS.
- exact HJ1.
- intros a Ha Hn. apply HX; [unfold PI_FRAME in *; lia | exact Hn].
- exact HKS.
- exact Hrk.
- exact HHp.
- exact Hab.
- exact Hled2.
- exact Hin2.
Qed.

End body.
