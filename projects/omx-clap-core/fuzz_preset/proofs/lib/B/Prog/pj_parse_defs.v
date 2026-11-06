(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the CUTS of pj_parse's image-B' walk (fuzz_preset asan-ubsan, pin d663f82d7f488d30; B'
   0x862ec, 36 instructions; preset_file.c :296-309), on the kit's cwpj-fix f29626eb1667 (the batch kit's CUT 7cdbb61b5fa0 plus
   (the kit cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) plus the prh_cw_pj repair). STATEMENTS ONLY
   (and pjp_invR's two one-line lemmas): the entry record, the walk's final post (the kit's tpj_parse_specX post, by its kit name), the cut states,
   the segment statements (each proved by its own file) and the keep statements the segments share. lib/B/Prog/pj_parse_top.v composes them.
   proves no function (kind: statement text).
   The body (B' listing lib/B/Listing_prog.v, slots 4872..4907), pc offsets from pj_parse's entry (DERIVED, by
   vm_compute below):
     +0x00..+0x10  prologue: sp -= 48, ra at sp+40, s0 at sp+32, a1 := t0 + len, p := t0 at sp+8
     +0x14         UBSan PTR-OVF `bltu a1, a0`                  NOT TAKEN (src_rd: t0 + len does not wrap)
     +0x18..+0x24  s0 := out; nullness xor;  +0x28 UBSan NULL `beqz a0`  NOT TAKEN (4096 <= t0)
     +0x2c..+0x40  end at sp+16, depth 0 at sp+24, memset (out, 0, 56)
     +0x44..+0x4c  a0 := sp + 8, a1 := out                       CUT pjp_C1 at the `jal parse_value` (+0x4c)
     +0x50         bnez a0 (taken: refusal)                      CUT pjp_C2ok at +0x54 (the fall-through)
     +0x54..+0x64  a0 := sp + 8, skip_ws, reload p / end, beq       taken -> +0x84 (a0 := 0, j +0x74)
     +0x68..+0x70  a0 := s0, pj_free, a0 := -1                     CUT pjp_C2ref at +0x68
     +0x74..+0x80  ld ra, ld s0, sp += 48, ret                      CUT pjp_C3 at +0x74
   TEXTS: the kit's cwpj-fix f29626eb1667 (lib/A/PRH_FnPj.v blob 38a83863585f, PRH_FnParse.v, PRH_FnReader.v, PRH_Base.v
   (lib/A/PRH_FnPj.v (sha256 35457d119ddb; internal record), PRH_FnParse.v, PRH_FnReader.v, PRH_Base.v (sha256 ada75e4a39ad; internal record)):
   no run-word list DW (prh_univ_closure B CTX0; the cursor set CW and its room YCbqGwild.wild_room ..  CW 0), the
   budgeted posts (fpostWFbm at YCbqGwild.wbudget CW 0), the re-keyed prh_oks and the refusal peak, the outcome
   conjunct, the trees' free order (pj_foR) and CAP (pj_ncapR) in the reader posts.
   TARGET: the kit's tpj_parse_specX CTX0 CW ITSELF (PRH_FnPj.v :592-738), NO twin. The kit's repair of PRH_Base.prh_cw_pj
   (:1521-1527, the ruling FIX (i), 2026-10-30) keeps each cursor arm's FIRST disjunct only, so it is
   word for word the B' cursor set this walk proved under its twin on the cut (prh_cw_pjB / tpj_parse_specX_B_FIX,
   preset-tree-at-2026-10-30T09-35-36Z.tsv (sha256 60ab58a4fb09; internal record), the finding CWPJ-B); the twin is deleted. The B' cursor frees store the traces
   [pc0; r; t0 + len] (parse_items) and [pc0; r; w0] (parse_string, w0 the word at pj_parse's never-written slot
   sp - pi_frame F_pj_parse), and prh_cw_pj's two arms name exactly these. The one real caller, parse_noting, meets
   prh_cw_pj with its pn_cw (lib/B/Prog/PN102BCuts.v pn_cw_pj).
   Callee texts (pjp_texts, the batch kit's, at EVERY float state): parse_value = tparse_value_specX 0 CTX CTX0 CW (every CTX);
   skip_ws = tskip_ws_specX; pj_free = tpj_free_specX CTX0 DOC_D; __asan_memset = YGcallMxmn.aintrin_realizes_xm OSet.
   Every name is stated at PA := PI_prog_B.
   THE BUDGET: before the parse_value call the journal is at the empty budget (ajournal_x = ajournal_xw .. []); after it
   the cuts carry the journal REBASED (YCbqGwild.ajournal_xw_rebase: from the entry state with its depot set to the
   call's return depot dp, at the empty budget) and pjp_wb (that depot's wild part inside the entry's plus parse_value's
   budget WS, wbudget CW 0 WS); the exit unbases (ajournal_xw_unbase0) and closes at WS (fpostWF_xb_of_kept).
   MEMNORM is a STATE fact of every cut after the prologue (pjp_inv's last conjunct), seeded by the text's premise.
   THE RE-HIDING MOVE AND THE HULL (the texts' current form): parse_value and pj_free can hide shadow again, so the
   text and every segment conclude SRr' segs RZ_cf (YA0nH), and the journal of the cuts after parse_value's call is at
   wle' SEGS RZ_cf: pjp_invR is pjp_inv over a world relation R (a copy beside it; pjp_inv_R_wle checks the two by
   reflexivity), C1 uses pjp_inv (wle), C2ok / C2ref / C3 and the keep statement use pjp_invR at wle'. The text
   takes the hull budget hull_budget (parse_evs tl []) (pjp_pre's last conjunct); parse_value's use of its own list
   is carried by C2ok / C2ref (hull_used from the entry state); pj_free (out) uses none.
   THE OUTCOME OF AN INJECTED READING (the text's GUARDED conjunct): parse_value's conjunct of the same name, carried
   by C2ok / C2ref as pjp_inj.
   pjp_Q IS the text's post tpjP_Q (PRH_FnPj.v) at the entry's values.
   THE RUN POSITION: after parse_value the cuts carry its position transfer and live-set move (pjp_pos_pv) and its
   OUTCOME conjunct (pjp_outc); on the refused path the order list F of out's tree and its tie to the model's pj_frees
   come from parse_value's post (the batch kit: the tree's free order, under cf_head = HEAD, the walk's prh_head16).
   Numerals: 48 / 56 / 24 / 32 / 40 / 16 / 8 (LENGTH: frame, struct sizes, slot offsets); pc offsets DERIVED.
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.
(* image B's generated PrhImg values (frames, statics, return sites) as the instance every kit name reads *)
#[local] Existing Instance prh_img_B.

(* pc offsets of the cuts from pj_parse's entry (DERIVED from the listing: slot index differences times 4) *)
Definition PJP_PC : Z := B_prog_sigma AS_pj_parse - B_prog_base.
Definition PJP_C1 : Z := PJP_PC + 76.    (* the `jal parse_value` *)
Definition PJP_C2OK : Z := PJP_PC + 84.  (* after `bnez a0` falls through: parse_value returned 0 *)
Definition PJP_C2REF : Z := PJP_PC + 104. (* `mv a0, s0` before `jal pj_free` *)
Definition PJP_C3 : Z := PJP_PC + 116.   (* the epilogue `ld ra, 40(sp)` *)
Definition PJP_FR : Z := 48.             (* pj_parse's own frame (prh_img_B's pi_frame F_pj_parse) *)

(* the callee-saved registers pj_parse never writes: gp, tp, s1, s2 .. s11 (s0 and sp are restored by the epilogue) *)
Definition PJP_KEPT : list (bv 5) := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* the callee texts, the batch kit's, each at every float state; parse_value at every entry context CTX *)
Definition pjp_texts (CTX0 CW : list (list Z)) : Prop :=
  (forall (fy : YK11.FPState) (CTX : list (list Z)),
     tparse_value_specX (fx := fy) (PA := PA) B ARx SK 0%nat CTX CTX0 CW) /\
  (forall fy : YK11.FPState, tskip_ws_specX (fx := fy) (PA := PA) B ARx SK) /\
  (forall fy : YK11.FPState, tpj_free_specX (fx := fy) (PA := PA) B ARx SK CTX0 DOC_D) /\
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (pa_sigma AS___asan_memset).

(* ---- the entry ---- *)
Record PjpEnt : Type := MkPjpEnt {
  je_ly : alayout; je_S : astate; je_Hp : list Z; je_W : world SEGS; je_regs : bvmap 5 word;
  je_mem : word -> option byte; je_md : Model; je_ch : list (Z * Z * Z);
  je_d : Z; je_t0 : Z; je_len : Z; je_out : Z; je_tl : list Z; je_Lam : list (Z * Z);
  je_peak : Z; je_cnt : Z; je_fail : Z; je_ran : Z; je_most : Z; je_own : Z }.
Definition je_sp0 (en : PjpEnt) : Z := spZ (je_regs en).
Definition je_sp1 (en : PjpEnt) : Z := je_sp0 en - PJP_FR.

(* the premises of the kit's tpj_parse_specX, verbatim, at the entry float state fx. ORDER: the f97c walk's 26 positions
   kept (the cursor set prh_cw_pj in the third place, the room wild_room in the fourth, where the two DW memberships
   were), the kit's two NEW premises appended (the text's end below alloc_ceiling, RQ_pj_parse tl <= most), then the hull
   budget; pjp_compose reorders *)
Definition pjp_pre (CTX0 CW : list (list Z)) (en : PjpEnt) : Prop :=
  let ly := je_ly en in let S := je_S en in let Hp := je_Hp en in let W := je_W en in let regs := je_regs en in
  let mem := je_mem en in let md := je_md en in let ch := je_ch en in let d := je_d en in let t0 := je_t0 en in
  let len := je_len en in let out := je_out en in let tl := je_tl en in let Lam := je_Lam en in
  fpre (PA := PA) B ARx STK_pj_parse ly S Hp W regs mem md ch /\
  prh_univ_closure B CTX0 /\
  prh_cw_pj (PA := PA) B CW W mem regs t0 len /\
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) /\
  room_live_cf S /\ frm_zero (@YK11.fp_csr fx) /\
  getr regs 10 = w64 t0 /\ getr regs 11 = w64 len /\ getr regs 12 = w64 out /\
  Z.of_nat (length tl) = len /\ src_rd (PA := PA) W mem t0 tl /\ prhReader_home (PA := PA) B ly S Hp Lam t0 len /\
  Z.of_nat (PjRoundTrip.maxrun tl) < 2 ^ 30 /\
  fwin (PA := PA) ly W regs mem d /\ prhPj_slot (PA := PA) B STK_pj_parse d ly S Lam W regs mem out /\
  out < YM05.alloc_ceiling /\
  (forall a k, In (a, k) Lam -> out + 56 <= a \/ a + k <= out) /\
  (0 < len -> t0 + len <= out \/ out + 56 <= t0) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam (je_peak en) (je_cnt en) (je_fail en) (je_ran en) (je_most en) (je_own en) /\
  je_cnt en + 2 * len + 2 < 2 ^ 64 - 1 /\
  RQ_pj_parse tl + cf_head < cf_malloc_max /\
  blocks_bytes S + LIVE_pj_parse tl <= LIVE_MAX /\
  Z.of_nat (length (frames S)) + Z.of_nat DOC_D <= fs_frames 0 /\
  YAkMemnorm.memnorm SEGS mem /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod tl [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  t0 + len < YM05.alloc_ceiling /\
  RQ_pj_parse tl <= je_most en /\
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs ReaderRes.jr_strtod tl []).

(* parse_value's two facts about the model run that the later cuts carry, at a cut's state S, by the events of its
   trace tr (the batch kit's PRH_FnParse.v tparse_value_specX): its POSITION TRANSFER from the ENTRY state je_S en (no allocation
   happens before the call), and the LIVE REQUESTS, the entry's moved by those events (what pj_free (out)'s class-24
   bound after a refusal is read from) *)
Definition pjp_pos_pv (en : PjpEnt) (S : astate) (tr : list PjGrammar.ev) : Prop :=
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
   PresetRoomPos.iface_room_pos sm x os i H0 hist (je_S en) ->
   PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs tr) ->
   exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs tr))%nat H0 hist' S) /\
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (je_S en))) (PresetReqAt.rd_hevs tr)).

(* parse_value's OUTCOME conjunct (the batch kit's PRH_FnParse.v tparse_value_specX), at d = 0 over pj_parse's whole text, from the
   entry state je_S en to a cut's state S (the state after parse_value; skip_ws keeps it) *)
Definition pjp_outc (en : PjpEnt) (S : astate) (res : option (PjTree.jv * list Z)) (tr : list PjGrammar.ev)
  (ran' : Z) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (je_S en) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en)))) ->
  (je_fail en < je_cnt en \/ je_cnt en + Z.of_nat (PjGrammar.calls (prhPv_gtrace 0 (je_tl en))) <= je_fail en) ->
  ran' = je_ran en /\ fst (PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en) []) = (res, tr) /\
  exists hist', PresetRoomPos.iface_room_pos sm x os
    (i + length (PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en))))%nat H0 hist' S.

(* parse_value's OUTCOME OF AN INJECTED READING (PRH_FnParse.v tparse_value_specX, the GUARDED conjunct), at d = 0
   over pj_parse's whole text, from the entry state je_S en, for the outcomes ok and the trace tr the call met *)
Definition pjp_inj (en : PjpEnt) (ok : list bool) (tr : list PjGrammar.ev) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (je_S en) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en)
    (PresetReqAt.okk (Z.to_nat (je_fail en - je_cnt en))))))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value ReaderRes.jr_strtod 0
    (je_tl en) (PresetReqAt.okk (Z.to_nat (je_fail en - je_cnt en)))))))) ->
  je_cnt en <= je_fail en < je_cnt en + Z.of_nat (PjGrammar.calls (prhPv_gtrace 0 (je_tl en))) ->
  PRH_Base.prh_granted ok (je_cnt en) (je_fail en) (PjGrammar.calls tr).

(* the post of the text tpj_parse_specX: the kit's own name for it, PRH_FnPj.v tpjP_Q (tpjP_Q_check ties it to the
   text), at the entry's values *)
Definition pjp_Q (en : PjpEnt) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
    (word -> option byte) -> Model -> Prop :=
  tpjP_Q (PA := PA) B (je_most en) (je_own en) (je_ly en) (je_S en) (je_len en) (je_out en) (je_tl en) (je_Lam en)
    (je_peak en) (je_cnt en) (je_fail en) (je_ran en).

(* the walk's goal: the text's post at the entry float state fx, budgeted at wbudget CW 0, in the m-form *)
Definition pjp_FIN (CW : list (list Z)) (en : PjpEnt) : world SEGS -> config -> Prop :=
  fpostWFbm (PA := PA) B ARx SK (YCbqGwild.wbudget CW 0) STK_pj_parse (je_d en)
    [(je_out en, je_out en + 56)] (je_regs en) (je_ly en) (je_S en) (je_Hp en) (je_W en) (je_mem en) (je_md en)
    (pjp_Q en).

(* the configuration at a cut, at float state fy *)
Definition pjp_cfg (fy : YK11.FPState) (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (@YK11.mkst fy regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS)) md.

(* ---- what holds at every cut after the prologue, the journal from the base state Sb: the entry state je_S en up to
   the parse_value call, the entry state with its depot moved to the call's return depot after it (the rebase) ---- *)
Definition pjp_inv (en : PjpEnt) (Sb : astate) (fy : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  (* the float state: entry's, or what a float-changing callee left *)
  frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy /\
  (* the journal from the base state, at the caller-window widened window, footprint = the struct out *)
  AJ (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly S Hp W mem md k /\
  (* the caller's window, untouched (fpostWF's window clause; out is below alloc_ceiling, so not in it) *)
  (forall a, je_sp0 en <= a < je_sp0 en + je_d en ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (je_W en)) (je_mem en) a) /\
  (* pj_parse's frame: sp, the saved ra / s0, s0 = out, the untouched callee-saved registers, the frame present and
     its cursor bytes addressable *)
  spZ regs = je_sp1 en /\
  val_mem SEGS (rdW W mem) (je_sp1 en + 40) 8 (raZ (je_regs en)) /\
  val_mem SEGS (rdW W mem) (je_sp1 en + 32) 8 (s0Z (je_regs en)) /\
  getr regs 8 = w64 (je_out en) /\
  (forall r, In r PJP_KEPT -> getr regs r = getr (je_regs en) r) /\
  (forall a, je_sp1 en <= a < je_sp0 en -> apresent (w_H W) mem a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (je_sp1 en + 8) 24 /\
  (* the read-only view *)
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  (* the memory overlay is normal *)
  YAkMemnorm.memnorm SEGS mem.

(* pjp_inv over a world relation R: a COPY of pjp_inv's body with the journal ajournal_xR R (the segment proofs take
   pjp_inv apart, so pjp_inv stays as it is); pjp_inv_R_wle checks by reflexivity that pjp_inv is pjp_invR at wle. The
   cut C1 (before parse_value) uses pjp_inv; the cuts after parse_value's call use pjp_invR at wle' SEGS RZ_cf *)
Definition pjp_invR (R : world SEGS -> world SEGS -> Prop) (en : PjpEnt) (Sb : astate) (fy : YK11.FPState)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (k : Z) : Prop :=
  frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy /\
  ajournal_xR (SK := SK) SEGS B PST ARx R (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly S Hp W mem md k /\
  (forall a, je_sp0 en <= a < je_sp0 en + je_d en ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H (je_W en)) (je_mem en) a) /\
  spZ regs = je_sp1 en /\
  val_mem SEGS (rdW W mem) (je_sp1 en + 40) 8 (raZ (je_regs en)) /\
  val_mem SEGS (rdW W mem) (je_sp1 en + 32) 8 (s0Z (je_regs en)) /\
  getr regs 8 = w64 (je_out en) /\
  (forall r, In r PJP_KEPT -> getr regs r = getr (je_regs en) r) /\
  (forall a, je_sp1 en <= a < je_sp0 en -> apresent (w_H W) mem a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (je_sp1 en + 8) 24 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) /\
  YAkMemnorm.memnorm SEGS mem.
Lemma pjp_inv_R_wle : forall en Sb fy ly S Hp W regs mem md k,
  pjp_inv en Sb fy ly S Hp W regs mem md k = pjp_invR (@wle SEGS) en Sb fy ly S Hp W regs mem md k.
Proof. reflexivity. Qed.
(* the move across a call that hides shadow again: wle lifts to wle' SEGS RZ_cf *)
Lemma pjp_inv_lift : forall en Sb fy ly S Hp W regs mem md k,
  pjp_inv en Sb fy ly S Hp W regs mem md k ->
  pjp_invR (wle' SEGS YGcfRehidePost.RZ_cf) en Sb fy ly S Hp W regs mem md k.
Proof.
intros en Sb fy ly S Hp W regs mem md k (Z1 & Z2 & HJ & HR).
split; [exact Z1|]. split; [exact Z2|]. split; [|exact HR].
exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ (je_Hp en) _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* THE BUDGET after parse_value (the rebase's data): the base state is the entry's with its depot dp; dp's wild part
   lies inside the entry's plus a budget WS that parse_value's post bounds, wbudget CW 0 WS *)
Definition pjp_wb (CW : list (list Z)) (en : PjpEnt) (Sb : astate) : Prop :=
  exists (dp WS : list (list Z)), Sb = set_depot dp (je_S en) /\ YCbqGwild.wbudget CW 0 WS /\
    incl (wild_part (as_universe B) dp) (wild_part (as_universe B) (st_depot (je_S en)) ++ WS).

(* out's facts at a state with ledger list Lam (prhPj_slot's content at the entry; out is NOT in a harness block:
   the kit's premise keeps it apart from every block of Lam, so it lies in another live allocator block or a live fake
   frame; the kit owner ruled the real stack out): writable, 8-aligned, outside the runtime's bytes, addressable *)
Definition pjp_out_ok (en : PjpEnt) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world SEGS)
  (mem : word -> option byte) : Prop :=
  let out := je_out en in
  4096 <= out /\ out < YM05.alloc_ceiling /\
  ((exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + cf_head, m - cf_head) Lam /\ b <= out /\ out + 56 <= b + m) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      frame_addr ly cid pos <= out /\ out + 56 <= frame_addr ly cid pos + fs_frame_bytes cid)) /\
  (forall a k, In (a, k) Lam -> out + 56 <= a \/ a + k <= out) /\
  pj_rwR SEGS (rdW W mem) out /\ amem_range out 56 /\
  (forall a, out <= a < out + 56 -> ~ aowned B ly S a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF out 56 /\ shadow_hull_vis (aview SEGS (w_H W) mem) out 56.

(* the text's facts at a state with ledger list Lam: its bytes, at home *)
Definition pjp_text_ok (en : PjpEnt) (ly : alayout) (S : astate) (Hp : list Z) (Lam : list (Z * Z))
  (W : world SEGS) (mem : word -> option byte) : Prop :=
  src_rd (PA := PA) W mem (je_t0 en) (je_tl en) /\
  prhReader_home (PA := PA) B ly S Hp Lam (je_t0 en) (je_len en).

(* the cursor struct pj_in at sp1 + 8 (p, end, depth 0) *)
Definition pjp_cursor (en : PjpEnt) (W : world SEGS) (mem : word -> option byte) (p : Z) : Prop :=
  pj_in_okR SEGS (rdW W mem) (je_sp1 en + 8) (je_t0 en) (je_len en) p 0 (je_tl en).

(* ---- the cuts ---- *)

(* C1, at the `jal parse_value`: entry float state, entry allocator state, memory after the memset *)
Definition pjp_C1 (CW : list (list Z)) (en : PjpEnt) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (k : Z) : Prop :=
  pjp_inv en (je_S en) fx (je_ly en) (je_S en) (je_Hp en) (je_W en) regs mem md k /\
  (* pj_parse's never-written slot at sp1 still holds the entry word, whose parse_string free trace is in CW
     (prh_cw_pj's second arm), for parse_value's prh_cw_entry *)
  (forall r, In r (prh_free_sites F_parse_string) ->
     forall w0, rdword (aview SEGS (w_H (je_W en)) mem) (je_sp1 en) = Some w0 ->
       In (prh_trace (pc_free_ra0 (as_code B)) r [w0]) CW) /\
  getr regs 10 = w64 (je_sp1 en + 8) /\ getr regs 11 = w64 (je_out en) /\
  pjp_cursor en (je_W en) mem (je_t0 en) /\
  pj_zeroR SEGS (rdW (je_W en) mem) (je_out en) /\
  pjp_out_ok en (je_ly en) (je_S en) (je_Lam en) (je_W en) mem /\
  pjp_text_ok en (je_ly en) (je_S en) (je_Hp en) (je_Lam en) (je_W en) mem /\
  prh_ledger (PA := PA) B (je_ly en) (je_S en) (je_Hp en) (je_W en) mem (je_Lam en)
    (je_peak en) (je_cnt en) (je_fail en) (je_ran en) (je_most en) (je_own en).

(* parse_value's outcome as the later cuts carry it (the batch kit: rd_ledger_move at g_most over the grant-all trace) *)
Definition pjp_pv_out (en : PjpEnt) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (ok : list bool) (res : option (PjTree.jv * list Z)) (tr : list PjGrammar.ev)
  (D : list (Z * Z)) (Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z) : Prop :=
  (exists okr, PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en) ok = (res, tr, okr)) /\
  prh_ledger (PA := PA) B ly S Hp W mem Lam' peak' cnt' fail' ran' (je_most en) (je_own en) /\
  rd_ledger_move (je_Lam en) (je_peak en) (je_cnt en) (je_fail en) (je_ran en) (je_most en) ok
    (prhPv_gtrace 0 (je_tl en)) tr D Lam' peak' cnt' fail' ran' /\
  rd_blocks_move B (je_ly en) (je_S en) ly S D tr (je_tl en) 0.

(* THE TREE'S FREE ORDER at a cut's memory (parse_value's post conjunct, the batch kit): at every depth bound n' >= n, pj_free's
   order list F of out's tree carries the model's pj_frees of the text IN ORDER (prhPv_frees 0 tl ok IS pj_frees ok tl
   by unfolding) *)
Definition pjp_ftie (en : PjpEnt) (W : world SEGS) (mem : word -> option byte) (Lam' D : list (Z * Z))
  (ok : list bool) (n : nat) : Prop :=
  cf_head = PresetReqAt.HEAD -> forall n', (n <= n')%nat ->
  exists F, pj_foR SEGS (rdW W mem) (prh_lin Lam') n' (je_out en) D F /\
    map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok (je_tl en).

(* C2ok, after parse_value returned 0 (Some (t, r)), before the skip_ws setup; the journal at wle' (parse_value may
   hide shadow again), parse_value's hull use from the entry state, its injected-reading outcome *)
Definition pjp_C2ok (en : PjpEnt) (Sb : astate) (fy : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjp_invR (wle' SEGS YGcfRehidePost.RZ_cf) en Sb fy ly S Hp W regs mem md k /\ room_live_cf S /\
  PresetHullBudget.hull_used (je_S en) S (PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en))) /\
  exists ok t r tr D Lam' peak' cnt' fail' ran',
  pjp_pv_out en ly S Hp W mem ok (Some (t, r)) tr D Lam' peak' cnt' fail' ran' /\ pjp_pos_pv en S tr /\
  pjp_outc en S (Some (t, r)) tr ran' /\
  pjp_cursor en W mem (je_t0 en + je_len en - Z.of_nat (length r)) /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam') (je_out en) t D /\
  pj_ncapR SEGS (rdW W mem) (je_out en) t /\
  pjp_out_ok en ly S Lam' W mem /\
  pjp_text_ok en ly S Hp Lam' W mem /\
  pjp_ftie en W mem Lam' D ok (PjTree.depth t) /\
  pjp_inj en ok tr.

(* C2ref, before `mv a0, s0; jal pj_free`: the parse refused (parse_value returned -1, or junk after the value); what
   was built has pj_free's order list F at depth DOC_D, and F carries the model's pj_frees of the text in order; the
   journal at wle', parse_value's hull use and its injected-reading outcome as at C2ok *)
Definition pjp_C2ref (en : PjpEnt) (Sb : astate) (fy : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjp_invR (wle' SEGS YGcfRehidePost.RZ_cf) en Sb fy ly S Hp W regs mem md k /\ room_live_cf S /\
  PresetHullBudget.hull_used (je_S en) S (PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en))) /\
  exists ok res tr D F Lam' peak' cnt' fail' ran',
  pjp_pv_out en ly S Hp W mem ok res tr D Lam' peak' cnt' fail' ran' /\ pjp_pos_pv en S tr /\
  pjp_outc en S res tr ran' /\
  PjGrammar.post res = None /\
  pj_foR SEGS (rdW W mem) (prh_lin Lam') DOC_D (je_out en) D F /\
  map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod ok (je_tl en) /\
  pjp_out_ok en ly S Lam' W mem /\
  pjp_inj en ok tr.

(* C3, at the epilogue: the text's post holds at this state, a0 included; the journal at wle' *)
Definition pjp_C3 (en : PjpEnt) (Sb : astate) (fy : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pjp_invR (wle' SEGS YGcfRehidePost.RZ_cf) en Sb fy ly S Hp W regs mem md k /\ pjp_Q en ly S Hp W regs mem md.

(* ---- the segment statements (one file each), at one driver context list CTX0 and cursor set CW; the cuts after
   the parse_value call are at a rebased journal (pjp_wb). Each concludes SRr' SEGS RZ_cf: its run reaches
   parse_value or pj_free, or continues from a journal at wle' ---- *)
Definition pjp_seg_C3 (CTX0 CW : list (list Z)) : Prop :=
  forall en Sb fy ly S Hp W regs mem md k, pjp_pre CTX0 CW en -> pjp_wb CW en Sb ->
  pjp_C3 en Sb fy ly S Hp W regs mem md k ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (pjp_cfg fy PJP_C3 regs mem md) (pjp_FIN CW en).
Definition pjp_seg_C2ref (CTX0 CW : list (list Z)) : Prop :=
  forall en Sb fy ly S Hp W regs mem md k, pjp_pre CTX0 CW en -> pjp_wb CW en Sb ->
  pjp_C2ref en Sb fy ly S Hp W regs mem md k ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (pjp_cfg fy PJP_C2REF regs mem md) (pjp_FIN CW en).
Definition pjp_seg_C2ok (CTX0 CW : list (list Z)) : Prop :=
  forall en Sb fy ly S Hp W regs mem md k, pjp_pre CTX0 CW en -> pjp_wb CW en Sb ->
  pjp_C2ok en Sb fy ly S Hp W regs mem md k ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (pjp_cfg fy PJP_C2OK regs mem md) (pjp_FIN CW en).
Definition pjp_seg_C1 (CTX0 CW : list (list Z)) : Prop :=
  forall en regs mem md k, pjp_pre CTX0 CW en -> pjp_C1 CW en regs mem md k ->
  SRr' SEGS YGcfRehidePost.RZ_cf (je_W en) (pjp_cfg fx PJP_C1 regs mem md) (pjp_FIN CW en).
Definition pjp_seg_entry (CTX0 CW : list (list Z)) : Prop :=
  forall en, pjp_pre CTX0 CW en ->
  SRr' SEGS YGcfRehidePost.RZ_cf (je_W en) (cfg_at SEGS (pa_sigma AS_pj_parse) (je_regs en) (je_mem en) (je_md en))
    (pjp_FIN CW en).

(* ---- shared keep statement (proved in lib/B/Prog/pj_parse_seg_ep.v): what a callee's own journal at its widened
   window (STK1 + e1) (sp1 + e1), e1 <= 32, keeps of pj_parse's state: the caller's window, the saved ra / s0 at
   sp1 + 40 / sp1 + 32 (above every callee window: the cursor ends at sp1 + 32), the frame's presence, the cursor's
   shadow and the read-only view. FP1 is the callee's footprint (rd_fp q v, [(q, q + 8)] or pj_free's); it holds no
   byte of [sp1 + 32, sp0 + d). The base state Sb of pj_parse's own journal is any; the callee's journal is at any
   budget WS1 (parse_value's is budgeted; AJ is the budget []). Both journals at wle' (the callee is a call after
   parse_value, or hides shadow again itself) ---- *)
Definition pjp_frame_kept_stmt : Prop :=
  forall en Sb fy ly S Hp W regs mem md k STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 WS1,
  pjp_invR (wle' SEGS YGcfRehidePost.RZ_cf) en Sb fy ly S Hp W regs mem md k ->
  ajournal_xwR (SK := SK) SEGS B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK1 + e1) (je_sp1 en + e1) FP1 ly S Hp W
    mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  0 <= STK1 -> 0 <= e1 <= 32 ->
  0 <= je_d en -> ~ YI16.sink_open_fp FP1 ->
  (forall a, inFP FP1 a -> ~ (je_sp1 en + 32 <= a < je_sp0 en + je_d en)) ->
  (forall a, je_sp0 en <= a < je_sp0 en + je_d en ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (je_W en)) (je_mem en) a) /\
  val_mem SEGS (rdW W2 mem2) (je_sp1 en + 40) 8 (raZ (je_regs en)) /\
  val_mem SEGS (rdW W2 mem2) (je_sp1 en + 32) 8 (s0Z (je_regs en)) /\
  (forall a, je_sp1 en <= a < je_sp0 en -> apresent (w_H W2) mem2 a) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (je_sp1 en + 8) 24 /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).

(* the allocator-trace premises the parse_value call needs (rd_pre: prh_malloc_univ and the realloc pair, the FIXED
   part), from pj_parse's closure (the kit's prh_univ_closure_malloc / prh_univ_closure_realloc) *)
Definition pjp_g_univ : Prop :=
  forall CTX0, prh_univ_closure B CTX0 ->
  prh_malloc_univ B /\ In [cf_pc_realloc_ra0] (u_fix (as_universe B)) /\
  In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)).

(* the shadow visibility the cuts after a call need, which no journal clause keeps (shadow bytes of blocks, globals and
   frames lie below alloc_ceiling and are not block / image / frame bytes): image facts, discharged at the instance
   (lib/B/Prog/pj_parse_inst.v, ARx := ARcf /\ xs_placed_cf, B := YD2l.TfibB) *)
Definition pjp_g_vis : Prop :=
  ARx_frame_hull_vis SEGS B ARx /\
  (forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0) /\
  (forall ly S Hp W mem md a, ARx ly S Hp W mem md -> @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA ->
     aview SEGS (w_H W) mem (shadow_addr a) <> None).
End d.

(* ---- the pure facts (lib/B/Prog/pj_parse_glue.v proves each) ---- *)
Definition pjp_g_fd_mono : Prop :=
  forall (segs : list Segment) m lblk n n' p D, (n <= n')%nat -> pj_fdR segs m lblk n p D -> pj_fdR segs m lblk n' p D.
Definition pjp_g_node_fd : Prop :=
  forall (segs : list Segment) m lblk t p D n,
  pj_nodeR segs m lblk p t D -> (PjTree.depth t <= n)%nat -> pj_fdR segs m lblk n p D.
Definition pjp_g_depth : Prop :=
  forall tl ok t r tr okr, PjGrammar.jr_value ReaderRes.jr_strtod 0 tl ok = (Some (t, r), tr, okr) ->
  (PjTree.depth t <= PjGrammar.MAXD)%nat.
Definition pjp_g_run : Prop :=
  forall tl ok res tr okr, PjGrammar.jr_value ReaderRes.jr_strtod 0 tl ok = (res, tr, okr) ->
  PjGrammar.jr_run ReaderRes.jr_strtod tl ok = (PjGrammar.post res, tr).
Definition pjp_g_fail_in : Prop :=
  forall tl ok res tr okr cnt fail ns most ran ran', PjGrammar.jr_value ReaderRes.jr_strtod 0 tl ok = (res, tr, okr) ->
  prh_oks ok cnt fail (PjGrammar.calls tr) ns most ran ran' ->
  cnt <= fail < cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) -> PjGrammar.post res = None.
Definition pjp_g_norefuse : Prop :=
  forall tl ok res tr okr cnt fail, PjGrammar.jr_value ReaderRes.jr_strtod 0 tl ok = (res, tr, okr) ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod tl) <= fail) ->
  prh_granted ok cnt fail (PjGrammar.calls tr) ->
  PjGrammar.post res = PjGrammar.json_read ReaderRes.jr_strtod tl /\
  PjGrammar.calls tr = PjGrammar.ncalls ReaderRes.jr_strtod tl.
Definition pjp_g_calls : Prop :=
  forall tl ok res tr okr, PjGrammar.jr_value ReaderRes.jr_strtod 0 tl ok = (res, tr, okr) ->
  (PjGrammar.calls tr <= 2 * length tl + 2)%nat.
Definition pjp_g_fail_after : Prop :=
  forall cnt fail k f', fail_afterR cnt fail k f' <-> ReaderRes.fail_after cnt fail k f'.
(* the unread rest after an accepted value, as the cursor sees it *)
Definition pjp_g_rest : Prop :=
  forall tl ok t r tr okr (t0 : Z), PjGrammar.jr_value ReaderRes.jr_strtod 0 tl ok = (Some (t, r), tr, okr) ->
  (length r <= length tl)%nat /\
  rest_atR tl t0 (t0 + Z.of_nat (length tl) - Z.of_nat (length r)) = r.
(* the two block-list spellings of a harness block list agree *)
Definition pjp_g_ab_hbl {cp : CfParams} : Prop := forall D, prhReader_ab D = prhPj_hbl D.
Definition pjp_glue {cp : CfParams} : Prop :=
  pjp_g_fd_mono /\ pjp_g_node_fd /\ pjp_g_depth /\ pjp_g_run /\ pjp_g_fail_in /\ pjp_g_norefuse /\
  pjp_g_calls /\ pjp_g_fail_after /\ pjp_g_rest /\ pjp_g_ab_hbl.
