(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 671 of its 740 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsKitAp.v; 15 of its 55 lines of code are new or changed and 700 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsBoundAp.v, with its module paths and module names changed; 64 of its 98 lines of code are new or changed and 21 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): ONE SHARED INTERIM PREMISE of the walk of check_reject_clean_starved, the
   pj_write text at crcs's four pj_write calls, with the call's exact position advance in the kit's terms. Requires
   the frozen kit lib/A/Prog/CrsKitAp.v (cold/h-w6u-rep-crsa2-v3 df14c8cd3eb9) only.
   rule 24: proves function check_reject_clean_starved (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that
   lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its
   released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). Written new. This file proves nothing: it STATES.
   INPUTS.
   - Pin A' asan sha256 1be0f53d96cb9d6c (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/A/Listing_prog.v blob 7ed1529926bd + lib/A/PAImg_prog.v blob 505a51ff7d08 (listings v3).
   - K0 texts (K0's #102 kit tip of record cold/h-hpreset-7-walkkit-next decff67d721f, by path on kit v3):
     tpj_write_specX in lib/A/PRH_FnWriter.v blob 2b497bc72172 (:654-703), the ledger prh_ledger .. ran most own of
     lib/A/PRH_Base.v blob 3004a98fe2d9, tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v blob 4cb899514e6c.
   WHY AN INTERIM. decff's tpj_write_specX is in the event form (entry premise prh_run_at .. (prhWriter_pjw_evs [] ..),
   exact advance under prh_granted), but it is not yet a delivered text of record for these calls: its callee
   write_value posts fpostWFm, whose defect is still open in decff. Until a Theorem Labs lane delivers pj_write (then this is a
   citation of tpj_write_specX plus PRH_Supply's prhWriter_pjw_evs_granted / _w_evs / _w_starved), each of the four
   calls is stated here AS tpj_write_specX at that call: the text's premises, in its order and spelling, at the
   call's own arguments, and the text's post with ONE conjunct added - under ran' = 0 the post's state is at the entry
   position plus the length of the call's kit event list (crs_ev_w / crs_ev_ws; with cf_head = PresetReqAt.HEAD it
   follows from the text's own advance by PRH_Supply.v). As weak as the four calls allow:
   - the model run, the tree and its blocks are C's (c_rp_sm .. c_rp_H0, c_doc, c_t, c_D); the entry position is the
     EXACT one of the call's boundary (c_rp_i C + length evs0, evs0 the kit's prefix at that call);
   - the ledger's last two arguments are the kit's (c_most C, the own cell 0: crs_core's LEDGER .. (c_most C) 0);
   - pretty is the call's (1, 0); g_fail_at is the call's (cnt + ck_pick tb (wcalls t p) after the injected
     fuzz_alloc_fail, SIZE_MAX for a whole write); nothing was refused at entry (ran = 0);
   - the depth bound is the walk's (DOC_D, the kit's STK_pj_write DOC_D);
   - the text's local abbreviation rdW W mem is written out (mrestrict (w_H W) mem).
   The four calls (the internal file SEGMENT-PLAN-Aprime.md; kit prefixes crs_evs_at_<SEG>, event lists crs_ev_w / crs_ev_ws):
     W1 (A' 0x82348) pj_write (doc, 1), whole:    entry crs_evs_at_W1 C, advance crs_ev_w C true
     X2 (A' 0x823e8) pj_write (doc, 1), injected: entry crs_evs_at_X2 C, advance crs_ev_ws C true
     Z  (A' 0x8252c) pj_write (doc, 0), whole:    entry crs_evs_at_Z C,  advance crs_ev_w C false
     X3 (A' 0x825c4) pj_write (doc, 0), injected: entry crs_evs_at_X3 C, advance crs_ev_ws C false
   A walk takes it as ONE premise `HW_exact : forall fx', crs_wexact (fx := fx') .. CTX0 C`, quantified over the
   float state as the callee texts are.
   Numerals: 1 / 0 are pretty (the C int the callers pass); 2 ^ 31 is the text's bound on pretty (WORD); 2 ^ 62 is the
   kit's count bound (DERIVED: crs_core's cnt3 < 2 ^ 62). No ADDRESS.
   KIT v4: ONE premise ADDED to crs_wcall, `cnt < 2 ^ 62`, right after
   `ran = 0`. Without it the added conjunct is false of the text: for a whole write (g_fail_at = SIZE_MAX) at
   cnt = 2 ^ 64 - 2 the second allocation is the chosen failure, prh_granted holds and ran' = 0, but the call made
   fewer events than crs_ev_w. Every call site has it from its boundary's crs_core (the count is not moved between
   the boundary and the call). With it the whole of crs_wexact follows from tpj_write_specX
   (lib/A/Prog/CrsBridgeAp.v crs_wexact_of_text). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import CrsKitAp.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ONE pj_write call of crcs: tpj_write_specX (lib/A/PRH_FnWriter.v:1142-1223) at the call's
   arguments - the model run C's (strtod keyed: ReaderRes.jr_strtod), the entry position c_rp_i C + length evs0,
   most := c_most C, own := 0, v := c_doc C, t := c_t C, D := c_D C, pretty, g_fail_at by inj, ran = 0,
   n := DOC_D - with the text's post and the exact advance by evs under ran' = 0. The text has, in its order:
   the consumer window prh_cons_from (:1165-1166), prh_oks over the run's requests prhWriter_reqs and the ledger's most
   (:1189-1190), prh_granted (DEAD-PJWRITE, :1198), and the refusal peak prhWriter_rpeak, failed arm (:1220-1223) *)
Definition crs_wcall (CTX0 : list (list Z)) (C : crsC) (pretty : Z) (inj : bool)
  (evs0 evs : list PresetReqAt.hev) : Prop :=
  forall (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran,
  fail = (if inj then cnt + ck_pick (c_tb C) (PjWriteHyp.wcalls (c_t C) (negb (pretty =? 0))) else SIZE_MAXZ) ->
  ran = 0 -> cnt < 2 ^ 62 ->
  fpre B ARx (STK_pj_write DOC_D) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  room_live_cf S ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C + length evs0)%nat (c_rp_H0 C) rp_hist S ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C + length evs0)%nat
    (length (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces (c_t C) (negb (pretty =? 0))))) ->
  getr regs 10 = w64 (c_doc C) -> getr regs 11 = w64 pretty -> 0 <= pretty < 2 ^ 31 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran (c_most C) 0 ->
  prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C + length evs0)%nat
    (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces (c_t C) (negb (pretty =? 0)))) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) (c_doc C) (c_t C) (c_D C) ->
  ((spZ regs <= c_doc C /\ c_doc C + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <= c_doc C /\ c_doc C + 56 <= x + y) \/
   prhWriter_in_frame ly S (c_doc C)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (c_doc C) 56 ->
  prhWriter_tree_vis W mem (c_D C) ->
  (forall a k, In (a, k) (c_D C) -> In (a, k) Lam) ->
  (PjTree.depth (c_t C) <= DOC_D)%nat -> Z.of_nat (PjTree.depth (c_t C)) <= 2 ^ 31 - 1 ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterValue.wdoc (c_t C) (negb (pretty =? 0)))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  blocks_bytes S + LIVE_pj_write (c_t C) (negb (pretty =? 0)) <= LIVE_MAX ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (pa_sigma AS_pj_write) regs mem md)
    (fpostFm B ARx SK (STK_pj_write DOC_D) [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       exists ok ran' q Lam' peak',
       let P := WriterValue.wdpieces (c_t C) (negb (pretty =? 0)) in
       let st' := prhWriter_putN ok (WriterApp.w0 cnt fail) P in
       prh_oks ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) (prhWriter_reqs ok (WriterApp.w0 cnt fail) P)
         (c_most C) ran ran' /\
       getr regs' 10 = w64 q /\
       room_live_cf S' /\
       prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) /\
       (prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) ->
          exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
            (c_rp_i C + length evs0 + length (prhWriter_pjw_evs ok cnt fail P))%nat (c_rp_H0 C) hist' S') /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) (c_doc C) (c_t C) (c_D C) /\
       prhWriter_tree_vis W' mem' (c_D C) /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' (c_most C) 0 /\
       ((WriterApp.w_failed st' = 0 /\ q <> 0 /\ ~ In (q - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B ly S) /\
         Lam' = (q, WriterApp.w_cap st') :: Lam /\ peak' = Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st') /\
         Permutation (ablocks B ly' S') ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ablocks B ly S) /\
         Z.of_nat (length (WriterValue.wdoc (c_t C) (negb (pretty =? 0)))) < WriterApp.w_cap st' /\
         bytes_at W' mem' q (WriterValue.wdoc (c_t C) (negb (pretty =? 0)) ++ [0]))
        \/
        (WriterApp.w_failed st' <> 0 /\ q = 0 /\ Lam' = Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
         ((WriterApp.w_cap st' = 0 /\ peak' = Z.max peak (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P)) \/
          (WriterApp.w_cap st' <> 0 /\
           peak' = Z.max (Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st'))
             (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P))))) /\
       (* THE ONE ADDED CONJUNCT: the exact advance by the call's own kit events *)
       (ran' = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
          (c_rp_i C + length evs0 + length evs)%nat (c_rp_H0 C) hist' S'))).

(* the four calls *)
Definition crs_wexact (CTX0 : list (list Z)) (C : crsC) : Prop :=
  crs_wcall CTX0 C 1 false (crs_evs_at_W1 C) (crs_ev_w C true) /\
  crs_wcall CTX0 C 1 true (crs_evs_at_X2 C) (crs_ev_ws C true) /\
  crs_wcall CTX0 C 0 false (crs_evs_at_Z C) (crs_ev_w C false) /\
  crs_wcall CTX0 C 0 true (crs_evs_at_X3 C) (crs_ev_ws C false).

End f.
End d.
