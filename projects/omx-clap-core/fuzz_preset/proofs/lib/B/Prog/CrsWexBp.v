(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 755 of its 825 lines of code are new or changed and 444 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrsKitBp.v; 14 of its 45 lines of code are new or changed and 794 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrsFree0Bp.v; 67 of its 102 lines of code are new or changed and 10 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): ONE SHARED INTERIM PREMISE of the walk of
   check_reject_clean_starved, the kit's pj_write text at crcs's four pj_write calls, with the call's exact position
   advance in the kit's terms. Requires the kit lib/B/Prog/CrsKitBp.v only.
   DONOR (rule 24, reuse): the A' interim lib/A/Prog/CrsWexAp.v blob 0ee29d46ef9f (a working branch
   3adfdcc651aa, kit v4: the `cnt < 2 ^ 62` premise included), restated at the B' instance. The statement is
   image-free except for the instance: same shape, same premise order and spelling, with the kit's `_B` names.
   rule 24: proves no function (kind: one interim premise of the crcs walk; reuse search: `proof-index check_reject_clean_starved
   0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that
   search origin/ossv/recipes had no lib/A or lib/B, its released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released
   asan Proof.v existed for check_reject_clean_starved). This file proves nothing: it STATES.
   INPUTS.
   - Pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
     unstripped twin ELF sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175.
   - Listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (listings v3); image
     record lib/B/PRH_ImgB.v blob 3216eca68342.
    - The callee and caller texts (by path on this branch):
     tpj_write_specX in lib/A/PRH_FnWriter.v blob 2b497bc72172, the ledger prh_ledger .. ran most own of
     lib/A/PRH_Base.v blob fdb45545469b, tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v blob 9ecd8eb167c6.
   WHY AN INTERIM. f97c's tpj_write_specX is in the event form (entry premise prh_run_at .. (prhWriter_pjw_evs [] ..),
   exact advance under prh_granted), but it is not yet a delivered text of record for these calls: its callee
   write_value posts fpostWFm, whose defect is still open. Until the kit owner delivers pj_write, each of the four calls is
   stated here AS tpj_write_specX at that call: the text's premises, in its order and spelling, at the call's own
   arguments, and the text's post with ONE conjunct added - under ran' = 0 the post's state is at the entry position
   plus the length of the call's kit event list (crs_ev_w_B / crs_ev_ws_B; with cf_head = PresetReqAt.HEAD it follows
   from the text's own advance by PRH_Supply.v, which is lib/B/Prog/CrsBridgeBp.v crs_wexact_of_text_B). As weak as
   the four calls allow:
   - the model run, the tree and its blocks are C's (cb_rp_sm .. cb_rp_H0, cb_doc, cb_t, cb_D); the entry position is
     the EXACT one of the call's boundary (cb_rp_i C + length evs0, evs0 the kit's prefix at that call);
   - the ledger's last two arguments are the kit's (cb_most C, the own cell 0: crs_core_B's LEDGER .. (cb_most C) 0);
   - pretty is the call's (1, 0); g_fail_at is the call's (cnt + ck_pick tb (wcalls t p) after the injected
     fuzz_alloc_fail, SIZE_MAX for a whole write); nothing was refused at entry (ran = 0), and cnt < 2 ^ 62 (kit v4:
     without it the added conjunct is false of the text - at cnt = 2 ^ 64 - 2 a whole write's second allocation is
     the chosen failure, prh_granted holds and ran' = 0, but the call made fewer events than crs_ev_w_B; every call
     site has it from its boundary's crs_core_B);
   - the depth bound is the walk's (DOC_D, the kit's STK_pj_write DOC_D);
   - the text's local abbreviation rdW W mem is written out (mrestrict (w_H W) mem).
   THE FOUR CALLS, at the B' addresses of the kit's cut (CrsKitBp.v's table; A' in brackets, the body is the same
   four calls - this is not a B' difference):
     W1 B' 0x822e0 (+512) [A' 0x82348]  pj_write (doc, 1), whole:    entry crs_evs_at_W1_B C, advance crs_ev_w_B C true
     X2 B' 0x82398 (+696) [A' 0x823e8]  pj_write (doc, 1), injected: entry crs_evs_at_X2_B C, advance crs_ev_ws_B C true
     Z  B' 0x824dc (+1020) [A' 0x8252c] pj_write (doc, 0), whole:    entry crs_evs_at_Z_B C,  advance crs_ev_w_B C false
     X3 B' 0x8251c (+1084) [A' 0x825c4] pj_write (doc, 0), injected: entry crs_evs_at_X3_B C, advance crs_ev_ws_B C false
   (their return sites 0x822e4 / 0x8239c / 0x824e0 / 0x82520 are pi_call_rets prh_img_B .. F_pj_write.)
   A walk takes it as ONE premise `HW_exact : forall fx', crs_wexact_B (fx := fx') .. CTX0 C`, quantified over the
   float state as the callee texts are.
   Numerals: 1 / 0 are pretty (the C int the callers pass); 2 ^ 31 is the text's bound on pretty (WORD); 2 ^ 62 is the
   kit's count bound (DERIVED: crs_core_B's cnt3 < 2 ^ 62). The four addresses above are the kit's, written only in
   this comment. No ADDRESS in a statement. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ONE pj_write call of crcs: tpj_write_specX (PRH_FnWriter.v on the kit's cut 7cdbb61b5fa0, :773-850) at the call's
   arguments - the model run C's (the strtod model keyed: ReaderRes.jr_strtod), the entry position cb_rp_i C + length
   evs0, most := cb_most C, own := 0, v := cb_doc C, t := cb_t C, D := cb_D C, pretty, g_fail_at by inj, ran = 0,
   n := DOC_D - with the text's post (DEAD-PJWRITE's prh_granted included) and the exact advance by evs under
   ran' = 0 *)
Definition crs_wcall_B (CTX0 : list (list Z)) (C : crsC_B) (pretty : Z) (inj : bool)
  (evs0 evs : list PresetReqAt.hev) : Prop :=
  forall (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran,
  fail = (if inj then cnt + ck_pick (cb_tb C) (PjWriteHyp.wcalls (cb_t C) (negb (pretty =? 0))) else SIZE_MAXZ) ->
  ran = 0 -> cnt < 2 ^ 62 ->
  fpre B ARx (STK_pj_write DOC_D) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  room_live_cf S ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length evs0)%nat (cb_rp_H0 C)
    rp_hist S ->
  (length (cb_rp_os C) <= 4)%nat ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length evs0)%nat
    (length (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces (cb_t C) (negb (pretty =? 0))))) ->
  getr regs 10 = w64 (cb_doc C) -> getr regs 11 = w64 pretty -> 0 <= pretty < 2 ^ 31 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran (cb_most C) 0 ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length evs0)%nat
    (prhWriter_pjw_evs [] cnt fail (WriterValue.wdpieces (cb_t C) (negb (pretty =? 0)))) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) (cb_doc C) (cb_t C) (cb_D C) ->
  ((spZ regs <= cb_doc C /\ cb_doc C + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <= cb_doc C /\ cb_doc C + 56 <= x + y) \/
   prhWriter_in_frame ly S (cb_doc C)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (cb_doc C) 56 ->
  prhWriter_tree_vis W mem (cb_D C) ->
  (forall a k, In (a, k) (cb_D C) -> In (a, k) Lam) ->
  (PjTree.depth (cb_t C) <= DOC_D)%nat -> Z.of_nat (PjTree.depth (cb_t C)) <= 2 ^ 31 - 1 ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterValue.wdoc (cb_t C) (negb (pretty =? 0)))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  blocks_bytes S + LIVE_pj_write (cb_t C) (negb (pretty =? 0)) <= LIVE_MAX ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (pa_sigma AS_pj_write) regs mem md)
    (fpostFm B ARx SK (STK_pj_write DOC_D) [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       exists ok ran' q Lam' peak',
       let P := WriterValue.wdpieces (cb_t C) (negb (pretty =? 0)) in
       let st' := prhWriter_putN ok (WriterApp.w0 cnt fail) P in
       prh_oks ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) (prhWriter_reqs ok (WriterApp.w0 cnt fail) P)
         (cb_most C) ran ran' /\
       getr regs' 10 = w64 q /\
       room_live_cf S' /\
       prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) /\
       (prh_granted ok cnt fail (prhWriter_k ok (WriterApp.w0 cnt fail) P) ->
          exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C)
            (cb_rp_i C + length evs0 + length (prhWriter_pjw_evs ok cnt fail P))%nat (cb_rp_H0 C) hist' S') /\
       pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) (cb_doc C) (cb_t C) (cb_D C) /\
       prhWriter_tree_vis W' mem' (cb_D C) /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak' (WriterApp.w_cnt st') (WriterApp.w_fail st') ran' (cb_most C) 0 /\
       ((WriterApp.w_failed st' = 0 /\ q <> 0 /\ ~ In (q - cf_head, WriterApp.w_cap st' + cf_head) (ablocks B ly S) /\
         Lam' = (q, WriterApp.w_cap st') :: Lam /\ peak' = Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st') /\
         Permutation (ablocks B ly' S') ((q - cf_head, WriterApp.w_cap st' + cf_head) :: ablocks B ly S) /\
         Z.of_nat (length (WriterValue.wdoc (cb_t C) (negb (pretty =? 0)))) < WriterApp.w_cap st' /\
         bytes_at W' mem' q (WriterValue.wdoc (cb_t C) (negb (pretty =? 0)) ++ [0]))
        \/
        (WriterApp.w_failed st' <> 0 /\ q = 0 /\ Lam' = Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
        ((WriterApp.w_cap st' = 0 /\ peak' = Z.max peak (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P)) \/
         (WriterApp.w_cap st' <> 0 /\
          peak' = Z.max (Z.max peak (Ledger.lsum Lam + WriterApp.w_cap st'))
            (prhWriter_rpeak ok Lam (WriterApp.w0 cnt fail) P))))) /\
       (* THE ONE ADDED CONJUNCT: the exact advance by the call's own kit events *)
       (ran' = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C)
          (cb_rp_i C + length evs0 + length evs)%nat (cb_rp_H0 C) hist' S'))).

(* the four calls *)
Definition crs_wexact_B (CTX0 : list (list Z)) (C : crsC_B) : Prop :=
  crs_wcall_B CTX0 C 1 false (crs_evs_at_W1_B C) (crs_ev_w_B C true) /\
  crs_wcall_B CTX0 C 1 true (crs_evs_at_X2_B C) (crs_ev_ws_B C true) /\
  crs_wcall_B CTX0 C 0 false (crs_evs_at_Z_B C) (crs_ev_w_B C false) /\
  crs_wcall_B CTX0 C 0 true (crs_evs_at_X3_B C) (crs_ev_ws_B C false).

End f.
End d.
