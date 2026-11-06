(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Open_sh.v, with its module paths and module names changed; 1178 of its 1215 lines of code are new or changed and 43 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (ASan build): SEGMENT WA2 (lane CawA102R,
   a Theorem Labs lane, INT102-READY on the kit's cut 7cdbb61b5fa0, prover CawA102R.KWA2; first proved by CawA102.CawA102WA2 at
   a0785435cdc, then by CawA102R.CawRWA2 on the caw_pst base, by CawA102R.CawDWA2 on the decff base e7a40f4137aa and
   by CawA102R.CawGWA2 on the f97c base a5641d45bc36).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   WHAT IT PROVES: caw_wa2_holds : caw_seg_WA2R (fx := fx) B SK CTX0 P (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
   (Caw102A_Base.v; the refused arm frees the scratch under the re-hide, so past the free the run is at wle'), for an
   abstract memory invariant P with srr_inv_laws / srr_inv_call / srr_inv_mn: from the cut CAW_PC_X (+68) to
   CAW_PC_R (+128, caw_k_RR) or CAW_PC_OOM (+252, caw_k_OOMR). THE CODE (the A' twin's disassembly
   in the internal file check_as_written.A_new.s of the
   plan-cno-caw, DERIVED offsets from the entry):
     +68  snez a1, s0; addi a1, a1, -1; and a1, a1, s1 (v = rc == 0 ? doc : 0); sd a0, 32(sp) (the scratch, struct +24);
          sd zero, 40(sp) (differs, struct +32); addi a0, sp, 8 (q = sp0 - 72); +92 jal ex_value
     +96  beqz a0 -> +128 (read: caw_k_RR)
     +100 ld a0, 32(sp); +104 jal __wrap_free (the scratch); +108 j +248; +248 li s2, -1; +252 (caw_k_OOMR, want = -1)
   BASE OF RECORD (as at the batch-prep base, lib/A/Prog/Caw102A_Base.v
   (Caw102A_Kit.v 3d241a90402d unchanged)), on the kit's cut
   (lib/A/PRH_FnCheck.v c40cf3fdcd2a, tcheck_as_written_specX :832-902; PRH_Base.v; PRH_FnEx.v, tex_value_specX: f97c's
   text plus hull_used S S' [] in its post, PRH_FnEx.v:335, read as HHU; the P'' engine set as the base carries it).
   WHAT CHANGED AT THIS BASE, AND WHY (the batch text, then the re-hide move and the hull budget; (1) names every statement change):
   (1) THE RUN-WORD LIST DW IS GONE (the text's binder and prh_univ_closure's argument, PRH_Base.v :1225): the
   Section variable DW is removed, every base name drops its DW argument (`caw_pre (fx := fx) B CTX0 D`,
   `caw_carry (fx := fx) B SK CTX0 D`, `caw_k_RR (fx := fx) B SK CTX0 P RW Q D`, ...), and the free's fixed trace cites
   `prh_univ_closure_lit B CTX0 F_check_as_written RT_free` (PRH_Base.v :1255, no DW). The statements of
   wa2_rod, wa2_scr_not_hp, wa2_src_rd_J, wa2_tree_J and wa2_foot lose DW only; caw_wa2_holds is now caw_seg_WA2R .. P RW
   and wa2_post96 takes the free's hull budget and ends at caw_k_RR / caw_k_OOMR, SRrG at RW.
   (2) caw_pre IS THE TEXT'S 27 PREMISES (the room counts `sec_cnt S <= LSEC + DRV` and `ccnt24 S <= L24 + DRV` are
   entry premises after room_live_cf, :862-863, then the hull budget and HPOS), READ BY NAME: every former positional destruct of
   caw_pre in this file (which would now mis-bind: ck_frm0 moved by four) is the base's projections caw_pre_fpre, caw_pre_mn, ...,
   caw_pre_frm0. caw_carry still carries caw_cnt D (the top supplies it by caw_pre_cnt; the named argument CAW_CNT is
   gone), and RL_free_step's class-24 count reads it as before.
   (3) THE OUTCOME (:879-888) does not reach this segment: caw_dead rides on caw_at_null and caw_at_END's r = 1 arm only;
   caw_at_OOM, caw_prog, caw_ledger and the journal are unchanged; caw_at_X / caw_at_R end with hull_budget (Caw102A_Base.v:579, :607).
   CARRIED FROM THE f97c BASE: the cuts carry THE PROGRESS FACT caw_prog D E S (for any run position i at the entry
   state whose next events are E, a position i + length E of the cut's state): caw_ev1 D = [HMal (size + 1)] at
   caw_at_X / caw_at_R, caw_evs D = [HMal (size + 1); HFr (size + 1)] at caw_at_OOM. ex_value keeps it (its post's
   position keep, in the implication form, composed under caw_prog); on the refused arm the free steps it from
   caw_ev1 D to caw_evs D: caw_run_at_app splits the run, caw_run_at_nth gives the HFr (size + 1) event at i + 1,
   PresetRoomPosKeep.room_pos_keep_free the position S (i + 1) = i + 2 at the free's exit state. RL_free_step's
   class-24 count is ccnt24 S4 <= ccnt24 (cw_S D) + 1 <= L24 + DRV + 1 (wa2_ccnt24_app: ccnt24 counts the requests
   ablocks lists, and caw_scr adds the scratch's one block to the entry's). fpre's last conjunct frm_zero (fp_csr fx)
   (FRM0-ENTRY): ex_value's fpre is built with it at the call's float state fy, from the cut's caw_fl fy.
   The ledger: own = 0 crosses the hand steps +68 .. +92 by S1Ledger.prh_ledger_kept_aview (they write only
   sp0 - 48 .. sp0 - 32; the prh_pst bytes are low image bytes, pa_segs_low; Lam's heads lie in live blocks above the
   ceiling), ex_value by its text's post, reaches caw_at_R unchanged (memory unchanged to +128) and, on the refused arm,
   crosses __wrap_free by prh_ledger_kept_aview from the runtime row's image clause (acall_kept's third clause, given
   cwi_pst_img / cwi_pst_ok / cwi_pst_errno for every prh_pst byte) and its block clause (Lam's heads lie in entry
   blocks, apart from the scratch), to caw_at_OOM (memory unchanged +108 .. +252). The base names in this file's
   statements take the entry float state explicitly, (fx := fx).
   THE PROOF: one engine run +68 .. the call (YC1fPx paj_run_tok_x_inv at P); ex_value by YCbqGcallW.aj_call_xWF_sp at
   window e1 = 48 (q + 40 = sp + 48), FP = scratch, p, depth, differs, against HEXV (tex_value_specX at the call's float
   state, n = DOC_D, most = cw_most D, own = 0); its memnorm entry premise by PMN; P after it by PCALL from the text's
   fQmn keep; the float state composed (wa2_fregs_trans). At +96 (wa2_post96) the cut is rebuilt (Caw102A_Kit
   caw_st_ok_e), the beqz split by paj_branch: the read arm runs to +128 and hands to caw_k_RR (src_rd at that state by
   wa2_src_rd_J); the refused arm runs to the free, calls __wrap_free by the keep-carrying free rule under the
   re-hide, YGcallMxmnKeep.aj_free_x_ct_m_rh_keep at the cf instance (its `admits` premise by YG01.admits_fix at the
   free's fixed trace, the journal lifted to wle' by YCbqG.ajournal_xwR_mono and its wild budget dropped again by
   YCbqG.ajournal_xw_fix1R; the call memory's QMm_cf from the room, the hull budget (PresetHullPay.hull_ok_of_budget)
   and the reader form through YGcfAroBridge.arodata_ok_cf_of_P at caw_img's relro rows; the memnorm keep its last
   conjunct; P after it by PCALL), then runs +108 .. +252 over the R runner (YC1fPx.paj_run_to_x_invR at wle') and
   hands to caw_k_OOMR: ck_read x = None (wa2_read_none), the blocks the entry's (wa2_split_last), the room by
   YGcfRoomLive.RL_free_step at L24 + DRV + 1 (the class-24 count from caw_cnt D and the scratch, wa2_ccnt24_app; the
   batch-room inequality of CfRoomLivePreset.preset_rl_b24_ok), the position by caw_prog stepped through
   room_pos_keep_free, the ledger by prh_ledger_kept_aview.
   REFUTED BRANCH ARMS (no ASan report / abort site lies in +68 .. +252): at +96, `beqz a0` taken when ex_value refused
   (a0 = -1, text's None arm) and not taken when it read (a0 = 0, text's Some arm), both by computation on the text's r.
   THE ALLOCATOR PARAMETERS: cp := CfParamsPreset.CfParams_preset (CawA102's ruling: WA2 may bind it; the free's ledger
   keep needs the hidden head to cover its 8-byte size word, cf_head = 16).
   SECTION HYPOTHESES (owners; none new at this base, DW removed): PAL : PALib B (a Theorem Labs lane, the unit's image binding of B, as
   FuzzFree.v states it); AFREE : forall fz, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (the runtime free row
   under the re-hide with the memnorm keep at the leaf, YGcfMallocComposeKeep.v, at the call's float state); HEXV :
   forall fz, tex_value_specX B ARcfx SK DOC_D (a Theorem Labs lane's text, PRH_FnEx.v, discharged by
   the ex_value walk); CWI : caw_img B (the base's image facts, by computation at the instance where B is bound; owner
   the instantiation / a Theorem Labs lane); P / PLAW / PCALL / PMN (the generic-P form; the top instantiates P with
   Caw102A_Base.caw_mn). caw_cnt D is the base's (caw_carry's, from caw_pre_cnt at the top), not a hypothesis of this
   file.
   INPUTS (by path, as this tree carries them; blob pins name the kit's cut's copies, as history):
   lib/A/Prog/Caw102A_Base.v (caw_pre_* projections, caw_prog, caw_run_at_app, caw_run_at_nth, caw_cnt),
   Caw102A_Kit.v 3d241a90402d; the kit's texts: lib/A/PRH_FnEx.v (tex_value_specX),
   PRH_FnCheck.v c40cf3fdcd2a, PRH_Base.v (prh_univ_closure / prh_univ_closure_lit :1225-1257, prh_glob /
   prh_ledger with most own, prh_ledger_heads, prh_pst, prh_run_at :372, fpre :1004), PRH_Img.v (the #102 integration line's),
   lib/A/Prog/S1Ledger.v (prh_ledger_kept_aview, prh_ledger_hblock); lib/Reusable/YCbqG.v
   (ajx_* projections, ajournal_xw_fix1R :637), YG01.v 845507e218b0 (admits_fix), YGcallMxmnKeep.v
   (aj_free_x_ct_m_rh_keep :439), YCbqGcallW.v, YGcallx.v, YGcallcf.v, YG0dcf.v, YGcfRoomLive.v (ccnt24, rl_b24_ok, RL_free_step),
   YC1fPx.v, YSRrMemnorm.v, lib/Spec/PresetRoomPosKeep.v (room_pos_keep_free), PresetLiveBounds.v,
   lib/A/CfRoomLivePreset.v (preset_rl_b24_ok), CfParamsPreset.v, lib/A/Prog/PRW_StepKit.v (the #102 integration line's); the rest of the
   base header's list. Donors (restated, cited at each lemma): H2CawBase.v,
   ExvB_Open_sh.v, S8aItemsWalk.v,
   S4_PsFree.v.
   Numerals: 68 / 96 / 100 / 104 / 108 / 128 / 248 / 252 and 2616 / 2628 / 2648 / 2772 (= CAW_OFF + those) are DERIVED
   offsets; 80 / 72 / 64 / 56 / 48 / 40 / 32 / 24 / 16 / 8 / 4 / 36 / 20 are LENGTHs (frame, struct slots, cells, the
   window); 25712 / 25632 / 8192 / 30 / 33 / 34 are the kit's budgets, checked by vm_compute; 529888 is A_prog_base
   through cwi_base, checked by vm_compute; 2 ^ 31 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 / 4096 / 2147450880 (SHADOW_OFF) the
   bounds; register numbers WORD; atoms 2 / 10 / 32 / 33 / 240 DERIVED (the engine's numbering); 0 the own byte (WORD);
   1 / 2 the event counts (lengths of caw_ev1 / caw_evs). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW YGcallx YGcallcf YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
(* the free under the re-hide with the memnorm keep (part 3c took the keep out of the plain rules' posts) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit S1Ledger Caw102A_Base Caw102A_Kit.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
(* PRW_StepKit loads YF0v.v, which turns zify's euclidean-division equations off globally; back on here *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* compute the symbolic register a goal reads (H2CawBase.v caw_sv) *)
Ltac wa2_sv := lazymatch goal with |- context [sv_denot ?Ex (sr_get ?sr ?r)] =>
  let t' := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t' end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
(* the allocator parameters: preset's (CawA102 13:5xZ: WA2 may bind cp := CfParams_preset; the free's ledger keep needs
   the head to fill its 8-byte size word, cf_head = 16) *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instances CW_PrhImg CW_PAListing CW_RL.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation ARX := (ARcfx B).

Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
(* the free wrapper's runtime row under the re-hide, with the memnorm keep at the leaf (YGcfMallocComposeKeep.v), at
   every float state *)
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
Hypothesis HEXV : forall fz : YK11.FPState, tex_value_specX (fx := fz) B (ARcfx B) SK DOC_D.
Hypothesis CWI : caw_img (PA := PA) B.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Hypothesis PCALL : srr_inv_call SEGS P.
Hypothesis PMN : srr_inv_mn SEGS P.
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B (ARcfx B) cf_head := AR_laws_x_xs SEGS B LAWS_cf.
(* the world relation past a free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* an SRr run whose post is an SRrG fact at RW is an SRrG run at RW (wle is inside RW) *)
Lemma wa2_lift : forall W c (Q : world SEGS -> config -> Prop),
  SRr SEGS W c (fun W' c' => YA0nH.SRrG SEGS RW W' c' Q) -> YA0nH.SRrG SEGS RW W c Q.
Proof.
intros W c Q H.
apply (YA0nH.SRrG_bind SEGS RW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W c _ Q
  (YA0nH.SRr_SRrG SEGS RW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) W c _ H)).
intros W' c' _ H'. exact H'.
Qed.

(* ---- generic arithmetic / list facts ---- *)
Lemma wa2_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma wa2_req_ge : forall z, 0 <= z -> z <= req_size z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma wa2_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.
Lemma wa2_count_le : forall cid l, 0 <= count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.
Lemma wa2_split_last : forall (l l1 l2 : list (Z * Z)) x, l ++ [x] = l1 ++ x :: l2 -> ~ In x l -> l1 = l /\ l2 = [].
Proof.
induction l as [|y l IH]; intros l1 l2 x E Hn.
- destruct l1 as [|z l1]; cbn in E.
  + inversion E. split; reflexivity.
  + inversion E as [[Ez E2]]. destruct l1; discriminate.
- destruct l1 as [|z l1]; cbn in E.
  + inversion E; subst. exfalso. apply Hn. left. reflexivity.
  + inversion E as [[Ey E2]]. subst z.
    destruct (IH l1 l2 x E2 (fun H => Hn (or_intror H))) as [-> ->]. split; reflexivity.
Qed.
Lemma wa2_read_none : forall x, prhex_V 0 x = None -> ck_read x = None.
Proof.
intros x H. unfold prhex_V in H. unfold ck_read, PjGrammar.json_read, PjGrammar.jr_run. cbv beta.
change (Z.to_nat 0) with 0%nat in H.
destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 x []) as [[[[t' r]|] tr] ok']; cbn [fst] in H |- *;
  [discriminate H | reflexivity].
Qed.

(* ---- bytes kept ---- *)
Lemma wa2_vm_eq : forall (W W' : world SEGS) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W' mem') a n v.
Proof.
intros W W' mem mem' a n v HE Hv kk Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') mem mem' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma wa2_garr8_eq : forall (W W' : world SEGS) mem mem' p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  garr8 SEGS (rdW W mem) p L -> garr8 SEGS (rdW W' mem') p L.
Proof.
intros W W' mem mem' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') mem mem' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma wa2_vm8_4 : forall m a, val_mem SEGS m a 8 0 -> val_mem SEGS m a 4 0.
Proof.
intros m a H kk Hk. rewrite (H kk ltac:(lia)).
do 4 (destruct kk as [|kk]; [reflexivity|]). lia.
Qed.
Lemma wa2_apres_view : forall (H : word -> bool) mem a, apresent H mem a -> aview SEGS H mem a <> None.
Proof.
intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* ---- the read-only view at any state the journal from entry reaches (FP = [], cwi_pst_rw) ---- *)
Lemma wa2_rod : forall D ly' S' Hp' W' mem' md' k',
  caw_pre (fx := fx) B CTX0 D -> caw_J B SK D ly' S' Hp' W' mem' md' k' ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W') mem').
Proof.
intros D ly' S' Hp' W' mem' md' k' Hpre HJ a Hro Ho He.
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (_ & HR & _).
unfold caw_J in HJ. pose proof (ajx_img HJ) as Himg.
rewrite (Himg a); [exact (HR a Hro Ho He) | | exact Ho | exact He | | ].
- destruct Hro as [(sg & Hs & _ & Hr) | Hrel]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
- intros Hp. exact (cwi_pst_rw CWI a Hp Hro).
- apply fp_spares_closed. intros (r & Hin & _). destruct Hin.
Qed.
(* wa2_rod over a journal at any world relation R (caw_JR R) *)
Lemma wa2_rodR : forall (R : world SEGS -> world SEGS -> Prop) D ly' S' Hp' W' mem' md' k',
  caw_pre (fx := fx) B CTX0 D -> caw_JR B SK R D ly' S' Hp' W' mem' md' k' ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W') mem').
Proof.
intros R D ly' S' Hp' W' mem' md' k' Hpre HJ a Hro Ho He.
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (_ & HR & _).
unfold caw_JR in HJ. pose proof (ajxR_img HJ) as Himg.
rewrite (Himg a); [exact (HR a Hro Ho He) | | exact Ho | exact He | | ].
- destruct Hro as [(sg & Hs & _ & Hr) | Hrel]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
- intros Hp. exact (cwi_pst_rw CWI a Hp Hro).
- apply fp_spares_closed. intros (r & Hin & _). destruct Hin.
Qed.

(* ---- blocks ---- *)
Lemma wa2_blk_disj : forall ly S Hp W mem md p n q m, ARX ly S Hp W mem md ->
  In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
  p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S Hp W mem md p n q m HAR H1 H2 Hne.
pose proof (sep_blocks_x SEGS B ARX LAWS ly S Hp W mem md p n q m HAR H1 H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.
Lemma wa2_scr_new : forall D ly3 S3 Hp3 W3 mem3 md3 scr, ARX ly3 S3 Hp3 W3 mem3 md3 -> caw_scr B D ly3 S3 scr ->
  ~ In (scr, cw_size D + 1) (ablocks B (cw_ly D) (cw_S D)).
Proof.
intros D ly3 S3 Hp3 W3 mem3 md3 scr HAR (Hs4 & E) Hin.
assert (Hn : 0 <= cw_size D) by (unfold cw_size; lia).
assert (Hin' : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (scr, req_size (cw_size D + 1)) (scr, req_size (cw_size D + 1))
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Dj.
unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite wa2_req in Dj by lia. lia.
Qed.
Lemma wa2_scr_not_hp : forall D ly3 S3 Hp3 W3 mem3 md3 scr, caw_pre (fx := fx) B CTX0 D ->
  ARX ly3 S3 Hp3 W3 mem3 md3 ->
  caw_scr B D ly3 S3 scr -> ~ In scr (cw_Hp D).
Proof.
intros D ly3 S3 Hp3 W3 mem3 md3 scr Hpre HAR Hscr Hin.
pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL.
pose proof cf_head_nonneg as CH0.
assert (Hn0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof (wa2_scr_new D ly3 S3 Hp3 W3 mem3 md3 scr HAR Hscr) as Hnew.
pose proof (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HL) as HP. apply (Permutation_in _ HP) in Hin.
apply in_map_iff in Hin as ([a k] & Ea & HinL). cbn [fst] in Ea.
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL HinL) as (Hk0 & Hab & _).
destruct Hscr as (H4 & E).
assert (Hin1 : In (a - cf_head, k + cf_head) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; left; exact Hab).
assert (Hin2 : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (Z.eq_dec (k + cf_head) (cw_size D + 1)) as [Eq | Ne].
- apply Hnew. replace scr with (a - cf_head) by lia. rewrite <- Eq. exact Hab.
- assert (Ne' : (a - cf_head, k + cf_head) <> (scr, cw_size D + 1)) by (intros X; injection X; lia).
  pose proof (wa2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR Hin1 Hin2 Ne') as Dj.
  assert (Hk1 : 0 <= k + cf_head) by lia. assert (Hs1 : 0 <= cw_size D + 1) by lia.
  pose proof (req_size_pos _ Hk1). pose proof (req_size_pos _ Hs1). lia.
Qed.

(* ---- the shadow of a range inside a live block (ExvB_Open_sh.v exv_sh_blk, origin/cold/h-mani-a4-img 9b7851e2734,
   restated over the walk's ARcfx) ---- *)
Lemma wa2_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.
Lemma wa2_hp_apart : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own b m,
  ARX ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In b Hp ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hbn h Hh Hr.
pose proof (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HP.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hak). cbn [fst] in Eh.
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED Hak) as (Hk0 & Hblk & Hinp & _ & _).
rewrite Eh in Hblk, Hinp.
assert (Hne : (b, m) <> (h, k + cf_head)) by (intros E; injection E as -> _; exact (Hbn Hinp)).
pose proof (sep_blocks_x SEGS B ARX LAWS ly S Hp W mem md b m h (k + cf_head) HAR Hin Hblk Hne) as Hd.
pose proof cf_head_nonneg as CH0.
assert (Hk1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0) as [Hz|Hz]; lia).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hr Hk1. lia.
Qed.
Lemma wa2_sh_blk : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own a n,
  ARX ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_inblk B ly S Hp a n -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a n HAR HLED (b & m & Hin & Hba & Ham & Hhd) Hn.
pose proof (wa2_req_ge m) as Hreq.
pose proof cf_head_nonneg as CH0.
destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & _).
destruct (in_dec Z.eq_dec b Hp) as [Hbh | Hbn].
- specialize (Hhd Hbh).
  destruct (alx_hshadow SEGS B ARX LAWS ly S Hp W mem md b m HAR Hin Hbh) as (BS & HV).
  assert (Hm0 : 0 <= m).
  { destruct BS as (_ & Hm & _). unfold req_size in Hm. destruct (Z.eqb_spec m 0); lia. }
  split.
  + apply (block_shadow_range _ _ (b + cf_head) (req_size m - cf_head) a n BS); pose proof (Hreq Hm0); lia.
  + apply (wa2_hull_sub _ (b + cf_head) (req_size m - cf_head)); [apply HV | | ]; pose proof (Hreq Hm0); lia.
- destruct (alx_shadow SEGS B ARX LAWS ly S Hp W mem md b m HAR Hin
    (wa2_hp_apart ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hbn)) as (BS & HV).
  assert (Hm0 : 0 <= m).
  { destruct BS as (_ & Hm & _). unfold req_size in Hm. destruct (Z.eqb_spec m 0); lia. }
  split.
  + apply (block_shadow_range _ _ b (req_size m) a n BS); pose proof (Hreq Hm0); lia.
  + apply (wa2_hull_sub _ b (req_size m)); [exact HV | | ]; pose proof (Hreq Hm0); lia.
Qed.

Lemma wa2_div8 : forall a, 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof. intros a. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.

(* ---- the text, at any state the journal from entry reaches with the entry's blocks live and the entry's Hp ---- *)
Lemma wa2_src_rd_J : forall D ly' S' Hp' W' mem' md' k' Lam' pk' cn' fl' rn' mo' ow',
  caw_pre (fx := fx) B CTX0 D -> caw_J B SK D ly' S' Hp' W' mem' md' k' ->
  incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly' S') -> Hp' = cw_Hp D ->
  prh_ledger B ly' S' Hp' W' mem' Lam' pk' cn' fl' rn' mo' ow' ->
  src_rd W' mem' (cw_data D) (cw_x D).
Proof.
intros D ly' S' Hp' W' mem' md' k' Lam' pk' cn' fl' rn' mo' ow' Hpre HJ Hinc EHp HL.
pose proof (caw_pre_src (fx := fx) B CTX0 D Hpre) as HSRC. pose proof (caw_pre_inblk (fx := fx) B CTX0 D Hpre) as HINB.
unfold caw_J in HJ. pose proof (ajx_ar HJ) as HAR'. pose proof (ajx_blk HJ) as F2.
pose proof HSRC as (Hby & H4096 & Hce & Ham & Hra & Hhv).
destruct (Z.eq_dec (cw_size D) 0) as [H0|H0].
- assert (Hx : cw_x D = []) by (unfold cw_size in H0; destruct (cw_x D); [reflexivity | cbn in H0; lia]).
  rewrite Hx in *. split; [intros j Hj; cbn in Hj; lia|].
  split; [exact H4096|]. split; [exact Hce|]. split; [exact Ham|].
  split; [apply range_addressable_nil; cbn; lia | intros Hl; cbn in Hl; lia].
- assert (Hsz0 : 0 < cw_size D) by (unfold cw_size in *; lia).
  pose proof (HINB Hsz0) as Hib. pose proof Hib as (b & m & Hin & Hb & Hm & Hhd).
  split.
  + apply (wa2_garr8_eq (cw_W D) W' (cw_mem D) mem' _ _); [|exact Hby].
    intros a Ha. replace a with (b + (a - b)) by lia.
    apply (F2 b m); [exact Hin | exact (Hinc _ Hin) | | apply inFP_nil].
    pose proof (wa2_req_ge m) as Hr. unfold cw_size in *. split; [lia|].
    assert (0 <= m) by lia. specialize (Hr H). lia.
  + split; [exact H4096|]. split; [exact Hce|]. split; [exact Ham|].
    assert (Hib' : prhex_inblk B ly' S' Hp' (cw_data D) (cw_size D)).
    { exists b, m. split; [exact (Hinc _ Hin)|]. split; [exact Hb|]. split; [exact Hm|].
      intros Hh. apply Hhd. rewrite <- EHp. exact Hh. }
    destruct (wa2_sh_blk ly' S' Hp' W' mem' md' Lam' pk' cn' fl' rn' mo' ow' _ _ HAR' HL Hib' Hsz0) as [SR SH].
    split; [exact SR | intros _; exact SH].
Qed.

(* ---- the reader's tree (rc = 0), at any state the journal from entry reaches with the entry's blocks live ---- *)
Lemma wa2_tree_J : forall D ly' S' Hp' W' regs' mem' md' k',
  caw_pre (fx := fx) B CTX0 D -> caw_J B SK D ly' S' Hp' W' mem' md' k' ->
  incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly' S') -> cw_rc D = 0 ->
  prhex_tree ly' S' (cw_Lam D) W' regs' mem' (cw_doc D) (cw_t D) (cw_D D).
Proof.
intros D ly' S' Hp' W' regs' mem' md' k' Hpre HJ Hinc Hrc.
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAF0 & _).
pose proof (caw_pre_tree (fx := fx) B CTX0 D Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL0.
pose proof HAF0 as (HAR0 & _).
unfold caw_J in HJ. pose proof (ajx_ar HJ) as HAR'. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_frs HJ) as Hfrs.
pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2. pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4.
destruct (HTREE Hrc) as (HN & HDL & _ & (Hal8 & (cid & pos & Hfin & Hf1 & Hf2) & HRA0)).
destruct (alx_layout SEGS B ARX LAWS _ _ _ _ _ _ ly' HAR0 Hly) as (_ & Efr & _).
assert (Hfin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hfin).
destruct (alx_frames SEGS B ARX LAWS _ _ _ _ _ _ cid pos HAR' Hfin') as (Hfa32 & _ & Hpr & Hsh).
destruct (alx_frames SEGS B ARX LAWS _ _ _ _ _ _ cid pos HAR0 Hfin) as (Hfa32' & _ & _ & _).
rewrite Efr in Hpr, Hsh.
set (fa := frame_addr (cw_ly D) cid pos) in *.
set (fsb := fs_frame_bytes cid) in *.
pose proof cf_head_nonneg as CH0.
split; [|split; [|split]].
- apply (pj_nodeR_frame SEGS (cw_t D) _ _ _ _ _ HN).
  intros x Hx. destruct Hx as [Hx | ([a kk] & HinD & Hx)].
  + assert (Ea : aview SEGS (w_H W') mem' x = aview SEGS (w_H (cw_W D)) (cw_mem D) x).
    { apply (F4 cid pos x Hfin); [left; unfold frame_rng, in_zr; cbn [fst snd]; fold fa fsb; lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|].
    intros _. apply (apresent_writable SEGS). apply (proj1 (Hpr x ltac:(lia))).
  + destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL0 (HDL _ HinD)) as (Hk0 & Hab & _).
    unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
    assert (Hkk : 0 <= kk + cf_head) by lia. pose proof (wa2_req_ge _ Hkk) as Hr.
    assert (Ea : aview SEGS (w_H W') mem' x = aview SEGS (w_H (cw_W D)) (cw_mem D) x).
    { replace x with (a - cf_head + (x - (a - cf_head))) by lia.
      apply (F2 (a - cf_head) (kk + cf_head)); [exact Hab | exact (Hinc _ Hab) | lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|]. intros _.
    destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR' (Hinc _ Hab)) as (_ & _ & _ & _ & Hpb & _).
    apply (apresent_writable SEGS). apply (proj1 (Hpb x ltac:(lia))).
- right. left. exists cid, pos. split; [exact Hfin'|]. rewrite Efr. fold fa fsb. lia.
- apply (range_addressable_agree (aview SEGS (w_H (cw_W D)) (cw_mem D))); [|exact HRA0].
  intros x Hx. unfold shadow_of_addr.
  apply (F4 cid pos (SHADOW_OFF + x / 8) Hfin); [right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd]. fold fa fsb.
  pose proof (Z.div_mod fa 32 ltac:(lia)) as Dm. rewrite Hfa32' in Dm.
  pose proof (Z.div_mod (cw_doc D) 8 ltac:(lia)) as Dm8. rewrite Hal8 in Dm8.
  pose proof (wa2_div8 x) as Dx. pose proof (wa2_div8 (cw_doc D)) as Dd. pose proof (wa2_div8 fsb) as Ds.
  pose proof (wa2_div8 fa) as Df. lia.
- (* the hull: the frame is 64-aligned and its size a multiple of 64 *)
  assert (Hcid : 0 <= cid).
  { destruct (Z_lt_le_dec cid 0) as [Hn|Hn]; [exfalso|exact Hn].
    assert (Hf : fsb <= 32).
    { unfold fsb, fs_frame_bytes. replace cid with (- (- cid)) by lia. rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 by lia.
      apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      assert (2 <= 2 ^ (- cid)) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia). lia. }
    lia. }
  assert (Efsb : fsb = 64 * 2 ^ cid) by (unfold fsb, fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by exact Hcid; lia).
  assert (HFal : ly_F (cw_ly D) mod 4096 = 0) by exact (lo_F_al _ (alx_layout_ok SEGS B ARX LAWS _ _ _ _ _ _ HAR0)).
  assert (Efa : exists F, fa = 64 * F).
  { apply Z.mod_divide in HFal; [|lia]. destruct HFal as (u & Hu).
    exists (64 * u + 576 + cid * 16384 + pos * 2 ^ cid).
    unfold fa, frame_addr, fs_frame_off. fold fsb. rewrite Efsb, Hu. change kFakeFramesOff with 36864.
    change (Z.shiftl 1 kStackSizeLog) with 1048576. ring. }
  destruct Efa as (F & EF).
  set (w := 2 ^ cid) in *.
  intros s Hs. unfold shadow_addr in Hs.
  assert (Hi : 0 <= s - shadow_addr fa < fsb / 8).
  { unfold shadow_addr. rewrite EF, Efsb in *.
    replace (64 * F / 8) with (8 * F) by (replace (64 * F) with (F * 8 * 8) by ring; rewrite Z.div_mul by lia; ring).
    replace (64 * w / 8) with (8 * w) by (replace (64 * w) with (w * 8 * 8) by ring; rewrite Z.div_mul by lia; ring).
    pose proof (wa2_div8 (cw_doc D)) as Dd. pose proof (wa2_div8 (cw_doc D + 56 - 1)) as De.
    pose proof (wa2_div8 (SHADOW_OFF + cw_doc D / 8)) as Dl.
    pose proof (wa2_div8 (SHADOW_OFF + (cw_doc D + 56 - 1) / 8)) as Du.
    change SHADOW_OFF with 2147450880 in *. lia. }
  replace s with (shadow_addr fa + (s - shadow_addr fa)) by lia.
  apply wa2_apres_view. exact (proj1 (Hsh _ Hi)).
Qed.

(* wa2_src_rd_J over any world relation R (its journal conjuncts by name over R; none reads R): the text at a cut past
   the free, whose journal is at the re-hide relation *)
Lemma wa2_src_rd_JR : forall (R : world SEGS -> world SEGS -> Prop) D ly' S' Hp' W' mem' md' k' Lam' pk' cn' fl' rn' mo' ow',
  caw_pre (fx := fx) B CTX0 D -> caw_JR B SK R D ly' S' Hp' W' mem' md' k' ->
  incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly' S') -> Hp' = cw_Hp D ->
  prh_ledger B ly' S' Hp' W' mem' Lam' pk' cn' fl' rn' mo' ow' ->
  src_rd W' mem' (cw_data D) (cw_x D).
Proof.
intros R D ly' S' Hp' W' mem' md' k' Lam' pk' cn' fl' rn' mo' ow' Hpre HJ Hinc EHp HL.
pose proof (caw_pre_src (fx := fx) B CTX0 D Hpre) as HSRC. pose proof (caw_pre_inblk (fx := fx) B CTX0 D Hpre) as HINB.
unfold caw_JR in HJ. pose proof (ajxR_ar HJ) as HAR'. pose proof (ajxR_blk HJ) as F2.
pose proof HSRC as (Hby & H4096 & Hce & Ham & Hra & Hhv).
destruct (Z.eq_dec (cw_size D) 0) as [H0|H0].
- assert (Hx : cw_x D = []) by (unfold cw_size in H0; destruct (cw_x D); [reflexivity | cbn in H0; lia]).
  rewrite Hx in *. split; [intros j Hj; cbn in Hj; lia|].
  split; [exact H4096|]. split; [exact Hce|]. split; [exact Ham|].
  split; [apply range_addressable_nil; cbn; lia | intros Hl; cbn in Hl; lia].
- assert (Hsz0 : 0 < cw_size D) by (unfold cw_size in *; lia).
  pose proof (HINB Hsz0) as Hib. pose proof Hib as (b & m & Hin & Hb & Hm & Hhd).
  split.
  + apply (wa2_garr8_eq (cw_W D) W' (cw_mem D) mem' _ _); [|exact Hby].
    intros a Ha. replace a with (b + (a - b)) by lia.
    apply (F2 b m); [exact Hin | exact (Hinc _ Hin) | | apply inFP_nil].
    pose proof (wa2_req_ge m) as Hr. unfold cw_size in *. split; [lia|].
    assert (0 <= m) by lia. specialize (Hr H). lia.
  + split; [exact H4096|]. split; [exact Hce|]. split; [exact Ham|].
    assert (Hib' : prhex_inblk B ly' S' Hp' (cw_data D) (cw_size D)).
    { exists b, m. split; [exact (Hinc _ Hin)|]. split; [exact Hb|]. split; [exact Hm|].
      intros Hh. apply Hhd. rewrite <- EHp. exact Hh. }
    destruct (wa2_sh_blk ly' S' Hp' W' mem' md' Lam' pk' cn' fl' rn' mo' ow' _ _ HAR' HL Hib' Hsz0) as [SR SH].
    split; [exact SR | intros _; exact SH].
Qed.

(* wa2_tree_J over any world relation R (its journal conjuncts by name over R; none reads R) *)
Lemma wa2_tree_JR : forall (R : world SEGS -> world SEGS -> Prop) D ly' S' Hp' W' regs' mem' md' k',
  caw_pre (fx := fx) B CTX0 D -> caw_JR B SK R D ly' S' Hp' W' mem' md' k' ->
  incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly' S') -> cw_rc D = 0 ->
  prhex_tree ly' S' (cw_Lam D) W' regs' mem' (cw_doc D) (cw_t D) (cw_D D).
Proof.
intros R D ly' S' Hp' W' regs' mem' md' k' Hpre HJ Hinc Hrc.
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAF0 & _).
pose proof (caw_pre_tree (fx := fx) B CTX0 D Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL0.
pose proof HAF0 as (HAR0 & _).
unfold caw_JR in HJ. pose proof (ajxR_ar HJ) as HAR'. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4.
destruct (HTREE Hrc) as (HN & HDL & _ & (Hal8 & (cid & pos & Hfin & Hf1 & Hf2) & HRA0)).
destruct (alx_layout SEGS B ARX LAWS _ _ _ _ _ _ ly' HAR0 Hly) as (_ & Efr & _).
assert (Hfin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hfin).
destruct (alx_frames SEGS B ARX LAWS _ _ _ _ _ _ cid pos HAR' Hfin') as (Hfa32 & _ & Hpr & Hsh).
destruct (alx_frames SEGS B ARX LAWS _ _ _ _ _ _ cid pos HAR0 Hfin) as (Hfa32' & _ & _ & _).
rewrite Efr in Hpr, Hsh.
set (fa := frame_addr (cw_ly D) cid pos) in *.
set (fsb := fs_frame_bytes cid) in *.
pose proof cf_head_nonneg as CH0.
split; [|split; [|split]].
- apply (pj_nodeR_frame SEGS (cw_t D) _ _ _ _ _ HN).
  intros x Hx. destruct Hx as [Hx | ([a kk] & HinD & Hx)].
  + assert (Ea : aview SEGS (w_H W') mem' x = aview SEGS (w_H (cw_W D)) (cw_mem D) x).
    { apply (F4 cid pos x Hfin); [left; unfold frame_rng, in_zr; cbn [fst snd]; fold fa fsb; lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|].
    intros _. apply (apresent_writable SEGS). apply (proj1 (Hpr x ltac:(lia))).
  + destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL0 (HDL _ HinD)) as (Hk0 & Hab & _).
    unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
    assert (Hkk : 0 <= kk + cf_head) by lia. pose proof (wa2_req_ge _ Hkk) as Hr.
    assert (Ea : aview SEGS (w_H W') mem' x = aview SEGS (w_H (cw_W D)) (cw_mem D) x).
    { replace x with (a - cf_head + (x - (a - cf_head))) by lia.
      apply (F2 (a - cf_head) (kk + cf_head)); [exact Hab | exact (Hinc _ Hab) | lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|]. intros _.
    destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR' (Hinc _ Hab)) as (_ & _ & _ & _ & Hpb & _).
    apply (apresent_writable SEGS). apply (proj1 (Hpb x ltac:(lia))).
- right. left. exists cid, pos. split; [exact Hfin'|]. rewrite Efr. fold fa fsb. lia.
- apply (range_addressable_agree (aview SEGS (w_H (cw_W D)) (cw_mem D))); [|exact HRA0].
  intros x Hx. unfold shadow_of_addr.
  apply (F4 cid pos (SHADOW_OFF + x / 8) Hfin); [right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd]. fold fa fsb.
  pose proof (Z.div_mod fa 32 ltac:(lia)) as Dm. rewrite Hfa32' in Dm.
  pose proof (Z.div_mod (cw_doc D) 8 ltac:(lia)) as Dm8. rewrite Hal8 in Dm8.
  pose proof (wa2_div8 x) as Dx. pose proof (wa2_div8 (cw_doc D)) as Dd. pose proof (wa2_div8 fsb) as Ds.
  pose proof (wa2_div8 fa) as Df. lia.
- (* the hull: the frame is 64-aligned and its size a multiple of 64 *)
  assert (Hcid : 0 <= cid).
  { destruct (Z_lt_le_dec cid 0) as [Hn|Hn]; [exfalso|exact Hn].
    assert (Hf : fsb <= 32).
    { unfold fsb, fs_frame_bytes. replace cid with (- (- cid)) by lia. rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 by lia.
      apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      assert (2 <= 2 ^ (- cid)) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia). lia. }
    lia. }
  assert (Efsb : fsb = 64 * 2 ^ cid) by (unfold fsb, fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by exact Hcid; lia).
  assert (HFal : ly_F (cw_ly D) mod 4096 = 0) by exact (lo_F_al _ (alx_layout_ok SEGS B ARX LAWS _ _ _ _ _ _ HAR0)).
  assert (Efa : exists F, fa = 64 * F).
  { apply Z.mod_divide in HFal; [|lia]. destruct HFal as (u & Hu).
    exists (64 * u + 576 + cid * 16384 + pos * 2 ^ cid).
    unfold fa, frame_addr, fs_frame_off. fold fsb. rewrite Efsb, Hu. change kFakeFramesOff with 36864.
    change (Z.shiftl 1 kStackSizeLog) with 1048576. ring. }
  destruct Efa as (F & EF).
  set (w := 2 ^ cid) in *.
  intros s Hs. unfold shadow_addr in Hs.
  assert (Hi : 0 <= s - shadow_addr fa < fsb / 8).
  { unfold shadow_addr. rewrite EF, Efsb in *.
    replace (64 * F / 8) with (8 * F) by (replace (64 * F) with (F * 8 * 8) by ring; rewrite Z.div_mul by lia; ring).
    replace (64 * w / 8) with (8 * w) by (replace (64 * w) with (w * 8 * 8) by ring; rewrite Z.div_mul by lia; ring).
    pose proof (wa2_div8 (cw_doc D)) as Dd. pose proof (wa2_div8 (cw_doc D + 56 - 1)) as De.
    pose proof (wa2_div8 (SHADOW_OFF + cw_doc D / 8)) as Dl.
    pose proof (wa2_div8 (SHADOW_OFF + (cw_doc D + 56 - 1) / 8)) as Du.
    change SHADOW_OFF with 2147450880 in *. lia. }
  replace s with (shadow_addr fa + (s - shadow_addr fa)) by lia.
  apply wa2_apres_view. exact (proj1 (Hsh _ Hi)).
Qed.

(* ---- the live class-24 count past a step that adds the blocks l to a state's (the scratch's malloc, caw_scr):
   ccnt24 counts the requests ablocks lists (YGcfRoomLive.v, YG0d.ablocks), so it grows by at most
   length l; from the entry's room count caw_cnt D (the text's entry premise, caw_pre_cnt) it bounds RL_free_step's
   count ---- *)
Lemma wa2_filter_app_len : forall (f : Z -> bool) (l1 : list Z) (l2 : list (Z * Z)),
  Z.of_nat (length (List.filter f (l1 ++ map snd l2))) <= Z.of_nat (length (List.filter f l1)) + Z.of_nat (length l2).
Proof.
intros f l1 l2. rewrite filter_app, length_app, Nat2Z.inj_add.
assert (H : (length (List.filter f (map snd l2)) <= length l2)%nat).
{ clear l1. induction l2 as [|x t IH]; [cbn; lia|]. cbn [map List.filter]. destruct (f (snd x)); cbn [length]; lia. }
lia.
Qed.
Lemma wa2_ccnt24_app : forall ly S ly0 S0 l, ablocks B ly S = ablocks B ly0 S0 ++ l ->
  YGcfRoomLive.ccnt24 S <= YGcfRoomLive.ccnt24 S0 + Z.of_nat (length l).
Proof.
intros ly S ly0 S0 l E.
assert (Hm : forall ly' S', map snd (ablocks B ly' S') = map snd (YG01.blocks S')).
{ intros ly' S'. unfold ablocks. rewrite map_map. reflexivity. }
apply (f_equal (map snd)) in E. rewrite map_app, !Hm in E.
unfold YGcfRoomLive.ccnt24, PresetRoom.ccnt. rewrite E. apply wa2_filter_app_len.
Qed.

(* ---- the free's chain and trace: s0 holds rc (an int), never a frame pointer (H2CawBase.v caw_chain / caw_trace,
   origin/cold/h-hpreset-7-walk-H2H5 1934271f1f4) ---- *)
Lemma wa2_chain : forall ly rd regs rc0, 4096 <= raZ regs -> getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  2 ^ 31 <= spZ regs -> ly_top ly <= 2 ^ 47 -> chain_pre ly rd regs [].
Proof.
intros ly rd regs rc0 Hra Hs0 Hrc Hsp Htop. split; [exact Hra|].
destruct (frame0_ok ly regs); [|reflexivity].
replace (bad_next (spZ regs) (ly_top ly) (s0Z regs)) with true; [reflexivity|]. symmetry.
unfold bad_next, s0Z. rewrite Hs0. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- rewrite Z.mod_small by lia. apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
- replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
  apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.
Lemma wa2_trace : forall ly pc0 regs (U : list (list Z)), In [pc0] U -> In [pc0; raZ regs] U -> pc0 <> raZ regs ->
  In (call_trace ly pc0 regs []) U.
Proof.
intros ly pc0 regs U H1 H2 Hne. unfold call_trace. destruct (frame0_ok ly regs); [|exact H1].
unfold unwind_of_chain. cbn [flat_map app]. replace (raZ regs =? pc0) with false by (symmetry; apply Z.eqb_neq; lia).
exact H2.
Qed.

(* ---- the tree's footprint (rc = 0) at a state the journal from entry reaches: below the ceiling, apart from the
   scratch, off errno ---- *)
Lemma wa2_foot : forall D ly' S' Hp' W' mem' md' k' scr,
  caw_pre (fx := fx) B CTX0 D -> caw_J B SK D ly' S' Hp' W' mem' md' k' -> caw_scr B D ly' S' scr ->
  cw_rc D = 0 ->
  forall z, PRH_Reader.pj_footR (cw_doc D) (cw_D D) z ->
    z < YM05.alloc_ceiling /\ ~ (scr <= z < scr + (cw_size D + 1)) /\ ~ (as_errno B <= z < as_errno B + 4).
Proof.
intros D ly' S' Hp' W' mem' md' k' scr Hpre HJ Hscr Hrc z Hz.
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAF0 & _).
pose proof (caw_pre_tree (fx := fx) B CTX0 D Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL0.
pose proof HAF0 as (HAR0 & _).
unfold caw_J in HJ. pose proof (ajx_ar HJ) as HAR'. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_frs HJ) as Hfrs.
destruct (HTREE Hrc) as (HN & HDL & _ & (Hal8 & (cid & pos & Hfin & Hf1 & Hf2) & HRA0)).
destruct (alx_layout SEGS B ARX LAWS _ _ _ _ _ _ ly' HAR0 Hly) as (Eab & Efr & _).
assert (Hfin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hfin).
pose proof Hscr as (Hs4 & Escr).
assert (Hscrb : In (scr, cw_size D + 1) (ablocks B ly' S')) by (rewrite Escr; apply in_or_app; right; left; reflexivity).
pose proof (wa2_scr_new D ly' S' Hp' W' mem' md' scr HAR' Hscr) as Hnew.
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof (proj1 (proj2 (pal_env B PAL))) as ERRIMG.
pose proof cf_head_nonneg as CH0.
destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR' Hscrb) as (_ & _ & Hsce & _).
rewrite wa2_req in Hsce by lia.
destruct Hz as [Hz | ([a kk] & HinD & Hz)].
- destruct (alx_sep SEGS B ARX LAWS _ _ _ _ _ _ HAR') as (Hpw & Hfr).
  rewrite Forall_forall in Hfr. pose proof (Hfr (cid, pos) Hfin') as (Hf4096 & Hfce). cbn [fst snd] in Hf4096, Hfce.
  rewrite Efr in Hf4096, Hfce.
  split; [lia|]. split.
  + intros Hzs. destruct (YG0s.pairwise_app_inv _ _ _ Hpw) as (_ & _ & Hx).
    assert (H1 : In (scr, req_size (cw_size D + 1)) (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly' S')))
      by (apply (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hscrb)).
    assert (H2 : In (frame_addr ly' cid pos, fs_frame_bytes cid)
      (map (fun f : Z * Z => (frame_addr ly' (fst f) (snd f), fs_frame_bytes (fst f))) (frames S')))
      by (apply (in_map (fun f : Z * Z => (frame_addr ly' (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hfin')).
    pose proof (Hx _ _ H1 H2) as Dj. unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite wa2_req in Dj by lia.
    pose proof (Efr cid pos). lia.
  + intros He. apply (frm_img_x SEGS B ARX LAWS _ _ _ _ _ _ cid pos z HAR0 Hfin); [lia|]. exact (ERRIMG z He).
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL0 (HDL _ HinD)) as (Hk0 & Hab & _).
  unfold pj_holdsR in Hz; cbn [fst snd] in Hz.
  assert (Hkk : 0 <= kk + cf_head) by lia. pose proof (wa2_req_ge _ Hkk) as Hr.
  assert (Hab' : In (a - cf_head, kk + cf_head) (ablocks B ly' S')) by (rewrite Escr; apply in_or_app; left; exact Hab).
  destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR' Hab') as (_ & _ & Hbce & _).
  split; [lia|]. split.
  + assert (Ne : (a - cf_head, kk + cf_head) <> (scr, cw_size D + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hab).
    pose proof (wa2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR' Hab' Hscrb Ne) as Dj. rewrite (wa2_req (cw_size D + 1)) in Dj by lia.
    lia.
  + intros He. apply (blk_img_x SEGS B ARX LAWS _ _ _ _ _ _ _ _ z HAR' Hab'); [lia|]. exact (ERRIMG z He).
Qed.

(* ---- small symbolic-state facts ---- *)
Lemma wa2_denot_off : forall E n x v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = w64 (v + x).
Proof.
intros E n x v H Hv Hvx. apply bv_eq. rewrite denot_SOff, H, unsigned_lit_small by lia.
unfold w64. rewrite unsigned_lit_small by lia. unfold zcanon, M64; apply Z.mod_small. lia.
Qed.
Lemma wa2_frame_view : forall (W : world SEGS) E rs (m m' : word -> option byte) a,
  frame_of E rs (rdW W m) (rdW W m') -> ~ in_wrange E rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W E rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma wa2_achain0 : forall ly rd sp v, v < YM05.alloc_ceiling \/ ly_top ly - 16 <= v -> achain ly rd sp v [].
Proof. intros ly rd sp v H. left. split; [destruct H; [left | right; left]; assumption | reflexivity]. Qed.
Lemma wa2_s0_bound : forall regs ly rc0, getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 -> ly_top ly <= 2 ^ 47 ->
  s0Z regs < YM05.alloc_ceiling \/ ly_top ly - 16 <= s0Z regs.
Proof.
intros regs ly rc0 H Hrc Ht. pose proof YM05.alloc_ceiling_val as HC.
unfold s0Z. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- rewrite Z.mod_small by lia. left. lia.
- right. replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity). lia.
Qed.
Lemma wa2_v_val : forall E rc0 doc0, U E (SOff 8 0) = rc0 mod 2 ^ 64 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  U E (SOff 9 0) = doc0 -> 0 <= doc0 < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 8 0)) (SLit (-1))) (SOff 9 0)) =
  if rc0 =? 0 then doc0 else 0.
Proof.
intros E rc0 doc0 H8 Hrc H9 Hd. rewrite !U_SAlu, !U_SLit, H8, H9. cbn [zalu_raw].
change (zcanon (-1)) with (2 ^ 64 - 1). change (zcanon 0) with 0.
destruct (Z.eqb_spec rc0 0) as [->|Hn].
- change (0 mod 2 ^ 64) with 0. replace (0 <? 0) with false by reflexivity. change (zcanon 0) with 0.
  change (zcanon (0 + (2 ^ 64 - 1))) with (2 ^ 64 - 1). change (2 ^ 64 - 1) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small doc0) by lia. unfold zcanon, M64; apply Z.mod_small. lia.
- assert (Hm : 0 < rc0 mod 2 ^ 64).
  { destruct (Z_le_gt_dec 0 rc0) as [Hp|Hq]; [rewrite Z.mod_small by lia; lia|].
    replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
      rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity). lia. }
  rewrite (proj2 (Z.ltb_lt 0 (rc0 mod 2 ^ 64)) Hm). change (zcanon 1) with 1.
  change (zcanon (1 + (2 ^ 64 - 1))) with 0. rewrite Z.land_0_l. reflexivity.
Qed.

Lemma wa2_pres : forall regs regs' (r : bv 5), acallee_saved (bv_unsigned r) -> aregs_preserved regs regs' ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r Hr Hp. pose proof (Hp _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma wa2_kregs_pres : forall D regs regs', caw_kregs D regs -> aregs_preserved regs regs' -> caw_kregs D regs'.
Proof.
intros D regs regs' Hk Hp r Hr. rewrite <- (Hk r Hr). apply wa2_pres; [|exact Hp].
cbn [In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr]; [vm_compute (bv_unsigned _); lia|]). destruct Hr.
Qed.

(* fpre's raZ bound at ex_value's call: the return slot +96 is a slot of the listing (CLOSED, outside the big proof) *)
Lemma wa2_ret_slot_ceil : bv_unsigned (Z_to_bv 64 (BASE + (CAW_OFF + 96))) < YM05.alloc_ceiling.
Proof.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
pose proof (pa_slot_lt_ceil_b (PL := PL_caw_A) (PI := PA) (CAW_OFF + 96) ltac:(rewrite CAW_OFF_val; lia)
  ltac:(vm_compute; reflexivity)) as H.
rewrite unsigned_lit_small; [exact H|]. rewrite CAW_OFF_val. lia.
Qed.

Definition wa2_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition wa2_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

(* ---- the cut after ex_value's return (+96): the result r in a0, the struct as ex_value's text leaves it ---- *)
Lemma wa2_post96 : forall Q D fy ly4 S4 Hp4 W4 regs4 mem4 md4 k4 scr r p' dl',
  caw_carry (fx := fx) B SK CTX0 D fy ly4 S4 Hp4 W4 regs4 mem4 md4 k4 ->
  caw_prog D (caw_ev1 D) S4 ->
  getr regs4 8 = w64 (cw_rc D) -> getr regs4 9 = w64 (cw_doc D) -> getr regs4 18 = w64 SHADOW_OFF ->
  getr regs4 10 = w64 r ->
  val_mem SEGS (rdW W4 mem4) (cw_sp0 D - 72) 8 (cw_data D + p') ->
  val_mem SEGS (rdW W4 mem4) (cw_sp0 D - 64) 8 (cw_data D + cw_size D) ->
  val_mem SEGS (rdW W4 mem4) (cw_sp0 D - 48) 8 scr ->
  val_mem SEGS (rdW W4 mem4) (cw_sp0 D - 40) 4 dl' -> (dl' = 0 \/ dl' = 1) ->
  caw_scr B D ly4 S4 scr -> caw_ledger B D ly4 S4 Hp4 W4 mem4 0 ->
  PresetHullBudget.hull_budget S4 [PresetReqAt.HFr (cw_size D + 1)] ->
  match prhex_V 0 (cw_x D) with
  | None => r = -1
  | Some (u, rest) => r = 0 /\ p' = cw_size D - Z.of_nat (length rest) /\ (dl' = 1 <-> cw_rc D = 0 /\ cw_t D <> u)
  end ->
  caw_k_RR (fx := fx) B SK CTX0 P RW Q D -> caw_k_OOMR (fx := fx) B SK CTX0 P RW Q D -> P mem4 ->
  YA0nH.SRrG SEGS RW W4 (caw_cfg fy 96 regs4 mem4 md4) (caw_QP P Q).
Proof.
intros Q D fy ly4 S4 Hp4 W4 regs4 mem4 md4 k4 scr r p' dl' HC HRP R8 R9 R18 R10 V72 V64 V48 V40 Hdl HSCR HL HHB HM KR
  KOOM HP4.
unfold caw_ledger in HL.
pose proof HC as (Hpre & Hcnt & Hfl & HJ & Hkr & Hsp & HSV & EHp & HRL & HROD).
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAF & HROD0 & Hshi64 & Hraceil & Hfrm0).
pose proof (caw_pre_mn (fx := fx) B CTX0 D Hpre) as HMN0. pose proof (caw_pre_univ (fx := fx) B CTX0 D Hpre) as HUNIV.
pose proof (caw_pre_r10 (fx := fx) B CTX0 D Hpre) as H10. pose proof (caw_pre_r11 (fx := fx) B CTX0 D Hpre) as H11.
pose proof (caw_pre_r12 (fx := fx) B CTX0 D Hpre) as H12. pose proof (caw_pre_r13 (fx := fx) B CTX0 D Hpre) as H13.
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc. pose proof (caw_pre_doc (fx := fx) B CTX0 D Hpre) as Hdoc.
pose proof (caw_pre_size (fx := fx) B CTX0 D Hpre) as Hsz. pose proof (caw_pre_data0 (fx := fx) B CTX0 D Hpre) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B CTX0 D Hpre) as Hd62. pose proof (caw_pre_src (fx := fx) B CTX0 D Hpre) as HSRC.
pose proof (caw_pre_inblk (fx := fx) B CTX0 D Hpre) as HINB. pose proof (caw_pre_case (fx := fx) B CTX0 D Hpre) as HCASE.
pose proof (caw_pre_tree (fx := fx) B CTX0 D Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL0.
pose proof (caw_pre_ran (fx := fx) B CTX0 D Hpre) as Hran0. pose proof (caw_pre_live (fx := fx) B CTX0 D Hpre) as HLIVE.
pose proof (caw_pre_max (fx := fx) B CTX0 D Hpre) as HMAX. pose proof (caw_pre_frames (fx := fx) B CTX0 D Hpre) as HFR.
pose proof (caw_pre_room (fx := fx) B CTX0 D Hpre) as HRL0. pose proof (caw_pre_frm0 (fx := fx) B CTX0 D Hpre) as Hfrm.
pose proof HAF as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK_check_as_written = 25712) by (vm_compute; reflexivity).
unfold caw_J in HJ. unfold CAW_FRAME in Hsp. unfold cw_sp0 in *.
set (sp0 := spZ (cw_regs D)) in *.
pose proof YM05.alloc_ceiling_val as HCEIL.
assert (Hsp0 : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
pose proof (cwi_base CWI) as CWB.
assert (HBASE : BASE = 529888) by (rewrite CWB; vm_compute; reflexivity).
pose proof HSCR as (Hs4096 & Eab4).
pose proof (ajx_ar HJ) as HAR4. pose proof (ajx_ly HJ) as Hly4.
pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & Eslo4 & Eshi4 & _).
assert (Hscrb : In (scr, cw_size D + 1) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_or_app; right; left; reflexivity).
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof cf_head_nonneg as CH0.
destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR4 Hscrb) as (_ & _ & Hsce & _).
rewrite wa2_req in Hsce by lia.
set (vals := [scr]).
assert (HS : st_ok_pi (fx := fy) SEGS VAL (caw_Ee regs4 sp0 vals)
  (mkSS (CAW_OFF + 96) caw_sr80 [caw_fregion_e [(-48, 8%N)] 0 0] None wa2_facts)
  (restrict (w_H W4) (@YK11.mkst fy regs4 (Z_to_bv 64 (BASE + (CAW_OFF + 96))) mem4 (YK11.seg_rom SEGS)))).
{ apply (@caw_st_ok_e fy rc PA).
  - vm_compute. reflexivity.
  - cbn. lia.
  - unfold CAW_FRAME. lia.
  - unfold CAW_FRAME. lia.
  - intros o Ho. lia.
  - cbn [caw_vals_ok vals]. replace (sp0 + -48) with (sp0 - 48) by lia. change (N.to_nat 8) with 8%nat.
    change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8. split; [exact V48|]. split; [lia|]. split; [lia | exact I].
  - unfold facts_ok, wa2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite caw_Ee_sp, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia]. }
set (E := caw_Ee regs4 sp0 vals) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W4) mem4)) by (unfold sh_ok; apply Forall_nil).
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply caw_Ee_sp).
assert (EregE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv -> ew E n = getr regs4 r)
  by (intros n r0 Hn Hr; subst E; exact (caw_Ee_reg regs4 _ vals n r0 Hn Hr)).
assert (HAE : env_agree 32 (Ereg (regupd regs4 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E)
  by (subst E; apply caw_Ee_agree).
assert (UR : U E (SOff 10 0) = r mod 2 ^ 64).
{ rewrite U_SOff, (EregE 10%nat 10%bv eq_refl ltac:(discriminate)), R10. unfold w64. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, zcanon, M64. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
  reflexivity. }
pose (RUN := paj_run_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_caw_A) (PI := PA) B prh_pst ARX LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_caw_A) (PI := PA) B prh_pst ARX LAWS P PLAW).
pose (BR := paj_branch (fx := fy) (L := A_prog_listing) (PI := PA)).
apply wa2_lift.
unfold caw_cfg, caw_pc. replace (BASE + CAW_OFF + 96) with (BASE + (CAW_OFF + 96)) by lia.
psrr_branch_tok RUN BR HS SHOK wa2_Bspan.
- (* +96 taken: ex_value read a value (a0 = 0) *)
  rewrite branch_eq_U, UR, U_SLit in Hc.
  destruct (prhex_V 0 (cw_x D)) as [[u rest]|] eqn:EV;
    [| exfalso; rewrite HM in Hc; vm_compute in Hc; discriminate Hc].
  destruct HM as (Hr0 & Hp' & Hdlu).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HP4 wa2_Bspan (CAW_OFF + CAW_PC_R).
  { intros a (r0 & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. lia. }
  assert (Emem : ms_mem ms = mem4).
  { apply functional_extensionality. intros x. apply HF. intros (r0 & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. lia. }
  pose proof (regs_kept_of_st_ok_pi E _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HKP0.
  cbn [ms_regs restrict] in HKP0.
  assert (HKP : forall r0 : bv 5, In r0 [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms) r0 = getr regs4 r0).
  { intros r0 Hr. rewrite (HKP0 r0 Hr). apply caw_getr_upd_other. intros ->. cbn [In] in Hr.
    repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
  assert (Hsp6 : spZ (ms_regs ms) = sp0 - CAW_FRAME).
  { apply (caw_sp_st (fz := fy) (w_H W4) E _ ms sp0 HS); [vm_compute; reflexivity | exact E2 | unfold CAW_FRAME; lia]. }
  pmkst HS. rewrite Emem in HJ, HP4 |- *.
  replace (BASE + 2648) with (caw_pc CAW_PC_R) by (unfold caw_pc, CAW_PC_R; rewrite CAW_OFF_val; lia).
  apply SRr_ret. cbv beta.
  apply (KR fy ly4 S4 Hp4 W4 (ms_regs ms) mem4 _ k4 scr u rest dl'); [|exact HP4].
  assert (Hinc4 : incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly4 S4))
    by (intros x Hx; rewrite Eab4; apply in_or_app; left; exact Hx).
  refine (conj _ (conj HRP (conj _ (conj _ (conj _ (conj EV (conj _ (conj V64 (conj V48 (conj V40 (conj Hdl
    (conj Hdlu (conj _ (conj HSCR (conj HL HHB))))))))))))))).
  + refine (conj Hpre (conj Hcnt (conj Hfl (conj HJ (conj _ (conj Hsp6 (conj HSV (conj EHp (conj HRL HROD))))))))).
    intros r1 Hr1. rewrite (HKP r1 ltac:(cbn [In] in Hr1 |- *; tauto)). exact (Hkr r1 Hr1).
  + rewrite (HKP 8%bv ltac:(cbn; tauto)). exact R8.
  + rewrite (HKP 9%bv ltac:(cbn; tauto)). exact R9.
  + rewrite (HKP 18%bv ltac:(cbn; tauto)). exact R18.
  + replace (cw_data D + cw_size D - Z.of_nat (length rest)) with (cw_data D + p') by lia. exact V72.
  + exact (wa2_src_rd_J D ly4 S4 Hp4 W4 mem4 _ k4 _ _ _ _ _ _ _ Hpre HJ Hinc4 EHp HL).
- (* +96 not taken: refused (a0 = -1) *)
  rewrite branch_eq_U, UR, U_SLit in Hc.
  destruct (prhex_V 0 (cw_x D)) as [[u rest]|] eqn:EV;
    [exfalso; destruct HM as (Hr0 & _); rewrite Hr0 in Hc; vm_compute in Hc; discriminate Hc|].
  rewrite HM in Hc.
  paj_run_tok_x_inv RUN HS HJ SHOK HP4 wa2_Bspan.
  { intros a (r0 & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. lia. }
  assert (Emem : ms_mem ms = mem4).
  { apply functional_extensionality. intros x. apply HF. intros (r0 & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. lia. }
  pose proof (regs_kept_of_st_ok SEGS E _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HKP0.
  cbn [ms_regs restrict] in HKP0.
  assert (HKP : forall r0 : bv 5, In r0 [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms) r0 = getr regs4 r0).
  { intros r0 Hr. rewrite (HKP0 r0 Hr). apply caw_getr_upd_other. intros ->. cbn [In] in Hr.
    repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
  assert (Hspm : spZ (ms_regs ms) = sp0 - 80).
  { unfold spZ. rewrite (st_ok_restrict_reg SEGS (w_H W4) E _ ms 2%bv HS). wa2_sv.
    rewrite (wa2_denot_off E 2 (-80) sp0 E2) by lia. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (G10 : getr (ms_regs ms) 10 = w64 scr).
  { rewrite (st_ok_restrict_reg SEGS (w_H W4) E _ ms 10%bv HS). wa2_sv.
    rewrite (wa2_denot_off E 33 0 scr); [f_equal; lia | | lia | lia].
    subst E vals. exact (caw_Ee_val regs4 sp0 [scr] 0 ltac:(lia)). }
  assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CAW_OFF + 108))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W4) E _ ms 1%bv HS). wa2_sv.
    replace (CAW_OFF + 108) with 2628 by (rewrite CAW_OFF_val; reflexivity). exact (codeptr_val E 2628 HEI). }
  rewrite Emem in HJ, HP4.
  pose proof (wa2_scr_new D ly4 S4 Hp4 W4 mem4 _ scr HAR4 HSCR) as Hnew.
  pose proof (wa2_scr_not_hp D ly4 S4 Hp4 W4 mem4 _ scr Hpre HAR4 HSCR) as Hnhp.
  assert (Hinc4 : incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly4 S4))
    by (intros x Hx; rewrite Eab4; apply in_or_app; left; exact Hx).
  pose proof (ajx_ar HJ) as HAR4'. pose proof (ajx_qt HJ) as HQT4.
  pose proof (pal_rt_below B PAL) as (Hrtf & _).
  pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
  assert (Hsite : In (BASE + (CAW_OFF + 108)) (pi_ret_sites F_check_as_written RT_free))
    by (rewrite HBASE, CAW_OFF_val; vm_compute; left; reflexivity).
  assert (Hraw : 0 <= BASE + (CAW_OFF + 108) < 2 ^ 64) by (rewrite HBASE, CAW_OFF_val; lia).
  (* the free's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
     post carries the trace in the journal's wild budget, which ajournal_xw_fix1R drops again) *)
  assert (HTRf : In (call_trace ly4 (pc_free_ra0 (as_code B)) (ms_regs ms) []) (as_universe B)).
  { apply wa2_trace.
    + exact (proj1 HUNIV RT_free).
    + pose proof (prh_univ_closure_lit B CTX0 F_check_as_written RT_free _ HUNIV Hsite) as Htr.
      unfold raZ. rewrite G1, unsigned_lit_small by exact Hraw.
      unfold prh_trace in Htr. cbn [flat_map app prh_pc0] in Htr.
      rewrite (proj2 (Z.eqb_neq (BASE + (CAW_OFF + 108)) (pc_free_ra0 (as_code B)))) in Htr
        by (rewrite CAW_OFF_val; lia).
      exact Htr.
    + unfold raZ. rewrite G1, unsigned_lit_small by exact Hraw. rewrite CAW_OFF_val. lia. }
  (* ---- the free of the scratch, under the re-hide, with the keep ---- *)
  apply SRr_ret. cbv beta.
  eapply (YA0nH.SRrG_bind SEGS RW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  { eapply (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (fx := fy) (SK := SK) SEGS B prh_pst LAWS (@pa_segs_low _ _ PA)
      (pal_env B PAL) (ARx_owned_low_law_xs SEGS B LAWS_cf) (ARx_wf_law_xs SEGS B)
      (alloc_model_laws_x_cf B (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR0))) (AFREE fy)
      W4 E _ ms STK_check_as_written sp0 [] (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) [] ly4 S4 Hp4 _ k4
      scr (cw_size D + 1) (-80) (ew E 2) (Z_to_bv 64 (BASE + (CAW_OFF + 108))) [] HS).
    - exact (pal_free B PAL).
    - reflexivity.
    - rewrite Emem. apply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst _ (@wle SEGS) RW
        (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)). exact HJ.
    - exact Hscrb.
    - rewrite EHp. exact Hnhp.
    - exact G10.
    - rewrite (st_ok_restrict_reg SEGS (w_H W4) E _ ms 2%bv HS). wa2_sv. reflexivity.
    - reflexivity.
    - rewrite E2. apply unsigned_lit_small. lia.
    - reflexivity.
    - lia.
    - rewrite HSTK. unfold ASTACK. lia.
    - rewrite (HKP 3%bv ltac:(cbn; tauto)), (Hkr 3%bv ltac:(cbn; tauto)). exact Hgp0.
    - rewrite (HKP 4%bv ltac:(cbn; tauto)), (Hkr 4%bv ltac:(cbn; tauto)). exact Htp0.
    - exact G1.
    - apply (ret_ok_codeptr_v (PI := PA)); rewrite CAW_OFF_val; [lia | reflexivity].
    - (* the call memory's QMm_cf: the room, cf_hull_ok from the cut's hull budget, arodata_ok_cf from the cut's
         reader form through the bridge at caw_img's relro rows *)
      destruct (QM_cf_of_room SEGS B ly4 S4 Hp4 W4 mem4 _ (proj1 HAR4') HQT4 (YGcfRoomLive.room_live_room S4 HRL)
        (PresetHullPay.hull_ok_of_budget _ _ HHB)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
      rewrite Emem. destruct (cwi_relro_eq CWI) as [ERL ERH].
      apply (YGcfAroBridge.arodata_ok_cf_of_P SEGS B W4 mem4 (cwi_relro_seg CWI) (cwi_errno_relro CWI)
        (cwi_relro_top CWI) (cwi_ro_reads_nw CWI)).
      rewrite ERL, ERH. exact HROD.
    - apply (wa2_chain _ _ _ (cw_rc D)).
      + unfold raZ. rewrite G1, unsigned_lit_small by exact Hraw. rewrite HBASE, CAW_OFF_val. lia.
      + rewrite (HKP 8%bv ltac:(cbn; tauto)). exact R8.
      + exact Hrc.
      + rewrite Hspm. lia.
      + rewrite Etop4. lia.
    - exact (admits_fix _ _ _ (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR0)) HTRf).
    - intros Hin. exfalso. exact (Hnew Hin). }
  cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & Eab4' & Eab5) & Hfr5 & Hpre5
    & Hun5 & (q & trc & Hq & Hqin & Hpath & Hg & Hleaf) & Hkept & Hmn5).
  rewrite Emem in Hkept, Hmn5, Hpre5.
  (* the journal after the call: the fixed trace leaves the budget *)
  pose proof (ajournal_xw_fix1R HTRf HJ5) as HJ5f. clear HJ5. rename HJ5f into HJ5.
  assert (HPM5 : P mem5) by exact (PCALL mem4 mem5 Hmn5 HP4).
  assert (Eab0 : ablocks B ly5 S5 = ablocks B (cw_ly D) (cw_S D)).
  { rewrite Eab4 in Eab4'. destruct (wa2_split_last _ _ _ _ Eab4' Hnew) as [-> ->]. rewrite Eab5, app_nil_r. reflexivity. }
  unfold acall_kept_x, acall_kept in Hkept. destruct Hkept as (K1 & K2 & K3 & _ & _ & _).
  pose proof (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ Hpre5) as Hpre5cf.
  (* the class-24 count at the free's entry state S4: the entry's (caw_carry's caw_cnt D, the text's room count) plus the
     scratch's one block (caw_scr: S4's blocks are the entry's and the scratch) *)
  assert (HC24 : YGcfRoomLive.ccnt24 S4 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1).
  { pose proof (wa2_ccnt24_app ly4 S4 (cw_ly D) (cw_S D) _ Eab4) as Hc24s. cbn [length] in Hc24s.
    destruct Hcnt as (_ & Hc24e). clear - Hc24s Hc24e. lia. }
  assert (HRL5 : room_live_cf S5).
  { exact (YGcfRoomLive.RL_free_step SEGS B ly4 S4 Hp4 W4 (ms_regs ms) mem4 _ [] (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1)
      q _ trc ((), S5) Hpre5cf (conj HC24 (proj2 (CfRoomLivePreset.preset_rl_b24_ok (cw_S D) (proj2 Hcnt)))) HRL Hpath). }
  assert (Hqnn : q <> PNull) by (intros ->; cbn in Hq; lia).
  (* the progress fact after the free: the run's next events at i are caw_ev1 D then HFr (size + 1); caw_prog at
     caw_ev1 D gives a position i + 1 at S4, room_pos_keep_free the next one at S5 *)
  assert (HRP5 : caw_prog D (caw_evs D) S5).
  { intros rsm rx ros ri rH0 rhist Hpos Hrun.
    change (caw_evs D) with (caw_ev1 D ++ [PresetReqAt.HFr (cw_size D + 1)]) in Hrun.
    destruct (caw_run_at_app rsm rx ros ri _ _ Hrun) as (Hr1 & Hr2).
    destruct (HRP rsm rx ros ri rH0 rhist Hpos Hr1) as (rhist4 & Hrp4).
    pose proof (caw_run_at_nth rsm rx ros _ _ _ Hr2) as HEVF.
    pose proof (PresetRoomPosKeep.room_pos_keep_free SEGS B ly4 S4 Hp4 W4 (ms_regs ms) mem4 _ [] rsm rx ros
      (ri + length (caw_ev1 D))%nat rH0 rhist4 q (cw_size D + 1) _ trc S5 Hpre5cf Hun5 Hqin Hqnn Hpath Hrp4 HEVF) as Hrp5.
    exists (rhist4 ++ YGcfRoom.freed_cf S4 q).
    replace (ri + length (caw_evs D))%nat with (Datatypes.S (ri + length (caw_ev1 D)))
      by exact (eq_sym (Nat.add_succ_r ri 1)).
    exact Hrp5. }
  (* every prh_pst byte is kept by the free: an image byte (cwi_pst_img) off the owned statics (cwi_pst_ok) and errno
     (cwi_pst_errno), acall_kept's image clause *)
  assert (KP5 : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) mem4 a).
  { intros a Ha. exact (K3 a (cwi_pst_img CWI a Ha) (proj2 (cwi_pst_ok CWI a Ha)) (cwi_pst_errno CWI a Ha)). }
  (* the ledger after the free (S1Ledger.prh_ledger_kept_aview): the statics by KP5; Lam's heads lie in entry blocks,
     apart from the scratch, so the runtime row's block clause keeps their 8 bytes; Lam's blocks stay live (the entry's
     blocks are left); Hp is the entry's *)
  assert (HL5 : prh_ledger B ly5 S5 Hp4 W5 mem5 (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D) (cw_most D) 0).
  { apply (prh_ledger_kept_aview B ly4 S4 Hp4 W4 mem4 ly5 S5 Hp4 W5 mem5 _ _ _ _ _ _ _ HL).
    - exact KP5.
    - intros a kk i Hak Hi. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL0 Hak) as (Hk0 & Hab & _).
      assert (Ne : (a - cf_head, kk + cf_head) <> (scr, cw_size D + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hab).
      pose proof (wa2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR4 (Hinc4 _ Hab) Hscrb Ne) as Dj.
      assert (Hkk : 0 <= kk + cf_head) by lia. pose proof (wa2_req_ge _ Hkk).
      rewrite (wa2_req (cw_size D + 1)) in Dj by lia.
      assert (Hch : cf_head = 16) by reflexivity.
      apply (K2 (a - cf_head) (kk + cf_head) i (Hinc4 _ Hab)); [lia|]. rewrite (wa2_req (cw_size D + 1)) by lia. lia.
    - intros a kk Hak _. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL0 Hak) as (_ & Hab & _).
      rewrite Eab0. exact Hab.
    - apply Permutation_refl. }
  assert (KS5 : forall a, sp0 - 32 <= a < sp0 -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) mem4 a).
  { intros a Ha. apply K1; [lia | unfold ASTACK; lia]. }
  assert (HSV5 : caw_saved D W5 mem5).
  { unfold caw_saved, cw_sp0 in HSV |- *. change (spZ (cw_regs D)) with sp0 in HSV |- *. destruct HSV as (V1 & V2 & V3 & V4).
    split; [|split; [|split]]; (eapply wa2_vm_eq; [|eassumption]); intros x Hx; apply KS5; change (Z.of_nat 8) with 8 in Hx;
      lia. }
  assert (Hk4 : caw_kregs D (ms_regs ms)).
  { intros r1 Hr1. rewrite (HKP r1 ltac:(cbn [In] in Hr1 |- *; tauto)). exact (Hkr r1 Hr1). }
  pose proof (wa2_kregs_pres D (ms_regs ms) regs5 Hk4 HP5) as Hk5.
  assert (R85 : getr regs5 8 = w64 (cw_rc D)).
  { rewrite (wa2_pres (ms_regs ms) regs5 8%bv ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia) HP5).
    rewrite (HKP 8%bv ltac:(cbn; tauto)). exact R8. }
  assert (Hsp5 : spZ regs5 = sp0 - 80).
  { unfold spZ. rewrite (wa2_pres (ms_regs ms) regs5 2%bv ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia) HP5).
    exact Hspm. }
  (* ---- +108 .. +252: j, li s2, -1 ---- *)
  assert (HS5 : st_ok_pi (fx := fy) SEGS VAL (caw_Ee regs5 sp0 [])
    (mkSS (CAW_OFF + 108) caw_sr80 [caw_fregion_e [] 0 0] None wa2_facts)
    (restrict (w_H W5) (@YK11.mkst fy regs5 (Z_to_bv 64 (BASE + (CAW_OFF + 108))) mem5 (YK11.seg_rom SEGS)))).
  { apply (@caw_st_ok_e fy rc PA).
    - vm_compute. reflexivity.
    - cbn. lia.
    - unfold CAW_FRAME. lia.
    - unfold CAW_FRAME. lia.
    - intros o Ho. lia.
    - exact I.
    - unfold facts_ok, wa2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
      split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite caw_Ee_sp, unsigned_lit_small by lia.
      change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia]. }
  set (E5 := caw_Ee regs5 sp0 []) in HS5.
  assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; unfold caw_Ee; apply Eimg_env).
  assert (SHOK5 : sh_ok SEGS (SOff 32 0) [] E5 (mrestrict (w_H W5) mem5)) by (unfold sh_ok; apply Forall_nil).
  assert (E25 : ew E5 2 = Z_to_bv 64 sp0) by (subst E5; apply caw_Ee_sp).
  assert (HAE5 : env_agree 32 (Ereg (regupd regs5 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: []))) E5)
    by (subst E5; apply caw_Ee_agree).
  clear HF HFr HG.
  pose (RUNTOR := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_caw_A) (PI := PA) B prh_pst
    ARX LAWS P PLAW RW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  paj_run_to_tok_x_invR RUNTOR HS5 HJ5 SHOK5 HPM5 wa2_Bspan (CAW_OFF + CAW_PC_OOM).
  { intros a (r0 & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. lia. }
  lazymatch type of HS5 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (ms6 := m) in * end.
  assert (Emem6 : ms_mem ms6 = mem5).
  { apply functional_extensionality. intros x. apply HF. intros (r0 & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. lia. }
  pose proof (regs_kept_of_st_ok_pi E5 _ _ _ _ [3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS5 HAE5
    ltac:(vm_compute; reflexivity)) as HKP6.
  cbn [ms_regs restrict] in HKP6.
  assert (HKQ : forall r1 : bv 5, In r1 [3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms6) r1 = getr regs5 r1).
  { intros r1 Hr. rewrite (HKP6 r1 Hr). apply caw_getr_upd_other. intros ->. cbn [In] in Hr.
    repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
  assert (Hsp6 : spZ (ms_regs ms6) = sp0 - CAW_FRAME).
  { apply (caw_sp_st (fz := fy) (w_H W5) E5 _ ms6 sp0 HS5); [vm_compute; reflexivity | exact E25 | unfold CAW_FRAME; lia]. }
  assert (G18 : getr (ms_regs ms6) 18 = w64 (-1)).
  { rewrite (st_ok_pi_restrict_reg (w_H W5) E5 _ ms6 18%bv HS5). wa2_sv. cbn [sv_denot]. apply bv_eq. unfold w64.
    rewrite !Z_to_bv_unsigned. reflexivity. }
  pmkst HS5. rewrite Emem6 in HJ5, HPM5 |- *.
  replace (BASE + 2772) with (caw_pc CAW_PC_OOM) by (unfold caw_pc, CAW_PC_OOM; rewrite CAW_OFF_val; lia).
  apply (KOOM fy ly5 S5 Hp4 W5 (ms_regs ms6) mem5 _ (k4 + (st_nev S5 - st_nev S4)) (-1)); [|exact HPM5].
  refine (conj _ (conj HRP5 (conj _ (conj G18 (conj _ (conj Eab0 HL5)))))).
  + refine (conj Hpre (conj Hcnt (conj Hfl (conj HJ5 (conj _ (conj Hsp6 (conj HSV5 (conj EHp (conj HRL5 _))))))))).
    * intros r1 Hr1. rewrite (HKQ r1 ltac:(cbn [In] in Hr1 |- *; tauto)). exact (Hk5 r1 Hr1).
    * exact (wa2_rodR RW D ly5 S5 Hp4 W5 mem5 _ _ Hpre HJ5).
  + rewrite (HKQ 8%bv ltac:(cbn; tauto)). exact R85.
  + left. split; [exact (wa2_read_none _ EV) | reflexivity].
Qed.

Lemma caw_wa2_holds : caw_seg_WA2R (fx := fx) B SK CTX0 P RW.
Proof.
intros Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr HX KR KOOM HP3.
apply wa2_lift.
destruct HX as (HC & HRP & R10 & R8 & R9 & R18 & V72 & V64 & V56 & HSCR & HL & HHB3).
unfold caw_ledger in HL.
pose proof HC as (Hpre & Hcnt & Hfl & HJ & Hkr & Hsp & HSV & EHp & HRL & HROD).
pose proof (caw_pre_fpre (fx := fx) B CTX0 D Hpre) as (HAF & HROD0 & Hshi64 & Hraceil & Hfrm0).
pose proof (caw_pre_mn (fx := fx) B CTX0 D Hpre) as HMN0. pose proof (caw_pre_univ (fx := fx) B CTX0 D Hpre) as HUNIV.
pose proof (caw_pre_r10 (fx := fx) B CTX0 D Hpre) as H10. pose proof (caw_pre_r11 (fx := fx) B CTX0 D Hpre) as H11.
pose proof (caw_pre_r12 (fx := fx) B CTX0 D Hpre) as H12. pose proof (caw_pre_r13 (fx := fx) B CTX0 D Hpre) as H13.
pose proof (caw_pre_rc (fx := fx) B CTX0 D Hpre) as Hrc. pose proof (caw_pre_doc (fx := fx) B CTX0 D Hpre) as Hdoc.
pose proof (caw_pre_size (fx := fx) B CTX0 D Hpre) as Hsz. pose proof (caw_pre_data0 (fx := fx) B CTX0 D Hpre) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B CTX0 D Hpre) as Hd62. pose proof (caw_pre_src (fx := fx) B CTX0 D Hpre) as HSRC.
pose proof (caw_pre_inblk (fx := fx) B CTX0 D Hpre) as HINB. pose proof (caw_pre_case (fx := fx) B CTX0 D Hpre) as HCASE.
pose proof (caw_pre_tree (fx := fx) B CTX0 D Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B CTX0 D Hpre) as HL0.
pose proof (caw_pre_ran (fx := fx) B CTX0 D Hpre) as Hran0. pose proof (caw_pre_live (fx := fx) B CTX0 D Hpre) as HLIVE.
pose proof (caw_pre_max (fx := fx) B CTX0 D Hpre) as HMAX. pose proof (caw_pre_frames (fx := fx) B CTX0 D Hpre) as HFR.
pose proof (caw_pre_room (fx := fx) B CTX0 D Hpre) as HRL0. pose proof (caw_pre_frm0 (fx := fx) B CTX0 D Hpre) as Hfrm.
pose proof HAF as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK_check_as_written = 25712) by (vm_compute; reflexivity).
unfold caw_J in HJ. unfold CAW_FRAME in Hsp. unfold cw_sp0 in *.
set (sp0 := spZ (cw_regs D)) in *.
pose proof YM05.alloc_ceiling_val as HCEIL.
assert (Hsp0 : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
set (vals := @nil Z).
assert (HS : st_ok_pi SEGS VAL (caw_Ee regs3 sp0 vals)
  (mkSS (CAW_OFF + CAW_PC_X) caw_sr80 [caw_fregion_e [] (-48) (-32)] None wa2_facts)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (CAW_OFF + CAW_PC_X))) mem3 (YK11.seg_rom SEGS)))).
{ apply (@caw_st_ok_e fy rc PA).
  - vm_compute. reflexivity.
  - cbn. lia.
  - unfold CAW_FRAME. lia.
  - unfold CAW_FRAME. lia.
  - intros o Ho. apply (apresent_writable SEGS).
    pose proof (ajx_pres HJ) as Jpres.
    apply Jpres. rewrite HSTK. lia.
  - exact I.
  - unfold facts_ok, wa2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite caw_Ee_sp, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia]. }
set (E := caw_Ee regs3 sp0 vals) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold caw_Ee; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply caw_Ee_sp).
pose (RUN := paj_run_x_inv (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_caw_A) (PI := PA) B prh_pst (ARcfx B) LAWS P PLAW).
unfold caw_cfg, caw_pc. replace (BASE + CAW_OFF + CAW_PC_X) with (BASE + (CAW_OFF + CAW_PC_X)) by lia.
paj_run_tok_x_inv RUN HS HJ SHOK HP3 wa2_Bspan.
{ intros a (r & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. rewrite E2, unsigned_lit_small in Hr by lia.
  left. rewrite HSTK. lia. }
(* ---- the call state: pc = ex_value, a0 = q = sp0 - 72, a1 = v, ra = +96, the scratch and differs stored ---- *)
set (memc := ms_mem ms) in *.
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pose proof (cwi_base CWI) as CWB.
assert (HBASE : BASE = 529888) by (rewrite CWB; vm_compute; reflexivity).
assert (HAE : env_agree 32 (Ereg (regupd regs3 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E)
  by (subst E; apply caw_Ee_agree).
pose proof (regs_kept_of_st_ok SEGS E _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HKP0.
cbn [ms_regs restrict] in HKP0.
assert (HKP : forall r : bv 5, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs3 r).
{ intros r Hr. rewrite (HKP0 r Hr). apply caw_getr_upd_other. intros ->. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
assert (EregE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv -> ew E n = getr regs3 r)
  by (intros n r Hn Hr; subst E; exact (caw_Ee_reg regs3 _ vals n r Hn Hr)).
assert (Hspc : spZ (ms_regs ms) = sp0 - 80).
{ unfold spZ. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms 2%bv HS). wa2_sv.
  rewrite (wa2_denot_off E 2 (-80) sp0 E2) by lia. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (G10 : getr (ms_regs ms) 10 = w64 (sp0 - 72)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms 10%bv HS). wa2_sv.
  rewrite (wa2_denot_off E 2 (-72) sp0 E2) by lia. f_equal. }
assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CAW_OFF + 96))).
{ rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms 1%bv HS). wa2_sv. exact (codeptr_val E 2616 HEI). }
assert (U8 : U E (SOff 8 0) = cw_rc D mod 2 ^ 64).
{ rewrite U_SOff, (EregE 8%nat 8%bv eq_refl ltac:(discriminate)), R8. unfold w64. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, zcanon, M64. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
  reflexivity. }
assert (U9 : U E (SOff 9 0) = cw_doc D).
{ rewrite U_SOff, (EregE 9%nat 9%bv eq_refl ltac:(discriminate)), R9. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.add_0_r. unfold zcanon, M64; apply Z.mod_small. lia. }
set (v := if cw_rc D =? 0 then cw_doc D else 0).
assert (G11 : getr (ms_regs ms) 11 = w64 v).
{ rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms 11%bv HS). wa2_sv. apply bv_eq. unfold w64.
  rewrite unsigned_lit_small by (unfold v; destruct (cw_rc D =? 0); lia).
  exact (wa2_v_val E (cw_rc D) (cw_doc D) U8 Hrc U9 Hdoc). }
(* the written cells, off the symbolic state's frame region *)
pose proof (st_ok_region_nth SEGS E _ _ 0 _ HS eq_refl) as Hreg. cbn [ms_mem restrict] in Hreg.
pose proof (ajx_ar HJ) as HAR3c. pose proof (ajx_ly HJ) as Hly3.
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & Eslo3 & Eshi3 & _).
pose proof HSCR as (Hs4096 & Eab3).
assert (Hinc3 : incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly3 S3))
  by (intros x Hx; rewrite Eab3; apply in_or_app; left; exact Hx).
assert (Hscrb : In (scr, cw_size D + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
assert (Hsz0 : 0 <= cw_size D) by (unfold cw_size; lia).
pose proof cf_head_nonneg as CH0.
destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR3c Hscrb) as (_ & _ & Hsce & Happs & Hprs & _).
rewrite wa2_req in Hsce, Happs, Hprs by lia.
assert (Vscr : val_mem SEGS (rdW W3 memc) (sp0 + -48) 8 scr).
{ apply (field_of_region SEGS E _ 2 sp0 _ _ _ _ _ (-48) 8 (SOff 10 0) scr Hreg).
  - rewrite E2. apply unsigned_lit_small. lia.
  - cbn. right. left. reflexivity.
  - rewrite (wa2_denot_off E 10 0 scr); [unfold w64; f_equal; lia | | lia | lia].
    rewrite (EregE 10%nat 10%bv eq_refl ltac:(discriminate)), R10. reflexivity.
  - change (8 * Z.of_N 8) with 64. lia.
  - change (Z.of_N 8) with 8. lia. }
assert (Vdl0 : val_mem SEGS (rdW W3 memc) (sp0 + -40) 8 0).
{ apply (field_of_region SEGS E _ 2 sp0 _ _ _ _ _ (-40) 8 (SLit 0) 0 Hreg).
  - rewrite E2. apply unsigned_lit_small. lia.
  - cbn. left. reflexivity.
  - reflexivity.
  - change (8 * Z.of_N 8) with 64. lia.
  - change (Z.of_N 8) with 8. lia. }
(* every other byte is the cut's *)
assert (NWR : forall a, ~ (sp0 - 48 <= a < sp0 - 32) ->
  ~ in_wrange E (ss_mem (mkSS (CAW_OFF + CAW_PC_X) caw_sr80 [caw_fregion_e [] (-48) (-32)] None wa2_facts)) a).
{ intros a Hn (r & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi caw_fregion_e base_val] in Hr. rewrite E2, unsigned_lit_small in Hr by lia. lia. }
assert (VMc : forall a, ~ (sp0 - 48 <= a < sp0 - 32) -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W3) memc a = aview SEGS (w_H W3) mem3 a).
{ intros a Hn Ha. exact (wa2_frame_view W3 E _ mem3 memc a HFr (NWR a Hn) Ha). }
(* the prh_pst bytes are low image bytes (pa_segs_low), off the frame cells the hand steps write *)
assert (KPc : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W3) memc a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (pa_segs_low a (cwi_pst_img CWI a Ha)). unfold kLowMemEnd in *. apply VMc; lia. }
(* the ledger at the call state (S1Ledger.prh_ledger_kept_aview): the statics by KPc, Lam's heads lie in entry blocks
   above the ceiling, off the frame cells; the state's blocks and Hp unchanged *)
assert (HLc : prh_ledger B ly3 S3 Hp3 W3 memc (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D) (cw_most D) 0).
{ apply (prh_ledger_kept_aview B ly3 S3 Hp3 W3 mem3 ly3 S3 Hp3 W3 memc _ _ _ _ _ _ _ HL).
  - exact KPc.
  - intros a kk i Hak Hi. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL0 Hak) as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR3c (Hinc3 _ Hab)) as (_ & H4 & Hce & _).
    assert (Hkk : 0 <= kk + cf_head) by lia. pose proof (wa2_req_ge _ Hkk). apply VMc; lia.
  - intros a kk _ Hin. exact Hin.
  - apply Permutation_refl. }
pose proof (wa2_scr_not_hp D ly3 S3 Hp3 W3 memc mdc scr Hpre HAR3c HSCR) as Hnhp.
pose proof (wa2_scr_new D ly3 S3 Hp3 W3 memc mdc scr HAR3c HSCR) as Hnew.
assert (Hdocnz : cw_rc D = 0 -> cw_doc D <> 0).
{ intros Hrc0. destruct (HTREE Hrc0) as (_ & _ & _ & (_ & (cid & pos & Hfin & Hf1 & _) & _)).
  destruct (alx_frames SEGS B ARX LAWS _ _ _ _ _ _ cid pos HAR0 Hfin) as (_ & Happ & _). unfold in_app in Happ. lia. }
assert (HSTK1 : STK_ex_value DOC_D = 25632) by (vm_compute; reflexivity).
assert (HDOC : Z.of_nat DOC_D = 33) by (vm_compute; reflexivity).
pose proof YM05.alloc_ceiling_val as HCV.
assert (Hs0b : s0Z (ms_regs ms) < YM05.alloc_ceiling \/ ly_top ly3 - 16 <= s0Z (ms_regs ms)).
{ apply (wa2_s0_bound _ ly3 (cw_rc D)); [rewrite (HKP 8%bv ltac:(cbn; tauto)); exact R8 | exact Hrc | lia]. }
(* ---- the call ---- *)
eapply SRr_bind.
{ eapply (@aj_call_xWF_sp fy rc SK SEGS B prh_pst ARX cf_head LAWS (@pa_segs_low _ _ PA) W3 E _ ms
    STK_check_as_written sp0 [] (cw_ly D) (cw_S D) (cw_Hp D) (cw_W D) (cw_mem D) (cw_md D) [] ly3 S3 Hp3 mdc k
    (STK_ex_value DOC_D) 48 _ (-80) (Z_to_bv 64 (BASE + (CAW_OFF + 96))) [] _ HS eq_refl HJ).
  - rewrite Hspc. lia.
  - reflexivity.
  - lia.
  - rewrite HSTK1. lia.
  - rewrite HSTK1, HSTK. lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite (HKP 3%bv ltac:(cbn; tauto)), (Hkr 3%bv ltac:(cbn; tauto)). exact Hgp0.
  - rewrite (HKP 4%bv ltac:(cbn; tauto)), (Hkr 4%bv ltac:(cbn; tauto)). exact Htp0.
  - exact G1.
  - apply (ret_ok_codeptr_v (PI := PA)); rewrite CAW_OFF_val; [lia | reflexivity].
  - rewrite unsigned_lit_small by (rewrite HBASE, CAW_OFF_val; lia). rewrite HBASE, CAW_OFF_val. lia.
  - apply wa2_achain0. exact Hs0b.
  - intros HPRE HWIN.
    eapply (HEXV fy ly3 S3 Hp3 W3 (ms_regs ms) memc mdc [] (sp0 - 72) v (cw_data D) 0 0 0 scr 48 (cw_x D) (cw_t D)
      (cw_D D) (cw_Lam D) (cw_peak D) (cw_cnt D) (cw_fail D) (cw_ran D) (cw_most D) 0).
    all: try change (Z.of_nat (length (cw_x D))) with (cw_size D).
    + (* fpre at the call's float state fy: FRM0-ENTRY's frm_zero (fp_csr fy) is the cut's caw_fl fy *)
      refine (conj HPRE (conj (wa2_rod D ly3 S3 Hp3 W3 memc mdc k Hpre HJ) (conj _ (conj _ (proj1 Hfl))))).
      * rewrite Hspc. lia.
      * unfold raZ. rewrite G1. exact wa2_ret_slot_ceil.
    + exact (PMN memc HP3).
    + exact (proj1 Hfl).
    + pose proof (ajx_frs HJ) as Hfrs. rewrite Hfrs. cbn [app].
      pose proof (wa2_count_le 1 (frames (cw_S D))) as Hc.
      assert (Hcap : ck_FRAMES_CAP - FR_check_as_written = 30) by (vm_compute; reflexivity).
      assert (Hff : fs_frames 1 = 8192) by (vm_compute; reflexivity).
      rewrite Hff. rewrite Nat2Z.inj_succ. lia.
    + exact G10.
    + exact G11.
    + split; [|split; [|split; [|split]]].
      * rewrite Z.add_0_r. apply (wa2_vm_eq W3 W3 mem3 memc); [|exact V72].
        intros x Hx. apply VMc; [|split]; lia.
      * replace (sp0 - 72 + 8) with (sp0 - 64) by lia. apply (wa2_vm_eq W3 W3 mem3 memc); [|exact V64].
        intros x Hx. apply VMc; [|split]; lia.
      * replace (sp0 - 72 + 16) with (sp0 - 56) by lia. apply wa2_vm8_4. apply (wa2_vm_eq W3 W3 mem3 memc); [|exact V56].
        intros x Hx. apply VMc; [|split]; lia.
      * replace (sp0 - 72 + 24) with (sp0 + -48) by lia. exact Vscr.
      * replace (sp0 - 72 + 32) with (sp0 + -40) by lia. exact (wa2_vm8_4 _ _ Vdl0).
    + pose proof (Z.div_mod sp0 16 ltac:(lia)) as Dm. rewrite Hal16 in Dm.
      replace (sp0 - 72) with ((2 * (sp0 / 16) - 9) * 8) by lia. apply Z.mod_mul. lia.
    + intros rd' _. apply wa2_achain0. exact Hs0b.
    + rewrite Hspc. lia.
    + rewrite Hspc. lia.
    + exact HWIN.
    + exact (wa2_src_rd_J D ly3 S3 Hp3 W3 memc mdc k _ _ _ _ _ _ _ Hpre HJ Hinc3 EHp HLc).
    + intros Hl. destruct (HINB Hl) as (b & m & Hin & H1 & H2 & H3). exists b, m.
      split; [exact (Hinc3 _ Hin)|]. split; [exact H1|]. split; [exact H2|]. rewrite EHp. exact H3.
    + exact Hsz.
    + lia.
    + lia.
    + rewrite HDOC. lia.
    + left. reflexivity.
    + split; [lia|]. split; [lia|]. split.
      * unfold amem_range. unfold in_app in Happs. destruct Happs as (_ & [Hlo | (Hhi1 & Hhi2)]); [left | right];
          unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia.
      * split.
        -- intros a Ha. destruct (Hprs a ltac:(lia)) as (Hpa & Hno).
           split; [exact (apresent_writable SEGS _ _ _ Hpa)|]. split; [exact Hno|]. rewrite Hspc, HSTK1. lia.
        -- assert (Hib : prhex_inblk B ly3 S3 Hp3 scr (cw_size D + 1)).
           { exists scr, (cw_size D + 1). split; [exact Hscrb|]. split; [lia|]. split; [lia|].
             intros Hi. exfalso. apply Hnhp. rewrite <- EHp. exact Hi. }
           destruct (wa2_sh_blk ly3 S3 Hp3 W3 memc mdc _ _ _ _ _ _ _ scr (cw_size D + 1) HAR3c HLc Hib ltac:(lia)) as [SR SH].
           split; [exact SR | intros _; exact SH].
    + exists scr, (cw_size D + 1). split; [exact Hscrb|]. split; [lia|]. split; [lia|].
      intros Hi. exfalso. apply Hnhp. rewrite <- EHp. exact Hi.
    + destruct (Z.eq_dec (cw_size D) 0) as [H0|H0]; [lia|].
      destruct (HINB ltac:(lia)) as (b & m & Hin & H1 & H2 & H3).
      assert (Ne : (b, m) <> (scr, cw_size D + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hin).
      pose proof (wa2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR3c (Hinc3 _ Hin) Hscrb Ne) as Dj.
      rewrite (wa2_req (cw_size D + 1)) in Dj by lia.
      assert (Hm0 : 0 <= m) by lia. pose proof (wa2_req_ge m Hm0). lia.
    + left. lia.
    + unfold v. destruct (Z.eqb_spec (cw_rc D) 0) as [Hrc0 | Hrcn]; [right | left; reflexivity].
      split; [exact (wa2_tree_J D ly3 S3 Hp3 W3 (ms_regs ms) memc mdc k Hpre HJ Hinc3 Hrc0)|]. split.
      * destruct (HTREE Hrc0) as (_ & HDL & _). rewrite Forall_forall. intros [a kk] Hin. cbn [fst].
        destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HL0 (HDL _ Hin)) as (Hk0 & Hab & _).
        destruct (alx_blocks SEGS B ARX LAWS _ _ _ _ _ _ _ _ HAR0 Hab) as (_ & H4 & _). lia.
      * intros z Hz. destruct (wa2_foot D ly3 S3 Hp3 W3 memc mdc k scr Hpre HJ HSCR Hrc0 z Hz) as (Hzc & Hzs & Hze).
        split; [lia|]. split; [lia|]. split; [rewrite Hspc, HSTK1; lia | exact Hze].
    + exact HLc.
  - intros a Ha. rewrite !inFP_cons in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
    + right; left. exists scr, (cw_size D + 1). split; [exact Hscrb|]. split; [exact Hnew|].
      rewrite wa2_req by lia. unfold cw_size in *. lia.
    + right; right; right. rewrite HSTK. lia.
    + right; right; right. rewrite HSTK. lia.
    + right; right; right. rewrite HSTK. lia.
    + exfalso. exact (inFP_nil a Ha). }
(* ---- after the call: hand over at +96 ---- *)
cbv beta. intros W4 c4 Hwle4 (fy' & ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & -> & HFZ & HFK & HJ4 & HJ1 & HX & HPres & HK).
destruct HK as (HQ & HMN).
(* the ledger after ex_value at most and own = 0 is its text's post (HL4); the hand-over below carries it to +96 *)
destruct HQ as (HRLk & HHU & HRPk & r & p' & dep' & dl' & H10r & HCur & Hdl' & EHp4 & Eab4 & HL4 & HM).
assert (HPM4 : P mem4) by exact (PCALL memc mem4 HMN HP3).
assert (KS : forall a, sp0 - 32 <= a < sp0 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (ajx_hi HJ1) as G1h.
  rewrite (G1h a); [apply VMc; lia | lia | rewrite HSTK1; lia]. }
assert (HSV4 : caw_saved D W4 mem4).
{ unfold caw_saved, cw_sp0 in HSV |- *. change (spZ (cw_regs D)) with sp0 in HSV |- *. destruct HSV as (V1 & V2 & V3 & V4).
  split; [|split; [|split]]; (eapply wa2_vm_eq; [|eassumption]); intros x Hx; apply KS; change (Z.of_nat 8) with 8 in Hx; lia. }
destruct HCur as (C1 & C2 & C3 & C4 & C5).
replace (BASE + (CAW_OFF + 96)) with (caw_pc 96) by (unfold caw_pc; lia).
apply SRr_ret. cbv beta.
apply (wa2_post96 Q D fy' ly4 S4 Hp4 W4 regs4 mem4 md4 (k + k1) scr r p' dl').
- unfold caw_carry. refine (conj Hpre (conj Hcnt (conj _ (conj _ (conj _ (conj _ (conj HSV4 (conj _ (conj _ _))))))))).
  + split; [exact HFZ | exact (wa2_fregs_trans fx fy fy' (proj2 Hfl) HFK)].
  + exact HJ4.
  + apply (wa2_kregs_pres D (ms_regs ms) regs4); [|exact HPres]. intros r0 Hr0.
    rewrite (HKP r0 ltac:(cbn [In] in Hr0 |- *; tauto)). exact (Hkr r0 Hr0).
  + unfold spZ. rewrite (wa2_pres (ms_regs ms) regs4 2%bv ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia) HPres).
    fold (spZ (ms_regs ms)). rewrite Hspc. unfold CAW_FRAME, cw_sp0. change (spZ (cw_regs D)) with sp0. lia.
  + rewrite EHp4. exact EHp.
  + exact (HRLk HRL).
  + exact (wa2_rod D ly4 S4 Hp4 W4 mem4 md4 (k + k1) Hpre HJ4).
- (* the progress fact at caw_ev1 D crosses ex_value: its post keeps every run position (the implication form) *)
  intros rsm rx ros ri rH0 rhist Hpos Hrun. destruct (HRP rsm rx ros ri rH0 rhist Hpos Hrun) as (h & Hh).
  exists h. exact (HRPk _ _ _ _ _ _ Hh).
- rewrite (wa2_pres _ _ 8%bv ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia) HPres).
  rewrite (HKP 8%bv ltac:(cbn; tauto)). exact R8.
- rewrite (wa2_pres _ _ 9%bv ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia) HPres).
  rewrite (HKP 9%bv ltac:(cbn; tauto)). exact R9.
- rewrite (wa2_pres _ _ 18%bv ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia) HPres).
  rewrite (HKP 18%bv ltac:(cbn; tauto)). exact R18.
- exact H10r.
- exact C1.
- change (cw_sp0 D) with sp0. replace (sp0 - 64) with (sp0 - 72 + 8) by lia. exact C2.
- change (cw_sp0 D) with sp0. replace (sp0 - 48) with (sp0 - 72 + 24) by lia. exact C4.
- change (cw_sp0 D) with sp0. replace (sp0 - 40) with (sp0 - 72 + 32) by lia. exact C5.
- exact Hdl'.
- split; [exact Hs4096 | rewrite Eab4; exact Eab3].
- exact HL4.
- (* the hull budget crosses ex_value: it uses nothing (its post's hull_used S3 S4 []) *)
  exact (PresetHullBudget.hull_budget_app S3 S4 [] [PresetReqAt.HFr (cw_size D + 1)] HHB3 HHU).
- change (skipn (Z.to_nat 0) (cw_x D)) with (cw_x D) in HM.
  destruct (prhex_V 0 (cw_x D)) as [[u rest]|] eqn:EV.
  + destruct HM as (Hr0 & Hp' & _ & Hdlu). split; [exact Hr0|]. split; [unfold cw_size; exact Hp'|].
    rewrite Hdlu. unfold v. split.
    * intros [H01 | (Hv & Htu)]; [lia|].
      destruct (Z.eqb_spec (cw_rc D) 0) as [Hz|Hz]; [exact (conj Hz Htu) | exfalso; exact (Hv eq_refl)].
    * intros (Hrc0 & Htu). right. rewrite (proj2 (Z.eqb_eq _ _) Hrc0). exact (conj (Hdocnz Hrc0) Htu).
  + destruct HM as (Hr0 & _). exact Hr0.
- exact KR.
- exact KOOM.
- exact HPM4.
Qed.
End s.

Print Assumptions caw_wa2_holds.
