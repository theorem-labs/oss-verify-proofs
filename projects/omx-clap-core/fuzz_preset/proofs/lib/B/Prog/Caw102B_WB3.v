(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Disp_word.v, with its module paths and module names changed; 116 of its 154 lines of code are new or changed and 465 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Caw102A_Kit.v, with its module names changed; 674 of its 759 lines of code are new or changed and 69 lines of the source are left out. *)
(* fuzz_preset, image B' (#102): check_as_written's segment WB3 (B' 0x82000 `addi a0, sp, 8` -> jal ex_ws 0x82004 ->
   the three loads -> jal __wrap_free 0x82014 -> beq s1, s2 0x82018 -> {0x82074 lw s2 -> 0x82020 = cut_oB,
   0x8201c = cut_oA}) from cut_ws, in the continuation form of Caw102B.v. Lane CawB102.CawB102WB3; re-proved on the
   caw_pst base by CawA102R.CawRWB3; re-proved on the decff67d721f ledger base by CawA102R.CawDWB3; re-fitted to the
   f97c re-keyed base by CawA102R.CawGWB3; re-fitted to the batch-prep base by CawA102R.KWB34 (now INT102-READY).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   BASE OF RECORD: the kit's cut, this row's lib/B/Prog/Caw102B.v (its
   statements, not edited here). The kit as the cut carries it, its texts by path:
   lib/A/PRH_FnCheck.v c40cf3fdcd2a (tcheck_as_written_specX :832-902), lib/A/PRH_Base.v (fpre :988-1010,
   its last conjunct frm_zero (fp_csr fx); prh_univ_closure :1203, one argument CTX0), lib/A/PRH_FnEx.v
   (tex_ws_specX :199-213 at `.. ran most own`); the P'' engine as the cut carries it: YCbqG.v (the journal
   read by ajx_*, ajournal_xw_fix1), YCbqGcallW.v fb6aa11676a2 (aj_call_xW_sp), YGcallMxmn.v 3c08bbab8292
   (aj_free_x_ct_m), YG01.v 845507e218b0 (admits_fix), YG0d.v 9c24275f4fa6 (ablocks); lib/A/Prog/S1Ledger.v
   8cf15eeb6311 (prh_ledger_kept_aview at most own); lib/Reusable/YGcfRoomLive.v (ccnt24, RL_free_step,
   room_live_room); lib/A/CfRoomLivePreset.v d0e5e47dcb02 (preset_rl_b24_ok: its closed batch-room conjunct at L24 +
   DRV + 1); lib/Spec/PresetRoomPosKeep.v (room_pos_keep_free); lib/Spec/PresetLiveBounds.v f78da450d5f6
   (L24, DRV); lib/Spec/PresetRoom.v 0b749d72634f (ccnt).
   WHAT CHANGED ON THIS BASE AND WHY (the previous fit: this file 1ddb9da0a6f5 on the P'' journal,
   in the P'' trial; the batch text's changes that reach WB3):
   - THE RUN-WORD LIST DW IS GONE (PRH_Base.v :1225 `prh_univ_closure CTX0`; Caw102B.v's record loses c_DW): the helper
     w3_trace drops its DW binder (STATEMENT CHANGE, helper only: `forall CTX0 ly regs, prh_univ_closure B CTX0 -> ..`;
     its proof reads the closure's first two clauses, as before), and caw_WB3 passes c_CTX0 C alone.
   - caw_pre IS READ BY NAME: caw_pre is the text's 27 premises now (the two room counts after room_live_cf, then the hull budget and HPOS; ck_frm0
     moved by four), so a positional destruct would mis-bind; caw_WB3 and w3_scr_not_hp take each premise by the base's
     projection (caw_pre_fpre, caw_pre_src, caw_pre_ledger, ...) under its old name.
   - THE ROOM COUNTS are entry premises of the text (:862-863), and caw_cnt C is their conjunction (Caw102B.v
     caw_pre_cnt, by conversion): caw_WB3 keeps its premise `caw_cnt C` after caw_pre, the top supplies caw_pre_cnt; no
     named argument CAW_CNT remains.
   STATEMENT CHANGE (part 3c, the free under the re-hide): caw_WB3 states the continuations' R forms at wle', the
   re-hide's world relation past the free (caw_K_oAR / caw_K_oBR in, caw_K_wsR out): the free is the keep-carrying
   rule under the re-hide, YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (its memnorm keep the last conjunct), so past it the
   run is at wle' (YC1fPx's R runner, w3_branchR for the branch); the run before the free is the wle one, lifted
   (w3_lift). The free's call memory QMm_cf: the room, the hull budget cut_ws carries (the free's state is cut_ws's,
   ex_ws keeps it; PresetHullPay.hull_ok_of_budget) and the reader form through YGcfAroBridge.arodata_ok_cf_of_P at
   the image's relro rows. THE OUTCOME (caw_dead in cut_end's r = 1 arm) does not reach WB3: neither exit
   of WB3 is cut_end.
   KEPT FROM THE EARLIER FITS: each cut carries THE PROGRESS FACT caw_prog C E S (for any run position i at the entry
   state whose next events are E, a position i + length E at S): cut_ws at caw_ev1 C = [HMal (size + 1)], cut_oA /
   cut_oB at caw_evs C = [HMal (size + 1); HFr (size + 1)]. __wrap_free steps the position: a run at caw_evs C =
   caw_ev1 C ++ [HFr (size + 1)] splits (caw_run_at_app), cut_ws's caw_prog at caw_ev1 gives the position i + 1 at the
   free's entry state S3, caw_run_at_nth reads the event HFr (size + 1) there, room_pos_keep_free moves it to S (i + 1)
   = i + 2 at the free's exit state; both exits take that caw_prog at caw_evs. The free's room_live_cf keep
   (RL_free_step) needs rl_b24_ok at S3: caw_cnt C gives ccnt24 (c_S C) <= L24 + DRV at entry, cut_ws's caw_scr gives
   ablocks at S3 = the entry's ++ [(scr, size + 1)], so ccnt24 grows by at most 1 (w3_ccnt24_app, the A' twin's
   caw_ccnt24_app), and rl_b24_ok (L24 + DRV + 1) S3 holds with preset_rl_b24_ok's closed batch-room conjunct.
   FRM0-ENTRY: the ex_ws call's callee fpre takes its last conjunct frm_zero (fp_csr fy) at the call's float state,
   cut_ws's caw_base first conjunct. Every cut ends in caw_ledger C .. own (cut_ws gives it at 0; both exits need it at
   0): across ex_ws by the text's post (tex_ws_specX gives the ledger at the same most own); across the scratch's
   __wrap_free by S1Ledger.prh_ledger_kept_aview at most own (each prh_pst byte, g_most's and g_own_ran_out's included,
   is an image byte off the owned statics and errno, kept by the runtime row's image clause, aj_free_x_ct_m_rh_keep's
   acall_kept, through Hpst_img / Hpst); the hand runs after the free are read-only (memory equal). The free's trace is
   a FIXED one of the universe (w3_trace), passed to the call rule's `admits` by admits_fix and dropped from the
   journal's wild budget by ajournal_xw_fix1R. Every base name in a statement here takes the entry state explicitly,
   (fx := fx).
   SECTION HYPOTHESES AND OWNERS (the relro rows are new with the free's QMm_cf): TEXWS (callee text, a Theorem Labs lane: PRH_FnEx.v
   tex_ws_specX); AFREE (the free row under the re-hide with the memnorm keep at the leaf,
   YGcfMallocComposeKeep.afree_realizes_cf_rh_keep); PAL, Hpst, Hpst_img, Hpst_rw, Hfree2, PAB (image
   facts of B', carried by the B' top Caw102B_Top.v with the same spelling and discharged at PI_prog_B: S1ImgB.v
   pst_in_img_B / pst_not_ro_B, pal_pst_ok, the generated pi_ret_caw_free2, PjGetB.v pgb_PAB; owner h-mani-a2's
   IMG_TOP_B, PAImg_prog.v); Hrelro_seg / Herrno_relro / Hrelro_top / Hrelro_eq / Hro_reads_nw (the cf layer's relro
   rows at the image, the cno B' base's cnbi_relro_* rows; at the image by lib/AU/CfAroPresetB.v relro_seg_preset_AU /
   errno_relro_preset_AU / relro_top_preset_AU / ro_reads_nw_preset_AU and the range equation by computation).
   Generic P, abstract. The ex_ws call by its text (tex_ws_specX, a TEXWS hypothesis at every float state) through
   YCbqGcallW.aj_call_xW_sp at the whole frame as window (o = -80, e1 = 80); the free of the scratch by the runtime
   row AFREE through YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (the free under the re-hide, with the memnorm keep); P across each
   call by srr_inv_call. The room after the free by YGcfRoomLive.RL_free_step at L24 + DRV + 1 (above); the run
   position after the free by PresetRoomPosKeep.room_pos_keep_free at the HFr event of the run (above). Structure: H2CawF.v
   (h-hpreset-7-walk-H2H5, old caw A: the free, the compare) and PjGetB.v (a K0 call, a fresh seat after it); the seat
   is Caw102A_Kit.v's (atom 2 = the entry sp, sp = SOff 2 (-80)) at B; the text's window home is PvB_A_Home.v's.
   Numerals: 8 / 40 / 48 / 64 / 72 (LENGTH: the struct ex cells off the entry sp, Caw102B.v's frame layout), 80
   (LENGTH: the frame, the ex_ws window), 136 / 144 / 160 / 164 / 168 (DERIVED: 4 * the slot inside the function:
   the cut, the two return sites, the two cuts after), 2364 / 2380 (DERIVED: AF_cawB + 144 / AF_cawB + 160, the two
   return sites as the engine prints them), 26800 / 16 / 16384 (DERIVED by computation: STK_check_as_written,
   STK_ex_ws, ASTACK), 32 / 33 (DERIVED: the engine's atom numbering), 2 ^ 46 / 2 ^ 47 (LENGTH: the entry sp's
   range), 1 (COUNT: the one block the scratch adds to the class-24 count; the one run event before the free). No
   ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
(* the free under the re-hide with the memnorm keep (part 3c took the keep out of the plain rules' posts) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetLiveBounds PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require H2CawPure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- a seat: the frame [sp0 - 80, sp0) below the ENTRY sp (atom 2 = sp0, sp the term SOff 2 (-80)), the words a
   run reads as atoms 33, 34, .. (atom 32 the shadow base), every other register its own atom (Caw102A_Kit.v's
   caw_fregion_e / caw_sr80 / caw_Ee, at image B). The journal from entry is at sp0, so the call rules' `ew E 2 = spw`,
   `bv_unsigned spw = sp0` hold of the seat as they do at the entry ---- *)
Fixpoint w3_fchunks (k : nat) (offs : list (Z * N)) : list YP09.chunk :=
  match offs with
  | [] => []
  | (o, w) :: r => YP09.mkChunk o (CVal w (SOff k 0)) :: w3_fchunks (S k) r
  end.
Definition w3_fregion (offs : list (Z * N)) (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (- CAWB_FRAME) 0 wlo whi (w3_fchunks 33 offs).
Definition w3_sr80 : list sv := sr_set sr_atoms 2%bv (SOff 2 (- CAWB_FRAME)).
Definition w3_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

Section bld. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGSz := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VALz := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation BASEz := (@pa_val _ B_prog_listing PA A_TEXT).
Fixpoint w3_vals_ok (m : word -> option byte) (sp : Z) (offs : list (Z * N)) (vals : list Z) : Prop :=
  match offs, vals with
  | [], [] => True
  | (o, w) :: r, v :: vs =>
      val_mem SEGSz m (sp + o) (N.to_nat w) v /\ 0 <= v < 2 ^ (8 * Z.of_N w) /\ Z.of_N w <= 8 /\
      w3_vals_ok m sp r vs
  | _, _ => False
  end.
Definition w3_E (regs : bvmap 5 word) (sp0 : Z) (vals : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))).
Lemma w3_fchunks_ok : forall E m sp offs vals k,
  (forall i, (i < length offs)%nat -> ew E (k + i) = Z_to_bv 64 (nth i vals 0)) ->
  w3_vals_ok m sp offs vals -> Forall (YP09.chunk_ok SEGSz E m sp) (w3_fchunks k offs).
Proof.
intros E m sp offs. induction offs as [|[o w] r IH]; intros vals k He Hv; [constructor|].
destruct vals as [|v vs]; [destruct Hv|]. destruct Hv as (Hm & Hr & Hw & Hv).
constructor.
- apply (chunk_ok_val SEGSz E m sp o w (SOff k 0) v); [| exact Hr | exact Hw | exact Hm].
  cbn [sv_denot]. specialize (He 0%nat ltac:(cbn; lia)). rewrite Nat.add_0_r in He. rewrite He.
  cbn [nth]. rewrite Z.add_0_r, unsigned_lit_small by (split; [lia|]; apply (Z.lt_le_trans _ _ _ (proj2 Hr)); apply Z.pow_le_mono_r; lia).
  reflexivity.
- apply (IH vs (S k)); [| exact Hv].
  intros i Hi. specialize (He (S i) ltac:(cbn; lia)). rewrite <- Nat.add_succ_comm in He. exact He.
Qed.
Lemma w3_getr_upd_other : forall regs (r r' : bv 5) w, r' <> r -> getr (regupd regs r w) r' = getr regs r'.
Proof.
intros regs r r' w Hne. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other by (intros Heq; apply Hne; symmetry; exact Heq). reflexivity.
Qed.
Lemma w3_getr_upd_same : forall regs (r : bv 5) w, bv_eqb r 0 = false -> getr (regupd regs r w) r = w.
Proof. intros regs r w H. unfold getr, regupd. rewrite H. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma w3_E_reg : forall regs sp0 vals n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv ->
  ew (w3_E regs sp0 vals) n = getr regs r.
Proof.
intros regs sp0 vals n r Hn Hr. pose proof (u5_range r) as Hu. unfold w3_E.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat _ _ n r Hn).
apply w3_getr_upd_other. exact Hr.
Qed.
Lemma w3_E_sp : forall regs sp0 vals, ew (w3_E regs sp0 vals) 2 = Z_to_bv 64 sp0.
Proof.
intros regs sp0 vals. unfold w3_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). apply w3_getr_upd_same. reflexivity.
Qed.
Lemma w3_E_val : forall regs sp0 vals i, (i < 200)%nat -> ew (w3_E regs sp0 vals) (33 + i) = Z_to_bv 64 (nth i vals 0).
Proof.
intros regs sp0 vals i Hi. unfold w3_E. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (33 + i)%nat with (32 + S i)%nat by lia. rewrite ew_Ereg_extra.
change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma w3_regs_ok : forall regs sp0 vals, spZ regs = sp0 - CAWB_FRAME -> CAWB_FRAME <= sp0 < 2 ^ 64 ->
  regs_ok (w3_E regs sp0 vals) w3_sr80 regs.
Proof.
intros regs sp0 vals Hsp Hsp0 r'.
pose proof (regs_ok_Eimg_Ereg (L := B_prog_listing) (PI := PA) (regupd regs 2%bv (Z_to_bv 64 sp0))
  (map (Z_to_bv 64) (SHADOW_OFF :: vals)) r') as H.
fold (w3_E regs sp0 vals) in H.
unfold w3_sr80, sr_set. change (bv_eqb 2%bv 0%bv) with false. cbv iota.
unfold getr, regupd, sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact H|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx 2%bv)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'.
  cbn [sv_denot]. rewrite w3_E_sp. unfold spZ in Hsp. unfold CAWB_FRAME in *.
  rewrite unsigned_lit_small by lia.
  unfold getr in Hsp. change (bv_eqb 2%bv 0%bv) with false in Hsp. cbv iota in Hsp.
  apply bv_eq. rewrite unsigned_lit_small by lia. lia.
- apply Nat.eqb_neq in Hi.
  unfold reg_get in *. rewrite bvmap_get_set_other in H by (intros Heq; apply Hi; rewrite Heq; reflexivity).
  exact H.
Qed.
Lemma w3_st_ok : forall (W : world SEGSz) regs mem pc sp0 offs vals wlo whi G,
  regions_wf [w3_fregion offs wlo whi] = true -> (length offs <= 100)%nat ->
  spZ regs = sp0 - CAWB_FRAME -> CAWB_FRAME <= sp0 < 2 ^ 64 ->
  (forall o, wlo <= o < whi -> writable_at SEGSz (mrestrict (w_H W) mem) (sp0 + o)) ->
  w3_vals_ok (mrestrict (w_H W) mem) sp0 offs vals ->
  facts_ok (w3_E regs sp0 vals) G ->
  st_ok_pi SEGSz VALz (w3_E regs sp0 vals) (mkSS pc w3_sr80 [w3_fregion offs wlo whi] None G)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASEz + pc)) mem (YK11.seg_rom SEGSz))).
Proof.
intros W regs mem pc sp0 offs vals wlo whi G Hwf Hlen Hsp Hsp0 Hwr Hvals HG.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact (w3_regs_ok regs sp0 vals Hsp Hsp0).
- exact Hwf.
- assert (Hb : base_val (w3_E regs sp0 vals) (Some 2%nat) = sp0)
    by (cbn [base_val]; rewrite w3_E_sp; apply unsigned_lit_small; unfold CAWB_FRAME in *; lia).
  constructor; [|constructor]. unfold region_ok, w3_fregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
  split; [unfold CAWB_FRAME in *; lia|]. split; [lia|]. split; [exact Hwr|].
  apply (w3_fchunks_ok _ _ _ offs vals 33); [| exact Hvals].
  intros i Hi. apply w3_E_val. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
Lemma w3_E_agree : forall regs sp0 vals,
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) (w3_E regs sp0 vals).
Proof. intros regs sp0 vals. unfold w3_E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma w3_facts_ok : forall regs sp0 vals, 2 ^ 46 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  facts_ok (w3_E regs sp0 vals) w3_facts.
Proof.
intros regs sp0 vals Hr Ha. unfold facts_ok, w3_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite w3_E_sp, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia.
Qed.
(* the registers a run leaves at their seat values: gp, tp, s0 and s3 .. s11 (atoms of the seat's register file) *)
Definition w3_kl : list (bv 5) := [3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma w3_regs_kept : forall E ss (ms : machine_state) regs sp0 vals,
  st_ok SEGSz E ss ms -> E = w3_E regs sp0 vals ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) w3_kl = true ->
  forall r, In r w3_kl -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs sp0 vals HS -> Hl r Hr.
rewrite (regs_kept_of_st_ok SEGSz _ ss ms (regupd regs 2%bv (Z_to_bv 64 sp0)) _ w3_kl HS (w3_E_agree regs sp0 vals) Hl r Hr).
apply w3_getr_upd_other. intros ->. cbn [In w3_kl] in Hr.
repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr.
Qed.
End bld.

(* ---- the live class-24 count after one new block: the entry's count plus at most 1 (the scratch's malloc adds one
   block to ablocks, which keeps every request size; YGcfRoomLive.ccnt24 counts the class-24 request sizes). The A'
   twin's caw_ccnt24_app (Caw102A_WA3.v at bef23d2b454f), statement and proof unchanged ---- *)
Lemma w3_ccnt24_app : forall (B : asyms) ly S ly' S' (x : Z * Z),
  ablocks B ly' S' = ablocks B ly S ++ [x] -> YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S + 1.
Proof.
intros B ly S ly' S' x E. apply (f_equal (map snd)) in E. unfold ablocks in E. rewrite map_app, !map_map in E.
change (map snd (blocks S') = map snd (blocks S) ++ [snd x]) in E.
unfold YGcfRoomLive.ccnt24, PresetRoom.ccnt. rewrite E, filter_app, length_app.
lazymatch goal with |- context [List.filter ?f [?y]] => cbn [List.filter]; destruct (f y); cbn [length]; lia end.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation STK := (STK_check_as_written (PI := prh_img_B)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Abbreviation LEDGER := (prh_ledger B).
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.

(* ---- Section hypotheses: the callee texts and the image facts this segment uses ---- *)
(* callee text: ex_ws (a Theorem Labs lane, PRH_FnEx.v tex_ws_specX), at every float state (the call is after ex_value's) *)
Hypothesis TEXWS : forall fz, tex_ws_specX (fx := fz) B ARcfx SK.
(* callee text: the free wrapper's runtime row under the re-hide, with the memnorm keep at the leaf
   (YGcfMallocComposeKeep.v), at every float state *)
Hypothesis AFREE : forall fz, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
(* image facts, discharged at PI_prog_B: the unit's image binding of B; alloc.c's statics are image bytes, not
   runtime-owned, not errno, not read-only (S1ImgB.v pst_in_img_B / pst_not_ro_B at PI_prog_B); the second free's
   return site is the generated pi_ret_caw_free2 (B' 0x82018); the image starts at YImgTop.IMG_LO_B, image B's own
   bound (YImgTop.v :22; a B file never cites image A's IMG_LO) (PjGetB.v pgb_PAB) *)
Hypothesis PAL : PALib B.
Hypothesis Hpst : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis Hpst_img : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
Hypothesis Hpst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
Hypothesis Hfree2 : BASE + (AF_cawB + 160) = pi_ret_caw_free2.
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO_B.
(* the cf layer's relro rows at the image (what arodata_ok_cf, the free's call memory premise, asks; discharged at the
   image as the image facts above are, lib/AU/CfAroPresetB.v) *)
Hypothesis Hrelro_seg : YG0ncf.relro_seg_t SEGS.
Hypothesis Herrno_relro : YG0ncf.errno_relro_t B.
Hypothesis Hrelro_top : cf_relro_hi <= 2 ^ 64.
Hypothesis Hrelro_eq : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA.
Hypothesis Hro_reads_nw : YGcfAroBridge.ro_reads_nw_t SEGS.
(* the world relation past a free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* an SRr run whose post is an SRrG fact at RW is an SRrG run at RW (wle is inside RW) *)
Lemma w3_lift : forall W c (Q : world SEGS -> config -> Prop),
  SRr SEGS W c (fun W' c' => YA0nH.SRrG SEGS RW W' c' Q) -> YA0nH.SRrG SEGS RW W c Q.
Proof.
intros W c Q H.
apply (YA0nH.SRrG_bind SEGS RW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W c _ Q
  (YA0nH.SRr_SRrG SEGS RW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) W c _ H)).
intros W' c' _ H'. exact H'.
Qed.
(* YC1fP.paj_branch over any world relation R (a branch takes no step: the case split on its condition) *)
Lemma w3_branchR : forall (fz : YK11.FPState) (R : world SEGS -> world SEGS -> Prop) W E ss ms md Q c a b,
  st_ok_pi (fx := fz) SEGS VAL E ss (restrict (w_H W) ms) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = true ->
   st_ok_pi (fx := fz) SEGS VAL E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG SEGS R W (mkCfg ms md) Q) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = false ->
   st_ok_pi (fx := fz) SEGS VAL E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG SEGS R W (mkCfg ms md) Q) ->
  YA0nH.SRrG SEGS R W (mkCfg ms md) Q.
Proof.
intros fz R W E ss ms md Q c a b HS HT HF.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply HT; [reflexivity|]. pose proof (st_ok_add_cond SEGS E _ _ c a b HS Hb) as H. destruct ss; exact H.
- apply HF; [reflexivity|]. pose proof (st_ok_add_cond_neg SEGS E _ _ c a b HS Hb) as H. destruct ss; exact H.
Qed.

(* a return site of the walk is a text address: 4096 <= it < 2 ^ 64, below the ceiling *)
Lemma w3_ret : forall kk, 0 <= kk < 2 ^ 40 ->
  match plookup (@pl_tpi _ PL_caw_B) kk with Some _ => true | None => false end = true ->
  4096 <= BASE + kk /\ BASE + kk < YM05.alloc_ceiling /\ 0 <= BASE + kk < 2 ^ 64.
Proof.
intros kk Hk Hl. pose proof (pa_base_lo (PL := PL_caw_B) (PI := PA)) as HBLO. rewrite PAB in HBLO. unfold IMG_LO_B in HBLO.
pose proof (@pa_B_ok _ _ PA) as HB.
pose proof (pa_slot_lt_ceil_b (PL := PL_caw_B) (PI := PA) kk Hk Hl) as HC. lia.
Qed.

(* a callee-saved register across a call *)
Lemma w3_pres_r : forall regs regs' (r : bv 5), aregs_preserved regs regs' ->
  In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hr. assert (Hc : acallee_saved (bv_unsigned r)) by (unfold acallee_saved; cbn [In] in Hr; lia).
pose proof (H _ Hc) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.
Lemma w3_pres_kl : forall regs regs' r, aregs_preserved regs regs' -> In r w3_kl -> getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hr. apply w3_pres_r; [exact H|]. cbn [In w3_kl] in Hr.
repeat (destruct Hr as [<- | Hr]; [vm_compute; repeat (first [left; reflexivity | right]) |]). destruct Hr.
Qed.

(* s0 holds rc (an int, sign-extended): the empty chain *)
Lemma w3_achain : forall ly rd sp (regs : bvmap 5 word) rc0, getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  ly_top ly <= 2 ^ 47 -> achain ly rd sp (s0Z regs) [].
Proof.
intros ly rd sp regs rc0 Hs0 Hrc Htop. left. split; [|reflexivity].
pose proof asan_consts as (C1 & _).
unfold s0Z. rewrite Hs0. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- left. rewrite Z.mod_small by lia. lia.
- right. left. replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity). lia.
Qed.

(* ---- helpers ---- *)
(* the read-only view rides through a journal whose footprint leaves the sink closed: the image clause, with the
   relro range in the image (pa_relro_img) and alloc.c's statics off the read-only bytes (Hpst_rw) *)
Lemma w3_rod_kept : forall STK0 sp0 FP ly S Hp (W : world SEGS) mem md own lyc Sc Hpc (W' : world SEGS) mem' md' k,
  ajournal_x (SK := SK) SEGS B prh_pst ARcfx STK0 sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W') mem').
Proof.
intros STK0 sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
pose proof (ajx_img HJ) as F3.
rewrite (F3 a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
- intros Hp'. exact (Hpst_rw a Hp' Hro).
Qed.

Lemma w3_sink_nil : ~ YI16.sink_open_fp [].
Proof. intros (r & Hr & _). destruct Hr. Qed.

(* a hull covers its sub-ranges' hulls (PvB_A_Home.v pvh_hull_sub, FuzzStrdupB.v sd_hull_sub) *)
Lemma w3_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
assert (M1 : shadow_addr p <= shadow_addr d) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (M2 : shadow_addr (d + n - 1) <= shadow_addr (p + m - 1))
  by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the text's window [a, a + n) inside a live block, past a hidden head (prhex_inblk): addressable, hull visible, at
   any allocator state whose ledger it is (PvB_A_Home.v pva_home_shadow's two block arms) *)
Lemma w3_inblk_shadow : forall ly S Hp W mem md Lam peak cnt fail ran most own a n,
  ARcfx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> 0 < n ->
  prhex_inblk B ly S Hp a n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a n HAR HL Hn (b & m & Hin & Hb & Hm & Hh).
pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) as HF.
pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HL) as HP.
rewrite Forall_forall in HF.
change (@cf_head CfParams_preset) with 16 in *.
assert (Hreq : req_size m = m) by (apply caw_req; lia).
destruct (in_dec Z.eq_dec b Hp) as [Hbh | Hbh].
- specialize (Hh Hbh).
  destruct (alx_hshadow SEGS B ARcfx LAWS ly S Hp W mem md b m HAR Hin Hbh) as [Hbs Hhu].
  change (@cf_head CfParams_preset) with 16 in Hbs, Hhu. rewrite Hreq in Hbs, Hhu.
  split; [eapply block_shadow_range; [exact Hbs | lia | lia] |].
  apply (w3_hull_sub _ (b + 16) (m - 16) a n (Hhu ltac:(lia))); lia.
- assert (HnoH : forall h, In h Hp -> ~ (b <= h < b + req_size m)).
  { intros h Hhp Hr.
    apply (Permutation_in _ HP) in Hhp. apply in_map_iff in Hhp as ((a0 & k0) & Eh & Hak). cbn [fst] in Eh. subst h.
    destruct (HF (a0, k0) Hak) as (Hk0 & Hab & Hah & _). cbn [fst snd] in Hk0, Hab, Hah.
    change (@cf_head CfParams_preset) with 16 in *.
    destruct (Z.eq_dec (a0 - 16) b) as [E | E]; [rewrite E in Hah; exact (Hbh Hah) |].
    assert (Hne : (a0 - 16, k0 + 16) <> (b, m)) by (intros X; injection X as X1 _; exact (E X1)).
    pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (caw_req (k0 + 16)) in Hd by lia. lia. }
  destruct (alx_shadow SEGS B ARcfx LAWS ly S Hp W mem md b m HAR Hin HnoH) as [Hbs Hhu].
  rewrite Hreq in Hbs, Hhu.
  split; [eapply block_shadow_range; [exact Hbs | lia | lia] |].
  apply (w3_hull_sub _ b m a n Hhu); lia.
Qed.

(* a source window at a later state: its bytes there, its block live there (PvB_A_Home.v pva_src_rd_at) *)
Lemma w3_src_rd : forall ly S Hp W mem md Lam peak cnt fail ran most own W0 mem0 data x,
  ARcfx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  (0 < Z.of_nat (length x) -> prhex_inblk B ly S Hp data (Z.of_nat (length x))) ->
  src_rd W0 mem0 data x -> bytes_at W mem data x -> src_rd W mem data x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own W0 mem0 data x HAR HL Hin (_ & H4 & Hc & Ham & _ & _) Hby.
split; [exact Hby|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Ham|].
destruct (Z_lt_le_dec 0 (Z.of_nat (length x))) as [Hn | Hn].
- destruct (w3_inblk_shadow ly S Hp W mem md Lam peak cnt fail ran most own data _ HAR HL Hn (Hin Hn)) as [Hr Hu].
  split; [exact Hr | intros _; exact Hu].
- split; [apply range_addressable_nil; exact Hn | intros Hp0; lia].
Qed.

(* the scratch's base is no harness head (H2CawBase.v caw_scr_not_hp) *)
Lemma w3_scr_not_hp : forall C ly3 S3 Hp3 W3 mem3 md3 scr, caw_pre (fx := fx) B C -> ARcfx ly3 S3 Hp3 W3 mem3 md3 ->
  caw_scr B C ly3 S3 scr -> ~ In scr (c_Hp C).
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 scr Hpre HAR Hscr Hin.
pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL.
assert (Hn0 : 0 <= c_size C) by (unfold c_size; lia).
pose proof (caw_scr_new B C ly3 S3 Hp3 W3 mem3 md3 scr HAR Hscr Hn0) as Hnew.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL) as HF.
pose proof (prh_ledger_heads B _ _ _ _ _ _ _ _ _ _ _ _ HL) as HP.
apply (Permutation_in _ HP) in Hin.
apply in_map_iff in Hin as ([a k] & Ea & HinL). cbn [fst] in Ea.
destruct (proj1 (Forall_forall _ _) HF _ HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hab, Hk0.
change (@cf_head CfParams_preset) with 16 in *.
destruct Hscr as (H4 & E).
assert (Hin1 : In (a - 16, k + 16) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; left; exact Hab).
assert (Hin2 : In (scr, c_size C + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (Z.eq_dec (k + 16) (c_size C + 1)) as [Eq | Ne].
- apply Hnew. replace scr with (a - 16) by lia. rewrite <- Eq. exact Hab.
- assert (Ne' : (a - 16, k + 16) <> (scr, c_size C + 1)) by (intros X; injection X; lia).
  pose proof (sep_blocks_x SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hin1 Hin2 Ne') as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite !caw_req in D by lia. lia.
Qed.

(* the second free's trace: the empty chain's (s0 = rc), pc0-filtered, at the generated return site *)
Lemma w3_trace : forall CTX0 ly (regs : bvmap 5 word), prh_univ_closure B CTX0 ->
  raZ regs = pi_ret_caw_free2 -> In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B).
Proof.
intros CTX0 ly regs (H1 & H2 & _) Hra. unfold call_trace.
destruct (frame0_ok ly regs); [|exact (H1 RT_free)].
assert (Hr : In (raZ regs) (pi_ret_sites F_check_as_written RT_free)).
{ rewrite Hra. unfold pi_ret_caw_free2. vm_compute. right. left. reflexivity. }
pose proof (H2 F_check_as_written RT_free (raZ regs) Hr) as H.
unfold prh_trace in H. unfold unwind_of_chain. cbn [flat_map prh_pc0] in H |- *. exact H.
Qed.

(* the room counts (caw_cnt C, the conjunction of the text's two count premises; the top supplies caw_pre_cnt) are a
   premise here: the free's RL_free_step needs the class-24 count, and the B' caw_base does not carry it *)
Lemma caw_WB3 : forall C P Q, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  caw_pre (fx := fx) B C -> caw_cnt C -> caw_K_oAR (fx := fx) B RW C P Q -> caw_K_oBR (fx := fx) B RW C P Q ->
  caw_K_wsR (fx := fx) B RW C P Q.
Proof.
intros C P Q PLAW PCALL Hpre Hcnt KoA KoB fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr dl' u rest Hcut HPM.
destruct Hcut as ((Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM) & R9 & R18 & HV & (Vp & Vend) & Vdep &
  Vscr & Vdl & Hdl & Hdlu & Hscr & Hrp & HL & HHB).
(* caw_pre read BY NAME (the base's caw_pre_* projections), never positionally *)
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as (HPRE & HROD & HTOP & HRAZ & HFZ0).
pose proof (caw_pre_mn (fx := fx) B C Hpre) as HMN. pose proof (caw_pre_univ (fx := fx) B C Hpre) as HUNIV.
pose proof (caw_pre_r10 (fx := fx) B C Hpre) as H10. pose proof (caw_pre_r11 (fx := fx) B C Hpre) as H11.
pose proof (caw_pre_r12 (fx := fx) B C Hpre) as H12. pose proof (caw_pre_r13 (fx := fx) B C Hpre) as H13.
pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc. pose proof (caw_pre_doc (fx := fx) B C Hpre) as Hdoc.
pose proof (caw_pre_size (fx := fx) B C Hpre) as Hsz. pose proof (caw_pre_data0 (fx := fx) B C Hpre) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B C Hpre) as Hd62. pose proof (caw_pre_src (fx := fx) B C Hpre) as HSRC.
pose proof (caw_pre_inblk (fx := fx) B C Hpre) as HINB. pose proof (caw_pre_case (fx := fx) B C Hpre) as HCASE.
pose proof (caw_pre_tree (fx := fx) B C Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL0.
pose proof (caw_pre_ran (fx := fx) B C Hpre) as Hran. pose proof (caw_pre_live (fx := fx) B C Hpre) as HMAX.
pose proof (caw_pre_max (fx := fx) B C Hpre) as HMAL. pose proof (caw_pre_frames (fx := fx) B C Hpre) as HFR.
pose proof (caw_pre_room (fx := fx) B C Hpre) as HROOM0. pose proof (caw_pre_frm0 (fx := fx) B C Hpre) as HFRM.
unfold caw_ledger in HL.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK = 26800) by (vm_compute; reflexivity).
assert (HSTKw : STK_ex_ws (PI := prh_img_B) = 16) by (vm_compute; reflexivity).
assert (Has : ASTACK = 16384) by reflexivity.
unfold caw_J in HJ. unfold caw_saved in HSV.
unfold c_sp in *. unfold CAWB_FRAME in Hsp.
set (sp0 := spZ (c_regs C)) in *.
assert (Rsp : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
assert (Hsz0 : 0 <= c_size C) by (unfold c_size; lia).
pose proof (H2CawPure.caw_V_len 0 (c_x C) u rest HV) as Hrl.
pose proof (H2CawPure.caw_V_suffix 0 (c_x C) u rest HV) as Hsfx.
assert (Hsk : (length (PjGrammar.skip rest) <= length rest)%nat).
{ clear. induction rest as [|b r IH]; [cbn; lia|]. cbn. destruct (PjGrammar.ws b); cbn; lia. }
pose proof Hscr as [Hs4 Eab3].
assert (Hscrb : In (scr, c_size C + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
(* the journal read BY NAME (YCbqG's ajx_ projections), never positionally *)
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hly3.
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR3 Hscrb) as (_ & Hscr4096 & Hscrc & _).
rewrite caw_req in Hscrc by lia.
assert (Hnew : ~ In (scr, c_size C + 1) (ablocks B (c_ly C) (c_S C))) by exact (caw_scr_new B C _ _ _ _ _ _ scr HAR3 Hscr Hsz0).
destruct (caw_J_keep B C ly3 S3 Hp3 W3 mem3 md3 k Hpre HJ ltac:(intros x Hx; rewrite Eab3; apply in_or_app; left; exact Hx))
  as [HBY3 _].
assert (HINB3 : 0 < Z.of_nat (length (c_x C)) -> prhex_inblk B ly3 S3 Hp3 (c_data C) (Z.of_nat (length (c_x C)))).
{ intros Hn. destruct (HINB Hn) as (b & m & Hin & Hb & Hm & Hh). exists b, m. rewrite Eab3, EHp.
  split; [apply in_or_app; left; exact Hin | split; [exact Hb | split; [exact Hm | exact Hh]]]. }
assert (HSRC3 : src_rd W3 mem3 (c_data C) (c_x C))
  by exact (w3_src_rd ly3 S3 Hp3 W3 mem3 md3 _ _ _ _ _ _ _ (c_W C) (c_mem C) (c_data C) (c_x C) HAR3 HL HINB3 HSRC HBY3).
(* ==== seat 1 at +136 (cut_ws): addi a0, sp, 8; jal ex_ws ==== *)
assert (HS : st_ok_pi (fx := fy) SEGS VAL (w3_E regs3 sp0 []) (mkSS (AF_cawB + CAWB_WS) w3_sr80 [w3_fregion [] 0 0] None w3_facts)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (AF_cawB + CAWB_WS))) mem3 (YK11.seg_rom SEGS)))).
{ apply w3_st_ok; [vm_compute; reflexivity | cbn; lia | exact Hsp | unfold CAWB_FRAME; lia | intros o Ho; lia | exact I |
    apply w3_facts_ok; [exact Rsp | exact Hal16]]. }
set (E := w3_E regs3 sp0 []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold w3_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := @paj_run_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (BR := @paj_branch fy rc B_prog_listing PA).
apply w3_lift.
unfold caw_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
rename ms into ms1.
assert (Emem : ms_mem ms1 = mem3).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hin & Hrg). cbn in Hin.
  destruct Hin as [<- | []]. cbn in Hrg. lia. }
clear HF HFr HG.
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply w3_E_sp).
assert (U2 : bv_unsigned (ew E 2) = sp0) by (rewrite E2; apply unsigned_lit_small; lia).
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (10%bv : bv 5) F10.
rewrite U2 in F2, F10.
assert (Hspc : spZ (ms_regs ms1) = sp0 + -80) by (unfold spZ; rewrite F2; apply unsigned_lit_small; lia).
assert (KR1 : forall r, In r w3_kl -> getr (ms_regs ms1) r = getr regs3 r).
{ intros r Hr. lazymatch type of HS with st_ok _ _ ?ss _ =>
    exact (w3_regs_kept E ss (restrict (w_H W3) ms1) regs3 sp0 [] HS eq_refl ltac:(vm_compute; reflexivity) r Hr) end. }
(* the text's premises at the call *)
set (q := sp0 - 72).
set (i0 := c_size C - Z.of_nat (length rest)).
assert (Hi0 : 0 <= i0 <= Z.of_nat (length (c_x C))) by (unfold i0, c_size; lia).
assert (Esk : skipn (Z.to_nat i0) (c_x C) = rest).
{ rewrite <- Hsfx. f_equal. unfold i0, c_size. lia. }
assert (Ha0 : getr (ms_regs ms1) 10 = w64 q) by (rewrite F10; unfold w64, q; f_equal; lia).
assert (Vq : val_mem SEGS (rdW W3 (ms_mem ms1)) q 8 (c_data C + i0)).
{ rewrite Emem. unfold q, i0.
  replace (c_data C + (c_size C - Z.of_nat (length rest))) with (c_data C + c_size C - Z.of_nat (length rest)) by lia.
  exact Vp. }
assert (Vq8 : val_mem SEGS (rdW W3 (ms_mem ms1)) (q + 8) 8 (c_data C + Z.of_nat (length (c_x C)))).
{ rewrite Emem. unfold q. replace (sp0 - 72 + 8) with (sp0 - 64) by lia. exact Vend. }
assert (Hq8 : q mod 8 = 0).
{ unfold q. pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hdm. rewrite Hal16, Z.add_0_r in Hdm.
  replace (sp0 - 72) with ((2 * (sp0 / 16) - 9) * 8) by lia. apply Z.mod_mul. lia. }
assert (HL1 : LEDGER ly3 S3 Hp3 W3 (ms_mem ms1) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0)
  by (rewrite Emem; exact HL).
assert (HSRC1 : src_rd W3 (ms_mem ms1) (c_data C) (c_x C)) by (rewrite Emem; exact HSRC3).
destruct (w3_ret 2364 ltac:(lia) ltac:(vm_compute; reflexivity)) as (RA1 & RA2 & RA3).
(* ==== the call of ex_ws (+140) by its text, the whole frame as window ==== *)
eapply SRr_bind.
{ eapply (aj_call_xW_sp (fx := fy) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) W3 E _ ms1 STK sp0 []
    (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly3 S3 Hp3 _ k (STK_ex_ws (PI := prh_img_B)) 80
    [(q, q + 8)] (-80) _ [] _ HS eq_refl HJ).
  - exact Hspc.
  - reflexivity.
  - lia.
  - rewrite HSTKw. lia.
  - rewrite HSTK, HSTKw. lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite (KR1 3%bv ltac:(cbv [In w3_kl]; left; reflexivity)), (Hk 3%bv ltac:(left; reflexivity)). exact Hgp.
  - rewrite (KR1 4%bv ltac:(cbv [In w3_kl]; right; left; reflexivity)), (Hk 4%bv ltac:(right; left; reflexivity)). exact Htp.
  - exact F1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. exact RA1.
  - apply (w3_achain _ _ _ _ (c_rc C)); [| exact Hrc | rewrite Etop; lia].
    rewrite (KR1 8%bv ltac:(cbv [In w3_kl]; right; right; left; reflexivity)). exact R8.
  - intros HPRE1 HWIN1.
    assert (HROD1 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W3) (ms_mem ms1)))
      by exact (w3_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ w3_sink_nil HROD).
    assert (HTOP1 : spZ (ms_regs ms1) + 64 <= ly_stk_hi ly3) by (rewrite Hspc, Eshi; lia).
    assert (HRAZ1 : raZ (ms_regs ms1) < YM05.alloc_ceiling) by (unfold raZ; rewrite F1, unsigned_lit_small by lia; exact RA2).
    assert (Hqlo : spZ (ms_regs ms1) <= q) by (rewrite Hspc; unfold q; lia).
    assert (Hqhi : q + 16 <= spZ (ms_regs ms1) + 80) by (rewrite Hspc; unfold q; lia).
    exact (TEXWS fy ly3 S3 Hp3 W3 (ms_regs ms1) (ms_mem ms1) _ [] q (c_data C) i0 80 (c_x C) (c_Lam C) (c_peak C)
      (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0 (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 Hfz)))) Ha0 Vq Vq8
      Hq8 Hqlo Hqhi HWIN1 HSRC1 HINB3 Hsz Hi0 HL1).
  - intros a (rr & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha. right. right. right. rewrite HSTK.
    unfold q in Ha. lia. }
cbv beta. intros W2 c2 Hwle2 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & -> & HJ4 & HJc & HX & HP4 & HK4).
unfold fQmn in HK4. destruct HK4 as ((HRL4 & Vp4 & EHp4 & ES4 & Eab4 & HL4) & HMN4).
subst Hp4 S4.
assert (HPM4 : P mem4) by exact (PCALL _ _ HMN4 HPM).
clear HPM HMN4 HJc.
rewrite Esk in Vp4.
set (p2 := c_data C + c_size C - Z.of_nat (length (PjGrammar.skip rest))).
assert (Vp2 : val_mem SEGS (rdW W2 mem4) (sp0 - 72) 8 p2) by exact Vp4.
(* the frame but in->p is kept across ex_ws *)
assert (KW : forall a, sp0 - 80 <= a < sp0 -> ~ (q <= a < q + 8) -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite <- Emem. apply HX; [lia | intros (rr & Hr & Ha2); destruct Hr as [<- | []]; cbn [fst snd] in Ha2; exact (Hn Ha2)]. }
assert (Vend4 : val_mem SEGS (rdW W2 mem4) (sp0 - 64) 8 (c_data C + c_size C)).
{ apply (val_mem_kept SEGS (w_H W3) (w_H W2) mem3 mem4); [|exact Vend]. intros kk Hkk. apply KW; unfold q; lia. }
assert (Vscr4 : val_mem SEGS (rdW W2 mem4) (sp0 - 48) 8 scr).
{ apply (val_mem_kept SEGS (w_H W3) (w_H W2) mem3 mem4); [|exact Vscr]. intros kk Hkk. apply KW; unfold q; lia. }
assert (Vdl4 : val_mem SEGS (rdW W2 mem4) (sp0 - 40) 4 dl').
{ apply (val_mem_kept SEGS (w_H W3) (w_H W2) mem3 mem4); [|exact Vdl]. intros kk Hkk. apply KW; unfold q; lia. }
destruct HSV as (V1 & V2 & V3 & V4).
assert (HSV4 : val_mem SEGS (rdW W2 mem4) (sp0 - 8) 8 (bv_unsigned (getr (c_regs C) 1)) /\
  val_mem SEGS (rdW W2 mem4) (sp0 - 16) 8 (bv_unsigned (getr (c_regs C) 8)) /\
  val_mem SEGS (rdW W2 mem4) (sp0 - 24) 8 (bv_unsigned (getr (c_regs C) 9)) /\
  val_mem SEGS (rdW W2 mem4) (sp0 - 32) 8 (bv_unsigned (getr (c_regs C) 18))).
{ split; [|split; [|split]]; (apply (val_mem_kept SEGS (w_H W3) (w_H W2) mem3 mem4); [intros kk Hkk; apply KW; unfold q; lia|]);
  assumption. }
clear V1 V2 V3 V4.
assert (KR4 : forall r, In r w3_kl -> getr regs4 r = getr regs3 r).
{ intros r Hr. rewrite (w3_pres_kl _ _ r HP4 Hr). exact (KR1 r Hr). }
assert (Hsp4 : spZ regs4 = sp0 - 80).
{ unfold spZ. rewrite (w3_pres_r _ _ 2%bv HP4 ltac:(vm_compute; left; reflexivity)). unfold spZ in Hspc. lia. }
(* ==== seat 2 at +144 (ex_ws's return): ld s1 / s2 / a0 from in->p, in->end, in->scratch; jal __wrap_free ==== *)
assert (HS2 : st_ok_pi (fx := fy) SEGS VAL (w3_E regs4 sp0 [p2; c_data C + c_size C; scr])
  (mkSS (AF_cawB + 144) w3_sr80 [w3_fregion [(-72, 8%N); (-64, 8%N); (-48, 8%N)] 0 0] None w3_facts)
  (restrict (w_H W2) (@YK11.mkst fy regs4 (Z_to_bv 64 (BASE + (AF_cawB + 144))) mem4 (YK11.seg_rom SEGS)))).
{ apply w3_st_ok; [vm_compute; reflexivity | cbn; lia | exact Hsp4 | unfold CAWB_FRAME; lia | intros o Ho; lia | |
    apply w3_facts_ok; [exact Rsp | exact Hal16]].
  cbn [w3_vals_ok]. change (N.to_nat 8) with 8%nat. change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8.
  replace (sp0 + -72) with (sp0 - 72) by lia. replace (sp0 + -64) with (sp0 - 64) by lia.
  replace (sp0 + -48) with (sp0 - 48) by lia.
  split; [exact Vp2|]. split; [unfold p2, c_size in *; lia|]. split; [lia|].
  split; [exact Vend4|]. split; [unfold c_size in *; lia|]. split; [lia|].
  split; [exact Vscr4|]. split; [lia|]. split; [lia | exact I]. }
set (E2' := w3_E regs4 sp0 [p2; c_data C + c_size C; scr]) in HS2.
assert (HEI2 : img_env VAL A_LIM E2') by (subst E2'; unfold w3_E; apply Eimg_env).
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2' (mrestrict (w_H W2) mem4)) by (unfold sh_ok; apply Forall_nil).
paj_run_tok_x_inv RUN HS2 HJ4 SHOK2 HPM4 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
rename ms into ms2. clear HS HJ. rename HS2 into HS. rename HJ4 into HJ. rename HPM4 into HPM.
assert (Emem2 : ms_mem ms2 = mem4).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hin & Hrg). cbn in Hin.
  destruct Hin as [<- | []]. cbn in Hrg. lia. }
clear HF HFr HG.
assert (E2a : ew E2' 2 = Z_to_bv 64 sp0) by (subst E2'; apply w3_E_sp).
assert (U2a : bv_unsigned (ew E2' 2) = sp0) by (rewrite E2a; apply unsigned_lit_small; lia).
prreg HS (1%bv : bv 5) G1. prreg HS (2%bv : bv 5) G2. prreg HS (9%bv : bv 5) G9. prreg HS (10%bv : bv 5) G10.
prreg HS (18%bv : bv 5) G18.
assert (E33 : ew E2' 33 = Z_to_bv 64 p2) by (subst E2'; exact (w3_E_val regs4 sp0 _ 0 ltac:(lia))).
assert (E34 : ew E2' 34 = Z_to_bv 64 (c_data C + c_size C)) by (subst E2'; exact (w3_E_val regs4 sp0 _ 1 ltac:(lia))).
assert (E35 : ew E2' 35 = Z_to_bv 64 scr) by (subst E2'; exact (w3_E_val regs4 sp0 _ 2 ltac:(lia))).
rewrite U2a in G2. rewrite E33 in G9. rewrite E35 in G10. rewrite E34 in G18.
assert (Hspc2 : spZ (ms_regs ms2) = sp0 + -80) by (unfold spZ; rewrite G2; apply unsigned_lit_small; lia).
assert (KR2 : forall r, In r w3_kl -> getr (ms_regs ms2) r = getr regs3 r).
{ intros r Hr. transitivity (getr regs4 r); [|exact (KR4 r Hr)].
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    exact (w3_regs_kept E2' ss (restrict (w_H W2) ms2) regs4 sp0 _ HS eq_refl ltac:(vm_compute; reflexivity) r Hr) end. }
pose proof (ajx_ar HJ) as HAR4. pose proof (ajx_ly HJ) as Hly4. pose proof (ajx_qt HJ) as HQT4.
pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & E4top & _).
(* the free's call memory QMm_cf: the room, cf_hull_ok from cut_ws's hull budget (the free's state is cut_ws's),
   arodata_ok_cf from the reader form at the call memory (w3_rod_kept from the entry's) through the bridge *)
assert (HQM : QMm_cf SEGS B S3 (ms_mem ms2)).
{ destruct (QM_cf_of_room SEGS B _ _ _ _ _ _ (proj1 HAR4) HQT4 (YGcfRoomLive.room_live_room S3 HROOM)
    (PresetHullPay.hull_ok_of_budget _ _ HHB)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
  destruct Hrelro_eq as [ERL ERH].
  apply (YGcfAroBridge.arodata_ok_cf_of_P SEGS B W2 (ms_mem ms2) Hrelro_seg Herrno_relro Hrelro_top Hro_reads_nw).
  rewrite ERL, ERH. exact (w3_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ w3_sink_nil HROD). }
pose proof (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR)) as HUok.
pose proof (alloc_model_laws_x_cf B HUok) as AMX.
assert (Hnhp : ~ In scr Hp3) by (rewrite EHp; exact (w3_scr_not_hp C ly3 S3 Hp3 W3 mem3 md3 scr Hpre HAR3 Hscr)).
destruct (w3_ret 2380 ltac:(lia) ltac:(vm_compute; reflexivity)) as (RF1 & RF2 & RF3).
(* the free's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
   post carries the trace in the journal's wild budget, which ajournal_xw_fix1R drops again) *)
assert (HTR : In (call_trace ly4 (pc_free_ra0 (as_code B)) (ms_regs ms2) []) (as_universe B)).
{ apply (w3_trace (c_CTX0 C) ly4 (ms_regs ms2) HUNIV). unfold raZ. rewrite G1, unsigned_lit_small by lia.
  exact Hfree2. }
(* ==== the free of the scratch (+156) by the runtime row under the re-hide, with the memnorm keep ==== *)
apply SRr_ret. cbv beta.
eapply (YA0nH.SRrG_bind SEGS RW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (fx := fy) (SK := SK) SEGS B prh_pst LAWS (@pa_segs_low _ _ PA)
    (pal_env B PAL) (ARx_owned_low_law_xs SEGS B LAWS_cf) (ARx_wf_law_xs SEGS B) AMX (AFREE fy)
    W2 E2' _ ms2 STK sp0 [] (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly4 S3 Hp3 _ (k + k1)
    scr (c_size C + 1) (-80) (ew E2' 2) (Z_to_bv 64 (BASE + 2380)) [] HS (pal_free B PAL) eq_refl
    (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARcfx (@wle SEGS) RW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  - rewrite Eab4. exact Hscrb.
  - exact Hnhp.
  - rewrite G10. reflexivity.
  - exact (st_ok_restrict_reg SEGS (w_H W2) E2' _ ms2 2%bv HS).
  - reflexivity.
  - exact U2a.
  - reflexivity.
  - lia.
  - rewrite Has, HSTK. lia.
  - rewrite (KR2 3%bv ltac:(cbv [In w3_kl]; left; reflexivity)), (Hk 3%bv ltac:(left; reflexivity)). exact Hgp.
  - rewrite (KR2 4%bv ltac:(cbv [In w3_kl]; right; left; reflexivity)), (Hk 4%bv ltac:(right; left; reflexivity)). exact Htp.
  - exact G1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - exact HQM.
  - apply (caw_chain _ _ _ (c_rc C)).
    + unfold raZ. rewrite G1, unsigned_lit_small by lia. exact RF1.
    + rewrite (KR2 8%bv ltac:(cbv [In w3_kl]; right; right; left; reflexivity)). exact R8.
    + exact Hrc.
    + rewrite Hspc2. lia.
    + rewrite E4top. lia.
  - exact (admits_fix _ _ _ HUok HTR).
  - intros Hin. exfalso. exact (Hnew Hin). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & Eab4' & Eab5) & Hfr5 & Hpre5 &
  Hun5 & (qq & trc & Hqq & Hqqin & Hpath & Hg & Hleaf) & Hkept & HMN5).
(* the journal after the call: the fixed trace leaves the budget *)
pose proof (ajournal_xw_fix1R HTR HJ5) as HJ5f. clear HJ5. rename HJ5f into HJ5.
assert (HPM5 : P mem5) by exact (PCALL _ _ HMN5 HPM).
clear HPM HMN5 Hleaf.
assert (Eab0 : ablocks B ly5 S5 = ablocks B (c_ly C) (c_S C)).
{ rewrite Eab4, Eab3 in Eab4'. destruct (caw_split_last _ _ _ _ Eab4' Hnew) as [-> ->]. rewrite Eab5, app_nil_r. reflexivity. }
destruct Hkept as (K1 & K2 & K3 & K4 & K5 & K6).
(* the class-24 count at the free's entry state S3: the entry's (caw_cnt C) plus the scratch (caw_scr: one block more) *)
pose proof Hcnt as (_ & Hc0).
assert (Hc3 : YGcfRoomLive.ccnt24 S3 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1)
  by (pose proof (w3_ccnt24_app B (c_ly C) (c_S C) ly3 S3 _ Eab3) as X; clear - X Hc0; lia).
(* the room after the free: a8's keep at L24 + DRV + 1, its batch-room conjunct preset_rl_b24_ok's closed one *)
assert (HRL5 : room_live_cf S5).
{ change S5 with (snd (tt, S5)).
  exact (YGcfRoomLive.RL_free_step SEGS B _ _ _ _ _ _ _ _ (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) _ _ _ _
    (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ Hpre5)
    (conj Hc3 (proj2 (CfRoomLivePreset.preset_rl_b24_ok (c_S C) Hc0))) HROOM Hpath). }
(* the run position after the free: caw_prog at caw_evs = caw_ev1 ++ [HFr (size + 1)]; cut_ws's caw_prog at caw_ev1
   gives the position i + 1 at S3, the free's event HFr (size + 1) moves it to S (i + 1) = i + 2 at S5 *)
assert (Hqnn : qq <> PNull) by (intros ->; cbn in Hqq; lia).
assert (HRP5 : caw_prog C (caw_evs C) S5).
{ intros rsm rx ros ri rH0 rhist Hp0 Hrun.
  change (caw_evs C) with (caw_ev1 C ++ [PresetReqAt.HFr (c_size C + 1)]) in Hrun.
  destruct (caw_run_at_app rsm rx ros ri _ _ Hrun) as (Hr1 & Hr2).
  destruct (Hrp rsm rx ros ri rH0 rhist Hp0 Hr1) as (hist' & Hpos3).
  pose proof (caw_run_at_nth rsm rx ros _ _ [] Hr2) as HEVfr.
  replace (ri + length (caw_evs C))%nat with (Datatypes.S (ri + length (caw_ev1 C)))
    by (unfold caw_evs, caw_ev1; cbn [length]; rewrite !(Nat.add_comm ri); reflexivity).
  eexists.
  exact (PresetRoomPosKeep.room_pos_keep_free SEGS B _ _ _ _ _ _ _ _ rsm rx ros _ rH0 hist' qq (c_size C + 1) _ trc S5
    (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ Hpre5) Hun5 Hqqin Hqnn Hpath Hpos3 HEVfr). }
(* the ledger after the free, at the entry's most and own 0: every prh_pst byte (g_most's and g_own_ran_out's
   included) an image byte off the owned statics and errno, kept by the runtime row's image clause *)
rewrite <- Emem2 in HL4.
assert (HL5 : LEDGER ly5 S5 Hp3 W5 mem5 (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0).
{ apply (S1Ledger.prh_ledger_kept_aview B ly4 S3 Hp3 W2 (ms_mem ms2) ly5 S5 Hp3 W5 mem5 _ _ _ _ _ _ _ HL4).
  - intros a Ha. destruct (Hpst a Ha) as [Ho He]. exact (K3 a (Hpst_img a Ha) Ho He).
  - intros a kk i Hin Hi.
    destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL0 Hin) as (Hk0 & Hab & _).
    change (@cf_head CfParams_preset) with 16 in *.
    assert (Hab4 : In (a - 16, kk + 16) (ablocks B ly4 S3)) by (rewrite Eab4, Eab3; apply in_or_app; left; exact Hab).
    assert (Ne : (a - 16, kk + 16) <> (scr, c_size C + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hab).
    assert (Hscr4 : In (scr, c_size C + 1) (ablocks B ly4 S3)) by (rewrite Eab4; exact Hscrb).
    pose proof (sep_blocks_x SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ _ _ HAR4 Hab4 Hscr4 Ne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite !caw_req in D by lia.
    apply (K2 (a - 16) (kk + 16) i Hab4); [rewrite caw_req by lia; lia | cbv beta; rewrite caw_req by lia; lia].
  - intros a kk Hin _. destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL0 Hin) as (_ & Hab & _). rewrite Eab0. exact Hab.
  - apply Permutation_refl. }
(* the frame across the free: above the call's stack window *)
assert (KS5 : forall a, sp0 - 80 <= a < sp0 -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W2) mem4 a).
{ intros a Ha. rewrite <- Emem2. apply K1; [rewrite HSTK in Hslo; lia | lia]. }
assert (Vdl5 : val_mem SEGS (rdW W5 mem5) (sp0 - 40) 4 dl').
{ apply (val_mem_kept SEGS (w_H W2) (w_H W5) mem4 mem5); [|exact Vdl4]. intros kk Hkk. apply KS5. lia. }
destruct HSV4 as (V1 & V2 & V3 & V4).
assert (HSV5 : val_mem SEGS (rdW W5 mem5) (sp0 - 8) 8 (bv_unsigned (getr (c_regs C) 1)) /\
  val_mem SEGS (rdW W5 mem5) (sp0 - 16) 8 (bv_unsigned (getr (c_regs C) 8)) /\
  val_mem SEGS (rdW W5 mem5) (sp0 - 24) 8 (bv_unsigned (getr (c_regs C) 9)) /\
  val_mem SEGS (rdW W5 mem5) (sp0 - 32) 8 (bv_unsigned (getr (c_regs C) 18))).
{ split; [|split; [|split]]; (apply (val_mem_kept SEGS (w_H W2) (w_H W5) mem4 mem5); [intros kk Hkk; apply KS5; lia|]);
  assumption. }
clear V1 V2 V3 V4.
assert (KR5 : forall r, In r w3_kl -> getr regs5 r = getr regs3 r).
{ intros r Hr. rewrite (w3_pres_kl _ _ r HP5 Hr). exact (KR2 r Hr). }
assert (Hsp5 : spZ regs5 = sp0 - 80).
{ unfold spZ. rewrite (w3_pres_r _ _ 2%bv HP5 ltac:(vm_compute; left; reflexivity)). unfold spZ in Hspc2. lia. }
assert (R95 : getr regs5 9 = Z_to_bv 64 p2).
{ rewrite (w3_pres_r _ _ 9%bv HP5 ltac:(vm_compute; repeat (first [left; reflexivity | right]))). exact G9. }
assert (R185 : getr regs5 18 = Z_to_bv 64 (c_data C + c_size C)).
{ rewrite (w3_pres_r _ _ 18%bv HP5 ltac:(vm_compute; repeat (first [left; reflexivity | right]))). exact G18. }
(* ==== seat 3 at +160 (the free's return): beq s1, s2 ==== *)
assert (HS3 : st_ok_pi (fx := fy) SEGS VAL (w3_E regs5 sp0 [dl'])
  (mkSS (AF_cawB + 160) w3_sr80 [w3_fregion [(-40, 4%N)] 0 0] None w3_facts)
  (restrict (w_H W5) (@YK11.mkst fy regs5 (Z_to_bv 64 (BASE + (AF_cawB + 160))) mem5 (YK11.seg_rom SEGS)))).
{ apply w3_st_ok; [vm_compute; reflexivity | cbn; lia | exact Hsp5 | unfold CAWB_FRAME; lia | intros o Ho; lia | |
    apply w3_facts_ok; [exact Rsp | exact Hal16]].
  cbn [w3_vals_ok]. change (N.to_nat 4) with 4%nat. change (8 * Z.of_N 4) with 32. change (Z.of_N 4) with 4.
  replace (sp0 + -40) with (sp0 - 40) by lia.
  split; [exact Vdl5|]. split; [destruct Hdl; lia|]. split; [lia | exact I]. }
set (E3 := w3_E regs5 sp0 [dl']) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; unfold w3_E; apply Eimg_env).
assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] E3 (mrestrict (w_H W5) mem5)) by (unfold sh_ok; apply Forall_nil).
assert (U9 : U E3 (SOff 9 0) = p2).
{ apply U_atom; [subst E3; rewrite (w3_E_reg regs5 sp0 _ 9 9%bv eq_refl ltac:(discriminate)); exact R95 | unfold p2, c_size in *; lia]. }
assert (U18 : U E3 (SOff 18 0) = c_data C + c_size C).
{ apply U_atom; [subst E3; rewrite (w3_E_reg regs5 sp0 _ 18 18%bv eq_refl ltac:(discriminate)); exact R185 | unfold c_size in *; lia]. }
pose (RUNTOR := @paj_run_to_x_invR fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BRR := w3_branchR fy RW).
psrr_branch_tok RUN BRR HS3 SHOK3 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- (* taken (B' 0x82018 -> 0x82074): p'' = end, so the whole rest is whitespace: rc = 0 and differs = 0 *)
  rewrite branch_eq_U, U9, U18 in Hc. apply Z.eqb_eq in Hc.
  assert (Hsk0 : PjGrammar.skip rest = []) by (apply length_zero_iff_nil; unfold p2 in Hc; lia).
  assert (Hread : ck_read (c_x C) = Some u) by (apply H2CawPure.caw_read_V; exists rest; split; [exact HV | exact Hsk0]).
  destruct HCASE as [[Hrc0 Ht] | [Hrcn Hn]]; [| rewrite Hread in Hn; discriminate Hn].
  rewrite Hread in Ht. injection Ht as Ht.
  assert (Hdl0 : dl' = 0).
  { destruct Hdl as [H0 | H1]; [exact H0|]. destruct (proj1 Hdlu H1) as [_ Hne]. exfalso. exact (Hne (eq_sym Ht)). }
  paj_run_to_tok_x_invR RUNTOR HS3 HJ5 SHOK3 HPM5 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_OB).
  { intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
  rename ms into msB.
  assert (EmB : ms_mem msB = mem5).
  { apply functional_extensionality. intros x. apply HF. intros (rg & Hin & Hrg). cbn in Hin.
    destruct Hin as [<- | []]. cbn in Hrg. lia. }
  clear HF HFr HG.
  prreg HS3 (2%bv : bv 5) B2. prreg HS3 (18%bv : bv 5) B18.
  assert (E33c : ew E3 33 = Z_to_bv 64 dl') by (subst E3; exact (w3_E_val regs5 sp0 _ 0 ltac:(lia))).
  assert (E2c : bv_unsigned (ew E3 2) = sp0) by (subst E3; rewrite w3_E_sp; apply unsigned_lit_small; lia).
  rewrite E2c in B2.
  assert (KRB : forall r, In r w3_kl -> getr (ms_regs msB) r = getr regs3 r).
  { intros r Hr. transitivity (getr regs5 r); [|exact (KR5 r Hr)].
    lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ =>
      exact (w3_regs_kept E3 (abs_ss VAL ss) (restrict (w_H W5) msB) regs5 sp0 _ HS3 eq_refl
        ltac:(vm_compute; reflexivity) r Hr) end. }
  pmkst HS3. rewrite EmB. rewrite EmB in HJ5, HPM5.
  apply (KoB fy ly5 S5 Hp3 W5 (ms_regs msB) mem5 _ (k + k1 + (st_nev S5 - st_nev S3)) 0); [|exact HPM5].
  split; [|split; [|split; [|split; [|split]]]].
  + split; [exact Hfz|]. split; [exact Hfk|]. split; [unfold caw_JR; exact HJ5|].
    split; [intros r Hr; rewrite (KRB r ltac:(clear - Hr; cbv [In w3_kl] in *; tauto)); exact (Hk r Hr)|].
    split; [unfold spZ; rewrite B2, unsigned_lit_small by lia; change (c_sp C) with sp0; unfold CAWB_FRAME; lia|].
    split; [rewrite (KRB 8%bv ltac:(cbv [In w3_kl]; right; right; left; reflexivity)); exact R8|].
    split; [unfold caw_saved; change (c_sp C) with sp0; exact HSV5|].
    split; [exact EHp|]. exact HRL5.
  + rewrite B18, E33c, Hdl0. apply bv_eq. vm_compute. reflexivity.
  + right. split; [reflexivity | exact Hrc0].
  + exact Eab0.
  + exact HRP5.
  + exact HL5.
- (* not taken (B' 0x8201c): p'' <> end, so rc <> 0 *)
  rewrite branch_eq_U, U9, U18 in Hc. apply Z.eqb_neq in Hc.
  assert (Hrcn : c_rc C <> 0).
  { intros Hrc0. destruct HCASE as [[_ Ht] | [Hrcn _]]; [|exact (Hrcn Hrc0)].
    apply H2CawPure.caw_read_V in Ht as (r & Hr & Hs). rewrite HV in Hr. injection Hr as _ <-.
    apply Hc. unfold p2. rewrite Hs. cbn [length Z.of_nat]. lia. }
  paj_run_to_tok_x_invR RUNTOR HS3 HJ5 SHOK3 HPM5 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_OA).
  { intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
  rename ms into msA.
  assert (EmA : ms_mem msA = mem5).
  { apply functional_extensionality. intros x. apply HF. intros (rg & Hin & Hrg). cbn in Hin.
    destruct Hin as [<- | []]. cbn in Hrg. lia. }
  clear HF HFr HG.
  prreg HS3 (2%bv : bv 5) A2.
  assert (E2c : bv_unsigned (ew E3 2) = sp0) by (subst E3; rewrite w3_E_sp; apply unsigned_lit_small; lia).
  rewrite E2c in A2.
  assert (KRA : forall r, In r w3_kl -> getr (ms_regs msA) r = getr regs3 r).
  { intros r Hr. transitivity (getr regs5 r); [|exact (KR5 r Hr)].
    lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ =>
      exact (w3_regs_kept E3 (abs_ss VAL ss) (restrict (w_H W5) msA) regs5 sp0 _ HS3 eq_refl
        ltac:(vm_compute; reflexivity) r Hr) end. }
  pmkst HS3. rewrite EmA. rewrite EmA in HJ5, HPM5.
  apply (KoA fy ly5 S5 Hp3 W5 (ms_regs msA) mem5 _ (k + k1 + (st_nev S5 - st_nev S3))); [|exact HPM5].
  split; [|split; [|split; [|split]]].
  + split; [exact Hfz|]. split; [exact Hfk|]. split; [unfold caw_JR; exact HJ5|].
    split; [intros r Hr; rewrite (KRA r ltac:(clear - Hr; cbv [In w3_kl] in *; tauto)); exact (Hk r Hr)|].
    split; [unfold spZ; rewrite A2, unsigned_lit_small by lia; change (c_sp C) with sp0; unfold CAWB_FRAME; lia|].
    split; [rewrite (KRA 8%bv ltac:(cbv [In w3_kl]; right; right; left; reflexivity)); exact R8|].
    split; [unfold caw_saved; change (c_sp C) with sp0; exact HSV5|].
    split; [exact EHp|]. exact HRL5.
  + exact Hrcn.
  + exact Eab0.
  + exact HRP5.
  + exact HL5.
Qed.

End f.
End d.

Check caw_WB3.
Print Assumptions caw_WB3.
