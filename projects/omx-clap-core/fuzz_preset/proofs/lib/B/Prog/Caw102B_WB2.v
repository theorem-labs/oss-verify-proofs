(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Disp_word.v, with its module paths and module names changed; 116 of its 154 lines of code are new or changed and 465 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Caw102A_Kit.v, with its module names changed; 989 of its 1073 lines of code are new or changed and 70 lines of the source are left out. *)
(* fuzz_preset, image B' (#102): segment WB2 of the walk of check_as_written (Caw102B.v), from cut_ev (B' 0x81fc4,
   the scratch non-NULL) through the ex_value call to cut_ws (0x82000, ex_value returned 0) or, on its refusal, through
   the scratch's free to cut_oA (0x8201c). Lane CawB102 (segment lane CawB102WB2); re-walk lane CawA102R for B'
   (re-fitted to the f97c re-keyed base by CawA102R.CawGWB2; to the batch kit's base by CawA102R.KWB2; now INT102-READY).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   caw_WB2 (generic P, abstract): from cut_ev, +76 .. +100 (a1 = (rc == 0 ? doc : 0), the scratch and 0 into the
   struct, a0 = q = sp0 - 72) by the runner; the jal ex_value by YCbqGcallW.aj_call_xWF_sp at window 80 with the
   tex_value_specX at nesting DOC_D (its memnorm by srr_inv_mn, its keep by srr_inv_call); the re-seat at +104 and
   `beqz a0`: r = 0 runs to +136 and closes caw_K_wsR; r = -1 (prhex_V 0 x = None, so ck_read x = None by
   H2CawPure.caw_read_V and rc <> 0 by caw_pre) loads the scratch, frees it at +112 by the keep-carrying free rule
   under the re-hide, YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (its memnorm keep the last conjunct; the call memory's
   QMm_cf from the room, the hull budget cut_ev carries across ex_value (PresetHullPay.hull_ok_of_budget) and the
   reader form through YGcfAroBridge.arodata_ok_cf_of_P at the image's relro rows; ablocks back to entry's by
   caw_split_last, the room by YGcfRoomLive.RL_free_step at L24 + DRV + 1, the progress fact caw_prog stepped from
   caw_ev1 to caw_evs by PresetRoomPosKeep.room_pos_keep_free), re-seats at +116 and runs `j` to +164 over the R runner
   at wle' (the re-hide's world relation), closing caw_K_oAR. caw_WB2 therefore states the continuations' R forms at
   wle' (caw_K_wsR / caw_K_oAR / caw_K_evR); the run before the free is the wle one, lifted (wb2_lift).
   BASE OF RECORD: the kit's cut, this row's lib/B/Prog/Caw102B.v
   (its statements, unchanged here), the inputs as the cut carries them: lib/A/PRH_FnCheck.v
   c40cf3fdcd2a (tcheck_as_written_specX :832-902), PRH_Base.v (fpre :988-1010, its last conjunct
   frm_zero (fp_csr fx), FRM0-ENTRY; prh_univ_closure :1203, prh_univ_closure_lit :1225), PRH_FnEx.v
   (tex_value_specX :291, unchanged by the batch; now f97c's text plus hull_used S S' [] in its post, PRH_FnEx.v:335, read as HHU4), lib/A/Prog/S1Ledger.v 8cf15eeb6311 (prh_ledger_kept_aview :736),
   lib/Reusable/YGcfRoomLive.v (ccnt24 :1141, rl_b24_ok :1204, RL_free_step :1432),
   lib/A/CfRoomLivePreset.v d0e5e47dcb02 (preset_rl_b24_ok :53), lib/Spec/PresetRoomPosKeep.v
   (room_pos_keep_free), PresetLiveBounds.v f78da450d5f6 (L24, DRV), PresetRoom.v 0b749d72634f (ccnt),
   lib/Reusable/YGcallMxmn.v 3c08bbab8292 (aj_free_x_ct_m :1650), YCbqGcallW.v fb6aa11676a2 (aj_call_xWF_sp :480),
   YCbqG.v (the journal read by ajx_*; ajournal_xw_fix1 :488), YG01.v 845507e218b0 (admits_fix :218).
   WHAT CHANGED AT THIS BASE (a Theorem Labs lane, the batch; this file was last green at
   the P'' trial), and
   why:
   (1) THE RUN-WORD LIST DW IS GONE (PRH_FnCheck.v :841; prh_univ_closure CTX0): the base dropped cawB's c_DW.
   wb2_free_trace reads the closure by name (Caw102B.caw_pre_univ) and its literal clause by
   PRH_Base.prh_univ_closure_lit (no DW argument).
   (2) THE ROOM COUNTS are the text's entry premises after room_live_cf (:862-863), then the hull budget and HPOS: caw_pre has 27 conjuncts and ck_frm0
   moved by four, so a positional pattern over caw_pre would now bind silently wrong. Every destruct of caw_pre in this
   file (wb2_scr_not_hp, wb2_rod, wb2_src_rd, wb2_apart_x, wb2_tree, wb2_ledger_free, wb2_free_trace, caw_WB2) is the
   base's projections caw_pre_* now; caw_WB2 poses them in the order and under the names of its former pattern. The
   premise caw_cnt C stays (the top gives it by Caw102B.caw_pre_cnt, by conversion; the named argument CAW_CNT is gone).
   (3) THE OUTCOME (:879-888, caw_dead) is carried by cut_end only; WB2 builds cut_ws, which now ends with the free's hull budget (Caw102B.v:435), and cut_oAR, cut_oA's R form (:437-442).
   STATEMENT CHANGES (part 3c, the free under the re-hide): caw_WB2 states the continuations' R forms at wle'
   (caw_K_wsR / caw_K_oAR in, caw_K_evR out), the re-hide's world relation past the free; every other lemma of this
   file keeps its statement and name.
   THE DESIGN (from the f97c re-fit and the P'' set, unchanged here):
   - THE PROGRESS FACT: cut_ev / cut_ws carry caw_prog C (caw_ev1 C) S, cut_oA caw_prog C (caw_evs C) S (for any run
   position i at the entry state whose next events are E, a position i + length E at S). ex_value keeps it (its post's
   position keep, in the implication form, composed under caw_prog); on the refused arm the free steps it:
   caw_run_at_app splits a run at caw_evs C = caw_ev1 C ++ [HFr (size + 1)], the cut's caw_prog at caw_ev1 C gives the
   position i + 1 at the free's entry state, caw_run_at_nth reads the event HFr (size + 1) there, and
   room_pos_keep_free gives S (i + 1) = i + 2 at the free's exit state.
   - THE ROOM COUNT at the free: RL_free_step needs rl_b24_ok at the free's entry state S4: ccnt24 S4 <= ccnt24 (c_S C)
   + 1 <= L24 + DRV + 1 (wb2_ccnt24_app: ccnt24 counts the requests ablocks lists, and caw_scr adds the scratch's one
   block to the entry's; caw_cnt C bounds the entry's), with preset_rl_b24_ok's closed batch-room conjunct.
   - FRM0-ENTRY: fpre's fifth conjunct frm_zero (fp_csr fx); ex_value's callee fpre is built with it at the call's
   float state fy, from caw_base's first conjunct frm_zero (fp_csr fy).
   - THE FREE'S TRACE is a FIXED one of the universe (the P'' set: the call rule asks admits, YG01.admits_fix; its post
   carries the trace in the journal's wild budget, which YCbqG.ajournal_xw_fix1R drops again).
   - The ledger at own = 0: over the hand steps by S1Ledger.prh_ledger_kept_aview, across ex_value by its text's post,
   across __wrap_free by wb2_ledger_free. The base names in this file's statements take the entry float state
   explicitly, (fx := fx).
   SECTION HYPOTHESES (discharged later at the image instance / by the callee texts; owners; the relro rows are new):
   TEXV (ex_value's text at every float state; the kit owner, the walkkit texts' prover), AFREE (the free row under the re-hide
   with the memnorm keep at the leaf, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep, at every float state), PAL
   (PALib B; the kit owner), and four image facts: Hpst (prh_pst neither runtime-owned nor errno),
   Hpst_img (prh_pst in the image), Hpst_rw (prh_pst not read-only: arodata_okP crosses a journal), Hret_free (caw's
   first free return site is listed in pi_ret_sites F_check_as_written RT_free); PAL and the four image facts are
   discharged at PI_prog_B (a Theorem Labs lane's IMG_TOP_B), as Caw102B_Top.v states them. NEW with the free's QMm_cf: the cf
   layer's relro rows Hrelro_seg / Herrno_relro / Hrelro_top / Hrelro_eq / Hro_reads_nw (the cno B' base's
   cnbi_relro_* rows), discharged at the image by lib/AU/CfAroPresetB.v relro_seg_preset_AU / errno_relro_preset_AU /
   relro_top_preset_AU / ro_reads_nw_preset_AU and the range equation by computation. caw_cnt C is a premise of caw_WB2
   (the text's room counts, Caw102B.caw_pre_cnt), not a Section hypothesis.
   Numerals: 80 (LENGTH: the frame), 8 / 32 / 40 / 48 / 56 / 64 / 72 (LENGTH: frame offsets off sp0 read on the
   listing), 104 / 116 / 136 / 164 (DERIVED: 4 * the slot inside the function), 16 (LENGTH: cf_head at
   CfParams_preset), 33 / 2 ^ 46 / 2 ^ 47 (DERIVED: the engine's atom numbering, the stack atom's range), 1 / 2 (COUNT:
   the lengths of caw_ev1 / caw_evs). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfHeadSh YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YGcfRoom.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require H2CawPure S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seat kit (Caw102A_Kit.v's Section bld, ported to the B listing; prefix wb2_) ---- *)
Fixpoint wb2_fchunks (k : nat) (offs : list (Z * N)) : list YP09.chunk :=
  match offs with
  | [] => []
  | (o, w) :: r => YP09.mkChunk o (CVal w (SOff k 0)) :: wb2_fchunks (S k) r
  end.
Definition wb2_fregion (offs : list (Z * N)) (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (- CAWB_FRAME) 0 wlo whi (wb2_fchunks 33 offs).
Definition wb2_sr80 : list sv := sr_set sr_atoms 2%bv (SOff 2 (- CAWB_FRAME)).
Definition wb2_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

Section bld. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGSz := (@pa_segs _ B_prog_listing PA).
#[local] Notation VALz := (@pa_val _ B_prog_listing PA).
#[local] Notation BASEz := (@pa_val _ B_prog_listing PA A_TEXT).
Fixpoint wb2_vals_ok (m : word -> option byte) (sp : Z) (offs : list (Z * N)) (vals : list Z) : Prop :=
  match offs, vals with
  | [], [] => True
  | (o, w) :: r, v :: vs =>
      val_mem SEGSz m (sp + o) (N.to_nat w) v /\ 0 <= v < 2 ^ (8 * Z.of_N w) /\ Z.of_N w <= 8 /\
      wb2_vals_ok m sp r vs
  | _, _ => False
  end.
Definition wb2_E (regs : bvmap 5 word) (sp0 : Z) (vals : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))).
Lemma wb2_fchunks_ok : forall E m sp offs vals k,
  (forall i, (i < length offs)%nat -> ew E (k + i) = Z_to_bv 64 (nth i vals 0)) ->
  wb2_vals_ok m sp offs vals -> Forall (YP09.chunk_ok SEGSz E m sp) (wb2_fchunks k offs).
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
Lemma wb2_getr_upd_other : forall regs (r r' : bv 5) w, r' <> r -> getr (regupd regs r w) r' = getr regs r'.
Proof.
intros regs r r' w Hne. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other by (intros Heq; apply Hne; symmetry; exact Heq). reflexivity.
Qed.
Lemma wb2_getr_upd_same : forall regs (r : bv 5) w, bv_eqb r 0 = false -> getr (regupd regs r w) r = w.
Proof. intros regs r w H. unfold getr, regupd. rewrite H. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma wb2_E_reg : forall regs sp0 vals n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv ->
  ew (wb2_E regs sp0 vals) n = getr regs r.
Proof.
intros regs sp0 vals n r Hn Hr. pose proof (u5_range r) as Hu. unfold wb2_E.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat _ _ n r Hn).
apply wb2_getr_upd_other. exact Hr.
Qed.
Lemma wb2_E_sp : forall regs sp0 vals, ew (wb2_E regs sp0 vals) 2 = Z_to_bv 64 sp0.
Proof.
intros regs sp0 vals. unfold wb2_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). apply wb2_getr_upd_same. reflexivity.
Qed.
Lemma wb2_E_val : forall regs sp0 vals i, (i < 200)%nat -> ew (wb2_E regs sp0 vals) (33 + i) = Z_to_bv 64 (nth i vals 0).
Proof.
intros regs sp0 vals i Hi. unfold wb2_E. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (33 + i)%nat with (32 + S i)%nat by lia. rewrite ew_Ereg_extra.
change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma wb2_regs_ok : forall regs sp0 vals, spZ regs = sp0 - CAWB_FRAME -> CAWB_FRAME <= sp0 < 2 ^ 64 ->
  regs_ok (wb2_E regs sp0 vals) wb2_sr80 regs.
Proof.
intros regs sp0 vals Hsp Hsp0 r'.
pose proof (regs_ok_Eimg_Ereg (L := B_prog_listing) (PI := PA) (regupd regs 2%bv (Z_to_bv 64 sp0))
  (map (Z_to_bv 64) (SHADOW_OFF :: vals)) r') as H.
fold (wb2_E regs sp0 vals) in H.
unfold wb2_sr80, sr_set. change (bv_eqb 2%bv 0%bv) with false. cbv iota.
unfold getr, regupd, sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact H|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx 2%bv)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'.
  cbn [sv_denot]. rewrite wb2_E_sp. unfold spZ in Hsp. unfold CAWB_FRAME in *.
  rewrite unsigned_lit_small by lia.
  unfold getr in Hsp. change (bv_eqb 2%bv 0%bv) with false in Hsp. cbv iota in Hsp.
  apply bv_eq. rewrite unsigned_lit_small by lia. lia.
- apply Nat.eqb_neq in Hi.
  unfold reg_get in *. rewrite bvmap_get_set_other in H by (intros Heq; apply Hi; rewrite Heq; reflexivity).
  exact H.
Qed.
Lemma wb2_st_ok : forall (W : world SEGSz) regs mem pc sp0 offs vals wlo whi G,
  regions_wf [wb2_fregion offs wlo whi] = true -> (length offs <= 100)%nat ->
  spZ regs = sp0 - CAWB_FRAME -> CAWB_FRAME <= sp0 < 2 ^ 64 ->
  (forall o, wlo <= o < whi -> writable_at SEGSz (mrestrict (w_H W) mem) (sp0 + o)) ->
  wb2_vals_ok (mrestrict (w_H W) mem) sp0 offs vals ->
  facts_ok (wb2_E regs sp0 vals) G ->
  st_ok_pi SEGSz VALz (wb2_E regs sp0 vals) (mkSS pc wb2_sr80 [wb2_fregion offs wlo whi] None G)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASEz + pc)) mem (YK11.seg_rom SEGSz))).
Proof.
intros W regs mem pc sp0 offs vals wlo whi G Hwf Hlen Hsp Hsp0 Hwr Hvals HG.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact (wb2_regs_ok regs sp0 vals Hsp Hsp0).
- exact Hwf.
- assert (Hb : base_val (wb2_E regs sp0 vals) (Some 2%nat) = sp0)
    by (cbn [base_val]; rewrite wb2_E_sp; apply unsigned_lit_small; unfold CAWB_FRAME in *; lia).
  constructor; [|constructor]. unfold region_ok, wb2_fregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
  split; [unfold CAWB_FRAME in *; lia|]. split; [lia|]. split; [exact Hwr|].
  apply (wb2_fchunks_ok _ _ _ offs vals 33); [| exact Hvals].
  intros i Hi. apply wb2_E_val. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
Lemma wb2_E_agree : forall regs sp0 vals,
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) (wb2_E regs sp0 vals).
Proof. intros regs sp0 vals. unfold wb2_E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
End bld.

(* a register of a stage's machine state, read off its symbolic state with the symbolic value computed *)
Ltac wb2_reg HS r H :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) => pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) => pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H
  end;
  lazymatch type of H with context [sr_get ?srs ?rr] =>
    let e := eval vm_compute in (sr_get srs rr) in change (sr_get srs rr) with e in H end.
Ltac wb2_inbv := repeat (first [left; apply bv_eq; reflexivity | right]).
(* acallee_saved of a register literal *)
Ltac wb2_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?b] => let n := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with n end;
  lia.

(* the two return slots are listing slots (closed: the engine's table, computed once here, never inside the walk) *)
Lemma wb2_slot104 : match plookup (@pl_tpi _ PL_caw_B) (AF_cawB + 104) with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wb2_slot116 : match plookup (@pl_tpi _ PL_caw_B) (AF_cawB + 116) with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

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
Hypothesis TEXV : forall fz : YK11.FPState, tex_value_specX (fx := fz) B ARcfx SK DOC_D.
(* the free row under the re-hide, with the memnorm keep at the leaf (YGcfMallocComposeKeep.v), at every float state *)
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
Hypothesis PAL : PALib B.
Hypothesis Hpst : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis Hpst_img : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
Hypothesis Hpst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
Hypothesis Hret_free : In (BASE + (AF_cawB + 116)) (pi_ret_sites F_check_as_written RT_free).
(* the cf layer's relro rows at the image (what arodata_ok_cf, the free's call memory premise, asks; discharged at the
   image as the four image facts above are, lib/AU/CfAroPresetB.v) *)
Hypothesis Hrelro_seg : YG0ncf.relro_seg_t SEGS.
Hypothesis Herrno_relro : YG0ncf.errno_relro_t B.
Hypothesis Hrelro_top : cf_relro_hi <= 2 ^ 64.
Hypothesis Hrelro_eq : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA.
Hypothesis Hro_reads_nw : YGcfAroBridge.ro_reads_nw_t SEGS.
(* the world relation past a free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* an SRr run whose post is an SRrG fact at RW is an SRrG run at RW (wle is inside RW) *)
Lemma wb2_lift : forall W c (Q : world SEGS -> config -> Prop),
  SRr SEGS W c (fun W' c' => YA0nH.SRrG SEGS RW W' c' Q) -> YA0nH.SRrG SEGS RW W c Q.
Proof.
intros W c Q H.
apply (YA0nH.SRrG_bind SEGS RW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W c _ Q
  (YA0nH.SRr_SRrG SEGS RW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) W c _ H)).
intros W' c' _ H'. exact H'.
Qed.

(* ---- small facts ---- *)
Lemma wb2_le_byte0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l. reflexivity. Qed.
Lemma wb2_vm0_4 : forall m a, val_mem SEGS m a 8 0 -> val_mem SEGS m a 4 0.
Proof. intros m a H kk Hk. rewrite (H kk ltac:(lia)), !wb2_le_byte0. reflexivity. Qed.
Lemma wb2_denot_w : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma wb2_denot_sp : forall E sp0 o, ew E 2 = Z_to_bv 64 sp0 -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + o < 2 ^ 64 ->
  sv_denot E (SOff 2 o) = Z_to_bv 64 (sp0 + o).
Proof.
intros E sp0 o HE H1 H2. apply bv_eq. rewrite denot_SOff, HE, !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma wb2_count_cid : forall c l, count_cid c l <= Z.of_nat (length l).
Proof. intros c l. induction l as [|[c0 p0] l IH]; cbn [count_cid length]; [lia|]. destruct (c0 =? c); lia. Qed.
(* the live class-24 count past a step that adds the blocks l to a state's (the scratch's malloc, caw_scr): ccnt24
   counts the requests ablocks lists (YGcfRoomLive.v, YG0d.ablocks), so it grows by at most
   length l; from caw_cnt C (the text's room counts at the entry state, Caw102B.caw_pre_cnt) it bounds RL_free_step's
   count (the A' twin: Caw102A_WA2.v f4334a4d9ca1, wa2_ccnt24_app) *)
Lemma wb2_filter_app_len : forall (f : Z -> bool) (l1 : list Z) (l2 : list (Z * Z)),
  Z.of_nat (length (List.filter f (l1 ++ map snd l2))) <= Z.of_nat (length (List.filter f l1)) + Z.of_nat (length l2).
Proof.
intros f l1 l2. rewrite filter_app, length_app, Nat2Z.inj_add.
assert (H : (length (List.filter f (map snd l2)) <= length l2)%nat).
{ clear l1. induction l2 as [|x t IH]; [cbn; lia|]. cbn [map List.filter]. destruct (f (snd x)); cbn [length]; lia. }
lia.
Qed.
Lemma wb2_ccnt24_app : forall ly S ly0 S0 l, ablocks B ly S = ablocks B ly0 S0 ++ l ->
  YGcfRoomLive.ccnt24 S <= YGcfRoomLive.ccnt24 S0 + Z.of_nat (length l).
Proof.
intros ly S ly0 S0 l E.
assert (Hm : forall ly' S', map snd (ablocks B ly' S') = map snd (YG01.blocks S')).
{ intros ly' S'. unfold ablocks. rewrite map_map. reflexivity. }
apply (f_equal (map snd)) in E. rewrite map_app, !Hm in E.
unfold YGcfRoomLive.ccnt24, PresetRoom.ccnt. rewrite E. apply wb2_filter_app_len.
Qed.
Lemma wb2_w64_neg : forall z, - 2 ^ 31 <= z < 0 -> bv_unsigned (w64 z) = z + 2 ^ 64.
Proof.
intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite <- (Z.mod_small (z + 2 ^ 64) (2 ^ 64)) by lia. rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.
Lemma wb2_w64_nn : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
(* the empty chain from s0 = rc (an int) *)
Lemma wb2_achain0 : forall ly rd sp (regs : bvmap 5 word) rc0, getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  ly_top ly <= 2 ^ 47 -> achain ly rd sp (s0Z regs) [].
Proof.
intros ly rd sp regs rc0 Hs0 Hrc Htop. left. split; [|reflexivity]. pose proof asan_consts as (C1 & _).
unfold s0Z. rewrite Hs0.
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- left. rewrite wb2_w64_nn by lia. lia.
- right. left. rewrite wb2_w64_neg by lia. lia.
Qed.
(* a1 = (rc == 0 ? doc : 0), B' 0x81fc4-0x81fcc *)
Lemma wb2_a1 : forall E rc0 doc0, ew E 8 = w64 rc0 -> ew E 9 = w64 doc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 -> 0 <= doc0 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 8 0)) (SLit (-1))) (SOff 9 0)) =
  w64 (if rc0 =? 0 then doc0 else 0).
Proof.
intros E rc0 doc0 H8 H9 Hrc Hdoc. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !U_SAlu, !U_SOff, !U_SLit, H8, H9. cbn [zalu_raw]. rewrite !Z.add_0_r.
assert (Ed : zcanon (bv_unsigned (w64 doc0)) = doc0) by (rewrite wb2_w64_nn by lia; apply zcanon_id; unfold M64; lia).
assert (Em : zcanon (-1) = 2 ^ 64 - 1) by reflexivity.
assert (E0 : zcanon 0 = 0) by reflexivity.
rewrite Ed, Em, E0.
destruct (Z.eqb_spec rc0 0) as [-> | Hne].
- replace (zcanon (bv_unsigned (w64 0))) with 0 by reflexivity. cbn [Z.ltb Z.compare]. rewrite Z.add_0_l.
  rewrite (zcanon_id (2 ^ 64 - 1)) by (unfold M64; lia).
  replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.land_comm, Z.land_ones by lia.
  rewrite (Z.mod_small doc0) by lia. apply zcanon_id. unfold M64. lia.
- assert (Epos : 0 < zcanon (bv_unsigned (w64 rc0))).
  { destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
    - rewrite wb2_w64_nn by lia. rewrite zcanon_id by (unfold M64; lia). lia.
    - rewrite wb2_w64_neg by lia. unfold zcanon, M64.
      rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. lia. }
  destruct (Z.ltb_spec 0 (zcanon (bv_unsigned (w64 rc0)))) as [_ | X]; [|lia].
  replace (zcanon (1 + (2 ^ 64 - 1))) with 0 by reflexivity. rewrite Z.land_0_l. reflexivity.
Qed.

(* ---- the scratch block ---- *)
Lemma wb2_scr_blk : forall C ly3 S3 Hp3 W3 mem3 md3 scr, ARcfx ly3 S3 Hp3 W3 mem3 md3 -> caw_scr B C ly3 S3 scr ->
  0 <= c_size C ->
  In (scr, c_size C + 1) (ablocks B ly3 S3) /\ scr mod 16 = 0 /\ 4096 <= scr /\ scr + (c_size C + 1) <= YM05.alloc_ceiling /\
  in_app scr (c_size C + 1) /\
  (forall a, scr <= a < scr + (c_size C + 1) -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a).
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 scr HAR (Hs4 & E) Hn.
assert (Hin : In (scr, c_size C + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (H16 & H4 & Hc & Ha & Hp & _).
rewrite caw_req in Hc, Ha, Hp by lia. split; [exact Hin|]. split; [exact H16|]. split; [exact H4|]. split; [exact Hc|].
split; [exact Ha | exact Hp].
Qed.

(* two different blocks of a state are apart *)
Lemma wb2_blk_disj : forall ly S Hp W mem md p n q m, ARcfx ly S Hp W mem md ->
  In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
  p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S Hp W mem md p n q m HAR H1 H2 Hne.
pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md p n q m HAR H1 H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

(* a head of Hp is a block base, of a block of size at least cf_head *)
Lemma wb2_head_blk : forall ly S Hp W mem Lam peak cnt fail ran most own h,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> In h Hp ->
  exists k, 0 <= k /\ In (h, k + cf_head) (ablocks B ly S).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own h HL Hh.
pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HL) as HP.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Ea & HinL). cbn [fst] in Ea. subst h.
destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a k HL HinL) as (Hk0 & Hab & _). exists k. split; [exact Hk0 | exact Hab].
Qed.

(* the shadow of a window inside a live block: addressable, its hull visible *)
Lemma wb2_blk_shadow : forall ly S Hp W mem md Lam peak cnt fail ran most own b m a n,
  ARcfx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> b <= a -> a + n <= b + m -> 0 < n -> (In b Hp -> b + cf_head <= a) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m a n HAR HL Hin Hba Han Hn Hhd.
assert (Hm : req_size m = m) by (apply caw_req; lia).
change (@cf_head CfParams_preset) with 16 in *.
destruct (in_dec Z.eq_dec b Hp) as [Hb | Hb].
- specialize (Hhd Hb).
  destruct (alx_hshadow SEGS B ARcfx LAWS ly S Hp W mem md b m HAR Hin Hb) as [Hbs Hhv].
  change (@cf_head CfParams_preset) with 16 in Hbs, Hhv. rewrite Hm in Hbs, Hhv.
  split.
  + apply (block_shadow_range _ SHADOW_OFF (b + 16) (m - 16) a n Hbs); lia.
  + apply (YGcfHeadSh.shadow_hull_vis_sub_cf _ (b + 16) (m - 16) a n); [apply Hhv; lia | lia | lia].
- assert (Hno : forall h, In h Hp -> ~ (b <= h < b + req_size m)).
  { intros h Hh Hr. destruct (wb2_head_blk ly S Hp W mem Lam peak cnt fail ran most own h HL Hh) as (k & Hk0 & Hk).
    change (@cf_head CfParams_preset) with 16 in Hk.
    destruct (Z.eq_dec h b) as [-> | Hne]; [exact (Hb Hh)|].
    pose proof (wb2_blk_disj ly S Hp W mem md b m h (k + 16) HAR Hin Hk ltac:(congruence)) as D.
    rewrite (caw_req (k + 16)) in D by lia. lia. }
  destruct (alx_shadow SEGS B ARcfx LAWS ly S Hp W mem md b m HAR Hin Hno) as [Hbs Hhv]. rewrite Hm in Hbs, Hhv.
  split.
  + apply (block_shadow_range _ SHADOW_OFF b m a n Hbs); lia.
  + apply (YGcfHeadSh.shadow_hull_vis_sub_cf _ b m a n Hhv); lia.
Qed.

(* the scratch's base is no harness head *)
Lemma wb2_scr_not_hp : forall C ly3 S3 Hp3 W3 mem3 md3 scr, caw_pre (fx := fx) B C -> ARcfx ly3 S3 Hp3 W3 mem3 md3 ->
  caw_scr B C ly3 S3 scr -> ~ In scr (c_Hp C).
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 scr Hpre HAR Hscr Hin.
pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL.
assert (Hn0 : 0 <= c_size C) by (unfold c_size; lia).
pose proof (caw_scr_new B C ly3 S3 Hp3 W3 mem3 md3 scr HAR Hscr Hn0) as Hnew.
destruct (wb2_head_blk _ _ _ _ _ _ _ _ _ _ _ _ scr HL Hin) as (k & Hk0 & Hab).
change (@cf_head CfParams_preset) with 16 in Hab.
destruct Hscr as (H4 & E).
assert (Hin1 : In (scr, k + 16) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; left; exact Hab).
assert (Hin2 : In (scr, c_size C + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (Z.eq_dec (k + 16) (c_size C + 1)) as [Eq | Ne].
- apply Hnew. rewrite <- Eq. exact Hab.
- assert (Ne' : (scr, k + 16) <> (scr, c_size C + 1)) by (intros X; injection X; lia).
  pose proof (wb2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR Hin1 Hin2 Ne') as D. rewrite !caw_req in D by lia. lia.
Qed.

(* a listing slot's pc is in the image, so at or above the image's low end (the call's 4096 <= ra) *)
Lemma wb2_slot_lo : forall ly S Hp W mem md k, ARcfx ly S Hp W mem md -> 0 <= k < 2 ^ 40 ->
  match plookup (@pl_tpi _ PL_caw_B) k with Some _ => true | None => false end = true ->
  kImgLo <= BASE + k.
Proof.
intros ly S Hp W mem md k HAR Hk H. destruct (plookup (@pl_tpi _ PL_caw_B) k) as [e|] eqn:He; [|discriminate H].
pose proof (@pa_B_ok _ _ PA) as HB. rewrite <- (@pl_tpi_eq _ PL_caw_B) in He.
pose proof (cert_slot asym (clookup (@pa_tbl _ _ PA)) (@pa_val _ _ PA) (@pa_sigma _ _ PA) B_prog_listing (@pa_cert _ _ PA) k e He)
  as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup (@pa_tbl _ _ PA) (BASE + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (@pa_tbl_ok _ _ PA _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (BASE + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
rewrite unsigned_lit_small in Hlo by lia.
destruct (alx_img SEGS B ARcfx LAWS ly S Hp W mem md HAR) as [Hsg _].
destruct (Hsg sg Hin) as [Hs1 _].
pose proof (alx_layout_ok SEGS B ARcfx LAWS ly S Hp W mem md HAR) as LO.
destruct (lo_img _ LO) as (Hli & _).
lia.
Qed.

(* the read-only view at any state the journal from entry reaches (the fpre's second conjunct at a call) *)
Lemma wb2_rod : forall C ly3 S3 Hp3 W3 mem3 md3 k, caw_pre (fx := fx) B C -> caw_J B C ly3 S3 Hp3 W3 mem3 md3 k ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W3) mem3).
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 k Hpre HJ a Hro Hown Herr.
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as [_ [HROD _]].
unfold caw_J in HJ. pose proof (ajx_img HJ) as F3.
assert (Himg : in_img SEGS a).
{ destruct Hro as [(s & Hs & _ & Hr) | Hr].
  - exists s. split; [exact Hs | exact Hr].
  - exact (@pa_relro_img _ _ PA a Hr). }
rewrite (F3 a Himg Hown Herr).
- exact (HROD a Hro Hown Herr).
- intros Hp. exact (Hpst_rw a Hp Hro).
- apply fp_spares_closed. intros (r & Hr & _). destruct Hr.
Qed.

(* the text's window at any state the journal from entry reaches with entry's blocks live (tex_value_specX's src_rd) *)
Lemma wb2_src_rd : forall C ly3 S3 Hp3 W3 mem3 md3 k Lam' peak' cnt' fail' ran' most' own',
  caw_pre (fx := fx) B C -> caw_J B C ly3 S3 Hp3 W3 mem3 md3 k ->
  (forall x, In x (ablocks B (c_ly C) (c_S C)) -> In x (ablocks B ly3 S3)) -> Hp3 = c_Hp C ->
  LEDGER ly3 S3 Hp3 W3 mem3 Lam' peak' cnt' fail' ran' most' own' ->
  src_rd W3 mem3 (c_data C) (c_x C).
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 k Lam' peak' cnt' fail' ran' most' own' Hpre HJ Hbl EHp HL.
unfold caw_J in HJ.
pose proof (caw_pre_src (fx := fx) B C Hpre) as HSRC. pose proof (caw_pre_inblk (fx := fx) B C Hpre) as HINB.
pose proof HSRC as (_ & H4 & Hceil & Hamr & _).
destruct (caw_J_keep B C ly3 S3 Hp3 W3 mem3 md3 k Hpre HJ Hbl) as [Hbytes _].
split; [exact Hbytes|]. split; [exact H4|]. split; [exact Hceil|]. split; [exact Hamr|].
destruct (Z_le_gt_dec (Z.of_nat (length (c_x C))) 0) as [H0 | H0].
- split; [apply range_addressable_nil; exact H0 | intros; lia].
- destruct (HINB ltac:(unfold c_size; lia)) as (b & m & Hin & Hb & Hm & Hhd).
  destruct (wb2_blk_shadow ly3 S3 Hp3 W3 mem3 md3 Lam' peak' cnt' fail' ran' most' own' b m (c_data C)
    (Z.of_nat (length (c_x C)))
    (ajx_ar HJ) HL (Hbl _ Hin) Hb Hm ltac:(lia) ltac:(rewrite EHp; exact Hhd)) as [HR HV].
  split; [exact HR | intros _; exact HV].
Qed.

(* the scratch as a write destination of a callee whose window lies on the stack *)
Lemma wb2_wdest_scr : forall C ly S Hp W regs mem md Lam' peak' cnt' fail' ran' most' own' scr STK1,
  ARcfx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam' peak' cnt' fail' ran' most' own' ->
  caw_scr B C ly S scr -> ~ In scr Hp -> YM05.alloc_ceiling <= spZ regs - STK1 ->
  wdest_ok B STK1 ly S W regs mem scr (c_size C + 1).
Proof.
intros C ly S Hp W regs mem md Lam' peak' cnt' fail' ran' most' own' scr STK1 HAR HL Hscr Hnhp Hsp.
assert (Hsz0 : 0 <= c_size C) by (unfold c_size; lia).
destruct (wb2_scr_blk C ly S Hp W mem md scr HAR Hscr Hsz0) as (Hin & H16 & H4 & Hc & Ha & Hpa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wb2_blk_shadow ly S Hp W mem md Lam' peak' cnt' fail' ran' most' own' scr (c_size C + 1) scr (c_size C + 1)
  HAR HL Hin ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros X; exfalso; exact (Hnhp X))) as [HR HV].
split; [lia|]. split; [exact Hc|].
split.
{ unfold amem_range. destruct Ha as (_ & [Ha | (Ha1 & Ha2)]).
  - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
  - right. split; [exact Ha1|]. pose proof (@ASAN_CEIL_range rc) as [AC _]. unfold ASAN_CEIL in *. lia. }
split.
{ intros a Ha'. destruct (Hpa a Ha') as [Hpr Hno]. split; [apply (apresent_writable SEGS); exact Hpr|].
  split; [exact Hno | lia]. }
split; [exact HR | intros _; exact HV].
Qed.

(* the text and the scratch are apart *)
Lemma wb2_apart_x : forall C ly3 S3 Hp3 W3 mem3 md3 scr, caw_pre (fx := fx) B C -> ARcfx ly3 S3 Hp3 W3 mem3 md3 ->
  caw_scr B C ly3 S3 scr ->
  scr + c_size C + 1 <= c_data C \/ c_data C + c_size C <= scr.
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 scr Hpre HAR Hscr.
pose proof (caw_pre_inblk (fx := fx) B C Hpre) as HINB.
assert (Hsz0 : 0 <= c_size C) by (unfold c_size; lia).
destruct (Z.eq_dec (c_size C) 0) as [H0 | H0]; [lia|].
destruct (HINB ltac:(lia)) as (b & m & Hin & Hb & Hm & _).
pose proof (caw_scr_new B C ly3 S3 Hp3 W3 mem3 md3 scr HAR Hscr Hsz0) as Hnew.
pose proof Hscr as (_ & Eab).
assert (Hin3 : In (b, m) (ablocks B ly3 S3)) by (rewrite Eab; apply in_or_app; left; exact Hin).
assert (Hin2 : In (scr, c_size C + 1) (ablocks B ly3 S3)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Ne : (b, m) <> (scr, c_size C + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hin).
pose proof (wb2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR Hin3 Hin2 Ne) as D.
rewrite (caw_req m) in D by lia. rewrite (caw_req (c_size C + 1)) in D by lia. lia.
Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* rc = 0: the tree at doc as tex_value_specX's v arm asks it at a state the journal from entry reaches (the root in an
   entry fake frame, its blocks harness blocks of entry), apart from the scratch, the struct, the callee's window and
   errno; doc is not NULL *)
Lemma wb2_tree : forall C ly3 S3 Hp3 W3 (regs : bvmap 5 word) mem3 md3 k scr STK1,
  caw_pre (fx := fx) B C -> caw_J B C ly3 S3 Hp3 W3 mem3 md3 k -> caw_scr B C ly3 S3 scr ->
  YM05.alloc_ceiling <= spZ regs - STK1 -> YM05.alloc_ceiling <= c_sp C - 72 -> c_rc C = 0 ->
  prhex_tree ly3 S3 (c_Lam C) W3 regs mem3 (c_doc C) (c_t C) (c_D C) /\ Forall (fun ak => 0 < fst ak) (c_D C) /\
  (forall z, pj_footR (c_doc C) (c_D C) z ->
     ~ (scr <= z < scr + c_size C + 1) /\ ~ (c_sp C - 72 <= z < c_sp C - 72 + 40) /\
     ~ (spZ regs - STK1 <= z < spZ regs) /\ ~ (as_errno B <= z < as_errno B + 4)) /\
  c_doc C <> 0.
Proof.
intros C ly3 S3 Hp3 W3 regs mem3 md3 k scr STK1 Hpre HJ Hscr Hwin Hq Hrc0.
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as [HPRE _]. pose proof (caw_pre_tree (fx := fx) B C Hpre) as HTREE.
pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL.
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (HTREE Hrc0) as (HN & HDL & _ & (Hal & (cid & pos & Hfin & Hf1 & Hf2) & HRA)).
unfold caw_J in HJ.
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hly3. pose proof (ajx_frs HJ) as Hfrs3.
pose proof (ajx_frm HJ) as F4.
cbn [app] in Hfrs3.
pose proof Hscr as (Hs4 & Eab).
assert (Hsz0 : 0 <= c_size C) by (unfold c_size; lia).
assert (Hbl : forall x, In x (ablocks B (c_ly C) (c_S C)) -> In x (ablocks B ly3 S3))
  by (intros x Hx; rewrite Eab; apply in_or_app; left; exact Hx).
destruct (caw_J_keep B C ly3 S3 Hp3 W3 mem3 md3 k Hpre HJ Hbl) as [_ Hnode]. specialize (Hnode Hrc0).
destruct (alx_layout SEGS B ARcfx LAWS _ _ _ _ _ _ ly3 HAR Hly3) as (_ & Efr & _).
assert (Hfin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; exact Hfin).
destruct (alx_frames SEGS B ARcfx LAWS _ _ _ _ _ _ cid pos HAR3 Hfin3) as (_ & Happ & _ & Hsh).
destruct (YG0scf.frame_facts_cf B ly3 S3 Hp3 _ cid pos (proj1 (proj1 HAR3)) Hfin3)
  as (Hcid & Hpos & _ & _ & Hpg & _ & _ & Hoff64 & Hfs64 & Hfs64m & _).
rewrite <- (Efr cid pos) in Hf1, Hf2.
assert (Hf64 : frame_addr ly3 cid pos mod 64 = 0).
{ unfold frame_addr, page_aligned in *. rewrite Z.add_mod, Hoff64, Z.add_0_r, Z.mod_mod by lia.
  replace (ly_F ly3) with (64 * (ly_F ly3 / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly3) 4096 ltac:(lia)); lia).
  rewrite Z.mul_comm. apply Z_mod_mult. }
set (f := frame_addr ly3 cid pos) in *. set (fs := fs_frame_bytes cid) in *.
assert (Ef : f = frame_addr ly3 cid pos) by reflexivity. assert (Efs : fs = fs_frame_bytes cid) by reflexivity.
assert (Hfapp : 4096 <= f /\ f + fs <= YM05.alloc_ceiling).
{ destruct Happ as (Ha4 & [Ha | (Ha1 & Ha2)]); [unfold kLowShadowBeg in Ha; lia|].
  unfold ASAN_CEIL in Ha2. lia. }
(* the root's footprint is a frame's: apart from blocks, below the ceiling, outside the image *)
assert (Hroot : forall z, c_doc C <= z < c_doc C + 56 ->
  ~ (scr <= z < scr + c_size C + 1) /\ ~ (c_sp C - 72 <= z < c_sp C - 72 + 40) /\
  ~ (spZ regs - STK1 <= z < spZ regs) /\ ~ (as_errno B <= z < as_errno B + 4)).
{ intros z Hz.
  destruct (in_split _ _ Hfin3) as (fr1 & fr2 & Efrs).
  pose proof (proj1 (alx_sep SEGS B ARcfx LAWS _ _ _ _ _ _ HAR3)) as Hsep.
  assert (D : zdisjoint (scr, req_size (c_size C + 1)) (f, fs)).
  { apply (pairwise_In2 zdisjoint _ _ _ (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B (c_ly C) (c_S C)))
      (map (fun f0 : Z * Z => (frame_addr ly3 (fst f0) (snd f0), fs_frame_bytes (fst f0))) fr1)
      (map (fun f0 : Z * Z => (frame_addr ly3 (fst f0) (snd f0), fs_frame_bytes (fst f0))) fr2) Hsep).
    rewrite Eab, Efrs, !map_app. cbn [map fst snd]. rewrite <- app_assoc. reflexivity. }
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite caw_req in D by lia.
  split; [lia|]. split; [lia|]. split; [lia|].
  assert (Hzf : exists cid0 pos0, In (cid0, pos0) (frames S3) /\
    frame_addr ly3 cid0 pos0 <= z < frame_addr ly3 cid0 pos0 + fs_frame_bytes cid0)
    by (exists cid, pos; split; [exact Hfin3 | rewrite <- Ef, <- Efs; lia]).
  intros Hze. apply (proj2 (alx_client_img SEGS B ARcfx LAWS _ _ _ _ _ _ z HAR3 (or_intror (or_introl Hzf)))).
  exact (proj1 (proj2 (pal_env B PAL)) z Hze). }
split; [|split; [|split]].
- split; [exact Hnode|]. split.
  { right. left. exists cid, pos. split; [exact Hfin3|]. rewrite <- ?Ef, <- ?Efs. lia. }
  split.
  + apply (range_addressable_agree (aview SEGS (w_H (c_W C)) (c_mem C))); [|exact HRA].
    intros x Hx. apply (F4 cid pos); [exact Hfin | | apply inFP_nil].
    right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. rewrite <- (Efr cid pos), <- ?Ef, <- ?Efs. lia.
  + intros s Hs. unfold shadow_addr in Hs.
    assert (Hi : 0 <= s - shadow_addr f < fs / 8) by (unfold shadow_addr, SHADOW_OFF in *; lia).
    destruct (Hsh (s - shadow_addr f) Hi) as [Hpr _]. replace s with (shadow_addr f + (s - shadow_addr f)) by lia.
    exact (aview_some_of_apresent SEGS _ _ _ Hpr).
- apply Forall_forall. intros [a kk] HinD. cbn [fst].
  destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL (HDL _ HinD)) as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & _). lia.
- intros z [Hz | ([a kk] & HinD & Hz)]; [exact (Hroot z Hz)|].
  unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
  destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL (HDL _ HinD)) as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  pose proof (caw_scr_new B C ly3 S3 Hp3 W3 mem3 md3 scr HAR3 Hscr Hsz0) as Hnew.
  assert (Hab3 : In (a - 16, kk + 16) (ablocks B ly3 S3)) by exact (Hbl _ Hab).
  assert (Hin2 : In (scr, c_size C + 1) (ablocks B ly3 S3)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  assert (Ne : (a - 16, kk + 16) <> (scr, c_size C + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hab).
  pose proof (wb2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR3 Hab3 Hin2 Ne) as D. rewrite !caw_req in D by lia.
  destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR3 Hab3) as (_ & H4 & Hc & _). rewrite caw_req in Hc by lia.
  split; [lia|]. split; [lia|]. split; [lia|].
  assert (Hzb : exists p0 n0, In (p0, n0) (ablocks B ly3 S3) /\ p0 <= z < p0 + req_size n0)
    by (exists (a - 16), (kk + 16); split; [exact Hab3 | rewrite caw_req by lia; lia]).
  intros Hze. apply (proj2 (alx_client_img SEGS B ARcfx LAWS _ _ _ _ _ _ z HAR3 (or_introl Hzb))).
  exact (proj1 (proj2 (pal_env B PAL)) z Hze).
- lia.
Qed.

(* a callee-saved register across a call *)
Lemma wb2_ap : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. specialize (H _ Hr). rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* the prologue's saves at a later memory that agrees on them *)
Lemma wb2_saved_move : forall C (W W' : world SEGS) mem mem',
  (forall a, c_sp C - 32 <= a < c_sp C -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  caw_saved C W mem -> caw_saved C W' mem'.
Proof.
intros C W W' mem mem' H (V1 & V2 & V3 & V4). unfold caw_saved.
split; [|split; [|split]]; (eapply (val_mem_kept SEGS); [|eassumption]); intros kk Hkk; apply H; lia.
Qed.

(* the ledger after the scratch's free: the free kept every other block's bytes and the image outside the runtime's
   own statics (so every prh_pst byte: g_most and g_own_ran_out among them); the heads of Lam lie in entry blocks, apart
   from the scratch (H2CawBase caw_ledger_free, by the ledger's projections) *)
Lemma wb2_ledger_free : forall C ly4 S4 Hp4 W4 mem4 md4 ly7 S7 W7 mem7 scr own,
  caw_pre (fx := fx) B C -> ARcfx ly4 S4 Hp4 W4 mem4 md4 -> caw_scr B C ly4 S4 scr ->
  LEDGER ly4 S4 Hp4 W4 mem4 (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) own ->
  ablocks B ly7 S7 = ablocks B (c_ly C) (c_S C) ->
  (forall b m i, In (b, m) (ablocks B ly4 S4) -> 0 <= i < req_size m -> ~ (scr <= b + i < scr + req_size (c_size C + 1)) ->
     aview SEGS (w_H W7) mem7 (b + i) = aview SEGS (w_H W4) mem4 (b + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ as_errno B <= a < as_errno B + 4 ->
     aview SEGS (w_H W7) mem7 a = aview SEGS (w_H W4) mem4 a) ->
  LEDGER ly7 S7 Hp4 W7 mem7 (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) own.
Proof.
intros C ly4 S4 Hp4 W4 mem4 md4 ly7 S7 W7 mem7 scr own Hpre HAR Hscr HL Eab K2 K3.
pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL0.
assert (Hn0 : 0 <= c_size C) by (unfold c_size; lia).
pose proof (caw_scr_new B C ly4 S4 Hp4 W4 mem4 md4 scr HAR Hscr Hn0) as Hnew.
destruct Hscr as (H4 & E3).
apply (S1Ledger.prh_ledger_kept_aview B ly4 S4 Hp4 W4 mem4 ly7 S7 Hp4 W7 mem7 _ _ _ _ _ _ _ HL).
- intros a Ha. destruct (Hpst a Ha) as [H1 H2]. apply K3; [exact (Hpst_img a Ha) | exact H1 | exact H2].
- intros a k i HinL Hi. change (@cf_head CfParams_preset) with 16.
  destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a k HL0 HinL) as (Hk0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  assert (Hab3 : In (a - 16, k + 16) (ablocks B ly4 S4)) by (rewrite E3; apply in_or_app; left; exact Hab).
  assert (Hin2 : In (scr, c_size C + 1) (ablocks B ly4 S4)) by (rewrite E3; apply in_or_app; right; left; reflexivity).
  assert (Ne : (a - 16, k + 16) <> (scr, c_size C + 1)) by (intros X; apply Hnew; rewrite <- X; exact Hab).
  pose proof (wb2_blk_disj _ _ _ _ _ _ _ _ _ _ HAR Hab3 Hin2 Ne) as D.
  rewrite (caw_req (k + 16)) in D by lia. rewrite (caw_req (c_size C + 1)) in D by lia.
  apply (K2 (a - 16) (k + 16) i Hab3); rewrite ?(caw_req (k + 16)) by lia; rewrite ?(caw_req (c_size C + 1)) by lia; lia.
- intros a k HinL _. destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a k HL0 HinL) as (Hk0 & Hab & _).
  rewrite Eab. exact Hab.
- apply Permutation_refl.
Qed.

(* the free's trace with the empty chain (s0 = rc), from the call-context closure at caw's free site *)
Lemma wb2_free_trace : forall C ly (regs : bvmap 5 word), caw_pre (fx := fx) B C -> raZ regs = BASE + (AF_cawB + 116) ->
  In (call_trace ly (pc_free_ra0 (as_code B)) regs []) (as_universe B).
Proof.
intros C ly regs Hpre Hra. pose proof (caw_pre_univ (fx := fx) B C Hpre) as HUNIV.
unfold call_trace. destruct (frame0_ok ly regs).
- replace (unwind_of_chain (pc_free_ra0 (as_code B)) [(spZ regs, raZ regs, s0Z regs)])
    with (prh_trace (prh_pc0 B RT_free) (raZ regs) []) by reflexivity.
  apply (prh_univ_closure_lit B (c_CTX0 C) F_check_as_written RT_free (raZ regs) HUNIV). rewrite Hra. exact Hret_free.
- exact (proj1 HUNIV RT_free).
Qed.

Lemma caw_WB2 : forall C P Q, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> srr_inv_mn SEGS P ->
  caw_pre (fx := fx) B C -> caw_cnt C -> caw_K_wsR (fx := fx) B RW C P Q -> caw_K_oAR (fx := fx) B RW C P Q ->
  caw_K_evR (fx := fx) B RW C P Q.
Proof.
intros C P Q PLAW PCALL PMN Hpre Hcnt Kws KoA fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr Hcut HPM.
pose proof Hcut as (Hbase & R9 & R18 & R10 & HEX3 & V56 & Hscr & Hfr3 & Hrp & HL3 & HHB3).
pose proof Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HRL3).
unfold caw_ledger in HL3.
(* caw_pre read BY NAME (the base's projections), in the order and under the names of the former pattern *)
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as [HPRE [HROD [HTOP [HRAZ HFRM0]]]].
pose proof (caw_pre_mn (fx := fx) B C Hpre) as HMN. pose proof (caw_pre_univ (fx := fx) B C Hpre) as HUNIV.
pose proof (caw_pre_r10 (fx := fx) B C Hpre) as H10. pose proof (caw_pre_r11 (fx := fx) B C Hpre) as H11.
pose proof (caw_pre_r12 (fx := fx) B C Hpre) as H12. pose proof (caw_pre_r13 (fx := fx) B C Hpre) as H13.
pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc. pose proof (caw_pre_doc (fx := fx) B C Hpre) as Hdoc.
pose proof (caw_pre_size (fx := fx) B C Hpre) as Hsz. pose proof (caw_pre_data0 (fx := fx) B C Hpre) as Hd0.
pose proof (caw_pre_data62 (fx := fx) B C Hpre) as Hd62. pose proof (caw_pre_src (fx := fx) B C Hpre) as HSRC.
pose proof (caw_pre_inblk (fx := fx) B C Hpre) as HINB. pose proof (caw_pre_case (fx := fx) B C Hpre) as HCASE.
pose proof (caw_pre_tree (fx := fx) B C Hpre) as HTREE. pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL0.
pose proof (caw_pre_ran (fx := fx) B C Hpre) as Hran0. pose proof (caw_pre_live (fx := fx) B C Hpre) as HLIVE.
pose proof (caw_pre_max (fx := fx) B C Hpre) as HMAX. pose proof (caw_pre_frames (fx := fx) B C Hpre) as HFR.
pose proof (caw_pre_room (fx := fx) B C Hpre) as HRL0. pose proof (caw_pre_frm0 (fx := fx) B C Hpre) as HFRM.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold caw_J in HJ.
(* the journal read BY NAME (YCbqG's ajx_ projections), never positionally *)
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hly3. pose proof (ajx_frs HJ) as Hfrs3.
pose proof (ajx_pres HJ) as Hpres3. pose proof (ajx_qt HJ) as HQT3.
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _ & _ & Etop3 & Eslo3 & Eshi3 & _).
lazymatch eval vm_compute in STK with ?n => assert (HSTK : STK = n) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in (STK_ex_value (PI := prh_img_B) DOC_D) with ?n =>
  assert (HSTKV : STK_ex_value (PI := prh_img_B) DOC_D = n) by (vm_compute; reflexivity) end.
lazymatch eval vm_compute in AF_cawB with ?n => assert (EAF : AF_cawB = n) by reflexivity end.
pose proof (@pa_B_ok _ _ PA) as HBok.
assert (Hsz0 : 0 <= c_size C) by (unfold c_size; lia).
set (sp0 := c_sp C) in *.
assert (Rsp : 2 ^ 46 <= sp0 <= 2 ^ 47) by (unfold sp0, c_sp; lia).
assert (Hsp016 : sp0 mod 16 = 0) by exact Hal16.
destruct (wb2_scr_blk C ly3 S3 Hp3 W3 mem3 md3 scr (ajx_ar HJ) Hscr Hsz0) as (Hscrb & Hs16 & Hs4096 & Hsceil & Hsapp & Hspres).
pose (E := wb2_E regs3 sp0 []).
assert (E2 : ew E 2 = Z_to_bv 64 sp0) by (subst E; apply wb2_E_sp).
assert (EregE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv -> ew E n = getr regs3 r)
  by (intros n r Hn Hr; subst E; exact (wb2_E_reg regs3 _ [] n r Hn Hr)).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E (mkSS (AF_cawB + CAWB_EV) wb2_sr80 [wb2_fregion [] (-48) (-32)] None wb2_facts)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (AF_cawB + CAWB_EV))) mem3 (YK11.seg_rom SEGS)))).
{ apply wb2_st_ok.
  - vm_compute. reflexivity.
  - cbn. lia.
  - exact Hsp.
  - unfold CAWB_FRAME. lia.
  - intros o Ho. apply (apresent_writable SEGS). apply Hpres3. rewrite HSTK. lia.
  - exact I.
  - unfold facts_ok, wb2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    first [rewrite E2 | rewrite wb2_E_sp]. rewrite unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp016 | lia]. }
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wb2_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := @paj_run_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
apply wb2_lift.
unfold caw_cfg.
(* ---- +76 .. +100: a1 = (rc == 0 ? doc : 0), the scratch and 0 into the struct, a0 = q, jal ex_value ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi wb2_fregion base_val] in Hr. rewrite E2, unsigned_lit_small in Hr by lia.
  left. rewrite HSTK. lia. }
(* ---- the call state ---- *)
clear HG.
assert (Esp0 : sp0 = spZ (c_regs C)) by reflexivity.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0 - 32) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi wb2_fregion base_val] in Hr. rewrite E2, unsigned_lit_small in Hr by lia. lia. }
clear HF HFr.
wb2_reg HS (1%bv : bv 5) R1c. wb2_reg HS (2%bv : bv 5) R2c. wb2_reg HS (3%bv : bv 5) R3c.
wb2_reg HS (4%bv : bv 5) R4c. wb2_reg HS (8%bv : bv 5) R8c. wb2_reg HS (10%bv : bv 5) R10c.
wb2_reg HS (11%bv : bv 5) R11c.
assert (Hra1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_cawB + 104)))
  by (rewrite R1c, <- (codeptr_val (PI := PA) E (AF_cawB + 104) HEI), EAF; reflexivity).
assert (Hsp1 : spZ (ms_regs ms) = sp0 + -80)
  by (unfold spZ; rewrite R2c, (wb2_denot_sp E sp0 (-80) E2) by lia; apply unsigned_lit_small; lia).
assert (Hgp1 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite R3c, (wb2_denot_w E 3 (getr regs3 3) (EregE 3%nat 3%bv eq_refl ltac:(discriminate))).
  rewrite (Hk 3%bv ltac:(wb2_inbv)). exact Hgp. }
assert (Htp1 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite R4c, (wb2_denot_w E 4 (getr regs3 4) (EregE 4%nat 4%bv eq_refl ltac:(discriminate))).
  rewrite (Hk 4%bv ltac:(wb2_inbv)). exact Htp. }
assert (Hs01 : getr (ms_regs ms) 8 = w64 (c_rc C))
  by (rewrite R8c, (wb2_denot_w E 8 (getr regs3 8) (EregE 8%nat 8%bv eq_refl ltac:(discriminate))); exact R8).
assert (Ha01 : getr (ms_regs ms) 10 = w64 (sp0 - 72))
  by (rewrite R10c, (wb2_denot_sp E sp0 (-72) E2) by lia; reflexivity).
assert (Ha11 : getr (ms_regs ms) 11 = w64 (if c_rc C =? 0 then c_doc C else 0)).
{ rewrite R11c. apply wb2_a1; [| | exact Hrc | exact Hdoc].
  - rewrite (EregE 8%nat 8%bv eq_refl ltac:(discriminate)). exact R8.
  - rewrite (EregE 9%nat 9%bv eq_refl ltac:(discriminate)). exact R9. }
pose proof (st_ok_region_nth SEGS E _ _ 0
  (YP09.mkRegion (Some 2%nat) (-80) 0 (-48) (-32)
    [YP09.mkChunk (-40) (CVal 8 (SLit 0)); YP09.mkChunk (-48) (CVal 8 (SOff 10 0))]) HS eq_refl) as RG1.
assert (Vscr1 : val_mem SEGS (rdW W3 (ms_mem ms)) (sp0 - 48) 8 scr).
{ replace (sp0 - 48) with (sp0 + -48) by lia.
  apply (slot_of_region SEGS E _ sp0 _ _ _ _ _ (-48) (SOff 10 0) scr RG1); [rewrite E2; apply unsigned_lit_small; lia | right; left; reflexivity | | lia].
  apply wb2_denot_w. rewrite (EregE 10%nat 10%bv eq_refl ltac:(discriminate)). exact R10. }
assert (Vdl1 : val_mem SEGS (rdW W3 (ms_mem ms)) (sp0 - 40) 4 0).
{ apply wb2_vm0_4. replace (sp0 - 40) with (sp0 + -40) by lia.
  apply (slot_of_region SEGS E _ sp0 _ _ _ _ _ (-40) (SLit 0) 0 RG1); [rewrite E2; apply unsigned_lit_small; lia | left; reflexivity | reflexivity | lia]. }
assert (Vp1 : val_mem SEGS (rdW W3 (ms_mem ms)) (sp0 - 72) 8 (c_data C)).
{ apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [intros kk Hkk; apply KA1; lia | exact (proj1 HEX3)]. }
assert (Ve1 : val_mem SEGS (rdW W3 (ms_mem ms)) (sp0 - 64) 8 (c_data C + c_size C)).
{ apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [intros kk Hkk; apply KA1; lia | exact (proj2 HEX3)]. }
assert (Vd1 : val_mem SEGS (rdW W3 (ms_mem ms)) (sp0 - 56) 4 0).
{ apply wb2_vm0_4. apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms)); [intros kk Hkk; apply KA1; lia | exact V56]. }
(* the ledger at the call (own = 0, g_most and g_own_ran_out among the prh_pst bytes): the stretch wrote only the
   frame, and the prh_pst bytes are low image bytes *)
assert (HL1 : LEDGER ly3 S3 Hp3 W3 (ms_mem ms) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0).
{ apply (S1Ledger.prh_ledger_kept_aview B ly3 S3 Hp3 W3 mem3 ly3 S3 Hp3 W3 (ms_mem ms) _ _ _ _ _ _ _ HL3).
  - intros a Ha. pose proof (@pa_segs_low _ _ PA a (Hpst_img a Ha)) as Hlo. apply KA1; clear - Hlo Rsp C5; lia.
  - intros a kk i Hin Hi. change (@cf_head CfParams_preset) with 16.
    destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a kk HL3 Hin) as (Hk0 & Hab & _).
    change (@cf_head CfParams_preset) with 16 in Hab.
    destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ (ajx_ar HJ) Hab) as (_ & H4 & Hc & _).
    rewrite caw_req in Hc by lia. apply KA1; [lia|]. rewrite HSTK in Hslo. lia.
  - intros a kk _ H. exact H.
  - apply Permutation_refl. }
(* the registers the stretch kept *)
assert (K1c : forall r : bv 5, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs3 r).
{ intros r Hr.
  pose proof (regs_kept_of_st_ok SEGS E _ _ (regupd regs3 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) [SHADOW_OFF])
    [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS ltac:(subst E; apply wb2_E_agree)
    ltac:(vm_compute; reflexivity) r Hr) as X.
  cbn [ms_regs restrict] in X. rewrite X. apply wb2_getr_upd_other.
  intros ->. cbn [In] in Hr. repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]).
  exact Hr. }
assert (Hdoc0 : c_rc C = 0 -> c_doc C <> 0).
{ intros Hrc0. exact (proj2 (proj2 (proj2 (wb2_tree C ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ k scr
    (STK_ex_value (PI := prh_img_B) DOC_D) Hpre HJ Hscr ltac:(rewrite Hsp1, HSTKV; rewrite HSTK in Hslo; lia)
    ltac:(rewrite HSTK in Hslo; lia) Hrc0)))). }
(* ---- the call of ex_value (+100), by its text at nesting DOC_D, through the window-and-float call rule ---- *)
eapply SRr_bind.
{ eapply (aj_call_xWF_sp (fx := fy) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) W3 E _ ms STK sp0 []
    (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly3 S3 Hp3 _ k (STK_ex_value (PI := prh_img_B) DOC_D) 80
    [(scr, scr + Z.of_nat (length (c_x C)) + 1); (sp0 - 72, sp0 - 72 + 8); (sp0 - 72 + 16, sp0 - 72 + 20);
     (sp0 - 72 + 32, sp0 - 72 + 36)] (-80) (Z_to_bv 64 (BASE + (AF_cawB + 104))) [] _ HS eq_refl HJ).
  - exact Hsp1.
  - reflexivity.
  - lia.
  - rewrite HSTKV. lia.
  - rewrite HSTKV, HSTK. lia.
  - lia.
  - reflexivity.
  - lia.
  - exact Hgp1.
  - exact Htp1.
  - exact Hra1.
  - apply (ret_ok_codeptr_v (PI := PA)); rewrite EAF; [lia | reflexivity].
  - rewrite unsigned_lit_small by (rewrite EAF; lia).
    pose proof (wb2_slot_lo ly3 S3 Hp3 W3 (ms_mem ms) _ (AF_cawB + 104) (ajx_ar HJ) ltac:(rewrite EAF; lia)
      wb2_slot104) as HLO. unfold kImgLo in HLO. lia.
  - rewrite <- Hsp1. apply (wb2_achain0 _ _ _ _ (c_rc C) Hs01 Hrc). rewrite Etop3. lia.
  - intros HPRE1 HWIN1. cbn [ss_pc setpc].
    refine (TEXV fy ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ [] (sp0 - 72) (if c_rc C =? 0 then c_doc C else 0)
      (c_data C) 0 0 0 scr 80 (c_x C) (c_t C) (c_D C) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + (* fpre at the call's float state fy; FRM0-ENTRY's frm_zero (fp_csr fy) is caw_base's first conjunct *)
      split; [exact HPRE1|]. split; [exact (wb2_rod C ly3 S3 Hp3 W3 (ms_mem ms) _ k Hpre HJ)|].
      split; [rewrite Hsp1, Eshi3; lia|].
      split; [|exact Hfz].
      unfold raZ. rewrite Hra1, unsigned_lit_small by (rewrite EAF; lia).
      apply (pa_slot_lt_ceil_b (PL := PL_caw_B) (PI := PA)); [rewrite EAF; lia | exact wb2_slot104].
    + exact (PMN _ HPM).
    + exact Hfz.
    + rewrite Hfr3. pose proof (wb2_count_cid 1 (frames (c_S C))) as Hcc.
      lazymatch eval vm_compute in (ck_FRAMES_CAP - FR_check_as_written) with ?n =>
        assert (EC : ck_FRAMES_CAP - FR_check_as_written = n) by reflexivity end.
      lazymatch eval vm_compute in (fs_frames 1) with ?n => assert (EF1 : fs_frames 1 = n) by reflexivity end.
      lazymatch eval vm_compute in (Z.of_nat (Datatypes.S DOC_D)) with ?n =>
        assert (ED : Z.of_nat (Datatypes.S DOC_D) = n) by reflexivity end.
      change (Z.of_nat (Nat.succ DOC_D)) with (Z.of_nat (Datatypes.S DOC_D)). rewrite EF1, ED. rewrite EC in HFR. lia.
    + exact Ha01.
    + exact Ha11.
    + unfold prhex_cur. replace (sp0 - 72 + 8) with (sp0 - 64) by lia. replace (sp0 - 72 + 16) with (sp0 - 56) by lia.
      replace (sp0 - 72 + 24) with (sp0 - 48) by lia. replace (sp0 - 72 + 32) with (sp0 - 40) by lia.
      rewrite Z.add_0_r. split; [exact Vp1|]. split; [exact Ve1|]. split; [exact Vd1|]. split; [exact Vscr1 | exact Vdl1].
    + lia.
    + intros rd' _. apply (wb2_achain0 _ _ _ _ (c_rc C) Hs01 Hrc). rewrite Etop3. lia.
    + rewrite Hsp1. lia.
    + rewrite Hsp1. lia.
    + exact HWIN1.
    + apply (wb2_src_rd C ly3 S3 Hp3 W3 (ms_mem ms) _ k (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0
        Hpre HJ); [| exact EHp | exact HL1].
      intros x Hx. rewrite (proj2 Hscr). apply in_or_app. left. exact Hx.
    + intros Hpos. change (Z.of_nat (length (c_x C))) with (c_size C) in *.
      destruct (HINB Hpos) as (b & m & Hin & H1 & H2 & H3).
      exists b, m. split; [rewrite (proj2 Hscr); apply in_or_app; left; exact Hin|]. split; [exact H1|]. split; [exact H2|].
      intros Hb. apply H3. rewrite <- EHp. exact Hb.
    + exact Hsz.
    + unfold c_size in Hsz0. lia.
    + lia.
    + lazymatch eval vm_compute in (Z.of_nat DOC_D) with ?n => change (Z.of_nat DOC_D) with n end. lia.
    + left. reflexivity.
    + apply (wb2_wdest_scr C ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C)
        (c_most C) 0 scr _ (ajx_ar HJ) HL1 Hscr).
      * rewrite EHp. exact (wb2_scr_not_hp C ly3 S3 Hp3 W3 (ms_mem ms) _ scr Hpre (ajx_ar HJ) Hscr).
      * rewrite Hsp1, HSTKV. rewrite HSTK in Hslo. lia.
    + exists scr, (c_size C + 1). split; [exact Hscrb|]. split; [lia|]. split; [unfold c_size; lia|].
      intros Hh. exfalso. apply (wb2_scr_not_hp C ly3 S3 Hp3 W3 (ms_mem ms) _ scr Hpre (ajx_ar HJ) Hscr).
      rewrite <- EHp. exact Hh.
    + exact (wb2_apart_x C ly3 S3 Hp3 W3 (ms_mem ms) _ scr Hpre (ajx_ar HJ) Hscr).
    + left. rewrite HSTK in Hslo. unfold c_size in Hsceil. lia.
    + destruct (Z.eqb_spec (c_rc C) 0) as [Hrc0 | Hrcn]; [right | left; reflexivity].
      destruct (wb2_tree C ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ k scr (STK_ex_value (PI := prh_img_B) DOC_D)
        Hpre HJ Hscr ltac:(rewrite Hsp1, HSTKV; rewrite HSTK in Hslo; lia) ltac:(rewrite HSTK in Hslo; lia) Hrc0)
        as (HT & HD & HFt & _).
      exact (conj HT (conj HD HFt)).
    + exact HL1.
  - intros a (r & Hin & Ha). cbn [In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
    + right. left. exists scr, (c_size C + 1). split; [exact Hscrb|].
      split; [exact (caw_scr_new B C ly3 S3 Hp3 W3 (ms_mem ms) _ scr (ajx_ar HJ) Hscr Hsz0)|].
      rewrite caw_req by lia. unfold c_size in *. lia.
    + right. right. right. rewrite HSTK. lia.
    + right. right. right. rewrite HSTK. lia.
    + right. right. right. rewrite HSTK. lia. }
(* ---- ex_value returned (+104): a0 = r, the float state its post's ---- *)
cbv beta. intros W4 c4 Hwle4 (fx' & ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & -> & HFZ & HFK & HJ4 & HJc & HX & HP4 & [HQ4 HKP4]).
destruct HQ4 as (HRL4i & HHU4 & HRP4i & r & p' & dep' & dl' & Rr4 & Hcur4 & Hdl4 & EHp4 & Eab4 & HL4 & Hmatch).
subst Hp4. clear HJc.
change (skipn (Z.to_nat 0) (c_x C)) with (c_x C) in Hmatch.
assert (HPM4 : P mem4) by exact (PCALL _ _ HKP4 HPM).
assert (Hfk4 : fregs_kept_x fx fx') by (intros rr Hrr; rewrite (HFK rr Hrr); exact (Hfk rr Hrr)).
assert (HRL4 : room_live_cf S4) by exact (HRL4i HRL3).
(* the progress fact at caw_ev1 C crosses ex_value: its post keeps every run position (the implication form) *)
assert (Hrp4 : caw_prog C (caw_ev1 C) S4).
{ intros rsm rx ros ri rH0 rhist Hpos Hrun. destruct (Hrp rsm rx ros ri rH0 rhist Hpos Hrun) as (h & Hh).
  exists h. exact (HRP4i _ _ _ _ _ _ Hh). }
assert (P4 : forall rr : bv 5, In rr [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs4 rr = getr regs3 rr).
{ intros rr Hr. rewrite (wb2_ap (ms_regs ms) regs4 rr HP4); [exact (K1c rr Hr)|].
  unfold acallee_saved. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [wb2_cs |]). destruct Hr. }
assert (Hsp4 : spZ regs4 = sp0 - CAWB_FRAME).
{ unfold spZ. rewrite (wb2_ap (ms_regs ms) regs4 2%bv HP4) by wb2_cs.
  fold (spZ (ms_regs ms)). rewrite Hsp1. unfold CAWB_FRAME. lia. }
assert (KS4 : forall a, sp0 - 32 <= a < sp0 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite HX; [apply KA1; lia | lia |].
  intros (r0 & Hin & Hr0). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr0;
    unfold c_size in Hsceil; rewrite HSTK in Hslo; lia. }
pose proof Hcur4 as (Vp4 & Ve4 & Vd4 & Vs4 & Vdl4).
replace (sp0 - 72 + 8) with (sp0 - 64) in Ve4 by lia. replace (sp0 - 72 + 16) with (sp0 - 56) in Vd4 by lia.
replace (sp0 - 72 + 24) with (sp0 - 48) in Vs4 by lia. replace (sp0 - 72 + 32) with (sp0 - 40) in Vdl4 by lia.
(* the re-seat at +104: the frame word at sp0 - 48 (the scratch) *)
pose (E2e := wb2_E regs4 sp0 [scr]).
assert (E22 : ew E2e 2 = Z_to_bv 64 sp0) by (subst E2e; apply wb2_E_sp).
assert (EregE2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> rr <> 2%bv -> ew E2e n = getr regs4 rr)
  by (intros n rr Hn Hr; subst E2e; exact (wb2_E_reg regs4 _ [scr] n rr Hn Hr)).
assert (HS2 : st_ok_pi (fx := fx') SEGS VAL E2e (mkSS (AF_cawB + 104) wb2_sr80 [wb2_fregion [(-48, 8%N)] 0 0] None wb2_facts)
  (restrict (w_H W4) (@YK11.mkst fx' regs4 (Z_to_bv 64 (BASE + (AF_cawB + 104))) mem4 (YK11.seg_rom SEGS)))).
{ apply wb2_st_ok.
  - vm_compute. reflexivity.
  - cbn. lia.
  - exact Hsp4.
  - unfold CAWB_FRAME. lia.
  - intros o Ho. lia.
  - cbn [wb2_vals_ok]. change (N.to_nat 8) with 8%nat. change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8.
    replace (sp0 + -48) with (sp0 - 48) by lia. split; [exact Vs4|]. split; [lia|]. split; [lia | exact I].
  - unfold facts_ok, wb2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    first [rewrite E22 | rewrite wb2_E_sp]. rewrite unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp016 | lia]. }
assert (HEI2 : img_env VAL A_LIM E2e) by (subst E2e; unfold wb2_E; apply Eimg_env).
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2e (mrestrict (w_H W4) mem4)) by (unfold sh_ok; apply Forall_nil).
pose (RUN2 := @paj_run_x_inv fx' rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RUNTO2 := @paj_run_to_x_inv fx' rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (BR2 := @paj_branch fx' rc B_prog_listing PA).
assert (U10 : U E2e (SOff 10 0) = bv_unsigned (w64 r)).
{ rewrite U_SOff, (EregE2 10%nat 10%bv eq_refl ltac:(discriminate)), Rr4, Z.add_0_r. apply zcanon_id.
  pose proof (bv_unsigned_in_range 64 (w64 r)) as X. unfold bv_modulus in X. unfold M64. exact X. }
destruct (prhex_V 0 (c_x C)) as [[u rest] | ] eqn:HV.
- (* the reading succeeded: r = 0 *)
  destruct Hmatch as (Er & Ep' & Edep & Hdlu). subst r dep'.
  psrr_branch_tok RUN2 BR2 HS2 SHOK2 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + clear Hc.
    paj_run_to_tok_x_inv RUNTO2 HS2 HJ4 SHOK2 HPM4 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_WS).
    { intros a (r0 & Hin & Hr0). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi wb2_fregion base_val] in Hr0. lia. }
    lazymatch type of HF with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM5 end.
    clear HF HFr HG.
    assert (R5 : forall rr : bv 5, In rr [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
      getr (ms_regs ms0) rr = getr regs3 rr).
    { intros rr Hr.
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E2e _ _ (regupd regs4 2%bv (Z_to_bv 64 sp0))
        (map (Z_to_bv 64) [SHADOW_OFF; scr]) [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS2
        ltac:(subst E2e; apply wb2_E_agree) ltac:(vm_compute; reflexivity) rr Hr) as X.
      cbn [ms_regs restrict] in X. rewrite X, wb2_getr_upd_other; [exact (P4 rr Hr)|].
      intros ->. cbn [In] in Hr.
      repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
    wb2_reg HS2 (2%bv : bv 5) R25.
    assert (Hsp5 : spZ (ms_regs ms0) = c_sp C - CAWB_FRAME)
      by (unfold spZ; rewrite R25, (wb2_denot_sp E2e sp0 (-80) E22) by lia; rewrite unsigned_lit_small by lia;
          unfold CAWB_FRAME; lia).
    pmkst HS2.
    match goal with |- SRr _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (BASE + ?pc)) _ _; cfg_model := _ |} _ =>
      change pc with (AF_cawB + CAWB_WS) end.
    apply SRr_ret. cbv beta.
    apply (Kws fx' ly4 S4 Hp3 W4 (ms_regs ms0) (ms_mem ms0) _ (k + k1) scr dl' u rest); [|exact HPM4].
    split.
    { split; [exact HFZ|]. split; [exact Hfk4|]. split; [unfold caw_J; exact HJ4|].
      split; [intros rr Hr; rewrite (R5 rr) by (cbn [In] in Hr |- *; tauto); exact (Hk rr Hr)|].
      split; [exact Hsp5|].
      split; [rewrite (R5 8%bv) by wb2_inbv; exact R8|].
      split; [apply (wb2_saved_move C W3 W4 mem3 (ms_mem ms0)); [intros a Ha; rewrite EM5; exact (KS4 a Ha) | exact HSV]|].
      split; [exact EHp|]. exact HRL4. }
    split; [rewrite (R5 9%bv) by wb2_inbv; exact R9|].
    split; [rewrite (R5 18%bv) by wb2_inbv; exact R18|].
    split; [exact HV|].
    split.
    { unfold caw_ex3. rewrite EM5. split.
      - rewrite Ep' in Vp4. replace (c_data C + c_size C - Z.of_nat (length rest))
          with (c_data C + (Z.of_nat (length (c_x C)) - Z.of_nat (length rest))) by (unfold c_size; lia). exact Vp4.
      - exact Ve4. }
    split; [rewrite EM5; exact Vd4|].
    split; [rewrite EM5; exact Vs4|].
    split; [rewrite EM5; exact Vdl4|].
    split; [exact Hdl4|].
    split.
    { rewrite Hdlu. destruct (Z.eqb_spec (c_rc C) 0) as [Hrc0 | Hrcn].
      - specialize (Hdoc0 Hrc0). split.
        + intros [H | [_ Ht]]; [lia | split; [exact Hrc0 | exact Ht]].
        + intros [_ Ht]. right. split; [exact Hdoc0 | exact Ht].
      - split.
        + intros [H | [H _]]; [lia | exfalso; exact (H eq_refl)].
        + intros [H _]. exfalso. exact (Hrcn H). }
    split; [split; [exact Hs4096 | rewrite Eab4; exact (proj2 Hscr)]|].
    split; [exact Hrp4|].
    split; [unfold caw_ledger; rewrite EM5; exact HL4|].
    (* the hull budget crosses ex_value: it uses nothing (its post's hull_used S3 S4 []) *)
    exact (PresetHullBudget.hull_budget_app S3 S4 [] [PresetReqAt.HFr (c_size C + 1)] HHB3 HHU4).
  + exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. cbn in Hc. discriminate Hc.
- destruct Hmatch as (Er & Hp'r & Hdep). subst r.
  psrr_branch_tok RUN2 BR2 HS2 SHOK2 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. cbn in Hc. discriminate Hc.
  + clear Hc.
    paj_run_tok_x_inv RUN2 HS2 HJ4 SHOK2 HPM4 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    { intros a (r0 & Hin & Hr0). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi wb2_fregion base_val] in Hr0. lia. }
    lazymatch type of HF with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM6 end.
    clear HF HFr HG.
    (* the reading was refused, so the text is not JSON and rc <> 0 (caw_pre's case split) *)
    assert (Hrcn : c_rc C <> 0).
    { destruct HCASE as [[Hrc0 Hrd] | [Hrcn _]]; [|exact Hrcn].
      destruct (proj1 (H2CawPure.caw_read_V (c_x C) (c_t C)) Hrd) as (rr & Hrr & _). rewrite HV in Hrr. discriminate Hrr. }
    assert (R6 : forall rr : bv 5, In rr [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
      getr (ms_regs ms0) rr = getr regs3 rr).
    { intros rr Hr.
      pose proof (regs_kept_of_st_ok SEGS E2e _ _ (regupd regs4 2%bv (Z_to_bv 64 sp0))
        (map (Z_to_bv 64) [SHADOW_OFF; scr]) [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS2
        ltac:(subst E2e; apply wb2_E_agree) ltac:(vm_compute; reflexivity) rr Hr) as X.
      cbn [ms_regs restrict] in X. rewrite X, wb2_getr_upd_other; [exact (P4 rr Hr)|].
      intros ->. cbn [In] in Hr.
      repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
    wb2_reg HS2 (1%bv : bv 5) R61. wb2_reg HS2 (2%bv : bv 5) R62. wb2_reg HS2 (10%bv : bv 5) R610.
    assert (Hra6 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (AF_cawB + 116)))
      by (rewrite R61, <- (codeptr_val (PI := PA) E2e (AF_cawB + 116) HEI2), EAF; reflexivity).
    assert (Hsp6 : spZ (ms_regs ms0) = sp0 + -80)
      by (unfold spZ; rewrite R62, (wb2_denot_sp E2e sp0 (-80) E22) by lia; apply unsigned_lit_small; lia).
    assert (Hlo6 : kImgLo <= BASE + (AF_cawB + 116))
      by exact (wb2_slot_lo ly4 S4 Hp3 W4 (ms_mem ms0) _ (AF_cawB + 116) (ajx_ar HJ4) ltac:(rewrite EAF; lia)
        wb2_slot116).
    (* the journal read BY NAME (YCbqG's ajx_ projections), never positionally *)
    pose proof (ajx_ar HJ4) as HAR6. pose proof (ajx_ly HJ4) as Hly6. pose proof (ajx_frs HJ4) as Hfrs6.
    pose proof (ajx_qt HJ4) as HQT6.
    pose proof Hly6 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop6 & _).
    assert (Hscr4 : caw_scr B C ly4 S4 scr) by (split; [exact Hs4096 | rewrite Eab4; exact (proj2 Hscr)]).
    pose proof (caw_scr_new B C ly4 S4 Hp3 W4 (ms_mem ms0) _ scr HAR6 Hscr4 Hsz0) as Hnew4.
    pose proof (universe_ok_of_ARcf SEGS B ly4 S4 Hp3 W4 (ms_mem ms0) _ (proj1 HAR6)) as HUok.
    pose proof (alloc_model_laws_x_cf B HUok) as AMX.
    (* the free's call memory QMm_cf: the room, cf_hull_ok from the hull budget cut_ev carries across ex_value (its
       post's hull_used S3 S4 []), arodata_ok_cf from the reader form at the call memory (wb2_rod) through the bridge *)
    assert (HQM : QMm_cf SEGS B S4 (ms_mem ms0)).
    { destruct (QM_cf_of_room SEGS B ly4 S4 Hp3 W4 (ms_mem ms0) _ (proj1 HAR6) HQT6 (YGcfRoomLive.room_live_room S4 HRL4)
        (PresetHullPay.hull_ok_of_budget _ _
          (PresetHullBudget.hull_budget_app S3 S4 [] [PresetReqAt.HFr (c_size C + 1)] HHB3 HHU4)))
        as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
      destruct Hrelro_eq as [ERL ERH].
      apply (YGcfAroBridge.arodata_ok_cf_of_P SEGS B W4 (ms_mem ms0) Hrelro_seg Herrno_relro Hrelro_top Hro_reads_nw).
      rewrite ERL, ERH. exact (wb2_rod C ly4 S4 Hp3 W4 (ms_mem ms0) _ _ Hpre HJ4). }
    (* the free's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
       post carries the trace in the journal's wild budget, which ajournal_xw_fix1R drops again) *)
    assert (HTR : In (call_trace ly4 (pc_free_ra0 (as_code B)) (ms_regs ms0) []) (as_universe B)).
    { apply (wb2_free_trace C). exact Hpre. unfold raZ. rewrite Hra6. apply unsigned_lit_small. rewrite EAF. lia. }
    (* ---- the free of the scratch (+112), by the free row under the re-hide with its memnorm keep ---- *)
    apply SRr_ret. cbv beta.
    eapply (YA0nH.SRrG_bind SEGS RW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    { eapply (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (fx := fx') (SK := SK) SEGS B prh_pst LAWS (@pa_segs_low _ _ PA)
        (pal_env B PAL) (ARx_owned_low_law_xs SEGS B LAWS_cf) (ARx_wf_law_xs SEGS B) AMX (AFREE fx')
        W4 E2e _ ms0 STK sp0 [] (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly4 S4 Hp3 _ (k + k1)
        scr (c_size C + 1) (-80) (ew E2e 2) (Z_to_bv 64 (BASE + (AF_cawB + 116))) [] HS2 (pal_free B PAL) eq_refl
        (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARcfx (@wle SEGS) RW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4)).
      - exact (proj1 (wb2_scr_blk C ly4 S4 Hp3 W4 (ms_mem ms0) _ scr HAR6 Hscr4 Hsz0)).
      - rewrite EHp. exact (wb2_scr_not_hp C ly4 S4 Hp3 W4 (ms_mem ms0) _ scr Hpre HAR6 Hscr4).
      - rewrite R610. apply wb2_denot_w. exact (wb2_E_val regs4 sp0 [scr] 0 ltac:(lia)).
      - exact R62.
      - reflexivity.
      - rewrite E22. apply unsigned_lit_small. lia.
      - reflexivity.
      - lia.
      - rewrite HSTK. unfold ASTACK. lia.
      - rewrite (R6 3%bv) by wb2_inbv. rewrite (Hk 3%bv) by wb2_inbv. exact Hgp.
      - rewrite (R6 4%bv) by wb2_inbv. rewrite (Hk 4%bv) by wb2_inbv. exact Htp.
      - exact Hra6.
      - apply (ret_ok_codeptr_v (PI := PA)); rewrite EAF; [lia | reflexivity].
      - exact HQM.
      - apply (caw_chain _ _ _ (c_rc C)).
        + unfold raZ. rewrite Hra6, unsigned_lit_small by (rewrite EAF; lia). unfold kImgLo in Hlo6. lia.
        + rewrite (R6 8%bv) by wb2_inbv. exact R8.
        + exact Hrc.
        + rewrite Hsp6. lia.
        + rewrite Etop6. lia.
      - exact (admits_fix _ _ _ HUok HTR).
      - intros Hin. exfalso. exact (Hnew4 Hin). }
    cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & (l1 & l2 & Eab4' & Eab7) & Hfr7 &
      Hpre7 & Hun7 & (q & trc & Hq & Hqin & Hpath & Hg & Hleaf) & Hkept & HKP7).
    (* the journal after the call: the fixed trace leaves the budget *)
    pose proof (ajournal_xw_fix1R HTR HJ7) as HJ7f. clear HJ7. rename HJ7f into HJ7.
    destruct Hkept as (K71 & K72 & K73 & _).
    assert (HPM7 : P mem7) by exact (PCALL _ _ HKP7 HPM4).
    assert (Eab0 : ablocks B ly7 S7 = ablocks B (c_ly C) (c_S C)).
    { rewrite Eab4, (proj2 Hscr) in Eab4'. destruct (caw_split_last _ _ _ _ Eab4' Hnew4) as [-> ->].
      rewrite Eab7, app_nil_r. reflexivity. }
    (* the class-24 count at the free's entry state S4: the entry's (caw_cnt C, the text's room counts) plus the
       scratch's one block (caw_scr: S4's blocks are the entry's and the scratch) *)
    assert (HC24 : YGcfRoomLive.ccnt24 S4 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1).
    { pose proof (wb2_ccnt24_app ly4 S4 (c_ly C) (c_S C) _ (proj2 Hscr4)) as Hc24s. cbn [length] in Hc24s.
      pose proof Hcnt as (_ & Hc24e). clear - Hc24s Hc24e. lia. }
    assert (HRL7 : room_live_cf S7).
    { change S7 with (snd (tt, S7)).
      eapply (YGcfRoomLive.RL_free_step SEGS B _ _ _ _ _ _ _ _ (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1));
        [exact (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ Hpre7) |
         exact (conj HC24 (proj2 (CfRoomLivePreset.preset_rl_b24_ok (c_S C) (proj2 Hcnt)))) | exact HRL4 | exact Hpath]. }
    assert (Hqnn : q <> PNull) by (intros ->; cbn in Hq; clear - Hq Hs4096; lia).
    (* the progress fact after the free: the run's next events at i are caw_ev1 C then HFr (size + 1); caw_prog at
       caw_ev1 C gives a position i + 1 at S4, room_pos_keep_free the next one at S7 *)
    assert (Hrp7 : caw_prog C (caw_evs C) S7).
    { intros rsm rx ros ri rH0 rhist Hpos Hrun.
      change (caw_evs C) with (caw_ev1 C ++ [PresetReqAt.HFr (c_size C + 1)]) in Hrun.
      destruct (caw_run_at_app rsm rx ros ri _ _ Hrun) as (Hr1 & Hr2).
      destruct (Hrp4 rsm rx ros ri rH0 rhist Hpos Hr1) as (rhist4 & Hrp4p).
      pose proof (caw_run_at_nth rsm rx ros _ _ _ Hr2) as HEVF.
      replace (ri + length (caw_evs C))%nat with (Datatypes.S (ri + length (caw_ev1 C)))
        by exact (eq_sym (Nat.add_succ_r ri 1)).
      eexists. exact (PresetRoomPosKeep.room_pos_keep_free SEGS B ly4 S4 Hp3 W4 (ms_regs ms0) (ms_mem ms0) _ [] rsm rx ros
        (ri + length (caw_ev1 C))%nat rH0 rhist4 q (c_size C + 1) _ trc S7
        (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ Hpre7) Hun7 Hqin Hqnn Hpath Hrp4p HEVF). }
    (* the ledger after the free (own = 0): the runtime row keeps every other block's bytes and every prh_pst byte (in
       the image, neither runtime-owned nor errno) *)
    assert (HL7 : LEDGER ly7 S7 Hp3 W7 mem7 (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0).
    { apply (wb2_ledger_free C ly4 S4 Hp3 W4 (ms_mem ms0) _ ly7 S7 W7 mem7 scr 0 Hpre HAR6 Hscr4);
        [rewrite EM6; exact HL4 | exact Eab0 | exact K72 | exact K73]. }
    assert (KS7 : forall a, sp0 - 32 <= a < sp0 -> aview SEGS (w_H W7) mem7 a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha. rewrite K71; [rewrite EM6; exact (KS4 a Ha) | rewrite HSTK in Hslo; lia | unfold ASTACK; lia]. }
    (* ---- the re-seat at +116 and `j` to +164 ---- *)
    pose (E3 := @Eimg _ B_prog_listing PA (Ereg regs7 [Z_to_bv 64 SHADOW_OFF])).
    assert (HS3 : st_ok_pi (fx := fx') SEGS VAL E3 (mkSS (AF_cawB + 116) sr_atoms [] None (mkFacts [] [] []))
      (restrict (w_H W7) (@YK11.mkst fx' regs7 (Z_to_bv 64 (BASE + (AF_cawB + 116))) mem7 (YK11.seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - subst E3. apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - apply Forall_nil.
      - cbn [pairwise_disjoint all_disjoint]. exact I.
      - split; [exact I | split; exact I]. }
    assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
    assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] E3 (mrestrict (w_H W7) mem7)) by (unfold sh_ok; apply Forall_nil).
    pose (RUNTO2R := @paj_run_to_x_invR fx' rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
      (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    paj_run_to_tok_x_invR RUNTO2R HS3 HJ7 SHOK3 HPM7 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (AF_cawB + CAWB_OA).
    { intros a (rg & Hin & _). destruct Hin. }
    lazymatch type of HF with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM8 end.
    clear HF HFr HG.
    assert (KR8 : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
      getr (ms_regs ms1) rr = getr regs7 rr).
    { intros rr Hr.
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E3 _ _ regs7 [Z_to_bv 64 SHADOW_OFF]
        [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS3
        ltac:(subst E3; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity])
        ltac:(vm_compute; reflexivity) rr Hr) as X.
      cbn [ms_regs restrict] in X. exact X. }
    assert (R7 : forall rr : bv 5, In rr [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
      getr (ms_regs ms1) rr = getr regs3 rr).
    { intros rr Hr. rewrite (KR8 rr) by (cbn [In] in Hr |- *; tauto).
      rewrite (wb2_ap (ms_regs ms0) regs7 rr HP7) by (cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [wb2_cs |]); destruct Hr).
      exact (R6 rr Hr). }
    pmkst HS3.
    match goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (BASE + ?pc)) _ _; cfg_model := _ |} _ =>
      change pc with (AF_cawB + CAWB_OA) end.
    apply (KoA fx' ly7 S7 Hp3 W7 (ms_regs ms1) (ms_mem ms1) _ (k + k1 + (st_nev S7 - st_nev S4))); [|exact HPM7].
    split.
    { split; [exact HFZ|]. split; [exact Hfk4|]. split; [unfold caw_JR; exact HJ7|].
      split; [intros rr Hr; rewrite (R7 rr) by (cbn [In] in Hr |- *; tauto); exact (Hk rr Hr)|].
      split.
      { unfold spZ. rewrite (KR8 2%bv) by wb2_inbv. rewrite (wb2_ap (ms_regs ms0) regs7 2%bv HP7) by wb2_cs.
        fold (spZ (ms_regs ms0)). rewrite Hsp6. unfold CAWB_FRAME. lia. }
      split; [rewrite (R7 8%bv) by wb2_inbv; exact R8|].
      split; [apply (wb2_saved_move C W3 W7 mem3 (ms_mem ms1)); [intros a Ha; rewrite EM8; exact (KS7 a Ha) | exact HSV]|].
      split; [exact EHp|]. exact HRL7. }
    split; [exact Hrcn|]. split; [exact Eab0|].
    split; [exact Hrp7|].
    unfold caw_ledger. rewrite EM8. exact HL7.
Qed.
End f.
End d.

Print Assumptions caw_WB2.
