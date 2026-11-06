(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   relay_finish, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)),
   after lib/A/W_relay_finish_h.v (a working branch a3987bff22c: its loop rf_loop and its tail rf_tail), in the
   form of the B walks lib/B/W_check_bounded.v (a working branch 7e062bb9b9c) and lib/B/W_gse_loop.v
   (a working branch bb5ed8a0689). *)
(* Modified by Theorem Labs, 2026-10: the room `_x` form (a Theorem Labs lane, RoomRFB): the walk is pb_relay_finish_x,
   stated over any allocator relation ARx with its laws as W_contract_x.v rf_spec_x (Section c below: PST / ARx / hl /
   LAWS / HP0 / BLKN, the callees' and the allocator rules' `_x` twins, PSTR / PSTC), and it threads rf_spec_x's room
   round: the budget rp_RM RP (each round: the free's 1, then gestures_end's charge) and the count premise
   cnt_ok_pk RP rf_pk (rf_pk = 5) to the free (cnt_ok) and to gestures_end (gse_pk = 4); the round's room bound follows
   rf_room's `- cap` threading (the round frees the old g_out block).  The room argument is lib/A/W_relay_finish_h.v's
   (a working branch 9e4f84a8fb9), the ARx form that of lib/B/W_list_free.v / W_source_reset.v
   (a working branch dfa1a225350).
   B's relay_finish sets no frame pointer and calls no __asan_stack_malloc, so A's fake-frame seat, its set_fs step and rp_RPF across the seat do not apply.
   pb_relay_finish keeps its statement, byte-identical, and its Section hypotheses (the same terms in the same order;
   HPLAIN / HWSEG write rf_cells as rf_cells RG GTU GL): it is re-derived from pb_relay_finish_x at ARx := ARi0,
   PST := [], RP := RP_AR (Section cAR); pb_relay_finish_fr / _fr_tfib are unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_relay_finish.v, with its module paths and module names changed; 2648 of its 2780 lines of code are new or changed and 4211 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/FuzzReallocB_p102.v, with its module paths, module names and numbers changed; 715 of its 832 lines of code are new or changed and 2663 lines of the source are left out. *)
(* fuzz_preset, the #102 re-walk of fuzz_malloc on image B' (asan-ubsan, pinned d663f82d; merged alloc.c fuzz_malloc
   :80-93, refused :70-78; B' 0x85d08, 45 instructions, frame 16, own out of line at 0x85dbc) against the batch-cut
   text tfuzz_malloc_specX (lib/A/PRH_FnAlloc.v blob 4d8aeba047e5 with PRH_Base.v ef7c8ca98529, the cut of
   the batch: the kit's previous text plus THE OUTCOME conjunct and the
   LIVE premise guarded by cnt <> fail; the POST-IMPLICATION form of the header's FAMILY - no entry position, each arm
   transfers any model run's position by its own event list E, E = [] at the two NULL returns, [HMal (n + cf_head)] at
   the grant;
   the room counts position-free entry premises; fpre with FRM0-ENTRY; the refusal arm
   with g_peak := max (g_peak, min SIZE_MAX (g_live + n)) and g_ran_out := 1 iff n <= g_most, the ledger with g_most /
   g_own_ran_out as FIELDS (prh_glob / prh_ledger bind most own; S1Ledger 8cf15eeb6311), the m-form post fpostm,
   room_live_cf), at preset's CfParams (cf_malloc_max
   2 ^ 28 + 2 ^ 27, lib/A/CfParamsPreset.v of the cf layer 0dcba76f6f92), the allocator relation ARcf pa_segs B /\
   xs_placed_cf (the cf layer's YG0ncf.v; YGcallcf.v's ARxs) and image B' numbers prh_img_B (lib/B/PRH_ImgB.v, generated on
   the unstripped twin c90d4fa5).
   The listing facts, the symbolic state, the windows, the entry state and the pure engine runs of every segment are
   the statement-independent part, lib/B/Prog/FuzzMallocB_p102.v (row AL2's prep). This file adds the journal: the
   runner YC80x / YC1fPx over YCbqG's ajournal_x in its memnorm-carrying form (YSRrMemnorm's srr_inv_laws_memnorm_k,
   the carrier of FuzzFreeB.v), the malloc wrapper by YGcallMxmnKeep's aj_malloc_x_m_keep over the keep text
   YGcfMallocComposeKeep.amalloc_realizes_cf_keep (its last conjunct carries memnorm across the call),
   own by its text town_specX through YCbqGcall's aj_call_x in TAIL form.
   The arms (the code, lib/B/Prog/FuzzMallocB_p102.v's cut table): g_count += 1; CHOSEN-FAIL (g_count = g_fail_at):
   g_fail_at := SIZE_MAX, j to the shared return-0 epilogue; TOOBIG is decided by the engine from n's fact (n + cf_head
   < cf_malloc_max); the malloc wrapper at n + 16; NULL: refused(n) (g_peak raised to held when peak < held, g_ran_out
   := 1 when n <= g_most), return 0 (four paths); else the frame is popped and own (b, n) is tail-called (SUCCESS).
   Room: room_live_cf S' by the cf layer's YGcfRoomLive.RL_malloc_step at the preset counts
   (CfRoomLivePreset.preset_rl_sec_ok / preset_rl_b24_ok, the text's two count premises); the call's QMm_cf by
   YGcfRoomLive.room_live_room; own keeps S; own's fpre takes the entry's frm_zero (the float state is the section's
   fx, untouched). The position arms: the position kit's PresetRoomPosKeep.room_pos_keep_alloc (SUCCESS, its run event from
   PRH_Base.prh_run_at_one) and room_pos_keep_alloc_null (REFUSED); CHOSEN-FAIL keeps S; both NULL arms advance by
   length [] = 0 with the history kept.
   THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a consumer allocation of a model run whose next
   event is HMal (n + cf_head), with cnt <> fail, res <> 0 and S' is the granted advance. CHOSEN-FAIL contradicts
   cnt <> fail; REFUSED is impossible there by the kit's PRH_Refute.prh_refute_window (P8 at the call's state S and the
   engine's grant on the path aj_malloc_x_m returns); SUCCESS returns res + cf_head <> 0 at the grant arm's position.
   The LIVE premise is used only past the CHOSEN-FAIL test, where cnt <> fail holds. own's post is read BY NAME
   (fmw_conj_pick, the kit's ec_conj_pick pattern), so a conjunct the kit adds to town_specX's post cannot shift the others.
   The ledger is reached only through PRH_Base's named projections (Section ledger_proj) and S1Ledger's lemmas.
   RULE-24: lib/B/Prog/FuzzMallocB_p102.v's header and the record in the internal file p102-AL2-prep.md.
   Numerals: as FuzzMallocB_p102.v; 52 (DERIVED: 48 + a0's place in CLOB); 16384 / 4096 (DERIVED: ASTACK / ESTACK);
   2 ^ 28 + 2 ^ 27 (DERIVED: CfParams_preset's cf_malloc_max, by reflexivity). No ADDRESS literal.
   STEP 2 (the kit's Step-1 text, PRH_FnAlloc.v bf282cf2f794 with PRH_Base.v ed555f753097): THE HULL, route (b). The text's
   entry budget PresetHullBudget.hull_budget S [HMal (n + cf_head)] gives the call's cf_hull_ok at S (the call's state:
   no allocator step before it; lib/A/PresetHullPay.v hull_ok_of_budget), and each arm's hull use is the call's model
   path (YGcfSecsStep.secs_malloc_step, PresetHullBudget.hull_used_of_call), or none on CHOSEN-FAIL (hull_used_refl).
   PART 3c: the call memory's QMm_cf is QMm_cf_of_room with arodata_ok_cf carried from fpre's reader form arodata_okP
   by the journal to the call (YGcallcf.v arodata_ok_cf_of_journal_P at image B''s rows, lib/AU/CfAroPresetB.v), so the
   walk is at image B''s CfImg_B (as FuzzFreeB.v); QMm_cf asks no memnorm. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop YCbqGcall YGcallx YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep YGcfAroBridge YF0m
  YGcfMallocComposeKeep YGcallMxmnKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset PRH_Refute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoom PresetRun PresetReqAt
  PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB FuzzMallocB_p102.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* image B''s cf instance: the call memory's read-only rows are image B''s (lib/AU/CfAroPresetB.v), as FuzzFreeB.v *)
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParams_preset.
Context {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation CP := CfParams_preset.

(* ---- B''s generated numbers (PRH_ImgB.v) against the listing (computed, never typed) ---- *)
Lemma fmw_objs : VAL OBJ_g_count = @pi_g_count prh_img_B /\ VAL OBJ_g_fail_at = @pi_g_fail prh_img_B /\
  VAL OBJ_g_ran_out = @pi_g_ran_out prh_img_B /\ VAL OBJ_g_live = @pi_g_live prh_img_B /\
  VAL OBJ_g_peak = @pi_g_peak prh_img_B /\ VAL OBJ_g_most = @pi_g_most prh_img_B.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma fmw_ret_site : BASE + (FM_K + 72) = @pi_ret_malloc prh_img_B.
Proof. vm_compute. reflexivity. Qed.
Lemma fmw_stk : @STK_fuzz_malloc prh_img_B = 16 + ASTACK.
Proof. vm_compute. reflexivity. Qed.
Lemma fmw_stk_own : @STK_own prh_img_B = 32 + ESTACK.
Proof. vm_compute. reflexivity. Qed.
Lemma fmw_head : @cf_head CP = 16.
Proof. reflexivity. Qed.
Lemma fmw_mmax : @cf_malloc_max CP = 2 ^ 28 + 2 ^ 27.
Proof. reflexivity. Qed.
(* the statics at B''s generated widths (pi_gz_*: 8 / 8 / 8 / 8 / 1 / 8 / 1) *)
Lemma fmw_pst_eq : PST = [(@pi_g_live prh_img_B, 8); (@pi_g_peak prh_img_B, 8); (@pi_g_count prh_img_B, 8);
  (@pi_g_fail prh_img_B, 8); (@pi_g_ran_out prh_img_B, 1); (@pi_g_most prh_img_B, 8); (@pi_g_own_ran_out prh_img_B, 1)].
Proof. reflexivity. Qed.
(* g_own_ran_out (fuzz_preset.c's static, A_OBJ 13) sits between g_most and g_live: off every window of the walk *)
Lemma fmw_own_place : B_prog_val OBJ_g_most + 8 <= @pi_g_own_ran_out prh_img_B /\
  @pi_g_own_ran_out prh_img_B + 1 <= B_prog_val OBJ_g_live.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
(* the walk's facts in the generated names *)
Lemma fmw_order : IMG_LO_B <= @pi_g_fail prh_img_B /\ @pi_g_fail prh_img_B + 8 <= @pi_g_most prh_img_B /\
  @pi_g_most prh_img_B + 8 <= @pi_g_own_ran_out prh_img_B /\ @pi_g_own_ran_out prh_img_B + 1 <= @pi_g_live prh_img_B /\
  @pi_g_live prh_img_B + 8 <= @pi_g_peak prh_img_B /\ @pi_g_peak prh_img_B + 8 <= @pi_g_count prh_img_B /\
  @pi_g_count prh_img_B + 8 <= @pi_g_ran_out prh_img_B /\ @pi_g_ran_out prh_img_B + 8 <= IMG_TOP_B.
Proof.
pose proof fm_order as (D0 & D1 & D2 & D3 & D4 & D5 & D6). pose proof fmw_own_place as (P1 & P2).
pose proof fmw_objs as (O1 & O2 & O3 & O4 & O5 & O6).
change (B_prog_val OBJ_g_count) with (VAL OBJ_g_count) in *. change (B_prog_val OBJ_g_fail_at) with (VAL OBJ_g_fail_at) in *.
change (B_prog_val OBJ_g_ran_out) with (VAL OBJ_g_ran_out) in *. change (B_prog_val OBJ_g_live) with (VAL OBJ_g_live) in *.
change (B_prog_val OBJ_g_peak) with (VAL OBJ_g_peak) in *. change (B_prog_val OBJ_g_most) with (VAL OBJ_g_most) in *.
rewrite O1, O2, O3, O4, O5, O6 in *. lia.
Qed.
Lemma fmw_stored_eq : fm_stored = [(@pi_g_count prh_img_B, 8); (@pi_g_fail prh_img_B, 8); (@pi_g_ran_out prh_img_B, 1);
  (@pi_g_peak prh_img_B, 8)].
Proof.
pose proof fmw_objs as (O1 & O2 & O3 & O4 & O5 & O6). unfold fm_stored.
change (B_prog_val OBJ_g_count) with (VAL OBJ_g_count). change (B_prog_val OBJ_g_fail_at) with (VAL OBJ_g_fail_at).
change (B_prog_val OBJ_g_ran_out) with (VAL OBJ_g_ran_out). change (B_prog_val OBJ_g_peak) with (VAL OBJ_g_peak).
rewrite O1, O2, O3, O5. reflexivity.
Qed.
Lemma fmw_stored_pst : forall a, Exists (in_zr a) fm_stored -> Exists (in_zr a) PST.
Proof.
intros a H. rewrite fmw_stored_eq in H. apply Exists_exists in H as (r & Hr & Hz). rewrite fmw_pst_eq.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; unfold in_zr in Hz; cbn [fst snd] in Hz.
- do 2 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma fmw_pst_bounds : forall a, Exists (in_zr a) PST -> IMG_LO_B <= a < IMG_TOP_B.
Proof.
intros a H. pose proof fmw_order as N. apply Exists_exists in H as (r & Hr & Hz).
rewrite fmw_pst_eq in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold in_zr in Hz; cbn [fst snd] in Hz; lia.
Qed.
(* the cells the walk does not store: g_live, g_most, g_own_ran_out (and every other PST byte off fm_stored) *)
Lemma fmw_not_stored : forall a, ~ (@pi_g_count prh_img_B <= a < @pi_g_count prh_img_B + 8) ->
  ~ (@pi_g_fail prh_img_B <= a < @pi_g_fail prh_img_B + 8) -> a <> @pi_g_ran_out prh_img_B ->
  ~ (@pi_g_peak prh_img_B <= a < @pi_g_peak prh_img_B + 8) -> ~ Exists (in_zr a) fm_stored.
Proof.
intros a H1 H2 H3 H4 H. rewrite fmw_stored_eq in H. apply Exists_exists in H as (r & Hr & Hz).
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; unfold in_zr in Hz; cbn [fst snd] in Hz; lia.
Qed.

(* ---- the walk's write premise and what a run keeps ---- *)
Lemma fmw_wr : forall E rs sp0 STK (bl0 blc : list (Z * Z)) ly a,
  wins_of rs = fm_wins -> img_env VAL A_LIM E -> bv_unsigned (ew E 2) = sp0 -> 16 <= STK ->
  in_wrange E rs a -> awr_byte STK sp0 [] bl0 blc ly [] a \/ Exists (in_zr a) PST.
Proof.
intros E rs sp0 STK bl0 blc ly a Hw HE Hsp HS Hr.
destruct (fm_win_cases E rs a Hw HE Hr) as [Hs | Hx]; [left; left; lia | right; exact (fmw_stored_pst a Hx)].
Qed.
(* the statics' bytes the walk does not store keep their value *)
Definition fmw_ks (m m' : word -> option byte) : Prop :=
  forall a, Exists (in_zr a) PST -> ~ Exists (in_zr a) fm_stored -> mbyte SEGS m' a = mbyte SEGS m a.
Lemma fmw_ks_trans : forall m1 m2 m3, fmw_ks m1 m2 -> fmw_ks m2 m3 -> fmw_ks m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha Hs. rewrite (H2 a Ha Hs). exact (H1 a Ha Hs). Qed.
Lemma fmw_ks_frame : forall E rs m m', frame_of E rs m m' -> wins_of rs = fm_wins -> img_env VAL A_LIM E ->
  IMG_TOP_B + 16 <= bv_unsigned (ew E 2) -> fmw_ks m m'.
Proof.
intros E rs m m' HF Hw HE Hsp a Ha Hs. pose proof (fmw_pst_bounds a Ha) as Hb.
apply (fm_frame_keep E rs m m' a HF Hw HE); [unfold IMG_LO_B, IMG_TOP_B in *; lia | lia | exact Hs].
Qed.
Lemma fmw_ks_val : forall m m' a (n : nat) v, fmw_ks m m' -> val_mem SEGS m a n v ->
  (forall k, (k < n)%nat -> Exists (in_zr (a + Z.of_nat k)) PST /\ ~ Exists (in_zr (a + Z.of_nat k)) fm_stored) ->
  val_mem SEGS m' a n v.
Proof.
intros m m' a n v HK Hv Hin. apply (prh_val_mem_keep m m' a n v Hv).
intros k Hk. destruct (Hin k Hk) as [H1 H2]. exact (HK _ H1 H2).
Qed.
(* g_live, g_most and g_own_ran_out: PST cells off fm_stored *)
Lemma fmw_keep3 : forall m m' l mo o, fmw_ks m m' ->
  (val_mem SEGS m (@pi_g_live prh_img_B) 8 l -> val_mem SEGS m' (@pi_g_live prh_img_B) 8 l) /\
  (val_mem SEGS m (@pi_g_most prh_img_B) 8 mo -> val_mem SEGS m' (@pi_g_most prh_img_B) 8 mo) /\
  (val_mem SEGS m (@pi_g_own_ran_out prh_img_B) 1 o -> val_mem SEGS m' (@pi_g_own_ran_out prh_img_B) 1 o).
Proof.
intros m m' l mo o HK. pose proof fmw_order as N.
split; [|split]; intros Hv; apply (fmw_ks_val m m' _ _ _ HK Hv); intros k Hk; (split; [rewrite fmw_pst_eq|apply fmw_not_stored; lia]).
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma fmw_wrap : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof. exact fm_wrap. Qed.

Section f.
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).

(* ---- Section hypotheses: callee texts and marked stand-ins only ---- *)
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : @PALib _ B_prog_listing PA B.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* callee text: the malloc wrapper (the cf layer, YG0dcf.v), with the memnorm keep at the leaf (YGcfMallocComposeKeep.v) *)
Hypothesis AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep (cp := CP) SEGS B.
(* callee text: own (the town_specX, PRH_FnAlloc.v) *)
Hypothesis OWN : town_specX (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (L := B_prog_listing)
  (PA := PA) B ARc SK.
(* STAND-IN for the unit's TFIB symbol binding of B (image binding, no state; the instance's TfibB_syms): errno's
   place, apart from the read-only ranges of the call memory's arodata_ok_cf (CfAroPresetB.errno_relro_preset_AU) *)
Hypothesis TS : YF0m.TfibSyms B.

Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs (cp := CP) SEGS B.
Let XSL := ARx_xs_law_xs (cp := CP) SEGS B.
Let AMALLOCx := YGcallMxmnKeep.amalloc_realizes_x_xs_keep SEGS B AMALLOC.

Lemma fmw_PST_ok : forall a, Exists (in_zr a) PST -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. intros a H. split; [exact (pst_in_img_B a H) | exact (proj1 (pal_pst_ok a H))]. Qed.
(* alloc.c's statics are no byte the call memory's arodata_ok_cf covers: each such byte is a read-only image byte
   (RELRO, or a report read inside a non-writable segment, CfAroPresetB.ro_reads_nw_preset_AU), and no static is one
   (S1ImgB.pst_not_ro_B) *)
Lemma fmw_pst_aro : forall a, aro_addr_cf a -> ~ Exists (in_zr a) PST.
Proof.
intros a Ha Hx. apply (pst_not_ro_B a Hx). destruct Ha as [Ha | Ha].
- right. unfold B_prog_relro_lo, B_prog_relro_hi. cbv [cf_relro_lo cf_relro_hi CfImgB.CfImg_B] in Ha.
  exact Ha.
- left. pose proof CfAroPresetB.ro_reads_nw_preset_AU as RONW.
  unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite Forall_forall in RONW.
  apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
  destruct (RONW r Hr) as (_ & sg & Hin & NW & L & R). exists sg. split; [exact Hin|]. split; [exact NW | lia].
Qed.

Let RUN := @paj_run_x_m fx rc SK B_prog_listing PL_prog_B PA B PST ARc _ LAWS fmw_PST_ok.
(* the same runner carrying the memnorm keep from a fixed memory m0 (YSRrMemnorm.v, FuzzFreeB.v's carrier) *)
Let RUNM (m0 : word -> option byte) := @paj_run_x_m_inv fx rc SK B_prog_listing PL_prog_B PA B PST ARc _ LAWS
  fmw_PST_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
Let BR := @paj_branch fx rc B_prog_listing PA.
Let RET := @paj_ret_at fx rc B_prog_listing PL_prog_B PA.

(* an allocator call keeps the statics: they are image bytes that are neither runtime-owned nor errno *)
Lemma fmw_static_call : forall (W : world SEGS) (mem : word -> option byte) (W' : world SEGS) (mem' : word -> option byte),
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  forall a, Exists (in_zr a) PST -> mbyte SEGS (mrestrict (w_H W') mem') a = mbyte SEGS (mrestrict (w_H W) mem) a.
Proof.
intros W mem W' mem' HK a Ha. apply prh_mbyte_of_aview.
destruct (pal_pst_ok a Ha) as [H1 H2]. exact (HK a (pst_in_img_B a Ha) H1 H2).
Qed.
Lemma fmw_ks_call : forall (W : world SEGS) (mem : word -> option byte) (W' : world SEGS) (mem' : word -> option byte),
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  fmw_ks (mrestrict (w_H W) mem) (mrestrict (w_H W') mem').
Proof. intros W mem W' mem' HK a Ha _. exact (fmw_static_call W mem W' mem' HK a Ha). Qed.
(* g_own_ran_out and g_most survive a stretch that keeps the unstored statics: the post's ledger carries the entry's
   most / own *)
Lemma fmw_own_most : forall (W : world SEGS) mem (W' : world SEGS) mem',
  fmw_ks (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') ->
  (forall o, prh_own (PI := prh_img_B) (L := B_prog_listing) (PA := PA) W mem o ->
     prh_own (PI := prh_img_B) (L := B_prog_listing) (PA := PA) W' mem' o) /\
  (forall m, prh_most (PI := prh_img_B) (L := B_prog_listing) (PA := PA) W mem m ->
     prh_most (PI := prh_img_B) (L := B_prog_listing) (PA := PA) W' mem' m).
Proof.
intros W mem W' mem' HK. split.
- intros o (Hv & Ho). split; [|exact Ho]. exact (proj2 (proj2 (fmw_keep3 _ _ 0 0 o HK)) Hv).
- intros m (Hv & Hm). split; [|exact Hm]. exact (proj1 (proj2 (fmw_keep3 _ _ 0 m 0 HK)) Hv).
Qed.
(* the read-only view survives the walk's journal *)
Lemma fmw_ro_keep : forall (W : world SEGS) (mem : word -> option byte) (W' : world SEGS) (mem' : word -> option byte),
  arodata_okP SEGS B_prog_relro_lo B_prog_relro_hi B (aview SEGS (w_H W) mem) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> fp_spares [] a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  arodata_okP SEGS B_prog_relro_lo B_prog_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros W mem W' mem' HR HK a Hro Hns He.
rewrite (HK a); [exact (HR a Hro Hns He) | | exact Hns | exact He | | ].
- destruct Hro as [(s & Hs & _ & Hb) | Hb]; [exists s; split; [exact Hs | exact Hb] | exact (B_prog_relro a Hb)].
- intros Hp. exact (pst_not_ro_B a Hp Hro).
- apply fp_spares_closed. intros (r & Hr & _). destruct Hr.
Qed.
(* the harness heads survive a journal with an empty footprint (its block clause) *)
Lemma fmw_hk : forall STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k Lam,
  ajournal_x (SK := SK) SEGS B PST ARc STK sp0 [] ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  Forall (fun ak => prh_hblock (cp := CP) (L := B_prog_listing) (PA := PA) B ly S Hp W mem (fst ak) (snd ak)) Lam ->
  (forall a k0, In (a, k0) Lam -> In (a - @cf_head CP, k0 + @cf_head CP) (ablocks B ly S) ->
     In (a - @cf_head CP, k0 + @cf_head CP) (ablocks B ly' S')) ->
  forall a k0 i, In (a, k0) Lam -> 0 <= i < 8 ->
  mbyte SEGS (mrestrict (w_H W') mem') (a - @cf_head CP + i) = mbyte SEGS (mrestrict (w_H W) mem) (a - @cf_head CP + i).
Proof.
intros STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k Lam HJ HF Hb a k0 i Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (proj1 (Forall_forall _ _) HF (a, k0) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
apply prh_mbyte_of_aview. apply (F2 (a - cf_head) (k0 + cf_head) i Hblk (Hb a k0 Hin Hblk)).
- rewrite fmw_head. unfold req_size. destruct (Z.eqb_spec (k0 + 16) 0); lia.
- apply inFP_nil.
Qed.
(* a block appended to a pairwise-disjoint block list was not in it before *)
Lemma fmw_new_block : forall (bl : list (Z * Z)) x, 0 <= snd x ->
  YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (bl ++ [x])) -> ~ In x bl.
Proof.
intros bl x Hx Hp Hin. rewrite map_app in Hp. cbn [map] in Hp.
pose proof (prh_pw_last zdisjoint _ _ Hp (fst x, req_size (snd x))
  (in_map (fun b => (fst b, req_size (snd b))) bl x Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (prh_req_size_pos (snd x) Hx). lia.
Qed.
(* refused()'s ledger: Lam and the blocks unchanged, g_peak raised (not lowered), g_count / g_fail_at / g_ran_out
   given, g_most / g_own_ran_out the entry's. ONE construction of prh_glob at a raised peak: S1Ledger 8cf15eeb6311 (the kit's
   sweep, of record) has prh_glob_final_le (the unraised peak) and prh_glob_final (peak := max peak live', live' the new
   g_live), neither of which covers g_live kept with g_peak := max peak (min SIZE_MAX (live + n)); it belongs in S1Ledger
   (a Theorem Labs lane). *)
Lemma fmw_glob_raise : forall (W' : world SEGS) mem' live peak' cnt' fail' ran' most own,
  val_mem SEGS (mrestrict (w_H W') mem') (@pi_g_live prh_img_B) (@pi_gz_live prh_img_B) live -> 0 <= live <= peak' ->
  val_mem SEGS (mrestrict (w_H W') mem') (@pi_g_peak prh_img_B) (@pi_gz_peak prh_img_B) peak' -> peak' < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W') mem') (@pi_g_count prh_img_B) (@pi_gz_count prh_img_B) cnt' -> 0 <= cnt' < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W') mem') (@pi_g_fail prh_img_B) (@pi_gz_fail prh_img_B) fail' -> 0 <= fail' < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W') mem') (@pi_g_ran_out prh_img_B) (@pi_gz_ran_out prh_img_B) ran' -> (ran' = 0 \/ ran' = 1) ->
  prh_most (PI := prh_img_B) (L := B_prog_listing) (PA := PA) W' mem' most ->
  prh_own (PI := prh_img_B) (L := B_prog_listing) (PA := PA) W' mem' own ->
  prh_glob (PI := prh_img_B) (L := B_prog_listing) (PA := PA) W' mem' live peak' cnt' fail' ran' most own.
Proof.
intros W' mem' live peak' cnt' fail' ran' most own Hl Rl Hp Rp Hc Rc Hf Rf Hr Rr Hm Ho.
unfold prh_glob. repeat match goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

(* the top-level conjuncts of a hypothesis (a syntactic `_ /\ _` only), then the goal BY ITS TYPE: the kit's ec_conj_split /
   ec_conj_pick (lib/AU/Prog/Ent102CallB.v), as S1's sd_conj_pick (FuzzStrdupB.v). own's post is read through it. *)
#[local] Ltac fmw_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Sc" in let H2 := fresh "Sc" in destruct H as [H1 H2]; fmw_conj_split H1; fmw_conj_split H2
  | _ => idtac
  end.
#[local] Ltac fmw_conj_pick H := fmw_conj_split H; assumption.

(* ---- the walk ---- *)
Theorem fuzz_malloc_holds_B :
  tfuzz_malloc_specX (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (L := B_prog_listing)
    (PA := PA) B ARc SK.
Proof.
unfold tfuzz_malloc_specX, fpre, fpostm, fQmn.
intros ly S Hp W regs mem md ch n Lam peak cnt fail ran most own
  (HPRE & HRO & HSHI & HRAC & HFRM) HRL HUNIV HSEC HC24 HHB H10 Hn0 Hnmax HLED HLIVE.
rewrite fmw_head, fmw_mmax in Hnmax. rewrite fmw_head in HLIVE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof fmw_stk as WS. pose proof fmw_stk_own as WSo.
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof fm_img_top as ITOP. pose proof fmw_order as NUMS. pose proof fmw_objs as (O1 & O2 & O3 & O4 & O5 & O6).
pose proof fm_K_range as HK72.
(* the ledger's facts, by PRH_Base's named projections *)
pose proof (prh_ledger_glob B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HGL.
pose proof (prh_ledger_live B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mlive.
pose proof (prh_ledger_peak B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mpeak.
pose proof (prh_ledger_count B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mcnt.
pose proof (prh_ledger_fail B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mfail.
pose proof (prh_ledger_ran B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mran.
pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HFA.
destruct (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HLED) as (Rlp & Rpk & Rcnt & Rfail & Rran).
pose proof (prh_ledger_most B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HMOST.
(* PRH_Base's projection; S1Ledger's prh_ledger_own (the OWN arm) shares its short name *)
pose proof (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HOWN.
pose proof HMOST as (Mmost & Rmost).
change (@pi_gz_live prh_img_B) with 8%nat in Mlive. change (@pi_gz_peak prh_img_B) with 8%nat in Mpeak.
change (@pi_gz_count prh_img_B) with 8%nat in Mcnt. change (@pi_gz_fail prh_img_B) with 8%nat in Mfail.
change (@pi_gz_ran_out prh_img_B) with 1%nat in Mran. change (@pi_gz_most prh_img_B) with 8%nat in Mmost.
assert (Hlo_ceil : alloc_ceiling <= spZ regs - @STK_fuzz_malloc prh_img_B) by lia.
pose proof (fm_entry B ARc (@STK_fuzz_malloc prh_img_B) ly S Hp W regs mem md ch n cnt fail ran (Ledger.lsum Lam) peak most
  HPRE ltac:(rewrite WS; lia) H10 ltac:(lia)
  ltac:(rewrite O1; exact Mcnt) Rcnt ltac:(rewrite O2; exact Mfail) Rfail ltac:(rewrite O3; exact Mran) Rran
  ltac:(rewrite O4; exact Mlive) ltac:(lia) ltac:(rewrite O5; exact Mpeak) ltac:(lia) ltac:(rewrite O6; exact Mmost) Rmost)
  as HS.
assert (SHOK : sh_ok SEGS FM_Bx FM_SH (FM_E regs cnt fail ran (Ledger.lsum Lam) peak most) (mrestrict (w_H W) mem)) by constructor.
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARc (@STK_fuzz_malloc prh_img_B) [] ly S Hp W regs mem md ch HPRE) as HJ.
pose proof (@pa_B_ok _ B_prog_listing PA) as HBASE.
pose proof (pal_env B PAL) as HENV.
set (E := FM_E regs cnt fail ran (Ledger.lsum Lam) peak most) in *.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (fm_extra cnt fail ran (Ledger.lsum Lam) peak most)) k)
  by (intros k Hk; subst E; unfold FM_E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 cnt) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 fail) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ran) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Ledger.lsum Lam)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 peak) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 most) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (HAE : env_agree 32 (Ereg regs (fm_extra cnt fail ran (Ledger.lsum Lam) peak most)) E)
  by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; unfold FM_E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clearbody E. clear EL.
set (m0 := mrestrict (w_H W) mem) in *.
(* the cell values a final symbolic memory gives *)
assert (Dcnt : forall E', ew E' 32 = ew E 32 -> sv_denot E' (SOff 32 1) = Z_to_bv 64 ((cnt + 1) mod 2 ^ 64)).
{ intros E' HE'. cbn [sv_denot]. rewrite HE', E32, unsigned_lit_small by lia. symmetry. apply fmw_wrap. }
assert (Dfail : forall E', ew E' 33 = ew E 33 -> sv_denot E' (SOff 33 0) = Z_to_bv 64 fail).
{ intros E' HE'. rewrite fm_denot0, HE', E33. reflexivity. }
assert (Dran : forall E', ew E' 34 = ew E 34 -> sv_denot E' (SOff 34 0) = Z_to_bv 64 ran).
{ intros E' HE'. rewrite fm_denot0, HE', E34. reflexivity. }
assert (Dpeak : forall E', ew E' 36 = ew E 36 -> sv_denot E' (SOff 36 0) = Z_to_bv 64 peak).
{ intros E' HE'. rewrite fm_denot0, HE', E36. reflexivity. }
assert (Rcnt1 : 0 <= (cnt + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
unfold cfg_at. rewrite fm_entry_pc. change (w64 (BASE + FM_K)) with (Z_to_bv 64 (BASE + FM_K)).
(* g_count += 1, the CHOSEN-FAIL test *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FM_Bspan.
{ intros a Ha. refine (fmw_wr E _ (spZ regs) _ _ _ _ a _ HEI Usp _ Ha); [vm_compute; reflexivity | lia]. }
rename HFr into HFr1. clear HF HG.
psrr_branch_tok RUN BR HS SHOK FM_Bspan.
all: rewrite !fm_denot0, E32, E33, fm_bne in Hc by lia.
2:{
  (* ===== CHOSEN-FAIL: g_count = g_fail_at; g_fail_at := SIZE_MAX, return 0 ===== *)
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FM_Bspan.
  { intros a Ha. refine (fmw_wr E _ (spZ regs) _ _ _ _ a _ HEI Usp _ Ha); [vm_compute; reflexivity | lia]. }
  rename HFr into HFr2. clear HF HG.
  lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HSx (1%bv : bv 5) R1; prreg HSx (10%bv : bv 5) R10;
    pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ssx) (restrict (w_H W) msc) HSx) as HMO;
    cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
    let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
    eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mat';
    unfold fpost, apost_base_x;
    exists ly, S, Hp, (ms_regs msc), (ms_mem msc); eexists; exists 0;
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
    split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARc LAWS pa_segs_low); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs _ HSx);
            [exact HAE | vm_compute; reflexivity]|];
    split; [|exact HPM];
    set (mF := mrestrict (w_H W) (ms_mem msc)) in *
  end.
  assert (HKS : fmw_ks m0 mF).
  { eapply fmw_ks_trans.
    - eapply fmw_ks_frame; [exact HFr1 | vm_compute; reflexivity | exact HEI | rewrite Usp; lia].
    - eapply fmw_ks_frame; [exact HFr2 | vm_compute; reflexivity | exact HEI | rewrite Usp; lia]. }
  destruct (fmw_own_most W mem W _ HKS) as (Kown & Kmost).
  exists 0. split; [rewrite R10; reflexivity|].
  split; [exact HRL|].
  (* the hull: no allocator call, S' = S *)
  split; [exact (PresetHullBudget.hull_used_refl S _)|].
  split; [intros _ smq xq osq iq H0q hq Hpq _; exists hq; cbn [length]; rewrite Nat.add_0_r; exact Hpq|].
  split; [intros Hc0; exfalso; exact (Hc0 eq_refl)|].
  (* THE OUTCOME: this arm is the chosen failure, cnt = fail *)
  split; [intros smq xq osq iq H0q hq _ _ _ Hcf; exfalso; exact (Hcf Hc)|].
  unfold prh_alloc_post. left. split; [exact Hc|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  pose proof (fmw_keep3 m0 mF (Ledger.lsum Lam) 0 0 HKS) as (Kl & _).
  pose proof (Kl Mlive) as Ml'.
  assert (Mp' : val_mem SEGS mF (@pi_g_peak prh_img_B) 8 peak).
  { rewrite <- O5. apply (fm_cell E mF _ 5 _ 10 0 8 (SOff 36 0) peak HEI ltac:(lia) HMO eq_refl eq_refl
      ltac:(cbn; left; reflexivity) (Dpeak E eq_refl) ltac:(cbn; lia) ltac:(cbn; lia)). }
  pose proof (fm_cell E mF _ 1 _ 7 0 8 (SOff 32 1) _ HEI ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
    (Dcnt E eq_refl) Rcnt1 ltac:(cbn; lia)) as Mc'.
  pose proof (fm_cell E mF _ 2 _ 8 0 8 (SLit 18446744073709551615) SIZE_MAXZ HEI ltac:(lia) HMO eq_refl eq_refl
    ltac:(cbn; left; reflexivity) ltac:(cbn [sv_denot]; unfold SIZE_MAXZ; reflexivity)
    ltac:(unfold SIZE_MAXZ; cbn; lia) ltac:(cbn; lia)) as Mf'.
  pose proof (fm_cell E mF _ 3 _ 11 0 1 (SOff 34 0) ran HEI ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
    (Dran E eq_refl) ltac:(cbn; destruct Rran; lia) ltac:(cbn; lia)) as Mr1.
  change (N.to_nat 8) with 8%nat in Mc', Mf'. change (N.to_nat 1) with 1%nat in Mr1.
  rewrite Z.add_0_r in Mc', Mf', Mr1.
  change (A_OBJ 7) with OBJ_g_count in Mc'. change (A_OBJ 8) with OBJ_g_fail_at in Mf'.
  change (A_OBJ 11) with OBJ_g_ran_out in Mr1.
  rewrite O1 in Mc'. rewrite O2 in Mf'. rewrite O3 in Mr1.
  apply (prh_ledger_frame B ly S Hp W mem ly S Hp W (ms_mem _) Lam peak cnt fail ran
    peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own HLED).
  + exact (prh_glob_final_le W mem W _ _ peak cnt fail ran _ _ _ _ most own HGL Ml' Rlp Mp' Mc' Rcnt1 Mf'
      ltac:(unfold SIZE_MAXZ; lia) Mr1 Rran (Kmost most HMOST) (Kown own HOWN)).
  + exact (fmw_hk _ _ ly S Hp W mem md [] ly S Hp W _ _ _ Lam HJ HFA (fun a k0 _ H => H)).
  + intros a k0 _ H. exact H.
  + apply Permutation_refl. }
(* ===== g_count <> g_fail_at ===== *)
apply Bool.negb_true_iff, Z.eqb_neq in Hc.
(* the call is made (cnt <> fail): the text's guarded LIVE premise applies from here on *)
specialize (HLIVE Hc).
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FM_Bspan.
{ intros a Ha. refine (fmw_wr E _ (spZ regs) _ _ _ _ a _ HEI Usp _ Ha); [vm_compute; reflexivity | lia]. }
rename HFr into HFr2. clear HF HG. rename HPM into HPMc.
(* the malloc wrapper at n + 16 (YGcallMxmnKeep's aj_malloc_x_m_keep at the cf instance) *)
lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc), HJx : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  |- SRr _ _ (mkCfg _ ?mdc) _ =>
  prreg HSx (1%bv : bv 5) R1; prreg HSx (2%bv : bv 5) R2; prreg HSx (3%bv : bv 5) R3;
  prreg HSx (4%bv : bv 5) R4; prreg HSx (8%bv : bv 5) R8; prreg HSx (10%bv : bv 5) R10;
  rename HSx into HSc; rename HJx into HJc; rename msc into msC; set (mdC := mdc) in *
end.
assert (Hsp1 : spZ (ms_regs msC) = spZ regs - 16) by (unfold spZ at 1; rewrite R2, Usp, unsigned_lit_small by lia; lia).
assert (Hra1 : raZ (ms_regs msC) = BASE + (FM_K + 72)) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; reflexivity).
assert (Hs01 : s0Z (ms_regs msC) = n) by (unfold s0Z; rewrite R8, E10, unsigned_lit_small by lia; reflexivity).
assert (HROOM : @ROOM_cf CP S) by exact (YGcfRoomLive.room_live_room S HRL).
(* the call memory QMm_cf at the call (the state is still S): the room from room_live_room, cf_hull_ok from the text's
   budget (PresetHullPay.hull_ok_of_budget), arodata_ok_cf from fpre's reader form carried by the journal to the call
   memory (arodata_ok_cf_of_journal_P at image B''s rows; the footprint is empty, so it opens no sink) *)
assert (HQM : QMm_cf (cp := CP) SEGS B S (ms_mem msC)).
{ destruct (QM_cf_of_room (cp := CP) SEGS B ly S Hp W mem md (proj1 HAR) HQT HROOM
    (PresetHullPay.hull_ok_of_budget S _ HHB)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _)))))).
  apply (arodata_ok_cf_of_journal_P (SK := SK) SEGS B PST ARc (@wle SEGS)
    _ _ [] ly S Hp W mem md _ ly S Hp W (ms_mem msC) mdC _ [] HJc
    CfAroPresetB.relro_seg_preset_AU (CfAroPresetB.errno_relro_preset_AU B TS)
    CfAroPresetB.relro_top_preset_AU CfAroPresetB.ro_reads_nw_preset_AU fmw_pst_aro);
  [ intros (r & Hin & _); destruct Hin | exact HRO ]. }
eapply SRr_bind.
{ eapply (YGcallMxmnKeep.aj_malloc_x_m_keep (SK := SK) SEGS B PST ARc (@QM_cf CP) (QMm_cf (cp := CP) SEGS B) malloc_cf
    (@cf_malloc_max CP) free_cf (@Wf_cf CP (as_universe B)) xs_cf LAWS pa_segs_low HENV OWNLOW WFL
    (alloc_model_laws_x_cf (cp := CP) B (universe_ok_of_ARcf (cp := CP) SEGS B ly S Hp W mem md (proj1 HAR)))
    (QMQ_cf (cp := CP) SEGS B) XSL AMALLOCx
    W E _ msC (@STK_fuzz_malloc prh_img_B) (spZ regs) [] ly S Hp W mem md [] ly S Hp mdC 0 (n + 16) (-16)
    (getr regs 2) (Z_to_bv 64 (BASE + (FM_K + 72))) [] HSc (pal_malloc B PAL) eq_refl HJc).
  - rewrite R10, E10, unsigned_lit_small by lia. reflexivity.
  - rewrite fmw_mmax. lia.
  - exact HLIVE.
  - rewrite R2. reflexivity.
  - exact E2.
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite WS. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [exact HK72 | vm_compute; reflexivity].
  - exact HQM.
  - unfold chain_pre. split; [rewrite Hra1; apply Z.leb_le; vm_compute; reflexivity|].
    assert (Hbn : bad_next (spZ (ms_regs msC)) (ly_top ly) (s0Z (ms_regs msC)) = true).
    { unfold bad_next. rewrite Hsp1, Hs01. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
    destruct (frame0_ok ly (ms_regs msC)); [rewrite Hbn|]; reflexivity.
  - unfold call_trace0, unwind_of_chain. rewrite Hra1, fmw_ret_site.
    destruct HUNIV as [HU1 HU2]. unfold prh_trace in HU2. cbn [flat_map app] in HU2 |- *.
    (* the P'' set: the rule takes the ADMISSION at the call; the trace is a FIXED one (HU2, membership in u_fix),
       admitted at every state (YG01.admits_fix, over universe_ok from the entry ARcf) *)
    exact (YG01.admits_fix (as_universe B) _ _
      (universe_ok_of_ARcf (cp := CP) SEGS B ly S Hp W mem md (proj1 HAR)) HU2). }
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfrs2 & HPREc & Htrc &
  (pM & trc & Hpath & Hgf & Hleaf & Hpiff & Hpaddr) & HARM & Hmn2).
(* THE UNIV FORM's journal (P''): the wrapper's post journals the trace it stored (ajournal_xw .. [call_trace ..]).
   The trace is a FIXED one (prh_malloc_univ), so it leaves the budget (YCbqG.ajournal_xw_fix1) and the journal is
   ajournal_x again (Padded102B_S1.v's step) *)
assert (HFIX : In (call_trace ly (pc_malloc_ra0 (as_code B)) (ms_regs msC) []) (u_fix (as_universe B))).
{ destruct HUNIV as [HU1 HU2]. apply call_trace_in; [exact HU1|].
  unfold call_trace0, unwind_of_chain. rewrite Hra1, fmw_ret_site.
  unfold prh_trace in HU2. cbn [flat_map app] in HU2 |- *. exact HU2. }
apply (ajournal_xw_fix1 HFIX) in HJ2.
(* the memory stays normal from the entry to the call's return *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => Hmn2 (HPMc H)) as HPM. clear HPMc Hmn2.
(* what the call keeps, whichever its answer: the stack above the call's window, and the image bytes *)
assert (Hkc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs + -16 - ASTACK <= a < spZ regs + -16) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem msC) a).
{ destruct HARM as [(_ & _ & (K1 & _) & _) | (_ & _ & (K1 & _))]; exact K1. }
assert (Hki : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem msC) a).
{ destruct HARM as [(_ & _ & (_ & _ & K3 & _) & _) | (_ & _ & (_ & _ & K3 & _))]; exact K3. }
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & HJhi2 & _ & _ & _ & _ & Hpres2 & _).
assert (Hres_rng : 0 <= res < 2 ^ 64).
{ destruct HARM as [(-> & _) | (H4096 & Eab2 & _)]; [lia|].
  assert (Hin : In (res, n + 16) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp W2 mem2 md2 res (n + 16) HAR2 Hin) as (_ & _ & Hc' & _).
  pose proof (prh_req_size_pos (n + 16) ltac:(lia)). pose proof alloc_ceiling_val as [CL _]. lia. }
(* the room after the allocator step (the cf layer's RL_malloc_step at the preset counts) *)
assert (HRL2 : YGcfRoomLive.room_live_cf (cp := CP) S2).
{ change S2 with (snd (pM, S2)).
  eapply (YGcfRoomLive.RL_malloc_step SEGS B); [exact (acall_pre_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ HPREc) |
    exact (CfRoomLivePreset.preset_rl_sec_ok S HSEC) | exact (CfRoomLivePreset.preset_rl_b24_ok S HC24) | exact HRL |
    exact Hpath]. }
(* back at the return slot: the frame and the six statics' regions are kept by the call *)
jafter_call_keep_pi HSc 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRKp : tq); [|specialize (HS2 HRKp); clear HRKp] end.
{ cbn [ms_mem restrict].
  (* the six objects at the literal atom numbers the computed symbolic memory carries *)
  assert (VC : bv_unsigned (ew E (A_OBJ 7)) = @pi_g_count prh_img_B) by (rewrite (fm_obj_env E 7 HEI) by lia; exact O1).
  assert (VF : bv_unsigned (ew E (A_OBJ 8)) = @pi_g_fail prh_img_B) by (rewrite (fm_obj_env E 8 HEI) by lia; exact O2).
  assert (VR : bv_unsigned (ew E (A_OBJ 11)) = @pi_g_ran_out prh_img_B) by (rewrite (fm_obj_env E 11 HEI) by lia; exact O3).
  assert (VL : bv_unsigned (ew E (A_OBJ 9)) = @pi_g_live prh_img_B) by (rewrite (fm_obj_env E 9 HEI) by lia; exact O4).
  assert (VP : bv_unsigned (ew E (A_OBJ 10)) = @pi_g_peak prh_img_B) by (rewrite (fm_obj_env E 10 HEI) by lia; exact O5).
  assert (VM : bv_unsigned (ew E (A_OBJ 14)) = @pi_g_most prh_img_B) by (rewrite (fm_obj_env E 14 HEI) by lia; exact O6).
  let i := eval vm_compute in (A_OBJ 7) in change (A_OBJ 7) with i in VC.
  let i := eval vm_compute in (A_OBJ 8) in change (A_OBJ 8) with i in VF.
  let i := eval vm_compute in (A_OBJ 11) in change (A_OBJ 11) with i in VR.
  let i := eval vm_compute in (A_OBJ 9) in change (A_OBJ 9) with i in VL.
  let i := eval vm_compute in (A_OBJ 10) in change (A_OBJ 10) with i in VP.
  let i := eval vm_compute in (A_OBJ 14) in change (A_OBJ 14) with i in VM.
  assert (KST : forall a, Exists (in_zr a) PST ->
    mbyte SEGS (mrestrict (w_H W2) mem2) a = mbyte SEGS (mrestrict (w_H W) (ms_mem msC)) a)
    by exact (fmw_static_call W (ms_mem msC) W2 mem2 Hki).
  assert (WRP : forall a, Exists (in_zr a) PST -> writable_at SEGS (mrestrict (w_H W2) mem2) a)
    by (intros a Ha; exact (pst_writable_B _ a Ha)).
  repeat apply Forall_cons; try apply Forall_nil; split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite Usp in Ha. apply prh_mbyte_of_aview. apply Hkc; lia.
  - intros _. apply (apresent_writable SEGS). rewrite Usp in Ha. apply Hpres2. rewrite WS. lia.
  - rewrite VC in Ha.
    apply KST. rewrite fmw_pst_eq. do 2 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros _. rewrite VC in Ha.
    apply WRP. rewrite fmw_pst_eq. do 2 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - rewrite VF in Ha.
    apply KST. rewrite fmw_pst_eq. do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros _. rewrite VF in Ha.
    apply WRP. rewrite fmw_pst_eq. do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - rewrite VR in Ha.
    apply KST. rewrite fmw_pst_eq. do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros _. rewrite VR in Ha.
    apply WRP. rewrite fmw_pst_eq. do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - rewrite VL in Ha.
    apply KST. rewrite fmw_pst_eq. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros _. lia.
  - rewrite VP in Ha.
    apply KST. rewrite fmw_pst_eq. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros _. rewrite VP in Ha.
    apply WRP. rewrite fmw_pst_eq. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - rewrite VM in Ha.
    apply KST. rewrite fmw_pst_eq. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  - intros _. lia. }
rewrite <- restrict_mkst_fx in HS2.
remember (havoc E 48 (map (getr regs2) CLOB)) as E' eqn:HE' in HS2.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 48)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (E'52 : ew E' 52 = w64 res) by (rewrite HE'; unfold havoc; cbn [ew]; exact Hres).
assert (HAE' : env_agree 32 (Ereg regs (fm_extra cnt fail ran (Ledger.lsum Lam) peak most)) E')
  by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (SHOK' : sh_ok SEGS FM_Bx FM_SH E' (mrestrict (w_H W2) mem2)) by constructor.
clear HE'.
assert (HKS1 : fmw_ks m0 (mrestrict (w_H W2) mem2)).
{ eapply fmw_ks_trans; [eapply fmw_ks_trans|].
  - eapply fmw_ks_frame; [exact HFr1 | vm_compute; reflexivity | exact HEI | rewrite Usp; lia].
  - eapply fmw_ks_frame; [exact HFr2 | vm_compute; reflexivity | exact HEI | rewrite Usp; lia].
  - exact (fmw_ks_call W (ms_mem msC) W2 mem2 Hki). }
(* the NULL test *)
paj_run_tok_x_inv (RUNM mem) HS2 HJ2 SHOK' HPM FM_Bspan.
{ intros a Ha. refine (fmw_wr E' _ (spZ regs) _ _ _ _ a _ HEI' Usp' _ Ha); [vm_compute; reflexivity | lia]. }
rename HFr into HFr3. clear HF HG. rename Hc into HcF.
psrr_branch_tok RUN BR HS2 SHOK' FM_Bspan.
all: rewrite fm_denot0, E'52 in Hc; cbn [sv_denot] in Hc; unfold w64 in Hc; rewrite fm_beq in Hc by lia.
- (* ===== REFUSED: the allocator's NULL; refused(n), return 0 ===== *)
  apply Z.eqb_eq in Hc. subst res.
  destruct HARM as [(_ & Eab2 & _ & Herr & _) | (H4096 & _)]; [|lia].
  assert (HpN : pM = PNull) by (apply Hpiff; reflexivity). subst pM.
  (* refused()'s loads and the saturating add, to the g_peak compare *)
  paj_run_tok_x_inv (RUNM mem) HS2 HJ2 SHOK' HPM FM_Bspan.
  { intros a Ha. refine (fmw_wr E' _ (spZ regs) _ _ _ _ a _ HEI' Usp' _ Ha); [vm_compute; reflexivity | lia]. }
  rename HFr into HFr4. clear HF HG.
  psrr_branch_tok RUN BR HS2 SHOK' FM_Bspan.
  all: rename Hc into Hcp.
  (* both arms, to the g_most compare *)
  all: paj_run_tok_x_inv (RUNM mem) HS2 HJ2 SHOK' HPM FM_Bspan;
    [ intros a Ha; refine (fmw_wr E' _ (spZ regs) _ _ _ _ a _ HEI' Usp' _ Ha); [vm_compute; reflexivity | lia] |].
  all: rename HFr into HFr5; clear HF HG.
  all: psrr_branch_tok RUN BR HS2 SHOK' FM_Bspan.
  all: rename Hc into Hcm.
  (* each of the four paths, to the shared epilogue's ret *)
  all: paj_run_tok_x_inv (RUNM mem) HS2 HJ2 SHOK' HPM FM_Bspan;
    [ intros a Ha; refine (fmw_wr E' _ (spZ regs) _ _ _ _ a _ HEI' Usp' _ Ha); [vm_compute; reflexivity | lia] |].
  all: rename HFr into HFr6; clear HF HG.
  (* the two compares, read through U: held is fm_held_U's, g_most is atom 37, n is atom 10 *)
  all: pose proof (fm_held_U E' (Ledger.lsum Lam) n ltac:(rewrite OLD by lia; exact E35)
         ltac:(rewrite OLD by lia; exact E10) ltac:(lia) ltac:(lia)) as HUh; unfold fm_held_sv in HUh.
  all: assert (HUp : U E' (SOff 36 0) = peak) by (apply U_atom; [rewrite OLD by lia; exact E36 | lia]).
  all: assert (HUm : U E' (SOff 37 0) = most) by (apply U_atom; [rewrite OLD by lia; exact E37 | lia]).
  all: assert (HUn : U E' (SOff 10 0) = n) by (apply U_atom; [rewrite OLD by lia; exact E10 | lia]).
  all: rewrite ?branch_geu_U, ?branch_ltu_U, ?HUp, ?HUh in Hcp; rewrite ?branch_geu_U, ?branch_ltu_U, ?HUm, ?HUn in Hcm.
  all: set (held := Z.min (2 ^ 64 - 1) (Ledger.lsum Lam + n)) in *.
  all: assert (Hheld : held = Z.min SIZE_MAXZ (Ledger.lsum Lam + n)) by (unfold held, SIZE_MAXZ; reflexivity).
  all: lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HSx (1%bv : bv 5) Q1; prreg HSx (10%bv : bv 5) Q10;
    pose proof (st_ok_mem_ok SEGS E' (abs_ss VAL ssx) (restrict (w_H W2) msc) HSx) as HMO;
    cbn [abs_ss setpc ss_mem restrict ms_mem add_cond] in HMO;
    let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
    eapply (RET W2 _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mat';
    unfold fpost, apost_base_x;
    exists ly2, S2, Hp, (ms_regs msc), (ms_mem msc); do 2 eexists;
    split; [cbn [ms_regs]; rewrite Q1, OLD, E1, Hra by lia; reflexivity|];
    split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARc LAWS pa_segs_low); exact HJ2|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs _ HSx);
            [exact HAE' | vm_compute; reflexivity]|];
    split; [|exact HPM];
    set (mF := mrestrict (w_H W2) (ms_mem msc)) in *
  end.
  all: assert (HKS : fmw_ks m0 mF) by
    (eapply fmw_ks_trans; [exact HKS1|];
     eapply fmw_ks_trans; [eapply fmw_ks_frame; [exact HFr3 | vm_compute; reflexivity | exact HEI' | rewrite Usp'; lia]|];
     eapply fmw_ks_trans; [eapply fmw_ks_frame; [exact HFr4 | vm_compute; reflexivity | exact HEI' | rewrite Usp'; lia]|];
     eapply fmw_ks_trans; [eapply fmw_ks_frame; [exact HFr5 | vm_compute; reflexivity | exact HEI' | rewrite Usp'; lia]|];
     eapply fmw_ks_frame; [exact HFr6 | vm_compute; reflexivity | exact HEI' | rewrite Usp'; lia]).
  all: destruct (fmw_own_most W mem W2 _ HKS) as (Kown & Kmost).
  all: exists 0; split; [rewrite Q10; reflexivity|].
  all: split; [exact HRL2|].
  (* the hull use: the refused call's model path (YGcfSecsStep.secs_malloc_step, PresetHullBudget.hull_used_of_call) *)
  all: split; [exact (PresetHullBudget.hull_used_of_call _ S _ S2 (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath))|].
  all: split; [intros _ smq xq osq iq H0q hq Hpq _; exists hq; cbn [length]; rewrite Nat.add_0_r;
         exact (PresetRoomPosKeep.room_pos_keep_alloc_null SEGS B ly S _ W _ _ _ [] smq xq osq iq
         H0q hq (n + 16) _ trc S2 (acall_pre_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ HPREc)
         ltac:(rewrite fmw_mmax; lia) HLIVE HFIX Hpath Hpq)|].
  all: split; [intros Hc0; exfalso; exact (Hc0 eq_refl)|].
  (* THE OUTCOME: at a consumer allocation of the run the allocator's NULL on its granted path (Hpath / Hgf) is
     impossible: the kit's PRH_Refute.prh_refute_window at the call's state S (the run's event 0 of [HMal (n + cf_head)]) *)
  all: split; [intros smq xq osq iq H0q hq Hpq Hrq Hcq _; exfalso;
         apply (PRH_Refute.prh_refute_window (ci := CfImgB.CfImg_B) (cp := CP) (as_universe B) smq xq osq iq _ 0 _ H0q hq S
           Hrq Hcq eq_refl eq_refl);
         [ rewrite Nat.add_0_r; exact Hpq
         | exact (proj1 (YGcfRoomLive.rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _
             (acall_pre_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ HPREc)))
         | left; do 4 eexists; exact (conj Hpath Hgf) ]|].
  all: unfold prh_alloc_post; right; left; split; [exact HcF|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [exact Eab2|].
  all: split; [exists (ms_regs msC), (ms_mem msC), mdC, W2, (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (FM_K + 72))) mem2 (seg_rom SEGS)) md2);
         rewrite fmw_head;
         exact (malloc_cf_null_post_of_leaf SEGS B ly S Hp W (ms_regs msC) (ms_mem msC) mdC (n + 16) [] _ trc S2 W2 _
           (acall_pre_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ HPREc) Hpath Hgf
           (malloc_leaf_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ _ _ _ Hleaf))|].
  (* errno is outside every write window of the walk: the runs after the call keep it *)
  all: split; [intros k Hk; specialize (Herr k Hk); unfold aview in Herr |- *;
         destruct HENV as ((He0 & He1) & _ & _);
         assert (Hnw : forall E0 rs0 (m m' : word -> option byte), frame_of E0 rs0 m m' -> wins_of rs0 = fm_wins ->
           img_env VAL A_LIM E0 -> bv_unsigned (ew E0 2) = spZ regs ->
           mbyte SEGS m' (as_errno B + Z.of_nat k) = mbyte SEGS m (as_errno B + Z.of_nat k))
           by (intros E0 rs0 m m' HF Hw HE0 Hsp0; apply (fm_frame_keep E0 rs0 m m' _ HF Hw HE0);
               [unfold kLowMemEnd in *; lia | rewrite Hsp0; unfold kLowMemEnd in *; lia |
                intros Hx; destruct (pal_pst_ok _ (fmw_stored_pst _ Hx)) as [_ Hne]; apply Hne; lia]);
         unfold mF in *;
         rewrite (Hnw _ _ _ _ HFr6 ltac:(vm_compute; reflexivity) HEI' Usp'),
                 (Hnw _ _ _ _ HFr5 ltac:(vm_compute; reflexivity) HEI' Usp'),
                 (Hnw _ _ _ _ HFr4 ltac:(vm_compute; reflexivity) HEI' Usp'),
                 (Hnw _ _ _ _ HFr3 ltac:(vm_compute; reflexivity) HEI' Usp');
         exact Herr|].
  (* the ledger: Lam, Hp and the blocks unchanged; the four statics off the last symbolic memory *)
  all: pose proof (fmw_keep3 m0 mF (Ledger.lsum Lam) 0 0 HKS) as (Kl & _).
  all: pose proof (Kl Mlive) as Ml'.
  all: pose proof (fm_cell E' mF _ 1 _ 7 0 8 (SOff 32 1) _ HEI' ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
         (Dcnt E' ltac:(apply OLD; lia)) Rcnt1 ltac:(cbn; lia)) as Mc'.
  all: pose proof (fm_cell E' mF _ 2 _ 8 0 8 (SOff 33 0) fail HEI' ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
         (Dfail E' ltac:(apply OLD; lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as Mf'.
  all: change (N.to_nat 8) with 8%nat in Mc', Mf'. all: rewrite Z.add_0_r in Mc', Mf'.
  all: change (A_OBJ 7) with OBJ_g_count in Mc'. all: change (A_OBJ 8) with OBJ_g_fail_at in Mf'.
  all: rewrite O1 in Mc'. all: rewrite O2 in Mf'.
  (* g_peak: kept when peak >= held, held when peak < held: in both, Z.max peak held *)
  all: assert (Mp' : val_mem SEGS mF (@pi_g_peak prh_img_B) 8 (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + n))));
    [ rewrite <- Hheld, <- O5;
      first
      [ apply Bool.negb_true_iff, Z.ltb_ge in Hcp; rewrite Z.max_l by lia;
        exact (fm_cell E' mF _ 5 _ 10 0 8 (SOff 36 0) peak HEI' ltac:(lia) HMO eq_refl eq_refl
          ltac:(cbn; left; reflexivity) (Dpeak E' ltac:(apply OLD; lia)) ltac:(cbn; lia) ltac:(cbn; lia))
      | apply Bool.negb_false_iff, Z.ltb_lt in Hcp; rewrite Z.max_r by lia;
        refine (fm_cell E' mF _ 5 _ 10 0 8 _ held HEI' ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
          _ ltac:(cbn; unfold held; lia) ltac:(cbn; lia));
        unfold U in HUh; rewrite <- HUh; rewrite Z_to_bv_bv_unsigned; reflexivity ]
    |].
  (* g_ran_out: kept when g_most < n, 1 when n <= g_most *)
  all: assert (Mr' : val_mem SEGS mF (@pi_g_ran_out prh_img_B) 1 (if n <=? most then 1 else ran));
    [ rewrite <- O3;
      first
      [ apply Z.ltb_lt in Hcm; replace (n <=? most) with false by (symmetry; apply Z.leb_gt; lia);
        exact (fm_cell E' mF _ 3 _ 11 0 1 (SOff 34 0) ran HEI' ltac:(lia) HMO eq_refl eq_refl
          ltac:(cbn; left; reflexivity) (Dran E' ltac:(apply OLD; lia)) ltac:(cbn; destruct Rran; lia) ltac:(cbn; lia))
      | apply Z.ltb_ge in Hcm; replace (n <=? most) with true by (symmetry; apply Z.leb_le; lia);
        exact (fm_cell E' mF _ 3 _ 11 0 1 (SLit 1) 1 HEI' ltac:(lia) HMO eq_refl eq_refl
          ltac:(cbn; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) ]
    |].
  all: apply (prh_ledger_frame B ly S Hp W mem ly2 S2 Hp W2 (ms_mem _) Lam peak cnt fail ran
         (Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + n))) ((cnt + 1) mod 2 ^ 64) fail (if n <=? most then 1 else ran)
         most own HLED).
  all: try (refine (fmw_glob_raise W2 _ _ _ _ _ _ most own Ml' _ Mp' _ Mc' Rcnt1 Mf' Rfail Mr' _
         (Kmost most HMOST) (Kown own HOWN));
    [ lia | unfold SIZE_MAXZ; lia | destruct (n <=? most); [right; reflexivity | exact Rran] ]).
  all: try (refine (fmw_hk _ _ ly S Hp W mem md [] ly2 S2 Hp W2 _ _ _ Lam HJ2 HFA _); intros a k0 _ H; rewrite Eab2; exact H).
  all: try (intros a k0 _ H; rewrite Eab2; exact H).
  all: try apply Permutation_refl.
- (* ===== SUCCESS: a new block at res; the frame popped, own (res, n) tail-called ===== *)
  apply Z.eqb_neq in Hc.
  destruct HARM as [(Hr0 & _) | (H4096 & Eab2 & _)]; [lia|].
  rename Hc into Hres0. rename HcF into Hc.
  paj_run_tok_x_inv (RUNM mem) HS2 HJ2 SHOK' HPM FM_Bspan.
  { intros a Ha. refine (fmw_wr E' _ (spZ regs) _ _ _ _ a _ HEI' Usp' _ Ha); [vm_compute; reflexivity | lia]. }
  rename HFr into HFr4. clear HF HG.
  lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc), HJx : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    |- SRr _ _ (mkCfg _ ?mdc) _ =>
    prreg HSx (1%bv : bv 5) Q1; prreg HSx (2%bv : bv 5) Q2; prreg HSx (3%bv : bv 5) Q3;
    prreg HSx (4%bv : bv 5) Q4; prreg HSx (8%bv : bv 5) Q8; prreg HSx (10%bv : bv 5) Q10;
    prreg HSx (11%bv : bv 5) Q11;
    pose proof (st_ok_mem_ok SEGS E' ssx (restrict (w_H W2) msc) HSx) as HMO;
    cbn [ss_mem restrict ms_mem setpc] in HMO;
    rename HSx into HSt; rename HJx into HJt; rename msc into msT; set (mdT := mdc) in *;
    let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO
  end.
  set (mT := mrestrict (w_H W2) (ms_mem msT)) in *.
  pose proof HJt as (HARt & Hlyt & _ & _ & _ & _ & _ & _ & HJhit & HJbt & HJit & _).
  pose proof Hlyt as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & _).
  assert (Hin2 : In (res, n + 16) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp W2 mem2 md2 res (n + 16) HAR2 Hin2) as (Hal_r & _ & _ & _ & _ & Hpw2).
  assert (Hnotin : ~ In (res, n + 16) (ablocks B ly S)).
  { apply (fmw_new_block (ablocks B ly S) (res, n + 16)); [cbn; lia|]. rewrite <- Eab2. exact Hpw2. }
  assert (Hfresh : ~ In (res + @cf_head CP) (map fst Lam)).
  { apply (prh_fresh_malloc B ly S Hp W mem ly2 S2 Lam res n
      (proj2 (proj1 (prh_ledger_iff B ly S Hp W mem Lam peak cnt fail ran most own) HLED)) Hn0).
    - rewrite fmw_head. exact Eab2.
    - exact Hpw2. }
  assert (Hroom : Ledger.lsum Lam + n < 2 ^ 64).
  { exact (proj2 (prh_live_room B ly S Hp W mem Lam peak cnt fail ran n most own HLED
      (prh_ablocks_nonneg_cf B ly S Hp W mem md (proj1 HAR)) ltac:(rewrite fmw_head; exact HLIVE))). }
  (* the ledger at own's call: g_count + 1, the rest kept *)
  assert (HKS : fmw_ks m0 mT).
  { eapply fmw_ks_trans; [exact HKS1|].
    eapply fmw_ks_trans.
    - eapply fmw_ks_frame; [exact HFr3 | vm_compute; reflexivity | exact HEI' | rewrite Usp'; lia].
    - eapply fmw_ks_frame; [exact HFr4 | vm_compute; reflexivity | exact HEI' | rewrite Usp'; lia]. }
  destruct (fmw_own_most W mem W2 (ms_mem msT) HKS) as (Kown & Kmost).
  pose proof (fmw_keep3 m0 mT (Ledger.lsum Lam) 0 0 HKS) as (Kl & _).
  pose proof (Kl Mlive) as Ml'.
  assert (Mp' : val_mem SEGS mT (@pi_g_peak prh_img_B) 8 peak).
  { rewrite <- O5. apply (fm_cell E' mT _ 5 _ 10 0 8 (SOff 36 0) peak HEI' ltac:(lia) HMO eq_refl eq_refl
      ltac:(cbn; left; reflexivity) (Dpeak E' ltac:(apply OLD; lia)) ltac:(cbn; lia) ltac:(cbn; lia)). }
  pose proof (fm_cell E' mT _ 1 _ 7 0 8 (SOff 32 1) _ HEI' ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
    (Dcnt E' ltac:(apply OLD; lia)) Rcnt1 ltac:(cbn; lia)) as Mc'.
  pose proof (fm_cell E' mT _ 2 _ 8 0 8 (SOff 33 0) fail HEI' ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
    (Dfail E' ltac:(apply OLD; lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as Mf'.
  pose proof (fm_cell E' mT _ 3 _ 11 0 1 (SOff 34 0) ran HEI' ltac:(lia) HMO eq_refl eq_refl ltac:(cbn; left; reflexivity)
    (Dran E' ltac:(apply OLD; lia)) ltac:(cbn; destruct Rran; lia) ltac:(cbn; lia)) as Mr1.
  change (N.to_nat 8) with 8%nat in Mc', Mf'. change (N.to_nat 1) with 1%nat in Mr1.
  rewrite Z.add_0_r in Mc', Mf', Mr1.
  change (A_OBJ 7) with OBJ_g_count in Mc'. change (A_OBJ 8) with OBJ_g_fail_at in Mf'.
  change (A_OBJ 11) with OBJ_g_ran_out in Mr1.
  rewrite O1 in Mc'. rewrite O2 in Mf'. rewrite O3 in Mr1.
  assert (HLEDt : prh_ledger (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ly2 S2 Hp W2 (ms_mem msT)
    Lam peak ((cnt + 1) mod 2 ^ 64) fail ran most own).
  { apply (prh_ledger_frame B ly S Hp W mem ly2 S2 Hp W2 (ms_mem msT) Lam peak cnt fail ran
      peak ((cnt + 1) mod 2 ^ 64) fail ran most own HLED).
    + exact (prh_glob_final_le W mem W2 (ms_mem msT) _ peak cnt fail ran _ _ _ _ most own HGL Ml' Rlp Mp' Mc'
        Rcnt1 Mf' Rfail Mr1 Rran (Kmost most HMOST) (Kown own HOWN)).
    + refine (fmw_hk _ _ ly S Hp W mem md [] ly2 S2 Hp W2 _ _ _ Lam HJt HFA _).
      intros a k0 _ H. rewrite Eab2. apply in_or_app. left. exact H.
    + intros a k0 _ H. rewrite Eab2. apply in_or_app. left. exact H.
    + apply Permutation_refl. }
  (* own's fpre at the tail call: the caller's sp and ra, so fuzz_malloc's own caller-frame and ra bounds, and the
     entry's frm_zero (fx is the section's float state) *)
  assert (HspT : spZ (ms_regs msT) = spZ regs)
    by (unfold spZ at 1; rewrite Q2; try rewrite fm_denot0; rewrite OLD by lia; exact Usp).
  assert (HraT : raZ (ms_regs msT) = raZ regs)
    by (unfold raZ at 1; rewrite Q1; try rewrite fm_denot0; rewrite OLD, E1 by lia; reflexivity).
  assert (HSHIt : spZ (ms_regs msT) + 64 <= ly_stk_hi ly2) by (rewrite HspT, Eshi; exact HSHI).
  assert (HRAt : raZ (ms_regs msT) < YM05.alloc_ceiling) by (rewrite HraT; exact HRAC).
  (* own (res, n), tail-called with the caller's ra and sp (YCbqGcall aj_call_x at o = 0) *)
  eapply SRr_mono.
  { eapply (aj_call_x (SK := SK) SEGS B PST ARc LAWS pa_segs_low W2 E' _ msT (@STK_fuzz_malloc prh_img_B) (spZ regs)
      [] ly S Hp W mem md [] ly2 S2 Hp mdT _ (@STK_own prh_img_B) [(res, res + 8)] 0 (getr regs 2) (getr regs 1) ch
      _ HSt eq_refl HJt).
    - rewrite Q2; try rewrite fm_denot0. reflexivity.
    - rewrite OLD by lia. exact E2.
    - reflexivity.
    - reflexivity.
    - lia.
    - rewrite WSo. lia.
    - rewrite WSo, WS. lia.
    - rewrite Q3; try rewrite fm_denot0; rewrite OLD, E3 by lia. exact Hgp.
    - rewrite Q4; try rewrite fm_denot0; rewrite OLD, E4 by lia. exact Htp.
    - rewrite Q1; try rewrite fm_denot0; rewrite OLD, E1 by lia. reflexivity.
    - exact Hra.
    - exact Hra4.
    - rewrite Z.add_0_r.
      assert (Hs0t : s0Z (ms_regs msT) = s0Z regs) by (unfold s0Z; rewrite Q8; try rewrite fm_denot0; rewrite OLD, E8 by lia; reflexivity).
      rewrite Hs0t. apply (achain_ly_top ly ly2); [exact Etop|].
      apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia)
        ltac:(lia)).
      intros a Ha. apply HJhit; lia.
    - intros HPRE'.
      exact (OWN ly2 S2 Hp W2 (ms_regs msT) (ms_mem msT) mdT ch res n Lam peak ((cnt + 1) mod 2 ^ 64) fail ran most own
        (conj HPRE' (conj (fmw_ro_keep W mem W2 (ms_mem msT) HRO (fun a H1 H2 H3 H4 H5 => HJit a H1 H2 H3 H4 H5))
          (conj HSHIt (conj HRAt HFRM))))
        ltac:(rewrite Q10; try rewrite fm_denot0; rewrite E'52; reflexivity)
        ltac:(rewrite Q11; try rewrite fm_denot0; rewrite OLD, E10 by lia; reflexivity) Hn0
        ltac:(rewrite fmw_head; exact Hin2) Hal_r H4096 Hfresh Hroom HLEDt).
    - intros a Ha. right; left. apply inFP_cons in Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
      exists res, (n + 16). split; [exact Hin2|]. split; [exact Hnotin|].
      unfold req_size. destruct (Z.eqb_spec (n + 16) 0); lia. }
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k1 & -> & HJ3 & _ & HP3 & HQ3 & Hmn3).
  (* own's post BY NAME (fmw_conj_pick); its other conjuncts are not needed here *)
  cbv beta in HQ3.
  assert (ES3 : S3 = S2) by fmw_conj_pick HQ3.
  assert (R3a : getr regs3 10 = w64 (res + @cf_head CP)) by fmw_conj_pick HQ3.
  assert (EHp3 : Hp3 = res :: Hp) by fmw_conj_pick HQ3.
  assert (Eab3 : ablocks B ly3 S3 = ablocks B ly2 S2) by fmw_conj_pick HQ3.
  assert (HLED3 : prh_ledger (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ly3 S3 Hp3 W3 mem3
    ((res + @cf_head CP, n) :: Lam) (Z.max peak (Ledger.lsum Lam + n)) ((cnt + 1) mod 2 ^ 64) fail ran most own)
    by fmw_conj_pick HQ3.
  clear HQ3.
  pose proof HJ3 as (HAR3 & _).
  unfold fpost, apost_base_x.
  exists ly3, S3, Hp3, regs3, mem3, md3. eexists.
  split; [reflexivity|]. split; [exact HJ3|].
  split.
  { eapply aregs_preserved_trans; [|exact HP3].
    eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs _ HSt);
      [exact HAE' | vm_compute; reflexivity]. }
  split; [|intros H0; exact (Hmn3 (HPM H0))].
  exists (res + 16). split; [rewrite fmw_head in R3a; exact R3a|].
  split; [rewrite ES3; exact HRL2|].
  (* the hull use: the grant's model path (YGcfSecsStep.secs_malloc_step, PresetHullBudget.hull_used_of_call) *)
  split; [rewrite ES3; exact (PresetHullBudget.hull_used_of_call _ S _ S2 (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath))|].
  split; [intros Hz; exfalso; lia|].
  split.
  { intros _ smq xq osq iq H0q hq Hpq Hrq. exists hq. rewrite ES3. cbn [length]. rewrite Nat.add_1_r.
    apply PRH_Base.prh_run_at_one in Hrq.
    exact (PresetRoomPosKeep.room_pos_keep_alloc SEGS B ly S _ W _ _ _ [] smq xq osq iq H0q hq
      (n + 16) _ trc pM S2 (acall_pre_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ HPREc)
      ltac:(rewrite fmw_mmax; lia) HLIVE HFIX Hpath ltac:(intros HpN; apply Hres0; apply Hpiff; exact HpN) Hpq
      ltac:(rewrite fmw_head in Hrq; exact Hrq)). }
  (* THE OUTCOME: the grant, res + cf_head <> 0, at the grant arm's position *)
  split.
  { intros smq xq osq iq H0q hq Hpq Hrq _ _. split; [lia|]. exists hq. rewrite ES3. cbn [length]. rewrite Nat.add_1_r.
    apply PRH_Base.prh_run_at_one in Hrq.
    exact (PresetRoomPosKeep.room_pos_keep_alloc SEGS B ly S _ W _ _ _ [] smq xq osq iq H0q hq
      (n + 16) _ trc pM S2 (acall_pre_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ HPREc)
      ltac:(rewrite fmw_mmax; lia) HLIVE HFIX Hpath ltac:(intros HpN; apply Hres0; apply Hpiff; exact HpN) Hpq
      ltac:(rewrite fmw_head in Hrq; exact Hrq)). }
  unfold prh_alloc_post. right; right.
  assert (Hin3 : In (res, n + 16) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin2).
  destruct (AR_shadow_law_ok_cf (cp := CP) SEGS B ly3 S3 Hp3 W3 mem3 md3 res (n + 16) (proj1 HAR3) Hin3) as [Hbs Hhv].
  assert (Hhd : hd_skip (cp := CP) Hp3 res = 16).
  { unfold hd_skip. rewrite EHp3. cbn [existsb]. rewrite Z.eqb_refl. reflexivity. }
  assert (Hrq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
  rewrite Hhd, Hrq in Hbs. rewrite Hrq in Hhv.
  rewrite fmw_head.
  split; [exact Hc|]. split; [lia|]. split; [rewrite Zplus_mod, Hal_r; reflexivity|].
  split; [rewrite fmw_head in Hfresh; exact Hfresh|].
  split; [rewrite EHp3; f_equal; lia|].
  split; [rewrite Eab3, Eab2; do 3 f_equal; lia|].
  split.
  { destruct (Z.eq_dec n 0) as [-> | Hn1]; [apply range_addressable_nil; lia|].
    apply (block_shadow_range _ SHADOW_OFF (res + 16) (n + 16 - 16) (res + 16) n Hbs); lia. }
  split.
  { intros Hn1 s Hs. apply Hhv.
    pose proof (shadow_mono res (res + 16) ltac:(lia)) as M1.
    assert (Rdiv8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
      by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
    pose proof (Rdiv8 _ _ M1). replace (res + (n + 16) - 1) with (res + 16 + n - 1) by lia. lia. }
  split.
  { destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 res (n + 16) HAR3 Hin3) as (_ & _ & _ & _ & Hpr3 & _).
    destruct (garr8_of_present SEGS (mrestrict (w_H W3) mem3) (res + 16) (Z.to_nat n)) as (l & Hl & Hg).
    { intros a Ha. destruct (Hpr3 a ltac:(rewrite Hrq; lia)) as [(Hh & bb & Hb) _].
      exists bb. unfold mrestrict. rewrite Hh. exact Hb. }
    exists l. split; [rewrite Hl; lia | exact Hg]. }
  rewrite fmw_head in HLED3. exact HLED3.
Qed.

End f.
End d.
