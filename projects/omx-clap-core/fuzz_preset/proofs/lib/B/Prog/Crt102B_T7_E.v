(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/Prog/Ent102L3B.v, with its module paths and module names changed; 94 of its 120 lines of code are new or changed and 531 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T7 = CRT-B-CEXIT: the row's LAST
   stretch, E (+0x808, pj_free (&back)'s return) .. X (+0x30c): `mv s5, zero` (+0x808, the return flag r = 0) and
   `j` X (+0x80c), B/Listing_prog.v 8bcc2c9e7809 lines 1640-1641.

   proves no function (kind: segment lemma).

   t7_stretch_E : T7_AT_X -> T7_AT_E. The state at E (Crt102B_T7_bd.v t7_at_E) is crt_at_X_B's r = 0 state but for
   s5; the two instructions store nothing, clear s5 and jump, so the X statement (the glue's CRT_B_AT_X at the B
   instance, a premise) applies at r = 0, own = 0 and ran = 0.
   KB ROUND: E and X are at kb = prh_wk F_check_round_trip (66); the run keeps the journal's budget WS
   (Crt102Kit.v crt_run_to_xw, the A' twin's runner), so crt_at_J_B's crt_live is rebuilt at the same WS.

   NAMED SECTION HYPOTHESES:
   - LAWS : AR_laws_x SEGS B ARx cf_head (the allocator relation's laws; owner the engine, discharged at
     the instance ARcfx by lib/Reusable/YGcallcf.v AR_laws_x_xs);
   - HRAN : ran = 0 (tcheck_round_trip_specX's entry premise, PRH_FnCheck.v :1260 at the kit tip 3ac20a5c9e30).

   INPUTS OF RECORD: base commit cbe6d10993c2 (Crt102Glue.v crt_at_X_B /
   crt_at_J_B with its `r = 0 /\`, and at 275deb46b92d copy's free-order conjunct, which t7_at_E carries in as
   t7_copy_tie; Crt102Img.v); lib/B/Prog/Crt102B_T7_bd.v (this row). Model read, not cited:
   Crt102B_T4.v crtB_T4_X (a B' run into a boundary premise). Engine: YC1fPx.v paj_run_to_x /
   paj_run_to_tok_x.

   NUMERALS. WORD: register numbers. No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102B_T7_bd.
(* the image-free kb runners (Crt102Kit.v Section kbw), by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* the re-hiding move's world relation and step relation (YA0nH.wle', YA0nH.SRr') at preset's zone RZ_cf
   (Crt102Glue.v, the wle' contract: the journal at R := wle' SEGS RZ_cf, the cuts at SRr'), by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Section t7e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model)
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).
#[local] Notation AT_X := (@T7_AT_X fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation AT_E := (@T7_AT_E fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).

Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HRAN : ran = 0.

(* the symbolic state at E: no region (the two instructions read and write no memory) *)
Definition t7_ssE : sstate := mkSS (CRT_PC_B + CRT7_E_OFF_B) cur_atoms [] None (mkFacts [] [] []).

(* a register the run did not write keeps its start value (Crt102B_T4.v's cb4_keep) *)
Ltac t7e_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

Lemma t7_stretch_E : AT_X -> AT_E.
Proof.
intros HX fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg mms cset
  (Ht & HFZ & HFK & HL & HBR & HRAb & HRAv & Hcs & Hcs0 & Hcnt & HFD & HPOS & HNC & HTB & (Fc & HFOc & HFtc) & HDP).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_memnorm HL) as HMNl.
assert (HS : st_ok_pi SEGS VAL (TEB regs rg []) t7_ssE
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT7_E_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ apply (ts_st_ok (fx := fxk)); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
pose (RUNTO := @Crt102Kit.crt_run_to_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WS_HJ).
unfold crt_cfg.
paj_run_to_tok_x RUNTO HS HJ SHOK (0, 0) (CRT_PC_B + CRT_X_OFF_B).
{ apply awr_ok_nil. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. clear HFr HG.
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [t7e_keep HS |]). destruct Hr. }
prreg HS (21%bv : bv 5) Q21.
pmkst HS.
rewrite HF in HJ |- *.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_B + CRT_X_OFF_B) end.
assert (EJ : crt_evs_J (t := t) = [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set mms))])
  by (unfold crt_evs_J; rewrite Ht; reflexivity).
apply (HX fxk lyc Sc Hpc Wc memc _ kj pos Lamc peakc cntc 0 0 Dc (ms_regs ms) 0).
refine {| crt_at_X_B_join := _; crt_at_X_B_back_open := HRAb; crt_at_X_B_v_open := HRAv |}.
refine {| crt_at_J_B_live := _; crt_at_J_B_frm_zero := HFZ; crt_at_J_B_fregs := HFK; crt_at_J_B_bregs := _;
  crt_at_J_B_ret := Q21; crt_at_J_B_copy_fd := HFD; crt_at_J_B_r0 := eq_refl; crt_at_J_B_count := _ |}.
{ refine {| crt_live_journal := ex_intro _ WS_HJ (conj HJ HB_HJ); crt_live_side := crt_live_side HL;
    crt_live_lam_perm := crt_live_lam_perm HL;
    crt_live_blocks_perm := crt_live_blocks_perm HL; crt_live_dx_apart := crt_live_dx_apart HL;
    crt_live_saved := crt_live_saved HL; crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
    crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
    crt_live_memnorm := crt_live_memnorm HL |}. }
{ refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
    crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
    crt_bregs_B_s11 := _ |}; rewrite KR by (cbv; tauto).
  - exact (crt_bregs_B_sp HBR). - exact (crt_bregs_B_gp HBR). - exact (crt_bregs_B_tp HBR).
  - exact (crt_bregs_B_s0 HBR). - exact (crt_bregs_B_s1 HBR). - exact (crt_bregs_B_s2 HBR).
  - exact (crt_bregs_B_s4 HBR). - exact (crt_bregs_B_s3 HBR). - exact (crt_bregs_B_s7 HBR).
  - exact (crt_bregs_B_s9 HBR). - exact (crt_bregs_B_s11 HBR). }
exists cset. split; [exact Hcs|].
split; [intros mm Ht' Hin; rewrite Ht in Ht'; injection Ht' as <-; exact (Hcs0 Hin)|].
right. split; [reflexivity|]. split; [reflexivity|]. split; [symmetry; exact HRAN|]. split; [exact Hcnt|].
split; [rewrite EJ; exact HPOS|]. split; [exact HNC|]. split; [exact HTB|].
split; [exists Fc; split; [exact HFOc | exact HFtc] | exact HDP].
Qed.

End g.
End f.
End t7e.
