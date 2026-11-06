(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): aj_flag_store_xR is aj_flag_store_x over a journal at
   a world relation R and the step relation SRrG R (YSRrG.SRrG_msteps for the run, YCbqG's R forms for the journal);
   the run keeps the world, so no law of R is read, and the R form takes R reflexive and transitive as every R rule
   does. aj_flag_store_x keeps its statement and is the instance at wle. aj_stack_malloc_at_xR (the call's own journal
   enters the caller's at R by reflexivity and transitivity; the post's own-call journal stays at wle) and
   aj_set_shadow_at_xR are the other two rules over R; their old names are the instances at wle. *)
(* Modified by Theorem Labs, 2026-10: cgif's frame-area call rule aj_stack_malloc_at (proofs/cgif/cgif_file_fuzzer/lib/
   YCbq.v:1749-1809, this tree's copy lib/Reusable/YCbq.v:1749) restated over YCbqG.v's journal ajournal_x (allocator
   invariant a parameter ARx, ghost head set Hp after S / Hpc after Sc, program statics PST), for the frame-area
   contract astack_malloc_realizes_x of the frozen lib/Reusable/FCiface.v (frameclass d9a884240c6e, sha256
   673aac5ee2f6ed86). Generic: no image
   class, no address, no allocator instance.
   Differences from the donor, each minimal:
   (a) cgif read the model's progress and post from model_laws (stack_malloc_progressP, ml_stack_malloc through
       am_wf); here they are ONE hypothesis in ARx form, SMX, which an instance discharges from its own model laws
       (the cf instance: YG05cf.v stack_malloc_progress_cf and stack_malloc_ok_cf with Wf_cf from ARcf);
   (b) the call's own journal is call_effect_journal_x (YGcallx.v:251) at PST = [], lifted by ajournal_x_nil_pst, and
       composed by ajournal_x_sub (YCbqG.v, footprint FP1 = []); Hp is threaded unchanged (FCiface: a frame-area call
       neither poisons nor unpoisons a head);
   (c) the frame's presence (FCiface's post) is also returned, which a caller writing its new frame needs;
   (d) as cgif's aj_stack_malloc_atS (cgif_file_fuzzer lib/YC85.v:292), the post ends with the call's own journal and
       `exists f, S2 = set_fs f Sc` (the call changes st_fs only), so a caller carries a state fact across the call.
   SECOND RULE, aj_flag_store_x: cgif's aj_flag_store (YCbq.v:2362-2439, the inline release under astack_free_law)
   for the LISTING engine over ajournal_x; its ARx-form hypotheses and their cf discharges are stated at the rule
   (ASFX = YG0dcf.v astack_free_law_cf; FFLX = the two conjuncts of cgif's frame_flag_lawP the rule reads, over ARx;
   SFX = YG05cf.v stack_free_ok_cf).
   THIRD RULE, aj_set_shadow_at_x: cgif's frame-area set_shadow call rule (cgif_rgb_fuzzer lib/YC05.v:206) over
   ajournal_x for FCiface's aset_shadow_realizes_x, taken from WalkH6's set-shadow-v2.patch (cold/h-hpreset-7-walk-H6
   321efcb143d) unchanged but for its comment.
   Rule 24: no ajournal_x port of aj_stack_malloc_at or aj_flag_store existed on any branch read (WalkS8a confirmed,
   2026-10-28 ~23:40Z; h-hpreset-7 stopped c-omx-alloc's lane for both); cgif's released YCbq.v is the source ported.
   Numerals: 0, 10 (cgif's class range), 16 (stack alignment), 64 (the smallest frame), 4096 (= ESTACK, YG0d.v),
   2 ^ 40, 2 ^ 64: LENGTH / DERIVED. No ADDRESS. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSx.v, with its module names changed; 817 of its 892 lines of code are new or changed and 286 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PRW_put_string_t.v, with its numbers changed; 997 of its 1155 lines of code are new or changed and 734 lines of the source are left out. *)
(* fuzz_preset image A, slice S7b (WalkS7b.S7bPutString.PsLoop): put_string's walk, the LOOP lane: from the loop head
   (A 0x884ec = AF_put_string + 384) through the byte test, the run put of a special byte (A 0x88514) and the re-poison /
   shadow-checked load of the next byte (A 0x885b8 = AF_put_string + 588 .. 0x88604), to the escape join (AF + 428,
   the ESC premise), the next head (AF + 384) or the tail join (AF + 672, the TAIL premise), over PRW_put_string_base.v.
   Rule 24: not in released set (proof-index put_string, 2026-10-28T23:37Z, PS's lookup); segment lemmas only.
   #102 re-fit (WalkS7bR.PutStringF.PsLoopF, the internal file PS102-CONTRACT.md (L)): the continuations quantify their float state; the
   two steps run at the Section's fx; ps_loop is proved after that Section closes, with put's text at every fx.
   No address literal: entries, return sites and literals are by name (A_prog_slot, AF_put_string).
   The re-hiding move: the whole loop lies after the opening-quote put (put reallocs when it grows, a crossing call),
   so its joins are ps_commonR at wle' SEGS RZ_cf, its stretches and branches run at that relation, and the two steps,
   the continuations and ps_loop conclude SRr' SEGS RZ_cf. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the step relation over a world relation and the re-hiding relation (SRrG, wle', SRr'), the fixed zone RZ_cf and
   the branch over a world relation (paj_branchR) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_S7bKit PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S7a_WriterRet S7a_WriterLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_put_string_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia must see the division equations: the realignment is a mod 32 (never rely on an inherited flag) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's generated numbers (PRH_Img.v) are the PrhImg the texts read *)
#[local] Existing Instance prh_img_A.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
(* The kit's non-primary room invariant (PRH_Base.v PrhRoomLive, owner a Theorem Labs lane) *)
Context {RL : PrhRoomLive}.
Section f.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* the entry (DERIVED: slot * 4, PAImg_prog A_entry_put_string) *)
Hypothesis Hent : SIGMA AS_put_string = BASE + AF_put_string.
(* image-link gap, proposed PALib field pal_got_uar *)
Hypothesis Huar : as_got_uar B = VAL (A_OBJ 1).
(* image facts, discharged at PI_prog_A: the GOT words of the shadow base and of the use-after-return flag, the shadow
   cell and the flag cell lie in the image's segments and apart *)
Hypothesis Hobj : forall i, 0 <= i < 8 ->
  in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\ in_img SEGS (VAL (A_OBJ 1) + i).
Hypothesis HOBJ : ps_objs_disj.
Hypothesis HUARC : ps_uar_ok B.
(* the engine's / instance's side conditions of the frame-area step (YGcallSx.v Section x, owner c-omx-alloc) *)
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env SEGS B.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
(* frame class 0's text in the m-form (YGcallMxmn astack_malloc_realizes_xm, owner R4) and its entry; image-link gap *)
Hypothesis ASM0 : astack_malloc_realizes_xm SEGS B ARx 0.
Hypothesis Hsm0 : pc_stack_malloc (as_code B) 0 = SIGMA AS___asan_stack_malloc_0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, discharged by a8's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
(* the registered zero-shadow ranges are granule-aligned (YG0f.v asyms_ok's aso_zshadow; image fact of the instance,
   discharged at PI_prog_A) *)
Hypothesis ASO : asyms_ok B.
(* image fact, discharged at PI_prog_A by reflexivity (PAImg_prog.v:408 pa_lo := IMG_LO; pa_hi := IMG_TOP): the
   instance's image band is image A's (kept_at's image arms are per instance since 2026-10-29; WalkS7bR's ruling) *)
Hypothesis HPAB : pa_lo = IMG_LO /\ pa_hi = IMG_TOP.
(* the image's shadow is visible (PRW_HShadow.v ARx_img_shadow_vis, owner a8 YImgShadowCoverCf.v) and every live fake
   frame's shadow hull (ARx_frame_hull_vis, owner a8 YGcfFsVis.v) *)
Hypothesis HIMGSH : ARx_img_shadow_vis SEGS ARx.
Hypothesis HFHULL : ARx_frame_hull_vis SEGS ARx.
(* alloc.c's six statics and fuzz_preset.c's g_own_ran_out (the ledger's globals, prh_pst, PRH_Base.v:752-755) are image bytes the runtime does not own, apart from errno, and none
   lies in the read-only band (YC1fPx's PST_ok; the S7b walk's pj_write takes the same texts; image facts) *)
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).
(* the generic memory invariant (h-hpreset-7's 12:18Z ruling) and its laws; the walk crosses calls *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNI := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS Pm PLAW.
Let NTRUNTO := SRr_run_to_pi_AJx B ARx LAWS.
(* the tokenless runner and the branch at the re-hiding relation: every stretch of this file runs after a put *)
Let NTRUNTOI := SRr_run_to_pi_AJx_invR B ARx LAWS Pm PLAW (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BR := paj_branchR (PI := PA) (wle' SEGS RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx).
Variable CTX0 : list (list Z).
(* put's text (the kit's tput_specX, WalkS7a's walk): the ONE callee-text use of put in this file *)
Hypothesis PUT : tput_specX (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
(* the double-quote literal .str.17 put_string puts twice (IMAGE FACT, discharged at PI_prog_A; pj_write's HLIT form):
   its byte is the image's, its shadow the read-only global's, at every state *)
Hypothesis HLIT17 : forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (ps_str 65) [34] /\ kept_at B [] (ps_str 65) 1.
(* the base file's lemmas at this section's variables and hypotheses *)
Local Notation ps_entry := (ps_entry B ARx LAWS TL Huar Hobj HOBJ HUARC).
Local Notation prhW_out_kept := (prhW_out_kept B ARx LAWS).
Local Notation prh_ledger_kept := (prh_ledger_kept B).
Local Notation ps_arodata_keep := (ps_arodata_keep B).
Local Notation kept_at_nil_lam := (kept_at_nil_lam B).
Local Notation ps_put_call := (ps_put_call B ARx LAWS segs_low CTX0 PUT).
Local Notation ps_put_step := (ps_put_step B ARx LAWS segs_low HPAB HPSTRO Pm PCALL CTX0 PUT).
Local Notation ps_pre := (ps_pre B ARx CTX0).
Local Notation ps_head := (ps_head B ARx Pm).
Local Notation ps_tail := (ps_tail B ARx Pm).
Local Notation ps_commonR := (ps_commonR B ARx Pm).
Local Notation ps_Qfin := (ps_Qfin B ARx Pm).
Local Notation kept_at_blk := (kept_at_blk B).
Local Notation blk_kept_at := (blk_kept_at B).
Local Notation kept_at_bounds := (kept_at_bounds B ARx LAWS HPAB).
Local Notation str_notin_fp := (str_notin_fp B ARx LAWS).
Local Notation cstr_from_entryR := (cstr_from_entryR B ARx HPSTRO).
Local Notation str_shadow_at := (str_shadow_at B ARx LAWS ASO HIMGSH HPAB).
Local Notation kept_at_loc := (kept_at_loc B ARx LAWS HPAB).
Local Notation ledger_blocks_disj := (ledger_blocks_disj B ARx LAWS).
Local Notation blk_src_disj := (blk_src_disj B ARx LAWS).
Local Notation hblock_shadow := (hblock_shadow B ARx LAWS).

Local Notation ps_common_frameR := (ps_common_frameR B ARx LAWS segs_low HW PST_ok Pm CTX0).
Local Notation ps_esc := (ps_esc B ARx Pm).
Local Notation ps_next := (ps_next B ARx Pm).

(* ---- the seated states (MEASURED: the internal file build-20261029T151134Z, the four head cases and
   the four next cases) ---- *)
(* u's shadow granule (F + 32's cell, at SHF + 4): the only byte the loop's own stretches write *)
Definition psl_shf : YP09.region := YP09.mkRegion (Some 22%nat) 4 5 4 5 [].
(* the loop head (A 0x884ec = AF + 384): the registers as atoms, that one shadow byte *)
Definition psl_ssH : sstate := mkSS (AF_put_string + 384) sr_atoms [psl_shf] None (mkFacts [] [] []).
(* the re-poison join (A 0x885b8 = AF + 588): the same shadow byte, the next byte's shadow cell (atom 33, its value
   atom 34), the next byte itself at s12 = s + i + 1 (atom 35), the two words R + 8 / R + 16 (the frame F, atom 32).
   The alias declares atom 33 as the shadow address of s4 + 1 *)
Definition psl_shb : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition psl_byt : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition psl_rblk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 32 0))].
Definition psl_factsN : facts :=
  mkFacts [(34%nat, mkAF 0 7 0); (35%nat, mkAF 0 255 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 24 1) (SLit 3)) (SOff 23 0), SOff 33 0)].
Definition psl_ssN : sstate :=
  mkSS (AF_put_string + 588) sr_atoms [psl_shf; psl_shb; psl_byt; psl_rblk] None psl_factsN.
(* the seats' envs: the join's registers are atoms 0 .. 31; the next join's four extras are F, the next byte's
   shadow address, its shadow byte and the byte *)
Definition psl_EH (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition psl_EN (regs : bvmap 5 word) (F SHS sv b : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 F; Z_to_bv 64 SHS; Z_to_bv 64 sv; Z_to_bv 64 b]).

(* ---- the continuations the loop takes and gives (the internal file PS102-CONTRACT.md (L)): FLOAT-FREE, each quantifies the float state
   it runs at (frm = 0, the entry's callee-saved f registers), so the loop's induction carries them across escapes
   (PRW_put_string_a.v's KH / KT and PRW_put_string_e.v's ps_esc_run at fxc). Each runs after a put (a crossing call),
   so each concludes SRr' SEGS RZ_cf ---- *)
Definition psl_HEADC (X : psx) (i : nat) : Prop :=
  forall fxc : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fxc) -> fregs_kept_x (x_fx X) fxc ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc,
    PRW_put_string_base.ps_head (fx := fxc) B ARx Pm X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
    SRr' SEGS RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
      (ps_Qfin X).
Definition psl_NEXTC (X : psx) (i : nat) : Prop :=
  forall fxc : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fxc) -> fregs_kept_x (x_fx X) fxc ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc,
    PRW_put_string_base.ps_next (fx := fxc) B ARx Pm X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
    SRr' SEGS RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + (AF_put_string + 588))) memc (seg_rom SEGS)) mdc)
      (ps_Qfin X).
Definition psl_TAILC (X : psx) : Prop :=
  forall fxc : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fxc) -> fregs_kept_x (x_fx X) fxc ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc,
    PRW_put_string_base.ps_tail (fx := fxc) B ARx Pm X pos j P lyc Sc Hpc Wc regsc memc mdc kc ->
    SRr' SEGS RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + (AF_put_string + 672))) memc (seg_rom SEGS)) mdc)
      (ps_Qfin X).
Definition psl_ESCC (X : psx) : Prop :=
  forall fxc : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fxc) -> fregs_kept_x (x_fx X) fxc ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc,
    PRW_put_string_base.ps_esc (fx := fxc) B ARx Pm X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  (forall fx' : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x (x_fx X) fx' ->
   forall lyn Sn Hpn Wn regsn memn mdn kn,
     PRW_put_string_base.ps_next (fx := fx') B ARx Pm X pos i (S i) (P ++ [WriterSpec.esc (nth i (x_bs X) 0)])
       lyn Sn Hpn Wn regsn memn mdn kn ->
     SRr' SEGS RZ_cf Wn (mkCfg (@mkst fx' regsn (Z_to_bv 64 (BASE + (AF_put_string + 588))) memn (seg_rom SEGS))
       mdn) (ps_Qfin X)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fxc regsc (Z_to_bv 64 (BASE + (AF_put_string + 428))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin X).

(* ---- pure facts about the string and the plan ---- *)
(* a byte of the NUL-terminated image of the string: inside it, or the NUL at its end *)
Lemma psl_byte_in : forall (bs : list Z) k, (k <= length bs)%nat -> nth k (bs ++ [0]) 0 <> 0 ->
  (k < length bs)%nat /\ nth k (bs ++ [0]) 0 = nth k bs 0.
Proof.
intros bs k Hk Hc. destruct (Nat.eq_dec k (length bs)) as [-> | Hne].
- exfalso. rewrite nth_middle in Hc. exact (Hc eq_refl).
- assert (Hlt : (k < length bs)%nat) by lia. split; [exact Hlt | apply app_nth1; exact Hlt].
Qed.
Lemma psl_byte_nul : forall (bs : list Z) k, Forall (fun x => x <> 0) bs -> (k <= length bs)%nat ->
  nth k (bs ++ [0]) 0 = 0 -> k = length bs.
Proof.
intros bs k Hnz Hk Hc. destruct (Nat.eq_dec k (length bs)) as [-> | Hne]; [reflexivity|].
exfalso. assert (Hlt : (k < length bs)%nat) by lia. rewrite app_nth1 in Hc by exact Hlt.
rewrite Forall_forall in Hnz. exact (Hnz (nth k bs 0) (nth_In bs 0 Hlt) Hc).
Qed.
(* the head's plan at a byte that is put as itself: the same plan at the next join *)
Lemma psl_plan_ns : forall (bs : list Z) P i j, (j <= i)%nat -> (i < length bs)%nat ->
  WriterSpec.special (nth i bs 0) = false ->
  [34] :: WriterSpec.spieces_run [] bs = P ++ WriterSpec.spieces_run (firstn (i - j) (skipn j bs)) (skipn i bs) ->
  [34] :: WriterSpec.spieces_run [] bs =
    P ++ WriterSpec.spieces_run (firstn (S i - j) (skipn j bs)) (skipn (S i) bs).
Proof.
intros bs P i j Hji Hi Hsp Heq. rewrite Heq. f_equal.
rewrite (skipn_nth_cons bs i Hi), (sr_nonspec _ _ _ Hsp), (firstn_skipn_snoc bs i j Hji Hi). reflexivity.
Qed.
(* the next join's plan when the string is consumed: the pending run is its tail *)
Lemma psl_plan_tail : forall (bs : list Z) P i j, (j <= S i)%nat -> S i = length bs ->
  [34] :: WriterSpec.spieces_run [] bs =
    P ++ WriterSpec.spieces_run (firstn (S i - j) (skipn j bs)) (skipn (S i) bs) ->
  [34] :: WriterSpec.spieces_run [] bs = P ++ [skipn j bs].
Proof.
intros bs P i j Hji Hlen Heq. rewrite Heq. f_equal.
rewrite (skipn_all2 (n := S i) bs) by lia. cbn [WriterSpec.spieces_run]. f_equal.
apply firstn_all2. rewrite length_skipn. lia.
Qed.
(* the head's plan at a special byte: the pending run is one piece, the escape the next *)
Lemma psl_plan_esc : forall (bs : list Z) P i j, (j <= i)%nat -> (i < length bs)%nat ->
  WriterSpec.special (nth i bs 0) = true ->
  [34] :: WriterSpec.spieces_run [] bs = P ++ WriterSpec.spieces_run (firstn (i - j) (skipn j bs)) (skipn i bs) ->
  WriterSpec.spieces bs =
    P ++ firstn (i - j) (skipn j bs)
         :: WriterSpec.esc (nth i bs 0) :: WriterSpec.spieces_run [] (skipn (S i) bs) ++ [[34]] /\
  [34] :: WriterSpec.spieces_run [] bs =
    (P ++ [firstn (i - j) (skipn j bs)]) ++
      WriterSpec.esc (nth i bs 0) :: WriterSpec.spieces_run [] (skipn (S i) bs).
Proof.
intros bs P i j Hji Hi Hsp Heq.
assert (HE : [34] :: WriterSpec.spieces_run [] bs =
  P ++ firstn (i - j) (skipn j bs) :: WriterSpec.esc (nth i bs 0) :: WriterSpec.spieces_run [] (skipn (S i) bs)).
{ rewrite Heq. f_equal. rewrite (skipn_nth_cons bs i Hi). exact (sr_spec _ _ _ Hsp). }
split.
- unfold WriterSpec.spieces. rewrite app_comm_cons, HE, <- app_assoc. reflexivity.
- rewrite <- app_assoc. exact HE.
Qed.
(* a window of the string's bytes, from its NUL-terminated image *)
Lemma psl_nth_fs : forall (l : list Z) j n k, (k < n)%nat -> nth k (firstn n (skipn j l)) 0 = nth (j + k) l 0.
Proof.
intros l j n k Hk. rewrite nth_firstn. replace (k <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
apply nth_skipn.
Qed.
Lemma psl_len_fs : forall (l : list Z) j i, (i <= length l)%nat -> length (firstn (i - j) (skipn j l)) = (i - j)%nat.
Proof. intros l j i Hi. rewrite length_firstn, length_skipn. lia. Qed.

(* ---- arithmetic the engine's values need ---- *)
Lemma psl_and255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof.
intros c Hc. replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 8) with 256. apply Z.mod_small. exact Hc.
Qed.
(* an atom's value, and an atom plus a literal offset *)
Lemma psl_atom_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c Hn Hv Hvc. apply bv_eq. rewrite unsigned_lit_small by exact Hvc.
change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
apply U_atom_off; assumption.
Qed.
(* s11 at the run put (A 0x88504 `andi s11, s2, 255`) *)
Lemma psl_and_val : forall E p (c : Z), ew E p = Z_to_bv 64 c -> 0 <= c < 256 ->
  sv_denot E (SAlu ALU_AND (SOff p 0) (SLit 255)) = Z_to_bv 64 c.
Proof.
intros E p c Hp Hc. apply bv_eq. rewrite unsigned_lit_small by lia.
change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff p 0) (SLit 255))))
  with (U E (SAlu ALU_AND (SOff p 0) (SLit 255))).
rewrite U_SAlu, (U_atom E p c Hp ltac:(lia)), U_SLit. cbn [zalu_raw].
assert (H255 : zcanon 255 = 255) by (unfold zcanon, M64; vm_compute; reflexivity).
rewrite H255, psl_and255 by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* a2 at the run put (A 0x88508 `sub a2, s8, s10`): the run's length *)
Lemma psl_sub_val : forall E p q (a b : Z), ew E p = Z_to_bv 64 a -> ew E q = Z_to_bv 64 b ->
  0 <= b -> b <= a -> a < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff p 0) (SMd M_MUL (SOff q 0) (SLit (-1)))) = Z_to_bv 64 (a - b).
Proof.
intros E p q a b Hp Hq Hb Hba Ha. apply bv_eq. rewrite unsigned_lit_small by lia.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff p 0) (SMd M_MUL (SOff q 0) (SLit (-1))))))
  with (U E (SAlu ALU_ADD (SOff p 0) (SMd M_MUL (SOff q 0) (SLit (-1))))).
rewrite U_SAlu, U_SMd, (U_atom E p a Hp ltac:(lia)), (U_atom E q b Hq ltac:(lia)), U_SLit.
cbn [zalu_raw zmd_raw].
assert (Hm1 : zcanon (-1) = 2 ^ 64 - 1) by (unfold zcanon, M64; vm_compute; reflexivity).
rewrite Hm1. unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia.
replace (a + b * (2 ^ 64 - 1)) with (a - b + b * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* the partial granule's test of the shadow-checked load of s[i + 1] (A 0x885ec `blt (a & 7), shadow`) *)
Lemma psl_slow_lt : forall E p q (a sv : Z), ew E p = Z_to_bv 64 (a - 1) -> ew E q = Z_to_bv 64 sv ->
  0 <= a - 1 -> a < 2 ^ 64 -> 0 < sv < 8 -> a mod 8 < sv ->
  branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SOff p 1) (SLit 7))) (sv_denot E (SOff q 0)) = true.
Proof.
intros E p q a sv Hp Hq Ha1 Ha Hvr Hlt.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E (SOff q 0)). fold (U E (SAlu ALU_AND (SOff p 1) (SLit 7))).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E p (a - 1) 1 Hp ltac:(lia) ltac:(lia)), U_SLit, (U_atom E q sv Hq ltac:(lia)).
change (zcanon 7) with 7. replace (a - 1 + 1) with a by lia.
rewrite (YP0e.zcanon_id (Z.land a 7)) by (pose proof (YP0m.Z_land_upper a 7 ltac:(lia)); unfold M64; lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
rewrite !YP0e.swrap64_id by (unfold half64; lia). apply Z.ltb_lt. lia.
Qed.
(* the shadow address of the next byte, as the alias of the seat declares it *)
Lemma psl_shadow_decl1 : forall E (p b s : nat) (pv Bs : Z),
  ew E p = Z_to_bv 64 pv -> 0 <= pv -> pv + 1 < 2 ^ 64 -> ew E b = Z_to_bv 64 Bs ->
  ew E s = Z_to_bv 64 (Bs + (pv + 1) / 8) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 1) (SLit 3)) (SOff b 0)) = sv_denot E (SOff s 0).
Proof.
intros E p b s pv Bs Hp Hpv Hpv2 Hb Hs. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, (U_atom_off E p pv 1 Hp ltac:(lia) ltac:(lia)), !U_SOff, Hb, Hs.
rewrite !Z.add_0_r, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold zcanon, M64. rewrite (Z.mod_mod Bs) by lia. rewrite Z.add_mod_idemp_r by lia.
rewrite (Z.mod_mod (Bs + (pv + 1) / 8)) by lia. f_equal. lia.
Qed.
(* one byte read back through the view *)
Lemma psl_aview1 : forall (H : word -> bool) (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview SEGS H mem a = Some v.
Proof.
intros H mem a v Hm Hv. pose proof (Hm 0%nat ltac:(lia)) as Hb.
replace (a + Z.of_nat 0) with a in Hb by lia.
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
rewrite (Z.mod_small v 256) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hv.
Qed.
(* the string's granule is not u's granule: the string lies outside the fake frame *)
Lemma psl_shs_ne : forall a F, F mod 32 = 0 -> 0 <= F -> 0 <= a -> (a < F \/ F + 64 <= a) -> a / 8 <> F / 8 + 4.
Proof.
intros a F H32 HF Ha Hd Heq.
assert (HF8 : 8 * (F / 8) = F) by lia.
assert (Ha8 : 8 * (a / 8) <= a < 8 * (a / 8) + 8) by lia.
lia.
Qed.
(* a byte the loop's stretches keep: they write u's shadow granule only *)
Lemma psl_keep_av : forall E rs (H : word -> bool) (m m' : word -> option byte) (lo hi : Z),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall x, in_wrange E rs x -> lo <= x < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> (a < lo \/ hi <= a) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi Hfr Hw a Ha Hout.
apply (kept_of_frame E rs H m m' (fun x => x = a) Hfr); [|reflexivity].
intros x ->. split; [exact Ha|]. intros Hin. pose proof (Hw a Hin). lia.
Qed.

(* ---- the walk's facts at a join of the loop (after a put: the join at wle' SEGS RZ_cf) ---- *)
Lemma psl_frame_facts : forall X ch pos P lyc Sc Hpc Wc memc mdc kc,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  In (0, pos) (frames Sc) /\ frame_addr lyc 0 pos = x_F X pos /\
  x_F X pos mod 32 = 0 /\ 4096 <= x_F X pos /\ x_F X pos + 64 <= YM05.alloc_ceiling /\
  (x_F X pos + 64 <= kLowShadowBeg \/ (kHighMemBeg <= x_F X pos /\ x_F X pos + 64 <= ASAN_CEIL)) /\
  (forall a, x_F X pos <= a < x_F X pos + 64 -> apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 8 -> apresent (w_H Wc) memc (x_SHF X pos + i) /\ ~ aowned B lyc Sc (x_SHF X pos + i)) /\
  x_SHF X pos = SHADOW_OFF + x_F X pos / 8.
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM.
pose proof HCOM as (HJ & _).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as HLLE. pose proof (ajxR_frs HJ) as HFRS.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
assert (EF : frame_addr lyc 0 pos = x_F X pos) by (unfold x_F, frame_addr; rewrite HlyF; reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR Hin) as (HF32 & HFapp & HFpres & HFsh).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite EF in HF32, HFapp, HFpres, HFsh, HF4096, HFceil. change (fs_frame_bytes 0) with 64 in *.
change (64 / 8) with 8 in HFsh.
assert (HSHF : x_SHF X pos = SHADOW_OFF + x_F X pos / 8) by (unfold x_SHF, PS_SB; reflexivity).
split; [exact Hin|]. split; [exact EF|]. split; [exact HF32|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [unfold in_app in HFapp; lia|]. split; [exact HFpres|].
split; [intros i Hi; rewrite HSHF; exact (HFsh i Hi) | exact HSHF].
Qed.

(* the string at a join of the loop: its bytes, its home, its shadow (PRW_put_string_a.v's derivation at the first
   byte, at an arbitrary join) *)
Lemma psl_str_now : forall X ch pos P lyc Sc Hpc Wc memc mdc kc,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  cstr Wc memc (x_s X) (x_bs X) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (x_s X) (x_n X + 1) /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (x_s X) (x_n X + 1) /\
  4096 <= x_s X /\ x_s X + x_n X + 1 <= ASAN_CEIL /\
  (x_s X + (x_n X + 1) <= kLowShadowBeg \/ kHighMemBeg <= x_s X) /\
  (x_s X + (x_n X + 1) <= x_F X pos \/ x_F X pos + 64 <= x_s X).
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & Hout0 & Hled0 & Hcstr0 & Hkept0 &
  Hdisj0 & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
pose proof HCOM as (HJ & _ & _ & _ & _ & (ok & ranc & bufc & Lamc & peakc & _ & _ & Hled & _ & Hkept & Hlive & _) & _).
pose proof (ajxR_ar HJ) as HARc.
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM) as (Hin & _ & _ & _ & _ & _ & _ & _ & _).
assert (Hn1 : 0 < x_n X + 1) by (unfold x_n; lia).
destruct (kept_at_bounds (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) (x_Lam X) (x_peak X) _ _ (x_ran X)
  (x_s X) _ HAR0 Hled0 Hkept0 Hn1) as (Hs4096 & HsC).
assert (HSPc : ASAN_CEIL + STK_put_string <= x_sp X) by (unfold ASAN_CEIL, x_sp; clear - Hceil Hslo; lia).
assert (Hso : x_s X + (x_n X + 1) <= x_o X) by (clear - HsC HSPc Ho1 HSTK208; lia).
assert (Hcase0 : WriterApp.w_cap (x_st X) <> 0 -> In (x_buf X, WriterApp.w_cap (x_st X)) (x_Lam X)).
{ intros Hc0. destruct Hout0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz0 & _) | (_ & HinL & _)]); [lia | exact HinL]. }
assert (Hdisj0' : WriterApp.w_cap (x_st X) = 0 \/ x_s X + (x_n X + 1) <= x_buf X \/
  x_buf X + WriterApp.w_cap (x_st X) <= x_s X) by (clear - Hdisj0; lia).
assert (Hnfp : forall a, x_s X <= a < x_s X + x_n X + 1 -> ~ inFP (x_FP X) a).
{ intros a Ha. unfold x_FP.
  apply (str_notin_fp (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) (x_Lam X) (x_peak X) _ _ (x_ran X)
    (x_o X) (x_buf X) (WriterApp.w_cap (x_st X)) (x_s X) _ HAR0 Hled0 Hkept0 Hn1 Hdisj0' Hcase0 Hso a).
  clear - Ha; lia. }
assert (HCSTR : cstr Wc memc (x_s X) (x_bs X)).
{ apply (cstr_from_entryR (wle' SEGS RZ_cf) _ _ (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) _ lyc Sc
    Hpc Wc memc mdc _
    (x_Lam X) (x_peak X) _ _ (x_ran X) Lamc peakc _ _ ranc (x_s X) (x_bs X) HJ Hled0 Hled (proj1 Hcstr0) Hkept0
    Hlive Hnfp (ps_fp_closed B ARx LAWS CTX0 X ch Hpre)). }
destruct (str_shadow_at lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (x_s X) _ HARc Hled Hkept Hn1) as (HRA & HHV).
destruct (kept_at_loc lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (x_s X) _ 0 pos HARc Hled Hkept Hn1 Hin
  ltac:(vm_compute; reflexivity)) as (Hsapp & HsF).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM) as (_ & EF & _).
change (fs_frame_bytes 0) with 64 in HsF.
split; [exact HCSTR|]. split; [exact HRA|]. split; [exact HHV|]. split; [exact Hs4096|].
split; [clear - HsC; lia|]. split; [exact Hsapp|].
rewrite <- EF. exact HsF.
Qed.

(* ---- the seats ---- *)
Lemma psl_seat_H : forall X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_pre X ch -> ps_head X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  img_env VAL A_LIM (psl_EH regsc) /\
  st_ok_pi SEGS VAL (psl_EH regsc) psl_ssH
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS))).
Proof.
intros X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc Hpre Hh.
pose proof Hh as (HCOM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & _).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM)
  as (_ & _ & _ & HF4096 & HFceil & _ & _ & HFsh & HSHF).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSHFr : SHADOW_OFF + 512 <= x_SHF X pos /\ x_SHF X pos + 8 <= kHighMemBeg).
{ rewrite HSHF. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. split; lia. }
assert (HEI : img_env VAL A_LIM (psl_EH regsc)) by (unfold psl_EH; apply Eimg_env).
assert (E22 : ew (psl_EH regsc) 22 = Z_to_bv 64 (x_SHF X pos)).
{ unfold psl_EH. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 22 22%bv eq_refl). exact R22. }
assert (R22b : base_val (psl_EH regsc) (Some 22%nat) = x_SHF X pos)
  by (cbn [base_val]; rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF, kHighMemBeg in HSHFr; lia).
split; [exact HEI|].
rewrite restrict_mkst_fx. unfold psl_ssH. apply pa_entry_st_ok_full.
- unfold psl_EH. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, psl_shf.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst]. rewrite R22b.
  unfold SHADOW_OFF, kHighMemBeg in HSHFr.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). replace (x_SHF X pos + o) with (x_SHF X pos + 4) by lia.
  exact (proj1 (HFsh 4 ltac:(lia))).
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- repeat split; exact I.
Qed.

Lemma psl_seat_N : forall X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc F SHS a sv b,
  ps_pre X ch -> ps_next X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  F = x_F X pos -> a = x_s X + Z.of_nat i + 1 -> SHS = SHADOW_OFF + a / 8 ->
  0 <= sv < 8 -> 0 <= b < 256 ->
  aview SEGS (w_H Wc) memc SHS = Some sv -> aview SEGS (w_H Wc) memc a = Some b ->
  (a < F \/ F + 64 <= a) -> (a < kLowShadowBeg \/ kHighMemBeg <= a) -> 4096 <= a <= ASAN_CEIL ->
  img_env VAL A_LIM (psl_EN regsc F SHS sv b) /\
  st_ok_pi SEGS VAL (psl_EN regsc F SHS sv b) psl_ssN
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 588))) memc (seg_rom SEGS))).
Proof.
intros X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc F SHS a sv b Hpre Hn HFe Hae HSe Hsvr Hbr Hsh Hby Hdf Hdl Har.
pose proof Hn as (HCOM & _ & _ & _ & R2 & _ & _ & R8 & R9 & _ & R20 & _ & R22 & R23 & R24 & _ & _ &
  W8 & W16 & _).
pose proof Hpre as (HFPRE & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM)
  as (_ & _ & HF32 & HF4096 & HFceil & HFloc & _ & HFsh & HSHF).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC. unfold ASAN_CEIL in Har.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
assert (HSHFr : SHADOW_OFF + 512 <= x_SHF X pos /\ x_SHF X pos + 8 <= kHighMemBeg).
{ rewrite HSHF. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  clear - HF4096 HFceil HC. split; lia. }
assert (HSHSr : SHADOW_OFF <= SHS < kHighMemBeg).
{ rewrite HSe. unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. clear - Har HC. lia. }
assert (HSHSne : SHS <> x_SHF X pos + 4).
{ rewrite HSe, HSHF. intros Heq.
  exact (psl_shs_ne a (x_F X pos) HF32 ltac:(clear - HF4096; lia) ltac:(clear - Har; lia)
    ltac:(clear - Hdf HFe; lia) ltac:(clear - Heq; lia)). }
assert (HEI : img_env VAL A_LIM (psl_EN regsc F SHS sv b)) by (unfold psl_EN; apply Eimg_env).
assert (Ereg_ : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (psl_EN regsc F SHS sv b) n = getr regsc r).
{ intros n r Hn32 Hr. unfold psl_EN. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regsc _ n r Hr). }
assert (E32 : ew (psl_EN regsc F SHS sv b) 32 = Z_to_bv 64 F)
  by (unfold psl_EN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew (psl_EN regsc F SHS sv b) 33 = Z_to_bv 64 SHS)
  by (unfold psl_EN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew (psl_EN regsc F SHS sv b) 34 = Z_to_bv 64 sv)
  by (unfold psl_EN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew (psl_EN regsc F SHS sv b) 35 = Z_to_bv 64 b)
  by (unfold psl_EN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E9 : ew (psl_EN regsc F SHS sv b) 9 = Z_to_bv 64 (x_R X))
  by (rewrite (Ereg_ 9%nat 9%bv) by (lia || reflexivity); exact R9).
assert (E20 : ew (psl_EN regsc F SHS sv b) 20 = Z_to_bv 64 a)
  by (rewrite (Ereg_ 20%nat 20%bv) by (lia || reflexivity); rewrite Hae; exact R20).
assert (E22 : ew (psl_EN regsc F SHS sv b) 22 = Z_to_bv 64 (x_SHF X pos))
  by (rewrite (Ereg_ 22%nat 22%bv) by (lia || reflexivity); exact R22).
assert (E23 : ew (psl_EN regsc F SHS sv b) 23 = Z_to_bv 64 PS_SB)
  by (rewrite (Ereg_ 23%nat 23%bv) by (lia || reflexivity); exact R23).
assert (E24 : ew (psl_EN regsc F SHS sv b) 24 = Z_to_bv 64 (x_s X + Z.of_nat i))
  by (rewrite (Ereg_ 24%nat 24%bv) by (lia || reflexivity); exact R24).
assert (HRr : YM05.alloc_ceiling <= x_R X /\ x_R X + 88 <= 2 ^ 47).
{ unfold x_R, x_sp, PS_R in *. clear - HR Hceil Hslo Hstk0 HSTK208 H47 Hshi. lia. }
assert (R9b : base_val (psl_EN regsc F SHS sv b) (Some 9%nat) = x_R X)
  by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; clear - HRr HC; lia).
assert (R20b : base_val (psl_EN regsc F SHS sv b) (Some 20%nat) = a)
  by (cbn [base_val]; rewrite E20; apply unsigned_lit_small; clear - Har HC; lia).
assert (R22b : base_val (psl_EN regsc F SHS sv b) (Some 22%nat) = x_SHF X pos)
  by (cbn [base_val]; rewrite E22; apply unsigned_lit_small;
      unfold SHADOW_OFF, kHighMemBeg in HSHFr; clear - HSHFr; lia).
assert (R33b : base_val (psl_EN regsc F SHS sv b) (Some 33%nat) = SHS)
  by (cbn [base_val]; rewrite E33; apply unsigned_lit_small;
      unfold SHADOW_OFF, kHighMemBeg in HSHSr; clear - HSHSr; lia).
assert (HFr2 : 4096 <= F /\ F + 64 <= YM05.alloc_ceiling) by (rewrite HFe; clear - HF4096 HFceil; lia).
split; [exact HEI|].
rewrite restrict_mkst_fx. unfold psl_ssN. apply pa_entry_st_ok_full.
- unfold psl_EN. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold psl_shf, psl_shb, psl_byt, psl_rblk.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  + rewrite R22b. unfold SHADOW_OFF, kHighMemBeg in HSHFr.
    split; [clear - HSHFr; lia|]. split; [clear - HSHFr; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    replace (x_SHF X pos + o) with (x_SHF X pos + 4) by (clear - Ho; lia).
    exact (proj1 (HFsh 4 ltac:(lia))).
  + rewrite R33b. unfold SHADOW_OFF, kHighMemBeg in HSHSr.
    split; [clear - HSHSr; lia|]. split; [clear - HSHSr; lia|]. split; [intros o Ho; clear - Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (psl_EN regsc F SHS sv b) _ SHS 0 1 (SOff 34 0) sv);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem1_of_aview _ _ _ _ Hsh).
  + rewrite R20b. split; [clear - Har HC; lia|]. split; [clear - Har HC; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (psl_EN regsc F SHS sv b) _ a 0 1 (SOff 35 0) b);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem1_of_aview _ _ _ _ Hby).
  + rewrite R9b. split; [clear - HRr HC; lia|]. split; [clear - HRr HC; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    [ apply (chunk_ok_val SEGS (psl_EN regsc F SHS sv b) _ (x_R X) 8 8 (SOff 32 0) F);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HFr2 HC; lia | zside
        | rewrite HFe; exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W8)]
    | apply (chunk_ok_val SEGS (psl_EN regsc F SHS sv b) _ (x_R X) 16 8 (SOff 32 0) F);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HFr2 HC; lia | zside
        | rewrite HFe; exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W16)] ].
- apply pairwise_disjoint_of_extents.
  unfold psl_shf, psl_shb, psl_byt, psl_rblk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite R22b, R33b, R20b, R9b.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *.
  clear - HSHFr HSHSr HSHSne Hdl Har HRr HC. repeat split; lia.
- unfold psl_factsN. split; [|split].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E34, E35, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    clear - Hsvr Hbr. repeat split; lia.
  + exact I.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply (psl_shadow_decl1 (psl_EN regsc F SHS sv b) 24 23 33 (x_s X + Z.of_nat i) PS_SB E24
      ltac:(clear - Har Hae; lia) ltac:(clear - Har Hae HC; lia) E23).
    rewrite E33, HSe, Hae. unfold PS_SB. reflexivity.
Qed.

(* ---- the seven realigned slots every join of the loop carries ---- *)
Definition psl_rwords (X : psx) (pos : Z) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 8) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 16) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 24) = Some (ps_str 91) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 32) = Some (ps_str 89) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 40) = Some (ps_str 87) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 48) = Some (ps_str 85) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 56) = Some (ps_str 93).
Lemma psl_rwords_keep : forall X pos (W1 W2 : world SEGS) (m1 m2 : word -> option byte),
  psl_rwords X pos W1 m1 ->
  (forall a, x_R X + 8 <= a < x_R X + 64 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  psl_rwords X pos W2 m2.
Proof.
intros X pos W1 W2 m1 m2 (A8 & A16 & A24 & A32 & A40 & A48 & A56) K.
unfold psl_rwords. repeat split;
  [ rewrite <- A8 | rewrite <- A16 | rewrite <- A24 | rewrite <- A32 | rewrite <- A40 | rewrite <- A48
  | rewrite <- A56 ];
  apply rdword_eq_of; intros k Hk; apply K; lia.
Qed.
(* a register of a seated state: the join's own, or a symbolic value *)
Lemma psl_reg_of : forall (H : word -> bool) E ss ms regs0 extra (r q : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned q)) 0 -> getr (ms_regs ms) r = getr regs0 q.
Proof.
intros H E ss ms regs0 extra r q HS HA Hr.
rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
destruct HA as (HA & _). rewrite HA by (pose proof (u5_range q); lia). apply ew_Ereg_reg.
Qed.
Lemma psl_reg_of_ok : forall (H : word -> bool) E ss ms regs0 extra (r q : bv 5),
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned q)) 0 -> getr (ms_regs ms) r = getr regs0 q.
Proof.
intros H E ss ms regs0 extra r q HS HA Hr.
rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
destruct HA as (HA & _). rewrite HA by (pose proof (u5_range q); lia). apply ew_Ereg_reg.
Qed.
Lemma psl_reg_val : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = Z_to_bv 64 v ->
  getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS Hr He. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr, He. reflexivity. Qed.
Lemma psl_reg_val_ok : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = Z_to_bv 64 v ->
  getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS Hr He. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr, He. reflexivity. Qed.
Lemma psl_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity. Qed.
Lemma psl_pres_at : forall regs regs', aregs_preserved regs regs' ->
  forall (r : Z) (q : bv 5), acallee_saved r -> bv_unsigned q = r -> getr regs' q = getr regs q.
Proof. intros regs regs' HP r q Hr Hq. pose proof (HP r Hr) as H. rewrite <- Hq, !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* ---- the re-poison join (AF + 588): u's granule re-poisoned (sb -8, 4(s6)), the shadow-checked load of byte i + 1
   (lb of its shadow byte; when it is nonzero, the partial granule's test `blt (a & 7), shadow`, whose report arm is
   not taken: byte i + 1 is addressable), then the next loop head (AF + 384) when the byte is nonzero, or the tail
   join (AF + 672) at the NUL. All after a put: the stretches and branches at wle' SEGS RZ_cf, the conclusion SRr' ---- *)
Lemma psl_next_step : forall X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_pre X ch -> ps_s0 X -> psl_HEADC X (S i) -> psl_TAILC X ->
  ps_next X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 588))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin X).
Proof.
intros X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc Hpre HS0 HEAD TAIL Hn.
unfold SRr'.
pose proof Hn as (HCOMc & Hji & Hi & Hplan & R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 &
  W8 & W16 & W24 & W32 & W40 & W48 & W56).
pose proof Hpre as (HFPRE & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & HR32).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc)
  as (Hin & EF & HF32 & HF4096 & HFceil & HFloc & HFpres & HFsh & HSHF).
destruct (psl_str_now X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc)
  as (HCSTR & HRA & HHV & Hs4096 & HsC & Hsloc & HsF).
unfold ASAN_CEIL in HsC.
destruct HCSTR as (Hg & Hnz).
assert (HSHFr : SHADOW_OFF + 512 <= x_SHF X pos /\ x_SHF X pos + 8 <= kHighMemBeg).
{ rewrite HSHF. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. clear - HF4096 HFceil HC. split; lia. }
assert (HRr : YM05.alloc_ceiling <= x_R X /\ x_R X + 88 <= x_sp X /\ x_sp X <= 2 ^ 47).
{ unfold x_R, x_sp, PS_R in *. clear - HR Hceil Hslo Hstk0 HSTK208 Hshi H47. lia. }
assert (HRhi : kHighMemBeg <= x_R X) by (unfold kHighMemBeg in *; clear - HRr HC; lia).
(* byte i + 1 of the NUL-terminated string (the NUL when i + 1 = n), and its shadow byte *)
assert (Hi1 : (S i <= length (x_bs X))%nat) by (clear - Hi; lia).
destruct (Hg (S i) ltac:(rewrite length_app; cbn [length]; clear - Hi1; lia)) as (Hbv & Hbr).
replace (x_s X + Z.of_nat (S i)) with (x_s X + Z.of_nat i + 1) in Hbv by (clear - Hi; lia).
destruct (HRA (x_s X + Z.of_nat i + 1) ltac:(unfold x_n; clear - Hi1; lia)) as (sv & Hsv & Hsok).
assert (Hsvr : 0 <= sv < 8) by (unfold saddr_ok in Hsok; clear - Hsok; lia).
unfold shadow_of_addr in Hsv.
assert (Har : 4096 <= x_s X + Z.of_nat i + 1 <= ASAN_CEIL)
  by (unfold ASAN_CEIL; unfold x_n in *; clear - Hs4096 HsC Hi1; lia).
destruct (psl_seat_N X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc (x_F X pos)
  (SHADOW_OFF + (x_s X + Z.of_nat i + 1) / 8) (x_s X + Z.of_nat i + 1) sv (nth (S i) (x_bs X ++ [0]) 0)
  Hpre Hn eq_refl eq_refl eq_refl Hsvr Hbr Hsv (psl_aview1 _ _ _ _ Hbv Hbr)
  ltac:(unfold x_n in *; clear - HsF Hi1; lia) ltac:(unfold x_n in *; clear - Hsloc Hi1; lia) Har) as (HEI & HS).
unfold ASAN_CEIL in Har.
set (EN := psl_EN regsc (x_F X pos) (SHADOW_OFF + (x_s X + Z.of_nat i + 1) / 8) sv (nth (S i) (x_bs X ++ [0]) 0))
  in HEI, HS.
assert (HAG : env_agree 32 (Ereg regsc [Z_to_bv 64 (x_F X pos); Z_to_bv 64 (SHADOW_OFF + (x_s X + Z.of_nat i + 1) / 8);
  Z_to_bv 64 sv; Z_to_bv 64 (nth (S i) (x_bs X ++ [0]) 0)]) EN).
{ split; [intros n Hn32; unfold EN, psl_EN; apply Eimg_low; unfold A_TEXT; clear - Hn32; lia | reflexivity]. }
assert (Ereg_ : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EN n = getr regsc r).
{ intros n r Hn32 Hr. unfold EN, psl_EN. rewrite Eimg_low by (unfold A_TEXT; clear - Hn32; lia).
  exact (ew_Ereg_nat regsc _ n r Hr). }
assert (E32 : ew EN 32 = Z_to_bv 64 (x_F X pos))
  by (unfold EN, psl_EN; rewrite Eimg_low by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E34 : ew EN 34 = Z_to_bv 64 sv)
  by (unfold EN, psl_EN; rewrite Eimg_low by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew EN 35 = Z_to_bv 64 (nth (S i) (x_bs X ++ [0]) 0))
  by (unfold EN, psl_EN; rewrite Eimg_low by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E20 : ew EN 20 = Z_to_bv 64 (x_s X + Z.of_nat i + 1))
  by (rewrite (Ereg_ 20%nat 20%bv) by (lia || reflexivity); exact R20).
assert (E22 : ew EN 22 = Z_to_bv 64 (x_SHF X pos))
  by (rewrite (Ereg_ 22%nat 22%bv) by (lia || reflexivity); exact R22).
assert (E24 : ew EN 24 = Z_to_bv 64 (x_s X + Z.of_nat i))
  by (rewrite (Ereg_ 24%nat 24%bv) by (lia || reflexivity); exact R24).
assert (R22b : base_val EN (Some 22%nat) = x_SHF X pos)
  by (cbn [base_val]; rewrite E22; apply unsigned_lit_small;
      unfold SHADOW_OFF, kHighMemBeg in HSHFr; clear - HSHFr; lia).
assert (HFrng : 0 <= x_F X pos < 2 ^ 64) by (clear - HF4096 HFceil HC; lia).
assert (Hs0r : 0 <= x_s X + Z.of_nat i < 2 ^ 64) by (clear - Har HC; lia).
assert (Hs1r : 0 <= x_s X + Z.of_nat i + 1 < 2 ^ 64) by (clear - Har HC; lia).
assert (Hsrng : 0 <= x_s X + Z.of_nat i + 1 + 1 < 2 ^ 64) by (clear - Har HC; lia).
assert (HRW : psl_rwords X pos Wc memc) by (unfold psl_rwords; repeat split; assumption).
pose proof HCOMc as (HJ & _ & _ & _ & HPM & _ & _ & _ & _ & Hfz & Hfk).
(* ---- the stretches' one write window is u's shadow granule (SHF + 4) ---- *)
let nwrW := fun _ => (let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros ? (r & Hin & Hx); cbn [In ss_mem psl_ssN] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf psl_shb psl_byt psl_rblk] in Hx; rewrite ?R22b in Hx;
      clear - Hx; lia | ]);
  try destruct Hin) in
let awrRun := fun _ => (let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros ? (r & Hin & Hx); cbn [In ss_mem psl_ssN] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf psl_shb psl_byt psl_rblk] in Hx; rewrite ?R22b in Hx;
      first [ clear - Hx; lia
            | unfold awr_byte, in_frames; right; right; right; exists 0, pos; split; [left; reflexivity|];
              right; unfold in_zr; cbn [fst snd]; unfold shadow_addr; change (fs_frame_bytes 0) with 64;
              change (64 / 8) with 8; rewrite EF, <- HSHF; clear - Hx; lia ] | ]);
  try destruct Hin) in
let nwrQ := fun _ => (let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros ? (r & Hin & Hx); cbn [In ss_mem psl_ssN] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf psl_shb psl_byt psl_rblk] in Hx; rewrite ?R22b in Hx;
      first [ clear - Hx; lia
            | right; right; unfold SHADOW_OFF, kHighMemBeg in *; clear - Hx HSHFr; lia ] | ]);
  try destruct Hin) in
let pcom := fun _ => (let H := fresh "HCOMn" in
  eassert (H : ps_commonR (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _);
  [ eapply ps_common_frameR; [exact Hpre | exact HCOMc | exact HJ | exact HPM | eassumption | nwrQ ()] | ];
  clear HCOMc; rename H into HCOMc) in
let prw := fun _ => (lazymatch goal with |- SRrG _ _ _ (mkCfg ?msx _) _ =>
  let H := fresh "HRWn" in
  assert (H : psl_rwords X pos Wc (ms_mem msx));
  [ apply (psl_rwords_keep X pos Wc Wc _ (ms_mem msx) HRW);
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    eapply (psl_keep_av _ _ _ _ _ (x_SHF X pos + 4) (x_SHF X pos + 5));
    [ eassumption | nwrW () | clear - Ha HRr HC; lia
    | unfold SHADOW_OFF, kHighMemBeg in *; clear - Ha HRhi HSHFr; lia ]
  | ]; clear HRW; rename H into HRW end) in
(* ---- the next loop head (AF + 384): byte i + 1 is nonzero, the run [j, i + 2) is pending ---- *)
let head_leaf := fun _ => (
  lazymatch goal with Hc : branch_taken BC_NE _ _ = true |- _ =>
    rewrite branch_ne_U, U_SLit, (U_atom _ 35 _ E35 ltac:(clear - Hbr; lia)) in Hc;
    change (zcanon 0) with 0 in Hc; apply Bool.negb_true_iff, Z.eqb_neq in Hc;
    let Hi2 := fresh "Hi2" in let Hbeq := fresh "Hbeq" in
    destruct (psl_byte_in (x_bs X) (S i) Hi1 Hc) as (Hi2 & Hbeq);
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384);
    [ awrRun ()
    | pcom (); prw (); pmkst HS;
      lazymatch goal with |- context [BASE + ?k] =>
        replace k with (AF_put_string + 384) by (unfold AF_put_string; rewrite (proj2 A_entry_put_string);
          vm_compute; reflexivity) end;
      eapply (HEAD fx Hfz Hfk pos j P); unfold PRW_put_string_base.ps_head;
      pose proof HRW as (A8 & A16 & A24 & A32 & A40 & A48 & A56);
      split; [exact HCOMc|];
      split; [clear - Hji Hi2; lia|];
      split; [exact Hplan|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 2%bv 2%bv HS HAG ltac:(vm_compute; reflexivity)); exact R2|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 3%bv 3%bv HS HAG ltac:(vm_compute; reflexivity)); exact R3|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 4%bv 4%bv HS HAG ltac:(vm_compute; reflexivity)); exact R4|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 8%bv 8%bv HS HAG ltac:(vm_compute; reflexivity)); exact R8|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 9%bv 9%bv HS HAG ltac:(vm_compute; reflexivity)); exact R9|];
      split; [rewrite (psl_reg_val _ _ _ _ 18%bv (SOff 35 0) _ HS ltac:(vm_compute; reflexivity)
                (psl_atom _ 35 _ E35 ltac:(clear - Hbr; lia))), Hbeq; reflexivity|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 19%bv 19%bv HS HAG ltac:(vm_compute; reflexivity)); exact R19|];
      split; [replace (x_s X + Z.of_nat (S i) + 1) with (x_s X + Z.of_nat i + 1 + 1) by (clear - Hji; lia);
              exact (psl_reg_val _ _ _ _ 20%bv (SOff 20 1) _ HS ltac:(vm_compute; reflexivity)
                (psl_atom_off _ 20 _ 1 E20 Hs1r Hsrng))|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 21%bv 21%bv HS HAG ltac:(vm_compute; reflexivity)); exact R21|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 22%bv 22%bv HS HAG ltac:(vm_compute; reflexivity)); exact R22|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 23%bv 23%bv HS HAG ltac:(vm_compute; reflexivity)); exact R23|];
      split; [replace (x_s X + Z.of_nat (S i)) with (x_s X + Z.of_nat i + 1) by (clear - Hji; lia);
              exact (psl_reg_val _ _ _ _ 24%bv (SOff 24 1) _ HS ltac:(vm_compute; reflexivity)
                (psl_atom_off _ 24 _ 1 E24 Hs0r Hs1r))|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 25%bv 25%bv HS HAG ltac:(vm_compute; reflexivity)); exact R25|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 26%bv 26%bv HS HAG ltac:(vm_compute; reflexivity)); exact R26|];
      split; [exact A8|]; split; [exact A16|]; split; [exact A24|]; split; [exact A32|]; split; [exact A40|];
      split; [exact A48 | exact A56] ]
  end) in
(* ---- the tail join (AF + 672): byte i + 1 is the NUL, s4 back on it, s5 / s8 reloaded with F from R + 16 / R + 8 ---- *)
let tail_leaf := fun _ => (
  lazymatch goal with Hc : branch_taken BC_NE _ _ = false |- _ =>
    rewrite branch_ne_U, U_SLit, (U_atom _ 35 _ E35 ltac:(clear - Hbr; lia)) in Hc;
    change (zcanon 0) with 0 in Hc; apply Bool.negb_false_iff, Z.eqb_eq in Hc;
    let Hlen := fresh "Hlen" in
    pose proof (psl_byte_nul (x_bs X) (S i) Hnz Hi1 Hc) as Hlen;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 672);
    [ awrRun ()
    | pcom (); pmkst HS;
      lazymatch goal with |- context [BASE + ?k] =>
        replace k with (AF_put_string + 672) by (unfold AF_put_string; rewrite (proj2 A_entry_put_string);
          vm_compute; reflexivity) end;
      eapply (TAIL fx Hfz Hfk pos j P); unfold PRW_put_string_base.ps_tail;
      split; [exact HCOMc|];
      split; [clear - Hji Hlen; lia|];
      split; [exact (psl_plan_tail (x_bs X) P i j Hji Hlen Hplan)|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 2%bv 2%bv HS HAG ltac:(vm_compute; reflexivity)); exact R2|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 3%bv 3%bv HS HAG ltac:(vm_compute; reflexivity)); exact R3|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 4%bv 4%bv HS HAG ltac:(vm_compute; reflexivity)); exact R4|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 8%bv 8%bv HS HAG ltac:(vm_compute; reflexivity)); exact R8|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 9%bv 9%bv HS HAG ltac:(vm_compute; reflexivity)); exact R9|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 19%bv 19%bv HS HAG ltac:(vm_compute; reflexivity)); exact R19|];
      split; [replace (x_s X + x_n X) with (x_s X + Z.of_nat i + 1)
                by (unfold x_n; rewrite <- Hlen; clear - Hji; lia);
              exact (psl_reg_val _ _ _ _ 20%bv (SOff 20 0) _ HS ltac:(vm_compute; reflexivity)
                (psl_atom _ 20 _ E20 Hs1r))|];
      split; [exact (psl_reg_val _ _ _ _ 21%bv (SOff 32 0) _ HS ltac:(vm_compute; reflexivity)
                (psl_atom _ 32 _ E32 HFrng))|];
      split; [rewrite (psl_reg_of _ _ _ _ regsc _ 22%bv 22%bv HS HAG ltac:(vm_compute; reflexivity)); exact R22|];
      split; [exact (psl_reg_val _ _ _ _ 24%bv (SOff 32 0) _ HS ltac:(vm_compute; reflexivity)
                (psl_atom _ 32 _ E32 HFrng))|];
      rewrite (psl_reg_of _ _ _ _ regsc _ 26%bv 26%bv HS HAG ltac:(vm_compute; reflexivity)); exact R26 ]
  end) in
(* ---- the byte's test (AF + 628 `bne s2, zero`) ---- *)
let byte_test := fun _ => (
  pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384);
  [ awrRun () | pcom (); prw (); pnt_branch BR HS; [ head_leaf () | tail_leaf () ] ]) in
(* ---- the re-poison and the shadow byte's test (AF + 612 `bne a1, zero`) ---- *)
pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384);
[ awrRun ()
| pcom (); prw (); pnt_branch BR HS;
  [ (* the shadow byte is nonzero: the partial granule's test (AF + 640) *)
    lazymatch goal with Hc : branch_taken BC_NE _ _ = true |- _ =>
      rewrite branch_ne_U, U_SLit, (U_atom _ 34 sv E34 ltac:(clear - Hsvr; lia)) in Hc;
      change (zcanon 0) with 0 in Hc; apply Bool.negb_true_iff, Z.eqb_neq in Hc; rename Hc into Hsvnz end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384);
    [ awrRun ()
    | pcom (); prw (); pnt_branch BR HS;
      [ (* (a & 7) < the shadow byte: the load (AF + 616) *)
        byte_test ()
      | (* the report arm (AF + 644, __asan_report_load1) is not taken: byte i + 1 is addressable *)
        exfalso;
        assert (Hlt : (x_s X + Z.of_nat i + 1) mod 8 < sv) by (unfold saddr_ok in Hsok; clear - Hsok Hsvnz; lia);
        lazymatch goal with Hc : branch_taken BC_LT _ _ = false |- _ =>
          rewrite (psl_slow_lt _ 24 34 (x_s X + Z.of_nat i + 1) sv
                     ltac:(replace (x_s X + Z.of_nat i + 1 - 1) with (x_s X + Z.of_nat i) by ring; exact E24)
                     E34 ltac:(clear - Har; lia) ltac:(clear - Har HC; lia) ltac:(clear - Hsvr Hsvnz; lia) Hlt) in Hc;
          discriminate Hc end ] ]
  | (* the shadow byte is 0: the load (AF + 616) *)
    lazymatch goal with Hc : branch_taken BC_NE _ _ = false |- _ => clear Hc end;
    byte_test () ] ].
Qed.

(* ---- the loop head (A 0x884ec): the byte test, then either the run put before the escape (A 0x88514), or the
   re-poison join (A 0x885b8) with the same pending run. All after a put: the stretches, the branches and the run put
   at wle' SEGS RZ_cf, the conclusion SRr' ---- *)
Lemma psl_head_step : forall X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_pre X ch -> ps_s0 X -> psl_ESCC X -> psl_NEXTC X i ->
  ps_head X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin X).
Proof.
intros X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc Hpre HS0 ESC NEXT Hh.
unfold SRr'.
pose proof Hh as (HCOMc & (Hji & Hi) & Hplan & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 &
  R25 & R26 & W8 & W16 & W24 & W32 & W40 & W48 & W56).
pose proof Hpre as (HFPRE & Hroom0 & Hrp0 & Huniv & H10e & H11e & Hocase & Hoch & HWIN0 & Ho1 & Ho2 & Hout0 & Hled0 &
  Hcstr0 & Hkept0 & Hdisj0 & Hfr0 & Hwmax0 & Hhead0 & Hlive0 & Hcons0 & Hevs0 & Hlen4).
destruct HFPRE as (HPRE & Hro0 & Htopstk & Hraceil & Hfrm0).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & HR32).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc)
  as (Hin & EF & HF32 & HF4096 & HFceil & HFloc & HFpres & HFsh & HSHF).
destruct (psl_str_now X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc)
  as (HCSTR & HRA & HHV & Hs4096 & HsC & Hsloc & HsF).
unfold ASAN_CEIL in HsC.
destruct HCSTR as (Hg & Hnz).
assert (Hc : 0 <= nth i (x_bs X) 0 < 256).
{ destruct (Hg i ltac:(rewrite length_app; cbn [length]; lia)) as (_ & Hr).
  rewrite app_nth1 in Hr by lia. exact Hr. }
assert (Hn0 : Z.of_nat j <= Z.of_nat i < x_n X) by (unfold x_n; lia).
assert (HSHFr : SHADOW_OFF + 512 <= x_SHF X pos /\ x_SHF X pos + 8 <= kHighMemBeg).
{ rewrite HSHF. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. clear - HF4096 HFceil HC. split; lia. }
assert (HRr : YM05.alloc_ceiling <= x_R X /\ x_R X + 88 <= x_sp X /\ x_sp X <= 2 ^ 47).
{ unfold x_R, x_sp, PS_R in *. clear - HR Hceil Hslo Hstk0 HSTK208 Hshi H47. lia. }
assert (HRhi : kHighMemBeg <= x_R X) by (unfold kHighMemBeg in *; clear - HRr HC; lia).
assert (Horng : 0 <= x_o X < 2 ^ 64)
  by (clear - Ho1 Ho2 Hdtop HRr Htop2 H47 HC; unfold x_sp in *; lia).
(* the pending run [j, i), its bytes and its home *)
assert (Hblen : length (firstn (i - j) (skipn j (x_bs X))) = (i - j)%nat) by (apply psl_len_fs; lia).
assert (Hbsrc : forall (W : world SEGS) (m : word -> option byte),
  cstr W m (x_s X) (x_bs X) ->
  bytes_at W m (x_s X + Z.of_nat j) (firstn (i - j) (skipn j (x_bs X)))).
{ intros W m (Hg2 & _). unfold bytes_at. intros k Hk. rewrite Hblen in Hk.
  destruct (Hg2 (j + k)%nat ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & Hr).
  rewrite app_nth1 in Hv, Hr by lia.
  rewrite psl_nth_fs by lia. split; [|exact Hr].
  replace (x_s X + Z.of_nat j + Z.of_nat k) with (x_s X + Z.of_nat (j + k)) by lia. exact Hv. }
assert (Hbhome : forall Lamc, kept_at B Lamc (x_s X) (x_n X + 1) ->
  kept_at B Lamc (x_s X + Z.of_nat j) (Z.of_nat (length (firstn (i - j) (skipn j (x_bs X)))))).
{ intros Lamc Hk. rewrite Hblen. unfold x_n in *.
  destruct Hk as [(bb & m & Hinb & Hle2 & Hhi) | [(Hzs & Hlo & Hhi & Hall) | (Hlo & Hhi & Hall)]].
  - left. exists bb, m. split; [exact Hinb|]. split; clear - Hle2 Hhi Hn0 Hji; lia.
  - right. left. destruct Hzs as (q & m & Hinq & Hq1 & Hq2).
    split; [exists q, m; split; [exact Hinq|]; split; clear - Hq1 Hq2 Hn0 Hji; lia|].
    split; [clear - Hlo Hn0 Hji; lia|]. split; [clear - Hhi Hn0 Hji; lia|].
    intros aa Haa. apply Hall. clear - Haa Hn0 Hji. lia.
  - right. right. unfold kept_img in *.
    split; [clear - Hlo Hn0 Hji; lia|]. split; [clear - Hhi Hn0 Hji; lia|].
    intros aa Haa. apply Hall. clear - Haa Hn0 Hji. lia. }
assert (HRW : psl_rwords X pos Wc memc) by (unfold psl_rwords; repeat split; assumption).
(* the seat *)
destruct (psl_seat_H X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc Hpre Hh) as (HEI & HS).
assert (HAG : env_agree 32 (Ereg regsc []) (psl_EH regsc)).
{ split; [intros n Hn; unfold psl_EH; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (Ereg_ : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (psl_EH regsc) n = getr regsc r).
{ intros n r Hn32 Hr. unfold psl_EH. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regsc _ n r Hr). }
assert (E18 : ew (psl_EH regsc) 18 = Z_to_bv 64 (nth i (x_bs X) 0))
  by (rewrite (Ereg_ 18%nat 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew (psl_EH regsc) 19 = Z_to_bv 64 (x_o X))
  by (rewrite (Ereg_ 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E22 : ew (psl_EH regsc) 22 = Z_to_bv 64 (x_SHF X pos))
  by (rewrite (Ereg_ 22%nat 22%bv) by (lia || reflexivity); exact R22).
assert (E24 : ew (psl_EH regsc) 24 = Z_to_bv 64 (x_s X + Z.of_nat i))
  by (rewrite (Ereg_ 24%nat 24%bv) by (lia || reflexivity); exact R24).
assert (E25 : ew (psl_EH regsc) 25 = Z_to_bv 64 34)
  by (rewrite (Ereg_ 25%nat 25%bv) by (lia || reflexivity); exact R25).
assert (E26 : ew (psl_EH regsc) 26 = Z_to_bv 64 (x_s X + Z.of_nat j))
  by (rewrite (Ereg_ 26%nat 26%bv) by (lia || reflexivity); exact R26).
assert (R22b : base_val (psl_EH regsc) (Some 22%nat) = x_SHF X pos)
  by (cbn [base_val]; rewrite E22; apply unsigned_lit_small;
      unfold SHADOW_OFF, kHighMemBeg in HSHFr; clear - HSHFr; lia).
pose proof (AF_ps_ret_k 428 ltac:(lia) ltac:(reflexivity)) as (H428 & H428b).
assert (H428c : BASE + (AF_put_string + 428) < YM05.alloc_ceiling) by (apply ps_ret_lt_ceil; cbn [In]; tauto).
pose proof HCOMc as (HJ & _ & _ & _ & HPM & _ & _ & _ & _ & Hfz & Hfk).
(* ---- the stretches' one write window is u's shadow granule (SHF + 4) ---- *)
let nwrW := fun _ => (let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros ? (r & Hin & Hx); cbn [In ss_mem] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf] in Hx; rewrite ?R22b in Hx; clear - Hx; lia | ]);
  try destruct Hin) in
let awrRun := fun _ => (let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros ? (r & Hin & Hx); cbn [In ss_mem] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf] in Hx; rewrite ?R22b in Hx;
      first [ clear - Hx; lia
            | unfold awr_byte, in_frames; right; right; right; exists 0, pos; split; [left; reflexivity|];
              right; unfold in_zr; cbn [fst snd]; unfold shadow_addr; change (fs_frame_bytes 0) with 64;
              change (64 / 8) with 8; rewrite EF, <- HSHF; clear - Hx; lia ] | ]);
  try destruct Hin) in
let nwrQ := fun _ => (let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros ? (r & Hin & Hx); cbn [In ss_mem] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf] in Hx; rewrite ?R22b in Hx;
      first [ clear - Hx; lia
            | right; right; unfold SHADOW_OFF, kHighMemBeg in *; clear - Hx HSHFr; lia ] | ]);
  try destruct Hin) in
let pcom := fun _ => (let H := fresh "HCOMn" in
  eassert (H : ps_commonR (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _);
  [ eapply ps_common_frameR; [exact Hpre | exact HCOMc | exact HJ | exact HPM | eassumption | nwrQ ()] | ];
  clear HCOMc; rename H into HCOMc) in
let prw := fun _ => (lazymatch goal with |- SRrG _ _ _ (mkCfg ?msx _) _ =>
  let H := fresh "HRWn" in
  assert (H : psl_rwords X pos Wc (ms_mem msx));
  [ apply (psl_rwords_keep X pos Wc Wc _ (ms_mem msx) HRW);
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    eapply (psl_keep_av _ _ _ _ _ (x_SHF X pos + 4) (x_SHF X pos + 5));
    [ eassumption | nwrW () | clear - Ha HRr HC; lia
    | unfold SHADOW_OFF, kHighMemBeg in *; clear - Ha HRhi HSHFr; lia ]
  | ]; clear HRW; rename H into HRW end) in
(* ---- the leaf at the re-poison join (A 0x885b8): the byte is put as itself ---- *)
let next_leaf := fun _ => (
  lazymatch goal with Hns : WriterSpec.special (nth i (x_bs X) 0) = false |- _ =>
  pcom (); prw (); pmkst HS;
  lazymatch goal with |- context [BASE + ?k] =>
    replace k with (AF_put_string + 588) by (unfold AF_put_string; rewrite (proj2 A_entry_put_string);
      vm_compute; reflexivity) end;
  eapply (NEXT fx Hfz Hfk pos j P); unfold PRW_put_string_base.ps_next;
  pose proof HRW as (A8 & A16 & A24 & A32 & A40 & A48 & A56);
  split; [exact HCOMc|];
  split; [clear - Hji; lia|];
  split; [exact Hi|];
  split; [exact (psl_plan_ns (x_bs X) P i j Hji Hi Hns Hplan)|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 2%bv 2%bv HS HAG ltac:(vm_compute; reflexivity)); exact R2|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 3%bv 3%bv HS HAG ltac:(vm_compute; reflexivity)); exact R3|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 4%bv 4%bv HS HAG ltac:(vm_compute; reflexivity)); exact R4|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 8%bv 8%bv HS HAG ltac:(vm_compute; reflexivity)); exact R8|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 9%bv 9%bv HS HAG ltac:(vm_compute; reflexivity)); exact R9|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 19%bv 19%bv HS HAG ltac:(vm_compute; reflexivity)); exact R19|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 20%bv 20%bv HS HAG ltac:(vm_compute; reflexivity)); exact R20|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 21%bv 21%bv HS HAG ltac:(vm_compute; reflexivity)); exact R21|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 22%bv 22%bv HS HAG ltac:(vm_compute; reflexivity)); exact R22|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 23%bv 23%bv HS HAG ltac:(vm_compute; reflexivity)); exact R23|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 24%bv 24%bv HS HAG ltac:(vm_compute; reflexivity)); exact R24|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 25%bv 25%bv HS HAG ltac:(vm_compute; reflexivity)); exact R25|];
  split; [rewrite (psl_reg_of _ _ _ _ regsc [] 26%bv 26%bv HS HAG ltac:(vm_compute; reflexivity)); exact R26|];
  split; [exact A8|]; split; [exact A16|]; split; [exact A24|]; split; [exact A32|]; split; [exact A40|];
  split; [exact A48 | exact A56] end) in
(* ---- the leaf at the run put (A 0x88514), and the escape join it returns to (A 0x88518) ---- *)
let put_leaf := fun _ => (
  lazymatch goal with
  | Hsp : WriterSpec.special (nth i (x_bs X) 0) = true |- SRrG _ _ _ (mkCfg ?msx _) _ =>
    pcom (); prw ();
    let HCS2 := fresh "HCS2" in let HRA2 := fresh "HRA2" in
    let HHV2 := fresh "HHV2" in let HSH4 := fresh "HSH4" in
    destruct (psl_str_now X ch pos P _ _ _ Wc (ms_mem msx) _ _ Hpre HCOMc)
      as (HCS2 & HRA2 & HHV2 & _ & _ & _ & _);
    assert (HSH4 : aview SEGS (w_H Wc) (ms_mem msx) (x_SHF X pos + 4) = Some 0);
    [ lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
        let rv := eval vm_compute in (nth_error (ss_mem ssx) 0) in
        lazymatch rv with
        | Some ?rg =>
          let Hrg := fresh "Hrg" in
          pose proof (st_ok_region_nth SEGS Ev ssx _ 0 rg HS ltac:(vm_compute; reflexivity)) as Hrg;
          cbn [ms_mem restrict mkst] in Hrg;
          apply psl_aview1; [|clear - Hrg; lia];
          exact (field_of_region SEGS Ev _ 22%nat (x_SHF X pos) _ 4 5 4 5 4 1%N (SLit 0) 0 Hrg R22b
                   ltac:(cbn [In]; repeat first [left; reflexivity | right])
                   ltac:(cbn [sv_denot]; reflexivity) ltac:(zside) ltac:(zside))
        end end
    | ];
    pmkst HS;
    eapply (ps_put_step X ch pos P (firstn (i - j) (skipn j (x_bs X)))
             (WriterSpec.esc (nth i (x_bs X) 0) :: WriterSpec.spieces_run [] (skipn (S i) (x_bs X)) ++ [[34]])
             _ _ _ Wc (ms_regs msx) (ms_mem msx) _ _
             (Z_to_bv 64 (BASE + (AF_put_string + 428))) (x_s X + Z.of_nat j));
    [ exact Hpre
    | exact HS0
    | exact HCOMc
    | exact (proj1 (psl_plan_esc (x_bs X) P i j Hji Hi Hsp Hplan))
    | unfold spZ; rewrite (psl_reg_of_ok _ _ _ _ regsc [] 2%bv 2%bv HS HAG ltac:(vm_compute; reflexivity)), R2;
      unfold w64; apply unsigned_lit_small; clear - HRr HC; lia
    | rewrite (psl_reg_of_ok _ _ _ _ regsc [] 3%bv 3%bv HS HAG ltac:(vm_compute; reflexivity)), R3; exact Hgp
    | rewrite (psl_reg_of_ok _ _ _ _ regsc [] 4%bv 4%bv HS HAG ltac:(vm_compute; reflexivity)), R4; exact Htp
    | rewrite (psl_reg_val_ok _ _ _ _ 1%bv (SOff A_TEXT (AF_put_string + 428)) (BASE + (AF_put_string + 428)) HS
                ltac:(vm_compute; reflexivity) (codeptr_val _ (AF_put_string + 428) HEI));
      reflexivity
    | apply ret_ok_codeptr_v; [exact (proj1 H428) | exact (proj2 H428)]
    | rewrite unsigned_lit_small by (clear - H428b H428c HC; lia); exact H428b
    | rewrite unsigned_lit_small by (clear - H428b H428c HC; lia); exact H428c
    | unfold s0Z; rewrite (psl_reg_of_ok _ _ _ _ regsc [] 8%bv 8%bv HS HAG ltac:(vm_compute; reflexivity)), R8;
      unfold w64; apply unsigned_lit_small; clear - HRr HC Ho1 Ho2 Hdtop Htop2 H47; unfold x_sp in *; lia
    | exact (psl_reg_val_ok _ _ _ _ 10%bv (SOff 19 0) (x_o X) HS ltac:(vm_compute; reflexivity)
               (psl_atom _ 19 (x_o X) E19 ltac:(clear - Horng; lia)))
    | exact (psl_reg_val_ok _ _ _ _ 11%bv (SOff 26 0) (x_s X + Z.of_nat j) HS ltac:(vm_compute; reflexivity)
               (psl_atom _ 26 _ E26 ltac:(clear - Hs4096 HsC HC Hn0 Hji; unfold x_n in *; lia)))
    | rewrite Hblen;
      refine (psl_reg_val_ok _ _ _ _ 12%bv (SAlu ALU_ADD (SOff 24 0) (SMd M_MUL (SOff 26 0) (SLit (-1))))
                (Z.of_nat (i - j)) HS ltac:(vm_compute; reflexivity) _);
      rewrite (psl_sub_val _ 24 26 (x_s X + Z.of_nat i) (x_s X + Z.of_nat j) E24 E26
                 ltac:(clear - Hs4096; lia) ltac:(clear - Hji; lia)
                 ltac:(clear - Hs4096 HsC HC Hn0; unfold x_n in *; lia));
      f_equal; clear - Hji; lia
    | (* the run's bytes at s + j *)
      unfold src_rd;
      split; [exact (Hbsrc Wc (ms_mem msx) HCS2)|];
      split; [clear - Hs4096 Hji Hn0; lia|];
      split; [rewrite Hblen; clear - Hs4096 HsC HC Hn0 Hji Hcstr0; unfold x_n in *;
              destruct Hcstr0 as (_ & _ & Hub & _); lia|];
      split; [rewrite Hblen; destruct Hcstr0 as (_ & _ & _ & _ & Har8 & _);
              unfold YGcfStr.amem_range8 in Har8; unfold amem_range; unfold x_n in *;
              clear - Har8 Hn0 Hji Hs4096; lia|];
      split; [rewrite Hblen; apply (range_addressable_sub _ _ (x_s X) (x_n X + 1));
              [exact HRA2 | clear - Hji; lia | unfold x_n in *; clear - Hn0 Hji; lia]|];
      intros _; rewrite Hblen; apply (hull_sub _ (x_s X) (x_n X + 1));
      [exact HHV2 | clear - Hji; lia | unfold x_n in *; clear - Hn0 Hji; lia]
    | (* the run's home *)
      let Lamx := fresh "Lamx" in let bufx := fresh "bufx" in let capx := fresh "capx" in
      let Hk := fresh "Hk" in let Hd := fresh "Hd" in let Hinb := fresh "Hinb" in let Hbl := fresh "Hbl" in
      intros Lamx bufx capx Hk Hd Hinb Hbl;
      split; [left; exact (Hbhome Lamx Hk)|];
      rewrite Hblen; destruct Hd as [Hz | [Hd1 | Hd2]];
      [ left; exact Hz
      | right; left; unfold x_n in *; clear - Hd1 Hn0 Hji; lia
      | right; right; unfold x_n in *; clear - Hd2 Hn0 Hji; lia ]
    | (* the escape join *)
      let ly2 := fresh "ly2" in let S2 := fresh "S2" in let Hp2 := fresh "Hp2" in let W2 := fresh "W2" in
      let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
      let k2 := fresh "k2" in let HCOM2 := fresh "HCOM2" in let HP2 := fresh "HP2" in
      let KW2 := fresh "KW2" in let KP2 := fresh "KP2" in let KF2 := fresh "KF2" in
      intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HCOM2 HP2 KW2 KP2 KF2;
      apply (ESC fx Hfz Hfk pos i (P ++ [firstn (i - j) (skipn j (x_bs X))]) ly2 S2 Hp2 W2 regs2 mem2 md2 (kc + k2));
      [ unfold PRW_put_string_base.ps_esc;
        pose proof (psl_rwords_keep X pos Wc W2 (ms_mem msx) mem2 HRW
                     ltac:(intros aa Haa; apply KW2; clear - Haa HRr; lia))
          as (A8 & A16 & A24 & A32 & A40 & A48 & A56);
        split; [exact HCOM2|];
        split; [exact Hi|];
        split; [exact Hsp|];
        split; [exact (proj2 (psl_plan_esc (x_bs X) P i j Hji Hi Hsp Hplan))|];
        split; [rewrite (psl_pres_at _ _ HP2 2 2%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 2%bv 2%bv HS HAG ltac:(vm_compute; reflexivity)); exact R2|];
        split; [rewrite (psl_pres_at _ _ HP2 3 3%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 3%bv 3%bv HS HAG ltac:(vm_compute; reflexivity)); exact R3|];
        split; [rewrite (psl_pres_at _ _ HP2 4 4%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 4%bv 4%bv HS HAG ltac:(vm_compute; reflexivity)); exact R4|];
        split; [rewrite (psl_pres_at _ _ HP2 8 8%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 8%bv 8%bv HS HAG ltac:(vm_compute; reflexivity)); exact R8|];
        split; [rewrite (psl_pres_at _ _ HP2 9 9%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 9%bv 9%bv HS HAG ltac:(vm_compute; reflexivity)); exact R9|];
        split; [rewrite (psl_pres_at _ _ HP2 18 18%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 18%bv 18%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R18|];
        split; [rewrite (psl_pres_at _ _ HP2 19 19%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 19%bv 19%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R19|];
        split; [rewrite (psl_pres_at _ _ HP2 20 20%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 20%bv 20%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R20|];
        split; [rewrite (psl_pres_at _ _ HP2 21 21%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 21%bv 21%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R21|];
        split; [rewrite (psl_pres_at _ _ HP2 22 22%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 22%bv 22%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R22|];
        split; [rewrite (psl_pres_at _ _ HP2 23 23%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 23%bv 23%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R23|];
        split; [rewrite (psl_pres_at _ _ HP2 24 24%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 24%bv 24%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R24|];
        split; [rewrite (psl_pres_at _ _ HP2 25 25%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                rewrite (psl_reg_of_ok _ _ _ _ regsc [] 25%bv 25%bv HS HAG ltac:(vm_compute; reflexivity));
                exact R25|];
        split; [rewrite (psl_pres_at _ _ HP2 27 27%bv ltac:(cbv [acallee_saved]; clear - HP2; lia) ltac:(reflexivity));
                exact (psl_reg_val_ok _ _ _ _ 27%bv (SAlu ALU_AND (SOff 18 0) (SLit 255)) (nth i (x_bs X) 0) HS
                         ltac:(vm_compute; reflexivity) (psl_and_val _ 18 _ E18 Hc))|];
        split; [rewrite (KF2 (x_SHF X pos + 4) ltac:(right; clear; lia)); exact HSH4|];
        split; [exact A8|]; split; [exact A16|]; split; [exact A24|]; split; [exact A32|]; split; [exact A40|];
        split; [exact A48 | exact A56]
      | let lyn := fresh "lyn" in let Sn := fresh "Sn" in let Hpn := fresh "Hpn" in let Wn := fresh "Wn" in
        let rn := fresh "rn" in let mn := fresh "mn" in let dn := fresh "dn" in let kn := fresh "kn" in
        let Hn := fresh "Hn" in let fx' := fresh "fx'" in let Hz' := fresh "Hz'" in let Hk' := fresh "Hk'" in
        intros fx' Hz' Hk' lyn Sn Hpn Wn rn mn dn kn Hn;
        exact (NEXT fx' Hz' Hk' pos (S i) _ lyn Sn Hpn Wn rn mn dn kn Hn) ] ]
  end) in
(* ---- the byte tests (A 0x884f0 `beq s2, s9`, 0x884f8 `beq s2, 92`, 0x88500 `bgeu 31, s2`) ---- *)
pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 588);
[ awrRun ()
| pcom (); prw (); pnt_branch BR HS;
  [ (* the byte is a quote *)
    lazymatch goal with Hb : branch_taken BC_EQ _ _ = true |- _ =>
      rewrite branch_eq_U, (U_atom _ 18 _ E18 ltac:(clear - Hc; lia)),
        (U_atom _ 25 34 E25 ltac:(clear - E25; lia)) in Hb; apply Z.eqb_eq in Hb;
      assert (Hsp : WriterSpec.special (nth i (x_bs X) 0) = true)
        by (unfold WriterSpec.special; rewrite Hb; reflexivity) end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 588); [ awrRun () | put_leaf () ]
  | lazymatch goal with Hb : branch_taken BC_EQ _ _ = false |- _ =>
      rewrite branch_eq_U, (U_atom _ 18 _ E18 ltac:(clear - Hc; lia)),
        (U_atom _ 25 34 E25 ltac:(clear - E25; lia)) in Hb; apply Z.eqb_neq in Hb; rename Hb into Hnq end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 588);
    [ awrRun ()
    | pcom (); prw (); pnt_branch BR HS;
      [ (* the byte is a backslash *)
        lazymatch goal with Hb2 : branch_taken BC_EQ _ _ = true |- _ =>
          rewrite branch_eq_U, (U_atom _ 18 _ E18 ltac:(clear - Hc; lia)), U_SLit in Hb2;
          change (zcanon 92) with 92 in Hb2; apply Z.eqb_eq in Hb2;
          assert (Hsp : WriterSpec.special (nth i (x_bs X) 0) = true)
            by (unfold WriterSpec.special; rewrite Hb2; reflexivity) end;
        pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 588); [ awrRun () | put_leaf () ]
      | lazymatch goal with Hb2 : branch_taken BC_EQ _ _ = false |- _ =>
          rewrite branch_eq_U, (U_atom _ 18 _ E18 ltac:(clear - Hc; lia)), U_SLit in Hb2;
          change (zcanon 92) with 92 in Hb2; apply Z.eqb_neq in Hb2; rename Hb2 into Hnb end;
        pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 588);
        [ awrRun ()
        | pcom (); prw (); pnt_branch BR HS;
          [ (* 31 < the byte (unsigned): it is put as itself *)
            lazymatch goal with Hb3 : branch_taken BC_LTU _ _ = true |- _ =>
              rewrite branch_ltu_U, U_SLit, (U_atom _ 18 _ E18 ltac:(clear - Hc; lia)) in Hb3;
              change (zcanon 31) with 31 in Hb3; apply Z.ltb_lt in Hb3;
              assert (Hns : WriterSpec.special (nth i (x_bs X) 0) = false)
                by (unfold WriterSpec.special; apply Bool.orb_false_iff;
                    split; [apply Bool.orb_false_iff; split; apply Z.eqb_neq; clear - Hnq Hnb; lia
                           | apply Z.ltb_ge; clear - Hb3; lia]) end;
            pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 588); [ awrRun () | next_leaf () ]
          | (* the byte is a control character *)
            lazymatch goal with Hb3 : branch_taken BC_LTU _ _ = false |- _ =>
              rewrite branch_ltu_U, U_SLit, (U_atom _ 18 _ E18 ltac:(clear - Hc; lia)) in Hb3;
              change (zcanon 31) with 31 in Hb3; apply Z.ltb_ge in Hb3;
              assert (Hsp : WriterSpec.special (nth i (x_bs X) 0) = true)
                by (unfold WriterSpec.special; apply Bool.orb_true_iff; right; apply Z.ltb_lt;
                    clear - Hb3; lia) end;
            pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 588); [ awrRun () | put_leaf () ] ] ] ] ] ] ].
Qed.

End h.
End f.
End d.

(* ---- the loop (the internal file PS102-CONTRACT.md (L)): from any loop head, by induction on the bytes left. Each head step and each
   re-poison step runs at the float state of its join (the continuations quantify it), so this Section has no
   float-state Context; put's text, the one hypothesis of the steps that reads a float state, quantifies it. The other
   hypotheses are the step Section's, same texts and owners. ---- *)
Section loop.
Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {SK : YI16.sink_head}.
(* The kit's non-primary room invariant (PRH_Base.v PrhRoomLive, owner a Theorem Labs lane) *)
Context {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the engine's / instance's side condition of the frame-area step (YGcallSx.v Section x, owner a Theorem Labs lane) *)
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, discharged by a8's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
(* the registered zero-shadow ranges are granule-aligned (YG0f.v asyms_ok's aso_zshadow; image fact of the instance,
   discharged at PI_prog_A) *)
Hypothesis ASO : asyms_ok B.
(* image fact, discharged at PI_prog_A by reflexivity (PAImg_prog.v:408 pa_lo := IMG_LO; pa_hi := IMG_TOP): the
   instance's image band is image A's (kept_at's image arms are per instance since 2026-10-29; WalkS7bR's ruling) *)
Hypothesis HPAB : pa_lo = IMG_LO /\ pa_hi = IMG_TOP.
(* the image's shadow is visible (PRW_HShadow.v ARx_img_shadow_vis, owner a8 YImgShadowCoverCf.v) *)
Hypothesis HIMGSH : ARx_img_shadow_vis SEGS ARx.
(* alloc.c's six statics and fuzz_preset.c's g_own_ran_out (the ledger's globals, prh_pst, PRH_Base.v:752-755) are image bytes the runtime does not own, apart from errno, and none
   lies in the read-only band (YC1fPx's PST_ok; the S7b walk's pj_write takes the same texts; image facts) *)
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).
(* the generic memory invariant (h-hpreset-7's 12:18Z ruling) and its laws; the walk crosses calls *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
Variable CTX0 : list (list Z).
(* put's text (the kit's tput_specX, WalkS7a's walk) at every float state: a head step runs at its join's (the internal file REFIT-WRITER.md's
   float design, point 4) *)
Hypothesis PUT : forall fx0 : YK11.FPState, tput_specX (fx := fx0) (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
Local Notation ps_pre := (ps_pre B ARx CTX0).
Local Notation psl_HEADC := (psl_HEADC B ARx Pm).
Local Notation psl_TAILC := (psl_TAILC B ARx Pm).
Local Notation psl_ESCC := (psl_ESCC B ARx Pm).

Lemma ps_loop : forall X ch, ps_pre X ch -> ps_s0 X -> psl_ESCC X -> psl_TAILC X -> forall i, psl_HEADC X i.
Proof.
intros X ch Hpre HS0 ESC TAIL.
assert (IND : forall k i, (length (x_bs X) - i <= k)%nat -> psl_HEADC X i).
{ induction k as [|k IH]; intros i Hk fxc Hz Hf pos j P lyc Sc Hpc Wc regsc memc mdc kc Hh.
  - exfalso. pose proof Hh as (_ & (_ & Hi) & _). clear - Hk Hi. lia.
  - apply (@psl_head_step fxc rc ci cp SK RL PA B ARx LAWS segs_low HW ASO HPAB HIMGSH PST_ok HPSTRO Pm PLAW PCALL
      CTX0 (PUT fxc) X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc Hpre HS0 ESC); [|exact Hh].
    intros fxn Hzn Hfn posn jn Pn lyn Sn Hpn Wn regsn memn mdn kn Hn.
    apply (@psl_next_step fxn rc ci cp SK RL PA B ARx LAWS segs_low HW ASO HPAB HIMGSH PST_ok HPSTRO Pm PLAW
      CTX0 X ch posn i jn Pn lyn Sn Hpn Wn regsn memn mdn kn Hpre HS0); [|exact TAIL|exact Hn].
    apply IH. clear - Hk. lia. }
intros i. apply (IND (length (x_bs X) - i)%nat i). lia.
Qed.

End loop.

Print Assumptions psl_head_step.
Print Assumptions psl_next_step.
Print Assumptions ps_loop.
Set Printing All.
Print ps_loop.
Unset Printing All.
