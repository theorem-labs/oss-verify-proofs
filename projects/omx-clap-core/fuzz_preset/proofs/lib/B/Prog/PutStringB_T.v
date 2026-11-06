(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30), this file: put_string's
   walk, the TAIL (B' + 0x2c8 .. + 0x388): from the tail join ps_tail (AF + 712) the closing put of the pending run
   (+ 0x2d4), the closing-quote put (+ 0x2e8), the fake frame's release (magic, f5 shadow, flag byte cleared: + 0x2ec ..
   + 0x324), the epilogue and the return, to the walk's final post ps_Qfin fx0 at the ENTRY float state fx0 (the exit
   float state is the Section's fx, whose two float facts the walk carries: frm_zero, fregs_kept_x fx0 fx). Over
   PutStringB_Base.v, toward the #102 tput_string_specX (PRH_FnWriter.v 2b497bc72172).
   PORTED from lib/A/Prog/PRW_put_string_t.v (blob
   230a142f9957): B' moved the run start from s10 to s2 and the offsets by + 40; one engine lemma (pst_flag_store_invR,
   the memory-invariant twin of YGcallSx.v's aj_flag_store_xR, its proof with SRr_msteps_invR in place of SRrG_msteps;
   pst_flag_store_inv is its instance at wle).
   rule 24: proves function put_string (segment; proof-index 17:58Z, census-1 sweep 18:01Z, second-agent check CONFIRM).
   Added Section hypotheses: ASFX / FFLX / SFX (YGcallSx.v's, verbatim). ONE marked premise, FPRX
   (flag-cell presence at the release), of the release lemma pst_tail_end, threaded only to its caller ps_tail_run
   (first argument): STAND-IN; it is AR_laws_x field 23 (YCbqG.v :296); at ARcfx it is YG0scf.AR_flag_law_ok_cf.
   The re-hiding move: the whole tail lies after put calls (put reallocs when it grows, a crossing call), so its joins
   are ps_commonR at wle' SEGS RZ_cf, its runs and the release are at that relation, the final post is ps_Qfin's
   fpostWFR at it, and the tail concludes SRr'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the step relation over a world relation and the re-hiding relation (SRrG, wle', SRr') and the fixed zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_CallerJ PutStringB_S7bKit PutStringB_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_Base.
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

(* image B's generated numbers (lib/B/PRH_ImgB.v, the #102 B' table) are the PrhImg the texts read *)
#[local] Existing Instance prh_img_B.

(* ---- the release stretch's seated state (B' + 0x2ec = AF + 748): closed, so the engine runs on it at top level.
   Atoms 32 / 33 / 34: the fake frame F, its flag cell FL, F's shadow SHF; atoms 35 .. 47: the entry's s11 .. s2, s1,
   s0, ra (PRW_put_string_base.v's ps_saved_list order), the values the epilogue restores. s5 and s8 hold F, s6 holds
   SHF; the saved slots are read from s0 (= the entry sp) ---- *)
Definition pst_saved : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [ YP09.mkChunk (-104) (CVal 8 (SOff 35 0)); YP09.mkChunk (-96) (CVal 8 (SOff 36 0));
      YP09.mkChunk (-88) (CVal 8 (SOff 37 0)); YP09.mkChunk (-80) (CVal 8 (SOff 38 0));
      YP09.mkChunk (-72) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
      YP09.mkChunk (-56) (CVal 8 (SOff 41 0)); YP09.mkChunk (-48) (CVal 8 (SOff 42 0));
      YP09.mkChunk (-40) (CVal 8 (SOff 43 0)); YP09.mkChunk (-32) (CVal 8 (SOff 44 0));
      YP09.mkChunk (-24) (CVal 8 (SOff 45 0)); YP09.mkChunk (-16) (CVal 8 (SOff 46 0));
      YP09.mkChunk (-8) (CVal 8 (SOff 47 0)) ].
Definition pst_flag : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition pst_mem : smem := [fframe_reg 32 33; fshadow_reg 34; pst_flag; pst_saved].
Definition pst_facts : facts :=
  mkFacts [ (32%nat, mkAF 4096 (2 ^ 47) 5); (33%nat, mkAF 4096 (2 ^ 47) 0);
            (34%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0) ] [] [].
Definition pst_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 21%bv (SOff 32 0)) 24%bv (SOff 32 0)) 22%bv (SOff 34 0).
Definition pst_ss : sstate := mkSS (AF_put_string + 748) pst_regs pst_mem None pst_facts.
(* the first two stretches' seats: the registers only *)
Definition pst_ss1 : sstate := mkSS (AF_put_string + 712) sr_atoms [] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
(* the kit's non-primary room invariant (PRH_Base.v PrhRoomLive) *)
Context {RL : PrhRoomLive}.
Section f.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* the entry (DERIVED: slot * 4, PAImg_prog B_entry_put_string) *)
Hypothesis Hent : SIGMA AS_put_string = BASE + AF_put_string.
(* image-link gap, proposed PALib field pal_got_uar *)
Hypothesis Huar : as_got_uar B = VAL (A_OBJ 1).
(* image facts, discharged at PI_prog_B: the GOT words of the shadow base and of the use-after-return flag, the shadow
   cell and the flag cell lie in the image's segments and apart *)
Hypothesis Hobj : forall i, 0 <= i < 8 ->
  in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\ in_img SEGS (VAL (A_OBJ 1) + i).
Hypothesis HOBJ : ps_objs_disj.
Hypothesis HUARC : ps_uar_ok B.
(* the engine's / instance's side conditions of the frame-area step (YGcallSx.v Section x) *)
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
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, discharged by CfParamsPreset.v's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
(* the registered zero-shadow ranges are granule-aligned (YG0f.v asyms_ok's aso_zshadow; image fact of the instance,
   discharged at PI_prog_B) *)
Hypothesis ASO : asyms_ok B.
(* the image's shadow is visible over the instance's bounds (PutStringB_Base.v HIMGSH) and every live fake frame's
   shadow hull (ARx_frame_hull_vis, YGcfFsVis.v) *)
Hypothesis HIMGSH : forall ly S Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis HFHULL : ARx_frame_hull_vis SEGS ARx.
(* the instance's image bounds (IMAGE FACT, PI_prog_B: IMG_LO_B / IMG_TOP_B, below the low shadow) *)
Hypothesis HPAB : 4096 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= kLowShadowBeg.
(* alloc.c's six statics and fuzz_preset.c's g_own_ran_out (the ledger's globals, prh_pst, PRH_Base.v:752-755) are image bytes the runtime does not own, apart from errno, and none
   lies in the read-only band (YC1fPx's PST_ok; PRW_pj_write.v's pj_write walk takes the same texts; image facts) *)
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).
(* the generic memory invariant (the 12:18Z ruling) and its laws; the walk crosses calls *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
Let RUN := @paj_run_x fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS.
Let RUNI := @paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS Pm PLAW.
Let NTRUNTO := SRr_run_to_pi_AJx B ARx LAWS.
(* the tokenless runner at the re-hiding relation: every stretch of this file runs after a put *)
Let NTRUNTOI := SRr_run_to_pi_AJx_invR B ARx LAWS Pm PLAW (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_B) (PI := PA).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx).
Local Notation AJR R := (ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R).
Variable CTX0 : list (list Z).
(* put's text (the #102 tput_specX), at this Section's float state: the ONE callee-text use of put in this file *)
Hypothesis PUT : tput_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* the double-quote literal .str.18 put_string puts twice (IMAGE FACT, discharged at PI_prog_B; pj_write's HLIT form):
   its byte is the image's, its shadow the read-only global's, at every state *)
Hypothesis HLIT18 : ps_lit_fact B ARx 65 [34].
(* the base file's lemmas at this section's variables and hypotheses; put's call step: its join premise, its
   continuation's join and its conclusion SRr' are at wle' SEGS RZ_cf *)
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

(* ---- this file's own Section hypotheses (beyond the header copied from PRW_put_string_a.v) ---- *)
(* YGcallSx.v's three laws of the inline release (aj_flag_store_x's Section x; cf discharges:
   YGcallScf.v astack_free_x_xs / frame_flag_x_xs / stack_free_x_any), verbatim at this section's segs, B and ARx *)
Hypothesis ASFX : forall ly S Hp (W : world SEGS) mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.

(* every Section hypothesis by name, for the base lemmas whose Section arguments a call leaves to eapply *)
Ltac kit_args := first [ exact LAWS | exact TL | exact Hent | exact Huar | exact Hobj | exact HOBJ | exact HUARC
  | exact segs_low | exact errno_low | exact OWNLOW | exact SMX | exact ASM0 | exact Hsm0 | exact HW | exact ASO
  | exact HIMGSH | exact HFHULL | exact HPAB | exact PST_ok | exact HPSTRO | exact PLAW | exact PCALL | exact PUT
  | exact HLIT18 ].

(* ---- the memory-invariant twin of YGcallSx.v's aj_flag_store_xR (the inline release of a frame-area frame) at the
   program listing, over a journal at a reflexive and transitive world relation R: the same proof with YC80x.v's
   SRr_msteps_invR in place of SRrG_msteps, so Pm crosses the run ---- *)
Lemma pst_flag_store_invR : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q,
  (A_LIM <= K)%nat -> img_env VAL A_LIM E -> 0 <= cid ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sh_ok SEGS Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_pi_tok (@pl_tpi B_prog_listing PL_prog_B) (@pl_tw B_prog_listing PL_prog_B) K Bx Bspan SH n ss = (st', r) ->
  match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
  AJR R STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k ->
  Pm (ms_mem ms) ->
  Forall (ob_holds SEGS Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
  (forall ws msr, length ws = sh_j st' -> st_ok_pi SEGS VAL (extK E K ws) (sh_ss st') msr ->
     mbyte SEGS (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  (forall ws ms' mat',
     length ws = sh_j st' -> img_env VAL A_LIM (extK E K ws) ->
     st_ok_pi SEGS VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
     sh_ok SEGS Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
     AJR R STK sp0 FP ly S Hp W0 mem md own' lyc (stack_free_state cid pos Sc) Hpc W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     Pm (ms_mem ms') ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRrG SEGS R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRrG SEGS R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q
  HK HE Hcid HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hflag0 Hk.
rewrite <- (@pl_tpi_eq B_prog_listing PL_prog_B), <- (@pl_tw_eq B_prog_listing PL_prog_B) in Hrun.
destruct (sym_run_pi_tok_sound asym SEGS (clookup pa_tbl) VAL SIGMA B_prog_listing pa_fetch_ok pa_cert pa_B_ok
  A_LIM A_LIM_text (@pl_lim B_prog_listing PL_prog_B) (@pl_len B_prog_listing PL_prog_B) K Bx Bspan SH HK n E ss _ st' r
  HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
assert (HS' : st_ok_pi SEGS VAL (extK E K ws) (sh_ss st') msr')
  by (destruct r; cbn [ptok_post] in HP; first [exact HP | destruct Hr | destruct HP]).
clear HP.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_frs HJ) as Hfrs.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFLX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfo & Hfr_rng).
apply (SRr_msteps_invR SEGS pa_wx Pm PLAW R W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows SEGS _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) ->
  mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a ->
  aview SEGS (w_H W) memc' a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
destruct (SFX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
  rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
  pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc W (ms_mem ms) mdc (cid, pos) (cid, pos) [] l1' l2 HAR
    ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). lia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
assert (HAR' : ARx lyc (stack_free_state cid pos Sc) Hpc W memc'
  (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASFX lyc Sc Hpc W (ms_mem ms) mdc memc' _ cid pos HAR Hin).
  - unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 ws msr' Hlen HS'). reflexivity.
  - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
    destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
    exact (proj1 (awr_byte_cases_xR SEGS B (@prh_pst prh_img_B) ARx LAWS R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- subst memc'. rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_after_writeR SEGS B (@prh_pst prh_img_B) ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md
    ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc)
    Hpc own' HJ Heqw ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
  + intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  + exact HAR'.
  + unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  + reflexivity.
  + cbn. zlia.
  + etransitivity; [exact E2 | symmetry; exact E1].
  + pose proof (ajxR_qt HJ) as HQT.
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
  + reflexivity.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
(* pst_flag_store_invR at wle *)
Lemma pst_flag_store_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k
    cid pos Q,
  (A_LIM <= K)%nat -> img_env VAL A_LIM E -> 0 <= cid ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sh_ok SEGS Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_pi_tok (@pl_tpi B_prog_listing PL_prog_B) (@pl_tw B_prog_listing PL_prog_B) K Bx Bspan SH n ss = (st', r) ->
  match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
  AJ STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k ->
  Pm (ms_mem ms) ->
  Forall (ob_holds SEGS Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
  (forall ws msr, length ws = sh_j st' -> st_ok_pi SEGS VAL (extK E K ws) (sh_ss st') msr ->
     mbyte SEGS (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  (forall ws ms' mat',
     length ws = sh_j st' -> img_env VAL A_LIM (extK E K ws) ->
     st_ok_pi SEGS VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
     sh_ok SEGS Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
     AJ STK sp0 FP ly S Hp W0 mem md own' lyc (stack_free_state cid pos Sc) Hpc W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     Pm (ms_mem ms') ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof. exact (pst_flag_store_invR (@wle SEGS) (wle_refl SEGS) (wle_trans SEGS)). Qed.

(* ---- base lemmas at this file's goals (their Section arguments left to eapply) ---- *)
Lemma pst_out_own : forall X ch pos lyc Sc Hpc Wc memc mdc kc a,
  ps_pre X ch ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc mdc kc ->
  (x_sp X <= a < 2 ^ 64 \/ in_img SEGS a \/ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) ->
  (a < x_R X \/ x_sp X <= a) /\ (a < x_F X pos \/ x_F X pos + 64 <= a) /\ (a < SHADOW_OFF \/ kHighMemBeg <= a).
Proof. intros. eapply (ps_out_ownR B ARx); try kit_args; eassumption. Qed.

Lemma pst_common_frame : forall X ch pos P lyc Sc Hpc Wc memc mdc kc E rs memc' mdc' kc',
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' ->
  frame_of E rs (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  (forall a, in_wrange E rs a ->
     x_R X <= a < x_R X + 88 \/ x_F X pos <= a < x_F X pos + 56 \/ SHADOW_OFF <= a < kHighMemBeg) ->
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc' mdc' kc'.
Proof. intros. eapply (ps_common_frameR B ARx); try kit_args; eassumption. Qed.

Lemma pst_fp_closed : forall X ch, ps_pre X ch -> ~ YI16.sink_open_fp (x_FP X).
Proof. intros. eapply (ps_fp_closed B ARx); try kit_args; eassumption. Qed.

(* ---- the string's tail run [j, n): its home and its bytes at a later state of the walk ---- *)
Lemma pst_kept_sub : forall Lam p n p' n', kept_at B Lam p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  kept_at B Lam p' n'.
Proof.
intros Lam p n p' n' Hk H1 H2 H3.
destruct Hk as [(b & m & Hin & Hb & Hpe) | [(Hzs & Hlo & Hhi & Hall) | (Hlo & Hhi & Hall)]].
- left. exists b, m. split; [exact Hin|]. lia.
- right; left. split; [|split; [lia | split; [lia |]]].
  + destruct Hzs as (q & m & Hin & Hq & Hqm). exists q, m. split; [exact Hin | lia].
  + intros a Ha. apply Hall. lia.
- right; right. split; [lia | split; [lia |]]. intros a Ha. apply Hall. lia.
Qed.

Lemma pst_home_tail : forall X lyc Sc Lamc bufc capc (j : nat), (j <= length (x_bs X))%nat ->
  kept_at B Lamc (x_s X) (x_n X + 1) -> (capc = 0 \/ x_s X + x_n X + 1 <= bufc \/ bufc + capc <= x_s X) ->
  prhWriter_src_home B lyc Sc Lamc bufc capc (x_s X + Z.of_nat j) (Z.of_nat (length (skipn j (x_bs X)))).
Proof.
intros X lyc Sc Lamc bufc capc j Hj Hk Hd. rewrite length_skipn. unfold x_n in *.
split.
- left. apply (pst_kept_sub Lamc (x_s X) (Z.of_nat (length (x_bs X)) + 1)); [exact Hk | lia | lia | lia].
- lia.
Qed.

Lemma pst_src_tail : forall X ch pos P lyc Sc Hpc Wc memc mdc kc (j : nat),
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc -> (j <= length (x_bs X))%nat ->
  src_rd Wc memc (x_s X + Z.of_nat j) (skipn j (x_bs X)).
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc j Hpre HCOM Hj.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & Hout0 & Hled0 & Hcstr0 & Hkept0 & Hdisj0 & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
destruct HCOM as (HJ & _ & _ & _ & _ & (ok & ranc & bufc & Lamc & peakc & Hoks & Hout & Hled & Hblk & Hkept & Hlive & Hdisj
  & _) & _).
pose proof (ajxR_ar HJ) as HARc.
pose proof Hcstr0 as (Hcs & Hs4096 & Hsceil & H32 & Har8 & _).
assert (Hn1 : 0 < x_n X + 1) by (unfold x_n; lia).
destruct (kept_at_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HAR Hled0 Hkept0 Hn1) as (Hs4096' & HsC).
assert (Hcase0 : WriterApp.w_cap (x_st X) <> 0 -> In (x_buf X, WriterApp.w_cap (x_st X)) (x_Lam X)).
{ intros Hc0. destruct Hout0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & HinL & _)]); [lia | exact HinL]. }
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
assert (Hso : x_s X + (x_n X + 1) <= x_o X) by (unfold x_sp, ASAN_CEIL in *; lia).
assert (Hnfp : forall a, x_s X <= a < x_s X + Z.of_nat (length (x_bs X)) + 1 -> ~ inFP (x_FP X) a).
{ intros a Ha. unfold x_FP.
  apply (str_notin_fp _ _ _ _ _ _ _ _ _ _ _ (x_o X) (x_buf X) (WriterApp.w_cap (x_st X)) (x_s X) (x_n X + 1)
    HAR Hled0 Hkept0 Hn1); [lia | exact Hcase0 | exact Hso | unfold x_n; lia]. }
assert (Hcs' : cstr Wc memc (x_s X) (x_bs X)).
{ apply (cstr_from_entryR (wle' SEGS RZ_cf) _ _ (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) _ lyc Sc
    Hpc Wc memc mdc kc
    (x_Lam X) (x_peak X) _ _ (x_ran X) Lamc peakc _ _ ranc (x_s X) (x_bs X) HJ Hled0 Hled Hcs Hkept0 Hlive Hnfp).
  exact (pst_fp_closed X ch Hpre). }
destruct (str_shadow_at lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (x_s X) (x_n X + 1) HARc Hled Hkept Hn1)
  as (HRA & HHV).
unfold src_rd, bytes_at. rewrite length_skipn.
destruct Hcs' as (Hg & _).
split.
{ rewrite <- (firstn_skipn j (x_bs X)) in Hg. rewrite <- app_assoc in Hg.
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg. destruct Hg as (_ & Hg). rewrite length_firstn in Hg.
  replace (Nat.min j (length (x_bs X))) with j in Hg by lia.
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg. destruct Hg as (Hg & _). exact Hg. }
unfold x_n in *.
split; [lia|]. split; [lia|].
split; [unfold amem_range; unfold YGcfStr.amem_range8 in Har8; lia|].
split; [intros x Hx; apply HRA; lia|].
intros Hpos. apply (hull_sub _ (x_s X) (Z.of_nat (length (x_bs X)) + 1)); [exact HHV | lia | lia].
Qed.

(* ---- the release stretch's seat (B' + 0x2ec, after the closing-quote put) ---- *)
Definition pst_sv (X : psx) : list word := map (fun p => getr (x_regs X) (Z_to_bv 5 (snd p))) ps_saved_list.
Definition pst_E (X : psx) (pos : Z) (regs : bvmap 5 word) : env :=
  Eimg (Ereg regs (Z_to_bv 64 (x_F X pos) :: Z_to_bv 64 (x_FL X pos) :: Z_to_bv 64 (x_SHF X pos) :: pst_sv X)).

(* the facts the release stretch reads, from a join of the walk *)
Lemma pst_frame_facts : forall X ch pos P ly3 S3 Hp3 W3 mem3 md3 k3,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P ly3 S3 Hp3 W3 mem3 md3 k3 ->
  In (0, pos) (frames S3) /\ frame_addr ly3 0 pos = x_F X pos /\ flag_addr ly3 0 pos = x_FL X pos /\
  x_F X pos mod 32 = 0 /\ 4096 <= x_F X pos /\ x_F X pos + 64 <= YM05.alloc_ceiling /\
  (x_F X pos + 64 <= kLowShadowBeg \/ (kHighMemBeg <= x_F X pos /\ x_F X pos + 64 <= ASAN_CEIL)) /\
  (forall a, x_F X pos <= a < x_F X pos + 64 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  (forall i, 0 <= i < 8 -> apresent (w_H W3) mem3 (x_SHF X pos + i) /\ ~ aowned B ly3 S3 (x_SHF X pos + i)) /\
  x_SHF X pos = SHADOW_OFF + x_F X pos / 8 /\
  aowned B ly3 S3 (x_FL X pos) /\ app_addr (x_FL X pos) /\
  ~ in_img SEGS (x_FL X pos).
Proof.
intros X ch pos P ly3 S3 Hp3 W3 mem3 md3 k3 Hpre HCOM.
pose proof HCOM as (HJ & _).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as HLLE. pose proof (ajxR_frs HJ) as HFRS.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hin : In (0, pos) (frames S3)) by (rewrite HFRS; left; reflexivity).
assert (EF : frame_addr ly3 0 pos = x_F X pos) by (unfold x_F, frame_addr; rewrite HlyF; reflexivity).
assert (EFL : flag_addr ly3 0 pos = x_FL X pos) by (unfold x_FL, flag_addr; rewrite HlyF; reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR Hin) as (HF32 & HFapp & HFpres & HFsh).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite EF in HF32, HFapp, HFpres, HFsh, HF4096, HFceil. change (fs_frame_bytes 0) with 64 in *.
change (64 / 8) with 8 in HFsh.
destruct (FFLX _ _ _ _ _ _ 0 pos HAR Hin) as (HFLown & HFLapp & HFLimg). rewrite EFL in HFLown, HFLapp, HFLimg.
assert (HSHF : x_SHF X pos = SHADOW_OFF + x_F X pos / 8) by (unfold x_SHF, PS_SB; reflexivity).
split; [exact Hin|]. split; [exact EF|]. split; [exact EFL|]. split; [exact HF32|]. split; [exact HF4096|].
split; [exact HFceil|]. split; [unfold in_app in HFapp; lia|]. split; [exact HFpres|].
split; [intros i Hi; rewrite HSHF; exact (HFsh i Hi)|]. split; [exact HSHF|].
split; [exact HFLown|]. split; [exact HFLapp | exact HFLimg].
Qed.

Lemma pst_seat : forall X ch pos P ly3 S3 Hp3 W3 regs3 mem3 md3 k3,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P ly3 S3 Hp3 W3 mem3 md3 k3 -> apresent (w_H W3) mem3 (x_FL X pos) ->
  getr regs3 8 = w64 (x_sp X) -> getr regs3 21 = w64 (x_F X pos) -> getr regs3 22 = w64 (x_SHF X pos) ->
  getr regs3 24 = w64 (x_F X pos) ->
  img_env VAL A_LIM (pst_E X pos regs3) /\
  st_ok_pi SEGS VAL (pst_E X pos regs3) pst_ss
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_put_string + 748))) mem3 (seg_rom SEGS))).
Proof.
intros X ch pos P ly3 S3 Hp3 W3 regs3 mem3 md3 k3 Hpre HCOM HFLpres G8 G21 G22 G24.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & _).
destruct HFPRE as (HPRE & _ & Htopstk & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HCOM as (HJ & Hsav & HF56 & _). unfold ps_saved_ok in Hsav.
destruct (pst_frame_facts X ch pos P ly3 S3 Hp3 W3 mem3 md3 k3 Hpre HCOM) as (Hin & EF & EFL & HF32 & HF4096 & HFceil
  & HFapp & HFpres & HFsh & HSHF & HFLown & HFLapp & HFLimg).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
assert (Rng : forall x : bv 64, 0 <= bv_unsigned x < 2 ^ 64).
{ intros x. pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. exact Hx. }
set (F := x_F X pos) in *. set (FL := x_FL X pos) in *. set (SHF := x_SHF X pos) in *. set (sp := x_sp X) in *.
assert (HFLr : 4096 <= FL < ASAN_CEIL) by (apply app_addr_below_ceil; exact HFLapp).
unfold ASAN_CEIL in HFLr.
assert (HSHFr : SHADOW_OFF + 512 <= SHF /\ SHF + 8 <= kHighMemBeg).
{ rewrite HSHF. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. split; [lia|]. lia. }
assert (HSHFn : 0 <= SHF /\ SHF + 8 < YM05.alloc_ceiling) by (unfold kHighMemBeg, SHADOW_OFF in HSHFr; lia).
assert (DFS : F + 64 <= SHF \/ SHF + 8 <= F).
{ rewrite HSHF. unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (DFL1 : FL < F \/ F + 64 <= FL).
{ destruct (Z_lt_le_dec FL F) as [H1 | H1]; [left; exact H1|].
  destruct (Z_lt_le_dec FL (F + 64)) as [H2 | H2]; [exfalso | right; exact H2].
  exact (proj2 (HFpres FL ltac:(lia)) HFLown). }
assert (DFL2 : FL < SHF \/ SHF + 8 <= FL).
{ destruct (Z_lt_le_dec FL SHF) as [H1 | H1]; [left; exact H1|].
  destruct (Z_lt_le_dec FL (SHF + 8)) as [H2 | H2]; [exfalso | right; exact H2].
  pose proof (proj2 (HFsh (FL - SHF) ltac:(lia))) as Hn. replace (SHF + (FL - SHF)) with FL in Hn by lia.
  exact (Hn HFLown). }
set (E := pst_E X pos regs3).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pst_E; apply Eimg_env).
assert (E8 : ew E 8 = Z_to_bv 64 sp).
{ subst E. unfold pst_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl).
  exact G8. }
assert (E32 : ew E 32 = Z_to_bv 64 F)
  by (subst E; unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 FL)
  by (subst E; unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SHF)
  by (subst E; unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (ESV : forall i, (i < 13)%nat -> ew E (35 + i) = nth i (pst_sv X) (Z_to_bv 64 0)).
{ intros i Hi. subst E. unfold pst_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace (35 + i)%nat with (32 + (3 + i))%nat by lia. rewrite ew_Ereg_extra. reflexivity. }
assert (HSPr : YM05.alloc_ceiling + 208 <= sp <= 2 ^ 47) by (unfold sp, x_sp in *; lia).
assert (R8 : base_val E (Some 8%nat) = sp) by (cbn [base_val]; rewrite E8; apply unsigned_lit_small; lia).
assert (R32 : base_val E (Some 32%nat) = F) by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
assert (R33 : base_val E (Some 33%nat) = FL) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (R34 : base_val E (Some 34%nat) = SHF) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
rewrite Forall_forall in Hsav.
assert (SV : forall p, In p ps_saved_list ->
  val_mem SEGS (mrestrict (w_H W3) mem3) (sp + fst p) 8 (bv_unsigned (getr (x_regs X) (Z_to_bv 5 (snd p))))).
{ intros p Hp. apply (val_mem_of_rdword SEGS). exact (Hsav p Hp). }
split; [exact HEI|].
rewrite restrict_mkst_fx. unfold pst_ss. apply pa_entry_st_ok_full.
- unfold pst_regs.
  apply regs_ok_rereg; [| reflexivity | cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; exact G22].
  apply regs_ok_rereg; [| reflexivity | cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact G24].
  apply regs_ok_rereg; [| reflexivity | cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact G21].
  subst E. unfold pst_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pst_mem, fframe_reg, fshadow_reg, pst_flag, pst_saved.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite R32. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o) ltac:(lia))).
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ F 56 8 (SOff 33 0) FL);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ HF56).
  + rewrite R34. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFsh o ltac:(lia))).
  + rewrite R33. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLpres.
  + rewrite R8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?od (CVal 8 (SOff ?n 0))) =>
      let i := eval vm_compute in (n - 35)%nat in
      pose proof (ESV i ltac:(lia)) as Hx; cbn [Nat.add] in Hx;
      cbn [pst_sv map ps_saved_list nth snd] in Hx;
      lazymatch type of Hx with _ = getr _ (Z_to_bv 5 ?rr) =>
        apply (chunk_ok_val SEGS E _ sp od 8 (SOff n 0) (bv_unsigned (getr (x_regs X) (Z_to_bv 5 rr))));
          [ cbn [sv_denot]; rewrite Hx, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Rng
          | zside
          | exact (SV (od, rr) ltac:(cbv [ps_saved_list In]; tauto)) ] end end.
- apply pairwise_disjoint_of_extents.
  unfold pst_mem, fframe_reg, fshadow_reg, pst_flag, pst_saved, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite R32, R34, R33, R8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold pst_facts. split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32, E33, E34, !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  rewrite HSHF. unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

(* ---- the release stretch (B' + 0x2ec .. + 0x388, after the closing-quote put): the magic word at F, `beqz s5` not
   taken (s5 = F >= 4096), the f5 shadow bytes of F, `ld a0, 56(s5)` = FL and `sb zero, 0(a0)` = THE RELEASE
   (pst_flag_store_invR at wle' SEGS RZ_cf), the epilogue's 13 restores from the saved slots, `ret`; then the walk's
   final post at the entry float state fx0, in the kit's FLOAT form at the re-hiding relation (fpostWFR at wle' SEGS
   RZ_cf): the exit float state is this Section's fx, whose two float facts the walk carries (HFRM, HFK) ---- *)
Lemma pst_tail_end :
  (* STAND-IN (FPRX): flag-cell presence at the release; verified as AR_laws_x field 23, a citation
     when the P'' engine lands; at ARcfx it is YG0scf.AR_flag_law_ok_cf (its apresent conjunct) *)
  forall (FPRX : forall ly S Hp (W : world SEGS) mem md cid pos,
     ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos)),
  forall (fx0 : YK11.FPState), frm_zero (@fp_csr fx) -> fregs_kept_x fx0 fx ->
  forall X ch pos P2 ly3 S3 Hp3 W3 regs3 mem3 md3 k3,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P2 ly3 S3 Hp3 W3 mem3 md3 k3 ->
  P2 = WriterSpec.spieces (x_bs X) ->
  getr regs3 3 = getr (x_regs X) 3 -> getr regs3 4 = getr (x_regs X) 4 ->
  getr regs3 8 = w64 (x_sp X) -> getr regs3 21 = w64 (x_F X pos) -> getr regs3 22 = w64 (x_SHF X pos) ->
  getr regs3 24 = w64 (x_F X pos) ->
  SRr' SEGS RZ_cf W3 (mkCfg (mkst (fx := fx) regs3 (Z_to_bv 64 (BASE + (AF_put_string + 748))) mem3 (seg_rom SEGS))
    md3)
    (ps_Qfin fx0 X).
Proof.
intros FPRX fx0 HFRM HFK X ch pos P2 ly3 S3 Hp3 W3 regs3 mem3 md3 k3 Hpre HCOM HP2 G3 G4 G8 G21 G22 G24.
(* the entry float state must not be taken by instance resolution: only the Section's fx stays an FPState hypothesis *)
destruct fx0 as [fr0 fc0]. (* NB: the bare name fx0 is now YK11's global fx0; write mkFP fr0 fc0 *)
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & _).
destruct HFPRE as (HPRE & _ & Htopstk & _).
pose proof HPRE as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN0 as (Hd0 & _ & Hdtop & _).
pose proof HCOM as (HJ & Hsav & HF56 & Hok & HPM & HWR & Hroom & Hro & Hwk).
destruct (pst_frame_facts X ch pos P2 ly3 S3 Hp3 W3 mem3 md3 k3 Hpre HCOM) as (Hin & EF & EFL & HF32 & HF4096 & HFceil
  & HFapp & HFpres & HFsh & HSHF & HFLown & HFLapp & HFLimg).
pose proof (ajxR_ar HJ) as HAR3.
pose proof (FPRX _ _ _ _ _ _ 0 pos HAR3 Hin) as HFLpres. rewrite EFL in HFLpres.
destruct (pst_seat X ch pos P2 ly3 S3 Hp3 W3 regs3 mem3 md3 k3 Hpre HCOM HFLpres G8 G21 G22 G24) as (HEI & HS).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
set (F := x_F X pos) in *. set (FL := x_FL X pos) in *. set (SHF := x_SHF X pos) in *.
assert (HFLr : 4096 <= FL < ASAN_CEIL) by (apply app_addr_below_ceil; exact HFLapp).
unfold ASAN_CEIL in HFLr.
assert (HSHFr : SHADOW_OFF + 512 <= SHF /\ SHF + 8 <= kHighMemBeg).
{ rewrite HSHF. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. split; [lia|]. lia. }
assert (HSHFn : 0 <= SHF /\ SHF + 8 < YM05.alloc_ceiling) by (unfold kHighMemBeg, SHADOW_OFF in HSHFr; lia).
assert (HSPr : YM05.alloc_ceiling + 208 <= x_sp X <= 2 ^ 47) by (unfold x_sp in *; lia).
set (E := pst_E X pos regs3) in *.
assert (E8 : ew E 8 = Z_to_bv 64 (x_sp X)).
{ subst E. unfold pst_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl).
  exact G8. }
assert (E32 : ew E 32 = Z_to_bv 64 F)
  by (subst E; unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 FL)
  by (subst E; unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SHF)
  by (subst E; unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (R8 : base_val E (Some 8%nat) = x_sp X) by (cbn [base_val]; rewrite E8; apply unsigned_lit_small; lia).
assert (R32 : base_val E (Some 32%nat) = F) by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
assert (R33 : base_val E (Some 33%nat) = FL) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (R34 : base_val E (Some 34%nat) = SHF) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W3) mem3)) by constructor.
(* the run, to the `ret` (B' + 0x388, AF + 904; the token engine stops there: SR_jalr), at the re-hiding relation *)
unfold SRr'.
let K := eval vm_compute in (run_K A_LIM (SLit 0) [] pst_ss) in
let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi B_prog_listing PL_prog_B) (@pl_tw B_prog_listing PL_prog_B)
  K (SLit 0) (0, 0) [] FUEL pst_ss) in
lazymatch r with
| (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi B_prog_listing PL_prog_B) (@pl_tw B_prog_listing PL_prog_B)
    K (SLit 0) (0, 0) [] FUEL pst_ss = (st', rs)) by (vm_compute; reflexivity);
  apply (pst_flag_store_invR (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W3 FUEL E K (SLit 0)
    (0, 0) [] pst_ss st' rs
    (mkst regs3 (Z_to_bv 64 (BASE + (AF_put_string + 748))) mem3 (seg_rom SEGS))
    (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) []
    ly3 S3 Hp3 md3 k3 0 pos (ps_Qfin (mkFP fr0 fc0) X) ltac:(unfold A_LIM; cbn; lia) HEI ltac:(lia) HS SHOK
    ltac:(vm_compute; reflexivity) Hrun I HJ HPM); clear Hrun
end.
- (* no shadow obligation *)
  cbn [sh_obls]. constructor.
- (* the writes: F's first 32 bytes and F's shadow (the owned frame), the flag byte *)
  intros a (r & Hin' & Hx). unfold pst_ss, pst_mem in Hin'. cbn [ss_mem In] in Hin'.
  destruct Hin' as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi fframe_reg fshadow_reg pst_flag pst_saved] in Hx;
    rewrite ?R32, ?R33, ?R34, ?R8 in Hx.
  + left. unfold awr_byte. right; right; right. exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  + left. unfold awr_byte. right; right; right. exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0 / 8) with 8.
    unfold shadow_addr. rewrite HSHF in Hx. lia.
  + right. rewrite EFL. lia.
  + lia.
- (* the flag byte reads 0 at the end of the run (the flag region's chunk) *)
  intros ws msr Hlen HSr. cbn [sh_j] in Hlen. destruct ws as [|w ws]; [|cbn in Hlen; discriminate Hlen].
  cbn [extK sh_ss] in HSr. unfold st_ok_pi in HSr.
  lazymatch type of HSr with st_ok _ _ ?ssa _ =>
    let rv := eval vm_compute in (nth_error (ss_mem ssa) 2) in
    lazymatch rv with Some ?rg =>
      pose proof (st_ok_region_nth SEGS E ssa msr 2 rg HSr ltac:(vm_compute; reflexivity)) as HRG end end.
  assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
  pose proof (field_of_region SEGS E (ms_mem msr) 33 FL _ 0 1 0 1 0 1 (SLit 0) 0 HRG U33
    ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HV.
  specialize (HV 0%nat ltac:(cbn; lia)).
  replace (FL + 0 + Z.of_nat 0) with FL in HV by lia. rewrite EFL. exact HV.
- (* the run's end: the `ret`, then the post *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HPM' HF HFr HG.
  cbn [sh_j] in Hlen. destruct ws as [|w ws]; [|cbn in Hlen; discriminate Hlen].
  cbn [extK sh_ss] in HS', HEI'. cbn [ms_mem mkst] in HF, HFr, HG.
  (* the registers at the return: ra, sp, s0 .. s11 restored, gp / tp kept *)
  assert (RA : getr (ms_regs ms') 1 = getr (x_regs X) 1).
  { rewrite (st_ok_pi_restrict_reg _ _ _ ms' 1%bv HS').
    lazymatch goal with |- sv_denot _ (sr_get ?sr ?rr) = _ =>
      let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    subst E. unfold pst_E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
    cbn [Nat.ltb Nat.leb Nat.sub nth pst_sv map ps_saved_list snd]. reflexivity. }
  assert (RF : aregs_preserved (x_regs X) (ms_regs ms')).
  { intros r Hr. unfold acallee_saved in Hr.
    rewrite (st_ok_pi_restrict_reg _ _ _ ms' (Z_to_bv 5 r) HS').
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr. subst E.
    repeat (destruct Hc as [-> | Hc];
      [ lazymatch goal with |- sv_denot _ (sr_get ?sr ?rr) = _ =>
          let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end;
        cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); unfold Ereg; cbn [ew];
        cbn [Nat.ltb Nat.leb Nat.sub nth pst_sv map ps_saved_list snd];
        first [ reflexivity | exact G3 | exact G4
              | transitivity (w64 (x_sp X)); [exact G8 | unfold w64, x_sp, spZ; apply Z_to_bv_bv_unsigned] ]
      | ]).
    subst r.
    lazymatch goal with |- sv_denot _ (sr_get ?sr ?rr) = _ =>
      let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end;
    cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    unfold pst_E; rewrite Eimg_low by (unfold A_TEXT; lia); unfold Ereg; cbn [ew];
    cbn [Nat.ltb Nat.leb Nat.sub nth pst_sv map ps_saved_list snd]; reflexivity. }
  (* every byte above sp, of the image or of a live block of the join is kept by the run *)
  assert (KEEP : forall a, (x_sp X <= a < 2 ^ 64 \/ in_img SEGS a \/
      exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m) ->
    aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha.
    destruct (pst_out_own X ch pos ly3 S3 Hp3 W3 mem3 md3 k3 a Hpre HJ Ha) as (O1 & O2 & O3). fold F in O2.
    assert (HaFL : a <> FL).
    { intros ->. destruct Ha as [Ha | [Hi | (b & m & HB & Hb)]].
      - unfold x_sp in *. lia.
      - exact (HFLimg Hi).
      - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR3 HB) as (_ & _ & _ & _ & Hbo & _).
        exact (proj2 (Hbo FL Hb) HFLown). }
    apply (kept_of_frame E pst_mem (w_H W3) mem3 (ms_mem ms') (fun x => x = a) HFr); [|reflexivity].
    intros x ->. split.
    - destruct Ha as [Ha | [Hi | (b & m & HB & Hb)]].
      + unfold x_sp in *. lia.
      + pose proof (segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
      + destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR3 HB) as (_ & Hb4096 & Hbceil & _). lia.
    - intros (r & Hin' & Hx). unfold pst_mem in Hin'. cbn [In] in Hin'.
      destruct Hin' as [<- | [<- | [<- | [<- | []]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi fframe_reg fshadow_reg pst_flag pst_saved] in Hx;
        rewrite ?R32, ?R33, ?R34, ?R8 in Hx.
      + lia.
      + unfold kHighMemBeg, SHADOW_OFF in *. lia.
      + apply HaFL. lia.
      + lia. }
  (* the return stays in the world W3: the plain step relation suffices from here *)
  apply (SRr_SRrG SEGS (wle' SEGS RZ_cf) (wle_wle' SEGS RZ_cf)).
  eapply (RET W3 _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat2.
  unfold ps_Qfin. split; [| exact HPM'].
  (* THE FLOAT POST (fpostWFR at wle' SEGS RZ_cf): the exit float state is the current fx *)
  unfold fpostWFR. exists fx.
  lazymatch goal with |- exists _ _ _ _ _ _ _, ?c = _ /\ _ =>
    lazymatch c with mkCfg (mkst ?rg _ ?m _) ?d => exists ly3, (stack_free_state 0 pos S3), Hp3, rg, m, d, k3 end end.
  split; [rewrite RA; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [exact HFRM|]. split; [exact HFK|].
  split; [apply (ajournal_x_materializeR SEGS B (@prh_pst prh_img_B) ARx LAWS segs_low (wle' SEGS RZ_cf)); exact HJ'|].
  split.
  { intros a Ha Hnfp. unfold ps_wkeep in Hwk.
    assert (Hal : x_sp X <= a < 2 ^ 64) by (unfold x_sp in *; lia).
    rewrite (KEEP a (or_introl Hal)). exact (Hwk a Ha Hnfp). }
  split; [exact RF|].
  unfold ps_Qin. split; [apply RL_stack_free; exact Hroom|].
  rewrite <- HP2.
  destruct HWR as (ok & ranc & bufc & Lamc & peakc & Hoks & Hout & Hled & Hblk & Hkept & Hlive & Hdisj & (rph & Hrp)).
  unfold ps_oks in Hoks. destruct Hoks as (Hoks & Hgk).
  (* the writer clause's outcomes ok, NO REFUSAL among them (prh_granted, DEAD-PUTSTRING), with the room position
     at the EXACT advance under them, kept across the release (PresetRoomPosKeep.room_pos_stack_free) *)
  exists ok. split; [| split; [exact Hgk | exists rph; apply PresetRoomPosKeep.room_pos_stack_free; exact Hrp]].
  set (st2 := prhWriter_putN ok (x_st X) P2) in *.
  assert (Eab : ablocks B ly3 (stack_free_state 0 pos S3) = ablocks B ly3 S3)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  assert (Hcase : WriterApp.w_cap st2 <> 0 -> In (bufc, WriterApp.w_cap st2) Lamc).
  { intros Hc0. destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & HinL & _)]); [lia | exact HinL]. }
  pose proof (@cf_head_nonneg cp) as Hh.
  pose proof (ps_led_blocks B _ _ _ _ _ _ _ _ _ _ Hled) as HallL. rewrite Forall_forall in HallL.
  assert (KB : forall b k a, In (b, k) Lamc -> b - cf_head <= a < b + k ->
    aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) mem3 a).
  { intros b k a Hin' Ha. apply KEEP. right. right.
    destruct (HallL _ Hin') as (Hk0 & HB & _). cbn [fst snd] in Hk0, HB.
    exists (b - cf_head), (k + cf_head). split; [exact HB|].
    assert (Hz : 0 <= k + cf_head) by lia. pose proof (req_size_pos _ Hz) as Rq. lia. }
  assert (HLEDf : prh_ledger B ly3 (stack_free_state 0 pos S3) Hp3 W3 (ms_mem ms') Lamc peakc
    (WriterApp.w_cnt st2) (WriterApp.w_fail st2) ranc (x_most X) (x_own X)).
  { apply (prh_ledger_kept ly3 S3 Hp3 W3 mem3 Lamc peakc _ _ ranc _ _ ly3 (stack_free_state 0 pos S3) W3 (ms_mem ms')
      Hled Eab).
    - intros a Ha. apply KEEP. right. left. exact (proj1 (PST_ok a Ha)).
    - intros b k a Hin' Ha. apply (KB b k a Hin'). unfold prh_head_wide in HW.
      destruct (HallL _ Hin') as (Hk0 & _). cbn [snd] in Hk0. lia. }
  (* The batch kit's prhWriter_ret_ok from the granted run's parts (Model's prhW_ret_ok_close_g) *)
  apply (prhW_ret_ok_close_g B ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ranc bufc Lamc peakc Hgk).
  + pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hled0e & _).
    exact (ps_led_peak B _ _ _ _ _ _ _ _ _ _ Hled0e).
  + exact Hoks.
  + apply (prhW_out_kept W3 mem3 Lamc (x_o X) bufc st2 W3 (ms_mem ms') ly3 (stack_free_state 0 pos S3) Hp3 _ Hout
      (ajxR_ar HJ')).
    * intros Hc0. pose proof (ps_led_blocks B _ _ _ _ _ _ _ _ _ _ HLEDf) as Hall. rewrite Forall_forall in Hall.
      exact (Hall _ (Hcase Hc0)).
    * intros a Ha. apply KEEP. left. unfold x_sp in *. lia.
    * intros Hc0 a Ha. apply (KB _ _ a (Hcase Hc0)). lia.
  + exact HLEDf.
  + unfold prhWriter_blk in *. rewrite Eab. exact Hblk.
Qed.

(* ---- THE TAIL (B' + 0x2c8 .. + 0x388): the closing put of the pending run [j, n) (+ 0x2d4), the closing-quote put
   (+ 0x2e8), then pst_tail_end; at the current float state fx, whose float facts the walk carries ---- *)
Lemma ps_tail_run :
  (* STAND-IN (FPRX): flag-cell presence at the release; verified as AR_laws_x field 23, a citation
     when the P'' engine lands; at ARcfx it is YG0scf.AR_flag_law_ok_cf (its apresent conjunct) *)
  forall (FPRX : forall ly S Hp (W : world SEGS) mem md cid pos,
     ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos)),
  forall (fx0 : YK11.FPState), frm_zero (@fp_csr fx) -> fregs_kept_x fx0 fx ->
  forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_tail X pos j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (BASE + (AF_put_string + 712))) memc (seg_rom SEGS))
    mdc)
    (ps_Qfin fx0 X).
Proof.
intros FPRX fx0 HFRM HFK X ch Hpre HS0 pos j P lyc Sc Hpc Wc regsc memc mdc kc HT.
unfold SRr'.
destruct fx0 as [fr0 fc0].
destruct HT as (HCOM & Hj & HPeq & G2 & G3 & G4 & G8 & G9 & G19 & G18 & G20 & G21 & G22 & G24).
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & _ & _ & Hcstr0 & _).
destruct HFPRE as (HPRE & _ & _ & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN0 as (Hd0 & _ & Hdtop & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
pose proof (pa_B_ok (L := B_prog_listing) (PAImg := PA)) as (HB0 & HB1 & _).
pose proof Hcstr0 as (_ & Hs4096 & Hsceil & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & HR32).
assert (Hspr : YM05.alloc_ceiling + 208 <= x_sp X <= 2 ^ 47) by (unfold x_sp in *; lia).
assert (HSP : WriterSpec.spieces (x_bs X) = (P ++ [skipn j (x_bs X)]) ++ [[34]]).
{ unfold WriterSpec.spieces. rewrite <- HPeq. reflexivity. }
pose proof (AF_ps_ret_k 728 ltac:(lia) ltac:(reflexivity)) as (H688 & H688b).
pose proof (AF_ps_ret_k 748 ltac:(lia) ltac:(reflexivity)) as (H708 & H708b).
(* ---- stretch 1 (+ 0x2c8 .. + 0x2d4): a2 := s4 - s2, a0 := s3, a1 := s2, `jal put` ---- *)
set (E1 := Eimg (Ereg regsc [])).
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (E1r : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E1 n = getr regsc r).
{ intros n r Hn Hr. subst E1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regsc _ n r Hr). }
assert (HS1 : st_ok_pi SEGS VAL E1 pst_ss1
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 712))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pst_ss1. apply pa_entry_st_ok_full.
  - subst E1. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
pose proof HCOM as (HJ & _ & _ & _ & HPM & _).
pnt_run_to_inv NTRUNTOI HS1 HJ HPM (AF_put_string + 728).
{ intros a (r & Hr & _). cbn [In ss_mem pst_ss1] in Hr. destruct Hr. }
rename ms into ms1. rename mat into mat1.
pmkst HS1.
prreg HS1 (10%bv : bv 5) A0. prreg HS1 (11%bv : bv 5) A1.
prreg HS1 (1%bv : bv 5) Ra1. prreg HS1 (2%bv : bv 5) Sp1. prreg HS1 (3%bv : bv 5) Gp1. prreg HS1 (4%bv : bv 5) Tp1.
prreg HS1 (8%bv : bv 5) S01.
lazymatch type of Ra1 with context [BASE + ?k] =>
  assert (Hk688 : k = AF_put_string + 728)
    by (unfold AF_put_string; rewrite (proj2 B_entry_put_string); vm_compute; reflexivity);
  rewrite Hk688 in Ra1 end.
assert (RA0 : getr (ms_regs ms1) 10 = w64 (x_o X)) by (rewrite A0, (E1r 19%nat 19%bv) by (lia || reflexivity); exact G19).
assert (RA1 : getr (ms_regs ms1) 11 = w64 (x_s X + Z.of_nat j))
  by (rewrite A1, (E1r 18%nat 18%bv) by (lia || reflexivity); exact G18).
assert (RA2 : getr (ms_regs ms1) 12 = w64 (Z.of_nat (length (skipn j (x_bs X))))).
{ pose proof (st_ok_restrict_reg SEGS _ E1 _ ms1 (12%bv : bv 5) HS1) as Hr.
  lazymatch type of Hr with _ = sv_denot _ (sr_get ?sr ?rr) =>
    let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v in Hr end.
  rewrite Hr. clear Hr.
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite U_SLit.
  rewrite (U_atom E1 20 (x_s X + x_n X)) by (first [rewrite (E1r 20%nat 20%bv) by (lia || reflexivity); exact G20
    | unfold x_n in *; lia]).
  rewrite (U_atom E1 18 (x_s X + Z.of_nat j)) by (first [rewrite (E1r 18%nat 18%bv) by (lia || reflexivity); exact G18
    | unfold x_n in *; lia]).
  rewrite length_skipn. unfold zcanon, M64.
  (* B' engine form: (s + j) * (-1) + (s + n), the product first *)
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  rewrite Z.add_mod_idemp_l by (clear; lia).
  replace ((x_s X + Z.of_nat j) * (2 ^ 64 - 1) + (x_s X + x_n X))
    with ((x_n X - Z.of_nat j) + (x_s X + Z.of_nat j) * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. unfold x_n in *. rewrite Z.mod_small by lia. lia. }
assert (HCOM1 : ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc (ms_mem ms1) (with_vm_backing (m_vm_lazy mdc) mat1 mdc)
  kc).
{ apply (pst_common_frame X ch pos P lyc Sc Hpc Wc memc mdc kc E1 _ (ms_mem ms1) _ kc Hpre HCOM HJ HPM HFr).
  intros a (r & Hr & _). cbn [In ss_mem pst_ss1] in Hr. destruct Hr. }
(* ---- put #4 of the walk: put(o, s + j, n - j) ---- *)
eapply (ps_put_step X ch pos P (skipn j (x_bs X)) [[34]] lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ kc
  (Z_to_bv 64 (BASE + (AF_put_string + 728))) (x_s X + Z.of_nat j)).
- exact HFRM.
- exact Hpre.
- exact HS0.
- exact HCOM1.
- rewrite HSP, <- app_assoc. reflexivity.
- unfold spZ at 1. rewrite Sp1, (E1r 2%nat 2%bv), G2 by (lia || reflexivity). unfold w64.
  apply unsigned_lit_small. unfold x_R, x_sp in *. lia.
- rewrite Gp1, (E1r 3%nat 3%bv), G3 by (lia || reflexivity). exact Hgp.
- rewrite Tp1, (E1r 4%nat 4%bv), G4 by (lia || reflexivity). exact Htp.
- exact Ra1.
- apply ret_ok_codeptr_v; [exact (proj1 H688) | exact (proj2 H688)].
- rewrite unsigned_lit_small by lia. exact H688b.
- rewrite unsigned_lit_small by lia. apply ps_ret_lt_ceil. cbn [In]. tauto.
- unfold s0Z. rewrite S01, (E1r 8%nat 8%bv), G8 by (lia || reflexivity). unfold w64.
  apply unsigned_lit_small. lia.
- exact RA0.
- exact RA1.
- exact RA2.
- exact (pst_src_tail X ch pos P lyc Sc Hpc Wc (ms_mem ms1) _ kc j Hpre HCOM1 Hj).
- intros Lamc bufc capc Hk Hd _ _. exact (pst_home_tail X lyc Sc Lamc bufc capc j Hj Hk Hd).
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HCOM2 HP2 _ _ _.
  unfold SRr'.
  (* ---- stretch 2 (+ 0x2d8 .. + 0x2e8): a1 := .str.18, a2 := 1, a0 := s3, `jal put` ---- *)
  jafter_call_keep_pi HS1 64%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
  match type of HS2 with ?Pq -> _ => assert (HQ : Pq); [constructor | specialize (HS2 HQ); clear HQ] end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Epv _ _ => set (Ep := Epv) in HS2 end.
  assert (HEIp : img_env VAL A_LIM Ep) by (subst Ep; apply img_env_havoc; [exact HEI1 | cbv; lia]).
  assert (Epold : forall k, (k < 64)%nat -> ew Ep k = ew E1 k) by (intros k Hk; subst Ep; apply ew_havoc_old; exact Hk).
  assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ep n = getr regsc r).
  { intros n r Hn Hr. rewrite Epold by lia. apply E1r; assumption. }
  rewrite <- restrict_mkst_fx in HS2.
  lazymatch type of HS2 with context [Z_to_bv 64 (BASE + ?k)] =>
    assert (Hk2 : k = AF_put_string + 728)
      by (unfold AF_put_string; rewrite (proj2 B_entry_put_string); vm_compute; reflexivity);
    rewrite Hk2 in HS2 end.
  clear HS1 A0 A1 Ra1 Sp1 Gp1 Tp1 S01 RA0 RA1 RA2 HP2 HF HFr HG HCOM1 HJ HPM.
  pose proof HCOM2 as (HJ2 & _ & _ & _ & HPM2 & _).
  pnt_run_to_inv NTRUNTOI HS2 HJ2 HPM2 (AF_put_string + 748).
  { intros a (r & Hr & _). cbn [In ss_mem] in Hr. destruct Hr. }
  rename ms into ms2. rename mat into mat2.
  pmkst HS2.
  prreg HS2 (10%bv : bv 5) B0. prreg HS2 (11%bv : bv 5) B1. prreg HS2 (12%bv : bv 5) B2.
  prreg HS2 (1%bv : bv 5) Rb1. prreg HS2 (2%bv : bv 5) Spb. prreg HS2 (3%bv : bv 5) Gpb. prreg HS2 (4%bv : bv 5) Tpb.
  prreg HS2 (8%bv : bv 5) S0b. prreg HS2 (21%bv : bv 5) S5b. prreg HS2 (22%bv : bv 5) S6b.
  prreg HS2 (24%bv : bv 5) S8b.
  lazymatch type of Rb1 with context [BASE + ?k] =>
    assert (Hk708 : k = AF_put_string + 748)
      by (unfold AF_put_string; rewrite (proj2 B_entry_put_string); vm_compute; reflexivity);
    rewrite Hk708 in Rb1 end.
  assert (RB0 : getr (ms_regs ms2) 10 = w64 (x_o X)) by (rewrite B0, (ER 19%nat 19%bv) by (lia || reflexivity); exact G19).
  assert (RB1 : getr (ms_regs ms2) 11 = w64 (ps_str 65)).
  { rewrite B1, (HEIp 243%nat ltac:(unfold A_TEXT, A_LIM; lia)). unfold ps_str, w64. change (A_OBJ 2) with 243%nat.
    f_equal; try (f_equal; vm_compute; reflexivity). }
  assert (HCOM3 : ps_commonR (wle' SEGS RZ_cf) X pos (P ++ [skipn j (x_bs X)]) ly2 S2 Hp2 W2 (ms_mem ms2)
    (with_vm_backing (m_vm_lazy md2) mat2 md2) (kc + k1)).
  { apply (pst_common_frame X ch pos _ ly2 S2 Hp2 W2 mem2 md2 (kc + k1) Ep _ (ms_mem ms2) _ (kc + k1) Hpre HCOM2 HJ2
      HPM2 HFr).
    intros a (r & Hr & _). cbn [In ss_mem] in Hr. destruct Hr. }
  pose proof HCOM3 as (HJ3 & _ & _ & _ & _ & _ & _ & HRO3 & _).
  destruct (HLIT18 _ _ _ _ _ _ (ajxR_ar HJ3) HRO3) as (HSRC17 & HK17).
  assert (Hlit_img : in_img SEGS (ps_str 65)).
  { assert (Hx65 : ps_str 65 <= ps_str 65 < ps_str 65 + 1) by lia.
    destruct HK17 as [(b & m & Hin & _) | [(_ & _ & _ & Hall) | Himg]]; [destruct Hin | |].
    - destruct (Hall (ps_str 65) Hx65) as (Hro & _). exact (in_roP_img _ Hro).
    - unfold kept_img in Himg. destruct Himg as (_ & _ & Hall).
      destruct (Hall (ps_str 65) Hx65) as (Hro & _). exact (in_roP_img _ Hro). }
  (* ---- put #5 of the walk: put(o, .str.18, 1), the closing quote ---- *)
  eapply (ps_put_step X ch pos (P ++ [skipn j (x_bs X)]) [34] [] ly2 S2 Hp2 W2 (ms_regs ms2) (ms_mem ms2) _ (kc + k1)
    (Z_to_bv 64 (BASE + (AF_put_string + 748))) (ps_str 65)).
  + exact HFRM.
  + exact Hpre.
  + exact HS0.
  + exact HCOM3.
  + exact HSP.
  + unfold spZ at 1. rewrite Spb, (ER 2%nat 2%bv), G2 by (lia || reflexivity). unfold w64.
    apply unsigned_lit_small. unfold x_R, x_sp in *. lia.
  + rewrite Gpb, (ER 3%nat 3%bv), G3 by (lia || reflexivity). exact Hgp.
  + rewrite Tpb, (ER 4%nat 4%bv), G4 by (lia || reflexivity). exact Htp.
  + exact Rb1.
  + apply ret_ok_codeptr_v; [exact (proj1 H708) | exact (proj2 H708)].
  + rewrite unsigned_lit_small by lia. exact H708b.
  + rewrite unsigned_lit_small by lia. apply ps_ret_lt_ceil. cbn [In]. tauto.
  + unfold s0Z. rewrite S0b, (ER 8%nat 8%bv), G8 by (lia || reflexivity). unfold w64.
    apply unsigned_lit_small. lia.
  + exact RB0.
  + exact RB1.
  + exact B2.
  + exact HSRC17.
  + intros Lamc bufc capc Hk Hd Hin Hblks. change (Z.of_nat (length [34])) with 1.
    split; [left; exact (kept_at_nil_lam Lamc _ _ HK17)|].
    destruct (Z.eq_dec capc 0) as [Hz0 | Hnz]; [left; exact Hz0 | right].
    pose proof (Hblks _ _ (Hin Hnz)) as HinB. pose proof (@cf_head_nonneg cp) as Hch0.
    destruct (Z_lt_le_dec (ps_str 65) bufc) as [Hl | Hge]; [left; clear - Hl; lia|].
    destruct (Z_lt_le_dec (ps_str 65) (bufc + capc)) as [Hl2 | Hge2]; [|right; clear - Hge2; lia].
    exfalso.
    assert (Hcz : 0 <= capc + cf_head) by (clear - Hge Hl2 Hch0; lia).
    assert (Hin_blk : bufc - cf_head <= ps_str 65 < bufc - cf_head + req_size (capc + cf_head)).
    { pose proof (req_size_pos _ Hcz) as Rq. clear - Hge Hl2 Rq Hch0. lia. }
    apply (proj2 (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ (ps_str 65) (ajxR_ar HJ3)
      (or_introl (ex_intro _ (bufc - cf_head) (ex_intro _ (capc + cf_head) (conj HinB Hin_blk)))))).
    exact Hlit_img.
  + intros ly3 S3 Hp3 W3 regs3 mem3 md3 k2 HCOM4 HP3 _ _ _.
    assert (PR : forall (r : Z), acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr (ms_regs ms2) (Z_to_bv 5 r))
      by exact HP3.
    assert (CS : forall r, 2 <= r <= 27 -> r <> 5 -> r <> 6 -> r <> 7 -> (r < 10 \/ 18 <= r) -> acallee_saved r).
    { intros r H1 H2 H3 H4 H5. unfold acallee_saved. lia. }
    apply (pst_tail_end FPRX (mkFP fr0 fc0) HFRM HFK X ch pos ((P ++ [skipn j (x_bs X)]) ++ [[34]]) ly3 S3 Hp3 W3 regs3 mem3 md3
      (kc + k1 + k2) Hpre HCOM4).
    * symmetry. exact HSP.
    * transitivity (getr (ms_regs ms2) 3%bv); [exact (PR 3 (CS 3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))|].
      transitivity (ew Ep 3); [exact Gpb|]. transitivity (getr regsc 3%bv); [apply ER; [lia | reflexivity]|]. exact G3.
    * transitivity (getr (ms_regs ms2) 4%bv); [exact (PR 4 (CS 4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))|].
      transitivity (ew Ep 4); [exact Tpb|]. transitivity (getr regsc 4%bv); [apply ER; [lia | reflexivity]|]. exact G4.
    * transitivity (getr (ms_regs ms2) 8%bv); [exact (PR 8 (CS 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))|].
      transitivity (ew Ep 8); [exact S0b|]. transitivity (getr regsc 8%bv); [apply ER; [lia | reflexivity]|]. exact G8.
    * transitivity (getr (ms_regs ms2) 21%bv);
        [exact (PR 21 (CS 21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))|].
      transitivity (ew Ep 21); [exact S5b|]. transitivity (getr regsc 21%bv); [apply ER; [lia | reflexivity]|]. exact G21.
    * transitivity (getr (ms_regs ms2) 22%bv);
        [exact (PR 22 (CS 22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))|].
      transitivity (ew Ep 22); [exact S6b|]. transitivity (getr regsc 22%bv); [apply ER; [lia | reflexivity]|]. exact G22.
    * transitivity (getr (ms_regs ms2) 24%bv);
        [exact (PR 24 (CS 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))|].
      transitivity (ew Ep 24); [exact S8b|]. transitivity (getr regsc 24%bv); [apply ER; [lia | reflexivity]|]. exact G24.
Qed.

End h.
End f.
End d.
