(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30), this file: put_string's
   walk, SEGMENT E (the ESCAPE): from the escape join ps_esc (B' + 0x1c8 = AF + 456, the return of the run put) through
   the escape's write into u = F + 32 (__asan_memcpy of .str.21 "\\t" / .str.20 "\\n" / .str.22 "\\r" for c = 9 / 10 /
   13, else __wrap_snprintf (u, 8, "\\%c" or "\\u%04x", c)), __wrap_strlen (u) (+ 0x254), put (o, u, len) (+ 0x264),
   the UBSan pointer-overflow check of s + i (+ 0x26c `beq s10, -1` to the trap + 0x38c, NOT TAKEN: s + i lies below
   the allocation ceiling), the re-poison of u's shadow granule (+ 0x274 `sb -8, 4(s6)`) and `mv s2, s4` (j := i + 1),
   to the next join ps_next (+ 0x27c = AF + 636). Over PutStringB_Base.v, toward the #102 tput_string_specX
   (PRH_FnWriter.v 2b497bc72172).
   PORTED from image A's walk of this segment, lib/A/Prog/PRW_put_string_e.v (reuse, not trust): B' offsets / registers, the
   B' order (put before the overflow check and the re-poison), and the snprintf call through the stand-in AS THE ROW
   GIVES IT (YGcallSnpCk.snp_esc_realizes_xrom: some fx' post, frm = 0 at entry), never A's fx-keeping SNPK.
   FLOAT STATE: every lemma is at this Section's fx; its final post is ps_Qfin fx0 X at the ENTRY state fx0 (explicit).
   The memcpy arms continue at fx (pe_tail, k = 568); the snprintf arms call snprintf at fx and finish by the
   continuation KS at the returned fx' (ps_esc_run's premise; the owner discharges it with pe_tail at fz := fx').
   Added Section hypotheses (beyond PutStringB_A.v's header): AMCPY (__asan_memcpy, YGcallMxmn aintrin_realizes_xm,
   owner R2), ASTRLEN (__wrap_strlen, YGcallMxmn astrlen_realizes_xrom, owner R2), the
   snprintf instance's Variables Kp lo hi gcan can img_lo img_hi cr with ONE instance condition HSNPI (ps_snp_inst,
   discharged by the row's instance owner at PI_prog_B) and SNP (YGcallSnpCk snp_esc_realizes_xrom,
   bridged from the row's text by snp_esc_of_xrom). The stretch crosses ONE trap branch (the overflow check
   above) and no ASan report branch (the copies and the strlen are interceptor calls; the re-poison is a plain store).
   No address literal: entries, return sites and literals are by name (B_prog_slot, the listing's PAddHi addends).
   THE RE-HIDING MOVE: the whole escape runs after the opening-quote put, and put reallocs when it grows (a crossing
   call), so the escape's joins are ps_commonR at wle' SEGS RZ_cf, its journals are at that relation, its runs and
   branches are the R forms there, and it concludes SRr' SEGS RZ_cf; the continuations pe_KN / pe_KS keep their
   bodies and their R forms pe_KNR / pe_KSR stand beside them, at wle' SEGS RZ_cf in every statement here. The three
   runtime calls keep the world: the strlen and memcpy rules (aj_strlen_at_xromR, aj_intrin_at_xmR) and the snprintf
   row lift by SRr_SRr'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the step relation over a world relation and the re-hiding relation (SRrG, wle', SRr' with its bind / mono,
   paj_branchR) and the fixed zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0b YO0c FMsnprintfShared YGcallSnp YGcallSnpCk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia must see the division equations: the realignment is a mod 32 (never rely on an inherited flag) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's generated numbers (lib/B/PRH_ImgB.v, the #102 B' table) are the PrhImg the texts read *)
#[local] Existing Instance prh_img_B.

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
(* the image's shadow is visible over the instance's bounds (PutStringB_Base.v HIMGSH: YGcfAmx2.img_shadow_vis_cf
   at IMG_LO_B / IMG_TOP_B) and every live fake frame's shadow hull (ARx_frame_hull_vis, YGcfFsVis.v) *)
Hypothesis HIMGSH : forall ly S Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis HFHULL : ARx_frame_hull_vis SEGS ARx.
(* the instance's image bounds (IMAGE FACT, PI_prog_B: IMG_LO_B / IMG_TOP_B, below the low shadow) *)
Hypothesis HPAB : 4096 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= kLowShadowBeg.
(* alloc.c's six statics and fuzz_preset.c's g_own_ran_out (the ledger's globals, prh_pst, PRH_Base.v:752-755) are image bytes the runtime does not own, apart from errno, and none
   lies in the read-only band (YC1fPx's PST_ok; PRW_pj_write.v's pj_write walk takes the same texts less the errno conjunct; image facts) *)
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
(* the tokenless runner and the branch at the re-hiding relation: every stretch of this file runs after the
   opening-quote put *)
Let NTRUNTOI := SRr_run_to_pi_AJx_invR B ARx LAWS Pm PLAW (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BR := paj_branchR (PI := PA) (wle' SEGS RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_B) (PI := PA).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx).
Local Notation AJR R := (ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx R).
Variable CTX0 : list (list Z).
(* put's text (the #102 tput_specX), at this Section's float state: the ONE callee-text use of put in this file *)
Hypothesis PUT : tput_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* FRM0-ENTRY (fpre's last conjunct) at this Section's float state: the rounding mode is 0 at the escape put's
   entry (pe_tail is applied at the memcpy state or at the float state snprintf returns, both with frm = 0) *)
Hypothesis HFRMx : frm_zero (@fp_csr fx).
(* the double-quote literal .str.18 put_string puts twice (IMAGE FACT, discharged at PI_prog_B; pj_write's HLIT form):
   its byte is the image's, its shadow the read-only global's, at every state *)
Hypothesis HLIT18 : ps_lit_fact B ARx 65 [34].
(* the five escape literals the loop reads from the R block (IMAGE FACTS, discharged at PI_prog_B; bytes read off the
   B' image's .rodata): .str.21 "\\t", .str.20 "\\n", .str.22 "\\r", .str.19 "\\%c", .str.23 "\\u%04x" *)
Hypothesis HLIT85 : ps_lit_fact B ARx 85 [92; 116; 0].
Hypothesis HLIT87 : ps_lit_fact B ARx 87 [92; 110; 0].
Hypothesis HLIT91 : ps_lit_fact B ARx 91 [92; 114; 0].
Hypothesis HLIT93 : ps_lit_fact B ARx 93 [92; 37; 99; 0].
Hypothesis HLIT89 : ps_lit_fact B ARx 89 [92; 117; 37; 48; 52; 120; 0].
(* the base file's lemmas at this section's variables and hypotheses; put's call step: its join premise, its
   continuation's join and its conclusion SRr' are at wle' SEGS RZ_cf *)
Local Notation ps_put_step := (ps_put_step B ARx LAWS segs_low HPAB HPSTRO Pm PCALL CTX0 PUT).
Local Notation ps_pre := (ps_pre B ARx CTX0).
Local Notation ps_commonR := (ps_commonR B ARx Pm).
Local Notation ps_esc := (ps_esc B ARx Pm).
Local Notation ps_next := (ps_next B ARx Pm).
Local Notation ps_Qfin := (ps_Qfin B ARx Pm).
Local Notation ps_common_frameR := (ps_common_frameR B ARx LAWS segs_low HW PST_ok Pm CTX0).
Local Notation ps_common_runR := (ps_common_runR B ARx LAWS HW PST_ok Pm).

(* ==================== this file's additions ==================== *)
(* __asan_memcpy's text in the m-form at its entry, at this Section's fx (YGcallMxmn.v aintrin_realizes_xm OCpy; owner
   R2) *)
Hypothesis AMCPY : aintrin_realizes_xm SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
(* __wrap_strlen's text, the read-only (arodata) form with the keep, at its entry, at this Section's fx
   (YGcallMxmn.v astrlen_realizes_xrom; owner R2): the walk carries arodata_okP (ps_commonR) *)
Hypothesis ASTRLEN : astrlen_realizes_xrom SEGS B ARx pa_relro_lo pa_relro_hi (SIGMA AS___wrap_strlen).
(* the snprintf instance's parameters (the window Kp, the format band [lo, hi), the canary cells gcan / can, the image
   range [img_lo, img_hi) the buffer avoids, the constant ranges cr) and what the walk needs of them (ONE condition,
   discharged by the row's instance owner at PI_prog_B): the window fits the walk's runtime
   budget; the two formats lie in the format band (at the instance lo = cf_img_lo, hi = cf_got_stack_chk_guard, the
   GOT cell of the stack guard, YGcallSnpCk.v FF_esc: .rodata lies below the GOT; the band's top is NOT the image top
   pa_hi, so `pa_hi <= hi` would be false there and is not stated); the canary cells are image cells, readable at
   every state; the constant ranges are image bytes viewed at every state where the read-only view arodata_okP holds
   (the walk carries it, ps_common; at the owner's cr, the read-only segments, PSstrRo.rom_view_B_cf gives it; an
   unconditional view is not derivable from ARcf, review 22:2xZ); every live fake frame lies outside the
   image range *)
Definition ps_snp_inst (Kp lo hi gcan can img_lo img_hi : Z) (cr : list (Z * Z)) : Prop :=
  ESTACK <= Kp <= STK_RT_PRINTF /\
  lo <= ps_str 93 /\ ps_str 93 + 4 <= hi /\ lo <= ps_str 89 /\ ps_str 89 + 7 <= hi /\
  (forall j, 0 <= j < 8 -> in_img SEGS (gcan + j) /\ in_img SEGS (can + j)) /\
  (forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md ->
     (exists cval, val_mem SEGS (mrestrict (w_H W) mem) gcan 8 can /\ val_mem SEGS (mrestrict (w_H W) mem) can 8 cval) /\
     (arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> FMsnprintfShared.consts_view SEGS W mem cr)) /\
  Forall (fun r => 0 < snd r /\ forall a, fst r <= a < fst r + snd r -> in_img SEGS a) cr /\
  (forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
     img_hi <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= img_lo).
Variables (Kp lo hi gcan can img_lo img_hi : Z) (cr : list (Z * Z)).
Hypothesis HSNPI : ps_snp_inst Kp lo hi gcan can img_lo img_hi cr.
(* __wrap_snprintf's escape text AS THE ROW GIVES IT (YGcallSnpCk.v snp_esc_realizes_xrom: entry at this Section's fx
   with frm = 0, post at SOME fx' with frm = 0 and every f register but f10 kept), at its entry; its bridge from the
   row's text asnprintf_realizes_xrom (FF_esc lo hi) is YGcallSnpCk.snp_esc_of_xrom *)
Hypothesis SNP : YGcallSnpCk.snp_esc_realizes_xrom SEGS B ARx Kp pa_relro_lo pa_relro_hi lo hi gcan can img_lo img_hi
  cr (SIGMA AS___wrap_snprintf).

(* ---- the escape's own states ---- *)
(* the realigned slots R + 24 .. R + 64 (the five literal addresses), as atoms 32 .. 36 of the seat's env; s1 = R *)
Definition pe_rreg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 64 24 24
    [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0));
     YP09.mkChunk 48 (CVal 8 (SOff 35 0)); YP09.mkChunk 56 (CVal 8 (SOff 36 0))].
Definition pe_extra : list word :=
  [Z_to_bv 64 (ps_str 91); Z_to_bv 64 (ps_str 89); Z_to_bv 64 (ps_str 87); Z_to_bv 64 (ps_str 85); Z_to_bv 64 (ps_str 93)].
Definition pe_E (regs : bvmap 5 word) : env := Eimg (Ereg regs pe_extra).
Definition pe_ss456 : sstate := mkSS (AF_put_string + 456) sr_atoms [pe_rreg] None (mkFacts [] [] []).
Definition pe_ss0 (k : Z) : sstate := mkSS (AF_put_string + k) sr_atoms [] None (mkFacts [] [] []).
(* u's shadow granule's 8 bytes (s6 = SHF), written by the re-poison `sb -8, 4(s6)` *)
Definition pe_shreg : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 8 [].
Definition pe_ss616 : sstate := mkSS (AF_put_string + 616) sr_atoms [pe_shreg] None (mkFacts [] [] []).

(* the seat at a stretch that reads no memory: registers only *)
Lemma pe_seat0 : forall k (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (pe_ss0 k)
    (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (BASE + (AF_put_string + k))) mem (seg_rom SEGS))).
Proof.
intros k W regs mem. rewrite restrict_mkst_fx. unfold pe_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- first [ exact (conj I (conj I I)) | split; [exact I | split; [exact I | exact I]] ].
Qed.

(* the seat at B' + 0x1c8 (the escape join): registers as atoms, the five literal words at R + 24 .. R + 56 *)
Lemma pe_seat456 : forall X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_pre X ch -> ps_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  st_ok_pi SEGS VAL (pe_E regsc) pe_ss456
    (restrict (w_H Wc) (mkst (fx := fx) regsc (Z_to_bv 64 (BASE + (AF_put_string + 456))) memc (seg_rom SEGS))).
Proof.
intros X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc Hpre Hesc.
destruct Hesc as (_ & _ & _ & _ & LR & _ & _ & _ & _ & _ & _ & RB).
destruct LR as (_ & _ & _ & _ & R9 & _). destruct RB as (_ & _ & W24 & W32 & W40 & W48 & W56).
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
pose proof asan_consts as (C1 & _).
assert (HRr : 0 <= x_R X /\ x_R X + 64 < 2 ^ 64) by (unfold x_R, x_sp in *; (clear - C1 HR H47 Hshi Hslo Hceil Hstk0; lia)).
assert (B9 : base_val (pe_E regsc) (Some 9%nat) = x_R X).
{ cbn [base_val]. unfold pe_E. rewrite Eimg_low by (unfold A_TEXT; (clear; lia)).
  rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. (clear - HRr; lia). }
assert (E32 : ew (pe_E regsc) 32 = Z_to_bv 64 (ps_str 91))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew (pe_E regsc) 33 = Z_to_bv 64 (ps_str 89))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew (pe_E regsc) 34 = Z_to_bv 64 (ps_str 87))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew (pe_E regsc) 35 = Z_to_bv 64 (ps_str 85))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 3)).
assert (E36 : ew (pe_E regsc) 36 = Z_to_bv 64 (ps_str 93))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 4)).
pose proof (rdword_range_ps _ _ _ _ W24) as V24. pose proof (rdword_range_ps _ _ _ _ W32) as V32.
pose proof (rdword_range_ps _ _ _ _ W40) as V40. pose proof (rdword_range_ps _ _ _ _ W48) as V48.
pose proof (rdword_range_ps _ _ _ _ W56) as V56.
rewrite restrict_mkst_fx. unfold pe_ss456. apply pa_entry_st_ok_full.
- unfold pe_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, pe_rreg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
  split; [(clear - HRr; lia)|]. split; [(clear - HRr; lia)|]. split; [intros a Ha; (clear - Ha; lia)|].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 24 8 (SOff 32 0) (ps_str 91));
       [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); (clear - V24; lia) | zside
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W24)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 32 8 (SOff 33 0) (ps_str 89));
       [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); (clear - V32; lia) | zside
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W32)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 40 8 (SOff 34 0) (ps_str 87));
       [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); (clear - V40; lia) | zside
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W40)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 48 8 (SOff 35 0) (ps_str 85));
       [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); (clear - V48; lia) | zside
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W48)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 56 8 (SOff 36 0) (ps_str 93));
       [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); (clear - V56; lia) | zside
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W56)] |].
  apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- first [ exact (conj I (conj I I)) | split; [exact I | split; [exact I | exact I]] ].
Qed.

(* the seat after the put of the escape (B' + 0x268): registers as atoms, u's shadow granule SHF .. SHF + 8 (s6) *)
Lemma pe_seat616 : forall X pos (W : world SEGS) regs mem,
  getr regs 22 = w64 (x_SHF X pos) -> 0 <= x_SHF X pos -> x_SHF X pos + 8 < 2 ^ 64 ->
  (forall o, 0 <= o < 8 -> apresent (w_H W) mem (x_SHF X pos + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) pe_ss616
    (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (BASE + (AF_put_string + 616))) mem (seg_rom SEGS))).
Proof.
intros X pos W regs mem R22 Hlo Hhi Hpr.
assert (B22 : base_val (Eimg (Ereg regs [])) (Some 22%nat) = x_SHF X pos).
{ cbn [base_val]. rewrite Eimg_low by (unfold A_TEXT; (clear; lia)).
  rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl), R22. unfold w64. apply unsigned_lit_small. (clear - Hhi Hlo; lia). }
rewrite restrict_mkst_fx. unfold pe_ss616. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, pe_shreg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B22.
  split; [(clear - Hlo; lia)|]. split; [(clear - Hhi; lia)|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpr. (clear - Ho; lia).
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- first [ exact (conj I (conj I I)) | split; [exact I | split; [exact I | exact I]] ].
Qed.

(* ---- registers read back from a listing state ---- *)
Lemma pe_agree : forall regs extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; (clear - Hn; lia) | reflexivity]. Qed.
Lemma pe_reg_sv : forall (H : word -> bool) E ss ms (r : bv 5) e,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros H E ss ms r e HS He. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), He. reflexivity. Qed.
Lemma pe_reg_sv_pi : forall (H : word -> bool) E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros H E ss ms r e HS He. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), He. reflexivity. Qed.
Lemma pe_atom_reg : forall E regs0 extra (q : bv 5), env_agree 32 (Ereg regs0 extra) E ->
  sv_denot E (SOff (Z.to_nat (bv_unsigned q)) 0) = getr regs0 q.
Proof.
intros E regs0 extra q HA. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
destruct HA as [HA _]. rewrite HA by (pose proof (u5_range q) as Hq5; clear - Hq5; lia). apply ew_Ereg_reg.
Qed.
Lemma pe_atom_val : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity. Qed.
Lemma pe_reg_of : forall (H : word -> bool) E ss ms regs0 extra (r q : bv 5),
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned q)) 0 -> getr (ms_regs ms) r = getr regs0 q.
Proof.
intros H E ss ms regs0 extra r q HS HA Hr. rewrite (pe_reg_sv H E ss ms r _ HS Hr). exact (pe_atom_reg E regs0 extra q HA).
Qed.
Lemma pe_reg_of_pi : forall (H : word -> bool) E ss ms regs0 extra (r q : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned q)) 0 -> getr (ms_regs ms) r = getr regs0 q.
Proof.
intros H E ss ms regs0 extra r q HS HA Hr. rewrite (pe_reg_sv_pi H E ss ms r _ HS Hr). exact (pe_atom_reg E regs0 extra q HA).
Qed.
Lemma pe_ra : forall (H : word -> bool) E ss ms k, st_ok SEGS E ss (restrict H ms) -> img_env VAL A_LIM E ->
  sr_get (ss_regs ss) 1%bv = SOff A_TEXT k -> getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + k).
Proof. intros H E ss ms k HS HE Hr. rewrite (pe_reg_sv H E ss ms 1%bv _ HS Hr). exact (codeptr_val E k HE). Qed.
(* the callee-saved registers 2, 3, 4, 8, 9, 18 .. 27 *)
Definition pe_csl : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma pe_csl_in : forall r, acallee_saved r -> In (Z_to_bv 5 r) pe_csl.
Proof.
intros r Hr. unfold acallee_saved in Hr. unfold pe_csl.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (clear - Hr; lia).
repeat (destruct Hc as [-> | Hc]; [cbn [In]; repeat first [left; apply bv_eq; reflexivity | right] |]).
subst r. cbn [In]. repeat first [left; apply bv_eq; reflexivity | right].
Qed.
Lemma pe_pres : forall (H : word -> bool) E ss ms regs0 extra,
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) pe_csl = true ->
  aregs_preserved regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 extra HS HA Hl r Hr.
exact (regs_kept_of_st_ok SEGS E ss (restrict H ms) regs0 extra pe_csl HS HA Hl _ (pe_csl_in r Hr)).
Qed.
Lemma pe_pres_at : forall regs regs', aregs_preserved regs regs' ->
  forall (r : Z) (b : bv 5), acallee_saved r -> bv_unsigned b = r -> getr regs' b = getr regs b.
Proof. intros regs regs' HP r b Hr Hb. pose proof (HP r Hr) as H. rewrite <- Hb, !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* a callee-saved register a stretch leaves alone, read back through an earlier call's preservation *)
Lemma pe_kept_pi : forall (H : word -> bool) ss ms regs0 regsc (r : Z) (q : bv 5),
  st_ok_pi SEGS VAL (Eimg (Ereg regs0 [])) ss (restrict H ms) ->
  sr_get (ss_regs ss) q = SOff (Z.to_nat (bv_unsigned q)) 0 ->
  aregs_preserved regsc regs0 -> acallee_saved r -> bv_unsigned q = r ->
  getr (ms_regs ms) q = getr regsc q.
Proof.
intros H ss ms regs0 regsc r q HS Hq HP Hc Hr.
rewrite (pe_reg_of_pi H _ ss ms regs0 [] q q HS (pe_agree regs0 []) Hq).
exact (pe_pres_at regsc regs0 HP r q Hc Hr).
Qed.
(* a stretch whose regions have no write window keeps every byte *)
Lemma pe_keep_nowin : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hn a Ha. apply (kept_of_frame E rs H m m' (fun x => x = a) Hf); [|reflexivity].
intros x ->. split; [exact Ha | apply Hn].
Qed.
(* a stretch whose write windows lie in [wl, wh) keeps every byte outside it *)
Lemma pe_keep_win : forall E rs (H : word -> bool) (m m' : word -> option byte) wl wh,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> wl <= a < wh) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (wl <= a < wh) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' wl wh Hf Hw a Ha Hn. apply (kept_of_frame E rs H m m' (fun x => x = a) Hf); [|reflexivity].
intros x ->. split; [exact Ha|]. intros Hx. exact (Hn (Hw _ Hx)).
Qed.

(* ---- the string byte, its escape, and the literals ---- *)
Lemma pe_c_range : forall X ch i, ps_pre X ch -> (i < length (x_bs X))%nat -> 0 <= nth i (x_bs X) 0 < 256.
Proof.
intros X ch i Hpre Hi.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcstr0 & _).
destruct Hcstr0 as ((Hg & _) & _). destruct (Hg i ltac:(rewrite length_app; cbn [length]; (clear - Hi; lia))) as (_ & Hr).
rewrite app_nth1 in Hr by (clear - Hi; lia). exact Hr.
Qed.
Lemma pe_esc_facts : forall c, 0 <= c < 256 ->
  (length (WriterSpec.esc c) = 2 \/ length (WriterSpec.esc c) = 6)%nat /\ Forall (fun x => 0 < x < 256) (WriterSpec.esc c).
Proof.
intros c Hc. unfold WriterSpec.esc.
destruct (c =? 34) eqn:E1; [split; [left; reflexivity | repeat (apply Forall_cons; [(clear; lia)|]); apply Forall_nil]|].
destruct (c =? 92) eqn:E2; [split; [left; reflexivity | repeat (apply Forall_cons; [(clear; lia)|]); apply Forall_nil]|].
destruct (c =? 10) eqn:E3; [split; [left; reflexivity | repeat (apply Forall_cons; [(clear; lia)|]); apply Forall_nil]|].
destruct (c =? 9) eqn:E4; [split; [left; reflexivity | repeat (apply Forall_cons; [(clear; lia)|]); apply Forall_nil]|].
destruct (c =? 13) eqn:E5; [split; [left; reflexivity | repeat (apply Forall_cons; [(clear; lia)|]); apply Forall_nil]|].
split; [right; reflexivity|].
repeat (apply Forall_cons;
  [first [(clear; lia) | unfold WriterSpec.hexd; match goal with |- context [?x <? 10] => destruct (x <? 10) end; (clear - Hc; lia)] |]).
apply Forall_nil.
Qed.
(* the escape buffer's bytes: the escape of byte i and its NUL at u = F + 32 *)
Definition pe_u (X : psx) (pos : Z) (i : nat) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall j, (j < length (WriterSpec.esc (nth i (x_bs X) 0%Z) ++ [0%Z]))%nat ->
    aview SEGS (w_H Wc) memc (x_F X pos + 32 + Z.of_nat j) = Some (nth j (WriterSpec.esc (nth i (x_bs X) 0) ++ [0]) 0).
(* the escape's state between the escape join and the next join (fx-free): the join invariant, the plan, the
   registers the stretch and ps_next read (all callee-saved: ps_lregs, s4 = s + i + 1, s8 = s + i, s10 = s + i), u's
   shadow granule unpoisoned (0), the R block *)
Definition pe_s (X : psx) (pos : Z) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc /\
  (i < length (x_bs X))%nat /\
  [34] :: WriterSpec.spieces_run [] (x_bs X) =
    P ++ WriterSpec.esc (nth i (x_bs X) 0) :: WriterSpec.spieces_run [] (skipn (S i) (x_bs X)) /\
  ps_lregs X pos regsc /\
  getr regsc 20 = w64 (x_s X + Z.of_nat i + 1) /\ getr regsc 24 = w64 (x_s X + Z.of_nat i) /\
  getr regsc 26 = w64 (x_s X + Z.of_nat i) /\
  aview SEGS (w_H Wc) memc (x_SHF X pos + 4) = Some 0 /\
  ps_rblock X pos Wc memc.
(* KS's predicate: the state after the escape's write (fx-free): pe_s and the escape's bytes at u *)
Definition pe_wrt (X : psx) (pos : Z) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc /\ pe_u X pos i Wc memc.
Lemma pe_s_of_esc : forall X pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc.
Proof.
intros X pos i P lyc Sc Hpc Wc regsc memc mdc kc (Hcom & Hi & _ & Hplan & LR & R20 & R24 & _ & R26 & _ & SH4 & RB).
exact (conj Hcom (conj Hi (conj Hplan (conj LR (conj R20 (conj R24 (conj R26 (conj SH4 RB)))))))).
Qed.
(* the loop registers and the R block across a step that keeps them *)
Lemma pe_lregs_move : forall X pos regs regs', ps_lregs X pos regs -> aregs_preserved regs regs' ->
  ps_lregs X pos regs'.
Proof.
intros X pos regs regs' (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23) HP.
assert (RPx : forall (r : Z) (q : bv 5), acallee_saved r -> bv_unsigned q = r -> getr regs' q = getr regs q)
  by (intros r q Hr Hq; exact (pe_pres_at _ _ HP r q Hr Hq)).
unfold ps_lregs.
rewrite (RPx 2 2%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl), (RPx 3 3%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
  (RPx 4 4%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl), (RPx 8 8%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
  (RPx 9 9%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl), (RPx 19 19%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
  (RPx 21 21%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl), (RPx 22 22%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
  (RPx 23 23%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl).
exact (conj R2 (conj R3 (conj R4 (conj R8 (conj R9 (conj R19 (conj R21 (conj R22 R23)))))))).
Qed.
Lemma pe_rblock_move : forall X pos (W W' : world SEGS) mem mem', ps_rblock X pos W mem ->
  (forall a, x_R X <= a < x_R X + 64 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  ps_rblock X pos W' mem'.
Proof.
intros X pos W W' mem mem' (W8 & W16 & W24 & W32 & W40 & W48 & W56) K. unfold ps_rblock.
split; [rewrite <- W8; apply rdword_eq_of; intros j Hj; apply K; (clear - Hj; lia)|].
split; [rewrite <- W16; apply rdword_eq_of; intros j Hj; apply K; (clear - Hj; lia)|].
split; [rewrite <- W24; apply rdword_eq_of; intros j Hj; apply K; (clear - Hj; lia)|].
split; [rewrite <- W32; apply rdword_eq_of; intros j Hj; apply K; (clear - Hj; lia)|].
split; [rewrite <- W40; apply rdword_eq_of; intros j Hj; apply K; (clear - Hj; lia)|].
split; [rewrite <- W48; apply rdword_eq_of; intros j Hj; apply K; (clear - Hj; lia)|].
rewrite <- W56; apply rdword_eq_of; intros j Hj; apply K; (clear - Hj; lia).
Qed.

(* ---- where the walk's bytes lie ---- *)
Lemma pe_geo : forall X ch pos lyc Sc Hpc Wc memc mdc kc,
  ps_pre X ch ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc mdc kc ->
  In (0, pos) (frames Sc) /\ frame_addr lyc 0 pos = x_F X pos /\
  4096 <= x_F X pos /\ x_F X pos + 64 <= YM05.alloc_ceiling /\ x_F X pos mod 32 = 0 /\
  (x_F X pos + 64 <= kLowShadowBeg \/ kHighMemBeg <= x_F X pos) /\
  (forall a, x_F X pos <= a < x_F X pos + 64 -> apresent (w_H Wc) memc a) /\
  x_sp X mod 16 = 0 /\ x_d X mod 16 = 0 /\ 0 <= x_d X /\
  x_sp X - 208 <= x_R X <= x_sp X - 192 /\ x_R X mod 32 = 0 /\
  YM05.alloc_ceiling + STK_RT_PRINTF + 208 <= x_sp X /\ x_sp X + x_d X <= 2 ^ 47 /\
  ly_stk_lo lyc + STK_put_string <= x_sp X /\
  (forall a, x_sp X - STK_put_string <= a < x_sp X + x_d X -> apresent (w_H Wc) memc a).
Proof.
intros X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof STK_ps_facts as (_ & _ & _ & SK4 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & HR32).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLLE. pose proof (ajxR_frs HJ) as HFRS.
pose proof (ajxR_pres HJ) as Hpres.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _ & _ & _ & Eslo & _).
assert (HinF : In (0, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HARc HinF) as (HF32 & (HFa0 & HFa1) & HFpres & _).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HARc HinF) as (HF4096 & HFceil & _).
assert (EF : frame_addr lyc 0 pos = x_F X pos) by (unfold x_F, frame_addr; rewrite HlyF; reflexivity).
rewrite EF in HF32, HFa0, HFa1, HFpres, HF4096, HFceil. change (fs_frame_bytes 0) with 64 in HFa1, HFpres, HFceil.
unfold x_R, x_sp in *.
split; [exact HinF|]. split; [exact EF|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HF32|].
split; [destruct HFa1 as [Hx | (Hx & _)]; [left | right]; exact Hx|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [exact Hal16|]. split; [exact Hd16|]. split; [exact Hd0|]. split; [exact HR|]. split; [exact HR32|].
split; [unfold STK_RT_PRINTF, ESTACK in *; (clear - SK4 Hslo Hceil; lia)|]. split; [(clear - Hdtop Htop2 H47; lia)|].
split; [rewrite Eslo; (clear - Hslo; lia)|].
intros a Ha. apply Hpres. (clear - Ha; lia).
Qed.

(* image bytes lie apart from a live fake frame's bytes *)
Lemma pe_img_frame : forall ly S Hp (W : world SEGS) mem md cid pos p n q m,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> (forall a, p <= a < p + n -> in_img SEGS a) ->
  0 < n -> 0 < m ->
  frame_addr ly cid pos <= q -> q + m <= frame_addr ly cid pos + fs_frame_bytes cid ->
  p + n <= q \/ q + m <= p.
Proof.
intros ly S Hp W mem md cid pos p n q m HAR Hin Himg Hn Hm Hq1 Hq2.
destruct (Z_le_gt_dec (p + n) q) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec (q + m) p) as [H2 | H2]; [right; exact H2|]. exfalso.
destruct (Z_le_gt_dec p q) as [Hpq | Hpq].
- apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos q HAR Hin); [clear - Hq1 Hq2 Hm; lia|].
  apply Himg. clear - Hpq H1. (clear - Hpq H1; lia).
- apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos p HAR Hin); [clear - Hq1 Hq2 Hpq H2; lia|].
  apply Himg. clear - Hn. (clear - Hn; lia).
Qed.
(* u's granule (its shadow byte SHF + 4 is 0) is addressable *)
Lemma pe_radd : forall X pos (Wc : world SEGS) memc n, x_F X pos mod 32 = 0 -> 0 <= n <= 8 ->
  aview SEGS (w_H Wc) memc (x_SHF X pos + 4) = Some 0 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (x_F X pos + 32) n.
Proof.
intros X pos Wc memc n HF Hn H0 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (x_SHF X pos + 4); [exact H0|].
unfold x_SHF, PS_SB. (clear - Hx Hn HF; lia).
Qed.

(* the join invariant across a runtime call that writes at most its window below R (STK_RT_PRINTF bytes) and the
   escape buffer u .. u + 8 *)
Lemma pe_common_call : forall X ch pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc',
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - STK_RT_PRINTF <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc' mdc' kc'.
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hpre Hcom HJ' HPm' KK.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ho1 & Ho2 & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc' mdc' kc' Hpre HJ') as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof (ajxR_ar HJ') as HARc.
pose proof Hcom as (_ & Hsav & HF56 & _).
unfold STK_RT_PRINTF, ESTACK in *.
set (F := x_F X pos) in *. set (R := x_R X) in *. set (sp := x_sp X) in *.
apply (ps_common_runR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hcom).
- exact Ho1.
- unfold sp in *. clear - Ho2 Hd0 H47. (clear - H47 Ho2; lia).
- exact HJ'.
- exact HPm'.
- unfold ps_saved_ok in Hsav |- *. fold sp in Hsav |- *. rewrite Forall_forall in Hsav |- *.
  intros pz Hpin. rewrite <- (Hsav pz Hpin). apply rdword_eq_of. intros j Hj.
  assert (Hrg : -104 <= fst pz <= -8).
  { unfold ps_saved_list in Hpin. cbn [In] in Hpin. repeat (destruct Hpin as [<- | Hpin]; [cbn [fst]; (clear; lia)|]). destruct Hpin. }
  apply KK; clear - Hrg Hj HR HSPc HFceil HC H47 Hd0; lia.
- rewrite <- HF56. apply rdword_eq_of. intros j Hj. fold F. apply KK; clear - Hj HF4096 HFceil HC HSPc HR; lia.
- intros a Ha. destruct Ha as [Ha | [Hi | (b & m & HB & Hb)]].
  + apply KK; clear - Ha HR HSPc HFceil HC; lia.
  + pose proof (segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
    apply KK; [clear - Hl; lia | clear - Hl HR HSPc HC; lia |].
    intros Hx. apply (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos a HARc HinF); [|exact Hi].
    rewrite EF. change (fs_frame_bytes 0) with 64. fold F. clear - Hx. (clear - Hx; lia).
  + destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARc HB) as (_ & Hb4096 & Hbceil & _).
    pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HARc HB HinF) as Hzd.
    unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite EF in Hzd. change (fs_frame_bytes 0) with 64 in Hzd. fold F in Hzd.
    unfold ASAN_CEIL in *.
    apply KK; [clear - Hb Hb4096 Hbceil HC; lia | clear - Hb Hbceil HC HR HSPc; lia | clear - Hb Hzd; lia].
Qed.

(* the escape's state across a runtime call (registers callee-saved, bytes outside the call's window and u kept) *)
Lemma pe_s_move : forall X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs' memc' mdc' kc',
  ps_pre X ch -> pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> aregs_preserved regsc regs' ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - STK_RT_PRINTF <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  pe_s X pos i P lyc Sc Hpc Wc regs' memc' mdc' kc'.
Proof.
intros X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs' memc' mdc' kc' Hpre Hs HP HJ' HPm' KK.
destruct Hs as (Hcom & Hi & Hplan & LR & R20 & R24 & R26 & SH4 & RB).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc' mdc' kc' Hpre HJ') as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (KR : forall a, x_R X <= a < x_R X + 64 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply KK; unfold STK_RT_PRINTF, ESTACK in *; clear - Ha HR HSPc HFceil HC H47 Hd0; lia. }
assert (KS : aview SEGS (w_H Wc) memc' (x_SHF X pos + 4) = aview SEGS (w_H Wc) memc (x_SHF X pos + 4)).
{ apply KK; unfold x_SHF, PS_SB, SHADOW_OFF, STK_RT_PRINTF, ESTACK, kLowShadowBeg, kHighMemBeg in *;
    clear - HR HSPc HFceil HC H47 HFapp HF4096; lia. }
split; [exact (pe_common_call X ch pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hpre Hcom HJ' HPm' KK)|].
split; [exact Hi|]. split; [exact Hplan|].
split; [exact (pe_lregs_move X pos regsc regs' LR HP)|].
split; [rewrite (pe_pres_at _ _ HP 20 20%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl); exact R20|].
split; [rewrite (pe_pres_at _ _ HP 24 24%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl); exact R24|].
split; [rewrite (pe_pres_at _ _ HP 26 26%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl); exact R26|].
split; [rewrite KS; exact SH4|].
exact (pe_rblock_move X pos Wc Wc memc memc' RB KR).
Qed.
Lemma pe_u_move : forall X pos i (Wc : world SEGS) memc memc', pe_u X pos i Wc memc ->
  (forall a, x_F X pos + 32 <= a < x_F X pos + 40 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  0 <= nth i (x_bs X) 0 < 256 -> pe_u X pos i Wc memc'.
Proof.
intros X pos i Wc memc memc' Hu K Hc j Hj. destruct (pe_esc_facts _ Hc) as (Hl & _).
rewrite length_app in Hj. cbn [length] in Hj. rewrite K by (clear - Hl Hj; lia). apply Hu. rewrite length_app. cbn [length]. (clear - Hj; lia).
Qed.

(* the escape's next-join continuation at this Section's fx (KN): the re-poison join with the escape put *)
Definition pe_KN (fx0 : YK11.FPState) (X : psx) (pos : Z) (i : nat) (P : list (list Z)) : Prop :=
  forall lyn Sn Hpn Wn regsn memn mdn kn,
    ps_next X pos i (S i) (P ++ [WriterSpec.esc (nth i (x_bs X) 0)]) lyn Sn Hpn Wn regsn memn mdn kn ->
    SRr SEGS Wn (mkCfg (mkst (fx := fx) regsn (Z_to_bv 64 (BASE + (AF_put_string + 636))) memn (seg_rom SEGS)) mdn)
      (ps_Qfin fx0 X).
(* the escape's post-snprintf continuation KS, at EVERY float state fz with the two float facts from the entry fx0;
   its predicate pe_wrt is fx-free *)
Definition pe_KS (fx0 : YK11.FPState) (X : psx) (pos : Z) (i : nat) (P : list (list Z)) : Prop :=
  forall fz : YK11.FPState, frm_zero (@fp_csr fz) -> fregs_kept_x fx0 fz ->
  forall lyc Sc Hpc Wc regsc memc mdc kc, pe_wrt X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr SEGS Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 592))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
(* THE CONTINUATIONS OVER A WORLD RELATION R: a COPY of each beside it, its step relation SRrG SEGS R (pe_put / pe_tail /
   ps_esc_run unfold and change them, so each R form is a copy, not a retyping); X_R_wle (by reflexivity) checks that
   each IS its R form at wle. The escape runs after the opening-quote put (put reallocs when it grows, a crossing call),
   so every statement here names them at wle' SEGS RZ_cf *)
Definition pe_KNR (R : world SEGS -> world SEGS -> Prop) (fx0 : YK11.FPState) (X : psx) (pos : Z) (i : nat)
  (P : list (list Z)) : Prop :=
  forall lyn Sn Hpn Wn regsn memn mdn kn,
    ps_next X pos i (S i) (P ++ [WriterSpec.esc (nth i (x_bs X) 0)]) lyn Sn Hpn Wn regsn memn mdn kn ->
    SRrG SEGS R Wn (mkCfg (mkst (fx := fx) regsn (Z_to_bv 64 (BASE + (AF_put_string + 636))) memn (seg_rom SEGS)) mdn)
      (ps_Qfin fx0 X).
Lemma pe_KN_R_wle : forall fx0 X pos i P, pe_KN fx0 X pos i P = pe_KNR (@wle SEGS) fx0 X pos i P.
Proof. reflexivity. Qed.
Definition pe_KSR (R : world SEGS -> world SEGS -> Prop) (fx0 : YK11.FPState) (X : psx) (pos : Z) (i : nat)
  (P : list (list Z)) : Prop :=
  forall fz : YK11.FPState, frm_zero (@fp_csr fz) -> fregs_kept_x fx0 fz ->
  forall lyc Sc Hpc Wc regsc memc mdc kc, pe_wrt X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRrG SEGS R Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 592))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Lemma pe_KS_R_wle : forall fx0 X pos i P, pe_KS fx0 X pos i P = pe_KSR (@wle SEGS) fx0 X pos i P.
Proof. reflexivity. Qed.

(* ---- the post-put stretch's side tactics (+ 0x268 .. + 0x27c): its one region is u's shadow granule ---- *)
(* the write window lies in the fake frame's shadow (awr_byte's frame arm) *)
Ltac pe_awr616 B22 EF2 pos :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); cbn [In ss_mem pe_ss616] in Hin; destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi pe_shreg] in Ha; rewrite B22 in Ha;
  unfold awr_byte, in_frames; right; right; right; exists 0, pos; split; [left; reflexivity|]; right;
  unfold in_zr; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes 0) with 64;
  unfold shadow_addr, x_SHF, PS_SB in Ha |- *; clear - Ha; lia.
(* the write window is [SHF, SHF + 8) *)
Ltac pe_win616 B22 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); cbn [In ss_mem pe_ss616] in Hin; destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi pe_shreg] in Ha; rewrite B22 in Ha; clear - Ha; lia.
(* the write window is shadow memory (ps_common_frame's third arm) *)
Ltac pe_wr616 B22 HSHb :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); cbn [In ss_mem pe_ss616] in Hin; destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi pe_shreg] in Ha; rewrite B22 in Ha; right; right; clear - Ha HSHb; lia.
(* the UBSan pointer-overflow trap (+ 0x26c `beq s10, a0`, a0 = -1, to + 0x38c) is not taken: s10 = s + i lies below
   the allocation ceiling, far from 2 ^ 64 - 1 *)
Ltac pe_trap E26 Hsi :=
  lazymatch goal with Hc : branch_taken BC_EQ _ _ = true |- _ =>
    rewrite branch_eq_U in Hc; rewrite ?(U_atom _ 26 _ E26 ltac:(clear - Hsi; lia)), ?U_SLit in Hc;
    repeat (lazymatch type of Hc with context [zcanon ?z] =>
      let v := eval vm_compute in (zcanon z) in change (zcanon z) with v in Hc end);
    apply Z.eqb_eq in Hc; clear - Hc Hsi; lia
  end.

(* ---- the put of the escape (B' + 0x264), the overflow check (+ 0x26c, NOT TAKEN), the re-poison (+ 0x274) and
   `mv s2, s4` (+ 0x278), to the next join (+ 0x27c) ---- *)
Lemma pe_put : forall fx0 X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> pe_u X pos i Wc memc ->
  getr regsc 10 = w64 (x_o X) -> getr regsc 11 = w64 (x_F X pos + 32) ->
  getr regsc 12 = w64 (Z.of_nat (length (WriterSpec.esc (nth i (x_bs X) 0)))) ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 616)) ->
  pe_KNR (wle' SEGS RZ_cf) fx0 X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc Hs Hu H10 H11 H12 H1 K.
destruct fx0 as [fr0 fc0].
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcstr0 & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hcstr0 as (_ & _ & Hsceil & _).
pose proof Hs as (Hcom & Hi & Hplan & (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23) & R20 & R24 & R26 & SH4 & RB).
pose proof Hcom as (HJ & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HARc.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
destruct (pe_esc_facts _ Hc) as (Hlen & Hnz).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AF_ps_ret_k 616 ltac:((clear; lia)) ltac:(reflexivity)) as (H616 & H616b).
pose proof (pa_B_ok (L := B_prog_listing) (PAImg := PA)) as (HB0 & HB1 & _).
(* the bounds the post-put stretch needs: SHF's place in the shadow, below R; s + i far below 2 ^ 64 *)
assert (HSHb : SHADOW_OFF <= x_SHF X pos /\ x_SHF X pos + 8 <= kHighMemBeg).
{ unfold x_SHF, PS_SB. rewrite C3. unfold SHADOW_OFF. clear - HF4096 HFceil HC. (clear - HC HFceil HF4096; lia). }
assert (HSHR : x_SHF X pos + 8 <= x_R X).
{ rewrite C3 in HSHb. unfold SHADOW_OFF, STK_RT_PRINTF, ESTACK in *. clear - HSHb HSPc HR HC. (clear - HSHb HC HSPc HR; lia). }
assert (HRr : 0 <= x_R X /\ x_R X + 64 < 2 ^ 64) by (clear - HR H47 Hd0 HSPc HC; unfold STK_RT_PRINTF, ESTACK in *; (clear - HC H47 HSPc HR Hd0; lia)).
assert (Hsi : 0 <= x_s X + Z.of_nat i < 2 ^ 47).
{ pose proof Hcstr0 as (_ & Hs4096 & _). clear - Hs4096 Hsceil Hi HC. (clear - Hs4096 HC Hi Hsceil; lia). }
unfold pe_u in Hu.
set (c := nth i (x_bs X) 0) in *. set (b := WriterSpec.esc c) in *.
assert (Hlb : (2 <= length b <= 6)%nat) by (destruct Hlen as [Hl6 | Hl6]; clear - Hl6; lia).
apply (ps_put_step X ch pos P b (WriterSpec.spieces_run [] (skipn (S i) (x_bs X)) ++ [[34]]) lyc Sc Hpc Wc regsc memc mdc kc
  (Z_to_bv 64 (BASE + (AF_put_string + 616))) (x_F X pos + 32)).
- exact HFRMx.
- exact Hpre.
- exact HS0.
- exact Hcom.
- unfold WriterSpec.spieces.
  change ([34] :: WriterSpec.spieces_run [] (x_bs X) ++ [[34]]) with (([34] :: WriterSpec.spieces_run [] (x_bs X)) ++ [[34]]).
  rewrite Hplan, <- app_assoc. reflexivity.
- unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. (clear - HRr; lia).
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- exact H1.
- apply ret_ok_codeptr_v; [exact (proj1 H616) | exact (proj2 H616)].
- rewrite unsigned_lit_small by (clear - HB1 H616b H616; lia). exact H616b.
- rewrite unsigned_lit_small by (clear - HB1 H616b H616; lia). apply ps_ret_lt_ceil. cbn [In]. tauto.
- unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. unfold STK_RT_PRINTF, ESTACK in *. (clear - H47 HSPc Hd0 HFceil HF4096; lia).
- exact H10.
- exact H11.
- exact H12.
- (* the escape's bytes at u: read, in the fake frame, addressable *)
  split; [|split; [(clear - HF4096; lia)|split; [(clear - Hlen HFceil; lia)|split; [|split]]]].
  + apply (YGcallSnpCk.snp_garr8_of_aview SEGS (w_H Wc) memc (x_F X pos + 32) b). intros j Hj.
    pose proof (Hu j ltac:(rewrite length_app; cbn [length]; fold b; (clear - Hj; lia))) as Hx. fold b in Hx.
    rewrite app_nth1 in Hx by (clear - Hj; lia). exact Hx.
  + unfold amem_range. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. (clear - HC Hlen HFapp HFceil; lia).
  + apply (pe_radd X pos Wc memc); [exact HF32 | (clear - Hlen; lia) | exact SH4].
  + intros _. apply (hull_sub _ (x_F X pos) 64); [|(clear - pos; lia)|(clear - Hlen; lia)].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HARc HinF) as Hh. rewrite EF in Hh. exact Hh.
- (* the home: the fake frame, apart from the buffer block *)
  intros Lamc bufc capc Hk Hd Hin Hblks. split.
  + right. exists 0, pos. split; [exact HinF|]. rewrite EF. change (fs_frame_bytes 0) with 64. (clear - Hlen; lia).
  + destruct (Z.eq_dec capc 0) as [Hz | Hnz0]; [left; exact Hz | right].
    pose proof (Hblks _ _ (Hin Hnz0)) as HinB.
    pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HARc HinB HinF) as Hzd.
    unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite EF in Hzd. change (fs_frame_bytes 0) with 64 in Hzd.
    pose proof (@cf_head_nonneg cp) as Hch.
    destruct (Z_le_gt_dec (x_F X pos + 32 + Z.of_nat (length b)) bufc) as [Hl | Hl]; [left; exact Hl|].
    destruct (Z_le_gt_dec (bufc + capc) (x_F X pos + 32)) as [Hr | Hr]; [right; exact Hr|]. exfalso.
    revert Hzd. unfold req_size. destruct (Z.eqb_spec (capc + cf_head) 0) as [Hq | Hq]; intros Hzd;
      (clear - Hzd Hq Hr Hl Hch Hlen; lia).
- (* after put: + 0x268 .. + 0x27c *)
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HCOM2 HP2 KW KPR KF.
  idtac "PUT-POST". unfold SRr'.
  pose proof HCOM2 as (HJ2 & _ & _ & _ & HPM2 & _).
  pose proof (pe_geo X ch pos ly2 S2 Hp2 W2 mem2 md2 (kc + k1) Hpre HJ2) as (HinF2 & EF2 & _).
  pose proof (ajxR_ar HJ2) as HAR2.
  destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR2 HinF2) as (_ & _ & _ & HFsh2).
  assert (HSH2 : forall o, 0 <= o < 8 -> apresent (w_H W2) mem2 (x_SHF X pos + o)).
  { intros o Ho. rewrite EF2 in HFsh2.
    replace (x_SHF X pos + o) with (shadow_addr (x_F X pos) + o) by (unfold shadow_addr, x_SHF, PS_SB; (clear - o; lia)).
    exact (proj1 (HFsh2 o ltac:(change (fs_frame_bytes 0) with 64; (clear - Ho; lia)))). }
  assert (G22 : getr regs2 22 = w64 (x_SHF X pos))
    by (rewrite (pe_pres_at _ _ HP2 22 22%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl); exact R22).
  assert (G26 : getr regs2 26 = w64 (x_s X + Z.of_nat i))
    by (rewrite (pe_pres_at _ _ HP2 26 26%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl); exact R26).
  assert (HSHx : 0 <= x_SHF X pos /\ x_SHF X pos + 8 < 2 ^ 64) by (rewrite C3 in HSHb; unfold SHADOW_OFF in HSHb; (clear - HSHb; lia)).
  pose proof (pe_seat616 X pos W2 regs2 mem2 G22 (proj1 HSHx) (proj2 HSHx) HSH2) as HS.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  assert (B22 : base_val (Eimg (Ereg regs2 [])) (Some 22%nat) = x_SHF X pos).
  { cbn [base_val]. rewrite Eimg_low by (unfold A_TEXT; (clear; lia)).
    rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl), G22. unfold w64. apply unsigned_lit_small. (clear - HSHx; lia). }
  assert (E26 : ew (Eimg (Ereg regs2 [])) 26 = Z_to_bv 64 (x_s X + Z.of_nat i)).
  { rewrite Eimg_low by (unfold A_TEXT; (clear; lia)). rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl), G26. reflexivity. }
  (* run 1: `li a0, -1` to the overflow check's branch (+ 0x26c) *)
  pnt_run_to_inv NTRUNTOI HS HJ2 HPM2 (AF_put_string + 636).
  { pe_awr616 B22 EF2 pos. }
  idtac "PUT-POST-RUN1".
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  lazymatch goal with HF' : frame_of _ _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms1)) |- _ =>
    pose proof (pe_keep_win _ _ _ _ _ (x_SHF X pos) (x_SHF X pos + 8) HF' ltac:(pe_win616 B22)) as KM1;
    pose proof (ps_common_frameR (wle' SEGS RZ_cf) X ch pos (P ++ [b]) ly2 S2 Hp2 W2 mem2 md2 (kc + k1) _ _ _ _ _ Hpre
      HCOM2 HJ2 HPM2 HF'
      ltac:(pe_wr616 B22 HSHb)) as HCOM3;
    clear HF'
  end.
  pnt_branch BR HS.
  + (* the trap (+ 0x38c): NOT TAKEN, s + i < alloc_ceiling (cstr_ok's bound) *)
    exfalso. pe_trap E26 Hsi.
  + (* run 2: the re-poison `sb -8, 4(s6)`, `mv s2, s4`, to the next join (+ 0x27c) *)
    pnt_run_to_inv NTRUNTOI HS HJ2 HPM2 (AF_put_string + 636).
    { pe_awr616 B22 EF2 pos. }
    idtac "PUT-POST-RUN2".
    repeat rewrite wvb_collapse in HJ2.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    lazymatch goal with HF' : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms1)) (mrestrict (w_H W2) (ms_mem ms2)) |- _ =>
      pose proof (pe_keep_win _ _ _ _ _ (x_SHF X pos) (x_SHF X pos + 8) HF' ltac:(pe_win616 B22)) as KM2;
      pose proof (ps_common_frameR (wle' SEGS RZ_cf) X ch pos (P ++ [b]) ly2 S2 Hp2 W2 _ _ _ _ _ _ _ _ Hpre HCOM3 HJ2
        HPM2 HF'
        ltac:(pe_wr616 B22 HSHb)) as HCOM4;
      clear HF'
    end.
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?k)) _ _) _) _ =>
      replace k with (AF_put_string + 636) by (unfold AF_put_string; rewrite (proj2 B_entry_put_string); vm_compute; reflexivity)
    end.
    unfold pe_KNR in K. eapply K.
    assert (KMW : forall a, x_R X <= a < x_R X + 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a).
    { intros a Ha. rewrite KM2, KM1 by (clear - Ha HSHR HRr; lia). apply KW. clear - Ha HR. (clear - Ha HR; lia). }
    unfold ps_next.
    split; [exact HCOM4|].
    split; [(clear - i; lia)|]. split; [exact Hi|].
    split; [rewrite Nat.sub_diag; cbn [firstn]; rewrite <- app_assoc; exact Hplan|].
    split.
    { unfold ps_lregs.
      rewrite (pe_kept_pi _ _ _ regs2 regsc 2 2%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 3 3%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 4 4%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 8 8%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 9 9%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 19 19%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 21 21%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 22 22%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl),
        (pe_kept_pi _ _ _ regs2 regsc 23 23%bv HS ltac:(vm_compute; reflexivity) HP2 ltac:(unfold acallee_saved; (clear; lia)) eq_refl).
      exact (conj R2 (conj R3 (conj R4 (conj R8 (conj R9 (conj R19 (conj R21 (conj R22 R23)))))))). }
    split.
    { (* s2 := s4 = s + i + 1 = s + (i + 1) *)
      rewrite (pe_reg_of_pi _ _ _ _ _ _ 18%bv 20%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)).
      rewrite (pe_pres_at _ _ HP2 20 20%bv ltac:(unfold acallee_saved; (clear; lia)) eq_refl), R20.
      unfold w64. f_equal. (clear - i; lia). }
    split; [rewrite (pe_kept_pi _ _ _ regs2 regsc 20 20%bv HS ltac:(vm_compute; reflexivity) HP2
              ltac:(unfold acallee_saved; (clear; lia)) eq_refl); exact R20|].
    split; [rewrite (pe_kept_pi _ _ _ regs2 regsc 24 24%bv HS ltac:(vm_compute; reflexivity) HP2
              ltac:(unfold acallee_saved; (clear; lia)) eq_refl); exact R24|].
    exact (pe_rblock_move X pos Wc W2 memc (ms_mem ms2) RB KMW).
Qed.

(* ---- __wrap_strlen (u) (B' + 0x254), then the put's arguments (+ 0x258 .. + 0x260) ---- *)
Lemma pe_strlen : forall fx0 X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> pe_u X pos i Wc memc ->
  getr regsc 10 = w64 (x_F X pos + 32) -> getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 600)) ->
  pe_KNR (wle' SEGS RZ_cf) fx0 X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (SIGMA AS___wrap_strlen)) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc Hs Hu H10 H1 K.
destruct fx0 as [fr0 fc0].
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hs as (Hcom & Hi & Hplan & (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23) & R20 & R24 & R26 & SH4 & RB).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _ & _ & Hro & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HARc.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
destruct (pe_esc_facts _ Hc) as (Hlen & Hnz).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof (AF_ps_ret_k 600 ltac:((clear; lia)) ltac:(reflexivity)) as (H600 & H600b).
pose proof STK_ps_facts as (_ & _ & _ & SK4 & SK5 & _).
unfold pe_u in Hu.
set (c := nth i (x_bs X) 0) in *. set (b := WriterSpec.esc c) in *.
assert (Hlb : (2 <= length b <= 6)%nat) by (destruct Hlen as [Hl6 | Hl6]; clear - Hl6; lia).
unfold STK_RT_PRINTF, STK_RT_STR, ESTACK in *.
(* the strlen rule keeps the world (W2 = Wc): its SRr lifts to SRr' *)
eapply (SRr'_bind SEGS RZ_cf).
{ apply SRr_SRr'.
  apply (aj_strlen_at_xromR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx pa_relro_lo pa_relro_hi LAWS segs_low
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) _ ASTRLEN
    Wc regsc memc (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X)
    (x_md X) [(0, pos)] lyc Sc Hpc mdc kc (x_F X pos + 32) (Z.of_nat (length b)) (x_R X - (x_sp X + x_d X))
    (Z_to_bv 64 (BASE + (AF_put_string + 600)))).
  - exact HJ.
  - exact H10.
  - (clear - HF4096; lia).
  - (clear - b; lia).
  - (clear - Hlen; lia).
  - (clear - Hlen H47 HSPc Hd0 HFceil; lia).
  - unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by (clear - H47 HSPc HR Hd0 HFceil HF4096; lia). (clear - X; lia).
  - rewrite Zminus_mod, Zplus_mod, Hal16, Hd16. assert (H16 : x_R X mod 16 = 0) by (clear - HR32; lia). rewrite H16. reflexivity.
  - (clear - HR Hd0; lia).
  - unfold ESTACK. (clear - SK4 HR; lia).
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact H1.
  - apply ret_ok_codeptr_v; [exact (proj1 H600) | exact (proj2 H600)].
  - (* the escape's first NUL is at u + |b| *)
    split; [(clear - b; lia)|]. split.
    + intros j Hj. exists (nth (Z.to_nat j) b 0). split.
      * pose proof (Hu (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; fold b; (clear - Hj; lia))) as Hx. fold b in Hx.
        rewrite Z2Nat.id in Hx by (clear - Hj; lia). rewrite app_nth1 in Hx by (clear - Hj; lia). exact Hx.
      * rewrite Forall_forall in Hnz. fold b in Hnz.
        assert (Hin : In (nth (Z.to_nat j) b 0) b) by (apply nth_In; (clear - Hj; lia)).
        pose proof (Hnz _ Hin) as Hx. (clear - Hx; lia).
    + intros _. pose proof (Hu (length b) ltac:(rewrite length_app; cbn [length]; fold b; (clear - b; lia))) as Hx. fold b in Hx.
      rewrite app_nth2, Nat.sub_diag in Hx by (clear - b; lia). exact Hx.
  - intros a Ha. split.
    + replace a with (x_F X pos + 32 + Z.of_nat (Z.to_nat (a - (x_F X pos + 32)))) by (clear - Ha; lia).
      rewrite Hu by (rewrite length_app; cbn [length]; fold b; (clear - Ha; lia)). discriminate.
    + unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by (clear - H47 HSPc HR Hd0 HFceil HF4096; lia). unfold ESTACK. (clear - Ha Hlen HSPc HR HFceil; lia).
  - intros a Ha. unfold ESTACK. clear - Ha Hlb HFceil HSPc HR. (clear - Ha Hlb HSPc HR HFceil; lia).
  - first [unfold amem_range8 | unfold YGcallMx.amem_range8 | unfold YGcfStr.amem_range8].
    unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. (clear - Hlen H47 HSPc Hd0 HFapp HFceil; lia).
  - apply (pe_radd X pos Wc memc); [exact HF32 | (clear - Hlen; lia) | exact SH4].
  - apply (hull_sub _ (x_F X pos) 64); [|(clear - pos; lia)|(clear - Hlen; lia)].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HARc HinF) as Hh. rewrite EF in Hh. exact Hh.
  - intros a Ha. apply (aview_some_of_apresent SEGS). apply HFpres. (clear - Ha Hlen; lia).
  - exact Hro. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Hfr & Hpres2 & Hmn).
idtac "STRLEN-POST".
pose proof (PCALL _ _ Hmn HPM) as HPM2.
assert (KK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - 4 * 4096 <= a < x_R X) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hw. apply Hfr; [exact Ha|]. unfold ESTACK. (clear - Hw; lia). }
pose proof (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs2 mem2 md2 kc Hpre Hs HP2 HJ2 HPM2
  (fun a Ha Hw _ => KK0 a Ha Hw)) as Hs2.
pose proof (pe_u_move X pos i Wc memc mem2 Hu ltac:(intros a Ha; apply KK0; (clear - Ha H47 HSPc Hd0 HFceil HF4096 HR; lia)) Hc) as Hu2.
clear KK0.
pose proof Hs2 as (_ & _ & _ & (_ & _ & _ & _ & _ & R19' & R21' & _) & _).
(* + 0x258: mv a2, a0; mv a0, s3; mv a1, s5; jal put *)
pose proof (pe_seat0 600 Wc regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
unfold SRr'.
pnt_run_to_inv NTRUNTOI HS HJ2 HPM2 (AF_put_string + 616).
{ intros a (r & Hin & Ha). cbn [In ss_mem pe_ss0] in Hin. destruct Hin. }
idtac "STRLEN-POST-RUN".
lazymatch goal with HF' : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?msx)) |- _ =>
  pose proof (pe_keep_nowin _ _ _ _ _ HF' ltac:(intros a (r & Hin & _); destruct Hin)) as KM
end.
cbv beta iota in HS. pmkst HS.
pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as HP3.
pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 19%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as A0.
pose proof (pe_reg_of _ _ _ _ _ _ 11%bv 21%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as A1.
pose proof (pe_reg_of _ _ _ _ _ _ 12%bv 10%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as A2.
pose proof (pe_ra _ _ _ _ (AF_put_string + 616) HS HEI ltac:(vm_compute; reflexivity)) as RA.
apply (pe_put (mkFP fr0 fc0) X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ kc).
- apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regs2 mem2 md2 kc (ms_regs ms) (ms_mem ms) _ kc Hpre Hs2 HP3 HJ2 HPM2).
  intros a Ha _ _. exact (KM a Ha).
- apply (pe_u_move X pos i Wc mem2 (ms_mem ms) Hu2); [intros a Ha; apply KM; (clear - Ha H47 HSPc Hd0 HFceil HF4096; lia) | exact Hc].
- rewrite A0. exact R19'.
- rewrite A1. exact R21'.
- rewrite A2. exact Ha0.
- exact RA.
- exact K.
Qed.

(* ---- (1) the post-write stretch: from the memcpy return (+ 0x238 = AF + 568, `j + 0x250`) or the snprintf return
   (+ 0x250 = AF + 592), `mv a0, s5`, __wrap_strlen (u), put (o, u, len), the overflow check (NOT TAKEN), the
   re-poison, `mv s2, s4`, to the next join (+ 0x27c), at this Section's fx ---- *)
Lemma pe_tail : forall fx0 X ch, ps_pre X ch -> ps_s0 X ->
  forall k pos i P lyc Sc Hpc Wc regsc memc mdc kc, (k = 568 \/ k = 592) ->
  pe_wrt X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  (forall lyn Sn Hpn Wn regsn memn mdn kn,
     ps_next X pos i (S i) (P ++ [WriterSpec.esc (nth i (x_bs X) 0)]) lyn Sn Hpn Wn regsn memn mdn kn ->
     SRr' SEGS RZ_cf Wn (mkCfg (mkst (fx := fx) regsn (Z_to_bv 64 (BASE + (AF_put_string + 636))) memn (seg_rom SEGS))
       mdn) (ps_Qfin fx0 X)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (BASE + (AF_put_string + k))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 k pos i P lyc Sc Hpc Wc regsc memc mdc kc Hk (Hs & Hu) K.
unfold SRr'.
destruct fx0 as [fr0 fc0].
change (pe_KNR (wle' SEGS RZ_cf) (mkFP fr0 fc0) X pos i P) in K.
pose proof Hs as (Hcom & Hi & _ & (_ & _ & _ & _ & _ & _ & R21 & _) & _).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _).
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as (_ & _ & HF4096 & HFceil & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
destruct Hk as [-> | ->];
[ pose proof (pe_seat0 568 Wc regsc memc) as HS | pose proof (pe_seat0 592 Wc regsc memc) as HS ];
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env;
(pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 600);
 [ intros a (r & Hin & Ha); cbn [In ss_mem pe_ss0] in Hin; destruct Hin
 | idtac "TAIL-RUN";
   lazymatch goal with HF' : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
     pose proof (pe_keep_nowin _ _ _ _ _ HF' ltac:(intros a (r & Hin & _); destruct Hin)) as KM
   end;
   cbv beta iota in HS; pmkst HS;
   pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regsc []) ltac:(vm_compute; reflexivity)) as HP3;
   pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 21%bv HS (pe_agree regsc []) ltac:(vm_compute; reflexivity)) as A0;
   pose proof (pe_ra _ _ _ _ (AF_put_string + 600) HS HEI ltac:(vm_compute; reflexivity)) as RA;
   exact (pe_strlen (mkFP fr0 fc0) X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ kc
     (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc (ms_regs ms) (ms_mem ms) _ kc Hpre Hs HP3 HJ HPM
        (fun a Ha _ _ => KM a Ha))
     (pe_u_move X pos i Wc memc (ms_mem ms) Hu (fun a Ha => KM a ltac:(clear - Ha HF4096 HFceil HC; lia)) Hc)
     (eq_trans A0 R21) RA K) ]).
Qed.

(* ---- the escape by copy: __asan_memcpy (u, lit, 3) (B' + 0x234), lit = .str.21 / .str.20 / .str.22 ---- *)
Lemma pe_cpy : forall fx0 X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc lit,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  (nth i (x_bs X) 0 = 9 /\ lit = ps_str 85 \/ nth i (x_bs X) 0 = 10 /\ lit = ps_str 87 \/
   nth i (x_bs X) 0 = 13 /\ lit = ps_str 91) ->
  getr regsc 10 = w64 (x_F X pos + 32) -> getr regsc 11 = w64 lit -> getr regsc 12 = w64 3 ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 568)) ->
  pe_KNR (wle' SEGS RZ_cf) fx0 X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (SIGMA AS___asan_memcpy)) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc lit Hs Hcase H10 H11 H12 H1 K.
destruct fx0 as [fr0 fc0].
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hs as (Hcom & Hi & Hplan & (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23) & R20 & R24 & R26 & SH4 & RB).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _ & _ & Hro & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HARc.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof (AF_ps_ret_k 568 ltac:((clear; lia)) ltac:(reflexivity)) as (H568 & H568b).
pose proof STK_ps_facts as (SK1 & _).
(* the literal: ESC, the letter, NUL; read-only image bytes *)
assert (HL : exists x, WriterSpec.esc (nth i (x_bs X) 0) = [92; x] /\ src_rd Wc memc lit [92; x; 0] /\ kept_at B [] lit 3).
{ destruct Hcase as [(Hcx & ->) | [(Hcx & ->) | (Hcx & ->)]]; rewrite Hcx.
  - exists 116. split; [reflexivity|]. exact (HLIT85 _ _ _ _ _ _ HARc Hro).
  - exists 110. split; [reflexivity|]. exact (HLIT87 _ _ _ _ _ _ HARc Hro).
  - exists 114. split; [reflexivity|]. exact (HLIT91 _ _ _ _ _ _ HARc Hro). }
destruct HL as (x & Hesc & Hsrc & Hkept).
pose proof Hsrc as (Hbytes & Hl4096 & Hlceil & Hlam & Hlrad & Hlhull). cbn [length] in Hlceil, Hlam, Hlrad, Hlhull.
change (Z.of_nat 3) with 3 in Hlceil, Hlam, Hlrad, Hlhull.
assert (Hlimg : forall a, lit <= a < lit + 3 -> in_img SEGS a).
{ intros a Ha. destruct Hkept as [(b0 & m & Hin & _) | [(_ & _ & _ & Hall) | (_ & _ & Hall)]];
    [destruct Hin | exact (in_roP_img _ (proj1 (Hall a Ha))) | exact (in_roP_img _ (proj1 (Hall a Ha)))]. }
assert (Hdl : lit + 3 <= x_F X pos + 32 \/ x_F X pos + 32 + 3 <= lit).
{ apply (pe_img_frame _ _ _ _ _ _ 0 pos lit 3 (x_F X pos + 32) 3 HARc HinF Hlimg ltac:((clear; lia)) ltac:((clear; lia)));
    rewrite EF; [(clear - pos; lia) | change (fs_frame_bytes 0) with 64; (clear - pos; lia)]. }
unfold STK_RT_PRINTF, ESTACK in *.
(* the memcpy rule keeps the world (W2 = Wc): its SRr lifts to SRr' *)
eapply (SRr'_bind SEGS RZ_cf).
{ apply SRr_SRr'.
  apply (aj_intrin_at_xmR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS segs_low (wle' SEGS RZ_cf) OCpy _ AMCPY
    Wc regsc memc (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X)
    (x_md X) [(0, pos)] lyc Sc Hpc mdc kc (x_F X pos + 32) lit 3 (x_R X - (x_sp X + x_d X))
    (Z_to_bv 64 (BASE + (AF_put_string + 568)))).
  - exact HJ.
  - exact H10.
  - exact H11.
  - exact H12.
  - (clear; lia).
  - (clear - HF4096; lia).
  - (clear - H47 HSPc Hd0 HFceil; lia).
  - unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by (clear - H47 HSPc HR Hd0 HFceil HF4096; lia). (clear - X; lia).
  - rewrite Zminus_mod, Zplus_mod, Hal16, Hd16. assert (H16 : x_R X mod 16 = 0) by (clear - HR32; lia). rewrite H16. reflexivity.
  - (clear - HR Hd0; lia).
  - unfold ESTACK. (clear - SK1 HR; lia).
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact H1.
  - apply ret_ok_codeptr_v; [exact (proj1 H568) | exact (proj2 H568)].
  - intros a Ha. split.
    + unfold awr_byte, in_frames. right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. (clear - Ha; lia).
    + unfold ESTACK. (clear - Ha HSPc HR HFceil; lia).
  - unfold amem_range. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. (clear - H47 HSPc Hd0 HFapp HFceil; lia).
  - apply (pe_radd X pos Wc memc); [exact HF32 | (clear; lia) | exact SH4].
  - intros _. apply (hull_sub _ (x_F X pos) 64); [|(clear - pos; lia)|(clear - pos; lia)].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HARc HinF) as Hh. rewrite EF in Hh. exact Hh.
  - split; [(clear - Hl4096; lia)|]. split; [(clear - Hlceil H47 HSPc Hd0; lia)|]. split.
    + intros a Ha. split.
      * replace a with (lit + Z.of_nat (Z.to_nat (a - lit))) by (clear - Ha; lia).
        rewrite (YGcallSnpCk.snp_aview_of_garr8 SEGS (w_H Wc) memc lit [92; x; 0] (Z.to_nat (a - lit)) Hbytes
          ltac:(cbn [length]; (clear - Ha; lia))). discriminate.
      * unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by (clear - H47 HSPc HR Hd0 HFceil HF4096; lia). unfold ESTACK. (clear - Ha Hlceil HSPc HR; lia).
    + split; [(clear - Hdl; lia)|]. split; [exact Hlam|]. split; [exact Hlrad|]. intros _. apply Hlhull. (clear; lia). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2 & Hmn).
idtac "MEMCPY-POST".
pose proof (PCALL _ _ Hmn HPM) as HPM2.
assert (KK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - 4 * 4096 <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hw Hu. apply Hfr; [exact Ha | (clear - Hu; lia) | unfold ESTACK; (clear - Hw; lia)]. }
pose proof (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs2 mem2 md2 kc Hpre Hs HP2 HJ2 HPM2 KK0) as Hs2.
assert (Hu2 : pe_u X pos i Wc mem2).
{ unfold pe_u. rewrite Hesc. intros j Hj. cbn [length app] in Hj.
  pose proof (Heff (Z.of_nat j) ltac:((clear - Hj; lia))) as He. cbn iota in He. rewrite He.
  exact (YGcallSnpCk.snp_aview_of_garr8 SEGS (w_H Wc) memc lit [92; x; 0] j Hbytes ltac:(cbn [length]; (clear - Hj; lia))). }
exact (pe_tail (mkFP fr0 fc0) X ch Hpre HS0 568 pos i P lyc Sc Hpc Wc regs2 mem2 md2 kc (or_introl eq_refl) (conj Hs2 Hu2) K).
Qed.

(* the rendered escape is put_string's escape *)
Lemma pe_render_c : forall c, c = 34 \/ c = 92 ->
  YGcallSnpCk.snp_esc_render YGcallSnpCk.snp_esc_fmt_c c = WriterSpec.esc c.
Proof. intros c [-> | ->]; reflexivity. Qed.
Lemma pe_render_x : forall c, c <> 34 -> c <> 92 -> c <> 10 -> c <> 9 -> c <> 13 ->
  YGcallSnpCk.snp_esc_render YGcallSnpCk.snp_esc_fmt_x c = WriterSpec.esc c.
Proof.
intros c H1 H2 H3 H4 H5. unfold YGcallSnpCk.snp_esc_render, WriterSpec.esc.
destruct (list_eq_dec Z.eq_dec YGcallSnpCk.snp_esc_fmt_x YGcallSnpCk.snp_esc_fmt_c) as [He | _]; [discriminate He|].
rewrite (proj2 (Z.eqb_neq c 34) H1), (proj2 (Z.eqb_neq c 92) H2), (proj2 (Z.eqb_neq c 10) H3),
  (proj2 (Z.eqb_neq c 9) H4), (proj2 (Z.eqb_neq c 13) H5). reflexivity.
Qed.

(* ---- the escape by format: __wrap_snprintf (u, 8, fmt, c) (B' + 0x24c) through the row's stand-in SNP, at this
   Section's fx (frm = 0 at entry); the post's float state fx' (frm = 0, every f register but f10 kept) goes to KS ---- *)
Lemma pe_snp : forall fx0 X ch, ps_pre X ch -> frm_zero (@fp_csr fx) -> fregs_kept_x fx0 fx ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc f fmt,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  ((nth i (x_bs X) 0 = 34 \/ nth i (x_bs X) 0 = 92) /\ f = ps_str 93 /\ fmt = YGcallSnpCk.snp_esc_fmt_c \/
   (nth i (x_bs X) 0 <> 34 /\ nth i (x_bs X) 0 <> 92 /\ nth i (x_bs X) 0 <> 10 /\ nth i (x_bs X) 0 <> 9 /\
    nth i (x_bs X) 0 <> 13) /\ f = ps_str 89 /\ fmt = YGcallSnpCk.snp_esc_fmt_x) ->
  getr regsc 10 = w64 (x_F X pos + 32) -> getr regsc 11 = w64 8 -> getr regsc 12 = w64 f ->
  getr regsc 13 = w64 (nth i (x_bs X) 0) -> getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 592)) ->
  pe_KSR (wle' SEGS RZ_cf) fx0 X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (SIGMA AS___wrap_snprintf)) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HFRM HFK pos i P lyc Sc Hpc Wc regsc memc mdc kc f fmt Hs Hcase H10 H11 H12 H13 H1 KS.
destruct fx0 as [fr0 fc0].
unfold pe_KSR in KS.
assert (Hfmt : f = ps_str 93 /\ fmt = YGcallSnpCk.snp_esc_fmt_c \/ f = ps_str 89 /\ fmt = YGcallSnpCk.snp_esc_fmt_x)
  by (destruct Hcase as [(_ & Hf & Hm) | (_ & Hf & Hm)]; [left | right]; split; assumption).
assert (Hrend : YGcallSnpCk.snp_esc_render fmt (nth i (x_bs X) 0) = WriterSpec.esc (nth i (x_bs X) 0)).
{ destruct Hcase as [(Hc & _ & ->) | ((H34 & H92 & H10' & H9 & H13') & _ & ->)].
  - exact (pe_render_c _ Hc).
  - exact (pe_render_x _ H34 H92 H10' H9 H13'). }
pose proof HSNPI as (HKp & H93a & H93b & H89a & H89b & Hcimg & Hinst & Hcr & Himgr).
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hs as (Hcom & Hi & Hplan & (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23) & R20 & R24 & R26 & SH4 & RB).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _ & _ & Hro & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs.
pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres.
pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof STK_ps_facts as (_ & _ & _ & SK4 & _).
pose proof (AF_ps_ret_k 592 ltac:((clear; lia)) ltac:(reflexivity)) as (H592 & H592b).
destruct (Hinst _ _ _ _ _ _ HAR) as (Hcan & Hcv0). pose proof (Hcv0 Hro) as Hcv.
set (u := x_F X pos + 32) in *. set (c := nth i (x_bs X) 0) in *.
assert (Hsp' : spZ regsc = x_R X) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold STK_RT_PRINTF, ESTACK in *; (clear - H47 HSPc HR Hd0 HFceil HF4096; lia)).
(* the format: its bytes with the NUL, read-only image bytes, in the format band *)
assert (HF : src_rd Wc memc f (fmt ++ [0]) /\ kept_at B [] f (Z.of_nat (length fmt) + 1)).
{ destruct Hfmt as [(-> & ->) | (-> & ->)].
  - exact (HLIT93 _ _ _ _ _ _ HAR Hro).
  - exact (HLIT89 _ _ _ _ _ _ HAR Hro). }
destruct HF as (Hfsrc & Hfkept).
assert (Hfl : (Z.of_nat (length fmt) = 3 \/ Z.of_nat (length fmt) = 6)) by (destruct Hfmt as [(_ & ->) | (_ & ->)]; cbn; (clear; lia)).
assert (Hfband : lo <= f /\ f + Z.of_nat (length fmt) + 1 <= hi).
{ destruct Hfmt as [(-> & ->) | (-> & ->)].
  - change (Z.of_nat (length YGcallSnpCk.snp_esc_fmt_c)) with 3. clear - H93a H93b. (clear - H93b H93a; lia).
  - change (Z.of_nat (length YGcallSnpCk.snp_esc_fmt_x)) with 6. clear - H89a H89b. (clear - H89b H89a; lia). }
assert (Hfimg : forall a, f <= a < f + (Z.of_nat (length fmt) + 1) -> in_img SEGS a).
{ intros a Ha. destruct Hfkept as [(b0 & m & Hin & _) | [(_ & _ & _ & Hall) | (_ & _ & Hall)]];
    [destruct Hin | exact (in_roP_img _ (proj1 (Hall a Ha))) | exact (in_roP_img _ (proj1 (Hall a Ha)))]. }
(* image ranges lie below the window and apart from the escape buffer *)
assert (IW : forall p n, 0 < n -> (forall a, p <= a < p + n -> in_img SEGS a) ->
  Forall (zdisjoint (p, n)) (FMsnprintfShared.snp_out Kp (spZ regsc) u 8)).
{ intros p n Hn Hall. apply YGcallSnpCk.snp_out_Forall. split.
  - unfold zdisjoint. cbn [fst snd]. left. pose proof (segs_low _ (Hall (p + n - 1) ltac:((clear - Hn; lia)))) as Hl.
    rewrite Hsp'. unfold kLowMemEnd, STK_RT_PRINTF, ESTACK in *. (clear - Hl HC HSPc HR HKp; lia).
  - unfold zdisjoint. cbn [fst snd].
    apply (pe_img_frame _ _ _ _ _ _ 0 pos p n u 8 HAR HinF Hall Hn ltac:((clear; lia))); rewrite EF; unfold u; [(clear - pos; lia) | change (fs_frame_bytes 0) with 64; (clear - pos; lia)]. }
assert (Hgimg : forall j, 0 <= j < 8 -> in_img SEGS (gcan + j)) by (intros j Hj; exact (proj1 (Hcimg j Hj))).
assert (Hcimg2 : forall j, 0 <= j < 8 -> in_img SEGS (can + j)) by (intros j Hj; exact (proj2 (Hcimg j Hj))).
pose proof (segs_low _ (Hgimg 0 ltac:((clear; lia)))) as Lg0. pose proof (segs_low _ (Hgimg 7 ltac:((clear; lia)))) as Lg7.
pose proof (segs_low _ (Hcimg2 0 ltac:((clear; lia)))) as Lc0. pose proof (segs_low _ (Hcimg2 7 ltac:((clear; lia)))) as Lc7.
rewrite Z.add_0_r in Lg0, Lc0.
(* the call's entry state *)
assert (HPRE2 : ecall_pre_x SEGS B ARx lyc Sc Hpc Wc regsc memc mdc).
{ split; [exact HAR|]. split; [rewrite H1; apply ret_ok_codeptr_v; [exact (proj1 H592) | exact (proj2 H592)]|].
  split; [rewrite Hsp'; (clear - HR32; lia)|]. split; [rewrite Hsp'; unfold STK_RT_PRINTF, ESTACK in *; (clear - SK4 Hlo HR; lia)|].
  split; [rewrite Hsp'; pose proof Hstatic as (_ & _ & _ & _ & Hshi & _); pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _); rewrite Eshi; unfold x_sp in *; (clear - Hshi HR Hd0; lia)|].
  split; [intros a Ha; apply Hpw; rewrite Hsp' in Ha; unfold ESTACK in *; (clear - Ha SK4 HR Hd0 HKp; lia)|].
  split; [rewrite R3; exact Hgp | rewrite R4; exact Htp]. }
(* the row keeps the world (W2 = Wc): its SRr lifts to SRr' *)
eapply (SRr'_bind SEGS RZ_cf).
{ apply SRr_SRr'.
  apply (SNP lyc Sc Hpc Wc regsc memc mdc u f fmt c HPRE2).
  - rewrite Hsp'. unfold STK_RT_PRINTF, ESTACK in *. (clear - SK4 Hlo HR HKp; lia).
  - intros a Ha. apply Hpw. rewrite Hsp' in Ha. unfold STK_RT_PRINTF, ESTACK in *. (clear - Ha SK4 HR Hd0 HKp; lia).
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - destruct Hfmt as [(_ & ->) | (_ & ->)]; [left | right]; reflexivity.
  - exact Hc.
  - intros k _. pose proof Hfsrc as (Hfby & Hf4096 & Hfc & Hfam & Hfrad & Hfhull).
    rewrite length_app in Hfc, Hfam, Hfrad, Hfhull. cbn [length] in Hfc, Hfam, Hfrad, Hfhull.
    rewrite Nat2Z.inj_add in Hfc, Hfam, Hfrad, Hfhull. cbn [Z.of_nat Pos.of_succ_nat] in Hfc, Hfam, Hfrad, Hfhull.
    split; [exact Hfby|]. split; [(clear - Hf4096; lia)|]. split; [(clear - Hfc HC; lia)|]. split; [exact Hfam|]. split; [exact Hfrad|]. apply Hfhull. (clear - fmt; lia).
  - exact Hcan.
  - unfold u. (clear - HF4096; lia).
  - unfold u. (clear - HC HFceil; lia).
  - unfold amem_range, u. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. (clear - HC HFapp HFceil; lia).
  - intros a Ha.
    assert (Haw : awr_byte (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (ablocks B (x_ly X) (x_S X))
      (ablocks B lyc Sc) lyc [(0, pos)] a).
    { unfold awr_byte, in_frames. right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. unfold u in Ha. (clear - Ha; lia). }
    destruct (awr_byte_present_xR SEGS B (@prh_pst prh_img_B) ARx LAWS (wle' SEGS RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Haw)
      as (Hpa & Hno).
    split; [apply (apresent_writable SEGS); exact Hpa|]. split; [exact Hno|].
    rewrite Hsp'. unfold u in Ha. unfold STK_RT_PRINTF, ESTACK in *. clear - Ha HKp HFceil HSPc HR. (clear - Ha HSPc HR HFceil HKp; lia).
  - apply (pe_radd X pos Wc memc); [exact HF32 | (clear; lia) | exact SH4].
  - apply (hull_sub _ (x_F X pos) 64); [|unfold u; (clear - pos; lia)|unfold u; (clear - pos; lia)].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HAR HinF) as Hh. rewrite EF in Hh. exact Hh.
  - exact Hro.
  - exact Hcv.
  - rewrite Forall_forall in Hcr |- *. intros [p n] Hin. destruct (Hcr _ Hin) as (Hn & Hall). cbn [fst snd] in *.
    pose proof (segs_low _ (Hall p ltac:((clear - Hn; lia)))) as L0. pose proof (segs_low _ (Hall (p + n - 1) ltac:((clear - Hn; lia)))) as L1.
    unfold kLowMemEnd in *. (clear - L1 L0; lia).
  - rewrite Forall_forall in Hcr |- *. intros [p n] Hin. destruct (Hcr _ Hin) as (Hn & Hall). exact (IW p n Hn Hall).
  - (clear - Lg0; lia).
  - unfold kLowMemEnd in *. (clear - Lg0; lia).
  - (clear - Lc0; lia).
  - unfold kLowMemEnd in *. (clear - Lc0; lia).
  - apply IW; [(clear; lia) | intros a Ha; replace a with (gcan + (a - gcan)) by (clear - a; lia); apply Hgimg; (clear - Ha; lia)].
  - apply IW; [(clear; lia) | intros a Ha; replace a with (can + (a - can)) by (clear - a; lia); apply Hcimg2; (clear - Ha; lia)].
  - apply IW; [(clear - fmt; lia) | exact Hfimg].
  - exact (proj1 Hfband).
  - exact (proj2 Hfband).
  - rewrite Hsp'. unfold x_sp in *. unfold STK_RT_PRINTF, ESTACK in *. (clear - H47 HR Hd0; lia).
  - unfold amem_range, u. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. (clear - HC HFapp HFceil; lia).
  - destruct (Himgr _ _ _ _ _ _ 0 pos HAR HinF) as [Hx | Hx]; rewrite EF in Hx; change (fs_frame_bytes 0) with 64 in Hx;
      unfold zdisjoint, u; cbn [fst snd]; (clear - Hx; lia).
  - exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hc2 & Hfk & Hfz & HAR2 & HP2 & Hsame & Hres & Hgar & Hfr &
  Hpres2 & Hmn).
(* the returned float state must not be taken by instance resolution: name its two fields at once *)
destruct fx1 as [fr1 fc1].
idtac "SNPRINTF-POST".
pose proof (PCALL _ _ Hmn HPM) as HPM2.
set (T := YGcallSnpCk.snp_esc_render fmt c) in *.
assert (HTl : (length T <= 6)%nat).
{ unfold T, YGcallSnpCk.snp_esc_render. destruct (list_eq_dec Z.eq_dec fmt YGcallSnpCk.snp_esc_fmt_c); cbn [length]; (clear; lia). }
assert (HJ2 : AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X)
  (x_W X) (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc mem2 md2 kc).
{ apply (ajournal_x_after_writeR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS segs_low (wle' SEGS RZ_cf)
    (STK_put_string + x_d X)
    (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc mdc kc
    mem2 md2 (fun a => (u <= a < u + Z.of_nat (length T) + 1) \/ (spZ regsc - Kp <= a < spZ regsc)) Sc Hpc [(0, pos)] HJ).
  - intros a Ha Hna. apply Hfr; [exact Ha | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left.
    + unfold awr_byte, in_frames. right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. unfold u in Ha. (clear - Ha HTl; lia).
    + unfold awr_byte. left. rewrite Hsp' in Ha. unfold STK_RT_PRINTF, ESTACK in *. (clear - Ha SK4 HR Hd0 HKp; lia).
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - (clear - Sc; lia).
  - exact Hfrs.
  - exact HQT.
  - reflexivity. }
assert (KK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - STK_RT_PRINTF <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hw Hu. apply Hfr; [exact Ha | unfold u in *; (clear - Hu HTl; lia) | rewrite Hsp'; unfold STK_RT_PRINTF, ESTACK in *; (clear - Hw HKp; lia)]. }
pose proof (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs2 mem2 md2 kc Hpre Hs HP2 HJ2 HPM2 KK0) as Hs2.
assert (Hu2 : pe_u X pos i Wc mem2).
{ unfold pe_u. fold c. rewrite <- Hrend. fold T. intros j Hj.
  exact (YGcallSnpCk.snp_aview_of_garr8 SEGS (w_H Wc) mem2 u (T ++ [0]) j Hgar Hj). }
(* the post's float facts: frm = 0, and the callee-saved f registers are fx0's (snprintf keeps all but f10, the
   Section's fx keeps fx0's) *)
assert (HFK1 : fregs_kept_x (mkFP fr0 fc0) (mkFP fr1 fc1)).
{ intros r Hr. rewrite (Hfk (Z_to_bv 5 r)); [exact (HFK r Hr)|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by (clear - Hr; lia). (clear - Hr; lia). }
rewrite Hc2. unfold YG0d.cfg_at, raZ. rewrite H1. unfold w64. rewrite Z_to_bv_bv_unsigned.
exact (KS (mkFP fr1 fc1) Hfz HFK1 lyc Sc Hpc Wc regs2 mem2 md2 kc (conj Hs2 Hu2)).
Qed.

(* ---- the two kinds of call state at the end of the escape's branches (B' + 0x234 / + 0x24c) ---- *)
Lemma pe_leaf_cpy : forall fx0 X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc (ss : sstate) ms mdx n lit,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  @st_ok SEGS fx (pe_E regsc) (setpc ss (SIGMA AS___asan_memcpy)) (restrict (w_H Wc) ms) -> ss_resv ss = None ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) pe_csl = true ->
  sr_get (ss_regs ss) 10%bv = SOff 21 0 -> sr_get (ss_regs ss) 11%bv = SOff n 0 -> sr_get (ss_regs ss) 12%bv = SLit 3 ->
  sr_get (ss_regs ss) 1%bv = SOff A_TEXT (AF_put_string + 568) ->
  ew (pe_E regsc) n = Z_to_bv 64 lit -> 0 <= lit < 2 ^ 64 ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc (ms_mem ms) mdx kc -> Pm (ms_mem ms) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a) ->
  (nth i (x_bs X) 0 = 9 /\ lit = ps_str 85 \/ nth i (x_bs X) 0 = 10 /\ lit = ps_str 87 \/
   nth i (x_bs X) 0 = 13 /\ lit = ps_str 91) ->
  pe_KNR (wle' SEGS RZ_cf) fx0 X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg ms mdx) (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc ss ms mdx n lit Hs HS Hrv Hcs H10 H11 H12 H1 En Hl
  HJ HPM KM Hcase K.
destruct fx0 as [fr0 fc0].
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS Hrv). cbn [ss_pc setpc].
pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regsc pe_extra) Hcs) as HP.
pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 21%bv HS (pe_agree regsc pe_extra) H10) as A0.
pose proof (pe_reg_sv _ _ _ _ 11%bv _ HS H11) as A1.
pose proof (pe_reg_sv _ _ _ _ 12%bv _ HS H12) as A2.
pose proof (pe_ra _ _ _ _ _ HS (Eimg_env _) H1) as RA.
pose proof Hs as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & R21 & _) & _).
apply (pe_cpy (mkFP fr0 fc0) X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdx kc lit).
- apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc (ms_regs ms) (ms_mem ms) mdx kc Hpre Hs HP HJ HPM).
  intros a Ha _ _. exact (KM a Ha).
- exact Hcase.
- rewrite A0. exact R21.
- rewrite A1. exact (pe_atom_val _ n lit En Hl).
- rewrite A2. reflexivity.
- exact RA.
- exact K.
Qed.
Lemma pe_leaf_snp : forall fx0 X ch, ps_pre X ch -> frm_zero (@fp_csr fx) -> fregs_kept_x fx0 fx ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc (ss : sstate) ms mdx n f fmt,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> getr regsc 27 = w64 (nth i (x_bs X) 0) ->
  @st_ok SEGS fx (pe_E regsc) (setpc ss (SIGMA AS___wrap_snprintf)) (restrict (w_H Wc) ms) -> ss_resv ss = None ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) pe_csl = true ->
  sr_get (ss_regs ss) 10%bv = SOff 21 0 -> sr_get (ss_regs ss) 11%bv = SLit 8 -> sr_get (ss_regs ss) 12%bv = SOff n 0 ->
  sr_get (ss_regs ss) 13%bv = SOff 27 0 -> sr_get (ss_regs ss) 1%bv = SOff A_TEXT (AF_put_string + 592) ->
  ew (pe_E regsc) n = Z_to_bv 64 f -> 0 <= f < 2 ^ 64 ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc (ms_mem ms) mdx kc -> Pm (ms_mem ms) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a) ->
  ((nth i (x_bs X) 0 = 34 \/ nth i (x_bs X) 0 = 92) /\ f = ps_str 93 /\ fmt = YGcallSnpCk.snp_esc_fmt_c \/
   (nth i (x_bs X) 0 <> 34 /\ nth i (x_bs X) 0 <> 92 /\ nth i (x_bs X) 0 <> 10 /\ nth i (x_bs X) 0 <> 9 /\
    nth i (x_bs X) 0 <> 13) /\ f = ps_str 89 /\ fmt = YGcallSnpCk.snp_esc_fmt_x) ->
  pe_KSR (wle' SEGS RZ_cf) fx0 X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg ms mdx) (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HFRM HFK pos i P lyc Sc Hpc Wc regsc memc mdc kc ss ms mdx n f fmt Hs R27 HS Hrv Hcs H10 H11 H12
  H13 H1 En Hl HJ HPM KM Hcase KS.
destruct fx0 as [fr0 fc0].
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS Hrv). cbn [ss_pc setpc].
pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regsc pe_extra) Hcs) as HP.
pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 21%bv HS (pe_agree regsc pe_extra) H10) as A0.
pose proof (pe_reg_sv _ _ _ _ 11%bv _ HS H11) as A1.
pose proof (pe_reg_sv _ _ _ _ 12%bv _ HS H12) as A2.
pose proof (pe_reg_of _ _ _ _ _ _ 13%bv 27%bv HS (pe_agree regsc pe_extra) H13) as A3.
pose proof (pe_ra _ _ _ _ _ HS (Eimg_env _) H1) as RA.
pose proof Hs as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & R21 & _) & _).
apply (pe_snp (mkFP fr0 fc0) X ch Hpre HFRM HFK pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdx kc f fmt).
- apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc (ms_regs ms) (ms_mem ms) mdx kc Hpre Hs HP HJ HPM).
  intros a Ha _ _. exact (KM a Ha).
- exact Hcase.
- rewrite A0. exact R21.
- rewrite A1. reflexivity.
- rewrite A2. exact (pe_atom_val _ n f En Hl).
- rewrite A3. exact R27.
- exact RA.
- exact KS.
Qed.

(* ---- the stretch's own code: the seat at B' + 0x1c8, the escape's dispatch on c, to the calls ---- *)
Lemma pe_br_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (YO0b.s64 (U E a) <? YO0b.s64 (U E b)).
Proof. intros E a b. rewrite YO0c.branch_ge. reflexivity. Qed.
Ltac pe_bool H := first
  [ apply Z.eqb_eq in H | apply Z.eqb_neq in H
  | apply negb_true_iff in H; first [apply Z.eqb_neq in H | apply Z.ltb_ge in H]
  | apply negb_false_iff in H; first [apply Z.eqb_eq in H | apply Z.ltb_lt in H] ].
(* the branch just decided, on the byte c = s9 (atom 25) against a literal, as a fact on c (Hcr : 0 <= c < 256) *)
Ltac pe_hc E25 Hcr :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite ?branch_eq_U, ?branch_ne_U, ?pe_br_ge in Hc;
    rewrite ?(U_atom _ 25 _ E25 ltac:(clear - Hcr; lia)) in Hc;
    rewrite ?U_lit in Hc by (clear - Hcr; lia);
    rewrite ?YO0b.s64_small in Hc by (clear - Hcr; lia);
    pe_bool Hc;
    let Hn := fresh "Hcz" in rename Hc into Hn
  end.
Ltac pe_nowin := let a' := fresh "a" in let r' := fresh "r" in let Hin' := fresh "Hin" in let Ha' := fresh "Ha" in
  intros a' (r' & Hin' & Ha'); vm_compute in Hin'; destruct Hin' as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha'; clear - Ha'; lia.
Ltac pe_km KMc :=
  lazymatch type of KMc with forall a, _ -> aview _ (w_H ?W) ?m1 a = _ =>
    lazymatch goal with HF' : frame_of _ _ (mrestrict (w_H W) m1) (mrestrict (w_H W) ?m2) |- _ =>
      let KN := fresh "KMn" in
      pose proof (fun a Ha => eq_trans (pe_keep_nowin _ _ _ _ _ HF' ltac:(pe_nowin) a Ha) (KMc a Ha)) as KN;
      clear HF' KMc; rename KN into KMc
    end
  end.
Ltac pe_run HS HJ HPM KMc :=
  pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 592);
  [ let a' := fresh "a" in let Hw := fresh "Hw" in intros a' Hw; exfalso; revert a' Hw; pe_nowin
  | repeat rewrite wvb_collapse in HJ; pe_km KMc ].

(* ---- (2) the escape segment: from the escape join (+ 0x1c8 = AF + 456) to the next join (+ 0x27c = AF + 636). The
   memcpy arms (c = 9, 10, 13) continue at this Section's fx to the next join (KN); the snprintf arms (c = 34, 92: "\\%c";
   any other c < 32: "\\u%04x") call snprintf at fx (frm = 0) and finish by KS at the returned float state. The escape
   crosses put (its own put, and the opening-quote put before it), so its continuations and its conclusion are
   SRr' ---- *)
Lemma ps_esc_run : forall fx0 X ch, ps_pre X ch -> ps_s0 X ->
  frm_zero (@fp_csr fx) -> fregs_kept_x fx0 fx ->
  forall pos i P,
  (forall lyn Sn Hpn Wn regsn memn mdn kn,
     ps_next X pos i (S i) (P ++ [WriterSpec.esc (nth i (x_bs X) 0)]) lyn Sn Hpn Wn regsn memn mdn kn ->
     SRr' SEGS RZ_cf Wn (mkCfg (mkst (fx := fx) regsn (Z_to_bv 64 (BASE + (AF_put_string + 636))) memn (seg_rom SEGS))
       mdn)
       (ps_Qfin fx0 X)) ->
  (forall fz : YK11.FPState, frm_zero (@fp_csr fz) -> fregs_kept_x fx0 fz ->
   forall lyc Sc Hpc Wc regsc memc mdc kc, pe_wrt X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fz regsc (Z_to_bv 64 (BASE + (AF_put_string + 592))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin fx0 X)) ->
  forall lyc Sc Hpc Wc regsc memc mdc kc, ps_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (BASE + (AF_put_string + 456))) memc (seg_rom SEGS))
    mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 HFRM HFK pos i P K KS lyc Sc Hpc Wc regsc memc mdc kc Hesc.
unfold SRr'.
destruct fx0 as [fr0 fc0].
change (pe_KNR (wle' SEGS RZ_cf) (mkFP fr0 fc0) X pos i P) in K.
change (pe_KSR (wle' SEGS RZ_cf) (mkFP fr0 fc0) X pos i P) in KS.
pose proof (pe_s_of_esc _ _ _ _ _ _ _ _ _ _ _ _ Hesc) as Hs0.
pose proof Hesc as (Hcom & Hi & _ & _ & _ & _ & _ & R25 & _ & R27 & _ & RB).
pose proof RB as (_ & _ & W24 & W32 & W40 & W48 & W56).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _).
pose proof (pe_c_range X ch i Hpre Hi) as Hcrange.
pose proof (pe_seat456 X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc Hpre Hesc) as HS.
assert (HEI : img_env VAL A_LIM (pe_E regsc)) by (unfold pe_E; apply Eimg_env).
assert (E25 : ew (pe_E regsc) 25 = Z_to_bv 64 (nth i (x_bs X) 0))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); rewrite (ew_Ereg_nat regsc _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew (pe_E regsc) 32 = Z_to_bv 64 (ps_str 91))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew (pe_E regsc) 33 = Z_to_bv 64 (ps_str 89))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew (pe_E regsc) 34 = Z_to_bv 64 (ps_str 87))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew (pe_E regsc) 35 = Z_to_bv 64 (ps_str 85))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 3)).
assert (E36 : ew (pe_E regsc) 36 = Z_to_bv 64 (ps_str 93))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; (clear; lia)); exact (ew_Ereg_extra regsc _ 4)).
pose proof (rdword_range_ps _ _ _ _ W24) as V91. pose proof (rdword_range_ps _ _ _ _ W32) as V89.
pose proof (rdword_range_ps _ _ _ _ W40) as V87. pose proof (rdword_range_ps _ _ _ _ W48) as V85.
pose proof (rdword_range_ps _ _ _ _ W56) as V93.
pose proof Hcrange as Hcr.
assert (KMc : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
clear Hesc.
idtac "ESC-SEATED".
pe_run HS HJ HPM KMc.
pnt_branch BR HS.
- (* + 0x1cc `bge 12, c` taken: c <= 12, to + 0x1f8 *)
  pe_hc E25 Hcr. pe_run HS HJ HPM KMc. pnt_branch BR HS.
  + (* c = 9: + 0x228, __asan_memcpy (u, .str.21 "\\t", 3) *)
    pe_hc E25 Hcr. pe_run HS HJ HPM KMc.
    apply (pe_leaf_cpy (mkFP fr0 fc0) X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 35%nat (ps_str 85) Hs0 HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      E35 V85 HJ HPM KMc ltac:(left; split; [(clear - Hcz0; lia) | reflexivity]) K).
  + pe_hc E25 Hcr. pe_run HS HJ HPM KMc. pnt_branch BR HS.
    * (* c <> 9, c <> 10, c <= 12: + 0x23c, __wrap_snprintf (u, 8, "\\u%04x", c) *)
      pe_hc E25 Hcr. pe_run HS HJ HPM KMc.
      apply (pe_leaf_snp (mkFP fr0 fc0) X ch Hpre HFRM HFK pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 33%nat (ps_str 89)
        YGcallSnpCk.snp_esc_fmt_x Hs0 R27 HS
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity)
        E33 V89 HJ HPM KMc ltac:(right; split; [repeat split; (clear - Hcz Hcz1 Hcz0; lia) | split; reflexivity]) KS).
    * (* c = 10: + 0x208, __asan_memcpy (u, .str.20 "\\n", 3) *)
      pe_hc E25 Hcr. pe_run HS HJ HPM KMc.
      apply (pe_leaf_cpy (mkFP fr0 fc0) X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 34%nat (ps_str 87) Hs0 HS
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        E34 V87 HJ HPM KMc ltac:(right; left; split; [(clear - Hcz1; lia) | reflexivity]) K).
- (* `bge 12, c` not taken: c > 12 *)
  pe_hc E25 Hcr. pe_run HS HJ HPM KMc. pnt_branch BR HS.
  + (* c = 13: + 0x218, __asan_memcpy (u, .str.22 "\\r", 3) *)
    pe_hc E25 Hcr. pe_run HS HJ HPM KMc.
    apply (pe_leaf_cpy (mkFP fr0 fc0) X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 32%nat (ps_str 91) Hs0 HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      E32 V91 HJ HPM KMc ltac:(right; right; split; [(clear - Hcz0; lia) | reflexivity]) K).
  + pe_hc E25 Hcr. pe_run HS HJ HPM KMc. pnt_branch BR HS.
    * (* c = 92: + 0x1e8, __wrap_snprintf (u, 8, "\\%c", c) *)
      pe_hc E25 Hcr. pe_run HS HJ HPM KMc.
      apply (pe_leaf_snp (mkFP fr0 fc0) X ch Hpre HFRM HFK pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 36%nat (ps_str 93)
        YGcallSnpCk.snp_esc_fmt_c Hs0 R27 HS
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity)
        E36 V93 HJ HPM KMc ltac:(left; split; [(clear - Hcz1; lia) | split; reflexivity]) KS).
    * pe_hc E25 Hcr. pe_run HS HJ HPM KMc. pnt_branch BR HS.
      -- (* c <> 34, c <> 92, c <> 13, c > 12: + 0x23c, __wrap_snprintf (u, 8, "\\u%04x", c) *)
         pe_hc E25 Hcr. pe_run HS HJ HPM KMc.
         apply (pe_leaf_snp (mkFP fr0 fc0) X ch Hpre HFRM HFK pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 33%nat
           (ps_str 89) YGcallSnpCk.snp_esc_fmt_x Hs0 R27 HS
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)
           E33 V89 HJ HPM KMc ltac:(right; split; [repeat split; (clear - Hcz2 Hcz1 Hcz Hcz0; lia) | split; reflexivity]) KS).
      -- (* c = 34: + 0x1e8, __wrap_snprintf (u, 8, "\\%c", c) *)
         pe_hc E25 Hcr. pe_run HS HJ HPM KMc.
         apply (pe_leaf_snp (mkFP fr0 fc0) X ch Hpre HFRM HFK pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 36%nat
           (ps_str 93) YGcallSnpCk.snp_esc_fmt_c Hs0 R27 HS
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)
           E36 V93 HJ HPM KMc ltac:(left; split; [(clear - Hcz2; lia) | split; reflexivity]) KS).
Qed.

End h.
End f.
End d.

Print Assumptions ps_esc_run.
Print Assumptions pe_tail.
