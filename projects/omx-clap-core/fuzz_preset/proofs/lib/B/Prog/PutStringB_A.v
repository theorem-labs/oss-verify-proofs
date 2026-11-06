(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30), this file: put_string's
   walk, SEGMENT A: the entry, frame_alloc_0, the fake frame's header and shadow, the opening-quote put (+ 0x110), the
   UBSan NULL check of s (+ 0x114 `beqz s2` to the trap at + 0x38c, NOT TAKEN: s's atom carries 4096 <= s), s[0]'s
   ASan check (+ 0x118 .. + 0x124, the slow path + 0x390 / its report + 0x39c not taken: s[0] is addressable) and the
   first byte's test: to the loop head (+ 0x180) or, on the empty string, to the tail join (+ 0x2c8). Over
   PutStringB_Base.v, toward the #102 tput_string_specX (PRH_FnWriter.v 2b497bc72172).
   PORTED from lib/A/Prog/PRW_put_string_a.v (blob
   b01824cd44d1): offsets 0 .. 276 are word for word A's; after put #1 B' holds s in s2 (A: s10) and the byte in s9
   (A: s2), and has the NULL trap. No address literal: entries, return sites and literals are by name (B_prog_slot,
   the listing's PAddHi addends).
   The re-hiding move (route (b)): the stretch before the opening-quote put calls no freeing function, so it stays
   plain SRr at wle and is lifted ONCE at the top (YGcfRhLift.ra_rh_of_SRr) into the walk's SRr' SEGS RZ_cf; put
   reallocs when it grows (a crossing call), so from put #1 on the joins are ps_commonR at wle' SEGS RZ_cf, the
   stretches and branches run at that relation, and the continuations KH / KT conclude SRr'. *)
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
(* the branch rule over a world relation (paj_branchR) and the one lift of a plain segment into SRr'
   (ra_rh_of_SRr), by their qualified names *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YSRrG YGcfRhLift.
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
Let NTRUNTOI := SRr_run_to_pi_AJx_inv B ARx LAWS Pm PLAW.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_B) (PI := PA).
(* the tokenless runner and the branch at the re-hiding relation: the stretches after put #1 run at it *)
Let NTRUNTOIR := SRr_run_to_pi_AJx_invR B ARx LAWS Pm PLAW (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BRR := YSRrG.paj_branchR (PI := PA) (wle' SEGS RZ_cf).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx).
Variable CTX0 : list (list Z).
(* put's text (the #102 tput_specX), at this Section's float state: the ONE callee-text use of put in this file *)
Hypothesis PUT : tput_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* FRM0-ENTRY (fpre's last conjunct) at this Section's float state: the rounding mode is 0 (segment A runs at
   the entry state; the assembly reads it off the text's fpre) *)
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
Local Notation ps_common := (ps_common B ARx Pm).
Local Notation ps_commonR := (ps_commonR B ARx Pm).
Local Notation ps_Qfin := (ps_Qfin B ARx Pm fx).
Local Notation kept_at_blk := (kept_at_blk B).
Local Notation blk_kept_at := (blk_kept_at B).
Local Notation kept_at_bounds := (kept_at_bounds B ARx LAWS HPAB).
Local Notation str_notin_fp := (str_notin_fp B ARx LAWS).
Local Notation cstr_from_entry := (cstr_from_entry B ARx HPSTRO).
Local Notation cstr_from_entryR := (cstr_from_entryR B ARx HPSTRO).
Local Notation str_shadow_at := (str_shadow_at B ARx LAWS ASO HIMGSH HPAB).
Local Notation kept_at_loc := (kept_at_loc B ARx LAWS HPAB).
Local Notation ledger_blocks_disj := (ledger_blocks_disj B ARx LAWS).
Local Notation blk_src_disj := (blk_src_disj B ARx LAWS).
Local Notation hblock_shadow := (hblock_shadow B ARx LAWS).
Local Notation ps_common_frame := (ps_common_frame B ARx LAWS segs_low HW PST_ok Pm CTX0).
Local Notation ps_common_frameR := (ps_common_frameR B ARx LAWS segs_low HW PST_ok Pm CTX0).

(* the first byte decides: zero is the empty string, nonzero a first byte of bs *)
Lemma ps_c0_nil : forall bs c, Forall (fun x => x <> 0) bs -> c = nth 0 (bs ++ [0]) 0 -> c = 0 -> bs = [].
Proof.
intros bs c Hnz -> Hc. destruct bs as [|b bs']; [reflexivity|]. exfalso. cbn in Hc.
inversion Hnz as [|x l Hb _]. exact (Hb Hc).
Qed.
Lemma ps_c0_cons : forall bs c, Forall (fun x => x <> 0) bs -> c = nth 0 (bs ++ [0]) 0 -> c <> 0 ->
  (0 < length bs)%nat /\ c = nth 0 bs 0.
Proof.
intros bs c Hnz -> Hc. destruct bs as [|b bs']; [cbn in Hc; contradiction|]. split; [cbn; lia | reflexivity].
Qed.
(* the partial granule's test of the shadow-checked load (A 0x88198 `blt (s & 7), shadow`) *)
Lemma ps_slow_lt : forall E s sv, ew E 11 = Z_to_bv 64 s -> ew E 71 = Z_to_bv 64 sv ->
  0 <= s < 2 ^ 64 -> 0 < sv < 8 -> s mod 8 < sv ->
  branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SOff 11 0) (SLit 7))) (sv_denot E (SOff 71 0)) = true.
Proof.
intros E s sv Hs Hv Hsr Hvr Hlt.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E (SOff 71 0)). fold (U E (SAlu ALU_AND (SOff 11 0) (SLit 7))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 11 s Hs Hsr), U_SLit, (U_atom E 71 sv Hv) by lia.
change (zcanon 7) with 7.
rewrite (YP0e.zcanon_id (Z.land s 7)) by (pose proof (YP0m.Z_land_upper s 7 ltac:(lia)); unfold M64; lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
rewrite !YP0e.swrap64_id by (unfold half64; lia). apply Z.ltb_lt. lia.
Qed.
(* a word of the R block (region 34, [R, R + 88)) of a seated state *)
Lemma ps_rword : forall E (H : word -> bool) mem R cs od e v,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 34%nat) 0 88 0 88 cs) ->
  bv_unsigned (ew E 34) = R -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mem) (R + od) = Some v.
Proof.
intros E H mem R cs od e v Hr HR Hin He Hv.
apply rdword_of_vm; [|exact Hv].
exact (field_of_region SEGS E (mrestrict H mem) 34 R cs 0 88 0 88 od 8%N e v Hr HR Hin He
  ltac:(change (8 * Z.of_N 8) with 64; exact Hv) ltac:(lia)).
Qed.

(* the write windows of the regions seated after put #1 (the post-put stretches) *)
Ltac awrS0 Ha R513q R39q R34q R2q R70q R11q HFL3 HSHF HR Hd0 HSTK' ly3 pos F ly :=
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?R513q, ?R39q, ?R34q, ?R2q, ?R70q, ?R11q in Ha;
  first [ clear - Ha; lia
        | unfold awr_byte; left; clear - Ha HR Hd0 HSTK'; lia
        | unfold awr_byte, in_frames; right; right; right; exists 0, pos; split; [left; reflexivity|];
          unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
          change (frame_addr ly3 0 pos) with (ly_F ly3 + fs_frame_off 0 pos); rewrite HFL3;
          change (ly_F ly + fs_frame_off 0 pos) with F;
          first [left; clear - Ha; lia | right; rewrite <- HSHF; clear - Ha; lia] ].

(* segment A: the prologue, frame_alloc_0, the frame header and its shadow, the opening-quote put (+ 0x110), s's NULL
   trap and s[0]'s ASan check, to the loop head (+ 0x180) or the tail join (+ 0x2c8). Its run and its continuations
   pass the opening-quote put (a crossing call), so KH / KT and the segment conclude SRr' *)
Lemma ps_seg_a : forall X ch,
  ps_pre X ch -> ps_s0 X -> Pm (x_mem X) ->
  (forall pos i j P lyc Sc Hpc Wc regsc memc mdc kc, ps_head X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin X)) ->
  (forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_tail X pos j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 712))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin X)) ->
  SRr' SEGS RZ_cf (x_W X) (cfg_at SEGS (SIGMA AS_put_string) (x_regs X) (x_mem X) (x_md X)) (ps_Qfin X).
Proof.
intros X ch Hpre HS0 HPM KH KT.
(* the one lift (route (b)): the plain stretch up to put #1 proves SRr into the walk's SRr' continuation *)
apply YGcfRhLift.ra_rh_of_SRr.
pose proof Hpre as (HFPRE & Hroom0 & Hrp0 & Huniv & H10 & H11 & Hocase & Hoch & HWIN0 & Ho1 & Ho2 & Hout0 & Hled0 &
  Hcstr0 & Hkept0 & Hdisj0 & Hfr & Hwmax0 & Hhead & Hlive0 & Hevs0 & Hcons0 & Hlen4).
destruct HFPRE as (HPRE & Hro0 & Htopstk & Hraceil & _).
assert (HSTK : ESTACK + 208 <= STK_put_string) by (vm_compute; congruence).
assert (HWIN : fwin_x SEGS (x_ly X) (x_W X) (x_regs X) (x_mem X) (x_d X)) by exact HWIN0.
pose proof (proj1 Hout0) as Ho8.
pose proof Hcstr0 as (_ & Hs4096 & Hsceil & _).
pose proof ASAN_CEIL_range as HCEIL0. unfold ASAN_CEIL in HCEIL0.
assert (Ho : x_sp X <= x_o X < 2 ^ 47).
{ pose proof HPRE as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47x & _ & _ & Htopx) & _). unfold fwin in HWIN0. unfold x_sp in *. lia. }
assert (Hs : 4096 <= x_s X < 2 ^ 47) by lia.
destruct X as [d ly S Hp W regs mem md o s bs buf st Lam peak ran most own rpsm rpx rpos rpi rpH0 rphist].
cbn [x_d x_ly x_S x_Hp x_W x_regs x_mem x_md x_o x_s x_bs x_buf x_st x_Lam x_peak x_ran x_most x_own x_rpsm x_rpx
  x_rpos x_rpi x_rpH0 x_rphist] in *.
unfold x_sp, x_n in *. cbn [x_regs x_bs] in *.
set (FP := prhWriter_cfp o buf (WriterApp.w_cap st)).
remember STK_put_string as STK eqn:ESTK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
assert (HSTK' : 208 <= STK) by (unfold ESTACK in HSTK; lia).
destruct (ps_entry STK ly S Hp W regs mem md ch o s HPRE HSTK' H10 H11 Ho Ho8 Hs) as [HS SHOK].
pose proof (ajournal_x_init_W SK SEGS B (@prh_pst prh_img_B) ARx STK d FP ly S Hp W regs mem md ch HPRE HWIN) as HJ.
set (E := ps_E regs (as_uar_cell B)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ps_E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold ps_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HR : spZ regs - 208 <= PS_R (spZ regs) <= spZ regs - 192 /\ PS_R (spZ regs) mod 32 = 0).
{ unfold PS_R. pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)).
  assert ((spZ regs - 192) mod 32 = 0 \/ (spZ regs - 192) mod 32 = 16).
  { pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)). pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)). lia. }
  split; [lia|]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_put_string)) with (Z_to_bv 64 (BASE + AF_put_string)).
paj_run_tok_x_inv RUNI HS HJ SHOK HPM PS_Bspan.
{ unfold ps_ss0, probe_region, saved_region, got_regionP, bcell_regionP, uargot_region, uarcell_region.
  cbn [ss_mem]. intros a (r & Hin & Ha). cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha;
      first [lia | unfold awr_byte; left; lia] | ]).
  try destruct Hin. }
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
assert (E34 : ew E 34 = Z_to_bv 64 (PS_R (spZ regs))).
{ subst E. unfold ps_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
assert (E3 : ew E 3 = getr regs 3) by (subst E; unfold ps_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; unfold ps_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
rewrite E34 in Rsp. rewrite E3 in Rgp. rewrite E4 in Rtp.
pmkst HS. rewrite <- Hsm0.
eapply SRr_bind.
{ eapply (@aj_stack_malloc_at_xm fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS segs_low errno_low OWNLOW SMX 0 ASM0 ltac:(lia)
    W _ _ (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly S Hp _ 0
    (PS_R (spZ regs) - (spZ regs + d)) (Z_to_bv 64 (BASE + (AF_put_string + 116)))).
  - exact HJ.
  - assert (HR64 : 0 <= PS_R (spZ regs) < 2 ^ 64) by lia.
    unfold spZ at 1. rewrite Rsp, (unsigned_lit_small _ HR64). try lia.
  - assert (H16 : PS_R (spZ regs) mod 16 = 0) by (pose proof (proj2 HR) as H32; lia).
    rewrite Zminus_mod, Zplus_mod, Hal16, Hd16, H16. try reflexivity.
  - lia.
  - unfold ESTACK in *. lia.
  - rewrite Rgp. exact Hgp.
  - rewrite Rtp. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [exact (proj1 AF_ps_ret) | exact (proj2 AF_ps_ret)].
  - assert (Hcl : forall cid l, count_cid cid l <= Z.of_nat (length l)).
    { intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
      destruct (c =? cid); lia. }
    pose proof (Hcl 0 (frames S)). lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & Hc2 & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hfresh & Hnev2 &
  Hbb2 & Hz & Hflag & Hfpres & HKept & HJt & Hsetfs & Hmn2).
rewrite Hc2.
(* the memory invariant across frame_alloc_0 (its m-form keep, srr_inv_call) *)
pose proof (PCALL _ _ Hmn2 HPM) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
replace (spZ regs + d + (PS_R (spZ regs) - (spZ regs + d))) with (PS_R (spZ regs)) in HKept, HJt by lia.
(* re-seat after the call: the caller-saved registers are havocked into the free atom band 35.. (below A_TEXT); keep the
   saved-register slots and the two shadow-base cells *)
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [1; 2; 3]%nat HS2.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
destruct (alx_const SEGS B ARx LAWS _ _ _ _ _ _ (proj1 HJ)) as (Kc1 & _ & Kg1 & _).
destruct (alx_const SEGS B ARx LAWS _ _ _ _ _ _ (proj1 HJ2)) as (Kc2 & _ & Kg2 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kg1, Kg2. rewrite (pal_cell B TL) in Kc1, Kc2.
pose proof (pa_obj_img 0 ltac:(lia)) as IG. pose proof (pa_obj_img 12 ltac:(lia)) as IC.
match type of HS2 with ?P -> _ => assert (HQ : P); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - kept_stack HKept HJ2 AG Usp.
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* the fake frame F (atom 39 = a0 after the call), its flag cell's address FL and its shadow address (fresh atoms) *)
pose proof (proj1 HJ2) as HAR2.
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR2 Hin2) as (HF32 & HFapp & HFpres & HFsh).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR2 Hin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr ly 0 pos) in *. set (FL := flag_addr ly 0 pos) in *.
lazymatch type of HS with st_ok_pi _ _ ?E1v _ _ => set (E1 := E1v) in HS end.
assert (E39 : ew E1 39 = Z_to_bv 64 F).
{ subst E1. unfold havoc. cbn [ew]. unfold CLOB. cbn [nth map Nat.ltb Nat.leb Nat.sub]. exact Ha0. }
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply img_env_havoc; [exact HEI | cbv; lia]).
set (SHF := PS_SB + F / 8).
lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
  pose proof (st_ok_pi_havoc_hi 512 E1 ss1 _ [Z_to_bv 64 FL; Z_to_bv 64 SHF] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
set (E2 := havoc E1 512 [Z_to_bv 64 FL; Z_to_bv 64 SHF]) in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (E2old : forall n, (n < 512)%nat -> ew E2 n = ew E1 n) by (intros n Hn; subst E2; apply ew_havoc_old; exact Hn).
assert (E512 : ew E2 512 = Z_to_bv 64 FL) by (subst E2; unfold havoc; cbn [ew]; reflexivity).
assert (E513 : ew E2 513 = Z_to_bv 64 SHF) by (subst E2; unfold havoc; cbn [ew]; reflexivity).
assert (E2_39 : ew E2 39 = Z_to_bv 64 F) by (rewrite E2old by lia; exact E39).
assert (E2_32 : ew E2 32 = Z_to_bv 64 PS_SB).
{ rewrite E2old by lia. subst E1. rewrite ew_havoc_old by lia. subst E. unfold ps_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E2_34 : ew E2 34 = Z_to_bv 64 (PS_R (spZ regs))).
{ rewrite E2old by lia. subst E1. rewrite ew_havoc_old by lia. exact E34. }
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
(* the facts of the three frame atoms and the shadow declaration of F *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss2 _ =>
  pose proof (st_ok_pi_add_fact E2 ss2 _ 39 (mkAF 4096 140737479966720 5) HS) as HS3 end.
match type of HS3 with ?P -> _ => assert (HP : P); [|specialize (HS3 HP); clear HP] end.
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E2_39, unsigned_lit_small by lia. change (2 ^ 5) with 32.
  split; [lia|]. split; [rewrite HFq, Z.mul_comm; apply Z_mod_mult | lia]. }
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss2 _ =>
  pose proof (st_ok_pi_add_fact E2 ss2 _ 513 (mkAF (PS_SB + 512) (PS_SB + 2 ^ 44) 2) HS) as HS3 end.
match type of HS3 with ?P -> _ => assert (HP : P); [|specialize (HS3 HP); clear HP] end.
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. unfold SHF, PS_SB, SHADOW_OFF in *.
  rewrite E513, unsigned_lit_small by lia. change (2 ^ 2) with 4. split; [lia|]. split; [|lia].
  rewrite HFq. replace (32 * (F / 32)) with ((F / 32 * 4) * 8) by lia. rewrite Z.div_mul by lia.
  rewrite Zplus_mod, Z_mod_mult. reflexivity. }
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss2 _ =>
  pose proof (st_ok_pi_add_alias E2 ss2 _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 39 0) (SLit 3)) (SOff 32 0)) (SOff 513 0) HS
    (shadow_decl_ok E2 39 32 513 F PS_SB E2_39 ltac:(lia) E2_32 E513)) as HS3 end.
clear HS. rename HS3 into HS.
(* the regions the stretch writes: the realigned frame's slots, the fake frame, its shadow *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (UB : forall n v, ew E2 n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E2 (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HFimg : forall a, F <= a < F + 64 -> ~ in_img SEGS a).
{ intros a Ha. exact (proj2 (alx_client_img SEGS B ARx LAWS ly S2 Hp W mem2 md2 a HAR2
    (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj Hin2 Ha))))))). }
pose proof (Hobj 0 ltac:(lia)) as (Ig0 & Ic0 & _). pose proof (Hobj 7 ltac:(lia)) as (Ig7 & Ic7 & _).
rewrite Z.add_0_r in Ig0, Ic0.
assert (DG : F + 64 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= F).
{ destruct (Z_le_gt_dec (F + 64) (VAL (A_OBJ 0))); [left; lia|]. destruct (Z_le_gt_dec (VAL (A_OBJ 0) + 8) F); [right; lia|].
  exfalso. destruct (Z_le_gt_dec F (VAL (A_OBJ 0))).
  - apply (HFimg (VAL (A_OBJ 0))); [lia | exact Ig0].
  - apply (HFimg F); [lia|]. pose proof (proj1 (Hobj (F - VAL (A_OBJ 0)) ltac:(lia))) as Hx.
    replace (VAL (A_OBJ 0) + (F - VAL (A_OBJ 0))) with F in Hx by lia. exact Hx. }
assert (DC : F + 64 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= F).
{ destruct (Z_le_gt_dec (F + 64) (VAL (A_OBJ 12))); [left; lia|]. destruct (Z_le_gt_dec (VAL (A_OBJ 12) + 8) F); [right; lia|].
  exfalso. destruct (Z_le_gt_dec F (VAL (A_OBJ 12))).
  - apply (HFimg (VAL (A_OBJ 12))); [lia | exact Ic0].
  - apply (HFimg F); [lia|]. pose proof (proj1 (proj2 (Hobj (F - VAL (A_OBJ 12)) ltac:(lia)))) as Hx.
    replace (VAL (A_OBJ 12) + (F - VAL (A_OBJ 12))) with F in Hx by lia. exact Hx. }
pose proof (segs_low _ Ig7) as LG7. pose proof (segs_low _ Ic7) as LC7.
assert (RG : base_val E2 (Some (A_OBJ 0)) = VAL (A_OBJ 0)).
{ cbn [base_val]. exact (HEI2 (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). }
assert (RC : base_val E2 (Some (A_OBJ 12)) = VAL (A_OBJ 12)).
{ cbn [base_val]. exact (HEI2 (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). }
assert (R2 : base_val E2 (Some 2%nat) = spZ regs).
{ cbn [base_val]. rewrite E2old by lia. subst E1. rewrite ew_havoc_old by lia. exact Usp. }
assert (R34 : base_val E2 (Some 34%nat) = PS_R (spZ regs)) by (apply UB; [exact E2_34 | lia]).
assert (R39 : base_val E2 (Some 39%nat) = F) by (apply UB; [exact E2_39 | lia]).
assert (R513 : base_val E2 (Some 513%nat) = SHF) by (apply UB; [exact E513 | unfold SHF, PS_SB, SHADOW_OFF; lia]).
assert (HSHF : SHF = shadow_addr F) by (unfold SHF, shadow_addr, PS_SB; lia).
assert (HFsh' : forall i, 0 <= i < 8 -> apresent (w_H W) mem2 (SHF + i)).
{ intros i Hi. rewrite HSHF. exact (proj1 (HFsh i ltac:(change (64 / 8) with 8; lia))). }
assert (HFapp' := HFapp). destruct HFapp' as (HFa0 & HFa1).
pose proof ASAN_CEIL_range as HCEIL. unfold ASAN_CEIL in HCEIL.
assert (HSPc : YM05.alloc_ceiling <= spZ regs - STK) by lia.
assert (HSHFr : SHADOW_OFF + 512 <= SHF /\ SHF + 8 <= kHighMemBeg).
{ rewrite HSHF. unfold shadow_addr, kHighMemBeg, SHADOW_OFF. split; [lia|].
  unfold kLowShadowBeg, kHighMemBeg in HFa1. lia. }
(* the realigned frame's slots R .. R + 88 *)
norm_ss HS.
add_reg HS rframe_region.
{ unfold region_ok, rframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite R34. split; [lia|]. split; [lia|]. split; [|constructor].
  intros oo Hoo. apply (apresent_writable SEGS). apply Hpres2. lia. }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi rframe_region].
  lazymatch goal with |- context [base_val E2 (Some 241%nat)] => change (Some 241%nat) with (Some (A_OBJ 0)) | _ => idtac end.
  lazymatch goal with |- context [base_val E2 (Some 253%nat)] => change (Some 253%nat) with (Some (A_OBJ 12)) | _ => idtac end.
  rewrite ?R34, ?R2, ?RG, ?RC. unfold kLowMemEnd in *.
  repeat split; lia. }
(* the fake frame F .. F + 64, its flag cell's address at F + 56 *)
norm_ss HS.
add_reg HS (fframe_reg 39 512).
{ unfold region_ok, fframe_reg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite R39. split; [lia|]. split; [lia|]. split.
  - intros oo Hoo. apply (apresent_writable SEGS). apply Hfpres. lia.
  - constructor; [|constructor].
    pose proof (rdword_range_ps _ _ _ _ Hflag) as HFLr.
    apply (chunk_ok_val SEGS E2 _ F 56 8 (SOff 512 0) FL);
      [cbn [sv_denot]; rewrite E512, unsigned_lit_small, Z.add_0_r by lia; reflexivity | zside | zside |].
    replace (F + 56) with (F + 64 - 8) by lia. exact (val_mem_of_rdword SEGS (w_H W) mem2 _ _ Hflag). }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi rframe_region fframe_reg].
  lazymatch goal with |- context [base_val E2 (Some 241%nat)] => change (Some 241%nat) with (Some (A_OBJ 0)) | _ => idtac end.
  lazymatch goal with |- context [base_val E2 (Some 253%nat)] => change (Some 253%nat) with (Some (A_OBJ 12)) | _ => idtac end.
  rewrite ?R39, ?R34, ?R2, ?RG, ?RC. repeat split; lia. }
(* F's shadow bytes *)
norm_ss HS.
add_reg HS (fshadow_reg 513).
{ unfold region_ok, fshadow_reg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite R513. unfold SHADOW_OFF, kHighMemBeg in HSHFr. split; [lia|]. split; [lia|]. split; [|constructor].
  intros oo Hoo. apply (apresent_writable SEGS). apply HFsh'. lia. }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi rframe_region fframe_reg fshadow_reg].
  lazymatch goal with |- context [base_val E2 (Some 241%nat)] => change (Some 241%nat) with (Some (A_OBJ 0)) | _ => idtac end.
  lazymatch goal with |- context [base_val E2 (Some 253%nat)] => change (Some 253%nat) with (Some (A_OBJ 12)) | _ => idtac end.
  rewrite ?R513, ?R39, ?R34, ?R2, ?RG, ?RC. unfold kLowMemEnd, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  repeat split; lia. }
norm_ss HS.
idtac "REGIONS-ADDED".
(* run: the header (magic, the frame's descriptor, the pc), the shadow f1 f1 f1 f1 f8 f3 f3 f3, the opening-quote
   put's arguments, to the call of put (A 0x87f40) *)
pnt_run_to_inv NTRUNTOI HS HJ2 HPM (AF_put_string + 276).
{ intros a (r & Hin & Ha). cbn [In ss_mem] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi fshadow_reg fframe_reg rframe_region] in Ha;
      rewrite ?R513, ?R39, ?R34, ?R2 in Ha;
      first [ lia
            | unfold awr_byte; left; lia
            | unfold awr_byte, in_frames; right; right; right; exists 0, pos; split; [left; reflexivity|];
              unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
              first [left; fold F; lia | right; fold F; rewrite <- HSHF; lia] ] | ]).
  try destruct Hin. }
idtac "RUN-DONE".
try (match goal with H : frame_of ?Ex ?rsx ?m1 ?m2 |- _ => idtac "FRAME-HYP" H; fail end).
try (match goal with H : acall_kept_x _ _ _ _ _ _ _ _ _ _ _ |- _ => idtac "KEPT-HYP" H; fail end).
try (match goal with H : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => idtac "AJ-HYP" H; fail end).
try (match goal with H : st_ok _ _ _ _ |- _ => idtac "ST-HYP" H; fail end).
pmkst HS.
prreg HS (10%bv : bv 5) A0. prreg HS (11%bv : bv 5) A1. prreg HS (12%bv : bv 5) A2.
prreg HS (1%bv : bv 5) Ra1. prreg HS (2%bv : bv 5) Sp1. prreg HS (3%bv : bv 5) Gp1. prreg HS (4%bv : bv 5) Tp1.
prreg HS (8%bv : bv 5) S01.
(* ---- the put #1 call (A 0x87f40): put(o, .str.17, 1) ---- *)
assert (E2E : forall k, (k < 35)%nat -> ew E2 k = ew E k).
{ intros k Hk. rewrite E2old by lia. subst E1. apply ew_havoc_old. exact Hk. }
assert (EE : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk Hr. subst E. unfold ps_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ k r Hr). }
assert (RA0 : getr (ms_regs ms0) 10 = w64 o) by (rewrite A0, E2E, (EE 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (RA1 : getr (ms_regs ms0) 11 = w64 (ps_str 65)).
{ rewrite A1, (HEI2 243%nat ltac:(unfold A_TEXT, A_LIM; lia)). unfold ps_str, w64. change (A_OBJ 2) with 243%nat.
  f_equal; try (f_equal; vm_compute; reflexivity). }
assert (RA2 : getr (ms_regs ms0) 12 = w64 1) by exact A2.
lazymatch type of Ra1 with context [BASE + ?k] =>
  assert (Hk276 : k = AF_put_string + 276) by (unfold AF_put_string; rewrite (proj2 B_entry_put_string); vm_compute; reflexivity);
  rewrite Hk276 in Ra1 end.
assert (RSP : getr (ms_regs ms0) 2 = w64 (PS_R (spZ regs))) by (rewrite Sp1; exact E2_34).
assert (RS0 : getr (ms_regs ms0) 8 = w64 (spZ regs)).
{ rewrite S01, E2E, (EE 2%nat 2%bv) by (lia || reflexivity). unfold spZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (RGP : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite Gp1, E2E, (EE 3%nat 3%bv) by (lia || reflexivity); exact Hgp).
assert (RTP : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite Tp1, E2E, (EE 4%nat 4%bv) by (lia || reflexivity); exact Htp).
pose proof (AF_ps_ret_k 276 ltac:(lia) ltac:(reflexivity)) as (H276 & H276b).
pose proof STK_ps_facts as (SK1 & SK2 & SK3 & SK4 & SK5 & SK6).
idtac "PUT1-REGS-DONE".
pose proof (proj1 HJ2) as HARc.
unfold kHighMemBeg, SHADOW_OFF in HSHFr.
pose proof (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HAR2) as (HSEP2 & _).
(* ---- the bytes the walk carries, kept from the entry to the put #1 call: the prologue's run (HFr), frame_alloc_0
   (HKept), the header's run (HFr0) ---- *)
assert (KST : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha.
  transitivity (aview SEGS (w_H W) mem2 a).
  { apply (kept_of_frame E2 _ (w_H W) mem2 (ms_mem ms0) (fun x => spZ regs <= x < 2 ^ 64) HFr0); [|exact Ha].
    intros x Hx0. split; [clear - Hx0 HSPc HCEIL0 HSTK'; lia|].
    nwrA R513 R39 R34 R2 ltac:(fun Hx => clear - Hx Hx0 HSHFr HFceil HSPc HR HSTK' HCEIL0; lia). }
  transitivity (aview SEGS (w_H W) (ms_mem ms) a).
  { destruct HKept as (K1 & _). apply K1; clear - Ha HSPc HR HSTK'; lia. }
  apply (kept_of_frame E _ (w_H W) mem (ms_mem ms) (fun x => spZ regs <= x < 2 ^ 64) HFr); [|exact Ha].
  intros x Hx0. split; [clear - Hx0 HSPc HCEIL0 HSTK'; lia|]. nwr0 Usp ltac:(fun Hx => clear - Hx Hx0; lia). }
idtac "KST-DONE".
assert (KBLK : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  aview SEGS (w_H W) (ms_mem ms0) (b + i) = aview SEGS (w_H W) mem (b + i)).
{ intros b m i Hin Hi.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _).
  assert (HinS2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 Hp W mem2 md2 b m 0 pos HAR2 HinS2 Hin2) as Hzd.
  unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. change (fs_frame_bytes 0) with 64 in Hzd. fold F in Hzd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  transitivity (aview SEGS (w_H W) mem2 (b + i)).
  { apply (kept_of_frame E2 _ (w_H W) mem2 (ms_mem ms0) (fun x => x = b + i) HFr0); [|reflexivity].
    intros x ->. split; [clear - Hi Hb4096 Hbceil HCEIL0; unfold req_size in *; lia|].
    nwrA R513 R39 R34 R2 ltac:(fun Hx => clear - Hx Hi Hbapp Hbceil Hzd HSHFr HSPc HR HSTK' HF4096; lia). }
  transitivity (aview SEGS (w_H W) (ms_mem ms) (b + i)).
  { destruct HKept as (_ & K2 & _). apply (K2 b m i Hin Hi). exact (fun H => H). }
  apply (kept_of_frame E _ (w_H W) mem (ms_mem ms) (fun x => x = b + i) HFr); [|reflexivity].
  intros x ->. split; [clear - Hi Hb4096 Hbceil HCEIL0; unfold req_size in *; lia|].
  nwr0 Usp ltac:(fun Hx => clear - Hx Hi Hbceil HSPc HSTK'; lia). }
idtac "KBLK-DONE".
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Hi Hio Hie. pose proof (segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  assert (HaF : a < F \/ F + 64 <= a).
  { destruct (Z_lt_le_dec a F) as [Hlt | Hge]; [left; exact Hlt|].
    destruct (Z_lt_le_dec a (F + 64)) as [Hlt2 | Hge2]; [exfalso; exact (HFimg a ltac:(lia) Hi) | right; exact Hge2]. }
  transitivity (aview SEGS (w_H W) mem2 a).
  { apply (kept_of_frame E2 _ (w_H W) mem2 (ms_mem ms0) (fun x => x = a) HFr0); [|reflexivity].
    intros x ->. split; [clear - Hl; lia|].
    nwrA R513 R39 R34 R2 ltac:(fun Hx => clear - Hx Hl HaF HSHFr HSPc HR HSTK' HCEIL0; lia). }
  transitivity (aview SEGS (w_H W) (ms_mem ms) a).
  { destruct HKept as (_ & _ & K3 & _). apply K3; assumption. }
  apply (kept_of_frame E _ (w_H W) mem (ms_mem ms) (fun x => x = a) HFr); [|reflexivity].
  intros x ->. split; [clear - Hl; lia|]. nwr0 Usp ltac:(fun Hx => clear - Hx Hl HSPc HSTK' HCEIL0; lia). }
idtac "KIMG-DONE".
pose proof (ps_led_blocks B _ _ _ _ _ _ _ _ _ _ Hled0) as HallL.
assert (HLB : forall b k, In (b, k) Lam -> 0 <= k /\ In (b - cf_head, k + cf_head) (ablocks B ly S) /\
  (forall a, b - cf_head <= a < b + k -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)).
{ intros b k Hin. pose proof (proj1 (Forall_forall _ _) HallL (b, k) Hin) as (Hk0 & HinB & _). cbn [fst snd] in *.
  pose proof (@cf_head_nonneg cp) as Hch0.
  split; [exact Hk0|]. split; [exact HinB|]. intros a Ha.
  replace a with ((b - cf_head) + (a - (b - cf_head))) by lia. apply (KBLK _ _ _ HinB).
  unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia. }
assert (HLEDc : prh_ledger B ly S2 Hp W (ms_mem ms0) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own).
{ apply (prh_ledger_kept ly S Hp W mem Lam peak _ _ ran most own ly S2 W (ms_mem ms0) Hled0 Eab).
  - intros a Ha. destruct (PST_ok a Ha) as (Hi & Hio & Hie). exact (KIMG a Hi Hio Hie).
  - intros b k a Hin Ha. destruct (HLB b k Hin) as (Hk0 & _ & Hk). apply Hk. unfold prh_head_wide in HW. lia. }
idtac "LED-DONE".
assert (HOUTc : prhWriter_out W (ms_mem ms0) Lam o buf st).
{ assert (Hcase : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
  { intros Hc0. destruct Hout0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz0 & _) | (_ & HinL & _)]); [lia | exact HinL]. }
  apply (prhW_out_kept W mem Lam o buf st W (ms_mem ms0) ly S2 Hp _ Hout0 HARc).
  - intros Hc0. pose proof (ps_led_blocks B _ _ _ _ _ _ _ _ _ _ HLEDc) as Hall2.
    exact (proj1 (Forall_forall _ _) Hall2 _ (Hcase Hc0)).
  - intros a Ha. apply KST. lia.
  - intros Hc0 a Ha. destruct (HLB _ _ (Hcase Hc0)) as (_ & _ & Hk). apply Hk. pose proof (@cf_head_nonneg cp). lia. }
idtac "OUT-DONE".
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms0))).
{ apply (ps_arodata_keep W W mem (ms_mem ms0) Hro0). intros a Hro Hio Hie. exact (KIMG a (in_roP_img a Hro) Hio Hie). }
idtac "RO-DONE".
(* the saved ra / s0 slots at the call (the prologue's sd's, region 3 of the call state) *)
lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ =>
  let rv := eval vm_compute in (nth_error (ss_mem ssx) 3) in
  lazymatch rv with Some ?rg =>
    assert (HSV : region_ok SEGS E2 (mrestrict (w_H W) (ms_mem ms0)) rg)
      by exact (st_ok_region_nth SEGS E2 _ _ 3 rg HS ltac:(vm_compute; reflexivity)) end end.
assert (R2' : bv_unsigned (ew E2 2) = spZ regs) by (rewrite E2E, (EE 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (Rng : forall x : bv 64, 0 <= bv_unsigned x < 2 ^ 64).
{ intros x. pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. exact Hx. }
assert (VRA : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs + -8) 8 (raZ regs)).
{ apply (slot_of_region SEGS E2 _ (spZ regs) _ (-104) 0 (-104) 0 (-8) (SOff 1 0) (raZ regs) HSV R2').
  - cbn [In]. tauto.
  - cbn [sv_denot]. rewrite E2E, (EE 1%nat 1%bv) by (lia || reflexivity). unfold raZ. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity.
  - exact (Rng _). }
assert (VS0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs + -16) 8 (s0Z regs)).
{ apply (slot_of_region SEGS E2 _ (spZ regs) _ (-104) 0 (-104) 0 (-16) (SOff 8 0) (s0Z regs) HSV R2').
  - cbn [In]. tauto.
  - cbn [sv_denot]. rewrite E2E, (EE 8%nat 8%bv) by (lia || reflexivity). unfold s0Z. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity.
  - exact (Rng _). }
pose proof (rdword_of_vm _ _ _ _ VRA (Rng _)) as RDRA. pose proof (rdword_of_vm _ _ _ _ VS0 (Rng _)) as RDS0.
replace (spZ regs + -8) with (spZ regs - 8) in RDRA by lia. replace (spZ regs + -16) with (spZ regs - 16) in RDS0 by lia.
idtac "SAVED-DONE".
(* the frame chain at the call: put_string's own frame record pushed on the entry's chain *)
assert (HCH1 : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms0)) (PS_R (spZ regs)) (spZ regs) ch1).
{ destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    apply (achain_push ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem ms0)) (spZ regs) (s0Z regs) (raZ regs) ch
      (PS_R (spZ regs)) Hch); try lia.
    + intros a Ha. apply KST. lia.
    + exact RDRA.
    + exact RDS0.
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH1 as (ch1 & HCH1).
idtac "ACHAIN-DONE".
(* the literal, the capacity grid, the room and length budgets of the opening-quote put *)
destruct (HLIT18 ly S2 Hp W (ms_mem ms0) _ HARc HROc) as (HSRC17 & HK17).
assert (Hlit_img : in_img SEGS (ps_str 65)).
{ assert (Hx65 : ps_str 65 <= ps_str 65 < ps_str 65 + 1) by lia.
  destruct HK17 as [(b & m & Hin & _) | [(_ & _ & _ & Hall) | Himg]]; [destruct Hin | |].
  - destruct (Hall (ps_str 65) Hx65) as (Hro & _). exact (in_roP_img _ Hro).
  - unfold kept_img in Himg. destruct Himg as (_ & _ & Hall).
    destruct (Hall (ps_str 65) Hx65) as (Hro & _). exact (in_roP_img _ Hro). }
assert (Hcase : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc0. destruct Hout0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz0 & _) | (_ & HinL & _)]); [lia | exact HinL]. }
assert (HWM1 : Z.of_nat (length (WriterApp.w_text st)) + 1 + 1 <= prhWriter_WMAX).
{ pose proof (wstr_len2 bs). lia. }
assert (HHOME1 : prhWriter_src_home B ly S2 Lam buf (WriterApp.w_cap st) (ps_str 65) 1).
{ split; [left; exact (kept_at_nil_lam Lam _ _ HK17)|].
  destruct (Z.eq_dec (WriterApp.w_cap st) 0) as [Hz0 | Hnz]; [left; exact Hz0 | right].
  destruct (HLB _ _ (Hcase Hnz)) as (Hk0 & HinB & _).
  destruct (Z_lt_le_dec (ps_str 65) buf) as [Hl | Hge]; [left; lia|].
  destruct (Z_lt_le_dec (ps_str 65) (buf + WriterApp.w_cap st)) as [Hl2 | Hge2]; [|right; lia].
  exfalso. pose proof (@cf_head_nonneg cp) as Hch0.
  assert (Hin_blk : buf - cf_head <= ps_str 65 < buf - cf_head + req_size (WriterApp.w_cap st + cf_head)).
  { unfold req_size. destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); lia. }
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md (ps_str 65) HAR
    (or_introl (ex_intro _ (buf - cf_head) (ex_intro _ (WriterApp.w_cap st + cf_head) (conj HinB Hin_blk)))))).
  exact Hlit_img. }
idtac "PUT1-PREM-DONE".
(* put's chain from o at the call (the ARGUMENT ps_chain_arg): [o - 16, o) at or above sp is kept from the entry,
   the saved slots hold the entry registers *)
assert (HOK0 : forall a, o - 16 <= a < o -> spZ regs <= a ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha1 Ha2. apply KST. lia. }
assert (HSAV0 : Forall (fun p => rdword (aview SEGS (w_H W) (ms_mem ms0)) (spZ regs + fst p) =
  Some (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) ps_saved_list).
{ unfold ps_saved_list. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (apply rdword_of_vm; [| exact (Rng _)]);
  match goal with |- val_mem _ _ (_ + ?od) 8 (bv_unsigned (getr regs (Z_to_bv 5 ?r))) =>
    apply (slot_of_region SEGS E2 _ (spZ regs) _ (-104) 0 (-104) 0 od (SOff (Z.to_nat r) 0) _ HSV R2');
    [ cbn [In]; repeat first [left; reflexivity | right]
    | cbn [sv_denot]; rewrite E2E by (cbv; lia);
      rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)) by first [cbv; lia | vm_compute; reflexivity];
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | exact (Rng _) ] end. }
idtac "CHAIN-ARG-DONE".
pose proof (pa_B_ok (L := B_prog_listing) (PAImg := PA)) as (HB0 & HB1 & _).
(* the entry record (the continuations' X) *)
lazymatch type of Hpre with context [ps_pre ?X0 ?ch0] => set (XR := X0) in * end.
destruct Hsetfs as (fS2 & ES2).
(* the join invariant at the put #1 call: no piece put yet *)
assert (HF56c : rdword (aview SEGS (w_H W) (ms_mem ms0)) (F + 56) = Some FL).
{ replace (F + 56) with (F + 64 - 8) by lia. rewrite <- Hflag. apply rdword_eq_of. intros i Hi.
  apply (kept_of_frame E2 _ (w_H W) mem2 (ms_mem ms0) (fun x => x = F + 64 - 8 + i) HFr0); [|reflexivity].
  intros x ->. split; [clear - Hi HFceil HCEIL0 HF4096; lia|].
  nwrA R513 R39 R34 R2 ltac:(fun Hx => unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *;
    clear - Hx Hi HSHFr HFceil HSPc HR HSTK' HCEIL0 HF4096 HFa1 HSHF; lia). }
assert (HCOM0 : ps_common XR pos [] ly S2 Hp W (ms_mem ms0) (with_vm_backing (m_vm_lazy md2) mat0 md2) 0).
{ unfold XR, ps_common, ps_saved_ok, ps_okeep. unfold x_R, x_n, x_SHF, x_FL, x_F, x_FP. unfold x_sp.
  cbn [x_d x_ly x_S x_Hp x_W x_regs x_mem x_md x_o x_s x_bs x_buf x_st x_Lam x_peak x_ran x_most x_own x_rpsm x_rpx
    x_rpos x_rpi x_rpH0 x_rphist].
  split; [subst STK; exact HJ2|].
  split; [exact HSAV0|].
  split; [exact HF56c|].
  split; [intros a Ha1 Ha2; apply KST; clear - Ha1 Ha2 Ho; lia|].
  split; [exact HPM|].
  split.
  { exists [], ran, buf, Lam, peak. cbn [prhWriter_putN].
    (* no put yet: no outcome, no call (the batch kit's prh_oks at ns := prhWriter_reqs [] st [], most, ran, ran) *)
    split.
    { unfold ps_oks. rewrite prhW_k_nil. split.
      - unfold prh_oks. split; [intros i Hi; exfalso; lia|]. split; [left; reflexivity|]. intros i Hi; exfalso; lia.
      - intros i Hi; exfalso; lia. }
    split; [exact HOUTc|]. split; [exact HLEDc|].
    split; [left; repeat split; try reflexivity; rewrite Eab; apply Permutation_refl|].
    split; [exact Hkept0|]. split; [intros b0 m Hin _ _; exact Hin|]. split; [exact Hdisj0|].
    exists rphist. cbn [prhWriter_evs length]. rewrite Nat.add_0_r. rewrite ES2.
    apply PresetRoomPosKeep.room_pos_set_fs; exact Hrp0. }
  split; [rewrite ES2; apply RL_set_fs; exact Hroom0|].
  split; [exact HROc|].
  unfold ps_wkeep, x_sp, x_d, x_W, x_mem, x_regs. intros a Ha1 _. apply KST. clear - Ha1 Hdtop Htop2 H47. lia. }
idtac "COM0-DONE".
(* put #1: put(o, .str.17, 1) through the generic put step. The cut of route (b): the plain stretch hands its state to
   the walk's SRr' continuation (SRr_ret), and the join at wle is lifted to wle' (ps_commonR_mono, wle_wle') *)
apply SRr_ret.
apply (ps_put_step XR ch pos [] [34] (WriterSpec.spieces_run [] bs ++ [[34]]) ly S2 Hp W (ms_regs ms0) (ms_mem ms0)
  (with_vm_backing (m_vm_lazy md2) mat0 md2) 0 (Z_to_bv 64 (BASE + (AF_put_string + 276))) (ps_str 65)).
- exact HFRMx.
- exact Hpre.
- exact HS0.
- apply (ps_commonR_mono B ARx Pm (@wle SEGS) (wle' SEGS RZ_cf) (wle_wle' SEGS RZ_cf)). exact HCOM0.
- reflexivity.
- unfold XR, x_R, x_sp; cbn [x_regs]. unfold spZ at 1. rewrite RSP. apply unsigned_lit_small. lia.
- exact RGP.
- exact RTP.
- exact Ra1.
- apply ret_ok_codeptr_v; [exact (proj1 H276) | exact (proj2 H276)].
- rewrite unsigned_lit_small by lia. exact H276b.
- assert (Hc276 : BASE + (AF_put_string + 276) < YM05.alloc_ceiling).
  { apply ps_ret_lt_ceil. cbn [In]. tauto. }
  rewrite unsigned_lit_small by lia. exact Hc276.
- unfold XR, x_sp; cbn [x_regs]. unfold s0Z. rewrite RS0. unfold w64. apply unsigned_lit_small. lia.
- exact RA0.
- exact RA1.
- exact RA2.
- exact HSRC17.
- intros Lamc bufc capc Hk Hd Hin Hblks. change (Z.of_nat (length [34])) with 1.
  split; [left; exact (kept_at_nil_lam Lamc _ _ HK17)|].
  destruct (Z.eq_dec capc 0) as [Hz0 | Hnz]; [left; exact Hz0 | right].
  pose proof (Hblks _ _ (Hin Hnz)) as HinB. pose proof (@cf_head_nonneg cp) as Hch0.
  destruct (Z_lt_le_dec (ps_str 65) bufc) as [Hl | Hge]; [left; clear - Hl; lia|].
  destruct (Z_lt_le_dec (ps_str 65) (bufc + capc)) as [Hl2 | Hge2]; [|right; clear - Hge2; lia].
  exfalso.
  assert (Hcz : 0 <= capc + cf_head).
  { pose proof (ps_led_blocks B _ _ _ _ _ _ _ _ _ _ HLEDc) as _. clear - Hge Hl2 Hch0. lia. }
  assert (Hin_blk : bufc - cf_head <= ps_str 65 < bufc - cf_head + req_size (capc + cf_head)).
  { pose proof (req_size_pos _ Hcz) as Rq. clear - Hge Hl2 Rq Hch0. lia. }
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly S2 Hp W (ms_mem ms0) _ (ps_str 65) HARc
    (or_introl (ex_intro _ (bufc - cf_head) (ex_intro _ (capc + cf_head) (conj HinB Hin_blk)))))).
  exact Hlit_img.
- intros ly3 S3 Hp3 W3 regs3 mem3 md3 k1 HCOM1 HP3 KW3 KP3 KF3.
  idtac "PUT1-POST". subst STK.
  (* after put #1 the walk's relation is wle' SEGS RZ_cf: its runners and branches conclude SRrG at it *)
  unfold SRr'.
  change (x_R XR) with (PS_R (spZ regs)) in KW3, KP3. change (x_sp XR) with (spZ regs) in KW3, KP3.
  change (x_F XR pos) with F in KF3. change (x_SHF XR pos) with SHF in KF3.
  pose proof HCOM1 as (HJ3 & _ & _ & _ & HPM3 & HWR1 & _).
  unfold XR, x_FP, x_sp in HJ3. cbn [x_d x_ly x_S x_Hp x_W x_regs x_mem x_md x_o x_buf x_st] in HJ3.
  fold FP in HJ3. clear HPM. rename HPM3 into HPM.
  pose proof (ajxR_ar HJ3) as HAR3. pose proof (ajxR_ly HJ3) as HLLE3. pose proof (ajxR_frs HJ3) as HFRS3.
  assert (HFL3 : ly_F ly3 = ly_F ly) by (destruct HLLE3 as (_ & _ & _ & _ & _ & HFx & _); exact HFx).
  assert (Hin3 : In (0, pos) (frames S3)) by (rewrite HFRS3; left; reflexivity).
  pose proof (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR3 Hin3) as (_ & _ & HFpres3 & HFsh3).
  unfold frame_addr in HFpres3, HFsh3. rewrite HFL3 in HFpres3, HFsh3.
  change (ly_F ly + fs_frame_off 0 pos) with F in HFpres3, HFsh3.
  change (fs_frame_bytes 0) with 64 in HFpres3, HFsh3. change (64 / 8) with 8 in HFsh3.
  (* ---- after put #1 (A 0x87f44): re-seat, keeping F's shadow (0), F (1), the R slots (2); the saved slots stay out
     of every later window (the stretches to the joins never write them), so frame_of keeps them ---- *)
  jafter_call_keep_pi HS 51%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
  match type of HS3 with ?P -> _ => assert (HQ : P); [|specialize (HS3 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (region_kept_av2 E2 _ _ _ _ 513%nat SHF);
        [rewrite E513; apply unsigned_lit_small; clear - HSHFr; unfold SHADOW_OFF in HSHFr; lia | |].
      + intros a Ha. apply KF3. right. clear - Ha; lia.
      + intros a Ha. pose proof (HFsh3 (a - SHF) ltac:(clear - Ha; lia)) as Hx. rewrite <- HSHF in Hx.
        replace (SHF + (a - SHF)) with a in Hx by lia. exact (proj1 Hx).
    - apply (region_kept_av2 E2 _ _ _ _ 39%nat F);
        [rewrite E2_39; apply unsigned_lit_small; clear - HF4096 HFceil HCEIL0; lia | |].
      + intros a Ha. apply KF3. left. clear - Ha; lia.
      + intros a Ha. exact (proj1 (HFpres3 a ltac:(clear - Ha; lia))).
    - apply (region_kept_av2 E2 _ _ _ _ 34%nat (PS_R (spZ regs))); [rewrite E2_34; apply unsigned_lit_small; lia | |].
      + intros a Ha. apply KW3. clear - Ha HR; lia.
      + intros a Ha. apply KP3. clear - Ha HR; lia. }
  idtac "RESEAT1-DONE".
  lazymatch type of HS3 with st_ok_pi _ _ ?Epv _ _ => set (Ep := Epv) in HS3 end.
  assert (HEIp : img_env VAL A_LIM Ep) by (subst Ep; apply img_env_havoc; [exact HEI2 | cbv; lia]).
  assert (Epold : forall k, (k < 51)%nat -> ew Ep k = ew E2 k) by (intros k Hk; subst Ep; apply ew_havoc_old; exact Hk).
  clear HS. rename HS3 into HS.
  (* the writer after put #1 *)
  destruct HWR1 as (ok1 & ran1 & buf1 & Lam1 & peak1 & Hoks1 & Hout1 & Hled1 & Hblk1 & Hkept1 & Hlive1 & Hdisj1).
  change (x_st XR) with st in *. change (x_s XR) with s in *. change (x_n XR) with (Z.of_nat (length bs)) in *.
  change (x_Lam XR) with Lam in *. change (x_o XR) with o in *.
  assert (Hn1 : 0 < Z.of_nat (length bs) + 1) by lia.
  assert (Hd0' : WriterApp.w_cap st = 0 \/ s + (Z.of_nat (length bs) + 1) <= buf \/ buf + WriterApp.w_cap st <= s)
    by (clear - Hdisj0; lia).
destruct (kept_at_bounds ly S Hp W mem md Lam peak _ _ ran s _ HAR Hled0 Hkept0 Hn1) as (Hs4096' & HsC).
assert (Hso : s + (Z.of_nat (length bs) + 1) <= o) by (unfold ASAN_CEIL in HsC; clear - HsC HSPc HSTK' Ho; lia).
assert (Hnfp : forall a, s <= a < s + Z.of_nat (length bs) + 1 -> ~ inFP FP a).
{ intros a Ha. apply (str_notin_fp ly S Hp W mem md Lam peak _ _ ran o buf (WriterApp.w_cap st) s _ HAR Hled0 Hkept0 Hn1
    Hd0' Hcase Hso a). clear - Ha; lia. }
assert (Hcl : ~ YI16.sink_open_fp FP).
{ subst FP. apply sink_closed_pos. unfold prhWriter_cfp, prhWriter_fp.
  destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [Hz0 | Hnz]; constructor; cbn [fst];
    try (clear - Ho HSPc HCEIL0 HSTK'; lia).
  - constructor.
  - unfold ablocks_fp. cbn [map]. constructor; [cbn [fst] | constructor].
    destruct (HLB _ _ (Hcase Hnz)) as (Hk0 & HinB & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR HinB) as (_ & H4096 & _). cbn [fst] in H4096.
    clear - H4096; lia. }
assert (HCSTR3 : cstr W3 mem3 s bs).
{ apply (cstr_from_entryR (wle' SEGS RZ_cf) _ _ FP ly S Hp W mem md _ ly3 S3 Hp3 W3 mem3 md3 _ Lam peak _ _ ran Lam1
    peak1 _ _ ran1 s bs HJ3
    Hled0 Hled1 (proj1 Hcstr0) Hkept0 Hlive1 Hnfp Hcl). }
destruct (str_shadow_at ly3 S3 Hp3 W3 mem3 md3 Lam1 peak1 _ _ ran1 s _ HAR3 Hled1 Hkept1 Hn1) as (HRA3 & HHV3).
destruct (kept_at_loc ly3 S3 Hp3 W3 mem3 md3 Lam1 peak1 _ _ ran1 s _ 0 pos HAR3 Hled1 Hkept1 Hn1 Hin3 ltac:(vm_compute; reflexivity))
  as (Hsapp & HsF).
change (frame_addr ly3 0 pos) with (ly_F ly3 + fs_frame_off 0 pos) in HsF. rewrite HFL3 in HsF.
change (ly_F ly + fs_frame_off 0 pos) with F in HsF. change (fs_frame_bytes 0) with 64 in HsF.
(* the byte s[0] and its shadow byte *)
destruct HCSTR3 as (Hg3 & Hnz3).
assert (H0lt : (0 < length (bs ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
destruct (Hg3 0%nat H0lt) as (Hb0v & Hb0r).
set (c0 := nth 0 (bs ++ [0]) 0) in *. rewrite Z.add_0_r in Hb0v.
assert (Hss : s <= s < s + (Z.of_nat (length bs) + 1)) by lia.
destruct (HRA3 s Hss) as (sv0 & Hsv0 & Hsok0).
idtac "S0-FACTS-DONE".
(* seat s[0]'s shadow address (atom 70), its shadow byte (71) and the byte (72) *)
assert (Ep_11 : ew Ep 11 = Z_to_bv 64 s) by (rewrite Epold, E2E, (EE 11%nat 11%bv) by (lia || reflexivity); exact H11).
assert (Ep_32 : ew Ep 32 = Z_to_bv 64 PS_SB) by (rewrite Epold by lia; exact E2_32).
set (SHS := PS_SB + s / 8).
assert (HSHSv : shadow_of_addr SHADOW_OFF s = SHS) by (unfold shadow_of_addr, SHS, PS_SB; reflexivity).
rewrite HSHSv in Hsv0.
assert (Hsv0r : 0 <= sv0 < 8) by (unfold saddr_ok in Hsok0; clear - Hsok0; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ssp _ =>
  pose proof (st_ok_pi_havoc_hi 70 Ep ssp _ [Z_to_bv 64 SHS; Z_to_bv 64 sv0; Z_to_bv 64 c0] HS
    ltac:(vm_compute; reflexivity)) as HS4 end.
clear HS. rename HS4 into HS.
set (Eq := havoc Ep 70 [Z_to_bv 64 SHS; Z_to_bv 64 sv0; Z_to_bv 64 c0]) in HS.
assert (HEIq : img_env VAL A_LIM Eq) by (subst Eq; apply img_env_havoc; [exact HEIp | cbv; lia]).
assert (Eqold : forall k, (k < 70)%nat -> ew Eq k = ew Ep k) by (intros k Hk; subst Eq; apply ew_havoc_old; exact Hk).
assert (Eqhi : forall k, (73 <= k)%nat -> ew Eq k = ew Ep k) by (intros k Hk; subst Eq; apply ew_havoc_above; cbn; lia).
assert (E70 : ew Eq 70 = Z_to_bv 64 SHS) by (subst Eq; unfold havoc; cbn [ew]; reflexivity).
assert (E71 : ew Eq 71 = Z_to_bv 64 sv0) by (subst Eq; unfold havoc; cbn [ew]; reflexivity).
assert (E72 : ew Eq 72 = Z_to_bv 64 c0) by (subst Eq; unfold havoc; cbn [ew]; reflexivity).
assert (Eq_11 : ew Eq 11 = Z_to_bv 64 s) by (rewrite Eqold by lia; exact Ep_11).
assert (Eq_32 : ew Eq 32 = Z_to_bv 64 PS_SB) by (rewrite Eqold by lia; exact Ep_32).
assert (HSHSr : SHADOW_OFF <= SHS < kHighMemBeg) by (unfold SHS, PS_SB, SHADOW_OFF, kHighMemBeg; clear - Hs; lia).
(* the three facts *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssq _ =>
  pose proof (st_ok_pi_add_fact Eq ssq _ 70 (mkAF PS_SB (PS_SB + 2 ^ 44) 0) HS) as HS5 end.
match type of HS5 with ?P -> _ => assert (HP : P); [|specialize (HS5 HP); clear HP] end.
{ unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E70, unsigned_lit_small by (clear - HSHSr; unfold SHADOW_OFF, kHighMemBeg in *; lia).
  change (2 ^ 0) with 1. rewrite Z.mod_1_r. unfold SHS, PS_SB in *. clear - Hs. repeat split; lia. }
clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssq _ =>
  pose proof (st_ok_pi_add_fact Eq ssq _ 71 (mkAF 0 7 0) HS) as HS5 end.
match type of HS5 with ?P -> _ => assert (HP : P); [|specialize (HS5 HP); clear HP] end.
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E71, unsigned_lit_small by (clear - Hsv0r; lia).
  change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - Hsv0r. repeat split; lia. }
clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssq _ =>
  pose proof (st_ok_pi_add_fact Eq ssq _ 72 (mkAF 0 255 0) HS) as HS5 end.
match type of HS5 with ?P -> _ => assert (HP : P); [|specialize (HS5 HP); clear HP] end.
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E72, unsigned_lit_small by (clear - Hb0r; lia).
  change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - Hb0r. repeat split; lia. }
clear HS. rename HS5 into HS.
(* the shadow declaration of s *)
assert (Hs64 : 0 <= s < 2 ^ 64) by (clear - Hs; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ssq _ =>
  pose proof (st_ok_pi_add_alias Eq ssq _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 0) (SLit 3)) (SOff 32 0)) (SOff 70 0) HS
    (shadow_decl_ok Eq 11 32 70 s PS_SB Eq_11 Hs64 Eq_32 E70)) as HS5 end.
clear HS. rename HS5 into HS.
idtac "S0-SEAT-FACTS".
(* the base values of the state's regions under Eq *)
assert (Ephi : forall k, (67 <= k)%nat -> ew Ep k = ew E2 k).
{ intros k Hk. subst Ep. apply ew_havoc_above. rewrite ?length_map. unfold CLOB. cbn [length]. lia. }
assert (R2q : base_val Eq (Some 2%nat) = spZ regs) by (cbn [base_val]; rewrite Eqold, Epold by lia; exact R2').
assert (R34q : base_val Eq (Some 34%nat) = PS_R (spZ regs))
  by (cbn [base_val]; rewrite Eqold, Epold, E2_34 by lia; apply unsigned_lit_small; lia).
assert (R39q : base_val Eq (Some 39%nat) = F) by (cbn [base_val]; rewrite Eqold, Epold, E2_39 by lia; apply unsigned_lit_small; lia).
assert (R513q : base_val Eq (Some 513%nat) = SHF)
  by (cbn [base_val]; rewrite Eqhi, Ephi, E513 by lia; apply unsigned_lit_small; unfold SHADOW_OFF, kHighMemBeg in HSHFr; lia).
assert (R70q : base_val Eq (Some 70%nat) = SHS)
  by (cbn [base_val]; rewrite E70; apply unsigned_lit_small; unfold SHADOW_OFF, kHighMemBeg in HSHSr; lia).
assert (R11q : base_val Eq (Some 11%nat) = s) by (cbn [base_val]; rewrite Eq_11; apply unsigned_lit_small; lia).
assert (HLOC : (s + (Z.of_nat (length bs) + 1) <= kLowShadowBeg \/ kHighMemBeg <= s) /\
  (s + (Z.of_nat (length bs) + 1) <= F \/ F + 64 <= s) /\ s + (Z.of_nat (length bs) + 1) <= ASAN_CEIL /\
  SHADOW_OFF + 512 <= SHF /\ SHF + 8 <= kHighMemBeg /\ SHADOW_OFF <= SHS < kHighMemBeg /\
  SHF = SHADOW_OFF + F / 8 /\ SHS = SHADOW_OFF + s / 8 /\ F = 32 * (F / 32) /\ 4096 <= F /\
  (F + 64 <= kLowShadowBeg \/ kHighMemBeg <= F) /\ ASAN_CEIL + 208 <= spZ regs /\
  spZ regs - 208 <= PS_R (spZ regs) <= spZ regs - 192).
{ unfold ASAN_CEIL in *. split; [exact Hsapp|]. split; [exact HsF|]. split; [exact HsC|].
  split; [exact (proj1 HSHFr)|]. split; [exact (proj2 HSHFr)|]. split; [exact HSHSr|].
  split; [rewrite HSHF; reflexivity|]. split; [reflexivity|]. split; [exact HFq|]. split; [lia|].
  split; [unfold kLowShadowBeg, kHighMemBeg in HFa1 |- *; lia|]. split; [lia | exact (proj1 HR)]. }
idtac "S0-LOC".
destruct HLOC as (HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & HL7 & HL8 & HL9 & HL10 & HL11 & HL12 & HL13).
rewrite <- restrict_mkst_fx in HS.
norm_ss HS.
(* s[0]'s shadow byte *)
add_reg HS (YP09.mkRegion (Some 70%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 71 0))]).
{ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  rewrite R70q. pose proof HL6 as HL6'. unfold SHADOW_OFF, kHighMemBeg in HL6'.
  split; [clear - HL6'; lia|]. split; [clear - HL6'; lia|]. split; [intros oo Hoo; clear - Hoo; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS Eq _ SHS 0 1 (SOff 71 0) sv0);
    [cbn [sv_denot]; rewrite E71, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem1_of_aview _ _ _ _ Hsv0). }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite ?R513q, ?R39q, ?R34q, ?R2q, ?R70q.
  unfold ASAN_CEIL, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  clear - HL1 HL2 HL3 HL4 HL5 HL6 HL7 HL8 HL9 HL10 HL11 HL12 HL13 Hs HCEIL0.
  repeat split; lia. }
norm_ss HS.
(* the byte s[0] *)
add_reg HS (YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 72 0))]).
{ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
  rewrite R11q. split; [clear - Hs; lia|]. split; [clear - Hs; lia|]. split; [intros oo Hoo; clear - Hoo; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS Eq _ s 0 1 (SOff 72 0) c0);
    [cbn [sv_denot]; rewrite E72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact Hb0v. }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite ?R513q, ?R39q, ?R34q, ?R2q, ?R70q, ?R11q.
  unfold ASAN_CEIL, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  clear - HL1 HL2 HL3 HL4 HL5 HL6 HL7 HL8 HL9 HL10 HL11 HL12 HL13 Hs HCEIL0.
  repeat split; lia. }
norm_ss HS.
idtac "S0-REGIONS".
(* the env's values of the registers the joins read *)
assert (Q2 : ew Eq 2 = getr regs 2) by (rewrite Eqold, Epold, E2E, (EE 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (Q3 : ew Eq 3 = getr regs 3) by (rewrite Eqold, Epold, E2E, (EE 3%nat 3%bv) by (lia || reflexivity); reflexivity).
assert (Q4 : ew Eq 4 = getr regs 4) by (rewrite Eqold, Epold, E2E, (EE 4%nat 4%bv) by (lia || reflexivity); reflexivity).
assert (Q10 : ew Eq 10 = getr regs 10)
  by (rewrite Eqold, Epold, E2E, (EE 10%nat 10%bv) by (lia || reflexivity); reflexivity).
assert (Q34 : ew Eq 34 = Z_to_bv 64 (PS_R (spZ regs))) by (rewrite Eqold, Epold by lia; exact E2_34).
assert (Q39 : ew Eq 39 = Z_to_bv 64 F) by (rewrite Eqold, Epold by lia; exact E2_39).
assert (Q513 : ew Eq 513 = Z_to_bv 64 SHF) by (rewrite Eqhi, Ephi by lia; exact E513).
cbn [app] in HCOM1. rename HCOM1 into HCOMc.
(* ---- the rest is ONE proof-mode command: its local closures are segment A's leaves, which both shadow paths reach
   (proof-mode tactics may name the hypotheses of the goal; an Ltac definition may not) ---- *)
let awrRun := fun _ => (let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); cbn [In ss_mem] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?R513q, ?R39q, ?R34q, ?R2q, ?R70q, ?R11q in Ha;
      first [ clear - Ha; lia
            | unfold awr_byte; left; clear - Ha HR Hd0 HSTK'; lia
            | unfold awr_byte, in_frames; right; right; right; exists 0, pos; split; [left; reflexivity|];
              unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8;
              change (frame_addr ly3 0 pos) with (ly_F ly3 + fs_frame_off 0 pos); rewrite HFL3;
              change (ly_F ly + fs_frame_off 0 pos) with F;
              first [left; clear - Ha; lia | right; rewrite <- HSHF; clear - Ha; lia] ] | ]);
  try destruct Hin) in
let nwrQ := fun _ => (let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros a (r & Hin & Hx); cbn [In ss_mem] in Hin;
  change (x_R XR) with (PS_R (spZ regs)); change (x_F XR pos) with F;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite ?R513q, ?R39q, ?R34q, ?R2q, ?R70q, ?R11q in Hx;
      first [ clear - Hx; lia
            | left; clear - Hx; lia
            | right; left; clear - Hx; lia
            | right; right; clear - Hx HSHFr; unfold SHADOW_OFF, kHighMemBeg in *; lia ] | ]);
  try destruct Hin) in
let pcom := fun _ => (let H := fresh "HCOMn" in
  eassert (H : ps_commonR (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _);
  [ eapply ps_common_frameR; [exact Hpre | exact HCOMc | exact HJ3 | exact HPM | eassumption | nwrQ ()] | ];
  clear HCOMc; rename H into HCOMc) in
let pregs := fun _ => (let G := fresh "G" in
  first [ prreg HS (2%bv : bv 5) G; rename G into G2 | idtac ];
  let G := fresh "G" in first [ prreg HS (3%bv : bv 5) G; rename G into G3 | idtac ];
  let G := fresh "G" in first [ prreg HS (4%bv : bv 5) G; rename G into G4 | idtac ];
  let G := fresh "G" in first [ prreg HS (8%bv : bv 5) G; rename G into G8 | idtac ];
  let G := fresh "G" in first [ prreg HS (9%bv : bv 5) G; rename G into G9 | idtac ];
  let G := fresh "G" in first [ prreg HS (18%bv : bv 5) G; rename G into G18 | idtac ];
  let G := fresh "G" in first [ prreg HS (19%bv : bv 5) G; rename G into G19 | idtac ];
  let G := fresh "G" in first [ prreg HS (20%bv : bv 5) G; rename G into G20 | idtac ];
  let G := fresh "G" in first [ prreg HS (21%bv : bv 5) G; rename G into G21 | idtac ];
  let G := fresh "G" in first [ prreg HS (22%bv : bv 5) G; rename G into G22 | idtac ];
  let G := fresh "G" in first [ prreg HS (23%bv : bv 5) G; rename G into G23 | idtac ];
  let G := fresh "G" in first [ prreg HS (24%bv : bv 5) G; rename G into G24 | idtac ];
  let G := fresh "G" in first [ prreg HS (25%bv : bv 5) G; rename G into G25 | idtac ];
  let G := fresh "G" in first [ prreg HS (26%bv : bv 5) G; rename G into G26 | idtac ]) in
(* c0 = 0: the empty string, through + 0x2c4 (`mv s4, s2`) to the tail join (+ 0x2c8) *)
let leafZ := fun _ => (idtac "C0Z";
  lazymatch goal with Hc : branch_taken BC_EQ _ _ = true |- _ =>
    rewrite branch_eq_U, U_SLit, (U_atom Eq 72 c0 E72) in Hc by (clear - Hb0r; lia);
    change (zcanon 0) with 0 in Hc; apply Z.eqb_eq in Hc;
    pose proof (ps_c0_nil bs c0 Hnz3 eq_refl Hc) as Hbs end;
  pnt_run_to_inv NTRUNTOIR HS HJ3 HPM (AF_put_string + 712);
  [ awrRun ()
  | pcom (); pmkst HS; pregs ();
    lazymatch goal with |- context [BASE + ?k] =>
      replace k with (AF_put_string + 712) by (unfold AF_put_string; rewrite (proj2 B_entry_put_string);
        vm_compute; reflexivity) end;
    eapply (KT pos 0%nat [[34]] ly3 S3 Hp3 W3); unfold ps_tail;
    split; [exact HCOMc|];
    split; [lia|];
    split; [change (x_bs XR) with bs; rewrite Hbs; reflexivity|];
    split; [rewrite G2, Q34; reflexivity|];
    split; [rewrite G3, Q3; reflexivity|];
    split; [rewrite G4, Q4; reflexivity|];
    split; [rewrite G8, Q2; change (x_sp XR) with (spZ regs); unfold w64, spZ; rewrite Z_to_bv_bv_unsigned;
            reflexivity|];
    split; [rewrite G9, Q34; reflexivity|];
    split; [rewrite G19, Q10; exact H10|];
    split; [rewrite G18, Eq_11; unfold w64; f_equal; change (x_s XR) with s; cbn [Z.of_nat]; lia|];
    split; [rewrite G20, Eq_11; unfold w64, x_n; f_equal; change (x_bs XR) with bs; change (x_s XR) with s;
            rewrite Hbs; cbn [length Z.of_nat]; lia|];
    split; [rewrite G21, Q39; reflexivity|];
    split; [rewrite G22, Q513; reflexivity|];
    rewrite G24, Q39; reflexivity ]) in
(* c0 <> 0: the literal table and the loop registers, to the loop head (+ 0x180) with i = j = 0 *)
let leafNZ := fun _ => (idtac "C0NZ";
  lazymatch goal with Hc : branch_taken BC_EQ _ _ = false |- _ =>
    rewrite branch_eq_U, U_SLit, (U_atom Eq 72 c0 E72) in Hc by (clear - Hb0r; lia);
    change (zcanon 0) with 0 in Hc; apply Z.eqb_neq in Hc;
    destruct (ps_c0_cons bs c0 Hnz3 eq_refl Hc) as (Hlen0 & Hc0b) end;
  pnt_run_to_inv NTRUNTOIR HS HJ3 HPM (AF_put_string + 384);
  [ awrRun ()
  | pcom (); pmkst HS; pregs ();
    (* the R block of the end state (region 4) and the literals' ranges *)
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict (w_H W3) ?msx) =>
      let rv := eval vm_compute in (nth_error (ss_mem ssx) 4) in
      lazymatch rv with Some ?rg =>
        pose proof (st_ok_region_nth SEGS Eq (abs_ss VAL ssx) _ 4 rg HS ltac:(vm_compute; reflexivity)) as HR34 end end;
    cbn [ms_mem restrict] in HR34;
    pose proof HCOMc as (HJc & _ & _ & _ & _ & _ & _ & HROc' & _); pose proof (ajxR_ar HJc) as HARc';
    destruct (HLIT85 _ _ _ _ _ _ HARc' HROc') as ((_ & L85a & L85b & _) & _);
    destruct (HLIT87 _ _ _ _ _ _ HARc' HROc') as ((_ & L87a & L87b & _) & _);
    destruct (HLIT91 _ _ _ _ _ _ HARc' HROc') as ((_ & L91a & L91b & _) & _);
    destruct (HLIT93 _ _ _ _ _ _ HARc' HROc') as ((_ & L93a & L93b & _) & _);
    destruct (HLIT89 _ _ _ _ _ _ HARc' HROc') as ((_ & L89a & L89b & _) & _);
    assert (UR34 : bv_unsigned (ew Eq 34) = PS_R (spZ regs)) by (pose proof R34q as Hx; cbn [base_val] in Hx; exact Hx);
    assert (HeF : sv_denot Eq (SOff 39 0) = Z_to_bv 64 F)
      by (cbn [sv_denot]; rewrite Q39, unsigned_lit_small, Z.add_0_r by (clear - HF4096 HFceil HCEIL0; lia); reflexivity);
    assert (HeL : forall k, sv_denot Eq (SOff 243 (ps_lit k)) = Z_to_bv 64 (ps_str k))
      by (intros k; cbn [sv_denot]; rewrite (HEIq 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); unfold ps_str; reflexivity);
    lazymatch goal with |- context [BASE + ?k] =>
      replace k with (AF_put_string + 384) by (unfold AF_put_string; rewrite (proj2 B_entry_put_string);
        vm_compute; reflexivity) end;
    eapply (KH pos 0%nat 0%nat [[34]] ly3 S3 Hp3 W3); unfold ps_head;
    split; [exact HCOMc|];
    split; [change (x_bs XR) with bs; lia|];
    split; [reflexivity|];
    (* ps_lregs, one nested conjunction *)
    split;
    [ unfold ps_lregs;
      split; [rewrite G2, Q34; reflexivity|];
      split; [rewrite G3, Q3; reflexivity|];
      split; [rewrite G4, Q4; reflexivity|];
      split; [rewrite G8, Q2; change (x_sp XR) with (spZ regs); unfold w64, spZ; rewrite Z_to_bv_bv_unsigned;
              reflexivity|];
      split; [rewrite G9, Q34; reflexivity|];
      split; [rewrite G19, Q10; exact H10|];
      split; [rewrite G21, Q39, unsigned_lit_small by (clear - HF4096 HFceil HCEIL0; lia); reflexivity|];
      split; [rewrite G22, Q513; reflexivity|];
      rewrite G23, Eq_32; reflexivity
    |];
    split; [rewrite G18, Eq_11; unfold w64; f_equal; change (x_s XR) with s; cbn [Z.of_nat]; lia|];
    split; [rewrite G20, Eq_11, unsigned_lit_small by (clear - Hs; lia); unfold w64; f_equal;
            change (x_s XR) with s; cbn [Z.of_nat]; lia|];
    split; [rewrite G24, Eq_11; unfold w64; f_equal; change (x_s XR) with s; cbn [Z.of_nat]; lia|];
    split; [rewrite G25, E72, Hc0b; reflexivity|];
    (* ps_rblock, the last conjunct *)
    unfold ps_rblock;
    change (x_R XR) with (PS_R (spZ regs)); change (x_F XR pos) with F;
    split; [exact (ps_rword _ _ _ _ _ 8 (SOff 39 0) F HR34 UR34
              ltac:(vm_compute; repeat first [left; reflexivity | right]) HeF ltac:(clear - HF4096 HFceil HCEIL0; lia))|];
    split; [exact (ps_rword _ _ _ _ _ 16 (SOff 39 0) F HR34 UR34
              ltac:(vm_compute; repeat first [left; reflexivity | right]) HeF ltac:(clear - HF4096 HFceil HCEIL0; lia))|];
    split; [exact (ps_rword _ _ _ _ _ 24 (SOff 243 (ps_lit 91%nat)) (ps_str 91%nat) HR34 UR34
              ltac:(vm_compute; repeat first [left; reflexivity | right]) (HeL 91%nat)
              ltac:(clear - L91a L91b HCEIL0; lia))|];
    split; [exact (ps_rword _ _ _ _ _ 32 (SOff 243 (ps_lit 89%nat)) (ps_str 89%nat) HR34 UR34
              ltac:(vm_compute; repeat first [left; reflexivity | right]) (HeL 89%nat)
              ltac:(clear - L89a L89b HCEIL0; lia))|];
    split; [exact (ps_rword _ _ _ _ _ 40 (SOff 243 (ps_lit 87%nat)) (ps_str 87%nat) HR34 UR34
              ltac:(vm_compute; repeat first [left; reflexivity | right]) (HeL 87%nat)
              ltac:(clear - L87a L87b HCEIL0; lia))|];
    split; [exact (ps_rword _ _ _ _ _ 48 (SOff 243 (ps_lit 85%nat)) (ps_str 85%nat) HR34 UR34
              ltac:(vm_compute; repeat first [left; reflexivity | right]) (HeL 85%nat)
              ltac:(clear - L85a L85b HCEIL0; lia))|];
    exact (ps_rword _ _ _ _ _ 56 (SOff 243 (ps_lit 93%nat)) (ps_str 93%nat) HR34 UR34
              ltac:(vm_compute; repeat first [left; reflexivity | right]) (HeL 93%nat)
              ltac:(clear - L93a L93b HCEIL0; lia)) ]) in
(* run: s's NULL trap (+ 0x114, decided: s's seat facts) and s[0]'s shadow check, to its branch (+ 0x124) *)
pnt_run_to_inv NTRUNTOIR HS HJ3 HPM (AF_put_string + 384);
[ awrRun ()
| pcom (); idtac "S0-RUN-DONE"; pnt_branch BRR HS;
  [ (* the shadow byte is nonzero: the slow path (+ 0x390), the partial granule's test (+ 0x394) *)
    lazymatch goal with Hc : branch_taken BC_NE _ _ = true |- _ =>
      rewrite branch_ne_U, U_SLit, (U_atom Eq 71 sv0 E71) in Hc by (clear - Hsv0r; lia);
      change (zcanon 0) with 0 in Hc; apply Bool.negb_true_iff, Z.eqb_neq in Hc; rename Hc into Hsvnz end;
    pnt_run_to_inv NTRUNTOIR HS HJ3 HPM (AF_put_string + 296);
    [ awrRun ()
    | pcom (); idtac "S0-NZ-RUN-DONE"; pnt_branch BRR HS;
      [ (* (s & 7) < the shadow byte: the load at + 0x128 *)
        pnt_run_to_inv NTRUNTOIR HS HJ3 HPM (AF_put_string + 384);
        [ awrRun () | pcom (); pnt_branch BRR HS; [leafZ () | leafNZ ()] ]
      | (* the report branch (+ 0x398, __asan_report_load1) is not taken: s[0] is addressable *)
        exfalso;
        assert (Hlt : s mod 8 < sv0) by (unfold saddr_ok in Hsok0; clear - Hsok0 Hsvnz; lia);
        lazymatch goal with Hc : branch_taken BC_LT _ _ = false |- _ =>
          rewrite (ps_slow_lt Eq s sv0 Eq_11 E71) in Hc by (clear - Hs Hsv0r Hsvnz Hlt; lia); discriminate Hc end ] ]
  | (* the shadow byte is zero: the load at + 0x128 *)
    pnt_run_to_inv NTRUNTOIR HS HJ3 HPM (AF_put_string + 384);
    [ awrRun () | pcom (); pnt_branch BRR HS; [leafZ () | leafNZ ()] ] ] ].
Qed.


End h.
End f.
End d.
