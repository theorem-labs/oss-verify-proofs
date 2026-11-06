(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_string of fuzz_preset's asan-ubsan image (B 0x87208, 49 instructions; preset_file.c
   :406-411): the kit's text tpj_string_specX
   (lib/A/PRH_FnPj.v: ENTRY-keyed, no DW, the run keyed on ReaderRes.jr_strtod, the entry premise
   PRH_Base.prh_cons_from, the run premise prh_run_at .. (prhPj_string_evs |cs| cnt fail), the post conjunct
   DEAD-PJSTRING `cnt <> fail -> a <> 0` and the exact advance rp_i + |evs| on success or the chosen failure; the
   live premise guarded by the call's success flag, `cnt <> fail -> blocks_bytes S + LIVE_pj_string |cs| <= LIVE_MAX`,
   handed to fuzz_strdup's equally guarded one; its
   fpre ends in FRM0-ENTRY; a run of at most 4 calls, from which the walk pays fuzz_strdup's hull budget) at image B,
   composed from the segment files over the cuts of
   lib/B/Prog/pj_string_defs.v. No twin: the kit's text is proved as stated.
   proves pj_string at image B (kind: composition): the walk proves its own post pjs_Q at the return (the position
   from fuzz_strdup's post implication, lib/A/PRH_FnAlloc.v tfuzz_strdup_specX, applied at the entry position,
   and the grant from its OUTCOME conjunct at the same position, in pj_string_seg_call.v); pjs_Q_K0_of_Q turns it into
   the kit's post under the kit's run and prh_cons_from premises;
   pjs_compose turns the entry segment into the kit's text at the strtod model ReaderRes.jr_strtod, deriving fuzz_strdup's
   live-set premises (pjs_cnt) from the text's model-run position by counts_of_room_pos_rl (lib/Spec/PresetRoomCounts.v);
   tpj_string_B_holds chains pj_string_seg_ent.v, pj_string_seg_call.v and pj_string_seg_ep.v. Supply of the run
   premise at check_round_trip's entry: pj_string_evs_supply_rt (over the kit's prhPj_string_evs_supply).
   THE cf_head = 0 HOLE (this walk's finding against a3bdeca3920, now in the text as prh_head_wide): with cf_head < 8 -
   in particular cf_head = 0, which CfParams admits for a harness that hides no head - v may start a live harness block
   (prhPj_slot's first case with v = a), and pj_string's 56-byte memset of the node zeroes the block's head word, which
   prh_ledger reads (prh_hblock's `val_mem .. (a - cf_head) 8 k`): the post's ledger is then false. The same finding
   in pj_free: lib/B/Prog/pj_free_top.v. The kit's text
   takes prh_head_wide (PRH_Base.v `8 <= cf_head`); at preset's instance (cf_head = 16) it is
   lib/B/PALibB.v's exvi_eh_head (= CfParamsPreset.preset_head_wide).
   Theorems and their Section hypotheses (callee texts in the kit's forms, or named stand-ins; none proved here):
     tpj_string_B_holds (generic B, ARx, CfParams):
       MEMSET   YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (pa_sigma AS___asan_memset) (the m-form intrinsic text);
       STRDUP   tfuzz_strdup_specX B ARx SK (the text, lib/A/PRH_FnAlloc.v:517-558 at d607d12e4b0f; never unfolded,
                its post read by name);
       LAWS     AR_laws_x SEGS B ARx cf_head (the kit's allocator laws);
       PAL      PALib B (the unit's image binding of B; stand-in as in FuzzFreeB.v, owner a Theorem Labs lane);
       GLIT     pjs_g_lit B (pj_string_defs.v: G-Pj2, the "" literal's image facts, RESTATED 2026-10-29 to the one
                byte read; the old text is FALSE at TfibB: pjs_g_lit_unsat_B);
       GSH      pjs_g_lit_sh ARx (the state fact split off the old text: the image's shadow map is visible);
       HULL     pjs_g_hull (pj_string_defs.v: the hull budget at a run position, which pays fuzz_strdup's hull
                premise from the text's position; at preset's instance pjs_hull_preset, from lib/A/PresetHullPay.v
                hull_budget_of_room_pos).
     tpj_string_B_holds_kit: GLIT from TS : YF0m.TfibSyms B (the kit's binding record as the lib/AU consumers take
       it, lib/AU/AGic.v:35) by pjs_g_lit_of_tfib (image B's generated Tfib_owned_static / TFIB_ERRNO /
       Tfib_const_shadow, lib/Reusable/YF0m.v blob 04da606c5ad9, by computation); GSH is img_shadow_vis_cf
       (the Definition at lib/Reusable/YGcfAmx2.v, in this ARx form).
     tpj_string_B_preset: at preset's instance - CfParams_preset (cf_head = 16), B := YD2l.TfibB, ARx :=
       YG0ncf.ARcf rsegs TfibB - with PAL, LAWS and TS discharged by lib/B/PALibB.v (blob 23e2b7f0a8c8)
       exvi_eh_palib / exvi_eh_laws and YD2l.TfibB_syms, and img_shadow_vis_cf by pjs_g_lit_sh_B (the cover check of
       image B's shadow lists), HULL by pjs_hull_preset; left: MEMSET, STRDUP (callee texts at the instance). The kit's
       premises prh_head_wide,
       prh_cons_from and the run premise stay in the text the callers discharge (exvi_eh_head; pj_string_evs_supply_rt).
   Pins (checked against this tree's lib/B/Listing_prog.v, image B sha256 d663f82d7f48, slots 5839 .. 5887, and
   against the unstripped twin's disassembly): entry 0x87208 (PAImg_prog.v:502 B_entry_pj_string, slot 5839;
   __asan_memset at :105, fuzz_strdup at :47), the calls at +0x30 / +0x68
   (__asan_memset 0x5296c, fuzz_strdup 0x860e0), the return sites +0x34 / +0x6c, the `bnez s1` +0x58 and its target
   +0x64, the literal's auipc / addi +0x5c / +0x60 and the literal 0x21420 (A_OBJ 2 + 0x11420), the ret +0xa4: 13
   addresses, 0 mismatches. ADDRESS numerals only in Section g, the measured constants of the refutation. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l YImgShadowCover YImgShadowCoverCf.
(* the image-B instance facts (one home), and the live-set bounds at a model-run position: Required, cited
   by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_string_defs pj_string_seg_ent
  pj_string_seg_call pj_string_seg_ep.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* fpostWm is monotone in its Q *)
Lemma pjs_fpostWm_mono : forall (STK d : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (Q Q' : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (W' : world SEGS) (c' : config),
  (forall ly' S' Hp' W'' regs' mem' md', Q ly' S' Hp' W'' regs' mem' md' -> Q' ly' S' Hp' W'' regs' mem' md') ->
  fpostWm (PA := PA) B ARx SK STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWm (PA := PA) B ARx SK STK d FP regs ly S Hp W mem md Q' W' c'.
Proof.
intros STK d FP regs ly S Hp W mem md Q Q' W' c' HQ HF.
unfold fpostWm, fpostW, fQmn in *.
destruct HF as (ly' & S' & Hp' & regs' & mem' & md' & k & E & J & K & P & HQ0 & HM).
exists ly', S', Hp', regs', mem', md', k.
split; [exact E|]. split; [exact J|]. split; [exact K|]. split; [exact P|].
split; [exact (HQ _ _ _ _ _ _ _ HQ0) | exact HM].
Qed.

(* the walk's post gives the text's under the run and prh_cons_from premises: on success prh_alloc_post's third arm has
   cnt <> fail, so prhPj_string_evs is [HMal (|cs| + 1 + cf_head)], prh_run_at gives the event and the position is
   S rp_i = rp_i + 1; at the chosen failure (cnt = fail) the outcome is 0 (the first arm; the other two have
   cnt <> fail), the list is [] and the position is rp_i = rp_i + 0; the history is the one fuzz_strdup's post
   implication gave. DEAD-PJSTRING is the walk's own DEAD conjunct under the two premises. *)
Lemma pjs_Q_K0_of_Q : forall en, pjs_run en -> pjs_cons en -> forall ly' S' Hp' W' regs' mem' md',
  pjs_Q B en ly' S' Hp' W' regs' mem' md' -> pjs_Q_K0 B en ly' S' Hp' W' regs' mem' md'.
Proof.
intros en HRUN HCONS ly' S' Hp' W' regs' mem' md' (HR & a & P0 & P1 & PD & HP & HS & HF).
split; [exact HR|]. exists a. split; [exact HP|].
split; [intros Hc; exact (PD Hc HRUN HCONS)|].
split; [|split; [exact HS | exact HF]].
intros Hc. unfold pjs_run in HRUN. unfold prhPj_string_evs in HRUN |- *.
destruct (Z.eq_dec (js_cnt en) (js_fail en)) as [E | E].
- assert (Ha : a = 0).
  { destruct HP as [(_ & A & _) | [(Hne & _) | (Hne & _)]]; [exact A | exact (False_ind _ (Hne E)) |
      exact (False_ind _ (Hne E))]. }
  rewrite (proj2 (Z.eqb_eq _ _) E). cbn [length]. rewrite Nat.add_0_r.
  exact (P0 Ha).
- destruct Hc as [Ha | Hc]; [|exact (False_ind _ (E Hc))].
  rewrite (proj2 (Z.eqb_neq _ _) E) in HRUN |- *. cbn [length]. rewrite Nat.add_1_r.
  exact (P1 Ha (proj1 (prh_run_at_one _ _ _ _ _) HRUN)).
Qed.

(* THE COMPOSITION INTO THE TEXT: the premises but prh_cons_from and the run premise are pjs_pre of the entry
   record at the strtod model ReaderRes.jr_strtod (by conversion), the entry segment's post is pjs_FIN, and the run
   and prh_cons_from premises turn it into the post; fuzz_strdup's live-set premises at the entry state come from
   the text's position (counts_of_room_pos_rl) *)
Theorem pjs_compose : forall CTX0, pjs_seg_entry (SK := SK) B ARx CTX0 ->
  tpj_string_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK CTX0.
Proof.
intros CTX0 SEG rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own
  H1 H2 H3 H4 HLOS HCONS H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HRUN.
set (en := MkPjsEnt ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own ReaderRes.jr_strtod rp_x rp_os
  rp_i rp_H0 rp_hist).
eapply SRr_mono.
{ exact (SEG en
    (conj H1 (conj H2 (conj H3 (conj H4 (conj HLOS (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
     (conj H12 (conj H13 H14))))))))))))))
    (PresetRoomCounts.counts_of_room_pos_rl ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S H4)). }
intros W' c' _ HF.
exact (pjs_fpostWm_mono _ _ _ _ _ _ _ _ _ _ _ _ W' c' (pjs_Q_K0_of_Q en HRUN HCONS) HF).
Qed.

(* the callee texts and the stand-ins the walk rests on *)
Hypothesis MEMSET : YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (@pa_sigma _ B_prog_listing PA AS___asan_memset).
Hypothesis STRDUP : tfuzz_strdup_specX (PA := PA) B ARx SK.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
(* MARKED image fact G-Pj2 (pj_string_defs.v pjs_g_lit, restated 2026-10-29: the one byte read; instance witness
   pjs_g_lit_B) and the state fact split off it (pjs_g_lit_sh; instance witness pjs_g_lit_sh_B at ARcf rsegs TfibB) *)
Hypothesis GLIT : pjs_g_lit B.
Hypothesis GSH : pjs_g_lit_sh ARx.
(* the hull budget at a run position (pj_string_defs.v pjs_g_hull; instance witness pjs_hull_preset) *)
Hypothesis HULL : @pjs_g_hull cp.

(* pj_string at image B: the kit's tpj_string_specX *)
Theorem tpj_string_B_holds : forall CTX0,
  tpj_string_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK CTX0.
Proof.
intros CTX0. apply pjs_compose.
exact (pjs_seg_entry_holds B ARx LAWS PAL CTX0 (conj MEMSET STRDUP) GLIT GSH
  (pjs_seg_C1_holds B ARx LAWS HULL CTX0 (conj MEMSET STRDUP) (pjs_seg_C2_holds B ARx LAWS CTX0))).
Qed.
End c.

(* ---- THE OLD LITERAL PREMISE AND ITS REFUTATION AT THE REAL INSTANCE (kind-A vacuity; the image-A twin is
   S6PalLitRefute.v, blob eceb508ec279). pjs_g_lit_old_txt is pj_string_defs.v's pjs_g_lit at 39b77f9f3eda, verbatim over its Section's B and
   ARx. At YD2l.TfibB: PJS_LIT = 0x21420 (pjs_lit_B), and PJS_LIT + 1 lies in an owned-static range, ASan's redzone after
   the 1-byte global (pjs_lit_owned_B), so the old text is FALSE for every allocator relation (pjs_g_lit_unsat_B), and
   every theorem that took it was VACUOUS at the instance. The facts are closed goals decided by vm_compute; this
   section states the measured constants (the only ADDRESS numerals of this file). ---- *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Definition pjs_g_lit_old_txt (B : asyms)
    (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop) : Prop :=
  (forall a, PJS_LIT <= a < PJS_LIT + 8 ->
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
  (forall ly, In (z1 (ANum (shadow_addr PJS_LIT)) 1) (as_const B ly)) /\
  (forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
     aview SEGS (w_H W) mem (shadow_addr a) <> None).

(* the old route to it (statement unchanged, over the old text): from pal_rom_ok's form, which is FALSE at TfibB
   (lib/B/Prog/literal_inst.v blob 574383becb4d:
   pal_rom_ok_false_B); no theorem of this walk uses it any more *)
Lemma pjs_g_lit_of_kit : forall (B : asyms)
  (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop),
  (forall a, in_rom SEGS a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  (forall ly, In (z1 (ANum (shadow_addr PJS_LIT)) 1) (as_const B ly)) ->
  (forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
     aview SEGS (w_H W) mem (shadow_addr a) <> None) ->
  pjs_g_lit_old_txt B ARx.
Proof.
intros B ARx ROM CELL VIS. split; [|split; [exact CELL | exact VIS]].
intros a Ha. apply ROM.
assert (R : existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? PJS_LIT) &&
  (PJS_LIT + 8 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS = true) by (vm_compute; reflexivity).
apply existsb_exists in R as (sg & Hin & Hb). apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
exists sg. split; [exact Hin|]. split; [destruct (seg_writable sg); [discriminate H1 | reflexivity]|].
apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

(* (a) the literal's address at the instance *)
Lemma pjs_lit_B : PJS_LIT = 0x21420.
Proof. vm_compute. reflexivity. Qed.

(* (b) the literal's second byte is owned-static at the instance: the row (0x21421, 31) of image B's generated
   Tfib_owned_static (lib/Reusable/YF0m.v, TfibB's as_owned_static, YD2l.v:34) *)
Lemma pjs_lit_owned_B : In (0x21421, 31) YF0m.Tfib_owned_static /\
  Exists (in_zr (PJS_LIT + 1)) (as_owned_static YD2l.TfibB).
Proof.
assert (H : existsb (fun r => (fst r =? 0x21421) && (snd r =? 31)) YF0m.Tfib_owned_static = true)
  by (vm_compute; reflexivity).
apply existsb_exists in H as ([lo len] & Hin & Hr). apply andb_prop in Hr as [H1 H2].
apply Z.eqb_eq in H1, H2. cbn [fst snd] in H1, H2. subst lo len.
split; [exact Hin|]. rewrite pjs_lit_B.
apply Exists_exists. exists (0x21421, 31). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* (c) the old text is false at the real instance, for every allocator relation *)
Lemma pjs_g_lit_unsat_B : forall ARx, ~ pjs_g_lit_old_txt YD2l.TfibB ARx.
Proof.
intros ARx (HB & _).
destruct (HB (PJS_LIT + 1) ltac:(lia)) as (Hown & _).
exact (Hown (proj2 pjs_lit_owned_B)).
Qed.
End g.

(* the literal's const shadow cell from image B's generated table: ts_const, then the row by value *)
Lemma pjs_lit_cell_of_tfib : forall B, YF0m.TfibSyms B ->
  forall ly, In (z1 (ANum (shadow_addr PJS_LIT)) 1) (as_const B ly).
Proof.
intros B TS ly. rewrite (YF0m.ts_const B TS ly). unfold YF0m.Tfib_const.
apply in_or_app. right. apply in_or_app. right.
let a := eval vm_compute in (shadow_addr PJS_LIT) in change (shadow_addr PJS_LIT) with a.
unfold YF0m.Tfib_const_shadow.
repeat (first [left; reflexivity | right]).
Qed.

(* ---- THE RESTATED LITERAL PREMISE (pj_string_defs.v pjs_g_lit): from the kit's binding record, and its INSTANCE
   WITNESS at YD2l.TfibB; the state fact pjs_g_lit_sh's witness at ARcf rsegs TfibB is in Section p ---- *)
(* the byte read is not owned-static in image B's generated table *)
Lemma pjs_lit_not_owned_tfib : ~ Exists (in_zr PJS_LIT) YF0m.Tfib_owned_static.
Proof.
rewrite pjs_lit_B.
assert (Hb : forallb (fun r => negb ((fst r <=? 0x21420) && (0x21420 <? fst r + snd r))) YF0m.Tfib_owned_static = true)
  by (vm_compute; reflexivity).
intros HE. apply Exists_exists in HE as (r & Hr & Hin). rewrite forallb_forall in Hb. specialize (Hb r Hr).
unfold in_zr in Hin. destruct Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in Hb.
discriminate Hb.
Qed.

Lemma pjs_g_lit_of_tfib : forall B, YF0m.TfibSyms B -> pjs_g_lit B.
Proof.
intros B TS. unfold pjs_g_lit. rewrite (YF0m.ts_owned B TS), (YF0m.ts_errno B TS).
split; [exact pjs_lit_not_owned_tfib|]. split; [|exact (pjs_lit_cell_of_tfib B TS)].
rewrite pjs_lit_B. unfold YF0m.TFIB_ERRNO. lia.
Qed.

(* the INSTANCE WITNESS of the restated text at the real image binding *)
Lemma pjs_g_lit_B : pjs_g_lit YD2l.TfibB.
Proof. exact (pjs_g_lit_of_tfib YD2l.TfibB YD2l.TfibB_syms). Qed.

(* the cover check of image B's shadow lists over the image range (the A twin: A/AImgShadowVis.v) *)
Lemma pjs_img_shadow_cover_B :
  YImgShadowCover.img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow IMG_LO_B IMG_TOP_B = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- the literal's facts from the kit's binding record (pjs_g_lit_of_tfib) and the named state fact ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis MEMSET : YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (@pa_sigma _ B_prog_listing PA AS___asan_memset).
Hypothesis STRDUP : tfuzz_strdup_specX (PA := PA) B ARx SK.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
(* the state fact pjs_g_lit_sh at ARx (YGcfAmx2.v img_shadow_vis_cf, in this ARx form); at preset's
   instance it is pjs_g_lit_sh_B *)
Hypothesis img_shadow_vis_cf : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the kit's binding of B to image B's generated tables, as the lib/AU consumers take it (AU/AGic.v:35) *)
Hypothesis TS : YF0m.TfibSyms B.
Hypothesis HULL : @pjs_g_hull cp.

Theorem tpj_string_B_holds_kit : forall CTX0,
  tpj_string_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK CTX0.
Proof.
exact (tpj_string_B_holds B ARx MEMSET STRDUP LAWS PAL (pjs_g_lit_of_tfib B TS) img_shadow_vis_cf HULL).
Qed.
End k.

(* THE HULL BUDGET AT A RUN POSITION at preset's CfParams (pj_string_defs.v pjs_g_hull): preset's request bound
   2 ^ 28 + 2 ^ 27 is at most 2 ^ 30, and lib/A/PresetHullPay.v hull_budget_of_room_pos is the budget at a run
   position of at most 4 calls *)
Lemma pjs_hull_preset : @pjs_g_hull CfParams_preset.
Proof.
split; [cbn [cf_malloc_max CfParams_preset]; lia|].
exact PresetHullPay.hull_budget_of_room_pos.
Qed.

(* ---- at preset's instance: CfParams_preset, B := YD2l.TfibB, ARx := YG0ncf.ARcf rsegs TfibB ---- *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).
(* the callee texts at the instance *)
Hypothesis MEMSET : YGcallMxmn.aintrin_realizes_xm SEGS TB ARI OSet (@pa_sigma _ B_prog_listing PA AS___asan_memset).
Hypothesis STRDUP : tfuzz_strdup_specX (cp := CP) (PA := PA) TB ARI SK.

(* the INSTANCE WITNESS of the state fact pjs_g_lit_sh at ARcf rsegs TfibB: the cover check of image B's shadow lists
   (pjs_img_shadow_cover_B) with lib/Reusable/YImgShadowCoverCf.v img_shadow_vis_cf_at_of_cover *)
Lemma pjs_g_lit_sh_B : pjs_g_lit_sh ARI.
Proof.
assert (Iz : incl YF0m.Tfib_zero_shadow (as_zero_shadow TB)) by (cbn [as_zero_shadow YD2l.TfibB]; apply incl_refl).
assert (Ic : forall ly, incl YF0m.Tfib_const_shadow (as_const TB ly)).
{ intros ly. cbn [as_const YD2l.TfibB]. unfold YF0m.Tfib_const. apply incl_appr, incl_appr, incl_refl. }
unfold pjs_g_lit_sh. intros ly S Hp W mem md a HAR Ha.
exact (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover (cp := CP) rsegs TB YF0m.Tfib_zero_shadow
  YF0m.Tfib_const_shadow IMG_LO_B IMG_TOP_B pjs_img_shadow_cover_B Iz Ic ly S Hp W mem md a HAR Ha).
Qed.

Theorem tpj_string_B_preset : forall CTX0,
  tpj_string_specX (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) TB ARI SK CTX0.
Proof.
exact (tpj_string_B_holds_kit (cp := CP) TB ARI MEMSET STRDUP PALibB.exvi_eh_laws PALibB.exvi_eh_palib
  pjs_g_lit_sh_B YD2l.TfibB_syms pjs_hull_preset).
Qed.
End p.

(* ---- THE SUPPLY at check_round_trip's entry (anti-vacuity): the run premise of tpj_string_specX holds of the model
   run at the rewrite's pj_string, from check_round_trip's own run premise over PresetReqAt.round_trip (JObj ms): the
   rewrite's events come after the two round_trip_text runs and pj_free (&doc) (split by PRH_Base.prh_run_at_app_iff),
   and their head is pj_string's (the prhPj_string_evs_supply, PRH_FnPj.v:296 at f97c8b2f046b; the chosen failure
   needs nothing: prhPj_string_evs is [] there). The head width cf_head = HEAD is 16 = 16 at CfParams_preset
   (pjs_head_preset). ---- *)
Section s. Context {cp : CfParams}.
Lemma pj_string_evs_supply_rt : forall sm x os i ms cnt fail,
  prh_run_at sm x os i (PresetReqAt.round_trip sm (PjTree.JObj ms)) ->
  cf_head = PresetReqAt.HEAD ->
  prh_run_at sm x os
    (i + length (PresetReqAt.rt_text sm (PjTree.JObj ms) false) + length (PresetReqAt.rt_text sm (PjTree.JObj ms) true)
       + 1)%nat
    (prhPj_string_evs (Z.of_nat (length PresetReqAt.MOD_VAL)) cnt fail).
Proof.
intros sm x os i ms cnt fail H Hh.
unfold PresetReqAt.round_trip in H. cbv beta iota in H.
apply prh_run_at_app_iff in H as [_ H].
apply prh_run_at_app_iff in H as [_ H].
apply prh_run_at_app_iff in H as [_ H].
apply prh_run_at_app_iff in H as [H _].
unfold PresetReqAt.rw_evs in H.
apply prh_run_at_app_iff in H as [H _].
cbn [length] in H.
destruct (Z.eq_dec cnt fail) as [E | E].
- unfold prhPj_string_evs. rewrite (proj2 (Z.eqb_eq _ _) E). apply prhPj_run_at_nil.
- exact (prhPj_string_evs_supply sm x os _ ms cnt fail Hh E H).
Qed.
End s.

(* the head width at preset's instance *)
Lemma pjs_head_preset : @cf_head CfParams_preset = PresetReqAt.HEAD.
Proof. reflexivity. Qed.
