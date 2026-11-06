(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_parse_seg_c2ok.v, with its module paths, module names, addresses and numbers changed; 683 of its 883 lines of code are new or changed and 550 lines of the source are left out. *)
(* Theorem Labs, 2026-10: pj_parse's image-A' walk (fuzz_preset asan, #102 pin 1be0f53d96cb, unstripped twin
   bff8519bbe3e; A' 0x85e20; preset_file.c :296-309), the segment from the cut pjp_C2ok (+0x50, parse_value returned
   0) to the cuts pjp_C3 (+0xd4, the value is the whole text) and pjp_C2ref (+0xc8, junk after the value), over
   lib/A/Prog/PjParseA_defs.v's statements. proves no function (kind: segment lemma).
   THE CODE (whole-program listing lib/A/Listing_prog.v, PA := PI_prog_A; pc offsets from pj_parse's entry):
     +0x50 ld a3, 0(sp)   +0x54 ld a1, 8(sp)   +0x58 bgeu a3, a1 -> +0xc0 (p >= end: nothing after the value)
     +0x5c ld a2, 0(sp)   +0x60 li a4, 32      +0x64 lui a0, 0x800   +0x68 addiw a0, a0, 0x13   +0x6c slli a5, a0, 9
     +0x70 mv a0, a3      +0x74 .. +0xb8 the INLINED skip_ws loop (lib/A/Prog/PjParseA_skip.v pjs_loop: its shadow
                          check per byte, its report arm +0xb4 `jal __asan_report_load1` never reached)
     +0xbc sd a2, 0(sp)   (the loop's one store: p := t0 + len - |PjGrammar.skip r|)
     +0xc0 ld a0, 0(sp)   +0xc4 beq a0, a1 -> +0xe8 (a0 := 0, +0xec j +0xd4: the cut C3); else +0xc8 (the cut C2ref).
   PORTED from the image-B' walk (the version pj_parse_seg_c2ok.v (sha256 b4f0f253f223; internal record) of
   lib/B/Prog/pj_parse_seg_c2ok.v): the lemma name pjp_seg_C2ok_holds and its Section-hypothesis order, the two cut
   arms after the `beq` (pjp_C3's post pjp_Q and pjp_C2ref's tie, the position transfer and the outcome, read off
   parse_value's facts at the cut). RE-WALKED (A' has no skip_ws symbol): B''s `jal skip_ws` and the kit's tskip_ws_specX
   are replaced by the inline walk +0x50 .. +0xbc (this file and PjParseA_skip.v); the model is the same
   (lib/A/PRH_FnReader.v tskip_ws_specX: the stored p is t0 + len - |PjGrammar.skip (rest_atR tl t0 p)|, with
   rest_atR tl t0 p = r by pjp_g_rest). No callee text is assumed: the segment calls nothing.
   HOW: engine stretches over YCbqG's ajournal_x (YC1fPx.v paj_run_x_inv / paj_run_to_x_inv at P :=
   YAkMemnorm.memnorm, YSRrMemnorm.srr_inv_laws_memnorm_k), each seated fresh from the facts at its start:
   pjp_seg_C2ok_holds (+0x50, to the branch +0x58, then to +0xc0 or to the loop head +0x74), pjs_loop (the loop, to
   +0xbc), pjp2_exit (+0xbc: the store, to +0xc0), pjp2_tail (+0xc0: reload p, branch, to C3 or C2ref). Every stretch but
   the exit stores nothing, so its memory is the memory before it (frame_of_read_only); the exit's store writes the
   cursor's p word [sp1, sp1 + 8) only, a byte of pj_parse's own frame inside the widened window, above the ceiling:
   every other fact rides through it by the engine's frame_of / mem_grows (pjp2_kept8: the tree's bytes, out's facts,
   the text, the ledger, the frame slots and the cursor's end / depth words lie outside that window).
   Position and memory: nothing in the segment allocates, so the cut's state S, its run position pjp_pos_pv and its
   outcome pjp_outc are the ones at C3 / C2ref; memnorm rides along every stretch by the runners' P.
   THE RE-HIDING MOVE AND THE HULL: the cut is after parse_value's call, so its journal is at wle' SEGS RZ_cf (pjp_invR)
   and every stretch runs over that relation (YC1fPx.v paj_run_x_invR / paj_run_to_x_invR, YSRrG.v paj_branchR, the
   loop PjParseA_skip.v pjs_loop at it); every statement here concludes SRr' SEGS RZ_cf. The hull use of the cut
   (parse_value's, from the entry state) is the text's at C3 widened to pj_parse's list (PjParseA_counts.v
   pjc_hull_used_pv); C2ref carries it on. THE OUTCOME OF AN INJECTED READING (the text's GUARDED conjunct): at C3 the
   value was accepted, so the guard's window is empty (pjp_g_fail_in gives res = None there); C2ref carries the cut's
   pjp_inj on.
   Section hypotheses (all statements of PjParseA_defs.v or the kit, none of this file): pjp_seg_C3, pjp_seg_C2ref,
   prh_head16, AR_laws_x SEGS B ARx cf_head and the glue pjp_g_depth / _run / _fail_in / _norefuse / _calls /
   _fail_after / _rest / _ab_hbl. B''s pjp_texts (skip_ws's text), pjp_frame_kept_stmt (the call's keep) and pjp_g_vis
   (a fake frame's shadow hull after the call) are not hypotheses here: the A' segment makes no call.
   Numerals: 8 / 16 / 24 / 32 / 40 / 48 / 56 (LENGTH: slots, cursor, frame, node), 4096 / 4144 (LENGTH: page, ESTACK +
   frame), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 62 / 2 ^ 64 (LENGTH: shadow span, stack band, address bounds); atom numbers
   2 .. 33 DERIVED (the engine's numbering); pc offsets DERIVED from PjParseA_defs.v's PJP_* (PJP_C2OK + 112 = +0xc0)
   and PjParseA_skip.v's PJS_LOOP / PJS_EXIT. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjParseA_defs PjParseA_glue PjParseA_skip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PjParseA_counts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Existing Instance prh_img_A.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seats ---- *)
(* +0xc0, `ld a0, 0(sp)` after the store (or straight from the empty test) *)
Definition PJP2_TAIL : Z := PJP_C2OK + 112.
(* no shadow check in these stretches: the span the entries may name is the point (0, 0) *)
Definition PJP2_Bx : sv := SLit SHADOW_OFF.
Definition PJP2_Bspan : Z * Z := (0, 0).
(* the cut C2ok (+0x50): the cursor's p and end words at sp + 0 / sp + 8 (atom 2 = sp), atoms 32 = p, 33 = end *)
Definition pjp2_regA : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition pjp2_ssA : sstate := mkSS PJP_C2OK sr_atoms [pjp2_regA] None (mkFacts [] [] []).
(* the exit (+0xbc): the p word at sp + 0, written by `sd a2, 0(sp)` *)
Definition pjp2_regX : YP09.region := YP09.mkRegion (Some 2%nat) 0 8 0 8 [].
(* atom 2 (sp1) in the stack band, 8-aligned: the write window's interval, apart from the shadow span (YCbn.v
   cells_safe_b) *)
Definition pjp2_ssX : sstate :=
  mkSS PJS_EXIT sr_atoms [pjp2_regX] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 3)] [] []).
(* the tail (+0xc0): the p word at sp + 0, atom 32 *)
Definition pjp2_regT : YP09.region := YP09.mkRegion (Some 2%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition pjp2_ssT : sstate := mkSS PJP2_TAIL sr_atoms [pjp2_regT] None (mkFacts [] [] []).

(* the shadow hull of an application range below kHighMemEnd lies in the shadow region (pj_parse_seg_ent.v
   pje_hull_bounds, image-free) *)
Lemma pjp2_hull_bounds : forall x n s, 0 <= x -> 0 < n -> x + n <= kHighMemEnd ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *.
lia.
Qed.

(* ---- the tree's capacity words across a memory that agrees on the node's footprint (PORTED, image-free, from
   lib/B/Prog/PvB_Frees.v pvf_kids_items / pvf_kids_mems /
   pvf_ncap_frame; the 64-bit read's determinism is lib/A/PjFoMember.v pfm_rd_u64_det) ---- *)
Section t.
Variable segs : list Segment.
Lemma pjp2_kids_items : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q Q' : Z -> PjTree.jv -> Prop) l a D,
  pj_itemsR P a l D -> pj_kidsR Q a l ->
  (forall i u D1, nth_error l i = Some u -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     Q (a + 56 * Z.of_nat i) u -> Q' (a + 56 * Z.of_nat i) u) ->
  pj_kidsR Q' a l.
Proof.
intros P Q Q' l. induction l as [|u r IH]; intros a D H HQ HP; cbn [pj_itemsR pj_kidsR] in H, HQ |- *; [exact I|].
destruct H as (D1 & D2 & -> & H1 & H2). destruct HQ as (Q1 & Q2). split.
- specialize (HP 0%nat u D1 eq_refl (incl_appl D2 (incl_refl D1))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1 Q1).
- apply (IH (a + 56) D2 H2 Q2). intros i u' D1' Hi Hinc HPi HQi.
  specialize (HP (S i) u' D1' Hi (incl_appr D1 Hinc)).
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi HQi).
Qed.

Lemma pjp2_kids_mems : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q Q' : Z -> PjTree.jv -> Prop)
    l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in Q a u) a l ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     Q (a + 56 * Z.of_nat i) u -> Q' (a + 56 * Z.of_nat i) u) ->
  pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in Q' a u) a l.
Proof.
intros m lblk P Q Q' l. induction l as [|[nm u] r IH]; intros a ka D H HQ HP;
  cbn [pj_memsR pj_kidsR] in H, HQ |- *; [exact I|].
destruct H as (x & k & D1 & D2 & -> & _ & _ & H1 & H2). destruct HQ as (Q1 & Q2). split.
- specialize (HP 0%nat nm u D1 eq_refl (incl_tl (x, k) (incl_appl D2 (incl_refl D1)))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1 Q1).
- apply (IH (a + 56) (ka + 8) D2 H2 Q2). intros i nm' u' D1' Hi Hinc HPi HQi.
  specialize (HP (S i) nm' u' D1' Hi (incl_tl (x, k) (incl_appr D1 Hinc))).
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi HQi).
Qed.

Lemma pjp2_ncap_frame : forall t m m' lblk p D,
  pj_nodeR segs m lblk p t D -> pj_agreeR segs m m' (pj_footR p D) ->
  pj_ncapR segs m p t -> pj_ncapR segs m' p t.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m m' lblk p D HN HM HC; cbn [pj_ncapR] in HC |- *; try exact I.
- assert (HM1 : forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs m x)
    by (intros x Hx; exact (proj1 (HM x Hx))).
  cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb).
  destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (H48 & kids' & H24 & Hk).
  pose proof Hh as (_ & _ & _ & _ & Hkids & _).
  assert (Ekk : kids' = kids) by exact (PjFoMember.pfm_rd_u64_det segs m (p + 24) kids' kids H24 Hkids). subst kids'.
  split; [apply (rd_u64_frame segs _ _ _ _ H48); intros x Hx; apply HM1; left; lia|].
  exists kids. split; [apply (rd_u64_frame segs _ _ _ _ H24); intros x Hx; apply HM1; left; lia|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  apply (pjp2_kids_items (pj_nodeR segs m lblk) (pj_ncapR segs m) _ items kids Di Hi Hk).
  intros i u D1 Hil Hinc HP HQ.
  pose proof (pj_nth_lenR items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m m' lblk _ D1 HP); [|exact HQ].
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- assert (HM1 : forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs m x)
    by (intros x Hx; exact (proj1 (HM x Hx))).
  cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb).
  destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (H48 & kids' & H24 & Hk).
  pose proof Hh as (_ & _ & _ & _ & Hkids & _).
  assert (Ekk : kids' = kids) by exact (PjFoMember.pfm_rd_u64_det segs m (p + 24) kids' kids H24 Hkids). subst kids'.
  split; [apply (rd_u64_frame segs _ _ _ _ H48); intros x Hx; apply HM1; left; lia|].
  exists kids. split; [apply (rd_u64_frame segs _ _ _ _ H24); intros x Hx; apply HM1; left; lia|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  apply (pjp2_kids_mems m lblk (pj_nodeR segs m lblk) (pj_ncapR segs m) _ members kids keys Di Hi Hk).
  intros i nm u D1 Hil Hinc HP HQ.
  pose proof (pj_nth_lenR members i (nm, u) Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
  apply (IH m m' lblk _ D1 HP); [|exact HQ].
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
Qed.
End t.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the segment is after parse_value's call: the relation of its journal, its runs and its statements *)
#[local] Notation RW := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B prh_pst ARx RW).

(* ---- the segment's Section hypotheses: the two later segments; then the kit's allocator laws and the pure glue
   (PjParseA_defs.v) ---- *)
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
Hypothesis SEG3 : pjp_seg_C3 (SK := SK) B ARx CTX0 CW.
Hypothesis SEG2R : pjp_seg_C2ref (SK := SK) B ARx CTX0 CW.
(* CFHEAD-16, the walk's Section hypothesis (PRH_Base.v prh_head16; reflexivity at CfParams_preset): the tree's
   free order in parse_value's post is stated under it *)
Hypothesis HH : prh_head16.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis G_depth : pjp_g_depth.
Hypothesis G_run : pjp_g_run.
Hypothesis G_fail_in : pjp_g_fail_in.
Hypothesis G_norefuse : pjp_g_norefuse.
Hypothesis G_calls : pjp_g_calls.
Hypothesis G_fail_after : pjp_g_fail_after.
Hypothesis G_rest : pjp_g_rest.
Hypothesis G_ab_hbl : pjp_g_ab_hbl.

(* a chunk of a symbolic state and the bytes it states (pj_parse_seg_ent.v pje_cv / pje_cv_ok / pje_val) *)
Definition pjp2_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma pjp2_cv_ok : forall (fz : YK11.FPState) E ss ms j off w c, st_ok (fx := fz) SEGS E ss ms ->
  pjp2_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros fz E ss ms j off w c HS H. unfold pjp2_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pjp2_val : forall (fz : YK11.FPState) E ss ms j off (w : N) e v b a, st_ok_pi (fx := fz) SEGS VAL E ss ms ->
  pjp2_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros fz E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pjp2_cv_ok fz E (abs_ss VAL ss) ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- a stretch that stores nothing leaves every byte: the predicates ride along (pj_parse_seg_c2ok.v Section m) ---- *)
Section m.
Variable H : word -> bool.
Variables m m' : word -> option byte.
Hypothesis Hm : forall x, m' x = m x.
Lemma pjm_mb : forall a, mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros a. unfold mbyte, mrestrict. cbv beta. rewrite Hm. reflexivity. Qed.
Lemma pjm_av : forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros a. unfold aview. rewrite pjm_mb. reflexivity. Qed.
Lemma pjm_val : forall a n v, val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros a n v Hv. apply (pj_valR_frame SEGS (mrestrict H m) (mrestrict H m') a n v Hv). intros x _. apply pjm_mb. Qed.
Lemma pjm_pres : forall a, apresent H m a -> apresent H m' a.
Proof. intros a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite Hm. exact Hb. Qed.
Lemma pjm_ra : forall a n, range_addressable (aview SEGS H m) SHADOW_OFF a n ->
  range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof. intros a n Hr. apply (range_addressable_agree (aview SEGS H m) (aview SEGS H m') SHADOW_OFF a n); [|exact Hr].
intros x _. apply pjm_av. Qed.
Lemma pjm_rod : arodata_okP SEGS RLO RHI B (aview SEGS H m) -> arodata_okP SEGS RLO RHI B (aview SEGS H m').
Proof. intros Hr a H1 H2 H3. rewrite pjm_av. exact (Hr a H1 H2 H3). Qed.
Lemma pjm_mn : YAkMemnorm.memnorm SEGS m -> YAkMemnorm.memnorm SEGS m'.
Proof.
unfold YAkMemnorm.memnorm. intros [H1 H2].
split; intros a b E; rewrite Hm in E; [exact (H1 a b E) | exact (H2 a b E)].
Qed.
End m.

(* pjp_invR (at wle') across a stretch that stores nothing and keeps sp, s0, s1 and the callee-saved registers *)
Lemma pjm_inv : forall en Sb fy ly S Hp W regs mem md k ly' S' Hp' regs' mem' md' k',
  pjp_invR (fx := fx) (SK := SK) B ARx RW en Sb fy ly S Hp W regs mem md k ->
  AJ (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly' S' Hp' W mem' md' k' ->
  (forall x, mem' x = mem x) ->
  spZ regs' = spZ regs -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall r, In r PJP_KEPT -> getr regs' r = getr regs r) ->
  pjp_invR (fx := fx) (SK := SK) B ARx RW en Sb fy ly' S' Hp' W regs' mem' md' k'.
Proof.
intros en Sb fy ly S Hp W regs mem md k ly' S' Hp' regs' mem' md' k' HI HJ Hm Hsp H8 H9 HK.
destruct HI as (Z1 & Z2 & _ & Hwin & Hsp1 & Hra & Hs0 & Hs1 & H8' & H9' & HK' & Hpres & Hra24 & Hrod & Hmn).
split; [exact Z1|]. split; [exact Z2|]. split; [exact HJ|].
split; [intros a Ha; rewrite (pjm_av _ _ _ Hm); exact (Hwin a Ha)|].
split; [rewrite Hsp; exact Hsp1|].
split; [exact (pjm_val _ _ _ Hm _ _ _ Hra)|].
split; [exact (pjm_val _ _ _ Hm _ _ _ Hs0)|].
split; [exact (pjm_val _ _ _ Hm _ _ _ Hs1)|].
split; [rewrite H8; exact H8'|].
split; [rewrite H9; exact H9'|].
split; [intros r Hr; rewrite (HK r Hr); exact (HK' r Hr)|].
split; [intros a Ha; exact (pjm_pres _ _ _ Hm a (Hpres a Ha))|].
split; [exact (pjm_ra _ _ _ Hm _ _ Hra24)|].
split; [exact (pjm_rod _ _ _ Hm Hrod) | exact (pjm_mn _ _ Hm Hmn)].
Qed.

Ltac pjp2_in := cbn [In PJP_KEPT]; repeat (first [left; reflexivity | right]).

(* ---- the segment's state between the cut and the cuts after it: pjp_C2ok's facts with the witnesses named and the
   cursor's p word at pc (C2ok's own: t0 + len - |r|; after the store: t0 + len - |PjGrammar.skip r|); the journal
   at wle', parse_value's hull use and its injected-reading outcome last ---- *)
Definition pjp2_at (en : PjpEnt) (Sb : astate) (fy : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (ok : list bool)
  (t : PjTree.jv) (r : list Z) (tr : list PjGrammar.ev) (D Lam' : list (Z * Z)) (peak' cnt' fail' ran' : Z)
  (pc : Z) : Prop :=
  pjp_invR (fx := fx) (SK := SK) B ARx RW en Sb fy ly S Hp W regs mem md k /\ room_live_cf S /\
  pjp_pv_out B en ly S Hp W mem ok (Some (t, r)) tr D Lam' peak' cnt' fail' ran' /\ pjp_pos_pv en S tr /\
  pjp_outc en S (Some (t, r)) tr ran' /\
  pjp_cursor en W mem pc /\
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam') (je_out en) t D /\
  pj_ncapR SEGS (rdW W mem) (je_out en) t /\
  pjp_out_ok B en ly S Lam' W mem /\
  pjp_text_ok B en ly S Hp Lam' W mem /\
  pjp_ftie en W mem Lam' D ok (PjTree.depth t) /\
  PresetHullBudget.hull_used (je_S en) S (PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en))) /\
  pjp_inj en ok tr.

(* the same state at other registers and model, the memory unchanged *)
Lemma pjp2_at_regs : forall en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' pc regs' md',
  pjp2_at en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' pc ->
  AJ (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly S Hp W mem md' k ->
  spZ regs' = spZ regs -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall r, In r PJP_KEPT -> getr regs' r = getr regs r) ->
  pjp2_at en Sb fy ly S Hp W regs' mem md' k ok t r tr D Lam' peak' cnt' fail' ran' pc.
Proof.
intros en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' pc regs' md' (HI & Hrest) HJ Hsp H8 H9
  HK.
split; [|exact Hrest].
exact (pjm_inv en Sb fy ly S Hp W regs mem md k ly S Hp regs' mem md' k HI HJ (fun x => eq_refl) Hsp H8 H9 HK).
Qed.

(* ---- THE STORE `sd a2, 0(sp)` keeps every byte outside [q, q + 8) (q = sp1, the cursor's p word) and every
   present byte present ---- *)
Definition pjp2_kept8 (H : word -> bool) (m m' : word -> option byte) (q : Z) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) -> aview SEGS H m' a = aview SEGS H m a) /\
  mem_grows (mrestrict H m) (mrestrict H m').

Section k.
Variable H : word -> bool.
Variables (m m' : word -> option byte) (q : Z).
Hypothesis HK : pjp2_kept8 H m m' q.
Hypothesis Hq : YM05.alloc_ceiling + 4096 <= q.
Lemma pjp2_k_low : forall a, 0 <= a < YM05.alloc_ceiling + 4096 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros a Ha. pose proof YM05.alloc_ceiling_lt as Hc. destruct HK as [KV _]. apply KV; lia.
Qed.
Lemma pjp2_k_val : forall a (n : nat) v, val_mem SEGS (mrestrict H m) a n v -> 0 <= a ->
  a + Z.of_nat n <= YM05.alloc_ceiling + 4096 -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros a n v Hv H0 Hn kk Hk. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply pjp2_k_low. lia.
Qed.
Lemma pjp2_k_garr : forall a l, garr8 SEGS (mrestrict H m) a l -> 0 <= a ->
  a + Z.of_nat (length l) <= YM05.alloc_ceiling + 4096 -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros a l Hg H0 Hl j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pjp2_k_val _ 1 _ Hv); lia.
Qed.
Lemma pjp2_k_sh : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS H m' s = aview SEGS H m s.
Proof.
intros s Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). apply pjp2_k_low. lia.
Qed.
Lemma pjp2_k_ra : forall p n, 0 <= p -> p + n <= kHighMemEnd ->
  range_addressable (aview SEGS H m) SHADOW_OFF p n -> range_addressable (aview SEGS H m') SHADOW_OFF p n.
Proof.
intros p n Hp0 Hpn Hr. eapply range_addressable_agree; [|exact Hr]. intros x Hx.
pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
apply pjp2_k_sh. exact Hsx.
Qed.
Lemma pjp2_k_hull : forall p n, 0 <= p -> 0 < n -> p + n <= kHighMemEnd ->
  shadow_hull_vis (aview SEGS H m) p n -> shadow_hull_vis (aview SEGS H m') p n.
Proof.
intros p n Hp0 Hn Hpn Hh s Hs. rewrite pjp2_k_sh by exact (pjp2_hull_bounds p n s Hp0 Hn Hpn Hs). exact (Hh s Hs).
Qed.
Lemma pjp2_k_wr : forall a, writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m') a.
Proof. intros a Hw. destruct HK as [_ MG]. exact (writable_at_grows SEGS _ _ a MG Hw). Qed.
Lemma pjp2_k_agree : forall (X : Z -> Prop), (forall x, X x -> 0 <= x < YM05.alloc_ceiling) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H m') X.
Proof.
intros X HX x Hx. destruct (HX x Hx) as [H0 H1]. split.
- apply (mbyte_of_aview SEGS). apply pjp2_k_low. lia.
- apply pjp2_k_wr.
Qed.
End k.

(* the tree's footprint (out's node and the harness blocks D) lies below the ceiling *)
Lemma pjp2_foot_below : forall en ly S Hp W mem md Lam peak cnt fail ran most own D x,
  ARx ly S Hp W mem md -> pjp_out_ok B en ly S Lam W mem ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> (forall b, In b D -> In b Lam) ->
  pj_footR (je_out en) D x -> 0 <= x < YM05.alloc_ceiling.
Proof.
intros en ly S Hp W mem md Lam peak cnt fail ran most own D x HAR HO HL HDL Hx.
destruct HO as (H4096 & Hceil & Hplace & _).
pose proof HL as HLF. apply prh_ledger_blocks in HLF.
destruct Hx as [Hx | (b0 & Hb0 & Hhx)].
- destruct Hplace as [(b & m & Hbm & _ & Hb & Hm) | (cid & pos & Hcp & Hf1 & Hf2)].
  + destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm) as (_ & _ & Hc & _).
    pose proof (req_size_pos m ltac:(lia)) as [_ Rm]. lia.
  + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (_ & Hfc & _). lia.
- destruct b0 as [a k]. unfold pj_holdsR in Hhx. cbn [fst snd] in Hhx.
  destruct (proj1 (Forall_forall _ _) HLF (a, k) (HDL _ Hb0)) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  pose proof (@cf_head_nonneg cp) as Hc0. pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [_ Rk].
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _). lia.
Qed.

(* the ledger across the store: the statics are image bytes, every head word lies in its block below the ceiling *)
Lemma pjp2_ledger_store : forall ly S Hp W mem mem' md Lam peak cnt fail ran most own q,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  pjp2_kept8 (w_H W) mem mem' q -> YM05.alloc_ceiling + 4096 <= q ->
  prh_ledger (PA := PA) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' md Lam peak cnt fail ran most own q HAR HL HK Hq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HL).
- intros a Ha. pose proof (pst_in_img_A a Ha) as Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hlo.
  apply (pjp2_k_low _ _ _ _ HK Hq). lia.
- intros a k i Hin Hi.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & _ & _ & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (Hal & H4096 & Hcl & _).
  pose proof (@cf_head_nonneg cp) as Hh0.
  assert (Hreq : a - cf_head + 1 <= YM05.alloc_ceiling)
    by (unfold req_size in Hcl; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  apply (pjp2_k_low _ _ _ _ HK Hq). lia.
- intros a k _ Hb. exact Hb.
- apply Permutation_refl.
Qed.

(* pjp_invR (at wle') across the store: the slots at sp1 + 24 / 32 / 40, the caller window and the image lie outside
   the p word; the cursor's shadow is a shadow byte; the frame stays present *)
Lemma pjp2_inv_store : forall en Sb fy ly S Hp W regs mem md k regs' mem' md',
  pjp_invR (fx := fx) (SK := SK) B ARx RW en Sb fy ly S Hp W regs mem md k ->
  AJ (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly S Hp W mem' md' k ->
  YAkMemnorm.memnorm SEGS mem' ->
  pjp2_kept8 (w_H W) mem mem' (je_sp1 en) ->
  YM05.alloc_ceiling + 4096 <= je_sp1 en -> 0 <= je_d en -> je_sp0 en + je_d en <= 2 ^ 47 ->
  spZ regs' = spZ regs -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall r, In r PJP_KEPT -> getr regs' r = getr regs r) ->
  pjp_invR (fx := fx) (SK := SK) B ARx RW en Sb fy ly S Hp W regs' mem' md' k.
Proof.
intros en Sb fy ly S Hp W regs mem md k regs' mem' md' HI HJ HMN HK Hq Hd0 Htop Hsp H8 H9 HKP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Esp1 : je_sp1 en = je_sp0 en - 48) by reflexivity.
pose proof HK as [KV MG].
destruct HI as (Z1 & Z2 & _ & Hwin & Hsp1 & Hra & Hs0 & Hs1 & H8' & H9' & HK' & Hpres & Hra24 & Hrod & _).
split; [exact Z1|]. split; [exact Z2|]. split; [exact HJ|].
split; [intros a Ha; rewrite KV by lia; exact (Hwin a Ha)|].
split; [rewrite Hsp; exact Hsp1|].
split; [intros kk Hk; rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'); [exact (Hra kk Hk)|]; apply KV; lia|].
split; [intros kk Hk; rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'); [exact (Hs0 kk Hk)|]; apply KV; lia|].
split; [intros kk Hk; rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'); [exact (Hs1 kk Hk)|]; apply KV; lia|].
split; [rewrite H8; exact H8'|].
split; [rewrite H9; exact H9'|].
split; [intros r Hr; rewrite (HKP r Hr); exact (HK' r Hr)|].
split; [intros a Ha; exact (apresent_grows _ _ _ a MG (Hpres a Ha))|].
split; [apply (pjp2_k_ra _ _ _ _ HK Hq); [lia | rewrite C4; lia | exact Hra24]|].
split; [|exact HMN].
intros a Hro Hno Herr.
assert (Hi : in_img SEGS a).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
pose proof (@pa_segs_low _ _ PA a Hi) as Hlo.
rewrite (pjp2_k_low _ _ _ _ HK Hq) by lia. exact (Hrod a Hro Hno Herr).
Qed.

(* the state across the store: every fact of pjp2_at at the new memory, the cursor's p word the stored p2 *)
Lemma pjp2_at_store : forall en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' pc regs' mem' md'
    p2,
  pjp2_at en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' pc ->
  AJ (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) Sb (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly S Hp W mem' md' k ->
  YAkMemnorm.memnorm SEGS mem' ->
  pjp2_kept8 (w_H W) mem mem' (je_sp1 en) ->
  YM05.alloc_ceiling + 4096 <= je_sp1 en -> 0 <= je_d en -> je_sp0 en + je_d en <= 2 ^ 47 ->
  spZ regs' = spZ regs -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall r, In r PJP_KEPT -> getr regs' r = getr regs r) ->
  val_mem SEGS (rdW W mem') (je_sp1 en) 8 p2 -> je_t0 en <= p2 <= je_t0 en + je_len en ->
  pjp2_at en Sb fy ly S Hp W regs' mem' md' k ok t r tr D Lam' peak' cnt' fail' ran' p2.
Proof.
intros en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' pc regs' mem' md' p2 HA HJ HMN HK Hq
  Hd0 Htop Hsp H8 H9 HKP Vp2 Hp2.
destruct HA as (HINV & HROOM & HPV & HPOSPV & HOUTC & HCUR & HNODE & HNCAP & HOUT & HTXT & HTIE & HHU & HINJ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof YM05.alloc_ceiling_lt as Hcl.
assert (Esp1 : je_sp1 en = je_sp0 en - 48) by reflexivity.
pose proof HINV as (_ & _ & HJ0 & _).
pose proof HJ0 as (HAR & _).
pose proof HPV as (Hjv & HLED & HLM & HBM).
pose proof HLM as (Hoks & Hcnt' & Hfa' & HPL & HPD & HND & Hpk').
assert (HDL : forall b, In b D -> In b Lam').
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hb. }
assert (AGR : pj_agreeR SEGS (rdW W mem) (rdW W mem') (pj_footR (je_out en) D)).
{ apply (pjp2_k_agree _ _ _ _ HK Hq). intros x Hx.
  exact (pjp2_foot_below en ly S Hp W mem md Lam' peak' cnt' fail' ran' (je_most en) (je_own en) D x HAR HOUT HLED
    HDL Hx). }
pose proof HTXT as ((HBY & H4096 & Htc & Htam & HTRA & Hth) & Hhome).
pose proof HCUR as (V1 & V2 & V3 & Hrw & Hal8 & Ht0 & Ht62 & Hp0 & Hlen & Hg & Hap & Hdd).
split; [exact (pjp2_inv_store en Sb fy ly S Hp W regs mem md k regs' mem' md' HINV HJ HMN HK Hq Hd0 Htop Hsp H8 H9
  HKP)|].
split; [exact HROOM|].
split.
{ split; [exact Hjv|]. split; [exact (pjp2_ledger_store ly S Hp W mem mem' md Lam' peak' cnt' fail' ran' (je_most en)
    (je_own en) (je_sp1 en) HAR HLED HK Hq)|]. split; [exact HLM | exact HBM]. }
split; [exact HPOSPV|].
split; [exact HOUTC|].
split.
{ (* the cursor: p := p2 (the store), end and depth untouched, the text's bytes below the ceiling *)
  unfold pjp_cursor, pj_in_okR.
  split; [exact Vp2|].
  split; [intros kk Hk; rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'); [exact (V2 kk Hk)|];
          apply (proj1 HK); lia|].
  split; [intros kk Hk; rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'); [exact (V3 kk Hk)|];
          apply (proj1 HK); lia|].
  split; [intros x Hx; exact (pjp2_k_wr _ _ _ _ HK x (Hrw x Hx))|].
  split; [exact Hal8|]. split; [exact Ht0|]. split; [exact Ht62|]. split; [exact Hp2|]. split; [exact Hlen|].
  split; [apply (pjp2_k_garr _ _ _ _ HK Hq _ _ Hg); lia|].
  split; [exact Hap | exact Hdd]. }
split; [exact (pj_nodeR_frame SEGS t _ _ (prh_lin Lam') (je_out en) D HNODE AGR)|].
split; [exact (pjp2_ncap_frame SEGS t _ _ (prh_lin Lam') (je_out en) D HNODE AGR HNCAP)|].
split.
{ (* out's facts *)
  destruct HOUT as (O1 & O2 & O3 & O4 & (Oal & Orw) & O6 & O7 & O8 & O9).
  refine (conj O1 (conj O2 (conj O3 (conj O4 (conj (conj Oal _) (conj O6 (conj O7 (conj _ _)))))))).
  - intros x Hx. exact (pjp2_k_wr _ _ _ _ HK x (Orw x Hx)).
  - apply (pjp2_k_ra _ _ _ _ HK Hq); [lia | unfold amem_range in O6; lia | exact O8].
  - apply (pjp2_k_hull _ _ _ _ HK Hq); [lia | lia | unfold amem_range in O6; lia | exact O9]. }
split.
{ (* the text, at home *)
  split; [|exact Hhome].
  split; [apply (pjp2_k_garr _ _ _ _ HK Hq _ _ HBY); lia|].
  split; [exact H4096|]. split; [exact Htc|]. split; [exact Htam|].
  split; [apply (pjp2_k_ra _ _ _ _ HK Hq); [lia | unfold amem_range in Htam; lia | exact HTRA]|].
  intros Hn. apply (pjp2_k_hull _ _ _ _ HK Hq); [lia | exact Hn | unfold amem_range in Htam; lia | exact (Hth Hn)]. }
(* the tree's free order; parse_value's hull use and its injected-reading outcome are memory-free *)
split; [|split; [exact HHU | exact HINJ]].
intros HH' n Hn. destruct (HTIE HH' n Hn) as (F' & HFO' & HT'). exists F'. split; [|exact HT'].
apply (pj_foR_frame SEGS n _ _ (prh_lin Lam') (prh_lin Lam') (je_out en) D F' HFO').
- exact (pj_foR_lblk SEGS _ _ _ _ _ _ HFO').
- exact AGR.
Qed.

(* the frame's bounds at the entry (fpre's astk_ok, the caller window fwin; STK_pj_parse by computation) *)
Lemma pjp2_bounds : forall en, pjp_pre B ARx CTX0 CW en ->
  YM05.alloc_ceiling + 4096 <= je_sp1 en /\ 0 <= je_d en /\ je_sp0 en + je_d en <= 2 ^ 47 /\ 48 <= STK_pj_parse.
Proof.
intros en HPRE.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFWIN & _).
pose proof HFPRE as (HAFN & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
assert (HSTK : 4144 <= STK_pj_parse) by (apply Z.leb_le; vm_compute; reflexivity).
unfold je_sp1, je_sp0, PJP_FR. lia.
Qed.

(* ---- +0xc0 .. the cuts: `ld a0, 0(sp)`, `beq a0, a1` (a1 = end); taken: +0xe8 `mv a0, zero`, +0xec `j +0xd4`, the cut
   C3; not taken: the cut C2ref (+0xc8) ---- *)
Lemma pjp2_tail : forall en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran',
  pjp_pre (fx := fx) B ARx CTX0 CW en -> pjp_wb B CW en Sb ->
  pjp2_at en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran'
    (je_t0 en + je_len en - Z.of_nat (length (PjGrammar.skip r))) ->
  getr regs 11 = w64 (je_t0 en + je_len en) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (pjp_cfg fy PJP2_TAIL regs mem md) (pjp_FIN (fx := fx) (SK := SK) B ARx CW en).
Proof.
intros en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' HPRE HWB HA R11.
pose proof HA as (HINV & HROOM & HPV & HPOSPV & HOUTC & HCUR & HNODE & HNCAP & HOUT & HTXT & HTIE & HHU & HINJ).
pose proof HINV as (HFZ & HFK & HJ & HWIN0 & Hsp & Hra & Hs0 & Hs1 & H8 & H9 & HKP & Hpres & HRA24 & HROD & HMN).
pose proof HPRE as (HFPRE & HCLO & HDW1 & HDW2 & HROOM0 & HFZ0 & H10 & H11 & H12 & Hlen & HSRC0 & HHOME0 & HMAX &
  HFWIN & HSLOT & Hout & HLAM & HTXA & HLED0 & HCNT & HRQ & HBB & HFRB & HMN0 & HPKS & HPK24 & HTCEIL & HRQM & HHB0).
pose proof HPV as ((okr & Hjv) & HLED & HLM & HBM).
pose proof HLM as (Hoks & Hcnt' & Hfa' & HPL & HPD & HND & Hpk').
pose proof HBM as (Hnew & HPab & HPfr & Hhp).
destruct (pjp2_bounds en HPRE) as (Hq & Hd0 & Htop & HSTK).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Esp1 : je_sp1 en = je_sp0 en - 48) by reflexivity.
set (p2 := je_t0 en + je_len en - Z.of_nat (length (PjGrammar.skip r))) in *.
pose proof HCUR as (V1 & V2 & _ & _ & _ & Ht0' & Ht62' & Hp2r & _).
set (E2 := Eimg (Ereg regs [Z_to_bv 64 p2])).
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2; apply Eimg_env).
assert (EL2 : forall n (r0 : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r0 -> ew E2 n = getr regs r0).
{ intros n r0 Hn Hr0. unfold E2. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r0 Hr0). }
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 p2]) E2)
  by (unfold E2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E2 32 = Z_to_bv 64 p2)
  by (unfold E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E11 : ew E2 11 = Z_to_bv 64 (je_t0 en + je_len en)) by (rewrite (EL2 11%nat 11%bv ltac:(lia) eq_refl); exact R11).
assert (U2 : bv_unsigned (ew E2 2) = je_sp1 en).
{ rewrite (EL2 2%nat 2%bv ltac:(lia) eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs). exact Hsp. }
assert (U32 : bv_unsigned (ew E2 32) = p2) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E2 pjp2_ssT
  (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + PJP2_TAIL)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pjp2_ssT. apply (pa_entry_st_ok_full (fx := fy)).
  - unfold E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pjp2_regT, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E2 _ (je_sp1 en) 0 8 (SOff 32 0) p2);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
      | change (Z.of_N 8) with 8; lia | rewrite Z.add_0_r; exact V1].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - cbn. repeat split. }
assert (SHOK : sh_ok SEGS PJP2_Bx [] E2 (mrestrict (w_H W) mem)) by exact (Forall_nil _).
pose (RUN := paj_run_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  B prh_pst ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  RW (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  B prh_pst ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  RW (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fy) (L := A_prog_listing) (PI := PA) RW).
pose proof HMN as HPM.
pose proof (G_calls _ _ _ _ _ Hjv) as Hcl.
pose proof HLED0 as HLB0. apply prh_ledger_bounds in HLB0. destruct HLB0 as (_ & _ & Hcn0 & _).
unfold pjp_cfg. unfold SRr'.
paj_run_tok_x_invR RUN HS HJ SHOK HPM PJP2_Bspan.
{ pjs_nowr. }
pjs_ro0 HF HFr HG EM.
(* +0xc4: `beq a0, a1` on p (atom 32) and end (a1, atom 11) *)
psrr_branch_tok RUN BR HS SHOK PJP2_Bspan.
- (* p = end: the rest after the value is white space only; +0xe8 a0 := 0, +0xec j +0xd4: the cut C3 *)
  rewrite branch_eq_U, (U_atom E2 32 p2 E32 ltac:(lia)), (U_atom E2 11 _ E11 ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc.
  assert (Hsk : PjGrammar.skip r = []) by (apply length_zero_iff_nil; unfold p2 in Hc; lia).
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJP2_Bspan PJP_C3.
  { pjs_nowr. }
  pjs_ro HF HFr HG EM.
  pose proof (pjs_kept fy (w_H W) E2 _ _ regs _ ((2%bv : bv 5) :: (8%bv : bv 5) :: (9%bv : bv 5) :: PJP_KEPT) HS HAE2
    ltac:(vm_compute; reflexivity)) as RKE.
  prreg HS (10%bv : bv 5) R10e.
  pmkst HS.
  rewrite EM in HJ, HPM |- *.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?n)) ?mm _; cfg_model := ?dd |} _ =>
    replace n with PJP_C3 by (vm_compute; reflexivity);
    apply (SEG3 en Sb fy ly S Hp W rg mm dd k HPRE HWB) end.
  split.
  { apply (pjm_inv en Sb fy ly S Hp W regs mem md k ly S Hp _ _ _ k HINV HJ (fun x => eq_refl)).
    - unfold spZ. rewrite (RKE 2%bv) by pjp2_in. reflexivity.
    - exact (RKE 8%bv ltac:(pjp2_in)).
    - exact (RKE 9%bv ltac:(pjp2_in)).
    - intros r0 Hr0. exact (RKE r0 (or_intror (or_intror (or_intror Hr0)))). }
  assert (Hpost : PjGrammar.post (Some (t, r)) = Some t) by (unfold PjGrammar.post; rewrite Hsk; reflexivity).
  split; [exact HROOM|].
  (* the hull use: parse_value's (the cut's), inside pj_parse's list; skip_ws allocates nothing *)
  split; [exact (PjParseA_counts.pjc_hull_used_pv ReaderRes.jr_strtod _ _ _ HHU)|].
  exists ok, (Some t), tr, Lam', peak', cnt', fail', ran'.
  split; [rewrite (G_run _ _ _ _ _ Hjv), Hpost; reflexivity|].
  split; [exact Hoks|].
  split; [rewrite Hcnt'; apply Z.mod_small; lia|].
  split; [exact (proj1 (G_fail_after _ _ _ _) Hfa')|].
  split; [rewrite <- (pjg_gtrace (je_tl en)); exact Hpk'|].
  split; [rewrite Hlen in Hhp; change (Z.of_nat (PjGrammar.MAXD - 0)) with 32 in Hhp; lia|].
  split; [intros Hf; pose proof (G_fail_in _ _ _ _ _ _ _ _ _ _ _ Hjv Hoks Hf) as Hn; rewrite Hpost in Hn;
          discriminate Hn|].
  split; [intros Hf Hnr; destruct (G_norefuse _ _ _ _ _ _ _ Hjv Hf Hnr) as [Q1 Q2]; rewrite Hpost in Q1;
          exact (conj Q1 Q2)|].
  split; [exact HLED|].
  (* the text's position transfer: an accepted document makes the reader's events and no bulk (PresetReqAt.parse_evs
     at the outcomes ok of the run), so parse_value's transfer (the cut's pjp_pos_pv) is it *)
  assert (Ep : PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en) ok = PresetReqAt.rd_hevs tr).
  { unfold PresetReqAt.parse_evs, PresetReqAt.rtr, PjGrammar.jr_run. rewrite Hjv. cbn [fst snd].
    rewrite Hsk. cbv beta iota. apply app_nil_r. }
  split.
  { intros sm x os i H0 hist Hpos Hrun.
    rewrite Ep in Hrun |- *. exact (proj1 HPOSPV sm x os i H0 hist Hpos Hrun). }
  (* THE OUTCOME (the batch kit): at a run whose next events are the all-granted reading's, with no injected failure in its
     window, parse_value's outcome conjunct (the cut's pjp_outc) makes the reading the all-granted one; an accepted
     document makes no bulk under either outcome list *)
  split.
  { intros sm x os i H0 hist Hpos Hrun Hcons Hwin.
    assert (Egt : prhPv_gtrace 0 (je_tl en) = snd (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) [])).
    { rewrite (pjg_gtrace (je_tl en)). reflexivity. }
    assert (Ep0 : PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en) [] =
      PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en)) ++
      match fst (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) []) with
      | Some _ => [] | None => [PresetReqAt.HBulk (PresetReqAt.pj_frees ReaderRes.jr_strtod [] (je_tl en))] end).
    { rewrite Egt. reflexivity. }
    rewrite Ep0 in Hrun, Hcons. apply prh_run_at_app_iff in Hrun as (Hrun1 & _).
    rewrite length_app in Hcons. apply prh_cons_from_app_iff in Hcons as (Hcons1 & _).
    assert (Hwin' : je_fail en < je_cnt en \/
      je_cnt en + Z.of_nat (PjGrammar.calls (prhPv_gtrace 0 (je_tl en))) <= je_fail en).
    { rewrite Egt. exact Hwin. }
    destruct (HOUTC sm x os i H0 hist Hpos Hrun1 Hcons1 Hwin') as (Eran & Efst & h2 & Hpos2).
    destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en) []) as [[res0 tr0] okr0] eqn:Ev0.
    cbn [fst] in Efst. injection Efst as -> ->.
    pose proof (G_run _ _ _ _ _ Ev0) as Er0. rewrite Hpost in Er0.
    assert (Etr : prhPv_gtrace 0 (je_tl en) = tr).
    { unfold prhPv_gtrace. change prh_jr_strtod with ReaderRes.jr_strtod. rewrite Ev0. reflexivity. }
    split; [exact Eran|]. split; [exact Er0|].
    split; [rewrite Ep, Ep0, Etr, Er0; cbn [fst]; rewrite app_nil_r; reflexivity|].
    exists h2. rewrite Ep0, Etr, Er0, length_app. cbn [fst length]. rewrite Nat.add_0_r.
    rewrite Etr in Hpos2. exact Hpos2. }
  (* THE OUTCOME OF AN INJECTED READING (the text's GUARDED conjunct): the value was accepted, so no injected failure
     lies in the reading's window (pjp_g_fail_in: it would make the reading refused) *)
  split; [intros sm x os i H0 hist _ _ _ Hf; exfalso;
          pose proof (G_fail_in _ _ _ _ _ _ _ _ _ _ _ Hjv Hoks Hf) as Hn; rewrite Hpost in Hn; discriminate Hn|].
  split; [exact R10e|].
  exists D. split; [exact HPL|]. split; [exact HPD|]. split; [exact HND|]. split; [exact Hnew|].
  split; [rewrite <- G_ab_hbl; exact HPab|].
  split; [intros HH' n Hn; exact (HTIE HH' n Hn)|].
  split; [exact HNODE | exact HNCAP].
- (* p <> end: junk after the value; falls through to +0xc8: the cut C2ref *)
  rewrite branch_eq_U, (U_atom E2 32 p2 E32 ltac:(lia)), (U_atom E2 11 _ E11 ltac:(lia)) in Hc.
  apply Z.eqb_neq in Hc.
  assert (Hsk : PjGrammar.skip r <> []) by (intros E0; apply Hc; unfold p2; rewrite E0; cbn [length]; lia).
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJP2_Bspan PJP_C2REF.
  { pjs_nowr. }
  pjs_ro HF HFr HG EM.
  pose proof (pjs_kept fy (w_H W) E2 _ _ regs _ ((2%bv : bv 5) :: (8%bv : bv 5) :: (9%bv : bv 5) :: PJP_KEPT) HS HAE2
    ltac:(vm_compute; reflexivity)) as RKE.
  pmkst HS.
  rewrite EM in HJ, HPM |- *.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?n)) ?mm _; cfg_model := ?dd |} _ =>
    replace n with PJP_C2REF by (vm_compute; reflexivity);
    apply (SEG2R en Sb fy ly S Hp W rg mm dd k HPRE HWB) end.
  split.
  { apply (pjm_inv en Sb fy ly S Hp W regs mem md k ly S Hp _ _ _ k HINV HJ (fun x => eq_refl)).
    - unfold spZ. rewrite (RKE 2%bv) by pjp2_in. reflexivity.
    - exact (RKE 8%bv ltac:(pjp2_in)).
    - exact (RKE 9%bv ltac:(pjp2_in)).
    - intros r0 Hr0. exact (RKE r0 (or_intror (or_intror (or_intror Hr0)))). }
  split; [exact HROOM|].
  split; [exact HHU|].
  (* pj_free's order list F of out's tree at DOC_D (>= depth t, PjGrammar.jr_value_depth) *)
  assert (HdD : (PjTree.depth t <= DOC_D)%nat).
  { pose proof (G_depth _ _ _ _ _ _ Hjv) as Hdep. unfold DOC_D. lia. }
  destruct (HTIE HH DOC_D HdD) as (F & HFO0 & HTIEF).
  exists ok, (Some (t, r)), tr, D, F, Lam', peak', cnt', fail', ran'.
  split; [exact HPV|].
  split; [exact HPOSPV|].
  split; [exact HOUTC|].
  split; [unfold PjGrammar.post; destruct (PjGrammar.skip r) eqn:Esk;
          [exfalso; first [exact (Hsk Esk) | exact (Hsk eq_refl)] | reflexivity]|].
  split; [exact HFO0|].
  split; [exact HTIEF|].
  split; [exact HOUT | exact HINJ].
Qed.

(* ---- +0xbc: `sd a2, 0(sp)` (a2 = p2, the loop's exit), then the tail ---- *)
Lemma pjp2_exit : forall en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran',
  pjp_pre (fx := fx) B ARx CTX0 CW en -> pjp_wb B CW en Sb ->
  pjp2_at en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran'
    (je_t0 en + je_len en - Z.of_nat (length r)) ->
  getr regs 11 = w64 (je_t0 en + je_len en) ->
  getr regs 12 = w64 (je_t0 en + je_len en - Z.of_nat (length (PjGrammar.skip r))) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (pjp_cfg fy PJS_EXIT regs mem md) (pjp_FIN (fx := fx) (SK := SK) B ARx CW en).
Proof.
intros en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' HPRE HWB HA R11 R12.
destruct (pjp2_bounds en HPRE) as (Hq & Hd0 & Htop & HSTK).
pose proof HA as (HINV & HROOM & HPV & HPOSPV & HOUTC & HCUR & _).
pose proof HINV as (HFZ & HFK & HJ & HWIN0 & Hsp & Hra & Hs0 & Hs1 & H8 & H9 & HKP & Hpres & HRA24 & HROD & HMN).
pose proof HPV as ((okr & Hjv) & _).
pose proof HCUR as (V1 & V2 & V3 & Hrw & Hal8 & Ht0 & Ht62 & Hp0 & Hlen & Hg & Hap & Hdd).
pose proof (G_rest (je_tl en) ok t r tr okr (je_t0 en) Hjv) as [Hrl _].
pose proof (PjGrammar.skip_len r) as Hsl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Esp1 : je_sp1 en = je_sp0 en - 48) by reflexivity.
set (p2 := je_t0 en + je_len en - Z.of_nat (length (PjGrammar.skip r))) in *.
assert (Hp2 : je_t0 en <= p2 <= je_t0 en + je_len en) by (unfold p2; lia).
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall n (r0 : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r0 -> ew E n = getr regs r0).
{ intros n r0 Hn Hr0. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r0 Hr0). }
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (unfold E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (U2 : bv_unsigned (ew E 2) = je_sp1 en).
{ rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs). exact Hsp. }
assert (E12 : ew E 12 = Z_to_bv 64 p2) by (rewrite (EL 12%nat 12%bv ltac:(lia) eq_refl); exact R12).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E pjp2_ssX
  (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + PJS_EXIT)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pjp2_ssX. apply (pa_entry_st_ok_full (fx := fy)).
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pjp2_regX, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2. change (2 ^ 3) with 8. lia. }
assert (SHOK : sh_ok SEGS PJP2_Bx [] E (mrestrict (w_H W) mem)) by exact (Forall_nil _).
pose (RUNTO := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  B prh_pst ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  RW (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose proof HMN as HPM.
unfold pjp_cfg. unfold SRr'.
paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJP2_Bspan PJP2_TAIL.
{ (* the store writes the p word [sp1, sp1 + 8): pj_parse's own frame, inside the widened window *)
  intros a (r0 & Hin & Hr0). destruct Hin as [<- | []]. unfold pjp2_regX in Hr0.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr0. rewrite U2 in Hr0. left. lia. }
(* the memory after the store: changed only in [sp1, sp1 + 8), every present byte still present *)
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (je_sp1 en <= a < je_sp1 en + 8) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha.
  intros (r0 & Hin & Hr0). destruct Hin as [<- | []]. unfold pjp2_regX in Hr0.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr0. rewrite U2 in Hr0. lia. }
assert (HK8 : pjp2_kept8 (w_H W) mem (ms_mem ms) (je_sp1 en)) by exact (conj KV HG).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E' := Ex) in * end.
assert (EE : forall n, (n < 512)%nat -> ew E' n = ew E n)
  by (intros n0 Hn0; subst E'; rewrite ?ew_ewset_other by lia; reflexivity).
assert (ED : ed E' = ed E) by (subst E'; reflexivity).
assert (AG : env_agree 32 (Ereg regs []) E').
{ split.
  - intros i Hi. rewrite EE by lia. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
  - rewrite ED. unfold E. reflexivity. }
(* the stored word: the region's chunk at sp1 + 0, a2's value p2 *)
assert (U2' : bv_unsigned (ew E' 2) = je_sp1 en) by (rewrite EE by lia; exact U2).
assert (U12' : U E' (SOff 12 0) = p2) by (apply U_atom; [rewrite EE by lia; exact E12 | lia]).
assert (Vp2 : val_mem SEGS (rdW W (ms_mem ms)) (je_sp1 en) 8 p2).
{ refine (pjp2_val fy E' _ _ 2 0 8 (SOff 12 0) p2 (je_sp1 en) (je_sp1 en) HS _ U2' _ U12' _ _).
  - vm_compute. reflexivity.
  - lia.
  - cbn. lia.
  - cbn. lia. }
pose proof (pjs_kept fy (w_H W) E' _ _ regs _ ((2%bv : bv 5) :: (8%bv : bv 5) :: (9%bv : bv 5) :: (11%bv : bv 5) ::
  PJP_KEPT) HS AG ltac:(vm_compute; reflexivity)) as RKE.
pmkst HS.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?n)) ?mm _; cfg_model := ?dd |} _ =>
  replace n with PJP2_TAIL by (vm_compute; reflexivity);
  apply (pjp2_tail en Sb fy ly S Hp W rg mm dd k ok t r tr D Lam' peak' cnt' fail' ran' HPRE HWB) end.
- apply (pjp2_at_store en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' _ _ _ _ p2 HA HJ HPM
    HK8 Hq Hd0 Htop).
  + unfold spZ. rewrite (RKE 2%bv) by pjp2_in. reflexivity.
  + exact (RKE 8%bv ltac:(pjp2_in)).
  + exact (RKE 9%bv ltac:(pjp2_in)).
  + intros r0 Hr0. exact (RKE r0 (or_intror (or_intror (or_intror (or_intror Hr0))))).
  + exact Vp2.
  + exact Hp2.
- rewrite (RKE 11%bv) by pjp2_in. exact R11.
Qed.

(* ---- THE SEGMENT ---- *)
Theorem pjp_seg_C2ok_holds : pjp_seg_C2ok (SK := SK) B ARx CTX0 CW.
Proof.
intros en Sb fy ly S Hp W regs mem md k HPRE HWB HC.
destruct HC as (HINV & HROOM & HHU & ok & t & r & tr & D & Lam' & peak' & cnt' & fail' & ran' & HPV & HPOSPV & HOUTC &
  HCUR & HNODE & HNCAP & HOUT & HTXT & HTIE & HINJ).
assert (HA : pjp2_at en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran'
  (je_t0 en + je_len en - Z.of_nat (length r)))
  by exact (conj HINV (conj HROOM (conj HPV (conj HPOSPV (conj HOUTC (conj HCUR (conj HNODE (conj HNCAP
    (conj HOUT (conj HTXT (conj HTIE (conj HHU HINJ)))))))))))).
destruct (pjp2_bounds en HPRE) as (Hq & Hd0 & Htop & HSTK).
pose proof HINV as (HFZ & HFK & HJ & HWIN0 & Hsp & Hra & Hs0 & Hs1 & H8 & H9 & HKP & Hpres & HRA24 & HROD & HMN).
pose proof HPV as ((okr & Hjv) & _).
pose proof HCUR as (V1 & V2 & V3 & Hrw & Hal8 & Ht0 & Ht62 & Hp0 & Hlen & Hg & Hap & Hdd).
pose proof HTXT as ((HBY & H4096 & Htc & Htam & HTRA & Hth) & Hhome).
pose proof (G_rest (je_tl en) ok t r tr okr (je_t0 en) Hjv) as [Hrl Erest0].
pose proof YM05.alloc_ceiling_lt as Hcl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Esp1 : je_sp1 en = je_sp0 en - 48) by reflexivity.
assert (Erest : skipn (Z.to_nat (je_t0 en + je_len en - Z.of_nat (length r) - je_t0 en)) (je_tl en) = r).
{ rewrite <- Hlen. exact Erest0. }
set (p0 := je_t0 en + je_len en - Z.of_nat (length r)) in *.
set (E := Eimg (Ereg regs [Z_to_bv 64 p0; Z_to_bv 64 (je_t0 en + je_len en)])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall n (r0 : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r0 -> ew E n = getr regs r0).
{ intros n r0 Hn Hr0. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r0 Hr0). }
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 p0; Z_to_bv 64 (je_t0 en + je_len en)]) E)
  by (unfold E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 p0)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (je_t0 en + je_len en))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U2 : bv_unsigned (ew E 2) = je_sp1 en).
{ rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs). exact Hsp. }
assert (U32 : bv_unsigned (ew E 32) = p0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = je_t0 en + je_len en) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E pjp2_ssA
  (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + PJP_C2OK)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pjp2_ssA. apply (pa_entry_st_ok_full (fx := fy)).
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pjp2_regA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E _ (je_sp1 en) 0 8 (SOff 32 0) p0);
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | change (Z.of_N 8) with 8; lia | rewrite Z.add_0_r; exact V1].
    + apply (chunk_ok_val SEGS E _ (je_sp1 en) 8 8 (SOff 33 0) (je_t0 en + je_len en));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | change (Z.of_N 8) with 8; lia | exact V2].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - cbn. repeat split. }
assert (SHOK : sh_ok SEGS PJP2_Bx [] E (mrestrict (w_H W) mem)) by exact (Forall_nil _).
pose (RUN := paj_run_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  B prh_pst ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  RW (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  B prh_pst ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  RW (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fy) (L := A_prog_listing) (PI := PA) RW).
pose proof HMN as HPM.
unfold pjp_cfg. unfold SRr'.
(* ---- +0x50 .. +0x58: p and end reloaded from the cursor, `bgeu a3, a1` ---- *)
paj_run_tok_x_invR RUN HS HJ SHOK HPM PJP2_Bspan.
{ pjs_nowr. }
pjs_ro0 HF HFr HG EM.
psrr_branch_tok RUN BR HS SHOK PJP2_Bspan.
- (* p >= end: the value read the whole text (r = []); taken to +0xc0, the tail with nothing stored *)
  rewrite branch_geu_U, (U_atom E 32 p0 E32 ltac:(lia)), (U_atom E 33 _ E33 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Er : r = []) by (apply length_zero_iff_nil; unfold p0 in Hc; lia).
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJP2_Bspan PJP2_TAIL.
  { pjs_nowr. }
  pjs_ro HF HFr HG EM.
  pose proof (pjs_kept fy (w_H W) E _ _ regs _ ((2%bv : bv 5) :: (8%bv : bv 5) :: (9%bv : bv 5) :: PJP_KEPT) HS HAE
    ltac:(vm_compute; reflexivity)) as RKE.
  pmkst HS.
  rewrite EM in HJ, HPM |- *.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?n)) ?mm _; cfg_model := ?dd |} _ =>
    replace n with PJP2_TAIL by (vm_compute; reflexivity);
    apply (pjp2_tail en Sb fy ly S Hp W rg mm dd k ok t r tr D Lam' peak' cnt' fail' ran' HPRE HWB) end.
  + replace (je_t0 en + je_len en - Z.of_nat (length (PjGrammar.skip r))) with p0
      by (unfold p0; rewrite Er; reflexivity).
    apply (pjp2_at_regs en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' _ _ _ HA HJ).
    * unfold spZ. rewrite (RKE 2%bv) by pjp2_in. reflexivity.
    * exact (RKE 8%bv ltac:(pjp2_in)).
    * exact (RKE 9%bv ltac:(pjp2_in)).
    * intros r0 Hr0. exact (RKE r0 (or_intror (or_intror (or_intror Hr0)))).
  + rewrite (pjs_reg_off fy (w_H W) E _ _ 11%bv 33 0 (je_t0 en + je_len en) HS eq_refl E33 ltac:(lia) ltac:(lia)),
      Z.add_0_r.
    reflexivity.
- (* p < end: +0x5c .. +0x70, the loop's registers; to the loop head +0x74 *)
  rewrite branch_geu_U, (U_atom E 32 p0 E32 ltac:(lia)), (U_atom E 33 _ E33 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJP2_Bspan PJS_LOOP.
  { pjs_nowr. }
  pjs_ro HF HFr HG EM.
  pose proof (pjs_kept fy (w_H W) E _ _ regs _ ((2%bv : bv 5) :: (8%bv : bv 5) :: (9%bv : bv 5) :: PJP_KEPT) HS HAE
    ltac:(vm_compute; reflexivity)) as RKE.
  prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15.
  pose proof (pjs_reg_off fy (w_H W) E _ _ 10%bv 32 0 p0 HS eq_refl E32 ltac:(lia) ltac:(lia)) as R10.
  pose proof (pjs_reg_off fy (w_H W) E _ _ 11%bv 33 0 (je_t0 en + je_len en) HS eq_refl E33 ltac:(lia) ltac:(lia))
    as R11.
  pose proof (pjs_reg_off fy (w_H W) E _ _ 12%bv 32 0 p0 HS eq_refl E32 ltac:(lia) ltac:(lia)) as R12.
  pose proof (pjs_reg_off fy (w_H W) E _ _ 13%bv 32 0 p0 HS eq_refl E32 ltac:(lia) ltac:(lia)) as R13.
  rewrite Z.add_0_r in R10, R11, R12, R13.
  pmkst HS.
  rewrite EM in HJ, HPM |- *.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?n)) ?mm _; cfg_model := ?dd |} _ =>
    replace n with PJS_LOOP by (vm_compute; reflexivity);
    refine (pjs_loop (SK := SK) B prh_pst ARx LAWS RW (wle'_refl SEGS YGcfRehidePost.RZ_cf)
      (wle'_trans SEGS YGcfRehidePost.RZ_cf) (Z.to_nat (je_t0 en + je_len en - p0))
      (pjp_FIN (fx := fx) (SK := SK) B ARx CW en)
      fy W rg mm dd (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)] (je_ly en) Sb
      (je_Hp en) (je_W en) (je_mem en) (je_md en) [] ly S Hp k (je_t0 en) (je_tl en) r p0
      _ HJ HPM _ R10 _ R12 R13 R14 R15 H4096 _ HBY HTRA _ _ _) end.
  + rewrite Hlen. lia.
  + rewrite (RKE 9%bv) by pjp2_in. exact H9.
  + rewrite Hlen. exact R11.
  + lia.
  + rewrite Hlen. lia.
  + rewrite Erest. reflexivity.
  + (* the loop's exit +0xbc: the state with the loop's registers, the memory C2ok's *)
    intros regs' md' HJ' KP R12'.
    apply (pjp2_exit en Sb fy ly S Hp W regs' mem md' k ok t r tr D Lam' peak' cnt' fail' ran' HPRE HWB).
    * apply (pjp2_at_regs en Sb fy ly S Hp W regs mem md k ok t r tr D Lam' peak' cnt' fail' ran' _ _ _ HA HJ').
      -- unfold spZ. rewrite (KP 2%bv) by pjs_in. rewrite (RKE 2%bv) by pjp2_in. reflexivity.
      -- rewrite (KP 8%bv) by pjs_in. exact (RKE 8%bv ltac:(pjp2_in)).
      -- rewrite (KP 9%bv) by pjs_in. exact (RKE 9%bv ltac:(pjp2_in)).
      -- intros r0 Hr0. rewrite (KP r0) by (cbn [In PJP_KEPT] in Hr0; cbn [In PJS_KEPT]; tauto).
         exact (RKE r0 (or_intror (or_intror (or_intror Hr0)))).
    * rewrite (KP 11%bv) by pjs_in. exact R11.
    * rewrite Hlen in R12'. exact R12'.
Qed.

End c.

Check @pjp_seg_C2ok_holds.
Print Assumptions pjp_seg_C2ok_holds.
