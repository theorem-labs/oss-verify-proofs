(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1213 of its 1267 lines of code are new or changed and 724 lines of the source are left out. *)
(* THE FREE / REALLOC MOVE (S3 phase D, a Theorem Labs lane; plan rows D-2 .. D-12, rule F12): every tx_put call crosses the
   grow's free, so the text concludes SRr' segs RZ_cf with the post's journal at WR := wle' SEGS RZ_cf. The entry
   segment A (ts_A_cps: the prologue and frame_alloc_0, no free) runs at wle as before and is lifted once at its top
   (YGcfRhLift.ra_rh_of_SRr, a lift of that plain segment); its continuation gets the wle journal. THE ONE JOURNAL
   LIFT is at the cut B, the top of ts_at_B_B (ajournal_xwR_mono with YA0nH.wle_wle'); from there every journal is at
   WR (liveb = TxStr102Glue's ts_liveR at WR), every segment is SRW (SRr' at RZ_cf), the runners and the flag store
   are the R forms at WR, and ts_put_call / ts_LH / ts_loop are the glue's (at RCF = WR). The `ret` step is lifted by
   YA0nH.SRr_SRr'. HULL (R2320, row D-11): the text's `(length rp_os <= 4)%nat` is the Section-g hypothesis HOS,
   passed to the glue's ts_put_call (its premise right after the TS_ks split, in a2's glue). *)
(* fuzz_preset IMAGE B' (asan-ubsan #102 pin d663f82d7f48; unstripped twin c90d4fa54d43; RELOCATED from B f8f98a95bc52): the walk of tx_string
   (fuzz_preset.c :374-396; 221 instructions from slot 4221 of lib/B/Listing_prog.v, B' 0x858c0) against the Tx part's
   text ttx_string_specX (lib/A/PRH_FnTx.v 7cf918708def :665-720: the rp_* binders, the entry premise
   PresetRoomPos.iface_room_pos, the hull premise `(length rp_os <= 4)%nat`, the run premise, the room and the consumer
   window guarded by f0 = 0, the post SRr' segs RZ_cf over ONE BUDGETED fpostWbmR at wle' segs RZ_cf (fQmn: the memnorm
   keep) naming the outcome prhtx_out over what was ACTUALLY appended, DEAD-TXSTRING and the exact-or-frozen position),
   in cgif's per-function form over the listing engine (YC80x / YC1fPx over YCbqG's ajournal_x, caller-window form:
   YCbqGcallW.v ajournal_x_init_W). Every conclusion is `srealizes` through SRr'. This file holds ONLY image B': the
   seam offsets and literal addresses (read from the neutral listing of twin c90d4fa5), the image facts, and the runs
   over PL_prog_B. Everything image-generic is the #102 glue lib/A/Prog/TxStr102Glue.v (owner h-rw-pre-5, lane
   TxStrBp) over BTxValueB's lib/A/Prog/Tx102Glue.v (the text state), instantiated here at PI_prog_B, the
   whole-program instance (PALib is satisfiable only there). BASE: the kit's cut
   7cdbb61b5fa0 (merged forward); B' listing c97cc46b3e13 / PAImg_prog 15fab93fe702.
   RE-WALK FOR #102 (donor cold/h-rw-pre-5-b-tx 043041dbb091, Qed against the old-pin texts with the fabortW arm):
   prhtx_rec takes f, prh_ledger takes most / own, prhtx_fp is 28 bytes, and tx_put's post has THREE outcomes and no
   abort arm, so every call site continues on every outcome and the live state carries the buffer, failed, own and
   the appended prefix; the instruction-level segments are the donor's, relocated (3e23de6bf8c9, audited AGREE).
   THE BATCH KIT, NOW THE KIT'S CUT 7cdbb61b5fa0 (PRH_FnTx.v 88468bf162d8 at the cut; first fitted as a prep on a
   working branch over the batch kit's cdde0ed15730); now in PRH_FnTx.v 7cf918708def the text drops DW (:414 / :671),
   takes the guarded room and consumer window (:677 / :682: Section-g HROOMW / HCONS, carried into the glue's
   ts_pre), states DEAD-TXSTRING (:706) and a BUDGETED post fpostWbmR at wle' segs RZ_cf (wbudget_if f0 [] k) under
   SRr' segs RZ_cf (:695-696). Every lemma name kept; the changes here: Section f CTX0 alone, TXPUT and HCL
   without DW, HROOMW / HCONS, the ts_pre chains, the journal REBASED where the live state is built (ts_at_B_B) and
   where the flag-store run starts (ts_at_G_B), the post at G budgeted (the side facts' budget, the rebased journal
   unbased by YCbqGwild.ajournal_xw_unbase0R), the top theorem's binders / premises in the batch's order.
   THE MEMNORM KEEP. fpostWbm asks `memnorm mem -> memnorm mem'` from the entry to the return. Runs: YGcallMxmn.v's
   memnorm_frame_of (the run's full-memory frame_of from its start st_ok); the tx_put calls: the glue (s10_call_WbmR);
   frame_alloc_0: the stack_malloc rule is aj_stack_malloc_at_xm (YGcallMxmn.v:812) with ASM0 the m-form contract
   astack_malloc_realizes_xm (YGcallMxmn.v:303). The rule changed from aj_stack_malloc_at_x to _xm ONLY because
   fpostWbm needs the keep: aj_stack_malloc_at_x's post states the new memory through aview only, so no keep follows
   from it; the premises are identical (count premise HCNT from the text's own entry premise, as before).
   RULE 24: proves function tx_string (image B'). STATUS: tx_string_B_holds closes the walk (loop body BTxStep.ts_step_B).
   Reuse search
   (2026-10-29T01:01-01:36Z): proof-index tx_string /
   tx_value / tx_put (index v5 built 2026-10-28T23:48:31Z, each rc=0) + an unpiped git grep by name, by the B and A
   entry addresses (85494 / 85014 / 84e40 / 85808; 84e70 / 84a80 / 84908 / 851d0) over 374 shas carrying
   proofs/omx-clap-core/fuzz_preset (the four released refs, regen/fuzz-preset-ran-out-proofs, h-rw-pre-5-port-core,
   h-mani-a8-preset-alloc, every cold/h-hpreset-7-*, every cold/h-rw-pre-*, c-omx-alloc-preset-s1, port-fm*,
   port-grant*, pg-core*; every rc 0 or 1, checker CONFIRM): NO donor (released hits are preset's plain / UBSan SR
   proofs; no file mentions paj_run_x / ajournal_x / fpostW / PL_prog_B / PI_prog_B). Templates (old vocabulary,
   read only): cold/h-rw-pre-3-crtcc lib/B/Prog/tx_string.v. Shared glue: S10 (above).
   SEGMENTS, as S10TxString.v (image A): fresh symbolic states from concrete facts at each seam, environment TE regs0
   regsc more (atoms 0-31 entry registers, 32-63 current ones, 64- extras). B's prologue is A's byte for byte up to
   frame_alloc_0's return (B 0x858c0 .. 0x85934), so the A1 / A2 / A3 seams are the same offsets.
   NUMERALS. DERIVED: the seam offsets 92 / 96 / 116 / 276 / 348 / 668 / 688 (4 * the listing slot from tx_string's
   entry: B 0x8591c / 0x85920 / 0x85934 / 0x859d4 / 0x85a1c / 0x85b5c / 0x85b70) and the same seams from the listing
   base, as a run's pc states them (TS_PC_B + 276 / 348 / 668 / 688 = 17160 / 17232 / 17552 / 17572), the literal
   offsets 70432 / 70464 / 70368 from
   pa_val (A_OBJ 2) (the listing's PAddHi (A_OBJ 2) 0x11320 / 0x11340 / 0x112e0: .str.27, .str.28, tx_string.hex),
   atom indices. LENGTH: 64, 160, 176, 4096, 2 ^ 31 / 2 ^ 46 / 2 ^ 47. No ADDRESS literal: code addresses are
   pa_sigma / pa_val of lib/B/PAImg_prog.v. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
(* the memnorm keep: YAkMemnorm's memnorm, YGcallMxmn's m-form stack_malloc rule and memnorm_frame_of (Required
   qualified: YGcallMxmn carries its own copies of in_roP / arodata_okP) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YCbqGwild.
(* the re-hiding relation WR, its step relation, and the lift of a plain segment (the free / realloc move) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue TxStr102Glue.
(* pa_slot_lt_ceil_b (fpre's raZ bound at a call), generic in the listing, by path from walk-S7B c50d0958c0b; it loads
   YF0v.v, which sets the zify division flag to false globally: the #[local] reset below follows it *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
(* the loop body (sub-lane BTxStep, cold/h-rw-pre-5-b-txq 49a798cd1e08), Required qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require BTxStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image B: tx_string's entry, its seams (DERIVED; see the header) ---- *)
Definition TS_PC_B : Z := 4 * Z.of_nat (B_prog_slot AS_tx_string).
Definition TS_A2_OFF_B : Z := 92.    (* 0x8591c: lw a2, 0(a2), the use-after-return flag *)
Definition TS_A3_OFF_B : Z := 96.    (* 0x85920 *)
Definition TS_B_OFF_B : Z := 116.    (* 0x85934: frame_alloc_0's return *)
Definition TS_C_OFF_B : Z := 276.    (* 0x859d4: the opening quote's return *)
Definition TS_LH_OFF_B : Z := 348.   (* 0x85a1c: the loop head (li a0, 6; sb a0, 4(s10)) *)
Definition TS_G_OFF_B : Z := 688.    (* 0x85b70: the closing quote's return *)
Definition TS_X_OFF_B : Z := 668.    (* 0x85b5c: the closing quote's block *)
Definition TS_SPAN_B : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* (* DELETE when S10TxStrGlue carries it *) B-local copy of S10TxString.v's ts_list_cases (walk-S10 21e90e1b0e3 :66) *)
Lemma ts_list_cases_B : forall (l : list Z), l = [] \/ exists x l', l = x :: l'.
Proof. intros [|x l]; [left; reflexivity | right; exists x, l; reflexivity]. Qed.
(* B-local copy of S10TxString.v's tskeep (walk-S10 18165859e13 :69; DELETE when S10TxStrGlue carries it): a register a
   run did not write keeps the segment's start value (the run's env may extend the segment's TE by fresh atoms) *)
Ltac tskeep_B HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Notation STKS := (@STK_tx_string prh_img_B).
#[local] Notation TEb := (TE (L := B_prog_listing) (PA := PA)).

Definition TS_STR27_B : Z := VAL (A_OBJ 2) + 70432.   (* .str.27, the quote *)
Definition TS_STR28_B : Z := VAL (A_OBJ 2) + 70464.   (* .str.28, the backslash *)
Definition TS_HEX_B : Z := VAL (A_OBJ 2) + 70368.     (* tx_string.hex, the 16 digits *)

Lemma TS_PC_val_B : BASE + TS_PC_B = SIGMA AS_tx_string.
Proof. vm_compute. reflexivity. Qed.
(* the glue's image facts at B *)
Lemma pa_hi_ok_B : @pa_hi _ B_prog_listing PA <= 2 ^ 31.
Proof. vm_compute. discriminate. Qed.
(* the whole-program instance's image bounds lie in the ASan low memory (Tx102Glue.v s10_src_img's img_box) *)
Lemma img_box_B : 4096 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= kLowMemEnd.
Proof. vm_compute. split; discriminate. Qed.
Lemma HSTK_B : 4096 + 176 <= STKS.
Proof. vm_compute. discriminate. Qed.
Lemma pst_img_B : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact pst_in_img_B. Qed.
Lemma HSTKP_B : 0 <= @STK_tx_put prh_img_B /\ @STK_tx_put prh_img_B + 176 <= STKS.
Proof. split; vm_compute; discriminate. Qed.
Lemma pst_ro_B : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact pst_not_ro_B. Qed.
(* fpre's raZ bound at B's two tx_put return slots (C: the opening quote's, 17160 = TS_PC_B + 276;
   G: the closing quote's, 17572 = TS_PC_B + 688), each a CLOSED lemma (PRW_StepKit.v pa_slot_lt_ceil_b; vm_compute
   only on the closed slot test, never inside a walk) *)
Lemma ts_ret_ceil_C_B : bv_unsigned (Z_to_bv 64 (BASE + 17160)) < YM05.alloc_ceiling.
Proof.
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA) 17160 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
pose proof (@pa_B_ok _ _ PA) as HB. rewrite unsigned_lit_small by lia. exact H.
Qed.
Lemma ts_ret_ceil_G_B : bv_unsigned (Z_to_bv 64 (BASE + 17572)) < YM05.alloc_ceiling.
Proof.
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA) 17572 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
pose proof (@pa_B_ok _ _ PA) as HB. rewrite unsigned_lit_small by lia. exact H.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
(* THE RELATION after the cut B (F12): the journal from the entry at WR, every segment at SRW *)
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation SRW := (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx WR).
#[local] Notation WRrefl := (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRtrans := (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf).
(* the allocator laws at the cf instance's head (engine fold, YCbqG 83da015952be: 16 fields) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B: PALib's fields). Taken at PI_prog_B, the whole-program
   instance, where A_OBJ 1 is the UAR flag's GOT word (0xa28a8): satisfiable (owner ruling 2026-10-29 06:05Z) *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
(* MARKED STAND-IN (owner a Theorem Labs lane / the core's PALib; a Theorem Labs lane's ruling): the listing's frame_alloc_0 is the code record's *)
Hypothesis pal_stack_malloc0 : SIGMA AS___asan_stack_malloc_0 = pc_stack_malloc (as_code B) 0.
(* MARKED STAND-IN (owner a Theorem Labs lane / the core's PALib): the flag cell lies in the image, PER-INSTANCE over the CfImg bounds
   (TxStr102Glue.v's form; at CfImg_B: B' 0xab700, 4 bytes of .bss, inside [0x10000, 0x601000)) *)
Hypothesis pal_uar_img : @cf_img_lo ci <= as_uar_cell B /\ as_uar_cell B + 4 <= @cf_img_top ci.
(* the CfImg bounds are a low range, and the instance's pa_lo / pa_hi lie inside them (closed image facts at CfImg_B:
   BTxStrWitB.v tsw_cf_img_ok_B / tsw_img_cf_box_B) *)
Hypothesis cf_img_ok : 0 <= @cf_img_lo ci /\ @cf_img_top ci <= 2 ^ 31.
Hypothesis img_cf_box : @cf_img_lo ci <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= @cf_img_top ci.
(* SRC-CEIL RETIRED (on the cut 7cdbb61b5fa0, the internal file MIGRATION.md, section 4): the stand-in hypothesis is DELETED. The cut's
   src_rd states `p + len <= alloc_ceiling` (no `+ 8`), and TxStr102Glue.v ts_src_byte takes that bound from the
   string's prhtx_bvis granule bound, as BTxValue did *)
(* ---- frame class 0 (frame_alloc_0): the m-form contract astack_malloc_realizes_xm (YGcallMxmn.v:303 = FCiface.v's
   frozen astack_malloc_realizes_x plus the memnorm keep; owner the h-hpreset-7 frame-class lane,
   stack_malloc0_contract_xm) and exactly the hypotheses of YGcallMxmn.v's aj_stack_malloc_at_xm (= YGcallSx.v's
   aj_stack_malloc_at_x's). _xm in place of _x ONLY because fpostWbm needs the keep (header) ---- *)
Hypothesis ASM0 : YGcallMxmn.astack_malloc_realizes_xm SEGS B ARx 0.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
(* ---- the glue's Section hypotheses (Tx102Glue.v / TxStr102Glue.v, MARKED there) ---- *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (owner h-mani-a8; its rule 2026-10-29 18:56Z): PER-INSTANCE over the CfImg bounds cf_img_lo /
   cf_img_top (generated per image: B' 0x10000 / 0x601000), the form of h-mani-a8's img_shadow_vis_cf (YGcfAmx2.v);
   its B' instance tfib_img_shadow_vis_cf_B (lib/AU/AImgShadowVisCfB.v, cold/h-mani-a8-alloc102) when it lands *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
  @cf_img_lo ci <= a < @cf_img_top ci ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the callee's text (K0Tx, PRH_FnTx.v 7cf918708def :414-474, the budgeted tx_put under SRr' segs RZ_cf) at the
   caller's universe closure CTX0 (the batch drops DW): tx_put is a HELD slice (its NULL site changes with the fixed
   harness), so its text is a hypothesis here *)
Variables (CTX0 : list (list Z)).
Hypothesis TXPUT : ttx_put_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* MARKED STAND-IN (owner a Theorem Labs lane, the image binding of B; a Theorem Labs lane's ruling 2026-10-29 ~05:45Z): alloc.c's statics are not
   the runtime's own statics and not errno, so a runtime call's image clause (acall_kept) keeps them *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* ---- frame class 0's inline release (B 0x85bac / 0x85bb0): exactly the hypotheses of YGcallSx.v's aj_flag_store_x
   (engine fold), as S10TxString.v (image A) states them ---- *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* MARKED STAND-IN (owner h-mani-a8; WalkS10's ruling 2026-10-29): the frame's flag byte is present, so the epilogue's
   flag store has a writable region (discharged at ARcf by AR_flag_law_ok_cf's first conjunct, as WalkH2H5's
   H5CrtS7.v crt7_fflx does) *)
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* MARKED STAND-IN (owner h-mani-a8; WalkS10's ruling 2026-10-29): fake frames are 64-aligned. Needed because esc[]
   (F + 32, up to 6 bytes) is handed to tx_put, whose src_rd asks for the shadow hull of [F + 32, F + 38); the frame's
   own 8 shadow bytes cover that hull only when shadow_addr F is 8-aligned, i.e. F mod 64 = 0 (the base gives only
   F mod 32 = 0). Discharged at ARcf by frame_facts_cf's page-aligned fake stack; cgif's analogue at its AR is
   YCem.v:191-192 (frame_addr .. mod 64 = 0 from frame_facts' page alignment) *)
Hypothesis FAL64 : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0.
(* ---- the two quote literals (MARKED STAND-IN, owner a Theorem Labs lane, the image binding of B: .str.27 / .str.28, one byte each,
   zero shadow) and tx_string.hex (MARKED STAND-IN, owner a Theorem Labs lane, the image binding of B: 16 digits in two zero-shadow
   granules of .rodata) ---- *)
Hypothesis ts_lit_img_B : kept_img (PA := PA) B TS_STR27_B 1 /\ kept_img (PA := PA) B TS_STR28_B 1.
Hypothesis ts_hex_img_B : kept_at (PA := PA) B [] TS_HEX_B 16.
(* the glue's Context facts, at image B, for the implicit arguments a glue lemma leaves after refine / Unshelve *)
Ltac ts_ctx_B := first [exact HSTK_B | exact HSTKP_B | exact pa_hi_ok_B | exact LAWS | exact PAL | exact pal_uar_img
  | exact pst_img_B | exact pst_ro_B | exact pal_pst_static | exact TXPUT | exact zs_aligned | exact img_shadow_vis_x
  | exact img_box_B | exact img_cf_box | exact cf_img_ok | idtac].
(* the flag-store runner at WR (plan row D-5): YGcallSx.v's aj_flag_store_xR at image B's listing, R := WR *)
Definition ts_flag_store_B := aj_flag_store_xR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) ASFX FFLX SFX
  asym (@pa_wx _ _ PA) (clookup (@pa_tbl _ _ PA)) VAL SIGMA B_prog_listing (@pl_tpi _ PL) (@pl_tw _ PL)
  (pa_fetch_ok (PI := PA)) (@pa_cert _ _ PA) (@pa_B_ok _ _ PA) A_LIM A_LIM_text (@pl_lim _ PL) (@pl_len _ PL)
  (@pl_tpi_eq _ PL) (@pl_tw_eq _ PL) WR WRrefl WRtrans.

Section g.
(* ---- the entry: ttx_string_specX's binders and premises ---- *)
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (dw t s k b0 len0 cap0 f0 own0 : Z) (bs txt : list Z) (Lam : list (Z * Z))
  (peak cnt fail ran most : Z).
(* the model-run position the text takes at the entry (PRH_FnTx.v's rp_* binders) *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
  (rp_H0 : list Z) (rp_hist : list YG00.chunk).
(* HULL (R2320, plan row D-11): the run has at most 4 calls, the text's premise; ts_put_call's premise *)
Hypothesis HOS : (length rp_os <= 4)%nat.
#[local] Notation sp0 := (spZ regs).
(* the glue's definitions at this entry *)
#[local] Notation TSks := (@TS_ks bs).
#[local] Notation TSadd := (@TS_add bs).
#[local] Notation FP0b := (@FP0 t b0 cap0).
#[local] Notation sp1 := (@TS_sp1 regs).
#[local] Notation QFb := (@QF fx rc prh_img_B RL SK B_prog_listing PA B ARx ly S Hp W regs mem md dw t s k b0 len0 cap0
  f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
#[local] Notation sideb := (@ts_side rc ci prh_img_B RL B_prog_listing PA B ly S Hp W regs mem dw t s k b0 len0 cap0
  f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
(* the live state at WR (after the cut B): the glue's ts_liveR, LHb's live state (ts_LH at RCF = WR) *)
#[local] Notation liveb := (@ts_liveR rc ci prh_img_B RL SK B_prog_listing PA B ARx ly S Hp W regs mem md dw t s k b0
  len0 cap0 f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0 WR).
#[local] Notation bregsb := (@ts_bregs regs t).
#[local] Notation spillb := (ts_spill (L := B_prog_listing) (PA := PA) (regs := regs)).
(* the loop head at image B (TS_PC_B + 348, B 0x85a1c; s7 = .str.28, s9 = tx_string.hex) and the loop step there:
   STEPb is the glue's ts_loop premise at B (at RCF = WR, plan row D-2) *)
#[local] Notation LHb := (@ts_LH fx rc ci prh_img_B RL SK B_prog_listing PA TS_PC_B TS_LH_OFF_B TS_STR28_B TS_HEX_B B ARx
  ly S Hp W regs mem md dw t s k b0 len0 cap0 f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
#[local] Notation STEPb := (forall i Wc cf, LHb i Wc cf ->
  SRW Wc cf (fun W' c' => QFb W' c' \/ exists i', (length bs - i' < length bs - i)%nat /\ LHb i' W' c')).

Hypothesis HPRE : afn_pre_x SEGS B ARx STKS ly S Hp W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem).
Hypothesis HCL : prh_univ_closure (PI := prh_img_B) B CTX0.
Hypothesis HROOM : room_live_cf S.
Hypothesis HPOS : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S.
Hypothesis H10 : getr regs 10 = w64 t.
Hypothesis H11 : getr regs 11 = w64 s.
Hypothesis HFWIN : fwin (PA := PA) ly W regs mem dw.
Hypothesis HPLACE : prhtx_place (PA := PA) ly S W regs mem dw t.
Hypothesis HTRACE : prhtx_trace (PI := prh_img_B) (PA := PA) B ly W mem t.
Hypothesis HREC : prhtx_rec (PA := PA) W mem t b0 len0 cap0 f0.
Hypothesis HINV : prhtx_inv (PA := PA) B Lam ly S W mem b0 len0 cap0 txt.
Hypothesis HSTR : PRH_Reader.pj_cstrR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) s k bs.
Hypothesis HBVIS : prhtx_bvis (PA := PA) W mem s k.
Hypothesis HLEN : len0 + Z.of_nat (length TSadd) + 1 <= 2 ^ 28.
Hypothesis HLED : prh_ledger (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own0.
(* the run premise of the #102 text, guarded by f0 = 0, and fpre's FRM0-ENTRY conjunct; the batch's guarded room
   and guarded consumer window over the same events (PRH_FnTx.v 7cf918708def :677 / :682) *)
Hypothesis HEVS : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 TSks).
Hypothesis HROOMW : f0 = 0 ->
  YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 TSks)) (st_depot S).
Hypothesis HCONS : f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 TSks)).
Hypothesis HFRM : frm_zero (@YK11.fp_csr fx).
Hypothesis HLIVE : blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX.
Hypothesis HMAX : 2 * (len0 + Z.of_nat (length TSadd) + 1) < cf_malloc_max.
Hypothesis HCNT : count_cid 0 (frames S) < fs_frames 0.

(* ---- A: the entry, the prologue, the flag, frame_alloc_0, in continuation form: the continuation is segment B's
   start (S10TxString.v ts_at_B's premises, at B's seam TS_B_OFF_B), at the state frame_alloc_0 hands back (the layout,
   the heap list and the world of the entry: ts_B_run's binders). Segment A frees nothing: it runs at wle (its journal
   handed on at wle, lifted at the cut B, ts_at_B_B) and is lifted ONCE at its top by YGcfRhLift.ra_rh_of_SRr (plan
   row D-3) ---- *)
Lemma ts_A_cps :
  (forall Sc memc mdc kj pos rg,
     AJ (STKS + dw) (sp0 + dw) FP0b ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj ->
     sideb ly Sc Hp W memc b0 cap0 f0 own0 [] [] [] ->
     @ts_saved rc B_prog_listing PA regs W memc ->
     rdword (aview SEGS (w_H W) memc) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
     (forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> apresent (w_H W) memc a) ->
     getr rg 2 = w64 sp1 -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
     getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr ly 0 pos) -> getr rg 19 = w64 s ->
     getr rg 20 = w64 t -> getr rg 24 = w64 SHADOW_OFF ->
     SRW W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_B_OFF_B))) memc (seg_rom SEGS)) mdc) QFb) ->
  SRW W (cfg_at SEGS (SIGMA AS_tx_string) regs mem md) QFb.
Proof.
intros HB.
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof HSTK_B as HSTK.
assert (HSIDE0 : sideb ly S Hp W mem b0 cap0 f0 own0 [] [] []) by (eapply ts_side_init; eassumption).
destruct (ts_A1_entry (TS_PC := TS_PC_B) (pa_hi_ok := pa_hi_ok_B) (HSTK := HSTK_B) (LAWS := LAWS) (PAL := PAL)
  (img_box := img_box_B) ch HPRE)
  as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx STKS dw FP0b ly S Hp W regs mem md ch HPRE HFWIN) as HJ.
assert (E1a : forall more, ew (TE (L := B_prog_listing) (PA := PA) regs regs more) 2 = getr regs 2)
  by (intros more; apply te_entry; reflexivity).
assert (E64a : ew (TE (L := B_prog_listing) (PA := PA) regs regs [w64 (as_uar_cell B)]) 64 = w64 (as_uar_cell B))
  by exact (te_more_lt (L := B_prog_listing) (PA := PA) regs regs [w64 (as_uar_cell B)] 0 ltac:(lia)).
remember (TE (L := B_prog_listing) (PA := PA) regs regs [w64 (as_uar_cell B)]) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply te_env).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite E1a; reflexivity).
assert (EE : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros r n Hn; subst E; apply te_entry; exact Hn).
pose (RUNTO := paj_run_to_x (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
pose (RUN := paj_run_x (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
unfold cfg_at. rewrite <- TS_PC_val_B.
(* ---- A1: the entry to the flag's load ---- *)
pose proof HS as HSk1.
paj_run_to_tok_x RUNTO HS HJ SHOK (0, 0) (TS_PC_B + TS_A2_OFF_B).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- dw)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* the run's memnorm keep: YGcallMxmn.memnorm_frame_of from the run's start st_ok and its full-memory frame *)
assert (KN1 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk1 HF); exact Hm).
clear HSk1.
pmkst HS.
prreg HS (12%bv : bv 5) R12. prreg HS (11%bv : bv 5) R11. prreg HS (10%bv : bv 5) R10.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (2%bv : bv 5) R2. prreg HS (19%bv : bv 5) R19.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (ts_region_nth (L := B_prog_listing) (PA := PA) E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof HJ as (HAR1 & _).
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
assert (EP2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (H160 : 160 <= sp0) by lia.
assert (X2 : getr regs1 2 = w64 sp1) by (rewrite R2, EP2; exact (ts_sp1_word (regs := regs) H160)).
assert (X9 : getr regs1 9 = w64 sp1)
  by (rewrite R9, EP2, (ts_sp1_word (regs := regs) H160); apply ts_add0_word).
assert (X8 : getr regs1 8 = getr regs 2) by (rewrite R8; exact EP2).
assert (X10 : getr regs1 10 = w64 t) by (rewrite R10, (EE 10%bv 10%nat) by reflexivity; exact H10).
assert (X19 : getr regs1 19 = w64 s) by (rewrite R19, (EE 11%bv 11%nat) by reflexivity; exact H11).
assert (X3 : getr regs1 3 = getr regs 3) by (rewrite R3; apply EE; reflexivity).
assert (X4 : getr regs1 4 = getr regs 4) by (rewrite R4; apply EE; reflexivity).
assert (X11 : getr regs1 11 = w64 (VAL (A_OBJ 12)))
  by (rewrite R11, HEdef; apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (X12 : getr regs1 12 = w64 (as_uar_cell B)) by (rewrite R12; exact E64a).
assert (HSV : ts_saved (L := B_prog_listing) (PA := PA) (regs := regs) W mem1).
{ intros j Hj. do 13 (destruct j as [|j]; [
    lazymatch goal with |- val_mem _ _ _ _ (bv_unsigned (getr regs (nth ?jj TS_SAVED 0%bv))) =>
      let r := eval vm_compute in (nth jj TS_SAVED 0%bv) in
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      let off := eval vm_compute in (- 8 * (Z.of_nat jj + 1)) in
      pose proof (ts_field (L := B_prog_listing) (PA := PA) E _ 2 sp0 _ _ _ _ _ off 8 (SOff n 0) HR0 Usp
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; change (N.to_nat 8) with 8%nat in V;
      rewrite ts_U_atom_mod, (EE r n) in V by reflexivity;
      change (nth jj TS_SAVED 0%bv) with r;
      replace (sp0 - 8 * (Z.of_nat jj + 1)) with (sp0 + off) by (cbn; lia); exact V
    end |]). lia. }
rename HFr into HFr1. clear HF HG.
(* ---- A2: the flag's load ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR1) as (Kcell1 & Kuar1 & _ & _).
rewrite (pal_cell (PI := PA) B PAL) in Kcell1.
destruct (ts_A2_entry (TS_PC := TS_PC_B) (TS_A2_OFF := TS_A2_OFF_B) (pal_uar_img := pal_uar_img)
  (cf_img_ok := cf_img_ok) (regs := regs) regs1 mem1 W X12 Kuar1) as [HS2 SHOK2].
clear HS SHOK.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] => change (BASE + n) with (BASE + (TS_PC_B + TS_A2_OFF_B)) end.
assert (HEI2 : img_env VAL A_LIM (TE (L := B_prog_listing) (PA := PA) regs regs1 [])) by apply te_env.
pose proof HS2 as HSk2.
paj_run_to_tok_x RUNTO HS2 HJ SHOK2 (0, 0) (TS_PC_B + TS_A3_OFF_B).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KN2 : YAkMemnorm.memnorm SEGS mem1 -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk2 HF); exact Hm).
clear HSk2.
pmkst HS2.
set (regs2 := ms_regs ms0) in *. set (mem2 := ms_mem ms0) in *.
pose proof HJ as (HAR2 & _).
prreg HS2 (12%bv : bv 5) Q12.
assert (Y : forall (r : bv 5), In r [2; 3; 4; 8; 9; 10; 11; 19]%bv -> getr regs2 r = getr regs1 r).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ => let HH := fresh "HH" in prreg HS2 rr HH; unfold regs2; rewrite HH; te_close end |]).
  destruct Hr. }
rename HFr into HFr2. clear HF HG.
(* ---- A3: the shadow base's load, the flag test, to the frame call ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Kcell2 & _ & _ & _).
rewrite (pal_cell (PI := PA) B PAL) in Kcell2.
destruct (ts_A3_entry (TS_PC := TS_PC_B) (TS_A3_OFF := TS_A3_OFF_B) (pa_hi_ok := pa_hi_ok_B) (cf_img_ok := cf_img_ok)
  (img_cf_box := img_cf_box) (regs := regs)
  regs2 mem2 W ltac:(rewrite (Y 11%bv) by (cbv; tauto); exact X11) Q12 Kcell2) as [HS3 SHOK3].
clear HS2 SHOK2.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] => change (BASE + n) with (BASE + (TS_PC_B + TS_A3_OFF_B)) end.
assert (HEI3 : img_env VAL A_LIM (TE (L := B_prog_listing) (PA := PA) regs regs2 [w64 SHADOW_OFF])) by apply te_env.
pose proof HS3 as HSk3.
paj_run_tok_x RUN HS3 HJ SHOK3 (0, 0).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KN3 : YAkMemnorm.memnorm SEGS mem2 -> YAkMemnorm.memnorm SEGS (ms_mem ms1))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk3 HF); exact Hm).
clear HSk3.
set (regs3 := ms_regs ms1) in *. set (mem3 := ms_mem ms1) in *.
pose proof HJ as (HAR3 & _).
assert (Y3 : forall (r : bv 5), In r [2; 3; 4; 8; 9; 19]%bv -> getr regs3 r = getr regs2 r).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ => let HH := fresh "HH" in prreg HS3 rr HH; unfold regs3; rewrite HH; te_close end |]).
  destruct Hr. }
prreg HS3 (20%bv : bv 5) Z20.
prreg HS3 (24%bv : bv 5) Z24. prreg HS3 (1%bv : bv 5) Z1.
rename HFr into HFr3. clear HF HG.
(* the registers at the call *)
assert (T2 : getr regs3 2 = w64 sp1)
  by (rewrite (Y3 2%bv) by (cbv; tauto); rewrite (Y 2%bv) by (cbv; tauto); exact X2).
assert (T3 : getr regs3 3 = getr regs 3)
  by (rewrite (Y3 3%bv) by (cbv; tauto); rewrite (Y 3%bv) by (cbv; tauto); exact X3).
assert (T4 : getr regs3 4 = getr regs 4)
  by (rewrite (Y3 4%bv) by (cbv; tauto); rewrite (Y 4%bv) by (cbv; tauto); exact X4).
assert (T8 : getr regs3 8 = getr regs 2)
  by (rewrite (Y3 8%bv) by (cbv; tauto); rewrite (Y 8%bv) by (cbv; tauto); exact X8).
assert (T9 : getr regs3 9 = w64 sp1)
  by (rewrite (Y3 9%bv) by (cbv; tauto); rewrite (Y 9%bv) by (cbv; tauto); exact X9).
assert (T19 : getr regs3 19 = w64 s)
  by (rewrite (Y3 19%bv) by (cbv; tauto); rewrite (Y 19%bv) by (cbv; tauto); exact X19).
assert (T20 : getr regs3 20 = w64 t)
  by (unfold regs3; rewrite Z20; rewrite (te_cur regs regs2 _ 10%bv 10) by reflexivity;
      rewrite (Y 10%bv) by (cbv; tauto); exact X10).
assert (T24 : getr regs3 24 = w64 SHADOW_OFF)
  by (unfold regs3; rewrite Z24; exact (te_more_lt regs regs2 [w64 SHADOW_OFF] 0 ltac:(lia))).
(* the realigned frame base *)
assert (HR : sp0 - 176 <= sp1 <= sp0 - 160 /\ sp1 mod 32 = 0).
{ unfold TS_sp1. pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)).
  assert ((sp0 - 160) mod 32 = 0 \/ (sp0 - 160) mod 32 = 16) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
  split; [lia | apply Z.mod_mul; lia]. }
(* memory: the three runs wrote only the probe slot and the saves, below the entry sp *)
assert (K1 : forall x : word, ~ (sp0 - 160 <= bv_unsigned x < sp0) ->
  mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr1. intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia |]).
  destruct Hin. }
assert (K2 : forall x : word, mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem1 x).
{ intros x. apply HFr2. intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]). destruct Hin. }
assert (K3 : forall x : word, mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem2 x).
{ intros x. apply HFr3. intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]). destruct Hin. }
assert (K13 : forall x : word, mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem1 x) by (intros x; rewrite K3, K2; reflexivity).
assert (KA13 : forall a, aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem1 a)
  by (intros a; unfold aview, mbyte; rewrite K13; reflexivity).
(* the side facts after the three runs *)
assert (HSIDE3 : sideb ly S Hp W mem3 b0 cap0 f0 own0 [] [] []).
{ apply (ts_side_run (L := B_prog_listing) (PA := PA) (HSTK := HSTK_B) (LAWS := LAWS) (pst_img := pst_img_B)
    (pal_pst_static := pal_pst_static) ly S Hp W mem mem3 _ b0 cap0 f0 own0 [] [] []
    (fun a => sp0 - 160 <= a < sp0) HSIDE0 HAR3).
  - unfold alloc_ceiling in *. lia.
  - exact Hdwtop.
  - lia.
  - intros a Ha. split; [|lia].
    destruct (Hdwpres a Ha) as [Hh [bb Hb]]. split; [exact Hh|]. exists bb.
    pose proof (K13 (Z_to_bv 64 a)) as E13.
    pose proof (K1 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia)) as E1.
    unfold mrestrict in E13, E1. rewrite Hh in E13, E1. rewrite E13, E1. exact Hb.
  - intros x Hx. rewrite K13. exact (K1 x Hx).
  - intros a Ha. left. lia.
  - intros Hm. exact (KN3 (KN2 (KN1 Hm))). }
pmkst HS3. rewrite pal_stack_malloc0. fold regs3 mem3.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm SEGS B PST ARx LAWS Hsegs (pal_env (PI := PA) B PAL) OWNLOW SMX 0 ASM0 ltac:(lia)
    W _ _ (STKS + dw) (sp0 + dw) FP0b ly S Hp W mem md [] ly S Hp _ _
    (sp1 - (sp0 + dw)) (Z_to_bv 64 (BASE + (TS_PC_B + TS_B_OFF_B)))).
  - exact HJ.
  - unfold spZ at 1. rewrite T2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - assert (H16 : sp1 mod 16 = 0) by lia.
    rewrite Zminus_mod, Zplus_mod, Hal16, Hdw16, H16. reflexivity.
  - lia.
  - unfold ESTACK in *. lia.
  - rewrite T3. exact Hgp.
  - rewrite T4. exact Htp.
  - unfold regs3. rewrite Z1. first [reflexivity | f_equal; f_equal; vm_compute; reflexivity].
  - apply ret_ok_codeptr_v;
      [let v := eval vm_compute in (TS_PC_B + TS_B_OFF_B) in change (TS_PC_B + TS_B_OFF_B) with v; lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & rg & mem4 & md4 & pos & Hc2 & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hfresh & Hnev2 &
  Hbb2 & Hz & Hflag & Hfpres & HKept & HJt & Hsetfs & HMN4).
rewrite Hc2.
destruct HKept as (KC1 & KC2 & KC3 & KC4 & KC5 & _).
assert (KT : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KC1; [unfold alloc_ceiling in *; lia | lia]. }
pose proof HJ2 as (HAR4 & _).
assert (FB : fs_frame_bytes 0 = 64) by reflexivity.
rewrite FB in Hflag, Hfpres.
(* presence of the caller window at the call's start *)
assert (PW3 : forall a, sp0 <= a < sp0 + dw -> apresent (w_H W) mem3 a).
{ intros a Ha. destruct (Hdwpres a Ha) as [Hh [bb Hb]]. split; [exact Hh|]. exists bb.
  pose proof (K13 (Z_to_bv 64 a)) as E13.
  pose proof (K1 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia)) as E1.
  unfold mrestrict in E13, E1. rewrite Hh in E13, E1. rewrite E13, E1. exact Hb. }
(* the continuation (segment B on): SRW, under the top lift's plain SRr *)
apply SRr_ret. cbv beta.
apply (HB S2 mem4 md4 0 pos rg).
- exact HJ2.
- apply (ts_side_move (L := B_prog_listing) (PA := PA) (LAWS := LAWS) (pst_img := pst_img_B)
    (pal_pst_static := pal_pst_static) ly S Hp W mem3 ly S2 mem4 md4 b0 cap0 f0 own0 [] [] [] HSIDE3 HAR4 eq_refl Eab
    Hbb2).
  + right. exact Hsetfs.
  + exact Hdwtop.
  + intros a Ha. split; [|lia]. apply KC5; [unfold alloc_ceiling in *; lia | lia | exact (PW3 a Ha)].
  + intros a Ha. apply KT. lia.
  + intros p n i Hin Hi. apply (KC2 p n i Hin Hi). intros [].
  + intros a Hi Ho He. apply KC3; assumption.
  + exact HMN4.
- intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros jj Hjj. rewrite KT by lia. rewrite KA13. reflexivity.
- replace (frame_addr ly 0 pos + 56) with (frame_addr ly 0 pos + 64 - 8) by lia. exact Hflag.
- exact Hfpres.
- assert (P : getr rg 2%bv = getr regs3 2%bv) by exact (HP2 2 ltac:(unfold acallee_saved; lia)). rewrite P. exact T2.
- assert (P : getr rg 3%bv = getr regs3 3%bv) by exact (HP2 3 ltac:(unfold acallee_saved; lia)). rewrite P. exact T3.
- assert (P : getr rg 4%bv = getr regs3 4%bv) by exact (HP2 4 ltac:(unfold acallee_saved; lia)). rewrite P. exact T4.
- assert (P : getr rg 8%bv = getr regs3 8%bv) by exact (HP2 8 ltac:(unfold acallee_saved; lia)). rewrite P. exact T8.
- assert (P : getr rg 9%bv = getr regs3 9%bv) by exact (HP2 9 ltac:(unfold acallee_saved; lia)). rewrite P. exact T9.
- exact Ha0.
- assert (P : getr rg 19%bv = getr regs3 19%bv) by exact (HP2 19 ltac:(unfold acallee_saved; lia)). rewrite P. exact T19.
- assert (P : getr rg 20%bv = getr regs3 20%bv) by exact (HP2 20 ltac:(unfold acallee_saved; lia)). rewrite P. exact T20.
- assert (P : getr rg 24%bv = getr regs3 24%bv) by exact (HP2 24 ltac:(unfold acallee_saved; lia)). rewrite P. exact T24.
Qed.

(* ---- B: after frame_alloc_0 (B 0x85934): `mv s2, a0`, `mv s5, s2`, the frame test (F <> 0), F at sp1 + 48, the
   fake frame's header (F + 0 / + 8 / + 16), its 8 shadow bytes (f1 f1 f1 f1 f8 f3 f3 f3), a0 = t, a1 = .str.27,
   a2 = 1, to the opening quote's `jal tx_put` (B 0x859d0). Unlike A, B spills F to sp1 + 16 / + 24 only AFTER that
   call (B 0x859d8 / 0x859dc), so the call state is handed on in continuation form. Regions as S10's ss_B (A): s1's
   slots [sp1 + 16, sp1 + 56), the header [F, F + 24), F's shadow (atom 64, aliased to `(F >> 3) + s8`). ---- *)
Definition ss_Bb : sstate := mkSS (TS_PC_B + TS_B_OFF_B) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 16 56 16 56 [];
    YP09.mkRegion (Some (xr 10)) 0 24 0 24 [];
    YP09.mkRegion (Some 64%nat) 0 8 0 8 [] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 10, mkAF 4096 (2 ^ 47) 5); (xr 24, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] []
           [(SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 10) 0) (SLit 3)) (SOff (xr 24) 0), SOff 64 0)]).
(* SHAPE: S10TxString.v ts_B_entry (image A, walk-S10 1c3f6103b950), with B's seam *)
Lemma ts_B_entry_B : forall lyc Sc Hpc Wc memc mdc pos rg,
  ARx lyc Sc Hpc Wc memc mdc -> In (0, pos) (frames Sc) ->
  (forall a, frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64 -> apresent (w_H Wc) memc a) ->
  (forall a, sp1 + 16 <= a < sp1 + 56 -> apresent (w_H Wc) memc a) ->
  YM05.alloc_ceiling <= sp1 -> sp1 + 64 <= 2 ^ 47 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr lyc 0 pos) -> getr rg 24 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE (L := B_prog_listing) (PA := PA) regs rg [w64 (shadow_addr (frame_addr lyc 0 pos))]) ss_Bb
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_B_OFF_B))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE (L := B_prog_listing) (PA := PA) regs rg [w64 (shadow_addr (frame_addr lyc 0 pos))])
    (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Hpc Wc memc mdc pos rg HAR Hin Hfp Hsp Hc Hc47' R9 R10 R24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HAR Hin) as (F1 & F2 & F3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HAR Hin) as (F32 & _ & _ & Fsh).
change (fs_frame_bytes 0) with 64 in F2, F3, Fsh.
set (F := frame_addr lyc 0 pos) in *.
set (E := TE (L := B_prog_listing) (PA := PA) regs rg [w64 (shadow_addr F)]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X24 : bv_unsigned (ew E (xr 24)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. rewrite R24. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (Hsh2 : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (X64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
unfold SHADOW_OFF in Hsh2.
split.
- apply ts_st_ok.
  all: try change (TE (L := B_prog_listing) (PA := PA) regs rg [w64 (shadow_addr F)]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hsp. lia.
    * apply (ts_rok E _ (xr 10) F); [exact X10 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hfp. lia.
    * apply (ts_rok E _ 64 (shadow_addr F)); [exact X64 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Fsh o ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X10, X64.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X10, X24, X64.
      unfold TS_sp1 in *. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
      unfold shadow_addr, SHADOW_OFF. repeat split; try lia.
    * cbn [f_alias alias_ok]. split; [|exact I].
      apply (ts_alias_shadow E (xr 10) (xr 24) 64 F X10 X24 X64). lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* segment B's run, in continuation form, at the state ts_A_cps hands over (lyc = ly, Hpc = Hp, Wc = W), after the
   cut B's lift (plan row D-4): its journal at WR, the run at WR; the continuation receives the call state at B's
   opening `jal tx_put` with everything the glue's tx_put call rule (TxStr102Glue.v ts_put_call) asks *)
Lemma ts_B_run : forall Sc memc mdc kj pos rg,
  AJR (STKS + dw) (sp0 + dw) FP0b ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj ->
  sideb ly Sc Hp W memc b0 cap0 f0 own0 [] [] [] ->
  ts_saved (L := B_prog_listing) (PA := PA) (regs := regs) W memc ->
  rdword (aview SEGS (w_H W) memc) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
  (forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> apresent (w_H W) memc a) ->
  getr rg 2 = w64 sp1 -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr ly 0 pos) -> getr rg 19 = w64 s ->
  getr rg 20 = w64 t -> getr rg 24 = w64 SHADOW_OFF ->
  (forall E ss ms mdc' kj',
     st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
     bv_unsigned (ew E 2) = sp0 ->
     AJR (STKS + dw) (sp0 + dw) FP0b ly S Hp W mem md [(0, pos)] ly Sc Hp W (ms_mem ms) mdc' kj' ->
     sideb ly Sc Hp W (ms_mem ms) b0 cap0 f0 own0 [] [] [] ->
     ts_saved (L := B_prog_listing) (PA := PA) (regs := regs) W (ms_mem ms) ->
     rdword (aview SEGS (w_H W) (ms_mem ms)) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
     ts_bregs (regs := regs) (t := t) (ms_regs ms) ->
     getr (ms_regs ms) 18 = w64 (frame_addr ly 0 pos) -> getr (ms_regs ms) 21 = w64 (frame_addr ly 0 pos) ->
     getr (ms_regs ms) 19 = w64 s -> getr (ms_regs ms) 26 = w64 (shadow_addr (frame_addr ly 0 pos)) ->
     getr (ms_regs ms) 10 = w64 t -> getr (ms_regs ms) 11 = w64 TS_STR27_B -> getr (ms_regs ms) 12 = w64 1 ->
     getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (TS_PC_B + TS_C_OFF_B)) ->
     SRW W (mkCfg ms mdc') QFb) ->
  SRW W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_B_OFF_B))) memc (seg_rom SEGS)) mdc) QFb.
Proof.
intros Sc memc mdc kj pos rg HJ HSD HSV Hfl Hfp R2 R3 R4 R8 R9 R10 R19 R20 R24 HK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof HSTK_B as HSTK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_frs HJ) as HFRc. pose proof (ajxR_pres HJ) as HPRc.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (ts_sp1_range (regs := regs) Hal16 ltac:(lia)) as [Hsp1r Hsp1m].
destruct (ts_B_entry_B ly Sc Hp W memc mdc pos rg HARc Hin Hfp ltac:(intros a Ha; apply HPRc; lia)
  ltac:(unfold alloc_ceiling in *; lia) ltac:(lia) R9 R10 R24) as [HS SHOK].
destruct (frames_bounds_x _ _ _ LAWS ly Sc Hp W memc mdc 0 pos HARc Hin) as (F1 & F2 & F3).
change (fs_frame_bytes 0) with 64 in F2, F3.
set (F := frame_addr ly 0 pos) in *.
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hshr : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
set (E := TE (L := B_prog_listing) (PA := PA) regs rg [w64 (shadow_addr F)]) in *.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose proof HS as HSk.
paj_run_tok_xR RUN HS HJ SHOK (0, 0).
{ cbv [ss_Bb ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - (sp0 + dw))); [reflexivity | lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 10) F); [reflexivity | exact X10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 64%nat (shadow_addr F)); [reflexivity | exact X64 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. fold F. lia. }
  apply awr_ok_nil. }
assert (KN : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk HF); exact Hm).
clear HSk.
pose proof (ajxR_ar HJ) as HARn. pose proof (ajxR_pres HJ) as HPRn.
(* the run's writes: s1's slots, the header, F's shadow *)
assert (HWR : forall a, in_wrange E (ss_mem ss_Bb) a ->
  (sp1 + 16 <= a < sp1 + 56) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 8)).
{ intros a (r & Hin' & Hr). cbv [ss_Bb ss_mem] in Hin'.
  destruct Hin' as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?X9, ?X10, ?X64 in Hr; lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 56) -> ~ (F <= a < F + 24) ->
  ~ (shadow_addr F <= a < shadow_addr F + 8) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha N1 N2 N3. apply (ts_keep (L := B_prog_listing) (PA := PA) W E (ss_mem ss_Bb) memc (ms_mem ms)
    (fun a => (sp1 + 16 <= a < sp1 + 56) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 8)) HFr HWR a Ha).
  intros [H|[H|H]]; contradiction. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (18%bv : bv 5) Q18. prreg HS (21%bv : bv 5) Q21. prreg HS (26%bv : bv 5) Q26.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
eapply (HK E _ ms _ _ HS).
- reflexivity.
- reflexivity.
- unfold E. rewrite (te_entry regs rg _ 2%bv 2) by reflexivity. reflexivity.
- exact HJ.
- apply (ts_side_run (L := B_prog_listing) (PA := PA) (HSTK := HSTK_B) (LAWS := LAWS) (pst_img := pst_img_B)
    (pal_pst_static := pal_pst_static) ly Sc Hp W memc (ms_mem ms) _ b0 cap0 f0 own0 [] [] []
    (in_wrange E (ss_mem ss_Bb)) HSD HARn).
  + unfold alloc_ceiling in *. lia.
  + exact Hdwtop.
  + lia.
  + intros a Ha. split; [apply HPRn; lia | lia].
  + intros x Hx. exact (HFr x Hx).
  + intros a Ha. destruct (HWR a Ha) as [H|[H|H]].
    * left. lia.
    * right. exists pos. split; [exact Hin|]. left. unfold in_zr, frame_rng. cbn [fst snd].
      change (fs_frame_bytes 0) with 64. fold F. lia.
    * right. exists pos. split; [exact Hin|]. right. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 0 / 8) with 8. fold F. lia.
  + exact KN.
- intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros jj Hjj.
  apply KB; unfold shadow_addr, SHADOW_OFF in *; lia.
- rewrite <- Hfl. apply ts_rdword_keep. intros j Hj.
  apply KB; unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia.
- unfold ts_bregs. repeat split.
  + rewrite Q2. unfold E. rewrite (te_cur regs rg _ 2%bv 2) by reflexivity. exact R2.
  + rewrite Q3. unfold E. rewrite (te_cur regs rg _ 3%bv 3) by reflexivity. exact R3.
  + rewrite Q4. unfold E. rewrite (te_cur regs rg _ 4%bv 4) by reflexivity. exact R4.
  + rewrite Q8. unfold E. rewrite (te_cur regs rg _ 8%bv 8) by reflexivity. exact R8.
  + rewrite Q9. unfold E. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. exact R9.
  + rewrite Q20. unfold E. rewrite (te_cur regs rg _ 20%bv 20) by reflexivity. exact R20.
  + rewrite Q24. unfold E. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. exact R24.
- rewrite Q18. unfold E. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. exact R10.
- rewrite Q21. unfold E. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. exact R10.
- rewrite Q19. unfold E. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. exact R19.
- rewrite Q26. unfold E. rewrite (te_more_lt regs rg _ 0) by lia. reflexivity.
- rewrite Q10. unfold E. rewrite (te_cur regs rg _ 20%bv 20) by reflexivity. exact R20.
- rewrite Q11. unfold E. rewrite te_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (apply pa_val_range). reflexivity.
- rewrite Q12. reflexivity.
- rewrite Q1. first [reflexivity | f_equal; f_equal; vm_compute; reflexivity].
Qed.


(* ---- C: after the opening quote (B 0x859d4). Unlike A, B tests s first (`beqz s3` to the UBSan trap `unimp` at
   0x85c18: not taken, the run's fact s >= 4096 decides it) and spills F only now (`sd s5, 24(s1)`, `sd s2, 16(s1)`,
   B 0x859d8 / 0x859dc); then the inline check of s (0x859e0 .. 0x859ec, slow block 0x85c1c), the first byte, `beqz a1`
   to the closing block X (0x85b5c) or the loop setup (`ld a0, 24(s1)`, s6 = F + 32, s5 = s + 1, s2 = 92, s11 = 48,
   s9 = hex, s7 = .str.28) to the loop head (0x85a1c). Regions: s1's spill slots [sp1 + 16, sp1 + 32) (writable, no
   value yet), the string's first byte (atom 64, read-only) ---- *)
Definition ss_Cb : sstate := mkSS (TS_PC_B + TS_C_OFF_B) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 16 32 16 32 [];
    YP09.mkRegion (Some (xr 19)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 64 0))] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 19, mkAF 4096 (2 ^ 47 - 8) 3); (xr 24, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF 0 255 0)] [] []).
Lemma ts_C_entry_B : forall (Wc : world SEGS) memc rg c0,
  getr rg 9 = w64 sp1 -> getr rg 19 = w64 s -> getr rg 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 + 32 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= s -> s + 1 <= sp1 -> s mod 8 = 0 -> 0 <= c0 < 256 ->
  (forall a, sp1 + 16 <= a < sp1 + 32 -> apresent (w_H Wc) memc a) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) s 1 c0 ->
  st_ok_pi SEGS VAL (TEb regs rg [w64 c0]) ss_Cb
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_C_OFF_B))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SOff (xr 24) 0) [] (TEb regs rg [w64 c0]) (mrestrict (w_H Wc) memc).
Proof.
intros Wc memc rg c0 R9 R19 R24 H1 H2 H3 H4 H5 H6 H7 Hsp Vc.
set (E := TEb regs rg [w64 c0]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X19 : bv_unsigned (ew E (xr 19)) = s).
{ unfold E, xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small. lia. }
assert (X24 : bv_unsigned (ew E (xr 24)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. rewrite R24. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E64 : ew E 64 = w64 c0) by exact (te_more_lt (L := B_prog_listing) (PA := PA) regs rg [w64 c0] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = c0) by (rewrite E64; apply unsigned_lit_small; lia).
split.
- apply ts_st_ok.
  all: try change (TEb regs rg [w64 c0]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hsp. lia.
    * apply (ts_rok E _ (xr 19) s); [exact X19 | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 1 (SOff 64 0) c0);
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X19, X24, X64.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1. repeat split; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- the model at the end: the calls' sizes and the text appended (B-local copies of S10TxString.v's ts_ks_fin /
   ts_add_fin, walk-S10 18165859e13 :342-348; DELETE when S10TxStrGlue carries them) ---- *)
Lemma ts_ks_fin_B : TxModel.plen (ts_pieces bs) ++ [1] = TSks.
Proof. unfold TS_ks. rewrite s10s_ks. reflexivity. Qed.
Lemma ts_add_fin_B : concat (ts_pieces bs) ++ [34] = TSadd.
Proof.
unfold TS_add. rewrite <- s10_strp_wstr. unfold ts_pieces, TxModel.strp. cbn [concat]. rewrite concat_app.
cbn [concat]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* ---- G: after the closing quote (B 0x85b70, byte for byte A's 0x85594): the frame's retire (`sd` of 0x45e0360e at
   F + 0), `ld a1, 16(s1); beqz a1` (not taken: F <> 0), its shadow (eight `sb` of f5 at s10 .. s10 + 7), the flag store
   (`ld a0, 56(a1); sb zero, 0(a0)`), the epilogue (`addi sp, s0, -160` .. `ret`). Registers: gp, tp pinned to the
   entry's, s0 to the entry sp (atom 2). Regions: s1's slots (F), the frame's first word (writable) and its flag
   pointer (F + 56, atom 65), the frame's shadow (writable), the flag byte (writable), the prologue's saves below the
   entry sp (the entry registers) ---- *)
Definition sr_G_B : list sv := sr_set (sr_set (sr_set cur_atoms 3%bv (SOff 3 0)) 4%bv (SOff 4 0)) 8%bv (SOff 2 0).
Definition G_saves_B : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
Definition ss_Gb : sstate := mkSS (TS_PC_B + TS_G_OFF_B) sr_G_B
  [ YP09.mkRegion (Some (xr 9)) 16 32 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 64 0)); YP09.mkChunk 24 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some 64%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 65 0))];
    YP09.mkRegion (Some (xr 26)) 0 8 0 8 [];
    YP09.mkRegion (Some 65%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 2%nat) (-104) 0 0 0 G_saves_B ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (64%nat, mkAF 4096 (2 ^ 47) 5);
            (xr 26, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (65%nat, mkAF 0 (2 ^ 47) 0);
            (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Lemma ts_G_entry_B : forall (Wc : world SEGS) memc rg F fl,
  getr rg 9 = w64 sp1 -> getr rg 26 = w64 (shadow_addr F) ->
  getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
  2 ^ 46 <= sp1 -> sp1 + 32 <= sp0 - 104 -> sp1 mod 32 = 0 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  4096 <= F -> F + 64 <= sp1 -> F mod 32 = 0 -> in_app F 64 ->
  0 <= fl -> fl + 1 <= sp1 -> (fl + 1 <= F \/ F + 64 <= fl) ->
  (fl + 1 <= shadow_addr F \/ shadow_addr F + 8 <= fl) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + 16) 8 F -> val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + 24) 8 F ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 56) 8 fl ->
  @ts_saved rc B_prog_listing PA regs Wc memc ->
  (forall a, F <= a < F + 8 -> apresent (w_H Wc) memc a) ->
  (forall a, shadow_addr F <= a < shadow_addr F + 8 -> apresent (w_H Wc) memc a) ->
  apresent (w_H Wc) memc fl ->
  st_ok_pi SEGS VAL (TEb regs rg [w64 F; w64 fl]) ss_Gb
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_G_OFF_B))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TEb regs rg [w64 F; w64 fl]) (mrestrict (w_H Wc) memc).
Proof.
intros Wc memc rg F fl R9 R26 R3 R4 R8 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 V16 V24 VFL HSV PF PSH PFL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := TEb regs rg [w64 F; w64 fl]).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Hsh' := Hsh). unfold SHADOW_OFF in Hsh'.
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (E64 : ew E 64 = w64 F) by exact (te_more_lt regs rg [w64 F; w64 fl] 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 fl) by exact (te_more_lt regs rg [w64 F; w64 fl] 1 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = F) by (rewrite E64; apply unsigned_lit_small; lia).
assert (X65 : bv_unsigned (ew E 65) = fl) by (rewrite E65; apply unsigned_lit_small; lia).
assert (X2 : bv_unsigned (ew E 2) = sp0) by (unfold E; rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
assert (EN : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros r n Hn; unfold E; apply te_entry; exact Hn).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEb regs rg [w64 F; w64 fl]) with E.
- unfold sr_G_B.
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 2%bv 2%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R8].
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 4%bv 4%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R4].
  apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 3%bv 3%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R3].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 16 8 (SOff 64 0) F);
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact V16.
    * apply (ts_chunk E _ _ 24 8 (SOff 64 0) F);
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact V24.
  + apply (ts_rok E _ 64 F); [exact X64 | lia | lia | intros o Ho; apply (apresent_writable SEGS); apply PF; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 56 8 (SOff 65 0) fl);
      [cbn [sv_denot]; rewrite E65, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact VFL.
  + apply (ts_rok E _ (xr 26) (shadow_addr F)); [exact X26 | lia | lia |
      intros o Ho; apply (apresent_writable SEGS); apply PSH; lia | constructor].
  + apply (ts_rok E _ 65 fl); [exact X65 | lia | lia | intros o Ho; apply (apresent_writable SEGS);
      replace (fl + o) with fl by lia; exact PFL | constructor].
  + apply (ts_rok E _ 2 sp0); [exact X2 | lia | lia | intros o Ho; lia |].
    unfold G_saves_B. repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval vm_compute in (Z.to_nat (- off / 8 - 1)) in
      let r := eval vm_compute in (nth j TS_SAVED 0%bv) in
      apply (ts_chunk E _ _ off 8 (SOff n 0) (bv_unsigned (getr regs r)));
      [ cbn [sv_denot]; rewrite (EN r n) by reflexivity; rewrite Z.add_0_r; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR; cbn; lia
      | cbn; lia
      | pose proof (HSV j ltac:(lia)) as V; change (nth j TS_SAVED 0%bv) with r in V;
        replace (sp0 - 8 * (Z.of_nat j + 1)) with (sp0 + off) in V by (cbn; lia); exact V ]
    end.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X64, X26, X65, X2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X64, X26, X65, X2.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
  unfold SHADOW_OFF in *. repeat split; lia.
Qed.

Lemma ts_at_G_B : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg,
  liveb lyc Sc Hpc Wc memc mdc kj pos F b cap f own TSks TSadd ap -> spillb Wc memc F ->
  bregsb rg -> getr rg 26 = w64 (shadow_addr F) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_G_OFF_B))) memc (seg_rom SEGS)) mdc) QFb.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL [HF16 HF24] HBR R26.
pose proof HL as (HJ & HSD & EF & (HSV & HFL)).
pose proof HBR as (R2 & R3 & R4 & R8 & R9 & R20 & R24).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HSTK_B as HSTK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc. pose proof (ajxR_frs HJ) as HFRc.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (F32 & _ & Ffr & Fsh).
change (fs_frame_bytes 0) with 64 in Fb2, Fb3, Ffr, Fsh. rewrite <- EF in Fb1, Fb2, Fb3, F32, Ffr, Fsh.
destruct (FFLX lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fown & Fapp & Fimg).
pose proof (OWNLOW lyc Sc Hpc Wc memc mdc _ HARc Fown) as Flow.
pose proof (FFLP lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as Fpr.
destruct (ts_sp1_range (regs := regs) Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
set (fl := flag_addr lyc 0 pos) in *.
assert (Hflf : fl + 1 <= F \/ F + 64 <= fl).
{ destruct (Z_lt_le_dec fl F) as [Hl|Hl]; [left; lia|]. destruct (Z_le_gt_dec (F + 64) fl) as [Hg|Hg]; [right; lia|].
  exfalso. exact (proj2 (Ffr fl ltac:(lia)) Fown). }
assert (Hfls : fl + 1 <= shadow_addr F \/ shadow_addr F + 8 <= fl).
{ destruct (Z_lt_le_dec fl (shadow_addr F)) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (shadow_addr F + 8) fl) as [Hg|Hg]; [right; lia|].
  exfalso. replace fl with (shadow_addr F + (fl - shadow_addr F)) in Fown by lia.
  exact (proj2 (Fsh (fl - shadow_addr F) ltac:(change (64 / 8) with 8; lia)) Fown). }
destruct (ts_G_entry_B Wc memc rg F fl R9 R26 R3 R4 R8 ltac:(lia) ltac:(lia) Hsp1b ltac:(lia) Hal16 Fb1 ltac:(lia) F32 Fb3
  ltac:(lia) ltac:(lia) Hflf Hfls HF16 HF24 (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HFL) HSV
  ltac:(intros a Ha; exact (proj1 (Ffr a ltac:(lia))))
  ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by lia;
        exact (proj1 (Fsh (a - shadow_addr F) ltac:(change (64 / 8) with 8; lia)))) Fpr) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TEb regs rg [w64 F; w64 fl])) by apply te_env.
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (U64 : bv_unsigned (ew (TEb regs rg [w64 F; w64 fl]) 64) = F).
{ rewrite (te_more_lt regs rg [w64 F; w64 fl] 0) by lia. cbn [nth]. apply unsigned_lit_small. lia. }
assert (U65 : bv_unsigned (ew (TEb regs rg [w64 F; w64 fl]) 65) = fl).
{ change 65%nat with (64 + 1)%nat. rewrite (te_more_lt regs rg [w64 F; w64 fl] 1) by lia. cbn [nth].
  apply unsigned_lit_small. lia. }
assert (U26 : bv_unsigned (ew (TEb regs rg [w64 F; w64 fl]) (xr 26)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
(* G's writes: the frame's first word, its shadow, the flag byte *)
assert (Hwr : forall a, in_wrange (TEb regs rg [w64 F; w64 fl]) (ss_mem ss_Gb) a ->
  (F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = fl).
{ intros a (r & Hr & Ha). cbv [ss_Gb ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    rewrite ts_bv_some in Ha.
  - lia.
  - left. rewrite U64 in Ha. lia.
  - right; left. rewrite U26 in Ha. lia.
  - right; right. rewrite U65 in Ha. lia.
  - lia. }
(* the run has no inline check: its shadow span is a point far above every region (the flag's lower bound is 0) *)
lazymatch type of HS with st_ok_pi _ _ ?E ?ss _ =>
  let K := eval vm_compute in (run_K A_LIM (SLit 0) [] ss) in
  let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss) in
  lazymatch r with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss = (st', rs))
    by (vm_compute; reflexivity);
  eapply (ts_flag_store_B Wc FUEL E K (SLit 0) (2 ^ 63, 2 ^ 63) [] ss st' rs _ (STKS + dw) (sp0 + dw) FP0b ly
    (set_depot (st_depot Sc) S) Hp W mem md
    [] lyc Sc Hpc _ _ 0 pos _ ltac:(unfold A_LIM; cbn; lia) HEI ltac:(lia) HS SHOK ltac:(vm_compute; reflexivity) Hrun I
    HJ)
  end end.
- (* no inline check, no obligation *)
  match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end. apply Forall_nil.
- (* the writes: the own frame's first word and shadow, and the flag *)
  intros a HW. destruct (Hwr a HW) as [H1 | [H1 | H1]].
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr, frame_rng.
    cbn [fst snd]. change (fs_frame_bytes 0) with 64. rewrite <- EF. lia.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. right. unfold in_zr.
    cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. rewrite <- EF. lia.
  + right. exact H1.
- (* the flag is 0 after the run *)
  intros ws msr Hlen HSr.
  pose proof (ts_region_nth (L := B_prog_listing) (PA := PA) _ _ _ 3 _ HSr eq_refl) as HR3.
  lazymatch type of HSr with st_ok_pi _ _ (extK ?E0 ?KK ?ws0) _ _ =>
    assert (X65 : bv_unsigned (ew (extK E0 KK ws0) 65) = fl)
      by (rewrite (proj1 (env_agree_extK E0 KK ws0) 65%nat) by (cbv; lia); exact U65) end.
  pose proof (ts_field (L := B_prog_listing) (PA := PA) _ _ 65 fl _ 0 1 0 1 0 1%N (SLit 0) HR3 X65 ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0.
  unfold fl in V0. rewrite V0. f_equal; try (rewrite U_SLit; apply bv_eq; vm_compute; reflexivity).
- (* the epilogue's `ret`: the text's normal arm *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HFr1 HFr2 Hgr.
  cbn [ms_mem mkst] in HFr2.
  (* the flag store's memnorm keep: memnorm_frame_of from the run's start st_ok HS and its full-memory frame HFr1 *)
  assert (KNG : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms'))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HS HFr1); exact Hm).
  assert (K' : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = fl) ->
    aview SEGS (w_H Wc) (ms_mem ms') a = aview SEGS (w_H Wc) memc a)
    by (intros a Ha Hn; exact (ts_keep (L := B_prog_listing) (PA := PA) Wc _ (ss_mem ss_Gb) memc (ms_mem ms') _ HFr2 Hwr a Ha Hn)).
  pose proof (ajxR_ar HJ') as HAR'. pose proof (ajxR_pres HJ') as HPR'.
  pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & Eslo & Eshi & _).
  prreg HS' (1%bv : bv 5) Q1.
  assert (X1 : getr (ms_regs ms') 1 = getr regs 1).
  { rewrite Q1. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) 1 = _ =>
      rewrite (proj1 (env_agree_extK E0 KK ws0) 1%nat) by (cbv; lia) end.
    apply te_entry. reflexivity. }
  (* the `ret` step: a plain SRr step (it frees nothing), lifted by YA0nH.SRr_SRr' *)
  apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (paj_ret_at (PL := PL) (PI := PA) Wc _ _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat''.
  (* the side facts at the released state *)
  assert (HSIDE' : sideb lyc (stack_free_state 0 pos Sc) Hpc Wc (ms_mem ms') b cap f own TSks TSadd ap).
  { refine (ts_side_move (L := B_prog_listing) (PA := PA) (LAWS := LAWS) (pst_img := pst_img_B) (pal_pst_static := pal_pst_static)
      lyc Sc Hpc Wc memc lyc (stack_free_state 0 pos Sc) (ms_mem ms') _ b cap f own TSks TSadd ap HSD HAR' eq_refl
      eq_refl eq_refl _ _ _ _ _ _ _).
    all: lazymatch goal with
    | |- YAkMemnorm.memnorm _ _ -> YAkMemnorm.memnorm _ _ => exact KNG
    | |- _ = _ \/ _ => right; eexists; reflexivity
    | |- _ <= ly_top _ => rewrite Etopc; lia
    | |- forall a, _ -> apresent _ _ _ /\ _ => intros a Ha; rewrite Eslo, Eshi; split; [apply HPR'; lia | lia]
    | |- forall a, _ <= a < ly_top _ -> _ =>
        intros a Ha; apply K'; [lia|]; unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia
    | |- forall p n i, In (p, n) _ -> _ =>
        intros p n i Hpn Hi;
        destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hpn) as (_ & Hb4 & Hbc & Hbapp & Hbown & _);
        pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ 0 pos HARc Hpn Hin) as Hd;
        unfold zdisjoint in Hd; cbn [fst snd] in Hd; change (fs_frame_bytes 0) with 64 in Hd; rewrite <- EF in Hd;
        apply K'; [lia|]; intros [Hw | [Hw | Hw]];
        [ lia
        | unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia
        | exact (proj2 (Hbown (p + i) ltac:(lia)) ltac:(rewrite Hw; exact Fown)) ]
    | |- forall a, in_img _ a -> _ =>
        intros a Ha Hno Her; pose proof (@pa_segs_low _ _ PA a Ha) as Hlow; apply K'; [lia|]; intros [Hw | [Hw | Hw]];
        [ exact (frm_img_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos a HARc Hin ltac:(rewrite <- EF; change (fs_frame_bytes 0) with 64; lia) Ha)
        | unfold SHADOW_OFF in *; lia
        | rewrite Hw in Ha; exact (Fimg Ha) ]
    | _ => idtac
    end. }
  (* the post: the side facts at the released state are the text's body QT (TxStr102Glue.v ts_post), and their
     memnorm keep is fQmn's; ONE fpostWbm (the batch: budgeted, no abort arm; fpostW_xbR at WR): the budget and the
     depot's growth are the side facts' at Sc (the release keeps the depot), the journal is the rebased one at WR
     unbased at that budget (YCbqGwild.ajournal_xw_unbase0R) *)
  pose proof HSIDE' as (HWIN' & _ & _ & HMN' & _).
  pose proof HSD as (_ & _ & _ & _ & _ & _ & _ & (WSG & HWIG & HWBG)).
  unfold QF, fpostWbm, fpostWb, YCbqGwild.fpostW_xbR.
  exists lyc, (stack_free_state 0 pos Sc), Hpc, (ms_regs ms'), (ms_mem ms'). eexists. exists kj, WSG.
  split.
  { rewrite X1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [exact HWBG|].
  split.
  { eapply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp); [|exact HWIG].
    apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) WR). exact HJ'. }
  split; [exact HWIN'|].
  split.
  { eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (map (getr rg) all_regs ++ [w64 F; w64 fl]) HS');
      [| vm_compute; reflexivity].
    split.
    - intros n Hn. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) n = _ =>
        rewrite (proj1 (env_agree_extK E0 KK ws0) n) by lia end.
      unfold TE. apply Eimg_low. unfold A_TEXT. lia.
    - lazymatch goal with |- ed (extK ?E0 ?KK ?ws0) = _ => rewrite (proj2 (env_agree_extK E0 KK ws0)) end.
      reflexivity. }
  split; [|exact HMN'].
  exact (ts_post lyc (stack_free_state 0 pos Sc) Hpc Wc (ms_mem ms') lyc (stack_free_state 0 pos Sc) (ms_regs ms') _
    b cap f own ap HSIDE' eq_refl eq_refl).
Qed.

(* ---- X: the closing quote's block (B 0x85b5c: a1 = .str.27, a2 = 1, a0 = t, `jal tx_put` at 0x85b6c; byte for byte
   A's 0x85580), every byte done; the call through the glue's ts_put_call with the spill carried ---- *)
Definition ss_Xb : sstate := mkSS (TS_PC_B + TS_X_OFF_B) cur_atoms [] None (mkFacts [] [] []).
Lemma ts_at_X_B : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg,
  liveb lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces bs)) (concat (ts_pieces bs)) ap ->
  spillb Wc memc F ->
  bregsb rg -> getr rg 26 = w64 (shadow_addr F) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_X_OFF_B))) memc (seg_rom SEGS)) mdc) QFb.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HSP HBR R26.
pose proof HL as (HJ & _).
pose proof HBR as (R2 & R3 & R4 & R8 & R9 & R20 & R24).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS : st_ok_pi SEGS VAL (TEb regs rg []) ss_Xb
  (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_X_OFF_B))) memc (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEb regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEb regs rg [])) by apply te_env.
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose proof HS as HSk.
paj_run_tok_xR RUN HS HJ SHOK (0, 0).
{ cbv [ss_Xb ss_mem]. apply awr_ok_nil. }
assert (KN : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk HF); exact Hm).
clear HSk.
assert (Hm : forall x, mrestrict (w_H Wc) (ms_mem ms) x = mrestrict (w_H Wc) memc x).
{ intros x. apply HFr. intros (r & Hr & _). cbv [ss_Xb ss_mem In] in Hr. destruct Hr. }
pose proof (ts_live_sameR (HSTK := HSTK_B) (LAWS := LAWS) (pst_img := pst_img_B) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm KN) as HL1.
assert (HSP1 : spillb Wc (ms_mem ms) F).
{ apply (ts_spill_keep (L := B_prog_listing) (PA := PA) (regs := regs) Wc memc); [|exact HSP]. intros a Ha. apply aview_eq_of. apply Hm. }
clear HF HG HFr.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by tskeep_B HS.
assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by tskeep_B HS.
assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by tskeep_B HS.
assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by tskeep_B HS.
assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by tskeep_B HS.
assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by tskeep_B HS.
assert (Z24 : getr (ms_regs ms) 24 = getr rg 24) by tskeep_B HS.
assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by tskeep_B HS.
assert (HBR' : bregsb (ms_regs ms)).
{ unfold ts_bregs. rewrite Z2, Z3, Z4, Z8, Z9, Z20, Z24. repeat split; assumption. }
assert (X10 : getr (ms_regs ms) 10 = w64 t) by (rewrite Q10; rewrite <- R20; te_close).
assert (X11 : getr (ms_regs ms) 11 = w64 TS_STR27_B).
{ rewrite Q11. rewrite te_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (apply pa_val_range). reflexivity. }
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (HRAOK : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite Q1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia).
(* fpre's raZ bound: the return pc is a listing slot (the closed lemma ts_ret_ceil_G_B) *)
assert (HRAC : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite Q1; exact ts_ret_ceil_G_B).
assert (HE2 : bv_unsigned (ew (TEb regs rg []) 2) = sp0) by (rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
destruct (ts_src_litR (L := B_prog_listing) (PA := PA) (pa_hi_ok := pa_hi_ok_B) (HSTK := HSTK_B) (LAWS := LAWS)
  (zs_aligned := zs_aligned) (img_shadow_vis_x := img_shadow_vis_x) (img_box := img_box_B) (img_cf_box := img_cf_box)
  WR lyc Sc Hpc Wc (ms_mem ms) _ _ pos F b cap f own _ _ ap TS_STR27_B [34] HL1 (proj1 ts_lit_img_B)
  ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
refine (ts_put_call (HSTK := HSTK_B) (LAWS := LAWS) (TXPUT := TXPUT) (HSTKP := HSTKP_B) (pst_ro := pst_ro_B)
  ch Wc (TEb regs rg []) _ ms _ lyc Sc Hpc _ pos F b cap f own _ _ ap 1 TS_STR27_B [34] []
  (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX
    (conj HEVS (conj HROOMW (conj HCONS HFRM))))))))))
  HS eq_refl ltac:(vm_compute; reflexivity) HE2
  HL1 HBR' X10 X11 Q12 HRAOK HRA4 HRAC HSRC eq_refl HKEPT HDISJ ts_ks_fin_B HOS _).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec HL2 HSPk HP2.
rewrite ts_ks_fin_B, ts_add_fin_B in HL2.
rewrite Q1. change (BASE + 17572) with (BASE + (TS_PC_B + TS_G_OFF_B)).
apply (ts_at_G_B ly2 S2 Hp2 W2 mem2 md2 kj2 pos F b2 cap2 f2 own2 (ap ++ prec) regs2 HL2 (HSPk HSP1)
  (ts_bregs_pres _ _ HBR' HP2)).
rewrite (ts_ap _ _ 26%bv HP2) by ts_cs. rewrite Z26. exact R26.
Unshelve. all: ts_ctx_B.
Qed.

(* the loop step at B is a premise, STEPb (ts_loop's premise with B's loop head and literals): the loop body is
   another lane's *)
Lemma ts_at_C_B : STEPb -> forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg,
  liveb lyc Sc Hpc Wc memc mdc kj pos F b cap f own [1] [34] ap ->
  bregsb rg -> getr rg 18 = w64 F -> getr rg 21 = w64 F -> getr rg 19 = w64 s ->
  getr rg 26 = w64 (shadow_addr F) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_C_OFF_B))) memc (seg_rom SEGS)) mdc) QFb.
Proof.
intros STEP lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HBR R18 R21 R19 R26.
pose proof HL as (HJ & HSD & EF & (HSV & HFL)).
pose proof HSD as (HWIN & HTX & HPOSs & HMNs & HRO & ((Hl & Hlen & H32 & Hfa & Hga) & HBV) & _).
pose proof HBR as (R2 & R3 & R4 & R8 & R9 & R20 & R24).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc. pose proof (ajxR_frs HJ) as HFRc.
pose proof (ajxR_pres HJ) as HPRc.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (F32 & _).
change (fs_frame_bytes 0) with 64 in Fb2, Fb3. rewrite <- EF in Fb1, Fb2, Fb3, F32.
pose proof HBV as (Hs4096 & Hs8 & Hk0 & Hsk & Hamr & Hras & Hhull & Hpres_s).
destruct (ts_sp1_range (regs := regs) Hal16 ltac:(lia)) as (Hsp1a & Hsp1b). pose proof HSTK_B as HSTK.
destruct (Hga 0%nat ltac:(rewrite length_app; cbn; lia)) as (V0 & R0). rewrite Z.add_0_r in V0.
remember (nth 0 (bs ++ [0]) 0) as c0 eqn:Ec0.
destruct (ts_C_entry_B Wc memc rg c0 R9 R19 R24 ltac:(lia) ltac:(lia) Hsp1b ltac:(lia) ltac:(lia) Hs8 R0
  ltac:(intros a Ha; apply HPRc; lia) V0) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TEb regs rg [w64 c0])) by apply te_env.
assert (A64 : ew (TEb regs rg [w64 c0]) 64 = w64 c0)
  by exact (te_more_lt (L := B_prog_listing) (PA := PA) regs rg [w64 c0] 0 ltac:(lia)).
assert (U9 : bv_unsigned (ew (TEb regs rg [w64 c0]) (xr 9)) = sp1).
{ unfold xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew (TEb regs rg [w64 c0]) (xr 18)) = F).
{ unfold xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small. lia. }
assert (U21 : bv_unsigned (ew (TEb regs rg [w64 c0]) (xr 21)) = F).
{ unfold xr. rewrite (te_cur regs rg _ 21%bv 21) by reflexivity. rewrite R21. apply unsigned_lit_small. lia. }
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose (RUNTO := paj_run_to_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose (BR := YSRrG.paj_branchR (PI := PA) WR).
(* the run from C: `beqz s3` decided by the fact s >= 4096, the two spills, the check of s, the first byte's load, to
   `beqz a1` *)
pose proof HS as HSk.
paj_run_tok_xR RUN HS HJ SHOK TS_SPAN_B.
{ (* the inline check of s (B 0x859e0 .. 0x859ec, slow block 0x85c1c / errpath_load1 0x85c28): s addressable by
     prhtx_bvis *)
  cbn [ms_mem mkst restrict]. rewrite !ts_U0.
  assert (A56 : ew (TEb regs rg [w64 c0]) (xr 24) = getr rg 24)
    by (unfold xr; apply (te_cur regs rg _ 24%bv 24); reflexivity).
  assert (A51 : ew (TEb regs rg [w64 c0]) 51 = getr rg 19) by te_close.
  rewrite ?ew_ewset_other by lia.
  rewrite A56, A51, R24, R19. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  apply (range_addressable_sub _ SHADOW_OFF s k s 1 Hras); lia. }
{ cbv [ss_Cb ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - (sp0 + dw))); [reflexivity | lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KN1 : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk HF); exact Hm).
clear HSk.
assert (U9' : bv_unsigned (ew (TEb regs rg [w64 c0]) 41) = sp1) by exact U9.
(* the run wrote s1's two spill slots only *)
assert (HWR1 : forall x : word, ~ (sp1 + 16 <= bv_unsigned x < sp1 + 32) ->
  mrestrict (w_H Wc) (ms_mem ms) x = mrestrict (w_H Wc) memc x).
{ intros x Hx. apply HFr. intros (r & Hr & Ha). apply Hx. cbv [ss_Cb ss_mem] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9 in Ha; lia. }
clear HF HG HFr.
YSRrG.psrr_branch_tokR RUN BR HS SHOK TS_SPAN_B.
- (* c0 = 0: the empty string, to the closing block X (B 0x85b5c) *)
  rewrite branch_eq_U, !ts_U0, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia.
  rewrite A64 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite YP0m.zcanon_small in Hc by lia. apply Z.eqb_eq in Hc.
  destruct (ts_list_cases_B bs) as [Ebs | (cb & post & Ebs)].
  2: { exfalso. rewrite Ebs in Ec0, Hfa. cbn [app nth] in Ec0. inversion Hfa as [|? ? Hcb _]. lia. }
  pose proof HS as HSk2.
  paj_run_to_tok_xR RUNTO HS HJ SHOK TS_SPAN_B (TS_PC_B + TS_X_OFF_B).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 41%nat (sp1 - (sp0 + dw))); [reflexivity | | cbn; lia | cbn; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite U9'. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KN2 : YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk2 HF); exact Hm).
  clear HSk2.
  (* the second run wrote nothing outside s1's two spill slots *)
  assert (HWR2 : forall x : word, ~ (sp1 + 16 <= bv_unsigned x < sp1 + 32) ->
    mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) (ms_mem ms) x).
  { intros x Hx. apply HFr. intros (r & Hri & Hr). apply Hx. vm_compute in Hri.
    destruct Hri as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9' in Hr; lia. }
  assert (HWR : forall x : word, ~ (sp1 + 16 <= bv_unsigned x < sp1 + 32) ->
    mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) memc x)
    by (intros x Hx; rewrite (HWR2 x Hx); exact (HWR1 x Hx)).
  (* the live state: the two words are the own frame's, not the saves, not F + 56 *)
  pose proof (ts_live_runR (HSTK := HSTK_B) (LAWS := LAWS) (pst_img := pst_img_B) (pal_pst_static := pal_pst_static)
    WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a => sp1 + 16 <= a < sp1 + 32) HL HJ HWR
    ltac:(intros a Ha; cbv beta in Ha; unfold ts_own; left; lia)
    ltac:(intros a Ha; cbv beta in Ha; split; [lia | first [lia | unfold alloc_ceiling in *; lia]])
    (fun Hm => KN2 (KN1 Hm))) as HL2.
  (* the spill, from the final state's slot chunks (the run's stores of s2 = F and s5 = F) *)
  pose proof (ts_region_nth (L := B_prog_listing) (PA := PA) _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  lazymatch type of HR0 with YP09.region_ok _ ?Ex _ _ =>
    assert (UX9 : bv_unsigned (ew Ex (xr 9)) = sp1) by (rewrite ?ew_ewset_other by (unfold xr; lia); exact U9);
    assert (UX18 : bv_unsigned (ew Ex (xr 18)) = F) by (rewrite ?ew_ewset_other by (unfold xr; lia); exact U18);
    assert (UX21 : bv_unsigned (ew Ex (xr 21)) = F) by (rewrite ?ew_ewset_other by (unfold xr; lia); exact U21) end.
  pose proof (ts_field (L := B_prog_listing) (PA := PA) _ _ (xr 9) sp1 _ _ _ _ _ 16 8 (SOff (xr 18) 0) HR0 UX9
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V16.
  pose proof (ts_field (L := B_prog_listing) (PA := PA) _ _ (xr 9) sp1 _ _ _ _ _ 24 8 (SOff (xr 21) 0) HR0 UX9
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V24.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V16, V24. change (N.to_nat 8) with 8%nat in V16, V24.
  rewrite ts_U_atom_mod, UX18 in V16. rewrite ts_U_atom_mod, UX21 in V24.
  assert (HSP2 : spillb Wc (ms_mem ms0) F) by exact (conj V16 V24).
  clear HF HG HFr HR0.
  assert (Z2 : getr (ms_regs ms0) 2 = getr rg 2) by tskeep_B HS.
  assert (Z3 : getr (ms_regs ms0) 3 = getr rg 3) by tskeep_B HS.
  assert (Z4 : getr (ms_regs ms0) 4 = getr rg 4) by tskeep_B HS.
  assert (Z8 : getr (ms_regs ms0) 8 = getr rg 8) by tskeep_B HS.
  assert (Z9 : getr (ms_regs ms0) 9 = getr rg 9) by tskeep_B HS.
  assert (Z20 : getr (ms_regs ms0) 20 = getr rg 20) by tskeep_B HS.
  assert (Z24 : getr (ms_regs ms0) 24 = getr rg 24) by tskeep_B HS.
  assert (Z26 : getr (ms_regs ms0) 26 = getr rg 26) by tskeep_B HS.
  pmkst HS. change (BASE + 17552) with (BASE + (TS_PC_B + TS_X_OFF_B)).
  eapply (ts_at_X_B lyc Sc Hpc Wc _ _ _ pos F b cap f own ap).
  + rewrite Ebs. rewrite Ebs in HL2. exact HL2.
  + exact HSP2.
  + unfold ts_bregs. rewrite Z2, Z3, Z4, Z8, Z9, Z20, Z24. repeat split; assumption.
  + rewrite Z26. exact R26.
- (* c0 <> 0: the loop setup, to the loop head (B 0x85a1c) *)
  rewrite branch_eq_U, !ts_U0, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia.
  rewrite A64 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite YP0m.zcanon_small in Hc by lia. apply Z.eqb_neq in Hc.
  destruct (ts_list_cases_B bs) as [Ebs | (cb & post & Ebs)].
  1: { exfalso. rewrite Ebs in Ec0. cbn [app nth] in Ec0. lia. }
  assert (Ecb : c0 = cb) by (rewrite Ebs in Ec0; exact Ec0).
  pose proof HS as HSk2.
  paj_run_to_tok_xR RUNTO HS HJ SHOK TS_SPAN_B (TS_PC_B + TS_LH_OFF_B).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 41%nat (sp1 - (sp0 + dw))); [reflexivity | | cbn; lia | cbn; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite U9'. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KN2 : YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk2 HF); exact Hm).
  clear HSk2.
  (* the second run wrote nothing outside s1's two spill slots *)
  assert (HWR2 : forall x : word, ~ (sp1 + 16 <= bv_unsigned x < sp1 + 32) ->
    mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) (ms_mem ms) x).
  { intros x Hx. apply HFr. intros (r & Hri & Hr). apply Hx. vm_compute in Hri.
    destruct Hri as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9' in Hr; lia. }
  assert (HWR : forall x : word, ~ (sp1 + 16 <= bv_unsigned x < sp1 + 32) ->
    mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) memc x)
    by (intros x Hx; rewrite (HWR2 x Hx); exact (HWR1 x Hx)).
  (* the live state: the two words are the own frame's, not the saves, not F + 56 *)
  pose proof (ts_live_runR (HSTK := HSTK_B) (LAWS := LAWS) (pst_img := pst_img_B) (pal_pst_static := pal_pst_static)
    WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a => sp1 + 16 <= a < sp1 + 32) HL HJ HWR
    ltac:(intros a Ha; cbv beta in Ha; unfold ts_own; left; lia)
    ltac:(intros a Ha; cbv beta in Ha; split; [lia | first [lia | unfold alloc_ceiling in *; lia]])
    (fun Hm => KN2 (KN1 Hm))) as HL2.
  (* the spill, from the final state's slot chunks (the run's stores of s2 = F and s5 = F) *)
  pose proof (ts_region_nth (L := B_prog_listing) (PA := PA) _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  lazymatch type of HR0 with YP09.region_ok _ ?Ex _ _ =>
    assert (UX9 : bv_unsigned (ew Ex (xr 9)) = sp1) by (rewrite ?ew_ewset_other by (unfold xr; lia); exact U9);
    assert (UX18 : bv_unsigned (ew Ex (xr 18)) = F) by (rewrite ?ew_ewset_other by (unfold xr; lia); exact U18);
    assert (UX21 : bv_unsigned (ew Ex (xr 21)) = F) by (rewrite ?ew_ewset_other by (unfold xr; lia); exact U21) end.
  pose proof (ts_field (L := B_prog_listing) (PA := PA) _ _ (xr 9) sp1 _ _ _ _ _ 16 8 (SOff (xr 18) 0) HR0 UX9
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V16.
  pose proof (ts_field (L := B_prog_listing) (PA := PA) _ _ (xr 9) sp1 _ _ _ _ _ 24 8 (SOff (xr 21) 0) HR0 UX9
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V24.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V16, V24. change (N.to_nat 8) with 8%nat in V16, V24.
  rewrite ts_U_atom_mod, UX18 in V16. rewrite ts_U_atom_mod, UX21 in V24.
  assert (HSP2 : spillb Wc (ms_mem ms0) F) by exact (conj V16 V24).
  clear HF HG HFr HR0.
  assert (Z2 : getr (ms_regs ms0) 2 = getr rg 2) by tskeep_B HS.
  assert (Z3 : getr (ms_regs ms0) 3 = getr rg 3) by tskeep_B HS.
  assert (Z4 : getr (ms_regs ms0) 4 = getr rg 4) by tskeep_B HS.
  assert (Z8 : getr (ms_regs ms0) 8 = getr rg 8) by tskeep_B HS.
  assert (Z9 : getr (ms_regs ms0) 9 = getr rg 9) by tskeep_B HS.
  assert (Z19 : getr (ms_regs ms0) 19 = getr rg 19) by tskeep_B HS.
  assert (Z20 : getr (ms_regs ms0) 20 = getr rg 20) by tskeep_B HS.
  assert (Z24 : getr (ms_regs ms0) 24 = getr rg 24) by tskeep_B HS.
  assert (Z26 : getr (ms_regs ms0) 26 = getr rg 26) by tskeep_B HS.
  prreg HS (11%bv : bv 5) Q11. prreg HS (18%bv : bv 5) Q18. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  rewrite ?ew_ewset_other in Q11, Q18, Q21, Q22, Q23, Q25, Q27 by lia.
  assert (A51 : ew (TEb regs rg [w64 c0]) 51 = getr rg 19) by te_close.
  assert (A53 : ew (TEb regs rg [w64 c0]) 53 = getr rg 21) by te_close.
  assert (A243 : ew (TEb regs rg [w64 c0]) 243 = Z_to_bv 64 (VAL (A_OBJ 2)))
    by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (@pa_val_range _ _ PA (A_OBJ 2)) as RV2.
  pmkst HS. change (BASE + 17232) with (BASE + (TS_PC_B + TS_LH_OFF_B)).
  apply (ts_loop (TS_PC := TS_PC_B) (TS_LH_OFF := TS_LH_OFF_B) (TS_STR26 := TS_STR28_B) (TS_HEX := TS_HEX_B)
    STEP 0 Wc).
  exists lyc, Sc, Hpc, (ms_mem ms0). eexists. eexists.
  exists pos, F, b, cap, f, own, ap, (ms_regs ms0), [], cb, post.
  split; [reflexivity|]. split; [exact Ebs|]. split; [reflexivity|].
  split; [exact HL2|]. split; [exact HSP2|].
  split.
  + unfold ts_lregs. split; [unfold ts_bregs; rewrite Z2, Z3, Z4, Z8, Z9, Z20, Z24; repeat split; assumption|].
    rewrite Q18, Z19, Q21, Q22, Q23, Q25, Z26, Q27, ?A51, ?A53, ?A243, R19, ?R21.
    unfold w64. rewrite !unsigned_lit_small by lia. cbn [Z.of_nat]. rewrite !Z.add_0_r.
    repeat split; try reflexivity. exact R26.
  + rewrite Q11, A64, Ecb. reflexivity.
Qed.

(* ---- B at image B: segment B's run (ts_B_run) to the opening quote's `jal tx_put` (B 0x859d0), the call through the
   glue's ts_put_call (n = 1, .str.27, the quote; it returns on every outcome of tx_put's #102 text), then segment C.
   B has not spilled F at this call, so the call's spill transport is not used: the continuation hands C the live
   state and the kept registers (s2 = s5 = F, s3 = s, s10 = F's shadow, ts_bregs). THE ONE LIFT (F12, plan row D-8):
   the wle journal ts_A_cps hands over is lifted here, at the cut B, by ajournal_xwR_mono with YA0nH.wle_wle'; from
   here every journal is at WR, every segment SRW, and the first tx_put call is at WR: no lift at a call ---- *)
Lemma ts_at_B_B : STEPb -> forall Sc memc mdc kj pos rg,
  AJ (STKS + dw) (sp0 + dw) FP0b ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj ->
  sideb ly Sc Hp W memc b0 cap0 f0 own0 [] [] [] ->
  ts_saved (L := B_prog_listing) (PA := PA) (regs := regs) W memc ->
  rdword (aview SEGS (w_H W) memc) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
  (forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> apresent (w_H W) memc a) ->
  getr rg 2 = w64 sp1 -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr ly 0 pos) -> getr rg 19 = w64 s ->
  getr rg 20 = w64 t -> getr rg 24 = w64 SHADOW_OFF ->
  SRW W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_B + TS_B_OFF_B))) memc (seg_rom SEGS)) mdc) QFb.
Proof.
intros STEP Sc memc mdc kj pos rg HJ HSD HSV Hfl Hfp R2 R3 R4 R8 R9 R10 R19 R20 R24.
assert (HJR : AJR (STKS + dw) (sp0 + dw) FP0b ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj)
  by exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx (@wle SEGS) WR (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] HJ).
apply (ts_B_run Sc memc mdc kj pos rg HJR HSD HSV Hfl Hfp R2 R3 R4 R8 R9 R10 R19 R20 R24).
intros E ss ms mdc' kj' HS Hrv Hpcs HE2 HJ' HSD' HSV' HFL' HBR Q18 Q21 Q19 Q26 X10 X11 X12 Q1.
set (F := frame_addr ly 0 pos) in *.
assert (EKS : TSks = 1 :: ts_rest bs) by (unfold TS_ks, ts_rest; rewrite s10s_ks; reflexivity).
(* B's live state at the opening call: no calls yet (ks = [], add = [], nothing appended); its journal at WR REBASED to
   the current depot (ts_liveR's form; WS = [], the journal from the entry carries no growth yet) *)
pose proof (conj (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ [] HJ')
  (conj HSD' (conj (eq_refl F) (conj HSV' HFL')))) as HLIVE0.
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (EC : TS_PC_B + TS_C_OFF_B = 17160) by (vm_compute; reflexivity).
assert (HRAOK : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite Q1, EC; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite Q1, EC, unsigned_lit_small by lia; lia).
(* fpre's raZ bound: the return pc is a listing slot (the closed lemma ts_ret_ceil_C_B) *)
assert (HRAC : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite Q1, EC; exact ts_ret_ceil_C_B).
destruct (ts_src_litR (L := B_prog_listing) (PA := PA) (pa_hi_ok := pa_hi_ok_B) (HSTK := HSTK_B) (LAWS := LAWS)
  (zs_aligned := zs_aligned) (img_shadow_vis_x := img_shadow_vis_x) (img_box := img_box_B) (img_cf_box := img_cf_box)
  WR ly Sc Hp W (ms_mem ms) _ _ pos F b0 cap0 f0 own0 [] [] [] TS_STR27_B [34] HLIVE0 (proj1 ts_lit_img_B)
  ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
refine (ts_put_call (HSTK := HSTK_B) (LAWS := LAWS) (TXPUT := TXPUT) (HSTKP := HSTKP_B) (pst_ro := pst_ro_B)
  ch W E ss ms mdc' ly Sc Hp kj' pos F b0 cap0 f0 own0 [] [] [] 1 TS_STR27_B [34] (ts_rest bs)
  (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX
    (conj HEVS (conj HROOMW (conj HCONS HFRM))))))))))
  HS Hrv Hpcs HE2 HLIVE0 HBR X10 X11 X12 HRAOK HRA4 HRAC HSRC eq_refl HKEPT HDISJ (eq_sym EKS) HOS _).
(* the continuation: segment C (the spill transport, the call's second premise, is not used) *)
intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec HL2 _ HP2. cbn [app] in HL2.
rewrite Q1.
apply (ts_at_C_B STEP ly2 S2 Hp2 W2 mem2 md2 kj2 pos F b2 cap2 f2 own2 prec regs2 HL2 (ts_bregs_pres _ _ HBR HP2)).
- rewrite (ts_ap _ _ 18%bv HP2) by ts_cs. exact Q18.
- rewrite (ts_ap _ _ 21%bv HP2) by ts_cs. exact Q21.
- rewrite (ts_ap _ _ 19%bv HP2) by ts_cs. exact Q19.
- rewrite (ts_ap _ _ 26%bv HP2) by ts_cs. exact Q26.
Unshelve. all: ts_ctx_B.
Qed.

(* ---- the assembly modulo the loop: the entry (ts_A_cps), segment B and the opening quote (ts_at_B_B), segment C to
   the closing block (ts_at_X_B, ts_at_G_B) or the loop head; the loop closes by the glue's ts_loop from STEPb ---- *)
Lemma tx_string_B_of_step : STEPb -> SRW W (cfg_at SEGS (SIGMA AS_tx_string) regs mem md) QFb.
Proof. intros STEP. apply ts_A_cps. exact (ts_at_B_B STEP). Qed.

(* ---- the whole walk: the loop body is BTxStep.ts_step_B (closing block = ts_at_X_B) ---- *)
Lemma tx_string_B_main : SRW W (cfg_at SEGS (SIGMA AS_tx_string) regs mem md) QFb.
Proof.
apply tx_string_B_of_step.
eapply BTxStep.ts_step_B.
all: try eassumption.
all: try exact (proj2 ts_lit_img_B).
unfold BTxStep.ts_HX_B. intros lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HSP HBR R26.
exact (ts_at_X_B lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HSP HBR R26).
Qed.

End g.

(* ---- K0Tx's text (PRH_FnTx.v 7cf918708def :665-720: SRr' segs RZ_cf over fpostWbmR at wle' segs RZ_cf) at image B'
   ---- *)
Theorem tx_string_B_holds : ttx_string_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Proof.
unfold ttx_string_specX.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt
  fail ran most.
cbv zeta.
intros HPRE0 HCL HROOM HPOS HOS HROOMW HCONS H10 H11 HFWIN HPLACE HTRACE HREC HINV HSTR HBVIS HLEN HLED HEVS HLIVE HMAX
  HCNT.
destruct HPRE0 as (HPRE & HROD & _ & _ & HFRM).
eapply tx_string_B_main; eassumption.
Qed.
End f.
End w.
(* the audit: the top theorem's axioms (its Section hypotheses are its arguments, each MARKED above with its owner) *)
Print Assumptions tx_string_B_holds.
About tx_string_B_holds.
(* the Print implicit check: the top theorem and the glue definitions this re-fit changed, every implicit argument
   shown (image B' names only: PI_prog_B / B_prog_listing / prh_img_B) *)
Set Printing Implicit.
Check tx_string_B_holds.
Print QT.
Print QF.
Print ts_side.
Print ts_live.
Print ts_liveR.
Print ts_pre.
Unset Printing Implicit.
