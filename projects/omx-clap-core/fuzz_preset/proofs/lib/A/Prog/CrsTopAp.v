(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 359 of its 421 lines of code are new or changed and 716 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): THE TOP of the walk of check_reject_clean_starved against the text
   tcheck_reject_clean_starved_specX. It discharges, at the A' instance, every premise of the segment lemmas that the
   instance decides (one lemma each: the engine's Section hypotheses HX_*, the image facts, the instance facts HI_*,
   the bound HB_took and the kit's transport record CrsKeep), and states what stays open as named premises.
   rule 24: proves function check_reject_clean_starved (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record
   of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A
   or lib/B, its released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan
   Proof.v existed for check_reject_clean_starved). Written new.
   INPUTS.
   - Pin A' asan sha256 1be0f53d96cb9d6c (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/A/Listing_prog.v blob 7ed1529926bd + lib/A/PAImg_prog.v blob 505a51ff7d08 (h-verbs-1 74dcda1eda12);
     entry 0x82160 = slot 736 (A_entry_check_reject_clean_starved).
   - The text tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v:1756-1858
     (no DW, the strtod model keyed, the wild room, the room counts,
     the consumer window and `ran' = ran`, a post at a wild budget), through the kit lib/A/Prog/CrsKitAp.v and its
     crs_spec, with the kit's two bridges lib/A/Prog/CrsBridgeAp.v (crs_wexact_of_text, crs_free0_of_text: the latter
     from the NULL-only free text tfuzz_free_null_specX) over CrsWexAp.v and CrsFree0Ap.v, all on this branch.
   - THE SEGMENTS: CrsSeg_R / F / E / X3 / H3 / Z / X2 / H2 / W1 / X1 / H1 and CrsWitAp / CrsBoundAp, on this branch,
     ported to the cut; X1 takes pj_parse's text tpj_parse_specX itself, its guarded THE OUTCOME OF AN INJECTED
     READING included, at the re-hiding relation.
   - The cursor set of the starved reading's pj_parse: CrsSeg_X1.x_cw, the repaired prh_cw_pj's
     (lib/A/PRH_Base.v:1779-1785) two wild cursor traces at crcs's arguments, met by CrsSeg_X1.x_cw_pj;
     pj_parse's text is taken at every cursor set (HT_pj_parse), as CrsTopBp.v takes it.
   - THE INSTANCE: B := AD2l.TfibB (lib/A/AD2l.v blob eb321db7a357), PA := PI_prog_A, PI := prh_img_A,
     cp := CfParamsPreset.CfParams_preset (lib/A/CfParamsPreset.v), ARx := crs_ARx_Ap below = YGcallcf.v:211's ARxs at
     TfibB (h-mani-a8's ARcf with the message buffer placed, xs_placed_cf), laws YGcallcf.AR_laws_x_xs of
     YG0lawscf.AR_laws_ok_cf (YGcallcf.v blob 6d2b13c24437). fx, rc, ci, RL, SK stay Section variables (the text
     quantifies over them).
   - Image witnesses: lib/A/PALibA.v blob 88c72c8175cf (palib_A), lib/A/Prog/CrsWitAp.v blob 23fe6f23df62 (the use-after-
     return cell, __asan_stack_malloc_1, the statics), lib/A/AImgShadowVis.v (the image's shadow cover).
   HELPER NAMES: the segment files are Required, not Imported (H1 / H2 / H3 share helper names: h_*, hw_*, HSLOT,
   hfd, hpost ...), and every lemma of theirs is cited by qualified name, so no clash reaches this file.
   NUMERALS: 8 (granule), 56 (sizeof (struct pj)), 64 (the image margin of kept_at), 2 ^ 28 (HB_took, DERIVED by
   CrsBoundAp.crs_took_le). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
(* E's frame-area row text (HX_asmr) lives in the engine file of record: Required, cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
(* the cf instance, its laws and its shadow facts: Required, cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0scf YG0lawscf YGcallcf YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfTreeVis YGcfHeadSh YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
(* the live-set counts at a position of the run (h-pre-b1's leaf, lib/Spec/PresetRoomCounts.v blob 8a4dfa84e8be,
   origin/cold/h-pre-b1-iface-102 94736cca66e0): the two class-24 bounds of W1 and Z *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnReader PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
(* the instance record, its code-record tables, its shadow cover and its PALib: Required, cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l AF0m AImgShadowVis PALibA.
(* the frame-area row at class 1 (HX_asmr's text), proved by a Theorem Labs lane's frame-class lane: discharged below *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require FCifaceCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v FCm01xm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_WalkEnv PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import CrsKitAp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require CrsWitAp CrsBoundAp CrsWexAp CrsFree0Ap.
(* the kit's bridges from the writer and free texts to the walk's two interims *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require CrsBridgeAp.
(* the eleven segments: Required, not Imported (header) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require CrsSeg_R CrsSeg_F CrsSeg_E.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require CrsSeg_X3 CrsSeg_H3 CrsSeg_Z CrsSeg_X2 CrsSeg_H2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require CrsSeg_W1 CrsSeg_X1 CrsSeg_H1.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List Permutation.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* two entries of a pairwise-disjoint list whose ranges meet are the same entry *)
Lemma crs_pw_eq : forall (l : list (Z * Z)) x y, pairwise zdisjoint l -> In x l -> In y l -> ~ zdisjoint x y -> x = y.
Proof.
induction l as [|z t IH]; intros x y Hp Hx Hy Hd; [destruct Hx|].
cbn [pairwise] in Hp. destruct Hp as [Hz Ht].
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- reflexivity.
- exfalso. apply Hd. exact (proj1 (Forall_forall _ _) Hz y Hy).
- exfalso. apply Hd. pose proof (proj1 (Forall_forall _ _) Hz x Hx) as D. unfold zdisjoint in D |- *. lia.
- exact (IH x y Ht Hx Hy Hd).
Qed.

(* a one-byte const cell's value, read back *)
Lemma crs_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation CP := (CfParamsPreset.CfParams_preset).
#[local] Notation TA := (AD2l.TfibB).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_A) (PA := PA) TA).

(* ======================================================================================================== *)
(* ---- THE INSTANCE RELATION and its laws ---- *)

(* YGcallcf.v:211 ARxs at TfibB: h-mani-a8's allocator relation ARcf with the error-message buffer placed *)
Definition crs_ARx_Ap : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => YG0ncf.ARcf SEGS TA ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S.
#[local] Notation ARA := crs_ARx_Ap.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS TA PST ARA).

(* LAWS: AR_laws_x at the harness head, from AR_laws_cf alone *)
Lemma crs_Ap_laws : AR_laws_x SEGS TA ARA (@cf_head CP).
Proof. unfold crs_ARx_Ap. exact (YGcallcf.AR_laws_x_xs SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA)). Qed.

(* ======================================================================================================== *)
(* ---- THE ENGINE'S SECTION HYPOTHESES at the instance (each the segment's premise text, B := TfibB, ARx := the
   instance relation) ---- *)

(* HX_asfx (YGcallSx.v ASFX): YGcallScf.astack_free_x_xs *)
Lemma crs_Ap_HX_asfx : forall ly S Hp W mem md mem' md' cid pos,
    ARA ly S Hp W mem md -> In (cid, pos) (frames S) ->
    aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> aowned TA ly S a -> a <> flag_addr ly cid pos ->
       aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
    (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
    m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
    (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
    ARA ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. unfold crs_ARx_Ap. exact (YGcallScf.astack_free_x_xs SEGS TA). Qed.

(* HX_fflx (YGcallSx.v FFLX): YGcallScf.frame_flag_x_xs *)
Lemma crs_Ap_HX_fflx : forall ly S Hp (W : world SEGS) mem md cid pos,
    ARA ly S Hp W mem md -> In (cid, pos) (frames S) ->
    aowned TA ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Proof. unfold crs_ARx_Ap. exact (YGcallScf.frame_flag_x_xs SEGS TA). Qed.

(* HX_sfx (YGcallSx.v SFX): YGcallScf.stack_free_x_any, at any relation *)
Lemma crs_Ap_HX_sfx : forall ly S Hp W mem md cid pos, ARA ly S Hp W mem md -> In (cid, pos) (frames S) ->
    exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. exact (YGcallScf.stack_free_x_any SEGS ARA). Qed.

(* HX_fflp (Crt102Tail.v FFLP): the flag byte is present, AR_flag_law_ok_cf's first conjunct *)
Lemma crs_Ap_HX_fflp : forall ly S Hp (W : world SEGS) mem md cid pos, ARA ly S Hp W mem md ->
    In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Proof.
intros ly S Hp W mem md cid pos [HAR _] Hin.
exact (proj1 (YG0scf.AR_flag_law_ok_cf SEGS TA ly S Hp W mem md cid pos HAR Hin)).
Qed.

(* HX_ownlow (YGcallx.v ARx_owned_low_law): YGcallcf.ARx_owned_low_law_xs *)
Lemma crs_Ap_HX_ownlow : ARx_owned_low_law SEGS TA ARA.
Proof. unfold crs_ARx_Ap. exact (YGcallcf.ARx_owned_low_law_xs SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA)). Qed.

(* ---- E's image facts ---- *)
(* HX_pal: PALibA.palib_A *)
Lemma crs_Ap_HX_pal : PALib (L := A_prog_listing) (PI := PA) TA.
Proof. exact PALibA.palib_A. Qed.
(* HX_pal_uar_img / HX_pal_sm1 / HX_pal_pst_static: CrsWitAp's three lemmas *)
Lemma crs_Ap_HX_pal_uar_img : IMG_LO <= as_uar_cell TA /\ as_uar_cell TA + 4 <= IMG_TOP.
Proof. exact CrsWitAp.crs_wit_pal_uar_img_A'. Qed.
Lemma crs_Ap_HX_pal_sm1 : SIGMA AS___asan_stack_malloc_1 = pc_stack_malloc (as_code TA) 1.
Proof. exact CrsWitAp.crs_wit_pal_sm1_A'. Qed.
Lemma crs_Ap_HX_pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static TA) /\ ~ (as_errno TA <= a < as_errno TA + 4).
Proof. exact CrsWitAp.crs_wit_pal_pst_static_A'. Qed.

(* ---- the instance facts ---- *)
(* HI_head8: the preset's harness head is 16 bytes (CfParamsPreset.preset_head_wide) *)
Lemma crs_Ap_HI_head8 : 8 <= @cf_head CP.
Proof. exact CfParamsPreset.preset_head_wide. Qed.
(* HI_head: CfParams_preset's head is the model's HEAD (alloc.c:28), by computation *)
Lemma crs_Ap_HI_head : @cf_head CP = PresetReqAt.HEAD.
Proof. reflexivity. Qed.

(* HB_took: CrsBoundAp.crs_took_le at the instance *)
Lemma crs_Ap_HB_took : forall CTX0 C, crs_pre TA ARA CTX0 C -> c_took C <= 2 ^ 28.
Proof. intros CTX0 C H. eapply CrsBoundAp.crs_took_le. exact H. Qed.

(* ======================================================================================================== *)
(* ---- THE KIT'S TRANSPORT RECORD CrsKeep at the instance, one lemma per field ---- *)

(* the shadow of a range of the image's zero-shadow list is 0, so the range is addressable (aso_zshadow: 8-aligned) *)
Lemma crs_Ap_zs_ra : forall ly S Hp W mem md q m, ARA ly S Hp W mem md -> In (q, m) (as_zero_shadow TA) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q m.
Proof.
intros ly S Hp W mem md q m HAR Hin.
pose proof (alx_zshadow _ _ _ crs_Ap_laws ly S Hp W mem md (q, m) HAR (or_intror Hin)) as HZ.
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ AD2l.TfibB_ok) (q, m) Hin) as (_ & _ & Hq & Hm & _).
exact (zero_shadow_range _ _ q m Hq Hm HZ).
Qed.

(* the shadow byte of every image address is in the view (the image's cover check, AImgShadowVis.v, at ARcf) *)
Lemma crs_Ap_img_shadow : forall ly S Hp W mem md a, ARA ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HAR _] Ha.
exact (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover SEGS TA AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow
  IMG_LO IMG_TOP AImgShadowVis.tfib_img_shadow_cover
  (AImgShadowVis.tfib_zsh_incl TA (AF0m.ts_zsh _ AD2l.TfibB_syms))
  (AImgShadowVis.tfib_const_shadow_incl TA (AF0m.ts_const _ AD2l.TfibB_syms))
  ly S Hp W mem md a HAR Ha).
Qed.

(* so the shadow hull of a range 64 bytes inside the image is in the view *)
Lemma crs_Ap_img_hull : forall ly S Hp W mem md p n, ARA ly S Hp W mem md ->
  IMG_LO + 64 <= p -> p + n + 64 <= IMG_TOP -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md p n HAR Hlo Hhi Hn s Hs.
replace s with (shadow_addr ((s - SHADOW_OFF) * 8)) by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
apply (crs_Ap_img_shadow ly S Hp W mem md _ HAR).
unfold shadow_addr in Hs. lia.
Qed.

(* a const shadow cell of the image (route (a) of kept_img) makes its byte addressable *)
Lemma crs_Ap_cell_ra : forall ly S Hp W mem md a v, ARA ly S Hp W mem md ->
  In (z1 (ANum (shadow_addr a)) v) (as_const TA ly) -> (v = 0 \/ a mod 8 < v < 8) ->
  exists s, aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF a) = Some s /\ saddr_ok a s.
Proof.
intros ly S Hp W mem md a v HAR Hin Hv.
pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ crs_Ap_laws ly S Hp W mem md HAR) _ Hin) as HC.
unfold cell_holds, z1, c1 in HC. cbn [c_at c_w c_val aeval] in HC.
assert (E : aview SEGS (w_H W) mem (shadow_addr a + Z.of_nat 0) = Some (le_byte v 1 0))
  by exact (HC 0%nat ltac:(lia)).
rewrite crs_le_byte1 in E by lia. rewrite Z.add_0_r in E.
exists v. split; [unfold shadow_of_addr; unfold shadow_addr in E; exact E | unfold saddr_ok; lia].
Qed.

(* a live allocator block whose base is not a hidden head: its shadow is a block shadow (alx_shadow), since no
   hidden head lies inside it (every hidden head is the base of another, disjoint, block) *)
Lemma crs_Ap_live_blk : forall ly S Hp W mem md Lam peak cnt fail ran most own b m p n,
  ARA ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks TA ly S) -> ~ In b Hp -> b <= p -> p + n <= b + m -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m p n HAR HL Hb Hnh Hbp Hpn Hn.
pose proof (@cf_head_nonneg CP) as CH0.
assert (Hno : forall h, In h Hp -> ~ (b <= h < b + req_size m)).
{ intros h Hh Hr.
  pose proof HL as HH. apply prh_ledger_heads in HH.
  apply (Permutation_in _ HH) in Hh. apply in_map_iff in Hh as ([a k] & Ea & Hak). cbn [fst] in Ea.
  pose proof HL as HB. apply prh_ledger_blocks in HB.
  pose proof (proj1 (Forall_forall _ _) HB (a, k) Hak) as (Hk0 & Hb2 & Hh2 & _). cbn [fst snd] in Hk0, Hb2, Hh2.
  rewrite Ea in Hb2, Hh2.
  destruct (alx_blocks _ _ _ crs_Ap_laws ly S Hp W mem md b m HAR Hb) as (_ & _ & _ & _ & _ & PW).
  assert (Eq : (h, req_size (k + cf_head)) = (b, req_size m)).
  { apply (crs_pw_eq _ _ _ PW).
    - apply in_map_iff. exists (h, k + cf_head). split; [reflexivity | exact Hb2].
    - apply in_map_iff. exists (b, m). split; [reflexivity | exact Hb].
    - assert (R1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
      unfold zdisjoint. cbn [fst snd]. lia. }
  injection Eq as Ehb _. apply Hnh. rewrite <- Ehb. exact Hh2. }
destruct (alx_shadow _ _ _ crs_Ap_laws ly S Hp W mem md b m HAR Hb Hno) as [BS HV].
assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split.
- exact (block_shadow_range _ _ b (req_size m) p n BS Hbp ltac:(lia)).
- exact (YGcfHeadSh.shadow_hull_vis_sub_cf _ b (req_size m) p n HV Hbp ltac:(lia)).
Qed.

(* kp_tree_vis: the tree's blocks are harness blocks of the ledger (YGcfTreeVis.tree_vis_of_blocks_cf) *)
Lemma crs_Ap_tree_vis : forall ly S Hp W mem md Lam peak cnt fail ran most own D,
    ARA ly S Hp W mem md ->
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    (forall bk, In bk D -> In bk Lam) -> PRH_FnWriter.prhWriter_tree_vis W mem D.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own D [HAR _] HL HD.
unfold PRH_FnWriter.prhWriter_tree_vis.
apply (YGcfTreeVis.tree_vis_of_blocks_cf SEGS TA ly S Hp W mem md D HAR).
intros a k Hin.
pose proof HL as HB. apply prh_ledger_blocks in HB.
pose proof (proj1 (Forall_forall _ _) HB (a, k) (HD _ Hin)) as (_ & Hb & Hh & _).
exact (conj Hb Hh).
Qed.

(* kp_home_sh: the reader's home window - a ledger block, a registered global, an image string, or an unhidden
   live block - is addressable with its hull in the view *)
Lemma crs_Ap_home_sh : forall ly S Hp W mem md Lam peak cnt fail ran most own p n,
    ARA ly S Hp W mem md ->
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    PRH_FnReader.prhReader_home TA ly S Hp Lam p n ->
    0 < n -> 0 <= p -> p + n <= YM05.alloc_ceiling ->
    range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\
    shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n HAR HL HH Hn _ _.
unfold PRH_FnReader.prhReader_home in HH.
destruct HH as [HK | (b & m & Hb & Hnh & Hbp & Hpn)].
2: exact (crs_Ap_live_blk ly S Hp W mem md Lam peak cnt fail ran most own b m p n HAR HL Hb Hnh Hbp Hpn Hn).
unfold kept_at in HK.
destruct HK as [(b & m & Hin & Hbp & Hpn) | [(Hzs & Hlo & Hhi & _) | HKI]].
- (* a harness block of the ledger *)
  pose proof (crs_Ap_tree_vis ly S Hp W mem md Lam peak cnt fail ran most own [(b, m)] HAR HL
    ltac:(intros bk [<- | []]; exact Hin)) as TV.
  unfold PRH_FnWriter.prhWriter_tree_vis, YGcfTreeVis.tree_vis_cf in TV.
  destruct (TV b m (or_introl eq_refl)) as (_ & _ & _ & _ & RA & HV & _).
  split.
  + exact (range_addressable_sub _ _ b m p n RA Hbp Hpn).
  + exact (YGcfHeadSh.shadow_hull_vis_sub_cf _ b m p n (HV ltac:(lia)) Hbp Hpn).
- (* a registered global: zero shadow, 64 bytes inside the image *)
  assert (Hlo' : IMG_LO + 64 <= p) by exact Hlo. assert (Hhi' : p + n + 64 <= IMG_TOP) by exact Hhi.
  destruct Hzs as (q & m & Hq & Hqp & Hpm).
  split.
  + exact (range_addressable_sub _ _ q m p n (crs_Ap_zs_ra ly S Hp W mem md q m HAR Hq) Hqp Hpm).
  + exact (crs_Ap_img_hull ly S Hp W mem md p n HAR Hlo' Hhi' Hn).
- (* an image string under route (a): each granule zero shadow or a const shadow cell *)
  unfold kept_img in HKI. destruct HKI as (Hlo & Hhi & Hro).
  assert (Hlo' : IMG_LO + 64 <= p) by exact Hlo. assert (Hhi' : p + n + 64 <= IMG_TOP) by exact Hhi.
  split; [|exact (crs_Ap_img_hull ly S Hp W mem md p n HAR Hlo' Hhi' Hn)].
  intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & Hrs). unfold ro_shadow_ok in Hrs.
  destruct Hrs as [(q & m & Hq & Hqx & Hxm) | (v & Hv & Hvr)].
  + exact (crs_Ap_zs_ra ly S Hp W mem md q m HAR Hq x ltac:(lia)).
  + exact (crs_Ap_cell_ra ly S Hp W mem md x v HAR (Hv ly) Hvr).
Qed.

(* kp_home_move: a permutation of Lam and of the allocator blocks keeps the home (the hidden heads are the ledger's) *)
Lemma crs_Ap_home_move : forall ly S Hp W mem Lam peak cnt fail ran most own ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3
      ran3 most3 own3 p n,
    LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
    LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 ->
    Permutation Lam3 Lam -> Permutation (ablocks TA ly3 S3) (ablocks TA ly S) ->
    PRH_FnReader.prhReader_home TA ly S Hp Lam p n -> PRH_FnReader.prhReader_home TA ly3 S3 Hp3 Lam3 p n.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 p n
  HL HL3 HPL HPB HH.
unfold PRH_FnReader.prhReader_home in HH |- *.
destruct HH as [HK | (b & m & Hb & Hnh & Hbp & Hpn)].
- left. unfold kept_at in HK |- *. destruct HK as [(b & m & Hin & H1 & H2) | HK]; [left | right; exact HK].
  exists b, m. split; [exact (Permutation_in _ (Permutation_sym HPL) Hin) | split; assumption].
- right. exists b, m. split; [exact (Permutation_in _ (Permutation_sym HPB) Hb)|].
  split; [|split; assumption].
  intros Hh3. apply Hnh.
  pose proof HL as HH. apply prh_ledger_heads in HH.
  pose proof HL3 as HH3. apply prh_ledger_heads in HH3.
  apply (Permutation_in _ (Permutation_sym HH)).
  apply (Permutation_in _ (Permutation_map (fun ak => fst ak - cf_head) HPL)).
  exact (Permutation_in _ HH3 Hh3).
Qed.

(* kp_frame_keep: the journal's frame clause at FP = [], at any world relation (the clause does not read it) *)
Lemma crs_Ap_frame_keep : forall {R : world SEGS -> world SEGS -> Prop} STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3
    mem3 md3 k cid pos a,
    ajournal_xR (SK := SK) SEGS TA PST ARA R STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    In (cid, pos) (frames S) ->
    (in_zr a (frame_rng ly (cid, pos)) \/
     in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) mem a.
Proof.
intros R STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos a HJ Hin Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
exact (HF cid pos a Hin Ha (inFP_nil a)).
Qed.

(* kp_obj_keep: the frame stays (frames S3 = own ++ frames S, alx_layout keeps its address) and the object's shadow
   bytes lie in the frame's shadow (the frame is 32-aligned, the object 8-aligned), which the journal keeps *)
Lemma crs_Ap_obj_keep : forall {R : world SEGS -> world SEGS -> Prop} STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3
    mem3 md3 k p,
    ARA ly S Hp W mem md ->
    ajournal_xR (SK := SK) SEGS TA PST ARA R STK0 sp0 [] ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k ->
    ck_obj_home ly S W mem p -> ck_obj_home ly3 S3 W3 mem3 p.
Proof.
intros R STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k p HAR HJ HO.
unfold ck_obj_home, ck_in_frame in HO |- *.
destruct HO as (Hp8 & (cid & pos & Hin & Hlo & Hhi) & HRA).
pose proof HJ as (_ & Hle & _ & _ & _ & Hfr & _).
destruct (alx_layout _ _ _ crs_Ap_laws ly S Hp W mem md ly3 HAR Hle) as (_ & Hfa & _).
destruct (alx_frames _ _ _ crs_Ap_laws ly S Hp W mem md cid pos HAR Hin) as (F32 & _ & _ & _).
split; [exact Hp8|]. split.
- exists cid, pos. split; [rewrite Hfr; apply in_or_app; right; exact Hin|].
  rewrite (Hfa cid pos). split; lia.
- intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  apply (crs_Ap_frame_keep (R := R) STK0 sp0 ly S Hp W mem md own ly3 S3 Hp3 W3 mem3 md3 k cid pos _ HJ Hin).
  right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
Qed.

(* HK: the record, from its five fields *)
Lemma crs_Ap_keep : CrsKeep (SK := SK) TA ARA.
Proof.
constructor.
- exact crs_Ap_home_sh.
- exact crs_Ap_home_move.
- exact crs_Ap_tree_vis.
- exact (@crs_Ap_frame_keep (@wle SEGS)).
- exact (@crs_Ap_obj_keep (@wle SEGS)).
- exact @crs_Ap_frame_keep.
- exact @crs_Ap_obj_keep.
Qed.

(* ---- the class-24 bounds fuzz_free's text asks at its entry (W1's and Z's crs_cnt24_<SEG>): every position of the
   model run bounds the live class-24 requests, PresetRoomCounts.counts_of_room_pos_rl's second conjunct ---- *)
Lemma crs_Ap_cnt24_W1 : forall C : crsC, CrsSeg_W1.crs_cnt24_W1 C.
Proof. intros C i hist S H. exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ H)). Qed.
Lemma crs_Ap_cnt24_Z : forall C : crsC, CrsSeg_Z.crs_cnt24_Z C.
Proof. intros C i hist S H. exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ H)). Qed.

(* ======================================================================================================== *)
(* ---- the run's two meter caps within the instance's (X1's and W1's HI_hull): the one witness, W1's ---- *)
#[local] Notation HI_hull_Ap := CrsSeg_W1.crs_W1_HI_hull.

(* ======================================================================================================== *)
(* ---- THE COMPOSITION. The segments chained backwards at one stage record C: R, F, then X3 / H3, Z, X2 / H2, W1,
   X1, H1. X1 goes on after pj_parse at the REBASED context crs_with_dp C d ws (the kit's record comment: pj_parse's
   cursor traces are wild under the kit's repaired prh_cw_pj, so the walk's journal moves its entry depot), so the chain
   R .. W1 is built at every context (crs_Ap_from_W1), and every per-C premise of it is read by the rebase unchanged
   (crs_with_dp moves only c_dp / c_ws). Every instance premise is one of the lemmas above; the open ones (the callee
   texts, crs_free0, crs_wexact) are premises here (crs_holds_Ap turns crs_free0 and crs_wexact into the texts by the
   kit's bridges), pj_parse's text itself at every cursor set (CrsTopBp.v's route). Each segment lemma is applied
   with every fact in context, so the order of a lane's premises does not
   matter. ---- *)
Lemma crs_Ap_from_W1 : forall (CTX0 : list (list Z)) (C : crsC),
  (forall fx', tcheck_reject_clean_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_count_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_fail_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_ran_out_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_free_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', CrsFree0Ap.crs_free0 (fx := fx') (SK := SK) TA ARA) ->
  (forall fx', CrsWexAp.crs_wexact (fx := fx') (SK := SK) TA ARA CTX0 C) ->
  c_took C <= 2 ^ 28 ->
  crs_from_R (SK := SK) TA ARA CTX0 C /\ crs_from_W1 (SK := SK) TA ARA CTX0 C.
Proof.
intros CTX0 C HT_check_reject_clean HT_fuzz_alloc_count HT_fuzz_alloc_fail HT_fuzz_alloc_live
  HT_fuzz_alloc_ran_out HT_fuzz_free HT_fuzz_free0 HW_exact HB_took.
pose proof (crs_Ap_cnt24_W1 C) as H24W1. pose proof (crs_Ap_cnt24_Z C) as H24Z.
pose proof crs_Ap_laws as LAWS. pose proof crs_Ap_keep as HK. pose proof HI_hull_Ap as HI_hull.
pose proof crs_Ap_HI_head as HI_head. pose proof crs_Ap_HI_head8 as HI_head8.
pose proof crs_Ap_HX_asfx as HX_asfx. pose proof crs_Ap_HX_fflx as HX_fflx.
pose proof crs_Ap_HX_sfx as HX_sfx. pose proof crs_Ap_HX_fflp as HX_fflp.
assert (KR : crs_from_R (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_R.crs_seg_R; eassumption).
assert (KF : crs_from_F (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_F.crs_seg_F; eassumption).
assert (KX3 : crs_from_X3 (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_X3.crs_seg_X3; eassumption).
assert (KH3 : crs_from_H3 (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_H3.crs_seg_H3; eassumption).
assert (KZ : crs_from_Z (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_Z.crs_seg_Z; eassumption).
assert (KX2 : crs_from_X2 (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_X2.crs_seg_X2; eassumption).
assert (KH2 : crs_from_H2 (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_H2.crs_seg_H2; eassumption).
assert (KW1 : crs_from_W1 (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_W1.crs_seg_W1; eassumption).
split; [exact KR | exact KW1].
Qed.

Lemma crs_Ap_from_H1 : forall (CTX0 : list (list Z)) (C : crsC),
  (forall fx', tcheck_reject_clean_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_count_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_fail_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_alloc_ran_out_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', PRH_FnAlloc.tfuzz_free_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK) ->
  (forall fx', CrsFree0Ap.crs_free0 (fx := fx') (SK := SK) TA ARA) ->
  (forall (fx' : YK11.FPState) (CW : list (list Z)),
     PRH_FnPj.tpj_parse_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK CTX0 CW) ->
  (forall fx', CrsWexAp.crs_wexact (fx := fx') (SK := SK) TA ARA CTX0 C) ->
  c_took C <= 2 ^ 28 ->
  crs_from_H1 (SK := SK) TA ARA CTX0 C.
Proof.
intros CTX0 C HT_check_reject_clean HT_fuzz_alloc_count HT_fuzz_alloc_fail HT_fuzz_alloc_live
  HT_fuzz_alloc_ran_out HT_fuzz_free HT_fuzz_free0 HT_pj_parse HW_exact HB_took.
pose proof crs_Ap_laws as LAWS. pose proof crs_Ap_keep as HK.
(* R .. W1 at C and at every rebased context of C (crs_wexact and c_took read the fields the rebase keeps) *)
assert (KRW : forall d ws, crs_from_R (SK := SK) TA ARA CTX0 (crs_with_dp C d ws) /\
                           crs_from_W1 (SK := SK) TA ARA CTX0 (crs_with_dp C d ws)).
{ intros d ws. exact (crs_Ap_from_W1 CTX0 (crs_with_dp C d ws) HT_check_reject_clean HT_fuzz_alloc_count
    HT_fuzz_alloc_fail HT_fuzz_alloc_live HT_fuzz_alloc_ran_out HT_fuzz_free HT_fuzz_free0 HW_exact HB_took). }
destruct (crs_Ap_from_W1 CTX0 C HT_check_reject_clean HT_fuzz_alloc_count HT_fuzz_alloc_fail HT_fuzz_alloc_live
  HT_fuzz_alloc_ran_out HT_fuzz_free HT_fuzz_free0 HW_exact HB_took) as (KR & KW1).
assert (KX1 : crs_from_X1 (fx := fx) (SK := SK) TA ARA CTX0 C).
{ exact (CrsSeg_X1.crs_seg_X1 TA ARA LAWS CTX0 C HT_fuzz_alloc_fail HT_check_reject_clean HT_pj_parse HI_hull_Ap HK
    (fun d ws => proj1 (KRW d ws)) (fun d ws => proj2 (KRW d ws))). }
eapply CrsSeg_H1.crs_seg_H1; eassumption.
Qed.

(* ======================================================================================================== *)
(* ---- THE TOP: the text tcheck_reject_clean_starved_specX (lib/A/PRH_FnCheck.v:1756-1858) at
   the A' instance, through the kit's crs_spec.
   NAMED OPEN PREMISES, in order, each with its owner:
     HT_check_reject_clean, HT_fuzz_alloc_count, HT_fuzz_alloc_fail, HT_fuzz_alloc_live, HT_fuzz_alloc_ran_out,
       HT_fuzz_free, HT_fuzz_free_null, HT_pj_parse, HT_pj_write: the callee texts (lib/A/PRH_FnCheck.v,
       PRH_FnAlloc.v, PRH_FnPj.v, PRH_FnWriter.v) exactly, at every float state (pj_write at depth DOC_D; pj_parse at
       every cursor set CW, X1 takes it at its CrsSeg_X1.x_cw); owners: the callees' lanes;
     HX_asmr: YGcallMxmn.astack_malloc_realizes_xm at class 1, the frame-area row.
   GONE WITH THE CUT: the DW binder (the texts drop it), HP_sm (the keyed strtod model closes crs_sm_sp), HD_pjp_end
   and HD_pjp_frame (pj_parse's DW memberships are replaced by prh_cw_pj, met by CrsSeg_X1.x_cw_pj).
   GONE WITH THE GUARDED TEXT: the stand-in CrsPjpDeadAp.v and its Section hypothesis; X1 takes tpj_parse_specX itself.
   DISCHARGED INSIDE: crs_wexact by CrsBridgeAp.crs_wexact_of_text from HT_pj_write (cf_head = HEAD by computation,
   crs_Ap_HI_head); crs_free0 by CrsBridgeAp.crs_free0_of_text from HT_fuzz_free_null; the text's guarded conjunct's
   premises by CrsSeg_X1.crs_guard_x1; W1's and Z's class-24 bounds by crs_Ap_cnt24_W1 / _Z (PresetRoomCounts); the
   run's meter caps by HI_hull_Ap; every instance fact by the lemmas above. ---- *)
Theorem crs_holds_Ap : forall (CTX0 : list (list Z)),
  forall (HT_check_reject_clean : forall fx',
    tcheck_reject_clean_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK),
  forall (HT_fuzz_alloc_count : forall fx',
    PRH_FnAlloc.tfuzz_alloc_count_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK),
  forall (HT_fuzz_alloc_fail : forall fx',
    PRH_FnAlloc.tfuzz_alloc_fail_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK),
  forall (HT_fuzz_alloc_live : forall fx',
    PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK),
  forall (HT_fuzz_alloc_ran_out : forall fx',
    PRH_FnAlloc.tfuzz_alloc_ran_out_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK),
  forall (HT_fuzz_free : forall fx',
    PRH_FnAlloc.tfuzz_free_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK),
  forall (HT_fuzz_free_null : forall fx',
    PRH_FnAlloc.tfuzz_free_null_specX (fx := fx') (PI := prh_img_A) (PA := PA) TA ARA SK),
  forall (HT_pj_parse : forall (fx' : YK11.FPState) (CW : list (list Z)),
    PRH_FnPj.tpj_parse_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK CTX0 CW),
  forall (HT_pj_write : forall fx',
    PRH_FnWriter.tpj_write_specX (fx := fx') (PI := prh_img_A) (PA := PA) TA ARA SK CTX0 DOC_D),
  forall (HX_asmr : YGcallMxmn.astack_malloc_realizes_xm SEGS TA ARA 1),
  tcheck_reject_clean_starved_specX (fx := fx) (PI := prh_img_A) (RL := RL) (PA := PA) TA ARA SK CTX0.
Proof.
intros CTX0 HT_check_reject_clean HT_fuzz_alloc_count HT_fuzz_alloc_fail HT_fuzz_alloc_live
  HT_fuzz_alloc_ran_out HT_fuzz_free HT_fuzz_free_null HT_pj_parse HT_pj_write HX_asmr.
(* the two interims, from the texts (the kit's bridges) *)
pose proof (CrsBridgeAp.crs_free0_of_text TA ARA HT_fuzz_free_null) as HT_fuzz_free0.
pose proof (fun C Hp => CrsBridgeAp.crs_wexact_of_text TA ARA crs_Ap_HI_head CTX0 HT_pj_write C Hp) as HW_exact.
eapply crs_spec. intros C Hpre.
(* H1 at every frame position __asan_stack_malloc_1 may return: crs_with_fpos C p meets crs_pre as C does *)
assert (HH1 : forall p, crs_from_H1 (SK := SK) TA ARA CTX0 (crs_with_fpos C p)).
{ intros p. assert (Hp : crs_pre TA ARA CTX0 (crs_with_fpos C p)) by exact Hpre.
  exact (crs_Ap_from_H1 CTX0 (crs_with_fpos C p) HT_check_reject_clean HT_fuzz_alloc_count HT_fuzz_alloc_fail
    HT_fuzz_alloc_live HT_fuzz_alloc_ran_out HT_fuzz_free HT_fuzz_free0 HT_pj_parse (HW_exact _ Hp)
    (crs_Ap_HB_took _ _ Hp)). }
pose proof crs_Ap_laws as LAWS. pose proof crs_Ap_keep as HK. pose proof crs_Ap_HI_head8 as HI_head8.
pose proof crs_Ap_HX_ownlow as HX_ownlow. pose proof crs_Ap_HX_pal as HX_pal.
pose proof crs_Ap_HX_pal_uar_img as HX_pal_uar_img. pose proof crs_Ap_HX_pal_sm1 as HX_pal_sm1.
pose proof crs_Ap_HX_pal_pst_static as HX_pal_pst_static. pose proof (HT_fuzz_alloc_live fx) as HT_live_fx.
assert (KE : crs_from_E (SK := SK) TA ARA CTX0 C) by (eapply CrsSeg_E.crs_seg_E; eassumption).
exact (KE Hpre).
Qed.

(* ---- HX_asmr DISCHARGED (a Theorem Labs lane 14:30Z: a premise is not carried as unproved without asking its layer): the
   frame-area row at class 1 is lib/A/FCm01xm.v stack_malloc1_contract_xm (Qed, any ARx with fs_iface), lifted to
   ARcf /\ xs_placed_cf exactly as lib/A/FCxmCfx.v lifts class 3 (YGcallMxmn.astack_malloc_realizes_xm_conj; the
   set_fs law YGcallScf.xs_placed_cf_set_fs). pa_segs PI_prog_A is AB1v.tfibsegs by conversion (FCxmCfx.v header). ---- *)
Lemma crs_Ap_asmr : YGcallMxmn.astack_malloc_realizes_xm SEGS TA ARA 1.
Proof.
  unfold crs_ARx_Ap. change SEGS with AB1v.tfibsegs.
  exact (YGcallMxmn.astack_malloc_realizes_xm_conj AB1v.tfibsegs TA (YG0ncf.ARcf AB1v.tfibsegs TA)
    (fun ly S => YG0ncf.xs_placed_cf ly S) 1 YGcallScf.xs_placed_cf_set_fs
    (FCm01xm.stack_malloc1_contract_xm TA (YG0ncf.ARcf AB1v.tfibsegs TA)
      (FCifaceCf.fs_iface_ARcf AB1v.tfibsegs TA (YG0lawscf.AR_laws_ok_cf AB1v.tfibsegs TA)) (proj2 AD2l.TfibB_pair))).
Qed.

(* crs_holds_Ap with HX_asmr discharged: the same conclusion, one premise fewer *)
Definition crs_holds_Ap_closed := fun CTX0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
  crs_holds_Ap CTX0 h1 h2 h3 h4 h5 h6 h7 h8 h9 crs_Ap_asmr.

End top.

Print Assumptions crs_Ap_keep.
Print Assumptions crs_holds_Ap.
Print Assumptions crs_holds_Ap_closed.
(* the statement, elaborated: the class position of the text is the entry float state fx *)
Set Printing Implicit. Unset Printing Notations.
About crs_holds_Ap.
Check crs_holds_Ap_closed.
Print crs_ARx_Ap.
Set Printing Notations. Unset Printing Implicit.
