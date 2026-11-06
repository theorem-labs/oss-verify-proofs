(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v; 304 of its 337 lines of code are new or changed and 436 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the set-up piece of the
   checking segment M03 of LLVMFuzzerTestOneInput, lib/A/HPgSegM.v hq_piece_M3a_setup_stmt at image A's segments
   (hq_A_piece_M3a_setup): from X 0x82f30 (x into scope, memset(x, 0, 0x88), the null flag, is_props, params_struct
   and n_ent, then the pair loop's constants) to PAIR 0x8307c at index 0, RC 0x83694 or RCM 0x8369c. Proves no
   function (kind: segment lemma).

   HOW. The walk is lib/A/HPgM3aSetupBlk.v su_blk, applied at the run's own float state fx2 with the values X's cut
   names: s1 = R, s3 = (F >> 3) + K, s5 = pp + 0x4000, s7 = K, s10 = F + 0x180, the cells R + 0x40 (null), + 0x60
   (F), + 0x90 ((pp + n_ent's offset) >> 3), + 0xa0, + 0xf0 (pp), and the record's three fields from Layout.pp_bytes
   (HPgMem hm_pp_is_props / hm_pp_params_struct / hm_pp_n_ent). su_carry rebuilds each exit's hq_base3 from X's:
   every byte the walk writes (x, x's shadow granules 52 .. 68, the real-frame cells [R + 0xa8, R + 0x110)) lies in
   M03's write set hq_E3 and the memset's stack in the callees' window; the four blocks, res and the image are apart
   from them; the frame's shadow becomes hq_shX (HPgMem.hm_fsh_set); the errno cell still reads as some value
   (every byte present stays present). The answers: RCM when the null flag is 1 or the record is not a Props object
   (expect_model gives (-1, [], (0, 0, NONE))), RC when params_struct is 0 or there is no pod ((0, [], ..)); PAIR at
   0 with x all zero (hq_x_open [] 0 0) and the fold invariant at 0 as expect_model's own fold over pod_next_pair's
   pairs. The two float registers the walk writes (f9, f18) are in hq_fxk's list.

   SECTION HYPOTHESIS. AMEMSET: the kernel's __asan_memset contract (YG0d.aintrin_realizes) at image A's literal
   entry 0x521a8, for any float state; the harness composition supplies it at that literal from the start-up layer's
   proof of the runtime function. Nothing else is assumed. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM HPgMem HPgSteps HPgIntrin HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3aSetupBlk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* x's seventeen granules opened over the pattern at C6 *)
Lemma su_shX : hq_shX = hm_setn headamp_A_shB 52 17 0.
Proof. vm_compute. reflexivity. Qed.

(* the three parts of ha_result's answer are the fold's *)
Lemma su_res_parts : forall o : list Headamp.cell * Z * Z,
(ans_cells (Headamp.ha_result o), ans_keys (Headamp.ha_result o), ans_rf (Headamp.ha_result o)) = o.
Proof. intros [[c k] f]. reflexivity. Qed.

Section h. Context {fx : YK11.FPState}.
(* a register and a real-frame cell of a cut list *)
Lemma su_at_reg : forall H mem regs e L r v, Forall (fun f => hd_at rsegs H mem regs e (fst f) (snd f)) L ->
In (LReg r, v) L -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
Lemma su_at_cell : forall H mem regs e L o v, Forall (fun f => hd_at rsegs H mem regs e (fst f) (snd f)) L ->
In (LCell XR o, v) L -> val_mem rsegs (mrestrict H mem) (e_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HL Hin. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
(* a byte the reader gives is below 256 *)
Lemma su_aview_rng : forall H m x b, aview rsegs H m x = Some b -> 0 <= b < 256.
Proof.
intros H m x b Hv. unfold aview in Hv. destruct (mbyte rsegs (mrestrict H m) x) as [y|]; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range _ y) as Hr.
change (bv_modulus 8) with 256 in Hr. lia.
Qed.
(* bytes kept byte by byte *)
Lemma su_garr_kept : forall H (m m' : word -> option byte) a l,
garr8 rsegs (mrestrict H m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview rsegs H m' x = aview rsegs H m x) ->
garr8 rsegs (mrestrict H m') a l.
Proof.
intros H m m' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept rsegs H H m m' _ 1 _); [|exact Hv]. intros k Hk'. apply Hk. lia.
Qed.
End h.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* what a cut of the set-up carries over from X: the segment's journal and write set, the frame's shadow with x in
   scope, the read-only image, the four blocks' bytes, res and the errno cell *)
Lemma su_carry : forall (cx : hs_scx rsegs) r ev (fx2 fx3 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r (hi_shB headamp_himg_A) ly2 S2 W2 regs2 mem2 md2 ->
@hq_fxk fx fx3 ->
su_post B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2
  mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)) regs3 mem3 md3 ->
@hq_base3 fx rc SK rsegs B MT cx fx3 r hq_shX ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx r ev fx2 fx3 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb Hfx3 Hpost.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS. pose proof img_segs_low as Hsegs.
destruct Hb as (Hcore & _ & Hfsh & Hrom & Hpp & Hpod & Hout & Hres & Hev).
destruct Hcore as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
destruct Hpost as (HJ3 & Hio3 & Rk3 & R18 & Hx0 & Hsh0 & VF3 & K3 & Hgr3).
destruct HS as (Hpre & _ & Hwf & Hlen & _ & _ & Hpodf & _ & _ & _ & _ & Hfo & _ & _ & _ & _ & _).
destruct Hpre as (HJc & _ & H2c & H3c & H4c & HeS & HR32 & HRsz & HRstk & Hown & HeF & _ & Hcap & Hnull & _ & _ & _ & _ & _ & _ & _ & Hppf).
cbn [hi_cid hi_rsz headamp_himg_A] in Hown, HeF, HRsz.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
assert (Hfin : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
assert (Hfa : frame_addr ly2 4 (x_pos cx) = e_F (x_e cx)) by (rewrite HeF; eapply headamp_A_site_frame_at; [exact HJc | exact HJ]).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HAR Hfin) as (HF4096 & HFc & HFapp).
rewrite Hfa in HF4096, HFc, HFapp. change (fs_frame_bytes 4) with 1024 in HFc, HFapp.
pose proof (ASAN_CEIL_range) as Hceil. unfold ASAN_CEIL in Hceil, HFapp.
unfold T_SEG_STK, ASTACK in HRstk.
set (e := x_e cx) in *. set (F := e_F e) in *. set (R := e_R e) in *.
assert (HspR : spZ (x_regs cx) = R) by (unfold spZ; rewrite H2c; unfold w64; apply unsigned_lit_small; lia).
(* M03's write set holds every byte the set-up writes, but the callees' stack *)
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_SEG_STK <= a < R) -> ~ hq_E3 rsegs B cx a ->
  aview rsegs (w_H W2) mem3 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha Hs Hn. unfold hq_E3, hd_inw in Hn. fold e in Hn. cbn [hi_w3 headamp_himg_A] in Hn.
  unfold T_SEG_STK, ASTACK in Hs.
  rewrite K3; [ apply Hkeep; [exact Ha | rewrite HspR; unfold T_SEG_STK, ASTACK; exact Hs | exact Hn]
  | exact Ha | unfold ESTACK; lia
  | intros Hx; apply Hn; left; apply Exists_cons_hd; cbn [hd_xv fst snd]; fold F; lia
  | intros Hx; apply Hn; left; apply Exists_cons_tl, Exists_cons_hd; cbn [hd_xv fst snd]; fold F; lia
  | intros Hx; apply Hn; left; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; cbn [hd_xv fst snd]; fold R; lia ]. }
(* the four blocks lie apart from x, its shadow, the callees' stack and the real frame *)
assert (KBlk : forall p m x, In (p, m) (ablocks B ly2 S2) -> p <= x < p + req_size m ->
  aview rsegs (w_H W2) mem3 x = aview rsegs (w_H W2) mem2 x).
{ intros p m x Hin Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
  pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hfin) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Hfa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, HFapp.
  apply K3; unfold shadow_addr, SHADOW_OFF, ESTACK; lia. }
assert (Hwfe := Model.ents_wf r Hwf). destruct Hwfe as (Hn32 & Hents).
pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hbuf).
assert (Hs96 : Forall (fun en => (length (Model.e_body en) <= 96)%nat) (Model.ents r)).
{ eapply Forall_impl; [|exact Hents]. intros en (_ & Hl & Hz). lia. }
unfold hq_base3.
split; [|split; [exact Hfx3|]].
{ unfold hs_core, hs_mid. split; [exact HJ3|].
  split; [intros r0 Hr0; rewrite (Rk3 r0) by (cbn [In]; lia); exact (H234 r0 Hr0)|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
  split; [exact Hmo|].
  intros a Ha Hs Hn. rewrite HspR in Hs. exact (KK a Ha Hs Hn). }
split.
{ unfold hs_fsh_at. fold e F. rewrite su_shX.
  cbn [hi_shB headamp_himg_A] in Hfsh. unfold hs_fsh_at in Hfsh. fold e F in Hfsh.
  apply (hm_fsh_set rsegs (w_H W2) mem2 (w_H W2) mem3 F headamp_A_shB 52 17 0 Hfsh).
  - intros i Hi. apply Hsh0. cbn in Hi. lia.
  - intros i Hi Hn. change (length headamp_A_shB) with 80%nat in Hi. cbn in Hi, Hn.
    unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
    apply K3; unfold shadow_addr, SHADOW_OFF, ESTACK; lia. }
split.
{ apply (hm_rom_kept_wr rsegs (fun a => ~ (0 <= a < 2 ^ 64) \/ (R - ESTACK <= a < R) \/ (F + 0x1a0 <= a < F + 0x228) \/
    (shadow_addr F + 52 <= a < shadow_addr F + 69) \/ (R + 0xa8 <= a < R + 0x110)) W2 W2 mem2 mem3 Hrom).
  - intros a Hn. destruct (Z_lt_le_dec a 0); [exfalso; apply Hn; left; lia|].
    destruct (Z_lt_le_dec a (2 ^ 64)); [|exfalso; apply Hn; left; lia].
    apply K3; [lia | intros H'; apply Hn; right; left; exact H' | intros H'; apply Hn; right; right; left; exact H'
              | intros H'; apply Hn; right; right; right; left; exact H' | intros H'; apply Hn; right; right; right; right; exact H'].
  - intros a (sg & Hsg & _ & Hrg) Hw.
    assert (Hia : in_img rsegs a) by (exists sg; split; [exact Hsg | exact Hrg]).
    pose proof (Hsegs a Hia) as Hl. unfold kLowMemEnd in Hl.
    destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; [lia | unfold ESTACK in Hw; lia | | unfold shadow_addr, SHADOW_OFF in Hw; lia | lia].
    refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _) Hia). right. left. exists 4, (x_pos cx).
    split; [exact Hfin|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes 4) with 1024. fold e F. lia. }
assert (HppB : In (e_pp e, 19744) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact (proj1 (proj2 Hppf))).
assert (HpodB : In (e_pod e, e_len e) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact (proj1 (proj2 Hpodf))).
assert (HoutB : In (e_out e, 3 * (e_cap e + 1)) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact (proj1 (proj2 Hfo))).
split.
{ unfold hs_pp_at in Hpp |- *. fold e in Hpp |- *. apply (su_garr_kept _ mem2 mem3 _ _ Hpp).
  intros x Hx. apply (KBlk _ 19744 x HppB). change (req_size 19744) with 19744.
  unfold hd_zbytes in Hx. rewrite length_map in Hx. unfold Layout.pp_bytes in Hx.
  rewrite (hm_pp_len_img (Model.buf r) (Model.is_props r) (Model.has_params r) (Model.params_struct r) (Model.ents r) (Model.corrupt r)
    ltac:(unfold Layout.POD_BUF_MAX; lia) Hn32 Hs96) in Hx. unfold Layout.PP_SIZE in Hx. lia. }
split.
{ fold e in Hpod |- *. apply (su_garr_kept _ mem2 mem3 _ _ Hpod).
  intros x Hx. apply (KBlk _ (e_len e) x HpodB).
  unfold hd_zbytes in Hx. rewrite length_map, <- Hlen in Hx.
  unfold req_size. destruct (Z.eqb_spec (e_len e) 0); lia. }
split.
{ fold e in Hout |- *. apply (su_garr_kept _ mem2 mem3 _ _ Hout).
  intros x Hx. apply (KBlk _ (3 * (e_cap e + 1)) x HoutB).
  unfold hd_zbytes in Hx. rewrite length_map, length_ha_cells_bytes in Hx.
  pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
  apply answer_ok_parts in Hok as (Hcase & _). unfold hq_ans in Hx. fold e in Hx.
  assert (Hlc : Z.of_nat (length (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)))) <= e_cap e)
    by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
  unfold req_size. destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia. }
split.
{ fold e F in Hres |- *. apply (su_garr_kept _ mem2 mem3 _ _ Hres).
  intros x Hx. unfold hd_zbytes, ans_res_bytes in Hx. rewrite length_map, length_ha_res_bytes in Hx.
  unfold HQ_RES in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
  apply K3; unfold shadow_addr, SHADOW_OFF, ESTACK; lia. }
destruct Hev as (ev0 & Hev0).
apply (su_rd32_grows _ _ _ ev0 Hev0).
- intros x Hx. exact (su_aview_grows (w_H W2) mem2 mem3 x Hgr3 Hx).
- intros x b Hb. exact (su_aview_rng _ _ _ _ Hb).
Qed.

Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet A_ASAN_MEMSET.

Ltac su_in := cbn [In app hq_L_seg hq_L_frame hq_L_loopc hq_L_loopr]; repeat (first [left; reflexivity | right]).

Theorem hq_A_piece_M3a_setup : @hq_piece_M3a_setup_stmt fx rc SK rsegs B MT.
Proof using AMEMSET.
unfold hq_piece_M3a_setup_stmt. intros cx POST r ev HS HPAIR HRC HRCM.
unfold hq_from_X. intros fx2 ly2 S2 W2 regs2 mem2 md2 HX.
destruct HX as (Hb & Hat & Hcorr).
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof Hb as (Hcore & Hfxk & _ & _ & Hpp & _).
pose proof Hcore as (HJ & H234 & _ & Hperm & _).
pose proof HS as (Hpre & _ & Hwf & _).
destruct Hpre as (HJc & _ & H2c & H3c & H4c & HeS & HR32 & HRsz & HRstk & Hown & HeF & _ & Hcap & Hnull & _ & _ & _ & _ & _ & _ & _ & Hppf).
cbn [hi_cid hi_rsz headamp_himg_A] in Hown, HeF, HRsz.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
assert (Hfin : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
assert (Hfa : frame_addr ly2 4 (x_pos cx) = e_F (x_e cx)) by (rewrite HeF; eapply headamp_A_site_frame_at; [exact HJc | exact HJ]).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HAR Hfin) as (HF4096 & HFc & HFapp).
rewrite Hfa in HF4096, HFc, HFapp. change (fs_frame_bytes 4) with 1024 in HFc, HFapp.
pose proof (ASAN_CEIL_range) as Hceil. unfold ASAN_CEIL in Hceil, HFapp.
unfold T_SEG_STK, ASTACK in HRstk.
assert (HPP : In (e_pp (x_e cx), 19744) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact (proj1 (proj2 Hppf))).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HPP) as (_ & Hp4096 & Hpc & _).
change (req_size 19744) with 19744 in Hpc.
assert (Hwfe := Model.ents_wf r Hwf). destruct Hwfe as (Hn32 & Hents).
pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hbuf).
assert (Hs96 : Forall (fun en => (length (Model.e_body en) <= 96)%nat) (Model.ents r)).
{ eapply Forall_impl; [|exact Hents]. intros en (_ & Hl & Hz). lia. }
assert (HbL : Z.of_nat (length (Model.buf r)) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
unfold hs_at_cx, hs_at in Hat.
set (e := x_e cx) in *. set (F := e_F e) in *. set (R := e_R e) in *. set (pp := e_pp e) in *.
(* the registers and the cells at X *)
assert (H2 : getr regs2 (Z_to_bv 5 2) = w64 R)
  by (rewrite (H234 2 ltac:(lia)), (su_getr_z (x_regs cx) 2 2 eq_refl); exact H2c).
assert (H3 : getr regs2 (Z_to_bv 5 3) = w64 (as_gp B))
  by (rewrite (H234 3 ltac:(lia)), (su_getr_z (x_regs cx) 3 3 eq_refl); exact H3c).
assert (H4 : getr regs2 (Z_to_bv 5 4) = w64 (as_tp B))
  by (rewrite (H234 4 ltac:(lia)), (su_getr_z (x_regs cx) 4 4 eq_refl); exact H4c).
pose proof (su_at_reg _ _ _ _ _ 9 _ Hat ltac:(su_in)) as H9.
pose proof (su_at_reg _ _ _ _ _ 19 _ Hat ltac:(su_in)) as H19.
pose proof (su_at_reg _ _ _ _ _ 21 _ Hat ltac:(su_in)) as H21.
pose proof (su_at_reg _ _ _ _ _ 23 _ Hat ltac:(su_in)) as H23.
pose proof (su_at_reg _ _ _ _ _ 26 _ Hat ltac:(su_in)) as H26.
pose proof (su_at_cell _ _ _ _ _ 0x40 _ Hat ltac:(su_in)) as V40.
pose proof (su_at_cell _ _ _ _ _ 0x60 _ Hat ltac:(su_in)) as V60.
pose proof (su_at_cell _ _ _ _ _ 0x90 _ Hat ltac:(su_in)) as V90.
pose proof (su_at_cell _ _ _ _ _ 0xa0 _ Hat ltac:(su_in)) as VA0.
pose proof (su_at_cell _ _ _ _ _ 0xf0 _ Hat ltac:(su_in)) as VF0.
fold R in V40, V60, V90, VA0, VF0.
unfold Layout.OFF_N_ENT in V90, VA0.
assert (Hsh : 0 <= Z.shiftr (pp + 19732) 3 < 2 ^ 64) by (rewrite Z.shiftr_div_pow2 by lia; lia).
rewrite (Z.mod_small (e_null e)) in V40 by lia. rewrite (Z.mod_small F) in V60 by lia.
rewrite (Z.mod_small (Z.shiftr (pp + 19732) 3)) in V90 by exact Hsh.
rewrite (Z.mod_small (pp + 19732)) in VA0 by lia. rewrite (Z.mod_small pp) in VF0 by lia.
pose proof (hm_pp_is_props rsegs (Model.buf r) (Model.is_props r) (Model.has_params r) (Model.params_struct r)
  (Model.ents r) (Model.corrupt r) HbL Hn32 Hs96 (w_H W2) mem2 pp Hpp) as Vip.
pose proof (hm_pp_params_struct rsegs (Model.buf r) (Model.is_props r) (Model.has_params r) (Model.params_struct r)
  (Model.ents r) (Model.corrupt r) HbL Hn32 Hs96 (w_H W2) mem2 pp Hpp) as Vps.
pose proof (hm_pp_n_ent rsegs (Model.buf r) (Model.is_props r) (Model.has_params r) (Model.params_struct r)
  (Model.ents r) (Model.corrupt r) HbL Hn32 Hs96 (w_H W2) mem2 pp Hpp) as Vn.
unfold HQ_RES in H26.
apply (@su_blk fx2 rc SK B AMEMSET (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 R F pp (x_pos cx) (e_null e) (Z.of_nat (length (Model.ents r)))
  (Model.is_props r) (Model.params_struct r) POST HJ Hown Hfa HPP H2 H3 H4 H9 H19 H21 H23 H26 HR32
  ltac:(rewrite <- HeS; exact HRsz) ltac:(unfold ASTACK; lia) V40 ltac:(lia) V60 V90 VA0 VF0 Vip Vps Vn ltac:(lia)).
- (* RCM 0x8369c: the null flag or not a Props object *)
  intros regs3 mem3 md3 Hpost H11 Hc.
  pose proof (su_carry cx r ev fx2 fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb Hfxk Hpost) as Hb3.
  destruct Hpost as (_ & _ & Rk3 & R18 & Hx0 & _ & VF3 & K3 & _).
  assert (Hexp : hq_exp rsegs cx r = (-1, [], (0, 0, Headamp.REFUSE_NONE))).
  { unfold hq_exp, Headamp.expect_model. fold e.
    destruct Hc as [H1 | H1]; rewrite H1; [reflexivity | rewrite orb_true_r; reflexivity]. }
  apply (HRCM fx2 ly2 S2 W2 regs3 mem3 md3).
  split; [exact Hb3|].
  split; [|split; [exact Hcorr|]].
  + unfold hs_at_cx, hs_at. cbn [hq_L_seg hq_L_frame app].
    repeat apply Forall_cons; [..| apply Forall_nil]; cbv beta; cbn [fst snd hd_at hd_xv];
    change (x_e cx) with e; change (e_R e) with R; change (e_F e) with F; change (e_pp e) with pp;
    first
    [ rewrite Rk3 by (cbn [In]; lia); eapply (su_at_reg _ _ _ _ _ _ _ Hat); su_in
    | rewrite Hexp; exact H11
    | unfold HQ_XO; exact R18
    | rewrite (Z.mod_small pp) by lia; exact VF3
    | apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem3 _ 8 _);
      [ intros j Hj; unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; apply K3; unfold shadow_addr, SHADOW_OFF, ESTACK; lia
      | eapply (su_at_cell _ _ _ _ _ _ _ Hat); su_in ] ].
  + rewrite Hexp. cbn [ans_cells ans_keys ans_rf fst snd]. unfold Headamp.REFUSE_NONE.
    unfold hq_x_at. fold e F.
    split; [|split; [unfold X_CELLS; cbn; lia | split; [cbn; lia | split; [cbn; lia | split; [lia | left; reflexivity]]]]].
    replace (hd_zbytes (hq_x_open [] 0 0)) with (repeat 0 136) by (vm_compute; reflexivity).
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. unfold HQ_XO. apply hm_aview_val1. apply Hx0. lia.
- (* RC 0x83694: params_struct = 0 or no pod *)
  intros regs3 mem3 md3 Hpost H108 Hn0 Hip Hps.
  pose proof (su_carry cx r ev fx2 fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb Hfxk Hpost) as Hb3.
  destruct Hpost as (_ & _ & Rk3 & R18 & Hx0 & _ & VF3 & K3 & _).
  assert (Hexp : hq_exp rsegs cx r = (0, [], (0, 0, Headamp.REFUSE_NONE))).
  { unfold hq_exp, Headamp.expect_model. fold e. rewrite Hn0, Hip. cbn [Z.eqb orb negb].
    destruct Hps as [Hps | Hz]; [rewrite Hps; reflexivity|].
    destruct (Model.params_struct r); [|reflexivity].
    destruct (Model.ents r) as [|en es]; [reflexivity | cbn [length] in Hz; lia]. }
  apply (HRC fx2 ly2 S2 W2 regs3 mem3 md3).
  split; [exact Hb3|].
  split; [|split; [exact Hcorr | split; [rewrite Hexp; reflexivity|]]].
  + unfold hs_at_cx, hs_at. cbn [hq_L_seg hq_L_frame app].
    repeat apply Forall_cons; [..| apply Forall_nil]; cbv beta; cbn [fst snd hd_at hd_xv];
    change (x_e cx) with e; change (e_R e) with R; change (e_F e) with F; change (e_pp e) with pp;
    first
    [ rewrite Rk3 by (cbn [In]; lia); eapply (su_at_reg _ _ _ _ _ _ _ Hat); su_in
    | rewrite (Z.mod_small pp) by lia; exact VF3
    | unfold HQ_XO; rewrite Z.mod_small by lia; exact H108
    | apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem3 _ 8 _);
      [ intros j Hj; unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; apply K3; unfold shadow_addr, SHADOW_OFF, ESTACK; lia
      | eapply (su_at_cell _ _ _ _ _ _ _ Hat); su_in ] ].
  + rewrite Hexp. cbn [ans_cells ans_keys ans_rf fst snd]. unfold Headamp.REFUSE_NONE.
    unfold hq_x_at. fold e F.
    split; [|split; [unfold X_CELLS; cbn; lia | split; [cbn; lia | split; [cbn; lia | split; [lia | left; reflexivity]]]]].
    replace (hd_zbytes (hq_x_open [] 0 0)) with (repeat 0 136) by (vm_compute; reflexivity).
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. unfold HQ_XO. apply hm_aview_val1. apply Hx0. lia.
- (* PAIR 0x8307c at i = 0, at the float state the two `fmv.w.x` leave *)
  intros regs3 mem3 md3 Hpost HPr Hn0 Hip Hps Hnpos.
  assert (Hfx3 : @hq_fxk fx (su_fx fx2)).
  { destruct Hfxk as [Hk Hcs]. split; [|exact Hcs].
    intros k Hk'. unfold su_fx, su_fset. cbn [fp_regs]. unfold Sem.reg_get in Hk |- *.
    rewrite !bvmap_get_set_other; [exact (Hk k Hk') | |];
    intros Heq; apply Hk'; rewrite <- Heq; vm_compute; tauto. }
  pose proof (su_carry cx r ev fx2 (su_fx fx2) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb Hfx3 Hpost) as Hb3.
  destruct Hpost as (_ & _ & Rk3 & R18 & Hx0 & _ & VF3 & K3 & _).
  destruct HPr as (P1 & P31 & P29 & P30 & P17 & P21 & P7 & P28 & Ca8 & Cb0 & Cb8 & Cc0 & Ce8 & Cf8 & C100 & C108).
  apply (HPAIR (su_fx fx2) ly2 S2 W2 regs3 mem3 md3 [] 0 0).
  split; [exact Hb3|].
  split.
  { unfold hs_at_cx, hs_at. cbn [hq_L_seg hq_L_frame hq_L_loopc hq_L_loopr app].
    repeat apply Forall_cons; [..| apply Forall_nil]; cbv beta; cbn [fst snd hd_at hd_xv];
    change (x_e cx) with e; change (e_R e) with R; change (e_F e) with F; change (e_pp e) with pp;
    first
    [ rewrite Rk3 by (cbn [In]; lia); eapply (su_at_reg _ _ _ _ _ _ _ Hat); su_in
    | rewrite (Z.mod_small pp) by lia; exact VF3
    | unfold hq_nent; first [exact P7 | exact P28]
    | exact P1 | exact P31 | exact P29 | exact P30 | exact P17 | exact P21
    | unfold HQ_MHALF_HI, HQ_HALF_HI, HQ_XO, HQ_X_CELL0, HQ_RC_BIG, HQ_ENT_SZ, HQ_ENT_BODY; rewrite Z.mod_small by lia;
      first [exact Ca8 | exact Cb0 | exact Cb8 | exact Cc0 | exact Ce8 | exact Cf8 | exact C100 | exact C108]
    | apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem3 _ 8 _);
      [ intros j Hj; unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; apply K3; unfold shadow_addr, SHADOW_OFF, ESTACK; lia
      | eapply (su_at_cell _ _ _ _ _ _ _ Hat); su_in ] ]. }
  split.
  { unfold hq_fs, su_fx, su_fset. cbn [fp_regs]. unfold Sem.reg_get.
    rewrite bvmap_get_set_other, bvmap_get_set_same; [reflexivity|].
    intros Heq. apply (f_equal (@bv_unsigned 5)) in Heq. vm_compute in Heq. discriminate Heq. }
  split.
  { unfold hq_fs, su_fx, su_fset. cbn [fp_regs]. unfold Sem.reg_get.
    rewrite bvmap_get_set_same. reflexivity. }
  split.
  { unfold hq_live. fold e. split; [exact Hn0|]. split; [exact Hcorr|]. split; [exact Hip | exact Hps]. }
  split; [unfold hq_nent; exact Hnpos|].
  split; [lia|].
  split.
  { unfold hq_x_at. fold e F.
    split; [|split; [unfold X_CELLS; cbn; lia | split; [cbn; lia | split; [cbn; lia | split; [lia | left; reflexivity]]]]].
    replace (hd_zbytes (hq_x_open [] 0 0)) with (repeat 0 136) by (vm_compute; reflexivity).
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. unfold HQ_XO. apply hm_aview_val1. apply Hx0. lia. }
  unfold hq_fold_inv, hq_fin, hq_exp, Headamp.expect_model. fold e. rewrite Hn0, Hip, Hps. cbn [Z.eqb orb negb skipn].
  rewrite su_res_parts. reflexivity.
Qed.
End a.

Print Assumptions hq_A_piece_M3a_setup.
