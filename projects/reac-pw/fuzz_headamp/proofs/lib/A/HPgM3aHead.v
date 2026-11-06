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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module names changed; 197 of its 230 lines of code are new or changed and 436 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the head of the checking
   segment M03 of LLVMFuzzerTestOneInput, lib/A/HPgSegM.v hq_piece_M3a_head_stmt (from C5 0x82e98 to X 0x82f30 when
   pp->corrupt is 0 and to FIRST 0x83724 when it is 1). The walk is lib/A/HPgM3aHeadB.v's seven blocks (the null
   test, memset(out, 0xa5), res into scope and memset(res, 0x5a), the parse, check_no_overrun, check_count,
   check_cells_valid and the corrupt test); this file takes their last state apart into the two cut states
   HPgSegM.hq_cut_X and hq_cut_FIRST. Section hypotheses: AMEMSET (the runtime's __asan_memset at image A's entry,
   at any float state), ERRNO (YCbq.v api_env: the errno cell lies in the image), ERRNO_RW (it lies in no read-only
   segment), MTL (the meter's laws), PARSE (HPgCSpec.v hd_parse_result_specX at image A's entry and literals, read-only
   range 0 .. 0), CK_NO / CK_COUNT / CK_CV (HPgCSpec.v's three check texts at their entries, at any float state).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgSteps HPgCalls HPgIntrin HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3aHeadB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* lia over the arithmetic part of the context only, with the local definitions made opaque (lia would unfold
   them in the goal alone) *)
Ltac mh_arith T := lazymatch T with
  | _ /\ _ => idtac | _ \/ _ => idtac | ~ _ => idtac | @eq Z _ _ => idtac | @eq nat _ _ => idtac
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | lt _ _ => idtac | le _ _ => idtac end.
Ltac mlia :=
  repeat (match goal with x := _ : Z |- _ => clearbody x end);
  repeat (match goal with H : ?T |- _ =>
    lazymatch type of T with Prop => tryif mh_arith T then fail else clear H end end);
  lia.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section s.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet A_ASAN_MEMSET.
Hypothesis ERRNO : api_env rsegs B.
Hypothesis ERRNO_RW : forall a, as_errno B <= a < as_errno B + 4 -> ~ in_rom rsegs a.
Hypothesis MTL : ameter_laws MT.
Hypothesis PARSE : hd_parse_result_specX rsegs B MT A_PARSE_RESULT 0 0
  (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A).
Hypothesis CK_NO : forall fx' : YK11.FPState, hd_check_no_overrun_specX (fx := fx') rsegs B MT A_CK_NO_OVERRUN.
Hypothesis CK_COUNT : forall fx' : YK11.FPState, hd_check_count_specX (fx := fx') rsegs B MT A_CK_COUNT.
Hypothesis CK_CV : forall fx' : YK11.FPState, hd_check_cells_valid_specX (fx := fx') rsegs B MT A_CK_CELLS_VALID.

(* ============ the walk's last state, taken apart into what both cut states carry ============ *)
Lemma mh_last : forall cx r ev (fx2 : YK11.FPState) ly2 S2 W2 regs mem md,
mh_f (fx := fx) B cx r ev -> mh_P (fx := fx) B MT cx r fx2 ly2 S2 W2 regs mem md ->
getr regs (Z_to_bv 5 27) = w64 (ans_rc (mh_ans cx r)) ->
hq_base3 (fx := fx) rsegs B MT cx fx2 r (hi_shB headamp_himg_A) ly2 S2 W2 regs mem md /\
(forall l v, In (l, v) (hq_L_seg rsegs cx ++
   [(LReg 21, e_pp (x_e cx) + 0x4000);
    (LCell XR 0x20, e_F (x_e cx)); (LCell XR 0x40, e_null (x_e cx)); (LCell XR 0x60, e_F (x_e cx));
    (LCell XR 0x90, Z.shiftr (e_pp (x_e cx) + Layout.OFF_N_ENT) 3);
    (LCell XR 0xa0, e_pp (x_e cx) + Layout.OFF_N_ENT); (LCell XR 0xf0, e_pp (x_e cx));
    (LCell XR 0x110, hd_xv (x_e cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e cx) + 3)]) ->
 hd_at rsegs (w_H W2) mem regs (x_e cx) l v).
Proof using ERRNO ERRNO_RW.
intros cx r ev fx2 ly2 S2 W2 regs mem md HC HP H27.
pose proof (mh_bounds B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
unfold MHCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
destruct HP as (Hfx & HJ & Hfr & Hperm & Hio & Hmo & Rk & R24 & R26 & H110 & H118 & Hfsh & Hcells & Hguard & Hres & Hev
  & KP).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (f_J _ _ _ _ HC) as HJ0. pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs & _).
destruct (f_outf _ _ _ _ HC) as (_ & Hoin & _).
destruct (f_ppf _ _ _ _ HC) as (_ & Hppin & _).
destruct (f_podf _ _ _ _ HC) as (_ & Hpdin & _).
pose proof (f_dj _ _ _ _ HC) as Hdj.
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (f_own _ _ _ _ HC)).
assert (Hel : as_errno B + 4 <= kLowMemEnd) by (destruct ERRNO as ((_ & Hl) & _); exact Hl).
assert (Hel0 : 0 <= as_errno B) by (destruct ERRNO as ((Hl & _) & _); exact Hl).
pose proof (f_cap _ _ _ _ HC) as Hcap. pose proof (f_wf _ _ _ _ HC) as Hwf. pose proof (f_len _ _ _ _ HC) as Hlen.
assert (HFe : e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx)) by exact (f_F _ _ _ _ HC).
set (pp := e_pp (x_e cx)) in *. set (pod := e_pod (x_e cx)) in *. set (len := e_len (x_e cx)) in *.
set (out := e_out (x_e cx)) in *. set (cap := e_cap (x_e cx)) in *.
set (R := e_R (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
assert (F8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 8 ltac:(mlia)) as D.
  assert (F mod 8 = 0) by (rewrite <- (Z.mod_mod_divide F 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  mlia. }
(* a client byte (block or frame) is not in the image, so not the errno cell *)
assert (Hcerr : forall a p n, In (p, n) (ablocks B (x_lyc cx) (x_Sc cx)) -> p <= a < p + req_size n ->
  ~ (as_errno B <= a < as_errno B + 4)).
{ intros a p n Hin Ha He. destruct ERRNO as (_ & HAi & _).
  assert (Hcin : exists p0 n0, In (p0, n0) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p0 <= a < p0 + req_size n0)
    by (exists p, n; split; [exact Hin | exact Ha]).
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR0 (or_introl Hcin)) as (_ & Hni).
  exact (Hni (HAi a He)). }
assert (Hrqo : req_size (3 * (cap + 1)) = 3 * (cap + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (cap + 1)) 0); mlia).
assert (Hrqp : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); mlia).
assert (Hpo : pp + 19744 <= out \/ out + 3 * (cap + 1) <= pp).
{ assert (Hne : (pp, Layout.PP_SIZE) <> (out, 3 * (cap + 1)))
    by (intros Heq; injection Heq as _ Hl; unfold Layout.PP_SIZE in Hl; mlia).
  pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hppin Hoin Hne) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hrqo in Hz.
  change (req_size Layout.PP_SIZE) with 19744 in Hz. exact Hz. }
assert (Hpf : pp + 19744 <= F \/ F + 1024 <= pp).
{ pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hppin Hfin) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HFe in Hz.
  change (req_size Layout.PP_SIZE) with 19744 in Hz. change (fs_frame_bytes 4) with 1024 in Hz. exact Hz. }
assert (Hqf : pod + len <= F \/ F + 1024 <= pod).
{ pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR0 Hpdin Hfin) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HFe, Hrqp in Hz.
  change (fs_frame_bytes 4) with 1024 in Hz. exact Hz. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Oapp, Qapp, Papp, Fapp.
unfold kLowMemEnd in Hel.
(* the out block and the frame for locals lie outside the image *)
assert (Hoimg : forall a, out <= a < out + 3 * (cap + 1) -> ~ in_img rsegs a).
{ intros a Ha.
  assert (Hcin : exists p0 n0, In (p0, n0) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p0 <= a < p0 + req_size n0)
    by (exists out, (3 * (cap + 1)); rewrite Hrqo; split; [exact Hoin | exact Ha]).
  exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR0 (or_introl Hcin))). }
assert (Hfimg : forall a, F <= a < F + 1024 -> ~ in_img rsegs a).
{ intros a Ha.
  assert (Hcin : exists cid pos0, In (cid, pos0) (frames (x_Sc cx)) /\
    frame_addr (x_lyc cx) cid pos0 <= a < frame_addr (x_lyc cx) cid pos0 + fs_frame_bytes cid)
    by (exists 4, (x_pos cx); rewrite <- HFe; change (fs_frame_bytes 4) with 1024; split; [exact Hfin | exact Ha]).
  exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR0 (or_intror (or_introl Hcin)))). }
(* every byte of these ranges lies outside the callees' stack and outside what the head writes *)
assert (KK : forall a, 0 <= a < R - 16384 -> ~ (out <= a < out + 3 * (cap + 1)) ->
  ~ (shadow_addr F + 0x30 <= a < shadow_addr F + 0x32) -> ~ (F + 0x180 <= a < F + 0x18c) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview rsegs (w_H W2) mem a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha H1 H2 H3 H4. apply KP; [mlia | unfold T_SEG_STK, ASTACK; fold R; mlia |].
  intros [Hw|[Hw|[Hw|[Hw|Hw]]]]; [exact (H1 Hw) | fold R in Hw; mlia | exact (H2 Hw) | exact (H3 Hw) | exact (H4 Hw)]. }
assert (KC8 : forall o v, 0 <= o -> o + 8 <= 0x110 ->
  val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (R + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W2) mem) (R + o) 8 v).
{ intros o v Ho Ho8 Hv. eapply hd_val_mem_kept; [|exact Hv]. intros i Hi.
  apply KP; [mlia | unfold T_SEG_STK, ASTACK; fold R; mlia |].
  intros [Hw|[Hw|[Hw|[Hw|Hw]]]]; fold out cap R F in Hw;
    [mlia | mlia | unfold shadow_addr, SHADOW_OFF in Hw; mlia | mlia | mlia]. }
split.
- unfold hq_base3.
  split.
  { unfold hs_core, hs_mid. split; [exact HJ|].
    split; [intros r0 Hr; destruct Hr as [ -> | [ -> | -> ] ]; apply Rk; cbn; tauto|].
    split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
    intros a Ha Hs He. apply KP; [exact Ha | | intros Hw; apply He; exact (mh_W_E3 B cx a Hw)].
    unfold spZ in Hs. rewrite (f_r2 _ _ _ _ HC) in Hs. fold R in Hs. rewrite hc_u64 in Hs by mlia.
    exact Hs. }
  split.
  { destruct Hfx as [Hk Hf]. split; [|exact Hf]. intros k0 Hk0. apply Hk. intros Hin. apply Hk0.
    cbn [In] in Hin |- *. tauto. }
  split; [exact Hfsh|].
  split.
  { apply (hm_rom_kept rsegs (x_W cx) W2 (x_memc cx) mem (f_rom _ _ _ _ HC)).
    intros a Ha.
    assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (img_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
    apply KK; [mlia | intros Ho; exact (Hoimg a Ho Hi) | unfold shadow_addr, SHADOW_OFF; mlia
      | intros Hr; apply (Hfimg a); [mlia | exact Hi] |].
    intros He. exact (ERRNO_RW a He Ha). }
  split.
  { unfold hs_pp_at. eapply hd_garr8_kept; [|exact (f_pp _ _ _ _ HC)]. intros j Hj.
    pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hbl).
    destruct (Model.ents_wf r Hwf) as (He & Hew).
    assert (Hs : Forall (fun e => (length (Model.e_body e) <= 96)%nat) (Model.ents r)).
    { rewrite Forall_forall in Hew |- *. intros x Hx. destruct (Hew x Hx) as (_ & Hb' & Hsz). rewrite Hb'. lia. }
    assert (Hplen : Z.of_nat (length (Layout.pp_bytes r)) = Layout.PP_SIZE)
      by (unfold Layout.pp_bytes; apply Layout.length_pp_image; [unfold Layout.POD_BUF_MAX; mlia | exact He | exact Hs]).
    unfold hd_zbytes in Hj. rewrite length_map in Hj. unfold Layout.PP_SIZE in Hplen. fold pp.
    apply KK; [mlia | mlia | unfold shadow_addr, SHADOW_OFF; mlia | mlia |].
    eapply (Hcerr _ pp Layout.PP_SIZE Hppin). change (req_size Layout.PP_SIZE) with 19744. mlia. }
  split.
  { eapply hd_garr8_kept; [|exact (f_pod _ _ _ _ HC)]. intros j Hj.
    unfold hd_zbytes in Hj. rewrite length_map in Hj. fold pod.
    apply KK; [mlia | mlia | unfold shadow_addr, SHADOW_OFF; mlia | mlia |].
    eapply (Hcerr _ pod len Hpdin). rewrite Hrqp. mlia. }
  split; [exact Hcells|].
  split; [exact Hres | exact Hev].
- intros l v Hin.
  unfold hq_L_seg, hq_L_frame in Hin. cbn [app In] in Hin.
  repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-; cbn [hd_at hd_xv]|]).
  + rewrite (Rk 8 ltac:(cbn; tauto)). exact (f_s0 _ _ _ _ HC).
  + rewrite (Rk 9 ltac:(cbn; tauto)). exact (f_s1 _ _ _ _ HC).
  + rewrite (Rk 19 ltac:(cbn; tauto)). exact (f_s3 _ _ _ _ HC).
  + rewrite (Rk 23 ltac:(cbn; tauto)). exact (f_s7 _ _ _ _ HC).
  + rewrite (Rk 22 ltac:(cbn; tauto)). exact (f_s6 _ _ _ _ HC).
  + exact R24.
  + rewrite (Rk 25 ltac:(cbn; tauto)). exact (f_s9 _ _ _ _ HC).
  + unfold HQ_RES. exact R26.
  + rewrite (f_rc _ _ _ _ HC). exact H27.
  + rewrite (Rk 21 ltac:(cbn; tauto)). exact (f_s5 _ _ _ _ HC).
  + fold R. apply KC8; [mlia | mlia |]. pose proof (f_c20 _ _ _ _ HC) as Hc. rewrite Z.add_0_r in Hc. exact Hc.
  + fold R. apply KC8; [mlia | mlia | exact (f_c40 _ _ _ _ HC)].
  + fold R. apply KC8; [mlia | mlia |]. pose proof (f_c60 _ _ _ _ HC) as Hc. rewrite Z.add_0_r in Hc. exact Hc.
  + fold R. apply KC8; [mlia | mlia |]. change Layout.OFF_N_ENT with 0x4d14. exact (f_c90 _ _ _ _ HC).
  + fold R. apply KC8; [mlia | mlia |]. change Layout.OFF_N_ENT with 0x4d14. exact (f_ca0 _ _ _ _ HC).
  + fold R. apply KC8; [mlia | mlia |]. pose proof (f_cf0 _ _ _ _ HC) as Hc. rewrite Z.add_0_r in Hc. exact Hc.
  + exact H110.
  + exact H118.
  + destruct Hin.
Qed.

(* ===================== the piece ===================== *)
Theorem hq_A_piece_M3a_head : hq_piece_M3a_head_stmt rsegs B MT.
Proof using AMEMSET ERRNO ERRNO_RW MTL PARSE CK_NO CK_COUNT CK_CV.
unfold hq_piece_M3a_head_stmt. intros cx POST r ev Hst HX HFIRST.
destruct Hst as (Hpre & HL5 & Hwf & Hlen & Hpp & Hpod & Hpodf & Hra & Hhull & Hamem & Hal & Houtf & Hrao & Hdj & Hrc &
  Hev & Hfrm).
pose proof (mh_f_of B cx r ev Hpre HL5 Hwf Hlen Hpp Hpod Hpodf Houtf Hdj Hrc Hev Hfrm) as HC.
apply (mh_A B AMEMSET cx r ev POST HC). intros regs1 mem1 md1 HA.
apply (mh_B B AMEMSET cx r ev regs1 mem1 md1 POST HC HA). intros regs2 mem2 md2 HB.
apply (mh_C B MT ERRNO PARSE cx r ev regs2 mem2 md2 POST HC HB). intros fx2 ly3 S3 W3 regs3 mem3 md3 HP3 H10 _.
apply (mh_D (fx := fx) B MT ERRNO MTL CK_NO cx r ev fx2 ly3 S3 W3 regs3 mem3 md3 POST HC HP3 H10).
intros ly4 S4 W4 regs4 mem4 md4 HP4 H27.
apply (mh_E (fx := fx) B MT ERRNO MTL CK_COUNT cx r ev fx2 ly4 S4 W4 regs4 mem4 md4 POST HC HP4 H27).
intros ly5 S5 W5 regs5 mem5 md5 HP5 H27'.
apply (mh_F (fx := fx) B MT ERRNO MTL CK_CV cx r ev fx2 ly5 S5 W5 regs5 mem5 md5 POST HC HP5 H27').
intros ly6 S6 W6 regs6 mem6 md6 HP6 H27''.
apply (mh_G (fx := fx) B MT ERRNO cx r ev fx2 ly6 S6 W6 regs6 mem6 md6 POST HC HP6 H27'').
- intros regsF memF mdF Hc HPF H27F.
  destruct (mh_last cx r ev fx2 ly6 S6 W6 regsF memF mdF HC HPF H27F) as (Hbase & Hat).
  apply (HX fx2 ly6 S6 W6 regsF memF mdF).
  split; [exact Hbase|]. split; [|exact Hc].
  unfold hs_at_cx, hs_at. rewrite Forall_forall. intros [l v] Hin. exact (Hat l v Hin).
- intros regsF memF mdF HPF H27F.
  destruct (mh_last cx r ev fx2 ly6 S6 W6 regsF memF mdF HC HPF H27F) as (Hbase & Hat).
  apply (HFIRST fx2 ly6 S6 W6 regsF memF mdF).
  split; [exact Hbase|].
  unfold hs_at_cx, hs_at. rewrite Forall_forall. intros [l v] Hin. apply Hat.
  unfold hq_L_frame in Hin. unfold hq_L_seg, hq_L_frame. cbn [app In] in Hin |- *. tauto.
Qed.
End s.
End b.

Print Assumptions hq_A_piece_M3a_head.
