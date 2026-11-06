(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp_x734: proves no function (kind: segment lemma).
   cmp_x734_q734, a piece of the cmp segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput_seg_cmp.v): the exit of the bcmp double loop at +0x734 (cmp_x734: the loop's
   journal, its registers, the memory as at +0x66c outside the spill area and bcmp's stack window
   [d_sp1 - 8192, d_sp1 + 120), and the spill slots) is the cut point cmp_q734.
   No engine: every memory fact of cmp_q734 that is not a spill slot lies outside that window, so it is the
   +0x66c memory's.  The window starts at or above alloc_ceiling (the journal's astk_ok: alloc_ceiling <=
   ly_stk_lo, ly_stk_lo + DEC_LLVMF_STK <= d_sp0, d_sp0 - 240 <= d_sp1) and ends at or below d_sp0 - 104 (d_sp1 <=
   d_sp0 - 224): the saved words are above it, the fake frame, the heap blocks (res, the payload) and the frame's
   shadow below it (frames_bounds, al_blocks, shadow_addr), and so are the REAC_MODE table words, which
   dec_a_mode_ok reads (DEC_RO_RD, cmp_mode_re).  The payload and body lengths come from dec_a_base
   (n = length pl).  Helpers copied from LLVMFuzzerTestOneInput_seg_cmp_tail.v (a Theorem Labs lane) and, through it, from
   LLVMFuzzerTestOneInput_seg_crt1.v and LLVMFuzzerTestOneInput_seg_exit_free.v. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00 YO09 YM05 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaRun PaShadow PaJournal PaStep DecodeSyms DecodeList DecodeAddr DecodePa DecodeImg DecodePaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC1i YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require
reac_upstream_channels_cg reac_decode_plain_le_c reac_upstream_channels_c reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_cmp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_c.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_cg.
(* YC4b switches lia's division handling off for its importers; the shadow bound below needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* LLVMFuzzerTestOneInput_seg_crt1.v c1_saved_at_range (as a Theorem Labs lane's ct_saved_at_range). *)
Lemma cx_saved_at_range : Forall (fun o : Z * Z => 8 <= fst o <= 104) dec_a_saved_at.
Proof. unfold dec_a_saved_at. repeat constructor; cbn [fst]; lia. Qed.

Section cmpx.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.

(* a Theorem Labs lane's ct_rdword_kept / ct_garr8_kept / ct_saved_kept. *)
Lemma cx_rdword_kept : forall (W W' : world segs) mem mem' a v,
  (forall k, 0 <= k < 8 -> aview segs (w_H W') mem' (a + k) = aview segs (w_H W) mem (a + k)) ->
  rdword (aview segs (w_H W) mem) a = Some v -> rdword (aview segs (w_H W') mem') a = Some v.
Proof. intros W W' mem mem' a v Hk H. rewrite (rdword_ext _ _ a Hk). exact H. Qed.

Lemma cx_garr8_kept : forall (W W' : world segs) mem mem' p (l : list Z),
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs (w_H W') mem' (p + k) = aview segs (w_H W) mem (p + k)) ->
  garr8 segs (mrestrict (w_H W) mem) p l -> garr8 segs (mrestrict (w_H W') mem') p l.
Proof.
intros W W' mem mem' p l Hk H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk1. rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (p + Z.of_nat j + Z.of_nat k)).
- exact (Hv k Hk1).
- replace (p + Z.of_nat j + Z.of_nat k) with (p + (Z.of_nat j + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

Lemma cx_saved_kept : forall cx (r r' : reader),
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> r' a = r a) -> dec_a_saved cx r -> dec_a_saved cx r'.
Proof.
intros cx r r' HK Hsv. unfold dec_a_saved in *. rewrite Forall_forall in Hsv |- *. intros o Ho.
pose proof (proj1 (Forall_forall _ _) cx_saved_at_range o Ho) as Ro. cbv beta in Ro.
rewrite (rdword_ext r r' _); [exact (Hsv o Ho)|]. intros k Hk. apply HK. lia.
Qed.

Section x.
Context {fx : YK11.FPState}.

Lemma cmp_x734_q734 : forall (cx : dctx) ly5 S5 (W5 : world decodesegs0) regs5 mem5 md5 res out mode nch ns
    (W2 : world decodesegs0) c2,
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_core B cx ly5 S5 W5 regs5 mem5 md5 dec_ev_5fc ->
  Permutation (ablocks B ly5 S5) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++ [(out, dec_a_olen nch ns)]) ->
  4096 <= res -> 4096 <= out ->
  mo_le MT (d_S cx) S5 (dec_spent_5fc MT (d_n cx)) -> mo_ok MT S5 (dec_rest_5fc MT) ->
  dec_a_mode_ok cx W5 mem5 mode nch ns ->
  dec_a_fsh cx (aview decodesegs0 (w_H W5) mem5) 0 4 ->
  garr8 decodesegs0 (mrestrict (w_H W5) mem5) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  frm_zero (@fp_csr fx) ->
  @cmp_x734 rc B fx cx ly5 S5 W5 mem5 res out W2 c2 -> @cmp_q734 rc B MT cx W2 c2.
Proof.
intros cx ly5 S5 W5 regs5 mem5 md5 res out mode nch ns W2 c2 LAWS HCELLS HB Hcore5 Hperm5 Hres4096 Hout4096
  Hmle5 Hmok5 Hmode5 Hfsh5 Hres5 Hfrm HX.
destruct HX as (-> & regs & mem & md & -> & HJ & Rsp & R9x & R8x & Rgp & Rtp & Hfr & R17 & R18 & R20 & HK & Hgr
  & S8 & S16 & S24 & S40 & S48 & S56 & S64 & S72 & S112).
destruct Hcore5 as (HJ5 & Hfrs5 & R8 & R9 & Hsp5 & Hsp240 & Hsp32 & Rgp5 & Rtp5 & Hsaved5 & HF4096 & HF32 & HFpres5
  & HFL5 & Hblk5 & Hgarr5).
unfold dec_a_base, dec_lib_pre_x in HB.
destruct HB as (_ & _ & _ & _ & Hpn & Hplen & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ5 as (HAR5 & Hly5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk5 & _).
pose proof Hstk5 as (Hsp0al & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in Hslo.
(* the window [d_sp1 - 8192, d_sp1 + 120) lies between alloc_ceiling and d_sp0 - 104 *)
assert (KLO : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W5) mem a = aview segs (w_H W5) mem5 a)
  by (intros a Ha; apply HK; lia).
assert (KHI : forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> aview segs (w_H W5) mem a = aview segs (w_H W5) mem5 a)
  by (intros a Ha; apply HK; lia).
(* the fake frame and its shadow, below alloc_ceiling *)
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S5)) by (rewrite Hfrs5; left; reflexivity).
assert (HF5 : frame_addr ly5 DEC_FCLASS (d_fpos cx) = d_F cx).
{ destruct Hly5 as (_ & _ & _ & _ & _ & EF & _). unfold d_F, frame_addr. rewrite EF. reflexivity. }
destruct (frames_bounds segs B LAWS _ _ _ _ _ DEC_FCLASS (d_fpos cx) HAR5 Hfin) as (HFb4096 & HFbceil & _).
rewrite HF5 in HFb4096, HFbceil. change (fs_frame_bytes DEC_FCLASS) with 64 in HFbceil.
assert (HSHb : 0 <= d_SH cx /\ d_SH cx + 8 <= alloc_ceiling).
{ unfold d_SH, shadow_addr, SHADOW_OFF. split; [|]; lia. }
(* a heap block of state 5, below alloc_ceiling *)
assert (KBLK : forall p n k, In (p, n) (ablocks B ly5 S5) -> 0 <= k < n ->
  aview segs (w_H W5) mem (p + k) = aview segs (w_H W5) mem5 (p + k)).
{ intros p n k Hin Hk.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR5 Hin) as (_ & Hp4096 & Hpc & _).
  pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq). apply KLO. lia. }
assert (HinR : In (res, dec_a_len (d_n cx)) (ablocks B ly5 S5)).
{ apply (Permutation_in _ (Permutation_sym Hperm5)). apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
assert (Hblen : Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx))
  by (unfold d_body; exact (cmp_body_len (d_pl cx) (d_n cx) Hplen)).
unfold cmp_q734.
exists fx, ly5, S5, regs, mem, md, res, out, mode, nch, ns.
split; [reflexivity|].
split; [exact Hfrm|].
split.
{ unfold dec_a_core.
  split; [exact HJ|].
  split; [exact Hfrs5|].
  split; [exact R8x|]. split; [exact R9x|].
  split; [unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; lia|].
  split; [exact Hsp240|]. split; [exact Hsp32|].
  split; [exact Rgp|]. split; [exact Rtp|].
  split; [exact (cx_saved_kept cx _ _ KHI Hsaved5)|].
  split; [exact HF4096|]. split; [exact HF32|].
  split; [intros a Ha; apply Hgr; exact (HFpres5 a Ha)|].
  split; [apply (cx_rdword_kept W5 W5 mem5 mem); [intros k Hk; apply KLO; lia | exact HFL5]|].
  split; [exact Hblk5|].
  apply (cx_garr8_kept W5 W5 mem5 mem (d_p cx)); [|exact Hgarr5].
  intros k Hk. rewrite length_map, <- Hplen in Hk.
  exact (KBLK (d_p cx) (d_n cx) k (Hblk5 ltac:(lia)) Hk). }
split; [exact Hperm5|].
split; [exact Hres4096|]. split; [exact Hout4096|].
split; [exact Hmle5|]. split; [exact Hmok5|].
split; [exact Hfr|].
split; [exact R17|]. split; [exact R18|]. split; [exact R20|].
split; [apply (cmp_mode_re B cx W5 W5 mem5 mem ly5 S5 md5 ly5 S5 md mode nch ns HCELLS HAR5 (proj1 HJ) Hmode5);
  [intros a Ha; pose proof (cmp_ro_rd_low a Ha); apply KLO; lia | intros k Hk; apply KLO; lia]|].
split.
{ destruct Hfsh5 as (FS1 & FS4 & FS5 & FS6).
  split; [|split; [|split]].
  - intros i Hi. rewrite KLO by lia. exact (FS1 i Hi).
  - rewrite KLO by lia. exact FS4.
  - rewrite KLO by lia. exact FS5.
  - intros i Hi. rewrite KLO by lia. exact (FS6 i Hi). }
split.
{ apply (cx_garr8_kept W5 W5 mem5 mem res); [|exact Hres5].
  intros k Hk. rewrite length_map, Hblen in Hk. exact (KBLK res (dec_a_len (d_n cx)) k HinR Hk). }
split; [intros _; exact (conj S8 (conj S16 (conj S24 S48)))|].
split; [exact S40|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72|].
exact S112.
Qed.

End x.
End cmpx.
