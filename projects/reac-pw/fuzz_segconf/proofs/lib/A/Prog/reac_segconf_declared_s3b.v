(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of check_groupa on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CheckGroupaWalk.v, with its module paths, module names and numbers changed; 710 of its 769 lines of code are new or changed and 1128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_role.v, with its module paths and module names changed; 553 of its 596 lines of code are new or changed and 726 lines of the source are left out. *)
(* Helpers of segment S3 of the ASan image-A walk of reac_segconf_declared (fuzz_segconf.asan, interface
   reac_segconf_declared_d.v), part b: the premises reac_declared_vlan_add asks at the call 0x89a14, and the
   parts of the cut carried over that call and over the runs that re-poison parent and vid and write 56(s1). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI67 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot PaSB
PaNoChain PaCallRun PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegBase SegObj SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem reac_segconf_declared_s3a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
#[local] Notation PRE := (dc_pre B STK_reac_segconf_declared RLO RHI GOTW GUARD).
#[local] Notation FI := (dc_fi B STK_reac_segconf_declared).
#[local] Notation UN := (dc_un B).
#[local] Notation KA := (INV_KA B STK_reac_segconf_declared).
#[local] Notation WHERE := (dcs3_where B RLO RHI GOTW GUARD).
#[local] Notation VT := (dcs3_vt B).
#[local] Notation DPVT := (dcs3_dp_vt B).

(* the numbers of the cut that the rest of the file uses again and again *)
Lemma dcs3_nums : forall c k ly3 S3 W3 regs3 mem3 md3,
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
dc_F c + 128 <= alloc_ceiling /\ 4096 <= dc_F c /\ dc_F c mod 32 = 0 /\
in_app (dc_F c) 128 /\
alloc_ceiling + STK_reac_segconf_declared <= dc_sp0 c /\ dc_sp0 c <= 2 ^ 47 /\
dc_sp0 c - 208 <= dc_s1 c <= dc_sp0 c - 192 /\ dc_s1 c mod 32 = 0 /\
In (1, x_fpos c) (frames S3) /\ frame_addr ly3 1 (x_fpos c) = dc_F c /\ ly3 = x_ly c /\
ly_top ly3 <= 2 ^ 47 /\ alloc_ceiling <= ly_stk_lo ly3 /\ ly_stk_lo ly3 + STK_reac_segconf_declared <= dc_sp0 c /\
ly_top ly3 <= ly_stk_hi ly3 /\ dc_sp0 c mod 16 = 0.
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof HUN as [_ Uly _].
assert (Hin1 : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF3 : frame_addr ly3 1 (x_fpos c) = dc_F c) by (unfold dc_F; rewrite Uly; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 1 (x_fpos c) HAR3 Hin1) as (HF0 & HFc & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 (x_fpos c) HAR3 Hin1) as (HF32 & _ & _ & _).
rewrite EF3 in HF0, HFc, HF32, HFapp.
change (fs_frame_bytes 1) with 128 in HFc, HFapp.
pose proof (cp_afn _ _ _ _ _ _ _ HPRE) as HAFN.
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
unfold dc_s1 in *; unfold dc_sp0 in *.
destruct (dc_sp1_facts (spZ (x_regs c)) Hal16) as (Hs1m & Hs1v).
rewrite Uly.
destruct Hs1v as [Hs1e | Hs1e]; rewrite Hs1e in Hs1m |- *;
repeat split; try assumption; try reflexivity; try lia.
all: exact (proj2 HFapp).
Qed.

(* no byte of the walk's footprint is a shadow byte *)
Lemma dcs3_fp_offshadow : forall c k ly3 S3 W3 regs3 mem3 md3,
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
forall x, inFP (dc_FP c) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x.
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN x Hx.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs3 & _).
pose proof (VT _ _ _ _ _ _ _ _ _ (DPVT _ _ _ _ _ _ _ _ _ _ _ _ _ (cp_dpre _ _ _ _ _ _ _ HPRE)))
  as (_ & _ & _ & Hlt & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct (WHERE c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & HN).
destruct (dcs3_nums c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTF : Z.of_nat (length (snd (dc_res c))) <= x_max c).
{ unfold dc_res, r_declared.
  destruct (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 Hlt) as [_ G2]. exact G2. }
assert (HAPP : forall b m y, In (b, m) (ablocks B ly3 S3) -> b <= y < b + req_size m ->
  y < kLowShadowBeg \/ kHighShadowEnd <= y).
{ intros b m y Hin Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & _ & _ & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kHighShadowEnd, kLowShadowBeg. lia. }
unfold dc_FP, declared_W, vtab_W in Hx. cbn [app] in Hx. apply inFP_cons in Hx as [Hx | Hx].
- cbn [fst snd] in Hx. apply (HAPP b0 m0 x Hin0). unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|exfalso; exact (inFP_nil x Hx)].
  apply inFP_cons in Hx as [Hx | Hx]; [|exfalso; exact (inFP_nil x Hx)]. cbn [fst snd] in Hx.
  destruct HN as [(b & m & Hin & Hm & Hlo & Hhi) | [(cid & pos & Hin & Hcid & Hlo & Hhi) | (Hs1 & Hs2 & _)]].
  + pose proof (req_size_pos m Hm) as [P1 P2]. apply (HAPP b m x Hin). lia.
  + assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
    destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid pos HAR3 Hin3) as (_ & _ & Happ).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kHighShadowEnd, kLowShadowBeg. lia.
  + right. unfold kHighShadowEnd. lia.
Qed.

(* the read-only window is still the image's at the cut *)
Lemma dcs3_rod : forall c k ly3 S3 W3 regs3 mem3 md3,
PRE c -> forall (HROI : forall a, RLO <= a < RHI -> in_img SEGS a), ro_below_ofl SEGS RLO RHI ->
FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
arodata_okP SEGS RLO RHI B (rdW W3 mem3).
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HROI HRO HFI HUN.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
apply (arodata_ok_journalP SEGS RLO RHI HROI (RO := HRO) B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c)
  (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)] ly3 S3 W3 mem3 md3 k HJ).
- intros a Hro Hfp.
  apply (dcs3_fp_noimg B RLO RHI GOTW GUARD c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN a Hfp).
  destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (HROI a Hgot)].
- exact (cp_rod _ _ _ _ _ _ _ HPRE).
Qed.

(* a footprint byte above the entry sp is the count cell, and it is readable at the cut *)
Lemma dcs3_vis : forall c ly3 S3 W3 regs3 mem3 md3 (tj : list (list Z * Z)),
PRE c -> FI c 0 ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 -> dc_tab c tj W3 mem3 ->
forall a, inFP (dc_FP c) a -> dc_sp0 c <= a < ly_top ly3 -> rdW W3 mem3 a <> None.
Proof using LAWS.
intros c ly3 S3 W3 regs3 mem3 md3 tj HPRE HFI HUN HTAB a Ha Hrng.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
destruct (WHERE c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & _).
destruct (dcs3_nums c 0 ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
destruct HTAB as (_ & T2 & _ & _).
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
pose proof (VT _ _ _ _ _ _ _ _ _ (DPVT _ _ _ _ _ _ _ _ _ _ _ _ _ (cp_dpre _ _ _ _ _ _ _ HPRE)))
  as (_ & _ & _ & Hlt & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
assert (HTF : Z.of_nat (length (snd (dc_res c))) <= x_max c).
{ unfold dc_res, r_declared.
  destruct (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 Hlt) as [_ G2]. exact G2. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin0) as (_ & _ & Hc0 & _).
unfold dc_FP, declared_W, vtab_W in Ha. cbn [app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
- cbn [fst snd] in Ha. exfalso. unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|exfalso; exact (inFP_nil a Ha)].
  apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]. cbn [fst snd] in Ha.
  specialize (T2 (Z.to_nat (a - x_n c)) ltac:(lia)).
  replace (x_n c + Z.of_nat (Z.to_nat (a - x_n c))) with a in T2 by lia.
  rewrite T2. discriminate.
Qed.

(* every footprint byte is below the allocator's ceiling, unless the count cell is on the caller's real
   stack -- and then the caller's stack is present *)
Lemma dcs3_fp_low : forall c k ly3 S3 W3 regs3 mem3 md3,
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
(forall a, inFP (dc_FP c) a -> a < alloc_ceiling) \/
(dc_sp0 c <= x_n c /\ x_n c + 4 <= ly_top ly3 /\ astack_pres (x_ly c) (w_H (x_W c)) (x_mem c) (dc_sp0 c)).
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs3 & _).
pose proof (VT _ _ _ _ _ _ _ _ _ (DPVT _ _ _ _ _ _ _ _ _ _ _ _ _ (cp_dpre _ _ _ _ _ _ _ HPRE)))
  as (_ & _ & _ & Hlt & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct (WHERE c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & HN).
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin0) as (_ & _ & Hc0 & _).
assert (HTF : Z.of_nat (length (snd (dc_res c))) <= x_max c).
{ unfold dc_res, r_declared.
  destruct (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 Hlt) as [_ G2]. exact G2. }
destruct HN as [(b & m & Hin & Hm & Hlo & Hhi) | [(cid & pos & Hin & Hcid & Hlo & Hhi) | (Hs1 & Hs2 & HAP)]].
- left. intros a Ha. pose proof (req_size_pos m Hm) as [P1 P2].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & _ & Hc1 & _).
  unfold dc_FP, declared_W, vtab_W in Ha. cbn [app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
  + cbn [fst snd] in Ha. unfold seg_spec.RVLAN_SIZE in *. lia.
  + destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|exfalso; exact (inFP_nil a Ha)].
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]. cbn [fst snd] in Ha. lia.
- left. intros a Ha.
  assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid pos HAR3 Hin3) as (_ & Hgc & _).
  unfold dc_FP, declared_W, vtab_W in Ha. cbn [app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
  + cbn [fst snd] in Ha. unfold seg_spec.RVLAN_SIZE in *. lia.
  + destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|exfalso; exact (inFP_nil a Ha)].
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]. cbn [fst snd] in Ha. lia.
- right. split; [exact Hs1 | split; [exact Hs2 | exact HAP]].
Qed.

(* the frame chain at the call: the prologue's saved ra and s0 extend the caller's chain; when the count cell
   lies on the caller's real stack the stack is present and a chain exists for that reason *)
Lemma dcs3_chain : forall c ly3 S3 W3 regs3 (m : word -> option byte) md3 (tj : list (list Z * Z)),
PRE c -> FI c 0 ly3 S3 W3 regs3 m md3 -> UN c ly3 S3 -> dc_tab c tj W3 m ->
exists ch1, achain ly3 (rdW W3 m) (dc_s1 c) (dc_sp0 c) ch1.
Proof using LAWS.
intros c ly3 S3 W3 regs3 m md3 tj HPRE HFI HUN HTAB.
pose proof HFI as [HJ _ _ _ _ _ _ _ Fsaved _ _ _ _ _ _].
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof (cp_afn _ _ _ _ _ _ _ HPRE) as HAFN.
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct (dcs3_nums c 0 ly3 S3 W3 regs3 m md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (dcs3_vis c ly3 S3 W3 regs3 m md3 tj HPRE HFI HUN HTAB) as HVIS.
rewrite NLY. rewrite NLY in HVIS, NT1, NT2, NT3, NT4, HJ.
destruct (dcs3_fp_low c 0 ly3 S3 W3 regs3 m md3 HPRE HFI HUN) as [HLOW | (Hs1 & Hs2 & HAP)].
- (* the whole footprint is below the ceiling: the bytes at and above the entry sp are kept *)
  assert (HKEEP : forall a, dc_sp0 c <= a < 2 ^ 64 -> rdW W3 m a = rdW (x_W c) (x_mem c) a).
  { intros a Ha. apply G1; [lia | lia | intros HF; pose proof (HLOW a HF); lia]. }
  destruct (Z_lt_le_dec (dc_sp0 c) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
  + exists ((dc_sp0 c, raZ (x_regs c), s0Z (x_regs c)) :: x_ch c).
    pose proof (Fsaved 0%nat 1 eq_refl) as H0. pose proof (Fsaved 1%nat 8 eq_refl) as H1.
    change (Z.of_nat 0) with 0 in H0. change (Z.of_nat 1) with 1 in H1.
    replace (dc_sp0 c - 8 - 8 * 0) with (dc_sp0 c - 8) in H0 by lia.
    replace (dc_sp0 c - 8 - 8 * 1) with (dc_sp0 c - 16) in H1 by lia.
    assert (Q1 : getr (x_regs c) (Z_to_bv 5 1) = getr (x_regs c) 1) by (f_equal; apply bv_eq; reflexivity).
    assert (Q8 : getr (x_regs c) (Z_to_bv 5 8) = getr (x_regs c) 8) by (f_equal; apply bv_eq; reflexivity).
    rewrite Q1 in H0. rewrite Q8 in H1.
    apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 m) (dc_sp0 c) (s0Z (x_regs c))
      (raZ (x_regs c)) (x_ch c) (dc_s1 c) Hch).
    * lia.
    * exact HKEEP.
    * exact H0.
    * exact H1.
    * exact Hra4.
    * lia.
    * clear - NT5. Z.div_mod_to_equations. lia.
    * lia.
    * lia.
  + exists []. left. split; [right; left; lia | reflexivity].
- (* the count cell is on the caller's real stack: it keeps the stack present *)
  assert (HVIS' : forall a, inFP (dc_FP c) a -> dc_sp0 c <= a < ly_top (x_ly c) -> rdW W3 m a <> None)
    by exact HVIS.
  assert (HAPJ : astack_pres (x_ly c) (w_H W3) m (dc_sp0 c - STK_reac_segconf_declared))
    by (eapply astack_pres_journal; try eassumption; try exact pa_segs_low; try exact LAWS).
  assert (HRD1 : astack_rd (x_ly c) (rdW W3 m) (dc_s1 c)).
  { eapply astack_rd_mono; [|eapply astack_rd_of_pres; exact HAPJ]. lia. }
  destruct (achain_any (x_ly c) (rdW W3 m) (dc_s1 c) (dc_sp0 c) HRD1
    ltac:(right; right; right; lia)) as (ch & Hch1).
  exists ch. exact Hch1.
Qed.

(* where the table and the count cell lie, relative to the two ranges the post-call run writes *)
Lemma dcs3_app_off : forall c k ly3 S3 W3 regs3 mem3 md3,
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
(forall x, x_tab c <= x < x_tab c + seg_spec.RVLAN_SIZE * (x_max c + 1) ->
   4096 <= x < alloc_ceiling /\ ~ (SB + dc_F c / 8 <= x < SB + dc_F c / 8 + 16)) /\
(forall x, x_n c <= x < x_n c + 4 ->
   (4096 <= x < alloc_ceiling \/ (dc_sp0 c <= x /\ x < 2 ^ 47)) /\
   ~ (SB + dc_F c / 8 <= x < SB + dc_F c / 8 + 16)).
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN.
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs3 & _).
destruct (dcs3_nums c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
destruct (WHERE c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & HN).
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HD1 : 0 <= dc_F c / 8) by (apply Z.div_pos; lia).
assert (HD3 : dc_F c / 8 <= 17592185946112) by (Z.div_mod_to_equations; lia).
assert (HOFF : forall x, (x < kLowShadowBeg \/ kHighShadowEnd <= x) ->
  ~ (SB + dc_F c / 8 <= x < SB + dc_F c / 8 + 16)).
{ intros x Hx Hbad. unfold SB, kLowShadowBeg, kHighShadowEnd in *. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin0) as (_ & Hb40 & Hc0 & Happ0 & _).
split.
- intros x Hx. split; [unfold seg_spec.RVLAN_SIZE in *; lia|].
  apply HOFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ0.
  unfold kHighShadowEnd, kLowShadowBeg. unfold seg_spec.RVLAN_SIZE in *. lia.
- intros x Hx.
  destruct HN as [(b & m & Hin & Hm & Hlo & Hhi) | [(cid & pos & Hin & Hcid & Hlo & Hhi) | (Hs1 & Hs2 & _)]].
  + pose proof (req_size_pos m Hm) as [P1 P2].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hb41 & Hc1 & Happ1 & _).
    split; [left; lia|]. apply HOFF.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ1.
    unfold kHighShadowEnd, kLowShadowBeg. lia.
  + assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
    destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cid pos HAR3 Hin3) as (Hg0 & Hgc & Happ1).
    split; [left; lia|]. apply HOFF.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ1.
    unfold kHighShadowEnd, kLowShadowBeg. lia.
  + split; [right; split; lia|]. apply HOFF. right. unfold kHighShadowEnd. lia.
Qed.

(* reac_declared_vlan_add's premises at the call 0x89a14, over the state of the cut KA *)
Lemma dcs3_add_pre : forall c i ti added p v ly3 S3 W3 regs3 mem3 md3 (regsc : bvmap 5 word) memc,
PRE c -> KA c i ti added p v ly3 S3 W3 regs3 mem3 md3 ->
(forall x : word, memc x = mem3 x) -> spZ regsc = dc_s1 c ->
add_pre SEGS B ly3 S3 W3 memc regsc (x_tab c) (x_max c) (x_n c) (dc_F c + 32) v ti p.
Proof using LAWS.
intros c i ti added p v ly3 S3 W3 regs3 mem3 md3 regsc memc HPRE HKA HEQ HSP.
pose proof HKA as HKA0.
destruct HKA as (HFI & HUN & HTAB & Hi & HLOOP & HLR & H56 & Hign & Hsp & Hstrz & Hvid & Hsh4 & Hsh5 & Hsh8).
pose proof HFI as [HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof HUN as [Uperm Uly Ufs].
pose proof (cp_afn _ _ _ _ _ _ _ HPRE) as HAFN. pose proof (proj1 HAFN) as HAR0.
assert (HRD : forall a, rdW W3 memc a = rdW W3 mem3 a)
  by (intros a; exact (dcs3_aview_ext SEGS (w_H W3) mem3 memc HEQ a)).
destruct (dcs3_nums c 0 ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
destruct (WHERE c _ ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as ((b0 & m0 & Hin0 & Hm0 & Hb0 & Hb1) & _).
pose proof HJ as HJx. rewrite NLY in HJx.
pose proof (VT _ _ _ _ _ _ _ _ _ (DPVT _ _ _ _ _ _ _ _ _ _ _ _ _ (cp_dpre _ _ _ _ _ _ _ HPRE)))
  as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14).
destruct HTAB as (T1 & T2 & T3 & T4).
destruct (dcl_split_some _ _ _ Hsp) as (Hv16 & Hplen).
pose proof (req_size_pos m0 Hm0) as [Q1 Q2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 (x_fpos c) HAR3 NIN1) as (HF32b & HFapp2 & HFpres & HFSpres).
rewrite NEF in HFpres, HFSpres.
change (fs_frame_bytes 1) with 128 in HFpres, HFSpres.
change (128 / 8) with 16 in HFSpres.
assert (HF8 : dc_F c mod 8 = 0) by (clear - NF3; Z.div_mod_to_equations; lia).
assert (HFq : dc_F c = 8 * (dc_F c / 8)) by (clear - HF8; Z.div_mod_to_equations; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin0) as (_ & Hb4096 & Hbceil & Hbapp & _).
(* the table at the cut *)
assert (HRTAB : sa_rtab (rdW W3 memc) (x_tab c) ti).
{ destruct T1 as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
  intros j Hj. rewrite HRD. exact (Hbs j Hj). }
assert (HVAL : sa_val (rdW W3 memc) (x_n c) 4 (Z.of_nat (length ti)))
  by (intros kk Hkk; rewrite HRD; exact (T2 kk Hkk)).
assert (HHEAP : sa_heap B ly3 S3 (x_tab c) (seg_spec.RVLAN_SIZE * (x_max c + 1)))
  by (exists b0, m0; split; [exact Hin0 | split; [exact Hb0 | exact Hb1]]).
assert (HADDRTAB : sa_addr (rdW W3 memc) (x_tab c) (seg_spec.RVLAN_SIZE * x_max c)).
{ destruct V7 as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
  - eapply (range_addressable_agree (rdW W3 mem3)); [intros x _; exact (HRD _)|].
    apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0);
      [exact HAR3 | exact Hin0 | unfold seg_spec.RVLAN_SIZE in *; lia | unfold seg_spec.RVLAN_SIZE in *; lia].
  - intros Hpos s Hs. rewrite HRD. revert s Hs.
    apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0);
      [exact HAR3 | exact Hin0 | unfold seg_spec.RVLAN_SIZE in *; lia
       | unfold seg_spec.RVLAN_SIZE in *; lia | exact Hpos]. }
(* the count cell at the cut: shadow facts by its place *)
assert (HNRA : range_addressable (rdW W3 memc) SHADOW_OFF (x_n c) 4 /\
               shadow_hull_vis (rdW W3 memc) (x_n c) 4 /\
               sa_dst SEGS B ly3 S3 W3 memc regsc (x_n c) 4).
{ destruct V12 as [(Hfr & Hra) | [(Hhp & Hra) | (Hd1 & Hd2 & Hd3 & Hd4)]].
  - destruct Hfr as (cid & pos & Hin & Hcid & Hlo & Hhi).
    assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
    destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR0 Hin) as (Hal32 & _ & _ & _).
    assert (Hal8 : frame_addr (x_ly c) cid pos mod 8 = 0) by (clear - Hal32; Z.div_mod_to_equations; lia).
    assert (HRAe : range_addressable (rdW W3 mem3) SHADOW_OFF (x_n c) 4).
    { apply (range_addressable_entry_frame SEGS B LAWS STK_reac_segconf_declared (dc_sp0 c) (dc_FP c)
        (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)] ly3 S3 W3 mem3 md3 0 cid pos
        (x_n c) 4 HJ Hin Hcid Hlo Hhi Hal8
        (dcs3_fp_offshadow c 0 ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) HAR0 Hra). }
    assert (HRAc : range_addressable (rdW W3 memc) SHADOW_OFF (x_n c) 4)
      by (eapply (range_addressable_agree (rdW W3 mem3)); [intros x _; exact (HRD _) | exact HRAe]).
    split; [exact HRAc|]. split.
    + intros s Hs. rewrite HRD. revert s Hs.
      apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 mem3 md3 cid pos (x_n c) 4);
        [exact HAR3 | exact Hin3 | rewrite <- NLY in Hlo; exact Hlo | rewrite <- NLY in Hhi; exact Hhi | lia].
    + left. split; [|exact HRAc]. exists cid, pos.
      split; [exact Hin3|]. split; [exact Hcid|]. rewrite NLY. split; [exact Hlo | exact Hhi].
  - destruct Hhp as (b & m & Hin & Hlo & Hhi).
    assert (Hin3 : In (b, m) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Uperm)); exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m (proj1 Hm)) as [P1 P2].
    assert (HRAc : range_addressable (rdW W3 memc) SHADOW_OFF (x_n c) 4).
    { eapply (range_addressable_agree (rdW W3 mem3)); [intros x _; exact (HRD _)|].
      apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b m);
        [exact HAR3 | exact Hin3 | lia | lia]. }
    split; [exact HRAc|]. split.
    + intros s Hs. rewrite HRD. revert s Hs.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b m);
        [exact HAR3 | exact Hin3 | lia | lia | lia].
    + right. left. split; [|exact HRAc]. exists b, m. split; [exact Hin3 | split; [exact Hlo | exact Hhi]].
  - change (spZ (x_regs c)) with (dc_sp0 c) in Hd1.
    pose proof V13 as (HN0 & HN63 & _).
    assert (HVIS : forall a, inFP (dc_FP c) a -> dc_sp0 c <= a < ly_top (x_ly c) -> rdW W3 mem3 a <> None).
    { pose proof (dcs3_vis c ly3 S3 W3 regs3 mem3 md3 ti HPRE HFI HUN
        (conj T1 (conj T2 (conj T3 T4)))) as HV.
      rewrite NLY in HV. exact HV. }
    assert (HAPJ : astack_pres (x_ly c) (w_H W3) mem3 (dc_sp0 c - STK_reac_segconf_declared))
      by (eapply astack_pres_journal; [exact pa_segs_low | exact HJx | exact Hd4 | exact HVIS]).
    assert (HAPc : astack_pres ly3 (w_H W3) memc (spZ regsc)).
    { rewrite HSP, NLY. intros a Ha. unfold apresent. rewrite (HEQ (Z_to_bv 64 a)).
      exact (HAPJ a ltac:(lia)). }
    destruct (dcs3_stk_shadow B ly3 S3 W3 mem3 md3 (x_n c) 4 HAR3
      ltac:(lia) ltac:(rewrite <- NLY in Hd2; lia) ltac:(lia)) as (HRAe & HHUe).
    assert (HRAc : range_addressable (rdW W3 memc) SHADOW_OFF (x_n c) 4)
      by (eapply (range_addressable_agree (rdW W3 mem3)); [intros x _; exact (HRD _) | exact HRAe]).
    split; [exact HRAc|]. split.
    + intros s Hs. rewrite HRD. exact (HHUe ltac:(lia) s Hs).
    + right. right. split; [rewrite HSP; lia|]. split; [rewrite NLY; exact Hd2|]. split.
      * intros kk Hkk. unfold apresent. rewrite (HEQ (Z_to_bv 64 (x_n c + kk))).
        apply (apresent_of_aview SEGS (w_H W3) mem3 (x_n c + kk)); [lia| |].
        -- intros Him. pose proof (pa_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia.
        -- specialize (T2 (Z.to_nat kk) ltac:(lia)).
           replace (x_n c + Z.of_nat (Z.to_nat kk)) with (x_n c + kk) in T2 by lia.
           rewrite T2. discriminate.
      * exact HAPc. }
destruct HNRA as (HRAn & HHUn & HDST).
assert (HADDRN : sa_addr (rdW W3 memc) (x_n c) 4).
{ destruct V13 as (A1 & A2 & A3 & _ & _).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact HRAn | intros _; exact HHUn]. }
(* parent at F + 32 *)
assert (HPLEN : Z.of_nat (length p) <= 15) by lia.
assert (HPARRA : range_addressable (rdW W3 memc) SHADOW_OFF (dc_F c + 32) (Z.of_nat (length p) + 1)).
{ intros x Hx. exists 0. split; [|left; reflexivity]. rewrite HRD. unfold shadow_of_addr.
  assert (Hq : x / 8 = dc_F c / 8 + (x - dc_F c) / 8).
  { replace x with ((dc_F c / 8) * 8 + (x - dc_F c)) at 1 by lia.
    rewrite Z.div_add_l by lia. lia. }
  assert (Hd : (x - dc_F c) / 8 = 4 \/ (x - dc_F c) / 8 = 5) by (clear - Hx HPLEN; Z.div_mod_to_equations; lia).
  rewrite <- SB_SHADOW_OFF. rewrite Hq.
  destruct Hd as [Hd | Hd]; rewrite Hd.
  - replace (SB + (dc_F c / 8 + 4)) with (SB + dc_F c / 8 + 4) by lia. exact Hsh4.
  - replace (SB + (dc_F c / 8 + 5)) with (SB + dc_F c / 8 + 5) by lia. exact Hsh5. }
assert (HPARHU : shadow_hull_vis (rdW W3 memc) (dc_F c + 32) (Z.of_nat (length p) + 1)).
{ intros s Hs. rewrite HRD. revert s Hs.
  apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 mem3 md3 1 (x_fpos c)
    (dc_F c + 32) (Z.of_nat (length p) + 1));
  [exact HAR3 | exact NIN1 | rewrite NEF; lia | rewrite NEF; change (fs_frame_bytes 1) with 128; lia | lia]. }
assert (HPARSTRZ : sa_strz (rdW W3 memc) (dc_F c + 32) p).
{ destruct Hstrz as [HZ HN0]. split; [|exact HN0]. intros j Hj. rewrite HRD. exact (HZ j Hj). }
assert (HPARTAIL : sa_tail (rdW W3 memc) (dc_F c + 32 + Z.of_nat (length p))).
{ intros x Hx. pose proof (Z.mod_pos_bound (dc_F c + 32 + Z.of_nat (length p)) 8 ltac:(lia)) as Hm8.
  rewrite HRD. apply (aview_some_of_apresent SEGS (w_H W3) mem3 x).
  exact (proj1 (HFpres x ltac:(lia))). }
assert (HPARAMEM : amem_range (dc_F c + 32) (Z.of_nat (length p) + 8)).
{ apply (amem_range_sub_app (dc_F c) 128); [exact NFapp | lia | lia | lia | lia]. }
assert (HPARADDR : sa_addr (rdW W3 memc) (dc_F c + 32) (Z.of_nat (length p) + 1)).
{ split; [lia|]. split; [lia|]. split.
  - apply (amem_range_sub_app (dc_F c) 128); [exact NFapp | lia | lia | lia | lia].
  - split; [exact HPARRA | intros _; exact HPARHU]. }
assert (HPARLOC : sa_loc SEGS B ly3 S3 (dc_F c + 32) (Z.of_nat (length p) + 1)).
{ right. left. exists 1, (x_fpos c). split; [exact NIN1|]. split; [lia|].
  rewrite NEF. change (fs_frame_bytes 1) with 128. split; lia. }
assert (HPARDISJ : sa_disj (dc_F c + 32) (seg_spec.cstr_span (dc_F c + 32) p) (x_tab c)
                     (seg_spec.RVLAN_SIZE * (x_max c + 1))).
{ unfold seg_spec.cstr_span.
  pose proof (Z.mod_pos_bound (- (dc_F c + 32 + Z.of_nat (length p) + 1)) 8 ltac:(lia)) as Hm8.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b0 m0 1 (x_fpos c) HAR3 Hin0 NIN1) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite NEF in Hd.
  change (fs_frame_bytes 1) with 128 in Hd. unfold sa_disj. lia. }
(* assemble *)
unfold add_pre. split.
{ unfold vtab_pre. split; [exact V1|]. split; [exact V2|]. split; [exact HRTAB|].
  split; [split; [exact T4 | exact V5]|]. split; [exact HHEAP|]. split; [exact HADDRTAB|].
  split; [exact V8|]. split; [exact V9|]. split; [exact V10|]. split; [exact HVAL|].
  split; [exact HDST|]. split; [exact HADDRN | exact V14]. }
split; [lia|]. split; [split; [exact HPARSTRZ | exact HPARTAIL]|].
split; [exact HPARADDR|]. split; [lia|]. split; [exact HPARAMEM|].
split; [exact HPARLOC|]. split; [exact HPARDISJ | lia].
Qed.


(* the frame part of the cut after a run that writes only the running count at 56(s1) and the frame's own
   shadow bytes: the saved registers, the words at 16/24/32/40/48(s1) and the flag word at F + 120 are all
   outside those two ranges *)
Lemma dcs3_fi_run : forall c k ly S W regs (m : word -> option byte) md regs' (m' : word -> option byte) md',
PRE c -> FI c k ly S W regs m md -> UN c ly S ->
ajournal SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)]
  ly S W m' md' k ->
(forall x, ~ (dc_s1 c + 56 <= bv_unsigned x < dc_s1 c + 64) ->
           ~ (SB + dc_F c / 8 <= bv_unsigned x < SB + dc_F c / 8 + 16) -> m' x = m x) ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
getr regs' 20 = getr regs 20 ->
FI c k ly S W regs' m' md'.
Proof using LAWS.
intros c k ly S W regs m md regs' m' md' HPRE HFI HUN HJ' HEQ E2 E3 E4 E8 E9 E19 E20.
pose proof HFI as [HJ F2 F3 F4 F8 F9 F19 F20 Fsaved Ff16 Ff24 Ftab Fmax Fn Fflag].
destruct (dcs3_nums c k ly S W regs m md HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HD1 : 0 <= dc_F c / 8) by (apply Z.div_pos; lia).
assert (HD3 : dc_F c / 8 <= 17592185946112) by (Z.div_mod_to_equations; lia).
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 ->
  ~ (dc_s1 c + 56 <= a < dc_s1 c + 64) -> ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a).
{ intros a Ha H1 H2. unfold aview, mbyte, mrestrict. cbv beta.
  rewrite (HEQ (Z_to_bv 64 a)); [reflexivity| |];
  rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
  rewrite (Z.mod_small a (2 ^ 64)) by lia; assumption. }
assert (HSTKo : forall a, dc_sp0 c - 208 <= a < dc_sp0 c ->
  ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16)) by (intros a Ha Hb; unfold SB in *; lia).
assert (HFRo : forall a, dc_F c <= a < dc_F c + 128 ->
  ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16)).
{ intros a Ha Hb. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in NFapp. unfold SB in Hb. lia. }
constructor.
- exact HJ'.
- rewrite E2. exact F2.
- rewrite E3. exact F3.
- rewrite E4. exact F4.
- rewrite E8. exact F8.
- rewrite E9. exact F9.
- rewrite E19. exact F19.
- rewrite E20. exact F20.
- intros j r Hj. rewrite <- (Fsaved j r Hj). apply rdword_ext. intros ii Hii.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some dc_saved j) ltac:(rewrite Hj; discriminate)) as Hl.
    change (length dc_saved) with 13%nat in Hl. exact Hl. }
  apply HKEEP; [lia | lia | apply HSTKo; lia].
- rewrite <- Ff16. apply rdword_ext. intros ii Hii. apply HKEEP; [lia | lia | apply HSTKo; lia].
- rewrite <- Ff24. apply rdword_ext. intros ii Hii. apply HKEEP; [lia | lia | apply HSTKo; lia].
- rewrite <- Ftab. apply rdword_ext. intros ii Hii. apply HKEEP; [lia | lia | apply HSTKo; lia].
- rewrite <- Fmax. apply rdword_ext. intros ii Hii. apply HKEEP; [lia | lia | apply HSTKo; lia].
- rewrite <- Fn. apply rdword_ext. intros ii Hii. apply HKEEP; [lia | lia | apply HSTKo; lia].
- rewrite <- Fflag. apply rdword_ext. intros ii Hii. apply HKEEP; [lia | lia | apply HFRo; lia].
Qed.

(* the frame part of the cut carried over the call of add *)
Lemma dcs3_fi_call : forall c ti p v k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4,
PRE c ->
(forall a, inFP (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v))) a ->
   (a < alloc_ceiling \/ dc_sp0 c <= a) /\ ~ (dc_F c <= a < dc_F c + 128)) ->
FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
ajournal SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [(1, x_fpos c)] ly4 S4 W4 mem4 md4 (k + k1) ->
ajournal SEGS B STK_reac_declared_vlan_add (dc_s1 c) (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v)))
  ly3 S3 W3 mem3 md3 [] ly4 S4 W4 mem4 md4 k1 ->
aregs_preserved regs3 regs4 ->
FI c (k + k1) ly4 S4 W4 regs4 mem4 md4.
Proof using LAWS.
intros c ti p v k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
  HPRE HAPART HFI HUN HJout HJc HPR.
pose proof HFI as [HJ F2 F3 F4 F8 F9 F19 F20 Fsaved Ff16 Ff24 Ftab Fmax Fn Fflag].
destruct (dcs3_nums c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _ & _ & K12 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKADD : STK_reac_declared_vlan_add = 8304) by (vm_compute; reflexivity).
assert (CS : forall z, acallee_saved z -> forall r : bv 5, bv_unsigned r = z -> getr regs4 r = getr regs3 r).
{ intros z Hz r Hr. subst z. exact (dcs3_pres regs3 regs4 r HPR Hz). }
assert (HKEEP : forall a, dc_s1 c + 16 <= a < dc_sp0 c -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Hr. apply K9; [lia | lia |]. intros HF. destruct (HAPART a HF) as [[Hx | Hx] _]; lia. }
constructor.
- exact HJout.
- rewrite (CS 2 ltac:(unfold acallee_saved; lia) 2%bv eq_refl). exact F2.
- rewrite (CS 3 ltac:(unfold acallee_saved; lia) 3%bv eq_refl). exact F3.
- rewrite (CS 4 ltac:(unfold acallee_saved; lia) 4%bv eq_refl). exact F4.
- rewrite (CS 8 ltac:(unfold acallee_saved; lia) 8%bv eq_refl). exact F8.
- rewrite (CS 9 ltac:(unfold acallee_saved; lia) 9%bv eq_refl). exact F9.
- rewrite (CS 19 ltac:(unfold acallee_saved; lia) 19%bv eq_refl). exact F19.
- rewrite (CS 20 ltac:(unfold acallee_saved; lia) 20%bv eq_refl). exact F20.
- intros j r Hj. rewrite <- (Fsaved j r Hj). apply rdword_ext. intros ii Hii.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some dc_saved j) ltac:(rewrite Hj; discriminate)) as Hl.
    change (length dc_saved) with 13%nat in Hl. exact Hl. }
  apply HKEEP. lia.
- rewrite <- Ff16. apply rdword_ext. intros ii Hii. apply HKEEP. lia.
- rewrite <- Ff24. apply rdword_ext. intros ii Hii. apply HKEEP. lia.
- rewrite <- Ftab. apply rdword_ext. intros ii Hii. apply HKEEP. lia.
- rewrite <- Fmax. apply rdword_ext. intros ii Hii. apply HKEEP. lia.
- rewrite <- Fn. apply rdword_ext. intros ii Hii. apply HKEEP. lia.
- rewrite <- Fflag. apply rdword_ext. intros ii Hii.
  apply (K12 1 (x_fpos c)); [exact NIN1| |].
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite NEF.
    change (fs_frame_bytes 1) with 128. lia.
  + intros HF. destruct (HAPART _ HF) as [_ Hnf]. apply Hnf. lia.
Qed.

(* the word at 56(s1) is untouched by the call of add *)
Lemma dcs3_w56_call : forall c k ti p v added ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 mem4 md4 k1,
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
(forall a, inFP (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v))) a ->
   (a < alloc_ceiling \/ dc_sp0 c <= a) /\ ~ (dc_F c <= a < dc_F c + 128)) ->
rdword (rdW W3 mem3) (dc_s1 c + 56) = Some added ->
ajournal SEGS B STK_reac_declared_vlan_add (dc_s1 c) (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v)))
  ly3 S3 W3 mem3 md3 [] ly4 S4 W4 mem4 md4 k1 ->
rdword (rdW W4 mem4) (dc_s1 c + 56) = Some added.
Proof using LAWS.
intros c k ti p v added ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 mem4 md4 k1 HPRE HFI HUN HAPART H56 HJc.
destruct (dcs3_nums c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKADD : STK_reac_declared_vlan_add = 8304) by (vm_compute; reflexivity).
rewrite <- H56. apply rdword_ext. intros ii Hii.
apply K9; [lia | lia |]. intros HF. destruct (HAPART _ HF) as [[Hx | Hx] _]; lia.
Qed.

(* the table and the count cell survive a run that writes only 56(s1) and the frame's shadow *)
Lemma dcs3_tab_keep : forall c k ly3 S3 W3 regs3 mem3 md3 (tj : list (list Z * Z))
  (W4 : world SEGS) mem4 (mem5 : word -> option byte),
PRE c -> FI c k ly3 S3 W3 regs3 mem3 md3 -> UN c ly3 S3 ->
dc_tab c tj W4 mem4 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dc_s1 c + 56 <= a < dc_s1 c + 64) ->
   ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) -> rdW W4 mem5 a = rdW W4 mem4 a) ->
dc_tab c tj W4 mem5.
Proof using LAWS.
intros c k ly3 S3 W3 regs3 mem3 md3 tj W4 mem4 mem5 HPRE HFI HUN HTJ HEQ.
destruct (dcs3_nums c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
destruct (dcs3_app_off c k ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as (HOT & HON).
destruct HTJ as (J1 & J2 & J3 & J4).
split; [|split; [|split; [exact J3 | exact J4]]].
- destruct J1 as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
  pose proof (proj1 Henc) as Hlen.
  intros j Hj. rewrite Hlen in Hj.
  assert (Hin : x_tab c <= x_tab c + Z.of_nat j < x_tab c + seg_spec.RVLAN_SIZE * (x_max c + 1))
    by (unfold seg_spec.RVLAN_SIZE in *; lia).
  destruct (HOT (x_tab c + Z.of_nat j) Hin) as [Hc Hs].
  rewrite HEQ; [| lia | lia | exact Hs]. apply Hbs. rewrite Hlen. exact Hj.
- intros kk Hkk.
  assert (Hin : x_n c <= x_n c + Z.of_nat kk < x_n c + 4) by lia.
  destruct (HON (x_n c + Z.of_nat kk) Hin) as [Hc Hs].
  rewrite HEQ;
  [ exact (J2 kk Hkk)
  | destruct Hc as [Hx | Hx]; lia
  | destruct Hc as [Hx | Hx]; intros Hb; lia
  | exact Hs ].
Qed.

End e.
End f.
End d.
