(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmitTail), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The tail of the admission tests of fuzz_grant's entry function LLVMFuzzerTestOneInput
   on the ASan build: slots 0x80e30 .. 0x80e58 (GP_mid .. GP_sweep), fuzz_grant.c:269-277.

   The harness marks the 2-byte `a` usable in the frame's shadow (`li a0,2; sb a0,56(s6)`
   at 0x80e30, 0x80e34), zeroes it (`sh zero,0(s2)`, 0x80e38), calls reac_grant_allocate
   (0x80e48) with the address of `a`, the base and the width, then computes s3 - 1 and
   reads the address of `raw` back from the spill slot 72 (0x80e4c, 0x80e50). The branch
   at 0x80e54 (`bne a0,s3`) into the block at 0x81a0c (__asan_handle_no_return, then
   abort) is not taken: the call answers 0 exactly when the box fits (GrantModel.fits,
   which is GrantSlotPlan.ok of the input), and s3 held that answer as 1 or 0.

   The walk runs on a symbolic state of its own with three regions: the shadow byte
   that marks `a` (s6 + 56), the two bytes of `a` (s2), and the spill slot 72 (s1 + 72).
   The facts of the cut GI_mid on the rest of memory are carried across the stores and
   the call by `admKeep` (GrantEntryAdmitDefs.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
YC1g YC1h YC88 GrantFrame YC45 YC85 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
CtrlFinish GrantAllocate GrantEntryDefs GrantEntrySeat GrantEntryAdmitDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel Seg_admit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The base and the width the input asks for. *)
Local Notation hbase cx := (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))).
Local Notation hwid cx := (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* ---- small facts on the environment of the run ---- *)
Lemma at_ewR : forall (regs : bvmap 5 word) extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma at_zcanon_in : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma at_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma at_denot_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* A run that writes only into its windows keeps every byte outside them. *)
Lemma at_keep_outside : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a HF Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
(* A run whose regions have no window writes no byte. *)
Lemma at_frame_none : forall E rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hr & Hb).
rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.
(* Two zero bytes written as one halfword are two zero bytes. *)
Lemma at_val2_garr8 : forall (m : word -> option byte) a,
  val_mem SEGS m a 2 0 -> garr8 SEGS m a [0; 0].
Proof.
intros m a H j Hj. cbn [length] in Hj.
assert (Hc : j = 0%nat \/ j = 1%nat) by lia.
destruct Hc as [-> | ->]; cbn [nth]; (split; [|lia]); intros q Hq; replace q with 0%nat by lia.
- specialize (H 0%nat ltac:(lia)).
  replace (a + Z.of_nat 0 + Z.of_nat 0) with (a + Z.of_nat 0) by lia. rewrite H.
  do 2 f_equal; vm_compute; reflexivity.
- specialize (H 1%nat ltac:(lia)).
  replace (a + Z.of_nat 1 + Z.of_nat 0) with (a + Z.of_nat 1) by lia. rewrite H.
  do 2 f_equal; vm_compute; reflexivity.
Qed.

(* ---- the symbolic state of the run ---- *)
(* The shadow byte that marks `a`: s6 + 56 (s6 is the frame's shadow base). *)
Definition AT_Rsh : YP09.region := YP09.mkRegion (Some 22%nat) 56 57 56 57 [].
(* The two bytes of `a`: s2. *)
Definition AT_Ra : YP09.region := YP09.mkRegion (Some 18%nat) 0 2 0 2 [].
(* The spill slot 72 above the realigned stack pointer s1: the address of `raw`, atom 32. *)
Definition AT_R72 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 72 80 0 0 [YP09.mkChunk 72 (CVal 8 (SOff 32 0))].
Definition at_ss0 : sstate :=
  mkSS GP_mid sr_atoms [AT_Rsh; AT_Ra; AT_R72] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47) 5)] [] []).

(* The value of a register of the symbolic state, from the atom facts. *)
Local Ltac regval HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = w64 ?v =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R;
    lazymatch e with
    | SOff ?n 0 =>
        rewrite at_denot_off0;
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ => rewrite F; unfold w64; first [reflexivity | f_equal; lia] end
    | SOff ?n ?x =>
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite (at_denot_off_val Ex n u x F) by lia; unfold w64; f_equal; lia end
    end end end.
(* The register r of the symbolic state, as the symbolic value the run left in it. *)
Local Ltac regsv HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R
  end end.
(* After a call: the facts on the atoms below k hold in the new environment. *)
Local Ltac restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = Z_to_bv 64 ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = Z_to_bv 64 v |- _ => fail
      | _ => let F' := fresh "F" in assert (F' : ew En n = Z_to_bv 64 v) by (rewrite OLD by (cbv; lia); exact F)
      end
  end end.
(* Every region of the run's state has its window shut. *)
Local Ltac nowin HF :=
  lazymatch type of HF with frame_of ?Ex ?rs ?m ?m' =>
    let rs' := eval vm_compute in rs in change rs with rs' in HF;
    apply (at_frame_none Ex rs' m m'); [repeat constructor; cbn; lia | exact HF] end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis HALLOC : talloc_spec B (BASE + AF_reac_grant_allocate).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* The machine stack pointer the entry function was called with, and the realigned one. *)
Lemma at_gsp : forall cx, ge_base B MT cx ->
  alloc_ceiling + GE_STK <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 320 < c_sp1 cx <= spZ (c_regs cx) - 288 /\
  c_sp1 cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
intros cx HB.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hmp.
rewrite Hsp1. split; [lia|]. split; [lia|]. split; [|exact Hal16].
rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Theorem ge_admit_tail : forall POST,
  ge_from B MT POST (GI_sweep B MT) -> ge_from B MT POST (GI_mid B MT).
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & HBODY & Hk & Hacc & HBLK & HCN & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R26
                 & S88 & S120 & S64 & S96 & SLATE & HTAB & HWAS & HSET & HREL & HI1).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL
                     & Hlen & HIN).
pose proof SLATE as (SMID & SL8 & SL32 & SL40 & SL72 & SL80 & SL104 & SL112 & SL128).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (at_gsp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GE_STK in Hsp.
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & Hinp & _).
(* the model of the input: the header's ranges, and the library's rule is the harness's *)
pose proof (Seg_admit.hdr_ranges (c_pl cx)) as (Ru & Rb & Ri & Rr & Rs).
assert (Eok : GrantSlotPlan.ok (c_pl cx) = fits (hbase cx) (hwid cx)) by reflexivity.
(* the frame on the side stack, its shadow, and the table *)
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF1 & HF2 & _).
assert (EgF : gF cx fp = frame_addr ly3 GE_CID fp) by (unfold gF, frame_addr; rewrite HlyF; reflexivity).
rewrite <- EgF in HF1, HF2. change (fs_frame_bytes GE_CID) with 1024 in HF2.
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR Hfin) as (HFal & HFia & HFpres & HFSpres).
rewrite <- EgF in HFal, HFia, HFpres, HFSpres.
change (fs_frame_bytes GE_CID) with 1024 in HFia, HFpres.
change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres.
assert (HshA : shadow_addr (gF cx fp) = gSH cx fp) by (unfold shadow_addr, gSH, shadow_of_addr; reflexivity).
rewrite HshA in HFSpres.
assert (HSHeq : gSH cx fp = SHADOW_OFF + gF cx fp / 8) by reflexivity.
assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (Hm8 : gF cx fp mod 8 = 0).
{ pose proof HFal as H32. apply Z.mod_divide in H32; [|lia]. destruct H32 as [q Hq].
  apply Z.mod_divide; [lia|]. exists (4 * q). lia. }
pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as Hq8. rewrite Hm8, Z.add_0_r in Hq8.
assert (Hs16 : c_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as Hdm. rewrite Hsp32, Z.add_0_r in Hdm. rewrite Hdm.
  replace (32 * (c_sp1 cx / 32)) with ((c_sp1 cx / 32 * 2) * 16) by lia. apply Z_mod_mult. }
assert (GEOF : gF cx fp + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gF cx fp)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; lia).
assert (GEOS : 0x7fff8000 <= gSH cx fp /\ gSH cx fp + 128 <= 0x10007fef8080)
  by (rewrite HSHeq; unfold SHADOW_OFF; lia).
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as HFo.
rewrite <- EgF in HFo. change (fs_frame_bytes GE_CID) with 1024 in HFo. unfold off_img in HFo.
assert (Htin : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ t 460 HAR Htin) as (_ & Ht4096 & Htceil & Htapp & _).
change (req_size 460) with 460 in Htceil, Htapp.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ t 460 GE_CID fp HAR Htin Hfin) as Htd.
rewrite <- EgF in Htd. change (req_size 460) with 460 in Htd. change (fs_frame_bytes GE_CID) with 1024 in Htd.
unfold zdisjoint in Htd. cbn [fst snd] in Htd.
unfold in_app, kLowShadowBeg, kHighMemBeg in Htapp.
(* the caller's input block *)
assert (HINP : c_n cx = 0 \/
  (In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ c_p cx + c_n cx <= alloc_ceiling /\ c_n cx <= req_size (c_n cx) /\
   4096 <= c_p cx /\ (c_p cx + req_size (c_n cx) <= 0x7fff7000 \/ 0x10007fff8000 <= c_p cx) /\
   (c_p cx + req_size (c_n cx) <= gF cx fp \/ gF cx fp + 1024 <= c_p cx))).
{ destruct Hinp as [(Hn0 & _) | (Hn & Hin0)]; [left; exact Hn0 | right].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & Happ & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ GE_CID fp HAR Hin3 Hfin) as Hd.
  rewrite <- EgF in Hd. change (fs_frame_bytes GE_CID) with 1024 in Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  split; [exact Hin3|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Hd]. }
(* Every byte the cut's facts speak about lies outside the two windows the run writes. *)
assert (GEO : forall a, admZ cx fp t a ->
  0 <= a < 2 ^ 64 /\ ~ (gSH cx fp + 56 <= a < gSH cx fp + 57) /\ ~ (gF cx fp + 448 <= a < gF cx fp + 450)).
{ intros a Ha. unfold admZ in Ha.
  destruct Ha as [Ha | [Ha | [[Ha Hx] | [[Ha Hx] | Ha]]]].
  - lia.
  - destruct HINP as [Hn0 | (_ & Hpc1 & Hrq & Hp4 & Hpa & Hpd)]; lia.
  - lia.
  - lia.
  - lia. }
(* the environment of the run *)
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (gF cx fp + GO_RAW)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r Hq; subst E; apply at_ewR; exact Hq).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 (gF cx fp + 448)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (F19 : ew E 19 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx))))
  by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (F20 : ew E 20 = Z_to_bv 64 t) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (F21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (F22 : ew E 22 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (F23 : ew E 23 = Z_to_bv 64 (hbase cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (F24 : ew E 24 = Z_to_bv 64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (F26 : ew E 26 = Z_to_bv 64 (hwid cx)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (F32 : ew E 32 = Z_to_bv 64 (gF cx fp + GO_RAW))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = gF cx fp + 448) by (rewrite F18; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = gSH cx fp) by (rewrite F22; apply unsigned_lit_small; lia).
(* the machine state as the engine's symbolic state at 0x80e30 *)
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_mid))
  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E at_ss0 (restrict (w_H W3) ms3)).
{ rewrite Hms. unfold at_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold AT_Rsh, AT_Ra, AT_R72.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      unfold YP09.region_ok; cbv zeta;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    + rewrite U22. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite U18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (gF cx fp + 448 + o) ltac:(lia))).
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ _ 72 8 (SOff 32 0) (gF cx fp + GO_RAW)).
      * rewrite at_denot_off0. exact F32.
      * cbn [Z.of_N]. unfold GO_RAW. lia.
      * cbn [Z.of_N]. lia.
      * apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact SL72.
  - unfold AT_Rsh, AT_Ra, AT_R72. cbn [YP09.pairwise_disjoint YP09.all_disjoint]; repeat split;
      unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
      rewrite ?U22, ?U18, ?U9; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|split; [|exact I]];
      unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?U9, ?U18; change (2 ^ 5) with 32.
    + split; [lia|]. split; [exact Hsp32 | lia].
    + split; [lia|]. split; [|lia]. rewrite Z.add_mod, HFal by lia. reflexivity. }
clear HE EE.
(* ---- 0x80e30 .. 0x80e48: mark `a` usable, zero it, and call reac_grant_allocate ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 22%nat (gSH cx fp)); [reflexivity | exact U22 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists GE_CID, fp.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite <- EgF, HshA. change (fs_frame_bytes GE_CID / 8) with 128. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (gF cx fp + 448)); [reflexivity | exact U18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists GE_CID, fp.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite <- EgF. change (fs_frame_bytes GE_CID) with 1024. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msN) |- _ => rename msN into msC end.
rename HF into HFC. rename HFr into HFrC. clear HG.
(* What the run kept: every byte of the cut's facts. *)
assert (KA : admKeep cx fp t W3 (ms_mem ms3) (ms_mem msC)).
{ intros a Ha. destruct (GEO a Ha) as (Ha64 & N1 & N2).
  apply (at_keep_outside E _ _ _ (w_H W3) a HFC Ha64).
  intros (r & Hr & Hb). unfold at_ss0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; unfold AT_Rsh, AT_Ra, AT_R72 in Hb;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U22, ?U18, ?U9 in Hb; lia. }
(* What the run wrote: the shadow byte 2 at s6 + 56 and the two zero bytes of `a`. *)
pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as RG1.
assert (V56 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (gSH cx fp + 56) 1 2).
{ apply (field_of_region E _ 22%nat (gSH cx fp) _ _ _ _ _ 56 1%N (SLit 2) 2 RG0 U22);
    [cbn [In]; left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
assert (VA : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (gF cx fp + 448 + 0) 2 0).
{ apply (field_of_region E _ 18%nat (gF cx fp + 448) _ _ _ _ _ 0 2%N (SLit 0) 0 RG1 U18);
    [cbn [In]; left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
rewrite Z.add_0_r in VA.
assert (A56 : aview SEGS (w_H W3) (ms_mem msC) (gSH cx fp + 56) = Some 2)
  by (apply (aview_of_val_mem1 SEGS); [exact V56 | lia]).
(* the registers at the call *)
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
rewrite pa_sigma_reac_grant_allocate.
assert (Qsp : spZ (ms_regs msC) = c_sp1 cx) by (unfold spZ; rewrite Q2, F2; apply unsigned_lit_small; lia).
pose proof HJ as (HARC & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HARC Hfin) as (_ & _ & HFpresC & _).
rewrite <- EgF in HFpresC. change (fs_frame_bytes GE_CID) with 1024 in HFpresC.
(* the premises of reac_grant_allocate's contract that rule out NULL and the image for `a` *)
assert (POFF : off_img (gF cx fp + 448) 2) by (unfold off_img; lia).
assert (PAPP : forall x, gF cx fp + 448 <= x < gF cx fp + 448 + 2 -> app_addr x)
  by (intros x Hx; apply (in_app_addr (gF cx fp) 1024 x HFia); lia).
assert (TWR : twr_ok B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) ly3 S3 [(GE_CID, fp)] W3 (ms_mem msC)
  (spZ (ms_regs msC)) (gF cx fp + 448) 2).
{ intros a Ha. split; [|split; [|split]].
  - right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite <- EgF. change (fs_frame_bytes GE_CID) with 1024. lia.
  - exact (proj1 (HFpresC a ltac:(lia))).
  - exact (proj2 (HFpresC a ltac:(lia))).
  - rewrite Qsp. unfold ESTACK. lia. }
assert (RAD : range_addressable (aview SEGS (w_H W3) (ms_mem msC)) SHADOW_OFF (gF cx fp + 448) 2).
{ intros x Hx.
  assert (Hx8 : x / 8 = gF cx fp / 8 + 56).
  { symmetry. apply (Z.div_unique x 8 (gF cx fp / 8 + 56) (x - 8 * (gF cx fp / 8 + 56))); [left; lia | lia]. }
  exists 2. split.
  - unfold shadow_of_addr. rewrite Hx8. replace (SHADOW_OFF + (gF cx fp / 8 + 56)) with (gSH cx fp + 56) by lia.
    exact A56.
  - right. split; [|lia]. rewrite Z.mod_eq by lia. rewrite Hx8. lia. }
assert (GA0 : garr8 SEGS (mrestrict (w_H W3) (ms_mem msC)) (gF cx fp + 448) [0; 0])
  by (apply at_val2_garr8; exact VA).
eapply SRr_bind.
{ exact (HALLOC GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)]
    ly3 S3 W3 _ _ k (ms_regs msC) (gF cx fp + 448) (hbase cx) (hwid cx) 0 0 HJ
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
    ltac:(rewrite Q3, F3; reflexivity) ltac:(rewrite Q4, F4; reflexivity)
    ltac:(rewrite Q10, F18; reflexivity) ltac:(rewrite Q11, F23; reflexivity) ltac:(rewrite Q12, F26; reflexivity)
    ltac:(unfold int32; lia) ltac:(unfold int32; lia) ltac:(intros; lia)
    ltac:(rewrite Qsp; exact Hs16)
    ltac:(rewrite Qsp; unfold TALLOC_STK, ESTACK, GE_STK; lia) ltac:(rewrite Qsp; lia)
    ltac:(lia) ltac:(rewrite Qsp; right; unfold TALLOC_STK, ESTACK; lia)
    POFF PAPP TWR RAD GA0). }
(* ---- after the call ---- *)
intros W2 c2 _ (EW & regs2 & mem2 & md2 & Ec2 & HJ2 & HP2 & Ha0 & Hga & HKT). subst W2 c2.
unfold EV_ALLOC in HJ2. rewrite Z.add_0_r in HJ2.
rewrite Qsp in HKT. destruct HKT as (K1 & K2 & K3 & K4 & K5 & K6).
(* What the call kept: every byte of the cut's facts, and the shadow byte of `a`. *)
assert (KC : admKeep cx fp t W3 (ms_mem msC) mem2).
{ intros a Ha. destruct (GEO a Ha) as (Ha64 & N1 & N2).
  unfold admZ in Ha. destruct Ha as [Ha | [Ha | [[Ha Hx] | [[Ha Hx] | Ha]]]].
  - apply K1; [lia | unfold TALLOC_STK, ESTACK; lia | cbv beta; lia].
  - destruct HINP as [Hn0 | (Hin3 & Hpc1 & Hrq & Hp4 & Hpa & Hpd)]; [lia|].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin3); [lia | cbv beta; lia].
  - apply (K4 GE_CID fp a Hfin); [|cbv beta; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EgF. change (fs_frame_bytes GE_CID) with 1024. lia.
  - apply (K4 GE_CID fp a Hfin); [|cbv beta; lia].
    right. unfold in_zr. cbn [fst snd]. rewrite <- EgF, HshA. change (fs_frame_bytes GE_CID / 8) with 128. lia.
  - replace a with (t + (a - t)) by lia.
    apply (K2 t 460 (a - t) Htin); [change (req_size 460) with 460; lia | cbv beta; lia]. }
assert (A56b : aview SEGS (w_H W3) mem2 (gSH cx fp + 56) = Some 2).
{ rewrite <- A56. apply (K4 GE_CID fp _ Hfin); [|cbv beta; lia].
  right. unfold in_zr. cbn [fst snd]. rewrite <- EgF, HshA. change (fs_frame_bytes GE_CID / 8) with 128. lia. }
(* the symbolic state at the return slot 0x80e4c keeps the spill slot 72 *)
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W3) mem2) HP2 [2%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_cons; [|apply Forall_nil]. cbn [ms_mem restrict]. split.
  - cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9. intros a Ha.
    apply (mbyte_of_aview SEGS). apply K1; [lia | unfold TALLOC_STK, ESTACK; lia | cbv beta; lia].
  - cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val]. intros a Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite Q1.
remember (havoc E 33 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall q, (q < 33)%nat -> ew E1 q = ew E q)
  by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
assert (F37 : ew E1 37 = Z_to_bv 64 (if fits (hbase cx) (hwid cx) then 0 else -1)).
{ rewrite HE1. change 37%nat with (33 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 33 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Ha0. }
clear HE1.
restate OLD1.
clear HJ. rename HJ2 into HJ.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* ---- 0x80e4c .. 0x80e54: s3 - 1, the address of `raw`, and the check ---- *)
paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msD end.
assert (PD : forall x, ms_mem msD x = mem2 x) by nowin HF.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ (* the branch into 0x81a0c is taken only if a0 <> s3 - 1, and both are the answer *)
  exfalso. rewrite branch_ne_U in Hc. apply (proj1 (Bool.negb_true_iff _)), Z.eqb_neq in Hc. apply Hc.
  rewrite !U_SOff.
  repeat match goal with F : ew E1 19 = _ |- _ => rewrite F end.
  rewrite F37.
  destruct (fits (hbase cx) (hwid cx)); vm_compute; reflexivity. }
paj_run_to_shc RUNTOP HS HJ GP_sweep; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msF end.
assert (PF : forall x, ms_mem msF x = ms_mem msD x) by nowin HF.
clear HF HFr HG.
(* ---- 0x80e58: GI_sweep ---- *)
assert (PM : forall x, ms_mem msF x = mem2 x) by (intros x; rewrite PF; apply PD).
assert (KD : admKeep cx fp t W3 mem2 (ms_mem msF)) by (apply admKeep_pw; exact PM).
assert (AVF : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem2 a)
  by (intros a; unfold aview, YP09.mbyte, mrestrict; rewrite PM; reflexivity).
assert (KT : admKeep cx fp t W3 (ms_mem ms3) (ms_mem msF))
  by (eapply admKeep_trans; [exact KA | eapply admKeep_trans; [exact KC | exact KD]]).
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Lws & Lst & _).
(* the memory facts of GI_sweep *)
assert (MSV : gsaved cx W3 msF).
{ destruct HSV as (Hra & Hsj). split.
  - eapply (admK_rdword _ _ _ _ _ _ _ _ KT); [intros i Hi; unfold admZ; left; lia | exact Hra].
  - intros j Hj. eapply (admK_rdword _ _ _ _ _ _ _ _ KT); [intros i Hi; unfold admZ; left; lia | exact (Hsj j Hj)]. }
assert (MSH : gshadow cx fp W3 msF GSH_a).
{ intros i Hi. rewrite gsh_a_len in Hi.
  destruct (Nat.eq_dec i 56) as [-> | Hne].
  - rewrite gsh_a_56. change (Z.of_nat 56) with 56. rewrite AVF. exact A56b.
  - rewrite (gsh_a_other i Hi Hne). rewrite (KT (gSH cx fp + Z.of_nat i)).
    + apply HSH. rewrite gsh_tables_len. exact Hi.
    + unfold admZ. right; right; right; left. split; lia. }
assert (MFL : rdword (aview SEGS (w_H W3) (ms_mem msF)) (gF cx fp + 1016) = Some (gFL cx fp)).
{ eapply (admK_rdword _ _ _ _ _ _ _ _ KT); [|exact HFL].
  intros i Hi. unfold admZ. right; right; left. split; lia. }
assert (MIN : garr8 SEGS (mrestrict (w_H W3) (ms_mem msF)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx))).
{ eapply (admK_garr8 _ _ _ _ _ _ _ _ KT); [|exact HIN].
  intros i Hi. rewrite length_map in Hi. unfold admZ, c_n. right; left. lia. }
assert (KSL : forall off v, 0 <= off <= 184 -> gslot cx W3 ms3 off v ->
  rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + off) = Some v).
{ intros off v Ho Hv. unfold gslot in Hv.
  eapply (admK_rdword _ _ _ _ _ _ _ _ KT); [intros i Hi; unfold admZ; left; lia | exact Hv]. }
assert (MAB : if GrantSlotPlan.ok (c_pl cx)
   then gfb cx fp W3 msF GO_A (hbase cx) /\ gfb cx fp W3 msF (GO_A + 1) (hwid cx)
   else gfb cx fp W3 msF GO_A 0 /\ gfb cx fp W3 msF (GO_A + 1) 0).
{ rewrite Eok. unfold gfb, GO_A. rewrite !AVF.
  destruct (fits (hbase cx) (hwid cx)) eqn:Ef.
  - pose proof (proj1 (Seg_admit.fits_spec _ _) Ef) as (Hw & Hb0 & Hbw).
    assert (Hga' : garr8 SEGS (mrestrict (w_H W3) mem2) (gF cx fp + 448) [hbase cx mod 256; hwid cx mod 256])
      by (first [exact Hga | rewrite Ef in Hga; exact Hga]).
    destruct (Hga' 0%nat ltac:(cbn; lia)) as [Hv0 Hr0]. destruct (Hga' 1%nat ltac:(cbn; lia)) as [Hv1 Hr1].
    cbn [nth] in Hv0, Hr0, Hv1, Hr1. change (Z.of_nat 0) with 0 in Hv0. rewrite Z.add_0_r in Hv0.
    change (Z.of_nat 1) with 1 in Hv1.
    rewrite (Z.mod_small (hbase cx) 256) in Hv0 by lia. rewrite (Z.mod_small (hwid cx) 256) in Hv1 by lia.
    split; [apply (aview_of_val_mem1 SEGS); [exact Hv0 | lia]|].
    replace (gF cx fp + (448 + 1)) with (gF cx fp + 448 + 1) by lia.
    apply (aview_of_val_mem1 SEGS); [exact Hv1 | lia].
  - assert (Hga' : garr8 SEGS (mrestrict (w_H W3) mem2) (gF cx fp + 448) [0; 0])
      by (first [exact Hga | rewrite Ef in Hga; exact Hga]).
    destruct (Hga' 0%nat ltac:(cbn; lia)) as [Hv0 Hr0]. destruct (Hga' 1%nat ltac:(cbn; lia)) as [Hv1 Hr1].
    cbn [nth] in Hv0, Hr0, Hv1, Hr1. change (Z.of_nat 0) with 0 in Hv0. rewrite Z.add_0_r in Hv0.
    change (Z.of_nat 1) with 1 in Hv1.
    split; [apply (aview_of_val_mem1 SEGS); [exact Hv0 | lia]|].
    replace (gF cx fp + (448 + 1)) with (gF cx fp + 448 + 1) by lia.
    apply (aview_of_val_mem1 SEGS); [exact Hv1 | lia]. }
pose proof HTAB as (Tin & Tpos & Tlen & Tb).
assert (MTAB : gtab B cx ly3 S3 W3 msF t (GrantSlotPlan.T_end (c_pl cx))).
{ split; [exact Tin|]. split; [exact Tpos|]. split; [exact Tlen|].
  intros i Hi H1 H2 H3. rewrite (KT (t + i)); [exact (Tb i Hi H1 H2 H3)|].
  unfold admZ. right; right; right; right. lia. }
assert (MWAS : gfarr cx fp W3 msF GO_WAS (GrantSlotPlan.ws_end (c_pl cx))).
{ unfold gfarr in *. eapply (admK_garr8 _ _ _ _ _ _ _ _ KT); [|exact HWAS].
  intros i Hi. rewrite length_map, Lws in Hi. unfold admZ, GO_WAS. right; right; left. split; lia. }
assert (MSET : gfarr cx fp W3 msF GO_SET (GrantSlotPlan.st_end (c_pl cx))).
{ unfold gfarr in *. eapply (admK_garr8 _ _ _ _ _ _ _ _ KT); [|exact HSET].
  intros i Hi. rewrite length_map, Lst in Hi. unfold admZ, GO_SET. right; right; left. split; lia. }
destruct SMID as (M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176).
pmkst HS.
eapply HNEXT; [exact HB | exact HJ | exact HFR | exact HMO |].
unfold GI_sweep. exists t.
split.
{ unfold ge_body, gregs.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [ split; [regval HS|]; split; [regval HS|]; split; [regval HS|];
           split; [rewrite Hgp0; regval HS | rewrite Htp0; regval HS] |].
  split; [exact MSV|]. split; [exact MSH|]. split; [exact MFL|]. split; [exact gsh_a_len|]. exact MIN. }
split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact HCN|].
unfold GO_A, GO_RAW.
split; [regval HS|]. split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
split; [regval HS|]. split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
split.
{ regsv HS. cbn [sv_denot]. repeat match goal with F : ew E1 19 = _ |- _ => rewrite F end.
  rewrite Eok. destruct (fits (hbase cx) (hwid cx)); apply bv_eq; vm_compute; reflexivity. }
split.
{ regsv HS. rewrite at_denot_off0, F37, Eok. reflexivity. }
split; [exact MAB|].
unfold gslot. cbn [ms_mem mkst].
split; [exact (KSL 88 _ ltac:(lia) S88)|]. split; [exact (KSL 120 _ ltac:(lia) S120)|].
split; [exact (KSL 64 _ ltac:(lia) S64)|]. split; [exact (KSL 96 _ ltac:(lia) S96)|].
split.
{ unfold gslots_late, gslots_mid, gslot. cbn [ms_mem mkst].
  repeat match goal with |- _ /\ _ => split end; apply KSL; first [lia | assumption]. }
split; [exact MTAB|]. split; [exact MWAS|]. split; [exact MSET|]. split; [exact HREL | exact HI1].
Qed.

End c.
End b.
End a.
