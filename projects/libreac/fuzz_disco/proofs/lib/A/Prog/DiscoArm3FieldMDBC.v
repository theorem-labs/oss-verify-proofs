(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 501 of its 566 lines of code are new or changed and 1213 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeLeft.v, with its module paths and module names changed; 301 of its 341 lines of code are new or changed and 526 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YP03 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require jtok_is_c printf_facts_c disco_jscalar_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoArm3FieldCall DiscoArm3FieldMDFacts DiscoArm3FieldMDBKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoArm3FieldMDKit.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma mdbc_rdword_kept : forall (rd1 rd2 : Z -> option Z) a, (forall k, 0 <= k < 8 -> rd2 (a + k) = rd1 (a + k)) ->
  rdword rd2 a = rdword rd1 a.
Proof.
  intros rd1 rd2 a H. unfold rdword.
  assert (H0 : rd2 a = rd1 a) by (rewrite <- (Z.add_0_r a); apply H; lia).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma mdbc_mbyte_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a,
  d_kept P W m W' m' -> 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS (rd W' m') a = mbyte SEGS (rd W m) a.
Proof.
  intros P W m W' m' a HK Ha HP. pose proof (HK a Ha HP) as E. unfold aview in E.
  destruct (mbyte SEGS (rd W' m') a) as [b1|] eqn:E1; destruct (mbyte SEGS (rd W m) a) as [b2|] eqn:E2;
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma mdbc_val_mem_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a nb v,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat nb -> ~ P x) ->
  val_mem SEGS (rd W m) a nb v -> val_mem SEGS (rd W' m') a nb v.
Proof.
  intros P W m W' m' a nb v HK H0 H1 HP Hv k Hk.
  rewrite (mdbc_mbyte_kept P W m W' m'); [exact (Hv k Hk) | exact HK | lia |].
  apply HP. lia.
Qed.

Lemma mdbc_garr8_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a l,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length l) -> ~ P x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
  intros P W m W' m' a l HK H0 H1 HP Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (mdbc_val_mem_kept P W m W' m'); [exact HK | lia | lia | | exact Hv].
  intros x Hx. apply HP. lia.
Qed.

Lemma mdbc_region_ok_kept : forall (P : Z -> Prop) (W W' : world SEGS) (m m' : word -> option byte) (E : env)
    (r : YP09.region) lo hi,
  d_kept P W m W' m' ->
  region_ok SEGS E (rd W m) r ->
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) (YP09.r_chunks r) = true ->
  (forall a, base_val E (YP09.r_base r) + lo <= a < base_val E (YP09.r_base r) + hi -> 0 <= a < 2 ^ 64 /\ ~ P a) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> apresent (w_H W') m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E (rd W' m') r.
Proof.
  intros P W W' m m' E r lo hi HK HR Hb Hout Hw. destruct HR as (H0 & H1 & _ & HC).
  split; [exact H0|]. split; [exact H1|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply Hw. exact Ho.
  - rewrite Forall_forall in HC |- *. intros c Hc ii Hii. destruct (HC c Hc ii Hii) as (b & Hb1 & Hb2).
    exists b. split; [exact Hb1|].
    pose proof (proj1 (forallb_forall _ _) Hb c Hc) as Hcb. apply andb_prop in Hcb as [Hl Hh].
    apply Z.leb_le in Hl. apply Z.leb_le in Hh.
    destruct (Hout (base_val E (YP09.r_base r) + YP09.c_off c + ii) ltac:(lia)) as [Ha HPa].
    rewrite (mdbc_mbyte_kept P W m W' m' _ HK Ha HPa). exact Hb2.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis MCRO : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Theorem a3f_mdbC : forall p, 0 <= p < 8 -> mdbC_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
unfold mdb_c2, a3f_st, d_arm_at_pf, d_at in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R1 & R10 & R11 & R12) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & ((HSL & H392 & H408 & HUSED) & HAGE)) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HSL as (Hpc & H368 & H336).
pose proof HBODY as (TT & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo, GSTK.
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
assert (HTK : TJTOK_IS_STK = 8240) by reflexivity.
assert (HOO0 : d_obj cx OO = d_FB cx + 240) by reflexivity.
assert (HOA0 : d_obj cx OAGE = d_FB cx + 2064) by reflexivity.
assert (HOT0 : d_obj cx OT = d_FB cx + 2160) by reflexivity.
assert (HOU0 : d_obj cx OUSED = d_FB cx + 1664) by reflexivity.
pose proof HTAB as ((rem & _ & HAP) & HgOT).
pose proof HAP as (LT1 & _ & _ & _ & _ & _ & TOK & _).
destruct (a3f_count T1 now count os LT1 TOK Hnow HJR) as (Ec & Hc8 & Los & Lo6 & HINB & _ & _).
pose proof (a3f_obj T1 now count os p LT1 TOK Hnow HJR Hpc) as HOBJM. cbv zeta in HOBJM.
destruct HOBJM as (_ & _ & _ & _ & _ & HAJ).
change (disco_json_text.e_last_seen (reac_disco_table_json_c.tj_entry T1 p)) with (disco_table_c.last_of T1 p) in HAJ.
change (disco_json_text.age_of now (disco_table_c.last_of T1 p)) with (a3f_age T1 now p) in HAJ.
assert (HLS : 0 <= disco_table_c.last_of T1 p < 2 ^ 64).
{ pose proof (mdf_u_at_range T1 (48 * p + 40) 8) as HU. change (8 * Z.of_nat 8) with 64 in HU. exact HU. }
pose proof (disco_json_lemmas.age_range now (disco_table_c.last_of T1 p) Hnow HLS) as HAG.
change (disco_json_text.age_of now (disco_table_c.last_of T1 p)) with (a3f_age T1 now p) in HAG.
destruct (disco_json_lemmas.dec_spec (a3f_age T1 now p) ltac:(lia)) as (HDG & _ & _ & HDL0).
pose proof (HDL0 14 ltac:(lia) ltac:(lia)) as HDL. change (Z.to_nat 14) with 14%nat in HDL. clear HDL0.
assert (FT : Forall (fun cc => 0 < cc < 256) (disco_json_text.dec (a3f_age T1 now p))).
{ eapply Forall_impl; [|exact HDG]. intros cc Hcc. unfold disco_json_lemmas.digc in Hcc. lia. }
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & _).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (HbSh & HbHull).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbceil, Hbapp, HbSh, HbHull.
pose proof HBUF as ((Hr2 & Hrc) & HgB).
unfold a3_r in Hr2, Hrc.
assert (HNr : Z.of_nat (length (a3_text T1 now)) + 1 <= Z.max (slot_ser_defs.ser_cap op) 1) by lia.
set (N := Z.max (slot_ser_defs.ser_cap op) 1) in *.
destruct (DiscoArm3FieldMDKit.mdk_obj_tok os count p 5 Los Lo6 Hpc ltac:(lia)) as (Hoe & Ht0 & Ho6).
assert (Hoi : In (nth (Z.to_nat p) os []) os) by (eapply nth_error_In; exact Hoe).
assert (Hti : In (nth 5 (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) (nth (Z.to_nat p) os []))
  by (eapply nth_error_In; exact Ht0).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) HINB _ Hoi) _ Hti) as Hib.
set (t := nth 5 (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) in *.
set (text := disco_json_text.dec (a3f_age T1 now p)) in *.
destruct (DiscoArm3FieldMDKit.mdk_site SEGS (rd W mem3) T1 now count os p 5 (d_obj cx OO) buf
  (d_obj cx OO + 144 * p + 120) 2 vpad text t LT1 TOK Hnow HJR Hpc ltac:(lia) HVP HOO HgB ltac:(lia) ltac:(lia)
  eq_refl ltac:(lia) FT HAJ ltac:(change (Z.of_nat 5) with 5; lia))
  as (J1 & J2 & J3 & F1 & F2 & F3 & Hvp & Hvn & JM & LP & GP & Hp0 & Hp63).
unfold printf_facts_c.pf_bytes in JM, LP, GP, Hp63.
rewrite J3 in JM, GP.
destruct Hib as [Hz | (Hs0 & Hl0 & Hsl)]; [lia|].
unfold disco_jscalar_model.jlen in Hsl.
assert (LTm : length (map (Z_to_bv 8) text) = length text) by apply length_map.
destruct (mdf_frame_x B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k h n (a3_xb buf op) dsh_age 2064 24
  (d_obj cx OAGE) text HCTX HBODY ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DFRAME_SIZE; lia)
  ltac:(lia) ltac:(lia) FT HAGE)
  as (sl & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
destruct (mdf_frame_range B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k h n (a3_xb buf op) dsh_age 240 1296
  (d_obj cx OO + 144 * p + 120) 20 HCTX HBODY ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DFRAME_SIZE; lia)
  ltac:(lia) ltac:(lia) ltac:(lia)) as (VT1 & VT2 & VT3).
assert (QO1 : (d_A cx - d_S cx) mod 16 = 0).
{ pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
  rewrite GA32 in DA. rewrite GS16 in DS.
  replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult. }
assert (QRA : YK0s.ret_ok (getr regs 1)).
{ rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold MDJ_OFF; lia. }
assert (QRZ : 4096 <= raZ regs).
{ unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold MDJ_OFF; lia). unfold MDJ_OFF. lia. }
eapply SRr_mono.
{ refine (aj_jtok_at B LAWS TJTOK fq W regs mem3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k (d_A cx - d_S cx) (d_obj cx OO + 144 * p + 120)
    (d_obj cx OAGE) 2 (disco_json_reader_model.tv_kind t) (buf + snd (fst t)) (snd t) (map (Z_to_bv 8) text) sl
    (map (Z_to_bv 8) text) HJ
    ltac:(rewrite Rsp; lia) QO1 ltac:(lia) ltac:(unfold LLVMF_STK; lia) Rgp Rtp QRA QRZ HIMG
    (mc_cv_ok B W mem3 MCRO MCUN HIMG) R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    F1 F2 F3 Hvp Hvn VT1 VT2 VT3 ltac:(left; rewrite Rsp; lia)
    X1 X2 X3 X4 X5 X6 X7 X8 X9 ltac:(left; rewrite Rsp; lia) _).
  intros _ _.
  split; [reflexivity|].
  split; [exact GP|].
  split; [lia|].
  split; [exact Hp63|].
  split; [apply (amem_range_sub_app buf N); [exact Hbapp | lia | lia | lia | lia]|].
  split; [apply (block_shadow_range _ _ buf N); [exact HbSh | lia | lia]|].
  split.
  { intros Hpos s Hs. apply HbHull.
    pose proof (YCbq.shadow_mono buf (buf + snd (fst t)) ltac:(lia)) as Sm1.
    pose proof (YCbq.shadow_mono (buf + snd (fst t) + Z.of_nat (length (map (Z_to_bv 8) text)) - 1) (buf + N - 1)
      ltac:(lia)) as Sm2.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm1) as Sd1.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm2) as Sd2. lia. }
  left. rewrite Rsp. lia. }
cbv beta. intros W2 c2 HW2 (fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hcsr2 & HJ4 & HJc & HP & HAB & HKP & HRES).
pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _).
assert (HFR4 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly2 S2 W2 mem2 md2 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
unfold LLVMF_STK in GSTK4.
set (Pw := fun a => d_A cx - TJTOK_IS_STK <= a < d_A cx).
assert (HK : d_kept Pw W mem3 W2 mem2).
{ intros a Ha HPa. apply HKP; [exact Ha|]. rewrite Rsp. exact HPa. }
assert (HPlo : forall a, a < alloc_ceiling -> ~ Pw a) by (intros a Ha Hpw; unfold Pw in Hpw; lia).
assert (HPA : forall a, d_A cx <= a -> ~ Pw a) by (intros a Ha Hpw; unfold Pw in Hpw; lia).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
assert (BS : base_val E (Some AT_STK) = d_S cx).
{ cbn [base_val]. rewrite (EE AT_STK 2%bv eq_refl). reflexivity. }
assert (BA : base_val E (Some AT_A) = d_A cx).
{ cbn [base_val]. rewrite E60. unfold w64. apply unsigned_lit_small. lia. }
assert (BF : base_val E (Some AT_F) = d_FB cx).
{ cbn [base_val]. rewrite EF. unfold w64. apply unsigned_lit_small. lia. }
assert (BSH : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
{ cbn [base_val]. rewrite ESH. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (HSHlo : shadow_addr (d_FB cx) + 512 <= alloc_ceiling).
{ pose proof alloc_ceiling_value as (HCm & _). unfold shadow_addr, SHADOW_OFF. lia. }
assert (HSH0 : 0 <= shadow_addr (d_FB cx)) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HFRM4 : d_frame cx h dsh_age W2 mem2).
{ exists E. split; [exact HE|]. split; [|split; [|split]].
  - unfold d_regions in HREG |- *. rewrite !Forall_cons_iff in HREG |- *.
    destruct HREG as (HRS & HRA & HRF & HRH & _).
    split; [|split; [|split; [|split; [|exact (Forall_nil _)]]]].
    + apply (mdbc_region_ok_kept Pw W W2 mem3 mem2 E _ (-104) 0 HK HRS); [vm_compute; reflexivity | |];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BS.
      * intros a Ha. split; [lia | apply HPA; lia].
      * intros o Ho. lia.
    + apply (mdbc_region_ok_kept Pw W W2 mem3 mem2 E _ 0 472 HK HRA); [vm_compute; reflexivity | |];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BA.
      * intros a Ha. split; [lia | apply HPA; lia].
      * intros o Ho. apply GSTK4. lia.
    + apply (mdbc_region_ok_kept Pw W W2 mem3 mem2 E _ 0 24 HK HRF); [vm_compute; reflexivity | |];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BF.
      * intros a Ha. split; [lia | apply HPlo; lia].
      * intros o Ho. apply GFpres4. unfold DFRAME_SIZE in Ho. lia.
    + apply (mdbc_region_ok_kept Pw W W2 mem3 mem2 E _ 0 384 HK HRH); [vm_compute; reflexivity | |];
        unfold fshadow_region; cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BSH.
      * intros a Ha. split; [lia | apply HPlo; lia].
      * intros o Ho. apply GFsh4. unfold DFRAME_SH in Ho. lia.
  - rewrite <- HFLAG. apply mdbc_rdword_kept. intros kk0 Hkk0.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. apply HK; [lia | apply HPlo; lia].
  - apply (mdbc_val_mem_kept Pw W mem3 W2 mem2); [exact HK | lia | lia | intros x Hx; apply HPA; lia | exact H216].
  - apply (mdbc_val_mem_kept Pw W mem3 W2 mem2); [exact HK | lia | lia | intros x Hx; apply HPA; lia | exact H152]. }
assert (HSHD4 : d_shadow cx dsh_age W2 mem2).
{ intros kk0 Hkk0. rewrite <- (HSHD kk0 Hkk0). unfold DFRAME_SH in Hkk0.
  apply HK; [lia | apply HPlo; lia]. }
pose proof (DiscoEntBody.d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n
  (a3_xb buf op) dsh_age dsh_age ly3 S3 W mem3
  ly2 S2 W2 mem2 md2 k (d_A cx - TJTOK_IS_STK) (d_A cx) HBODY (conj HBASE HJ4)
  ltac:(unfold LLVMF_STK; lia) ltac:(lia) HK HAB HFRM4 HSHD4) as HBODY4.
assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr regs 25) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
assert (Q10 : getr regs2 10 = w64 1).
{ destruct HRES as [(_ & Q) | (HM & _)]; [exact Q | exfalso; exact (HM JM)]. }
assert (KV : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) nb v -> val_mem SEGS (rd W2 mem2) (d_A cx + off) nb v).
{ intros off nb v Hoff Hnb Hv. apply (mdbc_val_mem_kept Pw W mem3 W2 mem2); [exact HK | lia | lia | | exact Hv].
  intros y Hy. apply HPA. lia. }
assert (HLo : length (slot_ser_defs.objs_bytes buf vpad os) = (144 * Z.to_nat count)%nat).
{ rewrite (DiscoArm3FieldMDKit.mdk_objs_len _ _ _ HVP Lo6). rewrite Los. reflexivity. }
unfold mdb_c3, a3f_st, d_arm_at_pf, d_at.
split.
{ destruct HFROM as (HA3 & HW0 & HT0 & HEX). split; [exact HA3|].
  split; [eapply wle_trans; [exact HW0 | exact HW2]|]. split; [exact HT0 | exact HEX]. }
exists fq2, ly2, S2, regs2, mem2, md2, k, acc.
split; [unfold cfg_at, w64; rewrite R1; reflexivity|].
split; [destruct Hcsr2 as [Hcs | Hcs]; [rewrite Hcs; assumption | exact Hcs]|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P18; exact Rs2|]. split; [rewrite P20; exact Rs4|].
  rewrite P25; exact Rs9. }
split; [split; [rewrite P26; exact R26 | exact Q10]|].
split.
{ pose proof HSP1 as ((H232 & H344) & H224 & H248).
  split; [split; [split|split]|].
  - apply KV; [lia | cbn; lia | exact H232].
  - apply KV; [lia | cbn; lia | exact H344].
  - apply KV; [lia | cbn; lia | exact H224].
  - apply KV; [lia | cbn; lia | exact H248].
  - split.
    { split; [exact (proj1 HTAB)|].
      apply (mdbc_garr8_kept Pw W mem3 W2 mem2); [exact HK | lia | | | exact HgOT].
      - rewrite length_map, LT1. lia.
      - intros x Hx. rewrite length_map, LT1 in Hx. apply HPlo. lia. }
    split.
    { split; [unfold a3_r; lia|].
      apply (mdbc_garr8_kept Pw W mem3 W2 mem2); [exact HK | lia | | | exact HgB].
      - rewrite length_app. cbn [length]. lia.
      - intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply HPlo. lia. }
    split; [exact HJR|]. split; [exact HVP|].
    split.
    { apply (mdbc_garr8_kept Pw W mem3 W2 mem2); [exact HK | lia | | | exact HOO].
      - rewrite length_map, HLo. lia.
      - intros x Hx. rewrite length_map, HLo in Hx. apply HPlo. lia. }
    split; [split; [lia|]; split; [apply KV; [lia | cbn; lia | exact H368] | apply KV; [lia | cbn; lia | exact H336]]|].
    split; [apply KV; [lia | cbn; lia | exact H392]|].
    split; [apply KV; [lia | cbn; lia | exact H408]|].
    assert (LU : length (a3f_used (p + 1)) = 32%nat) by reflexivity.
    apply (mdbc_garr8_kept Pw W mem3 W2 mem2); [exact HK | lia | | | exact HUSED].
    + rewrite LU. lia.
    + intros x Hx. rewrite LU in Hx. apply HPlo. lia. }
split.
{ pose proof HSP0 as (H232 & H344).
  split; [apply KV; [lia | cbn; lia | exact H232] | apply KV; [lia | cbn; lia | exact H344]]. }
exact HBODY4.
Qed.

End h.
End f.
End d.
