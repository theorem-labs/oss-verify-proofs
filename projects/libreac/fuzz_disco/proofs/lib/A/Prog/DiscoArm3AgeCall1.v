(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module names changed; 599 of its 645 lines of code are new or changed and 192 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableAge CheckTable.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoRo DiscoArm3 DiscoArm3AgeSt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c reac_disco_table_age_c slot_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac a3c_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Lemma a3c_dsh_in_hi : forall o k c, (dobj_off o + dobj_size o + 7) / 8 = c -> c <= k -> dsh_in o k = false.
Proof. intros o k c Hc H. unfold dsh_in. apply andb_false_iff. right. apply Z.ltb_ge. rewrite Hc. exact H. Qed.

Lemma a3c_dsh_loop_T : forall j, 270 <= j < 320 -> dsh_loop j = 0.
Proof.
intros j Hj. unfold dsh_loop, dsh, dobjs. cbn [dsh_look].
rewrite (a3c_dsh_in_hi OCUR j 22 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OO j 192 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OUSED j 212 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OMAC j 219 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi ONM j 227 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OTOK j 235 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi ODISP j 246 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OWID j 253 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OAGE j 261 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OOUR j 267 ltac:(vm_compute; reflexivity) ltac:(lia)).
unfold dsh_in, dsh_live. cbn [dobj_off dobj_size live_loop].
replace ((2160 + 400 + 7) / 8) with 320 by (vm_compute; reflexivity).
replace ((2160 + 400) / 8) with 320 by (vm_compute; reflexivity).
replace (2160 / 8) with 270 by (vm_compute; reflexivity).
rewrite (proj2 (Z.leb_le 270 j) ltac:(lia)), (proj2 (Z.ltb_lt j 320) ltac:(lia)).
cbn [andb]. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma a3c_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma a3c_dE : forall (cx : dcx) E j ws, d_E cx E -> (530 <= j)%nat -> d_E cx (havoc E j ws).
Proof.
intros cx E j ws (H1 & H32 & HI & H60 & H516 & H529) Hj.
split; [|split; [|split; [|split; [|split]]]].
- intros nn r Hr. pose proof (bv_unsigned_in_range 5 r) as Hb. change (bv_modulus 5) with 32 in Hb.
  rewrite ew_havoc_old by lia. exact (H1 nn r Hr).
- rewrite ew_havoc_old by lia. exact H32.
- apply img_env_havoc_hi; [exact HI | unfold A_LIM; lia].
- rewrite ew_havoc_old by (unfold AT_A; lia). exact H60.
- rewrite ew_havoc_old by (unfold AT_F; lia). exact H516.
- rewrite ew_havoc_old by (unfold AT_SH; lia). exact H529.
Qed.

Lemma a3c_regs_ok : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ra : Z),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + ra) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT ra :: atom_regs 532 30) R.
Proof.
intros cx E R ra HEI H1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                             | rewrite H1; symmetry; exact (codeptr_val _ ra HEId) ]).
Qed.

Lemma a3c_chunk_kept : forall E (m m' : word -> option byte) base c,
  YP09.chunk_ok SEGS E m base c ->
  (forall i, 0 <= i < YP09.c_len c -> mbyte SEGS m' (base + YP09.c_off c + i) = mbyte SEGS m (base + YP09.c_off c + i)) ->
  YP09.chunk_ok SEGS E m' base c.
Proof.
intros E m m' base c H Hk i Hi. destruct (H i Hi) as (b & Hb1 & Hb2).
exists b. split; [exact Hb1|]. rewrite (Hk i Hi). exact Hb2.
Qed.

Lemma a3c_shgeo : forall (cx : dcx),
  4096 <= d_FB cx -> d_FB cx + 4096 <= alloc_ceiling -> in_app (d_FB cx) 4096 -> d_FB cx mod 32 = 0 ->
  alloc_ceiling + LLVMF_STK <= d_S cx -> d_S cx - MFRAME - 31 <= d_A cx ->
  shadow_addr (d_FB cx) + 512 <= d_A cx - 4176 /\
  (shadow_addr (d_FB cx) + 512 <= d_FB cx \/ d_FB cx + 4096 <= shadow_addr (d_FB cx)).
Proof.
intros cx HF0 HFc HFia HFal Hlo HA.
pose proof asan_consts as (Hac & _).
apply Z.mod_divide in HFal; [|lia]. destruct HFal as (q & Hq).
assert (HD8 : d_FB cx / 8 = 4 * q).
{ rewrite Hq. replace (q * 32) with (4 * q * 8) by lia. apply Z.div_mul. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
unfold shadow_addr, SHADOW_OFF, MFRAME, LLVMF_STK in *. rewrite HD8. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DBTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TAGE : treac_disco_table_age_spec B.
Hypothesis TCHKT : tcheck_table_spec B.

Lemma a3c_tgeo : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_shadow cx dsh_loop W3 mem3 ->
  0 < d_obj cx OT /\ d_obj cx OT mod 8 = 0 /\ d_obj cx OT + 400 <= 2 ^ 63 /\
  amem_range (d_obj cx OT) 400 /\ off_img (d_obj cx OT) 400 /\
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (d_obj cx OT) 400 /\
  shadow_hull_vis (aview SEGS (w_H W3) mem3) (d_obj cx OT) 400.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HC HSH.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (Hac & _).
apply Z.mod_divide in HFal; [|lia]. destruct HFal as (q & Hq).
assert (HD8 : d_FB cx / 8 = 4 * q).
{ rewrite Hq. replace (q * 32) with (4 * q * 8) by lia. apply Z.div_mul. lia. }
assert (HT : d_obj cx OT = d_FB cx + 2160) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFo.
split; [lia|]. split.
{ rewrite HT, Hq. replace (q * 32 + 2160) with ((4 * q + 270) * 8) by lia. apply Z_mod_mult. }
split; [lia|]. split.
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
assert (E1 : shadow_addr (d_obj cx OT) = shadow_addr (d_FB cx) + 270).
{ unfold shadow_addr. rewrite HD8, HT, Hq. replace (q * 32 + 2160) with ((4 * q + 270) * 8) by lia.
  rewrite Z.div_mul by lia. lia. }
assert (E2 : shadow_addr (d_obj cx OT + 400 - 1) = shadow_addr (d_FB cx) + 319).
{ unfold shadow_addr. rewrite HD8, HT, Hq.
  replace (q * 32 + 2160 + 400 - 1) with ((4 * q + 319) * 8 + 7) by lia.
  rewrite Z.div_add_l by lia. replace (7 / 8) with 0 by (vm_compute; reflexivity). lia. }
split.
{ intros x Hx. exists 0. unfold shadow_of_addr.
  assert (Hkk : SHADOW_OFF + x / 8 = shadow_addr (d_FB cx) + (x / 8 - d_FB cx / 8)).
  { unfold shadow_addr. lia. }
  assert (Hb : 270 <= x / 8 - d_FB cx / 8 < 320).
  { rewrite HD8. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
    rewrite HT, Hq in Hx. lia. }
  rewrite Hkk. split.
  - rewrite (HSH (x / 8 - d_FB cx / 8) ltac:(unfold DFRAME_SH; lia)). f_equal. apply a3c_dsh_loop_T. exact Hb.
  - unfold saddr_ok. left. reflexivity. }
intros s Hs. rewrite E1, E2 in Hs.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + 270) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + 270) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + 319) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + 319) 8 ltac:(lia)) as M2.
assert (Hkk : 0 <= s - shadow_addr (d_FB cx) < DFRAME_SH) by (unfold DFRAME_SH; lia).
replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
rewrite (HSH (s - shadow_addr (d_FB cx)) Hkk).
discriminate.
Qed.

Theorem c_age : c_age_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 W c HP0.
destruct HP0 as (HFROM & HST).
unfold a3_st, d_at in HST.
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R1v & R10v & R11v & R22v & HRA) & (HSP1 & HT0) & HSP0 & HBODY).
unfold w64 in R1v, R10v, R11v, R22v.
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (Tb & Gb & Lkb & Hb & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCANF & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HIMG as HROD.
pose proof HT0 as (HlenT0 & HokT0 & HgT0).
pose proof HSP1 as ((H232 & H344) & H224 & H248).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof asan_consts as (Hac & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (a3c_shgeo cx GF4096 GFceil GFapp GF32 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia)) as (SHA & SHB).
pose proof (a3c_tgeo cx ly3 S3 W mem3 md3 k HCTX HSHD) as (GT0 & GT8 & GT63 & GTmr & GToff & GTra & GThull).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
pose proof (pa_val_range A_TEXT) as PBR. pose proof pa_B_ok as (PB0 & PB1 & _).
assert (HOFFW : spZ regs <= d_obj cx OT \/ d_obj cx OT + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK).
{ pose proof HJ as (_ & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof HSTKOK as (_ & _ & Hceil' & Hslo' & Hshi' & _).
  pose proof (HSTKF (d_obj cx OT) ltac:(unfold d_obj, dobj_off, DFRAME_SIZE; lia)) as SF1.
  pose proof (HSTKF (d_obj cx OT + 399) ltac:(unfold d_obj, dobj_off, DFRAME_SIZE; lia)) as SF2.
  unfold REAC_DISCO_TABLE_AGE_STK, ESTACK, LLVMF_STK in *. rewrite SpR. lia. }
eapply SRr_mono.
{ apply (TAGE fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k regs (d_obj cx OT) now T0 HJ).
  - exact HROD.
  - rewrite R1v. apply ret_ok_codeptr_v; [unfold P_AGE_RA; lia | reflexivity].
  - unfold raZ. rewrite R1v. rewrite unsigned_lit_small by (unfold P_AGE_RA; lia). unfold P_AGE_RA; lia.
  - exact Rgp.
  - exact Rtp.
  - exact R10v.
  - exact R11v.
  - exact Hnow.
  - rewrite SpR. pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. rewrite GA32 in DA.
    replace (d_A cx) with ((2 * (d_A cx / 32)) * 16) by lia. apply Z_mod_mult.
  - rewrite SpR. unfold REAC_DISCO_TABLE_AGE_STK, ESTACK, LLVMF_STK. lia.
  - rewrite SpR. lia.
  - exact GT0.
  - exact GT8.
  - exact GT63.
  - exact GTmr.
  - exact HOFFW.
  - intros a Ha. apply HAWRF. unfold d_obj, dobj_off, dobj_size, DFRAME_SIZE in *. lia.
  - exact GTra.
  - exact GThull.
  - exact HlenT0.
  - exact HokT0.
  - exact HgT0. }
cbv beta. intros W2 c2 HW2 Hpost.
unfold treac_disco_table_age_post in Hpost.
destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & T1 & removed & -> & HJ4 & HPres & Ha0' & HFR4' & HPerm & HKept &
  HWeq & HKZ & Hg1 & Hmodel & Hpostm).
subst W2.
assert (KZ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_obj cx OT <= a < d_obj cx OT + 400) ->
  ~ (d_A cx - REAC_DISCO_TABLE_AGE_STK <= a < d_A cx) -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hta Hwa. pose proof (HKZ (Z_to_bv 64 a)) as HK.
  rewrite unsigned_lit_small in HK by lia. rewrite SpR in HK. exact (HK Hta Hwa). }
assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HFR4'; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KZ; unfold REAC_DISCO_TABLE_AGE_STK, ESTACK, d_obj, dobj_off in *; lia. }
assert (KF : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OT <= a < d_obj cx OT + 400) ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hta. apply KZ; unfold REAC_DISCO_TABLE_AGE_STK, ESTACK in *; lia. }
assert (KS : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KZ; unfold REAC_DISCO_TABLE_AGE_STK, ESTACK, d_obj, dobj_off, shadow_addr, SHADOW_OFF in *; lia. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E AF_reac_disco_table_age
  (SLit 0 :: SOff A_TEXT P_AGE_RA :: atom_regs 532 30) (map (getr regs) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (a3c_regs_ok cx E regs P_AGE_RA HEIE R1v)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
unfold ss_d in HS1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr regs) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W) mem4) HPres [0;1;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (a3c_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KS. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia. }
specialize (HS2 HQ). clear HQ.
set (E2 := havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)) in HS2.
assert (AGd : forall m, (m < 530)%nat -> ew E2 m = ew E m).
{ intros m Hm. unfold E2. rewrite ew_havoc_old by lia. apply d_env_old. unfold AT_FL. lia. }
assert (E2F : bv_unsigned (ew E2 516) = d_FB cx).
{ rewrite (AGd 516%nat ltac:(lia)), EF. unfold w64. apply unsigned_lit_small. lia. }
assert (E2FL : ew E2 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))).
{ unfold E2. rewrite ew_havoc_old by (unfold AT_FL; lia). apply d_env_fl. }
assert (HEI2 : img_env VAL A_LIM E2).
{ unfold E2. apply img_env_havoc_hi; [|unfold A_LIM; lia].
  apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]. }
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HREG))) as R3.
unfold region_ok in R3. cbv zeta in R3.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in R3.
destruct R3 as (_ & _ & _ & R3c).
change AT_F with 516%nat in R3c. rewrite EF in R3c. unfold w64 in R3c. rewrite unsigned_lit_small in R3c by lia.
assert (HFV : val_mem SEGS (rd W mem3) (d_FB cx + 4096 - 8) 8 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))).
{ change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFLAG. exact (val_mem_of_rdword SEGS (w_H W) mem3 _ _ HFLAG). }
pose proof (rdword_aview_range SEGS (w_H W) mem3 _ _ HFLAG) as HFLr.
assert (HFREG : region_ok SEGS E2 (rd W mem4)
  (YP09.mkRegion (Some AT_F) 0 4096 0 0 dfhdr_chunks)).
{ unfold region_ok. cbv zeta.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  change AT_F with 516%nat. rewrite E2F. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold dfhdr_chunks.
  pose proof (Forall_inv R3c) as C0. apply Forall_inv_tail in R3c.
  pose proof (Forall_inv R3c) as C8. apply Forall_inv_tail in R3c.
  pose proof (Forall_inv R3c) as C16.
  pose proof (img_env_atomP E (A_OBJ 2) HEIE ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as EO2.
  pose proof (img_env_atomP E (A_OBJ 3) HEIE ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as EO3.
  pose proof (pa_val_range (A_OBJ 2)) as RO2. pose proof (pa_val_range (A_OBJ 3)) as RO3.
  pose proof (val_of_chunk_ok SEGS E _ (d_FB cx) 0 8%N (SLit MAGIC_LIVE) MAGIC_LIVE C0
    ltac:(reflexivity) ltac:(cbn [Z.of_N]; unfold MAGIC_LIVE; lia) ltac:(cbn [Z.of_N]; lia)) as V0.
  pose proof (val_of_chunk_ok SEGS E _ (d_FB cx) 8 8%N (SOff (A_OBJ 2) 0) (VAL (A_OBJ 2)) C8
    ltac:(cbn [sv_denot]; rewrite EO2, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V8.
  pose proof (val_of_chunk_ok SEGS E _ (d_FB cx) 16 8%N (SOff (A_OBJ 3) 0) (VAL (A_OBJ 3)) C16
    ltac:(cbn [sv_denot]; rewrite EO3, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as V16.
  cbn [N.to_nat] in V0, V8, V16.
  apply Forall_cons.
  { apply (chunk_ok_val SEGS E2 _ (d_FB cx) 0 8%N (SLit MAGIC_LIVE) MAGIC_LIVE);
    [reflexivity | cbn [Z.of_N]; unfold MAGIC_LIVE; lia | cbn [Z.of_N]; lia |].
    cbn [N.to_nat]. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact V0].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KF; unfold d_obj, dobj_off; lia. }
  apply Forall_cons.
  { apply (chunk_ok_val SEGS E2 _ (d_FB cx) 8 8%N (SOff (A_OBJ 2) 0) (VAL (A_OBJ 2)));
    [cbn [sv_denot]; rewrite (img_env_atomP E2 (A_OBJ 2) HEI2 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), unsigned_lit_small, Z.add_0_r by lia; reflexivity
    | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
    cbn [N.to_nat]. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact V8].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KF; unfold d_obj, dobj_off; lia. }
  apply Forall_cons.
  { apply (chunk_ok_val SEGS E2 _ (d_FB cx) 16 8%N (SOff (A_OBJ 3) 0) (VAL (A_OBJ 3)));
    [cbn [sv_denot]; rewrite (img_env_atomP E2 (A_OBJ 3) HEI2 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), unsigned_lit_small, Z.add_0_r by lia; reflexivity
    | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
    cbn [N.to_nat]. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact V16].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KF; unfold d_obj, dobj_off; lia. }
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E2 _ (d_FB cx) 4088 8%N (SOff AT_FL 0) (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)));
  [cbn [sv_denot]; rewrite E2FL, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn [Z.of_N]; change (8 * 8) with 64; exact HFLr | cbn [Z.of_N]; lia |].
  cbn [N.to_nat]. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4);
  [| replace (d_FB cx + 4088) with (d_FB cx + 4096 - 8) by lia; exact HFV].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KF; unfold d_obj, dobj_off; lia. }
assert (U2 : base_val E2 (Some 2%nat) = d_S cx).
{ cbn [base_val]. rewrite (AGd 2%nat ltac:(lia)). exact ES2. }
assert (U60 : base_val E2 (Some 60%nat) = d_A cx).
{ cbn [base_val]. rewrite (AGd 60%nat ltac:(lia)), EA. unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : base_val E2 (Some 529%nat) = shadow_addr (d_FB cx)).
{ cbn [base_val]. rewrite (AGd 529%nat ltac:(lia)), ESH. unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (U516 : base_val E2 (Some AT_F) = d_FB cx) by (cbn [base_val]; exact E2F).
pose proof (st_ok_pi_add_region E2 _ _ (YP09.mkRegion (Some AT_F) 0 4096 0 0 dfhdr_chunks) HS2
  ltac:(vm_compute; reflexivity) HFREG
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
    rewrite U516, U2, U60, U529; unfold LLVMF_STK, MFRAME in *; repeat split; lia)) as HS3.
clear HS2. rename HS3 into HS2.
rewrite <- restrict_mkst_fx in HS2.
assert (HE2d : d_E cx E2) by (unfold E2; apply a3c_dE; [apply d_E_env; exact HE | lia]).
assert (H216' : val_mem SEGS (rd W mem4) (d_A cx + 216) 8 h).
{ eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact H216].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
assert (H152' : val_mem SEGS (rd W mem4) (d_A cx + 152) 8 (h + 440)).
{ eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact H152].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
pose proof (DLAND LAWS FFL fq cx h dsh_loop ly4 S4 W md4 k _ _
  (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + P_AGE_RA)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2d E2FL HS2 ltac:(vm_compute; reflexivity) H216' H152') as (HFRM4 & HSHD4).
pose proof Hpostm as (HlenT1 & Hrem & Hrem2 & HnT1 & _ & _ & HokT1 & _).
assert (HBODY4 : d_body B cx h n [] dsh_loop ly4 S4 W mem4).
{ apply (DBTOBS LAWS cx h n [] dsh_loop dsh_loop ly3 S3 W mem3 ly4 S4 W mem4 md4 k
    (d_A cx - REAC_DISCO_TABLE_AGE_STK) (d_A cx) [OT]
    (fun a => (d_A cx - REAC_DISCO_TABLE_AGE_STK <= a < d_A cx) \/ d_objr cx OT a)
    HBODY (conj HBASE HJ4)
    ltac:(unfold REAC_DISCO_TABLE_AGE_STK, ESTACK, LLVMF_STK in *; lia) ltac:(lia)).
  - intros a [Hl | Hr]; [left; exact Hl | right; left; apply Exists_cons_hd; exact Hr].
  - intros a Ha Hna. apply KZ; [exact Ha | intros Ht; apply Hna; right; exact Ht | intros Hw; apply Hna; left; exact Hw].
  - apply Forall_cons; [|apply Forall_nil]. cbn [d_obj_new]. exists T1.
    split; [exact HlenT1|]. split; [exact Hg1 | exact HokT1].
  - exact HPerm.
  - exact HFRM4.
  - exact HSHD4. }
assert (P2 : getr regs4 2 = getr regs 2) by exact (HPres 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs4 3 = getr regs 3) by exact (HPres 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs4 4 = getr regs 4) by exact (HPres 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs4 8 = getr regs 8) by exact (HPres 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs4 9 = getr regs 9) by exact (HPres 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs4 18 = getr regs 18) by exact (HPres 18 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs4 20 = getr regs 20) by exact (HPres 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs4 21 = getr regs 21) by exact (HPres 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs4 22 = getr regs 22) by exact (HPres 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs4 23 = getr regs 23) by exact (HPres 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs4 24 = getr regs 24) by exact (HPres 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs4 25 = getr regs 25) by exact (HPres 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs4 26 = getr regs 26) by exact (HPres 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs4 27 = getr regs 27) by exact (HPres 27 ltac:(unfold acallee_saved; lia)).
assert (KV : forall off v, 0 <= off <= 352 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
exists T1, removed.
split; [exact HFROM|].
unfold a3_st, d_at.
exists fq, ly4, S4, regs4, mem4, md4, k, acc.
split; [unfold cfg_at, w64; rewrite R1v; reflexivity|].
split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|].
split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P18; exact Rs2|]. split; [rewrite P20; exact Rs4|].
  rewrite P25; exact Rs9. }
split.
{ split; [exact Ha0'|].
  split.
  { rewrite P22, R22v. unfold a3_stale. rewrite <- Hrem. reflexivity. }
  pose proof HRA as (A21 & A23 & A24 & A26 & A27).
  split; [rewrite P21; exact A21|]. split; [rewrite P23; exact A23|]. split; [rewrite P24; exact A24|].
  split; [rewrite P26; exact A26|]. rewrite P27; exact A27. }
split.
{ split.
  { split; [split; [apply KV; [lia | exact H232] | apply KV; [lia | exact H344]]|].
    split; [apply KV; [lia | exact H224] | apply KV; [lia | exact H248]]. }
  split; [exact Hmodel|]. split; [exact Hpostm | exact Hg1]. }
split.
{ split; [apply KV; [lia | exact H232] | apply KV; [lia | exact H344]]. }
exact HBODY4.
Qed.

Theorem c_chk : c_chk_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 removed W c HP0.
destruct HP0 as (HFROM & HST).
unfold a3_st, d_at in HST.
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R1v & R10v & R19v & R22v & HRA) & (HSP1 & HAGED) & HSP0 & HBODY).
unfold w64 in R1v, R10v, R19v, R22v.
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (Tb & Gb & Lkb & Hb & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCANF & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HIMG as HROD.
pose proof HAGED as (Hmodel & Hpostm & Hg1).
pose proof Hpostm as (HlenT1 & Hrem & Hrem2 & HnT1 & _ & _ & HokT1 & _).
pose proof HokT1 as (HT1a & HT1b & HT1c & _).
pose proof HSP1 as ((H232 & H344) & H224 & H248).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof asan_consts as (Hac & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (a3c_tgeo cx ly3 S3 W mem3 md3 k HCTX HSHD) as (GT0 & GT8 & GT63 & GTmr & GToff & GTra & GThull).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
pose proof (pa_val_range A_TEXT) as PBR. pose proof pa_B_ok as (PB0 & PB1 & _).
assert (HOFFW : d_obj cx OT + 400 <= spZ regs - TCHECK_TABLE_STK \/ spZ regs <= d_obj cx OT).
{ pose proof HJ as (_ & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKOK & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof HSTKOK as (_ & _ & Hceil' & Hslo' & Hshi' & _).
  pose proof (HSTKF (d_obj cx OT) ltac:(unfold d_obj, dobj_off, DFRAME_SIZE; lia)) as SF1.
  pose proof (HSTKF (d_obj cx OT + 399) ltac:(unfold d_obj, dobj_off, DFRAME_SIZE; lia)) as SF2.
  unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK in *. rewrite SpR. lia. }
assert (HAFN : afn_pre SEGS B TCHECK_TABLE_STK ly3 S3 W (regupd regs 8 (Z_to_bv 64 0)) mem3 md3 []).
{ eapply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k (regupd regs 8 (Z_to_bv 64 0)) TCHECK_TABLE_STK
    (d_A cx - d_S cx) [] HJ).
  - unfold spZ. rewrite getr_other by a3c_bvne. fold (spZ regs). rewrite SpR. lia.
  - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
    rewrite GA32 in DA. rewrite GS16 in DS.
    replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold TCHECK_TABLE_STK, ESTACK. lia.
  - unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK. lia.
  - rewrite getr_other by a3c_bvne. rewrite R1v. apply ret_ok_codeptr_v; [unfold P_CHK_RA; lia | reflexivity].
  - unfold raZ. rewrite getr_other by a3c_bvne. rewrite R1v.
    rewrite unsigned_lit_small by (unfold P_CHK_RA; lia). unfold P_CHK_RA; lia.
  - rewrite getr_other by a3c_bvne. exact Rgp.
  - rewrite getr_other by a3c_bvne. exact Rtp.
  - left. split; [|reflexivity]. left. unfold s0Z. rewrite getr_same by a3c_bvne.
    rewrite unsigned_lit_small by lia. lia. }
assert (SpR8 : spZ (regupd regs 8 (Z_to_bv 64 0)) = d_A cx)
  by (unfold spZ; rewrite getr_other by a3c_bvne; fold (spZ regs); exact SpR).
eapply SRr_mono.
{ apply (TCHKT fq ly3 S3 W regs mem3 md3 [] (d_obj cx OT) T1 HAFN).
  - exact HROD.
  - exact R10v.
  - exact GT0.
  - exact GT8.
  - lia.
  - exact HlenT1.
  - exact Hg1.
  - exact GTmr.
  - exact GTra.
  - exact GThull.
  - rewrite SpR. rewrite SpR in HOFFW. exact HOFFW.
  - exact GToff.
  - exact HT1a.
  - exact HT1b.
  - exact HT1c. }
cbv beta. intros W2 c2 HW2 Hpost.
unfold tcheck_table_post, apost_base in Hpost.
destruct Hpost as (fq4 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hfreg4 & Hcsr4 & HJc & HPres & HPerm & HKeep).
pose proof (ajournal_sub SEGS B LAWS pa_segs_low LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k TCHECK_TABLE_STK (spZ regs) [] [] ly4 S4 W2 mem4 md4 0 HJ HJc
  ltac:(rewrite SpR; unfold LLVMF_STK, TCHECK_TABLE_STK, ESTACK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ4.
cbn [app] in HJ4. rewrite Z.add_0_r in HJ4.
pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _).
assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply HKeep; [lia | rewrite SpR; lia]. }
assert (KB : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply HKeep; [lia | rewrite SpR; unfold TCHECK_TABLE_STK, ESTACK; lia]. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E AF_check_table
  (SLit 0 :: SOff A_TEXT P_CHK_RA :: atom_regs 532 30) (map (getr regs) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (a3c_regs_ok cx E regs P_CHK_RA HEIE R1v)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
unfold ss_d in HS1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr regs) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W2) mem4) HPres [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EF. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KB. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
    + intros a Ha. apply GFpres4. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KB. unfold shadow_addr, SHADOW_OFF in *.
      change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2d : d_E cx (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply a3c_dE; [apply d_E_env; exact HE | lia]).
assert (HFL2 : ew (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (H216' : val_mem SEGS (rd W2 mem4) (d_A cx + 216) 8 h).
{ eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact H216].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
assert (H152' : val_mem SEGS (rd W2 mem4) (d_A cx + 152) 8 (h + 440)).
{ eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact H152].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
pose proof (DLAND LAWS FFL fq cx h dsh_loop ly4 S4 W2 md4 k _ _
  (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + P_CHK_RA)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2d HFL2 HS2 ltac:(vm_compute; reflexivity) H216' H152') as (HFRM4 & HSHD4).
pose proof (DBPC LAWS DROH DCAN cx h n [] dsh_loop dsh_loop ly3 S3 W mem3 md3 ly4 S4 W2 mem4 md4 k TCHECK_TABLE_STK
  (spZ regs) [] 0 HBODY (conj HBASE HJ4) HJc
  ltac:(rewrite SpR; unfold LLVMF_STK, TCHECK_TABLE_STK, ESTACK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
  ltac:(intros (a & Ha & _); exfalso; exact (inFP_nil a Ha))
  HPerm HFRM4 HSHD4) as HBODY4.
assert (P2 : getr regs4 2 = getr regs 2) by exact (HPres 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs4 3 = getr regs 3) by exact (HPres 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs4 4 = getr regs 4) by exact (HPres 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs4 8 = getr regs 8) by exact (HPres 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs4 9 = getr regs 9) by exact (HPres 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs4 18 = getr regs 18) by exact (HPres 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs4 19 = getr regs 19) by exact (HPres 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs4 20 = getr regs 20) by exact (HPres 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs4 21 = getr regs 21) by exact (HPres 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs4 22 = getr regs 22) by exact (HPres 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs4 23 = getr regs 23) by exact (HPres 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs4 24 = getr regs 24) by exact (HPres 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs4 25 = getr regs 25) by exact (HPres 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs4 26 = getr regs 26) by exact (HPres 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs4 27 = getr regs 27) by exact (HPres 27 ltac:(unfold acallee_saved; lia)).
assert (KV : forall off v, 0 <= off <= 352 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W2 mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
split.
{ pose proof HFROM as (HA3 & HWle & HlenT0 & HFQ).
  split; [exact HA3|]. split; [|split; [exact HlenT0 | exact HFQ]].
  pose proof HJc as (_ & _ & _ & Hwle2 & _). eapply wle_trans; [exact HWle | exact Hwle2]. }
unfold a3_st, d_at.
exists fq4, ly4, S4, regs4, mem4, md4, k, acc.
split; [unfold cfg_at, w64; rewrite R1v; reflexivity|].
split; [destruct Hcsr4 as [Hcs | Hcs]; [rewrite Hcs; exact Hfrm0 | exact Hcs]|].
split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|].
split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P18; exact Rs2|]. split; [rewrite P20; exact Rs4|].
  rewrite P25; exact Rs9. }
split.
{ split; [rewrite P19; exact R19v|]. split; [rewrite P22; exact R22v|].
  pose proof HRA as (A21 & A23 & A24 & A26 & A27).
  split; [rewrite P21; exact A21|]. split; [rewrite P23; exact A23|]. split; [rewrite P24; exact A24|].
  split; [rewrite P26; exact A26|]. rewrite P27; exact A27. }
split.
{ split.
  { split; [split; [apply KV; [lia | exact H232] | apply KV; [lia | exact H344]]|].
    split; [apply KV; [lia | exact H224] | apply KV; [lia | exact H248]]. }
  split; [exact Hmodel|]. split; [exact Hpostm|].
  eapply (garr8_frame SEGS (rd W mem3) (rd W2 mem4)); [exact Hg1|].
  intros a Ha. rewrite length_map, HlenT1 in Ha. apply (mbyte_of_aview SEGS). apply KB.
  unfold d_obj, dobj_off in *. lia. }
split.
{ split; [apply KV; [lia | exact H232] | apply KV; [lia | exact H344]]. }
exact HBODY4.
Qed.

End h.
End f.
End d.
