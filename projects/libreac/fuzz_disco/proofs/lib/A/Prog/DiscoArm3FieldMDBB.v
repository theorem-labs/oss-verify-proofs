(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 501 of its 566 lines of code are new or changed and 1213 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeLeft.v, with its module paths and module names changed; 453 of its 517 lines of code are new or changed and 502 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC81 YC88 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt DiscoEntSeat DiscoRo DiscoEntBodyStmt DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoArm3FieldCut DiscoArm3FieldCall DiscoArm3FieldMDBKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma mdbb_parse : pf_parse a3f_fmt_age = Some [Pllu].
Proof. vm_compute. reflexivity. Qed.

Lemma mdbb_text : forall u, pf_text [Pllu] [AU64 u] = Some (pf_udec u).
Proof. intros u. cbn [pf_text option_map]. rewrite app_nil_r. reflexivity. Qed.

Lemma mdbb_last_range : forall (T : list byte) (p : Z), 0 <= disco_table_c.last_of T p < 2 ^ 64.
Proof.
  intros T p. unfold disco_table_c.last_of.
  pose proof (slot_ser_pure.ser_u_at_bound T (48 * p + 40) 8) as H.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H. exact H.
Qed.

Lemma mdbb_age_range : forall (T : list byte) (now p : Z), 0 <= now < 2 ^ 64 ->
  0 <= a3f_age T now p <= 18446744073709.
Proof.
  intros T now p Hnow. unfold a3f_age.
  exact (disco_json_lemmas.age_range now (disco_table_c.last_of T p) Hnow (mdbb_last_range T p)).
Qed.

Lemma mdbb_dec : forall u, 0 <= u <= 18446744073709 -> disco_json_text.dec u = pf_udec u.
Proof.
  intros u Hu. apply tj_lemmas.dec_udec. split; [lia|].
  apply (Z.le_lt_trans _ 18446744073709); [lia | reflexivity].
Qed.

Lemma mdbb_udec_len : forall u, 0 <= u <= 18446744073709 -> (length (pf_udec u) <= 20)%nat.
Proof. intros u Hu. rewrite <- (mdbb_dec u Hu). apply tj_lemmas.dec_len. Qed.

Lemma mdbb_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.

Lemma mdbb_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os -> length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, mdbb_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Lemma mdbb_rdword : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma mdbb_chunk_in : forall r c, In c (YP09.r_chunks r) -> region_wf r = true ->
  YP09.r_lo r <= YP09.c_off c /\ YP09.c_off c + c_len c <= YP09.r_hi r.
Proof.
  intros r c Hin Hwf. unfold region_wf in Hwf. apply andb_prop in Hwf as [_ Hcs].
  pose proof (proj1 (forallb_forall _ _) Hcs c Hin) as X. unfold chunk_inside in X.
  apply andb_prop in X as [X _]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma mdbb_region_tr : forall (E : env) H (m m' : word -> option byte) (r : YP09.region),
  region_ok SEGS E (mrestrict H m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < c_len c ->
     aview SEGS H m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS H m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall a, apresent H m a -> apresent H m' a) ->
  region_ok SEGS E (mrestrict H m') r.
Proof.
  intros E H m m' r (B1 & B2 & Wr & C) Hc Hp. split; [exact B1|]. split; [exact B2|]. split.
  - intros o Ho. apply (writable_kept H m m'); [apply Hp | exact (Wr o Ho)].
  - apply Forall_forall. intros c Hin i Hi. destruct (proj1 (Forall_forall _ _) C c Hin i Hi) as (b & Hb1 & Hb2).
    exists b. split; [exact Hb1|]. rewrite (mbyte_of_aview SEGS H H m m' _ (Hc c i Hin Hi)). exact Hb2.
Qed.

Lemma mdbb_frame_tr : forall (cx : dcx) h shf (W : world SEGS) (m m' : word -> option byte) (K : Z -> Prop),
  d_frame cx h shf W m ->
  (forall a, K a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  (forall a, d_S cx - 104 <= a < d_S cx -> K a) ->
  (forall a, d_A cx <= a < d_A cx + 472 -> K a) ->
  (forall a, d_FB cx <= a < d_FB cx + 24 -> K a) ->
  (forall a, d_FB cx + 4088 <= a < d_FB cx + 4096 -> K a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 -> K a) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 47 ->
  d_frame cx h shf W m'.
Proof.
  intros cx h shf W m m' K (E & HE & HREG & HFLAG & H216 & H152) HK Hp K2 K60 K516 KFL KSH HA HF.
  exists E. split; [exact HE|].
  pose proof HE as (EE & _ & _ & E60 & EF & ESH).
  assert (B2 : base_val E (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (B60 : base_val E (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. unfold w64. apply unsigned_lit_small. lia. }
  assert (B516 : base_val E (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. unfold w64. apply unsigned_lit_small. lia. }
  assert (B529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  unfold d_regions in HREG |- *.
  apply Forall_cons_iff in HREG as [R2 HREG]. apply Forall_cons_iff in HREG as [R60 HREG].
  apply Forall_cons_iff in HREG as [R516 HREG]. apply Forall_cons_iff in HREG as [R529 _].
  split.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    - apply (mdbb_region_tr E (w_H W) m m' _ R2); [|exact Hp]. intros c i Hin Hi. apply HK.
      pose proof (mdbb_chunk_in _ c Hin ltac:(vm_compute; reflexivity)) as Hc.
      cbn [YP09.r_lo YP09.r_hi YP09.r_base] in Hc |- *. rewrite B2. apply K2. lia.
    - apply (mdbb_region_tr E (w_H W) m m' _ R60); [|exact Hp]. intros c i Hin Hi. apply HK.
      pose proof (mdbb_chunk_in _ c Hin ltac:(vm_compute; reflexivity)) as Hc.
      cbn [YP09.r_lo YP09.r_hi YP09.r_base] in Hc |- *. rewrite B60. apply K60. lia.
    - apply (mdbb_region_tr E (w_H W) m m' _ R516); [|exact Hp]. intros c i Hin Hi. apply HK.
      cbn [YP09.r_chunks YP09.r_base In] in Hin |- *. rewrite B516.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn in Hi |- *; apply K516; lia.
    - apply (mdbb_region_tr E (w_H W) m m' _ R529); [|exact Hp]. intros c i Hin Hi. apply HK.
      unfold fshadow_region in Hin |- *. cbn [YP09.r_chunks YP09.r_base] in Hin |- *. rewrite B529.
      unfold dsh_chunks in Hin. apply in_map_iff in Hin as (kk & <- & Hkk). apply in_seq in Hkk.
      change (Z.to_nat DFRAME_SH) with 384%nat in Hkk. cbn in Hi |- *. apply KSH. lia. }
  split.
  { rewrite <- HFLAG. apply mdbb_rdword. intros i Hi. apply HK. apply KFL.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  split.
  - apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact H216].
    intros kk Hkk. apply HK. apply K60. change (Z.of_nat 8) with 8 in Hkk. lia.
  - apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact H152].
    intros kk Hkk. apply HK. apply K60. change (Z.of_nat 8) with 8 in Hkk. lia.
Qed.

Lemma mdbb_shadow_tr : forall (cx : dcx) shf (W : world SEGS) (m m' : word -> option byte) (K : Z -> Prop),
  d_shadow cx shf W m ->
  (forall a, K a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 -> K a) ->
  d_shadow cx shf W m'.
Proof.
  intros cx shf W m m' K HS HK KSH kk Hkk. rewrite HK by (apply KSH; unfold DFRAME_SH in Hkk; lia).
  exact (HS kk Hkk).
Qed.

Lemma mdbb_garr8_tr : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
  intros W m m' a l Hk Hg. apply (garr8_frame SEGS (rd W m)); [exact Hg|].
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hk. exact Hx.
Qed.

Lemma mdbb_vm_tr : forall (W : world SEGS) (m m' : word -> option byte) a (nn : nat) v,
  (forall x, a <= x < a + Z.of_nat nn -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rd W m) a nn v -> val_mem SEGS (rd W m') a nn v.
Proof.
  intros W m m' a nn v Hk Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact Hv].
  intros kk Hkk. apply Hk. lia.
Qed.

Lemma mdbb_garr8_out : forall (W : world SEGS) (m : word -> option byte) d (T : list Z),
  (forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS (w_H W) m (d + i) = Some (nth (Z.to_nat i) T 0)) ->
  aview SEGS (w_H W) m (d + Z.of_nat (length T)) = Some 0 ->
  garr8 SEGS (rd W m) d (T ++ [0]).
Proof.
  intros W m d T Hb Hz jj Hjj. rewrite length_app in Hjj. cbn [length] in Hjj.
  destruct (Nat.lt_ge_cases jj (length T)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl.
    pose proof (Hb (Z.of_nat jj) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv.
    exact (val_mem1_of_aview SEGS (w_H W) m _ _ Hv).
  - assert (jj = length T) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    exact (val_mem1_of_aview SEGS (w_H W) m _ _ Hz).
Qed.

Lemma mdbb_aview_garr8 : forall H (m : word -> option byte) a L j,
  garr8 SEGS (mrestrict H m) a L -> (j < length L)%nat -> aview SEGS H m (a + Z.of_nat j) = Some (nth j L 0).
Proof.
  intros H m a L j HG Hj. unfold aview. rewrite (garr8_mbyte SEGS (mrestrict H m) a L j HG Hj). cbn [option_map].
  destruct (HG j Hj) as [_ Hr]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma mdbb_ra_frame : forall (cx : dcx) shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx -> 0 <= lo -> lo + len <= 3072 ->
  (forall k, lo / 8 <= k < (lo + len + 7) / 8 -> shf k = 0) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + lo) len.
Proof.
  intros cx shf W m lo len HSH H8 HF0 Hlo Hhi Hz x Hx. exists 0. split; [|left; reflexivity].
  assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_addr (d_FB cx) + (x - d_FB cx) / 8)
    by (unfold shadow_of_addr, shadow_addr; lia).
  rewrite Ex. rewrite HSH by (unfold DFRAME_SH; lia). f_equal. apply Hz. lia.
Qed.

Lemma mdbb_hull_frame : forall (cx : dcx) shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx -> 64 <= lo -> 0 < len -> lo + len + 64 <= 3072 ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + lo) len.
Proof.
  intros cx shf W m lo len HSH H8 HF0 Hlo Hn Hhi s Hs. unfold shadow_addr in Hs.
  replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
  rewrite HSH; [discriminate|]. unfold shadow_addr, DFRAME_SH. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi AE2k.FF_got_canary AE2k.FF_canary YImgTop.IMG_LO YImgTop.IMG_TOP
    disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis DAIL : asink_img_laws SEGS B tfib_K.
Hypothesis DKCAN : ak_can_got tfib_K = AE2k.FF_got_canary /\ ak_canary tfib_K = AE2k.FF_canary.

Theorem a3f_mdbB : forall p, 0 <= p < 8 -> mdbB_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R26 & R1 & R10 & R11 & R12 & R13 & R19 & R21) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HPYK).
pose proof HPYK as (HSL & H392 & H408 & HUSED).
pose proof HSL as (Hpr & H368 & H336).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HBUF as (Hr2 & HGB).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof ASAN_CEIL_range as Hceil. unfold ASAN_CEIL in Hceil.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HOFF.
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 buf (Z.max (slot_ser_defs.ser_cap op) 1) DFRAME_CLASS
  (c_fpos cx) HAR3 Hinb HFin3) as HSEP.
unfold zdisjoint in HSEP. cbn [fst snd] in HSEP. rewrite EFA3 in HSEP.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HSEP.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp.
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))) <= 1296).
{ rewrite length_map, (mdbb_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (LU : length (a3f_used (p + 1)) = 32%nat) by (unfold a3f_used; reflexivity).
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (Esn : SNPRINTF_STK = 11776) by reflexivity.
assert (Eoa : d_obj cx OAGE = d_FB cx + 2064) by reflexivity.
assert (Eoo : d_obj cx OO = d_FB cx + 240) by reflexivity.
assert (Eot : d_obj cx OT = d_FB cx + 2160) by reflexivity.
assert (Eou : d_obj cx OUSED = d_FB cx + 1664) by reflexivity.
assert (Hsh : shadow_addr (d_FB cx) = 2147450880 + d_FB cx / 8) by reflexivity.
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
pose proof (mdbb_age_range T1 now p Hnow) as Hage.
pose proof (mdbb_udec_len (a3f_age T1 now p) Hage) as LTx.
pose proof (DiscoEntBody.can_got_rdword B tfib_K ly3 S3 W mem3 md3 DAIL (proj1 DKCAN) (proj2 DKCAN) HAR3) as HCG1.
pose proof (DiscoEntBody.can_rdword cx W mem3 HCAN) as HCG2.
pose proof (DCRO LAWS (conj DRO (conj GM (HV))) ly3 S3 W mem3 md3 HAR3 HIMG) as HCONST.
destruct HCONST as (_ & _ & _ & HSTR & _).
destruct HSTR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HSC18 & _) & _).
destruct HSC18 as (Hc18 & HG18 & Hf18 & Hf63 & Hl32 & HAM18 & HRA18 & HHV18 & _ & HIM18).
replace (BASE + (SIGMA DS___interceptor_trampoline_snprintf - BASE))
  with (SIGMA DS___interceptor_trampoline_snprintf) by ring.
assert (Asp : spZ regs = d_S cx + (d_A cx - d_S cx)) by lia.
assert (Aal : (d_A cx - d_S cx) mod 16 = 0) by lia.
assert (Aneg : d_A cx - d_S cx <= 0) by lia.
assert (Abud : SNPRINTF_STK - (d_A cx - d_S cx) <= LLVMF_STK) by (rewrite Esn; unfold LLVMF_STK; lia).
assert (Araw : YK0s.ret_ok (getr regs 1))
  by (rewrite R1; apply ret_ok_codeptr_v; [unfold MDS_OFF; lia | reflexivity]).
assert (Actx : snp_ctx W mem3 (spZ regs) (d_obj cx OAGE) 24).
{ apply (snp_ctx_ok B W mem3 (spZ regs) (d_obj cx OAGE) 24 SNPRO SNPUN HIMG
    (ex_intro _ (c_canary cx) (conj HCG1 HCG2))).
  - rewrite SpR, Esn. unfold off_img, IMG_LO, IMG_TOP. lia.
  - unfold off_img in HOFF |- *. rewrite Eoa. lia. }
assert (Afmt : fmt_at (aview SEGS (w_H W) mem3) (snp_out SNPRINTF_STK (spZ regs) (d_obj cx OAGE) 24)
  (VAL (A_OBJ 18)) a3f_fmt_age).
{ pose proof (pa_img_range _ (HIM18 (VAL (A_OBJ 18)) ltac:(simpl; lia))) as I0.
  pose proof (pa_img_range _ (HIM18 (VAL (A_OBJ 18) + 4) ltac:(simpl; lia))) as I4.
  unfold IMG_LO, IMG_TOP in I0, I4.
  unfold fmt_at, a3f_fmt_age. split; [exact Hf18|]. split.
  { intros i0 Hi0. simpl in Hi0.
    pose proof (mdbb_aview_garr8 (w_H W) mem3 _ _ (Z.to_nat i0) HG18 ltac:(simpl; lia)) as Hv.
    rewrite Z2Nat.id in Hv by lia. exact Hv. }
  split.
  { unfold snp_out. rewrite SpR, Esn.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
      cbn [length Z.of_nat]; rewrite ?Eoa; unfold off_img, IMG_LO, IMG_TOP in HOFF; lia. }
  split; [exact HAM18|]. split; [exact HRA18 | exact HHV18]. }
assert (Ava : va_words regs (aview SEGS (w_H W) mem3) (spZ regs) [] (map (argZ regs) [3; 4; 5; 6; 7])).
{ unfold va_words. split; [rewrite app_nil_r; reflexivity|]. intros i0 Hi0. cbn in Hi0. lia. }
assert (Axs : spZ regs + 8 * Z.of_nat (length (@nil Z)) <= d_S cx) by (cbn [length Z.of_nat]; rewrite SpR; lia).
assert (Axd : Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length (@nil Z))))
  (snp_out SNPRINTF_STK (spZ regs) (d_obj cx OAGE) 24)).
{ unfold snp_out. rewrite SpR, Esn. cbn [length Z.of_nat].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
    rewrite ?Eoa; lia. }
assert (Garg : argZ regs 3 = a3f_age T1 now p).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R13. unfold w64. apply unsigned_lit_small. lia. }
assert (Aargs : pf_args_asan (aview SEGS (w_H W) mem3) (snp_out SNPRINTF_STK (spZ regs) (d_obj cx OAGE) 24)
  (map (argZ regs) [3; 4; 5; 6; 7]) [AU64 (a3f_age T1 now p)]).
{ cbn [map pf_args_asan pf_arg_asan]. split; [exact Garg | exact I]. }
assert (Adest : forall a, d_obj cx OAGE <= a < d_obj cx OAGE + 24 ->
  awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
    [(DFRAME_CLASS, c_fpos cx)] a /\ ~ (spZ regs - SNPRINTF_STK <= a < spZ regs)).
{ intros a Ha. rewrite Eoa in Ha.
  split; [exact (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia))) | rewrite SpR, Esn; lia]. }
assert (Aamr : amem_range (d_obj cx OAGE) (24 + 8)).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. rewrite Eoa. lia. }
assert (Ara : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (d_obj cx OAGE) 24).
{ rewrite Eoa. apply (mdbb_ra_frame cx dsh_age W mem3 2064 24 HSHD); [lia | lia | lia | lia |].
  intros kk Hkk. assert (Hk3 : kk = 258 \/ kk = 259 \/ kk = 260) by lia.
  destruct Hk3 as [-> | [-> | ->]]; vm_compute; reflexivity. }
assert (Ahull : shadow_hull_vis (aview SEGS (w_H W) mem3) (d_obj cx OAGE) 24).
{ rewrite Eoa. apply (mdbb_hull_frame cx dsh_age W mem3 2064 24 HSHD); lia. }
assert (Vf18 : VAL (A_OBJ 18) = 0x21040) by exact (pa_obj_val 18 ltac:(vm_compute; lia)).
eapply SRr_bind.
{ exact (aj_snprintf_at B LAWS ASNPRINTF fq W regs mem3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k (d_obj cx OAGE) 24 (VAL (A_OBJ 18)) a3f_fmt_age
    [Pllu] [] (map (argZ regs) [3; 4; 5; 6; 7]) [AU64 (a3f_age T1 now p)] (pf_udec (a3f_age T1 now p))
    (d_A cx - d_S cx) HJ R10 R11 R12 Asp Aal Aneg Abud Rgp Rtp Araw Actx Afmt mdbb_parse
    ltac:(apply Forall_cons; [exact I | apply Forall_nil]) Ava Axs Axd Aargs (mdbb_text (a3f_age T1 now p))
    ltac:(lia) ltac:(lia) ltac:(rewrite Eoa; lia) ltac:(rewrite Eoa; lia)
    ltac:(unfold snp_out; rewrite SpR, Esn; cbn [pairwise];
          split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rewrite Eoa; lia | apply Forall_nil]|];
          split; [apply Forall_nil | exact I])
    Adest Aamr Ara Ahull
    ltac:(rewrite Vf18; unfold disco_fmt_lo; lia)
    ltac:(rewrite Vf18; unfold disco_fmt_hi; change (length a3f_fmt_age) with 4%nat; lia)
    ltac:(unfold a3f_fmt_age; discriminate) I I Hfrm0 HIMG). }
intros W2 c2 _ (-> & fq2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HPR & Hsame & Hres & Heff & Hz & Hfr & Hpres2).
rewrite Z.min_l in Heff, Hz by lia.
assert (HAGE2 : garr8 SEGS (rd W mem2) (d_obj cx OAGE) (pf_udec (a3f_age T1 now p) ++ [0]))
  by exact (mdbb_garr8_out W mem2 (d_obj cx OAGE) _ Heff Hz).
pose (K := fun a : Z => 0 <= a < 2 ^ 64 /\ ~ (d_obj cx OAGE <= a < d_obj cx OAGE + 24) /\
  ~ (d_A cx - 11776 <= a < d_A cx)).
assert (HK : forall a, K a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a (Ha & Hb & Hc). apply Hfr; [exact Ha | lia | rewrite SpR, Esn; exact Hc]. }
assert (KR : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (hi <= d_obj cx OAGE \/ d_obj cx OAGE + 24 <= lo) -> (hi <= d_A cx - 11776 \/ d_A cx <= lo) ->
  forall a, lo <= a < hi -> K a).
{ intros lo hi H1 H2 H3 H4 a Ha. unfold K. lia. }
assert (HFRM2 : d_frame cx h dsh_age W mem2).
{ apply (mdbb_frame_tr cx h dsh_age W mem3 mem2 K HFRM HK Hpres2);
    try (apply KR; rewrite ?Eoa, ?Hsh; lia); lia. }
assert (HSHD2 : d_shadow cx dsh_age W mem2).
{ apply (mdbb_shadow_tr cx dsh_age W mem3 mem2 K HSHD HK). apply KR; rewrite ?Eoa, ?Hsh; lia. }
assert (HBODY2 : d_body B cx h n (a3_xb buf op) dsh_age ly3 S3 W mem2).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_age dsh_age ly3 S3 W mem3 mem2 (d_A cx - 11776) (d_A cx)
    (fun a => d_objr cx OAGE a \/ (d_A cx - 11776 <= a < d_A cx)) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a [Ha | Ha]; [right | left; exact Ha].
    unfold d_objr, d_obj, dobj_off, dobj_size in Ha.
    pose proof HGEO as (_ & _ & _ & _ & _ & _ & G7 & G8).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in G7, G8.
    unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size.
    intros [X | [X | [X | [X | [X | [X | [X | X]]]]]]];
      [ lia | lia | lia | lia
      | destruct G7 as [G7 | G7]; lia
      | destruct X as (Xn & X); destruct (G8 Xn) as (_ & _ & G9 & _); destruct G9 as [G9 | G9]; lia
      | destruct X as (X & _);
        exact (off_img_not_img (d_FB cx) 4096 a HOFF ltac:(lia) (in_roP_img a X))
      | exact (off_img_not_img (d_FB cx) 4096 a HOFF ltac:(lia) (proj2 (proj2 HCAN) a X)) ].
  - intros a Ha Hna. apply Hfr; [exact Ha | |].
    + intros Hd. apply Hna. left. unfold d_objr. cbn [dobj_size]. lia.
    + rewrite SpR, Esn. intros Hw. apply Hna. right. exact Hw.
  - intros a _ Hpa. exact (Hpres2 a Hpa).
  - exact HFRM2.
  - exact HSHD2.
  - lia. }
assert (KV : forall a (nn : nat) v, (forall x, a <= x < a + Z.of_nat nn -> K x) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W mem2) a nn v).
{ intros a nn v Hx Hv. apply (mdbb_vm_tr W mem3 mem2 a nn v); [|exact Hv]. intros x Hx'. apply HK. apply Hx. exact Hx'. }
assert (KG : forall a l, (forall x, a <= x < a + Z.of_nat (length l) -> K x) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W mem2) a l).
{ intros a l Hx Hg. apply (mdbb_garr8_tr W mem3 mem2 a l); [|exact Hg]. intros x Hx'. apply HK. apply Hx. exact Hx'. }
pose proof HSP1 as ((H232 & H344) & H224 & H248).
pose proof HSP0 as (S232 & S344).
assert (P2 : getr regs2 2 = getr regs 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr regs 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr regs 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr regs 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
rewrite R1. unfold w64.
pose proof (paj_run (fx := fq2) (PI := PI) B LAWS) as RUN.
remember (Eimg (Ereg regs2 [Z_to_bv 64 SB])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs2 r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (HS : st_ok_pi (fx := fq2) SEGS VAL E0 (mkSS MDS_OFF sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (YK11.mkst (fx := fq2) regs2 (Z_to_bv 64 (BASE + MDS_OFF)) mem2 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ lazymatch goal with |- awr_ok ?E ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' a b c d e f g) end.
  apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem2).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & _). cbn [ss_mem] in Hr. destruct Hr. }
pmkst HS.
rewrite Emem. rewrite Emem in HJ2.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
rewrite pa_sigma_jtok_is.
assert (G1 : getr (ms_regs ms) 1 = w64 (BASE + MDJ_OFF)) by (rewrite Q1; reflexivity).
assert (G2 : getr (ms_regs ms) 2 = getr regs 2) by (rewrite Q2, (EE0 2%nat 2%bv eq_refl); exact P2).
assert (G3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite Q3, (EE0 3%nat 3%bv eq_refl); exact P3).
assert (G4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite Q4, (EE0 4%nat 4%bv eq_refl); exact P4).
assert (G8 : getr (ms_regs ms) 8 = getr regs 8) by (rewrite Q8, (EE0 8%nat 8%bv eq_refl); exact P8).
assert (G9 : getr (ms_regs ms) 9 = getr regs 9) by (rewrite Q9, (EE0 9%nat 9%bv eq_refl); exact P9).
assert (G18 : getr (ms_regs ms) 18 = getr regs 18) by (rewrite Q18, (EE0 18%nat 18%bv eq_refl); exact P18).
assert (G20 : getr (ms_regs ms) 20 = getr regs 20) by (rewrite Q20, (EE0 20%nat 20%bv eq_refl); exact P20).
assert (G25 : getr (ms_regs ms) 25 = getr regs 25) by (rewrite Q25, (EE0 25%nat 25%bv eq_refl); exact P25).
assert (G26 : getr (ms_regs ms) 26 = getr regs 26) by (rewrite Q26, (EE0 26%nat 26%bv eq_refl); exact P26).
assert (G10 : getr (ms_regs ms) 10 = w64 (d_obj cx OO + 144 * p + 120)).
{ rewrite Q10, (EE0 21%nat 21%bv eq_refl), P21, R21. unfold w64. rewrite unsigned_lit_small by (rewrite Eoo; lia).
  f_equal; lia. }
assert (G11 : getr (ms_regs ms) 11 = w64 2) by (rewrite Q11; reflexivity).
assert (G12 : getr (ms_regs ms) 12 = w64 (d_obj cx OAGE)).
{ rewrite Q12, (EE0 19%nat 19%bv eq_refl), P19. exact R19. }
apply SRr_ret.
unfold mdb_c2, a3f_st. split; [exact Hfrom|].
unfold d_arm_at_pf, d_at.
exists fq2, ly3, S3, (ms_regs ms), mem2, (with_vm_backing (m_vm_lazy md2) mat md2), k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact Hfrm2|].
split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rL. split; [unfold spZ in Rsp |- *; rewrite G2; exact Rsp|].
  split; [rewrite G3; exact Rgp|]. split; [rewrite G4; exact Rtp|]. split; [rewrite G8; exact R8|].
  split; [rewrite G9; exact R9|]. split; [rewrite G18; exact R18|]. split; [rewrite G20; exact R20|].
  rewrite G25; exact R25. }
split.
{ cbv beta. split; [rewrite G26; exact R26|].
  split; [exact G1|]. split; [exact G10|]. split; [exact G11 | exact G12]. }
split.
{ cbv beta. split.
  { split; [split|].
    - apply KV; [apply KR; rewrite ?Eoa; lia | exact H232].
    - apply KV; [apply KR; rewrite ?Eoa; lia | exact H344].
    - split; [apply KV; [apply KR; rewrite ?Eoa; lia | exact H224]
             | apply KV; [apply KR; rewrite ?Eoa; lia | exact H248]]. }
  split.
  { split; [exact (proj1 HTAB)|].
    apply KG; [|exact HGT]. apply KR; rewrite ?length_map, ?HLT1, ?Eot, ?Eoa; lia. }
  split.
  { split; [exact Hr2|]. apply KG; [|exact HGB]. apply KR; rewrite ?Lb, ?Eoa; lia. }
  split; [exact HJR|]. split; [exact HVP|].
  split.
  { apply KG; [|exact HOO]. apply KR; rewrite ?Eoo, ?Eoa; lia. }
  split.
  { split.
    { split; [exact Hpr|]. split.
      - apply KV; [apply KR; rewrite ?Eoa; lia | exact H368].
      - apply KV; [apply KR; rewrite ?Eoa; lia | exact H336]. }
    split; [apply KV; [apply KR; rewrite ?Eoa; lia | exact H392]|].
    split; [apply KV; [apply KR; rewrite ?Eoa; lia | exact H408]|].
    apply KG; [|exact HUSED]. apply KR; rewrite ?LU, ?Eou, ?Eoa; lia. }
  rewrite (mdbb_dec (a3f_age T1 now p) Hage). exact HAGE2. }
split.
{ split; [apply KV; [apply KR; rewrite ?Eoa; lia | exact S232]
         | apply KV; [apply KR; rewrite ?Eoa; lia | exact S344]]. }
exact HBODY2.
Qed.

End h.
End f.
End d.
