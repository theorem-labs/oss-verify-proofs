(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA2.v, with its module paths and module names changed; 454 of its 523 lines of code are new or changed and 597 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YC88 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnShared SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldMDFacts DiscoArm3FieldMDKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldMDBKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs
disco_json_lemmas tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition mdbb_rgn : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 416 0 0 [YP09.mkChunk 408 (CVal 8 (SOff 33%nat 0))].

Lemma mdbb_parse : pf_parse a3f_fmt_age = Some [Pllu].
Proof. vm_compute. reflexivity. Qed.

Lemma mdbb_text : forall u, pf_text [Pllu] [AU64 u] = Some (pf_udec u).
Proof. intros u. cbn [pf_text option_map]. rewrite app_nil_r. reflexivity. Qed.

Lemma mdbb_last_range : forall (T : list byte) (p : Z), 0 <= disco_table_c.last_of T p < 2 ^ 64.
Proof.
  intros T p. unfold disco_table_c.last_of.
  pose proof (mdf_u_at_range T (48 * p + 40) 8) as H.
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

Lemma mdbb_chunk_in : forall r c, In c (YP09.r_chunks r) -> region_wf r = true ->
  YP09.r_lo r <= YP09.c_off c /\ YP09.c_off c + c_len c <= YP09.r_hi r.
Proof.
  intros r c Hin Hwf. unfold region_wf in Hwf. apply andb_prop in Hwf as [_ Hcs].
  pose proof (proj1 (forallb_forall _ _) Hcs c Hin) as X. unfold chunk_inside in X.
  apply andb_prop in X as [X _]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing} {POV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma mdbb_roimg : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hg)].
Qed.

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
  intros cx h shf W m m' K (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264)
    HK Hp K2 K60 K516 KFL KSH HA HF.
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
  { rewrite <- HFLAG. apply rdword_ext. intros i Hi. apply HK. apply KFL.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  assert (KV8 : forall off v, 0 <= off <= 464 -> val_mem SEGS (rd W m) (d_A cx + off) 8 v ->
    val_mem SEGS (rd W m') (d_A cx + off) 8 v).
  { intros off v Ho Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact Hv].
    intros kk Hkk. apply HK. apply K60. change (Z.of_nat 8) with 8 in Hkk. lia. }
  split; [exact (KV8 184 _ ltac:(lia) V184)|].
  split; [exact (KV8 120 _ ltac:(lia) V120)|].
  split; [exact (KV8 136 _ ltac:(lia) V136)|].
  split; [exact (KV8 376 _ ltac:(lia) V376)|].
  split; [exact (KV8 280 _ ltac:(lia) V280)|].
  split; [exact (KV8 232 _ ltac:(lia) V232)|].
  exact (KV8 264 _ ltac:(lia) V264).
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
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi FF_got_canary FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA AS___interceptor_trampoline_snprintf).
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_can_got tfib_K = FF_got_canary /\ ak_canary tfib_K = FF_canary.

Theorem a3f_mdbB : forall p, 0 <= p < 8 -> mdbB_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R1 & R10 & R11 & R12 & R13 & R21) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HPYK).
pose proof HPYK as (HSL & H408 & HUSED).
pose proof HSL as (Hpr & H368 & H360).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HBUF as (Hr2 & HGB).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
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
{ rewrite length_map, (mdk_objs_len buf vpad os HVP Lo6), Los. lia. }
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
pose proof HCAN as (HCv & HCr & HCimg).
destruct (snp_can_of B tfib_K AIL (proj1 KCAN) (proj2 KCAN) ly3 S3 W mem3 md3 (c_canary cx) HAR3 HCv HCr)
  as (cval & HCG1 & HCG2).
pose proof (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HIMG) as HCONST.
destruct HCONST as (_ & _ & _ & HSTR & _).
destruct HSTR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS18 & _).
destruct HS18 as ((Hf18 & HG18 & Hp18 & Hb18 & Hl18 & HAM18 & HRA18 & HHV18 & _ & HIM18) & _).
replace (BASE + (SIGMA AS___interceptor_trampoline_snprintf - BASE))
  with (SIGMA AS___interceptor_trampoline_snprintf) by ring.
assert (Asp : spZ regs = d_S cx + (d_A cx - d_S cx)) by lia.
assert (Aal : (d_A cx - d_S cx) mod 16 = 0) by lia.
assert (Aneg : d_A cx - d_S cx <= 0) by lia.
assert (Abud : SNPRINTF_STK - (d_A cx - d_S cx) <= LLVMF_STK) by (rewrite Esn; unfold LLVMF_STK; lia).
assert (Araw : YK0s.ret_ok (getr regs 1))
  by (rewrite R1; unfold w64; apply ret_ok_codeptr_v; [unfold MDS_OFF; lia | reflexivity]).
assert (Actx : snp_ctx W mem3 (spZ regs) (d_obj cx OAGE) 24).
{ apply (snp_ctx_ok B W mem3 (spZ regs) (d_obj cx OAGE) 24 SNPRO SNPUN HIMG
    (ex_intro _ cval (conj HCG1 HCG2))).
  - rewrite SpR, Esn. unfold off_img, IMG_LO, IMG_TOP. lia.
  - unfold off_img in HOFF |- *. rewrite Eoa. lia. }
assert (Afmt : SnShared.fmt_at (aview SEGS (w_H W) mem3) (SnShared.snp_out SNPRINTF_STK (spZ regs) (d_obj cx OAGE) 24)
  (VAL (A_OBJ 18)) a3f_fmt_age).
{ pose proof (pa_img_range _ (HIM18 (VAL (A_OBJ 18)) ltac:(cbn [length Z.of_nat]; lia))) as I0.
  pose proof (pa_img_range _ (HIM18 (VAL (A_OBJ 18) + 4) ltac:(cbn [length Z.of_nat]; lia))) as I4.
  unfold IMG_LO, IMG_TOP in I0, I4.
  unfold SnShared.fmt_at, a3f_fmt_age. split; [exact Hp18|]. split.
  { intros i0 Hi0. cbn [length Z.of_nat] in Hi0.
    pose proof (mdbb_aview_garr8 (w_H W) mem3 _ _ (Z.to_nat i0) HG18 ltac:(cbn [length app]; lia)) as Hv.
    rewrite Z2Nat.id in Hv by lia. exact Hv. }
  split.
  { unfold SnShared.snp_out. rewrite SpR, Esn.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
      cbn [length Z.of_nat]; rewrite ?Eoa; unfold off_img, IMG_LO, IMG_TOP in HOFF; lia. }
  split; [exact HAM18|]. split; [exact HRA18 | exact HHV18]. }
assert (Ava : SnShared.va_words regs (aview SEGS (w_H W) mem3) (spZ regs) [] (map (argZ regs) [3; 4; 5; 6; 7])).
{ unfold SnShared.va_words. split; [rewrite app_nil_r; reflexivity|]. intros i0 Hi0. cbn in Hi0. lia. }
assert (Axs : spZ regs + 8 * Z.of_nat (length (@nil Z)) <= 2 ^ 47) by (cbn [length Z.of_nat]; rewrite SpR; lia).
assert (Axd : Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length (@nil Z))))
  (SnShared.snp_out SNPRINTF_STK (spZ regs) (d_obj cx OAGE) 24)).
{ unfold SnShared.snp_out. rewrite SpR, Esn. cbn [length Z.of_nat].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
    rewrite ?Eoa; lia. }
assert (Garg : argZ regs 3 = a3f_age T1 now p).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R13. unfold w64. apply unsigned_lit_small. lia. }
assert (Aargs : SnShared.pf_args_asan (aview SEGS (w_H W) mem3) (SnShared.snp_out SNPRINTF_STK (spZ regs) (d_obj cx OAGE) 24)
  (map (argZ regs) [3; 4; 5; 6; 7]) [AU64 (a3f_age T1 now p)]).
{ cbn [map SnShared.pf_args_asan SnShared.pf_arg_asan]. split; [exact Garg | exact I]. }
assert (Adest : forall a, d_obj cx OAGE <= a < d_obj cx OAGE + 24 ->
  awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
    [(DFRAME_CLASS, c_fpos cx)] a /\ ~ (spZ regs - SNPRINTF_STK <= a < spZ regs)).
{ intros a Ha. rewrite Eoa in Ha.
  split; [exact (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia))) | rewrite SpR, Esn; lia]. }
assert (Aamr : amem_range (d_obj cx OAGE) (24 + 8)).
{ rewrite Eoa. apply (amem_range_sub_app (d_FB cx) 4096); [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; lia | lia | lia | lia | lia]. }
assert (Ara : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (d_obj cx OAGE) 24).
{ rewrite Eoa. apply (mdbb_ra_frame cx dsh_age W mem3 2064 24 HSHD); [lia | lia | lia | lia |].
  intros kk Hkk. assert (Hk3 : kk = 258 \/ kk = 259 \/ kk = 260) by lia.
  destruct Hk3 as [-> | [-> | ->]]; vm_compute; reflexivity. }
assert (Ahull : shadow_hull_vis (aview SEGS (w_H W) mem3) (d_obj cx OAGE) 24).
{ rewrite Eoa. apply (mdbb_hull_frame cx dsh_age W mem3 2064 24 HSHD); lia. }
assert (V18 : VAL (A_OBJ 18) = 0x21040)
  by (rewrite (pa_obj_val 18%nat ltac:(unfold tfib_nobj; lia)); reflexivity).
assert (Aflo : disco_fmt_lo <= VAL (A_OBJ 18)) by (rewrite V18; unfold disco_fmt_lo; lia).
assert (Afhi : VAL (A_OBJ 18) + Z.of_nat (length a3f_fmt_age) + 1 <= disco_fmt_hi).
{ rewrite V18. change (Z.of_nat (length a3f_fmt_age)) with 4. unfold disco_fmt_hi. lia. }
assert (Ane : a3f_fmt_age <> []) by (unfold a3f_fmt_age; discriminate).
assert (Aamem : SnFF.pf_args_amem (map (argZ regs) [3; 4; 5; 6; 7]) [AU64 (a3f_age T1 now p)]) by exact I.
eapply SRr_bind.
{ exact (aj_snprintf_at B LAWS ASNPRINTF fq W regs mem3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k (d_obj cx OAGE) 24 (VAL (A_OBJ 18)) a3f_fmt_age
    [Pllu] [] (map (argZ regs) [3; 4; 5; 6; 7]) [AU64 (a3f_age T1 now p)] (pf_udec (a3f_age T1 now p))
    (d_A cx - d_S cx) HJ Hfrm R10 R11 R12 Asp Aal Aneg Abud Rgp Rtp Araw Actx Afmt mdbb_parse
    ltac:(apply Forall_cons; [exact I | apply Forall_nil]) Aflo Afhi Ane Ava Axs Axd Aargs Aamem
    (mdbb_text (a3f_age T1 now p))
    ltac:(lia) ltac:(lia) ltac:(rewrite Eoa; lia) ltac:(rewrite Eoa; lia)
    ltac:(unfold SnShared.snp_out; rewrite SpR, Esn; cbn [pairwise];
          split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rewrite Eoa; lia | apply Forall_nil]|];
          split; [apply Forall_nil | exact I])
    Adest Aamr Ara Ahull HIMG). }
intros W2 c2 _ (-> & fq2 & regs2 & mem2 & md2 & -> & Hfrm2 & _ & HJ2 & HPR & Hsame & Hres & Heff & Hz & Hfr & Hpres2).
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
{ intros lo hi H1 H2 H3 H4 a Ha. unfold K. clear - H1 H2 H3 H4 Ha. lia. }
assert (HFRM2 : d_frame cx h dsh_age W mem2).
{ apply (mdbb_frame_tr cx h dsh_age W mem3 mem2 K HFRM HK Hpres2);
    try (apply KR; rewrite ?Eoa, ?Hsh; lia); lia. }
assert (HSHD2 : d_shadow cx dsh_age W mem2).
{ apply (mdbb_shadow_tr cx dsh_age W mem3 mem2 K HSHD HK). apply KR; rewrite ?Eoa, ?Hsh; lia. }
assert (HBODY2 : d_body B cx h n (a3_xb buf op) dsh_age ly3 S3 W mem2).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_age dsh_age ly3 S3 W mem3 mem2 (d_A cx - 11776) (d_A cx)
    (fun a => d_objr cx OAGE a \/ (d_A cx - 11776 <= a < d_A cx)) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a [Ha | Ha]; [right | left; exact Ha].
    unfold d_objr in Ha. rewrite Eoa in Ha. cbn [dobj_size] in Ha.
    pose proof HGEO as (_ & _ & _ & _ & _ & _ & G7 & G8).
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in G7, G8.
    unfold off_img, IMG_LO, IMG_TOP in HOFF.
    intros Xd. unfold d_rdset, d_objr, d_obj in Xd. cbn [dobj_off dobj_size] in Xd.
    destruct Xd as [X | [X | [X | [X | [X | [(Xn & X) | [(X & _) | X]]]]]]].
    + clear - Ha X. lia.
    + clear - Ha X. lia.
    + clear - Ha X. lia.
    + clear - Ha X. lia.
    + clear - Ha X G7. lia.
    + destruct (G8 Xn) as (_ & _ & G9 & _). clear - Ha X G9. lia.
    + pose proof (pa_img_range _ (mdbb_roimg a X)) as Xi. unfold IMG_LO, IMG_TOP in Xi.
      clear - Ha Xi HOFF. lia.
    + pose proof (pa_img_range _ (HCimg a X)) as Xi. unfold IMG_LO, IMG_TOP in Xi.
      clear - Ha Xi HOFF. lia.
  - intros a Ha Hna. apply Hfr; [exact Ha | |].
    + intros Hd. apply Hna. left. unfold d_objr. cbn [dobj_size]. lia.
    + rewrite SpR, Esn. intros Hw. apply Hna. right. exact Hw.
  - intros a _ Hpa. exact (Hpres2 a Hpa).
  - exact HFRM2.
  - exact HSHD2.
  - lia. }
assert (KV : forall a (nn : nat) v, (forall x, a <= x < a + Z.of_nat nn -> K x) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W mem2) a nn v).
{ intros a nn v Hx Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact Hv].
  intros kk Hkk. apply HK. apply Hx. lia. }
assert (KG : forall a l, (forall x, a <= x < a + Z.of_nat (length l) -> K x) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W mem2) a l).
{ intros a l Hx Hg. apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact Hg].
  intros x Hx'. apply HK. apply Hx. exact Hx'. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
pose proof HSP0 as (S208 & S320).
assert (V408 : val_mem SEGS (rd W mem2) (d_A cx + 408) 8 (d_obj cx OO + 144 * p))
  by (apply KV; [apply KR; rewrite ?Eoa; lia | exact H408]).
assert (P2 : getr regs2 2 = getr regs 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr regs 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr regs 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr regs 24) by exact (HPR 24 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27 = getr regs 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
rewrite R1. unfold w64.
pose proof (paj_run (fx := fq2) (PI := PI) B LAWS) as RUN.
remember (Eimg (Ereg regs2 [Z_to_bv 64 SB; Z_to_bv 64 (d_obj cx OO + 144 * p)])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs2 r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (E33 : ew E0 33 = Z_to_bv 64 (d_obj cx OO + 144 * p)).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
assert (EA9 : bv_unsigned (ew E0 9) = d_A cx).
{ rewrite (EE0 9%nat 9%bv eq_refl), P9, Rs1. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok_pi (fx := fq2) SEGS VAL E0 (mkSS MDS_OFF sr_atoms [mdbb_rgn] None (mkFacts [] [] []))
  (restrict (w_H W) (YK11.mkst (fx := fq2) regs2 (Z_to_bv 64 (BASE + MDS_OFF)) mem2 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold mdbb_rgn, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
    rewrite EA9. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E0 _ (d_A cx) 408 8 (SOff 33 0) (d_obj cx OO + 144 * p)).
    + cbn [sv_denot]. rewrite E33, Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_small by (rewrite Eoo; lia). reflexivity.
    + cbn. rewrite Eoo. lia.
    + cbn. lia.
    + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact V408.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [exact I | split; exact I]. }
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?cc ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b cc d e f g) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem2).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & Hw).
  cbn [In] in Hr. destruct Hr as [<- | []]. unfold mdbb_rgn in Hw.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
pmkst HS.
rewrite Emem. rewrite Emem in HJ2.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
rewrite pa_sigma_jtok_is.
assert (G1 : getr (ms_regs ms) 1 = w64 (BASE + MDJ_OFF)) by (rewrite Q1; reflexivity).
assert (G2 : getr (ms_regs ms) 2 = getr regs 2) by (rewrite Q2, (EE0 2%nat 2%bv eq_refl); exact P2).
assert (G3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite Q3, (EE0 3%nat 3%bv eq_refl); exact P3).
assert (G4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite Q4, (EE0 4%nat 4%bv eq_refl); exact P4).
assert (G8 : getr (ms_regs ms) 8 = getr regs 8) by (rewrite Q8, (EE0 8%nat 8%bv eq_refl); exact P8).
assert (G9 : getr (ms_regs ms) 9 = getr regs 9) by (rewrite Q9, (EE0 9%nat 9%bv eq_refl); exact P9).
assert (G18 : getr (ms_regs ms) 18 = getr regs 18) by (rewrite Q18, (EE0 18%nat 18%bv eq_refl); exact P18).
assert (G19 : getr (ms_regs ms) 19 = getr regs 19) by (rewrite Q19, (EE0 19%nat 19%bv eq_refl); exact P19).
assert (G20 : getr (ms_regs ms) 20 = getr regs 20) by (rewrite Q20, (EE0 20%nat 20%bv eq_refl); exact P20).
assert (G24 : getr (ms_regs ms) 24 = getr regs 24) by (rewrite Q24, (EE0 24%nat 24%bv eq_refl); exact P24).
assert (G27 : getr (ms_regs ms) 27 = getr regs 27) by (rewrite Q27, (EE0 27%nat 27%bv eq_refl); exact P27).
assert (G10 : getr (ms_regs ms) 10 = w64 (d_obj cx OO + 144 * p + 120)).
{ rewrite Q10, E33. unfold w64. rewrite unsigned_lit_small by (rewrite Eoo; lia). reflexivity. }
assert (G11 : getr (ms_regs ms) 11 = w64 2) by (rewrite Q11; reflexivity).
assert (G12 : getr (ms_regs ms) 12 = w64 (d_obj cx OAGE)).
{ rewrite Q12, (EE0 21%nat 21%bv eq_refl), P21. exact R21. }
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
  split; [rewrite G3; exact Rgp|]. split; [rewrite G4; exact Rtp|]. split; [rewrite G8; exact Rs0|].
  split; [rewrite G9; exact Rs1|]. split; [rewrite G19; exact Rs19|]. split; [rewrite G18; exact Rs18|].
  split; [rewrite G20; exact Rs20|]. rewrite G27; exact Rs27. }
split.
{ cbv beta. split; [rewrite G24; exact R24|].
  split; [exact G1|]. split; [exact G10|]. split; [exact G11 | exact G12]. }
split.
{ cbv beta. split.
  { split; [split|].
    - apply KV; [apply KR; rewrite ?Eoa; lia | exact H208].
    - apply KV; [apply KR; rewrite ?Eoa; lia | exact H320].
    - split; [apply KV; [apply KR; rewrite ?Eoa; lia | exact H192]
             | apply KV; [apply KR; rewrite ?Eoa; lia | exact H200]]. }
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
      - apply KV; [apply KR; rewrite ?Eoa; lia | exact H360]. }
    split; [exact V408|].
    apply KG; [|exact HUSED]. apply KR; rewrite ?LU, ?Eou, ?Eoa; lia. }
  rewrite (mdbb_dec (a3f_age T1 now p) Hage). exact HAGE2. }
split.
{ split; [apply KV; [apply KR; rewrite ?Eoa; lia | exact S208]
         | apply KV; [apply KR; rewrite ?Eoa; lia | exact S320]]. }
exact HBODY2.
Qed.

End h.
End f.
End d.
