(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 438 of its 509 lines of code are new or changed and 425 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonC2Cp.v, with its module paths, module names and numbers changed; 199 of its 357 lines of code are new or changed and 351 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP03 YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbp YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoArm3TailK DiscoYEntBodyStmt DiscoArm3 DiscoArm3JsonModel
DiscoArm3JsonCut DiscoArm3JsonJs DiscoArm3JsonCallee.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac jsc_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Lemma jsc_bytes_map : forall l : list Z, (forall jj, (jj < length l)%nat -> 0 <= nth jj l 0 < 256) ->
  map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|z l IH]; intros H; [reflexivity|]. cbn [map]. f_equal.
  - pose proof (H 0%nat ltac:(cbn [length]; lia)) as Hz. cbn [nth] in Hz. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
  - apply IH. intros jj Hjj. exact (H (S jj) ltac:(cbn [length]; lia)).
Qed.

Lemma jsc_zs_range : forall (rd : Z -> option Z) Bs lo len a n,
  zero_shadow rd Bs lo len -> lo <= a -> a + n + 16 <= lo + len -> range_addressable rd Bs a n.
Proof.
  intros rd Bs lo len a n Hz H1 H2 x Hx. exists 0. split; [|left; reflexivity].
  unfold zero_shadow, shadow_of_addr in *.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Ml.
  pose proof (Z.div_mod len 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as Mn.
  replace (Bs + x / 8) with (Bs + lo / 8 + (x / 8 - lo / 8)) by lia.
  apply Hz. lia.
Qed.

Lemma jsc_zs_hull : forall (rd : Z -> option Z) lo len a n,
  zero_shadow rd SHADOW_OFF lo len -> lo + 64 <= a -> a + n + 80 <= lo + len -> 0 < n -> shadow_hull_vis rd a n.
Proof.
  intros rd lo len a n Hz H1 H2 Hn s Hs. unfold zero_shadow, shadow_of_addr in Hz. unfold shadow_addr in Hs.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
  pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Db. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Mb.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Ml.
  pose proof (Z.div_mod len 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Dc.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Mc.
  pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Dd.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Md.
  replace s with (SHADOW_OFF + lo / 8 + (s - SHADOW_OFF - lo / 8)) by lia.
  rewrite Hz; [discriminate|]. lia.
Qed.

Lemma jsc_rdword_kept : forall (rd1 rd2 : Z -> option Z) a, (forall k, 0 <= k < 8 -> rd2 (a + k) = rd1 (a + k)) ->
  rdword rd2 a = rdword rd1 a.
Proof.
  intros rd1 rd2 a H. unfold rdword.
  assert (H0 : rd2 a = rd1 a) by (rewrite <- (Z.add_0_r a); apply H; lia).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma jsc_mbyte_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a,
  d_kept P W m W' m' -> 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS (rd W' m') a = mbyte SEGS (rd W m) a.
Proof.
  intros P W m W' m' a HK Ha HP. pose proof (HK a Ha HP) as E. unfold aview in E.
  destruct (mbyte SEGS (rd W' m') a) as [b1|] eqn:E1; destruct (mbyte SEGS (rd W m) a) as [b2|] eqn:E2;
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma jsc_val_mem_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a nb v,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat nb -> ~ P x) ->
  val_mem SEGS (rd W m) a nb v -> val_mem SEGS (rd W' m') a nb v.
Proof.
  intros P W m W' m' a nb v HK H0 H1 HP Hv k Hk.
  rewrite (jsc_mbyte_kept P W m W' m'); [exact (Hv k Hk) | exact HK | lia |].
  apply HP. lia.
Qed.

Lemma jsc_garr8_kept : forall (P : Z -> Prop) (W : world SEGS) m (W' : world SEGS) m' a l,
  d_kept P W m W' m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length l) -> ~ P x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
  intros P W m W' m' a l HK H0 H1 HP Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (jsc_val_mem_kept P W m W' m'); [exact HK | lia | lia | | exact Hv].
  intros x Hx. apply HP. lia.
Qed.

Lemma jsc_region_ok_kept : forall (E : env) (m m' : word -> option byte) (r : YP09.region) lo hi,
  region_ok SEGS E m r ->
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) (YP09.r_chunks r) = true ->
  (forall a, base_val E (YP09.r_base r) + lo <= a < base_val E (YP09.r_base r) + hi ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r lo hi HR Hb Hk Hw. destruct HR as (H0 & H1 & _ & HC).
  split; [exact H0|]. split; [exact H1|]. split; [exact Hw|].
  rewrite Forall_forall in HC |- *. intros c Hc ii Hii. destruct (HC c Hc ii Hii) as (b & Hb1 & Hb2).
  exists b. split; [exact Hb1|].
  pose proof (proj1 (forallb_forall _ _) Hb c Hc) as Hcb. apply andb_prop in Hcb as [Hl Hh].
  apply Z.leb_le in Hl. apply Z.leb_le in Hh.
  rewrite Hk; [exact Hb2|]. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis tjsc_roimg : tjson_scalar_roimg.
Hypothesis TJSC : tjson_scalar_spec B.
Hypothesis DBCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma jsc_consts_view : forall (W : world SEGS) m,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) -> consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W m.
Proof.
  intros W m HA a Ha. destruct (de_mc_un a Ha) as (H1 & H2). exact (HA a (de_mc_ro a Ha) H1 H2).
Qed.

Theorem jsc_step : jsc_step_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf shf ret idx voff j kk ks kl R X W c
    Hret Hret2 Hv8 Hv0 Hv1 Hidx Hjs HRk HXk Hin.
  unfold jsc_in, jcut, d_arm_at_pf, d_at in Hin.
  destruct Hin as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
    HMO &
    Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & R1 & R10 & R11 & R12 & R13 & HR) & (HSP1 & HTAB & HBUF & HX) &
    HSP0 & HBODY).
  pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
  pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HROD & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
  pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
  assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
  pose proof alloc_ceiling_value as Hceil0.
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
  unfold MFRAME in GA1. unfold LLVMF_STK in GSlo, GSTK.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hastk as (_ & _ & Hstk1 & Hstk2 & Hstk3 & _).
  unfold LLVMF_STK in Hstk2.
  pose proof (al_zshadow _ _ LAWS ly3 S3 W mem3 md3 (ly_stk_lo ly3, ly_stk_hi ly3 - ly_stk_lo ly3) HAR3
    ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZS.
  cbn [fst snd] in HZS. rewrite Elo, Ehi in HZS.
  assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & _).
  pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (HbSh & HbHull).
  assert (Hoffb : off_img buf (req_size (Z.max (slot_ser_defs.ser_cap op) 1))).
  { unfold a3_xb in HOFFb. inversion HOFFb as [|x l Hx Hl]. inversion Hl as [|y l2 Hy _]. exact Hy. }
  assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
  { unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
  rewrite Hreq in Hbceil, Hbapp, HbSh, HbHull, Hoffb.
  pose proof HBUF as ((Hr2 & Hrc) & HgB).
  assert (HNr : a3_r T1 now + 1 <= Z.max (slot_ser_defs.ser_cap op) 1) by lia.
  set (N := Z.max (slot_ser_defs.ser_cap op) 1) in *.
  assert (HgT : garr8 SEGS (rd W mem3) buf (a3_text T1 now)) by (apply garr8_app in HgB; exact (proj1 HgB)).
  set (BS := map (Z_to_bv 8) (a3_text T1 now)).
  assert (HBSm : map bv_unsigned BS = a3_text T1 now).
  { apply jsc_bytes_map. intros jj Hjj. exact (proj2 (HgT jj Hjj)). }
  pose proof (jscalar_in (a3_text T1 now) idx j kk ks kl Hjs) as Hidr.
  assert (Hidr' : idx < a3_r T1 now) by (unfold a3_r; unfold jlen in Hidr; lia).
  pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
  assert (SpR : spZ regs = d_A cx) by exact Rsp.
  assert (HA16 : d_A cx mod 16 = 0).
  { pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. rewrite GA32 in DA.
    replace (d_A cx) with ((2 * (d_A cx / 32)) * 16) by lia. apply Z_mod_mult. }
  assert (HV8 : (d_A cx + voff) mod 8 = 0).
  { pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. rewrite GA32 in DA.
    pose proof (Z.div_mod voff 8 ltac:(lia)) as DV. rewrite Hv8 in DV.
    replace (d_A cx + voff) with ((4 * (d_A cx / 32) + voff / 8) * 8) by lia. apply Z_mod_mult. }
  eapply SRr_mono.
  { apply (TJSC fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k regs buf idx (a3_r T1 now) (d_A cx + voff) BS []
      HJ HROD (jsc_consts_view W mem3 HROD) tjsc_roimg).
    - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [lia | exact Hret2].
    - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - exact Rgp.
    - exact Rtp.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact R13.
    - left. split; [|reflexivity]. left. unfold s0Z. rewrite getr_same by jsc_bvne.
      rewrite unsigned_lit_small by lia. lia.
    - rewrite SpR. exact HA16.
    - rewrite SpR. unfold TJSON_SCALAR_STK, ESTACK, LLVMF_STK. lia.
    - rewrite SpR. lia.
    - lia.
    - subst BS. rewrite length_map. reflexivity.
    - lia.
    - intros _. rewrite HBSm. split; [exact HgT|]. split; [lia|]. split; [lia|].
      split; [apply (amem_range_sub_app buf N buf (a3_r T1 now)); [exact Hbapp | lia | lia | lia | lia]|].
      split; [apply (block_shadow_range _ _ buf N buf (a3_r T1 now) HbSh); lia|].
      split.
      { intros s Hs. apply HbHull.
        pose proof (YCbq.shadow_mono (buf + a3_r T1 now - 1) (buf + N - 1) ltac:(lia)) as Sm.
        pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm) as Sd. lia. }
      split; [left; rewrite SpR; unfold TJSON_SCALAR_STK, ESTACK; lia|].
      split; [unfold off_img in *; lia|].
      left. lia.
    - lia.
    - exact HV8.
    - lia.
    - pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range. right. rewrite C3, C4. lia.
    - left. rewrite SpR. lia.
    - unfold off_img, IMG_TOP. right. lia.
    - intros a Ha. split; [left; unfold LLVMF_STK; lia | apply GSTK; lia].
    - apply (jsc_zs_range _ _ _ _ _ _ HZS); lia.
    - apply (jsc_zs_hull _ _ _ _ _ HZS); lia. }
  cbv beta. intros W2 c2 HW2 Hpost.
  unfold tjson_scalar_post in Hpost.
  destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & HFR2 & HAB & HM).
  rewrite HBSm, Hjs in HM. cbn beta iota in HM.
  destruct HM as (Q10 & V0 & V8 & V16 & K1 & K2 & K3 & K4 & K5 & K6).
  rewrite SpR in K1.
  assert (HFR4 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HFR2; exact HFR).
  assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k) by exact (conj HBASE (conj HJ2 HFR4)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly2 S2 W2 mem2 md2 k HCTX4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
  unfold LLVMF_STK in GSTK4.
  set (P := fun a => d_A cx - TJSON_SCALAR_STK <= a < d_A cx \/ d_A cx + voff <= a < d_A cx + voff + 20).
  assert (HK : d_kept P W mem3 W2 mem2).
  { intros a Ha HPa. apply K1; [exact Ha | intros Hc; apply HPa; left; exact Hc | intros Hc; apply HPa; right; exact Hc]. }
  assert (HPlo : forall a, a < alloc_ceiling -> ~ P a) by (intros a Ha [Hp|Hp]; unfold TJSON_SCALAR_STK, ESTACK in *; lia).
  assert (HPA : forall a, d_A cx <= a < d_A cx + 424 -> ~ P a) by (intros a Ha [Hp|Hp]; lia).
  assert (HPS : forall a, d_A cx + 472 <= a -> ~ P a) by (intros a Ha [Hp|Hp]; lia).
  assert (HJK : jsc_kept cx voff W mem3 W2 mem2).
  { split; [lia|]. split; [unfold TJSON_SCALAR_STK, ESTACK; lia|]. split; [lia|]. split; [lia|]. exact HK. }
  assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  pose proof HFRM as (E & HE & HREG & HFLAG & _).
  pose proof (d_hslots_of_frame cx h shf W mem3 HFRM) as HSL.
  pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
  assert (HSL4 : d_hslots cx h W2 mem2).
  { apply (d_hslots_kept cx h W W2 mem3 mem2); [|exact HSL].
    intros a Ha. apply HK; [lia | apply HPA; lia]. }
  assert (HFRM4 : d_frame cx h shf W2 mem2).
  { exists E. split; [exact HE|]. split; [|split].
    - unfold d_regions in HREG |- *. rewrite !Forall_cons_iff in HREG |- *.
      destruct HREG as (HRS & HRA & HRF & HRH & _).
      split; [|split; [|split; [|split; [|exact (Forall_nil _)]]]].
      + apply (jsc_region_ok_kept E _ _ _ (-104) 0 HRS); [vm_compute; reflexivity | |].
        * cbn [YP09.r_base base_val]; unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl).
          change (bv_unsigned (getr (c_regs cx) 2)) with (d_S cx).
          intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPS; lia].
        * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
      + apply (jsc_region_ok_kept E _ _ _ 0 424 HRA); [vm_compute; reflexivity | |].
        * cbn [YP09.r_base base_val]; unfold AT_STK. rewrite E60. unfold w64. rewrite unsigned_lit_small by lia.
          intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPA; lia].
        * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]; unfold AT_STK. rewrite E60. unfold w64.
          rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GSTK4. lia.
      + apply (jsc_region_ok_kept E _ _ _ 0 24 HRF); [vm_compute; reflexivity | |].
        * cbn [YP09.r_base base_val]; unfold AT_STK. rewrite EF. unfold w64. rewrite unsigned_lit_small by lia.
          intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPlo; lia].
        * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]; unfold AT_STK. rewrite EF. unfold w64.
          rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GFpres4.
          unfold DFRAME_SIZE in Ho. lia.
      + apply (jsc_region_ok_kept E _ _ _ 0 384 HRH); [vm_compute; reflexivity | |].
        * unfold fshadow_region. cbn [YP09.r_base base_val]; unfold AT_STK. rewrite ESH. unfold w64.
          rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
          intros a Ha. apply (mbyte_of_aview SEGS).
          apply HK; [unfold shadow_addr, SHADOW_OFF in *; lia | apply HPlo; unfold shadow_addr, SHADOW_OFF in *; lia].
        * unfold fshadow_region. cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]; unfold AT_STK. rewrite ESH. unfold w64.
          rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
          intros o Ho. apply (apresent_writable SEGS). apply GFsh4. unfold DFRAME_SH in Ho. lia.
    - rewrite <- HFLAG. apply jsc_rdword_kept. intros kk0 Hkk0.
      change (fs_frame_bytes DFRAME_CLASS) with 4096. apply HK; [lia | apply HPlo; lia].
    - destruct HSL4 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
      split; [exact Q5|]. split; [exact Q6|]. exact Q7. }
  assert (HSHD4 : d_shadow cx shf W2 mem2).
  { intros kk0 Hkk0. rewrite <- (HSHD kk0 Hkk0). unfold DFRAME_SH in Hkk0.
    apply HK; [unfold shadow_addr, SHADOW_OFF; lia | apply HPlo; unfold shadow_addr, SHADOW_OFF; lia]. }
  pose proof (DBCK LAWS cx h n (a3_xb buf op) shf shf ly3 S3 W mem3 ly2 S2 W2 mem2 md2 k
    (d_A cx - TJSON_SCALAR_STK) (d_A cx + 472) HBODY (conj HBASE HJ2)
    ltac:(unfold TJSON_SCALAR_STK, ESTACK, LLVMF_STK; lia) ltac:(lia)
    ltac:(intros a Ha Hlh; apply HK; [exact Ha | intros [Hp|Hp]; apply Hlh; cbv beta; unfold TJSON_SCALAR_STK, ESTACK in *; lia])
    ltac:(rewrite HAB; apply Permutation_refl) HFRM4 HSHD4) as HBODY4.
  assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
  assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
  assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
  assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr regs2 24 = getr regs 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
  assert (P25 : getr regs2 25 = getr regs 25) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
  assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
  assert (P27 : getr regs2 27 = getr regs 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
  assert (KV : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 424 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) nb v -> val_mem SEGS (rd W2 mem2) (d_A cx + off) nb v).
  { intros off nb v Hoff Hnb Hv. apply (jsc_val_mem_kept P W mem3 W2 mem2); [exact HK | lia | lia | | exact Hv].
    intros x Hx. apply HPA. lia. }
  unfold jsc_out, jcut, d_arm_at_pf, d_at.
  split.
  { destruct HFROM as (HA3 & HW0 & HT0 & HEX). split; [exact HA3|].
    split; [eapply wle_trans; [exact HW0 | exact HW2]|]. split; [exact HT0 | exact HEX]. }
  exists fq, ly2, S2, regs2, mem2, md2, k, acc.
  split; [unfold cfg_at, w64; rewrite R1; reflexivity|].
  split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR4|]. split; [exact Hk|].
  split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
  split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ in *; rewrite P2; exact Rsp|].
    split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
    split; [rewrite P9; exact Rs1|]. split; [rewrite P19; exact Rs3|]. split; [rewrite P18; exact Rs2|].
    split; [rewrite P20; exact Rs4|].
    rewrite P27; exact Rs11. }
  split.
  { split; [rewrite P26; exact R26|]. split; [rewrite P24; exact R24|]. split; [rewrite P25; exact R25|].
    split; [exact Q10|].
    exact (HRk regs regs2 HP HR). }
  split.
  { pose proof HSP1 as ((H208 & H320) & H192 & H200).
    split; [split; [split|split]|].
    - apply KV; [lia | cbn; lia | exact H208].
    - apply KV; [lia | cbn; lia | exact H320].
    - apply KV; [lia | cbn; lia | exact H192].
    - apply KV; [lia | cbn; lia | exact H200].
    - split.
      { pose proof HTAB as (HTex & HgOT). split; [exact HTex|].
        destruct HTex as (rem & _ & HAP). pose proof HAP as (HlenT1 & _).
        apply (jsc_garr8_kept P W mem3 W2 mem2); [exact HK | unfold d_obj, dobj_off; lia | | | exact HgOT].
        - rewrite length_map, HlenT1. unfold d_obj, dobj_off. lia.
        - intros x Hx. rewrite length_map, HlenT1 in Hx. unfold d_obj, dobj_off in Hx. apply HPlo. lia. }
      split.
      { split; [lia|].
        apply (jsc_garr8_kept P W mem3 W2 mem2); [exact HK | lia | | | exact HgB].
        - rewrite length_app. cbn [length]. unfold a3_r in *. lia.
        - intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. unfold a3_r in *. apply HPlo. lia. }
      split; [exact (HXk W mem3 W2 mem2 HX HJK)|].
      split; [exact V0|]. split; [exact V8 | exact V16]. }
  split.
  { pose proof HSP0 as (H208 & H320).
    split; [apply KV; [lia | cbn; lia | exact H208] | apply KV; [lia | cbn; lia | exact H320]]. }
  exact HBODY4.
Qed.

End h.
End f.
End d.
