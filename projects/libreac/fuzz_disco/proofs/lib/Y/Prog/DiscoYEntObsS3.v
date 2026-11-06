(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v, with its module paths changed; 120 of its 294 lines of code are new or changed and 814 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma s3_optZ_dec : forall x y : option Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.
Lemma s3_u_at_fb : forall (S : list byte) (k : nat), (k < length S)%nat -> u_at S (Z.of_nat k) 1 = CtrlParsed.fb S k.
Proof.
intros S k. unfold u_at, sub, CtrlParsed.fb. rewrite Nat2Z.id. revert S. induction k as [|k IH]; intros [|b S] Hk; cbn [length] in Hk; try lia.
- cbn [skipn firstn nth bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
- cbn [skipn nth]. apply IH. lia.
Qed.
Lemma s3_sight_S12 : forall S : list byte, disco_classify_c.sighting_ok S -> sighting_S1 S /\ sighting_S2 S.
Proof.
intros S (HL & HR & HD).
assert (Hb : 0 <= CtrlParsed.fu S 8 4 < 2 ^ 32).
{ unfold CtrlParsed.fu, CtrlParsed.fld. pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn 8 S))).
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 8 S))) as Hu. rewrite length_firstn, length_skipn, HL in Hu. cbn in Hu. lia. }
assert (SW : bv_swrap 32 (CtrlParsed.fu S 8 4) = CtrlParsed.s32 (CtrlParsed.fu S 8 4)).
{ unfold CtrlParsed.s32. change (bv_swrap 32 (CtrlParsed.fu S 8 4)) with ((CtrlParsed.fu S 8 4 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
  destruct (Z.ltb_spec (CtrlParsed.fu S 8 4) (2 ^ 31)); lia. }
split.
- unfold sighting_S1, s_role, s32_at. change (u_at S 8 4) with (CtrlParsed.fu S 8 4). rewrite SW. lia.
- unfold sighting_S2, s_hd, s_din, s_dout.
  change 12 with (Z.of_nat 12). change 13 with (Z.of_nat 13). change 14 with (Z.of_nat 14).
  rewrite !s3_u_at_fb by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma s3_in_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Ha)|Hr].
- exists s. split; [exact Hs | exact Ha].
- exact (pa_relro_img a Hr).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis TTOBS : ReacDiscoTableObserve.treac_disco_table_observe_spec B.

Lemma s3_tobs_frame : forall cx ly3 S3 W3 m3 md3 k3 W4 m4,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 ->
  ReacDiscoTableObserve.treac_disco_table_observe_kept B ly3 S3 W3 m3 W4 m4 (d_A cx) (d_obj cx OT) ->
  (forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OT <= a < d_obj cx OT + 400) ->
     aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall b m j, In (b, m) (ablocks B ly3 S3) -> 0 <= j < req_size m ->
     aview SEGS (w_H W4) m4 (b + j) = aview SEGS (w_H W3) m3 (b + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
Proof.
intros cx ly3 S3 W3 m3 md3 k3 W4 m4 Hc3 (K1 & K2 & K3 & K4 & K5 & K6).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 m3 md3 k3 Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
split; [|split; [|split; [|split]]].
- intros a Ha. apply K1; unfold d_obj, dobj_off, ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK in *; lia.
- intros a Ha Ht. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact Ht].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
- intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin).
  + right. unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia. unfold d_obj, dobj_off, shadow_addr, SHADOW_OFF in *. lia.
- intros b m j Hin Hj. apply (K2 b m j Hin Hj).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 m3 md3 b m DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa in Hd. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd.
  unfold d_obj, dobj_off. lia.
- exact K3.
Qed.

Lemma s3_oc_tobs_keep : forall cx h i n now op nb fr len Sg T T' regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 ->
  oc B cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 ->
  ReacDiscoTableObserve.treac_disco_table_observe_kept B ly3 S3 W3 m3 W4 m4 (d_A cx) (d_obj cx OT) ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) -> aregs_preserved regs regs' ->
  length T' = 400%nat -> garr8 SEGS (rd W4 m4) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T') ->
  disco_table_c.table_ok T' ->
  garr8 SEGS (rd W4 m4) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) ->
  oc B cx h i n now op nb fr len Sg T' regs' ly4 S4 W4 m4.
Proof.
intros cx h i n now op nb fr len Sg T T' regs ly3 S3 W3 m3 md3 k3 regs' ly4 S4 W4 m4 md4 k4 Hc3 Hc4 HOC HKT HPm HP HTl' HT' HTok' HSg'.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 m3 md3 k3 Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
destruct (s3_tobs_frame cx ly3 S3 W3 m3 md3 k3 W4 m4 Hc3 HKT) as (KA & KFr & KSh & KB & KI).
assert (VA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_S cx ->
  val_mem SEGS (rd W3 m3) a nn v -> val_mem SEGS (rd W4 m4) a nn v).
{ intros a nn v H1 H2 Hv. apply (oy_val_mem_keep W3 W4 m3 m4 a nn v); [|exact Hv]. intros j Hj. apply KA. lia. }
unfold oc.
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj HSg' (conj HSf
  (conj _ (conj Hlen (conj Hnb (conj HTl' (conj HT' (conj HTok' _))))))))))))))))).
- exact (oy_rL_pres B cx regs regs' HP HrL).
- destruct Hsp0 as (S1 & S2). split; apply VA; try exact S1; try exact S2; cbn; lia.
- destruct Hfrm as (F1 & F2 & F0 & F3). split; [exact F1|]. split; [exact F2|]. split; [exact F0|].
  destruct (Z.eq_dec fr 0) as [E0|E0].
  + rewrite (F2 E0). exact (garr8_nil SEGS _ _).
  + assert (Hin : In (fr, len) (ablocks B ly3 S3)).
    { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
      rewrite (proj2 (Z.eqb_neq fr 0) E0). left. reflexivity. }
    assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    apply (oy_garr8_keep W3 W4 m3 m4 fr _); [|exact F3]. intros j Hj.
    rewrite length_map, length_firstn in Hj. apply (KB fr len (Z.of_nat j) Hin). lia.
- destruct HREC as (R1 & R2 & R3 & R4).
  split; [apply VA; [lia | cbn; lia | exact R1]|]. split; [apply VA; [lia | cbn; lia | exact R2]|].
  split; [apply VA; [lia | cbn; lia | exact R3]|]. apply VA; [lia | cbn; lia | exact R4].
- assert (Hjr : d_jr B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4) by exact (conj (proj1 Hc4) (proj1 (proj2 Hc4))).
  assert (Hfr4 : d_frame cx h dsh_rec W4 m4).
  { apply (oy_frame_keep B MT XM_LIB RLO RHI tfib_K cx h dsh_rec W3 W4 m3 m4 ly4 S4 md4 k4 LAWS Hframe Hc4).
    intros a [Ha|[Ha|[Ha|Ha]]]; [apply KA; exact Ha | apply KFr | apply KFr | apply KSh; exact Ha];
    unfold d_obj, dobj_off; lia. }
  assert (Hsh4 : d_shadow cx dsh_rec W4 m4).
  { apply (oy_d_shadow_keep cx dsh_rec W3 W4 m3 m4 Hshadow). intros kk Hkk. apply KSh. unfold DFRAME_SH in Hkk. lia. }
  apply (BTOBS LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4
    (d_A cx - ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK) (d_A cx) [OT]
    (fun a => aview SEGS (w_H W4) m4 a <> aview SEGS (w_H W3) m3 a)
    Hbody Hjr ltac:(unfold ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK; lia) ltac:(lia)).
  + intros a HR.
    assert (Hw : (d_A cx - ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK <= a < d_A cx) \/
      ~ (d_A cx - ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK <= a < d_A cx)) by lia.
    destruct Hw as [Hw|Hw]; [left; exact Hw|].
    assert (Ht : (d_obj cx OT <= a < d_obj cx OT + 400) \/ ~ (d_obj cx OT <= a < d_obj cx OT + 400)) by lia.
    destruct Ht as [Ht|Ht]; [right; left; apply Exists_cons_hd; unfold d_objr, dobj_size; exact Ht|].
    right; right. intros Hrd. apply HR.
    destruct Hrd as [Ho|[Ho|[Ho|[Ho|[Hh|[Hin|[Hro|Hcn]]]]]]].
    * exfalso. apply Ht. unfold d_objr, dobj_size in Ho. exact Ho.
    * apply KFr; unfold d_objr, d_obj, dobj_off, dobj_size in *; lia.
    * apply KFr; unfold d_objr, d_obj, dobj_off, dobj_size in *; lia.
    * apply KFr; unfold d_objr, d_obj, dobj_off, dobj_size in *; lia.
    * assert (HinH : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
      { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)).
        apply in_or_app. right. left. reflexivity. }
      replace a with (h + (a - h)) by lia. apply (KB h HUNT_SIZE (a - h) HinH). unfold req_size, HUNT_SIZE in *. cbn. lia.
    * destruct Hin as (Hn0 & Hin).
      pose proof (proj1 Hc3) as ((_ & _ & _ & _ & Hpn & _) & _).
      destruct Hpn as [(E & _)|(_ & HinP)]; [lia|].
      assert (HinP3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
      { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)).
        apply in_or_app. right. right. exact HinP. }
      replace a with (c_p cx + (a - c_p cx)) by lia. apply (KB (c_p cx) (c_n cx) (a - c_p cx) HinP3).
      unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); lia.
    * destruct Hro as (Hrop & Hno & Hne). exact (KI a (s3_in_roP_img a Hrop) Hno Hne).
    * destruct DCAN as (AIL & KC).
      destruct (ail_env _ _ _ AIL a) as (Hai & Hno & Hne);
        [unfold aenv_addr; left; apply (ail_owned_core _ _ _ AIL a); unfold aenv_core; rewrite KC; right; right; right; exact Hcn|].
      exact (KI a Hai Hno Hne).
  + intros a _ HnR. destruct (s3_optZ_dec (aview SEGS (w_H W4) m4 a) (aview SEGS (w_H W3) m3 a)) as [E|E];
      [exact E | exfalso; exact (HnR E)].
  + constructor; [|constructor]. exists T'. split; [exact HTl'|]. split; [exact HT' | exact HTok'].
  + exact HPm.
  + exact Hfr4.
  + exact Hsh4.
Qed.

Theorem ob_s34 : ob_seg34 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & ai & ow & HOC & Hfind & How & Hsp22 & H360 & Hra & Ha0 & Ha1 & Ha2 & Ha3 & HrT & H22 & H21).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac. pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HB.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HrL as (Hsp & Hgp & Htp & _).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
destruct HSf as (Hs50 & Hs1 & Hs2 & Hs3 & Hs4 & HSok & Hs5).
destruct (s3_sight_S12 Sg HSok) as (HS1 & HS2).
eapply SRr_mono.
{ apply (TTOBS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W mem3 md3 k regs (d_obj cx OT) (d_obj cx OS) ow now T Sg HJ Himg).
  - rewrite Hra. unfold w64. apply ret_ok_codeptr_v; [unfold OB_TO_RET; lia | reflexivity].
  - unfold raZ. rewrite Hra. unfold w64. rewrite unsigned_lit_small by (unfold OB_TO_RET; lia).
    unfold YImgTop.IMG_LO in HBlo. unfold OB_TO_RET. lia.
  - exact Hgp.
  - exact Htp.
  - exact Ha0.
  - exact Ha1.
  - exact Ha2.
  - exact Ha3.
  - lia.
  - exact Hnow.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - right. rewrite Hsp. unfold d_obj, dobj_off, ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. apply Hawr. unfold d_obj, dobj_off in Ha. unfold DFRAME_SIZE. lia.
  - exact (oy_ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => oy_dsh_rec_t kk ltac:(lia))).
  - exact (oy_hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact HT.
  - exact HTl.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - unfold d_obj, dobj_off. lia.
  - intros a Ha. apply (proj2 (Hawr a ltac:(unfold d_obj, dobj_off in Ha; unfold DFRAME_SIZE; lia))).
  - exact (oy_ra_frame cx dsh_rec W mem3 2992 24 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => oy_dsh_rec_s kk ltac:(lia))).
  - right. rewrite Hsp. unfold d_obj, dobj_off, ReacDiscoTableObserve.REAC_DISCO_TABLE_OBSERVE_STK, ESTACK, LLVMF_STK in *. lia.
  - exact (oy_hull_frame cx dsh_rec W mem3 2992 24 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact HSg.
  - exact HSgl.
  - left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|]. rewrite Efa.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. unfold d_obj, dobj_off. lia.
  - right. unfold d_obj, dobj_off. lia.
  - exact (proj1 HTok).
  - exact (proj1 (proj2 HTok)).
  - exact (proj1 (proj2 (proj2 HTok))).
  - exact HS1.
  - exact HS2. }
cbv beta. intros W2 c2 _ HQ. unfold ReacDiscoTableObserve.treac_disco_table_observe_post in HQ.
destruct HQ as (ly4 & S4 & regs4 & mem4 & md4 & T' & ret & -> & HJ2 & HP & Hret & Hfr4 & HPm & HKT & HT' & HTl' & HSg' &
  Hmodel & T1' & T2' & T3' & T4').
rewrite Hsp in HKT.
assert (Hc4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k).
{ split; [exact Hbase|]. split; [exact HJ2|]. rewrite Hfr4. exact Hfrs. }
assert (HTok' : disco_table_c.table_ok T') by exact (conj T1' (conj T2' (conj T3' (T4' (proj2 (proj2 (proj2 HTok))))))).
pose proof (s3_oc_tobs_keep cx h i n now op nb fr len Sg T T' regs ly3 S3 W mem3 md3 k regs4 ly4 S4 W2 mem4 md4 k
  Hc3 Hc4 HOC HKT HPm HP HTl' HT' HTok' HSg') as HOC4.
destruct (s3_tobs_frame cx ly3 S3 W mem3 md3 k W2 mem4 Hc3 HKT) as (KA & _ & _ & _ & _).
assert (VA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_S cx ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W2 mem4) a nn v).
{ intros a nn v H1 H2 Hv. apply (oy_val_mem_keep W W2 mem3 mem4 a nn v); [|exact Hv]. intros j Hj. apply KA. lia. }
assert (HoT : obT cx now Sg T T' ai ow ret W2 mem4).
{ destruct Hsp22 as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
  unfold obT, ob_sp22.
  refine (conj HTl (conj HTok (conj Hfind (conj How (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ _)))))))))) (conj _ Hmodel)))))); apply VA; try assumption; cbn; lia. }
rewrite Hra.
apply (oy_dat B MT XM_LIB RLO RHI tfib_K cx OB_TO_RET kmax accmax _ fq ly4 S4 regs4 mem4 md4 k acc W2 MT_TRIV HFRM0 Hc4
  ltac:(lia) Hacc).
exists T, T', ai, ow, ret. split; [exact HOC4|]. split; [exact HoT|].
split; [destruct HrT as (R25 & R26); split;
  [transitivity (getr regs 25%bv); [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact R25]
  |transitivity (getr regs 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact R26]]|].
split; [exact Hret|].
split; [transitivity (getr regs 22%bv); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact H22]|].
transitivity (getr regs 21%bv); [exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact H21].
Qed.

End h.
End f.
End d.
