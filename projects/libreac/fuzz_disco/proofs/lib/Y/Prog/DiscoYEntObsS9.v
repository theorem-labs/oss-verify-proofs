(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v, with its module paths changed; 138 of its 219 lines of code are new or changed and 907 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt FindEntry RoleOf DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Context {PX : PAXcalls lib_both3_0_listing}.

Lemma o9_obT_slots : forall cx now Sg T T' ai ow ret (W3 W4 : world SEGS) m3 m4,
  (forall a nn v, 0 <= a -> a + Z.of_nat nn <= 448 ->
     val_mem SEGS (rd W3 m3) (d_A cx + a) nn v -> val_mem SEGS (rd W4 m4) (d_A cx + a) nn v) ->
  obT cx now Sg T T' ai ow ret W3 m3 -> obT cx now Sg T T' ai ow ret W4 m4.
Proof.
intros cx now Sg T T' ai ow ret W3 W4 m3 m4 KA
  (L & Ok & F & Ow & (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11) & V12 & M).
unfold obT, ob_sp22.
refine (conj L (conj Ok (conj F (conj Ow (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
  (conj _ _)))))))))) (conj _ M)))))); apply KA; try assumption; cbn; lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DRO : d_ro_hyps B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis BPCALL : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TROLE : RoleOf.trole_of_spec B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Lemma o9_oc_keep : forall cx h i n now op nb fr len Sg T regs regs' ly3 S3 (W3 : world SEGS) m3 md3 k3
    ly4 S4 (W4 : world SEGS) m4 md4 k4 STK kc,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 ->
  oc B cx h i n now op nb fr len Sg T regs ly3 S3 W3 m3 ->
  0 <= STK -> STK + 640 <= LLVMF_STK ->
  ajournal SEGS B STK (d_A cx) [] ly3 S3 W3 m3 md3 [] ly4 S4 W4 m4 md4 kc ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  aregs_preserved regs regs' ->
  oc B cx h i n now op nb fr len Sg T regs' ly4 S4 W4 m4 /\
  (forall a nn v, 0 <= a -> a + Z.of_nat nn <= 448 ->
     val_mem SEGS (rd W3 m3) (d_A cx + a) nn v -> val_mem SEGS (rd W4 m4) (d_A cx + a) nn v).
Proof.
intros cx h i n now op nb fr len Sg T regs regs' ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 STK kc
  Hc3 Hc4 HOC HS0 HS1 HJ1 HPm HP.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & _).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 m3 md3 k3 Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
assert (FFB : fs_frame_bytes DFRAME_CLASS = 4096) by reflexivity.
assert (FF8 : fs_frame_bytes DFRAME_CLASS / 8 = 512) by reflexivity.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10 & _ & K12 & _).
assert (KEEP : forall a, (d_A cx <= a < d_S cx \/ d_FB cx <= a < d_FB cx + 4096 \/
    shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
    aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a [Ha|[Ha|Ha]].
  - apply K9; unfold LLVMF_STK in *; lia.
  - apply (K12 DFRAME_CLASS (c_fpos cx) a Hfin); [|apply inFP_nil].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa, FFB. lia.
  - apply (K12 DFRAME_CLASS (c_fpos cx) a Hfin); [|apply inFP_nil].
    right. unfold in_zr. cbn [fst snd]. rewrite Efa, FF8. lia. }
assert (KVA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_S cx ->
  val_mem SEGS (rd W3 m3) a nn v -> val_mem SEGS (rd W4 m4) a nn v).
{ intros a nn v H1 H2 Hv. apply (oy_val_mem_keep W3 W4 m3 m4 a nn v); [|exact Hv].
  intros j Hj. apply KEEP. left. lia. }
assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W3 m3) a l -> garr8 SEGS (rd W4 m4) a l).
{ intros a l H1 H2 Hg. apply (oy_garr8_keep W3 W4 m3 m4 a l); [|exact Hg].
  intros j Hj. apply KEEP. right. left. lia. }
assert (Hframe4 : d_frame cx h dsh_rec W4 m4).
{ apply (oy_frame_keep B MT XM_LIB RLO RHI tfib_K cx h dsh_rec W3 W4 m3 m4 ly4 S4 md4 k4 LAWS Hframe Hc4).
  intros a [Ha|[Ha|[Ha|Ha]]]; apply KEEP; [left | right; left | right; left | right; right]; lia. }
assert (Hshadow4 : d_shadow cx dsh_rec W4 m4).
{ apply (oy_d_shadow_keep cx dsh_rec W3 W4 m3 m4 Hshadow).
  intros kk Hkk. apply KEEP. right. right. unfold DFRAME_SH in Hkk. lia. }
assert (Hjr4 : d_jr B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4)
  by exact (conj (proj1 Hc4) (proj1 (proj2 Hc4))).
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly4 S4 W4 m4).
{ apply (BPCALL LAWS DRO DCAN cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W3 m3 md3 ly4 S4 W4 m4 md4 k4
    STK (d_A cx) [] kc Hbody Hjr4 HJ1 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia)
    ltac:(intros a Ha; right; right; exact Ha)
    ltac:(intros (a & Ha & _); exfalso; exact (inFP_nil a Ha))
    HPm Hframe4 Hshadow4). }
split; [|intros a nn v Ha Hb Hv; apply (KVA (d_A cx + a) nn v ltac:(lia) ltac:(lia) Hv)].
unfold oc.
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj _ (conj HSf
  (conj _ (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok _))))))))))))))))).
- exact (oy_rL_pres B cx regs regs' HP HrL).
- destruct Hsp0 as (P1 & P2). split; apply KVA; try exact P1; try exact P2; cbn; lia.
- destruct Hfrm as (F1 & F2 & F0 & F3). split; [exact F1|]. split; [exact F2|]. split; [exact F0|].
  destruct (Z.eq_dec fr 0) as [E0|E0].
  + rewrite (F2 E0). exact (garr8_nil SEGS _ _).
  + assert (Hin : In (fr, len) (ablocks B ly3 S3)).
    { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
      rewrite (proj2 (Z.eqb_neq fr 0) E0). left. reflexivity. }
    assert (Hin4 : In (fr, len) (ablocks B ly4 S4))
      by (apply (Permutation_in _ (Permutation_sym HPm)); exact Hin).
    assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    assert (HL : Z.of_nat (length (map (fun b : byte => bv_unsigned b)
      (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))) <= len)
      by (rewrite length_map, length_firstn; lia).
    apply (oy_garr8_keep W3 W4 m3 m4); [|exact F3]. intros j Hj.
    exact (K10 fr len (Z.of_nat j) Hin Hin4 ltac:(lia) (inFP_nil _)).
- apply KGF; [unfold d_obj, dobj_off; lia | rewrite length_map, HSgl; unfold d_obj, dobj_off; cbn; lia | exact HSg].
- destruct HREC as (R1 & R2 & R3 & R4).
  split; [apply KVA; [lia | cbn; lia | exact R1]|]. split; [apply KVA; [lia | cbn; lia | exact R2]|].
  split; [apply KVA; [lia | cbn; lia | exact R3]|]. apply KVA; [lia | cbn; lia | exact R4].
- apply KGF; [unfold d_obj, dobj_off; lia | rewrite length_map, HTl; unfold d_obj, dobj_off; cbn; lia | exact HT].
- exact Hbody4.
Qed.

Theorem ob_s78 : ob_seg78 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HoT & HrT & H23 & Hai & Hrole & Hra & Ha0 & Ha1).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HrL as (Hsp & _).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
pose proof (oy_pre8 B MT XM_LIB RLO RHI tfib_K cx regs ly3 S3 W mem3 md3 k TROLE_OF_STK OB_RO_RET LAWS Hc3 HrL Hra
  ltac:(unfold OB_RO_RET; lia) ltac:(unfold OB_RO_RET; reflexivity)
  ltac:(unfold TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK; lia)
  ltac:(unfold TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia)) as HPRE.
eapply SRr_mono.
{ apply (TROLE fq ly3 S3 W regs mem3 md3 [] (d_obj cx OT) (d_obj cx OS) T' (s_mac Sg) HPRE Himg Ha0 Ha1).
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact HTl.
  - exact HT.
  - change (length (firstn 6 Sg) = 6%nat). rewrite length_firstn, HSgl. reflexivity.
  - change (garr8 SEGS (mrestrict (w_H W) mem3) (d_obj cx OS) (map bv_unsigned (firstn 6 Sg))). rewrite <- firstn_map.
    replace (d_obj cx OS) with (d_obj cx OS + Z.of_nat 0) by lia.
    exact (garr8_sub_x SEGS _ _ _ 0 6 HSg ltac:(rewrite length_map; lia)).
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - exact (oy_ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => oy_dsh_rec_t kk ltac:(lia))).
  - exact (oy_hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (oy_ra_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => oy_dsh_rec_s kk ltac:(lia))).
  - exact (oy_hull_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - left. rewrite Hsp. unfold d_obj, dobj_off, TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - left. rewrite Hsp. unfold d_obj, dobj_off, TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. unfold d_obj, dobj_off. lia.
  - exact (proj1 HTok).
  - exact (proj1 (proj2 HTok)). }
cbv beta. intros W2 c2 _ HQ. unfold trole_of_post, apost_base in HQ.
destruct HQ as (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & HFxr & HFxc & HJ1 & HP & HPm & r & v & Hfind & Hv & Hr10 & Hvr).
assert (HFRM1 : lib.Lib.FP.frm0 (@YK11.fp_csr fx')) by (destruct HFxc as [Ec|Ec]; [rewrite Ec; exact HFRM0 | exact Ec]).
rewrite Hsp in HJ1.
pose proof (oy_post B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k TROLE_OF_STK ly4 S4 W2 mem4 md4 LAWS Hc3
  ltac:(unfold TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK; lia)
  ltac:(unfold TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia) HJ1) as Hc4.
destruct (o9_oc_keep cx h i n now op nb fr len Sg T' regs regs4 ly3 S3 W mem3 md3 k ly4 S4 W2 mem4 md4 (k + 0)
  TROLE_OF_STK 0 Hc3 Hc4 HOC ltac:(unfold TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK; lia)
  ltac:(unfold TROLE_OF_STK, TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia) HJ1 HPm HP) as (HOC4 & KA).
rewrite Hra.
apply (oy_dat B MT XM_LIB RLO RHI tfib_K cx OB_RO_RET kmax accmax _ fx' ly4 S4 regs4 mem4 md4 (k + 0) acc W2 MT_TRIV HFRM1 Hc4
  ltac:(lia) Hacc).
cbv beta. exists T, T', ai, ow, ret, r, v.
split; [exact HOC4|].
split; [exact (o9_obT_slots cx now Sg T T' ai ow ret W W2 mem3 mem4 KA HoT)|].
split; [destruct HrT as (R25 & R26); split;
  [transitivity (getr regs 25%bv); [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact R25]
  |transitivity (getr regs 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact R26]]|].
split; [transitivity (getr regs 23%bv); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact H23]|].
split; [exact Hai|]. split; [exact Hrole|]. split; [exact Hr10|]. split; [exact Hfind | exact Hv].
Qed.
End h.
End f.
End d.
