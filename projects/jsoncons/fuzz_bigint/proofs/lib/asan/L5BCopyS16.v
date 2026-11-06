(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun Bo0_code_91368_92368 Bo0_code_92368_93368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core
     L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BAlloc L5BCopy16P.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5BCPS16.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5BCPY16P.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
(* [comment removed for export] *)
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma SCR_EQ : COPY_SCR = 4256. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition bytes256 : list Z := map Z.of_nat (seq 0 256).
Lemma byte_enum2 (f : Z -> Z -> bool) : forallb (fun x => forallb (f x) bytes256) bytes256 = true -> forall x y, 0 <= x < 256 -> 0 <= y < 256 -> f x y = true.
Proof.
  intros H x y Hx Hy. rewrite forallb_forall in H.
  assert (Ix : In x bytes256). { unfold bytes256. apply in_map_iff. exists (Z.to_nat x). split. lia. apply in_seq. lia. }
  assert (Iy : In y bytes256). { unfold bytes256. apply in_map_iff. exists (Z.to_nat y). split. lia. apply in_seq. lia. }
  specialize (H x Ix). rewrite forallb_forall in H. exact (H y Iy).
Qed.
Lemma fb_inl fbo fby : 0 <= fbo < 256 -> 0 <= fby < 256 ->
  ((4 * (fbo / 4)) mod 2 ^ 64 + Z.land fby 2) mod 2 ^ 64 = copy_fb fbo fby false /\ 0 <= copy_fb fbo fby false < 256 /\ Z.testbit (copy_fb fbo fby false) 0 = false.
Proof.
  intros Hx Hy.
  pose proof (byte_enum2 (fun x y => Z.eqb (((4 * (x / 4)) mod 2 ^ 64 + Z.land y 2) mod 2 ^ 64) (copy_fb x y false) && (0 <=? copy_fb x y false) && (copy_fb x y false <? 256)
                                    && negb (Z.testbit (copy_fb x y false) 0)) ltac:(vm_compute; reflexivity) fbo fby Hx Hy) as E.
  cbn beta in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E E2]. apply andb_prop in E as [E0 E1].
  split. apply Z.eqb_eq; exact E0. split. split. apply Z.leb_le; exact E1. apply Z.ltb_lt; exact E2. destruct (Z.testbit _ 0); [discriminate|reflexivity].
Qed.
Lemma fb_dyn fbo fby : 0 <= fbo < 256 -> 0 <= fby < 256 ->
  Z.lor (Z.land fby 2) (Z.land (((2 * (fbo / 2)) mod 2 ^ 64 + 1) mod 2 ^ 64) 253) = copy_fb fbo fby true /\ 0 <= copy_fb fbo fby true < 256
  /\ Z.testbit (copy_fb fbo fby true) 0 = true.
Proof.
  intros Hx Hy.
  pose proof (byte_enum2 (fun x y => Z.eqb (Z.lor (Z.land y 2) (Z.land (((2 * (x / 2)) mod 2 ^ 64 + 1) mod 2 ^ 64) 253)) (copy_fb x y true) && (0 <=? copy_fb x y true)
                                    && (copy_fb x y true <? 256) && Z.testbit (copy_fb x y true) 0) ltac:(vm_compute; reflexivity) fbo fby Hx Hy) as E.
  cbn beta in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E E2]. apply andb_prop in E as [E0 E1].
  split. apply Z.eqb_eq; exact E0. split. split. apply Z.leb_le; exact E1. apply Z.ltb_lt; exact E2. exact E3.
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 860160 884736 /\ L5.u64_at RSEGS MV 911160 2147450880 /\ L5.u32_at RSEGS MV 911168 1.
Proof.
  intros HH. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG 911160 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG 911168 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

(* [comment removed for export] *)
Lemma obj_vis LB FF LK cr A M model o :
  ri_inv HI LB FF LK cr A M (vml_of model) -> aobj FF o 32 -> shadow_zero M o 4 ->
  let MV := mrestrict (ahid A model) M in
  (forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v)
  /\ (forall v, L5.u8_at RSEGS M o v -> L5.u8_at RSEGS MV o v)
  /\ L5KA.zeros_at MV (o / 8 + SB) 4 /\ L5.writable RSEGS MV o 32.
Proof.
  intros HH AOB SZ MV.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 0 0 HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & _). change (32 / 8) with 4 in OVSH.
  split. { intros a v Ha Hc. apply (proj2 (u64_at_vis _ M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Ha; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Ha OR; lia))). exact Hc. }
  split. { intros v Hc. apply (proj2 (u8_at_vis _ M o v ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact Hc. }
  split. { apply (proj2 (zeros_at_vis _ M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis _ M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia.
Qed.

(* [comment removed for export] *)
Definition sobj (s0 o sz : Z) : Prop := s0 <= o /\ o + sz <= ar_sptop ar /\ o mod 8 = 0.
Lemma sobj_facts LB FF LK cr A M model o sz s0 sp scr :
  ri_inv HI LB FF LK cr A M (vml_of model) -> sobj s0 o sz -> 0 < sz -> sz mod 8 = 0 ->
  0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 -> ahl_ceil ar <= s0 -> sp <= s0 ->
  let H := ahid A model in
  (0x634000 <= o /\ s0 <= o /\ o + sz <= 2 ^ 47 /\ o mod 8 = 0 /\ (o / 8) * 8 = o)
  /\ (0x7fff7000 + 17592186048512 <= o \/ o + sz <= 0x7fff7000)
  /\ True /\ avis H o sz /\ avis H (o / 8 + SB) (sz / 8)
  /\ (forall i, 0 <= i < sz -> aclient L ar LB FF sp scr (o + i))
  /\ (forall i, 0 <= i < sz / 8 -> aclient L ar LB FF sp scr (o / 8 + SB + i)).
Proof.
  intros HH (O1 & O2 & O8) Hsz Hsz8 SPT HC HS H.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & VIS & _ & _ & _ & _ & _ & VSTSH).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Q : (o / 8) * 8 = o /\ (o + sz - 1) / 8 = o / 8 + sz / 8 - 1 /\ 0 < sz / 8) by (clear - O8 Hsz Hsz8; lia).
  assert (QC : ahl_ceil ar / 8 <= o / 8 /\ (o + sz - 1) / 8 <= (ar_sptop ar - 1) / 8) by (clear - O1 O2 HC Hsz; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct Q as (Q1 & Q2 & Q3). destruct QC as (QC1 & QC2).
  split. { clear - O1 O2 O8 Q1 SPT HC. lia. }
  split. { left. clear - O1 SPT HC. lia. }
  split. exact I.
  split. { apply VIS. clear - O1 HC; lia. clear - O2 SPT; lia. }
  split. { apply VSTSH. intros i Hi. unfold in_shadow_of, S. replace (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) with (ar_sptop ar - 1) by (clear; lia). clear - Hi Q2 QC1 QC2. lia. }
  split. { intros i Hi. apply stack_client. clear - Hi O1 O2 SPT HC; lia. clear - Hi O1 HS; lia. }
  intros i Hi. apply (stk_shadow_client L ar). 2:{ clear - SPT; lia. } unfold in_shadow_of, S. replace (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) with (ar_sptop ar - 1) by (clear; lia). clear - Hi Q2 QC1 QC2. lia.
Qed.
Lemma sobj_vis LB FF LK cr A M model o s0 :
  ri_inv HI LB FF LK cr A M (vml_of model) -> sobj s0 o 32 -> L5.defined M o 32 -> shadow_zero M o 4 ->
  0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 -> ahl_ceil ar <= s0 ->
  let MV := mrestrict (ahid A model) M in
  (forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v)
  /\ (forall v, L5.u8_at RSEGS M o v -> L5.u8_at RSEGS MV o v)
  /\ L5KA.zeros_at MV (o / 8 + SB) 4 /\ L5.writable RSEGS MV o 32.
Proof.
  intros HH AOB ODEF SZ SPT HC MV.
  pose proof (sobj_facts LB FF LK cr A M model o 32 s0 s0 0 HH AOB ltac:(clear; lia) ltac:(reflexivity) SPT HC ltac:(clear; lia)) as (OR & OBIG & _ & OVIS & OVSH & _). change (32 / 8) with 4 in OVSH.
  split. { intros a v Ha Hc. apply (proj2 (u64_at_vis _ M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Ha; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Ha OR; lia))). exact Hc. }
  split. { intros v Hc. apply (proj2 (u8_at_vis _ M o v ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact Hc. }
  split. { apply (proj2 (zeros_at_vis _ M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis _ M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition copy_post_at (c : Z) (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o o' sp fbo : Z) (b' : L5.bigobj) (ws' : list Z) (g : growth)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => L5.bo_dyn b' = false /\ LB' = LB /\ cr' = cr
            /\ L5.big_at RSEGS M' o (L5.BO (copy_fb fbo (L5.bo_fb b') false) (L5.bo_len b') (L5.bo_st b'))
            /\ ahpres L ar LB FF sp (COPY_SCR + c) [(o, 32)] M M'
  | Grown q cap => L5.bo_dyn b' = true /\ cap = L5.bo_cap b' /\ LB' = (q, 8 * cap) :: LB /\ cr' = adebit L cr (8 * cap)
            /\ afresh L ar LB (FF ++ LKq) M' q (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap q))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap q)) ws'
            /\ ahpres L ar LB FF sp (COPY_SCR + c) [(o, 32)] M M'
  end.

Definition copy_stk16_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o o' spq r fbo : Z) (b' : L5.bigobj) (ws' : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' ->
    (L5.bo_dyn b' = true -> 8 * L5.bo_cap b' <= 2 ^ 27 /\ acredit_ok L cr (8 * L5.bo_cap b')) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 (spq + 16) -> spq mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M (spq + 16) (COPY_SCR + 16) ->
    ffr FF LK 2 -> ffrs FF (spq + 16) ->
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> sobj (spq + 16) o 32 -> L5.defined M o 32 -> shadow_zero M o 4 ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> aobj FF o' 32 -> shadow_zero M o' 4 ->
    (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        copy_post_at 16 L ar LB FF LK' cr M M' R R' o o' (spq + 16) fbo b' ws' g LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R COPY M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acopy_run : opnew_spec L ar HI ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o o' spq r fbo : Z) (b' : L5.bigobj) (ws' : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' ->
    (L5.bo_dyn b' = true -> 8 * L5.bo_cap b' <= 2 ^ 27 /\ acredit_ok L cr (8 * L5.bo_cap b')) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 (spq + 16) -> spq mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M (spq + 16) (COPY_SCR + 16) ->
    ffr FF LK 2 -> ffrs FF (spq + 16) ->
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> sobj (spq + 16) o 32 -> L5.defined M o 32 -> shadow_zero M o 4 ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> aobj FF o' 32 -> shadow_zero M o' 4 ->
    (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (o + 32 <= o' \/ o' + 32 <= o) ->
    L5.bo_dyn b' = true ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (q : Z) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        let cap := L5.bo_cap b' in
        regs_preserved R R' -> LB' = (q, 8 * cap) :: LB -> cr' = adebit L cr (8 * cap) ->
        afresh L ar LB (FF ++ LK') M' q (8 * cap) ->
        L5.big_at RSEGS M' o (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap q)) ->
        L5C.obj_limbs RSEGS M' (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap q)) ws' ->
        ahpres L ar LB FF (spq + 16) (COPY_SCR + 16) [(o, 32)] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ACOPY M model) K.
Proof.
  intros NEW fx R M model K LB FF LK cr A o o' spq r fbo b' ws' HH AM HK G10 G11 CAP G1 RA G2 A32 G4 STK ROOM RS OFB FBO AOB ODEF SZ OB' OL' AOB' SZ' INB APART DYN KONT.
  rewrite SCR_EQ in STK. change (4256 + 16) with 4272 in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SA : (spq - 128) mod 32 = 0 /\ (spq - 128) mod 16 = 0).
  { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SA as (SA32 & SA16).
  assert (SPR : 0 <= (spq + 16) < 2 ^ 64 /\ 140735332487424 <= (spq + 16) <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (sobj_facts LB FF LK cr A M model o 32 (spq + 16) (spq + 16) 4272 HH AOB ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - SLO; lia) ltac:(clear; lia))
    as (OR & OBIG & _ & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o' 32 (spq + 16) 4272 HH AOB' ltac:(clear; lia) ltac:(reflexivity))
    as (YR & YBIG & YDEF & YVIS & YVSH & YCL & YCLSH). change (32 / 8) with 4 in YVSH, YCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  (* [comment removed for export] *)
  destruct b' as [fby leny sto']. pose proof OB' as (Y0 & Hfby & Y8 & OST'). unfold L5.bo_dyn, L5.bo_cap in DYN, CAP, KONT.
  cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  destruct sto' as [w0 w1|cap qy]. { exfalso. destruct OST' as (BT0 & _). clear - DYN BT0. rewrite BT0 in DYN. discriminate. }
  destruct OST' as (BT1 & Y16 & Y24 & Hlc & Hcap & QY8 & QY4096 & QY47 & QYH). specialize (INB cap qy eq_refl). specialize (CAP BT1). destruct CAP as [CAP8 CR].
  destruct OL' as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  pose proof (proj1 (WB _ INB)) as (QB0 & QB1 & QB2 & QB3 & QB4 & QB5). cbn [fst snd] in QB0, QB1, QB2, QB3, QB4, QB5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QB5.
  pose proof (fb_dyn fbo fby FBO Hfby) as (FBE & FBR & FBT).
  assert (QYO : qy + 8 * cap <= o \/ o + 32 <= qy).
  { left. clear - QB4 OR SLO. lia. }
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W128 : L5.writable RSEGS MV (spq - 128) 144).
  { apply (proj2 (writable_vis H M (spq - 128) 144 (VIS (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M (spq + 16)). exact STK. clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (ac16A_conc fx R MV (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => o' | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(sc).
  destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR19 & aR20 & aR25 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128)).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R ACOPY R1 SM1 M1v (fun a => spq - 128 <= a < (spq + 16)) K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = spq - 128). { rewrite r2, aR2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, (aKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. replace (spq - 128) with (spq + 16 - 144) by (clear; lia). apply (astack_ok_of_astk L ar C LY M M1 (spq + 16) 4272 144 512 STK MGM1). clear; lia. clear; lia. clear; lia. first [exact SA16 | (replace (spq + 16 - 144) with (spq - 128) by (clear; lia); exact SA16)].
  - clear - ROOM. unfold ffr in ROOM. unfold ff_room. lia.
  - intros f Hf. rewrite U2. specialize (RS f Hf). clear - RS. lia.
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, aR1.

    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 1 (spq - 128 + 32) fl HH2 ltac:(left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 (spq + 16) 4272).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ (spq + 16) _ (spq - 128) 512 HH STK MGM1 PRES2). clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (FF' := (F, 1, spq - 128 + 32) :: FF) in *.
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (AOB2' : aobj FF' o' 32). { apply aobj_cons. exact AOB'. }
    (* [comment removed for export] *)
    set (RNG := fun a => spq - 128 <= a < (spq + 16) \/ o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ o' <= a < o' + 32 \/ o' / 8 + SB <= a < o' / 8 + SB + 4).
    assert (RCL : forall a, RNG a -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF 0 0 a /\ (a + 1 <= ahl_ceil ar \/ spq - 128 <= a < (spq + 16) \/ (spq + 16) <= a)).
    { intros a [Ra|[Ra|[Ra|[Ra|Ra]]]].
      - split. clear - Ra SPR; lia. split. apply stack_client. clear - Ra SLO SHI SPT; lia. clear; lia. right; left; exact Ra.
      - split. clear - Ra OR; lia. split. replace a with (o + (a - o)) by (clear; lia). apply (aclient_narrow L ar LB FF (spq + 16) 4272). apply OCL. clear - Ra; lia. clear; lia. right; right; clear - Ra OR; lia.
      - split. clear - Ra OR; unfold SB in *; lia. split. replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (aclient_narrow L ar LB FF (spq + 16) 4272). apply OCLSH. clear - Ra; lia. clear; lia.
        left; clear - Ra OR SPT; unfold SB in *; lia.
      - split. clear - Ra YR; lia. split. replace a with (o' + (a - o')) by (clear; lia). apply (aclient_narrow L ar LB FF (spq + 16) 4272). apply YCL. clear - Ra; lia. clear; lia. left; clear - Ra YR; lia.
      - split. clear - Ra YR; unfold SB in *; lia. split. replace a with (o' / 8 + SB + (a - (o' / 8 + SB))) by (clear; lia). apply (aclient_narrow L ar LB FF (spq + 16) 4272). apply YCLSH. clear - Ra; lia. clear; lia.
        left; clear - Ra YR SPT; unfold SB in *; lia. }
    assert (RVIS : forall Ax mx a, ri_inv HI LB FF' LK2 cr Ax M2 (vml_of mx) \/ (exists LBx LKx crx Mx, ri_inv HI LBx FF' LKx crx Ax Mx (vml_of mx)) -> RNG a -> ahid Ax mx (Z_to_bv 64 a) = false).
    { intros Ax mx a HX Ra.
      assert (HY : exists LBx LKx crx Mx, ri_inv HI LBx FF' LKx crx Ax Mx (vml_of mx)). { destruct HX as [HX|HX]. exists LB, LK2, cr, M2; exact HX. exact HX. } clear HX.
      destruct HY as (LBx & LKx & crx & Mx & HX).
      pose proof (vis_pack L ar C HI LY HIok LBx FF' LKx crx Ax Mx mx HX) as (_ & VISx & _).
      pose proof (sobj_facts LBx FF' LKx crx Ax Mx mx o 32 (spq + 16) (spq + 16) 0 HX AOB ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - SLO; lia) ltac:(clear; lia)) as (_ & _ & _ & OVISx & OVSHx & _).
      pose proof (aobj_facts L ar C HI LY HIok LBx FF' LKx crx Ax Mx mx o' 32 0 0 HX AOB2' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & YVISx & YVSHx & _).
      change (32 / 8) with 4 in OVSHx, YVSHx.
      destruct Ra as [Ra|[Ra|[Ra|[Ra|Ra]]]].
      - replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VISx (spq - 128) 144). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (o + (a - o)) by (clear; lia). apply (OVISx (a - o)). clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSHx (a - (o / 8 + SB))). clear - Ra; lia.
      - replace a with (o' + (a - o')) by (clear; lia). apply (YVISx (a - o')). clear - Ra; lia.
      - replace a with (o' / 8 + SB + (a - (o' / 8 + SB))) by (clear; lia). apply (YVSHx (a - (o' / 8 + SB))). clear - Ra; lia. }
    assert (RVIS0 : forall a, RNG a -> H (Z_to_bv 64 a) = false).
    { intros a Ra. destruct Ra as [Ra|[Ra|[Ra|[Ra|Ra]]]].
      - replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VIS (spq - 128) 144). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (o + (a - o)) by (clear; lia). apply (OVIS (a - o)). clear - Ra; lia.
      - replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH (a - (o / 8 + SB))). clear - Ra; lia.
      - replace a with (o' + (a - o')) by (clear; lia). apply (YVIS (a - o')). clear - Ra; lia.
      - replace a with (o' / 8 + SB + (a - (o' / 8 + SB))) by (clear; lia). apply (YVSH (a - (o' / 8 + SB))). clear - Ra; lia. }
    assert (AG2 : forall a, RNG a -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ra. destruct (RCL a Ra) as (Ha & Ca & Sa). unfold MV2. rewrite (mrestrict_visible H2 M2) by (apply (RVIS A model2 a (or_introl HH2) Ra)).
      rewrite (proj1 PRES2 a). 2: exact Ha. 2:{ apply (aclient_narrow L ar LB FF 0 0). exact Ca. clear - Sa SLO; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. apply RVIS0. exact Ra. }
    assert (AG2e : forall a, RNG a -> ~ (spq - 128 <= a < (spq + 16)) -> MV2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ra Na. rewrite (AG2 a Ra). rewrite (aFZ a (proj1 (RCL a Ra)) ltac:(clear - Na; lia)). unfold MV. apply mrestrict_visible. apply RVIS0. exact Ra. }
    assert (W128b : L5.writable RSEGS MV2 (spq - 128) 144).
    { eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply AG2. left; clear - Hj; lia. clear - SPR; lia. clear - SPR; lia. eapply L5.writable_grows. exact MG1. exact W128. }
    (* [comment removed for export] *)
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl (spq + 16) 4272 o 32 HH2 SPT ltac:(left; reflexivity) ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC OCL ltac:(clear; lia)) as (OF & OFSH & OFL).
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl (spq + 16) 4272 o' 32 HH2 SPT ltac:(left; reflexivity) ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC YCL ltac:(clear; lia)) as (YF & YFSH & YFL).
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl (spq + 16) 0 (spq - 128) 144 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC ltac:(intros i Hi; apply stack_client; clear - Hi SLO SHI SPT; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 1) with 128 in OF, YF, SF. change (ff_bytes 1 / 8) with 16 in OFSH, YFSH, SFSH.
    (* [comment removed for export] *)
    assert (XO2 : forall a v, (o <= a <= o + 24 \/ o' <= a <= o' + 24) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AG2e. clear - Ha Hj; subst RNG; cbn beta; lia. clear - Ha Hj OR YR SLO; lia. clear - Ha OR YR; lia. clear - Ha OR YR; lia. }
    assert (XB2 : forall a v, (a = o \/ a = o') -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS MV2 a v).
    { intros a v Ha Hc. eapply L5C.u8_at_agree. 4: exact Hc. intros j Hj. apply AG2e. clear - Ha Hj; subst RNG; cbn beta; lia. clear - Ha Hj OR YR SLO; lia. clear - Ha OR YR; lia. clear - Ha OR YR; lia. }
    assert (OZ2 : L5KA.zeros_at MV2 (o / 8 + SB) 4). { intros i Hi. rewrite AG2e. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. subst RNG; cbn beta; clear - Hi; lia. clear - Hi OR SLO SPT; unfold SB in *; lia. }
    assert (YZ2 : L5KA.zeros_at MV2 (o' / 8 + SB) 4). { intros i Hi. rewrite AG2e. unfold shadow_zero, byte_at, S in SZ'. apply SZ'. exact Hi. subst RNG; cbn beta; clear - Hi; lia. clear - Hi YR SLO SPT; unfold SB in *; lia. }
    assert (OW2 : L5.writable RSEGS MV2 o 32).
    { pose proof (sobj_facts LB FF' LK2 cr A M2 model2 o 32 (spq + 16) (spq + 16) 0 HH2 AOB ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - SLO; lia) ltac:(clear; lia)) as (_ & _ & _ & OVIS2 & _).
      assert (ODEF2 : L5.defined M2 o 32).
      { intros i Hi. rewrite (proj1 PRES2 (o + i)). apply MGM1. apply ODEF. exact Hi. clear - Hi OR; lia. apply (aclient_narrow L ar LB FF (spq + 16) 4272). apply OCL. exact Hi. clear - Hi OR; lia. }
      apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 32 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
    (* [comment removed for export] *)
    assert (OFSS : o / 8 + 2147450880 + 4 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 16 <= o / 8 + 2147450880) by (clear - OF OR F8; lia).
    assert (YFSS : o' / 8 + 2147450880 + 4 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 16 <= o' / 8 + 2147450880) by (clear - YF YR F8; lia).
    assert (FRO : spq - 128 + 144 <= o \/ o + 32 <= spq - 128) by (clear - OR SLO; lia).
    assert (FRY : spq - 128 + 144 <= o' \/ o' + 32 <= spq - 128) by (clear - YR SLO; lia).
    assert (HV2 : 140735332487296 <= (spq + 16) <= 140737488355328) by (clear - SPR SLO SPT; lia).
    assert (HVF : 4096 <= F <= 140737488355200) by (clear - FR; lia). assert (HVFL : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
    assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVY : 4096 <= o' <= 140737488355296) by (clear - YR; lia).
    assert (ALO : aligned o 8) by (exact (proj1 (proj2 (proj2 (proj2 OR))))). assert (ALY : aligned o' 8) by (exact (proj1 (proj2 (proj2 (proj2 YR))))).
    assert (ALF : aligned F 32) by exact F32. assert (ALS : aligned spq 32) by exact A32.
    assert (HVL : 0 <= Z.of_nat leny <= 16777216) by (clear - Hlc CAP8; lia). assert (HVC : 0 <= cap <= 16777216) by (clear - Hcap CAP8; lia).
    assert (HVQY : 4096 <= qy <= 140737488355328) by (clear - QY4096 QY47 Hcap; lia).
    (* [comment removed for export] *)
    pose proof (ac16B_conc fx1 R2 MV2 (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => o' | 35%nat => fbo | 36%nat => fby | 37%nat => Z.of_nat leny | 38%nat => cap
                  | 39%nat => qy | 40%nat => F | 41%nat => fl | 43%nat => U R2 1 | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XO2; [clear; lia | sc]) | (apply XB2; [clear; lia | sc]) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR13 & bR14 & bR18 & bR20 & bR21 & bR22 & bR23 & bR24 & bR26 & bO24 & bO16 & bO8 & bO0 & bC104 & bB_V40nat & bB_V40nat_1 & bB_V40nat_2 & bB_V40nat_3 & bB_V40nat_4 & bB_V40nat_5 & bB_V40nat_6 & bB_V40nat_7 & bB_V40nat_8 & bB_V40nat_9 & bB_V40nat_10 & bB_V40nat_11 & bQ_V40nat & bQ_V40nat_1 & bQ_V40nat_2 & bDF)).
    rewrite FBE in bO0.
    set (W2 := fun a => spq - 112 <= a < spq - 104 \/ o <= a < o + 32 \/ F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 12).
    apply (apiece L ar C HI LY HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 0x922d8 R3 L5BALC.ALLOC M3v W2 K HH2 (conj Hh2 MI2) bMS MG3).
    { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W2; cbn beta in Hna; unfold SB in *; lia. }
    { intros a Ha Wa. subst W2; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa|Wa]]].
      - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
      - split. apply stack_client. clear - Wa OR SLO; lia. clear; lia. clear - Wa OR; lia.
      - split. apply (fframe_client L ar LB _ 0 0 F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB _ 0 0 F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. lia.
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 (spq + 16) 4272). { eapply astk_grows. exact ASTK2. exact MGM3. }
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as WF2.
    assert (ND2 : NoDup (map ff_addr (FF' ++ LK2))). { clear - WF2. decompose [and] WF2. assumption. }
    (* [comment removed for export] *)
    apply (L5BALC.alloc_ok L ar C HI LY HIok NEW fx3 R3 M3 model3 K LB FF' LK2 cr A cap (spq - 128) 0x92434 HH3 AM3 HK).
    + rewrite r11. exact bR11.
    + clear - Hcap CAP8; lia.
    + clear - Hcap CAP8; lia.
    + exact CR.
    + rewrite r1. exact bR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. rk.
    + rewrite r4. rk.
    + replace (spq - 128) with (spq + 16 - 144) by (clear; lia). apply (astk_sub ar M3 M3 (spq + 16) 4272 144 OPNEW_SCR ASTK3 (mem_grows_refl M3)). clear; lia. unfold OPNEW_SCR, MALLOC_SCR; clear; lia.
      unfold OPNEW_SCR, MALLOC_SCR; clear; lia. first [exact SA16 | (replace (spq + 16 - 144) with (spq - 128) by (clear; lia); exact SA16)].
    + (* [comment removed for export] *)
      intros fx4 R4 M4 model4 A4 q nR10 RP4 (BRq & BAq & FAq & DEFq & SHBq) PRES4 RT4 IA4 AM4 HH4.

      set (LB4 := (q, 8 * cap) :: LB) in *. set (cr4 := adebit L cr (8 * cap)) in *.
      assert (ASTK4 : astk ar M4 (spq + 16) 4272).
      { apply (astk_after L ar C HI HIok LB FF' LK2 cr A M3 M3 M4 _ (spq + 16) _ (spq - 128) OPNEW_SCR [] HH3 ASTK3 (mem_grows_refl M3) PRES4).
        unfold OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. unfold OPNEW_SCR, MALLOC_SCR; clear; lia. }
      pose proof (vis_pack L ar C HI LY HIok LB4 FF' LK2 cr4 A4 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
      pose proof (statics_vis LB4 FF' LK2 cr4 A4 M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4).
      set (H4 := ahid A4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
      pose proof (vis_pack L ar C HI LY HIok LB FF' LK2 cr A M2 model2 HH2) as (_ & _ & _ & _ & _ & _ & VFSSH2 & _).
      pose proof (BRq) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Q1.
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as (WB4 & WF4 & _).
      pose proof (WB4 (q, 8 * cap) (or_introl eq_refl)) as ((_ & _ & _ & _ & _ & _) & _ & QSH4 & QND & QFS). cbn [fst snd] in QSH4, QFS.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (FQ15 : (F + 128 - 1) / 8 = F / 8 + 15 /\ F mod 8 = 0) by (clear - F8; lia).
      assert (QSH : SB <= q / 8 + SB /\ (q + 8 * cap - 1) / 8 + SB < 0x10007fff8000 /\ (q / 8) * 8 = q /\ (8 * cap) / 8 = cap) by (clear - Q0 Q5 Q2 Hcap; unfold SB in *; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      (* [comment removed for export] *)
      set (RNG4 := fun a => RNG a \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16).   (* [comment removed for export] *)
      assert (RCL4 : forall a, RNG4 a -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF' 0 0 a /\ (a + 1 <= ahl_ceil ar \/ spq - 128 <= a < (spq + 16) \/ (spq + 16) <= a)).
      { intros a [Ra|[Ra|Ra]].
        - destruct (RCL a Ra) as (X1 & X2 & X3). split. exact X1. split. apply aclient_cons. exact X2. exact X3.
        - split. clear - Ra FR; lia. split. apply (fframe_client L ar LB FF' 0 0 F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ra; lia. left; clear - Ra FR FCEIL; lia.
        - split. clear - Ra FR; unfold SB in *; lia. split. apply (fframe_shadow_client L ar LB FF' 0 0 F 1 (spq - 128 + 32)). left; reflexivity.
          change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Ra F8; unfold SB in *; lia. left. clear - Ra FR SPT; unfold SB in *; lia. }
      assert (RV4 : forall a, RNG4 a -> H4 (Z_to_bv 64 a) = false).
      { intros a [Ra|[Ra|Ra]].
        - apply (RVIS A4 model4 a). right. exists LB4, LK2, cr4, M4. exact HH4. exact Ra.
        - replace a with (F + (a - F)) by (clear; lia). apply (VFS4 F 128 FS1 FS2). clear - Ra; lia.
        - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VFSSH4 (F / 8 + SB) 16). 2: clear - Ra; lia.
          intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (RV2 : forall a, RNG4 a -> H2 (Z_to_bv 64 a) = false).
      { intros a [Ra|[Ra|Ra]].
        - apply (RVIS A model2 a). left. exact HH2. exact Ra.
        - replace a with (F + (a - F)) by (clear; lia). apply (VFS2 F 128 FS1 FS2). clear - Ra; lia.
        - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VSH (a - (F / 8 + SB))). clear - Ra; lia. }
      assert (AG4 : forall a, RNG4 a -> MV4 (Z_to_bv 64 a) = M3v (Z_to_bv 64 a)).
      { intros a Ra. destruct (RCL4 a Ra) as (Ha & Ca & Sa). unfold MV4. rewrite (mrestrict_visible H4 M4) by (apply RV4; exact Ra).
        rewrite (proj1 PRES4 a). 2:{ split. exact Ha. split. apply (aclient_narrow L ar LB FF' 0 0). exact Ca. unfold OPNEW_SCR, MALLOC_SCR; clear - Sa SLO; lia. intros rr [ ]. }
        apply EQ3. apply RV2. exact Ra. }
      assert (XC4 : forall a v, (spq - 128 <= a <= spq + 8 \/ (F <= a <= F + 16 \/ F + 32 <= a <= F + 112) \/ o <= a <= o + 24) -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV4 a v).
      { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AG4. subst RNG4 RNG; cbn beta. clear - Ha Hj; lia. clear - Ha SPR FR OR; lia. clear - Ha SPR FR OR; lia. }
      (* [comment removed for export] *)
      assert (AGY : forall a, (o' <= a < o' + 32 \/ o' / 8 + SB <= a < o' / 8 + SB + 4) -> MV4 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ra. rewrite AG4. 2:{ left. subst RNG; cbn beta. clear - Ra; lia. }
        rewrite bFZ. apply AG2e. subst RNG; cbn beta; clear - Ra; lia. clear - Ra YR SLO SPT; unfold SB in *; lia. clear - Ra YR; unfold SB in *; lia.
        all: subst W2; cbn beta. all: clear - Ra YR OR APART YF YFSH SLO SPT FR F8 YBIG OBIG FBIG; unfold SB in *.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        all: lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (XY4 : forall a v, o' <= a <= o' + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV4 a v).
      { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AGY. clear - Ha Hj; lia. clear - Ha YR; lia. clear - Ha YR; lia. }
      assert (YB4 : L5.u8_at RSEGS MV4 o' fby). { eapply L5C.u8_at_agree. 4: exact Y0. intros j Hj. apply AGY. clear - Hj; lia. clear - YR; lia. clear - YR; lia. }
      assert (YZ4 : L5KA.zeros_at MV4 (o' / 8 + SB) 4). { intros i Hi. rewrite AGY. unfold shadow_zero, byte_at, S in SZ'. apply SZ'. exact Hi. clear - Hi; lia. }
      assert (OZ4 : L5KA.zeros_at MV4 (o / 8 + SB) 4).
      { eapply L5KA.zeros_at_agree1. 2: exact OZ2. intros j Hj. rewrite AG4. 2:{ subst RNG4 RNG; cbn beta. clear - Hj; lia. } apply bFZ. clear - Hj OR; unfold SB in *; lia.
        all: subst W2; cbn beta. all: clear - Hj OR OBIG SLO SPT FR F8 OF OFSH FBIG; unfold SB in *.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        all: lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (W128d : L5.writable RSEGS MV4 (spq - 128) 144).
      { apply (proj2 (writable_vis H4 M4 (spq - 128) 144 (VIS4 (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M4 (spq + 16)). exact ASTK4. clear; lia. clear; lia. clear; lia. }
      pose proof (sobj_facts LB4 FF' LK2 cr4 A4 M4 model4 o 32 (spq + 16) (spq + 16) 0 HH4 AOB ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - SLO; lia) ltac:(clear; lia)) as (_ & _ & _ & OVIS4 & OVSH4 & _). change (32 / 8) with 4 in OVSH4.
      assert (ODEF4 : L5.defined M4 o 32).
      { intros i Hi. apply (proj2 (proj2 PRES4)). clear - Hi OR; lia. apply stack_client. clear - Hi OR SLO; lia. clear - Hi OR; lia.
        apply MGM3. rewrite (proj1 PRES2 (o + i)). apply MGM1. apply ODEF. exact Hi. clear - Hi OR; lia. apply (aclient_narrow L ar LB FF (spq + 16) 4272). apply OCL. exact Hi. clear - Hi OR; lia. }
      assert (OW4 : L5.writable RSEGS MV4 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H4 M4 o 32 OVIS4)). exact ODEF4. clear - OR; lia. clear - OR; lia. }
      (* [comment removed for export] *)
      assert (QV : avis H4 q (8 * cap)). { apply (VBLK4 q (8 * cap)). left; reflexivity. clear; lia. clear; lia. }
      assert (QW4 : L5.writable RSEGS MV4 q 8).
      { apply (proj2 (writable_vis H4 M4 q 8 ltac:(eapply avis_sub; [exact QV | clear; lia | clear - Hcap; lia]) ltac:(clear - Q0; lia) ltac:(clear - Q4 Hcap SPT; lia))).
        apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact DEFq. clear; lia. clear - Hcap; lia. clear - Q0; lia. clear - Q4 Hcap SPT; lia. }
      assert (QZ4 : L5KA.zeros_at MV4 (q / 8 + SB) 1).
      { apply (proj2 (zeros_at_vis H4 M4 (q / 8 + SB) 1 ltac:(apply (VBSH4 q (8 * cap)); [left; reflexivity | intros i Hi; unfold in_shadow_of, S; clear - Hi QSH Hcap; lia]))).
        intros i Hi. destruct SHBq as [SZq _]. unfold shadow_zero, byte_at, S in SZq. apply SZq. clear - Hi QSH Hcap; lia. }
      assert (QO : q + 8 * cap <= o \/ o + 32 <= q).
      { left. clear - Q4 OR SLO. lia. }
      assert (QY : q + 8 * cap <= o' \/ o' + 32 <= q).
      { destruct AOB' as (g & Hg & X1 & X2 & _). specialize (FAq g ltac:(apply in_or_app; left; right; exact Hg)). clear - FAq X1 X2. lia. }
      assert (QF : q + 8 * cap <= F \/ F + 128 <= q). { apply (FAq (F, 1, spq - 128 + 32)). apply in_or_app; left; left; reflexivity. }
      assert (QFL : q + 8 * cap <= fl \/ fl + 1 <= q). { clear - QFS FLP. unfold FS_BYTES in *. lia. }
      assert (QQY : q + 8 * cap <= qy \/ qy + 8 * cap <= q). { apply (BAq (qy, 8 * cap)). exact INB. }
      assert (HVQ : 4096 <= q <= 140737488355320) by (clear - Q0 Q4 SPT Hcap; lia). assert (ALQ : aligned q 16) by exact Q2.
      assert (FRQ : spq - 128 + 144 <= q \/ q + 8 <= spq - 128) by (clear - Q4 SLO Hcap; lia).
      assert (OQ8 : o + 32 <= q \/ q + 8 <= o) by (clear - QO Hcap; lia). assert (YQ8 : o' + 32 <= q \/ q + 8 <= o') by (clear - QY Hcap; lia).
      assert (FQ8 : F + 128 <= q \/ q + 8 <= F) by (clear - QF Hcap; lia). assert (FLQ8 : fl + 1 <= q \/ q + 8 <= fl) by (clear - QFL Hcap; lia).
      (* [comment removed for export] *)
      pose proof (ac16C_conc fx4 R4 MV4 (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => o' | 35%nat => copy_fb fbo fby true | 36%nat => fby | 37%nat => Z.of_nat leny
                    | 38%nat => cap | 39%nat => qy | 40%nat => F | 41%nat => fl | 42%nat => q | 43%nat => U R4 1 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XC4; [clear; lia | sc]) | (apply XY4; [clear; lia | sc])
                          | (eapply L5C.u8_at_agree; [ | | | exact bO0]; [intros j Hj; apply AG4; left; subst RNG; cbn beta; clear - Hj; lia | clear - OR; lia | clear - OR; lia]) ]).
      destruct P as (fx5 & R5 & M5v & MG5 & cFR & cFZ & (cMS & cKS & cR1 & cR11 & cR12 & cR19 & cQ0 & cO24)).
      set (W4 := fun a => o + 24 <= a < o + 32 \/ q <= a < q + 8).
      apply (apiece L ar C HI LY HIok LB4 FF' LK2 cr4 A4 M4 model4 fx4 fx5 R4 0x92434 R5 0x5e354 M5v W4 K HH4 AM4 cMS MG5).
      { intros a Ha Hna. apply cFZ. exact Ha. all: clear - Hna; subst W4; cbn beta in Hna; lia. }
      { intros a Ha Wa. subst W4; cbn beta in Wa. destruct Wa as [Wa|Wa].
        - split. apply stack_client. clear - Wa OR SLO; lia. clear; lia. clear - Wa OR; lia.
        - split. apply (block_client L ar LB4 FF' 0 0 q (8 * cap)). left; reflexivity. clear - Wa Hcap; lia. clear - Wa Q1 Hcap; lia. }
      intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
      assert (ASTK5 : astk ar M5 (spq + 16) 4272). { eapply astk_grows. exact ASTK4. exact MGM5. }
      (* [comment removed for export] *)
      set (n8 := 8 * Z.of_nat leny) in *.
      pose proof (aio_memcpy _ _ _ _ _ HIok) as MC. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MC.
      rewrite (aly_segs L C LY), (aly_memcpy L C LY), (aly_scr_mem L C LY) in MC.
      assert (U52 : bv_unsigned (getr R5 2%bv) = spq - 128). { rewrite r2, (cKS 2%nat) by inl. rewrite (cs_of_preserved R3 R4 2 RP4) by inl. rewrite (bKS 2%nat) by inl.
        rewrite (cs_of_preserved R1 R2 2 RP2) by inl. rewrite aR2. apply L5.unsigned_lit. clear - SPR; lia. }
      (* [comment removed for export] *)
      assert (AGQY : forall a, (qy <= a < qy + 8 * cap \/ S qy <= a <= S (qy + 8 * cap - 1)) -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Hq. pose proof (FBLK _ INB) as X. cbn [fst snd] in X.
        assert (Ca : aclient L ar LB FF 0 0 a). { destruct Hq as [Ha|Ha]. apply (block_client L ar LB FF 0 0 qy (8 * cap)). exact INB. exact Ha.
          right; right; right; right; right; right. exists (qy, 8 * cap). split. exact INB. exact Ha. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (AR : 0 <= a < 2 ^ 64 /\ a + 1 <= ahl_ceil ar /\ ~ (o <= a < o + 32) /\ ~ (F <= a < F + 24) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 12) /\ ~ (q <= a < q + 8)).
        { unfold S in Hq. clear - Hq QYO QQY QB5 QB2 QB4 QB0 Hcap SLO SPT X F8 FR FBIG OBIG OR Q5 Q0 Q4. unfold SB in *. lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        destruct AR as (A0 & A1 & A2 & A3 & A4' & A5).
        rewrite FRM5. 2: exact A0. 2:{ subst W4; cbn beta. clear - A2 A5; lia. }
        rewrite (proj1 PRES4 a). 2:{ split. exact A0. split. apply aclient_cons. apply (aclient_narrow L ar LB FF 0 0). exact Ca. unfold OPNEW_SCR, MALLOC_SCR; clear - A1 SLO; lia. intros rr [ ]. }
        rewrite FRM3. 2: exact A0. 2:{ subst W2; cbn beta. clear - A1 A2 A3 A4' SLO; lia. }
        rewrite (proj1 PRES2 a). 2: exact A0. 2:{ apply (aclient_narrow L ar LB FF 0 0). exact Ca. clear - A1 SLO; lia. }
        apply FRM1. exact A0. clear - A1 SLO; lia. }
      eapply (MC fx5 R5 M5 model5 LB4 FF' LK2 cr4 A4 q qy n8 (limb_bytes ws') K); clear MC.
      { split. exact HH5. split. exact (proj1 AM5). split. exact (proj2 AM5).
        split. rewrite r10. rk. split. rewrite r12, cR12. subst n8; reflexivity. split. clear - Hlc CAP8; subst n8; lia.
        split. rewrite r4. rk. split. rewrite r1, cR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
        split. { rewrite U52. replace (spq - 128) with (spq + 16 - 144) by (clear; lia). apply (astack_ok_of_astk L ar C LY M4 M5 (spq + 16) 4272 144 2560 ASTK4 MGM5). clear; lia. clear; lia. clear; lia. first [exact SA16 | (replace (spq + 16 - 144) with (spq - 128) by (clear; lia); exact SA16)]. }
        split. { intros a Ha. left. unfold byte_at. rewrite FRM5. destruct SHBq as [SZq _]. unfold shadow_zero, byte_at in SZq. replace (S a) with (S q + (a / 8 - q / 8)) by (unfold S; clear; lia).
                 apply SZq. 2: unfold S. 3: unfold S; subst W4; cbn beta. all: clear - Ha Hlc QSH Q5 Hcap OBIG OR; subst n8; unfold SB in *.
                 Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
                 all: lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        split. { intros i Hi. rewrite U52. apply (block_client L ar LB4 FF' _ _ q (8 * cap)). left; reflexivity. clear - Hi Hlc; subst n8; lia. }
        split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M5 q n8). eapply L5.defined_grows. exact MGM5. eapply L5.defined_sub. exact DEFq. clear; lia. clear - Hlc; subst n8; lia.
                 clear - Q0; lia. clear - Q4 SPT Hlc Hcap; subst n8; lia. exact Hi. exact Hm. }
        split. exact HK. apply (app_rng_block L ar C HI HIok LB4 FF' LK2 cr4 A4 M5 _ q (8 * cap) q n8 HH5 ltac:(left; reflexivity)). clear; lia. clear - Hlc; subst n8; lia. }
      { rewrite r11. exact cR11. }
      { intros a Ha. left. unfold byte_at. rewrite AGQY. 2:{ right. unfold S. clear - Ha Hlc Hcap; subst n8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        pose proof (proj1 (proj2 (proj2 (WB _ INB)))) as [SZy _]. cbn [fst snd] in SZy. unfold shadow_zero, byte_at in SZy. replace (S a) with (S qy + (a / 8 - qy / 8)) by (unfold S; clear; lia). apply SZy.
        clear - Ha Hlc Hcap QY8; subst n8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      { clear - QY4096 QY47 Hlc; subst n8; lia. }
      { apply (app_rng_block L ar C HI HIok LB4 FF' LK2 cr4 A4 M5 _ qy (8 * cap) qy n8 HH5 ltac:(right; exact INB)). clear; lia. clear - Hlc; subst n8; lia. }
      { intros i Hi. right. apply (block_client L ar LB4 FF' _ _ qy (8 * cap)). right; exact INB. clear - Hi Hlc; subst n8; lia. }      (* [comment removed for export] *)
      { unfold n8. rewrite <- Lws. replace (Z.to_nat (8 * Z.of_nat (length ws'))) with (8 * length ws')%nat by (clear; lia).
        apply rdn_of_limbs_at. 2: clear - QY4096; lia. 2: rewrite Lws; clear - QY47 Hlc; lia.
        eapply L5C.limbs_at_agree. 4: exact LAT. 2: clear - QY4096; lia. 2: rewrite Lws; clear - QY47 Hlc; lia. intros j Hj. apply AGQY. left. rewrite Lws in Hj; clear - Hj Hlc; lia. }
      { intros _. clear - QQY Hlc; subst n8; lia. }
      (* [comment removed for export] *)
      intros R6 M6 model6 mR10 RP6 BYTES PRES6 SDEF6 RT6 MI6 HH6. rewrite U52 in PRES6, SDEF6. rewrite r1, cR1.
      assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 AM5). }

      assert (ASTK6 : astk ar M6 (spq + 16) 4272).
      { apply (astk_after_eq L ar C HI HIok LB4 FF' LK2 cr4 A4 M5 M5 M6 _ (spq + 16) _ (spq - 128) 2560 HH5 ASTK5 (mem_grows_refl M5)).
        intros a Ha Hs Hns. apply PRES6. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs Q4 Hlc Hcap; subst n8; lia.
        exact SDEF6. clear; lia. clear; lia. clear; lia. }
      pose proof (vis_pack L ar C HI LY HIok LB4 FF' LK2 cr4 A4 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
      pose proof (statics_vis LB4 FF' LK2 cr4 A4 M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
      set (H6 := ahid A4 model6) in *. set (MV6 := mrestrict H6 M6) in *.
      assert (RV6 : forall a, RNG4 a -> H6 (Z_to_bv 64 a) = false).
      { intros a [Ra|[Ra|Ra]].
        - apply (RVIS A4 model6 a). right. exists LB4, LK2, cr4, M6. exact HH6. exact Ra.
        - replace a with (F + (a - F)) by (clear; lia). apply (VFS6 F 128 FS1 FS2). clear - Ra; lia.
        - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VFSSH6 (F / 8 + SB) 16). 2: clear - Ra; lia.
          intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      (* [comment removed for export] *)
      assert (QRNG : forall a, RNG4 a -> ~ (q <= a < q + 8 * cap)).
      { intros a Ra. subst RNG4 RNG; cbn beta in Ra. clear - Ra Hcap QO QY QF Q4 Q5 SLO SPT OR YR FR F8. unfold SB in *.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (AG6 : forall a, RNG4 a -> ~ (o + 24 <= a < o + 32) -> MV6 (Z_to_bv 64 a) = M3v (Z_to_bv 64 a)).
      { intros a Ra No. destruct (RCL4 a Ra) as (Ha & Ca & Sa). unfold MV6. rewrite (mrestrict_visible H6 M6) by (apply RV6; exact Ra).
        rewrite (PRES6 a Ha). 2:{ apply aclient_consb. apply (aclient_narrow L ar LB FF' 0 0). exact Ca. clear - Sa SLO; lia. } 2:{ intros X; apply (QRNG a Ra). clear - X Hlc; subst n8; lia. }
        rewrite FRM5. 2: exact Ha. 2:{ subst W4; cbn beta. intros [X|X]. exact (No X). apply (QRNG a Ra). clear - X Hcap; lia. }
        rewrite <- (AG4 a Ra). unfold MV4. rewrite (mrestrict_visible H4 M4) by (apply RV4; exact Ra). reflexivity. }
      assert (XC6 : forall a v, (spq - 128 <= a <= spq + 8 \/ (F <= a <= F + 16 \/ F + 32 <= a <= F + 112)) -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV6 a v).
      { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR FR; lia. 2: clear - Ha SPR FR; lia.
        intros j Hj. apply AG6. subst RNG4 RNG; cbn beta. clear - Ha Hj; lia. clear - Ha Hj OR SLO FR OF; lia. }
      assert (XC26 : forall a v, spq - 128 <= a <= spq + 8 -> (a + 8 <= spq - 112 \/ spq - 104 <= a) -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV6 a v).
      { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Ha SPR; lia.
        intros j Hj. rewrite AG6. 2:{ subst RNG4 RNG; cbn beta. clear - Ha Hj; lia. } 2:{ clear - Ha Hj OR SLO; lia. }
        rewrite bFZ. apply AG2. subst RNG; cbn beta. clear - Ha Hj; lia. clear - Ha Hj SPR; lia.
        all: subst W2; cbn beta. all: clear - Ha Hb Hj OR SLO SPT FR SF F8 FBIG; unfold SB in *. all: lia. }
      assert (FLCv' : L5.u64_at RSEGS MV2 (F + 120) fl). { replace (F + 120) with (F + 128 - 8) by (clear; lia). exact FLCv. }
      assert (FLC3 : L5.u64_at RSEGS M3v (F + 120) fl).
      { eapply L5C.u64_at_agree. 4: exact FLCv'. 2: clear - FR; lia. 2: clear - FR; lia. intros j Hj. apply bFZ. clear - Hj FR; lia.
        all: subst W2; cbn beta. all: clear - Hj FR F8 SF OF FBIG; unfold SB in *. all: lia. }
      (* [comment removed for export] *)
      pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model6 F 1 _ _ fl HH2 HH6 (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) FLC) as [FLC6 FL6].
      change (ff_bytes 1) with 128 in FLC6, FL6. replace (F + 128 - 8) with (F + 120) in FLC6, FL6 by (clear; lia).
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB6 & WF6 & _).
      assert (FDEF6 : L5.defined MV6 F 128). { apply (proj2 (defined_vis H6 M6 F 128 (VFS6 F 128 FS1 FS2))). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF6 _ (or_introl eq_refl))))))). }
      assert (FW6 : L5.writable RSEGS MV6 F 128). { apply (L5C.writable_of_defined RSEGS). exact FDEF6. clear - FR; lia. clear - FR; lia. }
      pose proof (fl_writable L ar C HI LY HIok _ FF' LK2 _ A4 M6 _ fl HH6 FLP) as [FLD6 FLW6].
      pose proof (fl_vis L ar C HI LY HIok _ FF' LK2 _ A4 M6 model6 fl HH6 FLP) as FLV6.
      assert (FLW6v : L5.writable RSEGS MV6 fl 1). { apply (proj2 (writable_vis H6 M6 fl 1 FLV6 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW6. }
      assert (FSHW6 : L5.writable RSEGS MV6 (F / 8 + SB) 16).
      { apply (L5C.writable_of_defined RSEGS). 2: clear - FR F8; unfold SB; lia. 2: clear - FR F8; unfold SB; lia.
        eapply L5C.defined_agree. 2:{ eapply L5.defined_grows. exact MG3. eapply L5KA.zeros_at_defined. exact FSHZ. }
        intros j Hj. apply AG6. subst RNG4 RNG; cbn beta. clear - Hj; lia. clear - Hj OR OBIG FR F8; unfold SB in *; lia. }
      assert (W128f : L5.writable RSEGS MV6 (spq - 128) 144).
      { apply (proj2 (writable_vis H6 M6 (spq - 128) 144 (VIS6 (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M6 (spq + 16)). exact ASTK6. clear; lia. clear; lia. clear; lia. }
      (* [comment removed for export] *)
      pose proof (ac16D_conc fx5 R6 MV6 (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => o' | 40%nat => F | 41%nat => fl | 43%nat => U R6 1
                    | 44%nat => U R 1 | 45%nat => U R 8 | 46%nat => U R 9 | 47%nat => U R 18 | 48%nat => U R 19 | 49%nat => U R 20 | 50%nat => U R 21
                    | 51%nat => U R 22 | 52%nat => U R 23 | 53%nat => U R 24 | 54%nat => U R 25 | 55%nat => U R 26 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XC26; [clear; lia | clear; lia | unfold U; sc]) | (apply XC6; [clear; lia | sc]) | exact FL6 ]).
      destruct P as (fx7 & R7 & M7v & MG7 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26 & eFL0 & eB_V40nat & eB_V40nat_1 & eB_V40nat_2 & eB_V40nat_3 & eB_V40nat_4 & eB_V40nat_5 & eB_V40nat_6 & eB_V40nat_7 & eB_V40nat_8 & eB_V40nat_9 & eB_V40nat_10 & eB_V40nat_11 & eB_V40nat_12 & eB_V40nat_13 & eB_V40nat_14 & eB_V40nat_15 & eQ_V40nat & eDF)).
      assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
      pose proof (ret_to fx7 R7 M7v 0x92560 W_92560 r F_92560 eq_refl D_92560 ltac:(rewrite eR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
      pose proof (msteps_trans _ _ _ _ eMS RET) as MS8. clear eMS RET.
      set (W7 := fun a => (F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + 16) \/ a = fl).
      apply (apiece_retire L ar C HI LY HIok LB4 FF LK2 cr4 A4 M6 model6 fx5 fx7 R6 0x92498 R7 r M7v W7 F 1 (spq - 128 + 32) fl K HH6 (conj Hh6 MI6)).
      { change (ff_bytes 1) with 128. replace (F + 128 - 8) with (F + 120) by (clear; lia).
        exact FLC6. }
      { intros X. destruct (aclient_consb_inv L ar LB FF' _ 0 0 fl X) as [Y|[Y|Y]]. exact (FLNC Y).
        - cbn [fst snd] in Y. clear - Y QFL. lia.
        - cbn [fst snd] in Y. unfold in_shadow_of, S in Y. clear - Y FLBIG QSH. unfold SB in *. lia. }
      { exact FLV6. }
      { clear - FLR; lia. }
      { exact MS8. }
      { exact MG7. }
      { intros a Ha Hna. apply eFZ. exact Ha. all: clear - Hna; subst W7; cbn beta in Hna; unfold SB in *; lia. }
      { intros a Ha Wa. subst W7; cbn beta in Wa. destruct Wa as [[Wa|Wa]|Wa].
        - right. apply aclient_consb. apply (fframe_client L ar LB _ 0 0 F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia.
        - right. apply aclient_consb. apply (fframe_shadow_client L ar LB _ 0 0 F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128.
          unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. lia.
        - left; exact Wa. }
      { intros a. subst W7; cbn beta. repeat match goal with X : _ |- _ => clear X end.
        destruct (rng_dec a F (F + 8)); [left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 16)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto. }
      { exact eFL0. }
      intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 FRM7 EQ7.
      assert (ASTK7 : astk ar M7 (spq + 16) 4272). { eapply astk_grows. exact ASTK6. exact MGM7. }
      (* [comment removed for export] *)
      assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB FF (spq + 16) 4272 a).
      { intros a Ha. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) 4272 F 128 a HH SPT).
        clear - FR; lia. exact FCEIL. exact FAPP. exact (proj2 FQ15). clear; lia. reflexivity.
        eapply fframes_apart_incl. exact FAPART. intros g Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
      assert (NCQ : forall a, q <= a < q + 8 * cap -> ~ aclient L ar LB FF (spq + 16) 4272 a).
      { intros a Ha. apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) 4272 q (8 * cap) a HH SPT BRq BAq).
        eapply fframes_apart_incl. exact FAq. intros g Hg; apply in_or_app; left; right; exact Hg. exact Ha. }
      (* [comment removed for export] *)
      assert (E07 : ek L ar LB FF (spq + 16) 4272 [(o, 32)] M M7).
      { eapply ek_trans. { apply (ek_piece L ar LB FF (spq + 16) 4272 [(o, 32)] M M1 (fun a => spq - 128 <= a < (spq + 16)) FRM1).
          intros a Ha Hc _ X. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) 4272 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia. }
        eapply ek_trans. { apply (ek_rt L ar LB FF [] (spq + 16) 4272 (spq - 128) 512 [(o, 32)] M1 M2 PRES2). clear; lia. clear; lia. }
        eapply ek_trans. { apply (ek_piece L ar LB FF (spq + 16) 4272 [(o, 32)] M2 M3 W2 FRM3). intros a Ha Hc Ho X. subst W2; cbn beta in X. destruct X as [X|[X|[X|X]]].
          - destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) 4272 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia.
          - apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia.
          - apply (NCF a). left; clear - X; lia. exact Hc.
          - apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc. }
        eapply ek_trans. { apply (ek_callee L ar LB [] FF [(F, 1, spq - 128 + 32)] (spq + 16) 4272 (spq - 128) OPNEW_SCR [(o, 32)] [] M3 M4 PRES4).
          unfold OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. intros a _ _ rr [ ]. }
        eapply ek_trans. { apply (ek_piece L ar LB FF (spq + 16) 4272 [(o, 32)] M4 M5 W4 FRM5). intros a Ha Hc Ho X. subst W4; cbn beta in X. destruct X as [X|X].
          - apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia.
          - apply (NCQ a). clear - X Hcap; lia. exact Hc. }
        eapply ek_trans. { intros a (Ha & Hc & Ho). apply PRES6. exact Ha. apply aclient_consb. apply aclient_cons. eapply aclient_mono. exact Hc. intros x Hx; clear - Hx; lia.
          intros X. apply (NCQ a). clear - X Hlc; subst n8; lia. exact Hc. }
        intros a (Ha & Hc & Ho). apply FRM7. exact Ha. subst W7; cbn beta. intros [[X|X]|X].
        - apply (NCF a). left; clear - X; lia. exact Hc.
        - apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc.
        - subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc. }
      assert (D07 : dk L ar LB FF (spq + 16) 4272 M M7).
      { eapply dk_trans. apply dk_grows. exact MGM1.
        eapply dk_trans. apply (dk_rt L ar LB FF [] (spq + 16) 4272 (spq - 128) 512 M1 M2 PRES2). clear; lia. clear; lia.
        eapply dk_trans. apply dk_grows. exact MGM3.
        eapply dk_trans. apply (dk_callee L ar LB [] FF [(F, 1, spq - 128 + 32)] (spq + 16) 4272 (spq - 128) OPNEW_SCR [] M3 M4 PRES4). unfold OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
        eapply dk_trans. apply dk_grows. exact MGM5.
        eapply dk_trans. 2:{ apply dk_grows. exact MGM7. }
        intros a Ha Hc HM. destruct (rng_dec a q (q + n8)) as [X|X].
        { destruct (BYTES (a - q) ltac:(clear - X; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (q + (a - q)) with a in Bv by (clear; lia). rewrite Bv. discriminate. }
        destruct (rng_dec a (spq - 128 - 2560) (spq - 128)) as [Y|Y]. apply SDEF6. exact Y.
        rewrite PRES6. exact HM. exact Ha. apply aclient_consb. apply aclient_cons. apply (aclient_narrow L ar LB FF (spq + 16) 4272). exact Hc. exact Y. exact X. }
      (* [comment removed for export] *)
      assert (AGO7 : forall a, o <= a < o + 24 -> M7 (Z_to_bv 64 a) = M3v (Z_to_bv 64 a)).
      { intros a Ha. assert (Ra : RNG4 a). { left. subst RNG; cbn beta. clear - Ha; lia. }
        rewrite FRM7. 2: clear - Ha OR; lia. 2:{ subst W7; cbn beta. clear - Ha OR OF OFL OBIG FR F8; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        rewrite <- (AG6 a Ra ltac:(clear - Ha; lia)). unfold MV6. rewrite (mrestrict_visible H6 M6) by (apply RV6; exact Ra). reflexivity. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (O24_7 : L5.u64_at RSEGS M7 (o + 24) q).
      { eapply L5C.u64_at_agree. 4: exact cO24. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj.
        assert (Ra : RNG4 j). { left. subst RNG; cbn beta. clear - Hj; lia. }
        rewrite FRM7. 2: clear - Hj OR; lia. 2:{ subst W7; cbn beta. clear - Hj OR OF OFL OBIG FR F8; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        rewrite PRES6. 2: clear - Hj OR; lia. 2:{ apply stack_client. clear - Hj OR SLO; lia. clear - Hj OR; lia. } 2:{ intros X; apply (QRNG j Ra). clear - X Hlc; subst n8; lia. }
        apply EQ5. apply RV4. exact Ra. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      apply (KONT fx7 R7 M7 model7 q LB4 cr4 LK2 A4).
      * (* [comment removed for export] *)
        apply preserved_by_index. intros k Hk. cbn in Hk.
        destruct Hk as [<-|Hk]. { rewrite eR2. rewrite <- r2, G2. reflexivity. }
        destruct Hk as [<-|Hk]. { rk. }
        destruct Hk as [<-|Hk]. { rk. }
        destruct Hk as [<-|Hk]. { rewrite eR8. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR9. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR18. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR19. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR20. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR21. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR22. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR23. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR24. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR25. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rewrite eR26. symmetry. apply U_to. }
        destruct Hk as [<-|Hk]. { rk. }
        destruct Hk.
      * reflexivity.
      * reflexivity.
      * (* [comment removed for export] *)
        split. exact BRq. split. exact BAq. split. { eapply fframes_apart_tl. exact FAq. }
        split. { eapply L5.defined_grows. exact MGM7. intros i Hi. destruct (rng_dec (q + i) q (q + n8)) as [X|X].
                 { destruct (BYTES (q + i - q) ltac:(clear - X; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (q + (q + i - q)) with (q + i) in Bv by (clear; lia). rewrite Bv. discriminate. }
                 rewrite PRES6. apply MGM5. apply DEFq. exact Hi. clear - Hi Q0 Q4 SPT; lia.
                 apply (block_client L ar LB4 FF' _ _ q (8 * cap)). left; reflexivity. clear - Hi; lia. exact X. }
        destruct SHBq as [SZq _]. split. 2:{ intros X. exfalso. apply X. clear. rewrite Z.mul_comm. apply Z_mod_mult. }
        rewrite (proj2 (proj2 (proj2 QSH))) in SZq |- *.
        intros j Hj. unfold byte_at.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (SHJ : SB <= S q + j < 0x10007fff8000 /\ (S q + j + 1 <= F / 8 + SB \/ F / 8 + SB + 16 <= S q + j)). { unfold S. clear - Hj QSH QF F8 Q2 Hcap. unfold SB in *. lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        rewrite FRM7. 2: clear - SHJ; unfold S, SB in *; lia. 2:{ subst W7; cbn beta. clear - SHJ FR FBIG FLR FLBIG. unfold S, SB in *. lia. }
        rewrite PRES6. 2: clear - SHJ; unfold S, SB in *; lia. 2:{ right; right; right; right; right; right. exists (q, 8 * cap). split. left; reflexivity. cbn [fst snd]. unfold in_shadow_of. clear - Hj QSH Hcap.
             unfold S, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        2:{ clear - SHJ Q5 Hcap Hlc; subst n8; unfold S, SB in *; lia. }
        rewrite FRM5. apply SZq. exact Hj. clear - SHJ; unfold S, SB in *; lia. subst W4; cbn beta. clear - SHJ Q5 Hcap OBIG OR; unfold S, SB in *; lia.
      * (* [comment removed for export] *)
        unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
        split. { eapply L5C.u8_at_agree. 4: exact bO0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AGO7. clear - Hj; lia. }
        split. exact FBR.
        split. { eapply L5C.u64_at_agree. 4: exact bO8. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AGO7. clear - Hj; lia. }
        split. exact FBT.
        split. { eapply L5C.u64_at_agree. 4: exact bO16. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AGO7. clear - Hj; lia. }
        split. exact O24_7.
        split. exact Hlc. split. exact Hcap. split. { clear - Q2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        split. exact Q0. split. clear - Q4 SPT; lia. apply hull_apart_of. exact Q1.
      * (* [comment removed for export] *)
        split. exact Lws. split. exact Rws. cbn [L5.bo_st]. apply limbs_at_of_bytes. clear - Q0; lia. rewrite Lws; clear - Q4 SPT Hlc; lia.
        intros i Hi. rewrite Lws in Hi. destruct (BYTES (Z.of_nat i) ltac:(clear - Hi; subst n8; lia)) as (v & [Nv _] & Bv). unfold byte_at in Bv. rewrite Nat2Z.id in Nv.
        rewrite FRM7. rewrite Bv. symmetry. exact Nv. clear - Hi Q0 Q4 SPT Hlc; lia.
        subst W7; cbn beta. clear - Hi Hlc Hcap QF QFL FR F8 Q5 Q2; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      * Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        rewrite SCR_EQ. apply ahpres_of. exact E07. eapply astk_defined. exact ASTK7. clear; lia. clear; lia. exact D07.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3.
        eapply L5LZ.model_rt_trans. exact RT4. eapply L5LZ.model_rt_trans. exact RT5. eapply L5LZ.model_rt_trans. exact RT6. exact RT7.
      * exact IA4.
      * exact AM7.
      * exact LKI2.
      * exact HH7.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem copy_stk16_ok : opnew_spec L ar HI -> copy_stk16_spec.
Proof.
  intros NEW fx R M model K LB FF LK cr A o o' spq r fbo b' ws' HH AM HK G10 G11 CAP G1 RA G2 A32 G4 STK ROOM RS OFB FBO AOB ODEF SZ OB' OL' AOB' SZ' INB KONT.
  pose proof STK as STK0. rewrite SCR_EQ in STK. change (4256 + 16) with 4272 in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= (spq + 16) < 2 ^ 64 /\ 140735332487424 <= (spq + 16) <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (sobj_facts LB FF LK cr A M model o 32 (spq + 16) (spq + 16) 4272 HH AOB ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - SLO; lia) ltac:(clear; lia))
    as (OR & OBIG & _ & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o' 32 (spq + 16) 4272 HH AOB' ltac:(clear; lia) ltac:(reflexivity))
    as (YR & YBIG & YDEF & YVIS & YVSH & YCL & YCLSH). change (32 / 8) with 4 in YVSH, YCLSH.
  pose proof (sobj_vis LB FF LK cr A M model o (spq + 16) HH AOB ODEF SZ SPT ltac:(clear - SLO; lia)) as (XO & XBo & OZv & OWv).
  pose proof (obj_vis LB FF LK cr A M model o' HH AOB' SZ') as (XY & XBy & YZv & _).
  assert (APART : o + 32 <= o' \/ o' + 32 <= o) by (right; clear - OR YR SLO; lia).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W16 : L5.writable RSEGS MV spq 16).
  { apply (proj2 (writable_vis H M spq 16 (VIS spq 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M (spq + 16)). exact STK. clear; lia. clear; lia. clear; lia. }
  destruct b' as [fby leny sto']. pose proof OB' as (Y0 & Hfby & Y8 & OST'). unfold L5.bo_dyn, L5.bo_cap in CAP.
  cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  assert (HV2 : 140735332487184 <= (spq + 16) <= 140737488355328) by (clear - SPR SLO SPT; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVY : 4096 <= o' <= 140737488355296) by (clear - YR; lia).
  assert (ALO : aligned o 8) by (exact (proj1 (proj2 (proj2 (proj2 OR))))). assert (ALY : aligned o' 8) by (exact (proj1 (proj2 (proj2 (proj2 YR))))).
  assert (ALS : aligned spq 32) by exact A32.
  assert (FRO : spq + 16 <= o \/ o + 32 <= spq) by (clear - OR SLO; lia). assert (FRY : spq + 16 <= o' \/ o' + 32 <= spq) by (clear - YR SLO; lia).
  assert (FBO' : 0 <= fbo <= 255) by (clear - FBO; lia). assert (FBY' : 0 <= fby <= 255) by (clear - Hfby; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  (* [comment removed for export] *)
  assert (AFTER : forall M1, mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (spq <= a < (spq + 16)) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
            (forall a, 0 <= a -> (a + 1 <= ahl_ceil ar \/ (spq + 16) <= a < 2 ^ 47) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ ek L ar LB FF (spq + 16) 4272 [(o, 32)] M M1 /\ dk L ar LB FF (spq + 16) 4272 M M1).
  { intros M1 MG FR1. split. { intros a Ha Hc. apply FR1. clear - Ha Hc SPT; lia. clear - Hc SLO; lia. }
    split. { apply (ek_piece L ar LB FF (spq + 16) 4272 [(o, 32)] M M1 _ FR1). intros a Ha Hc _ X.
             destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) 4272 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia. }
    apply dk_grows. exact MG. }
  destruct sto' as [w0 w1|cap qy].
  - (* [comment removed for export] *)
    destruct OST' as (BT0 & Y16 & Y24 & Hl2 & Rw0 & Rw1).
    pose proof (fb_inl fbo fby FBO Hfby) as (FIE & FIR & FIT).
    pose proof (cp16I_conc fx R MV (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => o' | 35%nat => fbo | 36%nat => fby | 37%nat => Z.of_nat leny | 38%nat => w0 | 39%nat => w1 | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | sc]) | (apply XY; [clear; lia | sc]) | (apply XBo; sc) | (apply XBy; sc) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & iFR & iFZ & (iMS & iKS & iR10 & iR11 & iR12 & iR13 & iR14 & iR15 & iR16 & iO24 & iO16 & iO8 & iO0)).
    rewrite FIE in iO0.
    pose proof (ret_to fx1 R1 M1v 0x92218 W_92218 r F_92218 eq_refl D_92218 ltac:(rewrite (iKS 1%nat) by inl; rewrite <- r1; exact G1) (proj1 RA) (proj2 RA)) as RET.
    pose proof (msteps_trans _ _ _ _ iMS RET) as MS2. clear iMS RET.
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R COPY R1 r M1v (fun a => spq <= a < (spq + 16) \/ o <= a < o + 32) K HH AM MS2 MG1).
    { intros a Ha Hna. apply iFZ. exact Ha. clear - Hna; lia. clear - Hna; lia. }
    { intros a Ha [Wa|Wa]. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
      split. apply stack_client. clear - Wa OR SLO; lia. clear; lia. clear - Wa OR; lia. }
    intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
    assert (OV : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hc. apply (proj1 (u64_at_vis H M1 a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Ha; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Ha OR; lia))). unfold H. rewrite VIS1. exact Hc. }
    apply (KONT fx1 R1 M1 model1 Same LB cr LK A).
    + split. { apply preserved_by_index. intros k Hk. apply iKS. revert Hk. apply (L5K.incl_b _ KS_cp16I); vm_compute; reflexivity. }
      cbn iota. split. unfold L5.bo_dyn; cbn [L5.bo_fb]. exact BT0. split. reflexivity. split. reflexivity.
      split. { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
               split. { apply (proj1 (u8_at_vis H M1 o _ ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). unfold H. rewrite VIS1. exact iO0. }
               split. exact FIR. split. { apply OV. clear; lia. exact iO8. } split. exact FIT. split. { apply OV. clear; lia. exact iO16. } split. { apply OV. clear; lia. exact iO24. }
               split. exact Hl2. split. exact Rw0. exact Rw1. }
      rewrite SCR_EQ.
      apply ahpres_of. 2:{ eapply astk_defined. eapply astk_grows. exact STK. exact MGM1. clear; lia. clear; lia. } 2:{ apply dk_grows. exact MGM1. }
      apply (ek_piece L ar LB FF (spq + 16) 4272 [(o, 32)] M M1 _ FRM1). intros a Ha Hc Ho [X|X].
      destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) 4272 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia.
      apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia.
    + exact RT1. + apply incl_refl. + exact AM1. + apply incl_refl. + exact HH1.
  - (* [comment removed for export] *)
    destruct OST' as (BT1 & Y16 & Y24 & Hlc & Hcap & QY8 & QY4096 & QY47 & QYH).
    pose proof (cp16D_conc fx R MV (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => o' | 35%nat => fbo | 36%nat => fby | 37%nat => Z.of_nat leny | 38%nat => cap | 39%nat => qy | _ => 0 end)) as P.
    cbn beta iota in P.
    assert (HVC : 0 <= cap < 2 ^ 64) by (clear - Hcap; lia). assert (HVQY : 0 <= qy < 2 ^ 64) by (clear - QY4096 QY47 Hcap; lia).
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | sc]) | (apply XY; [clear; lia | sc]) | (apply XBo; sc) | (apply XBy; sc) ]).
    destruct P as (fx1 & R1 & M1v & MG1 & dFR & dFZ & (dMS & dKS & dR12 & dR13)).
    apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R COPY R1 ACOPY M1v (fun a => spq <= a < (spq + 16)) K HH AM dMS MG1).
    { intros a Ha Hna. apply dFZ. exact Ha. clear - Hna; lia. }
    { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
    intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
    destruct (AFTER M1 MGM1 FRM1) as (AG1 & E01 & D01).
    pose proof (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) _ (INB cap qy eq_refl)) as ((_ & _ & _ & _ & QB4 & _) & _). cbn [fst snd] in QB4.
    apply (acopy_run NEW fx1 R1 M1 model1 K LB FF LK cr A o o' spq r fbo (L5.BO fby leny (L5.BDyn cap qy)) ws' HH1 AM1 HK).
    + rewrite r10, (dKS 10%nat) by inl. rewrite <- r10. exact G10.
    + rewrite r11, (dKS 11%nat) by inl. rewrite <- r11. exact G11.
    + exact CAP.
    + rewrite r1, (dKS 1%nat) by inl. rewrite <- r1. exact G1.
    + exact RA.
    + rewrite r2, (dKS 2%nat) by inl. rewrite <- r2. exact G2.
    + exact A32.
    + rewrite r4, (dKS 4%nat) by inl. rewrite <- r4. exact G4.
    + eapply astk_grows. exact STK0. exact MGM1.
    + exact ROOM.
    + exact RS.
    + eapply L5C.u8_at_agree. 4: exact OFB. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AG1. clear - Hj OR; lia. clear - Hj OR; lia.
    + exact FBO.
    + exact AOB.
    + eapply L5.defined_grows. exact MGM1. exact ODEF.
    + intros j Hj. unfold byte_at. rewrite AG1. apply SZ. exact Hj. all: unfold S; clear - Hj OR SPT; unfold SB. 
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      all: lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      eapply L5C.big_at_agree. 4: exact OB'. 2: clear - YR; lia. 2: clear - YR; lia. intros j Hj. apply AG1. clear - Hj YR; lia. clear - Hj YR; lia.
    + destruct OL' as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT |- *. split. exact Lws. split. exact Rws.
      eapply L5C.limbs_at_agree. 4: exact LAT. 2: clear - QY4096; lia. 2: rewrite Lws; clear - QY47 Hlc; lia.
      intros j Hj. apply AG1. clear - Hj QY4096; lia. rewrite Lws in Hj. clear - Hj QB4 Hlc; lia.
    + exact AOB'.
    + intros j Hj. unfold byte_at. rewrite AG1. apply SZ'. exact Hj. all: unfold S; clear - Hj YR SPT; unfold SB.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      all: lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      exact INB.
    + exact APART.
    + unfold L5.bo_dyn; cbn [L5.bo_fb]. exact BT1.
    + cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_cap]. intros fx' R' M' model' q LB' cr' LK' A' RP' ELB Ecr FRESH BIG LIMBS AHP RT' IA' AM' LKI' HH'.
      apply (KONT fx' R' M' model' (Grown q cap) LB' cr' LK' A').
      * split. { eapply regs_preserved_trans. 2: exact RP'. apply preserved_by_index. intros k Hk. apply dKS. revert Hk. apply (L5K.incl_b _ KS_cp16D); vm_compute; reflexivity. }
        cbn iota. split. unfold L5.bo_dyn; cbn [L5.bo_fb]. exact BT1. split. reflexivity. split. exact ELB. split. exact Ecr. split. exact FRESH. split. exact BIG. split. exact LIMBS.
        destruct AHP as (P1 & P2 & P3). split. { intros a Ka. rewrite (P1 a Ka). apply E01. exact Ka. } split. exact P2.
        intros a Ha Hc HM. apply P3. exact Ha. exact Hc. apply MGM1. exact HM.
      * eapply L5LZ.model_rt_trans. exact RT1. exact RT'.
      * exact IA'.
      * exact AM'.
      * exact LKI'.
      * exact HH'.
Qed.

End WithIface.
End SCFG_1.
End L5BCPS16.
