(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ARed L5AMul10K L5AShrP L5AShr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASHROK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AMULK. Import L5ASHRP. Import L5ASHR. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].

Definition SHR_SCR : Z := 64 + RESIZE_SCR.
Lemma SCR_EQ : SHR_SCR = 4560. Proof. reflexivity. Qed.
Lemma RZSCR_EQ : RESIZE_SCR = 4496. Proof. reflexivity. Qed.

Definition shr_postC (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe)
           (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp : Z) (b : L5.bigobj) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  exists (rw : list Z) (st' : L5.bstore),
    length rw = L5.bo_len b /\ words_ok rw /\
    (let n' := rlen rw in
     let fb' := if Nat.eqb (L5.bo_len b) 0 then L5.bo_fb b else if Nat.eqb n' 0 then Z.land (L5.bo_fb b) 253 else L5.bo_fb b in
     L5.big_at RSEGS M' o (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' (L5.bo_len b) st') rw) /\
    match L5.bo_st b, st' with
    | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
    | L5.BInl _ _, L5.BInl _ _ => True
    | _, _ => False end /\
    ahpres L ar LB FF sp SHR_SCR [(o, 32); (L5.bo_data o b, 8 * Z.of_nat (L5.bo_len b))] M M'.

Definition shr_specA (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r k : Z) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 k -> 1 <= k <= 63 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SHR_SCR ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)),
        shr_postC L ar LB FF M M' R R' o sp b ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R SHR M model) K.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

(* [comment removed for export] *)
Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 860160 880640 /\ L5.u64_at RSEGS MV 908088 2147450880 /\ L5.u32_at RSEGS MV 908096 1.
Proof.
  intros HH. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG 908088 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG 908096 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma block_vis LB FF LK cr A M model q c sp :
  ri_inv HI LB FF LK cr A M (vml_of model) -> In (q, 8 * c) LB -> 1 <= c -> ahl_ceil ar + 4096 <= sp -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  let MV := mrestrict (ahid A model) M in
  (4096 <= q /\ q + 8 * c <= 140737479966720) /\ q mod 8 = 0 /\ (2147446784 + 17592186048512 <= q \/ q + 8 * c <= 2147446784)
  /\ (sp - 64 + 64 <= q \/ q + 8 * c <= sp - 4096) /\ (q + 8 * c <= q / 8 + SB \/ q / 8 + SB + c <= q) /\ (q + 8 * c <= 65536 \/ 6500352 <= q)
  /\ L5.writable RSEGS MV q (8 * c) /\ L5KA.zeros_at MV (q / 8 + SB) c /\ avis (ahid A model) q (8 * c)
  /\ (forall a v, q <= a -> a + 8 <= q + 8 * c -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
Proof.
  intros HH INB Hc SLO SPT MV.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof (WB _ INB) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & QDEF & QSH & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5, QDEF, QSH.
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & _ & _ & VBLK & VBSH & _).
  assert (QV : avis (ahid A model) q (8 * c)). { apply (VBLK q (8 * c)). exact INB. lia. lia. }
  split. lia. split. lia. split. lia. split. lia. split. { unfold SB. lia. } split. lia.
  split. { apply (proj2 (writable_vis _ M q (8 * c) QV ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact QDEF. lia. lia. }
  split. { apply (proj2 (zeros_at_vis _ M (q / 8 + SB) c ltac:(apply (VBSH q (8 * c)); [exact INB | intros i Hi; unfold in_shadow_of, S; lia]))).
           intros i Hi. destruct QSH as [SZq _]. unfold shadow_zero, byte_at, S in SZq. apply SZq. lia. }
  split. exact QV.
  intros a v Ha Hb Hx. apply (proj2 (u64_at_vis _ M a v ltac:(eapply avis_sub; [exact QV | lia | lia]) ltac:(lia) ltac:(lia))). exact Hx.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma shr_pos_ok : forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r k : Z) (b : L5.bigobj) (ws : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 k -> 1 <= k <= 63 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> astk ar M sp SHR_SCR ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> aobj FF o 32 -> shadow_zero M o 4 -> (1 <= L5.bo_len b)%nat ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        shr_postC L ar LB FF M M' R R' o sp b ->
        model_rt model model' -> amodel_ok A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R SHR M model) K.
Proof.
  intros fx R M model K LB FF LK cr A o sp r k b ws HH AM HK G10 G11 Hk G1 RA G2 A32 STK OB OL AOB SZ Lpos INB KONT.
  pose proof STK as STK0. rewrite SCR_EQ in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491728 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 4560 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (OZv : L5KA.zeros_at MV (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (W64 : L5.writable RSEGS MV (sp - 64) 64).
  { apply (proj2 (writable_vis H M (sp - 64) 64 (VIS (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear; lia. clear; lia. clear; lia. }
  assert (W80 : L5.writable RSEGS MV (sp - 80) 16).
  { apply (proj2 (writable_vis H M (sp - 80) 16 (VIS (sp - 80) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    apply (L5C.writable_of_defined RSEGS). eapply astk_defined. exact STK. clear; lia. clear; lia. clear - SPR; lia. clear - SPR; lia. }
  destruct b as [fb len sto]. cbn [L5.bo_len L5.bo_st L5.bo_fb] in Lpos, INB.
  set (d := L5.bo_data o (L5.BO fb len sto)). set (cap := L5.bo_cap (L5.BO fb len sto)).
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  assert (DF : mfacts MV sp o d cap /\ avis H d (8 * cap) /\ (forall a v, d <= a -> a + 8 <= d + 8 * cap -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v)
               /\ Z.of_nat len <= cap /\ match sto with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end
               /\ (forall a, d <= a < d + 8 * Z.of_nat len -> aclientw L ar LB FF 0 0 a /\ ~ (0x10000 <= a < 0x633000))).
  { subst d cap. unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st]. destruct sto as [u0 u1|c q].
    - destruct OST as (Bb & O16b & O24b & Hl2b & Ru0 & Ru1). split. 2: split. 3: split. 4: split. 5: split.
      + constructor. clear - SPR A16; lia. exact W64. split. exact IMGC. split. exact CSB. exact CUAR. clear - OR OBIG SLO; lia. exact OZv. exact OWv.
        { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          repeat split; clear - OR OBIG SLO SPT; unfold SB; lia. }
        eapply L5.writable_sub. exact OWv. clear; lia. clear; lia. eapply L5KA.zeros_at_sub. exact OZv. 2: clear; lia. clear - OR. lia.
      + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        eapply avis_sub. exact OVIS. clear; lia. clear; lia.
      + intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc.
      + clear - Hl2b; lia. + exact I.
      + intros a Ha. split. apply (obj_client L ar LB FF 0 0 o 32 a AOB). clear - Ha Hl2b; lia. clear - Ha OR Hl2b; lia.
    - destruct OST as (Bb & O16b & O24b & Hlcb & Hcapb & Q8b & Q4096b & Q47b & QHb). pose proof (INB c q eq_refl) as STB.
      pose proof (block_vis LB FF LK cr A M model q c sp HH STB ltac:(clear - Hcapb; lia) ltac:(clear - SLO; lia) SPT) as (QR & QD8 & QBIG & QFR & QSHD & QIMG & QW & QZ & QV & XQ).
      fold H in QV, XQ. fold MV in QW, QZ, XQ.
      assert (QO : o + 32 <= q \/ q + 8 * c <= o).
      { destruct AOB as (g0 & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ STB)))))) g0 ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X. clear - X X1 X2 Hcapb. lia. }
      split. 2: split. 3: split. 4: split. 5: split.
      + constructor. clear - SPR A16; lia. exact W64. split. exact IMGC. split. exact CSB. exact CUAR. clear - OR OBIG SLO; lia. exact OZv. exact OWv.
        { split. exact QR. split. exact QD8. split. exact QBIG. split. clear - Hcapb; lia. split. exact QFR. split. clear - QO; lia. split. exact QSHD. exact QIMG. } exact QW. exact QZ.
      + exact QV. + exact XQ. + exact Hlcb. + exact QO.
      + intros a Ha. split. apply (block_client L ar LB FF 0 0 q (8 * c)). exact STB. clear - Ha Hlcb; lia. clear - Ha QIMG Hlcb; lia. }
  destruct DF as (MF & DV & XD & CAPb & ODYN & DCL).
  assert (OBv : L5.big_at RSEGS MV o (L5.BO fb len sto)).
  { eapply L5C.big_at_agree. 4: exact OB. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. unfold MV. apply mrestrict_visible. replace j with (o + (j - o)) by (clear; lia). apply (OVIS (j - o)). clear - Hj; lia. }
  assert (OLv : L5C.obj_limbs RSEGS MV (L5.BO fb len sto) ws).
  { destruct OL as (L1 & R1' & LAT2). cbn [L5.bo_len L5.bo_st] in L1, LAT2 |- *. split. exact L1. split. exact R1'. destruct sto as [u0 u1|c q]. exact LAT2.
    subst d cap. unfold L5.bo_data, L5.bo_cap in XD, CAPb. cbn [L5.bo_st] in XD, CAPb. intros i Hi. apply XD. clear - Hi; lia. rewrite L1 in Hi. clear - Hi CAPb; lia. apply LAT2. exact Hi. }
  (* [comment removed for export] *)
  destruct (shr_runA fx R MV o sp r k (L5.BO fb len sto) ws) as (fx3 & R3 & M3v & MS3 & rw & RL & RO & [OB3 LIM3] & K3 & R3_2 & R3_10 & FR3 & GR3).
  { rewrite <- r10. exact G10. } { rewrite <- r11. exact G11. } { exact Hk. } { rewrite <- r1. exact G1. } { exact RA. } { rewrite <- r2. exact G2. }
  { exact Lpos. } { exact MF. } { exact W80. } { exact OBv. } { exact OLv. } { exact ODYN. }
  cbn [L5.bo_len L5.bo_fb L5.bo_st] in RL, OB3, LIM3, FR3. fold d in LIM3, FR3.
  set (W3 := fun a => d <= a < d + 8 * Z.of_nat len \/ o <= a < o + 16 \/ sp - 80 <= a < sp).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx3 R SHR R3 r M3v W3 K HH AM MS3 GR3).
  { intros a Ha Hna. apply FR3. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
    - apply DCL. exact Wa.
    - split. apply (obj_client L ar LB FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia.
    - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (ASTK3 : astk ar M3 sp 4560). { eapply astk_grows. exact STK. exact MGM3. }
  (* [comment removed for export] *)
  pose proof (L5W.rlen_le rw) as RLE. rewrite RL in RLE.
  set (n' := L5W.rlen rw) in *.
  set (stF := st_after sto rw) in *.
  set (fbF := if Nat.eqb n' 0 then Z.land fb 253 else fb) in *.
  assert (OB3' : L5.big_at RSEGS M3 o (L5.BO fbF n' stF)).
  { eapply L5C.big_at_agree. 4: exact OB3. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. symmetry. rewrite <- VIS3. apply mrestrict_visible.
    replace j with (o + (j - o)) by (clear; lia). apply (OVIS (j - o)). clear - Hj; lia. }
  assert (OL3' : L5C.obj_limbs RSEGS M3 (L5.BO fbF len stF) rw).
  { split. exact RL. split. exact RO.
    cbn [L5.bo_st L5.bo_len]. subst stF. unfold st_after. destruct sto as [u0 u1|cR qR].
    - destruct OST as (_ & _ & _ & Hl2b & _). rewrite <- RL.
      destruct rw as [|a0 [|b0 [|c0 l]]]; cbn [length] in *; try (exfalso; clear - RL Hl2b Lpos; lia); reflexivity.
    - intros i Hi. rewrite RL in Hi.
      subst d cap. unfold L5.bo_data, L5.bo_cap in *. cbn [L5.bo_st] in *. apply (proj1 (u64_at_vis (ahid A model) M3 (qR + 8 * Z.of_nat i) (nth i rw 0) ltac:(eapply avis_sub; [exact DV | clear - Hi; lia | clear - Hi CAPb; lia])
               ltac:(destruct OST as (_ & _ & _ & _ & _ & _ & Q4 & _); clear - Q4 Hi; lia) ltac:(destruct OST as (_ & _ & _ & Hlc4 & _ & _ & _ & Q47' & _); clear - Q47' Hlc4 Hi; lia))).
      rewrite VIS3. apply LIM3. rewrite RL. exact Hi. }
  assert (SDEF3 : L5.defined M3 (sp - 4560) 4560). { eapply astk_defined. exact ASTK3. clear; lia. clear; lia. }
  apply (KONT fx3 R3 M3 model3).
  - unfold shr_postC. split.
    { apply preserved_by_index. intros j Hj. cbn in Hj.
      destruct Hj as [<-|Hj]. { rewrite R3_2. rewrite <- r2, G2. reflexivity. }
      apply K3. revert Hj. clear. intros Hj. unfold KSF. cbn [In] in *. tauto. }
    split. { rewrite r10. exact R3_10. }
    exists rw, stF. cbn [L5.bo_len L5.bo_fb L5.bo_st]. split. exact RL. split. exact RO.
    split. { cbn zeta. fold n'. replace (Nat.eqb len 0) with false by (symmetry; apply Nat.eqb_neq; clear - Lpos; lia). fold fbF. split. exact OB3'. exact OL3'. }
    split. { subst stF. unfold st_after. destruct sto as [w0 w1|c q]. exact I. split; reflexivity. }
    rewrite SCR_EQ. apply ahpres_of. 2: exact SDEF3. 2:{ apply dk_grows. exact MGM3. }
    apply (ek_piece L ar LB FF sp 4560 _ M M3 W3 FRM3).
    intros a Ha Hc Ho Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
    + apply (Ho (d, 8 * Z.of_nat len)). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Wa.
    + apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - Wa; lia.
    + destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4560 a HH SPT Hc) as [Y|Y]. clear - Wa Y; lia. clear - Wa Y SLO; lia.
  - exact RT3.
  - exact AM3.
  - exact HH3.
Qed.

(* [comment removed for export] *)
Lemma shr_zero_ok : resize_spec L ar HI ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r k fb : Z) (sto : L5.bstore),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 k -> 1 <= k <= 63 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SHR_SCR ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o (L5.BO fb 0 sto) -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall cap q, sto = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)),
        shr_postC L ar LB FF M M' R R' o sp (L5.BO fb 0 sto) ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R SHR M model) K.
Proof.
  intros RZ fx R M model K LB FF LK cr A o sp r k fb sto HH AM HK G10 G11 Hk G1 RA G2 A32 G4 STK ROOM RS OB AOB SZ INB KONT.
  pose proof STK as STK0. rewrite SCR_EQ in STK. pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491728 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (SA : (sp - 64) mod 32 = 0 /\ (sp - 64) mod 16 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SA as [SA32 SA16].
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp 4560 HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (XO : forall a v, o <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v Ha Hb Hc. apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact OVIS | clear - Ha; lia | clear - Hb; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Hb OR; lia))). exact Hc. }
  assert (XB : forall v, L5.u8_at RSEGS M o v -> L5.u8_at RSEGS MV o v).
  { intros v Hc. apply (proj2 (u8_at_vis H M o v ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact Hc. }
  assert (OZv : L5KA.zeros_at MV (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (W64 : L5.writable RSEGS MV (sp - 64) 64).
  { apply (proj2 (writable_vis H M (sp - 64) 64 (VIS (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear; lia. clear; lia. clear; lia. }
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST. change (Z.of_nat 0) with 0 in O8.
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact (proj1 (proj2 (proj2 (proj2 OR)))).
  assert (HV2 : 140735332487232 <= sp <= 140737488355328) by (clear - SPR; lia). assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia).
  assert (FRO : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - OR SLO; lia). assert (HVF : 0 <= fb <= 255) by (clear - Hfb; lia).
  assert (HVL0 : 0 <= 0 <= 0) by (clear; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  (* [comment removed for export] *)
  assert (RUN : exists fx1 R1 M1v, mem_grows MV M1v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R SHR MV) (st fx1 R1 RESIZE M1v) /\ (forall j, In j [3; 4; 10; 23; 24; 25; 26; 27]%nat -> getr R1 (reg j) = getr R (reg j))
            /\ getr R1 (reg 1) = Z_to_bv 64 607016 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 0
            /\ L5.u64_at RSEGS M1v (sp - 64) (U R 22) /\ L5.u64_at RSEGS M1v (sp - 56) (U R 21) /\ L5.u64_at RSEGS M1v (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1v (sp - 40) (U R 19)
            /\ L5.u64_at RSEGS M1v (sp - 32) (U R 18) /\ L5.u64_at RSEGS M1v (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1v (sp - 16) (U R 8) /\ L5.u64_at RSEGS M1v (sp - 8) (U R 1)).
  { destruct sto as [w0 w1|cap q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1).
      pose proof (vsrZ_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => 0 | 35%nat => fb | 41%nat => k | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | clear; lia | sc]) | (apply XB; sc) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR20 & aR21 & aR22 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. split. exact MG1. split. exact aFZ. split. exact aMS. split. { intros j Hj. apply aKS. revert Hj; apply (L5K.incl_b _ KS_vsrZ); vm_compute; reflexivity. }
      unfold U. repeat split; assumption.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
      assert (HVQ : 0 <= q <= 18446744073709551615) by (clear - Q4096 Q47 Hcap; lia).
      pose proof (vsrZd_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => 0 | 35%nat => fb | 36%nat => q | 41%nat => k | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XO; [clear; lia | clear; lia | sc]) | (apply XB; sc) ]).
      destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR18 & aR20 & aR21 & aR22 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
      exists fx1, R1, M1v. split. exact MG1. split. exact aFZ. split. exact aMS. split. { intros j Hj. apply aKS. revert Hj; apply (L5K.incl_b _ KS_vsrZd); vm_compute; reflexivity. }
      unfold U. repeat split; assumption. }
  destruct RUN as (fx1 & R1 & M1v & MG1 & AFZ & AMS & AKS & aR1 & aR2 & aR8 & aR11 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R SHR R1 RESIZE M1v (fun a => sp - 64 <= a < sp) K HH AM AMS MG1).
  { intros a Ha Hna. apply AFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp 4560). { eapply astk_grows. exact STK. exact MGM1. }
  assert (AG1 : forall a, 0 <= a -> a + 1 <= ahl_ceil ar -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros a Ha Hc. apply FRM1. clear - Ha Hc SPT; lia. clear - Hc SLO; lia. }
  (* [comment removed for export] *)
  apply (RZ fx1 R1 M1 model1 K LB FF LK cr A o (sp - 64) 0x94328 0%nat (L5.BO fb 0 sto) [] HH1 AM1 HK).
  - rewrite r10, (AKS 10%nat) by inl. rewrite <- r10. exact G10.
  - rewrite r11, aR11. reflexivity.
  - cbn. clear; lia.
  - intros _. unfold L5.bo_cap. cbn [L5.bo_st]. destruct sto as [w0 w1|cap q]. cbn; clear; lia. destruct OST as (_ & _ & _ & _ & Hcap & _). cbn; clear - Hcap; lia.
  - intros H3. exfalso. clear - H3. lia.
  - rewrite r1. exact aR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact aR2.
  - exact SA32.
  - rewrite r4, (AKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite RZSCR_EQ. apply (astk_sub ar M1 M1 sp 4560 64 4496 ASTK1 (mem_grows_refl M1)). clear; lia. clear; lia. clear; lia. exact SA16.
  - exact ROOM.
  - intros f Hf. specialize (RS f Hf). clear - RS; lia.
  - eapply L5C.big_at_agree. 4: exact OB. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply AG1. clear - Hj OR; lia. clear - Hj OR; lia.
  - split. reflexivity. split. constructor. cbn [L5.bo_st L5.bo_len]. destruct sto as [w0 w1|cap q]. reflexivity. intros i Hi. exfalso. cbn in Hi. clear - Hi. lia.
  - exact AOB.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    intros j Hj. unfold byte_at. rewrite AG1. apply SZ. exact Hj. all: unfold S; clear - Hj OR SPT; unfold SB; lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    intros cap q E. apply INB. exact E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 LK2 A2 POST RT2 IA2 AM2 LKI2 HH2.
    destruct POST as [RP2 GPOST].
    destruct g as [|gq gc]. 2:{ exfalso. destruct GPOST as (_ & H3 & _). clear - H3. lia. }
    destruct GPOST as (DY & ELB & ECR & (st' & OB2 & OL2 & STM) & AH2). subst LB2 cr2.
    cbn [L5.bo_fb L5.bo_st L5.bo_len L5.bo_data] in OB2, OL2, STM, AH2. rewrite RZSCR_EQ in AH2.
    assert (ASTK2 : astk ar M2 sp 4560).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (sp - 64) 4496 _ HH STK MGM1 AH2). clear; lia. clear; lia. clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB FF LK2 cr A2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & _).
    pose proof (statics_vis LB FF LK2 cr A2 M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
    assert (K12 : forall a, sp - 64 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR; lia).
      apply (proj1 AH2 a). split. exact Ha. split. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
      intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. clear - Ra OR SLO; lia. clear; lia. }
    assert (V2F : forall a, sp - 64 <= a < sp -> H2 (Z_to_bv 64 a) = false /\ H (Z_to_bv 64 a) = false).
    { intros a Ra; split.
      - replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS2 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia. }
    assert (XF : forall a v, sp - 64 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj.
      destruct (V2F j ltac:(clear - Ha Hb Hj; lia)) as [Vj Vj0]. unfold MV2. rewrite (mrestrict_visible H2 M2) by exact Vj. rewrite K12 by (clear - Ha Hb Hj; lia).
      rewrite <- VIS1. symmetry. apply mrestrict_visible. exact Vj0. }
    assert (W64b : L5.writable RSEGS MV2 (sp - 64) 64).
    { apply (proj2 (writable_vis H2 M2 (sp - 64) 64 (VIS2 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 sp). exact ASTK2. clear; lia. clear; lia. clear; lia. }
    (* [comment removed for export] *)
    assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
    pose proof (vsrZE_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 43%nat => U R2 1 | 44%nat => r | 45%nat => U R 8 | 46%nat => U R 9 | 47%nat => U R 18
                  | 48%nat => U R 19 | 49%nat => U R 20 | 50%nat => U R 21 | 51%nat => U R 22 | _ => 0 end)) as P.
    cbn beta iota in P.
    assert (G2' : getr R2 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite (cs_of_preserved R1 R2 _ RP2) by inl. exact aR2. }
    assert (G8' : getr R2 (reg 8) = Z_to_bv 64 o). { rewrite (cs_of_preserved R1 R2 _ RP2) by inl. exact aR8. }
    rewrite UR1 in C8.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc]) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22)).
    pose proof (ret_to fx3 R3 M3v 0x943fc As0_code_94368_944b0.W_943fc r As0_code_94368_944b0.F_943fc eq_refl As0_code_94368_944b0.D_943fc eR1 (proj1 RA) (proj2 RA)) as RETs.
    apply (apiece L ar C HI LY HIok LB FF LK2 cr A2 M2 model2 fx2 fx3 R2 0x94328 R3 r M3v (fun _ => False) K HH2 AM2 (msteps_trans _ _ _ _ eMS RETs) MG3).
    { intros a Ha _. apply eFR. }
    { intros a Ha []. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp 4560). { eapply astk_grows. exact ASTK2. exact MGM3. }
    assert (SDEF3 : L5.defined M3 (sp - 4560) 4560). { eapply astk_defined. exact ASTK3. clear; lia. clear; lia. }
    assert (E23 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)). { intros a Ha. apply FRM3. exact Ha. intros []. }
    apply (KONT fx3 R3 M3 model3 LK2 A2).
    + unfold shr_postC. split.
      { apply preserved_by_index. intros j Hj. cbn in Hj.
        assert (CH : forall j', In j' [3; 4; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j') = getr R (reg j')).
        { intros j' Hj1. rewrite (eKS j'). rewrite (cs_of_preserved R1 R2 j' RP2). apply AKS. revert Hj1; apply (L5K.incl_b _ _); vm_compute; reflexivity.
          revert Hj1; apply (L5K.incl_b _ _); vm_compute; reflexivity. revert Hj1; apply (L5K.incl_b _ KS_vsrZE); vm_compute; reflexivity. }
        destruct Hj as [<-|Hj]. { rewrite eR2. rewrite <- r2, G2. reflexivity. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { rewrite eR8. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite eR9. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite eR18. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite eR19. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite eR20. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite eR21. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { rewrite eR22. symmetry. apply U_to. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj as [<-|Hj]. { apply CH; inl. }
        destruct Hj. }
      split. { rewrite r10. exact eR10. }
      exists [], st'. cbn [L5.bo_len L5.bo_fb L5.bo_st length]. split. reflexivity. split. constructor.
      split. { cbn zeta. change (rlen []) with 0%nat. cbn [Nat.eqb].
               split. { eapply L5C.big_at_agree. 4: exact OB2. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply E23. clear - Hj OR; lia. }
               split. reflexivity. split. constructor. cbn [L5.bo_st L5.bo_len]. destruct st' as [u0 u1|c' q']. reflexivity. intros i Hi. exfalso. cbn in Hi. clear - Hi; lia. }
      split. exact STM.
      rewrite SCR_EQ. apply ahpres_of. 2: exact SDEF3.
      * eapply ek_trans. { apply (ek_piece L ar LB FF sp 4560 _ M M1 (fun a => sp - 64 <= a < sp) FRM1).
          intros a Ha Hc _ X. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp 4560 a HH SPT Hc) as [Y|Y]. clear - X Y; lia. clear - X Y SLO; lia. }
        eapply ek_trans. { intros a (Ha & Hc & Ho). apply (proj1 AH2 a). split. exact Ha. split. eapply aclient_mono. exact Hc. intros x Hx; clear - Hx; lia.
          intros rr [<-|[<-|[]]]. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear; lia. }
        intros a (Ha & Hc & Ho). apply E23. exact Ha.
      * eapply dk_trans. apply dk_grows. exact MGM1. eapply dk_trans. 2:{ apply dk_grows. exact MGM3. }
        intros a Ha Hc HM. destruct AH2 as (_ & SD & DK). destruct (rng_dec a (sp - 64 - 4496) (sp - 64)) as [I|O].
        replace a with (sp - 64 - 4496 + (a - (sp - 64 - 4496))) by (clear; lia). apply SD. clear - I; lia.
        apply DK. exact Ha. eapply aclient_narrow. exact Hc. exact O. exact HM.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3.
    + exact IA2.
    + exact AM3.
    + exact LKI2.
    + exact HH3.
Qed.

(* [comment removed for export] *)
Theorem shr_okA : resize_spec L ar HI -> shr_specA L ar HI.
Proof.
  intros RZ fx R M model K LB FF LK cr A o sp r k b ws HH AM HK G10 G11 Hk G1 RA G2 A32 G4 STK ROOM RS OB OL AOB SZ INB KONT.
  destruct (Nat.eq_dec (L5.bo_len b) 0) as [L0|Lpos].
  - destruct b as [fb len sto]. cbn [L5.bo_len] in L0. subst len.
    apply (shr_zero_ok RZ fx R M model K LB FF LK cr A o sp r k fb sto HH AM HK G10 G11 Hk G1 RA G2 A32 G4 STK ROOM RS OB AOB SZ).
    { intros cap q E. apply INB. exact E. } exact KONT.
  - apply (shr_pos_ok fx R M model K LB FF LK cr A o sp r k b ws HH AM HK G10 G11 Hk G1 RA G2 A32 STK OB OL AOB SZ ltac:(clear - Lpos; lia) INB).
    intros fx' R' M' model' POST RT AM' HH'. apply (KONT fx' R' M' model' LK A POST RT (incl_refl _) AM' (incl_refl _) HH').
Qed.

End WithIface.
End SCFG_1.
End L5ASHROK.
