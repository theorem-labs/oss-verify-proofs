(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b PnACxaP_b Ba0_code_r6cfa8_6cfac_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMACXA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
  - rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !L5.unsigned_lit by lia. lia.
  - rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma segs_belowA : segs_below_b RSEGS 0x696000 = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma store_ok_defined (Mx : word -> option byte) a : 0x696000 <= a < 2 ^ 64 ->
  store_ok RSEGS Mx (Z_to_bv 64 a) 1 = true -> Mx (Z_to_bv 64 a) <> None.
Proof.
  intros Ha Hs. cbn [store_ok] in Hs. unfold wview in Hs.
  destruct (Mx (Z_to_bv 64 a)) as [b|]; [discriminate|]. exfalso.
  rewrite (find_segment1_none_above RSEGS 0x696000 (bv_unsigned (Z_to_bv 64 a)) segs_belowA) in Hs by (rewrite L5.unsigned_lit by lia; lia). discriminate.
Qed.
Lemma u64_norm M a v : L5.u64_at RSEGS M a (bv_unsigned (Z_to_bv 64 v)) -> L5.u64_at RSEGS M a v.
Proof. unfold L5.u64_at. rewrite Z_to_bv_bv_unsigned. exact (fun X => X). Qed.
(* [comment removed for export] *)
Lemma ret_rok fx R M (pc : Z) (W : bv 32) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  Hoare.ret_ok (getr R (reg 1)) ->
  msteps RSEGS (st fx R pc M) (st fx R (bv_unsigned (getr R (reg 1))) M).
Proof.
  intros HF HEC HD RO. rewrite Z_to_bv_bv_unsigned. eapply mst_step; [reflexivity | | apply mst_refl].
  assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
  rewrite (step_jalr_x0 RSEGS R _ M (seg_rom RSEGS) _ (reg 1) (0%bv : bv 12) (getr R (reg 1)) HF HEC D eq_refl).
  change (bv_signed (0%bv : bv 12)) with 0. unfold Hoare.ret_ok in RO. rewrite RO. reflexivity.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis FCTR : HAJ.rt_frame_ctr L ar HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma apiece_ctr LB FF LK cr A M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (W : Z -> Prop) K :
  ri_inv HI LB FF LK cr A M (vml_of model) -> L5CA.amodel_ok A model ->
  msteps RSEGS (st fx R pc (mrestrict (ahid A model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid A model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1v (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> W a -> ~ (hl_tp L + 16 <= a < hl_tp L + 20) -> aclientw L ar LB FF 0 0 a /\ ~ hl_rt_ro L a) ->
  L5.u32_at RSEGS M1v (hl_tp L + 16) 0 ->
  (forall M1 model1,
      ri_inv HI LB FF LK cr A M1 (vml_of model1) -> L5CA.amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      mrestrict (ahid A model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a : word, ahid A model a = false -> M1 a = M1v a) ->
      srealizes RSEGS SCFG (L5A.cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (L5A.cfg (fx:=fx) R pc M model) K.
Proof.
  intros HH [Hh MI] MS MG FZ WC CT KONT.
  pose proof (HAJ.aior_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr A M model HH) as (HOFF & _ & VIMG & _).
  set (H := ahid A model) in *.
  unfold L5A.cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF L5A.wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
  intros model1 MI1 SBM1 HC1.
  set (M1 := munrestrict H M M1v).
  assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
  assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
  assert (MGM1 : mem_grows M M1).
  { intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
  assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
  pose proof (PMA.ly_tp L C LY) as TP. cbn [pa_tp PMA.AD ADDR_A] in TP.
  apply (KONT M1 model1).
  - rewrite VML. apply (FCTR LB FF LK cr A M M1 _ HH).
    + intros a Ha Hp Hc. apply FRM1. exact Ha. intros CW. destruct (WC a Ha CW Hc) as [C1 C2]. destruct Hp as [Hp|[Hp|Hp]].
      * exact (Hp (aclientw_client _ _ _ _ _ _ _ C1)). * exact (C2 Hp).
      * exact (L5SAR.aclientw_not_bshadow L ar C HI LYa HIok LB FF LK cr A M _ 0 0 a HH C1 Hp).
    + rewrite (L5A.aly_segs L C LYa). rewrite TP in *. change (L5.u32_at RSEGS M1 (6765824 + 16) 0).
      apply (proj1 (L5A.u32_at_vis H M1 (6765824 + 16) 0 (VIMG (6765824 + 16) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      rewrite M1vis. exact CT.
    + exact MGM1.
  - split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
  - apply L5LZ.sbm_model_rt. exact SBM1.
  - apply L5LZ.sbm_ahid. exact SBM1.
  - exact M1vis.
  - exact MGM1.
  - exact FRM1.
  - intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ctr_not_client LB FF LK cr A M V sp scr x :
  ri_inv HI LB FF LK cr A M V -> 0x7fff80000000 <= ar_sptop ar -> 0x673d10 <= x < 0x673d14 -> ~ aclient L ar LB FF sp scr x.
Proof.
  intros HH SPT Hx Hc. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (L5A.aly_img_lo L C LYa) as IL. pose proof (L5A.aly_img_hi L C LYa) as IH.
  pose proof (PMA.ly_tp L C LY) as TP. cbn [pa_tp PMA.AD ADDR_A] in TP.
  unfold app_mem, FS_BYTES in *.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (_ & Y & _). lia.
  - lia.
  - apply (proj2 Hc). apply (PMA.ly_ctr_static L C LY). lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y2 & _). lia.
  - unfold in_shadow_of, S, SB in Hc. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. lia.
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _). unfold in_shadow_of, S, SB in X. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma cells_snoc M X f0 a0 f1 a1 atc hs f a :     (* [comment removed for export] *)
  L5.u8_at RSEGS M X 0 -> L5.u32_at RSEGS M (X + 4) 0 -> L5.u32_at RSEGS M (X + 8) (4 + 2 * Z.of_nat (length hs)) ->
  L5.u64_at RSEGS M (X + 16) (X + 24) -> L5.u64_at RSEGS M (X + 24) 0 -> L5.u64_at RSEGS M (X + 32) f0 -> L5.u64_at RSEGS M (X + 288) a0 ->
  L5.u64_at RSEGS M (X + 40) f1 -> L5.u64_at RSEGS M (X + 296) a1 ->
  (forall (i : nat) fi ai, nth_error hs i = Some (fi, ai) ->
      L5.u64_at RSEGS M (X + 48 + 16 * Z.of_nat i) fi /\ L5.u64_at RSEGS M (X + 56 + 16 * Z.of_nat i) atc
      /\ L5.u64_at RSEGS M (X + 304 + 16 * Z.of_nat i) ai /\ L5.u64_at RSEGS M (X + 312 + 16 * Z.of_nat i) 0) ->
  (L5.u64_at RSEGS M (X + 48 + 16 * Z.of_nat (length hs)) f /\ L5.u64_at RSEGS M (X + 56 + 16 * Z.of_nat (length hs)) atc
   /\ L5.u64_at RSEGS M (X + 304 + 16 * Z.of_nat (length hs)) a /\ L5.u64_at RSEGS M (X + 312 + 16 * Z.of_nat (length hs)) 0) ->
  HAJ.atexit_cells RSEGS M X f0 a0 f1 a1 atc (hs ++ [(f, a)]).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 OLD NEW. unfold HAJ.atexit_cells.
  split; [exact H1|]. split; [exact H2|]. split; [rewrite length_app; cbn [length]; replace (2 + 2 * Z.of_nat (length hs + 1)) with (4 + 2 * Z.of_nat (length hs)) by lia; exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  intros i fi ai Hi. destruct (Nat.lt_ge_cases i (length hs)) as [LT|GE].
  - rewrite nth_error_app1 in Hi by exact LT. exact (OLD i fi ai Hi).
  - rewrite nth_error_app2 in Hi by exact GE.
    destruct (i - length hs)%nat as [|r] eqn:E; cbn in Hi; [| destruct r; discriminate Hi].
    injection Hi as <- <-. replace i with (length hs) by lia. exact NEW.
Qed.

Theorem cxa_atexit_ok : HAJ.cxa_atexit_spec L ar SCFG HI (HAJ.ec_cxa_pc PMA.EXT) (HAJ.ec_cxa_scr PMA.EXT) (HAJ.ec_atexit PMA.EXT)
                          (HAJ.ec_f0 PMA.EXT) (HAJ.ec_a0 PMA.EXT) (HAJ.ec_f1 PMA.EXT) (HAJ.ec_a1 PMA.EXT) (HAJ.ec_atc PMA.EXT) (HAJ.ec_nl PMA.EXT).
Proof.
  unfold HAJ.cxa_atexit_spec.
  cbn [PMA.EXT HAJ.ec_cxa_pc HAJ.ec_cxa_scr HAJ.ec_atexit HAJ.ec_f0 HAJ.ec_a0 HAJ.ec_atc HAJ.ec_nl
       paa_cxa_atexit_icpt paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PMA.AAD AADDR_A pa_atexit pa_need_locks PMA.AD ADDR_A].
  cbv zeta.
  intros fx R M model LB FF LK cr Aw K hs f a d HH Mh MI A10 A11 A12 HLEN ATX NL Rtp RET ASO K0 KONT.
  rewrite (L5A.aly_segs L C LYa) in *.
  pose proof (PMA.ly_tp L C LY) as TP. cbn [pa_tp PMA.AD ADDR_A] in TP.
  set (sp := bv_unsigned (getr R 2%bv)) in *.
  assert (Rsp : getr R (reg 2) = Z_to_bv 64 sp) by (unfold sp; rewrite L5K.rl2, Z_to_bv_bv_unsigned; reflexivity).
  assert (Hsp : 0 <= sp < 2 ^ 64) by (unfold sp; pose proof (bv_unsigned_in_range 64 (getr R 2%bv)) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
  destruct ASO as (S16 & SLO & SHI & SPT & SST & SUP). rewrite (L5A.aly_segs L C LYa) in SST.
  rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12. rewrite L5K.rl4, TP in Rtp. rewrite L5K.rl1 in RET.
  set (f' := bv_unsigned (getr R (reg 10))). set (a' := bv_unsigned (getr R (reg 11))). set (d' := bv_unsigned (getr R (reg 12))).
  assert (R10 : getr R (reg 10) = Z_to_bv 64 f') by (unfold f'; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (R11 : getr R (reg 11) = Z_to_bv 64 a') by (unfold a'; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (R12 : getr R (reg 12) = Z_to_bv 64 d') by (unfold d'; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hf : 0 <= f' < 2 ^ 64) by (unfold f'; pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
  assert (Ha : 0 <= a' < 2 ^ 64) by (unfold a'; pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
  assert (Hd : 0 <= d' < 2 ^ 64) by (unfold d'; pose proof (bv_unsigned_in_range 64 (getr R (reg 12))) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  destruct ST as (_ & CS). rewrite Forall_forall in CS.
  assert (CINIT : L5.u8_at RSEGS M 0x140918 1).
  { exact (CS (0x140918, 1, 1) (L5A.aly_cells L C LYa _ ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 14 right; left; reflexivity))). }
  destruct (PMA.ly_cxa_cells L C LY) as (IR & IC).
  assert (CREAL : L5.u64_at RSEGS M 0x139470 0x118698) by exact (CS _ IR).
  assert (CCTR : L5.u32_at RSEGS M 0x673d10 0) by exact (CS _ IC).
  destruct ATX as (AF & ALK & ASL & AHD & ANX & AF0 & AA0 & AF1 & AA1 & AHS).
  (* [comment removed for export] *)
  assert (VU8 : forall x v0, 0x10000 <= x < 0x696000 -> L5.u8_at RSEGS M x v0 -> L5.u8_at RSEGS MV x v0).
  { intros x v0 Hx X. apply (proj2 (L5A.u8_at_vis H M x v0 (VIMG x 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (VU32 : forall x v0, 0x10000 <= x -> x + 4 <= 0x696000 -> L5.u32_at RSEGS M x v0 -> L5.u32_at RSEGS MV x v0).
  { intros x v0 Hx Hx' X. apply (proj2 (L5A.u32_at_vis H M x v0 (VIMG x 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (VU64 : forall x v0, 0x10000 <= x -> x + 8 <= 0x696000 -> L5.u64_at RSEGS M x v0 -> L5.u64_at RSEGS MV x v0).
  { intros x v0 Hx Hx' X. apply (proj2 (L5A.u64_at_vis H M x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply VU64; [lia| lia| exact CSB]).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply VU32; [lia| lia| exact CUAR]).
  assert (V3 : L5.writable RSEGS MV (sp - 1024) 1024).
  { apply (proj2 (L5A.writable_vis H M (sp - 1024) 1024 (VIS (sp - 1024) 1024 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    intros dd k Hdd Hkk. apply SST; lia. }
  assert (V4 : L5.u32_at RSEGS MV 6765840 0) by (apply VU32; [lia| lia| exact CCTR]).
  assert (V5 : L5.writable RSEGS MV 6765840 4) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
  assert (V6 : L5.u8_at RSEGS MV 1313048 1) by (apply VU8; [lia| exact CINIT]).
  assert (V7 : L5.u64_at RSEGS MV 1283184 1148568) by (apply VU64; [lia| lia| exact CREAL]).
  assert (V8 : L5.u8_at RSEGS MV 6896976 0) by (apply VU8; [lia| exact AF]).
  assert (V9 : L5.u32_at RSEGS MV 6896980 0) by (apply VU32; [lia| lia| exact ALK]).
  assert (V11 : L5.u64_at RSEGS MV 6896992 6897000) by (apply VU64; [lia| lia| exact AHD]).
  assert (V12 : L5.writable RSEGS MV 6896976 544) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
  assert (V13 : L5.u8_at RSEGS MV 6897555 0) by (apply VU8; [lia| exact NL]).
  destruct hs as [|p1 [|p2 [|p3 hs3]]]; [| | | exfalso; cbn in HLEN; lia].
  (* [comment removed for export] *)
  { assert (V10 : L5.u32_at RSEGS MV 6896984 2) by (apply VU32; [lia| lia| exact ASL]).
    LeanFeed.pfeed P (PMACXP.acxA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => f' | 34%nat => a' | 35%nat => 0 | 36%nat => d' | _ => 0 end)) ltac:(first [assumption | unfold PMACXP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & R1a0 & R1a1 & R1a2 & R1a3 & CT1 & SL1 & A21 & F21 & A11' & F11).
    assert (R1ra : getr R1 (reg 1) = getr R (reg 1)) by (apply KS1; inl).
    rewrite <- R1ra in RET.
    pose proof (ret_rok fx1 R1 M1v 0x6da98 W_6d680 F_6d680 eq_refl D_6d680 RET) as MS2. rewrite R1ra in MS2.
    set (WX := fun x => (sp - 1024 <= x < sp - 1024 + 1024) \/ (0 + 6765840 <= x < 0 + 6765840 + 4) \/ (0 + 6896984 <= x < 0 + 6896984 + 4)
                        \/ (0 + 6897024 <= x < 0 + 6897024 + 16) \/ (0 + 6897280 <= x < 0 + 6897280 + 16)).
    change (srealizes RSEGS SCFG (L5A.cfg (fx:=fx) R 0x6da18 M model) K).
    apply (apiece_ctr LB FF LK cr Aw M model fx fx1 R 0x6da18 R1 (bv_unsigned (getr R (reg 1))) M1v WX K HH (conj Mh MI)).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros x Hx N. unfold WX in N. apply FRZ1; [exact Hx| | | | |]; intros X; apply N; tauto. }
    { intros x Hx Wx Nc. rewrite TP in Nc. unfold WX in Wx. destruct Wx as [Wx|[Wx|Wx]].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY x X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - exfalso. lia.
      - split; [|apply (PMKA2.rt_ro_bss L C x LY); lia]. unfold aclientw, aclient_g. right; right; left.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
        intros [X|X].
        + apply (fun D_ => PMA.ly_static L C LY x (PnStatics.PNST.dep_of_j _ _ x D_)); [|exact X]. apply PMST.in_foot_atexit. cbn [pa_atexit PMA.AD ADDR_A]. lia.
        + pose proof (PMA.ly_ro L C LY x X). lia. }
    { rewrite TP. exact CT1. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (FR1' : forall x, 6896976 <= x < 6896976 + 544 -> ~ WX x -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx N; apply FR1; [lia| exact N]).
    assert (W1 : forall x v0, 6896976 <= x -> x + 8 <= 6896976 + 544 -> L5.u64_at RSEGS M1v x v0 -> L5.u64_at RSEGS M1 x v0).
    { intros x v0 Hx Hx' X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    unfold L5A.cfg. rewrite Z_to_bv_bv_unsigned. rewrite <- L5K.rl1.
    pose proof AM1 as (Mh1 & MI1).
    apply (KONT fx1 R1 M1 model1 Aw).
    - apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    - rewrite L5K.rl10. exact R1a0.
    - apply cells_snoc.
      + apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF].
      + apply (PMF.u32_at_agree RSEGS M M1); [intros j Hj; apply FR1'; [lia| unfold WX; lia]| lia| lia| exact ALK].
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
        rewrite <- VIS1 in SL1. exact (proj1 (L5A.u32_at_vis H M1 6896984 4 (VIMG 6896984 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) SL1).
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AHD].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact ANX].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF0].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA0].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF1].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA1].
      + intros i fi ai Hi. destruct i; cbn in Hi; [discriminate Hi| destruct i; discriminate Hi].
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
        split; [apply u64_norm; rewrite <- A10; apply (W1 6897024); [lia| lia| exact F11]|].
        split; [apply (W1 6897032); [lia| lia| exact F21]|].
        split; [apply u64_norm; rewrite <- A11; apply (W1 6897280); [lia| lia| exact A11']|].
        apply (W1 6897288); [lia| lia| exact A21].
    - intros x Hx Hc Hn. apply FR1; [exact Hx|]. unfold WX. intros [X|[X|X]].
      + destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 1024 x HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      + exact (ctr_not_client LB FF LK cr Aw M (vml_of model) sp 1024 x HH ltac:(lia) ltac:(lia) Hc).
      + apply Hn. lia.
    - intros x Hx HM. apply MGM1. exact HM.
    - intros x Hx. apply MGM1. replace x with (sp - 1024 + (x - (sp - 1024))) by lia.
      apply store_ok_defined; [lia|]. apply SST; lia.
    - exact MRT1.
    - intros x Hx. exact Hx.
    - exact MI1.
    - exact HH1.
  }
  (* [comment removed for export] *)
  { assert (V10 : L5.u32_at RSEGS MV 6896984 4) by (apply VU32; [lia| lia| exact ASL]).
    LeanFeed.pfeed P (PMACXP.acxA3_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => f' | 34%nat => a' | 35%nat => 0 | 36%nat => d' | _ => 0 end)) ltac:(first [assumption | unfold PMACXP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & R1a0 & R1a1 & R1a2 & R1a3 & CT1 & SL1 & A21 & F21 & A11' & F11).
    assert (R1ra : getr R1 (reg 1) = getr R (reg 1)) by (apply KS1; inl).
    rewrite <- R1ra in RET.
    pose proof (ret_rok fx1 R1 M1v 0x6da98 W_6d680 F_6d680 eq_refl D_6d680 RET) as MS2. rewrite R1ra in MS2.
    set (WX := fun x => (sp - 1024 <= x < sp - 1024 + 1024) \/ (0 + 6765840 <= x < 0 + 6765840 + 4) \/ (0 + 6896984 <= x < 0 + 6896984 + 4)
                        \/ (0 + 6897040 <= x < 0 + 6897040 + 16) \/ (0 + 6897296 <= x < 0 + 6897296 + 16)).
    change (srealizes RSEGS SCFG (L5A.cfg (fx:=fx) R 0x6da18 M model) K).
    apply (apiece_ctr LB FF LK cr Aw M model fx fx1 R 0x6da18 R1 (bv_unsigned (getr R (reg 1))) M1v WX K HH (conj Mh MI)).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros x Hx N. unfold WX in N. apply FRZ1; [exact Hx| | | | |]; intros X; apply N; tauto. }
    { intros x Hx Wx Nc. rewrite TP in Nc. unfold WX in Wx. destruct Wx as [Wx|[Wx|Wx]].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY x X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - exfalso. lia.
      - split; [|apply (PMKA2.rt_ro_bss L C x LY); lia]. unfold aclientw, aclient_g. right; right; left.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
        intros [X|X].
        + apply (fun D_ => PMA.ly_static L C LY x (PnStatics.PNST.dep_of_j _ _ x D_)); [|exact X]. apply PMST.in_foot_atexit. cbn [pa_atexit PMA.AD ADDR_A]. lia.
        + pose proof (PMA.ly_ro L C LY x X). lia. }
    { rewrite TP. exact CT1. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (FR1' : forall x, 6896976 <= x < 6896976 + 544 -> ~ WX x -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx N; apply FR1; [lia| exact N]).
    assert (W1 : forall x v0, 6896976 <= x -> x + 8 <= 6896976 + 544 -> L5.u64_at RSEGS M1v x v0 -> L5.u64_at RSEGS M1 x v0).
    { intros x v0 Hx Hx' X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    unfold L5A.cfg. rewrite Z_to_bv_bv_unsigned. rewrite <- L5K.rl1.
    pose proof AM1 as (Mh1 & MI1).
    apply (KONT fx1 R1 M1 model1 Aw).
    - apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    - rewrite L5K.rl10. exact R1a0.
    - apply cells_snoc.
      + apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF].
      + apply (PMF.u32_at_agree RSEGS M M1); [intros j Hj; apply FR1'; [lia| unfold WX; lia]| lia| lia| exact ALK].
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
        rewrite <- VIS1 in SL1. exact (proj1 (L5A.u32_at_vis H M1 6896984 6 (VIMG 6896984 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) SL1).
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AHD].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact ANX].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF0].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA0].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF1].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA1].
      + intros i fi ai Hi. pose proof (AHS i fi ai Hi) as (P1 & P2 & P3 & P4).
        assert (Hik : (i < 1)%nat) by (lazymatch type of Hi with nth_error ?l _ = _ => apply (proj1 (nth_error_Some l i)) end; rewrite Hi; discriminate).
        assert (Zi : 0 <= Z.of_nat i <= 0) by lia.
        repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [intros j Hj; apply FR1'; [lia| unfold WX; lia] | lia | lia | assumption]).
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
        split; [apply u64_norm; rewrite <- A10; apply (W1 6897040); [lia| lia| exact F11]|].
        split; [apply (W1 6897048); [lia| lia| exact F21]|].
        split; [apply u64_norm; rewrite <- A11; apply (W1 6897296); [lia| lia| exact A11']|].
        apply (W1 6897304); [lia| lia| exact A21].
    - intros x Hx Hc Hn. apply FR1; [exact Hx|]. unfold WX. intros [X|[X|X]].
      + destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 1024 x HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      + exact (ctr_not_client LB FF LK cr Aw M (vml_of model) sp 1024 x HH ltac:(lia) ltac:(lia) Hc).
      + apply Hn. lia.
    - intros x Hx HM. apply MGM1. exact HM.
    - intros x Hx. apply MGM1. replace x with (sp - 1024 + (x - (sp - 1024))) by lia.
      apply store_ok_defined; [lia|]. apply SST; lia.
    - exact MRT1.
    - intros x Hx. exact Hx.
    - exact MI1.
    - exact HH1.
  }
  (* [comment removed for export] *)
  { assert (V10 : L5.u32_at RSEGS MV 6896984 6) by (apply VU32; [lia| lia| exact ASL]).
    LeanFeed.pfeed P (PMACXP.acxA5_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => f' | 34%nat => a' | 35%nat => 0 | 36%nat => d' | _ => 0 end)) ltac:(first [assumption | unfold PMACXP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & R1a0 & R1a1 & R1a2 & R1a3 & CT1 & SL1 & A21 & F21 & A11' & F11).
    assert (R1ra : getr R1 (reg 1) = getr R (reg 1)) by (apply KS1; inl).
    rewrite <- R1ra in RET.
    pose proof (ret_rok fx1 R1 M1v 0x6da98 W_6d680 F_6d680 eq_refl D_6d680 RET) as MS2. rewrite R1ra in MS2.
    set (WX := fun x => (sp - 1024 <= x < sp - 1024 + 1024) \/ (0 + 6765840 <= x < 0 + 6765840 + 4) \/ (0 + 6896984 <= x < 0 + 6896984 + 4)
                        \/ (0 + 6897056 <= x < 0 + 6897056 + 16) \/ (0 + 6897312 <= x < 0 + 6897312 + 16)).
    change (srealizes RSEGS SCFG (L5A.cfg (fx:=fx) R 0x6da18 M model) K).
    apply (apiece_ctr LB FF LK cr Aw M model fx fx1 R 0x6da18 R1 (bv_unsigned (getr R (reg 1))) M1v WX K HH (conj Mh MI)).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros x Hx N. unfold WX in N. apply FRZ1; [exact Hx| | | | |]; intros X; apply N; tauto. }
    { intros x Hx Wx Nc. rewrite TP in Nc. unfold WX in Wx. destruct Wx as [Wx|[Wx|Wx]].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY x X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - exfalso. lia.
      - split; [|apply (PMKA2.rt_ro_bss L C x LY); lia]. unfold aclientw, aclient_g. right; right; left.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
        intros [X|X].
        + apply (fun D_ => PMA.ly_static L C LY x (PnStatics.PNST.dep_of_j _ _ x D_)); [|exact X]. apply PMST.in_foot_atexit. cbn [pa_atexit PMA.AD ADDR_A]. lia.
        + pose proof (PMA.ly_ro L C LY x X). lia. }
    { rewrite TP. exact CT1. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (FR1' : forall x, 6896976 <= x < 6896976 + 544 -> ~ WX x -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx N; apply FR1; [lia| exact N]).
    assert (W1 : forall x v0, 6896976 <= x -> x + 8 <= 6896976 + 544 -> L5.u64_at RSEGS M1v x v0 -> L5.u64_at RSEGS M1 x v0).
    { intros x v0 Hx Hx' X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    unfold L5A.cfg. rewrite Z_to_bv_bv_unsigned. rewrite <- L5K.rl1.
    pose proof AM1 as (Mh1 & MI1).
    apply (KONT fx1 R1 M1 model1 Aw).
    - apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    - rewrite L5K.rl10. exact R1a0.
    - apply cells_snoc.
      + apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF].
      + apply (PMF.u32_at_agree RSEGS M M1); [intros j Hj; apply FR1'; [lia| unfold WX; lia]| lia| lia| exact ALK].
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
        rewrite <- VIS1 in SL1. exact (proj1 (L5A.u32_at_vis H M1 6896984 8 (VIMG 6896984 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) SL1).
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AHD].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact ANX].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF0].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA0].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF1].
      + apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA1].
      + intros i fi ai Hi. pose proof (AHS i fi ai Hi) as (P1 & P2 & P3 & P4).
        assert (Hik : (i < 2)%nat) by (lazymatch type of Hi with nth_error ?l _ = _ => apply (proj1 (nth_error_Some l i)) end; rewrite Hi; discriminate).
        assert (Zi : 0 <= Z.of_nat i <= 1) by lia.
        repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [intros j Hj; apply FR1'; [lia| unfold WX; lia] | lia | lia | assumption]).
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
        split; [apply u64_norm; rewrite <- A10; apply (W1 6897056); [lia| lia| exact F11]|].
        split; [apply (W1 6897064); [lia| lia| exact F21]|].
        split; [apply u64_norm; rewrite <- A11; apply (W1 6897312); [lia| lia| exact A11']|].
        apply (W1 6897320); [lia| lia| exact A21].
    - intros x Hx Hc Hn. apply FR1; [exact Hx|]. unfold WX. intros [X|[X|X]].
      + destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 1024 x HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      + exact (ctr_not_client LB FF LK cr Aw M (vml_of model) sp 1024 x HH ltac:(lia) ltac:(lia) Hc).
      + apply Hn. lia.
    - intros x Hx HM. apply MGM1. exact HM.
    - intros x Hx. apply MGM1. replace x with (sp - 1024 + (x - (sp - 1024))) by lia.
      apply store_ok_defined; [lia|]. apply SST; lia.
    - exact MRT1.
    - intros x Hx. exact Hx.
    - exact MI1.
    - exact HH1.
  }
Qed.
End WithHeap.

End PMACXA.
