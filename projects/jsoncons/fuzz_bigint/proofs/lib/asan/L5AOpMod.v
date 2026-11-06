(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5ADetailK L5AFrameK L5DivKitA L5DivSpecsA L5OpmodSpecsA L5DivLeafSpecsA L5DivInnerSpecsA L5ParseSpecsA L5UnwindSpecsA L5ATopX L5ADivEA L5ADivO1 L5AOpModP L5AOpModH.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require As0_code_91368_92368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AOPMOD.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5AOPMODP. Import L5AOMH.
(* [comment removed for export] *)
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Lemma DEL_EQ : OPDEL_SCR = 4096. Proof. reflexivity. Qed.
Lemma DIVN_EQ : L5DIA.DIVN_SCR = 5008. Proof. reflexivity. Qed.
Lemma DIVEQ_EQ : L5DIA.DIVEQ_SCR = 5104. Proof. reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.

Section DQ.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl r X dv : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 96).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 96 + 5520 <= SCRD.
Hypothesis XR : 0 <= X < 2 ^ 64.
Hypothesis DVR : 0 <= dv < 2 ^ 64.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1).
Local Notation FF' := ((F, 1, SPA + 32) :: FF).
Local Notation Gx := (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G).
Local Notation SH := (F / 8 + 2147450880).

Lemma NUM : (0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= E < 2 ^ 64) /\ 4096 <= F <= 140737488355200 /\ 4096 <= fl <= 140737488355327 /\ aligned F 32
  /\ (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784) /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 128 <= fl \/ fl + 1 <= F) /\ (E - 96 + 96 <= F \/ F + 128 <= E - 96) /\ (E - 96 + 96 <= fl \/ fl + 1 <= E - 96)
  /\ (F + 128 <= E - 96 /\ fl + 1 <= E - 96).
Proof.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 1) with 128 in *.
  split. clear - FR FLR ER; lia. split. clear - FR; lia. split. clear - FLR; lia. split. exact F32. split. exact FBIG. split. exact FLBIG. split. exact FLA.
  assert (SFB : F + 128 <= E - 96 /\ fl + 1 <= E - 96) by (clear - FCEIL FLR SPC SLO; lia).
  split. clear - SFB; lia. split. clear - SFB; lia. exact SFB.
Qed.

(* [comment removed for export] *)
Definition pfq (MV : word -> option byte) : Prop :=
  L5.writable RSEGS MV (E - 96) 96 /\ L5.img_clear MV 860160 880640 /\ L5.u64_at RSEGS MV 908088 2147450880 /\ L5.u32_at RSEGS MV 908096 1 /\
  L5.defined MV F 128 /\ L5.writable RSEGS MV F 128 /\ L5.writable RSEGS MV (F / 8 + SB) 16 /\ L5.u64_at RSEGS MV (F + 120) fl /\ L5.writable RSEGS MV fl 1.
Lemma pfq_of_binv W BX Mc modelc LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> pfq (mrestrict (ahid Ac modelc) Mc).
Proof.
  intros BI.
  destruct (Gx W BX Mc modelc LKc crc Ac BI) as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & _).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. replace (F + 128 - 8) with (F + 120) in FLCv by (clear; lia).
  unfold pfq. split. { eapply L5.writable_sub. exact WSv. clear; lia. clear; lia. }
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dq_memset (fx : FPState) Rc Mc modelc W BX LKc crc Ac :
  binv W BX Mc modelc LKc crc Ac -> rinvQ R E F X dv Rc -> getr Rc (reg 1) = Z_to_bv 64 0x91f18 ->
  getr Rc (reg 10) = Z_to_bv 64 (F + 40) /\ getr Rc (reg 11) = Z_to_bv 64 0 /\ getr Rc (reg 12) = Z_to_bv 64 24 ->
  qsh Mc F 0 -> shadow_zero Mc (F + 32) 4 -> L5.u8_at RSEGS Mc (F + 32) 0 -> L5.u64_at RSEGS Mc F 1102416563 ->
  (forall (fx6 : FPState) R6 M6 model6,
      binv W BX M6 model6 LKc crc Ac -> rinvQ R E F X dv R6 ->
      qsh M6 F 0 -> L5DIA.zero_obj M6 (F + 32) -> shadow_zero M6 (F + 32) 4 -> L5.u64_at RSEGS M6 F 1102416563 ->
      srealizes RSEGS SCFG (cfg (fx:=fx6) R6 0x91f18 M6 model6) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc AMEMSET Mc modelc) K.
Proof.
  intros BI RI X1 (X10 & X11 & X12) QSH VZ1 T0F1 HD1 KF.
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (Y2 & Y8 & Y9 & Y3 & Y4 & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 1) with 128 in *.
  pose proof BI as (C1 & C2 & _ & _ & _ & C6 & _).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH4 : (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0 /\ 0 <= F / 8 /\ F / 8 + 16 <= 17592186044416 /\ F / 8 * 8 = F) by (clear - FRP ALF; unfold aligned in ALF; lia).
  assert (SA16 : (E - 96) mod 16 = 0). { clear - EA. unfold aligned in EA. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
  assert (U25 : bv_unsigned (getr Rc 2%bv) = SPA). { rewrite r2, Y2. apply L5.unsigned_lit. clear - ER; lia. }
  eapply (MS fx Rc Mc modelc (BX ++ LB) FF' LKc crc Ac (F + 40) 0 24 K); clear MS.
  { split. exact C1. split. exact (proj1 C2). split. exact (proj2 C2).
    split. rewrite r10. exact X10. split. rewrite r12. exact X12. split. clear; lia.
    split. rewrite r4, Y4. exact G4. split. rewrite r1, X1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    split. { rewrite U25. apply (astack_ok_of_astk L ar C LY Mc Mc E SCRD 96 2560 C6 (mem_grows_refl Mc)). clear; lia. clear; lia. clear - HSCR; lia. exact SA16. }
    split. { eapply aacc_of_zero. exact VZ1. exact (proj1 (proj2 FSH4)). clear - FR; lia. clear; lia. clear; lia. }
    split. { intros i Hi. rewrite U25. apply (fframe_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Hi; lia. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS Mc (F + 40) 24). 2: clear - FR; lia. 2: clear - FR; lia. 2: exact Hi. 2: exact Hm.
             pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ C1) as (_ & WF1 & _).
             pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WF1 _ (or_introl eq_refl))))))) as FD. cbn [ff_addr ff_class fst snd] in FD. change (ff_bytes 1) with 128 in FD.
             intros j Hj. replace (F + 40 + j) with (F + (40 + j)) by (clear; lia). apply FD. clear - Hj; lia. }
    split. exact HK. apply (app_rng_fs L ar C HI HIok _ _ _ _ _ _ _ (F + 40) 24 C1). clear - FS1; lia. clear - FS2; lia. }
  { rewrite r11. exact X11. }
  intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U25 in PRES6, SDEF6. rewrite r1, X1.
  assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 C2). }
  assert (BI6 : binv W BX M6 model6 LKc crc Ac).
  { apply (L5AFK.binv_mem L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G
             W BX Mc modelc LKc crc Ac M6 model6 (fun a => F + 40 <= a < F + 40 + 24) 2560 BI HH6 (conj Hh6 MI6) RT6 PRES6).
    - intros a Ha. apply SDEF6. clear - Ha; lia.
    - intros a Da. destruct (ZB (a - (F + 40)) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (F + 40 + (a - (F + 40))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    - intros a. destruct (rng_dec a (F + 40) (F + 40 + 24)); [left|right]; assumption.
    - intros a Da. change (ff_bytes 1) with 128. clear - Da; lia.
    - clear - HSCR; lia.
    - clear; lia. }
  assert (FCL6 : forall a, F <= a < F + 120 -> ~ (F + 24 <= a < F + 32) -> aclient L ar (BX ++ LB) FF' SPA 2560 a).
  { intros a Ha Hn. apply (fframe_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ha Hn; lia. }
  assert (SCL6 : forall a, SH <= a < SH + 16 -> aclient L ar (BX ++ LB) FF' SPA 2560 a).
  { intros a Ha. apply (fframe_shadow_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S, SB.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Ha FSH4. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VU6 : L5.u8_at RSEGS M6 (F + 32) 0).
  { eapply L5C.u8_at_agree. 4: exact T0F1. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply PRES6. clear - Hi FR; lia. apply FCL6. clear - Hi; lia. clear - Hi; lia. clear - Hi; lia. }
  assert (HD6 : L5.u64_at RSEGS M6 F 1102416563).
  { eapply L5C.u64_at_agree. 4: exact HD1. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply PRES6. clear - Hi FR; lia. apply FCL6. clear - Hi; lia. clear - Hi; lia. clear - Hi; lia. }
  assert (Z6 : L5KA.zeros_at M6 (F + 40) 24). { intros i Hi. destruct (ZB i Hi) as (v & Ev & Bv). subst v. exact Bv. }
  assert (VBIG6 : L5.big_at RSEGS M6 (F + 32) (L5.BO 0 0 (L5.BInl 0 0))).
  { apply L5ADK.big_at_zero. exact VU6.
    - replace (F + 32 + 8) with (F + 40) by (clear; lia). apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia.
    - replace (F + 32 + 16) with (F + 48) by (clear; lia). apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia.
    - replace (F + 32 + 24) with (F + 56) by (clear; lia). apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia. }
  assert (SHK6 : forall a, SH <= a < SH + 16 -> M6 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha. apply PRES6. clear - Ha FSH4; lia. apply SCL6. exact Ha. clear - Ha FSH4 FBIG; lia. }
  assert (QSH6 : qsh M6 F 0).
  { destruct QSH as (Q0 & Q4 & Q8 & Q12). unfold qsh, shr8, SB in *.
    repeat split; intros j Hj; (eapply L5C.u8_at_agree; [ | | | first [exact (Q0 j Hj) | exact (Q4 j Hj) | exact (Q8 j Hj) | exact (Q12 j Hj)]]);
      [ intros i Hi; apply SHK6; clear - Hi Hj; lia | clear - Hj FSH4; lia | clear - Hj FSH4; lia
      | intros i Hi; apply SHK6; clear - Hi Hj; lia | clear - Hj FSH4; lia | clear - Hj FSH4; lia
      | intros i Hi; apply SHK6; clear - Hi Hj; lia | clear - Hj FSH4; lia | clear - Hj FSH4; lia
      | intros i Hi; apply SHK6; clear - Hi Hj; lia | clear - Hj FSH4; lia | clear - Hj FSH4; lia ]. }
  assert (VZ6 : shadow_zero M6 (F + 32) 4).
  { intros j Hj. unfold byte_at. unfold S, SB. rewrite (proj1 FSH4). rewrite SHK6 by (clear - Hj; lia).
    specialize (VZ1 j Hj). unfold byte_at, S, SB in VZ1. rewrite (proj1 FSH4) in VZ1. exact VZ1. }
  apply (KF fx R6 M6 model6 BI6 (rinvQ_pres R E F X dv Rc R6 RI RP6) QSH6 VBIG6 VZ6 HD6).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qobj_at (Mk : word -> option byte) (o : Z) (b : L5.bigobj) (blk : option (Z * Z)) : Prop :=
  L5.big_at RSEGS Mk o b /\ match L5.bo_st b with L5.BInl _ _ => blk = None | L5.BDyn cap q => blk = Some (q, 8 * cap) end.

Lemma dq_dtor (fx : FPState) Rc Mc modelc W BX BXn LKc crc Ac b blk :
  binv W BX Mc modelc LKc crc Ac -> rinvQ R E F X dv Rc -> qobj_at Mc (F + 32) b blk ->
  match blk with None => BXn = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BXn ++ LB end ->
  (forall (fx' : FPState) R' M' model' A',
      binv W BXn M' model' LKc crc A' -> rinvQ R E F X dv R' -> incl Ac A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXn ++ LB) FF' SPA OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x91f50 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x91f30 Mc modelc) K.
Proof.
  intros BI RI [OB OBLK] BLK KF.
  pose proof (pfq_of_binv W BX Mc modelc LKc crc Ac BI) as (W96 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  destruct (Gx W BX Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & FV & SV & _)).
  change (ff_bytes 1) with 128 in FV.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (Y2 & Y8 & Y9 & Y3 & Y4 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (OV : avis (ahid Ac modelc) (F + 32) 32). { eapply avis_sub. exact FV. clear; lia. clear; lia. }
  assert (CELLV : forall a v, F + 32 <= a -> a + 8 <= F + 32 + 32 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact OV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 FRP; lia) ltac:(clear - H2 FRP; lia))). exact Hc. }
  assert (CELL1 : forall v, L5.u8_at RSEGS Mc (F + 32) v -> L5.u8_at RSEGS MV (F + 32) v).
  { intros v Hc. apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 32) v ltac:(eapply avis_sub; [exact OV | clear; lia | clear; lia]) ltac:(clear - FRP; lia) ltac:(clear - FRP; lia))). exact Hc. }
  destruct b as [fb len sto]. destruct OB as (O0 & FBR & _ & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia).
  pose proof (CELL1 _ O0) as O0v.
  destruct sto as [v0 v1|cap q].
  - (* [comment removed for export] *)
    subst blk. subst BXn. destruct OST as (BT0 & _).
    pose proof (vomP3i_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pEQ & _ & (pMS & pKS & _)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pEQ). rewrite EQM in pMS.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x91f30 R1 0x91f50 K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 Mc model1 Ac BI1). 2: apply incl_refl. 2: intros a _ _; reflexivity.
    apply (rinvQ_ks R E F X dv Rc R1 KS_vomP3i RI pKS). vm_compute; reflexivity.
  - (* [comment removed for export] *)
    subst blk. destruct BLK as [INP ELB]. destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    pose proof (CELLV (F + 32 + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) as O24v. pose proof (CELLV (F + 32 + 16) cap ltac:(clear; lia) ltac:(clear; lia) O16) as O16v.
    replace (F + 32 + 24) with (F + 56) in O24v by (clear; lia). replace (F + 32 + 16) with (F + 48) in O16v by (clear; lia).
    assert (QR : 4096 <= q <= 140737488355328 /\ 0 <= q < 2 ^ 64 /\ 0 <= cap < 2 ^ 64) by (clear - Q4096 Q47 CAPR; lia). destruct QR as (QR & QRG & CAPG).
    pose proof (vomP3d_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pEQ & _ & (pMS & pKS & dR1 & dR10 & dR11)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pEQ). rewrite EQM in pMS.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x91f30 R1 OPDEL_SIZED K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    assert (RI1 : rinvQ R E F X dv R1). { apply (rinvQ_ks R E F X dv Rc R1 KS_vomP3d RI pKS). vm_compute; reflexivity. }
    pose proof RI1 as (Z2 & _ & _ & _ & Z4 & _).
    assert (SPA16 : (E - 96) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (Hdel fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac q (8 * cap) SPA 0x91f50 HH1 AM1 HK INP).
    + rewrite r10. exact dR10.
    + rewrite r1. exact dR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. exact Z2.
    + rewrite r4, Z4. rewrite <- G4. reflexivity.
    + apply (astk_sub ar Mc Mc E SCRD 96 OPDEL_SCR B6 (mem_grows_refl Mc)).
      clear; lia. rewrite DEL_EQ; clear; lia. rewrite DEL_EQ; clear - HSCR; lia. exact SPA16.
    + intros fx3 R3 M3 model3 A3 RP3 AH3 RT3 IA3 AM3 HH3. rewrite ELB in AH3, HH3.
      assert (BI3 : binv W BXn M3 model3 LKc crc A3).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G
                 W W BX BXn BXn Mc model1 LKc crc Ac M3 model3 LKc crc A3 OPDEL_SCR [] BI1 AH3 HH3 AM3 RT3 IA3 (incl_refl _)).
        - rewrite DEL_EQ; clear; lia.
        - rewrite DEL_EQ; clear - HSCR; lia.
        - intros rr a [].
        - intros a _ _ rr [].
        - intros a X0. exact X0. }
      apply (KF fx3 R3 M3 model3 A3 BI3 (rinvQ_pres R E F X dv R1 R3 RI1 RP3) IA3).
      intros a Ha Hc. apply (proj1 AH3). split. exact Ha. split. exact Hc. intros rr [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dq_tail_run (fx : FPState) Rc MV : rinvQ R E F X dv Rc -> pfq MV -> qown E F R MV ->
  exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc 0x91f50 MV) (st fx9 R9 r M9v) /\ mem_grows MV M9v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ L5AFK.Wret F fl 1 a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.u8_at RSEGS M9v fl 0 /\ regs_preserved R R9 /\ getr R9 (reg 10) = Z_to_bv 64 X.
Proof.
  intros RI (W96 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv) OWNv.
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (Y2 & Y8 & Y9 & Y3 & Y4 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  destruct OWNv as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  pose proof (vomP4_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 41%nat => fl
                | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 58%nat => U Rc 1 | _ => 0 end)) as P.
  cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eFL0 & _)).
  pose proof (ret_to fx9 R9 M9v 0x92020 As0_code_91368_92368.W_92020 r As0_code_91368_92368.F_92020 eq_refl As0_code_91368_92368.D_92020
                ltac:(rewrite eR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
  exists fx9, R9, M9v. split. { eapply msteps_trans. exact eMS. exact RET. }
  split. exact MG9.
  split. { intros a Ha Hw. unfold L5AFK.Wret in Hw. change (ff_bytes 1 / 8) with 16 in Hw. apply eFZ. exact Ha.
           - clear - Hw; unfold SB in Hw; lia.
           - clear - Hw; lia.
           - clear - Hw; lia. }
  split. exact eFL0.
  split. 2: exact eR10.
  apply preserved_by_index. intros j Hj. unfold cs_all in Hj. cbn [In] in Hj.
  destruct Hj as [<-|Hj]. { rewrite eR2. symmetry. exact G2. }
  destruct Hj as [<-|Hj]. { rewrite (eKS 3%nat) by inl. exact Y3. }
  destruct Hj as [<-|Hj]. { rewrite (eKS 4%nat) by inl. exact Y4. }
  repeat (destruct Hj as [<-|Hj]; [first [rewrite eR8 | rewrite eR9 | rewrite eR18 | rewrite eR19 | rewrite eR20 | rewrite eR21 | rewrite eR22 | rewrite eR23 | rewrite eR24
                                          | (rewrite (eKS 25%nat) by inl; exact Y25) | (rewrite (eKS 26%nat) by inl; exact Y26) | (rewrite (eKS 27%nat) by inl; exact Y27)];
                                   first [ (symmetry; apply U_to) | idtac ] |]). destruct Hj.
Qed.

Lemma dq_tail (fx : FPState) Rc Mc modelc W BX LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> rinvQ R E F X dv Rc ->
  (forall (fxf : FPState) Rf Mf modelf,
      regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 X ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ L5AFK.Wret F fl 1 a -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      ahpres L ar LB FF E SCRD W M Mf ->
      model_rt model modelf -> amodel_ok Ac modelf ->
      ri_inv HI (BX ++ LB) FF LKc crc Ac Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x91f50 Mc modelc) K.
Proof.
  intros BI RI KF.
  pose proof (pfq_of_binv W BX Mc modelc LKc crc Ac BI) as PF.
  destruct (Gx W BX Mc modelc LKc crc Ac BI) as (_ & OWNv & _).
  destruct (dq_tail_run fx Rc _ RI PF OWNv) as (fx9 & R9 & M9v & MS9 & MG9 & FZ9 & FL9 & RP9 & R10).
  apply (L5AFK.retire_core L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac fx fx9 Rc 0x91f50 R9 r M9v K BI MS9 MG9 FZ9 FL9).
  intros Mf modelf FRMf AHf RTf AMf HHf. apply (KF fx9 R9 Mf modelf RP9 R10 FRMf AHf RTf AMf HHf).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis FFR1 : ffrk 1 FF LK 6.
Hypothesis FFR3 : ffrk 3 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis HH0 : ri_inv HI LB FF LK cr2 A M (vml_of model).
Lemma r3q : (3%bv : bv 5) = reg 3. Proof. apply bv_eq. reflexivity. Qed.
Lemma r13q : (13%bv : bv 5) = reg 13. Proof. apply bv_eq. reflexivity. Qed.
Lemma r14q : (14%bv : bv 5) = reg 14. Proof. apply bv_eq. reflexivity. Qed.
Lemma r25q : (25%bv : bv 5) = reg 25. Proof. apply bv_eq. reflexivity. Qed.
Lemma apart_of_client (P : Z -> Prop) x lx y ly : 0 < lx -> 0 < ly -> (forall a, x <= a < x + lx -> P a) -> (forall a, y <= a < y + ly -> ~ P a) -> x + lx <= y \/ y + ly <= x.
Proof.
  intros Hx Hy PX PY. destruct (Z_le_gt_dec (x + lx) y) as [A1|A1]. left; exact A1. destruct (Z_le_gt_dec (y + ly) x) as [A2|A2]. right; exact A2.
  exfalso. apply (PY (Z.max x y)). Lia.lia. apply PX. Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma stksh_sub (Mk Mk' : word -> option byte) lo lo' : L5OMA.stksh ar Mk lo -> lo <= lo' -> lo mod 8 = 0 -> lo' mod 8 = 0 -> ahl_ceil ar <= lo -> 0 <= lo -> ar_stack_top ar <= 2 ^ 47 -> ar_sptop ar <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> Mk' (Z_to_bv 64 a) = Mk (Z_to_bv 64 a)) -> L5OMA.stksh ar Mk' lo'.
Proof.
  intros SSH LE L8 L8' CE L0 TOP SPT AG j Hj. unfold byte_at. unfold L5OMA.stksh, shadow_zero, byte_at in SSH.
  set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
  assert (MX : mx <= 2 ^ 47) by (subst mx; apply Z.max_lub; assumption).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Q : S lo' + j = S lo + ((lo' - lo) / 8 + j) /\ 0 <= (lo' - lo) / 8 + j < (mx - lo) / 8 /\ 0 <= S lo' + j < 2 ^ 64 /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) (S lo' + j)).
  { unfold in_shadow_of, S, SB. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415.
    clear - Hj LE L8 L8' CE L0 MX. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct Q as (Q1 & Q2 & Q3 & Q4). rewrite AG by assumption. rewrite Q1. apply SSH. exact Q2.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section O2.
Hypothesis HdivO2 : L5DIA.divO2_specA L ar HI.
Lemma om2_rest (fx : FPState) R3 M3 model3 fba (by_ : L5.bigobj) (wy : list Z) :
  binv [] [] M3 model3 LK2 cr2 A -> rinvQ R E F X dv R3 -> getr R3 (reg 1) = Z_to_bv 64 0x91f18 ->
  getr R3 (reg 10) = Z_to_bv 64 (F + 40) /\ getr R3 (reg 11) = Z_to_bv 64 0 /\ getr R3 (reg 12) = Z_to_bv 64 24 ->
  qsh M3 F 0 -> shadow_zero M3 (F + 32) 4 -> L5.u8_at RSEGS M3 (F + 32) 0 -> L5.u64_at RSEGS M3 F 1102416563 ->
  L5OMA.y_ok LB M X by_ wy -> aobj FF X 32 -> shadow_zero M X 4 -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
  L5OMA.a_ok M dv fba -> aobj FF dv 32 -> shadow_zero M dv 4 -> (X + 32 <= dv \/ dv + 32 <= X) ->
  L5OMA.stksh ar M (E - SCRD) -> SCRD mod 8 = 0 ->
  L5OMA.acredit_for L cr2 L5DIA.DIVO2_K (L5DIA.divO2_bytes (L5.bo_cap by_)) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
      regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 X ->
      L5OMA.y_after L ar LB (FF ++ LK') M' X by_ LB' -> L5OMA.a_ok M' dv fba ->
      L5OMA.acredit_after L cr2 L5DIA.DIVO2_K (L5DIA.divO2_bytes (L5.bo_cap by_)) cr' ->
      ahpres L ar LB FF E SCRD [(X, 32); (L5.bo_data X by_, 8 * L5.bo_cap by_)] M M' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R3 AMEMSET M3 model3) K.
Proof.
  intros BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3 YOK AOX SZX LY1 CAPY AOK AOD SZD APXD SSH S8 CRD KN.
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model X 32 E SCRD HH0 AOX ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & _ & _ & OCL & OCLSH). change (32 / 8) with 4 in OCLSH.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model dv 32 E SCRD HH0 AOD ltac:(clear; lia) ltac:(reflexivity)) as (DR & DBIG & DDEF & _ & _ & DCL & DCLSH). change (32 / 8) with 4 in DCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. }
  destruct WF0 as (WB & _).
  destruct YOK as (OBY & OLY & REDY & INY). destruct AOK as (OBA & SGA).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH4 : (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0 /\ 0 <= F / 8 /\ F / 8 + 16 <= 17592186044416 /\ F / 8 * 8 = F) by (clear - FRP ALF; unfold aligned in ALF; lia).
  assert (SA : (E - 96) mod 16 = 0 /\ (E - 96) mod 32 = 0 /\ (E - SCRD) mod 8 = 0 /\ (E - 96 - L5DIA.DIVO_SCR) mod 8 = 0). { change L5DIA.DIVO_SCR with 5520. clear - EA S8. unfold aligned in EA. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (CLX : forall a, X <= a < X + 32 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (obj_client L ar LB FF E SCRD X 32 a AOX Ha)).
  assert (CLD : forall a, dv <= a < dv + 32 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (obj_client L ar LB FF E SCRD dv 32 a AOD Ha)).
  assert (SFR : forall a, F / 8 + SB <= a < F / 8 + SB + 16 -> S F <= a <= S (F + 128 - 1)). { intros a Ha. unfold S. rewrite (proj1 (proj2 F8)). clear - Ha. unfold SB in *. lia. }
  (* [comment removed for export] *)
  assert (CLY : forall a, L5.bo_data X by_ <= a < L5.bo_data X by_ + 8 * L5.bo_cap by_ -> aclient L ar LB FF E SCRD a).
  { intros a Ha. unfold L5.bo_data, L5.bo_cap in Ha. destruct (L5.bo_st by_) as [v0 v1|capy qy]. apply CLX. clear - Ha; lia. apply (block_client L ar LB FF E SCRD qy (8 * capy) a (proj1 INY) Ha). }
  (* [comment removed for export] *)
  apply (dq_memset fx R3 M3 model3 [] [] LK2 cr2 A BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3).
  intros fx6 R6 M6 model6 BI6 RI6 QSH6 ZT6 SZT6 HD6.
  pose proof BI6 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (EKX : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF E SCRD a -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc. apply B7. split. exact Ha. split. exact Hc. intros rr []. }
  assert (AHP6 : ahpres L ar LB FF E SCRD [] M M6). { apply ahpres_of. exact B7. destruct B6 as (_ & _ & _ & _ & DSCR & _). exact DSCR. exact B8. }
  assert (TY : L5ADVEA.tob LB M X by_ wy). { split. exact OBY. split. exact OLY. split. exact SZX. intros cap q Eq. rewrite Eq in INY. exact (proj1 INY). }
  destruct (L5ADVO1.arg_kept L ar C HI LY HIok M M6 model LB FF LK cr2 A E SCRD [] X by_ wy HH0 AHP6 AOX TY ltac:(intros a _ rr [])) as (OBY6 & OLY6).
  assert (OBA6 : L5.big_at RSEGS M6 dv (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1))). { eapply L5C.big_at_agree. 4: exact OBA. 2: clear - DR; lia. 2: clear - DR; lia. intros j Hj. apply EKX. clear - Hj DR; lia. apply CLD. exact Hj. }
  assert (SZX6 : shadow_zero M6 X 4). { intros j Hj. unfold byte_at. unfold S. rewrite EKX. exact (SZX j Hj). clear - Hj OR; unfold SB; lia. apply OCLSH. exact Hj. }
  assert (SZD6 : shadow_zero M6 dv 4). { intros j Hj. unfold byte_at. unfold S. rewrite EKX. exact (SZD j Hj). clear - Hj DR; unfold SB; lia. apply DCLSH. exact Hj. }
  assert (SSH6 : L5OMA.stksh ar M6 (E - 96 - L5DIA.DIVO_SCR)).
  { apply (stksh_sub M M6 (E - SCRD) (E - 96 - L5DIA.DIVO_SCR) SSH). change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia. exact (proj1 (proj2 (proj2 SA))). exact (proj2 (proj2 (proj2 SA))).
    clear - SLO; lia. clear - SLO FCEIL FR; lia. exact TOP. clear - SPT; lia. intros a Ha Hs. apply EKX. exact Ha. right; right; right; right; left. exact Hs. }
  (* [comment removed for export] *)
  pose proof (pfq_of_binv [] [] M6 model6 LK2 cr2 A BI6) as (W96 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof RI6 as (Y2 & Y8 & Y9 & Y3 & Y4 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  set (MV := mrestrict (ahid A model6) M6) in *.
  pose proof (vomP2_conc fx6 R6 MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 58%nat => U R6 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pEQ & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR13 & pR14)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok ([] ++ LB) FF' LK2 cr2 A M6 model6 fx6 fx1 R6 0x91f18 R1 L5DSA.DIVIDE K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1 [] [] M6 model6 LK2 cr2 A model1 BI6 HH1 AM1 RT1) as BI1.
  assert (RI1 : rinvQ R E F X dv R1). { apply (rinvQ_ks R E F X dv R6 R1 KS_vomP2 RI6 pKS). vm_compute; reflexivity. }
  pose proof RI1 as (Z2 & Z8 & Z9 & Z3 & Z4 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF.
  assert (ND : NoDup (map ff_addr (FF' ++ LK2))). { clear - WF. decompose [and] WF. assumption. }
  assert (STKc : astk ar M6 SPA L5DIA.DIVO_SCR). { apply (astk_sub ar M6 M6 E SCRD 96 L5DIA.DIVO_SCR B6 (mem_grows_refl M6)). clear; lia. vm_compute; discriminate. change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia. exact (proj1 SA). }
  assert (ROOM1 : ffrk 1 FF' LK2 5). { apply (ffrk_push 1 FF LK LK2 (F, 1, SPA + 32) 6 5 FFR1 B5 ND). clear; lia. }
  assert (ROOM3 : ffrk 3 FF' LK2 3). { apply (ffrk_le 3 FF' LK2 4 3). apply (ffrk_push_other 3 FF LK LK2 (F, 1, SPA + 32) 4). cbn [ff_class fst snd]. clear; lia. exact FFR3. exact B5. exact ND. clear; lia. }
  assert (RSc : ffrs FF' SPA). { apply (ffrs_push FF E). exact FFRS. clear; lia. clear; lia. }
  assert (XF : X + 32 <= F \/ F + 128 <= X). { apply (apart_of_client (aclient L ar LB FF E SCRD) X 32 F 128 ltac:(clear; lia) ltac:(clear; lia) CLX). intros a Ha. apply NCF. left. exact Ha. }
  assert (DF : dv + 32 <= F \/ F + 128 <= dv). { apply (apart_of_client (aclient L ar LB FF E SCRD) dv 32 F 128 ltac:(clear; lia) ltac:(clear; lia) CLD). intros a Ha. apply NCF. left. exact Ha. }
  set (Wy := [(X, 32); (L5.bo_data X by_, 8 * L5.bo_cap by_)]).
  assert (WAV : forall rr a, In rr [(X, 32); (L5.bo_data X by_, 8 * L5.bo_cap by_); (F + 32, 32)] -> L5.in_rng rr a -> ~ qocell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 16)).
  { intros rr a [Hr|[Hr|[Hr|[]]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
    - split. intros D. apply (NCS a). unfold qocell in D. clear - D; lia. apply CLX. exact IR. intros D. apply (NCF a). right. apply SFR. exact D. apply CLX. exact IR.
    - split. intros D. apply (NCS a). unfold qocell in D. clear - D; lia. apply CLY. exact IR. intros D. apply (NCF a). right. apply SFR. exact D. apply CLY. exact IR.
    - split. unfold qocell. clear - IR SFB; lia. unfold SB. clear - IR FSH4 FBIG FRP. lia. }
  assert (WOUT : forall a, aclient L ar LB FF E SCRD a -> L5.outside Wy a -> L5.outside [(X, 32); (L5.bo_data X by_, 8 * L5.bo_cap by_); (F + 32, 32)] a).
  { intros a Hc Ho rr [Hr|[Hr|[Hr|[]]]] IR. apply (Ho rr). left; exact Hr. exact IR. apply (Ho rr). right; left; exact Hr. exact IR.
    subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. apply (NCF a). left. clear - IR; lia. exact Hc. }
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX). assert (AOD' : aobj FF' dv 32) by (apply aobj_cons; exact AOD).
  assert (AOT' : aobj FF' (F + 32) 32). { exists (F, 1, SPA + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 1) with 128. split. clear; lia. split. clear; lia. exact (proj1 (proj2 FSH4)). }
  apply (HdivO2 fx1 R1 M6 model1 K ([] ++ LB) FF' LK2 cr2 A X dv (F + 32) SPA 0x91f30 fba by_ wy HH1 AM1 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - rewrite r12. exact pR12.
  - rewrite r13q. exact pR13.
  - rewrite r14q. exact pR14.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Z2.
  - exact (proj1 (proj2 SA)).
  - rewrite r4, Z4, <- G4. reflexivity.
  - exact STKc.
  - exact SSH6.
  - exact ROOM1.
  - exact ROOM3.
  - exact RSc.
  - split. exact OBY6. split. exact OLY6. split. exact REDY. exact INY.
  - exact AOX'.
  - exact SZX6.
  - exact LY1.
  - exact CAPY.
  - split. exact OBA6. exact SGA.
  - exact AOD'.
  - exact SZD6.
  - exact ZT6.
  - exact AOT'.
  - exact SZT6.
  - exact APXD.
  - clear - XF; lia.
  - clear - DF; lia.
  - exact CRD.
  - intros fx2 R2 Mn modeln LBn crn LKn An POST RTn IAn AMn ILKn HHn.
    destruct POST as (RPn & (LBy & LBq & ELB & (by' & wy' & OBYn & OLYn & STY) & (bq & wq & OBQn & OLQn & STQ)) & AOKn & CRn & AHPn).
    assert (RIn : rinvQ R E F X dv R2) by (apply (rinvQ_pres R E F X dv R1 R2 RI1 RPn)).
    subst LBn. cbn [app] in HHn. rewrite app_assoc in HHn.
    assert (BIn : binv Wy (LBy ++ LBq) Mn modeln LKn crn An).
    { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G
               [] Wy [] [] (LBy ++ LBq) M6 model1 LK2 cr2 A Mn modeln LKn crn An L5DIA.DIVO_SCR [(X, 32); (L5.bo_data X by_, 8 * L5.bo_cap by_); (F + 32, 32)] BI1 AHPn HHn AMn RTn IAn ILKn).
      - vm_compute; discriminate.
      - change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia.
      - exact WAV.
      - exact WOUT.
      - intros a _ rr []. }
    (* [comment removed for export] *)
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHn) as WFn.
    assert (NDn : NoDup (map fst ((LBy ++ LBq) ++ LB))). { clear - WFn. decompose [and] WFn. assumption. }
    destruct WFn as (WBn & _).
    assert (LBYC : LBy = [] \/ exists q', LBy = [(q', 64)]).
    { destruct (L5.bo_st by_) as [v0 v1|capy qy]; destruct (L5.bo_st by') as [v0' v1'|cap' q']. left; exact STY. right. exists q'. exact (proj1 (proj2 STY)). destruct STY. left. exact (proj2 (proj2 STY)). }
    set (blk := match L5.bo_st bq with L5.BInl _ _ => None | L5.BDyn cap q => Some (q, 8 * cap) end).
    assert (BLK : match blk with None => LBy = LBy ++ LBq | Some (q, n) => In (q, n) ((LBy ++ LBq) ++ LB) /\ lb_remove q ((LBy ++ LBq) ++ LB) = LBy ++ LB end).
    { subst blk. destruct (L5.bo_st bq) as [t0 t1|capq qq]. rewrite STQ. symmetry. apply app_nil_r. destruct STQ as (ELQ & _). subst LBq.
      split. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
      destruct LBYC as [-> | (q' & ->)]. cbn [app]. apply lb_remove_head.
      cbn [app]. rewrite lb_remove_skip. rewrite lb_remove_head. reflexivity.
      cbn [app map fst] in NDn. apply list_relations.list.NoDup_cons in NDn. destruct NDn as (NI & _). intros Eq. apply NI. subst q'. apply list_basics.list.elem_of_cons. left. reflexivity. }
    (* [comment removed for export] *)
    assert (QOB : qobj_at Mn (F + 32) bq blk) by (split; [exact OBQn | subst blk; destruct (L5.bo_st bq); reflexivity]).
    apply (dq_dtor fx2 R2 Mn modeln Wy (LBy ++ LBq) LBy LKn crn An bq blk BIn RIn QOB BLK).
    intros fx8 R8 M8 model8 A8 BI8 RI8 IA8 PRES8.
    (* [comment removed for export] *)
    apply (dq_tail fx8 R8 M8 model8 Wy LBy LKn crn A8 BI8 RI8).
    intros fxf Rf Mf modelf RPf R10f FRMf AHPf RTf AMf HHf.
    assert (NWR : forall a, (X <= a < X + 32 \/ dv <= a < dv + 32) -> ~ L5AFK.Wret F fl 1 a).
    { intros a Ha. assert (Hc : aclient L ar LB FF E SCRD a) by (destruct Ha as [Ha|Ha]; [apply CLX | apply CLD]; exact Ha).
      unfold L5AFK.Wret. change (ff_bytes 1 / 8) with 16. intros [[Wa|Wa]|Wa].
      - apply (NCF a). left; clear - Wa; lia. exact Hc.
      - apply (NCF a). right. apply SFR. exact Wa. exact Hc.
      - subst a. apply FLNC. destruct Ha as [Ha|Ha]. apply (obj_client L ar LB FF' 0 0 X 32 fl AOX' Ha). apply (obj_client L ar LB FF' 0 0 dv 32 fl AOD' Ha). }
    assert (KEEPO : forall a, (X <= a < X + 32 \/ dv <= a < dv + 32) -> Mf (Z_to_bv 64 a) = Mn (Z_to_bv 64 a)).
    { intros a Ha. assert (RGa : 0 <= a < 2 ^ 64) by (clear - Ha OR DR; lia). rewrite FRMf. apply PRES8. exact RGa.
      destruct Ha as [Ha|Ha]. apply (obj_client L ar (LBy ++ LB) FF' SPA OPDEL_SCR X 32 a AOX' Ha). apply (obj_client L ar (LBy ++ LB) FF' SPA OPDEL_SCR dv 32 a AOD' Ha). exact RGa. apply NWR. exact Ha. }
    assert (KEEPB : forall q n a, In (q, n) (LBy ++ LB) -> q <= a < q + n -> Mf (Z_to_bv 64 a) = Mn (Z_to_bv 64 a)).
    { intros q n a Hin Ha.
      assert (Hin' : In (q, n) ((LBy ++ LBq) ++ LB)). { apply in_app_or in Hin. destruct Hin as [Hin|Hin]. apply in_or_app. left. apply in_or_app. left. exact Hin. apply in_or_app. right. exact Hin. }
      destruct (WBn _ Hin') as ((Q0 & _ & _ & _ & QCE & (_ & QAPP & Q47)) & _ & _ & _ & _ & QFA & QFS). cbn [fst snd] in *.
      assert (RGa : 0 <= a < 2 ^ 64) by (clear - Ha Q0 Q47; lia). rewrite FRMf. apply PRES8. exact RGa.
      apply (block_client L ar (LBy ++ LB) FF' SPA OPDEL_SCR q n a Hin Ha). exact RGa.
      unfold L5AFK.Wret. change (ff_bytes 1 / 8) with 16. specialize (QFA (F, 1, SPA + 32) ltac:(apply in_or_app; left; left; reflexivity)). cbn [ff_addr ff_class fst snd] in QFA. change (ff_bytes 1) with 128 in QFA.
      unfold BIGSHADOW_LO, BIGSHADOW_HI in QAPP. intros [[Wa|Wa]|Wa]. clear - Wa Ha QFA; lia. unfold SB in Wa. clear - Wa Ha QAPP FSH4; lia. subst a. clear - Ha QFS FLP. unfold FS_BYTES in *. lia. }
    apply (KN fxf Rf Mf modelf (LBy ++ LB) crn LKn A8).
    + exact RPf.
    + rewrite r10. exact R10f.
    + exists by', wy'. split. { eapply L5C.big_at_agree. 4: exact OBYn. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply KEEPO. left; exact Hj. }
      split. { destruct OLYn as (L1 & L2 & L3). split. exact L1. split. exact L2. destruct (L5.bo_st by') as [v0' v1'|cap' q'] eqn:ESY'. exact L3.
               pose proof OBYn as (_ & _ & _ & STn). rewrite ESY' in STn. destruct STn as (_ & _ & _ & LCn & CRRn & _ & Q4096 & Q47 & _).
               assert (INB' : In (q', 8 * cap') (LBy ++ LB)).
               { destruct (L5.bo_st by_) as [v0 v1|capy qy]. destruct STY as (-> & -> & _). left. reflexivity. destruct STY as (-> & -> & ->). cbn [app]. exact (proj1 INY). }
               eapply (L5C.limbs_at_agree RSEGS Mn Mf). 4: exact L3. 2: clear - Q4096; lia. 2:{ rewrite L1. clear - Q47 LCn CRRn. lia. }
               intros j Hj. rewrite L1 in Hj. apply (KEEPB q' (8 * cap') j INB'). clear - Hj LCn. lia. }
      destruct (L5.bo_st by_) as [v0 v1|capy qy]; destruct (L5.bo_st by') as [v0' v1'|cap' q'].
      * rewrite STY. reflexivity.
      * destruct STY as (EC & ELY & _). subst LBy. split. exact EC. split. reflexivity. subst cap'. cbn [app] in HHf. exact (L5ADH.afresh_of_inv L ar C HI HIok q' 64 LB FF LKn crn A8 Mf (vml_of modelf) HHf).
      * destruct STY.
      * destruct STY as (EC & EQ & ELY). subst LBy. split. exact EC. split. exact EQ. reflexivity.
    + destruct AOKn as (OBAn & SGAn). split. 2: exact SGAn. eapply L5C.big_at_agree. 4: exact OBAn. 2: clear - DR; lia. 2: clear - DR; lia. intros j Hj. apply KEEPO. right; exact Hj.
    + exact CRn.
    + exact AHPf.
    + exact RTf.
    + intros x Hx. apply IA8. apply IAn. exact Hx.
    + exact AMf.
    + intros x Hx. apply LKI2. apply ILKn. exact Hx.
    + exact HHf.
Qed.
End O2.

Section O1.
Hypothesis HdivO1 : L5DIA.divO1_specA L ar HI.
(* [comment removed for export] *)
Definition om1_e3A (M' : word -> option byte) (R' : bvmap 5 word) (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (R1 : bvmap 5 word) (Mq : word -> option byte),
     (L5DSA.U R1 1 = L5DSA.DIV_RET_O /\ L5DSA.U R1 8 = E /\ L5DSA.U R1 9 = E - 96 /\ L5DSA.U R1 18 = F /\ L5DSA.U R1 19 = X /\ L5DSA.U R1 20 = dv /\ L5DSA.U R1 21 = F + 32
      /\ L5DSA.U R1 22 = S F /\ L5DSA.U R1 23 = F /\ L5DSA.U R1 24 = L5DSA.RETIRE_MAGIC /\ L5DSA.U R1 25 = L5DSA.U R 25 /\ L5DSA.U R1 26 = L5DSA.U R 26 /\ L5DSA.U R1 27 = L5DSA.U R 27)
  /\ getr R1 3%bv = getr R 3%bv /\ getr R1 4%bv = getr R 4%bv
  /\ L5DIA.divO1_e3A L ar LB FF' cr2 Mq M' R1 R' X (F + 32) (E - 96) F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx LB' cr'
  /\ qown E F R M' /\ L5DIA.sh_op M' F /\ L5DSA.fr_live L ar LB FF M' 1 F fl (E - 64)
  /\ ahpres L ar LB FF E SCRD [(X, 32)] M M'.

Lemma om1_rest (fx : FPState) R3 M3 model3 fbx (bb : L5.bigobj) (wb : list Z) :
  binv [] [] M3 model3 LK2 cr2 A -> rinvQ R E F X dv R3 -> getr R3 (reg 1) = Z_to_bv 64 0x91f18 ->
  getr R3 (reg 10) = Z_to_bv 64 (F + 40) /\ getr R3 (reg 11) = Z_to_bv 64 0 /\ getr R3 (reg 12) = Z_to_bv 64 24 ->
  qsh M3 F 0 -> shadow_zero M3 (F + 32) 4 -> L5.u8_at RSEGS M3 (F + 32) 0 -> L5.u64_at RSEGS M3 F 1102416563 ->
  L5OMA.x_is_a M X fbx -> aobj FF X 32 -> shadow_zero M X 4 ->
  L5OMA.b_ok LB M dv bb wb -> aobj FF dv 32 -> shadow_zero M dv 4 -> (X + 32 <= dv \/ dv + 32 <= X) ->
  L5.bo_cap bb <= 268 -> (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->
  L5OMA.stksh ar M (E - SCRD) -> SCRD mod 8 = 0 ->
  L5OMA.acredit_for L cr2 L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
      regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 X ->
      L5OMA.x_after L ar LB (FF ++ LK') M' X LB' -> L5.big_at RSEGS M' dv bb -> L5C.obj_limbs RSEGS M' bb wb -> (1 <= L5.bo_len bb)%nat ->
      L5OMA.acredit_after L cr2 L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) cr' ->
      ahpres L ar LB FF E SCRD [(X, 32)] M M' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (F3 fl3 : Z),
      L5DSA.zero_throw_atA L ar SCRD LB FF R M R' M' E X dv F fl F3 fl3 ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB (L5DSA.ff_e2 FF E F F3) LK' cr2 A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ZERO_THROW M' model') K) ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
          (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx : Z),
      om1_e3A M' R' F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' (L5DIA.ff_o ((F, 1, E - 64) :: FF) (E - 96) F3a F1b F3b F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R3 AMEMSET M3 model3) K.
Proof.
  intros BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3 XA AOX SZX BOK AOD SZD APXD CAPB DYN3 SSH S8 CRD KN KE2 KE3.
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model X 32 E SCRD HH0 AOX ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & _ & _ & OCL & OCLSH). change (32 / 8) with 4 in OCLSH.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model dv 32 E SCRD HH0 AOD ltac:(clear; lia) ltac:(reflexivity)) as (DR & DBIG & DDEF & _ & _ & DCL & DCLSH). change (32 / 8) with 4 in DCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. }
  destruct WF0 as (WB & _).
  destruct XA as (OBXA & SGX). pose proof BOK as (OBB & OLB & REDB & INB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH4 : (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0 /\ 0 <= F / 8 /\ F / 8 + 16 <= 17592186044416 /\ F / 8 * 8 = F) by (clear - FRP ALF; unfold aligned in ALF; lia).
  assert (SA : (E - 96) mod 16 = 0 /\ (E - 96) mod 32 = 0 /\ (E - SCRD) mod 8 = 0 /\ (E - 96 - L5DIA.DIVO_SCR) mod 8 = 0). { change L5DIA.DIVO_SCR with 5520. clear - EA S8. unfold aligned in EA. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (CLX : forall a, X <= a < X + 32 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (obj_client L ar LB FF E SCRD X 32 a AOX Ha)).
  assert (CLD : forall a, dv <= a < dv + 32 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (obj_client L ar LB FF E SCRD dv 32 a AOD Ha)).
  assert (SFR : forall a, F / 8 + SB <= a < F / 8 + SB + 16 -> S F <= a <= S (F + 128 - 1)). { intros a Ha. unfold S. rewrite (proj1 (proj2 F8)). clear - Ha. unfold SB in *. lia. }
  (* [comment removed for export] *)
  apply (dq_memset fx R3 M3 model3 [] [] LK2 cr2 A BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3).
  intros fx6 R6 M6 model6 BI6 RI6 QSH6 ZT6 SZT6 HD6.
  pose proof BI6 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (EKX : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF E SCRD a -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc. apply B7. split. exact Ha. split. exact Hc. intros rr []. }
  assert (AHP6 : ahpres L ar LB FF E SCRD [] M M6). { apply ahpres_of. exact B7. destruct B6 as (_ & _ & _ & _ & DSCR & _). exact DSCR. exact B8. }
  assert (TB : L5ADVEA.tob LB M dv bb wb). { split. exact OBB. split. exact OLB. split. exact SZD. intros cap q Eq. rewrite Eq in INB. exact INB. }
  destruct (L5ADVO1.arg_kept L ar C HI LY HIok M M6 model LB FF LK cr2 A E SCRD [] dv bb wb HH0 AHP6 AOD TB ltac:(intros a _ rr [])) as (OBB6 & OLB6).
  assert (OBX6 : L5.big_at RSEGS M6 X (L5.BO fbx 2 (L5.BInl L5PSA.A0 L5PSA.A1))). { eapply L5C.big_at_agree. 4: exact OBXA. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply EKX. clear - Hj OR; lia. apply CLX. exact Hj. }
  assert (SZX6 : shadow_zero M6 X 4). { intros j Hj. unfold byte_at. unfold S. rewrite EKX. exact (SZX j Hj). clear - Hj OR; unfold SB; lia. apply OCLSH. exact Hj. }
  assert (SZD6 : shadow_zero M6 dv 4). { intros j Hj. unfold byte_at. unfold S. rewrite EKX. exact (SZD j Hj). clear - Hj DR; unfold SB; lia. apply DCLSH. exact Hj. }
  assert (SSH6 : L5OMA.stksh ar M6 (E - 96 - L5DIA.DIVO_SCR)).
  { apply (stksh_sub M M6 (E - SCRD) (E - 96 - L5DIA.DIVO_SCR) SSH). change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia. exact (proj1 (proj2 (proj2 SA))). exact (proj2 (proj2 (proj2 SA))).
    clear - SLO; lia. clear - SLO FCEIL FR; lia. exact TOP. clear - SPT; lia. intros a Ha Hs. apply EKX. exact Ha. right; right; right; right; left. exact Hs. }
  (* [comment removed for export] *)
  pose proof (pfq_of_binv [] [] M6 model6 LK2 cr2 A BI6) as (W96 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof RI6 as (Y2 & Y8 & Y9 & Y3 & Y4 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  set (MV := mrestrict (ahid A model6) M6) in *.
  pose proof (vomP2_conc fx6 R6 MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 58%nat => U R6 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pEQ & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR13 & pR14)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok ([] ++ LB) FF' LK2 cr2 A M6 model6 fx6 fx1 R6 0x91f18 R1 L5DSA.DIVIDE K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1 [] [] M6 model6 LK2 cr2 A model1 BI6 HH1 AM1 RT1) as BI1.
  assert (RI1 : rinvQ R E F X dv R1). { apply (rinvQ_ks R E F X dv R6 R1 KS_vomP2 RI6 pKS). vm_compute; reflexivity. }
  pose proof RI1 as (Z2 & Z8 & Z9 & Z3 & Z4 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF.
  assert (ND : NoDup (map ff_addr (FF' ++ LK2))). { clear - WF. decompose [and] WF. assumption. }
  assert (STKc : astk ar M6 SPA L5DIA.DIVO_SCR). { apply (astk_sub ar M6 M6 E SCRD 96 L5DIA.DIVO_SCR B6 (mem_grows_refl M6)). clear; lia. vm_compute; discriminate. change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia. exact (proj1 SA). }
  assert (ROOM1 : ffrk 1 FF' LK2 5). { apply (ffrk_push 1 FF LK LK2 (F, 1, SPA + 32) 6 5 FFR1 B5 ND). clear; lia. }
  assert (ROOM3 : ffrk 3 FF' LK2 3). { apply (ffrk_le 3 FF' LK2 4 3). apply (ffrk_push_other 3 FF LK LK2 (F, 1, SPA + 32) 4). cbn [ff_class fst snd]. clear; lia. exact FFR3. exact B5. exact ND. clear; lia. }
  assert (RSc : ffrs FF' SPA). { apply (ffrs_push FF E). exact FFRS. clear; lia. clear; lia. }
  assert (XF : X + 32 <= F \/ F + 128 <= X). { apply (apart_of_client (aclient L ar LB FF E SCRD) X 32 F 128 ltac:(clear; lia) ltac:(clear; lia) CLX). intros a Ha. apply NCF. left. exact Ha. }
  assert (DF : dv + 32 <= F \/ F + 128 <= dv). { apply (apart_of_client (aclient L ar LB FF E SCRD) dv 32 F 128 ltac:(clear; lia) ltac:(clear; lia) CLD). intros a Ha. apply NCF. left. exact Ha. }
  set (Wx := [(X, 32)]).
  assert (WAV : forall rr a, In rr [(X, 32); (F + 32, 32)] -> L5.in_rng rr a -> ~ qocell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 16)).
  { intros rr a [Hr|[Hr|[]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
    - split. intros D. apply (NCS a). unfold qocell in D. clear - D; lia. apply CLX. exact IR. intros D. apply (NCF a). right. apply SFR. exact D. apply CLX. exact IR.
    - split. unfold qocell. clear - IR SFB; lia. unfold SB. clear - IR FSH4 FBIG FRP. lia. }
  assert (WOUT : forall a, aclient L ar LB FF E SCRD a -> L5.outside Wx a -> L5.outside [(X, 32); (F + 32, 32)] a).
  { intros a Hc Ho rr [Hr|[Hr|[]]] IR. apply (Ho rr). left; exact Hr. exact IR.
    subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. apply (NCF a). left. clear - IR; lia. exact Hc. }
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX). assert (AOD' : aobj FF' dv 32) by (apply aobj_cons; exact AOD).
  assert (AOT' : aobj FF' (F + 32) 32). { exists (F, 1, SPA + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 1) with 128. split. clear; lia. split. clear; lia. exact (proj1 (proj2 FSH4)). }
  (* [comment removed for export] *)
  assert (UV : L5DSA.U R1 1 = L5DSA.DIV_RET_O /\ L5DSA.U R1 8 = E /\ L5DSA.U R1 9 = E - 96 /\ L5DSA.U R1 18 = F /\ L5DSA.U R1 19 = X /\ L5DSA.U R1 20 = dv /\ L5DSA.U R1 21 = F + 32
      /\ L5DSA.U R1 22 = S F /\ L5DSA.U R1 23 = F /\ L5DSA.U R1 24 = L5DSA.RETIRE_MAGIC /\ L5DSA.U R1 25 = L5DSA.U R 25 /\ L5DSA.U R1 26 = L5DSA.U R 26 /\ L5DSA.U R1 27 = L5DSA.U R 27).
  { split. { unfold L5DSA.U. change (Z_to_bv 5 1) with (reg 1). rewrite pR1. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 8) with (reg 8). rewrite Z8. apply L5.unsigned_lit. exact ERG. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 9) with (reg 9). rewrite Z9. apply L5.unsigned_lit. clear - ER; lia. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 18) with (reg 18). rewrite Z18. apply L5.unsigned_lit. exact FRG. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 19) with (reg 19). rewrite Z19. apply L5.unsigned_lit. exact XR. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 20) with (reg 20). rewrite Z20. apply L5.unsigned_lit. exact DVR. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 21) with (reg 21). rewrite Z21. apply L5.unsigned_lit. clear - FRP; lia. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 22) with (reg 22). rewrite Z22. unfold S. apply L5.unsigned_lit. clear - FSH4; unfold SB; lia. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 23) with (reg 23). rewrite Z23. apply L5.unsigned_lit. exact FRG. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 24) with (reg 24). rewrite Z24. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 25) with (reg 25). rewrite Z25. reflexivity. }
    split. { unfold L5DSA.U. change (Z_to_bv 5 26) with (reg 26). rewrite Z26. reflexivity. }
    unfold L5DSA.U. change (Z_to_bv 5 27) with (reg 27). rewrite Z27. reflexivity. }
  (* [comment removed for export] *)
  assert (THROWK : forall (Mt : word -> option byte) (Wt Wo : list L5.range) LBt FFt LKt crt At modelt,
            ahpres L ar ([] ++ LB) FF' SPA L5DIA.DIVO_SCR Wt M6 Mt -> ri_inv HI LBt FFt LKt crt At Mt (vml_of modelt) -> In (F, 1, E - 64) FFt ->
            (forall a, aclient L ar LB FF E SCRD a -> L5.outside Wo a -> L5.outside Wt a) ->
            (forall a, (SPA <= a < E \/ F <= a < F + 32 \/ F / 8 + SB <= a < F / 8 + SB + 16) -> L5.outside Wt a) ->
            qown E F R Mt /\ L5DIA.sh_op Mt F /\ L5DSA.fr_live L ar LB FF Mt 1 F fl (E - 64) /\ ahpres L ar LB FF E SCRD Wo M Mt).
  { intros Mt Wt Wo LBt FFt LKt crt At modelt AHt HHt INF WSUB WOFF.
    assert (KQ : forall a, 0 <= a < 2 ^ 64 -> aclient L ar ([] ++ LB) FF' SPA L5DIA.DIVO_SCR a -> L5.outside Wt a -> Mt (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
    { intros a Ha Hc Ho. apply (proj1 AHt). split. exact Ha. split. exact Hc. exact Ho. }
    assert (KF0 : forall a, F <= a < F + 32 -> ~ (F + 24 <= a < F + 32) -> Mt (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
    { intros a Ha Hn. apply KQ. clear - Ha FRP; lia. apply (fframe_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ha Hn; lia. apply WOFF. right; left. exact Ha. }
    assert (KSH : forall a, F / 8 + SB <= a < F / 8 + SB + 16 -> Mt (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
    { intros a Ha. apply KQ. clear - Ha FSH4; unfold SB in Ha; lia. apply (fframe_shadow_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. apply SFR. exact Ha. apply WOFF. right; right. exact Ha. }
    assert (KST : forall a, SPA <= a < E -> Mt (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
    { intros a Ha. apply KQ. clear - Ha ER; lia. apply stack_client. clear - Ha SLO SPC SPT; lia. clear - Ha; lia. apply WOFF. left. exact Ha. }
    split. { apply (qown_agree E F R M6 Mt ltac:(clear - ER; lia) ltac:(clear - ER; lia) B9). intros a Ha. apply KST. unfold qocell in Ha. clear - Ha; lia. }
    assert (SHX : forall a v, F / 8 + SB <= a < F / 8 + SB + 16 -> L5.u8_at RSEGS M6 a v -> byte_at Mt a v).
    { intros a v Ha Hu. unfold byte_at. rewrite (KSH a Ha). apply (byte_of_u8 M6 a v Hu). right. clear - Ha FSH4; unfold SB in Ha; lia. clear - Ha FSH4; unfold SB in Ha; lia. }
    split. { destruct QSH6 as (Q0 & Q4 & Q8 & Q12). unfold L5DIA.sh_op, L5DSA.sh_run, S. unfold shr8 in Q0, Q4, Q8, Q12.
             split. intros j Hj. apply SHX. clear - Hj; lia. exact (Q0 j Hj).
             split. intros j Hj. apply SHX. clear - Hj; lia. exact (Q4 j Hj).
             split. intros j Hj. apply SHX. clear - Hj; lia. exact (Q8 j Hj).
             intros j Hj. apply SHX. clear - Hj; lia. exact (Q12 j Hj). }
    split. { apply L5DSA.FRL.
             - refine (proj1 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ modelt F 1 _ _ fl HH2 HHt (or_introl eq_refl) INF Hk FLC)).
             - exact FLP.
             - replace (E - 96 + 32) with (E - 64) in FLNC by (clear; lia). exact FLNC.
             - exact FLA.
             - eapply L5C.u64_at_agree. 4: exact HD6. 2: clear - FRP; lia. 2: clear - FRP; lia. intros j Hj. apply KF0. clear - Hj; lia. clear - Hj; lia. }
    apply ahpres_of.
    + eapply ek_trans. { eapply ek_W. exact B7. intros a _ rr []. } apply (ek_callee L ar LB [] FF [(F, 1, SPA + 32)] E SCRD SPA L5DIA.DIVO_SCR Wo Wt M6 Mt AHt).
      change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia. clear; lia. exact WSUB.
    + assert (STKt : astk ar Mt E SCRD).
      { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ ([] ++ LB) FF' M6 M6 Mt E SCRD SPA L5DIA.DIVO_SCR Wt B1 B6 (mem_grows_refl M6) AHt).
        change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia. clear; lia. clear - HSCR; lia. }
      eapply astk_defined. exact STKt. clear; lia. clear; lia.
    + eapply dk_trans. exact B8. apply (dk_callee L ar LB [] FF [(F, 1, SPA + 32)] E SCRD SPA L5DIA.DIVO_SCR Wt M6 Mt AHt).
      change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia. clear; lia. }
  apply (HdivO1 fx1 R1 M6 model1 K ([] ++ LB) FF' LK2 cr2 A X dv (F + 32) SPA 0x91f30 fbx bb wb HH1 AM1 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - rewrite r12. exact pR12.
  - rewrite r13q. exact pR13.
  - rewrite r14q. exact pR14.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Z2.
  - exact (proj1 (proj2 SA)).
  - rewrite r4, Z4, <- G4. reflexivity.
  - exact STKc.
  - exact SSH6.
  - exact ROOM1.
  - exact ROOM3.
  - exact RSc.
  - split. exact OBX6. exact SGX.
  - exact AOX'.
  - exact SZX6.
  - split. exact OBB6. split. exact OLB6. split. exact REDB. exact INB.
  - exact AOD'.
  - exact SZD6.
  - exact ZT6.
  - exact AOT'.
  - exact SZT6.
  - exact APXD.
  - clear - XF; lia.
  - clear - DF; lia.
  - exact CAPB.
  - exact DYN3.
  - exact CRD.
  - (* [comment removed for export] *)
    intros fx2 R2 Mn modeln LBn crn LKn An POST RTn IAn AMn ILKn HHn.
    destruct POST as (RPn & (LBx & LBq & ELB & (bx & wx & OBXn & OLXn & NEGX & STX) & (bq & wq & OBQn & OLQn & STQ)) & OBBn & OLBn & LB1 & CRn & AHPn).
    assert (RIn : rinvQ R E F X dv R2) by (apply (rinvQ_pres R E F X dv R1 R2 RI1 RPn)).
    subst LBn. cbn [app] in HHn. rewrite app_assoc in HHn.
    assert (BIn : binv Wx (LBx ++ LBq) Mn modeln LKn crn An).
    { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G
               [] Wx [] [] (LBx ++ LBq) M6 model1 LK2 cr2 A Mn modeln LKn crn An L5DIA.DIVO_SCR [(X, 32); (F + 32, 32)] BI1 AHPn HHn AMn RTn IAn ILKn).
      - vm_compute; discriminate.
      - change L5DIA.DIVO_SCR with 5520; clear - HSCR; lia.
      - exact WAV.
      - exact WOUT.
      - intros a _ rr []. }
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHn) as WFn.
    assert (NDn : NoDup (map fst ((LBx ++ LBq) ++ LB))). { clear - WFn. decompose [and] WFn. assumption. }
    destruct WFn as (WBn & _).
    assert (LBXC : LBx = [] \/ exists q', LBx = [(q', 64)]). { destruct (L5.bo_st bx) as [v0' v1'|cap' q']. left; exact STX. right. exists q'. exact (proj1 (proj2 STX)). }
    set (blk := match L5.bo_st bq with L5.BInl _ _ => None | L5.BDyn cap q => Some (q, 8 * cap) end).
    assert (BLK : match blk with None => LBx = LBx ++ LBq | Some (q, n) => In (q, n) ((LBx ++ LBq) ++ LB) /\ lb_remove q ((LBx ++ LBq) ++ LB) = LBx ++ LB end).
    { subst blk. destruct (L5.bo_st bq) as [t0 t1|capq qq]. rewrite STQ. symmetry. apply app_nil_r. destruct STQ as (ELQ & _). subst LBq.
      split. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
      destruct LBXC as [-> | (q' & ->)]. cbn [app]. apply lb_remove_head.
      cbn [app]. rewrite lb_remove_skip. rewrite lb_remove_head. reflexivity.
      cbn [app map fst] in NDn. apply list_relations.list.NoDup_cons in NDn. destruct NDn as (NI & _). intros Eq. apply NI. subst q'. apply list_basics.list.elem_of_cons. left. reflexivity. }
    assert (QOB : qobj_at Mn (F + 32) bq blk) by (split; [exact OBQn | subst blk; destruct (L5.bo_st bq); reflexivity]).
    apply (dq_dtor fx2 R2 Mn modeln Wx (LBx ++ LBq) LBx LKn crn An bq blk BIn RIn QOB BLK).
    intros fx8 R8 M8 model8 A8 BI8 RI8 IA8 PRES8.
    apply (dq_tail fx8 R8 M8 model8 Wx LBx LKn crn A8 BI8 RI8).
    intros fxf Rf Mf modelf RPf R10f FRMf AHPf RTf AMf HHf.
    assert (NWR : forall a, (X <= a < X + 32 \/ dv <= a < dv + 32) -> ~ L5AFK.Wret F fl 1 a).
    { intros a Ha. assert (Hc : aclient L ar LB FF E SCRD a) by (destruct Ha as [Ha|Ha]; [apply CLX | apply CLD]; exact Ha).
      unfold L5AFK.Wret. change (ff_bytes 1 / 8) with 16. intros [[Wa|Wa]|Wa].
      - apply (NCF a). left; clear - Wa; lia. exact Hc.
      - apply (NCF a). right. apply SFR. exact Wa. exact Hc.
      - subst a. apply FLNC. destruct Ha as [Ha|Ha]. apply (obj_client L ar LB FF' 0 0 X 32 fl AOX' Ha). apply (obj_client L ar LB FF' 0 0 dv 32 fl AOD' Ha). }
    assert (KEEPO : forall a, (X <= a < X + 32 \/ dv <= a < dv + 32) -> Mf (Z_to_bv 64 a) = Mn (Z_to_bv 64 a)).
    { intros a Ha. assert (RGa : 0 <= a < 2 ^ 64) by (clear - Ha OR DR; lia). rewrite FRMf. apply PRES8. exact RGa.
      destruct Ha as [Ha|Ha]. apply (obj_client L ar (LBx ++ LB) FF' SPA OPDEL_SCR X 32 a AOX' Ha). apply (obj_client L ar (LBx ++ LB) FF' SPA OPDEL_SCR dv 32 a AOD' Ha). exact RGa. apply NWR. exact Ha. }
    assert (KEEPB : forall q n a, In (q, n) (LBx ++ LB) -> q <= a < q + n -> Mf (Z_to_bv 64 a) = Mn (Z_to_bv 64 a)).
    { intros q n a Hin Ha.
      assert (Hin' : In (q, n) ((LBx ++ LBq) ++ LB)). { apply in_app_or in Hin. destruct Hin as [Hin|Hin]. apply in_or_app. left. apply in_or_app. left. exact Hin. apply in_or_app. right. exact Hin. }
      destruct (WBn _ Hin') as ((Q0 & _ & _ & _ & QCE & (_ & QAPP & Q47)) & _ & _ & _ & _ & QFA & QFS). cbn [fst snd] in *.
      assert (RGa : 0 <= a < 2 ^ 64) by (clear - Ha Q0 Q47; lia). rewrite FRMf. apply PRES8. exact RGa.
      apply (block_client L ar (LBx ++ LB) FF' SPA OPDEL_SCR q n a Hin Ha). exact RGa.
      unfold L5AFK.Wret. change (ff_bytes 1 / 8) with 16. specialize (QFA (F, 1, SPA + 32) ltac:(apply in_or_app; left; left; reflexivity)). cbn [ff_addr ff_class fst snd] in QFA. change (ff_bytes 1) with 128 in QFA.
      unfold BIGSHADOW_LO, BIGSHADOW_HI in QAPP. intros [[Wa|Wa]|Wa]. clear - Wa Ha QFA; lia. unfold SB in Wa. clear - Wa Ha QAPP FSH4; lia. subst a. clear - Ha QFS FLP. unfold FS_BYTES in *. lia. }
    apply (KN fxf Rf Mf modelf (LBx ++ LB) crn LKn A8).
    + exact RPf.
    + rewrite r10. exact R10f.
    + exists bx, wx. split. { eapply L5C.big_at_agree. 4: exact OBXn. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply KEEPO. left; exact Hj. }
      split. { destruct OLXn as (L1 & L2 & L3). split. exact L1. split. exact L2. destruct (L5.bo_st bx) as [v0' v1'|cap' q'] eqn:ESX'. exact L3.
               pose proof OBXn as (_ & _ & _ & STn). rewrite ESX' in STn. destruct STn as (_ & _ & _ & LCn & CRRn & _ & Q4096 & Q47 & _).
               destruct STX as (EC & ELX & _). subst LBx cap'.
               eapply (L5C.limbs_at_agree RSEGS Mn Mf). 4: exact L3. 2: clear - Q4096; lia. 2:{ rewrite L1. clear - Q47 LCn CRRn. lia. }
               intros j Hj. rewrite L1 in Hj. apply (KEEPB q' 64 j ltac:(left; reflexivity)). clear - Hj LCn. lia. }
      split. exact NEGX.
      destruct (L5.bo_st bx) as [v0' v1'|cap' q']. rewrite STX. reflexivity.
      destruct STX as (EC & ELX & _). subst LBx. split. exact EC. split. reflexivity. cbn [app] in HHf. exact (L5ADH.afresh_of_inv L ar C HI HIok q' 64 LB FF LKn crn A8 Mf (vml_of modelf) HHf).
    + eapply L5C.big_at_agree. 4: exact OBBn. 2: clear - DR; lia. 2: clear - DR; lia. intros j Hj. apply KEEPO. right; exact Hj.
    + destruct OLBn as (L1 & L2 & L3). split. exact L1. split. exact L2. destruct (L5.bo_st bb) as [v0' v1'|capb qb] eqn:ESB. exact L3.
      pose proof OBBn as (_ & _ & _ & STn). rewrite ESB in STn. destruct STn as (_ & _ & _ & LCn & CRRn & _ & Q4096 & Q47 & _).
      eapply (L5C.limbs_at_agree RSEGS Mn Mf). 4: exact L3. 2: clear - Q4096; lia. 2:{ rewrite L1. clear - Q47 LCn CRRn. lia. }
      intros j Hj. rewrite L1 in Hj. apply (KEEPB qb (8 * capb) j ltac:(apply in_or_app; right; exact INB)). clear - Hj LCn. lia.
    + exact LB1.
    + exact CRn.
    + exact AHPf.
    + exact RTf.
    + intros x Hx. apply IA8. apply IAn. exact Hx.
    + exact AMf.
    + intros x Hx. apply LKI2. apply ILKn. exact Hx.
    + exact HHf.
  - (* [comment removed for export] *)
    intros fx3 R3' M3' model3' LK3 A3 F3 fl3 L0 E2A RT3 IA3 AM3 ILK3 HH3.
    replace (E - 96 - 320) with (E - 416) in HH3 by (clear; lia). replace (E - 96 + 32) with (E - 64) in HH3 by (clear; lia).
    destruct E2A as (fden & v16 & v24 & e2 & e3 & e4 & e10 & e8 & e9 & e18 & e19 & e20 & e21 & e22 & e23 & e24 & e25 & e26 & e27 & DSV & s56 & s72 & s160 & s88 & s96 & s112 & s152 & OBDN & SHD & FRL3 & AHP3).
    destruct (THROWK M3' [] [] _ _ _ _ _ _ AHP3 HH3 ltac:(right; left; reflexivity) ltac:(intros a _ O; exact O) ltac:(intros a _ rr [])) as (QOWN3 & SHO3 & FRL1 & AHPE).
    apply (KE2 fx3 R3' M3' model3' LK3 A3 F3 fl3).
    2:{ eapply L5LZ.model_rt_trans. exact B3. eapply L5LZ.model_rt_trans. exact RT1. exact RT3. }
    2:{ intros x Hx. apply IA3. apply B4. exact Hx. }
    2: exact AM3.
    2:{ intros x Hx. apply B5. apply ILK3. exact Hx. }
    2: exact HH3.
    destruct UV as (u1 & u8 & u9 & u18 & u19 & u20 & u21 & u22 & u23 & u24 & u25 & u26 & u27).
    destruct DSV as (d1 & d8 & d9 & d18 & d19 & d20 & d21 & d22 & d23 & d24 & d25 & d26 & d27).
    rewrite u1 in d1. rewrite u8 in d8. rewrite u9 in d9. rewrite u18 in d18. rewrite u19 in d19. rewrite u20 in d20. rewrite u21 in d21. rewrite u22 in d22. rewrite u23 in d23. rewrite u24 in d24. rewrite u25 in d25. rewrite u26 in d26. rewrite u27 in d27.
    exists fden, v16, v24.
    split. { unfold L5DSA.zero_throw_regs. replace (E - 448) with (E - 96 - 352) by (clear; lia).
             split. exact e2. split. rewrite e3. rewrite r3q. exact Z3. split. rewrite e4. rewrite r4. exact Z4. split. exact e10. split. exact e8. split. exact e9.
             split. exact e18. split. exact e19. split. exact e20. split. exact e21. split. exact e22. split. exact e23. split. exact e24.
             split. rewrite e25. rewrite r25q. exact Z25. split. exact e26. exact e27. }
    split. exact QOWN3.
    split. { unfold L5DSA.divO_saves.
             replace (E - 104) with (E - 96 - 8) by (clear; lia). replace (E - 112) with (E - 96 - 16) by (clear; lia). replace (E - 120) with (E - 96 - 24) by (clear; lia). replace (E - 128) with (E - 96 - 32) by (clear; lia).
             replace (E - 136) with (E - 96 - 40) by (clear; lia). replace (E - 144) with (E - 96 - 48) by (clear; lia). replace (E - 152) with (E - 96 - 56) by (clear; lia). replace (E - 160) with (E - 96 - 64) by (clear; lia).
             replace (E - 168) with (E - 96 - 72) by (clear; lia). replace (E - 176) with (E - 96 - 80) by (clear; lia). replace (E - 184) with (E - 96 - 88) by (clear; lia). replace (E - 192) with (E - 96 - 96) by (clear; lia).
             replace (E - 200) with (E - 96 - 104) by (clear; lia).
             split. exact d1. split. exact d8. split. exact d9. split. exact d18. split. exact d19. split. exact d20. split. exact d21. split. exact d22. split. exact d23. split. exact d24. split. exact d25. split. exact d26. exact d27. }
    replace (E - 392) with (E - 96 - 296) by (clear; lia). replace (E - 376) with (E - 96 - 280) by (clear; lia). replace (E - 288) with (E - 96 - 192) by (clear; lia).
    replace (E - 360) with (E - 96 - 264) by (clear; lia). replace (E - 352) with (E - 96 - 256) by (clear; lia). replace (E - 336) with (E - 96 - 240) by (clear; lia). replace (E - 296) with (E - 96 - 200) by (clear; lia).
    split. exact s56. split. exact s72. split. exact s160. split. exact s88. split. exact s96. split. exact s112. split. exact s152.
    split. { eapply L5C.big_at_agree. 4: exact ZT6. 2: clear - FRP; lia. 2: clear - FRP; lia. intros j Hj. apply (proj1 AHP3). split. clear - Hj FRP; lia. split.
             apply (fframe_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Hj; lia. intros rr []. }
    split. exact OBDN.
    destruct SHO3 as (o0 & o4 & o8 & o12). split. exact o0. split. exact o4. split. exact o8. split. exact o12.
    destruct SHD as (h0 & h4 & h8 & h12 & h16 & h20 & h24 & h28 & h32 & h36 & h40 & h44 & h48 & h52).
    split. exact h0. split. exact h4. split. exact h8. split. exact h12. split. exact h16. split. exact h20. split. exact h24. split. exact h28. split. exact h32. split. exact h36. split. exact h40. split. exact h44. split. exact h48. split. exact h52.
    split. { replace (E - 416) with (E - 96 - 320) by (clear; lia). replace (E - 64) with (E - 96 + 32) by (clear; lia). exact FRL3. }
    split. exact FRL1. exact AHPE.
  - (* [comment removed for export] *)
    intros fx3 R3' M3' model3' LB3 cr3 LK3 A3 F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx E3A RT3 IA3 AM3 ILK3 HH3.
    replace (E - 96 + 32) with (E - 64) in HH3 by (clear; lia).
    assert (AHP3 : ahpres L ar ([] ++ LB) FF' SPA L5DIA.DIVO_SCR [(X, 32); (F + 32, 32)] M6 M3').
    { destruct E3A as (RU & MU & d3 & d4 & lenX & LBm & crm & fbx0 & fd0 & fn0 & fn & fden & v0 & v1 & v2 & v3 & nd0 & nn0 & nn & nd & bq & E3C). clear - E3C. decompose [and] E3C. assumption. }
    destruct (THROWK M3' [(X, 32); (F + 32, 32)] [(X, 32)] _ _ _ _ _ _ AHP3 HH3) as (QOWN3 & SHO3 & FRL1 & AHPE).
    { unfold L5DIA.ff_o, L5DIA.ff_u, L5DIA.ff_q, L5DIA.ff_n, L5DIA.ff_rz. do 5 right. left. reflexivity. }
    { exact WOUT. }
    { intros a Ha rr [<-|[<-|[]]] IR; unfold L5.in_rng in IR; cbn [fst snd] in IR.
      - destruct Ha as [Ha|[Ha|Ha]]. apply (NCS a). exact Ha. apply CLX. exact IR. apply (NCF a). left. clear - Ha; lia. apply CLX. exact IR. apply (NCF a). right. apply SFR. exact Ha. apply CLX. exact IR.
      - destruct Ha as [Ha|[Ha|Ha]]. clear - Ha IR SFB; lia. clear - Ha IR; lia. unfold SB in Ha. clear - Ha IR FSH4 FBIG FRP. lia. }
    apply (KE3 fx3 R3' M3' model3' LB3 cr3 LK3 A3 F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx).
    2:{ eapply L5LZ.model_rt_trans. exact B3. eapply L5LZ.model_rt_trans. exact RT1. exact RT3. }
    2:{ intros x Hx. apply IA3. apply B4. exact Hx. }
    2: exact AM3.
    2:{ intros x Hx. apply B5. apply ILK3. exact Hx. }
    2: exact HH3.
    exists R1, M6. split. exact UV. split. rewrite r3q. exact Z3. split. rewrite r4. exact Z4. split. exact E3A. split. exact QOWN3. split. exact SHO3. split. exact FRL1. exact AHPE.
Qed.
End O1.
End DQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCRo : Z := 73728.
Theorem opmod2A_ok : L5DIA.divO2_specA L ar HI -> L5OMA.opmod2A_spec L ar HI SCRo 6 0 4 L5DIA.DIVO2_K L5DIA.divO2_bytes.
Proof.
  intros HdivO2 fx R M model K LB FF LK cr A yo ao E r fba by_ wy capy HH AM HK G10 G11 G1 RA G2 A32 G4 STK SSH FFR1 FFR2 FFR3 FFRS IMG YOK AOY SZY LY1 CAPY AOK AOA SZA APYA CRF KN. subst capy.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold SCRo in SLO.
  assert (ER : 140735332487680 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - SLO SHI SPT; lia). destruct ER as (ER & ERG).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model yo 32 E SCRo HH AOY ltac:(clear; lia) ltac:(reflexivity)) as (OR & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model ao 32 E SCRo HH AOA ltac:(clear; lia) ltac:(reflexivity)) as (DR & _).
  assert (XR : 0 <= yo < 2 ^ 64) by (clear - OR; lia). assert (DVR : 0 <= ao < 2 ^ 64) by (clear - DR; lia).
  apply (dq_entry L ar C HI LY HIok SCRo fx R M model K LB FF LK cr A yo ao E r ltac:(vm_compute; discriminate) HH AM HK G10 G11 XR DVR G1 RA G2 A32 G4 STK (ffrk_le 1 FF LK 6 5 FFR1 ltac:(clear; lia)) FFRS).
  intros F fl LK2 M2 model2 fx3 R3 M3 model3 G UR1 G2' G4' BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3.
  eapply om2_rest with (X := yo) (dv := ao) (fba := fba) (by_ := by_) (wy := wy); try first [exact G | exact ER | exact A32 | exact HK | exact RA | exact UR1 | exact G2' | exact G4' | exact XR | exact DVR | exact FFR1 | exact FFR3 | exact FFRS | exact HH | exact HdivO2];
    [vm_compute; discriminate | exact BI3 | exact RI3 | exact X1 | exact X101112 | exact QSH3 | exact SZT3 | exact T03 | exact HD3 | exact YOK | exact AOY | exact SZY | exact LY1 | exact CAPY | exact AOK | exact AOA | exact SZA | exact APYA
     | exact SSH | reflexivity | exact CRF | ].
  intros fx' R' M' model' LB' cr' LK' A' RP R10 YA AK' CRA AHP RT IA AM' ILK HH'.
  exact (KN fx' R' M' model' LB' cr' LK' A' RP R10 YA AK' CRA AHP RT IA AM' ILK HH').
Qed.

(* [comment removed for export] *)
Definition om1_e3_arm : Prop :=
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (xo bo E r fbx : Z) (bb : L5.bigobj) (wb : list Z) (st : L5USA.XS) (F fl : Z)
         (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
         (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 1%bv = Z_to_bv 64 r -> r = 0x8e080 -> getr R 9%bv = Z_to_bv 64 E -> getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E SCRo ->
    getr R 3%bv = Z_to_bv 64 67584 -> L5OMA.stksh ar M (E - SCRo) -> ffrs FF E ->
    L5OMA.x_is_a M xo fbx -> aobj FF xo 32 -> shadow_zero M xo 4 -> L5OMA.b_ok LB M bo bb wb -> aobj FF bo 32 -> shadow_zero M bo 4 -> (xo + 32 <= bo \/ bo + 32 <= xo) ->
    L5OMA.acredit_for L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) -> L5USA.xs_pre ar st M ->
    om1_e3A R M LB FF E SCRo F fl xo bo cr M' R' F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx LB' cr' ->
    model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
    ri_inv HI LB' (L5DIA.ff_o ((F, 1, E - 64) :: FF) (E - 96) F3a F1b F3b F1c F1d) LK' cr' A' M' (vml_of model') ->
    (forall (fx'' : FPState) (R'' : bvmap 5 word) (M'' : word -> option byte) (model'' : Model) LB'' cr'' (LK'' : list fframe) (A'' : list (Z * Z)) fbx' nx qx' cr1,
        regs_preserved R R'' ->
        L5.big_at RSEGS M'' xo (L5.BO fbx' nx (L5.BDyn 8 qx')) -> afresh L ar LB (FF ++ LK'') M'' qx' 64 ->
        L5OMA.acredit_after L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) cr1 ->
        L5USA.e3_landed L st ((qx', 64) :: LB) FF LK cr1 E M'' R'' LB'' cr'' LK'' ->
        L5.big_at RSEGS M'' bo bb -> L5C.obj_limbs RSEGS M'' bb wb ->
        ahpres L ar LB FF E SCRo ((xo, 32) :: L5USA.xs_foot) M M'' ->
        model_rt model model'' -> incl A A'' -> amodel_ok A'' model'' ->
        ri_inv HI LB'' FF LK'' cr'' A'' M'' (vml_of model'') ->
        srealizes RSEGS SCFG (cfg (fx:=fx'') R'' L5OMA.TOP_PAD M'' model'') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K.

Theorem opmod1A_ok : L5DIA.divO1_specA L ar HI -> L5USA.e2_chainA_spec L ar HI -> om1_e3_arm -> L5USA.as0_unw_layout L ->
  L5OMA.opmod1A_spec L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) SCRo 6 0 4 L5DIA.DIVO1_K L5DIA.divO1_bytes.
Proof.
  intros HdivO1 He2 He3 UNWL fx R M model K LB FF LK cr A xo bo E r fbx bb wb st capb HH AM HK G10 G11 G1 RA RE G9 G2 A32 G4 STK G3 SSH FFR1 FFR2 FFR3 FFRS IMG XA AOX SZX BOK AOB SZB APXB CAPB DYN3 CRF XSP KN KE2 KE3. subst capb.
  pose proof (as0_layout2_of L C LY) as LY2.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold SCRo in SLO.
  assert (ER : 140735332487680 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - SLO SHI SPT; lia). destruct ER as (ER & ERG).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model xo 32 E SCRo HH AOX ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model bo 32 E SCRo HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (DR & DBIG & _).
  assert (XR : 0 <= xo < 2 ^ 64) by (clear - OR; lia). assert (DVR : 0 <= bo < 2 ^ 64) by (clear - DR; lia).
  apply (dq_entry L ar C HI LY HIok SCRo fx R M model K LB FF LK cr A xo bo E r ltac:(vm_compute; discriminate) HH AM HK G10 G11 XR DVR G1 RA G2 A32 G4 STK (ffrk_le 1 FF LK 6 5 FFR1 ltac:(clear; lia)) FFRS).
  intros F fl LK2 M2 model2 fx3 R3 M3 model3 G UR1 G2' G4' BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3.
  eapply om1_rest with (X := xo) (dv := bo) (fbx := fbx) (bb := bb) (wb := wb); try first [exact G | exact ER | exact A32 | exact HK | exact RA | exact UR1 | exact G2' | exact G4' | exact XR | exact DVR | exact FFR1 | exact FFR3 | exact FFRS | exact HH | exact HdivO1];
    [vm_compute; discriminate | exact BI3 | exact RI3 | exact X1 | exact X101112 | exact QSH3 | exact SZT3 | exact T03 | exact HD3 | exact XA | exact AOX | exact SZX | exact BOK | exact AOB | exact SZB | exact APXB | exact CAPB | exact DYN3
     | exact SSH | reflexivity | exact CRF | | | ].
  - (* [comment removed for export] *) intros fx' R' M' model' LB' cr' LK' A' RP R10 XAF OBB' OLB' LB1 CRA AHP RT IA AM' ILK HH'.
    exact (KN fx' R' M' model' LB' cr' LK' A' RP R10 XAF OBB' OLB' LB1 CRA AHP RT IA AM' ILK HH').
  - (* [comment removed for export] *)
    intros fx' Rt Mt modelt LKt At F3 fl3 ZTA RTt IAt AMt ILKt HHt.
    assert (AHPE : ahpres L ar LB FF E SCRo [] M Mt). { destruct ZTA as (fden & v16 & v24 & ZC). clear - ZC. decompose [and] ZC. assumption. }
    assert (AGC : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF E SCRo a -> Mt (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros a Ha Hc. apply (proj1 AHPE). split. exact Ha. split. exact Hc. intros rr []. }
    assert (XSPt : L5USA.xs_pre ar st Mt).
    { eapply L5ATX.xs_pre_same; try first [exact LY | exact HIok | exact UNWL]. 2: exact XSP. intros a Hd.
      assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hd as [(X0 & _)|X0]; clear - X0 SPT; lia). apply AGC. exact Ha.
      destruct Hd as [(X0 & NS)|X0]. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. exact X0. exact NS.
      right; left. split. clear - X0 SLO SHI; lia. clear - X0 SHI; lia. }
    assert (STKt : astk ar Mt E SCRo). { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ LB FF M M Mt E SCRo E SCRo [] HH STK (mem_grows_refl M) AHPE). clear; lia. clear; lia. vm_compute; discriminate. }
    assert (TOP : ar_stack_top ar <= 2 ^ 47). { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF0. clear - WF0. decompose [and] WF0. assumption. }
    assert (FCE : 4096 <= ahl_ceil ar). { destruct G as [_ _ _ _ _ _ _ _ _ FCEIL _ _ _ _ _ FR _ _ _ _ _ _ _ _]. clear - FCEIL FR. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (SSHt : L5OMA.stksh ar Mt (E - SCRo)).
    { apply (stksh_sub M Mt (E - SCRo) (E - SCRo)). exact SSH. clear; lia. 3: unfold SCRo; clear - SLO; lia. 3: unfold SCRo; clear - SLO FCE; lia. 3: exact TOP. 3: clear - SPT; lia.
      1,2: (unfold SCRo; clear - A32; lia).
      intros a Ha Hs. apply AGC. exact Ha. right; right; right; right; left. exact Hs. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (He2 fx' R M Rt Mt modelt K LB FF LK LKt cr At E SCRo xo bo F fl F3 fl3 st ZTA).
    + rewrite G1, RE. reflexivity.
    + exact G2.
    + exact G3.
    + exact G4.
    + exact G9.
    + exact A32.
    + exact XSPt.
    + exact HHt.
    + exact AMt.
    + exact HK.
    + exact ILKt.
    + exact STKt.
    + vm_compute; discriminate.
    + reflexivity.
    + exact SSHt.
    + apply (L5OMA.acredit_for_le L cr L5DIA.DIVO1_K (L5DIA.divO1_bytes (L5.bo_cap bb)) 2 (L5USA.EXC23_SZ + L5USA.REF2_SZ) LY2 CRF). vm_compute; discriminate.
      assert (CP : 0 <= L5.bo_cap bb). { unfold L5.bo_cap. destruct BOK as (OBB & _). destruct OBB as (_ & _ & _ & ST). destruct (L5.bo_st bb). clear; lia. destruct ST as (_ & _ & _ & _ & CR0 & _). clear - CR0; lia. }
      unfold L5DIA.divO1_bytes, L5USA.EXC23_SZ, L5USA.REF2_SZ. clear - CP. lia.
    + intros fxl Rl Ml modell LBl crl LKl Al RPl LND AHPl RTl IAl AMl HHl.
      assert (AHL : ahpres L ar LB FF E SCRo L5USA.xs_foot M Ml).
      { destruct AHPl as (EKl & DFl & DKl). split. eapply ek_trans. eapply ek_W. exact (proj1 AHPE). intros a _ rr []. exact EKl. split. exact DFl. eapply dk_trans. exact (proj2 (proj2 AHPE)). exact DKl. }
      assert (FOOT : forall a, 0x633000 <= a \/ a < 0x10000 -> L5.outside L5USA.xs_foot a).
      { intros a Ha rr [<-|[<-|[]]] IR; unfold L5.in_rng, L5USA.EH_UNCAUGHT, L5USA.UW_FLAGS in IR; cbn [fst snd] in IR; clear - Ha IR; lia. }
      destruct XA as (OBXA & SGX). pose proof BOK as (OBB & OLB & REDB & INB).
      assert (TXo : L5ADVEA.tob LB M xo (L5.BO fbx 2 (L5.BInl L5PSA.A0 L5PSA.A1)) [L5PSA.A0; L5PSA.A1]).
      { split. exact OBXA. split. { destruct OBXA as (_ & _ & _ & (_ & _ & _ & _ & V0 & V1)). split. reflexivity. split. constructor; [exact V0 | constructor; [exact V1 | constructor]]. reflexivity. } split. exact SZX. intros cap q Eq. discriminate Eq. }
      assert (TBo : L5ADVEA.tob LB M bo bb wb). { split. exact OBB. split. exact OLB. split. exact SZB. intros cap q Eq. rewrite Eq in INB. exact INB. }
      assert (OFFF : forall o b ws, aobj FF o 32 -> L5ADVEA.tob LB M o b ws -> forall a, L5ADVEA.oreg o b a -> L5.outside L5USA.xs_foot a).
      { intros o b ws AO (OBo & _ & _ & INo) a ORa. apply FOOT.
        pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 E SCRo HH AO ltac:(clear; lia) ltac:(reflexivity)) as ((OLO & _ & OHI & _) & _).
        destruct ORa as [ORa|[ORa|(cap & q & Eq & ORa)]]. left; clear - ORa OLO; lia. left. unfold SB in ORa. clear - ORa OLO. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB _ (INo cap q Eq)) as ((Q0 & QIMG & _) & _). cbn [fst snd] in Q0, QIMG. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in QIMG. clear - ORa QIMG Q0. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct (L5ADVO1.arg_kept L ar C HI LY HIok M Ml model LB FF LK cr A E SCRo _ xo _ _ HH AHL AOX TXo (OFFF _ _ _ AOX TXo)) as (OBXl & _).
      destruct (L5ADVO1.arg_kept L ar C HI LY HIok M Ml model LB FF LK cr A E SCRo _ bo _ _ HH AHL AOB TBo (OFFF _ _ _ AOB TBo)) as (OBBl & OLBl).
      apply (KE2 fxl Rl Ml modell LBl crl LKl Al RPl LND (conj OBXl SGX) OBBl OLBl).
      * destruct AHL as (EKL & DFL & DKL). split. eapply ek_W. exact EKL. intros a O rr Hr. apply O. right. exact Hr. split. exact DFL. exact DKL.
      * eapply L5LZ.model_rt_trans. exact RTt. exact RTl.
      * intros x Hx. apply IAl. apply IAt. exact Hx.
      * exact AMl.
      * exact HHl.
  - (* [comment removed for export] *)
    intros fx' Rt Mt modelt LBt crt LKt At F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx E3A RTt IAt AMt ILKt HHt.
    apply (He3 R M model K LB FF LK cr A xo bo E r fbx bb wb st F fl fx' Rt Mt modelt LBt crt LKt At F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx HH AM HK G1 RE G9 G2 A32 G4 STK G3 SSH FFRS XA AOX SZX BOK AOB SZB APXB CRF XSP E3A RTt IAt AMt ILKt HHt).
    intros fx'' R'' M'' model'' LB'' cr'' LK'' A'' fbx' nx qx' cr1 RP OBX'' AFR CRA LND OBB'' OLB'' AHP'' RT'' IA'' AM'' HH''.
    exact (KE3 fx'' R'' M'' model'' LB'' cr'' LK'' A'' fbx' nx qx' cr1 RP OBX'' AFR CRA LND OBB'' OLB'' AHP'' RT'' IA'' AM'' HH'').
Qed.
End WithIface.
End SCFG_1.
End L5AOPMOD.
