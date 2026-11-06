(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BDetailK L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BDivQP L5BDivQH.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_94368_9505c.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADIVQ.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADIVQP. Import L5ADQH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Lemma DEL_EQ : OPDEL_SCR = 4096. Proof. reflexivity. Qed.
Lemma DIVN_EQ : L5DIA.DIVN_SCR = 5168. Proof. reflexivity. Qed.
Lemma DIVEQ_EQ : L5DIA.DIVEQ_SCR = 5264. Proof. reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis HdivN : L5DIA.divN_specA L ar HI.

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
Hypothesis HSCR : 96 + 5168 <= SCRD.
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
  L5.writable RSEGS MV (E - 96) 96 /\ L5.img_clear MV 860160 884736 /\ L5.u64_at RSEGS MV 911160 2147450880 /\ L5.u32_at RSEGS MV 911168 1 /\
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
  binv W BX Mc modelc LKc crc Ac -> rinvQ R E F X dv Rc -> getr Rc (reg 1) = Z_to_bv 64 0x94c20 ->
  getr Rc (reg 10) = Z_to_bv 64 (F + 40) /\ getr Rc (reg 11) = Z_to_bv 64 0 /\ getr Rc (reg 12) = Z_to_bv 64 24 ->
  qsh Mc F 0 -> shadow_zero Mc (F + 32) 4 -> L5.u8_at RSEGS Mc (F + 32) 0 -> L5.u64_at RSEGS Mc F 1102416563 ->
  (forall (fx6 : FPState) R6 M6 model6,
      binv W BX M6 model6 LKc crc Ac -> rinvQ R E F X dv R6 ->
      qsh M6 F 0 -> L5DIA.zero_obj M6 (F + 32) -> shadow_zero M6 (F + 32) 4 -> L5.u64_at RSEGS M6 F 1102416563 ->
      srealizes RSEGS SCFG (cfg (fx:=fx6) R6 0x94c20 M6 model6) K) ->
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
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x94c58 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x94c38 Mc modelc) K.
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
    pose proof (vdeP3i_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pEQ & _ & (pMS & pKS & _)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pEQ). rewrite EQM in pMS.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x94c38 R1 0x94c58 K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 Mc model1 Ac BI1). 2: apply incl_refl. 2: intros a _ _; reflexivity.
    apply (rinvQ_ks R E F X dv Rc R1 KS_vdeP3i RI pKS). vm_compute; reflexivity.
  - (* [comment removed for export] *)
    subst blk. destruct BLK as [INP ELB]. destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    pose proof (CELLV (F + 32 + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) as O24v. pose proof (CELLV (F + 32 + 16) cap ltac:(clear; lia) ltac:(clear; lia) O16) as O16v.
    replace (F + 32 + 24) with (F + 56) in O24v by (clear; lia). replace (F + 32 + 16) with (F + 48) in O16v by (clear; lia).
    assert (QR : 4096 <= q <= 140737488355328 /\ 0 <= q < 2 ^ 64 /\ 0 <= cap < 2 ^ 64) by (clear - Q4096 Q47 CAPR; lia). destruct QR as (QR & QRG & CAPG).
    pose proof (vdeP3d_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & MG1 & pEQ & _ & (pMS & pKS & dR1 & dR10 & dR11)).
    assert (EQM : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pEQ). rewrite EQM in pMS.
    apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x94c38 R1 OPDEL_SIZED K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    assert (RI1 : rinvQ R E F X dv R1). { apply (rinvQ_ks R E F X dv Rc R1 KS_vdeP3d RI pKS). vm_compute; reflexivity. }
    pose proof RI1 as (Z2 & _ & _ & _ & Z4 & _).
    assert (SPA16 : (E - 96) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (Hdel fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac q (8 * cap) SPA 0x94c58 HH1 AM1 HK INP).
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
  exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc 0x94c58 MV) (st fx9 R9 r M9v) /\ mem_grows MV M9v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ L5AFK.Wret F fl 1 a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.u8_at RSEGS M9v fl 0 /\ regs_preserved R R9 /\ getr R9 (reg 10) = Z_to_bv 64 X.
Proof.
  intros RI (W96 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv) OWNv.
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (Y2 & Y8 & Y9 & Y3 & Y4 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  destruct OWNv as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  pose proof (vdeP4_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 41%nat => fl
                | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 58%nat => U Rc 1 | _ => 0 end)) as P.
  cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eFL0 & _)).
  pose proof (ret_to fx9 R9 M9v 0x94d28 Bo0_code_94368_9505c.W_94d28 r Bo0_code_94368_9505c.F_94d28 eq_refl Bo0_code_94368_9505c.D_94d28
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
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x94c58 Mc modelc) K.
Proof.
  intros BI RI KF.
  pose proof (pfq_of_binv W BX Mc modelc LKc crc Ac BI) as PF.
  destruct (Gx W BX Mc modelc LKc crc Ac BI) as (_ & OWNv & _).
  destruct (dq_tail_run fx Rc _ RI PF OWNv) as (fx9 & R9 & M9v & MS9 & MG9 & FZ9 & FL9 & RP9 & R10).
  apply (L5AFK.retire_core L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac fx fx9 Rc 0x94c58 R9 r M9v K BI MS9 MG9 FZ9 FL9).
  intros Mf modelf FRMf AHf RTf AMf HHf. apply (KF fx9 R9 Mf modelf RP9 R10 FRMf AHf RTf AMf HHf).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma apart_of_client (P : Z -> Prop) x lx y ly : 0 < lx -> 0 < ly -> (forall a, x <= a < x + lx -> P a) -> (forall a, y <= a < y + ly -> ~ P a) -> x + lx <= y \/ y + ly <= x.
Proof.
  intros Hx Hy PX PY. destruct (Z_le_gt_dec (x + lx) y) as [A1|A1]. left; exact A1. destruct (Z_le_gt_dec (y + ly) x) as [A2|A2]. right; exact A2.
  exfalso. apply (PY (Z.max x y)). Lia.lia. apply PX. Lia.lia.
Qed.

Hypothesis FFR1 : ffrk 1 FF LK 5.
Hypothesis FFR3 : ffrk 3 FF LK 2.
Hypothesis FFRS : ffrs FF E.
Hypothesis ESCR : SCRD = L5DIA.DIVEQ_SCR.
Lemma r3q : (3%bv : bv 5) = reg 3. Proof. apply bv_eq. reflexivity. Qed.

Lemma dq_call (fx : FPState) Rc Mc modelc LKc crc Ac (bX : L5.bigobj) (wX : list Z) qX fdv :
  binv [] [] Mc modelc LKc crc Ac -> rinvQ R E F X dv Rc ->
  qsh Mc F 0 -> L5DIA.zero_obj Mc (F + 32) -> shadow_zero Mc (F + 32) 4 -> L5.u64_at RSEGS Mc F 1102416563 ->
  L5.big_at RSEGS Mc X bX -> L5C.obj_limbs RSEGS Mc bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
  Z.testbit (L5.bo_fb bX) 1 = false -> In (qX, 64) LB -> aobj FF X 32 -> shadow_zero Mc X 4 ->
  L5DIA.mword_obj Mc dv fdv -> L5DIA.stkobj ar E dv 32 -> L5.defined Mc dv 32 ->
  L5OMA.stksh ar Mc (E - 96 - L5DIA.DIVN_SCR) ->
  L5OMA.acredit_for L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) R' M' model' LK' cr' A' BX1 (bT : L5.bigobj),
      binv [(X, 32); (qX, 64)] BX1 M' model' LK' cr' A' -> rinvQ R E F X dv R' -> incl Ac A' -> incl LK' LKc ->
      qobj_at M' (F + 32) bT (match L5.bo_st bT with L5.BInl _ _ => None | L5.BDyn cap q => Some (q, 8 * cap) end) ->
      match L5.bo_st bT with L5.BInl _ _ => BX1 = [] | L5.BDyn cap q => BX1 = [(q, 8 * cap)] end ->
      (exists fbq nq wq, L5.big_at RSEGS M' X (L5.BO fbq nq (L5.BDyn 8 qX)) /\ L5C.obj_limbs RSEGS M' (L5.BO fbq nq (L5.BDyn 8 qX)) wq
                         /\ Z.testbit fbq 1 = false /\ (nq <= 6)%nat) ->
      L5DIA.mword_obj M' dv fdv -> L5OMA.acredit_after L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES cr' ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x94c38 M' model') K) ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) R' M' model' LB' cr' LK' A' (F3 fl3 F1c fl1c F1d fl1d : Z),
      L5DIA.diveq_e3A L ar LB FF crc M M' R R' X qX (L5.bo_len bX) dv E F fl F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' (L5DIA.ff_q FF E F F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x94c20 Mc modelc) K.
Proof.
  intros BI RI QSH ZT SZT HD OBX OLX ESTX LENX SGNX INQ AOX SZX MWD SKD DFD SSH CRD KN KE3.
  pose proof (pfq_of_binv [] [] Mc modelc LKc crc Ac BI) as (W96 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (Y2 & Y8 & Y9 & Y3 & Y4 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH4 : (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0 /\ 0 <= F / 8 /\ F / 8 + 16 <= 17592186044416 /\ F / 8 * 8 = F) by (clear - FRP ALF; unfold aligned in ALF; lia).
  assert (SA : (E - 96) mod 16 = 0 /\ (E - 96) mod 32 = 0). { clear - EA. unfold aligned in EA. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  pose proof (vdeP2_conc fx Rc MV (fun j => match j with 2%nat => E | 33%nat => X | 34%nat => dv | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pEQ & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR13 & pR14)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok ([] ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x94c20 R1 L5DSA.DIVIDE K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (qown E F R) F 1 [] [] Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  assert (RI1 : rinvQ R E F X dv R1). { apply (rinvQ_ks R E F X dv Rc R1 KS_vdeP2 RI pKS). vm_compute; reflexivity. }
  pose proof RI1 as (Z2 & Z8 & Z9 & Z3 & Z4 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
  (* [comment removed for export] *)
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF.
  assert (ND : NoDup (map ff_addr (FF' ++ LKc))). { clear - WF. decompose [and] WF. assumption. }
  assert (STKc : astk ar Mc SPA L5DIA.DIVN_SCR). { apply (astk_sub ar Mc Mc E SCRD 96 L5DIA.DIVN_SCR B6 (mem_grows_refl Mc)). clear; lia. rewrite DIVN_EQ; clear; lia. rewrite DIVN_EQ; clear - HSCR; lia. exact (proj1 SA). }
  assert (ROOM1 : ffrk 1 FF' LKc 4). { apply (ffrk_push 1 FF LK LKc (F, 1, SPA + 32) 5 4 FFR1 B5 ND). clear; lia. }
  assert (ROOM3 : ffrk 3 FF' LKc 2). { apply (ffrk_push_other 3 FF LK LKc (F, 1, SPA + 32) 2). cbn [ff_class fst snd]. clear; lia. exact FFR3. exact B5. exact ND. }
  assert (RSc : ffrs FF' SPA). { apply (ffrs_push FF E). exact FFRS. clear; lia. clear; lia. }
  assert (CLX : forall a, X <= a < X + 32 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (obj_client L ar LB FF E SCRD X 32 a AOX Ha)).
  assert (CLQ : forall a, qX <= a < qX + 64 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (block_client L ar LB FF E SCRD qX 64 a INQ Ha)).
  assert (XF : X + 32 <= F \/ F + 128 <= X). { apply (apart_of_client (aclient L ar LB FF E SCRD) X 32 F 128 ltac:(clear; lia) ltac:(clear; lia) CLX). intros a Ha. apply NCF. left. exact Ha. }
  assert (SFR : forall a, F / 8 + SB <= a < F / 8 + SB + 16 -> S F <= a <= S (F + 128 - 1)). { intros a Ha. unfold S. rewrite (proj1 (proj2 F8)). clear - Ha. unfold SB in *. lia. }
  assert (WAV : forall rr a, In rr [(X, 32); (qX, 64); (F + 32, 32)] -> L5.in_rng rr a -> ~ qocell E a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 16)).
  { intros rr a [Hr|[Hr|[Hr|[]]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
    - split. intros D. apply (NCS a). unfold qocell in D. clear - D; lia. apply CLX. exact IR. intros D. apply (NCF a). right. apply SFR. exact D. apply CLX. exact IR.
    - split. intros D. apply (NCS a). unfold qocell in D. clear - D; lia. apply CLQ. exact IR. intros D. apply (NCF a). right. apply SFR. exact D. apply CLQ. exact IR.
    - split. unfold qocell. clear - IR SFB; lia. unfold SB. clear - IR FSH4 FBIG FRP. lia. }
  assert (WOUT : forall a, aclient L ar LB FF E SCRD a -> L5.outside [(X, 32); (qX, 64)] a -> L5.outside [(X, 32); (qX, 64); (F + 32, 32)] a).
  { intros a Hc Ho rr [Hr|[Hr|[Hr|[]]]] IR. apply (Ho rr). left; exact Hr. exact IR. apply (Ho rr). right; left; exact Hr. exact IR.
    subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. apply (NCF a). left. clear - IR; lia. exact Hc. }
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX).
  assert (AOT' : aobj FF' (F + 32) 32). { exists (F, 1, SPA + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 1) with 128. split. clear; lia. split. clear; lia. exact (proj1 (proj2 FSH4)). }
  apply (HdivN fx1 R1 Mc model1 K ([] ++ LB) FF' LKc crc Ac X qX (F + 32) dv fdv SPA 0x94c38 bX wX HH1 AM1 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - rewrite r12. exact pR12.
  - rewrite r13. exact pR13.
  - rewrite r14. exact pR14.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Z2.
  - exact (proj2 SA).
  - rewrite r4, Z4, <- G4. reflexivity.
  - exact STKc.
  - exact SSH.
  - exact ROOM1.
  - exact ROOM3.
  - exact RSc.
  - exact OBX.
  - exact OLX.
  - exact ESTX.
  - exact LENX.
  - exact SGNX.
  - exact INQ.
  - exact AOX'.
  - exact SZX.
  - exact MWD.
  - destruct SKD as (D1 & D2 & D3). split. clear - D1; lia. split. exact D2. exact D3.
  - exact DFD.
  - exact ZT.
  - exact AOT'.
  - exact SZT.
  - clear - XF; lia.
  - exact CRD.
  - (* [comment removed for export] *)
    intros fx2 R2 Mn modeln LBn crn LKn An POST RTn IAn AMn ILKn HHn.
    destruct POST as (RPn & XPOST & (fbr & nr & str & wr & OBT & OLT & STRC) & MWn & CRn & AHPn).
    assert (RIn : rinvQ R E F X dv R2) by (apply (rinvQ_pres R E F X dv R1 R2 RI1 RPn)).
    destruct str as [t0 t1|capT qT].
    + subst LBn.
      assert (BIn : binv [(X, 32); (qX, 64)] [] Mn modeln LKn crn An).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G
                 [] [(X, 32); (qX, 64)] [] [] [] Mc model1 LKc crc Ac Mn modeln LKn crn An L5DIA.DIVN_SCR [(X, 32); (qX, 64); (F + 32, 32)] BI1 AHPn HHn AMn RTn IAn ILKn).
        - rewrite DIVN_EQ; clear; lia.
        - rewrite DIVN_EQ; clear - HSCR; lia.
        - exact WAV.
        - exact WOUT.
        - intros a _ rr []. }
      apply (KN fx2 R2 Mn modeln LKn crn An [] (L5.BO fbr nr (L5.BInl t0 t1)) BIn RIn IAn ILKn). 2: reflexivity. 2: exact XPOST. 2: exact MWn. 2: exact CRn.
      split. exact OBT. reflexivity.
    + destruct STRC as (EC & ELB & FRSH). subst capT. subst LBn.
      assert (BIn : binv [(X, 32); (qX, 64)] [(qT, 64)] Mn modeln LKn crn An).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (qocell E) (qown E F R) F fl 1 LK2 M2 model2 cr2 G
                 [] [(X, 32); (qX, 64)] [] [] [(qT, 64)] Mc model1 LKc crc Ac Mn modeln LKn crn An L5DIA.DIVN_SCR [(X, 32); (qX, 64); (F + 32, 32)] BI1 AHPn HHn AMn RTn IAn ILKn).
        - rewrite DIVN_EQ; clear; lia.
        - rewrite DIVN_EQ; clear - HSCR; lia.
        - exact WAV.
        - exact WOUT.
        - intros a _ rr []. }
      apply (KN fx2 R2 Mn modeln LKn crn An [(qT, 64)] (L5.BO fbr nr (L5.BDyn 8 qT)) BIn RIn IAn ILKn). 2: reflexivity. 2: exact XPOST. 2: exact MWn. 2: exact CRn.
      split. exact OBT. reflexivity.
  - (* [comment removed for export] *)
    intros fx3 R3 M3 model3 LB3 cr3 LK3 A3 F3 fl3 F1c fl1c F1d fl1d E3A RT3 IA3 AM3 ILK3 HH3.
    pose proof E3A as (RZ & MZ & B0 & B1' & fd0 & fn0 & fn & fden & w1 & E3C).
    assert (AHP3 : ahpres L ar ([] ++ LB) FF' SPA L5DIA.DIVN_SCR [] Mc M3 /\ LB3 = (B0, 64) :: (B1', 64) :: ([] ++ LB)).
    { clear - E3C. decompose [and] E3C. split; assumption. }
    clear E3C. destruct AHP3 as [AHP3 ELB3].
    assert (KQ : forall a, 0 <= a < 2 ^ 64 -> aclient L ar ([] ++ LB) FF' SPA L5DIA.DIVN_SCR a -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha Hc. apply (proj1 AHP3). split. exact Ha. split. exact Hc. intros rr []. }
    assert (KF0 : forall a, F <= a < F + 120 -> ~ (F + 24 <= a < F + 32) -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha Hn. apply KQ. clear - Ha FRP; lia. apply (fframe_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ha Hn; lia. }
    assert (KSH : forall a, F / 8 + SB <= a < F / 8 + SB + 16 -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha. apply KQ. clear - Ha FSH4; unfold SB in Ha; lia. apply (fframe_shadow_client L ar _ _ _ _ F 1 (SPA + 32)). left; reflexivity. change (ff_bytes 1) with 128. apply SFR. exact Ha. }
    assert (KST : forall a, SPA <= a < E -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
    { intros a Ha. apply KQ. clear - Ha ER; lia. apply stack_client. clear - Ha SLO SPC SPT; lia. clear - Ha; lia. }
    replace (E - 96 + 32) with (E - 64) in E3A, HH3 by (clear; lia).
    apply (KE3 fx3 R3 M3 model3 LB3 cr3 LK3 A3 F3 fl3 F1c fl1c F1d fl1d).
    2:{ eapply L5LZ.model_rt_trans. exact B3. eapply L5LZ.model_rt_trans. exact RT1. exact RT3. }
    2:{ intros x Hx. apply IA3. apply B4. exact Hx. }
    2: exact AM3.
    2:{ intros x Hx. apply B5. apply ILK3. exact Hx. }
    2: exact HH3.
    exists R1, Mc.
    split. { unfold L5DSA.U. change (Z_to_bv 5 1) with (reg 1). rewrite pR1. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
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
    split. { unfold L5DSA.U. change (Z_to_bv 5 27) with (reg 27). rewrite Z27. reflexivity. }
    split. { rewrite r3q. exact Z3. }
    split. { rewrite r4. exact Z4. }
    split. exact E3A.
    split. { apply (qown_agree E F R Mc M3 ltac:(clear - ER; lia) ltac:(clear - ER; lia) B9). intros a Ha. apply KST. unfold qocell in Ha. clear - Ha; lia. }
    split. { unfold L5DIA.zero_obj. eapply L5C.big_at_agree. 4: exact ZT. 2: clear - FRP; lia. 2: clear - FRP; lia. intros j Hj. apply KF0. clear - Hj; lia. clear - Hj; lia. }
    assert (SHX : forall a v, F / 8 + SB <= a < F / 8 + SB + 16 -> L5.u8_at RSEGS Mc a v -> byte_at M3 a v).
    { intros a v Ha Hu. unfold byte_at. rewrite (KSH a Ha). apply (byte_of_u8 Mc a v Hu). right. clear - Ha FSH4; unfold SB in Ha; lia. clear - Ha FSH4; unfold SB in Ha; lia. }
    split. { destruct QSH as (Q0 & Q4 & Q8 & Q12). unfold L5DIA.sh_op, L5DSA.sh_run, S. unfold shr8 in Q0, Q4, Q8, Q12.
             split. intros j Hj. apply SHX. clear - Hj; lia. exact (Q0 j Hj).
             split. intros j Hj. apply SHX. clear - Hj; lia. exact (Q4 j Hj).
             split. intros j Hj. apply SHX. clear - Hj; lia. exact (Q8 j Hj).
             intros j Hj. apply SHX. clear - Hj; lia. exact (Q12 j Hj). }
    split. { apply L5DSA.FRL.
             - refine (proj1 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model3 F 1 _ _ fl HH2 HH3 (or_introl eq_refl) _ Hk FLC)).
               unfold L5DIA.ff_q, L5DIA.ff_n, L5DIA.ff_rz. right; right; right; left; reflexivity.
             - exact FLP.
             - subst LB3. replace (E - 96 + 32) with (E - 64) in FLNC by (clear; lia).
               apply (not_client_bx L ar ((F, 1, E - 64) :: FF) fl [(B0, 64); (B1', 64)] LB).
               apply (blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ [(B0, 64); (B1', 64)] LB HH3 eq_refl). exact FLP. exact FLBIG. exact FLNC.
             - exact FLA.
             - eapply L5C.u64_at_agree. 4: exact HD. 2: clear - FRP; lia. 2: clear - FRP; lia. intros j Hj. apply KF0. clear - Hj; lia. clear - Hj; lia. }
    rewrite <- ESCR. apply ahpres_of.
    + eapply ek_trans. exact B7. apply (ek_callee L ar LB [] FF [(F, 1, SPA + 32)] E SCRD SPA L5DIA.DIVN_SCR [] [] Mc M3 AHP3).
      rewrite DIVN_EQ; clear - HSCR; lia. clear; lia. intros a _ Ho. exact Ho.
    + assert (STK3 : astk ar M3 E SCRD).
      { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ ([] ++ LB) FF' Mc Mc M3 E SCRD SPA L5DIA.DIVN_SCR [] B1 B6 (mem_grows_refl Mc) AHP3).
        rewrite DIVN_EQ; clear - HSCR; lia. clear; lia. clear - HSCR; lia. }
      eapply astk_defined. exact STK3. clear; lia. clear; lia.
    + eapply dk_trans. exact B8. apply (dk_callee L ar LB [] FF [(F, 1, SPA + 32)] E SCRD SPA L5DIA.DIVN_SCR [] Mc M3 AHP3).
      rewrite DIVN_EQ; clear - HSCR; lia. clear; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis HH0 : ri_inv HI LB FF LK cr2 A M (vml_of model).

Lemma dq_rest (fx : FPState) R3 M3 model3 (bX : L5.bigobj) (wX : list Z) qX fdv :
  binv [] [] M3 model3 LK2 cr2 A -> rinvQ R E F X dv R3 -> getr R3 (reg 1) = Z_to_bv 64 0x94c20 ->
  getr R3 (reg 10) = Z_to_bv 64 (F + 40) /\ getr R3 (reg 11) = Z_to_bv 64 0 /\ getr R3 (reg 12) = Z_to_bv 64 24 ->
  qsh M3 F 0 -> shadow_zero M3 (F + 32) 4 -> L5.u8_at RSEGS M3 (F + 32) 0 -> L5.u64_at RSEGS M3 F 1102416563 ->
  L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
  Z.testbit (L5.bo_fb bX) 1 = false -> In (qX, 64) LB -> aobj FF X 32 -> shadow_zero M X 4 ->
  L5DIA.mword_obj M dv fdv -> L5DIA.stkobj ar E dv 32 -> L5.defined M dv 32 ->
  L5OMA.stksh ar M (E - L5DIA.DIVEQ_SCR) ->
  L5OMA.acredit_for L cr2 L5DIA.DIVN_K L5DIA.DIVN_BYTES ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
      L5DIA.diveq_postA L ar LB FF cr2 M M' R R' X qX dv fdv E cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  (forall (fx' : FPState) R' M' model' LB' cr' LK' A' (F3 fl3 F1c fl1c F1d fl1d : Z),
      L5DIA.diveq_e3A L ar LB FF cr2 M M' R R' X qX (L5.bo_len bX) dv E F fl F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB' (L5DIA.ff_q FF E F F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R3 AMEMSET M3 model3) K.
Proof.
  intros BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3 OBX OLX ESTX LENX SGNX INQ AOX SZX MWD SKD DFD SSH CRD KN KE3.
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr2 A M model X 32 E SCRD HH0 AOX ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & _ & _ & OCL & OCLSH). change (32 / 8) with 4 in OCLSH.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH0) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. }
  destruct WF0 as (WB & _).
  pose proof (proj1 (WB _ INQ)) as (Q0 & _ & _ & _ & Q4 & _). cbn [fst snd] in Q0, Q4.
  destruct SKD as (D1 & D2 & D3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FSH4 : 0 <= F / 8 /\ F / 8 + 16 <= 17592186044416) by (clear - FRP; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (CLX : forall a, X <= a < X + 32 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (obj_client L ar LB FF E SCRD X 32 a AOX Ha)).
  assert (CLQ : forall a, qX <= a < qX + 64 -> aclient L ar LB FF E SCRD a) by (intros a Ha; apply (block_client L ar LB FF E SCRD qX 64 a INQ Ha)).
  assert (CLD : forall a, dv <= a < dv + 32 -> aclient L ar LB FF E SCRD a). { intros a Ha. apply stack_client. clear - Ha D1 D2 SLO SPT SPC; lia. clear - Ha D1; lia. }
  assert (SFR : forall a, F / 8 + SB <= a < F / 8 + SB + 16 -> S F <= a <= S (F + 128 - 1)). { intros a Ha. unfold S. rewrite (proj1 (proj2 F8)). clear - Ha. unfold SB in *. lia. }
  (* [comment removed for export] *)
  apply (dq_memset fx R3 M3 model3 [] [] LK2 cr2 A BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3).
  intros fx6 R6 M6 model6 BI6 RI6 QSH6 ZT6 SZT6 HD6.
  pose proof BI6 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (EKX : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF E SCRD a -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc. apply B7. split. exact Ha. split. exact Hc. intros rr []. }
  (* [comment removed for export] *)
  assert (OBX6 : L5.big_at RSEGS M6 X bX). { eapply L5C.big_at_agree. 4: exact OBX. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply EKX. clear - Hj OR; lia. apply CLX. exact Hj. }
  assert (OLX6 : L5C.obj_limbs RSEGS M6 bX wX).
  { destruct OLX as (L1 & L2 & L3). split. exact L1. split. exact L2. rewrite ESTX in L3 |- *.
    eapply (L5C.limbs_at_agree RSEGS M M6). 4: exact L3. 2: clear - Q0; lia. 2:{ rewrite L1. clear - Q4 SPT LENX SLO SPC. lia. }
    intros j Hj. rewrite L1 in Hj. apply EKX. clear - Hj Q0 Q4 SPT SLO SPC LENX; lia. apply CLQ. clear - Hj LENX; lia. }
  assert (SZX6 : shadow_zero M6 X 4).
  { intros j Hj. unfold byte_at. unfold S. rewrite EKX. exact (SZX j Hj). clear - Hj OR; unfold SB; lia. apply OCLSH. exact Hj. }
  assert (MWD6 : L5DIA.mword_obj M6 dv fdv).
  { destruct MWD as [MW1 MW2]. split. 2: exact MW2. eapply L5C.big_at_agree. 4: exact MW1. 2: clear - D1 ER; lia. 2: clear - D2 SPT; lia. intros j Hj. apply EKX. clear - Hj D1 D2 SPT ER; lia. apply CLD. exact Hj. }
  assert (DFD6 : L5.defined M6 dv 32). { intros i Hi. apply B8. clear - Hi D1 D2 SPT ER; lia. apply CLD. clear - Hi; lia. apply DFD. exact Hi. }
  assert (SSH6 : L5OMA.stksh ar M6 (E - 96 - L5DIA.DIVN_SCR)).
  { replace (E - 96 - L5DIA.DIVN_SCR) with (E - L5DIA.DIVEQ_SCR) by (rewrite DIVN_EQ, DIVEQ_EQ; clear; lia).
    intros j Hj. unfold byte_at. unfold L5OMA.stksh, shadow_zero, byte_at in SSH.
    assert (HB : 0 <= S (E - L5DIA.DIVEQ_SCR) + j < 2 ^ 45 /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) (S (E - L5DIA.DIVEQ_SCR) + j)).
    { unfold in_shadow_of, S, SB. rewrite DIVEQ_EQ in Hj |- *. set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
      assert (MX : mx <= 2 ^ 47) by (subst mx; apply Z.max_lub; [clear - SPT; lia | exact TOP]).
      pose proof (Z.mul_div_le (E - 5264) 8 ltac:(clear; lia)) as D1'. pose proof (Z.mul_div_le (mx - (E - 5264)) 8 ltac:(clear; lia)) as D2'.
      assert (D0 : 0 <= (E - 5264) / 8) by (apply Z.div_pos; [clear - ER; lia | clear; lia]).
      assert (E1 : (ahl_ceil ar) / 8 <= (E - 5264) / 8) by (apply Z.div_le_mono; [clear; lia | clear - SLO HSCR ESCR; rewrite ESCR, DIVEQ_EQ in SLO; lia]).
      replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415.
      clear - Hj MX D1' D2' D0 E1. lia. }
    rewrite EKX. apply SSH. exact Hj. clear - HB; lia. right; right; right; right; left. exact (proj2 HB). }
  (* [comment removed for export] *)
  apply (dq_call fx6 R6 M6 model6 LK2 cr2 A bX wX qX fdv BI6 RI6 QSH6 ZT6 SZT6 HD6 OBX6 OLX6 ESTX LENX SGNX INQ AOX SZX6 MWD6 (conj D1 (conj D2 D3)) DFD6 SSH6 CRD). 2: exact KE3.
  intros fx7 R7 M7 model7 LK7 cr7 A7 BX1 bT BI7 RI7 IA7 ILK7 OBT7 BXT7 XPOST7 MWD7 CRD7.
  (* [comment removed for export] *)
  apply (dq_dtor fx7 R7 M7 model7 [(X, 32); (qX, 64)] BX1 [] LK7 cr7 A7 bT _ BI7 RI7 OBT7).
  { destruct (L5.bo_st bT) as [t0 t1|capT qT]. symmetry; exact BXT7. subst BX1. split. left; reflexivity. cbn [app]. apply lb_remove_head. }
  intros fx8 R8 M8 model8 A8 BI8 RI8 IA8 PRES8.
  (* [comment removed for export] *)
  apply (dq_tail fx8 R8 M8 model8 [(X, 32); (qX, 64)] [] LK7 cr7 A8 BI8 RI8).
  intros fxf Rf Mf modelf RPf R10f FRMf AHPf RTf AMf HHf.
  assert (AOX' : aobj FF' X 32) by (apply aobj_cons; exact AOX).
  assert (KEEPf : forall a, X <= a < X + 32 \/ qX <= a < qX + 64 \/ dv <= a < dv + 32 -> Mf (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha.
    assert (RGa : 0 <= a < 2 ^ 64) by (clear - Ha OR Q0 Q4 D1 D2 SPT SLO SPC ER; lia).
    assert (CL0 : aclient L ar LB FF E SCRD a \/ dv <= a < dv + 32). { destruct Ha as [Ha|[Ha|Ha]]. left; apply CLX; exact Ha. left; apply CLQ; exact Ha. right; exact Ha. }
    rewrite FRMf. apply PRES8. exact RGa.
    - destruct Ha as [Ha|[Ha|Ha]].
      + apply (obj_client L ar ([] ++ LB) FF' SPA OPDEL_SCR X 32 a AOX' Ha).
      + apply (block_client L ar ([] ++ LB) FF' SPA OPDEL_SCR qX 64 a INQ Ha).
      + apply stack_client. clear - Ha D1 D2 SLO SPT SPC; lia. clear - Ha D1; lia.
    - exact RGa.
    - unfold L5AFK.Wret. change (ff_bytes 1 / 8) with 16. intros [[Wa|Wa]|Wa].
      + destruct CL0 as [Hc|Hd]. apply (NCF a). left; clear - Wa; lia. exact Hc. clear - Wa Hd D1 SFB; lia.
      + destruct CL0 as [Hc|Hd]. apply (NCF a). right. apply SFR. exact Wa. exact Hc. clear - Wa Hd D1 FSH4 ER; unfold SB in Wa; lia.
      + subst a. destruct Ha as [Ha|[Ha|Ha]].
        * apply FLNC. apply (obj_client L ar LB FF' 0 0 X 32 fl AOX' Ha).
        * apply FLNC. apply (block_client L ar LB FF' 0 0 qX 64 fl INQ Ha).
        * clear - Ha D1 SFB; lia. }
  apply (KN fxf Rf Mf modelf cr7 LK7 A8).
  - split. exact RPf. split. rewrite r10. exact R10f.
    split. { destruct XPOST7 as (fbq & nq & wq & OBq & OLq & SGq & NQ). exists fbq, nq, wq.
             split. { eapply L5C.big_at_agree. 4: exact OBq. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply KEEPf. left; exact Hj. }
             split. 2:{ split. exact SGq. exact NQ. }
             destruct OLq as (L1 & L2 & L3). cbn [L5.bo_len L5.bo_st] in *. split. exact L1. split. exact L2.
             eapply (L5C.limbs_at_agree RSEGS M7 Mf). 4: exact L3. 2: clear - Q0; lia. 2:{ rewrite L1. clear - Q4 SPT NQ SLO SPC. lia. }
             intros j Hj. rewrite L1 in Hj. apply KEEPf. right; left. clear - Hj NQ; lia. }
    split. { destruct MWD7 as [MW1 MW2]. split. 2: exact MW2. eapply L5C.big_at_agree. 4: exact MW1. 2: clear - D1 ER; lia. 2: clear - D2 SPT; lia. intros j Hj. apply KEEPf. right; right; exact Hj. }
    split. exact CRD7. rewrite <- ESCR. exact AHPf.
  - exact RTf.
  - intros x Hx. apply IA8. apply IA7. exact Hx.
  - exact AMf.
  - intros x Hx. apply LKI2. apply ILK7. exact Hx.
  - exact HHf.
Qed.
End DQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem diveq_okA : L5DIA.diveq_specA L ar HI.
Proof.
  unfold L5DIA.diveq_specA.
  intros fx R M model K LB FF LK cr A X qX dv fdv E r bX wX HH AM HK G10 G11 G1 RA G2 A32 G4 STK SSH FFR1 FFR3 FFRS OBX OLX ESTX LENX SGNX INQ AOX SZX MWD SKD DFD CRD KN KE3.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite DIVEQ_EQ in SLO.
  assert (ER : 140735332487680 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - SLO SHI SPT; lia). destruct ER as (ER & ERG).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model X 32 E L5DIA.DIVEQ_SCR HH AOX ltac:(clear; lia) ltac:(reflexivity)) as (OR & _).
  assert (XR : 0 <= X < 2 ^ 64) by (clear - OR; lia).
  assert (DVR : 0 <= dv < 2 ^ 64). { destruct SKD as (D1 & D2 & _). clear - D1 D2 SPT ER; lia. }
  apply (dq_entry L ar C HI LY HIok L5DIA.DIVEQ_SCR fx R M model K LB FF LK cr A X dv E r ltac:(rewrite DIVEQ_EQ; clear; lia) HH AM HK G10 G11 XR DVR G1 RA G2 A32 G4 STK FFR1 FFRS).
  intros F fl LK2 M2 model2 fx3 R3 M3 model3 G UR1 G2' G4' BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3.
  apply (dq_rest R M model K LB FF LK A E L5DIA.DIVEQ_SCR F fl r X dv LK2 M2 model2 cr G ER A32 HK RA UR1 G2' G4' ltac:(rewrite DIVEQ_EQ; clear; lia) XR DVR FFR1 FFR3 FFRS eq_refl HH
           fx3 R3 M3 model3 bX wX qX fdv BI3 RI3 X1 X101112 QSH3 SZT3 T03 HD3 OBX OLX ESTX LENX SGNX INQ AOX SZX MWD SKD DFD SSH CRD KN
           (fun fx' R' M' model' LB' cr' LK' A' F3 fl3 F1c fl1c F1d fl1d => KE3 fx' R' M' model' LB' cr' LK' A' F fl F3 fl3 F1c fl1c F1d fl1d)).
Qed.
End WithIface.
End SCFG_1.
End L5ADIVQ.
