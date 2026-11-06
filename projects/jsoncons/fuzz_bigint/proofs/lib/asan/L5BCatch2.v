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
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0 L5BUnwK L5BCatchP2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ACA2.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5ACP2.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
(* [comment removed for export] *)
Local Ltac t64 AG H := eapply (L5C.u64_at_agree RSEGS); [apply AG; blia | blia | blia | exact H].
Local Ltac t32 AG H := eapply L5AUK.u32_at_agree; [apply AG; blia | blia | blia | exact H].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Hypothesis UNWL : L5USA.as0_unw_layout L.

Local Notation CW := [(L5USA.EH_CAUGHT, 8); (L5USA.EH_UNCAUGHT, 4)].
Lemma cw_img : forall r a, In r CW -> L5.in_rng r a -> 0x10000 <= a < 0x634000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Proof.
  intros r a Hr Ha.
  assert (X : 6360520 <= a < 6360532). { destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng, L5USA.EH_CAUGHT, L5USA.EH_UNCAUGHT in Ha; cbn [fst snd] in Ha; clear - Ha; lia. }
  split. clear - X; lia. apply (proj1 UNWL (L5USA.EH_CAUGHT, 12) a). unfold L5USA.UNW_STATICS; left; reflexivity. unfold L5USA.EH_CAUGHT; cbn [fst snd]. clear - X; lia.
Qed.
(* [comment removed for export] *)
Lemma eh_client LBx FFx spx scrx a : 6360520 <= a < 6360532 -> aclient L ar LBx FFx spx scrx a.
Proof.
  intros X. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. clear - X; lia.
  apply (proj1 UNWL (L5USA.EH_CAUGHT, 12) a). unfold L5USA.UNW_STATICS; left; reflexivity. unfold L5USA.EH_CAUGHT; cbn [fst snd]. clear - X; lia.
Qed.

Theorem catch2A_ok : L5USA.catch2A_spec L ar HI.
Proof.
  unfold L5USA.catch2A_spec, L5USA.catchA_spec.
  intros fx R M model K LB FF LK cr A obj ref Sp SCR HH AM HK G10 G2 G3 G4 G9 S32 S47 STK HSCR SCR8 SH EXC C0 U1 IC1 IC2 KONT.
  unfold L5USA.DTOR_SYSTEM_ERROR, L5USA.DTOR_RUNTIME_ERROR, L5USA.EXC1_SZ, L5USA.EXC23_SZ, L5USA.REF1_SZ, L5USA.REF2_SZ, L5USA.REF3_SZ in *.
  unfold L5USA.CATCH, L5USA.CATCH_RET in *. unfold L5USA.CATCH_SCR in HSCR. unfold L5USA.GP in G3. rewrite (proj2 (proj2 UNWL)) in G4. unfold L5USA.TPV in G4.
  unfold L5USA.EH_CAUGHT in C0. unfold L5USA.EH_UNCAUGHT in U1.
  destruct EXC as (EC & HC & AP & RC & DT & IMP & RCNT).
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (HS0 : 0 <= SCR) by (clear - HSCR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (ALS : (Sp - 512) mod 16 = 0 /\ (Sp - 512) mod 8 = 0 /\ (Sp - 48) mod 16 = 0 /\ (Sp - 32) mod 16 = 0) by (clear - S32; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct ALS as (ALS & ALS8 & AL48 & AL32).
  assert (SPR : 0 <= Sp - 512 < 2 ^ 64 /\ 140735332552704 <= Sp - 512 /\ Sp + 64 <= 140737488355328) by (clear - SLO SHI SPT HSCR S47; lia).
  destruct SPR as (SPR0 & SPLO & SPHI).
  (* [comment removed for export] *)
  pose proof (cinv_init L ar HI M model A LB FF Sp SCR CW [(ref, 37); (obj - 128, 144)] LK cr HH AM STK SH) as CI0.
  assert (InR : In (ref, 37) ([(ref, 37); (obj - 128, 144)] ++ LB)) by (left; reflexivity).
  assert (InO : In (obj - 128, 144) ([(ref, 37); (obj - 128, 144)] ++ LB)) by (right; left; reflexivity).
  pose proof (cv_blk L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0 ref 37 InR) as (BRr & WRv & DRv).
  pose proof (cv_blk L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0 (obj - 128) 144 InO) as (BRo & WOv & DOv).
  assert (NE : ref <> obj - 128).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF. do 10 apply proj2 in WF. destruct WF as (ND & _).
    cbn [map fst app] in ND. inversion ND as [|x0 l0 NI ND']. subst. intros E. apply NI. rewrite E. constructor. }
  assert (APRT : ref + 37 <= obj - 128 \/ obj - 128 + 144 <= ref).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB (ref, 37) InR) as (_ & _ & _ & _ & BA & _). cbn [fst snd] in BA.
    cbn [app lb_remove fst] in BA. rewrite Z.eqb_refl in BA. specialize (BA (obj - 128, 144) ltac:(left; reflexivity)). cbn [fst snd] in BA. clear - BA; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (ALO : obj mod 16 = 0 /\ obj mod 8 = 0 /\ ref mod 16 = 0) by (clear - BRo BRr; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct ALO as (ALO & ALO8 & ALR).
  assert (OBR : 0 <= obj < 2 ^ 64 /\ 0 <= ref < 2 ^ 64 /\ 4224 <= obj <= 140737488355328 /\ 4096 <= ref <= 140737488355328) by (clear - BRo BRr; lia).
  destruct OBR as (OBR0 & RFR0 & OBR & RFR).
  assert (WEC : forall Mx, L5.writable RSEGS Mx 6360520 8) by (intros Mx; apply (writable_img Mx L5USA.EH_CAUGHT 8 wseg_caught); unfold L5USA.EH_CAUGHT; clear; lia).
  assert (WEU : forall Mx, L5.writable RSEGS Mx 6360528 4) by (intros Mx; apply (writable_img Mx L5USA.EH_UNCAUGHT 4 wseg_uncaught); unfold L5USA.EH_UNCAUGHT; clear; lia).
  (* [comment removed for export] *)
  pose proof (cv_stack L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0 (Sp - 4096) 4096 ltac:(clear - HSCR; lia) ltac:(clear; lia) ltac:(clear; lia)) as (WS0 & DS0).
  pose proof (cv_stksh L ar C HI LY HIok M model A LB FF Sp SCR CW SCR8 _ _ _ _ _ _ CI0 (Sp - 512) 2147450432 512 ALS8 ltac:(unfold SB; clear - HSCR; lia) ltac:(unfold SB; clear - SHI; lia)) as ZS0.
  pose proof (cv_blksh L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0 (obj - 128) 144 obj 2147450864 18 InO ALO8 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) as ZO0.
  assert (CV0 : forall a n, (obj - 128 <= a /\ a + n <= obj - 128 + 144) \/ (ref <= a /\ a + n <= ref + 37) \/ (6360520 <= a /\ a + n <= 6360532) ->
                L5AUK.cvis ar LB [(ref, 37); (obj - 128, 144)] a n).
  { intros a n [X|[X|X]]. right; right. exists (obj - 128), 144. split. exact InO. exact X. right; right. exists ref, 37. split. exact InR. exact X.
    right; left. clear - X; lia. }
  set (MV := mrestrict (ahid A model) M) in *.
  assert (ECv : L5.u64_at RSEGS MV (obj - 32) 4849336966747728640) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0); [apply CV0; left; clear; lia | clear - OBR; lia | clear - OBR; lia | exact EC]).
  assert (HCv : L5.u32_at RSEGS MV (obj - 72) 0) by (apply (cv_u32 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0); [apply CV0; left; clear; lia | clear - OBR; lia | clear - OBR; lia | exact HC]).
  assert (APv : L5.u64_at RSEGS MV (obj - 40) obj) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0); [apply CV0; left; clear; lia | clear - OBR; lia | clear - OBR; lia | exact AP]).
  assert (C0v : L5.u64_at RSEGS MV 6360520 0) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0); [apply CV0; right; right; clear; lia | clear; lia | clear; lia | exact C0]).
  assert (U1v : L5.u32_at RSEGS MV 6360528 1) by (apply (cv_u32 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI0); [apply CV0; right; right; clear; lia | clear; lia | clear; lia | exact U1]).
  assert (I1v : L5.img_clear MV 65536 884736) by (apply img_clear_mrestrict; exact IC1).
  assert (I2v : L5.img_clear MV 895824 895856) by (apply img_clear_mrestrict; exact IC2).
  pose proof (WEC MV) as WECv. pose proof (WEU MV) as WEUv.
  pose proof (ue2b1_conc HFILL HCOPY HTLS fx R MV (fun j => match j with 2%nat => Sp - 512 | 10%nat => obj | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(sc).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & (MS1 & KS1 & bR1 & bR10 & bR11 & bR12 & bR13 & bR14 & bU0 & bC0 & bNX & bHC & _ & _)).
  set (W1 := fun a => Sp - 96 <= a < Sp \/ obj - 80 <= a < obj - 68 \/ 6360520 <= a < 6360528 \/ 6360528 <= a < 6360532).
  apply (cinv_piece L ar C HI LY HIok M model A LB FF Sp SCR CW cw_img _ _ _ _ _ _ fx fx1 R 0x8e644 R1 0x8e648 M1v W1 K CI0 HS0 MS1 MG1).
  { intros a Ha Hna. apply FZ1. exact Ha. all: clear - Hna; subst W1; cbn beta in Hna; lia. }
  { intros a Wa. subst W1; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa|Wa]]].
    - left. clear - Wa HSCR; lia.
    - right; left. exists (obj - 128, 144). split. right; left; reflexivity. cbn [fst snd]. clear - Wa; lia.
    - right; right. exists (L5USA.EH_CAUGHT, 8). split. left; reflexivity. unfold L5.in_rng, L5USA.EH_CAUGHT; cbn [fst snd]. clear - Wa; lia.
    - right; right. exists (L5USA.EH_UNCAUGHT, 4). split. right; left; reflexivity. unfold L5.in_rng, L5USA.EH_UNCAUGHT; cbn [fst snd]. clear - Wa; lia. }
  intros M1 model1 CI1 AH1 VIS1 FRM1. subst M1v.
  assert (AG1 : forall a k, (a + k <= Sp - 96 \/ Sp <= a) -> (a + k <= obj - 80 \/ obj - 68 <= a) -> (a + k <= 6360520 \/ 6360532 <= a) ->
                0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k E1 E2 E3 Ha Hk i Hi. apply FRM1. clear - Ha Hk Hi; lia. subst W1; cbn beta. clear - E1 E2 E3 Hi. lia. }
  (* [comment removed for export] *)
  pose proof (cv_blk L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1 ref 37 InR) as (_ & WRv1 & DRv1).
  pose proof (cv_blk L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1 (obj - 128) 144 InO) as (_ & WOv1 & DOv1).
  pose proof (cv_stack L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1 (Sp - 4096) 4096 ltac:(clear - HSCR; lia) ltac:(clear; lia) ltac:(clear; lia)) as (WS1 & DS1).
  pose proof (cv_stksh L ar C HI LY HIok M model A LB FF Sp SCR CW SCR8 _ _ _ _ _ _ CI1 (Sp - 512) 2147450432 512 ALS8 ltac:(unfold SB; clear - HSCR; lia) ltac:(unfold SB; clear - SHI; lia)) as ZS1.
  pose proof (cv_blksh L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1 (obj - 128) 144 obj 2147450864 18 InO ALO8 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) as ZO1.
  set (MV1 := mrestrict (ahid A model1) M1) in *.
  assert (EC1 : L5.u64_at RSEGS M1 (obj - 32) 4849336966747728640) by (t64 AG1 EC).
  assert (RC1 : L5.u64_at RSEGS M1 (obj - 120) 1) by (t64 AG1 RC).
  assert (DT1 : L5.u64_at RSEGS M1 (obj - 104) 721816) by (t64 AG1 DT).
  assert (IMP1 : L5.u64_at RSEGS M1 (obj + 8) (ref + 24)) by (t64 AG1 IMP).
  assert (RCNT1 : L5.u32_at RSEGS M1 (ref + 16) 0) by (t32 AG1 RCNT).
  assert (EC1v : L5.u64_at RSEGS MV1 (obj - 32) 4849336966747728640) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1); [apply CV0; left; clear; lia | clear - OBR; lia | clear - OBR; lia | exact EC1]).
  assert (RC1v : L5.u64_at RSEGS MV1 (obj - 120) 1) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1); [apply CV0; left; clear; lia | clear - OBR; lia | clear - OBR; lia | exact RC1]).
  assert (DT1v : L5.u64_at RSEGS MV1 (obj - 104) 721816) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1); [apply CV0; left; clear; lia | clear - OBR; lia | clear - OBR; lia | exact DT1]).
  assert (IMP1v : L5.u64_at RSEGS MV1 (obj + 8) (ref + 24)) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1); [apply CV0; left; clear; lia | clear - OBR; lia | clear - OBR; lia | exact IMP1]).
  assert (RCNT1v : L5.u32_at RSEGS MV1 (ref + 16) 0) by (apply (cv_u32 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1); [apply CV0; right; left; clear; lia | clear - RFR; lia | clear - RFR; lia | exact RCNT1]).
  assert (J1 : L5.img_clear M1 65536 884736). { intros i Hi. rewrite FRM1. apply IC1. exact Hi. clear - Hi; lia. subst W1; cbn beta. clear - Hi BRo SLO SPT HSCR. lia. }
  assert (J2 : L5.img_clear M1 895824 895856). { intros i Hi. rewrite FRM1. apply IC2. exact Hi. clear - Hi; lia. subst W1; cbn beta. clear - Hi BRo SLO SPT HSCR. lia. }
  assert (J1v : L5.img_clear MV1 65536 884736) by (apply img_clear_mrestrict; exact J1).
  assert (J2v : L5.img_clear MV1 895824 895856) by (apply img_clear_mrestrict; exact J2).
  pose proof (WEC MV1) as WECv1.
  pose proof (ue2e1_conc HFILL HCOPY HTLS fx1 R1 MV1 (fun j => match j with 2%nat => Sp - 512 | 10%nat => obj | 37%nat => ref | 40%nat => obj | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(sc).
  destruct P as (fx2 & R2 & M2v & MG2 & _ & FZ2 & (MS2 & KS2 & eR1 & eR2 & eR8 & eR10 & eR11 & eR12 & eR13 & eS16 & eS8 & eRC & eVT & eC120 & eC0 & eHC & eS1 & eS0 & eRA & _)).
  set (W2 := fun a => Sp - 112 <= a < Sp \/ obj - 120 <= a < obj + 8 \/ ref + 16 <= a < ref + 20 \/ 6360520 <= a < 6360528).
  apply (cinv_piece L ar C HI LY HIok M model A LB FF Sp SCR CW cw_img _ _ _ _ _ _ fx1 fx2 R1 0x8e648 R2 0x5fed4 M2v W2 K CI1 HS0 MS2 MG2).
  { intros a Ha Hna. apply FZ2. exact Ha. all: clear - Hna; subst W2; cbn beta in Hna; lia. }
  { intros a Wa. subst W2; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa|Wa]]].
    - left. clear - Wa HSCR; lia.
    - right; left. exists (obj - 128, 144). split. right; left; reflexivity. cbn [fst snd]. clear - Wa; lia.
    - right; left. exists (ref, 37). split. left; reflexivity. cbn [fst snd]. clear - Wa; lia.
    - right; right. exists (L5USA.EH_CAUGHT, 8). split. left; reflexivity. unfold L5.in_rng, L5USA.EH_CAUGHT; cbn [fst snd]. clear - Wa; lia. }
  intros M2 model2 CI2 AH2 VIS2 FRM2. subst M2v.
  (* [comment removed for export] *)
  assert (SA : ahl_ceil ar <= Sp - 4096 /\ Sp <= 2 ^ 64) by (clear - SLO SPT SHI HSCR; lia).
  assert (eS16f : L5.u64_at RSEGS M2 (Sp - 48) (obj - 128)) by (apply (cu_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI2); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | gmem]).
  assert (eS8f : L5.u64_at RSEGS M2 (Sp - 40) 726088) by (apply (cu_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI2); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | gmem]).
  assert (eS1f : L5.u64_at RSEGS M2 (Sp - 24) (bv_unsigned (getr R1 (reg 9)))) by (apply (cu_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI2); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | gmem]).
  assert (eS0f : L5.u64_at RSEGS M2 (Sp - 16) (bv_unsigned (getr R1 (reg 8)))) by (apply (cu_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI2); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | gmem]).
  assert (eRAf : L5.u64_at RSEGS M2 (Sp - 8) 583244) by (apply (cu_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI2); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | gmem]).
  assert (eC0f : L5.u64_at RSEGS M2 6360520 0) by (apply (cu_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI2); [right; left; clear; lia | clear; lia | clear; lia | exact eC0]).
  assert (AG2 : forall a k, (a + k <= Sp - 112 \/ Sp <= a) -> (a + k <= obj - 120 \/ obj + 8 <= a) -> (a + k <= ref + 16 \/ ref + 20 <= a) -> (a + k <= 6360520 \/ 6360528 <= a) ->
                0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M1 M2 a k).
  { intros a k E1 E2 E3 E4 Ha Hk i Hi. apply FRM2. clear - Ha Hk Hi; lia. subst W2; cbn beta. clear - E1 E2 E3 E4 Hi. lia. }
  assert (bU0f1 : L5.u32_at RSEGS M1 6360528 0) by (apply (cu_u32 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI1); [right; left; clear; lia | clear; lia | clear; lia | exact bU0]).
  assert (bU0f : L5.u32_at RSEGS M2 6360528 0) by (t32 AG2 bU0f1).
  assert (K1 : L5.img_clear M2 65536 884736). { intros i Hi. rewrite FRM2. apply J1. exact Hi. clear - Hi; lia. subst W2; cbn beta. clear - Hi BRo BRr SLO SPT HSCR. lia. }
  assert (K2 : L5.img_clear M2 895824 895856). { intros i Hi. rewrite FRM2. apply J2. exact Hi. clear - Hi; lia. subst W2; cbn beta. clear - Hi BRo BRr SLO SPT HSCR. lia. }
  assert (E9 : bv_unsigned (getr R1 (reg 9)) = Sp).
  { rewrite (KS1 9%nat) by inl. replace (reg 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G9. apply L5.unsigned_lit. clear - SPR0 SPHI; lia. }
  rewrite E9 in eS1f.
  (* [comment removed for export] *)
  apply (cinv_free L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ fx2 R2 ref 37 (Sp - 48) 721884 K CI2 HK HS0).
  { left; reflexivity. }
  { exact eR10. }
  { exact eR1. }
  { split. clear; lia. reflexivity. }
  { rewrite eR2. f_equal. clear; lia. }
  { rewrite (KS2 4%nat) by inl. rewrite (KS1 4%nat) by inl. rewrite <- r4. rewrite G4. rewrite (proj2 (proj2 UNWL)). reflexivity. }
  { exact AL48. }
  { clear - HSCR; lia. }
  { clear; lia. }
  intros fx3 R3 M3 model3 A3 RP3 CI3 PRES3. rewrite lb_remove_head in CI3, PRES3.
  assert (InO3 : In (obj - 128, 144) ([(obj - 128, 144)] ++ LB)) by (left; reflexivity).
  assert (AG3 : forall a k, (Sp - 48 <= a /\ a + k <= 2 ^ 47) \/ (6360520 <= a /\ a + k <= 6360532) \/ (65536 <= a /\ a + k <= 884736) \/ (895824 <= a /\ a + k <= 895856) ->
                0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M2 M3 a k).
  { intros a k X Ha Hk i Hi. apply PRES3. clear - Ha Hk Hi; lia. destruct X as [X|[X|[X|X]]].
    - apply stack_client. clear - X Hi SA; lia. clear - X Hi; lia.
    - apply eh_client. clear - X Hi; lia.
    - apply (img_client L ar C LY (as0_layout2_of L C LY)). clear - X Hi; lia.
    - right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. clear - X Hi; lia. apply (proj1 (proj2 UNWL) (0xdab50, 32) i). left; reflexivity. cbn [fst snd]. clear - X Hi; lia. }
  assert (eS16g : L5.u64_at RSEGS M3 (Sp - 48) (obj - 128)) by (t64 AG3 eS16f).
  assert (eS8g : L5.u64_at RSEGS M3 (Sp - 40) 726088) by (t64 AG3 eS8f).
  assert (eS1g : L5.u64_at RSEGS M3 (Sp - 24) Sp) by (t64 AG3 eS1f).
  assert (eS0g : L5.u64_at RSEGS M3 (Sp - 16) (bv_unsigned (getr R1 (reg 8)))) by (t64 AG3 eS0f).
  assert (eRAg : L5.u64_at RSEGS M3 (Sp - 8) 583244) by (t64 AG3 eRAf).
  assert (eC0g : L5.u64_at RSEGS M3 6360520 0) by (t64 AG3 eC0f).
  assert (bU0g : L5.u32_at RSEGS M3 6360528 0) by (t32 AG3 bU0f).
  assert (N1 : L5.img_clear M3 65536 884736). { intros i Hi. rewrite (AG3 i 1). apply K1. exact Hi. right; right; left. clear - Hi; lia. clear - Hi; lia. clear - Hi; lia. clear; lia. }
  assert (N2 : L5.img_clear M3 895824 895856). { intros i Hi. rewrite (AG3 i 1). apply K2. exact Hi. right; right; right. clear - Hi; lia. clear - Hi; lia. clear - Hi; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (cv_blk L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI3 (obj - 128) 144 InO3) as (_ & WOv3 & DOv3).
  pose proof (cv_stack L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI3 (Sp - 4096) 4096 ltac:(clear - HSCR; lia) ltac:(clear; lia) ltac:(clear; lia)) as (WS3 & DS3).
  pose proof (cv_stksh L ar C HI LY HIok M model A LB FF Sp SCR CW SCR8 _ _ _ _ _ _ CI3 (Sp - 512) 2147450432 512 ALS8 ltac:(unfold SB; clear - HSCR; lia) ltac:(unfold SB; clear - SHI; lia)) as ZS3.
  pose proof (cv_blksh L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI3 (obj - 128) 144 obj 2147450864 18 InO3 ALO8 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia)) as ZO3.
  set (MV3 := mrestrict (ahid A3 model3) M3) in *.
  assert (eS16v : L5.u64_at RSEGS MV3 (Sp - 48) (obj - 128)) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI3); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | exact eS16g]).
  assert (eS8v : L5.u64_at RSEGS MV3 (Sp - 40) 726088) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI3); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | exact eS8g]).
  assert (N1v : L5.img_clear MV3 65536 884736) by (apply img_clear_mrestrict; exact N1).
  assert (N2v : L5.img_clear MV3 895824 895856) by (apply img_clear_mrestrict; exact N2).
  assert (R3_2 : getr R3 (reg 2) = Z_to_bv 64 (Sp - 48)) by (rewrite (cs_of_preserved R2 R3 2 RP3) by inl; rewrite eR2; f_equal; clear; lia).
  assert (R3_8 : getr R3 (reg 8) = Z_to_bv 64 obj) by (rewrite (cs_of_preserved R2 R3 8 RP3) by inl; exact eR8).
  assert (R3_3 : getr R3 (reg 3) = Z_to_bv 64 67584).
  { rewrite (cs_of_preserved R2 R3 3 RP3) by inl. rewrite (KS2 3%nat) by inl. rewrite (KS1 3%nat) by inl. rewrite <- G3. f_equal; apply bv_eq; reflexivity. }
  assert (R3_4 : getr R3 (reg 4) = Z_to_bv 64 6363400).
  { rewrite (cs_of_preserved R2 R3 4 RP3) by inl. rewrite (KS2 4%nat) by inl. rewrite (KS1 4%nat) by inl. rewrite <- G4. f_equal; apply bv_eq; reflexivity. }
  assert (E2X : exists fx4 R4 M4v, mem_grows MV3 M4v
            /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (Sp - 112 <= i < Sp - 48) -> M4v (Z_to_bv 64 i) = MV3 (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx3 R3 0xb03dc MV3) (st fx4 R4 0x5fed4 M4v)
            /\ (forall x, In x [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg x) = getr R3 (reg x))
            /\ getr R4 (reg 1) = Z_to_bv 64 726096 /\ getr R4 (reg 2) = Z_to_bv 64 (Sp - 32) /\ getr R4 (reg 10) = Z_to_bv 64 (obj - 128)).
  { pose proof BRo as (_ & [BL|BH] & _).
    - pose proof (ue2e2_bl_conc HFILL HCOPY HTLS fx3 R3 MV3 (fun j => match j with 2%nat => Sp - 512 | 10%nat => obj | 40%nat => U R3 10 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & (MS4 & KS4 & fR1 & fR2 & fR8 & fR10 & _)).
      exists fx4, R4, M4v. split. exact MG4. split. { intros i Hi Hn. apply FZ4. exact Hi. clear - Hn; lia. }
      split. exact MS4. split. { intros x Hx. apply KS4. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. exact fR1. split. rewrite fR2; f_equal; clear; lia. exact fR10.
    - pose proof (ue2e2_bh_conc HFILL HCOPY HTLS fx3 R3 MV3 (fun j => match j with 2%nat => Sp - 512 | 10%nat => obj | 40%nat => U R3 10 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx4 & R4 & M4v & MG4 & _ & FZ4 & (MS4 & KS4 & fR1 & fR2 & fR8 & fR10 & _)).
      exists fx4, R4, M4v. split. exact MG4. split. { intros i Hi Hn. apply FZ4. exact Hi. clear - Hn; lia. }
      split. exact MS4. split. { intros x Hx. apply KS4. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. exact fR1. split. rewrite fR2; f_equal; clear; lia. exact fR10. }
  destruct E2X as (fx4 & R4 & M4v & MG4 & FZ4 & MS4 & KS4 & fR1 & fR2 & fR10).
  set (W4 := fun a => Sp - 112 <= a < Sp - 48).
  apply (cinv_piece L ar C HI LY HIok M model A LB FF Sp SCR CW cw_img _ _ _ _ _ _ fx3 fx4 R3 0xb03dc R4 0x5fed4 M4v W4 K CI3 HS0 MS4 MG4).
  { intros a Ha Hna. apply FZ4. exact Ha. exact Hna. }
  { intros a Wa. subst W4; cbn beta in Wa. left. clear - Wa HSCR; lia. }
  intros M4 model4 CI4 AH4 VIS4 FRM4. subst M4v.
  assert (AG4 : forall a k, (a + k <= Sp - 112 \/ Sp - 48 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M3 M4 a k).
  { intros a k E1 Ha Hk i Hi. apply FRM4. clear - Ha Hk Hi; lia. subst W4; cbn beta. clear - E1 Hi. lia. }
  assert (eS1h : L5.u64_at RSEGS M4 (Sp - 24) Sp) by (t64 AG4 eS1g).
  assert (eS0h : L5.u64_at RSEGS M4 (Sp - 16) (bv_unsigned (getr R1 (reg 8)))) by (t64 AG4 eS0g).
  assert (eRAh : L5.u64_at RSEGS M4 (Sp - 8) 583244) by (t64 AG4 eRAg).
  assert (eC0h : L5.u64_at RSEGS M4 6360520 0) by (t64 AG4 eC0g).
  assert (bU0h : L5.u32_at RSEGS M4 6360528 0) by (t32 AG4 bU0g).
  assert (O1 : L5.img_clear M4 65536 884736). { intros i Hi. rewrite (AG4 i 1). apply N1. exact Hi. left. clear - Hi SPLO; lia. clear - Hi; lia. clear - Hi; lia. clear; lia. }
  assert (O2 : L5.img_clear M4 895824 895856). { intros i Hi. rewrite (AG4 i 1). apply N2. exact Hi. left. clear - Hi SPLO; lia. clear - Hi; lia. clear - Hi; lia. clear; lia. }
  (* [comment removed for export] *)
  apply (cinv_free L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ fx4 R4 (obj - 128) 144 (Sp - 32) 726096 K CI4 HK HS0).
  { left; reflexivity. }
  { exact fR10. }
  { exact fR1. }
  { split. clear; lia. reflexivity. }
  { exact fR2. }
  { rewrite (KS4 4%nat) by inl. rewrite R3_4. rewrite (proj2 (proj2 UNWL)). reflexivity. }
  { exact AL32. }
  { clear - HSCR; lia. }
  { clear; lia. }
  intros fx5 R5 M5 model5 A5 RP5 CI5 PRES5. rewrite lb_remove_head in CI5, PRES5.
  assert (AG5 : forall a k, (Sp - 32 <= a /\ a + k <= 2 ^ 47) \/ (6360520 <= a /\ a + k <= 6360532) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M4 M5 a k).
  { intros a k X Ha Hk i Hi. apply PRES5. clear - Ha Hk Hi; lia. destruct X as [X|X].
    - apply stack_client. clear - X Hi SA; lia. clear - X Hi; lia.
    - apply eh_client. clear - X Hi; lia. }
  assert (eS1i : L5.u64_at RSEGS M5 (Sp - 24) Sp) by (t64 AG5 eS1h).
  assert (eS0i : L5.u64_at RSEGS M5 (Sp - 16) (bv_unsigned (getr R1 (reg 8)))) by (t64 AG5 eS0h).
  assert (eRAi : L5.u64_at RSEGS M5 (Sp - 8) 583244) by (t64 AG5 eRAh).
  assert (eC0i : L5.u64_at RSEGS M5 6360520 0) by (t64 AG5 eC0h).
  assert (bU0i : L5.u32_at RSEGS M5 6360528 0) by (t32 AG5 bU0h).
  (* [comment removed for export] *)
  pose proof (cv_stack L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI5 (Sp - 4096) 4096 ltac:(clear - HSCR; lia) ltac:(clear; lia) ltac:(clear; lia)) as (WS5 & DS5).
  pose proof (cv_stksh L ar C HI LY HIok M model A LB FF Sp SCR CW SCR8 _ _ _ _ _ _ CI5 (Sp - 512) 2147450432 512 ALS8 ltac:(unfold SB; clear - HSCR; lia) ltac:(unfold SB; clear - SHI; lia)) as ZS5.
  set (MV5 := mrestrict (ahid A5 model5) M5) in *.
  assert (eS1v : L5.u64_at RSEGS MV5 (Sp - 24) Sp) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI5); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | exact eS1i]).
  assert (eS0v : L5.u64_at RSEGS MV5 (Sp - 16) (bv_unsigned (getr R1 (reg 8)))) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI5); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | exact eS0i]).
  assert (eRAv : L5.u64_at RSEGS MV5 (Sp - 8) 583244) by (apply (cv_u64 L ar C HI LY HIok M model A LB FF Sp SCR CW _ _ _ _ _ _ CI5); [left; clear - SA; lia | clear - SPLO; lia | clear - SA; lia | exact eRAi]).
  assert (P1v : L5.img_clear MV5 65536 884736).
  { apply img_clear_mrestrict. intros i Hi. rewrite PRES5. apply O1. exact Hi. clear - Hi; lia. apply (img_client L ar C LY (as0_layout2_of L C LY)). clear - Hi; lia. }
  assert (P2v : L5.img_clear MV5 895824 895856).
  { apply img_clear_mrestrict. intros i Hi. rewrite PRES5. apply O2. exact Hi. clear - Hi; lia.
    right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. clear - Hi; lia. apply (proj1 (proj2 UNWL) (0xdab50, 32) i). left; reflexivity. cbn [fst snd]. clear - Hi; lia. }
  assert (R5_2 : getr R5 (reg 2) = Z_to_bv 64 (Sp - 32)) by (rewrite (cs_of_preserved R4 R5 2 RP5) by inl; exact fR2).
  assert (R5_3 : getr R5 (reg 3) = Z_to_bv 64 67584) by (rewrite (cs_of_preserved R4 R5 3 RP5) by inl; rewrite (KS4 3%nat) by inl; exact R3_3).
  assert (R5_4 : getr R5 (reg 4) = Z_to_bv 64 6363400) by (rewrite (cs_of_preserved R4 R5 4 RP5) by inl; rewrite (KS4 4%nat) by inl; exact R3_4).
  pose proof (ue2e3_conc HFILL HCOPY HTLS fx5 R5 MV5 (fun j => match j with 2%nat => Sp - 512 | 40%nat => U R5 10 | 41%nat => bv_unsigned (getr R1 (reg 8)) | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | apply BL.bvu_range | sc]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FZ6 & (MS6 & KS6 & gR1 & gR2 & gR8 & gR9)).
  set (W6 := fun a => Sp - 96 <= a < Sp - 32).
  apply (cinv_piece L ar C HI LY HIok M model A LB FF Sp SCR CW cw_img _ _ _ _ _ _ fx5 fx6 R5 0xb1450 R6 0x8e64c M6v W6 K CI5 HS0 MS6 MG6).
  { intros a Ha Hna. apply FZ6. exact Ha. subst W6; cbn beta in Hna. clear - Hna; lia. }
  { intros a Wa. subst W6; cbn beta in Wa. left. clear - Wa HSCR; lia. }
  intros M6 model6 CI6 AH6 VIS6 FRM6.
  assert (AG6 : forall a k, (a + k <= Sp - 96 \/ Sp - 32 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M5 M6 a k).
  { intros a k E1 Ha Hk i Hi. apply FRM6. clear - Ha Hk Hi; lia. subst W6; cbn beta. clear - E1 Hi. lia. }
  assert (eC0j : L5.u64_at RSEGS M6 6360520 0) by (t64 AG6 eC0i).
  assert (bU0j : L5.u32_at RSEGS M6 6360528 0) by (t32 AG6 bU0i).
  destruct CI6 as (HH6 & AM6 & RT6 & IA6 & STK6 & SH6 & EK6 & DK6).
  apply (KONT fx6 R6 M6 model6 A5).
  - apply preserved_by_index. intros k Hk. unfold cs_all in Hk.
    assert (R34 : forall x, In x [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg x) = getr R (reg x)).
    { intros x Hx. rewrite (KS6 x) by (revert x Hx; apply L5K.incl_b; vm_compute; reflexivity).
      rewrite (cs_of_preserved R4 R5 x RP5) by (revert x Hx; apply L5K.incl_b; vm_compute; reflexivity).
      rewrite (KS4 x) by (revert x Hx; apply L5K.incl_b; vm_compute; reflexivity).
      rewrite (cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply L5K.incl_b; vm_compute; reflexivity).
      rewrite (KS2 x) by (revert x Hx; apply L5K.incl_b; vm_compute; reflexivity).
      apply KS1. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
    destruct Hk as [<-|[<-|[<-|[<-|[<-|Hk]]]]].
    + rewrite gR2. replace (reg 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G2. f_equal. clear; lia.
    + apply R34. inl.
    + apply R34. inl.
    + rewrite gR8. rewrite Z_to_bv_bv_unsigned. apply KS1. inl.
    + rewrite gR9. replace (reg 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G9. f_equal. clear; lia.
    + apply R34. right; right. exact Hk.
  - exact eC0j.
  - exact bU0j.
  - split. exact EK6. split. exact (astk_defined ar M6 Sp SCR (Sp - SCR) SCR STK6 ltac:(clear; lia) ltac:(clear; lia)). exact DK6.
  - exact RT6.
  - exact IA6.
  - exact AM6.
  - exact HH6.
Qed.

End WithIface.
End SCFG_1.
End L5ACA2.
