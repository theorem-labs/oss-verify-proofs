(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf9
  AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHit AsanRepCa AsanRepX AsanFrame AsanRepFlip AsanRealloc AsanRefillM AsanRepEnq.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_iface AF_place AF_fakestack_rep AF_kit AF_kit2 AF_poison AF_free_kit AF_qkit AF_free1 AF_free1b AF_free1e AF_free1c AF_free1d AF_free3 AF_free4
  A_policy5 A_slack5 A_budget5 A_live A_bundle A_benv5 A_init5 A_instD5 A_balloc5 A_bpolicy5 A_rtok5 A_bevents5 A_bframe
  AF_alloc_iface AF_dput_iface AF_free_iface AF_refill_iface AF_tkit AF_ainv_kit AX_unreg AX_Exit AF_statics AF_caT AF_casT AF_refill_room AF_refillT AF_dputT AF_deallocT1 AF_deallocT2 AF_deallocT3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section DeallocT5.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation DPUT := (depot_put_srz E0 FSB0 HR0 L0 RES0 EB0 HR0_ok ENV0 ENV_depot EB0_ok L0OK).
(* [comment removed for export] *)
Lemma R2F1 : AF_deallocT2.R2F1_stmt E0.
Proof.
  intros a m m' lo cb n l b P. cbv zeta. intros TQ ROOMb PEND REP WF RENV WM AG LO NC1 NC2 NC3.
  exact (AsanRepEnq.ARep_after_enq1 asegs E0 P a cb n PEND WF RENV m m' lo l b TQ ROOMb REP WM AG LO NC1 NC2 NC3).
Qed.
Lemma R2F2 : AF_deallocT2.R2F2_stmt E0.
Proof.
  intros a m m' lo cb n P junk. cbv zeta. intros NE CI PEND REP WF RENV WM AG LO NC1 NC2 NC3 NC4 NC5 LJ NC6.
  exact (AsanRepEnq.ARep_after_enq2 asegs E0 P a cb n PEND WF RENV m m' lo junk NE CI REP WM AG LO NC1 NC2 NC3 NC4 NC5 LJ NC6).
Qed.
Hypothesis R3 : AF_deallocT3.R3_stmt E0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).
#[local] Notation T := (ae_thread E0).
#[local] Notation INST := 0xaa518.

(* [comment removed for export] *)
Definition recycle_srz_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (p n lo B A len C C' : Z) (ws : list word) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  K [] ->
  RTOKc C C' s mo -> 1 <= C -> FSLACK <= C' -> AINVc a m mo -> fbudget_pre a -> In (p, n) (live_blocks a) ->
  stk asegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 -> tp = wz 0x5e0b10 ->
  usp <= B -> B + 16 <= A -> A + 8 * zlen ws < 2^47 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     dealloc_post_state E0 FSB0 HR0 L0 RES0 EB0 PL0 a a' m m' mo mo' s C C' p n lo usp (bst_key len ws) ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom asegs)) mo') K) ->
  AF_deallocT3.QR_post E0 FSB0 HR0 L0 RES0 EB0 PL0 s mo m usp lo (p - 16) B C C' (bst_key len ws) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc K.
Hypothesis RECYC : recycle_srz_stmt.

(* [comment removed for export] *)
#[local] Notation REFILLc := (refill_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK).

Theorem dealloc_srz : dealloc_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof.
  unfold dealloc_srz_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s p n lo B A len C C' ws K. cbv zeta.
  intros KN TOK HC1 HCS AIV FB LIVE SK LOC LO SPA TP HB HBA HAW OBJ TR HLEN HWS KONT.
  pose proof AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & _).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  assert (SPH : bv_unsigned sp < 2^47) by (clear -HB HBA HAW; unfold zlen in HAW; lia).
  pose proof FB as (BU1 & BU2 & BU3). unfold kInitialCredit in BU3.
  assert (NP12 : 0 <= as_nprim_ever (aps_alloc s) <= 12000) by (clear -BU1 BU2 BU3; lia).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
  destruct (refill_room_of_binv E0 [] [] (aps_alloc s) kBatchClass Hwf Hbinv HB24 NP12) as [RROOM ROOM].
  (* [comment removed for export] *)
  destruct (freed_chunk_facts E0 s mo m p n Hrep Hwf Hkern EI1 EI2 LIVE) as (cm0 & aid0 & b10 & Hcm0 & UB0 & Ecn0 & _).
  (* [comment removed for export] *)
  eapply (qput_front_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 EB0_ok ENV_depot ENV0 PL0OK L0OK DPUT);
    [exact KN| exact TOK| exact HC1| exact HCS| exact AIV| | exact FB| exact LIVE| | exact SK| exact LOC| exact LO| exact SPA| exact TP| exact HB| exact HBA| exact HAW| exact OBJ| exact TR| exact HLEN| exact HWS|].
  { pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC0 & _).
    exact (AINV_dput_mutexes E0 FSB0 PL0 IC0 _ _ _ AIV). }
  { (* [comment removed for export] *) rewrite <- Ecn0. exact (Hcs _ _ Hcm0). }
  unfold AF_deallocT1.QPF_post. intros u0 u1 u2 v5 v6 v7 u3 u4 u5 u6 m5 mo5 a2 cm b1 aid fid. cbv zeta.
  intros Hcm ST UB HB1 HB1' RUNd FID WF2 SAME AK2 TOK2 KIA2 Ffs5 Ffds5 Ftid5 MI5 SK5 WM5 MUW AG5 DR5 DMX5 PF5 HDR5 FID5 ST5 SH5.
  assert (Ecm : cm = cm0) by (rewrite Hcm0 in Hcm; injection Hcm; auto). subst cm0.
  assert (En : n = cm_n cm) by (symmetry; exact Ecn0).
  (* [comment removed for export] *)
  eapply (enqueue_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK REFILLc R2F1 R2F2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s lo B C C' (bst_key len ws) K
            u0 u1 u2 v5 v6 v7 u3 u4 u5 u6 m5 mo5 a2 cm b1 aid fid (p - 16));
    [exact KN| exact AIV| exact ENV| exact FB| replace (p - 16 + 16) with p by (clear; lia); rewrite <- En; exact LIVE| exact (Hcs _ _ Hcm)
    | exact RROOM| exact ROOM| exact LOC| exact LO| exact SPA| exact SPH| exact TP
    | exact Hcm| exact ST| exact UB| exact HB1| exact HB1'| exact RUNd| exact FID| exact WF2| exact SAME| exact AK2| exact TOK2| exact KIA2| exact Ffs5| exact Ffds5| exact Ftid5
    | exact MI5| exact SK5| exact WM5| exact MUW| exact AG5| exact DR5| exact PF5| exact HDR5| exact FID5| exact ST5| exact SH5|].
  unfold AF_deallocT2.QE_post. intros w0 w1 w2 a0' a1' y2 a3' a4' x5 x6 x7 w3 w4 w5 w6 m6 mo6 a2x a4 cm' aid' fid'. cbv zeta.
  intros Hcm' ST' UB' RUNd' FID' DS2 ND2 RUNe FLD WF4 REP4 AK4 TOK4 KIA4 RES4 GQ4 TQ4 DI4 SS4 CS4 Ffs6 Ffds6 Ftid6 MI6 SK6 WM6 RT6 MUW6 PF6 QC6.
  (* [comment removed for export] *)
  eapply (putback_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s lo B C C' (bst_key len ws) K
            w0 w1 w2 a0' a1' y2 a3' a4' x5 x6 x7 w3 w4 w5 w6 m6 mo6 a2x a4 cm' aid' fid' (p - 16));
    [exact KN| exact TOK| exact HC1| exact HCS| exact AIV| exact FB| | exact LOC| exact LO| exact SPA| exact SPH| exact TP
    | exact Hcm'| exact ST'| exact UB'| exact RUNd'| exact FID'| exact DS2| exact ND2| exact RUNe| exact FLD| exact WF4| exact REP4| exact AK4| exact TOK4| exact KIA4
    | exact RES4| exact GQ4| exact TQ4| exact DI4| exact SS4| exact CS4| exact Ffs6| exact Ffds6| exact Ftid6| exact MI6| exact SK6| exact WM6| exact RT6| exact MUW6| exact PF6| exact QC6| |].
  { replace (p - 16 + 16) with p by (clear; lia). assert (Ecm' : cm' = cm) by (rewrite Hcm in Hcm'; injection Hcm'; auto). rewrite Ecm', <- En. exact LIVE. }
  { intros until a'. assert (Ecm' : cm' = cm) by (rewrite Hcm in Hcm'; injection Hcm'; auto). rewrite Ecm', <- En. replace (p - 16 + 16) with p by (clear; lia). exact (KONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' mo' a'). }
  (* [comment removed for export] *)
  unfold AF_deallocT3.QD_post. intros z0 z1 z2 a4'' z5 z6 z7 z3 z4 z8 z9 m6' mo6' a2y a4y cmy aidy fidy. cbv zeta.
  intros Hcmy STy UBy RUNdy FIDy DS2y ND2y RUNey FLDy WF4y REP4y AK4y TOK4y KIA4y RES4y GQ4y TQ4y DI4y SS4y CS4y Ffs6y Ffds6y Ftid6y MI6y SK6y WM6y RT6y MUW6y PF6y QC6y GTy.
  assert (Ecmy : cmy = cm) by (rewrite Hcm in Hcmy; injection Hcmy; auto).
  eapply (drain_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK R3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s lo B C C' (bst_key len ws) K
            z0 z1 z2 a4'' z5 z6 z7 z3 z4 z8 z9 m6' mo6' a2y a4y cmy aidy fidy (p - 16));
    [exact KN| exact TOK| exact HC1| exact HCS| exact AIV| exact FB| | exact LOC| exact LO| exact SPA| exact SPH| exact TP
    | exact Hcmy| exact STy| exact UBy| exact RUNdy| exact FIDy| exact DS2y| exact ND2y| exact RUNey| exact FLDy| exact WF4y| exact REP4y| exact AK4y| exact TOK4y| exact KIA4y
    | exact RES4y| exact GQ4y| exact TQ4y| exact DI4y| exact SS4y| exact CS4y| exact Ffs6y| exact Ffds6y| exact Ftid6y| exact MI6y| exact SK6y| exact WM6y| exact RT6y| exact MUW6y| exact PF6y| exact QC6y
    | exact GTy| |].
  { replace (p - 16 + 16) with p by (clear; lia). rewrite Ecmy, <- En. exact LIVE. }
  { intros until a'. rewrite Ecmy, <- En. replace (p - 16 + 16) with p by (clear; lia). exact (KONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' mo' a'). }
  (* [comment removed for export] *)
  exact (RECYC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s p n lo B A len C C' ws K KN TOK HC1 HCS AIV FB LIVE SK LOC LO SPA TP HB HBA HAW KONT).
Qed.

End DeallocT5.
End RC__1.
