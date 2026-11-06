(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue BigLinkGlueUb0 L5Defs L5Kn L5DDqU L5SubMulU L5DivNPU L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5DivSpecsU L5DivPartsU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5DIVLOOPU.
Import L5CSU. Import L5DSU. Import L5DIVPU.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition LBODY : Z := 0x2294c.
Definition L2 : Z := 0x22980.      (* [comment removed for export] *)
Definition L3 : Z := 0x229c0.      (* [comment removed for export] *)
Definition MM : Z := 2 ^ 64.

(* [comment removed for export] *)
Lemma zbv_mod a b : a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
Lemma zbv_addMM a : Z_to_bv 64 (a + 2 ^ 64) = Z_to_bv 64 a.
Proof. apply zbv_mod. rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity. Qed.
Lemma zbv_neg a : Z_to_bv 64 (- a) = Z_to_bv 64 (2 ^ 64 - a).
Proof. apply zbv_mod. replace (2 ^ 64 - a) with (- a + 2 ^ 64) by lia. rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity. Qed.

(* [comment removed for export] *)
Lemma word_of_defined M a : L5.defined M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists w, L5.u64_at RSEGS M a w /\ 0 <= w < 2 ^ 64.
Proof.
  intros D Ha Hb. destruct (L5KU.limbs_of_defined M a 1 ltac:(exact D) Ha ltac:(lia)) as (ws & L & R & LA).
  destruct ws as [|w [|]]; cbn in L; try lia. exists w. split. pose proof (LA 0%nat ltac:(cbn; lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
  inversion R. lia.
Qed.
Lemma words2_of_defined M a : L5.defined M a 16 -> 0 <= a -> a + 16 <= 2 ^ 64 ->
  exists w0 w1, L5.u64_at RSEGS M a w0 /\ L5.u64_at RSEGS M (a + 8) w1 /\ 0 <= w0 < 2 ^ 64 /\ 0 <= w1 < 2 ^ 64.
Proof.
  intros D Ha Hb. destruct (L5KU.limbs_of_defined M a 2 ltac:(exact D) Ha ltac:(lia)) as (ws & L & R & LA).
  destruct ws as [|w0 [|w1 [|]]]; cbn in L; try lia. exists w0, w1.
  split. pose proof (LA 0%nat ltac:(cbn; lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
  split. pose proof (LA 1%nat ltac:(cbn; lia)) as X. replace (a + 8 * Z.of_nat 1) with (a + 8) in X by lia. exact X.
  inversion R as [|x l' R0 R1]. inversion R1. lia.
Qed.

(* [comment removed for export] *)
Lemma u64_at_agreeW M M' a v : (forall x : word, a <= bv_unsigned x < a + 8 -> M' x = M x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof.
  intros HA Ha H8 Hu. eapply (L5C.u64_at_agree RSEGS M M'). 4: exact Hu. 2: exact Ha. 2: exact H8.
  intros i Hi. apply HA. rewrite BG.unsigned_lit by lia. exact Hi.
Qed.

(* [comment removed for export] *)
Definition VL (sp this denomd lp1 quotd v72 v73 v74 v75 v76 v77 v78 v79 : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 33%nat => this | 66%nat => denomd | 67%nat => lp1 | 68%nat => quotd
  | 72%nat => v72 | 73%nat => v73 | 74%nat => v74 | 75%nat => v75 | 76%nat => v76 | 77%nat => v77 | 78%nat => v78 | 79%nat => v79
  | _ => 0
  end.

Local Ltac kin := apply L5K.In_of_mem; reflexivity.

Section Loop.
Variables (sp this remd quotd denomd d : Z) (l n : nat).
Hypothesis Hd : 2 ^ 63 <= d < 2 ^ 64.
Hypothesis Hln : (l <= n <= 299)%nat.
Hypothesis Hthis : 0 <= this < 2 ^ 64.
Hypothesis A16 : sp mod 16 = 0.
Hypothesis SPR : 1048928 + 64 <= sp <= 2 ^ 47.
Hypothesis RA8 : remd mod 8 = 0. Hypothesis RLO : 4096 <= remd. Hypothesis RHI : remd + 8 * (Z.of_nat n + 1) <= 2 ^ 47.
Hypothesis QA8 : quotd mod 8 = 0. Hypothesis QLO : 4096 <= quotd. Hypothesis QHI : quotd + 8 * (Z.of_nat n - Z.of_nat l) <= 2 ^ 47.
Hypothesis DA8 : denomd mod 8 = 0. Hypothesis DLO : 4096 <= denomd. Hypothesis DHI : denomd + 8 * (Z.of_nat l + 1) <= 2 ^ 47.
Hypothesis AP1 : apart remd (8 * (Z.of_nat n + 1)) (sp - 416) 416.
Hypothesis AP2 : apart quotd (8 * (Z.of_nat n - Z.of_nat l)) (sp - 416) 416.
Hypothesis AP3 : apart remd (8 * (Z.of_nat n + 1)) quotd (8 * (Z.of_nat n - Z.of_nat l)).
Hypothesis AP4 : apart remd (8 * (Z.of_nat n + 1)) denomd (8 * (Z.of_nat l + 1)).
Hypothesis AP5 : apart quotd (8 * (Z.of_nat n - Z.of_nat l)) denomd (8 * (Z.of_nat l + 1)).
Hypothesis AP6 : apart denomd (8 * (Z.of_nat l + 1)) (sp - 312) 8.
Hypothesis AP7 : apart denomd (8 * (Z.of_nat l + 1)) (sp - 416) 64.

(* [comment removed for export] *)
Definition FRAME (M M' : word -> option byte) : Prop :=
  forall a : word, ~ inr remd (8 * (Z.of_nat n + 1)) (bv_unsigned a) -> ~ inr quotd (8 * (Z.of_nat n - Z.of_nat l)) (bv_unsigned a) ->
                   ~ inr (sp - 312) 8 (bv_unsigned a) -> ~ inr (sp - 416) 64 (bv_unsigned a) -> M' a = M a.
Lemma FRAME_trans M1 M2 M3 : FRAME M1 M2 -> FRAME M2 M3 -> FRAME M1 M3.
Proof. intros A B a H1 H2 H3 H4. rewrite (B a H1 H2 H3 H4). apply A; assumption. Qed.

(* [comment removed for export] *)
Record minv (M : word -> option byte) : Prop := MINV {
  mi_rd : L5.defined M remd (8 * (Z.of_nat n + 1));
  mi_rw : L5.writable RSEGS M remd (8 * (Z.of_nat n + 1));
  mi_qw : L5.writable RSEGS M quotd (8 * (Z.of_nat n - Z.of_nat l));
  mi_dd : L5.defined M denomd (8 * (Z.of_nat l + 1));
  mi_fw : L5.writable RSEGS M (sp - 416) 416;
  mi_qd : L5.defined M (sp - 312) 8;
  mi_vr : L5.u64_at RSEGS M (sp - 304) remd;
  mi_vq : L5.u64_at RSEGS M (sp - 232) quotd;
  mi_vd : L5.u64_at RSEGS M (sp - 152) denomd;
  mi_vl : L5.u64_at RSEGS M (sp - 144) (Z.of_nat l + 1) }.
Lemma minv_step M M' : minv M -> mem_grows M M' -> FRAME M M' -> minv M'.
Proof using sp this remd quotd denomd l n Hln Hthis SPR RLO QLO DLO AP1 AP2.
  intros [A B C D E F VR VQ VD VS] G FR. unfold apart in AP1, AP2. constructor.
  - eapply L5.defined_grows; eauto. - eapply L5.writable_grows; eauto. - eapply L5.writable_grows; eauto.
  - eapply L5.defined_grows; eauto. - eapply L5.writable_grows; eauto. - eapply L5.defined_grows; eauto.
  - eapply u64_at_agreeW. 4: exact VR. 2-3: lia. intros x Hx. apply FR; unfold inr; lia.
  - eapply u64_at_agreeW. 4: exact VQ. 2-3: lia. intros x Hx. apply FR; unfold inr; lia.
  - eapply u64_at_agreeW. 4: exact VD. 2-3: lia. intros x Hx. apply FR; unfold inr; lia.
  - eapply u64_at_agreeW. 4: exact VS. 2-3: lia. intros x Hx. apply FR; unfold inr; lia.
Qed.

(* [comment removed for export] *)
Definition at_body (R : bvmap 5 word) (k : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 352) /\ getr R (reg 18) = Z_to_bv 64 this /\
  getr R (reg 19) = Z_to_bv 64 (8 * (Z.of_nat k - Z.of_nat l - 1)) /\
  getr R (reg 20) = Z_to_bv 64 ((-1) * (Z.of_nat l + 1) + 1152921504606846976) /\
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l + 1) /\ getr R (reg 22) = Z_to_bv 64 (Z.of_nat l) /\
  getr R (reg 23) = Z_to_bv 64 (Z.of_nat k) /\ getr R (reg 24) = Z_to_bv 64 d /\
  getr R (reg 27) = Z_to_bv 64 ((-1) * (Z.of_nat l + 1)).

(* [comment removed for export] *)
Lemma iter fx R M (k : nat) :
  (l < k <= n)%nat -> at_body R k -> minv M ->
  exists fx' R' M',
    msteps RSEGS (st fx R LBODY M) (st fx' R' (if (l + 1 <? k)%nat then LBODY else LEXIT) M')
    /\ ((l + 1 < k)%nat -> at_body R' (k - 1))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 352)
    /\ (forall i, In i loop_kept -> getr R' (reg i) = getr R (reg i))
    /\ FRAME M M' /\ mem_grows M M'.
Proof.
  intros Hk (B2 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B27) MI. pose proof MI as [RD RW QW DD FW QD VR VQ VD VS].
  unfold apart in AP1, AP2, AP3, AP4, AP5, AP6, AP7.
  set (ks := Z.of_nat k) in *. assert (Hks: Z.of_nat l + 1 <= ks <= Z.of_nat n) by lia.
  set (idx := ks - Z.of_nat l - 1) in *.
  (* [comment removed for export] *)
  destruct (words2_of_defined M (remd + 8 * (ks - 1)) ltac:(intros i Hi; replace (remd + 8 * (ks - 1) + i) with (remd + (8 * (ks - 1) + i)) by lia; apply RD; lia)
              ltac:(lia) ltac:(lia)) as (w0 & w1 & W0 & W1 & Rw0 & Rw1).
  replace (remd + 8 * (ks - 1) + 8) with (remd + 8 * ks) in W1 by lia.
  (* [comment removed for export] *)
  pose proof (L5DIVNPU.d5ul1_conc fx R M (VL sp this denomd (Z.of_nat l + 1) quotd 0 w1 d 0 w0 idx 0 remd)) as P1. cbn [VL] in P1.
  destruct (P1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               B2 B18 B21 ltac:(rewrite B23; f_equal; lia) B24 ltac:(lia) A16
               ltac:(eapply L5.writable_sub; [exact FW | lia | lia]) VR ltac:(lia) ltac:(exact RA8)
               ltac:(replace (8 * (Z.of_nat l + 1) + (8 * idx + remd)) with (remd + 8 * ks) by lia; exact W1)
               ltac:(replace (8 * (Z.of_nat l + 1) + (8 * idx + remd) - 8) with (remd + 8 * (ks - 1)) by lia; exact W0)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & R1_1 & R1_10 & R1_11 & R1_12 & R1_13 & R1_14 & R1_25 & R1_26). clear P1.
  (* [comment removed for export] *)
  destruct (L5DDQU.ddq_run fx1 R1 M1 d L2 R1_13 Hd R1_1 ltac:(split; [unfold L2; lia | reflexivity])) as (fx2 & R2 & M2 & MS2 & K2 & RP2 & EM2).
  subst M2.
  pose proof (bv_unsigned_in_range _ (getr R2 (reg 10))) as Rq. change (bv_modulus 64) with (2 ^ 64) in Rq.
  set (q := bv_unsigned (getr R2 (reg 10))) in *.
  assert (R2_10: getr R2 (reg 10) = Z_to_bv 64 q). { apply BG.word_of_unsigned. reflexivity. }
  assert (T2: forall i v, In i L5DDQU.ddq_kept -> In i L5DIVNPU.KS_d5ul1 -> getr R (reg i) = v -> getr R2 (reg i) = v).
  { intros i v Hi1 Hi2 Hv. rewrite (K2 i Hi1), (K1 i Hi2). exact Hv. }
  (* [comment removed for export] *)
  assert (VR1: L5.u64_at RSEGS M1 (sp - 304) remd). { eapply u64_at_agreeW. 4: exact VR. 2-3: lia. intros x _. apply FR1. }
  assert (VD1: L5.u64_at RSEGS M1 (sp - 152) denomd). { eapply u64_at_agreeW. 4: exact VD. 2-3: lia. intros x _. apply FR1. }
  assert (VS1: L5.u64_at RSEGS M1 (sp - 144) (Z.of_nat l + 1)). { eapply u64_at_agreeW. 4: exact VS. 2-3: lia. intros x _. apply FR1. }
  (* [comment removed for export] *)
  pose proof (L5DIVNPU.d5ul2_conc fx2 R2 M1 (VL sp this denomd (Z.of_nat l + 1) quotd 0 0 0 0 q idx 0 remd)) as P2. cbn [VL] in P2.
  destruct (P2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(apply T2; [kin|kin|exact B2]) R2_10 ltac:(apply T2; [kin|kin|exact B18]) ltac:(apply T2; [kin|kin|]; rewrite B19; f_equal; lia)
               ltac:(apply T2; [kin|kin|exact B20]) ltac:(apply T2; [kin|kin|exact B21]) ltac:(apply T2; [kin|kin|]; rewrite B23; f_equal; lia)
               ltac:(apply T2; [kin|kin|exact B27])
               ltac:(lia) A16
               ltac:(eapply L5.writable_sub; [eapply L5.writable_grows; [exact MG1 | exact FW] | lia | lia]) VR1 VD1 VS1 ltac:(lia) ltac:(exact RA8)
               ltac:(lia) ltac:(lia) ltac:(lia))
    as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & K3 & R3_1 & R3_10 & R3_11 & R3_12 & R3_13 & R3_14 & R3_23 & Q3). clear P2.
  (* [comment removed for export] *)
  assert (FR13: FRAME M M3). { intros a N1 N2 N3 N4. unfold inr in N3. rewrite FR3 by lia. apply FR1. }
  pose proof (minv_step M M3 MI ltac:(eapply mem_grows_trans; [exact MG1 | exact MG3]) FR13) as MI3. pose proof MI3 as [RD3 RW3 QW3 DD3 FW3 QD3 VR3 VQ3 VD3 VS3].
  assert (CTX: L5SMU.smctx M3 (sp - 352) (remd + 8 * idx) denomd (sp - 312) (l + 1)).
  { constructor; unfold L5SMU.apart; rewrite ?Nat2Z.inj_add; try lia.
    - eapply L5.writable_sub. exact FW3. lia. lia.
    - eapply L5.writable_sub. exact RW3. lia. lia.
    - eapply L5.defined_sub. exact RD3. lia. lia.
    - eapply L5.defined_sub. exact DD3. lia. lia.
    - eapply L5.writable_sub. exact FW3. lia. lia.
    - exact QD3. }
  destruct (L5SMU.submul_run fx3 R3 M3 (sp - 352) (remd + 8 * idx) denomd (sp - 312) L3 (l + 1)
              ltac:(rewrite (K3 2%nat) by kin; apply T2; [kin|kin|exact B2])
              ltac:(rewrite R3_11; f_equal; lia)
              R3_12 ltac:(rewrite R3_13; rewrite Nat2Z.inj_add; reflexivity) R3_14 R3_1 ltac:(split; [unfold L3; lia | reflexivity]) CTX)
    as (fx4 & R4 & M4 & MS4 & K4 & K4' & RP4 & CTX4 & FR4 & MG4).
  assert (FR34: FRAME M3 M4).
  { intros a N1 N2 N3 N4. unfold inr in N1, N2, N3, N4. apply FR4. unfold L5.outside. intros rg Hrg. cbn in Hrg. unfold L5.in_rng.
    destruct Hrg as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite ?Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  pose proof (minv_step M3 M4 MI3 MG4 FR34) as MI4. pose proof MI4 as [RD4 RW4 QW4 DD4 FW4 QD4 VR4 VQ4 VD4 VS4].
  destruct (word_of_defined M4 (sp - 312) QD4 ltac:(lia) ltac:(lia)) as (q' & Q4 & Rq').
  assert (SMK: forall i, In i (L5SMU.sm_kept ++ L5SMU.sm_rest) -> getr R4 (reg i) = getr R3 (reg i)).
  { intros i Hi. apply in_app_iff in Hi. destruct Hi as [Hi|Hi]. apply K4. exact Hi. apply K4'. exact Hi. }
  assert (T4: forall i v, In i (L5SMU.sm_kept ++ L5SMU.sm_rest) -> In i L5DIVNPU.KS_d5ul2 -> getr R2 (reg i) = v -> getr R4 (reg i) = v).
  { intros i v Hi1 Hi2 Hv. rewrite (SMK i Hi1), (K3 i Hi2). exact Hv. }
  assert (R4_2': getr R4 (reg 2) = Z_to_bv 64 (sp - 352)). { apply T4; [kin|kin|]. apply T2; [kin|kin|exact B2]. }
  assert (R4_19: getr R4 (reg 19) = Z_to_bv 64 (8 * idx)). { apply T4; [kin|kin|]. apply T2; [kin|kin|]. rewrite B19; f_equal; lia. }
  assert (R4_22: getr R4 (reg 22) = Z_to_bv 64 (Z.of_nat l)). { apply T4; [kin|kin|]. apply T2; [kin|kin|exact B22]. }
  assert (R4_23: getr R4 (reg 23) = Z_to_bv 64 idx). { rewrite (SMK 23%nat) by kin. exact R3_23. }
  assert (R4_25: getr R4 (reg 25) = Z_to_bv 64 (ks - 1)). { apply T4; [kin|kin|]. rewrite (K2 25%nat) by kin. rewrite R1_25; f_equal; lia. }
  assert (QS: 4096 <= quotd + 8 * idx /\ quotd + 8 * idx + 8 <= quotd + 8 * (Z.of_nat n - Z.of_nat l)) by lia.
  assert (QSA: (quotd + 8 * idx) mod 8 = 0). { rewrite (Z.mul_comm 8), Z_mod_plus_full. exact QA8. }
  assert (QSW: L5.writable RSEGS M4 (quotd + 8 * idx) 8). { eapply L5.writable_sub. exact QW4. lia. lia. }
  assert (QSD: sp - 352 + 352 <= quotd + 8 * idx \/ quotd + 8 * idx + 8 <= sp - 352) by lia.
  (* [comment removed for export] *)
  assert (KEEP4: forall i, In i loop_kept -> getr R4 (reg i) = getr R (reg i)).
  { intros j Hj. assert (Hj4: In j (L5SMU.sm_kept ++ L5SMU.sm_rest)) by (pose proof Hj as H'; L5K.inlist H').
    assert (Hj3: In j L5DIVNPU.KS_d5ul2) by (pose proof Hj as H'; L5K.inlist H').
    assert (Hj2: In j L5DDQU.ddq_kept) by (pose proof Hj as H'; L5K.inlist H'). assert (Hj1: In j L5DIVNPU.KS_d5ul1) by (pose proof Hj as H'; L5K.inlist H').
    apply T4; [exact Hj4|exact Hj3|]. apply T2; [exact Hj2|exact Hj1|reflexivity]. }
  (* [comment removed for export] *)
  pose proof (FRAME_trans _ _ _ FR13 FR34) as FR14.
  destruct (Nat.ltb_spec (l + 1) k) as [Hlt|Hge].
  - (* [comment removed for export] *)
    pose proof (L5DIVNPU.d5ul3c_conc fx4 R4 M4 (VL sp this denomd (Z.of_nat l + 1) quotd 0 0 0 (ks - 1) q' idx (Z.of_nat l) 0)) as P3.
    cbn [VL] in P3.
    destruct (P3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R4_2' R4_19 R4_22 R4_23 R4_25 ltac:(lia) A16
                 ltac:(eapply L5.writable_sub; [exact FW4 | lia | lia]) Q4 VQ4 ltac:(lia) ltac:(exact QA8) QSW QSD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & K5 & R5_1 & R5_10 & R5_11 & R5_12 & R5_13 & R5_14 & R5_19 & R5_23 & R5_26 & Q5). clear P3.
    exists fx5, R5, M5. split.
    { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MS3. eapply msteps_trans. exact MS4. exact MS5. }
    split.
    { intros _. unfold at_body.
      assert (T5: forall i v, In i L5DIVNPU.KS_d5ul3c -> getr R4 (reg i) = v -> getr R5 (reg i) = v). { intros i v Hi Hv. rewrite (K5 i Hi). exact Hv. }
      split. apply T5; [kin | exact R4_2'].
      split. { apply T5; [kin|]. apply T4; [kin|kin|]. apply T2; [kin|kin|exact B18]. }
      split. { rewrite R5_19; f_equal; rewrite Nat2Z.inj_sub by lia; lia. }
      split. { apply T5; [kin|]. apply T4; [kin|kin|]. apply T2; [kin|kin|exact B20]. }
      split. { apply T5; [kin|]. apply T4; [kin|kin|]. apply T2; [kin|kin|exact B21]. }
      split. { apply T5; [kin|]. exact R4_22. }
      split. { rewrite R5_23; f_equal; rewrite Nat2Z.inj_sub by lia; lia. }
      split. { apply T5; [kin|]. apply T4; [kin|kin|]. apply T2; [kin|kin|exact B24]. }
      apply T5; [kin|]. apply T4; [kin|kin|]. apply T2; [kin|kin|exact B27]. }
    split. { rewrite (K5 2%nat) by kin. exact R4_2'. }
    split. { intros i Hi. rewrite (K5 i) by (pose proof Hi as H'; L5K.inlist H'). apply KEEP4. exact Hi. }
    split. { eapply FRAME_trans. exact FR14. intros a N1 N2 N3 N4. unfold inr in N2. apply FR5. lia. }
    eapply mem_grows_trans. eapply mem_grows_trans. exact MG1. exact MG3. eapply mem_grows_trans. exact MG4. exact MG5.
  - (* [comment removed for export] *)
    pose proof (L5DIVNPU.d5ul3x_conc fx4 R4 M4 (VL sp this denomd (Z.of_nat l + 1) quotd 0 0 0 (ks - 1) q' idx (Z.of_nat l) 0)) as P3.
    cbn [VL] in P3.
    destruct (P3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R4_2' R4_19 R4_22 R4_23 R4_25 ltac:(lia) A16
                 ltac:(eapply L5.writable_sub; [exact FW4 | lia | lia]) Q4 VQ4 ltac:(lia) ltac:(exact QA8) QSW QSD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (fx5 & R5 & M5 & MG5 & FR5 & _ & MS5 & K5 & R5_1 & R5_10 & R5_11 & R5_12 & R5_13 & R5_14 & R5_19 & R5_23 & R5_26 & Q5). clear P3.
    exists fx5, R5, M5. split.
    { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MS3. eapply msteps_trans. exact MS4. exact MS5. }
    split. { intros H'. exfalso. lia. }
    split. { rewrite (K5 2%nat) by kin. exact R4_2'. }
    split. { intros i Hi. rewrite (K5 i) by (pose proof Hi as H'; L5K.inlist H'). apply KEEP4. exact Hi. }
    split. { eapply FRAME_trans. exact FR14. intros a N1 N2 N3 N4. unfold inr in N2. apply FR5. lia. }
    eapply mem_grows_trans. eapply mem_grows_trans. exact MG1. exact MG3. eapply mem_grows_trans. exact MG4. exact MG5.
Qed.

(* [comment removed for export] *)
Lemma loop_ind (m : nat) : forall (k : nat) fx R M,
  (k = l + m)%nat -> (1 <= m)%nat -> (k <= n)%nat -> at_body R k -> minv M ->
  exists fx' R' M', msteps RSEGS (st fx R LBODY M) (st fx' R' LEXIT M')
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 352)
    /\ (forall i, In i loop_kept -> getr R' (reg i) = getr R (reg i))
    /\ FRAME M M' /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros k fx R M Hk Hm Hkn AB MI. exfalso; lia.
  destruct (iter fx R M k ltac:(lia) AB MI) as (fx1 & R1 & M1 & MS1 & AB1 & R1_2 & K1 & FR1 & MG1).
  destruct (Nat.lt_ge_cases (l + 1) k) as [Hlt|Hge].
  - assert (E: (l + 1 <? k)%nat = true) by (apply Nat.ltb_lt; exact Hlt). rewrite E in MS1.
    destruct (IH (k - 1)%nat fx1 R1 M1 ltac:(lia) ltac:(lia) ltac:(lia) (AB1 Hlt) (minv_step M M1 MI MG1 FR1)) as (fx2 & R2 & M2 & MS2 & R2_2 & K2 & FR2 & MG2).
    exists fx2, R2, M2. split. eapply msteps_trans. exact MS1. exact MS2.
    split. exact R2_2. split. { intros i Hi. rewrite (K2 i Hi). apply K1. exact Hi. }
    split. eapply FRAME_trans. exact FR1. exact FR2. eapply mem_grows_trans. exact MG1. exact MG2.
  - assert (E: (l + 1 <? k)%nat = false) by (apply Nat.ltb_ge; exact Hge). rewrite E in MS1.
    exists fx1, R1, M1. split. exact MS1. split. exact R1_2. split. exact K1. split. exact FR1. exact MG1.
Qed.

End Loop.

Theorem divloop_run : divloop_run_stmt.
Proof.
  unfold divloop_run_stmt. intros fx R M sp this remd quotd denomd d l n H2 H18 H21 H22 H23 VR VQ VD VS Wd Hd Hln Hthis A16 SPR
    RA8 RLO RHI RD RW QA8 QLO QHI QW DA8 DLO DHI DD FW QD AP1 AP2 AP3 AP4 AP5 AP6 AP7.
  destruct (Nat.lt_ge_cases l n) as [LT|GE].
  - (* [comment removed for export] *)
    pose proof (L5DIVNPU.d5upre_conc fx R M (VL sp this denomd (Z.of_nat l + 1) quotd 0 0 d (Z.of_nat n) 0 0 (Z.of_nat l) 0)) as P0. cbn [VL] in P0.
    destruct (P0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H2 H21 H22 H23 ltac:(lia) A16
                 ltac:(eapply L5.writable_sub; [exact FW | lia | lia]) VD VS ltac:(lia) ltac:(exact DA8)
                 Wd
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & R1_1 & R1_10 & R1_11 & R1_12 & R1_13 & R1_14 & R1_19 & R1_20 & R1_24 & R1_27). clear P0.
    assert (EM1: M1 = M). { apply FunctionalExtensionality.functional_extensionality. exact FR1. } subst M1.
    assert (AB: at_body sp this d l R1 n).
    { unfold at_body. split. rewrite (K1 2%nat) by kin. exact H2.
      split. rewrite (K1 18%nat) by kin. exact H18.
      split. rewrite R1_19; f_equal; lia.
      split. exact R1_20.
      split. rewrite (K1 21%nat) by kin. exact H21. split. rewrite (K1 22%nat) by kin. exact H22.
      split. rewrite (K1 23%nat) by kin. exact H23. split. exact R1_24. exact R1_27. }
    assert (MI: minv sp remd quotd denomd l n M). { constructor; assumption. }
    destruct (loop_ind sp this remd quotd denomd d l n Hd Hln Hthis A16 SPR RA8 RLO RHI QA8 QLO QHI DA8 DLO DHI AP1 AP2 AP3 AP4 AP5 AP6 AP7
                (n - l) n fx1 R1 M ltac:(lia) ltac:(lia) ltac:(lia) AB MI) as (fx2 & R2 & M2 & MS2 & R2_2 & K2 & FR2 & MG2).
    exists fx2, R2, M2. split. eapply msteps_trans. exact MS1. exact MS2.
    split. exact R2_2. split. { intros i Hi. rewrite (K2 i Hi). apply K1. pose proof Hi as H'; L5K.inlist H'. }
    split. { intros a N1 N2 N3 N4. apply FR2; assumption. } exact MG2.
  - (* [comment removed for export] *)
    pose proof (L5DIVNPU.d5uprx_conc fx R M (VL sp this denomd (Z.of_nat l + 1) quotd 0 0 0 (Z.of_nat n) 0 0 (Z.of_nat l) 0)) as P0. cbn [VL] in P0.
    destruct (P0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H2 H21 H22 H23 ltac:(lia) A16
                 ltac:(eapply L5.writable_sub; [exact FW | lia | lia]) VD VS ltac:(lia) ltac:(exact DA8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & _). clear P0.
    exists fx1, R1, M1. split. exact MS1. split. rewrite (K1 2%nat) by kin. exact H2.
    split. { intros i Hi. apply K1. pose proof Hi as H'; L5K.inlist H'. }
    split. { intros a _ _ _ _. apply FR1. } exact MG1.
Qed.

End SCFG_1.
End L5DIVLOOPU.
