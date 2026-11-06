(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
 AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
 Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU L5Defs L5CoreKit L5Kn
 L5Core L5CoreSpecsU L5CoreKitU L5Words L5WordsB L5ReduceU L5ReduceGU L5DDqU L5SubMulU L5ShlU L5MulMU L5Hp L5NormU
 L5DivSpecsU L5DivPartsU L5DivNPU L5DivO2PU L5DivO2SU L5DivTailU L5DivO2AU L5DivO2CU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2DU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVO2PU. Import L5DO2SU. Import L5DIVO2AU. Import L5DIVO2CU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac uSCR := unfold DIVO2_SCR, UNNORM_SCR, DIVEQ_SCR, DIV_SCR, L5NORMU.NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR,
  RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; lia.
Local Ltac fsclia := prune_impl; prune_disj; uSCR; lia.
(* [comment removed for export] *)
Local Ltac dlia := prune_impl; prune_disj; intros; repeat match goal with |- _ /\ _ => split end; lia.

Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis COPYA : copya_spec L HI.
Hypothesis ASSIGN : assign_spec L HI.
Hypothesis RESIZE : resize_spec L HI.
Hypothesis OPDEL : opdel_sized_spec L HI.
Hypothesis NORM : L5NORMU.norm_spec L HI.
Hypothesis UNNORMS : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.
Hypothesis DIVTAIL : divtail_stmt L HI.
Hypothesis DIVTAIL2 : L5DIVTAILU.divtail2_stmt L HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (Y Q A fba sp r : Z) (by_ : L5.bigobj) (wy : list Z).
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 Y.
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 A.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 Q.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 Y.
Hypothesis G14 : getr R0 14%bv = Z_to_bv 64 1.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 sp DIVO2_SCR.
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis YOK : y_ok LB M0 Y by_ wy.
Hypothesis LEN1 : (1 <= L5.bo_len by_)%nat.
Hypothesis CAPY : L5.bo_cap by_ <= 268.
Hypothesis AY8 : Y mod 8 = 0.
Hypothesis SY : sp + 48 <= Y.
Hypothesis HY : Y + 32 <= hl_sptop L.
Hypothesis WRY : L5.writable RSEGS M0 Y 32.
Hypothesis WRB : forall cap q, L5.bo_st by_ = L5.BDyn cap q -> L5.writable RSEGS M0 q (8 * cap).
Hypothesis AOK : a_ok M0 A fba.
Hypothesis AA8 : A mod 8 = 0.
Hypothesis SA : sp + 48 <= A.
Hypothesis HA : A + 32 <= hl_sptop L.
Hypothesis ZQ : zero_obj M0 Q.
Hypothesis AQ8 : Q mod 8 = 0.
Hypothesis SQ : sp <= Q.
Hypothesis HQ : Q + 32 <= hl_sptop L.
Hypothesis WRQ : L5.writable RSEGS M0 Q 32.
Hypothesis AP1 : Y + 32 <= A \/ A + 32 <= Y.
Hypothesis AP2 : Q + 32 <= Y.
Hypothesis AP3 : Q + 32 <= A.
Hypothesis CR : credit_for L cr DIVO2_K (divO2_bytes (L5.bo_cap by_)).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divO2_post L LB cr M0 M' R0 R' Y Q A fba sp by_ LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.

(* [comment removed for export] *)
Let Ln : nat := L5.bo_len by_.
Let fbY : Z := L5.bo_fb by_.
Let sty : L5.bstore := L5.bo_st by_.
Let capy : Z := L5.bo_cap by_.
Let yd0 : Z := L5.bo_data Y by_.
Let spd : Z := sp - 352.
Let WN : list L5.range := [(Y, 32); (yd0, 8 * capy); (Q, 32)].
Let Vd := VdO sp Y Q A fbY R0.
(* [comment removed for export] *)
Let IMG := @L5DIVO2AU.IMG L LY.
Let IMGLO := @L5DIVO2AU.IMGLO L LY.
Let ERRNO := @L5DIVO2AU.ERRNO L LY R0 Y Q A sp by_ LEN1.
Let ERRNOV := @L5DIVO2AU.ERRNOV L LY.
Let SPTOP := @L5DIVO2AU.SPTOP L M0 sp STK.
Let DIVO2_SCR_val := L5DIVO2AU.DIVO2_SCR_val.
Let SPW := @L5DIVO2AU.SPW L R0 M0 Y Q A sp by_ STK LEN1 AY8 SY AA8 SA HA AQ8 SQ.
Let LBhi := @L5DIVO2AU.LBhi _ L HI HIok.
Let LBdef := @L5DIVO2AU.LBdef _ L HI HIok.
Let LBapart := @L5DIVO2AU.LBapart _ L HI HIok.
Let UR1 := @L5DIVO2AU.UR1 R0 Y Q A sp r by_ G1 RA LEN1.
Let YB := @L5DIVO2AU.YB M0 LB Y by_ wy YOK.
Let fbY_rng := @L5DIVO2AU.fbY_rng M0 LB Y by_ wy YOK.
Let capy_rng := @L5DIVO2AU.capy_rng R0 M0 LB Y Q A sp by_ wy YOK LEN1 CAPY WRB.
Let Ln_le := @L5DIVO2AU.Ln_le M0 LB Y by_ wy YOK LEN1 WRB.
Let credit_debit64 := @L5DIVO2CU.credit_debit64 L M0 LB cr Y Q A sp by_ wy YOK LEN1 WRB.
Let credit_weaken := @L5DIVO2CU.credit_weaken L KPOS BPOS R0 M0 LB cr Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ.
Let credit_ok64 := @L5DIVO2CU.credit_ok64 L KPOS BPOS R0 M0 LB cr Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ CR.
Let lb_free_cons_ne := @L5DIVO2CU.lb_free_cons_ne.
Let fresh_ne := @L5DIVO2CU.fresh_ne L R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
Let ends_sameQ := @L5DIVO2CU.ends_sameQ L.
Let stage_G9 := @L5DIVO2CU.stage_G9 _ L HI LY HIok KPOS BPOS RESIZE UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G8 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg : Z) (fbR : Z) (nn : nat) (stR : L5.bstore) (wsY : list Z) (fq : Z) (stq : L5.bstore) (wsQ : list Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y ->
  getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat nn) -> (2 <= nn <= 298)%nat -> (nn <= Ln + 1)%nat ->
  match stR with L5.BDyn cap _ => Z.of_nat nn + 1 <= cap | L5.BInl _ _ => nn = 2%nat end ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr (DIVO2_K - DIVN_K - 2) (divO2_bytes capy - DIVN_BYTES - 128) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad -> marksO2 M sp Y (Z.land fbY 2) qneg -> 0 <= qneg <= 1 ->
  L5.u64_at RSEGS M (sp - 296) (Z.of_nat nn) -> L5.u64_at RSEGS M (sp - 224) (Z.of_nat nn - 2) -> L5.u64_at RSEGS M (sp - 152) Ad -> L5.u64_at RSEGS M (sp - 144) 2 ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (forall cap q, stR = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) -> (forall cap q, stq = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  L5.big_at RSEGS M Y (L5.BO fbR nn stR) -> L5C.obj_limbs RSEGS M (L5.BO fbR nn stR) wsY -> Z.testbit fbR 1 = false ->
  L5.defined M Y 32 -> L5.defined M (L5.bo_data Y (L5.BO fbR nn stR)) (8 * L5.bo_cap (L5.BO fbR nn stR)) ->
  (forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) (ob eb ++ LB)) ->
  L5.big_at RSEGS M Q (L5.BO fq (nn - 2) stq) -> L5C.obj_limbs RSEGS M (L5.BO fq (nn - 2) stq) wsQ ->
  L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq (nn - 2) stq)) (8 * L5.bo_cap (L5.BO fq (nn - 2) stq)) ->
  (forall cap q, stq = L5.BDyn cap q -> Z.of_nat nn - 1 <= cap) ->
  ends L LB sty stR stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x228b0 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H21 H22 H24 Hn NNLE YFIT MBV HH ELB CRA DS LOC MK Hq VRS VQS VD VS IN1 IN2 IN3 LBF INAd DD1 ADY ADQ OBY OLY SGN DY DYD INR OBQ OLQ DQ DQD QCAP ENDS DEB IMG1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16). rewrite IMG, IMGLO in Adimg.
  assert (INR': forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) LBc).
  { intros cap q E. subst LBc. destruct (in_app_or _ _ _ (INR cap q E)) as [X|X]. apply in_app_iff. left; exact X. apply in_app_iff. right. apply in_app_iff. right. exact X. }
  pose proof OBY as (Yb0 & Yfr & Yb8 & YST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Yb0, Yfr, Yb8, YST.
  pose proof OBQ as (Qb0 & Qfr & Qb8 & QST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qb0, Qfr, Qb8, QST.
  pose proof MK as (C320 & C328 & C336 & C284 & C344).
  (* [comment removed for export] *)
  pose proof (d5ug8_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 (Z.of_nat nn) 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) H2 H8 ltac:(flia) A16 ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0 | flia | flia] | flia | flia])
              VRS ltac:(flia))
    as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & B1 & B10 & B11). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  replace (Z.of_nat nn + 1) with (Z.of_nat (nn + 1)%nat) in B11 by flia.
  eapply (RESIZE fx1 R1 M model K LBc crc Y spd 0x228c0 (nn + 1)%nat (L5.BO fbR nn stR) wsY HH MOK HK0).
  - rewrite r10. exact B10.
  - rewrite r11. exact B11.
  - flia.
  - unfold L5.bo_dyn, L5.bo_cap. cbn [L5.bo_fb L5.bo_st]. intros DQY. destruct stR as [v0 v1|capR rd]. { destruct YST as (Ytb & _). rewrite Ytb in DQY. discriminate. } flia.
  - intros H3n Hd. unfold L5.bo_dyn in Hd. cbn [L5.bo_fb] in Hd. destruct stR as [v0 v1|capR rd]. 2:{ destruct YST as (Ytb & _). rewrite Ytb in Hd. discriminate Hd. }
    rewrite YFIT. unfold round_up. change (8 * (8 * (Z.of_nat (2 + 1) / 8) + 8)) with 64.
    eapply credit_ok64. exact CRA. unfold DIVO2_K, DIVN_K; flia. unfold divO2_bytes, DIVN_BYTES; flia.
  - rewrite r1. exact B1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (K1 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd. fsclia. split. unfold spd. flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact OBY.
  - exact OLY.
  - exact AY8.
  - unfold spd. flia.
  - exact HY.
  - apply (L5C.writable_of_defined RSEGS). exact DY. flia. flia.
  - cbn [L5.bo_st]. exact INR'.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
    destruct POST as (RP2 & GPOST).
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 spd). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
    assert (E3: getr R2 (reg 3) = Z_to_bv 64 GP). { rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3. }
    assert (E4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4. }
    assert (E9: getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
    assert (E18: getr R2 (reg 18) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 18 RP2) by inl. rewrite (K1 18%nat) by inl. exact H18. }
    assert (E8: getr R2 (reg 8) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 8 RP2) by inl. rewrite (K1 8%nat) by inl. exact H8. }
    assert (E21: getr R2 (reg 21) = Z_to_bv 64 2). { rewrite (preserved_sregs R1 R2 21 RP2) by inl. rewrite (K1 21%nat) by inl. exact H21. }
    assert (E22: getr R2 (reg 22) = Z_to_bv 64 1). { rewrite (preserved_sregs R1 R2 22 RP2) by inl. rewrite (K1 22%nat) by inl. exact H22. }
    assert (E24: getr R2 (reg 24) = Z_to_bv 64 (Z.of_nat nn)). { rewrite (preserved_sregs R1 R2 24 RP2) by inl. rewrite (K1 24%nat) by inl. exact H24. }
    (* [comment removed for export] *)
    assert (NQA: forall a, match stq with L5.BInl _ _ => Q + 16 <= a < Q + 32 | L5.BDyn cap q => q <= a < q + 8 * cap end ->
              (sp - 352 <= a < hl_sptop L /\ ~ (Y <= a < Y + 32) /\ forall cap q, stR = L5.BDyn cap q -> ~ (q <= a < q + 8 * cap)) \/ (in_block LBc a /\ a < hl_ceil L /\ forall cap q, stR = L5.BDyn cap q -> ~ (q <= a < q + 8 * cap))).
    { intros a Ha. destruct stq as [q0 q1|cq qq].
      - left. split. unfold hl_ceil in *; flia. split. flia. intros cap q ->. pose proof (LBhi _ _ _ _ HH _ (INR' cap q eq_refl)) as BH. cbn in BH. unfold hl_ceil in *; flia.
      - unfold ends in ENDS. destruct ENDS as (Eeb & BR & BA & CQ & SM). assert (INq: In (qq, 8 * cq) LBc) by (subst LBc eb; left; reflexivity).
        pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & _ & Qhi & _). right. split. exists (qq, 8 * cq). split. exact INq. cbn. flia. split. flia.
        intros cap q ->. unfold sty in SM. pose proof YOK as (_ & _ & _ & BLK). destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM, BLK. exfalso; exact SM.
        destruct SM as [-> ->]. pose proof (BA _ (proj1 BLK)) as X. cbn in X. generalize X; flia. }
    destruct g as [|Ag cap].
    + (* [comment removed for export] *)
      destruct GPOST as (SAMEC & -> & -> & (st' & OBY2 & OLY2 & SM2) & HP2). cbn [L5.bo_fb L5.bo_st L5.bo_data L5.bo_len] in OBY2, OLY2, SM2, HP2.
      destruct stR as [v0 v1|capR rd]. { exfalso. rewrite YFIT in SAMEC. destruct SAMEC as [DQY|Hle2]. unfold L5.bo_dyn in DQY. cbn [L5.bo_fb] in DQY. destruct YST as (Ytb & _). rewrite Ytb in DQY. discriminate DQY. flia. }
      destruct st' as [v0' v1'|capR' rd']. exfalso; exact SM2. destruct SM2 as [-> ->]. cbn [L5.bo_data L5.bo_cap L5.bo_st] in HP2, DYD.
      pose proof (LBdef _ _ _ _ HH rd (8 * capR) (INR' capR rd eq_refl)) as (_ & (RDlo & RDimg) & RDhi & RDpos & RD16). rewrite IMG, IMGLO in RDimg.
      assert (KST2: forall a, sp - 352 <= a < 2 ^ 64 -> ~ (Y <= a < Y + 32) -> ~ (rd <= a < rd + 8 * capR) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NY ND. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng. cbn [fst snd]. flia. }
      assert (KBL2: forall A0 n a, In (A0, n) LBc -> A0 <> rd -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros A0 n a Hin NQ Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_cons. 2: apply L5C.outside_nil.
        unfold L5.in_rng. cbn [fst snd]. pose proof (LBapart _ _ _ _ HH _ (INR' capR rd eq_refl)) as BA. cbn [fst snd] in BA.
        specialize (BA _ (L5C.in_lb_remove_neq _ _ _ _ Hin NQ)). cbn in BA. generalize BA; flia. }
      assert (KFR2: forall i, sp - 352 <= i < sp -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KST2. flia. flia. unfold hl_ceil in *; flia. }
      assert (CDEF2: forall a n, L5.defined M a n -> (forall i, a <= i < a + n -> sp - 352 <= i < hl_sptop L \/ in_block LBc i) -> L5.defined M2 a n).
      { intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
        - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
        - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
          apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
      assert (NQR: forall cap q, stq = L5.BDyn cap q -> q <> rd).
      { intros cap q ->. unfold ends in ENDS. destruct ENDS as (_ & _ & BA & CQ & SM). unfold sty in SM. pose proof YOK as (_ & _ & _ & BLK).
        destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM, BLK. exfalso; exact SM. destruct SM as [-> ->].
        pose proof (BA _ (proj1 BLK)) as X. cbn in X. pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & _ & _ & Pn & _). generalize X; flia. }
      eapply (stage_G9 fx2 R2 M2 model2 LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg fbR nn capR rd fq stq wsQ
                E2 E3 E4 E8 E9 E18 E21 E22 E24 Hn NNLE (L5C.model_but_vm_trans _ _ _ MBV MBV2) HH2 ELB
                (credit_weaken _ (DIVO2_K - DIVN_K - 1) _ (divO2_bytes capy - DIVN_BYTES - 64) _ CRA ltac:(unfold DIVO2_K, DIVN_K; flia) ltac:(unfold divO2_bytes, DIVN_BYTES; flia))).
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply marksO2_kept. 4: exact MK. intros i Hi; destruct Hi as [Hi|Hi]; apply KFR2; flia. flia. flia.
      * exact Hq.
      * eapply u64_at_agree1. 4: exact VQS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KFR2; flia. flia. flia.
      * exact IN1. * exact IN2. * exact IN3. * exact LBF. * exact INAd.
      * eapply u64_at_agree1. 4: exact DD1. 2: flia. 2: unfold hl_ceil in *; flia. intros i Hi. apply (KBL2 Ad 64). exact INAd'. 2: flia.
        pose proof (ADY capR rd eq_refl) as X. intros ->. generalize X; flia.
      * exact (ADY capR rd eq_refl).
      * exact ADQ.
      * replace (S nn) with (nn + 1)%nat by flia. exact OBY2.
      * exact SGN.
      * apply CDEF2. exact DY. intros i Hi. left. unfold hl_ceil in *. flia.
      * apply CDEF2. exact DYD. intros i Hi. right. exists (rd, 8 * capR). split. exact (INR' capR rd eq_refl). cbn. flia.
      * exact (INR capR rd eq_refl).
      * eapply big_at_agree1. 4: exact OBQ. 2: flia. 2: flia. intros i Hi. apply KST2. flia. flia. unfold hl_ceil in *; flia.
      * (* [comment removed for export] *)
        pose proof OLQ as (QL1 & QL2 & QL3). cbn [L5.bo_len L5.bo_st] in QL1, QL2, QL3. split. exact QL1. split. exact QL2. cbn [L5.bo_st].
        destruct stq as [q0 q1|cq qq]. exact QL3. eapply limbs_at_agree1. 4: exact QL3. 2,3: destruct QST as (_ & _ & _ & QHle & QHcap & Qq8 & Qqlo & Qqhi & _); flia.
        intros i Hi. rewrite QL1 in Hi. destruct (NQA i ltac:(destruct QST as (_ & _ & _ & QHle & _); flia)) as [(ST & NY & NR)|(IB & LO & NR)].
        -- apply KST2. flia. exact NY. exact (NR capR rd eq_refl).
        -- apply (KBL2 qq (8 * cq)). unfold ends in ENDS; destruct ENDS as (Eeb & _); subst LBc eb; left; reflexivity. exact (NQR cq qq eq_refl). destruct QST as (_ & _ & _ & QHle & _). flia.
      * apply CDEF2. exact DQ. intros i Hi. left. unfold hl_ceil in *. flia.
      * apply CDEF2. exact DQD. intros i Hi. destruct (NQA i ltac:(destruct stq; cbn [L5.bo_data L5.bo_cap L5.bo_st] in Hi |- *; flia)) as [(ST & _)|(IB & _)]. left; exact ST. right; exact IB.
      * exact QCAP.
      * apply (ends_same _ _ _ _ (L5.BDyn capR rd) _ _ ENDS). split; reflexivity.
      * intros b Hb. apply CDEF2. exact (DEB b Hb). intros i Hi. right. exists b. split. subst LBc. apply in_app_iff. left. exact Hb. destruct b; cbn in Hi |- *; flia.
      * eapply img_clear_kept. exact HP2. exact LY. 2: exact IMG1. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
        apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng. cbn [fst snd]. generalize RDimg; flia.
      * eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd RESIZE_SCR). exact HP. exact HP2.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
           intros OW. apply L5C.outside_cons. exact (OW _ ltac:(left; reflexivity)). apply L5C.outside_cons. 2: apply L5C.outside_nil.
           unfold L5.in_rng. cbn [fst snd].
           (* [comment removed for export] *)
           assert (OWD: ~ (yd0 <= a < yd0 + 8 * capy)) by exact (OW _ ltac:(right; left; reflexivity)).
           unfold yd0, capy, L5.bo_data, L5.bo_cap in OWD. unfold ends in ENDS. unfold sty in ENDS.
           destruct stq as [q0 q1|cq qq]; destruct (L5.bo_st by_) as [y0 y1|cy qy] in ENDS, OWD |- *.
           ++ destruct ENDS as (-> & -> & BR & BA). intros C. refine (L5C.kept_not_fresh L LB sp DIVO2_SCR WN a rd 64 KA BA _ _ (LBhi _ _ _ _ HH0) _).
              exact (proj1 (proj2 BR)). exact (proj2 (proj2 (proj2 (proj2 BR)))). flia.
           ++ destruct ENDS as (-> & -> & _). flia.
           ++ destruct ENDS as (_ & _ & _ & _ & SM). exfalso; exact SM.
           ++ destruct ENDS as (-> & _ & _ & _ & (-> & ->)). flia.
        -- intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb.
        -- unfold spd; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
    + (* [comment removed for export] *)
      destruct GPOST as (DQF & H3n & Ecap & -> & -> & FB & OBY2 & OLY2 & HP2). cbn [L5.bo_fb L5.bo_dyn] in DQF, OBY2, OLY2.
      destruct stR as [v0 v1|capR0 rd0]. 2:{ exfalso. unfold L5.bo_dyn in DQF. cbn [L5.bo_fb] in DQF. destruct YST as (Ytb & _). rewrite Ytb in DQF. discriminate DQF. }
      rewrite YFIT in *. assert (CAP8: cap = 8). { rewrite Ecap. reflexivity. } clear Ecap. subst cap.
      assert (EBN: eb = None /\ match sty with L5.BInl _ _ => True | _ => False end /\ match stq with L5.BInl _ _ => True | _ => False end).
      { unfold ends in ENDS. unfold sty in ENDS |- *. destruct stq as [q0 q1|cq qq]. 2:{ destruct ENDS as (_ & _ & _ & _ & SM). destruct (L5.bo_st by_) in SM; exfalso; exact SM. }
        destruct (L5.bo_st by_) as [y0 y1|cy qy] in ENDS |- *. split. exact ENDS. split; exact I. exfalso; exact ENDS. }
      destruct EBN as (-> & STYI & STQI). cbn [ob app] in ELB.
      pose proof FB as (FBR & FBA & FBD). change (8 * 8) with 64 in FBR, FBA, FBD, HH2, OBY2, OLY2 |- *.
      assert (KST2: forall a, sp - 352 <= a < 2 ^ 64 -> ~ (Y <= a < Y + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NQ. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
      assert (KBL2: forall A0 n a, In (A0, n) LBc -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_nil. }
      assert (KFR2: forall i, sp - 352 <= i < sp -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KST2; flia. }
      assert (NE1: Z.testbit fn0 0 = true -> Ag <> p1).
      { intros T. pose proof LOC as (_ & _ & _ & LO1 & _). destruct LO1 as (_ & _ & LD). destruct (LD T) as (_ & Hc & _). eapply fresh_ne. exact FB. exact (IN1 T). flia. }
      assert (NE2: Z.testbit fnum 0 = true -> Ag <> p2).
      { intros T. pose proof LOC as (_ & _ & _ & _ & LO2 & _). destruct LO2 as (_ & _ & LD). destruct (LD T) as (_ & Hc & _). eapply fresh_ne. exact FB.
        apply (L5DIVTAILU.in_lb_free _ fn0 p1). exact (IN2 T). flia. }
      assert (NE3: Ag <> Ad). { eapply fresh_ne. exact FB. exact INAd'. flia. }
      pose proof (FBA _ INAd') as APd. cbn in APd.
      eapply (stage_G9 fx2 R2 M2 model2 ((Ag, 64) :: LBc) TB (debit L crc 64) (Some (Ag, 64)) fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg (Z.lor fbR 1) 2%nat 8 Ag fq stq wsQ
                E2 E3 E4 E8 E9 E18 E21 E22 E24 Hn NNLE (L5C.model_but_vm_trans _ _ _ MBV MBV2) HH2).
      * rewrite ELB. reflexivity.
      * eapply credit_weaken. apply credit_debit64. exact CRA. unfold DIVO2_K, DIVN_K; flia. unfold divO2_bytes, DIVN_BYTES; flia.
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply marksO2_kept. 4: exact MK. intros i Hi; destruct Hi as [Hi|Hi]; apply KFR2; flia. flia. flia.
      * exact Hq.
      * eapply u64_at_agree1. 4: exact VQS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KFR2; flia. flia. flia.
      * intros T. right. exact (IN1 T).
      * intros T. rewrite (lb_free_cons_ne fn0 p1 Ag 64 LBc NE1). right. exact (IN2 T).
      * rewrite (lb_free_cons_ne fn0 p1 Ag 64 LBc NE1). rewrite (lb_free_cons_ne fnum p2 Ag 64 _ NE2). right. exact IN3.
      * rewrite (lb_free_cons_ne fn0 p1 Ag 64 LBc NE1). rewrite (lb_free_cons_ne fnum p2 Ag 64 _ NE2). rewrite (lb_remove_skip Ad Ag 64) by exact NE3. rewrite LBF. reflexivity.
      * exact INAd.
      * eapply u64_at_agree1. 4: exact DD1. intros i Hi; apply (KBL2 Ad 64); [exact INAd' | flia]. flia. unfold hl_ceil in *; flia.
      * generalize APd; flia.
      * exact ADQ.
      * replace (S 2) with (2 + 1)%nat by reflexivity. exact OBY2.
      * rewrite Z.lor_spec, SGN. reflexivity.
      * intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Y + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DY. exact Hi.
      * exact FBD.
      * left. reflexivity.
      * eapply big_at_agree1. 4: exact OBQ. intros i Hi; apply KST2; flia. flia. flia.
      * pose proof OLQ as (QL1 & QL2 & QL3). cbn [L5.bo_len L5.bo_st] in QL1, QL2, QL3. split. exact QL1. split. exact QL2. cbn [L5.bo_st].
        destruct stq as [q0 q1|cq qq]. exact QL3. destruct STQI.
      * intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Q + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DQ. exact Hi.
      * destruct stq as [q0 q1|cq qq]. 2: destruct STQI. cbn [L5.bo_data L5.bo_cap L5.bo_st] in DQD |- *.
        intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Q + 16 + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DQD. exact Hi.
      * exact QCAP.
      * unfold ends. destruct stq as [q0 q1|cq qq]. 2: destruct STQI. unfold sty in STYI |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in STYI |- *. 2: destruct STYI.
        split. reflexivity. split. reflexivity. split. exact FBR. intros b Hb. apply FBA. subst LBc. apply in_app_iff. right. exact Hb.
      * intros b [<-|[]]. cbn [fst snd]. exact FBD.
      * eapply img_clear_kept. exact HP2. exact LY. 2: exact IMG1. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil.
      * eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd RESIZE_SCR). exact HP. exact HP2.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. rewrite !in_app_iff. right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
           intros OW. apply L5C.outside_cons. exact (OW _ ltac:(left; reflexivity)). apply L5C.outside_nil.
        -- intros b Hb. subst LBc. rewrite !in_app_iff. right; exact Hb.
        -- unfold spd; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
Qed.



End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2DU.
