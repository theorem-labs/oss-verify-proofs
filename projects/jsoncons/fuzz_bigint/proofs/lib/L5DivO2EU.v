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
 L5DivSpecsU L5DivPartsU L5DivNPU L5DivO2PU L5DivO2SU L5DivTailU L5DivO2AU L5DivO2BU L5DivO2CU L5DivO2DU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2EU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVO2PU. Import L5DO2SU. Import L5DIVO2AU. Import L5DIVO2BU. Import L5DIVO2CU. Import L5DIVO2DU.

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
Let stage_L := @L5DIVO2BU.stage_L _ L HI LY HIok UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
Let credit_weaken := @L5DIVO2CU.credit_weaken L KPOS BPOS R0 M0 LB cr Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ.
Let stage_G8 := @L5DIVO2DU.stage_G8 _ L HI LY HIok KPOS BPOS RESIZE UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G7 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg : Z) (fbR : Z) (nn : nat) (stR : L5.bstore) (wsY : list Z) (fq : Z) (stq : L5.bstore) (wsQ : list Z) (quotd : Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y ->
  getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat nn) ->
  getr R (reg 25) = Z_to_bv 64 (Z.land fbY 2) -> getr R (reg 26) = Z_to_bv 64 qneg ->
  (2 <= nn)%nat -> (nn <= Ln + 1)%nat -> 0 <= qneg <= 1 ->
  (nn = S Ln -> nth_w wsY (nn - 1) < 4) ->
  match stR with L5.BDyn cap _ => Z.of_nat Ln + 1 <= cap | L5.BInl _ _ => True end ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr (DIVO2_K - DIVN_K - 2) (divO2_bytes capy - DIVN_BYTES - 128) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad ->
  L5.u32_at RSEGS M (sp - 284) 2 -> L5.u64_at RSEGS M (sp - 344) 0 ->
  L5.u64_at RSEGS M (sp - 152) Ad -> L5.u64_at RSEGS M (sp - 144) 2 -> L5.u64_at RSEGS M (sp - 232) quotd -> L5.u64_at RSEGS M (sp - 224) (Z.of_nat nn - 2) ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (forall cap q, stR = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) -> (forall cap q, stq = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  L5.big_at RSEGS M Y (L5.BO fbR nn stR) -> L5C.obj_limbs RSEGS M (L5.BO fbR nn stR) wsY -> Z.testbit fbR 1 = false ->
  L5.defined M Y 32 -> L5.defined M (L5.bo_data Y (L5.BO fbR nn stR)) (8 * L5.bo_cap (L5.BO fbR nn stR)) ->
  (forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) (ob eb ++ LB)) ->
  L5.big_at RSEGS M Q (L5.BO fq (nn - 2) stq) -> L5C.obj_limbs RSEGS M (L5.BO fq (nn - 2) stq) wsQ ->
  L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq (nn - 2) stq)) (8 * L5.bo_cap (L5.BO fq (nn - 2) stq)) ->
  quotd = L5.bo_data Q (L5.BO fq (nn - 2) stq) -> (forall cap q, stq = L5.BDyn cap q -> Z.of_nat nn - 1 <= cap) ->
  ends L LB sty stR stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22854 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H21 H23 H24 H25 H26 Hn NNLE Hq TOPW YCAP MBV HH ELB CRA DS LOC C284 C344 VD VS VQ VQS IN1 IN2 IN3 LBF INAd DD1 ADY ADQ OBY OLY SGN DY DYD INR OBQ OLQ DQ DQD Equotd QCAP ENDS DEB IMG1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR. pose proof D1_range as (D1R & D1ge).
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16). rewrite IMG, IMGLO in Adimg.
  assert (INR': forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) LBc).
  { intros cap q E. subst LBc. destruct (in_app_or _ _ _ (INR cap q E)) as [X|X]. apply in_app_iff. left; exact X. apply in_app_iff. right. apply in_app_iff. right. exact X. }
  pose proof OBY as (Yb0 & Yfr & Yb8 & YST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Yb0, Yfr, Yb8, YST.
  pose proof OLY as (YL1 & YL2 & YL3). cbn [L5.bo_len L5.bo_st] in YL1, YL2, YL3.
  pose proof (land2_rng fbY (proj1 FBY)) as S2.
  (* [comment removed for export] *)
  assert (NN: (nn <= 269)%nat). { unfold sty in LNS. unfold capy in CAPR. unfold L5.bo_cap in CAPR. destruct (L5.bo_st by_) as [y0 y1|cy qy] in LNS, CAPR; flia. }
  (* [comment removed for export] *)
  set (w := nth_w wsY (nn - 1)).
  assert (WR: 0 <= w < 2 ^ 64). { subst w. apply words_ok_nth. exact YL2. }
  assert (WAT: match stR with L5.BInl _ _ => nn = 2%nat /\ L5.u64_at RSEGS M (Y + 8 * Z.of_nat nn + 8) w
                              | L5.BDyn cap rd => L5.u64_at RSEGS M (8 * Z.of_nat nn + rd - 8) w /\ L5.u64_at RSEGS M (Y + 24) rd /\ 4096 <= rd /\ rd + 8 * cap <= hl_ceil L /\ rd mod 16 = 0 /\ Z.of_nat nn <= cap end).
  { destruct stR as [v0 v1|capR rd].
    - destruct YST as (Ytb & Yv0 & Yv1 & YHl2 & _). assert (E2: nn = 2%nat) by flia. split. exact E2.
      subst w. rewrite YL3, E2. cbn [nth_w nth firstn]. exactA Yv1.
    - destruct YST as (Ytb & Y16 & Y24 & YHle & YHcap & Yq8 & Yqlo & Yqhi & _).
      pose proof (LBdef _ _ _ _ HH rd (8 * capR) (INR' capR rd eq_refl)) as (_ & (RDlo & _) & RDhi & _ & RD16).
      split. { subst w. pose proof (YL3 (nn - 1)%nat ltac:(rewrite YL1; flia)) as X. replace (rd + 8 * Z.of_nat (nn - 1)%nat) with (8 * Z.of_nat nn + rd - 8) in X by flia. exact X. }
      split. exact Y24. split. exact RDlo. split. exact RDhi. split. exact RD16. exact YHle. }
  (* [comment removed for export] *)
  assert (PC: exists fx1 R1 M1, mem_grows M M1
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 336 <= i < sp - 288) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R 0x22854 M) (st fx1 R1 (if w <? D1 then PRE else 0x228b0) M1)
            /\ getr R1 (reg 2) = Z_to_bv 64 spd /\ getr R1 (reg 3) = Z_to_bv 64 GP /\ getr R1 (reg 4) = Z_to_bv 64 TP
            /\ getr R1 (reg 8) = Z_to_bv 64 Y /\ getr R1 (reg 9) = Z_to_bv 64 Q /\ getr R1 (reg 18) = Z_to_bv 64 Y
            /\ getr R1 (reg 21) = Z_to_bv 64 2 /\ getr R1 (reg 22) = Z_to_bv 64 1 /\ getr R1 (reg 23) = Z_to_bv 64 (Z.of_nat nn - 1) /\ getr R1 (reg 24) = Z_to_bv 64 (Z.of_nat nn)
            /\ L5.u64_at RSEGS M1 (sp - 296) (Z.of_nat nn) /\ L5.u64_at RSEGS M1 (sp - 304) (L5.bo_data Y (L5.BO fbR nn stR))
            /\ L5.u64_at RSEGS M1 (sp - 320) (Z.land fbY 2) /\ L5.u64_at RSEGS M1 (sp - 328) qneg /\ L5.u64_at RSEGS M1 (sp - 336) 1).
  { assert (WRF: L5.writable RSEGS M (sp - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
    destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_st].
    - destruct WAT as [E2 Uw]. destruct YST as (Ytb & _).
      destruct (Z.ltb_spec w D1) as [LT|GE].
      + pose proof (d7ug7i0_conc fx R M (Vd 0 0 0 0 0 0 0 0 qneg (Z.of_nat nn) Ad 0 0 0 fbR 0 w)) as P. cbn [Vd VdO] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WRF VD VS ltac:(unfold hl_ceil in *; flia) (mod16_mod8 Ad Ad16) ltac:(right; unfold hl_ceil in *; flia) DD1 ltac:(flia)
                    ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia) ltac:(exactA Yb8) Ytb ltac:(exactA Uw) ltac:(flia) ltac:(flia) LT ltac:(flia) Hq S2 ltac:(flia))
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & B1 & B10 & B11 & B12 & B13 & B14 & B19 & B22 & B23 & C296 & C304 & C320 & C328 & C336). clear P.
        exists fx1, R1, M1. split. exact MG1. split. { intros i Hi Hn'. apply FR1. exact Hi. flia. flia. } split. exact MS1.
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 21%nat), (K1 24%nat) by inl.
        repeat split; try assumption.
      + pose proof (d7ug7i1_conc fx R M (Vd 0 0 0 0 0 0 0 0 qneg (Z.of_nat nn) Ad 0 0 0 fbR 0 w)) as P. cbn [Vd VdO] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WRF VD VS ltac:(unfold hl_ceil in *; flia) (mod16_mod8 Ad Ad16) ltac:(right; unfold hl_ceil in *; flia) DD1 ltac:(flia)
                    ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia) ltac:(exactA Yb8) Ytb ltac:(exactA Uw) ltac:(flia) ltac:(flia) GE ltac:(flia) Hq S2 ltac:(flia))
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & B1 & B10 & B11 & B12 & B13 & B14 & B19 & B22 & B23 & C296 & C304 & C320 & C328 & C336). clear P.
        exists fx1, R1, M1. split. exact MG1. split. { intros i Hi Hn'. apply FR1. exact Hi. flia. flia. } split. exact MS1.
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 21%nat), (K1 24%nat) by inl.
        repeat split; try assumption.
    - destruct WAT as (Uw & Y24 & RDlo & RDhi & RD16 & YHle). destruct YST as (Ytb & _).
      destruct (Z.ltb_spec w D1) as [LT|GE].
      + pose proof (d7ug7d0_conc fx R M (Vd 0 0 0 0 0 0 0 0 qneg (Z.of_nat nn) Ad 0 0 0 fbR rd w)) as P. cbn [Vd VdO] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold hl_ceil in *; flia) ltac:(flia) ltac:(flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WRF VD VS ltac:(unfold hl_ceil in *; flia) (mod16_mod8 Ad Ad16) ltac:(right; unfold hl_ceil in *; flia) DD1 ltac:(flia)
                    ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia) ltac:(exactA Yb8) Ytb Y24 ltac:(unfold hl_ceil in *; flia) (mod16_mod8 rd RD16) ltac:(right; unfold hl_ceil in *; flia)
                    ltac:(exactA Uw) ltac:(flia) ltac:(flia) LT ltac:(flia) Hq S2 ltac:(flia))
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & B1 & B10 & B11 & B12 & B13 & B14 & B19 & B22 & B23 & C296 & C304 & C320 & C328 & C336). clear P.
        exists fx1, R1, M1. split. exact MG1. split. { intros i Hi Hn'. apply FR1. exact Hi. flia. flia. } split. exact MS1.
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 21%nat), (K1 24%nat) by inl.
        repeat split; try assumption.
      + pose proof (d7ug7d1_conc fx R M (Vd 0 0 0 0 0 0 0 0 qneg (Z.of_nat nn) Ad 0 0 0 fbR rd w)) as P. cbn [Vd VdO] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold hl_ceil in *; flia) ltac:(flia) ltac:(flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WRF VD VS ltac:(unfold hl_ceil in *; flia) (mod16_mod8 Ad Ad16) ltac:(right; unfold hl_ceil in *; flia) DD1 ltac:(flia)
                    ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia) ltac:(exactA Yb8) Ytb Y24 ltac:(unfold hl_ceil in *; flia) (mod16_mod8 rd RD16) ltac:(right; unfold hl_ceil in *; flia)
                    ltac:(exactA Uw) ltac:(flia) ltac:(flia) GE ltac:(flia) Hq S2 ltac:(flia))
          as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & B1 & B10 & B11 & B12 & B13 & B14 & B19 & B22 & B23 & C296 & C304 & C320 & C328 & C336). clear P.
        exists fx1, R1, M1. split. exact MG1. split. { intros i Hi Hn'. apply FR1. exact Hi. flia. flia. } split. exact MS1.
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 21%nat), (K1 24%nat) by inl.
        repeat split; try assumption. }
  destruct PC as (fx1 & R1 & M1 & MG1 & KEEP1 & MS1 & E2 & E3 & E4 & E8 & E9 & E18 & E21 & E22 & E23 & E24 & C296 & C304 & C320 & C328 & C336).
  (* [comment removed for export] *)
  assert (KOUT: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 352 <= i < sp) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn'. apply KEEP1. exact Hi. flia. }
  assert (MK1: marksO2 M1 sp Y (Z.land fbY 2) qneg).
  { split. exact C320. split. exact C328. split. exact C336. split. eapply u32_at_agree1. 4: exact C284. intros i Hi; apply KEEP1; flia. flia. flia.
    eapply u64_at_agree1. 4: exact C344. intros i Hi; apply KEEP1; flia. flia. flia. }
  assert (VD1: L5.u64_at RSEGS M1 (sp - 152) Ad). { eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KEEP1; flia. flia. flia. }
  assert (VS1: L5.u64_at RSEGS M1 (sp - 144) 2). { eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KEEP1; flia. flia. flia. }
  assert (VQ1: L5.u64_at RSEGS M1 (sp - 232) quotd). { eapply u64_at_agree1. 4: exact VQ. intros i Hi; apply KEEP1; flia. flia. flia. }
  assert (VQS1: L5.u64_at RSEGS M1 (sp - 224) (Z.of_nat nn - 2)). { eapply u64_at_agree1. 4: exact VQS. intros i Hi; apply KEEP1; flia. flia. flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 336)) as [X|X]. left; apply KEEP1; flia. destruct (Z_lt_le_dec a (sp - 288)) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KEEP1; flia. }
  assert (HP1: L5C.hpres L LB sp DIVO2_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => sp - 336 <= a < sp - 288)).
      + intros a Ha Hn'. apply KEEP1; assumption.
      + intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
      + rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
      + exact MG1.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  assert (OBY1: L5.big_at RSEGS M1 Y (L5.BO fbR nn stR)). { eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KOUT; flia. flia. flia. }
  assert (OBQ1: L5.big_at RSEGS M1 Q (L5.BO fq (nn - 2) stq)). { eapply big_at_agree1. 4: exact OBQ. intros i Hi; apply KOUT; flia. flia. flia. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  destruct (Z.ltb_spec w D1) as [LT|GE].
  - (* [comment removed for export] *)
    eapply (stage_L fx1 R1 M1 model LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg fbR (nn - 1)%nat stR fq stq (L5.bo_data Y (L5.BO fbR nn stR)) quotd
              E2 E3 E4 E8 E9 E18 C304 VD1 E21 E22 VS1 VQ1 ltac:(replace (Z.of_nat (nn - 1)%nat) with (Z.of_nat nn - 1) by flia; exact E23) ltac:(flia) MBV HH1 ELB
              (credit_weaken _ (DIVO2_K - DIVN_K) _ (divO2_bytes capy - DIVN_BYTES) _ CRA ltac:(unfold DIVO2_K, DIVN_K; flia) ltac:(unfold divO2_bytes, DIVN_BYTES; flia))).
    + eapply div_saves_kept. 4: exact DS. intros i Hi; apply KEEP1; flia. flia. flia.
    + eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KEEP1; flia. flia. flia.
    + exact MK1.
    + exact Hq.
    + exact IN1. + exact IN2. + exact IN3. + exact LBF. + exact INAd.
    + eapply u64_at_agree1. 4: exact DD1. intros i Hi; apply KOUT; unfold hl_ceil in *; flia. flia. unfold hl_ceil in *; flia.
    + exact ADY. + exact ADQ.
    + replace (S (nn - 1)) with nn by flia. exact OBY1.
    + exact SGN.
    + eapply L5.defined_grows. exact MG1. exact DY.
    + replace (S (nn - 1)) with nn by flia. eapply L5.defined_grows. exact MG1. exact DYD.
    + exact INR.
    + replace (S (nn - 1)) with nn by flia. reflexivity.
    + replace (nn - 1 - 1)%nat with (nn - 2)%nat by flia. exact OBQ1.
    + eapply L5.defined_grows. exact MG1. exact DQ.
    + replace (nn - 1 - 1)%nat with (nn - 2)%nat by flia. eapply L5.defined_grows. exact MG1. exact DQD.
    + replace (nn - 1 - 1)%nat with (nn - 2)%nat by flia. exact Equotd.
    + exact ENDS.
    + intros b Hb. eapply L5.defined_grows. exact MG1. exact (DEB b Hb).
    + intros i Hi. rewrite KOUT. exact (IMG1 i Hi). flia. flia.
    + exact HP1.
  - (* [comment removed for export] *)
    assert (YFIT: match stR with L5.BDyn cap _ => Z.of_nat nn + 1 <= cap | L5.BInl _ _ => nn = 2%nat end).
    { destruct stR as [v0 v1|capR rd]. exact (proj1 WAT).
      destruct (Nat.eq_dec nn (S Ln)) as [E|NE]. { exfalso. pose proof (TOPW E). subst w. flia. } flia. }
    eapply (stage_G8 fx1 R1 M1 model LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg fbR nn stR wsY fq stq wsQ
              E2 E3 E4 E8 E9 E18 E21 E22 E24 ltac:(flia) NNLE YFIT MBV HH1 ELB CRA).
    + eapply div_saves_kept. 4: exact DS. intros i Hi; apply KEEP1; flia. flia. flia.
    + eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KEEP1; flia. flia. flia.
    + exact MK1.
    + exact Hq.
    + exact C296.
    + exact VQS1. + exact VD1. + exact VS1.
    + exact IN1. + exact IN2. + exact IN3. + exact LBF. + exact INAd.
    + eapply u64_at_agree1. 4: exact DD1. intros i Hi; apply KOUT; unfold hl_ceil in *; flia. flia. unfold hl_ceil in *; flia.
    + exact ADY. + exact ADQ.
    + exact OBY1.
    + pose proof OLY as (L1' & L2' & L3'). split. exact L1'. split. exact L2'. cbn [L5.bo_len L5.bo_st] in L3' |- *. destruct stR as [v0 v1|capR rd]. exact L3'.
      destruct WAT as (_ & _ & RDlo & RDhi & RD16 & YHle). eapply limbs_at_agree1. 4: exact L3'. intros i Hi; apply KOUT; unfold hl_ceil in *; flia. flia. rewrite YL1. unfold hl_ceil in *; flia.
    + exact SGN.
    + eapply L5.defined_grows. exact MG1. exact DY.
    + eapply L5.defined_grows. exact MG1. exact DYD.
    + exact INR.
    + exact OBQ1.
    + pose proof OLQ as (L1' & L2' & L3'). split. exact L1'. split. exact L2'. cbn [L5.bo_len L5.bo_st] in L3' |- *. destruct stq as [q0 q1|cq qq]. exact L3'.
      pose proof OBQ as (_ & _ & _ & (_ & _ & _ & QHle & QHcap & Qq8 & Qqlo & Qqhi & _)).
      unfold ends in ENDS. destruct ENDS as (Eeb & _). pose proof (LBdef _ _ _ _ HH qq (8 * cq) ltac:(subst LBc eb; left; reflexivity)) as (_ & _ & Qhi & _).
      eapply limbs_at_agree1. 4: exact L3'. intros i Hi; apply KOUT; unfold hl_ceil in *; flia. flia. rewrite L1'. unfold hl_ceil in *; flia.
    + eapply L5.defined_grows. exact MG1. exact DQ.
    + eapply L5.defined_grows. exact MG1. exact DQD.
    + exact QCAP.
    + exact ENDS.
    + intros b Hb. eapply L5.defined_grows. exact MG1. exact (DEB b Hb).
    + intros i Hi. rewrite KOUT. exact (IMG1 i Hi). flia. flia.
    + exact HP1.
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2EU.
