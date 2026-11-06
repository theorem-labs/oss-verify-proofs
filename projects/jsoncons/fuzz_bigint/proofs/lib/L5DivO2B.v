(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigLinkShl L5Defs L5CoreKit L5Kn
     L5Core L5CoreSpecs L5CoreKitS L5Words L5WordsB L5Reduce L5ReduceG L5DDq L5SubMul L5Shl L5MulM L5Hp L5Norm
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivO2P L5DivO2S L5DivTail L5DivO2A.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5DIVO2B.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVO2P. Import L5DO2S. Import L5DIVO2A.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
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
Local Ltac uSCR := unfold DIVO2_SCR, UNNORM_SCR, DIVEQ_SCR, DIV_SCR, L5NORM.NORM_SCR, L5MULM.MULM_SCR, L5SHL.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR,
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
Hypothesis NORM : L5NORM.norm_spec L HI.
Hypothesis UNNORMS : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.
Hypothesis DIVTAIL : divtail_stmt L HI.
Hypothesis DIVTAIL2 : L5DIVTAIL.divtail2_stmt L HI.

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
Let spd : Z := sp - 304.
Let WN : list L5.range := [(Y, 32); (yd0, 8 * capy); (Q, 32)].
Let Vd := VdO sp Y Q A fbY R0.
(* [comment removed for export] *)
Let IMG := @L5DIVO2A.IMG L LY.
Let IMGLO := @L5DIVO2A.IMGLO L LY.
Let ERRNO := @L5DIVO2A.ERRNO L LY R0 Y Q A sp by_ LEN1.
Let ERRNOV := @L5DIVO2A.ERRNOV L LY.
Let SPTOP := @L5DIVO2A.SPTOP L M0 sp STK.
Let DIVO2_SCR_val := L5DIVO2A.DIVO2_SCR_val.
Let SPW := @L5DIVO2A.SPW L R0 M0 Y Q A sp by_ STK LEN1 AY8 SY AA8 SA HA AQ8 SQ.
Let LBhi := @L5DIVO2A.LBhi _ L HI HIok.
Let LBdef := @L5DIVO2A.LBdef _ L HI HIok.
Let LBapart := @L5DIVO2A.LBapart _ L HI HIok.
Let UR1 := @L5DIVO2A.UR1 R0 Y Q A sp r by_ G1 RA LEN1.
Let YB := @L5DIVO2A.YB M0 LB Y by_ wy YOK.
Let fbY_rng := @L5DIVO2A.fbY_rng M0 LB Y by_ wy YOK.
Let capy_rng := @L5DIVO2A.capy_rng R0 M0 LB Y Q A sp by_ wy YOK LEN1 CAPY WRB.
Let Ln_le := @L5DIVO2A.Ln_le M0 LB Y by_ wy YOK LEN1 WRB.
Let stage_T := @L5DIVO2A.stage_T _ L HI LY HIok DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
Let stage_X3 := @L5DIVO2A.stage_X3 _ L HI LY HIok DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
Let credit_after_unnorm := @L5DIVO2A.credit_after_unnorm L cr Y Q A sp by_ LEN1.
Let stage_U := @L5DIVO2A.stage_U _ L HI LY HIok UNNORMS DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
Let stage_Z := @L5DIVO2A.stage_Z _ L HI LY HIok UNNORMS DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.

(* [comment removed for export] *)
Local Ltac dlia := prune_impl; prune_disj; intros; repeat match goal with |- _ /\ _ => split end; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_L (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg : Z) (fbR : Z) (n : nat) (stR : L5.bstore) (fq : Z) (stq : L5.bstore)
      (remd quotd : Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y -> getr R (reg 10) = Z_to_bv 64 remd -> getr R (reg 20) = Z_to_bv 64 Ad ->
  getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 D1 -> getr R (reg 24) = Z_to_bv 64 quotd ->
  getr R (reg 26) = Z_to_bv 64 (Z.of_nat n) -> (1 <= n <= 298)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr (DIVO2_K - DIVN_K) (divO2_bytes capy - DIVN_BYTES) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad -> marksO2 M sp Y (Z.land fbY 2) qneg -> 0 <= qneg <= 1 ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (forall cap q, stR = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) -> (forall cap q, stq = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  L5.big_at RSEGS M Y (L5.BO fbR (S n) stR) -> Z.testbit fbR 1 = false ->
  L5.defined M Y 32 -> L5.defined M (L5.bo_data Y (L5.BO fbR (S n) stR)) (8 * L5.bo_cap (L5.BO fbR (S n) stR)) ->
  (forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) (ob eb ++ LB)) -> remd = L5.bo_data Y (L5.BO fbR (S n) stR) ->
  L5.big_at RSEGS M Q (L5.BO fq (n - 1) stq) -> L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq (n - 1) stq)) (8 * L5.bo_cap (L5.BO fq (n - 1) stq)) ->
  quotd = L5.bo_data Q (L5.BO fq (n - 1) stq) ->
  ends L LB sty stR stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R LTEST M model) K.
Proof.
  intros H2 H3 H4 H9 H18 H10 H20 H21 H22 H23 H24 H26 Hn MBV HH ELB CRA DS LOC MK Hq IN1 IN2 IN3 LBF INAd DD1 ADY ADQ OBY SGN DY DYD INR Eremd OBQ DQ DQD Equotd ENDS DEB IMG1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof D1_range as (D1R & D1ge).
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (INR': forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) LBc).
  { intros cap q E. subst LBc. destruct (in_app_or _ _ _ (INR cap q E)) as [X|X]. apply in_app_iff. left; exact X. apply in_app_iff. right. apply in_app_iff. right. exact X. }
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16). rewrite IMG, IMGLO in Adimg.
  (* [comment removed for export] *)
  assert (RY: match stR with L5.BInl _ _ => remd = Y + 16 /\ n = 1%nat
                             | L5.BDyn cap q => remd = q /\ Z.of_nat (S n) <= cap /\ In (q, 8 * cap) LBc /\ 4096 <= q /\ q + 8 * cap <= hl_ceil L /\ q mod 16 = 0 end).
  { subst remd. pose proof OBY as (_ & _ & _ & STY). cbn [L5.bo_fb L5.bo_len L5.bo_st] in STY.
    destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_st].
    - destruct STY as (_ & _ & _ & Hl2 & _). split. reflexivity. flia.
    - destruct STY as (_ & _ & _ & Hle & _). pose proof (LBdef _ _ _ _ HH rd (8 * capR) (INR' capR rd eq_refl)) as (_ & (RDlo & _) & RDhi & _ & RD16).
      split. reflexivity. split. exact Hle. split. exact (INR' capR rd eq_refl). split. exact RDlo. split. exact RDhi. exact RD16. }
  assert (RQ: match stq with L5.BInl _ _ => quotd = Q + 16 /\ (n - 1 <= 2)%nat
                             | L5.BDyn cap q => quotd = q /\ Z.of_nat (n - 1) <= cap /\ In (q, 8 * cap) LBc /\ 4096 <= q /\ q + 8 * cap <= hl_ceil L /\ q mod 16 = 0 /\
                                               eb = Some (q, 8 * cap) /\ blocks_apart q (8 * cap) LB end).
  { subst quotd. pose proof OBQ as (_ & _ & _ & STQ). cbn [L5.bo_fb L5.bo_len L5.bo_st] in STQ.
    destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_st].
    - destruct STQ as (_ & _ & _ & Hl2 & _). split. reflexivity. exact Hl2.
    - destruct STQ as (_ & _ & _ & Hle & _). unfold ends in ENDS. destruct ENDS as (Eeb & BR & BA & CQ & SM).
      assert (INQ: In (Aq, 8 * capq) LBc). { subst LBc eb. left. reflexivity. }
      pose proof (LBdef _ _ _ _ HH Aq (8 * capq) INQ) as (_ & (AQlo & _) & AQhi & _ & AQ16).
      split. reflexivity. split. exact Hle. split. exact INQ. split. exact AQlo. split. exact AQhi. split. exact AQ16. split. exact Eeb. exact BA. }
  (* [comment removed for export] *)
  assert (RYQ: apart remd (8 * (Z.of_nat n + 1)) quotd (8 * (Z.of_nat n - Z.of_nat 1))).
  { unfold apart. unfold hl_ceil in *. destruct stR as [v0 v1|capR rd]; destruct stq as [q0 q1|capq Aq].
    all: first [destruct RY as (-> & HleR & INrd & RDlo & RDhi & RD16) | destruct RY as [-> ->]];
         first [destruct RQ as (-> & HleQ & INq & AQlo & AQhi & AQ16 & Eeb & BAq) | destruct RQ as [-> Hl2]]; try flia.
    (* [comment removed for export] *)
    unfold ends in ENDS. destruct ENDS as (_ & _ & _ & _ & SM). unfold sty in SM. pose proof YOK as (_ & _ & _ & BLK).
    destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM, BLK. exfalso; exact SM.
    destruct SM as (-> & ->). pose proof (BAq _ (proj1 BLK)) as AP. cbn [fst snd] in AP. generalize AP; flia. }
  (* [comment removed for export] *)
  assert (RMD: remd mod 8 = 0 /\ 4096 <= remd /\ remd + 8 * (Z.of_nat n + 1) <= 2 ^ 47 /\ L5.defined M remd (8 * (Z.of_nat n + 1)) /\
               apart remd (8 * (Z.of_nat n + 1)) (sp - 320) 320 /\ apart remd (8 * (Z.of_nat n + 1)) Ad (8 * (Z.of_nat 1 + 1))).
  { unfold apart, hl_ceil in *. subst remd. destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_cap L5.bo_st] in DYD, RY |- *.
    - destruct RY as [_ ->]. split. rewrite <- Zplus_mod_idemp_l, AY8. reflexivity. split. flia. split. flia.
      split. eapply L5.defined_sub. exact DYD. flia. flia. split. flia. flia.
    - destruct RY as (_ & HleR & INrd & RDlo & RDhi & RD16). split. exact (mod16_mod8 rd RD16). split. flia. split. flia.
      split. eapply L5.defined_sub. exact DYD. flia. flia. split. flia. generalize (ADY capR rd eq_refl); flia. }
  destruct RMD as (RM8 & RMlo & RMhi & RMdef & RAP1 & RAP3).
  assert (QMD: quotd mod 8 = 0 /\ 4096 <= quotd /\ quotd + 8 * (Z.of_nat n - Z.of_nat 1) <= 2 ^ 47 /\ L5.defined M quotd (8 * (Z.of_nat n - Z.of_nat 1)) /\
               apart quotd (8 * (Z.of_nat n - Z.of_nat 1)) (sp - 320) 320 /\ apart quotd (8 * (Z.of_nat n - Z.of_nat 1)) Ad (8 * (Z.of_nat 1 + 1))).
  { unfold apart, hl_ceil in *. subst quotd. destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_cap L5.bo_st] in DQD, RQ |- *.
    - destruct RQ as [_ Hl2]. split. rewrite <- Zplus_mod_idemp_l, AQ8. reflexivity. split. flia. split. flia.
      split. eapply L5.defined_sub. exact DQD. flia. flia. split. flia. flia.
    - destruct RQ as (_ & HleQ & INq & AQlo & AQhi & AQ16 & Eeb & BAq). split. exact (mod16_mod8 Aq AQ16). split. flia. split. flia.
      split. eapply L5.defined_sub. exact DQD. flia. flia. split. flia. generalize (ADQ capq Aq eq_refl); flia. }
  destruct QMD as (QD8 & QDlo & QDhi & QDdef & QAP1 & QAP3).
  (* [comment removed for export] *)
  destruct (DIVLOOP fx R M sp Y remd quotd Ad D1 1%nat n H2 H10 H18 H20 ltac:(exact H21) ltac:(exact H22) H23 H24 H26
              D1R ltac:(flia) ltac:(flia) A16 ltac:(flia)
              RM8 RMlo RMhi RMdef ltac:(apply (L5C.writable_of_defined RSEGS); [exact RMdef | flia | flia])
              QD8 QDlo QDhi ltac:(apply (L5C.writable_of_defined RSEGS); [exact QDdef | flia | flia])
              (mod16_mod8 Ad Ad16) Adlo ltac:(unfold hl_ceil in *; flia) ltac:(eapply L5.defined_sub; [exact DAd | flia | flia])
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0 | flia | flia] | flia | flia])
              ltac:(eapply L5.defined_sub; [exact SCR0 | flia | flia])
              RAP1 QAP1 RYQ RAP3 QAP3 ltac:(unfold apart, hl_ceil in *; flia) ltac:(unfold apart, hl_ceil in *; flia))
    as (fx1 & R1 & M1 & MS1 & A2 & K1 & FR1 & MG1).
  (* [comment removed for export] *)
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (remd <= i < remd + 8 * (Z.of_nat n + 1)) -> ~ (quotd <= i < quotd + 8 * (Z.of_nat n - Z.of_nat 1)) ->
                 ~ (sp - 248 <= i < sp - 240) -> ~ (sp - 320 <= i < sp - 304) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2 N3 N4. apply FR1; unfold inr; rewrite BG.unsigned_lit by exact Hi; flia. }
  (* [comment removed for export] *)
  assert (NREM: forall i, remd <= i < remd + 8 * (Z.of_nat n + 1) ->
            ~ (sp - 240 <= i < sp) /\ ~ (Y <= i < Y + 16) /\ ~ (Q <= i < Q + 32) /\ ~ (0x10000 <= i < 0x20000) /\ ~ (Ad <= i < Ad + 64)).
  { intros i Hi. unfold apart, hl_ceil in *. subst remd. destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_st] in RY, Hi, RAP3 |- *.
    - destruct RY as [_ ->]. dlia.
    - destruct RY as (_ & HleR & INrd & RDlo & RDhi & RD16). pose proof (LBdef _ _ _ _ HH rd (8 * capR) INrd) as (_ & (_ & RDimg) & _). rewrite IMG, IMGLO in RDimg.
      generalize RDimg (ADY capR rd eq_refl). dlia. }
  assert (NQUO: forall i, quotd <= i < quotd + 8 * (Z.of_nat n - Z.of_nat 1) ->
            ~ (sp - 240 <= i < sp) /\ ~ (Y <= i < Y + 32) /\ ~ (Q <= i < Q + 16) /\ ~ (0x10000 <= i < 0x20000) /\ ~ (Ad <= i < Ad + 64)).
  { intros i Hi. unfold apart, hl_ceil in *. subst quotd. destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_st] in RQ, Hi, QAP3 |- *.
    - destruct RQ as [_ Hl2]. dlia.
    - destruct RQ as (_ & HleQ & INq & AQlo & AQhi & AQ16 & Eeb & BAq). pose proof (LBdef _ _ _ _ HH Aq (8 * capq) INq) as (_ & (_ & AQimg) & _). rewrite IMG, IMGLO in AQimg.
      generalize AQimg (ADQ capq Aq eq_refl). dlia. }
  assert (KFR: forall i, sp - 240 <= i < sp -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. intros C; exact (proj1 (NREM i C) Hi). intros C; exact (proj1 (NQUO i C) Hi). flia. flia. }
  assert (KFR2: forall i, sp - 304 <= i < sp - 248 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. 3: flia. 3: flia.
    - intros C. subst remd. unfold hl_ceil in *. destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_st] in RY, C; [destruct RY as [_ ->]; flia | destruct RY as (_ & HleR & INrd & RDlo & RDhi & RD16); flia].
    - intros C. subst quotd. unfold hl_ceil in *. destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_st] in RQ, C; [destruct RQ as [_ Hl2]; flia | destruct RQ as (_ & HleQ & INq & AQlo & AQhi & _); flia]. }
  assert (KYH: forall i, Y <= i < Y + 16 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. intros C; exact (proj1 (proj2 (NREM i C)) Hi). intros C; apply (proj1 (proj2 (NQUO i C))); flia. flia. flia. }
  assert (KQH: forall i, Q <= i < Q + 16 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. intros C; pose proof (proj1 (proj2 (proj2 (NREM i C)))); flia. intros C; exact (proj1 (proj2 (proj2 (NQUO i C))) Hi). flia. flia. }
  assert (KAD: forall i, Ad <= i < Ad + 64 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. intros C; exact (proj2 (proj2 (proj2 (proj2 (NREM i C)))) Hi). intros C; exact (proj2 (proj2 (proj2 (proj2 (NQUO i C)))) Hi).
    unfold hl_ceil in *; flia. unfold hl_ceil in *; flia. }
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK1.
  (* [comment removed for export] *)
  assert (OBY1: exists stR1, same_st stR stR1 /\ L5.big_at RSEGS M1 Y (L5.BO fbR (S n) stR1) /\ L5.bo_data Y (L5.BO fbR (S n) stR1) = remd
                 /\ L5.bo_cap (L5.BO fbR (S n) stR1) = L5.bo_cap (L5.BO fbR (S n) stR)).
  { pose proof OBY as (Ob0 & Obf & Ob8 & ObS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Ob0, Obf, Ob8, ObS.
    destruct stR as [v0 v1|capR rd].
    - destruct ObS as (Tb & _ & _ & Hle & _). destruct RY as [Er _].
      destruct (BSHL.defined_word M1 (Y + 16) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG1 | exact DY] | flia | flia]) ltac:(flia) ltac:(flia)) as (w0 & R0' & U0').
      destruct (BSHL.defined_word M1 (Y + 24) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG1 | exact DY] | flia | flia]) ltac:(flia) ltac:(flia)) as (w1 & R1' & U1').
      exists (L5.BInl w0 w1). split. exact I. split. 2: { cbn [L5.bo_data L5.bo_cap L5.bo_st]. split. symmetry; exact Er. reflexivity. }
      unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Ob0. intros i Hi; apply KYH; flia. flia. flia. }
      split. exact Obf. split. { eapply u64_at_agree1. 4: exact Ob8. intros i Hi; apply KYH; flia. flia. flia. }
      split. exact Tb. split. exact U0'. split. exact U1'. split. exact Hle. split. exact R0'. exact R1'.
    - exists (L5.BDyn capR rd). split. split; reflexivity. split. 2: { split. symmetry; exact (proj1 RY). reflexivity. }
      eapply big_at_agree1. 4: exact OBY. 2: flia. 2: flia. intros i Hi. destruct RY as (Er & _ & INrd & RDlo & RDhi & _).
      apply KEEP1. flia. unfold hl_ceil in *; flia. intros C; apply (proj1 (proj2 (NQUO i C))); flia. flia. flia. }
  destruct OBY1 as (stR1 & SM1 & OBY1 & ERD1 & ECAP1).
  (* [comment removed for export] *)
  assert (OBQ1: exists stq1, same_st stq stq1 /\ L5.big_at RSEGS M1 Q (L5.BO fq (n - 1) stq1) /\ L5.bo_data Q (L5.BO fq (n - 1) stq1) = quotd
                 /\ L5.bo_cap (L5.BO fq (n - 1) stq1) = L5.bo_cap (L5.BO fq (n - 1) stq)).
  { pose proof OBQ as (Ob0 & Obf & Ob8 & ObS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Ob0, Obf, Ob8, ObS.
    destruct stq as [q0 q1|capq Aq].
    - destruct ObS as (Tb & _ & _ & Hle & _). destruct RQ as [Eq _].
      destruct (BSHL.defined_word M1 (Q + 16) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG1 | exact DQ] | flia | flia]) ltac:(flia) ltac:(flia)) as (w0 & R0' & U0').
      destruct (BSHL.defined_word M1 (Q + 24) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG1 | exact DQ] | flia | flia]) ltac:(flia) ltac:(flia)) as (w1 & R1' & U1').
      exists (L5.BInl w0 w1). split. exact I. split. 2: { cbn [L5.bo_data L5.bo_cap L5.bo_st]. split. symmetry; exact Eq. reflexivity. }
      unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Ob0. intros i Hi; apply KQH; flia. flia. flia. }
      split. exact Obf. split. { eapply u64_at_agree1. 4: exact Ob8. intros i Hi; apply KQH; flia. flia. flia. }
      split. exact Tb. split. exact U0'. split. exact U1'. split. exact Hle. split. exact R0'. exact R1'.
    - exists (L5.BDyn capq Aq). split. split; reflexivity. split. 2: { split. symmetry; exact (proj1 RQ). reflexivity. }
      eapply big_at_agree1. 4: exact OBQ. 2: flia. 2: flia. intros i Hi. destruct RQ as (Eq & _ & INq & AQlo & AQhi & _).
      apply KEEP1. flia. intros C; apply (proj1 (proj2 (proj2 (NREM i C)))); flia. unfold hl_ceil in *; flia. flia. flia. }
  destruct OBQ1 as (stq1 & SMQ1 & OBQ1 & EQD1 & EQCAP1).
  (* [comment removed for export] *)
  assert (SCR1: L5.defined M1 (sp - 9264) 9264). { eapply L5.defined_grows. exact MG1. exact SCR0. }
  assert (HP1: L5C.hpres L LB sp DIVO2_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1
                (fun a => (remd <= a < remd + 8 * (Z.of_nat n + 1)) \/ (quotd <= a < quotd + 8 * (Z.of_nat n - Z.of_nat 1)) \/ (sp - 320 <= a < sp - 240))).
      + intros a Ha Hn'. apply KEEP1; flia.
      + intros a KA [C|[C|C]].
        * pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. subst remd. unfold ends in ENDS.
          destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_st] in C, RY.
          { apply (L5HP.outside_in _ _ Y 32 OW). cbn. left; reflexivity. destruct RY as [_ ->]. flia. }
          destruct RY as (_ & HleR & INrd & RDlo & RDhi & RD16). unfold WN, sty, yd0, capy in *. unfold L5.bo_data, L5.bo_cap in OW. pose proof YOK as (_ & _ & _ & BLK).
          destruct stq as [q0 q1|capq Aq]; destruct (L5.bo_st by_) as [y0 y1|cy qy] in ENDS, BLK, OW |- *.
          -- destruct ENDS as (-> & -> & BR & BA).
             refine (L5C.kept_not_fresh L LB sp DIVO2_SCR _ a rd 64 KA BA _ _ (LBhi _ _ _ _ HH0) _). exact (proj1 (proj2 BR)). exact (proj2 (proj2 (proj2 (proj2 BR)))). flia.
          -- destruct ENDS as (-> & -> & ->). apply (L5HP.outside_in _ _ qy (8 * cy) OW). cbn. right; left; reflexivity. flia.
          -- destruct ENDS as (_ & _ & _ & _ & SM). exfalso; exact SM.
          -- destruct ENDS as (-> & _ & _ & _ & (-> & ->)). apply (L5HP.outside_in _ _ qy (8 * cy) OW). cbn. right; left; reflexivity. flia.
        * pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. subst quotd.
          destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_st] in C, RQ.
          { apply (L5HP.outside_in _ _ Q 32 OW). cbn. right; right; left; reflexivity. destruct RQ as [_ Hl2]. flia. }
          destruct RQ as (_ & HleQ & INq & AQlo & AQhi & AQ16 & Eeb & BAq). unfold ends in ENDS. destruct ENDS as (_ & BR & _).
          refine (L5C.kept_not_fresh L LB sp DIVO2_SCR _ a Aq (8 * capq) KA BAq _ _ (LBhi _ _ _ _ HH0) _). exact (proj1 (proj2 BR)). exact (proj2 (proj2 (proj2 (proj2 BR)))). flia.
        * refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
      + rewrite DIVO2_SCR_val. exact SCR1.
      + exact MG1.
    - intros a KA; exact KA.
    - intros b Hb; exact Hb.
    - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha.
    destruct (Z_lt_le_dec a remd) as [Ra1|Ra1]; [| destruct (Z_lt_le_dec a (remd + 8 * (Z.of_nat n + 1))) as [Ra2|Ra2]].
    2:{ (* [comment removed for export] *) right. subst remd. destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_st] in RY, Ra1, Ra2 |- *.
        - destruct RY as [_ ->]. left. unfold hl_ceil in *. flia.
        - destruct RY as (_ & HleR & INrd & _). right. exists (rd, 8 * capR). split. exact INrd. cbn. flia. }
    all: destruct (Z_lt_le_dec a quotd) as [Q1|Q1]; [| destruct (Z_lt_le_dec a (quotd + 8 * (Z.of_nat n - Z.of_nat 1))) as [Q2|Q2]].
    2,5: right; subst quotd; destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_st] in RQ, Q1, Q2 |- *;
         [ destruct RQ as [_ Hl2]; left; unfold hl_ceil in *; flia
         | destruct RQ as (_ & HleQ & INq & _); right; exists (Aq, 8 * capq); split; [exact INq | cbn; flia] .. ].
    all: destruct (Z_lt_le_dec a (sp - 320)) as [S1|S1]; [left; apply KEEP1; flia |].
    all: destruct (Z_lt_le_dec a (sp - 240)) as [S2|S2]; [right; left; unfold hl_ceil in *; flia | left; apply KEEP1; flia]. }
  pose proof MK as (C272 & C280 & C288 & C256 & C236 & C296).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact (proj1 MOK1). exact (proj1 (proj2 MOK1)). exact MS1.
  eapply (stage_Z fx1 R1 M1 model LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg fbR (S n) stR1 fq (n - 1)%nat stq1).
  - exact A2.
  - rewrite (K1 3%nat) by (cbn; tauto). exact H3.
  - rewrite (K1 4%nat) by (cbn; tauto). exact H4.
  - rewrite (K1 9%nat) by (cbn; tauto). exact H9.
  - rewrite (K1 18%nat) by (cbn; tauto). exact H18.
  - exact MBV.
  - exact HH1.
  - exact ELB.
  - exact CRA.
  - eapply div_saves_kept. 4: exact DS. intros i Hi. apply KFR; flia. flia. flia.
  - eapply localsO2_kept. 4: exact LOC. intros i Hi. apply KFR; flia. flia. flia.
  - unfold marksO2. repeat split; first [ eapply u64_at_agree1; [intros i Hi; first [apply KFR; flia | apply KFR2; flia] | flia | flia | eassumption]
                                          | eapply u32_at_agree1; [intros i Hi; first [apply KFR; flia | apply KFR2; flia] | flia | flia | eassumption] ].
  - exact Hq.
  - exact IN1. - exact IN2. - exact IN3. - exact LBF.
  - exact OBY1.
  - flia.
  - exact SGN.
  - eapply L5.defined_grows. exact MG1. exact DY.
  - rewrite ERD1, ECAP1. eapply L5.defined_grows. exact MG1. subst remd. exact DYD.
  - intros cap q E. subst stR1. destruct stR as [v0 v1|c' q']. exfalso; exact SM1. destruct SM1 as [-> ->]. exact (INR c' q' eq_refl).
  - exact OBQ1.
  - eapply L5.defined_grows. exact MG1. exact DQ.
  - rewrite EQD1, EQCAP1. eapply L5.defined_grows. exact MG1. subst quotd. exact DQD.
  - (* [comment removed for export] *)
    assert (E1: ends L LB sty stR1 stq eb) by exact (ends_same _ _ _ _ _ _ _ ENDS SM1).
    unfold ends in E1 |- *. destruct stq as [q0 q1|capq Aq]; destruct stq1 as [q0' q1'|capq' Aq']; try (exfalso; exact SMQ1). exact E1.
    destruct SMQ1 as [-> ->]. exact E1.
  - intros b Hb. eapply L5.defined_grows. exact MG1. exact (DEB b Hb).
  - intros i Hi. rewrite KEEP1. exact (IMG1 i Hi). flia. intros C; exact (proj1 (proj2 (proj2 (proj2 (NREM i C)))) Hi). intros C; exact (proj1 (proj2 (proj2 (proj2 (NQUO i C)))) Hi). flia. flia.
  - exact HP1.
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2B.
