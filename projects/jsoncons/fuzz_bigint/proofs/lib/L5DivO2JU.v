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
 L5DivSpecsU L5DivPartsU L5DivNPU L5DivO2PU L5DivO2SU L5DivTailU L5DivOPU L5DivEarlyU L5CmpU L5DivO2AU L5DivO2CU L5DivO2IU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2JU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVO2PU. Import L5DO2SU. Import L5DIVO2AU. Import L5DIVO2CU. Import L5DIVO2IU.

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
Let stage_G1 := @L5DIVO2IU.stage_G1 _ L HI LY HIok KPOS BPOS COPYA ASSIGN RESIZE NORM UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.
(* [comment removed for export] *)
Local Ltac cb := clearbody IMG IMGLO ERRNO ERRNOV SPTOP DIVO2_SCR_val SPW LBhi LBdef LBapart UR1 YB fbY_rng capy_rng Ln_le credit_debit64 credit_weaken credit_ok64 lb_free_cons_ne fresh_ne stage_G1.

(* [comment removed for export] *)
Let VdX (qy fnum nl B1 c : Z) (j : nat) : Z := match j with 39%nat => nl | _ => Vd qy 0 0 0 fnum nl B1 c 0 0 0 0 0 0 0 0 0 j end.

Lemma land2_cases f : 0 <= f -> Z.land f 2 = 0 \/ Z.land f 2 = 2.
Proof using R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
  intros Hf. pose proof (land2_rng f Hf) as Rg. pose proof (land2_bit0 f) as B. rewrite Z.bit0_odd in B.
  destruct (Z.eq_dec (Z.land f 2) 1) as [E|NE]. rewrite E in B. discriminate B. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_T2 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc nb : list (Z * Z)) (crc : credit)
      (fn2 c2 p2 fden fbR q0 q1 qneg : Z) (stR : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = nb ++ LB -> nb = (if Z.testbit fn2 0 then [(p2, 8 * c2)] else []) -> credit_after L cr DIVO2_K (divO2_bytes capy) crc ->
  div_saves M sp R0 ->
  local_obj M (sp - 184) fn2 c2 p2 ->
  L5.u8_at RSEGS M (sp - 136) fden -> 0 <= fden < 256 -> Z.testbit fden 0 = false ->
  L5.big_at RSEGS M Y (L5.BO fbR Ln stR) -> same_st sty stR ->
  L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  L5.big_at RSEGS M Q (L5.BO (2 * qneg) 0 (L5.BInl q0 q1)) ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R L5DIVTAILU.DT2 M model) K.
Proof.
  intros H2 H3 H4 MBV HH ELB ENB CRA DS LO2 Fd Fdr Fdb OBY SST DY DYD OBQ HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof capy_rng as CAPR. pose proof Ln_le as [LN1 LNS].
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (LBF2: lb_free fn2 p2 LBc = LB). { unfold lb_free. rewrite ELB, ENB. destruct (Z.testbit fn2 0). apply lb_remove_head. reflexivity. }
  assert (LBF3: lb_free fden 0 (lb_free fn2 p2 LBc) = LB). { unfold lb_free at 1. rewrite Fdb. exact LBF2. }
  assert (SUBc: forall b, In b LB -> In b LBc). { intros b Hb. rewrite ELB. apply in_app_iff. right. exact Hb. }
  unfold cfg.
  eapply (DIVTAIL2 fx R M model K LBc crc sp R0 fn2 c2 p2 fden 0 0 HH MOK HK0 H2 H4).
  - (* [comment removed for export] *) split. { replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. exact SPTOP. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - flia.
  - eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact DS.
  - rewrite UR1. exact RA.
  - exact LO2.
  - split. exact Fd. split. exact Fdr. intros T. rewrite Fdb in T. discriminate T.
  - intros T. rewrite ELB, ENB, T. cbn [app]. left. reflexivity.
  - intros T. rewrite Fdb in T. discriminate T.
  - (* [comment removed for export] *)
    cbv zeta. rewrite LBF3. rewrite UR1.
    intros fx5 R5 M5 model5 T2 T3 T4 TS HP5 MBV5 HH5.
    assert (KST5: forall a, sp - 352 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_nil. }
    assert (KBL5: forall A0 n a, In (A0, n) LB -> A0 <= a < A0 + n -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH5 A0 n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia. apply L5C.outside_nil. }
    assert (OBY5: L5.big_at RSEGS M5 Y (L5.BO fbR Ln stR)). { eapply big_at_agree1. 4: exact OBY. intros i Hi. apply KST5; flia. flia. flia. }
    assert (OBQ5: L5.big_at RSEGS M5 Q (L5.BO (2 * qneg) 0 (L5.BInl q0 q1))). { eapply big_at_agree1. 4: exact OBQ. intros i Hi. apply KST5; flia. flia. flia. }
    (* [comment removed for export] *)
    assert (YL5: exists wy2 : list Z, L5C.obj_limbs RSEGS M5 (L5.BO fbR Ln stR) wy2 /\ match stR with L5.BDyn cap q => L5.defined M5 q (8 * cap) | L5.BInl _ _ => True end).
    { pose proof OBY5 as (_ & _ & _ & ST5). cbn [L5.bo_st L5.bo_fb L5.bo_len] in ST5.
      destruct stR as [v0 v1|capR rd].
      - exists (firstn Ln [v0; v1]). destruct ST5 as (_ & _ & _ & Hl2 & Hv0 & Hv1). split. 2: exact I.
        unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. { rewrite length_firstn. cbn [length]. flia. }
        split. { destruct Ln as [|[|[|n3]]]; cbn; repeat constructor; flia. } reflexivity.
      - destruct ST5 as (_ & _ & _ & Hle & Hcap & Rq8 & Rq & Rhi & _).
        assert (INR: In (rd, 8 * capR) LB /\ L5.defined M rd (8 * capR)).
        { pose proof YOK as (_ & _ & _ & BLK). unfold same_st, sty in SST. unfold yd0, capy, L5.bo_cap, L5.bo_data in DYD. unfold sty in BLK.
          destruct (L5.bo_st by_) as [y0 y1|cy qy] in SST, DYD, BLK |- *. destruct SST. destruct SST as (-> & ->). split. exact (proj1 BLK). exact DYD. }
        destruct INR as [INR DR].
        assert (DR5: L5.defined M5 rd (8 * capR)). { eapply defined_agree1. intros i Hi. apply (KBL5 rd (8 * capR)). exact INR. exact Hi. exact DR. }
        destruct (L5KU.limbs_of_defined M5 rd Ln ltac:(eapply L5.defined_sub; [exact DR5 | flia | flia]) ltac:(flia) ltac:(flia)) as (wr & WRL & WRR & WRA).
        exists wr. split. { unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. exact WRL. split. exact WRR. exact WRA. } exact DR5. }
    destruct YL5 as (wy' & YL5 & YD5).
    apply (KONT fx5 R5 M5 model5 LB crc).
    + unfold divO2_post. split.
      { apply preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|[<-|[<-|Hi]]];
          [ rewrite T2, <- r2, G2; reflexivity | rewrite T3, H3, <- r3, G3; reflexivity | rewrite T4, H4, <- r4, G4; reflexivity
          | apply TS; cbn; right; exact Hi ]. }
      split.
      { exists LB. split.
        - exists (L5.BO fbR Ln stR), wy'. split. exact OBY5. split. exact YL5. cbn [L5.bo_st]. unfold same_st, sty in SST. unfold sty.
          destruct (L5.bo_st by_) as [y0 y1|cy qy] in SST |- *; destruct stR as [v0 v1|capR rd]; try (exfalso; exact SST).
          + reflexivity.
          + destruct SST as (-> & ->). split. reflexivity. split. reflexivity. split. reflexivity. exact YD5.
        - exists (2 * qneg), 0%nat, (L5.BInl q0 q1). split. exact OBQ5. reflexivity. }
      split.
      { destruct AOK as [OBa SGa]. split. 2: exact SGa.
        eapply big_at_agree1. 4: { eapply (L5C.big_at_agree RSEGS M0 M). 4: exact OBa. 2: flia. 2: flia.
          intros i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
          unfold WN. apply L5C.outside_cons. unfold L5.in_rng; cbn; generalize AP1; flia. apply L5C.outside_cons.
          { unfold L5.in_rng; cbn. unfold yd0, capy, L5.bo_data, L5.bo_cap. pose proof YOK as (OB0 & _ & _ & BLK). unfold L5.big_at in OB0.
            destruct (L5.bo_st by_) as [y0 y1|cy qy]. generalize AP1; flia.
            pose proof (LBhi _ _ _ _ HH0 _ (proj1 BLK)) as BH. cbn in BH. flia. }
          apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
        intros i Hi. apply KST5; flia. flia. flia. }
      split. exact CRA.
      eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M5 (sp - 352) OPDEL_SCR []). exact HP. exact HP5.
      * intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. exact Hb. } fsclia. flia. intros _. apply L5C.outside_nil.
      * intros b Hb. exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
    + eapply L5C.model_but_vm_trans. exact MBV. exact MBV5.
    + exact HH5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E4 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc nb : list (Z * Z)) (crc : credit)
      (c fden fnum qneg : Z) (stn : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 10) = Z_to_bv 64 c -> getr R (reg 18) = Z_to_bv 64 Y ->
  getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (Z.land fbY 2) -> getr R (reg 26) = Z_to_bv 64 qneg ->
  L5.u64_at RSEGS M (sp - 144) 2 ->
  0 <= qneg <= 1 -> (c = L5CMPU.MAXW \/ (0 <= c <= 1 /\ (2 <= Ln)%nat)) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = nb ++ LB -> nb = match stn with L5.BDyn c q => [(q, 8 * c)] | L5.BInl _ _ => [] end -> credit_after L cr 1 (8 * capy) crc ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 184) (L5.BO fnum Ln stn) -> L5C.obj_limbs RSEGS M (L5.BO fnum Ln stn) wy -> Z.testbit fnum 1 = false ->
  match sty, stn with
  | L5.BDyn c q, L5.BDyn c' q' => c' = c /\ (q + 8 * c <= q' \/ q' + 8 * c' <= q) /\ L5.defined M q' (8 * c') /\ block_range L q' (8 * c') /\ blocks_apart q' (8 * c') LB
  | L5.BInl _ _, L5.BInl _ _ => True
  | _, _ => False end ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  zero_obj M Q -> L5.defined M Q 32 ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x225b8 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H10 H18 H23 H25 H26 VS Hq HC MBV HH ELB ENB CRA DS OBN OLN Fnb1 NST OBD Fdb1 OBY OLY DY DYD ZQ0 DQ IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (LN267: (Ln <= 267)%nat). { unfold sty in LNS. unfold capy, L5.bo_cap in CAPR. destruct (L5.bo_st by_) in LNS, CAPR; flia. }
  pose proof YOK as (_ & _ & RED & BLK).
  pose proof OBN as (Nb0 & Nfr & Nb8 & NSTF). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nfr, Nb8, NSTF.
  pose proof OLN as (WL & WO & WLA). cbn [L5.bo_len L5.bo_st] in WL, WLA.
  pose proof OBY as OBY'. unfold L5.big_at in OBY'. fold fbY Ln sty in OBY'. destruct OBY' as (Yb0 & _ & Yb8 & YST).
  assert (WRF: L5.writable RSEGS M (sp - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  assert (NBLK: forall cap q, stn = L5.BDyn cap q -> In (q, 8 * cap) LBc /\ q + 8 * cap <= hl_ceil L /\ 4096 <= q /\ Z.of_nat Ln + 1 <= cap /\ cap <= 268 /\ cap = capy).
  { intros cap q ->. unfold sty in NST, LNS. unfold capy, L5.bo_cap in CAPR |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in NST, LNS, CAPR |- *. exfalso; exact NST.
    destruct NST as (-> & AP & Dq & BR & BA). assert (INq: In (q, 8 * cy) LBc) by (rewrite ELB, ENB; left; reflexivity).
    pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & (Qlo & _) & Qhi & _). repeat split; try assumption; flia. }
  assert (SUBc: forall b, In b LB -> In b LBc). { intros b Hb. rewrite ELB. apply in_app_iff. right. exact Hb. }
  unfold cfg.
  destruct HC as [EC|[Hc LN2]].
  - (* [comment removed for export] *)
    subst c. unfold L5CMPU.MAXW in H10.
    pose proof (L5DIVOPU.d6ue4e_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
    destruct (P ltac:(flia) H2 H10 ltac:(flia) A16) as (fx1 & R1 & M1 & _ & FR1 & _ & MS1 & K1). clear P.
    pose proof (mem_eq M M1 FR1) as EM. subst M1.
    eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    eapply (@L5DIVEARLYU.early_path _ L HI LY HIok ASSIGN fx1 R1 M model K LBc crc sp Y Q qneg (Z.land fbY 2) by_ (L5.BO fnum Ln stn) wy R0
              ltac:(rewrite (K1 2%nat) by inl; exact H2) ltac:(rewrite (K1 3%nat) by inl; exact H3) ltac:(rewrite (K1 4%nat) by inl; exact H4)
              ltac:(rewrite (K1 26%nat) by inl; exact H26) Hq ltac:(rewrite (K1 9%nat) by inl; exact H9) ltac:(rewrite (K1 25%nat) by inl; exact H25)
              (land2_cases fbY (proj1 FBY)) ltac:(rewrite (K1 8%nat) by inl; exact H8) HH MOK HK0).
    + (* [comment removed for export] *) split. exact A16. split. rewrite L5DIVEARLYU.DIV_SCR_val. flia. split. flia. split. exact SPTOP.
      rewrite L5DIVEARLYU.DIV_SCR_val. eapply L5.defined_sub. exact SCR0. flia. flia.
    + exact OBY.
    + fold Ln. flia.
    + exact AY8. + flia. + exact HY. + exact DY.
    + intros cap q E. apply SUBc. rewrite E in BLK. exact (proj1 BLK).
    + exact OBN. + exact OLN. + reflexivity.
    + cbn [L5.bo_st]. intros cap q E. exact (proj1 (NBLK cap q E)).
    + cbn [L5.bo_st]. intros c0 q c' q' E1 E2. subst stn. unfold sty in NST. rewrite E1 in NST. exact (proj1 (proj2 NST)).
    + exact ZQ0. + exact AQ8. + flia. + exact HQ. + exact DQ.
    + right. exact AP2.
    + exact DS.
    + (* [comment removed for export] *)
      cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data]. fold fbY Ln.
      intros fx2 R2 M2 model2 q0 q1 stx T2 T3 T4 TS OBQ2 OBY2 OLY2 STM DY2 DQ2 DS2 KLOC HP2 MBV2 HH2.
      pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
      (* [comment removed for export] *)
      assert (CDEF2: forall a n, L5.defined M a n -> (forall i, a <= i < a + n -> sp <= i < hl_sptop L \/ in_block LBc i) -> L5.defined M2 a n).
      { intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
        - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. right; left. unfold hl_ceil. rewrite L5DIVEARLYU.DIV_SCR_val. flia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
        - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
          apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
      (* [comment removed for export] *)
      set (c2 := match stn with L5.BInl _ _ => 0 | L5.BDyn cq _ => cq end). set (p2 := match stn with L5.BInl _ _ => 0 | L5.BDyn _ p => p end).
      assert (LO2: local_obj M (sp - 184) fnum c2 p2 /\ nb = (if Z.testbit fnum 0 then [(p2, 8 * c2)] else [])).
      { subst c2 p2. destruct stn as [v0 v1|cq p].
        - destruct NSTF as (Tb & _). split. split. exact Nb0. split. exact Nfr. intros T. rewrite Tb in T. discriminate T. rewrite ENB, Tb. reflexivity.
        - destruct NSTF as (Tb & C16 & C24 & Hlc & Hcap & _ & Qlo & Qhi & _). destruct (NBLK cq p eq_refl) as (_ & _ & _ & _ & Hc268 & _).
          split. split. exact Nb0. split. exact Nfr. intros _. split. exactA C16. split. flia. split. exactA C24. flia. rewrite ENB, Tb. reflexivity. }
      destruct LO2 as [LO2 ENB'].
      pose proof OBD as (Db0 & Dfr & Db8 & (Dtb & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Db0, Dfr, Db8, Dtb.
      eapply (stage_T2 fx2 R2 M2 model2 LBc nb crc fnum c2 p2 fden (L5DIVEARLYU.early_fb fbY fnum Ln (Z.land fbY 2)) q0 q1 qneg stx).
      * exact T2. * exact T3. * exact T4.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * exact HH2. * exact ELB. * exact ENB'.
      * eapply credit_weaken. exact CRA. unfold DIVO2_K; flia. unfold divO2_bytes; flia.
      * exact DS2.
      * eapply L5DIVO2AU.local_obj_kept. 4: exact LO2. intros i Hi; apply KLOC; flia. flia. flia.
      * eapply u8_at_agree1. 4: exact Db0. intros i Hi; apply KLOC; flia. flia. flia.
      * exact Dfr. * exact Dtb.
      * exact OBY2.
      * unfold same_st, sty. destruct (L5.bo_st by_) as [y0 y1|cy qy] in STM |- *; destruct stx as [v0 v1|c' q']; exact STM.
      * exact DY2.
      * apply CDEF2. exact DYD. intros i Hi. unfold yd0, capy, L5.bo_data, L5.bo_cap in Hi.
        destruct (L5.bo_st by_) as [y0 y1|cy qy] in Hi, BLK. left; unfold hl_ceil in *; flia.
        right. exists (qy, 8 * cy). split. apply SUBc. exact (proj1 BLK). cbn. flia.
      * exact OBQ2.
      * eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 sp DIV_SCR [(Y, 32); (L5.bo_data Y by_, 8 * Z.of_nat Ln); (Q, 32)]). exact HP. exact HP2.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. exact SUBc. rewrite L5DIVEARLYU.DIV_SCR_val; fsclia. flia.
           intros OW. apply L5C.outside_cons. exact (OW _ ltac:(left; reflexivity)).
           apply L5C.outside_cons.
           { unfold L5.in_rng; cbn [fst snd]. pose proof (OW (yd0, 8 * capy) ltac:(right; left; reflexivity)) as O2. unfold L5.in_rng in O2; cbn [fst snd] in O2.
             unfold yd0, capy, L5.bo_data, L5.bo_cap in O2 |- *. unfold sty in LNS. destruct (L5.bo_st by_) as [y0 y1|cy qy] in O2, LNS |- *; generalize O2; flia. }
           apply L5C.outside_cons. exact (OW _ ltac:(right; right; left; reflexivity)). apply L5C.outside_nil.
        -- exact SUBc.
        -- try rewrite L5DIVEARLYU.DIV_SCR_val; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
  - (* [comment removed for export] *)
    destruct stn as [v0 v1|cn B1].
    + (* [comment removed for export] *)
      destruct NSTF as (Tb & N16 & N24 & _).
      assert (YI: exists y0 y1, sty = L5.BInl y0 y1). { unfold sty in NST |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy]. eexists _, _; reflexivity. exfalso; exact NST. }
      destruct YI as (y0 & y1 & EY). pose proof EY as EY'. unfold sty in EY'. pose proof YST as YST'. rewrite EY in YST'. destruct YST' as (Ytb & _).
      pose proof ZQ0 as ZQ'. unfold zero_obj, L5.big_at in ZQ'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in ZQ'. destruct ZQ' as (Qf0 & _ & Ql0 & _).
      pose proof (d7ue4i_conc fx R M (VdX 0 fnum (Z.of_nat Ln) 0 c)) as P. cbn [VdX Vd VdO] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
                  H2 H9 H10 H18 ltac:(flia) A16 WRF Nb0 ltac:(exactA Nb8) VS Hc ltac:(flia) Tb ltac:(flia) ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia) ltac:(exactA Yb8) Ytb ltac:(flia)
                  ltac:(flia) AQ8 ltac:(left; flia) Qf0 ltac:(exactA Ql0))
        as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & A10 & A11 & A12 & A13 & A14 & A21 & C240 & C248 & C224 & C232). clear P.
      assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 248 <= i < sp - 216) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn'. apply FR1. exact Hi. flia. flia. }
      assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
      { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
        intros a Ha. destruct (Z_lt_le_dec a (sp - 248)) as [X|X]. left; apply KEEP1; flia. destruct (Z_lt_le_dec a (sp - 216)) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KEEP1; flia. }
      eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
      eapply (stage_G1 fx1 R1 M1 model LBc nb crc fden fnum qneg (L5.BInl v0 v1)).
      all: try (rewrite (K1 _) by inl; eassumption).
      * exact LN2. * exact Hq. * exact MBV. * exact HH1. * exact ELB. * exact ENB. * exact CRA.
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KEEP1; flia. flia. flia.
      * eapply big_at_agree1. 4: exact OBN. intros i Hi; apply KEEP1; flia. flia. flia.
      * exact OLN.
      * exact Fnb1.
      * exact NST.
      * eapply big_at_agree1. 4: exact OBD. intros i Hi; apply KEEP1; flia. flia. flia.
      * exact Fdb1.
      * eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KEEP1; flia. flia. flia.
      * pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. rewrite EY' in YL3 |- *. exact YL3.
      * eapply L5.defined_grows. exact MG1. exact DY.
      * eapply L5.defined_grows. exact MG1. exact DYD.
      * unfold zero_obj. eapply big_at_agree1. 4: exact ZQ0. intros i Hi; apply KEEP1; flia. flia. flia.
      * eapply L5.defined_grows. exact MG1. exact DQ.
      * intros i Hi. rewrite KEEP1. exact (IMG1 i Hi). flia. flia.
      * eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
        -- eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => sp - 248 <= a < sp - 216)).
           ++ intros a Ha Hn'. apply KEEP1; flia.
           ++ intros a KA C0. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
           ++ rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
           ++ exact MG1.
        -- intros a KA; exact KA. -- intros b Hb; exact Hb. -- fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
    + (* [comment removed for export] *)
      destruct NSTF as (Tb & N16 & N24 & Hlc & Hcap & B18 & B1lo & B1hi & _).
      assert (YD: exists cy qy, sty = L5.BDyn cy qy). { unfold sty in NST |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy]. exfalso; exact NST. eexists _, _; reflexivity. }
      destruct YD as (cy & qy & EY). pose proof EY as EY'. unfold sty in EY'. pose proof YST as YST'. rewrite EY in YST'. destruct YST' as (Ytb & Y16 & Y24 & _ & Cyr & Qy8 & Qylo & Qyhi & _).
      pose proof ZQ0 as ZQ'. unfold zero_obj, L5.big_at in ZQ'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in ZQ'. destruct ZQ' as (Qf0 & _ & Ql0 & _).
      destruct (NBLK cn B1 eq_refl) as (_ & B1hi' & B1lo' & _).
      pose proof (d7ue4d_conc fx R M (VdX qy fnum (Z.of_nat Ln) B1 c)) as P. cbn [VdX Vd VdO] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold hl_ceil in *; flia) ltac:(flia) ltac:(flia) ltac:(unfold hl_ceil in *; flia) ltac:(flia)
                  H2 H9 H10 H18 ltac:(flia) A16 WRF Nb0 ltac:(exactA Nb8) ltac:(exactA N24) VS Hc ltac:(flia) Tb ltac:(flia) ltac:(unfold hl_ceil in *; flia)
                  ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia) ltac:(exactA Yb8) Ytb ltac:(flia) ltac:(exactA Y24) ltac:(unfold hl_ceil in *; flia)
                  ltac:(flia) AQ8 ltac:(left; flia) Qf0 ltac:(exactA Ql0))
        as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & A10 & A11 & A12 & A13 & A14 & A21 & C240 & C248 & C224 & C232). clear P.
      assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 248 <= i < sp - 216) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn'. apply FR1. exact Hi. flia. flia. }
      assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
      { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
        intros a Ha. destruct (Z_lt_le_dec a (sp - 248)) as [X|X]. left; apply KEEP1; flia. destruct (Z_lt_le_dec a (sp - 216)) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KEEP1; flia. }
      eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
      eapply (stage_G1 fx1 R1 M1 model LBc nb crc fden fnum qneg (L5.BDyn cn B1)).
      all: try (rewrite (K1 _) by inl; eassumption).
      * exact LN2. * exact Hq. * exact MBV. * exact HH1. * exact ELB. * exact ENB. * exact CRA.
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KEEP1; flia. flia. flia.
      * eapply big_at_agree1. 4: exact OBN. intros i Hi; apply KEEP1; flia. flia. flia.
      * pose proof OLN as (NL1 & NL2 & NL3). split. exact NL1. split. exact NL2. cbn [L5.bo_st] in NL3 |- *.
        destruct (NBLK cn B1 eq_refl) as (_ & Bhi & Blo & _). eapply limbs_at_agree1. 4: exact NL3. 2: flia. 2: rewrite WL; unfold hl_ceil in *; flia.
        intros i Hi; apply KEEP1; unfold hl_ceil in *; flia.
      * exact Fnb1.
      * unfold sty in NST |- *. rewrite EY' in NST |- *. destruct NST as (Ec & AP & Dq & BR & BA). split. exact Ec. split. exact AP. split.
        eapply L5.defined_grows. exact MG1. exact Dq. split. exact BR. exact BA.
      * eapply big_at_agree1. 4: exact OBD. intros i Hi; apply KEEP1; flia. flia. flia.
      * exact Fdb1.
      * eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KEEP1; flia. flia. flia.
      * pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. rewrite EY' in YL3 |- *.
        pose proof BLK as BLK'. rewrite EY' in BLK'. destruct BLK' as (INY & DYq & LNY). fold Ln in LNY.
        pose proof (LBdef _ _ _ _ HH0 _ _ INY) as (_ & (Ylo & _) & Yhi & _).
        eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
        intros i Hi. rewrite YL1 in Hi. fold Ln in Hi. apply KEEP1; unfold hl_ceil in *; flia.
      * eapply L5.defined_grows. exact MG1. exact DY.
      * eapply L5.defined_grows. exact MG1. exact DYD.
      * unfold zero_obj. eapply big_at_agree1. 4: exact ZQ0. intros i Hi; apply KEEP1; flia. flia. flia.
      * eapply L5.defined_grows. exact MG1. exact DQ.
      * intros i Hi. rewrite KEEP1. exact (IMG1 i Hi). flia. flia.
      * eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
        -- eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => sp - 248 <= a < sp - 216)).
           ++ intros a Ha Hn'. apply KEEP1; flia.
           ++ intros a KA C0. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
           ++ rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
           ++ exact MG1.
        -- intros a KA; exact KA. -- intros b Hb; exact Hb. -- fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2JU.
