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
 AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore AsanAcct
 Ub0_code_201fc_21084 Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkDivBaseU L5Defs L5Kn L5Core L5CoreSpecsU L5CoreKitU L5Words L5Hp
 L5ShlU L5MulMU L5Norm L5NormU L5CmpU L5CoreKit L5DivSpecsU L5DivPartsU L5DivNPU L5DivOPU L5DivO2PU L5DivEarlyU L5OpMod1SU L5OpMod1HU L5OpMod1V L5OpMod1GU L5OpMod1GBU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigFactsBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5OPMOD1GCU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVOPU. Import L5DIVO2PU. Import L5OM1SU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Local Notation preserved_sregs := L5DIVEARLYU.preserved_sregs.
Local Notation u64_at_agree1 := L5DIVEARLYU.u64_at_agree1.
Local Notation u8_at_agree1 := L5DIVEARLYU.u8_at_agree1.
Local Notation big_at_agree1 := L5DIVEARLYU.big_at_agree1.
Local Notation defined_agree1 := L5DIVEARLYU.defined_agree1.
Local Notation model_ok_but_vm := L5DIVEARLYU.model_ok_but_vm.
Local Notation mem_eq := L5DIVEARLYU.mem_eq.
Local Notation mod16_mod8 := L5DIVEARLYU.mod16_mod8.
Local Notation outside1 := L5DIVEARLYU.outside1.
Local Notation outside2 := L5DIVEARLYU.outside2.
Local Notation outside3 := L5DIVEARLYU.outside3.
Local Notation obj_limbs_agree1 := L5DIVEARLYU.obj_limbs_agree1.
Local Notation top_frame_kept := L5OPMOD1HU.top_frame_kept.
Local Notation hpres_wmono := L5OPMOD1HU.hpres_wmono.
Local Notation al8 := L5OPMOD1HU.al8.
Local Notation cs_all := L5OPMOD1HU.cs_all.

Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac kreg K i H := etransitivity; [exact (K i ltac:(inl)) | exact H].
Local Ltac uSCR := unfold SCR_OPMOD, DIV_SCR, L5NORMU.NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR,
  OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac prune_mod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; prune_mod; lia.
Local Ltac fsclia := prune_impl; prune_disj; prune_mod; uSCR; lia.
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].

(* [comment removed for export] *)
Local Notation SCR_OPMOD_val := L5OPMOD1GU.SCR_OPMOD_val.
Local Notation DIV_SCR_val := L5OPMOD1GU.DIV_SCR_val.
Local Notation RESIZE_SCR_val := L5OPMOD1GU.RESIZE_SCR_val.
Local Notation ASSIGN_SCR_val := L5OPMOD1GU.ASSIGN_SCR_val.
Local Notation u32_at_agree1 := L5OPMOD1GU.u32_at_agree1.
Local Notation o1_saves_kept := L5OPMOD1GU.o1_saves_kept.
Local Notation local_obj_kept := L5OPMOD1GU.local_obj_kept.
Local Notation blocks_ofst_inl := L5OPMOD1GU.blocks_ofst_inl.
Local Notation blocks_ofst_dyn := L5OPMOD1GU.blocks_ofst_dyn.

(* [comment removed for export] *)
Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis COPYA : copya_spec L HI.
Hypothesis ASSIGN : assign_spec L HI.
Hypothesis RESIZE : resize_spec L HI.
Hypothesis NORM : L5NORMU.norm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.

Let IMG := L5DIVEARLYU.IMG L LY.
Let IMGLO := L5DIVEARLYU.IMGLO L LY.
Let ERRNOV := L5DIVEARLYU.ERRNOV L LY.
Let LBdef := @L5DIVEARLYU.LBdef _ L HI HIok.
Let kept_above := L5DIVEARLYU.kept_above L LY.
Let kept_inblock := @L5DIVEARLYU.kept_inblock _ L HI LY HIok.
Let cdef_above := L5DIVEARLYU.cdef_above L LY.
Let cdef_below := L5DIVEARLYU.cdef_below L LY.
Let hi_heap_stackwrite := @L5DIVEARLYU.hi_heap_stackwrite _ L HI LY HIok.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (S fbx bo : Z) (bb : L5.bigobj) (wb : list Z) (b0 b1 fnum fden : Z).
Let capb : Z := L5.bo_cap bb.
Let X : Z := S + 64.
Let Q : Z := S - 64.
Let spd : Z := S - 416.
Let nb : nat := L5.bo_len bb.
Let qneg : Z := Z.b2z (Z.testbit (L5.bo_fb bb) 1).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis BO : bo = S + 128.
Hypothesis STK : L5C.stk (hl_sptop L) M0 S SCR_OPMOD.
Hypothesis HS : S + 240 <= hl_sptop L.
Hypothesis BOK : b_ok LB M0 bo bb wb.
Hypothesis CR : credit_for L cr OPMOD1_K (opmod1_bytes capb).
Hypothesis STB : L5.bo_st bb = L5.BInl b0 b1.
Hypothesis NB12 : nb = 1%nat \/ nb = 2%nat.
Hypothesis V1 : nb = 1%nat -> 2 ^ 32 <= b0.
Hypothesis V2 : nb = 2%nat -> BigFactsBase.val wb <= BigFactsBase.val [A0; A1].
(* [comment removed for export] *)
Let c : Z := L5OM1V.c nb wb.
Let sec : bool := L5OM1V.sec nb wb.
Let rwd : list Z := L5OM1V.rwd nb wb.
Let rwn : list Z := L5OM1V.rwn nb wb.
Let l1 : nat := rlen rwd.
Let n1 : nat := rlen rwn.
Let d : Z := nth_w rwd (l1 - 1).
Let sd : Z := (if sec then 1 else 0).

(* [comment removed for export] *)
Hypothesis KT : forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (c_ sd_ qneg_ : Z) (n_ : nat) (fq : Z) (nq : nat) (stq : L5.bstore) (fx_ : Z) (rst : L5.bstore) (wr : list Z)
      (fnum' cnum pnum fden' cden pden fn0 fd0 : Z),
    let BN := (if Z.testbit fnum' 0 then [(pnum, 8 * cnum)] else []) in
    let BD := (if Z.testbit fden' 0 then [(pden, 8 * cden)] else []) in
    let LBc := blocks_ofst stq ++ blocks_ofst rst ++ BN ++ BD ++ LB in
    getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
    getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
    model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
    fst cr - 4 * hl_k_per_malloc L <= fst crc -> snd cr - 4 * (64 + hl_b_overhead L) <= snd crc ->
    L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
    top_frame M S R0 -> o1_saves M S R0 ->
    local_obj M (S - 344) fd0 0 0 -> Z.testbit fd0 0 = false -> local_obj M (S - 280) fn0 0 0 -> Z.testbit fn0 0 = false ->
    local_obj M (S - 248) fnum' cnum pnum -> (Z.testbit fnum' 0 = true -> cnum = 8 /\ L5C.fresh_block L LB M pnum 64) ->
    local_obj M (S - 200) fden' cden pden -> (Z.testbit fden' 0 = true -> cden = 8 /\ L5C.fresh_block L (BN ++ LB) M pden 64) ->
    L5.u32_at RSEGS M (S - 348) c_ -> 0 <= c_ <= 63 ->
    L5.u64_at RSEGS M (S - 400) 1 -> L5.u64_at RSEGS M (S - 384) 0 ->
    L5.u64_at RSEGS M (S - 392) qneg_ -> 0 <= qneg_ <= 1 -> L5.u64_at RSEGS M (S - 408) sd_ -> (sd_ = 0 \/ sd_ = 1) ->
    L5.big_at RSEGS M Q (L5.BO fq nq stq) -> (nq <= 3)%nat ->
    (forall cq p, stq = L5.BDyn cq p -> cq = 8 /\ L5C.fresh_block L (blocks_ofst rst ++ BN ++ BD ++ LB) M p 64) ->
    L5.big_at RSEGS M X (L5.BO fx_ (Datatypes.S n_) rst) -> Z.testbit fx_ 1 = false ->
    L5C.obj_limbs RSEGS M (L5.BO fx_ (Datatypes.S n_) rst) wr -> L5.defined M X 32 ->
    (forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ L5C.fresh_block L (BN ++ BD ++ LB) M p 64) ->
    (sd_ = 1 -> (exists qx, rst = L5.BDyn 8 qx) /\ (1 <= n_ <= 5)%nat /\ (exists q0 q1, stq = L5.BInl q0 q1) /\ Z.testbit fnum' 0 = true /\ Z.testbit fden' 0 = true) ->
    L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (1 <= L5.bo_len bb)%nat ->
    (forall cap q, L5.bo_st bb = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
    srealizes RSEGS SCFG (cfg R LEXIT M model) K.

(* [comment removed for export] *)
Let SPW := @L5OPMOD1GU.SPW L M0 S bb wb b0 STK HS NB12 V1 V2.
Let WBF := @L5OPMOD1GU.WBF M0 LB bo bb wb b0 b1 BOK STB NB12.
Let OLB_any := @L5OPMOD1GU.OLB_any M0 LB bo bb wb b0 b1 BOK STB.
Let NF := @L5OPMOD1GU.NF M0 LB bo bb wb b0 b1 BOK STB NB12 V1 V2.
Let Hc63 := @L5OPMOD1GU.Hc63 M0 LB bo bb wb b0 b1 BOK STB NB12 V1 V2.
Let Hq01 := @L5OPMOD1GU.Hq01 S bb wb b0 NB12 V1 V2.
Let SCR_kept := @L5OPMOD1GU.SCR_kept L LY M0 S bb wb b0 STK HS NB12 V1 V2.
Let IC_kept := @L5OPMOD1GU.IC_kept L LY.
Let CAPB2 := @L5OPMOD1GU.CAPB2 bb b0 b1 STB.
Let credit_next := @L5OPMOD1GU.credit_next L KPOS BPOS cr S bb wb b0 b1 CR STB NB12 V1 V2.
Let credit_step := @L5OPMOD1GU.credit_step L cr S bb wb b0 NB12 V1 V2.
Let mid := @L5OPMOD1GU.mid L R0 LB S bb wb.
Let stage_G4 := @L5OPMOD1GBU.stage_G4 _ L HI LY HIok KPOS BPOS ASSIGN RESIZE DIVLOOP R0 M0 model0 K LB cr S fbx bo bb wb b0 b1 MOK0 HK0 BO STK HS BOK CR STB NB12 V1 V2 KT.

(* [comment removed for export] *)
Lemma NF' : (1 <= l1 <= 3)%nat /\ (2 <= n1 <= 4)%nat /\ (l1 <= n1)%nat /\ (n1 - l1 <= 2)%nat
  /\ (l1 <= length rwd)%nat /\ (length rwd <= 3)%nat /\ (n1 <= length rwn)%nat /\ (length rwn <= 4)%nat
  /\ 2 ^ 63 <= d < 2 ^ 64
  /\ (sec = true -> nb = 2%nat /\ l1 = 3%nat /\ (3 <= n1)%nat /\ length rwd = 3%nat /\ (3 <= length rwn)%nat)
  /\ (sec = false -> l1 = nb /\ (n1 <= 3)%nat)
  /\ ((3 <= length rwd)%nat <-> nb = 2%nat)
  /\ ((3 <= length rwn)%nat <-> 1 <= c)
  /\ (nb = 2%nat -> 1 <= c).
Proof. exact NF. Qed.
Lemma obj_limbs_x M fb : L5C.obj_limbs RSEGS M (L5.BO fb 2 (L5.BInl A0 A1)) [A0; A1].
Proof using L R0 M0 LB S bo bb wb b0 b1 BOK STB NB12 V1 V2. split. reflexivity. split. pose proof L5OPMOD1HU.A0_rng. pose proof L5OPMOD1HU.A1_rng. repeat constructor; lia. reflexivity. Qed.

Local Ltac zlia := flia.
Local Ltac pside :=
  first [ eassumption
        | lazymatch goal with
          | |- getr ?R (Z_to_bv 5 ?i) = _ => match goal with H : getr R (Z_to_bv 5 i) = _ |- _ => rewrite H; first [reflexivity | f_equal; zlia] end
          | |- L5.u64_at _ ?M ?a ?v' => match goal with H : L5.u64_at _ M ?b ?v |- _ => replace a with b by zlia; replace v' with v by zlia; exact H end
          | |- L5.u8_at _ ?M ?a ?v' => match goal with H : L5.u8_at _ M ?b ?v |- _ => replace a with b by zlia; exact H end
          | |- L5.writable _ ?M ?a ?n => match goal with H : L5.writable _ M ?b n |- _ => replace a with b by zlia; exact H end
          | |- aligned ?a _ => unfold aligned; assumption
          | |- _ \/ _ => first [left; zlia | right; zlia]
          | |- _ => zlia
          end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (fn0 fd0 : Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 22) = Z_to_bv 64 (Q - 120) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  top_frame M S R0 -> o1_saves M S R0 ->
  local_obj M (S - 344) fd0 0 0 -> Z.testbit fd0 0 = false -> local_obj M (S - 280) fn0 0 0 -> Z.testbit fn0 0 = false ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (S - 248) (L5.BO fnum 2 (L5.BInl A0 A1)) -> Z.testbit fnum 1 = false ->
  L5.big_at RSEGS M (S - 200) (L5.BO fden nb (L5.BInl b0 b1)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x227b8 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H22 H23 H25 H26 MBV HH SCR IC TF SAV LO0 F0b LO1 F1b ZQ XA DX ON FN1 OD FD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF' as (L13 & N24 & LN' & NL2 & LLR & LR3 & NLR & LR4 & DR & SECF & SECF' & LRD & LRN & C1). pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof WBF as (WB & Rb0 & Rb1 & TOPNZ).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (WFR: L5.writable RSEGS M (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI SLO; lia. }
  (* [comment removed for export] *)
  pose proof (d5ug3_conc fx R M (fun j => match j with 2%nat => Q | 33%nat => X | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold X; clear - SLO SHI; lia) ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H18
              ltac:(unfold Q; clear - SLO SHI; lia) AQ16 WFR)
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & Ara & A10 & A11 & A12 & A13 & C284)). clear P.
  unfold Q in C284, FR1. replace (S - 64 - 284) with (S - 348) in C284, FR1 by (clear; lia).
  assert (KF: forall i, 0 <= i < 2 ^ 64 -> ~ (S - 348 <= i < S - 344) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn. apply FR1. exact Hi. clear - Hn; lia. }
  assert (KU: forall i, S - 344 <= i < S + 200 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KF; clear - Hi SLO SHI; lia. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model)).
  { eapply (hi_heap_stackwrite LB cr M M1 _ (S - 348) (S - 344)). exact HH. exact KF. clear - SLO'; lia. clear - SHI'; lia. exact (proj1 SPT). exact MG1. }
  assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
  assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (HP1: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M1).
  { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M1 S SCR_OPMOD [(X, 32)]). exact HP.
    - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M1 (fun a => S - 348 <= a < S - 344)). exact KF.
      { intros a KA' C'. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' LBceil CEILS _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. clear - C'; lia. }
      rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR'. exact MG1.
    - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEILS. - clear - SHI; lia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - exact (proj1 SPT). }
  assert (SCR1: L5.defined M1 (S - 10240) 10240) by (eapply L5.defined_grows; [exact MG1 | exact SCR']).
  assert (ON1: L5.big_at RSEGS M1 (S - 248) (L5.BO fnum 2 (L5.BInl A0 A1))). { eapply big_at_agree1. 4: exact ON. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  assert (OD1: L5.big_at RSEGS M1 (S - 200) (L5.BO fden nb (L5.BInl b0 b1))). { eapply big_at_agree1. 4: exact OD. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  pose proof OD as (Db0 & Df & D8 & DT & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Db0, Df, D8, DT.
  pose proof ON as (Nb0 & Nf & N8 & NT & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nf, N8, NT.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  eapply (NORM fx1 R1 M1 model K LB cr (S - 200) (S - 248) (S - 348) spd 0x227d0 (L5.BO fden nb (L5.BInl b0 b1)) (L5.BO fnum 2 (L5.BInl A0 A1)) wb [A0; A1] HH1 MOK HK0).
  - etransitivity. exact A11. unfold Q; f_equal; clear; lia.
  - etransitivity. exact A12. unfold Q; f_equal; clear; lia.
  - etransitivity. exact A13. unfold Q; f_equal; clear; lia.
  - exact Ara.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; clear - SHI'; lia. split. exact SPT. unfold spd. uSCR. eapply L5.defined_sub. exact SCR1. clear; lia. clear; lia.
  - exact OD1.
  - pose proof (OLB_any M1) as (Ln & Wok & Wst). rewrite STB in Wst. split. exact Ln. split. exact Wok. exact Wst.
  - cbn [L5.bo_len]. fold nb. clear - NB12; lia.
  - cbn [L5.bo_len]. fold nb. exact TOPNZ.
  - cbn [L5.bo_len]. fold nb. intros NB2. assert (E2: nb = 2%nat) by (clear - NB2 NB12; lia). pose proof (L5OM1V.b1_small nb b0 b1 wb NB12 WB Rb0 Rb1 V1 V2 E2) as B1.
    rewrite WB. unfold nb. replace (L5.bo_len bb) with 2%nat by (symmetry; exact E2). cbn. clear - B1; lia.
  - exact ON1.
  - apply obj_limbs_x.
  - cbn [L5.bo_len]. clear; lia.
  - cbn [L5.bo_len]. intros _. split. clear; lia. exists 1%nat. split. clear; lia. cbn. unfold A1. clear. vm_compute. discriminate.
  - replace (S - 200) with (S + 8 * (-25)) by (clear; lia). apply al8. exact A16.
  - replace (S - 248) with (S + 8 * (-31)) by (clear; lia). apply al8. exact A16.
  - unfold spd; clear; lia. - unfold spd; clear; lia. - clear - SHI'; lia. - clear - SHI'; lia.
  - unfold L5NORMU.apart; clear; lia.
  - eapply L5.defined_sub. exact SCR1. clear; lia. clear; lia.
  - eapply L5.defined_sub. exact SCR1. clear; lia. clear; lia.
  - replace (S - 348) with (S + (-87) * 4) by (clear; lia). rewrite Z_mod_plus_full. clear - A16. apply Z.mod_divide in A16. 2: lia. apply Z.mod_divide. lia. destruct A16 as [k Hk]. exists (4 * k). lia.
  - unfold spd; clear; lia. - clear - SHI'; lia.
  - unfold L5NORMU.apart; clear; lia. - unfold L5NORMU.apart; clear; lia.
  - eapply L5.defined_sub. exact SCR1. clear; lia. clear; lia.
  - intros cap q E. discriminate E.
  - intros cap q E. discriminate E.
  - intros _. split; intros T; exfalso. change (Z.testbit fden 0 = true) in T. rewrite DT in T. discriminate T. change (Z.testbit fnum 0 = true) in T. rewrite NT in T. discriminate T.
  - intros cd' qd cn' qn E. discriminate E.
  - unfold L5NORMU.credits, L5NORMU.cnt, L5.bo_dyn. cbn [L5.bo_fb]. rewrite DT, NT.
    pose proof CR as [CR1 CR2]. unfold credit_for, OPMOD1_K, opmod1_bytes in CR1, CR2. unfold capb in CR2. rewrite CAPB2 in CR2. pose proof KPOS. pose proof BPOS. split; clear - CR1 CR2 H H0; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 c' gd gn LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
    destruct POST as (RP2 & Ec' & Hc' & Hp' & R2_10 & Cpx & (std & stn & OAD & OAN) & ELB & ECR & FRd & FRn & HP2 & V2d & V2n).
    cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn] in Ec', Hp', R2_10, OAD, OAN, FRd, FRn, HP2, V2d, V2n.
    assert (Ecc: c' = c). { rewrite Ec'. reflexivity. }
    subst c'.
    change (L5NORMU.obj_after M2 (S - 200) (L5.BO fden nb (L5.BInl b0 b1)) rwd gd std) in OAD.
    change (L5NORMU.obj_after M2 (S - 248) (L5.BO fnum 2 (L5.BInl A0 A1)) rwn gn stn) in OAN.
    change (getr R2 10%bv = Z_to_bv 64 sd) in R2_10.
    change (match gd with Same => True | Grown _ _ => (3 <= length (L5OM1V.D nb wb))%nat \/ sec = true end) in V2d.
    change (match gn with Same => True | Grown _ _ => (3 <= length (L5OM1V.N nb wb))%nat \/ sec = true end) in V2n.
    set (fd := match gd with Same => fden | Grown _ _ => Z.lor fden 1 end).
    set (pd := match gd with Same => 0 | Grown A _ => A end).
    set (fn := match gn with Same => fnum | Grown _ _ => Z.lor fnum 1 end).
    set (pn := match gn with Same => 0 | Grown A _ => A end).
    destruct OAD as (_ & _ & ODEN & LDEN & DCAP & DG). destruct OAN as (_ & _ & ONUM & LNUM & NCAP & NG).
    cbn [L5.bo_fb L5.bo_st L5.bo_dyn] in ODEN, LDEN, DG, ONUM, LNUM, NG.
    replace (rlen rwd =? 0)%nat with false in ODEN, LDEN by (symmetry; apply Nat.eqb_neq; clear - L13; unfold l1 in L13; lia).
    replace (rlen rwn =? 0)%nat with false in ONUM, LNUM by (symmetry; apply Nat.eqb_neq; clear - N24; unfold n1 in N24; lia).
    change (L5.big_at RSEGS M2 (S - 200) (L5.BO fd l1 std)) in ODEN. change (L5C.obj_limbs RSEGS M2 (L5.BO fd (length rwd) std) rwd) in LDEN.
    change (L5.big_at RSEGS M2 (S - 248) (L5.BO fn n1 stn)) in ONUM. change (L5C.obj_limbs RSEGS M2 (L5.BO fn (length rwn) stn) rwn) in LNUM.
    (* [comment removed for export] *)
    assert (DSH: match gd with Same => (exists u0 u1, std = L5.BInl u0 u1) /\ Z.testbit fd 0 = false
                                | Grown A cap => std = L5.BDyn 8 A /\ cap = 8 /\ Z.testbit fd 0 = true /\ L5C.fresh_block L LB M2 A 64 end).
    { destruct gd as [|A cap]. { destruct std as [u0 u1|]. 2: destruct DG. split. eexists _, _; reflexivity. exact DT. }
      destruct DG as (_ & Ecap & ->). subst cap. split. reflexivity. split. reflexivity. split. subst fd. rewrite Z.lor_spec, DT. reflexivity. exact FRd. }
    assert (NSH: match gn with Same => (exists u0 u1, stn = L5.BInl u0 u1) /\ Z.testbit fn 0 = false
                                | Grown A cap => stn = L5.BDyn 8 A /\ cap = 8 /\ Z.testbit fn 0 = true /\ L5C.fresh_block L (L5NORMU.blocks_of gd ++ LB) M2 A 64 end).
    { destruct gn as [|A cap]. { destruct stn as [u0 u1|]. 2: destruct NG. split. eexists _, _; reflexivity. exact NT. }
      destruct NG as (_ & Ecap & ->). subst cap. split. reflexivity. split. reflexivity. split. subst fn. rewrite Z.lor_spec, NT. reflexivity. exact FRn. }
    set (BN := if Z.testbit fn 0 then [(pn, 8 * 8)] else []).
    set (BD := if Z.testbit fd 0 then [(pd, 8 * 8)] else []).
    assert (EBN: L5NORMU.blocks_of gn = BN). { subst BN pn. destruct gn as [|A cap]. destruct NSH as [_ ->]. reflexivity. destruct NSH as (_ & -> & -> & _). reflexivity. }
    assert (EBD: L5NORMU.blocks_of gd = BD). { subst BD pd. destruct gd as [|A cap]. destruct DSH as [_ ->]. reflexivity. destruct DSH as (_ & -> & -> & _). reflexivity. }
    rewrite EBN, EBD in ELB. subst LB2.
    assert (CR2: fst cr - 2 * hl_k_per_malloc L <= fst cr2 /\ snd cr - 2 * (64 + hl_b_overhead L) <= snd cr2).
    { subst cr2. pose proof KPOS. pose proof BPOS. destruct gn as [|An cn']; destruct gd as [|Ad cd']; cbn [L5NORMU.blocks_of L5NORMU.debits app];
        try destruct NSH as (_ & En & _); try destruct DSH as (_ & Ed & _); subst; unfold debit; cbn [fst snd]; clear - H H0; split; lia. }
    destruct CR2 as [CRK2 CRB2].
    (* [comment removed for export] *)
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (S - 200 <= a < S - 168) -> ~ (S - 248 <= a < S - 216) -> ~ (S - 348 <= a < S - 344) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha N1 N2 N3. apply (kept_above M1 M2 LB spd L5NORMU.NORM_SCR _ a HP2). unfold spd; fsclia. uSCR; clear; lia. exact (proj1 SPT). exact Ha.
      unfold L5NORMU.norm_W, L5NORMU.dyn_area. cbn [L5.bo_st app]. apply outside3; clear - N1 N2 N3; lia. }
    assert (E2r: forall i v, In i cs_all -> getr R1 (reg i) = v -> getr R2 (reg i) = v). { intros i v Hi Hv. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. exact Hv. }
    assert (G4r: forall i v, In i cs_all -> getr R (reg i) = v -> In i KS_d5ug3 -> getr R2 (reg i) = v).
    { intros i v Hi Hv Hk. apply (E2r i v Hi). rewrite (K1 i Hk). exact Hv. }
    apply (stage_G4 fx2 R2 M2 model2 cr2 2 fn 8 pn stn fd 8 pd std fn0 fd0).
    all: try (eapply G4r; [inl | eassumption | inl]).
    all: try exact R2_10.
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
    + exact HH2.
    + exact CRK2. + exact CRB2. + clear; lia.
    + rewrite SCR_OPMOD_val. eapply SCR_kept. exact HP2. uSCR; clear; lia. exact SCR1.
    + eapply IC_kept. exact HP2. 2:{ intros i Hi. rewrite KF. apply IC; exact Hi. clear - Hi; lia. clear - Hi SLO; lia. }
      intros a Ha. unfold L5NORMU.norm_W, L5NORMU.dyn_area. cbn [L5.bo_st app]. apply outside3; clear - Ha SLO; lia.
    + eapply top_frame_kept. 4:{ eapply top_frame_kept. 4: exact TF. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
      intros i Hi; apply KA; unfold spd; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia.
    + eapply o1_saves_kept. 4:{ eapply o1_saves_kept. 4: exact SAV. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
      intros i Hi; apply KA; unfold spd; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia.
    + eapply local_obj_kept. 4:{ eapply local_obj_kept. 4: exact LO0. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
      intros i Hi; apply KA; unfold spd; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia.
    + exact F0b.
    + eapply local_obj_kept. 4:{ eapply local_obj_kept. 4: exact LO1. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
      intros i Hi; apply KA; unfold spd; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia.
    + exact F1b.
    + (* [comment removed for export] *)
      pose proof ONUM as (U0 & Uf & U8 & US). cbn [L5.bo_fb L5.bo_len L5.bo_st] in U0, Uf, U8, US. split. exact U0. split. exact Uf.
      intros T. destruct gn as [|A cap]. { destruct NSH as [_ F]. exfalso. rewrite F in T. discriminate T. } destruct NSH as (Es & _ & _ & FB). rewrite Es in US.
      destruct US as (_ & U16 & U24 & _ & _ & _ & Alo & Ahi & _). split. exact U16. split. clear; lia. split. exact U24. clear - Alo Ahi. lia.
    + intros T. split. reflexivity. destruct gn as [|A cap]. { destruct NSH as [_ F]. exfalso. rewrite F in T. discriminate T. } destruct NSH as (_ & _ & _ & (B1' & B2' & B3')).
      split. exact B1'. split. { intros b Hb. apply B2'. apply in_app_iff. right. exact Hb. } exact B3'.
    + pose proof ODEN as (U0 & Uf & U8 & US). cbn [L5.bo_fb L5.bo_len L5.bo_st] in U0, Uf, U8, US. split. exact U0. split. exact Uf.
      intros T. destruct gd as [|A cap]. { destruct DSH as [_ F]. exfalso. rewrite F in T. discriminate T. } destruct DSH as (Es & _ & _ & FB). rewrite Es in US.
      destruct US as (_ & U16 & U24 & _ & _ & _ & Alo & Ahi & _). split. exact U16. split. clear; lia. split. exact U24. clear - Alo Ahi. lia.
    + intros T. split. reflexivity. destruct gd as [|A cap]. { destruct DSH as [_ F]. exfalso. rewrite F in T. discriminate T. } destruct DSH as (_ & Ecap & _ & (B1' & B2' & B3')).
      split. exact B1'. split. 2: exact B3'. intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]. 2: apply B2'; exact Hb.
      subst BN pn. destruct gn as [|An cn']. { destruct NSH as [_ F]. rewrite F in Hb. destruct Hb. } destruct NSH as (_ & _ & Tn & (_ & BAn & _)). rewrite Tn in Hb.
      destruct Hb as [<-|[]]. cbn. destruct (BAn (A, 8 * cap) ltac:(apply in_app_iff; left; left; reflexivity)) as [C'|C']; cbn in C'; rewrite ?Ecap in C'; clear - C' Ecap; lia.
    + exact Cpx.
    + eapply big_at_agree1. 4:{ eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KU; unfold Q in Hi; clear - Hi; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
      intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
    + destruct XA as [OXA NEGA]. split. 2: exact NEGA. eapply big_at_agree1. 4:{ eapply big_at_agree1. 4: exact OXA. intros i Hi; apply KU; unfold X in Hi; clear - Hi; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia. }
      intros i Hi; apply KA; unfold X, spd in *; clear - Hi SLO SHI; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
    + eapply (cdef_above M1 M2 _ spd L5NORMU.NORM_SCR _ X 32 HP2). unfold spd; fsclia. uSCR; clear; lia. exact (proj1 SPT). unfold X, spd; clear; lia. unfold X; clear - SHI; lia.
      eapply L5.defined_grows. exact MG1. exact DX.
    + exact ONUM. + exact LNUM.
    + subst fn. destruct gn; rewrite ?Z.lor_spec, FN1; reflexivity.
    + intros cap p E. destruct gn as [|A cap']. { destruct NSH as [[u0 [u1 Es]] _]. rewrite Es in E. discriminate E. } destruct NSH as (Es & _). rewrite Es in E. injection E. intros <- <-. split; reflexivity.
    + intros u0 u1 E. rewrite E in NCAP. exact NCAP.
    + exact ODEN. + exact LDEN.
    + intros cap p E. destruct gd as [|A cap']. { destruct DSH as [[u0 [u1 Es]] _]. rewrite Es in E. discriminate E. } destruct DSH as (Es & _). rewrite Es in E. injection E. intros <- <-. split; reflexivity.
    + intros u0 u1 E. rewrite E in DCAP. exact DCAP.
    + intros T. destruct gd as [|A cap]. 2:{ destruct DSH as (_ & _ & F & _). rewrite F in T. discriminate T. } destruct DSH as [[u0 [u1 Es]] _]. rewrite Es in DCAP.
      destruct NB12 as [E1|E2]. exact E1. exfalso. pose proof (proj2 LRD E2) as L3. clear - DCAP L3. lia.
    + intros T. destruct gd as [|A cap]. { destruct DSH as [_ F]. rewrite F in T. discriminate T. } destruct V2d as [L3|SE]. 2: exact (proj1 (SECF SE)).
      destruct (L5OM1V.D_facts nb b0 b1 wb NB12 WB Rb0 Rb1 TOPNZ V1 V2) as [(E1 & _ & _ & LD & _)|[(E2 & _)|(E2 & _)]]. exfalso; clear - L3 LD; lia. exact E2. exact E2.
    + intros SE. destruct (SECF SE) as (_ & _ & _ & LD3 & LN3). split.
      * destruct gn as [|A cap]. 2: destruct NSH as (_ & _ & T & _); exact T. destruct NSH as [[u0 [u1 Es]] _]. rewrite Es in NCAP. exfalso. clear - NCAP LN3. lia.
      * destruct gd as [|A cap]. 2: destruct DSH as (_ & _ & T & _); exact T. destruct DSH as [[u0 [u1 Es]] _]. rewrite Es in DCAP. exfalso. clear - DCAP LD3. lia.
    + eapply big_at_agree1. 4:{ eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KU; subst bo; clear - Hi; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia. }
      intros i Hi; apply KA; subst bo; unfold spd; clear - Hi SLO SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
    + eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M1 M2 spd L5NORMU.NORM_SCR _). exact HP1. exact HP2.
      * intros a KA'. pose proof (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' LBceil CEILS ltac:(rewrite IMG'; clear - SPT; lia)) as NS'.
        eapply L5HP.kept_mono. exact KA'. intros b Hb; exact Hb. unfold spd; rewrite SCR_OPMOD_val; uSCR; clear; lia. unfold spd; clear; lia.
        intros _. unfold L5NORMU.norm_W, L5NORMU.dyn_area. cbn [L5.bo_st app]. rewrite SCR_OPMOD_val in NS'. apply outside3; clear - NS'; lia.
      * intros b Hb; exact Hb. * exact CEILS. * clear - SHI; lia. * rewrite SCR_OPMOD_val; clear; lia. * rewrite EV; clear; lia. * exact (proj1 SPT).
Qed.



Lemma COPY_SCR_val : COPY_SCR = 8304. Proof. reflexivity. Qed.
Lemma copy_fb_bit0 fbo fb : Z.testbit (copy_fb fbo fb false) 0 = false.
Proof. unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec. replace (Z.testbit 252 0) with false by reflexivity. replace (Z.testbit 2 0) with false by reflexivity. cbn. rewrite !Bool.andb_false_r. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G2 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (fn0 : Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 22) = Z_to_bv 64 (Q - 120) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  top_frame M S R0 -> o1_saves M S R0 ->
  local_obj M (S - 280) fn0 0 0 -> Z.testbit fn0 0 = false ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (S - 248) (L5.BO fnum 2 (L5.BInl A0 A1)) -> Z.testbit fnum 1 = false ->
  L5.big_at RSEGS M (S - 200) (L5.BO fden nb (L5.BInl b0 b1)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x227a8 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H22 H23 H25 H26 MBV HH SCR IC TF SAV LO1 F1b ZQ XA DX ON FN1 OD FD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  pose proof OD as (Db0 & Df & D8 & DT & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Db0, Df, D8, DT.
  (* [comment removed for export] *)
  pose proof (d5ug2_conc fx R M (fun j => match j with 2%nat => Q | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) ltac:(unfold Q; clear - SLO SHI; lia) AQ16)
    as (fx1 & R1 & M1 & MG1 & FR1 & _ & (MS1 & K1 & Ara & A10 & A11 & A12)). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  destruct (L5OPMOD1HU.defined_byte M (S - 344) ltac:(eapply L5.defined_sub; [exact SCR' | clear; lia | clear; lia]) ltac:(clear - SLO; lia) ltac:(clear - SHI; lia)) as (fbo & Fbo & Ubo).
  eapply (COPYA fx1 R1 M model K LB cr (S - 344) (S - 200) spd 0x227b8 fbo (L5.BO fden nb (L5.BInl b0 b1)) wb HH MOK HK0
            ltac:(etransitivity; [exact A10 | unfold Q; f_equal; clear; lia]) ltac:(etransitivity; [exact A11 | unfold Q; f_equal; clear; lia])).
  - intros T. exfalso. change (Z.testbit fden 0 = true) in T. rewrite DT in T. discriminate T.
  - exact Ara.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; clear - SHI'; lia. split. exact SPT. unfold spd. rewrite COPY_SCR_val. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia.
  - exact Ubo. - exact Fbo.
  - replace (S - 344) with (S + 8 * (-43)) by (clear; lia). apply al8. exact A16.
  - unfold spd; clear; lia. - clear - SHI'; lia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia. clear - SLO; lia. clear - SHI; lia.
  - exact OD.
  - pose proof (OLB_any M) as (Ln & Wok & Wst). rewrite STB in Wst. split. exact Ln. split. exact Wok. exact Wst.
  - replace (S - 200) with (S + 8 * (-25)) by (clear; lia). apply al8. exact A16.
  - unfold spd; clear; lia. - clear - SHI'; lia.
  - intros cap q E. discriminate E.
  - left. clear; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP2 & GP). destruct g as [|A cap]. 2:{ exfalso. destruct GP as (DYT & _). change (Z.testbit fden 0 = true) in DYT. rewrite DT in DYT. discriminate DYT. }
    destruct GP as (_ & -> & -> & OD0 & FB2 & MG2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OD0.
    assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (S - 344 <= a < S - 312) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn. apply FB2. apply outside1. rewrite BG.unsigned_lit by exact Ha. clear - Hn; lia. }
    assert (KU: forall i, S - 312 <= i < S + 200 -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KA; clear - Hi SLO SHI; lia. }
    assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
    assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
    assert (E2r: forall i v, In i cs_all -> getr R (reg i) = v -> In i KS_d5ug2 -> getr R2 (reg i) = v).
    { intros i v Hi Hv Hk. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. rewrite (K1 i Hk). exact Hv. }
    apply (stage_G3 fx2 R2 M2 model2 fn0 (copy_fb fbo fden false)).
    all: try (eapply E2r; [inl | eassumption | inl]).
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
    + exact HH2.
    + eapply L5.defined_grows. exact MG2. exact SCR.
    + intros i Hi. rewrite KA. apply IC; exact Hi. clear - Hi; lia. clear - Hi SLO; lia.
    + eapply top_frame_kept. 4: exact TF. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + eapply o1_saves_kept. 4: exact SAV. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + pose proof OD0 as (U0 & Uf & _). split. exact U0. split. exact Uf. intros T. exfalso. rewrite copy_fb_bit0 in T. discriminate T.
    + apply copy_fb_bit0.
    + eapply local_obj_kept. 4: exact LO1. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + exact F1b.
    + eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KU; unfold Q in Hi; clear - Hi; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
    + destruct XA as [OXA NEGA]. split. 2: exact NEGA. eapply big_at_agree1. 4: exact OXA. intros i Hi; apply KU; unfold X in Hi; clear - Hi; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
    + eapply L5.defined_grows. exact MG2. exact DX.
    + eapply big_at_agree1. 4: exact ON. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + exact FN1.
    + eapply big_at_agree1. 4: exact OD. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + exact FD1.
    + eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KU; subst bo; clear - Hi; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
    + eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M2 S SCR_OPMOD [(X, 32)]). exact HP.
      * eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M2 (fun a => S - 344 <= a < S - 312)). exact KA.
        { intros a KA' C'. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' LBceil CEILS _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. clear - C'; lia. }
        rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG2. exact SCR'. exact MG2.
      * intros a KA'; exact KA'. * intros b Hb; exact Hb. * exact CEILS. * clear - SHI; lia. * rewrite SCR_OPMOD_val; clear; lia. * rewrite EV; clear; lia. * exact (proj1 SPT).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G1 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 22) = Z_to_bv 64 (Q - 120) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  top_frame M S R0 -> o1_saves M S R0 ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (S - 248) (L5.BO fnum 2 (L5.BInl A0 A1)) -> Z.testbit fnum 1 = false ->
  L5.big_at RSEGS M (S - 200) (L5.BO fden nb (L5.BInl b0 b1)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R GEN M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H22 H23 H25 H26 MBV HH SCR IC TF SAV ZQ XA DX ON FN1 OD FD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  pose proof ON as (Nb0 & Nf & N8 & NT & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nf, N8, NT.
  (* [comment removed for export] *)
  pose proof (d5ug1_conc fx R M (fun j => match j with 2%nat => Q | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) ltac:(unfold Q; clear - SLO SHI; lia) AQ16)
    as (fx1 & R1 & M1 & MG1 & FR1 & _ & (MS1 & K1 & Ara & A10 & A11 & A12)). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  unfold cfg, GEN. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  destruct (L5OPMOD1HU.defined_byte M (S - 280) ltac:(eapply L5.defined_sub; [exact SCR' | clear; lia | clear; lia]) ltac:(clear - SLO; lia) ltac:(clear - SHI; lia)) as (fbo & Fbo & Ubo).
  eapply (COPYA fx1 R1 M model K LB cr (S - 280) (S - 248) spd 0x227a8 fbo (L5.BO fnum 2 (L5.BInl A0 A1)) [A0; A1] HH MOK HK0
            ltac:(etransitivity; [exact A10 | unfold Q; f_equal; clear; lia]) ltac:(etransitivity; [exact A11 | unfold Q; f_equal; clear; lia])).
  - intros T. exfalso. change (Z.testbit fnum 0 = true) in T. rewrite NT in T. discriminate T.
  - exact Ara.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; clear - SHI'; lia. split. exact SPT. unfold spd. rewrite COPY_SCR_val. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia.
  - exact Ubo. - exact Fbo.
  - replace (S - 280) with (S + 8 * (-35)) by (clear; lia). apply al8. exact A16.
  - unfold spd; clear; lia. - clear - SHI'; lia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia. clear - SLO; lia. clear - SHI; lia.
  - exact ON.
  - apply obj_limbs_x.
  - replace (S - 248) with (S + 8 * (-31)) by (clear; lia). apply al8. exact A16.
  - unfold spd; clear; lia. - clear - SHI'; lia.
  - intros cap q E. discriminate E.
  - left. clear; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP2 & GP). destruct g as [|A cap]. 2:{ exfalso. destruct GP as (DYT & _). change (Z.testbit fnum 0 = true) in DYT. rewrite NT in DYT. discriminate DYT. }
    destruct GP as (_ & -> & -> & ON0 & FB2 & MG2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in ON0.
    assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (S - 280 <= a < S - 248) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn. apply FB2. apply outside1. rewrite BG.unsigned_lit by exact Ha. clear - Hn; lia. }
    assert (KU: forall i, S - 248 <= i < S + 200 -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KA; clear - Hi SLO SHI; lia. }
    assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
    assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
    assert (E2r: forall i v, In i cs_all -> getr R (reg i) = v -> In i KS_d5ug1 -> getr R2 (reg i) = v).
    { intros i v Hi Hv Hk. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. rewrite (K1 i Hk). exact Hv. }
    apply (stage_G2 fx2 R2 M2 model2 (copy_fb fbo fnum false)).
    all: try (eapply E2r; [inl | eassumption | inl]).
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
    + exact HH2.
    + eapply L5.defined_grows. exact MG2. exact SCR.
    + intros i Hi. rewrite KA. apply IC; exact Hi. clear - Hi; lia. clear - Hi SLO; lia.
    + eapply top_frame_kept. 4: exact TF. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + eapply o1_saves_kept. 4: exact SAV. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + pose proof ON0 as (U0 & Uf & _). split. exact U0. split. exact Uf. intros T. exfalso. rewrite copy_fb_bit0 in T. discriminate T.
    + apply copy_fb_bit0.
    + eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KU; unfold Q in Hi; clear - Hi; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
    + destruct XA as [OXA NEGA]. split. 2: exact NEGA. eapply big_at_agree1. 4: exact OXA. intros i Hi; apply KU; unfold X in Hi; clear - Hi; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
    + eapply L5.defined_grows. exact MG2. exact DX.
    + eapply big_at_agree1. 4: exact ON. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + exact FN1.
    + eapply big_at_agree1. 4: exact OD. intros i Hi; apply KU; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
    + exact FD1.
    + eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KU; subst bo; clear - Hi; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
    + eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M2 S SCR_OPMOD [(X, 32)]). exact HP.
      * eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M2 (fun a => S - 280 <= a < S - 248)). exact KA.
        { intros a KA' C'. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' LBceil CEILS _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. clear - C'; lia. }
        rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG2. exact SCR'. exact MG2.
      * intros a KA'; exact KA'. * intros b Hb; exact Hb. * exact CEILS. * clear - SHI; lia. * rewrite SCR_OPMOD_val; clear; lia. * rewrite EV; clear; lia. * exact (proj1 SPT).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem o1_gen (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) :
  o1_gen_entry L HI LB cr S R0 M0 model0 fbx bo bb wb R M model fnum fden b0 b1 ->
  srealizes RSEGS SCFG (cfg R GEN M model) K.
Proof.
  intros GE. destruct GE as (H2 & H3 & H4 & H8 & H9 & H18 & H22 & H23 & H25 & H26 & HH & MBV & SCR & HP & IC & TF & SAV & ZQ & XA & DX
                        & ON & FN1 & _ & _ & OD & FD1 & _ & _ & _ & _ & _ & _ & OBB & OLB & _ & _).
  apply (stage_G1 fx R M model); try assumption.
  - replace (S - 248) with (S - 64 - 184) by (clear; lia). exact ON.
  - replace (S - 200) with (S - 64 - 136) by (clear; lia). exact OD.
  - eapply hpres_wmono. 2: exact HP. intros a _. apply L5C.outside_nil.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5OPMOD1GCU.
