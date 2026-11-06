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
 L5ShlU L5MulMU L5Norm L5NormU L5CmpU L5CoreKit L5DivSpecsU L5DivPartsU L5DivNPU L5DivOPU L5DivO2PU L5DivEarlyU L5OpMod1SU L5OpMod1HU L5OpMod1V L5OpMod1GU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigFactsBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5OPMOD1GBU.
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
Let mid_kept := @L5OPMOD1GU.mid_kept L R0 M0 LB S bb wb b0 STK HS NB12 V1 V2.
Let stage_G7 := @L5OPMOD1GU.stage_G7 _ L HI LY HIok KPOS BPOS RESIZE DIVLOOP R0 M0 model0 K LB cr S bo bb wb b0 b1 MOK0 HK0 BO STK HS BOK CR STB NB12 V1 V2 KT.



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
Lemma stage_G6 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (j : Z)
      (fq : Z) (nqo : nat) (q0 q1 : Z) (fn cn pn : Z) (stn : L5.bstore) (fd cd pd fn0 fd0 denomd : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l1) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat n1) ->
  getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  L5.u64_at RSEGS M (Q - 152) denomd -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat l1) -> L5.u64_at RSEGS M (Q - 232) (Q + 16) -> L5.u64_at RSEGS M (Q - 224) (Z.of_nat nqo) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - j * hl_k_per_malloc L <= fst crc -> snd cr - j * (64 + hl_b_overhead L) <= snd crc -> 0 <= j <= 2 ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  mid M fn cn pn fd cd pd fn0 fd0 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Q (L5.BO fq nqo (L5.BInl q0 q1)) -> (nqo + l + 1 = n1)%nat ->
  (* [comment removed for export] *)
  x_is_a M X fbx -> L5.defined M X 32 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M (S - 248) (L5.BO fn n1 stn) -> L5C.obj_limbs RSEGS M (L5.BO fn (length rwn) stn) rwn -> Z.testbit fn 1 = false ->
  (forall cap p, stn = L5.BDyn cap p -> cap = cn /\ p = pn) -> (forall u0 u1, stn = L5.BInl u0 u1 -> (length rwn <= 2)%nat) ->
  (* [comment removed for export] *)
  denomd = (if Z.testbit fd 0 then pd else S - 184) -> (Z.testbit fd 0 = false -> nb = 1%nat) -> (Z.testbit fd 0 = true -> nb = 2%nat) ->
  L5.defined M denomd (8 * Z.of_nat l1) -> L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d ->
  (sec = true -> Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22848 M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H18 H21 H23 H24 H25 H26 VD VS VQ VQS MBV HH CRK CRB Hj SCR IC MD OQ NQ XA DX ON LN FN1 NST NINL Edd DN1 DN2 DDEF Cd SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF' as (L13 & N24 & LN' & NL2 & _ & _ & NLR & LR4 & DR & SECF & SECF' & _). pose proof ERRNOV as EV. pose proof IMG as IMG'.
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia).
  pose proof MD as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C408).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AX8: X mod 8 = 0). { unfold X. replace (S + 64) with (S + 8 * 8) by (clear; lia). apply al8. exact A16. }
  pose proof XA as [OXA NEGA].
  assert (DNB: 4096 <= denomd /\ denomd + 8 * Z.of_nat l + 8 <= 2 ^ 47 /\ (Z.testbit fd 0 = true -> denomd + 64 <= hl_ceil L)).
  { rewrite Edd. destruct (Z.testbit fd 0) eqn:Tfd.
    - destruct (FR3 eq_refl) as [_ FBd]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & P2 & P3 & _ & P5). split. clear - P1; lia. split. clear - P5 Hl SPT; lia. intros _; exact P5.
    - split. clear - SLO; lia. split. clear - SHI Hl; lia. intros F; discriminate F. }
  destruct DNB as (DNlo' & DNhi & DNC). assert (DNlo: 4096 <= denomd + 8 * Z.of_nat l) by (clear - DNlo'; lia).
  (* [comment removed for export] *)
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  pose proof (d5ug6_conc fx R M (fun j => match j with 2%nat => Q | 36%nat => X | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold X; clear - SLO SHI; lia) ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H8
              ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold aligned; exact AQ16))
    as (fx1 & R1 & M1 & MG1 & FR1 & _ & (MS1 & K1 & Ara & A10 & A11)). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  assert (LBcI: forall b, In b LB -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb. }
  assert (INn: Z.testbit fn 0 = true -> In (pn, 64) LBc).
  { intros T. destruct (FR2 T) as [Ec _]. subst LBc BN. rewrite T, Ec. apply in_app_iff. left. left. reflexivity. }
  assert (INd: Z.testbit fd 0 = true -> In (pd, 64) LBc).
  { intros T. destruct (FR3 T) as [Ec _]. subst LBc BD. rewrite T, Ec. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
  pose proof ON as (Nb0 & Nf & N8 & NS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nf, N8, NS.
  pose proof LN as (RL & ROK & RST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in RL, RST.
  assert (OLN1: L5C.obj_limbs RSEGS M (L5.BO fn n1 stn) (firstn n1 rwn)).
  { split. { cbn [L5.bo_len]. rewrite length_firstn. clear - NLR; lia. } split. { apply (L5OM1V.words_ok_firstn' n1 rwn ROK). }
    cbn [L5.bo_st L5.bo_len]. destruct stn as [u0 u1|cap p]. { transitivity (firstn n1 (firstn (length rwn) [u0; u1])). f_equal. exact RST. apply L5C.firstn_firstn_le. exact NLR. }
    apply L5C.limbs_at_firstn. exact RST. }
  pose proof OXA as OXA'. unfold L5.big_at in OXA'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OXA'. destruct OXA' as (Xb0 & Xf & X8 & XT & _).
  eapply (ASSIGN fx1 R1 M model K LBc crc X (S - 248) spd 0x22854 (L5.BO fbx 2 (L5.BInl A0 A1)) (L5.BO fn n1 stn) (firstn n1 rwn) HH MOK HK0 A10
            ltac:(etransitivity; [exact A11 | unfold Q; f_equal; clear; lia])).
  - cbn [L5.bo_len]. clear - N24; lia.
  - intros T. exfalso. change (Z.testbit fbx 0 = true) in T. rewrite XT in T. discriminate T.
  - cbn [L5.bo_len]. intros N3 _. replace (round_up (Z.of_nat n1)) with 8 by (unfold round_up; clear - N24 N3; destruct n1 as [|[|[|[|[|]]]]]; cbn; lia). apply (credit_next crc j CRK CRB). clear - Hj; lia.
  - exact Ara.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; clear - SHI'; lia. split. exact SPT. unfold spd. rewrite ASSIGN_SCR_val. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia.
  - exact OXA.
  - exact AX8.
  - unfold spd, X; clear; lia.
  - unfold X; clear - SHI'; lia.
  - apply (L5C.writable_of_defined RSEGS). exact DX. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
  - intros cap q E. discriminate E.
  - exact ON.
  - exact OLN1.
  - replace (S - 248) with (S + 8 * (-31)) by (clear; lia). apply al8. exact A16.
  - unfold spd; clear; lia.
  - clear - SHI'; lia.
  - intros cap q E. cbn in E. destruct (NST cap q E) as [-> ->]. rewrite E in NS. destruct NS as (NT & _). destruct (FR2 NT) as [Ec _]. rewrite Ec. apply INn. exact NT.
  - right. unfold X; clear; lia.
  - intros c0 q c' q' E. discriminate E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. destruct POST as (RP2 & R2_10 & GP). cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_data] in GP.
    assert (E2r: forall i v, In i cs_all -> getr R1 (reg i) = v -> getr R2 (reg i) = v). { intros i v Hi Hv. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. exact Hv. }
    assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
    assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
    assert (SUB2: forall b, In b LBc -> In b LB2). { intros b Hb. destruct g as [|A cap]. destruct GP as (_ & -> & _). exact Hb. destruct GP as (_ & _ & _ & -> & _). right. exact Hb. }
    assert (LBceil0: forall b, In b LB -> fst b + snd b <= hl_ceil L). { intros b Hb. apply LBceil. apply LBcI. exact Hb. }
    (* [comment removed for export] *)
    assert (COMMON: forall W, L5C.hpres L LBc spd ASSIGN_SCR W M M2 -> (forall a, ~ (X <= a < X + 32) -> L5.outside W a) ->
              (forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
              /\ L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M2 /\ L5.defined M2 (S - SCR_OPMOD) SCR_OPMOD /\ L5.img_clear M2 0x10000 0x20000
              /\ mid M2 fn cn pn fd cd pd fn0 fd0 /\ (L5.defined M2 denomd (8 * Z.of_nat l1) /\ L5.u64_at RSEGS M2 (denomd + 8 * Z.of_nat l) d)
              /\ L5.big_at RSEGS M2 Q (L5.BO fq nqo (L5.BInl q0 q1)) /\ L5.big_at RSEGS M2 bo bb /\ L5.defined M2 X 32
              /\ (L5.u64_at RSEGS M2 (Q - 152) denomd /\ L5.u64_at RSEGS M2 (Q - 144) (Z.of_nat l1) /\ L5.u64_at RSEGS M2 (Q - 232) (Q + 16) /\ L5.u64_at RSEGS M2 (Q - 224) (Z.of_nat nqo))).
    { intros W HPW HWo.
      assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hn. apply (kept_above M M2 LBc spd ASSIGN_SCR W a HPW). unfold spd; fsclia. rewrite ASSIGN_SCR_val; clear; lia. exact (proj1 SPT). exact Ha. apply HWo. exact Hn. }
      assert (HW2: forall a, L5C.kept L LB S SCR_OPMOD [(X, 32)] a -> L5.outside W a).
      { intros a KA'. apply HWo. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA') as OW. apply (L5HP.outside_in _ _ X 32 OW). left; reflexivity. }
      split. exact KA. split.
      - eapply (L5HP.hpres_trans L LB LBc S SCR_OPMOD [(X, 32)] M0 M M2 spd ASSIGN_SCR W). exact HP. exact HPW.
        + intros a KA'. eapply L5HP.kept_mono. exact KA'. exact LBcI. unfold spd; rewrite SCR_OPMOD_val, ASSIGN_SCR_val; clear; lia. unfold spd; clear; lia.
          intros _. apply HW2. exact KA'.
        + exact LBcI. + exact CEILS. + clear - SHI; lia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + exact (proj1 SPT).
      - split. { rewrite SCR_OPMOD_val. eapply SCR_kept. exact HPW. rewrite ASSIGN_SCR_val; clear; lia. exact SCR'. }
        split. { eapply IC_kept. exact HPW. 2: exact IC. intros a Ha. apply HWo. unfold X; clear - Ha SLO; lia. }
        split. { eapply mid_kept. 4: exact MD.
          + intros i Hi. apply KA. unfold spd; clear - Hi SLO SHI; lia. unfold X; clear - Hi; lia.
          + intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pn 64). apply SUB2. apply INn. exact T.
          + intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pd 64). apply SUB2. apply INd. exact T. }
        assert (KD: forall i, denomd <= i < denomd + 8 * Z.of_nat l1 -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
        { intros i Hi. rewrite Edd in Hi. destruct (Z.testbit fd 0) eqn:Tfd.
          { pose proof (LBceil (pd, 64) (INd eq_refl)) as PC. cbn in PC.
            apply (kept_inblock M M2 LBc crc _ spd ASSIGN_SCR _ pd 64 i HH HPW). apply INd; reflexivity. clear - Hi L13; lia. exact SPT. apply HWo. unfold X; clear - Hi PC SLO' L13; lia. }
          apply KA. unfold spd; clear - Hi SLO SHI L13; lia. unfold X; clear - Hi L13 SLO; lia. }
        split. { split. { eapply defined_agree1. 2: exact DDEF. intros i Hi; apply KD; exact Hi. }
                 eapply u64_at_agree1. 4: exact Cd. intros i Hi; apply KD; subst l; clear - Hi L13; lia. clear - DNlo; lia. clear - DNhi; lia. }
        split. { eapply big_at_agree1. 4: exact OQ. intros i Hi. apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
        split. { eapply big_at_agree1. 4: exact OBB. intros i Hi. apply KA; subst bo; unfold X, spd in *; clear - Hi SLO SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia. }
        split. { eapply (cdef_above M M2 _ spd ASSIGN_SCR _ X 32 HPW). unfold spd; fsclia. rewrite ASSIGN_SCR_val; clear; lia. exact (proj1 SPT). unfold X, spd; clear; lia. unfold X; clear - SHI; lia. exact DX. }
        repeat split; (eapply u64_at_agree1; [ | | | eassumption]; [intros i Hi; apply KA; unfold Q, X, spd in *; clear - Hi SLO SHI; lia | unfold Q; clear - SLO; lia | unfold Q; clear - SHI; lia]). }
    assert (G7r: forall i v, In i cs_all -> getr R (reg i) = v -> In i KS_d5ug6 -> getr R2 (reg i) = v).
    { intros i v Hi Hv Hk. apply (E2r i v Hi). rewrite (K1 i Hk). exact Hv. }
    assert (NEG2: forall gr, Z.testbit (assign_fb fbx fn n1 gr) 1 = false).
    { intros gr. unfold assign_fb. replace (n1 =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; clear - N24; lia).
      rewrite Z.lor_spec, !Z.land_spec, FN1. replace (Z.testbit 253 1) with false by reflexivity. rewrite !Bool.andb_false_r. reflexivity. }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct GP as (DYS & -> & -> & (st' & OX2 & OL2 & SST) & HP2).
      assert (N2: (n1 <= 2)%nat). { destruct DYS as [T|T]. exfalso. change (Z.testbit fbx 0 = true) in T. rewrite XT in T. discriminate T. exact T. }
      destruct st' as [v0 v1|cq' p']. 2: destruct SST.
      destruct (COMMON _ HP2) as (KA & HP2' & SCR2 & IC2 & MD2 & [DDEF2 Cd2] & OQ2 & OBB2 & DX2 & (VD2 & VS2 & VQ2 & VQS2)).
      { intros a NX r [<-|[<-|[]]]; unfold L5.in_rng; cbn. exact NX. unfold X in NX |- *. clear - NX N2 N24. lia. }
      apply (stage_G7 fx2 R2 M2 model2 crc j fq nqo q0 q1 (assign_fb fbx fn n1 false) (L5.BInl v0 v1) (firstn n1 rwn) fn cn pn fd cd pd fn0 fd0 denomd).
      all: try (eapply G7r; [inl | eassumption | inl]).
      all: try assumption.
      all: first [ exact (L5C.model_but_vm_trans _ _ _ MBV MBV2)
                 | apply NEG2
                 | solve [cbv iota; clear - Hj N2; lia]
                 | solve [intros cx p E; discriminate E]
                 | exact DDEF2 | exact Cd2 ].
    + (* [comment removed for export] *)
      destruct GP as (DYF & N3 & Ecap & -> & -> & FB & OX2 & OL2 & HP2).
      replace (round_up (Z.of_nat n1)) with 8 in Ecap by (unfold round_up; clear - N24 N3; destruct n1 as [|[|[|[|[|]]]]]; cbn; lia). subst cap.
      destruct (COMMON _ HP2) as (KA & HP2' & SCR2 & IC2 & MD2 & [DDEF2 Cd2] & OQ2 & OBB2 & DX2 & (VD2 & VS2 & VQ2 & VQS2)). { intros a NX. apply outside1. exact NX. }
      pose proof (credit_step crc j CRK CRB) as [CRK' CRB'].
      apply (stage_G7 fx2 R2 M2 model2 (debit L crc (8 * 8)) (j + 1) fq nqo q0 q1 (assign_fb fbx fn n1 true) (L5.BDyn 8 A) (firstn n1 rwn) fn cn pn fd cd pd fn0 fd0 denomd).
      all: try (eapply G7r; [inl | eassumption | inl]).
      all: try assumption.
      all: first [ exact (L5C.model_but_vm_trans _ _ _ MBV MBV2)
                 | apply NEG2
                 | exact I
                 | solve [cbn [blocks_ofst app]; exact HH2]
                 | solve [cbv iota; clear - Hj; lia]
                 | solve [intros cx p E; injection E; intros <- <-; split; [reflexivity | subst LBc; exact FB]]
                 | exact DDEF2 | exact Cd2 ].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zkept : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%nat.
Lemma zfill (j : nat) : forall fx R M (nq : nat),
  (j < nq)%nat -> (nq <= 2)%nat ->
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 19) = Z_to_bv 64 18446744073709551615 -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat j) ->
  L5.writable RSEGS M (Q - 352) 352 -> L5.u64_at RSEGS M (Q - 232) (Q + 16) -> L5.u64_at RSEGS M (Q - 224) (Z.of_nat nq) -> L5.writable RSEGS M (Q + 16) 16 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x22830 M) (st fx' R' 0x22848 M')
    /\ (forall x, In x zkept -> getr R' (reg x) = getr R (reg x))
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (Q + 16 <= i < Q + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.
Proof.
  induction j as [|j IH]; intros fx R M nq Hj Hnq H2 H19 H22 WFR VQ VQS WQ; pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT);
    (assert (AQ16: Q mod 16 = 0) by (unfold Q; replace (S - 64) with (S + (-4) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16));
    (assert (AQ8: (Q + 16) mod 8 = 0) by (unfold Q; replace (S - 64 + 16) with (S + 8 * (-6)) by (clear; lia); apply al8; exact A16)).
  - assert (W8: L5.writable RSEGS M (Q + 16 + 8 * 0) 8). { intros dd k Hd Hk. replace (Q + 16 + 8 * 0 + dd) with (Q + 16 + dd) by (clear; lia). apply WQ. exact Hd. clear - Hd Hk; lia. }
    pose proof (d7uzl_conc fx R M (fun k => match k with 2%nat => Q | 68%nat => Q + 16 | 70%nat => Z.of_nat nq | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold Q; clear - SLO SHI; lia) ltac:(clear - Hnq; lia) ltac:(clear; lia) ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H19
                ltac:(rewrite H22; f_equal; clear; lia) ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold aligned; exact AQ16) WFR VQ VQS ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold aligned; exact AQ8)
                W8 ltac:(left; unfold Q; clear; lia) ltac:(clear; lia) ltac:(clear - Hnq; lia))
      as (fx1 & R1 & M1 & MG & FR & FRZ & [(MS & KS & _ & _ & _ & _ & _ & _ & _ & Hj1 & _)|(MS & KS & _ & _ & _ & _ & _ & _ & _ & _ & _)]). clear P.
    { exfalso. clear - Hj1. lia. }
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
    split. { intros i Hi Ni. apply FRZ. exact Hi. clear - Ni; lia. } exact MG.
  - assert (W8: L5.writable RSEGS M (Q + 16 + 8 * Z.of_nat (Datatypes.S j)) 8).
    { intros dd k Hd Hk. replace (Q + 16 + 8 * Z.of_nat (Datatypes.S j) + dd) with (Q + 16 + (8 * Z.of_nat (Datatypes.S j) + dd)) by (clear; lia). apply WQ. clear - Hd; lia. clear - Hd Hk Hj Hnq; lia. }
    pose proof (d7uzl_conc fx R M (fun k => match k with 2%nat => Q | 68%nat => Q + 16 | 70%nat => Z.of_nat nq | 75%nat => Z.of_nat (Datatypes.S j) | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold Q; clear - SLO SHI; lia) ltac:(clear - Hnq; lia) ltac:(clear - Hj Hnq; lia) ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H19
                H22 ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold aligned; exact AQ16) WFR VQ VQS ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold aligned; exact AQ8)
                W8 ltac:(left; unfold Q; clear; lia) ltac:(clear - Hj Hnq; lia) ltac:(clear - Hnq; lia))
      as (fx1 & R1 & M1 & MG & FR & FRZ & [(MS & KS & _ & _ & _ & _ & _ & _ & A22 & _ & _)|(MS & KS & _ & _ & _ & _ & _ & _ & _ & Hj0 & _)]). clear P.
    2:{ exfalso. clear - Hj0. lia. }
    assert (KF: forall i, 0 <= i < 2 ^ 64 -> ~ (Q + 16 <= i < Q + 32) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Ni. apply FRZ. exact Hi. clear - Ni Hj Hnq; lia. }
    destruct (IH fx1 R1 M1 nq ltac:(clear - Hj; lia) Hnq ltac:(rewrite (KS 2%nat) by inl; exact H2) ltac:(rewrite (KS 19%nat) by inl; exact H19)
                 ltac:(rewrite A22; f_equal; clear; lia) ltac:(eapply L5.writable_grows; [exact MG | exact WFR])
                 ltac:(eapply u64_at_agree1; [intros i Hi; apply KF; unfold Q in *; clear - Hi SLO SHI; lia | unfold Q; clear - SLO; lia | unfold Q; clear - SHI; lia | exact VQ])
                 ltac:(eapply u64_at_agree1; [intros i Hi; apply KF; unfold Q in *; clear - Hi SLO SHI; lia | unfold Q; clear - SLO; lia | unfold Q; clear - SHI; lia | exact VQS])
                 ltac:(eapply L5.writable_grows; [exact MG | exact WQ]))
      as (fx2 & R2 & M2 & MS2 & K2 & FR2 & MG2).
    exists fx2, R2, M2. split. eapply msteps_trans. exact MS. exact MS2.
    split. { intros x Hx. rewrite (K2 x Hx). apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
    split. { intros i Hi Ni. rewrite (FR2 i Hi Ni). apply KF. exact Hi. exact Ni. } eapply mem_grows_trans. exact MG. exact MG2.
Qed.

(* [comment removed for export] *)
Lemma stage_G5 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (j : Z)
      (fq : Z) (nqo : nat) (q0 q1 : Z) (fn cn pn : Z) (stn : L5.bstore) (fd cd pd fn0 fd0 denomd : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l1) -> getr R (reg 22) = Z_to_bv 64 denomd -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat n1) ->
  getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  L5.u64_at RSEGS M (Q - 152) denomd -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat l1) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - j * hl_k_per_malloc L <= fst crc -> snd cr - j * (64 + hl_b_overhead L) <= snd crc -> 0 <= j <= 2 ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  mid M fn cn pn fd cd pd fn0 fd0 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Q (L5.BO fq nqo (L5.BInl q0 q1)) -> (nqo + l + 1 = n1)%nat ->
  x_is_a M X fbx -> L5.defined M X 32 ->
  L5.big_at RSEGS M (S - 248) (L5.BO fn n1 stn) -> L5C.obj_limbs RSEGS M (L5.BO fn (length rwn) stn) rwn -> Z.testbit fn 1 = false ->
  (forall cap p, stn = L5.BDyn cap p -> cap = cn /\ p = pn) -> (forall u0 u1, stn = L5.BInl u0 u1 -> (length rwn <= 2)%nat) ->
  denomd = (if Z.testbit fd 0 then pd else S - 184) -> (Z.testbit fd 0 = false -> nb = 1%nat) -> (Z.testbit fd 0 = true -> nb = 2%nat) ->
  L5.defined M denomd (8 * Z.of_nat l1) -> L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d ->
  (sec = true -> Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22800 M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H18 H21 H22 H23 H24 H25 H26 VD VS MBV HH CRK CRB Hj SCR IC MD OQ NQ XA DX ON LN FN1 NST NINL Edd DN1 DN2 DDEF Cd SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF' as (L13 & N24 & LN' & NL2 & _ & _ & NLR & LR4 & DR & SECF & SECF' & _). pose proof ERRNOV as EV. pose proof IMG as IMG'.
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia). assert (Hq2: (nqo <= 2)%nat) by (subst l; clear - NQ NL2 L13; lia).
  pose proof MD as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C408).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (DNB: 4096 <= denomd /\ denomd + 8 * Z.of_nat l + 8 <= 2 ^ 47).
  { rewrite Edd. destruct (Z.testbit fd 0) eqn:Tfd.
    - destruct (FR3 eq_refl) as [_ FBd]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & P2 & P3 & _ & P5). split. clear - P1; lia. clear - P5 Hl SPT; lia.
    - split. clear - SLO; lia. clear - SHI Hl; lia. }
  destruct DNB as (DNlo' & DNhi).
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AQ8: Q mod 8 = 0). { apply mod16_mod8. exact AQ16. }
  assert (WFR: L5.writable RSEGS M (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI SLO; lia. }
  assert (WQ: L5.writable RSEGS M (Q + 16) 16).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI SLO; lia. }
  pose proof OQ as (Qb0 & Qf & Q8 & QT & Q16 & Q24 & _ & Rq0 & Rq1). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qb0, Qf, Q8, QT, Q16, Q24, Rq0, Rq1.
  (* [comment removed for export] *)
  pose proof (d7ug5i_conc fx R M (fun k => match k with 2%nat => Q | 35%nat => Q | 69%nat => fq | 70%nat => Z.of_nat nqo | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold Q; clear - SLO SHI; lia) ltac:(clear - Qf; lia) ltac:(clear - Hq2; lia)
              ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H9
              ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold aligned; exact AQ16) WFR ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold aligned; exact AQ8) ltac:(left; unfold Q; clear; lia)
              Qb0 ltac:(clear - Qf; lia) Q8 QT ltac:(clear - Hq2; lia))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & EX). clear P.
  assert (KF1: forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 232 <= i < Q - 216) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Ni. apply FR1. exact Hi. clear - Ni; lia. }
  (* [comment removed for export] *)
  assert (JOIN: exists fx2 R2 M2, msteps RSEGS (st fx R 0x22800 M) (st fx2 R2 0x22848 M2)
            /\ (forall x, In x [2; 3; 4; 8; 9; 18; 21; 23; 24; 25; 26]%nat -> getr R2 (reg x) = getr R (reg x))
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (Q + 16 <= i < Q + 32) -> ~ (Q - 232 <= i < Q - 216) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ mem_grows M M2 /\ L5.u64_at RSEGS M2 (Q - 232) (Q + 16) /\ L5.u64_at RSEGS M2 (Q - 224) (Z.of_nat nqo)).
  { destruct EX as [(MS & KS & A10 & A19 & A22 & NZ & VQS1 & VQ1)|(MS & KS & A10 & A22 & NZ & VQS1 & VQ1)].
    - destruct (zfill (nqo - 1) fx1 R1 M1 nqo ltac:(clear - NZ; lia) Hq2 ltac:(rewrite (KS 2%nat) by inl; exact H2) A19 ltac:(rewrite A22; f_equal; clear - NZ; lia)
                  ltac:(eapply L5.writable_grows; [exact MG1 | exact WFR]) VQ1 VQS1 ltac:(eapply L5.writable_grows; [exact MG1 | exact WQ]))
        as (fx2 & R2 & M2 & MS2 & K2 & FR2' & MG2).
      exists fx2, R2, M2. split. { eapply msteps_trans. exact MS. exact MS2. }
      split. { intros x Hx. rewrite (K2 x) by (revert x Hx; apply L5K.incl_b; vm_compute; reflexivity). apply KS. revert x Hx; apply L5K.incl_b; vm_compute; reflexivity. }
      split. { intros i Hi N1 N2. rewrite (FR2' i Hi N1). apply KF1. exact Hi. exact N2. }
      split. eapply mem_grows_trans. exact MG1. exact MG2.
      split. { eapply u64_at_agree1. 4: exact VQ1. intros i Hi. apply FR2'; unfold Q in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
      eapply u64_at_agree1. 4: exact VQS1. intros i Hi. apply FR2'; unfold Q in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
    - exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx; apply L5K.incl_b; vm_compute; reflexivity. }
      split. { intros i Hi N1 N2. apply KF1. exact Hi. exact N2. } split. exact MG1. split. exact VQ1. exact VQS1. }
  clear EX. destruct JOIN as (fx2 & R2 & M2 & MS2 & K2 & FR2' & MG2 & VQ2 & VQS2).
  assert (KQ: forall i, 0 <= i < 2 ^ 64 -> ~ (Q + 16 <= i < Q + 32) -> ~ (Q - 232 <= i < Q - 216) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) by exact FR2'.
  assert (SCR2: L5.defined M2 (S - 10240) 10240) by (eapply L5.defined_grows; [exact MG2 | exact SCR']).
  (* [comment removed for export] *)
  destruct (BDU.defined_word M2 (Q + 16) ltac:(eapply L5.defined_sub; [exact SCR2 | unfold Q; clear; lia | unfold Q; clear; lia]) ltac:(unfold Q; clear - SLO; lia) ltac:(unfold Q; clear - SHI; lia)) as (q0' & R0' & U0').
  destruct (BDU.defined_word M2 (Q + 24) ltac:(eapply L5.defined_sub; [exact SCR2 | unfold Q; clear; lia | unfold Q; clear; lia]) ltac:(unfold Q; clear - SLO; lia) ltac:(unfold Q; clear - SHI; lia)) as (q1' & R1' & U1').
  assert (OQ2: L5.big_at RSEGS M2 Q (L5.BO fq nqo (L5.BInl q0' q1'))).
  { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Qb0. intros i Hi; apply KQ; unfold Q in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
    split. exact Qf. split. { eapply u64_at_agree1. 4: exact Q8. intros i Hi; apply KQ; unfold Q in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
    split. exact QT. split. exact U0'. split. exact U1'. split. exact Hq2. split. exact R0'. exact R1'. }
  assert (LBcI: forall b, In b LB -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb. }
  assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
  assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (KF: forall i, S - 408 <= i < S - 296 \/ S - 280 <= i < S - 48 \/ S - 32 <= i < S + 160 -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KQ; unfold Q; clear - Hi SLO SHI; lia. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
  apply (stage_G6 fx2 R2 M2 model crc j fq nqo q0' q1' fn cn pn stn fd cd pd fn0 fd0 denomd).
  all: try (rewrite (K2 _) by inl; assumption).
  all: try assumption.
  - eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
  - eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
  - eapply (L5C.hi_heap_client L SCFG HI LBc crc M M2). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG'; clear; lia. exact (proj1 SPT). 2: exact MG2.
    intros a Ha. destruct (Z_le_gt_dec (Q + 16) a) as [C1|C1]; [destruct (Z_lt_le_dec a (Q + 32)) as [C2|C2]|]. { right; left. unfold Q in *; clear - C1 C2 SLO' SHI'; lia. }
    all: destruct (Z_le_gt_dec (Q - 232) a) as [C3|C3]; [destruct (Z_lt_le_dec a (Q - 216)) as [C4|C4]|].
    all: first [right; left; unfold Q in *; clear - C3 C4 SLO' SHI'; lia | left; apply KQ; [exact Ha | clear - C1 C2 || clear - C1; lia | clear - C3 C4 || clear - C3; lia]].
  - intros i Hi. rewrite KQ. apply IC; exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. unfold Q; clear - Hi SLO; lia.
  - eapply mid_kept. 4: exact MD. intros i Hi; apply KF; clear - Hi; lia. intros _ D'; eapply L5.defined_grows; [exact MG2 | exact D']. intros _ D'; eapply L5.defined_grows; [exact MG2 | exact D'].
  - destruct XA as [OXA NEGA]. split. 2: exact NEGA. eapply big_at_agree1. 4: exact OXA. intros i Hi; apply KF; unfold X in Hi; clear - Hi; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
  - eapply L5.defined_grows. exact MG2. exact DX.
  - eapply big_at_agree1. 4: exact ON. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - pose proof ON as (_ & _ & _ & NS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in NS. pose proof LN as (RL & _ & _). cbn [L5.bo_len] in RL.
    eapply obj_limbs_agree1. 3: exact LN. all: cbn [L5.bo_st L5.bo_len]; intros cap q E; destruct (NST cap q E) as [-> ->]; rewrite E in NS; destruct NS as (NT & _); destruct (FR2 NT) as [Ec FBn];
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBn) as (P1 & _ & _ & _ & P5).
    + intros i Hi. apply KQ. clear - Hi P1 P5 SPT LR4; lia. unfold Q; clear - Hi P5 SLO' LR4; lia. unfold Q; clear - Hi P5 SLO' LR4; lia.
    + clear - P1 P5 SPT LR4; lia.
  - eapply L5.defined_grows. exact MG2. exact DDEF.
  - eapply u64_at_agree1. 4: exact Cd. 2: clear - DNlo'; lia. 2: clear - DNhi; lia. intros i Hi. rewrite Edd in Hi. destruct (Z.testbit fd 0).
    + destruct (FR3 eq_refl) as [_ FBd]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & _ & _ & _ & P5). apply KQ. clear - Hi P1 P5 SPT Hl; lia. unfold Q; clear - Hi P5 SLO' Hl; lia. unfold Q; clear - Hi P5 SLO' Hl; lia.
    + apply KF. clear - Hi Hl; lia.
  - eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KF; subst bo; clear - Hi; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
  - eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M2 S SCR_OPMOD [(X, 32)]). exact HP.
    + eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M2 (fun a => Q + 16 <= a < Q + 32 \/ Q - 232 <= a < Q - 216)). { intros a Ha Hn. apply KQ. exact Ha. clear - Hn; lia. clear - Hn; lia. }
      { intros a KA' C. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' ltac:(intros b Hb; apply LBceil; apply LBcI; exact Hb) CEILS _ _). rewrite IMG'; clear - SPT; lia.
        rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia. }
      rewrite SCR_OPMOD_val. exact SCR2. exact MG2.
    + intros a KA'; exact KA'. + intros b Hb; exact Hb. + exact CEILS. + clear - SHI; lia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + exact (proj1 SPT).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G4 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (j : Z)
      (fn cn pn : Z) (stn : L5.bstore) (fd cd pd : Z) (std : L5.bstore) (fn0 fd0 : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 10) = Z_to_bv 64 sd -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 22) = Z_to_bv 64 (Q - 120) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - j * hl_k_per_malloc L <= fst crc -> snd cr - j * (64 + hl_b_overhead L) <= snd crc -> 0 <= j <= 2 ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  top_frame M S R0 -> o1_saves M S R0 ->
  local_obj M (S - 344) fd0 0 0 -> Z.testbit fd0 0 = false -> local_obj M (S - 280) fn0 0 0 -> Z.testbit fn0 0 = false ->
  local_obj M (S - 248) fn cn pn -> (Z.testbit fn 0 = true -> cn = 8 /\ L5C.fresh_block L LB M pn 64) ->
  local_obj M (S - 200) fd cd pd -> (Z.testbit fd 0 = true -> cd = 8 /\ L5C.fresh_block L (BN ++ LB) M pd 64) ->
  L5.u32_at RSEGS M (S - 348) c ->
  zero_obj M Q -> x_is_a M X fbx -> L5.defined M X 32 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M (S - 248) (L5.BO fn n1 stn) -> L5C.obj_limbs RSEGS M (L5.BO fn (length rwn) stn) rwn -> Z.testbit fn 1 = false ->
  (forall cap p, stn = L5.BDyn cap p -> cap = cn /\ p = pn) -> (forall u0 u1, stn = L5.BInl u0 u1 -> (length rwn <= 2)%nat) ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M (S - 200) (L5.BO fd l1 std) -> L5C.obj_limbs RSEGS M (L5.BO fd (length rwd) std) rwd ->
  (forall cap p, std = L5.BDyn cap p -> cap = cd /\ p = pd) -> (forall u0 u1, std = L5.BInl u0 u1 -> (length rwd <= 2)%nat) ->
  (Z.testbit fd 0 = false -> nb = 1%nat) -> (Z.testbit fd 0 = true -> nb = 2%nat) ->
  (sec = true -> Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x227d0 M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H10 H18 H22 H23 H25 H26 MBV HH CRK CRB Hj SCR IC TF SAV LO0 F0b LO1 F1b LO2 FR2 LO3 FR3 C348 ZQ XA DX
         ON LN FN1 NST NINL OD LD DST DINL DN1 DN2 SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF' as (L13 & N24 & LN' & NL2 & LLR & LR3 & NLR & LR4 & DR & SECF & SECF' & _). pose proof ERRNOV as EV. pose proof IMG as IMG'.
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AQ8: Q mod 8 = 0). { apply mod16_mod8. exact AQ16. }
  assert (WFR: L5.writable RSEGS M (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI SLO; lia. }
  assert (Hsd: 0 <= sd <= 1). { subst sd. destruct sec; clear; lia. }
  pose proof OD as (Db0 & Df & D8 & DS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Db0, Df, D8, DS.
  pose proof ON as (Nb0 & Nf & N8 & NS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nf, N8, NS.
  set (denomd := if Z.testbit fd 0 then pd else S - 184).
  (* [comment removed for export] *)
  assert (DEN: L5.defined M denomd (8 * Z.of_nat l1) /\ L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d /\ 4096 <= denomd /\ denomd + 8 * Z.of_nat l + 8 <= 2 ^ 47 /\
               match std with L5.BInl _ _ => Z.testbit fd 0 = false | L5.BDyn cap p => Z.testbit fd 0 = true /\ p = pd /\ L5.u64_at RSEGS M (S - 200 + 24) pd end).
  { subst denomd d l. pose proof LD as (RL & ROK & RST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in RL, RST. destruct std as [u0 u1|cap p].
    - destruct DS as (DT & U16 & U24 & Hle & Ru0 & Ru1). rewrite DT. pose proof (DINL u0 u1 eq_refl) as RL2.
      split. { eapply L5.defined_sub. exact SCR'. clear; lia. clear - Hle; lia. }
      split. { rewrite RST. destruct (l1) as [|[|[|k]]] eqn:EL. exfalso; clear - L13 EL; lia.
               - destruct rwd as [|w0 [|w1 [|w2 r]]]; cbn in RL2 |- *; try (exfalso; clear - RL2; lia); cbn; try exactA U16. exfalso. cbn in LLR. clear - LLR EL. lia.
               - destruct rwd as [|w0 [|w1 [|w2 r]]]; cbn in RL2 |- *; try (exfalso; clear - RL2; lia); cbn; try exactA U24. all: exfalso; cbn in LLR; clear - LLR EL; lia.
               - exfalso. clear - Hle EL. lia. }
      split. clear - SLO; lia. split. clear - SHI L13; lia. reflexivity.
    - destruct DS as (DT & U16 & U24 & _). rewrite DT. destruct (DST cap p eq_refl) as [-> ->]. destruct (FR3 DT) as [Ec FBd].
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & P2 & P3 & _ & P5). destruct FBd as (_ & _ & DFd).
      split. { eapply L5.defined_sub. exact DFd. clear; lia. clear - LR3 LLR; lia. }
      split. { unfold nth_w. replace (pd + 8 * Z.of_nat (rlen rwd - 1)) with (pd + 8 * Z.of_nat (rlen rwd - 1)%nat) by (clear; lia). apply RST. clear - L13 LLR; lia. }
      split. exact P1. split. clear - P5 SPT L13; lia. split. reflexivity. split. reflexivity. exact U24. }
  destruct DEN as (DDEF & Cd & DNlo' & DNhi & DW).
  (* [comment removed for export] *)
  assert (JOIN: exists fx1 R1 M1, msteps RSEGS (st fx R 0x227d0 M) (st fx1 R1 0x214e4 M1)
            /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
            /\ getr R1 (reg 1) = Z_to_bv 64 0x22800 /\ getr R1 (reg 10) = Z_to_bv 64 Q /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat n1 - Z.of_nat l1)
            /\ getr R1 (reg 21) = Z_to_bv 64 (Z.of_nat l1) /\ getr R1 (reg 22) = Z_to_bv 64 denomd /\ getr R1 (reg 24) = Z_to_bv 64 (Z.of_nat n1)
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 344 <= i < Q - 344 + 8) -> ~ (Q - 152 <= i < Q - 152 + 16) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M1
            /\ L5.u64_at RSEGS M1 (Q - 152) denomd /\ L5.u64_at RSEGS M1 (Q - 144) (Z.of_nat l1) /\ L5.u64_at RSEGS M1 (Q - 344) sd).
  { clear - H2 H3 H4 H8 H9 H10 H18 H22 H23 H25 H26 A16 SLO SHI SLO' SHI' SPT N24 L13 AQ16 AQ8 WFR Hsd Db0 Df D8 DS N8 DW.
    subst denomd. unfold X, Q, spd in *.
    destruct std as [u0 u1|cap p]; [rewrite DW | destruct DW as (DT & -> & U24); rewrite DT; destruct DS as (_ & _ & _ & _ & CAPR & _ & PLO & PHI & _)].
    - pose proof (d5ug4i_conc fx R M (fun j => match j with 2%nat => S - 64 | 35%nat => S - 64 | 41%nat => fd | 64%nat => sd | 65%nat => Z.of_nat n1 | 67%nat => Z.of_nat l1
                                                     | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & Ara & A10 & A11 & A21 & A24 & C0 & C1 & C2)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. exact Ara. split. exact A10. split. exact A11. split. exact A21. split. { rewrite (KS 22%nat) by inl. rewrite H22. cbv iota. f_equal. clear; lia. } split. exact A24.
      split. exact FRZ. split. exact MG. split. { cbv iota. replace (S - 184) with (S - 64 - 120) by (clear; lia). exact C1. } split. exact C0. exact C2.
    - pose proof (d6ug4d_conc fx R M (fun j => match j with 2%nat => S - 64 | 35%nat => S - 64 | 41%nat => fd | 64%nat => sd | 65%nat => Z.of_nat n1 | 66%nat => pd | 67%nat => Z.of_nat l1
                                                     | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & Ara & A10 & A11 & A21 & A22 & A24 & C0 & C1 & C2)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. exact Ara. split. exact A10. split. exact A11. split. exact A21. split. exact A22. split. exact A24.
      split. exact FRZ. split. exact MG. split. exact C1. split. exact C0. exact C2. }
  destruct JOIN as (fx1 & R1 & M1 & MS1 & K1 & Ara & A10 & A11 & A21 & A22 & A24 & FR1 & MG1 & VD1 & VS1 & C408).
  unfold Q in C408.
  assert (KF: forall i, 0 <= i < 2 ^ 64 -> ~ (S - 408 <= i < S - 400) -> ~ (S - 216 <= i < S - 200) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2. apply FR1. exact Hi. unfold Q; clear - N1; lia. unfold Q; clear - N2; lia. }
  assert (MD1: mid M1 fn cn pn fd cd pd fn0 fd0).
  { split. { eapply top_frame_kept. 4: exact TF. intros i Hi; apply KF; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia. }
    split. { eapply o1_saves_kept. 4: exact SAV. intros i Hi; apply KF; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia. }
    split. { eapply local_obj_kept. 4: exact LO0. intros i Hi; apply KF; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia. } split. exact F0b.
    split. { eapply local_obj_kept. 4: exact LO1. intros i Hi; apply KF; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia. } split. exact F1b.
    split. { eapply local_obj_kept. 4: exact LO2. intros i Hi; apply KF; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia. }
    split. { intros T. destruct (FR2 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'. }
    split. { eapply local_obj_kept. 4: exact LO3. intros i Hi; apply KF; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia. }
    split. { intros T. destruct (FR3 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'. }
    split. { eapply u32_at_agree1. 4: exact C348. intros i Hi; apply KF; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia. }
    exactA C408. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (hi_heap_stackwrite LBc crc M M1 _ (S - 408) (S - 200)). exact HH. { intros i Hi Hn. apply KF. exact Hi. clear - Hn; lia. clear - Hn; lia. }
    clear - SLO'; lia. clear - SHI'; lia. exact (proj1 SPT). exact MG1. }
  assert (LBcI: forall b, In b LB -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb. }
  assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
  assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (HP1: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M1).
  { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M1 S SCR_OPMOD [(X, 32)]). exact HP.
    - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M1 (fun a => S - 408 <= a < S - 200)). { intros a Ha Hn. apply KF. exact Ha. clear - Hn; lia. clear - Hn; lia. }
      { intros a KA' C. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' ltac:(intros b Hb; apply LBceil; apply LBcI; exact Hb) CEILS _ _). rewrite IMG'; clear - SPT; lia.
        rewrite SCR_OPMOD_val. clear - C; lia. }
      rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR'. exact MG1.
    - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEILS. - clear - SHI; lia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - exact (proj1 SPT). }
  assert (SCR1: L5.defined M1 (S - 10240) 10240) by (eapply L5.defined_grows; [exact MG1 | exact SCR']).
  assert (IC1: L5.img_clear M1 0x10000 0x20000). { intros i Hi. rewrite KF. apply IC; exact Hi. clear - Hi; lia. clear - Hi SLO; lia. clear - Hi SLO; lia. }
  assert (KU: forall i, S - 200 <= i < S + 200 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KF; clear - Hi SLO SHI; lia. }
  assert (KU2: forall i, S - 400 <= i < S - 216 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KF; clear - Hi SLO SHI; lia. }
  assert (ZQ1: zero_obj M1 Q). { eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply KU; unfold Q in Hi; clear - Hi; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
  pose proof MOK as MOK1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  replace (Z.of_nat n1 - Z.of_nat l1) with (Z.of_nat (n1 - l1)) in A11 by (clear - LN'; lia).
  eapply (RESIZE fx1 R1 M1 model K LBc crc Q spd 0x22800 (n1 - l1)%nat (L5.BO 0 0 (L5.BInl 0 0)) [] HH1 MOK1 HK0 A10 A11).
  - clear - NL2; lia.
  - intros T. exfalso. change (Z.testbit 0 0 = true) in T. discriminate T.
  - intros N3 _. exfalso. clear - N3 NL2. lia.
  - exact Ara.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; clear - SHI'; lia. split. exact SPT. unfold spd. rewrite RESIZE_SCR_val. eapply L5.defined_sub. exact SCR1. clear; lia. clear; lia.
  - exact ZQ1.
  - split. reflexivity. split. constructor. reflexivity.
  - exact AQ8.
  - unfold spd, Q; clear; lia.
  - unfold Q; clear - SHI'; lia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR1. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
  - intros cap q E. discriminate E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK1 MBV2) as MOK2. destruct POST as (RP2 & GP).
    assert (E2r: forall i v, In i cs_all -> getr R1 (reg i) = v -> getr R2 (reg i) = v). { intros i v Hi Hv. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. exact Hv. }
    destruct g as [|A cap]. 2:{ exfalso. destruct GP as (_ & N3 & _). clear - N3 NL2. lia. }
    destruct GP as (DYS & -> & -> & (st' & OQ2 & OL2 & SST) & HP2). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in OQ2, OL2, SST, HP2.
    destruct st' as [q0' q1'|cq' p']. 2: destruct SST.
    assert (INn: Z.testbit fn 0 = true -> In (pn, 64) LBc).
    { intros T. destruct (FR2 T) as [Ec _]. subst LBc BN. rewrite T, Ec. apply in_app_iff. left. left. reflexivity. }
    assert (INd: Z.testbit fd 0 = true -> In (pd, 64) LBc).
    { intros T. destruct (FR3 T) as [Ec _]. subst LBc BD. rewrite T, Ec. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
    assert (HWo: forall a, ~ (Q <= a < Q + 32) -> L5.outside [(Q, 32); (Q + 16 + 8 * Z.of_nat 0, 8 * Z.max 0 (Z.of_nat (n1 - l1) - Z.of_nat 0))] a).
    { intros a NQ r [<-|[<-|[]]]; unfold L5.in_rng; cbn -[Z.of_nat Z.max Z.mul Z.add Z.sub]. exact NQ. clear - NQ NL2. lia. }
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha Hn. apply (kept_above M1 M2 LBc spd RESIZE_SCR _ a HP2). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). exact Ha. apply HWo. exact Hn. }
    assert (HP2': L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M2).
    { eapply (L5HP.hpres_trans L LB LBc S SCR_OPMOD [(X, 32)] M0 M1 M2 spd RESIZE_SCR _). exact HP1. exact HP2.
      + intros a KA'. pose proof (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' ltac:(intros b Hb; apply LBceil; apply LBcI; exact Hb) CEILS ltac:(rewrite IMG'; clear - SPT; lia)) as NS'.
        eapply L5HP.kept_mono. exact KA'. exact LBcI. unfold spd; rewrite SCR_OPMOD_val, RESIZE_SCR_val; clear; lia. unfold spd; clear; lia.
        intros _. apply HWo. rewrite SCR_OPMOD_val in NS'. unfold Q. clear - NS'. lia.
      + exact LBcI. + exact CEILS. + clear - SHI; lia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + exact (proj1 SPT). }
    assert (KD: forall i, denomd <= i < denomd + 8 * Z.of_nat l1 -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
    { intros i Hi. subst denomd. destruct (Z.testbit fd 0) eqn:Tfd.
      { pose proof (LBceil (pd, 64) (INd eq_refl)) as PC. cbn in PC.
        apply (kept_inblock M1 M2 LBc crc _ spd RESIZE_SCR _ pd 64 i HH1 HP2). apply INd; reflexivity. clear - Hi L13; lia. exact SPT. apply HWo. unfold Q; clear - Hi PC SLO' L13; lia. }
      apply KA. unfold spd; clear - Hi SLO SHI L13; lia. unfold Q; clear - Hi L13; lia. }
    apply (stage_G5 fx2 R2 M2 model2 crc j 0 (n1 - l1)%nat q0' q1' fn cn pn stn fd cd pd fn0 fd0 denomd).
    all: try (eapply E2r; [inl | rewrite (K1 _) by inl; eassumption]).
    all: try (eapply E2r; [inl | eassumption]).
    all: try assumption.
    + eapply u64_at_agree1. 4: exact VD1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
    + eapply u64_at_agree1. 4: exact VS1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
    + rewrite SCR_OPMOD_val. eapply SCR_kept. exact HP2. rewrite RESIZE_SCR_val; clear; lia. exact SCR1.
    + eapply IC_kept. exact HP2. 2: exact IC1. intros a Ha. apply HWo. unfold Q; clear - Ha SLO; lia.
    + eapply mid_kept. 4: exact MD1.
      * intros i Hi. apply KA. unfold spd; clear - Hi SLO SHI; lia. unfold Q; clear - Hi; lia.
      * intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pn 64). apply INn. exact T.
      * intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pd 64). apply INd. exact T.
    + subst l. clear - LN' L13; lia.
    + destruct XA as [OXA NEGA]. split. 2: exact NEGA. eapply big_at_agree1. 4:{ eapply big_at_agree1. 4: exact OXA. intros i Hi; apply KU; unfold X in Hi; clear - Hi; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia. }
      intros i Hi; apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
    + eapply (cdef_above M1 M2 _ spd RESIZE_SCR _ X 32 HP2). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). unfold X, spd; clear; lia. unfold X; clear - SHI; lia.
      eapply L5.defined_grows. exact MG1. exact DX.
    + eapply big_at_agree1. 4:{ eapply big_at_agree1. 4: exact ON. intros i Hi; apply KU2; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
      intros i Hi; apply KA; unfold Q, spd; clear - Hi SLO SHI; lia. clear - SLO; lia. clear - SHI; lia.
    + eapply obj_limbs_agree1. 3:{ eapply obj_limbs_agree1. 3: exact LN. all: cbn [L5.bo_st L5.bo_len]; intros cap q E; destruct (NST cap q E) as [-> ->]; rewrite E in NS; destruct NS as (NT & _); destruct (FR2 NT) as [Ec FBn];
        pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBn) as (P1 & _ & _ & _ & P5). intros i Hi. apply KF. clear - Hi P1 P5 SPT LR4; lia. clear - Hi P5 SLO' LR4; lia. clear - Hi P5 SLO' LR4; lia. clear - P1 P5 SPT LR4; lia. }
      all: cbn [L5.bo_st L5.bo_len]; intros cap q E; destruct (NST cap q E) as [-> ->]; rewrite E in NS; destruct NS as (NT & _).
      * pose proof (LBceil (pn, 64) (INn NT)) as PC. cbn in PC. intros i Hi. apply (kept_inblock M1 M2 LBc crc _ spd RESIZE_SCR _ pn 64 i HH1 HP2). apply INn; exact NT. clear - Hi LR4; lia. exact SPT.
        apply HWo. unfold Q; clear - Hi PC SLO' LR4; lia.
      * destruct (FR2 NT) as [Ec FBn]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBn) as (P1 & _ & _ & _ & P5). clear - P1 P5 SPT LR4; lia.
    + reflexivity.
    + eapply defined_agree1. 2:{ eapply L5.defined_grows. exact MG1. exact DDEF. } intros i Hi; apply KD; exact Hi.
    + eapply u64_at_agree1. 4:{ eapply u64_at_agree1. 4: exact Cd. 2: clear - DNlo'; lia. 2: clear - DNhi; lia. intros i Hi. subst denomd. destruct (Z.testbit fd 0).
        - destruct (FR3 eq_refl) as [_ FBd]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & _ & _ & _ & P5). apply KF. clear - Hi P1 P5 SPT Hl; lia. clear - Hi P5 SLO' Hl; lia. clear - Hi P5 SLO' Hl; lia.
        - apply KF; clear - Hi Hl SLO SHI; lia. }
      intros i Hi; apply KD; subst l; clear - Hi L13; lia. clear - DNlo'; lia. clear - DNhi; lia.
    + eapply big_at_agree1. 4:{ eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KU; subst bo; clear - Hi; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia. }
      intros i Hi; apply KA; subst bo; unfold Q, spd; clear - Hi SLO SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5OPMOD1GBU.
