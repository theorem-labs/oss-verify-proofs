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
 Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkDivBaseU L5Defs L5Kn L5Core L5CoreSpecsU L5CoreKitU L5Words L5Hp
 L5ShlU L5MulMU L5NormU L5CmpU L5CoreKit L5DivSpecsU L5DivPartsU L5DivNPU L5DivOPU L5DivO2PU L5DivEarlyU L5OpMod1SU L5OpMod1HU L5OpMod1V.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigFactsBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Module L5OPMOD1GU.
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

Lemma SCR_OPMOD_val : SCR_OPMOD = 10240. Proof. reflexivity. Qed.
Lemma DIV_SCR_val : DIV_SCR = 8976. Proof. reflexivity. Qed.
Lemma RESIZE_SCR_val : RESIZE_SCR = 8416. Proof. reflexivity. Qed.
Lemma ASSIGN_SCR_val : ASSIGN_SCR = 8464. Proof. reflexivity. Qed.
Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.
Lemma o1_saves_kept M M' S R0 : (forall i, S - 168 <= i < S - 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= S - 168 -> S <= 2 ^ 64 ->
  o1_saves M S R0 -> o1_saves M' S R0.
Proof.
  intros HA Hlo Hhi SV. destruct SV as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  unfold o1_saves. repeat split; (eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]).
Qed.
Lemma local_obj_kept M M' o f c p : (forall i, o <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  local_obj M o f c p -> local_obj M' o f c p.
Proof.
  intros HA Ho Hhi (U0 & F & D). split. { eapply u8_at_agree1. 4: exact U0. intros i Hi; apply HA; clear - Hi; lia. exact Ho. clear - Hhi; lia. } split. exact F.
  intros T. destruct (D T) as (C16 & Hc & C24 & Hp). split. { eapply u64_at_agree1. 4: exact C16. intros i Hi; apply HA; clear - Hi; lia. clear - Ho; lia. clear - Hhi; lia. }
  split. exact Hc. split. { eapply u64_at_agree1. 4: exact C24. intros i Hi; apply HA; clear - Hi; lia. clear - Ho; lia. clear - Hhi; lia. } exact Hp.
Qed.
(* [comment removed for export] *)
Lemma blocks_ofst_inl v0 v1 : blocks_ofst (L5.BInl v0 v1) = []. Proof. reflexivity. Qed.
Lemma blocks_ofst_dyn cap p : blocks_ofst (L5.BDyn cap p) = [(p, 8 * cap)]. Proof. reflexivity. Qed.

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
Lemma SPW : S mod 16 = 0 /\ 0x7fff7f800000 + 10240 <= S /\ S + 240 <= 2 ^ 47 /\ hl_sptop L - 8388608 + 10240 <= S /\ S + 240 <= hl_sptop L
            /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof. pose proof STK as (A & B & C' & D & _). uSCR. repeat split; try lia. Qed.
Lemma WBF : wb = firstn nb [b0; b1] /\ 0 <= b0 < 2 ^ 64 /\ 0 <= b1 < 2 ^ 64 /\ nth_w wb (nb - 1) <> 0.
Proof.
  pose proof BOK as (OB & OL & RED & _). pose proof OL as (Ln & Wok & Wst). rewrite STB in Wst. unfold L5.big_at in OB. rewrite STB in OB.
  destruct OB as (_ & _ & _ & _ & _ & _ & _ & R0' & R1'). fold nb in Wst, Ln.
  split. exact Wst. split. exact R0'. split. exact R1'.
  destruct RED as [E|NZ]. { exfalso. rewrite E in Ln. cbn in Ln. destruct NB12 as [H|H]; rewrite H in Ln; discriminate Ln. }
  rewrite Ln in NZ. unfold nth_w. exact NZ.
Qed.
Lemma OLB_any M : L5C.obj_limbs RSEGS M bb wb.
Proof. pose proof BOK as (_ & (Ln & Wok & Wst) & _). split. exact Ln. split. exact Wok. rewrite STB in Wst |- *. exact Wst. Qed.
(* [comment removed for export] *)
Lemma NF : (1 <= l1 <= 3)%nat /\ (2 <= n1 <= 4)%nat /\ (l1 <= n1)%nat /\ (n1 - l1 <= 2)%nat
  /\ (l1 <= length rwd)%nat /\ (length rwd <= 3)%nat /\ (n1 <= length rwn)%nat /\ (length rwn <= 4)%nat
  /\ 2 ^ 63 <= d < 2 ^ 64
  /\ (sec = true -> nb = 2%nat /\ l1 = 3%nat /\ (3 <= n1)%nat /\ length rwd = 3%nat /\ (3 <= length rwn)%nat)
  /\ (sec = false -> l1 = nb /\ (n1 <= 3)%nat)
  /\ ((3 <= length rwd)%nat <-> nb = 2%nat)
  /\ ((3 <= length rwn)%nat <-> 1 <= c)
  /\ (nb = 2%nat -> 1 <= c).
Proof.
  pose proof WBF as (W1 & W2 & W3 & W4). pose proof BOK as (_ & _ & RED & _).
  exact (L5OM1V.norm_facts nb b0 b1 wb NB12 W1 W2 W3 W4 V1 V2).
Qed.

(* [comment removed for export] *)
Lemma Hc63 : 0 <= c <= 63.
Proof. pose proof WBF as (W1 & W2 & W3 & W4). exact (proj1 (L5OM1V.c_spec nb b0 b1 wb NB12 W1 W2 W3 W4 V1 V2)). Qed.
(* [comment removed for export] *)
Lemma SCR_kept M M' LBx W scr : L5C.hpres L LBx spd scr W M M' -> 0 <= scr <= 9000 ->
  L5.defined M (S - 10240) 10240 -> L5.defined M' (S - 10240) 10240.
Proof.
  intros HPW Hs D i Hi. pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT).
  destruct (Z_lt_le_dec (S - 10240 + i) (spd - scr)) as [C1|C1].
  - pose proof (cdef_below M M' LBx spd scr W (S - 10240) (spd - scr - (S - 10240)) HPW ltac:(clear - SLO'; lia) ltac:(clear; lia) ltac:(clear - Hs; lia) (proj1 SPT)
                  ltac:(unfold spd; clear - SHI; lia) ltac:(eapply L5.defined_sub; [exact D | clear; lia | unfold spd; clear - Hs; lia])) as D'.
    apply D'. clear - Hi C1. lia.
  - destruct (Z_lt_le_dec (S - 10240 + i) spd) as [C2|C2].
    + pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HPW) as D'. replace (S - 10240 + i) with (spd - scr + (S - 10240 + i - (spd - scr))) by (clear; lia). apply D'. clear - C1 C2; lia.
    + pose proof (cdef_above M M' LBx spd scr W spd 416 HPW ltac:(unfold spd; clear - SLO' Hs; lia) ltac:(clear - Hs; lia) (proj1 SPT) ltac:(clear; lia) ltac:(unfold spd; clear - SHI; lia)
                    ltac:(eapply L5.defined_sub; [exact D | unfold spd; clear; lia | unfold spd; clear; lia])) as D'.
      replace (S - 10240 + i) with (spd + (S - 10240 + i - spd)) by (clear; lia). apply D'. unfold spd in C2 |- *. clear - C2 Hi; lia.
Qed.
(* [comment removed for export] *)
Lemma IC_kept M M' LBx sp' scr W : L5C.hpres L LBx sp' scr W M M' -> (forall a, 0x10000 <= a < 0x20000 -> L5.outside W a) ->
  L5.img_clear M 0x10000 0x20000 -> L5.img_clear M' 0x10000 0x20000.
Proof.
  intros HPW HW IC i Hi. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'. pose proof ERRNOV as EV. rewrite <- (IC i Hi).
  apply (L5C.hpres_kept _ _ _ _ _ _ _ i HPW). eapply L5C.kept_static. rewrite IMGLO', IMG'; clear - Hi; lia.
  { intros ST. apply (ly_static L LY) in ST. clear - ST Hi. lia. } rewrite IMGLO'; clear; lia. rewrite IMG'; clear; lia. rewrite EV; clear - Hi; lia.
  apply HW. exact Hi.
Qed.
Lemma CAPB2 : capb = 2.
Proof. unfold capb, L5.bo_cap. rewrite STB. reflexivity. Qed.
(* [comment removed for export] *)
Lemma credit_next crc j : fst cr - j * hl_k_per_malloc L <= fst crc -> snd cr - j * (64 + hl_b_overhead L) <= snd crc -> 0 <= j <= 3 -> credit_ok L crc 64.
Proof.
  intros A B J. pose proof CR as [C1 C2]. unfold credit_for, OPMOD1_K, opmod1_bytes in C1, C2. rewrite CAPB2 in C2. pose proof KPOS. pose proof BPOS.
  unfold credit_ok. split; nia.
Qed.
Lemma credit_step crc j : fst cr - j * hl_k_per_malloc L <= fst crc -> snd cr - j * (64 + hl_b_overhead L) <= snd crc ->
  fst cr - (j + 1) * hl_k_per_malloc L <= fst (debit L crc 64) /\ snd cr - (j + 1) * (64 + hl_b_overhead L) <= snd (debit L crc 64).
Proof using L cr S bb wb b0 NB12 V1 V2. intros A B. unfold debit. cbn [fst snd]. split; lia. Qed.
Lemma Hq01 : 0 <= qneg <= 1.
Proof using S bb wb b0 NB12 V1 V2. subst qneg. destruct (Z.testbit (L5.bo_fb bb) 1); cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition late (M : word -> option byte) (fn cn pn fd cd pd fn0 fd0 : Z) : Prop :=
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  top_frame M S R0 /\ o1_saves M S R0 /\
  local_obj M (S - 344) fd0 0 0 /\ Z.testbit fd0 0 = false /\ local_obj M (S - 280) fn0 0 0 /\ Z.testbit fn0 0 = false /\
  local_obj M (S - 248) fn cn pn /\ (Z.testbit fn 0 = true -> cn = 8 /\ L5C.fresh_block L LB M pn 64) /\
  local_obj M (S - 200) fd cd pd /\ (Z.testbit fd 0 = true -> cd = 8 /\ L5C.fresh_block L (BN ++ LB) M pd 64) /\
  L5.u32_at RSEGS M (S - 348) c /\ L5.u64_at RSEGS M (S - 400) 1 /\
  L5.u64_at RSEGS M (S - 384) 0 /\ L5.u64_at RSEGS M (S - 392) qneg /\ L5.u64_at RSEGS M (S - 408) sd.
Lemma late_kept M M' fn cn pn fd cd pd fn0 fd0 :
  (forall i, (S - 408 <= i < S - 376 \/ S - 348 <= i < S - 312 \/ S - 280 <= i < S - 216 \/ S - 200 <= i < S - 64 \/ S - 32 <= i < S) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (Z.testbit fn 0 = true -> L5.defined M pn 64 -> L5.defined M' pn 64) -> (Z.testbit fd 0 = true -> L5.defined M pd 64 -> L5.defined M' pd 64) ->
  late M fn cn pn fd cd pd fn0 fd0 -> late M' fn cn pn fd cd pd fn0 fd0.
Proof.
  intros HA Dn Dd LT. pose proof SPW as (A16 & SLO & SHI & _).
  destruct LT as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C400 & C384 & C392 & C408).
  split. { eapply top_frame_kept. 4: exact TF. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { eapply o1_saves_kept. 4: exact SAV. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { eapply local_obj_kept. 4: exact LO0. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. } split. exact F0b.
  split. { eapply local_obj_kept. 4: exact LO1. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. } split. exact F1b.
  split. { eapply local_obj_kept. 4: exact LO2. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { intros T. destruct (FR2 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. exact (Dn T B3'). }
  split. { eapply local_obj_kept. 4: exact LO3. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { intros T. destruct (FR3 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. exact (Dd T B3'). }
  split. { eapply u32_at_agree1. 4: exact C348. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  repeat split; (eapply u64_at_agree1; [ | | | eassumption]; [intros i Hi; apply HA; clear - Hi; lia | clear - SLO; lia | clear - SHI; lia]).
Qed.
(* [comment removed for export] *)
Definition mid (M : word -> option byte) (fn cn pn fd cd pd fn0 fd0 : Z) : Prop :=
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  top_frame M S R0 /\ o1_saves M S R0 /\
  local_obj M (S - 344) fd0 0 0 /\ Z.testbit fd0 0 = false /\ local_obj M (S - 280) fn0 0 0 /\ Z.testbit fn0 0 = false /\
  local_obj M (S - 248) fn cn pn /\ (Z.testbit fn 0 = true -> cn = 8 /\ L5C.fresh_block L LB M pn 64) /\
  local_obj M (S - 200) fd cd pd /\ (Z.testbit fd 0 = true -> cd = 8 /\ L5C.fresh_block L (BN ++ LB) M pd 64) /\
  L5.u32_at RSEGS M (S - 348) c /\ L5.u64_at RSEGS M (S - 408) sd.
Lemma mid_kept M M' fn cn pn fd cd pd fn0 fd0 :
  (forall i, (S - 408 <= i < S - 400 \/ S - 348 <= i < S - 312 \/ S - 280 <= i < S - 216 \/ S - 200 <= i < S - 64 \/ S - 32 <= i < S) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (Z.testbit fn 0 = true -> L5.defined M pn 64 -> L5.defined M' pn 64) -> (Z.testbit fd 0 = true -> L5.defined M pd 64 -> L5.defined M' pd 64) ->
  mid M fn cn pn fd cd pd fn0 fd0 -> mid M' fn cn pn fd cd pd fn0 fd0.
Proof.
  intros HA Dn Dd LT. pose proof SPW as (A16 & SLO & SHI & _).
  destruct LT as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C408).
  split. { eapply top_frame_kept. 4: exact TF. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { eapply o1_saves_kept. 4: exact SAV. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { eapply local_obj_kept. 4: exact LO0. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. } split. exact F0b.
  split. { eapply local_obj_kept. 4: exact LO1. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. } split. exact F1b.
  split. { eapply local_obj_kept. 4: exact LO2. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { intros T. destruct (FR2 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. exact (Dn T B3'). }
  split. { eapply local_obj_kept. 4: exact LO3. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  split. { intros T. destruct (FR3 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. exact (Dd T B3'). }
  split. { eapply u32_at_agree1. 4: exact C348. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia. }
  eapply u64_at_agree1. 4: exact C408. intros i Hi; apply HA; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
Qed.
Lemma late_of_mid M fn cn pn fd cd pd fn0 fd0 :
  mid M fn cn pn fd cd pd fn0 fd0 -> L5.u64_at RSEGS M (S - 400) 1 -> L5.u64_at RSEGS M (S - 384) 0 -> L5.u64_at RSEGS M (S - 392) qneg ->
  late M fn cn pn fd cd pd fn0 fd0.
Proof.
  intros (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C408) C400 C384 C392.
  unfold late. repeat (split; [assumption|]). exact C408.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_L (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (n : nat) (fq : Z) (nq : nat) (stq : L5.bstore) (fxx : Z) (rst : L5.bstore) (wr : list Z)
      (fn cn pn fd cd pd fn0 fd0 remd quotd denomd : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := blocks_ofst stq ++ blocks_ofst rst ++ BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l + 1) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat l) -> getr R (reg 23) = Z_to_bv 64 (Z.of_nat n) ->
  (* [comment removed for export] *)
  L5.u64_at RSEGS M (Q - 304) remd -> L5.u64_at RSEGS M (Q - 232) quotd ->
  L5.u64_at RSEGS M (Q - 152) denomd -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat l + 1) ->
  (l <= n)%nat -> (n <= l + 3)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - 4 * hl_k_per_malloc L <= fst crc -> snd cr - 4 * (64 + hl_b_overhead L) <= snd crc ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  top_frame M S R0 -> o1_saves M S R0 ->
  local_obj M (S - 344) fd0 0 0 -> Z.testbit fd0 0 = false -> local_obj M (S - 280) fn0 0 0 -> Z.testbit fn0 0 = false ->
  local_obj M (S - 248) fn cn pn -> (Z.testbit fn 0 = true -> cn = 8 /\ L5C.fresh_block L LB M pn 64) ->
  local_obj M (S - 200) fd cd pd -> (Z.testbit fd 0 = true -> cd = 8 /\ L5C.fresh_block L (BN ++ LB) M pd 64) ->
  L5.u32_at RSEGS M (S - 348) c ->
  L5.u64_at RSEGS M (S - 400) 1 -> L5.u64_at RSEGS M (S - 384) 0 -> L5.u64_at RSEGS M (S - 392) qneg -> L5.u64_at RSEGS M (S - 408) sd ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Q (L5.BO fq nq stq) -> nq = (n - l)%nat ->
  (forall cq p, stq = L5.BDyn cq p -> cq = 8 /\ L5C.fresh_block L (blocks_ofst rst ++ BN ++ BD ++ LB) M p 64) ->
  quotd = L5.bo_data Q (L5.BO fq nq stq) -> (match stq with L5.BInl _ _ => (nq <= 2)%nat | L5.BDyn _ _ => True end) ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M X (L5.BO fxx (Datatypes.S n) rst) -> Z.testbit fxx 1 = false -> L5.defined M X 32 ->
  (forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ L5C.fresh_block L (BN ++ BD ++ LB) M p 64) ->
  remd = L5.bo_data X (L5.BO fxx (Datatypes.S n) rst) -> (match rst with L5.BInl _ _ => (n + 1 <= 2)%nat | L5.BDyn _ _ => True end) ->
  (* [comment removed for export] *)
  denomd = (if Z.testbit fd 0 then pd else S - 184) -> (Z.testbit fd 0 = false -> (l1 <= 2)%nat) -> L5.defined M denomd (8 * Z.of_nat l1) ->
  L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d ->
  (* [comment removed for export] *)
  (sec = true -> (exists qx, rst = L5.BDyn 8 qx) /\ (exists q0 q1, stq = L5.BInl q0 q1) /\ Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R PRE M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H18 H21 H22 H23 VR VQ VD VS Hln Hnl MBV HH CRK CRB SCR IC TF SAV LO0 F0b LO1 F1b LO2 FRESH2 LO3 FRESH3
         C348 C400 C384 C392 C408 OQ NQ QDYN Eqd QFIT OX NEGX DX XDYN Erd RFIT Edd DINL DDEF Cd SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'. rewrite SCR_OPMOD_val in SCR.
  pose proof NF as (L13 & N24 & LN & NL2 & _ & _ & _ & _ & DR & SECF & _).
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia).
  assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L).
  { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
  (* [comment removed for export] *)
  assert (REMD: remd mod 8 = 0 /\ 4096 <= remd /\ remd + 8 * (Z.of_nat n + 1) <= 2 ^ 47 /\ L5.defined M remd (8 * (Z.of_nat n + 1)) /\
                ((remd = X + 16 /\ (n + 1 <= 2)%nat) \/ (blocks_ofst rst = [(remd, 64)] /\ In (remd, 64) LBc /\ remd + 64 <= hl_ceil L /\ (n + 1 <= 8)%nat /\
                                                         (forall b, In b (BN ++ BD ++ LB) -> remd + 64 <= fst b \/ fst b + snd b <= remd)))).
  { rewrite Erd. destruct rst as [v0 v1|cx p]; cbn [L5.bo_data L5.bo_st].
    - split. { unfold X. replace (S + 64 + 16) with (S + 8 * 10) by (clear; lia). apply al8. exact A16. }
      split. unfold X; flia. split. unfold X; clear - RFIT SHI; lia. split. { eapply L5.defined_sub. exact DX. clear; lia. unfold X; clear - RFIT; lia. }
      left. split. reflexivity. exact RFIT.
    - destruct (XDYN cx p eq_refl) as [-> FBx]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBx) as (P1 & P2 & P3 & _ & P5). destruct FBx as (_ & BAx & DFx).
      split. apply mod16_mod8; exact P3. split. exact P1. split. clear - P5 Hnl Hl SPT; lia.
      split. { eapply L5.defined_sub. exact DFx. clear; lia. clear - Hnl Hl; lia. }
      right. split. reflexivity. split. { subst LBc. apply in_app_iff. right. apply in_app_iff. left. cbn. left. reflexivity. } split. exact P5. split. clear - Hnl Hl; lia. exact BAx. }
  assert (QUOTD: quotd mod 8 = 0 /\ 4096 <= quotd /\ quotd + 8 * (Z.of_nat n - Z.of_nat l) <= 2 ^ 47 /\ L5.writable RSEGS M quotd (8 * (Z.of_nat n - Z.of_nat l)) /\
                 ((quotd = Q + 16 /\ (n - l <= 2)%nat) \/ (blocks_ofst stq = [(quotd, 64)] /\ In (quotd, 64) LBc /\ quotd + 64 <= hl_ceil L /\
                                                          (forall b, In b (blocks_ofst rst ++ BN ++ BD ++ LB) -> quotd + 64 <= fst b \/ fst b + snd b <= quotd)))).
  { rewrite Eqd. destruct stq as [v0 v1|cq p]; cbn [L5.bo_data L5.bo_st].
    - split. { unfold Q. replace (S - 64 + 16) with (S + 8 * (-6)) by (clear; lia). apply al8. exact A16. }
      split. unfold Q; flia. split. unfold Q; clear - QFIT NQ SHI Hln; lia.
      split. { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR. unfold Q; clear; lia. unfold Q; clear - QFIT NQ Hln; lia. unfold Q; flia. unfold Q; clear - QFIT NQ Hln SHI; lia. }
      left. split. reflexivity. clear - QFIT NQ; lia.
    - destruct (QDYN cq p eq_refl) as [-> FBq]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBq) as (P1 & P2 & P3 & _ & P5). destruct FBq as (_ & BAq & DFq).
      split. apply mod16_mod8; exact P3. split. exact P1. split. clear - P5 Hnl Hln SPT; lia.
      split. { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact DFq. clear; lia. clear - Hnl Hln; lia. clear - P1; lia. clear - P5 Hnl Hln SPT; lia. }
      right. split. reflexivity. split. { subst LBc. apply in_app_iff. left. cbn. left. reflexivity. } split. exact P5. exact BAq. }
  assert (DEND: denomd mod 8 = 0 /\ 4096 <= denomd /\ denomd + 8 * (Z.of_nat l + 1) <= 2 ^ 47 /\ L5.defined M denomd (8 * (Z.of_nat l + 1)) /\
                ((denomd = S - 184 /\ (l1 <= 2)%nat) \/ (In (denomd, 64) (BD ++ LB) /\ In (denomd, 64) LBc /\ denomd + 64 <= hl_ceil L /\
                                                       (forall b, In b (BN ++ LB) -> denomd + 64 <= fst b \/ fst b + snd b <= denomd)))).
  { assert (EL: Z.of_nat l + 1 = Z.of_nat l1) by (subst l; clear - L13; lia). rewrite EL. rewrite Edd in DDEF |- *.
    destruct (Z.testbit fd 0) eqn:Tfd.
    - destruct (FRESH3 eq_refl) as [-> FBd]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & P2 & P3 & _ & P5). destruct FBd as (_ & BAd & DFd).
      split. apply mod16_mod8; exact P3. split. exact P1. split. clear - P5 L13 SPT; lia. split. exact DDEF.
      right. split. { subst BD. apply in_app_iff. left. cbn. left. reflexivity. }
      split. { subst LBc BD. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. cbn. left; reflexivity. }
      split. exact P5. exact BAd.
    - split. { replace (S - 184) with (S + 8 * (-23)) by (clear; lia). apply al8. exact A16. } split. flia. split. clear - L13 SHI; lia. split. exact DDEF.
      left. split. reflexivity. exact (DINL eq_refl). }
  destruct REMD as (RM8 & RMlo & RMhi & RMdef & RMW). destruct QUOTD as (QD8 & QDlo & QDhi & QDwr & QDW). destruct DEND as (DN8 & DNlo & DNhi & DNdef & DNW).
  assert (BNc: forall b, In b BN -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; left; exact Hb. }
  assert (BDc: forall b, In b BD -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; right; left; exact Hb. }
  assert (LBcI: forall b, In b LB -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; right; right; exact Hb. }
  assert (RSTc: forall b, In b (blocks_ofst rst) -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; left; exact Hb. }
  (* [comment removed for export] *)
  assert (AP_RQ: apart remd (8 * (Z.of_nat n + 1)) quotd (8 * (Z.of_nat n - Z.of_nat l))).
  { unfold apart. destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)]; destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)].
    - unfold X, Q. clear - Rn Qn Hln. lia.
    - pose proof (LBceil _ QIn) as QC. cbn in QC. unfold X. clear - QC Rn SLO' Hln. lia.
    - pose proof (LBceil _ RIn) as RC. cbn in RC. unfold Q. clear - RC Rn Qn SLO' Hln. lia.
    - destruct (QBA (remd, 64) ltac:(apply in_app_iff; left; rewrite RB; left; reflexivity)) as [A|A]; cbn in A; clear - A Rn Hln Hnl Hl; lia. }
  assert (AP_RD: apart remd (8 * (Z.of_nat n + 1)) denomd (8 * (Z.of_nat l + 1))).
  { unfold apart. destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)]; destruct DNW as [(-> & Dn)|(DIn & DInc & Dhi & DBA)].
    - unfold X. clear - Rn Dn Hl. lia.
    - unfold X. clear - Dhi Hl SLO'. lia.
    - clear - Rhi Rn SLO'. lia.
    - destruct (RBA (denomd, 64) ltac:(apply in_app_iff; right; exact DIn)) as [A|A]; cbn in A; clear - A Rn Hl; lia. }
  assert (AP_QD: apart quotd (8 * (Z.of_nat n - Z.of_nat l)) denomd (8 * (Z.of_nat l + 1))).
  { unfold apart. destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)]; destruct DNW as [(-> & Dn)|(DIn & DInc & Dhi & DBA)].
    - unfold Q. clear - Qn Dn Hl Hln. lia.
    - unfold Q. clear - Dhi Hl SLO' Hln. lia.
    - clear - Qhi Hln Hnl SLO'. lia.
    - destruct (QBA (denomd, 64) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact DIn)) as [A|A]; cbn in A; clear - A Hln Hnl Hl; lia. }
  assert (AP_RF: apart remd (8 * (Z.of_nat n + 1)) (Q - 416) 416).
  { unfold apart, Q. destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)]. unfold X; clear - Rn; lia. clear - Rhi Rn SLO'; lia. }
  assert (AP_QF: apart quotd (8 * (Z.of_nat n - Z.of_nat l)) (Q - 416) 416).
  { unfold apart, Q. destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)]. clear - Qn Hln; lia. clear - Qhi Hln Hnl SLO'; lia. }
  assert (AP_DF1: apart denomd (8 * (Z.of_nat l + 1)) (Q - 312) 8).
  { unfold apart, Q. destruct DNW as [(-> & Dn)|(DIn & DInc & Dhi & DBA)]. clear - Dn Hl; lia. clear - Dhi Hl SLO'; lia. }
  assert (AP_DF2: apart denomd (8 * (Z.of_nat l + 1)) (Q - 416) 64).
  { unfold apart, Q. destruct DNW as [(-> & Dn)|(DIn & DInc & Dhi & DBA)]. clear - Dn Hl; lia. clear - Dhi Hl SLO'; lia. }
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  (* [comment removed for export] *)
  destruct (DIVLOOP fx R M Q X remd quotd denomd d l n
              ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H18 H21 H22 H23 VR VQ VD VS Cd
              DR ltac:(clear - Hln Hnl Hl; lia) ltac:(unfold X; flia) AQ16 ltac:(unfold Q; flia)
              RM8 RMlo RMhi RMdef ltac:(apply (L5C.writable_of_defined RSEGS); [exact RMdef | clear - RMlo; lia | clear - RMhi; lia])
              QD8 QDlo QDhi QDwr
              DN8 DNlo DNhi DNdef
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR | unfold Q; clear; lia | unfold Q; clear; lia] | unfold Q; flia | unfold Q; flia])
              ltac:(eapply L5.defined_sub; [exact SCR | unfold Q; clear; lia | unfold Q; clear; lia])
              AP_RF AP_QF AP_RQ AP_RD AP_QD AP_DF1 AP_DF2)
    as (fx1 & R1 & M1 & MS1 & A2 & K1 & FR1 & MG1).
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (remd <= i < remd + 8 * (Z.of_nat n + 1)) -> ~ (quotd <= i < quotd + 8 * (Z.of_nat n - Z.of_nat l)) ->
                 ~ (Q - 312 <= i < Q - 312 + 8) -> ~ (Q - 416 <= i < Q - 416 + 64) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2 N3 N4. apply FR1; unfold inr; rewrite BG.unsigned_lit by exact Hi; assumption. }
  (* [comment removed for export] *)
  assert (KC: forall i, 0 <= i < 2 ^ 64 -> ~ (X + 16 <= i < X + 32) -> ~ (Q + 16 <= i < Q + 32) -> ~ (Q - 312 <= i < Q - 304) -> ~ (Q - 416 <= i < Q - 352) ->
                hl_ceil L <= i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2 N3 N4 N5. apply KEEP1. exact Hi.
    - destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)]. clear - N1 Rn; lia. clear - Rhi Rn N5; lia.
    - destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)]. clear - N2 Qn Hln; lia. clear - Qhi N5 Hln Hnl; lia.
    - clear - N3; lia. - clear - N4; lia. }
  assert (KF: forall i, S - 408 <= i < S - 48 -> ~ (S - 376 <= i < S - 368) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Ni. apply KC; unfold X, Q; clear - Hi Ni SLO SLO' SHI; lia. }
  assert (KXH: forall i, X <= i < X + 16 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KC; unfold X, Q in *; clear - Hi SLO SLO' SHI; lia. }
  assert (SCR1: L5.defined M1 (S - 10240) 10240) by (eapply L5.defined_grows; [exact MG1 | exact SCR]).
  assert (DX1: L5.defined M1 X 32) by (eapply L5.defined_grows; [exact MG1 | exact DX]).
  (* [comment removed for export] *)
  assert (RST1: exists rst1 wr1, blocks_ofst rst1 = blocks_ofst rst /\ (forall cx p, rst1 = L5.BDyn cx p -> rst = L5.BDyn cx p) /\ (forall cx p, rst = L5.BDyn cx p -> rst1 = rst)
            /\ L5.big_at RSEGS M1 X (L5.BO fxx (Datatypes.S n) rst1) /\ L5C.obj_limbs RSEGS M1 (L5.BO fxx (Datatypes.S n) rst1) wr1).
  { pose proof OX as (Ob0 & Obf & Ob8 & ObS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Ob0, Obf, Ob8, ObS.
    destruct rst as [v0 v1|cx p].
    - destruct ObS as (Tb & _ & _ & Hle & _).
      destruct (BDU.defined_word M1 (X + 16) ltac:(eapply L5.defined_sub; [exact DX1 | clear; lia | clear; lia]) ltac:(unfold X; flia) ltac:(unfold X; flia)) as (v0' & R0' & U0').
      destruct (BDU.defined_word M1 (X + 24) ltac:(eapply L5.defined_sub; [exact DX1 | clear; lia | clear; lia]) ltac:(unfold X; flia) ltac:(unfold X; flia)) as (v1' & R1' & U1').
      exists (L5.BInl v0' v1'), (firstn (Datatypes.S n) [v0'; v1']). split. reflexivity. split. intros cx p E; discriminate E. split. intros cx p E; discriminate E.
      split. { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Ob0. intros i Hi; apply KXH; clear - Hi; lia. unfold X; flia. unfold X; flia. }
               split. exact Obf. split. { eapply u64_at_agree1. 4: exact Ob8. intros i Hi; apply KXH; clear - Hi; lia. unfold X; flia. unfold X; flia. }
               split. exact Tb. split. exact U0'. split. exact U1'. split. exact Hle. split. exact R0'. exact R1'. }
      split. { cbn [L5.bo_len]. rewrite length_firstn. cbn [length]. clear - RFIT; lia. }
      split. { cbn. destruct n as [|[|n']]; cbn; repeat constructor; clear - R0' R1'; lia. } reflexivity.
    - destruct (XDYN cx p eq_refl) as [-> FBx]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBx) as (P1 & P2 & P3 & _ & P5). destruct FBx as (_ & BAx & DFx).
      rewrite Erd in RMdef. cbn [L5.bo_data L5.bo_st] in RMdef.
      destruct (L5KU.limbs_of_defined M1 p (Datatypes.S n) ltac:(eapply L5.defined_grows; [exact MG1|]; replace (8 * Z.of_nat (Datatypes.S n)) with (8 * (Z.of_nat n + 1)) by (clear; lia); exact RMdef)
                  ltac:(clear - P1; lia) ltac:(clear - P5 SPT Hnl Hl; lia)) as (wr1 & WL & WF & WA).
      exists (L5.BDyn 8 p), wr1. split. reflexivity. split. intros cx' p' E; exact E. split. intros; reflexivity.
      split. { eapply big_at_agree1. 4: exact OX. 2: unfold X; flia. 2: unfold X; flia. intros i Hi. apply KEEP1. unfold X in Hi; clear - Hi SHI SLO; lia.
               { rewrite Erd. cbn [L5.bo_data L5.bo_st]. unfold X in Hi. clear - Hi P5 SLO' Hnl Hl. lia. }
               { destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)]. unfold X, Q in *; clear - Hi Qn Hln; lia. unfold X in Hi; clear - Qhi Hi Hln Hnl SLO'; lia. }
               unfold X, Q in *; clear - Hi; lia. unfold X, Q in *; clear - Hi; lia. }
      split. exact WL. split. exact WF. exact WA. }
  destruct RST1 as (rst1 & wr1 & RB1 & RD1 & RD1' & OX1 & OLX1).
  (* [comment removed for export] *)
  assert (STQ1: exists stq1, blocks_ofst stq1 = blocks_ofst stq /\ (forall cq p, stq1 = L5.BDyn cq p -> stq = L5.BDyn cq p) /\ (forall q0 q1, stq = L5.BInl q0 q1 -> exists q0' q1', stq1 = L5.BInl q0' q1')
            /\ L5.big_at RSEGS M1 Q (L5.BO fq nq stq1)).
  { pose proof OQ as (Ob0 & Obf & Ob8 & ObS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Ob0, Obf, Ob8, ObS.
    destruct stq as [v0 v1|cq p].
    - destruct ObS as (Tb & _ & _ & Hle & _).
      destruct (BDU.defined_word M1 (Q + 16) ltac:(eapply L5.defined_sub; [exact SCR1 | unfold Q; clear; lia | unfold Q; clear; lia]) ltac:(unfold Q; flia) ltac:(unfold Q; flia)) as (v0' & R0' & U0').
      destruct (BDU.defined_word M1 (Q + 24) ltac:(eapply L5.defined_sub; [exact SCR1 | unfold Q; clear; lia | unfold Q; clear; lia]) ltac:(unfold Q; flia) ltac:(unfold Q; flia)) as (v1' & R1' & U1').
      exists (L5.BInl v0' v1'). split. reflexivity. split. intros cq p E; discriminate E. split. intros q0 q1 _; eexists _, _; reflexivity.
      unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Ob0. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia. }
      split. exact Obf. split. { eapply u64_at_agree1. 4: exact Ob8. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia. }
      split. exact Tb. split. exact U0'. split. exact U1'. split. exact Hle. split. exact R0'. exact R1'.
    - destruct (QDYN cq p eq_refl) as [-> FBq]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBq) as (P1 & P2 & P3 & _ & P5).
      exists (L5.BDyn 8 p). split. reflexivity. split. intros cq' p' E; exact E. split. intros q0 q1 E; discriminate E.
      eapply big_at_agree1. 4: exact OQ. 2: unfold Q; flia. 2: unfold Q; flia. intros i Hi. apply KEEP1. unfold Q in Hi; clear - Hi SHI SLO; lia.
      { destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)]. unfold X, Q in *; clear - Hi Rn; lia. unfold Q in Hi; clear - Rhi Rn Hi SLO'; lia. }
      { rewrite Eqd. cbn [L5.bo_data L5.bo_st]. unfold Q in Hi. clear - Hi P5 SLO' Hnl Hln. lia. }
      unfold Q in *; clear - Hi; lia. unfold Q in *; clear - Hi; lia. }
  destruct STQ1 as (stq1 & QB1 & QD1 & QI1 & OQ1).
  assert (LBceil0: forall b, In b LB -> fst b + snd b <= hl_ceil L). { intros b Hb. apply LBceil. apply LBcI. exact Hb. }
  assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  (* [comment removed for export] *)
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG'; clear; lia. exact (proj1 SPT). 2: exact MG1.
    assert (CASES: forall a, 0 <= a < 2 ^ 64 ->
       (remd <= a < remd + 8 * (Z.of_nat n + 1)) \/ (quotd <= a < quotd + 8 * (Z.of_nat n - Z.of_nat l)) \/ (Q - 416 <= a < Q) \/
       (~ (remd <= a < remd + 8 * (Z.of_nat n + 1)) /\ ~ (quotd <= a < quotd + 8 * (Z.of_nat n - Z.of_nat l)) /\ ~ (Q - 312 <= a < Q - 312 + 8) /\ ~ (Q - 416 <= a < Q - 416 + 64))).
    { intros a Ha. clear - Ha. lia. }
    intros a Ha. destruct (CASES a Ha) as [C|[C|[C|(C1 & C2 & C3 & C4)]]].
    - destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)]. right; left; unfold X in C; clear - C Rn SLO' SHI'; lia. right; right. exists (remd, 64). split. exact RIn. cbn; clear - C Rn; lia.
    - destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)]. right; left; unfold Q in C; clear - C Qn Hln SLO' SHI'; lia. right; right. exists (quotd, 64). split. exact QIn. cbn; clear - C Hln Hnl; lia.
    - right; left; unfold Q in C; clear - C SLO' SHI'; lia.
    - left. apply KEEP1; assumption. }
  (* [comment removed for export] *)
  assert (HP1: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M1).
  { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M1 S SCR_OPMOD [(X, 32)]). exact HP.
    - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M1
                (fun a => (remd <= a < remd + 8 * (Z.of_nat n + 1)) \/ (quotd <= a < quotd + 8 * (Z.of_nat n - Z.of_nat l)) \/ (Q - 312 <= a < Q - 312 + 8) \/ (Q - 416 <= a < Q - 416 + 64))).
      + intros a Ha Hn'. apply KEEP1. exact Ha. all: intros C; apply Hn'. left; exact C. right; left; exact C. right; right; left; exact C. right; right; right; exact C.
      + intros a KA [C|[C|[C|C]]].
        * pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)].
          { apply (L5HP.outside_in _ _ X 32 OW). cbn. left; reflexivity. clear - C Rn; lia. }
          pose proof (LBdef _ _ _ _ HH remd 64 RIn) as (_ & (_ & Rimg) & _ & _).
          refine (L5C.kept_not_fresh L LB S SCR_OPMOD [(X, 32)] a remd 64 KA _ Rimg Rhi LBceil0 _). { intros b Hb. apply RBA. rewrite !in_app_iff. right; right; exact Hb. } clear - C Rn; lia.
        * destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)].
          { refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA LBceil0 CEILS _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. unfold Q in C. clear - C Qn Hln; lia. }
          pose proof (LBdef _ _ _ _ HH quotd 64 QIn) as (_ & (_ & Qimg) & _ & _).
          refine (L5C.kept_not_fresh L LB S SCR_OPMOD [(X, 32)] a quotd 64 KA _ Qimg Qhi LBceil0 _). { intros b Hb. apply QBA. rewrite !in_app_iff. right; right; right; exact Hb. } clear - C Hln Hnl; lia.
        * refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA LBceil0 CEILS _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia.
        * refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA LBceil0 CEILS _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia.
      + rewrite SCR_OPMOD_val. exact SCR1.
      + exact MG1.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - exact CEILS. - clear - SHI; lia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - exact (proj1 SPT). }
  assert (IC1: L5.img_clear M1 0x10000 0x20000).
  { intros i Hi. rewrite KEEP1. apply IC; exact Hi. clear - Hi; lia.
    - destruct RMW as [(-> & Rn)|(RB & RIn & Rhi & Rn & RBA)]. unfold X; clear - Hi SLO; lia.
      pose proof (LBdef _ _ _ _ HH remd 64 RIn) as (_ & (_ & Rimg) & _ & _). rewrite IMG', IMGLO' in Rimg. clear - Hi Rimg Rn; lia.
    - destruct QDW as [(-> & Qn)|(QB & QIn & Qhi & QBA)]. unfold Q; clear - Hi SLO Hln; lia.
      pose proof (LBdef _ _ _ _ HH quotd 64 QIn) as (_ & (_ & Qimg) & _ & _). rewrite IMG', IMGLO' in Qimg. clear - Hi Qimg Hln Hnl; lia.
    - unfold Q; clear - Hi SLO; lia. - unfold Q; clear - Hi SLO; lia. }
  (* [comment removed for export] *)
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  apply (KT fx1 R1 M1 model crc c sd qneg n fq nq stq1 fxx rst1 wr1 fn cn pn fd cd pd fn0 fd0).
  - rewrite A2. unfold spd, Q. f_equal. clear; lia.
  - rewrite (K1 3%nat) by inl. exact H3.
  - rewrite (K1 4%nat) by inl. exact H4.
  - rewrite (K1 8%nat) by inl. exact H8.
  - rewrite (K1 9%nat) by inl. exact H9.
  - rewrite (K1 18%nat) by inl. exact H18.
  - exact MBV.
  - rewrite QB1, RB1. exact HH1.
  - exact CRK. - exact CRB.
  - rewrite SCR_OPMOD_val. exact SCR1.
  - exact IC1.
  - eapply top_frame_kept. 4: exact TF. intros i Hi. apply KC; unfold X, Q; clear - Hi SLO SLO' SHI; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply o1_saves_kept. 4: exact SAV. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply local_obj_kept. 4: exact LO0. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - exact F0b.
  - eapply local_obj_kept. 4: exact LO1. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - exact F1b.
  - eapply local_obj_kept. 4: exact LO2. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - intros T. destruct (FRESH2 T) as [Ec FB]. split. exact Ec. destruct FB as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - eapply local_obj_kept. 4: exact LO3. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - intros T. destruct (FRESH3 T) as [Ec FB]. split. exact Ec. destruct FB as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - eapply u32_at_agree1. 4: exact C348. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - exact Hc63.
  - eapply u64_at_agree1. 4: exact C400. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply u64_at_agree1. 4: exact C384. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply u64_at_agree1. 4: exact C392. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - exact Hq01.
  - eapply u64_at_agree1. 4: exact C408. intros i Hi. apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - subst sd. destruct sec; [right | left]; reflexivity.
  - exact OQ1.
  - rewrite NQ. clear - Hnl; lia.
  - intros cq p E. destruct (QDYN cq p (QD1 _ _ E)) as [Ec FB]. split. exact Ec. rewrite RB1. destruct FB as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - exact OX1.
  - exact NEGX.
  - exact OLX1.
  - exact DX1.
  - intros cx p E. destruct (XDYN cx p (RD1 _ _ E)) as [Ec FB]. split. exact Ec. destruct FB as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - intros E. assert (SEC: sec = true). { subst sd. destruct sec. reflexivity. discriminate E. }
    destruct (SD1 SEC) as ((qx & Erst) & (q0 & q1 & Estq) & Tn & Td). destruct (SECF SEC) as (_ & L3 & _).
    split. exists qx. rewrite (RD1' _ _ Erst). exact Erst. split. subst l. clear - Hln Hnl L3. lia. split. exact (QI1 _ _ Estq). split. exact Tn. exact Td.
  - eapply big_at_agree1. 4: exact OBB. intros i Hi. apply KC; subst bo; unfold X, Q; clear - Hi SLO SLO' SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
  - apply OLB_any.
  - fold nb. clear - NB12; lia.
  - intros cap q E. rewrite STB in E. discriminate E.
  - exact HP1.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G10 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (fq : Z) (nq : nat) (stq : L5.bstore) (fxx qx : Z) (fn cn pn fd cd pd fn0 fd0 denomd : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := blocks_ofst stq ++ [(qx, 64)] ++ BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l + 1) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat l) -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat n1) ->
  (* [comment removed for export] *)
  L5.u64_at RSEGS M (Q - 304) qx -> L5.u64_at RSEGS M (Q - 296) (Z.of_nat n1 + 1) ->
  L5.u64_at RSEGS M (Q - 152) denomd -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat l + 1) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - 4 * hl_k_per_malloc L <= fst crc -> snd cr - 4 * (64 + hl_b_overhead L) <= snd crc ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  late M fn cn pn fd cd pd fn0 fd0 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Q (L5.BO fq nq stq) -> nq = (n1 - l)%nat ->
  (forall cq p, stq = L5.BDyn cq p -> cq = 8 /\ L5C.fresh_block L ([(qx, 64)] ++ BN ++ BD ++ LB) M p 64) ->
  (match stq with L5.BInl _ _ => (nq <= 2)%nat | L5.BDyn _ _ => True end) ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M X (L5.BO fxx (Datatypes.S n1) (L5.BDyn 8 qx)) -> Z.testbit fxx 1 = false -> L5.defined M X 32 ->
  L5C.fresh_block L (BN ++ BD ++ LB) M qx 64 ->
  (* [comment removed for export] *)
  denomd = (if Z.testbit fd 0 then pd else S - 184) -> (Z.testbit fd 0 = false -> (l1 <= 2)%nat) -> L5.defined M denomd (8 * Z.of_nat l1) ->
  L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d ->
  (* [comment removed for export] *)
  (sec = true -> (exists q0 q1, stq = L5.BInl q0 q1) /\ Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x228f4 M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H18 H21 H22 H24 VR VRS VD VS MBV HH CRK CRB SCR IC LT OQ NQ QDYN QFIT OX NEGX DX FBX Edd DINL DDEF Cd SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF as (L13 & N24 & LN & NL2 & _ & _ & _ & _ & DR & SECF & _). pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia).
  pose proof LT as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C400 & C384 & C392 & C408).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (WFR: L5.writable RSEGS M (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia. }
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AQ8: Q mod 8 = 0). { apply mod16_mod8. exact AQ16. }
  pose proof OQ as (Qb0 & Qf & Q8 & QS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qb0, Qf, Q8, QS.
  pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBX) as (PX1 & PX2 & PX3 & _ & PX5).
  assert (DNW: (denomd = S - 184 /\ (l1 <= 2)%nat) \/ (4096 <= denomd /\ denomd + 64 <= hl_ceil L)).
  { rewrite Edd. destruct (Z.testbit fd 0). right. destruct (FR3 eq_refl) as [_ FB]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (P1 & P2 & P3 & _ & P5). split. exact P1. exact P5.
    left. split. reflexivity. exact (DINL eq_refl). }
  assert (NQ1: (1 <= nq)%nat) by (rewrite NQ; subst l; clear - LN L13; lia).
  assert (NQ3: (nq <= 3)%nat) by (rewrite NQ; subst l; clear - NL2 L13 LN; lia).
  assert (Q8': L5.u64_at RSEGS M (Q + 8) (Z.of_nat nq - 1 + 1)). { replace (Z.of_nat nq - 1 + 1) with (Z.of_nat nq) by (clear; lia). exact Q8. }
  (* [comment removed for export] *)
  assert (JOIN: exists fx1 R1 M1, msteps RSEGS (st fx R 0x228f4 M) (st fx1 R1 PRE M1)
            /\ (forall x, In x [2; 3; 4; 8; 9; 18; 21; 22; 24]%nat -> getr R1 (reg x) = getr R (reg x))
            /\ getr R1 (reg 23) = Z_to_bv 64 (Z.of_nat n1)
            /\ mem_grows M M1 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 232 <= i < Q - 232 + 16) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ L5.u64_at RSEGS M1 (Q - 232) (L5.bo_data Q (L5.BO fq nq stq))).
  { destruct stq as [q0 q1|cq p]; cbn [L5.bo_data L5.bo_st].
    - destruct QS as (QT & _).
      pose proof (d7ug10i_conc fx R M (fun j => match j with 2%nat => Q | 35%nat => Q | 65%nat => Z.of_nat n1 | 69%nat => fq | 70%nat => Z.of_nat nq - 1 | _ => 0 end)) as P. cbn beta iota in P.
      destruct (P ltac:(unfold Q; flia) ltac:(unfold Q; flia) ltac:(clear - N24; lia) ltac:(clear - Qf; lia) ltac:(clear - QFIT NQ1; lia)
                  ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H9 H24
                  ltac:(unfold Q; flia) AQ16 WFR ltac:(unfold Q; flia) AQ8 ltac:(left; unfold Q; clear; lia) Qb0 ltac:(clear - Qf; lia) QT Q8' ltac:(clear - QFIT NQ1; lia))
        as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & _ & _ & A23 & _ & C1)). clear P.
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. exact A23. split. exact MG. split. exact FRZ. exact C1.
    - destruct QS as (QT & Q16 & Q24 & _). destruct (QDYN cq p eq_refl) as [-> FBq]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBq) as (P1 & P2 & P3 & _ & P5).
      pose proof (d7ug10d_conc fx R M (fun j => match j with 2%nat => Q | 35%nat => Q | 65%nat => Z.of_nat n1 | 68%nat => p | 69%nat => fq | 70%nat => Z.of_nat nq - 1 | _ => 0 end)) as P. cbn beta iota in P.
      destruct (P ltac:(unfold Q; flia) ltac:(unfold Q; flia) ltac:(clear - N24; lia) ltac:(clear - P1 P5 SPT; lia) ltac:(clear - Qf; lia) ltac:(clear - NQ1 NQ3; lia)
                  ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H9 H24
                  ltac:(unfold Q; flia) AQ16 WFR ltac:(unfold Q; flia) AQ8 ltac:(left; unfold Q; clear; lia) Qb0 ltac:(clear - Qf; lia) QT Q24 Q8'
                  ltac:(clear - NQ1 NQ3; lia) ltac:(clear - P1 P5 SPT; lia))
        as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & _ & _ & A23 & _ & C1)). clear P.
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. exact A23. split. exact MG. split. exact FRZ. exact C1. }
  destruct JOIN as (fx1 & R1 & M1 & MS1 & K1 & A23 & MG1 & KA & VQ1).
  assert (KF: forall i, S - 480 <= i < S + 240 -> ~ (S - 296 <= i < S - 280) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn'. apply KA. clear - Hi SLO SHI; lia. unfold Q. clear - Hn'; lia. }
  assert (KB: forall i, 0 <= i < 2 ^ 64 -> i < hl_ceil L -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hc. apply KA. exact Hi. unfold Q, hl_ceil in *. clear - Hc SLO'; lia. }
  assert (SCR1: L5.defined M1 (S - 10240) 10240) by (eapply L5.defined_grows; [exact MG1 | exact SCR']).
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG'; clear; lia. exact (proj1 SPT). 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (Q - 232)) as [Y1|Y1]. left; apply KA; [exact Ha | clear - Y1; lia].
    destruct (Z_lt_le_dec a (Q - 232 + 16)) as [Y2|Y2]. right; left; unfold Q, hl_ceil in *; clear - Y1 Y2 SLO' SHI'; lia. left; apply KA; [exact Ha | clear - Y2; lia]. }
  assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. unfold hl_ceil. lia. }
  assert (LBceil0: forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros [A m] Hb. assert (Hb': In (A, m) LBc). { subst LBc. rewrite !in_app_iff. right; right; right; right; exact Hb. }
    pose proof (LBdef _ _ _ _ HH A m Hb') as (_ & _ & Ahi & _). exact Ahi. }
  assert (HP1: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M1).
  { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M1 S SCR_OPMOD [(X, 32)]). exact HP.
    - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M1 (fun a => Q - 232 <= a < Q - 232 + 16)).
      + intros a Ha Hn'. apply KA. exact Ha. exact Hn'.
      + intros a KA' C. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' LBceil0 CEILS _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia.
      + rewrite SCR_OPMOD_val. exact SCR1.
      + exact MG1.
    - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEILS. - clear - SHI; lia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - exact (proj1 SPT). }
  assert (IC1: L5.img_clear M1 0x10000 0x20000). { intros i Hi. rewrite KA. apply IC; exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  apply (stage_L fx1 R1 M1 model crc n1 fq nq stq fxx (L5.BDyn 8 qx) [] fn cn pn fd cd pd fn0 fd0 qx (L5.bo_data Q (L5.BO fq nq stq)) denomd).
  all: try (rewrite (K1 _) by inl; assumption).
  - exact A23.
  - eapply u64_at_agree1. 4: exact VR. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
  - exact VQ1.
  - eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
  - eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
  - subst l. clear - LN L13; lia. - subst l. clear - NL2 L13 LN; lia.
  - exact MBV.
  - cbn [blocks_ofst]. exact HH1.
  - exact CRK. - exact CRB. - rewrite SCR_OPMOD_val. exact SCR1. - exact IC1.
  - eapply top_frame_kept. 4: exact TF. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply o1_saves_kept. 4: exact SAV. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply local_obj_kept. 4: exact LO0. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - exact F0b.
  - eapply local_obj_kept. 4: exact LO1. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - exact F1b.
  - eapply local_obj_kept. 4: exact LO2. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - intros T. destruct (FR2 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - eapply local_obj_kept. 4: exact LO3. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - intros T. destruct (FR3 T) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - eapply u32_at_agree1. 4: exact C348. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply u64_at_agree1. 4: exact C400. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply u64_at_agree1. 4: exact C384. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply u64_at_agree1. 4: exact C392. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply u64_at_agree1. 4: exact C408. intros i Hi; apply KF; clear - Hi; lia. clear - SLO; lia. clear - SHI; lia.
  - eapply big_at_agree1. 4: exact OQ. intros i Hi; apply KF; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
  - exact NQ.
  - intros cq p E. destruct (QDYN cq p E) as [Ec (B1' & B2' & B3')]. split. exact Ec. cbn [blocks_ofst]. split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - reflexivity. - exact QFIT.
  - eapply big_at_agree1. 4: exact OX. intros i Hi; apply KF; unfold X in Hi; clear - Hi; lia. unfold X; flia. unfold X; flia.
  - exact NEGX.
  - eapply L5.defined_grows. exact MG1. exact DX.
  - intros cx p E. injection E. intros <- <-. split. reflexivity. destruct FBX as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'.
  - reflexivity. - cbv iota. exact I.
  - exact Edd. - exact DINL.
  - eapply L5.defined_grows. exact MG1. exact DDEF.
  - eapply u64_at_agree1. 4: exact Cd. { intros i Hi. destruct DNW as [(-> & _)|(Dlo & Dhi)]. apply KF; clear - Hi Hl; lia. apply KB. clear - Hi Dlo Dhi Hl SPT; unfold hl_ceil in *; lia. clear - Hi Dhi Hl; lia. }
    destruct DNW as [(-> & _)|(Dlo & Dhi)]. clear - SLO Hl; lia. clear - Dlo Hl; lia. destruct DNW as [(-> & _)|(Dlo & Dhi)]. clear - SHI Hl; lia. unfold hl_ceil in Dhi. clear - Dhi Hl SPT; lia.
  - intros SEC. destruct (SD1 SEC) as (EQ & Tn & Td). split. eexists; reflexivity. split. exact EQ. split. exact Tn. exact Td.
  - eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KF; subst bo; clear - Hi; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
  - exact HP1.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G9 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (fq : Z) (nqo : nat) (q0 q1 fxx qx : Z) (fn cn pn fd cd pd fn0 fd0 denomd : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := [(qx, 64)] ++ BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l + 1) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat l) -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat n1) ->
  (* [comment removed for export] *)
  L5.u64_at RSEGS M (Q - 224) (Z.of_nat nqo) ->
  L5.u64_at RSEGS M (Q - 152) denomd -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat l + 1) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - 3 * hl_k_per_malloc L <= fst crc -> snd cr - 3 * (64 + hl_b_overhead L) <= snd crc ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  late M fn cn pn fd cd pd fn0 fd0 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Q (L5.BO fq nqo (L5.BInl q0 q1)) -> (nqo + l + 1 = n1)%nat ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M X (L5.BO fxx (Datatypes.S n1) (L5.BDyn 8 qx)) -> Z.testbit fxx 1 = false -> L5.defined M X 32 ->
  L5C.fresh_block L (BN ++ BD ++ LB) M qx 64 ->
  (* [comment removed for export] *)
  denomd = (if Z.testbit fd 0 then pd else S - 184) -> (Z.testbit fd 0 = false -> (l1 <= 2)%nat) -> L5.defined M denomd (8 * Z.of_nat l1) ->
  L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d ->
  (sec = true -> Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x228c0 M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H18 H21 H22 H24 VQS VD VS MBV HH CRK CRB SCR IC LT OQ NQ OX NEGX DX FBX Edd DINL DDEF Cd SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF as (L13 & N24 & LN & NL2 & _ & _ & _ & _ & DR & SECF & _). pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia). assert (Hq2: (nqo <= 2)%nat) by (subst l; clear - NQ NL2 L13; lia).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AQ8: Q mod 8 = 0). { apply mod16_mod8. exact AQ16. }
  assert (AX8: X mod 8 = 0). { unfold X. replace (S + 64) with (S + 8 * 8) by (clear; lia). apply al8. exact A16. }
  pose proof OX as (Xb0 & Xf & X8 & XT & X16 & X24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Xb0, Xf, X8, XT, X16, X24.
  pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBX) as (PX1 & PX2 & PX3 & _ & PX5).
  assert (WFR: L5.writable RSEGS M (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia. }
  assert (X8': L5.u64_at RSEGS M (X + 8) (Z.of_nat n1 + 1)). { replace (Z.of_nat n1 + 1) with (Z.of_nat (Datatypes.S n1)) by (clear; lia). exact X8. }
  assert (DNW: (denomd = S - 184 /\ (l1 <= 2)%nat) \/ (4096 <= denomd /\ denomd + 64 <= hl_ceil L)).
  { rewrite Edd. pose proof LT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR3 & _). destruct (Z.testbit fd 0). right. destruct (FR3 eq_refl) as [_ FB]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (P1 & P2 & P3 & _ & P5). split. exact P1. exact P5.
    left. split. reflexivity. exact (DINL eq_refl). }
  (* [comment removed for export] *)
  pose proof (d5ug9_conc fx R M (fun j => match j with 2%nat => Q | 35%nat => Q | 36%nat => X | 65%nat => Z.of_nat n1 | 70%nat => Z.of_nat nqo | 71%nat => fxx | 72%nat => qx | _ => 0 end)) as P.
  cbn beta iota in P.
  destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold X; clear - SLO SHI; lia) ltac:(clear - N24; lia) ltac:(clear - Hq2; lia) ltac:(clear - Xf; lia) ltac:(clear - PX1 PX5 SPT; lia)
              ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H8 H9
              ltac:(unfold Q; clear - SLO SHI; lia) AQ16 WFR VQS ltac:(unfold X; clear - SLO SHI; lia) AX8 ltac:(left; unfold X, Q; clear; lia) Xb0 ltac:(clear - Xf; lia) XT X24 X8'
              ltac:(clear - Hq2; lia) ltac:(clear - N24; lia) ltac:(clear - PX1 PX5 SPT; lia))
    as (fx1 & R1 & M1 & MG1 & FR1 & FRZ & (MS1 & K1 & A1 & A10 & A11 & A12 & VRS1 & VR1)). clear P.
  (* [comment removed for export] *)
  assert (KF1: forall i, S - 480 <= i < S + 240 -> ~ (S - 368 <= i < S - 352) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn'. apply FRZ. clear - Hi SLO SHI; lia. unfold Q. clear - Hn'; lia. }
  assert (KB1: forall i, 0 <= i < 2 ^ 64 -> i < hl_ceil L -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hc. apply FRZ. exact Hi. unfold Q, hl_ceil in *. clear - Hc SLO'; lia. }
  assert (CEILS0: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. unfold hl_ceil. lia. }
  assert (LBceil0: forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros [A m] Hb. assert (Hb': In (A, m) LBc). { subst LBc. rewrite !in_app_iff. right; right; right; exact Hb. }
    pose proof (LBdef _ _ _ _ HH A m Hb') as (_ & _ & Ahi & _). exact Ahi. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG'; clear; lia. exact (proj1 SPT). 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (Q - 304)) as [Y1|Y1]. left; apply FRZ; [exact Ha | clear - Y1; lia].
    destruct (Z_lt_le_dec a (Q - 304 + 16)) as [Y2|Y2]. right; left; unfold Q, hl_ceil in *; clear - Y1 Y2 SLO' SHI'; lia. left; apply FRZ; [exact Ha | clear - Y2; lia]. }
  assert (HP1: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M1).
  { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M1 S SCR_OPMOD [(X, 32)]). exact HP.
    - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M1 (fun a => Q - 304 <= a < Q - 304 + 16)).
      + intros a Ha Hn'. apply FRZ. exact Ha. exact Hn'.
      + intros a KA' C. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' LBceil0 CEILS0 _ _). rewrite IMG'; clear - SPT; lia. rewrite SCR_OPMOD_val. unfold Q in C. clear - C; lia.
      + rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR'.
      + exact MG1.
    - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEILS0. - clear - SHI; lia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - exact (proj1 SPT). }
  assert (SCR1: L5.defined M1 (S - SCR_OPMOD) SCR_OPMOD) by (eapply L5.defined_grows; [exact MG1 | exact SCR]).
  assert (IC1: L5.img_clear M1 0x10000 0x20000). { intros i Hi. rewrite FRZ. apply IC; exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia. }
  assert (LT1: late M1 fn cn pn fd cd pd fn0 fd0).
  { eapply late_kept. 4: exact LT. intros i Hi; apply KF1; clear - Hi; lia. all: intros _ D; eapply L5.defined_grows; [exact MG1 | exact D]. }
  assert (OQ1: L5.big_at RSEGS M1 Q (L5.BO fq nqo (L5.BInl q0 q1))). { eapply big_at_agree1. 4: exact OQ. intros i Hi; apply KF1; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia. }
  assert (OX1: L5.big_at RSEGS M1 X (L5.BO fxx (Datatypes.S n1) (L5.BDyn 8 qx))). { eapply big_at_agree1. 4: exact OX. intros i Hi; apply KF1; unfold X in Hi; clear - Hi; lia. unfold X; flia. unfold X; flia. }
  assert (DX1: L5.defined M1 X 32) by (eapply L5.defined_grows; [exact MG1 | exact DX]).
  assert (FBX1: L5C.fresh_block L (BN ++ BD ++ LB) M1 qx 64). { destruct FBX as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'. }
  assert (DDEF1: L5.defined M1 denomd (8 * Z.of_nat l1)) by (eapply L5.defined_grows; [exact MG1 | exact DDEF]).
  assert (Cd1: L5.u64_at RSEGS M1 (denomd + 8 * Z.of_nat l) d).
  { eapply u64_at_agree1. 4: exact Cd. { intros i Hi. destruct DNW as [(-> & _)|(Dlo & Dhi)]. apply KF1; clear - Hi Hl; lia. apply KB1. clear - Hi Dlo Dhi Hl SPT; unfold hl_ceil in *; lia. clear - Hi Dhi Hl; lia. }
    destruct DNW as [(-> & _)|(Dlo & Dhi)]. clear - SLO Hl; lia. clear - Dlo Hl; lia. destruct DNW as [(-> & _)|(Dlo & Dhi)]. clear - SHI Hl; lia. unfold hl_ceil in Dhi. clear - Dhi Hl SPT; lia. }
  assert (OBB1: L5.big_at RSEGS M1 bo bb). { eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KF1; subst bo; clear - Hi; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia. }
  assert (VD1: L5.u64_at RSEGS M1 (Q - 152) denomd). { eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KF1; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia. }
  assert (VS1: L5.u64_at RSEGS M1 (Q - 144) (Z.of_nat l + 1)). { eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KF1; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  clear Xb0 Xf X8 XT X16 X24 X8' WFR HH HP SCR SCR' IC LT OQ OX DX FBX DDEF Cd OBB VD VS VQS MS1 MG1 FR1 FRZ KF1 KB1. clear M.
  rename M1 into M, HH1 into HH, HP1 into HP, SCR1 into SCR, IC1 into IC, LT1 into LT, OQ1 into OQ, OX1 into OX, DX1 into DX, FBX1 into FBX, DDEF1 into DDEF, Cd1 into Cd, OBB1 into OBB.
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  pose proof LT as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C400 & C384 & C392 & C408).
  pose proof OX as (Xb0 & Xf & X8 & XT & X16 & X24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Xb0, Xf, X8, XT, X16, X24.
  pose proof OQ as (Qb0 & Qf & Q8 & QT & Q16 & Q24 & _ & Rq0 & Rq1). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qb0, Qf, Q8, QT, Q16, Q24, Rq0, Rq1.
  assert (DNB: 4096 <= denomd + 8 * Z.of_nat l /\ denomd + 8 * Z.of_nat l + 8 <= 2 ^ 47).
  { destruct DNW as [(-> & _)|(Dlo & Dhi)]. split. clear - SLO; lia. clear - SHI Hl; lia. split. clear - Dlo; lia. unfold hl_ceil in Dhi. clear - Dhi Hl SPT; lia. }
  destruct DNB as (DNlo & DNhi).
  (* [comment removed for export] *)
  replace (Z.of_nat nqo + 1) with (Z.of_nat (nqo + 1)) in A11 by (clear; lia).
  unfold cfg. eapply (RESIZE fx1 R1 M model K LBc crc Q spd 0x228f4 (nqo + 1)%nat (L5.BO fq nqo (L5.BInl q0 q1)) (firstn nqo [q0; q1]) HH MOK HK0 A10 A11).
  - clear - Hq2; lia.
  - intros T. exfalso. change (Z.testbit fq 0 = true) in T. rewrite QT in T. discriminate T.
  - intros _ _. replace (round_up (Z.of_nat (nqo + 1))) with 8 by (unfold round_up; clear - Hq2; destruct nqo as [|[|[|]]]; cbn; lia). apply (credit_next crc 3 CRK CRB). clear; lia.
  - exact A1.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; clear - SHI'; lia. split. exact SPT. unfold spd. rewrite RESIZE_SCR_val. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia.
  - exact OQ.
  - split. { cbn [L5.bo_len]. rewrite length_firstn. cbn [length]. clear - Hq2; lia. } split. { destruct nqo as [|[|[|]]]; cbn; repeat constructor; clear - Rq0 Rq1 Hq2; lia. } cbn [L5.bo_st L5.bo_len]. reflexivity.
  - exact AQ8.
  - unfold spd, Q; clear; lia.
  - unfold Q; clear - SHI'; lia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
  - intros cap q E. discriminate E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. destruct POST as (RP2 & GP).
    assert (E2r: forall i v, In i cs_all -> getr R1 (reg i) = v -> getr R2 (reg i) = v). { intros i v Hi Hv. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. exact Hv. }
    assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
    assert (LBcI: forall b, In b LB -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; right; exact Hb. }
    assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
    assert (INn: Z.testbit fn 0 = true -> In (pn, 64) LBc).
    { intros T. destruct (FR2 T) as [Ec _]. subst LBc BN. rewrite T, Ec. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
    assert (INd: Z.testbit fd 0 = true -> In (pd, 64) LBc).
    { intros T. destruct (FR3 T) as [Ec _]. subst LBc BD. rewrite T, Ec. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
    assert (SUB2: forall b, In b LBc -> In b LB2). { intros b Hb. destruct g as [|A cap]. destruct GP as (_ & -> & _). exact Hb. destruct GP as (_ & _ & _ & -> & _). right. exact Hb. }
    (* [comment removed for export] *)
    assert (COMMON: forall W, L5C.hpres L LBc spd RESIZE_SCR W M M2 -> (forall a, L5.outside [(Q, 32)] a -> L5.outside W a) ->
              (forall a, spd <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
              /\ L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M2 /\ L5.defined M2 (S - SCR_OPMOD) SCR_OPMOD /\ L5.img_clear M2 0x10000 0x20000
              /\ late M2 fn cn pn fd cd pd fn0 fd0 /\ (forall i, denomd <= i < denomd + 8 * Z.of_nat l1 -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i))).
    { intros W HPW HW.
      assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hn. apply (kept_above M M2 LBc spd RESIZE_SCR W a HPW). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). exact Ha.
        apply HW. apply outside1. exact Hn. }
      split. exact KA. split.
      - eapply (L5HP.hpres_trans L LB LBc S SCR_OPMOD [(X, 32)] M0 M M2 spd RESIZE_SCR W). exact HP. exact HPW.
        + intros a KA'. pose proof (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' ltac:(intros b Hb; apply LBceil; apply LBcI; exact Hb) CEILS ltac:(rewrite IMG'; clear - SPT; lia)) as NS.
          eapply L5HP.kept_mono. exact KA'. exact LBcI. unfold spd; rewrite SCR_OPMOD_val, RESIZE_SCR_val; clear; lia. unfold spd; clear; lia.
          intros _. apply HW. apply outside1. rewrite SCR_OPMOD_val in NS. unfold Q. clear - NS. lia.
        + exact LBcI. + exact CEILS. + clear - SHI; lia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + exact (proj1 SPT).
      - split. { rewrite SCR_OPMOD_val. eapply SCR_kept. exact HPW. rewrite RESIZE_SCR_val; clear; lia. exact SCR'. }
        split. { eapply IC_kept. exact HPW. 2: exact IC. intros a Ha. apply HW. apply outside1. unfold Q; clear - Ha SLO; lia. }
        split. { eapply late_kept. 4: exact LT.
          + intros i Hi. apply KA. unfold spd; clear - Hi SLO SHI; lia. unfold Q; clear - Hi; lia.
          + intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pn 64). apply SUB2. apply INn. exact T.
          + intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pd 64). apply SUB2. apply INd. exact T. }
        intros i Hi. rewrite Edd in Hi. destruct (Z.testbit fd 0) eqn:Tfd.
        { pose proof (LBceil (pd, 64) (INd eq_refl)) as PC. cbn in PC.
          apply (kept_inblock M M2 LBc crc _ spd RESIZE_SCR _ pd 64 i HH HPW). apply INd; reflexivity. clear - Hi L13; lia. exact SPT. apply HW. apply outside1. unfold Q; clear - Hi PC SLO' L13; lia. }
        apply KA. unfold spd; clear - Hi SLO SHI L13; lia. unfold Q; clear - Hi L13; lia. }
    assert (G10r: forall i v, In i cs_all -> getr R (reg i) = v -> In i KS_d5ug9 -> getr R2 (reg i) = v).
    { intros i v Hi Hv Hk. apply (E2r i v Hi). rewrite (K1 i Hk). exact Hv. }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct GP as (DYS & -> & -> & (st' & OQ2 & OL2 & SST) & HP2). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in OQ2, OL2, SST, HP2.
      assert (Hq1: (nqo + 1 <= 2)%nat). { destruct DYS as [T|T]. exfalso. change (Z.testbit fq 0 = true) in T. rewrite QT in T. discriminate T. exact T. }
      destruct st' as [q0' q1'|cq' p']. 2: destruct SST.
      destruct (COMMON _ HP2) as (KA & HP2' & SCR2 & IC2 & LT2 & KD).
      { intros a OW r [<-|[<-|[]]]; unfold L5.in_rng; cbn; specialize (OW (Q, 32) ltac:(left; reflexivity)); unfold L5.in_rng in OW; cbn in OW. exact OW. clear - OW Hq1. lia. }
      apply (stage_G10 fx2 R2 M2 model2 crc fq (nqo + 1)%nat (L5.BInl q0' q1') fxx qx fn cn pn fd cd pd fn0 fd0 denomd).
      all: try (eapply G10r; [inl | eassumption | inl]).
      * eapply u64_at_agree1. 4: exact VR1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VRS1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VD1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VS1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * cbn [blocks_ofst app]. exact HH2.
      * pose proof KPOS. clear - CRK H. lia. * pose proof BPOS. clear - CRB H. lia.
      * exact SCR2. * exact IC2. * exact LT2.
      * exact OQ2.
      * subst l. clear - NQ L13. lia.
      * intros cq p E. discriminate E.
      * exact Hq1.
      * eapply big_at_agree1. 4: exact OX. intros i Hi. apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
      * exact NEGX.
      * eapply (cdef_above M M2 LBc spd RESIZE_SCR _ X 32 HP2). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). unfold X, spd; clear; lia. unfold X; clear - SHI; lia. exact DX.
      * destruct FBX as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply proj1, (LBdef _ _ _ _ HH2 qx 64). subst LBc. left. reflexivity.
      * exact Edd. * exact DINL.
      * eapply defined_agree1. 2: exact DDEF. intros i Hi; apply KD; exact Hi.
      * eapply u64_at_agree1. 4: exact Cd. intros i Hi; apply KD; subst l; clear - Hi L13; lia. clear - DNlo; lia. clear - DNhi; lia.
      * intros SEC. split. eexists _, _; reflexivity. exact (SD1 SEC).
      * eapply big_at_agree1. 4: exact OBB. intros i Hi. apply KA; subst bo; unfold Q, spd in *; clear - Hi SLO SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
      * exact HP2'.
    + (* [comment removed for export] *)
      destruct GP as (DYF & N3 & Ecap & -> & -> & FB & OQ2 & OL2 & HP2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ2, OL2.
      replace (round_up (Z.of_nat (nqo + 1))) with 8 in Ecap by (unfold round_up; clear - N3 Hq2; replace (Z.of_nat (nqo + 1)) with 3 by lia; reflexivity). subst cap.
      destruct (COMMON _ HP2) as (KA & HP2' & SCR2 & IC2 & LT2 & KD). { intros a OW; exact OW. }
      pose proof (credit_step crc 3 CRK CRB) as [CRK' CRB'].
      apply (stage_G10 fx2 R2 M2 model2 (debit L crc (8 * 8)) (Z.lor fq 1) (nqo + 1)%nat (L5.BDyn 8 A) fxx qx fn cn pn fd cd pd fn0 fd0 denomd).
      all: try (eapply G10r; [inl | eassumption | inl]).
      * eapply u64_at_agree1. 4: exact VR1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VRS1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VD1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VS1. intros i Hi; apply KA; unfold Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * cbn [blocks_ofst app]. exact HH2.
      * exact CRK'. * exact CRB'.
      * exact SCR2. * exact IC2. * exact LT2.
      * exact OQ2.
      * subst l. clear - NQ L13. lia.
      * intros cq p E. injection E. intros <- <-. split. reflexivity. subst LBc. exact FB.
      * exact I.
      * eapply big_at_agree1. 4: exact OX. intros i Hi. apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
      * exact NEGX.
      * eapply (cdef_above M M2 LBc spd RESIZE_SCR _ X 32 HP2). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). unfold X, spd; clear; lia. unfold X; clear - SHI; lia. exact DX.
      * destruct FBX as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply proj1, (LBdef _ _ _ _ HH2 qx 64). right. subst LBc. left. reflexivity.
      * exact Edd. * exact DINL.
      * eapply defined_agree1. 2: exact DDEF. intros i Hi; apply KD; exact Hi.
      * eapply u64_at_agree1. 4: exact Cd. intros i Hi; apply KD; subst l; clear - Hi L13; lia. clear - DNlo; lia. clear - DNhi; lia.
      * intros SEC. exfalso. destruct (SECF SEC) as (_ & L3 & N3' & _). subst l. clear - NQ L3 N3' N3 N24. lia.
      * eapply big_at_agree1. 4: exact OBB. intros i Hi. apply KA; subst bo; unfold Q, spd in *; clear - Hi SLO SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia.
      * exact HP2'.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_GROW (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (j : Z)
      (fq : Z) (nqo : nat) (q0 q1 fxx : Z) (rst : L5.bstore) (wr : list Z) (fn cn pn fd cd pd fn0 fd0 denomd : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := blocks_ofst rst ++ BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l + 1) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat l) -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat n1) ->
  (* [comment removed for export] *)
  L5.u64_at RSEGS M (Q - 296) (Z.of_nat n1) -> L5.u64_at RSEGS M (Q - 224) (Z.of_nat nqo) ->
  L5.u64_at RSEGS M (Q - 152) denomd -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat l + 1) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - j * hl_k_per_malloc L <= fst crc -> snd cr - j * (64 + hl_b_overhead L) <= snd crc -> 0 <= j <= 3 ->
  (match rst with L5.BInl _ _ => j <= 2 | L5.BDyn _ _ => True end) ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  late M fn cn pn fd cd pd fn0 fd0 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Q (L5.BO fq nqo (L5.BInl q0 q1)) -> (nqo + l + 1 = n1)%nat ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M X (L5.BO fxx n1 rst) -> Z.testbit fxx 1 = false -> L5C.obj_limbs RSEGS M (L5.BO fxx n1 rst) wr -> L5.defined M X 32 ->
  (forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ L5C.fresh_block L (BN ++ BD ++ LB) M p 64) ->
  (* [comment removed for export] *)
  denomd = (if Z.testbit fd 0 then pd else S - 184) -> (Z.testbit fd 0 = false -> (l1 <= 2)%nat) -> L5.defined M denomd (8 * Z.of_nat l1) ->
  L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d ->
  (sec = true -> Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x228b0 M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H18 H21 H22 H24 VRS VQS VD VS MBV HH CRK CRB Hj JX SCR IC LT OQ NQ OX NEGX OLX DX XDYN Edd DINL DDEF Cd SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF as (L13 & N24 & LN & NL2 & _ & _ & _ & _ & DR & SECF & _). pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia).
  pose proof LT as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C400 & C384 & C392 & C408).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AX8: X mod 8 = 0). { unfold X. replace (S + 64) with (S + 8 * 8) by (clear; lia). apply al8. exact A16. }
  assert (WFR: L5.writable RSEGS M (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI SLO; lia. }
  pose proof OX as (Xb0 & Xf & X8 & XS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Xb0, Xf, X8, XS.
  assert (DNB: 4096 <= denomd + 8 * Z.of_nat l /\ denomd + 8 * Z.of_nat l + 8 <= 2 ^ 47).
  { rewrite Edd. destruct (Z.testbit fd 0) eqn:Tfd.
    - destruct (FR3 eq_refl) as [_ FBd]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & P2 & P3 & _ & P5). split. clear - P1; lia. clear - P5 Hl SPT; lia.
    - split. clear - SLO; lia. clear - SHI Hl; lia. }
  destruct DNB as (DNlo & DNhi).
  (* [comment removed for export] *)
  pose proof (d5ug8_conc fx R M (fun j => match j with 2%nat => Q | 36%nat => X | 65%nat => Z.of_nat n1 | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P ltac:(unfold Q; clear - SLO SHI; lia) ltac:(unfold X; clear - SLO SHI; lia) ltac:(clear - N24; lia)
              ltac:(rewrite H2; unfold spd, Q; f_equal; clear; lia) H8
              ltac:(unfold Q; clear - SLO SHI; lia) AQ16 WFR VRS ltac:(clear - N24; lia))
    as (fx1 & R1 & M1 & MG1 & FR1 & _ & (MS1 & K1 & A1 & A10 & A11)). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  replace (Z.of_nat n1 + 1) with (Z.of_nat (n1 + 1)) in A11 by (clear; lia).
  assert (LBcI: forall b, In b LB -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; right; exact Hb. }
  eapply (RESIZE fx1 R1 M model K LBc crc X spd 0x228c0 (n1 + 1)%nat (L5.BO fxx n1 rst) wr HH MOK HK0 A10 A11).
  - clear - N24; lia.
  - intros T. destruct rst as [v0 v1|cx p]. { exfalso. destruct XS as (XT & _). change (Z.testbit fxx 0 = true) in T. rewrite XT in T. discriminate T. }
    destruct (XDYN cx p eq_refl) as [-> _]. cbn [L5.bo_cap L5.bo_st]. clear - N24; lia.
  - intros N3 DYF. assert (J2: j <= 2). { destruct rst as [v0 v1|cx p]. exact JX. exfalso. destruct XS as (XT & _). change (Z.testbit fxx 0 = false) in DYF. rewrite XT in DYF. discriminate DYF. }
    replace (round_up (Z.of_nat (n1 + 1))) with 8 by (unfold round_up; clear - N24; destruct n1 as [|[|[|[|[|]]]]]; cbn; lia). apply (credit_next crc j CRK CRB). clear - Hj J2; lia.
  - exact A1.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; clear - SHI'; lia. split. exact SPT. unfold spd. rewrite RESIZE_SCR_val. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia.
  - exact OX.
  - exact OLX.
  - exact AX8.
  - unfold spd, X; clear; lia.
  - unfold X; clear - SHI'; lia.
  - apply (L5C.writable_of_defined RSEGS). exact DX. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia.
  - intros cap q E. cbn in E. subst rst LBc. cbn. left. destruct (XDYN cap q eq_refl) as [-> _]. reflexivity.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. destruct POST as (RP2 & GP).
    assert (E2r: forall i v, In i cs_all -> getr R1 (reg i) = v -> getr R2 (reg i) = v). { intros i v Hi Hv. rewrite (preserved_sregs R1 R2 i RP2) by exact Hi. exact Hv. }
    assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
    assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
    assert (INn: Z.testbit fn 0 = true -> In (pn, 64) LBc).
    { intros T. destruct (FR2 T) as [Ec _]. subst LBc BN. rewrite T, Ec. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
    assert (INd: Z.testbit fd 0 = true -> In (pd, 64) LBc).
    { intros T. destruct (FR3 T) as [Ec _]. subst LBc BD. rewrite T, Ec. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
    assert (SUB2: forall b, In b LBc -> In b LB2). { intros b Hb. destruct g as [|A cap]. destruct GP as (_ & -> & _). exact Hb. destruct GP as (_ & _ & _ & -> & _). right. exact Hb. }
    assert (LBceil0: forall b, In b LB -> fst b + snd b <= hl_ceil L). { intros b Hb. apply LBceil. apply LBcI. exact Hb. }
    (* [comment removed for export] *)
    assert (COMMON: forall W, L5C.hpres L LBc spd RESIZE_SCR W M M2 ->
              (forall a, ~ (X <= a < X + 32) -> (forall cx p, rst = L5.BDyn cx p -> ~ (p <= a < p + 64)) -> L5.outside W a) ->
              (forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
              /\ L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M2 /\ L5.defined M2 (S - SCR_OPMOD) SCR_OPMOD /\ L5.img_clear M2 0x10000 0x20000
              /\ late M2 fn cn pn fd cd pd fn0 fd0 /\ (forall i, denomd <= i < denomd + 8 * Z.of_nat l1 -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
              /\ L5.big_at RSEGS M2 Q (L5.BO fq nqo (L5.BInl q0 q1)) /\ L5.big_at RSEGS M2 bo bb).
    { intros W HPW HWo.
      assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hn. apply (kept_above M M2 LBc spd RESIZE_SCR W a HPW). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). exact Ha.
        apply HWo. exact Hn. intros cx p E. destruct (XDYN cx p E) as [_ FBp]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBp) as (_ & _ & _ & _ & P5). unfold spd in Ha. clear - Ha P5 SLO'. lia. }
      assert (HW2: forall a, L5C.kept L LB S SCR_OPMOD [(X, 32)] a -> L5.outside W a).
      { intros a KA'. apply HWo. { pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA') as OW. apply (L5HP.outside_in _ _ X 32 OW). left; reflexivity. }
        intros cx p E. destruct (XDYN cx p E) as [_ FBp]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBp) as (_ & P2 & _ & _ & P5). destruct FBp as (_ & BAp & _).
        refine (L5C.kept_not_fresh L LB S SCR_OPMOD [(X, 32)] a p 64 KA' _ P2 P5 LBceil0). intros b Hb. apply BAp. rewrite !in_app_iff. right; right; exact Hb. }
      split. exact KA. split.
      - eapply (L5HP.hpres_trans L LB LBc S SCR_OPMOD [(X, 32)] M0 M M2 spd RESIZE_SCR W). exact HP. exact HPW.
        + intros a KA'. eapply L5HP.kept_mono. exact KA'. exact LBcI. unfold spd; rewrite SCR_OPMOD_val, RESIZE_SCR_val; clear; lia. unfold spd; clear; lia.
          intros _. apply HW2. exact KA'.
        + exact LBcI. + exact CEILS. + clear - SHI; lia. + rewrite SCR_OPMOD_val; clear; lia. + rewrite EV; clear; lia. + exact (proj1 SPT).
      - split. { rewrite SCR_OPMOD_val. eapply SCR_kept. exact HPW. rewrite RESIZE_SCR_val; clear; lia. exact SCR'. }
        split. { eapply IC_kept. exact HPW. 2: exact IC. intros a Ha. apply HWo. unfold X; clear - Ha SLO; lia.
                 intros cx p E. destruct (XDYN cx p E) as [_ FBp]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBp) as (_ & P2 & _). rewrite IMG', IMGLO' in P2. clear - Ha P2. lia. }
        split. { eapply late_kept. 4: exact LT.
          + intros i Hi. apply KA. unfold spd; clear - Hi SLO SHI; lia. unfold X; clear - Hi; lia.
          + intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pn 64). apply SUB2. apply INn. exact T.
          + intros T _. eapply proj1, (LBdef _ _ _ _ HH2 pd 64). apply SUB2. apply INd. exact T. }
        split. { intros i Hi. rewrite Edd in Hi. destruct (Z.testbit fd 0) eqn:Tfd.
          { pose proof (LBceil (pd, 64) (INd eq_refl)) as PC. cbn in PC.
            apply (kept_inblock M M2 LBc crc _ spd RESIZE_SCR _ pd 64 i HH HPW). apply INd; reflexivity. clear - Hi L13; lia. exact SPT. apply HWo. unfold X; clear - Hi PC SLO' L13; lia.
            intros cx p E. destruct (XDYN cx p E) as [_ (_ & BAp & _)]. destruct (FR3 eq_refl) as [Ec _].
            destruct (BAp (pd, 64) ltac:(rewrite !in_app_iff; right; left; subst BD; rewrite Ec; cbn; left; reflexivity)) as [A'|A']; cbn in A'; clear - A' Hi L13; lia. }
          apply KA. unfold spd; clear - Hi SLO SHI L13; lia. unfold X; clear - Hi L13 SLO; lia. }
        split. { eapply big_at_agree1. 4: exact OQ. intros i Hi. apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
        eapply big_at_agree1. 4: exact OBB. intros i Hi. apply KA; subst bo; unfold X, spd in *; clear - Hi SLO SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia. }
    assert (G9r: forall i v, In i cs_all -> getr R (reg i) = v -> In i KS_d5ug8 -> getr R2 (reg i) = v).
    { intros i v Hi Hv Hk. apply (E2r i v Hi). rewrite (K1 i Hk). exact Hv. }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct GP as (DYS & -> & -> & (st' & OX2 & OL2 & SST) & HP2). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in OX2, OL2, SST, HP2.
      destruct rst as [v0 v1|cx qx]. { exfalso. destruct XS as (XT & _ & _ & Hle & _). destruct DYS as [T|T]. change (Z.testbit fxx 0 = true) in T. rewrite XT in T. discriminate T. clear - T Hle N24. lia. }
      destruct st' as [|cap' qx']. destruct SST. destruct SST as [-> ->]. destruct (XDYN cx qx eq_refl) as [-> FBX].
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBX) as (PX1 & PX2 & PX3 & _ & PX5).
      destruct (COMMON _ HP2) as (KA & HP2' & SCR2 & IC2 & LT2 & KD & OQ2 & OBB2).
      { intros a NX NB r [<-|[<-|[]]]; unfold L5.in_rng; cbn. exact NX. intros C. apply (NB 8 qx eq_refl). clear - C N24. lia. }
      apply (stage_G9 fx2 R2 M2 model2 crc fq nqo q0 q1 fxx qx fn cn pn fd cd pd fn0 fd0 denomd).
      all: try (eapply G9r; [inl | eassumption | inl]).
      * eapply u64_at_agree1. 4: exact VQS. intros i Hi; apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * exact HH2.
      * pose proof KPOS. clear - CRK Hj H. nia. * pose proof BPOS. clear - CRB Hj H. nia.
      * exact SCR2. * exact IC2. * exact LT2. * exact OQ2. * exact NQ.
      * replace (Datatypes.S n1) with (n1 + 1)%nat by (clear; lia). exact OX2.
      * exact NEGX.
      * eapply (cdef_above M M2 _ spd RESIZE_SCR _ X 32 HP2). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). unfold X, spd; clear; lia. unfold X; clear - SHI; lia. exact DX.
      * destruct FBX as (B1' & B2' & B3'). split. exact B1'. split. exact B2'. eapply proj1, (LBdef _ _ _ _ HH2 qx 64). subst LBc. cbn. left. reflexivity.
      * exact Edd. * exact DINL.
      * eapply defined_agree1. 2: exact DDEF. intros i Hi; apply KD; exact Hi.
      * eapply u64_at_agree1. 4: exact Cd. intros i Hi; apply KD; subst l; clear - Hi L13; lia. clear - DNlo; lia. clear - DNhi; lia.
      * exact SD1. * exact OBB2. * exact HP2'.
    + (* [comment removed for export] *)
      destruct GP as (DYF & N3 & Ecap & -> & -> & FB & OX2 & OL2 & HP2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OX2, OL2, FB.
      destruct rst as [v0 v1|cx qx]. 2:{ exfalso. destruct XS as (XT & _). change (Z.testbit fxx 0 = false) in DYF. rewrite XT in DYF. discriminate DYF. }
      replace (round_up (Z.of_nat (n1 + 1))) with 8 in Ecap by (unfold round_up; clear - N24; destruct n1 as [|[|[|[|[|]]]]]; cbn; lia). subst cap.
      destruct (COMMON _ HP2) as (KA & HP2' & SCR2 & IC2 & LT2 & KD & OQ2 & OBB2). { intros a NX _. apply outside1. exact NX. }
      pose proof (credit_step crc j CRK CRB) as [CRK' CRB'].
      apply (stage_G9 fx2 R2 M2 model2 (debit L crc (8 * 8)) fq nqo q0 q1 (Z.lor fxx 1) A fn cn pn fd cd pd fn0 fd0 denomd).
      all: try (eapply G9r; [inl | eassumption | inl]).
      * eapply u64_at_agree1. 4: exact VQS. intros i Hi; apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KA; unfold X, Q, spd in *; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * subst LBc. cbn [blocks_ofst app] in HH2 |- *. exact HH2.
      * pose proof KPOS. unfold debit in CRK' |- *. cbn [fst snd] in CRK' |- *. clear - CRK' JX H. nia. * pose proof BPOS. unfold debit in CRB' |- *. cbn [fst snd] in CRB' |- *. clear - CRB' JX H. nia.
      * exact SCR2. * exact IC2. * exact LT2. * exact OQ2. * exact NQ.
      * replace (Datatypes.S n1) with (n1 + 1)%nat by (clear; lia). exact OX2.
      * rewrite Z.lor_spec, NEGX. reflexivity.
      * eapply (cdef_above M M2 _ spd RESIZE_SCR _ X 32 HP2). unfold spd; fsclia. rewrite RESIZE_SCR_val; clear; lia. exact (proj1 SPT). unfold X, spd; clear; lia. unfold X; clear - SHI; lia. exact DX.
      * subst LBc. cbn [blocks_ofst app] in FB. exact FB.
      * exact Edd. * exact DINL.
      * eapply defined_agree1. 2: exact DDEF. intros i Hi; apply KD; exact Hi.
      * eapply u64_at_agree1. 4: exact Cd. intros i Hi; apply KD; subst l; clear - Hi L13; lia. clear - DNlo; lia. clear - DNhi; lia.
      * exact SD1. * exact OBB2. * exact HP2'.
Qed.


(* [comment removed for export] *)
Local Ltac zlia := flia.
(* [comment removed for export] *)
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
Lemma stage_G7 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit) (j : Z)
      (fq : Z) (nqo : nat) (q0 q1 fxx : Z) (rst : L5.bstore) (wr : list Z) (fn cn pn fd cd pd fn0 fd0 denomd : Z) :
  let l := (l1 - 1)%nat in
  let BN := (if Z.testbit fn 0 then [(pn, 8 * cn)] else []) in
  let BD := (if Z.testbit fd 0 then [(pd, 8 * cd)] else []) in
  let LBc := blocks_ofst rst ++ BN ++ BD ++ LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 21) = Z_to_bv 64 (Z.of_nat l1) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat n1) ->
  getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 qneg ->
  (* [comment removed for export] *)
  L5.u64_at RSEGS M (Q - 152) denomd -> L5.u64_at RSEGS M (Q - 144) (Z.of_nat l1) ->
  L5.u64_at RSEGS M (Q - 232) (Q + 16) -> L5.u64_at RSEGS M (Q - 224) (Z.of_nat nqo) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  fst cr - j * hl_k_per_malloc L <= fst crc -> snd cr - j * (64 + hl_b_overhead L) <= snd crc -> 0 <= j <= 3 ->
  (match rst with L5.BInl _ _ => j <= 2 | L5.BDyn _ _ => True end) ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
  mid M fn cn pn fd cd pd fn0 fd0 ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Q (L5.BO fq nqo (L5.BInl q0 q1)) -> (nqo + l + 1 = n1)%nat ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M X (L5.BO fxx n1 rst) -> Z.testbit fxx 1 = false -> L5C.obj_limbs RSEGS M (L5.BO fxx n1 rst) wr -> L5.defined M X 32 ->
  (forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ L5C.fresh_block L (BN ++ BD ++ LB) M p 64) ->
  (match rst with L5.BInl _ _ => (n1 <= 2)%nat | L5.BDyn _ _ => True end) ->
  (* [comment removed for export] *)
  denomd = (if Z.testbit fd 0 then pd else S - 184) -> (Z.testbit fd 0 = false -> nb = 1%nat) -> (Z.testbit fd 0 = true -> nb = 2%nat) ->
  L5.defined M denomd (8 * Z.of_nat l1) -> L5.u64_at RSEGS M (denomd + 8 * Z.of_nat l) d ->
  (sec = true -> Z.testbit fn 0 = true /\ Z.testbit fd 0 = true) ->
  L5.big_at RSEGS M bo bb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22854 M model) K.
Proof.
  intros l BN BD LBc H2 H3 H4 H8 H9 H18 H21 H23 H24 H25 H26 VD VS VQ VQS MBV HH CRK CRB Hj JX SCR IC MD OQ NQ OX NEGX OLX DX XDYN RFIT Edd DN1 DN2 DDEF Cd SD1 OBB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof NF as (L13 & N24 & LN & NL2 & _ & _ & _ & _ & DR & SECF & SECF' & _). pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'. pose proof Hq01 as Hq.
  assert (Hl: (l <= 2)%nat) by (subst l; clear - L13; lia).
  pose proof MD as (TF & SAV & LO0 & F0b & LO1 & F1b & LO2 & FR2 & LO3 & FR3 & C348 & C408).
  pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'.
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AX8: X mod 8 = 0). { unfold X. replace (S + 64) with (S + 8 * 8) by (clear; lia). apply al8. exact A16. }
  assert (WFR: L5.writable RSEGS M (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI SLO; lia. }
  pose proof OX as (Xb0 & Xf & X8 & XS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Xb0, Xf, X8, XS.
  pose proof OLX as (WL & WOK & WST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in WL, WST.
  (* [comment removed for export] *)
  set (xn := nth (n1 - 1) wr 0).
  assert (XNR: 0 <= xn < 2 ^ 64). { subst xn. pose proof (proj1 (List.Forall_nth _ _) WOK (n1 - 1)%nat 0 ltac:(rewrite WL; clear - N24; lia)) as B. exact B. }
  (* [comment removed for export] *)
  assert (DL: (Z.testbit fd 0 = false -> l1 = 1%nat /\ denomd = S - 184) /\ (Z.testbit fd 0 = true -> (2 <= l1)%nat /\ denomd = pd)).
  { split; intros T; rewrite T in Edd; split; try exact Edd.
    - pose proof (DN1 T) as N1. destruct (Sumbool.sumbool_of_bool sec) as [ES|ES]. { destruct (SECF ES) as (N2 & _). exfalso. clear - N1 N2. lia. } destruct (SECF' ES) as [E _]. clear - E N1. lia.
    - pose proof (DN2 T) as N2. destruct (Sumbool.sumbool_of_bool sec) as [ES|ES]. { destruct (SECF ES) as (_ & E & _). clear - E. lia. } destruct (SECF' ES) as [E _]. clear - E N2. lia. }
  (* [comment removed for export] *)
  set (remd := L5.bo_data X (L5.BO fxx n1 rst)).
  assert (RC: L5.u64_at RSEGS M (remd + 8 * (Z.of_nat n1 - 1)) xn /\ remd mod 8 = 0 /\ 4096 <= remd /\ remd + 64 <= 2 ^ 47 /\
              match rst with L5.BInl _ _ => remd = X + 16 | L5.BDyn _ p => remd = p /\ p + 64 <= hl_ceil L /\ L5.u64_at RSEGS M (X + 24) p end).
  { subst remd xn. destruct rst as [v0 v1|cx p]; cbn [L5.bo_data L5.bo_st].
    - destruct XS as (XT & U16 & U24 & Hle & R0' & R1'). assert (E2: n1 = 2%nat) by (clear - Hle N24; lia). rewrite E2 in WST |- *. rewrite WST. cbn [firstn nth].
      split. exactA U24. split. { unfold X. replace (S + 64 + 16) with (S + 8 * 10) by (clear; lia). apply al8. exact A16. } split. unfold X; clear - SLO; lia. split. unfold X; clear - SHI; lia. reflexivity.
    - destruct XS as (XT & U16 & U24 & _). destruct (XDYN cx p eq_refl) as [-> FBp]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBp) as (P1 & P2 & P3 & _ & P5).
      split. { replace (p + 8 * (Z.of_nat n1 - 1)) with (p + 8 * Z.of_nat (n1 - 1)%nat) by (clear - N24; lia). unfold L5.limbs_at in WST. apply WST. rewrite WL. clear - N24; lia. }
      split. apply mod16_mod8; exact P3. split. exact P1. split. clear - P5 SPT; lia. split. reflexivity. split. exact P5. exact U24. }
  destruct RC as (Cxn & RM8 & RMlo & RMhi & RW).
  assert (DNB: 4096 <= denomd /\ denomd + 8 * Z.of_nat l + 8 <= 2 ^ 47 /\ denomd mod 8 = 0 /\
               (Z.testbit fd 0 = true -> denomd + 64 <= hl_ceil L)).
  { rewrite Edd. destruct (Z.testbit fd 0) eqn:Tfd.
    - destruct (FR3 eq_refl) as [_ FBd]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBd) as (P1 & P2 & P3 & _ & P5). split. clear - P1; lia. split. clear - P5 Hl SPT; lia.
      split. apply mod16_mod8; exact P3. intros _; exact P5.
    - split. clear - SLO; lia. split. clear - SHI Hl; lia. split. replace (S - 184) with (S + 8 * (-23)) by (clear; lia). apply al8. exact A16. intros F; discriminate F. }
  destruct DNB as (DNlo' & DNhi & DN8 & DNC). assert (DNlo: 4096 <= denomd + 8 * Z.of_nat l) by (clear - DNlo'; lia).
  (* [comment removed for export] *)
  assert (JOIN: exists fx1 R1 M1, msteps RSEGS (st fx R 0x22854 M) (st fx1 R1 (if xn <? d then PRE else 0x228b0) M1)
            /\ (forall x, In x [2; 3; 4; 8; 9; 18; 21; 24; 25; 26]%nat -> getr R1 (reg x) = getr R (reg x))
            /\ getr R1 (reg 22) = Z_to_bv 64 (Z.of_nat l) /\ getr R1 (reg 23) = Z_to_bv 64 (Z.of_nat n1 - 1)
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (Q - 336 <= i < Q - 288) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M1
            /\ L5.u64_at RSEGS M1 (Q - 296) (Z.of_nat n1) /\ L5.u64_at RSEGS M1 (Q - 304) remd
            /\ L5.u64_at RSEGS M1 (Q - 320) 0 /\ L5.u64_at RSEGS M1 (Q - 328) qneg /\ L5.u64_at RSEGS M1 (Q - 336) 1).
  { clear - H2 H3 H4 H8 H9 H18 H21 H23 H24 H25 H26 VD VS A16 SLO SHI SLO' SHI' SPT N24 L13 Hl AQ16 AX8 WFR Xb0 Xf X8 XS XNR DL DNC DNlo' DNlo DNhi DN8 RW Cxn RM8 RMlo RMhi Cd DR Hq XDYN.
    unfold X, Q, spd in *.
    destruct (Z.testbit fd 0) eqn:Tfd; [destruct DL as [_ DL]; destruct (DL eq_refl) as [DLl DLe]; pose proof (DNC eq_refl) as PC | destruct DL as [DL _]; destruct (DL eq_refl) as [DLl DLe]];
      (destruct rst as [v0 v1|cx p]; [destruct XS as (XT & U16 & U24 & Hle & _); pose proof RW as Erd | destruct XS as (XT & U16 & U24 & _); destruct RW as (Erd & PC' & Up);
         pose proof (proj1 (XDYN cx p eq_refl)) as Ecx]);
      destruct (Z.ltb_spec xn d) as [LT|GE].
    all: subst l.
    - (* [comment removed for export] *)
      pose proof (d6ug7i0_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 66%nat => denomd | 67%nat => Z.of_nat l1 | 71%nat => fxx | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
    - (* [comment removed for export] *)
      pose proof (d6ug7i1_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 66%nat => denomd | 67%nat => Z.of_nat l1 | 71%nat => fxx | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
    - (* [comment removed for export] *)
      pose proof (d6ug7d0_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 66%nat => denomd | 67%nat => Z.of_nat l1 | 71%nat => fxx | 72%nat => p | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
    - (* [comment removed for export] *)
      pose proof (d6ug7d1_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 66%nat => denomd | 67%nat => Z.of_nat l1 | 71%nat => fxx | 72%nat => p | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
    - (* [comment removed for export] *)
      pose proof (d5ug7ni0_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 67%nat => Z.of_nat l1 | 71%nat => fxx | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
    - (* [comment removed for export] *)
      pose proof (d5ug7ni1_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 67%nat => Z.of_nat l1 | 71%nat => fxx | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
    - (* [comment removed for export] *)
      pose proof (d5ug7nd0_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 67%nat => Z.of_nat l1 | 71%nat => fxx | 72%nat => p | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
    - (* [comment removed for export] *)
      pose proof (d5ug7nd1_conc fx R M (fun j => match j with 2%nat => S - 64 | 36%nat => S + 64 | 37%nat => 1 | 61%nat => qneg | 62%nat => 0 | 65%nat => Z.of_nat n1 | 67%nat => Z.of_nat l1 | 71%nat => fxx | 72%nat => p | 73%nat => xn | 74%nat => d | _ => 0 end)) as P; cbn beta iota in P.
      edestruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & C0 & C1 & C2 & C3 & C4)); [pside .. | clear P].
      exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
      split. rewrite A22; f_equal; clear - L13 DLl; lia. split. rewrite A23; f_equal; clear - N24; lia.
      split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. clear - Hn; lia. } split. exact MG.
      split. exact C0. split. rewrite Erd; exactA C1. split. exact C2. split. exact C3. exact C4.
  }
  destruct JOIN as (fx1 & R1 & M1 & MS1 & K1 & A22 & A23 & FR1 & MG1 & C296 & C304 & C320 & C328 & C336).
  pose proof C320 as C384. pose proof C328 as C392. pose proof C336 as C400. unfold Q in C384, C392, C400.
  assert (KF: forall i, 0 <= i < 2 ^ 64 -> ~ (S - 400 <= i < S - 352) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn. apply FR1. exact Hi. unfold Q; clear - Hn; lia. }
  assert (LT1: late M1 fn cn pn fd cd pd fn0 fd0).
  { apply late_of_mid. 2: exactA C400. 2: exactA C384. 2: exactA C392.
    eapply mid_kept. 4: exact MD. intros i Hi; apply KF; clear - Hi SLO SHI; lia.
    intros _ D'; eapply L5.defined_grows; [exact MG1 | exact D']. intros _ D'; eapply L5.defined_grows; [exact MG1 | exact D']. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (hi_heap_stackwrite LBc crc M M1 _ (S - 400) (S - 352)). exact HH. exact KF. clear - SLO'; lia. clear - SHI'; lia. exact (proj1 SPT). exact MG1. }
  assert (LBcI: forall b, In b LB -> In b LBc). { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; right; exact Hb. }
  assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L). { intros [A m] Hb. pose proof (LBdef _ _ _ _ HH A m Hb) as (_ & _ & Ahi & _). exact Ahi. }
  assert (CEILS: hl_ceil L <= S - SCR_OPMOD). { rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (HP1: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M1).
  { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M1 S SCR_OPMOD [(X, 32)]). exact HP.
    - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M1 (fun a => S - 400 <= a < S - 352)). exact KF.
      { intros a KA' C. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD [(X, 32)] a KA' ltac:(intros b Hb; apply LBceil; apply LBcI; exact Hb) CEILS _ _). rewrite IMG'; clear - SPT; lia.
        rewrite SCR_OPMOD_val. clear - C; lia. }
      rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR'. exact MG1.
    - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEILS. - clear - SHI; lia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - exact (proj1 SPT). }
  assert (IC1: L5.img_clear M1 0x10000 0x20000). { intros i Hi. rewrite KF. apply IC; exact Hi. clear - Hi; lia. clear - Hi SLO; lia. }
  assert (KX: forall i, X <= i < X + 32 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KF; unfold X in Hi; clear - Hi SLO SHI; lia. }
  assert (OX1: L5.big_at RSEGS M1 X (L5.BO fxx n1 rst)). { eapply big_at_agree1. 4: exact OX. exact KX. unfold X; clear - SLO; lia. unfold X; clear - SHI; lia. }
  assert (OLX1: L5C.obj_limbs RSEGS M1 (L5.BO fxx n1 rst) wr).
  { eapply obj_limbs_agree1. 3: exact OLX. all: cbn [L5.bo_st]; intros cap q E; rewrite E in RW; destruct RW as (Erd & PC' & _); rewrite WL.
    intros i Hi. apply KF. clear - Hi RMlo RMhi Erd N24; lia. clear - Hi PC' Erd SLO' N24; lia. clear - RMlo RMhi Erd N24; lia. }
  assert (XDYN1: forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ L5C.fresh_block L (BN ++ BD ++ LB) M1 p 64).
  { intros cx p E. destruct (XDYN cx p E) as [Ec (B1' & B2' & B3')]. split. exact Ec. split. exact B1'. split. exact B2'. eapply L5.defined_grows. exact MG1. exact B3'. }
  assert (OQ1: L5.big_at RSEGS M1 Q (L5.BO fq nqo (L5.BInl q0 q1))). { eapply big_at_agree1. 4: exact OQ. intros i Hi; apply KF; unfold Q in Hi; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
  assert (KD: forall i, denomd <= i < denomd + 8 * Z.of_nat l1 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KF. clear - Hi DNlo' DNhi L13; lia. rewrite Edd in Hi. destruct (Z.testbit fd 0). pose proof (DNC eq_refl) as PC. rewrite Edd in PC. clear - Hi PC SLO' L13; lia. clear - Hi L13; lia. }
  assert (DDEF1: L5.defined M1 denomd (8 * Z.of_nat l1)). { eapply L5.defined_grows. exact MG1. exact DDEF. }
  assert (Cd1: L5.u64_at RSEGS M1 (denomd + 8 * Z.of_nat l) d). { eapply u64_at_agree1. 4: exact Cd. intros i Hi; apply KD; subst l; clear - Hi L13; lia. clear - DNlo; lia. clear - DNhi; lia. }
  assert (OBB1: L5.big_at RSEGS M1 bo bb). { eapply big_at_agree1. 4: exact OBB. intros i Hi; apply KF; subst bo; clear - Hi SLO SHI; lia. subst bo; clear - SLO; lia. subst bo; clear - SHI; lia. }
  assert (DX1: L5.defined M1 X 32). { eapply L5.defined_grows. exact MG1. exact DX. }
  assert (SCR1: L5.defined M1 (S - SCR_OPMOD) SCR_OPMOD). { eapply L5.defined_grows. exact MG1. exact SCR. }
  assert (DINL: Z.testbit fd 0 = false -> (l1 <= 2)%nat). { intros T. destruct DL as [DL' _]. destruct (DL' T) as [E _]. rewrite E. clear; lia. }
  assert (SDX: sec = true -> (exists qx, rst = L5.BDyn 8 qx) /\ Z.testbit fn 0 = true /\ Z.testbit fd 0 = true).
  { intros SEC. destruct (SD1 SEC) as [Tn Td]. destruct (SECF SEC) as (_ & _ & N3 & _). split. 2: split; assumption.
    destruct rst as [v0 v1|cx p]. exfalso; clear - RFIT N3; lia. destruct (XDYN cx p eq_refl) as [-> _]. eexists; reflexivity. }
  (* [comment removed for export] *)
  assert (VD1: L5.u64_at RSEGS M1 (Q - 152) denomd). { eapply u64_at_agree1. 4: exact VD. intros i Hi; apply KF; unfold Q in Hi; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
  assert (VS1: L5.u64_at RSEGS M1 (Q - 144) (Z.of_nat l + 1)).
  { replace (Z.of_nat l + 1) with (Z.of_nat l1) by (subst l; clear - L13; lia). eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KF; unfold Q in Hi; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
  assert (VQ1: L5.u64_at RSEGS M1 (Q - 232) (Q + 16)). { eapply u64_at_agree1. 4: exact VQ. intros i Hi; apply KF; unfold Q in Hi; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
  assert (VQS1: L5.u64_at RSEGS M1 (Q - 224) (Z.of_nat nqo)). { eapply u64_at_agree1. 4: exact VQS. intros i Hi; apply KF; unfold Q in Hi; clear - Hi SLO SHI; lia. unfold Q; clear - SLO; lia. unfold Q; clear - SHI; lia. }
  pose proof LT1 as (TF1 & SAV1 & LO01 & _ & LO11 & _ & LO21 & FR21 & LO31 & FR31 & C3481 & C4001 & C3841 & C3921 & C4081).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  destruct (xn <? d).
  - (* [comment removed for export] *)
    apply (stage_L fx1 R1 M1 model crc (n1 - 1)%nat fq nqo (L5.BInl q0 q1) fxx rst wr fn cn pn fd cd pd fn0 fd0 remd (Q + 16) denomd).
    all: try (rewrite (K1 _) by inl; assumption).
    all: try assumption.
    + rewrite (K1 21%nat) by inl. rewrite H21. f_equal. subst l; clear - L13; lia.
    + rewrite A23. f_equal. clear - N24; lia.
    + subst l; clear - LN L13 N24; lia. + subst l; clear - NL2 L13 LN N24; lia.
    + pose proof KPOS. clear - CRK Hj H; nia. + pose proof BPOS. clear - CRB Hj H; nia.
    + subst l; clear - NQ L13 N24; lia.
    + intros cq p E; discriminate E.
    + reflexivity.
    + subst l; clear - NQ L13 N24 NL2; lia.
    + replace (Datatypes.S (n1 - 1)) with n1 by (clear - N24; lia). exact OX1.
    + subst remd. replace (Datatypes.S (n1 - 1)) with n1 by (clear - N24; lia). reflexivity.
    + destruct rst as [v0 v1|cx p]. clear - RFIT N24; lia. exact I.
    + intros SEC. destruct (SDX SEC) as (EX & Tn & Td). split. exact EX. split. eexists _, _; reflexivity. split. exact Tn. exact Td.
  - (* [comment removed for export] *)
    apply (stage_GROW fx1 R1 M1 model crc j fq nqo q0 q1 fxx rst wr fn cn pn fd cd pd fn0 fd0 denomd).
    all: try (rewrite (K1 _) by inl; assumption).
    all: try assumption.
    + rewrite (K1 21%nat) by inl. rewrite H21. f_equal. subst l; clear - L13; lia.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5OPMOD1GU.
