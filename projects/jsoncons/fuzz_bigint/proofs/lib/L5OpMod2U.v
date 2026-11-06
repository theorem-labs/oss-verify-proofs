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
     L5CmpU L5NormU L5NormOkU L5DivSpecsU L5DivPartsU L5OpModPU L5DivTailU L5DivEarlyU L5OpMod1SU L5DivO2SU L5DivO2KU L5OpMod2SpecU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5OPMOD2U.
Import L5CSU. Import L5DSU. Import L5DIVPU. Import L5OPMODPU. Import L5OM1SU. Import L5DO2SU. Import L5OM2SU.

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
Local Notation obj_limbs_agree1 := L5DIVEARLYU.obj_limbs_agree1.

Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r3 : (3%bv : bv 5) = reg 3. Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : (4%bv : bv 5) = reg 4. Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.
Lemma r12 : (12%bv : bv 5) = reg 12. Proof. apply bv_eq; reflexivity. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
Lemma r14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq; reflexivity. Qed.

Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall i, In i cs_all -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
(* [comment removed for export] *)
Lemma segs_below : segs_below_b RSEGS 0x92000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma writable_defined_hi M a n : L5.writable RSEGS M a n -> L5KU.IMG_HI <= a -> 0 <= n -> a + n <= 2 ^ 64 -> L5.defined M a n.
Proof.
  intros W Hlo Hn Hhi i Hi. specialize (W i 1%nat ltac:(lia) ltac:(cbn; lia)). cbn [store_ok] in W.
  unfold wview in W. destruct (M (Z_to_bv 64 (a + i))) eqn:E. congruence.
  unfold L5KU.IMG_HI in Hlo. rewrite BG.unsigned_lit in W by lia. rewrite (find_segment1_none_above RSEGS 0x92000 (a + i) segs_below) in W by lia. discriminate W.
Qed.
Lemma lb_remove_head A n LBx : lb_remove A ((A, n) :: LBx) = LBx.
Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
Definition VP (E X fq qp qc u1 u8 : Z) (j : nat) : Z :=
  match j with 2%nat => E | 33%nat => X | 36%nat => fq | 37%nat => qp | 38%nat => qc | 43%nat => u1 | 44%nat => u8 | _ => 0 end.
(* [comment removed for export] *)
Definition VF (S r x u1 u8 : Z) (j : nat) : Z :=
  match j with 2%nat => S | 33%nat => r | 34%nat => x | 43%nat => u1 | 44%nat => u8 | _ => 0 end.

Lemma SCR_OPMOD_val : SCR_OPMOD = 10240. Proof. reflexivity. Qed.
Lemma DIVO2_SCR_val : DIVO2_SCR = 9440. Proof. reflexivity. Qed.
Lemma OPDEL_SCR_val : OPDEL_SCR = 8224. Proof. reflexivity. Qed.
Lemma COPY_SCR_val : COPY_SCR = 8304. Proof. reflexivity. Qed.
Local Ltac uSCR := rewrite ?SCR_OPMOD_val, ?DIVO2_SCR_val, ?OPDEL_SCR_val, ?COPY_SCR_val in *.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac kreg K i H := etransitivity; [exact (K i ltac:(inl)) | exact H].
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; lia.
Local Ltac fsclia := prune_impl; prune_disj; uSCR; lia.
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].

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
Hypothesis OPDEL : opdel_sized_spec L HI.
Hypothesis COPYC : copy_spec L HI.
Hypothesis UNNORM : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.                                   (* [comment removed for export] *)
Let CMP : L5CMPU.cmp_spec := @L5CMPU.cmp_ok _.
Let NORM : L5NORMU.norm_spec L HI := L5NORMOKU.norm_ok L HI LY HIok RESIZE.
Let DIVTAIL : divtail_stmt L HI := L5DIVTAILU.divtail_ok L HI LY HIok OPDEL.
Let DIVTAIL2 : L5DIVTAILU.divtail2_stmt L HI := L5DIVTAILU.divtail2_ok L HI LY HIok OPDEL.
(* [comment removed for export] *)
Let DIVO2 : divO2_spec L HI := L5DIVO2KU.divO2_ok L HI LY HIok KPOS BPOS COPYA ASSIGN RESIZE NORM UNNORM DIVLOOP DIVTAIL DIVTAIL2 CMP.

Let IMG := L5DIVEARLYU.IMG L LY.
Let IMGLO := L5DIVEARLYU.IMGLO L LY.
Let ERRNOV := L5DIVEARLYU.ERRNOV L LY.
Let LBdef := @L5DIVEARLYU.LBdef _ L HI HIok.
Let kept_above := L5DIVEARLYU.kept_above L LY.
Let kept_inblock := @L5DIVEARLYU.kept_inblock _ L HI LY HIok.
Let cdef_above := L5DIVEARLYU.cdef_above L LY.
Let cdef_below := L5DIVEARLYU.cdef_below L LY.
Let hi_heap_stackwrite := @L5DIVEARLYU.hi_heap_stackwrite _ L HI LY HIok.
Lemma ERRNO : hl_errno L + 4 <= 0x7fff7f800000. Proof. rewrite (ly_errno L LY). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (S ao fba fdo : Z) (by_ : L5.bigobj) (wy : list Z).
Let capy : Z := L5.bo_cap by_.
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 (S + 32).
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 S.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 ao.
Hypothesis EAO : ao = S + 160.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 OPMOD2_RET.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 S.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 S SCR_OPMOD.
Hypothesis HS : S + 240 <= hl_sptop L.
Hypothesis WRY : L5.writable RSEGS M0 S 64.
Hypothesis WRB : forall cap q, L5.bo_st by_ = L5.BDyn cap q -> L5.writable RSEGS M0 q (8 * cap).
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis YOK : y_ok LB M0 S by_ wy.
Hypothesis LEN1 : (1 <= L5.bo_len by_)%nat.
Hypothesis CAPY : L5.bo_cap by_ <= 268.
Hypothesis FDO : L5.u8_at RSEGS M0 (S + 32) fdo.
Hypothesis FDOR : 0 <= fdo < 256.
Hypothesis AOK : a_ok M0 ao fba.
Hypothesis CR : credit_for L cr OPMOD2_K (opmodf2_bytes capy).
(* [comment removed for export] *)
Hypothesis KN : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    opmodf2_post L LB cr M0 M' R0 R' S ao fba fdo by_ capy LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' OPMOD2_RET M' model') K.

(* [comment removed for export] *)
Lemma SPW : S mod 16 = 0 /\ 0x7fff7f800000 + 10240 <= S /\ S + 240 <= 2 ^ 47 /\ hl_sptop L - 8388608 + 10240 <= S /\ S + 240 <= hl_sptop L
            /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof using L M0 S fdo by_ STK HS LEN1 FDOR. pose proof STK as (A & B & C & D & _). uSCR. repeat split; try lia. Qed.
Lemma SCR0 : L5.defined M0 (S - 10240) 10240. Proof. pose proof STK as (_ & _ & _ & _ & W). exact W. Qed.
Lemma UR01 : U R0 1 = OPMOD2_RET.
Proof using R0 fdo by_ G1 LEN1 FDOR. unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G1. apply BG.unsigned_lit. unfold OPMOD2_RET. lia. Qed.
Lemma CAPR : 1 <= capy <= 268.
Proof using M0 LB S fdo by_ wy WRB YOK LEN1 CAPY FDOR.
  pose proof CAPY as C. pose proof YOK as (OB & _). unfold capy, L5.bo_cap in C |- *. unfold L5.big_at in OB.
  destruct (L5.bo_st by_) as [v0 v1|c q]. lia. destruct OB as (_ & _ & _ & _ & _ & _ & _ & Hc & _). lia.
Qed.
Lemma CAPE : forall cy qy, L5.bo_st by_ = L5.BDyn cy qy -> capy = cy.
Proof. intros cy qy E. unfold capy, L5.bo_cap. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_FIN2 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (by' : L5.bigobj) (wy' : list Z) (LBy : list (Z * Z)) :
  getr R (reg 2) = Z_to_bv 64 (S - 16) -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 (S + 32) -> getr R (reg 10) = Z_to_bv 64 S ->
  (forall i, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LBy crc M (m_vmmaps model) ->
  credit_after L cr DIVO2_K (divO2_bytes capy) crc ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD ->
  L5.u64_at RSEGS M (S - 8) (U R0 1) -> L5.u64_at RSEGS M (S - 16) (U R0 8) ->
  L5.big_at RSEGS M S by' -> L5C.obj_limbs RSEGS M by' wy' ->
  match L5.bo_st by_, L5.bo_st by' with
  | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ LBy = LB /\ L5.defined M q (8 * cap)
  | L5.BInl _ _, L5.BInl _ _ => LBy = LB
  | L5.BInl _ _, L5.BDyn cap' q' => cap' = 8 /\ LBy = (q', 64) :: LB /\ L5C.fresh_block L LB M q' 64
  | L5.BDyn _ _, L5.BInl _ _ => False
  end ->
  L5.u8_at RSEGS M (S + 32) fdo -> a_ok M ao fba ->
  L5C.hpres L LB S SCR_OPMOD [(S, 64); (L5.bo_data S by_, 8 * L5.bo_cap by_)] M0 M ->
  srealizes RSEGS SCFG (cfg R OPF_BACK M model) K.
Proof.
  intros H2 H3 H4 H8 H10 HRS MBV HH CRA SCR T1 T8 OBY OLY STM FDO1 AOK1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof ERRNOV as EV. pose proof ERRNO as EV4. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'. rewrite SCR_OPMOD_val in SCR. pose proof UR01 as UR01'.
  pose proof CAPR as CB. pose proof CR as CR0. pose proof KPOS as KP. pose proof BPOS as BP.
  pose proof OBY as OBY'. unfold L5.big_at in OBY'. destruct OBY' as (Yf & Yfr & Yl & YST).
  pose proof YOK as (OB0 & _ & _ & BLK).
  assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (LBceil: forall b, In b LBy -> fst b + snd b <= hl_ceil L).
  { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
  (* [comment removed for export] *)
  assert (INY: forall cap q, L5.bo_st by' = L5.BDyn cap q -> In (q, 8 * cap) LBy).
  { intros cap q E. rewrite E in STM. destruct (L5.bo_st by_) as [v0 v1|cy qy].
    - destruct STM as (-> & -> & _). left. reflexivity.
    - destruct STM as (-> & -> & -> & _). exact (proj1 BLK). }
  assert (SUBLB: forall b, In b LB -> In b LBy).
  { intros b Hb. destruct (L5.bo_st by_) as [v0 v1|cy qy]; destruct (L5.bo_st by') as [w0 w1|cap q]; try contradiction.
    - rewrite STM. exact Hb. - destruct STM as (_ & -> & _). right. exact Hb. - destruct STM as (_ & _ & -> & _). exact Hb. }
  (* [comment removed for export] *)
  assert (CROK: L5.bo_dyn by' = true -> 8 * L5.bo_cap by' <= 2 ^ 27 /\ credit_ok L crc (8 * L5.bo_cap by')).
  { intros DY. unfold L5.bo_dyn in DY. unfold L5.bo_cap. destruct (L5.bo_st by') as [w0 w1|cap q] eqn:E. { destruct YST as (T & _). rewrite T in DY. discriminate DY. }
    assert (HC: cap = capy \/ cap = 8).
    { destruct (L5.bo_st by_) as [v0 v1|cy qy] eqn:EY. right. exact (proj1 STM). left. rewrite (CAPE cy qy EY). exact (proj1 STM). }
    unfold credit_for, credit_after, credit_ok, OPMOD2_K, opmodf2_bytes, DIVO2_K, divO2_bytes in CR0, CRA |- *.
    destruct CR0 as [C1 C2]. destruct CRA as [C3 C4]. clear - C1 C2 C3 C4 HC CB KP BP. split; [lia | split; lia]. }
  assert (CRA2: forall g : bool, credit_after L cr OPMOD2_K (opmodf2_bytes capy) (if g then debit L crc (8 * L5.bo_cap by') else crc)).
  { intros g. assert (HC: L5.bo_cap by' = capy \/ L5.bo_cap by' = 8 \/ g = false -> True) by (intros; exact I). clear HC.
    assert (HC: 8 * L5.bo_cap by' <= 8 * capy \/ L5.bo_cap by' = 8 \/ L5.bo_cap by' = 2).
    { unfold L5.bo_cap. destruct (L5.bo_st by') as [w0 w1|cap q] eqn:E. right; right; reflexivity.
      destruct (L5.bo_st by_) as [v0 v1|cy qy] eqn:EY. right; left. exact (proj1 STM). left. rewrite (CAPE cy qy EY). pose proof (proj1 STM) as EC. clear - EC; lia. }
    unfold credit_for, credit_after, credit_ok, debit, OPMOD2_K, opmodf2_bytes, DIVO2_K, divO2_bytes in CR0, CRA |- *.
    destruct CR0 as [C1 C2]. destruct CRA as [C3 C4]. destruct g; cbn [fst snd]; clear - C1 C2 C3 C4 HC CB KP BP; split; lia. }
  (* [comment removed for export] *)
  assert (KA0: forall a, S + 64 <= a < S + 240 -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha. apply (kept_above M0 M LB S SCR_OPMOD _ a HP). fsclia. rewrite SCR_OPMOD_val; clear; lia. flia. clear - Ha SHI; lia.
    apply L5C.outside_cons. { unfold L5.in_rng; cbn. clear - Ha; lia. }
    apply L5C.outside_cons. 2: apply L5C.outside_nil.
    unfold L5.in_rng; cbn [fst snd]. unfold L5.bo_data, L5.bo_cap. unfold L5.big_at in OB0. destruct (L5.bo_st by_) as [v0 v1|cy qy]. clear - Ha; lia.
    pose proof (LBdef _ _ _ _ HH0 qy (8 * cy) (proj1 BLK)) as (_ & _ & Bhi & _). unfold hl_ceil in Bhi. clear - Ha Bhi SLO'; lia. }
  (* [comment removed for export] *)
  assert (WF16: L5.writable RSEGS M (S - 16) 16). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. flia. flia. }
  pose proof (dofu2_conc fx R M (VF S (S + 32) S 0 0)) as P. cbn [VF] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) H2 H8 H10 ltac:(flia) A16 WF16 ltac:(flia)) as (fx1 & R1 & M1 & _ & FR1 & _ & (MS1 & K1 & A1 & A10 & A11)). clear P.
  pose proof (mem_eq M M1 FR1) as EM1. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  eapply (COPYC fx1 R1 M model K LBy crc (S + 32) S (S - 16) COPY_BACK fdo by' wy' HH MOK HK0 A10 A11).
  - exact CROK.
  - exact A1.
  - unfold COPY_BACK. split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { replace (S - 16) with (S + (-1) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. exact SPT. rewrite COPY_SCR_val. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia.
  - exact FDO1. - exact FDOR.
  - rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - clear; lia. - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply (cdef_above M0 M LB S SCR_OPMOD _ (S + 32) 32 HP). fsclia. rewrite SCR_OPMOD_val; clear; lia. flia. clear; lia. flia.
    eapply L5.defined_sub. apply (writable_defined_hi M0 S 64 WRY). unfold L5KU.IMG_HI; flia. clear; lia. flia. clear; lia. clear; lia. flia. flia.
  - exact OBY. - exact OLY.
  - exact (mod16_mod8 _ A16).
  - clear; lia. - flia.
  - exact INY.
  - right. clear; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _). destruct POST as (RP2 & GP).
    (* [comment removed for export] *)
    assert (KA2: (forall a, S - 16 <= a < 2 ^ 64 -> ~ (S + 32 <= a < S + 32 + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
                 /\ (forall A n a, In (A, n) LBy -> A <= a < A + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
                 /\ L5.defined M2 (S - 16) 16
                 /\ L5C.hpres L LB S SCR_OPMOD [(S, 64); (L5.bo_data S by_, 8 * L5.bo_cap by_)] M0 M2).
    { destruct g as [|A cap].
      - destruct GP as (_ & _ & _ & _ & FB2 & MG2).
        assert (K2: forall a, 0 <= a < 2 ^ 64 -> ~ (S + 32 <= a < S + 32 + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a Ha Hn. apply FB2. apply outside1. rewrite BG.unsigned_lit by exact Ha. exact Hn. }
        split. { intros a Ha Hn. apply K2. flia. exact Hn. }
        split. { intros A n a Hin Ha. pose proof (LBdef _ _ _ _ HH A n Hin) as (_ & (Alo & _) & Ahi & _). apply K2. clear - Ha Alo Ahi SPT SLO'; unfold hl_ceil in *; lia. clear - Ha Ahi SLO'; unfold hl_ceil in *; lia. }
        split. { eapply L5.defined_grows. exact MG2. eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. }
        eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD _ M0 M M2 S SCR_OPMOD [(S, 64); (L5.bo_data S by_, 8 * L5.bo_cap by_)]). exact HP.
        + eapply (L5HP.hpres_piece L LB S SCR_OPMOD _ M M2 (fun a => S + 32 <= a < S + 32 + 32)). exact K2.
          { intros a KA C. apply (L5HP.outside_in _ _ S 64 (L5HP.kept_outside_W _ _ _ _ _ _ KA)). cbn. left; reflexivity. clear - C; lia. }
          rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG2. exact SCR. exact MG2.
        + intros a KA; exact KA. + intros b Hb; exact Hb. + exact CEIL. + flia. + rewrite SCR_OPMOD_val; clear; lia. + exact EV4. + flia.
      - destruct GP as (_ & _ & _ & _ & _ & _ & _ & HP2).
        split. { intros a Ha Hn. apply (kept_above M M2 _ (S - 16) COPY_SCR _ a HP2). fsclia. rewrite COPY_SCR_val; clear; lia. flia. exact Ha. apply outside1. exact Hn. }
        split. { intros A' n a Hin Ha. pose proof (LBdef _ _ _ _ HH A' n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO' in Aimg.
                 apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; unfold hl_ceil in *; lia.
                 rewrite EV; clear - Aimg Ha; lia. apply outside1. clear - Ha Ahi SLO'; unfold hl_ceil in *; lia. }
        split. { eapply (cdef_above M M2 _ (S - 16) COPY_SCR _ (S - 16) 16 HP2). fsclia. rewrite COPY_SCR_val; clear; lia. flia. clear; lia. flia.
                 eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. }
        eapply (L5HP.hpres_trans L LB _ S SCR_OPMOD _ M0 M M2 (S - 16) COPY_SCR [(S + 32, 32)]). exact HP. exact HP2.
        + intros a KA. eapply L5HP.kept_mono. exact KA. exact SUBLB. fsclia. clear; lia.
          intros OW r [<-|[]]. unfold L5.in_rng; cbn. intros C. apply (OW (S, 64)). cbn. left; reflexivity. unfold L5.in_rng; cbn. clear - C; lia.
        + exact SUBLB. + exact CEIL. + flia. + rewrite SCR_OPMOD_val; clear; lia. + exact EV4. + flia. }
    destruct KA2 as (KA2 & KB2 & D16 & HPF).
    (* [comment removed for export] *)
    assert (WF16': L5.writable RSEGS M2 (S - 16) 16). { apply (L5C.writable_of_defined RSEGS). exact D16. flia. flia. }
    pose proof (dofu3_conc fx2 R2 M2 (VF S 0 0 (U R0 1) (U R0 8))) as P. cbn [VF] in P.
    destruct (P ltac:(flia) ltac:(unfold U; apply BL.bvu_range) ltac:(unfold U; apply BL.bvu_range)
                ltac:(rewrite (preserved_sregs R1 R2 2 RP2) by inl; kreg K1 2%nat H2) ltac:(flia) A16 WF16'
                ltac:(eapply u64_at_agree1; [intros i Hi; apply KA2; flia | flia | flia | exact T1])
                ltac:(eapply u64_at_agree1; [intros i Hi; apply KA2; flia | flia | flia | exact T8]))
      as (fx3 & R3 & M3 & _ & FR3 & _ & (MS3 & K3 & B1 & B2 & B8)). clear P.
    pose proof (mem_eq M2 M3 FR3) as EM3. subst M3. rewrite UR01' in B1.
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2.
    { eapply msteps_trans. exact MS3. apply (BDU.ret_to fx3 R3 M2 OPF_RETI W_20d2c OPMOD2_RET F_20d2c eq_refl D_20d2c B1). unfold OPMOD2_RET; clear; lia. reflexivity. }
    apply (KN fx3 R3 M2 model2 LB2 cr2).
    + split.
      { apply preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|Hi]. { rewrite B2. symmetry. exact G2. }
        destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by inl. rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. rewrite H3. symmetry. exact G3. }
        destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. rewrite H4. symmetry. exact G4. }
        destruct Hi as [<-|Hi]. { rewrite B8. unfold U. apply Z_to_bv_bv_unsigned. }
        repeat (destruct Hi as [<-|Hi]; [ rewrite K3 by inl; rewrite (preserved_sregs R1 R2 _ RP2) by inl; rewrite K1 by inl; apply HRS; inl |]). destruct Hi. }
      split.
      { exists by', wy', LBy.
        assert (OBY2: L5.big_at RSEGS M2 S by'). { eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KA2; flia. flia. flia. }
        assert (OLY2: L5C.obj_limbs RSEGS M2 by' wy').
        { eapply obj_limbs_agree1. 3: exact OLY.
          - intros cap q E i Hi. apply (KB2 q (8 * cap) i). apply INY. exact E. pose proof OLY as (Ln & _). rewrite Ln in Hi.
            rewrite E in YST. destruct YST as (_ & _ & _ & Hlc & _). clear - Hi Hlc; lia.
          - intros cap q E. pose proof OLY as (Ln & _). rewrite Ln. rewrite E in YST. destruct YST as (_ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). clear - Hlc Hcap Qlo Qhi; lia. }
        split. exact OBY2. split. exact OLY2.
        split. { destruct (L5.bo_st by_) as [v0 v1|cy qy]; destruct (L5.bo_st by') as [w0 w1|cap q] eqn:E; try exact STM.
                 - destruct STM as (Ec & EL & (BR & BA & BD)). split. exact Ec. split. exact EL. split. exact BR. split. exact BA.
                   exact (proj1 (LBdef _ _ _ _ HH2 q 64 ltac:(destruct g as [|A' cap']; [destruct GP as (_ & -> & _) | destruct GP as (_ & _ & -> & _)]; [|right]; rewrite EL; left; subst cap; reflexivity))).
                 - destruct STM as (Ec & Eq & EL & D). split. exact Ec. split. exact Eq. split. exact EL.
                   eapply defined_agree1. 2: exact D. intros i Hi. apply (KB2 qy (8 * cy) i). subst cap q. apply INY. reflexivity. exact Hi. }
        (* [comment removed for export] *)
        destruct g as [|A cap].
        - destruct GP as (DYF & -> & -> & OC2 & FB2 & _).
          exists (L5.BO (copy_fb fdo (L5.bo_fb by') false) (L5.bo_len by') (L5.bo_st by')).
          split. exact OC2. split. { pose proof OLY2 as (Ln & Fw & LA). split. exact Ln. split. exact Fw. cbn [L5.bo_st L5.bo_len]. exact LA. }
          split. reflexivity. split. { cbn [L5.bo_fb]. rewrite DYF. reflexivity. }
          cbn [L5.bo_st]. unfold L5.bo_dyn in DYF. destruct (L5.bo_st by') as [w0 w1|cap q] eqn:E. repeat split; reflexivity.
          exfalso. destruct YST as (T & _). rewrite T in DYF. discriminate DYF.
        - destruct GP as (DYT & Hcap & -> & -> & FBc & OC2 & OLc & _).
          exists (L5.BO (copy_fb fdo (L5.bo_fb by') true) (L5.bo_len by') (L5.BDyn cap A)).
          split. exact OC2. split. exact OLc. split. reflexivity. split. { cbn [L5.bo_fb]. rewrite DYT. reflexivity. }
          cbn [L5.bo_st]. unfold L5.bo_dyn in DYT. unfold L5.bo_cap in Hcap. destruct (L5.bo_st by') as [w0 w1|cap' q] eqn:E.
          { exfalso. destruct YST as (T & _). rewrite T in DYT. discriminate DYT. }
          subst cap. split. reflexivity. split. reflexivity. exact FBc. }
      split. { destruct AOK1 as [OBa SGa]. split. 2: exact SGa. eapply big_at_agree1. 4: exact OBa. intros i Hi; apply KA2; subst ao; flia. subst ao; flia. subst ao; flia. }
      split. { destruct g as [|A cap]. { destruct GP as (_ & _ & -> & _). exact (CRA2 false). }
               destruct GP as (DYT & Hcap & _ & -> & _). subst cap. exact (CRA2 true). }
      exact HPF.
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
    + exact HH2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem opmodf2_call : srealizes RSEGS SCFG (cfg R0 OPMODF M0 model0) K.
Proof.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof MOK0 as (Mh & Ml & _). pose proof SCR0 as SCR. pose proof ERRNOV as EV. pose proof ERRNO as EV4.
  pose proof IMG as IMG'. pose proof IMGLO as IMGLO'. pose proof CAPR as CB. pose proof KPOS as KP. pose proof BPOS as BP.
  pose proof YOK as (YB0 & OLY0 & RED & BLK). pose proof AOK as [OBa SGa].
  assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH0 A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
  assert (E10: getr R0 (reg 10) = Z_to_bv 64 (S + 32)). { replace (reg 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact G10. }
  assert (E11: getr R0 (reg 11) = Z_to_bv 64 S). { replace (reg 11) with (11%bv : bv 5) by (apply bv_eq; reflexivity). exact G11. }
  assert (E12: getr R0 (reg 12) = Z_to_bv 64 ao). { replace (reg 12) with (12%bv : bv 5) by (apply bv_eq; reflexivity). exact G12. }
  assert (U11: bv_unsigned (getr R0 (reg 11)) = S). { rewrite E11. apply BG.unsigned_lit. flia. }
  (* [comment removed for export] *)
  assert (YBLK: forall cy qy, L5.bo_st by_ = L5.BDyn cy qy ->
            In (qy, 8 * cy) LB /\ L5.defined M0 qy (8 * cy) /\ 4096 <= qy /\ qy + 8 * cy <= hl_ceil L /\ Z.of_nat (L5.bo_len by_) + 1 <= cy /\ 1 <= cy).
  { intros cy qy E. rewrite E in BLK. destruct BLK as (INB & DB & LC). pose proof (LBdef _ _ _ _ HH0 qy (8 * cy) INB) as (_ & (Blo & _) & Bhi & _).
    unfold L5.big_at in YB0. rewrite E in YB0. destruct YB0 as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _).
    split. exact INB. split. exact DB. split. exact Blo. split. exact Bhi. split. exact LC. clear - Hcap; lia. }
  (* [comment removed for export] *)
  pose proof (dofu1_conc fx0 R0 M0 (VF S 0 0 0 0)) as P. cbn [VF] in P.
  destruct (P ltac:(flia) ltac:(exact G2) ltac:(flia) A16
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR | clear; lia | clear; lia] | flia | flia])
              ltac:(rewrite U11; flia) ltac:(rewrite U11; unfold aligned; exact (mod16_mod8 _ A16)))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & (MS1 & K1 & A1 & A2 & A8 & A10 & A11 & C16 & C8)). clear P.
  rewrite E10 in A8. rewrite E11 in A10. rewrite E12 in A11.
  change (L5.u64_at RSEGS M1 (S - 16) (U R0 8)) in C16. change (L5.u64_at RSEGS M1 (S - 8) (U R0 1)) in C8.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  assert (SCR1: L5.defined M1 (S - 10240) 10240). { eapply L5.defined_grows. exact MG1. exact SCR. }
  pose proof (dopu1_conc fx1 R1 M1 (VP (S - 16) 0 0 0 0 0 0)) as P. cbn [VP] in P.
  destruct (P ltac:(flia) A2 ltac:(flia) ltac:(replace (S - 16) with (S + (-1) * 16) by (clear; lia); unfold aligned; rewrite Z_mod_plus_full; exact A16)
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR1 | clear; lia | clear; lia] | flia | flia]))
    as (fx2 & R2 & M2 & MG2 & _ & FR2 & (MS2 & K2 & B1 & B2 & B8 & B12 & B13 & B14 & C40 & C48 & C56 & C64 & C32 & C24)). clear P.
  rewrite A8 in C32. rewrite BG.unsigned_lit in C32 by flia. rewrite A1 in C24. rewrite BG.unsigned_lit in C24 by (clear; lia).
  rewrite A10 in B8, B13.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
  assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> M2 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha Hn. rewrite FR2. apply FR1. exact Ha. clear - Hn; lia. exact Ha. clear - Hn; lia. }
  assert (KUP: forall i, S <= i < S + 240 -> M2 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)). { intros i Hi. apply KA; clear - Hi SLO SHI; lia. }
  assert (K16: forall i, S - 16 <= i < S -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)). { intros i Hi. apply FR2; clear - Hi SLO SHI; lia. }
  pose proof (mem_grows_trans _ _ _ MG1 MG2) as MG.
  assert (HH2: hi_heap HI LB cr M2 (m_vmmaps model0)). { eapply (hi_heap_stackwrite LB cr M0 M2 _ (S - 64) S). exact HH0. exact KA. flia. flia. flia. exact MG. }
  assert (SCR2: L5.defined M2 (S - 10240) 10240). { eapply L5.defined_grows. exact MG. exact SCR. }
  (* [comment removed for export] *)
  eapply (DIVO2 fx2 R2 M2 model0 K LB cr S (S - 64) ao fba (S - 64) DIV_RET by_ wy HH2 MOK0 HK0).
  - rewrite r10. rewrite (K2 10%nat) by inl. exact A10.
  - rewrite r11. rewrite (K2 11%nat) by inl. exact A11.
  - rewrite r12. rewrite B12. f_equal. clear; lia.
  - rewrite r13. exact B13.
  - rewrite r14. exact B14.
  - rewrite r1. exact B1.
  - unfold DIV_RET. split. clear; lia. reflexivity.
  - rewrite r2. rewrite B2. f_equal. clear; lia.
  - rewrite r3. rewrite (K2 3%nat) by inl. rewrite (K1 3%nat) by inl. rewrite <- r3. exact G3.
  - rewrite r4. rewrite (K2 4%nat) by inl. rewrite (K1 4%nat) by inl. rewrite <- r4. exact G4.
  - split. { replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. rewrite DIVO2_SCR_val; flia. split. flia. split. exact SPT. rewrite DIVO2_SCR_val. eapply L5.defined_sub. exact SCR2. clear; lia. clear; lia.
  - intros i Hi. rewrite KA. exact (IMGC i Hi). clear - Hi; lia. clear - Hi SLO; lia.
  - (* [comment removed for export] *)
    split. { eapply big_at_agree1. 4: exact YB0. intros i Hi; apply KUP; flia. flia. flia. }
    split. { pose proof OLY0 as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2.
             destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY in YL3 |- *. exact YL3.
             destruct (YBLK cy qy ltac:(first [exact EY | reflexivity])) as (_ & _ & Ylo & Yhi & Ylc & _).
             eapply L5C.limbs_at_agree. 4: exact YL3. 2: flia. 2: rewrite YL1; unfold hl_ceil in *; flia.
             intros i Hi. rewrite YL1 in Hi. apply KA. unfold hl_ceil in *; flia. clear - Hi Yhi SLO' Ylc; unfold hl_ceil in *; lia. }
    split. exact RED.
    destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY. exact I. destruct (YBLK cy qy ltac:(first [exact EY | reflexivity])) as (INY & DYq & _ & _ & LNY & _).
    split. exact INY. split. eapply L5.defined_grows. exact MG. exact DYq. clear - LNY; lia.
  - exact LEN1.
  - exact CAPY.
  - exact (mod16_mod8 _ A16).
  - clear; lia.
  - flia.
  - eapply L5.writable_grows. exact MG. eapply L5.writable_sub. exact WRY. clear; lia. clear; lia.
  - intros cap q E. eapply L5.writable_grows. exact MG. exact (WRB cap q E).
  - split. 2: exact SGa. eapply big_at_agree1. 4: exact OBa. intros i Hi; apply KUP; subst ao; flia. subst ao; flia. subst ao; flia.
  - subst ao. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - subst ao; clear; lia.
  - subst ao; flia.
  - (* [comment removed for export] *)
    unfold zero_obj, L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exactA C64. split. clear; lia. split. exactA C56.
    split. reflexivity. split. exactA C48. split. exactA C40. split. clear; lia. clear; lia.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - clear; lia.
  - flia.
  - eapply L5.writable_grows. exact MG. apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR. clear; lia. clear; lia. flia. flia.
  - left. subst ao; clear; lia.
  - clear; lia.
  - subst ao; clear; lia.
  - pose proof CR as [C1 C2]. unfold OPMOD2_K, opmodf2_bytes in C1, C2. unfold credit_for, DIVO2_K, divO2_bytes. subst capy. split; clear - C1 C2 KP BP CB; lia.
  - (* [comment removed for export] *)
    intros fx3 R3 M3 model3 LB3 cr3 POST MBV3 HH3.
    pose proof (model_ok_but_vm _ _ MOK0 MBV3) as MOK3. pose proof MOK3 as (Mh3 & Ml3 & _).
    destruct POST as (RP3 & (LBy & YA & QA) & AOK3 & CRA3 & HP3).
    pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP3) as SCR3. rewrite DIVO2_SCR_val in SCR3.
    (* [comment removed for export] *)
    assert (KTOP: forall a, S - 32 <= a < S -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP3). apply L5C.kept_stack. rewrite DIVO2_SCR_val; flia. rewrite DIVO2_SCR_val; clear; lia. flia. exact EV4. exact (proj1 SPT).
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
      apply L5C.outside_cons. { unfold L5.in_rng; cbn [fst snd]. unfold L5.bo_data, L5.bo_cap. destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY. flia.
                                destruct (YBLK cy qy ltac:(first [exact EY | reflexivity])) as (_ & _ & _ & Bhi & _). unfold hl_ceil in Bhi. flia. }
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
    assert (T1: L5.u64_at RSEGS M3 (S - 8) (U R0 1)). { eapply u64_at_agree1. 4:{ eapply u64_at_agree1. 4: exact C8. intros i Hi; apply K16; flia. flia. flia. } intros i Hi; apply KTOP; flia. flia. flia. }
    assert (T8: L5.u64_at RSEGS M3 (S - 16) (U R0 8)). { eapply u64_at_agree1. 4:{ eapply u64_at_agree1. 4: exact C16. intros i Hi; apply K16; flia. flia. flia. } intros i Hi; apply KTOP; flia. flia. flia. }
    assert (T24: L5.u64_at RSEGS M3 (S - 24) OPF_BACK). { eapply u64_at_agree1. 4: exactA C24. intros i Hi; apply KTOP; flia. flia. flia. }
    assert (T32: L5.u64_at RSEGS M3 (S - 32) (S + 32)). { eapply u64_at_agree1. 4: exactA C32. intros i Hi; apply KTOP; flia. flia. flia. }
    assert (E2: getr R3 (reg 2) = Z_to_bv 64 (S - 16 - 48)). { rewrite (preserved_sregs R2 R3 2 RP3) by inl. exact B2. }
    assert (E8: getr R3 (reg 8) = Z_to_bv 64 S). { rewrite (preserved_sregs R2 R3 8 RP3) by inl. exact B8. }
    assert (E3: getr R3 (reg 3) = Z_to_bv 64 GP). { rewrite (preserved_sregs R2 R3 3 RP3) by inl. rewrite (K2 3%nat) by inl. rewrite (K1 3%nat) by inl. rewrite <- r3. exact G3. }
    assert (E4: getr R3 (reg 4) = Z_to_bv 64 TP). { rewrite (preserved_sregs R2 R3 4 RP3) by inl. rewrite (K2 4%nat) by inl. rewrite (K1 4%nat) by inl. rewrite <- r4. exact G4. }
    assert (HRS3: forall i, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg i) = getr R0 (reg i)).
    { intros i Hi. rewrite (preserved_sregs R2 R3 i RP3). rewrite K2. apply K1.
      revert Hi; apply (L5K.incl_b _ KS_dofu1); vm_compute; reflexivity. revert Hi; apply (L5K.incl_b _ KS_dopu1); vm_compute; reflexivity.
      revert Hi; apply (L5K.incl_b _ L5DIVEARLYU.cs_all); vm_compute; reflexivity. }
    assert (A16': aligned (S - 16) 16). { unfold aligned. replace (S - 16) with (S + (-1) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    assert (D48: L5.defined M2 (S - 64) 48). { eapply L5.defined_sub. exact SCR2. clear; lia. clear; lia. }
    assert (W48: L5.writable RSEGS M3 (S - 16 - 48) 48).
    { apply (L5C.writable_of_defined RSEGS). 2: flia. 2: flia. intros i Hi. destruct (Z_lt_le_dec i 32) as [X|X].
      - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (S - 16 - 48 + i) HP3). flia. right; left. unfold hl_ceil. rewrite DIVO2_SCR_val. flia. unfold in_errno; rewrite EV; flia.
        replace (S - 16 - 48 + i) with (S - 64 + i) by (clear; lia). exact (D48 i Hi).
      - rewrite KTOP by flia. replace (S - 16 - 48 + i) with (S - 64 + i) by (clear; lia). exact (D48 i Hi). }
    (* [comment removed for export] *)
    assert (D3: L5.defined M3 (S - 10240) 10240).
    { replace 10240 with (736 + (9440 + 64)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
      { eapply (cdef_below M2 M3 _ (S - 64) DIVO2_SCR _ (S - 10240) 736 HP3). flia. rewrite DIVO2_SCR_val; clear; lia. rewrite DIVO2_SCR_val; clear; lia. flia. flia.
        eapply L5.defined_sub. exact SCR2. clear; lia. clear; lia. }
      apply L5C.defined_app. 3: clear; lia. { exactA SCR3. }
      eapply (cdef_above M2 M3 _ (S - 64) DIVO2_SCR _ _ 64 HP3). rewrite DIVO2_SCR_val; fsclia. rewrite DIVO2_SCR_val; clear; lia. flia. clear; lia. flia.
      eapply L5.defined_sub. exact SCR2. clear; lia. clear; lia. }
    (* [comment removed for export] *)
    assert (FDO3: L5.u8_at RSEGS M3 (S + 32) fdo).
    { eapply u8_at_agree1. 4:{ eapply u8_at_agree1. 4: exact FDO. intros i Hi; apply KUP; flia. flia. flia. }
      intros i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP3). apply L5C.kept_stack. rewrite DIVO2_SCR_val; flia. rewrite DIVO2_SCR_val; clear; lia. flia. exact EV4. exact (proj1 SPT).
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
      apply L5C.outside_cons. { unfold L5.in_rng; cbn [fst snd]. unfold L5.bo_data, L5.bo_cap. destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY. flia.
                                destruct (YBLK cy qy ltac:(first [exact EY | reflexivity])) as (_ & _ & _ & Bhi & _). unfold hl_ceil in Bhi. flia. }
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. flia. flia. }
    (* [comment removed for export] *)
    assert (HP03: L5C.hpres L LB S SCR_OPMOD [(S, 64); (L5.bo_data S by_, 8 * L5.bo_cap by_)] M0 M3).
    { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD _ M0 M2 M3 (S - 64) DIVO2_SCR). 2: exact HP3.
      + eapply (L5HP.hpres_piece L LB S SCR_OPMOD _ M0 M2 (fun a => S - 64 <= a < S)). exact KA.
        { intros a KA' C. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD _ a KA' LBceil CEIL _ _). rewrite IMG'; unfold hl_ceil; clear - SPT; lia. rewrite SCR_OPMOD_val. clear - C; lia. }
        rewrite SCR_OPMOD_val. exact SCR2. exact MG.
      + intros a KA'. eapply L5HP.kept_mono. exact KA'. intros b Hb; exact Hb. rewrite SCR_OPMOD_val, DIVO2_SCR_val; clear; lia. clear; lia.
        intros OW. pose proof (L5HP.kept_not_in_scratch L LB S SCR_OPMOD _ a KA' LBceil CEIL ltac:(rewrite IMG'; unfold hl_ceil; clear - SPT; lia)) as NS. rewrite SCR_OPMOD_val in NS.
        apply L5C.outside_cons. { intros C. apply (OW (S, 64)). cbn. left; reflexivity. unfold L5.in_rng in C |- *; cbn in C |- *. clear - C; lia. }
        apply L5C.outside_cons. exact (OW _ ltac:(right; left; reflexivity)).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; clear - NS; lia. apply L5C.outside_nil.
      + intros b Hb; exact Hb. + exact CEIL. + flia. + rewrite SCR_OPMOD_val; clear; lia. + exact EV4. + exact (proj1 SPT). }
    destruct YA as (by' & wy' & OBY & OLY & STM).
    assert (SUBLB: forall b, In b LB -> In b LBy).
    { intros b Hb. destruct (L5.bo_st by_) as [v0 v1|cy qy]; destruct (L5.bo_st by') as [w0 w1|cap q]; try contradiction.
      - rewrite STM. exact Hb. - destruct STM as (_ & -> & _). right. exact Hb. - destruct STM as (_ & _ & -> & _). exact Hb. }
    destruct QA as (fbq & nq & stq & OBQ & QST).
    pose proof OBQ as (Qf & Qfr & Ql & QSTO). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qf, Qfr, Ql, QSTO.
    destruct stq as [q0 q1|cq p].
    + (* [comment removed for export] *)
      subst LB3. destruct QSTO as (Qb0 & _).
      pose proof (dopu2i_conc fx3 R3 M3 (VP (S - 16) S fbq 0 0 OPF_BACK (S + 32))) as P. cbn [VP] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(clear - Qfr; lia) ltac:(unfold OPF_BACK; clear; lia) ltac:(flia)
                  E2 E8 ltac:(flia) A16' W48 ltac:(exactA T24) ltac:(exactA T32) ltac:(exactA Qf) ltac:(clear - Qfr; lia) Qb0)
        as (fx6 & R6 & M6 & _ & FR6 & _ & (MS6 & K6 & B1' & B2' & B8' & B10')). clear P.
      pose proof (mem_eq M3 M6 FR6) as EM. subst M6.
      eapply (L5.cps_of_msteps RSEGS). exact Mh3. exact Ml3.
      { eapply msteps_trans. exact MS6. apply (BDU.ret_to fx6 R6 M3 0x224c4 W_224c4 OPF_BACK F_224c4 eq_refl D_224c4 B1'). unfold OPF_BACK; clear; lia. reflexivity. }
      apply (stage_FIN2 fx6 R6 M3 model3 cr3 by' wy' LBy).
      * exact B2'. * rewrite (K6 3%nat) by inl. exact E3. * rewrite (K6 4%nat) by inl. exact E4. * exact B8'. * exact B10'.
      * intros i Hi. rewrite K6. apply HRS3. exact Hi. revert Hi. apply (L5K.incl_b _ KS_dopu2i). vm_compute. reflexivity.
      * exact MBV3. * exact HH3.
      * exact CRA3.
      * rewrite SCR_OPMOD_val. exact D3. * exact T1. * exact T8.
      * exact OBY. * exact OLY. * exact STM. * exact FDO3. * exact AOK3. * exact HP03.
    + (* [comment removed for export] *)
      destruct QST as (-> & FBq & CQ). destruct QSTO as (Qb1 & C16q & C24q & Hlc & Hcap & P8 & Plo & Phi & _).
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBq) as (Plo' & Pimg & _ & _ & Phi'). unfold hl_ceil in Phi'.
      pose proof (dopu2d_conc fx3 R3 M3 (VP (S - 16) S fbq p cq OPF_BACK (S + 32))) as P. cbn [VP] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(clear - Qfr; lia) ltac:(clear - Plo Phi Hcap; lia) ltac:(clear - Hcap; lia) ltac:(unfold OPF_BACK; clear; lia) ltac:(flia)
                  E2 E8 ltac:(flia) A16' W48 ltac:(exactA T24) ltac:(exactA T32) ltac:(exactA Qf) ltac:(clear - Qfr; lia) Qb1
                  ltac:(exactA C24q) ltac:(clear - Plo Phi Hcap; lia) ltac:(exactA C16q) ltac:(clear - Hcap; lia))
        as (fx6 & R6 & M6 & _ & FR6 & _ & (MS6 & K6 & B1' & B10' & B11')). clear P.
      pose proof (mem_eq M3 M6 FR6) as EM. subst M6.
      eapply (L5.cps_of_msteps RSEGS). exact Mh3. exact Ml3. exact MS6.
      eapply (OPDEL fx6 R6 M3 model3 K ((p, 8 * cq) :: LBy) cr3 p (8 * cq) (S - 64) 0x224b4 HH3 MOK3 HK0).
      * left. reflexivity.
      * rewrite r10. exact B10'.
      * rewrite r1. exact B1'.
      * split. clear; lia. reflexivity.
      * rewrite r2. rewrite (K6 2%nat) by inl. rewrite E2. f_equal. clear; lia.
      * rewrite r4. rewrite (K6 4%nat) by inl. exact E4.
      * split. { replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
        split. rewrite OPDEL_SCR_val; flia. split. flia. split. exact SPT. rewrite OPDEL_SCR_val. eapply L5.defined_sub. exact D3. clear; lia. clear; lia.
      * (* [comment removed for export] *)
        intros fx7 R7 M7 model7 RP7 HP7 MBV7 HH7. rewrite lb_remove_head in HP7, HH7.
        pose proof (model_ok_but_vm _ _ MOK3 MBV7) as MOK7. pose proof MOK7 as (Mh7 & Ml7 & _).
        assert (KA7: forall a, S - 64 <= a < 2 ^ 64 -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
        { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP7). apply L5C.kept_stack. rewrite OPDEL_SCR_val; flia. rewrite OPDEL_SCR_val; clear; lia. flia. exact EV4. exact (proj1 SPT). apply L5C.outside_nil. }
        assert (KB7: forall A n a, In (A, n) LBy -> A <= a < A + n -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
        { intros A n a Hin Ha. pose proof (LBdef _ _ _ _ HH7 A n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO' in Aimg.
          apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP7). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; unfold hl_ceil in *; lia. rewrite EV. clear - Aimg Ha; lia. apply L5C.outside_nil. }
        assert (KD7: forall A n, In (A, n) LBy -> L5.defined M3 A n -> L5.defined M7 A n).
        { intros A n Hin D. eapply defined_agree1. intros i Hi. apply (KB7 A n). exact Hin. exact Hi. exact D. }
        assert (D7: L5.defined M7 (S - 10240) 10240).
        { replace 10240 with (1952 + (8224 + 64)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
          { eapply (cdef_below M3 M7 _ (S - 64) OPDEL_SCR _ (S - 10240) 1952 HP7). flia. rewrite OPDEL_SCR_val; clear; lia. rewrite OPDEL_SCR_val; clear; lia. flia. flia.
            eapply L5.defined_sub. exact D3. clear; lia. clear; lia. }
          apply L5C.defined_app. 3: clear; lia.
          { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP7) as D. rewrite OPDEL_SCR_val in D. exactA D. }
          eapply (cdef_above M3 M7 _ (S - 64) OPDEL_SCR _ _ 64 HP7). rewrite OPDEL_SCR_val; fsclia. rewrite OPDEL_SCR_val; clear; lia. flia. clear; lia. flia.
          eapply L5.defined_sub. exact D3. clear; lia. clear; lia. }
        assert (W48': L5.writable RSEGS M7 (S - 16 - 48) 48). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact D7. clear; lia. clear; lia. flia. flia. }
        pose proof (dopu3_conc fx7 R7 M7 (VP (S - 16) S 0 0 0 OPF_BACK (S + 32))) as P. cbn [VP] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(unfold OPF_BACK; clear; lia) ltac:(flia)
                    ltac:(rewrite (preserved_sregs R6 R7 2 RP7) by inl; rewrite (K6 2%nat) by inl; exact E2)
                    ltac:(rewrite (preserved_sregs R6 R7 8 RP7) by inl; rewrite (K6 8%nat) by inl; exact E8)
                    ltac:(flia) A16' W48'
                    ltac:(eapply u64_at_agree1; [intros i Hi; apply KA7; flia | flia | flia | exactA T24])
                    ltac:(eapply u64_at_agree1; [intros i Hi; apply KA7; flia | flia | flia | exactA T32]))
          as (fx8 & R8 & M8 & _ & FR8 & _ & (MS8 & K8 & B1'' & B2'' & B8'' & B10'')). clear P.
        pose proof (mem_eq M7 M8 FR8) as EM. subst M8.
        eapply (L5.cps_of_msteps RSEGS). exact Mh7. exact Ml7.
        { eapply msteps_trans. exact MS8. apply (BDU.ret_to fx8 R8 M7 0x224c4 W_224c4 OPF_BACK F_224c4 eq_refl D_224c4 B1''). unfold OPF_BACK; clear; lia. reflexivity. }
        apply (stage_FIN2 fx8 R8 M7 model7 cr3 by' wy' LBy).
        -- exact B2''.
        -- rewrite (K8 3%nat) by inl. rewrite (preserved_sregs R6 R7 3 RP7) by inl. rewrite (K6 3%nat) by inl. exact E3.
        -- rewrite (K8 4%nat) by inl. rewrite (preserved_sregs R6 R7 4 RP7) by inl. rewrite (K6 4%nat) by inl. exact E4.
        -- exact B8''. -- exact B10''.
        -- intros i Hi. rewrite K8. rewrite (preserved_sregs R6 R7 i RP7). rewrite K6. apply HRS3. exact Hi.
           revert Hi; apply (L5K.incl_b _ KS_dopu2d); vm_compute; reflexivity. revert Hi; apply (L5K.incl_b _ L5DIVEARLYU.cs_all); vm_compute; reflexivity. revert Hi; apply (L5K.incl_b _ KS_dopu3); vm_compute; reflexivity.
        -- exact (L5C.model_but_vm_trans _ _ _ MBV3 MBV7).
        -- exact HH7.
        -- exact CRA3.
        -- rewrite SCR_OPMOD_val. exact D7.
        -- eapply u64_at_agree1. 4: exact T1. intros i Hi; apply KA7; flia. flia. flia.
        -- eapply u64_at_agree1. 4: exact T8. intros i Hi; apply KA7; flia. flia. flia.
        -- eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KA7; flia. flia. flia.
        -- pose proof OBY as OBY'. unfold L5.big_at in OBY'. destruct OBY' as (_ & _ & _ & YST).
           eapply obj_limbs_agree1. 3: exact OLY.
           ++ intros cap q E i Hi. pose proof OLY as (Ln & _). rewrite Ln in Hi. rewrite E in YST. destruct YST as (_ & _ & _ & Hlc' & _).
              apply (KB7 q (8 * cap) i). 2: clear - Hi Hlc'; lia.
              rewrite E in STM. destruct (L5.bo_st by_) as [v0 v1|cy qy] eqn:EY. destruct STM as (-> & -> & _). left; reflexivity. destruct STM as (-> & -> & -> & _). exact (proj1 (YBLK cy qy eq_refl)).
           ++ intros cap q E. pose proof OLY as (Ln & _). rewrite Ln. rewrite E in YST. destruct YST as (_ & _ & _ & Hlc' & Hcap' & _ & Qlo & Qhi & _). clear - Hlc' Hcap' Qlo Qhi; lia.
        -- destruct (L5.bo_st by_) as [v0 v1|cy qy] eqn:EY; destruct (L5.bo_st by') as [w0 w1|cap q] eqn:E; try exact STM.
           ++ destruct STM as (Ec & EL & (BR & BA & BD)). split. exact Ec. split. exact EL. split. exact BR. split. exact BA.
              apply (KD7 q 64). rewrite EL. left. reflexivity. exact BD.
           ++ destruct STM as (Ec & Eq & EL & D). split. exact Ec. split. exact Eq. split. exact EL. apply (KD7 qy (8 * cy)). rewrite EL. exact (proj1 (YBLK cy qy eq_refl)). exact D.
        -- eapply u8_at_agree1. 4: exact FDO3. intros i Hi; apply KA7; flia. flia. flia.
        -- destruct AOK3 as [OBa3 SGa3]. split. 2: exact SGa3. eapply big_at_agree1. 4: exact OBa3. intros i Hi; apply KA7; subst ao; flia. subst ao; flia. subst ao; flia.
        -- eapply (L5HP.hpres_trans L LB LBy S SCR_OPMOD _ M0 M3 M7 (S - 64) OPDEL_SCR []). exact HP03. exact HP7.
           ++ intros a KA'. eapply L5HP.kept_mono. exact KA'. exact SUBLB. rewrite OPDEL_SCR_val, SCR_OPMOD_val; clear; lia. clear; lia. intros _; apply L5C.outside_nil.
           ++ exact SUBLB. ++ exact CEIL. ++ flia. ++ rewrite SCR_OPMOD_val; clear; lia. ++ exact EV4. ++ exact (proj1 SPT).
Qed.

End Call.
End WithHeap.

(* [comment removed for export] *)
Theorem opmodf2_ok (L : heap_layout) (HI : heap_iface) :
  layout L -> heap_iface_ok L SCFG HI -> 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L ->
  copya_spec L HI -> assign_spec L HI -> resize_spec L HI -> opdel_sized_spec L HI -> copy_spec L HI -> unnorm_spec L HI -> divloop_run_stmt ->
  opmodf2_spec L HI.
Proof.
  intros LY HIok KPOS BPOS COPYA ASSIGN RESIZE OPDEL COPYC UNNORM DIVLOOP.
  intros fx R M model K LB cr S ao fba fdo by_ wy capy HH MOK HK G10 G11 G12 EAO G1 G2 G3 G4 STK HS WRY WRB IMGC YOK LEN1 CAPY FDO FDOR AOK CR KN.
  eapply (opmodf2_call L HI); eassumption.
Qed.

End SCFG_1.
End L5OPMOD2U.
