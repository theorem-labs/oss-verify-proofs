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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore AsanAcct
     Src0_code_21134_21d54 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigLinkShl L5Defs L5CoreKit L5Kn
     L5Core L5CoreSpecs L5CoreKitS L5Words L5WordsB L5Hp L5Norm L5NormOk L5Cmp
     L5DivSpecs L5DivParts L5DivNP L5OpModP L5DivO2S L5DivTail L5DivO2A L5DivO2K.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5OPMOD2.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5OPMODP. Import L5DO2S.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Local Notation r1 := L5DIVO2A.r1. Local Notation r2 := L5DIVO2A.r2. Local Notation r3 := L5DIVO2A.r3. Local Notation r4 := L5DIVO2A.r4.
Local Notation r10 := L5DIVO2A.r10. Local Notation r11 := L5DIVO2A.r11. Local Notation r12 := L5DIVO2A.r12. Local Notation r13 := L5DIVO2A.r13.
Local Notation r14 := L5DIVO2A.r14.
Local Notation preserved_sregs := L5DIVO2A.preserved_sregs.
Local Notation preserved_by_index := L5DIVO2A.preserved_by_index.
Local Notation u64_at_agree1 := L5DIVO2A.u64_at_agree1.
Local Notation u8_at_agree1 := L5DIVO2A.u8_at_agree1.
Local Notation big_at_agree1 := L5DIVO2A.big_at_agree1.
Local Notation limbs_at_agree1 := L5DIVO2A.limbs_at_agree1.
Local Notation defined_agree1 := L5DIVO2A.defined_agree1.
Local Notation model_ok_but_vm := L5DIVO2A.model_ok_but_vm.
Local Notation mem_eq := L5DIVO2A.mem_eq.
Local Notation mod16_mod8 := L5DIVO2A.mod16_mod8.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

Lemma SCR_OPMOD_val : SCR_OPMOD = 10240. Proof. reflexivity. Qed.
Lemma DIVO2_SCR_val : DIVO2_SCR = 9264. Proof. reflexivity. Qed.
Lemma OPDEL_SCR_val : OPDEL_SCR = 8224. Proof. reflexivity. Qed.
Local Ltac uSCR := rewrite ?SCR_OPMOD_val, ?DIVO2_SCR_val, ?OPDEL_SCR_val in *; unfold HEAP_STACK in *.

Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; lia.
Local Ltac fsclia := prune_impl; prune_disj; uSCR; lia.

Lemma segs_below : segs_below_b RSEGS 0x91000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma writable_defined_hi M a n : L5.writable RSEGS M a n -> L5KS.IMG_HI <= a -> 0 <= n -> a + n <= 2 ^ 64 -> L5.defined M a n.
Proof.
  intros W Hlo Hn Hhi i Hi. specialize (W i 1%nat ltac:(lia) ltac:(cbn; lia)). cbn [store_ok] in W.
  unfold wview in W. destruct (M (Z_to_bv 64 (a + i))) eqn:E. congruence.
  unfold L5KS.IMG_HI in Hlo. rewrite BG.unsigned_lit in W by lia. rewrite (find_segment1_none_above RSEGS 0x91000 (a + i) segs_below) in W by lia. discriminate W.
Qed.
Lemma lb_remove_head A n LB : lb_remove A ((A, n) :: LB) = LB.
Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.

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
Hypothesis UNNORM : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.                                   (* [comment removed for export] *)
Let CMP : L5CMP.cmp_spec := @L5CMP.cmp_ok _.
Let NORM : L5NORM.norm_spec L HI := L5NORMOK.norm_ok L HI LY HIok RESIZE.
Let DIVTAIL : divtail_stmt L HI := L5DIVTAIL.divtail_ok L HI LY HIok OPDEL.
Let DIVTAIL2 : L5DIVTAIL.divtail2_stmt L HI := L5DIVTAIL.divtail2_ok L HI LY HIok OPDEL.

Lemma IMG : hl_img_hi L = 0x91000. Proof. apply (ly_img_hi L LY). Qed.
Lemma IMGLO : hl_img_lo L = 0x10000. Proof. apply (ly_img_lo L LY). Qed.
Lemma ERRNO : hl_errno L + 4 <= 0x7fff7f800000. Proof. rewrite (ly_errno L LY). lia. Qed.
Lemma ERRNOV : hl_errno L = 0x70394. Proof. apply (ly_errno L LY). Qed.
Lemma LBhi LBx crx M VM : hi_heap HI LBx crx M VM -> forall b, In b LBx -> fst b + snd b <= (hl_sptop L - 8388608).
Proof. intros HH b Hb. exact (L5DIVO2A.LBhi L HI HIok LBx crx M VM HH b Hb). Qed.
Lemma LBdef LBx crx M VM : hi_heap HI LBx crx M VM -> forall A0 n, In (A0, n) LBx ->
  L5.defined M A0 n /\ (4096 <= A0 /\ (A0 + n <= hl_img_lo L \/ hl_img_hi L <= A0)) /\ A0 + n <= hl_ceil L /\ 0 < n /\ A0 mod 16 = 0.
Proof. intros HH A0 n Hin. exact (L5DIVO2A.LBdef L HI HIok LBx crx M VM HH A0 n Hin). Qed.

(* [comment removed for export] *)
Definition VP (S fq qp qc u1 u8 : Z) (j : nat) : Z :=
  match j with 2%nat => S | 33%nat => S | 36%nat => fq | 37%nat => qp | 38%nat => qc | 43%nat => u1 | 44%nat => u8 | _ => 0 end.

(* [comment removed for export] *)
Theorem opmod2_ok : opmod2_spec L HI.
Proof.
  assert (DIVO2: divO2_spec L HI). { apply (L5DIVO2K.divO2_ok L HI); assumption. }
  unfold opmod2_spec. intros fx R M model K LB cr S ao fba by_ wy HH MOK HK G10 G11 EAO G1 G2 G3 G4 STK HS WRY WRB IMGC YOK LEN1 CAPY AOK CR KN.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO. pose proof ERRNOV as ERRNOV.
  pose proof STK as (A16 & SLO & SHI & SPTOP & SCR0). rewrite SCR_OPMOD_val in SLO, SCR0.
  pose proof MOK as (Mh & Ml & _).
  pose proof YOK as (YB0 & OLY0 & RED & BLK).
  set (capy := L5.bo_cap by_) in *.
  assert (CAPR: 1 <= capy <= 268). { pose proof YB0 as (_ & _ & _ & ST). unfold capy, L5.bo_cap in CAPY |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in ST, CAPY |- *. clear; lia. destruct ST as (_ & _ & _ & _ & Hc & _). clear - Hc CAPY. lia. }
  assert (UR: forall k, 0 <= U R k < 2 ^ 64). { intros k. unfold U. apply (BL.bvu_range (getr R (Z_to_bv 5 k))). }
  assert (UR1: U R 1 = OPMOD2_RET). { unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G1. apply BG.unsigned_lit. unfold OPMOD2_RET; clear; lia. }
  assert (W48: L5.writable RSEGS M (S - 48) 48). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. clear; lia. clear; lia. flia. flia. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof (dop1_conc fx R M (VP S 0 0 0 0 0)) as P. cbn [VP] in P.
  destruct (P ltac:(flia) ltac:(rewrite <- r2; exact G2) ltac:(flia) A16 W48)
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & A1 & A2 & A8 & A12 & A13 & A14 & Cq24 & Cq32 & Cq40 & Cq48 & T8 & T1). clear P.
  rewrite <- r10, G10 in A8, A13.
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (S - 48 <= i < S) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi N1. apply FR1. exact Hi. flia. }
  assert (KUP: forall i, S <= i < 2 ^ 64 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KFR; flia. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (S - 48)) as [X|X]. left; apply KFR; flia. destruct (Z_lt_le_dec a S) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KFR; flia. }
  assert (DY0: L5.defined M S 32). { apply writable_defined_hi. exact WRY. unfold L5KS.IMG_HI; flia. clear; lia. flia. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (DIVO2 fx1 R1 M1 model K LB cr S (S - 48) ao fba (S - 48) 0x21d20 by_ wy HH1 MOK HK).
  - rewrite r10. rewrite (K1 10%nat) by inl. rewrite <- r10. exact G10.
  - rewrite r11. rewrite (K1 11%nat) by inl. rewrite <- r11. exact G11.
  - rewrite r12. exact A12.
  - rewrite r13. exact A13.
  - rewrite r14. exact A14.
  - rewrite r1. exact A1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact A2.
  - rewrite r3. rewrite (K1 3%nat) by inl. rewrite <- r3. exact G3.
  - rewrite r4. rewrite (K1 4%nat) by inl. rewrite <- r4. exact G4.
  - split. { replace (S - 48) with (S + (-3) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. rewrite DIVO2_SCR_val; flia. split. flia. split. exact SPTOP. rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. clear; lia. clear; lia.
  - intros i Hi. rewrite KFR. exact (IMGC i Hi). flia. flia.
  - (* [comment removed for export] *)
    split. { eapply big_at_agree1. 4: exact YB0. intros i Hi; apply KUP; flia. flia. flia. }
    split. { pose proof OLY0 as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2.
             destruct (L5.bo_st by_) as [y0 y1|cy qy] in YL3, BLK |- *. exact YL3.
             pose proof (LBdef _ _ _ _ HH _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _).
             eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; unfold hl_ceil in *; flia.
             intros i Hi. rewrite YL1 in Hi. apply KFR. unfold hl_ceil in *; flia. generalize Hi Yhi SLO (proj2 (proj2 BLK)); clear; unfold hl_ceil; intros; lia. }
    split. exact RED.
    destruct (L5.bo_st by_) as [y0 y1|cy qy] in BLK |- *. exact I. destruct BLK as (INY & DYq & LNY). split. exact INY. split. eapply L5.defined_grows. exact MG1. exact DYq. exact LNY.
  - exact LEN1.
  - exact CAPY.
  - exact (mod16_mod8 _ A16).
  - clear; lia.
  - flia.
  - eapply L5.writable_grows. exact MG1. exact WRY.
  - intros cap q E. eapply L5.writable_grows. exact MG1. exact (WRB cap q E).
  - destruct AOK as [OBa SGa]. split. 2: exact SGa. eapply big_at_agree1. 4: exact OBa. intros i Hi; apply KUP; subst ao; flia. subst ao; flia. subst ao; flia.
  - subst ao. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - subst ao; clear; lia.
  - subst ao; flia.
  - (* [comment removed for export] *)
    unfold zero_obj, L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact Cq48. split. clear; lia. split. exactA Cq40.
    split. reflexivity. split. exactA Cq32. split. exactA Cq24. split. clear; lia. clear; lia.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - clear; lia.
  - flia.
  - eapply L5.writable_grows. exact MG1. apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. clear; lia. clear; lia. flia. flia.
  - left. subst ao; clear; lia.
  - clear; lia.
  - subst ao; clear; lia.
  - pose proof CR as [C1 C2]. unfold OPMOD2_K, opmod2_bytes in C1, C2. unfold credit_for, DIVO2_K, divO2_bytes. pose proof KPOS. pose proof BPOS. subst capy. split; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
    destruct POST as (RP2 & (LBy & YA & QA) & AOK2 & CRA2 & HP2).
    pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP2) as SCR2. rewrite DIVO2_SCR_val in SCR2.
    (* [comment removed for export] *)
    assert (KTOP: forall a, S - 16 <= a < S -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. rewrite DIVO2_SCR_val; flia. rewrite DIVO2_SCR_val; clear; lia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
      apply L5C.outside_cons. { unfold L5.in_rng; cbn [fst snd]. unfold L5.bo_data, L5.bo_cap. destruct (L5.bo_st by_) as [y0 y1|cy qy] in BLK |- *. flia.
                                pose proof (LBhi _ _ _ _ HH _ (proj1 BLK)) as BH. cbn [fst snd] in BH. flia. }
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
    assert (T1': L5.u64_at RSEGS M2 (S - 8) (U R 1)). { eapply u64_at_agree1. 4: exact T1. intros i Hi; apply KTOP; flia. flia. flia. }
    assert (T8': L5.u64_at RSEGS M2 (S - 16) (U R 8)). { eapply u64_at_agree1. 4: exact T8. intros i Hi; apply KTOP; flia. flia. flia. }
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 (S - 48)). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. exact A2. }
    assert (E8: getr R2 (reg 8) = Z_to_bv 64 S). { rewrite (preserved_sregs R1 R2 8 RP2) by inl. exact A8. }
    assert (D48: L5.defined M1 (S - 48) 48). { eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. clear; lia. clear; lia. }
    assert (W48': L5.writable RSEGS M2 (S - 48) 48).
    { apply (L5C.writable_of_defined RSEGS). 2: flia. 2: flia. intros i Hi. destruct (Z_lt_le_dec i 32) as [X|X].
      - (* [comment removed for export] *)
        apply (L5C.hpres_cdef _ _ _ _ _ _ _ (S - 48 + i) HP2). flia. right; left. unfold hl_ceil. rewrite DIVO2_SCR_val. flia. unfold in_errno; rewrite ERRNOV; flia. exact (D48 i Hi).
      - rewrite KTOP by flia. exact (D48 i Hi). }
    (* [comment removed for export] *)
    assert (PRES: forall R6 : bvmap 5 word,
              getr R6 (reg 2) = Z_to_bv 64 S -> getr R6 (reg 8) = Z_to_bv 64 (U R 8) ->
              (forall i, In i [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg i) = getr R2 (reg i)) -> regs_preserved R R6).
    { intros R6 B2 B8 BS. apply preserved_by_index. intros i Hi. cbn in Hi.
      destruct Hi as [<-|Hi]. { rewrite B2, <- r2, G2. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite BS by inl. rewrite (preserved_sregs R1 R2 3 RP2) by inl. apply K1. inl. }
      destruct Hi as [<-|Hi]. { rewrite BS by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. apply K1. inl. }
      destruct Hi as [<-|Hi]. { rewrite B8. unfold U. apply Z_to_bv_bv_unsigned. }
      repeat (destruct Hi as [<-|Hi]; [ rewrite BS by inl; rewrite (preserved_sregs R1 R2 _ RP2) by inl; apply K1; inl |]). destruct Hi. }
    assert (POSTK: forall M6, (forall a, S - 48 <= a < 2 ^ 64 -> M6 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
              (forall A0 n a, In (A0, n) LBy -> A0 <= a < A0 + n -> M6 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
              (forall A0 n, In (A0, n) LBy -> L5.defined M2 A0 n -> L5.defined M6 A0 n) ->
              L5C.hpres L LB (S - 48) DIVO2_SCR [(S, 32); (L5.bo_data S by_, 8 * L5.bo_cap by_); (S - 48, 32)] M1 M6 ->
              y_after L LB M M6 S by_ LBy /\ a_ok M6 ao fba /\ L5C.hpres L LB S SCR_OPMOD [(S, 32); (L5.bo_data S by_, 8 * L5.bo_cap by_)] M M6).
    { intros M6 KA KB KD HP6. split.
      - destruct YA as (by' & wy' & OB' & OL' & ST'). exists by', wy'.
        split. { eapply big_at_agree1. 4: exact OB'. intros i Hi; apply KA; flia. flia. flia. }
        assert (INB: forall cap q, L5.bo_st by' = L5.BDyn cap q -> In (q, 8 * cap) LBy /\ L5.defined M2 q (8 * cap)).
        { intros cap q E. rewrite E in ST'. destruct (L5.bo_st by_) as [y0 y1|cy qy] in ST', BLK.
          - destruct ST' as (-> & -> & FB). split. left; reflexivity. exact (proj2 (proj2 FB)).
          - destruct ST' as (-> & -> & -> & D). split. exact (proj1 BLK). exact D. }
        split. { pose proof OL' as (L1 & L2 & L3). split. exact L1. split. exact L2. destruct (L5.bo_st by') as [v0 v1|cap q] eqn:E in L3 |- *. exact L3.
                 destruct (INB cap q E) as [INq Dq]. eapply limbs_at_agree1. 4: exact L3.
                 2,3: pose proof OB' as (_ & _ & _ & STq); rewrite E in STq; destruct STq as (_ & _ & _ & Hlc & _ & _ & Qlo & Qhi & _); rewrite ?L1; clear - Hlc Qlo Qhi; lia.
                 intros i Hi. apply (KB q (8 * cap)). exact INq. pose proof OB' as (_ & _ & _ & STq). rewrite E in STq. destruct STq as (_ & _ & _ & Hlc & _). rewrite L1 in Hi. clear - Hi Hlc; lia. }
        destruct (L5.bo_st by_) as [y0 y1|cy qy]; destruct (L5.bo_st by') as [v0 v1|cap q]; try exact ST'.
        + destruct ST' as (-> & -> & FB). split. reflexivity. split. reflexivity. destruct FB as (BR & BA & D). split. exact BR. split. exact BA.
          apply (KD q 64). left; reflexivity. exact D.
        + destruct ST' as (-> & -> & -> & D). split. reflexivity. split. reflexivity. split. reflexivity. apply (KD qy (8 * cy)). exact (proj1 (INB cy qy eq_refl)). exact D.
      - split. { destruct AOK2 as [OBa SGa]. split. 2: exact SGa. eapply big_at_agree1. 4: exact OBa. intros i Hi; apply KA; subst ao; flia. subst ao; flia. subst ao; flia. }
        eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(S, 32); (L5.bo_data S by_, 8 * L5.bo_cap by_)] M M1 M6 (S - 48) DIVO2_SCR). 2: exact HP6.
        + eapply (L5HP.hpres_piece L LB S SCR_OPMOD _ M M1 (fun a => S - 48 <= a < S)).
          * intros a Ha Hn'. apply KFR; flia.
          * intros a KA' C. refine (L5HP.kept_not_in_scratch L LB S SCR_OPMOD _ a KA' (LBhi _ _ _ _ HH) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
          * rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG1. exact SCR0.
          * exact MG1.
        + intros a KA'. eapply L5HP.kept_mono. exact KA'. intros b Hb; exact Hb. fsclia. clear; lia.
          intros OW. pose proof (L5HP.kept_not_in_scratch L LB S SCR_OPMOD _ a KA' (LBhi _ _ _ _ HH) ltac:(fsclia) ltac:(rewrite IMG; unfold hl_ceil; flia)) as NS. rewrite SCR_OPMOD_val in NS.
          apply L5C.outside_cons. exact (OW _ ltac:(left; reflexivity)). apply L5C.outside_cons. exact (OW _ ltac:(right; left; reflexivity)).
          apply L5C.outside_cons. unfold L5.in_rng; cbn; clear - NS; lia. apply L5C.outside_nil.
        + intros b Hb; exact Hb. + fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP). }
    assert (CRA: credit_after L cr OPMOD2_K (opmod2_bytes capy) cr2).
    { destruct CRA2 as [CA1 CA2]. unfold DIVO2_K, divO2_bytes in CA1, CA2. unfold credit_after, OPMOD2_K, opmod2_bytes. pose proof KPOS. pose proof BPOS. subst capy. split; lia. }
    destruct QA as (fbq & nq & stq & OBQ & QST).
    pose proof OBQ as (Qf & Qfr & Ql & QSTO). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qf, Qfr, Ql, QSTO.
    destruct stq as [q0 q1|cq p].
    + (* [comment removed for export] *)
      subst LB2. destruct QSTO as (Qb0 & _).
      pose proof (dop2i_conc fx2 R2 M2 (VP S fbq 0 0 (U R 1) (U R 8))) as P. cbn [VP] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(clear - Qfr; lia) ltac:(apply UR) ltac:(apply UR) E2 E8 ltac:(flia) A16 W48' T1' T8' Qf ltac:(clear - Qfr; lia) Qb0)
        as (fx6 & R6 & M6 & _ & FR6 & _ & MS6 & K6 & B1 & B2 & B8 & B10). clear P.
      pose proof (mem_eq M2 M6 FR6) as EM. subst M6. rewrite UR1 in B1.
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2.
      { eapply msteps_trans. exact MS6. apply (BRED.ret_to fx6 R6 M2 0x21d50 W_21d50 OPMOD2_RET F_21d50 eq_refl D_21d50 B1). unfold OPMOD2_RET; clear; lia. reflexivity. }
      apply (KN fx6 R6 M2 model2 LBy cr2).
      * destruct (POSTK M2 ltac:(intros; reflexivity) ltac:(intros; reflexivity) ltac:(intros A0 n _ D; exact D) HP2) as (YA' & AOK' & HP').
        split. { apply PRES. exact B2. exact B8. intros i Hi; apply K6; revert Hi; apply (L5K.incl_b _ KS_dop2i); vm_compute; reflexivity. }
        split. rewrite r10. exact B10. split. exact YA'. split. exact AOK'. split. exact CRA. exact HP'.
      * exact MBV2. * exact HH2.
    + (* [comment removed for export] *)
      destruct QST as (-> & FBq & CQ). destruct QSTO as (Qb1 & C16 & C24 & Hlc & Hcap & P8 & Plo & Phi & _).
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBq) as (Plo' & Pimg & _ & _ & Phi'). unfold hl_ceil in Phi'.
      pose proof (dop2d_conc fx2 R2 M2 (VP S fbq p cq (U R 1) (U R 8))) as P. cbn [VP] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(clear - Qfr; lia) ltac:(flia) ltac:(clear - Hcap; lia) ltac:(apply UR) ltac:(apply UR)
                  E2 E8 ltac:(flia) A16 W48' T1' T8' Qf ltac:(clear - Qfr; lia) Qb1 ltac:(exactA C24) ltac:(flia) ltac:(exactA C16) ltac:(clear - Hcap; lia))
        as (fx6 & R6 & M6 & _ & FR6 & _ & MS6 & K6 & B1 & B10 & B11). clear P.
      pose proof (mem_eq M2 M6 FR6) as EM. subst M6.
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS6.
      eapply (OPDEL fx6 R6 M2 model2 K ((p, 8 * cq) :: LBy) cr2 p (8 * cq) (S - 48) 0x21d40 HH2 MOK2 HK).
      * left. reflexivity.
      * rewrite r10. exact B10.
      * rewrite r1. exact B1.
      * split. clear; lia. reflexivity.
      * rewrite r2. rewrite (K6 2%nat) by inl. exact E2.
      * rewrite r4. rewrite (K6 4%nat) by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact G4.
      * split. { replace (S - 48) with (S + (-3) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
        split. rewrite OPDEL_SCR_val; flia. split. flia. split. exact SPTOP. rewrite OPDEL_SCR_val. eapply L5.defined_sub. exact SCR2. clear; lia. clear; lia.
      * (* [comment removed for export] *)
        intros fx7 R7 M7 model7 RP7 HP7 MBV7 HH7. rewrite lb_remove_head in HP7, HH7.
        pose proof (model_ok_but_vm _ _ MOK2 MBV7) as MOK7. pose proof MOK7 as (Mh7 & Ml7 & _).
        assert (KA7: forall a, S - 48 <= a < 2 ^ 64 -> M7 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
        { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP7). apply L5C.kept_stack. rewrite OPDEL_SCR_val; flia. rewrite OPDEL_SCR_val; clear; lia. flia. exact ERRNO. exact (proj1 SPTOP). apply L5C.outside_nil. }
        assert (KB7: forall A0 n a, In (A0, n) LBy -> A0 <= a < A0 + n -> M7 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
        { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH7 A0 n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
          apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP7). eapply L5C.kept_block. exact Hin. exact Ha. flia. unfold hl_ceil in *; flia. rewrite ERRNOV. generalize Aimg Ha; clear; intros; lia. apply L5C.outside_nil. }
        assert (KD7: forall A0 n, In (A0, n) LBy -> L5.defined M2 A0 n -> L5.defined M7 A0 n).
        { intros A0 n Hin D. eapply defined_agree1. intros i Hi. apply (KB7 A0 n). exact Hin. exact Hi. exact D. }
        assert (W48'': L5.writable RSEGS M7 (S - 48) 48).
        { apply (L5C.writable_of_defined RSEGS). 2: flia. 2: flia. intros i Hi.
          apply (L5C.hpres_cdef _ _ _ _ _ _ _ (S - 48 + i) HP7). flia. right; left. unfold hl_ceil. rewrite OPDEL_SCR_val. flia. unfold in_errno; rewrite ERRNOV; flia.
          pose proof W48' as W. apply writable_defined_hi in W. apply W. exact Hi. unfold L5KS.IMG_HI; flia. clear; lia. flia. }
        pose proof (dop3_conc fx7 R7 M7 (VP S 0 0 0 (U R 1) (U R 8))) as P. cbn [VP] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(apply UR) ltac:(apply UR)
                    ltac:(rewrite (preserved_sregs R6 R7 2 RP7) by inl; rewrite (K6 2%nat) by inl; exact E2)
                    ltac:(rewrite (preserved_sregs R6 R7 8 RP7) by inl; rewrite (K6 8%nat) by inl; exact E8)
                    ltac:(flia) A16 W48''
                    ltac:(eapply u64_at_agree1; [intros i Hi; apply KA7; flia | flia | flia | exact T1'])
                    ltac:(eapply u64_at_agree1; [intros i Hi; apply KA7; flia | flia | flia | exact T8']))
          as (fx8 & R8 & M8 & _ & FR8 & _ & MS8 & K8 & B1' & B2' & B8' & B10'). clear P.
        pose proof (mem_eq M7 M8 FR8) as EM. subst M8. rewrite UR1 in B1'.
        eapply (L5.cps_of_msteps RSEGS). exact Mh7. exact Ml7.
        { eapply msteps_trans. exact MS8. apply (BRED.ret_to fx8 R8 M7 0x21d50 W_21d50 OPMOD2_RET F_21d50 eq_refl D_21d50 B1'). unfold OPMOD2_RET; clear; lia. reflexivity. }
        apply (KN fx8 R8 M7 model7 LBy cr2).
        -- assert (HP27: L5C.hpres L LB (S - 48) DIVO2_SCR [(S, 32); (L5.bo_data S by_, 8 * L5.bo_cap by_); (S - 48, 32)] M1 M7).
           { eapply (L5HP.hpres_trans L LB LBy (S - 48) DIVO2_SCR _ M1 M2 M7 (S - 48) OPDEL_SCR []). exact HP2. exact HP7.
             - intros a KA'. eapply L5HP.kept_mono. exact KA'.
               { intros b Hb. destruct YA as (by' & wy' & _ & _ & ST'). destruct (L5.bo_st by_) as [y0 y1|cy qy]; destruct (L5.bo_st by') as [v0 v1|cap q]; try (exfalso; exact ST').
                 rewrite ST'; exact Hb. destruct ST' as (_ & -> & _); right; exact Hb. destruct ST' as (_ & _ & -> & _); exact Hb. }
               rewrite OPDEL_SCR_val, DIVO2_SCR_val; clear; lia. clear; lia. intros _; apply L5C.outside_nil.
             - intros b Hb. destruct YA as (by' & wy' & _ & _ & ST'). destruct (L5.bo_st by_) as [y0 y1|cy qy]; destruct (L5.bo_st by') as [v0 v1|cap q]; try (exfalso; exact ST').
               rewrite ST'; exact Hb. destruct ST' as (_ & -> & _); right; exact Hb. destruct ST' as (_ & _ & -> & _); exact Hb.
             - rewrite DIVO2_SCR_val; unfold hl_ceil; flia. - flia. - rewrite DIVO2_SCR_val; clear; lia. - exact ERRNO. - exact (proj1 SPTOP). }
           destruct (POSTK M7 KA7 KB7 KD7 HP27) as (YA' & AOK' & HP').
           split. { apply PRES. exact B2'. exact B8'.
                    intros i Hi. rewrite K8. rewrite (preserved_sregs R6 R7 i RP7). apply K6. revert Hi; apply (L5K.incl_b _ KS_dop2d); vm_compute; reflexivity.
                    revert Hi; apply (L5K.incl_b _ L5DIVO2A.cs_all); vm_compute; reflexivity. revert Hi; apply (L5K.incl_b _ KS_dop3); vm_compute; reflexivity. }
           split. rewrite r10. exact B10'. split. exact YA'. split. exact AOK'. split. exact CRA. exact HP'.
        -- exact (L5C.model_but_vm_trans _ _ _ MBV2 MBV7).
        -- exact HH7.
Qed.

End WithHeap.
End SCFG_1.
End L5OPMOD2.
