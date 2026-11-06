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
 L5DivSpecsU L5DivPartsU L5DivNPU L5DivO2PU L5DivO2SU L5DivTailU L5DivOPU L5DivEarlyU L5CmpU AsanAcct L5DivO2AU L5DivO2CU L5DivO2JU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2KU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVO2PU. Import L5DO2SU. Import L5DIVO2AU. Import L5DIVO2CU. Import L5DIVO2JU.

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
Hypothesis CMP : L5CMPU.cmp_spec.

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
Let stage_E4 := @L5DIVO2JU.stage_E4 _ L HI LY HIok KPOS BPOS COPYA ASSIGN RESIZE NORM UNNORMS DIVLOOP DIVTAIL DIVTAIL2 R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.
(* [comment removed for export] *)
Local Ltac cb := clearbody IMG IMGLO ERRNO ERRNOV SPTOP DIVO2_SCR_val SPW LBhi LBdef LBapart UR1 YB fbY_rng capy_rng Ln_le credit_debit64 credit_weaken credit_ok64 lb_free_cons_ne fresh_ne stage_E4.

Lemma copy_fb_bits fbo fb' dyn : 0 <= fbo -> 0 <= fb' < 256 ->
  0 <= copy_fb fbo fb' dyn < 256 /\ Z.testbit (copy_fb fbo fb' dyn) 0 = dyn /\ Z.testbit (copy_fb fbo fb' dyn) 1 = Z.testbit fb' 1.
Proof using R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
  intros Hfbo Hfb'. unfold copy_fb. split.
  { apply lor_byte. apply lor_byte. apply land_byte. lia. lia. destruct dyn; lia. split. apply Z.land_nonneg. left; lia. pose proof (L5K.land_le_r fb' 2 ltac:(lia) ltac:(lia)). lia. }
  split.
  - rewrite !Z.lor_spec, !Z.land_spec. change (Z.testbit 252 0) with false. change (Z.testbit 2 0) with false.
    rewrite !Bool.andb_false_r, Bool.orb_false_r. cbn. destruct dyn; reflexivity.
  - rewrite !Z.lor_spec, !Z.land_spec. change (Z.testbit 252 1) with false. change (Z.testbit 2 1) with true.
    rewrite Bool.andb_false_r, Bool.andb_true_r. cbn. destruct dyn; reflexivity.
Qed.

Lemma land2_zero f : 0 <= f < 256 -> Z.testbit f 1 = false -> Z.land f 2 = 0.
Proof using R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
  intros Hf Hb. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec k 1) as [->|Nk]. rewrite Hb. reflexivity.
  replace (Z.testbit 2 k) with false. apply Bool.andb_false_r. symmetry.
  destruct (Z.eq_dec k 0) as [->|Nk0]. reflexivity. rewrite (Z.bits_above_log2 2 k). reflexivity. lia. cbn. lia.
Qed.
Lemma land253_bits f : Z.testbit (Z.land f 253) 0 = Z.testbit f 0 /\ Z.testbit (Z.land f 253) 1 = false.
Proof. rewrite !Z.land_spec. split. apply Bool.andb_true_r. apply Bool.andb_false_r. Qed.
Lemma land2_cases f : 0 <= f -> Z.land f 2 = 0 \/ Z.land f 2 = 2.
Proof using R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
  intros Hf. pose proof (land2_rng f Hf) as Rg. pose proof (land2_bit0 f) as B. rewrite Z.bit0_odd in B.
  destruct (Z.eq_dec (Z.land f 2) 1) as [E|NE]. rewrite E in B. discriminate B. lia.
Qed.
Lemma segs_below : segs_below_b RSEGS 0x92000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma writable_defined_hi M a n : L5.writable RSEGS M a n -> L5KU.IMG_HI <= a -> 0 <= n -> a + n <= 2 ^ 64 -> L5.defined M a n.
Proof using L R0 M0 LB Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ AP1.
  intros W Hlo Hn Hhi i Hi. specialize (W i 1%nat ltac:(lia) ltac:(cbn; lia)). cbn [store_ok] in W.
  unfold wview in W. destruct (M (Z_to_bv 64 (a + i))) eqn:E. congruence.
  unfold L5KU.IMG_HI in Hlo. rewrite BG.unsigned_lit in W by lia. rewrite (find_segment1_none_above RSEGS 0x92000 (a + i) segs_below) in W by lia. discriminate W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc nb : list (Z * Z)) (crc : credit)
      (fden fnum : Z) (stn : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y ->
  getr R (reg 19) = Z_to_bv 64 fden -> getr R (reg 20) = Z_to_bv 64 fbY -> getr R (reg 23) = Z_to_bv 64 1 ->
  L5.u64_at RSEGS M (sp - 144) 2 ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = nb ++ LB -> nb = match stn with L5.BDyn c q => [(q, 8 * c)] | L5.BInl _ _ => [] end -> credit_after L cr 1 (8 * capy) crc ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 184) (L5.BO fnum Ln stn) -> L5C.obj_limbs RSEGS M (L5.BO fnum Ln stn) wy ->
  match sty, stn with
  | L5.BDyn c q, L5.BDyn c' q' => c' = c /\ (q + 8 * c <= q' \/ q' + 8 * c' <= q) /\ L5.defined M q' (8 * c') /\ block_range L q' (8 * c') /\ blocks_apart q' (8 * c') LB
  | L5.BInl _ _, L5.BInl _ _ => True
  | _, _ => False end ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  zero_obj M Q -> L5.defined M Q 32 ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22584 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H19 H20 H23 VS MBV HH ELB ENB CRA DS OBN OLN NST OBD Fdb1 OBY OLY DY DYD ZQ0 DQ IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (LN267: (Ln <= 267)%nat). { unfold sty in LNS. unfold capy, L5.bo_cap in CAPR. destruct (L5.bo_st by_) in LNS, CAPR; flia. }
  pose proof YOK as (_ & _ & RED & BLK).
  pose proof OBN as (Nb0 & Nfr & Nb8 & NSTF). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nfr, Nb8, NSTF.
  pose proof OLN as (WL & WO & WLA). cbn [L5.bo_len L5.bo_st] in WL, WLA.
  pose proof OBD as (Db0 & Dfr & Db8 & (Dtb & D16 & D24 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Db0, Dfr, Db8, Dtb, D16, D24.
  assert (WRF: L5.writable RSEGS M (sp - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  assert (NBLK: forall cap q, stn = L5.BDyn cap q -> In (q, 8 * cap) LBc /\ q + 8 * cap <= hl_ceil L /\ 4096 <= q /\ Z.of_nat Ln + 1 <= cap /\ cap <= 268 /\ L5.defined M q (8 * cap)).
  { intros cap q ->. unfold sty in NST, LNS. unfold capy, L5.bo_cap in CAPR |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in NST, LNS, CAPR |- *. exfalso; exact NST.
    destruct NST as (-> & AP & Dq & BR & BA). assert (INq: In (q, 8 * cy) LBc) by (rewrite ELB, ENB; left; reflexivity).
    pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & (Qlo & _) & Qhi & _). repeat split; try assumption; flia. }
  unfold cfg.
  pose proof (d5ue3_conc fx R M (Vd 0 fden 0 0 fnum 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H19 H20 ltac:(flia) A16 WRF Nb0 Db0 ltac:(flia) ltac:(flia) ltac:(flia))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & Ar1 & A10 & A11 & A25 & A26 & C136 & C184). clear P.
  rewrite (land2_zero fden Dfr Fdb1), Z.lxor_0_l in A26.
  pose proof (land2_cases fbY (proj1 FBY)) as QC.
  assert (Hq: 0 <= Z.land fbY 2 / 2 <= 1). { destruct QC as [E|E]; rewrite E; cbn; clear; lia. }
  apply BG.word_of_unsigned in A25. apply BG.word_of_unsigned in A26.
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 184 <= i < sp - 183) -> ~ (sp - 136 <= i < sp - 135) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2. apply FR1. exact Hi. flia. flia. }
  assert (KOUT: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 184 <= i < sp - 135) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi N1. apply KEEP1; flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 184)) as [X|X]. left; apply KOUT; flia. destruct (Z_lt_le_dec a (sp - 135)) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KOUT; flia. }
  (* [comment removed for export] *)
  set (fnum' := Z.land fnum 253) in C184. set (fden' := Z.land fden 253) in C136.
  pose proof (land253_bits fnum) as [FN0 FN1]. pose proof (land253_bits fden) as [FD0 FD1]. fold fnum' in FN0, FN1. fold fden' in FD0, FD1.
  assert (FNR: 0 <= fnum' < 256). { subst fnum'. apply L5.land_byte_range. lia. }
  assert (FDR: 0 <= fden' < 256). { subst fden'. apply L5.land_byte_range. lia. }
  assert (OBN1: L5.big_at RSEGS M1 (sp - 184) (L5.BO fnum' Ln stn)).
  { eapply (big_at_refb M M1 (sp - 184) fnum fnum' Ln stn OBN). intros i Hi; apply KEEP1; flia. flia. flia. exact C184. exact FNR. exact FN0. }
  assert (OBD1: L5.big_at RSEGS M1 (sp - 136) (L5.BO fden' 2 (L5.BInl A0 A1))).
  { eapply (big_at_refb M M1 (sp - 136) fden fden' 2%nat (L5.BInl A0 A1) OBD). intros i Hi; apply KEEP1; flia. flia. flia. exact C136. exact FDR. exact FD0. }
  assert (OLN1: L5C.obj_limbs RSEGS M1 (L5.BO fnum' Ln stn) wy).
  { split. exact WL. split. exact WO. cbn [L5.bo_st]. destruct stn as [v0 v1|cn qn]. exact WLA.
    destruct (NBLK cn qn eq_refl) as (_ & Qhi & Qlo & _). eapply limbs_at_agree1. 4: exact WLA. intros i Hi; apply KOUT; unfold hl_ceil in *; flia. flia. rewrite WL. unfold hl_ceil in *; flia. }
  assert (OLD1: L5C.obj_limbs RSEGS M1 (L5.BO fden' 2 (L5.BInl A0 A1)) WA). { split. reflexivity. split. exact WA_ok. reflexivity. }
  assert (NDATA: 4096 <= L5.bo_data (sp - 184) (L5.BO fnum' Ln stn) /\ L5.bo_data (sp - 184) (L5.BO fnum' Ln stn) + 8 * Z.of_nat Ln <= 2 ^ 47
                 /\ L5.defined M1 (L5.bo_data (sp - 184) (L5.BO fnum' Ln stn)) (8 * Z.of_nat Ln)
                 /\ (sp - 352 - 80 + 80 <= L5.bo_data (sp - 184) (L5.BO fnum' Ln stn) \/ L5.bo_data (sp - 184) (L5.BO fnum' Ln stn) + 8 * Z.of_nat Ln <= sp - 352 - 80)).
  { unfold L5.bo_data. cbn [L5.bo_st]. destruct stn as [v0 v1|cn qn].
    - destruct NSTF as (_ & _ & _ & Hl2 & _). split. flia. split. flia. split. eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. flia. flia. left; flia.
    - destruct (NBLK cn qn eq_refl) as (_ & Qhi & Qlo & Hle & _ & Dq). split. flia. split. unfold hl_ceil in *; flia.
      split. eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact Dq. flia. flia. right. unfold hl_ceil in *; flia. }
  destruct NDATA as (ND1 & ND2 & ND3 & ND4).
  assert (VS1: L5.u64_at RSEGS M1 (sp - 144) 2). { eapply u64_at_agree1. 4: exact VS. intros i Hi; apply KEEP1; flia. flia. flia. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  eapply (CMP fx1 R1 M1 model K spd (sp - 184) (sp - 136) 0x225b8 (L5.BO fnum' Ln stn) (L5.BO fden' 2 (L5.BInl A0 A1)) wy WA Mh Ml
            ltac:(rewrite r2; rewrite (K1 2%nat) by inl; exact H2) A10 A11 Ar1).
  - split. flia. reflexivity.
  - unfold L5CMPU.cmp_obj. cbn [L5.bo_fb L5.bo_len]. split. exact OBN1. split. exact FN1. split. flia. split. flia.
    split. rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16); reflexivity. split. flia. split. flia. split. exact ND1. split. exact ND2. exact ND3.
  - unfold L5CMPU.cmp_obj. cbn [L5.bo_fb L5.bo_len L5.bo_data L5.bo_st]. split. exact OBD1. split. exact FD1. split. clear; lia. split. clear; lia.
    split. rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16); reflexivity. split. flia. split. flia. split. flia. split. flia.
    eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. flia. flia.
  - unfold L5CMPU.cmp_stack, L5CMPU.apart. cbn [L5.bo_len].
    split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; flia.
    split. { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG1. eapply L5.defined_sub. exact SCR0. unfold spd; flia. unfold spd; flia. unfold spd; flia. flia. }
    split. unfold spd; flia. split. unfold spd; flia. split. unfold spd. exact ND4.
    cbn [L5.bo_data L5.bo_st]. left. unfold spd; flia.
  - exact OLN1.
  - exact OLD1.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 POST. destruct POST as (K2 & RP & (c & A10' & RSZ & VEQ) & FR2 & MG2).
    cbn [L5.bo_len] in RSZ, VEQ.
    assert (HC: c = L5CMPU.MAXW \/ (0 <= c <= 1 /\ (2 <= Ln)%nat)).
    { destruct RSZ as (C01 & LT & GT). destruct (Z.eq_dec c L5CMPU.MAXW) as [E|NE]. left; exact E. right. split. { clear - C01 NE. unfold L5CMPU.MAXW in *. lia. }
      destruct (Nat.lt_ge_cases Ln 2) as [Hlt|Hge]. exfalso. exact (NE (LT Hlt)). exact Hge. }
    assert (KC: forall i, 0 <= i < 2 ^ 64 -> ~ (spd - 80 <= i < spd) -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
    { intros i Hi Ni. apply FR2. rewrite BG.unsigned_lit by exact Hi. exact Ni. }
    assert (KC2: forall i, 0 <= i < 2 ^ 64 -> ~ (spd - 80 <= i < spd) -> ~ (sp - 184 <= i < sp - 135) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi N0' N1. rewrite (KC i Hi N0'). apply KOUT. exact Hi. exact N1. }
    assert (MG02: mem_grows M M2). { eapply mem_grows_trans. exact MG1. exact MG2. }
    assert (HH2: hi_heap HI LBc crc M2 (m_vmmaps model)).
    { eapply (L5C.hi_heap_client L SCFG HI LBc crc M1 M2). exact HIok. exact HH1. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG2.
      intros a Ha. destruct (Z_lt_le_dec a (spd - 80)) as [X|X]. left; apply KC; flia. destruct (Z_lt_le_dec a spd) as [X'|X']. right; left; unfold spd, hl_ceil in *; flia. left; apply KC; flia. }
    assert (REGS: forall i v, In i L5CMPU.cmp_kept -> In i KS_d5ue3 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (K2 i Hi). rewrite (K1 i Hk). exact Hv. }
    apply (stage_E4 fx2 R2 M2 model LBc nb crc c fden' fnum' (Z.land fbY 2 / 2) stn).
    all: try (eapply REGS; [inl | inl | eassumption]).
    + exact A10'.
    + rewrite (K2 25%nat) by inl. exact A25.
    + rewrite (K2 26%nat) by inl. exact A26.
    + eapply u64_at_agree1. 4: exact VS1. intros i Hi; apply KC; unfold spd; flia. flia. flia.
    + exact Hq. + exact HC. + exact MBV. + exact HH2. + exact ELB. + exact ENB. + exact CRA.
    + eapply div_saves_kept. 4: exact DS. intros i Hi; apply KC2; unfold spd; flia. flia. flia.
    + eapply big_at_agree1. 4: exact OBN1. intros i Hi; apply KC; unfold spd; flia. flia. flia.
    + pose proof OLN1 as (L1' & L2' & L3'). split. exact L1'. split. exact L2'. cbn [L5.bo_st] in L3' |- *. destruct stn as [v0 v1|cn qn]. exact L3'.
      destruct (NBLK cn qn eq_refl) as (_ & Qhi & Qlo & _). eapply limbs_at_agree1. 4: exact L3'. intros i Hi; apply KC; unfold spd, hl_ceil in *; flia. flia. rewrite WL. unfold hl_ceil in *; flia.
    + exact FN1.
    + unfold sty in NST |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in NST |- *; destruct stn as [v0 v1|cn qn]; try exact NST.
      destruct NST as (Ec & AP & Dq & BR & BA). split. exact Ec. split. exact AP. split. eapply L5.defined_grows. exact MG02. exact Dq. split. exact BR. exact BA.
    + eapply big_at_agree1. 4: exact OBD1. intros i Hi; apply KC; unfold spd; flia. flia. flia.
    + exact FD1.
    + eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KC2; unfold spd; flia. flia. flia.
    + pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. unfold sty in BLK, LNS.
      destruct (L5.bo_st by_) as [y0 y1|cy qy] in YL3, BLK, LNS |- *. exact YL3.
      pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _).
      eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
      intros i Hi. rewrite YL1 in Hi. fold Ln in Hi. apply KC2; unfold spd, hl_ceil in *; flia.
    + eapply L5.defined_grows. exact MG02. exact DY.
    + eapply L5.defined_grows. exact MG02. exact DYD.
    + unfold zero_obj. eapply big_at_agree1. 4: exact ZQ0. intros i Hi; apply KC2; unfold spd; flia. flia. flia.
    + eapply L5.defined_grows. exact MG02. exact DQ.
    + intros i Hi. rewrite KC2. exact (IMG1 i Hi). flia. unfold spd; flia. flia.
    + eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M2 sp DIVO2_SCR WN). exact HP.
      * eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M2 (fun a => (sp - 184 <= a < sp - 135) \/ (spd - 80 <= a < spd))).
        -- intros a Ha Hn'. apply KC2. exact Ha. generalize Hn'; clear; intros; lia. generalize Hn'; clear; intros; lia.
        -- intros a KA C0. assert (C': sp - 9440 <= a < sp) by (unfold spd in C0; generalize C0 SLO'; clear; intros; lia). clear C0.
           refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
        -- rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG02. exact SCR0.
        -- exact MG02.
      * intros a KA; exact KA. * intros b Hb; exact Hb. * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E2 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (fden : Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y -> getr R (reg 23) = Z_to_bv 64 1 ->
  model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  zero_obj M Q -> L5.defined M Q 32 ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22548 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H23 MBV HH DS OBD Fdb1 OBY OLY DY DYD ZQ0 DQ IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (LN267: (Ln <= 267)%nat). { unfold sty in LNS. unfold capy, L5.bo_cap in CAPR. destruct (L5.bo_st by_) in LNS, CAPR; flia. }
  pose proof YOK as (_ & _ & RED & BLK).
  pose proof OBD as (Db0 & Dfr & Db8 & (Dtb & D16 & D24 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Db0, Dfr, Db8, Dtb, D16, D24.
  pose proof OBY as OBY'. unfold L5.big_at in OBY'. fold fbY Ln sty in OBY'. destruct OBY' as (Yb0 & _ & Yb8 & YST).
  assert (WRF: L5.writable RSEGS M (sp - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d7ue2_conc fx R M (Vd 0 fden 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
              H2 H8 H9 H18 H23 ltac:(flia) A16 WRF Db0 ltac:(exactA Db8) ltac:(flia) Dtb ltac:(clear; lia) ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & Ar1 & A10 & A11 & A12 & A19 & A20 & A22 & VS1 & VD1). clear P.
  (* [comment removed for export] *)
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 152 <= i < sp - 136) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1. apply FR1. exact Hi. flia. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 152)) as [X|X]. left; apply KFR; flia. destruct (Z_lt_le_dec a (sp - 136)) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KFR; flia. }
  assert (SCR1: L5.defined M1 (sp - 9440) 9440). { eapply L5.defined_grows. exact MG1. exact SCR0. }
  assert (DS1: div_saves M1 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR; flia. flia. flia. }
  assert (OBD1: L5.big_at RSEGS M1 (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1))). { eapply big_at_agree1. 4: exact OBD. intros i Hi; apply KFR; flia. flia. flia. }
  assert (OBY1: L5.big_at RSEGS M1 Y by_). { eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KFR; flia. flia. flia. }
  assert (OLY1: L5C.obj_limbs RSEGS M1 by_ wy).
  { pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. pose proof BLK as BLK0. pose proof LNS as LNS0. unfold sty in BLK0, LNS0.
    destruct (L5.bo_st by_) as [y0 y1|cy qy] in YL3, BLK0, LNS0 |- *. exact YL3.
    pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK0)) as (_ & (Ylo & _) & Yhi & _).
    eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
    intros i Hi. rewrite YL1 in Hi. fold Ln in Hi. apply KFR; unfold hl_ceil in *; flia. }
  assert (DY1: L5.defined M1 Y 32). { eapply L5.defined_grows. exact MG1. exact DY. }
  assert (DYD1: L5.defined M1 yd0 (8 * capy)). { eapply L5.defined_grows. exact MG1. exact DYD. }
  assert (ZQ1: zero_obj M1 Q). { unfold zero_obj. eapply big_at_agree1. 4: exact ZQ0. intros i Hi; apply KFR; flia. flia. flia. }
  assert (DQ1: L5.defined M1 Q 32). { eapply L5.defined_grows. exact MG1. exact DQ. }
  assert (IMG1': L5.img_clear M1 0x10000 0x20000). { intros i Hi. rewrite KFR. exact (IMG1 i Hi). flia. flia. }
  assert (HP1: L5C.hpres L LB sp DIVO2_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => sp - 152 <= a < sp - 136)).
      + intros a Ha Hn'. apply KFR; assumption.
      + intros a KA C0. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
      + rewrite DIVO2_SCR_val. exact SCR1.
      + exact MG1.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  destruct (defined_byte M1 (sp - 184) ltac:(eapply L5.defined_sub; [exact SCR1 | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo & FBO & U184).
  eapply (COPYA fx1 R1 M1 model K LB cr (sp - 184) Y spd 0x22584 fbo by_ wy HH1 MOK HK0).
  - rewrite r10. exact A10.
  - rewrite r11. exact A11.
  - fold capy. intros _. split. flia. unfold credit_ok. pose proof CR as [C1 C2]. fold capy in C1, C2. unfold DIVO2_K, divO2_bytes in C1, C2. pose proof KPOS. pose proof BPOS. split; flia.
  - rewrite r1. exact Ar1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (K1 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR1. flia. flia.
  - exact U184.
  - exact FBO.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia.
  - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR1. flia. flia. flia. flia.
  - exact OBY1.
  - exact OLY1.
  - exact AY8.
  - unfold spd; flia.
  - exact HY.
  - intros cap q E. rewrite E in BLK. exact (proj1 BLK).
  - left. flia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
    destruct POST as (RP & GPOST).
    assert (REGS: forall i v, In i cs_all -> In i KS_d7ue2 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (K1 i Hk). exact Hv. }
    assert (REGS1: forall i v, In i cs_all -> getr R1 (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hv. rewrite (preserved_sregs R1 R2 i RP Hi). exact Hv. }
    destruct g as [|B1 cB].
    + (* [comment removed for export] *)
      destruct GPOST as (DQF & -> & -> & OBn & FRB & MGB). unfold L5.bo_dyn in DQF. fold fbY Ln sty in OBn. fold fbY in DQF.
      assert (EYI: exists y0 y1, sty = L5.BInl y0 y1).
      { unfold sty in YST |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in YST |- *. eexists _, _; reflexivity. destruct YST as (T & _). rewrite T in DQF. discriminate DQF. }
      destruct EYI as (y0 & y1 & EY). pose proof EY as EY'. unfold sty in EY'.
      assert (KB: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 184 <= a < sp - 152) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha N1. apply FRB. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by flia. flia. }
      apply (stage_E3 fx2 R2 M2 model2 LB [] cr fden (copy_fb fbo fbY false) sty).
      all: try (eapply REGS; [inl | inl | eassumption]).
      * eapply REGS1. inl. exact A19.
      * eapply REGS1. inl. exact A20.
      * eapply u64_at_agree1. 4: exact VS1. intros i Hi; apply KB; flia. flia. flia.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * exact HH2.
      * reflexivity.
      * rewrite EY. reflexivity.
      * unfold credit_after. pose proof KPOS. pose proof BPOS. pose proof CAPR. split; flia.
      * eapply div_saves_kept. 4: exact DS1. intros i Hi; apply KB; flia. flia. flia.
      * exact OBn.
      * pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. cbn [L5.bo_st]. rewrite EY. rewrite EY' in YL3. exact YL3.
      * rewrite EY. exact I.
      * eapply big_at_agree1. 4: exact OBD1. intros i Hi; apply KB; flia. flia. flia.
      * exact Fdb1.
      * eapply big_at_agree1. 4: exact OBY1. intros i Hi; apply KB; flia. flia. flia.
      * pose proof OLY1 as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. rewrite EY' in YL3 |- *. exact YL3.
      * eapply L5.defined_grows. exact MGB. exact DY1.
      * eapply L5.defined_grows. exact MGB. exact DYD1.
      * unfold zero_obj. eapply big_at_agree1. 4: exact ZQ1. intros i Hi; apply KB; flia. flia. flia.
      * eapply L5.defined_grows. exact MGB. exact DQ1.
      * intros i Hi. rewrite KB. exact (IMG1' i Hi). flia. flia.
      * eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M1 M2 sp DIVO2_SCR WN). exact HP1.
        -- eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M1 M2 (fun a => sp - 184 <= a < sp - 152)).
           ++ intros a Ha Hn'. apply KB; flia.
           ++ intros a KA C0. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
           ++ rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MGB. exact SCR1.
           ++ exact MGB.
        -- intros a KA; exact KA. -- intros b Hb; exact Hb. -- fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
    + (* [comment removed for export] *)
      destruct GPOST as (DQT & EcB & -> & -> & FB1 & OBn & OLn & HPB). unfold L5.bo_dyn in DQT. fold fbY in DQT. fold capy in EcB. subst cB.
      fold fbY Ln capy in OBn. fold fbY Ln capy in OLn.
      assert (EYD: exists cy qy, sty = L5.BDyn cy qy).
      { unfold sty in YST |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in YST |- *. destruct YST as (T & _). rewrite T in DQT. discriminate DQT. eexists _, _; reflexivity. }
      destruct EYD as (cy & qy & EY). pose proof EY as EY'. unfold sty in EY'.
      pose proof BLK as BLK'. rewrite EY' in BLK'. destruct BLK' as (INY & DY0 & LNY).
      assert (ECY: capy = cy). { unfold capy, L5.bo_cap. rewrite EY'. reflexivity. }
      pose proof (LBdef _ _ _ _ HH0 _ _ INY) as (_ & (Ylo & Yimg) & Yhi & _). rewrite IMG, IMGLO in Yimg.
      pose proof FB1 as (BR1 & BA1 & DF1).
      assert (KS: forall a, sp - 352 <= a < 2 ^ 64 -> ~ (sp - 184 <= a < sp - 152) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha N1. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HPB). apply L5C.kept_stack. uSCR; unfold spd; flia. uSCR; flia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
      assert (KB: forall A0 n a, In (A0, n) LB -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HPB). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_nil. }
      assert (CDEF2: forall a n, L5.defined M1 a n -> (forall i, a <= i < a + n -> sp - 352 <= i < hl_sptop L \/ in_block LB i) -> L5.defined M2 a n).
      { intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
        - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HPB). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
        - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
          apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HPB). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
      apply (stage_E3 fx2 R2 M2 model2 ((B1, 8 * capy) :: LB) [(B1, 8 * capy)] (debit L cr (8 * capy)) fden (copy_fb fbo fbY true) (L5.BDyn capy B1)).
      all: try (eapply REGS; [inl | inl | eassumption]).
      * eapply REGS1. inl. exact A19.
      * eapply REGS1. inl. exact A20.
      * eapply u64_at_agree1. 4: exact VS1. intros i Hi; apply KS; flia. flia. flia.
      * exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
      * exact HH2.
      * reflexivity.
      * reflexivity.
      * unfold credit_after, debit. cbn [fst snd]. pose proof KPOS. pose proof BPOS. split; flia.
      * eapply div_saves_kept. 4: exact DS1. intros i Hi; apply KS; flia. flia. flia.
      * exact OBn.
      * exact OLn.
      * rewrite EY. split. exact ECY. split. { pose proof (BA1 _ INY) as X. cbn in X. rewrite ECY. destruct X; [right | left]; flia. }
        split. exact DF1. split. exact BR1. exact BA1.
      * eapply big_at_agree1. 4: exact OBD1. intros i Hi; apply KS; flia. flia. flia.
      * exact Fdb1.
      * eapply big_at_agree1. 4: exact OBY1. intros i Hi; apply KS; flia. flia. flia.
      * pose proof OLY1 as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. rewrite EY' in YL3 |- *.
        eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
        intros i Hi. rewrite YL1 in Hi. fold Ln in Hi. apply (KB qy (8 * cy)). exact INY. flia.
      * eapply defined_agree1. 2: exact DY1. intros i Hi; apply KS; flia.
      * eapply defined_agree1. 2: exact DYD1. intros i Hi. unfold yd0, capy, L5.bo_data, L5.bo_cap in Hi. rewrite EY' in Hi. apply (KB qy (8 * cy)). exact INY. exact Hi.
      * unfold zero_obj. eapply big_at_agree1. 4: exact ZQ1. intros i Hi; apply KS; flia. flia. flia.
      * eapply defined_agree1. 2: exact DQ1. intros i Hi; apply KS; flia.
      * eapply img_clear_kept. exact HPB. exact LY. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. exact IMG1'.
      * eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M1 M2 spd COPY_SCR). exact HP1. exact HPB.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. exact Hb. } unfold spd; fsclia. unfold spd; flia.
           intros OW. pose proof (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) ltac:(fsclia) ltac:(rewrite IMG; unfold hl_ceil; flia)) as NS.
           apply L5C.outside_cons. unfold L5.in_rng; cbn; generalize NS; clear; uSCR; intros; lia. apply L5C.outside_nil.
        -- intros b Hb. exact Hb.
        -- unfold spd; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E1 : srealizes RSEGS SCFG (cfg R0 DIVIDE M0 model0) K.
Proof.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof MOK0 as (Mh & Ml & _).
  pose proof STK as (_ & _ & _ & _ & SCR0). rewrite DIVO2_SCR_val in SCR0.
  pose proof YOK as (YB0 & OLY0 & RED & BLK).
  pose proof AOK as [OBa SGa]. pose proof OBa as (Ab0 & Afr & Ab8 & (Atb & Aw16 & Aw24 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Ab0, Afr, Ab8, Atb, Aw16, Aw24.
  assert (WRF: L5.writable RSEGS M0 (sp - 352) 352). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  assert (DY0: L5.defined M0 Y 32). { apply writable_defined_hi. exact WRY. unfold L5KU.IMG_HI; flia. flia. flia. }
  assert (DQ0: L5.defined M0 Q 32). { apply writable_defined_hi. exact WRQ. unfold L5KU.IMG_HI; flia. flia. flia. }
  assert (DYD0: L5.defined M0 yd0 (8 * capy)).
  { unfold yd0, capy, L5.bo_data, L5.bo_cap. destruct (L5.bo_st by_) as [y0 y1|cy qy] in BLK |- *. eapply L5.defined_sub. exact DY0. flia. flia. exact (proj1 (proj2 BLK)). }
  unfold cfg.
  pose proof (d5ue1_conc fx0 R0 M0 (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
              ltac:(rewrite <- r2; exact G2) ltac:(rewrite <- r10; exact G10) ltac:(rewrite <- r11; exact G11) ltac:(rewrite <- r12; exact G12)
              ltac:(rewrite <- r13; exact G13) ltac:(rewrite <- r14; exact G14) ltac:(flia) A16 WRF)
    as (fx1 & R1 & M1 & MG & _ & FR & MS & KS & Ar1 & Ar2 & A8 & A9 & A10 & A12 & A18 & A23 & S27 & S26 & S25 & S24 & S23 & S22 & S21 & S20 & S19 & S18 & S9 & S8 & S1). clear P.
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 352 <= i < sp) -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)). { intros i Hi N1. apply FR. exact Hi. flia. }
  assert (KUP: forall i, sp <= i < 2 ^ 64 -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)). { intros i Hi. apply KFR; flia. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model0)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M0 M1). exact HIok. exact HH0. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 352)) as [X|X]. left; apply KFR; flia. destruct (Z_lt_le_dec a sp) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KFR; flia. }
  assert (DS1: div_saves M1 sp R0). { unfold div_saves. repeat split; assumption. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  destruct (defined_byte M1 (sp - 136) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG | exact SCR0] | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo & FBO & UFBO).
  assert (OBa1: L5.big_at RSEGS M1 A (L5.BO fba 2 (L5.BInl A0 A1))). { eapply big_at_agree1. 4: exact OBa. intros i Hi; apply KUP; flia. flia. flia. }
  assert (OLa: L5C.obj_limbs RSEGS M1 (L5.BO fba 2 (L5.BInl A0 A1)) WA). { split. reflexivity. split. exact WA_ok. reflexivity. }
  eapply (COPYA fx1 R1 M1 model0 K LB cr (sp - 136) A spd 0x22548 fbo (L5.BO fba 2 (L5.BInl A0 A1)) WA HH1 MOK0 HK0 A10
            ltac:(rewrite r11; rewrite (KS 11%nat) by inl; rewrite <- r11; exact G11)).
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite Atb. intros F; discriminate F.
  - rewrite r1. exact Ar1.
  - split. flia. reflexivity.
  - rewrite r2. exact Ar2.
  - rewrite r4. rewrite (KS 4%nat) by inl. rewrite <- r4. exact G4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. eapply L5.defined_grows. exact MG. exact SCR0. flia. flia.
  - exact UFBO. - exact FBO.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. eapply L5.defined_grows. exact MG. exact SCR0. flia. flia. flia. flia.
  - exact OBa1. - exact OLa.
  - exact AA8. - unfold spd; flia. - exact HA.
  - cbn [L5.bo_st]. intros cap q E. discriminate E.
  - left. flia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & GPOST). destruct g as [|Ag cg].
    2:{ exfalso. destruct GPOST as (F & _). unfold L5.bo_dyn in F. cbn [L5.bo_fb] in F. rewrite Atb in F. discriminate F. }
    destruct GPOST as (_ & -> & -> & OB2 & FB2 & MG2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB2.
    assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 136 <= a < sp - 104) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha N1. apply FB2. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by exact Ha. flia. }
    assert (K02: forall i, sp <= i < 2 ^ 64 -> M2 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)). { intros i Hi. rewrite KA. apply KUP. exact Hi. flia. flia. }
    assert (KLO: forall i, 0 <= i < sp - 352 -> M2 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)). { intros i Hi. rewrite KA. apply KFR. flia. flia. flia. flia. }
    assert (REGS: forall i v, In i cs_all -> In i KS_d5ue1 -> getr R0 (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    set (fden := copy_fb fbo fba false) in OB2.
    pose proof (copy_fb_bits fbo fba false (proj1 FBO) Afr) as (Fr & Fb0 & Fb1). fold fden in Fr, Fb0, Fb1. rewrite SGa in Fb1.
    apply (stage_E2 fx2 R2 M2 model2 fden).
    + rewrite (preserved_sregs R1 R2 2 RP) by inl. exact Ar2.
    + eapply REGS. inl. inl. rewrite <- r3. exact G3.
    + eapply REGS. inl. inl. rewrite <- r4. exact G4.
    + rewrite (preserved_sregs R1 R2 8 RP) by inl. exact A8.
    + rewrite (preserved_sregs R1 R2 9 RP) by inl. exact A9.
    + rewrite (preserved_sregs R1 R2 18 RP) by inl. exact A18.
    + rewrite (preserved_sregs R1 R2 23 RP) by inl. exact A23.
    + exact MBV2. + exact HH2.
    + eapply div_saves_kept. 4: exact DS1. intros i Hi; apply KA; flia. flia. flia.
    + exact OB2. + exact Fb1.
    + eapply big_at_agree1. 4: exact YB0. intros i Hi; apply K02; flia. flia. flia.
    + pose proof OLY0 as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2.
      destruct (L5.bo_st by_) as [y0 y1|cy qy] in YL3, BLK |- *. exact YL3.
      pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _). pose proof (LBhi _ _ _ _ HH0 _ (proj1 BLK)) as BH. cbn [fst snd] in BH.
      eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; unfold hl_ceil in *; flia.
      intros i Hi. rewrite YL1 in Hi. apply KLO. generalize BH Hi Ylo SLO' (proj2 (proj2 BLK)); clear; intros; lia.
    + eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact DY0.
    + eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact DYD0.
    + unfold zero_obj. eapply big_at_agree1. 4: exact ZQ. intros i Hi; apply K02; flia. flia. flia.
    + eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact DQ0.
    + intros i Hi. rewrite KLO. exact (IMGC i Hi). flia.
    + eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M0 M2 (fun a => sp - 352 <= a < sp)).
      * intros a Ha Hn'. rewrite KA. apply KFR. exact Ha. exact Hn'. exact Ha. flia.
      * intros a KA' C0. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
      * rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact SCR0.
      * eapply mem_grows_trans. exact MG. exact MG2.
Qed.


End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem divO2_ok : divO2_spec L HI.
Proof.
  unfold divO2_spec. intros. eapply stage_E1; eassumption.
Qed.
End WithHeap.
End SCFG_1.
End L5DIVO2KU.
