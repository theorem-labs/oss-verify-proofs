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
     L5Core L5CoreSpecs L5CoreKitS L5Words L5WordsB L5Reduce L5ReduceG L5Cmp L5DDq L5SubMul L5Shl L5MulM L5Hp L5Norm L5NormOkA L5NormOk
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivNOkA L5DivNOkB L5DivNOkC L5DivNOkD L5DivNOkE L5DivNOkF L5DivNOkG.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKH.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVNOKA. Import L5DIVNOKB. Import L5DIVNOKC. Import L5DIVNOKD. Import L5DIVNOKE. Import L5DIVNOKF. Import L5DIVNOKG.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
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
Local Ltac uSCR := unfold DIV_SCR, L5NORM.NORM_SCR, L5MULM.MULM_SCR, L5SHL.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR,
  OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
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
Hypothesis HUGE : resize_huge_spec.
Hypothesis DIVLOOP : divloop_run_stmt.
Hypothesis DIVTAIL : divtail_stmt L HI.
Hypothesis CMP : L5CMP.cmp_spec.
Let norm_ok := L5NORMOK.norm_ok L HI LY HIok RESIZE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (X qX rr dv fdv sp r : Z) (bX : L5.bigobj) (wX : list Z).
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 X.
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 dv.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 X.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 rr.
Hypothesis G14 : getr R0 14%bv = Z_to_bv 64 0.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 sp DIV_SCR.
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis OBX : L5.big_at RSEGS M0 X bX.
Hypothesis OLX : L5C.obj_limbs RSEGS M0 bX wX.
Hypothesis STX : L5.bo_st bX = L5.BDyn 8 qX.
Hypothesis LENX : (2 <= L5.bo_len bX <= 6)%nat.
Hypothesis SGNX : Z.testbit (L5.bo_fb bX) 1 = false.
Hypothesis INQ : In (qX, 64) LB.
Hypothesis DEFQ : L5.defined M0 qX 64.
Hypothesis AX8 : X mod 8 = 0.
Hypothesis SX : sp <= X.
Hypothesis HX : X + 32 <= hl_sptop L.
Hypothesis DEFX : L5.defined M0 X 32.
Hypothesis MW : mword_obj M0 dv fdv.
Hypothesis ADV : dv mod 8 = 0.
Hypothesis SDV : sp <= dv.
Hypothesis HDV : dv + 32 <= hl_sptop L.
Hypothesis ZR : zero_obj M0 rr.
Hypothesis ARR : rr mod 8 = 0.
Hypothesis SRR : sp <= rr.
Hypothesis HRR : rr + 32 <= hl_sptop L.
Hypothesis DEFR : L5.defined M0 rr 32.
Hypothesis AP1 : X + 32 <= dv \/ dv + 32 <= X.
Hypothesis AP2 : X + 32 <= rr \/ rr + 32 <= X.
Hypothesis AP3 : dv + 32 <= rr \/ rr + 32 <= dv.
Hypothesis CR : credit_for L cr DIVN_K DIVN_BYTES.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divN_post L LB cr M0 M' R0 R' X qX rr dv fdv sp LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.
Hypothesis KONT3 : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divN_e3 L LB cr M0 M' R0 R' X qX (L5.bo_len bX) rr dv sp LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K.

(* [comment removed for export] *)
Let lenX : nat := L5.bo_len bX.
Let fbX : Z := L5.bo_fb bX.
Let nR : nat := rlen wX.
Let spd : Z := sp - 304.
Let WN : list L5.range := [(X, 32); (qX, 64); (rr, 32)].
Let Vd := VdG sp X qX rr dv fbX (Z.of_nat lenX) (Z.of_nat nR) R0.

(* [comment removed for export] *)
Let stk0 := @L5DIVNOKA.stk0 L M0 sp STK.
Let IMG := @L5DIVNOKA.IMG L LY.
Let IMGLO := @L5DIVNOKA.IMGLO L LY.
Let ERRNO := @L5DIVNOKA.ERRNO L LY R0 X qX rr dv sp bX wX LENX.
Let ERRNOV := @L5DIVNOKA.ERRNOV L LY.
Let SPTOP := @L5DIVNOKA.SPTOP L M0 sp STK.
Let SPW := @L5DIVNOKA.SPW L R0 M0 X qX rr dv sp bX wX STK LENX AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let DIV_SCR_val := L5DIVNOKA.DIV_SCR_val.
Let LBhi := @L5DIVNOKA.LBhi _ L HI HIok.
Let LBdef := @L5DIVNOKA.LBdef _ L HI HIok.
Let QX := @L5DIVNOKA.QX _ L HI LY HIok M0 model0 LB cr X qX bX HH0 OBX STX INQ.
Let wX_len := @L5DIVNOKA.wX_len M0 bX wX OLX.
Let wX_ok := @L5DIVNOKA.wX_ok M0 bX wX OLX.
Let nR_le := @L5DIVNOKA.nR_le M0 bX wX OLX.
Let fbX_rng := @L5DIVNOKA.fbX_rng M0 X bX OBX.
Let UR1 := @L5DIVNOKA.UR1 R0 X qX rr dv sp r bX wX G1 RA LENX.
Let fbX_bit0 := @L5DIVNOKA.fbX_bit0 M0 X qX bX OBX STX.
Let kept_above := @L5DIVNOKB.kept_above _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let kept_inblock := @L5DIVNOKB.kept_inblock _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let cdef_above := @L5DIVNOKB.cdef_above _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let cdef_inblock := @L5DIVNOKB.cdef_inblock _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let stage_G1 := @L5DIVNOKG.stage_G1 _ L HI LY HIok KPOS BPOS COPYA ASSIGN RESIZE HUGE DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX OLX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 CR KONT KONT3.
Local Ltac slia :=
  match goal with
  | A : 140735332483072 + 8848 <= ?s, B : ?s <= 2 ^ 47, C : ?s <= hl_sptop _ |- _ => generalize A B C SX SDV SRR HX HDV HRR SPTOP; clear; intros; lia
  end.
Local Ltac kcw K H := first [ eapply u64_at_agree1 | eapply u8_at_agree1 | eapply big_at_agree1 ];
  [ intros i Hi; apply K; generalize Hi SX; unfold spd; slia | slia | slia | exactA H ].

Lemma land2_zero f : 0 <= f < 256 -> Z.testbit f 1 = false -> Z.land f 2 = 0.
Proof using R0 M0 X qX rr dv sp bX wX OBX OLX LENX.
  intros Hf Hb. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec k 1) as [->|Nk]. rewrite Hb. reflexivity.
  replace (Z.testbit 2 k) with false. apply Bool.andb_false_r. symmetry.
  destruct (Z.eq_dec k 0) as [->|Nk0]. reflexivity. rewrite (Z.bits_above_log2 2 k). reflexivity. lia. cbn. lia.
Qed.
Lemma land253_bits f : Z.testbit (Z.land f 253) 0 = Z.testbit f 0 /\ Z.testbit (Z.land f 253) 1 = false.
Proof. rewrite !Z.land_spec. split. apply Bool.andb_true_r. apply Bool.andb_false_r. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E4 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B1 fnum fden : Z) :
  let LBc := (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 19) = Z_to_bv 64 1 ->
  getr R (reg 20) = Z_to_bv 64 (sp - 120) -> getr R (reg 21) = Z_to_bv 64 (sp - 120) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 25) = getr R0 (reg 25) ->
  getr R (reg 26) = Z_to_bv 64 0 -> getr R (reg 27) = Z_to_bv 64 rr ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  block_range L B1 64 /\ blocks_apart B1 64 LB -> crc = debit L cr 64 ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 168) (L5.BO fnum lenX (L5.BDyn 8 B1)) -> Z.testbit fnum 1 = false -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 1 (L5.BInl MWORD 0)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M X bX -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DS.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x21e3c M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H10 H18 H19 H20 H21 H23 H25 H26 H27 MBV HH [BR1 BA1] CRC DS OBn Fnb1 LAn OBd Fdb1 OBXc DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof wX_len as WL. unfold lenX in WL.
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof BR1 as (B1a & B1b & B1c & B1d & B1e).
  pose proof OBn as (N0 & Nr & N8 & Nb0 & N16 & N24 & Nlen & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in N0, Nr, N8, Nb0, N16, N24, Nlen.
  pose proof OBd as (D0 & Dr & D8 & Db0 & D16 & D24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in D0, Dr, D8, Db0, D16, D24.
  pose proof OBXc as OBq. unfold L5.big_at in OBq. rewrite STX in OBq. fold fbX lenX in OBq. destruct OBq as (U0 & _ & U8 & Ub0 & U16 & U24 & _).
  assert (WFR: L5.writable RSEGS M (sp - 304) 304).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d5e4n_conc fx R M (Vd B1 0 1 0 fnum 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold MWORD; flia)
              H2 H9 H10 H18 H19 H21 H23 ltac:(flia) A16 WFR N0 ltac:(exactA N8) ltac:(exactA N24) ltac:(exactA D16) ltac:(flia) ltac:(flia) Nb0 ltac:(flia) ltac:(flia)
              ltac:(unfold MWORD; flia) ltac:(unfold srl_range, MWORD; change ((2 ^ 64 - 1) / 4294967296) with 4294967295; lia) ltac:(flia) ltac:(flia) AX8 ltac:(left; flia) U0 ltac:(flia) Ub0 U24 ltac:(flia))
    as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A11 & A19 & A22 & A23 & A24 & C256)). clear P.
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 256 <= i < sp - 248) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1. apply FRZ. exact Hi. generalize N1; clear; intros; lia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_le_gt_dec (sp - 256) a) as [Ca|Ca]; [destruct (Z_lt_le_dec a (sp - 248)) as [Cb|Cb]|].
    right; left; flia. all: left; apply KFR; flia. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  apply (stage_G1 fx1 R1 M1 model crc B1 fnum fden).
  all: try (rewrite (KS _) by inl; assumption).
  - exact A22. - exact A23. - exact A24. - exact MBV. - exact HH1. - split; assumption. - exact CRC.
  - eapply div_saves_kept. 4: exact DS. intros i Hi. apply KFR; generalize Hi; slia. flia. flia.
  - kcw KFR OBn. - exact Fnb1.
  - eapply L5C.limbs_at_agree. 4: exact LAn. 2: flia. 2: flia. intros i Hi. apply KFR. flia. generalize Hi B1e SLO' WL LENX; clear; intros; lia.
  - kcw KFR OBd. - exact Fdb1. - exact C256.
  - kcw KFR OBXc.
  - eapply L5.defined_grows. exact MG. exact DQ.
  - eapply L5.defined_grows. exact MG. exact DX.
  - kcw KFR ZRc.
  - eapply L5.defined_grows. exact MG. exact DR.
  - destruct MWc as [OBv SGv]. split. 2: exact SGv. kcw KFR OBv.
  - eapply (L5HP.hpres_trans L LB LB sp DIV_SCR [] M0 M M1 sp DIV_SCR []). exact HP.
    + eapply (L5HP.hpres_piece L LB sp DIV_SCR [] M M1 (fun a => sp - 256 <= a < sp - 248)).
      * intros a Ha Hn'. apply KFR. exact Ha. exact Hn'.
      * intros a KA' C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
      * rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG. exact SCR0.
      * exact MG.
    + intros a KA'; exact KA'. + intros b Hb; exact Hb. + fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B1 fnum fden : Z) :
  let LBc := (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 fden -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 19) = Z_to_bv 64 1 ->
  getr R (reg 20) = Z_to_bv 64 (sp - 120) -> getr R (reg 21) = Z_to_bv 64 (sp - 120) -> getr R (reg 22) = Z_to_bv 64 fbX -> getr R (reg 23) = Z_to_bv 64 0 ->
  getr R (reg 25) = getr R0 (reg 25) -> getr R (reg 27) = Z_to_bv 64 rr ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  block_range L B1 64 /\ blocks_apart B1 64 LB -> crc = debit L cr 64 ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 168) (L5.BO fnum lenX (L5.BDyn 8 B1)) -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 1 (L5.BInl MWORD 0)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M X bX -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DS.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x21e08 M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H18 H19 H20 H21 H22 H23 H25 H27 MBV HH [BR1 BA1] CRC DS OBn LAn OBd Fdb1 OBXc DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof wX_len as WL. pose proof wX_ok as WO. unfold lenX in WL.
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof BR1 as (B1a & B1b & B1c & B1d & B1e).
  pose proof OBn as (N0 & Nr & N8 & Nb0 & N16 & N24 & Nlen & Ncap & N8' & Nlo & Nhi & Nhap). cbn [L5.bo_fb L5.bo_len L5.bo_st] in N0, Nr, N8, Nb0, N16, N24, Nlen, Nlo, Nhi, Nhap.
  pose proof OBd as (D0 & Dr & D8 & Db0 & D16 & D24 & Dle & Dv0 & Dv1). cbn [L5.bo_fb L5.bo_len L5.bo_st] in D0, Dr, D8, Db0, D16, D24.
  assert (WFR: L5.writable RSEGS M (sp - 304) 304).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d5e3_conc fx R M (Vd 0 fden 0 0 fnum 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H8 H22 ltac:(flia) A16 WFR N0 D0 ltac:(flia) ltac:(flia) ltac:(flia))
    as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A8 & A10 & A11 & A26 & C136 & C168)). clear P.
  rewrite (land2_zero fden Dr Fdb1) in A8. rewrite (land2_zero fbX FBX SGNX) in A8, A26. cbn in A8, A26.
  apply BG.word_of_unsigned in A8. apply BG.word_of_unsigned in A26.
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 168 <= i < sp - 167) -> ~ (sp - 136 <= i < sp - 135) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2. apply FRZ. exact Hi. generalize N1; clear; intros; lia. generalize N2; clear; intros; lia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_le_gt_dec (sp - 168) a) as [Ca|Ca]; [destruct (Z_lt_le_dec a (sp - 135)) as [Cb|Cb]|].
    right; left; flia. all: left; apply KFR; flia. }
  (* [comment removed for export] *)
  set (fnum' := Z.land fnum 253) in C168. set (fden' := Z.land fden 253) in C136.
  pose proof (land253_bits fnum) as [FN0 FN1]. pose proof (land253_bits fden) as [FD0 FD1]. fold fnum' in FN0, FN1. fold fden' in FD0, FD1.
  assert (FNR: 0 <= fnum' < 256). { subst fnum'. apply L5.land_byte_range. lia. }
  assert (FDR: 0 <= fden' < 256). { subst fden'. apply L5.land_byte_range. lia. }
  assert (OBn1: L5.big_at RSEGS M1 (sp - 168) (L5.BO fnum' lenX (L5.BDyn 8 B1))).
  { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact C168. split. exact FNR.
    split. { eapply u64_at_agree1. 4: exact N8. intros i Hi; apply KFR; generalize Hi; slia. slia. slia. }
    split. rewrite FN0. exact Nb0.
    split. { eapply u64_at_agree1. 4: exact N16. intros i Hi; apply KFR; generalize Hi; slia. slia. slia. }
    split. { eapply u64_at_agree1. 4: exact N24. intros i Hi; apply KFR; generalize Hi; slia. slia. slia. }
    repeat split; try assumption; lia. }
  assert (OBd1: L5.big_at RSEGS M1 (sp - 136) (L5.BO fden' 1 (L5.BInl MWORD 0))).
  { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact C136. split. exact FDR.
    split. { eapply u64_at_agree1. 4: exact D8. intros i Hi; apply KFR; generalize Hi; slia. slia. slia. }
    split. rewrite FD0. exact Db0.
    split. { eapply u64_at_agree1. 4: exact D16. intros i Hi; apply KFR; generalize Hi; slia. slia. slia. }
    split. { eapply u64_at_agree1. 4: exact D24. intros i Hi; apply KFR; generalize Hi; slia. slia. slia. }
    repeat split; try assumption; unfold MWORD; lia. }
  assert (LAn1: L5.limbs_at RSEGS M1 B1 wX).
  { eapply L5C.limbs_at_agree. 4: exact LAn. 2: flia. 2: flia. intros i Hi. apply KFR. flia.
    generalize Hi B1e SLO' WL LENX; clear; intros; lia. generalize Hi B1e SLO' WL LENX; clear; intros; lia. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  eapply (CMP fx1 R1 M1 model K (sp - 168) (sp - 136) 0x21e3c (L5.BO fnum' lenX (L5.BDyn 8 B1)) (L5.BO fden' 1 (L5.BInl MWORD 0)) wX [MWORD] Mh Ml A10 A11 A1).
  - split. flia. reflexivity.
  - unfold L5CMP.cmp_obj. cbn [L5.bo_fb L5.bo_len L5.bo_data L5.bo_st]. split. exact OBn1. split. exact FN1. split. lia. split. lia.
    split. rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16); reflexivity. split. flia. split. flia. split. flia. split. flia.
    eapply L5.defined_grows. exact MG. eapply L5.defined_sub. pose proof (LBdef _ _ _ _ HH B1 64 ltac:(left; reflexivity)) as (DB1 & _). exact DB1. lia. lia.
  - unfold L5CMP.cmp_obj. cbn [L5.bo_fb L5.bo_len L5.bo_data L5.bo_st]. split. exact OBd1. split. exact FD1. split. lia. split. lia.
    split. rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16); reflexivity. split. flia. split. flia. split. flia. split. flia.
    eapply L5.defined_grows. exact MG. eapply L5.defined_sub. exact SCR0. flia. flia.
  - split. cbn [L5.bo_len]. exact WL. split. exact WO. exact LAn1.
  - split. reflexivity. split. repeat constructor; unfold MWORD; lia. reflexivity.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 POST. destruct POST as (K2 & RP & (c & A10' & RSZ & _) & FR2 & MG2).
    pose proof (mem_eq M1 M2 FR2) as EM2. subst M2.
    assert (Hc: c = 1). { destruct RSZ as (_ & _ & GT). apply GT. cbn [L5.bo_len]. lia. } subst c.
    assert (REGS: forall i v, In i L5CMP.cmp_kept -> In i KS_d5e3 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (K2 i Hi). rewrite (KS i Hk). exact Hv. }
    apply (stage_E4 fx2 R2 M1 model crc B1 fnum' fden').
    all: try (eapply REGS; [inl | inl | assumption]).
    + rewrite (K2 8%nat) by inl. exact A8.
    + exact A10'.
    + rewrite (K2 26%nat) by inl. exact A26.
    + exact MBV. + exact HH1. + split; assumption. + exact CRC.
    + eapply div_saves_kept. 4: exact DS. intros i Hi. apply KFR; generalize Hi; slia. flia. flia.
    + exact OBn1. + exact FN1. + exact LAn1. + exact OBd1. + exact FD1.
    + kcw KFR OBXc.
    + eapply L5.defined_grows. exact MG. exact DQ.
    + eapply L5.defined_grows. exact MG. exact DX.
    + kcw KFR ZRc.
    + eapply L5.defined_grows. exact MG. exact DR.
    + destruct MWc as [OBv SGv]. split. 2: exact SGv. kcw KFR OBv.
    + eapply (L5HP.hpres_trans L LB LB sp DIV_SCR [] M0 M M1 sp DIV_SCR []). exact HP.
      * eapply (L5HP.hpres_piece L LB sp DIV_SCR [] M M1 (fun a => sp - 168 <= a < sp - 135)).
        -- intros a Ha Hn'. apply KFR. exact Ha. generalize Hn'; clear; intros; lia. generalize Hn'; clear; intros; lia.
        -- intros a KA' C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
        -- rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG. exact SCR0.
        -- exact MG.
      * intros a KA'; exact KA'. * intros b Hb; exact Hb. * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKH.
