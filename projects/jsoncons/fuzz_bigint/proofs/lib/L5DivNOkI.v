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
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivNOkA L5DivNOkB L5DivNOkC L5DivNOkD L5DivNOkE L5DivNOkF L5DivNOkG L5DivNOkH.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKI.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVNOKA. Import L5DIVNOKB. Import L5DIVNOKC. Import L5DIVNOKD. Import L5DIVNOKE. Import L5DIVNOKF. Import L5DIVNOKG. Import L5DIVNOKH.

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
Let stage_E3 := @L5DIVNOKH.stage_E3 _ L HI LY HIok KPOS BPOS COPYA ASSIGN RESIZE HUGE DIVLOOP DIVTAIL CMP R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX OLX STX LENX SGNX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 CR KONT KONT3.
Local Ltac slia :=
  match goal with
  | A : 140735332483072 + 8848 <= ?s, B : ?s <= 2 ^ 47, C : ?s <= hl_sptop _ |- _ => generalize A B C SX SDV SRR HX HDV HRR SPTOP; clear; intros; lia
  end.
Local Ltac kcw K H := first [ eapply u64_at_agree1 | eapply u8_at_agree1 | eapply big_at_agree1 ];
  [ intros i Hi; apply K; generalize Hi SX; unfold spd; slia | slia | slia | exactA H ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E2 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (fden : Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 25) = getr R0 (reg 25) -> getr R (reg 27) = Z_to_bv 64 rr ->
  model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 1 (L5.BInl MWORD 0)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M X bX -> L5.limbs_at RSEGS M qX wX -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DS.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x21dd4 M model) K.
Proof.
  intros H2 H9 H3 H4 H18 H23 H25 H27 MBV HH DS OBd Fdb1 OBXc LAX DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof wX_len as WL. pose proof wX_ok as WO. unfold lenX in WL.
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof (credit_chain L cr KPOS BPOS CR) as (CR1 & _ & _).
  pose proof OBd as (D0 & Dr & D8 & Db0 & D16 & D24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in D0, Dr, D8, Db0, D16, D24.
  pose proof OBXc as OBq. unfold L5.big_at in OBq. rewrite STX in OBq. fold fbX lenX in OBq. destruct OBq as (U0 & _ & U8 & Ub0 & U16 & U24 & _).
  pose proof DS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
  assert (WFR: L5.writable RSEGS M (sp - 304) 304).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  assert (UR: forall k, 0 <= U R0 k < 2 ^ 64). { intros k. unfold U. apply (BL.bvu_range (getr R0 (Z_to_bv 5 k))). }
  unfold cfg.
  pose proof (d5e2n_conc fx R M (Vd 0 fden 1 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
              ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR) ltac:(apply UR)
              H2 H9 H18 H23 H27 ltac:(flia) A16 WFR S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 D0 ltac:(exactA D8) ltac:(flia) Db0 ltac:(flia) ltac:(flia) AX8 ltac:(left; flia) U0 ltac:(flia))
    as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A8 & A10 & A11 & A12 & A19 & A20 & A21 & A22)). clear P.
  pose proof (mem_eq M M1 FR) as EM1. subst M1.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  destruct (defined_byte M (sp - 168) ltac:(eapply L5.defined_sub; [exact SCR0 | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo & FBO & UFBO).
  eapply (COPYA fx1 R1 M model K LB cr (sp - 168) X spd 0x21e08 fbo bX wX HH MOK HK0 A10 A11).
  - unfold L5.bo_cap. rewrite STX. intros _. split. lia. exact CR1.
  - exact A1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact UFBO. - exact FBO.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia.
  - exact OBXc.
  - split. symmetry. exact (eq_sym WL). split. exact WO. rewrite STX. exact LAX.
  - exact AX8. - unfold spd; flia. - exact HX.
  - rewrite STX. intros cap q E. injection E. intros <- <-. exact INQ.
  - left. unfold spd; flia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & GPOST). destruct g as [|B1 cap].
    { exfalso. destruct GPOST as (F & _). unfold L5.bo_dyn in F. pose proof fbX_bit0 as FB0. unfold fbX in FB0. rewrite FB0 in F. discriminate F. }
    destruct GPOST as (_ & Hcap & -> & -> & FB1 & OB2 & OL2 & HP2). unfold L5.bo_cap in Hcap. rewrite STX in Hcap. subst cap.
    fold fbX lenX in OB2, OL2.
    pose proof FB1 as (BR1 & BA1 & DF1). pose proof BR1 as (B1a & B1b & B1c & B1d & B1e).
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (sp - 168 <= a < sp - 136) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1. apply (kept_above M M2 LB COPY_SCR _ a HP2). uSCR; clear; lia. exact Ha. apply outside1. generalize N1; clear; intros; lia. }
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
    assert (REGS: forall i v, In i cs_all -> In i KS_d5e2n -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    set (fnum := copy_fb fbo fbX true) in OB2, OL2.
    apply (stage_E3 fx2 R2 M2 model2 (debit L cr (8 * 8)) B1 fnum fden).
    all: try (eapply REGS; [inl | inl | assumption]).
    + rewrite (preserved_sregs R1 R2 8 RP) by inl. exact A8.
    + rewrite (preserved_sregs R1 R2 19 RP) by inl. exact A19.
    + rewrite (preserved_sregs R1 R2 20 RP) by inl. exact A20.
    + rewrite (preserved_sregs R1 R2 21 RP) by inl. exact A21.
    + rewrite (preserved_sregs R1 R2 22 RP) by inl. exact A22.
    + exact MBV02. + exact HH2. + split; assumption. + reflexivity.
    + eapply div_saves_kept. 4: exact DS. intros i Hi. apply KA; generalize Hi; unfold spd; slia. flia. flia.
    + exact OB2.
    + destruct OL2 as (_ & _ & LA2). exact LA2.
    + kcw KA OBd. + exact Fdb1.
    + kcw KA OBXc.
    + eapply (cdef_inblock M M2 LB cr _ COPY_SCR _ qX 64 qX 64 HH HP2). exact INQ. lia. lia. exact DQ.
    + eapply (cdef_above M M2 LB COPY_SCR _ X 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DX.
    + kcw KA ZRc.
    + eapply (cdef_above M M2 LB COPY_SCR _ rr 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DR.
    + destruct MWc as [OBv SGv]. split. 2: exact SGv. kcw KA OBv.
    + eapply (L5HP.hpres_trans L LB LB sp DIV_SCR [] M0 M M2 spd COPY_SCR). exact HP. exact HP2.
      * intros a KA'. eapply L5HP.kept_mono. exact KA'. { intros b Hb. exact Hb. }
        unfold spd; fsclia. unfold spd; flia.
        intros _. apply outside1. pose proof (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) ltac:(fsclia) ltac:(rewrite IMG; flia)) as NS.
        generalize NS; clear; uSCR; intros; lia.
      * intros b Hb. exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_E1 : srealizes RSEGS SCFG (cfg R0 DIVIDE M0 model0) K.
Proof.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof MOK0 as (Mh & Ml & _).
  pose proof wX_len as WL. pose proof wX_ok as WO. unfold lenX in WL.
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia. assert (DVHI: dv + 32 <= 2 ^ 47) by flia.
  pose proof STK as (_ & _ & _ & _ & SCR0). rewrite DIV_SCR_val in SCR0.
  pose proof MW as [OBd SGd]. pose proof OBd as (D0 & Dr & D8 & (Db0 & D16 & D24 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in D0, Dr, D8, Db0, D16, D24.
  assert (WFR: L5.writable RSEGS M0 (sp - 304) 304).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d5e1_conc fx0 R0 M0 (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
              ltac:(rewrite <- r2; exact G2) ltac:(rewrite <- r10; exact G10) ltac:(rewrite <- r11; exact G11) ltac:(rewrite <- r12; exact G12)
              ltac:(rewrite <- r13; exact G13) ltac:(rewrite <- r14; exact G14) ltac:(flia) A16 WFR)
    as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A2 & A9 & A10 & A12 & A18 & A23 & A27 & S27 & S26 & S25 & S24 & S23 & S22 & S21 & S20 & S19 & S18 & S9 & S8 & S1)). clear P.
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 304 <= i < sp) -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
  { intros i Hi N1. apply FRZ. exact Hi. generalize N1; clear; intros; lia. }
  assert (KUP: forall i, sp <= i < 2 ^ 64 -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)). { intros i Hi. apply KFR; generalize Hi SLO; clear; intros; lia. }
  assert (HH1: hi_heap HI LB cr M1 (m_vmmaps model0)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M0 M1). exact HIok. exact HH0. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_le_gt_dec (sp - 304) a) as [Ca|Ca]; [destruct (Z_lt_le_dec a sp) as [Cb|Cb]|].
    right; left; flia. all: left; apply KFR; flia. }
  assert (DS1: div_saves M1 sp R0). { unfold div_saves. repeat split; assumption. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  destruct (defined_byte M1 (sp - 136) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG | exact SCR0] | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo & FBO & UFBO).
  assert (OBd1: L5.big_at RSEGS M1 dv (L5.BO fdv 1 (L5.BInl MWORD 0))) by kcw KUP OBd.
  assert (OLd: L5C.obj_limbs RSEGS M1 (L5.BO fdv 1 (L5.BInl MWORD 0)) [MWORD]). { split. reflexivity. split. repeat constructor; unfold MWORD; lia. reflexivity. }
  eapply (COPYA fx1 R1 M1 model0 K LB cr (sp - 136) dv spd 0x21dd4 fbo (L5.BO fdv 1 (L5.BInl MWORD 0)) [MWORD] HH1 MOK0 HK0 A10 ltac:(rewrite r11; rewrite (KS 11%nat) by inl; rewrite <- r11; exact G11)).
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite Db0. intros F; discriminate F.
  - exact A1.
  - split. flia. reflexivity.
  - rewrite r2. exact A2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact G4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. eapply L5.defined_grows. exact MG. exact SCR0. flia. flia.
  - exact UFBO. - exact FBO.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. eapply L5.defined_grows. exact MG. exact SCR0. flia. flia. flia. flia.
  - exact OBd1. - exact OLd.
  - exact ADV. - unfold spd; flia. - exact HDV.
  - cbn [L5.bo_st]. intros cap q E. discriminate E.
  - left. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & GPOST). destruct g as [|A cap].
    2:{ exfalso. destruct GPOST as (F & _). unfold L5.bo_dyn in F. cbn [L5.bo_fb] in F. rewrite Db0 in F. discriminate F. }
    destruct GPOST as (_ & -> & -> & OB2 & FB2 & MG2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB2.
    assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 136 <= a < sp - 104) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha N1. apply FB2. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by exact Ha. generalize N1; clear; intros; lia. }
    assert (KUP2: forall i, sp <= i < 2 ^ 64 -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)). { intros i Hi. apply KA; generalize Hi SLO; clear; intros; lia. }
    assert (REGS: forall i v, In i cs_all -> In i KS_d5e1 -> getr R0 (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    set (fden := copy_fb fbo fdv false) in OB2.
    assert (FD1: Z.testbit fden 1 = false). { subst fden. unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec, SGd. cbn. rewrite Bool.andb_false_r. reflexivity. }
    apply (stage_E2 fx2 R2 M2 model2 fden).
    + rewrite (preserved_sregs R1 R2 2 RP) by inl. exact A2.
    + rewrite (preserved_sregs R1 R2 9 RP) by inl. exact A9.
    + eapply REGS. inl. inl. rewrite <- r3. exact G3.
    + eapply REGS. inl. inl. rewrite <- r4. exact G4.
    + rewrite (preserved_sregs R1 R2 18 RP) by inl. exact A18.
    + rewrite (preserved_sregs R1 R2 23 RP) by inl. exact A23.
    + eapply REGS. inl. inl. reflexivity.
    + rewrite (preserved_sregs R1 R2 27 RP) by inl. exact A27.
    + exact MBV2. + exact HH2.
    + eapply div_saves_kept. 4: exact DS1. intros i Hi. apply KA; generalize Hi; slia. flia. flia.
    + exact OB2. + exact FD1.
    + assert (OBX1: L5.big_at RSEGS M1 X bX) by kcw KUP OBX. kcw KUP2 OBX1.
    + pose proof OLX as (_ & _ & LA0). rewrite STX in LA0.
      eapply L5C.limbs_at_agree. 4: exact LA0. 2: flia. 2: flia. intros i Hi. rewrite KA. apply KFR. flia.
      generalize Hi Q3 SLO' WL LENX; clear; intros; lia. flia. generalize Hi Q3 SLO' WL LENX; clear; intros; lia.
    + eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact DEFQ.
    + eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact DEFX.
    + assert (ZR1: L5DS.zero_obj M1 rr) by kcw KUP ZR. kcw KUP2 ZR1.
    + eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact DEFR.
    + split. 2: exact SGd. kcw KUP2 OBd1.
    + eapply (L5HP.hpres_piece L LB sp DIV_SCR [] M0 M2 (fun a => sp - 304 <= a < sp)).
      * intros a Ha Hn'. rewrite KA. apply KFR. exact Ha. exact Hn'. exact Ha. generalize Hn'; clear; intros; lia.
      * intros a KA' C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
      * rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG2. eapply L5.defined_grows. exact MG. exact SCR0.
      * eapply mem_grows_trans. exact MG. exact MG2.
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem divN_ok : divN_spec L HI.
Proof.
  unfold divN_spec. intros.
  eapply stage_E1; eassumption.
Qed.

End WithHeap.
End SCFG_1.
End L5DIVNOKI.
