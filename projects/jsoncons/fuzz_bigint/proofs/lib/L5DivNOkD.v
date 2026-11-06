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
     L5Core L5CoreSpecs L5CoreKitS L5Words L5WordsB L5Reduce L5ReduceG L5DDq L5SubMul L5Shl L5MulM L5Hp L5Norm L5NormOkA L5NormOk
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivNOkA L5DivNOkB L5DivNOkC.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKD.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVNOKA. Import L5DIVNOKB. Import L5DIVNOKC.

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
Let stage_G7 := @L5DIVNOKC.stage_G7 _ L HI LY HIok KPOS BPOS RESIZE DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX OLX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 CR KONT KONT3.

Lemma Forall_firstn' {A} (P : A -> Prop) n : forall l, Forall P l -> Forall P (firstn n l).
Proof. induction n as [|n IH]; intros [|x l] H; cbn; try constructor. inversion H; assumption. apply IH. inversion H; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G6 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden : Z) :
  let LBc := (B0, 64) :: (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 19) = Z_to_bv 64 (Z.of_nat nR) ->
  getr R (reg 20) = Z_to_bv 64 (sp - 120) -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 qX ->
  getr R (reg 25) = Z_to_bv 64 (Z.of_nat nR - 1) -> getr R (reg 26) = Z_to_bv 64 0 -> getr R (reg 27) = Z_to_bv 64 rr -> (1 <= nR)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> B0 <> B1 -> crc = debit L (debit L cr 64) 64 ->
  div_saves M sp R0 -> locals_N M sp B0 B1 fd0 fn0 fnum fden -> Z.testbit fnum 1 = false -> L5.u64_at RSEGS M (sp - 120) MWORD ->
  L5.u64_at RSEGS M (sp - 264) (X + 16) -> L5.u64_at RSEGS M (sp - 256) 0 ->
  L5.big_at RSEGS M (sp - 168) (L5.BO fnum nR (L5.BDyn 8 B1)) -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DS.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x2212c M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H18 H19 H20 H21 H24 H25 H26 H27 HnR MBV HH NE01 CRC DS LOC FN1 C120 C264 C256 OBn LAn OBq DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hn: (nR <= 6)%nat). { pose proof nR_le. unfold lenX in *. clear - H LENX. lia. }
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof (credit_chain L cr KPOS BPOS CR) as (_ & _ & CR3).
  pose proof (LBdef _ _ _ _ HH B1 64 ltac:(right; left; reflexivity)) as (DB1 & (B1lo & B1img) & B1hi & _).
  pose proof (LBdef _ _ _ _ HH B0 64 ltac:(left; reflexivity)) as (DB0 & (B0lo & B0img) & B0hi & _).
  unfold cfg.
  pose proof (d5g6_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) H2 H27 ltac:(flia) A16) as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11)). clear P.
  pose proof (mem_eq M M1 FR) as EM1. subst M1.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  assert (OLn: L5C.obj_limbs RSEGS M (L5.BO fnum nR (L5.BDyn 8 B1)) (firstn nR wX)).
  { pose proof wX_len as WL. pose proof wX_ok as WO. unfold lenX in WL.
    split. { cbn [L5.bo_len]. rewrite length_firstn. lia. }
    split. { apply Forall_firstn'. exact WO. } cbn [L5.bo_st]. apply L5C.limbs_at_firstn. exact LAn. }
  eapply (ASSIGN fx1 R1 M model K LBc crc rr (sp - 168) spd 0x22138 (L5.BO 0 0 (L5.BInl 0 0)) (L5.BO fnum nR (L5.BDyn 8 B1)) (firstn nR wX)
            HH MOK HK0 A10 A11).
  - cbn [L5.bo_len]. flia.
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. intros F. discriminate F.
  - cbn [L5.bo_len]. intros _ _. replace (round_up (Z.of_nat nR)) with 8. rewrite CRC. exact CR3.
    unfold round_up. replace (Z.of_nat nR / 8) with 0. reflexivity. symmetry. apply Z.div_small. lia.
  - exact A1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact ZRc.
  - exact ARR. - unfold spd; flia. - exact HRR.
  - apply (L5C.writable_of_defined RSEGS). exact DR. flia. flia.
  - cbn. intros cap q E. discriminate E.
  - exact OBn.
  - exact OLn.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - cbn. intros cap q E. injection E. intros <- <-. right. left. reflexivity.
  - right. flia.
  - cbn. intros c q c' q' E. discriminate E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & A10' & GPOST). cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_data] in GPOST.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
    assert (HP2W: exists W2, L5C.hpres L LBc spd ASSIGN_SCR W2 M M2 /\ (forall a, ~ (rr <= a < rr + 32) -> L5.outside W2 a)).
    { destruct g as [|A cap].
      - destruct GPOST as (DYS & _ & _ & _ & HP2). eexists. split. exact HP2. intros a N1. apply outside2. exact N1.
        destruct DYS as [DY|SM]. { unfold L5.bo_dyn in DY. cbn in DY. discriminate DY. } flia.
      - destruct GPOST as (_ & _ & _ & _ & _ & _ & _ & _ & HP2). eexists. split. exact HP2. intros a N1. apply outside1. exact N1. }
    destruct HP2W as (W2 & HP2 & OW2).
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (rr <= a < rr + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1. apply (kept_above M M2 LBc ASSIGN_SCR _ a HP2). uSCR; clear; lia. exact Ha. apply OW2. exact N1. }
    assert (DQ2: L5.defined M2 qX 64).
    { eapply (cdef_inblock M M2 LBc crc _ ASSIGN_SCR _ qX 64 qX 64 HH HP2). right. right. exact INQ. lia. lia. exact DQ. }
    assert (OBq2: L5.big_at RSEGS M2 X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX))).
    { eapply big_at_agree1. 4: exact OBq. intros i Hi. apply KA; unfold spd. flia. generalize AP2 Hi; clear; lia. flia. flia. }
    assert (DS2: div_saves M2 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (LOC2: locals_N M2 sp B0 B1 fd0 fn0 fnum fden). { eapply locals_N_kept. 4: exact LOC. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (C120': L5.u64_at RSEGS M2 (sp - 120) MWORD). { eapply u64_at_agree1. 4: exact C120. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (C264': L5.u64_at RSEGS M2 (sp - 264) (X + 16)). { eapply u64_at_agree1. 4: exact C264. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (C256': L5.u64_at RSEGS M2 (sp - 256) 0). { eapply u64_at_agree1. 4: exact C256. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (DX2: L5.defined M2 X 32). { eapply (cdef_above M M2 LBc ASSIGN_SCR _ X 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DX. }
    assert (DR2: L5.defined M2 rr 32). { eapply (cdef_above M M2 LBc ASSIGN_SCR _ rr 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DR. }
    assert (MW2: mword_obj M2 dv fdv).
    { destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KA; unfold spd. flia. generalize AP3 Hi; clear; lia. flia. flia. }
    assert (REGS: forall i v, In i cs_all -> In i KS_d5g6 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    assert (HPc: L5C.hpres L LB sp DIV_SCR WN M0 M2).
    { eapply (L5HP.hpres_trans L LB LBc sp DIV_SCR WN M0 M M2 spd ASSIGN_SCR). exact HP. exact HP2.
      * intros a KA'. eapply L5HP.kept_mono. exact KA'. { intros b Hb. right; right; exact Hb. }
        unfold spd; fsclia. unfold spd; flia.
        intros OW. apply OW2. apply (L5HP.outside_in _ _ rr 32 OW). cbn; right; right; left; reflexivity.
      * intros b Hb. right; right; exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP). }
    assert (FRB: forall f, 0 <= f < 256 -> Z.testbit f 1 = false -> Z.land f 2 = 0).
    { intros f Hf Hb. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec k 1) as [->|Nk]. rewrite Hb. reflexivity.
      replace (Z.testbit 2 k) with false. apply Bool.andb_false_r. symmetry. 
      destruct (Z.eq_dec k 0) as [->|Nk0]. reflexivity. rewrite (Z.bits_above_log2 2 k). reflexivity. lia. cbn. lia. }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct GPOST as (DYS & -> & -> & (st' & OB2 & OL2 & SAME) & _).
      destruct st' as [u0 u1|cap' q']. 2: contradiction.
      assert (HnR2: (nR <= 2)%nat). { destruct DYS as [DY|SM]. unfold L5.bo_dyn in DY. cbn in DY. discriminate DY. exact SM. }
      set (frem := assign_fb 0 fnum nR false) in OB2, OL2.
      assert (FREM: frem = 0).
      { subst frem. unfold assign_fb. destruct (Nat.eqb_spec nR 0). lia. rewrite Z.land_0_l, Z.lor_0_l. apply FRB.
        pose proof OBn as (_ & Nf & _). exact Nf. exact FN1. }
      rewrite FREM in OB2, OL2.
      apply (stage_G7 fx2 R2 M2 model2 LBc crc B0 B1 fd0 fn0 fnum fden 0 (L5.BInl u0 u1) (firstn nR wX)).
      all: try (eapply REGS; [inl | inl | assumption]).
      * exact HnR. * exact MBV02. * exact HH2. * reflexivity. * exact NE01. * exact CRC.
      * exact DS2. * exact LOC2. * exact C120'. * exact C264'. * exact C256'. * exact OBq2. * exact DQ2. * exact DX2.
      * exact OB2. * exact OL2. * exact I. * exact DR2. * exact MW2. * exact HPc.
    + (* [comment removed for export] *)
      destruct GPOST as (DYF & H3n & Hcap & -> & -> & FB & OB2 & OL2 & _).
      replace (round_up (Z.of_nat nR)) with 8 in Hcap. 2:{ unfold round_up. replace (Z.of_nat nR / 8) with 0. reflexivity. symmetry. apply Z.div_small. lia. }
      subst cap. rewrite CRC in *.
      set (frem := assign_fb 0 fnum nR true) in OB2, OL2.
      assert (FREM: frem = 1).
      { subst frem. unfold assign_fb. destruct (Nat.eqb_spec nR 0). lia. rewrite Z.lor_0_l. change (Z.land 1 253) with 1. rewrite (FRB fnum).
        reflexivity. pose proof OBn as (_ & Nf & _). exact Nf. exact FN1. }
      rewrite FREM in OB2, OL2.
      pose proof FB as (BRA & BAA & DFA). pose proof BRA as (BA0 & BA1 & BA2 & BA3 & BA4).
      assert (NA0: A <> B0). { pose proof (BAA (B0, 64) ltac:(left; reflexivity)) as Hb. cbn in Hb. lia. }
      assert (NA1: A <> B1). { pose proof (BAA (B1, 64) ltac:(right; left; reflexivity)) as Hb. cbn in Hb. lia. }
      apply (stage_G7 fx2 R2 M2 model2 ((A, 8 * 8) :: LBc) (debit L (debit L (debit L cr 64) 64) (8 * 8)) B0 B1 fd0 fn0 fnum fden 1 (L5.BDyn 8 A) (firstn nR wX)).
      all: try (eapply REGS; [inl | inl | assumption]).
      * exact HnR. * exact MBV02. * exact HH2. * reflexivity. * exact NE01. * apply credit_after3.
      * exact DS2. * exact LOC2. * exact C120'. * exact C264'. * exact C256'. * exact OBq2. * exact DQ2. * exact DX2.
      * exact OB2. * exact OL2.
      * unfold rem_store. split. reflexivity. split. exact BRA. split. { intros b Hb. apply BAA. right; right; exact Hb. }
        split. exact DFA. split. exact NA0. exact NA1.
      * exact DR2. * exact MW2. * exact HPc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G5 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden : Z) :
  let LBc := (B0, 64) :: (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 19) = Z_to_bv 64 (Z.of_nat nR) ->
  getr R (reg 20) = Z_to_bv 64 (sp - 120) -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 26) = Z_to_bv 64 0 -> getr R (reg 27) = Z_to_bv 64 rr -> (1 <= nR)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> B0 <> B1 -> blocks_apart B1 64 LB -> crc = debit L (debit L cr 64) 64 ->
  div_saves M sp R0 -> locals_N M sp B0 B1 fd0 fn0 fnum fden -> Z.testbit fnum 1 = false -> L5.u64_at RSEGS M (sp - 120) MWORD ->
  L5.u64_at RSEGS M (sp - 264) (X + 16) -> L5.u64_at RSEGS M (sp - 256) 0 ->
  L5.big_at RSEGS M (sp - 168) (L5.BO fnum nR (L5.BDyn 8 B1)) -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DS.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22100 M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H18 H19 H20 H21 H26 H27 HnR MBV HH NE01 BA1 CRC DS LOC FN1 C120 C264 C256 OBn LAn OBq DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hn: (nR <= 6)%nat). { pose proof nR_le. unfold lenX in *. clear - H LENX. lia. }
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof (LBdef _ _ _ _ HH B1 64 ltac:(right; left; reflexivity)) as (DB1 & (B1lo & B1img) & B1hi & _).
  pose proof OBq as (U0 & _ & U8 & Ub0 & U16 & U24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in U0, U8, Ub0, U16, U24.
  assert (WFR: L5.writable RSEGS M (sp - 304) 304).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d5g5d_conc fx R M (Vd 0 0 0 0 0 (X + 16) fbX (Z.of_nat nR - 1) 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H9 ltac:(flia) A16 WFR C264 ltac:(flia) AX8 ltac:(left; flia) U0 ltac:(flia)
              ltac:(replace (Z.of_nat nR - 1) with (Z.of_nat (nR - 1)%nat) by lia; exact U8) Ub0 ltac:(flia) U24)
    as (fx1 & R1 & M1 & MG & FR & FRZ & EX). clear P.
  pose proof (mem_eq M M1 FR) as EM1. subst M1.
  (* [comment removed for export] *)
  assert (JOIN: exists fx2 R2 M2, msteps RSEGS (st fx R 0x22100 M) (st fx2 R2 0x2212c M2)
            /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (qX <= i < qX + 8 * (Z.of_nat nR - 1)) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ mem_grows M M2 /\ getr R2 (reg 24) = Z_to_bv 64 qX /\ getr R2 (reg 25) = Z_to_bv 64 (Z.of_nat nR - 1)).
  { destruct EX as [(MS & KS & A1 & A10 & A11 & A12 & A24 & A25 & NQ)|(MS & KS & A10 & A24 & A25 & NQ)].
    - destruct (memset_run fx1 R1 M qX (8 * (Z.of_nat nR - 1)) 0x2212c A10 A11 A12 A1 ltac:(split; [flia | reflexivity]) ltac:(flia) ltac:(flia) ltac:(flia)
                  ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact DQ | flia | flia] | flia | flia]))
        as (R3 & MS3 & K3 & R3_10).
      eexists fx1, R3, _. split. { eapply msteps_trans. exact MS. exact MS3. }
      split. { intros x Hx. rewrite (K3 x) by (revert x Hx; apply L5K.incl_b; vm_compute; reflexivity). apply KS. revert x Hx; apply L5K.incl_b; vm_compute; reflexivity. }
      split. { intros i Hi Ni. apply AX2S.wbytes_out; rewrite ?BG.unsigned_lit, ?repeat_length, ?Z2Nat.id by flia; flia. }
      split. apply wbytes_grows. split. rewrite (K3 24%nat) by inl. exact A24. rewrite (K3 25%nat) by inl. exact A25.
    - exists fx1, R1, M. split. exact MS. split. { intros x Hx. apply KS. revert x Hx; apply L5K.incl_b; vm_compute; reflexivity. }
      split. { intros; reflexivity. } split. intros a Ha; exact Ha. split. exact A24. exact A25. }
  clear EX. destruct JOIN as (fx2 & R2 & M2 & MS2 & K2 & FR2 & MG2 & A24 & A25).
  assert (KQ: forall i, 0 <= i < 2 ^ 64 -> ~ (qX <= i < qX + 64) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Ni. apply FR2. exact Hi. flia. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
  apply (stage_G6 fx2 R2 M2 model crc B0 B1 fd0 fn0 fnum fden).
  all: try (rewrite (K2 _) by inl; assumption).
  - exact A24. - exact A25. - exact HnR. - exact MBV.
  - eapply (L5C.hi_heap_client L SCFG HI LBc crc M M2). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG2.
    intros a Ha. destruct (Z_le_gt_dec qX a) as [C1|C1]; [destruct (Z_lt_le_dec a (qX + 64)) as [C2|C2]|].
    { right; right. exists (qX, 64). split. right; right; exact INQ. cbn; flia. } all: left; apply KQ; flia.
  - exact NE01. - exact CRC.
  - eapply div_saves_kept. 4: exact DS. intros i Hi. apply KQ; flia. flia. flia.
  - eapply locals_N_kept. 4: exact LOC. intros i Hi. apply KQ; flia. flia. flia.
  - exact FN1.
  - eapply u64_at_agree1. 4: exact C120. intros i Hi. apply KQ; flia. flia. flia.
  - eapply u64_at_agree1. 4: exact C264. intros i Hi. apply KQ; flia. flia. flia.
  - eapply u64_at_agree1. 4: exact C256. intros i Hi. apply KQ; flia. flia. flia.
  - eapply big_at_agree1. 4: exact OBn. intros i Hi. apply KQ; flia. flia. flia.
  - pose proof wX_len as WL. unfold lenX in WL. pose proof (BA1 (qX, 64) INQ) as AP. cbn in AP.
    eapply L5C.limbs_at_agree. 4: exact LAn. 2: flia. 2: flia. intros i Hi. apply KQ. flia. generalize AP Hi WL LENX; clear; intros; lia.
  - eapply big_at_agree1. 4: exact OBq. intros i Hi. apply KQ; flia. flia. flia.
  - eapply L5.defined_grows. exact MG2. exact DQ.
  - eapply L5.defined_grows. exact MG2. exact DX.
  - eapply big_at_agree1. 4: exact ZRc. intros i Hi. apply KQ; flia. flia. flia.
  - eapply L5.defined_grows. exact MG2. exact DR.
  - destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KQ; flia. flia. flia.
  - eapply (L5HP.hpres_trans L LB LB sp DIV_SCR WN M0 M M2 sp DIV_SCR WN). exact HP.
    + eapply (L5HP.hpres_piece L LB sp DIV_SCR WN M M2 (fun a => qX <= a < qX + 64)).
      * intros a Ha Hn'. apply KQ. exact Ha. exact Hn'.
      * intros a KA C. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. apply (L5HP.outside_in _ _ qX 64 OW). cbn. right; left; reflexivity. exact C.
      * rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG2. exact SCR0.
      * exact MG2.
    + intros a KA; exact KA. + intros b Hb; exact Hb. + fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP).
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKD.
