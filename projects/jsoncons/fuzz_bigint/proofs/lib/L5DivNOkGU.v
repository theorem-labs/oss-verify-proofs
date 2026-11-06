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
     L5Core L5CoreSpecsU L5CoreKitU L5Words L5WordsB L5ReduceU L5ReduceGU L5DDqU L5SubMulU L5ShlU L5MulMU L5Hp L5NormU L5NormOkAU L5NormOkU
     L5DivSpecsU L5DivPartsU L5DivNPU L5DivNOkAU L5DivNOkBU L5DivNOkCU L5DivNOkDU L5DivNOkEU L5DivNOkFU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKGU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVNOKAU. Import L5DIVNOKBU. Import L5DIVNOKCU. Import L5DIVNOKDU. Import L5DIVNOKEU. Import L5DIVNOKFU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
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
Local Ltac uSCR := unfold DIV_SCR, L5NORMU.NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR,
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
Let norm_ok := L5NORMOKU.norm_ok L HI LY HIok RESIZE.

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
Let spd : Z := sp - 352.
Let WN : list L5.range := [(X, 32); (qX, 64); (rr, 32)].
Let Vd := VdG sp X qX rr dv fbX (Z.of_nat lenX) (Z.of_nat nR) R0.

(* [comment removed for export] *)
Let stk0 := @L5DIVNOKAU.stk0 L M0 sp STK.
Let IMG := @L5DIVNOKAU.IMG L LY.
Let IMGLO := @L5DIVNOKAU.IMGLO L LY.
Let ERRNO := @L5DIVNOKAU.ERRNO L LY R0 X qX rr dv sp bX wX LENX.
Let ERRNOV := @L5DIVNOKAU.ERRNOV L LY.
Let SPTOP := @L5DIVNOKAU.SPTOP L M0 sp STK.
Let SPW := @L5DIVNOKAU.SPW L R0 M0 X qX rr dv sp bX wX STK LENX AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let DIV_SCR_val := L5DIVNOKAU.DIV_SCR_val.
Let LBhi := @L5DIVNOKAU.LBhi _ L HI HIok.
Let LBdef := @L5DIVNOKAU.LBdef _ L HI HIok.
Let QX := @L5DIVNOKAU.QX _ L HI LY HIok M0 model0 LB cr X qX bX HH0 OBX STX INQ.
Let wX_len := @L5DIVNOKAU.wX_len M0 bX wX OLX.
Let wX_ok := @L5DIVNOKAU.wX_ok M0 bX wX OLX.
Let nR_le := @L5DIVNOKAU.nR_le M0 bX wX OLX.
Let fbX_rng := @L5DIVNOKAU.fbX_rng M0 X bX OBX.
Let UR1 := @L5DIVNOKAU.UR1 R0 X qX rr dv sp r bX wX G1 RA LENX.
Let fbX_bit0 := @L5DIVNOKAU.fbX_bit0 M0 X qX bX OBX STX.
Let kept_above := @L5DIVNOKBU.kept_above _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let kept_inblock := @L5DIVNOKBU.kept_inblock _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let cdef_above := @L5DIVNOKBU.cdef_above _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let cdef_inblock := @L5DIVNOKBU.cdef_inblock _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let stage_G3 := @L5DIVNOKFU.stage_G3 _ L HI LY HIok KPOS BPOS ASSIGN RESIZE HUGE DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX OLX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 CR KONT KONT3.
Local Ltac slia :=
  match goal with
  | A : 140735332483072 + 8976 <= ?s, B : ?s <= 2 ^ 47, C : ?s <= hl_sptop _ |- _ => generalize A B C SX SDV SRR HX HDV HRR SPTOP; clear; intros; lia
  end.
Local Ltac kcw K H := first [ eapply u64_at_agree1 | eapply u8_at_agree1 | eapply big_at_agree1 ];
  [ intros i Hi; apply K; generalize Hi SX; unfold spd; slia | slia | slia | exactA H ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G2 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B0 B1 fn0 fnum fden fd3 : Z) :
  let LBc := (B0, 64) :: (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 rr -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 19) = Z_to_bv 64 fd3 -> getr R (reg 20) = Z_to_bv 64 fbX ->
  getr R (reg 22) = Z_to_bv 64 (sp - 120) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 25) = Z_to_bv 64 0 ->
  getr R (reg 26) = Z_to_bv 64 0 -> getr R (reg 27) = getr R0 (reg 27) ->
  0 <= fd3 < 256 -> Z.testbit fd3 0 = false -> Z.testbit fd3 1 = false ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> B0 <> B1 ->
  block_range L B1 64 /\ blocks_apart B1 64 LB -> block_range L B0 64 /\ blocks_apart B0 64 ((B1, 64) :: LB) -> crc = debit L (debit L cr 64) 64 ->
  div_saves M sp R0 ->
  L5.u8_at RSEGS M (sp - 216) fn0 -> 0 <= fn0 < 256 -> Z.testbit fn0 0 = true ->
  L5.u64_at RSEGS M (sp - 208) (Z.of_nat lenX) -> L5.u64_at RSEGS M (sp - 200) 8 -> L5.u64_at RSEGS M (sp - 192) B0 ->
  L5.big_at RSEGS M (sp - 184) (L5.BO fnum lenX (L5.BDyn 8 B1)) -> Z.testbit fnum 1 = false -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 1 (L5.BInl MWORD 0)) -> Z.testbit fden 1 = false ->
  L5.u64_at RSEGS M (sp - 232) qX -> L5.u64_at RSEGS M (sp - 224) (Z.of_nat lenX) -> L5.u64_at RSEGS M (sp - 248) qX -> L5.u64_at RSEGS M (sp - 240) (Z.of_nat lenX) ->
  L5.big_at RSEGS M X bX -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DSU.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x227a8 M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H18 H19 H20 H22 H23 H25 H26 H27 Fd3r Fd3b Fd3b1 MBV HH NE01 [BR1 BA1] [BR0 BA0] CRC DS
         Fn0 Fn0r Fn0b F192 F184 F176 OBn Fnb1 LAn OBd Fdb1 VQ VQS VT VTS OBXc DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof wX_len as WL. pose proof wX_ok as WO. unfold lenX in WL.
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof BR1 as (B1a & B1b & B1c & B1d & B1e).
  pose proof OBd as (D0 & Dr & D8 & Db0 & D16 & D24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in D0, Dr, D8, Db0, D16, D24.
  unfold cfg.
  pose proof (d5ug2_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) H2 ltac:(flia) A16) as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12)). clear P.
  pose proof (mem_eq M M1 FR) as EM1. subst M1.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  destruct (defined_byte M (sp - 280) ltac:(eapply L5.defined_sub; [exact SCR0 | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo & FBO & UFBO).
  assert (OLd: L5C.obj_limbs RSEGS M (L5.BO fden 1 (L5.BInl MWORD 0)) [MWORD]). { split. reflexivity. split. repeat constructor; unfold MWORD; lia. reflexivity. }
  eapply (COPYA fx1 R1 M model K LBc crc (sp - 280) (sp - 136) spd 0x227b8 fbo (L5.BO fden 1 (L5.BInl MWORD 0)) [MWORD] HH MOK HK0 A10 A11).
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite Db0. intros F; discriminate F.
  - exact A1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact UFBO. - exact FBO.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia.
  - exact OBd. - exact OLd.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - cbn [L5.bo_st]. intros cap q E. discriminate E.
  - left. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & GPOST). destruct g as [|A cap].
    2:{ exfalso. destruct GPOST as (F & _). unfold L5.bo_dyn in F. cbn [L5.bo_fb] in F. rewrite Db0 in F. discriminate F. }
    destruct GPOST as (_ & -> & -> & OB2 & FB2 & MG2). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB2.
    assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 280 <= a < sp - 248) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1. apply FB2. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by exact Ha. generalize N1; clear; intros; lia. }
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
    assert (REGS: forall i v, In i cs_all -> In i KS_d5ug2 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    set (fd0 := copy_fb fbo fden false) in OB2.
    assert (FD0: 0 <= fd0 < 256 /\ Z.testbit fd0 0 = false).
    { pose proof OB2 as (_ & R2' & _ & T0 & _). split. exact R2'. exact T0. }
    pose proof OB2 as (E232 & _ & E224 & _ & E216 & E208 & _).
    apply (stage_G3 fx2 R2 M2 model2 crc B0 B1 fd0 fn0 fnum fden fd3).
    all: try (eapply REGS; [inl | inl | assumption]).
    + generalize Fd3r; clear; lia. + exact Fd3b. + exact Fd3b1.
    + exact MBV02. + exact HH2. + exact NE01. + split; assumption. + split; assumption. + exact CRC.
    + eapply div_saves_kept. 4: exact DS. intros i Hi. apply KA; generalize Hi; slia. flia. flia.
    + exact E232. + exact (proj1 FD0). + exact (proj2 FD0). + exactA E224. + exactA E216. + exactA E208.
    + kcw KA Fn0. + exact Fn0r. + exact Fn0b. + kcw KA F192. + kcw KA F184. + kcw KA F176.
    + kcw KA OBn. + exact Fnb1.
    + eapply L5C.limbs_at_agree. 4: exact LAn. 2: flia. 2: flia. intros i Hi. apply KA. flia. generalize Hi B1e SLO' WL LENX; clear; intros; lia.
    + kcw KA OBd. + exact Fdb1. + kcw KA VQ. + kcw KA VQS. + kcw KA VT. + kcw KA VTS.
    + kcw KA OBXc.
    + eapply L5.defined_grows. exact MG2. exact DQ.
    + eapply L5.defined_grows. exact MG2. exact DX.
    + kcw KA ZRc.
    + eapply L5.defined_grows. exact MG2. exact DR.
    + destruct MWc as [OBv SGv]. split. 2: exact SGv. kcw KA OBv.
    + eapply (L5HP.hpres_trans L LB LB sp DIV_SCR [] M0 M M2 sp DIV_SCR []). exact HP.
      * eapply (L5HP.hpres_piece L LB sp DIV_SCR [] M M2 (fun a => sp - 280 <= a < sp - 248)).
        -- intros a Ha Hn'. apply KA. exact Ha. exact Hn'.
        -- intros a KA' C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
        -- rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG2. exact SCR0.
        -- exact MG2.
      * intros a KA'; exact KA'. * intros b Hb; exact Hb. * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G1 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B1 fnum fden fd3 : Z) :
  let LBc := (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 rr -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 19) = Z_to_bv 64 fd3 -> getr R (reg 20) = Z_to_bv 64 fbX ->
  getr R (reg 22) = Z_to_bv 64 (sp - 120) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 25) = Z_to_bv 64 0 ->
  getr R (reg 26) = Z_to_bv 64 0 -> getr R (reg 27) = getr R0 (reg 27) ->
  0 <= fd3 < 256 -> Z.testbit fd3 0 = false -> Z.testbit fd3 1 = false ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  block_range L B1 64 /\ blocks_apart B1 64 LB -> crc = debit L cr 64 ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 184) (L5.BO fnum lenX (L5.BDyn 8 B1)) -> Z.testbit fnum 1 = false -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 1 (L5.BInl MWORD 0)) -> Z.testbit fden 1 = false ->
  L5.u64_at RSEGS M (sp - 232) qX -> L5.u64_at RSEGS M (sp - 224) (Z.of_nat lenX) -> L5.u64_at RSEGS M (sp - 248) qX -> L5.u64_at RSEGS M (sp - 240) (Z.of_nat lenX) ->
  L5.big_at RSEGS M X bX -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DSU.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22798 M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H18 H19 H20 H22 H23 H25 H26 H27 Fd3r Fd3b Fd3b1 MBV HH [BR1 BA1] CRC DS OBn Fnb1 LAn OBd Fdb1 VQ VQS VT VTS OBXc DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof wX_len as WL. pose proof wX_ok as WO. unfold lenX in WL.
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof (credit_chain L cr KPOS BPOS CR) as (_ & CR2 & _).
  pose proof BR1 as (B1a & B1b & B1c & B1d & B1e).
  pose proof OBn as (N0 & Nr & N8 & Nb0 & N16 & N24 & Nlen & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in N0, Nr, N8, Nb0, N16, N24, Nlen.
  unfold cfg.
  pose proof (d5ug1_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) H2 ltac:(flia) A16) as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12)). clear P.
  pose proof (mem_eq M M1 FR) as EM1. subst M1.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  destruct (defined_byte M (sp - 216) ltac:(eapply L5.defined_sub; [exact SCR0 | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo & FBO & UFBO).
  assert (OLn: L5C.obj_limbs RSEGS M (L5.BO fnum lenX (L5.BDyn 8 B1)) wX). { split. cbn [L5.bo_len]. exact WL. split. exact WO. exact LAn. }
  eapply (COPYA fx1 R1 M model K LBc crc (sp - 216) (sp - 184) spd 0x227a8 fbo (L5.BO fnum lenX (L5.BDyn 8 B1)) wX HH MOK HK0 A10 A11).
  - cbn [L5.bo_cap L5.bo_st]. intros _. split. lia. rewrite CRC. exact CR2.
  - exact A1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact UFBO. - exact FBO.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia.
  - exact OBn. - exact OLn.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - flia.
  - cbn [L5.bo_st]. intros cap q E. injection E. intros <- <-. left. reflexivity.
  - left. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & GPOST). destruct g as [|B0 cap].
    { exfalso. destruct GPOST as (F & _). unfold L5.bo_dyn in F. cbn [L5.bo_fb] in F. rewrite Nb0 in F. discriminate F. }
    destruct GPOST as (_ & Hcap & -> & -> & FB0 & OB2 & OL2 & HP2). cbn [L5.bo_cap L5.bo_st L5.bo_fb L5.bo_len] in Hcap, OB2, OL2. subst cap.
    pose proof FB0 as (BR0 & BA0 & DF0). pose proof BR0 as (B0a & B0b & B0c & B0d & B0e).
    assert (NE01: B0 <> B1). { pose proof (BA0 (B1, 64) ltac:(left; reflexivity)) as Hb. cbn in Hb. lia. }
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (sp - 216 <= a < sp - 184) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1. apply (kept_above M M2 LBc COPY_SCR _ a HP2). uSCR; clear; lia. exact Ha. apply outside1. generalize N1; clear; intros; lia. }
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
    assert (REGS: forall i v, In i cs_all -> In i KS_d5ug1 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    set (fn0 := copy_fb fbo fnum true) in OB2, OL2.
    pose proof OB2 as (E200 & Rn0 & E192 & Tn0 & E184 & E176 & _).
    apply (stage_G2 fx2 R2 M2 model2 (debit L crc (8 * 8)) B0 B1 fn0 fnum fden fd3).
    all: try (eapply REGS; [inl | inl | assumption]).
    + generalize Fd3r; clear; lia. + exact Fd3b. + exact Fd3b1.
    + exact MBV02. + exact HH2. + exact NE01. + split; assumption. + split; assumption. + rewrite CRC. reflexivity.
    + eapply div_saves_kept. 4: exact DS. intros i Hi. apply KA; generalize Hi; unfold spd; slia. flia. flia.
    + exact E200. + exact Rn0. + exact Tn0. + exactA E192. + exactA E184. + exactA E176.
    + kcw KA OBn. + exact Fnb1.
    + eapply L5C.limbs_at_agree. 4: exact LAn. 2: flia. 2: flia. intros i Hi.
      apply (kept_inblock M M2 LBc crc _ COPY_SCR _ B1 64 i HH HP2). left; reflexivity. generalize Hi WL LENX; clear; intros; lia.
      apply outside1. generalize Hi B1e SLO' WL LENX; clear; intros; lia.
    + kcw KA OBd. + exact Fdb1. + kcw KA VQ. + kcw KA VQS. + kcw KA VT. + kcw KA VTS.
    + kcw KA OBXc.
    + eapply (cdef_inblock M M2 LBc crc _ COPY_SCR _ qX 64 qX 64 HH HP2). right; exact INQ. lia. lia. exact DQ.
    + eapply (cdef_above M M2 LBc COPY_SCR _ X 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DX.
    + kcw KA ZRc.
    + eapply (cdef_above M M2 LBc COPY_SCR _ rr 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DR.
    + destruct MWc as [OBv SGv]. split. 2: exact SGv. kcw KA OBv.
    + eapply (L5HP.hpres_trans L LB LBc sp DIV_SCR [] M0 M M2 spd COPY_SCR). exact HP. exact HP2.
      * intros a KA'. eapply L5HP.kept_mono. exact KA'. { intros b Hb. right; exact Hb. }
        unfold spd; fsclia. unfold spd; flia.
        intros _. apply outside1. pose proof (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) ltac:(fsclia) ltac:(rewrite IMG; flia)) as NS.
        generalize NS; clear; uSCR; intros; lia.
      * intros b Hb. right; exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKGU.
