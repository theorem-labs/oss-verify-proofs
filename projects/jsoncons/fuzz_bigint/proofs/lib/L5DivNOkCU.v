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
     L5DivSpecsU L5DivPartsU L5DivNPU L5DivNOkAU L5DivNOkBU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKCU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVNOKAU. Import L5DIVNOKBU.

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
Let stage_L := @L5DIVNOKAU.stage_L _ L HI LY HIok DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 KONT KONT3.
Let kept_above := @L5DIVNOKBU.kept_above _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let kept_inblock := @L5DIVNOKBU.kept_inblock _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let cdef_above := @L5DIVNOKBU.cdef_above _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let cdef_inblock := @L5DIVNOKBU.cdef_inblock _ L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
Let stage_GROW := @L5DIVNOKBU.stage_GROW _ L HI LY HIok KPOS BPOS RESIZE DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX OLX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 CR KONT KONT3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G7 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden frem : Z) (rst : L5.bstore) (wr : list Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 rr -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 0 ->
  getr R (reg 24) = Z_to_bv 64 (Z.of_nat nR) -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 0 -> (1 <= nR)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = rem_blocks rst ++ (B0, 64) :: (B1, 64) :: LB -> B0 <> B1 ->
  match rst with L5.BInl _ _ => crc = debit L (debit L cr 64) 64 | L5.BDyn _ _ => credit_after L cr DIVN_K DIVN_BYTES crc end ->
  div_saves M sp R0 -> locals_N M sp B0 B1 fd0 fn0 fnum fden -> L5.u64_at RSEGS M (sp - 120) MWORD ->
  L5.u64_at RSEGS M (sp - 152) (sp - 120) -> L5.u64_at RSEGS M (sp - 144) 1 -> L5.u64_at RSEGS M (sp - 232) qX -> L5.u64_at RSEGS M (sp - 224) (Z.of_nat nR - 1) ->
  L5.big_at RSEGS M X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5.big_at RSEGS M rr (L5.BO frem nR rst) -> L5C.obj_limbs RSEGS M (L5.BO frem nR rst) wr -> rem_store L LB M B0 B1 rst -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22854 M model) K.
Proof.
  intros H2 H9 H3 H4 H8 H18 H21 H23 H24 H25 H26 HnR MBV HH ELB NE01 CRC DS LOC C120 VD VS VQ VQS OBq DQ DX OBr OLr RS DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hn: (nR <= 6)%nat). { pose proof nR_le. unfold lenX in *. clear - H LENX. lia. }
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  assert (CRA: credit_after L cr DIVN_K DIVN_BYTES crc). { destruct rst. rewrite CRC. apply credit_after2. exact KPOS. exact BPOS. exact CRC. }
  pose proof OBr as (W0 & Wf & W8 & WS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in W0, Wf, W8, WS.
  pose proof OLr as (WL & WR & WA). cbn [L5.bo_len L5.bo_st] in WL, WA.
  assert (WFR: L5.writable RSEGS M (sp - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  (* [comment removed for export] *)
  set (remd := L5.bo_data rr (L5.BO frem nR rst)).
  assert (TOP: exists w, 0 <= w < 2 ^ 64 /\ L5.u64_at RSEGS M (remd + 8 * (Z.of_nat nR - 1)) w).
  { exists (nth (nR - 1) wr 0). split. { apply (proj1 (List.Forall_nth _ _) WR). lia. }
    assert (LA: L5.limbs_at RSEGS M remd wr).
    { subst remd. destruct rst as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st]. 2: exact WA.
      subst wr. destruct WS as (_ & U0 & U1 & Hle & _). intros i Hi. rewrite length_firstn in Hi. cbn [length] in Hi.
      destruct i as [|[|i]]; cbn [nth firstn Z.of_nat]. { destruct nR as [|n1]. lia. cbn. exactA U0. }
      { destruct nR as [|[|n2]]. lia. lia. cbn. exactA U1. } lia. }
    replace (remd + 8 * (Z.of_nat nR - 1)) with (remd + 8 * Z.of_nat (nR - 1)%nat) by lia. apply LA. lia. }
  destruct TOP as (w & Rw & Uw).
  unfold cfg.
  (* [comment removed for export] *)
  assert (STEP: exists fx1 R1 M1 (pc1 : Z), mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 336 <= i < sp - 336 + 24) -> ~ (sp - 304 <= i < sp - 304 + 16) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (st fx R 0x22854 M) (st fx1 R1 pc1 M1)
      /\ (forall x, In x [2; 3; 4; 8; 9; 18; 21; 24]%nat -> getr R1 (reg x) = getr R (reg x))
      /\ getr R1 (reg 22) = Z_to_bv 64 0 /\ getr R1 (reg 23) = Z_to_bv 64 (Z.of_nat nR - 1)
      /\ L5.u64_at RSEGS M1 (sp - 296) (Z.of_nat nR) /\ L5.u64_at RSEGS M1 (sp - 304) remd
      /\ L5.u64_at RSEGS M1 (sp - 320) 0 /\ L5.u64_at RSEGS M1 (sp - 328) 0 /\ L5.u64_at RSEGS M1 (sp - 336) 0
      /\ ((w < MWORD /\ pc1 = PRE) \/ (MWORD <= w /\ pc1 = 0x228b0))).
  { destruct rst as [v0 v1|c q].
    - (* [comment removed for export] *)
      destruct WS as (Tb & _ & _ & Hle & _). subst remd. cbn [L5.bo_data L5.bo_st] in Uw |- *.
      destruct (Z_lt_le_dec w MWORD) as [LT|GE].
      + pose proof (d5ug7ni0_conc fx R M (Vd 0 0 0 0 0 0 0 0 frem 0 w 0 0 0)) as P. cbn [Vd VdG] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold MWORD; flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WFR C120 VD VS ltac:(unfold MWORD; flia) ltac:(flia) ARR ltac:(left; flia) W0 ltac:(flia) W8 Tb
                    ltac:(exactA Uw) ltac:(flia) LT ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia))
          as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & VRS1 & VRD1 & C320 & C328 & C336)). clear P.
        exists fx1, R1, M1, PRE. split. exact MG. split. exact FRZ. split. exact MS.
        split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
        repeat (split; [assumption|]). left. split. exact LT. reflexivity.
      + pose proof (d5ug7ni1_conc fx R M (Vd 0 0 0 0 0 0 0 0 frem 0 w 0 0 0)) as P. cbn [Vd VdG] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold MWORD; flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WFR C120 VD VS ltac:(unfold MWORD; flia) ltac:(flia) ARR ltac:(left; flia) W0 ltac:(flia) W8 Tb
                    ltac:(exactA Uw) ltac:(flia) ltac:(unfold MWORD in *; flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia))
          as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & VRS1 & VRD1 & C320 & C328 & C336)). clear P.
        exists fx1, R1, M1, 0x228b0. split. exact MG. split. exact FRZ. split. exact MS.
        split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
        repeat (split; [assumption|]). right. split. exact GE. reflexivity.
    - (* [comment removed for export] *)
      pose proof WS as (Tb & _ & Uq & _ & Hcap & Aq & Qlo & Qhi & _). subst remd. cbn [L5.bo_data L5.bo_st] in Uw |- *.
      unfold rem_store in RS. pose proof RS as (Ec & (Bq0 & Bq1 & Bq2 & Bq3 & Bq4) & _). subst c.
      destruct (Z_lt_le_dec w MWORD) as [LT|GE].
      + pose proof (d5ug7nd0_conc fx R M (Vd 0 0 0 0 0 0 0 0 frem q w 0 0 0)) as P. cbn [Vd VdG] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold MWORD; flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WFR C120 VD VS ltac:(unfold MWORD; flia) ltac:(flia) ARR ltac:(left; flia) W0 ltac:(flia) W8 Tb Uq
                    ltac:(flia) Aq ltac:(right; flia) ltac:(exactA Uw) ltac:(flia) LT ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia))
          as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & VRS1 & VRD1 & C320 & C328 & C336)). clear P.
        exists fx1, R1, M1, PRE. split. exact MG. split. exact FRZ. split. exact MS.
        split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
        repeat (split; [assumption|]). left. split. exact LT. reflexivity.
      + pose proof (d5ug7nd1_conc fx R M (Vd 0 0 0 0 0 0 0 0 frem q w 0 0 0)) as P. cbn [Vd VdG] in P.
        destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold MWORD; flia)
                    H2 H8 H21 H23 H24 H25 H26 ltac:(flia) A16 WFR C120 VD VS ltac:(unfold MWORD; flia) ltac:(flia) ARR ltac:(left; flia) W0 ltac:(flia) W8 Tb Uq
                    ltac:(flia) Aq ltac:(right; flia) ltac:(exactA Uw) ltac:(flia) ltac:(unfold MWORD in *; flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia))
          as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & A14 & A19 & A22 & A23 & VRS1 & VRD1 & C320 & C328 & C336)). clear P.
        exists fx1, R1, M1, 0x228b0. split. exact MG. split. exact FRZ. split. exact MS.
        split. { intros x Hx. apply KS. revert x Hx. apply L5K.incl_b. vm_compute. reflexivity. }
        repeat (split; [assumption|]). right. split. exact GE. reflexivity. }
  destruct STEP as (fx1 & R1 & M1 & pc1 & MG1 & FR1 & MS1 & K1 & A22 & A23 & VRS1 & VRD1 & C320 & C328 & C336 & BR).
  (* [comment removed for export] *)
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 336 <= i < sp - 288) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Ni. apply FR1. exact Hi. flia. flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_le_gt_dec (sp - 336) a) as [C1|C1]; [destruct (Z_lt_le_dec a (sp - 288)) as [C2|C2]|].
    right; left; flia. all: left; apply KFR; flia. }
  assert (DS1: div_saves M1 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi. apply KFR; flia. flia. flia. }
  assert (LOC1: locals_N M1 sp B0 B1 fd0 fn0 fnum fden). { eapply locals_N_kept. 4: exact LOC. intros i Hi. apply KFR; flia. flia. flia. }
  assert (MK1: marks_N M1 sp rr). { split. exact C320. split. exact C328. exact C336. }
  assert (C120': L5.u64_at RSEGS M1 (sp - 120) MWORD). { eapply u64_at_agree1. 4: exact C120. intros i Hi. apply KFR; flia. flia. flia. }
  assert (VD': L5.u64_at RSEGS M1 (sp - 152) (sp - 120)). { eapply u64_at_agree1. 4: exact VD. intros i Hi. apply KFR; flia. flia. flia. }
  assert (VS': L5.u64_at RSEGS M1 (sp - 144) 1). { eapply u64_at_agree1. 4: exact VS. intros i Hi. apply KFR; flia. flia. flia. }
  assert (VQ': L5.u64_at RSEGS M1 (sp - 232) qX). { eapply u64_at_agree1. 4: exact VQ. intros i Hi. apply KFR; flia. flia. flia. }
  assert (VQS': L5.u64_at RSEGS M1 (sp - 224) (Z.of_nat nR - 1)). { eapply u64_at_agree1. 4: exact VQS. intros i Hi. apply KFR; flia. flia. flia. }
  assert (OBq1: L5.big_at RSEGS M1 X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX))). { eapply big_at_agree1. 4: exact OBq. intros i Hi. apply KFR; flia. flia. flia. }
  assert (DQ1: L5.defined M1 qX 64). { eapply L5.defined_grows. exact MG1. exact DQ. }
  assert (DX1: L5.defined M1 X 32). { eapply L5.defined_grows. exact MG1. exact DX. }
  assert (DR1: L5.defined M1 rr 32). { eapply L5.defined_grows. exact MG1. exact DR. }
  assert (OBr1: L5.big_at RSEGS M1 rr (L5.BO frem nR rst)). { eapply big_at_agree1. 4: exact OBr. intros i Hi. apply KFR; flia. flia. flia. }
  assert (OLr1: L5C.obj_limbs RSEGS M1 (L5.BO frem nR rst) wr).
  { split. exact WL. split. exact WR. destruct rst as [v0 v1|c q]. exact WA. cbn [L5.bo_st]. eapply L5C.limbs_at_agree. 4: exact WA.
    2: flia. rewrite WL. unfold rem_store in RS. destruct RS as (_ & (_ & _ & _ & _ & Bq4) & _).
    intros i Hi. apply KFR; flia. rewrite WL. unfold rem_store in RS. destruct RS as (_ & (_ & _ & _ & _ & Bq4) & _). flia. }
  assert (RS1: rem_store L LB M1 B0 B1 rst).
  { destruct rst as [v0 v1|c q]. exact I. unfold rem_store in RS |- *. destruct RS as (RSa & RSb & RSc & RSd & RSe & RSf).
    refine (conj RSa (conj RSb (conj RSc (conj _ (conj RSe RSf))))). eapply L5.defined_grows. exact MG1. exact RSd. }
  assert (MW1: mword_obj M1 dv fdv). { destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KFR; flia. flia. flia. }
  assert (HP1: L5C.hpres L LB sp DIV_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIV_SCR WN M0 M M1 sp DIV_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIV_SCR WN M M1 (fun a => sp - 336 <= a < sp - 288)).
      + intros a Ha Hn'. apply KFR. exact Ha. exact Hn'.
      + intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
      + rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
      + exact MG1.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  destruct BR as [[LT ->]|[GE ->]].
  - (* [comment removed for export] *)
    apply (stage_L fx1 R1 M1 model LBc crc (nR - 1) B0 B1 fd0 fn0 fnum fden frem remd nR rst).
    all: try (rewrite (K1 _) by inl; assumption).
    + exact VRD1. + exact VD'. + exact A22. + exact VS'. + exact VQ'. + rewrite A23; f_equal; lia. + lia. + exact MBV. + exact HH1. + exact ELB. + exact NE01. + exact CRA.
    + exact DS1. + exact MK1. + exact LOC1. + exact C120'. + exact OBq1. + exact DQ1. + exact DX1. + exact OBr1. + exact RS1. + exact DR1.
    + reflexivity. + lia. + exact MW1. + exact HP1.
  - (* [comment removed for export] *)
    apply (stage_GROW fx1 R1 M1 model LBc crc B0 B1 fd0 fn0 fnum fden frem rst wr).
    all: try (rewrite (K1 _) by inl; assumption).
    + exact A22. + exact HnR. + exact MBV. + exact HH1. + exact ELB. + exact NE01. + exact CRC.
    + exact DS1. + exact MK1. + exact LOC1. + exact C120'. + exact VD'. + exact VS'. + exact VQS'. + exact VRS1. + exact OBq1. + exact DQ1. + exact DX1. + exact OBr1. + exact OLr1. + exact RS1. + exact DR1.
    + exact MW1. + exact HP1.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKCU.
