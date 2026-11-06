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
     L5DivSpecsU L5DivPartsU L5DivNPU L5DivNOkAU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKBU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVNOKAU.

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
Let stage_Z := @L5DIVNOKAU.stage_Z _ L HI LY HIok DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 KONT KONT3.
Let stage_L := @L5DIVNOKAU.stage_L _ L HI LY HIok DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 KONT KONT3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_above M M' LBx scr W a :
  L5C.hpres L LBx spd scr W M M' -> 0 <= scr <= 8624 -> spd <= a < 2 ^ 64 -> L5.outside W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof using SCFG_P L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
  intros HP Hscr Ha OW. pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP'. pose proof ERRNO as ERRNO'.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply L5C.kept_stack. unfold spd; flia. flia. unfold spd in *; flia. exact ERRNO'. exact (proj1 SPTOP'). exact OW.
Qed.
Lemma kept_inblock M M' LBx crx VM scr W A n a :
  hi_heap HI LBx crx M VM -> L5C.hpres L LBx spd scr W M M' -> In (A, n) LBx -> A <= a < A + n -> L5.outside W a ->
  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof using SCFG_P L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
  intros HH HP Hin Ha OW. pose proof (LBdef _ _ _ _ HH A n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
  pose proof SPTOP as SPTOP'. pose proof ERRNOV as ERRNOV'.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV'. generalize Aimg; flia. exact OW.
Qed.
Lemma cdef_above M M' LBx scr W A n :
  L5C.hpres L LBx spd scr W M M' -> 0 <= scr <= 8624 -> spd <= A -> A + n <= 2 ^ 64 -> L5.defined M A n -> L5.defined M' A n.
Proof using SCFG_P L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
  intros HP Hscr HA HAn D i Hi. pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP'. pose proof ERRNO as ERRNO'.
  apply (L5C.hpres_cdef _ _ _ _ _ _ _ (A + i) HP). unfold spd in *; flia. { right. left. unfold spd in *. flia. } { unfold in_errno. unfold spd in *. flia. }
  apply D. exact Hi.
Qed.
Lemma cdef_inblock M M' LBx crx VM scr W A n A' n' :
  hi_heap HI LBx crx M VM -> L5C.hpres L LBx spd scr W M M' -> In (A, n) LBx -> A <= A' -> A' + n' <= A + n ->
  L5.defined M A' n' -> L5.defined M' A' n'.
Proof using SCFG_P L HI LY HIok R0 M0 model0 LB cr X qX rr dv sp bX wX HH0 STK OBX OLX STX LENX INQ AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
  intros HH HP Hin H1 H2 D i Hi. pose proof (LBdef _ _ _ _ HH A n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
  pose proof SPTOP as SPTOP'. pose proof ERRNOV as ERRNOV'.
  apply (L5C.hpres_cdef _ _ _ _ _ _ _ (A' + i) HP). flia. { left. exists (A, n). split. exact Hin. cbn. flia. }
  { unfold in_errno. rewrite ERRNOV'. generalize Aimg; flia. } apply D. exact Hi.
Qed.
(* [comment removed for export] *)
Lemma outside1 lo n a : ~ (lo <= a < lo + n) -> L5.outside [(lo, n)] a.
Proof. intros H rg [<-|[]]. unfold L5.in_rng. cbn. exact H. Qed.
Lemma outside2 lo n lo' n' a : ~ (lo <= a < lo + n) -> ~ (lo' <= a < lo' + n') -> L5.outside [(lo, n); (lo', n')] a.
Proof. intros H H' rg [<-|[<-|[]]]; unfold L5.in_rng; cbn; assumption. Qed.
Lemma outside3 lo n lo' n' lo'' n'' a : ~ (lo <= a < lo + n) -> ~ (lo' <= a < lo' + n') -> ~ (lo'' <= a < lo'' + n'') -> L5.outside [(lo, n); (lo', n'); (lo'', n'')] a.
Proof. intros H H' H'' rg [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn; assumption. Qed.

(* [comment removed for export] *)
Lemma locals_N_keptV M M' B0 B1 fd0 fn0 fnum fden :
  (forall i, sp - 280 <= i < sp - 104 -> ~ (sp - 248 <= i < sp - 216) -> ~ (sp - 152 <= i < sp - 136) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  locals_N M sp B0 B1 fd0 fn0 fnum fden -> locals_N M' sp B0 B1 fd0 fn0 fnum fden.
Proof using L R0 M0 X qX rr dv sp bX wX STK OBX OLX LENX AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3.
  intros HA (A1 & A2 & A3 & B1' & B2 & B3 & B4 & B5 & C1 & C2 & C3 & C4 & C5 & D1 & D2 & D3). pose proof SPW as (_ & SLO & SHI & _). unfold locals_N.
  repeat split;
    first [ assumption | (clear HA; lia)
          | eapply u8_at_agree1; [intros i Hi; apply HA; clear -Hi; lia | clear -SLO; lia | clear -SHI; lia | eassumption]
          | eapply u64_at_agree1; [intros i Hi; apply HA; clear -Hi; lia | clear -SLO; lia | clear -SHI; lia | eassumption] ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G10 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden frem remd : Z) (nrem : nat) (rst : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 22) = Z_to_bv 64 0 -> getr R (reg 24) = Z_to_bv 64 (Z.of_nat nR) -> (1 <= nR)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = rem_blocks rst ++ (B0, 64) :: (B1, 64) :: LB -> B0 <> B1 -> credit_after L cr DIVN_K DIVN_BYTES crc ->
  div_saves M sp R0 -> marks_N M sp rr -> locals_N M sp B0 B1 fd0 fn0 fnum fden -> L5.u64_at RSEGS M (sp - 120) MWORD ->
  L5.u64_at RSEGS M (sp - 304) remd -> L5.u64_at RSEGS M (sp - 152) (sp - 120) -> L5.u64_at RSEGS M (sp - 144) 1 ->
  L5.big_at RSEGS M X (L5.BO fbX nR (L5.BDyn 8 qX)) -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5.big_at RSEGS M rr (L5.BO frem nrem rst) -> rem_store L LB M B0 B1 rst -> L5.defined M rr 32 ->
  remd = L5.bo_data rr (L5.BO frem nrem rst) -> nrem = S nR ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x228f4 M model) K.
Proof.
  intros H2 H9 H3 H4 H18 H21 H22 H24 HnR MBV HH ELB NE01 CRA DS MK LOC C120 VR VD VS OBq DQ DX OBr RS DR Eremd Enrem MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hn: (nR <= 6)%nat). { pose proof nR_le. unfold lenX in *. clear - H LENX. lia. }
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof OBq as (U0 & _ & U8 & Ub0 & U16 & U24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in U0, U8, Ub0, U16, U24.
  assert (WFR: L5.writable RSEGS M (sp - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d5ug10_conc fx R M (Vd 0 0 0 0 0 0 fbX (Z.of_nat nR - 1) 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H9 H24 ltac:(flia) A16 WFR ltac:(flia) AX8 ltac:(left; flia)
              U0 ltac:(flia) Ub0 U24 ltac:(replace (Z.of_nat nR - 1 + 1) with (Z.of_nat nR) by (clear; lia); exact U8) ltac:(flia) ltac:(flia))
    as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A10 & A11 & A23 & VQS1 & VQ1)). clear P.
  assert (KA: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 232 <= a < sp - 232 + 16) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn'. apply FRZ. exact Ha. exact Hn'. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  apply (stage_L fx1 R1 M1 model LBc crc nR B0 B1 fd0 fn0 fnum fden frem remd nrem rst).
  - rewrite (KS 2%nat) by inl. exact H2.
  - rewrite (KS 9%nat) by inl. exact H9.
  - rewrite (KS 3%nat) by inl. exact H3.
  - rewrite (KS 4%nat) by inl. exact H4.
  - eapply u64_at_agree1. 4: exact VR. intros i Hi. apply KA; flia. flia. flia.
  - rewrite (KS 18%nat) by inl. exact H18.
  - eapply u64_at_agree1. 4: exact VD. intros i Hi. apply KA; flia. flia. flia.
  - rewrite (KS 21%nat) by inl. exact H21.
  - rewrite (KS 22%nat) by inl. exact H22.
  - eapply u64_at_agree1. 4: exact VS. intros i Hi. apply KA; flia. flia. flia.
  - exact VQ1.
  - exact A23.
  - exact Hn.
  - exact MBV.
  - eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 232)) as [Y|Y]. left; apply KA; flia.
    destruct (Z_lt_le_dec a (sp - 232 + 16)) as [Y'|Y']. right; left; flia. left; apply KA; flia.
  - exact ELB. - exact NE01. - exact CRA.
  - eapply div_saves_kept. 4: exact DS. intros i Hi. apply KA; flia. flia. flia.
  - eapply marks_N_kept. 4: exact MK. intros i Hi. apply KA; flia. flia. flia.
  - eapply locals_N_keptV. 2: exact LOC. intros i Hi N1 N2. apply KA; flia.
  - eapply u64_at_agree1. 4: exact C120. intros i Hi. apply KA; flia. flia. flia.
  - eapply big_at_agree1. 4: exact OBq. intros i Hi. apply KA; flia. flia. flia.
  - eapply L5.defined_grows. exact MG. exact DQ.
  - eapply L5.defined_grows. exact MG. exact DX.
  - eapply big_at_agree1. 4: exact OBr. intros i Hi. apply KA; flia. flia. flia.
  - destruct rst as [v0 v1|c q]. exact I. unfold rem_store in RS |- *. destruct RS as (RSa & RSb & RSc & RSd & RSe & RSf).
    refine (conj RSa (conj RSb (conj RSc (conj _ (conj RSe RSf))))). eapply L5.defined_grows. exact MG. exact RSd.
  - eapply L5.defined_grows. exact MG. exact DR.
  - exact Eremd. - exact Enrem.
  - destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KA; flia. flia. flia.
  - (* [comment removed for export] *)
    eapply (L5HP.hpres_trans L LB LB sp DIV_SCR WN M0 M M1 sp DIV_SCR WN). exact HP.
    + eapply (L5HP.hpres_piece L LB sp DIV_SCR WN M M1 (fun a => sp - 352 <= a < sp)).
      * intros a Ha Hn'. apply KA; flia.
      * intros a KA' C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR WN a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
      * rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG. exact SCR0.
      * exact MG.
    + intros a KA'; exact KA'.
    + intros b Hb; exact Hb.
    + fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G9 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden frem : Z) (rst : L5.bstore) (wq : list Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 rr -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 22) = Z_to_bv 64 0 ->
  getr R (reg 24) = Z_to_bv 64 (Z.of_nat nR) -> (1 <= nR)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = rem_blocks rst ++ (B0, 64) :: (B1, 64) :: LB -> B0 <> B1 -> credit_after L cr DIVN_K DIVN_BYTES crc ->
  div_saves M sp R0 -> marks_N M sp rr -> locals_N M sp B0 B1 fd0 fn0 fnum fden -> L5.u64_at RSEGS M (sp - 120) MWORD ->
  L5.u64_at RSEGS M (sp - 152) (sp - 120) -> L5.u64_at RSEGS M (sp - 144) 1 -> L5.u64_at RSEGS M (sp - 224) (Z.of_nat nR - 1) ->
  L5.big_at RSEGS M X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) -> L5C.obj_limbs RSEGS M (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) wq ->
  L5.defined M qX 64 -> L5.defined M X 32 ->
  L5.big_at RSEGS M rr (L5.BO frem (S nR) rst) -> rem_store L LB M B0 B1 rst -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x228c0 M model) K.
Proof.
  intros H2 H9 H3 H4 H8 H18 H21 H22 H24 HnR MBV HH ELB NE01 CRA DS MK LOC C120 VD VS VQS OBq OLq DQ DX OBr RS DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hn: (nR <= 6)%nat). { pose proof nR_le. unfold lenX in *. clear - H LENX. lia. }
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof OBr as (W0 & Wf & W8 & WS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in W0, Wf, W8, WS.
  assert (WFR: L5.writable RSEGS M (sp - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  assert (W8': L5.u64_at RSEGS M (rr + 8) (Z.of_nat nR + 1)). { replace (Z.of_nat nR + 1) with (Z.of_nat (S nR)) by (clear; lia). exact W8. }
  unfold cfg.
  (* [comment removed for export] *)
  assert (STEP: exists fx1 R1 M1, mem_grows M M1
      /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 304 <= i < sp - 304 + 16) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (st fx R 0x228c0 M) (st fx1 R1 0x214e4 M1)
      /\ (forall x, In x cs_all -> getr R1 (reg x) = getr R (reg x))
      /\ getr R1 (reg 1) = Z_to_bv 64 141556 /\ getr R1 (reg 10) = Z_to_bv 64 X /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat nR - 1 + 1)
      /\ L5.u64_at RSEGS M1 (sp - 304) (L5.bo_data rr (L5.BO frem (S nR) rst))).
  { destruct rst as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st].
    - destruct WS as (Wb0 & _).
      pose proof (d5ug9i_conc fx R M (Vd 0 0 0 0 0 0 0 (Z.of_nat nR - 1) frem 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H8 H9 ltac:(flia) A16 WFR VQS ltac:(flia) ARR ltac:(left; flia) W0 ltac:(flia) Wb0 W8'
                  ltac:(flia) ltac:(flia))
        as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & VRS1 & VRD1)). clear P.
      exists fx1, R1, M1. split. exact MG. split. exact FRZ. split. exact MS. split. { intros x Hx. apply KS. revert Hx. clear. intros Hx. L5K.inlist Hx. }
      split. exact A1. split. exact A10. split. exact A11. exact VRD1.
    - destruct WS as (Wb0 & _ & Uq & _ & Hcap & _ & Qlo & Qhi & _).
      pose proof (d5ug9_conc fx R M (Vd 0 0 0 0 0 0 0 (Z.of_nat nR - 1) frem q 0 0 0 0)) as P. cbn [Vd VdG] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H8 H9 ltac:(flia) A16 WFR VQS ltac:(flia) ARR ltac:(left; flia)
                  W0 ltac:(flia) Wb0 Uq W8' ltac:(flia) ltac:(flia) ltac:(flia))
        as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & VRS1 & VRD1)). clear P.
      exists fx1, R1, M1. split. exact MG. split. exact FRZ. split. exact MS. split. { intros x Hx. apply KS. revert Hx. clear. intros Hx. L5K.inlist Hx. }
      split. exact A1. split. exact A10. split. exact A11. exact VRD1. }
  destruct STEP as (fx1 & R1 & M1 & MG & KA0 & MS & KS & A1 & A10 & A11 & VRD1).
  replace (Z.of_nat nR - 1 + 1) with (Z.of_nat nR) in A11 by lia.
  (* [comment removed for export] *)
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 304)) as [Y|Y]. left; apply KA0; flia.
    destruct (Z_lt_le_dec a (sp - 304 + 16)) as [Y'|Y']. right; left; flia. left; apply KA0; flia. }
  assert (SCR1: L5.defined M1 (sp - 8976) 8976). { eapply L5.defined_grows. exact MG. exact SCR0. }
  assert (OBq1: L5.big_at RSEGS M1 X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX))). { eapply big_at_agree1. 4: exact OBq. intros i Hi. apply KA0; flia. flia. flia. }
  assert (OLq1: L5C.obj_limbs RSEGS M1 (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) wq).
  { destruct OLq as (Ln & F & S). split. exact Ln. split. exact F. cbn [L5.bo_st] in S |- *.
    apply (L5C.limbs_at_agree RSEGS M M1). 2: flia. 2: rewrite Ln; cbn [L5.bo_len]; flia. 2: exact S.
    intros i Hi. rewrite Ln in Hi. cbn [L5.bo_len] in Hi. apply KA0; flia. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  eapply (RESIZE fx1 R1 M1 model K LBc crc X spd 0x228f4 nR (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) wq HH1 MOK HK0 A10 A11).
  - flia.
  - cbn. intros _. flia.
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. intros _ F. pose proof fbX_bit0 as FB0. unfold fbX in FB0, F. cbn [L5.bo_fb] in FB0, F. rewrite FB0 in F. discriminate F.
  - exact A1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR1. flia. flia.
  - exact OBq1.
  - exact OLq1.
  - exact AX8. - unfold spd; flia. - exact HX.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG. exact DX. flia. flia.
  - cbn. intros cap q E. injection E. intros <- <-. rewrite ELB. apply in_app_iff. right. right. right. exact INQ.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & GPOST). destruct g as [|A cap].
    2:{ exfalso. destruct GPOST as (F & _). unfold L5.bo_dyn in F. pose proof fbX_bit0 as FB0. unfold fbX in FB0, F. cbn [L5.bo_fb] in FB0, F.
        rewrite FB0 in F. discriminate F. }
    destruct GPOST as (_ & -> & -> & (st' & OB2 & OL2 & SAME) & HP2). cbn [L5.bo_fb L5.bo_st] in OB2, SAME, HP2.
    destruct st' as [u0 u1|cap' q']. contradiction. destruct SAME as [-> ->].
    cbn [L5.bo_data L5.bo_st L5.bo_len] in HP2.
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> ~ (sp - 304 <= a < sp - 304 + 16) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha NX NV. rewrite <- (KA0 a) by flia. apply (kept_above M1 M2 LBc RESIZE_SCR _ a HP2). uSCR; clear; lia. exact Ha. apply outside2. exact NX. flia. }
    assert (KV: forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha NX. apply (kept_above M1 M2 LBc RESIZE_SCR _ a HP2). uSCR; clear; lia. exact Ha. apply outside2. exact NX. flia. }
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
    apply (stage_G10 fx2 R2 M2 model2 LBc crc B0 B1 fd0 fn0 fnum fden frem (L5.bo_data rr (L5.BO frem (S nR) rst)) (S nR) rst).
    + rewrite (preserved_sregs R1 R2 2 RP) by inl. rewrite (KS 2%nat) by inl. exact H2.
    + rewrite (preserved_sregs R1 R2 9 RP) by inl. rewrite (KS 9%nat) by inl. exact H9.
    + rewrite (preserved_sregs R1 R2 3 RP) by inl. rewrite (KS 3%nat) by inl. exact H3.
    + rewrite (preserved_sregs R1 R2 4 RP) by inl. rewrite (KS 4%nat) by inl. exact H4.
    + rewrite (preserved_sregs R1 R2 18 RP) by inl. rewrite (KS 18%nat) by inl. exact H18.
    + rewrite (preserved_sregs R1 R2 21 RP) by inl. rewrite (KS 21%nat) by inl. exact H21.
    + rewrite (preserved_sregs R1 R2 22 RP) by inl. rewrite (KS 22%nat) by inl. exact H22.
    + rewrite (preserved_sregs R1 R2 24 RP) by inl. rewrite (KS 24%nat) by inl. exact H24.
    + exact HnR.
    + exact MBV02.
    + exact HH2.
    + exact ELB. + exact NE01. + exact CRA.
    + eapply div_saves_kept. 4: exact DS. intros i Hi. apply KA; unfold spd; flia. flia. flia.
    + eapply marks_N_kept. 4: exact MK. intros i Hi. apply KA; unfold spd; flia. flia. flia.
    + eapply locals_N_kept. 4: exact LOC. intros i Hi. apply KA; unfold spd; flia. flia. flia.
    + eapply u64_at_agree1. 4: exact C120. intros i Hi. apply KA; unfold spd; flia. flia. flia.
    + eapply u64_at_agree1. 4: exact VRD1. intros i Hi. apply KV; unfold spd; flia. flia. flia.
    + eapply u64_at_agree1. 4: exact VD. intros i Hi. apply KA; unfold spd; flia. flia. flia.
    + eapply u64_at_agree1. 4: exact VS. intros i Hi. apply KA; unfold spd; flia. flia. flia.
    + exact OB2.
    + eapply (cdef_inblock M1 M2 LBc crc _ RESIZE_SCR _ qX 64 qX 64 HH1 HP2). rewrite ELB. apply in_app_iff. right. right. right. exact INQ. lia. lia.
      eapply L5.defined_grows. exact MG. exact DQ.
    + eapply (cdef_above M1 M2 LBc RESIZE_SCR _ X 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. eapply L5.defined_grows. exact MG. exact DX.
    + eapply big_at_agree1. 4: exact OBr. intros i Hi. apply KA; unfold spd. flia. generalize AP2 Hi; clear; lia. generalize SRR Hi; clear; lia. flia. flia.
    + destruct rst as [v0 v1|c q]. exact I. unfold rem_store in RS |- *. destruct RS as (RSa & RSb & RSc & RSd & RSe & RSf).
      refine (conj RSa (conj RSb (conj RSc (conj _ (conj RSe RSf))))).
      eapply (cdef_inblock M1 M2 LBc crc _ RESIZE_SCR _ q 64 q 64 HH1 HP2). rewrite ELB. cbn. left. reflexivity. lia. lia. eapply L5.defined_grows. exact MG. exact RSd.
    + eapply (cdef_above M1 M2 LBc RESIZE_SCR _ rr 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. eapply L5.defined_grows. exact MG. exact DR.
    + reflexivity. + reflexivity.
    + destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KA; unfold spd. flia. generalize AP1 Hi; clear; lia.
      generalize SDV Hi; clear; lia. flia. flia.
    + (* [comment removed for export] *)
      assert (HP1: L5C.hpres L LB sp DIV_SCR WN M0 M1).
      { eapply (L5HP.hpres_trans L LB LB sp DIV_SCR WN M0 M M1 sp DIV_SCR WN). exact HP.
        - eapply (L5HP.hpres_piece L LB sp DIV_SCR WN M M1 (fun a => sp - 352 <= a < sp)).
          + intros a Ha Hn'. apply KA0; flia.
          + intros a KA' C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR WN a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
          + rewrite DIV_SCR_val. exact SCR1.
          + exact MG.
        - intros a KA'; exact KA'.
        - intros b Hb; exact Hb.
        - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
      eapply (L5HP.hpres_trans L LB LBc sp DIV_SCR WN M0 M1 M2 spd RESIZE_SCR). exact HP1. exact HP2.
      * intros a KA'. eapply L5HP.kept_mono. exact KA'. { intros b Hb. rewrite ELB. apply in_app_iff. right; right; right; exact Hb. }
        unfold spd; fsclia. unfold spd; flia.
        intros OW. apply outside2. apply (L5HP.outside_in _ _ X 32 OW). cbn; left; reflexivity.
        intros C. apply (L5HP.outside_in _ _ qX 64 OW). cbn; right; left; reflexivity. flia.
      * intros b Hb. rewrite ELB. apply in_app_iff. right; right; right; exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_GROW (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden frem : Z) (rst : L5.bstore) (wr : list Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 rr -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 22) = Z_to_bv 64 0 ->
  getr R (reg 24) = Z_to_bv 64 (Z.of_nat nR) -> (1 <= nR)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = rem_blocks rst ++ (B0, 64) :: (B1, 64) :: LB -> B0 <> B1 ->
  match rst with L5.BInl _ _ => crc = debit L (debit L cr 64) 64 | L5.BDyn _ _ => credit_after L cr DIVN_K DIVN_BYTES crc end ->
  div_saves M sp R0 -> marks_N M sp rr -> locals_N M sp B0 B1 fd0 fn0 fnum fden -> L5.u64_at RSEGS M (sp - 120) MWORD ->
  L5.u64_at RSEGS M (sp - 152) (sp - 120) -> L5.u64_at RSEGS M (sp - 144) 1 -> L5.u64_at RSEGS M (sp - 224) (Z.of_nat nR - 1) ->
  L5.u64_at RSEGS M (sp - 296) (Z.of_nat nR) ->
  L5.big_at RSEGS M X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5.big_at RSEGS M rr (L5.BO frem nR rst) -> L5C.obj_limbs RSEGS M (L5.BO frem nR rst) wr -> rem_store L LB M B0 B1 rst -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x228b0 M model) K.
Proof.
  intros H2 H9 H3 H4 H8 H18 H21 H22 H24 HnR MBV HH ELB NE01 CRC DS MK LOC C120 VD VS VQS VRS OBq DQ DX OBr OLr RS DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hn: (nR <= 6)%nat). { pose proof nR_le. unfold lenX in *. clear - H LENX. lia. }
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  assert (CRA: credit_after L cr DIVN_K DIVN_BYTES crc). { destruct rst. rewrite CRC. apply credit_after2. exact KPOS. exact BPOS. exact CRC. }
  pose proof (credit_chain L cr KPOS BPOS CR) as (_ & _ & CR3).
  pose proof OBr as (W0 & Wf & W8 & WS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in W0, Wf, W8, WS.
  assert (WFR: L5.writable RSEGS M (sp - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d5ug8_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) H2 H8 ltac:(flia) A16 WFR VRS ltac:(flia))
    as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11)). clear P.
  pose proof (mem_eq M M1 FR) as EM1. subst M1.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  replace (Z.of_nat nR + 1) with (Z.of_nat (S nR)) in A11 by lia.
  eapply (RESIZE fx1 R1 M model K LBc crc rr spd 0x228c0 (S nR) (L5.BO frem nR rst) wr HH MOK HK0 A10 A11).
  - flia.
  - unfold L5.bo_dyn. cbn [L5.bo_fb L5.bo_cap L5.bo_st]. destruct rst as [v0 v1|c q]. { destruct WS as (Tb & _). rewrite Tb. intros F; discriminate F. }
    unfold rem_store in RS. destruct RS as (-> & _). cbn. intros _. flia.
  - unfold L5.bo_dyn. cbn [L5.bo_fb]. intros _ DYF. replace (round_up (Z.of_nat (S nR))) with 8.
    2:{ unfold round_up. replace (Z.of_nat (S nR) / 8) with 0. reflexivity. symmetry. apply Z.div_small. lia. }
    destruct rst as [v0 v1|c q]. rewrite CRC. exact CR3.
    exfalso. destruct WS as (Tb & _). rewrite Tb in DYF. discriminate DYF.
  - exact A1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact OBr.
  - exact OLr.
  - exact ARR. - unfold spd; flia. - exact HRR.
  - apply (L5C.writable_of_defined RSEGS). exact DR. flia. flia.
  - cbn. intros cap q E. subst rst. rewrite ELB. cbn. left. unfold rem_store in RS. destruct RS as (-> & _). reflexivity.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP & GPOST).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
    (* [comment removed for export] *)
    assert (HP2W: exists W2, L5C.hpres L LBc spd RESIZE_SCR W2 M M2 /\
                  (forall a, ~ (rr <= a < rr + 32) -> (forall c q, rst = L5.BDyn c q -> ~ (q <= a < q + 64)) -> L5.outside W2 a)).
    { destruct g as [|A cap].
      - destruct GPOST as (DYS & _ & _ & _ & HP2). eexists. split. exact HP2. intros a N1 N2. apply outside2. exact N1.
        destruct rst as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st L5.bo_len].
        { destruct DYS as [DY|SM]. { unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY. destruct WS as (Tb & _). rewrite Tb in DY. discriminate DY. } flia. }
        specialize (N2 c q eq_refl). flia.
      - destruct GPOST as (_ & _ & _ & _ & _ & _ & _ & _ & HP2). eexists. split. exact HP2. intros a N1 N2. apply outside1. exact N1. }
    destruct HP2W as (W2 & HP2 & OW2).
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (rr <= a < rr + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1. apply (kept_above M M2 LBc RESIZE_SCR _ a HP2). uSCR; clear; lia. exact Ha. apply OW2. exact N1.
      intros c q E. subst rst. unfold rem_store in RS. destruct RS as (_ & (_ & _ & _ & _ & Bq4) & _). unfold spd in Ha. flia. }
    assert (DQ2: L5.defined M2 qX 64).
    { eapply (cdef_inblock M M2 LBc crc _ RESIZE_SCR _ qX 64 qX 64 HH HP2). rewrite ELB. apply in_app_iff. right. right. right. exact INQ. lia. lia. exact DQ. }
    destruct (L5KU.limbs_of_defined M2 qX (nR - 1) ltac:(eapply L5.defined_sub; [exact DQ2 | flia | flia]) ltac:(flia) ltac:(flia)) as (wq & WQL & WQR & WQA).
    assert (OLq2: L5C.obj_limbs RSEGS M2 (L5.BO fbX (nR - 1) (L5.BDyn 8 qX)) wq). { split. exact WQL. split. exact WQR. exact WQA. }
    assert (OBq2: L5.big_at RSEGS M2 X (L5.BO fbX (nR - 1) (L5.BDyn 8 qX))).
    { eapply big_at_agree1. 4: exact OBq. intros i Hi. apply KA; unfold spd. flia. generalize AP2 Hi; clear; lia. flia. flia. }
    assert (DS2: div_saves M2 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (MK2: marks_N M2 sp rr). { eapply marks_N_kept. 4: exact MK. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (LOC2: locals_N M2 sp B0 B1 fd0 fn0 fnum fden). { eapply locals_N_kept. 4: exact LOC. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (C120': L5.u64_at RSEGS M2 (sp - 120) MWORD). { eapply u64_at_agree1. 4: exact C120. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (VD': L5.u64_at RSEGS M2 (sp - 152) (sp - 120)). { eapply u64_at_agree1. 4: exact VD. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (VS': L5.u64_at RSEGS M2 (sp - 144) 1). { eapply u64_at_agree1. 4: exact VS. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (VQS': L5.u64_at RSEGS M2 (sp - 224) (Z.of_nat nR - 1)). { eapply u64_at_agree1. 4: exact VQS. intros i Hi. apply KA; unfold spd; flia. flia. flia. }
    assert (DX2: L5.defined M2 X 32). { eapply (cdef_above M M2 LBc RESIZE_SCR _ X 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DX. }
    assert (DR2: L5.defined M2 rr 32). { eapply (cdef_above M M2 LBc RESIZE_SCR _ rr 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DR. }
    assert (MW2: mword_obj M2 dv fdv).
    { destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KA; unfold spd. flia. generalize AP3 Hi; clear; lia. flia. flia. }
    assert (REGS: forall i v, In i cs_all -> In i KS_d5ug8 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    assert (HPc: L5C.hpres L LB sp DIV_SCR WN M0 M2).
    { eapply (L5HP.hpres_trans L LB LBc sp DIV_SCR WN M0 M M2 spd RESIZE_SCR). exact HP. exact HP2.
      * intros a KA'. eapply L5HP.kept_mono. exact KA'. { intros b Hb. rewrite ELB. apply in_app_iff. right; right; right; exact Hb. }
        unfold spd; fsclia. unfold spd; flia.
        intros OW. apply OW2. apply (L5HP.outside_in _ _ rr 32 OW). cbn; right; right; left; reflexivity.
        intros c q E. subst rst. unfold rem_store in RS. destruct RS as (-> & (Bq0 & Bq1 & Bq2 & Bq3 & Bq4) & BAq & DQq & Nq0 & Nq1).
        refine (L5C.kept_not_fresh L LB sp DIV_SCR WN a q 64 KA' BAq _ Bq4 (LBhi _ _ _ _ HH0)). exact Bq1.
      * intros b Hb. rewrite ELB. apply in_app_iff. right; right; right; exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP). }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct GPOST as (_ & -> & -> & (st' & OB2 & OL2 & SAME) & _). cbn [L5.bo_fb L5.bo_st] in OB2, SAME.
      assert (RS2: rem_store L LB M2 B0 B1 st' /\ rem_blocks st' = rem_blocks rst).
      { destruct rst as [v0 v1|c q]; destruct st' as [u0 u1|c' q']; try contradiction. split. exact I. reflexivity.
        destruct SAME as [-> ->]. split. 2: reflexivity. unfold rem_store in RS |- *. destruct RS as (RSa & RSb & RSc & RSd & RSe & RSf).
        refine (conj RSa (conj RSb (conj RSc (conj _ (conj RSe RSf))))).
        eapply (cdef_inblock M M2 LBc crc _ RESIZE_SCR _ q 64 q 64 HH HP2). rewrite ELB. cbn. left. reflexivity. lia. lia. exact RSd. }
      destruct RS2 as [RS2 RB2].
      apply (stage_G9 fx2 R2 M2 model2 LBc crc B0 B1 fd0 fn0 fnum fden frem st' wq).
      all: try (eapply REGS; [inl | inl | assumption]).
      * exact HnR. * exact MBV02. * exact HH2. * rewrite RB2. exact ELB. * exact NE01. * exact CRA.
      * exact DS2. * exact MK2. * exact LOC2. * exact C120'. * exact VD'. * exact VS'. * exact VQS'. * exact OBq2. * exact OLq2. * exact DQ2. * exact DX2.
      * exact OB2. * exact RS2. * exact DR2. * exact MW2.
      * exact HPc.
    + (* [comment removed for export] *)
      destruct GPOST as (DYF & H3n & Hcap & -> & -> & FB & OB2 & OL2 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB2, OL2.
      replace (round_up (Z.of_nat (S nR))) with 8 in Hcap.
      2:{ unfold round_up. replace (Z.of_nat (S nR) / 8) with 0. reflexivity. symmetry. apply Z.div_small. lia. }
      subst cap.
      assert (RST0: exists v0 v1, rst = L5.BInl v0 v1).
      { destruct rst as [v0 v1|c q]. eexists _, _; reflexivity. exfalso. unfold L5.bo_dyn in DYF. cbn [L5.bo_fb] in DYF. destruct WS as (Tb & _). rewrite Tb in DYF. discriminate DYF. }
      destruct RST0 as (v0 & v1 & ->). cbn [rem_blocks app] in ELB. rewrite CRC in *.
      pose proof FB as (BRA & BAA & DFA). pose proof BRA as (BA0 & BA1 & BA2 & BA3 & BA4).
      assert (NA0: A <> B0). { pose proof (BAA (B0, 64) ltac:(rewrite ELB; cbn; left; reflexivity)). cbn in H. lia. }
      assert (NA1: A <> B1). { pose proof (BAA (B1, 64) ltac:(rewrite ELB; cbn; right; left; reflexivity)). cbn in H. lia. }
      apply (stage_G9 fx2 R2 M2 model2 ((A, 8 * 8) :: LBc) (debit L (debit L (debit L cr 64) 64) (8 * 8)) B0 B1 fd0 fn0 fnum fden (Z.lor frem 1) (L5.BDyn 8 A) wq).
      all: try (eapply REGS; [inl | inl | assumption]).
      * exact HnR. * exact MBV02. * exact HH2. * rewrite ELB. reflexivity. * exact NE01. * apply credit_after3.
      * exact DS2. * exact MK2. * exact LOC2. * exact C120'. * exact VD'. * exact VS'. * exact VQS'. * exact OBq2. * exact OLq2. * exact DQ2. * exact DX2.
      * exact OB2.
      * unfold rem_store. split. reflexivity. split. exact BRA. split. { intros b Hb. apply BAA. rewrite ELB. cbn. right; right; exact Hb. }
        split. exact DFA. split. exact NA0. exact NA1.
      * exact DR2. * exact MW2.
      * exact HPc.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKBU.
