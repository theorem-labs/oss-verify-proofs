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
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivNOkA L5DivNOkB L5DivNOkC L5DivNOkD.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKE.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVNOKA. Import L5DIVNOKB. Import L5DIVNOKC. Import L5DIVNOKD.

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
Let stage_G5 := @L5DIVNOKD.stage_G5 _ L HI LY HIok KPOS BPOS ASSIGN RESIZE DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX OLX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 CR KONT KONT3.
Local Ltac slia :=
  match goal with
  | A : 140735332483072 + 8848 <= ?s, B : ?s <= 2 ^ 47, C : ?s <= hl_sptop _, D : hl_sptop _ - 8388608 + 8848 <= ?s |- _ => generalize A B C D SX SDV SRR HX HDV HRR SPTOP; clear; intros; lia
  end.
Local Ltac kcw K H := first [ eapply u64_at_agree1 | eapply u8_at_agree1 | eapply big_at_agree1 ];
  [ intros i Hi; apply K; generalize Hi SX; unfold spd; slia | slia | slia | exactA H ].

Lemma r19 : (19%bv : bv 5) = reg 19. Proof. apply bv_eq; reflexivity. Qed.
Lemma r20 : (20%bv : bv 5) = reg 20. Proof. apply bv_eq; reflexivity. Qed.
Lemma r21 : (21%bv : bv 5) = reg 21. Proof. apply bv_eq; reflexivity. Qed.
Lemma r22 : (22%bv : bv 5) = reg 22. Proof. apply bv_eq; reflexivity. Qed.
Lemma r23 : (23%bv : bv 5) = reg 23. Proof. apply bv_eq; reflexivity. Qed.
Lemma r24 : (24%bv : bv 5) = reg 24. Proof. apply bv_eq; reflexivity. Qed.
Lemma r25 : (25%bv : bv 5) = reg 25. Proof. apply bv_eq; reflexivity. Qed.
Lemma r26 : (26%bv : bv 5) = reg 26. Proof. apply bv_eq; reflexivity. Qed.
Lemma r27 : (27%bv : bv 5) = reg 27. Proof. apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Definition frame4 (M : word -> option byte) (B0 B1 fd0 fn0 fnum fden : Z) : Prop :=
     L5.u8_at RSEGS M (sp - 232) fd0 /\ 0 <= fd0 < 256 /\ Z.testbit fd0 0 = false
  /\ L5.u64_at RSEGS M (sp - 224) 1 /\ L5.u64_at RSEGS M (sp - 216) MWORD /\ L5.u64_at RSEGS M (sp - 208) 0
  /\ L5.u8_at RSEGS M (sp - 200) fn0 /\ 0 <= fn0 < 256 /\ Z.testbit fn0 0 = true
  /\ L5.u64_at RSEGS M (sp - 192) (Z.of_nat lenX) /\ L5.u64_at RSEGS M (sp - 184) 8 /\ L5.u64_at RSEGS M (sp - 176) B0
  /\ L5.u8_at RSEGS M (sp - 168) fnum /\ 0 <= fnum < 256 /\ Z.testbit fnum 0 = true /\ Z.testbit fnum 1 = false
  /\ L5.u64_at RSEGS M (sp - 160) (Z.of_nat nR) /\ L5.u64_at RSEGS M (sp - 152) 8 /\ L5.u64_at RSEGS M (sp - 144) B1
  /\ L5.u8_at RSEGS M (sp - 136) fden /\ 0 <= fden < 256 /\ Z.testbit fden 0 = false /\ Z.testbit fden 1 = false
  /\ L5.u64_at RSEGS M (sp - 128) 1 /\ L5.u64_at RSEGS M (sp - 120) MWORD /\ L5.defined M (sp - 112) 8
  /\ L5.u32_at RSEGS M (sp - 236) 0 /\ L5.u64_at RSEGS M (sp - 256) 0.
Lemma frame4_kept M M' B0 B1 fd0 fn0 fnum fden :
  (forall i, sp - 256 <= i < sp - 104 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> frame4 M B0 B1 fd0 fn0 fnum fden -> frame4 M' B0 B1 fd0 fn0 fnum fden.
Proof.
  intros HA F4. pose proof SPW as (A16 & SLO & SHI & _).
  destruct F4 as (A1 & A2 & A3 & A4 & A5 & A6 & B1' & B2 & B3 & B4 & B5 & B6 & C1 & C2 & C3 & C3' & C4 & C5 & C6 & D1 & D2 & D3 & D3' & D4 & D5 & D6 & E1 & E2).
  unfold frame4. repeat split;
    first [ assumption
          | eapply u8_at_agree1; [intros i Hi; apply HA; clear - Hi; lia | clear - SLO; lia | clear -SHI; lia | eassumption]
          | eapply u64_at_agree1; [intros i Hi; apply HA; clear - Hi; lia | clear - SLO; lia | clear - SHI; lia | eassumption]
          | eapply u32_at_agree1; [intros i Hi; apply HA; clear - Hi; lia | clear - SLO; lia | clear - SHI; lia | eassumption]
          | eapply defined_agree1; [intros i Hi; apply HA; clear - Hi; lia | eassumption]
          | clear - A2 B2 C2 D2; lia ].
Qed.
Lemma hpres_weakW M M' W : L5C.hpres L LB sp DIV_SCR [] M M' -> L5C.hpres L LB sp DIV_SCR W M M'.
Proof.
  intros (P1 & P2 & P3). split. { intros a (Ha & CA & NE & OW). apply P1. split. exact Ha. split. exact CA. split. exact NE. apply L5C.outside_nil. }
  split. exact P2. exact P3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G4 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden : Z) :
  let LBc := (B0, 64) :: (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 20) = Z_to_bv 64 (sp - 120) ->
  getr R (reg 22) = Z_to_bv 64 B1 -> getr R (reg 23) = Z_to_bv 64 qX -> getr R (reg 24) = Z_to_bv 64 (X + 16) -> getr R (reg 25) = getr R0 (reg 25) ->
  getr R (reg 26) = Z_to_bv 64 0 -> getr R (reg 27) = Z_to_bv 64 rr ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> B0 <> B1 ->
  block_range L B1 64 /\ blocks_apart B1 64 LB -> block_range L B0 64 /\ blocks_apart B0 64 ((B1, 64) :: LB) -> crc = debit L (debit L cr 64) 64 ->
  div_saves M sp R0 -> frame4 M B0 B1 fd0 fn0 fnum fden ->
  L5.big_at RSEGS M (sp - 168) (L5.BO fnum nR (L5.BDyn 8 B1)) -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M X bX -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DS.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x220d4 M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H10 H18 H20 H22 H23 H24 H25 H26 H27 MBV HH NE01 [BR1 BA1] [BR0 BA0] CRC DS F4 OBn LAn OBXc DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hn: (nR <= 6)%nat). { pose proof nR_le. unfold lenX in *. clear - H LENX. lia. }
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof F4 as (Fd0 & Fd0r & Fd0b & F224 & F216 & F208 & Fn0 & Fn0r & Fn0b & F192 & F184 & F176 & Fn & Fnr & Fnb & Fnb1 & F160 & F152 & F144 & Fd & Fdr & Fdb & Fdb1 & F128 & F120 & F112 & F236 & F256).
  assert (WFR: L5.writable RSEGS M (sp - 304) 304).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  pose proof OBXc as OBq. unfold L5.big_at in OBq. rewrite STX in OBq. fold fbX lenX in OBq.
  unfold cfg.
  pose proof (d5g4i_conc fx R M (Vd 0 fden 0 0 0 (X + 16) 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H9 H10 H24 ltac:(flia) A16 WFR Fd F128 F160 ltac:(flia) Fdb ltac:(flia) ltac:(flia))
    as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A19 & A21 & C264 & C296)). clear P.
  change (Z.of_nat nR - 1) with (Z.of_nat nR - 1) in A11.
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 296 <= i < sp - 288) -> ~ (sp - 264 <= i < sp - 256) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2. apply FRZ. exact Hi. flia. flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_le_gt_dec (sp - 296) a) as [C1|C1]; [destruct (Z_lt_le_dec a (sp - 256)) as [C2|C2]|].
    right; left; flia. all: left; apply KFR; flia. }
  assert (DS1: div_saves M1 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi. apply KFR; generalize Hi SX SRR SDV; slia. slia. slia. }
  assert (F4': frame4 M1 B0 B1 fd0 fn0 fnum fden). { eapply frame4_kept. 2: exact F4. intros i Hi. apply KFR; generalize Hi SX SRR SDV; slia. }
  assert (OBn1: L5.big_at RSEGS M1 (sp - 168) (L5.BO fnum nR (L5.BDyn 8 B1))). { eapply big_at_agree1. 4: exact OBn. intros i Hi. apply KFR; generalize Hi SX SRR SDV; slia. slia. slia. }
  pose proof BR1 as (B1a & B1b & B1c & B1d & B1e). pose proof BR0 as (B0a & B0b & B0c & B0d & B0e).
  assert (LAn1: L5.limbs_at RSEGS M1 B1 wX).
  { pose proof wX_len as WL. unfold lenX in WL. eapply L5C.limbs_at_agree. 4: exact LAn. 2: flia. 2: flia. intros i Hi. apply KFR; generalize Hi B1a B1e WL LENX; slia. }
  assert (OBX1: L5.big_at RSEGS M1 X bX). { eapply big_at_agree1. 4: exact OBXc. intros i Hi. apply KFR; generalize Hi SX SRR SDV; slia. slia. slia. }
  assert (DQ1: L5.defined M1 qX 64). { eapply L5.defined_grows. exact MG. exact DQ. }
  assert (DX1: L5.defined M1 X 32). { eapply L5.defined_grows. exact MG. exact DX. }
  assert (ZR1: L5DS.zero_obj M1 rr). { eapply big_at_agree1. 4: exact ZRc. intros i Hi. apply KFR; generalize Hi SX SRR SDV; slia. slia. slia. }
  assert (DR1: L5.defined M1 rr 32). { eapply L5.defined_grows. exact MG. exact DR. }
  assert (MW1: mword_obj M1 dv fdv). { destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KFR; generalize Hi SX SRR SDV; slia. slia. slia. }
  assert (HP1: L5C.hpres L LB sp DIV_SCR [] M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIV_SCR [] M0 M M1 sp DIV_SCR []). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIV_SCR [] M M1 (fun a => sp - 296 <= a < sp - 256)).
      + intros a Ha Hn'. apply KFR. exact Ha. flia. flia.
      + intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
      + rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG. exact SCR0.
      + exact MG.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  assert (SCR1: L5.defined M1 (sp - 8848) 8848). { eapply L5.defined_grows. exact MG. exact SCR0. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  destruct (Nat.eq_dec nR 0) as [NZ|NZ].
  - (* [comment removed for export] *)
    rewrite NZ in A11, A19, OBn1. cbn [Z.of_nat] in A11, A19.
    assert (A11': getr R1 (reg 11) = Z_to_bv 64 (2 ^ 64 - 1)). { rewrite A11. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
    eapply (HUGE fx1 R1 M1 model K X spd (2 ^ 64 - 1) bX Mh Ml A10 A11').
    + unfold MAX_SIZE. lia.
    + rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
    + unfold spd; flia. + unfold spd; flia.
    + unfold spd. eapply L5.defined_sub. exact SCR1. flia. flia.
    + exact OBX1.
    + unfold L5.bo_dyn. pose proof fbX_bit0 as FB0. unfold fbX in FB0. exact FB0.
    + flia. + exact XHI. + right. unfold spd; flia.
    + (* [comment removed for export] *)
      intros fx3 R3 M3 HAT.
      destruct HAT as (T2 & T3 & T4 & T1 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & T10 & T11 & T12
                       & U8 & U16 & U24 & U32 & U72 & U80 & U88 & U96 & U104 & U112 & U120 & FB3 & MG3).
      assert (K3: forall i, 0 <= i < 2 ^ 64 -> ~ (spd - 128 <= i < spd) -> M3 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
      { intros i Hi Ni. apply FB3. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by exact Hi. unfold spd in *. flia. }
      assert (REG1: forall k v, In k KS_d5g4i -> getr R (reg k) = v -> getr R1 (reg k) = v). { intros k v Hk Hv. rewrite (KS k Hk). exact Hv. }
      assert (UR: forall (Rx : bvmap 5 word) (k : Z) v, getr Rx (Z_to_bv 5 k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U Rx k = v).
      { intros Rx k v Hk Hv. unfold U. rewrite Hk. apply BG.unsigned_lit. exact Hv. }
      pose proof F4' as (Gd0 & _ & _ & G224 & G216 & G208 & Gn0 & _ & _ & G192 & G184 & G176 & Gn & _ & _ & _ & G160 & G152 & G144 & Gd & _ & _ & _ & G128 & G120 & G112 & G236 & G256).
      apply (KONT3 fx3 R3 M3 model LBc crc).
      2: exact MBV.
      2:{ eapply (L5C.hi_heap_client L SCFG HI LBc crc M1 M3). exact HIok. exact HH1. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG3.
          intros a Ha. destruct (Z_le_gt_dec (spd - 128) a) as [C1|C1]; [destruct (Z_lt_le_dec a spd) as [C2|C2]|].
          right; left; unfold spd in *; flia. all: left; apply K3; flia. }
      unfold divN_e3. exists B0, B1, (2 ^ 64 - 1), fd0, fn0, fnum, fden.
      Ltac kcell K3 H := first [ eapply u64_at_agree1 | eapply u8_at_agree1 | eapply u32_at_agree1 ];
                         [ intros i Hi; apply K3; generalize Hi; unfold spd; slia | unfold spd; slia | unfold spd; slia | exactA H ].
      repeat match goal with |- _ /\ _ => split end.
      * rewrite T2. unfold spd. f_equal. lia.
      * rewrite T3, r3. rewrite (KS 3%nat) by inl. rewrite H3, <- r3, G3. reflexivity.
      * rewrite T4, r4. rewrite (KS 4%nat) by inl. rewrite H4, <- r4, G4. reflexivity.
      * exact T1. * exact T10. * exact T11. * exact T12. * reflexivity.
      * exact T8. * exact T9. * rewrite T18. unfold lenX. reflexivity.
      * rewrite T19, r19. exact A19.
      * rewrite T20, r20. apply (REG1 20%nat). inl. exact H20.
      * rewrite T21, r21. exact A21.
      * rewrite T22, r22. apply (REG1 22%nat). inl. exact H22.
      * rewrite T23, r23. apply (REG1 23%nat). inl. exact H23.
      * rewrite T24, r24. apply (REG1 24%nat). inl. exact H24.
      * rewrite T25, r25. rewrite (KS 25%nat) by inl. exact H25.
      * rewrite T26, r26. apply (REG1 26%nat). inl. exact H26.
      * rewrite T27, r27. apply (REG1 27%nat). inl. exact H27.
      * (* [comment removed for export] *) rewrite (UR R1 1 139520 A1 ltac:(lia)) in U8. exactA U8.
      * rewrite (UR R1 8 0 (REG1 8%nat _ ltac:(inl) H8) ltac:(lia)) in U16. exactA U16.
      * rewrite (UR R1 9 X (REG1 9%nat _ ltac:(inl) H9) ltac:(generalize SX SLO HX SPTOP; clear; intros; lia)) in U24. exactA U24.
      * rewrite (UR R1 18 X (REG1 18%nat _ ltac:(inl) H18) ltac:(generalize SX SLO HX SPTOP; clear; intros; lia)) in U32. exactA U32.
      * exactA U72. * exactA U80. * exactA U88.
      * unfold lenX. exactA U96.
      * rewrite (UR R1 19 0 A19 ltac:(lia)) in U104. exactA U104.
      * rewrite (UR R1 20 (sp - 120) (REG1 20%nat _ ltac:(inl) H20) ltac:(generalize SLO SHI; clear; intros; lia)) in U112. exactA U112.
      * rewrite (UR R1 21 1 A21 ltac:(lia)) in U120. exactA U120.
      * eapply div_saves_kept. 4: exact DS1. intros i Hi. apply K3; generalize Hi; unfold spd; slia. flia. flia.
      * kcell K3 Gd0. * flia. * flia. * exact Fd0b. * kcell K3 G224. * kcell K3 G216. * kcell K3 G208.
      * kcell K3 Gn0. * flia. * flia. * exact Fn0b. * kcell K3 G192. * kcell K3 G184. * kcell K3 G176.
      * kcell K3 Gn. * flia. * flia. * exact Fnb. * exact Fnb1. * rewrite NZ in G160. cbn [Z.of_nat] in G160. kcell K3 G160. * kcell K3 G152. * kcell K3 G144.
      * kcell K3 Gd. * flia. * flia. * exact Fdb. * exact Fdb1. * kcell K3 G128. * kcell K3 G120.
      * eapply defined_agree1. 2: exact G112. intros i Hi. apply K3; unfold spd; flia.
      * kcell K3 G236. * kcell K3 G256. * kcell K3 C264. * kcell K3 C296.
      * reflexivity.
      * split. exact BR1. split. exact BA1. eapply L5.defined_grows. exact MG3. eapply L5.defined_grows. exact MG.
        exact (proj1 (LBdef _ _ _ _ HH B1 64 ltac:(right; left; reflexivity))).
      * split. exact BR0. split. exact BA0. eapply L5.defined_grows. exact MG3. eapply L5.defined_grows. exact MG.
        exact (proj1 (LBdef _ _ _ _ HH B0 64 ltac:(left; reflexivity))).
      * exact CRC.
      * eapply (L5HP.hpres_trans L LB LB sp DIV_SCR [] M0 M1 M3 sp DIV_SCR []). exact HP1.
        -- eapply (L5HP.hpres_piece L LB sp DIV_SCR [] M1 M3 (fun a => spd - 128 <= a < spd)).
           ++ intros a Ha Hn'. apply K3. exact Ha. exact Hn'.
           ++ intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. unfold spd in C; fsclia.
           ++ rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG3. exact SCR1.
           ++ exact MG3.
        -- intros a KA; exact KA. -- intros b Hb; exact Hb. -- fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
  - (* [comment removed for export] *)
    pose proof nR_le as NRLE. fold lenX in NRLE.
    destruct (L5KS.limbs_of_defined M1 qX lenX ltac:(eapply L5.defined_sub; [exact DQ1 | flia | unfold lenX in *; flia]) ltac:(flia) ltac:(unfold lenX in *; flia)) as (wq & WQL & WQR & WQA).
    replace (Z.of_nat nR - 1) with (Z.of_nat (nR - 1)%nat) in A11 by (clear - NZ; lia).
    eapply (RESIZE fx1 R1 M1 model K LBc crc X spd 0x22100 (nR - 1)%nat bX wq HH1 MOK HK0 A10 A11).
    + flia.
    + unfold L5.bo_cap. rewrite STX. intros _. flia.
    + intros _ F. exfalso. unfold L5.bo_dyn in F. pose proof fbX_bit0 as FB0. unfold fbX in FB0. rewrite FB0 in F. discriminate F.
    + exact A1.
    + split. flia. reflexivity.
    + rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
    + rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
    + split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
      split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR1. flia. flia.
    + exact OBX1.
    + split. rewrite WQL. reflexivity. split. exact WQR. rewrite STX. exact WQA.
    + exact AX8. + unfold spd; flia. + exact HX.
    + apply (L5C.writable_of_defined RSEGS). exact DX1. flia. flia.
    + rewrite STX. intros cap q E. injection E. intros <- <-. right. right. exact INQ.
    + (* [comment removed for export] *)
      intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
      destruct POST as (RP & GPOST). destruct g as [|A cap].
      2:{ exfalso. destruct GPOST as (F & _). unfold L5.bo_dyn in F. pose proof fbX_bit0 as FB0. unfold fbX in FB0. rewrite FB0 in F. discriminate F. }
      destruct GPOST as (_ & -> & -> & (st' & OB2 & OL2 & SAME) & HP2). rewrite STX in SAME. fold fbX in OB2.
      destruct st' as [u0 u1|cap' q']. contradiction. destruct SAME as [-> ->].
      unfold L5.bo_data in HP2. rewrite STX in HP2. cbn [L5.bo_len] in HP2. fold lenX in HP2.
      pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
      assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha NX. apply (kept_above M1 M2 LBc RESIZE_SCR _ a HP2). uSCR; clear; lia. exact Ha. apply outside2. exact NX.
        unfold spd in Ha. generalize Ha Q3 NRLE Hn SLO'; clear; intros; lia. }
      assert (REGS: forall i v, In i cs_all -> In i KS_d5g4i -> getr R (reg i) = v -> getr R2 (reg i) = v).
      { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
      pose proof F4' as (Gd0 & Gd0r & Gd0b & G224 & G216 & G208 & Gn0 & Gn0r & Gn0b & G192 & G184 & G176 & Gn & Gnr & Gnb & Gnb1 & G160 & G152 & G144 & Gd & Gdr & Gdb & Gdb1 & G128 & G120 & G112 & G236 & G256).
      apply (stage_G5 fx2 R2 M2 model2 crc B0 B1 fd0 fn0 fnum fden).
      all: try (eapply REGS; [inl | inl | assumption]).
      * rewrite (preserved_sregs R1 R2 19 RP) by inl. exact A19.
      * rewrite (preserved_sregs R1 R2 21 RP) by inl. exact A21.
      * clear - NZ; lia. * exact MBV02. * exact HH2. * exact NE01. * exact BA1. * exact CRC.
      * eapply div_saves_kept. 4: exact DS1. intros i Hi. apply KA; generalize Hi SX; unfold spd; slia. flia. flia.
      * unfold locals_N. repeat match goal with |- _ /\ _ => split end.
        -- kcw KA Gd0. -- lia. -- lia. -- exact Gd0b. -- kcw KA Gn0. -- lia. -- lia. -- exact Gn0b. -- kcw KA G184. -- kcw KA G176.
        -- kcw KA Gn. -- lia. -- lia. -- exact Gnb. -- kcw KA G152. -- kcw KA G144. -- kcw KA Gd. -- lia. -- lia. -- exact Gdb.
      * exact Gnb1.
      * kcw KA G120. * kcw KA C264. * kcw KA G256.
      * kcw KA OBn1.
      * pose proof wX_len as WL. unfold lenX in WL. pose proof (BA1 (qX, 64) INQ) as AP. cbn in AP.
        eapply L5C.limbs_at_agree. 4: exact LAn1. 2: flia. 2: flia. intros i Hi.
        apply (kept_inblock M1 M2 LBc crc _ RESIZE_SCR _ B1 64 i HH1 HP2). right; left; reflexivity. generalize Hi WL LENX; clear; intros; lia.
        apply outside2. generalize Hi B1e SLO' SX WL LENX; clear; intros; lia. generalize AP Hi WL LENX NRLE; clear; intros; lia.
      * exact OB2.
      * eapply (cdef_inblock M1 M2 LBc crc _ RESIZE_SCR _ qX 64 qX 64 HH1 HP2). right; right; exact INQ. lia. lia. exact DQ1.
      * eapply (cdef_above M1 M2 LBc RESIZE_SCR _ X 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DX1.
      * eapply big_at_agree1. 4: exact ZR1. intros i Hi. apply KA; unfold spd. flia. generalize AP2 Hi; clear; lia. flia. flia.
      * eapply (cdef_above M1 M2 LBc RESIZE_SCR _ rr 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. exact DR1.
      * destruct MW1 as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KA; unfold spd. flia. generalize AP1 Hi; clear; lia. flia. flia.
      * eapply (L5HP.hpres_trans L LB LBc sp DIV_SCR WN M0 M1 M2 spd RESIZE_SCR). apply hpres_weakW. exact HP1. exact HP2.
        -- intros a KA'. eapply L5HP.kept_mono. exact KA'. { intros b Hb. right; right; exact Hb. }
           unfold spd; fsclia. unfold spd; flia.
           intros OW. apply outside2. apply (L5HP.outside_in _ _ X 32 OW). cbn; left; reflexivity.
           intros C. apply (L5HP.outside_in _ _ qX 64 OW). cbn; right; left; reflexivity. generalize C NRLE Hn; clear; intros; lia.
        -- intros b Hb. right; right; exact Hb.
        -- fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKE.
