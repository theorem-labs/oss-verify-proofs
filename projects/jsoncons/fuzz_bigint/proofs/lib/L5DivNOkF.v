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
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivNOkA L5DivNOkB L5DivNOkC L5DivNOkD L5DivNOkE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVNOKF.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVNOKA. Import L5DIVNOKB. Import L5DIVNOKC. Import L5DIVNOKD. Import L5DIVNOKE.

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
Let stage_G4 := @L5DIVNOKE.stage_G4 _ L HI LY HIok KPOS BPOS ASSIGN RESIZE HUGE DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX OLX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 CR KONT KONT3.
Let frame4 := @L5DIVNOKE.frame4 sp bX wX.
Local Ltac slia :=
  match goal with
  | A : 140735332483072 + 8848 <= ?s, B : ?s <= 2 ^ 47, C : ?s <= hl_sptop _ |- _ => generalize A B C SX SDV SRR HX HDV HRR SPTOP; clear; intros; lia
  end.
Local Ltac kcw K H := first [ eapply u64_at_agree1 | eapply u8_at_agree1 | eapply big_at_agree1 ];
  [ intros i Hi; apply K; generalize Hi SX; unfold spd; slia | slia | slia | exactA H ].


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (B0 B1 fd0 fn0 fnum fden : Z) :
  let LBc := (B0, 64) :: (B1, 64) :: LB in
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 X -> getr R (reg 20) = Z_to_bv 64 (sp - 120) ->
  getr R (reg 22) = Z_to_bv 64 B1 -> getr R (reg 23) = Z_to_bv 64 qX -> getr R (reg 24) = Z_to_bv 64 (X + 16) -> getr R (reg 25) = getr R0 (reg 25) ->
  getr R (reg 26) = Z_to_bv 64 0 -> getr R (reg 27) = Z_to_bv 64 rr ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) -> B0 <> B1 ->
  block_range L B1 64 /\ blocks_apart B1 64 LB -> block_range L B0 64 /\ blocks_apart B0 64 ((B1, 64) :: LB) -> crc = debit L (debit L cr 64) 64 ->
  div_saves M sp R0 ->
  L5.u8_at RSEGS M (sp - 232) fd0 -> 0 <= fd0 < 256 -> Z.testbit fd0 0 = false ->
  L5.u64_at RSEGS M (sp - 224) 1 -> L5.u64_at RSEGS M (sp - 216) MWORD -> L5.u64_at RSEGS M (sp - 208) 0 ->
  L5.u8_at RSEGS M (sp - 200) fn0 -> 0 <= fn0 < 256 -> Z.testbit fn0 0 = true ->
  L5.u64_at RSEGS M (sp - 192) (Z.of_nat lenX) -> L5.u64_at RSEGS M (sp - 184) 8 -> L5.u64_at RSEGS M (sp - 176) B0 ->
  L5.big_at RSEGS M (sp - 168) (L5.BO fnum lenX (L5.BDyn 8 B1)) -> Z.testbit fnum 1 = false -> L5.limbs_at RSEGS M B1 wX ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 1 (L5.BInl MWORD 0)) -> Z.testbit fden 1 = false ->
  L5.u64_at RSEGS M (sp - 256) 0 ->
  L5.big_at RSEGS M X bX -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5DS.zero_obj M rr -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR [] M0 M ->
  srealizes RSEGS SCFG (cfg R 0x220bc M model) K.
Proof.
  intros LBc H2 H9 H3 H4 H8 H18 H20 H22 H23 H24 H25 H26 H27 MBV HH NE01 [BR1 BA1] [BR0 BA0] CRC DS
         Fd0 Fd0r Fd0b F224 F216 F208 Fn0 Fn0r Fn0b F192 F184 F176 OBn Fnb1 LAn OBd Fdb1 F256 OBXc DQ DX ZRc DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof nR_le as NRLE. pose proof wX_len as WL. pose proof wX_ok as WO. unfold lenX in NRLE, WL.
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  pose proof (credit_chain L cr KPOS BPOS CR) as (_ & _ & CR3).
  pose proof BR1 as (B1a & B1b & B1c & B1d & B1e).
  pose proof OBn as (N0 & Nr & N8 & Nb0 & N16 & N24 & Nlen & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in N0, Nr, N8, Nb0, N16, N24, Nlen.
  pose proof OBd as (D0 & Dr & D8 & Db0 & D16 & D24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in D0, Dr, D8, Db0, D16, D24.
  assert (WFR: L5.writable RSEGS M (sp - 304) 304).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  unfold cfg.
  pose proof (d5g3_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdG] in P.
  destruct (P ltac:(flia) ltac:(flia) H2 H18 ltac:(flia) A16 WFR) as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A10 & A11 & A12 & A13 & C236)). clear P.
  assert (KFR: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 236 <= i < sp - 232) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1. apply FRZ. exact Hi. generalize N1; clear; intros; lia. }
  assert (Fd0' : L5.u8_at RSEGS M1 (sp - 232) fd0) by kcw KFR Fd0.
  assert (F224' : L5.u64_at RSEGS M1 (sp - 224) 1) by kcw KFR F224.
  assert (F216' : L5.u64_at RSEGS M1 (sp - 216) MWORD) by kcw KFR F216.
  assert (F208' : L5.u64_at RSEGS M1 (sp - 208) 0) by kcw KFR F208.
  assert (Fn0' : L5.u8_at RSEGS M1 (sp - 200) fn0) by kcw KFR Fn0.
  assert (F192' : L5.u64_at RSEGS M1 (sp - 192) (Z.of_nat lenX)) by kcw KFR F192.
  assert (F184' : L5.u64_at RSEGS M1 (sp - 184) 8) by kcw KFR F184.
  assert (F176' : L5.u64_at RSEGS M1 (sp - 176) B0) by kcw KFR F176.
  assert (F256' : L5.u64_at RSEGS M1 (sp - 256) 0) by kcw KFR F256.
  assert (OBX1 : L5.big_at RSEGS M1 X bX) by kcw KFR OBXc.
  assert (ZR1 : L5DS.zero_obj M1 rr) by kcw KFR ZRc.
  assert (MW1 : mword_obj M1 dv fdv). { destruct MWc as [OBv SGv]. split. 2: exact SGv. kcw KFR OBv. }
  assert (DS1 : div_saves M1 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi. apply KFR; generalize Hi; slia. flia. flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG.
    intros a Ha. destruct (Z_le_gt_dec (sp - 236) a) as [C1|C1]; [destruct (Z_lt_le_dec a (sp - 232)) as [C2|C2]|].
    right; left; flia. all: left; apply KFR; flia. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS.
  (* [comment removed for export] *)
  assert (OLd: L5C.obj_limbs RSEGS M1 (L5.BO fden 1 (L5.BInl MWORD 0)) [MWORD]). { split. reflexivity. split. repeat constructor; unfold MWORD; lia. reflexivity. }
  assert (OLn: L5C.obj_limbs RSEGS M1 (L5.BO fnum lenX (L5.BDyn 8 B1)) wX).
  { split. cbn [L5.bo_len]. exact WL. split. exact WO. cbn [L5.bo_st]. eapply L5C.limbs_at_agree. 4: exact LAn. 2: flia. 2: flia.
    intros i Hi. apply KFR. flia. flia. }
  eapply (norm_ok fx1 R1 M1 model K LBc crc (sp - 136) (sp - 168) (sp - 236) spd 0x220d4 (L5.BO fden 1 (L5.BInl MWORD 0)) (L5.BO fnum lenX (L5.BDyn 8 B1)) [MWORD] wX
            HH1 MOK HK0 A11 A12 A13 A1).
  - split. flia. reflexivity.
  - rewrite r2. rewrite (KS 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (KS 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. eapply L5.defined_grows. exact MG. exact SCR0. flia. flia.
  - kcw KFR OBd.
  - exact OLd.
  - cbn [L5.bo_len]. lia.
  - cbn [L5.bo_len nth_w nth Nat.sub]. unfold MWORD. lia.
  - cbn [L5.bo_len]. intros Hx. exfalso. lia.
  - kcw KFR OBn.
  - exact OLn.
  - cbn [L5.bo_len]. lia.
  - cbn [L5.bo_len]. intros Hx. exfalso. lia.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - unfold spd; flia. - flia. - flia.
  - unfold L5NORM.apart. right. lia.
  - eapply defined_agree1. 2:{ eapply L5.defined_sub. exact SCR0. flia. flia. } intros i Hi. apply KFR; flia.
  - eapply defined_agree1. 2:{ eapply L5.defined_sub. exact SCR0. flia. flia. } intros i Hi. apply KFR; flia.
  - pose proof (Z.div_mod sp 16 ltac:(lia)) as E16. rewrite A16, Z.add_0_r in E16. replace (sp - 236) with ((4 * (sp / 16) - 59) * 4) by lia. apply Z_mod_mult.
  - unfold spd; flia. - flia.
  - unfold L5NORM.apart. left. lia. - unfold L5NORM.apart. left. lia.
  - eapply L5.defined_sub. eapply L5.defined_grows. exact MG. exact SCR0. flia. flia.
  - cbn [L5.bo_st]. intros cap q E. discriminate E.
  - cbn [L5.bo_st L5.bo_len]. intros cap q E. injection E. intros <- <-. split. right; left; reflexivity. split. lia. unfold L5NORM.apart. right. flia.
  - intros _. split. { unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite Db0. intros F; discriminate F. } unfold L5.bo_dyn, L5.bo_cap. cbn [L5.bo_fb L5.bo_st L5.bo_len]. intros _. lia.
  - cbn [L5.bo_st]. intros cd qd cn qn E. discriminate E.
  - unfold L5NORM.credits, L5NORM.cnt, L5.bo_dyn. cbn [L5.bo_fb]. rewrite Db0, Nb0. cbn. rewrite CRC. unfold credit_ok, debit in CR3 |- *. cbn [fst snd] in CR3 |- *. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 c gd gn LB2 cr2 POST MBV2 HH2.
    unfold L5NORM.norm_post in POST. cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn] in POST.
    destruct POST as (RP & Hc & Hcr & Hpow & A10' & PX & (std & stn & OAd & OAn) & ELB2 & ECR2 & FBd & FBn & HP2 & GD3 & GN3).
    assert (C0: c = 0). { rewrite Hc. vm_compute. reflexivity. } clear Hc. subst c.
    assert (SHL1: L5SHL.shl_result [MWORD] 0 = [MWORD]) by reflexivity.
    assert (SHLn: L5SHL.shl_result wX 0 = wX) by reflexivity.
    rewrite SHL1 in *. rewrite SHLn in *.
    assert (SEC: L5NORM.second 1 [MWORD] = false) by reflexivity. rewrite SEC in *.
    (* [comment removed for export] *)
    destruct gd as [|Ad cd]. 2:{ exfalso. cbn in GD3. destruct GD3 as [G|G]. lia. discriminate G. }
    destruct gn as [|An cn].
    2:{ exfalso. unfold L5NORM.obj_after in OAn. cbn [L5.bo_fb L5.bo_st L5.bo_dyn] in OAn.
        destruct OAn as (_ & _ & _ & _ & _ & DYF & _). unfold L5.bo_dyn in DYF. cbn [L5.bo_fb] in DYF. rewrite Nb0 in DYF. discriminate DYF. }
    cbn [L5NORM.blocks_of app L5NORM.debits] in ELB2, ECR2. subst LB2 cr2.
    unfold L5NORM.obj_after in OAd, OAn. unfold L5NORM.norm_words in OAd, OAn. rewrite SHL1 in OAd. rewrite SHLn in OAn.
    cbn [L5.bo_fb L5.bo_st length] in OAd, OAn.
    assert (RL1: rlen [MWORD] = 1%nat) by reflexivity. rewrite RL1 in OAd. cbn [Nat.eqb] in OAd.
    destruct OAd as (_ & _ & OBd2 & OLd2 & _ & SAMEd). destruct std as [v0' v1'|cd' qd']. 2: contradiction.
    fold nR in OAn. destruct OAn as (_ & _ & OBn2 & OLn2 & _ & SAMEn). destruct stn as [u0 u1|cn' qn']. contradiction. destruct SAMEn as [-> ->].
    assert (V0: v0' = MWORD). { destruct OLd2 as (_ & _ & Hf). cbn in Hf. injection Hf. intros E. symmetry. exact E. }
    subst v0'.
    set (fnum' := if (nR =? 0)%nat then Z.land fnum 253 else fnum) in OBn2, OLn2.
    assert (FN': 0 <= fnum' < 256 /\ Z.testbit fnum' 0 = true /\ Z.testbit fnum' 1 = false).
    { subst fnum'. destruct (nR =? 0)%nat. 2:{ split. exact Nr. split. exact Nb0. exact Fnb1. }
      split. apply L5.land_byte_range. lia. rewrite !Z.land_spec, Nb0, Fnb1. split; reflexivity. }
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV02.
    unfold L5NORM.norm_W, L5NORM.dyn_area in HP2. cbn [L5.bo_st L5.bo_len app] in HP2.
    (* [comment removed for export] *)
    assert (KA: forall a, spd <= a < 2 ^ 64 -> ~ (sp - 168 <= a < sp - 104) -> ~ (sp - 236 <= a < sp - 232) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha N1 N2. apply (kept_above M1 M2 LBc L5NORM.NORM_SCR _ a HP2). uSCR; clear; lia. exact Ha.
      intros rg [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng; cbn; try (generalize N1 N2; clear; intros; lia).
      unfold spd in Ha. unfold lenX. generalize Ha B1e SLO' LENX; clear; intros; lia. }
    assert (REGS: forall i v, In i cs_all -> In i KS_d5g3 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (KS i Hk). exact Hv. }
    pose proof OBd2 as (_ & _ & E128 & _ & E120 & E112 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in E128, E120, E112.
    pose proof OBn2 as (E168 & _ & E160 & _ & E152 & E144 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in E168, E160, E152, E144.
    apply (stage_G4 fx2 R2 M2 model2 crc B0 B1 fd0 fn0 fnum' fden).
    all: try (eapply REGS; [inl | inl | assumption]).
    + rewrite <- r10. exact A10'.
    + exact MBV02. + exact HH2. + exact NE01. + split; assumption. + split; assumption. + exact CRC.
    + eapply div_saves_kept. 4: exact DS1. intros i Hi. apply KA; generalize Hi; unfold spd; slia. flia. flia.
    + (* [comment removed for export] *)
      unfold frame4, L5DIVNOKE.frame4. repeat match goal with |- _ /\ _ => split end.
      * kcw KA Fd0'. * lia. * lia. * exact Fd0b. * kcw KA F224'. * kcw KA F216'. * kcw KA F208'.
      * kcw KA Fn0'. * lia. * lia. * exact Fn0b. * kcw KA F192'. * kcw KA F184'. * kcw KA F176'.
      * exact E168. * lia. * lia. * exact (proj1 (proj2 FN')). * exact (proj2 (proj2 FN')). * exactA E160. * exactA E152. * exactA E144.
      * exact (proj1 OBd2). * lia. * lia. * exact Db0. * exact Fdb1. * exactA E128. * exactA E120.
      * replace (sp - 112) with (sp - 136 + 24) by lia. eapply (L5KS.u64_at_defined M2 (sp - 136 + 24) v1'). exact E112. unfold L5KS.IMG_HI; flia. flia.
      * exact PX.
      * kcw KA F256'.
    + exact OBn2.
    + destruct OLn2 as (_ & _ & LA2). cbn [L5.bo_st] in LA2. exact LA2.
    + kcw KA OBX1.
    + eapply (cdef_inblock M1 M2 LBc crc _ L5NORM.NORM_SCR _ qX 64 qX 64 HH1 HP2). right; right; exact INQ. lia. lia. eapply L5.defined_grows. exact MG. exact DQ.
    + eapply (cdef_above M1 M2 LBc L5NORM.NORM_SCR _ X 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. eapply L5.defined_grows. exact MG. exact DX.
    + kcw KA ZR1.
    + eapply (cdef_above M1 M2 LBc L5NORM.NORM_SCR _ rr 32 HP2). uSCR; clear; lia. unfold spd; flia. flia. eapply L5.defined_grows. exact MG. exact DR.
    + destruct MW1 as [OBv SGv]. split. 2: exact SGv. kcw KA OBv.
    + (* [comment removed for export] *)
      eapply (L5HP.hpres_trans L LB LBc sp DIV_SCR [] M0 M1 M2 spd L5NORM.NORM_SCR).
      * eapply (L5HP.hpres_trans L LB LB sp DIV_SCR [] M0 M M1 sp DIV_SCR []). exact HP.
        -- eapply (L5HP.hpres_piece L LB sp DIV_SCR [] M M1 (fun a => sp - 236 <= a < sp - 232)).
           ++ intros a Ha Hn'. apply KFR. exact Ha. exact Hn'.
           ++ intros a KA' C. refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
           ++ rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG. exact SCR0.
           ++ exact MG.
        -- intros a KA'; exact KA'. -- intros b Hb; exact Hb. -- fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
      * exact HP2.
      * intros a KA'. eapply L5HP.kept_mono. exact KA'. { intros b Hb. right; right; exact Hb. }
        unfold spd; fsclia. unfold spd; flia.
        intros _. pose proof (L5HP.kept_not_in_scratch L LB sp DIV_SCR [] a KA' (LBhi _ _ _ _ HH0) ltac:(fsclia) ltac:(rewrite IMG; flia)) as NS.
        pose proof (L5C.kept_not_fresh L LB sp DIV_SCR [] a B1 64 KA' BA1 B1b B1e (LBhi _ _ _ _ HH0)) as NB.
        intros rg [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng; cbn; try (generalize NS; clear; uSCR; intros; lia).
        unfold lenX. generalize NB LENX WL; clear; intros; lia.
      * intros b Hb. right; right; exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKF.
