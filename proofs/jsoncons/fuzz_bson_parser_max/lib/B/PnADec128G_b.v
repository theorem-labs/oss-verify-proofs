(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128P1_b PnADec128E_b PnADec128S_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADG.
Import L5A. Import L5CA. Import L5SAR. Import PNADK. Import PNADE. Import PNADS.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Lemma bax_add_warm ax : PNST.bax_dec ax = true -> PNST.bax_add_dec ax = ax.
Proof. destruct ax; cbn; intros H; first [reflexivity | discriminate]. Qed.
Definition RGD : list nat := [2; 3; 4; 8; 9; 19; 20; 23; 24; 26; 27]%nat.
Lemma rgd_keep E R R' : rgd E R -> (forall j, In j RGD -> getr R' (reg j) = getr R (reg j)) -> rgd E R'.
Proof.
  intros ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20 & Q24) KS. unfold rgd, PNADD.RBA.
  rewrite !KS by (unfold RGD; cbn [In]; tauto). repeat split; assumption.
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Definition cold_stmt : Prop :=
  forall (E : dve), dkc L ar HI E -> PNST.bax_dec (vax E) = false ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    dsg L ar HI E (vax E) Mc modelc LKc Ac -> rgd E Rc ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb3fac Mc modelc) (vK E).

(* [comment removed for export] *)
Lemma warm_step E (X : dkc L ar HI E) axc (fx : FPState) Rc Mc modelc LKc Ac (pc0 pc1 : Z) :
  dsg L ar HI E axc Mc modelc LKc Ac -> rgd E Rc ->
  (exists fx' R' M1v, (forall i : Z, 0 <= i < 2 ^ 64 -> M1v (Z_to_bv 64 i) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 i))
       /\ msteps RSEGS (st fx Rc pc0 (mrestrict (ahid Ac modelc) Mc)) (st fx' R' pc1 M1v)
       /\ (forall j, In j RGD -> getr R' (reg j) = getr Rc (reg j))) ->
  (forall fx' R' M3 model3, dsg L ar HI E axc M3 model3 LKc Ac -> rgd E R' -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' pc1 M3 model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc pc0 Mc modelc) (vK E).
Proof.
  intros ST RG (fx' & R' & M1v & FRZ & MS & KS) KONT.
  assert (E1 : M1v = mrestrict (ahid Ac modelc) Mc) by (apply L5SAR.mem_eq_of_agree; exact FRZ). subst M1v.
  apply (PNADK.dg_piece L ar C HI LY HIok E X axc fx fx' Rc R' pc0 pc1 Mc modelc LKc Ac (mrestrict (ahid Ac modelc) Mc) (fun _ => False) ST MS).
  - intros x Hx. exact Hx.
  - intros a Ha _. reflexivity.
  - intros a [].
  - intros M3 model3 ST3 HID3 VIS3 FR3. apply (KONT fx' R' M3 model3 ST3). exact (rgd_keep E Rc R' RG KS).
Qed.

Theorem guards : at_b2 L ar HI -> cold_stmt -> PNADE.at_guards L ar HI.
Proof.
  intros B2 COLD E X fx Rc Mc modelc LKc Ac ST RG.
  destruct (PNST.bax_dec (vax E)) eqn:WARM; [| exact (COLD E X WARM fx Rc Mc modelc LKc Ac ST RG)].
  rewrite <- (bax_add_warm (vax E) WARM) in ST.
  assert (GST : forall fx0 R0 M0 model0, dsg L ar HI E (PNST.bax_add_dec (vax E)) M0 model0 LKc Ac -> rgd E R0 -> forall (pc0 pc1 g : Z), (g = 6759136 \/ g = 6759168) ->
            (forall V, 0 <= V 2%nat < 2 ^ 64 -> 0 <= V 33%nat < 2 ^ 64 -> 0 <= V 34%nat < 2 ^ 64 -> 0 <= V 46%nat < 2 ^ 64 -> 0 <= V 50%nat < 2 ^ 64 ->
               getr R0 (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R0 (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R0 (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) ->
               getr R0 (reg 19) = Z_to_bv 64 2147450880 -> getr R0 (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R0 (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) ->
               getr R0 (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R0 (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R0 (reg 27) = Z_to_bv 64 (V 50%nat) ->
               140735332487296 <= (V 2%nat) <= 140737488355328 -> (V 2%nat) mod 32 = 0 -> L5.writable RSEGS (mrestrict (ahid Ac model0) M0) ((V 2%nat) - 256) 256 ->
               L5.u8_at RSEGS (mrestrict (ahid Ac model0) M0) g (V 46%nat) -> 0 <= (V 46%nat) <= 1 ->
               exists fx' R' M', mem_grows (mrestrict (ahid Ac model0) M0) M' /\ (forall a : word, M' a = (mrestrict (ahid Ac model0) M0) a)
                 /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = (mrestrict (ahid Ac model0) M0) (Z_to_bv 64 i))
                 /\ ((msteps RSEGS (st fx0 R0 pc0 (mrestrict (ahid Ac model0) M0)) (st fx' R' pc1 M') /\ (forall x, In x RGD -> getr R' (reg x) = getr R0 (reg x)) /\ 1 <= (((V 46%nat) - 0) mod 2 ^ 64))
                     \/ ((((V 46%nat) - 0) mod 2 ^ 64) < 1))) ->
            (forall fx' R' M3 model3, dsg L ar HI E (PNST.bax_add_dec (vax E)) M3 model3 LKc Ac -> rgd E R' -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' pc1 M3 model3) (vK E)) ->
            srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx0 R0 pc0 M0 model0) (vK E)).
  { intros fx0 R0 M0 model0 ST0 RG0 pc0 pc1 g Hg P KONT.
    dgeom L ar HI E X. gfacts L ar C HI LY HIok E X ST0.
    pose proof RG0 as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20 & Q24). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
    pose proof ST0 as (_ & _ & _ & _ & _ & _ & ERR & _). pose proof ERR as (_ & DEC & _). rewrite bax_dec_add in DEC.
    cbn [PNST.bdec_ok PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC. destruct DEC as (GI & GN & _).
    assert (GV : L5.u8_at RSEGS (mrestrict (ahid Ac model0) M0) g 1).
    { destruct Hg as [-> | ->].
      - apply (proj2 (L5A.u8_at_vis (ahid Ac model0) M0 6759136 1 (VIV 6759136 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))). exact GI.
      - apply (proj2 (L5A.u8_at_vis (ahid Ac model0) M0 6759168 1 (VIV 6759168 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))). exact GN. }
    specialize (P (fun j => match j with 2%nat => vsp E | 33%nat => vfirst E | 34%nat => vvp E | 46%nat => 1 | 50%nat => vF E | _ => 0 end)).
    cbn beta iota in P.
    specialize (P RGs RGf RGv ltac:(clear; lia) RGF Q2 Q8 Q9 Q19 Q20 Q23 Q24 Q26 Q27 SR GS32 MWS GV ltac:(clear; lia)).
    destruct P as (fx' & R' & M' & _ & _ & FRZ & [(MS & KS & _)|C1]); [| exfalso; change ((1 - 0) mod 2 ^ 64) with 1 in C1; clear - C1; lia].
    apply (warm_step E X _ fx0 R0 M0 model0 LKc Ac pc0 pc1 ST0 RG0); [| exact KONT].
    exists fx', R', M'. split; [exact FRZ|]. split; [exact MS| exact KS]. }
  apply (GST fx Rc Mc modelc ST RG 0xb3fac 0xb3fbc 6759136 (or_introl eq_refl)).
  { intros V V2 V33 V34 V46 V50 A2 A8 A9 A19 A20 A23 A24 A26 A27 S1 S32 WR GB G01.
    destruct (PNADP1.adkG1_conc fx Rc _ V V2 V33 V34 V46 V50 A2 A8 A9 A19 A20 A23 A24 A26 A27 S1 S32 WR GB G01) as (fx' & R' & M' & MG & FA & FRZ & [(MS & KS & _ & C1)|(_ & _ & _ & C1)]).
    - exists fx', R', M'. split; [exact MG|]. split; [exact FA|]. split; [exact FRZ|]. left. split; [exact MS|]. split; [| exact C1].
      intros x Hx. apply KS. revert x Hx. apply (L5K.incl_b RGD). vm_compute. reflexivity.
    - exists fx', R', M'. split; [exact MG|]. split; [exact FA|]. split; [exact FRZ|]. right. exact C1. }
  intros fx1 R1 M1 model1 ST1 RG1.
  apply (GST fx1 R1 M1 model1 ST1 RG1 0xb3fbc 0xb3fcc 6759168 (or_intror eq_refl)).
  { intros V V2 V33 V34 V46 V50 A2 A8 A9 A19 A20 A23 A24 A26 A27 S1 S32 WR GB G01.
    destruct (PNADP1.adkG2_conc fx1 R1 _ V V2 V33 V34 V46 V50 A2 A8 A9 A19 A20 A23 A24 A26 A27 S1 S32 WR GB G01) as (fx' & R' & M' & MG & FA & FRZ & [(MS & KS & _ & C1)|(_ & _ & _ & C1)]).
    - exists fx', R', M'. split; [exact MG|]. split; [exact FA|]. split; [exact FRZ|]. left. split; [exact MS|]. split; [| exact C1].
      intros x Hx. apply KS. revert x Hx. apply (L5K.incl_b RGD). vm_compute. reflexivity.
    - exists fx', R', M'. split; [exact MG|]. split; [exact FA|]. split; [exact FRZ|]. right. exact C1. }
  intros fx2 R2 M2 model2 ST2 RG2. exact (B2 E X fx2 R2 M2 model2 LKc Ac ST2 RG2).
Qed.

End WithHeap.
End SCFG_1.
End PNADG.
