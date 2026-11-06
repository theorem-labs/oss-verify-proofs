(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core L5DefsA L5CoreAS8 L5StepARS8 HeapIfaceAEx L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA PmSpecsA PeSpecsAa PmModelFactsA PeStepA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeACHarnessStmts PeACHarnessKit PeACHarnessKit2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAHK5.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation RSEGS := Asan.M.loaded_segments.

Lemma iosb_revptr (M1 M2 : word -> option byte) o vp vp' rdb st :
  PM.iosb_at RSEGS AD PMSPA.accA M1 o vp rdb st -> L5.u64_at RSEGS M2 o vp' ->
  L5C.agree_on M1 M2 (o + 8) 144 -> PMFA.agsh M1 M2 o 152 -> L5.defined M2 o 8 -> 0 <= o -> o + 152 <= 2 ^ 64 ->
  PM.iosb_at RSEGS AD PMSPA.accA M2 o vp' rdb st.
Proof.
  intros (H0 & H32 & H36 & H40 & H48 & Z & D & C & ST) U AG SH D8 Ho Ho'.
  split; [exact U|]. split; [apply (PEAHK.u32_agree M1 M2 (o + 32) st); [intros i Hi; apply AG; lia| lia| lia| exact H32]|].
  split; [apply (PEAHK.u32_agree M1 M2 (o + 36) 0); [intros i Hi; apply AG; lia| lia| lia| exact H36]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M2 (o + 40) rdb); [intros i Hi; apply AG; lia| lia| lia| exact H40]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M2 (o + 48) _); [intros i Hi; apply AG; lia| lia| lia| exact H48]|].
  split; [apply (PMF.zeros_at_agree M1 M2); [intros i Hi; apply AG; lia| exact Z]|].
  split; [intros i Hi; destruct (Z.lt_ge_cases i 8) as [Y|Y]; [apply (D8 i); lia| rewrite AG by lia; apply (D i Hi)]|].
  split; [apply (PMFA.accA_agree M1 M2 o 152 SH C)| exact ST].
Qed.

Definition hfin (F : Z) (M : word -> option byte) (s : PM.vstr) (st : Z) : Prop :=
  PM.vstr_at RSEGS PMSPA.accA M (F + 32) s /\ L5.u64_at RSEGS M (F + 120) (pa_classic_imp AD)
  /\ PM.iosb_at RSEGS AD PMSPA.accA M (F + 216) (pa_vp_iss_ios AD) (F + 112) st.

Section K.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Section Objs.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : PEAHK2.hf F.
Variables (slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte).
Hypothesis S1 : ahl_ceil ar <= slo.
Hypothesis S2 : BIGSHADOW_HI <= slo.
Hypothesis FR : forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Hypothesis WP : PEAHK2.pfoot F slo shi Wp.
Let oav := PEAHK2.oav Wp.

Lemma hfin_piece s st : incl (PM.vs_own s) LBx -> oav (F + 32) 24 -> oav (F + 120) 8 -> oav (F + 216) 152 -> hfin F M1 s st -> hfin F M2 s st.
Proof.
  intros INC O1 O2 O3 (VS & LC & IO). pose proof HFF as (F8 & F0 & F1 & FB).
  assert (AG2 : PMFA.agA M1 M2 (F + 120) 8) by (apply (PEAHK.agA_frame M1 M2 Wp (F + 120) 8 FR); [lia| lia| exact O2]).
  assert (AG3 : PMFA.agA M1 M2 (F + 216) 152) by (apply (PEAHK.agA_frame M1 M2 Wp (F + 216) 152 FR); [lia| lia| exact O3]).
  split; [|split].
  - apply (PEAHK2.vstr_keep_piece L ar C SCFG HI HIok LBx FFx LKx crx Ax Mx Vx F rs HH HF HFF slo shi Wp M1 M2 S1 S2 FR WP (F + 32) s); [exact INC| lia| lia| exact O1| exact VS].
  - apply (PEAHK2.u64_agA M1 M2 (F + 120) 8 (F + 120) _ AG2); [lia| lia| lia| lia| exact LC].
  - apply (PMFA.iosb_at_agreeA RSEGS AD M1 M2 (F + 216)); [lia| lia| exact AG3| exact IO].
Qed.
End Objs.

Section ObjsC.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : PEAHK2.hf F.
Variables (LBc : list (Z * Z)) (FFc : list fframe) (spc scrc : Z) (Wc : list L5.range) (M1 M2 : word -> option byte) (f : fframe).
Hypothesis AH : L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2.
Hypothesis WF : PEAHK2.wfi F Wc.
Hypothesis Hf : In f FFc.
Hypothesis HfF : ff_addr f = F /\ ff_bytes (ff_class f) = 2048.
Let ffc := PEAHK2.ffc L ar F HFF LBc FFc spc scrc Wc M1 M2 f AH WF Hf HfF.

Lemma hfin_callee s st : incl (PM.vs_own s) LBx -> incl (PM.vs_own s) LBc -> PEAHK2.wapart Wc (F + 32) 24 -> PEAHK2.wapart Wc (F + 120) 8 -> PEAHK2.wapart Wc (F + 216) 152 ->
  hfin F M1 s st -> hfin F M2 s st.
Proof.
  intros INC INCc O1 O2 O3 (VS & LC & IO). pose proof HFF as (F8 & F0 & F1 & FB).
  pose proof (ffc (F + 120) 8 ltac:(lia) ltac:(lia) O2) as AG2. pose proof (ffc (F + 216) 152 ltac:(lia) ltac:(lia) O3) as AG3.
  split; [|split].
  - apply (PEAHK2.vstr_keep_callee L ar C SCFG HI LY HIok LBx FFx LKx crx Ax Mx Vx F rs HH HF HFF LBc FFc spc scrc Wc M1 M2 f AH WF Hf HfF (F + 32) s);
      [exact INC| exact INCc| lia| lia| exact O1| exact VS].
  - apply (PEAHK2.u64_agA M1 M2 (F + 120) 8 (F + 120) _ AG2); [lia| lia| lia| lia| exact LC].
  - apply (PMFA.iosb_at_agreeA RSEGS AD M1 M2 (F + 216)); [lia| lia| exact AG3| exact IO].
Qed.
End ObjsC.
End K.
End PEAHK5.
