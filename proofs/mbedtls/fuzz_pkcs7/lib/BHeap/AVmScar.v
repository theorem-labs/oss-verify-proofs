(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ AVm AKinvM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AVmScar () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AVm.vst"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vranges_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_unit"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.JW"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_cover"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_hulls"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinvM.scar_site"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.HKv"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"].


Section ARUN_1. Context {hAR : arun}.
Section Scar.
Variable AL : asan_layout.
Hypothesis ASB : al_sb AL = 0x7fff8000.
Hypothesis IMH : al_img_hi AL <= 0x65f000.


#[using="ASB IMH"] Theorem HKv_scar_site : ltac2:(CDefT.buildp (gd_tbl_AVmScar ()) "Pv,$0.PU,$1.Pn,$1.P,(2.VAL,R3.)P,(3.R4.R3.R2.)P,(4.+65?000.R4.)P,(5.(4.(6.R5.R4.)+7???7000.)(4.+10007???8000.R5.))P,(4.$7.R5.)P,Pt,$8.P,(9.$8.R1.(:.R9.))(5.(4.(6.R9.R8.)(;.R2.))(4.(<.R2.)R9.))P,(=.(>.$1.$1.)Lc,(>.$1.$1.)(?.(9.(>.$1.$1.)R1.(10.R:.))(?.(4.(11.$1.$1.R1.)R9.)(4.(6.R9.R8.)(6.(11.$1.$1.R1.)(12.$1.$1.R1.))))))P,(=.(>.$1.$1.)LH,(>.$1.$1.)(?.(9.(>.$1.$1.)R1.(13.R;.))(?.(4.(11.$1.$1.R1.)R:.)(4.(6.R:.R9.)(6.(11.$1.$1.R1.)(12.$1.$1.R1.))))))(14.VhAR,VAL,(15.VAL,R;.)(16.VhAR,VAL,R;.)R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros v U n W HUN U68 UHI NW APT COV HUL. exists (HKh AL v U n). split; [exact (HKh_kinv AL v U n W)|]. split; [exact UHI|]. split; [exact NW|]. split.
  - intros mo K.
    dpose K as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & UC & (UNC & _) & _) & _ & _ & _ & VW & _).
    dpose VW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UW & _).
    dpose (UW U n HUN) as (N0 & U0 & UCE & _). pose proof aceil_bounds as ACB.
    split; [apply covers_map_contains; [lia| lia| lia| exact (UC U n HUN)]|].
    split; [exact (UNC U n HUN APT)|].
    apply (HKh_of_destroy AL v mo U n K ASB IMH HUN); [exact U68| exact UHI| exact APT].
  - intros mh KH. exact (HKv_rereserve AL v mh U n KH ASB IMH HUN U68 UHI APT COV HUL).
Qed.

(* [comment removed for export] *)

#[using="ASB IMH"] Theorem HKv_scar_site_guard : ltac2:(CDefT.buildp (gd_tbl_AVmScar ()) "PP,SpPv,$0.PU,$1.Pn,$1.P,P,R4.(2.VAL,R4.)P,P,R5.(3.R5.R4.R3.)P,(4.+65?000.R4.)P,(5.(4.(6.R5.R4.)+7???7000.)(4.+10007???8000.R5.))P,(4.$7.R5.)P,P,R9.Pt,$8.P,(9.$8.R1.(:.R:.))(5.(4.(6.R:.R9.)(;.R2.))(4.(<.R2.)R:.))P,(=.(>.$1.$1.)Lc,(>.$1.$1.)(?.(9.(>.$1.$1.)R1.(10.R:.))(?.(4.(11.$1.$1.R1.)R9.)(4.(6.R9.R8.)(6.(11.$1.$1.R1.)(12.$1.$1.R1.))))))P,(=.(>.$1.$1.)LH,(>.$1.$1.)(?.(9.(>.$1.$1.)R1.(13.R;.))(?.(4.(11.$1.$1.R1.)R:.)(4.(6.R:.R9.)(6.(11.$1.$1.R1.)(12.$1.$1.R1.))))))(14.VhAR,VAL,(15.VAL,R;.)Lmo,$17.(?.R=.(16.VhAR,VAL,R<.R1.))R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros P v U n W HUN U68 UHI NW APT COV HUL. exists (fun mh => P /\ HKh AL v U n mh). split; [| split; [exact UHI| split; [exact NW| split]]].
  - split.
    + intros mo [HP K]. exact (ki_halted (HKh_kinv AL v U n (W HP)) mo K).
    + intros mo [HP K]. exact (ki_top (HKh_kinv AL v U n (W HP)) mo K).
    + intros mo acc [HP K] OK. ddestruct (ki_mat (HKh_kinv AL v U n (W HP)) mo acc K OK) as (mo' & E & K' & MM). exists mo'. auto.
  - intros mo [HP K].
    dpose K as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & UC & (UNC & _) & _) & _ & _ & _ & VW & _).
    dpose VW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UW & _).
    dpose (UW U n (HUN HP)) as (N0 & U0 & UCE & _). pose proof aceil_bounds as ACB.
    split; [apply covers_map_contains; [lia| lia| lia| exact (UC U n (HUN HP))]|].
    split; [exact (UNC U n (HUN HP) (APT HP))|].
    split; [exact HP|]. apply (HKh_of_destroy AL v mo U n K ASB IMH (HUN HP)); [exact U68| exact UHI| exact (APT HP)].
  - intros mh [HP KH]. destruct (HKv_rereserve AL v mh U n KH ASB IMH (HUN HP) U68 UHI (APT HP) COV HUL) as [RF K']. auto.
Qed.
End Scar.
End ARUN_1.
