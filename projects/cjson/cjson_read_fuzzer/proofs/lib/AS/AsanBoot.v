(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymExec3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanCore.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesWJoin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanStartupCertB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlanAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHSAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanStartupCertDefs.
From Ltac2 Require Ltac2.
From Ltac2 Require Constr.
From Ltac2 Require Std.
From Ltac2 Require Control.
Module AsanStartupCertB1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertB.AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITB1 : itab := mk_itab_ranges ASEGS [(0x3e7d0, 24%nat); (0x49400, 40%nat); (0x4a2f0, 6632%nat); (0x52fd0, 92%nat); (0x540f0, 24%nat); (0x54310, 28%nat); (0x54450, 16%nat); (0x55650, 8%nat); (0x5ad10, 32%nat); (0x5b270, 56%nat); (0x5b790, 20%nat); (0x5c200, 12%nat); (0x601a0, 16%nat); (0x601f0, 8%nat); (0x61ef0, 16%nat); (0x62600, 8%nat); (0x62640, 8%nat); (0x62910, 48%nat); (0x62af0, 16%nat); (0x63140, 16%nat); (0x66000, 20%nat); (0x66e30, 80%nat); (0x67490, 8%nat); (0x676e0, 68%nat); (0x683d0, 24%nat); (0x68520, 16%nat); (0x68b90, 12%nat); (0x6d310, 12%nat); (0x6d350, 8%nat); (0x6d520, 8%nat); (0x6e420, 8%nat); (0x8d5c0, 32%nat); (0x8d660, 28%nat); (0x8d7c0, 12%nat)]%Z.
Lemma ITB1_ok : itab_sound ASEGS ITB1.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition NXB1 : nat := 207%nat.
Lemma NXB1_ge : (NX0 <= NXB1)%nat. Proof. unfold NX0, NXB1. lia. Qed.
Definition startup_shapeB1 : shape := SHole 13.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certB1 :
  check ASEGS ITB1 ASAN NXB1 AsanInit.LIMIT (XNS ASEGS ASAN NXB1 AsanInit.LIMIT) XE0 XB0 HS_asanB1 KC0 BFUEL FUEL None HS_asanA_10 startup_plan_segA = COk startup_shapeB1.
Proof. Time (vm_cert_refl constr:(COk startup_shapeB1)). Time Qed.
End AsanStartupCertB1.

(* [comment removed for export] *)
Module AsanStartupCertC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertB.AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITC : itab := mk_itab_ranges ASEGS [(0x3cc80, 40%nat); (0x55670, 44%nat); (0x557d0, 12%nat); (0x558a0, 40%nat); (0x559d0, 24%nat); (0x567d0, 16%nat); (0x5dcb0, 48%nat); (0x5de10, 20%nat); (0x5df00, 12%nat); (0x5df50, 24%nat); (0x5e070, 28%nat); (0x5e1b0, 12%nat); (0x5e200, 36%nat); (0x5e330, 24%nat); (0x5e430, 28%nat); (0x5e560, 24%nat); (0x5e5d0, 24%nat); (0x61f30, 16%nat); (0x66000, 20%nat); (0x676f0, 44%nat); (0x678a0, 20%nat); (0x683d0, 24%nat); (0x68520, 16%nat); (0x6b710, 8%nat); (0x6e130, 48%nat); (0x6e240, 16%nat); (0x6e740, 24%nat); (0x6e850, 44%nat); (0x9b5e4, 8%nat); (0x9cee4, 16%nat)]%Z.
Lemma ITC_ok : itab_sound ASEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition NXC : nat := 344%nat.
Lemma NXC_ge : (NX0 <= NXC)%nat. Proof. unfold NX0, NXC. lia. Qed.
Definition startup_shapeC : shape := SCase (EVar 6) 10 (SCase (EVar 10) 0 (SHole 14) (SHole 14)) (SCase (EVar 10) 6 (SHole 14) (SHole 14)).
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certC :
  check ASEGS ITC ASAN NXC AsanInit.LIMIT (XNS ASEGS ASAN NXC AsanInit.LIMIT) XE0 XB0 HS_asanC KC0 BFUEL FUEL None HS_asanB_11 startup_plan_segB = COk startup_shapeC.
Proof. Time (vm_cert_refl constr:(COk startup_shapeC)). Time Qed.
End AsanStartupCertC.

(* [comment removed for export] *)
Module AsanStartupCertD.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertB.AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITD : itab := mk_itab_ranges ASEGS [(0x30ce0, 8%nat); (0x53c00, 20%nat); (0x55670, 28%nat); (0x558a0, 12%nat); (0x558f0, 16%nat); (0x559d0, 24%nat); (0x567d0, 16%nat); (0x5a580, 12%nat); (0x5b200, 16%nat); (0x5b3f0, 20%nat); (0x5b770, 16%nat); (0x5c210, 8%nat); (0x5d130, 40%nat); (0x5dc90, 12%nat); (0x5df00, 8%nat); (0x60050, 28%nat); (0x60110, 20%nat); (0x61ef0, 16%nat); (0x62600, 8%nat); (0x62640, 8%nat); (0x65790, 8%nat); (0x65800, 8%nat); (0x658c0, 20%nat); (0x65960, 12%nat); (0x66000, 20%nat); (0x676f0, 64%nat); (0x67870, 12%nat); (0x678c0, 12%nat); (0x683d0, 24%nat); (0x68520, 16%nat); (0x6a790, 20%nat); (0x6a7f0, 16%nat); (0x6a9d0, 12%nat); (0x6aa20, 40%nat); (0x6aad0, 28%nat); (0x6ac70, 24%nat); (0x81c00, 84%nat); (0x81ea0, 12%nat); (0x82540, 8%nat); (0x8da40, 16%nat); (0x8daf0, 8%nat); (0x8e564, 8%nat); (0x8e594, 8%nat); (0x8f504, 24%nat); (0x8f574, 24%nat); (0x8f5e4, 124%nat); (0x8fae4, 56%nat); (0x8fd24, 164%nat); (0x900c4, 156%nat); (0x903a4, 108%nat); (0x92c14, 84%nat); (0x9b5e4, 8%nat); (0x9bb14, 8%nat); (0x9bd04, 8%nat); (0x9bd94, 12%nat); (0x9bea4, 36%nat); (0x9cee4, 16%nat); (0x9dea4, 28%nat)]%Z.
Lemma ITD_ok : itab_sound ASEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition NXD : nat := 394%nat.
Lemma NXD_ge : (NX0 <= NXD)%nat. Proof. unfold NX0, NXD. lia. Qed.
Definition startup_shapeD : shape := SCase (EVar 5) 524277 (SHole 0) (SHole 0).
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certD :
  check ASEGS ITD ASAN NXD AsanInit.LIMIT (XNS ASEGS ASAN NXD AsanInit.LIMIT) XE0 XB0 HS_asanD KC0 BFUEL FUEL None HS_asanQ_12 startup_plan_segC = COk startup_shapeD.
Proof. Time (vm_cert_refl constr:(COk startup_shapeD)). Time Qed.
End AsanStartupCertD.

(* [comment removed for export] *)
Module AsanStartupCertQ.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertB.AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITQ : itab := mk_itab_ranges ASEGS [(0x3cd00, 20%nat); (0x3d440, 20%nat); (0x42520, 8%nat); (0x483e0, 40%nat); (0x53130, 8%nat); (0x53b00, 72%nat); (0x567d0, 16%nat); (0x568e0, 12%nat); (0x56950, 12%nat); (0x56990, 8%nat); (0x5b3d0, 16%nat); (0x5b490, 20%nat); (0x5b9f0, 12%nat); (0x5bcd0, 8%nat); (0x5dc90, 12%nat); (0x5e0c0, 16%nat); (0x5e480, 16%nat); (0x5e6c0, 32%nat); (0x5f860, 8%nat); (0x61ef0, 16%nat); (0x66000, 20%nat); (0x67780, 28%nat); (0x6b3c0, 40%nat); (0x6b4c0, 12%nat); (0x6b580, 28%nat); (0x6c730, 48%nat); (0x6c860, 88%nat); (0x7c4c0, 20%nat); (0x7c550, 16%nat); (0x8ee44, 8%nat); (0x8f504, 44%nat); (0x8f7d4, 20%nat); (0x8f834, 12%nat); (0x8f8b4, 12%nat); (0x8f9c4, 24%nat); (0x8fa94, 12%nat); (0x8fad4, 12%nat); (0x8fb44, 32%nat); (0x8fd24, 12%nat); (0x9b1e4, 8%nat); (0x9be34, 32%nat); (0x9cee4, 16%nat)]%Z.
Lemma ITQ_ok : itab_sound ASEGS ITQ.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition NXQ : nat := 378%nat.
Lemma NXQ_ge : (NX0 <= NXQ)%nat. Proof. unfold NX0, NXQ. lia. Qed.
Definition startup_shapeQ : shape := SCase e_atr8 17592186044384 (SHole 12) (SCase e_atr8 17592186044385 (SHole 12) (SCase e_atr8 17592186044386 (SHole 12) (SCase e_atr8 17592186044387 (SHole 12) (SCase e_atr8 17592186044388 (SHole 12) (SCase e_atr8 17592186044389 (SHole 12) (SCase e_atr8 17592186044390 (SHole 12) (SHole 12))))))).
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certQ :
  check ASEGS ITQ ASAN NXQ AsanInit.LIMIT (XNS ASEGS ASAN NXQ AsanInit.LIMIT) XE0 XB0 HS_asanQ KC0 BFUEL FUEL None HS_asanC_14 startup_plan_segQ = COk startup_shapeQ.
Proof. Time (vm_cert_refl constr:(COk startup_shapeQ)). Time Qed.
End AsanStartupCertQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import PropExec ShapeAlg SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanNodesWJoin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanStartupCertB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertB.AsanStartup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StartupPlanAsan StartupHSAsan AsanStartupCertDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanStartupCertB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertB.AsanStartupCert.
Import AsanStartupCertB1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanStartupCertB.
Import AsanStartupCertC.
Import AsanStartupCertQ.
Import AsanStartupCertD.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StartupPlan2Asan StartupHS2Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanStartupCertB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertB.AsanStartupCert2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => holes_only a && holes_only b
  | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Section Boot.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.   (* [comment removed for export] *)
  Variable abt : bool.
  (* [comment removed for export] *)
  Variable ifs : Fs.Fs.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Hypothesis Hfs : fs = fs_seed_tmp ifs tmp.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (AsanInit.E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt ASEGS ASAN LIM HS_asan2 SINV argH (fun _ => H) fs.

  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AH2 := argH0_high2 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  (* [comment removed for export] *)
  Definition HH (h : nat) (E : env) (fs' : Fs.Fs) : TSet := H E fs'.
  Lemma HH_agree : forall h E E' fs', env_agree NX0 E E' -> HH h E fs' = HH h E' fs'.
  Proof. intros. unfold HH. apply H_agree. assumption. Qed.
  Lemma HH_nil : forall h E fs', HH h E fs' [].
  Proof. intros. unfold HH. apply H_nil. Qed.

  (* [comment removed for export] *)
  Lemma sd_allH : forall E fs' s, holes_only s = true -> t_eq (sd HH t_nil E fs' s) (H E fs').
  Proof.
    assert (ID : forall X Y Z : TSet, Z [] -> t_eq X Z -> t_eq Y Z -> t_eq (t_alt2 X Y) Z).
    { intros X Y Z HZ HX HY tr. unfold t_alt2. specialize (HX tr). specialize (HY tr). tauto. }
    intros E fs' s. induction s as [| |fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros Hs; try discriminate.
    - apply andb_prop in Hs as [Ha Hb]. apply ID; [apply H_nil | exact (IHa Ha) | exact (IHb Hb)].
    - apply andb_prop in Hs as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha) | exact (IHb Hb)].
    - unfold HH. apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Section Seg.
    Variable nx : nat.
    Hypothesis Hnx : (NX0 <= nx)%nat.
    Lemma env_agree_nx : forall E E', env_agree nx E E' -> env_agree NX0 E E'.
    Proof. intros E E' [Hag Hb]. split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.
    Let AAn : forall E E' (a : word), env_agree nx E E' -> argH E a = argH E' a :=
      fun E E' a Hag => AA E E' a (env_agree_nx E E' Hag).
    Let SAn : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M :=
      fun E E' M Hag => SA E E' M (env_agree_nx E E' Hag).

    (* [comment removed for export] *)
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound ASEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt ASEGS ASAN LIM HSn SINV argH HH fs ->
      check ASEGS IT ASAN nx LIM (XNS ASEGS ASAN nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
        srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound ASEGS IT IT_ok ASAN nx Hnx LIM HSn (XNS ASEGS ASAN nx LIM) XE0 XB0
                asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                (AsanNodesMmB.node_sys_sound ASEGS ASAN nx LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL ASEGS ASAN nx LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH fs)
                (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M HH0 => HH0) SF nx Hnx SAn)
                (node_join_sound ASEGS ASAN nx LIM SINV argH fs)
                (XNS_sound ASEGS ASAN nx LIM SINV argH fs AAn SAn asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH fs E start R FULL model ->
         srealizes ASEGS (cfg_of ASEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt ASEGS ASAN LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt ASEGS ASAN LIM HS_asanD SINV argH HH fs.
  Proof.
    apply (seg_holes HS_asanD 0%nat HS_asanD_0).
    { intros h ch Hh. unfold HS_asanD in Hh. do 0 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXS2 NXS2_ge IT2 IT2_ok HS_asan2 FUEL BFUEL KC0 startup2_plan HS_asanD_0 startup2_shape); [| exact startup2_cert | reflexivity].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt ASEGS ASAN LIM HS_asanQ SINV argH HH fs.
  Proof.
    apply (seg_holes HS_asanQ 12%nat HS_asanQ_12).
    { intros h ch Hh. unfold HS_asanQ in Hh. do 12 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXD NXD_ge ITD ITD_ok HS_asanD FUEL BFUEL KC0 startup_plan_segC HS_asanQ_12 startup_shapeD); [exact S2_sound | exact startup_certD | reflexivity].
  Qed.
  Lemma Q_sound : holes_stmt ASEGS ASAN LIM HS_asanC SINV argH HH fs.
  Proof.
    apply (seg_holes HS_asanC 14%nat HS_asanC_14).
    { intros h ch Hh. unfold HS_asanC in Hh. do 14 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXQ NXQ_ge ITQ ITQ_ok HS_asanQ FUEL BFUEL KC0 startup_plan_segQ HS_asanC_14 startup_shapeQ); [exact D_sound | exact startup_certQ | reflexivity].
  Qed.
  Lemma C_sound : holes_stmt ASEGS ASAN LIM HS_asanB SINV argH HH fs.
  Proof.
    apply (seg_holes HS_asanB 11%nat HS_asanB_11).
    { intros h ch Hh. unfold HS_asanB in Hh. do 11 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXC NXC_ge ITC ITC_ok HS_asanC FUEL BFUEL KC0 startup_plan_segB HS_asanB_11 startup_shapeC); [exact Q_sound | exact startup_certC | reflexivity].
  Qed.
  Lemma B_sound : holes_stmt ASEGS ASAN LIM HS_asanB1 SINV argH HH fs.
  Proof.
    apply (seg_holes HS_asanB1 13%nat HS_asanB1_13).
    { intros h ch Hh. unfold HS_asanB1 in Hh. do 13 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXB NXB_ge ITB ITB_ok HS_asanB FUEL BFUEL KC0 startup_plan_segB1 HS_asanB1_13 startup_shapeB); [exact C_sound | exact startup_certB | reflexivity].
  Qed.
  Lemma B1_sound : holes_stmt ASEGS ASAN LIM HS_asanA SINV argH HH fs.
  Proof.
    apply (seg_holes HS_asanA 10%nat HS_asanA_10).
    { intros h ch Hh. unfold HS_asanA in Hh. do 10 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXB1 NXB1_ge ITB1 ITB1_ok HS_asanB1 FUEL BFUEL KC0 startup_plan_segA HS_asanA_10 startup_shapeB1); [exact B_sound | exact startup_certB1 | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Theorem asan_boot_shape :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp))
              (sd HH t_nil E0a fs startup_shape).
  Proof.
    exact (asan_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt ifs urnd tmp Hfs Hsp Hbrk Hva Hve Hfit Huid Hhw
             IT0 IT0_ok HS_asanA startup_plan startup_shape KC0 BFUEL FUEL startup_cert HH HH_agree HH_nil B1_sound).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_boot :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp))
              (H E0a fs).
  Proof. eapply srz_conseq; [exact asan_boot_shape | apply sd_allH; reflexivity]. Qed.
End Boot.
