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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesWJoin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlanBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHSBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertDefs.
From Ltac2 Require Ltac2.
From Ltac2 Require Constr.
From Ltac2 Require Std.
From Ltac2 Require Control.
Module BothStartupCertB1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITB1 : itab := mk_itab_ranges BSEGS [(0x3e800, 24%nat); (0x49430, 36%nat); (0x4a320, 6628%nat); (0x53000, 92%nat); (0x54120, 8%nat); (0x54150, 8%nat); (0x54340, 28%nat); (0x54480, 16%nat); (0x55670, 12%nat); (0x5ad40, 32%nat); (0x5b2a0, 56%nat); (0x5b7c0, 20%nat); (0x5c230, 12%nat); (0x601d0, 16%nat); (0x60220, 8%nat); (0x61f10, 20%nat); (0x62620, 8%nat); (0x62670, 8%nat); (0x62930, 52%nat); (0x62b20, 16%nat); (0x63170, 12%nat); (0x66030, 16%nat); (0x66e60, 68%nat); (0x66f80, 8%nat); (0x674c0, 8%nat); (0x67710, 68%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x68bc0, 8%nat); (0x6d340, 24%nat); (0x6d550, 8%nat); (0x6e450, 8%nat); (0x8cd40, 32%nat); (0x8cde0, 28%nat); (0x8cf40, 12%nat)]%Z.
Lemma ITB1_ok : itab_sound BSEGS ITB1.
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
  check BSEGS ITB1 BOTH NXB1 AsanInit.LIMIT (XNS BSEGS BOTH NXB1 AsanInit.LIMIT) XE0 XB0 HS_bothB1 KC0 BFUEL FUEL None HS_bothA_10 startup_plan_both_segA = COk startup_shapeB1.
Proof. Time (vm_cert_refl constr:(COk startup_shapeB1)). Time Qed.
End BothStartupCertB1.

(* [comment removed for export] *)
Module BothStartupCertC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITC : itab := mk_itab_ranges BSEGS [(0x3ccb0, 40%nat); (0x556a0, 44%nat); (0x55800, 12%nat); (0x558d0, 40%nat); (0x55a00, 20%nat); (0x56800, 12%nat); (0x5dcd0, 24%nat); (0x5dd40, 20%nat); (0x5de40, 16%nat); (0x5df30, 12%nat); (0x5df70, 28%nat); (0x5e090, 32%nat); (0x5e1e0, 12%nat); (0x5e220, 40%nat); (0x5e360, 24%nat); (0x5e460, 28%nat); (0x5e590, 24%nat); (0x5e600, 20%nat); (0x61f60, 16%nat); (0x66030, 20%nat); (0x67720, 44%nat); (0x678d0, 20%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x6b730, 12%nat); (0x6e160, 48%nat); (0x6e270, 16%nat); (0x6e770, 24%nat); (0x6e880, 24%nat); (0x6e8f0, 16%nat); (0x9ad64, 8%nat); (0x9c664, 16%nat)]%Z.
Lemma ITC_ok : itab_sound BSEGS ITC.
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
  check BSEGS ITC BOTH NXC AsanInit.LIMIT (XNS BSEGS BOTH NXC AsanInit.LIMIT) XE0 XB0 HS_bothC KC0 BFUEL FUEL None HS_bothB_11 startup_plan_both_segB = COk startup_shapeC.
Proof. Time (vm_cert_refl constr:(COk startup_shapeC)). Time Qed.
End BothStartupCertC.

(* [comment removed for export] *)
Module BothStartupCertD.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITD : itab := mk_itab_ranges BSEGS [(0x30d10, 8%nat); (0x53c30, 20%nat); (0x55680, 36%nat); (0x558d0, 12%nat); (0x55920, 16%nat); (0x55a00, 20%nat); (0x56800, 12%nat); (0x5a5a0, 16%nat); (0x5b230, 16%nat); (0x5b420, 20%nat); (0x5b790, 16%nat); (0x5c240, 8%nat); (0x5d160, 40%nat); (0x5dcb0, 16%nat); (0x60070, 32%nat); (0x60140, 16%nat); (0x61f10, 20%nat); (0x62620, 8%nat); (0x62670, 8%nat); (0x657b0, 8%nat); (0x65830, 8%nat); (0x658e0, 20%nat); (0x65980, 16%nat); (0x66030, 16%nat); (0x67720, 64%nat); (0x678a0, 12%nat); (0x678f0, 12%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x6a7c0, 36%nat); (0x6a9f0, 16%nat); (0x6aa50, 40%nat); (0x6ab00, 28%nat); (0x6aca0, 24%nat); (0x81c30, 84%nat); (0x81ed0, 12%nat); (0x825d0, 8%nat); (0x8d1c0, 16%nat); (0x8d270, 8%nat); (0x8dce4, 8%nat); (0x8dd14, 8%nat); (0x8ec84, 24%nat); (0x8ecf4, 24%nat); (0x8ed64, 124%nat); (0x8f264, 56%nat); (0x8f4a4, 164%nat); (0x8f844, 156%nat); (0x8fb24, 108%nat); (0x92394, 84%nat); (0x9ad64, 8%nat); (0x9b294, 8%nat); (0x9b484, 8%nat); (0x9b514, 12%nat); (0x9b624, 36%nat); (0x9c664, 16%nat); (0x9d624, 28%nat)]%Z.
Lemma ITD_ok : itab_sound BSEGS ITD.
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
  check BSEGS ITD BOTH NXD AsanInit.LIMIT (XNS BSEGS BOTH NXD AsanInit.LIMIT) XE0 XB0 HS_bothD KC0 BFUEL FUEL None HS_bothQ_12 startup_plan_both_segC = COk startup_shapeD.
Proof. Time (vm_cert_refl constr:(COk startup_shapeD)). Time Qed.
End BothStartupCertD.

(* [comment removed for export] *)
Module BothStartupCertQ.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITQ : itab := mk_itab_ranges BSEGS [(0x3cd30, 20%nat); (0x3d470, 20%nat); (0x42560, 4%nat); (0x48410, 36%nat); (0x53160, 8%nat); (0x53b30, 68%nat); (0x56800, 12%nat); (0x56900, 16%nat); (0x56980, 20%nat); (0x5b400, 12%nat); (0x5b4b0, 20%nat); (0x5ba20, 12%nat); (0x5bd00, 8%nat); (0x5dcb0, 16%nat); (0x5e0f0, 12%nat); (0x5e4b0, 16%nat); (0x5e6f0, 28%nat); (0x5f890, 8%nat); (0x61f10, 20%nat); (0x66030, 16%nat); (0x677b0, 28%nat); (0x6b3e0, 44%nat); (0x6b4f0, 12%nat); (0x6b5b0, 28%nat); (0x6c760, 44%nat); (0x6c890, 52%nat); (0x6c970, 32%nat); (0x7c4f0, 20%nat); (0x7c570, 20%nat); (0x8e5c4, 8%nat); (0x8ec84, 44%nat); (0x8ef54, 20%nat); (0x8efb4, 12%nat); (0x8f034, 12%nat); (0x8f144, 24%nat); (0x8f214, 12%nat); (0x8f254, 12%nat); (0x8f2c4, 32%nat); (0x8f4a4, 12%nat); (0x9a964, 8%nat); (0x9b5b4, 32%nat); (0x9c664, 16%nat)]%Z.
Lemma ITQ_ok : itab_sound BSEGS ITQ.
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
  check BSEGS ITQ BOTH NXQ AsanInit.LIMIT (XNS BSEGS BOTH NXQ AsanInit.LIMIT) XE0 XB0 HS_bothQ KC0 BFUEL FUEL None HS_bothC_14 startup_plan_both_segQ = COk startup_shapeQ.
Proof. Time (vm_cert_refl constr:(COk startup_shapeQ)). Time Qed.
End BothStartupCertQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import PropExec ShapeAlg SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanNodesWJoin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StartupPlanBoth StartupHSBoth BothStartupCertDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert.
Import BothStartupCertB1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import BothStartupCertB.
Import BothStartupCertC.
Import BothStartupCertQ.
Import BothStartupCertD.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StartupPlan2Both StartupHS2Both.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertB.BothStartupCert2.
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
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (AsanInit.E0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable H : env -> Fs.Fs -> TSet.
  Hypothesis H_agree : forall E E' fs', env_agree NX0 E E' -> H E fs' = H E' fs'.
  Hypothesis H_nil : forall E fs', H E fs' [].
  Hypothesis MAIN : holes_stmt BSEGS BOTH LIM HS_both2 SINV argH (fun _ => H) fs.

  Let AH := argH0_high BPH sp rdraw argv envp uid hw Hsp Hva.
  Let AH2 := argH0_high2 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let AA := argH0_agree BPH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame BPH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree BPH sp rdraw brk0 argv envp uid hw.

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
    Lemma seg_sound : forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HSn : nat -> option acs) (FUEL BFUEL KC : nat)
                             (p : plan) (start : acs) (shp : shape),
      holes_stmt BSEGS BOTH LIM HSn SINV argH HH fs ->
      check BSEGS IT BOTH nx LIM (XNS BSEGS BOTH nx LIM) XE0 XB0 HSn KC BFUEL FUEL None start p = COk shp ->
      holes_only shp = true ->
      forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
        srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model)).
    Proof.
      intros IT IT_ok HSn FUEL BFUEL KC p start shp HSOUND CERT Hshp E R FULL model HC.
      pose proof (check_sound BSEGS IT IT_ok BOTH nx Hnx LIM HSn (XNS BSEGS BOTH nx LIM) XE0 XB0
                both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AAn SF SAn
                HH (fun h E1 E2 fs' Hag => HH_agree h E1 E2 fs' (env_agree_nx E1 E2 Hag)) HH_nil fs KC
                (AsanNodesMmB.node_sys_sound BSEGS BOTH nx LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AH2 AAn SF SAn)
                (AsanNodesMmB.node_brk2_sound BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
                (node_mmap2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mmapin_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (node_mprotect2_sound_OBL BSEGS BOTH nx LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AAn SF SAn)
                (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH fs)
                (both_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M HH0 => HH0) SF nx Hnx SAn)
                (node_join_sound BSEGS BOTH nx LIM SINV argH fs)
                (XNS_sound BSEGS BOTH nx LIM SINV argH fs AAn SAn both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
                HSOUND FUEL BFUEL None p start shp CERT
                E R FULL model t_nil HC I eq_refl) as R0.
      eapply srz_conseq; [exact R0 | apply sd_allH; exact Hshp].
    Qed.

    (* [comment removed for export] *)
    Lemma seg_holes : forall (HSp : nat -> option acs) (h0 : nat) (start : acs),
      (forall h ch, HSp h = Some ch -> h = h0 /\ ch = start) ->
      (forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E start R FULL model ->
         srealizes BSEGS (cfg_of BSEGS R (pc start) FULL model) (H E (m_fs model))) ->
      holes_stmt BSEGS BOTH LIM HSp SINV argH HH fs.
    Proof.
      intros HSp h0 start Hone Hseg h ch Hh E R FULL model HC. destruct (Hone h ch Hh) as [-> ->]. unfold HH. exact (Hseg E R FULL model HC).
    Qed.
  End Seg.

  (* [comment removed for export] *)
  Lemma S2_sound : holes_stmt BSEGS BOTH LIM HS_bothD SINV argH HH fs.
  Proof.
    apply (seg_holes HS_bothD 0%nat HS_bothD_0).
    { intros h ch Hh. unfold HS_bothD in Hh. do 0 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXS2 NXS2_ge IT2 IT2_ok HS_both2 FUEL BFUEL KC0 startup2_plan_both HS_bothD_0 startup2_shape); [| exact startup2_cert | reflexivity].
    intros h ch Hh E R FULL model HC. unfold HH. exact (MAIN h ch Hh E R FULL model HC).
  Qed.
  Lemma D_sound : holes_stmt BSEGS BOTH LIM HS_bothQ SINV argH HH fs.
  Proof.
    apply (seg_holes HS_bothQ 12%nat HS_bothQ_12).
    { intros h ch Hh. unfold HS_bothQ in Hh. do 12 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXD NXD_ge ITD ITD_ok HS_bothD FUEL BFUEL KC0 startup_plan_both_segC HS_bothQ_12 startup_shapeD); [exact S2_sound | exact startup_certD | reflexivity].
  Qed.
  Lemma Q_sound : holes_stmt BSEGS BOTH LIM HS_bothC SINV argH HH fs.
  Proof.
    apply (seg_holes HS_bothC 14%nat HS_bothC_14).
    { intros h ch Hh. unfold HS_bothC in Hh. do 14 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXQ NXQ_ge ITQ ITQ_ok HS_bothQ FUEL BFUEL KC0 startup_plan_both_segQ HS_bothC_14 startup_shapeQ); [exact D_sound | exact startup_certQ | reflexivity].
  Qed.
  Lemma C_sound : holes_stmt BSEGS BOTH LIM HS_bothB SINV argH HH fs.
  Proof.
    apply (seg_holes HS_bothB 11%nat HS_bothB_11).
    { intros h ch Hh. unfold HS_bothB in Hh. do 11 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXC NXC_ge ITC ITC_ok HS_bothC FUEL BFUEL KC0 startup_plan_both_segB HS_bothB_11 startup_shapeC); [exact Q_sound | exact startup_certC | reflexivity].
  Qed.
  Lemma B_sound : holes_stmt BSEGS BOTH LIM HS_bothB1 SINV argH HH fs.
  Proof.
    apply (seg_holes HS_bothB1 13%nat HS_bothB1_13).
    { intros h ch Hh. unfold HS_bothB1 in Hh. do 13 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXB NXB_ge ITB ITB_ok HS_bothB FUEL BFUEL KC0 startup_plan_both_segB1 HS_bothB1_13 startup_shapeB); [exact C_sound | exact startup_certB | reflexivity].
  Qed.
  Lemma B1_sound : holes_stmt BSEGS BOTH LIM HS_bothA SINV argH HH fs.
  Proof.
    apply (seg_holes HS_bothA 10%nat HS_bothA_10).
    { intros h ch Hh. unfold HS_bothA in Hh. do 10 (destruct h as [|h]; [discriminate Hh|]).
      destruct h as [|h]; [injection Hh as <-; split; reflexivity | discriminate Hh]. }
    apply (seg_sound NXB1 NXB1_ge ITB1 ITB1_ok HS_bothB1 FUEL BFUEL KC0 startup_plan_both_segA HS_bothA_10 startup_shapeB1); [exact B_sound | exact startup_certB1 | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot_shape :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp))
              (sd HH t_nil E0a fs startup_shape).
  Proof.
    exact (both_startup sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt ifs urnd tmp Hfs Hsp Hbrk Hva Hve Hfit Huid Hhw
             IT0 IT0_ok HS_bothA startup_plan_both startup_shape KC0 BFUEL FUEL startup_cert HH HH_agree HH_nil B1_sound).
  Qed.

  (* [comment removed for export] *)
  Theorem both_boot :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp))
              (H E0a fs).
  Proof. eapply srz_conseq; [exact both_boot_shape | apply sd_allH; reflexivity]. Qed.
End Boot.
