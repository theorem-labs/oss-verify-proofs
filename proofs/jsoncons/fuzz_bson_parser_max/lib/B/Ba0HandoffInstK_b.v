(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffLedgerK HandoffBInvK ArtRuns ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b
  Ba0HSK_0_b Ba0HSK_1_b Ba0MainTableK_b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

Definition HSA (h : nat) : acs := match h with O => HS_0 | _ => HS_1 end.
Lemma HSA_some : forall h, (h < 2)%nat -> HS_as0 h = Some (HSA h).
Proof. intros [|[|h]] H; [reflexivity|reflexivity|lia]. Qed.
Lemma HSA_none : forall h, (2 <= h)%nat -> HS_as0 h = None.
Proof. intros [|[|h]] H; [lia|lia|reflexivity]. Qed.
Lemma HSA_nofog : forall h, (h < 2)%nat -> no_fog (a_maps (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_mapslin : forall h, (h < 2)%nat -> amaps_lin (kn (HSA h)) (a_maps (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_vislin : forall h, (h < 2)%nat -> vis_lin (kn (HSA h)) (a_vis (HSA h) ++ a_ghost (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_brklin : forall h, (h < 2)%nat -> lin_nowrapR (kn (HSA h)) (a_brk (HSA h)) = true.
Proof. intros [|[|h]] H; [vm_compute; reflexivity|vm_compute; reflexivity|lia]. Qed.
Lemma HSA_fd : forall h, (h < 2)%nat -> a_fd (HSA h) = FdStd.
Proof. intros [|[|h]] H; [reflexivity|reflexivity|lia]. Qed.

Lemma as0_chk_0 : as0_chk HS_0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma as0_chk_1 : as0_chk HS_1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma as0_chk_HSA : forall h, (h < 2)%nat -> as0_chk (HSA h) = true.
Proof. intros [|[|h]] H; [exact as0_chk_0 | exact as0_chk_1 | lia]. Qed.

(* [comment removed for export] *)
Lemma HSA_numbers : forall h, (h < 2)%nat ->
  a_totsz (HSA h) <= 17729665200128 /\ a_eager (HSA h) <= 16515072 /\ a_abytes (HSA h) <= 2461330432 /\ length (a_maps (HSA h)) = 17%nat.
Proof. intros [|[|h]] H; [vm_compute; repeat split; discriminate || reflexivity | vm_compute; repeat split; discriminate || reflexivity | lia]. Qed.

Section Inst.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  (* [comment removed for export] *)
  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461330432 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665200128 + BUDGET) + (21 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Lemma as0_inst_bud : forall h, (h < 2)%nat -> a_eager (HSA h) + a_abytes (HSA h) + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Proof. intros h Hh. destruct (HSA_numbers h Hh) as (_ & N2 & N3 & _). lia. Qed.
  Lemma as0_inst_gap : forall h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + LENMAX + (a_totsz (HSA h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps (HSA h))) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros h Hh. destruct (HSA_numbers h Hh) as (N1 & _ & _ & N4). rewrite N4, asan0_res_eq. cbn [length Nat.add].
    change (Z.of_nat 21) with 21. assert (0 <= LENMAX + 4095) by lia. nia.
  Qed.

  Theorem as0_handoff_static : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    bridge_static ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model)) (as0_RES E)
                  (uE E e_sp0 - 8388608) BUDGET LENMAX KMAX.
  Proof.
    intros h Hh E R FULL model HC.
    eapply as0_bridge_static; try eassumption.
    - exact (as0_chk_HSA h Hh).
    - exact (as0_inst_gap h Hh).
  Qed.

  Theorem as0_handoff_binv : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    BInv ASEGS0 (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model))
         (uE E e_sp0 - 8388608) (as0_BASE EXTRA (HSA h)) BUDGET [] (as0_A0 EXTRA (HSA h) E) FULL model.
  Proof.
    intros h Hh E R FULL model HC.
    eapply as0_binv_main with (LENMAX := LENMAX) (KMAX := KMAX); try eassumption.
    - exact (as0_chk_HSA h Hh).
    - exact (as0_inst_bud h Hh).
    - exact (as0_inst_gap h Hh).
  Qed.
End Inst.
