(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel A_RegConsts A_Gsh.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem R_thread RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition tsd_fact (RT : rt_sig) : Prop := forall Σ m, ART RT Σ m -> rw_cells asegs m 0xba3e98 [C8 (Z_to_bv 64 0xbc5298)].
Definition errno_acc_fact (RT : rt_sig) : Prop := forall Σ m, ART RT Σ m -> acc asegs m 0xba3e48 8.

Lemma rta_tsd : tsd_fact RTA.
Proof. intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & ((_ & _ & T & _) & _) & _). exact T. Qed.

Lemma gshw_errno : AsanGshModel.GSM.gshw A_RegConsts.A_RGC A_Gsh.A_GTAB (shad 0xba3e48) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma rta_errno_acc : errno_acc_fact RTA.
Proof.
  intros Σ m HA i Hi. destruct (ART_shadow Σ m HA) as (_ & _ & _ & _ & _ & GS).
  assert (EG : shad (0xba3e48 + i) = shad 0xba3e48) by (unfold shad; f_equal; clear - Hi; Z.div_mod_to_equations; lia).
  pose proof (GS (shad (0xba3e48 + i)) ltac:(rewrite EG; unfold shad, SHB, SEGTOP_A; lia)) as CELL. rewrite EG, gshw_errno in CELL.
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  split; [unfold shad, SHB; lia|]. split; [unfold shad, SHB; cbn [length]; lia|].
  intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd, wa. rewrite EG, CELL. reflexivity.
Qed.
