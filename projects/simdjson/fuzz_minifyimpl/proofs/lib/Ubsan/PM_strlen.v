(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim HarnessM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition PSTRLEN : Z := 0xcf630.       (* [comment removed for export] *)
Definition PMSG : Z := 0x11e1a.          (* [comment removed for export] *)
Definition MSG : list byte := Eval vm_compute in (match image_bytes usegs PMSG 54 with Some bs => bs | None => [] end).
Lemma MSG_length : length MSG = 54%nat. Proof. vm_compute. reflexivity. Qed.
Lemma MSG_ro : ro_bytes_b usegs PMSG MSG = true. Proof. vm_compute. reflexivity. Qed.
Definition PMSGW : Z := 0x11e28.         (* [comment removed for export] *)
Definition MSGW : list byte := Eval vm_compute in (match image_bytes usegs PMSGW 64 with Some bs => bs | None => [] end).
Lemma MSGW_ro : ro_bytes_b usegs PMSGW MSGW = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition PSTRLEN_K : Z := 0x13f78.
Definition STRLEN_K : list byte := Eval vm_compute in (match image_bytes usegs PSTRLEN_K 32 with Some bs => bs | None => [] end).
Lemma STRLEN_K_ro : ro_bytes_b usegs PSTRLEN_K STRLEN_K = true. Proof. vm_compute. reflexivity. Qed.

Ltac lit_if_vm := lazymatch goal with |- evt _ _ (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?mm ?ro) =>
   let v := eval vm_compute in c in
   lazymatch v with true => if_true | false => if_false end | |- _ => idtac end.
Ltac run_to stop := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lit_if_vm
  end).

Definition strlen_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 : word,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ERRMSG_LEN) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs).
Lemma strlen_msg : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m ->
  evt usegs (strlen_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PMSG) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PSTRLEN) fc None m (seg_rom usegs)).
Proof.
  intros. unfold PMSG, PSTRLEN.
  assert (ROW : ro_cells usegs m PMSGW [CB 64 MSGW]).
  { change 64%nat with (length MSGW). apply (ro_cells_image usegs m); [exact H| exact MSGW_ro| unfold PMSGW; lia| unfold PMSGW; cbn; lia]. }
  assert (ROK : ro_cells usegs m PSTRLEN_K [CB 32 STRLEN_K]).
  { change 32%nat with (length STRLEN_K). apply (ro_cells_image usegs m); [exact H| exact STRLEN_K_ro| unfold PSTRLEN_K; lia| unfold PSTRLEN_K; cbn; lia]. }
  unfold PMSGW in ROW. unfold PSTRLEN_K in ROK.
  run_to 0xcf6b4.
  zstep.
  apply evt_done. unfold strlen_post, ERRMSG_LEN. do 6 eexists.
  first [ reflexivity | f_equal; unfold mkR; repeat f_equal; apply bv_eq; vm_compute; reflexivity ].
Qed.
