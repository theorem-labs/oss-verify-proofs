(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook HxQuery.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsHook HxsKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaEceInit HxaImage HxaHk HxaHkFrame HxaHkRelease HxaQuery.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hooksE : list (@hook xcd) := [hkA_free TRACES_E; hkA_stack_malloc0; hkA_release].

Definition hookixE : itrie nat :=
  fold_left (fun tr p => iset ICD tr (ic_key (W false p)) 2%nat) REL0_PCS
    (iset ICD (iset ICD IEmpty (ic_key PC_FREE) 0%nat) (ic_key PC_STACK_MALLOC0) 1%nat).

Definition finalE (pc : w64) : bool := w_eqb pc PC_ECE_FINAL.

Definition run_result_E (r : int) : icache * @xres xcd := hxs_drive SHBW bsegs hookixE hooksE finalE 4000 23 IEmpty (XCD [] [] 0 0) (SE0 r).

(* [comment removed for export] *)
Definition final_regs_E (r : int) : list (rix * hval) :=
  [(X1, VC RA_ECE); (X2, VP T_STK (W false (ESTK + r)%uint63)); (X3, VP TE_GP w_zero); (X4, VC TPV);
   (X8, VP T_S0 w_zero); (X9, VP (T_S0 + 1)%uint63 w_zero); (X18, VP (T_S0 + 2)%uint63 w_zero); (X19, VP (T_S0 + 3)%uint63 w_zero);
   (X20, VP (T_S0 + 4)%uint63 w_zero); (X21, VP (T_S0 + 5)%uint63 w_zero); (X22, VP (T_S0 + 6)%uint63 w_zero); (X23, VP (T_S0 + 7)%uint63 w_zero);
   (X24, VP (T_S0 + 8)%uint63 w_zero); (X25, VP (T_S0 + 9)%uint63 w_zero); (X26, VP (T_S0 + 10)%uint63 w_zero); (X27, VP (T_S0 + 11)%uint63 w_zero)].

Definition final_regs_ok_E (r : int) (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) (final_regs_E r).

(* [comment removed for export] *)
Definition Q_es_E : query := Q T_ES 0 904 0 (kbs_bytes (repeat 0 704 ++ repeat 255 64 ++ repeat 0 136)).

Definition run_ok_E (r : int) (x : icache * @xres xcd) : bool :=
  match snd x with
  | XDone cd X =>
      (match x_frames cd with [] => true | _ => false end) && (match x_blocks cd with [] => true | _ => false end)
      && w_eqb (s_pc X) PC_ECE_FINAL && (match s_resv X with RNone => true | _ => false end)
      && final_regs_ok_E r X && (x_calls cd <=? 64) && q_ok X Q_es_E
  | _ => false
  end.

Lemma run_ok_E_inv (r : int) (x : icache * @xres xcd) : run_ok_E r x = true ->
  exists ic cd S, x = (ic, XDone cd S) /\ x_frames cd = [] /\ x_blocks cd = [] /\ s_pc S = PC_ECE_FINAL /\ s_resv S = RNone
                  /\ final_regs_ok_E r S = true /\ x_calls cd <= 64 /\ q_ok S Q_es_E = true.
Proof.
  destruct x as [ic [cd S| |]]; cbn [run_ok_E snd]; try discriminate. intros H.
  apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists ic, cd, S. split; [reflexivity|]. split; [destruct (x_frames cd); [reflexivity | discriminate]|].
  split; [destruct (x_blocks cd); [reflexivity | discriminate]|].
  split; [apply w_eqb_true_iff; exact H3|]. split; [destruct (s_resv S); [reflexivity | discriminate | discriminate]|].
  split; [exact H5|]. split; [apply Z.leb_le; exact H6 | exact H7].
Qed.

(* [comment removed for export] *)
Lemma run_result_E_unfold (r : int) : run_result_E r = hxs_drive SHBW bsegs hookixE hooksE finalE 4000 23 IEmpty (XCD [] [] 0 0) (SE0 r).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_checked_E0 : run_ok_E 0 (run_result_E 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma run_checked_E16 : run_ok_E 16 (run_result_E 16) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fetch_final_E : exists ic', hx_fetch bsegs IEmpty PC_ECE_FINAL = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.
