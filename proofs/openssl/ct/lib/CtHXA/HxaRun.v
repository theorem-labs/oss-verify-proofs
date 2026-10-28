(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaHkDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition finalA (pc : w64) : bool := w_eqb pc PC_FINAL.

Definition run_result (r : int) : icache * @xres xcd := hxs_drive SHBW ctasegs hookixA hooksA finalA 4000 23 IEmpty (XCD [] [] 0 0) (S0 r).

Definition end_state (x : icache * @xres xcd) : sstate := match snd x with XDone _ X => X | XStuck _ _ X => X | XFuel _ X => X end.
Definition end_cd (x : icache * @xres xcd) : xcd := match snd x with XDone cd _ => cd | XStuck _ cd _ => cd | XFuel cd _ => cd end.

(* [comment removed for export] *)
Definition final_regs (r : int) : list (rix * hval) :=
  [(X1, VP T_RA w_zero); (X2, VP T_STK (W false (STK + r)%uint63)); (X3, VP T_GP w_zero); (X4, VC TPV);
   (X8, VP T_S0 w_zero); (X9, VP (T_S0 + 1)%uint63 w_zero); (X18, VP (T_S0 + 2)%uint63 w_zero); (X19, VP (T_S0 + 3)%uint63 w_zero);
   (X20, VP (T_S0 + 4)%uint63 w_zero); (X21, VP (T_S0 + 5)%uint63 w_zero); (X22, VP (T_S0 + 6)%uint63 w_zero); (X23, VP (T_S0 + 7)%uint63 w_zero);
   (X24, VP (T_S0 + 8)%uint63 w_zero); (X25, VP (T_S0 + 9)%uint63 w_zero); (X26, VP (T_S0 + 10)%uint63 w_zero); (X27, VP (T_S0 + 11)%uint63 w_zero)].

Definition final_regs_ok (r : int) (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) (final_regs r).

Definition run_ok (r : int) (x : icache * @xres xcd) : bool :=
  match snd x with
  | XDone cd X =>
      (match x_frames cd with [] => true | _ => false end) && w_eqb (s_pc X) PC_FINAL && (match s_resv X with RNone => true | _ => false end)
      && final_regs_ok r X && (x_calls cd <=? 4096) && (x_nb cd <=? 1700)
  | _ => false
  end.

Lemma run_ok_inv (r : int) (x : icache * @xres xcd) : run_ok r x = true ->
  exists ic cd S, x = (ic, XDone cd S) /\ x_frames cd = [] /\ s_pc S = PC_FINAL /\ s_resv S = RNone
                  /\ final_regs_ok r S = true /\ x_calls cd <= 4096 /\ x_nb cd <= 1700.
Proof.
  destruct x as [ic [cd S| |]]; cbn [run_ok snd]; try discriminate. intros H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists ic, cd, S. split; [reflexivity|]. split; [destruct (x_frames cd); [reflexivity | discriminate]|].
  split; [apply w_eqb_true_iff; exact H2|]. split; [destruct (s_resv S); [reflexivity | discriminate | discriminate]|].
  split; [exact H4|]. split; apply Z.leb_le; assumption.
Qed.

(* [comment removed for export] *)
Lemma run_result_unfold (r : int) : run_result r = hxs_drive SHBW ctasegs hookixA hooksA finalA 4000 23 IEmpty (XCD [] [] 0 0) (S0 r).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_checked_0 : run_ok 0 (run_result 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma run_checked_16 : run_ok 16 (run_result 16) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fetch_final : exists ic', hx_fetch ctasegs IEmpty PC_FINAL = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.
