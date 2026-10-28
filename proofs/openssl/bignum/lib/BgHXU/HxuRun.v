(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Image.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInit HxuHooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation bgusegs := ImageBg.bgusegs.

Definition hooksP : list (w64 * (acd -> sstate -> option (acd * sstate))) :=
  [(PC_MALLOC, hkp_malloc); (PC_FREE, hkp_free); (PC_REALLOC, hkp_realloc); (PC_MEMSET, hkp_memset)].
Definition finalP (pc : w64) : bool := w_eqb pc PC_FINAL.

Definition run_result : icache * dres := hx_drive bgusegs hooksP finalP 4000 22 IEmpty (ACD OPS [] 0) S0.

Definition end_state (r : icache * @dres acd) : sstate := match snd r with DDone _ X => X | DStuck _ _ X => X | DFuel _ X => X end.
Definition end_cd (r : icache * @dres acd) : acd := match snd r with DDone cd _ => cd | DStuck _ cd _ => cd | DFuel cd _ => cd end.

Notation S_end := (end_state run_result).
Notation cd_end := (end_cd run_result).

Lemma end_state_eq (r : icache * @dres acd) (ic : icache) (cd : acd) (X : sstate) : r = (ic, DDone cd X) -> end_state r = X /\ end_cd r = cd.
Proof. intros ->. split; reflexivity. Qed.

Definition hval_eqb (a b : hval) : bool :=
  match a, b with
  | VC x, VC y => w_eqb x y
  | VP t o, VP t' o' => (t =? t')%uint63 && w_eqb o o'
  | VU, VU => true
  | _, _ => false
  end.

Lemma hval_eqb_eq (a b : hval) : hval_eqb a b = true -> a = b.
Proof.
  destruct a as [x|t o| |], b as [y|t' o'| |]; cbn; intros H; try discriminate; try reflexivity.
  - apply w_eqb_true_iff in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Uint63.eqb_spec in H1. apply w_eqb_true_iff in H2. subst. reflexivity.
Qed.

Definition final_regs : list (rix * hval) :=
  [(X1, VP T_RA w_zero); (X2, VP 1%uint63 (W false STK)); (X3, VP T_GP w_zero); (X4, VC TPV);
   (X8, VP T_S0 w_zero); (X9, VP (T_S0 + 1)%uint63 w_zero); (X18, VP (T_S0 + 2)%uint63 w_zero); (X19, VP (T_S0 + 3)%uint63 w_zero);
   (X20, VP (T_S0 + 4)%uint63 w_zero); (X21, VP (T_S0 + 5)%uint63 w_zero); (X22, VP (T_S0 + 6)%uint63 w_zero); (X23, VP (T_S0 + 7)%uint63 w_zero);
   (X24, VP (T_S0 + 8)%uint63 w_zero); (X25, VP (T_S0 + 9)%uint63 w_zero); (X26, VP (T_S0 + 10)%uint63 w_zero); (X27, VP (T_S0 + 11)%uint63 w_zero)].

Definition final_regs_ok (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) final_regs.

Definition errno_region_ok (S : sstate) : bool :=
  match mget (s_mem S) T_ERRNO with
  | Some rg => match rg_abs rg with Some a => (a =? ERRNO_INT)%uint63 && (rg_size rg =? 4)%uint63 && rg_wr rg | None => false end
  | None => false
  end.

Definition byte_known (rg : region) (off z : Z) : bool := match rg_kb bgusegs rg off with KB z' => z' =? z | _ => false end.

Definition exit_cells_ok (S : sstate) : bool :=
  match mget (s_mem S) T_OSSL with
  | Some rg => match rg_abs rg with
               | Some a => (a =? OSSL_LO)%uint63 && rg_wr rg && (OFF_DO_CLEANUP <? to_Z (rg_size rg)) && byte_known rg OFF_DO_CLEANUP 0
               | None => false
               end
  | None => false
  end.

Definition run_ok (r : icache * dres) : bool :=
  match snd r with
  | DDone cd X =>
      (match a_ops cd with [] => true | _ => false end) && w_eqb (s_pc X) PC_FINAL && (match s_resv X with RNone => true | _ => false end)
      && final_regs_ok X && errno_region_ok X && exit_cells_ok X
  | _ => false
  end.

Lemma run_ok_inv (r : icache * dres) : run_ok r = true ->
  exists ic cd S, r = (ic, DDone cd S) /\ a_ops cd = [] /\ s_pc S = PC_FINAL /\ s_resv S = RNone
                  /\ final_regs_ok S = true /\ errno_region_ok S = true /\ exit_cells_ok S = true.
Proof.
  destruct r as [ic [cd S| |]]; cbn [run_ok snd]; try discriminate. intros H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists ic, cd, S. split; [reflexivity|]. split; [destruct (a_ops cd); [reflexivity | discriminate]|].
  split; [apply w_eqb_true_iff; exact H2|]. split; [destruct (s_resv S); [reflexivity | discriminate | discriminate]|]. auto.
Qed.

Lemma run_result_unfold : run_result = hx_drive bgusegs hooksP finalP 4000 22 IEmpty (ACD OPS [] 0) S0.
Proof. reflexivity. Qed.

Lemma run_checked : run_ok run_result = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_final : exists ic', hx_fetch bgusegs IEmpty PC_FINAL = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.
