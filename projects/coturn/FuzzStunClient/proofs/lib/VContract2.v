(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStepMem VCert VContract VState2 VStepMem2 VContractA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive contract2 : Type :=
| CV1 (c : contract)                 (* [comment removed for export] *)
| C_stack_malloc (cid : Z)           (* [comment removed for export] *)
| C_set_shadow (v : Z)               (* [comment removed for export] *)
| C_asan_memset                      (* [comment removed for export] *)
| C_asan_memcpy                      (* [comment removed for export] *)
| C_i_strlen | C_i_strcmp | C_i_strncpy | C_i_bcmp.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition contract2_K (c : contract2) : Z :=
  match c with
  | CV1 c1 => contract_K c1
  | C_stack_malloc _ => K_stack_malloc
  | C_set_shadow _ => K_set_shadow
  | C_asan_memset => K_asan_memset
  | C_asan_memcpy => K_asan_memcpy
  | C_i_strlen => K_i_strlen | C_i_strcmp => K_i_strcmp | C_i_strncpy => K_i_strncpy | C_i_bcmp => K_i_bcmp
  end.

(* [comment removed for export] *)
Inductive cres2' : Type :=
| CR2OkN (l : list (vstate2 * absval))
| CR2Dead
| CR2Fail (msg : string).
Definition CR2Ok (A' : vstate2) (a0 : absval) : cres2' := CR2OkN [(A', a0)].

Definition lift_cres (A : vstate2) (r : cres) : cres2' :=
  match r with
  | CROk A1 v => CR2Ok (with_v1 A A1) v
  | CRDead => CR2Dead
  | CRFail m => CR2Fail m
  end.

(* [comment removed for export] *)
Definition of_ca (r : ca_res) : cres2' :=
  match r with CA_ok l => CR2OkN l | CA_dead => CR2Dead | CA_fail m => CR2Fail m end.

(* [comment removed for export] *)
Definition contract_apply2 (P : vparams2) (CI : cimg) (c : contract2) (A : vstate2) (spoff : Z) : cres2' :=
  match c with
  | CV1 c1 => lift_cres A (contract_apply (p1 P) CI c1 (v1 A) spoff)
  | C_stack_malloc cid => of_ca (ca_stack_malloc P (ci_tp CI) A spoff cid)
  | C_set_shadow b => of_ca (ca_set_shadow P A b)
  | C_asan_memset => of_ca (ca_asan_memset P A)
  | C_asan_memcpy => of_ca (ca_asan_memcpy P A)
  | C_i_strlen => of_ca (ca_i_strlen P A)
  | C_i_strcmp => of_ca (ca_i_strcmp P A)
  | C_i_strncpy => of_ca (ca_i_strncpy P A spoff)
  | C_i_bcmp => of_ca (ca_i_bcmp P A)
  end.

(* [comment removed for export] *)
Definition frame_rule (K : Z) (A : vstate) (spoff : Z) (a0 : absval) : vstate :=
  let A1 := if Z.eqb K 0 then A
            else kill_nul (set_slots A (cm_kill (vs_slots A) (spoff - K) spoff)) (spoff - K) (spoff - 1) None in
  let A2 := set_tops A1 CALLER_SAVED in
  set_reg A2 A0r a0.

Lemma frame_rule_v1 c A spoff a0 : frame_rule (contract_K c) A spoff a0 = contract_frame c A spoff a0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition contract_frame2 (c : contract2) (A : vstate2) (spoff : Z) (a0 : absval) : vstate2 :=
  with_v1 A (frame_rule (contract2_K c) (v1 A) spoff a0).
