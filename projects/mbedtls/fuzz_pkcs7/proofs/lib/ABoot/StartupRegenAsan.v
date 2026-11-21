(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the start-up hand-off tables su_P1_tab, su_P2_tab and su_P3_tab of this unit's ABoot/StartupPiecesAsan.v, each now taken at a value of the run's CONFIG_RSEQ flag and built from the states the renumbered recorded plan reaches in the build (collect_handoffs), in place of the recorded hand-off states this unit's ABoot/StartupHSAsan.v held. *)
(* The start-up's hand-off states, computed in the build from the run at LPS 727298f3, one per value
   of the run's CONFIG_RSEQ flag rz, in the form of jsoncons/fuzz_bigint's As0CertK_root.v (its
   start-up hand-off states computed by collect_handoffs): each state is the one the renumbered
   recorded plan (StartupPiecesAsan.v) reaches at that hand-off, so no recorded hand-off state is used.
   A state computed here is a definition, not an assumption: the certificate that names it runs the
   check again, and the state the run reaches must entail it. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan AsanCertDefs PlanCut PlanRegen StartupPiecesAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* P1: from [asan_init rz] to hand-off 1000. *)
Definition HSL_P1_0 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 4 (fun js => s1_check 0 IT0 js su_P1_planR) [].
Definition HSL_P1_1 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 4 (fun js => s1_check 1 IT0 js su_P1_planR) [].
Definition HS_1000_0 : acs := hstate HSL_P1_0 (asan_init 0) 1000.
Definition HS_1000_1 : acs := hstate HSL_P1_1 (asan_init 1) 1000.
Definition HS_1000 (rz : Z) : acs := if Z.eqb rz 1 then HS_1000_1 else HS_1000_0.
Definition su_P1_tab (rz : Z) : nat -> option acs := hs_tab [(1000%nat, HS_1000 rz)].

(* P2: from HS_1000 rz to hand-offs 1001, 1002 and 1003. *)
Definition HSL_P2_0 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 8 (fun js => s2_check NX0 0 IT0 js (HS_1000 0) su_P2_planR) [].
Definition HSL_P2_1 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 8 (fun js => s2_check NX0 1 IT0 js (HS_1000 1) su_P2_planR) [].
Definition HSL_P2 (rz : Z) : list (nat * acs) := if Z.eqb rz 1 then HSL_P2_1 else HSL_P2_0.
Definition HS_1001 (rz : Z) : acs := hstate (HSL_P2 rz) (HS_1000 rz) 1001.
Definition HS_1002 (rz : Z) : acs := hstate (HSL_P2 rz) (HS_1000 rz) 1002.
Definition HS_1003 (rz : Z) : acs := hstate (HSL_P2 rz) (HS_1000 rz) 1003.
Definition su_P2_tab (rz : Z) : nat -> option acs :=
  hs_tab [(1001%nat, HS_1001 rz); (1002%nat, HS_1002 rz); (1003%nat, HS_1003 rz)].

(* P3A, P3B, P3C: from HS_1001, HS_1002, HS_1003 to the one hand-off 0 all three reach, collected
   over the three runs together, so the state at 0 is entailed by every path of all three. *)
Definition su_P3_run (rz : Z) (js : nat -> option acs) : cres :=
  match s2_check NX0 rz IT0 js (HS_1001 rz) su_P3A_planR with
  | COk _ =>
      match s2_check NX0 rz IT0 js (HS_1002 rz) su_P3B_planR with
      | COk _ => s2_check NX0 rz IT0 js (HS_1003 rz) su_P3C_planR
      | e => e
      end
  | e => e
  end.
Definition HSL_P3_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 40 (su_P3_run 0) [].
Definition HSL_P3_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 40 (su_P3_run 1) [].
Definition HS_0 (rz : Z) : acs := hstate (if Z.eqb rz 1 then HSL_P3_1 else HSL_P3_0) (HS_1000 rz) 0.
Definition su_P3_tab (rz : Z) (h : nat) : option acs := match h with 0%nat => Some (HS_0 rz) | _ => None end.
