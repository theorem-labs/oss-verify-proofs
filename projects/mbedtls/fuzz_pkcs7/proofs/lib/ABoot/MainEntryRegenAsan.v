(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the main-entry hand-off tables me_R0_tab to me_B4_tab of this unit's ABoot/MainEntryPiecesAsan.v, each now taken at a value of the run's CONFIG_RSEQ flag and built from the states the renumbered recorded plan reaches in the build (collect_handoffs) from the start-up's computed state, in place of the recorded hand-off states this unit's ABoot/MainEntryHScutAsan.v held. *)
(* The main entry's hand-off states, computed in the build from the run at LPS 727298f3, one per
   value of the run's CONFIG_RSEQ flag rz, in the form of jsoncons/fuzz_bigint's As0CertK_202.v (its
   hand-off states computed by collect_handoffs): each state is the one the renumbered recorded plan
   (MainEntryPiecesAsan.v) reaches at that hand-off from the start-up's computed hand-off state HS_0
   (StartupRegenAsan.v), so no recorded hand-off state is used.  A state computed here is a definition,
   not an assumption: the certificate that names it runs the check again, and the state the run reaches
   must entail it. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan AsanCertDefs PlanCut PlanRegen StartupRegenAsan MainEntryPiecesAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [me_col rz cs0 p fuel]: the hand-off states the check of [p] from [cs0] reaches, collected. *)
Definition me_col (rz : Z) (cs0 : acs) (p : plan) (fuel : nat) : list (nat * acs) :=
  collect_handoffs fuel (fun js => s2_check NX1 rz IT1 js cs0 p) [].
Definition rzsel {T : Type} (rz : Z) (a0 a1 : T) : T := if Z.eqb rz 1 then a1 else a0.

(* R0: from the start-up's hand-off state HS_0 rz to hand-offs 1000 and 1001. *)
Definition HSL_R0_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HS_0 0) me_R0_planR 6.
Definition HSL_R0_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HS_0 1) me_R0_planR 6.
Definition HSm_1000 (rz : Z) : acs := hstate (rzsel rz HSL_R0_0 HSL_R0_1) (HS_0 rz) 1000.
Definition HSm_1001 (rz : Z) : acs := hstate (rzsel rz HSL_R0_0 HSL_R0_1) (HS_0 rz) 1001.
Definition me_R0_tab (rz : Z) : nat -> option acs := hs_tab [(1000%nat, HSm_1000 rz); (1001%nat, HSm_1001 rz)].

(* A1: from 1000 to 1010. *)
Definition HSL_A1_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1000 0) me_A1_planR 4.
Definition HSL_A1_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1000 1) me_A1_planR 4.
Definition HSm_1010 (rz : Z) : acs := hstate (rzsel rz HSL_A1_0 HSL_A1_1) (HSm_1000 rz) 1010.
Definition me_A1_tab (rz : Z) : nat -> option acs := hs_tab [(1010%nat, HSm_1010 rz)].
(* A2: from 1010 to 1011. *)
Definition HSL_A2_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1010 0) me_A2_planR 4.
Definition HSL_A2_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1010 1) me_A2_planR 4.
Definition HSm_1011 (rz : Z) : acs := hstate (rzsel rz HSL_A2_0 HSL_A2_1) (HSm_1010 rz) 1011.
Definition me_A2_tab (rz : Z) : nat -> option acs := hs_tab [(1011%nat, HSm_1011 rz)].
(* A3: from 1011 to 1012. *)
Definition HSL_A3_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1011 0) me_A3_planR 4.
Definition HSL_A3_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1011 1) me_A3_planR 4.
Definition HSm_1012 (rz : Z) : acs := hstate (rzsel rz HSL_A3_0 HSL_A3_1) (HSm_1011 rz) 1012.
Definition me_A3_tab (rz : Z) : nat -> option acs := hs_tab [(1012%nat, HSm_1012 rz)].
(* A4: from 1012 to 1013. *)
Definition HSL_A4_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1012 0) me_A4_planR 4.
Definition HSL_A4_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1012 1) me_A4_planR 4.
Definition HSm_1013 (rz : Z) : acs := hstate (rzsel rz HSL_A4_0 HSL_A4_1) (HSm_1012 rz) 1013.
Definition me_A4_tab (rz : Z) : nat -> option acs := hs_tab [(1013%nat, HSm_1013 rz)].
(* B1: from 1001 to 1020. *)
Definition HSL_B1_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1001 0) me_B1_planR 4.
Definition HSL_B1_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1001 1) me_B1_planR 4.
Definition HSm_1020 (rz : Z) : acs := hstate (rzsel rz HSL_B1_0 HSL_B1_1) (HSm_1001 rz) 1020.
Definition me_B1_tab (rz : Z) : nat -> option acs := hs_tab [(1020%nat, HSm_1020 rz)].
(* B2: from 1020 to 1021. *)
Definition HSL_B2_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1020 0) me_B2_planR 4.
Definition HSL_B2_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1020 1) me_B2_planR 4.
Definition HSm_1021 (rz : Z) : acs := hstate (rzsel rz HSL_B2_0 HSL_B2_1) (HSm_1020 rz) 1021.
Definition me_B2_tab (rz : Z) : nat -> option acs := hs_tab [(1021%nat, HSm_1021 rz)].
(* B3: from 1021 to 1022. *)
Definition HSL_B3_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1021 0) me_B3_planR 4.
Definition HSL_B3_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1021 1) me_B3_planR 4.
Definition HSm_1022 (rz : Z) : acs := hstate (rzsel rz HSL_B3_0 HSL_B3_1) (HSm_1021 rz) 1022.
Definition me_B3_tab (rz : Z) : nat -> option acs := hs_tab [(1022%nat, HSm_1022 rz)].
(* B4: from 1022 to 1023. *)
Definition HSL_B4_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1022 0) me_B4_planR 4.
Definition HSL_B4_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1022 1) me_B4_planR 4.
Definition HSm_1023 (rz : Z) : acs := hstate (rzsel rz HSL_B4_0 HSL_B4_1) (HSm_1022 rz) 1023.
Definition me_B4_tab (rz : Z) : nat -> option acs := hs_tab [(1023%nat, HSm_1023 rz)].
(* A5 and B5: from 1013 and 1023 to the main phase's entry, hand-offs 1 and 2. *)
Definition HSL_A5_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1013 0) me_A5_planR 4.
Definition HSL_A5_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1013 1) me_A5_planR 4.
Definition HSL_B5_0 : list (nat * acs) := Eval vm_compute in me_col 0 (HSm_1023 0) me_B5_planR 4.
Definition HSL_B5_1 : list (nat * acs) := Eval vm_compute in me_col 1 (HSm_1023 1) me_B5_planR 4.
Definition HS_main_1_0 : acs := hstate HSL_A5_0 (HSm_1013 0) 1.
Definition HS_main_1_1 : acs := hstate HSL_A5_1 (HSm_1013 1) 1.
Definition HS_main_2_0 : acs := hstate HSL_B5_0 (HSm_1023 0) 2.
Definition HS_main_2_1 : acs := hstate HSL_B5_1 (HSm_1023 1) 2.
Definition HS_main_1 (rz : Z) : acs := rzsel rz HS_main_1_0 HS_main_1_1.
Definition HS_main_2 (rz : Z) : acs := rzsel rz HS_main_2_0 HS_main_2_1.
Definition HS_main (rz : Z) (h : nat) : option acs :=
  match h with 1%nat => Some (HS_main_1 rz) | 2%nat => Some (HS_main_2 rz) | _ => None end.
