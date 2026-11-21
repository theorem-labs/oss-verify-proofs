(* SPDX-License-Identifier: MIT *)
(* The ASan image's start-up certificates made again for LPS 727298f3, by the
   method of jsoncons/fuzz_bigint's As0CertK_{root,201,202}.v (OSSV-343's certificate-data-method):
   the recorded plans of StartupPlanAsan.v / StartupPlan2Asan.v renumbered by [psh] with the map read
   off this unit's probe of the run ([vsh_asan], below), every hand-off state computed here by
   [collect_handoffs], and each certificate proved at rz = 0 and at rz = 1.  The splits on [e_atr8]
   are moved by [atr8_shift rz] ([PlanRegen.pmid]: the auxv is [AUXSZ rz] bytes, not 160).  The
   recorded hand-off states of the old launch are not read.
   A result shape is never computed into a term: [SH_X r] is [shape_of] of the run itself, and one
   boolean per segment and rz ([cres_holes], checked by the kernel's VM at Qed) gives both the
   certificate and [only_holes] of its shape.  (Reading a shape back into a term took 918 s for the
   root segment alone, against 53 s for the run.) *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin StartupPlanAsan StartupPlan2Asan PlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* The checker's extension tables are empty here: [run_*] passes [fun _ _ _ => None] where
   AsanStartup names them XE0 / XB0 (the same functions), so this file does not wait on AsanStartup. *)

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.

(** the renumbering, read off the probe of the run (notes/probe-simdjson__fuzz_minifyimpl.md) *)
Definition VSTEPS_asan : list (nat * nat) := [(78%nat, 4%nat); (310%nat, 2%nat)].
Definition vsh_asan : nat -> nat := vsteps VSTEPS_asan.

(** a result shape whose every leaf is a hand-off hole *)
Fixpoint only_holes (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SAlt2 a b | SCase _ _ a b => only_holes a && only_holes b
  | SNil | SExit _ | SEmitP _ _ _ | SNext => false
  end.

(** the shape of a certificate's result, and the one test each certificate is proved by *)
Definition shape_of (c : cres) : shape := match c with COk s => s | CErr _ _ _ => SNil end.
Definition cres_holes (c : cres) : bool := match c with COk s => only_holes s | CErr _ _ _ => false end.
Lemma cres_holes_ok : forall c, cres_holes c = true -> c = COk (shape_of c) /\ only_holes (shape_of c) = true.
Proof. intros [s | code p cs] H; cbn [cres_holes shape_of] in *; [split; [reflexivity | exact H] | discriminate H]. Qed.

(** segment root *)
Definition IT_0 : itab := mk_itab_ranges ASEGS startup_plan_ranges_0.
Lemma IT_0_ok : itab_sound ASEGS IT_0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition PL_0 (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh_asan startup_plan).
Definition ST_0 (r : Z) : acs := (asan_init r).
Definition NX_0 (r : Z) : nat := NX0.
Definition run_0 (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS IT_0 ASAN (NX_0 r) AsanInit.LIMIT r (XNS ASEGS ASAN (NX_0 r) AsanInit.LIMIT) (fun _ _ _ => None) (fun _ _ _ => None) js KC0 BFUEL FUEL None (ST_0 r) (PL_0 r).
Definition HSL_0_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 4 (run_0 0) [].
Definition HSL_0_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 4 (run_0 1) [].
Definition HSL_0 (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_0_1 else HSL_0_0.
Definition SH_0 (r : Z) : shape := shape_of (run_0 r (hlookup (HSL_0 r))).
Lemma ok_0_0 : cres_holes (run_0 0 (hlookup HSL_0_0)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_0_1 : cres_holes (run_0 1 (hlookup HSL_0_1)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_0 : forall r, 0 <= r <= 1 -> cres_holes (run_0 r (hlookup (HSL_0 r))) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact ok_0_0 | exact ok_0_1]. Qed.
Lemma cert_0 : forall r, 0 <= r <= 1 -> run_0 r (hlookup (HSL_0 r)) = COk (SH_0 r).
Proof. intros r Hr. unfold SH_0. exact (proj1 (cres_holes_ok (run_0 r (hlookup (HSL_0 r))) (ok_0 r Hr))). Qed.
Lemma holes_0 : forall r, 0 <= r <= 1 -> only_holes (SH_0 r) = true.
Proof. intros r Hr. unfold SH_0. exact (proj2 (cres_holes_ok (run_0 r (hlookup (HSL_0 r))) (ok_0 r Hr))). Qed.
Lemma keys_0 : forall r, 0 <= r <= 1 -> map fst (HSL_0 r) = [10%nat].
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma nx_A_ge : forall r, 0 <= r <= 1 -> (NX0 <= nxt (hstate (HSL_0 r) (ST_0 r) 10))%nat.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; lia. Qed.

(** segment A *)
Definition IT_A : itab := mk_itab_ranges ASEGS startup_plan_ranges_A.
Lemma IT_A_ok : itab_sound ASEGS IT_A.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition PL_A (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh_asan startup_plan_segA).
Definition ST_A (r : Z) : acs := hstate (HSL_0 r) (ST_0 r) 10.
Definition NX_A (r : Z) : nat := nxt (ST_A r).
Definition run_A (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS IT_A ASAN (NX_A r) AsanInit.LIMIT r (XNS ASEGS ASAN (NX_A r) AsanInit.LIMIT) (fun _ _ _ => None) (fun _ _ _ => None) js KC0 BFUEL FUEL None (ST_A r) (PL_A r).
Definition HSL_A_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 6 (run_A 0) [].
Definition HSL_A_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 6 (run_A 1) [].
Definition HSL_A (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_A_1 else HSL_A_0.
Definition SH_A (r : Z) : shape := shape_of (run_A r (hlookup (HSL_A r))).
Lemma ok_A_0 : cres_holes (run_A 0 (hlookup HSL_A_0)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_A_1 : cres_holes (run_A 1 (hlookup HSL_A_1)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_A : forall r, 0 <= r <= 1 -> cres_holes (run_A r (hlookup (HSL_A r))) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact ok_A_0 | exact ok_A_1]. Qed.
Lemma cert_A : forall r, 0 <= r <= 1 -> run_A r (hlookup (HSL_A r)) = COk (SH_A r).
Proof. intros r Hr. unfold SH_A. exact (proj1 (cres_holes_ok (run_A r (hlookup (HSL_A r))) (ok_A r Hr))). Qed.
Lemma holes_A : forall r, 0 <= r <= 1 -> only_holes (SH_A r) = true.
Proof. intros r Hr. unfold SH_A. exact (proj2 (cres_holes_ok (run_A r (hlookup (HSL_A r))) (ok_A r Hr))). Qed.
Lemma keys_A : forall r, 0 <= r <= 1 -> map fst (HSL_A r) = [11%nat].
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma nx_B_ge : forall r, 0 <= r <= 1 -> (NX0 <= nxt (hstate (HSL_A r) (ST_A r) 11))%nat.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; lia. Qed.

(** segment B *)
Definition IT_B : itab := mk_itab_ranges ASEGS startup_plan_ranges_B.
Lemma IT_B_ok : itab_sound ASEGS IT_B.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition PL_B (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh_asan startup_plan_segB).
Definition ST_B (r : Z) : acs := hstate (HSL_A r) (ST_A r) 11.
Definition NX_B (r : Z) : nat := nxt (ST_B r).
Definition run_B (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS IT_B ASAN (NX_B r) AsanInit.LIMIT r (XNS ASEGS ASAN (NX_B r) AsanInit.LIMIT) (fun _ _ _ => None) (fun _ _ _ => None) js KC0 BFUEL FUEL None (ST_B r) (PL_B r).
Definition HSL_B_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 40 (run_B 0) [].
Definition HSL_B_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 40 (run_B 1) [].
Definition HSL_B (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_B_1 else HSL_B_0.
Definition SH_B (r : Z) : shape := shape_of (run_B r (hlookup (HSL_B r))).
Lemma ok_B_0 : cres_holes (run_B 0 (hlookup HSL_B_0)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_B_1 : cres_holes (run_B 1 (hlookup HSL_B_1)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_B : forall r, 0 <= r <= 1 -> cres_holes (run_B r (hlookup (HSL_B r))) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact ok_B_0 | exact ok_B_1]. Qed.
Lemma cert_B : forall r, 0 <= r <= 1 -> run_B r (hlookup (HSL_B r)) = COk (SH_B r).
Proof. intros r Hr. unfold SH_B. exact (proj1 (cres_holes_ok (run_B r (hlookup (HSL_B r))) (ok_B r Hr))). Qed.
Lemma holes_B : forall r, 0 <= r <= 1 -> only_holes (SH_B r) = true.
Proof. intros r Hr. unfold SH_B. exact (proj2 (cres_holes_ok (run_B r (hlookup (HSL_B r))) (ok_B r Hr))). Qed.
Lemma keys_B : forall r, 0 <= r <= 1 -> map fst (HSL_B r) = [12%nat].
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma nx_C_ge : forall r, 0 <= r <= 1 -> (NX0 <= nxt (hstate (HSL_B r) (ST_B r) 12))%nat.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; lia. Qed.

(** segment C *)
Definition IT_C : itab := mk_itab_ranges ASEGS startup_plan_ranges_C.
Lemma IT_C_ok : itab_sound ASEGS IT_C.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition PL_C (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh_asan startup_plan_segC).
Definition ST_C (r : Z) : acs := hstate (HSL_B r) (ST_B r) 12.
Definition NX_C (r : Z) : nat := nxt (ST_C r).
Definition run_C (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS IT_C ASAN (NX_C r) AsanInit.LIMIT r (XNS ASEGS ASAN (NX_C r) AsanInit.LIMIT) (fun _ _ _ => None) (fun _ _ _ => None) js KC0 BFUEL FUEL None (ST_C r) (PL_C r).
Definition HSL_C_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 12 (run_C 0) [].
Definition HSL_C_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 12 (run_C 1) [].
Definition HSL_C (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_C_1 else HSL_C_0.
Definition SH_C (r : Z) : shape := shape_of (run_C r (hlookup (HSL_C r))).
Lemma ok_C_0 : cres_holes (run_C 0 (hlookup HSL_C_0)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_C_1 : cres_holes (run_C 1 (hlookup HSL_C_1)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_C : forall r, 0 <= r <= 1 -> cres_holes (run_C r (hlookup (HSL_C r))) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact ok_C_0 | exact ok_C_1]. Qed.
Lemma cert_C : forall r, 0 <= r <= 1 -> run_C r (hlookup (HSL_C r)) = COk (SH_C r).
Proof. intros r Hr. unfold SH_C. exact (proj1 (cres_holes_ok (run_C r (hlookup (HSL_C r))) (ok_C r Hr))). Qed.
Lemma holes_C : forall r, 0 <= r <= 1 -> only_holes (SH_C r) = true.
Proof. intros r Hr. unfold SH_C. exact (proj2 (cres_holes_ok (run_C r (hlookup (HSL_C r))) (ok_C r Hr))). Qed.
Lemma keys_C : forall r, 0 <= r <= 1 -> map fst (HSL_C r) = [0%nat].
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.
Lemma nx_2_ge : forall r, 0 <= r <= 1 -> (NX0 <= nxt (hstate (HSL_C r) (ST_C r) 0))%nat.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute; lia. Qed.

(** segment S2 *)
Definition IT_2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma IT_2_ok : itab_sound ASEGS IT_2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition PL_2 (r : Z) : plan := pmid e_atr8 (atr8_shift r) (psh vsh_asan startup2_plan).
Definition ST_2 (r : Z) : acs := hstate (HSL_C r) (ST_C r) 0.
Definition NX_2 (r : Z) : nat := nxt (ST_2 r).
Definition run_2 (r : Z) (js : nat -> option acs) : cres :=
  check ASEGS IT_2 ASAN (NX_2 r) AsanInit.LIMIT r (XNS ASEGS ASAN (NX_2 r) AsanInit.LIMIT) (fun _ _ _ => None) (fun _ _ _ => None) js KC0 BFUEL FUEL None (ST_2 r) (PL_2 r).
Definition HSL_2_0 : list (nat * acs) := Eval vm_compute in collect_handoffs 12 (run_2 0) [].
Definition HSL_2_1 : list (nat * acs) := Eval vm_compute in collect_handoffs 12 (run_2 1) [].
Definition HSL_2 (r : Z) : list (nat * acs) := if Z.eqb r 1 then HSL_2_1 else HSL_2_0.
Definition SH_2 (r : Z) : shape := shape_of (run_2 r (hlookup (HSL_2 r))).
Lemma ok_2_0 : cres_holes (run_2 0 (hlookup HSL_2_0)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_2_1 : cres_holes (run_2 1 (hlookup HSL_2_1)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ok_2 : forall r, 0 <= r <= 1 -> cres_holes (run_2 r (hlookup (HSL_2 r))) = true.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact ok_2_0 | exact ok_2_1]. Qed.
Lemma cert_2 : forall r, 0 <= r <= 1 -> run_2 r (hlookup (HSL_2 r)) = COk (SH_2 r).
Proof. intros r Hr. unfold SH_2. exact (proj1 (cres_holes_ok (run_2 r (hlookup (HSL_2 r))) (ok_2 r Hr))). Qed.
Lemma holes_2 : forall r, 0 <= r <= 1 -> only_holes (SH_2 r) = true.
Proof. intros r Hr. unfold SH_2. exact (proj2 (cres_holes_ok (run_2 r (hlookup (HSL_2 r))) (ok_2 r Hr))). Qed.
(** the main phase starts at hand-offs 1 and 2 only (the table's order is [hupd]'s, not fixed here) *)
Lemma keys_2 : forall r, 0 <= r <= 1 -> forall h, In h (map fst (HSL_2 r)) -> h = 1%nat \/ h = 2%nat.
Proof. intros r Hr h Hin. assert (r = 0 \/ r = 1) as [-> | ->] by lia; vm_compute in Hin; lia. Qed.
