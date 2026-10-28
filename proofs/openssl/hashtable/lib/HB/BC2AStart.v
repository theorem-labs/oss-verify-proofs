(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CxPlan HBPlanImage HBAtable BC1HS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import CAP. Open Scope Z_scope.
Definition c2_kids (cs : acs) : bool * acs * acs := match node_brk2 HAT NX0 AsanInit.LIMIT cs with Some r => r | None => (true, cs, cs) end.
Definition c2b_start0_ (_ : unit) : acs := snd (fst (c2_kids c1_hs0)).
Abbreviation c2b_start0 := (c2b_start0_ tt).
Definition c2a_start0_ (_ : unit) : acs := snd (c2_kids c1_hs0).
Abbreviation c2a_start0 := (c2a_start0_ tt).
Definition c2b_start1_ (_ : unit) : acs := snd (fst (c2_kids c1_hs1)).
Abbreviation c2b_start1 := (c2b_start1_ tt).
Definition c2a_start1_ (_ : unit) : acs := snd (c2_kids c1_hs1).
Abbreviation c2a_start1 := (c2a_start1_ tt).
Lemma c1_hs0_brk2 : node_brk2 HAT NX0 AsanInit.LIMIT c1_hs0 = Some (false, c2b_start0, c2a_start0).
Proof. vm_compute. reflexivity. Qed.
Lemma c1_hs1_brk2 : node_brk2 HAT NX0 AsanInit.LIMIT c1_hs1 = Some (false, c2b_start1, c2a_start1).
Proof. vm_compute. reflexivity. Qed.
Lemma c1_hs0_ecall : is_ecall_at HASEGS c1_hs0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1_hs1_ecall : is_ecall_at HASEGS c1_hs1 = true. Proof. vm_compute. reflexivity. Qed.
