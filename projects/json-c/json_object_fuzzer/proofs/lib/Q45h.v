(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main-entry states of both CONFIG_RSEQ values in HSCLASS_S, HS2s indexed by the value, HSCLASS_R with HS2s_class_R for the states of one value, and the map objects OBJS_W read from the computed states' maps). *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUwk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUwk.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition HSCLASS_S (w : bool) (ch : acs) : Prop :=
if w then ch = HS2sA_1 \/ ch = HS2sA_2 \/ ch = HS2sA_1R \/ ch = HS2sA_2R
else ch = HS2sB_3 \/ ch = HS2sB_4 \/ ch = HS2sB_3R \/ ch = HS2sB_4R.

Definition HS2s (r : Z) (h : nat) : option acs := match HS2sA r h with Some c => Some c | None => HS2sB r h end.
Lemma HS2s_class : forall r h ch, HS2s r h = Some ch -> exists w, HSCLASS_S w ch.
Proof.
intros r h ch H. unfold HS2s, HS2sA, HS2sB in H. revert H.
destruct (Z.eqb r 1); destruct h as [|[|[|[|[|h]]]]]; intros H; cbv beta iota in H; try discriminate H; injection H as <-;
[exists true; right; right; left | exists true; right; right; right | exists false; right; right; left | exists false; right; right; right
|exists true; left | exists true; right; left | exists false; left | exists false; right; left];
reflexivity.
Qed.

(* the main-entry states of one CONFIG_RSEQ value b: the states a run at that value hands main *)
Definition HSCLASS_R (b w : bool) (ch : acs) : Prop :=
if b then (if w then ch = HS2sA_1R \/ ch = HS2sA_2R else ch = HS2sB_3R \/ ch = HS2sB_4R)
else (if w then ch = HS2sA_1 \/ ch = HS2sA_2 else ch = HS2sB_3 \/ ch = HS2sB_4).
Lemma HSCLASS_R_S : forall b w ch, HSCLASS_R b w ch -> HSCLASS_S w ch.
Proof.
intros [|] [|] ch [-> | ->];
[right; right; left | right; right; right | right; right; left | right; right; right
|left | right; left | left | right; left]; reflexivity.
Qed.
Lemma HS2s_class_R : forall b h ch, HS2s (rseq_z b) h = Some ch -> exists w, HSCLASS_R b w ch.
Proof.
intros b h ch H. unfold HS2s, HS2sA, HS2sB in H. revert H.
destruct b; destruct h as [|[|[|[|[|h]]]]]; intros H; cbn [rseq_z Z.eqb Pos.eqb] in H; try discriminate H; injection H as <-;
[exists true; left | exists true; right | exists false; left | exists false; right
|exists true; left | exists true; right | exists false; left | exists false; right]; reflexivity.
Qed.

Definition MAPS_A : list amap := Eval vm_compute in a_maps HS2sA_1.
Definition MAPS_B : list amap := Eval vm_compute in a_maps HS2sB_3.
Definition MAPS_W (w : bool) : list amap := if w then MAPS_A else MAPS_B.
Lemma MAPS_W_eq : forall w ch, HSCLASS_S w ch -> a_maps ch = MAPS_W w.
Proof. intros [|] ch [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. Qed.
Lemma MAPS_W_exact : forall w, forallb (fun m => negb (is_fog m)) (MAPS_W w) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition e_high (E : env) : word * word := (edenot E (ELit 2201439137792), edenot E (ELit 15392894357504)).
Definition e_gap (E : env) : word * word := (edenot E (ELit 2415882240), edenot E (ELit 2199023255552)).
Definition e_low (E : env) : word * word := (edenot E (ELit 2147446784), edenot E (ELit 268435456)).

(* the objects the main-entry states map, (v, n) for a region of n bytes at 4096 * EVar v, read off the
   computed maps in their order *)
Definition obj_of (m : amap) : list (nat * Z) :=
match am_base m, am_len m with
| EMd Instr.M_MUL (ELit 4096) (EVar v), ELit n => [(v, n)]
| _, _ => []
end.
Definition OBJS_A : list (nat * Z) := Eval vm_compute in flat_map obj_of MAPS_A.
Definition OBJS_B : list (nat * Z) := Eval vm_compute in flat_map obj_of MAPS_B.
Definition OBJS_W (w : bool) : list (nat * Z) := if w then OBJS_A else OBJS_B.
Definition obj_e (E : env) (o : nat * Z) : word * word := (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar (fst o))), edenot E (ELit (snd o))).

Lemma MAPS_W_objs : forall w E, map (amap_den E) (MAPS_W w) = map (obj_e E) (OBJS_W w) ++ [e_high E; e_gap E; e_low E].
Proof. intros [|] E; reflexivity. Qed.

Lemma main_maps_S : forall w E l, maps_match E (MAPS_W w) l -> l = map (obj_e E) (OBJS_W w) ++ [e_high E; e_gap E; e_low E].
Proof. intros w E l H. rewrite (maps_match_nofog E _ l (MAPS_W_exact w) H). apply MAPS_W_objs. Qed.
