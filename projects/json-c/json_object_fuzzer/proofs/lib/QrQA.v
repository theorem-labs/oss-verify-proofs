(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUwk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUwk.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition HSCLASS_S (w : bool) (ch : acs) : Prop :=
if w then ch = HS2sA_1 \/ ch = HS2sA_2 else ch = HS2sB_3 \/ ch = HS2sB_4.

Definition HS2s (h : nat) : option acs := match HS2sA h with Some c => Some c | None => HS2sB h end.
Lemma HS2s_class : forall h ch, HS2s h = Some ch -> exists w, HSCLASS_S w ch.
Proof.
intros h ch H. unfold HS2s, HS2sA, HS2sB in H.
destruct h as [|[|[|[|[|h]]]]]; cbn in H; try discriminate; injection H as <-;
[exists true; left | exists true; right | exists false; left | exists false; right]; reflexivity.
Qed.

Definition MAPS_A : list amap := Eval vm_compute in a_maps HS2sA_1.
Definition MAPS_B : list amap := Eval vm_compute in a_maps HS2sB_3.
Definition MAPS_W (w : bool) : list amap := if w then MAPS_A else MAPS_B.
Lemma MAPS_W_eq : forall w ch, HSCLASS_S w ch -> a_maps ch = MAPS_W w.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.
Lemma MAPS_W_exact : forall w, forallb (fun m => negb (is_fog m)) (MAPS_W w) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition e_high (E : env) : word * word := (edenot E (ELit 2201439137792), edenot E (ELit 15392894357504)).
Definition e_gap (E : env) : word * word := (edenot E (ELit 2415882240), edenot E (ELit 2199023255552)).
Definition e_low (E : env) : word * word := (edenot E (ELit 2147446784), edenot E (ELit 268435456)).

Definition OBJS_W (w : bool) : list (nat * Z) :=
[(2129%nat, 4096); (496%nat, 4096); (479%nat, 8388608); (478%nat, 1048576)]
++ (if w then [(423%nat, 4096); (5%nat, 8192)] else [(424%nat, 4096); (423%nat, 8192)])
++ [(406%nat, 11571200); (330%nat, 4096); (265%nat, 4096); (238%nat, 65536); (237%nat, 4096); (236%nat, 8388608);
(208%nat, 137439023104); (207%nat, 3727360); (78%nat, 65536)].
Definition obj_e (E : env) (o : nat * Z) : word * word := (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar (fst o))), edenot E (ELit (snd o))).

Lemma MAPS_W_objs : forall w E, map (amap_den E) (MAPS_W w) = map (obj_e E) (OBJS_W w) ++ [e_high E; e_gap E; e_low E].
Proof. intros [|] E; reflexivity. Qed.

Lemma main_maps_S : forall w E l, maps_match E (MAPS_W w) l -> l = map (obj_e E) (OBJS_W w) ++ [e_high E; e_gap E; e_low E].
Proof. intros w E l H. rewrite (maps_match_nofog E _ l (MAPS_W_exact w) H). apply MAPS_W_objs. Qed.
