(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngZ.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ.AxScChk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0rz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0rz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_nprz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_nprz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ng0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ng0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Abbreviation SEGS := Asan.M.loaded_segments.
Ltac zlh H := clear - H; lia.
Definition ca_place (CA : Z) : Prop := (4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA.
Definition LOW : iv := (4304, 61648).
Definition HIGH : iv := (6529232, 2^47).
Definition B47 : iv := (4194304, 2^47).
Ltac zat R := repeat match goal with |- context [bv_unsigned (ev (Ez R ?V) ?n)] =>
              lazymatch eval cbn in (Nat.ltb n 32) with
              | true => change (bv_unsigned (ev (Ez R V) n)) with (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat n))))
              | false => let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by lia
              end end.
Ltac fact_go R HSPa HX HH :=
  try unfold rf_ok; try unfold df_ok; try unfold LOW; try unfold HIGH; try unfold B47; cbn [fst snd zeval edenot]; zat R; rewrite ?HSPa, ?HX; zlh HH.
Ltac facts_go R HSPa HX HH := repeat (first [apply Forall_nil | apply Forall_cons; [fact_go R HSPa HX HH|]]).
Ltac sc_refl rf df R HSPa HX HH :=
  apply (scs_chk_sound rf df); [ facts_go R HSPa HX HH | facts_go R HSPa HX HH | vm_compute; reflexivity ].
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SCS.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variables (SPa CA ND SB RIB : Z).
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis HCA : ca_place CA /\ CA + 2592 + 256 <= SPa /\ 2^46 <= SPa <= 2^47.
Hypothesis HRI : 4194304 <= RIB /\ RIB + 4096 + 256 <= SPa.
Hypothesis HSEP : CA + 2592 <= RIB \/ RIB + 4096 <= CA.

(* [comment removed for export] *)
#[using="SPa HSPa HND HCA"] Lemma sc_np0p_p : forall cnt sz cp st, 1 <= cnt <= 16 ->
  scs_denot SEGS m (Ez R (AXF_np0z.VALS_np0 CA ND cnt sz cp SB st)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_np0z.AXF_np0.RES_pnp0p)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA : LiaFast.U) => LiaFast.u0).
  intros cnt sz cp st Hc. unfold AXF_np0z.VALS_np0. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP]; assert (HH := conj HP (conj HC2 (conj HND Hc))).
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (1, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA"] Lemma sc_np0r_p : forall sz st,
  scs_denot SEGS m (Ez R (AXF_np0rz.VALS_np0r CA ND 0 sz SB st)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_np0rz.AXF_np0r.RES_pnp0r)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA : LiaFast.U) => LiaFast.u0).
  intros sz st. unfold AXF_np0rz.VALS_np0r. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP]; assert (HH := conj HP (conj HC2 HND)).
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (0, 0))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (0, 0))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA"] Lemma sc_npr_p : forall mc, 2 <= mc <= 16 ->
  scs_denot SEGS m (Ez R (AXF_nprz.VALS_npr CA ND mc)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_nprz.AXF_npr.RES_pnpr)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA : LiaFast.U) => LiaFast.u0).
  intros mc Hmc. unfold AXF_nprz.VALS_npr. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP]; assert (HH := conj HP (conj HC2 (conj HND Hmc))).
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (2, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
  - sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (2, 16))] [(EVar 2, EVar 32, 2848)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI HSEP"] Lemma sc_ng0_p : forall n nf, 1 <= n <= 8 -> n <= nf <= 16384 ->
  scs_denot SEGS m (Ez R (AXF_ng0z.VALS_ng0 CA ND n SB RIB nf)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_ng0z.AXF_ng0.RES_png0)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI HSEP : LiaFast.U) => LiaFast.u0).
  intros n nf Hn Hnf. unfold AXF_ng0z.VALS_ng0. destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP].
  - assert (HH := conj HP (conj HC2 (conj HND (conj Hn (conj Hnf HRI))))).
    sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))]
            [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
  - destruct HSEP as [HD|HD]; assert (HH := conj HD (conj HP (conj HC2 (conj HND (conj Hn (conj Hnf HRI)))))).
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47); (EVar 37, (1, 16384))]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 37, EVar 34, 0); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
#[using="SPa HSPa HND HCA HRI HSEP"] Lemma sc_ngt_p : forall n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, 1 <= n <= 8 ->
  scs_denot SEGS m (Ez R (AXF_ngtz.VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXF_ngtz.AXF_ngt.RES_pngt)).
Proof. LiaFast.lf_pins (fun (SPa HSPa HND HCA HRI HSEP : LiaFast.U) => LiaFast.u0).
  intros n na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra Hn. unfold AXF_ngtz.VALS_ngt.
  destruct HCA as (HP & HC2). unfold ca_place in HP.
  destruct HP as [HP|HP].
  - assert (HH := conj HP (conj HC2 (conj HND (conj Hn HRI)))).
    sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, LOW); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47)]
            [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
  - destruct HSEP as [HD|HD]; assert (HH := conj HD (conj HP (conj HC2 (conj HND (conj Hn HRI))))).
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47)]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 36, EVar 32, 2592)] R HSPa HSPa HH.
    + sc_refl [(EVar 2, (2^46, 2^47)); (EVar 32, HIGH); (EVar 33, (33, 512)); (EVar 34, (1, 8)); (EVar 36, B47)]
              [(EVar 2, EVar 32, 2848); (EVar 2, EVar 36, 4352); (EVar 32, EVar 36, 4096)] R HSPa HSPa HH.
Qed.
End SCS.
