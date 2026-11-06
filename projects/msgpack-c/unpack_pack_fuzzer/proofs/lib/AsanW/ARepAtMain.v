(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase AProto ALayout ARep ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainExport MainFactsAsan MainEntry.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module MF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainFactsAsan.
Module MA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.

Definition VL (V : nat -> Z) (n : nat) : Z :=
  match n with
  | 240%nat => V 227%nat | 241%nat => V 228%nat | 221%nat => V 208%nat | 222%nat => V 209%nat | 239%nat => V 226%nat
  | 485%nat => V 453%nat | 486%nat => V 454%nat | 406%nat => V 377%nat | 323%nat => V 310%nat | 91%nat => V 78%nat | 220%nat => V 207%nat

  | 584%nat => V 471%nat | 503%nat => V 245%nat | 258%nat => V 245%nat
  | 6%nat => 256 * V 10%nat + V 6%nat
  | _ => V n
  end.
Definition L0 (V : nat -> Z) (w : bool) (U : list (list Z)) : alayout := mkALayout (VL V) w U.

Definition usum (U : list (list Z)) : Z := fold_right (fun u s => Z.of_nat (length u) + 1 + s) 0 U.
Definition univ_ok (U : list (list Z)) : Prop := (length U <= 4096)%nat /\ usum U + 8 <= 2 ^ 20.

Definition usp_pin {rc : runConstT} (V : nat -> Z) : Prop := 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = ATOP + 8388608.

Section AtMain.
Context {rc : runConstT}.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis HMF : Forall (ME.mfact_ok asegs V m) MF.asan_mem_facts.
Hypothesis HMFw : Forall (ME.mfact_ok asegs V m) (MA.asan_mem_facts_w w).
Hypothesis HPF : Forall (ME.pfact_ok V) MF.asan_pure_facts.
Hypothesis MINV : mem_inv asegs m.

Hypothesis HUSP : usp_pin V.
Hypothesis HSH0 : MA.ashadow0 V m.
Hypothesis HU : univ_ok U.

Let L := L0 V w U.

Lemma hf : forall f, existsb (ME.mfact_eqb f) MF.asan_mem_facts = true -> ME.mfact_ok asegs V m f.
Proof. intros f H. exact (ME.mfact_find asegs V m _ f HMF H). Qed.
Lemma hp : forall k f, nth_error MF.asan_pure_facts k = Some f -> ME.pfact_ok V f.
Proof. intros k f H. exact (proj1 (Forall_forall _ _) HPF f (nth_error_In _ _ H)). Qed.

Ltac hcell A W X :=
  let H := fresh "HC" in
  pose proof (hf (ME.MCell (ME.ZLit A) W (ME.ZLit X)) ltac:(vm_compute; reflexivity)) as H;
  cbn [ME.mfact_ok ME.zv ME.cellw] in H.

Lemma himg : forall lo hi, existsb (fun f => match f with ME.MImg lo' hi' => (lo' <=? lo) && (hi <=? hi') | _ => false end) MF.asan_mem_facts = true ->
  forall i, lo <= i < hi -> m (wa i) = None.
Proof. intros lo hi H. exact (ME.mimg_cover asegs V m _ lo hi HMF H). Qed.

Lemma bytes_eq_unsigned : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma rt1 : rw_cells asegs m 857336 [C8 (Z_to_bv 64 1480032)].
Proof.
  assert (K0 : rw_cells asegs m 857336 [C8 (Z_to_bv 64 1480032)]).
  { apply (rw_cells_recast asegs m 857336 [CB 8%nat [Z_to_bv 8 96; Z_to_bv 8 149; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857336 [Z_to_bv 8 96; Z_to_bv 8 149; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt2 : rw_cells asegs m 857352 [C8 (Z_to_bv 64 1488360); C8 (Z_to_bv 64 881336); C8 (Z_to_bv 64 891576); C8 (Z_to_bv 64 894888); C8 (Z_to_bv 64 894896); C8 (Z_to_bv 64 894880)].
Proof.
  assert (K0 : rw_cells asegs m 857352 [C8 (Z_to_bv 64 1488360)]).
  { apply (rw_cells_recast asegs m 857352 [CB 8%nat [Z_to_bv 8 232; Z_to_bv 8 181; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857352 [Z_to_bv 8 232; Z_to_bv 8 181; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 857360 [C8 (Z_to_bv 64 881336)]).
  { apply (rw_cells_recast asegs m 857360 [CB 8%nat [Z_to_bv 8 184; Z_to_bv 8 114; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857360 [Z_to_bv 8 184; Z_to_bv 8 114; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells asegs m 857368 [C8 (Z_to_bv 64 891576)]).
  { apply (rw_cells_recast asegs m 857368 [CB 8%nat [Z_to_bv 8 184; Z_to_bv 8 154; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857368 [Z_to_bv 8 184; Z_to_bv 8 154; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells asegs m 857376 [C8 (Z_to_bv 64 894888)]).
  { apply (rw_cells_recast asegs m 857376 [CB 8%nat [Z_to_bv 8 168; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857376 [Z_to_bv 8 168; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K4 : rw_cells asegs m 857384 [C8 (Z_to_bv 64 894896)]).
  { apply (rw_cells_recast asegs m 857384 [CB 8%nat [Z_to_bv 8 176; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857384 [Z_to_bv 8 176; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K5 : rw_cells asegs m 857392 [C8 (Z_to_bv 64 894880)]).
  { apply (rw_cells_recast asegs m 857392 [CB 8%nat [Z_to_bv 8 160; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857392 [Z_to_bv 8 160; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K3|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K4|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K5.
Qed.

Lemma rt3 : rw_cells asegs m 857400 [C8 (Z_to_bv 64 865320)].
Proof.
  assert (K0 : rw_cells asegs m 857400 [C8 (Z_to_bv 64 865320)]).
  { apply (rw_cells_recast asegs m 857400 [CB 8%nat [Z_to_bv 8 40; Z_to_bv 8 52; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857400 [Z_to_bv 8 40; Z_to_bv 8 52; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt4 : rw_cells asegs m 860288 [C8 (Z_to_bv 64 894873)].
Proof.
  assert (K0 : rw_cells asegs m 860288 [C8 (Z_to_bv 64 894873)]).
  { apply (rw_cells_recast asegs m 860288 [CB 8%nat [Z_to_bv 8 153; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 860288 [Z_to_bv 8 153; Z_to_bv 8 167; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt5 : rw_cells asegs m 860528 [C8 (Z_to_bv 64 16)].
Proof.
  assert (K0 : rw_cells asegs m 860528 [C8 (Z_to_bv 64 16)]).
  { apply (rw_cells_recast asegs m 860528 [CB 8%nat [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 860528 [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt6 : rw_cells asegs m 865312 [C8 (Z_to_bv 64 816288); C8 (Z_to_bv 64 817316)].
Proof.
  assert (K0 : rw_cells asegs m 865312 [C8 (Z_to_bv 64 816288)]).
  { apply (rw_cells_recast asegs m 865312 [CB 8%nat [Z_to_bv 8 160; Z_to_bv 8 116; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865312 [Z_to_bv 8 160; Z_to_bv 8 116; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 865320 [C8 (Z_to_bv 64 817316)]).
  { apply (rw_cells_recast asegs m 865320 [CB 8%nat [Z_to_bv 8 164; Z_to_bv 8 120; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865320 [Z_to_bv 8 164; Z_to_bv 8 120; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rt7 : rw_cells asegs m 881272 [C8 (Z_to_bv 64 1099511627776); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048); C1 (Z_to_bv 8 1)].
Proof.
  hcell 881272 8%nat 1099511627776. rename HC into K0.
  hcell 881280 2%nat 16. rename HC into K1.
  hcell 881282 2%nat 2048. rename HC into K2.
  hcell 881284 1%nat 1. rename HC into K3.
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma rt8 : rw_cells asegs m 881336 [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 1024); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 2048)].
Proof.
  hcell 881336 4%nat 4294967295. rename HC into K0.
  hcell 881340 4%nat 256. rename HC into K1.
  hcell 881344 4%nat 1024. rename HC into K2.
  hcell 881348 4%nat 16. rename HC into K3.
  hcell 881352 4%nat 2048. rename HC into K4.
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K3|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K4.
Qed.

Lemma rt9 : rw_cells asegs m 881380 [C4 (Z_to_bv 64 4096); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 190)].
Proof.
  hcell 881380 4%nat 4096. rename HC into K0.
  hcell 881384 8%nat 816043786240. rename HC into HW1.
  apply (rw_cells_recast asegs m 881384 _ [C4 (Z_to_bv 64 0); CB 4%nat [Z_to_bv 8 190; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW1; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW1 as [HW1 _].
  rename HW1 into K1.
  hcell 881384 8%nat 816043786240. rename HC into HW2.
  apply (rw_cells_recast asegs m 881384 _ [CB 4%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (Z_to_bv 64 190)]) in HW2; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW2 as [_ HW2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW2.
  rename HW2 into K2.
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma rt10 : rw_cells asegs m 881421 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 881416 8%nat 72340172838010881. rename HC into HW0.
  apply (rw_cells_recast asegs m 881416 _ [CB 5%nat [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1]; C1 (Z_to_bv 8 1); CB 2%nat [Z_to_bv 8 1; Z_to_bv 8 1]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma rt11 : rw_cells asegs m 891576 [C8 (Z_to_bv 64 2147450880)].
Proof.
  hcell 891576 8%nat 2147450880. rename HC into K0.
  exact K0.
Qed.

Lemma rt12 : rw_cells asegs m 889628 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 889628 1%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rt13 : rw_cells asegs m 889632 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 889632 1%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rt14 : rw_cells asegs m 889636 [C4 (Z_to_bv 64 0)].
Proof.
  hcell 889636 4%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma rt15 : rw_cells asegs m 894872 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof.
  hcell 894872 1%nat 1. rename HC into K0.
  hcell 894873 1%nat 1. rename HC into K1.
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rt16 : rw_cells asegs m 894880 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  hcell 894880 8%nat 140737488355327. rename HC into K0.
  assert (K1 : rw_cells asegs m 894888 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 894888 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 894888 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 894888 894904); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells asegs m 894896 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 894896 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 894896 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 894888 894904); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma rt17 : rw_cells asegs m 894908 [C4 (Z_to_bv 64 30)].
Proof.
  hcell 894908 4%nat 30. rename HC into K0.
  exact K0.
Qed.

Lemma rt19 : rw_cells asegs m 1480032 [C8 (Z_to_bv 64 4096)].
Proof.
  hcell 1480032 8%nat 4096. rename HC into K0.
  exact K0.
Qed.

Lemma rt20 : rw_cells asegs m 1488256 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells asegs m 1488256 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 1488256 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1488256 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1488255 1488352); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 1488264 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 1488264 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1488264 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1488255 1488352); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rt21 : rw_cells asegs m 1488392 [C8 (Z_to_bv 64 128849084416)].
Proof.
  hcell 1488392 8%nat 128849084416. rename HC into K0.
  exact K0.
Qed.

Lemma rt22 : rw_cells asegs m 1488394 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 1488392 8%nat 128849084416. rename HC into HW0.
  apply (rw_cells_recast asegs m 1488392 _ [CB 2%nat [Z_to_bv 8 0; Z_to_bv 8 0]; C1 (Z_to_bv 8 1); CB 5%nat [Z_to_bv 8 0; Z_to_bv 8 30; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma rt23 : rw_cells asegs m 1488480 [C8 (Z_to_bv 64 18446744073709551615)].
Proof.
  hcell 1488480 8%nat 18446744073709551615. rename HC into K0.
  exact K0.
Qed.

Lemma rt24 : rw_cells asegs m 6343720 [C8 (Z_to_bv 64 6479912)].
Proof.
  hcell 6343720 8%nat 6479912. rename HC into K0.
  exact K0.
Qed.

Lemma rt26 : rw_cells asegs m 6343824 [C4 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells asegs m 6343824 [C4 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 6343824 [CB 4%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 6343824 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 6343824 6343840); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtb1 : rw_cells asegs m 1488620 [C1 (Z_to_bv 8 0)].
Proof.
  hcell 1488616 8%nat 16843009. rename HC into HW0.
  apply (rw_cells_recast asegs m 1488616 _ [CB 4%nat [Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1]; C1 (Z_to_bv 8 0); CB 3%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma rtb2 : rw_cells asegs m 1488504 [C8 (Z_to_bv 64 0)].
Proof.
  hcell 1488504 8%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma rtb3 : rw_cells asegs m 865200 [C8 (Z_to_bv 64 797344)].
Proof.
  assert (K0 : rw_cells asegs m 865200 [C8 (Z_to_bv 64 797344)]).
  { apply (rw_cells_recast asegs m 865200 [CB 8%nat [Z_to_bv 8 160; Z_to_bv 8 42; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865200 [Z_to_bv 8 160; Z_to_bv 8 42; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc1 : rw_cells asegs m 865040 [C8 (Z_to_bv 64 814572); C8 (Z_to_bv 64 802012)].
Proof.
  assert (K0 : rw_cells asegs m 865040 [C8 (Z_to_bv 64 814572)]).
  { apply (rw_cells_recast asegs m 865040 [CB 8%nat [Z_to_bv 8 236; Z_to_bv 8 109; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865040 [Z_to_bv 8 236; Z_to_bv 8 109; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 865048 [C8 (Z_to_bv 64 802012)]).
  { apply (rw_cells_recast asegs m 865048 [CB 8%nat [Z_to_bv 8 220; Z_to_bv 8 60; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865048 [Z_to_bv 8 220; Z_to_bv 8 60; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rtc2 : rw_cells asegs m 865008 [C8 (Z_to_bv 64 838564)].
Proof.
  assert (K0 : rw_cells asegs m 865008 [C8 (Z_to_bv 64 838564)]).
  { apply (rw_cells_recast asegs m 865008 [CB 8%nat [Z_to_bv 8 164; Z_to_bv 8 203; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865008 [Z_to_bv 8 164; Z_to_bv 8 203; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc3 : rw_cells asegs m 865016 [C8 (Z_to_bv 64 801448)].
Proof.
  assert (K0 : rw_cells asegs m 865016 [C8 (Z_to_bv 64 801448)]).
  { apply (rw_cells_recast asegs m 865016 [CB 8%nat [Z_to_bv 8 168; Z_to_bv 8 58; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865016 [Z_to_bv 8 168; Z_to_bv 8 58; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc4 : rw_cells asegs m 865232 [C8 (Z_to_bv 64 818476)].
Proof.
  assert (K0 : rw_cells asegs m 865232 [C8 (Z_to_bv 64 818476)]).
  { apply (rw_cells_recast asegs m 865232 [CB 8%nat [Z_to_bv 8 44; Z_to_bv 8 125; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865232 [Z_to_bv 8 44; Z_to_bv 8 125; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc5 : rw_cells asegs m 864992 [C8 (Z_to_bv 64 816036)].
Proof.
  assert (K0 : rw_cells asegs m 864992 [C8 (Z_to_bv 64 816036)]).
  { apply (rw_cells_recast asegs m 864992 [CB 8%nat [Z_to_bv 8 164; Z_to_bv 8 115; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 864992 [Z_to_bv 8 164; Z_to_bv 8 115; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc6 : rw_cells asegs m 1488440 [C8 (Z_to_bv 64 4294967296)].
Proof.
  hcell 1488440 8%nat 4294967296. rename HC into K0.
  exact K0.
Qed.

Lemma rtc7 : rw_cells asegs m 1488608 [C8 (Z_to_bv 64 72340172838076673)].
Proof.
  hcell 1488608 8%nat 72340172838076673. rename HC into K0.
  exact K0.
Qed.

Lemma rtc8 : rw_cells asegs m 891584 [C4 (Z_to_bv 64 1)].
Proof.
  hcell 891584 4%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rtc9 : rw_cells asegs m 881432 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 881432 1%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rtc10 : rw_cells asegs m 1480024 [C4 (Z_to_bv 64 0)].
Proof.
  hcell 1480024 4%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma rtc11 : rw_cells asegs m 857336 [C8 (Z_to_bv 64 1480032); C8 (Z_to_bv 64 865376)].
Proof.
  assert (K0 : rw_cells asegs m 857336 [C8 (Z_to_bv 64 1480032)]).
  { apply (rw_cells_recast asegs m 857336 [CB 8%nat [Z_to_bv 8 96; Z_to_bv 8 149; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857336 [Z_to_bv 8 96; Z_to_bv 8 149; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 857344 [C8 (Z_to_bv 64 865376)]).
  { apply (rw_cells_recast asegs m 857344 [CB 8%nat [Z_to_bv 8 96; Z_to_bv 8 52; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 857344 [Z_to_bv 8 96; Z_to_bv 8 52; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rtc12 : rw_cells asegs m 865376 [C8 (Z_to_bv 64 107652)].
Proof.
  assert (K0 : rw_cells asegs m 865376 [C8 (Z_to_bv 64 107652)]).
  { apply (rw_cells_recast asegs m 865376 [CB 8%nat [Z_to_bv 8 132; Z_to_bv 8 164; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865376 [Z_to_bv 8 132; Z_to_bv 8 164; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc13 : rw_cells asegs m 1480032 [C8 (Z_to_bv 64 4096)].
Proof.
  hcell 1480032 8%nat 4096. rename HC into K0.
  exact K0.
Qed.

Lemma rtc14 : rw_cells asegs m 1488576 [C8 (Z_to_bv 64 1103823372544)].
Proof.
  hcell 1488576 8%nat 1103823372544. rename HC into K0.
  exact K0.
Qed.

Lemma rtc15 : rw_cells asegs m 1488600 [C8 (Z_to_bv 64 72339073309605888)].
Proof.
  hcell 1488600 8%nat 72339073309605888. rename HC into K0.
  exact K0.
Qed.

Lemma rtc17 : rw_cells asegs m 6475584 [C8 (Z_to_bv 64 4096)].
Proof.
  hcell 6475584 8%nat 4096. rename HC into K0.
  exact K0.
Qed.

Tactic Notation "hfact" constr(F) ident(H) := pose proof (hf F ltac:(vm_compute; reflexivity)) as H; cbn [ME.mfact_ok ME.zv ME.cellw] in H.

Tactic Notation "hpf" constr(k) ident(H) := pose proof (hp k _ eq_refl) as H; cbn [ME.pfact_ok ME.zv] in H.

Fixpoint seg_wr_b (A : Z) (n : nat) : bool :=
  match n with O => true | S n' => match wview asegs (fun _ => None) (wa A) with Some _ => seg_wr_b (A + 1) n' | None => false end end.
Lemma seg_wr_b_sound : forall n A (mm : amem), seg_wr_b A n = true -> forall i, 0 <= i < Z.of_nat n -> wview asegs mm (wa (A + i)) <> None.
Proof.
  induction n as [|n IH]; intros A mm H i Hi; [lia|]. cbn [seg_wr_b] in H.
  destruct (wview asegs (fun _ => None) (wa A)) as [b|] eqn:W; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.add_0_r. unfold wview in *. destruct (mm (wa A)); [discriminate|]. exact (fun E => ltac:(rewrite E in W; discriminate W)).
  - replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) mm H). lia.
Qed.
Lemma wr_at_seg : forall A n, 0 <= A -> A + n <= 2 ^ 64 -> 0 <= n -> seg_wr_b A (Z.to_nat n) = true -> wr_at asegs m A n.
Proof.
  intros A n HA HB Hn H. split; [exact HA|]. split; [exact HB|]. intros i Hi. apply (seg_wr_b_sound (Z.to_nat n) A m H). lia.
Qed.

Lemma arelro_main : arelro m.
Proof. intros i Hi. apply (himg 65536 865384); [vm_compute; reflexivity| unfold ARELRO_LO, ARELRO_HI in Hi; lia]. Qed.

Lemma oom_main : exists oomb : byte, rw_cells asegs m 0x15bd20 [C1 oomb; C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells asegs m 1424672 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 1424672 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1424672 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1424672 1424673); [vm_compute; reflexivity| lia]. }
  hcell 1424673 1%nat 1. rename HC into K1.
  assert (K2 : rw_cells asegs m 1424674 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 1424674 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1424674 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1424674 1480016); [vm_compute; reflexivity| lia]. }
  exists (Z_to_bv 8 0).
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma canary_main : exists cb : list byte, rw_cells asegs m 0x62ccc0 [CB 8 cb].
Proof.
  hfact (ME.MRo (ME.ZLit 6474944) 8%nat (ME.ZV 45)) HB.
  exists (word_to_le_bytes 8 (Z_to_bv 64 (V 45%nat))). split.
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. apply wr_at_seg; [lia| lia| lia| vm_compute; reflexivity].
Qed.

Theorem arep_rt_main : arep_rt L m.
Proof.
  unfold arep_rt.
  hfact (ME.MCell (ME.ZLit 6479912) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 228))) HTSD.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 228)) (ME.ZLit 8)) 4%nat (ME.ZLit 0)) HTID.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 228)) (ME.ZLit 152)) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 227))) HCT.
  split; [exact rt1|]. split; [exact rt2|]. split; [exact rt3|]. split; [exact rt4|]. split; [exact rt5|]. split; [exact rt6|].
  split; [exact rt7|]. split; [exact rt8|]. split; [exact rt9|]. split; [exact rt10|]. split; [exact rt11|]. split; [exact rt12|].
  split; [exact rt13|]. split; [exact rt14|]. split; [exact rt15|]. split; [exact rt16|]. split; [exact rt17|]. split; [exact oom_main|].
  split; [exact rt19|]. split; [exact rt20|]. split; [exact rt21|]. split; [exact rt22|]. split; [exact rt23|].
  split; [exact rt24|]. split; [exact HTSD|]. split; [exact rt26|]. split; [exact HTID| exact HCT].
Qed.

Theorem arep_rt2_main : arep_rt2 m.
Proof. split; [exact rtb1|]. split; [exact rtb2| exact rtb3]. Qed.

Theorem arep_rt3_main : arep_rt3 m.
Proof.
  split; [exact rtc1|]. split; [exact rtc2|]. split; [exact rtc3|]. split; [exact rtc4|]. split; [exact rtc5|]. split; [exact rtc6|].
  split; [exact rtc7|]. split; [exact rtc8|]. split; [exact rtc9|]. split; [exact rtc10|]. split; [exact rtc11|]. split; [exact rtc12|].
  split; [exact rtc13|]. split; [exact rtc14|]. split; [exact rtc15|]. split; [exact canary_main| exact rtc17].
Qed.

Definition st0 : astate := ainit (al_space_beg L) (al_ptr_array L).
Definition xc0 : xclass := mkXClass [] [].
Definition X0 : aconc := mkAConc (fun _ => xc0) [].

Lemma get_cls_st0 : forall c, get_cls st0 c = aclass0.
Proof. intros c. unfold get_cls, st0, ainit. cbn [a_cls]. rewrite lookup_empty. reflexivity. Qed.
Lemma max_count_st0 : forall c, max_count st0 c = 0.
Proof. intros c. reflexivity. Qed.
Lemma ndist_st0 : forall c, ndist st0 c = 0.
Proof. intros c. unfold ndist. rewrite get_cls_st0. cbn [c_allocated_user aclass0]. destruct (size_of_class c); reflexivity. Qed.
Lemma busy_of_X0 : forall c k, busy_of X0 c k = None.
Proof. intros. reflexivity. Qed.

Lemma al_t_eq : al_t L = 4096 * V 227%nat. Proof. reflexivity. Qed.
Lemma al_ctx_eq : al_ctx L = 4096 * V 228%nat. Proof. reflexivity. Qed.
Lemma al_ptr_eq : al_ptr_array L = 4096 * V 226%nat. Proof. reflexivity. Qed.
Lemma al_nodes_eq : al_nodes L = 4096 * V 453%nat. Proof. reflexivity. Qed.
Lemma al_store_eq : al_store L = 4096 * V 454%nat. Proof. reflexivity. Qed.
Lemma al_fake_eq : al_fake L = 4096 * V 377%nat. Proof. reflexivity. Qed.
Lemma al_dtls_eq : al_dtls L = 4096 * V 310%nat. Proof. reflexivity. Qed.
Lemma al_res_eq : al_res L = 4096 * V 208%nat. Proof. reflexivity. Qed.
Lemma al_space_beg_eq : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536.
Proof. unfold L, L0, al_space_beg. cbn [al_V VL]. lia. Qed.
Lemma al_sp0_eq : al_sp0 L = 32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat).
Proof. unfold L, L0, al_sp0. cbn [al_V VL]. lia. Qed.

Definition zrun (A n : Z) : Prop := (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at asegs m A n.
Lemma zrun_sub : forall A n A' n', zrun A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> zrun A' n'.
Proof.
  intros A n A' n' [Z1 (W1 & W2 & W3)] H1 H2 H3. split.
  - intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply Z1. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply W3. lia.
Qed.
Lemma zrun_CB : forall A n, zrun A n -> 0 <= n -> rw_cells asegs m A [CB (Z.to_nat n) (ME.zeros n)].
Proof. intros A n [Z1 W1] Hn. exact (ME.mzero_rw_cells asegs m A n Z1 W1 Hn). Qed.
Lemma zrun_junk : forall A n, zrun A n -> 0 <= n -> junk_at m A n.
Proof. intros A n H Hn. exists (ME.zeros n). exact (zrun_CB A n H Hn). Qed.

Lemma zrun_cells : forall A cs, cells_wf cs -> cells_bytes cs = ME.zeros (Z.of_nat (cells_size cs)) -> zrun A (Z.of_nat (cells_size cs)) -> rw_cells asegs m A cs.
Proof.
  intros A cs WF EB ZR. apply (rw_cells_recast asegs m A [CB (cells_size cs) (ME.zeros (Z.of_nat (cells_size cs)))]); [| exact WF| rewrite EB; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; lia].
  rewrite <- (Nat2Z.id (cells_size cs)) at 1. apply zrun_CB; [exact ZR| lia].
Qed.
Lemma u32s_zeros : forall k, u32s (repeat (Z_to_bv 64 0) k) = ME.zeros (4 * Z.of_nat k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u32s]. rewrite IH. unfold ME.zeros.
  replace (Z.to_nat (4 * Z.of_nat (S k))) with (4 + Z.to_nat (4 * Z.of_nat k))%nat by lia. rewrite repeat_app.
  f_equal; try (apply bytes_eq_unsigned; vm_compute; reflexivity).
Qed.
Lemma u64s_zeros : forall k, u64s (repeat (Z_to_bv 64 0) k) = ME.zeros (8 * Z.of_nat k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH. unfold ME.zeros.
  replace (Z.to_nat (8 * Z.of_nat (S k))) with (8 + Z.to_nat (8 * Z.of_nat k))%nat by lia. rewrite repeat_app.
  f_equal; try (apply bytes_eq_unsigned; vm_compute; reflexivity).
Qed.
Lemma zrun_u32arr : forall A k, zrun A (4 * Z.of_nat k) -> u32arr asegs m A (repeat (Z_to_bv 64 0) k).
Proof.
  intros A k ZR. destruct (zrun_CB A _ ZR ltac:(lia)) as [[_ BA] WA]. split.
  - cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. rewrite u32s_zeros. exact BA.
  - rewrite repeat_length. cbn [cells_size csize] in WA. rewrite Nat.add_0_r, Z2Nat.id in WA by lia. exact WA.
Qed.
Lemma zrun_u64arr : forall A k, zrun A (8 * Z.of_nat k) -> u64arr asegs m A (repeat (Z_to_bv 64 0) k).
Proof.
  intros A k ZR. destruct (zrun_CB A _ ZR ltac:(lia)) as [[_ BA] WA]. split.
  - cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. rewrite u64s_zeros. exact BA.
  - rewrite repeat_length. cbn [cells_size csize] in WA. rewrite Nat.add_0_r, Z2Nat.id in WA by lia. exact WA.
Qed.

Lemma rw_cells_nil0 : forall A, 0 <= A <= 2 ^ 64 -> rw_cells asegs m A [CB 0 []].
Proof.
  intros A HA. split; [split; [cbn; auto|]|]; unfold bytes_at, wr_at; cbn [cells_bytes cbytes cells_size csize length app Z.of_nat]; (split; [lia|]); (split; [lia|]); intros i Hi; [cbn in Hi; lia| lia].
Qed.

Lemma rw_cells_glue : forall A n cs1 cs2, rw_cells asegs m A cs1 -> rw_cells asegs m (A + n) cs2 -> n = Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
Proof. intros A n cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app asegs m A cs1 cs2)). exact (conj H1 H2). Qed.

Lemma thr_zrun : zrun (al_t L + 80) 3088.
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 80)) 3088) HZ.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) 4096) HW.
  rewrite al_t_eq. split; [exact HZ|]. destruct HW as (W1 & W2 & W3). split; [lia|]. split; [lia|].
  intros i Hi. replace (4096 * V 227%nat + 80 + i) with (4096 * V 227%nat + (80 + i)) by lia. apply W3. lia.
Qed.
Lemma ri_zrun : zrun (al_space_beg L + K_SPACE_SIZE) 4096.
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 137439019008)) 4096) HZ.
  hfact (ME.MWr (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 137439019008)) 4096) HW.
  rewrite al_space_beg_eq. unfold K_SPACE_SIZE.
  replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37) with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia.
  split; [exact HZ| exact HW].
Qed.

Lemma inst112 : rw_cells asegs m 877768 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells asegs m 877768 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 877768 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 877768 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 877760 878336); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 877776 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 877776 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 877776 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 877760 878336); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma inst984 : rw_cells asegs m 878640 [C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells asegs m 878640 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 878640 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 878640 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 878538 881272); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma ainstance_main : ainstance L st0 m.
Proof.
  unfold ainstance, AINSTANCE. unfold st0, ainit. cbn [a_nres a_nsec].
  hfact (ME.MCell (ME.ZLit 877688) 8%nat (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 65536))) H32.
  hfact (ME.MCell (ME.ZLit 877704) 8%nat (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 137439019008))) H48.
  hcell 877720 8%nat 4096. rename HC into H64.
  hfact (ME.MCell (ME.ZLit 877728) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 226))) H72.
  hcell 878336 1%nat 0. rename HC into H680.
  hcell 877696 4%nat 18446744073709551615. rename HC into H40.
  hcell 877712 1%nat 0. rename HC into H56.
  pose proof inst112 as H112. pose proof inst984 as H984.
  split. { rewrite al_space_beg_eq. exact H32. }
  split. { rewrite al_space_beg_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37) with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia. exact H48. }
  split; [exact H64|]. split; [rewrite al_ptr_eq; exact H72|]. split; [exact H112|]. split; [exact H680|]. split; [exact H984|].
  split; [| exact H56].
  apply (rw_cells_recast asegs m 877696 [C4 (Z_to_bv 64 18446744073709551615)]); [exact H40| cbn; auto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
Qed.

Lemma acache_main : forall c, 1 <= c < K_NUM_CLASSES -> acache_cells L st0 X0 m c.
Proof.
  intros c Hc. unfold acache_cells, acache_addr. rewrite get_cls_st0, max_count_st0. cbn [x_cls X0 xc_cache xc0 c_count aclass0 map app].
  unfold st0, ainit. cbn [a_cinit]. unfold K_NUM_CLASSES in Hc.
  exists (repeat (Z_to_bv 64 0) 16). split; [| split; [| rewrite repeat_length; reflexivity]].
  - apply zrun_cells; [cbn; auto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add].
    apply (zrun_sub _ _ _ _ thr_zrun); lia.
  - apply zrun_u32arr. apply (zrun_sub _ _ _ _ thr_zrun); cbn; lia.
Qed.

Lemma al_top_eq : al_top L = 32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat).
Proof.
  pose proof (hp 35 _ eq_refl) as P. cbn [ME.pfact_ok ME.zv] in P. unfold ME.two64 in P.
  pose proof (hp 22 _ eq_refl) as P344. cbn [ME.pfact_ok] in P344.
  pose proof (hp 6 _ eq_refl) as P6. cbn [ME.pfact_ok] in P6.
  unfold al_top. rewrite al_sp0_eq. unfold page_round_up_Z, page_size.
  assert (C : V 344%nat = 0 /\ 16 * V 6%nat <= 160 \/ V 344%nat = 1 /\ 161 <= 16 * V 6%nat).
  { destruct (Z.eq_dec (V 344%nat) 0) as [E|E]; [left| right]; (split; [lia|]).
    - rewrite E in P. rewrite Z.mod_small in P by lia. lia.
    - assert (E1 : V 344%nat = 1) by lia. rewrite E1 in P.
      destruct (Z_lt_ge_dec (16 * V 6%nat + -4096 * 1 + 3935) 0) as [NEG|POS]; [| rewrite Z.mod_small in P by lia; lia].
      exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in P by lia. rewrite Z.mod_small in P by lia. lia. }
  destruct C as [[E B]|[E B]]; rewrite E; Z.div_mod_to_equations; lia.
Qed.

Lemma athread_main : athread L st0 X0 m.
Proof.
  unfold athread.
  hfact (ME.MCell (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 228))) T0.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 8)) 8%nat (ME.ZAdd (ME.ZMul (ME.ZLit 32768) (ME.ZV 0)) (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 10)) (ME.ZMul (ME.ZLit 4096) (ME.ZV 344))))) T8.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 16)) 8%nat (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 32768) (ME.ZV 0)) (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 10)) (ME.ZMul (ME.ZLit 4096) (ME.ZV 344)))) (ME.ZLit (-8388608)))) T16.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 40)) 1%nat (ME.ZLit 0)) T40.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 3168)) 1%nat (ME.ZLit 0)) T3168.
  rewrite al_t_eq, al_ctx_eq. unfold al_bot. rewrite al_top_eq.
  split.
  { apply (rw_cells_glue _ 8 [_]); [exact T0| | reflexivity].
    apply (rw_cells_glue _ 8 [_]); [exact T8| | reflexivity].
    replace (4096 * V 227%nat + 8 + 8) with (4096 * V 227%nat + 16) by lia.
    replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) - 8388608) with (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) + -8388608) by lia.
    exact T16. }
  split; [exact T40|]. split; [exact acache_main|].
  split. { rewrite <- al_t_eq. apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ thr_zrun); lia. }
  split. { exists (repeat (Z_to_bv 64 0) ASTATS_WORDS). split; [| apply repeat_length]. rewrite <- al_t_eq. apply zrun_u64arr. apply (zrun_sub _ _ _ _ thr_zrun); unfold ASTATS_WORDS; cbn; lia. }
  exact T3168.
Qed.

Lemma ao_t_main : aobj (al_t L) 4096.
Proof.
  rewrite al_t_eq. hpf 17%nat P1. hpf 104%nat D1. hpf 106%nat D2.
  hpf 105%nat D3.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_ctx_main : aobj (al_ctx L) 65536.
Proof.
  rewrite al_ctx_eq. hpf 18%nat P1. hpf 116%nat D1. hpf 117%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_nodes_main : aobj (al_nodes L) 1048576.
Proof.
  rewrite al_nodes_eq. hpf 32%nat P1. hpf 161%nat D1. hpf 162%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_store_main : aobj (al_store L) 8388608.
Proof.
  rewrite al_store_eq. hpf 33%nat P1. hpf 166%nat D1. hpf 167%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_fake_main : aobj (al_fake L) 11571200.
Proof.
  rewrite al_fake_eq. hpf 24%nat P1. hpf 149%nat D1. hpf 150%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_res_main : aobj (al_res L) 137439023104.
Proof.
  rewrite al_res_eq. hpf 14%nat P1. hpf 79%nat D1. hpf 80%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_ptr_main : aobj (al_ptr_array L) 8388608.
Proof.
  rewrite al_ptr_eq. hpf 16%nat P1. hpf 92%nat D1. hpf 93%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_dtls_main : aobj (al_dtls L) 4096.
Proof.
  rewrite al_dtls_eq. hpf 20%nat P1. hpf 136%nat D1. hpf 138%nat D2.
  hpf 137%nat D3.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ad_t_res_main : adisj (al_t L) 4096 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_t_eq, al_res_eq. hpf 82%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_ctx_res_main : adisj (al_ctx L) 65536 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_ctx_eq, al_res_eq. hpf 83%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_nodes_res_main : adisj (al_nodes L) 1048576 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_nodes_eq, al_res_eq. hpf 88%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_res_main : adisj (al_store L) 8388608 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_store_eq, al_res_eq. hpf 89%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_fake_res_main : adisj (al_fake L) 11571200 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_fake_eq, al_res_eq. hpf 87%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_ptr_res_main : adisj (al_ptr_array L) 8388608 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_ptr_eq, al_res_eq. hpf 81%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_t_ctx_main : adisj (al_t L) 4096 (al_ctx L) 65536.
Proof. unfold adisj. rewrite al_t_eq, al_ctx_eq. hpf 107%nat D. exact D. Qed.

Lemma ad_t_nodes_main : adisj (al_t L) 4096 (al_nodes L) 1048576.
Proof. unfold adisj. rewrite al_t_eq, al_nodes_eq. hpf 112%nat D. exact D. Qed.

Lemma ad_t_store_main : adisj (al_t L) 4096 (al_store L) 8388608.
Proof. unfold adisj. rewrite al_t_eq, al_store_eq. hpf 113%nat D. exact D. Qed.

Lemma ad_t_fake_main : adisj (al_t L) 4096 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_t_eq, al_fake_eq. hpf 111%nat D. exact D. Qed.

Lemma ad_t_ptr_main : adisj (al_t L) 4096 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_t_eq, al_ptr_eq. hpf 94%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_ctx_nodes_main : adisj (al_ctx L) 65536 (al_nodes L) 1048576.
Proof. unfold adisj. rewrite al_ctx_eq, al_nodes_eq. hpf 122%nat D. exact D. Qed.

Lemma ad_ctx_store_main : adisj (al_ctx L) 65536 (al_store L) 8388608.
Proof. unfold adisj. rewrite al_ctx_eq, al_store_eq. hpf 123%nat D. exact D. Qed.

Lemma ad_ctx_fake_main : adisj (al_ctx L) 65536 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_ctx_eq, al_fake_eq. hpf 121%nat D. exact D. Qed.

Lemma ad_ctx_ptr_main : adisj (al_ctx L) 65536 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_ctx_eq, al_ptr_eq. hpf 95%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_nodes_store_main : adisj (al_nodes L) 1048576 (al_store L) 8388608.
Proof. unfold adisj. rewrite al_nodes_eq, al_store_eq. hpf 163%nat D. exact D. Qed.

Lemma ad_nodes_fake_main : adisj (al_nodes L) 1048576 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_nodes_eq, al_fake_eq. hpf 151%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_nodes_ptr_main : adisj (al_nodes L) 1048576 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_nodes_eq, al_ptr_eq. hpf 100%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_fake_main : adisj (al_store L) 8388608 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_store_eq, al_fake_eq. hpf 152%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_ptr_main : adisj (al_store L) 8388608 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_store_eq, al_ptr_eq. hpf 101%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_fake_ptr_main : adisj (al_fake L) 11571200 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_fake_eq, al_ptr_eq. hpf 99%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_dtls_res_main : adisj (al_dtls L) 4096 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_dtls_eq, al_res_eq. hpf 85%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_t_dtls_main : adisj (al_t L) 4096 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_t_eq, al_dtls_eq. hpf 109%nat D. exact D. Qed.

Lemma ad_ctx_dtls_main : adisj (al_ctx L) 65536 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_ctx_eq, al_dtls_eq. hpf 119%nat D. exact D. Qed.

Lemma ad_nodes_dtls_main : adisj (al_nodes L) 1048576 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_nodes_eq, al_dtls_eq. hpf 141%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_dtls_main : adisj (al_store L) 8388608 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_store_eq, al_dtls_eq. hpf 142%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_fake_dtls_main : adisj (al_fake L) 11571200 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_fake_eq, al_dtls_eq. hpf 140%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_dtls_ptr_main : adisj (al_dtls L) 4096 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_dtls_eq, al_ptr_eq. hpf 97%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma space_mod_main : (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat.
Proof.
  hpf 37%nat P. hpf 15%nat R9. pose proof (HV 208%nat) as B8. unfold ME.two64 in P.
  change 65535 with (Z.ones 16) in P. rewrite Z.land_ones in P by lia. change (2 ^ 16) with 65536 in P.
  assert (M : 0 <= (4096 * V 208%nat) mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_ge_dec (-4096 * V 209%nat + (4096 * V 208%nat) mod 65536) 0) as [NEG|POS].
  - exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in P by lia. rewrite Z.mod_small in P by lia. lia.
  - rewrite Z.mod_small in P by lia. lia.
Qed.
Lemma ao_space_main : al_res L + 4096 <= al_space_beg L <= al_res L + 65536.
Proof.
  rewrite al_res_eq, al_space_beg_eq. hpf 15%nat R9. lia.
Qed.
Lemma ao_space_al_main : al_space_beg L mod 65536 = 0.
Proof.
  rewrite al_space_beg_eq. pose proof space_mod_main as SM. pose proof (HV 208%nat) as B8.
  replace (4096 * V 208%nat + -4096 * V 209%nat + 65536) with ((4096 * V 208%nat - (4096 * V 208%nat) mod 65536) + 1 * 65536) by lia.
  rewrite Z.mod_add by lia. rewrite <- Zminus_mod_idemp_l. rewrite Z.sub_diag. reflexivity.
Qed.
Lemma ao_res_hi_main : 0x10007fff8000 <= al_res L.
Proof. rewrite al_res_eq. hpf 14%nat P. lia. Qed.

Lemma v344_cases : (V 344%nat = 0 /\ 16 * V 6%nat <= 160) \/ (V 344%nat = 1 /\ 161 <= 16 * V 6%nat).
Proof.
  hpf 35%nat P. unfold ME.two64 in P. hpf 22%nat P344. hpf 6%nat P6.
  destruct (Z.eq_dec (V 344%nat) 0) as [E|E]; [left| right]; (split; [lia|]).
  - rewrite E in P. rewrite Z.mod_small in P by lia. lia.
  - assert (E1 : V 344%nat = 1) by lia. rewrite E1 in P.
    destruct (Z_lt_ge_dec (16 * V 6%nat + -4096 * 1 + 3935) 0) as [NEG|POS]; [| rewrite Z.mod_small in P by lia; lia].
    exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in P by lia. rewrite Z.mod_small in P by lia. lia.
Qed.
Lemma ao_stack_main : al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936).
Proof.
  unfold al_bot. rewrite al_top_eq. pose proof v344_cases as C. pose proof HUSP as HU0. unfold usp_pin in HU0. hpf 41%nat P. unfold ME.two64 in P.
  pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. hpf 6%nat P6. rewrite Z.mod_small in P by lia.
  split; [lia|]. split; [| lia].
  replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat)) with ((8 * V 0%nat + V 10%nat + V 344%nat) * 4096) by lia. apply Z_mod_mult.
Qed.

Theorem alayout_ok_main : alayout_ok L.
Proof.
  constructor.
  - exact ao_t_main. - exact ao_ctx_main. - exact ao_nodes_main. - exact ao_store_main. - exact ao_fake_main. - exact ao_res_main.
  - exact ao_ptr_main. - exact ao_dtls_main. - exact ao_res_hi_main. - exact ao_space_main. - exact ao_space_al_main.
  - exact ad_t_res_main. - exact ad_ctx_res_main. - exact ad_nodes_res_main. - exact ad_store_res_main. - exact ad_fake_res_main. - exact ad_ptr_res_main.
  - exact ad_t_ctx_main. - exact ad_t_nodes_main. - exact ad_t_store_main. - exact ad_t_fake_main. - exact ad_t_ptr_main.
  - exact ad_ctx_nodes_main. - exact ad_ctx_store_main. - exact ad_ctx_fake_main. - exact ad_ctx_ptr_main.
  - exact ad_nodes_store_main. - exact ad_nodes_fake_main. - exact ad_nodes_ptr_main.
  - exact ad_store_fake_main. - exact ad_store_ptr_main. - exact ad_fake_ptr_main.
  - exact ad_dtls_res_main. - exact ad_t_dtls_main. - exact ad_ctx_dtls_main. - exact ad_nodes_dtls_main. - exact ad_store_dtls_main. - exact ad_fake_dtls_main.
  - exact ad_dtls_ptr_main.
  - exact ao_stack_main.
  - cbn [al_U L L0]. unfold AUMAX. pose proof HU as HU1. unfold univ_ok in HU1. exact (proj1 HU1).
Qed.

End AtMain.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainFactsBoth MainEntryBoth.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB AProto.TwinB ALayout.TwinB ARep.TwinB ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module MF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainFactsBoth.
Module MA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.

Definition VL (V : nat -> Z) (n : nat) : Z :=
  match n with
  | 240%nat => V 227%nat | 241%nat => V 228%nat | 221%nat => V 208%nat | 222%nat => V 209%nat | 239%nat => V 226%nat
  | 485%nat => V 453%nat | 486%nat => V 454%nat | 406%nat => V 377%nat | 323%nat => V 310%nat | 91%nat => V 78%nat | 220%nat => V 207%nat

  | 584%nat => V 471%nat | 503%nat => V 245%nat | 258%nat => V 245%nat
  | 6%nat => 256 * V 10%nat + V 6%nat
  | _ => V n
  end.
Definition L0 (V : nat -> Z) (w : bool) (U : list (list Z)) : alayout := mkALayout (VL V) w U.

Definition usum (U : list (list Z)) : Z := fold_right (fun u s => Z.of_nat (length u) + 1 + s) 0 U.
Definition univ_ok (U : list (list Z)) : Prop := (length U <= 4096)%nat /\ usum U + 8 <= 2 ^ 20.

Definition usp_pin {rc : runConstT} (V : nat -> Z) : Prop := 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = ATOP + 8388608.

Section AtMain.
Context {rc : runConstT}.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis HMF : Forall (ME.mfact_ok bsegs V m) MF.both_mem_facts.
Hypothesis HMFw : Forall (ME.mfact_ok bsegs V m) (MA.both_mem_facts_w w).
Hypothesis HPF : Forall (ME.pfact_ok V) MF.both_pure_facts.
Hypothesis MINV : mem_inv bsegs m.

Hypothesis HUSP : usp_pin V.
Hypothesis HSH0 : MA.bshadow0 V m.
Hypothesis HU : univ_ok U.

Let L := L0 V w U.

Lemma hf : forall f, existsb (ME.mfact_eqb f) MF.both_mem_facts = true -> ME.mfact_ok bsegs V m f.
Proof. intros f H. exact (ME.mfact_find bsegs V m _ f HMF H). Qed.
Lemma hp : forall k f, nth_error MF.both_pure_facts k = Some f -> ME.pfact_ok V f.
Proof. intros k f H. exact (proj1 (Forall_forall _ _) HPF f (nth_error_In _ _ H)). Qed.

Ltac hcell A W X :=
  let H := fresh "HC" in
  pose proof (hf (ME.MCell (ME.ZLit A) W (ME.ZLit X)) ltac:(vm_compute; reflexivity)) as H;
  cbn [ME.mfact_ok ME.zv ME.cellw] in H.

Lemma himg : forall lo hi, existsb (fun f => match f with ME.MImg lo' hi' => (lo' <=? lo) && (hi <=? hi') | _ => false end) MF.both_mem_facts = true ->
  forall i, lo <= i < hi -> m (wa i) = None.
Proof. intros lo hi H. exact (ME.mimg_cover bsegs V m _ lo hi HMF H). Qed.

Lemma bytes_eq_unsigned : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma rt1 : rw_cells bsegs m 865808 [C8 (Z_to_bv 64 1488672)].
Proof.
  assert (K0 : rw_cells bsegs m 865808 [C8 (Z_to_bv 64 1488672)]).
  { apply (rw_cells_recast bsegs m 865808 [CB 8%nat [Z_to_bv 8 32; Z_to_bv 8 183; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865808 [Z_to_bv 8 32; Z_to_bv 8 183; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt2 : rw_cells bsegs m 865824 [C8 (Z_to_bv 64 1497000); C8 (Z_to_bv 64 889976); C8 (Z_to_bv 64 900216); C8 (Z_to_bv 64 903528); C8 (Z_to_bv 64 903536); C8 (Z_to_bv 64 903520)].
Proof.
  assert (K0 : rw_cells bsegs m 865824 [C8 (Z_to_bv 64 1497000)]).
  { apply (rw_cells_recast bsegs m 865824 [CB 8%nat [Z_to_bv 8 168; Z_to_bv 8 215; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865824 [Z_to_bv 8 168; Z_to_bv 8 215; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 865832 [C8 (Z_to_bv 64 889976)]).
  { apply (rw_cells_recast bsegs m 865832 [CB 8%nat [Z_to_bv 8 120; Z_to_bv 8 148; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865832 [Z_to_bv 8 120; Z_to_bv 8 148; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells bsegs m 865840 [C8 (Z_to_bv 64 900216)]).
  { apply (rw_cells_recast bsegs m 865840 [CB 8%nat [Z_to_bv 8 120; Z_to_bv 8 188; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865840 [Z_to_bv 8 120; Z_to_bv 8 188; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells bsegs m 865848 [C8 (Z_to_bv 64 903528)]).
  { apply (rw_cells_recast bsegs m 865848 [CB 8%nat [Z_to_bv 8 104; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865848 [Z_to_bv 8 104; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K4 : rw_cells bsegs m 865856 [C8 (Z_to_bv 64 903536)]).
  { apply (rw_cells_recast bsegs m 865856 [CB 8%nat [Z_to_bv 8 112; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865856 [Z_to_bv 8 112; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K5 : rw_cells bsegs m 865864 [C8 (Z_to_bv 64 903520)]).
  { apply (rw_cells_recast bsegs m 865864 [CB 8%nat [Z_to_bv 8 96; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865864 [Z_to_bv 8 96; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K3|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K4|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K5.
Qed.

Lemma rt3 : rw_cells bsegs m 865872 [C8 (Z_to_bv 64 873792)].
Proof.
  assert (K0 : rw_cells bsegs m 865872 [C8 (Z_to_bv 64 873792)]).
  { apply (rw_cells_recast bsegs m 865872 [CB 8%nat [Z_to_bv 8 64; Z_to_bv 8 85; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865872 [Z_to_bv 8 64; Z_to_bv 8 85; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt4 : rw_cells bsegs m 868760 [C8 (Z_to_bv 64 903513)].
Proof.
  assert (K0 : rw_cells bsegs m 868760 [C8 (Z_to_bv 64 903513)]).
  { apply (rw_cells_recast bsegs m 868760 [CB 8%nat [Z_to_bv 8 89; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 868760 [Z_to_bv 8 89; Z_to_bv 8 201; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt5 : rw_cells bsegs m 869000 [C8 (Z_to_bv 64 16)].
Proof.
  assert (K0 : rw_cells bsegs m 869000 [C8 (Z_to_bv 64 16)]).
  { apply (rw_cells_recast bsegs m 869000 [CB 8%nat [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 869000 [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rt6 : rw_cells bsegs m 873784 [C8 (Z_to_bv 64 824764); C8 (Z_to_bv 64 825792)].
Proof.
  assert (K0 : rw_cells bsegs m 873784 [C8 (Z_to_bv 64 824764)]).
  { apply (rw_cells_recast bsegs m 873784 [CB 8%nat [Z_to_bv 8 188; Z_to_bv 8 149; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873784 [Z_to_bv 8 188; Z_to_bv 8 149; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 873792 [C8 (Z_to_bv 64 825792)]).
  { apply (rw_cells_recast bsegs m 873792 [CB 8%nat [Z_to_bv 8 192; Z_to_bv 8 153; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873792 [Z_to_bv 8 192; Z_to_bv 8 153; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rt7 : rw_cells bsegs m 889912 [C8 (Z_to_bv 64 1099511627776); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048); C1 (Z_to_bv 8 1)].
Proof.
  hcell 889912 8%nat 1099511627776. rename HC into K0.
  hcell 889920 2%nat 16. rename HC into K1.
  hcell 889922 2%nat 2048. rename HC into K2.
  hcell 889924 1%nat 1. rename HC into K3.
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma rt8 : rw_cells bsegs m 889976 [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 1024); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 2048)].
Proof.
  hcell 889976 4%nat 4294967295. rename HC into K0.
  hcell 889980 4%nat 256. rename HC into K1.
  hcell 889984 4%nat 1024. rename HC into K2.
  hcell 889988 4%nat 16. rename HC into K3.
  hcell 889992 4%nat 2048. rename HC into K4.
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K3|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K4.
Qed.

Lemma rt9 : rw_cells bsegs m 890020 [C4 (Z_to_bv 64 4096); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 190)].
Proof.
  hcell 890020 4%nat 4096. rename HC into K0.
  hcell 890024 8%nat 816043786240. rename HC into HW1.
  apply (rw_cells_recast bsegs m 890024 _ [C4 (Z_to_bv 64 0); CB 4%nat [Z_to_bv 8 190; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW1; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW1 as [HW1 _].
  rename HW1 into K1.
  hcell 890024 8%nat 816043786240. rename HC into HW2.
  apply (rw_cells_recast bsegs m 890024 _ [CB 4%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (Z_to_bv 64 190)]) in HW2; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW2 as [_ HW2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW2.
  rename HW2 into K2.
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma rt10 : rw_cells bsegs m 890061 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 890056 8%nat 72340172838010881. rename HC into HW0.
  apply (rw_cells_recast bsegs m 890056 _ [CB 5%nat [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1]; C1 (Z_to_bv 8 1); CB 2%nat [Z_to_bv 8 1; Z_to_bv 8 1]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma rt11 : rw_cells bsegs m 900216 [C8 (Z_to_bv 64 2147450880)].
Proof.
  hcell 900216 8%nat 2147450880. rename HC into K0.
  exact K0.
Qed.

Lemma rt12 : rw_cells bsegs m 898268 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 898268 1%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rt13 : rw_cells bsegs m 898272 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 898272 1%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rt14 : rw_cells bsegs m 898276 [C4 (Z_to_bv 64 0)].
Proof.
  hcell 898276 4%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma rt15 : rw_cells bsegs m 903512 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof.
  hcell 903512 1%nat 1. rename HC into K0.
  hcell 903513 1%nat 1. rename HC into K1.
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rt16 : rw_cells bsegs m 903520 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  hcell 903520 8%nat 140737488355327. rename HC into K0.
  assert (K1 : rw_cells bsegs m 903528 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 903528 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 903528 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 903528 903544); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells bsegs m 903536 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 903536 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 903536 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 903528 903544); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma rt17 : rw_cells bsegs m 903548 [C4 (Z_to_bv 64 30)].
Proof.
  hcell 903548 4%nat 30. rename HC into K0.
  exact K0.
Qed.

Lemma rt19 : rw_cells bsegs m 1488672 [C8 (Z_to_bv 64 4096)].
Proof.
  hcell 1488672 8%nat 4096. rename HC into K0.
  exact K0.
Qed.

Lemma rt20 : rw_cells bsegs m 1496896 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells bsegs m 1496896 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 1496896 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1496896 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1496895 1496992); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 1496904 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 1496904 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1496904 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1496895 1496992); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rt21 : rw_cells bsegs m 1497032 [C8 (Z_to_bv 64 128849084416)].
Proof.
  hcell 1497032 8%nat 128849084416. rename HC into K0.
  exact K0.
Qed.

Lemma rt22 : rw_cells bsegs m 1497034 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 1497032 8%nat 128849084416. rename HC into HW0.
  apply (rw_cells_recast bsegs m 1497032 _ [CB 2%nat [Z_to_bv 8 0; Z_to_bv 8 0]; C1 (Z_to_bv 8 1); CB 5%nat [Z_to_bv 8 0; Z_to_bv 8 30; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma rt23 : rw_cells bsegs m 1497120 [C8 (Z_to_bv 64 18446744073709551615)].
Proof.
  hcell 1497120 8%nat 18446744073709551615. rename HC into K0.
  exact K0.
Qed.

Lemma rt24 : rw_cells bsegs m 6352360 [C8 (Z_to_bv 64 6488552)].
Proof.
  hcell 6352360 8%nat 6488552. rename HC into K0.
  exact K0.
Qed.

Lemma rt26 : rw_cells bsegs m 6352464 [C4 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells bsegs m 6352464 [C4 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 6352464 [CB 4%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 6352464 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 6352464 6352480); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtb1 : rw_cells bsegs m 1497260 [C1 (Z_to_bv 8 0)].
Proof.
  hcell 1497256 8%nat 16843009. rename HC into HW0.
  apply (rw_cells_recast bsegs m 1497256 _ [CB 4%nat [Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 1]; C1 (Z_to_bv 8 0); CB 3%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma rtb2 : rw_cells bsegs m 1497144 [C8 (Z_to_bv 64 0)].
Proof.
  hcell 1497144 8%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma rtb3 : rw_cells bsegs m 873672 [C8 (Z_to_bv 64 805820)].
Proof.
  assert (K0 : rw_cells bsegs m 873672 [C8 (Z_to_bv 64 805820)]).
  { apply (rw_cells_recast bsegs m 873672 [CB 8%nat [Z_to_bv 8 188; Z_to_bv 8 75; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873672 [Z_to_bv 8 188; Z_to_bv 8 75; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc1 : rw_cells bsegs m 873512 [C8 (Z_to_bv 64 823048); C8 (Z_to_bv 64 810488)].
Proof.
  assert (K0 : rw_cells bsegs m 873512 [C8 (Z_to_bv 64 823048)]).
  { apply (rw_cells_recast bsegs m 873512 [CB 8%nat [Z_to_bv 8 8; Z_to_bv 8 143; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873512 [Z_to_bv 8 8; Z_to_bv 8 143; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 873520 [C8 (Z_to_bv 64 810488)]).
  { apply (rw_cells_recast bsegs m 873520 [CB 8%nat [Z_to_bv 8 248; Z_to_bv 8 93; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873520 [Z_to_bv 8 248; Z_to_bv 8 93; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rtc2 : rw_cells bsegs m 873480 [C8 (Z_to_bv 64 847040)].
Proof.
  assert (K0 : rw_cells bsegs m 873480 [C8 (Z_to_bv 64 847040)]).
  { apply (rw_cells_recast bsegs m 873480 [CB 8%nat [Z_to_bv 8 192; Z_to_bv 8 236; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873480 [Z_to_bv 8 192; Z_to_bv 8 236; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc3 : rw_cells bsegs m 873488 [C8 (Z_to_bv 64 809924)].
Proof.
  assert (K0 : rw_cells bsegs m 873488 [C8 (Z_to_bv 64 809924)]).
  { apply (rw_cells_recast bsegs m 873488 [CB 8%nat [Z_to_bv 8 196; Z_to_bv 8 91; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873488 [Z_to_bv 8 196; Z_to_bv 8 91; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc4 : rw_cells bsegs m 873704 [C8 (Z_to_bv 64 826952)].
Proof.
  assert (K0 : rw_cells bsegs m 873704 [C8 (Z_to_bv 64 826952)]).
  { apply (rw_cells_recast bsegs m 873704 [CB 8%nat [Z_to_bv 8 72; Z_to_bv 8 158; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873704 [Z_to_bv 8 72; Z_to_bv 8 158; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc5 : rw_cells bsegs m 873464 [C8 (Z_to_bv 64 824512)].
Proof.
  assert (K0 : rw_cells bsegs m 873464 [C8 (Z_to_bv 64 824512)]).
  { apply (rw_cells_recast bsegs m 873464 [CB 8%nat [Z_to_bv 8 192; Z_to_bv 8 148; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873464 [Z_to_bv 8 192; Z_to_bv 8 148; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc6 : rw_cells bsegs m 1497080 [C8 (Z_to_bv 64 4294967296)].
Proof.
  hcell 1497080 8%nat 4294967296. rename HC into K0.
  exact K0.
Qed.

Lemma rtc7 : rw_cells bsegs m 1497248 [C8 (Z_to_bv 64 72340172838076673)].
Proof.
  hcell 1497248 8%nat 72340172838076673. rename HC into K0.
  exact K0.
Qed.

Lemma rtc8 : rw_cells bsegs m 900224 [C4 (Z_to_bv 64 1)].
Proof.
  hcell 900224 4%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rtc9 : rw_cells bsegs m 890072 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 890072 1%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma rtc10 : rw_cells bsegs m 1488664 [C4 (Z_to_bv 64 0)].
Proof.
  hcell 1488664 4%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma rtc11 : rw_cells bsegs m 865808 [C8 (Z_to_bv 64 1488672); C8 (Z_to_bv 64 873848)].
Proof.
  assert (K0 : rw_cells bsegs m 865808 [C8 (Z_to_bv 64 1488672)]).
  { apply (rw_cells_recast bsegs m 865808 [CB 8%nat [Z_to_bv 8 32; Z_to_bv 8 183; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865808 [Z_to_bv 8 32; Z_to_bv 8 183; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 865816 [C8 (Z_to_bv 64 873848)]).
  { apply (rw_cells_recast bsegs m 865816 [CB 8%nat [Z_to_bv 8 120; Z_to_bv 8 85; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 865816 [Z_to_bv 8 120; Z_to_bv 8 85; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma rtc12 : rw_cells bsegs m 873848 [C8 (Z_to_bv 64 107586)].
Proof.
  assert (K0 : rw_cells bsegs m 873848 [C8 (Z_to_bv 64 107586)]).
  { apply (rw_cells_recast bsegs m 873848 [CB 8%nat [Z_to_bv 8 66; Z_to_bv 8 164; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873848 [Z_to_bv 8 66; Z_to_bv 8 164; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma rtc13 : rw_cells bsegs m 1488672 [C8 (Z_to_bv 64 4096)].
Proof.
  hcell 1488672 8%nat 4096. rename HC into K0.
  exact K0.
Qed.

Lemma rtc14 : rw_cells bsegs m 1497216 [C8 (Z_to_bv 64 1103823372544)].
Proof.
  hcell 1497216 8%nat 1103823372544. rename HC into K0.
  exact K0.
Qed.

Lemma rtc15 : rw_cells bsegs m 1497240 [C8 (Z_to_bv 64 72339073309605888)].
Proof.
  hcell 1497240 8%nat 72339073309605888. rename HC into K0.
  exact K0.
Qed.

Lemma rtc17 : rw_cells bsegs m 6484224 [C8 (Z_to_bv 64 4096)].
Proof.
  hcell 6484224 8%nat 4096. rename HC into K0.
  exact K0.
Qed.

Tactic Notation "hfact" constr(F) ident(H) := pose proof (hf F ltac:(vm_compute; reflexivity)) as H; cbn [ME.mfact_ok ME.zv ME.cellw] in H.

Tactic Notation "hpf" constr(k) ident(H) := pose proof (hp k _ eq_refl) as H; cbn [ME.pfact_ok ME.zv] in H.

Fixpoint seg_wr_b (A : Z) (n : nat) : bool :=
  match n with O => true | S n' => match wview bsegs (fun _ => None) (wa A) with Some _ => seg_wr_b (A + 1) n' | None => false end end.
Lemma seg_wr_b_sound : forall n A (mm : amem), seg_wr_b A n = true -> forall i, 0 <= i < Z.of_nat n -> wview bsegs mm (wa (A + i)) <> None.
Proof.
  induction n as [|n IH]; intros A mm H i Hi; [lia|]. cbn [seg_wr_b] in H.
  destruct (wview bsegs (fun _ => None) (wa A)) as [b|] eqn:W; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.add_0_r. unfold wview in *. destruct (mm (wa A)); [discriminate|]. exact (fun E => ltac:(rewrite E in W; discriminate W)).
  - replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) mm H). lia.
Qed.
Lemma wr_at_seg : forall A n, 0 <= A -> A + n <= 2 ^ 64 -> 0 <= n -> seg_wr_b A (Z.to_nat n) = true -> wr_at bsegs m A n.
Proof.
  intros A n HA HB Hn H. split; [exact HA|]. split; [exact HB|]. intros i Hi. apply (seg_wr_b_sound (Z.to_nat n) A m H). lia.
Qed.

Lemma arelro_main : arelro m.
Proof. intros i Hi. apply (himg 65536 873856); [vm_compute; reflexivity| unfold ARELRO_LO, ARELRO_HI in Hi; lia]. Qed.

Lemma oom_main : exists oomb : byte, rw_cells bsegs m 0x15dee0 [C1 oomb; C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells bsegs m 1433312 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 1433312 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1433312 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1433312 1433313); [vm_compute; reflexivity| lia]. }
  hcell 1433313 1%nat 1. rename HC into K1.
  assert (K2 : rw_cells bsegs m 1433314 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 1433314 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1433314 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 1433314 1488656); [vm_compute; reflexivity| lia]. }
  exists (Z_to_bv 8 0).
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma canary_main : exists cb : list byte, rw_cells bsegs m 0x62ee80 [CB 8 cb].
Proof.
  hfact (ME.MRo (ME.ZLit 6483584) 8%nat (ME.ZV 45)) HB.
  exists (word_to_le_bytes 8 (Z_to_bv 64 (V 45%nat))). split.
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. apply wr_at_seg; [lia| lia| lia| vm_compute; reflexivity].
Qed.

Theorem arep_rt_main : arep_rt L m.
Proof.
  unfold arep_rt.
  hfact (ME.MCell (ME.ZLit 6488552) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 228))) HTSD.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 228)) (ME.ZLit 8)) 4%nat (ME.ZLit 0)) HTID.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 228)) (ME.ZLit 152)) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 227))) HCT.
  split; [exact rt1|]. split; [exact rt2|]. split; [exact rt3|]. split; [exact rt4|]. split; [exact rt5|]. split; [exact rt6|].
  split; [exact rt7|]. split; [exact rt8|]. split; [exact rt9|]. split; [exact rt10|]. split; [exact rt11|]. split; [exact rt12|].
  split; [exact rt13|]. split; [exact rt14|]. split; [exact rt15|]. split; [exact rt16|]. split; [exact rt17|]. split; [exact oom_main|].
  split; [exact rt19|]. split; [exact rt20|]. split; [exact rt21|]. split; [exact rt22|]. split; [exact rt23|].
  split; [exact rt24|]. split; [exact HTSD|]. split; [exact rt26|]. split; [exact HTID| exact HCT].
Qed.

Theorem arep_rt2_main : arep_rt2 m.
Proof. split; [exact rtb1|]. split; [exact rtb2| exact rtb3]. Qed.

Theorem arep_rt3_main : arep_rt3 m.
Proof.
  split; [exact rtc1|]. split; [exact rtc2|]. split; [exact rtc3|]. split; [exact rtc4|]. split; [exact rtc5|]. split; [exact rtc6|].
  split; [exact rtc7|]. split; [exact rtc8|]. split; [exact rtc9|]. split; [exact rtc10|]. split; [exact rtc11|]. split; [exact rtc12|].
  split; [exact rtc13|]. split; [exact rtc14|]. split; [exact rtc15|]. split; [exact canary_main| exact rtc17].
Qed.

Definition st0 : astate := ainit (al_space_beg L) (al_ptr_array L).
Definition xc0 : xclass := mkXClass [] [].
Definition X0 : aconc := mkAConc (fun _ => xc0) [].

Lemma get_cls_st0 : forall c, get_cls st0 c = aclass0.
Proof. intros c. unfold get_cls, st0, ainit. cbn [a_cls]. rewrite lookup_empty. reflexivity. Qed.
Lemma max_count_st0 : forall c, max_count st0 c = 0.
Proof. intros c. reflexivity. Qed.
Lemma ndist_st0 : forall c, ndist st0 c = 0.
Proof. intros c. unfold ndist. rewrite get_cls_st0. cbn [c_allocated_user aclass0]. destruct (size_of_class c); reflexivity. Qed.
Lemma busy_of_X0 : forall c k, busy_of X0 c k = None.
Proof. intros. reflexivity. Qed.

Lemma al_t_eq : al_t L = 4096 * V 227%nat. Proof. reflexivity. Qed.
Lemma al_ctx_eq : al_ctx L = 4096 * V 228%nat. Proof. reflexivity. Qed.
Lemma al_ptr_eq : al_ptr_array L = 4096 * V 226%nat. Proof. reflexivity. Qed.
Lemma al_nodes_eq : al_nodes L = 4096 * V 453%nat. Proof. reflexivity. Qed.
Lemma al_store_eq : al_store L = 4096 * V 454%nat. Proof. reflexivity. Qed.
Lemma al_fake_eq : al_fake L = 4096 * V 377%nat. Proof. reflexivity. Qed.
Lemma al_dtls_eq : al_dtls L = 4096 * V 310%nat. Proof. reflexivity. Qed.
Lemma al_res_eq : al_res L = 4096 * V 208%nat. Proof. reflexivity. Qed.
Lemma al_space_beg_eq : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536.
Proof. unfold L, L0, al_space_beg. cbn [al_V VL]. lia. Qed.
Lemma al_sp0_eq : al_sp0 L = 32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat).
Proof. unfold L, L0, al_sp0. cbn [al_V VL]. lia. Qed.

Definition zrun (A n : Z) : Prop := (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at bsegs m A n.
Lemma zrun_sub : forall A n A' n', zrun A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> zrun A' n'.
Proof.
  intros A n A' n' [Z1 (W1 & W2 & W3)] H1 H2 H3. split.
  - intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply Z1. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply W3. lia.
Qed.
Lemma zrun_CB : forall A n, zrun A n -> 0 <= n -> rw_cells bsegs m A [CB (Z.to_nat n) (ME.zeros n)].
Proof. intros A n [Z1 W1] Hn. exact (ME.mzero_rw_cells bsegs m A n Z1 W1 Hn). Qed.
Lemma zrun_junk : forall A n, zrun A n -> 0 <= n -> junk_at m A n.
Proof. intros A n H Hn. exists (ME.zeros n). exact (zrun_CB A n H Hn). Qed.

Lemma zrun_cells : forall A cs, cells_wf cs -> cells_bytes cs = ME.zeros (Z.of_nat (cells_size cs)) -> zrun A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m A cs.
Proof.
  intros A cs WF EB ZR. apply (rw_cells_recast bsegs m A [CB (cells_size cs) (ME.zeros (Z.of_nat (cells_size cs)))]); [| exact WF| rewrite EB; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; lia].
  rewrite <- (Nat2Z.id (cells_size cs)) at 1. apply zrun_CB; [exact ZR| lia].
Qed.
Lemma u32s_zeros : forall k, u32s (repeat (Z_to_bv 64 0) k) = ME.zeros (4 * Z.of_nat k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u32s]. rewrite IH. unfold ME.zeros.
  replace (Z.to_nat (4 * Z.of_nat (S k))) with (4 + Z.to_nat (4 * Z.of_nat k))%nat by lia. rewrite repeat_app.
  f_equal; try (apply bytes_eq_unsigned; vm_compute; reflexivity).
Qed.
Lemma u64s_zeros : forall k, u64s (repeat (Z_to_bv 64 0) k) = ME.zeros (8 * Z.of_nat k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u64s]. rewrite IH. unfold ME.zeros.
  replace (Z.to_nat (8 * Z.of_nat (S k))) with (8 + Z.to_nat (8 * Z.of_nat k))%nat by lia. rewrite repeat_app.
  f_equal; try (apply bytes_eq_unsigned; vm_compute; reflexivity).
Qed.
Lemma zrun_u32arr : forall A k, zrun A (4 * Z.of_nat k) -> u32arr bsegs m A (repeat (Z_to_bv 64 0) k).
Proof.
  intros A k ZR. destruct (zrun_CB A _ ZR ltac:(lia)) as [[_ BA] WA]. split.
  - cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. rewrite u32s_zeros. exact BA.
  - rewrite repeat_length. cbn [cells_size csize] in WA. rewrite Nat.add_0_r, Z2Nat.id in WA by lia. exact WA.
Qed.
Lemma zrun_u64arr : forall A k, zrun A (8 * Z.of_nat k) -> u64arr bsegs m A (repeat (Z_to_bv 64 0) k).
Proof.
  intros A k ZR. destruct (zrun_CB A _ ZR ltac:(lia)) as [[_ BA] WA]. split.
  - cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. rewrite u64s_zeros. exact BA.
  - rewrite repeat_length. cbn [cells_size csize] in WA. rewrite Nat.add_0_r, Z2Nat.id in WA by lia. exact WA.
Qed.

Lemma rw_cells_nil0 : forall A, 0 <= A <= 2 ^ 64 -> rw_cells bsegs m A [CB 0 []].
Proof.
  intros A HA. split; [split; [cbn; auto|]|]; unfold bytes_at, wr_at; cbn [cells_bytes cbytes cells_size csize length app Z.of_nat]; (split; [lia|]); (split; [lia|]); intros i Hi; [cbn in Hi; lia| lia].
Qed.

Lemma rw_cells_glue : forall A n cs1 cs2, rw_cells bsegs m A cs1 -> rw_cells bsegs m (A + n) cs2 -> n = Z.of_nat (cells_size cs1) -> rw_cells bsegs m A (cs1 ++ cs2).
Proof. intros A n cs1 cs2 H1 H2 ->. apply (proj2 (rw_cells_app bsegs m A cs1 cs2)). exact (conj H1 H2). Qed.

Lemma thr_zrun : zrun (al_t L + 80) 3088.
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 80)) 3088) HZ.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) 4096) HW.
  rewrite al_t_eq. split; [exact HZ|]. destruct HW as (W1 & W2 & W3). split; [lia|]. split; [lia|].
  intros i Hi. replace (4096 * V 227%nat + 80 + i) with (4096 * V 227%nat + (80 + i)) by lia. apply W3. lia.
Qed.
Lemma ri_zrun : zrun (al_space_beg L + K_SPACE_SIZE) 4096.
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 137439019008)) 4096) HZ.
  hfact (ME.MWr (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 137439019008)) 4096) HW.
  rewrite al_space_beg_eq. unfold K_SPACE_SIZE.
  replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37) with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia.
  split; [exact HZ| exact HW].
Qed.

Lemma inst112 : rw_cells bsegs m 886408 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells bsegs m 886408 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 886408 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 886408 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 886400 886976); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 886416 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 886416 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 886416 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 886400 886976); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K1.
Qed.

Lemma inst984 : rw_cells bsegs m 887280 [C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells bsegs m 887280 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 887280 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 887280 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg 887178 889912); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma ainstance_main : ainstance L st0 m.
Proof.
  unfold ainstance, AINSTANCE. unfold st0, ainit. cbn [a_nres a_nsec].
  hfact (ME.MCell (ME.ZLit 886328) 8%nat (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 65536))) H32.
  hfact (ME.MCell (ME.ZLit 886344) 8%nat (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 208)) (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 209))) (ME.ZLit 137439019008))) H48.
  hcell 886360 8%nat 4096. rename HC into H64.
  hfact (ME.MCell (ME.ZLit 886368) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 226))) H72.
  hcell 886976 1%nat 0. rename HC into H680.
  hcell 886336 4%nat 18446744073709551615. rename HC into H40.
  hcell 886352 1%nat 0. rename HC into H56.
  pose proof inst112 as H112. pose proof inst984 as H984.
  split. { rewrite al_space_beg_eq. exact H32. }
  split. { rewrite al_space_beg_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37) with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia. exact H48. }
  split; [exact H64|]. split; [rewrite al_ptr_eq; exact H72|]. split; [exact H112|]. split; [exact H680|]. split; [exact H984|].
  split; [| exact H56].
  apply (rw_cells_recast bsegs m 886336 [C4 (Z_to_bv 64 18446744073709551615)]); [exact H40| cbn; auto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
Qed.

Lemma acache_main : forall c, 1 <= c < K_NUM_CLASSES -> acache_cells L st0 X0 m c.
Proof.
  intros c Hc. unfold acache_cells, acache_addr. rewrite get_cls_st0, max_count_st0. cbn [x_cls X0 xc_cache xc0 c_count aclass0 map app].
  unfold st0, ainit. cbn [a_cinit]. unfold K_NUM_CLASSES in Hc.
  exists (repeat (Z_to_bv 64 0) 16). split; [| split; [| rewrite repeat_length; reflexivity]].
  - apply zrun_cells; [cbn; auto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add].
    apply (zrun_sub _ _ _ _ thr_zrun); lia.
  - apply zrun_u32arr. apply (zrun_sub _ _ _ _ thr_zrun); cbn; lia.
Qed.

Lemma al_top_eq : al_top L = 32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat).
Proof.
  pose proof (hp 35 _ eq_refl) as P. cbn [ME.pfact_ok ME.zv] in P. unfold ME.two64 in P.
  pose proof (hp 22 _ eq_refl) as P344. cbn [ME.pfact_ok] in P344.
  pose proof (hp 6 _ eq_refl) as P6. cbn [ME.pfact_ok] in P6.
  unfold al_top. rewrite al_sp0_eq. unfold page_round_up_Z, page_size.
  assert (C : V 344%nat = 0 /\ 16 * V 6%nat <= 160 \/ V 344%nat = 1 /\ 161 <= 16 * V 6%nat).
  { destruct (Z.eq_dec (V 344%nat) 0) as [E|E]; [left| right]; (split; [lia|]).
    - rewrite E in P. rewrite Z.mod_small in P by lia. lia.
    - assert (E1 : V 344%nat = 1) by lia. rewrite E1 in P.
      destruct (Z_lt_ge_dec (16 * V 6%nat + -4096 * 1 + 3935) 0) as [NEG|POS]; [| rewrite Z.mod_small in P by lia; lia].
      exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in P by lia. rewrite Z.mod_small in P by lia. lia. }
  destruct C as [[E B]|[E B]]; rewrite E; Z.div_mod_to_equations; lia.
Qed.

Lemma athread_main : athread L st0 X0 m.
Proof.
  unfold athread.
  hfact (ME.MCell (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 228))) T0.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 8)) 8%nat (ME.ZAdd (ME.ZMul (ME.ZLit 32768) (ME.ZV 0)) (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 10)) (ME.ZMul (ME.ZLit 4096) (ME.ZV 344))))) T8.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 16)) 8%nat (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 32768) (ME.ZV 0)) (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 10)) (ME.ZMul (ME.ZLit 4096) (ME.ZV 344)))) (ME.ZLit (-8388608)))) T16.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 40)) 1%nat (ME.ZLit 0)) T40.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 3168)) 1%nat (ME.ZLit 0)) T3168.
  rewrite al_t_eq, al_ctx_eq. unfold al_bot. rewrite al_top_eq.
  split.
  { apply (rw_cells_glue _ 8 [_]); [exact T0| | reflexivity].
    apply (rw_cells_glue _ 8 [_]); [exact T8| | reflexivity].
    replace (4096 * V 227%nat + 8 + 8) with (4096 * V 227%nat + 16) by lia.
    replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) - 8388608) with (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) + -8388608) by lia.
    exact T16. }
  split; [exact T40|]. split; [exact acache_main|].
  split. { rewrite <- al_t_eq. apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ thr_zrun); lia. }
  split. { exists (repeat (Z_to_bv 64 0) ASTATS_WORDS). split; [| apply repeat_length]. rewrite <- al_t_eq. apply zrun_u64arr. apply (zrun_sub _ _ _ _ thr_zrun); unfold ASTATS_WORDS; cbn; lia. }
  exact T3168.
Qed.

Lemma ao_t_main : aobj (al_t L) 4096.
Proof.
  rewrite al_t_eq. hpf 17%nat P1. hpf 104%nat D1. hpf 106%nat D2.
  hpf 105%nat D3.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_ctx_main : aobj (al_ctx L) 65536.
Proof.
  rewrite al_ctx_eq. hpf 18%nat P1. hpf 116%nat D1. hpf 117%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_nodes_main : aobj (al_nodes L) 1048576.
Proof.
  rewrite al_nodes_eq. hpf 32%nat P1. hpf 161%nat D1. hpf 162%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_store_main : aobj (al_store L) 8388608.
Proof.
  rewrite al_store_eq. hpf 33%nat P1. hpf 166%nat D1. hpf 167%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_fake_main : aobj (al_fake L) 11571200.
Proof.
  rewrite al_fake_eq. hpf 24%nat P1. hpf 149%nat D1. hpf 150%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_res_main : aobj (al_res L) 137439023104.
Proof.
  rewrite al_res_eq. hpf 14%nat P1. hpf 79%nat D1. hpf 80%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_ptr_main : aobj (al_ptr_array L) 8388608.
Proof.
  rewrite al_ptr_eq. hpf 16%nat P1. hpf 92%nat D1. hpf 93%nat D2.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ao_dtls_main : aobj (al_dtls L) 4096.
Proof.
  rewrite al_dtls_eq. hpf 20%nat P1. hpf 136%nat D1. hpf 138%nat D2.
  hpf 137%nat D3.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 6%nat) as B6. pose proof (HV 10%nat) as B10.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI. split; [rewrite Z.mul_comm; apply Z_mod_mult| lia].
Qed.

Lemma ad_t_res_main : adisj (al_t L) 4096 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_t_eq, al_res_eq. hpf 82%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_ctx_res_main : adisj (al_ctx L) 65536 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_ctx_eq, al_res_eq. hpf 83%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_nodes_res_main : adisj (al_nodes L) 1048576 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_nodes_eq, al_res_eq. hpf 88%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_res_main : adisj (al_store L) 8388608 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_store_eq, al_res_eq. hpf 89%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_fake_res_main : adisj (al_fake L) 11571200 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_fake_eq, al_res_eq. hpf 87%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_ptr_res_main : adisj (al_ptr_array L) 8388608 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_ptr_eq, al_res_eq. hpf 81%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_t_ctx_main : adisj (al_t L) 4096 (al_ctx L) 65536.
Proof. unfold adisj. rewrite al_t_eq, al_ctx_eq. hpf 107%nat D. exact D. Qed.

Lemma ad_t_nodes_main : adisj (al_t L) 4096 (al_nodes L) 1048576.
Proof. unfold adisj. rewrite al_t_eq, al_nodes_eq. hpf 112%nat D. exact D. Qed.

Lemma ad_t_store_main : adisj (al_t L) 4096 (al_store L) 8388608.
Proof. unfold adisj. rewrite al_t_eq, al_store_eq. hpf 113%nat D. exact D. Qed.

Lemma ad_t_fake_main : adisj (al_t L) 4096 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_t_eq, al_fake_eq. hpf 111%nat D. exact D. Qed.

Lemma ad_t_ptr_main : adisj (al_t L) 4096 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_t_eq, al_ptr_eq. hpf 94%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_ctx_nodes_main : adisj (al_ctx L) 65536 (al_nodes L) 1048576.
Proof. unfold adisj. rewrite al_ctx_eq, al_nodes_eq. hpf 122%nat D. exact D. Qed.

Lemma ad_ctx_store_main : adisj (al_ctx L) 65536 (al_store L) 8388608.
Proof. unfold adisj. rewrite al_ctx_eq, al_store_eq. hpf 123%nat D. exact D. Qed.

Lemma ad_ctx_fake_main : adisj (al_ctx L) 65536 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_ctx_eq, al_fake_eq. hpf 121%nat D. exact D. Qed.

Lemma ad_ctx_ptr_main : adisj (al_ctx L) 65536 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_ctx_eq, al_ptr_eq. hpf 95%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_nodes_store_main : adisj (al_nodes L) 1048576 (al_store L) 8388608.
Proof. unfold adisj. rewrite al_nodes_eq, al_store_eq. hpf 163%nat D. exact D. Qed.

Lemma ad_nodes_fake_main : adisj (al_nodes L) 1048576 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_nodes_eq, al_fake_eq. hpf 151%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_nodes_ptr_main : adisj (al_nodes L) 1048576 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_nodes_eq, al_ptr_eq. hpf 100%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_fake_main : adisj (al_store L) 8388608 (al_fake L) 11571200.
Proof. unfold adisj. rewrite al_store_eq, al_fake_eq. hpf 152%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_ptr_main : adisj (al_store L) 8388608 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_store_eq, al_ptr_eq. hpf 101%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_fake_ptr_main : adisj (al_fake L) 11571200 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_fake_eq, al_ptr_eq. hpf 99%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_dtls_res_main : adisj (al_dtls L) 4096 (al_res L) 137439023104.
Proof. unfold adisj. rewrite al_dtls_eq, al_res_eq. hpf 85%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_t_dtls_main : adisj (al_t L) 4096 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_t_eq, al_dtls_eq. hpf 109%nat D. exact D. Qed.

Lemma ad_ctx_dtls_main : adisj (al_ctx L) 65536 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_ctx_eq, al_dtls_eq. hpf 119%nat D. exact D. Qed.

Lemma ad_nodes_dtls_main : adisj (al_nodes L) 1048576 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_nodes_eq, al_dtls_eq. hpf 141%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_store_dtls_main : adisj (al_store L) 8388608 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_store_eq, al_dtls_eq. hpf 142%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_fake_dtls_main : adisj (al_fake L) 11571200 (al_dtls L) 4096.
Proof. unfold adisj. rewrite al_fake_eq, al_dtls_eq. hpf 140%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma ad_dtls_ptr_main : adisj (al_dtls L) 4096 (al_ptr_array L) 8388608.
Proof. unfold adisj. rewrite al_dtls_eq, al_ptr_eq. hpf 97%nat D. destruct D as [D|D]; [right; exact D| left; exact D]. Qed.

Lemma space_mod_main : (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat.
Proof.
  hpf 37%nat P. hpf 15%nat R9. pose proof (HV 208%nat) as B8. unfold ME.two64 in P.
  change 65535 with (Z.ones 16) in P. rewrite Z.land_ones in P by lia. change (2 ^ 16) with 65536 in P.
  assert (M : 0 <= (4096 * V 208%nat) mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_ge_dec (-4096 * V 209%nat + (4096 * V 208%nat) mod 65536) 0) as [NEG|POS].
  - exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in P by lia. rewrite Z.mod_small in P by lia. lia.
  - rewrite Z.mod_small in P by lia. lia.
Qed.
Lemma ao_space_main : al_res L + 4096 <= al_space_beg L <= al_res L + 65536.
Proof.
  rewrite al_res_eq, al_space_beg_eq. hpf 15%nat R9. lia.
Qed.
Lemma ao_space_al_main : al_space_beg L mod 65536 = 0.
Proof.
  rewrite al_space_beg_eq. pose proof space_mod_main as SM. pose proof (HV 208%nat) as B8.
  replace (4096 * V 208%nat + -4096 * V 209%nat + 65536) with ((4096 * V 208%nat - (4096 * V 208%nat) mod 65536) + 1 * 65536) by lia.
  rewrite Z.mod_add by lia. rewrite <- Zminus_mod_idemp_l. rewrite Z.sub_diag. reflexivity.
Qed.
Lemma ao_res_hi_main : 0x10007fff8000 <= al_res L.
Proof. rewrite al_res_eq. hpf 14%nat P. lia. Qed.

Lemma v344_cases : (V 344%nat = 0 /\ 16 * V 6%nat <= 160) \/ (V 344%nat = 1 /\ 161 <= 16 * V 6%nat).
Proof.
  hpf 35%nat P. unfold ME.two64 in P. hpf 22%nat P344. hpf 6%nat P6.
  destruct (Z.eq_dec (V 344%nat) 0) as [E|E]; [left| right]; (split; [lia|]).
  - rewrite E in P. rewrite Z.mod_small in P by lia. lia.
  - assert (E1 : V 344%nat = 1) by lia. rewrite E1 in P.
    destruct (Z_lt_ge_dec (16 * V 6%nat + -4096 * 1 + 3935) 0) as [NEG|POS]; [| rewrite Z.mod_small in P by lia; lia].
    exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in P by lia. rewrite Z.mod_small in P by lia. lia.
Qed.
Lemma ao_stack_main : al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936).
Proof.
  unfold al_bot. rewrite al_top_eq. pose proof v344_cases as C. pose proof HUSP as HU0. unfold usp_pin in HU0. hpf 41%nat P. unfold ME.two64 in P.
  pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. hpf 6%nat P6. rewrite Z.mod_small in P by lia.
  split; [lia|]. split; [| lia].
  replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat)) with ((8 * V 0%nat + V 10%nat + V 344%nat) * 4096) by lia. apply Z_mod_mult.
Qed.

Theorem alayout_ok_main : alayout_ok L.
Proof.
  constructor.
  - exact ao_t_main. - exact ao_ctx_main. - exact ao_nodes_main. - exact ao_store_main. - exact ao_fake_main. - exact ao_res_main.
  - exact ao_ptr_main. - exact ao_dtls_main. - exact ao_res_hi_main. - exact ao_space_main. - exact ao_space_al_main.
  - exact ad_t_res_main. - exact ad_ctx_res_main. - exact ad_nodes_res_main. - exact ad_store_res_main. - exact ad_fake_res_main. - exact ad_ptr_res_main.
  - exact ad_t_ctx_main. - exact ad_t_nodes_main. - exact ad_t_store_main. - exact ad_t_fake_main. - exact ad_t_ptr_main.
  - exact ad_ctx_nodes_main. - exact ad_ctx_store_main. - exact ad_ctx_fake_main. - exact ad_ctx_ptr_main.
  - exact ad_nodes_store_main. - exact ad_nodes_fake_main. - exact ad_nodes_ptr_main.
  - exact ad_store_fake_main. - exact ad_store_ptr_main. - exact ad_fake_ptr_main.
  - exact ad_dtls_res_main. - exact ad_t_dtls_main. - exact ad_ctx_dtls_main. - exact ad_nodes_dtls_main. - exact ad_store_dtls_main. - exact ad_fake_dtls_main.
  - exact ad_dtls_ptr_main.
  - exact ao_stack_main.
  - cbn [al_U L L0]. unfold AUMAX. pose proof HU as HU1. unfold univ_ok in HU1. exact (proj1 HU1).
Qed.

End AtMain.
End TwinB.
