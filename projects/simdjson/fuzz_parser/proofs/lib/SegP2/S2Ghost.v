(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjStage1 SjInvPath SjS2Inv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Section G.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Definition mbyte (m : word -> option byte) (a : Z) : Z :=
    match rdn segs m (Z_to_bv 64 a) 1 with Some [b] => bv_unsigned b | _ => 0 end.

  (* [comment removed for export] *)
  Definition mdata (m : word -> option byte) (B L : Z) : list Z := map (fun i => mbyte m (B + Z.of_nat i)) (seq 0 (Z.to_nat L)).

  Lemma mdata_length : forall m B L, 0 <= L -> Z.of_nat (length (mdata m B L)) = L.
  Proof. intros. unfold mdata. rewrite length_map, length_seq. lia. Qed.

  Lemma mdata_byte : forall m B L i, 0 <= i < L -> byte_at (mdata m B L) i = mbyte m (B + i).
  Proof.
    intros m B L i Hi. unfold byte_at, mdata.
    rewrite (nth_indep _ 0 (mbyte m (B + Z.of_nat 0))) by (rewrite length_map, length_seq; lia).
    change (mbyte m (B + Z.of_nat 0)) with ((fun j : nat => mbyte m (B + Z.of_nat j)) 0%nat).
    rewrite map_nth, seq_nth by lia. f_equal. lia.
  Qed.

  Definition GP (id : nat) (args : list word) (m : word -> option byte) : Prop :=
    match id, args with
    | O, [b; l; p; q] =>
        bv_unsigned b + bv_unsigned l + 64 < 2 ^ 64 /\ bv_unsigned q < bv_unsigned l /\
        bpath (mdata m (bv_unsigned b) (bv_unsigned l)) (bv_unsigned l) (bv_unsigned p) (bv_unsigned q)
    | _, _ => False
    end.

  Definition gfp (id : nat) (args : list expr) : list SG.gwin :=
    match id, args with
    | O, [b; l; _; _] => [(b, 0, l)]
    | _, _ => []
    end.

  (* [comment removed for export] *)
  Lemma mbyte_ext : forall m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte m' a = mbyte m a.
  Proof. intros m m' a H. unfold mbyte. cbn [rdn]. rewrite H. reflexivity. Qed.

  Lemma mdata_ext : forall m m' B L, 0 <= B -> 0 <= L -> B + L < 2 ^ 64 ->
    (forall x : word, B <= bv_unsigned x < B + L -> m' x = m x) -> mdata m' B L = mdata m B L.
  Proof.
    intros m m' B L HB HL HBL H. unfold mdata. apply map_ext_in. intros i Hi. apply in_seq in Hi.
    apply mbyte_ext. apply H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma gp_frame : SG.gp_frameP GP gfp.
  Proof.
    unfold SG.gp_frameP. intros id args E M M' Hagree HG.
    destruct id as [|id]; [|destruct args; cbn in HG; contradiction].
    destruct args as [|b [|l [|p [|q [|]]]]]; cbn [map GP] in HG |- *; try contradiction.
    destruct HG as (HBL & HQ & HP). split; [exact HBL|]. split; [exact HQ|].
    pose proof (bv_unsigned_in_range _ (edenot E b)) as Rb. pose proof (bv_unsigned_in_range _ (edenot E l)) as Rl.
    rewrite (mdata_ext M M'); [exact HP| lia | lia | lia |].
    intros x Hx. apply Hagree. exists (b, 0, l). split; [cbn; left; reflexivity|]. cbn [SG.win_den]. lia.
  Qed.

End G.
