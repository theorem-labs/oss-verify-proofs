(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Definition v_x0 : int := 0%uint63.
Definition v_x1 : int := 1%uint63.
Definition v_x2 : int := 2%uint63.
Definition v_x3 : int := 3%uint63.
Definition v_b : int := 4%uint63.
Definition v_r0 : int := 5%uint63.
Definition v_r1 : int := 6%uint63.
Definition v_hw : int := 7%uint63.
Definition v_uid : int := 8%uint63.
Definition v_argc : int := 9%uint63.
Definition v_envc : int := 10%uint63.
Definition v_ta : int := 11%uint63.
Definition v_te : int := 12%uint63.
Definition v_q : int := 13%uint63.

Definition lenvar (k : Z) : int := of_Z (2 ^ 41 + k).
Definition strvar (k j : Z) : int := of_Z (2 ^ 40 + k * 2 ^ 17 + j).
Definition elenvar (k : Z) : int := of_Z (2 ^ 42 + k).
Definition estrvar (k j : Z) : int := of_Z (2 ^ 42 + 2 ^ 20 + k * 2 ^ 17 + j).

Definition entry_var (v : int) : bool := (v <? 100)%uint63 || (1099511627776 <=? v)%uint63.

Definition sp_terms : terms := [(v_x0, 16); (v_x1, 64); (v_x2, 4096); (v_x3, 32768)].

Definition sp_val (ρ : valuation) : Z := teval ρ sp_terms.

Definition dec_strs (ρ : valuation) (cnt : int) (len : Z -> int) (bytev : Z -> Z -> int) : list (list byte) :=
  map (fun k => map (fun j => Z_to_bv 8 (ρ (bytev (Z.of_nat k) (Z.of_nat j)))) (seq 0 (Z.to_nat (ρ (len (Z.of_nat k))))))
      (seq 0 (Z.to_nat (ρ cnt))).

Definition dec_argv (ρ : valuation) : list (list byte) := dec_strs ρ v_argc lenvar strvar.
Definition dec_envp (ρ : valuation) : list (list byte) := dec_strs ρ v_envc elenvar estrvar.

Definition dec_random (ρ : valuation) : bv 128 := Z_to_bv 128 (ρ v_r0 mod 2 ^ 64 + 2 ^ 64 * (ρ v_r1 mod 2 ^ 64)).

Definition dec_draw (ρ : valuation) : EntryDraw := mkDraw (dec_random ρ) (fun _ => Z_to_bv 8 0).

Definition eb_image (ph : PhdrInfo) (ρ : valuation) : list byte :=
  build_stack_bytes ph (Z_to_bv 64 (sp_val ρ)) (dec_argv ρ) (dec_envp ρ) (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw ρ).

Definition eb_facts (ρ : valuation) : Prop :=
  1 <= ρ v_argc <= 1024 /\ 0 <= ρ v_envc <= 256
  /\ (forall k, 0 <= k < ρ v_argc -> 0 <= ρ (lenvar k) <= 131071
                /\ forall j, 0 <= j < ρ (lenvar k) -> 1 <= ρ (strvar k j) < 256)
  /\ (forall k, 0 <= k < ρ v_envc -> 0 <= ρ (elenvar k) <= 131071
                /\ forall j, 0 <= j < ρ (elenvar k) -> 1 <= ρ (estrvar k j) < 256)
  /\ ρ v_ta = total_arg_bytes (dec_argv ρ) /\ ρ v_te = total_arg_bytes (dec_envp ρ)
  /\ ρ v_q = (ρ v_ta + ρ v_te + 7) / 8
  /\ 0 <= ρ v_r0 < 2 ^ 64 /\ 0 <= ρ v_r1 < 2 ^ 64
  /\ 0 <= ρ v_uid < 2 ^ 32 /\ 0 <= ρ v_hw < 2 ^ 64
  /\ sp_window_lo <= sp_val ρ /\ sp_val ρ + Z.of_nat (length (eb_image (mkPhdrInfo 0 0 0) ρ)) <= sp_window_hi.

Definition eb_rel (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (base nR : Z) : Prop :=
  eb_facts ρ /\ base = sp_val ρ /\ Z.of_nat (length (eb_image ph ρ)) <= nR
  /\ forall z, 0 <= z < Z.of_nat (length (eb_image ph ρ)) -> m (Z_to_bv 64 (base + z)) = Some (nth (Z.to_nat z) (eb_image ph ρ) (Z_to_bv 8 0)).
