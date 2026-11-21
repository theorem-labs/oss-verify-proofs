(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ flag, the new auxv layout, the init stack window and the vDSO). *)

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
(* The 08b1429 entry block (StackLayout.build_stack_bytes): the head is
   argc | argv | 0 | envp | 0 | auxv (29 pairs, the default kernel) | an 8-byte
   gap when argc + envc + 3 is odd | 16 AT_RANDOM bytes, then the
   arch_align_stack pad, then the strings ending 8 bytes below the stack top.
   [v_par] is the gap bit, [v_g] the distance from the auxv's end to argv[0]
   (gap + random + pad), and the rest are the auxv values the block now holds. *)
Definition v_par : int := 14%uint63.
Definition v_g : int := 15%uint63.
Definition v_gid : int := 16%uint63.
Definition v_ent : int := 17%uint63.
Definition v_vd : int := 18%uint63.
Definition v_mss : int := 19%uint63.
Definition v_xl : int := 20%uint63.

Definition lenvar (k : Z) : int := of_Z (2 ^ 41 + k).
Definition strvar (k j : Z) : int := of_Z (2 ^ 40 + k * 2 ^ 17 + j).
Definition elenvar (k : Z) : int := of_Z (2 ^ 42 + k).
Definition estrvar (k j : Z) : int := of_Z (2 ^ 42 + 2 ^ 20 + k * 2 ^ 17 + j).
Definition xstrvar (j : Z) : int := of_Z (2 ^ 43 + j).

Definition entry_var (v : int) : bool := (v <? 100)%uint63 || (1099511627776 <=? v)%uint63.

Definition sp_terms : terms := [(v_x0, 16); (v_x1, 64); (v_x2, 4096); (v_x3, 32768)].

Definition sp_val (ρ : valuation) : Z := teval ρ sp_terms.

Definition dec_strs (ρ : valuation) (cnt : int) (len : Z -> int) (bytev : Z -> Z -> int) : list (list byte) :=
  map (fun k => map (fun j => Z_to_bv 8 (ρ (bytev (Z.of_nat k) (Z.of_nat j)))) (seq 0 (Z.to_nat (ρ (len (Z.of_nat k))))))
      (seq 0 (Z.to_nat (ρ cnt))).

Definition dec_argv (ρ : valuation) : list (list byte) := dec_strs ρ v_argc lenvar strvar.
Definition dec_envp (ρ : valuation) : list (list byte) := dec_strs ρ v_envc elenvar estrvar.

Definition dec_execfn (ρ : valuation) : list byte :=
  map (fun j => Z_to_bv 8 (ρ (xstrvar (Z.of_nat j)))) (seq 0 (Z.to_nat (ρ v_xl))).

Definition dec_random (ρ : valuation) : bv 128 := Z_to_bv 128 (ρ v_r0 mod 2 ^ 64 + 2 ^ 64 * (ρ v_r1 mod 2 ^ 64)).

(** argv[0]'s offset from [sp].  [r] is the launch's rseq flag: the auxv holds 29 pairs
    under it and 27 without, so this is 488 at [true] and 456 at [false]
    ([StackLayout.auxv_size]).  rseq is NOT pinned, so every definition below carries [r]. *)
Definition str_off (r : bool) (ρ : valuation) : Z :=
  24 + Z.of_nat (auxv_size r) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g.

(** the stack top: the strings, the execfn and its NUL, then 8 zero bytes *)
Definition dec_top (r : bool) (ρ : valuation) : Z := sp_val ρ + str_off r ρ + ρ v_ta + ρ v_te + ρ v_xl + 1 + 8.

Definition dec_draw (r : bool) (ρ : valuation) : EntryDraw :=
  mkDraw (dec_random ρ) (Z_to_bv 64 (dec_top r ρ)) vdso_keeps_all.

(** [Run.launch_auxv]: the vDSO base and AT_MINSIGSTKSZ are read off the valuation, the cache
    words are the pinned ones, and the rseq flag is [r]. *)
Definition dec_la (r : bool) (ρ : valuation) : LaunchAuxv :=
  mkLaunchAuxv (Z_to_bv 64 (ρ v_vd)) (launch_cache_words default_kernel) (Z_to_bv 64 (ρ v_mss)) r.

Definition eb_image (r : bool) (ph : PhdrInfo) (ρ : valuation) : list byte :=
  build_stack_bytes (dec_la r ρ) ph (Z_to_bv 64 (ρ v_ent)) (Z_to_bv 64 (sp_val ρ)) (Z_to_bv 64 (dec_top r ρ))
    (dec_argv ρ) (dec_envp ρ) (dec_execfn ρ)
    (Z_to_bv 64 (ρ v_uid)) (Z_to_bv 64 (ρ v_gid)) (Z_to_bv 64 (ρ v_hw)) (dec_draw r ρ).

Definition eb_facts (r : bool) (ρ : valuation) : Prop :=
  1 <= ρ v_argc <= 1024 /\ 0 <= ρ v_envc <= 256
  /\ (forall k, 0 <= k < ρ v_argc -> 0 <= ρ (lenvar k) <= 131071
                /\ forall j, 0 <= j < ρ (lenvar k) -> 1 <= ρ (strvar k j) < 256)
  /\ (forall k, 0 <= k < ρ v_envc -> 0 <= ρ (elenvar k) <= 131071
                /\ forall j, 0 <= j < ρ (elenvar k) -> 1 <= ρ (estrvar k j) < 256)
  /\ ρ v_ta = total_arg_bytes (dec_argv ρ) /\ ρ v_te = total_arg_bytes (dec_envp ρ)
  /\ ρ v_par = (ρ v_argc + ρ v_envc + 1) mod 2
  /\ 16 + 8 * ρ v_par <= ρ v_g <= 16 + 8 * ρ v_par + 4110
  /\ (0 <= ρ v_xl <= 4114 /\ (forall j, 0 <= j < ρ v_xl -> 0 <= ρ (xstrvar j) < 256))
  /\ 0 <= ρ v_r0 < 2 ^ 64 /\ 0 <= ρ v_r1 < 2 ^ 64
  /\ 0 <= ρ v_uid < 2 ^ 32 /\ 0 <= ρ v_hw < 2 ^ 64 /\ 0 <= ρ v_gid < 2 ^ 32
  /\ 0 <= ρ v_ent < 2 ^ 64 /\ 0 <= ρ v_vd < 2 ^ 64 /\ 0 <= ρ v_mss < 2 ^ 64
  /\ sp_window_lo <= sp_val ρ /\ dec_top r ρ <= sp_window_hi /\ dec_top r ρ mod 8 = 0.

Definition eb_rel (r : bool) (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (base nR : Z) : Prop :=
  eb_facts r ρ /\ base = sp_val ρ /\ Z.of_nat (length (eb_image r ph ρ)) <= nR
  /\ forall z, 0 <= z < Z.of_nat (length (eb_image r ph ρ)) -> m (Z_to_bv 64 (base + z)) = Some (nth (Z.to_nat z) (eb_image r ph ρ) (Z_to_bv 8 0)).
