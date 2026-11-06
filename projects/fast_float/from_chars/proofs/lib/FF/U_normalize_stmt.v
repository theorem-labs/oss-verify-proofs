(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition normalize_entry : Z := 0x276ac.

(* [comment removed for export] *)
Fixpoint norm_len (ws : list word) (n : nat) : nat :=
  match n with
  | O => O
  | S n' => if (limbZ ws n' =? 0)%Z then norm_len ws n' else n
  end.

Lemma norm_len_le : forall ws n, (norm_len ws n <= n)%nat.
Proof. induction n as [|n IH]; cbn; [lia|]. destruct (limbZ ws n =? 0)%Z; lia. Qed.

Lemma norm_len_bnorm : forall ws n, bnorm ws (norm_len ws n).
Proof.
  induction n as [|n IH]; cbn. { apply bnorm_0. }
  destruct (Z.eqb_spec (limbZ ws n) 0); [exact IH|]. right. rewrite Nat.sub_1_r. cbn. exact n0.
Qed.

Lemma norm_len_bval : forall ws n, bval ws (norm_len ws n) = bval ws n.
Proof.
  induction n as [|n IH]; cbn -[bval]; [reflexivity|].
  destruct (Z.eqb_spec (limbZ ws n) 0) as [E|]; [|reflexivity]. rewrite IH, bval_S, E. lia.
Qed.

Definition normalize_W (A : Z) : list ivl := [(A + 496, A + 498)]%Z.

Definition normalize_post
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (normalize_W (bv_unsigned a0)) m m'
    /\ wmono USEGS m m'
    /\ u64arr USEGS m' (bv_unsigned a0) ws
    /\ rw_cells USEGS m' (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 (Z.of_nat (norm_len ws (Z.to_nat len))))].

Definition normalize_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    evt USEGS (normalize_post ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x276ac) fc None m (seg_rom USEGS)).
