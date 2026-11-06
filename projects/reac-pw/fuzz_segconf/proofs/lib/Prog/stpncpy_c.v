(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/pupnp/FuzzHttp/lib/P0/F_stpncpy.v, with its module paths and module names changed; 7 of its 37 lines of code are new or changed and 445 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
Import ListNotations.
Open Scope bv_scope.

(* musl __stpncpy (segconf plain 0x1ee0c, 272 B), the callee of strncpy. Contract restated from the walk
   P0/F_stpncpy.v (stpncpy_spec; re-walked from pupnp/FuzzHttp's). *)
Definition STPNCPY : Z := 0x1ee0c.

(* The bytes stpncpy leaves at the destination: the first min(|str|, n) bytes of str, then NUL padding to n. *)
Definition stpn_k (str : list byte) (n : nat) : nat := Nat.min (length str) n.
Definition stpn_result (str : list byte) (n : nat) : list byte :=
  firstn (stpn_k str n) str ++ repeat (Z_to_bv 8 0) (n - stpn_k str n)%nat.

Definition stpncpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (stpn_k str (Z.to_nat (bv_unsigned a2)))))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ u8arr rsegs m' (bv_unsigned a0) (stpn_result str (Z.to_nat (bv_unsigned a2)))
    /\ bytes_at rsegs m' (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).

Definition stpncpy_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack bs : list byte) (lo : Z),
  u8arr rsegs m (bv_unsigned a0) bs -> length bs = Z.to_nat (bv_unsigned a2) ->
  bytes_at rsegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1 \/ bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z ->
  mem_inv rsegs m ->
  evt rsegs (stpncpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STPNCPY) fc None m (seg_rom rsegs)).
