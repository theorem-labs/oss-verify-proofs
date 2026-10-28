(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Definition htons_entry := 0x19ff0%Z.

Definition htons_expr (x : Z) : Z :=
  Z.lor (Z.shiftl x 8 mod 18446744073709551616) (Z.shiftr x 8) mod 65536.

Section ZFacts.
  Local Open Scope Z_scope.
  #[using="Type"] Lemma htons_eval : forall x, 0 <= x < 65536 -> htons_expr x = htons_z x.
  Proof.
    intros x Hx. unfold htons_expr, htons_z.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    rewrite (Z.mod_small (x * 256)) by lia.
    assert (D1 : 0 <= x / 256) by (apply Z.div_pos; lia).
    assert (D2 : x / 256 < 256) by (apply Z.div_lt_upper_bound; lia).
    rewrite (lor_add (x * 256) (x / 256) 8); [| lia | change (2^8) with 256; lia | change (2^8) with 256; rewrite Z.mul_comm, Z.mul_mod by lia; reflexivity ].
    rewrite (Z.div_mod x 256) at 1 by lia.
    replace ((256 * (x / 256) + x mod 256) * 256 + x / 256) with ((x mod 256) * 256 + x / 256 + (x / 256) * 65536) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small.
    pose proof (Z.mod_pos_bound x 256). lia.
  Qed.
End ZFacts.

Definition htons_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Ltac pg := match goal with |- ?G => idtac G end.

Lemma htons_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned a0 < 65536)%Z ->
  mem_inv rsegs m ->
  evt rsegs (htons_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (htons_z (bv_unsigned a0)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19ff0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros Hx MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as R0.
  do 5 zstep.
  lazymatch goal with |- context [Some (Z_to_bv 64 (?e mod 65536))] =>
    change (Z_to_bv 64 (e mod 65536)) with (Z_to_bv 64 (htons_expr (bv_unsigned a0))) end.
  rewrite (htons_eval (bv_unsigned a0)) by lia.
  zstep. finish.
Qed.
