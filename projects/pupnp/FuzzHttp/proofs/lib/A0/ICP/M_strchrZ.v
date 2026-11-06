(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit M_strchrnul.
Import ListNotations.
Open Scope Z_scope.

Definition strchr_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S c : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 32, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack)
    /\ strchr_res S str c r.

Lemma strchr_specZ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (S c : Z) (str slack : list byte) (lo : Z),
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  stk asegs m lo q -> lo <= q - 32 ->
  (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= q - 32 \/ q <= S) ->
  mem_inv asegs m -> 0 <= S < 2^64 -> 0 <= q < 2^64 -> 0 < c < 256 ->
  evt asegs (strchr_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S c str slack lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xa2314) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros STR NONUL PAD ST LO SEP MI HS HQ HC.
  assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 c) mod 256 = c) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evt_mono.
  { eapply strchr_spec with (str := str) (slack := slack) (lo := lo); rewrite ?Es, ?Eq, ?Ec; eauto. lia. }
  intros ms' Q. unfold strchr_post in Q. rewrite !Es, !Eq, !Ec in Q. exact Q.
Qed.
