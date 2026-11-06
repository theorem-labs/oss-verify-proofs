(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition memtoshadow_entry : Z := 0x5558c.
End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition a_high_mem (SB p : Z) : Prop := SB + 0x100000000000 <= p <= A_HIGHEND_VAL.
Definition a_in_mem (SB p : Z) : Prop := (0 <= p < SB) \/ a_high_mem SB p.

Definition memtoshadow_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (SB p : Z) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SB + Z.shiftr p 3)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (SB p : Z).
Hypothesis MI : mem_inv bsegs m.
Hypothesis G : icp_globals bsegs m SB.
Hypothesis HP : a_in_mem SB p.
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).

Notation POST := (memtoshadow_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SB p).

Lemma memtoshadow_body : forall x10, x10 = Z_to_bv 64 p ->
  evtA bsegs P POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memtoshadow_entry) fc None m (seg_rom bsegs)).
Proof.
  intros x10 ->. unfold memtoshadow_entry.
  assert (MU : munch [] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
  unfold a_in_mem, a_high_mem, A_HIGHEND_VAL in HP.
  pose proof G as G'. icp_globals_open G.
  stepA. stepA. stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  replace (SB <? SB + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
  change ((-1) mod 18446744073709551616) with (Z.ones 64).
  rewrite (Z.land_comm (Z.ones 64)), Z.land_ones, Z.mod_small by lia.
  zstepA. (* [comment removed for export] *) if_cases KL; zify_cond KL.
  - (* [comment removed for export] *) zstepA. zstepA. zstepA. (* [comment removed for export] *) finishA.
  - (* [comment removed for export] *)
    stepA. stepA. stepA. stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    if_cases KM; zify_cond KM. 2:{ exfalso. revert KM. cbn. lia. }
    stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) if_cases KH1; zify_cond KH1. { exfalso. revert KH1. cbn. lia. }
    zstepA. (* [comment removed for export] *) if_cases KH2; zify_cond KH2. { exfalso. revert KH2. cbn. lia. }
    zstepA. zstepA. zstepA. (* [comment removed for export] *) finishA.
Qed.
End Walk.

Lemma memtoshadow_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (SB p : Z) (P : acc -> Prop),
  mem_inv bsegs m -> icp_globals bsegs m SB -> a_in_mem SB p -> a0 = Z_to_bv 64 p ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (memtoshadow_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SB p)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memtoshadow_entry) fc None m (seg_rom bsegs)).
Proof. intros. eapply memtoshadow_body; eassumption. Qed.
End RC__2.
