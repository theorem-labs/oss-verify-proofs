(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim.
Import ListNotations.
Open Scope Z_scope.

Definition malloc_hooks_entry := 0x66608%Z.
Definition free_hooks_entry := 0x666c4%Z.
Notation HOOKS := 1332160%Z.

Definition hooks_env (m : mem) : Prop := rw_cells asegs m HOOKS [C8 (wz 0); C8 (wz 0)].

Section HK.
  Context {HC : HasCeiling}.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q : Z) (m0 : mem).

  Definition free_hooks_post (lo : Z) : machine_state -> Prop :=
    fun ms' => exists a1 a2 m', ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 32, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

  #[using="Type"] Lemma free_hooks_spec : forall lo a0 a1 a2,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 32 -> q mod 16 = 0 -> q <= 2^47 ->
    hooks_env m0 -> mem_inv asegs m0 ->
    evt asegs (free_hooks_post lo)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz free_hooks_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo a0 a1 a2 ST CLO LO AL QH HE MI. unfold free_hooks_entry. unfold hooks_env in HE.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 32, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 32%nat ST. rewrite !E in *.
    zstep. do 3 zstep.
    zstep.
    zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0; [| exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia]. clear K0.
    zstep. zstep. zstep.
    zstep. zstep.
    zstep.
    zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear; intros K1; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    zstep.
    do 3 zstep.
    zstep. replace (q + -32 + 32) with q by lia.
    zstep.
    release_frame FR ST q.
    apply evt_done. unfold free_hooks_post. eexists _, _, _. split; [reflexivity|].
    replace (q - 32) with (q + -32) by lia.
    split; [exact MU|]. split; [exact WM|]. split; assumption.
  Qed.

  Definition malloc_hooks_post (lo : Z) : machine_state -> Prop :=
    fun ms' => exists a0 a1 a2 m', ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 32, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

  #[using="Type"] Lemma malloc_hooks_spec : forall lo a0 a1 a2,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 32 -> q mod 16 = 0 -> q <= 2^47 ->
    hooks_env m0 -> mem_inv asegs m0 ->
    evt asegs (malloc_hooks_post lo)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz malloc_hooks_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo a0 a1 a2 ST CLO LO AL QH HE MI. unfold malloc_hooks_entry. unfold hooks_env in HE.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 32, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 32%nat ST. rewrite !E in *.
    zstep. do 4 zstep.
    do 2 zstep.
    zstep. zstep.
    zstep. zstep.
    zstep.
    zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear; intros K1; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    do 4 zstep.
    zstep. replace (q + -32 + 32) with q by lia.
    zstep.
    release_frame FR ST q.
    apply evt_done. unfold malloc_hooks_post. eexists _, _, _, _. split; [reflexivity|].
    replace (q - 32) with (q + -32) by lia.
    split; [exact MU|]. split; [exact WM|]. split; assumption.
  Qed.
End HK.
