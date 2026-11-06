(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit.
Import ListNotations.
Open Scope Z_scope.

Definition A0_m2s : Z := 0x59cfc.
Definition m2s_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t1 t2 t3 t4 t5 t6 : word) (p : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (sh p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Lemma m2s_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p : Z),
  mem_inv asegs m -> env_shadow m -> env_layout m ->
  a0 = wz p ->
  (0 <= p /\ p < 0x7fff8000) \/ (0x10007fff8000 <= p /\ p < 2^47) ->
  evt asegs (m2s_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t1 t2 t3 t4 t5 t6 p m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_m2s) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros MI (GOT & SHB) (LG & LC) -> APP. unfold A0_m2s.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 8 zstep.
  fold_lits.
  if_cases K; zify_cond K.
  - do 3 zstep.
    replace (2147450880 + Z.shiftr p 3) with (sh p) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; lia).
    finish.
  - do 7 zstep. fold_lits. zsimp. zstep.
    if_cases K2; zify_cond K2.
    2:{ exfalso. lia. }
    do 5 zstep. fold_lits.
    zstep.
    if_cases K3; zify_cond K3. { exfalso; lia. }
    zstep.
    if_cases K4; zify_cond K4. { exfalso; lia. }
    do 3 zstep.
    replace (2147450880 + Z.shiftr p 3) with (sh p) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; lia).
    finish.
Qed.
