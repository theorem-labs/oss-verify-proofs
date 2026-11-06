(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.

Definition au64_pins : list (reg * zx) := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33)].
Definition au64_ctx (lo hi : Z) : ctx := CTX (vi_regs ++ [Some (0, M64 - 516); Some (lo, hi)]) [] [KW (ZV 32) 0 516].

Ltac au64_run lo hi regs m rom :=
  zx_run SEGS_P (au64_ctx lo hi) 60%nat (@nil Z) (SCR [] []) au64_pins
         constr:([ev (Eof regs []) (ZV 32); 0]) constr:([Some (0, M64 - 516); Some (lo, hi)]) regs m rom 0x356d0.

#[using="Type"] Theorem au64_P : forall regs m rom (o v : Z) (ret : word),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 v -> getr regs 1%bv = ret -> ret_ok ret ->
  0 <= v < M64 -> 0 <= o -> o + 516 <= M64 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x356d0) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_P m' o (assign_u64 v) /\ unch m m' [(o, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m rom o v ret R10 R11 R1 Hret Hv Ho Hob Hst.
  assert (KW0 : forall lo hi, kw_conj SEGS_P (Eof regs [o; v]) m (c_kw (au64_ctx lo hi))).
  { intros. cbn [kw_conj c_kw au64_ctx]. kw1 Hst. exact I. }
  unfold bn_at, assign_u64. cbn [cells BnModel.ex].
  (* [comment removed for export] *)
  assert (CASES : v = 0 \/ 1 <= v < B \/ B <= v < B * B \/ B * B <= v < M64) by (unfold B; lia).
  destruct CASES as [Hv0 | [Hv1 | [Hv2 | Hv3]]].
  - (* [comment removed for export] *)
    subst v. rewrite chunks_0.
    zx_run SEGS_P (au64_ctx 0 0) 60%nat (@nil Z) (SCR [] []) au64_pins [o; 0] [Some (0, M64 - 516); Some (0, 0)] regs m rom 0x356d0.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(apply KW0) ltac:(exact I).
    
    assert (R1' : getr regs0 1%bv = ret) by (rewrite <- R1; eapply reg_kept; [exact ZR|reflexivity]).
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|split; [unchx|growsx]].
    pose proof (bn_ctor_store SEGS_P m o ltac:(lia) ltac:(lia)) as [C0 C2].
    unfold zlen. cbn [length Z.of_nat]. repeat split; try lia; try assumption. apply arr32_nil.
  - rewrite chunks_1 by exact Hv1.
    zx_run SEGS_P (au64_ctx 1 (B - 1)) 60%nat (@nil Z) (SCR [] []) au64_pins [o; v] [Some (0, M64 - 516); Some (1, B - 1)] regs m rom 0x356d0.
    zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(exact I) ltac:(apply KW0) ltac:(exact I).
    
    assert (R1' : getr regs0 1%bv = ret) by (rewrite <- R1; eapply reg_kept; [exact ZR|reflexivity]).
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|split; [unchx|growsx]].
    pose proof (bn_ctor_store SEGS_P m o ltac:(lia) ltac:(lia)) as [C0 C2].
    unfold zlen. change (Z.of_nat (length [v])) with 1. unfold B in *.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r. cellx.
  - rewrite chunks_2 by exact Hv2.
    zx_run SEGS_P (au64_ctx B (B * B - 1)) 60%nat (@nil Z) (SCR [] []) au64_pins [o; v] [Some (0, M64 - 516); Some (B, B * B - 1)] regs m rom 0x356d0.
    zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(exact I) ltac:(apply KW0) ltac:(exact I).
    
    assert (R1' : getr regs0 1%bv = ret) by (rewrite <- R1; eapply reg_kept; [exact ZR|reflexivity]).
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|split; [unchx|growsx]].
    pose proof (bn_ctor_store SEGS_P m o ltac:(lia) ltac:(lia)) as [C0 C2].
    unfold zlen. change (Z.of_nat (length [v mod B; v / B])) with 2. unfold B in *.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|]]; [| |lia]; cbn [nth]; zwidth.
    + rewrite Z.mul_0_r, Z.add_0_r. cellx.
    + replace (o + 4 + 4 * 1) with (o + 8) by lia. cellx.
  - rewrite chunks_3 by exact Hv3.
    zx_run SEGS_P (au64_ctx (B * B) (M64 - 1)) 60%nat (@nil Z) (SCR [] []) au64_pins [o; v] [Some (0, M64 - 516); Some (B * B, M64 - 1)] regs m rom 0x356d0.
    zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(exact I) ltac:(apply KW0) ltac:(exact I).
    
    assert (R1' : getr regs0 1%bv = ret) by (rewrite <- R1; eapply reg_kept; [exact ZR|reflexivity]).
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|split; [unchx|growsx]].
    pose proof (bn_ctor_store SEGS_P m o ltac:(lia) ltac:(lia)) as [C0 C2].
    unfold zlen. change (Z.of_nat (length [v mod B; (v / B) mod B; v / B / B])) with 3. unfold B in *.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|[|]]]; [| | |lia]; cbn [nth]; zwidth.
    + rewrite Z.mul_0_r, Z.add_0_r. cellx.
    + replace (o + 4 + 4 * 1) with (o + 8) by lia. cellx.
    + replace (o + 4 + 4 * 2) with (o + 12) by lia. cellx.
Qed.

End S.
