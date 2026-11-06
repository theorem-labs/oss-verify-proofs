(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnB_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac cellN_go :=
  lazymatch goal with
  | |- cellN _ (wbytes _ (Z_to_bv 64 ?a) (word_to_le_bytes ?n _)) ?x _ _ =>
      first [ replace x with a by ring; apply cellN_store_same';
              [cbn; lia | lia | zwidth; lia | rewrite ?u_Z2bv64; zwidth; rewrite ?Z.mod_mod by lia;
                first [reflexivity | apply Z.mod_small; lia | rewrite (Z.mod_small _ 18446744073709551616) by lia; first [reflexivity | apply Z.mod_small; lia | lia] | lia] ]
            | apply cellN_store_skip; [lia | zwidth; lia | lia | zwidth; lia | zwidth; lia | cellN_go] ]
  | |- cellN _ _ _ _ _ => first [assumption | idtac]
  end.

Ltac obls ZXB Hst Hsts SC1 SC2 OSH :=
    zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kcsh OSH 0; kcsh OSH 0; kcsh OSH 1; kcsh OSH 1; exact I)
      ltac:(kw1 Hst; kw1 Hsts; exact I)
      ltac:(unhide; zx_scs ltac:(lia)).
Ltac fin regs0 ret R1 R2 Hret ZM ZR ZE :=
    let R1' := fresh "R1'" in
    assert (R1' : getr regs0 1%bv = ret) by (etransitivity; [zx_regv ZR|]; etransitivity; [apply Z_to_bv_bv_unsigned | exact R1]);
    eexists regs0, _; split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|];
    split; [apply keeps_CS_of; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | etransitivity; [zx_regv ZR | symmetry; exact R2]]|];
    clear ZM ZE ZR; unhide;
    split; [|split; [unchx|growsx]].

Section S.
Context {fx : FPState}.

(* [comment removed for export] *)
Abbreviation au64_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)].
Abbreviation au64_uvi lo hi := [Some (IMG, HIE - 516); Some (lo, hi); Some (KHI + 16, HIE)].
Abbreviation au64_kn := [KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA);
   KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0);
   KC (ZDivP (ZAdd (ZV 32) (ZL 4)) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 32) (ZL 8)) 3) SHA 1 (ZL 0);
   KC (ZDivP (ZAdd (ZV 32) (ZL 12)) 3) SHA 1 (ZL 0)].
Abbreviation au64_ctx lo hi := (CTX (vi_regs ++ au64_uvi lo hi) au64_kn [KW (ZV 32) 0 516; KW (ZV 34) (-16) 0]).

#[using="Type"] Theorem au64_B : forall regs m rom (o v sp : Z) (ret : word),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 v -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= v < M64 -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 ->
  KHI + 16 <= sp -> sp <= HIE -> (o + 516 <= sp - 16 \/ sp <= o) ->
  shcellsB m -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0a9b60) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_B m' o (assign_u64 v)
    /\ unch m m' [(o, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m rom o v sp ret R10 R11 R2 R1 Hret Hv Ho Hob Ho8 Hsp1 Hsp2 Hdisj [SC1 SC2] OSH Hst Hsts.
  pose proof (u64_range ret) as Rret.
  unfold bn_at, assign_u64. cbn [cells BnModel.ex].
  hide Hdisj.
  (* [comment removed for export] *)
  assert (CASES : v = 0 \/ 1 <= v < B \/ B <= v < B * B \/ B * B <= v < M64) by (unfold B; lia).
  destruct CASES as [Hv0 | [Hv1 | [Hv2 | Hv3]]].
  - (* [comment removed for export] *)
    subst v. rewrite chunks_0.
    zx_run SEGS_B constr:(au64_ctx 0 0) 80%nat (@nil Z) (SCR [] []) constr:(au64_pins) [o; 0; sp]
           constr:(au64_uvi 0 0) regs m rom 0x0a9b60.
    obls ZXB Hst Hsts SC1 SC2 OSH. fin regs0 ret R1 R2 Hret ZM ZR ZE.
    unfold zlen. cbn [length Z.of_nat]. repeat split; try lia; [cellN_go | cellN_go | apply arr32_nil].
  - rewrite chunks_1 by exact Hv1.
    zx_run SEGS_B constr:(au64_ctx 1 (B - 1)) 80%nat (@nil Z) (SCR [] []) constr:(au64_pins) [o; v; sp]
           constr:(au64_uvi 1 (B - 1)) regs m rom 0x0a9b60.
    obls ZXB Hst Hsts SC1 SC2 OSH. fin regs0 ret R1 R2 Hret ZM ZR ZE.
    unfold zlen. change (Z.of_nat (length [v])) with 1. unfold B in *.
    split; [cellN_go|split; [cellN_go|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r. cellN_go.
  - rewrite chunks_2 by exact Hv2.
    zx_run SEGS_B constr:(au64_ctx B (B * B - 1)) 80%nat (@nil Z) (SCR [] []) constr:(au64_pins) [o; v; sp]
           constr:(au64_uvi B (B * B - 1)) regs m rom 0x0a9b60.
    obls ZXB Hst Hsts SC1 SC2 OSH. fin regs0 ret R1 R2 Hret ZM ZR ZE.
    unfold zlen. change (Z.of_nat (length [v mod B; v / B])) with 2. unfold B in *.
    split; [cellN_go|split; [cellN_go|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|]]; [| |lia]; cbn [nth]; zwidth.
    + rewrite Z.mul_0_r, Z.add_0_r. cellN_go.
    + replace (o + 4 + 4 * 1) with (o + 8) by lia. cellN_go.
  - rewrite chunks_3 by exact Hv3.
    zx_run SEGS_B constr:(au64_ctx (B * B) (M64 - 1)) 80%nat (@nil Z) (SCR [] []) constr:(au64_pins) [o; v; sp]
           constr:(au64_uvi (B * B) (M64 - 1)) regs m rom 0x0a9b60.
    obls ZXB Hst Hsts SC1 SC2 OSH. fin regs0 ret R1 R2 Hret ZM ZR ZE.
    unfold zlen. change (Z.of_nat (length [v mod B; (v / B) mod B; v / B / B])) with 3. unfold B in *.
    split; [cellN_go|split; [cellN_go|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|[|]]]; [| | |lia]; cbn [nth]; zwidth.
    + rewrite Z.mul_0_r, Z.add_0_r. cellN_go.
    + replace (o + 4 + 4 * 1) with (o + 8) by lia. cellN_go.
    + replace (o + 4 + 4 * 2) with (o + 12) by lia. cellN_go.
Qed.

End S.
