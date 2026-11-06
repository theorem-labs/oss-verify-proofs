(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatPoison EatAllocG EatUnwind EatFree1 EatFp.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r5fac4_60344 Ea0_code_r67bcc_67d3c Ea0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_fx_null_mem (M : word -> option byte) (S t f22 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x7a350 : bv 64)%bv)) (S - 2144) S) (S - 2152) 0) (S - 2160) (U (0x7a2e0 : bv 64)%bv)) (S - 2168) 1)
     (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22.

Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_fx_null_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S t f22 f23 f24 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> ret_ok raw0 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> hid (t + 4096 <= 0x10000 \/ 0x698000 <= t) ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x7a33c -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 0 -> cellA M (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  exists regs', msteps ASEGS (mkst regs (0x8291c : word) M rom) (mkst regs' raw0 (art_fx_null_mem M S t f22) rom)
    /\ getr regs' 1 = raw0 /\ getr regs' 2 = Z_to_bv 64 S
    /\ getr regs' 8 = Z_to_bv 64 g16 /\ getr regs' 9 = Z_to_bv 64 g24 /\ getr regs' 18 = Z_to_bv 64 g32 /\ getr regs' 19 = Z_to_bv 64 g40 /\ getr regs' 20 = Z_to_bv 64 g48
    /\ getr regs' 21 = Z_to_bv 64 g56 /\ getr regs' 22 = Z_to_bv 64 f22 /\ getr regs' 23 = Z_to_bv 64 f23 /\ getr regs' 24 = Z_to_bv 64 f24
    /\ (forall r : reg, In r [3; 4; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw0 S t f22 f23 f24 g16 g24 g32 g40 g48 g56 H2 H24 Hret HS HS' Ht Ht' Atsp Timg Hf22 Hf23 Hf24 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 W Wt
         C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 F8 F16 F24 F32 F40 F48 F56.
  pose proof Timg as Timg'; unfold hid in Timg'. unfold apart in Atsp.
  eexists. split.
  {
    zsb F_828cc D_828cc (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (D36 : cellA X (S - 2136) 8 0x7a33c) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 0) by zcell;
      assert (D60 : cellA X (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
      assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
      assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
    zld F_828d0 D_828d0 (S - 2136) D36. zld F_828d4 D_828d4 (S - 2144) D44. zld F_828d8 D_828d8 (S - 2152) D52. zld F_828dc D_828dc (S - 2160) D60.
    zld F_828e0 D_828e0 (S - 2168) D68. zld F_828e4 D_828e4 (S - 2176) D76. zld F_828e8 D_828e8 (S - 2184) D84. zld F_828ec D_828ec (S - 2192) D92.
    zld F_828f0 D_828f0 (S - 2200) D00. zld F_828f4 D_828f4 (S - 2208) D08.
    zstep F_828f8 D_828f8.
    stepjr F_828fc D_828fc (0x7a33c : bv 64)%bv ltac:(gres; bveq).

    zstep F_7a2ec D_7a2ec. zstep F_7a2f0 D_7a2f0. zstep F_7a2f4 D_7a2f4. zstep F_7a2f8 D_7a2f8.
    stepn F_7a2fc D_7a2fc.
    zstep F_52a40 D_52a40. zstep F_52a44 D_52a44. zstep F_52a48 D_52a48. zstep F_52a4c D_52a4c. zstep F_52a50 D_52a50. zstep F_52a54 D_52a54.
    zstep F_52a58 D_52a58. zstep F_52a5c D_52a5c. zstep F_52a60 D_52a60.
    stepn F_52a64 D_52a64.

    zstep F_52a68 D_52a68.
    zsd F_52a6c D_52a6c (S - 2136) (U (0x7a350 : bv 64)%bv) ltac:(rewok W). zsd F_52a70 D_52a70 (S - 2144) S ltac:(rewok W). zsd F_52a74 D_52a74 (S - 2152) 0 ltac:(rewok W).
    zsd F_52a78 D_52a78 (S - 2160) (U (0x7a2e0 : bv 64)%bv) ltac:(rewok W). zsd F_52a7c D_52a7c (S - 2168) 1 ltac:(rewok W). zsd F_52a80 D_52a80 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_52a84 D_52a84 (S - 2184) (S - 81) ltac:(rewok W). zsd F_52a88 D_52a88 (S - 2192) f22 ltac:(rewok W).
    zbtk F_52a8c D_52a8c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (E36 : cellA X (S - 2136) 8 (U (0x7a350 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell; assert (E52 : cellA X (S - 2152) 8 0) by zcell;
      assert (E60 : cellA X (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv)) by zcell; assert (E68 : cellA X (S - 2168) 8 1) by zcell;
      assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell;
      assert (G8 : cellA X (S - 8) 8 (U raw0)) by zcell; assert (G16 : cellA X (S - 16) 8 g16) by zcell; assert (G24 : cellA X (S - 24) 8 g24) by zcell;
      assert (G32 : cellA X (S - 32) 8 g32) by zcell; assert (G40 : cellA X (S - 40) 8 g40) by zcell; assert (G48 : cellA X (S - 48) 8 g48) by zcell; assert (G56 : cellA X (S - 56) 8 g56) by zcell end.
    zld F_52ac8 D_52ac8 (S - 2136) E36. zld F_52acc D_52acc (S - 2144) E44. zld F_52ad0 D_52ad0 (S - 2152) E52. zld F_52ad4 D_52ad4 (S - 2160) E60.
    zld F_52ad8 D_52ad8 (S - 2168) E68. zld F_52adc D_52adc (S - 2176) E76. zld F_52ae0 D_52ae0 (S - 2184) E84. zld F_52ae4 D_52ae4 (S - 2192) E92.
    zstep F_52ae8 D_52ae8.
    stepjr F_52aec D_52aec (0x7a350 : bv 64)%bv ltac:(gres; bveq).
    zstep F_7a300 D_7a300.
    zld F_7a304 D_7a304 (S - 8) G8. rewrite Z_to_bv_bv_unsigned.
    zld F_7a308 D_7a308 (S - 16) G16. zld F_7a30c D_7a30c (S - 24) G24. zld F_7a310 D_7a310 (S - 32) G32.
    zld F_7a314 D_7a314 (S - 40) G40. zld F_7a318 D_7a318 (S - 48) G48. zld F_7a31c D_7a31c (S - 56) G56.
    zstep F_7a320 D_7a320.
    stepret F_7a324 D_7a324 raw0 ltac:(rwH; reflexivity).
    unfold art_fx_null_mem. rnorm. apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | zval | zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. repeat (split; [gres; reflexivity|]).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; gres; reflexivity.
Qed.
End FPX.
