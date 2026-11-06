(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtPoison ArtAllocG ArtUnwind ArtFree1 ArtFree2 ArtFp.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_5fc54_604d4 As0_code_67d5c_67ecc As0_code_3d034_3dfbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_fx_null_mem (M : word -> option byte) (S t f22 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x5fe0c : bv 64)%bv)) (S - 2144) S) (S - 2152) 0) (S - 2160) (U (0x5fd9c : bv 64)%bv)) (S - 2168) 1)
     (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22.

Section FPX. Context {fx : PropExec.FPState}.
Lemma art_fx_null_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S t f22 f23 f24 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> ret_ok raw0 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> hid (t + 4096 <= 0x10000 \/ 0x633000 <= t) ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x5fdf8 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 0 -> cellA M (S - 2160) 8 (U (0x5fd9c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  exists regs', msteps ASEGS (mkst regs (0x67e98 : word) M rom) (mkst regs' raw0 (art_fx_null_mem M S t f22) rom)
    /\ getr regs' 1 = raw0 /\ getr regs' 2 = Z_to_bv 64 S
    /\ getr regs' 8 = Z_to_bv 64 g16 /\ getr regs' 9 = Z_to_bv 64 g24 /\ getr regs' 18 = Z_to_bv 64 g32 /\ getr regs' 19 = Z_to_bv 64 g40 /\ getr regs' 20 = Z_to_bv 64 g48
    /\ getr regs' 21 = Z_to_bv 64 g56 /\ getr regs' 22 = Z_to_bv 64 f22 /\ getr regs' 23 = Z_to_bv 64 f23 /\ getr regs' 24 = Z_to_bv 64 f24
    /\ (forall r : reg, In r [3; 4; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw0 S t f22 f23 f24 g16 g24 g32 g40 g48 g56 H2 H24 Hret HS HS' Ht Ht' Atsp Timg Hf22 Hf23 Hf24 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 W Wt
         C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 F8 F16 F24 F32 F40 F48 F56.
  pose proof Timg as Timg'; unfold hid in Timg'. unfold apart in Atsp.
  eexists. split.
  { (* [comment removed for export] *)
    zsb F_67e98 D_67e98 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (D36 : cellA X (S - 2136) 8 0x5fdf8) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 0) by zcell;
      assert (D60 : cellA X (S - 2160) 8 (U (0x5fd9c : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
      assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
      assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
    zld F_67e9c D_67e9c (S - 2136) D36. zld F_67ea0 D_67ea0 (S - 2144) D44. zld F_67ea4 D_67ea4 (S - 2152) D52. zld F_67ea8 D_67ea8 (S - 2160) D60.
    zld F_67eac D_67eac (S - 2168) D68. zld F_67eb0 D_67eb0 (S - 2176) D76. zld F_67eb4 D_67eb4 (S - 2184) D84. zld F_67eb8 D_67eb8 (S - 2192) D92.
    zld F_67ebc D_67ebc (S - 2200) D00. zld F_67ec0 D_67ec0 (S - 2208) D08.
    zstep F_67ec4 D_67ec4.
    stepjr F_67ec8 D_67ec8 (0x5fdf8 : bv 64)%bv ltac:(gres; bveq).
    (* [comment removed for export] *)
    zstep F_5fdf8 D_5fdf8. zstep F_5fdfc D_5fdfc. zstep F_5fe00 D_5fe00. zstep F_5fe04 D_5fe04.
    stepn F_5fe08 D_5fe08.
    zstep F_3d034 D_3d034. zstep F_3d038 D_3d038. zstep F_3d03c D_3d03c. zstep F_3d040 D_3d040. zstep F_3d044 D_3d044. zstep F_3d048 D_3d048.
    zstep F_3d04c D_3d04c. zstep F_3d050 D_3d050. zstep F_3d054 D_3d054.
    stepn F_3d058 D_3d058.
    (* [comment removed for export] *)
    zstep F_3d05c D_3d05c.
    zsd F_3d060 D_3d060 (S - 2136) (U (0x5fe0c : bv 64)%bv) ltac:(rewok W). zsd F_3d064 D_3d064 (S - 2144) S ltac:(rewok W). zsd F_3d068 D_3d068 (S - 2152) 0 ltac:(rewok W).
    zsd F_3d06c D_3d06c (S - 2160) (U (0x5fd9c : bv 64)%bv) ltac:(rewok W). zsd F_3d070 D_3d070 (S - 2168) 1 ltac:(rewok W). zsd F_3d074 D_3d074 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_3d078 D_3d078 (S - 2184) (S - 81) ltac:(rewok W). zsd F_3d07c D_3d07c (S - 2192) f22 ltac:(rewok W).
    zbtk F_3d080 D_3d080.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (E36 : cellA X (S - 2136) 8 (U (0x5fe0c : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell; assert (E52 : cellA X (S - 2152) 8 0) by zcell;
      assert (E60 : cellA X (S - 2160) 8 (U (0x5fd9c : bv 64)%bv)) by zcell; assert (E68 : cellA X (S - 2168) 8 1) by zcell;
      assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell;
      assert (G8 : cellA X (S - 8) 8 (U raw0)) by zcell; assert (G16 : cellA X (S - 16) 8 g16) by zcell; assert (G24 : cellA X (S - 24) 8 g24) by zcell;
      assert (G32 : cellA X (S - 32) 8 g32) by zcell; assert (G40 : cellA X (S - 40) 8 g40) by zcell; assert (G48 : cellA X (S - 48) 8 g48) by zcell; assert (G56 : cellA X (S - 56) 8 g56) by zcell end.
    zld F_3d0bc D_3d0bc (S - 2136) E36. zld F_3d0c0 D_3d0c0 (S - 2144) E44. zld F_3d0c4 D_3d0c4 (S - 2152) E52. zld F_3d0c8 D_3d0c8 (S - 2160) E60.
    zld F_3d0cc D_3d0cc (S - 2168) E68. zld F_3d0d0 D_3d0d0 (S - 2176) E76. zld F_3d0d4 D_3d0d4 (S - 2184) E84. zld F_3d0d8 D_3d0d8 (S - 2192) E92.
    zstep F_3d0dc D_3d0dc.
    stepjr F_3d0e0 D_3d0e0 (0x5fe0c : bv 64)%bv ltac:(gres; bveq).
    zstep F_5fe0c D_5fe0c.
    zld F_5fe10 D_5fe10 (S - 8) G8. rewrite Z_to_bv_bv_unsigned.
    zld F_5fe14 D_5fe14 (S - 16) G16. zld F_5fe18 D_5fe18 (S - 24) G24. zld F_5fe1c D_5fe1c (S - 32) G32.
    zld F_5fe20 D_5fe20 (S - 40) G40. zld F_5fe24 D_5fe24 (S - 48) G48. zld F_5fe28 D_5fe28 (S - 56) G56.
    zstep F_5fe2c D_5fe2c.
    stepret F_5fe30 D_5fe30 raw0 ltac:(rwH; reflexivity).
    unfold art_fx_null_mem. rnorm. apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | zval | zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. repeat (split; [gres; reflexivity|]).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; gres; reflexivity.
Qed.
End FPX.
