(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison BrtAllocG BrtUnwind BrtFree1 BrtFree2 BrtFp.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_5fed4_60754 Bo0_code_67fdc_6814c Bo0_code_3d2b4_3e23c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_fx_null_mem (M : word -> option byte) (S t f22 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x6008c : bv 64)%bv)) (S - 2144) S) (S - 2152) 0) (S - 2160) (U (0x6001c : bv 64)%bv)) (S - 2168) 1)
     (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22.

Section FPX. Context {fx : PropExec.FPState}.
Lemma art_fx_null_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S t f22 f23 f24 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> ret_ok raw0 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> hid (t + 4096 <= 0x10000 \/ 0x634000 <= t) ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x60078 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 0 -> cellA M (S - 2160) 8 (U (0x6001c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  exists regs', msteps ASEGS (mkst regs (0x68118 : word) M rom) (mkst regs' raw0 (art_fx_null_mem M S t f22) rom)
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
    zsb F_68118 D_68118 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (D36 : cellA X (S - 2136) 8 0x60078) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 0) by zcell;
      assert (D60 : cellA X (S - 2160) 8 (U (0x6001c : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
      assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
      assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
    zld F_6811c D_6811c (S - 2136) D36. zld F_68120 D_68120 (S - 2144) D44. zld F_68124 D_68124 (S - 2152) D52. zld F_68128 D_68128 (S - 2160) D60.
    zld F_6812c D_6812c (S - 2168) D68. zld F_68130 D_68130 (S - 2176) D76. zld F_68134 D_68134 (S - 2184) D84. zld F_68138 D_68138 (S - 2192) D92.
    zld F_6813c D_6813c (S - 2200) D00. zld F_68140 D_68140 (S - 2208) D08.
    zstep F_68144 D_68144.
    stepjr F_68148 D_68148 (0x60078 : bv 64)%bv ltac:(gres; bveq).
    (* [comment removed for export] *)
    zstep F_60078 D_60078. zstep F_6007c D_6007c. zstep F_60080 D_60080. zstep F_60084 D_60084.
    stepn F_60088 D_60088.
    zstep F_3d2b4 D_3d2b4. zstep F_3d2b8 D_3d2b8. zstep F_3d2bc D_3d2bc. zstep F_3d2c0 D_3d2c0. zstep F_3d2c4 D_3d2c4. zstep F_3d2c8 D_3d2c8.
    zstep F_3d2cc D_3d2cc. zstep F_3d2d0 D_3d2d0. zstep F_3d2d4 D_3d2d4.
    stepn F_3d2d8 D_3d2d8.
    (* [comment removed for export] *)
    zstep F_3d2dc D_3d2dc.
    zsd F_3d2e0 D_3d2e0 (S - 2136) (U (0x6008c : bv 64)%bv) ltac:(rewok W). zsd F_3d2e4 D_3d2e4 (S - 2144) S ltac:(rewok W). zsd F_3d2e8 D_3d2e8 (S - 2152) 0 ltac:(rewok W).
    zsd F_3d2ec D_3d2ec (S - 2160) (U (0x6001c : bv 64)%bv) ltac:(rewok W). zsd F_3d2f0 D_3d2f0 (S - 2168) 1 ltac:(rewok W). zsd F_3d2f4 D_3d2f4 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_3d2f8 D_3d2f8 (S - 2184) (S - 81) ltac:(rewok W). zsd F_3d2fc D_3d2fc (S - 2192) f22 ltac:(rewok W).
    zbtk F_3d300 D_3d300.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (E36 : cellA X (S - 2136) 8 (U (0x6008c : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell; assert (E52 : cellA X (S - 2152) 8 0) by zcell;
      assert (E60 : cellA X (S - 2160) 8 (U (0x6001c : bv 64)%bv)) by zcell; assert (E68 : cellA X (S - 2168) 8 1) by zcell;
      assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell;
      assert (G8 : cellA X (S - 8) 8 (U raw0)) by zcell; assert (G16 : cellA X (S - 16) 8 g16) by zcell; assert (G24 : cellA X (S - 24) 8 g24) by zcell;
      assert (G32 : cellA X (S - 32) 8 g32) by zcell; assert (G40 : cellA X (S - 40) 8 g40) by zcell; assert (G48 : cellA X (S - 48) 8 g48) by zcell; assert (G56 : cellA X (S - 56) 8 g56) by zcell end.
    zld F_3d33c D_3d33c (S - 2136) E36. zld F_3d340 D_3d340 (S - 2144) E44. zld F_3d344 D_3d344 (S - 2152) E52. zld F_3d348 D_3d348 (S - 2160) E60.
    zld F_3d34c D_3d34c (S - 2168) E68. zld F_3d350 D_3d350 (S - 2176) E76. zld F_3d354 D_3d354 (S - 2184) E84. zld F_3d358 D_3d358 (S - 2192) E92.
    zstep F_3d35c D_3d35c.
    stepjr F_3d360 D_3d360 (0x6008c : bv 64)%bv ltac:(gres; bveq).
    zstep F_6008c D_6008c.
    zld F_60090 D_60090 (S - 8) G8. rewrite Z_to_bv_bv_unsigned.
    zld F_60094 D_60094 (S - 16) G16. zld F_60098 D_60098 (S - 24) G24. zld F_6009c D_6009c (S - 32) G32.
    zld F_600a0 D_600a0 (S - 40) G40. zld F_600a4 D_600a4 (S - 48) G48. zld F_600a8 D_600a8 (S - 56) G56.
    zstep F_600ac D_600ac.
    stepret F_600b0 D_600b0 raw0 ltac:(rwH; reflexivity).
    unfold art_fx_null_mem. rnorm. apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | zval | zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. repeat (split; [gres; reflexivity|]).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; gres; reflexivity.
Qed.
End FPX.
