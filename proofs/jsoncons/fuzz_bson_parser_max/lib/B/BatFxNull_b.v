(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatAllocG_b BatUnwind_b BatFree1_b BatFp_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5fac4_60344_b Ba0_code_r67bcc_67d3c_b Ba0_code_r3cf10_3de98_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_fx_null_mem (M : word -> option byte) (S t f22 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x799cc : bv 64)%bv)) (S - 2144) S) (S - 2152) 0) (S - 2160) (U (0x7995c : bv 64)%bv)) (S - 2168) 1)
     (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22.

Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_fx_null_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S t f22 f23 f24 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> ret_ok raw0 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> hid (t + 4096 <= 0x10000 \/ 0x696000 <= t) ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x799b8 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 0 -> cellA M (S - 2160) 8 (U (0x7995c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  exists regs', msteps ASEGS (mkst regs (0x81f98 : word) M rom) (mkst regs' raw0 (art_fx_null_mem M S t f22) rom)
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
    zsb F_81b80 D_81b80 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (D36 : cellA X (S - 2136) 8 0x799b8) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 0) by zcell;
      assert (D60 : cellA X (S - 2160) 8 (U (0x7995c : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
      assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
      assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
    zld F_81b84 D_81b84 (S - 2136) D36. zld F_81b88 D_81b88 (S - 2144) D44. zld F_81b8c D_81b8c (S - 2152) D52. zld F_81b90 D_81b90 (S - 2160) D60.
    zld F_81b94 D_81b94 (S - 2168) D68. zld F_81b98 D_81b98 (S - 2176) D76. zld F_81b9c D_81b9c (S - 2184) D84. zld F_81ba0 D_81ba0 (S - 2192) D92.
    zld F_81ba4 D_81ba4 (S - 2200) D00. zld F_81ba8 D_81ba8 (S - 2208) D08.
    zstep F_81bac D_81bac.
    stepjr F_81bb0 D_81bb0 (0x799b8 : bv 64)%bv ltac:(gres; bveq).
    (* [comment removed for export] *)
    zstep F_795a0 D_795a0. zstep F_795a4 D_795a4. zstep F_795a8 D_795a8. zstep F_795ac D_795ac.
    stepn F_795b0 D_795b0.
    zstep F_51e90 D_51e90. zstep F_51e94 D_51e94. zstep F_51e98 D_51e98. zstep F_51e9c D_51e9c. zstep F_51ea0 D_51ea0. zstep F_51ea4 D_51ea4.
    zstep F_51ea8 D_51ea8. zstep F_51eac D_51eac. zstep F_51eb0 D_51eb0.
    stepn F_51eb4 D_51eb4.
    (* [comment removed for export] *)
    zstep F_51eb8 D_51eb8.
    zsd F_51ebc D_51ebc (S - 2136) (U (0x799cc : bv 64)%bv) ltac:(rewok W). zsd F_51ec0 D_51ec0 (S - 2144) S ltac:(rewok W). zsd F_51ec4 D_51ec4 (S - 2152) 0 ltac:(rewok W).
    zsd F_51ec8 D_51ec8 (S - 2160) (U (0x7995c : bv 64)%bv) ltac:(rewok W). zsd F_51ecc D_51ecc (S - 2168) 1 ltac:(rewok W). zsd F_51ed0 D_51ed0 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_51ed4 D_51ed4 (S - 2184) (S - 81) ltac:(rewok W). zsd F_51ed8 D_51ed8 (S - 2192) f22 ltac:(rewok W).
    zbtk F_51edc D_51edc.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (E36 : cellA X (S - 2136) 8 (U (0x799cc : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell; assert (E52 : cellA X (S - 2152) 8 0) by zcell;
      assert (E60 : cellA X (S - 2160) 8 (U (0x7995c : bv 64)%bv)) by zcell; assert (E68 : cellA X (S - 2168) 8 1) by zcell;
      assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell;
      assert (G8 : cellA X (S - 8) 8 (U raw0)) by zcell; assert (G16 : cellA X (S - 16) 8 g16) by zcell; assert (G24 : cellA X (S - 24) 8 g24) by zcell;
      assert (G32 : cellA X (S - 32) 8 g32) by zcell; assert (G40 : cellA X (S - 40) 8 g40) by zcell; assert (G48 : cellA X (S - 48) 8 g48) by zcell; assert (G56 : cellA X (S - 56) 8 g56) by zcell end.
    zld F_51f18 D_51f18 (S - 2136) E36. zld F_51f1c D_51f1c (S - 2144) E44. zld F_51f20 D_51f20 (S - 2152) E52. zld F_51f24 D_51f24 (S - 2160) E60.
    zld F_51f28 D_51f28 (S - 2168) E68. zld F_51f2c D_51f2c (S - 2176) E76. zld F_51f30 D_51f30 (S - 2184) E84. zld F_51f34 D_51f34 (S - 2192) E92.
    zstep F_51f38 D_51f38.
    stepjr F_51f3c D_51f3c (0x799cc : bv 64)%bv ltac:(gres; bveq).
    zstep F_795b4 D_795b4.
    zld F_795b8 D_795b8 (S - 8) G8. rewrite Z_to_bv_bv_unsigned.
    zld F_795bc D_795bc (S - 16) G16. zld F_795c0 D_795c0 (S - 24) G24. zld F_795c4 D_795c4 (S - 32) G32.
    zld F_795c8 D_795c8 (S - 40) G40. zld F_795cc D_795cc (S - 48) G48. zld F_795d0 D_795d0 (S - 56) G56.
    zstep F_795d4 D_795d4.
    stepret F_795d8 D_795d8 raw0 ltac:(rwH; reflexivity).
    unfold art_fx_null_mem. rnorm. apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | zval | zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. repeat (split; [gres; reflexivity|]).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; gres; reflexivity.
Qed.
End FPX.
