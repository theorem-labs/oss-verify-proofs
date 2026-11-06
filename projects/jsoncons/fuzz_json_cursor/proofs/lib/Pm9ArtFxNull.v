(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtPoison Pm9ArtAllocG Pm9ArtUnwind Pm9ArtFree1 Pm9ArtFree2 Pm9ArtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000 Pm9_code_80000_81000 Pm9_code_89000_8a000      .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_fx_null_mem (M : word -> option byte) (S t f22 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x80f6c : bv 64)%bv)) (S - 2144) S) (S - 2152) 0) (S - 2160) (U (0x80efc : bv 64)%bv)) (S - 2168) 1)
     (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22.

Section FPX. Context {fx : PropExec.FPState}.
Lemma art_fx_null_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S t f22 f23 f24 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> ret_ok raw0 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> hid (t + 4096 <= 0x10000 \/ 0x6b4000 <= t) ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x80f58 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 0 -> cellA M (S - 2160) 8 (U (0x80efc : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  exists regs', msteps ASEGS (mkst regs (0x89538 : word) M rom) (mkst regs' raw0 (art_fx_null_mem M S t f22) rom)
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
    zsb F_894f0 D_894f0 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (D36 : cellA X (S - 2136) 8 0x80f58) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 0) by zcell;
      assert (D60 : cellA X (S - 2160) 8 (U (0x80efc : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
      assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
      assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
    zld F_894f4 D_894f4 (S - 2136) D36. zld F_894f8 D_894f8 (S - 2144) D44. zld F_894fc D_894fc (S - 2152) D52. zld F_89500 D_89500 (S - 2160) D60.
    zld F_89504 D_89504 (S - 2168) D68. zld F_89508 D_89508 (S - 2176) D76. zld F_8950c D_8950c (S - 2184) D84. zld F_89510 D_89510 (S - 2192) D92.
    zld F_89514 D_89514 (S - 2200) D00. zld F_89518 D_89518 (S - 2208) D08.
    zstep F_8951c D_8951c.
    stepjr F_89520 D_89520 (0x80f58 : bv 64)%bv ltac:(gres; bveq).

    zstep F_80f10 D_80f10. zstep F_80f14 D_80f14. zstep F_80f18 D_80f18. zstep F_80f1c D_80f1c.
    stepn F_80f20 D_80f20.
    zstep F_59498 D_59498. zstep F_5949c D_5949c. zstep F_594a0 D_594a0. zstep F_594a4 D_594a4. zstep F_594a8 D_594a8. zstep F_594ac D_594ac.
    zstep F_594b0 D_594b0. zstep F_594b4 D_594b4. zstep F_594b8 D_594b8.
    stepn F_594bc D_594bc.

    zstep F_594c0 D_594c0.
    zsd F_594c4 D_594c4 (S - 2136) (U (0x80f6c : bv 64)%bv) ltac:(rewok W). zsd F_594c8 D_594c8 (S - 2144) S ltac:(rewok W). zsd F_594cc D_594cc (S - 2152) 0 ltac:(rewok W).
    zsd F_594d0 D_594d0 (S - 2160) (U (0x80efc : bv 64)%bv) ltac:(rewok W). zsd F_594d4 D_594d4 (S - 2168) 1 ltac:(rewok W). zsd F_594d8 D_594d8 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_594dc D_594dc (S - 2184) (S - 81) ltac:(rewok W). zsd F_594e0 D_594e0 (S - 2192) f22 ltac:(rewok W).
    zbtk F_594e4 D_594e4.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (E36 : cellA X (S - 2136) 8 (U (0x80f6c : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell; assert (E52 : cellA X (S - 2152) 8 0) by zcell;
      assert (E60 : cellA X (S - 2160) 8 (U (0x80efc : bv 64)%bv)) by zcell; assert (E68 : cellA X (S - 2168) 8 1) by zcell;
      assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell;
      assert (G8 : cellA X (S - 8) 8 (U raw0)) by zcell; assert (G16 : cellA X (S - 16) 8 g16) by zcell; assert (G24 : cellA X (S - 24) 8 g24) by zcell;
      assert (G32 : cellA X (S - 32) 8 g32) by zcell; assert (G40 : cellA X (S - 40) 8 g40) by zcell; assert (G48 : cellA X (S - 48) 8 g48) by zcell; assert (G56 : cellA X (S - 56) 8 g56) by zcell end.
    zld F_59520 D_59520 (S - 2136) E36. zld F_59524 D_59524 (S - 2144) E44. zld F_59528 D_59528 (S - 2152) E52. zld F_5952c D_5952c (S - 2160) E60.
    zld F_59530 D_59530 (S - 2168) E68. zld F_59534 D_59534 (S - 2176) E76. zld F_59538 D_59538 (S - 2184) E84. zld F_5953c D_5953c (S - 2192) E92.
    zstep F_59540 D_59540.
    stepjr F_59544 D_59544 (0x80f6c : bv 64)%bv ltac:(gres; bveq).
    zstep F_80f24 D_80f24.
    zld F_80f28 D_80f28 (S - 8) G8. rewrite Z_to_bv_bv_unsigned.
    zld F_80f2c D_80f2c (S - 16) G16. zld F_80f30 D_80f30 (S - 24) G24. zld F_80f34 D_80f34 (S - 32) G32.
    zld F_80f38 D_80f38 (S - 40) G40. zld F_80f3c D_80f3c (S - 48) G48. zld F_80f40 D_80f40 (S - 56) G56.
    zstep F_80f44 D_80f44.
    stepret F_80f48 D_80f48 raw0 ltac:(rwH; reflexivity).
    unfold art_fx_null_mem. rnorm. apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | zval | zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. repeat (split; [gres; reflexivity|]).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; gres; reflexivity.
Qed.
End FPX.
