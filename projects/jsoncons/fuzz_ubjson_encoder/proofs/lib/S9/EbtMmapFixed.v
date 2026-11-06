(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac EbtDepotA EbtSecAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r719b0_719e8 Eb0_code_r6d8b4_6d91c
     Eb0_code_r7b920_7b940 Eb0_code_r736dc_7386c Eb0_code_r73d7c_73f88 Eb0_code_r95a8c_95b00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma mf_roundup_id : forall x, 0 <= x -> x mod 4096 = 0 -> (x + 4095) mod 4096 = 4095.
Proof.
  intros x Hx Hm. pose proof (Z.div_mod x 4096 ltac:(lia)) as E. rewrite Hm in E.
  symmetry. apply (Z.mod_unique_pos (x + 4095) 4096 (x / 4096) 4095); lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Definition art_mmapfixed_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 96) 50)
    (s - 104) 0x8ebd0) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x1d5ba0) (s - 152) (U (getr rg 21)).

#[using="Type"] Lemma art_mmapfixed_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size tol name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 tol -> getr regs 13 = Z_to_bv 64 name ->
  0x69c000 <= s - 368 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 <= tol < 2 ^ 64 -> 0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x69c000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 368) 368 ->
  cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 -> cellA M 0x13d8b8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x8eb40 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8ebec)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 tol)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1d5ba0)) 21 (getr regs 21))
          (0x8ce2c : word) (art_mmapfixed_mem M s raw regs addr size tol name) rom).
Proof.
  intros regs M rom raw s addr size tol name F fb H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_mmapfixed_mem.
  zstep F_8eaf0 D_8eaf0.
  zsd F_8eaf4 D_8eaf4 (s - 8) (U raw) ltac:(rewok W).
  zsd F_8eaf8 D_8eaf8 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_8eafc D_8eafc (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_8eb00 D_8eb00 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_8eb04 D_8eb04 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_8eb08 D_8eb08 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_8eb0c D_8eb0c. zstep F_8eb10 D_8eb10. zstep F_8eb14 D_8eb14.
  zstep F_8eb18 D_8eb18.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0x13d8a8 8 0x1d5ba0) by zcell; assert (Cpc' : cellA X 0x1d5ba0 8 4096) by zcell end.
  zld F_8eb1c D_8eb1c 0x13d8a8 Cg28'. zld F_8eb20 D_8eb20 0x1d5ba0 Cpc'.
  zstep F_8eb24 D_8eb24.
  zbtk F_8eb28 D_8eb28.
  zstep F_8eb38 D_8eb38. zstep F_8eb3c D_8eb3c.
  zbft F_8eb40 D_8eb40.
  zstep F_8eb44 D_8eb44. zstep F_8eb48 D_8eb48. zstep F_8eb4c D_8eb4c.
  pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
  stepn F_8eb50 D_8eb50. rwH.
  replace (size + 4096 + -1) with (size + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite RU. replace (size + 4095 - 4095) with size by lia.
  zbtk F_8eb54 D_8eb54.
  stepn F_8eb64 D_8eb64. rwH. rewrite art_zb_and by lia.
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite Hal, Z.sub_0_r.
  zstep F_8eb68 D_8eb68.
  zsw F_8eb6c D_8eb6c (s - 96) 50 ltac:(rewok W).
  zstep F_8eb70 D_8eb70. zstep F_8eb74 D_8eb74. zstep F_8eb78 D_8eb78.
  stepn F_8eb7c D_8eb7c.
  zstep F_8f184 D_8f184.
  zsd F_8f188 D_8f188 (s - 104) 0x8ebd0 ltac:(rewok W).
  zsd F_8f18c D_8f18c (s - 112) size ltac:(rewok W).
  zsd F_8f190 D_8f190 (s - 120) tol ltac:(rewok W).
  zsd F_8f194 D_8f194 (s - 128) addr ltac:(rewok W).
  zsd F_8f198 D_8f198 (s - 136) name ltac:(rewok W).
  zsd F_8f19c D_8f19c (s - 144) 0x1d5ba0 ltac:(rewok W).
  zsd F_8f1a0 D_8f1a0 (s - 152) (U (getr regs 21)) ltac:(rewok W).
  zstep F_8f1a4 D_8f1a4.
  zstep F_8f1a8 D_8f1a8.
  zbft F_8f1ac D_8f1ac.
  zstep F_8f1b0 D_8f1b0.
  stepn F_8f1b4 D_8f1b4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x13d8b8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_8f1b8 D_8f1b8 0x13d8b8 C38c.
  zlbu F_8f1bc D_8f1bc (F + 260) Cflc.
  stepn F_8f1c0 D_8f1c0. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_8f1c4 D_8f1c4.
  stepn F_8f2d4 D_8f2d4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x8ebd0) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
    assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
    assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x1d5ba0) by zcell;
    assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
  zld F_8f2d8 D_8f2d8 (s - 104) R1. zld F_8f2dc D_8f2dc (s - 112) R2. zld F_8f2e0 D_8f2e0 (s - 120) R3. zld F_8f2e4 D_8f2e4 (s - 128) R4.
  zld F_8f2e8 D_8f2e8 (s - 136) R5. zld F_8f2ec D_8f2ec (s - 144) R6. zld F_8f2f0 D_8f2f0 (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
  zstep F_8f2f4 D_8f2f4.
  stepret F_8f2f8 D_8f2f8 (Z_to_bv 64 0x8ebd0 : word) ltac:(rwH; reflexivity).
  zlw F_8eb80 D_8eb80 (s - 96) R8.
  zstep F_8eb84 D_8eb84. zstep F_8eb88 D_8eb88. zstep F_8eb8c D_8eb8c. zstep F_8eb90 D_8eb90. zstep F_8eb94 D_8eb94.
  stepn F_8eb98 D_8eb98.
  zstep F_8cdd8 D_8cdd8.
  zret.
Qed.

#[using="Type"] Lemma art_mmapfixed_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x69c000 <= s - 368 -> s < 2 ^ 47 ->
  forall x : word, ~ (s - 368 <= U x < s) -> art_mmapfixed_mem M s raw rg addr size tol name x = M x.
Proof.
  intros M s raw rg addr size tol name Hs Hs' x Y. unfold art_mmapfixed_mem.
  do 14 (rewrite Wn_outside; [ | lia | cbn; lia | cbn; lia ]). reflexivity.
Qed.
#[using="Type"] Lemma art_mmapfixed_mem_grows : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  mem_grows M (art_mmapfixed_mem M s raw rg addr size tol name).
Proof.
  intros. unfold art_mmapfixed_mem. do 14 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
#[using="Type"] Lemma art_mmapfixed_mem_cells : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x69c000 <= s - 368 -> s < 2 ^ 47 ->
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 8) 8 (U raw) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 40) 8 (U (getr rg 19)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 48) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size tol name Hs Hs'. unfold art_mmapfixed_mem. repeat split; zcell.
Qed.

Definition art_rar_frame (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18)).

Definition art_rar_map_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (art_rar_frame M s raw rg)
    (s - 40) 0x96da4) (s - 48) size) (s - 56) addr) (s - 64) (U (getr rg 18))) (s - 72) (U (getr rg 19))) (s - 80) (U (getr rg 20)))
    (s - 128) 50)
    (s - 136) 0x8ebd0) (s - 144) size) (s - 152) 1) (s - 160) addr) (s - 168) name) (s - 176) 0x1d5ba0) (s - 184) (U (getr rg 21)).

#[using="Type"] Lemma art_rar_map_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 addr -> getr regs 12 = Z_to_bv 64 size -> getr regs 13 = Z_to_bv 64 name ->
  0x69c000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x69c000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 400) 400 ->
  cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 -> cellA M 0x13d8b8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x96d78 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8ebec)) 2 (Z_to_bv 64 (s - 128))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1d5ba0)) 21 (getr regs 21))
          (0x8ce2c : word) (art_rar_map_mem M s raw regs addr size name) rom).
Proof.
  intros regs M rom raw s addr size name F fb H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_rar_map_mem, art_rar_frame.
  zstep F_96d28 D_96d28.
  zsd F_96d2c D_96d2c (s - 8) (U raw) ltac:(rewok W).
  zsd F_96d30 D_96d30 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_96d34 D_96d34 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_96d38 D_96d38 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_96d3c D_96d3c. zstep F_96d40 D_96d40.
  zstep F_96d44 D_96d44. zstep F_96d48 D_96d48. zstep F_96d4c D_96d4c.
  stepn F_96d50 D_96d50.
  zstep F_8ec68 D_8ec68. zstep F_8ec6c D_8ec6c.
  stepn F_8ec70 D_8ec70.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cg28' : cellA X 0x13d8a8 8 0x1d5ba0) by zcell; assert (Cpc' : cellA X 0x1d5ba0 8 4096) by zcell;
    assert (Cg38' : cellA X 0x13d8b8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell;
    assert (W' : wrA X (s - 32 - 368) 368) by zwr end.
  zcall (art_mmapfixed_pre_fn _ _ rom (Z_to_bv 64 0x96da4) (s - 32) addr size 1 name F fb).
  unfold art_mmapfixed_mem. gres.
  zret.
Qed.

#[using="Type"] Lemma art_rar_map_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x69c000 <= s - 400 -> s < 2 ^ 47 ->
  forall x : word, ~ (s - 400 <= U x < s) -> art_rar_map_mem M s raw rg addr size name x = M x.
Proof.
  intros M s raw rg addr size name Hs Hs' x Y. unfold art_rar_map_mem, art_rar_frame.
  do 18 (rewrite Wn_outside; [ | lia | cbn; lia | cbn; lia ]). reflexivity.
Qed.
#[using="Type"] Lemma art_rar_map_mem_grows : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  mem_grows M (art_rar_map_mem M s raw rg addr size name).
Proof.
  intros. unfold art_rar_map_mem, art_rar_frame. do 18 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
#[using="Type"] Lemma art_rar_map_mem_cells : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x69c000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> 0 <= size < 2 ^ 47 ->
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 40) 8 0x96da4 /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 48) 8 size /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 56) 8 addr /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 64) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 72) 8 (U (getr rg 19)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 80) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size name Hs Hs' Ha Hsz. unfold art_rar_map_mem, art_rar_frame. repeat split; zcell.
Qed.

#[using="Type"] Lemma art_rar_map_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 y8 y9 y18 : word) (s size q F : Z),
  getr regs 1 = Z_to_bv 64 0x8ebec -> getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x69c000 <= s - 400 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 < q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x69c000 ->
  wrA M (s - 400) 400 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) ->
  cellA M (s - 40) 8 0x96da4 -> cellA M (s - 48) 8 (U y8) -> cellA M (s - 56) 8 (U y9) -> cellA M (s - 64) 8 (U y18) -> cellA M (s - 72) 8 (U x19) -> cellA M (s - 80) 8 (U x20) ->
  cellA M 0x13d8b8 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x8ce30 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 84) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 y8 y9 y18 s size q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 C38 C144.
  stepret F_8cde0 D_8cde0 (Z_to_bv 64 0x8ebec : word) ltac:(rwH; reflexivity).
  zstep F_8eb9c D_8eb9c.
  zstep F_8eba0 D_8eba0.
  stepn F_8eba4 D_8eba4.
  zstep F_8cdb8 D_8cdb8. zstep F_8cdbc D_8cdbc.
  zbtk F_8cdc0 D_8cdc0.
  zstep F_8cdd0 D_8cdd0.
  stepret F_8cdd4 D_8cdd4 (Z_to_bv 64 0x8ebf8 : word) ltac:(rwH; reflexivity).
  zstep F_8eba8 D_8eba8. zstep F_8ebac D_8ebac.
  zsw F_8ebb0 D_8ebb0 (s - 84) 18446744072277895850 ltac:(rewok W).
  zstep F_8ebb4 D_8ebb4. zstep F_8ebb8 D_8ebb8.
  stepn F_8ebbc D_8ebbc.
  zstep F_8cdb8 D_8cdb8. zstep F_8cdbc D_8cdbc.
  zbtk F_8cdc0 D_8cdc0.
  zstep F_8cdd0 D_8cdd0.
  stepret F_8cdd4 D_8cdd4 (Z_to_bv 64 0x8ec10 : word) ltac:(rwH; reflexivity).
  zbft F_8ebc0 D_8ebc0.
  zstep F_8ebc4 D_8ebc4.
  stepn F_8ebc8 D_8ebc8.
  zstep F_88ca0 D_88ca0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x13d8b8 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_88ca4 D_88ca4 0x13d8b8 C38'. zld F_88ca8 D_88ca8 (F + 144) C144'.
  zbtk F_88cac D_88cac.
  stepret F_88cc8 D_88cc8 (Z_to_bv 64 0x8ec1c : word) ltac:(rwH; reflexivity).
  zstep F_8ebcc D_8ebcc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 40) 8 0x96da4) by zcell; assert (R2 : cellA X (s - 48) 8 (U y8)) by zcell; assert (R3 : cellA X (s - 56) 8 (U y9)) by zcell;
    assert (R4 : cellA X (s - 64) 8 (U y18)) by zcell; assert (R5 : cellA X (s - 72) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 80) 8 (U x20)) by zcell;
    assert (Q1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (Q2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (Q3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (Q4 : cellA X (s - 32) 8 (U x18)) by zcell end.
  zld F_8ebd0 D_8ebd0 (s - 40) R1.
  zld F_8ebd4 D_8ebd4 (s - 48) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_8ebd8 D_8ebd8 (s - 56) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_8ebdc D_8ebdc (s - 64) R4; rewrite Z_to_bv_bv_unsigned.
  zld F_8ebe0 D_8ebe0 (s - 72) R5; rewrite Z_to_bv_bv_unsigned.
  zld F_8ebe4 D_8ebe4 (s - 80) R6; rewrite Z_to_bv_bv_unsigned.
  zstep F_8ebe8 D_8ebe8.
  stepret F_8ebec D_8ebec (Z_to_bv 64 0x96da4 : word) ltac:(rwH; reflexivity).
  zbft F_96d54 D_96d54.
  zld F_96d58 D_96d58 (s - 8) Q1; rewrite Z_to_bv_bv_unsigned.
  zld F_96d5c D_96d5c (s - 16) Q2; rewrite Z_to_bv_bv_unsigned.
  zld F_96d60 D_96d60 (s - 24) Q3; rewrite Z_to_bv_bv_unsigned.
  zld F_96d64 D_96d64 (s - 32) Q4; rewrite Z_to_bv_bv_unsigned.
  zstep F_96d68 D_96d68.
  stepret F_96d6c D_96d6c x1 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
