(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac EatDepotA EatSecAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r719b0_719e8 Ea0_code_r6d8b4_6d91c
     Ea0_code_r7b920_7b940 Ea0_code_r736dc_7386c Ea0_code_r73d7c_73f88 Ea0_code_r956bc_95730.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
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
    (s - 104) 0x8e3a8) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x1d14a0) (s - 152) (U (getr rg 21)).

#[using="Type"] Lemma art_mmapfixed_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size tol name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 tol -> getr regs 13 = Z_to_bv 64 name ->
  0x698000 <= s - 368 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 <= tol < 2 ^ 64 -> 0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x698000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 368) 368 ->
  cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 -> cellA M 0x1391a8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x8e318 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8e3c4)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 tol)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1d14a0)) 21 (getr regs 21))
          (0x8c604 : word) (art_mmapfixed_mem M s raw regs addr size tol name) rom).
Proof.
  intros regs M rom raw s addr size tol name F fb H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_mmapfixed_mem.
  zstep F_8e2c8 D_8e2c8.
  zsd F_8e2cc D_8e2cc (s - 8) (U raw) ltac:(rewok W).
  zsd F_8e2d0 D_8e2d0 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_8e2d4 D_8e2d4 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_8e2d8 D_8e2d8 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_8e2dc D_8e2dc (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_8e2e0 D_8e2e0 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_8e2e4 D_8e2e4. zstep F_8e2e8 D_8e2e8. zstep F_8e2ec D_8e2ec.
  zstep F_8e2f0 D_8e2f0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0x139198 8 0x1d14a0) by zcell; assert (Cpc' : cellA X 0x1d14a0 8 4096) by zcell end.
  zld F_8e2f4 D_8e2f4 0x139198 Cg28'. zld F_8e2f8 D_8e2f8 0x1d14a0 Cpc'.
  zstep F_8e2fc D_8e2fc.
  zbtk F_8e300 D_8e300.
  zstep F_8e310 D_8e310. zstep F_8e314 D_8e314.
  zbft F_8e318 D_8e318.
  zstep F_8e31c D_8e31c. zstep F_8e320 D_8e320. zstep F_8e324 D_8e324.
  pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
  stepn F_8e328 D_8e328. rwH.
  replace (size + 4096 + -1) with (size + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite RU. replace (size + 4095 - 4095) with size by lia.
  zbtk F_8e32c D_8e32c.
  stepn F_8e33c D_8e33c. rwH. rewrite art_zb_and by lia.
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite Hal, Z.sub_0_r.
  zstep F_8e340 D_8e340.
  zsw F_8e344 D_8e344 (s - 96) 50 ltac:(rewok W).
  zstep F_8e348 D_8e348. zstep F_8e34c D_8e34c. zstep F_8e350 D_8e350.
  stepn F_8e354 D_8e354.
  zstep F_8e95c D_8e95c.
  zsd F_8e960 D_8e960 (s - 104) 0x8e3a8 ltac:(rewok W).
  zsd F_8e964 D_8e964 (s - 112) size ltac:(rewok W).
  zsd F_8e968 D_8e968 (s - 120) tol ltac:(rewok W).
  zsd F_8e96c D_8e96c (s - 128) addr ltac:(rewok W).
  zsd F_8e970 D_8e970 (s - 136) name ltac:(rewok W).
  zsd F_8e974 D_8e974 (s - 144) 0x1d14a0 ltac:(rewok W).
  zsd F_8e978 D_8e978 (s - 152) (U (getr regs 21)) ltac:(rewok W).
  zstep F_8e97c D_8e97c.
  zstep F_8e980 D_8e980.
  zbft F_8e984 D_8e984.
  zstep F_8e988 D_8e988.
  stepn F_8e98c D_8e98c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x1391a8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_8e990 D_8e990 0x1391a8 C38c.
  zlbu F_8e994 D_8e994 (F + 260) Cflc.
  stepn F_8e998 D_8e998. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_8e99c D_8e99c.
  stepn F_8eaac D_8eaac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x8e3a8) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
    assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
    assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x1d14a0) by zcell;
    assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
  zld F_8eab0 D_8eab0 (s - 104) R1. zld F_8eab4 D_8eab4 (s - 112) R2. zld F_8eab8 D_8eab8 (s - 120) R3. zld F_8eabc D_8eabc (s - 128) R4.
  zld F_8eac0 D_8eac0 (s - 136) R5. zld F_8eac4 D_8eac4 (s - 144) R6. zld F_8eac8 D_8eac8 (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
  zstep F_8eacc D_8eacc.
  stepret F_8ead0 D_8ead0 (Z_to_bv 64 0x8e3a8 : word) ltac:(rwH; reflexivity).
  zlw F_8e358 D_8e358 (s - 96) R8.
  zstep F_8e35c D_8e35c. zstep F_8e360 D_8e360. zstep F_8e364 D_8e364. zstep F_8e368 D_8e368. zstep F_8e36c D_8e36c.
  stepn F_8e370 D_8e370.
  zstep F_8c5b0 D_8c5b0.
  zret.
Qed.

#[using="Type"] Lemma art_mmapfixed_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x698000 <= s - 368 -> s < 2 ^ 47 ->
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
  0x698000 <= s - 368 -> s < 2 ^ 47 ->
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
    (s - 40) 0x9657c) (s - 48) size) (s - 56) addr) (s - 64) (U (getr rg 18))) (s - 72) (U (getr rg 19))) (s - 80) (U (getr rg 20)))
    (s - 128) 50)
    (s - 136) 0x8e3a8) (s - 144) size) (s - 152) 1) (s - 160) addr) (s - 168) name) (s - 176) 0x1d14a0) (s - 184) (U (getr rg 21)).

#[using="Type"] Lemma art_rar_map_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 addr -> getr regs 12 = Z_to_bv 64 size -> getr regs 13 = Z_to_bv 64 name ->
  0x698000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x698000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 400) 400 ->
  cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 -> cellA M 0x1391a8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x96550 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8e3c4)) 2 (Z_to_bv 64 (s - 128))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1d14a0)) 21 (getr regs 21))
          (0x8c604 : word) (art_rar_map_mem M s raw regs addr size name) rom).
Proof.
  intros regs M rom raw s addr size name F fb H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_rar_map_mem, art_rar_frame.
  zstep F_96500 D_96500.
  zsd F_96504 D_96504 (s - 8) (U raw) ltac:(rewok W).
  zsd F_96508 D_96508 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_9650c D_9650c (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_96510 D_96510 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_96514 D_96514. zstep F_96518 D_96518.
  zstep F_9651c D_9651c. zstep F_96520 D_96520. zstep F_96524 D_96524.
  stepn F_96528 D_96528.
  zstep F_8e440 D_8e440. zstep F_8e444 D_8e444.
  stepn F_8e448 D_8e448.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cg28' : cellA X 0x139198 8 0x1d14a0) by zcell; assert (Cpc' : cellA X 0x1d14a0 8 4096) by zcell;
    assert (Cg38' : cellA X 0x1391a8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell;
    assert (W' : wrA X (s - 32 - 368) 368) by zwr end.
  zcall (art_mmapfixed_pre_fn _ _ rom (Z_to_bv 64 0x9657c) (s - 32) addr size 1 name F fb).
  unfold art_mmapfixed_mem. gres.
  zret.
Qed.

#[using="Type"] Lemma art_rar_map_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x698000 <= s - 400 -> s < 2 ^ 47 ->
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
  0x698000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> 0 <= size < 2 ^ 47 ->
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 40) 8 0x9657c /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 48) 8 size /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 56) 8 addr /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 64) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 72) 8 (U (getr rg 19)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 80) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size name Hs Hs' Ha Hsz. unfold art_rar_map_mem, art_rar_frame. repeat split; zcell.
Qed.

#[using="Type"] Lemma art_rar_map_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 y8 y9 y18 : word) (s size q F : Z),
  getr regs 1 = Z_to_bv 64 0x8e3c4 -> getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x698000 <= s - 400 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 < q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x698000 ->
  wrA M (s - 400) 400 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) ->
  cellA M (s - 40) 8 0x9657c -> cellA M (s - 48) 8 (U y8) -> cellA M (s - 56) 8 (U y9) -> cellA M (s - 64) 8 (U y18) -> cellA M (s - 72) 8 (U x19) -> cellA M (s - 80) 8 (U x20) ->
  cellA M 0x1391a8 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x8c608 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 84) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 y8 y9 y18 s size q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 C38 C144.
  stepret F_8c5b8 D_8c5b8 (Z_to_bv 64 0x8e3c4 : word) ltac:(rwH; reflexivity).
  zstep F_8e374 D_8e374.
  zstep F_8e378 D_8e378.
  stepn F_8e37c D_8e37c.
  zstep F_8c590 D_8c590. zstep F_8c594 D_8c594.
  zbtk F_8c598 D_8c598.
  zstep F_8c5a8 D_8c5a8.
  stepret F_8c5ac D_8c5ac (Z_to_bv 64 0x8e3d0 : word) ltac:(rwH; reflexivity).
  zstep F_8e380 D_8e380. zstep F_8e384 D_8e384.
  zsw F_8e388 D_8e388 (s - 84) 18446744072277895850 ltac:(rewok W).
  zstep F_8e38c D_8e38c. zstep F_8e390 D_8e390.
  stepn F_8e394 D_8e394.
  zstep F_8c590 D_8c590. zstep F_8c594 D_8c594.
  zbtk F_8c598 D_8c598.
  zstep F_8c5a8 D_8c5a8.
  stepret F_8c5ac D_8c5ac (Z_to_bv 64 0x8e3e8 : word) ltac:(rwH; reflexivity).
  zbft F_8e398 D_8e398.
  zstep F_8e39c D_8e39c.
  stepn F_8e3a0 D_8e3a0.
  zstep F_88478 D_88478.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x1391a8 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_8847c D_8847c 0x1391a8 C38'. zld F_88480 D_88480 (F + 144) C144'.
  zbtk F_88484 D_88484.
  stepret F_884a0 D_884a0 (Z_to_bv 64 0x8e3f4 : word) ltac:(rwH; reflexivity).
  zstep F_8e3a4 D_8e3a4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 40) 8 0x9657c) by zcell; assert (R2 : cellA X (s - 48) 8 (U y8)) by zcell; assert (R3 : cellA X (s - 56) 8 (U y9)) by zcell;
    assert (R4 : cellA X (s - 64) 8 (U y18)) by zcell; assert (R5 : cellA X (s - 72) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 80) 8 (U x20)) by zcell;
    assert (Q1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (Q2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (Q3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (Q4 : cellA X (s - 32) 8 (U x18)) by zcell end.
  zld F_8e3a8 D_8e3a8 (s - 40) R1.
  zld F_8e3ac D_8e3ac (s - 48) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_8e3b0 D_8e3b0 (s - 56) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_8e3b4 D_8e3b4 (s - 64) R4; rewrite Z_to_bv_bv_unsigned.
  zld F_8e3b8 D_8e3b8 (s - 72) R5; rewrite Z_to_bv_bv_unsigned.
  zld F_8e3bc D_8e3bc (s - 80) R6; rewrite Z_to_bv_bv_unsigned.
  zstep F_8e3c0 D_8e3c0.
  stepret F_8e3c4 D_8e3c4 (Z_to_bv 64 0x9657c : word) ltac:(rwH; reflexivity).
  zbft F_9652c D_9652c.
  zld F_96530 D_96530 (s - 8) Q1; rewrite Z_to_bv_bv_unsigned.
  zld F_96534 D_96534 (s - 16) Q2; rewrite Z_to_bv_bv_unsigned.
  zld F_96538 D_96538 (s - 24) Q3; rewrite Z_to_bv_bv_unsigned.
  zld F_9653c D_9653c (s - 32) Q4; rewrite Z_to_bv_bv_unsigned.
  zstep F_96540 D_96540.
  stepret F_96544 D_96544 x1 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
