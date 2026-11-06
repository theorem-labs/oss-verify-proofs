(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtDepotA ArtSecAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_71b40_71b78 As0_code_6da44_6daac
     As0_code_7386c_739fc As0_code_73f0c_74118 As0_code_7bab0_7bbfc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)
Definition art_mmapfixed_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 96) 50)
    (s - 104) 0x73908) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x16d5e0) (s - 152) (U (getr rg 21)).

Lemma art_mmapfixed_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size tol name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 tol -> getr regs 13 = Z_to_bv 64 name ->
  0x633000 <= s - 368 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 <= tol < 2 ^ 64 -> 0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x633000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 368) 368 ->
  cellA M 0xd5898 8 0x16d5e0 -> cellA M 0x16d5e0 8 4096 -> cellA M 0xd58a8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x73878 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x73924)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 tol)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x16d5e0)) 21 (getr regs 21))
          (0x71b64 : word) (art_mmapfixed_mem M s raw regs addr size tol name) rom).
Proof.
  intros regs M rom raw s addr size tol name F fb H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_mmapfixed_mem.
  zstep F_73878 D_73878.                                                         (* [comment removed for export] *)
  zsd F_7387c D_7387c (s - 8) (U raw) ltac:(rewok W).
  zsd F_73880 D_73880 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_73884 D_73884 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_73888 D_73888 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_7388c D_7388c (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_73890 D_73890 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_73894 D_73894. zstep F_73898 D_73898. zstep F_7389c D_7389c.           (* [comment removed for export] *)
  zstep F_738a0 D_738a0.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0xd5898 8 0x16d5e0) by zcell; assert (Cpc' : cellA X 0x16d5e0 8 4096) by zcell end.
  zld F_738a4 D_738a4 0xd5898 Cg28'. zld F_738a8 D_738a8 0x16d5e0 Cpc'.
  zstep F_738ac D_738ac.                                                         (* [comment removed for export] *)
  zbtk F_738b0 D_738b0.                                                          (* [comment removed for export] *)
  zstep F_738c0 D_738c0. zstep F_738c4 D_738c4.                                  (* [comment removed for export] *)
  zbft F_738c8 D_738c8.
  zstep F_738cc D_738cc. zstep F_738d0 D_738d0. zstep F_738d4 D_738d4.           (* [comment removed for export] *)
  pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
  stepn F_738d8 D_738d8. rwH.                                                    (* [comment removed for export] *)
  replace (size + 4096 + -1) with (size + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite RU. replace (size + 4095 - 4095) with size by lia.
  zbtk F_738dc D_738dc.                                                          (* [comment removed for export] *)
  stepn F_738ec D_738ec. rwH. rewrite art_zb_and by lia.                         (* [comment removed for export] *)
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite Hal, Z.sub_0_r.
  zstep F_738f0 D_738f0.                                                         (* [comment removed for export] *)
  zsw F_738f4 D_738f4 (s - 96) 50 ltac:(rewok W).                                  (* [comment removed for export] *)
  zstep F_738f8 D_738f8. zstep F_738fc D_738fc. zstep F_73900 D_73900.           (* [comment removed for export] *)
  stepn F_73904 D_73904.                                                         (* [comment removed for export] *)
  zstep F_73f0c D_73f0c.                                                         (* [comment removed for export] *)
  zsd F_73f10 D_73f10 (s - 104) 0x73908 ltac:(rewok W).
  zsd F_73f14 D_73f14 (s - 112) size ltac:(rewok W).
  zsd F_73f18 D_73f18 (s - 120) tol ltac:(rewok W).
  zsd F_73f1c D_73f1c (s - 128) addr ltac:(rewok W).
  zsd F_73f20 D_73f20 (s - 136) name ltac:(rewok W).
  zsd F_73f24 D_73f24 (s - 144) 0x16d5e0 ltac:(rewok W).
  zsd F_73f28 D_73f28 (s - 152) (U (getr regs 21)) ltac:(rewok W).
  zstep F_73f2c D_73f2c.                                                         (* [comment removed for export] *)
  zstep F_73f30 D_73f30.                                                         (* [comment removed for export] *)
  zbft F_73f34 D_73f34.                                                          (* [comment removed for export] *)
  zstep F_73f38 D_73f38.                                                         (* [comment removed for export] *)
  stepn F_73f3c D_73f3c.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0xd58a8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_73f40 D_73f40 0xd58a8 C38c.                                              (* [comment removed for export] *)
  zlbu F_73f44 D_73f44 (F + 260) Cflc.                                           (* [comment removed for export] *)
  stepn F_73f48 D_73f48. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.          (* [comment removed for export] *)
  zbtk F_73f4c D_73f4c.                                                          (* [comment removed for export] *)
  stepn F_7405c D_7405c.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x73908) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
    assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
    assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x16d5e0) by zcell;
    assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
  zld F_74060 D_74060 (s - 104) R1. zld F_74064 D_74064 (s - 112) R2. zld F_74068 D_74068 (s - 120) R3. zld F_7406c D_7406c (s - 128) R4.
  zld F_74070 D_74070 (s - 136) R5. zld F_74074 D_74074 (s - 144) R6. zld F_74078 D_74078 (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
  zstep F_7407c D_7407c.                                                         (* [comment removed for export] *)
  stepret F_74080 D_74080 (Z_to_bv 64 0x73908 : word) ltac:(rwH; reflexivity).
  zlw F_73908 D_73908 (s - 96) R8.                                               (* [comment removed for export] *)
  zstep F_7390c D_7390c. zstep F_73910 D_73910. zstep F_73914 D_73914. zstep F_73918 D_73918. zstep F_7391c D_7391c.   (* [comment removed for export] *)
  stepn F_73920 D_73920.                                                         (* [comment removed for export] *)
  zstep F_71b60 D_71b60.                                                         (* [comment removed for export] *)
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_mmapfixed_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x633000 <= s - 368 -> s < 2 ^ 47 ->
  forall x : word, ~ (s - 368 <= U x < s) -> art_mmapfixed_mem M s raw rg addr size tol name x = M x.
Proof.
  intros M s raw rg addr size tol name Hs Hs' x Y. unfold art_mmapfixed_mem.
  do 14 (rewrite Wn_outside; [ | lia | cbn; lia | cbn; lia ]). reflexivity.
Qed.
Lemma art_mmapfixed_mem_grows : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  mem_grows M (art_mmapfixed_mem M s raw rg addr size tol name).
Proof.
  intros. unfold art_mmapfixed_mem. do 14 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
Lemma art_mmapfixed_mem_cells : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x633000 <= s - 368 -> s < 2 ^ 47 ->
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 8) 8 (U raw) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 40) 8 (U (getr rg 19)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 48) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size tol name Hs Hs'. unfold art_mmapfixed_mem. repeat split; zcell.
Qed.

(* [comment removed for export] *)
Definition art_rar_frame (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18)).
Definition art_rar_map_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (art_rar_frame M s raw rg)
    (s - 40) 0x7badc) (s - 48) size) (s - 56) addr) (s - 64) (U (getr rg 18))) (s - 72) (U (getr rg 19))) (s - 80) (U (getr rg 20)))
    (s - 128) 50)
    (s - 136) 0x73908) (s - 144) size) (s - 152) 1) (s - 160) addr) (s - 168) name) (s - 176) 0x16d5e0) (s - 184) (U (getr rg 21)).

Lemma art_rar_map_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 addr -> getr regs 12 = Z_to_bv 64 size -> getr regs 13 = Z_to_bv 64 name ->
  0x633000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x633000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 400) 400 ->
  cellA M 0xd5898 8 0x16d5e0 -> cellA M 0x16d5e0 8 4096 -> cellA M 0xd58a8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x7bab0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x73924)) 2 (Z_to_bv 64 (s - 128))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x16d5e0)) 21 (getr regs 21))
          (0x71b64 : word) (art_rar_map_mem M s raw regs addr size name) rom).
Proof.
  intros regs M rom raw s addr size name F fb H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_rar_map_mem, art_rar_frame.           (* [comment removed for export] *)
  zstep F_7bab0 D_7bab0.                                                         (* [comment removed for export] *)
  zsd F_7bab4 D_7bab4 (s - 8) (U raw) ltac:(rewok W).
  zsd F_7bab8 D_7bab8 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7babc D_7babc (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7bac0 D_7bac0 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_7bac4 D_7bac4. zstep F_7bac8 D_7bac8.
  zstep F_7bacc D_7bacc. zstep F_7bad0 D_7bad0. zstep F_7bad4 D_7bad4.
  stepn F_7bad8 D_7bad8.
  zstep F_739f0 D_739f0. zstep F_739f4 D_739f4.                                  (* [comment removed for export] *)
  stepn F_739f8 D_739f8.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cg28' : cellA X 0xd5898 8 0x16d5e0) by zcell; assert (Cpc' : cellA X 0x16d5e0 8 4096) by zcell;
    assert (Cg38' : cellA X 0xd58a8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell;
    assert (W' : wrA X (s - 32 - 368) 368) by zwr end.
  zcall (art_mmapfixed_pre_fn _ _ rom (Z_to_bv 64 0x7badc) (s - 32) addr size 1 name F fb).
  unfold art_mmapfixed_mem. gres.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_rar_map_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x633000 <= s - 400 -> s < 2 ^ 47 ->
  forall x : word, ~ (s - 400 <= U x < s) -> art_rar_map_mem M s raw rg addr size name x = M x.
Proof.
  intros M s raw rg addr size name Hs Hs' x Y. unfold art_rar_map_mem, art_rar_frame.
  do 18 (rewrite Wn_outside; [ | lia | cbn; lia | cbn; lia ]). reflexivity.
Qed.
Lemma art_rar_map_mem_grows : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  mem_grows M (art_rar_map_mem M s raw rg addr size name).
Proof.
  intros. unfold art_rar_map_mem, art_rar_frame. do 18 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
Lemma art_rar_map_mem_cells : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x633000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> 0 <= size < 2 ^ 47 ->
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 40) 8 0x7badc /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 48) 8 size /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 56) 8 addr /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 64) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 72) 8 (U (getr rg 19)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 80) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size name Hs Hs' Ha Hsz. unfold art_rar_map_mem, art_rar_frame. repeat split; zcell.
Qed.

Lemma art_rar_map_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 y8 y9 y18 : word) (s size q F : Z),
  getr regs 1 = Z_to_bv 64 0x73924 -> getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x633000 <= s - 400 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 < q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x633000 ->
  wrA M (s - 400) 400 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) ->
  cellA M (s - 40) 8 0x7badc -> cellA M (s - 48) 8 (U y8) -> cellA M (s - 56) 8 (U y9) -> cellA M (s - 64) 8 (U y18) -> cellA M (s - 72) 8 (U x19) -> cellA M (s - 80) 8 (U x20) ->
  cellA M 0xd58a8 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x71b68 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 84) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 y8 y9 y18 s size q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 C38 C144.
  stepret F_71b68 D_71b68 (Z_to_bv 64 0x73924 : word) ltac:(rwH; reflexivity).        (* [comment removed for export] *)
  zstep F_73924 D_73924.                                                         (* [comment removed for export] *)
  zstep F_73928 D_73928.                                                         (* [comment removed for export] *)
  stepn F_7392c D_7392c.                                                         (* [comment removed for export] *)
  zstep F_71b40 D_71b40. zstep F_71b44 D_71b44.
  zbtk F_71b48 D_71b48.
  zstep F_71b58 D_71b58.
  stepret F_71b5c D_71b5c (Z_to_bv 64 0x73930 : word) ltac:(rwH; reflexivity).
  zstep F_73930 D_73930. zstep F_73934 D_73934.                                  (* [comment removed for export] *)
  zsw F_73938 D_73938 (s - 84) 18446744072277895850 ltac:(rewok W).              (* [comment removed for export] *)
  zstep F_7393c D_7393c. zstep F_73940 D_73940.                                  (* [comment removed for export] *)
  stepn F_73944 D_73944.                                                         (* [comment removed for export] *)
  zstep F_71b40 D_71b40. zstep F_71b44 D_71b44.
  zbtk F_71b48 D_71b48.
  zstep F_71b58 D_71b58.
  stepret F_71b5c D_71b5c (Z_to_bv 64 0x73948 : word) ltac:(rwH; reflexivity).
  zbft F_73948 D_73948.                                                          (* [comment removed for export] *)
  zstep F_7394c D_7394c.                                                         (* [comment removed for export] *)
  stepn F_73950 D_73950.                                                         (* [comment removed for export] *)
  zstep F_6da44 D_6da44.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0xd58a8 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_6da48 D_6da48 0xd58a8 C38'. zld F_6da4c D_6da4c (F + 144) C144'.
  zbtk F_6da50 D_6da50.
  stepret F_6da6c D_6da6c (Z_to_bv 64 0x73954 : word) ltac:(rwH; reflexivity).
  zstep F_73954 D_73954.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 40) 8 0x7badc) by zcell; assert (R2 : cellA X (s - 48) 8 (U y8)) by zcell; assert (R3 : cellA X (s - 56) 8 (U y9)) by zcell;
    assert (R4 : cellA X (s - 64) 8 (U y18)) by zcell; assert (R5 : cellA X (s - 72) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 80) 8 (U x20)) by zcell;
    assert (Q1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (Q2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (Q3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (Q4 : cellA X (s - 32) 8 (U x18)) by zcell end.
  zld F_73958 D_73958 (s - 40) R1.
  zld F_7395c D_7395c (s - 48) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_73960 D_73960 (s - 56) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_73964 D_73964 (s - 64) R4; rewrite Z_to_bv_bv_unsigned.
  zld F_73968 D_73968 (s - 72) R5; rewrite Z_to_bv_bv_unsigned.
  zld F_7396c D_7396c (s - 80) R6; rewrite Z_to_bv_bv_unsigned.
  zstep F_73970 D_73970.                                                         (* [comment removed for export] *)
  stepret F_73974 D_73974 (Z_to_bv 64 0x7badc : word) ltac:(rwH; reflexivity).
  zbft F_7badc D_7badc.
  zld F_7bae0 D_7bae0 (s - 8) Q1; rewrite Z_to_bv_bv_unsigned.
  zld F_7bae4 D_7bae4 (s - 16) Q2; rewrite Z_to_bv_bv_unsigned.
  zld F_7bae8 D_7bae8 (s - 24) Q3; rewrite Z_to_bv_bv_unsigned.
  zld F_7baec D_7baec (s - 32) Q4; rewrite Z_to_bv_bv_unsigned.
  zstep F_7baf0 D_7baf0.
  stepret F_7baf4 D_7baf4 x1 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
