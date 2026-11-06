(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac Pm8ArtDepotA Pm8ArtSecAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_8e000_8f000 Pm8_code_92000_93000 Pm8_code_94000_95000 Pm8_code_95000_96000 Pm8_code_9c000_9d000
       .
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

Definition art_mmapfixed_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 96) 50)
    (s - 104) 0x94c04) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x1ec460) (s - 152) (U (getr rg 21)).

Lemma art_mmapfixed_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size tol name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 tol -> getr regs 13 = Z_to_bv 64 name ->
  0x6b3000 <= s - 336 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 <= tol < 2 ^ 64 -> 0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x6b3000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 336) 336 ->
  cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 -> cellA M 0x153128 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x94b74 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x94c20)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 tol)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1ec460)) 21 (getr regs 21))
          (0x92e60 : word) (art_mmapfixed_mem M s raw regs addr size tol name) rom).
Proof.
  intros regs M rom raw s addr size tol name F fb H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_mmapfixed_mem.
  zstep F_94b24 D_94b24.
  zsd F_94b28 D_94b28 (s - 8) (U raw) ltac:(rewok W).
  zsd F_94b2c D_94b2c (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_94b30 D_94b30 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_94b34 D_94b34 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_94b38 D_94b38 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_94b3c D_94b3c (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_94b40 D_94b40. zstep F_94b44 D_94b44. zstep F_94b48 D_94b48.
  zstep F_94b4c D_94b4c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0x153118 8 0x1ec460) by zcell; assert (Cpc' : cellA X 0x1ec460 8 4096) by zcell end.
  zld F_94b50 D_94b50 0x153118 Cg28'. zld F_94b54 D_94b54 0x1ec460 Cpc'.
  zstep F_94b58 D_94b58.
  zbtk F_94b5c D_94b5c.
  zstep F_94b6c D_94b6c. zstep F_94b70 D_94b70.
  zbft F_94b74 D_94b74.
  zstep F_94b78 D_94b78. zstep F_94b7c D_94b7c. zstep F_94b80 D_94b80.
  pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
  stepn F_94b84 D_94b84. rwH.
  replace (size + 4096 + -1) with (size + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite RU. replace (size + 4095 - 4095) with size by lia.
  zbtk F_94b88 D_94b88.
  stepn F_94b98 D_94b98. rwH. rewrite art_zb_and by lia.
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite Hal, Z.sub_0_r.
  zstep F_94b9c D_94b9c.
  zsw F_94ba0 D_94ba0 (s - 96) 50 ltac:(rewok W).
  zstep F_94ba4 D_94ba4. zstep F_94ba8 D_94ba8. zstep F_94bac D_94bac.
  stepn F_94bb0 D_94bb0.
  zstep F_951b8 D_951b8.
  zsd F_951bc D_951bc (s - 104) 0x94c04 ltac:(rewok W).
  zsd F_951c0 D_951c0 (s - 112) size ltac:(rewok W).
  zsd F_951c4 D_951c4 (s - 120) tol ltac:(rewok W).
  zsd F_951c8 D_951c8 (s - 128) addr ltac:(rewok W).
  zsd F_951cc D_951cc (s - 136) name ltac:(rewok W).
  zsd F_951d0 D_951d0 (s - 144) 0x1ec460 ltac:(rewok W).
  zsd F_951d4 D_951d4 (s - 152) (U (getr regs 21)) ltac:(rewok W).
  zstep F_951d8 D_951d8.
  zstep F_951dc D_951dc.
  zbft F_951e0 D_951e0.
  zstep F_951e4 D_951e4.
  stepn F_951e8 D_951e8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x153128 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_951ec D_951ec 0x153128 C38c.
  zlbu F_951f0 D_951f0 (F + 260) Cflc.
  stepn F_951f4 D_951f4. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_951f8 D_951f8.
  stepn F_95308 D_95308.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x94c04) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
    assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
    assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x1ec460) by zcell;
    assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
  zld F_9530c D_9530c (s - 104) R1. zld F_95310 D_95310 (s - 112) R2. zld F_95314 D_95314 (s - 120) R3. zld F_95318 D_95318 (s - 128) R4.
  zld F_9531c D_9531c (s - 136) R5. zld F_95320 D_95320 (s - 144) R6. zld F_95324 D_95324 (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
  zstep F_95328 D_95328.
  stepret F_9532c D_9532c (Z_to_bv 64 0x94c04 : word) ltac:(rwH; reflexivity).
  zlw F_94bb4 D_94bb4 (s - 96) R8.
  zstep F_94bb8 D_94bb8. zstep F_94bbc D_94bbc. zstep F_94bc0 D_94bc0. zstep F_94bc4 D_94bc4. zstep F_94bc8 D_94bc8.
  stepn F_94bcc D_94bcc.
  zstep F_92e0c D_92e0c.
  zret.
Qed.

Lemma art_mmapfixed_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x6b3000 <= s - 336 -> s < 2 ^ 47 ->
  forall x : word, ~ (s - 336 <= U x < s) -> art_mmapfixed_mem M s raw rg addr size tol name x = M x.
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
  0x6b3000 <= s - 336 -> s < 2 ^ 47 ->
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 8) 8 (U raw) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 40) 8 (U (getr rg 19)) /\
  cellA (art_mmapfixed_mem M s raw rg addr size tol name) (s - 48) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size tol name Hs Hs'. unfold art_mmapfixed_mem. repeat split; zcell.
Qed.

Definition art_rarmap_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z) : word -> option byte :=
  art_mmapfixed_mem (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18)))
    (s - 32) (0x9cdd8 : word) (regupd (regupd rg 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 addr)) addr size 1 name.

Lemma art_rarmap_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x6b3000 <= s - 368 -> s < 2 ^ 47 ->
  forall x : word, ~ (s - 368 <= U x < s) -> art_rarmap_mem M s raw rg addr size name x = M x.
Proof.
  intros M s raw rg addr size name Hs Hs' x Y. unfold art_rarmap_mem.
  rewrite art_mmapfixed_mem_agree by lia.
  do 4 (rewrite Wn_outside; [ | lia | cbn; lia | cbn; lia ]). reflexivity.
Qed.
Lemma art_rarmap_mem_grows : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  mem_grows M (art_rarmap_mem M s raw rg addr size name).
Proof.
  intros. unfold art_rarmap_mem. eapply mem_grows_trans; [ | apply art_mmapfixed_mem_grows ].
  do 4 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
Lemma art_rarmap_mem_cells : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x6b3000 <= s - 368 -> s < 2 ^ 47 ->
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32 - 8) 8 (U (0x9cdd8 : word)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32 - 16) 8 (U (Z_to_bv 64 size : word)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32 - 24) 8 (U (Z_to_bv 64 addr : word)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32 - 32) 8 (U (getr rg 18)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32 - 40) 8 (U (getr rg 19)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32 - 48) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size name Hs Hs'. unfold art_rarmap_mem, art_mmapfixed_mem. gres. repeat split; zcell.
Qed.

Lemma art_rar_map_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 addr -> getr regs 12 = Z_to_bv 64 size -> getr regs 13 = Z_to_bv 64 name ->
  0x6b3000 <= s - 368 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x6b3000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 368) 368 ->
  cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 -> cellA M 0x153128 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x9cdac : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x94c20)) 2 (Z_to_bv 64 (s - 128))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1ec460)) 21 (getr regs 21))
          (0x92e60 : word) (art_rarmap_mem M s raw regs addr size name) rom).
Proof.
  intros regs M rom raw s addr size name F fb H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  zstep F_9cd5c D_9cd5c.
  zsd F_9cd60 D_9cd60 (s - 8) (U raw) ltac:(rewok W).
  zsd F_9cd64 D_9cd64 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_9cd68 D_9cd68 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_9cd6c D_9cd6c (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_9cd70 D_9cd70. zstep F_9cd74 D_9cd74.
  zstep F_9cd78 D_9cd78. zstep F_9cd7c D_9cd7c. zstep F_9cd80 D_9cd80.
  stepn F_9cd84 D_9cd84.
  zstep F_94c9c D_94c9c. zstep F_94ca0 D_94ca0.
  stepn F_94ca4 D_94ca4.
  zcall (art_mmapfixed_pre_fn _ _ rom (0x9cdd8 : word) (s - 32) addr size 1 name F fb).
  unfold art_rarmap_mem, art_mmapfixed_mem. gres.
  zret.
Qed.

Lemma art_mmapfixed_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 : word) (s size q F : Z),
  getr regs 1 = Z_to_bv 64 0x94c20 -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x6b3000 <= s - 336 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 <= q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x6b3000 ->
  wrA M (s - 336) 336 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) -> cellA M (s - 40) 8 (U x19) -> cellA M (s - 48) 8 (U x20) ->
  cellA M 0x153128 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x92e64 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 52) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 s size q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 C38 C144.
  stepret F_92e14 D_92e14 (Z_to_bv 64 0x94c20 : word) ltac:(rwH; reflexivity).
  zstep F_94bd0 D_94bd0.
  zstep F_94bd4 D_94bd4.
  stepn F_94bd8 D_94bd8.
  zstep F_92dec D_92dec. zstep F_92df0 D_92df0.
  zbtk F_92df4 D_92df4.
  zstep F_92e04 D_92e04.
  stepret F_92e08 D_92e08 (Z_to_bv 64 0x94c2c : word) ltac:(rwH; reflexivity).
  zstep F_94bdc D_94bdc. zstep F_94be0 D_94be0.
  zsw F_94be4 D_94be4 (s - 52) 18446744072277895850 ltac:(rewok W).
  zstep F_94be8 D_94be8. zstep F_94bec D_94bec.
  stepn F_94bf0 D_94bf0.
  zstep F_92dec D_92dec. zstep F_92df0 D_92df0.
  zbtk F_92df4 D_92df4.
  zstep F_92e04 D_92e04.
  stepret F_92e08 D_92e08 (Z_to_bv 64 0x94c44 : word) ltac:(rwH; reflexivity).
  zbft F_94bf4 D_94bf4.
  zstep F_94bf8 D_94bf8.
  stepn F_94bfc D_94bfc.
  zstep F_8ecd4 D_8ecd4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x153128 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_8ecd8 D_8ecd8 0x153128 C38'. zld F_8ecdc D_8ecdc (F + 144) C144'.
  zbtk F_8ece0 D_8ece0.
  stepret F_8ecfc D_8ecfc (Z_to_bv 64 0x94c50 : word) ltac:(rwH; reflexivity).
  zstep F_94c00 D_94c00.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (R2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (R3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (R4 : cellA X (s - 32) 8 (U x18)) by zcell; assert (R5 : cellA X (s - 40) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 48) 8 (U x20)) by zcell end.
  zld F_94c04 D_94c04 (s - 8) R1; rewrite Z_to_bv_bv_unsigned.
  zld F_94c08 D_94c08 (s - 16) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_94c0c D_94c0c (s - 24) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_94c10 D_94c10 (s - 32) R4; rewrite Z_to_bv_bv_unsigned.
  zld F_94c14 D_94c14 (s - 40) R5; rewrite Z_to_bv_bv_unsigned.
  zld F_94c18 D_94c18 (s - 48) R6; rewrite Z_to_bv_bv_unsigned.
  zstep F_94c1c D_94c1c.
  stepret F_94c20 D_94c20 x1 ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rar_map_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 : word) (s size addr q F : Z),
  getr regs 1 = Z_to_bv 64 0x94c20 -> getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x6b3000 <= s - 368 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 < q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x6b3000 ->
  wrA M (s - 368) 368 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) ->
  cellA M (s - 32 - 8) 8 (U (0x9cdd8 : word)) -> cellA M (s - 32 - 16) 8 (U (Z_to_bv 64 size : word)) -> cellA M (s - 32 - 24) 8 (U (Z_to_bv 64 addr : word)) ->
  cellA M (s - 32 - 32) 8 (U x18) -> cellA M (s - 32 - 40) 8 (U x19) -> cellA M (s - 32 - 48) 8 (U x20) ->
  cellA M 0x153128 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x92e64 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 84) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 s size addr q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 I1 I2 I3 I4 I5 I6 C38 C144.
  zcall (art_mmapfixed_post_fn _ M rom (0x9cdd8 : word) (Z_to_bv 64 size : word) (Z_to_bv 64 addr : word) x18 x19 x20 (s - 32) size q F).
  zbft F_9cd88 D_9cd88.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (R2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (R3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (R4 : cellA X (s - 32) 8 (U x18)) by zcell end.
  zld F_9cd8c D_9cd8c (s - 8) R1; rewrite Z_to_bv_bv_unsigned.
  zld F_9cd90 D_9cd90 (s - 16) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_9cd94 D_9cd94 (s - 24) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_9cd98 D_9cd98 (s - 32) R4; rewrite Z_to_bv_bv_unsigned.
  zstep F_9cd9c D_9cd9c.
  stepret F_9cda0 D_9cda0 x1 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
