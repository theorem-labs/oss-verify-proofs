(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac Pm9ArtDepotA Pm9ArtSecAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_8f000_90000 Pm9_code_93000_94000 Pm9_code_94000_95000 Pm9_code_95000_96000 Pm9_code_9d000_9e000
       .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
    (s - 104) 0x94fc4) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x1ed7a0) (s - 152) (U (getr rg 21)).

Lemma art_mmapfixed_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size tol name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 tol -> getr regs 13 = Z_to_bv 64 name ->
  0x6b4000 <= s - 336 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 <= tol < 2 ^ 64 -> 0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x6b4000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 336) 336 ->
  cellA M 0x1544e0 8 0x1ed7a0 -> cellA M 0x1ed7a0 8 4096 -> cellA M 0x1544f0 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x94f34 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x94fe0)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 tol)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1ed7a0)) 21 (getr regs 21))
          (0x93220 : word) (art_mmapfixed_mem M s raw regs addr size tol name) rom).
Proof.
  intros regs M rom raw s addr size tol name F fb H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_mmapfixed_mem.
  zstep F_94eec D_94eec.
  zsd F_94ef0 D_94ef0 (s - 8) (U raw) ltac:(rewok W).
  zsd F_94ef4 D_94ef4 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_94ef8 D_94ef8 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_94efc D_94efc (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_94f00 D_94f00 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_94f04 D_94f04 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_94f08 D_94f08. zstep F_94f0c D_94f0c. zstep F_94f10 D_94f10.
  zstep F_94f14 D_94f14.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0x1544e0 8 0x1ed7a0) by zcell; assert (Cpc' : cellA X 0x1ed7a0 8 4096) by zcell end.
  zld F_94f18 D_94f18 0x1544e0 Cg28'. zld F_94f1c D_94f1c 0x1ed7a0 Cpc'.
  zstep F_94f20 D_94f20.
  zbtk F_94f24 D_94f24.
  zstep F_94f34 D_94f34. zstep F_94f38 D_94f38.
  zbft F_94f3c D_94f3c.
  zstep F_94f40 D_94f40. zstep F_94f44 D_94f44. zstep F_94f48 D_94f48.
  pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
  stepn F_94f4c D_94f4c. rwH.
  replace (size + 4096 + -1) with (size + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite RU. replace (size + 4095 - 4095) with size by lia.
  zbtk F_94f50 D_94f50.
  stepn F_94f60 D_94f60. rwH. rewrite art_zb_and by lia.
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite Hal, Z.sub_0_r.
  zstep F_94f64 D_94f64.
  zsw F_94f68 D_94f68 (s - 96) 50 ltac:(rewok W).
  zstep F_94f6c D_94f6c. zstep F_94f70 D_94f70. zstep F_94f74 D_94f74.
  stepn F_94f78 D_94f78.
  zstep F_95580 D_95580.
  zsd F_95584 D_95584 (s - 104) 0x94fc4 ltac:(rewok W).
  zsd F_95588 D_95588 (s - 112) size ltac:(rewok W).
  zsd F_9558c D_9558c (s - 120) tol ltac:(rewok W).
  zsd F_95590 D_95590 (s - 128) addr ltac:(rewok W).
  zsd F_95594 D_95594 (s - 136) name ltac:(rewok W).
  zsd F_95598 D_95598 (s - 144) 0x1ed7a0 ltac:(rewok W).
  zsd F_9559c D_9559c (s - 152) (U (getr regs 21)) ltac:(rewok W).
  zstep F_955a0 D_955a0.
  zstep F_955a4 D_955a4.
  zbft F_955a8 D_955a8.
  zstep F_955ac D_955ac.
  stepn F_955b0 D_955b0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x1544f0 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_955b4 D_955b4 0x1544f0 C38c.
  zlbu F_955b8 D_955b8 (F + 260) Cflc.
  stepn F_955bc D_955bc. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_955c0 D_955c0.
  stepn F_956d0 D_956d0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x94fc4) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
    assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
    assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x1ed7a0) by zcell;
    assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
  zld F_956d4 D_956d4 (s - 104) R1. zld F_956d8 D_956d8 (s - 112) R2. zld F_956dc D_956dc (s - 120) R3. zld F_956e0 D_956e0 (s - 128) R4.
  zld F_956e4 D_956e4 (s - 136) R5. zld F_956e8 D_956e8 (s - 144) R6. zld F_956ec D_956ec (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
  zstep F_956f0 D_956f0.
  stepret F_956f4 D_956f4 (Z_to_bv 64 0x94fc4 : word) ltac:(rwH; reflexivity).
  zlw F_94f7c D_94f7c (s - 96) R8.
  zstep F_94f80 D_94f80. zstep F_94f84 D_94f84. zstep F_94f88 D_94f88. zstep F_94f8c D_94f8c. zstep F_94f90 D_94f90.
  stepn F_94f94 D_94f94.
  zstep F_931d4 D_931d4.
  zret.
Qed.

Lemma art_mmapfixed_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x6b4000 <= s - 336 -> s < 2 ^ 47 ->
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
  0x6b4000 <= s - 336 -> s < 2 ^ 47 ->
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
    (s - 32) (0x9d198 : word) (regupd (regupd rg 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 addr)) addr size 1 name.

Lemma art_rarmap_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x6b4000 <= s - 368 -> s < 2 ^ 47 ->
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
  0x6b4000 <= s - 368 -> s < 2 ^ 47 ->
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_rarmap_mem M s raw rg addr size name) (s - 32 - 8) 8 (U (0x9d198 : word)) /\
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
  0x6b4000 <= s - 368 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x6b4000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 368) 368 ->
  cellA M 0x1544e0 8 0x1ed7a0 -> cellA M 0x1ed7a0 8 4096 -> cellA M 0x1544f0 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x9d16c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x94fe0)) 2 (Z_to_bv 64 (s - 128))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1ed7a0)) 21 (getr regs 21))
          (0x93220 : word) (art_rarmap_mem M s raw regs addr size name) rom).
Proof.
  intros regs M rom raw s addr size name F fb H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  zstep F_9d124 D_9d124.
  zsd F_9d128 D_9d128 (s - 8) (U raw) ltac:(rewok W).
  zsd F_9d12c D_9d12c (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_9d130 D_9d130 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_9d134 D_9d134 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_9d138 D_9d138. zstep F_9d13c D_9d13c.
  zstep F_9d140 D_9d140. zstep F_9d144 D_9d144. zstep F_9d148 D_9d148.
  stepn F_9d14c D_9d14c.
  zstep F_95064 D_95064. zstep F_95068 D_95068.
  stepn F_9506c D_9506c.
  zcall (art_mmapfixed_pre_fn _ _ rom (0x9d198 : word) (s - 32) addr size 1 name F fb).
  unfold art_rarmap_mem, art_mmapfixed_mem. gres.
  zret.
Qed.

Lemma art_mmapfixed_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 : word) (s size q F : Z),
  getr regs 1 = Z_to_bv 64 0x94fe0 -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x6b4000 <= s - 336 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 <= q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x6b4000 ->
  wrA M (s - 336) 336 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) -> cellA M (s - 40) 8 (U x19) -> cellA M (s - 48) 8 (U x20) ->
  cellA M 0x1544f0 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x93224 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 52) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 s size q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 C38 C144.
  stepret F_931dc D_931dc (Z_to_bv 64 0x94fe0 : word) ltac:(rwH; reflexivity).
  zstep F_94f98 D_94f98.
  zstep F_94f9c D_94f9c.
  stepn F_94fa0 D_94fa0.
  zstep F_931b4 D_931b4. zstep F_931b8 D_931b8.
  zbtk F_931bc D_931bc.
  zstep F_931cc D_931cc.
  stepret F_931d0 D_931d0 (Z_to_bv 64 0x94fec : word) ltac:(rwH; reflexivity).
  zstep F_94fa4 D_94fa4. zstep F_94fa8 D_94fa8.
  zsw F_94fac D_94fac (s - 52) 18446744072277895850 ltac:(rewok W).
  zstep F_94fb0 D_94fb0. zstep F_94fb4 D_94fb4.
  stepn F_94fb8 D_94fb8.
  zstep F_931b4 D_931b4. zstep F_931b8 D_931b8.
  zbtk F_931bc D_931bc.
  zstep F_931cc D_931cc.
  stepret F_931d0 D_931d0 (Z_to_bv 64 0x95004 : word) ltac:(rwH; reflexivity).
  zbft F_94fbc D_94fbc.
  zstep F_94fc0 D_94fc0.
  stepn F_94fc4 D_94fc4.
  zstep F_8f09c D_8f09c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x1544f0 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_8f0a0 D_8f0a0 0x1544f0 C38'. zld F_8f0a4 D_8f0a4 (F + 144) C144'.
  zbtk F_8f0a8 D_8f0a8.
  stepret F_8f0c4 D_8f0c4 (Z_to_bv 64 0x95010 : word) ltac:(rwH; reflexivity).
  zstep F_94fc8 D_94fc8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (R2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (R3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (R4 : cellA X (s - 32) 8 (U x18)) by zcell; assert (R5 : cellA X (s - 40) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 48) 8 (U x20)) by zcell end.
  zld F_94fcc D_94fcc (s - 8) R1; rewrite Z_to_bv_bv_unsigned.
  zld F_94fd0 D_94fd0 (s - 16) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_94fd4 D_94fd4 (s - 24) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_94fd8 D_94fd8 (s - 32) R4; rewrite Z_to_bv_bv_unsigned.
  zld F_94fdc D_94fdc (s - 40) R5; rewrite Z_to_bv_bv_unsigned.
  zld F_94fe0 D_94fe0 (s - 48) R6; rewrite Z_to_bv_bv_unsigned.
  zstep F_94fe4 D_94fe4.
  stepret F_94fe8 D_94fe8 x1 ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rar_map_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 : word) (s size addr q F : Z),
  getr regs 1 = Z_to_bv 64 0x94fe0 -> getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x6b4000 <= s - 368 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 < q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x6b4000 ->
  wrA M (s - 368) 368 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) ->
  cellA M (s - 32 - 8) 8 (U (0x9d198 : word)) -> cellA M (s - 32 - 16) 8 (U (Z_to_bv 64 size : word)) -> cellA M (s - 32 - 24) 8 (U (Z_to_bv 64 addr : word)) ->
  cellA M (s - 32 - 32) 8 (U x18) -> cellA M (s - 32 - 40) 8 (U x19) -> cellA M (s - 32 - 48) 8 (U x20) ->
  cellA M 0x1544f0 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x93224 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 84) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 s size addr q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 I1 I2 I3 I4 I5 I6 C38 C144.
  zcall (art_mmapfixed_post_fn _ M rom (0x9d198 : word) (Z_to_bv 64 size : word) (Z_to_bv 64 addr : word) x18 x19 x20 (s - 32) size q F).
  zbft F_9d150 D_9d150.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (R2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (R3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (R4 : cellA X (s - 32) 8 (U x18)) by zcell end.
  zld F_9d154 D_9d154 (s - 8) R1; rewrite Z_to_bv_bv_unsigned.
  zld F_9d158 D_9d158 (s - 16) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_9d15c D_9d15c (s - 24) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_9d160 D_9d160 (s - 32) R4; rewrite Z_to_bv_bv_unsigned.
  zstep F_9d164 D_9d164.
  stepret F_9d168 D_9d168 x1 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
