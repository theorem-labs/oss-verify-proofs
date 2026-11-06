(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac BrtDepotA BrtSecAlloc.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_71dc0_71df8 Bo0_code_6dcc4_6dd2c
     Bo0_code_73aec_73c7c Bo0_code_7418c_74398 Bo0_code_7bd30_7be7c.
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

(* [comment removed for export] *)
Definition art_mmapfixed_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 96) 50)
    (s - 104) 0x73b88) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x16e1e0) (s - 152) (U (getr rg 21)).

Lemma art_mmapfixed_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size tol name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 tol -> getr regs 13 = Z_to_bv 64 name ->
  0x634000 <= s - 368 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 <= tol < 2 ^ 64 -> 0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x634000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 368) 368 ->
  cellA M 0xd64a8 8 0x16e1e0 -> cellA M 0x16e1e0 8 4096 -> cellA M 0xd64b8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x73af8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x73ba4)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 tol)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x16e1e0)) 21 (getr regs 21))
          (0x71de4 : word) (art_mmapfixed_mem M s raw regs addr size tol name) rom).
Proof.
  intros regs M rom raw s addr size tol name F fb H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_mmapfixed_mem.
  zstep F_73af8 D_73af8.                                                         (* [comment removed for export] *)
  zsd F_73afc D_73afc (s - 8) (U raw) ltac:(rewok W).
  zsd F_73b00 D_73b00 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_73b04 D_73b04 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_73b08 D_73b08 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_73b0c D_73b0c (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_73b10 D_73b10 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_73b14 D_73b14. zstep F_73b18 D_73b18. zstep F_73b1c D_73b1c.           (* [comment removed for export] *)
  zstep F_73b20 D_73b20.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0xd64a8 8 0x16e1e0) by zcell; assert (Cpc' : cellA X 0x16e1e0 8 4096) by zcell end.
  zld F_73b24 D_73b24 0xd64a8 Cg28'. zld F_73b28 D_73b28 0x16e1e0 Cpc'.
  zstep F_73b2c D_73b2c.                                                         (* [comment removed for export] *)
  zbtk F_73b30 D_73b30.                                                          (* [comment removed for export] *)
  zstep F_73b40 D_73b40. zstep F_73b44 D_73b44.                                  (* [comment removed for export] *)
  zbft F_73b48 D_73b48.
  zstep F_73b4c D_73b4c. zstep F_73b50 D_73b50. zstep F_73b54 D_73b54.           (* [comment removed for export] *)
  pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
  stepn F_73b58 D_73b58. rwH.                                                    (* [comment removed for export] *)
  replace (size + 4096 + -1) with (size + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite RU. replace (size + 4095 - 4095) with size by lia.
  zbtk F_73b5c D_73b5c.                                                          (* [comment removed for export] *)
  stepn F_73b6c D_73b6c. rwH. rewrite art_zb_and by lia.                         (* [comment removed for export] *)
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite Hal, Z.sub_0_r.
  zstep F_73b70 D_73b70.                                                         (* [comment removed for export] *)
  zsw F_73b74 D_73b74 (s - 96) 50 ltac:(rewok W).                                  (* [comment removed for export] *)
  zstep F_73b78 D_73b78. zstep F_73b7c D_73b7c. zstep F_73b80 D_73b80.           (* [comment removed for export] *)
  stepn F_73b84 D_73b84.                                                         (* [comment removed for export] *)
  zstep F_7418c D_7418c.                                                         (* [comment removed for export] *)
  zsd F_74190 D_74190 (s - 104) 0x73b88 ltac:(rewok W).
  zsd F_74194 D_74194 (s - 112) size ltac:(rewok W).
  zsd F_74198 D_74198 (s - 120) tol ltac:(rewok W).
  zsd F_7419c D_7419c (s - 128) addr ltac:(rewok W).
  zsd F_741a0 D_741a0 (s - 136) name ltac:(rewok W).
  zsd F_741a4 D_741a4 (s - 144) 0x16e1e0 ltac:(rewok W).
  zsd F_741a8 D_741a8 (s - 152) (U (getr regs 21)) ltac:(rewok W).
  zstep F_741ac D_741ac.                                                         (* [comment removed for export] *)
  zstep F_741b0 D_741b0.                                                         (* [comment removed for export] *)
  zbft F_741b4 D_741b4.                                                          (* [comment removed for export] *)
  zstep F_741b8 D_741b8.                                                         (* [comment removed for export] *)
  stepn F_741bc D_741bc.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0xd64b8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_741c0 D_741c0 0xd64b8 C38c.                                              (* [comment removed for export] *)
  zlbu F_741c4 D_741c4 (F + 260) Cflc.                                           (* [comment removed for export] *)
  stepn F_741c8 D_741c8. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.          (* [comment removed for export] *)
  zbtk F_741cc D_741cc.                                                          (* [comment removed for export] *)
  stepn F_742dc D_742dc.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x73b88) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
    assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
    assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x16e1e0) by zcell;
    assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
  zld F_742e0 D_742e0 (s - 104) R1. zld F_742e4 D_742e4 (s - 112) R2. zld F_742e8 D_742e8 (s - 120) R3. zld F_742ec D_742ec (s - 128) R4.
  zld F_742f0 D_742f0 (s - 136) R5. zld F_742f4 D_742f4 (s - 144) R6. zld F_742f8 D_742f8 (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
  zstep F_742fc D_742fc.                                                         (* [comment removed for export] *)
  stepret F_74300 D_74300 (Z_to_bv 64 0x73b88 : word) ltac:(rwH; reflexivity).
  zlw F_73b88 D_73b88 (s - 96) R8.                                               (* [comment removed for export] *)
  zstep F_73b8c D_73b8c. zstep F_73b90 D_73b90. zstep F_73b94 D_73b94. zstep F_73b98 D_73b98. zstep F_73b9c D_73b9c.   (* [comment removed for export] *)
  stepn F_73ba0 D_73ba0.                                                         (* [comment removed for export] *)
  zstep F_71de0 D_71de0.                                                         (* [comment removed for export] *)
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_mmapfixed_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x634000 <= s - 368 -> s < 2 ^ 47 ->
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
  0x634000 <= s - 368 -> s < 2 ^ 47 ->
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
    (s - 40) 0x7bd5c) (s - 48) size) (s - 56) addr) (s - 64) (U (getr rg 18))) (s - 72) (U (getr rg 19))) (s - 80) (U (getr rg 20)))
    (s - 128) 50)
    (s - 136) 0x73b88) (s - 144) size) (s - 152) 1) (s - 160) addr) (s - 168) name) (s - 176) 0x16e1e0) (s - 184) (U (getr rg 21)).

Lemma art_rar_map_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 addr -> getr regs 12 = Z_to_bv 64 size -> getr regs 13 = Z_to_bv 64 name ->
  0x634000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x634000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 400) 400 ->
  cellA M 0xd64a8 8 0x16e1e0 -> cellA M 0x16e1e0 8 4096 -> cellA M 0xd64b8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x7bd30 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x73ba4)) 2 (Z_to_bv 64 (s - 128))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x16e1e0)) 21 (getr regs 21))
          (0x71de4 : word) (art_rar_map_mem M s raw regs addr size name) rom).
Proof.
  intros regs M rom raw s addr size name F fb H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_rar_map_mem, art_rar_frame.           (* [comment removed for export] *)
  zstep F_7bd30 D_7bd30.                                                         (* [comment removed for export] *)
  zsd F_7bd34 D_7bd34 (s - 8) (U raw) ltac:(rewok W).
  zsd F_7bd38 D_7bd38 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7bd3c D_7bd3c (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_7bd40 D_7bd40 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_7bd44 D_7bd44. zstep F_7bd48 D_7bd48.
  zstep F_7bd4c D_7bd4c. zstep F_7bd50 D_7bd50. zstep F_7bd54 D_7bd54.
  stepn F_7bd58 D_7bd58.
  zstep F_73c70 D_73c70. zstep F_73c74 D_73c74.                                  (* [comment removed for export] *)
  stepn F_73c78 D_73c78.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cg28' : cellA X 0xd64a8 8 0x16e1e0) by zcell; assert (Cpc' : cellA X 0x16e1e0 8 4096) by zcell;
    assert (Cg38' : cellA X 0xd64b8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell;
    assert (W' : wrA X (s - 32 - 368) 368) by zwr end.
  zcall (art_mmapfixed_pre_fn _ _ rom (Z_to_bv 64 0x7bd5c) (s - 32) addr size 1 name F fb).
  unfold art_mmapfixed_mem. gres.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_rar_map_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x634000 <= s - 400 -> s < 2 ^ 47 ->
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
  0x634000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> 0 <= size < 2 ^ 47 ->
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 40) 8 0x7bd5c /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 48) 8 size /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 56) 8 addr /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 64) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 72) 8 (U (getr rg 19)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 80) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size name Hs Hs' Ha Hsz. unfold art_rar_map_mem, art_rar_frame. repeat split; zcell.
Qed.

Lemma art_rar_map_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 y8 y9 y18 : word) (s size q F : Z),
  getr regs 1 = Z_to_bv 64 0x73ba4 -> getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x634000 <= s - 400 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 < q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x634000 ->
  wrA M (s - 400) 400 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) ->
  cellA M (s - 40) 8 0x7bd5c -> cellA M (s - 48) 8 (U y8) -> cellA M (s - 56) 8 (U y9) -> cellA M (s - 64) 8 (U y18) -> cellA M (s - 72) 8 (U x19) -> cellA M (s - 80) 8 (U x20) ->
  cellA M 0xd64b8 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x71de8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 84) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 y8 y9 y18 s size q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 C38 C144.
  stepret F_71de8 D_71de8 (Z_to_bv 64 0x73ba4 : word) ltac:(rwH; reflexivity).        (* [comment removed for export] *)
  zstep F_73ba4 D_73ba4.                                                         (* [comment removed for export] *)
  zstep F_73ba8 D_73ba8.                                                         (* [comment removed for export] *)
  stepn F_73bac D_73bac.                                                         (* [comment removed for export] *)
  zstep F_71dc0 D_71dc0. zstep F_71dc4 D_71dc4.
  zbtk F_71dc8 D_71dc8.
  zstep F_71dd8 D_71dd8.
  stepret F_71ddc D_71ddc (Z_to_bv 64 0x73bb0 : word) ltac:(rwH; reflexivity).
  zstep F_73bb0 D_73bb0. zstep F_73bb4 D_73bb4.                                  (* [comment removed for export] *)
  zsw F_73bb8 D_73bb8 (s - 84) 18446744072277895850 ltac:(rewok W).              (* [comment removed for export] *)
  zstep F_73bbc D_73bbc. zstep F_73bc0 D_73bc0.                                  (* [comment removed for export] *)
  stepn F_73bc4 D_73bc4.                                                         (* [comment removed for export] *)
  zstep F_71dc0 D_71dc0. zstep F_71dc4 D_71dc4.
  zbtk F_71dc8 D_71dc8.
  zstep F_71dd8 D_71dd8.
  stepret F_71ddc D_71ddc (Z_to_bv 64 0x73bc8 : word) ltac:(rwH; reflexivity).
  zbft F_73bc8 D_73bc8.                                                          (* [comment removed for export] *)
  zstep F_73bcc D_73bcc.                                                         (* [comment removed for export] *)
  stepn F_73bd0 D_73bd0.                                                         (* [comment removed for export] *)
  zstep F_6dcc4 D_6dcc4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0xd64b8 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_6dcc8 D_6dcc8 0xd64b8 C38'. zld F_6dccc D_6dccc (F + 144) C144'.
  zbtk F_6dcd0 D_6dcd0.
  stepret F_6dcec D_6dcec (Z_to_bv 64 0x73bd4 : word) ltac:(rwH; reflexivity).
  zstep F_73bd4 D_73bd4.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 40) 8 0x7bd5c) by zcell; assert (R2 : cellA X (s - 48) 8 (U y8)) by zcell; assert (R3 : cellA X (s - 56) 8 (U y9)) by zcell;
    assert (R4 : cellA X (s - 64) 8 (U y18)) by zcell; assert (R5 : cellA X (s - 72) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 80) 8 (U x20)) by zcell;
    assert (Q1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (Q2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (Q3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (Q4 : cellA X (s - 32) 8 (U x18)) by zcell end.
  zld F_73bd8 D_73bd8 (s - 40) R1.
  zld F_73bdc D_73bdc (s - 48) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_73be0 D_73be0 (s - 56) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_73be4 D_73be4 (s - 64) R4; rewrite Z_to_bv_bv_unsigned.
  zld F_73be8 D_73be8 (s - 72) R5; rewrite Z_to_bv_bv_unsigned.
  zld F_73bec D_73bec (s - 80) R6; rewrite Z_to_bv_bv_unsigned.
  zstep F_73bf0 D_73bf0.                                                         (* [comment removed for export] *)
  stepret F_73bf4 D_73bf4 (Z_to_bv 64 0x7bd5c : word) ltac:(rwH; reflexivity).
  zbft F_7bd5c D_7bd5c.
  zld F_7bd60 D_7bd60 (s - 8) Q1; rewrite Z_to_bv_bv_unsigned.
  zld F_7bd64 D_7bd64 (s - 16) Q2; rewrite Z_to_bv_bv_unsigned.
  zld F_7bd68 D_7bd68 (s - 24) Q3; rewrite Z_to_bv_bv_unsigned.
  zld F_7bd6c D_7bd6c (s - 32) Q4; rewrite Z_to_bv_bv_unsigned.
  zstep F_7bd70 D_7bd70.
  stepret F_7bd74 D_7bd74 x1 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
