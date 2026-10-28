(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatDepotA_b BatSecAlloc_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r719b0_719e8_b Ba0_code_r6d8b4_6d91c_b
     Ba0_code_r7b920_7b940_b Ba0_code_r736dc_7386c_b Ba0_code_r73d7c_73f88_b Ba0_code_956bc_95730_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
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
    (s - 104) 0x8da24) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x1cf6e0) (s - 152) (U (getr rg 21)).

#[using="Type"] Lemma art_mmapfixed_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size tol name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 addr -> getr regs 11 = Z_to_bv 64 size ->
  getr regs 12 = Z_to_bv 64 tol -> getr regs 13 = Z_to_bv 64 name ->
  0x696000 <= s - 368 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 <= tol < 2 ^ 64 -> 0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x696000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 368) 368 ->
  cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M 0x1374b0 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x8d994 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8da40)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 tol)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1cf6e0)) 21 (getr regs 21))
          (0x8bc80 : word) (art_mmapfixed_mem M s raw regs addr size tol name) rom).
Proof.
  intros regs M rom raw s addr size tol name F fb H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_mmapfixed_mem.
  zstep F_8d57c D_8d57c.                                                         (* [comment removed for export] *)
  zsd F_8d580 D_8d580 (s - 8) (U raw) ltac:(rewok W).
  zsd F_8d584 D_8d584 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_8d588 D_8d588 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_8d58c D_8d58c (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_8d590 D_8d590 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_8d594 D_8d594 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zstep F_8d598 D_8d598. zstep F_8d59c D_8d59c. zstep F_8d5a0 D_8d5a0.           (* [comment removed for export] *)
  zstep F_8d5a4 D_8d5a4.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0x1374a0 8 0x1cf6e0) by zcell; assert (Cpc' : cellA X 0x1cf6e0 8 4096) by zcell end.
  zld F_8d5a8 D_8d5a8 0x1374a0 Cg28'. zld F_8d5ac D_8d5ac 0x1cf6e0 Cpc'.
  zstep F_8d5b0 D_8d5b0.                                                         (* [comment removed for export] *)
  zbtk F_8d5b4 D_8d5b4.                                                          (* [comment removed for export] *)
  zstep F_8d5c4 D_8d5c4. zstep F_8d5c8 D_8d5c8.                                  (* [comment removed for export] *)
  zbft F_8d5cc D_8d5cc.
  zstep F_8d5d0 D_8d5d0. zstep F_8d5d4 D_8d5d4. zstep F_8d5d8 D_8d5d8.           (* [comment removed for export] *)
  pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
  stepn F_8d5dc D_8d5dc. rwH.                                                    (* [comment removed for export] *)
  replace (size + 4096 + -1) with (size + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite RU. replace (size + 4095 - 4095) with size by lia.
  zbtk F_8d5e0 D_8d5e0.                                                          (* [comment removed for export] *)
  stepn F_8d5f0 D_8d5f0. rwH. rewrite art_zb_and by lia.                         (* [comment removed for export] *)
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  rewrite Hal, Z.sub_0_r.
  zstep F_8d5f4 D_8d5f4.                                                         (* [comment removed for export] *)
  zsw F_8d5f8 D_8d5f8 (s - 96) 50 ltac:(rewok W).                                  (* [comment removed for export] *)
  zstep F_8d5fc D_8d5fc. zstep F_8d600 D_8d600. zstep F_8d604 D_8d604.           (* [comment removed for export] *)
  stepn F_8d608 D_8d608.                                                         (* [comment removed for export] *)
  zstep F_8dc10 D_8dc10.                                                         (* [comment removed for export] *)
  zsd F_8dc14 D_8dc14 (s - 104) 0x8da24 ltac:(rewok W).
  zsd F_8dc18 D_8dc18 (s - 112) size ltac:(rewok W).
  zsd F_8dc1c D_8dc1c (s - 120) tol ltac:(rewok W).
  zsd F_8dc20 D_8dc20 (s - 128) addr ltac:(rewok W).
  zsd F_8dc24 D_8dc24 (s - 136) name ltac:(rewok W).
  zsd F_8dc28 D_8dc28 (s - 144) 0x1cf6e0 ltac:(rewok W).
  zsd F_8dc2c D_8dc2c (s - 152) (U (getr regs 21)) ltac:(rewok W).
  zstep F_8dc30 D_8dc30.                                                         (* [comment removed for export] *)
  zstep F_8dc34 D_8dc34.                                                         (* [comment removed for export] *)
  zbft F_8dc38 D_8dc38.                                                          (* [comment removed for export] *)
  zstep F_8dc3c D_8dc3c.                                                         (* [comment removed for export] *)
  stepn F_8dc40 D_8dc40.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x1374b0 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_8dc44 D_8dc44 0x1374b0 C38c.                                              (* [comment removed for export] *)
  zlbu F_8dc48 D_8dc48 (F + 260) Cflc.                                           (* [comment removed for export] *)
  stepn F_8dc4c D_8dc4c. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.          (* [comment removed for export] *)
  zbtk F_8dc50 D_8dc50.                                                          (* [comment removed for export] *)
  stepn F_8dd60 D_8dd60.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x8da24) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
    assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
    assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x1cf6e0) by zcell;
    assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
  zld F_8dd64 D_8dd64 (s - 104) R1. zld F_8dd68 D_8dd68 (s - 112) R2. zld F_8dd6c D_8dd6c (s - 120) R3. zld F_8dd70 D_8dd70 (s - 128) R4.
  zld F_8dd74 D_8dd74 (s - 136) R5. zld F_8dd78 D_8dd78 (s - 144) R6. zld F_8dd7c D_8dd7c (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
  zstep F_8dd80 D_8dd80.                                                         (* [comment removed for export] *)
  stepret F_8dd84 D_8dd84 (Z_to_bv 64 0x8da24 : word) ltac:(rwH; reflexivity).
  zlw F_8d60c D_8d60c (s - 96) R8.                                               (* [comment removed for export] *)
  zstep F_8d610 D_8d610. zstep F_8d614 D_8d614. zstep F_8d618 D_8d618. zstep F_8d61c D_8d61c. zstep F_8d620 D_8d620.   (* [comment removed for export] *)
  stepn F_8d624 D_8d624.                                                         (* [comment removed for export] *)
  zstep F_8b864 D_8b864.                                                         (* [comment removed for export] *)
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_mmapfixed_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z),
  0x696000 <= s - 368 -> s < 2 ^ 47 ->
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
  0x696000 <= s - 368 -> s < 2 ^ 47 ->
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
(* [comment removed for export] *)
Definition art_rar_map_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (art_rar_frame M s raw rg)
    (s - 40) 0x95bf8) (s - 48) size) (s - 56) addr) (s - 64) (U (getr rg 18))) (s - 72) (U (getr rg 19))) (s - 80) (U (getr rg 20)))
    (s - 128) 50)
    (s - 136) 0x8da24) (s - 144) size) (s - 152) 1) (s - 160) addr) (s - 168) name) (s - 176) 0x1cf6e0) (s - 184) (U (getr rg 21)).

(* [comment removed for export] *)
#[using="Type"] Lemma art_rar_map_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s addr size name F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 addr -> getr regs 12 = Z_to_bv 64 size -> getr regs 13 = Z_to_bv 64 name ->
  0x696000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> addr mod 4096 = 0 -> 0 <= size < 2 ^ 47 -> size mod 4096 = 0 ->
  0 < name < 2 ^ 64 -> 0x10000 <= F -> F + 512 < 0x696000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 400) 400 ->
  cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M 0x1374b0 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x95bcc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8da40)) 2 (Z_to_bv 64 (s - 128))) 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 addr)) 11 (Z_to_bv 64 size)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 addr)) 19 (Z_to_bv 64 name)) 20 (Z_to_bv 64 0x1cf6e0)) 21 (getr regs 21))
          (0x8bc80 : word) (art_rar_map_mem M s raw regs addr size name) rom).
Proof.
  intros regs M rom raw s addr size name F fb H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
  unfold art_rar_map_mem, art_rar_frame.
  zstep F_957b4 D_957b4.                                                         (* [comment removed for export] *)
  zsd F_957b8 D_957b8 (s - 8) (U raw) ltac:(rewok W).                            (* [comment removed for export] *)
  zsd F_957bc D_957bc (s - 16) (U (getr regs 8)) ltac:(rewok W).                 (* [comment removed for export] *)
  zsd F_957c0 D_957c0 (s - 24) (U (getr regs 9)) ltac:(rewok W).                 (* [comment removed for export] *)
  zsd F_957c4 D_957c4 (s - 32) (U (getr regs 18)) ltac:(rewok W).                (* [comment removed for export] *)
  zstep F_957c8 D_957c8. zstep F_957cc D_957cc.                                  (* [comment removed for export] *)
  zstep F_957d0 D_957d0. zstep F_957d4 D_957d4. zstep F_957d8 D_957d8.           (* [comment removed for export] *)
  stepn F_957dc D_957dc.                                                         (* [comment removed for export] *)
  zstep F_8d6f4 D_8d6f4. zstep F_8d6f8 D_8d6f8.                                  (* [comment removed for export] *)
  stepn F_8d6fc D_8d6fc.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cg28' : cellA X 0x1374a0 8 0x1cf6e0) by zcell; assert (Cpc' : cellA X 0x1cf6e0 8 4096) by zcell;
    assert (Cg38' : cellA X 0x1374b0 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell;
    assert (W' : wrA X (s - 32 - 368) 368) by zwr end.
  zcall (art_mmapfixed_pre_fn _ _ rom (Z_to_bv 64 0x95bf8) (s - 32) addr size 1 name F fb).
  unfold art_mmapfixed_mem. gres.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rar_map_mem_agree : forall (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z),
  0x696000 <= s - 400 -> s < 2 ^ 47 ->
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
  0x696000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 47 -> 0 <= size < 2 ^ 47 ->
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 40) 8 0x95bf8 /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 48) 8 size /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 56) 8 addr /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 64) 8 (U (getr rg 18)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 72) 8 (U (getr rg 19)) /\
  cellA (art_rar_map_mem M s raw rg addr size name) (s - 80) 8 (U (getr rg 20)).
Proof.
  intros M s raw rg addr size name Hs Hs' Ha Hsz. unfold art_rar_map_mem, art_rar_frame. repeat split; zcell.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rar_map_post_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 y8 y9 y18 : word) (s size q F : Z),
  getr regs 1 = Z_to_bv 64 0x8da40 -> getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 8 = Z_to_bv 64 size -> getr regs 10 = Z_to_bv 64 q ->
  ret_ok x1 ->
  0x696000 <= s - 400 -> s < 2 ^ 47 -> 0 <= size < 2 ^ 47 -> 0 < q < 2 ^ 64 - 4095 -> 0x10000 <= F -> F + 512 < 0x696000 ->
  wrA M (s - 400) 400 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) ->
  cellA M (s - 40) 8 0x95bf8 -> cellA M (s - 48) 8 (U y8) -> cellA M (s - 56) 8 (U y9) -> cellA M (s - 64) 8 (U y18) -> cellA M (s - 72) 8 (U x19) -> cellA M (s - 80) 8 (U x20) ->
  cellA M 0x1374b0 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x8bc84 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521))
             18 x18) 19 x19) 20 x20)
          x1 (Wn 4 M (s - 84) 18446744072277895850) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 y8 y9 y18 s size q F H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 C38 C144.
  stepret F_8b86c D_8b86c (Z_to_bv 64 0x8da40 : word) ltac:(rwH; reflexivity).        (* [comment removed for export] *)
  zstep F_8d628 D_8d628.                                                         (* [comment removed for export] *)
  zstep F_8d62c D_8d62c.                                                         (* [comment removed for export] *)
  stepn F_8d630 D_8d630.                                                         (* [comment removed for export] *)
  zstep F_8b844 D_8b844. zstep F_8b848 D_8b848.
  zbtk F_8b84c D_8b84c.
  zstep F_8b85c D_8b85c.
  stepret F_8b860 D_8b860 (Z_to_bv 64 0x8da4c : word) ltac:(rwH; reflexivity).
  zstep F_8d634 D_8d634. zstep F_8d638 D_8d638.                                  (* [comment removed for export] *)
  zsw F_8d63c D_8d63c (s - 84) 18446744072277895850 ltac:(rewok W).              (* [comment removed for export] *)
  zstep F_8d640 D_8d640. zstep F_8d644 D_8d644.                                  (* [comment removed for export] *)
  stepn F_8d648 D_8d648.                                                         (* [comment removed for export] *)
  zstep F_8b844 D_8b844. zstep F_8b848 D_8b848.
  zbtk F_8b84c D_8b84c.
  zstep F_8b85c D_8b85c.
  stepret F_8b860 D_8b860 (Z_to_bv 64 0x8da64 : word) ltac:(rwH; reflexivity).
  zbft F_8d64c D_8d64c.                                                          (* [comment removed for export] *)
  zstep F_8d650 D_8d650.                                                         (* [comment removed for export] *)
  stepn F_8d654 D_8d654.                                                         (* [comment removed for export] *)
  zstep F_8772c D_8772c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x1374b0 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_87730 D_87730 0x1374b0 C38'. zld F_87734 D_87734 (F + 144) C144'.
  zbtk F_87738 D_87738.
  stepret F_87754 D_87754 (Z_to_bv 64 0x8da70 : word) ltac:(rwH; reflexivity).
  zstep F_8d658 D_8d658.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 40) 8 0x95bf8) by zcell; assert (R2 : cellA X (s - 48) 8 (U y8)) by zcell; assert (R3 : cellA X (s - 56) 8 (U y9)) by zcell;
    assert (R4 : cellA X (s - 64) 8 (U y18)) by zcell; assert (R5 : cellA X (s - 72) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 80) 8 (U x20)) by zcell;
    assert (Q1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (Q2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (Q3 : cellA X (s - 24) 8 (U x9)) by zcell;
    assert (Q4 : cellA X (s - 32) 8 (U x18)) by zcell end.
  zld F_8d65c D_8d65c (s - 40) R1.
  zld F_8d660 D_8d660 (s - 48) R2; rewrite Z_to_bv_bv_unsigned.
  zld F_8d664 D_8d664 (s - 56) R3; rewrite Z_to_bv_bv_unsigned.
  zld F_8d668 D_8d668 (s - 64) R4; rewrite Z_to_bv_bv_unsigned.
  zld F_8d66c D_8d66c (s - 72) R5; rewrite Z_to_bv_bv_unsigned.
  zld F_8d670 D_8d670 (s - 80) R6; rewrite Z_to_bv_bv_unsigned.
  zstep F_8d674 D_8d674.                                                         (* [comment removed for export] *)
  stepret F_8d678 D_8d678 (Z_to_bv 64 0x95bf8 : word) ltac:(rwH; reflexivity).        (* [comment removed for export] *)
  zbft F_957e0 D_957e0.                                                          (* [comment removed for export] *)
  zld F_957e4 D_957e4 (s - 8) Q1; rewrite Z_to_bv_bv_unsigned.                   (* [comment removed for export] *)
  zld F_957e8 D_957e8 (s - 16) Q2; rewrite Z_to_bv_bv_unsigned.                  (* [comment removed for export] *)
  zld F_957ec D_957ec (s - 24) Q3; rewrite Z_to_bv_bv_unsigned.                  (* [comment removed for export] *)
  zld F_957f0 D_957f0 (s - 32) Q4; rewrite Z_to_bv_bv_unsigned.                  (* [comment removed for export] *)
  zstep F_957f4 D_957f4.                                                         (* [comment removed for export] *)
  stepret F_957f8 D_957f8 x1 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
