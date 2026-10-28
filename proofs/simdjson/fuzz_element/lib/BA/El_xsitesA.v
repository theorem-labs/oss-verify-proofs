(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation mem := (word -> option byte).

Definition XS_VPTR : Z := 0x164598.
Definition XS_TINFO : Z := 0x164570.
Definition XS_DTOR : Z := 0x104dd0.
Definition XS_DTORGOT : Z := 0x16aeb8.
Definition XS_CXA_THROW : Z := 0x106750.

Ltac lit_store_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?c)) _) => change (Z_to_le_bytes 8 c) with (le8 (Z_to_bv 64 c)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?c)) _) => change (Z_to_le_bytes 4 c) with (le4 (Z_to_bv 64 c)); mem_after_store
  | _ => idtac
  end.
Ltac zstepl := zstep; lit_store_fix.
Ltac chkz SZ x := chk0 SZ x; step; if_false; repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.

Definition siteA_post (RA1 usp p : Z) (gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 S2 S3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' code : word) (m' : mem),
      ms = MS (mkR (wz RA1) (wz usp) gp tp t0 t1 t2 (wz (p + 128)) s1 a0' a1' a2' a3 a4 a5 a6 a7 S2 S3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_handle_no_return) fc None m' (seg_rom asegs)
      /\ munch [(p + 128, p + 144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' p [CB 128 (repeat z8 128); C8 (wz XS_VPTR); C4 code; C4 (wz 0)].

Definition siteA_walk2 (RA0 RA1 : Z) : Prop :=
  forall (usp p : Z) (gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 144 < 2^47 -> p mod 16 = 0 ->
  rw_cells asegs m p [CB 128 (repeat z8 128); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  (forall m', munch [(p + 128, p + 144)] m m' -> wmono asegs m m' -> shz m' (p + 128) 16) -> mem_inv asegs m ->
  evt asegs (siteA_post RA1 usp p gp tp t0 t1 t2 (wz SHB) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR (wz RA0) (wz usp) gp tp t0 t1 t2 s0 (wz SHB) (wz (p + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA0) fc None m (seg_rom asegs)).

Definition siteB_walk (RA1 RA : Z) : Prop :=
  forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  ro_cells asegs m XS_DTORGOT [C8 (wz XS_DTOR)] -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz RA) sp gp tp t0 t1 t2 s0 s1 s0 (wz XS_TINFO) (wz XS_DTOR) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz XS_CXA_THROW) fc None m (seg_rom asegs))
    (MS (mkR (wz RA1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA1) fc None m (seg_rom asegs)).

Ltac siteA_done := apply evt_done; do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [assumption| eassumption].

Lemma siteA_b272c : siteA_walk2 0xb2734 0xb2780.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstep. zstep. zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b272c : siteB_walk 0xb2780 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b27f8 : siteA_walk2 0xb2800 0xb2840.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b27f8 : siteB_walk 0xb2840 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b29e8 : siteA_walk2 0xb29f0 0xb2a30.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b29e8 : siteB_walk 0xb2a30 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b2ac4 : siteA_walk2 0xb2acc 0xb2b0c.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b2ac4 : siteB_walk 0xb2b0c 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b2b84 : siteA_walk2 0xb2b8c 0xb2bcc.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b2b84 : siteB_walk 0xb2bcc 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b2c64 : siteA_walk2 0xb2c6c 0xb2ca8.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b2c64 : siteB_walk 0xb2ca8 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b2cc0 : siteA_walk2 0xb2cc8 0xb2d04.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b2cc0 : siteB_walk 0xb2d04 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 6 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b2d2c : siteA_walk2 0xb2d34 0xb2d74.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b2d2c : siteB_walk 0xb2d74 0xb2d1c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b2fb4 : siteA_walk2 0xb2fbc 0xb2ffc.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b2fb4 : siteB_walk 0xb2ffc 0xb3014.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 6 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b3170 : siteA_walk2 0xb3178 0xb31b8.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b3170 : siteB_walk 0xb31b8 0xb31d0.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 6 zstep. apply evt_done. reflexivity.
Qed.
