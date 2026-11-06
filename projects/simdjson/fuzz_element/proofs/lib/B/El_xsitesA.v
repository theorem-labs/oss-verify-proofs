(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface5 Sj_akit Atp_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation mem := (word -> option byte).

Definition XS_VPTR : Z := 0x173198.
Definition XS_TINFO : Z := 0x173170.
Definition XS_DTOR : Z := 0x11395c.
Definition XS_DTORGOT : Z := 0x179ab8.
Definition XS_CXA_THROW : Z := 0x1152dc.

Ltac lit_store_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?c)) _) => change (Z_to_le_bytes 8 c) with (le8 (Z_to_bv 64 c)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?c)) _) => change (Z_to_le_bytes 4 c) with (le4 (Z_to_bv 64 c)); mem_after_store
  | _ => idtac
  end.
Ltac zstepl := zstep; lit_store_fix.
Ltac chkz SZ x := chk0 SZ x; step; if_false; repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.

Ltac br_not K := if_cases K; zify_cond K; [exfalso; rewrite ?a_sx32_small, ?a_zx32_small in K by lia; rewrite ?unsigned_lit in K by lia; lia|].

Definition siteA_post (RA1 usp p : Z) (gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 S2 S3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' code : word) (m' : mem),
      ms = MS (mkR (wz RA1) (wz usp) gp tp t0 t1 t2 (wz (p + 128)) s1 a0' a1' a2' a3 a4 a5 a6 a7 S2 S3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_handle_no_return) fc None m' (seg_rom bsegs)
      /\ munch [(p + 128, p + 144)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' p [CB 128 (repeat z8 128); C8 (wz XS_VPTR); C4 code; C4 (wz 0)].

Definition siteA_walk2 (RA0 RA1 : Z) : Prop :=
  forall (usp p : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 144 < 2^47 -> p mod 16 = 0 ->
  rw_cells bsegs m p [CB 128 (repeat z8 128); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  (forall m', munch [(p + 128, p + 144)] m m' -> wmono bsegs m m' -> shz m' (p + 128) 16) -> mem_inv bsegs m ->
  evt bsegs (siteA_post RA1 usp p gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR (wz RA0) (wz usp) gp tp t0 t1 t2 s0 s1 (wz (p + 128)) a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA0) fc None m (seg_rom bsegs)).

Definition siteB_walk (RA1 RA : Z) : Prop :=
  forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  ro_cells bsegs m XS_DTORGOT [C8 (wz XS_DTOR)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => ms = MS (mkR (wz RA) sp gp tp t0 t1 t2 s0 s1 s0 (wz XS_TINFO) (wz XS_DTOR) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz XS_CXA_THROW) fc None m (seg_rom bsegs))
    (MS (mkR (wz RA1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA1) fc None m (seg_rom bsegs)).

Ltac siteA_done := apply evt_done; do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [assumption| eassumption].

Lemma siteA_b4d9c : siteA_walk2 0xb4dcc 0xb4e18.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b4d9c : siteB_walk 0xb4e18 0xb5264.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b4e2c : forall (usp p cv : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 144 < 2^47 -> p mod 16 = 0 ->
  rw_cells bsegs m p [CB 128 (repeat z8 128); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  (forall m', munch [(p + 128, p + 144)] m m' -> wmono bsegs m m' -> shz m' (p + 128) 16) -> mem_inv bsegs m ->
  rw_cells bsegs m (usp + 24) [C4 (wz cv)] -> 0 <= cv < 64 -> 0 <= usp -> usp + 80 < 2^63 ->
  evt bsegs (siteA_post 0xb4eb0 usp p gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR (wz 0xb4e5c) (wz usp) gp tp t0 t1 t2 s0 s1 (wz (p + 128)) a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0xb4e5c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI FRL CV U0 U1. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. zstep. br_not K2. zstep. zstep. br_not K4. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b4e2c : siteB_walk 0xb4eb0 0xb5264.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b4ec4 : siteA_walk2 0xb4ef4 0xb4f3c.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b4ec4 : siteB_walk 0xb4f3c 0xb5264.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b4f50 : siteA_walk2 0xb4f80 0xb4fc8.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b4f50 : siteB_walk 0xb4fc8 0xb5264.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b5018 : siteA_walk2 0xb5048 0xb5094.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b5018 : siteB_walk 0xb5094 0xb5264.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b50a8 : siteA_walk2 0xb50d8 0xb5120.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b50a8 : siteB_walk 0xb5120 0xb5264.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 7 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b51d0 : siteA_walk2 0xb5200 0xb524c.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b51d0 : siteB_walk 0xb524c 0xb5264.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 6 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b832c : siteA_walk2 0xb835c 0xb83a8.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b832c : siteB_walk 0xb83a8 0xb83c0.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 6 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b53f8 : siteA_walk2 0xb5428 0xb5474.
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. br_not K0. zstep. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstep. zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b53f8 : siteB_walk 0xb5474 0xb548c.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 6 zstep. apply evt_done. reflexivity.
Qed.

Lemma siteA_b8570 : forall (usp p cv : Z) (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 144 < 2^47 -> p mod 16 = 0 ->
  rw_cells bsegs m p [CB 128 (repeat z8 128); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  (forall m', munch [(p + 128, p + 144)] m m' -> wmono bsegs m m' -> shz m' (p + 128) 16) -> mem_inv bsegs m ->
  rw_cells bsegs m (usp + 88) [C4 (wz cv)] -> 0 <= cv < 64 -> 0 <= usp -> usp + 144 < 2^63 ->
  (forall m', munch [(p + 128, p + 144)] m m' -> wmono bsegs m m' -> shz m' (usp + 88) 4) ->
  evt bsegs (siteA_post 0xb85fc usp p gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 (wz (usp + 88)) (wz SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR (wz 0xb85a0) (wz usp) gp tp t0 t1 t2 (wz ((usp + 88) / 8 + SHB)) s1 (wz (p + 128)) a1 a2 a3 a4 a5 a6 a7 (wz (usp + 88)) (wz SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb85a0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros P0 P47 P16 BLK SZ MI FRL CV U0 U1 SZR. unfold siteA_post, e_handle_no_return, SHB, XS_VPTR in *.
  assert (PM8 : (p + 128) mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(p + 128, p + 144)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  shz_pose SZR (usp + 88). zstep. shz_norm. zstep. step. if_false. repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end. zstep. zstep. zstep. br_not K5. zstep. br_not K6. zstep. rewrite ?land7_mod, ?PM8 by lia. step. if_false. chkz SZ (p + 128). zstep. zstep. zstep. zstepl. chkz SZ (p + 136). zstepl. zstep.
  siteA_done.
Qed.
Lemma siteB_b8570 : siteB_walk 0xb85fc 0xb8614.
Proof.
  intros until m. intros G MI. unfold XS_DTORGOT, XS_DTOR, XS_TINFO, XS_CXA_THROW in *.
  do 6 zstep. apply evt_done. reflexivity.
Qed.
