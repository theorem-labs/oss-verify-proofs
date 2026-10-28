(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_W7_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition J_w7_fpart : Z := 0x1f32d0.
(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.
(* [comment removed for export] *)
Definition w7_mframe3 (pd f : Z) (j1 j2 j3 j4 j5 j6 : list byte) : cell * cell * cell * cell * cell * cell * cell :=
  if pd =? 0 then (C8 (Z_to_bv 64 0), CB 8 j1, C8 (Z_to_bv 64 (f + 96)), C8 (Z_to_bv 64 (f + 64)), CB 8 j4, CB 8 j5, C8 (Z_to_bv 64 f))
  else (C8 (Z_to_bv 64 (f + 96)), C8 (Z_to_bv 64 (f + 64)), CB 8 j2, CB 8 j3, C8 (Z_to_bv 64 f), CB 8 j5, CB 8 j6).

(* [comment removed for export] *)
Definition w7_regs (ra : word) (sp : word) (gp tp t0 t1 t2 : word) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (s9 : word) (t3 t4 t5 t6 : word) (buf BI f pd : Z) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
      a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 buf) (Z_to_bv 64 BI) (Z_to_bv 64 (buf / 8 + 2147450880)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) s9
      (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w7_p0f_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf BI f pd ret : Z),
  0 <= ret < 2 ^ 32 -> ret <> 1 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regs (Z_to_bv 64 SITE_w7_pem) sp gp tp t0 t1 t2 (Z_to_bv 64 ret) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 J_w7_fpart) fc None m (seg_rom asegs))
    (MS (w7_regs (Z_to_bv 64 SITE_w7_pem) sp gp tp t0 t1 t2 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 SITE_w7_pem) fc None m (seg_rom asegs)).
Proof.
  intros until ret. intros RR RNE MI. unfold w7_regs, SITE_w7_pem, J_w7_fpart in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w7_p0_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
    (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd NM : Z) (j1 j2 j3 j4 j5 j6 : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> 0xbc6000 <= f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  (let '(c1, c2, c3, c4, c5, c6) := w7_mframe2 pd f j1 j2 j3 j4 j5 j6 in
   rw_cells asegs m (bv_unsigned sp + -160) (w7_mframe c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 NM)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists m',
       let '(c0, c1, c2, c3, c4, c5, c6) := w7_mframe3 pd f j1 j2 j3 j4 j5 j6 in
       ms = MS (w7_regs (Z_to_bv 64 SITE_w7_slen1) sp gp tp t0 t1 t2 (Z_to_bv 64 NM) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 NM) t3 t4 t5 t6 buf BI f pd)
               F (Z_to_bv 64 e_strlen) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 160, bv_unsigned sp - 136)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -160) (w7_mframe7 c0 c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)
       /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160))
    (MS (w7_regs (Z_to_bv 64 SITE_w7_pem) sp gp tp t0 t1 t2 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 SITE_w7_pem) fc None m (seg_rom asegs)).
Proof.
  intros until j6. intros HP F0 FIMG FLO HLO HLOS SPH FR GAP NMC MI. unfold w7_regs, SITE_w7_pem, SITE_w7_slen1 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 160, SP - 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  unfold w7_mframe2, w7_mframe, w7_mframe7 in FR.
  destruct HP as [-> | ->]; cbn [Z.eqb] in FR.
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  (* [comment removed for export] *)
  all: zstep; zstep; if_false.
  all: zstep. all: zstep. all: zstep. all: zstep.
  all: subst SP; unfold w7_mframe3, w7_mframe7; cbn [Z.eqb].
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w7_p1_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf BI f pd NM n1 : Z),
  0 <= n1 < 2 ^ 31 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regs (Z_to_bv 64 SITE_w7_write2) sp gp tp t0 t1 t2 (Z_to_bv 64 BI) (Z_to_bv 64 NM) (Z_to_bv 64 n1) a3 a4 a5 a6 a7 (Z_to_bv 64 NM) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 A_BIO_write) fc None m (seg_rom asegs))
    (MS (w7_regs (Z_to_bv 64 SITE_w7_slen1) sp gp tp t0 t1 t2 (Z_to_bv 64 n1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 NM) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 SITE_w7_slen1) fc None m (seg_rom asegs)).
Proof.
  intros until n1. intros N1 MI. unfold w7_regs, SITE_w7_slen1, SITE_w7_write2, A_BIO_write in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. rewrite Z.add_0_r, (swrap32_small n1) by lia. zstep. zstep. zstep.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w7_p2_walk : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
    (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd HD : Z) (j1 j2 j3 j4 j5 j6 : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> 0xbc6000 <= f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  (let '(c0, c1, c2, c3, c4, c5, c6) := w7_mframe3 pd f j1 j2 j3 j4 j5 j6 in
   rw_cells asegs m (bv_unsigned sp + -160) (w7_mframe7 c0 c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)) ->
  rw_cells asegs m (f + 64) [C8 (Z_to_bv 64 HD)] -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regs (Z_to_bv 64 SITE_w7_slen2) sp gp tp t0 t1 t2 (Z_to_bv 64 HD) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 HD) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 e_strlen) fc None m (seg_rom asegs))
    (MS (w7_regs (Z_to_bv 64 SITE_w7_write2) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 SITE_w7_write2) fc None m (seg_rom asegs)).
Proof.
  intros until j6. intros HP F0 FIMG FLO HLO HLOS SPH FR HDC MI. unfold w7_regs, SITE_w7_write2, SITE_w7_slen2 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  unfold w7_mframe3, w7_mframe7 in FR.
  destruct HP as [-> | ->]; cbn [Z.eqb] in FR.
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep.
  all: subst SP.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w7_p3_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
    (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd HD n2 : Z) (j1 j2 j3 j4 j5 j6 : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> 0 <= n2 < 2 ^ 31 ->
  (let '(c0, c1, c2, c3, c4, c5, c6) := w7_mframe3 pd f j1 j2 j3 j4 j5 j6 in
   rw_cells asegs m (bv_unsigned sp + -160) (w7_mframe7 c0 c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regs (Z_to_bv 64 SITE_w7_write3) sp gp tp t0 t1 t2 (Z_to_bv 64 BI) (Z_to_bv 64 HD) (Z_to_bv 64 n2) a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 A_BIO_write) fc None m (seg_rom asegs))
    (MS (w7_regs (Z_to_bv 64 SITE_w7_slen2) sp gp tp t0 t1 t2 (Z_to_bv 64 n2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 HD) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 SITE_w7_slen2) fc None m (seg_rom asegs)).
Proof.
  intros until j6. intros HP F0 FLO HLO HLOS SPH N2 FR MI. unfold w7_regs, SITE_w7_slen2, SITE_w7_write3, A_BIO_write in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold w7_mframe3, w7_mframe7 in FR.
  destruct HP as [-> | ->]; cbn [Z.eqb] in FR.
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  (* [comment removed for export] *)
  all: zstep; rewrite Z.add_0_r, (swrap32_small n2) by lia.
  all: zstep; zstep; zstep; zstep.
  all: subst SP.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w7_p4_walk : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd DT dlen : Z),
  0 < f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> 0 <= dlen < 2 ^ 31 ->
  rw_cells asegs m (f + 96) [C8 (Z_to_bv 64 DT)] -> rw_cells asegs m (f + 128) [C8 (Z_to_bv 64 dlen)] -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regs (Z_to_bv 64 SITE_w7_write4) sp gp tp t0 t1 t2 (Z_to_bv 64 BI) (Z_to_bv 64 DT) (Z_to_bv 64 dlen) a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 A_BIO_write) fc None m (seg_rom asegs))
    (MS (w7_regs (Z_to_bv 64 SITE_w7_write3) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 SITE_w7_write3) fc None m (seg_rom asegs)).
Proof.
  intros until dlen. intros F0 FLO HLO HLOS SPH DL DTC OLC MI. unfold w7_regs, SITE_w7_write3, SITE_w7_write4, A_BIO_write in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof OLC as OL4. replace dlen with (dlen + 2 ^ 32 * 0) in OL4 by (clear; lia).
  apply (proj2 (t_cells_halves asegs m _ dlen 0 ltac:(clear - DL; lia) ltac:(clear; lia))) in OL4.
  (* [comment removed for export] *)
  zstep. zstep. rewrite (sx32_small dlen) by lia. zstep. zstep.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w7_regsF (ra : word) (sp : word) (gp tp t0 t1 t2 : word) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (s9 : word) (t3 t4 t5 t6 : word) (buf BI f pd : Z) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
      a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 W7_FILE) (Z_to_bv 64 BI) (Z_to_bv 64 (buf / 8 + 2147450880)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) s9
      (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6.

Lemma w7_f0_walk : forall (ra : word) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (b0 : byte) (bsr : list byte) (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd p n NM : Z),
  0 < f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < p -> p <= buf -> buf + 1 <= p + n -> p + n <= lo -> acc asegs m p n -> bytes_at asegs m buf (b0 :: bsr) ->
  rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 NM)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
       ms = MS (w7_regsF (Z_to_bv 64 (if Z.odd (bv_unsigned b0) then SITE_w7_sfree1 else SITE_w7_free1)) sp gp tp t0 t1 t2 (Z_to_bv 64 NM) (Z_to_bv 64 W7_FILE)
                  (Z_to_bv 64 (if Z.odd (bv_unsigned b0) then 50 else 54)) a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
               F (Z_to_bv 64 (if Z.odd (bv_unsigned b0) then A_CRYPTO_secure_free else A_CRYPTO_free)) fc None m (seg_rom asegs))
    (MS (w7_regs ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 J_w7_fpart) fc None m (seg_rom asegs)).
Proof.
  intros until NM. intros F0 FLO HLO HLOS SPH P0 PB BP PN ACC BS NMC MI. unfold w7_regs, w7_regsF, SITE_w7_write4, J_w7_fpart in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  pose proof (bytes_at_read asegs m buf (b0 :: bsr) 0 1 BS ltac:(lia) ltac:(cbn; lia)) as RD.
  replace (firstn 1 (skipn (Z.to_nat 0) (b0 :: bsr))) with [b0] in RD by reflexivity. replace (buf + 0) with buf in RD by lia.
  destruct (ACC (buf - p) ltac:(lia)) as (sb & SHB0 & SOK). replace (p + (buf - p)) with buf in SHB0, SOK by lia. unfold shad, SHB in SHB0. unfold sh_ok in SOK.
  pose proof (bytes_at_read asegs m (buf / 8 + 2147450880) [sb] 0 1 SHB0 ltac:(lia) ltac:(cbn; lia)) as RDs.
  replace (firstn 1 (skipn (Z.to_nat 0) [sb])) with [sb] in RDs by reflexivity. replace (buf / 8 + 2147450880 + 0) with (buf / 8 + 2147450880) in RDs by lia.
  pose proof (bv_unsigned_in_range 8 sb) as SBR. unfold bv_modulus in SBR. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul] in SBR.
  pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul] in B0R.
  assert (L7 : Z.land buf 7 = buf mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  assert (L1 : Z.land (bv_unsigned b0) 1 = bv_unsigned b0 mod 2) by (change 1 with (Z.ones 1) at 1; rewrite Z.land_ones by lia; reflexivity).
  (* [comment removed for export] *)
  zstep; rewrite (sxb_small sb) by (clear - SOK SBR; lia).
  zstep; if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by (clear - SBR; lia);
    [zstep; zstep; if_cases KT; zify_cond KT;
     [| exfalso; rewrite L7, !bv_signed_small in KT by (rewrite unsigned_lit by (clear - SBR EUb; Z.div_mod_to_equations; lia); clear - SBR EUb; Z.div_mod_to_equations; lia);
        rewrite !unsigned_lit in KT by (clear - SBR EUb; Z.div_mod_to_equations; lia); clear - KS KT SOK; lia] |].
  all: zstep; zstep; zstep.
  all: zstep; if_cases KB; zify_cond KB; unfold zxb in KB; rewrite ?unsigned_lit, ?L1 in KB by (clear - B0R; rewrite ?unsigned_lit; lia).
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; zstep.
  all: unfold W7_FILE, SITE_w7_sfree1, SITE_w7_free1, A_CRYPTO_secure_free, A_CRYPTO_free.
  all: first [ replace (Z.odd (bv_unsigned b0)) with true by (symmetry; apply Z.odd_spec; clear - KB B0R; Z.div_mod_to_equations; exists q; lia)
             | replace (Z.odd (bv_unsigned b0)) with false by (symmetry; rewrite <- Z.negb_even, Bool.negb_false_iff; apply Z.even_spec; clear - KB B0R; Z.div_mod_to_equations; exists q; lia) ].
  all: apply evt_done; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w7_free_entry (sec : bool) : Z := if sec then A_CRYPTO_secure_free else A_CRYPTO_free.

Lemma w7_f1_walk : forall (sec : bool) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
    (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd HD : Z) (j1 j2 j3 j4 j5 j6 : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  (let '(c0, c1, c2, c3, c4, c5, c6) := w7_mframe3 pd f j1 j2 j3 j4 j5 j6 in
   rw_cells asegs m (bv_unsigned sp + -160) (w7_mframe7 c0 c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)) ->
  rw_cells asegs m (f + 64) [C8 (Z_to_bv 64 HD)] -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsF (Z_to_bv 64 (if sec then SITE_w7_sfree2 else SITE_w7_free2)) sp gp tp t0 t1 t2 (Z_to_bv 64 HD) (Z_to_bv 64 W7_FILE)
                                         (Z_to_bv 64 (if sec then 51 else 55)) a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 (w7_free_entry sec)) fc None m (seg_rom asegs))
    (MS (w7_regsF (Z_to_bv 64 (if sec then SITE_w7_sfree1 else SITE_w7_free1)) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 (if sec then SITE_w7_sfree1 else SITE_w7_free1)) fc None m (seg_rom asegs)).
Proof.
  intros until j6. intros HP F0 FLO HLO HLOS SPH FR HDC MI. unfold w7_regsF, w7_free_entry, SITE_w7_sfree1, SITE_w7_free1, SITE_w7_sfree2, SITE_w7_free2, A_CRYPTO_secure_free, A_CRYPTO_free, W7_FILE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  unfold w7_mframe3, w7_mframe7 in FR.
  destruct sec; destruct HP as [-> | ->]; cbn [Z.eqb] in FR.
  all: try replace (SP + -160 - 0) with (SP + -160) in * by lia.
  all: try replace (SP + -160 - 16) with (SP + -176) in * by lia.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; zstep.
  all: subst SP.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; reflexivity.
Qed.

Lemma w7_f2_walk : forall (sec : bool) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd DT : Z),
  0 < f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (f + 96) [C8 (Z_to_bv 64 DT)] -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsF (Z_to_bv 64 (if sec then SITE_w7_sfree3 else SITE_w7_free3)) sp gp tp t0 t1 t2 (Z_to_bv 64 DT) (Z_to_bv 64 W7_FILE)
                                         (Z_to_bv 64 (if sec then 52 else 56)) a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 (w7_free_entry sec)) fc None m (seg_rom asegs))
    (MS (w7_regsF (Z_to_bv 64 (if sec then SITE_w7_sfree2 else SITE_w7_free2)) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 (if sec then SITE_w7_sfree2 else SITE_w7_free2)) fc None m (seg_rom asegs)).
Proof.
  intros until DT. intros F0 FLO HLO HLOS SPH DTC MI. unfold w7_regsF, w7_free_entry, SITE_w7_sfree2, SITE_w7_free2, SITE_w7_sfree3, SITE_w7_free3, A_CRYPTO_secure_free, A_CRYPTO_free, W7_FILE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  destruct sec.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep.
  all: apply evt_done; reflexivity.
Qed.

Lemma w7_f3_walk : forall (sec : bool) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf BI f pd : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsF (Z_to_bv 64 SITE_w7_bfree) sp gp tp t0 t1 t2 (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 A_BIO_free) fc None m (seg_rom asegs))
    (MS (w7_regsF (Z_to_bv 64 (if sec then SITE_w7_sfree3 else SITE_w7_free3)) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 (if sec then SITE_w7_sfree3 else SITE_w7_free3)) fc None m (seg_rom asegs)).
Proof.
  intros until pd. intros MI. unfold w7_regsF, SITE_w7_sfree3, SITE_w7_free3, SITE_w7_bfree, A_BIO_free in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct sec.
  (* [comment removed for export] *)
  2: zstep.
  all: zstep; zstep.
  all: apply evt_done; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w7_b_walk : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf BI f pd : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsF (Z_to_bv 64 J_w7_exit) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 A_ERR_clear_error) fc None m (seg_rom asegs))
    (MS (w7_regsF (Z_to_bv 64 SITE_w7_bfree) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 SITE_w7_bfree) fc None m (seg_rom asegs)).
Proof.
  intros until pd. intros MI. unfold w7_regsF, SITE_w7_bfree, J_w7_exit, A_ERR_clear_error in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w7_regsE (ra : word) (sp : word) (gp tp t0 t1 t2 : word) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (s4 s5 s8 s9 : word) (t3 t4 t5 t6 : word) (buf f pd : Z) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
      a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 buf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 0x7fff8000) s8 s9
      (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6.

Lemma w7_lx_walk : forall sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s8 s9 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf f pd len : Z),
  0 <= len < 2 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsE (Z_to_bv 64 SITE_w7_smalloc) sp gp tp t0 t1 t2 (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646)) a2 a3 a4 a5 a6 a7
                                          s4 (Z_to_bv 64 len) s8 s9 t3 t4 t5 t6 buf f pd)
                              F (Z_to_bv 64 J_w7_exit) fc None m (seg_rom asegs))
    (MS (w7_regsE (Z_to_bv 64 SITE_w7_smalloc) sp gp tp t0 t1 t2 (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646)) a2 a3 a4 a5 a6 a7
                  s4 (Z_to_bv 64 len) s8 s9 t3 t4 t5 t6 buf f pd)
        F (Z_to_bv 64 J_w7_lentest) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros LEN MI. unfold w7_regsE, SITE_w7_smalloc, J_w7_lentest, J_w7_exit in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K; zify_cond K; [| exfalso; generalize K LEN; clear; intros K LEN; change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia; Z.div_mod_to_equations; lia].
  apply evt_done. reflexivity.
Qed.

Lemma w7_lc_walk : forall sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s8 s9 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf f pd len : Z),
  2 <= len < 2 ^ 31 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsE (Z_to_bv 64 SITE_w7_smem) sp gp tp t0 t1 t2 (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646)) a2 a3 a4 a5 a6 a7
                                          s4 (Z_to_bv 64 len) s8 s9 t3 t4 t5 t6 buf f pd)
                              F (Z_to_bv 64 A_BIO_s_mem) fc None m (seg_rom asegs))
    (MS (w7_regsE (Z_to_bv 64 SITE_w7_smalloc) sp gp tp t0 t1 t2 (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646)) a2 a3 a4 a5 a6 a7
                  s4 (Z_to_bv 64 len) s8 s9 t3 t4 t5 t6 buf f pd)
        F (Z_to_bv 64 J_w7_lentest) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros LEN MI. unfold w7_regsE, SITE_w7_smalloc, SITE_w7_smem, J_w7_lentest, A_BIO_s_mem in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K; zify_cond K; [exfalso; generalize K LEN; clear; intros K LEN; change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia; Z.div_mod_to_equations; lia|].
  (* [comment removed for export] *)
  zstep. apply evt_done. reflexivity.
Qed.

Lemma w7_n0_walk : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf f pd len : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsE (Z_to_bv 64 SITE_w7_bnew) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 len) s8 s9 t3 t4 t5 t6 buf f pd)
                              F (Z_to_bv 64 A_BIO_new) fc None m (seg_rom asegs))
    (MS (w7_regsE (Z_to_bv 64 SITE_w7_smem) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 len) s8 s9 t3 t4 t5 t6 buf f pd)
        F (Z_to_bv 64 SITE_w7_smem) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros MI. unfold w7_regsE, SITE_w7_smem, SITE_w7_bnew, A_BIO_new in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. apply evt_done. reflexivity.
Qed.

Lemma w7_n1_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf f lo pd len BI : Z),
  0 < BI -> BI + 128 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> 2 <= len < 2 ^ 31 -> 0 < buf -> buf + 1 < 2 ^ 64 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsE (Z_to_bv 64 SITE_w7_write1) sp gp tp t0 t1 t2 (Z_to_bv 64 BI) (Z_to_bv 64 (buf + 1)) (Z_to_bv 64 (len + -1)) a3 a4 a5 a6 a7
                                          (Z_to_bv 64 BI) (Z_to_bv 64 (len + -1)) s8 s9 t3 t4 t5 t6 buf f pd)
                              F (Z_to_bv 64 A_BIO_write) fc None m (seg_rom asegs))
    (MS (w7_regsE (Z_to_bv 64 SITE_w7_bnew) sp gp tp t0 t1 t2 (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 len) s8 s9 t3 t4 t5 t6 buf f pd)
        F (Z_to_bv 64 SITE_w7_bnew) fc None m (seg_rom asegs)).
Proof.
  intros until BI. intros B0 BLO HLO HLOS SPH LEN BUF0 BUFH MI. unfold w7_regsE, SITE_w7_bnew, SITE_w7_write1, A_BIO_write in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
  zstep. zstep.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  apply evt_done. reflexivity.
Qed.
