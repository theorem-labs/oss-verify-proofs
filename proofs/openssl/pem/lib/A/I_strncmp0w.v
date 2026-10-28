(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit I_pck D_kit I_strncmpw I_strncmpw3 I_strncmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma istrncmp0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : Z) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 <= p1 < 2^64 -> 0 <= p2 < 2^64 -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ad0c8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO SPH P1 P2 IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  call (isc_prologue usp p1 p2 0); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icells_sc mm)
      by (apply (icells_sc_agree m mm IC); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                          | exact WM]) end.
  pose proof IC1 as (G70 & G2 & SHC & AI & SSC). clear IC1.
  call asan_inited_spec; [exact AI| assumption|].
  xsteps_to 0x1ca818%Z.
  call I_ikit.try_init_spec; [exact AI| rewrite EU2176; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2176 in H; rename H into ST2 end.
  assert (EUp1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  assert (EUp2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  assert (EUnp1 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p1)) = 18446744073709551615 - p1) by (apply unsigned_lit; lia).
  assert (EUnp2 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p2)) = 18446744073709551615 - p2) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  lstep. if_false. lstep. if_true.
  (* [comment removed for export] *)
  do 5 lstep. lstep. if_true.
  (* [comment removed for export] *)
  lstep. lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_true.
  (* [comment removed for export] *)
  lstep. lstep. lstep. if_true. lstep. if_false. lstep.
  (* [comment removed for export] *)
  lstep. lstep. if_true. lstep. lstep. rewrite (lxor_ones64 p2) by lia. lstep. if_true.
  (* [comment removed for export] *)
  lstep. lstep. lstep. if_true. lstep. if_false. lstep.
  (* [comment removed for export] *)
  do 3 lstep.
  do 23 lstep.
  release_frame FR ST2 (usp + -104). release_frame FRs ST2 usp.
  lstep.
  unfold istrncmp_post. sys_finish.
  + rewrite (unsigned_lit usp) by lia. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite (unsigned_lit usp) by lia. assumption.
Qed.
