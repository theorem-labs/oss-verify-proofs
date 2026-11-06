(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow R_small R_m2s I_consts RT_iface D_defs D_kit D_libiface X_atexit Fz_defs Fz_tac Fz_w2.
From OSSVerify.Proofs.openssl.punycode.lib.A Require R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Definition cz_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma wi_wA : forall (S lo : Z) (gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (lv : byte),
  stk asegs m lo (S + -128) -> 0x7fff7f800000 <= lo -> lo + 0x1000 <= S + -128 -> S < 2^63 -> mem_inv asegs m ->
  ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_cmalloc)] -> ro_cells asegs m 0x5a9ba0 [C8 (Z_to_bv 64 e_cmalloc)] ->
  rw_cells asegs m G_LATCH [C1 lv] -> bv_unsigned lv <> 0 ->
  evt asegs (fun ms => exists (m1 : mem) (jf : list byte),
      ms = entry_st (Z_to_bv 64 0x1f34d0) (Z_to_bv 64 (S + -208)) gp tp u0 u1 u2 (Z_to_bv 64 (S + -160)) (Z_to_bv 64 110)
             (Z_to_bv 64 40) (Z_to_bv 64 (bv_unsigned lv)) (Z_to_bv 64 5936256) (Z_to_bv 64 2045016) a4 a5 a6 a7
             (Z_to_bv 64 519360) (Z_to_bv 64 40) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc e_malloc m1
      /\ munch [(S + -208, S + -128)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (S + -208)
      /\ rw_cells asegs m1 (S + -160) (cz_frame s2 s1 s0 (Z_to_bv 64 0x26d8b8))
      /\ rw_cells asegs m1 (S + -208) (cm_frame jf s3 s2 (Z_to_bv 64 40) (Z_to_bv 64 (S + -128)) (Z_to_bv 64 0x1f3544)))
    (MS (mkR (Z_to_bv 64 0x26d8a4) (Z_to_bv 64 (S + -128)) gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6) F (Z_to_bv 64 0x26d8a4) fc None m (seg_rom asegs)).
Proof.
  intros until lv. intros ST LOS LO SPH MI GM GG LT LNZ.
  unfold entry_st, e_malloc, cz_frame, cm_frame, e_cmalloc, G_MALLOC_IMPL, G_LATCH in *.
  pose proof (munch_refl [(S + -208, S + -128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LVR : 0 <= bv_unsigned lv < 256) by (pose proof (bv_unsigned_in_range 8 lv) as R; unfold bv_modulus in R; cbn in R; lia).
  xs_to 0x1f3524%Z.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR. rename FR into FRZ.
  xs_to 0x1f3458%Z.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0x1c3040%Z.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRZ | exact FR].
Qed.

(* [comment removed for export] *)
Lemma wi_wB : forall (S lo p : Z) (gp tp u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 f3 f2 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jf : list byte),
  stk asegs m lo (S + -208) -> 0x7fff7f800000 <= lo -> lo + 0x1000 <= S + -208 -> S < 2^63 -> mem_inv asegs m -> 0 < p < 2^64 ->
  rw_cells asegs m (S + -208) (cm_frame jf f3 f2 (Z_to_bv 64 40) (Z_to_bv 64 (S + -128)) (Z_to_bv 64 0x1f3544)) ->
  evt asegs (fun ms =>
      ms = entry_st (Z_to_bv 64 0x1f355c) (Z_to_bv 64 (S + -160)) gp tp u0 u1 u2 (Z_to_bv 64 (S + -128)) (Z_to_bv 64 40)
             (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 40) a3 a4 a5 a6 a7 (Z_to_bv 64 p) f3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             F fc e_asan_memset m
      /\ stk asegs m lo (S + -160))
    (MS (mkR (Z_to_bv 64 0x1f34d0) (Z_to_bv 64 (S + -208)) gp tp u0 u1 u2 (Z_to_bv 64 (S + -160)) (Z_to_bv 64 110)
             (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 519360) (Z_to_bv 64 40) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x1f34d0) fc None m (seg_rom asegs)).
Proof.
  intros until jf. intros ST LOS LO SPH MI Hp FR.
  unfold entry_st, e_asan_memset, cm_frame in *.
  assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  xs_to 0x1c1e18%Z.
  release_frame FR ST (S + -160).
  apply evt_done. split; [reflexivity | exact ST].
Qed.

(* [comment removed for export] *)
Lemma wi_wC : forall (S lo p : Z) (gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 f2 f1 f0 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem),
  stk asegs m lo (S + -160) -> 0x7fff7f800000 <= lo -> lo + 0x1000 <= S + -160 -> S < 2^63 -> mem_inv asegs m ->
  rw_cells asegs m (S + -160) (cz_frame f2 f1 f0 (Z_to_bv 64 0x26d8b8)) ->
  evt asegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x26d8b8) (Z_to_bv 64 (S + -128)) gp tp u0 u1 u2 f0 f1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 f2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x26d8b8) fc None m (seg_rom asegs)
      /\ stk asegs m lo (S + -128))
    (MS (mkR (Z_to_bv 64 0x1f355c) (Z_to_bv 64 (S + -160)) gp tp u0 u1 u2 (Z_to_bv 64 (S + -128)) (Z_to_bv 64 40)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x1f355c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LOS LO SPH MI FR.
  unfold cz_frame in *.
  xs_to 0x26d8b8%Z.
  release_frame FR ST (S + -128).
  apply evt_done. split; [reflexivity | exact ST].
Qed.
