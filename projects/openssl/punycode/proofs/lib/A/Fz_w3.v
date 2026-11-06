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
Lemma fz_wC : forall (usp spa lo n d FB b : Z) (gp tp u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jf : list byte),
  stk asegs m lo (spa + -48) -> 0x7fff7f800000 <= lo -> lo + 0x1000 <= spa -> spa < 2^63 -> 0 <= usp < 2^63 ->
  mem_inv asegs m -> 0 < b < 2^64 -> 0 <= n < 2^26 -> 0 <= d < 2^64 -> 0 <= FB -> FB + 256 < 2^63 ->
  rw_cells asegs m (spa + -48) (cm_frame jf (Z_to_bv 64 n) (Z_to_bv 64 FB) (Z_to_bv 64 spa) (Z_to_bv 64 usp) (Z_to_bv 64 0x1f3244)) ->
  evt asegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x1f3264) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa)
                 (Z_to_bv 64 d) (Z_to_bv 64 n) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128)) a4 a5 a6 a7 (Z_to_bv 64 FB) (Z_to_bv 64 n)
                 (Z_to_bv 64 d) (Z_to_bv 64 b) (Z_to_bv 64 (shad FB)) (Z_to_bv 64 FB) (Z_to_bv 64 SHB) (Z_to_bv 64 (-8)) s10 s11 u3 u4 u5 u6)
              F (Z_to_bv 64 e_decode) fc None m (seg_rom asegs)
      /\ stk asegs m lo spa)
    (MS (mkR (Z_to_bv 64 0x1f34d0) (Z_to_bv 64 (spa + -48)) gp tp u0 u1 u2 (Z_to_bv 64 spa) (Z_to_bv 64 29)
          (Z_to_bv 64 b) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 299232) (Z_to_bv 64 (n + 1)) (Z_to_bv 64 d) s5 (Z_to_bv 64 (shad FB))
          (Z_to_bv 64 FB) (Z_to_bv 64 SHB) (Z_to_bv 64 (-8)) s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x1f34d0) fc None m (seg_rom asegs)).
Proof.
  intros until jf. intros ST LOS LO SPH USP MI Hb Hn Hd HF0 HF1 FR.
  unfold cm_frame in *.
  assert (EB : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  xs_to 0x407b38%Z.
  release_frame FR ST spa.
  apply evt_done. split; [reflexivity | exact ST].
Qed.

(* [comment removed for export] *)
Lemma fz_wD : forall (spa n d b : Z) (gp tp u0 u1 u2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem),
  evt asegs (fun ms =>
      ms = entry_st (Z_to_bv 64 0x1f3274) (Z_to_bv 64 spa) gp tp u0 u1 u2 s0 (Z_to_bv 64 spa) (Z_to_bv 64 b) (Z_to_bv 64 d) (Z_to_bv 64 n)
             a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 b) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc e_asan_memcpy m)
    (MS (mkR (Z_to_bv 64 0x1f3264) (Z_to_bv 64 spa) gp tp u0 u1 u2 s0 (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n)
             (Z_to_bv 64 d) (Z_to_bv 64 b) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x1f3264) fc None m (seg_rom asegs)).
Proof.
  intros. unfold entry_st, e_asan_memcpy. xs_to 0x1c197c%Z. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition a2u_frame (jl : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (Z_to_bv 64 0); CB 112 jl; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma fz_wE : forall (usp spa lo n d b FB : Z) (gp tp u0 u1 u2 a0 a3 a4 a5 a6 a7 s6 s9 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem),
  stk asegs m lo spa -> 0x7fff7f800000 <= lo -> lo + 0x1000 <= spa -> spa < 2^63 -> spa mod 32 = 0 -> 0 <= usp < 2^63 ->
  client_consts m -> mem_inv asegs m -> 0 <= FB -> FB + 256 < 2^63 -> 0 < b < 2^63 ->
  evt asegs (fun ms => exists (m1 : mem) (jl : list byte),
      ms = entry_st (Z_to_bv 64 0x408044) (Z_to_bv 64 (spa + -224)) gp tp u0 u1 u2 (Z_to_bv 64 spa) (Z_to_bv 64 (spa + -224))
             (Z_to_bv 64 2368) (Z_to_bv 64 6753080) (Z_to_bv 64 1) a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) (Z_to_bv 64 n) (Z_to_bv 64 d)
             (Z_to_bv 64 b) (Z_to_bv 64 16) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 SHB) (Z_to_bv 64 b) s10 s11 u3 u4 u5 u6
             F fc e_stack_malloc_6 m1
      /\ munch [(spa + -224, spa)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (spa + -224)
      /\ rw_cells asegs m1 (spa + -224)
           (a2u_frame jl s11 s10 s9 (Z_to_bv 64 SHB) (Z_to_bv 64 FB) s6 (Z_to_bv 64 b) (Z_to_bv 64 d) (Z_to_bv 64 n) (Z_to_bv 64 FB)
                      (Z_to_bv 64 spa) (Z_to_bv 64 usp) (Z_to_bv 64 0x1f32a0)))
    (MS (mkR (Z_to_bv 64 0x1f3274) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 16)
             a3 a4 a5 a6 a7 (Z_to_bv 64 FB) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 b) s6 (Z_to_bv 64 FB) (Z_to_bv 64 SHB) s9 s10 s11
             u3 u4 u5 u6) F (Z_to_bv 64 0x1f3294) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LOS LO SPH S32 USP CC MI HF0 HF1 Hb.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_stack_malloc_6, a2u_frame, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return in *.
  assert (ES : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; lia).
  pose proof (wmono_refl asegs m) as WM.
  xs_to 0x407fc4%Z.
  pose proof (munch_refl [(spa + -224, spa)] m) as MU.
  carve_frame 224%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 224 _ [] [8;112;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 16 xs. xs. rewrite (land_m32_al (spa + -224)) by (try lia; Z.div_mod_to_equations; lia).
  xs_to 0x1a6ef0%Z.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.
