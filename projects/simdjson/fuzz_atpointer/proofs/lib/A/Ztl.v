(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd Zsl Zqa Zq7 Zt5 Ztr Ztu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section NDB.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 160 - d)%Z.
  Hypothesis ROOM : (lo + NDCA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x669000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x669000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= S \/ S + 128 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 128 <= X / 8 + 2147450880))%Z.
  Variable Q : machine_state -> Prop.
  Collection NDH := SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP.
  Notation NDINV := (nd_inv X spq f m0).

  Notation NDS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac nd_env :=
    destruct SPQ as [Hd Hspq]; unfold NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let F8 := fresh "F8" in pose proof (f64_8 f F64) as F8;
    let F32 := fresh "F32" in assert (F32 : ((f + 32) / 8 = f / 8 + 4)%Z) by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; apply f64_div; exact F64).

  Notation WNA := [(spq, spq + 56); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.

  Definition nd_a_mset_k (xs8 : word) : Prop :=
    forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs9 xt3 xt4 xt5 xt6 j0 j8 j16 j32 j40 (mm : mem),
      rw_cells asegs mm spq [CB 8 j0; CB 8 j8; CB 8 j16; C8 xs5; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f)] ->
      rw_cells asegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] ->
      mem_inv asegs mm -> munch WNA m0 mm -> wmono asegs m0 mm ->
      evt asegs Q (NDS 0x66b58 (Z_to_bv 64 0xc8f0c) xt0 xt1 xt2 (Z_to_bv 64 (f + 40)) (Z_to_bv 64 0) (Z_to_bv 64 496) xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 X) xs6
                       (Z_to_bv 64 (f + 32)) xs8 xs9 xt3 xt4 xt5 xt6 mm).

  Lemma nd_a : forall xs8, nd_a_mset_k xs8 ->
    forall xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs7 xs9 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j40 j48 jz (mm : mem),
    rw_cells asegs mm spq [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] ->
    rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    mem_inv asegs mm -> munch WNA m0 mm -> wmono asegs m0 mm ->
    evt asegs Q (NDS 0xc8d4c xra xt0 xt1 xt2 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) xa3 xa4 xa5 xa6 xa7 xs3 xs5 (Z_to_bv 64 X) xs7 xs8 xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH.
    intros xs8 KMS. intros until mm. intros SPILL TSH MI MU WM. nd_env.
    assert (DM3 : IsData xs3) by exact I. assert (DM5 : IsData xs5) by exact I.
    assert (KC0 : forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys9 yt3 yt4 yt5 yt6 (mm' : mem),
              rw_cells asegs mm' spq [CB 8 j0; CB 8 j8; CB 8 j16; C8 xs5; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f)] ->
              rw_cells asegs mm' (f / 8 + 2147450884) [CB 63 jz] -> mem_inv asegs mm' -> munch WNA m0 mm' -> wmono asegs m0 mm' ->
              evt asegs Q (NDS 0xc8dfc yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs3 (Z_to_bv 64 X) (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) xs8 ys9 yt3 yt4 yt5 yt6 mm')).
    { clear SPILL TSH MI MU WM. intros until mm'. intros SPILL TSH MI MU WM.
      num_cur_mem ltac:(fun m1 => eapply (nd_run1 f m1 ltac:(lia) Q); [exact TSH | exact MI | apply munch_refl | apply wmono_refl |];
        clear MI TSH; intros mm2 TSH MI MU' WM'; transport_after_call asegs m1 mm2 MU' WM'; clear MU' WM').
      awalk ltac:(fun pc => lazymatch pc with
        | 0x66b58%Z => first [ unfold nd_a_mset_k in KMS; eapply evt_eq; [| eapply KMS; eassumption]; num_st_eq | fail 100 "cut" pc ]
        end). }
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc8dfc%Z => first [ eapply evt_eq; [| eapply KC0; eassumption]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End NDB.
