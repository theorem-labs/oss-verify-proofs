(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_lm_runs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMLX.
  Variables (X lo : Z) (m0 : mem).
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6c1000 <= X /\ X + 504 <= lo /\ lo < 2^62)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Variable Q : machine_state -> Prop.
  Notation WX := [(X, X + 496)]%Z.

  Lemma lm_mulx : forall (fuel : nat) (i n : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc xbs (mm : mem),
    u8arr asegs mm X xbs -> length xbs = 496%nat ->
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    mem_inv asegs mm -> munch WX m0 mm -> wmono asegs m0 mm ->
    (0 <= i < n)%Z -> (n <= 62)%Z -> (n - i <= Z.of_nat fuel)%Z ->
    (forall a0' a1' a3' a4' a6' a7' xbs' (mm' : mem), u8arr asegs mm' X xbs' -> length xbs' = 496%nat ->
       mem_inv asegs mm' -> munch WX m0 mm' -> wmono asegs m0 mm' ->
       evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3' a4' (Z_to_bv 64 0) a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe1330) fc None mm' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 8 * i)) a1 a2 (Z_to_bv 64 (2147450880 + X / 8 + i)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (n - i)) a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe12f8) fc None mm (seg_rom asegs)).
  Proof using X8 XR XSH XS0.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros XA XL ZR MI MU WM Hi Hn Hf HK; [exfalso; lia|].
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe12f8%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n); [eassumption | lia | eassumption | eassumption | eassumption | eassumption | lia | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe1330%Z => first [ eapply evt_eq; [| eapply HK; [eassumption | lia | eassumption | eassumption | eassumption]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End LMLX.
