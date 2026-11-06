(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Walk Arr FP ITree Decode StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface F_printf_core.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module I_strerror.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.      (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition strerror_i_entry := 0x48eac%Z.
Definition STRERROR_I_DEPTH : Z := 32.


Definition strerror_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e loc lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strerror_res e)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition strerror_w_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e loc lo k : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (KHIGH <= lo)%Z ->
  rt_inited m -> rt_real_strerror m ->
  rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)] ->                          (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] ->               (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->            (* [comment removed for export] *)
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->                          (* [comment removed for export] *)
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  (0 <= k <= 1)%Z -> (48 <= bv_unsigned tp /\ bv_unsigned tp + 20 <= 0x5e24f0)%Z -> (0x5e14f0 <= bv_unsigned tp + -48)%Z ->   (* [comment removed for export] *)
  (bv_unsigned tp + 20 <= lo)%Z ->                                             (* [comment removed for export] *)
  (0x5e24f0 <= loc /\ loc + 48 <= 0x603000)%Z ->                                    (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (bv_unsigned tp + 16) 4 -> rng RNG (loc + 40) 8 ->
  evtF asegs RNG (strerror_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e loc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444c0) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo k : ltac2:(SecDiet.SzSec.tyM 'strerror_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_w_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO INI RSE GOTL CNT TLSL LOC -> He K01 TPLO TPK TPHI Hloc RIMG RSTK RTL RCNT RLOC.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof CNT as CNT0. change (rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]) with (sf_hide (rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)])) in CNT0.
  zstep.
  carve_frame 16%nat ST.
  do 4 zstep.
  zstep. call_sp tryinit_spec. all: iprem.
  rename PC into ST. clear POST.
  zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. rewrite (Z.add_comm 16 (bv_unsigned tp)).
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. call_sp strerror_spec.
  all: lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- rw_cells _ _ _ _ => first [exact TLSL | exact LOC]
       | |- mem_inv _ _ => exact MI0
       | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
       | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RSTK | lia]]
       | |- _ => first [exact He | lia]
       end.
  rename PC into ST. clear PC0 POST.
  rewrite (sx32_lit 0) in CNT by lia. rewrite unsigned_lit in CNT by lia. change (0 + 1)%Z with 1%Z in CNT.
  zstep.                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. carve_frame 16%nat ST.
  do 5 zstep. zstep. rewrite (Z.add_comm 16 (bv_unsigned tp)).
  zstep.
  rewrite (sx32_lit 1) by lia.
  zstep. if_false.                             (* [comment removed for export] *)
  zstep. zstep.                                (* [comment removed for export] *)
  zstep. zstep. zstep.
  release_frame FR0 ST (bv_unsigned sp + -16)%Z.
  zstep.                                       (* [comment removed for export] *)
  do 4 zstep.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  zstep.
  (* [comment removed for export] *)
  unfold strerror_i_post. finish.
Qed.
End Sz2.
#[using="Type"] Lemma strerror_w_spec : ltac:(let t := eval cbv delta [strerror_w_spec__stmt] in strerror_w_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo k. ltac2:(SecDiet.SzSec.closeP 'strerror_w_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.      (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition strerror_i_entry := 0x48f14%Z.
Definition STRERROR_I_DEPTH : Z := 32.


Definition strerror_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e loc lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strerror_res e)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition strerror_w_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e loc lo k : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (KHIGH <= lo)%Z ->
  rt_inited m -> rt_real_strerror m ->
  rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)] ->                          (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] ->               (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->            (* [comment removed for export] *)
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->                          (* [comment removed for export] *)
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  (0 <= k <= 1)%Z -> (48 <= bv_unsigned tp /\ bv_unsigned tp + 20 <= 0x5e28f0)%Z -> (0x5e18f0 <= bv_unsigned tp + -48)%Z ->   (* [comment removed for export] *)
  (bv_unsigned tp + 20 <= lo)%Z ->                                             (* [comment removed for export] *)
  (0x5e28f0 <= loc /\ loc + 48 <= 0x604000)%Z ->                                    (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (bv_unsigned tp + 16) 4 -> rng RNG (loc + 40) 8 ->
  evtF asegs RNG (strerror_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e loc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44528) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo k : ltac2:(SecDiet.SzSec.tyM 'strerror_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_w_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO INI RSE GOTL CNT TLSL LOC -> He K01 TPLO TPK TPHI Hloc RIMG RSTK RTL RCNT RLOC.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof CNT as CNT0. change (rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]) with (sf_hide (rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)])) in CNT0.
  zstep.
  carve_frame 16%nat ST.
  do 4 zstep.
  zstep. call_sp tryinit_spec. all: iprem.
  rename PC into ST. clear POST.
  zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. rewrite (Z.add_comm 16 (bv_unsigned tp)).
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. call_sp strerror_spec.
  all: lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- rw_cells _ _ _ _ => first [exact TLSL | exact LOC]
       | |- mem_inv _ _ => exact MI0
       | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
       | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RSTK | lia]]
       | |- _ => first [exact He | lia]
       end.
  rename PC into ST. clear PC0 POST.
  rewrite (sx32_lit 0) in CNT by lia. rewrite unsigned_lit in CNT by lia. change (0 + 1)%Z with 1%Z in CNT.
  zstep.                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. carve_frame 16%nat ST.
  do 5 zstep. zstep. rewrite (Z.add_comm 16 (bv_unsigned tp)).
  zstep.
  rewrite (sx32_lit 1) by lia.
  zstep. if_false.                             (* [comment removed for export] *)
  zstep. zstep.                                (* [comment removed for export] *)
  zstep. zstep. zstep.
  release_frame FR0 ST (bv_unsigned sp + -16)%Z.
  zstep.                                       (* [comment removed for export] *)
  do 4 zstep.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  zstep.
  (* [comment removed for export] *)
  unfold strerror_i_post. finish.
Qed.
End Sz2.
#[using="Type"] Lemma strerror_w_spec : ltac:(let t := eval cbv delta [strerror_w_spec__stmt] in strerror_w_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo k. ltac2:(SecDiet.SzSec.closeP 'strerror_w_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End I_strerror.

(* [comment removed for export] *)
Module F_strrchr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strlen. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memrchr_entry := 0x9eaa4%Z.
Definition strrchr_entry := 0x9f038%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
    /\ bytes_at asegs m (bv_unsigned a0) buf.

Section MemrchrProof.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis BUF : bytes_at asegs m (bv_unsigned a0) buf.
  Hypothesis LEN : length buf = Z.to_nat (bv_unsigned a2).
  Hypothesis RBUF : rng RNG (bv_unsigned a0) (Z.of_nat (length buf)).
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation POST := (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m).
  (* [comment removed for export] *)
  Notation ST pc x10 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition NOA (k : Z) : Prop :=
    forall j b, (Z.to_nat k <= j)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  Lemma A_bound : (0 <= A /\ A + n <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof using BUF LEN. pin_using (fun (BUF LEN : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ BUF). rewrite LEN in H.
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  Lemma res_found : forall k b, (1 <= k <= n)%Z -> NOA k -> nth_error buf (Z.to_nat (k - 1)) = Some b -> bv_unsigned b = c ->
    memrchr_res A c buf = (A + (k - 1))%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros k b Hk HN Hn Hb. unfold memrchr_res.
    rewrite (last_byte_charact c buf (Z.to_nat (k - 1)) b Hn Hb). { f_equal. lia. }
    intros j b' Hj Hn'. eapply HN; [|exact Hn']. lia.
  Qed.

  Lemma res_none : NOA 0 -> memrchr_res A c buf = 0%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros HN. unfold memrchr_res. rewrite last_byte_None_intro; [reflexivity|].
    intros j b Hn. eapply HN; [|exact Hn]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memrchr_loop : forall (kn : nat) (k : Z) (x10 x14 : word),
    Z.to_nat k = kn -> (0 <= k <= n)%Z -> NOA k ->
    evtF asegs RNG POST (ST 0x9eab0 x10 (Z_to_bv 64 (A + k)) (Z_to_bv 64 (- k)) x14).
  Proof using BUF LEN MI RBUF. pin_using (fun (BUF LEN MI : unit) => tt).
    induction kn as [|kn IH]; intros k x10 x14 Hk Hkn HN; pose proof A_bound as AB.
    - zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
      zstep. zstep. rewrite <- res_none at 1. { finish. } replace 0%Z with k by lia. exact HN.
    - zstep. if_cases K; zify_cond K.
      { exfalso. replace (-k)%Z with ((2^64 - k) + (-1) * 2^64)%Z in K by lia.
        rewrite Z.mod_add in K by lia. rewrite Z.mod_small in K by lia. lia. }
      destruct (nth_error buf (Z.to_nat (k - 1))) as [b|] eqn:Hn.
      2:{ exfalso. apply nth_error_None in Hn. lia. }
      pose proof (u8ro_read asegs m A buf (k - 1) b (wa (A + k + -1)) BUF Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. replace (- k + 1)%Z with (- (k - 1))%Z by lia.
        apply (IH (k - 1)%Z); [lia|lia|].
        intros j b' Hj Hn'. destruct (Nat.eq_dec j (Z.to_nat (k - 1))) as [->|NE].
        { rewrite Hn in Hn'. injection Hn' as <-. exact K2. }
        eapply HN; [|exact Hn']. lia.
      + (* [comment removed for export] *)
        zstep. replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. rewrite <- (res_found k b ltac:(lia) HN Hn K2). finish.
  Qed.
End MemrchrProof.

Definition memrchr_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at asegs m (bv_unsigned a0) buf ->
  length buf = Z.to_nat (bv_unsigned a2) ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length buf)) ->
  evtF asegs RNG (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9eaa4) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf : ltac2:(SecDiet.SzSec.tyM 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma memrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BUF LEN MI RBUF.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB. rewrite LEN in AB.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. rewrite (Z.land_ones _ 8) by lia. change (Z.ones 8) with 255%Z. rewrite <- (Z.land_ones (bv_unsigned a1) 8) by lia.
  change (Z.land (bv_unsigned a1) (Z.ones 8)) with (Z.land (bv_unsigned a1) 255).
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (Z.ones 8). rewrite Z.land_ones by (pose proof (bv_unsigned_in_range 64 a1); lia). reflexivity. }
  zstep. zstep.
  replace (0 - bv_unsigned a2)%Z with (- bv_unsigned a2)%Z by lia.
  eapply (memrchr_loop RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
            MI BUF LEN RBUF (Z.to_nat (bv_unsigned a2)) (bv_unsigned a2)); [reflexivity|lia|].
  intros j b Hj Hn. exfalso. apply nth_error_lt in Hn. lia.
Qed.
End Sz5.
Lemma memrchr_spec : ltac:(let t := eval cbv delta [memrchr_spec__stmt] in memrchr_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf. ltac2:(SecDiet.SzSec.closeP 'memrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section CANSEC1. Context {rc : runConstT}.
Definition strrchr_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 2256)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (* [comment removed for export] *)
  (KHIGH <= lo)%Z -> icptenv m -> sobj RNG m (bv_unsigned a0) (bv_unsigned a0 + (Z.of_nat (length str) + 1)) ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (strrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f038) fc None m (seg_rom asegs)).
Section Sz6.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP KLO ENV SO RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (RFR : rng RNG (bv_unsigned sp + -32) 32) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  carve_frame 32%nat ST.
  do 6 step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV| exact MU| exact WM| unfold KHIGH in KLO; solve_iesafe]);
    assert (SO1 : sobj RNG m1 (bv_unsigned a0) (bv_unsigned a0 + (Z.of_nat (length str) + 1)))
      by (eapply sobj_transport; [exact SO| exact MU| exact WM| unfold KHIGH in KLO; solve_appW]) end.
  destruct SO1 as (APP1 & UNP1 & SZ1 & RLO & RHI & HULL1 & WR1 & RSH1).
  call_sp strlen_w_spec;
    [ exact MI | exact ST | lia | exact KLO | exact (ie_got _ ENV1) | exact (ie_shb _ ENV1) | exact (ie_ini _ ENV1) | exact (ie_lay _ ENV1)
    | exact (ie_strlen _ ENV1) | exact (ie_isl _ ENV1) | exact STR | exact NONUL | exact PAD
    | rewrite length_app; cbn [length]; lia | exact APP1 | exact UNP1 | lia | exact HULL1 | exact WR1
    | eapply rng_sub'; [exact RSTK | lia] | ].
  rename PC into ST.
  do 3 zstep.
  do 4 step. release_frame FR ST (bv_unsigned sp).
  step.
  (* [comment removed for export] *)
  pose proof POST as P2.
  replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in P2 by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in P2. destruct P2 as [STR0 _].
  eapply evtF_mono. { eapply memrchr_spec; [exact STR0 | | exact MI0 |].
    - rewrite length_app. cbn [length]. rewrite unsigned_lit by lia. lia.
    - eapply rng_sub'; [exact RSTR|]. rewrite !length_app. cbn [length]. lia. }
  intros ms' H. unfold memrchr_post in H. unfold strrchr_post, strrchr_res. destruct_exs H.
  destruct H as (-> & _ & _ & _ & _).
  do 15 eexists. split; [reflexivity|]. repeat (split; [assumption|]). exact POST.
Qed.
End Sz6.
#[using="Type"] Lemma strrchr_spec : ltac:(let t := eval cbv delta [strrchr_spec__stmt] in strrchr_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memrchr_entry := 0x9ee88%Z.
Definition strrchr_entry := 0x9f41c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (memrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) buf))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
    /\ bytes_at asegs m (bv_unsigned a0) buf.

Section MemrchrProof.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis BUF : bytes_at asegs m (bv_unsigned a0) buf.
  Hypothesis LEN : length buf = Z.to_nat (bv_unsigned a2).
  Hypothesis RBUF : rng RNG (bv_unsigned a0) (Z.of_nat (length buf)).
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation POST := (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m).
  (* [comment removed for export] *)
  Notation ST pc x10 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition NOA (k : Z) : Prop :=
    forall j b, (Z.to_nat k <= j)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

  Lemma A_bound : (0 <= A /\ A + n <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
  Proof using BUF LEN. pin_using (fun (BUF LEN : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ BUF). rewrite LEN in H.
    pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
  Qed.

  Lemma res_found : forall k b, (1 <= k <= n)%Z -> NOA k -> nth_error buf (Z.to_nat (k - 1)) = Some b -> bv_unsigned b = c ->
    memrchr_res A c buf = (A + (k - 1))%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros k b Hk HN Hn Hb. unfold memrchr_res.
    rewrite (last_byte_charact c buf (Z.to_nat (k - 1)) b Hn Hb). { f_equal. lia. }
    intros j b' Hj Hn'. eapply HN; [|exact Hn']. lia.
  Qed.

  Lemma res_none : NOA 0 -> memrchr_res A c buf = 0%Z.
  Proof using LEN. pin_using (fun (LEN : unit) => tt).
    intros HN. unfold memrchr_res. rewrite last_byte_None_intro; [reflexivity|].
    intros j b Hn. eapply HN; [|exact Hn]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memrchr_loop : forall (kn : nat) (k : Z) (x10 x14 : word),
    Z.to_nat k = kn -> (0 <= k <= n)%Z -> NOA k ->
    evtF asegs RNG POST (ST 0x9ee94 x10 (Z_to_bv 64 (A + k)) (Z_to_bv 64 (- k)) x14).
  Proof using BUF LEN MI RBUF. pin_using (fun (BUF LEN MI : unit) => tt).
    induction kn as [|kn IH]; intros k x10 x14 Hk Hkn HN; pose proof A_bound as AB.
    - zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
      zstep. zstep. rewrite <- res_none at 1. { finish. } replace 0%Z with k by lia. exact HN.
    - zstep. if_cases K; zify_cond K.
      { exfalso. replace (-k)%Z with ((2^64 - k) + (-1) * 2^64)%Z in K by lia.
        rewrite Z.mod_add in K by lia. rewrite Z.mod_small in K by lia. lia. }
      destruct (nth_error buf (Z.to_nat (k - 1))) as [b|] eqn:Hn.
      2:{ exfalso. apply nth_error_None in Hn. lia. }
      pose proof (u8ro_read asegs m A buf (k - 1) b (wa (A + k + -1)) BUF Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. replace (- k + 1)%Z with (- (k - 1))%Z by lia.
        apply (IH (k - 1)%Z); [lia|lia|].
        intros j b' Hj Hn'. destruct (Nat.eq_dec j (Z.to_nat (k - 1))) as [->|NE].
        { rewrite Hn in Hn'. injection Hn' as <-. exact K2. }
        eapply HN; [|exact Hn']. lia.
      + (* [comment removed for export] *)
        zstep. replace (A + k + -1)%Z with (A + (k - 1))%Z by lia. rewrite <- (res_found k b ltac:(lia) HN Hn K2). finish.
  Qed.
End MemrchrProof.

Definition memrchr_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
  bytes_at asegs m (bv_unsigned a0) buf ->
  length buf = Z.to_nat (bv_unsigned a2) ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length buf)) ->
  evtF asegs RNG (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ee88) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf : ltac2:(SecDiet.SzSec.tyM 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma memrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'memrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BUF LEN MI RBUF.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB. rewrite LEN in AB.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. rewrite (Z.land_ones _ 8) by lia. change (Z.ones 8) with 255%Z. rewrite <- (Z.land_ones (bv_unsigned a1) 8) by lia.
  change (Z.land (bv_unsigned a1) (Z.ones 8)) with (Z.land (bv_unsigned a1) 255).
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (Z.ones 8). rewrite Z.land_ones by (pose proof (bv_unsigned_in_range 64 a1); lia). reflexivity. }
  zstep. zstep.
  replace (0 - bv_unsigned a2)%Z with (- bv_unsigned a2)%Z by lia.
  eapply (memrchr_loop RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
            MI BUF LEN RBUF (Z.to_nat (bv_unsigned a2)) (bv_unsigned a2)); [reflexivity|lia|].
  intros j b Hj Hn. exfalso. apply nth_error_lt in Hn. lia.
Qed.
End Sz5.
Lemma memrchr_spec : ltac:(let t := eval cbv delta [memrchr_spec__stmt] in memrchr_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf. ltac2:(SecDiet.SzSec.closeP 'memrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section CANSEC1. Context {rc : runConstT}.
Definition strrchr_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 2256)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (* [comment removed for export] *)
  (KHIGH <= lo)%Z -> icptenv m -> sobj RNG m (bv_unsigned a0) (bv_unsigned a0 + (Z.of_nat (length str) + 1)) ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (strrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f41c) fc None m (seg_rom asegs)).
Section Sz6.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strrchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strrchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP KLO ENV SO RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (RFR : rng RNG (bv_unsigned sp + -32) 32) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  carve_frame 32%nat ST.
  do 6 step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV| exact MU| exact WM| unfold KHIGH in KLO; solve_iesafe]);
    assert (SO1 : sobj RNG m1 (bv_unsigned a0) (bv_unsigned a0 + (Z.of_nat (length str) + 1)))
      by (eapply sobj_transport; [exact SO| exact MU| exact WM| unfold KHIGH in KLO; solve_appW]) end.
  destruct SO1 as (APP1 & UNP1 & SZ1 & RLO & RHI & HULL1 & WR1 & RSH1).
  call_sp strlen_w_spec;
    [ exact MI | exact ST | lia | exact KLO | exact (ie_got _ ENV1) | exact (ie_shb _ ENV1) | exact (ie_ini _ ENV1) | exact (ie_lay _ ENV1)
    | exact (ie_strlen _ ENV1) | exact (ie_isl _ ENV1) | exact STR | exact NONUL | exact PAD
    | rewrite length_app; cbn [length]; lia | exact APP1 | exact UNP1 | lia | exact HULL1 | exact WR1
    | eapply rng_sub'; [exact RSTK | lia] | ].
  rename PC into ST.
  do 3 zstep.
  do 4 step. release_frame FR ST (bv_unsigned sp).
  step.
  (* [comment removed for export] *)
  pose proof POST as P2.
  replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in P2 by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in P2. destruct P2 as [STR0 _].
  eapply evtF_mono. { eapply memrchr_spec; [exact STR0 | | exact MI0 |].
    - rewrite length_app. cbn [length]. rewrite unsigned_lit by lia. lia.
    - eapply rng_sub'; [exact RSTR|]. rewrite !length_app. cbn [length]. lia. }
  intros ms' H. unfold memrchr_post in H. unfold strrchr_post, strrchr_res. destruct_exs H.
  destruct H as (-> & _ & _ & _ & _).
  do 15 eexists. split; [reflexivity|]. repeat (split; [assumption|]). exact POST.
Qed.
End Sz6.
#[using="Type"] Lemma strrchr_spec : ltac:(let t := eval cbv delta [strrchr_spec__stmt] in strrchr_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strrchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_strrchr.

(* [comment removed for export] *)
Module I_strchr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac F_rip. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strlen. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.


Section CANSEC1. Context {rc : runConstT}.
Definition strchr_i_entry := 0x44f68%Z.

Definition strchr_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S cc : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strchr_res S cc str)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section STRCHR.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation cc := (bv_unsigned a1 mod 256)%Z.
  Notation K := (Z.of_nat (strchrnul_idx cc str)).
  Notation N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z.
  Notation RES := (strchr_res S cc str).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RSC : rt_real_strchr m.
  Hypothesis ISL : rt_isl m.
  Hypothesis SSC : rt_ssc m.
  Hypothesis STR : bytes_at asegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis CNZ : (cc <> 0)%Z.
  Hypothesis SEPB : (S + Z.of_nat (length full) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis SPOS : (0 < S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length full)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m).
  Notation SAVES := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at asegs mc S full.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m slack ST LO KLO CNZ SPOS APP NSZ R1"] Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    pose proof (strchrnul_idx_le cc str) as KL.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m slack ST LO KLO CNZ SPOS APP NSZ R1"] Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & STR1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RSC; change (?P) with (sf_hide P) in ISL; change (?P) with (sf_hide P) in SSC;
    change (?P) with (sf_hide P) in STR; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO STR CNZ SEPB SPOS APP UNP NSZ R1 WR1"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact STR | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.


  (* [comment removed for export] *)
  Definition sregs (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
        a0 x19 (Z_to_bv 64 0x140128) (Z_to_bv 64 (bv_unsigned sp + -2144)) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNZ SPOS APP NSZ R1 RSTK"] Lemma SX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4508c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 12 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -72 + Z.of_nat 72)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strchr_i_post.
    replace (bv_unsigned sp - 2224)%Z with (bv_unsigned sp + -2224)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNZ SPOS APP NSZ R1 RSTK RSH1"] Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x9 x14 x15 x16 x17 x19 x22 x23 x28 x29 x30 x31,
    SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
                                   x19 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4514c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNZ SPOS APP NSZ R1 RSTK RSH1"] Lemma SE : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   x13 x14 x15 x16 x17 (Z_to_bv 64 (S + N + -1)) x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45130) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SX; eassumption.
    - eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO STR CNZ SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RSH1"] Lemma SC : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
                                 a0 (Z_to_bv 64 K) (Z_to_bv 64 0x140128) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45038) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 5 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SX. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (K + S)%Z with (S + N + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SE; eassumption.
      + eapply SX; eassumption.
  Qed.

  #[using="RLO RHI MI ST LO KLO GOT SHB INI LAY RSC ISL SSC STR NONUL PAD CNZ SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma strchr_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44f68) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ STR) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RSC as RSCc. pose proof ISL as ISLc. pose proof SSC as SSCc.
    shide_all.
    carve_frame 72%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    do 6 zstep.
    assert (STRn : bytes_at asegs x13 S full).
    { unfold sf_hide in STR, SEPB, LO. eapply bytes_at_transport; [exact STR | exact MU |]. cbn [disjoint_from]. clear -SEPB LO BL0. lia. }
    unfold sf_hide in PAD.
    call_sp strchr_spec; [ exact PC | exact STRn | exact NONUL | exact PAD | exact MI0 | clear -BL0; lia
                         | unfold sf_hide in SEPB, LO; rewrite length_app in SEPB; cbn [length] in SEPB; clear -SEPB LO BL0; lia | exact CNZ | ].
    assert (ISL1 : rw_cells asegs x28 0x140220 [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]).
    { pose proof ISLc as ISL'. recell ISL' 0%nat 1%nat [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]. exact ISL'. }
    assert (SSC1 : rw_cells asegs x28 0x140218 [CB 5 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1]; C1 (Z_to_bv 8 0); CB 2 (repeat (Z_to_bv 8 1) 2)]).
    { pose proof SSCc as SSC'. recell SSC' 0%nat 1%nat [CB 5 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1]; C1 (Z_to_bv 8 0); CB 2 (repeat (Z_to_bv 8 1) 2)]. exact SSC'. }
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str).
    { apply Forall_forall. intros b Hb E. apply NONUL. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    assert (IVn : SINV x28) by (eapply sinv_of; eassumption).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.find_byte cc str) as [i|] eqn:FB.
    - (* [comment removed for export] *)
      assert (ER : RES = (S + Z.of_nat i)%Z).
      { unfold strchr_res. rewrite FB. destruct (Z.eqb_spec cc 0) as [E0|_]; [exfalso; exact (CNZ E0)| reflexivity]. }
      assert (EK : K = Z.of_nat i) by (unfold strchrnul_idx; rewrite FB; reflexivity).
      rewrite ER. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 BL0 SPOS EK. lia. } clear K4.
      zstep. zstep.
      replace (S + Z.of_nat i - S)%Z with K by lia. rewrite <- ER.
      eapply SC; exact IVn.
    - (* [comment removed for export] *)
      assert (ER : RES = 0%Z).
      { unfold strchr_res. rewrite FB. destruct (Z.eqb_spec cc 0) as [E0|_]; [exfalso; exact (CNZ E0)| reflexivity]. }
      assert (EK : K = Z.of_nat (length str)) by (unfold strchrnul_idx; rewrite FB; reflexivity).
      rewrite ER. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. } clear K4.
      zstep. zstep. zstep.
      call istrlen_spec; [ eassumption | exact POST0 | exact NZ
                         | unfold sf_hide in *; eapply rng_sub'; [exact RB | rewrite length_app; cbn [length]; lia] | ].
      zstep. zstep.
      rewrite <- EK. rewrite <- ER.
      eapply SC; exact IVn.
  Qed.
End STRCHR.

#[using="Type"] Lemma strchr_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strchr m -> rt_isl m -> rt_ssc m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (cc <> 0)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44f68) fc None m (seg_rom asegs)).
Proof. intros. eapply strchr_i_body; eassumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strchr_w_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strchr m -> rt_isl m -> rt_ssc m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (cc <> 0)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44474) fc None m (seg_rom asegs)).
Proof.
  intros. assert (RI' : rng_aimg RNG) by assumption.
  zstep. eapply strchr_i_body; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strchr_wb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte),
  let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (cc <> 0)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  sobj RNG m S (S + N) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  evtF asegs RNG (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44474) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros S cc N MI ST LO KLO ENV STR NONUL PAD CNZ SEPB SPOS (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK RB.
  eapply (strchr_w_spec RNG) with (RLO := RLO) (RHI := RHI); try eassumption;
    first [ exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_ini _ ENV) | exact (ie_lay _ ENV) | exact (ie_strchr _ ENV)
          | exact (ie_isl _ ENV) | exact (ie_ssc _ ENV) | (unfold N, cc, S in NSZ; lia) ].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.


Section CANSEC1. Context {rc : runConstT}.
Definition strchr_i_entry := 0x44fd0%Z.

Definition strchr_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S cc : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strchr_res S cc str)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section STRCHR.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation cc := (bv_unsigned a1 mod 256)%Z.
  Notation K := (Z.of_nat (strchrnul_idx cc str)).
  Notation N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z.
  Notation RES := (strchr_res S cc str).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RSC : rt_real_strchr m.
  Hypothesis ISL : rt_isl m.
  Hypothesis SSC : rt_ssc m.
  Hypothesis STR : bytes_at asegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis CNZ : (cc <> 0)%Z.
  Hypothesis SEPB : (S + Z.of_nat (length full) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis SPOS : (0 < S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length full)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m).
  Notation SAVES := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at asegs mc S full.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m slack ST LO KLO CNZ SPOS APP NSZ R1"] Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    pose proof (strchrnul_idx_le cc str) as KL.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m slack ST LO KLO CNZ SPOS APP NSZ R1"] Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & STR1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RSC; change (?P) with (sf_hide P) in ISL; change (?P) with (sf_hide P) in SSC;
    change (?P) with (sf_hide P) in STR; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO STR CNZ SEPB SPOS APP UNP NSZ R1 WR1"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact STR | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.


  (* [comment removed for export] *)
  Definition sregs (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
        a0 x19 (Z_to_bv 64 0x140528) (Z_to_bv 64 (bv_unsigned sp + -2144)) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNZ SPOS APP NSZ R1 RSTK"] Lemma SX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x450f4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 12 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -72 + Z.of_nat 72)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strchr_i_post.
    replace (bv_unsigned sp - 2224)%Z with (bv_unsigned sp + -2224)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNZ SPOS APP NSZ R1 RSTK RSH1"] Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x9 x14 x15 x16 x17 x19 x22 x23 x28 x29 x30 x31,
    SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
                                   x19 x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x451b4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO CNZ SPOS APP NSZ R1 RSTK RSH1"] Lemma SE : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   x13 x14 x15 x16 x17 (Z_to_bv 64 (S + N + -1)) x22 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45198) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SX; eassumption.
    - eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO STR CNZ SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RSH1"] Lemma SC : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
                                 a0 (Z_to_bv 64 K) (Z_to_bv 64 0x140528) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x450a0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 5 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SX. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (K + S)%Z with (S + N + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SE; eassumption.
      + eapply SX; eassumption.
  Qed.

  #[using="RLO RHI MI ST LO KLO GOT SHB INI LAY RSC ISL SSC STR NONUL PAD CNZ SEPB SPOS APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma strchr_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44fd0) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ STR) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RSC as RSCc. pose proof ISL as ISLc. pose proof SSC as SSCc.
    shide_all.
    carve_frame 72%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    do 6 zstep.
    assert (STRn : bytes_at asegs x13 S full).
    { unfold sf_hide in STR, SEPB, LO. eapply bytes_at_transport; [exact STR | exact MU |]. cbn [disjoint_from]. clear -SEPB LO BL0. lia. }
    unfold sf_hide in PAD.
    call_sp strchr_spec; [ exact PC | exact STRn | exact NONUL | exact PAD | exact MI0 | clear -BL0; lia
                         | unfold sf_hide in SEPB, LO; rewrite length_app in SEPB; cbn [length] in SEPB; clear -SEPB LO BL0; lia | exact CNZ | ].
    assert (ISL1 : rw_cells asegs x28 0x140620 [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]).
    { pose proof ISLc as ISL'. recell ISL' 0%nat 1%nat [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]. exact ISL'. }
    assert (SSC1 : rw_cells asegs x28 0x140618 [CB 5 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1]; C1 (Z_to_bv 8 0); CB 2 (repeat (Z_to_bv 8 1) 2)]).
    { pose proof SSCc as SSC'. recell SSC' 0%nat 1%nat [CB 5 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1]; C1 (Z_to_bv 8 0); CB 2 (repeat (Z_to_bv 8 1) 2)]. exact SSC'. }
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str).
    { apply Forall_forall. intros b Hb E. apply NONUL. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    assert (IVn : SINV x28) by (eapply sinv_of; eassumption).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.find_byte cc str) as [i|] eqn:FB.
    - (* [comment removed for export] *)
      assert (ER : RES = (S + Z.of_nat i)%Z).
      { unfold strchr_res. rewrite FB. destruct (Z.eqb_spec cc 0) as [E0|_]; [exfalso; exact (CNZ E0)| reflexivity]. }
      assert (EK : K = Z.of_nat i) by (unfold strchrnul_idx; rewrite FB; reflexivity).
      rewrite ER. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 BL0 SPOS EK. lia. } clear K4.
      zstep. zstep.
      replace (S + Z.of_nat i - S)%Z with K by lia. rewrite <- ER.
      eapply SC; exact IVn.
    - (* [comment removed for export] *)
      assert (ER : RES = 0%Z).
      { unfold strchr_res. rewrite FB. destruct (Z.eqb_spec cc 0) as [E0|_]; [exfalso; exact (CNZ E0)| reflexivity]. }
      assert (EK : K = Z.of_nat (length str)) by (unfold strchrnul_idx; rewrite FB; reflexivity).
      rewrite ER. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. } clear K4.
      zstep. zstep. zstep.
      call istrlen_spec; [ eassumption | exact POST0 | exact NZ
                         | unfold sf_hide in *; eapply rng_sub'; [exact RB | rewrite length_app; cbn [length]; lia] | ].
      zstep. zstep.
      rewrite <- EK. rewrite <- ER.
      eapply SC; exact IVn.
  Qed.
End STRCHR.

#[using="Type"] Lemma strchr_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strchr m -> rt_isl m -> rt_ssc m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (cc <> 0)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44fd0) fc None m (seg_rom asegs)).
Proof. intros. eapply strchr_i_body; eassumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strchr_w_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strchr m -> rt_isl m -> rt_ssc m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (cc <> 0)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444dc) fc None m (seg_rom asegs)).
Proof.
  intros. assert (RI' : rng_aimg RNG) by assumption.
  zstep. eapply strchr_i_body; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strchr_wb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte),
  let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let N := (Z.of_nat (strchrnul_idx cc str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (cc <> 0)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  sobj RNG m S (S + N) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  evtF asegs RNG (strchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444dc) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros S cc N MI ST LO KLO ENV STR NONUL PAD CNZ SEPB SPOS (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK RB.
  eapply (strchr_w_spec RNG) with (RLO := RLO) (RHI := RHI); try eassumption;
    first [ exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_ini _ ENV) | exact (ie_lay _ ENV) | exact (ie_strchr _ ENV)
          | exact (ie_isl _ ENV) | exact (ie_ssc _ ENV) | (unfold N, cc, S in NSZ; lia) ].
Qed.
End CANSEC1.
End TwB.
End I_strchr.

(* [comment removed for export] *)
Module F_fmodeflags.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strchr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fmodeflags_entry := 0x9a8a0%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Local Open Scope Z_scope.
  Notation M64 := 18446744073709551616.

  #[using="Type"] Lemma snez_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> (0 <? (v + k') mod M64) = negb (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - cbn [negb]. apply Z.ltb_lt. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma seqz_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> ((v + k') mod M64 <? 1) = (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - apply Z.ltb_ge. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma b2z_shiftl_mod : forall (b : bool) k, 0 <= k < 64 -> (Z.shiftl (Z.b2z b) k) mod M64 = Z.shiftl (Z.b2z b) k.
  Proof.
    intros b k Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 ^ k < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    destruct b; cbn [Z.b2z]; lia.
  Qed.

  #[using="Type"] Lemma strchr_res_found : forall A c str, 0 < A -> c <> 0 -> A + Z.of_nat (length str) < M64 ->
    (0 <? strchr_res A c str mod M64) = has_byte c str.
  Proof.
    intros A c str HA Hc HB. unfold strchr_res, has_byte.
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
    destruct (find_byte c str) as [i|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
    - reflexivity.
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fmodeflags_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fmodeflags str)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

(* [comment removed for export] *)
Local Ltac read_b0 STR FULL RD :=
  lazymatch type of STR with bytes_at _ ?mm (bv_unsigned ?a) _ =>
    pose proof (u8ro_read asegs mm (bv_unsigned a) _ 0 _ a STR ltac:(rewrite FULL; reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition fmodeflags_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 2256)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  (* [comment removed for export] *)
  (KHIGH <= lo)%Z -> icptenv m -> sobj RNG m (bv_unsigned a0) (bv_unsigned a0 + (Z.of_nat (length str) + 1)) ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9a8a0) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fmodeflags_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP A0 KLO ENV SO RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (RFR : rng RNG (bv_unsigned sp + -32) 32) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  destruct (str ++ Z_to_bv 8 0 :: slack) as [|b0 rest] eqn:FULL. { destruct str; discriminate. }
  rewrite <- FULL in STR, RSTR. pose proof (byte_range b0) as Rb0.
  assert (M0 : mode_m0 str = bv_unsigned b0). { destruct str; cbn in FULL; injection FULL; intros; subst; reflexivity. }
  carve_frame 32%nat ST.
  do 7 step.
  step. ienv_now ENV MU WM as ENVn. sobj_now SO MU WM as SOn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 43) mod 256) str) as IDXLE.
    call_sp strchr_wb_spec. all: icpt_prem RSTK.
    clear ENVn SOn IDXLE.
  rename PC into ST; clear STR; rename POST into STR.
  zstep.
  (* [comment removed for export] *)
  assert (JOIN : forall (s1v xa0 : word) mm,
    s1v = Z_to_bv 64 (if has_byte 43 str then 2 else Z.b2z (negb (mode_m0 str =? 114)))%Z ->
    mem_inv asegs mm -> munch [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m mm -> wmono asegs m mm ->
    rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
    stk asegs mm lo (bv_unsigned sp + -32) ->
    evtF asegs RNG (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
      (MS (mkR (Z_to_bv 64 0x9a8c0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x x0 x1 a0 s1v xa0 x2 x3 x4 x5 x6 x7 x8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x9 x10 x11 x12)
          F (Z_to_bv 64 0x9a8d8) fc None mm (seg_rom asegs))).
  { clear dependent x13. intros s1v xa0 mm -> MI MU WM FR STR ST.
    zstep. zstep. step. ienv_now ENV MU WM as ENVn. sobj_now SO MU WM as SOn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 120) mod 256) str) as IDXLE.
    call_sp strchr_wb_spec. all: icpt_prem RSTK.
    clear ENVn SOn IDXLE.
    rename PC into ST; clear STR; rename POST into STR.
    zstep. zstep. zstep. zstep. step. ienv_now ENV MU WM as ENVn. sobj_now SO MU WM as SOn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 101) mod 256) str) as IDXLE.
    call_sp strchr_wb_spec. all: icpt_prem RSTK.
    clear ENVn SOn IDXLE.
    rename PC into ST; clear STR; rename POST into STR.
    zstep. read_b0 STR FULL RD.
    do 16 zstep.
    rewrite !b2z_shiftl_mod by lia.
    rewrite !(strchr_res_found (bv_unsigned a0)) by lia.
    rewrite !(snez_sub_byte (bv_unsigned b0) 114 (-114)), !(seqz_sub_byte (bv_unsigned b0) 119 (-119)), !(seqz_sub_byte (bv_unsigned b0) 97 (-97)) by lia.
    rewrite <- !M0.
    setreg 10%Z (Z_to_bv 64 (fmodeflags str)) ltac:(unfold fmodeflags, fmodeflags_w; destruct (has_byte 43 str); reflexivity).
    do 5 step. release_frame FR ST (bv_unsigned sp). step.
    unfold fmodeflags_post. finish. }
  if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    read_b0 STR FULL RD. zstep. zstep. zstep.
    eapply JOIN; try eassumption.
    rewrite (snez_sub_byte (bv_unsigned b0) 114 (-114)), <- M0 by lia.
    replace (has_byte 43 str) with false; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_ge. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
  - zstep. zstep.
    eapply JOIN; try eassumption.
    replace (has_byte 43 str) with true; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_lt. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
Qed.
End Sz5.
#[using="Type"] Lemma fmodeflags_spec : ltac:(let t := eval cbv delta [fmodeflags_spec__stmt] in fmodeflags_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'fmodeflags_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strchr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fmodeflags_entry := 0x9ac84%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFacts.
  Local Open Scope Z_scope.
  Notation M64 := 18446744073709551616.

  #[using="Type"] Lemma snez_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> (0 <? (v + k') mod M64) = negb (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - cbn [negb]. apply Z.ltb_lt. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma seqz_sub_byte : forall v k k', 0 <= v < 256 -> 0 <= k < 256 -> k + k' = 0 -> ((v + k') mod M64 <? 1) = (v =? k).
  Proof.
    intros v k k' Hv Hk Hkk. replace k' with (- k) by lia. destruct (Z.eqb_spec v k) as [->|NE].
    - replace (k + - k) with 0 by lia. reflexivity.
    - apply Z.ltb_ge. destruct (Z.lt_ge_cases v k).
      + replace (v + - k) with ((M64 + v - k) + (-1) * M64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma b2z_shiftl_mod : forall (b : bool) k, 0 <= k < 64 -> (Z.shiftl (Z.b2z b) k) mod M64 = Z.shiftl (Z.b2z b) k.
  Proof.
    intros b k Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 ^ k < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    destruct b; cbn [Z.b2z]; lia.
  Qed.

  #[using="Type"] Lemma strchr_res_found : forall A c str, 0 < A -> c <> 0 -> A + Z.of_nat (length str) < M64 ->
    (0 <? strchr_res A c str mod M64) = has_byte c str.
  Proof.
    intros A c str HA Hc HB. unfold strchr_res, has_byte.
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
    destruct (find_byte c str) as [i|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
    - reflexivity.
  Qed.
End ZFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fmodeflags_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fmodeflags str)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

(* [comment removed for export] *)
Local Ltac read_b0 STR FULL RD :=
  lazymatch type of STR with bytes_at _ ?mm (bv_unsigned ?a) _ =>
    pose proof (u8ro_read asegs mm (bv_unsigned a) _ 0 _ a STR ltac:(rewrite FULL; reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition fmodeflags_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 2256)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  (* [comment removed for export] *)
  (KHIGH <= lo)%Z -> icptenv m -> sobj RNG m (bv_unsigned a0) (bv_unsigned a0 + (Z.of_nat (length str) + 1)) ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ac84) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fmodeflags_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fmodeflags_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP A0 KLO ENV SO RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (RFR : rng RNG (bv_unsigned sp + -32) 32) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  destruct (str ++ Z_to_bv 8 0 :: slack) as [|b0 rest] eqn:FULL. { destruct str; discriminate. }
  rewrite <- FULL in STR, RSTR. pose proof (byte_range b0) as Rb0.
  assert (M0 : mode_m0 str = bv_unsigned b0). { destruct str; cbn in FULL; injection FULL; intros; subst; reflexivity. }
  carve_frame 32%nat ST.
  do 7 step.
  step. ienv_now ENV MU WM as ENVn. sobj_now SO MU WM as SOn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 43) mod 256) str) as IDXLE.
    call_sp strchr_wb_spec. all: icpt_prem RSTK.
    clear ENVn SOn IDXLE.
  rename PC into ST; clear STR; rename POST into STR.
  zstep.
  (* [comment removed for export] *)
  assert (JOIN : forall (s1v xa0 : word) mm,
    s1v = Z_to_bv 64 (if has_byte 43 str then 2 else Z.b2z (negb (mode_m0 str =? 114)))%Z ->
    mem_inv asegs mm -> munch [(bv_unsigned sp - 2256, bv_unsigned sp)]%Z m mm -> wmono asegs m mm ->
    rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
    stk asegs mm lo (bv_unsigned sp + -32) ->
    evtF asegs RNG (fmodeflags_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
      (MS (mkR (Z_to_bv 64 0x9aca4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x x0 x1 a0 s1v xa0 x2 x3 x4 x5 x6 x7 x8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x9 x10 x11 x12)
          F (Z_to_bv 64 0x9acbc) fc None mm (seg_rom asegs))).
  { clear dependent x13. intros s1v xa0 mm -> MI MU WM FR STR ST.
    zstep. zstep. step. ienv_now ENV MU WM as ENVn. sobj_now SO MU WM as SOn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 120) mod 256) str) as IDXLE.
    call_sp strchr_wb_spec. all: icpt_prem RSTK.
    clear ENVn SOn IDXLE.
    rename PC into ST; clear STR; rename POST into STR.
    zstep. zstep. zstep. zstep. step. ienv_now ENV MU WM as ENVn. sobj_now SO MU WM as SOn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 101) mod 256) str) as IDXLE.
    call_sp strchr_wb_spec. all: icpt_prem RSTK.
    clear ENVn SOn IDXLE.
    rename PC into ST; clear STR; rename POST into STR.
    zstep. read_b0 STR FULL RD.
    do 16 zstep.
    rewrite !b2z_shiftl_mod by lia.
    rewrite !(strchr_res_found (bv_unsigned a0)) by lia.
    rewrite !(snez_sub_byte (bv_unsigned b0) 114 (-114)), !(seqz_sub_byte (bv_unsigned b0) 119 (-119)), !(seqz_sub_byte (bv_unsigned b0) 97 (-97)) by lia.
    rewrite <- !M0.
    setreg 10%Z (Z_to_bv 64 (fmodeflags str)) ltac:(unfold fmodeflags, fmodeflags_w; destruct (has_byte 43 str); reflexivity).
    do 5 step. release_frame FR ST (bv_unsigned sp). step.
    unfold fmodeflags_post. finish. }
  if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    read_b0 STR FULL RD. zstep. zstep. zstep.
    eapply JOIN; try eassumption.
    rewrite (snez_sub_byte (bv_unsigned b0) 114 (-114)), <- M0 by lia.
    replace (has_byte 43 str) with false; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_ge. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
  - zstep. zstep.
    eapply JOIN; try eassumption.
    replace (has_byte 43 str) with true; [reflexivity|].
    rewrite <- (strchr_res_found (bv_unsigned a0)) by lia. symmetry. apply Z.ltb_lt. pose proof (Z.mod_pos_bound (strchr_res (bv_unsigned a0) 43 str) 18446744073709551616). lia.
Qed.
End Sz5.
#[using="Type"] Lemma fmodeflags_spec : ltac:(let t := eval cbv delta [fmodeflags_spec__stmt] in fmodeflags_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'fmodeflags_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_fmodeflags.

(* [comment removed for export] *)
Module I_strrchr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac F_rip. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_strrchr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition strrchr_i_entry := 0x45248%Z.

Definition strrchr_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S cc : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strrchr_res S cc str)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 4400, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section STRRCHR.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation cc := (bv_unsigned a1 mod 256)%Z.
  Notation L0 := (Z.of_nat (length str)).
  Notation N := (Z.of_nat (length str) + 1)%Z.
  Notation RES := (strrchr_res S cc str).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 4400)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis ENV : icptenv m.
  Hypothesis STR : bytes_at asegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis SEPB : (S + Z.of_nat (length full) <= lo \/ bv_unsigned sp <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length full)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strrchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m).
  Notation SAVES := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72)
    /\ munch [(bv_unsigned sp + -4400, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at asegs mc S full
    /\ icptenv mc.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 4400 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 4400 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & STR1 & ENV1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in STR; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -4400) 4400) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO ENV STR SEPB APP UNP NSZ R1 WR1"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72) ->
    munch [(bv_unsigned sp + -4400, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    assert (ENV1 : icptenv mc) by (eapply icptenv_transport; [exact ENV| exact MU1| exact WM1| solve_iesafe]).
    repeat (split; [assumption|]).
    split; [exact (ie_got _ ENV1)|]. split; [exact (ie_shb _ ENV1)|]. split; [exact (ie_lay _ ENV1)|].
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split; [| exact ENV1].
    eapply bytes_at_transport; [exact STR | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sregs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 N) x20 (Z_to_bv 64 0x140128) (Z_to_bv 64 (bv_unsigned sp + -2144)) x23 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO NONUL PAD SEPB APP NSZ R1 RI RSTK RB RSH1"] Lemma SX : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x452fc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    pose proof (ie_strrchr _ ENV1) as RSR1.
    do 4 zstep. zstep.
    unfold sf_hide in PAD, SEPB, LO, KLO, R1.
    call_sp strrchr_spec;
      [ exact ST1 | exact STR1 | exact NONUL | exact PAD | exact MI1 | clear -BL0; lia
      | rewrite length_app in SEPB; cbn [length] in SEPB; clear -SEPB BL0; lia
      | exact KLO | exact ENV1
      | split; [exact APP| split; [exact UNP1| split; [clear -NSZ; lia| exists RLO, RHI; split; [exact R1| split; [exact WR11| exact RSH1]]]]]
      | eapply rng_sub'; [exact RSTK | clear -BL0; lia] | ].
    do 12 zstep.
    pose proof (stk_merge _ _ _ _ _ PC STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -72 + Z.of_nat 72)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strrchr_i_post.
    replace (bv_unsigned sp - 4400)%Z with (bv_unsigned sp + -4400)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO NONUL PAD SEPB APP NSZ R1 RI RSTK RB RSH1"] Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
    SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x20 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45448) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO NONUL PAD SEPB APP NSZ R1 RI RSTK RB RSH1"] Lemma SE : forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4542c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SX; eassumption.
    - eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO ENV STR NONUL PAD SEPB APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma SC : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 x20 (Z_to_bv 64 0x140128) (Z_to_bv 64 (bv_unsigned sp + -2144)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x452b0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SX. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (L0 + S)%Z with (S + N + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SE; eassumption.
      + eapply SX; eassumption.
  Qed.

  #[using="RLO RHI MI ST LO KLO ENV STR NONUL PAD SEPB APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma strrchr_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x45248) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -4400, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ STR) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -4400) 4400) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0.
    pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_isl _ ENV) as ISLc.
    shide_all.
    carve_frame 72%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    assert (ISL1 : rw_cells asegs x13 0x140220 [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]).
    { pose proof ISLc as ISL'. recell ISL' 0%nat 1%nat [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]. exact ISL'. }
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    zstep. zstep. zstep. zstep.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str).
    { apply Forall_forall. intros b Hb E. apply NONUL. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    assert (STRn : bytes_at asegs x13 S full).
    { unfold sf_hide in STR, SEPB, LO. eapply bytes_at_transport; [exact STR | exact MU |]. cbn [disjoint_from]. clear -SEPB LO BL0. lia. }
    call istrlen_spec; [ eassumption | exact STRn | exact NZ
                       | eapply rng_sub'; [exact RB | rewrite length_app; cbn [length]; lia] | ].
    eapply SC. eapply sinv_of; eassumption.
  Qed.
End STRRCHR.

(* [comment removed for export] *)
#[using="Type"] Lemma strrchr_w_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4400)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  sobj RNG m S (S + N) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  evtF asegs RNG (strrchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S (bv_unsigned a1 mod 256) str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44478) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros S N MI ST LO KLO ENV STR NONUL PAD SEPB (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK RB.
  zstep. eapply (strrchr_i_body RNG) with (RLO := RLO) (RHI := RHI); try eassumption. subst N S. lia.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_irt.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_strrchr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition strrchr_i_entry := 0x452b0%Z.

Definition strrchr_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S cc : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strrchr_res S cc str)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 4400, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section STRRCHR.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation cc := (bv_unsigned a1 mod 256)%Z.
  Notation L0 := (Z.of_nat (length str)).
  Notation N := (Z.of_nat (length str) + 1)%Z.
  Notation RES := (strrchr_res S cc str).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 4400)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis ENV : icptenv m.
  Hypothesis STR : bytes_at asegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis SEPB : (S + Z.of_nat (length full) <= lo \/ bv_unsigned sp <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length full)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strrchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc str slack lo m).
  Notation SAVES := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72)
    /\ munch [(bv_unsigned sp + -4400, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at asegs mc S full
    /\ icptenv mc.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 4400 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 4400 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & STR1 & ENV1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in STR; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -4400) 4400) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO ENV STR SEPB APP UNP NSZ R1 WR1"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -72) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -72) ->
    munch [(bv_unsigned sp + -4400, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    assert (ENV1 : icptenv mc) by (eapply icptenv_transport; [exact ENV| exact MU1| exact WM1| solve_iesafe]).
    repeat (split; [assumption|]).
    split; [exact (ie_got _ ENV1)|]. split; [exact (ie_shb _ ENV1)|]. split; [exact (ie_lay _ ENV1)|].
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    split; [| exact ENV1].
    eapply bytes_at_transport; [exact STR | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sregs (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 N) x20 (Z_to_bv 64 0x140528) (Z_to_bv 64 (bv_unsigned sp + -2144)) x23 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO NONUL PAD SEPB APP NSZ R1 RI RSTK RB RSH1"] Lemma SX : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 x10 x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45364) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    pose proof (ie_strrchr _ ENV1) as RSR1.
    do 4 zstep. zstep.
    unfold sf_hide in PAD, SEPB, LO, KLO, R1.
    call_sp strrchr_spec;
      [ exact ST1 | exact STR1 | exact NONUL | exact PAD | exact MI1 | clear -BL0; lia
      | rewrite length_app in SEPB; cbn [length] in SEPB; clear -SEPB BL0; lia
      | exact KLO | exact ENV1
      | split; [exact APP| split; [exact UNP1| split; [clear -NSZ; lia| exists RLO, RHI; split; [exact R1| split; [exact WR11| exact RSH1]]]]]
      | eapply rng_sub'; [exact RSTK | clear -BL0; lia] | ].
    do 12 zstep.
    pose proof (stk_merge _ _ _ _ _ PC STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -72 + Z.of_nat 72)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strrchr_i_post.
    replace (bv_unsigned sp - 4400)%Z with (bv_unsigned sp + -4400)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO NONUL PAD SEPB APP NSZ R1 RI RSTK RB RSH1"] Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31,
    SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                                   x20 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x454b0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO NONUL PAD SEPB APP NSZ R1 RI RSTK RB RSH1"] Lemma SE : forall mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45494) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SX; eassumption.
    - eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO ENV STR NONUL PAD SEPB APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma SC : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 x20 (Z_to_bv 64 0x140528) (Z_to_bv 64 (bv_unsigned sp + -2144)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45318) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 3 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SX. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (L0 + S)%Z with (S + N + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SE; eassumption.
      + eapply SX; eassumption.
  Qed.

  #[using="RLO RHI MI ST LO KLO ENV STR NONUL PAD SEPB APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma strrchr_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x452b0) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -4400, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ STR) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -4400) 4400) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0.
    pose proof (ie_got _ ENV) as GOTc. pose proof (ie_ini _ ENV) as INIc. pose proof (ie_isl _ ENV) as ISLc.
    shide_all.
    carve_frame 72%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    assert (ISL1 : rw_cells asegs x13 0x140620 [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]).
    { pose proof ISLc as ISL'. recell ISL' 0%nat 1%nat [CB 5 (repeat (Z_to_bv 8 1) 5); C1 (Z_to_bv 8 1); CB 2 (repeat (Z_to_bv 8 1) 2)]. exact ISL'. }
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    zstep. zstep. zstep. zstep.
    assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str).
    { apply Forall_forall. intros b Hb E. apply NONUL. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
    assert (STRn : bytes_at asegs x13 S full).
    { unfold sf_hide in STR, SEPB, LO. eapply bytes_at_transport; [exact STR | exact MU |]. cbn [disjoint_from]. clear -SEPB LO BL0. lia. }
    call istrlen_spec; [ eassumption | exact STRn | exact NZ
                       | eapply rng_sub'; [exact RB | rewrite length_app; cbn [length]; lia] | ].
    eapply SC. eapply sinv_of; eassumption.
  Qed.
End STRRCHR.

(* [comment removed for export] *)
#[using="Type"] Lemma strrchr_w_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4400)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  sobj RNG m S (S + N) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  evtF asegs RNG (strrchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S (bv_unsigned a1 mod 256) str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444e0) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros S N MI ST LO KLO ENV STR NONUL PAD SEPB (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK RB.
  zstep. eapply (strrchr_i_body RNG) with (RLO := RLO) (RHI := RHI); try eassumption. subst N S. lia.
Qed.
End CANSEC1.
End TwB.
End I_strrchr.

(* [comment removed for export] *)
Module F_strerror_r.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg RtCells ShadowTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen I_strlen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Ltac sprem ENVn RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rt_inited _ => exact (ie_ini _ ENVn)
  | |- rt_real_strerror _ => exact (ie_strerror _ ENVn)
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
  | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RSTK | lia]]
  | |- _ => first [assumption | eassumption | unfold KHIGH; lia]
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition STRERROR_R_DEPTH : Z := 2272.

Definition strerror_r_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e : Z) (B n : Z) (junk : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2272, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' B [CB (length (strerror_msgb e) + 1) (strerror_msgb e ++ [Z_to_bv 8 0]);
                            CB (Z.to_nat n - (length (strerror_msgb e) + 1)) (skipn (length (strerror_msgb e) + 1) junk)].

Definition strerror_r_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (B n loc : Z) (junk : list byte) (lo k : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2272)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)] ->                          (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] ->               (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->            (* [comment removed for export] *)
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->                          (* [comment removed for export] *)
  rw_cells asegs m B [CB (Z.to_nat n) junk] ->                                (* [comment removed for export] *)
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 n -> (41 <= n < 2^40)%Z ->
  (0 <= k <= 1)%Z -> (48 <= bv_unsigned tp /\ bv_unsigned tp + 20 <= 0x5e24f0)%Z -> (0x5e14f0 <= bv_unsigned tp + -48)%Z ->   (* [comment removed for export] *)
  (bv_unsigned tp + 20 <= lo)%Z ->                                             (* [comment removed for export] *)
  (0x5e24f0 <= loc /\ loc + 48 <= 0x603000)%Z ->                                    (* [comment removed for export] *)
  (0x5e14f0 <= B)%Z -> (B + n <= 0x5e24f0)%Z -> (B + n <= lo)%Z ->   (* [comment removed for export] *)
  (B + n <= bv_unsigned tp - 48 \/ bv_unsigned tp + 20 <= B)%Z ->             (* [comment removed for export] *)
  sobj RNG m B (B + n) ->                                                      (* [comment removed for export] *)
  sobj RNG m 0x234bc 0x23d70 ->                                                (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (bv_unsigned tp + 16) 4 -> rng RNG (loc + 40) 8 -> rng RNG B n ->
  evtF asegs RNG (strerror_r_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e B n junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ed20) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo k : ltac2:(SecDiet.SzSec.tyM 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_r_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV GOTL CNT TLSL LOC DST -> He -> -> Hn K01 TPLO TPK TPHI Hloc BLO BK BHI SEPB SOB SOT RIMG RSTK RTL RCNT RLOC RB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_CB_length _ _ _ _ _ DST) as JL.
  pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (strerror_res_range e) as RR. pose proof (strerror_msgb_length e) as ML.
  unfold KHIGH in KLO.
  assert (IEB : iesafe [(B, B + n)%Z]) by (unfold iesafe; cbn [disjoint_from]; repeat split; lia).
  assert (APB : appW [(B, B + n)%Z]) by (exact (sobj_appW _ _ _ _ SOB)).
  carve_frame 32%nat ST.
  do 7 zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  zstep. call_sp strerror_w_spec. all: sprem ENVn RSTK.
  rename POST into ST. rename PC into CNTw. rename MI0 into MI1. clear ENVn.
  zstep.                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (strerror_msg_at x13 e MI1) as (MSG & NONUL & SL).
  rewrite <- (unsigned_lit (strerror_res e)) in MSG by lia.
  ienv_now ENV MU WM as ENVn. sobj_now SOT MU WM as SOTn.
  zstep. call_sp strlen_wb_spec.
  all: try (icpt_prem RSTK).
  all: lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- _ => rewrite ?(unsigned_lit (strerror_res e)) by lia; rewrite ?length_app; cbn [length]; rewrite ?SL;
                 first [ lia | left; lia | (eapply sobj_sub; [exact SOTn | lia | lia | lia]) | (eapply rng_sub'; [exact RIMG | lia])
                       | (Z.div_mod_to_equations; lia) ]
       end.
  rename PC into ST. clear ENVn SOTn. rename POST into MSG. rename MI into MI2.
  zstep. if_cases K; zify_cond K. { exfalso. lia. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  rewrite (unsigned_lit (strerror_res e)) in MSG by lia.
  pose proof MSG as MSG1.
  replace (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e) with ((strerror_msgb e ++ [Z_to_bv 8 0]) ++ strerror_slack e) in MSG1
    by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in MSG1. destruct MSG1 as [MSG1 _].
  apply (rw_cells_split_CB asegs _ _ [] _ _ [] [length (strerror_msgb e) + 1; Z.to_nat n - (length (strerror_msgb e) + 1)]%nat) in DST.
  2:{ cbn [sum_nat]. lia. }
  cbn [mk_CB_cells app] in DST. apply rw_cells_split2 in DST. destruct DST as [DST DST2]. cbn [csize] in DST2.
  set (N1 := (Z.of_nat (length (strerror_msgb e)) + 1)%Z) in *.
  assert (EN1 : Z.to_nat N1 = (length (strerror_msgb e) + 1)%nat) by (subst N1; lia).
  assert (HN1 : (1 <= N1 <= 41)%Z) by (subst N1; lia).
  rewrite <- EN1 in DST.
  ienv_now ENV MU WM as ENVn. sobj_now SOT MU WM as SOTn. sobj_now SOB MU WM as SOBn.
  assert (SOS : sobj RNG x28 (strerror_res e) (strerror_res e + N1)) by (eapply sobj_sub; [exact SOTn | lia | lia | lia]).
  assert (SOD : sobj RNG x28 B (B + N1)) by (eapply sobj_sub; [exact SOBn | lia | lia | lia]).
  assert (RSRC : rng RNG (strerror_res e) N1) by (eapply rng_sub'; [exact RIMG | lia]).
  assert (RDST : rng RNG B N1) by (eapply rng_sub'; [exact RB | lia]).
  zstep. call memcpy_wb_spec.
  1:{ exact MSG1. }
  1:{ rewrite length_app. cbn [length]. lia. }
  1:{ exact DST. }
  all: lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- mem_inv _ _ => exact MI2
       | |- stk _ _ _ _ => exact ST
       | |- icptenv _ => exact ENVn
       | |- sobj _ _ _ _ => first [exact SOS | exact SOD]
       | |- rng _ _ _ => eapply rng_sub'; [exact RSTK | lia]
       | |- (KHIGH <= _)%Z => unfold KHIGH; lia
       | |- _ => first [lia | left; lia | right; lia]
       end.
  rename PC into ST. rename PC0 into DSTn. clear POST.
  zstep. do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  rewrite EN1 in DSTn.
  lazymatch goal with H : rw_cells asegs ?mm (B + Z.of_nat (length (strerror_msgb e) + 1)) _ |- _ =>
    pose proof (rw_cells_join2 asegs mm B _ _ DSTn H) as DSTF end.
  rewrite firstn_all2 in DSTF by (rewrite length_skipn; lia).
  unfold strerror_r_post. finish.
Qed.
End Sz1.
#[using="Type"] Lemma strerror_r_spec : ltac:(let t := eval cbv delta [strerror_r_spec__stmt] in strerror_r_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo k. ltac2:(SecDiet.SzSec.closeP 'strerror_r_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Ltac sprem ENVn RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rt_inited _ => exact (ie_ini _ ENVn)
  | |- rt_real_strerror _ => exact (ie_strerror _ ENVn)
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
  | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RSTK | lia]]
  | |- _ => first [assumption | eassumption | unfold KHIGH; lia]
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition STRERROR_R_DEPTH : Z := 2272.

Definition strerror_r_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e : Z) (B n : Z) (junk : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2272, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' B [CB (length (strerror_msgb e) + 1) (strerror_msgb e ++ [Z_to_bv 8 0]);
                            CB (Z.to_nat n - (length (strerror_msgb e) + 1)) (skipn (length (strerror_msgb e) + 1) junk)].

Definition strerror_r_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (B n loc : Z) (junk : list byte) (lo k : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2272)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)] ->                          (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] ->               (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->            (* [comment removed for export] *)
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->                          (* [comment removed for export] *)
  rw_cells asegs m B [CB (Z.to_nat n) junk] ->                                (* [comment removed for export] *)
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 n -> (41 <= n < 2^40)%Z ->
  (0 <= k <= 1)%Z -> (48 <= bv_unsigned tp /\ bv_unsigned tp + 20 <= 0x5e28f0)%Z -> (0x5e18f0 <= bv_unsigned tp + -48)%Z ->   (* [comment removed for export] *)
  (bv_unsigned tp + 20 <= lo)%Z ->                                             (* [comment removed for export] *)
  (0x5e28f0 <= loc /\ loc + 48 <= 0x604000)%Z ->                                    (* [comment removed for export] *)
  (0x5e18f0 <= B)%Z -> (B + n <= 0x5e28f0)%Z -> (B + n <= lo)%Z ->   (* [comment removed for export] *)
  (B + n <= bv_unsigned tp - 48 \/ bv_unsigned tp + 20 <= B)%Z ->             (* [comment removed for export] *)
  sobj RNG m B (B + n) ->                                                      (* [comment removed for export] *)
  sobj RNG m 0x234bc 0x23d70 ->                                                (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (bv_unsigned tp + 16) 4 -> rng RNG (loc + 40) 8 -> rng RNG B n ->
  evtF asegs RNG (strerror_r_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e B n junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f104) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo k : ltac2:(SecDiet.SzSec.tyM 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_r_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV GOTL CNT TLSL LOC DST -> He -> -> Hn K01 TPLO TPK TPHI Hloc BLO BK BHI SEPB SOB SOT RIMG RSTK RTL RCNT RLOC RB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_CB_length _ _ _ _ _ DST) as JL.
  pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (strerror_res_range e) as RR. pose proof (strerror_msgb_length e) as ML.
  unfold KHIGH in KLO.
  assert (IEB : iesafe [(B, B + n)%Z]) by (unfold iesafe; cbn [disjoint_from]; repeat split; lia).
  assert (APB : appW [(B, B + n)%Z]) by (exact (sobj_appW _ _ _ _ SOB)).
  carve_frame 32%nat ST.
  do 7 zstep.
  (* [comment removed for export] *)
  ienv_now ENV MU WM as ENVn.
  zstep. call_sp strerror_w_spec. all: sprem ENVn RSTK.
  rename POST into ST. rename PC into CNTw. rename MI0 into MI1. clear ENVn.
  zstep.                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (strerror_msg_at x13 e MI1) as (MSG & NONUL & SL).
  rewrite <- (unsigned_lit (strerror_res e)) in MSG by lia.
  ienv_now ENV MU WM as ENVn. sobj_now SOT MU WM as SOTn.
  zstep. call_sp strlen_wb_spec.
  all: try (icpt_prem RSTK).
  all: lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- _ => rewrite ?(unsigned_lit (strerror_res e)) by lia; rewrite ?length_app; cbn [length]; rewrite ?SL;
                 first [ lia | left; lia | (eapply sobj_sub; [exact SOTn | lia | lia | lia]) | (eapply rng_sub'; [exact RIMG | lia])
                       | (Z.div_mod_to_equations; lia) ]
       end.
  rename PC into ST. clear ENVn SOTn. rename POST into MSG. rename MI into MI2.
  zstep. if_cases K; zify_cond K. { exfalso. lia. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  rewrite (unsigned_lit (strerror_res e)) in MSG by lia.
  pose proof MSG as MSG1.
  replace (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e) with ((strerror_msgb e ++ [Z_to_bv 8 0]) ++ strerror_slack e) in MSG1
    by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in MSG1. destruct MSG1 as [MSG1 _].
  apply (rw_cells_split_CB asegs _ _ [] _ _ [] [length (strerror_msgb e) + 1; Z.to_nat n - (length (strerror_msgb e) + 1)]%nat) in DST.
  2:{ cbn [sum_nat]. lia. }
  cbn [mk_CB_cells app] in DST. apply rw_cells_split2 in DST. destruct DST as [DST DST2]. cbn [csize] in DST2.
  set (N1 := (Z.of_nat (length (strerror_msgb e)) + 1)%Z) in *.
  assert (EN1 : Z.to_nat N1 = (length (strerror_msgb e) + 1)%nat) by (subst N1; lia).
  assert (HN1 : (1 <= N1 <= 41)%Z) by (subst N1; lia).
  rewrite <- EN1 in DST.
  ienv_now ENV MU WM as ENVn. sobj_now SOT MU WM as SOTn. sobj_now SOB MU WM as SOBn.
  assert (SOS : sobj RNG x28 (strerror_res e) (strerror_res e + N1)) by (eapply sobj_sub; [exact SOTn | lia | lia | lia]).
  assert (SOD : sobj RNG x28 B (B + N1)) by (eapply sobj_sub; [exact SOBn | lia | lia | lia]).
  assert (RSRC : rng RNG (strerror_res e) N1) by (eapply rng_sub'; [exact RIMG | lia]).
  assert (RDST : rng RNG B N1) by (eapply rng_sub'; [exact RB | lia]).
  zstep. call memcpy_wb_spec.
  1:{ exact MSG1. }
  1:{ rewrite length_app. cbn [length]. lia. }
  1:{ exact DST. }
  all: lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- mem_inv _ _ => exact MI2
       | |- stk _ _ _ _ => exact ST
       | |- icptenv _ => exact ENVn
       | |- sobj _ _ _ _ => first [exact SOS | exact SOD]
       | |- rng _ _ _ => eapply rng_sub'; [exact RSTK | lia]
       | |- (KHIGH <= _)%Z => unfold KHIGH; lia
       | |- _ => first [lia | left; lia | right; lia]
       end.
  rename PC into ST. rename PC0 into DSTn. clear POST.
  zstep. do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  rewrite EN1 in DSTn.
  lazymatch goal with H : rw_cells asegs ?mm (B + Z.of_nat (length (strerror_msgb e) + 1)) _ |- _ =>
    pose proof (rw_cells_join2 asegs mm B _ _ DSTn H) as DSTF end.
  rewrite firstn_all2 in DSTF by (rewrite length_skipn; lia).
  unfold strerror_r_post. finish.
Qed.
End Sz1.
#[using="Type"] Lemma strerror_r_spec : ltac:(let t := eval cbv delta [strerror_r_spec__stmt] in strerror_r_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo k. ltac2:(SecDiet.SzSec.closeP 'strerror_r_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_strerror_r.

(* [comment removed for export] *)
Module I_strerror_r.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_strerror_r.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac word_eq_tac ::=
  first [ exact eq_refl
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition strerror_r_i_entry := 0x48f10%Z.
Definition STRERROR_R_I_DEPTH : Z := 4400.

(* [comment removed for export] *)
Definition unpoisoned_zero_bytes__stmt : Prop := forall (m : word -> option byte) lo hi,
  unpoisoned m lo hi -> (lo mod 8 = 0)%Z -> (hi mod 8 = 0)%Z -> (lo < hi)%Z -> (hi <= 2^47)%Z ->
  shadow_bytes m (shad lo) (shad hi) (fun _ => 0%Z).
Section Sz1.
Variables m lo hi : ltac2:(SecDiet.SzSec.tyM 'unpoisoned_zero_bytes__stmt "vvv" @m).
#[using="Type"] Lemma unpoisoned_zero_bytes__body : ltac2:(SecDiet.SzSec.bodyP 'unpoisoned_zero_bytes__stmt "vvv").
Proof.
  intros (U0 & U1 & U) A1 A2 LT HI.
  rewrite !shad_div. unfold ASHOFF. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros s Hs. set (G := (s - 2147450880)%Z).
  destruct (U G LT ltac:(subst G; Z.div_mod_to_equations; lia) ltac:(subst G; Z.div_mod_to_equations; lia)) as (b & Hb & OK).
  unfold ASHOFF in Hb. replace (2147450880 + G)%Z with s in Hb by (subst G; lia). rewrite Hb. f_equal.
  apply (gran_ok_full _ _ OK). subst G. Z.div_mod_to_equations. lia.
Qed.
End Sz1.
#[using="Type"] Lemma unpoisoned_zero_bytes : ltac:(let t := eval cbv delta [unpoisoned_zero_bytes__stmt] in unpoisoned_zero_bytes__stmt in exact t).
Proof. intros m lo hi. ltac2:(SecDiet.SzSec.closeP 'unpoisoned_zero_bytes__body "vvv"). Qed.

(* [comment removed for export] *)
Definition isn_loop__stmt : Prop := forall RNG (Q : machine_state -> Prop) (m : word -> option byte) (B n : Z) (msg rest : list byte)
    sp gp tp x5 x6 x7 s0 s1 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32),
  bytes_at asegs m B (msg ++ Z_to_bv 8 0 :: rest) -> ~ In (Z_to_bv 8 0) msg -> (Z.of_nat (length msg) < n < 2^63)%Z ->
  rng RNG B (Z.of_nat (length msg) + 1) -> rng_aimg RNG ->
  (forall x13, evtF asegs RNG Q
     (MS (mkR (Z_to_bv 64 0x48f80) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (Z.of_nat (length msg))) (Z_to_bv 64 n) (Z_to_bv 64 B) x13 x14 x15 x16 x17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x48f80) fc None m (seg_rom asegs))) ->
  forall (k : nat) (i : Z) x13, Z.to_nat (Z.of_nat (length msg) - i) = k -> (0 <= i <= Z.of_nat (length msg))%Z ->
  evtF asegs RNG Q
     (MS (mkR (Z_to_bv 64 0x48f80) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 n) (Z_to_bv 64 B) x13 x14 x15 x16 x17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x67e5c) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG Q m B n msg rest sp gp tp x5 x6 x7 s0 s1 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc : ltac2:(SecDiet.SzSec.tyM 'isn_loop__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma isn_loop__body : ltac2:(SecDiet.SzSec.bodyP 'isn_loop__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros BA NONUL Hn RB RIMG CONT.
  pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_app in BB. cbn [length] in BB.
  induction k as [|k IH]; intros i x13 Hk Hi.
  - (* [comment removed for export] *)
    assert (Ei : i = Z.of_nat (length msg)) by lia. subst i.
    pose proof (bytes_at_read asegs m B (msg ++ Z_to_bv 8 0 :: rest) (Z.of_nat (length msg)) 1 BA ltac:(lia)
                  ltac:(rewrite length_app; cbn [length]; lia)) as RD.
    rewrite Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag in RD. cbn [app skipn firstn] in RD.
    zstep.
    zstep. rewrite ?unsigned_lit8 by lia.
    zstep. if_true. zstep.
    apply CONT.
  - (* [comment removed for export] *)
    assert (Hlt : (i < Z.of_nat (length msg))%Z) by lia.
    pose proof (bytes_at_read asegs m B (msg ++ Z_to_bv 8 0 :: rest) i 1 BA ltac:(lia)
                  ltac:(rewrite length_app; cbn [length]; lia)) as RD.
    rewrite skipn_app in RD. replace (Z.to_nat i - length msg)%nat with 0%nat in RD by lia. cbn [skipn] in RD.
    destruct (skipn (Z.to_nat i) msg) as [|b tl] eqn:ESK.
    { exfalso. apply (f_equal (@length byte)) in ESK. rewrite length_skipn in ESK. cbn [length] in ESK. lia. }
    cbn [app firstn] in RD.
    assert (Hb : b <> Z_to_bv 8 0).
    { intros ->. apply NONUL. rewrite <- (firstn_skipn (Z.to_nat i) msg). rewrite ESK. apply in_or_app. right. left. reflexivity. }
    zstep. zstep.
    zstep. if_cases K; zify_cond K.
    { exfalso. apply Hb. apply bv_eq. rewrite K. reflexivity. }
    zstep. zstep. if_cases K2; zify_cond K2.
    2:{ exfalso. lia. }
    apply IH; lia.
Qed.
End Sz2.
#[using="Type"] Lemma isn_loop : ltac:(let t := eval cbv delta [isn_loop__stmt] in isn_loop__stmt in exact t).
Proof. intros RNG Q m B n msg rest sp gp tp x5 x6 x7 s0 s1 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc. ltac2:(SecDiet.SzSec.closeP 'isn_loop__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition strerror_r_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e : Z) (B n : Z) (junk : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 4400, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' B [CB (length (strerror_msgb e) + 1) (strerror_msgb e ++ [Z_to_bv 8 0]);
                            CB (Z.to_nat n - (length (strerror_msgb e) + 1)) (skipn (length (strerror_msgb e) + 1) junk)].

(* [comment removed for export] *)
Ltac rprem ENVn RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- icptenv _ => exact ENVn
  | |- rt_inited _ => exact (ie_ini _ ENVn)
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- sobj _ _ _ _ => first [assumption | eassumption]
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
  | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RSTK | lia]]
  | |- _ => first [assumption | eassumption | unfold KHIGH; lia]
  end.

(* [comment removed for export] *)
Definition strerror_r_wb_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (B n loc : Z) (junk : list byte) (lo HLO HHI k : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4400)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)] ->                          (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] ->               (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->            (* [comment removed for export] *)
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->                          (* [comment removed for export] *)
  rw_cells asegs m B [CB (Z.to_nat n) junk] ->                                (* [comment removed for export] *)
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 n -> (41 <= n < 2^40)%Z ->
  (0 <= k <= 1)%Z -> (48 <= bv_unsigned tp /\ bv_unsigned tp + 20 <= 0x5e24f0)%Z -> (0x5e14f0 <= bv_unsigned tp + -48)%Z ->   (* [comment removed for export] *)
  (bv_unsigned tp + 20 <= lo)%Z ->                                             (* [comment removed for export] *)
  (0x5e24f0 <= loc /\ loc + 48 <= 0x603000)%Z ->                                    (* [comment removed for export] *)
  (0x5e14f0 <= B)%Z -> (B + n <= 0x5e24f0)%Z -> (B + n <= lo)%Z ->   (* [comment removed for export] *)
  (B + n <= bv_unsigned tp - 48 \/ bv_unsigned tp + 20 <= B)%Z ->             (* [comment removed for export] *)
  sobj RNG m B (B + n) ->                                                      (* [comment removed for export] *)
  sobj RNG m 0x234bc 0x23d70 ->                                                (* [comment removed for export] *)
  sobj RNG m HLO HHI -> (HLO mod 64 = 0)%Z -> (HHI mod 64 = 0)%Z -> (HLO <= B)%Z -> (B + 41 <= HHI)%Z ->   (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (bv_unsigned tp + 16) 4 -> rng RNG (loc + 40) 8 -> rng RNG B n ->
  evtF asegs RNG (strerror_r_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e B n junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444c4) fc None m (seg_rom asegs)).
Section Sz3.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo HLO HHI k : ltac2:(SecDiet.SzSec.tyM 'strerror_r_wb_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_r_wb_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_wb_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO ENV GOTL CNT TLSL LOC DST -> He -> -> Hn K01 TPLO TPK TPHI Hloc BLO BK BHI SEPB SOB SOT SOH HL64 HH64 HLB HHB
         RIMG RSTK RTL RCNT RLOC RB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (munch_refl [(bv_unsigned sp - 4400, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (strerror_res_range e) as RR. pose proof (strerror_msgb_length e) as ML.
  unfold KHIGH in KLO.
  assert (IEB : iesafe [(B, B + n)%Z]) by (unfold iesafe; cbn [disjoint_from]; repeat split; lia).
  assert (APB : appW [(B, B + n)%Z]) by (exact (sobj_appW _ _ _ _ SOB)).
  pose proof (ie_strerror _ ENV) as RSE. pose proof (ie_got _ ENV) as GOT. pose proof (ie_shb _ ENV) as SHB.
  zstep.
  carve_frame 56%nat ST.
  destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST ltac:(lia)) as [ST1 STM]. clear ST.
  do 13 zstep.
  ienv_now ENV MU WM as ENVn.
  zstep. call_sp tryinit_spec. all: rprem ENVn RSTK.
  rename PC into ST1'. clear POST.
  do 2 zstep. do 4 zstep.
  (* [comment removed for export] *)
  clear ENVn. ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOT MU WM as SOTn.
  zstep. call_sp (strerror_r_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e B n loc junk lo k). all: rprem ENVn RSTK.
  rename PC into ST1. rename POST into DSTF. rename MI into MI2. clear ENVn SOBn SOTn.
  zstep. if_false.                             (* [comment removed for export] *)
  do 5 zstep.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. if_cases KN; zify_cond KN. { exfalso. lia. }
  zstep. zstep.
  assert (BAF : bytes_at asegs x28 B (strerror_msgb e ++ Z_to_bv 8 0 :: skipn (length (strerror_msgb e) + 1) junk)).
  { destruct DSTF as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r, <- app_assoc in BA. exact BA. }
  assert (NONUL : ~ In (Z_to_bv 8 0) (strerror_msgb e)) by (destruct (strerror_msg_at x28 e MI2) as (_ & NN & _); exact NN).
  eapply (isn_loop RNG _ x28 B n (strerror_msgb e) (skipn (length (strerror_msgb e) + 1) junk)); 
    [ exact BAF | exact NONUL | lia | eapply rng_sub'; [exact RB | lia] | exact RIMG | | reflexivity | lia ].
  intros x13'.
  (* [comment removed for export] *)
  do 4 zstep.
  replace (Z.of_nat (length (strerror_msgb e)) <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0.
  { exfalso. lia. }
  clear K0.
  zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { exfalso. change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia.
    replace ((Z.of_nat (length (strerror_msgb e)) + -64) mod 2 ^ 64)%Z with (2^64 + (Z.of_nat (length (strerror_msgb e)) + -64))%Z in K2.
    - lia.
    - symmetry. replace (Z.of_nat (length (strerror_msgb e)) + -64)%Z with ((2^64 + (Z.of_nat (length (strerror_msgb e)) + -64)) + (-1) * 2^64)%Z at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  clear K2.
  (* [comment removed for export] *)
  do 4 zstep.
  do 7 zstep.
  assert (SH1 : (0 <= 2147450880 + Z.shiftr B 3 < 2^64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
  assert (SH2 : (0 <= 2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3 < 2^64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
  change 18446744073709551615%Z with (Z.ones 64). rewrite !Z.land_ones by lia.
  rewrite (Z.mod_small _ _ SH1), (Z.mod_small _ _ SH2).
  change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
  sobj_now SOH MU WM as SOHn.
  destruct SOHn as (APPH & UNPH & SZH & RLO & RHI & R1 & WRH & RSHH).
  assert (HH47 : (0 <= HLO /\ HHI <= 2^47)%Z) by (destruct APPH as [? [?|?]]; unfold KLOW, KHIGH, KEND in *; lia).
  pose proof (unpoisoned_zero_bytes x28 HLO HHI UNPH ltac:(clear -HL64; Z.div_mod_to_equations; lia) ltac:(clear -HH64; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as SBZ.
  rewrite !shad_div in SBZ. unfold ASHOFF in SBZ.
  assert (P1 : ov_read_bytes asegs x28 (wa (2147450880 + Z.shiftr B 3 - (2147450880 + Z.shiftr B 3) mod 8)) 8 = Some (le8 (Z_to_bv 64 0))).
  { apply (ov_read8_zero asegs x28 _ _ _ _ SBZ); [| | intros; reflexivity]; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
      clear -HL64 HH64 HLB HHB HH47 BLO; Z.div_mod_to_equations; lia. }
  assert (P2 : ov_read_bytes asegs x28 (wa (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3
                                             - (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3) mod 8)) 8 = Some (le8 (Z_to_bv 64 0))).
  { apply (ov_read8_zero asegs x28 _ _ _ _ SBZ); [| | intros; reflexivity]; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
      clear -HL64 HH64 HLB HHB HH47 BLO ML; Z.div_mod_to_equations; lia. }
  assert (ACC1 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr B 3 - (2147450880 + Z.shiftr B 3) mod 8), 8%nat)).
  { apply (rng_acc_litZ' RNG (shad RLO) (shad RHI - shad RLO) _ 8%nat 8 RSHH eq_refl eq_refl).
    rewrite !shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    clear -R1 HL64 HH64 HLB HHB HH47 BLO. Z.div_mod_to_equations. lia. }
  assert (ACC2 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3
                                             - (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3) mod 8), 8%nat)).
  { apply (rng_acc_litZ' RNG (shad RLO) (shad RHI - shad RLO) _ 8%nat 8 RSHH eq_refl eq_refl).
    rewrite !shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    clear -R1 HL64 HH64 HLB HHB HH47 BLO ML. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.                  (* [comment removed for export] *)
  zstep. if_false.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 10 zstep.
  pose proof (stk_merge _ _ _ _ _ ST1 STM ltac:(lia)) as SK.
  pose proof (stk_release _ _ _ _ _ SK FR ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
  replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
  apply evtF_done. unfold strerror_r_i_post.
  replace (bv_unsigned sp - 4400)%Z with (bv_unsigned sp + -4400)%Z by lia.
  do 15 eexists. split; [reflexivity|].
  split; [replace (bv_unsigned sp + -4400)%Z with (bv_unsigned sp - 4400)%Z by lia; exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact SK2|]. split; [assumption | exact DSTF].
Qed.
End Sz3.
#[using="Type"] Lemma strerror_r_wb_spec : ltac:(let t := eval cbv delta [strerror_r_wb_spec__stmt] in strerror_r_wb_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo HLO HHI k. ltac2:(SecDiet.SzSec.closeP 'strerror_r_wb_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_strerror_r.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Section CANSEC1. Context {rc : runConstT}.
Definition strerror_r_i_entry := 0x48f78%Z.
Definition STRERROR_R_I_DEPTH : Z := 4400.

(* [comment removed for export] *)
Definition unpoisoned_zero_bytes__stmt : Prop := forall (m : word -> option byte) lo hi,
  unpoisoned m lo hi -> (lo mod 8 = 0)%Z -> (hi mod 8 = 0)%Z -> (lo < hi)%Z -> (hi <= 2^47)%Z ->
  shadow_bytes m (shad lo) (shad hi) (fun _ => 0%Z).
Section Sz1.
Variables m lo hi : ltac2:(SecDiet.SzSec.tyM 'unpoisoned_zero_bytes__stmt "vvv" @m).
#[using="Type"] Lemma unpoisoned_zero_bytes__body : ltac2:(SecDiet.SzSec.bodyP 'unpoisoned_zero_bytes__stmt "vvv").
Proof.
  intros (U0 & U1 & U) A1 A2 LT HI.
  rewrite !shad_div. unfold ASHOFF. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros s Hs. set (G := (s - 2147450880)%Z).
  destruct (U G LT ltac:(subst G; Z.div_mod_to_equations; lia) ltac:(subst G; Z.div_mod_to_equations; lia)) as (b & Hb & OK).
  unfold ASHOFF in Hb. replace (2147450880 + G)%Z with s in Hb by (subst G; lia). rewrite Hb. f_equal.
  apply (gran_ok_full _ _ OK). subst G. Z.div_mod_to_equations. lia.
Qed.
End Sz1.
#[using="Type"] Lemma unpoisoned_zero_bytes : ltac:(let t := eval cbv delta [unpoisoned_zero_bytes__stmt] in unpoisoned_zero_bytes__stmt in exact t).
Proof. intros m lo hi. ltac2:(SecDiet.SzSec.closeP 'unpoisoned_zero_bytes__body "vvv"). Qed.

(* [comment removed for export] *)
Definition isn_loop__stmt : Prop := forall RNG (Q : machine_state -> Prop) (m : word -> option byte) (B n : Z) (msg rest : list byte)
    sp gp tp x5 x6 x7 s0 s1 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32),
  bytes_at asegs m B (msg ++ Z_to_bv 8 0 :: rest) -> ~ In (Z_to_bv 8 0) msg -> (Z.of_nat (length msg) < n < 2^63)%Z ->
  rng RNG B (Z.of_nat (length msg) + 1) -> rng_aimg RNG ->
  (forall x13, evtF asegs RNG Q
     (MS (mkR (Z_to_bv 64 0x48fe8) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (Z.of_nat (length msg))) (Z_to_bv 64 n) (Z_to_bv 64 B) x13 x14 x15 x16 x17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x48fe8) fc None m (seg_rom asegs))) ->
  forall (k : nat) (i : Z) x13, Z.to_nat (Z.of_nat (length msg) - i) = k -> (0 <= i <= Z.of_nat (length msg))%Z ->
  evtF asegs RNG Q
     (MS (mkR (Z_to_bv 64 0x48fe8) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 n) (Z_to_bv 64 B) x13 x14 x15 x16 x17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x67ec4) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG Q m B n msg rest sp gp tp x5 x6 x7 s0 s1 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc : ltac2:(SecDiet.SzSec.tyM 'isn_loop__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma isn_loop__body : ltac2:(SecDiet.SzSec.bodyP 'isn_loop__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros BA NONUL Hn RB RIMG CONT.
  pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_app in BB. cbn [length] in BB.
  induction k as [|k IH]; intros i x13 Hk Hi.
  - (* [comment removed for export] *)
    assert (Ei : i = Z.of_nat (length msg)) by lia. subst i.
    pose proof (bytes_at_read asegs m B (msg ++ Z_to_bv 8 0 :: rest) (Z.of_nat (length msg)) 1 BA ltac:(lia)
                  ltac:(rewrite length_app; cbn [length]; lia)) as RD.
    rewrite Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag in RD. cbn [app skipn firstn] in RD.
    zstep.
    zstep. rewrite ?unsigned_lit8 by lia.
    zstep. if_true. zstep.
    apply CONT.
  - (* [comment removed for export] *)
    assert (Hlt : (i < Z.of_nat (length msg))%Z) by lia.
    pose proof (bytes_at_read asegs m B (msg ++ Z_to_bv 8 0 :: rest) i 1 BA ltac:(lia)
                  ltac:(rewrite length_app; cbn [length]; lia)) as RD.
    rewrite skipn_app in RD. replace (Z.to_nat i - length msg)%nat with 0%nat in RD by lia. cbn [skipn] in RD.
    destruct (skipn (Z.to_nat i) msg) as [|b tl] eqn:ESK.
    { exfalso. apply (f_equal (@length byte)) in ESK. rewrite length_skipn in ESK. cbn [length] in ESK. lia. }
    cbn [app firstn] in RD.
    assert (Hb : b <> Z_to_bv 8 0).
    { intros ->. apply NONUL. rewrite <- (firstn_skipn (Z.to_nat i) msg). rewrite ESK. apply in_or_app. right. left. reflexivity. }
    zstep. zstep.
    zstep. if_cases K; zify_cond K.
    { exfalso. apply Hb. apply bv_eq. rewrite K. reflexivity. }
    zstep. zstep. if_cases K2; zify_cond K2.
    2:{ exfalso. lia. }
    apply IH; lia.
Qed.
End Sz2.
#[using="Type"] Lemma isn_loop : ltac:(let t := eval cbv delta [isn_loop__stmt] in isn_loop__stmt in exact t).
Proof. intros RNG Q m B n msg rest sp gp tp x5 x6 x7 s0 s1 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc. ltac2:(SecDiet.SzSec.closeP 'isn_loop__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition strerror_r_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e : Z) (B n : Z) (junk : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 4400, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' B [CB (length (strerror_msgb e) + 1) (strerror_msgb e ++ [Z_to_bv 8 0]);
                            CB (Z.to_nat n - (length (strerror_msgb e) + 1)) (skipn (length (strerror_msgb e) + 1) junk)].

(* [comment removed for export] *)
Ltac rprem ENVn RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- icptenv _ => exact ENVn
  | |- rt_inited _ => exact (ie_ini _ ENVn)
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- sobj _ _ _ _ => first [assumption | eassumption]
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
  | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RSTK | lia]]
  | |- _ => first [assumption | eassumption | unfold KHIGH; lia]
  end.

(* [comment removed for export] *)
Definition strerror_r_wb_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (B n loc : Z) (junk : list byte) (lo HLO HHI k : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4400)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)] ->                          (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] ->               (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->            (* [comment removed for export] *)
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->                          (* [comment removed for export] *)
  rw_cells asegs m B [CB (Z.to_nat n) junk] ->                                (* [comment removed for export] *)
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 n -> (41 <= n < 2^40)%Z ->
  (0 <= k <= 1)%Z -> (48 <= bv_unsigned tp /\ bv_unsigned tp + 20 <= 0x5e28f0)%Z -> (0x5e18f0 <= bv_unsigned tp + -48)%Z ->   (* [comment removed for export] *)
  (bv_unsigned tp + 20 <= lo)%Z ->                                             (* [comment removed for export] *)
  (0x5e28f0 <= loc /\ loc + 48 <= 0x604000)%Z ->                                    (* [comment removed for export] *)
  (0x5e18f0 <= B)%Z -> (B + n <= 0x5e28f0)%Z -> (B + n <= lo)%Z ->   (* [comment removed for export] *)
  (B + n <= bv_unsigned tp - 48 \/ bv_unsigned tp + 20 <= B)%Z ->             (* [comment removed for export] *)
  sobj RNG m B (B + n) ->                                                      (* [comment removed for export] *)
  sobj RNG m 0x234bc 0x23d70 ->                                                (* [comment removed for export] *)
  sobj RNG m HLO HHI -> (HLO mod 64 = 0)%Z -> (HHI mod 64 = 0)%Z -> (HLO <= B)%Z -> (B + 41 <= HHI)%Z ->   (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (bv_unsigned tp + 16) 4 -> rng RNG (loc + 40) 8 -> rng RNG B n ->
  evtF asegs RNG (strerror_r_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e B n junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4452c) fc None m (seg_rom asegs)).
Section Sz3.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo HLO HHI k : ltac2:(SecDiet.SzSec.tyM 'strerror_r_wb_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_r_wb_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_wb_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros MI ST LO KLO ENV GOTL CNT TLSL LOC DST -> He -> -> Hn K01 TPLO TPK TPHI Hloc BLO BK BHI SEPB SOB SOT SOH HL64 HH64 HLB HHB
         RIMG RSTK RTL RCNT RLOC RB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (munch_refl [(bv_unsigned sp - 4400, bv_unsigned sp); (B, B + n); (bv_unsigned tp + 16, bv_unsigned tp + 20)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (strerror_res_range e) as RR. pose proof (strerror_msgb_length e) as ML.
  unfold KHIGH in KLO.
  assert (IEB : iesafe [(B, B + n)%Z]) by (unfold iesafe; cbn [disjoint_from]; repeat split; lia).
  assert (APB : appW [(B, B + n)%Z]) by (exact (sobj_appW _ _ _ _ SOB)).
  pose proof (ie_strerror _ ENV) as RSE. pose proof (ie_got _ ENV) as GOT. pose proof (ie_shb _ ENV) as SHB.
  zstep.
  carve_frame 56%nat ST.
  destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST ltac:(lia)) as [ST1 STM]. clear ST.
  do 13 zstep.
  ienv_now ENV MU WM as ENVn.
  zstep. call_sp tryinit_spec. all: rprem ENVn RSTK.
  rename PC into ST1'. clear POST.
  do 2 zstep. do 4 zstep.
  (* [comment removed for export] *)
  clear ENVn. ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOT MU WM as SOTn.
  zstep. call_sp (strerror_r_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e B n loc junk lo k). all: rprem ENVn RSTK.
  rename PC into ST1. rename POST into DSTF. rename MI into MI2. clear ENVn SOBn SOTn.
  zstep. if_false.                             (* [comment removed for export] *)
  do 5 zstep.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. if_cases KN; zify_cond KN. { exfalso. lia. }
  zstep. zstep.
  assert (BAF : bytes_at asegs x28 B (strerror_msgb e ++ Z_to_bv 8 0 :: skipn (length (strerror_msgb e) + 1) junk)).
  { destruct DSTF as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r, <- app_assoc in BA. exact BA. }
  assert (NONUL : ~ In (Z_to_bv 8 0) (strerror_msgb e)) by (destruct (strerror_msg_at x28 e MI2) as (_ & NN & _); exact NN).
  eapply (isn_loop RNG _ x28 B n (strerror_msgb e) (skipn (length (strerror_msgb e) + 1) junk)); 
    [ exact BAF | exact NONUL | lia | eapply rng_sub'; [exact RB | lia] | exact RIMG | | reflexivity | lia ].
  intros x13'.
  (* [comment removed for export] *)
  do 4 zstep.
  replace (Z.of_nat (length (strerror_msgb e)) <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0.
  { exfalso. lia. }
  clear K0.
  zstep. zstep. zstep. if_cases K2; zify_cond K2.
  { exfalso. change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite Z.land_ones in K2 by lia.
    replace ((Z.of_nat (length (strerror_msgb e)) + -64) mod 2 ^ 64)%Z with (2^64 + (Z.of_nat (length (strerror_msgb e)) + -64))%Z in K2.
    - lia.
    - symmetry. replace (Z.of_nat (length (strerror_msgb e)) + -64)%Z with ((2^64 + (Z.of_nat (length (strerror_msgb e)) + -64)) + (-1) * 2^64)%Z at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  clear K2.
  (* [comment removed for export] *)
  do 4 zstep.
  do 7 zstep.
  assert (SH1 : (0 <= 2147450880 + Z.shiftr B 3 < 2^64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
  assert (SH2 : (0 <= 2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3 < 2^64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
  change 18446744073709551615%Z with (Z.ones 64). rewrite !Z.land_ones by lia.
  rewrite (Z.mod_small _ _ SH1), (Z.mod_small _ _ SH2).
  change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
  sobj_now SOH MU WM as SOHn.
  destruct SOHn as (APPH & UNPH & SZH & RLO & RHI & R1 & WRH & RSHH).
  assert (HH47 : (0 <= HLO /\ HHI <= 2^47)%Z) by (destruct APPH as [? [?|?]]; unfold KLOW, KHIGH, KEND in *; lia).
  pose proof (unpoisoned_zero_bytes x28 HLO HHI UNPH ltac:(clear -HL64; Z.div_mod_to_equations; lia) ltac:(clear -HH64; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as SBZ.
  rewrite !shad_div in SBZ. unfold ASHOFF in SBZ.
  assert (P1 : ov_read_bytes asegs x28 (wa (2147450880 + Z.shiftr B 3 - (2147450880 + Z.shiftr B 3) mod 8)) 8 = Some (le8 (Z_to_bv 64 0))).
  { apply (ov_read8_zero asegs x28 _ _ _ _ SBZ); [| | intros; reflexivity]; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
      clear -HL64 HH64 HLB HHB HH47 BLO; Z.div_mod_to_equations; lia. }
  assert (P2 : ov_read_bytes asegs x28 (wa (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3
                                             - (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3) mod 8)) 8 = Some (le8 (Z_to_bv 64 0))).
  { apply (ov_read8_zero asegs x28 _ _ _ _ SBZ); [| | intros; reflexivity]; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
      clear -HL64 HH64 HLB HHB HH47 BLO ML; Z.div_mod_to_equations; lia. }
  assert (ACC1 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr B 3 - (2147450880 + Z.shiftr B 3) mod 8), 8%nat)).
  { apply (rng_acc_litZ' RNG (shad RLO) (shad RHI - shad RLO) _ 8%nat 8 RSHH eq_refl eq_refl).
    rewrite !shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    clear -R1 HL64 HH64 HLB HHB HH47 BLO. Z.div_mod_to_equations. lia. }
  assert (ACC2 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3
                                             - (2147450880 + Z.shiftr (B + (Z.of_nat (length (strerror_msgb e)) + 1) + -1) 3) mod 8), 8%nat)).
  { apply (rng_acc_litZ' RNG (shad RLO) (shad RHI - shad RLO) _ 8%nat 8 RSHH eq_refl eq_refl).
    rewrite !shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    clear -R1 HL64 HH64 HLB HHB HH47 BLO ML. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. zstep.                  (* [comment removed for export] *)
  zstep. if_false.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 10 zstep.
  pose proof (stk_merge _ _ _ _ _ ST1 STM ltac:(lia)) as SK.
  pose proof (stk_release _ _ _ _ _ SK FR ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
  replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
  apply evtF_done. unfold strerror_r_i_post.
  replace (bv_unsigned sp - 4400)%Z with (bv_unsigned sp + -4400)%Z by lia.
  do 15 eexists. split; [reflexivity|].
  split; [replace (bv_unsigned sp + -4400)%Z with (bv_unsigned sp - 4400)%Z by lia; exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact SK2|]. split; [assumption | exact DSTF].
Qed.
End Sz3.
#[using="Type"] Lemma strerror_r_wb_spec : ltac:(let t := eval cbv delta [strerror_r_wb_spec__stmt] in strerror_r_wb_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e B n loc junk lo HLO HHI k. ltac2:(SecDiet.SzSec.closeP 'strerror_r_wb_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End I_strerror_r.

(* [comment removed for export] *)
Module F_vfprintf_sn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep FP ITree Nodes Decode StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface F_printf_core. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
(* [comment removed for export] *)
Local Ltac acc_enrich ::=
  repeat match goal with
  | H : nth_error ?l ?k = Some ?x |- _ =>
      lazymatch goal with
      | _ : (k < length l)%nat |- _ => fail
      | _ => pose proof (nth_error_some_bound l k x H)
      end
  end;
  (tryif (match goal with
          | H : context [length (u32s _)] |- _ => idtac
          | H : context [length (u64s _)] |- _ => idtac
          | H : context [length (_ ++ _)] |- _ => idtac
          | H : context [length (repeat _ _)] |- _ => idtac
          | |- context [length (u32s _)] => idtac
          | |- context [length (u64s _)] => idtac
          | |- context [length (_ ++ _)] => idtac
          | |- context [length (repeat _ _)] => idtac
          end)
   then rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length in *
   else idtac);
  cbn [length] in *.
Local Ltac acc_hint ::= first [ progress (unfold wa); solve_acc1   (* [comment removed for export] *)
  (* [comment removed for export] *)
  | lazymatch goal with
    | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
        let X := leftmost E in is_var X;
        tryif (match goal with H : rng RNG X _ |- _ => idtac end) then fail else
        tryif (match goal with H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X] end) then fail else
        match goal with H : rng RNG ?lo ?len |- _ => lazymatch len with context [bv_unsigned _] => solve_acc_with H end end
    end ].
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells asegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x9aee0.
Definition TOWRITE : Z := 0x9ac80.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition towrite_sn__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp bufp bufsize CK : Z) (md : word) (wend wpos wbase : Z),
  a0 = Z_to_bv 64 Fp ->
  rw_cells asegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  (0 <= bufp) -> (bufp + bufsize < 2^64) -> (0 <= bufsize) -> mem_inv asegs m ->
  rng RNG Fp 232 ->
  evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (md' : word) (m' : mem),
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
               /\ rw_cells asegs m' Fp (snfile_cells (bufp + bufsize) bufp bufp bufp bufsize md' CK))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TOWRITE) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase : ltac2:(SecDiet.SzSec.tyM 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma towrite_sn__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> FC B0 BHI BS0 MI RFP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite snfile_cells_size in FB.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold snfile_cells in FC. unfold TOWRITE.
  do 5 zs. zs. zs. first [if_lit | brf K0; [exfalso; revert K0; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]].
  do 10 zs.
  apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  unfold snfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "TW:" t end; fail] end.
Qed.
End Sz1.
Lemma towrite_sn : ltac:(let t := eval cbv delta [towrite_sn__stmt] in towrite_sn__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase. ltac2:(SecDiet.SzSec.closeP 'towrite_sn__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vf : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

(* [comment removed for export] *)
Definition arg_ok_vf__stmt : Prop := forall RNG Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS RNG m lo sp ap w a -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS RNG m' lo sp' ap w a.
Section Sz3.
Variables RNG Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vf__stmt "vvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma arg_ok_vf__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vf__stmt "vvvvvvvvvvvvvv").
Proof.
  intros H Hsp MU WM AW HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47 & RGs & SOs). exists slack.
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact (sobj_transport _ _ _ _ _ _ SOs MU WM AW)].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vf; [exact HW | | | | lia]; lia.
Qed.
End Sz3.
Lemma arg_ok_vf : ltac:(let t := eval cbv delta [arg_ok_vf__stmt] in arg_ok_vf__stmt in exact t).
Proof. intros RNG Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vf__body "vvvvvvvvvvvvvv"). Qed.
Lemma args_ok_vf : forall RNG Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS RNG m lo sp ap ws args -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS RNG m' lo sp' ap ws args.
Proof.
  intros RNG Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU WM AW HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma sobj_empty0 : forall RNG (m : mem), rng0 RNG -> sobj RNG m 0 0.
Proof.
  intros RNG m R0. split; [unfold app_blk, KLOW; lia|]. split; [split; [lia|]; split; [lia|]; intros G HG; lia|]. split; [lia|].
  exists 0, 0. split; [unfold KEND; repeat split; lia|].
  split; [split; [rewrite shad_div; unfold ASHOFF; lia|]; split; [rewrite shad_div; unfold ASHOFF; lia|]; intros i Hi; lia|].
  replace (shad 0 - shad 0) with 0 by lia. apply rng0_use; [exact R0|]. rewrite shad_div. unfold ASHOFF. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D cap : Z) (dn : nat) (out : list Z) (r lo : Z) (canary : word) (icf : list cell) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fj jd' : list byte) (m' : mem),
    let q := bv_unsigned sp in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q + 296); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' D [CB dn (zb (firstn (Z.to_nat cap) out) ++ Z_to_bv 8 0 :: jd')]
    /\ rw_cells asegs m' q icf
    /\ rw_cells asegs m' (q + 48) [CB 248 fj]
    /\ 0 <= r <= 2147483647.   (* [comment removed for export] *)

Section Vfprintf.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D cap : Z) (dn : nat) (A VA qtop lo bufp0 : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word) (icf : list cell).
  Let q := bv_unsigned sp.
  Hypothesis DN : Z.of_nat dn = cap + 1.
  Hypothesis CAP0 : 0 <= cap.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QTOP : q + 296 <= qtop.
  Hypothesis QHI : qtop <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : qtop <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis BUFP0 : 0 < bufp0 < 2^64.
  Hypothesis HD : 0 < D /\ D + Z.of_nat dn <= 2^63 /\ (D + Z.of_nat dn <= 0x10000 \/ 0x603000 <= D)
                  /\ (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D \/ (qtop <= D /\ D + Z.of_nat dn <= VA)).
  (* [comment removed for export] *)
  Hypothesis ICF : cells_size icf = 48%nat.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + Z.of_nat dn)].
  Hypothesis RSTK : rng RNG lo (q + 296 - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RD : rng RNG D (Z.of_nat dn).
  Hypothesis R0 : rng0 RNG.   (* [comment removed for export] *)

  Definition vfprintf_sn_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte) (Fp : Z),
    q + 48 = Fp ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (snfile_cells 0 0 0 bufp0 0 (Z_to_bv 64 0) (Fp + 232)) ->
    rw_cells asegs m (Fp + 232) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 cap)] ->
    rw_cells asegs m D [CB dn jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 352) SN_FS D (Z.of_nat dn) RNG m lo qtop (q - 368) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    rw_cells asegs m q icf ->
    icptenv m -> sobj RNG m lo (q + 296) -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D cap dn (concat ps) r lo canary icf m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp : ltac2:(SecDiet.SzSec.tyM 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP ICF KLO IESD RSTK RIMG RVA RD R0. pin_using (fun (BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP ICF KLO IESD RSTK RIMG RVA RD R0 : unit) => tt).
    intros EFP -> -> -> FC0 CKC0 DST0 BY VAA AOK ST SSP MI FRM ICC ENV SOSTK SOFMT SOPFX SOD.
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST0) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + Z.of_nat dn <= lo \/ bv_unsigned sp + 296 <= D) by (clear -HD HVA QTOP NNs; lia).
    assert (DHI : 0 < D /\ D + Z.of_nat dn <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl asegs m) as WM.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash FC0. stash CKC0. stash DST0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0, CKC0, DST0, HD.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call asegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp + 296); (D, D + Z.of_nat dn)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      assert (MU1 : munch [(lo, bv_unsigned sp + 296)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]
    end.
    clear MUp. stash HD. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evtF_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia
        | eapply rng_sub'; [exact RSTK | lia] | exact RIMG | eapply rng_sub'; [exact RIMG | lia] ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    unfold snfile_cells in FC0.
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in *. zs. rewrite ?unsigned_lit by lia. change (Z.land 0 18446744073709551583) with 0.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (Bi := bv_unsigned sp + -352) in *.
    eapply evtF_cut.
    { eapply (towrite_sn RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fp Bi 80 (Fp + 232) (Z_to_bv 64 0) 0 0 0);
        [ reflexivity | unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end | lia | lia | lia | assumption
        | eapply rng_sub'; [exact RSTK | lia] ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & md & m'' & -> & MUc & WMc & MIt & FC1).
    match goal with H : rw_cells _ ?mm Fp (_ :: _) |- _ => clear H end.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    do 5 zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB asegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc Bi. readdr FRv (Bi + 80)%Z. readdr AP2 (bv_unsigned sp + -360)%Z.
    match type of IBc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in IBc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ IBc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    (* [comment removed for export] *)
    lazymatch type of FRv with rw_cells _ ?mm _ ?fr =>
      assert (FRI : rw_cells asegs mm (Bi + 80) (fr ++ icf))
        by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRv | eapply rwc_eqA; [exact ICC | cbn [cells_size csize Nat.add]; subst Bi; lia]]);
      assert (FRL0 : cells_size (fr ++ icf) = 320%nat) by (rewrite cells_size_app, ICF; reflexivity);
      set (frest := fr ++ icf) in FRI, FRL0 end.
    clear FRv ICC. rename FRI into FRv.
    unfold hide in HD.
    assert (SNK : SINK_sn Bi md frest D cap dn m'' []).
    { exists [], [], jb, jd, Bi, D, cap. cbv zeta. unfold SN_FOFF, SN_FS. rewrite !firstn_nil.
      split; [reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split. { replace (Bi + 400) with Fp by lia. replace (Bi + 400 + 232) with (Fp + 232) by lia. exact FC1. }
      split; [cbn [zb map app]; exact IBc|].
      split; [exact FRv|]. split; [exact FRL0|].
      split. { replace (Bi + 400 + 232) with (Fp + 232) by lia. exact CKC0. }
      split; [cbn [zb map app]; exact DST0|].
      clear -DN CAP0 GLO LO HD SPHI QTOP QHI HVA EFP. subst Bi. repeat (split; [lia|]). lia. }
    (* [comment removed for export] *)
    assert (PCALL : forall Q ms, implXM px_atn px_sil px_npk px_fst RNG (printf_model OUT_app fmtz args) [] Q ms -> evtF asegs RNG (Q r (concat ps)) ms).
    { intros Q ms H. eapply implXM_pure_evtF; [| exact H]. rewrite (printf_model_app _ _ _ _ [] PIECES). reflexivity. }
    pose proof (printf_core_proof px_atn px_sil px_npk px_fst (list Z) Bi SN_FS (Bi + SN_FOFF) D (Z.of_nat dn) (SINK_sn Bi md frest D cap dn) (TOPOK_sn Bi) OUT_app
                  (sn_sink_frame Bi md frest D cap dn) (sn_sink_flags Bi md frest D cap dn) (sn_topok Bi) (sn_out Bi md frest D cap dn)) as PC2.
    unfold printf_core_stmt in PC2.
    unfold hide in AOK. try clear BY. try clear VAA.
    assert (BY : bytes_at asegs m'' A (zb fmtz)).
    { unfold hide in BYm. eapply bytes_at_transport; [exact BYm | exact MU1 | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia]. }
    assert (VAA : va_area m'' VA slots).
    { unfold hide in VAAm. unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]. }
    eapply evtF_cut.
    { apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots); clear PC2 PCALL; rewrite ?unsigned_lit by lia;
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_sn, SN_FS, SN_FOFF, zlength.
      - exact SNK.
      - exact BY.
      - exact HF.
      - f_equal. subst Bi. lia.
      - exact APC.
      - exact VAA.
      - lia.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | subst Bi; lia | exact MU1 | exact WM | solve_appW |].
        constructor; [cbn [fst snd]; left; lia | constructor].
      - exact STc.
      - lia.
      - lia.
      - lia.
      - subst Bi; lia.
      - unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM.
      - lia.
      - lia.
      - subst Bi; lia.
      - right; left. subst Bi. clear -HVA QTOP SPHI LO GLO. lia.
      - clear -HD DHI LO GLO QTOP SPHI. destruct HD as (HD1 & HD1' & HD2 & [HD3 | [HD3 | HD3]]);
          [right; right; left; lia | right; right; right; lia | right; left; lia].
      - lia.
      - clear -HVA QTOP SPHI. lia.
      - lia.
      - exact KLO.
      - eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe].
      - eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [exact SOFMT | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [exact SOPFX | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | subst Bi; lia | lia | subst Bi; lia] | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [exact SOD | exact MU | exact WM | solve_appW].
      - eapply rng_sub'; [exact RSTK | lia].
      - exact RIMG.
      - eapply rng_sub'; [exact RSTK | lia].
      - exact RVA.
      - eapply rng_sub'; [exact RSTK | subst Bi; lia].
      - exact RD.
      - eapply rng_sub'; [exact RIMG | lia]. }
    cbv beta. intros ms' PO. clear PC2 PCALL.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    subst fc' Ft.
    unfold SR, SN_FS in MUc. cbn [app] in MUc.
    clear SNK APC IBc FRv FC1 CKC0 DST0 AOK VAA BY MU1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    destruct SNK3 as (P & o & jb3 & jd3 & wp & cs & cn & SNK3). cbv zeta in SNK3.
    destruct SNK3 as (ET & LO80 & Ewp & Ecs & Ecn & FC3 & IB3 & FR3 & FRL & CKC3 & DST3 & _).
    unfold SN_FOFF in FC3, CKC3. readdr FC3 Fp. readdr CKC3 (Fp + 232)%Z.
    replace (Bi + 400 + 232) with (Fp + 232) in FC3 by lia.
    pose proof (rw_CB_length _ _ _ _ IB3) as LJ3. rewrite length_app, zb_length in LJ3.
    assert (NNo : 0 <= zlength o <= 80) by (unfold zlength in *; clear -LJ3; lia).
    unfold snfile_cells in FC3.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf Kb; [exfalso; clear -Kb BUFP0; rewrite ?unsigned_lit in Kb by lia; lia|].
    zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : rw_cells _ mm Fp (_ :: _) |- _ =>
        destruct (snfile_split mm Fp _ _ _ _ _ _ _ H) as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160); clear H end end.
    cbn [firstn skipn snfile_cells] in G0, G96.
    rewrite Ewp in G40. rewrite Ecs, Ecn in CKC3.
    pose proof (rw_cells_bytes_at _ _ _ _ IB3) as BO3. cbn [cells_bytes cbytes app] in BO3. rewrite app_nil_r in BO3.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BO3. destruct BO3 as [BO3 _].
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST3' end.
    ienv_now ENV MU WM as ENV3.
    sobj_now SOD MU WM as SOD3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SOB3 : sobj RNG mm Bi (Bi + Z.of_nat (length o)))
        by (eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | subst Bi; lia | lia | subst Bi; unfold zlength in *; lia] | exact MU | exact WM | solve_appW]);
      assert (SOS3 : sobj RNG mm 0 (0 + Z.of_nat (length (@nil Z)))) by (apply sobj_empty0; exact R0) end.
    eapply evtF_cut.
    { eapply (sn_write_spec RNG (Z_to_bv 64 634888) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp s6 s7 s8 s9 s10 s11 F fc Fp (Fp + 232) D cap Bi 0 Bi lo o [] dn)
        with (wr := firstn (Z.to_nat cap) P) (junk := jd3);
        rewrite ?unsigned_lit by lia; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption
              | apply bytes_at_nil; lia
              | exact KLO | exact IESD | exact RIMG | exact RD
              | apply iesafe_one_high; subst Bi; clear -KLO LO EFP SPHI; unfold KHIGH in KLO; lia
              | apply appW_one_high; subst Bi; clear -KLO LO EFP SPHI; unfold KHIGH in *; lia
              | apply (rng0_use _ _ R0); lia
              | eapply rng_sub'; [exact RSTK | subst Bi; clear -NNo LO EFP SPHI LJ3; cbn [length Z.of_nat]; lia]
              | subst Bi; clear -CAP0 DN NNo LO GLO SPHI QTOP QHI DSEP DHI LJ3 EFP; cbn [length Z.of_nat]; rewrite ?length_firstn; lia
              | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
    cbv beta. intros ms' PO.
    unfold sn_write_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & junk' & -> & MUc & WMc & MI4 & ST4 & CKC4 & DST4 & F40 & F56 & BO4 & BS4 & LE4).
    clear G40 G56 CKC3 DST3 BO3 ST3'.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    fix_ret.
    (* [comment removed for export] *)
    subst frest. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR3. destruct FR3 as [FR3 ICC3]. cbn [cells_size csize Nat.add] in ICC3.
    readdr FR3 (bv_unsigned sp + -272)%Z. readdr ICC3 (bv_unsigned sp). readdr IB3 (bv_unsigned sp + -352)%Z.
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (0 <? Bi)%Z with true by (symmetry; apply Z.ltb_lt; subst Bi; lia). cbn [Z.b2z].
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word).
    zs. zs. zs. zs. zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs. (* [comment removed for export] *)
    unfold INT_MAX in Hr. first [rewrite (land_W64_small r) by lia | rewrite (Z.mod_small r 18446744073709551616) by lia].
    (* [comment removed for export] *)
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST5 end.
    release_frame APC3 ST5 (bv_unsigned sp + -360)%Z.
    release_frame AP2 ST5 (bv_unsigned sp + -352)%Z.
    release_frame IB3 ST5 (bv_unsigned sp + -272)%Z.
    release_frame FR3 ST5 (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of CKC4 with rw_cells _ _ _ ?ckc =>
      assert (FALL : rw_cells asegs mm Fp
        ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 bufp0)]
         ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
             C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 (Fp + 232))] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)] ++ ckc))
    end end.
    { apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact G0|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact F40|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G48|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact F56|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G64|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G88|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G96|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G152|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G160|lia]|]; cbn [cells_size csize Nat.add].
      eapply rwc_eqA; [exact CKC4|lia]. }
    destruct (rw_cells_forget _ _ _ _ FALL) as [fj FJ]. cbn [cells_size csize Nat.add app length] in FJ.
    (* [comment removed for export] *)
    rewrite app_nil_r in DST4. rewrite (firstn_cap_app cap P o CAP0) in DST4. rewrite <- ET in DST4.
    rewrite <- EFP in FJ.
    apply evtF_done. unfold vfprintf_sn_post. cbv zeta.
    exists w5, w6, w7. do 11 eexists. exists fj, junk', m4.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [assumption|]. split; [assumption|].
    split; [exact ST5|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact DST4|]. split; [exact ICC3|]. split; [exact FJ | exact Hr].
  Qed.
  End Sz6.
  Theorem vfprintf_sn_spec : ltac:(let t := eval cbv delta [vfprintf_sn_spec__stmt] in vfprintf_sn_spec__stmt in exact t).
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP ICF KLO IESD RSTK RIMG RVA RD R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp. ltac2:(SecDiet.SzSec.closeP 'vfprintf_sn_spec__body "vvvvvvvvvvvvvvvvvv"). Qed.
End Vfprintf.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac acc_enrich ::=
  repeat match goal with
  | H : nth_error ?l ?k = Some ?x |- _ =>
      lazymatch goal with
      | _ : (k < length l)%nat |- _ => fail
      | _ => pose proof (nth_error_some_bound l k x H)
      end
  end;
  (tryif (match goal with
          | H : context [length (u32s _)] |- _ => idtac
          | H : context [length (u64s _)] |- _ => idtac
          | H : context [length (_ ++ _)] |- _ => idtac
          | H : context [length (repeat _ _)] |- _ => idtac
          | |- context [length (u32s _)] => idtac
          | |- context [length (u64s _)] => idtac
          | |- context [length (_ ++ _)] => idtac
          | |- context [length (repeat _ _)] => idtac
          end)
   then rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length in *
   else idtac);
  cbn [length] in *.
Local Ltac acc_hint ::= first [ progress (unfold wa); solve_acc1   (* [comment removed for export] *)
  (* [comment removed for export] *)
  | lazymatch goal with
    | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
        let X := leftmost E in is_var X;
        tryif (match goal with H : rng RNG X _ |- _ => idtac end) then fail else
        tryif (match goal with H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X] end) then fail else
        match goal with H : rng RNG ?lo ?len |- _ => lazymatch len with context [bv_unsigned _] => solve_acc_with H end end
    end ].
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells asegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x9b2c4.
Definition TOWRITE : Z := 0x9b064.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition towrite_sn__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp bufp bufsize CK : Z) (md : word) (wend wpos wbase : Z),
  a0 = Z_to_bv 64 Fp ->
  rw_cells asegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  (0 <= bufp) -> (bufp + bufsize < 2^64) -> (0 <= bufsize) -> mem_inv asegs m ->
  rng RNG Fp 232 ->
  evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (md' : word) (m' : mem),
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
               /\ rw_cells asegs m' Fp (snfile_cells (bufp + bufsize) bufp bufp bufp bufsize md' CK))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TOWRITE) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase : ltac2:(SecDiet.SzSec.tyM 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma towrite_sn__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_sn__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> FC B0 BHI BS0 MI RFP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite snfile_cells_size in FB.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold snfile_cells in FC. unfold TOWRITE.
  do 5 zs. zs. zs. first [if_lit | brf K0; [exfalso; revert K0; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]].
  do 10 zs.
  apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  unfold snfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "TW:" t end; fail] end.
Qed.
End Sz1.
Lemma towrite_sn : ltac:(let t := eval cbv delta [towrite_sn__stmt] in towrite_sn__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp bufp bufsize CK md wend wpos wbase. ltac2:(SecDiet.SzSec.closeP 'towrite_sn__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vf : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

(* [comment removed for export] *)
Definition arg_ok_vf__stmt : Prop := forall RNG Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS RNG m lo sp ap w a -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS RNG m' lo sp' ap w a.
Section Sz3.
Variables RNG Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vf__stmt "vvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma arg_ok_vf__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vf__stmt "vvvvvvvvvvvvvv").
Proof.
  intros H Hsp MU WM AW HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47 & RGs & SOs). exists slack.
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact (sobj_transport _ _ _ _ _ _ SOs MU WM AW)].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vf; [exact HW | | | | lia]; lia.
Qed.
End Sz3.
Lemma arg_ok_vf : ltac:(let t := eval cbv delta [arg_ok_vf__stmt] in arg_ok_vf__stmt in exact t).
Proof. intros RNG Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vf__body "vvvvvvvvvvvvvv"). Qed.
Lemma args_ok_vf : forall RNG Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS RNG m lo sp ap ws args -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS RNG m' lo sp' ap ws args.
Proof.
  intros RNG Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU WM AW HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma sobj_empty0 : forall RNG (m : mem), rng0 RNG -> sobj RNG m 0 0.
Proof.
  intros RNG m R0. split; [unfold app_blk, KLOW; lia|]. split; [split; [lia|]; split; [lia|]; intros G HG; lia|]. split; [lia|].
  exists 0, 0. split; [unfold KEND; repeat split; lia|].
  split; [split; [rewrite shad_div; unfold ASHOFF; lia|]; split; [rewrite shad_div; unfold ASHOFF; lia|]; intros i Hi; lia|].
  replace (shad 0 - shad 0) with 0 by lia. apply rng0_use; [exact R0|]. rewrite shad_div. unfold ASHOFF. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D cap : Z) (dn : nat) (out : list Z) (r lo : Z) (canary : word) (icf : list cell) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fj jd' : list byte) (m' : mem),
    let q := bv_unsigned sp in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q + 296); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' D [CB dn (zb (firstn (Z.to_nat cap) out) ++ Z_to_bv 8 0 :: jd')]
    /\ rw_cells asegs m' q icf
    /\ rw_cells asegs m' (q + 48) [CB 248 fj]
    /\ 0 <= r <= 2147483647.   (* [comment removed for export] *)

Section Vfprintf.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D cap : Z) (dn : nat) (A VA qtop lo bufp0 : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word) (icf : list cell).
  Let q := bv_unsigned sp.
  Hypothesis DN : Z.of_nat dn = cap + 1.
  Hypothesis CAP0 : 0 <= cap.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QTOP : q + 296 <= qtop.
  Hypothesis QHI : qtop <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : qtop <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis BUFP0 : 0 < bufp0 < 2^64.
  Hypothesis HD : 0 < D /\ D + Z.of_nat dn <= 2^63 /\ (D + Z.of_nat dn <= 0x10000 \/ 0x604000 <= D)
                  /\ (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D \/ (qtop <= D /\ D + Z.of_nat dn <= VA)).
  (* [comment removed for export] *)
  Hypothesis ICF : cells_size icf = 48%nat.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + Z.of_nat dn)].
  Hypothesis RSTK : rng RNG lo (q + 296 - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RD : rng RNG D (Z.of_nat dn).
  Hypothesis R0 : rng0 RNG.   (* [comment removed for export] *)

  Definition vfprintf_sn_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte) (Fp : Z),
    q + 48 = Fp ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (snfile_cells 0 0 0 bufp0 0 (Z_to_bv 64 0) (Fp + 232)) ->
    rw_cells asegs m (Fp + 232) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 cap)] ->
    rw_cells asegs m D [CB dn jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 352) SN_FS D (Z.of_nat dn) RNG m lo qtop (q - 368) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    rw_cells asegs m q icf ->
    icptenv m -> sobj RNG m lo (q + 296) -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D cap dn (concat ps) r lo canary icf m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp : ltac2:(SecDiet.SzSec.tyM 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_sn_spec__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP ICF KLO IESD RSTK RIMG RVA RD R0. pin_using (fun (BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP ICF KLO IESD RSTK RIMG RVA RD R0 : unit) => tt).
    intros EFP -> -> -> FC0 CKC0 DST0 BY VAA AOK ST SSP MI FRM ICC ENV SOSTK SOFMT SOPFX SOD.
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST0) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + Z.of_nat dn <= lo \/ bv_unsigned sp + 296 <= D) by (clear -HD HVA QTOP NNs; lia).
    assert (DHI : 0 < D /\ D + Z.of_nat dn <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl asegs m) as WM.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash FC0. stash CKC0. stash DST0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0, CKC0, DST0, HD.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call asegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp + 296); (D, D + Z.of_nat dn)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      assert (MU1 : munch [(lo, bv_unsigned sp + 296)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]
    end.
    clear MUp. stash HD. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evtF_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia
        | eapply rng_sub'; [exact RSTK | lia] | exact RIMG | eapply rng_sub'; [exact RIMG | lia] ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    unfold snfile_cells in FC0.
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in *. zs. rewrite ?unsigned_lit by lia. change (Z.land 0 18446744073709551583) with 0.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (Bi := bv_unsigned sp + -352) in *.
    eapply evtF_cut.
    { eapply (towrite_sn RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fp Bi 80 (Fp + 232) (Z_to_bv 64 0) 0 0 0);
        [ reflexivity | unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end | lia | lia | lia | assumption
        | eapply rng_sub'; [exact RSTK | lia] ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & md & m'' & -> & MUc & WMc & MIt & FC1).
    match goal with H : rw_cells _ ?mm Fp (_ :: _) |- _ => clear H end.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    do 5 zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
    apply (rw_cells_split_CB asegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc Bi. readdr FRv (Bi + 80)%Z. readdr AP2 (bv_unsigned sp + -360)%Z.
    match type of IBc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in IBc end. clearbody jb.
    match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
    pose proof (rw_CB_length _ _ _ _ IBc) as LJB.
    replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
    (* [comment removed for export] *)
    lazymatch type of FRv with rw_cells _ ?mm _ ?fr =>
      assert (FRI : rw_cells asegs mm (Bi + 80) (fr ++ icf))
        by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRv | eapply rwc_eqA; [exact ICC | cbn [cells_size csize Nat.add]; subst Bi; lia]]);
      assert (FRL0 : cells_size (fr ++ icf) = 320%nat) by (rewrite cells_size_app, ICF; reflexivity);
      set (frest := fr ++ icf) in FRI, FRL0 end.
    clear FRv ICC. rename FRI into FRv.
    unfold hide in HD.
    assert (SNK : SINK_sn Bi md frest D cap dn m'' []).
    { exists [], [], jb, jd, Bi, D, cap. cbv zeta. unfold SN_FOFF, SN_FS. rewrite !firstn_nil.
      split; [reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|].
      split; [change (zlength (@nil Z)) with 0; lia|]. split; [change (zlength (@nil Z)) with 0; lia|].
      split. { replace (Bi + 400) with Fp by lia. replace (Bi + 400 + 232) with (Fp + 232) by lia. exact FC1. }
      split; [cbn [zb map app]; exact IBc|].
      split; [exact FRv|]. split; [exact FRL0|].
      split. { replace (Bi + 400 + 232) with (Fp + 232) by lia. exact CKC0. }
      split; [cbn [zb map app]; exact DST0|].
      clear -DN CAP0 GLO LO HD SPHI QTOP QHI HVA EFP. subst Bi. repeat (split; [lia|]). lia. }
    (* [comment removed for export] *)
    assert (PCALL : forall Q ms, implXM px_atn px_sil px_npk px_fst RNG (printf_model OUT_app fmtz args) [] Q ms -> evtF asegs RNG (Q r (concat ps)) ms).
    { intros Q ms H. eapply implXM_pure_evtF; [| exact H]. rewrite (printf_model_app _ _ _ _ [] PIECES). reflexivity. }
    pose proof (printf_core_proof px_atn px_sil px_npk px_fst (list Z) Bi SN_FS (Bi + SN_FOFF) D (Z.of_nat dn) (SINK_sn Bi md frest D cap dn) (TOPOK_sn Bi) OUT_app
                  (sn_sink_frame Bi md frest D cap dn) (sn_sink_flags Bi md frest D cap dn) (sn_topok Bi) (sn_out Bi md frest D cap dn)) as PC2.
    unfold printf_core_stmt in PC2.
    unfold hide in AOK. try clear BY. try clear VAA.
    assert (BY : bytes_at asegs m'' A (zb fmtz)).
    { unfold hide in BYm. eapply bytes_at_transport; [exact BYm | exact MU1 | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia]. }
    assert (VAA : va_area m'' VA slots).
    { unfold hide in VAAm. unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; clear -HVA QTOP; lia]. }
    eapply evtF_cut.
    { apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots); clear PC2 PCALL; rewrite ?unsigned_lit by lia;
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_sn, SN_FS, SN_FOFF, zlength.
      - exact SNK.
      - exact BY.
      - exact HF.
      - f_equal. subst Bi. lia.
      - exact APC.
      - exact VAA.
      - lia.
      - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | subst Bi; lia | exact MU1 | exact WM | solve_appW |].
        constructor; [cbn [fst snd]; left; lia | constructor].
      - exact STc.
      - lia.
      - lia.
      - lia.
      - subst Bi; lia.
      - unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
      - assumption.
      - exact FRM.
      - lia.
      - lia.
      - subst Bi; lia.
      - right; left. subst Bi. clear -HVA QTOP SPHI LO GLO. lia.
      - clear -HD DHI LO GLO QTOP SPHI. destruct HD as (HD1 & HD1' & HD2 & [HD3 | [HD3 | HD3]]);
          [right; right; left; lia | right; right; right; lia | right; left; lia].
      - lia.
      - clear -HVA QTOP SPHI. lia.
      - lia.
      - exact KLO.
      - eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe].
      - eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [exact SOFMT | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [exact SOPFX | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | subst Bi; lia | lia | subst Bi; lia] | exact MU | exact WM | solve_appW].
      - eapply sobj_transport; [exact SOD | exact MU | exact WM | solve_appW].
      - eapply rng_sub'; [exact RSTK | lia].
      - exact RIMG.
      - eapply rng_sub'; [exact RSTK | lia].
      - exact RVA.
      - eapply rng_sub'; [exact RSTK | subst Bi; lia].
      - exact RD.
      - eapply rng_sub'; [exact RIMG | lia]. }
    cbv beta. intros ms' PO. clear PC2 PCALL.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
    subst fc' Ft.
    unfold SR, SN_FS in MUc. cbn [app] in MUc.
    clear SNK APC IBc FRv FC1 CKC0 DST0 AOK VAA BY MU1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    destruct SNK3 as (P & o & jb3 & jd3 & wp & cs & cn & SNK3). cbv zeta in SNK3.
    destruct SNK3 as (ET & LO80 & Ewp & Ecs & Ecn & FC3 & IB3 & FR3 & FRL & CKC3 & DST3 & _).
    unfold SN_FOFF in FC3, CKC3. readdr FC3 Fp. readdr CKC3 (Fp + 232)%Z.
    replace (Bi + 400 + 232) with (Fp + 232) in FC3 by lia.
    pose proof (rw_CB_length _ _ _ _ IB3) as LJ3. rewrite length_app, zb_length in LJ3.
    assert (NNo : 0 <= zlength o <= 80) by (unfold zlength in *; clear -LJ3; lia).
    unfold snfile_cells in FC3.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf Kb; [exfalso; clear -Kb BUFP0; rewrite ?unsigned_lit in Kb by lia; lia|].
    zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : rw_cells _ mm Fp (_ :: _) |- _ =>
        destruct (snfile_split mm Fp _ _ _ _ _ _ _ H) as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160); clear H end end.
    cbn [firstn skipn snfile_cells] in G0, G96.
    rewrite Ewp in G40. rewrite Ecs, Ecn in CKC3.
    pose proof (rw_cells_bytes_at _ _ _ _ IB3) as BO3. cbn [cells_bytes cbytes app] in BO3. rewrite app_nil_r in BO3.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BO3. destruct BO3 as [BO3 _].
    match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST3' end.
    ienv_now ENV MU WM as ENV3.
    sobj_now SOD MU WM as SOD3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SOB3 : sobj RNG mm Bi (Bi + Z.of_nat (length o)))
        by (eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | subst Bi; lia | lia | subst Bi; unfold zlength in *; lia] | exact MU | exact WM | solve_appW]);
      assert (SOS3 : sobj RNG mm 0 (0 + Z.of_nat (length (@nil Z)))) by (apply sobj_empty0; exact R0) end.
    eapply evtF_cut.
    { eapply (sn_write_spec RNG (Z_to_bv 64 635884) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp s6 s7 s8 s9 s10 s11 F fc Fp (Fp + 232) D cap Bi 0 Bi lo o [] dn)
        with (wr := firstn (Z.to_nat cap) P) (junk := jd3);
        rewrite ?unsigned_lit by lia; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption
              | apply bytes_at_nil; lia
              | exact KLO | exact IESD | exact RIMG | exact RD
              | apply iesafe_one_high; subst Bi; clear -KLO LO EFP SPHI; unfold KHIGH in KLO; lia
              | apply appW_one_high; subst Bi; clear -KLO LO EFP SPHI; unfold KHIGH in *; lia
              | apply (rng0_use _ _ R0); lia
              | eapply rng_sub'; [exact RSTK | subst Bi; clear -NNo LO EFP SPHI LJ3; cbn [length Z.of_nat]; lia]
              | subst Bi; clear -CAP0 DN NNo LO GLO SPHI QTOP QHI DSEP DHI LJ3 EFP; cbn [length Z.of_nat]; rewrite ?length_firstn; lia
              | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
    cbv beta. intros ms' PO.
    unfold sn_write_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & junk' & -> & MUc & WMc & MI4 & ST4 & CKC4 & DST4 & F40 & F56 & BO4 & BS4 & LE4).
    clear G40 G56 CKC3 DST3 BO3 ST3'.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    fix_ret.
    (* [comment removed for export] *)
    subst frest. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR3. destruct FR3 as [FR3 ICC3]. cbn [cells_size csize Nat.add] in ICC3.
    readdr FR3 (bv_unsigned sp + -272)%Z. readdr ICC3 (bv_unsigned sp). readdr IB3 (bv_unsigned sp + -352)%Z.
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (0 <? Bi)%Z with true by (symmetry; apply Z.ltb_lt; subst Bi; lia). cbn [Z.b2z].
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word).
    zs. zs. zs. zs. zs. (* [comment removed for export] *) rewrite ?Z.lor_0_l.
    zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs. (* [comment removed for export] *)
    unfold INT_MAX in Hr. first [rewrite (land_W64_small r) by lia | rewrite (Z.mod_small r 18446744073709551616) by lia].
    (* [comment removed for export] *)
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST5 end.
    release_frame APC3 ST5 (bv_unsigned sp + -360)%Z.
    release_frame AP2 ST5 (bv_unsigned sp + -352)%Z.
    release_frame IB3 ST5 (bv_unsigned sp + -272)%Z.
    release_frame FR3 ST5 (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of CKC4 with rw_cells _ _ _ ?ckc =>
      assert (FALL : rw_cells asegs mm Fp
        ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 bufp0)]
         ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
             C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
         ++ [C8 (Z_to_bv 64 (Fp + 232))] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)] ++ ckc))
    end end.
    { apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact G0|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact F40|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G48|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact F56|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G64|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G88|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G96|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G152|lia]|]; cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact G160|lia]|]; cbn [cells_size csize Nat.add].
      eapply rwc_eqA; [exact CKC4|lia]. }
    destruct (rw_cells_forget _ _ _ _ FALL) as [fj FJ]. cbn [cells_size csize Nat.add app length] in FJ.
    (* [comment removed for export] *)
    rewrite app_nil_r in DST4. rewrite (firstn_cap_app cap P o CAP0) in DST4. rewrite <- ET in DST4.
    rewrite <- EFP in FJ.
    apply evtF_done. unfold vfprintf_sn_post. cbv zeta.
    exists w5, w6, w7. do 11 eexists. exists fj, junk', m4.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [assumption|]. split; [assumption|].
    split; [exact ST5|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [exact DST4|]. split; [exact ICC3|]. split; [exact FJ | exact Hr].
  Qed.
  End Sz6.
  Theorem vfprintf_sn_spec : ltac:(let t := eval cbv delta [vfprintf_sn_spec__stmt] in vfprintf_sn_spec__stmt in exact t).
  Proof using BUFP0 CAP0 DN GLO HA HD HF HVA LO P1 PIECES QHI QTOP ICF KLO IESD RSTK RIMG RVA RD R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd Fp. ltac2:(SecDiet.SzSec.closeP 'vfprintf_sn_spec__body "vvvvvvvvvvvvvvvvvv"). Qed.
End Vfprintf.
End TwB.
End F_vfprintf_sn.

(* [comment removed for export] *)
Module F_vsnprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep FP ITree Nodes Decode StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface F_printf_core. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition VSNPRINTF : Z := 0x9e00c.
Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5904.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells asegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells asegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

(* [comment removed for export] *)
Definition zfile_cells : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (out : list Z) (r lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jd' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' D [CB (Z.to_nat n) (zb (firstn (Z.to_nat (n - 1)) out) ++ Z_to_bv 8 0 :: jd')]
    /\ 0 <= r <= 2147483647.

Section Vsnprintf.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word) (fstr : list byte) (its : list pitem).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VSN_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x603000 <= D)
                  /\ (D + n <= lo \/ VA + 8 * zlength slots <= D \/ (q <= D /\ D + n <= VA)).
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RD : rng RNG D n.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Definition vsnprintf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 704) SN_FS D n RNG m lo q (q - 720) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) -> pargs_sep [(D, D + n)] its (Z_to_bv 64 VA) ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma vsnprintf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK. pin_using (fun (GLO HA HD HF HN HVA LO P1 PIECES QHI KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK : unit) => tt).
 intros -> -> -> -> DST BY VAA AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PAOK PSEP.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    unfold VSN_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + n <= lo \/ bv_unsigned sp <= D) by (clear -HD HVA NNs; lia).
    assert (DHI : 0 < D /\ D + n <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + n)]%Z m) as MU.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VSNPRINTF.
    carve_frame 304%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 304 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 304 j [] [256; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    do 12 zs.
    zs. zs. brf K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. clear -HN. lia. }
    zs. zs. zs. zs. zs.
    (* [comment removed for export] *)
    replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
    change (Z.land (-1) 18446744073709551615) with 18446744073709551615.
    replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zs. zs. zs. zs. zs.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
    match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -72)%Z.
    (* [comment removed for export] *)
    zs. ienv_now ENV MU WM as ENVn. sobj_now SOSTK MU WM as SOSn.
    eapply evtF_cut.
    { eapply (memset_wb_spec RNG) with (lo := lo) (q := (bv_unsigned sp + -304)%Z) (junk := j0);
        [ cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact FZ | assumption | lia | lia | lia | lia | exact ST | lia | exact KLO | exact ENVn
        | eapply sobj_sub; [exact SOSn | lia | lia | lia] | right; lia | exact RIMG | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RSTK | lia] ]. }
    cbv beta. intros ms' PO. unfold memset_postw in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & ST2 & FZ').
    clear FZ ENVn SOSn.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
    try clear ST. rename ST2 into ST.
    fix_ret.
    (* [comment removed for export] *)
    pose proof (rw_cells_recast _ _ _ zfile_cells FZ' ltac:(cbn [cells_wf cell_wf zfile_cells]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
    unfold zfile_cells in FC.
    do 10 zs.
    c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).
    (* [comment removed for export] *)
    unfold hide in HD.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
    pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJD; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite ?le1_zero. replace (Z_to_bv 64 D : word) with (wa (D + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJD; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJD in DST. clear DA2.
    zs. zs. zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -56)%Z. readdr CKC (bv_unsigned sp + -304 + 232)%Z.
    unfold hide in BY, VAA, AOK, BYm, VAAm.
    assert (BY2 : bytes_at asegs m2 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (VAA2 : va_area m2 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA HD LO; lia]. }
    assert (NN : Z.of_nat (Z.to_nat n) = n) by lia.
    clear BY VAA BY2 VAA2.
    replace (bv_unsigned sp + -72) with (bv_unsigned sp + -304 + 232) in FC by lia.
    replace (n + -1) with (n - 1) in CKC by lia.
    try replace (Z.land 18446744073709551615 (n - 1)) with (n - 1) in CKC
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    change (Z_to_bv 64 647384) with (Z_to_bv 64 SN_WRITE) in FC.
    (* [comment removed for export] *)
    assert (LFS : Z.of_nat (length fmtz) = Z.of_nat (length fstr) + 1).
    { rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    assert (BYF : bytes_at asegs m2 A (fstr ++ [Z_to_bv 8 0])).
    { rewrite <- FSTR. eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (PAOK2 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -304)) m2 its (Z_to_bv 64 VA)).
    { eapply pargs_okL_transport; [exact PAOK | exact MU | exact WM | solve_appW | | rewrite unsigned_lit by lia; lia].
      change [(lo, bv_unsigned sp); (D, D + n)] with ([(lo, bv_unsigned sp)] ++ [(D, D + n)]).
      apply pargs_sep_app; [eapply pargs_sep_stack; [exact PAOK | constructor; [cbn [fst snd]; lia | constructor]] | exact PSEP]. }
    ienv_now ENV MU WM as ENV2. sobj_now SOFMT MU WM as SOFMT2.
    eapply evtF_cut.
    { eapply (vfprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        rewrite ?unsigned_lit by lia;
        [ assumption | exact ST | lia | exact KLO | exact ENV2 | exact CKP | reflexivity | exact BYF | exact NOZ | left; lia
        | unfold zlength in SOFMT2; rewrite <- LFS; exact SOFMT2 | exact RIMG | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK2 ]. }
    cbv beta. intros ms' PO. unfold vfprintf_i_mid in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2' & j16 & -> & MUc & WMc & MI2' & ST2' & ICC).
    clear ENV2 SOFMT2 BYF PAOK2.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m2' MUc WMc; clear MUc WMc; try clear MI2 end.
    (* [comment removed for export] *)
    assert (BY2 : bytes_at asegs m2' A (zb fmtz)).
    { eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (VAA2 : va_area m2' VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA HD LO; lia]. }
    assert (AOK2 : args_ok (bv_unsigned sp + -352 - 352) 648 D (Z.of_nat (Z.to_nat n)) RNG m2' lo (bv_unsigned sp) (bv_unsigned sp + -352 - 368) slots args).
    { replace (bv_unsigned sp + -352 - 352) with (bv_unsigned sp - 704) by lia. replace (bv_unsigned sp + -352 - 368) with (bv_unsigned sp - 720) by lia.
      rewrite NN.
      eapply args_ok_vf; [exact AOK | lia | exact MU | exact WM | solve_appW |]. constructor; [cbn [fst snd]; left; lia|]. constructor; [cbn [fst snd]; right; right; lia | constructor]. }
    clear AOK.
    ienv_now ENV MU WM as ENV3. sobj_now SOFMT MU WM as SOFMT3. sobj_now SOSTK MU WM as SOSTK3. sobj_now SOPFX MU WM as SOPFX3. sobj_now SOD MU WM as SOD3.
    replace (bv_unsigned sp + -304 + -48) with (bv_unsigned sp + -352) in * by lia.
    eapply evtF_cut.
    { lazymatch type of ICC with rw_cells _ _ _ ?icf =>
        eapply (vfprintf_sn_spec RNG _ _ gp tp _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 F fc D (n - 1) (Z.to_nat n) A VA (bv_unsigned sp) lo (bv_unsigned sp + -49)
                  fmtz slots args ps r canary icf) with (Fp := bv_unsigned sp + -304) end;
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS, zlength;
        fastfirst (first [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact FRM | reflexivity | eassumption
              | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]
              | rewrite NN; first [exact IESD | exact RD | exact SOD3]
              | eapply rng_sub'; [exact RSTK | clear -LO SPHI; unfold VSN_DEPTH in LO; lia]
              | eapply sobj_sub; [exact SOSTK3 | lia | lia | lia]
              | clear -HN LO GLO QHI HA HVA HD SPHI; lia
              | match goal with |- ?g => idtac "VF-PREM:" g end; match type of CKC with ?t => idtac "CKC:" t end; match type of DST with ?t => idtac "DST:" t end; fail ]). }
    cbv beta. intros ms' PO.
    unfold vfprintf_sn_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & fj & jd' & m3 & -> & MUc & WMc & MI3 & ST3 & SSP3 & DST3 & ICC3 & FJ3 & Hr3).
    clear FC CKC DST BY2 VAA2 AOK2 ICC ENV3 SOFMT3 SOSTK3 SOPFX3 SOD3.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MI2' end.
    (* [comment removed for export] *)
    fix_ret.
    eapply evtF_cut.
    { eapply (vfprintf_i_post RNG) with (j16 := j16); rewrite ?unsigned_lit by lia; [exact MI3 | exact ICC3 | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms' ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -352 + 48) with (bv_unsigned sp + -304) in * by lia.
    release_frame ICC3 ST3 (bv_unsigned sp + -304)%Z.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 7 zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -304) ([CB 248 fj] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FJ3|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact FRv | lia]
      | clear FJ3 FRv ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evtF_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. clear -SPHI. intros; lia. }
    split; [exact WM|]. split; [exact MI3|].
    split; [exact ST3|].
    split; [split; [exact SSP1 | exact SSP2]|].
    replace (Z.to_nat (n - 1)) with (Z.to_nat (n - 1)) in DST3 by reflexivity. split; [exact DST3 | exact Hr3].
  Qed.
  End Sz3.
  Theorem vsnprintf_spec : ltac:(let t := eval cbv delta [vsnprintf_spec__stmt] in vsnprintf_spec__stmt in exact t).
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End Vsnprintf.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition VSNPRINTF : Z := 0x9e3f0.
Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5904.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells asegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells asegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

(* [comment removed for export] *)
Definition zfile_cells : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (out : list Z) (r lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jd' : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' D [CB (Z.to_nat n) (zb (firstn (Z.to_nat (n - 1)) out) ++ Z_to_bv 8 0 :: jd')]
    /\ 0 <= r <= 2147483647.

Section Vsnprintf.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word) (fstr : list byte) (its : list pitem).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VSN_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.   (* [comment removed for export] *)
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x604000 <= D)
                  /\ (D + n <= lo \/ VA + 8 * zlength slots <= D \/ (q <= D /\ D + n <= VA)).
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RD : rng RNG D n.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Definition vsnprintf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok (q - 704) SN_FS D n RNG m lo q (q - 720) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) -> pargs_sep [(D, D + n)] its (Z_to_bv 64 VA) ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma vsnprintf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK. pin_using (fun (GLO HA HD HF HN HVA LO P1 PIECES QHI KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK : unit) => tt).
 intros -> -> -> -> DST BY VAA AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PAOK PSEP.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    unfold VSN_DEPTH, GLOBALS_TOP, SN_FS in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, HD, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (DSEP : D + n <= lo \/ bv_unsigned sp <= D) by (clear -HD HVA NNs; lia).
    assert (DHI : 0 < D /\ D + n <= 2^63) by (clear -HD; lia).
    pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + n)]%Z m) as MU.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash HD. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VSNPRINTF.
    carve_frame 304%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 304 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 304 j [] [256; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    do 12 zs.
    zs. zs. brf K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. clear -HN. lia. }
    zs. zs. zs. zs. zs.
    (* [comment removed for export] *)
    replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
    change (Z.land (-1) 18446744073709551615) with 18446744073709551615.
    replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zs. zs. zs. zs. zs.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
    match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -72)%Z.
    (* [comment removed for export] *)
    zs. ienv_now ENV MU WM as ENVn. sobj_now SOSTK MU WM as SOSn.
    eapply evtF_cut.
    { eapply (memset_wb_spec RNG) with (lo := lo) (q := (bv_unsigned sp + -304)%Z) (junk := j0);
        [ cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact FZ | assumption | lia | lia | lia | lia | exact ST | lia | exact KLO | exact ENVn
        | eapply sobj_sub; [exact SOSn | lia | lia | lia] | right; lia | exact RIMG | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RSTK | lia] ]. }
    cbv beta. intros ms' PO. unfold memset_postw in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & ST2 & FZ').
    clear FZ ENVn SOSn.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
    try clear ST. rename ST2 into ST.
    fix_ret.
    (* [comment removed for export] *)
    pose proof (rw_cells_recast _ _ _ zfile_cells FZ' ltac:(cbn [cells_wf cell_wf zfile_cells]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
    unfold zfile_cells in FC.
    do 10 zs.
    c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).
    (* [comment removed for export] *)
    unfold hide in HD.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
    pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJD; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite ?le1_zero. replace (Z_to_bv 64 D : word) with (wa (D + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJD; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJD in DST. clear DA2.
    zs. zs. zs. zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr FRv (bv_unsigned sp + -56)%Z. readdr CKC (bv_unsigned sp + -304 + 232)%Z.
    unfold hide in BY, VAA, AOK, BYm, VAAm.
    assert (BY2 : bytes_at asegs m2 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (VAA2 : va_area m2 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA HD LO; lia]. }
    assert (NN : Z.of_nat (Z.to_nat n) = n) by lia.
    clear BY VAA BY2 VAA2.
    replace (bv_unsigned sp + -72) with (bv_unsigned sp + -304 + 232) in FC by lia.
    replace (n + -1) with (n - 1) in CKC by lia.
    try replace (Z.land 18446744073709551615 (n - 1)) with (n - 1) in CKC
      by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    change (Z_to_bv 64 648380) with (Z_to_bv 64 SN_WRITE) in FC.
    (* [comment removed for export] *)
    assert (LFS : Z.of_nat (length fmtz) = Z.of_nat (length fstr) + 1).
    { rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    assert (BYF : bytes_at asegs m2 A (fstr ++ [Z_to_bv 8 0])).
    { rewrite <- FSTR. eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (PAOK2 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -304)) m2 its (Z_to_bv 64 VA)).
    { eapply pargs_okL_transport; [exact PAOK | exact MU | exact WM | solve_appW | | rewrite unsigned_lit by lia; lia].
      change [(lo, bv_unsigned sp); (D, D + n)] with ([(lo, bv_unsigned sp)] ++ [(D, D + n)]).
      apply pargs_sep_app; [eapply pargs_sep_stack; [exact PAOK | constructor; [cbn [fst snd]; lia | constructor]] | exact PSEP]. }
    ienv_now ENV MU WM as ENV2. sobj_now SOFMT MU WM as SOFMT2.
    eapply evtF_cut.
    { eapply (vfprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        rewrite ?unsigned_lit by lia;
        [ assumption | exact ST | lia | exact KLO | exact ENV2 | exact CKP | reflexivity | exact BYF | exact NOZ | left; lia
        | unfold zlength in SOFMT2; rewrite <- LFS; exact SOFMT2 | exact RIMG | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK2 ]. }
    cbv beta. intros ms' PO. unfold vfprintf_i_mid in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2' & j16 & -> & MUc & WMc & MI2' & ST2' & ICC).
    clear ENV2 SOFMT2 BYF PAOK2.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m2' MUc WMc; clear MUc WMc; try clear MI2 end.
    (* [comment removed for export] *)
    assert (BY2 : bytes_at asegs m2' A (zb fmtz)).
    { eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO HD; lia]. }
    assert (VAA2 : va_area m2' VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA HD LO; lia]. }
    assert (AOK2 : args_ok (bv_unsigned sp + -352 - 352) 648 D (Z.of_nat (Z.to_nat n)) RNG m2' lo (bv_unsigned sp) (bv_unsigned sp + -352 - 368) slots args).
    { replace (bv_unsigned sp + -352 - 352) with (bv_unsigned sp - 704) by lia. replace (bv_unsigned sp + -352 - 368) with (bv_unsigned sp - 720) by lia.
      rewrite NN.
      eapply args_ok_vf; [exact AOK | lia | exact MU | exact WM | solve_appW |]. constructor; [cbn [fst snd]; left; lia|]. constructor; [cbn [fst snd]; right; right; lia | constructor]. }
    clear AOK.
    ienv_now ENV MU WM as ENV3. sobj_now SOFMT MU WM as SOFMT3. sobj_now SOSTK MU WM as SOSTK3. sobj_now SOPFX MU WM as SOPFX3. sobj_now SOD MU WM as SOD3.
    replace (bv_unsigned sp + -304 + -48) with (bv_unsigned sp + -352) in * by lia.
    eapply evtF_cut.
    { lazymatch type of ICC with rw_cells _ _ _ ?icf =>
        eapply (vfprintf_sn_spec RNG _ _ gp tp _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 F fc D (n - 1) (Z.to_nat n) A VA (bv_unsigned sp) lo (bv_unsigned sp + -49)
                  fmtz slots args ps r canary icf) with (Fp := bv_unsigned sp + -304) end;
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, SN_FS, zlength;
        fastfirst (first [ noevar_assumption | exact HF | exact P1 | exact PIECES | exact FRM | reflexivity | eassumption
              | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]
              | rewrite NN; first [exact IESD | exact RD | exact SOD3]
              | eapply rng_sub'; [exact RSTK | clear -LO SPHI; unfold VSN_DEPTH in LO; lia]
              | eapply sobj_sub; [exact SOSTK3 | lia | lia | lia]
              | clear -HN LO GLO QHI HA HVA HD SPHI; lia
              | match goal with |- ?g => idtac "VF-PREM:" g end; match type of CKC with ?t => idtac "CKC:" t end; match type of DST with ?t => idtac "DST:" t end; fail ]). }
    cbv beta. intros ms' PO.
    unfold vfprintf_sn_post in PO. cbv zeta in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & fj & jd' & m3 & -> & MUc & WMc & MI3 & ST3 & SSP3 & DST3 & ICC3 & FJ3 & Hr3).
    clear FC CKC DST BY2 VAA2 AOK2 ICC ENV3 SOFMT3 SOSTK3 SOPFX3 SOD3.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MI2' end.
    (* [comment removed for export] *)
    fix_ret.
    eapply evtF_cut.
    { eapply (vfprintf_i_post RNG) with (j16 := j16); rewrite ?unsigned_lit by lia; [exact MI3 | exact ICC3 | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms' ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -352 + 48) with (bv_unsigned sp + -304) in * by lia.
    release_frame ICC3 ST3 (bv_unsigned sp + -304)%Z.
    fix_ret.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 7 zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -304) ([CB 248 fj] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FJ3|]; cbn [cells_size csize Nat.add]; eapply rwc_eqA; [exact FRv | lia]
      | clear FJ3 FRv ] end.
    cbn [app] in FALL.
    release_frame FALL ST3 (bv_unsigned sp).
    apply evtF_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. clear -SPHI. intros; lia. }
    split; [exact WM|]. split; [exact MI3|].
    split; [exact ST3|].
    split; [split; [exact SSP1 | exact SSP2]|].
    replace (Z.to_nat (n - 1)) with (Z.to_nat (n - 1)) in DST3 by reflexivity. split; [exact DST3 | exact Hr3].
  Qed.
  End Sz3.
  Theorem vsnprintf_spec : ltac:(let t := eval cbv delta [vsnprintf_spec__stmt] in vsnprintf_spec__stmt in exact t).
  Proof using GLO HA HD HF HN HVA LO P1 PIECES QHI KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m jd. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End Vsnprintf.
End TwB.
End F_vsnprintf.
