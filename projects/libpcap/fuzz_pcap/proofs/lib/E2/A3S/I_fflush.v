(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread I_ahm. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Notation rt_ahm m TABLE := (rw_cells asegs m 0xade40 [C8 (Z_to_bv 64 0xade48); C8 (Z_to_bv 64 TABLE)]).

Section CANSEC1. Context {rc : runConstT}.
Definition FFLUSH_I_RA : Z := 0x49b0c.

(* [comment removed for export] *)
Definition fflush_i_mid (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 (junk : list byte) m',
    ms' = MS (mkR (Z_to_bv 64 0x49b0c) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                  a0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9a324) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [CB 56 junk; C8 s1; C8 s0; C8 ra].

Definition fflush_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> KHIGH <= lo ->
  icptenv m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fflush_i_mid ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444d8) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo : ltac2:(SecDiet.SzSec.tyM 'fflush_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fflush_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV RI RSTK.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_ini _ ENV) as INIc. pose proof (ie_fopen _ ENV) as RFOc.
  zstep. (* [comment removed for export] *)
  carve_frame 80%nat ST.
  do 5 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 4 zstep.
  apply evtF_done. unfold fflush_i_mid.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; first [assumption | eassumption].
Qed.
End Sz1.
#[using="Type"] Lemma fflush_i_pre : ltac:(let t := eval cbv delta [fflush_i_pre__stmt] in fflush_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo. ltac2:(SecDiet.SzSec.closeP 'fflush_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition fflush_i_post_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v res : word) (lo BKT : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -256, bv_unsigned sp); (BKT, BKT + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' BKT ahm_bucket0.

Definition fflush_i_post__stmt : Prop := forall RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo fp TABLE : Z) (junk : list byte) (rav s0v s1v : word),
  let BKT := TABLE + 120 * ahm_idx fp in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp + -256 ->
  rw_cells asegs m (bv_unsigned sp + -80) [CB 56 junk; C8 s1v; C8 s0v; C8 rav] ->
  rt_ahm m TABLE -> rw_cells asegs m BKT ahm_bucket0 ->
  0 < fp < 2^64 -> TABLE mod 8 = 0 -> 0x603000 <= TABLE -> TABLE + AHM_BYTES <= lo -> 0x603000 <= lo -> bv_unsigned sp <= 2^63 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG BKT 120 ->
  evtF asegs RNG (fflush_i_post_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rav s0v s1v res lo BKT m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 fp) x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x49b0c) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fp TABLE junk rav s0v s1v : ltac2:(SecDiet.SzSec.tyM 'fflush_i_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fflush_i_post__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_i_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BKT MI ST LO FR AHM BC FP TAL TLO THI GLO SP63 RI RSTK RB.
  pose proof (ahm_idx_range fp) as IDX.
  assert (BR1 : TABLE <= BKT) by (subst BKT; lia). assert (BR2 : BKT + 120 <= TABLE + AHM_BYTES) by (subst BKT; unfold AHM_BYTES; lia).
  unfold AHM_BYTES in *. unfold ahm_bucket0 in BC.
  pose proof (munch_refl [(bv_unsigned sp + -256, bv_unsigned sp); (BKT, BKT + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0 FP. lia. } clear K0.
  do 5 zstep.
  do 6 zstep.
  recell FR 6%nat 1%nat [C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); CB 5 (repeat (Z_to_bv 8 170) 5)].
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app asegs _ _ [_] [_;_;_;_;_;_;_;_;_;_;_;_])) in FR. destruct FR as [FRa FRb].
  cbn [cells_size csize Nat.add] in FRb.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_] [_;_;_])) in FRb. destruct FRb as [HC FRs].
  cbn [cells_size csize Nat.add] in FRs.
  replace (bv_unsigned sp + -80 + Z.of_nat 8) with (bv_unsigned sp + -72) in HC, FRs by lia.
  replace (bv_unsigned sp + -72 + Z.of_nat 48) with (bv_unsigned sp + -24) in FRs by lia.
  pose proof AHM as AHM2. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in AHM2. destruct AHM2 as [_ MAPC].
  cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in MAPC.
  change (712256 + Z.of_nat 8) with 712264 in MAPC.
  (* [comment removed for export] *)
  zstep.
  call_sp (ahm_acquire_miss_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 712264 TABLE (bv_unsigned sp + -72) fp).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => first [reflexivity | assumption | exact HC | (unfold ahm_bucket0; exact BC) | (unfold AHM_BYTES; lia) ] end).
  rename PC into ST. rename PC0 into HC. rename POST into BC. unfold ahm_handle in HC. unfold ahm_bucket0 in BC.
  zstep. zstep. if_true.
  zstep. zstep. zstep.
  call_sp (ahm_release_nocell_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -72) fp).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => first [reflexivity | assumption | exact HC | lia ] end).
  clear HC. rename PC into ST. rename POST into HC.
  do 4 zstep. zstep.
  pose proof (stk_release _ _ _ _ _ ST FRa ltac:(lia)) as SK1. cbn [cells_size csize Nat.add] in SK1.
  replace (bv_unsigned sp + -80 + Z.of_nat 8) with (bv_unsigned sp + -72) in SK1 by lia.
  pose proof (stk_release _ _ _ _ _ SK1 HC ltac:(lia)) as SK2. unfold ahm_handle in SK2. cbn [cells_size csize Nat.add] in SK2.
  replace (bv_unsigned sp + -72 + Z.of_nat 48) with (bv_unsigned sp + -24) in SK2 by lia.
  pose proof (stk_release _ _ _ _ _ SK2 FRs ltac:(lia)) as SK3. cbn [cells_size csize Nat.add] in SK3.
  replace (bv_unsigned sp + -24 + Z.of_nat 24) with (bv_unsigned sp) in SK3 by lia.
  zstep.
  apply evtF_done. unfold fflush_i_post_post, ahm_bucket0.
  do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End Sz2.
#[using="Type"] Lemma fflush_i_post : ltac:(let t := eval cbv delta [fflush_i_post__stmt] in fflush_i_post__stmt in exact t).
Proof. intros RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fp TABLE junk rav s0v s1v. ltac2:(SecDiet.SzSec.closeP 'fflush_i_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Notation rt_ahm m TABLE := (rw_cells asegs m 0xae240 [C8 (Z_to_bv 64 0xae248); C8 (Z_to_bv 64 TABLE)]).

Section CANSEC1. Context {rc : runConstT}.
Definition FFLUSH_I_RA : Z := 0x49b74.

(* [comment removed for export] *)
Definition fflush_i_mid (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 (junk : list byte) m',
    ms' = MS (mkR (Z_to_bv 64 0x49b74) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                  a0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9a708) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [CB 56 junk; C8 s1; C8 s0; C8 ra].

Definition fflush_i_pre__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> KHIGH <= lo ->
  icptenv m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fflush_i_mid ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44540) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo : ltac2:(SecDiet.SzSec.tyM 'fflush_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fflush_i_pre__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_i_pre__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros MI ST LO KLO ENV RI RSTK.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). pose proof KLO as KLO'. unfold KHIGH in KLO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (ie_ini _ ENV) as INIc. pose proof (ie_fopen _ ENV) as RFOc.
  zstep. (* [comment removed for export] *)
  carve_frame 80%nat ST.
  do 5 zstep. zstep.
  call_sp tryinit_spec. all: iprem.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
  do 4 zstep.
  apply evtF_done. unfold fflush_i_mid.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; first [assumption | eassumption].
Qed.
End Sz1.
#[using="Type"] Lemma fflush_i_pre : ltac:(let t := eval cbv delta [fflush_i_pre__stmt] in fflush_i_pre__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo. ltac2:(SecDiet.SzSec.closeP 'fflush_i_pre__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition fflush_i_post_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v res : word) (lo BKT : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -256, bv_unsigned sp); (BKT, BKT + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' BKT ahm_bucket0.

Definition fflush_i_post__stmt : Prop := forall RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo fp TABLE : Z) (junk : list byte) (rav s0v s1v : word),
  let BKT := TABLE + 120 * ahm_idx fp in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp + -256 ->
  rw_cells asegs m (bv_unsigned sp + -80) [CB 56 junk; C8 s1v; C8 s0v; C8 rav] ->
  rt_ahm m TABLE -> rw_cells asegs m BKT ahm_bucket0 ->
  0 < fp < 2^64 -> TABLE mod 8 = 0 -> 0x604000 <= TABLE -> TABLE + AHM_BYTES <= lo -> 0x604000 <= lo -> bv_unsigned sp <= 2^63 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG BKT 120 ->
  evtF asegs RNG (fflush_i_post_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rav s0v s1v res lo BKT m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 fp) x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x49b74) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fp TABLE junk rav s0v s1v : ltac2:(SecDiet.SzSec.tyM 'fflush_i_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fflush_i_post__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_i_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BKT MI ST LO FR AHM BC FP TAL TLO THI GLO SP63 RI RSTK RB.
  pose proof (ahm_idx_range fp) as IDX.
  assert (BR1 : TABLE <= BKT) by (subst BKT; lia). assert (BR2 : BKT + 120 <= TABLE + AHM_BYTES) by (subst BKT; unfold AHM_BYTES; lia).
  unfold AHM_BYTES in *. unfold ahm_bucket0 in BC.
  pose proof (munch_refl [(bv_unsigned sp + -256, bv_unsigned sp); (BKT, BKT + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0 FP. lia. } clear K0.
  do 5 zstep.
  do 6 zstep.
  recell FR 6%nat 1%nat [C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); C1 (Z_to_bv 8 170); CB 5 (repeat (Z_to_bv 8 170) 5)].
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app asegs _ _ [_] [_;_;_;_;_;_;_;_;_;_;_;_])) in FR. destruct FR as [FRa FRb].
  cbn [cells_size csize Nat.add] in FRb.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_] [_;_;_])) in FRb. destruct FRb as [HC FRs].
  cbn [cells_size csize Nat.add] in FRs.
  replace (bv_unsigned sp + -80 + Z.of_nat 8) with (bv_unsigned sp + -72) in HC, FRs by lia.
  replace (bv_unsigned sp + -72 + Z.of_nat 48) with (bv_unsigned sp + -24) in FRs by lia.
  pose proof AHM as AHM2. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in AHM2. destruct AHM2 as [_ MAPC].
  cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in MAPC.
  change (713280 + Z.of_nat 8) with 713288 in MAPC.
  (* [comment removed for export] *)
  zstep.
  call_sp (ahm_acquire_miss_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 713288 TABLE (bv_unsigned sp + -72) fp).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => first [reflexivity | assumption | exact HC | (unfold ahm_bucket0; exact BC) | (unfold AHM_BYTES; lia) ] end).
  rename PC into ST. rename PC0 into HC. rename POST into BC. unfold ahm_handle in HC. unfold ahm_bucket0 in BC.
  zstep. zstep. if_true.
  zstep. zstep. zstep.
  call_sp (ahm_release_nocell_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -72) fp).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => first [reflexivity | assumption | exact HC | lia ] end).
  clear HC. rename PC into ST. rename POST into HC.
  do 4 zstep. zstep.
  pose proof (stk_release _ _ _ _ _ ST FRa ltac:(lia)) as SK1. cbn [cells_size csize Nat.add] in SK1.
  replace (bv_unsigned sp + -80 + Z.of_nat 8) with (bv_unsigned sp + -72) in SK1 by lia.
  pose proof (stk_release _ _ _ _ _ SK1 HC ltac:(lia)) as SK2. unfold ahm_handle in SK2. cbn [cells_size csize Nat.add] in SK2.
  replace (bv_unsigned sp + -72 + Z.of_nat 48) with (bv_unsigned sp + -24) in SK2 by lia.
  pose proof (stk_release _ _ _ _ _ SK2 FRs ltac:(lia)) as SK3. cbn [cells_size csize Nat.add] in SK3.
  replace (bv_unsigned sp + -24 + Z.of_nat 24) with (bv_unsigned sp) in SK3 by lia.
  zstep.
  apply evtF_done. unfold fflush_i_post_post, ahm_bucket0.
  do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End Sz2.
#[using="Type"] Lemma fflush_i_post : ltac:(let t := eval cbv delta [fflush_i_post__stmt] in fflush_i_post__stmt in exact t).
Proof. intros RNG x1 sp gp tp t0 t1 t2 x9 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fp TABLE junk rav s0v s1v. ltac2:(SecDiet.SzSec.closeP 'fflush_i_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
