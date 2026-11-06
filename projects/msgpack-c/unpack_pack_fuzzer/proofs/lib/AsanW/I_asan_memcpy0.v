(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF FpZero.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg RtCells ShadowTac F_memcpy F_rip.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module I_asan_memcpy0.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.FpZero.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ShadowTac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_memcpy. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rip.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_asan_memcpy.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.

Definition asan_memcpy0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition memcpy_n0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma memcpy_n0_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  rng RNG (bv_unsigned a1) 0 -> rng RNG (bv_unsigned a0) 0 ->
  evtF asegs RNG (memcpy_n0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc74a0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI RS RD.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in *.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
  eapply evtF_mono.
  - apply (memcpy_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [] []).
    + apply bytes_at_nil. lia.
    + reflexivity.
    + split; [split; [cbn; auto| cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia]|]. cbn [cells_size csize Nat.add]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. split; [lia|]. split; [lia|]. intros i Hi. lia.
    + change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    + exact MI.
    + exact RS.
    + exact RD.
  - cbv beta. intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & E & MU & WM & MI' & _).
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m'. split; [exact E|]. split; [| split; [exact WM| exact MI']].
    eapply munch_weaken; [| exact MU]. intros x _. cbn [outside]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. split; [lia| exact I].
Qed.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation a2 := (Z_to_bv 64 0).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RS0 : rng RNG S 0.
  Hypothesis RD0 : rng RNG D 0.

  Notation POST := (asan_memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m).

  Definition INV0 (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
                  [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc.

  Ltac inv_open0 H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1).

  Definition BL0 : Prop := (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= S < 2^64 /\ 0 <= D < 2^64)%Z.
  Lemma BL0_ok : BL0.
  Proof.
    unfold BL0. destruct ST as (L0 & _). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in *.
    change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. lia.
  Qed.

  Lemma LX0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV0 mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5ccf4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof IV as IV0. inv_open0 IV. pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    zstep. zstep. zstep.
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1.
    call memcpy_n0_spec; first [exact MI1 | exact RS0 | exact RD0 | idtac].
    do 12 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.
  Lemma inv0_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV0 mc.
  Proof. intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. split; [exists jk; exact FR|]. repeat (split; [assumption|]). assumption. Qed.

  Lemma LW0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x28 x29 x30 x31,
    INV0 mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 (Z_to_bv 64 (-65)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5ccac) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LX0; exact IV.
  Qed.

  Lemma LR0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV0 mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5cc60) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LW0; exact IV.
  Qed.

  Lemma asan_memcpy0_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x5cc04) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
    carve_frame 2144%nat ST0.
    do 12 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. lia. }
    do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IV : INV0 m1) by (eapply inv0_of; eassumption) end.
    zstep. if_cases K1; zify_cond K1.
    { eapply LR0; exact IV. }
    zstep. if_cases K2; zify_cond K2.
    { eapply LR0; exact IV. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K1 K2 K3 B. lia. }
    eapply LR0; exact IV.
  Qed.
End Proofs.

Lemma asan_memcpy_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a1) 0 -> rng RNG (bv_unsigned a0) 0 ->
  evtF asegs RNG (asan_memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5cc04) fc None m (seg_rom asegs)).
Proof. intros. eapply asan_memcpy0_body; eassumption. Qed.

Lemma asan_memcpy_spec0_any : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (asan_memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5cc04) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO G1 G2 G3 G4 G5 G6 RI RSTK.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R0, R1.
  apply evtF_fp_zero.
  eapply asan_memcpy_spec0; try eassumption.
  - apply rng_fp_zero_mono; exact RI.
  - apply rng_fp_zero_mono; exact RSTK.
  - apply rng_fp_zero. lia.
  - apply rng_fp_zero. lia.
Qed.
End CANSEC1.
End I_asan_memcpy0.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_syscalls F_tryinit.
Module I_read.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ShadowTac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rip.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition read_i_entry := 0x4f1f8%Z.

Definition read_i_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB n junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z).
  Notation B := (bv_unsigned a1).
  Notation W := [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + count); (errno_addr tp, errno_addr tp + 4)]%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_read m.
  Hypothesis DST : rw_cells asegs m B [CB (Z.to_nat count) junk].
  Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
  Hypothesis A0 : a0 = Z_to_bv 64 fd.
  Hypothesis A2 : a2 = Z_to_bv 64 count.
  Hypothesis FD : (3 <= fd < 2^32)%Z.
  Hypothesis CNT : (1 <= count <= 16777216)%Z.

  Hypothesis BHI : (0x62f000 <= B \/ (0x5fc110 <= B /\ B + count <= 0x60c110 /\ B + count <= errno_addr tp))%Z.
  Hypothesis SEPD : (B + count <= lo)%Z.
  Hypothesis SEPE : (0xdacc0 <= errno_addr tp /\ errno_addr tp + 4 <= 0x62f000)%Z.
  Hypothesis TP : (164 <= bv_unsigned tp)%Z.
  Hypothesis APPD : app_blk B (B + count).
  Hypothesis UDST : unpoisoned m B (B + count).
  Hypothesis R2 : (RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (errno_addr tp) 4.
  Hypothesis RD : rng RNG B count.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m).

  Definition INV2 (bs : list byte) (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2128)
    /\ munch W m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_read mc
    /\ unpoisoned mc B (B + count)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2)
    /\ rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
    /\ rw_cells asegs mc (errno_addr tp) [C4 errv]
    /\ (length bs <= Z.to_nat count)%nat.

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 1 <= count <= 16777216
     /\ 0x5fc110 <= B /\ (0x62f000 <= B \/ B + count <= 0x60c110 /\ B + count <= errno_addr tp) /\ B + count <= lo /\ B + count + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr B 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0
     /\ 0xdacc0 <= errno_addr tp /\ errno_addr tp + 4 <= 0x62f000)%Z.

  Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. nia.
  Qed.

  Ltac acc_facts Bf ::= pose proof BND_ok as Bf; unfold BND, KHIGH, KEND in Bf.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 1 <= count <= 16777216 /\ 0x5fc110 <= B /\ (0x62f000 <= B \/ B + count <= 0x60c110 /\ B + count <= errno_addr tp) /\ B + count <= lo
     /\ B + count + 8 <= 2^47 /\ 0 <= Z.shiftr B 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296
     /\ 0xdacc0 <= errno_addr tp /\ errno_addr tp + 4 <= 0x62f000)%Z.
  Lemma BL_ok : BL. Proof. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & INI1 & LAY1 & REAL1 & UD1 & WR21 & BUF1 & ERR1 & LENB).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let Bl := fresh "BL" in pose proof BL_ok as Bl; unfold BL in Bl;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in ERR; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.

  Lemma inv2_of : forall bs mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2128) ->
    munch W m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_read mc ->
    rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)] ->
    rw_cells asegs mc (errno_addr tp) [C4 errv] -> (length bs <= Z.to_nat count)%nat ->
    INV2 bs mc.
  Proof.
    intros bs mc jk FR ST1 MU1 WM1 MI1 G1 G3 G4 G5 G6 BUF1 ERR1 LENB. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : (shad (B + count - 1) + 1 <= 17594333495296 /\ 2147450880 <= shad B /\
                  (B + count <= shad B \/ shad (B + count - 1) + 1 <= B))%Z).
    { pose proof APPD as [_ AD]. unfold KLOW, KHIGH, KEND in AD. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma LX : forall bs mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat (length bs))) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4f2a8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 9 zstep.
    release_frame FR ST1 (bv_unsigned sp). unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish.
  Qed.

  Lemma LSL : forall bs mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    Z.to_nat (shad (B + Z.of_nat (length bs) - 1) - c) = k -> (shad B <= c < shad (B + Z.of_nat (length bs) - 1))%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4f40c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (B + Z.of_nat (length bs) - 1) = 2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)%Z)
      by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc B (B + count) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  Lemma LSS : forall bs mc x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 (2147450880 + Z.shiftr B 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3))
               (Z_to_bv 64 (B + Z.of_nat (length bs) + -1)) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4f3f0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    pose proof (shad_mono B (B + Z.of_nat (length bs) - 1) ltac:(lia)) as SM2.
    destruct (unpoisoned_check_rd asegs mc B (B + count) (B + Z.of_nat (length bs) + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((B + Z.of_nat (length bs) + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LSL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  Lemma LC : forall bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4f248) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    assert (Rr : (0 <= Z.of_nat (length bs) <= count)%Z) by lia.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. if_cases KZ; zify_lts KZ.
    {   eapply LX; eassumption. }
    assert (R1' : (1 <= Z.of_nat (length bs))%Z) by lia.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      do 4 zstep.
      unfold sf_hide in DST.
      pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; eapply app_blk_sub; [exact APPD | lia | lia | lia]
        | zsimp; eapply unpoisoned_sub; [exact UD1 | lia | lia]
        | zsimp; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 3 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv2_of; eassumption.
    -
      assert (N1 : (Z.of_nat (length bs) <= 64)%Z) by (clear - K2 Rr R1' BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 B WR21 ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (B + Z.of_nat (length bs) + -1) WR21
                  ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LSS; [eassumption | lia].
      + eapply LX; eassumption.
  Qed.

  Lemma read_i_body :
    implA asegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
          (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x4f1f8) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    pose proof DST as DST0. change (?P) with (sf_hide P) in DST. pose proof ERR as ERR0. change (?P) with (sf_hide P) in ERR.
    rewrite A0, A2.
    iprefix.
    carve_frame 2128%nat ST0.
    do 9 zstep. do 3 zstep. zstep.
    call_sp tryinit_spec; [ assumption | exact ST0 | lia | unfold KHIGH; lia | assumption | eapply rng_sub'; [exact RSTK | lia] | ].
    do 6 zstep. zstep.
    name_sp sp (-2128)%Z.
    Local Ltac usp := match goal with H : bv_unsigned _ = (bv_unsigned sp + -2128)%Z |- _ => rewrite H end.
    icallk read_spec;
      [ usp; eassumption | eassumption | eassumption | assumption | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | lia | lia
      | usp; eapply rng_sub'; [exact RSTK | lia] | ].
    ipost asegs. unname_sp.
    lazymatch goal with P : context [match ?a with RdErr _ => _ | RdData _ => _ end] |- _ => rename P into RP end.
    destruct ans as [e|bs]; cbn [read_ret].
    -
      destruct RP as (BUFe & ERRe & He).
      zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
      zstep. if_cases KZ; zify_lts KZ. 2:{ exfalso. clear - KZ. lia. }
      do 9 zstep.
      lazymatch goal with ST2 : stk asegs _ lo _ |- _ => release_frame FR ST2 (bv_unsigned sp) end.
      unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish; lia.
    -
      destruct RP as (BUF1 & ERR1 & LENB).
      eapply LC. eapply inv2_of; try eassumption.
  Qed.
End Proofs.

Lemma read_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_read m ->
  rw_cells asegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (0x62f000 <= bv_unsigned a1 \/ (0x5fc110 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= 0x60c110 /\ bv_unsigned a1 + count <= errno_addr tp))%Z -> (bv_unsigned a1 + count <= lo)%Z ->
  (0xdacc0 <= errno_addr tp /\ errno_addr tp + 4 <= 0x62f000)%Z -> (164 <= bv_unsigned tp)%Z ->
  app_blk (bv_unsigned a1) (bv_unsigned a1 + count) ->
  unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + count) ->
  (RLO2 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (errno_addr tp) 4 -> rng RNG (bv_unsigned a1) count ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  implA asegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
        (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x4f1f8) fc None m (seg_rom asegs)).
Proof. intros. eapply read_i_body; eassumption. Qed.
End CANSEC1.
End I_read.

Module I_memcpy0.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.FpZero.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ShadowTac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_memcpy. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rip.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy. Import I_asan_memcpy0.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.

Definition memcpy_i0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation a2 := (Z_to_bv 64 0).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RS0 : rng RNG S 0.
  Hypothesis RD0 : rng RNG D 0.

  Notation POST := (memcpy_i0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m).

  Definition INV0 (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2160)
                  [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2160)
    /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc.

  Ltac inv_open0 H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1).

  Definition BL0 : Prop := (0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ 17594333495296 <= lo /\ 0 <= S < 2^64 /\ 0 <= D < 2^64)%Z.
  Lemma BL0_ok : BL0.
  Proof.
    unfold BL0. destruct ST as (L0 & _). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in *.
    change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. lia.
  Qed.

  Lemma LX0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV0 mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5db84) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof IV as IV0. inv_open0 IV. pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]).
    zstep. zstep. zstep.
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1.
    call memcpy_n0_spec; first [exact MI1 | exact RS0 | exact RD0 | idtac].
    do 13 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.
  Lemma inv0_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2160) [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2160) ->
    munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV0 mc.
  Proof. intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. split; [exists jk; exact FR|]. repeat (split; [assumption|]). assumption. Qed.

  Lemma LW0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x28 x29 x30 x31,
    INV0 mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 (Z_to_bv 64 (-65)) x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5db3c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LX0; exact IV.
  Qed.

  Lemma LR0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV0 mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5daf0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LW0; exact IV.
  Qed.

  Lemma memcpy_i0_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x5da90) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2160)%Z) by lia.
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
    carve_frame 2160%nat ST0.
    do 13 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. lia. }
    do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IV : INV0 m1) by (eapply inv0_of; eassumption) end.
    zstep. if_cases K1; zify_cond K1.
    { eapply LR0; exact IV. }
    zstep. if_cases K2; zify_cond K2.
    { eapply LR0; exact IV. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K1 K2 K3 B. lia. }
    eapply LR0; exact IV.
  Qed.
End Proofs.

Lemma memcpy_i_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a1) 0 -> rng RNG (bv_unsigned a0) 0 ->
  evtF asegs RNG (memcpy_i0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5da90) fc None m (seg_rom asegs)).
Proof. intros. eapply memcpy_i0_body; eassumption. Qed.

Lemma memcpy_i_spec0_any : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (memcpy_i0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5da90) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO G1 G2 G3 G4 G5 G6 RI RSTK.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R0, R1.
  apply evtF_fp_zero.
  eapply memcpy_i_spec0; try eassumption.
  - apply rng_fp_zero_mono; exact RI.
  - apply rng_fp_zero_mono; exact RSTK.
  - apply rng_fp_zero. lia.
  - apply rng_fp_zero. lia.
Qed.
End CANSEC1.
End I_memcpy0.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module I_asan_memcpy0.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.FpZero.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ShadowTac.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_memcpy.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rip.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_asan_memcpy.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.

Definition asan_memcpy0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition memcpy_n0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Lemma memcpy_n0_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv bsegs m ->
  rng RNG (bv_unsigned a1) 0 -> rng RNG (bv_unsigned a0) 0 ->
  evtF bsegs RNG (memcpy_n0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc95bc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI RS RD.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in *.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
  eapply evtF_mono.
  - apply (memcpy_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [] []).
    + apply bytes_at_nil. lia.
    + reflexivity.
    + split; [split; [cbn; auto| cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia]|]. cbn [cells_size csize Nat.add]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. split; [lia|]. split; [lia|]. intros i Hi. lia.
    + change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    + exact MI.
    + exact RS.
    + exact RD.
  - cbv beta. intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & E & MU & WM & MI' & _).
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m'. split; [exact E|]. split; [| split; [exact WM| exact MI']].
    eapply munch_weaken; [| exact MU]. intros x _. cbn [outside]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. split; [lia| exact I].
Qed.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation a2 := (Z_to_bv 64 0).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RS0 : rng RNG S 0.
  Hypothesis RD0 : rng RNG D 0.

  Notation POST := (asan_memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m).

  Definition INV0 (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells bsegs mc (bv_unsigned sp + -2144)
                  [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk bsegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
    /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc.

  Ltac inv_open0 H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1).

  Definition BL0 : Prop := (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= S < 2^64 /\ 0 <= D < 2^64)%Z.
  Lemma BL0_ok : BL0.
  Proof.
    unfold BL0. destruct ST as (L0 & _). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in *.
    change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. lia.
  Qed.

  Lemma LX0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV0 mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5d684) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. pose proof IV as IV0. inv_open0 IV. pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    zstep. zstep. zstep.
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1.
    call memcpy_n0_spec; first [exact MI1 | exact RS0 | exact RD0 | idtac].
    do 12 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.
  Lemma inv0_of : forall mc jk,
    rw_cells bsegs mc (bv_unsigned sp + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV0 mc.
  Proof. intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. split; [exists jk; exact FR|]. repeat (split; [assumption|]). assumption. Qed.

  Lemma LW0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x28 x29 x30 x31,
    INV0 mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 (Z_to_bv 64 (-65)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5d63c) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LX0; exact IV.
  Qed.

  Lemma LR0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV0 mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5d5f0) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LW0; exact IV.
  Qed.

  Lemma asan_memcpy0_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x5d594) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
    carve_frame 2144%nat ST0.
    do 12 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. lia. }
    do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IV : INV0 m1) by (eapply inv0_of; eassumption) end.
    zstep. if_cases K1; zify_cond K1.
    { eapply LR0; exact IV. }
    zstep. if_cases K2; zify_cond K2.
    { eapply LR0; exact IV. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K1 K2 K3 B. lia. }
    eapply LR0; exact IV.
  Qed.
End Proofs.

Lemma asan_memcpy_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a1) 0 -> rng RNG (bv_unsigned a0) 0 ->
  evtF bsegs RNG (asan_memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d594) fc None m (seg_rom bsegs)).
Proof. intros. eapply asan_memcpy0_body; eassumption. Qed.

Lemma asan_memcpy_spec0_any : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (asan_memcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d594) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST LO KLO G1 G2 G3 G4 G5 G6 RI RSTK.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R0, R1.
  apply evtF_fp_zero.
  eapply asan_memcpy_spec0; try eassumption.
  - apply rng_fp_zero_mono; exact RI.
  - apply rng_fp_zero_mono; exact RSTK.
  - apply rng_fp_zero. lia.
  - apply rng_fp_zero. lia.
Qed.
End CANSEC1.
End I_asan_memcpy0.

Module I_read.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ShadowTac.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_syscalls.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rip.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition read_i_entry := 0x4fb88%Z.

Definition read_i_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells bsegs m' B [CB n junk]
                    /\ rw_cells bsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells bsegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z).
  Notation B := (bv_unsigned a1).
  Notation W := [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + count); (errno_addr tp, errno_addr tp + 4)]%Z.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_read m.
  Hypothesis DST : rw_cells bsegs m B [CB (Z.to_nat count) junk].
  Hypothesis ERR : rw_cells bsegs m (errno_addr tp) [C4 errv].
  Hypothesis A0 : a0 = Z_to_bv 64 fd.
  Hypothesis A2 : a2 = Z_to_bv 64 count.
  Hypothesis FD : (3 <= fd < 2^32)%Z.
  Hypothesis CNT : (1 <= count <= 16777216)%Z.

  Hypothesis BHI : (0x631000 <= B \/ (0x5fe2d0 <= B /\ B + count <= 0x60e2d0 /\ B + count <= errno_addr tp))%Z.
  Hypothesis SEPD : (B + count <= lo)%Z.
  Hypothesis SEPE : (0xdce80 <= errno_addr tp /\ errno_addr tp + 4 <= 0x631000)%Z.
  Hypothesis TP : (164 <= bv_unsigned tp)%Z.
  Hypothesis APPD : app_blk B (B + count).
  Hypothesis UDST : unpoisoned m B (B + count).
  Hypothesis R2 : (RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (errno_addr tp) 4.
  Hypothesis RD : rng RNG B count.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m).

  Definition INV2 (bs : list byte) (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells bsegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk bsegs mc lo (bv_unsigned sp + -2128)
    /\ munch W m mc
    /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_read mc
    /\ unpoisoned mc B (B + count)
    /\ wr_at bsegs mc (shad RLO2) (shad RHI2 - shad RLO2)
    /\ rw_cells bsegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
    /\ rw_cells bsegs mc (errno_addr tp) [C4 errv]
    /\ (length bs <= Z.to_nat count)%nat.

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 1 <= count <= 16777216
     /\ 0x5fe2d0 <= B /\ (0x631000 <= B \/ B + count <= 0x60e2d0 /\ B + count <= errno_addr tp) /\ B + count <= lo /\ B + count + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr B 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0
     /\ 0xdce80 <= errno_addr tp /\ errno_addr tp + 4 <= 0x631000)%Z.

  Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. nia.
  Qed.

  Ltac acc_facts Bf ::= pose proof BND_ok as Bf; unfold BND, KHIGH, KEND in Bf.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 1 <= count <= 16777216 /\ 0x5fe2d0 <= B /\ (0x631000 <= B \/ B + count <= 0x60e2d0 /\ B + count <= errno_addr tp) /\ B + count <= lo
     /\ B + count + 8 <= 2^47 /\ 0 <= Z.shiftr B 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296
     /\ 0xdce80 <= errno_addr tp /\ errno_addr tp + 4 <= 0x631000)%Z.
  Lemma BL_ok : BL. Proof. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & INI1 & LAY1 & REAL1 & UD1 & WR21 & BUF1 & ERR1 & LENB).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let Bl := fresh "BL" in pose proof BL_ok as Bl; unfold BL in Bl;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in ERR; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.

  Lemma inv2_of : forall bs mc jk,
    rw_cells bsegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs mc lo (bv_unsigned sp + -2128) ->
    munch W m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_read mc ->
    rw_cells bsegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)] ->
    rw_cells bsegs mc (errno_addr tp) [C4 errv] -> (length bs <= Z.to_nat count)%nat ->
    INV2 bs mc.
  Proof.
    intros bs mc jk FR ST1 MU1 WM1 MI1 G1 G3 G4 G5 G6 BUF1 ERR1 LENB. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : (shad (B + count - 1) + 1 <= 17594333495296 /\ 2147450880 <= shad B /\
                  (B + count <= shad B \/ shad (B + count - 1) + 1 <= B))%Z).
    { pose proof APPD as [_ AD]. unfold KLOW, KHIGH, KEND in AD. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma LX : forall bs mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF bsegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat (length bs))) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4fc38) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 9 zstep.
    release_frame FR ST1 (bv_unsigned sp). unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish.
  Qed.

  Lemma LSL : forall bs mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    Z.to_nat (shad (B + Z.of_nat (length bs) - 1) - c) = k -> (shad B <= c < shad (B + Z.of_nat (length bs) - 1))%Z ->
    evtF bsegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4fd9c) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (B + Z.of_nat (length bs) - 1) = 2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)%Z)
      by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc B (B + count) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  Lemma LSS : forall bs mc x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    evtF bsegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 (2147450880 + Z.shiftr B 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3))
               (Z_to_bv 64 (B + Z.of_nat (length bs) + -1)) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4fd80) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    pose proof (shad_mono B (B + Z.of_nat (length bs) - 1) ltac:(lia)) as SM2.
    destruct (unpoisoned_check_rd bsegs mc B (B + count) (B + Z.of_nat (length bs) + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((B + Z.of_nat (length bs) + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LSL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  Lemma LC : forall bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF bsegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4fbd8) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    assert (Rr : (0 <= Z.of_nat (length bs) <= count)%Z) by lia.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. if_cases KZ; zify_lts KZ.
    {   eapply LX; eassumption. }
    assert (R1' : (1 <= Z.of_nat (length bs))%Z) by lia.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      do 4 zstep.
      unfold sf_hide in DST.
      pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; eapply app_blk_sub; [exact APPD | lia | lia | lia]
        | zsimp; eapply unpoisoned_sub; [exact UD1 | lia | lia]
        | zsimp; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 3 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv2_of; eassumption.
    -
      assert (N1 : (Z.of_nat (length bs) <= 64)%Z) by (clear - K2 Rr R1' BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 bsegs mc RLO2 RHI2 B WR21 ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 bsegs mc RLO2 RHI2 (B + Z.of_nat (length bs) + -1) WR21
                  ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LSS; [eassumption | lia].
      + eapply LX; eassumption.
  Qed.

  Lemma read_i_body :
    implA bsegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
          (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x4fb88) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    pose proof DST as DST0. change (?P) with (sf_hide P) in DST. pose proof ERR as ERR0. change (?P) with (sf_hide P) in ERR.
    rewrite A0, A2.
    iprefix.
    carve_frame 2128%nat ST0.
    do 9 zstep. do 3 zstep. zstep.
    call_sp tryinit_spec; [ assumption | exact ST0 | lia | unfold KHIGH; lia | assumption | eapply rng_sub'; [exact RSTK | lia] | ].
    do 6 zstep. zstep.
    name_sp sp (-2128)%Z.
    Local Ltac usp := match goal with H : bv_unsigned _ = (bv_unsigned sp + -2128)%Z |- _ => rewrite H end.
    icallk read_spec;
      [ usp; eassumption | eassumption | eassumption | assumption | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | lia | lia
      | usp; eapply rng_sub'; [exact RSTK | lia] | ].
    ipost bsegs. unname_sp.
    lazymatch goal with P : context [match ?a with RdErr _ => _ | RdData _ => _ end] |- _ => rename P into RP end.
    destruct ans as [e|bs]; cbn [read_ret].
    -
      destruct RP as (BUFe & ERRe & He).
      zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
      zstep. if_cases KZ; zify_lts KZ. 2:{ exfalso. clear - KZ. lia. }
      do 9 zstep.
      lazymatch goal with ST2 : stk bsegs _ lo _ |- _ => release_frame FR ST2 (bv_unsigned sp) end.
      unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish; lia.
    -
      destruct RP as (BUF1 & ERR1 & LENB).
      eapply LC. eapply inv2_of; try eassumption.
  Qed.
End Proofs.

Lemma read_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_read m ->
  rw_cells bsegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (0x631000 <= bv_unsigned a1 \/ (0x5fe2d0 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= 0x60e2d0 /\ bv_unsigned a1 + count <= errno_addr tp))%Z -> (bv_unsigned a1 + count <= lo)%Z ->
  (0xdce80 <= errno_addr tp /\ errno_addr tp + 4 <= 0x631000)%Z -> (164 <= bv_unsigned tp)%Z ->
  app_blk (bv_unsigned a1) (bv_unsigned a1 + count) ->
  unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + count) ->
  (RLO2 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (errno_addr tp) 4 -> rng RNG (bv_unsigned a1) count ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  implA bsegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
        (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x4fb88) fc None m (seg_rom bsegs)).
Proof. intros. eapply read_i_body; eassumption. Qed.
End CANSEC1.
End I_read.

Module I_memcpy0.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.FpZero.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ShadowTac.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_memcpy.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_rip.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy. Import I_asan_memcpy0.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.

Definition memcpy_i0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation a2 := (Z_to_bv 64 0).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RS0 : rng RNG S 0.
  Hypothesis RD0 : rng RNG D 0.

  Notation POST := (memcpy_i0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m).

  Definition INV0 (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells bsegs mc (bv_unsigned sp + -2160)
                  [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk bsegs mc lo (bv_unsigned sp + -2160)
    /\ munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc
    /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc.

  Ltac inv_open0 H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1).

  Definition BL0 : Prop := (0 <= lo /\ lo <= bv_unsigned sp - 2240 /\ 17594333495296 <= lo /\ 0 <= S < 2^64 /\ 0 <= D < 2^64)%Z.
  Lemma BL0_ok : BL0.
  Proof.
    unfold BL0. destruct ST as (L0 & _). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in *.
    change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. lia.
  Qed.

  Lemma LX0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV0 mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5e514) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. pose proof IV as IV0. inv_open0 IV. pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]).
    zstep. zstep. zstep.
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1.
    call memcpy_n0_spec; first [exact MI1 | exact RS0 | exact RD0 | idtac].
    do 13 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.
  Lemma inv0_of : forall mc jk,
    rw_cells bsegs mc (bv_unsigned sp + -2160) [CB 2080 jk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs mc lo (bv_unsigned sp + -2160) ->
    munch [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV0 mc.
  Proof. intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. split; [exists jk; exact FR|]. repeat (split; [assumption|]). assumption. Qed.

  Lemma LW0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x28 x29 x30 x31,
    INV0 mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 (Z_to_bv 64 (-65)) x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5e4cc) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LX0; exact IV.
  Qed.

  Lemma LR0 : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    INV0 mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5e480) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. pose proof BL0_ok as B. unfold BL0 in B.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2. lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. }
    zstep. eapply LW0; exact IV.
  Qed.

  Lemma memcpy_i0_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x5e420) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BL0_ok as B. unfold BL0 in B.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2240) 2240) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2160)%Z) by lia.
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
    carve_frame 2160%nat ST0.
    do 13 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. lia. }
    do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IV : INV0 m1) by (eapply inv0_of; eassumption) end.
    zstep. if_cases K1; zify_cond K1.
    { eapply LR0; exact IV. }
    zstep. if_cases K2; zify_cond K2.
    { eapply LR0; exact IV. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K1 K2 K3 B. lia. }
    eapply LR0; exact IV.
  Qed.
End Proofs.

Lemma memcpy_i_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a1) 0 -> rng RNG (bv_unsigned a0) 0 ->
  evtF bsegs RNG (memcpy_i0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e420) fc None m (seg_rom bsegs)).
Proof. intros. eapply memcpy_i0_body; eassumption. Qed.

Lemma memcpy_i_spec0_any : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (memcpy_i0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e420) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST LO KLO G1 G2 G3 G4 G5 G6 RI RSTK.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R0, R1.
  apply evtF_fp_zero.
  eapply memcpy_i_spec0; try eassumption.
  - apply rng_fp_zero_mono; exact RI.
  - apply rng_fp_zero_mono; exact RSTK.
  - apply rng_fp_zero. lia.
  - apply rng_fp_zero. lia.
Qed.
End CANSEC1.
End I_memcpy0.
End TwinB.
