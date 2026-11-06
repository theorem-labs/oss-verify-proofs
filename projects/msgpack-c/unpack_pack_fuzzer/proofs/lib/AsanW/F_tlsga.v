(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg RtCells AProto ABase F_tryinit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit FsKit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_tlsga.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition AFSDESC : Z := 0xd2298.
Definition AREAL_TLSGA : Z := 0xd3358.
Definition ATLSGA : Z := 0xc8094.
Definition ADTLSF : Z := 0x75bf8.
Definition ATLSGA_ICPT : Z := 0x51e50.
Definition ADTV : Z := 0x60cca0.
Definition ADTLSV : Z := 0x60cc88.
Definition AVERB : Z := 0x169558.
Definition ACF137 : Z := 0x16b671.

End CANSEC1.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC2. Context {rc : runConstT}.
Lemma musl_tlsga_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (fsw : word),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw] ->
  rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AFSDESC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA) fc None m (seg_rom asegs)).
Proof.
  intros until fsw. intros -> DESC DTVP DTV1 RIMG.
  unfold AFSDESC, ATP, ADTV, ATLSGA in *. lit_in DTVP; lit_in DTV1.
  do 9 zstep. finish.
Qed.

Definition dtls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma dtls_fast_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo B v : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_got m ->
  rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd1568 [C8 (Z_to_bv 64 AVERB)] ->
  rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells asegs m 0xd22a8 [C8 (Z_to_bv 64 8)] ->
  rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)] ->
  iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG B 4096 ->
  evtF asegs RNG (dtls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADTLSF) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros MI ST LO CEIL -> -> G50 CF GB0 VERB DESC G08 DV BD BLO BHI V RIMG RSTK RB. destruct BLO as [BLO _].
  unfold GOT_CFLAGS, ACFLAGS, ACF137, AVERB, AFSDESC, ADTLSV, ADTLSF, ATP, AIMG_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 144%nat ST.
  do 14 zstep.
  zstep.
  zstep. zstep.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].
  zstep. zstep. zstep.
  zstep.
  zstep. zstep; lits.
  zstep.
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].
  zstep.
  zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 V BHI; lia|].
  zstep. if_cases K4; zify_cond K4; [| exfalso; clear - K4 BLO; lia].
  zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 BLO; lia|].
  zstep. zstep.
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; clear - K6; lia].
  zstep. zstep. zstep.
  zstep.
  zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7 V; lia|].
  do 16 zstep.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Definition tlsga_cells (m : amem) (t B v : Z) (fsw : word) : Prop :=
     rw_cells asegs m AREAL_TLSGA [C8 (Z_to_bv 64 ATLSGA)]
  /\ rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]
  /\ rw_cells asegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw]
  /\ rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))]
  /\ rt_got m
  /\ rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xd1568 [C8 (Z_to_bv 64 AVERB)]
  /\ rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xd22a8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)]
  /\ rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)]
  /\ (exists tb te : word, rw_cells asegs m (t + 48) [C8 tb; C8 te]).

Definition tlsga_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma tlsga_icpt_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo ctx t B v : Z) (fsw : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v fsw ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  evtF asegs RNG (tlsga_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).
Proof.
  intros until fsw. intros MI ST LO CEIL TP A0 INI TI TK T88 TSD CT
         (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48))
         C0 C1 T0 T1 BLO BHI V RIMG RSTK RCTX RT RB.
  subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).

  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ATLSGA_ICPT, ATLSGA in *.
  lit_in DTVP; lit_in DTV1.
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.

  zstep. call_sp tryinit_spec;
    first [exact MI| exact ST| exact INI| exact RIMG| unfold KHIGH; lia| solve_rng | idtac].
  rename PC into ST. clear POST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI1 end.
  zstep. zstep.
  zstep. zstep.
  zstep.
  callp musl_tlsga_spec; first [exact TP| exact DESC| exact DTVP| exact DTV1| exact RIMG| idtac].
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].

  box RT; box RB.
  zstep. call_sp get_current_thread_spec;
    first [exact ST| exact MI1| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| exact RIMG| exact RCTX
          | atop_facts; lia| solve_rng | idtac].
  unbox RT; unbox RB. rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 T0; lia|].
  zstep. zstep.
  zstep. zstep. zstep.

  zstep. call_sp dtls_fast_spec;
    first [exact MI2| exact ST| exact TP| reflexivity| exact G50| exact CF| exact GB0| exact VERB| exact DESC
          | exact G08| exact DV| exact BD| exact RIMG| exact RB| exact BLO| unfold AIMG_HI; lia| solve_rng | idtac].
  rename POST into ST.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp). subst tp. finish.
Qed.
End CANSEC2.

End F_tlsga.

Module F_tlsgaG.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. Import F_tlsga.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC2. Context {rc : runConstT}.
Lemma musl_tlsga_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (fsw : word) (A : Z),
  tp = Z_to_bv 64 ATP ->
  ro_cells asegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> rng RNG A 16 ->
  rw_cells asegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw] ->
  rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))] ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ATP + 0x800)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA) fc None m (seg_rom asegs)).
Proof.
  intros until A. intros -> DESC RA DTVP DTV1 RIMG.
  pose proof (ro_cells_bound asegs m A _ DESC) as AB. cbn [cells_size csize Nat.add] in AB.
  unfold ATP, ADTV, ATLSGA in *. lit_in DTVP; lit_in DTV1.
  do 9 zstep. finish.
Qed.

Definition dtls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma dtls_fast_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo B v A : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  rt_got m ->
  rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd1568 [C8 (Z_to_bv 64 AVERB)] ->
  rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)] ->
  ro_cells asegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> rng RNG A 16 ->
  rw_cells asegs m 0xd22a8 [C8 (Z_to_bv 64 8)] ->
  rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)] ->
  rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)] ->
  iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG B 4096 ->
  evtF asegs RNG (dtls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADTLSF) fc None m (seg_rom asegs)).
Proof.
  intros until A. intros MI ST LO CEIL -> -> ABV G50 CF GB0 VERB DESC RA G08 DV BD BLO BHI V RIMG RSTK RB. destruct BLO as [BLO _].
  pose proof (ro_cells_bound asegs m A _ DESC) as AB. cbn [cells_size csize Nat.add] in AB.
  unfold GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ADTLSF, ATP, AIMG_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 144%nat ST.
  do 14 zstep.
  zstep.
  zstep. zstep.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].
  zstep. zstep. zstep.
  zstep.
  zstep. zstep; lits.
  zstep.
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].
  zstep.
  zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 V BHI; lia|].
  zstep. if_cases K4; zify_cond K4; [| exfalso; clear - K4 BLO; lia].
  zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 BLO; lia|].
  zstep. zstep.
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; clear - K6; lia].
  zstep. zstep. zstep.
  zstep.
  zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7 V; lia|].
  do 16 zstep.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Definition tlsga_gcells (m : amem) (t B v : Z) (fsw : word) : Prop :=
     rw_cells asegs m AREAL_TLSGA [C8 (Z_to_bv 64 ATLSGA)]
  /\ rw_cells asegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw]
  /\ rw_cells asegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))]
  /\ rt_got m
  /\ rw_cells asegs m ACF137 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xd1568 [C8 (Z_to_bv 64 AVERB)]
  /\ rw_cells asegs m AVERB [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xd22a8 [C8 (Z_to_bv 64 8)]
  /\ rw_cells asegs m ADTLSV [C8 (Z_to_bv 64 B)]
  /\ rw_cells asegs m (B + 24) [C8 (Z_to_bv 64 v)]
  /\ (exists tb te : word, rw_cells asegs m (t + 48) [C8 tb; C8 te]).

Definition tlsga_icpt_gpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ATP + 0x800)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma tlsga_icpt_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo ctx t B v : Z) (fsw : word) (A : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells asegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> rng RNG A 16 ->
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_gcells m t B v fsw ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  evtF asegs RNG (tlsga_icpt_gpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).
Proof.
  intros until A. intros MI ST LO CEIL TP A0 ABV DESC RA INI TI TK T88 TSD CT
         (REAL & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48))
         C0 C1 T0 T1 BLO BHI V RIMG RSTK RCTX RT RB.
  subst a0.
  pose proof (ro_cells_bound asegs m A _ DESC) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).

  unfold AIMG_HI, AREAL_TLSGA, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ATLSGA_ICPT, ATLSGA in *.
  lit_in DTVP; lit_in DTV1.
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.

  zstep. call_sp tryinit_spec;
    first [exact MI| exact ST| exact INI| exact RIMG| unfold KHIGH; lia| solve_rng | idtac].
  rename PC into ST. clear POST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI1 end.
  zstep. zstep.
  zstep. zstep.
  zstep.
  callp musl_tlsga_gspec; first [exact TP| exact DESC| exact RA| exact DTVP| exact DTV1| exact RIMG| idtac].
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].

  box RT; box RB.
  zstep. call_sp get_current_thread_spec;
    first [exact ST| exact MI1| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| exact RIMG| exact RCTX
          | atop_facts; lia| solve_rng | idtac].
  unbox RT; unbox RB. rename POST into ST.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 T0; lia|].
  zstep. zstep.
  zstep. zstep. zstep.

  zstep. call_sp dtls_fast_gspec;
    first [exact MI2| exact ST| exact TP| reflexivity| exact G50| exact CF| exact GB0| exact VERB| exact DESC| exact RA
          | exact G08| exact DV| exact BD| exact RIMG| exact RB| exact BLO| unfold AIMG_HI; lia| solve_rng | idtac].
  rename POST into ST.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp). subst tp. finish.
Qed.
End CANSEC2.

End F_tlsgaG.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_tlsga.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition AFSDESC : Z := 0xd43b0.
Definition AREAL_TLSGA : Z := 0xd5470.
Definition ATLSGA : Z := 0xca1b0.
Definition ADTLSF : Z := 0x76588.
Definition ATLSGA_ICPT : Z := 0x527e0.
Definition ADTV : Z := 0x60ee60.
Definition ADTLSV : Z := 0x60ee48.
Definition AVERB : Z := 0x16b718.
Definition ACF137 : Z := 0x16d831.

End CANSEC1.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC2. Context {rc : runConstT}.
Lemma musl_tlsga_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (fsw : word),
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells bsegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw] ->
  rw_cells bsegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))] ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AFSDESC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA) fc None m (seg_rom bsegs)).
Proof.
  intros until fsw. intros -> DESC DTVP DTV1 RIMG.
  unfold AFSDESC, ATP, ADTV, ATLSGA in *. lit_in DTVP; lit_in DTV1.
  do 9 zstep. finish.
Qed.

Definition dtls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma dtls_fast_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo B v : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_got m ->
  rw_cells bsegs m ACF137 [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd3680 [C8 (Z_to_bv 64 AVERB)] ->
  rw_cells bsegs m AVERB [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)] ->
  rw_cells bsegs m 0xd43c0 [C8 (Z_to_bv 64 8)] ->
  rw_cells bsegs m ADTLSV [C8 (Z_to_bv 64 B)] ->
  rw_cells bsegs m (B + 24) [C8 (Z_to_bv 64 v)] ->
  iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG B 4096 ->
  evtF bsegs RNG (dtls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADTLSF) fc None m (seg_rom bsegs)).
Proof.
  intros until v. intros MI ST LO CEIL -> -> G50 CF GB0 VERB DESC G08 DV BD BLO BHI V RIMG RSTK RB. destruct BLO as [BLO _].
  unfold GOT_CFLAGS, ACFLAGS, ACF137, AVERB, AFSDESC, ADTLSV, ADTLSF, ATP, AIMG_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 144%nat ST.
  do 14 zstep.
  zstep.
  zstep. zstep.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].
  zstep. zstep. zstep.
  zstep.
  zstep. zstep; lits.
  zstep.
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].
  zstep.
  zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 V BHI; lia|].
  zstep. if_cases K4; zify_cond K4; [| exfalso; clear - K4 BLO; lia].
  zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 BLO; lia|].
  zstep. zstep.
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; clear - K6; lia].
  zstep. zstep. zstep.
  zstep.
  zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7 V; lia|].
  do 16 zstep.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Definition tlsga_cells (m : amem) (t B v : Z) (fsw : word) : Prop :=
     rw_cells bsegs m AREAL_TLSGA [C8 (Z_to_bv 64 ATLSGA)]
  /\ rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]
  /\ rw_cells bsegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw]
  /\ rw_cells bsegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))]
  /\ rt_got m
  /\ rw_cells bsegs m ACF137 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xd3680 [C8 (Z_to_bv 64 AVERB)]
  /\ rw_cells bsegs m AVERB [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xd43c0 [C8 (Z_to_bv 64 8)]
  /\ rw_cells bsegs m ADTLSV [C8 (Z_to_bv 64 B)]
  /\ rw_cells bsegs m (B + 24) [C8 (Z_to_bv 64 v)]
  /\ (exists tb te : word, rw_cells bsegs m (t + 48) [C8 tb; C8 te]).

Definition tlsga_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma tlsga_icpt_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo ctx t B v : Z) (fsw : word),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AFSDESC ->
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v fsw ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  evtF bsegs RNG (tlsga_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom bsegs)).
Proof.
  intros until fsw. intros MI ST LO CEIL TP A0 INI TI TK T88 TSD CT
         (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48))
         C0 C1 T0 T1 BLO BHI V RIMG RSTK RCTX RT RB.
  subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).

  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ATLSGA_ICPT, ATLSGA in *.
  lit_in DTVP; lit_in DTV1.
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.

  zstep. call_sp tryinit_spec;
    first [exact MI| exact ST| exact INI| exact RIMG| unfold KHIGH; lia| solve_rng | idtac].
  rename PC into ST. clear POST.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI1 end.
  zstep. zstep.
  zstep. zstep.
  zstep.
  callp musl_tlsga_spec; first [exact TP| exact DESC| exact DTVP| exact DTV1| exact RIMG| idtac].
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].

  box RT; box RB.
  zstep. call_sp get_current_thread_spec;
    first [exact ST| exact MI1| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| exact RIMG| exact RCTX
          | atop_facts; lia| solve_rng | idtac].
  unbox RT; unbox RB. rename POST into ST.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 T0; lia|].
  zstep. zstep.
  zstep. zstep. zstep.

  zstep. call_sp dtls_fast_spec;
    first [exact MI2| exact ST| exact TP| reflexivity| exact G50| exact CF| exact GB0| exact VERB| exact DESC
          | exact G08| exact DV| exact BD| exact RIMG| exact RB| exact BLO| unfold AIMG_HI; lia| solve_rng | idtac].
  rename POST into ST.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp). subst tp. finish.
Qed.
End CANSEC2.

End F_tlsga.

Module F_tlsgaG.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tryinit.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind. Import F_tlsga.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC2. Context {rc : runConstT}.
Lemma musl_tlsga_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (fsw : word) (A : Z),
  tp = Z_to_bv 64 ATP ->
  ro_cells bsegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> rng RNG A 16 ->
  rw_cells bsegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw] ->
  rw_cells bsegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))] ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ATP + 0x800)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA) fc None m (seg_rom bsegs)).
Proof.
  intros until A. intros -> DESC RA DTVP DTV1 RIMG.
  pose proof (ro_cells_bound bsegs m A _ DESC) as AB. cbn [cells_size csize Nat.add] in AB.
  unfold ATP, ADTV, ATLSGA in *. lit_in DTVP; lit_in DTV1.
  do 9 zstep. finish.
Qed.

Definition dtls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma dtls_fast_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo B v A : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  rt_got m ->
  rw_cells bsegs m ACF137 [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd3680 [C8 (Z_to_bv 64 AVERB)] ->
  rw_cells bsegs m AVERB [C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> rng RNG A 16 ->
  rw_cells bsegs m 0xd43c0 [C8 (Z_to_bv 64 8)] ->
  rw_cells bsegs m ADTLSV [C8 (Z_to_bv 64 B)] ->
  rw_cells bsegs m (B + 24) [C8 (Z_to_bv 64 v)] ->
  iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG B 4096 ->
  evtF bsegs RNG (dtls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADTLSF) fc None m (seg_rom bsegs)).
Proof.
  intros until A. intros MI ST LO CEIL -> -> ABV G50 CF GB0 VERB DESC RA G08 DV BD BLO BHI V RIMG RSTK RB. destruct BLO as [BLO _].
  pose proof (ro_cells_bound bsegs m A _ DESC) as AB. cbn [cells_size csize Nat.add] in AB.
  unfold GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ADTLSF, ATP, AIMG_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 144%nat ST.
  do 14 zstep.
  zstep.
  zstep. zstep.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].
  zstep. zstep. zstep.
  zstep.
  zstep. zstep; lits.
  zstep.
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].
  zstep.
  zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 V BHI; lia|].
  zstep. if_cases K4; zify_cond K4; [| exfalso; clear - K4 BLO; lia].
  zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 BLO; lia|].
  zstep. zstep.
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; clear - K6; lia].
  zstep. zstep. zstep.
  zstep.
  zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7 V; lia|].
  do 16 zstep.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Definition tlsga_gcells (m : amem) (t B v : Z) (fsw : word) : Prop :=
     rw_cells bsegs m AREAL_TLSGA [C8 (Z_to_bv 64 ATLSGA)]
  /\ rw_cells bsegs m (ATP - 8) [C8 (Z_to_bv 64 ADTV); C8 fsw]
  /\ rw_cells bsegs m (ADTV + 8) [C8 (Z_to_bv 64 (ATP + 0x800))]
  /\ rt_got m
  /\ rw_cells bsegs m ACF137 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xd3680 [C8 (Z_to_bv 64 AVERB)]
  /\ rw_cells bsegs m AVERB [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xd43c0 [C8 (Z_to_bv 64 8)]
  /\ rw_cells bsegs m ADTLSV [C8 (Z_to_bv 64 B)]
  /\ rw_cells bsegs m (B + 24) [C8 (Z_to_bv 64 v)]
  /\ (exists tb te : word, rw_cells bsegs m (t + 48) [C8 tb; C8 te]).

Definition tlsga_icpt_gpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ATP + 0x800)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma tlsga_icpt_gspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo ctx t B v : Z) (fsw : word) (A : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells bsegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] -> rng RNG A 16 ->
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_gcells m t B v fsw ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  evtF bsegs RNG (tlsga_icpt_gpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom bsegs)).
Proof.
  intros until A. intros MI ST LO CEIL TP A0 ABV DESC RA INI TI TK T88 TSD CT
         (REAL & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48))
         C0 C1 T0 T1 BLO BHI V RIMG RSTK RCTX RT RB.
  subst a0.
  pose proof (ro_cells_bound bsegs m A _ DESC) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).

  unfold AIMG_HI, AREAL_TLSGA, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ATLSGA_ICPT, ATLSGA in *.
  lit_in DTVP; lit_in DTV1.
  carve_frame 32%nat ST.
  do 5 zstep.
  zstep.

  zstep. call_sp tryinit_spec;
    first [exact MI| exact ST| exact INI| exact RIMG| unfold KHIGH; lia| solve_rng | idtac].
  rename PC into ST. clear POST.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI1 end.
  zstep. zstep.
  zstep. zstep.
  zstep.
  callp musl_tlsga_gspec; first [exact TP| exact DESC| exact RA| exact DTVP| exact DTV1| exact RIMG| idtac].
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K; lia|].

  box RT; box RB.
  zstep. call_sp get_current_thread_spec;
    first [exact ST| exact MI1| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| exact RIMG| exact RCTX
          | atop_facts; lia| solve_rng | idtac].
  unbox RT; unbox RB. rename POST into ST.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 T0; lia|].
  zstep. zstep.
  zstep. zstep. zstep.

  zstep. call_sp dtls_fast_gspec;
    first [exact MI2| exact ST| exact TP| reflexivity| exact G50| exact CF| exact GB0| exact VERB| exact DESC| exact RA
          | exact G08| exact DV| exact BD| exact RIMG| exact RB| exact BLO| unfold AIMG_HI; lia| solve_rng | idtac].
  rename POST into ST.
  do 7 zstep.
  release_frame FR ST (bv_unsigned sp). subst tp. finish.
Qed.
End CANSEC2.

End F_tlsgaG.
End TwinB.
