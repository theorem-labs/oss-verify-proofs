(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2ABlob.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import StrFun RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (Zs lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - 672.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ESPA : SPA = (SP - 640) - (SP - 640) mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition inf_SAVED : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma inf_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo SP -> mem_inv asegs m ->
    rt_got m -> rt_shbase m -> u2_img m -> rt_suar m ->
    evtF asegs RNG (fun ms' => exists m' (jA : list byte),
        (* the 1.4 prologue leaves SHB in s5 and 0 in s6 (1.3.1: 0 in s5, SHB in s9); read off probe
           ZProbe/PgPro1 (reg_val x1..x31 at the __asan_stack_malloc call) *)
        ms' = MS (mkR (Z_to_bv 64 0x8db84) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 64) (Z_to_bv 64 886328) (Z_to_bv 64 1)
                     a3 a4 a5 a6 a7 (Z_to_bv 64 Zs) s3 s4 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASM0) fc None m' (seg_rom asegs)
        /\ munch [(SP - 672, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SP + -104) inf_SAVED
        /\ rw_cells asegs m' SPA (chop (repeat SH8 67) jA)
        /\ stk asegs m' lo SPA /\ stk asegs m' (SPA + 536) (SP + -104))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_INFLATE) fc None m (seg_rom asegs)).
  Proof using All.
    intros until m. intros ST MI GOT SHB (GSU & GZC) SUA. unfold rt_suar in SUA.
    unfold A_INFLATE, AGOT_SUAR, ASUAR, AGOT_ZCALLOC, ASM0, inf_SAVED in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts.
    assert (SPAB : SP - 656 <= SPA <= SP - 640 /\ SPA mod 32 = 0) by (rewrite ESPA; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 672, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.
    carve_frame 104%nat ST. carve_frame 536%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia.
    replace ((SP + -640) - (SP + -640) mod 2^5) with SPA by (rewrite ESPA; change (2^5) with 32; replace (SP + -640) with (SP - 640) by lia; reflexivity).
    release_frame FR1 ST (SP + -104).
    destruct (stk_split asegs _ lo (SPA + 536) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 536) 536 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 536) with 536 in STL, FRA. replace (SPA + 536 - 536) with SPA in STL, FRA by lia.
    apply (rw_cells_chop asegs _ SPA 536 jA (repeat SH8 67)) in FRA; [| reflexivity].
    pose proof FRA as FRA0.
    cbn [chop chop1 shape_size repeat] in FRA. chop_names FRA.
    zrunb [0x48778].
    apply evtF_done. eexists _, jA. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact FR0|].
    split; [exact FRA0| split; [exact STL| exact STG]].
  Qed.
End S.
End CANSEC1.
