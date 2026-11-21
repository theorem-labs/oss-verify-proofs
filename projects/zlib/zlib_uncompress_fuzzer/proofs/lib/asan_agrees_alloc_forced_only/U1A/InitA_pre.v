(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (Fu Zs lo : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - INIT_STACK.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ZSE : Zs = Fu + 32.
  Hypothesis FU256 : Fu mod 256 = 0.
  Hypothesis FUB : ablk Fu (Fu + 256).
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RZ : rng RNG Zs 112.
  Hypothesis RSZ : rng RNG (Z.shiftr Zs 3 + 2147450880) 14.

  Definition init_W : list (Z * Z) := [(SP - 112, SP); (Zs, Zs + 112)].

  (* 1.4: inflateInit_ (0x8dab0) is a stub (mv a3,a2; mv a2,a1; li a1,15; j inflateInit2_). inflateInit2_ (0x8d6c4)
     saves ra and s0 .. s11 at sp+8 .. sp+104 (sp+0 is not written), keeps strm in s3 and windowBits in s11, forms
     zcalloc / zcfree pc-relative, and calls zalloc (ra = 0x8d800); zcalloc tail-jumps to malloc. *)
  Lemma init_pre : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m
      (next_in avail_in total_in next_out avail_out total_out msg state opaque data_type adler reserved p1 p2 p3 : word),
    stk asegs m lo SP -> mem_inv asegs m ->
    rt_got m -> rt_shbase m -> u2_img m ->
    rw_cells asegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg state
                                    (Z_to_bv 64 0) (Z_to_bv 64 0) opaque data_type adler reserved p1 p2 p3) ->
    shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
    shadow_bytes m 2147468524 2147468525 (fun _ => 4) ->
    evtF asegs RNG (fun ms' => exists m' (a4' a5' a6' a7' : word) (j8 : list byte),
        ms' = MS (mkR (Z_to_bv 64 0x8d850) (Z_to_bv 64 (SP + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Zs + 80)) (Z_to_bv 64 (Zs + 72))
                     (Z_to_bv 64 7176) (Z_to_bv 64 1) (Z_to_bv 64 7176) (Z_to_bv 64 605476) a4' a5' a6' a7'
                     s2 (Z_to_bv 64 Zs) (Z_to_bv 64 (Zs + 64)) s5 (Z_to_bv 64 2147450880)
                     (Z_to_bv 64 (Z.shiftr (Zs + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (Zs + 80) 3 + 2147450880)) s9
                     (Z_to_bv 64 (Z.shiftr (Zs + 64) 3 + 2147450880)) (Z_to_bv 64 15) t3 t4 t5 t6)
                 FR (Z_to_bv 64 AMALLOC_SYM) fc None m' (seg_rom asegs)
        /\ munch init_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -112)
        /\ rw_cells asegs m' (SP + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells asegs m' Zs (strm_cells next_in avail_in total_in next_out avail_out total_out (Z_to_bv 64 0) state
                                            (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) data_type adler reserved p1 p2 p3))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Zs) (Z_to_bv 64 AVERSION) (Z_to_bv 64 112) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_INFLATEINIT) fc None m (seg_rom asegs)).
  Proof using All.
    intros until p3. intros ST MI GOT SHB (GSU & _) STRM SHZ SHV.
    unfold init_W, A_INFLATEINIT, AVERSION, INIT_STACK, A_ZCALLOC, A_ZCFREE, AMALLOC_SYM, strm_cells in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose (W := [(SP - 112, SP); (Zs, Zs + 112)]).
    assert (DJZ : disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))).
    { subst W. cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB. Z.div_mod_to_equations. lia. }
    assert (DJV : disjoint_from W 2147468524 (2147468525 - 2147468524)).
    { subst W. cbn [disjoint_from]. unfold ablk, AIMG_HI, KLS in FUB. lia. }
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM. subst W.
    zs. zs. zs. zs. (* the inflateInit_ stub: mv a3,a2; mv a2,a1; li a1,15; j inflateInit2_ *)
    zstep. (* addi sp,sp,-112 *)
    carve_frame 112%nat ST.
    zrunb [0x8d84c].
    zs. (* jalr a3: zcalloc *)
    zs. zs. zs. zs. (* zcalloc: mul; slli; srli; j malloc *)
    apply evtF_done. do 6 eexists. split; [reflexivity|].
    replace (SP - 112) with (SP + -112) by lia.
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR0| exact STRM].
  Qed.
End S.
End CANSEC1.
