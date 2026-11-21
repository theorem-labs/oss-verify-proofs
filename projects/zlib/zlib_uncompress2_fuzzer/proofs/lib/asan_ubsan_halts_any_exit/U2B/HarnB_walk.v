(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* [U14B-unc2] A2 2026-11-12: carried to unc2's combined image by tools/merge3_u2.sh: ours = my unc text (U1B, built at unc c31)
   moved by tools/t12.py (the measured unc -> unc2 combined image map), base = G's unc ASan twin moved the same
   way, theirs = G2's unc2 ASan twin moved by tools/g2b_u2.py.
   Any comment above or below that names the unc merge describes the unc text this one was carried from. *)
(* [U14B] A2 2026-11-12: the 1.4 uncompress chain.  This text is a 3-way merge (tools/merge3.sh run hw1): the view's
   text, the 1.3.1 ASan twin as base, and G's 1.4 ASan twin U1A/HarnA_walk moved to the combined image by tools/g2b.py (the harness code sits at a constant
   +0x88, the uncompress wrapper maps in five runs); all 7 conflicts take G's side. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AObj U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface U2BIfaceS U2cB_pre U2cB_epi U2BKit_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D n lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  (* 1.4: the uncompress2 wrapper's 64-byte frame lies below the harness's *)
  Definition H_STACK : Z := 128 + 64 + UC_STACK.
  Hypothesis LOS : lo <= SP - H_STACK.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ESPA : SPA = SP - 96 - SP mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Local Ltac acc_hint ::=
    lazymatch goal with
    | |- acc_in _ (Z_to_bv 64 (SPA + _)%Z, _) => solve_acc_with RSTK
    | |- acc_in _ (Z_to_bv 64 SPA, _) => solve_acc_with RSTK
    | |- _ => acc_hint_sh
    end.

  Definition HFRB : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma hspa_props : SP - 112 <= SPA <= SP - 96 /\ SPA mod 32 = 0 /\ (SP + -96) - (SP + -96) mod 2^5 = SPA.
  Proof. rewrite ESPA. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.
  Lemma h_pre : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SP -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m -> u2_img m -> rt_suar m ->
    evtF bsegs RNG (fun ms' => exists m' (jA : list byte),
        ms' = MS (mkR (Z_to_bv 64 0x8cba0) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 96) (Z_to_bv 64 892344)
                     (Z_to_bv 64 1) a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ASM1) fc None m' (seg_rom bsegs)
        /\ munch [(SP - 112, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SP + -72) HFRB /\ rw_cells bsegs m' SPA [CB 24 jA]
        /\ stk bsegs m' lo SPA /\ stk bsegs m' (SPA + 24) (SP + -72))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_HARNESS) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until m. intros ST MI GOT SHB (GSU & GZC) SUA. unfold rt_suar in SUA.
    unfold A_HARNESS, H_STACK, UC_STACK, AGOT_SUAR, ASUAR, ASM1, HFRB in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts.
    pose proof hspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 112, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. (* add sp,sp,-96 *)
    carve_frame 72%nat ST. carve_frame 24%nat ST.
    zstep. (* sd zero,0(sp) *)
    do 9 zstep. (* sd ra, s0 .. s7 *)
    zstep. (* add s0,sp,96 *)
    zstep. (* and sp,sp,-32 *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. rewrite ESPA'.
    release_frame FR1 ST (SP + -72).
    destruct (stk_split bsegs _ lo (SPA + 24) (SP + -72) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (SPA + 24) 24 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 24) with 24 in STL, FRA. replace (SPA + 24 - 24) with SPA in STL, FRA by lia.
    zrung [0x8cb9c].
    zs. (* jal __asan_stack_malloc_1 *)
    apply evtF_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [exact FRA|]. split; [exact STL| exact STG].
  Qed.

  Variables (F1 FLG : Z).
  Hypothesis F1128 : F1 mod 128 = 0.
  Hypothesis F1B : ablk F1 (F1 + 128).
  Hypothesis RF1 : rng RNG F1 128.
  Hypothesis RSF1 : rng RNG (Z.shiftr F1 3 + 2147450880) 16.

  Definition c1z16 : list cell := Eval cbv in repeat (C1 (Z_to_bv 8 0)) 16.
  Definition HFRA (j16 : list byte) : list cell := [CB 16 j16; C8 (Z_to_bv 64 F1)].
  Definition HFHD : list cell := [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 77974); C8 (Z_to_bv 64 576316)].
  Definition HFSH : list cell :=
    [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  (* 1.4: the wrapper's frame at SPA - 64 when it calls uncompress2_z: sp+0 not written, the sourceLen copy (n), the
     destLen copy (262144), then the saved s3 = n, s2 = F1, s1 = SPA, s0 = sp and ra = 0x8cca0 *)
  Definition WFR (j8 : list byte) : list cell :=
    [CB 8 j8; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 262144); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 F1); C8 (Z_to_bv 64 SPA); C8 sp;
     C8 (Z_to_bv 64 0x8cc68)].
  Definition h_hdrW : list (Z * Z) := [(SPA - 64, SPA + 24); (F1, F1 + 128); (Z.shiftr F1 3 + 2147450880, Z.shiftr F1 3 + 2147450896)].
  Definition hfr_shape : list cshape := [SHB 8; SH8; SHB 24; SH8; SHB 48].

  (* 1.4: from the stack_malloc_1 return (0x8cbd8) through the fake-frame header, the call of the uncompress2 wrapper
     (0x8cc9c -> 0x8d284), its prologue and both shadow checks, to uncompress2_z's entry (A_UNCOMPRESS2) with
     ra = 0x8d304, a1 = &(destLen copy) (sp + 16), a3 = &(sourceLen copy) (sp + 8), s0 / s1 = destLen / sourceLen
     (F1 + 32 / F1 + 64), s2 / s3 = their shadow bytes *)
  Lemma h_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (j0 j1 j2 : word) (junk jA : list byte),
    stk bsegs m lo SPA -> mem_inv bsegs m ->
    rt_got m -> rt_shbase m ->
    rw_cells bsegs m SPA [CB 24 jA] ->
    rw_cells bsegs m F1 [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (128 - 32)) junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad F1) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    0 <= n < 2^32 ->
    evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y14 y15 : word) (j16 j8 : list byte),
        ms' = MS (mkR (Z_to_bv 64 0x8d2cc) (Z_to_bv 64 (SPA + -64)) gp tp y5 y6 y7 (Z_to_bv 64 (F1 + 32)) (Z_to_bv 64 (F1 + 64))
                     (Z_to_bv 64 6341696) (Z_to_bv 64 (SPA + -48)) (Z_to_bv 64 D) (Z_to_bv 64 (SPA + -56)) y14 y15 x16 x17
                     (Z_to_bv 64 (Z.shiftr F1 3 + 2147450880 + 4)) (Z_to_bv 64 (Z.shiftr F1 3 + 2147450880 + 8)) (Z_to_bv 64 D)
                     (Z_to_bv 64 (Z.shiftr F1 3 + 2147450880)) (Z_to_bv 64 F1) (Z_to_bv 64 (-8))
                     s8 s9 s10 s11 x28 x29 x30 x31)
                 FR (Z_to_bv 64 A_UNCOMPRESS2) fc None m' (seg_rom bsegs)
        /\ munch h_hdrW m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (SPA + -64)
        /\ rw_cells bsegs m' (SPA + -64) (WFR j8)
        /\ rw_cells bsegs m' SPA (HFRA j16) /\ rw_cells bsegs m' F1 HFHD /\ rw_cells bsegs m' (F1 + 120) [C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr F1 3 + 2147450880) HFSH
        /\ rw_cells bsegs m' (F1 + 32) [C8 (Z_to_bv 64 262144)] /\ rw_cells bsegs m' (F1 + 64) [C8 (Z_to_bv 64 n)])
      (MS (mkR (Z_to_bv 64 0x8cba0) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F1) x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8cba0) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until jA. intros ST MI GOT SHB FRA FFR FSH N0.
    unfold H_STACK, UC_STACK, h_hdrW, HFRA, HFHD, HFSH, WFR, A_UNCOMPRESS2 in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof hspa_props as (SPAB & SPA32 & ESPA').
    pose proof (ablk_lin _ _ F1B) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    assert (F8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    rw_split FFR 3%nat FHD FREST. rw_split FREST 1%nat FBLOB FFLG.
    rewrite shadE in FSH.
    eapply (rw_cells_recast bsegs _ _ _ c1z16) in FSH; [| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
    unfold c1z16 in FSH.
    assert (BSF : 2147450880 <= Z.shiftr F1 3 + 2147450880 /\ Z.shiftr F1 3 + 2147450880 + 16 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    band_ind F1B bU.
    pose (W := [(SPA - 64, SPA + 24); (F1, F1 + 128); (Z.shiftr F1 3 + 2147450880, Z.shiftr F1 3 + 2147450896)]).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM. subst W.
    apply (rw_cells_chop bsegs _ _ _ junk hfr_shape) in FBLOB; [| vm_compute; reflexivity].
    cbn [chop chop1 shape_size hfr_shape] in FBLOB. chop_names FBLOB.
    rw_split FBLOB 1%nat FPAD FR1'. rw_split FR1' 1%nat FDL FR2'. rw_split FR2' 1%nat FMID FR3'. rw_split FR3' 1%nat FSL FTAIL.
    zrung [0x8cc64].
    zs. (* jal uncompress2 (0x8d284), ra = 0x8cca0 *)
    zstep. (* 1.4: add sp,sp,-64 *)
    carve_frame 64%nat ST.
    (* the destLen shadow byte: s2 = (F1 + 32) >> 3 + shadow base = SHF + 4 *)
    assert (ESD : Z.shiftr (F1 + 32) 3 + 2147450880 = Z.shiftr F1 3 + 2147450880 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (ESS : Z.shiftr (F1 + 64) 3 + 2147450880 = Z.shiftr F1 3 + 2147450880 + 8)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    zrung [0x8d288].
    try rewrite ESD.
    zrung [0x8d2b0].
    try rewrite ESS.
    zrung [0x8d2c8].
    zs. (* jal uncompress2_z (0x8cdd4), ra = 0x8d304 *)
    apply evtF_done. do 8 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|].
    split; [exact FRA|]. split; [exact FHD|]. split; [exact FFLG|]. split; [exact FSH|]. split; [exact FDL| exact FSL].
  Qed.

  Hypothesis RFRM : rng RNG (SPA - 64) 88.
  Hypothesis GB : ablk FLG (FLG + 1).
  Hypothesis GF : FLG + 1 <= F1 \/ F1 + 128 <= FLG.
  Hypothesis RG : rng RNG FLG 1.
  Notation SHF := (Z.shiftr F1 3 + 2147450880).

  (* 1.4: from uncompress2_z's return into the wrapper (0x8d304): the sourceLen shadow check, *sourceLen = its copy,
     the destLen shadow check, *destLen = its copy, the 64-byte frame's restore and ret to 0x8cca0, then the harness
     epilogue as before *)
  Lemma h_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 v4 x28 x29 x30 x31 slv dlv dv sv : word) m (j16 j8 : list byte),
    stk bsegs m lo (SPA + -64) -> stk bsegs m (SPA + 24) (SP + -72) -> mem_inv bsegs m ->
    rw_cells bsegs m (SPA + -64) [CB 8 j8; C8 slv; C8 dlv; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 F1); C8 (Z_to_bv 64 SPA); C8 sp;
                                  C8 (Z_to_bv 64 0x8cc68)] ->
    rw_cells bsegs m SPA (HFRA j16) ->
    rw_cells bsegs m (SP + -72) HFRB ->
    rw_cells bsegs m F1 HFHD ->
    rw_cells bsegs m (F1 + 32) [C8 dv] ->
    rw_cells bsegs m (F1 + 64) [C8 sv] ->
    rw_cells bsegs m (F1 + 120) [C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m SHF HFSH ->
    evtF bsegs RNG (fun ms' => exists (mp m' : amem) (q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
        ms' = MS (mkR ra sp gp tp q5 q6 q7 s0 s1 (Z_to_bv 64 0) q11 q12 q13 q14 q15 q16 q17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(SHF, SHF + 16); (F1, F1 + 72)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 (SPA + -64)) gp tp x5 x6 x7 (Z_to_bv 64 (F1 + 32)) (Z_to_bv 64 (F1 + 64)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 8)) v4 (Z_to_bv 64 SHF) (Z_to_bv 64 F1) (Z_to_bv 64 (-8))
               s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8d2cc) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until j8. intros STL STG MI WF FRA FRB FH FDL FSL FFL FLC FSH.
    unfold HFRA, HFRB, HFHD, HFSH, H_STACK, UC_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ F1B) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
    pose proof hspa_props as (SPAB & SPA32 & _).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    assert (F8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (BSF : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    band_ind F1B bU. band_ind GB bG.
    destruct (sepI FLG 1 F1 128 GF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (cG & CG0 & CG1 & CG2). clear GF.
    pose proof (munch_refl [(SHF, SHF + 16); (F1, F1 + 72)] m) as MU1. pose proof (wmono_refl bsegs m) as WM1.
    zrung [0x8ccc4].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bxu (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (bxu T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (bxu T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zs. (* ld a0,120(s2) *)
    zs. (* sb zero,0(a0) *)
    zs. zs. zs. (* j; li a0,0; add sp,s0,-96 *)
    do 9 zs. zs. zs.
    (* the frames: the wrapper's (SPA - 64), the harness's aligned area (SPA), its register save (SP - 72) *)
    lazymatch goal with H : rw_cells bsegs _ (SPA + -64) _ |- _ => rename H into WF2 end.
    lazymatch goal with H : rw_cells bsegs _ SPA _ |- _ => rename H into FRA2 end.
    lazymatch goal with H : rw_cells bsegs _ (SP + -72) _ |- _ => rename H into FRB2 end.
    lazymatch goal with H : stk bsegs _ lo (SPA + -64) |- _ => rename H into STL2 end.
    lazymatch goal with H : stk bsegs _ (SPA + 24) (SP + -72) |- _ => rename H into STG2 end.
    eapply stk_release in WF2; [| exact STL2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in WF2.
    replace (SPA + -64 + Z.of_nat 64) with SPA in WF2 by (change (Z.of_nat 64) with 64; lia).
    eapply stk_release in FRA2; [| exact WF2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 24) (SP + -72) FRA2 STG2 ltac:(lia)) as ST2 end.
    release_frame FRB2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold bxu in MU1, WM1, MIp.
    replace (Z.shiftr F1 3 + 2147450896) with (SHF + 16) by lia.
    eexists _, _. do 14 eexists. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MIp|].
    split; [exact MU2|]. split; [exact WM2|]. split; [eassumption|]. split; [exact ST2| eassumption].
  Qed.
End S.
End CANSEC1.
