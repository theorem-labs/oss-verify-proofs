(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg AKit RtCells ShadowTac F_syscalls StdioFiles Stdio_kit F_tryinit F_memcpy AIos_iface AExitU_wr
     AIcptU_hmap AIcptU_fflush AIcptU_mem0 AIcptU_defs AIcptU_wdefs.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.

Theorem wcrtomb0_proof : forall T, wcrtomb0_stmt (icptW T) (icptW_rng T) XSLO XSHI.
Proof.
  intros T. unfold wcrtomb0_stmt.
  intros until ST. intros STK PB PLO PHI SSP IC MI -> -> -> HST -> SLOK SHIK LO GLO ATL AL SP47 RSTK RP RI RX.
  pose proof (munch_refl [(bv_unsigned sp - 4096, bv_unsigned sp); (P, P + 1)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct STK as [? _]; assumption).
  pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR. unfold GLOBALS_TOP in GLO. unfold XSLO, XSHI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof IC as IC0. destruct IC as [[RT TAB] WCRC]. destruct RT as (INI & RFF & RFW & RWC & RMEM & RIC).
  destruct WCRC as (G1 & SZ & G2 & SB & G3 & MB & XS). unfold MBST_SH in *.
  destruct RX as (_ & RMB & RXS). unfold MBST_SH in RMB.
  unfold WCRTOMB_STUB.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 2176%nat STK.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB bsegs m _ [] 2176%nat junk []
           [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1; 2072; 8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 10 zstep.                             (* [comment removed for export] *)
  do 5 zstep. zstep.                       (* [comment removed for export] *)
  call_sp tryinit_spec. all: iprem.
  zstep. if_false.                         (* [comment removed for export] *)
  do 2 zstep.                              (* [comment removed for export] *)
  destruct HST as [-> | ->].
  (* [comment removed for export] *)
  - zstep. if_false.                       (* [comment removed for export] *)
    do 3 zstep. rewrite (zx32_lit 8) by lia.   (* [comment removed for export] *)
    steps_to 0x71e88%Z.                    (* [comment removed for export] *)
    zstep. bsplit.                         (* [comment removed for export] *)
    steps_to 0x71f28%Z.                    (* [comment removed for export] *)
    zstep.                                 (* [comment removed for export] *)
    run_to 0x71f2c%Z.
    steps_to 0x71f44%Z.                    (* [comment removed for export] *)
    zstep. if_cases KW; zify_cond KW.      (* [comment removed for export] *)
    { exfalso. rewrite zb_lxor_ones in KW by lia. lia. }
    run_to 0x71f78%Z.                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (SAR : 0 <= 2147450880 + Z.shiftr P 3 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    replace (Z.land (Z.land (2147450880 + Z.shiftr P 3) 18446744073709551615) 18446744073709551608)
      with (2147450880 + Z.shiftr P 3 - (2147450880 + Z.shiftr P 3) mod 8).
    2:{ change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite (Z.mod_small _ (2^64)) by exact SAR.
        change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia. reflexivity. }
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (XSc : shadow_bytes mc (shad ATOP) XSH_HI (fun _ => 0))
        by (eapply shadow_bytes_munch; [exact XS | exact MU |]; rewrite shad_div; unfold AsanEmbed.ASHOFF, XSH_HI; cbn [disjoint_from];
            Z.div_mod_to_equations; lia);
      pose proof (ov_read8_zero bsegs mc _ _ _ (2147450880 + Z.shiftr P 3 - (2147450880 + Z.shiftr P 3) mod 8) XSc
                    ltac:(rewrite shad_div; unfold AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia)
                    ltac:(unfold XSH_HI; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia)
                    ltac:(intros; reflexivity)) as PRD
    end.
    assert (RPRD : rng RNG (2147450880 + Z.shiftr P 3 - (2147450880 + Z.shiftr P 3) mod 8) 8).
    { eapply rng_sub'; [exact RXS|]. rewrite shad_div. unfold AsanEmbed.ASHOFF, XSH_HI. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      Z.div_mod_to_equations. lia. }
    do 2 zstep.
    run_to 0x71fa4%Z.                      (* [comment removed for export] *)
    zstep.
    match goal with FRx : rw_cells _ ?mc (bv_unsigned sp + -2176) (?c0 :: ?rest) |- _ =>
      pose proof (proj1 (proj1 (proj1 (rw_cells_app bsegs mc (bv_unsigned sp + -2176) [c0] rest) FRx))) as [_ SRCB]; cbn [cells_bytes cbytes app] in SRCB
    end.
    assert (EP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
    assert (E1 : bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity.
    assert (EL : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2176)) = bv_unsigned sp + -2176) by (apply unsigned_lit; lia).
    call_sp (memcpy_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [Z_to_bv 8 0] jb).
    1: (rewrite ?EL; exact SRCB).
    1: (rewrite E1; reflexivity).
    1: (rewrite EP, E1; exact PB).
    1: (rewrite EP, E1; lia).
    1: assumption.
    rewrite EP, E1 in *.
    zstep.                                 (* [comment removed for export] *)
    do 12 zstep. zstep.                    (* [comment removed for export] *)
    release_frame FR PC (bv_unsigned sp).
    apply evtF_done. unfold wcr_post.
    do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PC|].
    assert (HW : Forall exit_wr_ok [(bv_unsigned sp - 4096, bv_unsigned sp); (P, P + 1)])
      by (unfold exit_wr_ok; constructor; [left; cbn [fst snd]; lia | constructor; [left; cbn [fst snd]; lia | constructor]]).
    split. { unfold ssp_cells, got_ssp, ssp_guard in *. destruct SSP as [S1 S2].
             split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    split; [exact (icptW_frame_exit T _ _ _ IC0 MU WM HW)|].
    eapply rw_cells_recast; [exact PC0 | repeat constructor | reflexivity | reflexivity].
  - zstep. if_false.                       (* [comment removed for export] *)
    do 3 zstep. rewrite (zx32_lit 8) by lia.   (* [comment removed for export] *)
    steps_to 0x71e88%Z.                    (* [comment removed for export] *)
    zstep. bsplit.                         (* [comment removed for export] *)
    steps_to 0x71f28%Z.                    (* [comment removed for export] *)
    zstep.                                 (* [comment removed for export] *)
    run_to 0x71f2c%Z.
    steps_to 0x71f44%Z.                    (* [comment removed for export] *)
    zstep. if_cases KW; zify_cond KW.      (* [comment removed for export] *)
    { exfalso. rewrite zb_lxor_ones in KW by lia. lia. }
    run_to 0x71f78%Z.                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (SAR : 0 <= 2147450880 + Z.shiftr P 3 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    replace (Z.land (Z.land (2147450880 + Z.shiftr P 3) 18446744073709551615) 18446744073709551608)
      with (2147450880 + Z.shiftr P 3 - (2147450880 + Z.shiftr P 3) mod 8).
    2:{ change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite (Z.mod_small _ (2^64)) by exact SAR.
        change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia. reflexivity. }
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (XSc : shadow_bytes mc (shad ATOP) XSH_HI (fun _ => 0))
        by (eapply shadow_bytes_munch; [exact XS | exact MU |]; rewrite shad_div; unfold AsanEmbed.ASHOFF, XSH_HI; cbn [disjoint_from];
            Z.div_mod_to_equations; lia);
      pose proof (ov_read8_zero bsegs mc _ _ _ (2147450880 + Z.shiftr P 3 - (2147450880 + Z.shiftr P 3) mod 8) XSc
                    ltac:(rewrite shad_div; unfold AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia)
                    ltac:(unfold XSH_HI; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia)
                    ltac:(intros; reflexivity)) as PRD
    end.
    assert (RPRD : rng RNG (2147450880 + Z.shiftr P 3 - (2147450880 + Z.shiftr P 3) mod 8) 8).
    { eapply rng_sub'; [exact RXS|]. rewrite shad_div. unfold AsanEmbed.ASHOFF, XSH_HI. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      Z.div_mod_to_equations. lia. }
    do 2 zstep.
    run_to 0x71fa4%Z.                      (* [comment removed for export] *)
    zstep.
    match goal with FRx : rw_cells _ ?mc (bv_unsigned sp + -2176) (?c0 :: ?rest) |- _ =>
      pose proof (proj1 (proj1 (proj1 (rw_cells_app bsegs mc (bv_unsigned sp + -2176) [c0] rest) FRx))) as [_ SRCB]; cbn [cells_bytes cbytes app] in SRCB
    end.
    assert (EP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
    assert (E1 : bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity.
    assert (EL : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2176)) = bv_unsigned sp + -2176) by (apply unsigned_lit; lia).
    call_sp (memcpy_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [Z_to_bv 8 0] jb).
    1: (rewrite ?EL; exact SRCB).
    1: (rewrite E1; reflexivity).
    1: (rewrite EP, E1; exact PB).
    1: (rewrite EP, E1; lia).
    1: assumption.
    rewrite EP, E1 in *.
    zstep.                                 (* [comment removed for export] *)
    do 12 zstep. zstep.                    (* [comment removed for export] *)
    release_frame FR PC (bv_unsigned sp).
    apply evtF_done. unfold wcr_post.
    do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PC|].
    assert (HW : Forall exit_wr_ok [(bv_unsigned sp - 4096, bv_unsigned sp); (P, P + 1)])
      by (unfold exit_wr_ok; constructor; [left; cbn [fst snd]; lia | constructor; [left; cbn [fst snd]; lia | constructor]]).
    split. { unfold ssp_cells, got_ssp, ssp_guard in *. destruct SSP as [S1 S2].
             split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    split; [exact (icptW_frame_exit T _ _ _ IC0 MU WM HW)|].
    eapply rw_cells_recast; [exact PC0 | repeat constructor | reflexivity | reflexivity].
Qed.
End CANSEC1.
