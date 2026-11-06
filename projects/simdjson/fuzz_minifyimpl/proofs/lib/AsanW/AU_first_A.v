(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
Section CANSEC1. Context {rc : runConstT}.
Definition ARSI : Z := 0xb0e58.          (* [comment removed for export] *)
Definition AMEMSET_FN : Z := 0x80fe4.    (* [comment removed for export] *)

Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - 8192.
  Hypothesis LOC : ATOP <= lo.
  Hypothesis SPT : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.

  (* [comment removed for export] *)
  Definition RSIFR (j : list byte) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma rsi_a1 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo SP -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    evtF asegs RNG (fun ms' => exists m' j,
        ms' = MS (mkR (Z_to_bv 64 0xb0e94) (Z_to_bv 64 (SP + -64)) gp tp t0 t1 t2 (Z_to_bv 64 AVEC) s1 (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 AMEMSET_FN) fc None m' (seg_rom asegs)
        /\ munch [(SP - 64, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (SP + -64) (RSIFR j) /\ stk asegs m' lo (SP + -64))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AVEC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 ARSI) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI GOT SHB. unfold ARSI, AMEMSET_FN, AVEC in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. carve_frame 64%nat ST.
    steps_to 0x80fe4.
    apply evtF_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact FR0| exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition shz (X : Z) (m : amem) : Prop := rw_cells asegs m (shad X) [C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Definition simdjson_statics (m : amem) : Prop :=
       rw_cells asegs m 0x6a2b40 guard1 /\ rw_cells asegs m 0x6a2b60 [C8 (Z_to_bv 64 0x6a2ba0); C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x6a2b80 guard1
    /\ rw_cells asegs m 0x6a2ba0 [C8 (Z_to_bv 64 AFALLBACK)]
    /\ rw_cells asegs m AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT); C8 (Z_to_bv 64 0x29520); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0x29ae0); C8 (Z_to_bv 64 0x1f); C4 w0]
    /\ rw_cells asegs m 0x6a2c20 guard1.
  Definition shz7 (m : amem) : Prop :=
    shz 0x6a2ba0 m /\ shz 0x6a2bc0 m /\ shz 0x161360 m /\ shz 0x6a2be8 m /\ shz 0x6a2a48 m /\ shz 0x6a2a50 m /\ shz 0x6a2a40 m.
  (* [comment removed for export] *)
  Definition RSI_IMGW : list (Z * Z) :=
    [(0x6a2b40, 0x6a2b42); (0x6a2b60, 0x6a2b70); (0x6a2b80, 0x6a2b82); (0x6a2ba0, 0x6a2ba8); (0x6a2bc0, 0x6a2bec); (0x6a2c20, 0x6a2c22)].
  (* [comment removed for export] *)
  Definition EBFR (j : list byte) : list cell :=
    [CB 32 j; C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 2148320628); C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 0x6a2ba0);
     C8 (Z_to_bv 64 0x6a2ba8); C8 (Z_to_bv 64 0x6a2ba0); C8 (Z_to_bv 64 AVEC); C8 (Z_to_bv 64 0xb0ee0)].

  (* [comment removed for export] *)
  Lemma rsi_a2 : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk asegs m lo (SP + -64) -> mem_inv asegs m -> rt_got m -> rt_shbase m ->
    rw_cells asegs m AVEC [C8 w0; C8 w0; C8 w0] ->
    rw_cells asegs m 0x6a2b40 guard0 -> rw_cells asegs m 0x6a2b60 [C8 w0; C8 w0] -> rw_cells asegs m 0x6a2b80 guard0 ->
    rw_cells asegs m 0x6a2ba0 [C8 w0] ->
    rw_cells asegs m AFALLBACK [C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C4 w0] -> rw_cells asegs m 0x6a2c20 guard0 ->
    rw_cells asegs m AVTAB_SRS [C8 (Z_to_bv 64 ASRS_FN)] ->
    shz7 m ->
    evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) j,
        ms' = MS (mkR (Z_to_bv 64 0xb4304) (Z_to_bv 64 (SP + -176)) gp tp y5 y6 y7 (Z_to_bv 64 1) (Z_to_bv 64 0x6a2ba0) (Z_to_bv 64 8) y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 AVEC) (Z_to_bv 64 0) (Z_to_bv 64 2148320585) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 FR (Z_to_bv 64 0x15fb3c) fc None m' (seg_rom asegs)
        /\ munch ((SP - 176, SP - 64) :: RSI_IMGW) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (SP + -176)
        /\ rw_cells asegs m' (SP + -176) [C8 (Z_to_bv 64 (AVEC + 8)); C8 (Z_to_bv 64 0xb1088)]
        /\ rw_cells asegs m' (SP + -160) (EBFR j)
        /\ rw_cells asegs m' AVEC [C8 w0; C8 w0; C8 w0] /\ simdjson_statics m'
        /\ rw_cells asegs m' AVTAB_SRS [C8 (Z_to_bv 64 ASRS_FN)] /\ shz7 m')
      (MS (mkR x1 (Z_to_bv 64 (SP + -64)) gp tp t0 t1 t2 (Z_to_bv 64 AVEC) s1 (Z_to_bv 64 AVEC) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0xb0e94) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI GOT SHB VEC G1 IL G2 ARR SGL G3 VT (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    unfold shz7, simdjson_statics, EBFR, RSI_IMGW, shz, AVEC, AFALLBACK, AFALLBACK_VT, AVTAB_SRS, ASRS_FN, guard0, guard1, w0 in *.
    change (shad 0x6a2ba0) with 2148320628 in *. change (shad 0x6a2bc0) with 2148320632 in *. change (shad 0x161360) with 2147631724 in *.
    change (shad 0x6a2be8) with 2148320637 in *. change (shad 0x6a2a48) with 2148320585 in *. change (shad 0x6a2a50) with 2148320586 in *. change (shad 0x6a2a40) with 2148320584 in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SP - 176, SP - 64); (0x6a2b40, 0x6a2b42); (0x6a2b60, 0x6a2b70); (0x6a2b80, 0x6a2b82); (0x6a2ba0, 0x6a2ba8); (0x6a2bc0, 0x6a2bec); (0x6a2c20, 0x6a2c22)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    zstep. (* [comment removed for export] *)
    zstep. carve_frame 16%nat ST.
    steps_to 0xb549c. release_frame FR0 ST (SP + -64).          (* [comment removed for export] *)
    steps_to 0xb5194. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xde940. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xde9c4. release_frame FR1 ST (SP + -80).
    steps_to 0xb521c. release_frame FR0 ST (SP + -64).
    steps_to 0xb5224. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xb5260. release_frame FR0 ST (SP + -64).
    steps_to 0xb5134. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0xde448. zstep. carve_frame 16%nat ST.
    steps_to 0xde478. release_frame FR1 ST (SP + -80).
    steps_to 0xb5180. release_frame FR0 ST (SP + -64).
    steps_to 0xb0f7c. zstep. carve_frame 96%nat ST.             (* [comment removed for export] *)
    steps_to 0xb42e4. zstep. carve_frame 16%nat ST.             (* [comment removed for export] *)
    steps_to 0x15fb3c.
    apply evtF_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    split; [exact FR1|]. split; [exact FR0|]. split; [exact VEC|].
    split. { split; [exact G1|]. split; [exact IL|]. split; [exact G2|]. split; [exact ARR|]. split; [exact SGL| exact G3]. }
    split; [exact VT|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6| exact S7].
  Qed.
End S.
End CANSEC1.
