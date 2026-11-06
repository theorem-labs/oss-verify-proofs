(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Theorem Labs, 2026-10-28: copied from proofs/leptonica/fhmtgen_fuzzer/lib/K5/B10/I_strcmpw.v at origin/ossv/recipes c8557374ad2e, with its module paths changed to fuzz_preset's. Its address literals are still fhmtgen_fuzzer.asan-ubsan's. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.B10 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_strcmp_spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ISTRCMP_DEPTH := 2272%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition icells_scmp (m : mem) : Prop :=
  ro_cells asegs m 0xa2840 [C8 (Z_to_bv 64 0x13d228)]           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2850 [C8 (Z_to_bv 64 0xab6f8)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xab6f8 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac3d8 [C1 (Z_to_bv 8 1)]                (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13d31d [C1 (Z_to_bv 8 0)]               (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13d322 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)

Lemma icells_scmp_agree : forall m m', icells_scmp m -> agree_on (fun x => 0 <= x < 0x1d9d80) m m' -> wmono asegs m m' -> icells_scmp m'.
Proof.
  intros m m' (C1 & C2 & C3 & C4 & C5 & C6) AG WM.
  split; [| split; [| split; [| split; [| split]]]].
  - apply (ro_cells_agree asegs m m' _ _ C1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C4); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C5). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C6). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

Lemma m2s_cells_agree : forall m m', m2s_cells m -> agree_on (fun x => 0 <= x < 0x1d9d80) m m' -> wmono asegs m m' -> m2s_cells m'.
Proof.
  intros m m' (C1 & C2 & C3) AG WM.
  split; [| split].
  - apply (rw_cells_agree asegs m m' _ _ C1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C2); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iscmp_loop : forall (r k : nat) (p1 p2 : Z) (b1 b2 : list byte)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  (strcmp_idx_aux b1 b2 = k + r)%nat -> Z.of_nat (length b1) < 2^40 -> Z.of_nat (length b2) < 2^40 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> strcmp_ok b1 b2 -> sc_pre b1 b2 k -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (x1 x2 : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) (Z_to_bv 64 (p2 + strcmp_idx b1 b2)) a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 p1) s3 (Z_to_bv 64 (strcmp_idx b1 b2 + 1)) s5 s6 s7 s8 (Z_to_bv 64 x1) (Z_to_bv 64 x2) s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4343c) fc None m (seg_rom asegs)
      /\ 0 <= x1 < 256 /\ 0 <= x2 < 256 /\ cmpx x1 x2 = strcmp_res b1 b2)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p1) s3 (Z_to_bv 64 (Z.of_nat k)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43420) fc None m (seg_rom asegs)).
Proof.
  induction r as [|r IH]; intros k p1 p2 b1 b2 ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HR L1 L2 B1 B2 OK HP MI;
  ( pose proof OK as (OK1 & OK2); unfold strcmp_sz, strcmp_idx in OK1, OK2;
    destruct (nth_error b1 k) as [x|] eqn:E1; [| apply nth_error_None in E1; lia];
    destruct (nth_error b2 k) as [y|] eqn:E2; [| apply nth_error_None in E2; lia];
    pose proof (bytes_at_nth1 asegs m p1 b1 k x B1 E1) as BX; pose proof (ro_C1_of_bytes m _ _ BX) as CX;
    pose proof (bytes_at_nth1 asegs m p2 b2 k y B2 E2) as BY; pose proof (ro_C1_of_bytes m _ _ BY) as CY;
    pose proof (bytes_at_bound _ _ _ _ B1) as BB1; pose proof (bytes_at_bound _ _ _ _ B2) as BB2;
    pose proof (bv_unsigned_in_range 8 x) as XR; pose proof (bv_unsigned_in_range 8 y) as YR; unfold bv_modulus in XR, YR;
    change (2 ^ Z.of_N 8) with 256 in XR, YR;
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia);
    assert (EUk1 : bv_unsigned (Z_to_bv 64 (Z.of_nat k + 1)) = Z.of_nat k + 1) by (apply unsigned_lit; lia);
    assert (EU1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia);
    assert (EU2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia);
    assert (EUx : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia);
    assert (EUy : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia);
    lstep; set (q1 := p1 + Z.of_nat k) in *; lstep;
    lstep; set (q2 := p2 + Z.of_nat k) in *; lstep;
    cbv beta in *;
    lstep; lstep; if_cases K; zify_cond K; rewrite ?EUx, ?EUy in K; change (bv_unsigned z64) with 0 in K).
  - (* [comment removed for export] *)
    destruct (res_break b1 b2 k x y HP E1 E2 (or_intror K)) as (RI & RR).
    apply evt_done. exists (bv_unsigned x), (bv_unsigned y). rewrite RI. unfold q2.
    split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
  - lstep. if_cases K2; zify_cond K2; rewrite ?EUx, ?EUy in K2.
    + (* [comment removed for export] *)
      assert (Exy : x = y) by (apply bv_eq; exact K2). subst y.
      pose proof (idx_aux_ge (S k) b1 b2 (sc_pre_S b1 b2 k x HP E1 E2 K)). lia.
    + destruct (res_break b1 b2 k x y HP E1 E2 (or_introl K2)) as (RI & RR).
      apply evt_done. exists (bv_unsigned x), (bv_unsigned y). rewrite RI. unfold q2.
      split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
  - (* [comment removed for export] *)
    pose proof (idx_aux_break k b1 b2 x y HP E1 E2 (or_intror K)). lia.
  - lstep. if_cases K2; zify_cond K2; rewrite ?EUx, ?EUy in K2.
    + assert (Exy : x = y) by (apply bv_eq; exact K2). subst y.
      pose proof (sc_pre_S b1 b2 k x HP E1 E2 K) as HP1.
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      apply (IH (S k) p1 p2 b1 b2); [lia| exact L1| exact L2| exact B1| exact B2| exact OK| exact HP1| exact MI].
    + pose proof (idx_aux_break k b1 b2 x y HP E1 E2 (or_introl K2)). lia.
Qed.
